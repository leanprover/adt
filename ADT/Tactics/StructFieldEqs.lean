/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import Std.Data.DHashMap.Basic

/-!
# Equational theorems for functions that return structure instances

This file develops a utility for generating equational
theorems for functions that return structure instances
-/

open Lean Elab Meta Parser

namespace StructFieldEqs

inductive NestedStructMode where
  | terminal
  | chain
deriving Inhabited

instance : KVMap.Value NestedStructMode where
  toDataValue : NestedStructMode → DataValue
  | .terminal => "terminal"
  | .chain => "chain"
  ofDataValue? : DataValue → Option NestedStructMode
  | .ofString "terminal" => .some .terminal
  | .ofString "chain" => .some .chain
  | _ => .none

end StructFieldEqs

register_option struct_field_eqs.nestedStructMode : StructFieldEqs.NestedStructMode := {
  defValue := .terminal
  descr := "enable the 'unused rcases pattern' linter"
}

namespace StructFieldEqs

/-
  Generate equational theorems for functions that return structure instances

  **TODO (Maybe Reconsider)** Note that there is no need to recurse into sub-objects when generating
  the equational theorems.
-/

initialize registerTraceClass `struct_field_eqs.thmNames


theorem ite_comm.{u, v}
    {α : Sort u} {β : Sort v} {c : Prop} [Decidable c]
    (a b : α) (f : α → β) : f (if c then a else b) = if c then (f a) else (f b) := by
  cases Decidable.em c <;> simp [*]

structure ProjFnInfo where
  ctorName    : Name
  fieldIdx    : Nat
  numParams   : Nat
  val         : Expr
  type        : Expr
  isDep       : Bool

/--
  Check if `e` is a `matcherApp` of the form
    `matcherName params (fun _ => motive) discrs [[fun _ => alt]]`
  Which is provably equal to just `alt`
-/
def isIdMatcher (e : Expr) : MetaM (Option Expr) := do
  let .some matcherApp ← matchMatcherApp? e
    | return .none
  let altInfos := matcherApp.alts.zip matcherApp.altNumParams
  let .some (alt₀, altNumParams₀) := altInfos[0]?
    | throwError "{decl_name%} :: Cannot deal with nomatch currently"
  let alt := Expr.headBeta (mkAppN alt₀ ⟨List.replicate altNumParams₀ (.bvar 0)⟩)
  if alt.hasLooseBVars then
    return .none
  for (alt', altNumParams') in altInfos do
    let alt' := Expr.headBeta (mkAppN alt' ⟨List.replicate altNumParams' (.bvar 0)⟩)
    if alt'.hasLooseBVars then
      return .none
    if !(← isDefEq alt alt') then
      return .none
  return alt

/--
  For a matcher `matcherName` used as
    `matcherName params motive discrs alts`
  and an array of universe level parameters `us` for `matcherName`,
  generate a theorem of type
    `∀ [[params : _]] (motive : _) [[discrs : _]] (alt : _),`
    `  matcherName params (fun _ => motive) discrs [[fun _ => alt]] = alt`
  Return the proof of the theorem and the type of the theorem

  Note that more generally, we should be able to support dependent
  motives. However, to do that, we would have to use `HEq`. Therefore,
  we're sticking to the non-dependent motive case.
-/
def mkIdThmForMatcher (matcherName : Name) (us : Array Level) : MetaM (Expr × Expr) := do
  let .some matcherInfo ← getMatcherInfo? matcherName
    | throwError "{decl_name%} :: {matcherName} is not a matcher"
  if let .some pos := matcherInfo.uElimPos? then
    if pos >= us.size then
      throwError "{decl_name%} :: uElimPos {pos} is out of bounds"
  let motiveLvl :=
    match matcherInfo.uElimPos? with
    | .some pos => us[pos]!
    | .none => .zero
  let usRep (uelim : Level) : Array Level :=
    match matcherInfo.uElimPos? with
    | .some pos => us.set! pos uelim
    | .none => us
  let matchEqns ← Match.getEquationsFor matcherName
  let .some matcherConstInfo := (← getEnv).find? matcherName
    | throwError "{decl_name%} :: Unexpected error, cannot find {matcherName}"
  let matcher := Expr.const matcherName us.toList
  let matcherType := matcherConstInfo.type.instantiateLevelParamsArray ⟨matcherConstInfo.levelParams⟩ us
  forallBoundedTelescope matcherType matcherInfo.numParams fun params b =>
    withLocalDecl `motive .default (.sort motiveLvl) fun motive => do
      let motiveVal ← forallBoundedTelescope b (.some 1) fun motiveFVar _ => do
        let #[motiveFVar] := motiveFVar
          | throwError "{decl_name%} :: Unexpected error"
        forallBoundedTelescope (← inferType motiveFVar) matcherInfo.numDiscrs fun discrs _ =>
          mkLambdaFVars discrs motive
      let matcherPartial := mkAppN matcher (params ++ #[motiveVal])
      withLocalDecl `alt .default motive fun alt => do
        forallBoundedTelescope (← inferType matcherPartial) matcherInfo.numDiscrs fun discrs b => do
          -- Constructing Type
          let alts ← forallBoundedTelescope b matcherInfo.numAlts fun alts _ => do
            let altInfos := alts.zip matcherInfo.altNumParams
            altInfos.mapM (fun (altFVar, altNumParams) => do
              forallBoundedTelescope (← inferType altFVar) altNumParams fun xs _ => do
                mkLambdaFVars xs alt)
          let lhs := mkAppN matcherPartial (discrs ++ alts)
          let genEq ← mkEq lhs alt
          let genEqFn ← mkLambdaFVars discrs genEq
          -- Constructing Proof
          let splitter := Expr.const matchEqns.splitterName (usRep .zero).toList
          let splitterPartial := mkAppN splitter (params ++ #[genEqFn] ++ discrs)
          let splitterPartialTy ← inferType splitterPartial
          forallBoundedTelescope splitterPartialTy matcherInfo.numAlts fun pralts _ => do
            let altInfos := pralts.zip matcherInfo.altNumParams
            let altProofs ← altInfos.mapM (fun (alt, nparams) => do
              let altType ← inferType alt
              forallBoundedTelescope altType nparams fun altParams altb => do
                let_expr Eq _ lhs _ := altb
                  | throwError "{decl_name%} :: Unexpected error"
                let rflProof ← mkEqRefl lhs
                mkLambdaFVars altParams rflProof)
            let proof := mkAppN splitterPartial altProofs
            let fvars := params ++ #[motive] ++ discrs ++ #[alt]
            return (← mkForallFVars fvars genEq, ← mkLambdaFVars fvars proof)

/--
  For a matcher `matcherName` used as
    `matcherName params motive discrs alts`,
  an array of universe level parameters `us` for `matcherName`,
  and an extra universe level `u`, generate a theorem of type
    `∀ [[params : _]] (motive : _ → Sort _) (motive' : _ → Sort u)`
    `  (f : ∀ (discrs : _), motives discrs → motive' discrs)`
    `  [[discrs : _]] [[alts : _]],`
    `  f _ (matcherName params motive discrs alts) =`
    `    matcherName params motive' discrs [[fun _ => f _ (alts _)]]`
  Return the proof of the theorem and the type of the theorem

  Note that more generally, the type of `f` could be
    `f : ∀ (x : _) (h : motive x), Sort u`
  But that would require the motive on the right-hand side
  to contain a `matcherName` application. We haven't
  come up with convincing use cases for this, therefore
  we're sticking to the easier case
-/
def mkCommThmForMatcher (matcherName : Name) (us : Array Level) (u : Level) : MetaM (Expr × Expr) := do
  let .some matcherInfo ← getMatcherInfo? matcherName
    | throwError "{decl_name%} :: {matcherName} is not a matcher"
  if !(← isLevelDefEq u .zero) && matcherInfo.uElimPos?.isNone then
    throwError "{decl_name%} :: Cannot eliminate into non-zero universe level {u}"
  if let .some pos := matcherInfo.uElimPos? then
    if pos >= us.size then
      throwError "{decl_name%} :: uElimPos {pos} is out of bounds"
  let usRep (uelim : Level) : Array Level :=
    match matcherInfo.uElimPos? with
    | .some pos => us.set! pos uelim
    | .none => us
  let matchEqns ← Match.getEquationsFor matcherName
  let .some matcherConstInfo := (← getEnv).find? matcherName
    | throwError "{decl_name%} :: Unexpected error, cannot find {matcherName}"
  let matcher := Expr.const matcherName us.toList
  let matcherType := matcherConstInfo.type.instantiateLevelParamsArray ⟨matcherConstInfo.levelParams⟩ us
  forallBoundedTelescope matcherType matcherInfo.numParams fun params b =>
    forallBoundedTelescope b (.some 1) fun motive b => do
      let #[motive] := motive
        | throwError "{decl_name%} :: Expected one motive, got none"
      let motiveType ← inferType motive
      let motive'Type ← forallTelescope motiveType fun xs _ => mkForallFVars xs (.sort u)
      withLocalDecl `motive' .default motive'Type fun motive' => do
        let fnType ← forallTelescope motiveType fun xs _ => do
          return ← mkForallFVars xs (← mkArrow (mkAppN motive xs) (mkAppN motive' xs))
        withLocalDecl `f .default fnType fun f => do
          forallBoundedTelescope b matcherInfo.numDiscrs fun discrs b => do
            forallBoundedTelescope b matcherInfo.numAlts fun alts _ => do
              -- Constructing Type
              let matcherPartial := mkAppN matcher (params ++ #[motive] ++ discrs)
              let lhs := mkAppN f (discrs ++ #[mkAppN matcherPartial alts])
              let altInfos := alts.zip matcherInfo.altNumParams
              let rhsAlts ← altInfos.mapM (fun (alt, nparams) => do
                let altType ← inferType alt
                forallBoundedTelescope altType nparams fun altParams _ => do
                  let altApp := mkAppN alt altParams
                  let fApp ← mkAppOptM' f (discrs.map (fun _ => Option.none) ++ #[.some altApp])
                  mkLambdaFVars altParams fApp)
              let matcher' := Expr.const matcherName (usRep u).toList
              let rhs := mkAppN matcher' (params ++ [motive'] ++ discrs ++ rhsAlts)
              let genEq ← mkEq lhs rhs
              let genEqFn ← mkLambdaFVars discrs genEq
              -- Constructing Proof
              let splitter := Expr.const matchEqns.splitterName (usRep .zero).toList
              let splitterPartial := mkAppN splitter (params ++ #[genEqFn] ++ discrs)
              let splitterPartialTy ← inferType splitterPartial
              forallBoundedTelescope splitterPartialTy matcherInfo.numAlts fun pralts _ => do
                let altInfos := pralts.zip matcherInfo.altNumParams
                let altProofs ← altInfos.mapM (fun (alt, nparams) => do
                  let altType ← inferType alt
                  forallBoundedTelescope altType nparams fun altParams altb => do
                    let_expr Eq _ lhs _ := altb
                      | throwError "{decl_name%} :: Unexpected error"
                    let rflProof ← mkEqRefl lhs
                    mkLambdaFVars altParams rflProof)
                let proof := mkAppN splitterPartial altProofs
                let fvars := params ++ #[motive, motive', f] ++ discrs ++ alts
                return (← mkForallFVars fvars genEq, ← mkLambdaFVars fvars proof)

def mkProjFnInfo (structName : Name) (fieldIdx : Nat) (fieldName : Name) (valType : Expr) : MetaM ProjFnInfo := do
  let structCtor := getStructureCtor (← getEnv) structName
  let projFn ← withLocalDecl `lhsCore .default valType fun x => do
    let proj ← mkProjection x fieldName
    mkLambdaFVars #[x] proj
  let type ← whnf (← inferType projFn)
  let .forallE _ _ b _ := type
    | throwError "{decl_name%} :: The type of {projFn} is not a `∀`"
  return {
    ctorName := structCtor.name,
    numParams := structCtor.numParams,
    fieldIdx := fieldIdx,
    val := projFn,
    type := type,
    isDep := b.hasLooseBVars
  }

/--
  Input
  · `namePrefix`: Prefix of the name of the theorem to be generated
  · `structNames`: Structures to recurse into
  · `lhsCore, lhsValCore`: Two provably equal expressions
    `proof`: A proof of `lhsCore = lhsValCore`

  Output:
    An array of `(name, eqExpr, proof)`, where `proof` proves
    `eqExpr`, and the name of the generated theorem with type
    `eqExpr` and value `proof` is `name`
  · If `nestedStructMode` is `terminal`, `eqExpr` will be of the
    form `proj₁ (proj₂ ... (projₖ lhsCore)) = rhs`, where the type
    of `rhs` is either not a structure, or is a structure but not
    in `structNames`
  · If `nestedStructMode` is `chain`
    · Equations related to direct subfields of `lhs` will be of the form
      `proj₁ lhs = rhs`
    · Equations related to indirect subfields of `lhs` will be of the form
      `projᵢ lhs' = rhs`, where `lhs'` is the right-hand-side of
      some preceeding equation
-/
partial def mkElabStructFieldEqs
    (namePrefix : Name) (structNames : Std.HashSet Name)
    (lhsCore : Expr) (lhsValCore : Expr) (lhsEq : Expr)
    (nestedStructMode : NestedStructMode) : MetaM (Array (Name × Expr × Expr)) := do
  let b ← whnf (← inferType lhsCore)
  let .const structName _ := b.getAppFn
    | return #[]
  unless structNames.contains structName && isStructure (← getEnv) structName do
    return #[]
  let structFields := getStructureFields (← getEnv) structName
  let arr : Array (Array (Name × Expr × Expr)) ← structFields.mapIdxM (fun fieldIdx field => do
    let structFieldStr := String.intercalate "_" (field.components.map Name.toString)
    let subNamePrefix := namePrefix.appendAfter ("_" ++ structFieldStr)
    let name := subNamePrefix.appendAfter "_eq"
    let lhs ← mkProjection lhsCore field
    let projFnInfo ← mkProjFnInfo structName fieldIdx field (← inferType lhsCore)
    -- Here `proof` proves that `projFnInfo.val lhsValCore = rhs`
    let (rhs, proof) ← go projFnInfo lhsValCore
    -- Here `proof` proves that `projFnInfo.val lhs = rhs`
    let proof ← mkEqTrans (← mkCongrArg projFnInfo.val lhsEq) proof
    let eqExpr ← mkEq lhs rhs
    match nestedStructMode with
    | .terminal =>
      let subEqs ← mkElabStructFieldEqs subNamePrefix structNames lhs rhs proof nestedStructMode
      if subEqs.isEmpty then
        trace[struct_field_eqs.thmNames] "{name}"
        return #[(name, eqExpr, proof)]
      else
        return subEqs
    | .chain =>
      let subEqs ← mkElabStructFieldEqs subNamePrefix structNames rhs rhs (← mkEqRefl rhs) nestedStructMode
      trace[struct_field_eqs.thmNames] "{name}"
      return #[(name, eqExpr, proof)] ++ subEqs)
  return arr.flatMap id
where
  -- Returns `rhs` and the proof of `projFn body = rhs`
  go (pi : ProjFnInfo) : Expr → MetaM (Expr × Expr)
    | .letE name type val body _ =>
      withLetDecl name type val fun x => do
        let (rhs, proof) ← go pi (body.instantiate1 x)
        let rhs ← mkLetFVars #[x] rhs
        let proof ← mkLetFVars #[x] proof
        return (rhs, proof)
    | .mdata data b => do
      let (rhs, proof) ← go pi b
      return (.mdata data rhs, proof)
    | b@(.app _ _ ) => do
      let appFn := b.getAppFn
      let appArgs := b.getAppArgs
      let .some appFnName := appFn.constName?
        | return ← goFallBack pi b
      if appFnName == pi.ctorName then
        let some rhs := appArgs[pi.numParams + pi.fieldIdx]?
          | throwError "{decl_name%} :: Cannot get the {pi.fieldIdx}-th field from (supposedly) structure instance {b}"
        let rflExpr ← mkEqRefl (.app pi.val b)
        return (rhs, rflExpr)
      if pi.isDep then
        return ← goFallBack pi b
      if appFnName == ``ite then
        return ← goIteApp pi b
      if let .some matcherApp ← matchMatcherApp? b then
        return ← goMatcherApp pi matcherApp
      return ← goFallBack pi b
    | b => return ← goFallBack pi b
  goFallBack (pi : ProjFnInfo) (e : Expr) : MetaM (Expr × Expr) := do
    let rhs := Expr.headBeta (mkApp pi.val e)
    return (rhs, ← mkEqRefl rhs)
  goIteApp (pi : ProjFnInfo) (b : Expr) : MetaM (Expr × Expr) := do
    let .forallE _ _ β _ := pi.type
      | throwError "{decl_name%} :: Unexpected error"
    let #[type, cond, dec, left, right] := b.getAppArgs
      | throwError "{decl_name%} :: Unexpected `ite expression {b}"
    let iteCommProof ← mkAppOptM ``ite_comm #[type, β, cond, dec, left, right, pi.val]
    let (leftrw, leftProof) ← go pi left
    let (rightrw, rightProof) ← go pi right
    let rhs ← mkAppOptM ``ite #[β, cond, dec, leftrw, rightrw]
    let iteCongrProof ← mkAppOptM ``ite_congr
      #[β, cond, cond, Expr.app pi.val left, Expr.app pi.val right,
        leftrw, rightrw, dec, dec, ← mkEqRefl cond,
        Expr.lam `_ cond leftProof .default,
        Expr.lam `_ (mkNot cond) rightProof .default]
    let proof ← mkEqTrans iteCommProof iteCongrProof
    let (rhs, proof) ← (do
      if ← isDefEq leftrw rightrw then
        let id_proof ← mkAppOptM ``ite_id #[cond, dec, β, leftrw]
        return (leftrw, ← mkEqTrans proof id_proof)
      return (rhs, proof))
    return (rhs, proof)
  goMatcherApp (pi : ProjFnInfo) (matcherApp : MatcherApp) : MetaM (Expr × Expr) := do
    let .forallE _ _ β _ := pi.type
      | throwError "{decl_name%} :: Unexpected error"
    let .sort βLevel ← Meta.whnf (← inferType β)
      | throwError "{decl_name%} :: Unexpected error"
    let name := matcherApp.matcherName
    let levels := matcherApp.matcherLevels
    let motive := matcherApp.motive
    let (matchCommEq, matchCommProof) ← mkCommThmForMatcher name levels βLevel
    let (motive', fn) ← lambdaBoundedTelescope motive matcherApp.discrs.size fun xs _ =>
      return (← mkLambdaFVars xs β, ← mkLambdaFVars xs pi.val)
    let thmArgs :=
      matcherApp.params ++ #[motive, motive', fn] ++ matcherApp.discrs ++ matcherApp.alts
    let matchCommEq ← instantiateForall matchCommEq thmArgs
    let matchCommProof ← instantiateLambda matchCommProof thmArgs
    let_expr Eq _ _ rhs := matchCommEq
      | throwError "{decl_name%} :: Unexpected error"
    let argEqs ← (matcherApp.alts.zip matcherApp.altNumParams).mapM (fun (alt, numParam) => do
      lambdaBoundedTelescope alt numParam fun xs b => do
        let (rhs, proof) ← go pi b
        let rhs ← mkLambdaFVars xs rhs
        let mut proof := proof
        for x in xs.reverse do
          proof ← mkLambdaFVars #[x] proof
          proof ← mkAppM ``funext #[proof]
        return (rhs, proof))
    let .some matcherApp' ← matchMatcherApp? rhs
      | throwError "{decl_name%} :: Unexpected error"
    let matcher := Expr.const matcherApp'.matcherName matcherApp'.matcherLevels.toList
    let matcherPartial := mkAppN matcher (matcherApp'.params ++ #[matcherApp'.motive] ++ matcherApp'.discrs)
    let rhs := mkAppN matcherPartial (argEqs.map Prod.fst)
    let mut congrProof ← mkEqRefl matcherPartial
    for (_, argProof) in argEqs do
      congrProof ← mkCongr congrProof argProof
    let proof ← mkEqTrans matchCommProof congrProof
    let (rhs, proof) ← (do
      if let .some alt ← isIdMatcher rhs then
        let motive ← inferType alt
        let thmArgs := matcherApp'.params ++ #[motive] ++ matcherApp'.discrs ++ #[alt]
        let (_, matchIdProof) ← mkIdThmForMatcher matcherApp'.matcherName matcherApp'.matcherLevels
        let matchIdProof ← instantiateLambda matchIdProof thmArgs
        return (alt, ← mkEqTrans proof matchIdProof)
      return (rhs, proof))
    return (rhs, proof)

def mkElabStructFieldEqsStx
    (declName : Name) (structNames : Std.HashSet Name) (modifiers : TSyntax ``Command.declModifiers) :
    TermElabM (Array (TSyntax ``Command.declaration)) := do
  let .some ci := (← getEnv).find? declName
    | throwError "{decl_name%} :: Cannot find declaration `{declName}`"
  let .some declBody := ci.value?
    | throwError "{decl_name%} :: `{declName}` does not have a value"
  let nBinders ← forallTelescopeReducing ci.type fun xs b => do
    let b ← whnf b
    let .const constName _ := b.getAppFn
      | throwError "{decl_name%} :: The head of the type {b} is not a constant"
    unless isStructure (← getEnv) constName do
      throwError "{decl_name%} :: `{constName}` is not a structure"
    return xs.size
  let nestedStructMode := struct_field_eqs.nestedStructMode.get (← getOptions)
  lambdaBoundedTelescope declBody nBinders fun xs b => do
    let declConst := Expr.const declName (ci.levelParams.map Level.param)
    let lhsCore := mkAppN declConst xs
    let thms ← mkElabStructFieldEqs declName structNames lhsCore b (← mkEqRefl lhsCore) nestedStructMode
    thms.mapM (fun (name, eqExpr, proof) => do
      let eqExpr ← mkForallFVars xs eqExpr
      let proof ← mkLambdaFVars xs proof
      let eqStx ← Term.exprToSyntax eqExpr
      let proofStx ← Term.exprToSyntax proof
      let fieldEqDeclStx := mkIdent (.append (.str .anonymous "_root_") name)
      `(Command.declaration| $(modifiers):declModifiers theorem $fieldEqDeclStx : $eqStx := $proofStx))

def elabStructFieldEqsAux
    (declName : Name) (modifiers : TSyntax ``Command.declModifiers)
    (vars : Array Expr) (sc : Command.Scope) (structNames : Std.HashSet Name) : TermElabM Unit := do
  let stxs ← mkElabStructFieldEqsStx declName structNames modifiers
  let modifiersVal ← elabModifiers modifiers
  let views := stxs.map (fun stx => Command.mkDefViewOfTheorem modifiersVal stx.raw[1])
  let _ ← views.mapM (fun view => Term.elabMutualDef vars sc #[view])

syntax (name := structFieldEqsStx) declModifiers "struct_field_eqs" ident "#[" withoutPosition(ident,*,?) "]" : command

/--
  This command generates equational theorems for functions that
  return structure instances, i.e. functions with signatures
  `∀ (x₁ : _) ⋯ (xₖ : _), S t₁ ⋯ tₙ`, where `S` is a `structure`.

  The syntax of the command is
    `<decl_modifiers> struct_field_eqs <ident> #[<ident>,*]`
  where `<decl_modifiers>` are modifiers that can be added to
  declarations, for example `@[simp]`. `<ident>` is the function
  which we want to generate equational theorems. `#[<ident>,*]`
  specifies the list of structures we want to visit.

  For simple structures, this command generates one equational theorem for
  each field of the structure. For example, given the following code
  ```lean
  structure Foo where
    a : Nat
    b : Nat

  def foo (n : Nat) : Foo := { a := n, b := n * n }
  ```
  The command `struct_field_eqs foo #[Foo]` generates
  · `foo_a_eq : ∀ n, (foo n).a = n`
  · `foo_b_eq : ∀ n, (foo n).b = n * n`

  For function definitions that have `if` and `match` in it, the projection
  function is permuted with `match`. For example, given the above structure
  `Foo` and the function
  ```lean
  def foo' (n : Nat) : Foo :=
    match n with
    | 0 => { a := 2, b := 1 }
    | 1 => { a := 1, b := 1 }
    | n + 2 => { a := n, b := 1}
  ```
  instead of generating
  ```lean
  foo'_a_eq : ∀ n, (foo' n).a =
    (match n with
     | 0 => { a := 2, b := 1 }
     | 1 => { a := 1, b := 1 }
     | n + 2 => { a := n, b := 1}).a
  ```
  we generate
  ```lean
  foo'_a_eq : ∀ n, (foo' n).a =
    match n with
    | 0 => 2
    | 1 => 1
    | n + 2 => n
  ```
  If all branches of a `match` return the same value,
  they are automatically merged, hence
  ```lean
  foo'_b_eq : ∀ n, (foo' n).b = 1
  ```

  For structures that `extend` existing structures, we offer two
  options for how we recurse into subobjects. For example, given
  ```lean
  structure Bar₁ where a : Nat
  structure Bar₂ extends Bar₁ where b : Nat
  structure Bar₃ extends Bar₂ where c : Nat

  def bar : Bar₃ := { a := 1, b := 2, c := 3 }
  ```
  and the command
  `struct_field_eqs bar #[Bar₁, Bar₂, Bar₃]`
  · If `struct_field_eqs.nestedStructMode` is set to the default
    value `terminal`, the following theorems will be generated:
    ```lean
    bar_toBar₂_toBar₁_a_eq : bar.a = 1
    bar_toBar₂_b_eq : bar.b = 2
    bar_c_eq : bar.c = 3
    ```
  · If `struct_field_eqs.nestedStructMode` is set to `chain`, the
    following theorems will be generated:
    ```lean
    bar_toBar₂_toBar₁_a_eq : { a := 1 }.a = 1
    bar_toBar₂_toBar₁_eq : { a := 1, b := 2 }.toBar₁ = { a := 1 }
    bar_toBar₂_b_eq : { a := 1, b := 2 }.b = 2
    bar_toBar₂_eq : bar.toBar₂ = { a := 1, b := 2 }
    bar_c_eq : bar.c = 3
    ```
-/
@[command_elab structFieldEqsStx] def elabStructFieldEqs : Command.CommandElab
  | `(command | $modifiers:declModifiers struct_field_eqs $declNameStx:ident #[ $elems,* ]) => do
    let sc ← Command.getScope
    let declName ← resolveGlobalConstNoOverload declNameStx
    let structNames ← elems.getElems.mapM resolveGlobalConstNoOverload
    let structNames := Std.HashSet.ofArray structNames
    Command.runTermElabM fun xs =>
      elabStructFieldEqsAux declName modifiers xs sc structNames
  | _ => throwUnsupportedSyntax

end StructFieldEqs

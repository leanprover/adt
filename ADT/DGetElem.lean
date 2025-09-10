/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

import Lean
import Std.Data

open Lean Std

class DGetElem (coll : Type u) (idx : Type v) (elem : outParam (idx → Type w))
              (valid : outParam (coll → idx → Prop)) where
  /--
  The syntax `arr[i]ᵈ` gets the `i`'th element of the collection `arr`. If there
  are proof side conditions to the application, they will be automatically
  inferred by the `get_elem_tactic` tactic.
  -/
  dGetElem (xs : coll) (i : idx) (h : valid xs i) : elem i

export DGetElem (dGetElem)

@[inherit_doc dGetElem]
syntax:max term noWs "[" withoutPosition(term) "]ᵈ" : term
macro_rules | `($x[$i]ᵈ) => `(dGetElem $x $i (by get_elem_tactic))

@[inherit_doc getElem]
syntax term noWs "[" withoutPosition(term) "]ᵈ'" term:max : term
macro_rules | `($x[$i]ᵈ'$h) => `(dGetElem $x $i $h)

class DGetElem? (coll : Type u) (idx : Type v) (elem : outParam (idx → Type w))
    (valid : outParam (coll → idx → Prop)) extends DGetElem coll idx elem valid where
  /--
  The syntax `arr[i]ᵈ?` gets the `i`'th element of the collection `arr`,
  if it is present (and wraps it in `some`), and otherwise returns `none`.
  -/
  dGetElem? : coll → (i : idx) → Option (elem i)

  /--
  The syntax `arr[i]ᵈ!` gets the `i`'th element of the collection `arr`,
  if it is present, and otherwise panics at runtime and returns the `default` term
  from `Inhabited (elem i)`.
  -/
  dGetElem! (xs : coll) (i : idx) [Inhabited (elem i)] : elem i :=
    match dGetElem? xs i with | some e => e | none => outOfBounds

export DGetElem? (dGetElem? dGetElem!)

/--
The syntax `arr[i]?` gets the `i`'th element of the collection `arr` or
returns `none` if `i` is out of bounds.
-/
macro:max x:term noWs "[" i:term "]ᵈ" noWs "?" : term => `(dGetElem? $x $i)

/--
The syntax `arr[i]!` gets the `i`'th element of the collection `arr` and
panics `i` is out of bounds.
-/
macro:max x:term noWs "[" i:term "]ᵈ" noWs "!" : term => `(dGetElem! $x $i)

/--
Lawful `DGetElem?` instances (which extend `DGetElem`) are those for which the potentially-failing
`DGetElem?.dGetElem?` and `DGetElem?.dGetElem!` operators succeed when the validity predicate is
satisfied, and fail when it is not.
-/
class LawfulDGetElem (cont : Type u) (idx : Type v) (elem : outParam (idx → Type w))
   (dom : outParam (cont → idx → Prop)) [ge : DGetElem? cont idx elem dom] : Prop where

  /-- `GetElem?.getElem?` succeeds when the validity predicate is satisfied and fails otherwise. -/
  dGetElem?_def (c : cont) (i : idx) [Decidable (dom c i)] :
    c[i]ᵈ? = if h : dom c i then some (c[i]ᵈ'h) else none := by
    intros
    try simp only [dGetElem?] <;> congr

  /-- `GetElem?.getElem!` succeeds and fails when `GetElem.getElem?` succeeds and fails. -/
  dGetElem!_def (c : cont) (i : idx) [Inhabited (elem i)] :
    c[i]ᵈ! = match c[i]ᵈ? with | some e => e | none => default := by
    intros
    simp only [dGetElem!, dGetElem?, outOfBounds_eq_default]

export LawfulDGetElem (dGetElem?_def dGetElem!_def)

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : DGetElem? (DHashMap α β) α β (fun m x => x ∈ m) where
  dGetElem := DHashMap.get
  dGetElem? := DHashMap.get?
  dGetElem! := DHashMap.get!

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : LawfulDGetElem (DHashMap α β) α β (fun m x => x ∈ m) where
  dGetElem!_def := by
    intros
    simp only [dGetElem!, dGetElem?, DHashMap.get!_eq_get!_get?]
    split <;> simp_all
  dGetElem?_def := by
    intros
    simp only [dGetElem?, dGetElem]; split
    case isTrue h => rw [DHashMap.get?_eq_some_get h]
    case isFalse h => rw [DHashMap.get?_eq_none h]

instance {α β} [Ord α] [LawfulEqOrd α] : DGetElem? (DTreeMap α β) α β (fun m x => x ∈ m) where
  dGetElem := DTreeMap.get
  dGetElem? := DTreeMap.get?
  dGetElem! := DTreeMap.get!

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulDGetElem (DTreeMap α β) α β (fun m x => x ∈ m) where
  dGetElem!_def := by
    intros
    simp only [dGetElem!, dGetElem?, DTreeMap.get!_eq_get!_get?]
    split <;> simp_all
  dGetElem?_def := by
    intros
    simp only [dGetElem?, dGetElem]; split
    case isTrue h => rw [DTreeMap.get?_eq_some_get] -- *TODO*: Compare this with `DHashMap`, why?
    case isFalse h => rw [DTreeMap.get?_eq_none h]

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : DGetElem? (ExtDHashMap α β) α β (fun m x => x ∈ m) where
  dGetElem := ExtDHashMap.get
  dGetElem? := ExtDHashMap.get?
  dGetElem! := ExtDHashMap.get!

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : LawfulDGetElem (ExtDHashMap α β) α β (fun m x => x ∈ m) where
  dGetElem!_def := by
    intros
    simp only [dGetElem!, dGetElem?, ExtDHashMap.get!_eq_get!_get?]
    split <;> simp_all
  dGetElem?_def := by
    intros
    simp only [dGetElem?, dGetElem]; split
    case isTrue h => rw [ExtDHashMap.get?_eq_some_get h]
    case isFalse h => rw [ExtDHashMap.get?_eq_none h]

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : DGetElem? (ExtDTreeMap α β) α β (fun m x => x ∈ m) where
  dGetElem := ExtDTreeMap.get
  dGetElem? := ExtDTreeMap.get?
  dGetElem! := ExtDTreeMap.get!

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulDGetElem (ExtDTreeMap α β) α β (fun m x => x ∈ m) where
  dGetElem!_def := by
    intros
    simp only [dGetElem!, dGetElem?, ExtDTreeMap.get!_eq_get!_get?]
    split <;> simp_all
  dGetElem?_def := by
    intros
    simp only [dGetElem?, dGetElem]; split
    case isTrue h => rw [ExtDTreeMap.get?_eq_some_get h]
    case isFalse h => rw [ExtDTreeMap.get?_eq_none h]

/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

import Lean
import ADT.IsomMap
import ADT.Array
import ADT.Mapy
import ADT.Tactics.StructFieldEqs

open Lean

structure IndexMap (γ : Type v) (α : Type u) [Mapy γ α Nat] where
  map : γ
  ind : Array α
  off : Nat

namespace IndexMap

variable {γ : Type v} {α : Type u} [inst : Mapy γ α Nat]

def emptyWithCapacity (off : Nat := 0) (capacity : Nat := 8) : IndexMap γ α :=
  { map := Mapy.emptyWithCapacity (self:=inst) capacity, ind := #[], off }

def getIdx? (m : IndexMap γ α) (x : α) : Option Nat :=
  m.map[x]?

def getVal? (m : IndexMap γ α) (i : Nat) : Option α :=
  Array.getShl? m.ind i m.off

def size (m : IndexMap γ α) := m.ind.size

def elem (m : IndexMap γ α) (x : α) := x ∈ m.map

instance : Membership α (IndexMap γ α) where
  mem m a := m.elem a

def getIdx (m : IndexMap γ α) (x : α) (h : x ∈ m) : Nat :=
  m.map[x]

instance : IsomMap α Nat (IndexMap γ α) where
  find₁ := getIdx?
  find₂ := getVal?

def insert (m : IndexMap γ α) (x : α) : IndexMap γ α :=
  { map := Mapy.insert m.map x (m.off + m.size), ind := m.ind.push x, off := m.off }

def getIdxThenInsertIfNew? (m : IndexMap γ α) (a : α) : Option Nat × IndexMap γ α :=
  match m.getIdx? a with
  | .some i => ⟨.some i, m⟩
  | .none => ⟨.none, m.insert a⟩

def insertIfNewThenGetIdx (m : IndexMap γ α) (a : α) : Nat × IndexMap γ α :=
  match m.getIdx? a with
  | .some i => ⟨i, m⟩
  | .none => ⟨m.off + m.size, m.insert a⟩

def insertIfNew (m : IndexMap γ α) (a : α) : IndexMap γ α :=
  match m.getIdx? a with
  | .some _ => m
  | .none => m.insert a

def insertIfNewMany (m : IndexMap γ α) (as : Array α) : IndexMap γ α :=
  Array.foldl insertIfNew m as

struct_field_eqs getIdxThenInsertIfNew? #[Prod, IndexMap]
struct_field_eqs insertIfNewThenGetIdx #[Prod, IndexMap]
struct_field_eqs insertIfNew #[Prod, IndexMap]
struct_field_eqs insertIfNewMany #[Prod, IndexMap]

def WF (m : IndexMap γ α) := WFIsomMap α Nat _ m

/-
theorem size_eq_of_WF
  {α : Type u} [inst : Mapy γ α Nat] {m : IndexMap γ α} {x : α}
  (hwf : m.WF) : m.size = Sizy.size m.map := by
  simp only [IndexMap.size]
-/

@[simp]
theorem off_insert {m : IndexMap γ α} {x : α} :
  (m.insert x).off = m.off := rfl

@[simp]
theorem off_getIdxThenInsertIfNew? {m : IndexMap γ α} {x : α} :
  (m.getIdxThenInsertIfNew? x).snd.off = m.off := getIdxThenInsertIfNew?_snd_off_eq _ _

@[simp]
theorem off_insertIfNewThenGetIdx {m : IndexMap γ α} {x : α} :
  (m.insertIfNewThenGetIdx x).snd.off = m.off := insertIfNewThenGetIdx_snd_off_eq _ _

@[simp]
theorem off_insertIfNew {m : IndexMap γ α} {x : α} :
  (m.insertIfNew x).off = m.off := insertIfNew_off_eq _ _

@[simp]
theorem off_insertIfNewMany {m : IndexMap γ α} {as : Array α} :
  (m.insertIfNewMany as).off = m.off := by
  induction as using Array.push_ind
  case base => simp [insertIfNewMany]
  case ind head tail IH =>
    simp only [insertIfNewMany] at IH; simp [insertIfNewMany, *]

@[simp]
theorem size_insert {m : IndexMap γ α} {x : α} :
  (m.insert x).size = m.size + 1 := by
  simp [insert, size]

theorem mem_def {m : IndexMap γ α} {x : α} :
  x ∈ m ↔ x ∈ m.map := Iff.rfl

theorem getVal?_def {m : IndexMap γ α} {i : Nat} :
  m.getVal? i = if i >= m.off then m.ind[i - m.off]? else .none := rfl

theorem mem_iff_getIdx?_eq_some [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} : x ∈ m ↔ ∃ i, m.getIdx? x = .some i := by
  rw [mem_def, LawfulMapy.mem_iff_isSome_getElem?]
  exact Option.isSome_iff_exists

theorem mem_iff_getIdx?_isSome [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} : x ∈ m ↔ (m.getIdx? x).isSome :=
  iff_iff_eq.mp Option.isSome_iff_exists ▸ mem_iff_getIdx?_eq_some

theorem mem_iff_getVal?_eq_some [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} (hwf : WF m) : x ∈ m ↔ ∃ i, m.getVal? i = .some x := by
  rw [mem_iff_getIdx?_eq_some]; apply Iff.intro <;> intro ⟨i, hi⟩ <;> exists i
  case mp => apply hwf.find₁_find₂ _ _ hi
  case mpr => apply hwf.find₂_find₁ _ _ hi

theorem mem_iff_mem_ind [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} (hwf : WF m) : x ∈ m ↔ x ∈ m.ind := by
  rw [Array.mem_iff_getElem?, mem_iff_getVal?_eq_some hwf]
  apply Iff.intro
  case mp =>
    intro ⟨i, heq⟩; simp only [getVal?_def] at heq
    split at heq
    case isTrue hi => exists i - m.off
    case isFalse hi => cases heq
  case mpr =>
    intro ⟨i, heq⟩; exists i + m.off
    simp [getVal?_def, heq]

theorem not_mem_iff_getIdx?_eq_none [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} : x ∉ m ↔ m.getIdx? x = .none := by
  simp [Option.eq_none_iff_forall_ne_some, mem_iff_getIdx?_eq_some]

theorem not_mem_iff_getIdx?_isNone [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} : x ∉ m ↔ (m.getIdx? x).isNone :=
  iff_iff_eq.mp Option.isNone_iff_eq_none ▸ not_mem_iff_getIdx?_eq_none

theorem insert_eq_if_mem [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α} [Decidable (x ∈ m)] :
  m.insertIfNew x = if (x ∈ m) then m else m.insert x := by
  simp only [insertIfNew]; split
  case h_1 heq => simp [mem_iff_getIdx?_eq_some.mpr ⟨_, heq⟩]
  case h_2 heq => simp [not_mem_iff_getIdx?_eq_none.mpr heq]

theorem size_insertIfNew [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} [Decidable (x ∈ m)] :
  (m.insertIfNew x).size = if (x ∈ m) then m.size else m.size + 1 := by
  simp only [insertIfNew]
  cases heq : m.getIdx? x
  case none => simp [size_insert, not_mem_iff_getIdx?_eq_none.mpr heq]
  case some i => simp [mem_iff_getIdx?_eq_some.mpr ⟨_, heq⟩]

open Classical in
theorem size_insertIfNew_of_mem [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α}
  (hmem : x ∈ m) : (m.insertIfNew x).size = m.size := by
  simp [size_insertIfNew, hmem]

open Classical in
theorem size_insertIfNew_of_not_mem [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} (hmem : x ∉ m) : (m.insertIfNew x).size = m.size + 1 := by
  simp [size_insertIfNew, hmem]

@[simp]
theorem not_mem_empty [LawfulMapy γ α Nat] {off capacity : Nat} {x : α} :
  ¬ x ∈ emptyWithCapacity (inst:=inst) off capacity := by
  apply LawfulMapy.not_mem_empty

@[simp]
theorem mem_insert [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x y : α} : y ∈ m.insert x ↔ x = y ∨ y ∈ m := by
  simp only [insert, mem_def, LawfulMapy.mem_insert]

theorem getIdx?_eq_some_getIdx [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α} (h : x ∈ m) :
  m.getIdx? x = .some (m.getIdx x h) := LawfulMapy.getElem?_eq_some_getElem h

/-- Recommended choice for both `apply` and `have` -/
theorem getIdx_eq_of_getIdx?_eq_some [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} {i : Nat} (h : m.getIdx? x = .some i) :
  m.getIdx x (mem_iff_getIdx?_eq_some.mpr ⟨_, h⟩) = i := by
  rw [getIdx?_eq_some_getIdx] at h; injection h

/-- Recommended choice for `apply` -/
theorem getIdx_eq_of_getIdx?_eq_some' [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} {i : Nat} {hmem : x ∈ m} (h : m.getIdx? x = .some i) :
  m.getIdx x hmem = i := by
  rw [getIdx?_eq_some_getIdx] at h; injection h

theorem getIdx?_ge_of_WF {m : IndexMap γ α} {x : α} {i : Nat} (hwf : WF m)
  (heq : m.getIdx? x = .some i) : i ≥ m.off := by
  have heq' : m.getVal? i = some x := hwf.find₁_find₂ _ _ heq
  simp only [getVal?, Array.getShl?] at heq'
  revert heq'; split <;> intro heq <;> simp_all

theorem getIdx?_lt_of_WF {m : IndexMap γ α} {x : α} {i : Nat} (hwf : WF m)
  (heq : m.getIdx? x = .some i) : i < m.off + m.size := by
  have heq' : m.getVal? i = some x := hwf.find₁_find₂ _ _ heq
  simp only [getVal?, Array.getShl?] at heq'
  revert heq'; split <;> intro heq'
  case isTrue =>
    have ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp heq'
    rw [size]; omega
  case isFalse => cases heq'

theorem getIdx_ge_of_WF [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α}
  (hwf : WF m) (hmem : x ∈ m) : m.getIdx x hmem ≥ m.off := by
  have heq := LawfulMapy.getElem?_eq_some_getElem hmem
  exact getIdx?_ge_of_WF hwf heq

theorem getIdx_lt_of_WF [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α}
  (hwf : WF m) (hmem : x ∈ m) : m.getIdx x hmem < m.off + m.size := by
  have heq := LawfulMapy.getElem?_eq_some_getElem hmem
  exact getIdx?_lt_of_WF hwf heq

theorem insertIfNewThenGetIdx_ge_of_WF {m : IndexMap γ α} {x : α} (hwf : WF m) :
  (m.insertIfNewThenGetIdx x).fst ≥ m.off := by
  simp only [insertIfNewThenGetIdx]; split
  case h_1 i heq => exact getIdx?_ge_of_WF hwf heq
  case h_2 => simp

theorem insertIfNewThenGetIdx_lt_of_WF {m : IndexMap γ α} {x : α} (hwf : WF m) :
  (m.insertIfNewThenGetIdx x).fst < m.off + (m.insertIfNewThenGetIdx x).snd.size := by
  simp only [insertIfNewThenGetIdx]; split
  case h_1 i heq => exact getIdx?_lt_of_WF hwf heq
  case h_2 => simp

theorem empty_WF {off capacity} [LawfulMapy γ α Nat] :
  (IndexMap.emptyWithCapacity (α:=α) (γ:=γ) off capacity).WF := by
  constructor <;> intro a b <;>
    simp [IsomMap.find₁, IsomMap.find₂, getIdx?, getVal?_def, emptyWithCapacity, LawfulMapy.getElem?_empty]

open Classical in
theorem insert_WF [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α}
  (hwf : m.WF) (notin : x ∉ m) : (m.insert x).WF := by
  cases m
  case mk map ind off =>
    simp only [mem_def] at notin
    simp only [insert, size]
    constructor <;> intro a b <;>
      simp only [IsomMap.find₁, IsomMap.find₂, getVal?_def,
                 getIdx?, LawfulMapy.getElem?_insert]
    case find₁_find₂ =>
      split
      case isTrue h =>
        cases h; intro hb
        injection hb with hb; rw [← hb]; simp
      case isFalse h =>
        intro hb
        have hget? : Array.getShl? ind b off = some a := hwf.find₁_find₂ _ _ hb
        simp only [Array.getShl?] at hget?; split at hget?
        case isTrue hb =>
          have ⟨hle, hget⟩ := Array.getElem?_eq_some_iff.mp hget?
          simp [Array.getElem?_push_lt hle, hget, hb]
        case isFalse hb => cases hget?
    case find₂_find₁ =>
      split
      case isTrue hb =>
        split <;> rw [Array.getElem?_push]
        case isTrue h =>
          cases h; split
          case isTrue h =>
            have h' : b = off + ind.size := by omega
            simp [h']
          case isFalse h =>
            intro hind
            have hind' : Array.getShl? ind b off = .some x := by
              simp [Array.getShl?, hb, hind]
            have hin : map[x]? = b := hwf.find₂_find₁ _ _ hind'
            have isin : x ∈ map := LawfulMapy.mem_iff_isSome_getElem?.mpr (by rw [hin]; rfl)
            contradiction
        case isFalse h =>
          split
          case isTrue h =>
            intro ha; injection ha; contradiction
          case isFalse h =>
            intro hind; apply hwf.find₂_find₁
            simp [IsomMap.find₂, getVal?_def, hb, hind]
      case isFalse hb => intro h; cases h

theorem getIdxThenInsertIfNew?_fst_eq_getIdx? {m : IndexMap γ α} {x : α} :
  (m.getIdxThenInsertIfNew? x).fst = m.getIdx? x := by
  simp only [getIdxThenInsertIfNew?, getIdx?]
  cases m.map[x]? <;> rfl

theorem mem_getIdxThenInsertIfNew?_snd [LawfulMapy γ α Nat] {m : IndexMap γ α} {x y : α} :
  y ∈ (m.getIdxThenInsertIfNew? x).snd ↔ x = y ∨ y ∈ m := by
  simp only [getIdxThenInsertIfNew?]
  cases hmx : m.getIdx? x
  case none => simp [mem_insert]
  case some i =>
    have hxm := mem_iff_getIdx?_eq_some.mpr ⟨_, hmx⟩
    grind

theorem getIdxThenInsertIfNew?_snd_WF [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α}
  (hwf : m.WF) : (m.getIdxThenInsertIfNew? x).snd.WF := by
  rw [getIdxThenInsertIfNew?]
  cases hmx : m.getIdx? x
  case none =>
    rw [← not_mem_iff_getIdx?_eq_none] at hmx
    apply insert_WF (hwf:=hwf) (notin:=hmx)
  case some i =>
    exact hwf

theorem insertIfNewThenGetIdx_fst_eq_getIdx?_getD {m : IndexMap γ α} {x : α} :
  (m.insertIfNewThenGetIdx x).fst = (m.getIdx? x).getD (m.off + m.size) := by
  simp only [insertIfNewThenGetIdx, getIdx?]
  cases m.map[x]? <;> rfl

theorem insertIfNewThenGetIdx_snd_WF [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α}
  (hwf : m.WF) : (m.insertIfNewThenGetIdx x).snd.WF := by
  rw [insertIfNewThenGetIdx]
  cases hmx : m.getIdx? x
  case none =>
    rw [← not_mem_iff_getIdx?_eq_none] at hmx
    apply insert_WF (hwf:=hwf) (notin:=hmx)
  case some i =>
    exact hwf

theorem insertIfNewThenGetIdx_snd_eq_getIdxThenInsertIfNew?_snd {m : IndexMap γ α} {x : α} :
  (m.insertIfNewThenGetIdx x).snd = (m.getIdxThenInsertIfNew? x).snd := by
  simp only [insertIfNewThenGetIdx, getIdxThenInsertIfNew?]
  cases m.getIdx? x <;> rfl

theorem mem_insertIfNewThenGetIdx_snd [LawfulMapy γ α Nat] {m : IndexMap γ α} {x y : α} :
  y ∈ (m.insertIfNewThenGetIdx x).snd ↔ x = y ∨ y ∈ m := by
  rw [insertIfNewThenGetIdx_snd_eq_getIdxThenInsertIfNew?_snd]
  apply mem_getIdxThenInsertIfNew?_snd

@[simp]
theorem insertIfNewThenGetIdx_snd_eq_insertIfNew {m : IndexMap γ α} {x : α} :
  (m.insertIfNewThenGetIdx x).snd = m.insertIfNew x := by
  simp only [insertIfNew, insertIfNewThenGetIdx]
  cases m.getIdx? x <;> rfl

@[simp]
theorem getIdxThenInsertIfNew?_snd_eq_insertIfNew {m : IndexMap γ α} {x : α} :
  (m.getIdxThenInsertIfNew? x).snd = m.insertIfNew x := by
  simp only [insertIfNew, getIdxThenInsertIfNew?]
  cases m.getIdx? x <;> rfl

theorem insertIfNew_eq_of_getIdx?_eq_some {m : IndexMap γ α} {x : α}
  (i : Nat) (hm : m.getIdx? x = .some i) : m.insertIfNew x = m := by
  simp only [insertIfNew, hm]

theorem insertIfNew_eq_of_mem [LawfulMapy γ α Nat] {m : IndexMap γ α}
  {x : α} (hm : x ∈ m) : m.insertIfNew x = m := by
  have ⟨i, hi⟩ := mem_iff_getIdx?_eq_some.mp hm
  simp only [insertIfNew, hi]

theorem insertIfNew_eq_insert_of_getIdx?_eq_none {m : IndexMap γ α} {x : α}
  (hnm : m.getIdx? x = .none) : m.insertIfNew x = m.insert x := by
  simp only [insertIfNew, hnm]

theorem insertIfNew_eq_insert_of_not_mem [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x : α} (hnm : x ∉ m) : m.insertIfNew x = m.insert x := by
  have hn := not_mem_iff_getIdx?_eq_none.mp hnm
  simp only [insertIfNew, hn]

theorem mem_insertIfNew [LawfulMapy γ α Nat]
  {m : IndexMap γ α} {x y : α} : y ∈ m.insertIfNew x ↔ x = y ∨ y ∈ m := by
  rw [← insertIfNewThenGetIdx_snd_eq_insertIfNew]
  apply mem_insertIfNewThenGetIdx_snd

theorem insertIfNew_WF [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α}
  (hwf : m.WF) : (m.insertIfNew x).WF := by
  rw [← insertIfNewThenGetIdx_snd_eq_insertIfNew]
  apply insertIfNewThenGetIdx_snd_WF (hwf:=hwf)

@[simp]
theorem insertIfNewMany_nil {m : IndexMap γ α} :
  m.insertIfNewMany #[] = m := rfl

@[simp]
theorem insertIfNewMany_singleton {m : IndexMap γ α} (x : α) :
  m.insertIfNewMany #[x] = m.insertIfNew x := rfl

@[simp]
theorem insertIfNewMany_push {m : IndexMap γ α} {xs : Array α} {x : α} :
  m.insertIfNewMany (xs.push x) = (m.insertIfNewMany xs).insertIfNew x := by
  simp [insertIfNewMany]

@[simp]
theorem insertIfNewMany_append {m : IndexMap γ α} {xs ys : Array α} :
  m.insertIfNewMany (xs ++ ys) = (m.insertIfNewMany xs).insertIfNewMany ys := by
  simp [insertIfNewMany]

@[simp]
theorem mem_insertIfNewMany [LawfulMapy γ α Nat] {m : IndexMap γ α} {xs : Array α} {y : α} :
  y ∈ IndexMap.insertIfNewMany m xs ↔ y ∈ m ∨ y ∈ xs := by
  rw [IndexMap.insertIfNewMany]
  revert m y; induction xs using Array.push_ind
  case base => simp
  case ind IH =>
    grind [Array.foldl_push, mem_insertIfNew]

theorem insertIfNewMany_WF [LawfulMapy γ α Nat] {m : IndexMap γ α} {xs : Array α}
  (hwf : m.WF) : (m.insertIfNewMany xs).WF := by
  revert m hwf; induction xs using Array.push_ind
  case base => simp [insertIfNewMany]
  case ind head tail IH =>
    intro m hwf
    rw [insertIfNewMany_push]
    apply insertIfNew_WF
    apply IH <;> assumption

theorem getVal?_eq_none_iff {m : IndexMap γ α} {i : Nat} :
  m.getVal? i = .none ↔ i < m.off ∨ i ≥ m.off + m.size :=
  Array.getShl?_eq_none_iff

theorem getVal?_eq_some_iff {m : IndexMap γ α} {i : Nat} :
  (∃ x, m.getVal? i = .some x) ↔ i ≥ m.off ∧ i < m.off + m.size :=
  Array.getShl?_eq_some_iff

theorem getVal?_isSome_iff {m : IndexMap γ α} {i : Nat} :
  (m.getVal? i).isSome ↔ i ≥ m.off ∧ i < m.off + m.size :=
  Array.getShl?_isSome_iff

theorem getVal?_insert {m : IndexMap γ α} {x : α} {i : Nat} :
  (m.insert x).getVal? i = if i = m.off + m.size then .some x else m.getVal? i := by
  simp only [insert, getVal?, IndexMap.size, Array.getShl?_push]

theorem getVal?_insert_eq {m : IndexMap γ α} {x : α} :
  (m.insert x).getVal? (m.off + m.size) = .some x := by
  simp [getVal?_insert]

theorem getVal?_insert_ne {m : IndexMap γ α} {x : α} {i : Nat}
  (hne : i ≠ m.off + m.size) : (m.insert x).getVal? i = m.getVal? i := by
  simp [getVal?_insert, hne]

theorem getVal?_insert_lt {m : IndexMap γ α} {x : α} {i : Nat}
  (hlt : i < m.off + m.size) : (m.insert x).getVal? i = m.getVal? i := by
  rw [getVal?_insert_ne]; apply Nat.ne_of_lt hlt

theorem getVal?_insert_gt {m : IndexMap γ α} {x : α} {i : Nat}
  (hgt : i > m.off + m.size) : (m.insert x).getVal? i = m.getVal? i := by
  rw [getVal?_insert_ne]; apply Nat.ne_of_gt hgt

theorem getVal?_insert_eq_none_of_gt {m : IndexMap γ α} {x : α} {i : Nat}
  (hgt : i > m.off + m.size) : (m.insert x).getVal? i = .none := by
  rw [getVal?_insert_gt hgt]; apply getVal?_eq_none_iff.mpr
  simp [Nat.le_of_lt hgt]

open Classical in
theorem getIdx?_insert_eq [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α} :
  (m.insert x).getIdx? x = .some (m.off + m.size) := by
  simp [getIdx?, insert, LawfulMapy.getElem?_insert_self]

open Classical in
theorem getIdx?_insert_ne [LawfulMapy γ α Nat] {m : IndexMap γ α} {x y : α} (hne : x ≠ y) :
  (m.insert x).getIdx? y = m.getIdx? y := by
  simp [getIdx?, insert, LawfulMapy.getElem?_insert_ne hne]

theorem getIdx_insert_eq [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α} :
  (m.insert x).getIdx x (mem_insert.mpr (.inl rfl)) = m.off + m.size := by
  have h := getIdx?_insert_eq (m:=m) (x:=x)
  apply getIdx_eq_of_getIdx?_eq_some h

theorem getIdx_insert_ne₁ [LawfulMapy γ α Nat] {m : IndexMap γ α} {x y : α} (hne : x ≠ y) (hmem : y ∈ m) :
  (m.insert x).getIdx y (mem_insert.mpr (.inr hmem)) = m.getIdx y hmem := by
  have h := getIdx?_insert_ne (m:=m) hne
  rw [getIdx?_eq_some_getIdx hmem] at h
  apply getIdx_eq_of_getIdx?_eq_some h

theorem getIdx_insert_ne₂ [LawfulMapy γ α Nat] {m : IndexMap γ α} {x y : α} (hne : x ≠ y) (hmem : y ∈ m.insert x) :
  (m.insert x).getIdx y hmem = m.getIdx y (Or.resolve_left (mem_insert.mp hmem) hne) := by
  apply getIdx_insert_ne₁ hne

theorem getIdx_insertIfNew_eq_of_mem [LawfulMapy γ α Nat] {m : IndexMap γ α} {x y : α} (hmem : y ∈ m) :
  (m.insertIfNew x).getIdx y (mem_insertIfNew.mpr (Or.inr hmem)) = m.getIdx y hmem := by
  apply Option.some.inj
  simp only [← getIdx?_eq_some_getIdx]
  simp only [insertIfNew]; split
  case h_1 heq => rfl
  case h_2 heq => grind [not_mem_iff_getIdx?_eq_none, getIdx?_insert_ne]

theorem getIdx_insertIfNew_self_of_not_mem [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α} (hnm : x ∉ m) :
  (m.insertIfNew x).getIdx x (mem_insertIfNew.mpr (Or.inl rfl)) = m.off + m.size := by
  apply Option.some.inj
  simp only [← getIdx?_eq_some_getIdx]
  rw [insertIfNew_eq_insert_of_not_mem hnm]
  rw [getIdx?_insert_eq]

theorem getVal?_getIdx [LawfulMapy γ α Nat] {m : IndexMap γ α} {x : α} (hwf : m.WF) (h : x ∈ m) :
  m.getVal? (m.getIdx x h) = .some x := by
  have ⟨i, hi⟩ := mem_iff_getIdx?_eq_some.mp h
  rw [getIdx_eq_of_getIdx?_eq_some hi]
  apply hwf.find₁_find₂ _ _ hi

end IndexMap

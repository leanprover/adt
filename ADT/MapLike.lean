/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import ADT.List
import ADT.OptArr
import ADT.Logic
import ADT.MapLemmas
import ADT.Size
import ADT.DGetElem
import Std.Data
open Std

/-!
# Abstract datatypes for maps and dependently typed maps
-/

/-
  This section defines an abstract datatype `DMapLike` and its lawful
  counterpart `LawfulDMapLike`. An instance `inst : DMapLike γ α β` denotes
  that `γ` models a finite, dependently typed map from `α` to `β`,
  i.e. a function from a finite collection of elements of type `α`
  (i.e. the keys) to `β`.

  `DMapLike` is a subtype of `Membership` and `DGetElem?`. In addition,
  it must support the following operations: `emptyWithCapacity`,
  `insert`, `erase`, `size`
  · `a ∈ m` iff `a` is present in the keys
  · `emptyWithCapacity k` returns an empty map with capacity `k`.
    The capacity parameter is present because of performance considerations.
  · `insert m k v`: insert the key-value pair `(k, v)` to `m`. If
    `k` is already present, its value is overriden
  · `erase m k`: erase the key `k` from `m`
  · `size m`: return the size of `m`

  `LawfulDMapLike` specifies the behavior of the operations supported by
  `DMapLike`, whereby the behavior of the operations are uniquely determined
  up to `DMapLike.equiv`.
-/

section DMapLike

class DMapLike (γ : Type u) (α : Type v) (β : α → Type w) extends
  Membership α γ, DGetElem? γ α β (fun m x => x ∈ m), Size γ where
  emptyWithCapacity {γ α β} : Nat → γ
  insert : γ → (x : α) → (y : β x) → γ
  erase {γ α β} : γ → α → γ

def DMapLike.keyEquiv {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  (m₁ : γ₁) (m₂ : γ₂) := ∀ (x : α), x ∈ m₁ ↔ x ∈ m₂

def DMapLike.equiv {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  keyEquiv (β:=β) m₁ m₂ ∧ ∀ (x : α) (h₁ : x ∈ m₁) (h₂ : x ∈ m₂), m₁[x]ᵈ'h₁ = m₂[x]ᵈ'h₂

def DMapLike.equiv' {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α), m₁[x]ᵈ? = m₂[x]ᵈ?

def DMapLike.keySubset {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α), x ∈ m₁ → x ∈ m₂

def DMapLike.subset {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α) (y : β x), m₁[x]ᵈ? = .some y → m₂[x]ᵈ? =.some y

theorem DMapLike.keyEquiv.refl {γ α β} [inst : DMapLike γ α β] {m : γ} : keyEquiv (β:=β) m m := by
  simp [keyEquiv]

theorem DMapLike.keyEquiv.comm {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (β:=β) m₁ m₂ ↔ keyEquiv (β:=β) m₂ m₁ := by
  simp only [keyEquiv]
  conv => left; enter [x]; rw [Iff.comm]

theorem DMapLike.keyEquiv.symm {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (β:=β) m₁ m₂ → keyEquiv (β:=β) m₂ m₁ :=
  DMapLike.keyEquiv.comm.mp

theorem DMapLike.keyEquiv.trans {γ₁ γ₂ γ₃ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] [inst₃ : DMapLike γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : keyEquiv (β:=β) m₁ m₂ → keyEquiv (β:=β) m₂ m₃ → keyEquiv (β:=β) m₁ m₃ := by
  intro h₁ h₂ x
  rw [h₁, h₂]

theorem DMapLike.equiv.refl {γ α β} [inst : DMapLike γ α β] {m : γ} : equiv (β:=β) m m := by
  simp [equiv, keyEquiv]

theorem DMapLike.equiv.comm {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (β:=β) m₁ m₂ ↔ equiv (β:=β) m₂ m₁ := by
  simp only [equiv, keyEquiv.comm (m₁:=m₁)]
  conv => enter [1, 2, x]; rw [forall_comm]
  conv => enter [1, 2, x, h₁, h₂]; rw [Eq.comm]

theorem DMapLike.equiv.symm {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (β:=β) m₁ m₂ → equiv (β:=β) m₂ m₁ :=
  DMapLike.equiv.comm.mp

theorem DMapLike.equiv.trans {γ₁ γ₂ γ₃ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] [inst₃ : DMapLike γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv (β:=β) m₁ m₂ → equiv (β:=β) m₂ m₃ → equiv (β:=β) m₁ m₃ := by
  intro h₁ h₂; apply And.intro
  case left => intro x; rw [h₁.left, h₂.left]
  case right =>
    intro x h₁' h₃'
    have h₂' := by rw [← h₂.left] at h₃'; exact h₃'
    rw [h₁.right _ h₁' h₂', h₂.right _ h₂' h₃']

theorem DMapLike.equiv'.refl {γ α β} [inst : DMapLike γ α β] {m : γ} : equiv' (β:=β) m m := by
  simp [equiv']

theorem DMapLike.equiv'.comm {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (β:=β) m₁ m₂ ↔ equiv' (β:=β) m₂ m₁ := by
  simp only [equiv']
  conv => left; enter [x]; rw [Eq.comm]

theorem DMapLike.equiv'.symm {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (β:=β) m₁ m₂ → equiv' (β:=β) m₂ m₁ :=
  DMapLike.equiv'.comm.mp

theorem DMapLike.equiv'.trans {γ₁ γ₂ γ₃ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] [inst₃ : DMapLike γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv' (β:=β) m₁ m₂ → equiv' (β:=β) m₂ m₃ → equiv' (β:=β) m₁ m₃ := by
  intro h₁ h₂ x; rw [h₁, h₂]

theorem DMapLike.keyEquiv_iff_keySubset {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (β:=β) m₁ m₂ ↔ keySubset (β:=β) m₁ m₂ ∧ keySubset (β:=β) m₂ m₁ := by
  simp only [keySubset, keyEquiv]; apply Iff.intro <;> intro h
  case mp => simp [h]
  case mpr => intro x; apply Iff.intro <;> simp_all

theorem DMapLike.equiv'_iff_subset {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (β:=β) m₁ m₂ ↔ subset (β:=β) m₁ m₂ ∧ subset (β:=β) m₂ m₁ := by
  simp only [subset, equiv']; apply Iff.intro <;> intro h
  case mp => simp [h]
  case mpr =>
    intro x
    have h₁ := h.left x; have h₂ := h.right x
    revert h₁ h₂ <;> cases m₁[x]ᵈ? <;> cases m₂[x]ᵈ? <;> simp

open DMapLike

/--
  A finite dependently typed map where the behavior of
  `· ∈ m , m[·]?, m[·]!, m[·], emptyWithCapacity, insert, erase, size`
  are uniquely determined up to `Map.equiv`
-/
class LawfulDMapLike (γ : Type u) (α : Type v) (β : α → Type w) [inst : DMapLike γ α β]
  extends LawfulMemSize γ α, LawfulDGetElem γ α β (fun m x => x ∈ m) where
  not_mem_empty : ∀ {k : α} {n : Nat}, ¬ k ∈ emptyWithCapacity (self:=inst) n
  mem_iff_isSome_dGetElem? : ∀ {m : γ} {k : α}, k ∈ m ↔ m[k]ᵈ?.isSome
  dGetElem?_insert_self : ∀ {m : γ} {k : α} {v : β k}, (insert m k v)[k]ᵈ? = .some v
  dGetElem?_insert_ne : ∀ {m : γ} {k a : α} {v : β k}, k ≠ a → (insert m k v)[a]ᵈ? = m[a]ᵈ?
  dGetElem?_erase_self : ∀ {m : γ} {k : α}, (erase (β:=β) m k)[k]ᵈ? = .none
  dGetElem?_erase_ne : ∀ {m : γ} {k a : α}, k ≠ a → (erase (β:=β) m k)[a]ᵈ? = m[a]ᵈ?
  size_erase_mem : ∀ {m : γ} {k : α}, k ∈ m → Size.size (erase (β:=β) m k) + 1 = Size.size m

theorem LawfulDMapLike.mem_iff_dGetElem?_eq_some {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} : k ∈ m ↔ ∃ v, m[k]ᵈ? = .some v := by
  rw [mem_iff_isSome_dGetElem?]; rw [Option.isSome_iff_exists]

theorem LawfulDMapLike.not_mem_iff_dGetElem?_eq_none {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} : k ∉ m ↔ m[k]ᵈ? = .none := by
  rw [mem_iff_isSome_dGetElem?]; simp

theorem LawfulDMapLike.mem_insert {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k a : α} {v : β k} :
  a ∈ insert m k v ↔ (k = a) ∨ a ∈ m := by
  rw [mem_iff_isSome_dGetElem?]; by_cases k = a
  case pos h => cases h; simp [dGetElem?_insert_self]
  case neg h => simp only [dGetElem?_insert_ne h]; simp [← mem_iff_isSome_dGetElem?, *]

theorem LawfulDMapLike.mem_erase {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k a : α} :
  a ∈ erase (β:=β) m k ↔ k ≠ a ∧ a ∈ m := by
  rw [mem_iff_isSome_dGetElem?]; by_cases k = a
  case pos h => cases h; simp [dGetElem?_erase_self]
  case neg h => simp only [dGetElem?_erase_ne h]; simp [← mem_iff_isSome_dGetElem?, h]

open Classical in
theorem LawfulDMapLike.dGetElem?_eq_none_iff {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β]
  {c : γ} {i : α} : c[i]ᵈ? = .none ↔ i ∉ c := by
  simp only [dGetElem?_def]
  split <;> simp_all

open Classical in
theorem LawfulDMapLike.dGetElem?_eq_some_dGetElem {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} (h : k ∈ m) :
  m[k]ᵈ? = .some (m[k]ᵈ'h) := by
  simp [dGetElem?_def, h]

theorem LawfulDMapLike.dGetElem!_eq_dGetElem {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} [Inhabited (β k)] (h : k ∈ m) :
  m[k]ᵈ! = m[k]ᵈ'h := by
  simp [dGetElem!_def, dGetElem?_eq_some_dGetElem h]

theorem LawfulDMapLike.dGetElem!_eq_default {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} [Inhabited (β k)] (h : k ∉ m) :
  m[k]ᵈ! = default := by
  simp [dGetElem!_def, dGetElem?_eq_none_iff.mpr h]

theorem LawfulDMapLike.dGetElem!_eq_get!_dGetElem? {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} [Inhabited (β k)] : m[k]ᵈ! = m[k]ᵈ?.get! := by
  simp only [dGetElem!_def]; split <;> simp [*]

theorem LawfulDMapLike.dGetElem?_eq_some_dGetElem! {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} [Inhabited (β k)] (h : k ∈ m) :
  m[k]ᵈ? = .some m[k]ᵈ! := by
  simp [dGetElem?_eq_some_dGetElem h, dGetElem!_eq_dGetElem h]

theorem LawfulDMapLike.dGetElem?_eq_none {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} [Inhabited (β k)] (h : k ∉ m) :
  m[k]ᵈ? = .none := by
  simp [dGetElem?_eq_none_iff.mpr h]

theorem LawfulDMapLike.dGetElem_eq_iff_dGetElem?_eq_some {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} {v : β k} (h : k ∈ m) :
  m[k]ᵈ'h = v ↔ m[k]ᵈ? = .some v := by
  rw [dGetElem?_eq_some_dGetElem h]; simp

theorem LawfulDMapLike.dGetElem_eq_of_dGetElem?_eq_some {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} {v : β k}
  (h : m[k]ᵈ? = .some v) : m[k]ᵈ'(mem_iff_dGetElem?_eq_some.mpr ⟨_, h⟩) = v := by
  apply (LawfulDMapLike.dGetElem_eq_iff_dGetElem?_eq_some _).mpr h

theorem LawfulDMapLike.dGetElem_eq_dGetElem_iff_dGetElem?_eq_dGetElem? {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m₁ m₂ : γ} {k : α}
  (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) : m₁[k]ᵈ'h₁ = m₂[k]ᵈ'h₂ ↔ m₁[k]ᵈ? = m₂[k]ᵈ? := by
  rw [dGetElem?_eq_some_dGetElem h₁, dGetElem?_eq_some_dGetElem h₂]; simp

theorem LawfulDMapLike.dGetElem_insert_self {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k : α} {v : β k} :
  (insert m k v)[k]ᵈ'(mem_insert.mpr (Or.inl rfl)) = v := by
  have hmem : k ∈ insert m k v := mem_insert.mpr (Or.inl rfl)
  have heq := dGetElem?_eq_some_dGetElem hmem
  rw [dGetElem?_insert_self] at heq
  injection heq with heq; rw [← heq]

theorem LawfulDMapLike.dGetElem_insert_ne {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k a : α} {v : β k} (h₁ : a ∈ insert m k v) (h₂ : k ≠ a) :
  (insert m k v)[a]ᵈ'h₁ = m[a]ᵈ'(Or.resolve_left (mem_insert.mp h₁) h₂) := by
  have heq := dGetElem?_eq_some_dGetElem h₁
  have heq' := dGetElem?_eq_some_dGetElem (Or.resolve_left (mem_insert.mp h₁) h₂)
  rw [dGetElem?_insert_ne h₂, heq'] at heq
  injection heq with heq; rw [← heq]

theorem LawfulDMapLike.dGetElem_erase {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} {k a : α} (h' : a ∈ erase m k) :
  (erase (β:=β) m k)[a]ᵈ'h' = m[a]ᵈ'((mem_erase.mp h').right) := by
  have heq := dGetElem?_eq_some_dGetElem h'
  have heq' := dGetElem?_eq_some_dGetElem (mem_erase.mp h').right
  by_cases k = a
  case pos h => cases h; simp [dGetElem?_erase_self] at heq
  case neg h =>
    simp only [dGetElem?_erase_ne h, heq'] at heq
    injection heq with heq; rw [← heq]

theorem LawfulDMapLike.insert_mem_keyEquiv {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β]
  {m : γ} {k : α} {v : β k} (hmem : k ∈ m) : keyEquiv (β:=β) (insert m k v) m := by
  simp [keyEquiv, mem_insert, hmem]

theorem LawfulDMapLike.erase_insert_not_mem_equiv {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β]
  {m : γ} {k : α} {v : β k} (hnmem : k ∉ m) : equiv (β:=β) (erase (β:=β) (insert m k v) k) m := by
  simp only [equiv, keyEquiv, mem_erase, mem_insert, dGetElem_erase]
  apply And.intro
  case left => intro x; by_cases (k = x) <;> simp_all
  case right => intro x ⟨hne, h₁⟩ h₂; simp [dGetElem_insert_ne _ hne]

theorem LawfulDMapLike.erase_not_mem_equiv {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β]
  {m : γ} {k : α} (hnmem : k ∉ m) : equiv (β:=β) (erase (β:=β) m k) m := by
  simp only [equiv, keyEquiv, mem_erase, dGetElem_erase]
  apply And.intro
  case left => intro x; by_cases (k = x) <;> simp_all
  case right => simp

theorem LawfulDMapLike.insert_erase_mem_keyEquiv {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β]
  {m : γ} {k : α} {v : β k} (hmem : k ∈ m) : keyEquiv (β:=β) (insert (erase (β:=β) m k) k v) m := by
  simp only [keyEquiv, mem_insert, mem_erase]
  intro x; by_cases (k = x) <;> simp_all

theorem LawfulDMapLike.insert_erase_dGetElem_eq_equiv {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β]
  {m : γ} {k : α} {v : β k} (hmem : k ∈ m) (hget : m[k]ᵈ'hmem = v) : equiv (β:=β) (insert (erase (β:=β) m k) k v) m := by
  simp only [equiv, keyEquiv, mem_insert, mem_erase]
  apply And.intro
  case left => intro x; grind
  case right =>
    intro x h₁ h₂; cases h₁
    case inl heq => cases heq; simp [dGetElem_insert_self, hget]
    case inr hne => simp [dGetElem_insert_ne _ hne.left, dGetElem_erase]

theorem LawfulDMapLike.exists_key_list {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} :
  ∃ (l : List α), l.length = Size.size m ∧ l.Nodup ∧ ∀ k, k ∈ m ↔ k ∈ l := by
  generalize hsz : Size.size m = n
  induction n generalizing m
  case zero =>
    exists []; simp [LawfulMemSize.size_zero_iff_forall_not_mem.mp hsz]
  case succ n IH =>
    have hnz : Size.size m ≠ 0 := by
      intro h; rw [h] at hsz; simp at hsz
    have ⟨x, hx⟩ := LawfulMemSize.size_ne_zero_iff_exists_mem.mp hnz
    let me := erase (β:=β) m x
    have hmesz : Size.size (erase (β:=β) m x) = n := by
      have := (size_erase_mem hx).trans hsz; simp_all
    have ⟨l, hlen, hnd, hequiv⟩ := IH hmesz
    exists x::l
    apply And.intro ?len (And.intro ?nd ?equiv)
    case len => simp [hlen]
    case nd => simp [← hequiv, hnd, mem_erase]
    case equiv =>
      simp only [List.mem_cons, ← hequiv, mem_erase]
      intro k; apply Iff.intro
      case mp => intro hk; grind
      case mpr => intro hk; cases hk <;> simp [*]

noncomputable def LawfulDMapLike.exKeyList {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] (m : γ) : List α :=
  (exists_key_list (α:=α) (β:=β) (m:=m)).choose

noncomputable def LawfulDMapLike.length_exKeyList_eq_size {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} :
  (exKeyList (α:=α) (β:=β) m).length = Size.size m :=
  (Exists.choose_spec exists_key_list).left

noncomputable def LawfulDMapLike.length_exKeyList_nodup {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} :
  (exKeyList (α:=α) (β:=β) m).Nodup :=
  (Exists.choose_spec exists_key_list).right.left

noncomputable def LawfulDMapLike.length_exKeyList_equiv {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ} :
  ∀ k, k ∈ m ↔ k ∈ (exKeyList (α:=α) (β:=β) m) :=
  (Exists.choose_spec exists_key_list).right.right

theorem LawfulDMapLike.size_le_of_keySubset {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hsub : keySubset (β:=β) m₁ m₂) : Size.size m₁ ≤ Size.size m₂ := by
  let ⟨l₁, heq₁, hnd₁, hequiv₁⟩ := exists_key_list (inst:=inst₁) (m:=m₁)
  let ⟨l₂, heq₂, hnd₂, hequiv₂⟩ := exists_key_list (inst:=inst₂) (m:=m₂)
  rw [← heq₁, ← heq₂]
  apply List.length_le_of_subset hnd₁
  intro x hx
  rw [← hequiv₂]; apply hsub; rw [hequiv₁]; exact hx

theorem LawfulDMapLike.size_eq_of_keyEquiv {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : keyEquiv (β:=β) m₁ m₂) : Size.size m₁ = Size.size m₂ := by
  rw [keyEquiv_iff_keySubset] at hequiv
  have h₁ := size_le_of_keySubset hequiv.left
  have h₂ := size_le_of_keySubset hequiv.right
  omega

theorem LawfulDMapLike.keyEquiv_iff_size_eq_and_keySubset {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂} :
  keyEquiv (β:=β) m₁ m₂ ↔ Size.size m₁ = Size.size m₂ ∧ keySubset (β:=β) m₁ m₂ := by
  let ⟨l₁, heq₁, hnd₁, hequiv₁⟩ := exists_key_list (β:=β) (m:=m₁)
  let ⟨l₂, heq₂, hnd₂, hequiv₂⟩ := exists_key_list (β:=β) (m:=m₂)
  simp only [keyEquiv, keySubset]
  rw [← heq₁, ← heq₂]; simp only [hequiv₁, hequiv₂]
  simp only [← List.nodup_perm_iff_equiv hnd₁ hnd₂,
             ← List.subset_def,
             ← List.nodup_subPerm_iff_subset hnd₁ hnd₂]
  apply List.perm_iff_length_eq_andsubPerm

theorem LawfulDMapLike.size_insert_mem {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ}
  {k : α} {v : β k} (hmem : k ∈ m) : Size.size (insert m k v) = Size.size m := by
  apply size_eq_of_keyEquiv; apply insert_mem_keyEquiv hmem

theorem LawfulDMapLike.size_insert_not_mem {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ}
  {k : α} {v : β k} (hnmem : k ∉ m) : Size.size (insert m k v) = Size.size m + 1 := by
  have hke := erase_insert_not_mem_equiv hnmem (v:=v)
  rw [← size_eq_of_keyEquiv hke.left]; symm
  apply size_erase_mem; simp [mem_insert]

theorem LawfulDMapLike.size_insert_le {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ}
  {k : α} {v : β k} : Size.size (insert m k v) ≤ Size.size m + 1 := by
  by_cases k ∈ m
  case pos h => rw [size_insert_mem h]; simp
  case neg h => rw [size_insert_not_mem h]; exact .refl

theorem LawfulDMapLike.le_size_insert {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ}
  {k : α} {v : β k} : Size.size m ≤ Size.size (insert m k v) := by
  by_cases k ∈ m
  case pos h => rw [size_insert_mem h]; exact .refl
  case neg h => rw [size_insert_not_mem h]; simp

theorem LawfulDMapLike.size_insert_gt_zero {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ}
  {k : α} {v : β k} : Size.size (insert m k v) > 0 := by
  by_cases k ∈ m
  case pos h => rw [size_insert_mem h]; apply LawfulMemSize.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
  case neg h => rw [size_insert_not_mem h]; simp

theorem LawfulDMapLike.size_erase_not_mem {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ}
  {k : α} (hnm : k ∉ m) : Size.size (erase (β:=β) m k) = Size.size m := by
  apply size_eq_of_keyEquiv; apply (erase_not_mem_equiv hnm).left

theorem LawfulDMapLike.size_erase_le {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ}
  {k : α} : Size.size (erase (β:=β) m k) ≤ Size.size m := by
  by_cases k ∈ m
  case pos h => have := size_erase_mem h; omega
  case neg h => rw [size_erase_not_mem h]; exact .refl

theorem LawfulDMapLike.le_size_erase {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β] {m : γ}
  {k : α} : Size.size m ≤ Size.size (erase (β:=β) m k) + 1 := by
  by_cases k ∈ m
  case pos h => simp [size_erase_mem h]
  case neg h => rw [size_erase_not_mem h]; simp

theorem LawfulDMapLike.dGetElem?_empty {γ α β} [inst : DMapLike γ α β] [LawfulDMapLike γ α β]
  {capacity : Nat} {k : α} : (emptyWithCapacity (γ:=γ) (β:=β) capacity)[k]ᵈ? = .none := by
  rw [← not_mem_iff_dGetElem?_eq_none]; apply not_mem_empty

theorem LawfulDMapLike.dGetElem?_insert {γ α β} [inst : DMapLike γ α β]
  [LawfulDMapLike γ α β] [DecidableEq α] {m : γ} {k a : α} {v : β k} :
  (insert m k v)[a]ᵈ? = if h : k = a then h ▸ some v else m[a]ᵈ? := by
  by_cases (a ∈ insert m k v)
  case pos h =>
    rw [mem_insert] at h; by_cases (k = a)
    case pos heq => cases heq; simp [dGetElem?_insert_self]
    case neg heq => simp [dGetElem?_insert_ne heq, heq]
  case neg h =>
    rw [not_mem_iff_dGetElem?_eq_none.mp h]
    rw [mem_insert, not_or] at h
    simp [not_mem_iff_dGetElem?_eq_none.mp h.right, h.left]

theorem LawfulDMapLike.dGetElem?_erase {γ α β} [inst : DMapLike γ α β]
  [LawfulDMapLike γ α β] [DecidableEq α] {m : γ} {k a : α} :
  (erase (β:=β) m k)[a]ᵈ? = if (k = a) then .none else m[a]ᵈ? := by
  by_cases k = a
  case pos h => cases h; simp [dGetElem?_erase_self]
  case neg h => simp [dGetElem?_erase_ne h, h]

open Classical in
theorem LawfulDMapLike.dGetElem?_eq_none_iff_dGetElem?_eq_none_of_keyEquiv {γ₁ γ₂ α β}
  [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (hequiv : DMapLike.keyEquiv (β:=β) m₁ m₂)
  (k : α) : m₁[k]ᵈ? = .none ↔ m₂[k]ᵈ? = .none := by
  simp [dGetElem?_eq_none_iff, hequiv k]

theorem LawfulDMapLike.equiv_iff_equiv' {γ₁ γ₂ α β}
  [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} :
  DMapLike.equiv (β:=β) m₁ m₂ ↔ DMapLike.equiv' (β:=β) m₁ m₂ := by
  simp only [equiv, equiv']; apply Iff.intro
  case mp =>
    intro ⟨hk, hv⟩ x
    cases h₁ : m₁[x]ᵈ?
    case none =>
      simp [(dGetElem?_eq_none_iff_dGetElem?_eq_none_of_keyEquiv hk _).mp h₁]
    case some =>
      have hxm₁ := @mem_iff_dGetElem?_eq_some.mpr ⟨_, h₁⟩
      rw [dGetElem?_eq_some_dGetElem hxm₁,
          hv _ hxm₁ ((hk _).mp hxm₁), ← dGetElem?_eq_some_dGetElem] at h₁
      simp [h₁]
  case mpr =>
    intro h?; apply And.intro
    case left => intro x; simp [mem_iff_dGetElem?_eq_some, h?]
    case right =>
      intro x h₁ h₂
      apply Option.some.inj
      simp only [← dGetElem?_eq_some_dGetElem, h?]

theorem LawfulDMapLike.equiv_iff_subset {γ₁ γ₂ α β}
  [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (β:=β) m₁ m₂ ↔ subset (β:=β) m₁ m₂ ∧ subset (β:=β) m₂ m₁ := by
  rw [LawfulDMapLike.equiv_iff_equiv', DMapLike.equiv'_iff_subset]

theorem LawfulDMapLike.keySubset_of_subset {γ₁ γ₂ α β}
  [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β] [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (h : subset (β:=β) m₁ m₂) : keySubset (β:=β) m₁ m₂ := by
  simp only [subset] at h
  intro x
  simp only [mem_iff_isSome_dGetElem?]
  have hx := h x
  revert hx
  cases m₁[x]ᵈ? <;> grind

theorem LawfulDMapLike.mem_congr {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) : x ∈ m₁ ↔ x ∈ m₂ := hequiv.left _

theorem LawfulDMapLike.dGetElem?_congr {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) : m₁[x]ᵈ? = m₂[x]ᵈ? :=
  LawfulDMapLike.equiv_iff_equiv'.mp hequiv _

theorem LawfulDMapLike.dGetElem_congr {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) (h₁ : x ∈ m₁) (h₂ : x ∈ m₂) : m₁[x]ᵈ'h₁ = m₂[x]ᵈ'h₂ := by
  have heq := LawfulDMapLike.dGetElem?_congr hequiv x
  simp only [dGetElem?_eq_some_dGetElem h₁,
             dGetElem?_eq_some_dGetElem h₂] at heq
  injection heq

theorem LawfulDMapLike.dGetElem_congr' {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) (h₁ : x ∈ m₁) : m₁[x]ᵈ'h₁ = m₂[x]ᵈ'((hequiv.left _).mp h₁) := by
  have heq := LawfulDMapLike.dGetElem?_congr hequiv x
  simp only [dGetElem?_eq_some_dGetElem h₁,
             dGetElem?_eq_some_dGetElem ((hequiv.left _).mp h₁)] at heq
  injection heq

theorem LawfulDMapLike.dGetElem!_congr {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) [Inhabited (β x)] : m₁[x]ᵈ! = m₂[x]ᵈ! := by
  simp [dGetElem!_def, LawfulDMapLike.dGetElem?_congr hequiv]

theorem LawfulDMapLike.emptyWithCapacity_congr {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] (capacity₁ capacity₂ : Nat) :
  equiv (β:=β) (inst₂:=inst₂)
    (emptyWithCapacity (self:=inst₁) capacity₁)
    (emptyWithCapacity (self:=inst₂) capacity₂) := by
  rw [equiv_iff_equiv']; intro x
  simp [dGetElem?_empty]

open Classical in
theorem LawfulDMapLike.insert_congr {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (k : α) (v : β k) :
  equiv (β:=β) (insert m₁ k v) (insert m₂ k v) := by
  rw [equiv_iff_equiv']
  intro x
  simp [dGetElem?_insert, equiv_iff_equiv'.mp hequiv _]

open Classical in
theorem LawfulDMapLike.erase_congr {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (k : α) :
  equiv (β:=β) (erase m₁ (self:=inst₁) k) (erase m₂ (self:=inst₂) k) := by
  rw [equiv_iff_equiv']
  intro x
  simp [dGetElem?_erase, equiv_iff_equiv'.mp hequiv _]

theorem LawfulDMapLike.size_congr {γ₁ γ₂ α β} [inst₁ : DMapLike γ₁ α β] [inst₂ : DMapLike γ₂ α β]
  [LawfulDMapLike γ₁ α β] [LawfulDMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) : Size.size m₁ = Size.size m₂ := by
  apply LawfulDMapLike.size_eq_of_keyEquiv; exact hequiv.left

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : DMapLike (DHashMap α β) α β where
  emptyWithCapacity capacity := DHashMap.emptyWithCapacity (capacity:=capacity)
  insert := DHashMap.insert
  erase := DHashMap.erase
  size := DHashMap.size

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : LawfulDMapLike (DHashMap α β) α β where
  not_mem_empty := by intro k n; simp [DMapLike.emptyWithCapacity]
  mem_iff_isSome_dGetElem? := DHashMap.mem_iff_isSome_get?
  dGetElem?_insert_self := DHashMap.get?_insert_self
  dGetElem?_insert_ne := by
    intro m k a v h
    simp [DMapLike.insert, dGetElem?, DHashMap.get?_insert, h]
  dGetElem?_erase_self := DHashMap.get?_erase_self
  dGetElem?_erase_ne := by
    intro m k a h
    simp [DMapLike.erase, dGetElem?, DHashMap.get?_erase, h]
  size_zero_iff_forall_not_mem := by
    intro m; simp only [Size.size]
    apply DHashMap.size_zero_iff_forall_not_mem
  size_erase_mem := DHashMap.size_erase_mem

instance {α β} [Ord α] [LawfulEqOrd α] : DMapLike (DTreeMap α β) α β where
  emptyWithCapacity _ := DTreeMap.empty
  insert := DTreeMap.insert
  erase := DTreeMap.erase
  size := DTreeMap.size

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulDMapLike (DTreeMap α β) α β where
  not_mem_empty := DTreeMap.not_mem_emptyc
  mem_iff_isSome_dGetElem? := DTreeMap.mem_iff_isSome_get?
  dGetElem?_insert_self := DTreeMap.get?_insert_self
  dGetElem?_insert_ne := by
    intro m k a v hne
    simp only [DMapLike.insert, dGetElem?, DTreeMap.get?_insert]
    rw [dite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  dGetElem?_erase_self := DTreeMap.get?_erase_self
  dGetElem?_erase_ne := by
    intro m k a hne
    simp only [DMapLike.erase, dGetElem?, DTreeMap.get?_erase]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← DTreeMap.isEmpty_iff_forall_not_mem,
        DTreeMap.isEmpty_eq_size_eq_zero]
    simp [Size.size]
  size_erase_mem := DTreeMap.size_erase_mem

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : DMapLike (ExtDHashMap α β) α β where
  emptyWithCapacity capacity := ExtDHashMap.emptyWithCapacity capacity
  insert := ExtDHashMap.insert
  erase := ExtDHashMap.erase
  size := ExtDHashMap.size

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : LawfulDMapLike (ExtDHashMap α β) α β where
  not_mem_empty := by
    intro k n; simp [DMapLike.emptyWithCapacity]
    apply ExtDHashMap.not_mem_empty
  mem_iff_isSome_dGetElem? := ExtDHashMap.mem_iff_isSome_get?
  dGetElem?_insert_self := ExtDHashMap.get?_insert_self
  dGetElem?_insert_ne := by
    intros m k a v hne
    simp [DMapLike.insert, dGetElem?, ExtDHashMap.get?_insert, hne]
  dGetElem?_erase_self := ExtDHashMap.get?_erase_self
  dGetElem?_erase_ne := by
    intros m k a hne
    simp [DMapLike.erase, dGetElem?, ExtDHashMap.get?_erase, hne]
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtDHashMap.eq_empty_iff_forall_not_mem,
        ExtDHashMap.eq_empty_iff_size_eq_zero]
    rfl
  size_erase_mem := ExtDHashMap.size_erase_mem

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : DMapLike (ExtDTreeMap α β) α β where
  emptyWithCapacity _ := ExtDTreeMap.empty
  insert := ExtDTreeMap.insert
  erase := ExtDTreeMap.erase
  size := ExtDTreeMap.size

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulDMapLike (ExtDTreeMap α β) α β where
  not_mem_empty := DTreeMap.not_mem_emptyc
  mem_iff_isSome_dGetElem? := ExtDTreeMap.mem_iff_isSome_get?
  dGetElem?_insert_self := ExtDTreeMap.get?_insert_self
  dGetElem?_insert_ne := by
    intro m k a v hne
    simp only [DMapLike.insert, dGetElem?, ExtDTreeMap.get?_insert]
    rw [dite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  dGetElem?_erase_self := ExtDTreeMap.get?_erase_self
  dGetElem?_erase_ne := by
    intro m k a hne
    simp only [DMapLike.erase, dGetElem?, ExtDTreeMap.get?_erase]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtDTreeMap.isEmpty_iff_forall_not_mem,
        ExtDTreeMap.isEmpty_eq_size_eq_zero]
    simp [Size.size]
  size_erase_mem := ExtDTreeMap.size_erase_mem

end DMapLike

/-
  This section defines an abstract datatype `MapLike` and its lawful
  counterpart `LawfulMapLike`. An instance `inst : MapLike γ α β` denotes
  that `γ` models a finite map from `α` to `β`, i.e. a function
  from a finite collection of elements of type `α` (i.e. the keys) to `β`.

  `MapLike` is a subtype of `Membership` and `GetElem?`. Therefore,
  `γ` must support `∈` and `[ ], [ ]?, [ ]!`. In addition, it
  must support the following operations: `emptyWithCapacity`,
  `insert`, `erase`, `size`
  · `a ∈ m` iff `a` is present in the keys
  · `emptyWithCapacity k` returns an empty map with capacity `k`.
    The capacity parameter is present because of performance considerations.
  · `insert m k v`: insert the key-value pair `(k, v)` to `m`. If
    `k` is already present, its value is overriden
  · `erase m k`: erase the key `k` from `m`
  · `size m`: return the size of `m`

  `LawfulMapLike` specifies the behavior of the operations supported by
  `MapLike`, whereby the behavior of the operations are uniquely determined
  up to `MapLike.equiv`.
-/

section MapLike

/--
  A finite map which supports insertion, deletion, lookup,
  and computing size
-/
class MapLike (γ : Type u) (α : Type v) (β : Type w) extends
  Membership α γ, GetElem? γ α β (fun m x => x ∈ m), Size γ where
  emptyWithCapacity {γ α β} : Nat → γ
  insert : γ → α → β → γ
  erase {γ α β} : γ → α → γ

def MapLike_of_DMapLike {γ α β} (inst : DMapLike γ α (fun _ => β)) : MapLike γ α β where
  getElem := inst.dGetElem
  getElem? := inst.dGetElem?
  getElem! c i := inst.dGetElem! c i
  emptyWithCapacity := inst.emptyWithCapacity
  insert := inst.insert
  erase := inst.erase
  size := inst.size

def DMapLike_of_MapLike {γ α β} (inst : MapLike γ α β) : DMapLike γ α (fun _ => β) where
  dGetElem := inst.getElem
  dGetElem? := inst.getElem?
  dGetElem! c i := inst.getElem! c i
  emptyWithCapacity := inst.emptyWithCapacity
  insert := inst.insert
  erase := inst.erase
  size := inst.size

def DMapLike_MapLike_inv {γ α β} {inst : DMapLike γ α (fun _ => β)} :
  DMapLike_of_MapLike (MapLike_of_DMapLike inst) = inst := rfl

def MapLike_DMapLike_inv {γ α β} {inst : MapLike γ α β} :
  MapLike_of_DMapLike (DMapLike_of_MapLike inst) = inst := rfl

def MapLike.keyEquiv {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  (m₁ : γ₁) (m₂ : γ₂) := ∀ (x : α), x ∈ m₁ ↔ x ∈ m₂

def MapLike.equiv {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  keyEquiv (α:=α) (β:=β) m₁ m₂ ∧ ∀ (x : α) (h₁ : x ∈ m₁) (h₂ : x ∈ m₂), m₁[x] = m₂[x]

def MapLike.equiv' {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α), m₁[x]? = m₂[x]?

def MapLike.keySubset {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α), x ∈ m₁ → x ∈ m₂

def MapLike.subset {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α) (y : β), m₁[x]? = y → m₂[x]? = y

theorem MapLike.keyEquiv.refl {γ α β} [inst : MapLike γ α β] {m : γ} : keyEquiv (α:=α) (β:=β) m m := by
  simp [keyEquiv]

theorem MapLike.keyEquiv.comm {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (α:=α) (β:=β) m₁ m₂ ↔ keyEquiv (α:=α) (β:=β) m₂ m₁ :=
  DMapLike.keyEquiv.comm (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂)

theorem MapLike.keyEquiv.symm {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (α:=α) (β:=β) m₁ m₂ → keyEquiv (α:=α) (β:=β) m₂ m₁ :=
  MapLike.keyEquiv.comm.mp

theorem MapLike.keyEquiv.trans {γ₁ γ₂ γ₃ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] [inst₃ : MapLike γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : keyEquiv (α:=α) (β:=β) m₁ m₂ → keyEquiv (α:=α) (β:=β) m₂ m₃ → keyEquiv (α:=α) (β:=β) m₁ m₃ := by
  intro h₁ h₂ x
  rw [h₁, h₂]

theorem MapLike.equiv.refl {γ α β} [inst : MapLike γ α β] {m : γ} : equiv (α:=α) (β:=β) m m := by
  simp [equiv, keyEquiv]

theorem MapLike.equiv.comm {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (α:=α) (β:=β) m₁ m₂ ↔ equiv (α:=α) (β:=β) m₂ m₁ :=
  DMapLike.equiv.comm (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂)

theorem MapLike.equiv.symm {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (α:=α) (β:=β) m₁ m₂ → equiv (α:=α) (β:=β) m₂ m₁ :=
  MapLike.equiv.comm.mp

theorem MapLike.equiv.trans {γ₁ γ₂ γ₃ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] [inst₃ : MapLike γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv (α:=α) (β:=β) m₁ m₂ → equiv (α:=α) (β:=β) m₂ m₃ → equiv (α:=α) (β:=β) m₁ m₃ :=
  DMapLike.equiv.trans (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) (inst₃:=DMapLike_of_MapLike inst₃)

theorem MapLike.equiv'.refl {γ α β} [inst : MapLike γ α β] {m : γ} : equiv' (α:=α) (β:=β) m m := by
  simp [equiv']

theorem MapLike.equiv'.comm {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (α:=α) (β:=β) m₁ m₂ ↔ equiv' (α:=α) (β:=β) m₂ m₁ :=
  DMapLike.equiv'.comm (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂)

theorem MapLike.equiv'.symm {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (α:=α) (β:=β) m₁ m₂ → equiv' (α:=α) (β:=β) m₂ m₁ :=
  MapLike.equiv'.comm.mp

theorem MapLike.equiv'.trans {γ₁ γ₂ γ₃ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] [inst₃ : MapLike γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv' (α:=α) (β:=β) m₁ m₂ → equiv' (α:=α) (β:=β) m₂ m₃ → equiv' (α:=α) (β:=β) m₁ m₃ := by
  intro h₁ h₂ x; rw [h₁, h₂]

theorem MapLike.keyEquiv_iff_keySubset {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (α:=α) (β:=β) m₁ m₂ ↔ keySubset (α:=α) (β:=β) m₁ m₂ ∧ keySubset (α:=α) (β:=β) m₂ m₁ := by
  simp only [keySubset, keyEquiv]; apply Iff.intro <;> intro h
  case mp => simp [h]
  case mpr => intro x; apply Iff.intro <;> simp_all

theorem MapLike.equiv'_iff_subset {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (α:=α) (β:=β) m₁ m₂ ↔ subset (α:=α) (β:=β) m₁ m₂ ∧ subset (α:=α) (β:=β) m₂ m₁ := by
  simp only [subset, equiv']; apply Iff.intro <;> intro h
  case mp => simp [h]
  case mpr =>
    intro x
    have h₁ := h.left x; have h₂ := h.right x
    revert h₁ h₂ <;> cases m₁[x]? <;> cases m₂[x]? <;> simp

open MapLike

/--
  A finite map where the behavior of
  `· ∈ m , m[·]?, m[·]!, m[·], emptyWithCapacity, insert, erase, size`
  are uniquely determined up to `MapLike.equiv`
-/
class LawfulMapLike (γ : Type u) (α : Type v) (β : Type w) [inst : MapLike γ α β]
  extends LawfulGetElem γ α β (fun m x => x ∈ m), LawfulMemSize γ α where
  not_mem_empty : ∀ {k : α} {n : Nat}, ¬ k ∈ emptyWithCapacity (self:=inst) n
  mem_iff_isSome_getElem? : ∀ {m : γ} {k : α}, k ∈ m ↔ m[k]?.isSome
  getElem?_insert_self : ∀ {m : γ} {k : α} {v : β}, (insert m k v)[k]? = .some v
  getElem?_insert_ne : ∀ {m : γ} {k a : α} {v : β}, k ≠ a → (insert m k v)[a]? = m[a]?
  getElem?_erase_self : ∀ {m : γ} {k : α}, (erase (β:=β) m k)[k]? = .none
  getElem?_erase_ne : ∀ {m : γ} {k a : α}, k ≠ a → (erase (β:=β) m k)[a]? = m[a]?
  size_erase_mem : ∀ {m : γ} {k : α}, k ∈ m → Size.size (erase (β:=β) m k) + 1 = Size.size m

def LawfulMapLike_of_LawfulDMapLike {γ α β} [inst : MapLike γ α β]
  [instL : LawfulDMapLike (inst:=DMapLike_of_MapLike inst) γ α (fun _ => β)] :
  LawfulMapLike γ α β where
  getElem?_def := instL.dGetElem?_def
  getElem!_def c i := by
    have h := instL.dGetElem!_def c i
    simp only [dGetElem!, dGetElem?, DMapLike_of_MapLike] at h
    split at h <;> simp [*]
  not_mem_empty := instL.not_mem_empty
  mem_iff_isSome_getElem? := instL.mem_iff_isSome_dGetElem?
  getElem?_insert_self := instL.dGetElem?_insert_self
  getElem?_insert_ne := instL.dGetElem?_insert_ne
  getElem?_erase_self := instL.dGetElem?_erase_self
  getElem?_erase_ne := instL.dGetElem?_erase_ne
  size_zero_iff_forall_not_mem := instL.size_zero_iff_forall_not_mem
  size_erase_mem := instL.size_erase_mem

theorem LawfulMapLike_of_LawfulDMapLike' {γ α β} [inst : DMapLike γ α (fun _ => β)]
  [instL : LawfulDMapLike γ α (fun _ => β)] :
  LawfulMapLike (inst:=MapLike_of_DMapLike inst) γ α β :=
  LawfulMapLike_of_LawfulDMapLike (inst:=MapLike_of_DMapLike inst)

def LawfulDMapLike_of_LawfulMapLike {γ α β} [inst : DMapLike γ α (fun _ => β)]
  [instL : LawfulMapLike (inst:=MapLike_of_DMapLike inst) γ α β] :
  LawfulDMapLike γ α (fun _ => β) where
  dGetElem?_def := instL.getElem?_def
  dGetElem!_def c i := by
    intro _; have h := instL.getElem!_def c i
    simp only [getElem!, getElem?, MapLike_of_DMapLike] at h
    split at h <;> simp [*]
  not_mem_empty := instL.not_mem_empty
  mem_iff_isSome_dGetElem? := instL.mem_iff_isSome_getElem?
  dGetElem?_insert_self := instL.getElem?_insert_self
  dGetElem?_insert_ne := instL.getElem?_insert_ne
  dGetElem?_erase_self := instL.getElem?_erase_self
  dGetElem?_erase_ne := instL.getElem?_erase_ne
  size_zero_iff_forall_not_mem := instL.size_zero_iff_forall_not_mem
  size_erase_mem := instL.size_erase_mem

local instance LawfulDMapLike_of_LawfulMapLike' {γ α β} [inst : MapLike γ α β]
  [instL : LawfulMapLike γ α β] :
  LawfulDMapLike (inst:=DMapLike_of_MapLike inst) γ α (fun _ => β) :=
  LawfulDMapLike_of_LawfulMapLike (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.mem_iff_getElem?_eq_some {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} : k ∈ m ↔ ∃ v, m[k]? = .some v :=
  LawfulDMapLike.mem_iff_dGetElem?_eq_some (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.not_mem_iff_getElem?_eq_none {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} : k ∉ m ↔ m[k]? = .none :=
  LawfulDMapLike.not_mem_iff_dGetElem?_eq_none (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.mem_insert {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k a : α} {v : β} :
  a ∈ insert m k v ↔ (k = a) ∨ a ∈ m :=
  LawfulDMapLike.mem_insert (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.mem_erase {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k a : α} :
  a ∈ erase (β:=β) m k ↔ k ≠ a ∧ a ∈ m :=
  LawfulDMapLike.mem_erase (inst:=DMapLike_of_MapLike inst)

open Classical in
theorem LawfulMapLike.getElem?_eq_none_iff {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β]
  {c : γ} {i : α} : c[i]? = .none ↔ i ∉ c := by
  simp only [getElem?_def]
  split <;> simp_all

theorem LawfulMapLike.getElem?_eq_some_getElem {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} (h : k ∈ m) : m[k]? = .some m[k] :=
  LawfulDMapLike.dGetElem?_eq_some_dGetElem (inst:=DMapLike_of_MapLike inst) h

theorem LawfulMapLike.getElem!_eq_getElem {γ α β} [Inhabited β] [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} (h : k ∈ m) :
  m[k]! = m[k] := LawfulDMapLike.dGetElem!_eq_dGetElem (inst:=DMapLike_of_MapLike inst) h

theorem LawfulMapLike.getElem!_eq_default {γ α β} [Inhabited β] [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} (h : k ∉ m) :
  m[k]! = default := LawfulDMapLike.dGetElem!_eq_default (inst:=DMapLike_of_MapLike inst) h

theorem LawfulMapLike.getElem!_eq_get!_getElem? {γ α β} [Inhabited β] [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} :
  m[k]! = m[k]?.get! := LawfulDMapLike.dGetElem!_eq_get!_dGetElem? (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.getElem?_eq_some_getElem! {γ α β} [Inhabited β] [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} (h : k ∈ m) :
  m[k]? = .some m[k]! := LawfulDMapLike.dGetElem?_eq_some_dGetElem! (inst:=DMapLike_of_MapLike inst) h

theorem LawfulMapLike.getElem?_eq_none {γ α β} [Inhabited β]  [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} (h : k ∉ m) :
  m[k]? = .none := LawfulDMapLike.dGetElem?_eq_none (inst:=DMapLike_of_MapLike inst) h

theorem LawfulMapLike.getElem_eq_iff_getElem?_eq_some {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} {v : β} (h : k ∈ m) :
  m[k] = v ↔ m[k]? = .some v := LawfulDMapLike.dGetElem_eq_iff_dGetElem?_eq_some (inst:=DMapLike_of_MapLike inst) h

theorem LawfulMapLike.getElem_eq_of_getElem?_eq_some {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} {v : β}
  (h : m[k]? = .some v) : m[k]'(mem_iff_getElem?_eq_some.mpr ⟨_, h⟩) = v :=
  LawfulDMapLike.dGetElem_eq_of_dGetElem?_eq_some (inst:=DMapLike_of_MapLike inst) h

theorem LawfulMapLike.getElem_eq_getElem_iff_getElem?_eq_getElem? {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m₁ m₂ : γ} {k : α}
  (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) : m₁[k] = m₂[k] ↔ m₁[k]? = m₂[k]? :=
  LawfulDMapLike.dGetElem_eq_dGetElem_iff_dGetElem?_eq_dGetElem? (inst:=DMapLike_of_MapLike inst) h₁ h₂

theorem LawfulMapLike.getElem_insert_self {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k : α} {v : β} :
  (insert m k v)[k]'(mem_insert.mpr (Or.inl rfl)) = v :=
  LawfulDMapLike.dGetElem_insert_self (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.getElem_insert_ne {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k a : α} {v : β} (h₁ : a ∈ insert m k v) (h₂ : k ≠ a) :
  (insert m k v)[a] = m[a]'(Or.resolve_left (mem_insert.mp h₁) h₂) :=
  LawfulDMapLike.dGetElem_insert_ne (inst:=DMapLike_of_MapLike inst) h₁ h₂

theorem LawfulMapLike.getElem_erase {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} {k a : α} (h' : a ∈ erase m k) :
  (erase (β:=β) m k)[a] = m[a]'((mem_erase.mp h').right) :=
  LawfulDMapLike.dGetElem_erase (inst:=DMapLike_of_MapLike inst) h'

theorem LawfulMapLike.insert_mem_keyEquiv {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β]
  {m : γ} {k : α} {v : β} (hmem : k ∈ m) : keyEquiv (α:=α) (β:=β) (insert (self:=inst) m k v) m :=
  LawfulDMapLike.insert_mem_keyEquiv (inst:=DMapLike_of_MapLike inst) hmem

theorem LawfulMapLike.erase_insert_not_mem_equiv {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β]
  {m : γ} {k : α} {v : β} (hnmem : k ∉ m) : equiv (α:=α) (β:=β) (erase (self:=inst) (insert (self:=inst) m k v) k) m :=
  LawfulDMapLike.erase_insert_not_mem_equiv (inst:=DMapLike_of_MapLike inst) hnmem

theorem LawfulMapLike.erase_not_mem_equiv {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β]
  {m : γ} {k : α} (hnmem : k ∉ m) : equiv (α:=α) (β:=β) (erase (self:=inst) m k) m :=
  LawfulDMapLike.erase_not_mem_equiv (inst:=DMapLike_of_MapLike inst) hnmem

theorem LawfulMapLike.insert_erase_mem_keyEquiv {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β]
  {m : γ} {k : α} {v : β} (hmem : k ∈ m) : keyEquiv (α:=α) (β:=β) (insert (erase (self:=inst) m k) k v) m :=
  LawfulDMapLike.insert_erase_mem_keyEquiv (inst:=DMapLike_of_MapLike inst) hmem

theorem LawfulMapLike.insert_erase_getElem_eq_equiv {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β]
  {m : γ} {k : α} {v : β} (hmem : k ∈ m) (hget : m[k] = v) : equiv (α:=α) (β:=β) (insert (erase (self:=inst) m k) k v) m :=
  LawfulDMapLike.insert_erase_dGetElem_eq_equiv (inst:=DMapLike_of_MapLike inst) hmem hget

theorem LawfulMapLike.exists_key_list {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} :
  ∃ (l : List α), l.length = Size.size m ∧ l.Nodup ∧ ∀ k, k ∈ m ↔ k ∈ l :=
  LawfulDMapLike.exists_key_list (inst:=DMapLike_of_MapLike inst)

noncomputable def LawfulMapLike.exKeyList {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] (m : γ) : List α :=
  (exists_key_list (α:=α) (β:=β) (m:=m)).choose

noncomputable def LawfulMapLike.length_exKeyList_eq_size {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} :
  (exKeyList (α:=α) (β:=β) m).length = Size.size m :=
  (Exists.choose_spec exists_key_list).left

noncomputable def LawfulMapLike.length_exKeyList_nodup {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} :
  (exKeyList (α:=α) (β:=β) m).Nodup :=
  (Exists.choose_spec exists_key_list).right.left

noncomputable def LawfulMapLike.length_exKeyList_equiv {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ} :
  ∀ k, k ∈ m ↔ k ∈ (exKeyList (α:=α) (β:=β) m) :=
  (Exists.choose_spec exists_key_list).right.right

theorem LawfulMapLike.size_le_of_keySubset {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hsub : keySubset (α:=α) (β:=β) m₁ m₂) : Size.size m₁ ≤ Size.size m₂ :=
  LawfulDMapLike.size_le_of_keySubset (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) hsub

theorem LawfulMapLike.size_eq_of_keyEquiv {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : keyEquiv (α:=α) (β:=β) m₁ m₂) : Size.size m₁ = Size.size m₂ :=
  LawfulDMapLike.size_eq_of_keyEquiv (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) hequiv

theorem LawfulMapLike.keyEquiv_iff_size_eq_and_keySubset {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂} :
  keyEquiv (α:=α) (β:=β) m₁ m₂ ↔ Size.size m₁ = Size.size m₂ ∧ keySubset (α:=α) (β:=β) m₁ m₂ :=
  LawfulDMapLike.keyEquiv_iff_size_eq_and_keySubset (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂)

theorem LawfulMapLike.size_insert_mem {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ}
  {k : α} {v : β} (hmem : k ∈ m) : Size.size (insert (self:=inst) m k v) = Size.size m :=
  LawfulDMapLike.size_insert_mem (inst:=DMapLike_of_MapLike inst) hmem

theorem LawfulMapLike.size_insert_not_mem {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ}
  {k : α} {v : β} (hnmem : k ∉ m) : Size.size (insert (self:=inst) m k v) = Size.size m + 1 :=
  LawfulDMapLike.size_insert_not_mem (inst:=DMapLike_of_MapLike inst) hnmem

theorem LawfulMapLike.size_insert_le {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ}
  {k : α} {v : β} : Size.size (insert m k v) ≤ Size.size m + 1 :=
  LawfulDMapLike.size_insert_le (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.le_size_insert {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ}
  {k : α} {v : β} : Size.size m ≤ Size.size (insert m k v) :=
  LawfulDMapLike.le_size_insert (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.size_insert_gt_zero {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ}
  {k : α} {v : β} : Size.size (insert m k v) > 0 :=
  LawfulDMapLike.size_insert_gt_zero (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.size_erase_not_mem {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ}
  {k : α} (hnm : k ∉ m) : Size.size (erase (β:=β) m k) = Size.size m :=
  LawfulDMapLike.size_erase_not_mem (inst:=DMapLike_of_MapLike inst) hnm

theorem LawfulMapLike.size_erase_le {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ}
  {k : α} : Size.size (erase (β:=β) m k) ≤ Size.size m :=
  LawfulDMapLike.size_erase_le (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.le_size_erase {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β] {m : γ}
  {k : α} : Size.size m ≤ Size.size (erase (β:=β) m k) + 1 :=
  LawfulDMapLike.le_size_erase (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.getElem?_empty {γ α β} [inst : MapLike γ α β] [LawfulMapLike γ α β]
  {capacity : Nat} {k : α} : (emptyWithCapacity (self:=inst) capacity)[k]? = .none :=
  LawfulDMapLike.dGetElem?_empty (inst:=DMapLike_of_MapLike inst)

theorem LawfulMapLike.getElem?_insert {γ α β} [inst : MapLike γ α β]
  [LawfulMapLike γ α β] [DecidableEq α] {m : γ} {k a : α} {v : β} :
  (insert m k v)[a]? = if (k = a) then some v else m[a]? := by
  have h := LawfulDMapLike.dGetElem?_insert (inst:=DMapLike_of_MapLike inst) (m:=m) (k:=k) (a:=a) (v:=v)
  simp only [dGetElem?, DMapLike_of_MapLike] at h
  rw [h]; split
  case isTrue heq => cases heq <;> rfl
  case isFalse => rfl

theorem LawfulMapLike.getElem?_erase {γ α β} [inst : MapLike γ α β]
  [LawfulMapLike γ α β] [DecidableEq α] {m : γ} {k a : α} :
  (erase (self:=inst) m k)[a]? = if (k = a) then .none else m[a]? :=
  LawfulDMapLike.dGetElem?_erase (inst:=DMapLike_of_MapLike inst)

open Classical in
theorem LawfulMapLike.getElem?_eq_none_iff_getElem?_eq_none_of_keyEquiv {γ₁ γ₂ α β}
  [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (hequiv : MapLike.keyEquiv (α:=α) (β:=β) m₁ m₂)
  (k : α) : m₁[k]? = .none ↔ m₂[k]? = .none := by
  simp [hequiv k]

theorem LawfulMapLike.equiv_iff_equiv' {γ₁ γ₂ α β}
  [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} :
  MapLike.equiv (α:=α) (β:=β) m₁ m₂ ↔ MapLike.equiv' (α:=α) (β:=β) m₁ m₂ :=
  LawfulDMapLike.equiv_iff_equiv' (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂)

theorem LawfulMapLike.equiv_iff_subset {γ₁ γ₂ α β}
  [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (α:=α) (β:=β) m₁ m₂ ↔ subset (α:=α) (β:=β) m₁ m₂ ∧ subset (α:=α) (β:=β) m₂ m₁ := by
  rw [LawfulMapLike.equiv_iff_equiv', MapLike.equiv'_iff_subset]

theorem LawfulMapLike.keySubset_of_subset {γ₁ γ₂ α β}
  [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β] [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (h : subset (α:=α) (β:=β) m₁ m₂) : keySubset (α:=α) (β:=β) m₁ m₂ := by
  simp only [subset] at h
  intro x
  simp only [mem_iff_isSome_getElem?]
  have hx := h x
  revert hx
  cases m₁[x]? <;> grind

theorem LawfulMapLike.mem_congr {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) : x ∈ m₁ ↔ x ∈ m₂ := hequiv.left _

theorem LawfulMapLike.getElem?_congr {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) : m₁[x]? = m₂[x]? :=
  LawfulMapLike.equiv_iff_equiv'.mp hequiv _

theorem LawfulMapLike.getElem_congr {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) (h₁ : x ∈ m₁) (h₂ : x ∈ m₂) : m₁[x] = m₂[x] :=
  LawfulDMapLike.dGetElem_congr (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) hequiv x h₁ h₂

theorem LawfulMapLike.getElem_congr' {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) (h₁ : x ∈ m₁) : m₁[x] = m₂[x]'((hequiv.left _).mp h₁) :=
  LawfulDMapLike.dGetElem_congr' (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) hequiv x h₁

theorem LawfulMapLike.getElem!_congr {γ₁ γ₂ α β} [Inhabited β] [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) : m₁[x]! = m₂[x]! :=
  LawfulDMapLike.dGetElem!_congr (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) hequiv x

theorem LawfulMapLike.emptyWithCapacity_congr {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] (capacity₁ capacity₂ : Nat) :
  equiv (α:=α) (β:=β)
    (emptyWithCapacity (self:=inst₁) capacity₁)
    (emptyWithCapacity (self:=inst₂) capacity₂) :=
  LawfulDMapLike.emptyWithCapacity_congr (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) _ _

theorem LawfulMapLike.insert_congr {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (k : α) (v : β) :
  equiv (α:=α) (β:=β) (insert m₁ k v) (insert m₂ k v) :=
  LawfulDMapLike.insert_congr (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) hequiv k v

open Classical in
theorem LawfulMapLike.erase_congr {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (k : α) :
  equiv (α:=α) (β:=β) (erase m₁ (self:=inst₁) k) (erase m₂ (self:=inst₂) k) :=
  LawfulDMapLike.erase_congr (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) hequiv k

theorem LawfulMapLike.size_congr {γ₁ γ₂ α β} [inst₁ : MapLike γ₁ α β] [inst₂ : MapLike γ₂ α β]
  [LawfulMapLike γ₁ α β] [LawfulMapLike γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) : Size.size m₁ = Size.size m₂ :=
  LawfulDMapLike.size_congr (inst₁:=DMapLike_of_MapLike inst₁) (inst₂:=DMapLike_of_MapLike inst₂) hequiv

instance {α β} [BEq α] [Hashable α] : MapLike (HashMap α β) α β where
  emptyWithCapacity capacity := HashMap.emptyWithCapacity (capacity:=capacity)
  insert := HashMap.insert
  erase := HashMap.erase
  size := HashMap.size

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : LawfulMapLike (HashMap α β) α β where
  not_mem_empty := by intro k n; simp [MapLike.emptyWithCapacity]
  mem_iff_isSome_getElem? := HashMap.mem_iff_isSome_getElem?
  getElem?_insert_self := HashMap.getElem?_insert_self
  getElem?_insert_ne := by
    intro m k a v h
    simp [MapLike.insert, HashMap.getElem?_insert, h]
  getElem?_erase_self := HashMap.getElem?_erase_self
  getElem?_erase_ne := by
    intro m k a h
    simp [MapLike.erase, HashMap.getElem?_erase, h]
  size_erase_mem := HashMap.size_erase_mem

instance {α} : MapLike (OptArr α) Nat α where
  emptyWithCapacity capacity := OptArr.emptyWithCapacity capacity
  insert := OptArr.insert
  erase := OptArr.erase
  size := OptArr.size

instance {α} : LawfulMapLike (OptArr α) Nat α where
  not_mem_empty := OptArr.not_mem_empty
  mem_iff_isSome_getElem? := OptArr.mem_iff_isSome_getElem?
  getElem?_insert_self := OptArr.getElem?_insert_self
  getElem?_insert_ne := OptArr.getElem?_insert_ne
  getElem?_erase_self := OptArr.getElem?_erase_self
  getElem?_erase_ne := OptArr.getElem?_erase_ne
  size_erase_mem := OptArr.size_erase_mem

instance {α β} [Ord α] : MapLike (TreeMap α β) α β where
  emptyWithCapacity _ := TreeMap.empty
  insert := TreeMap.insert
  erase := TreeMap.erase
  size := TreeMap.size

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulMapLike (TreeMap α β) α β where
  not_mem_empty := TreeMap.not_mem_emptyc
  mem_iff_isSome_getElem? := TreeMap.mem_iff_isSome_getElem?
  getElem?_insert_self := TreeMap.getElem?_insert_self
  getElem?_insert_ne := by
    intro m k a v hne
    simp only [MapLike.insert, TreeMap.getElem?_insert]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  getElem?_erase_self := TreeMap.getElem?_erase_self
  getElem?_erase_ne := by
    intro m k a hne
    simp only [MapLike.erase, TreeMap.getElem?_erase]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  size_erase_mem := TreeMap.size_erase_mem

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : MapLike (ExtHashMap α β) α β where
  emptyWithCapacity capacity := ExtHashMap.emptyWithCapacity capacity
  insert := ExtHashMap.insert
  erase := ExtHashMap.erase
  size := ExtHashMap.size

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : LawfulMapLike (ExtHashMap α β) α β where
  not_mem_empty := by intro k n; simp [MapLike.emptyWithCapacity]
  mem_iff_isSome_getElem? := ExtHashMap.mem_iff_isSome_getElem?
  getElem?_insert_self := ExtHashMap.getElem?_insert_self
  getElem?_insert_ne := by
    intros m k a v hne
    simp [MapLike.insert, ExtHashMap.getElem?_insert, hne]
  getElem?_erase_self := ExtHashMap.getElem?_erase_self
  getElem?_erase_ne := by
    intros m k a hne
    simp [MapLike.erase, ExtHashMap.getElem?_erase, hne]
  size_erase_mem := Std.ExtHashMap.size_erase_mem

instance {α β} [Ord α] [TransOrd α] : MapLike (ExtTreeMap α β) α β where
  emptyWithCapacity _ := ExtTreeMap.empty
  insert := ExtTreeMap.insert
  erase := ExtTreeMap.erase
  size := ExtTreeMap.size

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulMapLike (ExtTreeMap α β) α β where
  not_mem_empty := TreeMap.not_mem_emptyc
  mem_iff_isSome_getElem? := ExtTreeMap.mem_iff_isSome_getElem?
  getElem?_insert_self := ExtTreeMap.getElem?_insert_self
  getElem?_insert_ne := by
    intro m k a v hne
    simp only [MapLike.insert, ExtTreeMap.getElem?_insert]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  getElem?_erase_self := ExtTreeMap.getElem?_erase_self
  getElem?_erase_ne := by
    intro m k a hne
    simp only [MapLike.erase, ExtTreeMap.getElem?_erase]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  size_erase_mem := ExtTreeMap.size_erase_mem

end MapLike

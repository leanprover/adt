/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

import Lean
import ADT.List
import ADT.OptArr
import ADT.Logic
import ADT.Lemmas
import ADT.Sizy
import ADT.DGetElem
import Std.Data
open Std

/-!
  This section defines an abstract datatype `DMapy` and its lawful
  counterpart `LawfulDMapy`. An instance `inst : DMapy γ α β` denotes
  that `γ` models a finite, dependently typed map from `α` to `β`,
  i.e. a function from a finite collection of elements of type `α`
  (i.e. the keys) to `β`.

  `DMapy` is a subtype of `Membership` and `DGetElem?`. In addition,
  it must support the following operations: `emptyWithCapacity`,
  `insert`, `erase`, `size`
  · `a ∈ m` iff `a` is present in the keys
  · `emptyWithCapacity k` returns an empty map with capacity `k`.
    The capacity parameter is present because of performance considerations.
  · `insert m k v`: insert the key-value pair `(k, v)` to `m`. If
    `k` is already present, its value is overriden
  · `erase m k`: erase the key `k` from `m`
  · `size m`: return the size of `m`

  `LawfulDMapy` specifies the behavior of the operations supported by
  `DMapy`, whereby the behavior of the operations are uniquely determined
  up to `DMapy.equiv`.
-/

section DMapy

class DMapy (γ : Type u) (α : Type v) (β : α → Type w) extends
  Membership α γ, DGetElem? γ α β (fun m x => x ∈ m), Sizy γ where
  emptyWithCapacity {γ α β} : Nat → γ
  insert : γ → (x : α) → (y : β x) → γ
  erase {γ α β} : γ → α → γ

def DMapy.keyEquiv {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  (m₁ : γ₁) (m₂ : γ₂) := ∀ (x : α), x ∈ m₁ ↔ x ∈ m₂

def DMapy.equiv {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  keyEquiv (β:=β) m₁ m₂ ∧ ∀ (x : α) (h₁ : x ∈ m₁) (h₂ : x ∈ m₂), m₁[x]ᵈ'h₁ = m₂[x]ᵈ'h₂

def DMapy.equiv' {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α), m₁[x]ᵈ? = m₂[x]ᵈ?

def DMapy.keySubset {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α), x ∈ m₁ → x ∈ m₂

def DMapy.subset {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α) (y : β x), m₁[x]ᵈ? = .some y → m₂[x]ᵈ? =.some y

theorem DMapy.keyEquiv.refl {γ α β} [inst : DMapy γ α β] {m : γ} : keyEquiv (β:=β) m m := by
  simp [keyEquiv]

theorem DMapy.keyEquiv.comm {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (β:=β) m₁ m₂ ↔ keyEquiv (β:=β) m₂ m₁ := by
  simp only [keyEquiv]
  conv => left; enter [x]; rw [Iff.comm]

theorem DMapy.keyEquiv.symm {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (β:=β) m₁ m₂ → keyEquiv (β:=β) m₂ m₁ :=
  DMapy.keyEquiv.comm.mp

theorem DMapy.keyEquiv.trans {γ₁ γ₂ γ₃ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] [inst₃ : DMapy γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : keyEquiv (β:=β) m₁ m₂ → keyEquiv (β:=β) m₂ m₃ → keyEquiv (β:=β) m₁ m₃ := by
  intro h₁ h₂ x
  rw [h₁, h₂]

theorem DMapy.equiv.refl {γ α β} [inst : DMapy γ α β] {m : γ} : equiv (β:=β) m m := by
  simp [equiv, keyEquiv]

theorem DMapy.equiv.comm {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (β:=β) m₁ m₂ ↔ equiv (β:=β) m₂ m₁ := by
  simp only [equiv, keyEquiv.comm (m₁:=m₁)]
  conv => enter [1, 2, x]; rw [forall_comm]
  conv => enter [1, 2, x, h₁, h₂]; rw [Eq.comm]

theorem DMapy.equiv.symm {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (β:=β) m₁ m₂ → equiv (β:=β) m₂ m₁ :=
  DMapy.equiv.comm.mp

theorem DMapy.equiv.trans {γ₁ γ₂ γ₃ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] [inst₃ : DMapy γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv (β:=β) m₁ m₂ → equiv (β:=β) m₂ m₃ → equiv (β:=β) m₁ m₃ := by
  intro h₁ h₂; apply And.intro
  case left => intro x; rw [h₁.left, h₂.left]
  case right =>
    intro x h₁' h₃'
    have h₂' := by rw [← h₂.left] at h₃'; exact h₃'
    rw [h₁.right _ h₁' h₂', h₂.right _ h₂' h₃']

theorem DMapy.equiv'.refl {γ α β} [inst : DMapy γ α β] {m : γ} : equiv' (β:=β) m m := by
  simp [equiv']

theorem DMapy.equiv'.comm {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (β:=β) m₁ m₂ ↔ equiv' (β:=β) m₂ m₁ := by
  simp only [equiv']
  conv => left; enter [x]; rw [Eq.comm]

theorem DMapy.equiv'.symm {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (β:=β) m₁ m₂ → equiv' (β:=β) m₂ m₁ :=
  DMapy.equiv'.comm.mp

theorem DMapy.equiv'.trans {γ₁ γ₂ γ₃ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] [inst₃ : DMapy γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv' (β:=β) m₁ m₂ → equiv' (β:=β) m₂ m₃ → equiv' (β:=β) m₁ m₃ := by
  intro h₁ h₂ x; rw [h₁, h₂]

theorem DMapy.keyEquiv_iff_keySubset {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (β:=β) m₁ m₂ ↔ keySubset (β:=β) m₁ m₂ ∧ keySubset (β:=β) m₂ m₁ := by
  simp only [keySubset, keyEquiv]; apply Iff.intro <;> intro h
  case mp => simp [h]
  case mpr => intro x; apply Iff.intro <;> simp_all

theorem DMapy.equiv'_iff_subset {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (β:=β) m₁ m₂ ↔ subset (β:=β) m₁ m₂ ∧ subset (β:=β) m₂ m₁ := by
  simp only [subset, equiv']; apply Iff.intro <;> intro h
  case mp => simp [h]
  case mpr =>
    intro x
    have h₁ := h.left x; have h₂ := h.right x
    revert h₁ h₂ <;> cases m₁[x]ᵈ? <;> cases m₂[x]ᵈ? <;> simp

open DMapy

/--
  A finite dependently typed map where the behavior of
  `· ∈ m , m[·]?, m[·]!, m[·], emptyWithCapacity, insert, erase, size`
  are uniquely determined up to `Map.equiv`
-/
class LawfulDMapy (γ : Type u) (α : Type v) (β : α → Type w) [inst : DMapy γ α β]
  extends LawfulMemSizy γ α, LawfulDGetElem γ α β (fun m x => x ∈ m) where
  not_mem_empty : ∀ {k : α} {n : Nat}, ¬ k ∈ emptyWithCapacity (self:=inst) n
  mem_iff_isSome_dGetElem? : ∀ {m : γ} {k : α}, k ∈ m ↔ m[k]ᵈ?.isSome
  dGetElem?_insert_self : ∀ {m : γ} {k : α} {v : β k}, (insert m k v)[k]ᵈ? = .some v
  dGetElem?_insert_ne : ∀ {m : γ} {k a : α} {v : β k}, k ≠ a → (insert m k v)[a]ᵈ? = m[a]ᵈ?
  dGetElem?_erase_self : ∀ {m : γ} {k : α}, (erase (β:=β) m k)[k]ᵈ? = .none
  dGetElem?_erase_ne : ∀ {m : γ} {k a : α}, k ≠ a → (erase (β:=β) m k)[a]ᵈ? = m[a]ᵈ?
  size_erase_mem : ∀ {m : γ} {k : α}, k ∈ m → Sizy.size (erase (β:=β) m k) + 1 = Sizy.size m

theorem LawfulDMapy.mem_iff_dGetElem?_eq_some {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} : k ∈ m ↔ ∃ v, m[k]ᵈ? = .some v := by
  rw [mem_iff_isSome_dGetElem?]; rw [Option.isSome_iff_exists]

theorem LawfulDMapy.not_mem_iff_dGetElem?_eq_none {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} : k ∉ m ↔ m[k]ᵈ? = .none := by
  rw [mem_iff_isSome_dGetElem?]; simp

theorem LawfulDMapy.mem_insert {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k a : α} {v : β k} :
  a ∈ insert m k v ↔ (k = a) ∨ a ∈ m := by
  rw [mem_iff_isSome_dGetElem?]; by_cases k = a
  case pos h => cases h; simp [dGetElem?_insert_self]
  case neg h => simp only [dGetElem?_insert_ne h]; simp [← mem_iff_isSome_dGetElem?, *]

theorem LawfulDMapy.mem_erase {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k a : α} :
  a ∈ erase (β:=β) m k ↔ k ≠ a ∧ a ∈ m := by
  rw [mem_iff_isSome_dGetElem?]; by_cases k = a
  case pos h => cases h; simp [dGetElem?_erase_self]
  case neg h => simp only [dGetElem?_erase_ne h]; simp [← mem_iff_isSome_dGetElem?, h]

open Classical in
theorem LawfulDMapy.dGetElem?_eq_none_iff {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β]
  {c : γ} {i : α} : c[i]ᵈ? = .none ↔ i ∉ c := by
  simp only [dGetElem?_def]
  split <;> simp_all

open Classical in
theorem LawfulDMapy.dGetElem?_eq_some_dGetElem {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} (h : k ∈ m) :
  m[k]ᵈ? = .some (m[k]ᵈ'h) := by
  simp [dGetElem?_def, h]

theorem LawfulDMapy.dGetElem!_eq_dGetElem {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} [Inhabited (β k)] (h : k ∈ m) :
  m[k]ᵈ! = m[k]ᵈ'h := by
  simp [dGetElem!_def, dGetElem?_eq_some_dGetElem h]

theorem LawfulDMapy.dGetElem!_eq_default {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} [Inhabited (β k)] (h : k ∉ m) :
  m[k]ᵈ! = default := by
  simp [dGetElem!_def, dGetElem?_eq_none_iff.mpr h]

theorem LawfulDMapy.dGetElem!_eq_get!_dGetElem? {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} [Inhabited (β k)] : m[k]ᵈ! = m[k]ᵈ?.get! := by
  simp only [dGetElem!_def]; split <;> simp [*]

theorem LawfulDMapy.dGetElem?_eq_some_dGetElem! {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} [Inhabited (β k)] (h : k ∈ m) :
  m[k]ᵈ? = .some m[k]ᵈ! := by
  simp [dGetElem?_eq_some_dGetElem h, dGetElem!_eq_dGetElem h]

theorem LawfulDMapy.dGetElem?_eq_none {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} [Inhabited (β k)] (h : k ∉ m) :
  m[k]ᵈ? = .none := by
  simp [dGetElem?_eq_none_iff.mpr h]

theorem LawfulDMapy.dGetElem_eq_iff_dGetElem?_eq_some {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} {v : β k} (h : k ∈ m) :
  m[k]ᵈ'h = v ↔ m[k]ᵈ? = .some v := by
  rw [dGetElem?_eq_some_dGetElem h]; simp

theorem LawfulDMapy.dGetElem_eq_of_dGetElem?_eq_some {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} {v : β k}
  (h : m[k]ᵈ? = .some v) : m[k]ᵈ'(mem_iff_dGetElem?_eq_some.mpr ⟨_, h⟩) = v := by
  apply (LawfulDMapy.dGetElem_eq_iff_dGetElem?_eq_some _).mpr h

theorem LawfulDMapy.dGetElem_eq_dGetElem_iff_dGetElem?_eq_dGetElem? {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m₁ m₂ : γ} {k : α}
  (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) : m₁[k]ᵈ'h₁ = m₂[k]ᵈ'h₂ ↔ m₁[k]ᵈ? = m₂[k]ᵈ? := by
  rw [dGetElem?_eq_some_dGetElem h₁, dGetElem?_eq_some_dGetElem h₂]; simp

theorem LawfulDMapy.dGetElem_insert_self {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k : α} {v : β k} :
  (insert m k v)[k]ᵈ'(mem_insert.mpr (Or.inl rfl)) = v := by
  have hmem : k ∈ insert m k v := mem_insert.mpr (Or.inl rfl)
  have heq := dGetElem?_eq_some_dGetElem hmem
  rw [dGetElem?_insert_self] at heq
  injection heq with heq; rw [← heq]

theorem LawfulDMapy.dGetElem_insert_ne {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k a : α} {v : β k} (h₁ : a ∈ insert m k v) (h₂ : k ≠ a) :
  (insert m k v)[a]ᵈ'h₁ = m[a]ᵈ'(Or.resolve_left (mem_insert.mp h₁) h₂) := by
  have heq := dGetElem?_eq_some_dGetElem h₁
  have heq' := dGetElem?_eq_some_dGetElem (Or.resolve_left (mem_insert.mp h₁) h₂)
  rw [dGetElem?_insert_ne h₂, heq'] at heq
  injection heq with heq; rw [← heq]

theorem LawfulDMapy.dGetElem_erase {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} {k a : α} (h' : a ∈ erase m k) :
  (erase (β:=β) m k)[a]ᵈ'h' = m[a]ᵈ'((mem_erase.mp h').right) := by
  have heq := dGetElem?_eq_some_dGetElem h'
  have heq' := dGetElem?_eq_some_dGetElem (mem_erase.mp h').right
  by_cases k = a
  case pos h => cases h; simp [dGetElem?_erase_self] at heq
  case neg h =>
    simp only [dGetElem?_erase_ne h, heq'] at heq
    injection heq with heq; rw [← heq]

theorem LawfulDMapy.insert_mem_keyEquiv {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β]
  {m : γ} {k : α} {v : β k} (hmem : k ∈ m) : keyEquiv (β:=β) (insert m k v) m := by
  simp [keyEquiv, mem_insert, hmem]

theorem LawfulDMapy.erase_insert_not_mem_equiv {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β]
  {m : γ} {k : α} {v : β k} (hnmem : k ∉ m) : equiv (β:=β) (erase (β:=β) (insert m k v) k) m := by
  simp only [equiv, keyEquiv, mem_erase, mem_insert, dGetElem_erase]
  apply And.intro
  case left => intro x; by_cases (k = x) <;> simp_all
  case right => intro x ⟨hne, h₁⟩ h₂; simp [dGetElem_insert_ne _ hne]

theorem LawfulDMapy.erase_not_mem_equiv {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β]
  {m : γ} {k : α} (hnmem : k ∉ m) : equiv (β:=β) (erase (β:=β) m k) m := by
  simp only [equiv, keyEquiv, mem_erase, dGetElem_erase]
  apply And.intro
  case left => intro x; by_cases (k = x) <;> simp_all
  case right => simp

theorem LawfulDMapy.insert_erase_mem_keyEquiv {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β]
  {m : γ} {k : α} {v : β k} (hmem : k ∈ m) : keyEquiv (β:=β) (insert (erase (β:=β) m k) k v) m := by
  simp only [keyEquiv, mem_insert, mem_erase]
  intro x; by_cases (k = x) <;> simp_all

theorem LawfulDMapy.insert_erase_dGetElem_eq_equiv {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β]
  {m : γ} {k : α} {v : β k} (hmem : k ∈ m) (hget : m[k]ᵈ'hmem = v) : equiv (β:=β) (insert (erase (β:=β) m k) k v) m := by
  simp only [equiv, keyEquiv, mem_insert, mem_erase]
  apply And.intro
  case left => intro x; grind
  case right =>
    intro x h₁ h₂; cases h₁
    case inl heq => cases heq; simp [dGetElem_insert_self, hget]
    case inr hne => simp [dGetElem_insert_ne _ hne.left, dGetElem_erase]

theorem LawfulDMapy.exists_key_list {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} :
  ∃ (l : List α), l.length = Sizy.size m ∧ l.Nodup ∧ ∀ k, k ∈ m ↔ k ∈ l := by
  generalize hsz : Sizy.size m = n
  induction n generalizing m
  case zero =>
    exists []; simp [LawfulMemSizy.size_zero_iff_forall_not_mem.mp hsz]
  case succ n IH =>
    have hnz : Sizy.size m ≠ 0 := by
      intro h; rw [h] at hsz; simp at hsz
    have ⟨x, hx⟩ := LawfulMemSizy.size_ne_zero_iff_exists_mem.mp hnz
    let me := erase (β:=β) m x
    have hmesz : Sizy.size (erase (β:=β) m x) = n := by
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

noncomputable def LawfulDMapy.exKeyList {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] (m : γ) : List α :=
  (exists_key_list (α:=α) (β:=β) (m:=m)).choose

noncomputable def LawfulDMapy.length_exKeyList_eq_size {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} :
  (exKeyList (α:=α) (β:=β) m).length = Sizy.size m :=
  (Exists.choose_spec exists_key_list).left

noncomputable def LawfulDMapy.length_exKeyList_nodup {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} :
  (exKeyList (α:=α) (β:=β) m).Nodup :=
  (Exists.choose_spec exists_key_list).right.left

noncomputable def LawfulDMapy.length_exKeyList_equiv {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ} :
  ∀ k, k ∈ m ↔ k ∈ (exKeyList (α:=α) (β:=β) m) :=
  (Exists.choose_spec exists_key_list).right.right

theorem LawfulDMapy.size_le_of_keySubset {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hsub : keySubset (β:=β) m₁ m₂) : Sizy.size m₁ ≤ Sizy.size m₂ := by
  let ⟨l₁, heq₁, hnd₁, hequiv₁⟩ := exists_key_list (inst:=inst₁) (m:=m₁)
  let ⟨l₂, heq₂, hnd₂, hequiv₂⟩ := exists_key_list (inst:=inst₂) (m:=m₂)
  rw [← heq₁, ← heq₂]
  apply List.length_le_of_subset hnd₁
  intro x hx
  rw [← hequiv₂]; apply hsub; rw [hequiv₁]; exact hx

theorem LawfulDMapy.size_eq_of_keyEquiv {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : keyEquiv (β:=β) m₁ m₂) : Sizy.size m₁ = Sizy.size m₂ := by
  rw [keyEquiv_iff_keySubset] at hequiv
  have h₁ := size_le_of_keySubset hequiv.left
  have h₂ := size_le_of_keySubset hequiv.right
  omega

theorem LawfulDMapy.keyEquiv_iff_size_eq_and_keySubset {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂} :
  keyEquiv (β:=β) m₁ m₂ ↔ Sizy.size m₁ = Sizy.size m₂ ∧ keySubset (β:=β) m₁ m₂ := by
  let ⟨l₁, heq₁, hnd₁, hequiv₁⟩ := exists_key_list (β:=β) (m:=m₁)
  let ⟨l₂, heq₂, hnd₂, hequiv₂⟩ := exists_key_list (β:=β) (m:=m₂)
  simp only [keyEquiv, keySubset]
  rw [← heq₁, ← heq₂]; simp only [hequiv₁, hequiv₂]
  simp only [← List.nodup_perm_iff_equiv hnd₁ hnd₂,
             ← List.subset_def,
             ← List.nodup_subPerm_iff_subset hnd₁ hnd₂]
  apply List.perm_iff_length_eq_andsubPerm

theorem LawfulDMapy.size_insert_mem {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ}
  {k : α} {v : β k} (hmem : k ∈ m) : Sizy.size (insert m k v) = Sizy.size m := by
  apply size_eq_of_keyEquiv; apply insert_mem_keyEquiv hmem

theorem LawfulDMapy.size_insert_not_mem {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ}
  {k : α} {v : β k} (hnmem : k ∉ m) : Sizy.size (insert m k v) = Sizy.size m + 1 := by
  have hke := erase_insert_not_mem_equiv hnmem (v:=v)
  rw [← size_eq_of_keyEquiv hke.left]; symm
  apply size_erase_mem; simp [mem_insert]

theorem LawfulDMapy.size_insert_le {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ}
  {k : α} {v : β k} : Sizy.size (insert m k v) ≤ Sizy.size m + 1 := by
  by_cases k ∈ m
  case pos h => rw [size_insert_mem h]; simp
  case neg h => rw [size_insert_not_mem h]; exact .refl

theorem LawfulDMapy.le_size_insert {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ}
  {k : α} {v : β k} : Sizy.size m ≤ Sizy.size (insert m k v) := by
  by_cases k ∈ m
  case pos h => rw [size_insert_mem h]; exact .refl
  case neg h => rw [size_insert_not_mem h]; simp

theorem LawfulDMapy.size_insert_gt_zero {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ}
  {k : α} {v : β k} : Sizy.size (insert m k v) > 0 := by
  by_cases k ∈ m
  case pos h => rw [size_insert_mem h]; apply LawfulMemSizy.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
  case neg h => rw [size_insert_not_mem h]; simp

theorem LawfulDMapy.size_erase_not_mem {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ}
  {k : α} (hnm : k ∉ m) : Sizy.size (erase (β:=β) m k) = Sizy.size m := by
  apply size_eq_of_keyEquiv; apply (erase_not_mem_equiv hnm).left

theorem LawfulDMapy.size_erase_le {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ}
  {k : α} : Sizy.size (erase (β:=β) m k) ≤ Sizy.size m := by
  by_cases k ∈ m
  case pos h => have := size_erase_mem h; omega
  case neg h => rw [size_erase_not_mem h]; exact .refl

theorem LawfulDMapy.le_size_erase {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β] {m : γ}
  {k : α} : Sizy.size m ≤ Sizy.size (erase (β:=β) m k) + 1 := by
  by_cases k ∈ m
  case pos h => simp [size_erase_mem h]
  case neg h => rw [size_erase_not_mem h]; simp

theorem LawfulDMapy.dGetElem?_empty {γ α β} [inst : DMapy γ α β] [LawfulDMapy γ α β]
  {capacity : Nat} {k : α} : (emptyWithCapacity (γ:=γ) (β:=β) capacity)[k]ᵈ? = .none := by
  rw [← not_mem_iff_dGetElem?_eq_none]; apply not_mem_empty

theorem LawfulDMapy.dGetElem?_insert {γ α β} [inst : DMapy γ α β]
  [LawfulDMapy γ α β] [DecidableEq α] {m : γ} {k a : α} {v : β k} :
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

theorem LawfulDMapy.dGetElem?_erase {γ α β} [inst : DMapy γ α β]
  [LawfulDMapy γ α β] [DecidableEq α] {m : γ} {k a : α} :
  (erase (β:=β) m k)[a]ᵈ? = if (k = a) then .none else m[a]ᵈ? := by
  by_cases k = a
  case pos h => cases h; simp [dGetElem?_erase_self]
  case neg h => simp [dGetElem?_erase_ne h, h]

open Classical in
theorem LawfulDMapy.dGetElem?_eq_none_iff_dGetElem?_eq_none_of_keyEquiv {γ₁ γ₂ α β}
  [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (hequiv : DMapy.keyEquiv (β:=β) m₁ m₂)
  (k : α) : m₁[k]ᵈ? = .none ↔ m₂[k]ᵈ? = .none := by
  simp [dGetElem?_eq_none_iff, hequiv k]

theorem LawfulDMapy.equiv_iff_equiv' {γ₁ γ₂ α β}
  [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} :
  DMapy.equiv (β:=β) m₁ m₂ ↔ DMapy.equiv' (β:=β) m₁ m₂ := by
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

theorem LawfulDMapy.equiv_iff_subset {γ₁ γ₂ α β}
  [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (β:=β) m₁ m₂ ↔ subset (β:=β) m₁ m₂ ∧ subset (β:=β) m₂ m₁ := by
  rw [LawfulDMapy.equiv_iff_equiv', DMapy.equiv'_iff_subset]

theorem LawfulDMapy.keySubset_of_subset {γ₁ γ₂ α β}
  [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β] [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (h : subset (β:=β) m₁ m₂) : keySubset (β:=β) m₁ m₂ := by
  simp only [subset] at h
  intro x
  simp only [mem_iff_isSome_dGetElem?]
  have hx := h x
  revert hx
  cases m₁[x]ᵈ? <;> grind

theorem LawfulDMapy.mem_congr {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) : x ∈ m₁ ↔ x ∈ m₂ := hequiv.left _

theorem LawfulDMapy.dGetElem?_congr {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) : m₁[x]ᵈ? = m₂[x]ᵈ? :=
  LawfulDMapy.equiv_iff_equiv'.mp hequiv _

theorem LawfulDMapy.dGetElem_congr {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) (h₁ : x ∈ m₁) (h₂ : x ∈ m₂) : m₁[x]ᵈ'h₁ = m₂[x]ᵈ'h₂ := by
  have heq := LawfulDMapy.dGetElem?_congr hequiv x
  simp only [dGetElem?_eq_some_dGetElem h₁,
             dGetElem?_eq_some_dGetElem h₂] at heq
  injection heq

theorem LawfulDMapy.dGetElem_congr' {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) (h₁ : x ∈ m₁) : m₁[x]ᵈ'h₁ = m₂[x]ᵈ'((hequiv.left _).mp h₁) := by
  have heq := LawfulDMapy.dGetElem?_congr hequiv x
  simp only [dGetElem?_eq_some_dGetElem h₁,
             dGetElem?_eq_some_dGetElem ((hequiv.left _).mp h₁)] at heq
  injection heq

theorem LawfulDMapy.dGetElem!_congr {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (x : α) [Inhabited (β x)] : m₁[x]ᵈ! = m₂[x]ᵈ! := by
  simp [dGetElem!_def, LawfulDMapy.dGetElem?_congr hequiv]

theorem LawfulDMapy.emptyWithCapacity_congr {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] (capacity₁ capacity₂ : Nat) :
  equiv (β:=β) (inst₂:=inst₂)
    (emptyWithCapacity (self:=inst₁) capacity₁)
    (emptyWithCapacity (self:=inst₂) capacity₂) := by
  rw [equiv_iff_equiv']; intro x
  simp [dGetElem?_empty]

open Classical in
theorem LawfulDMapy.insert_congr {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (k : α) (v : β k) :
  equiv (β:=β) (insert m₁ k v) (insert m₂ k v) := by
  rw [equiv_iff_equiv']
  intro x
  simp [dGetElem?_insert, equiv_iff_equiv'.mp hequiv _]

open Classical in
theorem LawfulDMapy.erase_congr {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) (k : α) :
  equiv (β:=β) (erase m₁ (self:=inst₁) k) (erase m₂ (self:=inst₂) k) := by
  rw [equiv_iff_equiv']
  intro x
  simp [dGetElem?_erase, equiv_iff_equiv'.mp hequiv _]

theorem LawfulDMapy.size_congr {γ₁ γ₂ α β} [inst₁ : DMapy γ₁ α β] [inst₂ : DMapy γ₂ α β]
  [LawfulDMapy γ₁ α β] [LawfulDMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (β:=β) m₁ m₂) : Sizy.size m₁ = Sizy.size m₂ := by
  apply LawfulDMapy.size_eq_of_keyEquiv; exact hequiv.left

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : DMapy (DHashMap α β) α β where
  emptyWithCapacity capacity := DHashMap.emptyWithCapacity (capacity:=capacity)
  insert := DHashMap.insert
  erase := DHashMap.erase
  size := DHashMap.size

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : LawfulDMapy (DHashMap α β) α β where
  not_mem_empty := by intro k n; simp [DMapy.emptyWithCapacity]
  mem_iff_isSome_dGetElem? := DHashMap.mem_iff_isSome_get?
  dGetElem?_insert_self := DHashMap.get?_insert_self
  dGetElem?_insert_ne := by
    intro m k a v h
    simp [DMapy.insert, dGetElem?, DHashMap.get?_insert, h]
  dGetElem?_erase_self := DHashMap.get?_erase_self
  dGetElem?_erase_ne := by
    intro m k a h
    simp [DMapy.erase, dGetElem?, DHashMap.get?_erase, h]
  size_zero_iff_forall_not_mem := by
    intro m; simp only [Sizy.size]
    apply DHashMap.size_zero_iff_forall_not_mem
  size_erase_mem := DHashMap.size_erase_mem

instance {α β} [Ord α] [LawfulEqOrd α] : DMapy (DTreeMap α β) α β where
  emptyWithCapacity _ := DTreeMap.empty
  insert := DTreeMap.insert
  erase := DTreeMap.erase
  size := DTreeMap.size

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulDMapy (DTreeMap α β) α β where
  not_mem_empty := DTreeMap.not_mem_emptyc
  mem_iff_isSome_dGetElem? := DTreeMap.mem_iff_isSome_get?
  dGetElem?_insert_self := DTreeMap.get?_insert_self
  dGetElem?_insert_ne := by
    intro m k a v hne
    simp only [DMapy.insert, dGetElem?, DTreeMap.get?_insert]
    rw [dite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  dGetElem?_erase_self := DTreeMap.get?_erase_self
  dGetElem?_erase_ne := by
    intro m k a hne
    simp only [DMapy.erase, dGetElem?, DTreeMap.get?_erase]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← DTreeMap.isEmpty_iff_forall_not_mem,
        DTreeMap.isEmpty_eq_size_eq_zero]
    simp [Sizy.size]
  size_erase_mem := DTreeMap.size_erase_mem

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : DMapy (ExtDHashMap α β) α β where
  emptyWithCapacity capacity := ExtDHashMap.emptyWithCapacity capacity
  insert := ExtDHashMap.insert
  erase := ExtDHashMap.erase
  size := ExtDHashMap.size

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : LawfulDMapy (ExtDHashMap α β) α β where
  not_mem_empty := by
    intro k n; simp [DMapy.emptyWithCapacity]
    apply ExtDHashMap.not_mem_empty
  mem_iff_isSome_dGetElem? := ExtDHashMap.mem_iff_isSome_get?
  dGetElem?_insert_self := ExtDHashMap.get?_insert_self
  dGetElem?_insert_ne := by
    intros m k a v hne
    simp [DMapy.insert, dGetElem?, ExtDHashMap.get?_insert, hne]
  dGetElem?_erase_self := ExtDHashMap.get?_erase_self
  dGetElem?_erase_ne := by
    intros m k a hne
    simp [DMapy.erase, dGetElem?, ExtDHashMap.get?_erase, hne]
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtDHashMap.eq_empty_iff_forall_not_mem,
        ExtDHashMap.eq_empty_iff_size_eq_zero]
    rfl
  size_erase_mem := ExtDHashMap.size_erase_mem

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : DMapy (ExtDTreeMap α β) α β where
  emptyWithCapacity _ := ExtDTreeMap.empty
  insert := ExtDTreeMap.insert
  erase := ExtDTreeMap.erase
  size := ExtDTreeMap.size

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulDMapy (ExtDTreeMap α β) α β where
  not_mem_empty := DTreeMap.not_mem_emptyc
  mem_iff_isSome_dGetElem? := ExtDTreeMap.mem_iff_isSome_get?
  dGetElem?_insert_self := ExtDTreeMap.get?_insert_self
  dGetElem?_insert_ne := by
    intro m k a v hne
    simp only [DMapy.insert, dGetElem?, ExtDTreeMap.get?_insert]
    rw [dite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  dGetElem?_erase_self := ExtDTreeMap.get?_erase_self
  dGetElem?_erase_ne := by
    intro m k a hne
    simp only [DMapy.erase, dGetElem?, ExtDTreeMap.get?_erase]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtDTreeMap.isEmpty_iff_forall_not_mem,
        ExtDTreeMap.isEmpty_eq_size_eq_zero]
    simp [Sizy.size]
  size_erase_mem := ExtDTreeMap.size_erase_mem

end DMapy

/-!
  This section defines an abstract datatype `Mapy` and its lawful
  counterpart `LawfulMapy`. An instance `inst : Mapy γ α β` denotes
  that `γ` models a finite map from `α` to `β`, i.e. a function
  from a finite collection of elements of type `α` (i.e. the keys) to `β`.

  `Mapy` is a subtype of `Membership` and `GetElem?`. Therefore,
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

  `LawfulMapy` specifies the behavior of the operations supported by
  `Mapy`, whereby the behavior of the operations are uniquely determined
  up to `Mapy.equiv`.
-/

section Mapy

/--
  A finite map which supports insertion, deletion, lookup,
  and computing size
-/
class Mapy (γ : Type u) (α : Type v) (β : Type w) extends
  Membership α γ, GetElem? γ α β (fun m x => x ∈ m), Sizy γ where
  emptyWithCapacity {γ α β} : Nat → γ
  insert : γ → α → β → γ
  erase {γ α β} : γ → α → γ

def Mapy_of_DMapy {γ α β} (inst : DMapy γ α (fun _ => β)) : Mapy γ α β where
  getElem := inst.dGetElem
  getElem? := inst.dGetElem?
  getElem! c i := inst.dGetElem! c i
  emptyWithCapacity := inst.emptyWithCapacity
  insert := inst.insert
  erase := inst.erase
  size := inst.size

def DMapy_of_Mapy {γ α β} (inst : Mapy γ α β) : DMapy γ α (fun _ => β) where
  dGetElem := inst.getElem
  dGetElem? := inst.getElem?
  dGetElem! c i := inst.getElem! c i
  emptyWithCapacity := inst.emptyWithCapacity
  insert := inst.insert
  erase := inst.erase
  size := inst.size

def DMapy_Mapy_inv {γ α β} {inst : DMapy γ α (fun _ => β)} :
  DMapy_of_Mapy (Mapy_of_DMapy inst) = inst := rfl

def Mapy_DMapy_inv {γ α β} {inst : Mapy γ α β} :
  Mapy_of_DMapy (DMapy_of_Mapy inst) = inst := rfl

def Mapy.keyEquiv {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  (m₁ : γ₁) (m₂ : γ₂) := ∀ (x : α), x ∈ m₁ ↔ x ∈ m₂

def Mapy.equiv {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  keyEquiv (α:=α) (β:=β) m₁ m₂ ∧ ∀ (x : α) (h₁ : x ∈ m₁) (h₂ : x ∈ m₂), m₁[x] = m₂[x]

def Mapy.equiv' {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α), m₁[x]? = m₂[x]?

def Mapy.keySubset {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α), x ∈ m₁ → x ∈ m₂

def Mapy.subset {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] (m₁ : γ₁) (m₂ : γ₂) :=
  ∀ (x : α) (y : β), m₁[x]? = y → m₂[x]? = y

theorem Mapy.keyEquiv.refl {γ α β} [inst : Mapy γ α β] {m : γ} : keyEquiv (α:=α) (β:=β) m m := by
  simp [keyEquiv]

theorem Mapy.keyEquiv.comm {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (α:=α) (β:=β) m₁ m₂ ↔ keyEquiv (α:=α) (β:=β) m₂ m₁ :=
  DMapy.keyEquiv.comm (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂)

theorem Mapy.keyEquiv.symm {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (α:=α) (β:=β) m₁ m₂ → keyEquiv (α:=α) (β:=β) m₂ m₁ :=
  Mapy.keyEquiv.comm.mp

theorem Mapy.keyEquiv.trans {γ₁ γ₂ γ₃ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] [inst₃ : Mapy γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : keyEquiv (α:=α) (β:=β) m₁ m₂ → keyEquiv (α:=α) (β:=β) m₂ m₃ → keyEquiv (α:=α) (β:=β) m₁ m₃ := by
  intro h₁ h₂ x
  rw [h₁, h₂]

theorem Mapy.equiv.refl {γ α β} [inst : Mapy γ α β] {m : γ} : equiv (α:=α) (β:=β) m m := by
  simp [equiv, keyEquiv]

theorem Mapy.equiv.comm {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (α:=α) (β:=β) m₁ m₂ ↔ equiv (α:=α) (β:=β) m₂ m₁ :=
  DMapy.equiv.comm (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂)

theorem Mapy.equiv.symm {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (α:=α) (β:=β) m₁ m₂ → equiv (α:=α) (β:=β) m₂ m₁ :=
  Mapy.equiv.comm.mp

theorem Mapy.equiv.trans {γ₁ γ₂ γ₃ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] [inst₃ : Mapy γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv (α:=α) (β:=β) m₁ m₂ → equiv (α:=α) (β:=β) m₂ m₃ → equiv (α:=α) (β:=β) m₁ m₃ :=
  DMapy.equiv.trans (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) (inst₃:=DMapy_of_Mapy inst₃)

theorem Mapy.equiv'.refl {γ α β} [inst : Mapy γ α β] {m : γ} : equiv' (α:=α) (β:=β) m m := by
  simp [equiv']

theorem Mapy.equiv'.comm {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (α:=α) (β:=β) m₁ m₂ ↔ equiv' (α:=α) (β:=β) m₂ m₁ :=
  DMapy.equiv'.comm (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂)

theorem Mapy.equiv'.symm {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (α:=α) (β:=β) m₁ m₂ → equiv' (α:=α) (β:=β) m₂ m₁ :=
  Mapy.equiv'.comm.mp

theorem Mapy.equiv'.trans {γ₁ γ₂ γ₃ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] [inst₃ : Mapy γ₃ α β]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv' (α:=α) (β:=β) m₁ m₂ → equiv' (α:=α) (β:=β) m₂ m₃ → equiv' (α:=α) (β:=β) m₁ m₃ := by
  intro h₁ h₂ x; rw [h₁, h₂]

theorem Mapy.keyEquiv_iff_keySubset {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : keyEquiv (α:=α) (β:=β) m₁ m₂ ↔ keySubset (α:=α) (β:=β) m₁ m₂ ∧ keySubset (α:=α) (β:=β) m₂ m₁ := by
  simp only [keySubset, keyEquiv]; apply Iff.intro <;> intro h
  case mp => simp [h]
  case mpr => intro x; apply Iff.intro <;> simp_all

theorem Mapy.equiv'_iff_subset {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv' (α:=α) (β:=β) m₁ m₂ ↔ subset (α:=α) (β:=β) m₁ m₂ ∧ subset (α:=α) (β:=β) m₂ m₁ := by
  simp only [subset, equiv']; apply Iff.intro <;> intro h
  case mp => simp [h]
  case mpr =>
    intro x
    have h₁ := h.left x; have h₂ := h.right x
    revert h₁ h₂ <;> cases m₁[x]? <;> cases m₂[x]? <;> simp

open Mapy

/--
  A finite map where the behavior of
  `· ∈ m , m[·]?, m[·]!, m[·], emptyWithCapacity, insert, erase, size`
  are uniquely determined up to `Mapy.equiv`
-/
class LawfulMapy (γ : Type u) (α : Type v) (β : Type w) [inst : Mapy γ α β]
  extends LawfulGetElem γ α β (fun m x => x ∈ m), LawfulMemSizy γ α where
  not_mem_empty : ∀ {k : α} {n : Nat}, ¬ k ∈ emptyWithCapacity (self:=inst) n
  mem_iff_isSome_getElem? : ∀ {m : γ} {k : α}, k ∈ m ↔ m[k]?.isSome
  getElem?_insert_self : ∀ {m : γ} {k : α} {v : β}, (insert m k v)[k]? = .some v
  getElem?_insert_ne : ∀ {m : γ} {k a : α} {v : β}, k ≠ a → (insert m k v)[a]? = m[a]?
  getElem?_erase_self : ∀ {m : γ} {k : α}, (erase (β:=β) m k)[k]? = .none
  getElem?_erase_ne : ∀ {m : γ} {k a : α}, k ≠ a → (erase (β:=β) m k)[a]? = m[a]?
  size_erase_mem : ∀ {m : γ} {k : α}, k ∈ m → Sizy.size (erase (β:=β) m k) + 1 = Sizy.size m

def LawfulMapy_of_LawfulDMapy {γ α β} [inst : Mapy γ α β]
  [instL : LawfulDMapy (inst:=DMapy_of_Mapy inst) γ α (fun _ => β)] :
  LawfulMapy γ α β where
  getElem?_def := instL.dGetElem?_def
  getElem!_def c i := by
    have h := instL.dGetElem!_def c i
    simp only [dGetElem!, dGetElem?, DMapy_of_Mapy] at h
    split at h <;> simp [*]
  not_mem_empty := instL.not_mem_empty
  mem_iff_isSome_getElem? := instL.mem_iff_isSome_dGetElem?
  getElem?_insert_self := instL.dGetElem?_insert_self
  getElem?_insert_ne := instL.dGetElem?_insert_ne
  getElem?_erase_self := instL.dGetElem?_erase_self
  getElem?_erase_ne := instL.dGetElem?_erase_ne
  size_zero_iff_forall_not_mem := instL.size_zero_iff_forall_not_mem
  size_erase_mem := instL.size_erase_mem

theorem LawfulMapy_of_LawfulDMapy' {γ α β} [inst : DMapy γ α (fun _ => β)]
  [instL : LawfulDMapy γ α (fun _ => β)] :
  LawfulMapy (inst:=Mapy_of_DMapy inst) γ α β :=
  LawfulMapy_of_LawfulDMapy (inst:=Mapy_of_DMapy inst)

def LawfulDMapy_of_LawfulMapy {γ α β} [inst : DMapy γ α (fun _ => β)]
  [instL : LawfulMapy (inst:=Mapy_of_DMapy inst) γ α β] :
  LawfulDMapy γ α (fun _ => β) where
  dGetElem?_def := instL.getElem?_def
  dGetElem!_def c i := by
    intro _; have h := instL.getElem!_def c i
    simp only [getElem!, getElem?, Mapy_of_DMapy] at h
    split at h <;> simp [*]
  not_mem_empty := instL.not_mem_empty
  mem_iff_isSome_dGetElem? := instL.mem_iff_isSome_getElem?
  dGetElem?_insert_self := instL.getElem?_insert_self
  dGetElem?_insert_ne := instL.getElem?_insert_ne
  dGetElem?_erase_self := instL.getElem?_erase_self
  dGetElem?_erase_ne := instL.getElem?_erase_ne
  size_zero_iff_forall_not_mem := instL.size_zero_iff_forall_not_mem
  size_erase_mem := instL.size_erase_mem

local instance LawfulDMapy_of_LawfulMapy' {γ α β} [inst : Mapy γ α β]
  [instL : LawfulMapy γ α β] :
  LawfulDMapy (inst:=DMapy_of_Mapy inst) γ α (fun _ => β) :=
  LawfulDMapy_of_LawfulMapy (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.mem_iff_getElem?_eq_some {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} : k ∈ m ↔ ∃ v, m[k]? = .some v :=
  LawfulDMapy.mem_iff_dGetElem?_eq_some (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.not_mem_iff_getElem?_eq_none {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} : k ∉ m ↔ m[k]? = .none :=
  LawfulDMapy.not_mem_iff_dGetElem?_eq_none (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.mem_insert {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k a : α} {v : β} :
  a ∈ insert m k v ↔ (k = a) ∨ a ∈ m :=
  LawfulDMapy.mem_insert (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.mem_erase {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k a : α} :
  a ∈ erase (β:=β) m k ↔ k ≠ a ∧ a ∈ m :=
  LawfulDMapy.mem_erase (inst:=DMapy_of_Mapy inst)

open Classical in
theorem LawfulMapy.getElem?_eq_none_iff {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β]
  {c : γ} {i : α} : c[i]? = .none ↔ i ∉ c := by
  simp only [getElem?_def]
  split <;> simp_all

theorem LawfulMapy.getElem?_eq_some_getElem {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} (h : k ∈ m) : m[k]? = .some m[k] :=
  LawfulDMapy.dGetElem?_eq_some_dGetElem (inst:=DMapy_of_Mapy inst) h

theorem LawfulMapy.getElem!_eq_getElem {γ α β} [Inhabited β] [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} (h : k ∈ m) :
  m[k]! = m[k] := LawfulDMapy.dGetElem!_eq_dGetElem (inst:=DMapy_of_Mapy inst) h

theorem LawfulMapy.getElem!_eq_default {γ α β} [Inhabited β] [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} (h : k ∉ m) :
  m[k]! = default := LawfulDMapy.dGetElem!_eq_default (inst:=DMapy_of_Mapy inst) h

theorem LawfulMapy.getElem!_eq_get!_getElem? {γ α β} [Inhabited β] [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} :
  m[k]! = m[k]?.get! := LawfulDMapy.dGetElem!_eq_get!_dGetElem? (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.getElem?_eq_some_getElem! {γ α β} [Inhabited β] [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} (h : k ∈ m) :
  m[k]? = .some m[k]! := LawfulDMapy.dGetElem?_eq_some_dGetElem! (inst:=DMapy_of_Mapy inst) h

theorem LawfulMapy.getElem?_eq_none {γ α β} [Inhabited β]  [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} (h : k ∉ m) :
  m[k]? = .none := LawfulDMapy.dGetElem?_eq_none (inst:=DMapy_of_Mapy inst) h

theorem LawfulMapy.getElem_eq_iff_getElem?_eq_some {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} {v : β} (h : k ∈ m) :
  m[k] = v ↔ m[k]? = .some v := LawfulDMapy.dGetElem_eq_iff_dGetElem?_eq_some (inst:=DMapy_of_Mapy inst) h

theorem LawfulMapy.getElem_eq_of_getElem?_eq_some {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} {v : β}
  (h : m[k]? = .some v) : m[k]'(mem_iff_getElem?_eq_some.mpr ⟨_, h⟩) = v :=
  LawfulDMapy.dGetElem_eq_of_dGetElem?_eq_some (inst:=DMapy_of_Mapy inst) h

theorem LawfulMapy.getElem_eq_getElem_iff_getElem?_eq_getElem? {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m₁ m₂ : γ} {k : α}
  (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) : m₁[k] = m₂[k] ↔ m₁[k]? = m₂[k]? :=
  LawfulDMapy.dGetElem_eq_dGetElem_iff_dGetElem?_eq_dGetElem? (inst:=DMapy_of_Mapy inst) h₁ h₂

theorem LawfulMapy.getElem_insert_self {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k : α} {v : β} :
  (insert m k v)[k]'(mem_insert.mpr (Or.inl rfl)) = v :=
  LawfulDMapy.dGetElem_insert_self (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.getElem_insert_ne {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k a : α} {v : β} (h₁ : a ∈ insert m k v) (h₂ : k ≠ a) :
  (insert m k v)[a] = m[a]'(Or.resolve_left (mem_insert.mp h₁) h₂) :=
  LawfulDMapy.dGetElem_insert_ne (inst:=DMapy_of_Mapy inst) h₁ h₂

theorem LawfulMapy.getElem_erase {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} {k a : α} (h' : a ∈ erase m k) :
  (erase (β:=β) m k)[a] = m[a]'((mem_erase.mp h').right) :=
  LawfulDMapy.dGetElem_erase (inst:=DMapy_of_Mapy inst) h'

theorem LawfulMapy.insert_mem_keyEquiv {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β]
  {m : γ} {k : α} {v : β} (hmem : k ∈ m) : keyEquiv (α:=α) (β:=β) (insert (self:=inst) m k v) m :=
  LawfulDMapy.insert_mem_keyEquiv (inst:=DMapy_of_Mapy inst) hmem

theorem LawfulMapy.erase_insert_not_mem_equiv {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β]
  {m : γ} {k : α} {v : β} (hnmem : k ∉ m) : equiv (α:=α) (β:=β) (erase (self:=inst) (insert (self:=inst) m k v) k) m :=
  LawfulDMapy.erase_insert_not_mem_equiv (inst:=DMapy_of_Mapy inst) hnmem

theorem LawfulMapy.erase_not_mem_equiv {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β]
  {m : γ} {k : α} (hnmem : k ∉ m) : equiv (α:=α) (β:=β) (erase (self:=inst) m k) m :=
  LawfulDMapy.erase_not_mem_equiv (inst:=DMapy_of_Mapy inst) hnmem

theorem LawfulMapy.insert_erase_mem_keyEquiv {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β]
  {m : γ} {k : α} {v : β} (hmem : k ∈ m) : keyEquiv (α:=α) (β:=β) (insert (erase (self:=inst) m k) k v) m :=
  LawfulDMapy.insert_erase_mem_keyEquiv (inst:=DMapy_of_Mapy inst) hmem

theorem LawfulMapy.insert_erase_getElem_eq_equiv {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β]
  {m : γ} {k : α} {v : β} (hmem : k ∈ m) (hget : m[k] = v) : equiv (α:=α) (β:=β) (insert (erase (self:=inst) m k) k v) m :=
  LawfulDMapy.insert_erase_dGetElem_eq_equiv (inst:=DMapy_of_Mapy inst) hmem hget

theorem LawfulMapy.exists_key_list {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} :
  ∃ (l : List α), l.length = Sizy.size m ∧ l.Nodup ∧ ∀ k, k ∈ m ↔ k ∈ l :=
  LawfulDMapy.exists_key_list (inst:=DMapy_of_Mapy inst)

noncomputable def LawfulMapy.exKeyList {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] (m : γ) : List α :=
  (exists_key_list (α:=α) (β:=β) (m:=m)).choose

noncomputable def LawfulMapy.length_exKeyList_eq_size {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} :
  (exKeyList (α:=α) (β:=β) m).length = Sizy.size m :=
  (Exists.choose_spec exists_key_list).left

noncomputable def LawfulMapy.length_exKeyList_nodup {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} :
  (exKeyList (α:=α) (β:=β) m).Nodup :=
  (Exists.choose_spec exists_key_list).right.left

noncomputable def LawfulMapy.length_exKeyList_equiv {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ} :
  ∀ k, k ∈ m ↔ k ∈ (exKeyList (α:=α) (β:=β) m) :=
  (Exists.choose_spec exists_key_list).right.right

theorem LawfulMapy.size_le_of_keySubset {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hsub : keySubset (α:=α) (β:=β) m₁ m₂) : Sizy.size m₁ ≤ Sizy.size m₂ :=
  LawfulDMapy.size_le_of_keySubset (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) hsub

theorem LawfulMapy.size_eq_of_keyEquiv {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : keyEquiv (α:=α) (β:=β) m₁ m₂) : Sizy.size m₁ = Sizy.size m₂ :=
  LawfulDMapy.size_eq_of_keyEquiv (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) hequiv

theorem LawfulMapy.keyEquiv_iff_size_eq_and_keySubset {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂} :
  keyEquiv (α:=α) (β:=β) m₁ m₂ ↔ Sizy.size m₁ = Sizy.size m₂ ∧ keySubset (α:=α) (β:=β) m₁ m₂ :=
  LawfulDMapy.keyEquiv_iff_size_eq_and_keySubset (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂)

theorem LawfulMapy.size_insert_mem {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ}
  {k : α} {v : β} (hmem : k ∈ m) : Sizy.size (insert (self:=inst) m k v) = Sizy.size m :=
  LawfulDMapy.size_insert_mem (inst:=DMapy_of_Mapy inst) hmem

theorem LawfulMapy.size_insert_not_mem {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ}
  {k : α} {v : β} (hnmem : k ∉ m) : Sizy.size (insert (self:=inst) m k v) = Sizy.size m + 1 :=
  LawfulDMapy.size_insert_not_mem (inst:=DMapy_of_Mapy inst) hnmem

theorem LawfulMapy.size_insert_le {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ}
  {k : α} {v : β} : Sizy.size (insert m k v) ≤ Sizy.size m + 1 :=
  LawfulDMapy.size_insert_le (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.le_size_insert {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ}
  {k : α} {v : β} : Sizy.size m ≤ Sizy.size (insert m k v) :=
  LawfulDMapy.le_size_insert (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.size_insert_gt_zero {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ}
  {k : α} {v : β} : Sizy.size (insert m k v) > 0 :=
  LawfulDMapy.size_insert_gt_zero (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.size_erase_not_mem {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ}
  {k : α} (hnm : k ∉ m) : Sizy.size (erase (β:=β) m k) = Sizy.size m :=
  LawfulDMapy.size_erase_not_mem (inst:=DMapy_of_Mapy inst) hnm

theorem LawfulMapy.size_erase_le {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ}
  {k : α} : Sizy.size (erase (β:=β) m k) ≤ Sizy.size m :=
  LawfulDMapy.size_erase_le (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.le_size_erase {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β] {m : γ}
  {k : α} : Sizy.size m ≤ Sizy.size (erase (β:=β) m k) + 1 :=
  LawfulDMapy.le_size_erase (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.getElem?_empty {γ α β} [inst : Mapy γ α β] [LawfulMapy γ α β]
  {capacity : Nat} {k : α} : (emptyWithCapacity (self:=inst) capacity)[k]? = .none :=
  LawfulDMapy.dGetElem?_empty (inst:=DMapy_of_Mapy inst)

theorem LawfulMapy.getElem?_insert {γ α β} [inst : Mapy γ α β]
  [LawfulMapy γ α β] [DecidableEq α] {m : γ} {k a : α} {v : β} :
  (insert m k v)[a]? = if (k = a) then some v else m[a]? := by
  have h := LawfulDMapy.dGetElem?_insert (inst:=DMapy_of_Mapy inst) (m:=m) (k:=k) (a:=a) (v:=v)
  simp only [dGetElem?, DMapy_of_Mapy] at h
  rw [h]; split
  case isTrue heq => cases heq <;> rfl
  case isFalse => rfl

theorem LawfulMapy.getElem?_erase {γ α β} [inst : Mapy γ α β]
  [LawfulMapy γ α β] [DecidableEq α] {m : γ} {k a : α} :
  (erase (self:=inst) m k)[a]? = if (k = a) then .none else m[a]? :=
  LawfulDMapy.dGetElem?_erase (inst:=DMapy_of_Mapy inst)

open Classical in
theorem LawfulMapy.getElem?_eq_none_iff_getElem?_eq_none_of_keyEquiv {γ₁ γ₂ α β}
  [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (hequiv : Mapy.keyEquiv (α:=α) (β:=β) m₁ m₂)
  (k : α) : m₁[k]? = .none ↔ m₂[k]? = .none := by
  simp [hequiv k]

theorem LawfulMapy.equiv_iff_equiv' {γ₁ γ₂ α β}
  [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} :
  Mapy.equiv (α:=α) (β:=β) m₁ m₂ ↔ Mapy.equiv' (α:=α) (β:=β) m₁ m₂ :=
  LawfulDMapy.equiv_iff_equiv' (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂)

theorem LawfulMapy.equiv_iff_subset {γ₁ γ₂ α β}
  [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} : equiv (α:=α) (β:=β) m₁ m₂ ↔ subset (α:=α) (β:=β) m₁ m₂ ∧ subset (α:=α) (β:=β) m₂ m₁ := by
  rw [LawfulMapy.equiv_iff_equiv', Mapy.equiv'_iff_subset]

theorem LawfulMapy.keySubset_of_subset {γ₁ γ₂ α β}
  [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β] [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (h : subset (α:=α) (β:=β) m₁ m₂) : keySubset (α:=α) (β:=β) m₁ m₂ := by
  simp only [subset] at h
  intro x
  simp only [mem_iff_isSome_getElem?]
  have hx := h x
  revert hx
  cases m₁[x]? <;> grind

theorem LawfulMapy.mem_congr {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  {m₁ : γ₁} {m₂ : γ₂} (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) : x ∈ m₁ ↔ x ∈ m₂ := hequiv.left _

theorem LawfulMapy.getElem?_congr {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) : m₁[x]? = m₂[x]? :=
  LawfulMapy.equiv_iff_equiv'.mp hequiv _

theorem LawfulMapy.getElem_congr {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) (h₁ : x ∈ m₁) (h₂ : x ∈ m₂) : m₁[x] = m₂[x] :=
  LawfulDMapy.dGetElem_congr (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) hequiv x h₁ h₂

theorem LawfulMapy.getElem_congr' {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) (h₁ : x ∈ m₁) : m₁[x] = m₂[x]'((hequiv.left _).mp h₁) :=
  LawfulDMapy.dGetElem_congr' (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) hequiv x h₁

theorem LawfulMapy.getElem!_congr {γ₁ γ₂ α β} [Inhabited β] [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (x : α) : m₁[x]! = m₂[x]! :=
  LawfulDMapy.dGetElem!_congr (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) hequiv x

theorem LawfulMapy.emptyWithCapacity_congr {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] (capacity₁ capacity₂ : Nat) :
  equiv (α:=α) (β:=β)
    (emptyWithCapacity (self:=inst₁) capacity₁)
    (emptyWithCapacity (self:=inst₂) capacity₂) :=
  LawfulDMapy.emptyWithCapacity_congr (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) _ _

theorem LawfulMapy.insert_congr {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (k : α) (v : β) :
  equiv (α:=α) (β:=β) (insert m₁ k v) (insert m₂ k v) :=
  LawfulDMapy.insert_congr (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) hequiv k v

open Classical in
theorem LawfulMapy.erase_congr {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (k : α) :
  equiv (α:=α) (β:=β) (erase m₁ (self:=inst₁) k) (erase m₂ (self:=inst₂) k) :=
  LawfulDMapy.erase_congr (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) hequiv k

theorem LawfulMapy.size_congr {γ₁ γ₂ α β} [inst₁ : Mapy γ₁ α β] [inst₂ : Mapy γ₂ α β]
  [LawfulMapy γ₁ α β] [LawfulMapy γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) (β:=β) m₁ m₂) : Sizy.size m₁ = Sizy.size m₂ :=
  LawfulDMapy.size_congr (inst₁:=DMapy_of_Mapy inst₁) (inst₂:=DMapy_of_Mapy inst₂) hequiv

instance {α β} [BEq α] [Hashable α] : Mapy (HashMap α β) α β where
  emptyWithCapacity capacity := HashMap.emptyWithCapacity (capacity:=capacity)
  insert := HashMap.insert
  erase := HashMap.erase
  size := HashMap.size

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : LawfulMapy (HashMap α β) α β where
  not_mem_empty := by intro k n; simp [Mapy.emptyWithCapacity]
  mem_iff_isSome_getElem? := HashMap.mem_iff_isSome_getElem?
  getElem?_insert_self := HashMap.getElem?_insert_self
  getElem?_insert_ne := by
    intro m k a v h
    simp [Mapy.insert, HashMap.getElem?_insert, h]
  getElem?_erase_self := HashMap.getElem?_erase_self
  getElem?_erase_ne := by
    intro m k a h
    simp [Mapy.erase, HashMap.getElem?_erase, h]
  size_erase_mem := HashMap.size_erase_mem

instance {α} : Mapy (OptArr α) Nat α where
  emptyWithCapacity capacity := OptArr.emptyWithCapacity capacity
  insert := OptArr.insert
  erase := OptArr.erase
  size := OptArr.size

instance {α} : LawfulMapy (OptArr α) Nat α where
  not_mem_empty := OptArr.not_mem_empty
  mem_iff_isSome_getElem? := OptArr.mem_iff_isSome_getElem?
  getElem?_insert_self := OptArr.getElem?_insert_self
  getElem?_insert_ne := OptArr.getElem?_insert_ne
  getElem?_erase_self := OptArr.getElem?_erase_self
  getElem?_erase_ne := OptArr.getElem?_erase_ne
  size_erase_mem := OptArr.size_erase_mem

instance {α β} [Ord α] : Mapy (TreeMap α β) α β where
  emptyWithCapacity _ := TreeMap.empty
  insert := TreeMap.insert
  erase := TreeMap.erase
  size := TreeMap.size

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulMapy (TreeMap α β) α β where
  not_mem_empty := TreeMap.not_mem_emptyc
  mem_iff_isSome_getElem? := TreeMap.mem_iff_isSome_getElem?
  getElem?_insert_self := TreeMap.getElem?_insert_self
  getElem?_insert_ne := by
    intro m k a v hne
    simp only [Mapy.insert, TreeMap.getElem?_insert]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  getElem?_erase_self := TreeMap.getElem?_erase_self
  getElem?_erase_ne := by
    intro m k a hne
    simp only [Mapy.erase, TreeMap.getElem?_erase]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  size_erase_mem := TreeMap.size_erase_mem

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Mapy (ExtHashMap α β) α β where
  emptyWithCapacity capacity := ExtHashMap.emptyWithCapacity capacity
  insert := ExtHashMap.insert
  erase := ExtHashMap.erase
  size := ExtHashMap.size

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : LawfulMapy (ExtHashMap α β) α β where
  not_mem_empty := by intro k n; simp [Mapy.emptyWithCapacity]
  mem_iff_isSome_getElem? := ExtHashMap.mem_iff_isSome_getElem?
  getElem?_insert_self := ExtHashMap.getElem?_insert_self
  getElem?_insert_ne := by
    intros m k a v hne
    simp [Mapy.insert, ExtHashMap.getElem?_insert, hne]
  getElem?_erase_self := ExtHashMap.getElem?_erase_self
  getElem?_erase_ne := by
    intros m k a hne
    simp [Mapy.erase, ExtHashMap.getElem?_erase, hne]
  size_erase_mem := Std.ExtHashMap.size_erase_mem

instance {α β} [Ord α] [TransOrd α] : Mapy (ExtTreeMap α β) α β where
  emptyWithCapacity _ := ExtTreeMap.empty
  insert := ExtTreeMap.insert
  erase := ExtTreeMap.erase
  size := ExtTreeMap.size

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulMapy (ExtTreeMap α β) α β where
  not_mem_empty := TreeMap.not_mem_emptyc
  mem_iff_isSome_getElem? := ExtTreeMap.mem_iff_isSome_getElem?
  getElem?_insert_self := ExtTreeMap.getElem?_insert_self
  getElem?_insert_ne := by
    intro m k a v hne
    simp only [Mapy.insert, ExtTreeMap.getElem?_insert]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  getElem?_erase_self := ExtTreeMap.getElem?_erase_self
  getElem?_erase_ne := by
    intro m k a hne
    simp only [Mapy.erase, ExtTreeMap.getElem?_erase]
    rw [ite_cond_eq_false]
    rw [LawfulEqOrd.compare_eq_iff_eq]
    simp [hne]
  size_erase_mem := ExtTreeMap.size_erase_mem

end Mapy

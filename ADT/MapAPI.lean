/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import ADT.MapLike
import ADT.Mem
import ADT.ListLike
open Std

/-!
# API for maps and dependently typed maps

The typeclasses defined in this file extends those
defined in `MapLike` with useful operations.
-/

section DMapAPI

class DMapAPI (γ : Type u) (α : Type v) (β : α → Type w) extends
  DMapLike γ α β, IsEmpty γ, Contains γ α where
  insertIfNew : γ → (a : α) → β a → γ
  containsThenInsert : γ → (a : α) → β a → Bool × γ
  containsThenInsertIfNew : γ → (a : α) → β a → Bool × γ
  getThenInsertIfNew? : γ → (a : α) → β a → Option (β a) × γ
  filter : ((a : α) → β a → Bool) → γ → γ
  modify : γ → (a : α) → (β a → β a) → γ
  alter : γ → (a : α) → (Option (β a) → Option (β a)) → γ

open DMapAPI DMapLike

class LawfulDMapAPI (γ : Type u) (α : Type v) (β : α → Type w) [inst : DMapAPI γ α β]
  extends LawfulDMapLike γ α β, LawfulIsEmptySize γ, LawfulContainsMem γ α where
  dGetElem?_insertIfNew_self {m : γ} {k : α} {v : β k} (h : k ∉ m) :
    (insertIfNew m k v)[k]ᵈ? = .some v
  dGetElem?_insertIfNew_ne {m : γ} {k a : α} {v : β k} (h : k ≠ a ∨ k ∈ m) :
    (insertIfNew m k v)[a]ᵈ? = m[a]ᵈ?
  containsThenInsert_fst {m : γ} {k : α} {v : β k} : (containsThenInsert m k v).fst = Contains.contains m k
  containsThenInsert_snd {m : γ} {k : α} {v : β k} : (containsThenInsert m k v).snd = insert m k v
  containsThenInsertIfNew_fst {m : γ} {k : α} {v : β k} : (containsThenInsertIfNew m k v).fst = Contains.contains m k
  containsThenInsertIfNew_snd {m : γ} {k : α} {v : β k} : (containsThenInsertIfNew m k v).snd = insertIfNew m k v
  getThenInsertIfNew?_fst {m : γ} {k : α} {v : β k} : (getThenInsertIfNew? m k v).fst = m[k]ᵈ?
  getThenInsertIfNew?_snd {m : γ} {k : α} {v : β k} : (getThenInsertIfNew? m k v).snd = insertIfNew m k v
  dGetElem?_filter {m : γ} {f : (a : α) → β a → Bool} {k : α} : (filter f m)[k]ᵈ? = Option.filter (f k) m[k]ᵈ?
  dGetElem?_modify_self {m : γ} {k : α} {f : β k → β k} :
    (modify m k f)[k]ᵈ? = Option.map f m[k]ᵈ?
  dGetElem?_modify_ne {m : γ} {k k' : α} {f : β k → β k} (h : k ≠ k') :
    (modify m k f)[k']ᵈ? = m[k']ᵈ?
  dGetElem?_alter_self {m : γ} {k : α} {f : Option (β k) → Option (β k)} :
    (alter m k f)[k]ᵈ? = f m[k]ᵈ?
  dGetElem?_alter_ne {m : γ} {k k' : α} {f : Option (β k) → Option (β k)} (h : k ≠ k') :
    (alter m k f)[k']ᵈ? = m[k']ᵈ?

namespace LawfulDMapAPI

  open LawfulDMapLike

  theorem isEmpty_congr {γ₁ γ₂ α β} [inst₁ : DMapAPI γ₁ α β] [inst₂ : DMapAPI γ₂ α β]
    [LawfulDMapAPI γ₁ α β] [LawfulDMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (β:=β) m₁ m₂) : IsEmpty.isEmpty m₁ = IsEmpty.isEmpty m₂ := by
    rw [Bool.eq_iff_iff]
    simp only [LawfulIsEmptySize.isEmpty_iff_size_eq_zero]
    rw [size_congr hequiv]

  theorem isEmpty_erase {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} : IsEmpty.isEmpty (erase (β:=β) m k) = (IsEmpty.isEmpty m || (Size.size m == 1 && Contains.contains m k)) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
               LawfulContainsMem.contains_iff_mem, LawfulIsEmptySize.isEmpty_iff_size_eq_zero]
    grind [size_erase_mem, size_erase_not_mem]

  theorem isEmpty_insert_eq_false {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {v : β k} : IsEmpty.isEmpty (insert m k v) = false := by
    rw [LawfulIsEmptySize.isEmpty_eq_false_iff_size_gt_zero]
    apply size_insert_gt_zero

  theorem contains_congr {γ₁ γ₂ α β} [inst₁ : DMapAPI γ₁ α β] [inst₂ : DMapAPI γ₂ α β]
    [LawfulDMapAPI γ₁ α β] [LawfulDMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (β:=β) m₁ m₂) (k : α) : Contains.contains m₁ k = Contains.contains m₂ k := by
    rw [Bool.eq_iff_iff]
    simp only [LawfulContainsMem.contains_iff_mem]
    rw [mem_congr hequiv]

  theorem not_contains_iff_not_mem {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} : Contains.contains m k = false ↔ k ∉ m := by
    grind [LawfulContainsMem.contains_iff_mem]

  theorem isEmpty_iff_forall_not_mem {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} : IsEmpty.isEmpty m ↔ ∀ (x : α), x ∉ m := by
    rw [LawfulIsEmptySize.isEmpty_iff_size_eq_zero, LawfulMemSize.size_zero_iff_forall_not_mem (α:=α)]

  theorem insertIfNew_equiv_of_mem {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {v : β k} (h : k ∈ m) : equiv (β:=β) (insertIfNew m k v) m := by
    simp only [equiv_iff_equiv', equiv']
    grind [dGetElem?_insertIfNew_ne]

  open Classical in
  theorem insertIfNew_equiv_of_not_mem {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {v : β k} (h : k ∉ m) : equiv (β:=β) (insertIfNew m k v) (insert m k v) := by
    simp only [equiv_iff_equiv', equiv', dGetElem?_insert]
    grind [dGetElem?_insertIfNew_ne, dGetElem?_insertIfNew_self]

  theorem insertIfNew_equiv {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {v : β k} : equiv (β:=β) (insertIfNew m k v) (if Contains.contains m k then m else insert m k v) := by
    split
    case isTrue h =>
      apply insertIfNew_equiv_of_mem; apply LawfulContainsMem.contains_iff_mem.mp h
    case isFalse h =>
      apply insertIfNew_equiv_of_not_mem; grind [LawfulContainsMem.contains_iff_mem]

  theorem insertIfNew_congr {γ₁ γ₂ α β} [inst₁ : DMapAPI γ₁ α β] [inst₂ : DMapAPI γ₂ α β]
    [LawfulDMapAPI γ₁ α β] [LawfulDMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (β:=β) m₁ m₂) (k : α) (v : β k) :
    equiv (β:=β) (insertIfNew m₁ k v) (insertIfNew m₂ k v) := by
    apply equiv.trans insertIfNew_equiv
    apply equiv.trans _ (equiv.symm insertIfNew_equiv)
    rw [contains_congr hequiv]; cases (Contains.contains m₂ k)
    case false => simp [insert_congr hequiv]
    case true => simp [*]

  theorem size_insertIfNew_mem {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {v : β k} (h : k ∈ m) : Size.size (insertIfNew m k v) = Size.size m := by
    rw [size_congr (insertIfNew_equiv_of_mem h)]

  theorem size_insertIfNew_not_mem {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {v : β k} (h : k ∉ m) : Size.size (insertIfNew m k v) = Size.size m + 1 := by
    rw [size_congr (insertIfNew_equiv_of_not_mem h), size_insert_not_mem h]

  theorem size_insertIfNew {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} [Decidable (k ∈ m)] {v : β k} : Size.size (insertIfNew m k v) = if k ∈ m then Size.size m else Size.size m + 1 := by
    grind [size_insertIfNew_mem, size_insertIfNew_not_mem]

  theorem mem_insertIfNew' {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k a : α} {v : β k} : a ∈ DMapAPI.insertIfNew m k v ↔ k = a ∨ a ∈ m := by
    rw [mem_congr insertIfNew_equiv]
    grind [mem_insert, LawfulContainsMem.contains_iff_mem]

  theorem mem_insertIfNew {γ α β} [BEq α] [LawfulBEq α] [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k a : α} {v : β k} : a ∈ DMapAPI.insertIfNew m k v ↔ k == a ∨ a ∈ m := by
    simp [mem_insertIfNew']

  theorem mem_of_mem_insertIfNew' {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β] {m : γ} {k a : α} {v : β k} :
    a ∈ insertIfNew m k v → k ≠ a ∨ k ∈ m → a ∈ m := by
    rw [mem_insertIfNew']; grind

  theorem contains_insertIfNew {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k a : α} {v : β k} : Contains.contains (DMapAPI.insertIfNew m k v) a ↔ k = a ∨ a ∈ m := by
    simp [LawfulContainsMem.contains_iff_mem, mem_insertIfNew']

  theorem dGetElem_insertIfNew_ne {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k a : α} {v : β k} {h₁ : a ∈ insertIfNew m k v} {h₂ : k ≠ a ∨ k ∈ m} :
    (insertIfNew m k v)[a]ᵈ'h₁ = m[a]ᵈ'(mem_of_mem_insertIfNew' h₁ h₂) := by
    rw [dGetElem_eq_dGetElem_iff_dGetElem?_eq_dGetElem?, dGetElem?_insertIfNew_ne h₂]

  theorem dGetElem_insertIfNew_ne' {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k a : α} {v : β k} {h : a ∈ m} :
    (insertIfNew m k v)[a]ᵈ'(mem_insertIfNew'.mpr (Or.inr h)) = m[a]ᵈ'h := by
    rw [dGetElem_eq_dGetElem_iff_dGetElem?_eq_dGetElem?, dGetElem?_insertIfNew_ne]; grind

  theorem dGetElem_insertIfNew_self {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k: α} {v : β k} {h : k ∉ m} :
    (insertIfNew m k v)[k]ᵈ'(by simp [mem_insertIfNew']) = v := by
    rw [dGetElem_eq_iff_dGetElem?_eq_some, dGetElem?_insertIfNew_self h]

  theorem dGetElem!_insertIfNew_ne {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k a : α} [Inhabited (β a)] {v : β k} {h : k ≠ a ∨ k ∈ m} :
    (insertIfNew m k v)[a]ᵈ! = m[a]ᵈ! := by
    simp [dGetElem!_eq_get!_dGetElem?, dGetElem?_insertIfNew_ne h]

  theorem dGetElem!_insertIfNew_self {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} [Inhabited (β k)] {v : β k} {h : k ∉ m} :
    (insertIfNew m k v)[k]ᵈ! = v := by
    simp [dGetElem!_eq_get!_dGetElem?, dGetElem?_insertIfNew_self h]

  theorem filter_congr {γ₁ γ₂ α β} [inst₁ : DMapAPI γ₁ α β] [inst₂ : DMapAPI γ₂ α β]
    [LawfulDMapAPI γ₁ α β] [LawfulDMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (β:=β) m₁ m₂) (f : (a : α) → β a → Bool) :
    equiv (β:=β) (filter f m₁) (filter f m₂) := by
    rw [equiv_iff_equiv']; intro x
    simp only [dGetElem?_filter, dGetElem?_congr hequiv]

  theorem mem_filter {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} {k : α} :
    k ∈ filter f m ↔ ∃ h, f k (m[k]ᵈ'h) = true := by
    rw [mem_iff_dGetElem?_eq_some, dGetElem?_filter]
    simp only [Option.filter]; split
    case h_1 heq =>
      simp [dGetElem_eq_of_dGetElem?_eq_some heq, mem_iff_dGetElem?_eq_some.mpr ⟨_, heq⟩]
    case h_2 heq =>
      simp [not_mem_iff_dGetElem?_eq_none.mpr heq]

  theorem mem_of_mem_filter {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} {k : α} (h : k ∈ filter f m) : k ∈ m := by
    apply (mem_filter.mp h).choose

  theorem filter_subset {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} :
    subset (β:=β) (filter f m) m := by
    intro k v; simp_all [dGetElem?_filter]

  theorem filter_keySubset {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} :
    keySubset (β:=β) (filter f m) m := fun _ => mem_of_mem_filter

  theorem contains_filter {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} {k : α} :
    Contains.contains (filter f m) k ↔ Option.any (f k) m[k]ᵈ? := by
    simp only [LawfulContainsMem.contains_iff_mem, mem_iff_dGetElem?_eq_some, dGetElem?_filter]
    simp only [Option.filter, Option.any]; grind

  theorem contains_of_contains_filter {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} {k : α} (h : Contains.contains (filter f m) k) : Contains.contains m k := by
    simp only [LawfulContainsMem.contains_iff_mem, mem_filter] at *
    apply h.choose

  theorem dGetElem_filter {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} {k : α} {h' : k ∈ filter f m} :
    (filter f m)[k]ᵈ'h' = m[k]ᵈ'(mem_of_mem_filter h') := by
    apply (dGetElem_eq_dGetElem_iff_dGetElem?_eq_dGetElem? _ _).mpr
    have ⟨h, heq⟩ := mem_filter.mp h'
    simp [dGetElem?_filter, dGetElem?_eq_some_dGetElem h, Option.filter, heq]

  theorem dGetElem!_filter {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} {k : α} [Inhabited (β k)] :
    (filter f m)[k]ᵈ! = (Option.filter (f k) m[k]ᵈ?).get! := by
    rw [dGetElem!_eq_get!_dGetElem?, dGetElem?_filter]

  theorem isEmpty_filter_iff {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} :
    IsEmpty.isEmpty (filter f m) ↔ ∀ (k : α) (h : k ∈ m), f k (m[k]ᵈ'h) = false := by
    simp [isEmpty_iff_forall_not_mem, mem_filter]

  theorem isEmpty_filter_eq_false_iff {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} :
    IsEmpty.isEmpty (filter f m) = false ↔ ∃ (k : α) (h : k ∈ m), f k (m[k]ᵈ'h) := by
    rw [Bool.eq_false_iff, Ne, isEmpty_filter_iff]; simp

  theorem size_filter_le_size {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} :
    Size.size (filter f m) ≤ Size.size m := by
    apply size_le_of_keySubset
    apply filter_keySubset

  theorem size_filter_eq_size_iff {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {f : (a : α) → β a → Bool} :
    Size.size (filter f m) = Size.size m ↔ ∀ (k : α) (h : k ∈ m), f k (m[k]ᵈ'h) := by
    have hsub := filter_keySubset (m:=m) (f:=f)
    have hequiv := keyEquiv_iff_size_eq_and_keySubset (β:=β) (m₁:=filter f m) (m₂:=m)
    simp only [hsub, and_true] at hequiv
    simp only [← hequiv, keyEquiv, mem_filter]
    grind

  theorem modify_congr {γ₁ γ₂ α β} [inst₁ : DMapAPI γ₁ α β] [inst₂ : DMapAPI γ₂ α β]
    [LawfulDMapAPI γ₁ α β] [LawfulDMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (β:=β) m₁ m₂) (k : α) (f : β k → β k) :
    equiv (β:=β) (modify m₁ k f) (modify m₂ k f) := by
    rw [equiv_iff_equiv']; intro k'
    by_cases k = k'
    case pos heq => cases heq; simp only [dGetElem?_modify_self, dGetElem?_congr hequiv]
    case neg hne => simp only [dGetElem?_modify_ne hne, dGetElem?_congr hequiv]

  theorem mem_modify {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k k' : α} {f : β k → β k} : k' ∈ modify m k f ↔ k' ∈ m := by
    simp only [mem_iff_isSome_dGetElem?]
    by_cases k = k'
    case pos heq => cases heq; rw [dGetElem?_modify_self]; simp
    case neg hne => rw [dGetElem?_modify_ne hne]

  theorem contains_modify {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k k' : α} {f : β k → β k} : Contains.contains (modify m k f) k' = Contains.contains m k' := by
    apply Bool.eq_iff_iff.mpr
    simp only [LawfulContainsMem.contains_iff_mem, mem_modify]

  theorem modify_keyEquiv {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : β k → β k} : keyEquiv (β:=β) (modify m k f) m :=
    fun _ => mem_modify

  theorem size_modify {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : β k → β k} : Size.size (modify m k f) = Size.size m := by
    apply size_eq_of_keyEquiv; apply modify_keyEquiv

  theorem isEmpty_modify {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : β k → β k} : IsEmpty.isEmpty (modify m k f) = IsEmpty.isEmpty m := by
    apply Bool.eq_iff_iff.mpr
    simp only [LawfulIsEmptySize.isEmpty_iff_size_eq_zero, size_modify]

  theorem dGetElem_modify_self {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : β k → β k} (h : k ∈ modify m k f) :
    (DMapAPI.modify m k f)[k]ᵈ'h = f (m[k]ᵈ'(mem_modify.mp h)) := by
    rw [dGetElem_eq_iff_dGetElem?_eq_some]
    rw [dGetElem?_modify_self, dGetElem?_eq_some_dGetElem (mem_modify.mp h)]
    rfl

  theorem dGetElem_modify_self' {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : β k → β k} (h : k ∈ m) :
    (DMapAPI.modify m k f)[k]ᵈ'(mem_modify.mpr h) = f (m[k]ᵈ'h) :=
    dGetElem_modify_self (mem_modify.mpr h)

  theorem dGetElem_modify_ne {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k a : α} {f : β k → β k} (h : a ∈ modify m k f) (hne : k ≠ a) :
    (DMapAPI.modify m k f)[a]ᵈ'h = m[a]ᵈ'(mem_modify.mp h) := by
    rw [dGetElem_eq_dGetElem_iff_dGetElem?_eq_dGetElem?]
    rw [dGetElem?_modify_ne hne]

  theorem dGetElem_modify_ne' {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k a : α} {f : β k → β k} (h : a ∈ m) (hne : k ≠ a) :
    (DMapAPI.modify m k f)[a]ᵈ'(mem_modify.mpr h) = m[a]ᵈ'h :=
    dGetElem_modify_ne (mem_modify.mpr h) hne

  theorem dGetElem!_modify_self {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} [Inhabited (β k)] {f : β k → β k} : (modify m k f)[k]ᵈ! = (Option.map f m[k]ᵈ?).get! := by
    rw [dGetElem!_eq_get!_dGetElem?, dGetElem?_modify_self]

  theorem dGetElem!_modify_ne {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k k' : α} [Inhabited (β k')] {f : β k → β k} (h : k ≠ k'):
    (modify m k f)[k']ᵈ! = m[k']ᵈ! := by
    simp only [dGetElem!_eq_get!_dGetElem?, dGetElem?_modify_ne h]

  theorem alter_congr {γ₁ γ₂ α β} [inst₁ : DMapAPI γ₁ α β] [inst₂ : DMapAPI γ₂ α β]
    [LawfulDMapAPI γ₁ α β] [LawfulDMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (β:=β) m₁ m₂) (k : α) (f : Option (β k) → Option (β k)) :
    equiv (β:=β) (alter m₁ k f) (alter m₂ k f) := by
    rw [equiv_iff_equiv']; intro k'
    by_cases k = k'
    case pos heq => cases heq; simp only [dGetElem?_alter_self, dGetElem?_congr hequiv]
    case neg hne => simp only [dGetElem?_alter_ne hne, dGetElem?_congr hequiv]

  theorem alter_none {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)}
    (hnone : f m[k]ᵈ? = .none) : equiv (β:=β) (alter m k f) (erase (β:=β) m k) := by
    rw [equiv_iff_equiv']; intro x
    by_cases k = x
    case pos heq =>
      cases heq
      rw [dGetElem?_alter_self, dGetElem?_erase_self, hnone]
    case neg hne =>
      rw [dGetElem?_alter_ne hne, dGetElem?_erase_ne hne]

  theorem alter_some {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {v : β k} {f : Option (β k) → Option (β k)}
    (hsome : f m[k]ᵈ? = .some v) : equiv (β:=β) (alter m k f) (insert m k v) := by
    rw [equiv_iff_equiv']; intro x
    by_cases k = x
    case pos heq =>
      cases heq
      rw [dGetElem?_alter_self, dGetElem?_insert_self, hsome]
    case neg hne =>
      rw [dGetElem?_alter_ne hne, dGetElem?_insert_ne hne]

  theorem mem_alter_self {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)} :
    k ∈ alter m k f ↔ (f m[k]ᵈ?).isSome := by
    simp only [mem_iff_dGetElem?_eq_some, dGetElem?_alter_self]
    rw [Option.isSome_iff_exists]

  theorem mem_alter_ne {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k k' : α} {f : Option (β k) → Option (β k)} (hne : k ≠ k') :
    k' ∈ alter m k f ↔ k' ∈ m := by
    simp only [mem_iff_dGetElem?_eq_some, dGetElem?_alter_ne hne]

  theorem contains_alter_self {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)} :
    Contains.contains (alter m k f) k = (f m[k]ᵈ?).isSome := by
    rw [Bool.eq_iff_iff, LawfulContainsMem.contains_iff_mem]
    apply mem_alter_self

  theorem contains_alter_ne {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k k' : α} {f : Option (β k) → Option (β k)} (hne : k ≠ k') :
    Contains.contains (alter m k f) k' = Contains.contains m k' := by
    rw [Bool.eq_iff_iff]; simp only [LawfulContainsMem.contains_iff_mem]
    apply mem_alter_ne hne

  theorem size_alter_eq_add_one {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)}
    (h : ¬k ∈ m) (h' : (f m[k]ᵈ?).isSome) :
    Size.size (alter m k f) = Size.size m + 1 := by
    have ⟨a, ha⟩ := Option.isSome_iff_exists.mp h'
    rw [size_congr (alter_some ha), size_insert_not_mem h]

  theorem size_alter_eq_self_of_mem {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∈ m) (h' : (f m[k]ᵈ?).isSome) :
    Size.size (alter m k f) = Size.size m := by
    have ⟨a, ha⟩ := Option.isSome_iff_exists.mp h'
    rw [size_congr (alter_some ha), size_insert_mem h]

  theorem size_alter_eq_self_of_not_mem {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∉ m) (h' : (f m[k]ᵈ?).isNone) :
    Size.size (alter m k f) = Size.size m := by
    rw [Option.isNone_iff_eq_none] at h'
    rw [size_congr (alter_none h'), size_erase_not_mem h]

  theorem size_alter_eq_sub_one {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∈ m) (h' : (f m[k]ᵈ?).isNone) :
    Size.size (alter m k f) + 1 = Size.size m := by
    rw [Option.isNone_iff_eq_none] at h'
    rw [size_congr (alter_none h'), size_erase_mem h]

  theorem size_alter_le_size {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)} :
    Size.size (alter m k f) ≤ Size.size m + 1 := by
    cases h : f m[k]ᵈ?
    case none =>
      rw [size_congr (alter_none h)]
      have := size_erase_le (β:=β) (m:=m) (k:=k); omega
    case some =>
      rw [size_congr (alter_some h)]
      apply size_insert_le

  theorem size_le_size_alter {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)} :
    Size.size m ≤ Size.size (alter m k f) + 1:= by
    cases h : f m[k]ᵈ?
    case none =>
      rw [size_congr (alter_none h)]
      apply le_size_erase
    case some v =>
      rw [size_congr (alter_some h)]
      have := le_size_insert (β:=β) (m:=m) (k:=k) (v:=v); omega

  theorem isEmpty_alter {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)} :
    IsEmpty.isEmpty (alter m k f) = ((IsEmpty.isEmpty m || Size.size m == 1 && Contains.contains m k) && (f m[k]ᵈ?).isNone) := by
    cases h : f m[k]ᵈ?
    case none => simp [isEmpty_congr (alter_none h), isEmpty_erase]
    case some => simp [isEmpty_congr (alter_some h), isEmpty_insert_eq_false]

  theorem isEmpty_alter_eq_isEmpty_erase {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)} :
    IsEmpty.isEmpty (alter m k f) = (IsEmpty.isEmpty (erase (β:=β) m k) && (f m[k]ᵈ?).isNone) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none]
    cases h : f m[k]ᵈ?
    case none => simp [isEmpty_congr (alter_none h)]
    case some => rw [isEmpty_congr (alter_some h)]; simp [isEmpty_insert_eq_false]

  theorem dGetElem_alter_self {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} {f : Option (β k) → Option (β k)} {h : k ∈ alter m k f} :
    (alter m k f)[k]ᵈ'h = (f m[k]ᵈ?).get (mem_alter_self.mp h) := by
    rw [dGetElem_eq_iff_dGetElem?_eq_some, dGetElem?_alter_self, Option.some_get]

  theorem dGetElem_alter_ne {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k k' : α} {f : Option (β k) → Option (β k)} {h : k' ∈ alter m k f} (hne : k ≠ k') :
    (alter m k f)[k']ᵈ'h = m[k']ᵈ'((mem_alter_ne hne).mp h) := by
    rw [dGetElem_eq_iff_dGetElem?_eq_some, dGetElem?_alter_ne hne, dGetElem?_eq_some_dGetElem]

  theorem dGetElem!_alter_self {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k : α} [Inhabited (β k)] {f : Option (β k) → Option (β k)} :
    (alter m k f)[k]ᵈ! = (f m[k]ᵈ?).get! := by
    rw [dGetElem!_eq_get!_dGetElem?, dGetElem?_alter_self]

  theorem dGetElem!_alter_ne {γ α β} [inst : DMapAPI γ α β] [LawfulDMapAPI γ α β]
    {m : γ} {k k' : α} [Inhabited (β k')] {f : Option (β k) → Option (β k)} (hne : k ≠ k') :
    (alter m k f)[k']ᵈ! = m[k']ᵈ! := by
    simp [dGetElem!_eq_get!_dGetElem?, dGetElem?_alter_ne hne]

end LawfulDMapAPI

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : DMapAPI (DHashMap α β) α β where
  insertIfNew := DHashMap.insertIfNew
  containsThenInsert := DHashMap.containsThenInsert
  containsThenInsertIfNew := DHashMap.containsThenInsertIfNew
  getThenInsertIfNew? := DHashMap.getThenInsertIfNew?
  contains := DHashMap.contains
  isEmpty := DHashMap.isEmpty
  filter := DHashMap.filter
  modify := DHashMap.modify
  alter := DHashMap.alter

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : LawfulDMapAPI (DHashMap α β) α β where
  dGetElem?_insertIfNew_self := by
    intros; simp [dGetElem?, insertIfNew, DHashMap.get?_insertIfNew, *]
  dGetElem?_insertIfNew_ne := by
    intros m k a v h
    simp only [dGetElem?, insertIfNew, DHashMap.get?_insertIfNew, beq_iff_eq, dite_eq_right_iff]
    intro h'; cases h'.left; simp_all
  containsThenInsert_fst := DHashMap.containsThenInsert_fst
  containsThenInsert_snd := DHashMap.containsThenInsert_snd
  containsThenInsertIfNew_fst := DHashMap.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := DHashMap.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := DHashMap.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := DHashMap.getThenInsertIfNew?_snd
  contains_iff_mem := DHashMap.contains_iff_mem
  dGetElem?_filter := by
    intros m f k; simp [dGetElem?, filter, DHashMap.get?_filter]
  dGetElem?_modify_self := by
    intros m k f; simp [dGetElem?, DMapAPI.modify]
  dGetElem?_modify_ne := by
    intros m k k' f hk; simp [dGetElem?, DMapAPI.modify, DHashMap.get?_modify, hk]
  dGetElem?_alter_self := by
    intros m k f; simp [dGetElem?, alter]
  dGetElem?_alter_ne := by
    intros m k k' f hk; simp [dGetElem?, alter, DHashMap.get?_alter, hk]

instance {α β} [Ord α] [LawfulEqOrd α] : DMapAPI (DTreeMap α β) α β where
  insertIfNew := DTreeMap.insertIfNew
  containsThenInsert := DTreeMap.containsThenInsert
  containsThenInsertIfNew := DTreeMap.containsThenInsertIfNew
  getThenInsertIfNew? := DTreeMap.getThenInsertIfNew?
  contains := DTreeMap.contains
  isEmpty := DTreeMap.isEmpty
  filter := DTreeMap.filter
  modify := DTreeMap.modify
  alter := DTreeMap.alter

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulDMapAPI (DTreeMap α β) α β where
  dGetElem?_insertIfNew_self := by
    intros; simp [dGetElem?, insertIfNew, DTreeMap.get?_insertIfNew, *]
  dGetElem?_insertIfNew_ne := by
    intros m k a v h
    simp only [dGetElem?, insertIfNew, DTreeMap.get?_insertIfNew, compare_eq_iff_eq, dite_eq_right_iff]
    intro h'; cases h'.left; simp_all
  containsThenInsert_fst := DTreeMap.containsThenInsert_fst
  containsThenInsert_snd := DTreeMap.containsThenInsert_snd
  containsThenInsertIfNew_fst := DTreeMap.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := DTreeMap.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := DTreeMap.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := DTreeMap.getThenInsertIfNew?_snd
  contains_iff_mem := DTreeMap.contains_iff_mem
  dGetElem?_filter := by
    intros m f k; simp [dGetElem?, filter, DTreeMap.get?_filter]
  dGetElem?_modify_self := by
    intros m k f; simp [dGetElem?, DMapAPI.modify]
  dGetElem?_modify_ne := by
    intros m k k' f hk; simp [dGetElem?, DMapAPI.modify, DTreeMap.get?_modify, hk]
  dGetElem?_alter_self := by
    intros m k f; simp [dGetElem?, alter]
  dGetElem?_alter_ne := by
    intros m k k' f hk; simp [dGetElem?, alter, DTreeMap.get?_alter, hk]

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : DMapAPI (ExtDHashMap α β) α β where
  insertIfNew := ExtDHashMap.insertIfNew
  containsThenInsert := ExtDHashMap.containsThenInsert
  containsThenInsertIfNew := ExtDHashMap.containsThenInsertIfNew
  getThenInsertIfNew? := ExtDHashMap.getThenInsertIfNew?
  contains := ExtDHashMap.contains
  isEmpty := ExtDHashMap.isEmpty
  filter := ExtDHashMap.filter
  modify := ExtDHashMap.modify
  alter := ExtDHashMap.alter

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : LawfulDMapAPI (ExtDHashMap α β) α β where
  dGetElem?_insertIfNew_self := by
    intros; simp [dGetElem?, insertIfNew, ExtDHashMap.get?_insertIfNew, *]
  dGetElem?_insertIfNew_ne := by
    intros m k a v h
    simp only [dGetElem?, insertIfNew, ExtDHashMap.get?_insertIfNew, beq_iff_eq, dite_eq_right_iff]
    intro h'; cases h'.left; simp_all
  containsThenInsert_fst := ExtDHashMap.containsThenInsert_fst
  containsThenInsert_snd := ExtDHashMap.containsThenInsert_snd
  containsThenInsertIfNew_fst := ExtDHashMap.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := ExtDHashMap.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := ExtDHashMap.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := ExtDHashMap.getThenInsertIfNew?_snd
  contains_iff_mem := ExtDHashMap.contains_iff_mem
  dGetElem?_filter := by
    intros m f k; simp [dGetElem?, filter, ExtDHashMap.get?_filter]
  dGetElem?_modify_self := by
    intros m k f; simp [dGetElem?, DMapAPI.modify]
  dGetElem?_modify_ne := by
    intros m k k' f hk; simp [dGetElem?, DMapAPI.modify, ExtDHashMap.get?_modify, hk]
  dGetElem?_alter_self := by
    intros m k f; simp [dGetElem?, alter]
  dGetElem?_alter_ne := by
    intros m k k' f hk; simp [dGetElem?, alter, ExtDHashMap.get?_alter, hk]

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : DMapAPI (ExtDTreeMap α β) α β where
  insertIfNew := ExtDTreeMap.insertIfNew
  containsThenInsert := ExtDTreeMap.containsThenInsert
  containsThenInsertIfNew := ExtDTreeMap.containsThenInsertIfNew
  getThenInsertIfNew? := ExtDTreeMap.getThenInsertIfNew?
  contains := ExtDTreeMap.contains
  isEmpty := ExtDTreeMap.isEmpty
  filter := ExtDTreeMap.filter
  modify := ExtDTreeMap.modify
  alter := ExtDTreeMap.alter

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulDMapAPI (ExtDTreeMap α β) α β where
  dGetElem?_insertIfNew_self := by
    intros; simp [dGetElem?, insertIfNew, ExtDTreeMap.get?_insertIfNew, *]
  dGetElem?_insertIfNew_ne := by
    intros m k a v h
    simp only [dGetElem?, insertIfNew, ExtDTreeMap.get?_insertIfNew, compare_eq_iff_eq, dite_eq_right_iff]
    intro h'; cases h'.left; simp_all
  containsThenInsert_fst := ExtDTreeMap.containsThenInsert_fst
  containsThenInsert_snd := ExtDTreeMap.containsThenInsert_snd
  containsThenInsertIfNew_fst := ExtDTreeMap.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := ExtDTreeMap.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := ExtDTreeMap.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := ExtDTreeMap.getThenInsertIfNew?_snd
  contains_iff_mem := ExtDTreeMap.contains_iff_mem
  dGetElem?_filter := by
    intros m f k; simp [dGetElem?, filter, ExtDTreeMap.get?_filter]
  dGetElem?_modify_self := by
    intros m k f; simp [dGetElem?, DMapAPI.modify]
  dGetElem?_modify_ne := by
    intros m k k' f hk; simp [dGetElem?, DMapAPI.modify, ExtDTreeMap.get?_modify, hk]
  dGetElem?_alter_self := by
    intros m k f; simp [dGetElem?, alter]
  dGetElem?_alter_ne := by
    intros m k k' f hk; simp [dGetElem?, alter, ExtDTreeMap.get?_alter, hk]

end DMapAPI


section MapAPI

class MapAPI (γ : Type u) (α : Type v) (β : Type w) extends
  MapLike γ α β, IsEmpty γ, Contains γ α where
  insertIfNew : γ → α → β → γ
  containsThenInsert : γ → α → β → Bool × γ
  containsThenInsertIfNew : γ → α → β → Bool × γ
  getThenInsertIfNew? : γ → α → β → Option β × γ
  filter : (α → β → Bool) → γ → γ
  modify : γ → α → (β → β) → γ
  alter : γ → α → (Option β → Option β) → γ

def MapAPI_of_DMapAPI {γ α β} (inst : DMapAPI γ α (fun _ => β)) : MapAPI γ α β where
  toMapLike := MapLike_of_DMapLike inst.toDMapLike
  insertIfNew := inst.insertIfNew
  containsThenInsert := inst.containsThenInsert
  containsThenInsertIfNew := inst.containsThenInsertIfNew
  getThenInsertIfNew? := inst.getThenInsertIfNew?
  filter := inst.filter
  modify := inst.modify
  alter := inst.alter

def DMapAPI_of_MapAPI {γ α β} (inst : MapAPI γ α β) : DMapAPI γ α (fun _ => β) where
  toDMapLike := DMapLike_of_MapLike inst.toMapLike
  insertIfNew := inst.insertIfNew
  containsThenInsert := inst.containsThenInsert
  containsThenInsertIfNew := inst.containsThenInsertIfNew
  getThenInsertIfNew? := inst.getThenInsertIfNew?
  filter := inst.filter
  modify := inst.modify
  alter := inst.alter

def DMapAPI_MapAPI_inv {γ α β} {inst : DMapAPI γ α (fun _ => β)} :
  DMapAPI_of_MapAPI (MapAPI_of_DMapAPI inst) = inst := rfl

def MapAPI_DMapAPI_inv {γ α β} {inst : MapAPI γ α β} :
  MapAPI_of_DMapAPI (DMapAPI_of_MapAPI inst) = inst := rfl

open MapAPI MapLike

class LawfulMapAPI (γ : Type u) (α : Type v) (β : Type w) [inst : MapAPI γ α β]
  extends LawfulMapLike γ α β, LawfulIsEmptySize γ, LawfulContainsMem γ α where
  getElem?_insertIfNew_self {m : γ} {k : α} {v : β} (h : k ∉ m) :
    (insertIfNew m k v)[k]? = .some v
  getElem?_insertIfNew_ne {m : γ} {k a : α} {v : β} (h : k ≠ a ∨ k ∈ m) :
    (insertIfNew m k v)[a]? = m[a]?
  containsThenInsert_fst {m : γ} {k : α} {v : β} : (containsThenInsert m k v).fst = Contains.contains m k
  containsThenInsert_snd {m : γ} {k : α} {v : β} : (containsThenInsert m k v).snd = insert m k v
  containsThenInsertIfNew_fst {m : γ} {k : α} {v : β} : (containsThenInsertIfNew m k v).fst = Contains.contains m k
  containsThenInsertIfNew_snd {m : γ} {k : α} {v : β} : (containsThenInsertIfNew m k v).snd = insertIfNew m k v
  getThenInsertIfNew?_fst {m : γ} {k : α} {v : β} : (getThenInsertIfNew? m k v).fst = m[k]?
  getThenInsertIfNew?_snd {m : γ} {k : α} {v : β} : (getThenInsertIfNew? m k v).snd = insertIfNew m k v
  getElem?_filter {m : γ} {f : α → β → Bool} {k : α} : (filter f m)[k]? = Option.filter (f k) m[k]?
  getElem?_modify_self {m : γ} {k : α} {f : β → β} :
    (modify m k f)[k]? = Option.map f m[k]?
  getElem?_modify_ne {m : γ} {k k' : α} {f : β → β} (h : k ≠ k') :
    (modify m k f)[k']? = m[k']?
  getElem?_alter_self {m : γ} {k : α} {f : Option β → Option β} :
    (alter m k f)[k]? = f m[k]?
  getElem?_alter_ne {m : γ} {k k' : α} {f : Option β → Option β} (h : k ≠ k') :
    (alter m k f)[k']? = m[k']?

def LawfulMapAPI_of_LawfulDMapAPI {γ α β} [inst : MapAPI γ α β]
  [instL : LawfulDMapAPI (inst:=DMapAPI_of_MapAPI inst) γ α (fun _ => β)] :
  LawfulMapAPI γ α β where
  toLawfulMapLike := LawfulMapLike_of_LawfulDMapLike (inst:=inst.toMapLike) (instL:=instL.toLawfulDMapLike)
  isEmpty_iff_size_eq_zero := instL.isEmpty_iff_size_eq_zero
  contains_iff_mem := instL.contains_iff_mem
  getElem?_insertIfNew_self := instL.dGetElem?_insertIfNew_self
  getElem?_insertIfNew_ne := instL.dGetElem?_insertIfNew_ne
  containsThenInsert_fst := instL.containsThenInsert_fst
  containsThenInsert_snd := instL.containsThenInsert_snd
  containsThenInsertIfNew_fst := instL.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := instL.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := instL.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := instL.getThenInsertIfNew?_snd
  getElem?_filter := instL.dGetElem?_filter
  getElem?_modify_self := instL.dGetElem?_modify_self
  getElem?_modify_ne := instL.dGetElem?_modify_ne
  getElem?_alter_self := instL.dGetElem?_alter_self
  getElem?_alter_ne := instL.dGetElem?_alter_ne

theorem LawfulMapAPI_of_LawfulDMapAPI' {γ α β} [inst : DMapAPI γ α (fun _ => β)]
  [instL : LawfulDMapAPI γ α (fun _ => β)] :
  LawfulMapAPI (inst:=MapAPI_of_DMapAPI inst) γ α β :=
  LawfulMapAPI_of_LawfulDMapAPI (inst:=MapAPI_of_DMapAPI inst)

def LawfulDMapAPI_of_LawfulMapAPI {γ α β} [inst : DMapAPI γ α (fun _ => β)]
  [instL : LawfulMapAPI (inst:=MapAPI_of_DMapAPI inst) γ α β] :
  LawfulDMapAPI γ α (fun _ => β) where
  toLawfulDMapLike := LawfulDMapLike_of_LawfulMapLike (inst:=inst.toDMapLike) (instL:=instL.toLawfulMapLike)
  isEmpty_iff_size_eq_zero := instL.isEmpty_iff_size_eq_zero
  contains_iff_mem := instL.contains_iff_mem
  dGetElem?_insertIfNew_self := instL.getElem?_insertIfNew_self
  dGetElem?_insertIfNew_ne := instL.getElem?_insertIfNew_ne
  containsThenInsert_fst := instL.containsThenInsert_fst
  containsThenInsert_snd := instL.containsThenInsert_snd
  containsThenInsertIfNew_fst := instL.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := instL.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := instL.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := instL.getThenInsertIfNew?_snd
  dGetElem?_filter := instL.getElem?_filter
  dGetElem?_modify_self := instL.getElem?_modify_self
  dGetElem?_modify_ne := instL.getElem?_modify_ne
  dGetElem?_alter_self := instL.getElem?_alter_self
  dGetElem?_alter_ne := instL.getElem?_alter_ne

local instance LawfulDMapAPI_of_LawfulMapAPI' {γ α β} [inst : MapAPI γ α β]
  [instL : LawfulMapAPI γ α β] :
  LawfulDMapAPI (inst:=DMapAPI_of_MapAPI inst) γ α (fun _ => β) :=
  LawfulDMapAPI_of_LawfulMapAPI (inst:=DMapAPI_of_MapAPI inst)

namespace LawfulMapAPI

  open LawfulMapLike

  theorem isEmpty_congr {γ₁ γ₂ α β} [inst₁ : MapAPI γ₁ α β] [inst₂ : MapAPI γ₂ α β]
    [LawfulMapAPI γ₁ α β] [LawfulMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (α:=α) (β:=β) m₁ m₂) : IsEmpty.isEmpty m₁ = IsEmpty.isEmpty m₂ :=
    LawfulDMapAPI.isEmpty_congr (inst₁:=DMapAPI_of_MapAPI inst₁) (inst₂:=DMapAPI_of_MapAPI inst₂) hequiv

  theorem isEmpty_erase {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} : IsEmpty.isEmpty (erase (β:=β) m k) = (IsEmpty.isEmpty m || (Size.size m == 1 && Contains.contains m k)) :=
    LawfulDMapAPI.isEmpty_erase (inst:=DMapAPI_of_MapAPI inst)

  theorem isEmpty_insert_eq_false {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {v : β} : IsEmpty.isEmpty (insert m k v) = false :=
    LawfulDMapAPI.isEmpty_insert_eq_false (inst:=DMapAPI_of_MapAPI inst)

  theorem contains_congr {γ₁ γ₂ α β} [inst₁ : MapAPI γ₁ α β] [inst₂ : MapAPI γ₂ α β]
    [LawfulMapAPI γ₁ α β] [LawfulMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (k : α) : Contains.contains m₁ k = Contains.contains m₂ k :=
    LawfulDMapAPI.contains_congr (inst₁:=DMapAPI_of_MapAPI inst₁) (inst₂:=DMapAPI_of_MapAPI inst₂) hequiv _

  theorem not_contains_iff_not_mem {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} : Contains.contains m k = false ↔ k ∉ m :=
    LawfulDMapAPI.not_contains_iff_not_mem (inst:=DMapAPI_of_MapAPI inst)

  theorem isEmpty_iff_forall_not_mem {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} : IsEmpty.isEmpty m ↔ ∀ (x : α), x ∉ m :=
    LawfulDMapAPI.isEmpty_iff_forall_not_mem (inst:=DMapAPI_of_MapAPI inst)

  theorem insertIfNew_equiv_of_mem {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {v : β} (h : k ∈ m) : equiv (α:=α) (β:=β) (insertIfNew m k v) m :=
    LawfulDMapAPI.insertIfNew_equiv_of_mem (inst:=DMapAPI_of_MapAPI inst) h

  theorem insertIfNew_equiv_of_not_mem {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {v : β} (h : k ∉ m) : equiv (α:=α) (β:=β) (insertIfNew m k v) (insert m k v) :=
    LawfulDMapAPI.insertIfNew_equiv_of_not_mem (inst:=DMapAPI_of_MapAPI inst) h

  theorem insertIfNew_equiv {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {v : β} : equiv (α:=α) (β:=β) (insertIfNew m k v) (if Contains.contains m k then m else insert m k v) :=
    LawfulDMapAPI.insertIfNew_equiv (inst:=DMapAPI_of_MapAPI inst)

  theorem insertIfNew_congr {γ₁ γ₂ α β} [inst₁ : MapAPI γ₁ α β] [inst₂ : MapAPI γ₂ α β]
    [LawfulMapAPI γ₁ α β] [LawfulMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (k : α) (v : β) :
    equiv (α:=α) (β:=β) (insertIfNew m₁ k v) (insertIfNew m₂ k v) :=
    LawfulDMapAPI.insertIfNew_congr (inst₁:=DMapAPI_of_MapAPI inst₁) (inst₂:=DMapAPI_of_MapAPI inst₂) hequiv _ _

  theorem size_insertIfNew_mem {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {v : β} (h : k ∈ m) : Size.size (insertIfNew m k v) = Size.size m :=
    LawfulDMapAPI.size_insertIfNew_mem (inst:=DMapAPI_of_MapAPI inst) h

  theorem size_insertIfNew_not_mem {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {v : β} (h : k ∉ m) : Size.size (insertIfNew m k v) = Size.size m + 1 :=
    LawfulDMapAPI.size_insertIfNew_not_mem (inst:=DMapAPI_of_MapAPI inst) h

  theorem size_insertIfNew {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} [Decidable (k ∈ m)] {v : β} : Size.size (insertIfNew m k v) = if k ∈ m then Size.size m else Size.size m + 1 :=
    LawfulDMapAPI.size_insertIfNew (inst:=DMapAPI_of_MapAPI inst)

  theorem mem_insertIfNew' {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k a : α} {v : β} : a ∈ MapAPI.insertIfNew m k v ↔ k = a ∨ a ∈ m :=
    LawfulDMapAPI.mem_insertIfNew' (inst:=DMapAPI_of_MapAPI inst)

  theorem mem_insertIfNew {γ α β} [BEq α] [LawfulBEq α] [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k a : α} {v : β} : a ∈ MapAPI.insertIfNew m k v ↔ k == a ∨ a ∈ m :=
    LawfulDMapAPI.mem_insertIfNew (inst:=DMapAPI_of_MapAPI inst)

  theorem mem_of_mem_insertIfNew' {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β] {m : γ} {k a : α} {v : β} :
    a ∈ insertIfNew m k v → k ≠ a ∨ k ∈ m → a ∈ m :=
    LawfulDMapAPI.mem_of_mem_insertIfNew' (inst:=DMapAPI_of_MapAPI inst)

  theorem contains_insertIfNew {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k a : α} {v : β} : Contains.contains (MapAPI.insertIfNew m k v) a ↔ k = a ∨ a ∈ m :=
    LawfulDMapAPI.contains_insertIfNew (inst:=DMapAPI_of_MapAPI inst)

  theorem getElem_insertIfNew_ne {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k a : α} {v : β} {h₁ : a ∈ insertIfNew m k v} {h₂ : k ≠ a ∨ k ∈ m} :
    (insertIfNew m k v)[a]'h₁ = m[a]'(mem_of_mem_insertIfNew' h₁ h₂) :=
    LawfulDMapAPI.dGetElem_insertIfNew_ne (inst:=DMapAPI_of_MapAPI inst) (h₁:=h₁) (h₂:=h₂)

  theorem getElem_insertIfNew_ne' {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k a : α} {v : β} {h : a ∈ m} :
    (insertIfNew m k v)[a]'(mem_insertIfNew'.mpr (Or.inr h)) = m[a]'h :=
    LawfulDMapAPI.dGetElem_insertIfNew_ne' (inst:=DMapAPI_of_MapAPI inst)

  theorem getElem_insertIfNew_self {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k: α} {v : β} {h : k ∉ m} :
    (insertIfNew m k v)[k]'(by simp [mem_insertIfNew']) = v :=
    LawfulDMapAPI.dGetElem_insertIfNew_self (inst:=DMapAPI_of_MapAPI inst) (h:=h)

  theorem getElem!_insertIfNew_ne {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k a : α} [Inhabited β] {v : β} {h : k ≠ a ∨ k ∈ m} :
    (insertIfNew m k v)[a]! = m[a]! :=
    LawfulDMapAPI.dGetElem!_insertIfNew_ne (inst:=DMapAPI_of_MapAPI inst) (h:=h)

  theorem getElem!_insertIfNew_self {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} [Inhabited β] {v : β} {h : k ∉ m} :
    (insertIfNew m k v)[k]! = v :=
    LawfulDMapAPI.dGetElem!_insertIfNew_self (inst:=DMapAPI_of_MapAPI inst) (h:=h)

  theorem filter_congr {γ₁ γ₂ α β} [inst₁ : MapAPI γ₁ α β] [inst₂ : MapAPI γ₂ α β]
    [LawfulMapAPI γ₁ α β] [LawfulMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (f : α → β → Bool) :
    equiv (α:=α) (β:=β) (filter f m₁) (filter f m₂) :=
    LawfulDMapAPI.filter_congr (inst₁:=DMapAPI_of_MapAPI inst₁) (inst₂:=DMapAPI_of_MapAPI inst₂) hequiv _

  theorem mem_filter {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} {k : α} :
    k ∈ filter f m ↔ ∃ h, f k (m[k]'h) = true :=
    LawfulDMapAPI.mem_filter (inst:=DMapAPI_of_MapAPI inst)

  theorem mem_of_mem_filter {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} {k : α} (h : k ∈ filter f m) : k ∈ m :=
    LawfulDMapAPI.mem_of_mem_filter (inst:=DMapAPI_of_MapAPI inst) h

  theorem filter_subset {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} : subset (α:=α) (β:=β) (filter f m) m :=
    LawfulDMapAPI.filter_subset (inst:=DMapAPI_of_MapAPI inst)

  theorem filter_keySubset {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} : keySubset (α:=α) (β:=β) (filter f m) m :=
    fun _ => mem_of_mem_filter

  theorem contains_filter {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} {k : α} :
    Contains.contains (filter f m) k ↔ Option.any (f k) m[k]? :=
    LawfulDMapAPI.contains_filter (inst:=DMapAPI_of_MapAPI inst)

  theorem contains_of_contains_filter {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} {k : α} (h : Contains.contains (filter f m) k) : Contains.contains m k :=
    LawfulDMapAPI.contains_of_contains_filter (inst:=DMapAPI_of_MapAPI inst) h

  theorem getElem_filter {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} {k : α} {h' : k ∈ filter f m} :
    (filter f m)[k]'h' = m[k]'(mem_of_mem_filter h') :=
    LawfulDMapAPI.dGetElem_filter (inst:=DMapAPI_of_MapAPI inst)

  theorem getElem!_filter {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} {k : α} [Inhabited β] :
    (filter f m)[k]! = (Option.filter (f k) m[k]?).get! :=
    LawfulDMapAPI.dGetElem!_filter (inst:=DMapAPI_of_MapAPI inst)

  theorem isEmpty_filter_iff {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} :
    IsEmpty.isEmpty (filter f m) ↔ ∀ (k : α) (h : k ∈ m), f k (m[k]'h) = false :=
    LawfulDMapAPI.isEmpty_filter_iff (inst:=DMapAPI_of_MapAPI inst)

  theorem isEmpty_filter_eq_false_iff {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} :
    IsEmpty.isEmpty (filter f m) = false ↔ ∃ (k : α) (h : k ∈ m), f k (m[k]'h) :=
    LawfulDMapAPI.isEmpty_filter_eq_false_iff (inst:=DMapAPI_of_MapAPI inst)

  theorem size_filter_le_size {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} :
    Size.size (filter f m) ≤ Size.size m :=
    LawfulDMapAPI.size_filter_le_size (inst:=DMapAPI_of_MapAPI inst)

  theorem size_filter_eq_size_iff {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {f : α → β → Bool} :
    Size.size (filter f m) = Size.size m ↔ ∀ (k : α) (h : k ∈ m), f k (m[k]'h) :=
    LawfulDMapAPI.size_filter_eq_size_iff (inst:=DMapAPI_of_MapAPI inst)

  theorem modify_congr {γ₁ γ₂ α β} [inst₁ : MapAPI γ₁ α β] [inst₂ : MapAPI γ₂ α β]
    [LawfulMapAPI γ₁ α β] [LawfulMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (k : α) (f : β → β) :
    equiv (α:=α) (β:=β) (modify m₁ k f) (modify m₂ k f) :=
    LawfulDMapAPI.modify_congr (inst₁:=DMapAPI_of_MapAPI inst₁) (inst₂:=DMapAPI_of_MapAPI inst₂) hequiv _ _

  theorem mem_modify {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k k' : α} {f : β → β} : k' ∈ modify m k f ↔ k' ∈ m :=
    LawfulDMapAPI.mem_modify (inst:=DMapAPI_of_MapAPI inst)

  theorem contains_modify {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k k' : α} {f : β → β} : Contains.contains (modify m k f) k' = Contains.contains m k' :=
    LawfulDMapAPI.contains_modify (inst:=DMapAPI_of_MapAPI inst)

  theorem modify_keyEquiv {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : β → β} : keyEquiv (α:=α) (β:=β) (modify m k f) m :=
    fun _ => mem_modify

  theorem size_modify {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : β → β} : Size.size (modify m k f) = Size.size m :=
    LawfulDMapAPI.size_modify (inst:=DMapAPI_of_MapAPI inst)

  theorem isEmpty_modify {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : β → β} : IsEmpty.isEmpty (modify m k f) = IsEmpty.isEmpty m :=
    LawfulDMapAPI.isEmpty_modify (inst:=DMapAPI_of_MapAPI inst)

  theorem getElem_modify_self {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : β → β} (h : k ∈ modify m k f) :
    (MapAPI.modify m k f)[k]'h = f (m[k]'(mem_modify.mp h)) :=
    LawfulDMapAPI.dGetElem_modify_self (inst:=DMapAPI_of_MapAPI inst) h

  theorem getElem_modify_self' {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : β → β} (h : k ∈ m) :
    (MapAPI.modify m k f)[k]'(mem_modify.mpr h) = f (m[k]'h) :=
    LawfulDMapAPI.dGetElem_modify_self' (inst:=DMapAPI_of_MapAPI inst) h

  theorem getElem_modify_ne {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k a : α} {f : β → β} (h : a ∈ modify m k f) (hne : k ≠ a) :
    (MapAPI.modify m k f)[a]'h = m[a]'(mem_modify.mp h) :=
    LawfulDMapAPI.dGetElem_modify_ne (inst:=DMapAPI_of_MapAPI inst) h hne

  theorem getElem_modify_ne' {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k a : α} {f : β → β} (h : a ∈ m) (hne : k ≠ a) :
    (MapAPI.modify m k f)[a]'(mem_modify.mpr h) = m[a]'h :=
    getElem_modify_ne (mem_modify.mpr h) hne

  theorem getElem!_modify_self {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} [Inhabited β] {f : β → β} : (modify m k f)[k]! = (Option.map f m[k]?).get! :=
    LawfulDMapAPI.dGetElem!_modify_self (inst:=DMapAPI_of_MapAPI inst)

  theorem getElem!_modify_ne {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k k' : α} [Inhabited β] {f : β → β} (h : k ≠ k'):
    (modify m k f)[k']! = m[k']! :=
    LawfulDMapAPI.dGetElem!_modify_ne (inst:=DMapAPI_of_MapAPI inst) h

  theorem alter_congr {γ₁ γ₂ α β} [inst₁ : MapAPI γ₁ α β] [inst₂ : MapAPI γ₂ α β]
    [LawfulMapAPI γ₁ α β] [LawfulMapAPI γ₂ α β] {m₁ : γ₁} {m₂ : γ₂}
    (hequiv : equiv (α:=α) (β:=β) m₁ m₂) (k : α) (f : Option β → Option β) :
    equiv (α:=α) (β:=β) (alter m₁ k f) (alter m₂ k f) :=
    LawfulDMapAPI.alter_congr (inst₁:=DMapAPI_of_MapAPI inst₁) (inst₂:=DMapAPI_of_MapAPI inst₂) hequiv _ _

  theorem alter_none {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β}
    (hnone : f m[k]? = .none) : equiv (α:=α) (β:=β) (alter m k f) (erase (β:=β) m k) :=
    LawfulDMapAPI.alter_none (inst:=DMapAPI_of_MapAPI inst) hnone

  theorem alter_some {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {v : β} {f : Option β → Option β}
    (hsome : f m[k]? = .some v) : equiv (α:=α) (β:=β) (alter m k f) (insert m k v) :=
    LawfulDMapAPI.alter_some (inst:=DMapAPI_of_MapAPI inst) hsome

  theorem mem_alter_self {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β} :
    k ∈ alter m k f ↔ (f m[k]?).isSome :=
    LawfulDMapAPI.mem_alter_self (inst:=DMapAPI_of_MapAPI inst)

  theorem mem_alter_ne {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k k' : α} {f : Option β → Option β} (hne : k ≠ k') :
    k' ∈ alter m k f ↔ k' ∈ m :=
    LawfulDMapAPI.mem_alter_ne (inst:=DMapAPI_of_MapAPI inst) hne

  theorem contains_alter_self {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β} :
    Contains.contains (alter m k f) k = (f m[k]?).isSome :=
    LawfulDMapAPI.contains_alter_self (inst:=DMapAPI_of_MapAPI inst)

  theorem contains_alter_ne {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k k' : α} {f : Option β → Option β} (hne : k ≠ k') :
    Contains.contains (alter m k f) k' = Contains.contains m k' :=
    LawfulDMapAPI.contains_alter_ne (inst:=DMapAPI_of_MapAPI inst) hne

  theorem size_alter_eq_add_one {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β}
    (h : ¬k ∈ m) (h' : (f m[k]?).isSome) :
    Size.size (alter m k f) = Size.size m + 1 :=
    LawfulDMapAPI.size_alter_eq_add_one (inst:=DMapAPI_of_MapAPI inst) h h'

  theorem size_alter_eq_self_of_mem {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f m[k]?).isSome) :
    Size.size (alter m k f) = Size.size m :=
    LawfulDMapAPI.size_alter_eq_self_of_mem (inst:=DMapAPI_of_MapAPI inst) h h'

  theorem size_alter_eq_self_of_not_mem {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f m[k]?).isNone) :
    Size.size (alter m k f) = Size.size m :=
    LawfulDMapAPI.size_alter_eq_self_of_not_mem (inst:=DMapAPI_of_MapAPI inst) h h'

  theorem size_alter_eq_sub_one {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f m[k]?).isNone) :
    Size.size (alter m k f) + 1 = Size.size m :=
    LawfulDMapAPI.size_alter_eq_sub_one (inst:=DMapAPI_of_MapAPI inst) h h'

  theorem size_alter_le_size {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β} :
    Size.size (alter m k f) ≤ Size.size m + 1 :=
    LawfulDMapAPI.size_alter_le_size (inst:=DMapAPI_of_MapAPI inst)

  theorem size_le_size_alter {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β} :
    Size.size m ≤ Size.size (alter m k f) + 1:=
    LawfulDMapAPI.size_le_size_alter (inst:=DMapAPI_of_MapAPI inst)

  theorem isEmpty_alter {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β} :
    IsEmpty.isEmpty (alter m k f) = ((IsEmpty.isEmpty m || Size.size m == 1 && Contains.contains m k) && (f m[k]?).isNone) :=
    LawfulDMapAPI.isEmpty_alter (inst:=DMapAPI_of_MapAPI inst)

  theorem isEmpty_alter_eq_isEmpty_erase {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β} :
    IsEmpty.isEmpty (alter m k f) = (IsEmpty.isEmpty (erase (β:=β) m k) && (f m[k]?).isNone) :=
    LawfulDMapAPI.isEmpty_alter_eq_isEmpty_erase (inst:=DMapAPI_of_MapAPI inst)

  theorem getElem_alter_self {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} {f : Option β → Option β} {h : k ∈ alter m k f} :
    (alter m k f)[k]'h = (f m[k]?).get (mem_alter_self.mp h) :=
    LawfulDMapAPI.dGetElem_alter_self (inst:=DMapAPI_of_MapAPI inst) (h:=h)

  theorem getElem_alter_ne {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k k' : α} {f : Option β → Option β} {h : k' ∈ alter m k f} (hne : k ≠ k') :
    (alter m k f)[k']'h = m[k']'((mem_alter_ne hne).mp h) :=
    LawfulDMapAPI.dGetElem_alter_ne (inst:=DMapAPI_of_MapAPI inst) hne

  theorem getElem!_alter_self {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k : α} [Inhabited β] {f : Option β → Option β} :
    (alter m k f)[k]! = (f m[k]?).get! :=
    LawfulDMapAPI.dGetElem!_alter_self (inst:=DMapAPI_of_MapAPI inst)

  theorem getElem!_alter_ne {γ α β} [inst : MapAPI γ α β] [LawfulMapAPI γ α β]
    {m : γ} {k k' : α} [Inhabited β] {f : Option β → Option β} (hne : k ≠ k') :
    (alter m k f)[k']! = m[k']! :=
    LawfulDMapAPI.dGetElem!_alter_ne (inst:=DMapAPI_of_MapAPI inst) hne

end LawfulMapAPI

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : MapAPI (HashMap α β) α β where
  insertIfNew := HashMap.insertIfNew
  containsThenInsert := HashMap.containsThenInsert
  containsThenInsertIfNew := HashMap.containsThenInsertIfNew
  getThenInsertIfNew? := HashMap.getThenInsertIfNew?
  contains := HashMap.contains
  isEmpty := HashMap.isEmpty
  filter := HashMap.filter
  modify := HashMap.modify
  alter := HashMap.alter

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : LawfulMapAPI (HashMap α β) α β where
  getElem?_insertIfNew_self := by
    intros
    simp only [insertIfNew, HashMap.getElem?_insertIfNew]
    simp [*]
  getElem?_insertIfNew_ne := by
    intros m k a v h
    simp only [insertIfNew, HashMap.getElem?_insertIfNew, beq_iff_eq]
    grind
  containsThenInsert_fst := HashMap.containsThenInsert_fst
  containsThenInsert_snd := HashMap.containsThenInsert_snd
  containsThenInsertIfNew_fst := HashMap.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := HashMap.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := HashMap.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := HashMap.getThenInsertIfNew?_snd
  contains_iff_mem := HashMap.contains_iff_mem
  getElem?_filter := by
    intros m f k; simp [filter, HashMap.getElem?_filter]
  getElem?_modify_self := by
    intros m k f; simp [MapAPI.modify]
  getElem?_modify_ne := by
    intros m k k' f hk; simp [MapAPI.modify, HashMap.getElem?_modify, hk]
  getElem?_alter_self := by
    intros m k f; simp [alter]
  getElem?_alter_ne := by
    intros m k k' f hk; simp [alter, HashMap.getElem?_alter, hk]

instance {α β} [Ord α] [LawfulEqOrd α] : MapAPI (TreeMap α β) α β where
  insertIfNew := TreeMap.insertIfNew
  containsThenInsert := TreeMap.containsThenInsert
  containsThenInsertIfNew := TreeMap.containsThenInsertIfNew
  getThenInsertIfNew? := TreeMap.getThenInsertIfNew?
  contains := TreeMap.contains
  isEmpty := TreeMap.isEmpty
  filter := TreeMap.filter
  modify := TreeMap.modify
  alter := TreeMap.alter

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulMapAPI (TreeMap α β) α β where
  getElem?_insertIfNew_self := by
    intros
    simp only [insertIfNew]
    rw [TreeMap.getElem?_insertIfNew]
    grind
  getElem?_insertIfNew_ne := by
    intros m k a v h
    simp only [insertIfNew, TreeMap.getElem?_insertIfNew, compare_eq_iff_eq]
    grind
  containsThenInsert_fst := TreeMap.containsThenInsert_fst
  containsThenInsert_snd := TreeMap.containsThenInsert_snd
  containsThenInsertIfNew_fst := TreeMap.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := TreeMap.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := TreeMap.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := TreeMap.getThenInsertIfNew?_snd
  contains_iff_mem := TreeMap.contains_iff_mem
  getElem?_filter := by
    intros m f k; simp [filter, TreeMap.getElem?_filter]
  getElem?_modify_self := by
    intros m k f; simp [MapAPI.modify]
  getElem?_modify_ne := by
    intros m k k' f hk; simp [MapAPI.modify, TreeMap.getElem?_modify, hk]
  getElem?_alter_self := by
    intros m k f; simp [alter]
  getElem?_alter_ne := by
    intros m k k' f hk; simp [alter, TreeMap.getElem?_alter, hk]

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] : MapAPI (ExtHashMap α β) α β where
  insertIfNew := ExtHashMap.insertIfNew
  containsThenInsert := ExtHashMap.containsThenInsert
  containsThenInsertIfNew := ExtHashMap.containsThenInsertIfNew
  getThenInsertIfNew? := ExtHashMap.getThenInsertIfNew?
  contains := ExtHashMap.contains
  isEmpty := ExtHashMap.isEmpty
  filter := ExtHashMap.filter
  modify := ExtHashMap.modify
  alter := ExtHashMap.alter

instance {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : LawfulMapAPI (ExtHashMap α β) α β where
  getElem?_insertIfNew_self := by
    intros
    simp only [insertIfNew]
    rw [ExtHashMap.getElem?_insertIfNew]
    grind
  getElem?_insertIfNew_ne := by
    intros m k a v h
    simp only [insertIfNew, ExtHashMap.getElem?_insertIfNew, beq_iff_eq]
    grind
  containsThenInsert_fst := ExtHashMap.containsThenInsert_fst
  containsThenInsert_snd := ExtHashMap.containsThenInsert_snd
  containsThenInsertIfNew_fst := ExtHashMap.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := ExtHashMap.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := ExtHashMap.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := ExtHashMap.getThenInsertIfNew?_snd
  contains_iff_mem := ExtHashMap.contains_iff_mem
  getElem?_filter := by
    intros m f k; simp [filter]
  getElem?_modify_self := by
    intros m k f; simp [MapAPI.modify]
  getElem?_modify_ne := by
    intros m k k' f hk; simp [MapAPI.modify, ExtHashMap.getElem?_modify, hk]
  getElem?_alter_self := by
    intros m k f; simp [alter]
  getElem?_alter_ne := by
    intros m k k' f hk; simp [alter, ExtHashMap.getElem?_alter, hk]

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : MapAPI (ExtTreeMap α β) α β where
  insertIfNew := ExtTreeMap.insertIfNew
  containsThenInsert := ExtTreeMap.containsThenInsert
  containsThenInsertIfNew := ExtTreeMap.containsThenInsertIfNew
  getThenInsertIfNew? := ExtTreeMap.getThenInsertIfNew?
  contains := ExtTreeMap.contains
  isEmpty := ExtTreeMap.isEmpty
  filter := ExtTreeMap.filter
  modify := ExtTreeMap.modify
  alter := ExtTreeMap.alter

instance {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulMapAPI (ExtTreeMap α β) α β where
  getElem?_insertIfNew_self := by
    intros
    simp only [insertIfNew]
    rw [ExtTreeMap.getElem?_insertIfNew]
    grind
  getElem?_insertIfNew_ne := by
    intros m k a v h
    simp only [insertIfNew, ExtTreeMap.getElem?_insertIfNew, compare_eq_iff_eq]
    grind
  containsThenInsert_fst := ExtTreeMap.containsThenInsert_fst
  containsThenInsert_snd := ExtTreeMap.containsThenInsert_snd
  containsThenInsertIfNew_fst := ExtTreeMap.containsThenInsertIfNew_fst
  containsThenInsertIfNew_snd := ExtTreeMap.containsThenInsertIfNew_snd
  getThenInsertIfNew?_fst := ExtTreeMap.getThenInsertIfNew?_fst
  getThenInsertIfNew?_snd := ExtTreeMap.getThenInsertIfNew?_snd
  contains_iff_mem := ExtTreeMap.contains_iff_mem
  getElem?_filter := by
    intros m f k; simp [filter, ExtTreeMap.getElem?_filter]
  getElem?_modify_self := by
    intros m k f; simp [MapAPI.modify]
  getElem?_modify_ne := by
    intros m k k' f hk; simp [MapAPI.modify, ExtTreeMap.getElem?_modify, hk]
  getElem?_alter_self := by
    intros m k f; simp [alter]
  getElem?_alter_ne := by
    intros m k k' f hk; simp [alter, ExtTreeMap.getElem?_alter, hk]


end MapAPI

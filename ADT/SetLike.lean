/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import ADT.List
import ADT.SetLemmas
import ADT.Size
import Std.Data
open Std

/-!
# Abstract datatypes for sets
-/

/-
  **TODO:** Not using the typeclass `Insert` because the type
  of `Insert.insert` does not match `Std.HashSet.insert`
  and `Std.TreeSet.insert`
-/
class SetLike (γ : Type u) (α : Type v) extends
  Membership α γ, Size γ where
  insert : γ → α → γ
  erase  : γ → α → γ

def SetLike.equiv {γ₁ γ₂ α} [inst₁ : SetLike γ₁ α] [inst₂ : SetLike γ₂ α]
  (m₁ : γ₁) (m₂ : γ₂) := ∀ (x : α), x ∈ m₁ ↔ x ∈ m₂

theorem SetLike.equiv.refl {γ α} [SetLike γ α] {m : γ} : equiv (α:=α) m m := by
  simp [equiv]

theorem SetLike.equiv.symm {γ₁ γ₂ α} [SetLike γ₁ α] [SetLike γ₂ α] {m₁ : γ₁} {m₂ : γ₂} :
  equiv (α:=α) m₁ m₂ ↔ equiv (α:=α) m₂ m₁ := by
  simp only [equiv]
  conv => left; enter [x]; rw [Iff.comm]

theorem SetLike.equiv.trans {γ₁ γ₂ γ₃ α} [inst₁ : SetLike γ₁ α] [inst₂ : SetLike γ₂ α] [inst₃ : SetLike γ₃ α]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv (α:=α) m₁ m₂ → equiv (α:=α) m₂ m₃ → equiv (α:=α) m₁ m₃ := by
  intro h₁ h₂ x
  rw [h₁, h₂]

open SetLike

class LawfulSetLike (γ : Type u) (α : Type v) [SetLike γ α] extends
  LawfulMemSize γ α where
  mem_insert : ∀ {m : γ} {x y : α}, y ∈ insert m x ↔ y ∈ m ∨ y = x
  mem_erase : ∀ {m : γ} {x y : α}, y ∈ erase m x ↔ y ∈ m ∧ y ≠ x
  size_erase_mem : ∀ {m : γ} {k : α}, k ∈ m → Size.size (erase m k) + 1 = Size.size m

theorem LawfulSetLike.exists_toList {γ α} [inst : SetLike γ α] [LawfulSetLike γ α] {m : γ} :
  ∃ (l : List α), l.length = Size.size m ∧ l.Nodup ∧ ∀ k, k ∈ m ↔ k ∈ l := by
  generalize hsz : Size.size m = n
  induction n generalizing m
  case zero =>
    exists []; simp [(LawfulMemSize.size_zero_iff_forall_not_mem (α:=α)).mp hsz]
  case succ n IH =>
    have hnz : Size.size m ≠ 0 := by
      intro h; rw [h] at hsz; simp at hsz
    have ⟨x, hx⟩ := LawfulMemSize.size_ne_zero_iff_exists_mem.mp hnz
    let me := erase m x
    have hmesz : Size.size (erase m x) = n := by
      have := (size_erase_mem hx).trans hsz; simp_all
    have ⟨l, hlen, hnd, hequiv⟩ := IH hmesz
    exists x::l
    apply And.intro ?len (And.intro ?nd ?equiv)
    case len => simp [hlen]
    case nd => simp [← hequiv, hnd, mem_erase]
    case equiv =>
      simp only [List.mem_cons, ← hequiv, mem_erase]
      intro k; apply Iff.intro
      case mp => intro hk; by_cases k = x <;> simp [*]
      case mpr => intro hk; cases hk <;> simp [*]

noncomputable def LawfulSetLike.exKeyList {γ α} [SetLike γ α] [LawfulSetLike γ α] (m : γ) : List α :=
  (exists_toList (α:=α) (m:=m)).choose

noncomputable def LawfulSetLike.length_exKeyList_eq_size {γ α} [SetLike γ α] [LawfulSetLike γ α] {m : γ} :
  (exKeyList (α:=α) m).length = Size.size m :=
  (Exists.choose_spec exists_toList).left

noncomputable def LawfulSetLike.length_exKeyList_nodup {γ α} [SetLike γ α] [LawfulSetLike γ α] {m : γ} :
  (exKeyList (α:=α) m).Nodup :=
  (Exists.choose_spec exists_toList).right.left

noncomputable def LawfulSetLike.length_exKeyList_equiv {γ α} [SetLike γ α] [LawfulSetLike γ α] {m : γ} :
  ∀ k, k ∈ m ↔ k ∈ (exKeyList (α:=α) m) :=
  (Exists.choose_spec exists_toList).right.right

theorem LawfulSetLike.size_eq_of_equiv {γ₁ γ₂ α} [SetLike γ₁ α] [SetLike γ₂ α]
  [LawfulSetLike γ₁ α] [LawfulSetLike γ₂ α] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) m₁ m₂) : Size.size m₁ = Size.size m₂ := by
  let ⟨l₁, heq₁, hnd₁, hequiv₁⟩ := exists_toList (α:=α) (m:=m₁)
  let ⟨l₂, heq₂, hnd₂, hequiv₂⟩ := exists_toList (α:=α) (m:=m₂)
  rw [← heq₁, ← heq₂]
  apply List.length_eq_of_perm
  apply (List.nodup_perm_iff_equiv hnd₁ hnd₂).mpr
  intro x; rw [← hequiv₁, ← hequiv₂]; apply hequiv

theorem LawfulSetLike.insert_mem_equiv {γ α} [SetLike γ α] [LawfulSetLike γ α]
  {m : γ} {k : α} (hmem : k ∈ m) : equiv (α:=α) (insert (α:=α) m k) m := by
  simp [equiv, mem_insert, hmem]

theorem LawfulSetLike.erase_insert_not_mem_equiv {γ α} [SetLike γ α] [LawfulSetLike γ α]
  {m : γ} {k : α} (hnmem : k ∉ m) : equiv (α:=α) (erase (insert m k) k) m := by
  simp only [equiv, mem_erase, mem_insert]
  intro x; by_cases (x = k) <;> simp_all

theorem LawfulSetLike.erase_not_mem_equiv {γ α} [SetLike γ α] [LawfulSetLike γ α]
  {m : γ} {k : α} (hnmem : k ∉ m) : equiv (α:=α) (erase m k) m := by
  simp only [equiv, mem_erase]
  intro x; by_cases (x = k) <;> simp_all

theorem LawfulSetLike.size_insert_mem {γ α} [SetLike γ α] [LawfulSetLike γ α] {m : γ}
  {k : α} (hmem : k ∈ m) : Size.size (insert m k) = Size.size m := by
  apply size_eq_of_equiv; apply insert_mem_equiv hmem

theorem LawfulSetLike.size_insert_not_mem {γ α} [SetLike γ α] [LawfulSetLike γ α] {m : γ}
  {k : α} (hnmem : k ∉ m) : Size.size (insert m k) = Size.size m + 1 := by
  have hke := erase_insert_not_mem_equiv hnmem
  rw [← size_eq_of_equiv hke]; symm
  apply size_erase_mem; simp [mem_insert]

theorem LawfulSetLike.size_erase_not_mem {γ α} [SetLike γ α] [LawfulSetLike γ α] {m : γ}
  {k : α} (hnm : k ∉ m) : Size.size (erase m k) = Size.size m := by
  apply size_eq_of_equiv; apply erase_not_mem_equiv hnm

set_option linter.unusedVariables false in
theorem LawfulSetLike.mem_congr {γ₁ γ₂ α} [inst₁ : SetLike γ₁ α] [inst₂ : SetLike γ₂ α]
  {m₁ : γ₁} {m₂ : γ₂} (hequiv : equiv (inst₁:=inst₁) m₁ m₂) (x : α) : x ∈ m₁ ↔ x ∈ m₂ :=
  hequiv _

theorem LawfulSetLike.insert_congr {γ₁ γ₂ α} [inst₁ : SetLike γ₁ α] [inst₂ : SetLike γ₂ α]
  [LawfulSetLike γ₁ α] [LawfulSetLike γ₂ α] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (inst₁:=inst₁) m₁ m₂) (k : α) :
  equiv (inst₁:=inst₁) (insert m₁ k) (insert m₂ k) := by
  intro x; simp only [LawfulSetLike.mem_insert]; rw [hequiv]

open Classical in
theorem LawfulSetLike.erase_congr {γ₁ γ₂ α} [inst₁ : SetLike γ₁ α] [inst₂ : SetLike γ₂ α]
  [LawfulSetLike γ₁ α] [LawfulSetLike γ₂ α] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (inst₁:=inst₁) m₁ m₂) (k : α) :
  equiv (inst₁:=inst₁) (erase m₁ (self:=inst₁) k) (erase m₂ (self:=inst₂) k) := by
  intro x; simp only [LawfulSetLike.mem_erase]; rw [hequiv]

theorem LawfulSetLike.size_congr {γ₁ γ₂ α} [inst₁ : SetLike γ₁ α] [inst₂ : SetLike γ₂ α]
  [LawfulSetLike γ₁ α] [LawfulSetLike γ₂ α] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (inst₁:=inst₁) m₁ m₂) : Size.size m₁ = Size.size m₂ :=
  LawfulSetLike.size_eq_of_equiv hequiv

instance {α} [BEq α] [Hashable α] : SetLike (HashSet α) α where
  insert := HashSet.insert
  erase := HashSet.erase
  size := HashSet.size

instance {α} [BEq α] [Hashable α] [LawfulBEq α] : LawfulSetLike (HashSet α) α where
  mem_insert := by
    intro m x y; simp only [SetLike.insert]
    simp only [HashSet.mem_insert, beq_iff_eq]
    apply Iff.intro <;> intro h <;> cases h <;> simp_all
  mem_erase := by
    intro m x y; simp only [SetLike.erase]
    simp only [HashSet.mem_erase, beq_eq_false_iff_ne]
    conv => enter [1, 1]; rw [ne_comm]
    apply and_comm
  size_erase_mem := by
    intro m x h
    have hnz := LawfulMemSize.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
    have hm : m.size - 1 + 1 = m.size := Nat.sub_add_cancel hnz
    simp [SetLike.erase, Size.size, HashSet.size_erase, h, hm]

instance {α} [Ord α] : SetLike (TreeSet α) α where
  insert := TreeSet.insert
  erase := TreeSet.erase
  size := TreeSet.size

instance {α} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulSetLike (TreeSet α) α where
  mem_insert := by
    intro m x y; simp only [SetLike.insert]
    rw [TreeSet.mem_insert, LawfulEqOrd.compare_eq_iff_eq]
    apply Iff.intro <;> intro h <;> cases h <;> simp_all
  mem_erase := by
    intro m x y; simp only [SetLike.erase]
    rw [TreeSet.mem_erase, Ne, LawfulEqOrd.compare_eq_iff_eq]
    conv => enter [2, 2]; rw [ne_comm]
    apply and_comm
  size_erase_mem := by
    intro m x h
    have hnz := LawfulMemSize.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
    have hm : m.size - 1 + 1 = m.size := Nat.sub_add_cancel hnz
    simp [SetLike.erase, Size.size, TreeSet.size_erase, h, hm]

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : SetLike (ExtHashSet α) α where
  insert := ExtHashSet.insert
  erase := ExtHashSet.erase
  size := ExtHashSet.size

instance {α} [BEq α] [Hashable α] [LawfulBEq α] : LawfulSetLike (ExtHashSet α) α where
  mem_insert := by
    intro m x y; simp only [SetLike.insert]
    simp only [ExtHashSet.mem_insert, beq_iff_eq]
    apply Iff.intro <;> intro h <;> cases h <;> simp_all
  mem_erase := by
    intro m x y; simp only [SetLike.erase]
    simp only [ExtHashSet.mem_erase, beq_eq_false_iff_ne]
    conv => enter [1, 1]; rw [ne_comm]
    apply and_comm
  size_erase_mem := by
    intro m x h
    have hnz := LawfulMemSize.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
    have hm : m.size - 1 + 1 = m.size := Nat.sub_add_cancel hnz
    simp [SetLike.erase, Size.size, ExtHashSet.size_erase, h, hm]

instance {α} [Ord α] : SetLike (TreeSet α) α where
  insert := TreeSet.insert
  erase := TreeSet.erase
  size := TreeSet.size

instance {α} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulSetLike (TreeSet α) α where
  mem_insert := by
    intro m x y; simp only [SetLike.insert]
    rw [TreeSet.mem_insert, LawfulEqOrd.compare_eq_iff_eq]
    apply Iff.intro <;> intro h <;> cases h <;> simp_all
  mem_erase := by
    intro m x y; simp only [SetLike.erase]
    rw [TreeSet.mem_erase, Ne, LawfulEqOrd.compare_eq_iff_eq]
    conv => enter [2, 2]; rw [ne_comm]
    apply and_comm
  size_erase_mem := by
    intro m x h
    have hnz := LawfulMemSize.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
    have hm : m.size - 1 + 1 = m.size := Nat.sub_add_cancel hnz
    simp [SetLike.erase, Size.size, TreeSet.size_erase, h, hm]

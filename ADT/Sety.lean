/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

import Lean
import ADT.List
import ADT.Lemmas
import ADT.Sizy
import Std.Data
open Std

-- Not using the typeclass `Insert` because the type
-- of `Insert.insert` does not match `Std.HashSet.insert`
-- and `Std.TreeSet.insert`
class Sety (γ : Type u) (α : Type v) extends
  Membership α γ, Sizy γ where
  insert : γ → α → γ
  erase  : γ → α → γ

def Sety.equiv {γ₁ γ₂ α} [inst₁ : Sety γ₁ α] [inst₂ : Sety γ₂ α]
  (m₁ : γ₁) (m₂ : γ₂) := ∀ (x : α), x ∈ m₁ ↔ x ∈ m₂

theorem Sety.equiv.refl {γ α} [Sety γ α] {m : γ} : equiv (α:=α) m m := by
  simp [equiv]

theorem Sety.equiv.symm {γ₁ γ₂ α} [Sety γ₁ α] [Sety γ₂ α] {m₁ : γ₁} {m₂ : γ₂} :
  equiv (α:=α) m₁ m₂ ↔ equiv (α:=α) m₂ m₁ := by
  simp only [equiv]
  conv => left; enter [x]; rw [Iff.comm]

theorem Sety.equiv.trans {γ₁ γ₂ γ₃ α} [inst₁ : Sety γ₁ α] [inst₂ : Sety γ₂ α] [inst₃ : Sety γ₃ α]
  {m₁ : γ₁} {m₂ : γ₂} {m₃ : γ₃} : equiv (α:=α) m₁ m₂ → equiv (α:=α) m₂ m₃ → equiv (α:=α) m₁ m₃ := by
  intro h₁ h₂ x
  rw [h₁, h₂]

open Sety

class LawfulSety (γ : Type u) (α : Type v) [Sety γ α] extends
  LawfulMemSizy γ α where
  mem_insert : ∀ {m : γ} {x y : α}, y ∈ insert m x ↔ y ∈ m ∨ y = x
  mem_erase : ∀ {m : γ} {x y : α}, y ∈ erase m x ↔ y ∈ m ∧ y ≠ x
  size_erase_mem : ∀ {m : γ} {k : α}, k ∈ m → Sizy.size (erase m k) + 1 = Sizy.size m

theorem LawfulSety.exists_toList {γ α} [inst : Sety γ α] [LawfulSety γ α] {m : γ} :
  ∃ (l : List α), l.length = Sizy.size m ∧ l.Nodup ∧ ∀ k, k ∈ m ↔ k ∈ l := by
  generalize hsz : Sizy.size m = n
  induction n generalizing m
  case zero =>
    exists []; simp [(LawfulMemSizy.size_zero_iff_forall_not_mem (α:=α)).mp hsz]
  case succ n IH =>
    have hnz : Sizy.size m ≠ 0 := by
      intro h; rw [h] at hsz; simp at hsz
    have ⟨x, hx⟩ := LawfulMemSizy.size_ne_zero_iff_exists_mem.mp hnz
    let me := erase m x
    have hmesz : Sizy.size (erase m x) = n := by
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

noncomputable def LawfulSety.exKeyList {γ α} [Sety γ α] [LawfulSety γ α] (m : γ) : List α :=
  (exists_toList (α:=α) (m:=m)).choose

noncomputable def LawfulSety.length_exKeyList_eq_size {γ α} [Sety γ α] [LawfulSety γ α] {m : γ} :
  (exKeyList (α:=α) m).length = Sizy.size m :=
  (Exists.choose_spec exists_toList).left

noncomputable def LawfulSety.length_exKeyList_nodup {γ α} [Sety γ α] [LawfulSety γ α] {m : γ} :
  (exKeyList (α:=α) m).Nodup :=
  (Exists.choose_spec exists_toList).right.left

noncomputable def LawfulSety.length_exKeyList_equiv {γ α} [Sety γ α] [LawfulSety γ α] {m : γ} :
  ∀ k, k ∈ m ↔ k ∈ (exKeyList (α:=α) m) :=
  (Exists.choose_spec exists_toList).right.right

theorem LawfulSety.size_eq_of_equiv {γ₁ γ₂ α} [Sety γ₁ α] [Sety γ₂ α]
  [LawfulSety γ₁ α] [LawfulSety γ₂ α] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (α:=α) m₁ m₂) : Sizy.size m₁ = Sizy.size m₂ := by
  let ⟨l₁, heq₁, hnd₁, hequiv₁⟩ := exists_toList (α:=α) (m:=m₁)
  let ⟨l₂, heq₂, hnd₂, hequiv₂⟩ := exists_toList (α:=α) (m:=m₂)
  rw [← heq₁, ← heq₂]
  apply List.length_eq_of_perm
  apply (List.nodup_perm_iff_equiv hnd₁ hnd₂).mpr
  intro x; rw [← hequiv₁, ← hequiv₂]; apply hequiv

theorem LawfulSety.insert_mem_equiv {γ α} [Sety γ α] [LawfulSety γ α]
  {m : γ} {k : α} (hmem : k ∈ m) : equiv (α:=α) (insert (α:=α) m k) m := by
  simp [equiv, mem_insert, hmem]

theorem LawfulSety.erase_insert_not_mem_equiv {γ α} [Sety γ α] [LawfulSety γ α]
  {m : γ} {k : α} (hnmem : k ∉ m) : equiv (α:=α) (erase (insert m k) k) m := by
  simp only [equiv, mem_erase, mem_insert]
  intro x; by_cases (x = k) <;> simp_all

theorem LawfulSety.erase_not_mem_equiv {γ α} [Sety γ α] [LawfulSety γ α]
  {m : γ} {k : α} (hnmem : k ∉ m) : equiv (α:=α) (erase m k) m := by
  simp only [equiv, mem_erase]
  intro x; by_cases (x = k) <;> simp_all

theorem LawfulSety.size_insert_mem {γ α} [Sety γ α] [LawfulSety γ α] {m : γ}
  {k : α} (hmem : k ∈ m) : Sizy.size (insert m k) = Sizy.size m := by
  apply size_eq_of_equiv; apply insert_mem_equiv hmem

theorem LawfulSety.size_insert_not_mem {γ α} [Sety γ α] [LawfulSety γ α] {m : γ}
  {k : α} (hnmem : k ∉ m) : Sizy.size (insert m k) = Sizy.size m + 1 := by
  have hke := erase_insert_not_mem_equiv hnmem
  rw [← size_eq_of_equiv hke]; symm
  apply size_erase_mem; simp [mem_insert]

theorem LawfulSety.size_erase_not_mem {γ α} [Sety γ α] [LawfulSety γ α] {m : γ}
  {k : α} (hnm : k ∉ m) : Sizy.size (erase m k) = Sizy.size m := by
  apply size_eq_of_equiv; apply erase_not_mem_equiv hnm

set_option linter.unusedVariables false in
theorem LawfulSety.mem_congr {γ₁ γ₂ α} [inst₁ : Sety γ₁ α] [inst₂ : Sety γ₂ α]
  {m₁ : γ₁} {m₂ : γ₂} (hequiv : equiv (inst₁:=inst₁) m₁ m₂) (x : α) : x ∈ m₁ ↔ x ∈ m₂ :=
  hequiv _

theorem LawfulSety.insert_congr {γ₁ γ₂ α} [inst₁ : Sety γ₁ α] [inst₂ : Sety γ₂ α]
  [LawfulSety γ₁ α] [LawfulSety γ₂ α] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (inst₁:=inst₁) m₁ m₂) (k : α) :
  equiv (inst₁:=inst₁) (insert m₁ k) (insert m₂ k) := by
  intro x; simp only [LawfulSety.mem_insert]; rw [hequiv]

open Classical in
theorem LawfulSety.erase_congr {γ₁ γ₂ α} [inst₁ : Sety γ₁ α] [inst₂ : Sety γ₂ α]
  [LawfulSety γ₁ α] [LawfulSety γ₂ α] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (inst₁:=inst₁) m₁ m₂) (k : α) :
  equiv (inst₁:=inst₁) (erase m₁ (self:=inst₁) k) (erase m₂ (self:=inst₂) k) := by
  intro x; simp only [LawfulSety.mem_erase]; rw [hequiv]

theorem LawfulSety.size_congr {γ₁ γ₂ α} [inst₁ : Sety γ₁ α] [inst₂ : Sety γ₂ α]
  [LawfulSety γ₁ α] [LawfulSety γ₂ α] {m₁ : γ₁} {m₂ : γ₂}
  (hequiv : equiv (inst₁:=inst₁) m₁ m₂) : Sizy.size m₁ = Sizy.size m₂ :=
  LawfulSety.size_eq_of_equiv hequiv

instance {α} [BEq α] [Hashable α] : Sety (HashSet α) α where
  insert := HashSet.insert
  erase := HashSet.erase
  size := HashSet.size

instance {α} [BEq α] [Hashable α] [LawfulBEq α] : LawfulSety (HashSet α) α where
  mem_insert := by
    intro m x y; simp only [Sety.insert]
    simp only [HashSet.mem_insert, beq_iff_eq]
    apply Iff.intro <;> intro h <;> cases h <;> simp_all
  mem_erase := by
    intro m x y; simp only [Sety.erase]
    simp only [HashSet.mem_erase, beq_eq_false_iff_ne]
    conv => enter [1, 1]; rw [ne_comm]
    apply and_comm
  size_erase_mem := by
    intro m x h
    have hnz := LawfulMemSizy.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
    have hm : m.size - 1 + 1 = m.size := Nat.sub_add_cancel hnz
    simp [Sety.erase, Sizy.size, HashSet.size_erase, h, hm]

instance {α} [Ord α] : Sety (TreeSet α) α where
  insert := TreeSet.insert
  erase := TreeSet.erase
  size := TreeSet.size

instance {α} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulSety (TreeSet α) α where
  mem_insert := by
    intro m x y; simp only [Sety.insert]
    rw [TreeSet.mem_insert, LawfulEqOrd.compare_eq_iff_eq]
    apply Iff.intro <;> intro h <;> cases h <;> simp_all
  mem_erase := by
    intro m x y; simp only [Sety.erase]
    rw [TreeSet.mem_erase, Ne, LawfulEqOrd.compare_eq_iff_eq]
    conv => enter [2, 2]; rw [ne_comm]
    apply and_comm
  size_erase_mem := by
    intro m x h
    have hnz := LawfulMemSizy.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
    have hm : m.size - 1 + 1 = m.size := Nat.sub_add_cancel hnz
    simp [Sety.erase, Sizy.size, TreeSet.size_erase, h, hm]

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Sety (ExtHashSet α) α where
  insert := ExtHashSet.insert
  erase := ExtHashSet.erase
  size := ExtHashSet.size

instance {α} [BEq α] [Hashable α] [LawfulBEq α] : LawfulSety (ExtHashSet α) α where
  mem_insert := by
    intro m x y; simp only [Sety.insert]
    simp only [ExtHashSet.mem_insert, beq_iff_eq]
    apply Iff.intro <;> intro h <;> cases h <;> simp_all
  mem_erase := by
    intro m x y; simp only [Sety.erase]
    simp only [ExtHashSet.mem_erase, beq_eq_false_iff_ne]
    conv => enter [1, 1]; rw [ne_comm]
    apply and_comm
  size_erase_mem := by
    intro m x h
    have hnz := LawfulMemSizy.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
    have hm : m.size - 1 + 1 = m.size := Nat.sub_add_cancel hnz
    simp [Sety.erase, Sizy.size, ExtHashSet.size_erase, h, hm]

instance {α} [Ord α] : Sety (TreeSet α) α where
  insert := TreeSet.insert
  erase := TreeSet.erase
  size := TreeSet.size

instance {α} [Ord α] [LawfulEqOrd α] [TransOrd α] : LawfulSety (TreeSet α) α where
  mem_insert := by
    intro m x y; simp only [Sety.insert]
    rw [TreeSet.mem_insert, LawfulEqOrd.compare_eq_iff_eq]
    apply Iff.intro <;> intro h <;> cases h <;> simp_all
  mem_erase := by
    intro m x y; simp only [Sety.erase]
    rw [TreeSet.mem_erase, Ne, LawfulEqOrd.compare_eq_iff_eq]
    conv => enter [2, 2]; rw [ne_comm]
    apply and_comm
  size_erase_mem := by
    intro m x h
    have hnz := LawfulMemSizy.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
    have hm : m.size - 1 + 1 = m.size := Nat.sub_add_cancel hnz
    simp [Sety.erase, Sizy.size, TreeSet.size_erase, h, hm]

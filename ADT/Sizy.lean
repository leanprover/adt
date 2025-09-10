/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

import Lean
import ADT.OptArr
import ADT.Lemmas
import Std.Data
open Std

class Sizy (γ : Type u) where
  size : γ → Nat

instance {α} : Sizy (Option α) where
  size o := match o with | .some _ => 1 | .none => 0

instance {α} : Sizy (List α) where
  size := List.length

instance {α} : Sizy (Array α) where
  size := Array.size

instance {α β} [BEq α] [Hashable α] : Sizy (DHashMap α β) where
  size := DHashMap.size

instance {α β} [Ord α] : Sizy (DTreeMap α β) where
  size := DTreeMap.size

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Sizy (ExtDHashMap α β) where
  size := ExtDHashMap.size

instance {α β} [Ord α] : Sizy (ExtDTreeMap α β) where
  size := ExtDTreeMap.size

instance {α β} [BEq α] [Hashable α] : Sizy (HashMap α β) where
  size := HashMap.size

instance {α} : Sizy (OptArr α) where
  size := OptArr.size

instance {α β} [Ord α] : Sizy (TreeMap α β) where
  size := TreeMap.size

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Sizy (ExtHashMap α β) where
  size := ExtHashMap.size

instance {α β} [Ord α] : Sizy (ExtTreeMap α β) where
  size := ExtTreeMap.size

instance {α} [BEq α] [Hashable α] : Sizy (HashSet α) where
  size := HashSet.size

instance {α} [Ord α] : Sizy (TreeSet α) where
  size := TreeSet.size

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Sizy (ExtHashSet α) where
  size := ExtHashSet.size

instance {α} [Ord α] : Sizy (ExtTreeSet α) where
  size := ExtTreeSet.size

class LawfulMemSizy (γ : Type u) (α : Type v) [Sizy γ] [Membership α γ] where
  size_zero_iff_forall_not_mem : ∀ {m : γ}, Sizy.size m = 0 ↔ ∀ (x : α), ¬ x ∈ m

theorem LawfulMemSizy.size_ne_zero_iff_exists_mem {γ α} [Sizy γ] [Membership α γ] [LawfulMemSizy γ α] {m : γ} :
  Sizy.size m ≠ 0 ↔ ∃ (x : α), x ∈ m := by
  rw [ne_eq, size_zero_iff_forall_not_mem (α:=α)]; simp

theorem LawfulMemSizy.size_gt_zero_iff_exists_mem {γ α} [Sizy γ] [Membership α γ] [LawfulMemSizy γ α] {m : γ} :
  Sizy.size m > 0 ↔ ∃ (x : α), x ∈ m := by
  rw [← size_ne_zero_iff_exists_mem, Nat.ne_zero_iff_zero_lt];

instance {α} : LawfulMemSizy (Option α) α where
  size_zero_iff_forall_not_mem := by
    intro m; cases m <;> simp [Sizy.size]

instance {α} : LawfulMemSizy (List α) α where
  size_zero_iff_forall_not_mem := by
    intro m
    simp only [Sizy.size, List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]

instance {α} : LawfulMemSizy (Array α) α where
  size_zero_iff_forall_not_mem := by
    intro m
    simp only [Sizy.size, Array.size_eq_zero_iff, Array.eq_empty_iff_forall_not_mem]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSizy (DHashMap α β) α where
  size_zero_iff_forall_not_mem := DHashMap.size_zero_iff_forall_not_mem

instance {α β} [Ord α] [TransOrd α] : LawfulMemSizy (DTreeMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← DTreeMap.isEmpty_iff_forall_not_mem,
        DTreeMap.isEmpty_eq_size_eq_zero]
    simp [Sizy.size]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSizy (ExtDHashMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtDHashMap.eq_empty_iff_forall_not_mem,
        ExtDHashMap.eq_empty_iff_size_eq_zero]
    rfl

instance {α β} [Ord α] [TransOrd α] : LawfulMemSizy (ExtDTreeMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtDTreeMap.isEmpty_iff_forall_not_mem,
        ExtDTreeMap.isEmpty_eq_size_eq_zero]
    simp [Sizy.size]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSizy (HashMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m; simp only [Sizy.size]
    apply HashMap.size_zero_iff_forall_not_mem

instance {α} : LawfulMemSizy (OptArr α) Nat where
  size_zero_iff_forall_not_mem := OptArr.size_zero_iff_forall_not_mem

instance {α β} [Ord α] [TransOrd α] : LawfulMemSizy (TreeMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← TreeMap.isEmpty_iff_forall_not_mem,
        TreeMap.isEmpty_eq_size_eq_zero]
    simp [Sizy.size]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSizy (ExtHashMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtHashMap.eq_empty_iff_forall_not_mem,
        ExtHashMap.eq_empty_iff_size_eq_zero]
    rfl

instance {α β} [Ord α] [TransOrd α] : LawfulMemSizy (ExtTreeMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtTreeMap.isEmpty_iff_forall_not_mem,
        ExtTreeMap.isEmpty_eq_size_eq_zero]
    simp [Sizy.size]

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSizy (HashSet α) α where
  size_zero_iff_forall_not_mem := HashSet.size_zero_iff_forall_not_mem

instance {α} [Ord α] [TransOrd α] : LawfulMemSizy (TreeSet α) α where
  size_zero_iff_forall_not_mem := TreeSet.size_zero_iff_forall_not_mem

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSizy (ExtHashSet α) α where
  size_zero_iff_forall_not_mem := ExtHashSet.size_zero_iff_forall_not_mem

instance {α} [Ord α] [TransOrd α] : LawfulMemSizy (ExtTreeSet α) α where
  size_zero_iff_forall_not_mem := ExtTreeSet.size_zero_iff_forall_not_mem

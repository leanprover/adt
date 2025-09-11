/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

import Lean
import ADT.OptArr
import ADT.MapLemmas
import ADT.SetLemmas
import Std.Data
open Std

/-!
# The typeclass `Size`

The typeclass `Size` for the operation `size`, and
related `Lawful` typeclasses.
-/

class Size (γ : Type u) where
  size : γ → Nat

instance {α} : Size (Option α) where
  size o := match o with | .some _ => 1 | .none => 0

instance {α} : Size (List α) where
  size := List.length

instance {α} : Size (Array α) where
  size := Array.size

instance {α β} [BEq α] [Hashable α] : Size (DHashMap α β) where
  size := DHashMap.size

instance {α β} [Ord α] : Size (DTreeMap α β) where
  size := DTreeMap.size

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Size (ExtDHashMap α β) where
  size := ExtDHashMap.size

instance {α β} [Ord α] : Size (ExtDTreeMap α β) where
  size := ExtDTreeMap.size

instance {α β} [BEq α] [Hashable α] : Size (HashMap α β) where
  size := HashMap.size

instance {α} : Size (OptArr α) where
  size := OptArr.size

instance {α β} [Ord α] : Size (TreeMap α β) where
  size := TreeMap.size

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Size (ExtHashMap α β) where
  size := ExtHashMap.size

instance {α β} [Ord α] : Size (ExtTreeMap α β) where
  size := ExtTreeMap.size

instance {α} [BEq α] [Hashable α] : Size (HashSet α) where
  size := HashSet.size

instance {α} [Ord α] : Size (TreeSet α) where
  size := TreeSet.size

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Size (ExtHashSet α) where
  size := ExtHashSet.size

instance {α} [Ord α] : Size (ExtTreeSet α) where
  size := ExtTreeSet.size

class LawfulMemSize (γ : Type u) (α : Type v) [Size γ] [Membership α γ] where
  size_zero_iff_forall_not_mem : ∀ {m : γ}, Size.size m = 0 ↔ ∀ (x : α), ¬ x ∈ m

theorem LawfulMemSize.size_ne_zero_iff_exists_mem {γ α} [Size γ] [Membership α γ] [LawfulMemSize γ α] {m : γ} :
  Size.size m ≠ 0 ↔ ∃ (x : α), x ∈ m := by
  rw [ne_eq, size_zero_iff_forall_not_mem (α:=α)]; simp

theorem LawfulMemSize.size_gt_zero_iff_exists_mem {γ α} [Size γ] [Membership α γ] [LawfulMemSize γ α] {m : γ} :
  Size.size m > 0 ↔ ∃ (x : α), x ∈ m := by
  rw [← size_ne_zero_iff_exists_mem, Nat.ne_zero_iff_zero_lt];

instance {α} : LawfulMemSize (Option α) α where
  size_zero_iff_forall_not_mem := by
    intro m; cases m <;> simp [Size.size]

instance {α} : LawfulMemSize (List α) α where
  size_zero_iff_forall_not_mem := by
    intro m
    simp only [Size.size, List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]

instance {α} : LawfulMemSize (Array α) α where
  size_zero_iff_forall_not_mem := by
    intro m
    simp only [Size.size, Array.size_eq_zero_iff, Array.eq_empty_iff_forall_not_mem]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSize (DHashMap α β) α where
  size_zero_iff_forall_not_mem := DHashMap.size_zero_iff_forall_not_mem

instance {α β} [Ord α] [TransOrd α] : LawfulMemSize (DTreeMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← DTreeMap.isEmpty_iff_forall_not_mem,
        DTreeMap.isEmpty_eq_size_eq_zero]
    simp [Size.size]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSize (ExtDHashMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtDHashMap.eq_empty_iff_forall_not_mem,
        ExtDHashMap.eq_empty_iff_size_eq_zero]
    rfl

instance {α β} [Ord α] [TransOrd α] : LawfulMemSize (ExtDTreeMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtDTreeMap.isEmpty_iff_forall_not_mem,
        ExtDTreeMap.isEmpty_eq_size_eq_zero]
    simp [Size.size]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSize (HashMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m; simp only [Size.size]
    apply HashMap.size_zero_iff_forall_not_mem

instance {α} : LawfulMemSize (OptArr α) Nat where
  size_zero_iff_forall_not_mem := OptArr.size_zero_iff_forall_not_mem

instance {α β} [Ord α] [TransOrd α] : LawfulMemSize (TreeMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← TreeMap.isEmpty_iff_forall_not_mem,
        TreeMap.isEmpty_eq_size_eq_zero]
    simp [Size.size]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSize (ExtHashMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtHashMap.eq_empty_iff_forall_not_mem,
        ExtHashMap.eq_empty_iff_size_eq_zero]
    rfl

instance {α β} [Ord α] [TransOrd α] : LawfulMemSize (ExtTreeMap α β) α where
  size_zero_iff_forall_not_mem := by
    intro m
    rw [← ExtTreeMap.isEmpty_iff_forall_not_mem,
        ExtTreeMap.isEmpty_eq_size_eq_zero]
    simp [Size.size]

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSize (HashSet α) α where
  size_zero_iff_forall_not_mem := HashSet.size_zero_iff_forall_not_mem

instance {α} [Ord α] [TransOrd α] : LawfulMemSize (TreeSet α) α where
  size_zero_iff_forall_not_mem := TreeSet.size_zero_iff_forall_not_mem

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulMemSize (ExtHashSet α) α where
  size_zero_iff_forall_not_mem := ExtHashSet.size_zero_iff_forall_not_mem

instance {α} [Ord α] [TransOrd α] : LawfulMemSize (ExtTreeSet α) α where
  size_zero_iff_forall_not_mem := ExtTreeSet.size_zero_iff_forall_not_mem

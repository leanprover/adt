/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import Std.Data
import ADT.Size
open Std

/-!
# Typeclasses related to the membership operation
-/

class IsEmpty (γ : Type u) where
  isEmpty : γ → Bool

instance {α} : IsEmpty (List α) where
  isEmpty := List.isEmpty

instance {α} : IsEmpty (Array α) where
  isEmpty := Array.isEmpty

instance {α β} [BEq α] [Hashable α] : IsEmpty (DHashMap α β) where
  isEmpty := DHashMap.isEmpty

instance {α β} [Ord α] : IsEmpty (DTreeMap α β) where
  isEmpty := DTreeMap.isEmpty

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : IsEmpty (ExtDHashMap α β) where
  isEmpty := ExtDHashMap.isEmpty

instance {α β} [Ord α] : IsEmpty (ExtDTreeMap α β) where
  isEmpty := ExtDTreeMap.isEmpty

instance {α β} [BEq α] [Hashable α] : IsEmpty (HashMap α β) where
  isEmpty := HashMap.isEmpty

instance {α} : IsEmpty (OptArr α) where
  isEmpty := OptArr.isEmpty

instance {α β} [Ord α] : IsEmpty (TreeMap α β) where
  isEmpty := TreeMap.isEmpty

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : IsEmpty (ExtHashMap α β) where
  isEmpty := ExtHashMap.isEmpty

instance {α β} [Ord α] : IsEmpty (ExtTreeMap α β) where
  isEmpty := ExtTreeMap.isEmpty

instance {α} [BEq α] [Hashable α] : IsEmpty (HashSet α) where
  isEmpty := HashSet.isEmpty

instance {α} [Ord α] : IsEmpty (TreeSet α) where
  isEmpty := TreeSet.isEmpty

class Contains (γ : Type u) (α : Type v) where
  contains : γ → α → Bool

instance {α} [BEq α] : Contains (Array α) α where
  contains := Array.contains

instance {α} [BEq α] : Contains (List α) α where
  contains := List.contains

instance {α β} [BEq α] [Hashable α] : Contains (DHashMap α β) α where
  contains := DHashMap.contains

instance {α β} [Ord α] : Contains (DTreeMap α β) α where
  contains := DTreeMap.contains

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Contains (ExtDHashMap α β) α where
  contains := ExtDHashMap.contains

instance {α β} [Ord α] [TransOrd α] : Contains (ExtDTreeMap α β) α where
  contains := ExtDTreeMap.contains

instance {α β} [BEq α] [Hashable α] : Contains (HashMap α β) α where
  contains := HashMap.contains

instance {α} : Contains (OptArr α) Nat where
  contains := OptArr.containsIdx

instance {α β} [Ord α] : Contains (TreeMap α β) α where
  contains := TreeMap.contains

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Contains (ExtHashMap α β) α where
  contains := ExtHashMap.contains

instance {α β} [Ord α] [TransOrd α] : Contains (ExtTreeMap α β) α where
  contains := ExtTreeMap.contains

instance {α} [BEq α] [Hashable α] : Contains (HashSet α) α where
  contains := HashSet.contains

instance {α} [Ord α] : Contains (TreeSet α) α where
  contains := TreeSet.contains

class LawfulIsEmptySize (γ) [IsEmpty γ] [Size γ] where
  isEmpty_iff_size_eq_zero {m : γ} : IsEmpty.isEmpty m ↔ Size.size m = 0

theorem LawfulIsEmptySize.isEmpty_eq_size_beq_zero {γ} [IsEmpty γ] [Size γ] [LawfulIsEmptySize γ]
  {m : γ} : IsEmpty.isEmpty m = (Size.size m == 0) := by
  rw [Bool.eq_iff_iff, isEmpty_iff_size_eq_zero]; simp

theorem LawfulIsEmptySize.isEmpty_eq_false_iff_size_ne_zero {γ} [IsEmpty γ] [Size γ] [LawfulIsEmptySize γ]
  {m : γ} : IsEmpty.isEmpty m = false ↔ Size.size m ≠ 0 := by
  rw [Ne, ← isEmpty_iff_size_eq_zero]; simp

theorem LawfulIsEmptySize.isEmpty_eq_false_iff_size_gt_zero {γ} [IsEmpty γ] [Size γ] [LawfulIsEmptySize γ]
  {m : γ} : IsEmpty.isEmpty m = false ↔ Size.size m > 0 := by
  rw [isEmpty_eq_false_iff_size_ne_zero]; apply Nat.ne_zero_iff_zero_lt

instance {α} : LawfulIsEmptySize (List α) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, Size.size, List.isEmpty_iff_length_eq_zero]

instance {α} : LawfulIsEmptySize (Array α) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, Size.size, Array.isEmpty_iff_size_eq_zero]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulIsEmptySize (DHashMap α β) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, DHashMap.isEmpty_iff_forall_not_mem,
               LawfulMemSize.size_zero_iff_forall_not_mem]

instance {α β} [Ord α] [TransOrd α] : LawfulIsEmptySize (DTreeMap α β) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, DTreeMap.isEmpty_iff_forall_not_mem,
               LawfulMemSize.size_zero_iff_forall_not_mem]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulIsEmptySize (ExtDHashMap α β) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, ExtDHashMap.isEmpty_iff]
    rw [ExtDHashMap.eq_empty_iff_forall_not_mem,
        LawfulMemSize.size_zero_iff_forall_not_mem (α:=α)]

instance {α β} [Ord α] [TransOrd α] : LawfulIsEmptySize (ExtDTreeMap α β) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, ExtDTreeMap.isEmpty_iff_forall_not_mem,
               LawfulMemSize.size_zero_iff_forall_not_mem]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulIsEmptySize (HashMap α β) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, HashMap.isEmpty_iff_forall_not_mem,
               LawfulMemSize.size_zero_iff_forall_not_mem]

instance {α} : LawfulIsEmptySize (OptArr α) where
  isEmpty_iff_size_eq_zero := OptArr.isEmpty_iff_size_eq_zero

instance {α β} [Ord α] [TransOrd α] : LawfulIsEmptySize (TreeMap α β) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, TreeMap.isEmpty_iff_forall_not_mem,
               LawfulMemSize.size_zero_iff_forall_not_mem]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulIsEmptySize (ExtHashMap α β) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, ExtHashMap.isEmpty_iff]
    rw [ExtHashMap.eq_empty_iff_forall_not_mem,
        LawfulMemSize.size_zero_iff_forall_not_mem (α:=α)]

instance {α β} [Ord α] [TransOrd α] : LawfulIsEmptySize (ExtTreeMap α β) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, ExtTreeMap.isEmpty_iff_forall_not_mem,
               LawfulMemSize.size_zero_iff_forall_not_mem]

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulIsEmptySize (HashSet α) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, HashSet.isEmpty_iff_forall_not_mem,
               LawfulMemSize.size_zero_iff_forall_not_mem]

instance {α} [Ord α] [TransOrd α] : LawfulIsEmptySize (TreeSet α) where
  isEmpty_iff_size_eq_zero := by
    intro m
    simp only [IsEmpty.isEmpty, TreeSet.isEmpty_iff_forall_not_mem,
               LawfulMemSize.size_zero_iff_forall_not_mem]

class LawfulContainsMem (γ α) [Contains γ α] [Membership α γ] where
  contains_iff_mem {m : γ} {k : α} : Contains.contains m k ↔ k ∈ m

instance {α} [BEq α] [LawfulBEq α] : LawfulContainsMem (List α) α where
  contains_iff_mem := List.contains_iff_mem

instance {α} [BEq α] [LawfulBEq α] : LawfulContainsMem (Array α) α where
  contains_iff_mem := Array.contains_iff_mem

instance {α β} [BEq α] [Hashable α] : LawfulContainsMem (DHashMap α β) α where
  contains_iff_mem := DHashMap.contains_iff_mem

instance {α β} [Ord α] : LawfulContainsMem (DTreeMap α β) α where
  contains_iff_mem := DTreeMap.contains_iff_mem

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulContainsMem (ExtDHashMap α β) α where
  contains_iff_mem := ExtDHashMap.contains_iff_mem

instance {α β} [BEq α] [Hashable α] : LawfulContainsMem (HashMap α β) α where
  contains_iff_mem := HashMap.contains_iff_mem

instance {α} : LawfulContainsMem (OptArr α) Nat where
  contains_iff_mem := OptArr.containsIdx_iff_mem

instance {α β} [Ord α] : LawfulContainsMem (TreeMap α β) α where
  contains_iff_mem := TreeMap.contains_iff_mem

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulContainsMem (ExtHashMap α β) α where
  contains_iff_mem := ExtHashMap.contains_iff_mem

instance {α β} [Ord α] [TransOrd α] : LawfulContainsMem (ExtTreeMap α β) α where
  contains_iff_mem := ExtTreeMap.contains_iff_mem

instance {α} [BEq α] [Hashable α] : LawfulContainsMem (HashSet α) α where
  contains_iff_mem := HashSet.contains_iff_mem

instance {α} [Ord α] : LawfulContainsMem (TreeSet α) α where
  contains_iff_mem := TreeSet.contains_iff_mem

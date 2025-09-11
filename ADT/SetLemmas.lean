/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import Std.Data
open Std

/-!
# Additional theorems about sets
-/

theorem Std.HashSet.size_zero_iff_forall_not_mem
  {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : HashSet α} : m.size = 0 ↔ ∀ x, x ∉ m := by
  rw [← HashSet.isEmpty_iff_forall_not_mem, HashSet.isEmpty_eq_size_eq_zero]
  simp

theorem Std.TreeSet.size_zero_iff_forall_not_mem
  {α} [Ord α] [TransOrd α] {m : TreeSet α} : m.size = 0 ↔ ∀ x, x ∉ m := by
  rw [← TreeSet.isEmpty_iff_forall_not_mem, TreeSet.isEmpty_eq_size_eq_zero]
  simp

theorem Std.ExtHashSet.size_zero_iff_forall_not_mem
  {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : ExtHashSet α} : m.size = 0 ↔ ∀ x, x ∉ m := by
  rw [← ExtHashSet.eq_empty_iff_forall_not_mem, ExtHashSet.eq_empty_iff_size_eq_zero]

theorem Std.ExtTreeSet.size_zero_iff_forall_not_mem
  {α} [Ord α] [TransOrd α] {m : ExtTreeSet α} : m.size = 0 ↔ ∀ x, x ∉ m := by
  rw [← ExtTreeSet.eq_empty_iff_forall_not_mem, ExtTreeSet.eq_empty_iff_size_eq_zero]

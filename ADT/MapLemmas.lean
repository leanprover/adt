/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import Std.Data
open Std

/-!
# Additional theorems about maps
-/

theorem Std.DHashMap.size_zero_iff_forall_not_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : DHashMap α β} : m.size = 0 ↔ ∀ x, x ∉ m := by
  rw [← DHashMap.isEmpty_iff_forall_not_mem, DHashMap.isEmpty_eq_size_eq_zero]
  simp

theorem Std.DHashMap.size_ne_zero_iff_exists_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : DHashMap α β} :
    m.size ≠ 0 ↔ ∃ (x : α), x ∈ m := by
  rw [ne_eq, size_zero_iff_forall_not_mem]
  simp

theorem Std.DHashMap.size_gt_zero_iff_exists_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : DHashMap α β} :
    m.size > 0 ↔ ∃ (x : α), x ∈ m := by
  rw [← size_ne_zero_iff_exists_mem, Nat.ne_zero_iff_zero_lt]

theorem Std.DHashMap.size_erase_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : DHashMap α β} {k : α} (h : k ∈ m) :
    size (erase m k) + 1 = size m := by
  have hnz := DHashMap.size_gt_zero_iff_exists_mem.mpr ⟨_, h⟩
  grind

theorem Std.DTreeMap.size_ne_zero_of_mem {α β} [Ord α] [TransOrd α]
    {t : DTreeMap α β} {k : α} (hmem : k ∈ t) : t.size ≠ 0 := by
  have hne := DTreeMap.isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨_, hmem⟩
  rw [DTreeMap.isEmpty_eq_size_eq_zero] at hne
  simp_all

theorem Std.DTreeMap.size_erase_mem {α β} [Ord α] [TransOrd α]
    {m : DTreeMap α β} {k : α} (hk : k ∈ m) : size (erase m k) + 1 = size m := by
  have hne : m.size ≠ 0 := DTreeMap.size_ne_zero_of_mem hk
  grind

theorem Std.DTreeMap.get?_filter {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] {t : DTreeMap α β}
    {k : α} {f : (a : α) → β a → Bool} : (t.filter f).get? k = Option.filter (f k) (t.get? k) := by
  cases h : Option.filter (f k) (t.get? k)
  case none =>
    rw [Option.eq_none_iff_forall_ne_some]; intro a ha
    rw [← DTreeMap.mem_toList_iff_get?_eq_some] at ha
    simp only [DTreeMap.filter, DTreeMap.toList] at ha
    simp only [DTreeMap.Internal.Impl.toList_eq_toListModel,
               DTreeMap.Internal.Impl.toListModel_filter,
               List.mem_filter] at ha
    rw [← DTreeMap.Internal.Impl.toList_eq_toListModel,
        ← DTreeMap.toList, DTreeMap.mem_toList_iff_get?_eq_some] at ha
    revert h ha; cases t.get? k
    case none => simp
    case some => intro h ha; cases ha.left; simp_all
  case some v =>
    rw [← DTreeMap.mem_toList_iff_get?_eq_some]
    simp only [DTreeMap.filter, DTreeMap.toList]
    simp only [DTreeMap.Internal.Impl.toList_eq_toListModel,
               DTreeMap.Internal.Impl.toListModel_filter,
               List.mem_filter]
    rw [← DTreeMap.Internal.Impl.toList_eq_toListModel,
        ← DTreeMap.toList, DTreeMap.mem_toList_iff_get?_eq_some]
    revert h; cases t.get? k <;> simp

theorem Std.ExtDHashMap.size_ne_zero_of_mem {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {t : ExtDHashMap α β} {k : α} (hmem : k ∈ t) : t.size ≠ 0 := by
  have hne : t ≠ ∅ := by
    rw [Ne, ExtDHashMap.eq_empty_iff_forall_not_mem]
    intro h; exact h _ hmem
  rw [Ne, ExtDHashMap.eq_empty_iff_size_eq_zero] at hne
  exact hne

theorem Std.ExtDHashMap.size_erase_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : ExtDHashMap α β} {k : α} (hk : k ∈ m) : size (erase m k) + 1 = size m := by
  have hne : m.size ≠ 0 := ExtDHashMap.size_ne_zero_of_mem hk
  grind

theorem Std.ExtDTreeMap.isEmpty_iff_forall_not_mem {α β} [Ord α] [TransOrd α] {t : ExtDTreeMap α β} :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t := by
  rw [ExtDTreeMap.isEmpty_iff, ExtDTreeMap.eq_empty_iff_forall_not_mem]

theorem Std.ExtDTreeMap.isEmpty_eq_size_eq_zero {α β} [Ord α] [TransOrd α] {t : ExtDTreeMap α β} :
    t.isEmpty = (t.size == 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [ExtDTreeMap.isEmpty_iff, ExtDTreeMap.eq_empty_iff_size_eq_zero]
  simp

theorem Std.ExtDTreeMap.size_ne_zero_of_mem {α β} [Ord α] [TransOrd α]
    {t : ExtDTreeMap α β} {k : α} (hmem : k ∈ t) : t.size ≠ 0 := by
  have hne : t ≠ ∅ := by
    rw [Ne, ExtDTreeMap.eq_empty_iff_forall_not_mem]
    intro h; exact h _ hmem
  rw [Ne, ExtDTreeMap.eq_empty_iff_size_eq_zero] at hne
  exact hne

theorem Std.ExtDTreeMap.size_erase_mem
    {α β} [Ord α] [TransOrd α]
    {m : ExtDTreeMap α β} {k : α} (hk : k ∈ m) : size (erase m k) + 1 = size m := by
  have hne : m.size ≠ 0 := ExtDTreeMap.size_ne_zero_of_mem hk
  grind

theorem Std.ExtDTreeMap.get?_filter {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] {t : ExtDTreeMap α β}
    {k : α} {f : (a : α) → β a → Bool} : (t.filter f).get? k = Option.filter (f k) (t.get? k) := by
  cases t
  simp only [ExtDTreeMap.get?, ExtDTreeMap.filter, ExtDTreeMap.lift]
  simp only [Quotient.lift, Quotient.mk]
  apply DTreeMap.get?_filter

theorem Std.HashMap.size_zero_iff_forall_not_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : HashMap α β} : m.size = 0 ↔ ∀ x, x ∉ m :=
  Std.DHashMap.size_zero_iff_forall_not_mem

theorem Std.HashMap.size_ne_zero_iff_exists_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : HashMap α β} :
    m.size ≠ 0 ↔ ∃ (x : α), x ∈ m :=
  Std.DHashMap.size_ne_zero_iff_exists_mem

theorem Std.HashMap.size_gt_zero_iff_exists_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : HashMap α β} :
    m.size > 0 ↔ ∃ (x : α), x ∈ m :=
  Std.DHashMap.size_gt_zero_iff_exists_mem

theorem Std.HashMap.size_erase_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : HashMap α β} {k : α} (hk : k ∈ m) : size (erase m k) + 1 = size m := by
  have hnz := HashMap.size_gt_zero_iff_exists_mem.mpr ⟨_, hk⟩
  grind

theorem Std.TreeMap.size_ne_zero_of_mem {α β} {cmp : α → α → Ordering} [TransCmp cmp]
    {t : TreeMap α β cmp} {k : α} (hmem : k ∈ t) : t.size ≠ 0 := by
  have hne := TreeMap.isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨_, hmem⟩
  rw [TreeMap.isEmpty_eq_size_eq_zero] at hne
  simp_all

theorem Std.TreeMap.size_erase_mem
    {α β} {cmp : α → α → Ordering} [TransCmp cmp]
    {m : TreeMap α β cmp} {k : α} (hk : k ∈ m) :
    size (erase m k) + 1 = size m := by
  have hne : m.size ≠ 0 := TreeMap.size_ne_zero_of_mem hk
  grind

theorem Std.TreeMap.getElem?_filter {α β} [Ord α] [LawfulEqOrd α] [TransOrd α] {t : TreeMap α β}
    {k : α} {f : α → β → Bool} : (t.filter f)[k]? = Option.filter (f k) (t.get? k) := by
  cases t
  simp only [getElem?, TreeMap.get?, TreeMap.filter, DTreeMap.Const.get?_eq_get?]
  apply DTreeMap.get?_filter

theorem Std.ExtHashMap.size_ne_zero_of_mem {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {t : ExtHashMap α β} {k : α} (hmem : k ∈ t) : t.size ≠ 0 :=
  Std.ExtDHashMap.size_ne_zero_of_mem hmem

theorem Std.ExtHashMap.size_erase_mem
    {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : ExtHashMap α β} {k : α} (hk : k ∈ m) :
    size (erase m k) + 1 = size m := by
  have hne : m.size ≠ 0 := ExtHashMap.size_ne_zero_of_mem hk
  grind

theorem Std.ExtTreeMap.isEmpty_iff_forall_not_mem {α β} [Ord α] [TransOrd α] {t : ExtTreeMap α β} :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t := by
  rw [ExtTreeMap.isEmpty_iff, ExtTreeMap.eq_empty_iff_forall_not_mem]

theorem Std.ExtTreeMap.isEmpty_eq_size_eq_zero {α β} [Ord α] [TransOrd α] {t : ExtTreeMap α β} :
    t.isEmpty = (t.size == 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [ExtTreeMap.isEmpty_iff, ExtTreeMap.eq_empty_iff_size_eq_zero]
  simp

theorem Std.ExtTreeMap.size_ne_zero_of_mem {α β} [Ord α] [TransOrd α]
    {t : ExtDTreeMap α β} {k : α} (hmem : k ∈ t) : t.size ≠ 0 := by
  have hne : t ≠ ∅ := by grind
  rw [Ne, ExtDTreeMap.eq_empty_iff_size_eq_zero] at hne
  exact hne

theorem Std.ExtTreeMap.size_erase_mem
    {α β} [Ord α] [TransOrd α]
    {m : ExtTreeMap α β} {k : α} (hk : k ∈ m) : size (erase m k) + 1 = size m := by
  have hne : m.size ≠ 0 := ExtDTreeMap.size_ne_zero_of_mem hk
  grind

theorem Std.ExtTreeMap.getElem?_filter  {α β} [Ord α] [TransOrd α] [LawfulEqOrd α] {t : ExtTreeMap α β}
    {k : α} {f : α → β → Bool} :
    (t.filter f)[k]? = Option.filter (f k) (t.get? k) := by
  cases t
  simp only [getElem?, ExtTreeMap.filter, ExtTreeMap.get?, ExtDTreeMap.Const.get?_eq_get?]
  apply ExtDTreeMap.get?_filter

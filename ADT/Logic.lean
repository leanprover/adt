/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

/-!
# Extra logical theorems
-/

theorem iff_exists_of_forall_iff {α} {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
  (∃ x, p x) ↔ (∃ x, q x) := by simp [h]

theorem iff_forall_of_forall_iff {α} {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
  (∀ x, p x) ↔ (∀ x, q x) := by simp [h]

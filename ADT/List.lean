/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

/-!
# Additional theorems about lists
-/

open Classical in
def List.SubPerm {α} (l₁ l₂ : List α) := ∀ ⦃a : α⦄, l₁.count a ≤ l₂.count a

theorem List.length_eq_of_perm {α} {l₁ l₂ : List α}
    (hperm : l₁.Perm l₂) : l₁.length = l₂.length := by induction hperm <;> simp [*]

theorem List.nodup_count_le_one {α} [BEq α] [LawfulBEq α] {l : List α} {x : α}
    (hnd : l.Nodup) : l.count x ≤ 1 := by
  induction l
  case nil => simp
  case cons head tail IH =>
    rw [List.nodup_cons] at hnd
    rw [List.count_cons]
    cases heq : head == x
    case false => exact IH hnd.right
    case true =>
      have heq : head = x := by simp_all
      cases heq
      have hz : count x tail = 0 := List.count_eq_zero.mpr hnd.left
      simp [*]

theorem List.mem_nodup_iff_count_eq_one {α} [BEq α] [LawfulBEq α] {l : List α} {x : α}
    (hnd : l.Nodup) : x ∈ l ↔ l.count x = 1 := by
  have hle := Nat.le_one_iff_eq_zero_or_eq_one.mp (nodup_count_le_one (x:=x) hnd)
  have hiff := List.count_eq_zero (a:=x) (l:=l)
  cases hle <;> simp_all

theorem List.nodup_mem_eq_iff_count_eq {α} [BEq α] [LawfulBEq α] {l₁ l₂ : List α} {x : α}
    (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup) : (x ∈ l₁ ↔ x ∈ l₂) ↔ (l₁.count x = l₂.count x) := by
  have h₁ := mem_nodup_iff_count_eq_one (x:=x) hnd₁
  have h₁' := List.count_eq_zero (l:=l₁) (a:=x)
  have h₂ := mem_nodup_iff_count_eq_one (x:=x) hnd₂
  have h₂' := List.count_eq_zero (l:=l₂) (a:=x)
  by_cases x ∈ l₁ <;> by_cases x ∈ l₂ <;> simp_all

open Classical in
theorem List.nodup_subPerm_iff_subset {α} {l₁ l₂ : List α}
    (hnd₁ : Nodup l₁) (hnd₂ : Nodup l₂) : l₁.SubPerm l₂ ↔ l₁ ⊆ l₂ := by
  simp only [SubPerm, List.subset_def,
             mem_nodup_iff_count_eq_one hnd₁, mem_nodup_iff_count_eq_one hnd₂]
  grind

open Classical in
theorem List.SubPerm_of_nodup_subset {α} {l₁ l₂ : List α}
    (hnd : Nodup l₁) (hsub : l₁ ⊆ l₂) : l₁.SubPerm l₂ := by
  simp only [List.subset_def, mem_nodup_iff_count_eq_one hnd] at hsub
  grind [SubPerm, List.count_pos_iff]

open Classical in
theorem List.nodup_perm_iff_equiv {α} {l₁ l₂ : List α}
    (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup) :
  l₁.Perm l₂ ↔ (∀ x, x ∈ l₁ ↔ x ∈ l₂) := by
  let instBEq : BEq α := BEq.mk (fun x y => decide (x = y))
  have : LawfulBEq α := { rfl := by simp, eq_of_beq := by simp }
  simp [perm_iff_count, nodup_mem_eq_iff_count_eq hnd₁ hnd₂]

theorem List.mem_iff_exists_append {α} {l : List α} {x : α} :
    x ∈ l ↔ ∃ (l₁ l₂ : List α), l = l₁ ++ (x :: l₂) := by
  induction l
  case nil => simp
  case cons a as IH =>
    simp only [mem_cons]; apply Iff.intro
    case mp =>
      intro h; cases h
      case inl heq =>
        cases heq; exists .nil, as
      case inr hmem =>
        have ⟨l₁, l₂, h⟩ := IH.mp hmem
        exists a :: l₁, l₂; simp [h]
    case mpr =>
      intro ⟨l₁, l₂, h⟩; cases l₁
      case nil => simp_all
      case cons b bs =>
        simp only [cons_append, cons.injEq] at h
        apply Or.inr (IH.mpr ⟨_, _, h.right⟩)

open Classical in
theorem List.subperm_iff {α} {l₁ l₂ : List α} :
    l₁.SubPerm l₂ ↔ ∃ l₃, l₁.Sublist l₃ ∧ l₂.Perm l₃ := by
  simp only [SubPerm]; apply Iff.intro
  case mp =>
    generalize h : l₁.length = n; induction n generalizing l₁ l₂
    case zero =>
      rw [List.length_eq_zero_iff] at h; cases h
      intro _; exists l₂; simp
    case succ n IH =>
      cases l₁; case nil => simp at h
      case cons x xs =>
        simp only [length_cons, Nat.add_right_cancel_iff] at h
        intro hc
        have hx : x ∈ l₂ := by
          have hcx := @hc x
          apply count_pos_iff.mp; grind
        have ⟨l₂₁, l₂₂, h⟩ := List.mem_iff_exists_append.mp hx
        cases h
        have hp : ∀ x, count x xs ≤ count x (l₂₁ ++ l₂₂) := by
          intro x; rw [count_append]
          simp only [count_append, count_cons] at hc
          have hsubx := @hc x; omega
        have ⟨l₃, hsub, hperm⟩ := IH h hp
        exists x :: l₃; grind
  case mpr => grind

theorem List.perm_iff_length_eq_andsubPerm {α} {l₁ l₂ : List α} :
    l₁.Perm l₂ ↔ l₁.length = l₂.length ∧ l₁.SubPerm l₂ := by
  rw [List.subperm_iff]; apply Iff.intro
  case mp =>
    intro h; apply And.intro
    case left => apply List.length_eq_of_perm h
    case right => exists l₁; simp [h.symm]
  case mpr =>
    intro ⟨hl, l₃, hsub, hperm⟩
    apply Perm.trans _ hperm.symm
    rw [length_eq_of_perm hperm] at hl
    cases List.Sublist.eq_of_length hsub hl
    apply Perm.refl

theorem List.length_le_of_subPerm {α} {l₁ l₂ : List α}
    (hsub : l₁.SubPerm l₂) : l₁.length ≤ l₂.length := by
  have ⟨l, hsub, hperm⟩ := List.subperm_iff.mp hsub
  rw [length_eq_of_perm hperm]
  apply List.Sublist.length_le hsub

open Classical in
theorem List.length_le_of_subset {α} {l₁ l₂ : List α}
    (hnd : l₁.Nodup) (hsub : l₁ ⊆ l₂) : l₁.length ≤ l₂.length := by
  apply length_le_of_subPerm
  apply SubPerm_of_nodup_subset hnd hsub

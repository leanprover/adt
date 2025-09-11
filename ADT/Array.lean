/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

/-!
# Additional lemmas for arrays
-/

theorem Array.push_ind {α : Type u} {motive : Array α → Prop}
  (base : motive #[]) (ind : ∀ (head : Array α) (tail : α), motive head → motive (head.push tail)) :
  ∀ (t : Array α), motive t := by
  intro t; generalize hsz : t.size = tsz; revert t
  induction tsz
  case zero =>
    intro t ht₀; rw [Array.size_eq_zero_iff] at ht₀
    rw [ht₀]; exact base
  case succ tsz IH =>
    intro t hts
    have ts_ne_0 : t.size ≠ 0 := by rw [hts]; simp
    have ⟨head, tail, hpush⟩ := Array.eq_push_of_size_ne_zero ts_ne_0
    rw [hpush]; apply ind; apply IH
    rw [hpush, Array.size_push] at hts; simp_all

theorem Array.forall_nat_lt_size_eq
  {α} (xs : Array α) (p : α → Prop) :
  (∀ (i : Nat) (h : i < xs.size), p xs[i]) ↔ (∀ x ∈ xs, p x) := by
  apply Iff.intro <;> intro h
  case mp =>
    intro x hx
    have ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hx
    rw [← heq]; apply h
  case mpr => intro i _; apply h; simp

theorem Array.forall_nat_lt_size_push
  {α} (xs : Array α) (x : α) (p : α → Prop) :
  (∀ (i : Nat) (h : i < (xs.push x).size), p (xs.push x)[i]) ↔
    (∀ (i : Nat) (h : i < xs.size), p xs[i]) ∧ p x := by
  simp only [Array.size_push, Nat.forall_lt_succ_right']
  conv => enter [1, 1, m, h]; simp [Array.getElem_push, h]
  simp

theorem Array.skolemizeFinD {α} {n : Nat} (p : Fin n → α → Prop)
  (h : ∀ (i : Fin n), ∃ (x : α), p i x) :
  ∃ (xs : Array α) (heq : xs.size = n), ∀ (i : Fin n), p i xs[i.val] := by
  induction n
  case zero => exists #[]; exists rfl; intro i; cases i <;> contradiction
  case succ n IH =>
    rw [Fin.forall_fin_succ] at h
    have ⟨⟨head, hhead⟩, hptail⟩ := h
    have ⟨tail, heq, htail⟩ := IH (fun i x => p i.succ x) hptail
    exists #[head] ++ tail
    exists (by simp [heq, Nat.add_comm 1 n])
    rw [Fin.forall_fin_succ]
    apply And.intro
    case left => simp [hhead]
    case right => intro i; simp [htail i]

theorem Array.skolemizeBoundedD {α} {n : Nat} (p : (i : Nat) → i < n → α → Prop)
  (h : ∀ (i : Nat) (h : i < n), ∃ (x : α), p i h x) :
  ∃ (xs : Array α) (heq : xs.size = n), ∀ (i : Nat) (h : i < n), p i h xs[i] := by
  let p' : Fin n → α → Prop := fun i x => p i.val i.isLt x
  have ⟨xs, heq, h'⟩ := Array.skolemizeFinD p' (fun ⟨i, hi⟩ => h i hi)
  exists xs; exists heq; intro i hi; exact h' ⟨i, hi⟩

def Array.getShl? {α} (xs : Array α) (i : Nat) (off : Nat) : Option α :=
  if i >= off then xs[i - off]? else .none

theorem Array.getShl?_eq_none_iff {α} {xs : Array α} {i : Nat} {off : Nat} :
  xs.getShl? i off = .none ↔ i < off ∨ i ≥ off + xs.size := by
  simp only [getShl?]; split
  case isTrue h => rw [Array.getElem?_eq_none_iff]; omega
  case isFalse h => simp [Nat.lt_of_not_ge h]

theorem Array.getShl?_eq_some_iff {α} {xs : Array α} {i : Nat} {off : Nat} :
  (∃ x, xs.getShl? i off = .some x) ↔ i ≥ off ∧ i < off + xs.size := by
  have h := Array.getShl?_eq_none_iff (xs:=xs) (i:=i) (off:=off)
  revert h; cases (xs.getShl? i off) <;> simp <;> omega

theorem Array.getShl?_isSome_iff {α} {xs : Array α} {i : Nat} {off : Nat} :
  (xs.getShl? i off).isSome ↔ i ≥ off ∧ i < off + xs.size := by
  rw [← Array.getShl?_eq_some_iff]
  cases xs.getShl? i off <;> simp

theorem Array.getShl?_push {α} {xs : Array α} {x : α} {i : Nat} {off : Nat} :
  (xs.push x).getShl? i off = if i = off + xs.size then .some x else xs.getShl? i off := by
  simp only [getShl?]; split
  case isTrue h =>
    split <;> rw [Array.getElem?_push]
    case isTrue hi => cases hi; simp
    case isFalse hi =>
      have hi' : i - off ≠ xs.size := by omega
      simp [hi']
  case isFalse h =>
    have hi : i ≠ off + xs.size := by omega
    simp [hi]

theorem Array.size_singleton {α} {x : α} : #[x].size = 1 := by
  rfl

theorem Array.modify_const_eq_set {α} {xs : Array α} {i : Nat} {val : α} :
  xs.modify i (fun _ => val) = if h : i < xs.size then xs.set i val else xs := by
  split
  case isTrue hlt =>
    ext
    case h₁ => simp
    case h₂ j hj _ =>
      simp only [Array.size_modify] at hj
      simp only [Array.getElem_modify]; split
      case isTrue heq => cases heq; simp
      case isFalse hne => simp [Array.getElem_set, hne]
  case isFalse hge =>
    ext
    case h₁ => simp
    case h₂ j _ hj =>
      have : i ≠ j := by omega
      simp [Array.getElem_modify, *]

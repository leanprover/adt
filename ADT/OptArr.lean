/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import ADT.Array

/-!
# Array of `Option`

This file explores one way of interpreting an `Array (Option α)`:
vieweing it as a map from natural numbers to elements of `α`.

If the `k`-th entry of the array is `.none`, it means that
the key `k` is not present in the map. If the `k`-th entry of the
array is `.some v`, it means that the key `k` is present in the map
and it corresponds to the value `v`.
-/

def OptArr (α : Type) := Array (Option α)

def OptArr.emptyWithCapacity {α} (capacity : Nat := 0) : OptArr α := Array.emptyWithCapacity capacity

def OptArr.get? {α} (a : OptArr α) (i : Nat) := (getElem? (coll:=Array _) a i).join

def OptArr.containsIdx {α} (a : OptArr α) (i : Nat) := (a.get? i).isSome

instance {α} : Membership Nat (OptArr α) where
  mem a i := OptArr.containsIdx a i

theorem OptArr.containsIdx_iff_mem {α} {a : OptArr α} {i : Nat} : a.containsIdx i ↔ i ∈ a := by simp [Membership.mem]

theorem OptArr.lt_of_containsIdx {α} {a : OptArr α} {i : Nat} (h : a.containsIdx i) : i < a.size := by
  simp only [containsIdx, get?] at h; cases heq : (getElem? (coll:=Array _) a i)
  case none => rw [heq] at h; simp at h
  case some => apply (Array.getElem?_eq_some_iff.mp heq).choose

theorem OptArr.isSome_array_getElem_of_containsIdx {α} {a : OptArr α} {i : Nat} (h : a.containsIdx i) :
  (getElem (coll:=Array _) a i (a.lt_of_containsIdx h)).isSome := by
  simp only [containsIdx, get?] at h
  rw [Array.getElem?_eq_getElem (a.lt_of_containsIdx h)] at h
  exact h

def OptArr.get {α} (a : OptArr α) (i : Nat) (h : a.containsIdx i) :=
  (getElem (coll:=Array _) a i (a.lt_of_containsIdx h)).get (a.isSome_array_getElem_of_containsIdx h)

instance {α} : GetElem? (OptArr α) Nat α fun xs i => i ∈ xs where
  getElem := OptArr.get
  getElem? := OptArr.get?

theorem OptArr.containsIdx_of_isSome_getElem? {α} {xs : OptArr α} {i : Nat} (h : xs[i]?.isSome) : xs.containsIdx i := h

def OptArr.insert {α} (a : OptArr α) (key : Nat) (val : α) : OptArr α :=
  if key < a.size then
    a.modify key (fun _ => val)
  else
    (HAppend.hAppend (α:=Array _) a (Array.replicate (key - a.size) .none)).push (.some val)

def OptArr.erase {α} (a : OptArr α) (key : Nat) : OptArr α :=
  a.modify key (fun _ => .none)

def OptArr.size {α} (a : OptArr α) : Nat := Array.countP (fun x => x.isSome) a

def OptArr.isEmpty {α} (a : OptArr α) : Bool := a.size = 0

theorem OptArr.mem_iff_isSome_array_getElem {α} {xs : OptArr α} {i : Nat} : i ∈ xs ↔
  ∃ (h : i < Array.size xs), (getElem (coll:=Array _) xs i h).isSome := by
  apply Iff.intro <;> intro h
  case mp =>
    exists lt_of_containsIdx h
    apply isSome_array_getElem_of_containsIdx h
  case mpr =>
    have ⟨h, heq⟩ := h
    simp only [Membership.mem, containsIdx, get?]
    rw [Array.getElem?_eq_getElem h]; simp [heq]

theorem OptArr.mem_iff_isSome_getElem? {α} {xs : OptArr α} {i : Nat} : i ∈ xs ↔ xs[i]?.isSome := Iff.rfl

theorem OptArr.not_mem_iff_getElem?_eq_none {α} {xs : OptArr α} {i : Nat} : i ∉ xs ↔ xs[i]? = .none := by
  rw [mem_iff_isSome_getElem?]; simp

theorem OptArr.not_mem_empty {α} {i : Nat} : ¬ i ∈ (OptArr.emptyWithCapacity : OptArr α) := by
  simp [Membership.mem, emptyWithCapacity, containsIdx, get?]

theorem OptArr.getElem?_insert_self {α} {xs : OptArr α} {k : Nat} {v : α} :
  (xs.insert k v)[k]? = some v := by
  simp only [insert, getElem?]; simp only [get?]; split
  case isTrue hlt =>
    simp [Array.getElem?_modify, Array.getElem?_eq_getElem hlt]
  case isFalse hge =>
    have hsz : Array.size xs + (k - Array.size xs) = k := by omega
    simp only [Array.getElem?_push, Array.getElem?_append]
    simp [Array.size_append, Array.size_replicate, hsz]

theorem OptArr.getElem?_insert_ne {α} {xs : OptArr α} {k a : Nat} {v : α} (h : k ≠ a) :
  (xs.insert k v)[a]? = xs[a]? := by
  simp only [insert, getElem?]; simp only [get?]; split
  case isTrue hlt =>
    simp [Array.getElem?_modify, h]
  case isFalse hge =>
    have hsz : Array.size xs + (k - Array.size xs) = k := by omega
    simp only [Array.getElem?_push, Array.getElem?_append]
    simp only [Array.size_append, Array.size_replicate, hsz, h.symm, ite_false]
    split
    case isTrue hlt => rfl
    case isFalse hge =>
      have hge : a ≥ Array.size xs := by omega
      rw [Array.getElem?_eq_none hge]
      rw [Array.getElem?_replicate]
      split <;> simp

theorem OptArr.getElem?_erase_self {α} {xs : OptArr α} {k : Nat} :
  (xs.erase k)[k]? = .none := by
  simp only [erase, getElem?]
  simp only [get?, Array.getElem?_modify, ite_true]
  cases (getElem? (coll:=Array _) xs k) <;> rfl

theorem OptArr.getElem?_erase_ne {α} {xs : OptArr α} {k a : Nat} (hne : k ≠ a) :
  (xs.erase k)[a]? = xs[a]? := by
  simp only [erase, getElem?]
  simp [get?, Array.getElem?_modify, hne]

theorem OptArr.isEmpty_iff_size_eq_zero {α} {m : OptArr α} : m.isEmpty ↔ m.size = 0 := by
  simp [OptArr.isEmpty]

theorem OptArr.size_zero_iff_forall_not_mem {α} {m : OptArr α} : size m = 0 ↔ ∀ (x : Nat), x ∉ m := by
  simp only [size, Array.size_eq_zero_iff, OptArr.mem_iff_isSome_array_getElem,
             Array.countP_eq_size_filter, Array.filter_eq_empty_iff]
  apply Iff.intro <;> intro h
  case mp =>
    intro x ⟨hx, heq⟩
    have contra := h (getElem (coll:=Array _) m x hx) (by simp)
    contradiction
  case mpr =>
    intro a ha hsome
    have ⟨i, ilt, heq⟩ := Array.mem_iff_getElem.mp ha
    apply h i; exists ilt; simp [*]

theorem OptArr.get?_eq_some_get {α} {a : OptArr α} {k : Nat} (h : k ∈ a) :
  a[k]? = .some a[k] := by
  have ⟨h, hget⟩ := mem_iff_isSome_array_getElem.mp h
  simp only [getElem?, getElem]
  simp [get?, get, Array.getElem?_eq_getElem h]

theorem OptArr.size_erase_mem {α} {m : OptArr α} {k : Nat} : k ∈ m → size (erase m k) + 1 = size m := by
  intro hk; simp only [erase, size]
  have ⟨h, hget⟩ := mem_iff_isSome_array_getElem.mp hk
  have hcountnz : Array.countP (fun x => x.isSome) m > 0 := by
    apply Nat.ne_zero_iff_zero_lt.mp; intro h
    have h' := Array.countP_eq_zero.mp h
    have contra := h' (getElem (coll:=Array _) m k (by assumption)) (by simp)
    contradiction
  have hcount : Array.countP (fun x => x.isSome) m - 1 + 1 = Array.countP (fun x => x.isSome) m := by omega
  simp [Array.modify_const_eq_set, h, Array.countP_set, hget, hcount]

instance {α} : LawfulGetElem (OptArr α) Nat α (fun xs i => i ∈ xs) where
  getElem?_def := by
    intro c i _; split
    case isTrue => rw [OptArr.get?_eq_some_get]
    case isFalse h => apply OptArr.not_mem_iff_getElem?_eq_none.mp h
  getElem!_def := by
    intro _ c i; rfl

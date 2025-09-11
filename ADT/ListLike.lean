/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import ADT.Size
import ADT.Fold
open Lean Std

/-!
# `ToList` and related `Lawful` classes
-/

class ToList (γ : Type u) (α : Type v) where
  toList : γ → List α

instance {α} : ToList (List α) α where
  toList x := x

instance {α} : ToList (Array α) α where
  toList := Array.toList

instance {α β} [BEq α] [Hashable α] : ToList (DHashMap α β) (Sigma β) where
  toList := DHashMap.toList

instance {α β} [Ord α] : ToList (DTreeMap α β) (Sigma β) where
  toList := DTreeMap.toList

instance {α β} [BEq α] [Hashable α] : ToList (HashMap α β) (α × β) where
  toList := HashMap.toList

instance {α β} [Ord α] : ToList (TreeMap α β) (α × β) where
  toList := TreeMap.toList

instance {α} [BEq α] [Hashable α] : ToList (HashSet α) α where
  toList := HashSet.toList

instance {α} [Ord α] : ToList (TreeSet α) α where
  toList := TreeSet.toList

class LawfulSizeToList (γ : Type u) (α : Type v) [Size γ] [ToList γ α] where
  length_toList_eq_size {m : γ} : (ToList.toList (α:=α) m).length = Size.size m

class LawfulFoldlToList (γ : Type u) (α : Type v) [Foldl γ α] [ToList γ α] where
  foldl_eq_foldl_toList {m : γ} {β} {f : β → α → β} {init : β} : Foldl.foldl f init m = (ToList.toList m).foldl f init

class LawfulFoldrToList (γ : Type u) (α : Type v) [Foldr γ α] [ToList γ α] where
  foldr_eq_foldr_toList {m : γ} {β} {f : α → β → β} {init : β} : Foldr.foldr f init m = (ToList.toList m).foldr f init

class LawfulFoldlMToList (γ : Type u) (α : Type v) [FoldlM γ α] [ToList γ α]
  extends LawfulFoldlM γ α where
  foldlM_eq_foldlM_toList {m : γ} {β} {n} [Monad n] [LawfulMonad n] {f : β → α → n β} {init : β} : FoldlM.foldlM f init m = (ToList.toList m).foldlM f init

class LawfulFoldrMToList (γ : Type u) (α : Type v) [FoldrM γ α] [ToList γ α]
  extends LawfulFoldrM γ α where
  foldrM_eq_foldrM_toList {m : γ} {β} {n} [Monad n] [LawfulMonad n] {f : α → β → n β} {init : β} : FoldrM.foldrM f init m = (ToList.toList m).foldrM f init

instance {α} : LawfulSizeToList (List α) α where
  length_toList_eq_size := rfl

instance {α} : LawfulFoldlToList (List α) α where
  foldl_eq_foldl_toList := rfl

instance {α} : LawfulFoldrToList (List α) α where
  foldr_eq_foldr_toList := rfl

instance {α} : LawfulFoldlMToList (List α) α where
  foldlM_eq_foldlM_toList := rfl

instance {α} : LawfulFoldrMToList (List α) α where
  foldrM_eq_foldrM_toList := rfl

instance {α} : LawfulSizeToList (Array α) α where
  length_toList_eq_size := rfl

instance {α} : LawfulFoldlToList (Array α) α where
  foldl_eq_foldl_toList := by
    intros
    simp only [ToList.toList, Foldl.foldl, Array.foldl_toList]

instance {α} : LawfulFoldrToList (Array α) α where
  foldr_eq_foldr_toList := by
    intros
    simp only [ToList.toList, Foldr.foldr, Array.foldr_toList]

instance {α} : LawfulFoldlMToList (Array α) α where
  foldlM_eq_foldlM_toList := by
    intros
    simp only [ToList.toList, FoldlM.foldlM, Array.foldlM_toList]

instance {α} : LawfulFoldrMToList (Array α) α where
  foldrM_eq_foldrM_toList := by
    intros
    simp only [ToList.toList, FoldrM.foldrM, Array.foldrM_toList]

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulSizeToList (HashSet α) α where
  length_toList_eq_size := by
    intros
    simp only [ToList.toList, Size.size, HashSet.length_toList]

instance {α} [BEq α] [Hashable α] : LawfulFoldlToList (HashSet α) α where
  foldl_eq_foldl_toList := by
    intros
    simp only [ToList.toList, Foldl.foldl, HashSet.fold_eq_foldl_toList]

instance {α} [BEq α] [Hashable α] : LawfulFoldlMToList (HashSet α) α where
  foldlM_eq_foldlM_toList := by
    intros
    simp only [ToList.toList, FoldlM.foldlM, HashSet.foldM_eq_foldlM_toList]

instance {α} [Ord α] [TransOrd α] : LawfulSizeToList (TreeSet α) α where
  length_toList_eq_size := by
    intros
    simp only [ToList.toList, Size.size, TreeSet.length_toList]

instance {α} [Ord α] : LawfulFoldlToList (TreeSet α) α where
  foldl_eq_foldl_toList := by
    intros
    simp only [ToList.toList, Foldl.foldl, TreeSet.foldl_eq_foldl_toList]

instance {α} [Ord α] : LawfulFoldrToList (TreeSet α) α where
  foldr_eq_foldr_toList := by
    intros
    simp only [ToList.toList, Foldr.foldr, TreeSet.foldr_eq_foldr_toList]

instance {α} [Ord α] : LawfulFoldlMToList (TreeSet α) α where
  foldlM_eq_foldlM_toList := by
    intros
    simp only [ToList.toList, FoldlM.foldlM, TreeSet.foldlM_eq_foldlM_toList]

instance {α} [Ord α] : LawfulFoldrMToList (TreeSet α) α where
  foldrM_eq_foldrM_toList := by
    intros
    simp only [ToList.toList, FoldrM.foldrM, TreeSet.foldrM_eq_foldrM_toList]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulSizeToList (DHashMap α β) (Sigma β) where
  length_toList_eq_size := by
    intros
    simp only [ToList.toList, Size.size, DHashMap.length_toList]

instance {α β} [BEq α] [Hashable α] : LawfulFoldlToList (DHashMap α β) (Sigma β) where
  foldl_eq_foldl_toList := by
    intros
    simp only [ToList.toList, Foldl.foldl, DHashMap.fold_eq_foldl_toList]

instance {α β} [BEq α] [Hashable α] : LawfulFoldlMToList (DHashMap α β) (Sigma β) where
  foldlM_eq_foldlM_toList := by
    intros
    simp only [ToList.toList, FoldlM.foldlM, DHashMap.foldM_eq_foldlM_toList]

instance {α β} [Ord α] [TransOrd α] : LawfulSizeToList (DTreeMap α β) (Sigma β) where
  length_toList_eq_size := by
    intros
    simp only [ToList.toList, Size.size, DTreeMap.length_toList]

instance {α β} [Ord α] : LawfulFoldlToList (DTreeMap α β) (Sigma β) where
  foldl_eq_foldl_toList := by
    intros m β f init
    simp only [ToList.toList, Foldl.foldl, DTreeMap.foldl_eq_foldl_toList]

instance {α β} [Ord α] : LawfulFoldrToList (DTreeMap α β) (Sigma β) where
  foldr_eq_foldr_toList := by
    intros
    simp only [ToList.toList, Foldr.foldr, DTreeMap.foldr_eq_foldr_toList]

instance {α β} [Ord α] : LawfulFoldlMToList (DTreeMap α β) (Sigma β) where
  foldlM_eq_foldlM_toList := by
    intros
    simp only [ToList.toList, FoldlM.foldlM, DTreeMap.foldlM_eq_foldlM_toList]

instance {α β} [Ord α] : LawfulFoldrMToList (DTreeMap α β) (Sigma β) where
  foldrM_eq_foldrM_toList := by
    intros
    simp only [ToList.toList, FoldrM.foldrM, DTreeMap.foldrM_eq_foldrM_toList]

instance {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulSizeToList (HashMap α β) (α × β) where
  length_toList_eq_size := by
    intros
    simp only [ToList.toList, Size.size, HashMap.length_toList]

instance {α β} [BEq α] [Hashable α] : LawfulFoldlToList (HashMap α β) (α × β) where
  foldl_eq_foldl_toList := by
    intros
    simp only [ToList.toList, Foldl.foldl, HashMap.fold_eq_foldl_toList]

instance {α β} [BEq α] [Hashable α] : LawfulFoldlMToList (HashMap α β) (α × β) where
  foldlM_eq_foldlM_toList := by
    intros
    simp only [ToList.toList, FoldlM.foldlM, HashMap.foldM_eq_foldlM_toList]

instance {α β} [Ord α] [TransOrd α] : LawfulSizeToList (TreeMap α β) (α × β) where
  length_toList_eq_size := by
    intros
    simp only [ToList.toList, Size.size, TreeMap.length_toList]

instance {α β} [Ord α] : LawfulFoldlToList (TreeMap α β) (α × β) where
  foldl_eq_foldl_toList := by
    intros m β f init
    simp only [ToList.toList, Foldl.foldl, TreeMap.foldl_eq_foldl_toList]

instance {α β} [Ord α] : LawfulFoldrToList (TreeMap α β) (α × β) where
  foldr_eq_foldr_toList := by
    intros
    simp only [ToList.toList, Foldr.foldr, TreeMap.foldr_eq_foldr_toList]

instance {α β} [Ord α] : LawfulFoldlMToList (TreeMap α β) (α × β) where
  foldlM_eq_foldlM_toList := by
    intros
    simp only [ToList.toList, FoldlM.foldlM, TreeMap.foldlM_eq_foldlM_toList]

instance {α β} [Ord α] : LawfulFoldrMToList (TreeMap α β) (α × β) where
  foldrM_eq_foldrM_toList := by
    intros
    simp only [ToList.toList, FoldrM.foldrM, TreeMap.foldrM_eq_foldrM_toList]

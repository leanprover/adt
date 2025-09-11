/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

import Lean
import Std.Data
open Std

class Foldl (γ : Type _) (α : Type _) where
  foldl {β} : (β → α → β) → β → γ → β

class FoldlM (γ : Type _) (α : Type _) extends Foldl γ α where
  foldlM {m} [Monad m] {β} : (β → α → m β) → β → γ → m β

class LawfulFoldlM (γ α) [FoldlM γ α] where
  foldl_eq_foldlM {β} {f : β → α → β} {b : β} {l : γ} :
  Foldl.foldl f b l = (FoldlM.foldlM (m:=Id) (fun x1 x2 => pure (f x1 x2)) b l).run

class Foldr (γ : Type _) (α : Type _) where
  foldr {β} : (α → β → β) → β → γ → β

class FoldrM (γ : Type _) (α : Type _) extends Foldr γ α where
  foldrM {m} [Monad m] {β} : (α → β → m β) → β → γ → m β

class LawfulFoldrM (γ α) [FoldrM γ α] where
  foldr_eq_foldrM {β} {f : α → β → β} {b : β} {l : γ} :
  Foldr.foldr f b l = (FoldrM.foldrM (m:=Id) (fun x1 x2 => pure (f x1 x2)) b l).run

instance {α} : FoldlM (List α) α where
  foldl := List.foldl
  foldlM := List.foldlM

instance {α} : LawfulFoldlM (List α) α where
  foldl_eq_foldlM := List.foldl_eq_foldlM

instance {α} : FoldrM (List α) α where
  foldr := List.foldr
  foldrM := List.foldrM

instance {α} : LawfulFoldrM (List α) α where
  foldr_eq_foldrM := List.foldr_eq_foldrM

instance {α} : FoldlM (Array α) α where
  foldl := Array.foldl
  foldlM := Array.foldlM

instance {α} : LawfulFoldlM (Array α) α where
  foldl_eq_foldlM := Array.foldl_eq_foldlM

instance {α} : FoldrM (Array α) α where
  foldr := Array.foldr
  foldrM := Array.foldrM

instance {α} : LawfulFoldrM (Array α) α where
  foldr_eq_foldrM := Array.foldr_eq_foldrM

instance {α} [BEq α] [Hashable α] : FoldlM (HashSet α) α where
  foldl := HashSet.fold
  foldlM := HashSet.foldM

instance {α} [BEq α] [Hashable α] : LawfulFoldlM (HashSet α) α where
  foldl_eq_foldlM := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [HashSet.fold_eq_foldl_toList, HashSet.foldM_eq_foldlM_toList]
    apply List.foldl_eq_foldlM

instance {α} [Ord α] : FoldlM (TreeSet α) α where
  foldl := TreeSet.foldl
  foldlM := TreeSet.foldlM

instance {α} [Ord α] : LawfulFoldlM (TreeSet α) α where
  foldl_eq_foldlM := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [TreeSet.foldl_eq_foldl_toList, TreeSet.foldlM_eq_foldlM_toList]
    apply List.foldl_eq_foldlM

instance {α} [Ord α] : FoldrM (TreeSet α) α where
  foldr := TreeSet.foldr
  foldrM := TreeSet.foldrM

instance {α} [Ord α] : LawfulFoldrM (TreeSet α) α where
  foldr_eq_foldrM := by
    intros; simp only [Foldr.foldr, FoldrM.foldrM]
    rw [TreeSet.foldr_eq_foldr_toList, TreeSet.foldrM_eq_foldrM_toList]
    apply List.foldr_eq_foldrM

instance {α β} [BEq α] [Hashable α] : FoldlM (DHashMap α β) (Sigma β) where
  foldl f := DHashMap.fold (fun s a b => f s ⟨a, b⟩)
  foldlM f := DHashMap.foldM (fun s a b => f s ⟨a, b⟩)

instance {α β} [BEq α] [Hashable α] : LawfulFoldlM (DHashMap α β) (Sigma β) where
  foldl_eq_foldlM := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [DHashMap.fold_eq_foldl_toList, DHashMap.foldM_eq_foldlM_toList]
    apply List.foldl_eq_foldlM

instance {α β} [Ord α] : FoldlM (DTreeMap α β) (Sigma β) where
  foldl f := DTreeMap.foldl (fun s a b => f s ⟨a, b⟩)
  foldlM f := DTreeMap.foldlM (fun s a b => f s ⟨a, b⟩)

instance {α β} [Ord α] : LawfulFoldlM (DTreeMap α β) (Sigma β) where
  foldl_eq_foldlM := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [DTreeMap.foldl_eq_foldl_toList, DTreeMap.foldlM_eq_foldlM_toList]
    apply List.foldl_eq_foldlM

instance {α β} [Ord α] : FoldrM (DTreeMap α β) (Sigma β) where
  foldr f := DTreeMap.foldr (fun a b s => f ⟨a, b⟩ s)
  foldrM f := DTreeMap.foldrM (fun a b s => f ⟨a, b⟩ s)

instance {α β} [Ord α] : LawfulFoldrM (DTreeMap α β) (Sigma β) where
  foldr_eq_foldrM := by
    intros; simp only [Foldr.foldr, FoldrM.foldrM]
    rw [DTreeMap.foldr_eq_foldr_toList, DTreeMap.foldrM_eq_foldrM_toList]
    apply List.foldr_eq_foldrM

instance {α β} [BEq α] [Hashable α] : FoldlM (HashMap α β) (α × β) where
  foldl f := HashMap.fold (fun s a b => f s (a, b))
  foldlM f := HashMap.foldM (fun s a b => f s (a, b))

instance {α β} [BEq α] [Hashable α] : LawfulFoldlM (HashMap α β) (α × β) where
  foldl_eq_foldlM := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [HashMap.fold_eq_foldl_toList, HashMap.foldM_eq_foldlM_toList]
    apply List.foldl_eq_foldlM

instance {α β} [Ord α] : FoldlM (TreeMap α β) (α × β) where
  foldl f := TreeMap.foldl (fun s a b => f s (a, b))
  foldlM f := TreeMap.foldlM (fun s a b => f s (a, b))

instance {α β} [Ord α] : LawfulFoldlM (TreeMap α β) (α × β) where
  foldl_eq_foldlM := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [TreeMap.foldl_eq_foldl_toList, TreeMap.foldlM_eq_foldlM_toList]
    apply List.foldl_eq_foldlM

instance {α β} [Ord α] : FoldrM (TreeMap α β) (α × β) where
  foldr f := TreeMap.foldr (fun a b s => f (a, b) s)
  foldrM f := TreeMap.foldrM (fun a b s => f (a, b) s)

instance {α β} [Ord α] : LawfulFoldrM (TreeMap α β) (α × β) where
  foldr_eq_foldrM := by
    intros; simp only [Foldr.foldr, FoldrM.foldrM]
    rw [TreeMap.foldr_eq_foldr_toList, TreeMap.foldrM_eq_foldrM_toList]
    apply List.foldr_eq_foldrM

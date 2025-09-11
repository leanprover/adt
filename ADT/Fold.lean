/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import Std.Data
open Std

/-!
# Fold-related operations

This file defines typeclasses for `Fold`-related operations and
their `Lawful` typeclasses.
-/

class Foldl (γ : Type _) (α : Type _) where
  foldl {β} : (β → α → β) → β → γ → β

class FoldlM (γ : Type _) (α : Type _) extends Foldl γ α where
  foldlM {m} [Monad m] {β} : (β → α → m β) → β → γ → m β

class LawfulFoldlM (γ α) [FoldlM γ α] where
  foldlM_pure {m} [Monad m] [LawfulMonad m] {β} {f : β → α → β} {b : β} {l : γ} :
    FoldlM.foldlM (m:=m) (fun x1 x2 => pure (f x1 x2)) b l = pure (Foldl.foldl f b l)

class LawfulAppendFoldl (γ α) [Foldl γ α] [Append γ] where
  foldl_append {β} {f : β → α → β} {b : β} {l l' : γ} :
    Foldl.foldl f b (l ++ l') = Foldl.foldl f (Foldl.foldl f b l) l'

class LawfulAppendFoldlM (γ : Type u) (α : Type v) [FoldlM γ α] [Append γ] extends LawfulFoldlM γ α where
  foldlM_append {m : Type w → Type x} [Monad m] [LawfulMonad m] {β} {f : β → α → m β} {b : β} {l l' : γ} :
    FoldlM.foldlM f b (l ++ l') = FoldlM.foldlM f b l >>= fun b' => FoldlM.foldlM f b' l'

class Foldr (γ : Type _) (α : Type _) where
  foldr {β} : (α → β → β) → β → γ → β

class FoldrM (γ : Type _) (α : Type _) extends Foldr γ α where
  foldrM {m} [Monad m] {β} : (α → β → m β) → β → γ → m β

class LawfulFoldrM (γ α) [FoldrM γ α] where
  foldrM_pure {m} [Monad m] [LawfulMonad m] {β} {f : α → β → β} {b : β} {l : γ} :
    FoldrM.foldrM (m:=m) (fun x1 x2 => pure (f x1 x2)) b l = pure (Foldr.foldr f b l)

class LawfulAppendFoldr (γ α) [Foldr γ α] [Append γ] where
  foldr_append {β} {f : α → β → β} {b : β} {l l' : γ} :
    Foldr.foldr f b (l ++ l') = Foldr.foldr f (Foldr.foldr f b l') l

class LawfulAppendFoldrM (γ : Type u) (α : Type v) [FoldrM γ α] [Append γ] extends LawfulFoldrM γ α where
  foldrM_append {m : Type w → Type x} [Monad m] [LawfulMonad m] {β} {f : α → β → m β} {b : β} {l l' : γ} :
    FoldrM.foldrM f b (l ++ l') = FoldrM.foldrM f b l' >>= fun b' => FoldrM.foldrM f b' l

theorem LawfulFoldlM.foldl_eq_foldlM {γ α} [FoldlM γ α] [LawfulFoldlM γ α] {β} {f : β → α → β} {b : β} {l : γ} :
  Foldl.foldl f b l = FoldlM.foldlM (m:=Id) (fun x1 x2 => pure (f x1 x2)) b l := by
  rw [foldlM_pure]; rfl

theorem LawfulFoldrM.foldr_eq_foldrM {γ α} [FoldrM γ α] [LawfulFoldrM γ α] {β} {f : α → β → β} {b : β} {l : γ} :
  Foldr.foldr f b l = FoldrM.foldrM (m:=Id) (fun x1 x2 => pure (f x1 x2)) b l := by
  rw [foldrM_pure]; rfl

instance {γ α} [FoldlM γ α] [Append γ] [LawfulAppendFoldlM.{u, v, w, w} γ α] : LawfulAppendFoldl γ α where
  foldl_append := by
    intros
    simp only [LawfulFoldlM.foldl_eq_foldlM]
    apply LawfulAppendFoldlM.foldlM_append

instance {γ α} [FoldrM γ α] [Append γ] [LawfulAppendFoldrM.{u, v, w, w} γ α] : LawfulAppendFoldr γ α where
  foldr_append := by
    intros
    simp only [LawfulFoldrM.foldr_eq_foldrM]
    apply LawfulAppendFoldrM.foldrM_append

instance {α} : FoldlM (List α) α where
  foldl := List.foldl
  foldlM := List.foldlM

instance {α} : LawfulAppendFoldlM (List α) α where
  foldlM_pure := List.foldlM_pure
  foldlM_append := List.foldlM_append

instance {α} : FoldrM (List α) α where
  foldr := List.foldr
  foldrM := List.foldrM

instance {α} : LawfulFoldrM (List α) α where
  foldrM_pure := List.foldrM_pure

instance {α} : FoldlM (Array α) α where
  foldl := Array.foldl
  foldlM := Array.foldlM

instance {α} : LawfulAppendFoldlM (Array α) α where
  foldlM_pure := Array.foldlM_pure
  foldlM_append := Array.foldlM_append

instance {α} : FoldrM (Array α) α where
  foldr := Array.foldr
  foldrM := Array.foldrM

instance {α} : LawfulAppendFoldrM (Array α) α where
  foldrM_pure := Array.foldrM_pure
  foldrM_append := Array.foldrM_append

instance {α} [BEq α] [Hashable α] : FoldlM (HashSet α) α where
  foldl := HashSet.fold
  foldlM := HashSet.foldM

instance {α} [BEq α] [Hashable α] : LawfulFoldlM (HashSet α) α where
  foldlM_pure := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [HashSet.fold_eq_foldl_toList, HashSet.foldM_eq_foldlM_toList]
    apply List.foldlM_pure

instance {α} [Ord α] : FoldlM (TreeSet α) α where
  foldl := TreeSet.foldl
  foldlM := TreeSet.foldlM

instance {α} [Ord α] : LawfulFoldlM (TreeSet α) α where
  foldlM_pure := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [TreeSet.foldl_eq_foldl_toList, TreeSet.foldlM_eq_foldlM_toList]
    apply List.foldlM_pure

instance {α} [Ord α] : FoldrM (TreeSet α) α where
  foldr := TreeSet.foldr
  foldrM := TreeSet.foldrM

instance {α} [Ord α] : LawfulFoldrM (TreeSet α) α where
  foldrM_pure := by
    intros; simp only [Foldr.foldr, FoldrM.foldrM]
    rw [TreeSet.foldr_eq_foldr_toList, TreeSet.foldrM_eq_foldrM_toList]
    apply List.foldrM_pure

instance {α β} [BEq α] [Hashable α] : FoldlM (DHashMap α β) (Sigma β) where
  foldl f := DHashMap.fold (fun s a b => f s ⟨a, b⟩)
  foldlM f := DHashMap.foldM (fun s a b => f s ⟨a, b⟩)

instance {α β} [BEq α] [Hashable α] : LawfulFoldlM (DHashMap α β) (Sigma β) where
  foldlM_pure := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [DHashMap.fold_eq_foldl_toList, DHashMap.foldM_eq_foldlM_toList]
    apply List.foldlM_pure

instance {α β} [Ord α] : FoldlM (DTreeMap α β) (Sigma β) where
  foldl f := DTreeMap.foldl (fun s a b => f s ⟨a, b⟩)
  foldlM f := DTreeMap.foldlM (fun s a b => f s ⟨a, b⟩)

instance {α β} [Ord α] : LawfulFoldlM (DTreeMap α β) (Sigma β) where
  foldlM_pure := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [DTreeMap.foldl_eq_foldl_toList, DTreeMap.foldlM_eq_foldlM_toList]
    apply List.foldlM_pure

instance {α β} [Ord α] : FoldrM (DTreeMap α β) (Sigma β) where
  foldr f := DTreeMap.foldr (fun a b s => f ⟨a, b⟩ s)
  foldrM f := DTreeMap.foldrM (fun a b s => f ⟨a, b⟩ s)

instance {α β} [Ord α] : LawfulFoldrM (DTreeMap α β) (Sigma β) where
  foldrM_pure := by
    intros; simp only [Foldr.foldr, FoldrM.foldrM]
    rw [DTreeMap.foldr_eq_foldr_toList, DTreeMap.foldrM_eq_foldrM_toList]
    apply List.foldrM_pure

instance {α β} [BEq α] [Hashable α] : FoldlM (HashMap α β) (α × β) where
  foldl f := HashMap.fold (fun s a b => f s (a, b))
  foldlM f := HashMap.foldM (fun s a b => f s (a, b))

instance {α β} [BEq α] [Hashable α] : LawfulFoldlM (HashMap α β) (α × β) where
  foldlM_pure := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [HashMap.fold_eq_foldl_toList, HashMap.foldM_eq_foldlM_toList]
    apply List.foldlM_pure

instance {α β} [Ord α] : FoldlM (TreeMap α β) (α × β) where
  foldl f := TreeMap.foldl (fun s a b => f s (a, b))
  foldlM f := TreeMap.foldlM (fun s a b => f s (a, b))

instance {α β} [Ord α] : LawfulFoldlM (TreeMap α β) (α × β) where
  foldlM_pure := by
    intros; simp only [Foldl.foldl, FoldlM.foldlM]
    rw [TreeMap.foldl_eq_foldl_toList, TreeMap.foldlM_eq_foldlM_toList]
    apply List.foldlM_pure

instance {α β} [Ord α] : FoldrM (TreeMap α β) (α × β) where
  foldr f := TreeMap.foldr (fun a b s => f (a, b) s)
  foldrM f := TreeMap.foldrM (fun a b s => f (a, b) s)

instance {α β} [Ord α] : LawfulFoldrM (TreeMap α β) (α × β) where
  foldrM_pure := by
    intros; simp only [Foldr.foldr, FoldrM.foldrM]
    rw [TreeMap.foldr_eq_foldr_toList, TreeMap.foldrM_eq_foldrM_toList]
    apply List.foldrM_pure

/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean
import Std.Data

/-!
# Dependently typed functor

This file defines a dependently typed version of the `Functor` typeclass.
-/

open Lean Std

class DFunctor {α} (f : (α → Type u) → Type v) where
  /--
  Applies a function inside a dependently typed functor.

  When mapping a constant function, use `DFunctor.mapConst` instead, because it may be more
  efficient.
  -/
  map : {β γ : α → Type u} → ((a : α) → β a → γ a) → f β → f γ
  /--
  Mapping a constant function.

  Given `a : α` and `v : f α`, `mapConst a v` is equivalent to `DFunctor.map (fun x _ => a x) v`.
  For some functors, this can be implemented more efficiently; for all other functors, the default
  implementation may be used.
  -/
  mapConst : {β γ : α → Type u} → ((a : α) → γ a) → f β → f γ
    := fun a => map (fun x _ => a x)

@[inherit_doc] notation:100 f " <$>ᵈ " " [ " t " ] " x => DFunctor.map (f:=t) f x

class LawfulDFunctor {α} (f : (α → Type u) → Type v) [DFunctor f] where
  /--
  The `mapConst` implementation is equivalent to the default implementation.
  -/
  map_const {γ β} : (DFunctor.mapConst : ((a : α) → γ a) → f β → f γ) = fun f => DFunctor.map (fun a _ => f a)
  /--
  The `map` implementation preserves identity.
  -/
  id_map {β} {x : f β} : DFunctor.map (fun _ => id) x = x
    /--
  The `map` implementation preserves function composition.
  -/
  comp_map {β γ δ : α → _} (g : (a : α) → β a → γ a) (h : (a : α) → γ a → δ a) (x : f β) :
    DFunctor.map (fun a x => h a (g a x)) x = DFunctor.map h (DFunctor.map g x)

instance {α} [BEq α] [Hashable α] : DFunctor (fun β => DHashMap α β) where
  map := DHashMap.map

/-
instance {α} [BEq α] [Hashable α] : LawfulDFunctor (fun β => DHashMap α β) where
  map_const := rfl
  id_map := **TODO**
-/

instance {α} [Ord α] : DFunctor (fun β => DTreeMap α β) where
  map := DTreeMap.map

/-
instance {α} [Ord α] : LawfulDFunctor (fun β => DTreeMap α β) where
  map_const := rfl
  id_map := **TODO**
-/

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : DFunctor (fun β => ExtDHashMap α β) where
  map := ExtDHashMap.map

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : LawfulDFunctor (fun β => ExtDHashMap α β) where
  map_const := rfl
  id_map := ExtDHashMap.map_id_fun
  comp_map := by intros; simp only [DFunctor.map, ExtDHashMap.map_map]

instance {α} [Ord α] : DFunctor (fun β => ExtDTreeMap α β) where
  map := ExtDTreeMap.map

/-
instance {α} [Ord α] : LawfulDFunctor (fun β => ExtDTreeMap α β) where
  map_const := rfl
  id_map := **TODO**
-/

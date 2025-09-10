/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/

import Lean

class IsomMap (α : Type u) (β : Type v) (μ : Type w) where
  find₁ : μ → α → Option β
  find₂ : μ → β → Option α

structure WFIsomMap (α : Type u) (β : Type v) (μ : Type w) [IsomMap α β μ] (m : μ) : Prop where
  find₁_find₂ : ∀ (a : α) (b : β), IsomMap.find₁ m a = .some b → IsomMap.find₂ m b = .some a
  find₂_find₁ : ∀ (a : α) (b : β), IsomMap.find₂ m b = .some a → IsomMap.find₁ m a = .some b

class LawfulIsomMap (α : Type u) (β : Type v) (μ : Type w) [IsomMap α β μ] where
  wf : ∀ m, WFIsomMap α β μ m

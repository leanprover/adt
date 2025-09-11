/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yicheng Qian
-/
import Lean

/-!
# Bijective Mapping

This file defines a typeclass `BiMap` that represents a bidirectional
mapping between elements of two types. `LawfulBiMap` is the lawful
counterpart of `BiMap`, which requires that the mapping is a bijection.
-/

class BiMap (α : Type u) (β : Type v) (μ : Type w) where
  find₁ : μ → α → Option β
  find₂ : μ → β → Option α

structure WFBiMap (α : Type u) (β : Type v) (μ : Type w) [BiMap α β μ] (m : μ) : Prop where
  find₁_find₂ : ∀ (a : α) (b : β), BiMap.find₁ m a = .some b → BiMap.find₂ m b = .some a
  find₂_find₁ : ∀ (a : α) (b : β), BiMap.find₂ m b = .some a → BiMap.find₁ m a = .some b

class LawfulBiMap (α : Type u) (β : Type v) (μ : Type w) [BiMap α β μ] where
  wf : ∀ m, WFBiMap α β μ m

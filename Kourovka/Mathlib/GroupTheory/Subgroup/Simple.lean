/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Supplements to the simple group API

This file contains small general-purpose lemmas that are candidates for
`Mathlib.GroupTheory.Subgroup.Simple`.
-/

open Subgroup

/-- A nontrivial direct product is not simple. -/
@[to_additive not_isSimpleAddGroup_prod /-- A nontrivial product is not additively simple. -/]
theorem not_isSimpleGroup_prod (A B : Type*) [Group A] [Group B] [Nontrivial A] [Nontrivial B] :
    ¬ IsSimpleGroup (A × B) := by
  rintro ⟨h⟩
  exact (h (prod ⊤ ⊥) inferInstance).elim (by simp) fun heq ↦
    bot_ne_top (Submonoid.prod_eq_top_iff.mp (congrArg Subgroup.toSubmonoid heq)).2

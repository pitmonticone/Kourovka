/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable

/-!
# Locally solvable groups

A group is *locally solvable* if every finitely generated subgroup is solvable. This file
defines `IsLocallySolvable` and the notion of a maximal locally solvable normal subgroup,
`IsMaxLocSolvNormal`.
-/

/-- A group is locally solvable if every finitely generated subgroup is solvable. -/
def IsLocallySolvable (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → IsSolvable H

/-- A maximal locally solvable normal subgroup of `G` is a normal subgroup `M` that
is locally solvable and maximal among locally solvable normal subgroups. -/
def IsMaxLocSolvNormal (G : Type*) [Group G] (M : Subgroup G) : Prop :=
  M.Normal ∧ IsLocallySolvable M ∧ ∀ N : Subgroup G, N.Normal → IsLocallySolvable N → M ≤ N → N = M

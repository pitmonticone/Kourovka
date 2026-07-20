/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Kourovka.Mathlib.InducedGraph
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The power graph of a group

The *power graph* of a group `G` has the elements of `G` as vertices, with distinct `x, y`
adjacent when one is a power of the other. This file defines `PowerGraph` and records a few
basic facts about paths in it.
-/

open Subgroup

/-- The power graph of a group `G`: distinct elements `x, y` are adjacent iff one is a power of
the other. -/
def PowerGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj x y := x ≠ y ∧ (x ∈ zpowers y ∨ y ∈ zpowers x)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ ⟨h, _⟩ ↦ h rfl⟩

namespace PowerGraph

variable {G : Type*} [Group G]

/-- From a path `a — b — c` in the power graph with `a ≁ c`, conclude that `a, c ∈ ⟨b⟩` or
`b ∈ ⟨a⟩ ∧ b ∈ ⟨c⟩`. -/
lemma path_fork {a b c : G} (hab : a ∈ zpowers b ∨ b ∈ zpowers a)
    (hbc : b ∈ zpowers c ∨ c ∈ zpowers b) (hac : ¬(a ∈ zpowers c ∨ c ∈ zpowers a)) :
    (a ∈ zpowers b ∧ c ∈ zpowers b) ∨ (b ∈ zpowers a ∧ b ∈ zpowers c) := by
  rw [not_or] at hac
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · exact absurd (zpowers_le.mpr hbc hab) hac.1
  · exact .inl ⟨hab, hbc⟩
  · exact .inr ⟨hab, hbc⟩
  · exact absurd (zpowers_le.mpr hab hbc) hac.2

end PowerGraph

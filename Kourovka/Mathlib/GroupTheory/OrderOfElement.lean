/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement

/-!
# Supplements to the element-order API

This file contains small general-purpose lemmas that are candidates for
`Mathlib.GroupTheory.OrderOfElement`.
-/

namespace Group

variable (G : Type*) [Group G]

open Finset in
/-- The totient sum of a finite group: `∑ g : G, φ (orderOf g)`. -/
@[to_additive /-- The totient sum of a finite additive group. -/]
noncomputable def totientSum [Fintype G] : ℕ :=
  ∑ g : G, (orderOf g).totient

end Group

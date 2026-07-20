/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone, Daniel Morrison
-/
import Mathlib.GroupTheory.OrderOfElement

/-!
# Local element-order certificate support

This file records the element-order certificate helpers used by the Kourovka
19.25 formalization.
-/

namespace Kourovka.Internal

universe u

variable (G : Type u) [Group G]

/-- A bounded element-order search used for finite certificates. -/
def boundedOrderOf [DecidableEq G] (bound : ℕ) (g : G) : ℕ :=
  if h : ∃ n : Fin (bound + 1), 0 < n.1 ∧ g ^ n.1 = 1 then
    (Fin.find (fun n : Fin (bound + 1) ↦ 0 < n.1 ∧ g ^ n.1 = 1) h).1
  else 0

/-- If a positive bound kills `g`, then bounded search computes `orderOf g`. -/
lemma orderOf_eq_boundedOrderOf_of_pow_bound [DecidableEq G] (bound : ℕ) (g : G)
    (hbound_pos : 0 < bound) (hbound : g ^ bound = 1) :
    orderOf g = boundedOrderOf G bound g := by
  let p : Fin (bound + 1) → Prop := fun n ↦ 0 < n.1 ∧ g ^ n.1 = 1
  have hex : ∃ n : Fin (bound + 1), p n :=
    ⟨⟨bound, bound.lt_succ_self⟩, hbound_pos, by simpa [p] using hbound⟩
  rw [boundedOrderOf, dif_pos hex, orderOf_eq_iff (Fin.find_spec (p := p) hex).1]
  exact
    ⟨(Fin.find_spec (p := p) hex).2, fun m hm hmpos hpow ↦ Fin.find_min (p := p) hex hm
    (show p ⟨m, hm.trans (Fin.find p hex).2⟩ from ⟨hmpos, hpow⟩)⟩

end Kourovka.Internal

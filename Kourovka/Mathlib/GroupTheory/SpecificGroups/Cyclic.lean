/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Supplements to the cyclic group API

This file contains small general-purpose lemmas that are candidates for
`Mathlib.GroupTheory.SpecificGroups.Cyclic`.
-/

open Finset

namespace IsCyclic

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G] [IsCyclic G] (n : ℕ)

/-- In a finite cyclic group, the number of elements killed by `n` is `gcd n |G|`. -/
@[to_additive
  /-- In a finite cyclic additive group, the number of elements killed by multiplication by `n` is
  `gcd n |G|`. -/]
lemma card_pow_eq_one :
    #{x : G | x ^ n = 1} = Nat.gcd n (Fintype.card G) := by
  rw [show univ.filter (fun x : G => x ^ n = 1) =
    univ.filter (fun x : G => x ^ Nat.gcd n (Fintype.card G) = 1) by
    ext x
    simpa [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_gcd_iff] using fun _ ↦ orderOf_dvd_card,
    ← sum_card_orderOf_eq_card_pow_eq_one (G := G)
    (Nat.gcd_pos_of_pos_right n Fintype.card_pos).ne']
  exact
    (sum_congr rfl fun m hm ↦ IsCyclic.card_orderOf_eq_totient (α := G) <|
    (Nat.dvd_of_mem_divisors hm).trans (Nat.gcd_dvd_right n _)).trans (Nat.sum_totient _)

end IsCyclic

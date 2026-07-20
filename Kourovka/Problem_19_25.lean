/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.ElementOrders
import Kourovka.Util.SameCardTotientSumCounterexample

/-!
# Kourovka Notebook Problem 19.25

## Problem Statement

The Kourovka Notebook problem 19.25 of B. Curtin and G. R. Pourgholi asks about
finite groups with the same order and the same element-totient sum
`∑_{g ∈ G} φ(|g|) = ∑_{h ∈ H} φ(|h|)`.

**Question**: If two finite groups `G` and `H` have the same order and the same
element-totient sum, and if `G` is simple, must `H` be simple?

**Answer**: No.

## Proof Outline

The group `PSU(3,3)` is simple and has order `6048` and element-totient sum
`23984`. The nonsimple comparison group built in the same-cardinality
totient-sum support module has the same order and the same element-totient sum,
giving a counterexample to the proposed transfer of simplicity.
-/

namespace Kourovka

open Group (totientSum)

/-- There are finite groups of the same order and same element-totient sum where
the first is simple and the second is not. -/
theorem exists_same_card_totient_sum_simple_not_simple :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (H : Type) (_ : Group H) (_ : Fintype H),
      Fintype.card G = Fintype.card H ∧
      @totientSum G _ _ = @totientSum H _ _ ∧
      @IsSimpleGroup G _ ∧
      ¬@IsSimpleGroup H _ := by
  exact
    ⟨PSU33.psuPerm, inferInstance, inferInstance,
      SameCardTotientSum.CounterexampleH, inferInstance, inferInstance,
      by rw [PSU33.card_psuPerm, SameCardTotientSum.card_counterexample_h],
      by rw [PSU33.totientSum_psuPerm, SameCardTotientSum.totient_sum_counterexample_h],
      PSU33.isSimpleGroup_psuPerm, SameCardTotientSum.not_isSimpleGroup_counterexample_h⟩

end Kourovka

/-! ### Main Theorem -/

/-- **Kourovka Notebook, Problem 19.25.** The proposed transfer of simplicity from
one finite group to another finite group of the same order and same element-totient
sum is false. -/
theorem kourovka_19_25 :
    ¬∀ (G : Type) [Group G] [Fintype G] (H : Type) [Group H] [Fintype H],
      Fintype.card G = Fintype.card H →
      Group.totientSum G = Group.totientSum H →
      IsSimpleGroup G →
      IsSimpleGroup H := by
  push_neg
  exact Kourovka.exists_same_card_totient_sum_simple_not_simple

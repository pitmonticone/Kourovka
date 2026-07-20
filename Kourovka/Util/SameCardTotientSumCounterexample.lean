/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.OrderOfElement
import Kourovka.Mathlib.GroupTheory.OrderOfElement
import Kourovka.Mathlib.GroupTheory.SpecificGroups.Cyclic
import Kourovka.Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime

/-!
# Same-cardinality totient-sum counterexample

This file constructs the nonsimple comparison group `C₆ × S₄ × (C₇ ⋊ C₆)` and
computes its order and element-totient sum.
-/

namespace Kourovka

open Group (totientSum)

namespace SameCardTotientSum

/-! ### The nonsimple comparison group `H = C₆ × (S₄ × (C₇ ⋊ C₆))`

The cyclic group `C₆` acts on `C₇` by multiplication by `3` modulo `7`. -/

/-- The order-six unit defining the nontrivial action in `C₇ ⋊ C₆`. -/
def unitThreeModSeven : (ZMod 7)ˣ :=
  ZMod.unitOfCoprime 3 (by norm_num)

/-- The unit `unitThreeModSeven` has order dividing `6`. -/
lemma unitThreeModSeven_pow_six : unitThreeModSeven ^ 6 = 1 := by
  rw [Units.ext_iff, unitThreeModSeven, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  norm_cast

/-- Multiplication by `3` on the additive group of `ZMod 7`, transferred to the
multiplicative notation used by `SemidirectProduct`. -/
def frobeniusAut : MulAut (Multiplicative (ZMod 7)) :=
  (MulAutMultiplicative (ZMod 7)).symm ((ZMod.AddAutEquivUnits 7).symm unitThreeModSeven)

/-- The automorphism `frobeniusAut` has order dividing `6`. -/
lemma frobeniusAut_pow_six : frobeniusAut ^ 6 = 1 := by
  simp [frobeniusAut, ← map_pow, unitThreeModSeven_pow_six]

/-- The action of `C₆` on `C₇` used in the Frobenius group `C₇ ⋊ C₆`. -/
def frobeniusAction : Multiplicative (ZMod 6) →* MulAut (Multiplicative (ZMod 7)) where
  toFun x := frobeniusAut ^ (Multiplicative.toAdd x).val
  map_one' := by rfl
  map_mul' x y := by
    simp only [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ frobeniusAut_pow_six, ← pow_add]

/-- The cyclic group `C₆`, written multiplicatively. -/
abbrev CyclicSix := Multiplicative (ZMod 6)

/-- The symmetric group `S₄`. -/
abbrev SymmetricFour := Equiv.Perm (Fin 4)

/-- The Frobenius group `C₇ ⋊ C₆`. -/
abbrev FrobeniusFortyTwo :=
  Multiplicative (ZMod 7) ⋊[frobeniusAction] Multiplicative (ZMod 6)

/-- The Frobenius group `C₇ ⋊ C₆` is a finite type. -/
instance instFintypeFrobeniusFortyTwo : Fintype FrobeniusFortyTwo :=
  Fintype.ofEquiv (Multiplicative (ZMod 7) × Multiplicative (ZMod 6))
  (SemidirectProduct.equivProd (φ := frobeniusAction)).symm

/-- The nonsimple candidate `H = C₆ × (S₄ × (C₇ ⋊ C₆))`. -/
abbrev CounterexampleH := CyclicSix × (SymmetricFour × FrobeniusFortyTwo)

/-- `|C₇ ⋊ C₆| = 42`. -/
lemma card_frobenius_forty_two : Fintype.card FrobeniusFortyTwo = 42 := by
  rw [← Nat.card_eq_fintype_card, SemidirectProduct.card]
  simp

/-- `|H| = 6048`. -/
theorem card_counterexample_h : Fintype.card CounterexampleH = 6048 := by
  norm_num [Fintype.card_prod, Fintype.card_perm, Nat.factorial, card_frobenius_forty_two]

/-! ### Computing `T(H) = 23984`

Rather than enumerate all `6048` elements of `H`, we compute the element-order
multiset of each of the three direct factors separately, and then combine them
by the identity `orderOf (a, b) = lcm (orderOf a) (orderOf b)`. -/

/-- The multiset of element orders of `C₆`. -/
def cyclicSixOrders : Multiset ℕ := {1, 2, 3, 3, 6, 6}

/-- The multiset of element orders of `S₄`: one element of order `1`, nine of
order `2`, eight of order `3`, six of order `4`. -/
def symmetricFourOrders : Multiset ℕ :=
  Multiset.replicate 1 1 + Multiset.replicate 9 2 + Multiset.replicate 8 3 +
  Multiset.replicate 6 4

/-- The multiset of element orders of `C₇ ⋊ C₆`: one element of order `1`, seven
of order `2`, fourteen of order `3`, fourteen of order `6`, six of order `7`. -/
def frobeniusFortyTwoOrders : Multiset ℕ :=
  Multiset.replicate 1 1 + Multiset.replicate 7 2 + Multiset.replicate 14 3 +
  Multiset.replicate 14 6 + Multiset.replicate 6 7

set_option maxRecDepth 100000 in
/-- The multiset of bounded element orders of `C₆` equals `cyclicSixOrders`. -/
lemma cyclicSixOrders_eq :
    Finset.univ.val.map (Kourovka.Internal.boundedOrderOf CyclicSix 6) = cyclicSixOrders := by
  decide

set_option maxRecDepth 100000 in
/-- The multiset of bounded element orders of `S₄` equals `symmetricFourOrders`. -/
lemma symmetricFourOrders_eq :
    Finset.univ.val.map (Kourovka.Internal.boundedOrderOf SymmetricFour 24) =
    symmetricFourOrders := by
  decide

set_option maxRecDepth 100000 in
/-- The multiset of bounded element orders of `C₇ ⋊ C₆` equals `frobeniusFortyTwoOrders`. -/
lemma frobeniusFortyTwoOrders_eq :
    Finset.univ.val.map (Kourovka.Internal.boundedOrderOf FrobeniusFortyTwo 42) =
    frobeniusFortyTwoOrders := by
  decide

/-- Contribution of the `C₇ ⋊ C₆` factor for fixed outer orders `m` (from `C₆`)
and `n` (from `S₄`). -/
def frobeniusFortyTwoContrib (m n : ℕ) : ℕ :=
  (frobeniusFortyTwoOrders.map (fun k => (Nat.lcm m (Nat.lcm n k)).totient)).sum

/-- Contribution of the `S₄ × (C₇ ⋊ C₆)` factor for a fixed outer order `m`
from `C₆`. -/
def symmetricFourContrib (m : ℕ) : ℕ :=
  (symmetricFourOrders.map (fun n => frobeniusFortyTwoContrib m n)).sum

/-- The totient sum, expressed as a convolution over the three factor order
multisets. -/
def cyclicSixTotal : ℕ :=
  (cyclicSixOrders.map (fun m => symmetricFourContrib m)).sum

/-- Reduce the totient sum over the `C₇ ⋊ C₆` factor to `frobeniusFortyTwoContrib`. -/
lemma sum_frobenius_forty_two (m n : ℕ) :
    ∑ c : FrobeniusFortyTwo, (Nat.lcm m (Nat.lcm n (orderOf c))).totient =
    frobeniusFortyTwoContrib m n := by
  rw [frobeniusFortyTwoContrib, ← frobeniusFortyTwoOrders_eq, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  congr with c
  rw [Function.comp_apply,
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound FrobeniusFortyTwo 42 c
    (by norm_num) pow_card_eq_one]

/-- Reduce the totient sum over the `S₄` factor to `symmetricFourContrib`. -/
lemma sum_symmetric_four (m : ℕ) :
    ∑ b : SymmetricFour, frobeniusFortyTwoContrib m (orderOf b) = symmetricFourContrib m := by
  have horder (b : SymmetricFour) :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound SymmetricFour 24 b
    (by norm_num) pow_card_eq_one
  simpa only [symmetricFourContrib, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun n => frobeniusFortyTwoContrib m n) symmetricFourOrders_eq)

/-- Reduce the totient sum over the `C₆` factor to `cyclicSixTotal`. -/
lemma sum_cyclic_six :
    ∑ a : CyclicSix, symmetricFourContrib (orderOf a) = cyclicSixTotal := by
  have horder (a : CyclicSix) :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound CyclicSix 6 a
    (by norm_num) pow_card_eq_one
  simpa only [cyclicSixTotal, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun m => symmetricFourContrib m) cyclicSixOrders_eq)

set_option maxHeartbeats 4000000 in
/-- The concrete candidate `H = C₆ × (S₄ × (C₇ ⋊ C₆))` has `T(H) = 23984`. -/
theorem totient_sum_counterexample_h : totientSum CounterexampleH = 23984 := by
  simp_rw [totientSum, Fintype.sum_prod_type, Prod.orderOf, sum_frobenius_forty_two,
    sum_symmetric_four, sum_cyclic_six]
  have h3 : Nat.totient 3 = 2 := by rw [Nat.totient_prime (by norm_num)]
  have h4 : Nat.totient 4 = 2 := by
    rw [show 4 = 2 ^ 2 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have h6 : Nat.totient 6 = 2 := by
    rw [show 6 = 2 * 3 by norm_num, Nat.totient_mul (by norm_num), Nat.totient_two, h3]
  have h7 : Nat.totient 7 = 6 := by rw [Nat.totient_prime (by norm_num)]
  have h12 : Nat.totient 12 = 4 := by
    rw [show 12 = 3 * 4 by norm_num, Nat.totient_mul (by norm_num), h3, h4]
  have h14 : Nat.totient 14 = 6 := by
    rw [show 14 = 2 * 7 by norm_num, Nat.totient_mul (by norm_num), Nat.totient_two, h7]
  have h21 : Nat.totient 21 = 12 := by
    rw [show 21 = 3 * 7 by norm_num, Nat.totient_mul (by norm_num), h3, h7]
  have h28 : Nat.totient 28 = 12 := by
    rw [show 28 = 4 * 7 by norm_num, Nat.totient_mul (by norm_num), h4, h7]
  have h42 : Nat.totient 42 = 12 := by
    rw [show 42 = 6 * 7 by norm_num, Nat.totient_mul (by norm_num), h6, h7]
  have h84 : Nat.totient 84 = 24 := by
    rw [show 84 = 12 * 7 by norm_num, Nat.totient_mul (by norm_num), h12, h7]
  norm_num [cyclicSixTotal, cyclicSixOrders, symmetricFourContrib, symmetricFourOrders,
    frobeniusFortyTwoContrib, frobeniusFortyTwoOrders, Nat.totient_one, Nat.totient_two,
    h3, h4, h6, h7, h12, h14, h21, h28, h42, h84]

/-- `H = C₆ × (S₄ × (C₇ ⋊ C₆))` is not simple, since it factors as a nontrivial
direct product with a `C₆` factor. -/
theorem not_isSimpleGroup_counterexample_h : ¬IsSimpleGroup CounterexampleH := by
  have : Nontrivial CyclicSix := Fintype.one_lt_card_iff_nontrivial.mp <| by
    simp [CyclicSix]
  exact not_isSimpleGroup_prod CyclicSix (SymmetricFour × FrobeniusFortyTwo)

end SameCardTotientSum

end Kourovka

/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.ElementOrders
import Kourovka.Util.SameCardTotientSumCounterexample
import Kourovka.Mathlib.GroupTheory.OrderOfElement
import Kourovka.Mathlib.GroupTheory.Subgroup.Simple

/-!
# Same-cardinality totient-sum wreath counterexample

This file constructs an alternate nonsimple comparison group
`C₂ × ((C₆ ≀ C₂) × (C₇ ⋊ C₆))` with the same order and element-totient sum as
the `PSU(3,3)` model.
-/

namespace Kourovka

open Group (totientSum)

namespace WreathDecomposition

/-- The base group of the wreath product `C₆ ≀ C₂` is `C₆ × C₆`. -/
abbrev C6Squared := Multiplicative (ZMod 6) × Multiplicative (ZMod 6)

/-- The swap automorphism on `C₆ × C₆`. -/
def swapAut : MulAut C6Squared where
  toFun := fun ⟨a, b⟩ ↦ ⟨b, a⟩
  invFun := fun ⟨a, b⟩ ↦ ⟨b, a⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The swap automorphism on `C₆ × C₆` has order `2`. -/
lemma swapAut_sq : swapAut ^ 2 = 1 := by
  ext ⟨a, b⟩ <;> rfl

/-- The action of `C₂` on `C₆ × C₆` by swapping factors. -/
def wreathSwapAction : Multiplicative (ZMod 2) →* MulAut C6Squared where
  toFun x := swapAut ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ swapAut_sq]

/-- The regular wreath product `C₆ ≀ C₂ = (C₆ × C₆) ⋊ C₂`. -/
abbrev WreathC6C2 := C6Squared ⋊[wreathSwapAction] Multiplicative (ZMod 2)

/-- The finite-type structure on `C₆ ≀ C₂`, transported along its product decomposition. -/
instance instFintypeWreathC6C2 : Fintype WreathC6C2 :=
  Fintype.ofEquiv (C6Squared × Multiplicative (ZMod 2))
  (SemidirectProduct.equivProd (φ := wreathSwapAction)).symm

/-- `|C₆ ≀ C₂| = 72`. -/
lemma card_wreathC6C2 : Fintype.card WreathC6C2 = 72 := by
  rw [← Nat.card_eq_fintype_card, SemidirectProduct.card]
  simp

/-- The cyclic group `C₂`. -/
abbrev CyclicTwo := Multiplicative (ZMod 2)

/-- The wreath-product comparison group `H' = C₂ × ((C₆ ≀ C₂) × (C₇ ⋊ C₆))`. -/
abbrev NewCounterexampleH :=
  CyclicTwo × (WreathC6C2 × SameCardTotientSum.FrobeniusFortyTwo)

/-- `|H'| = 6048`. -/
theorem card_newCounterexampleH : Fintype.card NewCounterexampleH = 6048 := by
  norm_num [Fintype.card_prod, card_wreathC6C2,
    SameCardTotientSum.card_frobenius_forty_two]

/-- The multiset of element orders of `C₂`. -/
def cyclicTwoOrders : Multiset ℕ := {1, 2}

/-- The multiset of element orders of `C₆`. -/
def cyclicSixOrders : Multiset ℕ := {1, 2, 3, 3, 6, 6}

/-- The multiset of element orders of `S₄`: one element of order `1`, nine of order `2`,
eight of order `3`, six of order `4`. -/
def symmetricFourOrders : Multiset ℕ :=
  Multiset.replicate 1 1 + Multiset.replicate 9 2 + Multiset.replicate 8 3 +
  Multiset.replicate 6 4

/-- The multiset of element orders of the Frobenius group `C₇ ⋊ C₆`: one element of order `1`,
seven of order `2`, fourteen of order `3`, fourteen of order `6`, six of order `7`. -/
def frobeniusFortyTwoOrders : Multiset ℕ :=
  Multiset.replicate 1 1 + Multiset.replicate 7 2 + Multiset.replicate 14 3 +
  Multiset.replicate 14 6 + Multiset.replicate 6 7

/-- The multiset of element orders of `C₆ ≀ C₂`: one element of order `1`, nine of order `2`,
eight of order `3`, six of order `4`, thirty-six of order `6`, twelve of order `12`. -/
def wreathC6C2Orders : Multiset ℕ :=
  Multiset.replicate 1 1 + Multiset.replicate 9 2 + Multiset.replicate 8 3 +
  Multiset.replicate 6 4 + Multiset.replicate 36 6 + Multiset.replicate 12 12

set_option maxRecDepth 100000 in
/-- The `boundedOrderOf` values of `C₂` form the multiset `cyclicTwoOrders`. -/
lemma cyclicTwoOrders_eq :
    Finset.univ.val.map (Kourovka.Internal.boundedOrderOf CyclicTwo 2) = cyclicTwoOrders := by
  decide

set_option maxRecDepth 100000 in
/-- The `boundedOrderOf` values of `C₆` form the multiset `cyclicSixOrders`. -/
lemma cyclicSixOrders_eq :
    Finset.univ.val.map (Kourovka.Internal.boundedOrderOf SameCardTotientSum.CyclicSix 6) =
    cyclicSixOrders := by
  decide

set_option maxRecDepth 100000 in
/-- The `boundedOrderOf` values of `S₄` form the multiset `symmetricFourOrders`. -/
lemma symmetricFourOrders_eq :
    Finset.univ.val.map
    (Kourovka.Internal.boundedOrderOf SameCardTotientSum.SymmetricFour 24) =
    symmetricFourOrders := by
  decide

set_option maxRecDepth 100000 in
/-- The `boundedOrderOf` values of `C₇ ⋊ C₆` form the multiset `frobeniusFortyTwoOrders`. -/
lemma frobeniusFortyTwoOrders_eq :
    Finset.univ.val.map
    (Kourovka.Internal.boundedOrderOf SameCardTotientSum.FrobeniusFortyTwo 42) =
    frobeniusFortyTwoOrders := by
  decide

set_option maxRecDepth 1000000 in
/-- The `boundedOrderOf` values of `C₆ ≀ C₂` form the multiset `wreathC6C2Orders`. -/
lemma wreathC6C2Orders_eq :
    Finset.univ.val.map (Kourovka.Internal.boundedOrderOf WreathC6C2 72) =
    wreathC6C2Orders := by
  decide

/-! ### Computing `T(H') = 23984` -/

/-- Contribution of the `C₇ ⋊ C₆` factor to `T(H')` for fixed outer orders `m` and `n`. -/
def frobeniusFortyTwoContrib (m n : ℕ) : ℕ :=
  (frobeniusFortyTwoOrders.map (fun k => (Nat.lcm m (Nat.lcm n k)).totient)).sum

/-- Contribution of the `(C₆ ≀ C₂) × (C₇ ⋊ C₆)` factor to `T(H')` for a fixed outer order `m`
from `C₂`. -/
def wreathC6C2Contrib (m : ℕ) : ℕ :=
  (wreathC6C2Orders.map (fun n => frobeniusFortyTwoContrib m n)).sum

/-- The element-totient sum `T(H')`, obtained by summing the contributions over the order
multiset of `C₂`. -/
def cyclicTwoTotal : ℕ :=
  (cyclicTwoOrders.map (fun m => wreathC6C2Contrib m)).sum

/-- Rewrites the sum of `φ(lcm m n (orderOf c))` over `C₇ ⋊ C₆` as `frobeniusFortyTwoContrib m n`. -/
lemma sum_frobenius_forty_two (m n : ℕ) :
    (∑ c : SameCardTotientSum.FrobeniusFortyTwo,
      (Nat.lcm m (Nat.lcm n (orderOf c))).totient) = frobeniusFortyTwoContrib m n := by
  have horder (c : SameCardTotientSum.FrobeniusFortyTwo) :
      orderOf c =
      Kourovka.Internal.boundedOrderOf SameCardTotientSum.FrobeniusFortyTwo 42 c :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound _ _ _
    (by norm_num) pow_card_eq_one
  simpa only [frobeniusFortyTwoContrib, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun k => (Nat.lcm m (Nat.lcm n k)).totient)
    frobeniusFortyTwoOrders_eq)

/-- Rewrites the sum of `frobeniusFortyTwoContrib m (orderOf b)` over `C₆ ≀ C₂`
as `wreathC6C2Contrib m`. -/
lemma sum_wreathC6C2 (m : ℕ) :
    ∑ b : WreathC6C2, frobeniusFortyTwoContrib m (orderOf b) = wreathC6C2Contrib m := by
  have horder (b : WreathC6C2) :
      orderOf b = Kourovka.Internal.boundedOrderOf WreathC6C2 72 b :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound _ _ _ (by norm_num)
    (by simpa only [card_wreathC6C2] using pow_card_eq_one (G := WreathC6C2) (x := b))
  simpa only [wreathC6C2Contrib, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun n => frobeniusFortyTwoContrib m n) wreathC6C2Orders_eq)

/-- Rewrites the sum of `wreathC6C2Contrib (orderOf a)` over `C₂` as `cyclicTwoTotal`. -/
lemma sum_cyclic_two :
    ∑ a : CyclicTwo, wreathC6C2Contrib (orderOf a) = cyclicTwoTotal := by
  have horder (a : CyclicTwo) :
      orderOf a = Kourovka.Internal.boundedOrderOf CyclicTwo 2 a :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound _ _ _
    (by norm_num) pow_card_eq_one
  simpa only [cyclicTwoTotal, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun m => wreathC6C2Contrib m) cyclicTwoOrders_eq)

set_option maxHeartbeats 4000000 in
/-- The wreath-product comparison group `H'` has element-totient sum `23984`. -/
theorem totient_sum_newCounterexampleH : totientSum NewCounterexampleH = 23984 := by
  simp_rw [totientSum, NewCounterexampleH, Fintype.sum_prod_type, Prod.orderOf,
    sum_frobenius_forty_two, sum_wreathC6C2, sum_cyclic_two]
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
  norm_num [cyclicTwoTotal, cyclicTwoOrders, wreathC6C2Contrib, wreathC6C2Orders,
    frobeniusFortyTwoContrib, frobeniusFortyTwoOrders, Nat.totient_one, Nat.totient_two,
    h3, h4, h6, h7, h12, h14, h21, h28, h42, h84]

/-- The wreath-product comparison group `H'` is not simple. -/
theorem not_isSimpleGroup_newCounterexampleH : ¬IsSimpleGroup NewCounterexampleH := by
  have : Nontrivial CyclicTwo := Fintype.one_lt_card_iff_nontrivial.mp <| by
    simp [CyclicTwo]
  have : Nontrivial WreathC6C2 :=
    Fintype.one_lt_card_iff_nontrivial.mp <| by norm_num [card_wreathC6C2]
  exact not_isSimpleGroup_prod CyclicTwo (WreathC6C2 × SameCardTotientSum.FrobeniusFortyTwo)

/-! ### Distinguishing the two nonsimple comparison groups -/

/-- Number of elements of `C₇ ⋊ C₆` whose overall order is `3`, for fixed outer orders `m`
and `n`: the count of element orders `k` with `lcm m n k = 3`. -/
def frobeniusFortyTwoOrderThreeContrib (m n : ℕ) : ℕ :=
  (frobeniusFortyTwoOrders.map fun k =>
    if Nat.lcm m (Nat.lcm n k) = 3 then 1 else 0).sum

/-- Order-`3` count for the `S₄ × (C₇ ⋊ C₆)` factor for a fixed outer order `m` from `C₆`. -/
def symmetricFourOrderThreeContrib (m : ℕ) : ℕ :=
  (symmetricFourOrders.map (fun n => frobeniusFortyTwoOrderThreeContrib m n)).sum

/-- The number of order-`3` elements of the original comparison group
`C₆ × (S₄ × (C₇ ⋊ C₆))`. -/
def cyclicSixOrderThreeTotal : ℕ :=
  (cyclicSixOrders.map (fun m => symmetricFourOrderThreeContrib m)).sum

/-- Order-`3` count for the `(C₆ ≀ C₂) × (C₇ ⋊ C₆)` factor for a fixed outer order `m`
from `C₂`. -/
def wreathC6C2OrderThreeContrib (m : ℕ) : ℕ :=
  (wreathC6C2Orders.map (fun n => frobeniusFortyTwoOrderThreeContrib m n)).sum

/-- The number of order-`3` elements of the decomposed comparison group `H'`. -/
def cyclicTwoOrderThreeTotal : ℕ :=
  (cyclicTwoOrders.map (fun m => wreathC6C2OrderThreeContrib m)).sum

/-- Rewrites the order-`3` indicator sum over `C₇ ⋊ C₆` as
`frobeniusFortyTwoOrderThreeContrib m n`. -/
lemma sum_frobenius_forty_two_order_three (m n : ℕ) :
    (∑ c : SameCardTotientSum.FrobeniusFortyTwo,
      if Nat.lcm m (Nat.lcm n (orderOf c)) = 3 then 1 else 0) =
      frobeniusFortyTwoOrderThreeContrib m n := by
  have horder (c : SameCardTotientSum.FrobeniusFortyTwo) :
      orderOf c =
      Kourovka.Internal.boundedOrderOf SameCardTotientSum.FrobeniusFortyTwo 42 c :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound _ _ _
    (by norm_num) pow_card_eq_one
  simpa only [frobeniusFortyTwoOrderThreeContrib, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun k =>
      if Nat.lcm m (Nat.lcm n k) = 3 then 1 else 0) frobeniusFortyTwoOrders_eq)

/-- Rewrites the order-`3` contribution sum over `S₄` as `symmetricFourOrderThreeContrib m`. -/
lemma sum_symmetric_four_order_three (m : ℕ) :
    (∑ b : SameCardTotientSum.SymmetricFour,
      frobeniusFortyTwoOrderThreeContrib m (orderOf b)) =
      symmetricFourOrderThreeContrib m := by
  have horder (b : SameCardTotientSum.SymmetricFour) :
      orderOf b =
      Kourovka.Internal.boundedOrderOf SameCardTotientSum.SymmetricFour 24 b :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound _ _ _
    (by norm_num) pow_card_eq_one
  simpa only [symmetricFourOrderThreeContrib, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun n => frobeniusFortyTwoOrderThreeContrib m n)
    symmetricFourOrders_eq)

/-- Rewrites the order-`3` contribution sum over `C₆` as `cyclicSixOrderThreeTotal`. -/
lemma sum_cyclic_six_order_three :
    (∑ a : SameCardTotientSum.CyclicSix, symmetricFourOrderThreeContrib (orderOf a)) =
    cyclicSixOrderThreeTotal := by
  have horder (a : SameCardTotientSum.CyclicSix) :
      orderOf a = Kourovka.Internal.boundedOrderOf SameCardTotientSum.CyclicSix 6 a :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound _ _ _
    (by norm_num) pow_card_eq_one
  simpa only [cyclicSixOrderThreeTotal, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun m => symmetricFourOrderThreeContrib m) cyclicSixOrders_eq)

/-- Rewrites the order-`3` contribution sum over `C₆ ≀ C₂` as `wreathC6C2OrderThreeContrib m`. -/
lemma sum_wreathC6C2_order_three (m : ℕ) :
    ∑ b : WreathC6C2, frobeniusFortyTwoOrderThreeContrib m (orderOf b) =
    wreathC6C2OrderThreeContrib m := by
  have horder (b : WreathC6C2) :
      orderOf b = Kourovka.Internal.boundedOrderOf WreathC6C2 72 b :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound _ _ _ (by norm_num)
    (by simpa only [card_wreathC6C2] using pow_card_eq_one (G := WreathC6C2) (x := b))
  simpa only [wreathC6C2OrderThreeContrib, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun n => frobeniusFortyTwoOrderThreeContrib m n)
    wreathC6C2Orders_eq)

/-- Rewrites the order-`3` contribution sum over `C₂` as `cyclicTwoOrderThreeTotal`. -/
lemma sum_cyclic_two_order_three :
    ∑ a : CyclicTwo, wreathC6C2OrderThreeContrib (orderOf a) =
    cyclicTwoOrderThreeTotal := by
  have horder (a : CyclicTwo) :
      orderOf a = Kourovka.Internal.boundedOrderOf CyclicTwo 2 a :=
    Kourovka.Internal.orderOf_eq_boundedOrderOf_of_pow_bound _ _ _
    (by norm_num) pow_card_eq_one
  simpa only [cyclicTwoOrderThreeTotal, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply, horder] using congrArg Multiset.sum
    (congrArg (Multiset.map fun m => wreathC6C2OrderThreeContrib m) cyclicTwoOrders_eq)

/-- The number of elements of order `3` in the original nonsimple comparison group. -/
theorem order3_count_orig :
    (Finset.univ.filter fun h : SameCardTotientSum.CounterexampleH ↦ orderOf h = 3).card =
    404 := by
  simp_rw [Finset.card_filter, SameCardTotientSum.CounterexampleH, Fintype.sum_prod_type,
    Prod.orderOf,
    sum_frobenius_forty_two_order_three, sum_symmetric_four_order_three,
    sum_cyclic_six_order_three]
  norm_num [cyclicSixOrderThreeTotal, cyclicSixOrders, symmetricFourOrderThreeContrib,
    symmetricFourOrders, frobeniusFortyTwoOrderThreeContrib, frobeniusFortyTwoOrders]

/-- The number of elements of order `3` in the decomposed comparison group. -/
theorem order3_count_new :
    (Finset.univ.filter fun h : NewCounterexampleH ↦ orderOf h = 3).card = 134 := by
  simp_rw [Finset.card_filter, NewCounterexampleH, Fintype.sum_prod_type, Prod.orderOf,
    sum_frobenius_forty_two_order_three, sum_wreathC6C2_order_three,
    sum_cyclic_two_order_three]
  norm_num [cyclicTwoOrderThreeTotal, cyclicTwoOrders, wreathC6C2OrderThreeContrib,
    wreathC6C2Orders, frobeniusFortyTwoOrderThreeContrib, frobeniusFortyTwoOrders]

/-- The two nonsimple comparison groups are not isomorphic; the number of elements of
order `3` is different. -/
theorem not_isomorphic_counterexamples :
    IsEmpty (SameCardTotientSum.CounterexampleH ≃* NewCounterexampleH) := by
  refine ⟨fun f => ?_⟩
  have h :
      (Finset.univ.filter fun x : SameCardTotientSum.CounterexampleH ↦ orderOf x = 3).card =
      (Finset.univ.filter fun x : NewCounterexampleH ↦ orderOf x = 3).card :=
    Finset.card_equiv f (by simp)
  simp [order3_count_orig, order3_count_new] at h

/-- A concrete counterexample using the decomposed nonsimple group
`C₂ × ((C₆ ≀ C₂) × (C₇ ⋊ C₆))`. -/
theorem exists_wreath_counterexample :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (H : Type) (_ : Group H) (_ : Fintype H),
      Fintype.card G = Fintype.card H ∧
      @totientSum G _ _ = @totientSum H _ _ ∧
      @IsSimpleGroup G _ ∧
      ¬@IsSimpleGroup H _ := by
  exact
    ⟨PSU33.psuPerm, inferInstance, inferInstance,
      NewCounterexampleH, inferInstance, inferInstance,
      by rw [PSU33.card_psuPerm, card_newCounterexampleH],
      by rw [PSU33.totientSum_psuPerm, totient_sum_newCounterexampleH],
      PSU33.isSimpleGroup_psuPerm, not_isSimpleGroup_newCounterexampleH⟩

end WreathDecomposition

end Kourovka

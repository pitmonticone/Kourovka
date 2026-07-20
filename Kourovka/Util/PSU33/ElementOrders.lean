/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.BigOperators
import Kourovka.Mathlib.GroupTheory.OrderOfElement
import Kourovka.Util.PSU33.Involutions
import Kourovka.Util.PSU33.OrderEight
import Kourovka.Util.PSU33.PointStabilizer
import Kourovka.Util.PSU33.SylowSeven

/-!
# Element-order counts for `PSU(3,3)`

This file assembles the element-order histogram for the geometric permutation
group `psuPerm` and computes its element-totient sum.
-/

open Group (totientSum)

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

/-! ## Element-order and totient-sum assembly for `PSU(3,3)` -/

/-- The `order 1` entry of the element-order histogram of `SU(3,3)`: the only
element of order `1` is the identity. -/
theorem card_orderOf_eq_one_su :
    (Finset.univ.filter (fun g : specialUnitaryGroup => orderOf g = 1)).card = 1 := by
  exact Finset.card_eq_one.mpr ⟨1, by ext; simp [orderOf_eq_one_iff]⟩

/-- **Exhaustiveness of the listed orders.** Under the eight count hypotheses, the
orders `1`, `2`, `3`, `4`, `6`, `7`, `8`, and `12` already account for all `6048`
elements of `SU(3,3)`. -/
theorem su_orders_exhaustive
    (h1 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 1).card = 1)
    (h2 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 2).card = 63)
    (h3 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 3).card = 728)
    (h4 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 4).card = 504)
    (h6 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 6).card = 504)
    (h7 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 7).card = 1728)
    (h8 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 8).card = 1512)
    (h12 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 12).card = 1008)
    (g : specialUnitaryGroup) :
    orderOf g ∈ ({1, 2, 3, 4, 6, 7, 8, 12} : Finset ℕ) := by
  have h_card_eq :
      (Finset.univ.filter fun g : specialUnitaryGroup =>
      orderOf g ∈ ({1, 2, 3, 4, 6, 7, 8, 12} : Finset ℕ)).card = 6048 := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ
    {1, 2, 3, 4, 6, 7, 8, 12} orderOf]
    simp_all +decide [Finset.sum]
  simpa using Finset.eq_univ_iff_forall.mp (Finset.eq_univ_of_card _
    (h_card_eq.trans (by simpa using card_univ_specialUnitaryGroup.symm))) g

set_option maxHeartbeats 800000 in
set_option maxRecDepth 1000000 in
/-- **Conditional totient-sum assembly.** Given the element-order histogram of
`SU(3,3)` for orders `1`, `2`, `3`, `4`, `6`, `7`, `8`, and `12`, the totient sum
of the geometric permutation group `psuPerm` is `23984`. -/
theorem totientSum_psuPerm_of_su_order_counts
    (h1 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 1).card = 1)
    (h2 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 2).card = 63)
    (h3 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 3).card = 728)
    (h4 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 4).card = 504)
    (h6 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 6).card = 504)
    (h7 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 7).card = 1728)
    (h8 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 8).card = 1512)
    (h12 : (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 12).card = 1008) :
    totientSum psuPerm = 23984 := by
  classical
  let e : specialUnitaryGroup ≃* psuPerm :=
    MulEquiv.ofBijective toPsu ⟨toPsu_injective, toPsu_surjective⟩
  rw [totientSum, ← Fintype.sum_equiv e.toEquiv]
  · have h_sum :
        ∑ g : specialUnitaryGroup, (orderOf g).totient =
        ∑ d ∈ ({1, 2, 3, 4, 6, 7, 8, 12} : Finset ℕ),
        (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = d).card *
        d.totient := by
      rw [Finset.sum_comp Nat.totient orderOf]
      apply Finset.sum_subset
      · intro x hx
        obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hx
        exact su_orders_exhaustive h1 h2 h3 h4 h6 h7 h8 h12 g
      · simp +contextual [Finset.ext_iff]
    simp only [orderOf_eq_one_iff] at h1
    exact h_sum.trans (by
      norm_num [Nat.totient, h1, h2, h3, h4, h6, h7, h8, h12]
      decide)
  · exact fun g => congrArg Nat.totient (e.orderOf_eq g).symm

/-- The geometric permutation group `PSU(3,3)` has totient sum `23984`. -/
theorem totientSum_psuPerm :
    totientSum psuPerm = 23984 :=
  totientSum_psuPerm_of_su_order_counts card_orderOf_eq_one_su card_orderOf_eq_two_su
    card_orderOf_eq_three_su card_orderOf_eq_four_su card_orderOf_eq_six_su
    card_orderOf_eq_seven_su card_orderOf_eq_eight_su card_orderOf_eq_twelve_su

end PSU33

/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.PointStabilizerOrderTwelve

/-!
# Order-six point-stabilizer count for `PSU(3,3)`

This file isolates the order-six condition in the point-stabilizer
parametrization and counts the corresponding parameters.
-/

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

section PointStabilizerCounts

/-! ### The order-six scalar predicate and its count -/

/-- The order-six refinement over `F9`. -/
def order_six_pred_f9 (t : F9 × F9 × F9) : Prop :=
  param_pred_f9 t ∧ t.1 = -1 ∧ t.2.1 + t.2.2 ^ 4 ≠ 0

/-- The finite model predicate agrees with the `F9` order-six predicate. -/
lemma order_six_pred_iff (t : f9_pair × f9_pair × f9_pair) :
    order_six_pred_model t ↔ order_six_pred_f9 (f9_pair_triple_equiv t) := by
  constructor
  · rintro ⟨hp, hμ, hne⟩
    refine ⟨(param_pred_model_iff t).1 hp, ?_, ?_⟩
    · simpa +decide [to_f9] using congr_arg to_f9 hμ
    · simpa +decide [← to_f9_add, ← to_f9_fourth] using
        fun h => hne <| to_f9_injective <| by simpa using h
  · rintro ⟨hp, hμ, hne⟩
    refine ⟨(param_pred_model_iff t).2 hp, ?_, ?_⟩
    · exact to_f9_injective <| by simpa +decide [to_f9] using hμ
    · intro h
      apply hne
      simpa +decide [← to_f9_add, ← to_f9_fourth] using congr_arg to_f9 h

/-- The finite model has exactly `18` order-six parameters. -/
lemma card_order_six_model :
    Fintype.card {t : f9_pair × f9_pair × f9_pair // order_six_pred_model t} = 18 := by
  simpa only [modelCounts, Prod.snd_sum, Fintype.card_subtype, Finset.card_filter] using
    congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) modelCounts_eq

/-- **The order-six parameter count.** -/
lemma card_order_six_f9 :
    Nat.card {t : F9 × F9 × F9 // order_six_pred_f9 t} = 18 := by
  rw [← Nat.card_congr (f9_pair_triple_equiv.subtypeEquiv order_six_pred_iff),
    Nat.card_eq_fintype_card, card_order_six_model]

/-! ### Powers of a parametrized stabilizer element -/

/-- The second power fixes `fv0` when the diagonal scalar is `-1`. -/
lemma param_g2_fv0 (g : specialUnitaryGroup) (μ : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (hμ : μ = -1) :
    toLinearEquiv (g ^ 2) fv0 = fv0 := by simpa +decide [hμ] using param_pow_fv0 g μ e0 2

/-- The second power fixes `fw` when the diagonal scalar is `-1`. -/
lemma param_g2_fw (g : specialUnitaryGroup) (μ a c : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ : μ = -1) :
    toLinearEquiv (g ^ 2) fw = fw := by
  convert
    param_M_action g μ a c e0 e1 e2 (-c ^ 3 * μ ^ 3) (0 : F9) (μ ^ 2) using 1 <;>
    simp +decide [sq, e2, hμ, toLinearEquiv_mul_apply]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The second power acts on `fv1` as a transvection with coefficient `a + c ^ 4`
when the diagonal scalar is `-1`. -/
lemma param_g2_fv1 (g : specialUnitaryGroup) (μ a c : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ : μ = -1) :
    toLinearEquiv (g ^ 2) fv1 = fv1 + (a + c ^ 4) • fv0 := by
  convert param_M_action g μ a c e0 e1 e2 a (μ ^ 3)⁻¹ c using 1
  · rw [← e1, sq, toLinearEquiv_mul_apply]
  · simp +decide [hμ, pow_succ, mul_assoc]
    grind

/-- The second power is trivial iff `a + c ^ 4 = 0`, when `μ = -1`. -/
lemma param_g2_eq_one_iff (g : specialUnitaryGroup) (μ a c : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ : μ = -1) :
    g ^ 2 = 1 ↔ a + c ^ 4 = 0 := by
  constructor <;> intro h
  · have h_g2_fv1 := congr_arg (fun x => x - fv1)
      (param_g2_fv1 g μ a c e0 e1 e2 hμ)
    simpa +decide [h, smul_eq_zero, fv0_ne] using h_g2_fv1.symm
  · exact su_eq_one_of_frame_fix (g ^ 2) (param_g2_fv0 g μ e0 hμ)
      (by simpa [h] using param_g2_fv1 g μ a c e0 e1 e2 hμ)
      (param_g2_fw g μ a c e0 e1 e2 hμ)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The third power negates `fv0`, hence is nontrivial, when `μ = -1`. -/
lemma param_g3_ne_one_of_neg (g : specialUnitaryGroup) (μ : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (hμ : μ = -1) :
    g ^ 3 ≠ 1 := by
  intro h
  have := param_pow_fv0 g μ e0 3
  simp +decide [hμ, h, toLinearEquiv_one] at this
  grind [fv0_ne]

/-- The third power is trivial when the diagonal scalar is `1`. -/
lemma param_g3_eq_one_of_diag_one (g : specialUnitaryGroup) (μ a c : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ : μ = 1) :
    g ^ 3 = 1 := by
  apply PSU33.su_eq_one_of_frame_fix
  · simpa +decide [hμ] using PSU33.param_pow_fv0 g μ e0 3
  all_goals
    simp_all +decide [pow_succ, toLinearEquiv_mul_apply]
    grind

/-! ### The order-six criterion -/

/-- **Order-six criterion.** A stabilizer element of `p0` with Borel parameters
`(μ, a, c)` has order `6` iff `μ = -1` and `a + c ^ 4 ≠ 0`. -/
lemma orderOf_six_iff_of_param (g : specialUnitaryGroup) (μ a c : F9) (hμ0 : μ ≠ 0)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw) :
    orderOf g = 6 ↔ (μ = -1 ∧ a + c ^ 4 ≠ 0) := by
  constructor
  · intro hg
    have hμ2 : μ ^ 2 = 1 := by
      have hμ_sq : μ ^ 6 = 1 := smul_left_injective _ fv0_ne <| by
        change μ ^ 6 • fv0 = 1 • fv0
        rw [← param_pow_fv0 g μ e0 6,
          show g ^ 6 = 1 by rw [← hg, pow_orderOf_eq_one]]
        simp +decide [toLinearEquiv_one]
      grind
    have hμ_neg : μ = -1 := by
      by_contra hμ_ne_neg_one
      have := orderOf_dvd_of_pow_eq_one
        (PSU33.param_g3_eq_one_of_diag_one g μ a c e0 e1 e2 <|
          mul_left_cancel₀ (sub_ne_zero_of_ne hμ_ne_neg_one) (by linear_combination' hμ2))
      simp_all +decide
    have h_order2 : g ^ 2 ≠ 1 :=
      (not_congr orderOf_dvd_iff_pow_eq_one).mp (by simp [hg])
    exact ⟨hμ_neg, fun hzero =>
      h_order2 ((param_g2_eq_one_iff g μ a c e0 e1 e2 hμ_neg).2 hzero)⟩
  · intro h
    have h_order : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one <|
      param_g6_eq_one_of_sq_one g μ a c hμ0 e0 e1 e2 (by
        rw [h.1]
        ring)
    have h_not_div_2 : ¬ (orderOf g ∣ 2) := by
      simpa [orderOf_dvd_iff_pow_eq_one, param_g2_eq_one_iff g μ a c e0 e1 e2 h.1]
        using h.2
    have h_not_div_3 : ¬ (orderOf g ∣ 3) :=
      (not_congr orderOf_dvd_iff_pow_eq_one).mpr
        (PSU33.param_g3_ne_one_of_neg g μ e0 h.1)
    have := Nat.le_of_dvd (by decide) h_order
    interval_cases orderOf g <;> trivial

/-! ### Transfer of the criterion to the stabilizer subtype -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The order-six criterion transported to the stabilizer subtype. -/
lemma orderOf_stab_six_iff (s : stabilizer specialUnitaryGroup p0) :
    orderOf s = 6 ↔ order_six_pred_f9 (stab_param s).1 := by
  obtain ⟨hμ0, _, e0, e1, e2⟩ := stab_param_spec s
  rw [← show orderOf (s : specialUnitaryGroup) = orderOf s from
    orderOf_injective (stabilizer specialUnitaryGroup p0).subtype Subtype.coe_injective s]
  simpa [order_six_pred_f9, (stab_param s).2] using
    orderOf_six_iff_of_param (s : specialUnitaryGroup) _ _ _ hμ0 e0 e1 e2

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The order-six count in the point stabilizer of `p0` is `18`.** -/
theorem card_orderOf_eq_six_stab_p0 :
    (Finset.univ.filter fun g : MulAction.stabilizer specialUnitaryGroup p0 =>
      orderOf g = 6).card = 18 := by
  rw [← Fintype.card_subtype]
  have e1 : {s : stabilizer specialUnitaryGroup p0 // orderOf s = 6}
      ≃ {t : F9 × F9 × F9 // order_six_pred_f9 t} := by
    refine (stab_param_equiv.subtypeEquiv (fun s => ?_)).trans
      (Equiv.subtypeSubtypeEquivSubtype (fun {t} ht => ht.1))
    simpa [stab_param_equiv] using orderOf_stab_six_iff s
  rw [Fintype.card_congr e1, ← Nat.card_eq_fintype_card, card_order_six_f9]

end PointStabilizerCounts

end PSU33

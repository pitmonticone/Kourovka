/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.PointStabilizerOrderSix

/-!
# Order-three and global point-stabilizer counts for `PSU(3,3)`

This file counts order-three elements by first counting them in a point
stabilizer and then summing over the unique fixed isotropic point.
-/

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

section PointStabilizerCounts

/-! ## Problem-specific order-three count for `PSU(3,3)` -/

/-- An order-three special-unitary element has cube `1` in the linear
representation. -/
lemma toLinearEquiv_pow_three_eq_one
    (g : specialUnitaryGroup) (hg : orderOf g = 3) :
    toLinearEquiv g * toLinearEquiv g * toLinearEquiv g =
      LinearEquiv.refl F9 (Fin 3 → F9) := by
  simpa [← toLinearEquiv_mul, hg, pow_succ, pow_two] using
    congr_arg toLinearEquiv (pow_orderOf_eq_one g)

/-- An eigenvalue of an order-three element on a nonzero eigenvector over `F9`
is `1`. -/
lemma eigenvalue_eq_one_of_orderOf_eq_three
    (g : specialUnitaryGroup) (hg : orderOf g = 3)
    (v : Fin 3 → F9) (hv : v ≠ 0) (μ : F9)
    (h : toLinearEquiv g v = μ • v) : μ = 1 := by
  have h_mu_cubed : μ ^ 3 = 1 := by
    apply smul_left_injective _ hv
    simpa [h, pow_succ, mul_assoc, smul_smul] using
      congr_arg (fun f => f v) (toLinearEquiv_pow_three_eq_one g hg)
  grind +revert

/-- The order-three elements fixing an isotropic point. -/
noncomputable def orderThreeFixing (p : IsotropicPoint) : Finset specialUnitaryGroup :=
  univ.filter fun g => orderOf g = 3 ∧ g • p = p

/-- The stabilizer of the chosen isotropic base vector. -/
def baseVectorStabilizer : Subgroup specialUnitaryGroup where
  carrier := {g | toLinearEquiv g baseVec = baseVec}
  one_mem' := by
    simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp only [toLinearEquiv_mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_setOf_eq, toLinearEquiv_inv_apply,
      LinearEquiv.symm_apply_eq] using ha.symm

set_option synthInstance.maxHeartbeats 1000000 in
/-- The stabilizer of the chosen isotropic base vector has order `27`. -/
lemma card_base_vector_stabilizer : Nat.card baseVectorStabilizer = 27 := by
  let act : MulAction specialUnitaryGroup (Fin 3 → F9) :=
    MulAction.compHom _ toLinearEquivHomStab
  have hsmul : ∀ (g : specialUnitaryGroup) (v : Fin 3 → F9), g • v = toLinearEquiv g v :=
    fun _ _ => rfl
  have hstab : baseVectorStabilizer = MulAction.stabilizer specialUnitaryGroup baseVec := by
    ext
    rfl
  have horbit : (MulAction.orbit specialUnitaryGroup baseVec : Set (Fin 3 → F9))
      = {v | v ≠ 0 ∧ hermForm conj9 v v = 0} := by
    ext x
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, hsmul]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(toLinearEquiv g).map_eq_zero_iff.not.mpr baseVec_ne,
        by simpa only [toLinearEquiv_hermForm] using baseVec_iso⟩
    · rintro ⟨hx0, hxi⟩
      obtain ⟨h, _, hh⟩ :=
        rootGenerated_transitive_isotropic baseVec x baseVec_ne hx0 baseVec_iso hxi
      exact ⟨h, hh⟩
  have hcardorbit : Nat.card (MulAction.orbit specialUnitaryGroup baseVec) = 224 := by
    simpa only [horbit] using card_isotropic_nonzero
  have hos :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group specialUnitaryGroup baseVec
  rw [← Nat.card_eq_fintype_card, hcardorbit, ← Nat.card_eq_fintype_card, ← hstab,
    ← Nat.card_eq_fintype_card, card_specialUnitaryGroup] at hos
  omega

set_option synthInstance.maxHeartbeats 400000 in
/-- Every element of the base-vector stabilizer has cube `1`. -/
lemma base_vector_stabilizer_pow_three
    (g : specialUnitaryGroup) (hg : g ∈ baseVectorStabilizer) : g ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have coe_pow : ∀ (e : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9)) (n : ℕ),
      ((e ^ n : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9)) :
        Module.End F9 (Fin 3 → F9)) = (e : Module.End F9 (Fin 3 → F9)) ^ n := by
    intro e n
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, pow_succ, ← ih]
      rfl
  have htoLinearEquiv_pow (n : ℕ) : toLinearEquiv (g ^ n) = (toLinearEquiv g) ^ n :=
    map_pow toLinearEquivHomStab g n
  have hdvd27 : orderOf g ∣ 27 := by
    simpa only [card_base_vector_stabilizer,
      (orderOf_injective baseVectorStabilizer.subtype Subtype.coe_injective
        ⟨g, hg⟩).symm] using
      orderOf_dvd_natCard (⟨g, hg⟩ : baseVectorStabilizer)
  have hg27 : g ^ 27 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd27
  set a : Module.End F9 (Fin 3 → F9) := (toLinearEquiv g : Module.End F9 (Fin 3 → F9))
    with ha
  have ha27 : a ^ 27 = 1 := by
    rw [ha, ← coe_pow, ← htoLinearEquiv_pow, hg27, toLinearEquiv_one]
    rfl
  have : CharP (Module.End F9 (Fin 3 → F9)) 3 :=
    charP_of_injective_algebraMap (algebraMap F9 (Module.End F9 (Fin 3 → F9))).injective 3
  set N : Module.End F9 (Fin 3 → F9) := a - 1 with hN
  have hNnil : IsNilpotent N := by
    refine ⟨27, ?_⟩
    simpa [hN, show (3 : ℕ) ^ 3 = 27 by norm_num, ha27] using
      sub_pow_char_pow_of_commute (R := Module.End F9 (Fin 3 → F9)) 3 3
        (Commute.one_right a)
  have hN3 : N ^ 3 = 0 := by
    have hch := N.aeval_self_charpoly
    rw [hNnil.charpoly_eq_X_pow_finrank] at hch
    simpa only [map_pow, Polynomial.aeval_X,
      show Module.finrank F9 (Fin 3 → F9) = 3 by simp] using hch
  have h3 : (3 : Module.End F9 (Fin 3 → F9)) = 0 :=
    CharP.cast_eq_zero (Module.End F9 (Fin 3 → F9)) 3
  have hcube : a ^ 3 = 1 := by
    rw [show a = 1 + N by
      rw [hN]
      abel]
    calc
      (1 + N) ^ 3 = 1 + 3 • N + 3 • N ^ 2 + N ^ 3 := by noncomm_ring
      _ = 1 := by simp [hN3, nsmul_eq_mul, h3]
  apply (toLinearEquiv_eq_refl_iff_one (g ^ 3)).mp
  apply LinearEquiv.toLinearMap_injective
  rw [htoLinearEquiv_pow, coe_pow, ← ha, hcube]
  rfl

/-- A special-unitary element fixing an isotropic vector fixes the corresponding
isotropic projective point. -/
lemma fixed_point_of_fixed_vector
    (g : specialUnitaryGroup) (v : Fin 3 → F9) (hv : v ≠ 0)
    (hvi : hermForm conj9 v v = 0) (h : toLinearEquiv g v = v) :
    g • mkIso v hv hvi = mkIso v hv hvi :=
  su_smul_mkIso_of_scale g v hv hvi 1 one_ne_zero (by simpa using h)

/-- Exactly `26` order-three elements fix the chosen isotropic point. -/
lemma card_order_three_fixing_base : (orderThreeFixing a0Pt).card = 26 := by
  unfold orderThreeFixing
  have h_order_three :
      ∀ g : specialUnitaryGroup, g ∈ baseVectorStabilizer → g ≠ 1 → orderOf g = 3 := by
    intro g hg hg_ne_one
    have h_order := orderOf_dvd_of_pow_eq_one (base_vector_stabilizer_pow_three g hg)
    have := Nat.le_of_dvd (by decide) h_order
    interval_cases _ : orderOf g <;> simp_all +decide
  have h_eq :
      {g : specialUnitaryGroup | orderOf g = 3 ∧ g • a0Pt = a0Pt} =
      (baseVectorStabilizer : Set specialUnitaryGroup) \ {1} := by
    ext g
    specialize h_order_three g
    by_cases hg : g = 1 <;> simp_all +decide [baseVectorStabilizer]
    constructor <;> intro h <;> simp_all +decide [a0Pt]
    · obtain ⟨μ, _, hμ⟩ := su_stab_point_scales g baseVec baseVec_ne baseVec_iso h.2
      simpa [eigenvalue_eq_one_of_orderOf_eq_three g h.1 baseVec baseVec_ne μ hμ]
        using hμ
    · exact fixed_point_of_fixed_vector g baseVec baseVec_ne baseVec_iso h
  convert congr_arg Set.ncard h_eq using 1
  · rw [← Set.ncard_coe_finset]
    congr
    aesop
  · rw [Set.ncard_diff_singleton_of_mem baseVectorStabilizer.one_mem,
      show (baseVectorStabilizer : Set specialUnitaryGroup).ncard = 27 from
        card_base_vector_stabilizer]

set_option synthInstance.maxHeartbeats 400000 in
/-- Exactly `26` order-three elements fix any given isotropic point. -/
lemma card_order_three_fixing (p : IsotropicPoint) :
    (orderThreeFixing p).card = 26 := by
  have : MulAction.IsMultiplyPretransitive specialUnitaryGroup IsotropicPoint 2 :=
    specialUnitaryGroup_twoTransitive
  have : MulAction.IsPretransitive specialUnitaryGroup IsotropicPoint :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq specialUnitaryGroup a0Pt p
  rw [← card_order_three_fixing_base]
  have horder (g : specialUnitaryGroup) : orderOf (h * g * h⁻¹) = orderOf g := by
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj h) g
  have hfix (g : specialUnitaryGroup) :
      (h * g * h⁻¹) • p = p ↔ g • a0Pt = a0Pt := by
    simp only [← hh, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  have hmem (g : specialUnitaryGroup) :
      g ∈ orderThreeFixing a0Pt ↔ h * g * h⁻¹ ∈ orderThreeFixing p := by
    simp only [orderThreeFixing, mem_filter, mem_univ, true_and, horder, hfix]
  refine (Finset.card_bij
    (fun g _ => h * g * h⁻¹)
    (fun g hg => (hmem g).mp hg)
    (fun a _ b _ hab => mul_left_cancel (mul_right_cancel hab))
    (fun g hg => ?_)).symm
  refine ⟨h⁻¹ * g * h, (hmem _).mpr ?_, by group⟩
  simpa only [show h * (h⁻¹ * g * h) * h⁻¹ = g by group] using hg

set_option synthInstance.maxHeartbeats 400000 in
/-- **There are exactly `728` elements of order `3` in `SU(3,3)`.** -/
theorem card_orderOf_eq_three_su :
    (univ.filter (fun g : specialUnitaryGroup => orderOf g = 3)).card = 728 := by
  convert Set.ncard_eq_toFinset_card' ({g : specialUnitaryGroup | orderOf g = 3}) using 1
  · rw [Set.ncard_eq_toFinset_card']
    aesop
  · rw [eq_comm, Set.toFinset_setOf]
    have h_biUnion :
        univ.filter (fun g : specialUnitaryGroup => orderOf g = 3) =
        Finset.biUnion (univ : Finset IsotropicPoint) fun p => orderThreeFixing p := by
      ext g
      simp only [mem_filter, mem_univ, true_and, mem_biUnion, orderThreeFixing]
      refine ⟨fun hg => ?_, fun ⟨_, hg, _⟩ => hg⟩
      obtain ⟨p, hp⟩ := exists_fixed_isotropic_of_order_three g hg
      exact ⟨p, hg, hp⟩
    rw [h_biUnion, card_biUnion]
    · norm_num [card_order_three_fixing, card_isotropicPoint]
    · intros p _ q _ hpq
      change Disjoint (orderThreeFixing p) (orderThreeFixing q)
      simp only [Finset.disjoint_left, orderThreeFixing, mem_filter, mem_univ, true_and]
      rintro g ⟨hg, hgp⟩ ⟨_, hgq⟩
      obtain ⟨_, _, huniq⟩ := unique_fixed_isotropic_of_order_three g hg
      exact hpq ((huniq p hgp).trans (huniq q hgq).symm)

/-- **There are exactly `504` elements of order `6` in `SU(3,3)`.** -/
theorem card_orderOf_eq_six_su :
    (univ.filter (fun g : specialUnitaryGroup => orderOf g = 6)).card = 504 := by
  rw [card_orderOf_eq_su_eq_28_mul_stabilizer_of_unique_fixed 6
    unique_fixed_isotropic_of_order_six, card_orderOf_stabilizer_eq 6 a0Pt p0,
    card_orderOf_eq_six_stab_p0]

/-- **There are exactly `1008` elements of order `12` in `SU(3,3)`.** -/
theorem card_orderOf_eq_twelve_su :
    (univ.filter (fun g : specialUnitaryGroup => orderOf g = 12)).card = 1008 := by
  rw [card_orderOf_eq_su_eq_28_mul_stabilizer_of_unique_fixed 12
    unique_fixed_isotropic_of_order_twelve, card_orderOf_stabilizer_eq 12 a0Pt p0,
    card_orderOf_eq_twelve_stab_p0]

end PointStabilizerCounts

end PSU33

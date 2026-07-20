/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.RootGeneration
import Kourovka.Util.PSU33.Cardinality
import Mathlib.Algebra.CharP.Pi
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.NormNum.Prime

/-!
# Point-stabilizer element-order counts for `PSU(3,3)`

Point-stabilizer parametrization and the order `3`, `6`, and `12` counts for
the geometric `SU(3,3)` model.
-/

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

section PointStabilizerCounts

-- The stabilizer parametrization proofs below expand deeply nested finite-field data.
set_option maxRecDepth 1000000

/-- Every vector is a combination of the Hermitian frame, with unique coordinates. -/
lemma frame_coords (x : Fin 3 → F9) :
    ∃ a b c : F9, x = a • fv0 + b • fv1 + c • fw := by
  have h_top : Submodule.span F9 (Set.range ![fv0, fv1, fw]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card frame_indep]
    simp [Module.finrank_fintype_fun_eq_card]
  have hx : x ∈ Submodule.span F9 (Set.range ![fv0, fv1, fw]) := by
    rw [h_top]
    trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c 0, c 1, c 2, by simp [Fin.sum_univ_three]⟩

/-- Coordinates in the Hermitian frame are unique. -/
lemma frame_coords_unique {a b c a' b' c' : F9}
    (h : a • fv0 + b • fv1 + c • fw = a' • fv0 + b' • fv1 + c' • fw) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hli := Fintype.linearIndependent_iff.mp frame_indep
    (fun i ↦ if i = 0 then a - a' else if i = 1 then b - b' else c - c')
  simp_all +decide [Fin.sum_univ_three, Fin.forall_fin_succ, sub_eq_zero]
  exact hli (by
    rw [sub_smul, sub_smul, sub_smul]
    linear_combination' h)

/-- **The point stabilizer has order `216`.** This follows from orbit-stabilizer
for the transitive action on the `28` isotropic points and `|SU(3,3)| = 6048`. -/
theorem card_stabilizer_p0 :
    Nat.card (stabilizer specialUnitaryGroup p0) = 216 := by
  have : IsMultiplyPretransitive specialUnitaryGroup IsotropicPoint 2 :=
    specialUnitaryGroup_twoTransitive
  have : IsPretransitive specialUnitaryGroup IsotropicPoint :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have h_orbit_stabilizer :
      Nat.card (orbit specialUnitaryGroup p0) *
      Nat.card (stabilizer specialUnitaryGroup p0) = Nat.card specialUnitaryGroup := by
    simpa only [Nat.card_prod] using
      Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup specialUnitaryGroup p0)
  have h_orbit : Nat.card (orbit specialUnitaryGroup p0) = 28 := by
    rw [MulAction.orbit_eq_univ specialUnitaryGroup p0, Nat.card_eq_fintype_card]
    simp [card_isotropicPoint]
  rw [h_orbit, card_specialUnitaryGroup] at h_orbit_stabilizer
  omega

/-- Determinant of a special-unitary element expressed in Hermitian-frame
coordinates. -/
lemma frame_det_coords (g : specialUnitaryGroup)
    {x00 x10 x20 x01 x11 x21 x02 x12 x22 : F9}
    (h0 : toLinearEquiv g fv0 = x00 • fv0 + x10 • fv1 + x20 • fw)
    (h1 : toLinearEquiv g fv1 = x01 • fv0 + x11 • fv1 + x21 • fw)
    (h2 : toLinearEquiv g fw = x02 • fv0 + x12 • fv1 + x22 • fw) :
    x00 * (x11 * x22 - x21 * x12) - x01 * (x10 * x22 - x20 * x12)
      + x02 * (x10 * x21 - x20 * x11) = 1 := by
  have h_det : LinearMap.det (toLinearEquiv g).toLinearMap = 1 := by
    simpa +decide [Units.ext_iff] using toLinearEquiv_det g
  let B := basisOfLinearIndependentOfCardEqFinrank frame_indep (by simp +decide)
  -- Express `toLinearEquiv g` as a matrix in the Hermitian frame basis `(fv0, fv1, fw)`.
  -- The matrix has columns `[x00, x10, x20]`, `[x01, x11, x21]`, `[x02, x12, x22]`.
  have hM :
      ∃ M : Matrix (Fin 3) (Fin 3) F9, Matrix.det M = 1 ∧
        ∀ i, ∃ c0 c1 c2 : F9,
          ((toLinearEquiv g).toLinearMap
            (if i = 0 then fv0 else if i = 1 then fv1 else fw) =
            c0 • fv0 + c1 • fv1 + c2 • fw) ∧
          M i 0 = c0 ∧ M i 1 = c1 ∧ M i 2 = c2 := by
    refine ⟨Matrix.of (fun i j =>
        (LinearMap.toMatrix B B (toLinearEquiv g).toLinearMap) j i), ?_, ?_⟩
    · convert h_det using 1
      rw [← LinearMap.det_toMatrix B]
      exact Matrix.det_transpose _
    · intro i
      let x := (toLinearEquiv g) (if i = 0 then fv0 else if i = 1 then fv1 else fw)
      use B.repr x 0, B.repr x 1, B.repr x 2
      simp +decide [LinearMap.toMatrix_apply, x]
      convert B.sum_repr x using 1
      fin_cases i <;> simp +decide [Fin.sum_univ_three, x, B]
      all_goals exact eq_comm
  simp_all +decide [Fin.forall_fin_succ, Matrix.det_fin_three]
  obtain ⟨M, hM₁, hM₂, hM₃, hM₄⟩ := hM
  obtain ⟨rfl, rfl, rfl⟩ := frame_coords_unique hM₂
  obtain ⟨rfl, rfl, rfl⟩ := frame_coords_unique hM₃
  obtain ⟨rfl, rfl, rfl⟩ := frame_coords_unique hM₄
  grind +ring

/-- **Forward structure lemma.** The underlying linear map of a stabilizer element of `p0`
has the explicit triangular form determined by three field parameters `μ, a, c` subject to
one cubic constraint. -/
theorem stab_p0_param (g : specialUnitaryGroup) (hg : g • p0 = p0) :
    ∃ μ a c : F9, μ ≠ 0 ∧ a ^ 3 + μ ^ 2 * a + c ^ 4 * μ ^ 3 = 0 ∧
      toLinearEquiv g fv0 = μ • fv0 ∧
      toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw ∧
      toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw := by
  -- By `su_stab_point_scales`, we get `μ ≠ 0` and a scalar action on `fv0`.
  obtain ⟨μ, hμ_ne_zero, hμ⟩ := su_stab_point_scales g fv0 fv0_ne fv0_iso hg
  -- Decompose the other frame vectors in the fixed Hermitian frame.
  obtain ⟨a, b, c, h1⟩ :
      ∃ a b c : F9, toLinearEquiv g fv1 = a • fv0 + b • fv1 + c • fw :=
    frame_coords _
  obtain ⟨d, e, k, h2⟩ :
      ∃ d e k : F9, toLinearEquiv g fw = d • fv0 + e • fv1 + k • fw :=
    frame_coords _
  -- Using `toLinearEquiv_hermForm`, we get the following equations:
  have h_eq1 : μ * b ^ 3 = 1 := by
    simpa +decide [hμ, h1, hermForm_add_right, conj9_apply, frame_spec] using
      toLinearEquiv_hermForm g fv0 fv1
  have h_eq2 : μ * e ^ 3 = 0 := by
    simpa +decide [hμ, h2, hermForm_add_right, conj9_apply, fv0_iso, fv01, fv0w] using
      toLinearEquiv_hermForm g fv0 fw
  have h_eq3 : k ^ 4 = 1 := by
    have h := toLinearEquiv_hermForm g fw fw
    simp_all +decide [hermForm_add_right, frame_spec]
    rw [show conj9 k = k ^ 3 from conj9_apply k] at h
    linear_combination' h
  have h_eq4 : b * d ^ 3 + c * k ^ 3 = 0 := by
    have := toLinearEquiv_hermForm g fv1 fw
    simp_all +decide [hermForm_add_right, conj9_apply, fv0_iso, fv10, fv0w, fwv0, fv1w, fww]
  have h_eq5 : a * b ^ 3 + a ^ 3 * b + c ^ 4 = 0 := by
    have := toLinearEquiv_hermForm g fv1 fv1
    simp_all +decide [hermForm_add_right, conj9_apply, fv0_iso, fv1_iso, fv01, fv10,
      fv0w, fwv0, fv1w, fwv1, fww]
    linear_combination' this
  have h_eq6 : μ * b * k = 1 := by
    have := frame_det_coords g
      (show toLinearEquiv g fv0 = μ • fv0 + 0 • fv1 + 0 • fw by simpa using hμ)
      (show toLinearEquiv g fv1 = a • fv0 + b • fv1 + c • fw by simpa using h1)
      (show toLinearEquiv g fw = d • fv0 + e • fv1 + k • fw by simpa using h2)
    simp_all +decide [mul_comm, mul_left_comm]
  -- From `h_eq4`, we get `d = -(c ^ 3) * μ ^ 3`.
  have hd : d = -(c ^ 3) * μ ^ 3 := by
    convert congr_arg (· ^ 3) (show d ^ 3 = -c * μ by grind) using 1 <;> ring_nf
    rw [← card_f9, FiniteField.pow_card]
  simp_all +decide [mul_comm, mul_left_comm]
  grind

/-- The stabilizer of an isotropic point in `SU(3,3)` is a finite type. -/
noncomputable instance instFintypeStabilizer (p : IsotropicPoint) :
    Fintype (stabilizer specialUnitaryGroup p) :=
  Fintype.ofFinite _

/-- The faithful linear representation `toLinearEquiv` as a bundled monoid homomorphism. -/
noncomputable def toLinearEquivHomStab :
    specialUnitaryGroup →* ((Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9)) where
  toFun := toLinearEquiv
  map_one' := toLinearEquiv_one
  map_mul' := toLinearEquiv_mul

/-- `toLinearEquiv` is injective: a special-unitary element is determined by its linear map. -/
lemma toLinearEquiv_injective_stab : Function.Injective toLinearEquiv := by
  change Function.Injective toLinearEquivHomStab
  rw [injective_iff_map_eq_one]
  intro g hg
  rwa [← toLinearEquiv_eq_refl_iff_one]

/-- **Injectivity of the Borel parametrization.** A stabilizer element of `p0` is determined by
its action on the frame, hence by its parameters `(μ, a, c)`: if two special-unitary elements
agree on `fv0, fv1, fw` they are equal. -/
lemma stab_p0_param_injective (g h : specialUnitaryGroup)
    (e0 : toLinearEquiv g fv0 = toLinearEquiv h fv0)
    (e1 : toLinearEquiv g fv1 = toLinearEquiv h fv1)
    (e2 : toLinearEquiv g fw = toLinearEquiv h fw) : g = h := by
  apply toLinearEquiv_injective_stab
  ext x
  obtain ⟨a, b, c, rfl⟩ := frame_coords x
  simp only [map_add, map_smul, e0, e1, e2]

open MulAction Finset
open scoped Classical

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- By transitivity, all point stabilizers have the same number of elements of a fixed order. -/
theorem card_orderOf_stabilizer_eq (n : ℕ) (p q : IsotropicPoint) :
    (univ.filter fun g : stabilizer specialUnitaryGroup p => orderOf g = n).card =
      (univ.filter fun g : stabilizer specialUnitaryGroup q => orderOf g = n).card := by
  classical
  have : IsMultiplyPretransitive specialUnitaryGroup IsotropicPoint 2 :=
    specialUnitaryGroup_twoTransitive
  have : IsPretransitive specialUnitaryGroup IsotropicPoint :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let e : stabilizer specialUnitaryGroup p ≃* stabilizer specialUnitaryGroup q :=
    MulAction.stabilizerEquivStabilizerOfOrbitRel <| by
      simpa only [orbitRel_apply] using
        (MulAction.mem_orbit_iff).2 (MulAction.IsPretransitive.exists_smul_eq q p)
  apply Finset.card_nbij' (fun g ↦ e g) (fun g ↦ e.symm g)
  · intro g hg
    simpa only [Finset.mem_coe, mem_filter, mem_univ, true_and, e.orderOf_eq] using hg
  · intro g hg
    simpa only [Finset.mem_coe, mem_filter, mem_univ, true_and, e.symm.orderOf_eq] using hg
  · intro g _
    simp
  · intro g _
    simp

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Counting elements of a fixed order in a point stabilizer is the same as counting
ambient group elements of that order which fix the point. -/
theorem card_orderOf_stabilizer_eq_subset (n : ℕ) (p : IsotropicPoint) :
    (univ.filter fun g : stabilizer specialUnitaryGroup p => orderOf g = n).card =
      (univ.filter fun g : specialUnitaryGroup => orderOf g = n ∧ g • p = p).card := by
  classical
  refine Finset.card_bij (fun g _ => (g : specialUnitaryGroup)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact ⟨orderOf_injective (stabilizer specialUnitaryGroup p).subtype
      Subtype.coe_injective a ▸ ha, (mem_stabilizer_iff).1 a.2⟩
  · exact fun _ _ _ _ hab => Subtype.ext hab
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    refine ⟨⟨b, (mem_stabilizer_iff).2 hb.2⟩, ?_, rfl⟩
    simpa only [mem_filter, mem_univ, true_and] using
      orderOf_injective (stabilizer specialUnitaryGroup p).subtype
        Subtype.coe_injective ⟨b, _⟩ ▸ hb.1

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- If the order of `g` does not divide `8`, then `g` fixes at most one isotropic point. -/
theorem fixed_isotropic_eq_of_not_orderOf_dvd_eight
    (g : specialUnitaryGroup) (hg : ¬ orderOf g ∣ 8)
    {p q : IsotropicPoint} (hp : g • p = p) (hq : g • q = q) : p = q := by
  by_contra hpq
  obtain ⟨h, hhp, hhq⟩ :=
    exists_specialUnitaryGroup_map_isotropic_pair p0 p1 p q p0_ne_p1 hpq
  set k : specialUnitaryGroup := h⁻¹ * g * h with hk
  have hkmem : k ∈ fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint) := by
    rw [mem_fixingSubgroup_iff]
    rintro y (rfl | rfl)
    · rw [hk, mul_smul, mul_smul, hhp, hp, ← hhp, inv_smul_smul]
    · rw [hk, mul_smul, mul_smul, hhq, hq, ← hhq, inv_smul_smul]
  have hord : orderOf k = orderOf g := by
    rw [hk, ← orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective g]
    simp [mul_assoc]
  apply hg
  rw [← hord, ← card_fixingSubgroup_two_eq_eight]
  have := orderOf_dvd_natCard
    (⟨k, hkmem⟩ :
      fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint))
  rwa [← orderOf_injective
      (fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)).subtype
      Subtype.coe_injective ⟨k, hkmem⟩] at this

/-- An order-`3` element fixes some isotropic point. -/
theorem exists_fixed_isotropic_of_order_three
    (u : specialUnitaryGroup) (hu : orderOf u = 3) :
    ∃ p : IsotropicPoint, u • p = p := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpg : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) <| by
      rw [Nat.card_zpowers, hu]
      norm_num
  have hmod := hpg.card_modEq_card_fixedPoints (α := IsotropicPoint)
  rw [Nat.card_eq_fintype_card, card_isotropicPoint] at hmod
  have hne : 0 < Nat.card (fixedPoints (Subgroup.zpowers u) IsotropicPoint) :=
    (Nat.eq_zero_or_pos _).resolve_left fun h => by
      rw [h] at hmod
      norm_num [Nat.ModEq] at hmod
  obtain ⟨a, ha⟩ := (Nat.card_pos_iff.mp hne).1
  exact ⟨a, ha ⟨u, Subgroup.mem_zpowers u⟩⟩

/-- An order-`3` element fixes a unique isotropic point. -/
theorem unique_fixed_isotropic_of_order_three
    (u : specialUnitaryGroup) (hu : orderOf u = 3) :
    ∃! p : IsotropicPoint, u • p = p := by
  obtain ⟨p, hp⟩ := exists_fixed_isotropic_of_order_three u hu
  exact ⟨p, hp, fun q hq =>
    fixed_isotropic_eq_of_not_orderOf_dvd_eight u (by
      rw [hu]
      decide) hq hp⟩

/-- An order-`6` element fixes a unique isotropic point. -/
theorem unique_fixed_isotropic_of_order_six
    (g : specialUnitaryGroup) (hg : orderOf g = 6) :
    ∃! p : IsotropicPoint, g • p = p := by
  obtain ⟨p, hp, hpuniq⟩ := unique_fixed_isotropic_of_order_three (g ^ 2)
    (by
      rw [orderOf_pow, hg]
      decide)
  exact ⟨p,
    hpuniq (g • p) (by
      change (g ^ 2) • (g • p) = g • p
      rw [← mul_smul, show g ^ 2 * g = g * g ^ 2 by group, mul_smul, hp]),
    fun q hq => hpuniq q (by
      change (g ^ 2) • q = q
      rw [pow_two, mul_smul, hq, hq])⟩

/-- An order-`12` element fixes a unique isotropic point. -/
theorem unique_fixed_isotropic_of_order_twelve
    (g : specialUnitaryGroup) (hg : orderOf g = 12) :
    ∃! p : IsotropicPoint, g • p = p := by
  obtain ⟨p, hp, hpuniq⟩ := unique_fixed_isotropic_of_order_three (g ^ 4)
    (by
      rw [orderOf_pow, hg]
      decide)
  exact ⟨p,
    hpuniq (g • p) (by
      change (g ^ 4) • (g • p) = g • p
      rw [← mul_smul, show g ^ 4 * g = g * g ^ 4 by group, mul_smul, hp]),
    fun q hq => hpuniq q (by simp [pow_succ, mul_smul, hq])⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- If every element of order `n` fixes a unique isotropic point, then the global
order-`n` count is `28` times the corresponding count in one point stabilizer. -/
theorem card_orderOf_eq_su_eq_28_mul_stabilizer_of_unique_fixed (n : ℕ)
    (huniq : ∀ g : specialUnitaryGroup, orderOf g = n →
      ∃! p : IsotropicPoint, g • p = p) :
    (univ.filter (fun g : specialUnitaryGroup => orderOf g = n)).card
      = 28 * (univ.filter fun g : stabilizer specialUnitaryGroup a0Pt =>
        orderOf g = n).card := by
  classical
  set F := univ.filter (fun g : specialUnitaryGroup => orderOf g = n) with hF
  set f : specialUnitaryGroup → IsotropicPoint :=
    fun g => if h : orderOf g = n then (huniq g h).choose else a0Pt with hf
  have hfiber (p : IsotropicPoint) : F.filter (fun g => f g = p) =
      univ.filter (fun g : specialUnitaryGroup => orderOf g = n ∧ g • p = p) := by
    ext g
    simp only [hF, mem_filter, mem_univ, true_and]
    refine and_congr_right fun hgn => ?_
    change (if h : orderOf g = n then (huniq g h).choose else a0Pt) = p ↔ g • p = p
    rw [dif_pos hgn]
    exact ⟨fun h => h ▸ (huniq g hgn).choose_spec.1,
      fun hgp => ((huniq g hgn).choose_spec.2 p hgp).symm⟩
  rw [Finset.card_eq_sum_card_fiberwise (fun g _ => mem_univ (f g)),
    Finset.sum_congr rfl fun p _ => by
      rw [hfiber p, ← card_orderOf_stabilizer_eq_subset n p,
        card_orderOf_stabilizer_eq n p a0Pt],
    Finset.sum_const, Finset.card_univ, card_isotropicPoint, smul_eq_mul]

end PointStabilizerCounts

end PSU33

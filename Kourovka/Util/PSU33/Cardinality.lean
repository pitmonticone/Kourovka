/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.ProjectiveAction

/-!
# The order of the geometric `PSU(3,3)`

This file computes `Fintype.card psuPerm = 6048` for the geometric model of
`PSU(3,3)` acting on the `28` isotropic points of the Hermitian polarity over
`GF(9)`, using only structural/geometric data:

* the action is `2`-transitive (`specialUnitaryGroup_twoTransitive`), so by
  `MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq` the pointwise
  stabilizer of a hyperbolic pair of isotropic points has index
  `C(28,2)·2! = 756`;
* that stabilizer is the rescaling torus, of order `q² - 1 = 8` (freeness of the
  action on hyperbolic pairs plus the explicit diagonal torus elements);
* the special unitary group acts faithfully on the isotropic points, so the
  permutation image `psuPerm` has the same order as `SU(3,3)`.

Hence `|psuPerm| = 756 · 8 = 6048`.
-/

namespace PSU33

open PSU33.HermitianForm
open MulAction

/-! ## A fixed Hermitian frame -/

/-- A Hermitian frame: a hyperbolic isotropic pair `(v0, v1)` together with a
unit anisotropic vector `w` orthogonal to both. -/
lemma exists_hermitian_frame : ∃ v0 v1 w : Fin 3 → F9,
    v0 ≠ 0 ∧ v1 ≠ 0 ∧
    hermForm conj9 v0 v0 = 0 ∧ hermForm conj9 v1 v1 = 0 ∧
    hermForm conj9 v0 v1 = 1 ∧ hermForm conj9 v1 v0 = 1 ∧
    hermForm conj9 v0 w = 0 ∧ hermForm conj9 w v0 = 0 ∧
    hermForm conj9 v1 w = 0 ∧ hermForm conj9 w v1 = 0 ∧
    hermForm conj9 w w = 1 ∧ LinearIndependent F9 ![v0, v1, w] := by
  obtain ⟨u, hu0, huiso⟩ := exists_isotropic_ne
  obtain ⟨p, hpiso, hup, hpu⟩ := exists_isotropic_partner u hu0 huiso
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp [hermForm_apply] at hup
  obtain ⟨w, h0w, hw0, h1w, hw1, hww, hindep⟩ :=
    exists_orthogonal_unit u p hu0 huiso hpiso hup hpu
  exact ⟨u, p, w, hu0, hp0, huiso, hpiso, hup, hpu, h0w, hw0, h1w, hw1, hww, hindep⟩

/-- First frame vector. -/
noncomputable def fv0 : Fin 3 → F9 := exists_hermitian_frame.choose
/-- Second frame vector. -/
noncomputable def fv1 : Fin 3 → F9 := exists_hermitian_frame.choose_spec.choose
/-- Anisotropic frame vector. -/
noncomputable def fw : Fin 3 → F9 := exists_hermitian_frame.choose_spec.choose_spec.choose

/-- The defining properties of the chosen Hermitian frame `(fv0, fv1, fw)`. -/
lemma frame_spec :
    fv0 ≠ 0 ∧ fv1 ≠ 0 ∧
    hermForm conj9 fv0 fv0 = 0 ∧ hermForm conj9 fv1 fv1 = 0 ∧
    hermForm conj9 fv0 fv1 = 1 ∧ hermForm conj9 fv1 fv0 = 1 ∧
    hermForm conj9 fv0 fw = 0 ∧ hermForm conj9 fw fv0 = 0 ∧
    hermForm conj9 fv1 fw = 0 ∧ hermForm conj9 fw fv1 = 0 ∧
    hermForm conj9 fw fw = 1 ∧ LinearIndependent F9 ![fv0, fv1, fw] :=
  exists_hermitian_frame.choose_spec.choose_spec.choose_spec

/-- The first frame vector is nonzero. -/
lemma fv0_ne : fv0 ≠ 0 := frame_spec.1

/-- The second frame vector is nonzero. -/
lemma fv1_ne : fv1 ≠ 0 := frame_spec.2.1

/-- The first frame vector is isotropic. -/
lemma fv0_iso : hermForm conj9 fv0 fv0 = 0 := frame_spec.2.2.1

/-- The second frame vector is isotropic. -/
lemma fv1_iso : hermForm conj9 fv1 fv1 = 0 := frame_spec.2.2.2.1

/-- The frame pair `(fv0, fv1)` is hyperbolic. -/
lemma fv01 : hermForm conj9 fv0 fv1 = 1 := frame_spec.2.2.2.2.1

/-- The frame pair `(fv1, fv0)` is hyperbolic. -/
lemma fv10 : hermForm conj9 fv1 fv0 = 1 := frame_spec.2.2.2.2.2.1

/-- `fv0` is orthogonal to the anisotropic vector `fw`. -/
lemma fv0w : hermForm conj9 fv0 fw = 0 := frame_spec.2.2.2.2.2.2.1

/-- The anisotropic vector `fw` is orthogonal to `fv0`. -/
lemma fwv0 : hermForm conj9 fw fv0 = 0 := frame_spec.2.2.2.2.2.2.2.1

/-- `fv1` is orthogonal to the anisotropic vector `fw`. -/
lemma fv1w : hermForm conj9 fv1 fw = 0 := frame_spec.2.2.2.2.2.2.2.2.1

/-- The anisotropic vector `fw` is orthogonal to `fv1`. -/
lemma fwv1 : hermForm conj9 fw fv1 = 0 := frame_spec.2.2.2.2.2.2.2.2.2.1

/-- The anisotropic frame vector `fw` is a unit vector. -/
lemma fww : hermForm conj9 fw fw = 1 := frame_spec.2.2.2.2.2.2.2.2.2.2.1

/-- The frame vectors `fv0`, `fv1`, `fw` are linearly independent. -/
lemma frame_indep : LinearIndependent F9 ![fv0, fv1, fw] :=
  frame_spec.2.2.2.2.2.2.2.2.2.2.2

/-- The isotropic point with representative `v`. -/
noncomputable def mkIso (v : Fin 3 → F9) (hv : v ≠ 0) (hvi : hermForm conj9 v v = 0) :
    IsotropicPoint :=
  ⟨Projectivization.mk F9 v hv, (isotropicProj_mk_iff v hv).2 hvi⟩

/-- The first isotropic point of the frame. -/
noncomputable def p0 : IsotropicPoint := mkIso fv0 fv0_ne fv0_iso

/-- The second isotropic point of the frame. -/
noncomputable def p1 : IsotropicPoint := mkIso fv1 fv1_ne fv1_iso

/-- The two frame isotropic points `p0` and `p1` are distinct. -/
lemma p0_ne_p1 : p0 ≠ p1 := by
  intro h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff F9 fv0 fv1 fv0_ne fv1_ne).1
    (congrArg Subtype.val h)
  rw [Units.smul_def] at hc
  have : hermForm conj9 fv0 fv1 = 0 := by rw [← hc, hermForm_smul_left, fv1_iso, mul_zero]
  exact one_ne_zero (fv01 ▸ this)

/-! ## Scalar action on the frame points -/

/-- An element of `SU` fixing the isotropic point `⟨v⟩` scales the representative
`v` by a nonzero scalar. -/
lemma su_stab_point_scales (g : specialUnitaryGroup) (v : Fin 3 → F9) (hv : v ≠ 0)
    (hvi : hermForm conj9 v v = 0)
    (hg : g • mkIso v hv hvi = mkIso v hv hvi) :
    ∃ μ : F9, μ ≠ 0 ∧ toLinearEquiv g v = μ • v := by
  have h1 := congrArg Subtype.val hg
  rw [mkIso, su_smul_fst] at h1
  simp only at h1
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h1
  obtain ⟨c, hc⟩ := h1
  rw [Units.smul_def] at hc
  exact ⟨(c : F9), c.ne_zero, hc.symm⟩

/-! ## The two-point stabilizer is the torus of order 8 -/

set_option maxHeartbeats 1000000 in
/-- **Explicit diagonal torus element.** For a fourth-power-trivial unit
parameter, an explicit special-unitary element scales the frame diagonally:
`v0 ↦ a·v0`, `v1 ↦ a⁻³·v1`, `w ↦ a²·w`. Together with freeness this realizes
the whole rescaling torus of the two isotropic points `⟨v0⟩, ⟨v1⟩`. -/
lemma exists_su_frame_diag (a : F9ˣ) :
    ∃ g : specialUnitaryGroup,
      toLinearEquiv g fv0 = (a : F9) • fv0 ∧
      toLinearEquiv g fv1 = ((a : F9) ^ 3)⁻¹ • fv1 ∧
      toLinearEquiv g fw = ((a : F9) ^ 2) • fw := by
  obtain ⟨g, hg⟩ :
      ∃ g : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9),
        g fv0 = a • fv0 ∧
        g fv1 = (a ^ 3)⁻¹ • fv1 ∧
        g fw = a ^ 2 • fw := by
    use (basisOfLinearIndependentOfCardEqFinrank frame_indep (by norm_num)).equiv
      ((basisOfLinearIndependentOfCardEqFinrank frame_indep (by norm_num)).unitsSMul
        ![a, (a ^ 3)⁻¹, a ^ 2]) (Equiv.refl (Fin 3))
    generalize_proofs at *
    simp +decide [basisOfLinearIndependentOfCardEqFinrank] at *
    simp +decide [Module.Basis.equiv, Module.Basis.unitsSMul] at *
    have h_repr :
        frame_indep.repr ⟨fv0, by
          exact Submodule.subset_span (Set.mem_range_self 0)⟩ = Finsupp.single 0 1 ∧
        frame_indep.repr ⟨fv1, by
          exact Submodule.subset_span (Set.mem_range.mpr ⟨1, rfl⟩)⟩ = Finsupp.single 1 1 ∧
        frame_indep.repr ⟨fw, by
          exact Submodule.subset_span (Set.mem_range_self 2)⟩ = Finsupp.single 2 1 := by
      all_goals generalize_proofs at *
      exact ⟨LinearIndependent.repr_eq_single frame_indep 0 _ rfl,
        LinearIndependent.repr_eq_single frame_indep 1 _ rfl,
        LinearIndependent.repr_eq_single frame_indep 2 _ rfl⟩
    generalize_proofs at *
    simp +decide [h_repr]
  have hg_preserves : ∀ u v : Fin 3 → F9, hermForm conj9 (g u) (g v) = hermForm conj9 u v := by
    intro u v
    have h_basis :
        ∃ (u0 u1 u2 v0 v1 v2 : F9),
          u = u0 • fv0 + u1 • fv1 + u2 • fw ∧
          v = v0 • fv0 + v1 • fv1 + v2 • fw := by
      have h_basis :
          ∀ u : Fin 3 → F9,
            ∃ (u0 u1 u2 : F9), u = u0 • fv0 + u1 • fv1 + u2 • fw := by
        intro u
        have h_basis : u ∈ Submodule.span F9 {fv0, fv1, fw} := by
          have h_basis : Submodule.span F9 {fv0, fv1, fw} = ⊤ := by
            refine Submodule.eq_top_of_finrank_eq ?_
            rw [finrank_span_set_eq_card] <;> norm_num [frame_indep]
            · grind +locals
            · convert frame_indep.linearIndepOn_id using 1
              aesop
          aesop
        rw [Submodule.mem_span_insert] at h_basis
        rcases h_basis with ⟨a, z, hz, rfl⟩
        rw [Submodule.mem_span_pair] at hz
        obtain ⟨b, c, rfl⟩ := hz
        exact ⟨a, b, c, by ring⟩
      exact ⟨_, _, _, _, _, _,
        h_basis u |> Classical.choose_spec |> Classical.choose_spec |> Classical.choose_spec,
        h_basis v |> Classical.choose_spec |> Classical.choose_spec |> Classical.choose_spec⟩
    obtain ⟨u0, u1, u2, v0, v1, v2, rfl, rfl⟩ := h_basis
    simp +decide [*, hermForm_add_right]
    ring_nf
    have h_a_pow : (a : F9) ^ 8 = 1 := by
      convert FiniteField.pow_card_sub_one_eq_one (a : F9) _ using 1
      · rw [card_f9]
      · exact Units.ne_zero a
    simp_all +decide [Units.smul_def]
    simp_all +decide [conj9_apply, pow_succ, mul_assoc]
    simp_all +decide [mul_assoc, mul_comm, mul_left_comm, pow_three, pow_two]
    simp_all +decide [
      show hermForm conj9 fv0 fv0 = 0 from fv0_iso,
      show hermForm conj9 fv1 fv1 = 0 from fv1_iso,
      show hermForm conj9 fv0 fv1 = 1 from fv01,
      show hermForm conj9 fv1 fv0 = 1 from fv10,
      show hermForm conj9 fv0 fw = 0 from fv0w,
      show hermForm conj9 fw fv0 = 0 from fwv0,
      show hermForm conj9 fv1 fw = 0 from fv1w,
      show hermForm conj9 fw fv1 = 0 from fwv1,
      show hermForm conj9 fw fw = 1 from fww]
  have hg_det : LinearEquiv.det g = 1 := by
    have hg_det : LinearEquiv.det g = (a : F9) * ((a ^ 3)⁻¹ : F9) * (a ^ 2 : F9) := by
      have h_det :
          LinearEquiv.det g =
            Matrix.det (LinearMap.toMatrix
              (basisOfLinearIndependentOfCardEqFinrank frame_indep (by simp))
              (basisOfLinearIndependentOfCardEqFinrank frame_indep (by simp))
              (g : (Fin 3 → F9) →ₗ[F9] (Fin 3 → F9))) := by
        convert rfl
        convert LinearMap.det_toMatrix
          (basisOfLinearIndependentOfCardEqFinrank frame_indep (by simp)) _ using 1
        exact LinearEquiv.coe_det g
      rw [h_det, Matrix.det_of_upperTriangular]
      · simp +decide [Fin.prod_univ_three, LinearMap.toMatrix_apply]
        simp +decide [hg, LinearMap.codRestrict]
        erw [LinearIndependent.repr_eq, LinearIndependent.repr_eq, LinearIndependent.repr_eq]
        rotate_left
        exact Finsupp.single 2 (a ^ 2)
        rotate_left
        exact Finsupp.single 1 ((a ^ 3)⁻¹ : F9)
        rotate_left
        exact Finsupp.single 0 (a : F9)
        · exact Finsupp.linearCombination_single F9 (a : F9) 0
        · simp +decide
        · simp +decide [Finsupp.linearCombination_apply]
          norm_cast
        · simp +decide [Finsupp.linearCombination_apply]
          norm_cast
      · intro i j hij
        simp_all +decide [LinearMap.toMatrix_apply, basisOfLinearIndependentOfCardEqFinrank]
        fin_cases i <;> fin_cases j <;> simp_all +decide
        · erw [LinearIndependent.repr_eq] <;> norm_num [frame_indep]
          rotate_left
          exact Finsupp.single 0 (a : F9)
          · exact Finsupp.linearCombination_single F9 (a : F9) 0
          · exact Finsupp.single_eq_of_ne (by decide)
        · rw [LinearIndependent.repr_eq]
          rotate_left
          exact Finsupp.single 0 (a : F9)
          · simp [Finsupp.linearCombination_apply]
            rfl
          · grind
        · erw [LinearIndependent.repr_eq]
          rotate_left
          exact Finsupp.single 1 ((a ^ 3)⁻¹ : F9)
          · simp +decide [Finsupp.linearCombination_apply]
            norm_cast
          · grind
    have hg_det_simplified : (a : F9) * ((a ^ 3)⁻¹ : F9) * (a ^ 2 : F9) = 1 := by
      field_simp
    exact Units.ext <| hg_det.trans hg_det_simplified
  refine ⟨mkSpecialUnitary g hg_preserves hg_det, ?_, ?_, ?_⟩ <;>
    simp_all +decide [toLinearEquiv]
  · convert hg.1 using 1
  · convert hg.2.1 using 1
    norm_cast
  · convert hg.2.2 using 1

/-- An `SU` element scaling the representative `v` of an isotropic point by a
nonzero scalar fixes that point. -/
lemma su_smul_mkIso_of_scale (g : specialUnitaryGroup) (v : Fin 3 → F9)
    (hv : v ≠ 0) (hvi : hermForm conj9 v v = 0) (a : F9) (ha : a ≠ 0)
    (hsc : toLinearEquiv g v = a • v) :
    g • mkIso v hv hvi = mkIso v hv hvi := by
  apply Subtype.ext
  rw [su_smul_fst, mkIso]
  simp only
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 a ha, by
    rw [Units.smul_def, Units.val_mk0]
    exact hsc.symm⟩

/-- The scalar by which a two-point-stabilizing element scales `fv1` is forced by
the `fv0` scalar via unitarity: if `toLinearEquiv g fv0 = a • fv0` and
`toLinearEquiv g fv1 = b • fv1` with `a ≠ 0`, then `b = (a ^ 3)⁻¹`. -/
lemma su_fix_two_fv1_scale (g : specialUnitaryGroup) (a b : F9)
    (h0 : toLinearEquiv g fv0 = a • fv0) (h1 : toLinearEquiv g fv1 = b • fv1) :
    b = (a ^ 3)⁻¹ := by
  have hform := toLinearEquiv_hermForm g fv0 fv1
  rw [h0, h1, hermForm_smul_left, hermForm_smul_right, fv01, mul_one, conj9_apply] at hform
  -- hform : a * b ^ 3 = 1
  have hb : b ^ 3 = a⁻¹ := eq_inv_of_mul_eq_one_left (by
    rw [mul_comm]
    exact hform)
  have hb9 : ∀ x : F9, x ^ 9 = x := fun x => by
    rw [← card_f9]
    exact FiniteField.pow_card x
  have hbb : b = (b ^ 3) ^ 3 := by
    rw [← pow_mul]
    exact (hb9 b).symm
  rw [hbb, hb, inv_pow]

/-- **Freeness + torus.** The pointwise stabilizer of the two isotropic points
`{p0, p1}` inside `SU(3,3)` is the rescaling torus, of order `q² - 1 = 8`. -/
theorem card_fixingSubgroup_two_eq_eight :
    Nat.card (fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)) = 8 := by
  rw [← card_units_F9]
  have h_forward :
      ∃ toFun : ↥(fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)) → F9ˣ,
        Function.Bijective toFun := by
    have h_forward :
        ∀ g : specialUnitaryGroup,
          g ∈ fixingSubgroup specialUnitaryGroup
            ({p0, p1} : Set IsotropicPoint) →
          ∃ μ : F9ˣ,
            toLinearEquiv g fv0 = (μ : F9) • fv0 ∧
            toLinearEquiv g fv1 = ((μ : F9) ^ 3)⁻¹ • fv1 := by
      intro g hg
      obtain ⟨μ, hμ⟩ : ∃ μ : F9, μ ≠ 0 ∧ toLinearEquiv g fv0 = μ • fv0 := by
        apply su_stab_point_scales
        all_goals norm_num [mem_fixingSubgroup_iff] at *
        exact hg.1
        exact fv0_ne
      have hμ1 : ∃ ν : F9, ν ≠ 0 ∧ toLinearEquiv g fv1 = ν • fv1 := by
        apply su_stab_point_scales
        convert hg using 1
        all_goals norm_num [p0, p1, mkIso]
        all_goals norm_num [mem_fixingSubgroup_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        all_goals try exact fv1_ne
        all_goals try exact fv1_iso
        exact fun h => hg ⟨p0, by simp +decide [p0]⟩
      obtain ⟨ν, hν⟩ := hμ1
      exact ⟨Units.mk0 μ hμ.1, hμ.2,
        by simpa [su_fix_two_fv1_scale g μ ν hμ.right hν.right] using hν.2⟩
    choose! μ hμ using h_forward
    refine ⟨fun g => μ g, ?_, ?_⟩
    · intro g h hgh
      have h_eq :
          toLinearEquiv g fv0 = toLinearEquiv h fv0 ∧
          toLinearEquiv g fv1 = toLinearEquiv h fv1 := by
        grind
      have h_eq :
          toLinearEquiv (g⁻¹ * h) fv0 = fv0 ∧
          toLinearEquiv (g⁻¹ * h) fv1 = fv1 := by
        simp +decide [toLinearEquiv_mul_apply]
        simp +decide [← h_eq, toLinearEquiv_inv_apply]
      have h_eq : (g⁻¹ * h : specialUnitaryGroup) = 1 := by
        apply su_fixing_hyperbolic_pair_eq_one
        exact fv0_iso
        exact fv1_iso
        · exact fv01
        · exact fv10
        · exact h_eq.1
        · exact h_eq.2
      exact Subtype.ext (inv_mul_eq_one.mp h_eq)
    · intro a
      obtain ⟨g, hg⟩ := exists_su_frame_diag a
      use ⟨g, by
          simp +decide [fixingSubgroup]
          simp +decide [fixingSubmonoid]
          exact ⟨su_smul_mkIso_of_scale g fv0 fv0_ne fv0_iso _ (Units.ne_zero _) hg.1,
            su_smul_mkIso_of_scale g fv1 fv1_ne fv1_iso _
              (by simp +decide [Units.ne_zero]) hg.2.1⟩⟩
      generalize_proofs at *
      have := hμ g ‹_›
      simp_all +decide [funext_iff, Fin.forall_fin_succ]
      have h_fv0_ne_zero : fv0 ≠ 0 := fv0_ne
      exact Units.ext (by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h_fv0_ne_zero
        fin_cases i <;> aesop)
  exact Nat.card_congr (Equiv.ofBijective _ h_forward.choose_spec)

/-! ## Faithfulness of the action -/

/-- **Faithfulness core.** A special unitary element fixing every isotropic
point is the identity. -/
lemma su_fixes_all_isotropic_points_eq_one (g : specialUnitaryGroup)
    (h : ∀ p : IsotropicPoint, g • p = p) : g = 1 := by
  obtain ⟨α, hα⟩ : ∃ α : F9, α ≠ 0 ∧ toLinearEquiv g fv0 = α • fv0 :=
    su_stab_point_scales g fv0 fv0_ne fv0_iso (h _)
  obtain ⟨β, hβ⟩ : ∃ β : F9, β ≠ 0 ∧ toLinearEquiv g fv1 = β • fv1 :=
    su_stab_point_scales g fv1 fv1_ne fv1_iso (h (mkIso fv1 fv1_ne fv1_iso))
  obtain ⟨γ, hγ⟩ : ∃ γ : F9, toLinearEquiv g fw = γ • fw := by
    have h_ortho :
        hermForm conj9 (toLinearEquiv g fw) fv0 = 0 ∧
        hermForm conj9 (toLinearEquiv g fw) fv1 = 0 := by
      have hfw0 := toLinearEquiv_hermForm g fw fv0
      have hfw1 := toLinearEquiv_hermForm g fw fv1
      simp_all +decide
      simp_all +decide [fwv0, fwv1]
    have h_basis : ∀ x : Fin 3 → F9, ∃ a b c : F9, x = a • fv0 + b • fv1 + c • fw := by
      intro x
      have h_basis : x ∈ Submodule.span F9 (Set.range ![fv0, fv1, fw]) := by
        have h_basis : Submodule.span F9 (Set.range ![fv0, fv1, fw]) = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [finrank_span_eq_card] <;> norm_num [frame_indep]
        aesop
      rw [Submodule.mem_span_range_iff_exists_fun] at h_basis
      obtain ⟨c, rfl⟩ := h_basis
      exact ⟨c 0, c 1, c 2, by simp +decide [Fin.sum_univ_three]⟩
    obtain ⟨a, b, c, h⟩ := h_basis (toLinearEquiv g fw)
    simp_all +decide
    simp_all +decide [fv0_iso, fv1_iso, fv01, fv10, fwv0, fwv1]
    exact ⟨c, rfl⟩
  obtain ⟨δ, hδ⟩ :
      ∃ δ : F9,
        δ ≠ 0 ∧ toLinearEquiv g (fv0 + fv1 + fw) = δ • (fv0 + fv1 + fw) := by
    apply su_stab_point_scales
    exact h _
    · have := frame_indep
      simp_all +decide [linearIndependent_iff']
      specialize this {0, 1, 2} (fun i => if i = 0 then 1 else if i = 1 then 1 else 1)
      simp_all +decide
      simpa only [add_assoc] using this
    · simp +decide [hermForm_add_right, fv0_iso, fv1_iso, fww, fv01, fv10,
        fv0w, fwv0, fv1w, fwv1]
      grind
  have h_eq : α = δ ∧ β = δ ∧ γ = δ := by
    have h_eq : α • fv0 + β • fv1 + γ • fw = δ • (fv0 + fv1 + fw) := by
      rw [← hα.2, ← hβ.2, ← hγ, ← hδ.2, map_add, map_add]
    have h_eq : (α - δ) • fv0 + (β - δ) • fv1 + (γ - δ) • fw = 0 := by
      convert sub_eq_zero.mpr h_eq using 1
      simp +decide [sub_smul]
      abel1
    have := Fintype.linearIndependent_iff.mp frame_indep
    specialize this (fun i => if i = 0 then α - δ else if i = 1 then β - δ else γ - δ)
    simp_all +decide [Fin.sum_univ_three]
    exact ⟨sub_eq_zero.mp (this 0), sub_eq_zero.mp (this 1), sub_eq_zero.mp (this 2)⟩
  have h_det : α ^ 3 = 1 := by
    have h_det : LinearEquiv.det (toLinearEquiv g) = α ^ 3 := by
      convert LinearEquiv.coe_det (toLinearEquiv g) using 1
      rw [← LinearMap.det_toMatrix
        (basisOfLinearIndependentOfCardEqFinrank frame_indep (by simp +decide))]
      rw [Matrix.det_fin_three]
      simp +decide [LinearMap.toMatrix_apply, hα, hβ, hγ, h_eq]
      erw [LinearIndependent.repr_eq, LinearIndependent.repr_eq, LinearIndependent.repr_eq]
      rotate_left
      exact Finsupp.single 2 1
      rotate_left
      exact Finsupp.single 1 1
      rotate_left
      exact Finsupp.single 0 1
      · simp +decide [Finsupp.linearCombination_apply]
      · simp +decide
        ring
      · simp +decide [Finsupp.linearCombination_apply]
      · simp +decide [Finsupp.linearCombination_apply]
    rw [← h_det, toLinearEquiv_det]
    norm_num
  have h_unit : α * conj9 α = 1 := by
    have h_unitarity :
        hermForm conj9 (toLinearEquiv g fv0) (toLinearEquiv g fv1) =
        hermForm conj9 fv0 fv1 :=
      toLinearEquiv_hermForm g fv0 fv1
    simp_all +decide
    simp_all +decide [mul_comm, fv01]
  have h_alpha_one : α = 1 := (eq_one_iff_eq_one_of_mul_eq_one h_unit).mpr h_det
  simp_all +decide
  exact su_fixing_hyperbolic_pair_eq_one g fv0 fv1 fv0_iso fv1_iso fv01 fv10
    (by simpa [← h_eq.1] using hα) (by simpa [← h_eq.1] using hβ)

/-- **Faithfulness.**  The special unitary group acts faithfully on the isotropic
points; equivalently the corestricted permutation homomorphism `toPsu` is
injective. -/
theorem toPsu_injective : Function.Injective toPsu := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine su_fixes_all_isotropic_points_eq_one g fun p => ?_
  rw [← toPsu_smul, hg, one_smul]

/-- `SU(3,3)` is finite: it injects into the finite permutation group `psuPerm`. -/
noncomputable instance instFiniteSpecialUnitaryGroup : Finite specialUnitaryGroup :=
  Finite.of_injective toPsu toPsu_injective

/-- `SU(3,3)` is a `Fintype`. -/
noncomputable instance instFintypeSpecialUnitaryGroup : Fintype specialUnitaryGroup :=
  Fintype.ofFinite _

/-! ## The order of `psuPerm` -/

/-- `psuPerm` is a `Fintype`. -/
noncomputable instance : Fintype psuPerm := Fintype.ofFinite _

/-- The index of the two-point stabilizer is `C(28,2)·2! = 756`. -/
lemma index_fixingSubgroup_two :
    (fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)).index = 756 := by
  have hncard : ({p0, p1} : Set IsotropicPoint).ncard = 2 := Set.ncard_pair p0_ne_p1
  have h2 :
      IsMultiplyPretransitive specialUnitaryGroup IsotropicPoint
        (({p0, p1} : Set IsotropicPoint).ncard) := by
    rw [hncard]
    exact specialUnitaryGroup_twoTransitive
  have hcard : Nat.card IsotropicPoint = 28 :=
    Nat.card_eq_fintype_card.trans card_isotropicPoint
  have := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq
    (G := specialUnitaryGroup) (α := IsotropicPoint)
    ({p0, p1} : Set IsotropicPoint) h2
  rw [hncard, hcard] at this
  rw [this]
  decide

/-- The order of `SU(3,3)` is `6048`. -/
theorem card_specialUnitaryGroup : Nat.card specialUnitaryGroup = 6048 := by
  rw [← Subgroup.card_mul_index
      (fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)),
    card_fixingSubgroup_two_eq_eight, index_fixingSubgroup_two]

/-- The `card` of `Finset.univ` for `SU(3,3)` is `6048`. -/
theorem card_univ_specialUnitaryGroup :
    (Finset.univ : Finset specialUnitaryGroup).card = 6048 := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact card_specialUnitaryGroup

/-- **The order of `psuPerm` is `6048`.** -/
theorem card_psuPerm : Fintype.card psuPerm = 6048 := by
  rw [← Nat.card_eq_fintype_card,
    (Nat.card_congr (Equiv.ofBijective toPsu ⟨toPsu_injective, toPsu_surjective⟩)).symm,
    card_specialUnitaryGroup]

end PSU33

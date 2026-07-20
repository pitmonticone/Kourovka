/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.Reflections

/-!
# Order-four count for `PSU(3,3)`

This file computes the order-four elements from the squaring fibers over
Hermitian reflections.
-/

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

section InvolutionOrderFourCount

/-! ## The standard anisotropic vector `e2` and the base involution `r0` -/

/-- The third standard basis vector, a unit anisotropic vector. -/
noncomputable def e2vec : Fin 3 → F9 := Pi.single 2 1

/-- The vector `e2vec` has Hermitian norm one. -/
lemma e2vec_norm : hermForm conj9 e2vec e2vec = 1 := by
  simp [e2vec, hermForm_apply, conj9_apply, Fin.sum_univ_three]

/-- The vector `e2vec` is anisotropic. -/
lemma e2vec_aniso : hermForm conj9 e2vec e2vec ≠ 0 := e2vec_norm ▸ one_ne_zero

/-- The base involution: the Hermitian reflection in `e2`. -/
noncomputable def r0 : specialUnitaryGroup := reflSU e2vec e2vec_aniso

/-! ## Group-theoretic reduction lemmas -/

/-- If `x ^ 2 = r` for an involution `r`, then `x` has order exactly `4`. -/
lemma order_four_of_square (x r : specialUnitaryGroup) (hr : orderOf r = 2)
    (hx : x ^ 2 = r) : orderOf x = 4 := by
  have h_order_x : orderOf x ∣ 4 ∧ ¬orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, orderOf_dvd_iff_pow_eq_one]
    have := pow_orderOf_eq_one r
    simp_all +decide [pow_succ, mul_assoc]
    aesop
  have := Nat.le_of_dvd (by decide) h_order_x.1
  interval_cases orderOf x <;> trivial

/-- The fiber over an involution under squaring coincides with the set of square
roots, since every square root automatically has order `4`. -/
lemma fiber_eq (r : specialUnitaryGroup) (hr : orderOf r = 2) :
    (univ.filter (fun x : specialUnitaryGroup => orderOf x = 4 ∧ x ^ 2 = r))
      = (univ.filter (fun x : specialUnitaryGroup => x ^ 2 = r)) := by
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨order_four_of_square x r hr h, h⟩⟩

/-- Conjugating a Hermitian reflection: `g * reflSU w * g⁻¹ = reflSU (g • w)`. -/
lemma conj_reflSU (g : specialUnitaryGroup) (w : Fin 3 → F9)
    (hn : hermForm conj9 w w ≠ 0)
    (hn' : hermForm conj9 (toLinearEquiv g w) (toLinearEquiv g w) ≠ 0) :
    g * reflSU w hn * g⁻¹ = reflSU (toLinearEquiv g w) hn' := by
  refine specialUnitaryGroup_ext ?_
  ext x
  simp +decide [toLinearEquiv_mul_apply, toLinearEquiv_inv_apply, toLinearEquiv_reflSU,
    reflEquiv_apply, reflMap_apply]
  have := toLinearEquiv_hermForm g ((toLinearEquiv g).symm x) w
  simp_all +decide [hermForm_apply]
  exact Or.inl <| Or.inl <| by simpa [mul_comm] using Eq.symm <| toLinearEquiv_hermForm g w w

set_option maxHeartbeats 1000000 in
/-- The fiber cardinality is conjugation-invariant. -/
lemma card_fiber_conj (a r : specialUnitaryGroup) :
    (univ.filter (fun x : specialUnitaryGroup => x ^ 2 = a * r * a⁻¹)).card
      = (univ.filter (fun x : specialUnitaryGroup => x ^ 2 = r)).card := by
  fapply Finset.card_bij'
  use fun x hx => a⁻¹ * x * a
  use fun x hx => a * x * a⁻¹
  · simp +decide [mul_assoc, sq]
    simp_all +decide [← mul_assoc]
  · aesop
  · simp +decide [mul_assoc]
  · simp +decide [mul_assoc]

/-! ## Transitivity on anisotropic lines -/

set_option maxHeartbeats 1000000 in
/-- A unit anisotropic vector extends to an orthonormal basis whose last vector
is it (Gram matrix equal to the standard orthonormal one). -/
lemma exists_orthonormal_basis_last (w : Fin 3 → F9) (hw1 : hermForm conj9 w w = 1) :
    ∃ b : Module.Basis (Fin 3) F9 (Fin 3 → F9), b 2 = w ∧
      (∀ i j, hermForm conj9 (b i) (b j)
        = hermForm conj9 (Pi.single i 1) (Pi.single j 1)) := by
  obtain ⟨a0, a1, ha0, ha1, h_ortho⟩ :
      ∃ a0 a1 : Fin 3 → F9,
        hermForm conj9 a0 a0 = 1 ∧
        hermForm conj9 a1 a1 = 1 ∧
        ∀ i j : Fin 3,
          hermForm conj9
            (if i = 0 then a0 else if i = 1 then a1 else w)
            (if j = 0 then a0 else if j = 1 then a1 else w) =
          if i = j then 1 else 0 := by
    obtain ⟨a0, ha0⟩ :
        ∃ a0 : Fin 3 → F9, hermForm conj9 a0 a0 = 1 ∧
          hermForm conj9 a0 w = 0 := by
      -- Choose u0 among the standard basis vectors so that P u0 ≠ 0.
      obtain ⟨u0, hu0⟩ :
          ∃ u0 : Fin 3 → F9,
            u0 ≠ 0 ∧ hermForm conj9 u0 w = 0 ∧ hermForm conj9 u0 u0 ≠ 0 := by
        have h_orthogonal : ∃ u0 : Fin 3 → F9, u0 ≠ 0 ∧ hermForm conj9 u0 w = 0 := by
          simp only [hermForm_apply] at *
          by_cases hw0 : w 0 = 0
          · use fun i => if i = 0 then 1 else 0
            simp_all +decide [funext_iff]
          · use ![-conj9 (w 1), conj9 (w 0), 0]
            simp_all +decide [Fin.sum_univ_three]
            ring
        obtain ⟨u0, hu0⟩ := h_orthogonal
        by_cases hu0' : hermForm conj9 u0 u0 = 0 <;> simp_all +decide
        · obtain ⟨u1, hu1⟩ :
              ∃ u1 : Fin 3 → F9,
              hermForm conj9 u1 w = 0 ∧ hermForm conj9 u1 u0 ≠ 0 := by
            by_contra h_contra
            push_neg at h_contra
            have h_orthogonal : ∀ u1 : Fin 3 → F9, hermForm conj9 u1 u0 = 0 := by
              intro u1
              by_cases hu1 : hermForm conj9 u1 w = 0
              · exact h_contra u1 hu1
              · have := h_contra (u1 - (hermForm conj9 u1 w) • w) ?_ <;>
                  simp_all +decide
                simp_all +decide [hermForm_apply]
                have hwu0 : ∑ i, w i * conj9 (u0 i) = 0 := by
                  have h_orthogonal :
                      ∑ i, w i * conj9 (u0 i) =
                      conj9 (∑ i, u0 i * conj9 (w i)) := by
                    rw [map_sum]
                    exact Finset.sum_congr rfl fun i _ => by
                      rw [map_mul, conj9_involutive]
                      ring
                  rw [h_orthogonal, hu0.2, map_zero]
                linear_combination this + (∑ i, u1 i * conj9 (w i)) * hwu0
            exact hu0.1 (hermForm_right_nondegen u0 h_orthogonal)
          obtain ⟨c, hc⟩ :
              ∃ c : F9,
              hermForm conj9 (u1 + c • u0) (u1 + c • u0) ≠ 0 := by
            by_contra! h
            have := h 0
            have := h 1
            have := h (-1)
            simp_all +decide
            simp_all +decide [hermForm_apply, Fin.sum_univ_three]
            grind
          refine ⟨u1 + c • u0, ?_, ?_, hc⟩
          · intro h0
            apply hc
            rw [h0]
            simp
          · rw [hermForm_add_left, hermForm_smul_left, hu1.1, hu0.2, mul_zero, add_zero]
        · exact ⟨u0, hu0.1, hu0.2, hu0'⟩
      obtain ⟨s, hs⟩ : ∃ s : F9, s ≠ 0 ∧ s ^ 4 * hermForm conj9 u0 u0 = 1 := by
        have := @exists_fourth_root (hermForm conj9 u0 u0)⁻¹ ?_ <;>
          simp_all +decide
        · exact ⟨this.choose, this.choose_spec.2, by
            rw [this.choose_spec.1, inv_mul_cancel₀ hu0.2.2]⟩
        · have := hermForm_self_cases u0
          aesop
      refine ⟨s • u0, ?_, ?_⟩ <;>
        simp_all +decide
      grind [conj9_apply]
    obtain ⟨a1, ha1⟩ :
        ∃ a1 : Fin 3 → F9,
          hermForm conj9 a1 a1 = 1 ∧ hermForm conj9 a1 w = 0 ∧
          hermForm conj9 a1 a0 = 0 := by
      -- Use the Hermitian cross product of `a0` and `w`.
      use ![conj9 (a0 1 * w 2 - a0 2 * w 1),
        conj9 (a0 2 * w 0 - a0 0 * w 2),
        conj9 (a0 0 * w 1 - a0 1 * w 0)]
      simp only [hermForm_apply] at *
      simp_all +decide [Fin.sum_univ_three]
      grind [conj9_apply]
    use a0, a1
    have h_conj_symm :
        ∀ u v : Fin 3 → F9, hermForm conj9 u v = conj9 (hermForm conj9 v u) :=
      fun u v => (hermForm_conj_symm conj9_involutive v u).symm
    grind +ring
  have h_lin_ind : LinearIndependent F9 ![a0, a1, w] := by
    refine Fintype.linearIndependent_iff.2 ?_
    intro g hg i
    fin_cases i <;> simp_all +decide [Fin.sum_univ_three]
    · have := congr_arg (fun x => hermForm conj9 x a0) hg
      norm_num [ha0, ha1, hw1, hermForm_add_left, hermForm_smul_left] at this
      simp_all +decide [Fin.forall_fin_succ, hermForm_apply]
    · have := congr_arg (fun x => hermForm conj9 x a1) hg
      norm_num [ha0, ha1, hw1, hermForm_add_left, hermForm_smul_left] at this
      simp_all +decide [Fin.forall_fin_succ, hermForm_apply]
    · replace hg := congr_arg (fun x => hermForm conj9 x w) hg
      simp_all +decide
      simp_all +decide [Fin.forall_fin_succ, hermForm_apply]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank h_lin_ind ?_, ?_, ?_⟩ <;>
    simp_all +decide [Fin.forall_fin_succ]
  simp +decide [hermForm_apply, Pi.single_apply]

/-- **Transitivity on anisotropic lines.** For any anisotropic vector `w` there is
a special-unitary map carrying `e2` to a nonzero multiple of `w`. -/
lemma exists_su_aniso_line (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    ∃ (g : specialUnitaryGroup) (c : F9), c ≠ 0 ∧ toLinearEquiv g e2vec = c • w := by
  -- Let `w' := s • w` where `s ^ 4 = (hermForm conj9 w w)⁻¹`
  obtain ⟨s, hs⟩ : ∃ s : F9, s ≠ 0 ∧ s ^ 4 = (hermForm conj9 w w)⁻¹ := by
    convert exists_fourth_root (hermForm conj9 w w)⁻¹ _ using 1
    · aesop
    · have := hermForm_self_cases w
      aesop
  set w' : Fin 3 → F9 := s • w
  have hw'_norm : hermForm conj9 w' w' = 1 := by
    rw [hermForm_smul_self, mul_comm]
    grind [conj9_apply]
  obtain ⟨b, hb₁, hb₂⟩ := exists_orthonormal_basis_last w' hw'_norm
  -- Let `δ := LinearEquiv.det f0` (an `F9ˣ`). It has norm 1 by `det_pow_four_of_unitary`.
  set f0 : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9) :=
    (Pi.basisFun F9 (Fin 3)).equiv b (Equiv.refl (Fin 3))
  have hδ_norm : f0.det * conj9 f0.det = 1 := by
    convert det_pow_four_of_unitary f0 _
    · rw [show conj9 _ = _ ^ 3 from conj9_apply _]
      ring
    · convert unitary_of_basis_gram (Pi.basisFun F9 (Fin 3)) b f0 _ _
      · simp +zetaDelta at *
        simp +decide [Pi.basisFun]
        simp +decide [Module.Basis.equiv]
        simp +decide [Module.Basis.ofEquivFun]
      · aesop
  -- Set `g := mkSpecialUnitary f (its unitarity) (its det = 1)`.
  obtain ⟨g, hg⟩ :
      ∃ g : specialUnitaryGroup,
        toLinearEquiv g =
          (Pi.basisFun F9 (Fin 3)).equiv
            (b.unitsSMul fun i => if i = 0 then f0.det⁻¹ else 1)
            (Equiv.refl (Fin 3)) := by
    have h_unitary :
        ∀ i j,
          hermForm conj9
            ((b.unitsSMul fun i => if i = 0 then f0.det⁻¹ else 1) i)
            ((b.unitsSMul fun i => if i = 0 then f0.det⁻¹ else 1) j) =
            hermForm conj9 (Pi.single i 1) (Pi.single j 1) := by
      intro i j
      by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
        simp +decide [*, gram_unitsSMul]
      · simp_all +decide [← mul_inv, conj9_apply]
      · fin_cases j <;> simp +decide [hermForm_apply] at hj ⊢
        · simp +decide [Pi.single_apply]
        · simp +decide [Pi.single_apply]
      · fin_cases i <;> simp +decide [hermForm_apply] at hi ⊢
        all_goals simp +decide [Pi.single_apply]
    have h_det :
        LinearEquiv.det
            ((Pi.basisFun F9 (Fin 3)).equiv
              (b.unitsSMul fun i => if i = 0 then f0.det⁻¹ else 1)
              (Equiv.refl (Fin 3))) = 1 := by
      have h_det :
          LinearEquiv.det
              ((Pi.basisFun F9 (Fin 3)).equiv
                (b.unitsSMul fun i => if i = 0 then f0.det⁻¹ else 1)
                (Equiv.refl (Fin 3))) =
            (∏ i : Fin 3, (if i = 0 then (f0.det)⁻¹ else 1)) * f0.det := by
        convert det_equiv_unitsSMul (Pi.basisFun F9 (Fin 3)) b
          (fun i => if i = 0 then (LinearEquiv.det f0)⁻¹ else 1) using 1
      simp_all +decide
    have h_unitary :
        ∀ u v,
          hermForm conj9
            (((Pi.basisFun F9 (Fin 3)).equiv
              (b.unitsSMul fun i => if i = 0 then f0.det⁻¹ else 1)
              (Equiv.refl (Fin 3))) u)
            (((Pi.basisFun F9 (Fin 3)).equiv
              (b.unitsSMul fun i => if i = 0 then f0.det⁻¹ else 1)
              (Equiv.refl (Fin 3))) v) =
            hermForm conj9 u v := by
      convert unitary_of_basis_gram (Pi.basisFun F9 (Fin 3))
          (b.unitsSMul fun i => if i = 0 then (f0.det)⁻¹ else 1) _ _ using 1
      rotate_left
      exact (Pi.basisFun F9 (Fin 3)).equiv
        (b.unitsSMul fun i => if i = 0 then (LinearEquiv.det f0)⁻¹ else 1)
        (Equiv.refl (Fin 3))
      · simp +decide [Pi.basisFun]
        simp +decide [Module.Basis.equiv]
        simp +decide [Module.Basis.ofEquivFun]
      · simp +decide [Pi.basisFun_apply]
        exact Or.inl h_unitary
    exact ⟨mkSpecialUnitary _ h_unitary h_det, rfl⟩
  refine ⟨g, s, hs.1, ?_⟩
  simp +decide [hg, e2vec]
  convert hb₁ using 1
  simp +decide [Module.Basis.equiv, Module.Basis.unitsSMul]
  simp +decide [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  simp +decide [Fin.sum_univ_three, Pi.single_apply]

/-- Every involution of `SU(3,3)` is conjugate to the base involution `r0`. -/
lemma involution_conj_r0 (r : specialUnitaryGroup) (hr : orderOf r = 2) :
    ∃ g : specialUnitaryGroup, r = g * r0 * g⁻¹ := by
  -- Classify the involution as a Hermitian reflection.
  obtain ⟨w, hw⟩ :
      ∃ w : Fin 3 → F9, ∃ hn : hermForm conj9 w w ≠ 0, r = reflSU w hn := by
    exact involution_eq_reflSU r hr
  obtain ⟨hn, hr⟩ := hw
  obtain ⟨g, c, hc, hgc⟩ := exists_su_aniso_line w hn
  have hn' : hermForm conj9 (toLinearEquiv g e2vec) (toLinearEquiv g e2vec) ≠ 0 := by
    simp_all +decide
  have hr'' : g * r0 * g⁻¹ = reflSU (toLinearEquiv g e2vec) hn' := by
    convert conj_reflSU g e2vec e2vec_aniso hn' using 1
  have hr''' : reflSU (toLinearEquiv g e2vec) hn' = reflSU (c • w) (by grobner) := by
    grobner
  have hr'''' :
      reflSU (c • w) (by
        all_goals generalize_proofs at *
        assumption) = reflSU w hn := by
    all_goals generalize_proofs at *
    exact reflSU_smul w c hc (by assumption) hn
  generalize_proofs at *
  exact ⟨g, by rw [hr, hr'', hr''', hr'''']⟩

/-! ## The concrete fiber count over the base involution -/

open Matrix

/-- The diagonal matrix `diag(-1,-1,1)`: the matrix of the base involution `r0`
in the standard (orthonormal) basis. -/
noncomputable def Rmat : Matrix (Fin 3) (Fin 3) F9 := !![(-1 : F9), 0, 0; 0, -1, 0; 0, 0, 1]

/-- Conjugate-transpose of a matrix using `conj9`. -/
noncomputable def cT (X : Matrix (Fin 3) (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9 :=
  (X.map conj9)ᵀ

/-- The matrix of an `SU(3,3)` element in the standard (orthonormal) basis. -/
noncomputable def suMat (x : specialUnitaryGroup) : Matrix (Fin 3) (Fin 3) F9 :=
  LinearMap.toMatrix (Pi.basisFun F9 (Fin 3)) (Pi.basisFun F9 (Fin 3)) (toLinearEquiv x).toLinearMap

/-- The structured set of `3 × 3` matrices in bijection with the base fiber. -/
noncomputable def Sset : Finset (Matrix (Fin 3) (Fin 3) F9) :=
  univ.filter (fun X => X * X = Rmat ∧ cT X * X = 1 ∧ X.det = 1)

/-- The entries of `suMat x` recover the action of `toLinearEquiv x` on the standard
basis: `suMat x i j = (toLinearEquiv x) (Pi.single j 1) i`. -/
lemma suMat_apply (x : specialUnitaryGroup) (i j : Fin 3) :
    suMat x i j = (toLinearEquiv x) (Pi.single j 1) i := by
  simp [suMat]

/-- `suMat` is multiplicative. -/
lemma suMat_mul (x y : specialUnitaryGroup) : suMat (x * y) = suMat x * suMat y := by
  convert LinearMap.toMatrix_comp (Pi.basisFun F9 (Fin 3)) (Pi.basisFun F9 (Fin 3))
    (Pi.basisFun F9 (Fin 3)) _ _ using 1

/-- The matrix of the base involution is `Rmat`. -/
lemma suMat_r0 : suMat r0 = Rmat := by
  ext i j
  simp [suMat_apply, Rmat]
  fin_cases i <;> fin_cases j <;>
    simp +decide <;> ring_nf!
  all_goals
    erw [toLinearEquiv_reflSU, reflEquiv_apply, reflMap_apply]
    simp +decide [e2vec]
  · simp +decide [Pi.single_apply, hermForm_apply]
  · simp +decide [hermForm_apply, Pi.single_apply]
  · simp +decide [hermForm_apply, Pi.single_apply]
    grind

/-- The matrix of any `SU(3,3)` element is unitary in the standard basis. -/
lemma suMat_unitary (x : specialUnitaryGroup) : cT (suMat x) * suMat x = 1 := by
  unfold cT suMat
  ext i j
  convert toLinearEquiv_hermForm x (Pi.single j 1) (Pi.single i 1) using 1
  · simp only [hermForm_apply]
    simp +decide [Matrix.mul_apply, mul_comm]
  · fin_cases i <;> fin_cases j <;> simp +decide [hermForm_apply]
    all_goals simp +decide [Pi.single_apply]

/-- The matrix of any `SU(3,3)` element has determinant one. -/
lemma suMat_det (x : specialUnitaryGroup) : (suMat x).det = 1 := by
  rw [suMat, LinearMap.det_toMatrix]
  convert toLinearEquiv_det x
  simp +decide [Units.ext_iff]

/-- `suMat` is injective. -/
lemma suMat_injective : Function.Injective suMat := by
  intro x y hxy
  have h_le : (toLinearEquiv x).toLinearMap = (toLinearEquiv y).toLinearMap :=
    (LinearMap.toMatrix (Pi.basisFun F9 (Fin 3)) (Pi.basisFun F9 (Fin 3))).injective hxy
  generalize_proofs at *
  exact specialUnitaryGroup_ext (LinearEquiv.ext fun v => by
    simpa using congr_arg (fun f => f v) h_le)

/-- Given a matrix satisfying the unitary and determinant conditions, there is an
`SU(3,3)` element with that matrix. -/
lemma exists_su_of_matrix (X : Matrix (Fin 3) (Fin 3) F9)
    (hu : cT X * X = 1) (hd : X.det = 1) :
    ∃ x : specialUnitaryGroup, suMat x = X := by
  obtain ⟨f, hf⟩ :
      ∃ f : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9),
        ∀ i j, f (Pi.single j 1) i = X i j := by
    refine ⟨?_, ?_⟩
    refine LinearEquiv.ofBijective (Matrix.mulVecLin X) ⟨?_, ?_⟩
    all_goals norm_num [Function.Injective, Function.Surjective]
    · exact fun x y hxy => by
        simpa [hd] using congr_arg (fun z => X⁻¹.mulVec z) hxy
    · exact fun b => ⟨X⁻¹.mulVec b, by simp +decide [hd, isUnit_iff_ne_zero]⟩
  have hf_unitary : ∀ u v : Fin 3 → F9, hermForm conj9 (f u) (f v) = hermForm conj9 u v := by
    intro u v
    have h_f_u : ∀ i, f u i = ∑ j, X i j * u j := by
      intro i
      have h_sum : f u = ∑ j, u j • f (Pi.single j 1) := by
        convert f.pi_apply_eq_sum_univ u
        aesop
      simp +decide [h_sum, hf, mul_comm]
    have h_f_v : ∀ i, f v i = ∑ j, X i j * v j := by
      intro i
      have h_f_v : f v = ∑ j, v j • f (Pi.single j 1) := by
        convert f.pi_apply_eq_sum_univ v using 1
        congr! 2
        exact congr_arg _ (by
          ext j
          aesop)
      generalize_proofs at *
      simp +decide [h_f_v, hf, mul_comm]
    simp [h_f_u, h_f_v, hermForm_apply]
    simp_all +decide [Fin.sum_univ_three, cT]
    have := congr_fun (congr_fun hu 0) 0
    have := congr_fun (congr_fun hu 1) 0
    have := congr_fun (congr_fun hu 2) 0
    have := congr_fun (congr_fun hu 0) 1
    have := congr_fun (congr_fun hu 1) 1
    have := congr_fun (congr_fun hu 2) 1
    have := congr_fun (congr_fun hu 0) 2
    have := congr_fun (congr_fun hu 1) 2
    have := congr_fun (congr_fun hu 2) 2
    simp_all +decide [Matrix.mul_apply, Fin.sum_univ_three]
    grind
  have hf_det : LinearEquiv.det f = 1 := by
    have hf_det : LinearMap.det (f.toLinearMap) = X.det := by
      have h_det :
          LinearMap.toMatrix (Pi.basisFun F9 (Fin 3)) (Pi.basisFun F9 (Fin 3))
            (f.toLinearMap) = X := by
        ext i j
        simp +decide [hf]
      generalize_proofs at *
      rw [← h_det, LinearMap.det_toMatrix]
    aesop
  use mkSpecialUnitary f hf_unitary hf_det
  ext i j
  simp +decide [suMat_apply]
  exact hf i j

set_option maxHeartbeats 1000000 in
/-- **The structured matrix count.** There are exactly `8` matrices in `Sset`. -/
lemma card_Sset : Sset.card = 8 := by
  have hSset_eq_union :
      Sset =
        Finset.image
          (fun p : F9 × F9 => !![p.1, 0, 0; 0, p.2, 0; 0, 0, p.1 * p.2])
          (Finset.filter (fun a => a ^ 2 = -1) (Finset.univ : Finset F9) ×ˢ
            Finset.filter (fun e => e ^ 2 = -1) (Finset.univ : Finset F9)) ∪
        Finset.image (fun b : F9 => !![0, b, 0; -b ^ 3, 0, 0; 0, 0, 1])
          (Finset.filter (fun b => b ^ 4 = 1) (Finset.univ : Finset F9)) := by
    apply Finset.ext
    intro X
    simp [Sset, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hX
      obtain ⟨hX1, hX2, hX3⟩ := hX
      have hX4 : ∀ i j, conj9 (X j i) = Rmat i i * X i j := by
        have hX4 : cT X = Rmat * X := by
          have hRmat : Rmat * Rmat = 1 := by
            simp +decide [Rmat]
            exact Matrix.one_fin_three.symm
          grind +revert
        intro i j
        replace hX4 := congr_fun (congr_fun hX4 i) j
        simp_all +decide [Matrix.mul_apply, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> simp_all +decide [cT, Rmat]
      have hX5 : X 0 2 = 0 ∧ X 2 0 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0 := by
        have hX5 :
            conj9 (X 2 0) = -X 0 2 ∧ conj9 (X 0 2) = X 2 0 ∧
            conj9 (X 2 1) = -X 1 2 ∧ conj9 (X 1 2) = X 2 1 := by
          simp_all +decide [Fin.forall_fin_succ, Rmat]
        have hX5 : conj9 (conj9 (X 2 0)) = X 2 0 ∧ conj9 (conj9 (X 2 1)) = X 2 1 := by
          exact ⟨conj9_involutive _, conj9_involutive _⟩
        grind +ring
      have hX6 :
          conj9 (X 0 0) = -X 0 0 ∧ conj9 (X 1 1) = -X 1 1 ∧
          conj9 (X 2 2) = X 2 2 ∧ conj9 (X 0 1) = -X 1 0 := by
        simp_all +decide [Fin.forall_fin_succ, Rmat]
      have hX7 : (X 2 2) ^ 2 = 1 := by
        replace hX1 := congr_fun (congr_fun hX1 2) 2
        simp_all +decide [Matrix.mul_apply, Fin.sum_univ_three]
        exact eq_or_eq_neg_of_sq_eq_sq _ _ <| by
          rw [sq, hX1]
          simp +decide [Rmat]
      have hX8 :
          (X 0 0) ^ 2 + X 0 1 * X 1 0 = -1 ∧
          (X 1 1) ^ 2 + X 0 1 * X 1 0 = -1 := by
        have := congr_fun (congr_fun hX1 0) 0
        have := congr_fun (congr_fun hX1 1) 1
        simp_all +decide [Matrix.mul_apply, Fin.sum_univ_three]
        simp_all +decide [sq, mul_comm, Rmat]
        rw [add_comm, this]
      have hX9 :
          X 0 1 * (X 0 0 + X 1 1) = 0 ∧
          X 1 0 * (X 0 0 + X 1 1) = 0 := by
        have := congr_fun (congr_fun hX1 0) 1
        simp +decide [Matrix.mul_apply, Fin.sum_univ_three] at this
        have := congr_fun (congr_fun hX1 1) 0
        simp +decide [Matrix.mul_apply, Fin.sum_univ_three] at this
        have := congr_fun (congr_fun hX1 1) 1
        simp +decide [Matrix.mul_apply, Fin.sum_univ_three] at this
        simp_all +decide [mul_add, mul_comm]
        exact ⟨rfl, rfl⟩
      have hX10 : X 2 2 * (X 0 0 * X 1 1 - X 0 1 * X 1 0) = 1 := by
        rw [← hX3, Matrix.det_fin_three]
        simp +decide [hX5]
        ring_nf!
      by_cases hX11 : X 0 0 = 0
      · have hX12 : X 1 1 = 0 := by
          grind +extAll
        have hX13 : X 0 1 ^ 4 = 1 := by
          grind [conj9_apply]
        have hX14 : X 2 2 = 1 := by
          grobner
        have hX15 : X 1 0 = -X 0 1 ^ 3 := by
          grind
        exact Or.inr ⟨X 0 1, hX13, by
          ext i j
          fin_cases i <;> fin_cases j <;> simp +decide [*]⟩
      · have hX12 : X 0 1 = 0 ∧ X 1 0 = 0 := by
          have hX12 : X 0 1 * X 1 0 = 0 := by
            grind [conj9_apply]
          grind +qlia
        simp_all +decide [← Matrix.ext_iff]
        cases hX7 <;> simp_all +decide [Fin.forall_fin_succ]
        all_goals grind +qlia
    · rintro (⟨a, b, ⟨ha, hb⟩, rfl⟩ | ⟨a, ha, rfl⟩) <;>
        simp +decide [*, Matrix.det_fin_three]
      · refine ⟨?_, ?_, ?_⟩
        · simp_all +decide [sq, Rmat]
          grind
        · ext i j
          fin_cases i <;> fin_cases j <;>
            simp +decide [*, Matrix.mul_apply, Fin.sum_univ_succ]
          all_goals simp +decide [cT]
          all_goals grind [conj9_apply]
        · linear_combination' ha * hb
      · simp_all +decide [← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.mul_apply, cT]
        simp_all +decide [Fin.sum_univ_succ, Rmat]
        grind [conj9_apply]
  rw [hSset_eq_union, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective, Finset.card_image_of_injective] <;>
      norm_num [Function.Injective]
    have := card_fourth_one
    simp_all +decide [Fintype.card_subtype]
    rw [show
        (Finset.filter (fun x : F9 => x ^ 2 = -1) Finset.univ) =
          Finset.filter (fun x : F9 => x ^ 4 = 1) Finset.univ \
            Finset.filter (fun x : F9 => x ^ 2 = 1) Finset.univ from ?_]
    simp_all +decide [Finset.card_sdiff]
    · simp +decide [Finset.filter_eq', Finset.filter_or]
      grind
    · grind +qlia
  · simp +decide [Finset.disjoint_right]
    aesop

/-- **The base fiber count.** There are exactly `8` elements of `SU(3,3)` whose
square is the base involution `r0`. -/
lemma card_fiber_e2 :
    (univ.filter (fun x : specialUnitaryGroup => x ^ 2 = r0)).card = 8 := by
  rw [← card_Sset]
  apply Finset.card_bij (fun x _ => suMat x)
  · -- maps into Sset
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    refine mem_filter.mpr ⟨mem_univ _, ?_, suMat_unitary x, suMat_det x⟩
    rw [← suMat_mul, ← sq, hx, suMat_r0]
  · -- injective
    intro a _ b _ h
    exact suMat_injective h
  · -- surjective
    intro X hX
    simp only [Sset, mem_filter, mem_univ, true_and] at hX
    obtain ⟨hsq, hu, hd⟩ := hX
    obtain ⟨x, hx⟩ := exists_su_of_matrix X hu hd
    refine ⟨x, ?_, hx⟩
    simp only [mem_filter, mem_univ, true_and]
    exact suMat_injective (by
      rw [suMat_r0, sq, suMat_mul, hx]
      exact hsq)

/-- **The fiber over an involution `r` under the squaring map.** For each
involution `r` of `SU(3,3)` there are exactly `8` elements of order `4` whose
square is `r`. -/
theorem card_order_four_square_fiber
    (r : specialUnitaryGroup) (hr : orderOf r = 2) :
    (univ.filter
      (fun x : specialUnitaryGroup => orderOf x = 4 ∧ x ^ 2 = r)).card = 8 := by
  rw [fiber_eq r hr]
  obtain ⟨g, hg⟩ := involution_conj_r0 r hr
  rw [hg, card_fiber_conj g r0, card_fiber_e2]

/-- **There are exactly `504` elements of order `4` in `SU(3,3)`.** -/
theorem card_orderOf_eq_four_su :
    (Finset.univ.filter
      (fun g : specialUnitaryGroup => orderOf g = 4)).card = 504 := by
  have hsq_order : ∀ x : specialUnitaryGroup, orderOf x = 4 → orderOf (x ^ 2) = 2 :=
    fun x hx => by
      rw [orderOf_pow, hx]
      norm_num
  -- Fiberwise count over the involutions.
  have hfib :
      (univ.filter (fun g : specialUnitaryGroup => orderOf g = 4)).card =
        ∑ r ∈ (univ.filter (fun r : specialUnitaryGroup => orderOf r = 2)),
          (univ.filter
            (fun x : specialUnitaryGroup => orderOf x = 4 ∧ x ^ 2 = r)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x : specialUnitaryGroup => x ^ 2)
      (t := univ.filter (fun r : specialUnitaryGroup => orderOf r = 2))
      (s := univ.filter (fun g : specialUnitaryGroup => orderOf g = 4))
      (fun x hx => mem_filter.mpr ⟨mem_univ _, hsq_order x (by simpa using hx)⟩)]
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
  have hconst : ∀ r ∈ univ.filter (fun r : specialUnitaryGroup => orderOf r = 2),
      (univ.filter
        (fun x : specialUnitaryGroup => orderOf x = 4 ∧ x ^ 2 = r)).card = 8 :=
    fun r hr => card_order_four_square_fiber r (mem_filter.mp hr).2
  rw [hfib, Finset.sum_congr rfl hconst, Finset.sum_const, card_orderOf_eq_two_su]
  norm_num

end InvolutionOrderFourCount

end PSU33

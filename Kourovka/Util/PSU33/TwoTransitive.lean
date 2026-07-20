/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.HermitianGeometryF9

/-!
# Two-transitivity for the `PSU(3,3)` Hermitian action

This file proves two-transitivity of the special unitary action on isotropic
points over `GF(9)`.
-/

namespace PSU33

open PSU33.HermitianForm
open scoped Classical

/-!
## Geometric two-transitivity of `SU(3,3)` on isotropic points

This section proves that `specialUnitaryGroup` acts `2`-transitively on
`IsotropicPoint`. The argument is a Witt extension: any ordered pair of
distinct isotropic points spans a hyperbolic Hermitian plane, and a canonical
orthonormal-style frame attached to such a pair lets us realize any pair-to-pair
map by an explicit special unitary basis change. -/

section TwoTransitive

open Module

/-- The underlying linear equivalence of a special-unitary element. -/
def toLinearEquiv (g : specialUnitaryGroup) : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9) :=
  ((g : unitaryGroup) : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9))

/-- The action of a special-unitary element on an isotropic point is induced by
its underlying linear equivalence. -/
lemma su_smul_fst (g : specialUnitaryGroup) (p : IsotropicPoint) :
    (g • p).1 = (toLinearEquiv g) • p.1 := rfl

/-- Build a special unitary element from a unitary, determinant-one linear
equivalence. -/
def mkSpecialUnitary (f : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9))
    (hu : ∀ u v, hermForm conj9 (f u) (f v) = hermForm conj9 u v)
    (hd : LinearEquiv.det f = 1) : specialUnitaryGroup :=
  ⟨⟨f, hu⟩, by
    show (LinearEquiv.det.comp (HermitianForm.unitaryGroup conj9).subtype) ⟨f, hu⟩ = 1
    simpa using hd⟩

/-- The underlying linear equivalence of `mkSpecialUnitary f hu hd` is `f`. -/
lemma toLinearEquiv_mkSpecialUnitary (f) (hu) (hd) :
    toLinearEquiv (mkSpecialUnitary f hu hd) = f := rfl

/-- Additivity of the Hermitian form over a finite sum in the left argument. -/
lemma hermForm_sum_left {n : ℕ} (f : Fin n → (Fin 3 → F9)) (v : Fin 3 → F9) :
    hermForm conj9 (∑ i, f i) v = ∑ i, hermForm conj9 (f i) v := by
  simp only [map_sum, LinearMap.sum_apply]

/-- Additivity of the Hermitian form over a finite sum in the right argument. -/
lemma hermForm_sum_right {n : ℕ} (u : Fin 3 → F9) (g : Fin n → (Fin 3 → F9)) :
    hermForm conj9 u (∑ j, g j) = ∑ j, hermForm conj9 u (g j) := by
  rw [map_sum]

/-- Sesquilinear expansion of the Hermitian form over finite sums. -/
lemma hermForm_sum_sum {n : ℕ} (a b : Fin n → F9)
    (x y : Fin n → (Fin 3 → F9)) :
    hermForm conj9 (∑ i, a i • x i) (∑ j, b j • y j)
      = ∑ i, ∑ j, a i * conj9 (b j) * hermForm conj9 (x i) (y j) := by
  rw [hermForm_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [hermForm_smul_left, hermForm_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hermForm_smul_right]
  ring

/-- A linear equivalence carrying one basis to another with the same Gram matrix
preserves the Hermitian form (hence is unitary). -/
lemma unitary_of_basis_gram
    (b1 b2 : Basis (Fin 3) F9 (Fin 3 → F9))
    (f : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9))
    (hf : ∀ i, f (b1 i) = b2 i)
    (hgram : ∀ i j, hermForm conj9 (b2 i) (b2 j) = hermForm conj9 (b1 i) (b1 j)) :
    ∀ u v, hermForm conj9 (f u) (f v) = hermForm conj9 u v := by
  intro u v
  have key : ∀ z, f z = ∑ i, (b1.repr z i) • b2 i := fun z => by
    conv_lhs => rw [← b1.sum_repr z]
    simp only [map_sum, map_smul, hf]
  rw [key u, key v, hermForm_sum_sum]
  conv_rhs => rw [← b1.sum_repr u, ← b1.sum_repr v, hermForm_sum_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hgram]

/-- Witt index one for the `PSU(3,3)` Hermitian form: an isotropic vector
perpendicular to a nonzero isotropic vector is a scalar multiple of it. -/
lemma exists_smul_of_isotropic_perp
    (a b : Fin 3 → F9) (ha : a ≠ 0)
    (hai : hermForm conj9 a a = 0) (hbi : hermForm conj9 b b = 0)
    (hperp : hermForm conj9 a b = 0) :
    ∃ c : F9, b = c • a := by
  by_contra! h_contra
  -- Extend `{a, b}` to a basis by choosing a vector outside its span.
  obtain ⟨t, ht⟩ : ∃ t : Fin 3 → F9, LinearIndependent F9 ![a, b, t] := by
    obtain ⟨t, ht⟩ : ∃ t : Fin 3 → F9, t ∉ Submodule.span F9 {a, b} := by
      have h_subspace : Submodule.span F9 {a, b} ≠ ⊤ := by
        have h_subspace : Module.finrank F9 (Submodule.span F9 {a, b}) ≤ 2 := by
          refine le_trans (finrank_span_le_card _) ?_
          norm_num
          exact Finset.card_insert_le _ _
        exact fun h => by
          rw [h] at h_subspace
          norm_num at h_subspace
      exact not_forall.mp fun h => h_subspace <| eq_top_iff.mpr fun x hx => h x
    refine ⟨t, ?_⟩
    have h_lin_indep : LinearIndependent F9 ![a, b] := by
      rw [Fintype.linearIndependent_iff]
      simp_all +decide [funext_iff, Fin.forall_fin_succ]
      intro g hg₀ hg₁ hg₂
      by_cases hg₀' : g 0 = 0 <;> by_cases hg₁' : g 1 = 0 <;>
        simp_all +decide [add_eq_zero_iff_eq_neg]
      refine h_contra (-g 0 / g 1) ?_ ?_ ?_ <;> simp_all +decide [div_eq_inv_mul, mul_assoc]
    rw [Fintype.linearIndependent_iff] at *
    intro g hg i
    simp_all +decide [Fin.sum_univ_three, Fin.forall_fin_succ]
    by_cases h : g 2 = 0 <;> simp_all +decide [add_eq_zero_iff_eq_neg]
    · specialize h_lin_indep (fun i => if i = 0 then g 0 else g 1)
      simp_all +decide
      fin_cases i <;> tauto
    · exact False.elim <| ht <| by
        rw [show t = -(g 2)⁻¹ • (g 0 • a + g 1 • b) by
          simp +decide [hg, h, smul_smul]]
        exact Submodule.smul_mem _ _ <| Submodule.add_mem _
          (Submodule.smul_mem _ _ <| Submodule.subset_span <| Set.mem_insert _ _)
          (Submodule.smul_mem _ _ <| Submodule.subset_span <|
            Set.mem_insert_of_mem _ <| Set.mem_singleton _)
  -- The Gram matrix is `M * (M.map conj9)ᵀ`, where the rows of `M` are `a, b, t`.
  set G : Matrix (Fin 3) (Fin 3) F9 :=
    Matrix.of (fun i j => hermForm conj9 (![a, b, t] i) (![a, b, t] j))
  -- Hence `G.det = M.det * conj9 (M.det)`.
  have hG_det :
      G.det = Matrix.det (Matrix.of (fun i j => (![a, b, t] i) j)) *
        conj9 (Matrix.det (Matrix.of (fun i j => (![a, b, t] i) j))) := by
    have hG_det :
        G = Matrix.of (fun i j => (![a, b, t] i) j) *
          Matrix.transpose (Matrix.map (Matrix.of (fun i j => (![a, b, t] i) j)) conj9) := by
      ext i j
      simp +decide [G, Matrix.mul_apply, hermForm_apply]
    rw [hG_det, Matrix.det_mul, Matrix.det_transpose]
    simp +decide [Matrix.det_apply']
  -- Since `M.det ≠ 0`, we have `G.det = (M.det)^4 ≠ 0`.
  have hG_det_ne_zero : G.det ≠ 0 := by
    have hM_det_ne_zero :
        Matrix.det (Matrix.of (fun i j => (![a, b, t] i) j)) ≠ 0 := by
      rw [Fintype.linearIndependent_iff] at ht
      intro h_det_zero
      obtain ⟨g, hg⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h_det_zero
      exact hg.1 (funext fun i =>
        ht g (by simpa [funext_iff, Fin.forall_fin_succ] using hg.2) i)
    simp_all +decide [conj9_apply]
  simp_all +decide [Matrix.det_fin_three]
  simp +zetaDelta at *
  simp_all +decide [
    show hermForm conj9 b a = 0 by
      rw [← hermForm_conj_symm conj9_involutive]
      aesop]

/-- The determinant of a unitary map has norm one, so it is a fourth root of
unity. -/
lemma det_pow_four_of_unitary (f : (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9))
    (hu : ∀ u v, hermForm conj9 (f u) (f v) = hermForm conj9 u v) :
    ((LinearEquiv.det f : F9ˣ) : F9) ^ 4 = 1 := by
  set e := Pi.basisFun F9 (Fin 3) with he
  set M := LinearMap.toMatrix e e f.toLinearMap with hM
  have hdet : ((LinearEquiv.det f : F9ˣ) : F9) = M.det := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix e]
  have hMij : ∀ i j, M i j = f (e j) i := by
    intro i j
    rw [hM, LinearMap.toMatrix_apply]
    simp [he, Pi.basisFun_repr]
  have hnorm : M.det * conj9 (M.det) = 1 := by
    have hMM : M.transpose * M.map conj9 = 1 := by
      ext i j
      rw [Matrix.mul_apply]
      have key :
          ∑ k, M.transpose i k * (M.map conj9) k j =
          hermForm conj9 (f (e i)) (f (e j)) := by
        rw [hermForm_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [Matrix.transpose_apply, Matrix.map_apply, hMij, hMij]
      rw [key, hu]
      simp only [he, Matrix.one_apply, hermForm_apply, Pi.basisFun_apply]
      rcases eq_or_ne i j with h | h
      · subst h
        simp [Pi.single_apply]
      · rw [if_neg h]
        apply Finset.sum_eq_zero
        intro k _
        simp only [Pi.single_apply]
        by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
    have := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [show M.map conj9 = conj9.mapMatrix M from rfl, ← RingHom.map_det] at this
    exact this
  calc
    ((LinearEquiv.det f : F9ˣ) : F9) ^ 4 = M.det * conj9 (M.det) := by
      rw [hdet, conj9_apply]
      ring
    _ = 1 := hnorm

/-- Gram entries transform by the scaling units under `Basis.unitsSMul`. -/
lemma gram_unitsSMul (b : Basis (Fin 3) F9 (Fin 3 → F9)) (w : Fin 3 → F9ˣ)
    (i j : Fin 3) :
    hermForm conj9 ((b.unitsSMul w) i) ((b.unitsSMul w) j)
      = (w i : F9) * conj9 (w j : F9) * hermForm conj9 (b i) (b j) := by
  simp only [Basis.unitsSMul_apply, Units.smul_def]
  rw [hermForm_smul_left, hermForm_smul_right]
  ring

/-- The matrix of the basis-change equivalence `b1.equiv b2` in the basis `b1`
is the change-of-basis matrix `b1.toMatrix b2`. -/
lemma toMatrix_equiv (b1 b2 : Basis (Fin 3) F9 (Fin 3 → F9)) :
    LinearMap.toMatrix b1 b1 (b1.equiv b2 (Equiv.refl (Fin 3))).toLinearMap
      = b1.toMatrix b2 := by
  ext i j
  simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, Basis.equiv_apply]

/-- The determinant of `b1.equiv b2` equals the determinant of the
change-of-basis matrix. -/
lemma det_equiv_eq (b1 b2 : Basis (Fin 3) F9 (Fin 3 → F9)) :
    ((LinearEquiv.det (b1.equiv b2 (Equiv.refl (Fin 3)))) : F9) = (b1.toMatrix b2).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b1, toMatrix_equiv]

/-- Determinant of the basis-change equivalence under a `unitsSMul` rescaling of
the target basis. -/
lemma det_equiv_unitsSMul (b1 b2 : Basis (Fin 3) F9 (Fin 3 → F9))
    (w : Fin 3 → F9ˣ) :
    LinearEquiv.det (b1.equiv (b2.unitsSMul w) (Equiv.refl (Fin 3)))
      = (∏ i, w i) * LinearEquiv.det (b1.equiv b2 (Equiv.refl (Fin 3))) := by
  apply Units.ext
  push_cast
  rw [det_equiv_eq, det_equiv_eq]
  rw [show
    b1.toMatrix (b2.unitsSMul w) =
      b1.toMatrix b2 * Matrix.diagonal (Units.val ∘ w) from ?_]
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    simp [mul_comm]
  · rw [← Basis.toMatrix_mul_toMatrix b1 b2, Basis.toMatrix_unitsSMul]

/-- The Hermitian self-form `hermForm conj9 v v` of any vector lies in
`{0, 1, -1}` (it is a norm down to `GF(3)`). -/
lemma hermForm_self_cases (v : Fin 3 → F9) :
    hermForm conj9 v v = 0 ∨ hermForm conj9 v v = 1 ∨ hermForm conj9 v v = -1 := by
  rw [hermForm_self_eq]
  have h3 : (3 : F9) = 0 := three_eq_zero
  rcases sum_fourth_mem (v 0) (v 1) with h | h | h <;>
    rcases fourth_pow_cases (v 2) with h2 | h2 | h2 <;>
    first
      | left
        linear_combination h + h2
      | left
        linear_combination h + h2 + h3
      | left
        linear_combination h + h2 - h3
      | right
        left
        linear_combination h + h2
      | right
        left
        linear_combination h + h2 + h3
      | right
        left
        linear_combination h + h2 - h3
      | right
        right
        linear_combination h + h2
      | right
        right
        linear_combination h + h2 + h3

/-- Every element of `{1, -1} ⊆ GF(9)` is a fourth power of a nonzero element. -/
lemma exists_fourth_root (e : F9) (he : e = 1 ∨ e = -1) :
    ∃ s : F9, s ^ 4 = e ∧ s ≠ 0 := by
  rcases he with rfl | rfl
  · exact ⟨1, by norm_num, one_ne_zero⟩
  · have hpos : 0 < Nat.card {x : F9 // x ^ 4 = -1} := by
      rw [card_fourth_negone]
      norm_num
    obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨x, hx, fun h => by
      rw [h] at hx
      norm_num at hx⟩

/-- Normalization step: a pair of distinct isotropic points admits representative
vectors forming a normalized hyperbolic pair (`h v0 v1 = h v1 v0 = 1`).  This uses
Witt index one (`exists_smul_of_isotropic_perp`) to know the representatives are
not perpendicular. -/
lemma exists_hyperbolic_pair (p q : IsotropicPoint) (hpq : p ≠ q) :
    ∃ v0 v1 : Fin 3 → F9, ∃ (h0 : v0 ≠ 0) (h1 : v1 ≠ 0),
      Projectivization.mk F9 v0 h0 = p.1 ∧
      Projectivization.mk F9 v1 h1 = q.1 ∧
      hermForm conj9 v0 v0 = 0 ∧ hermForm conj9 v1 v1 = 0 ∧
      hermForm conj9 v0 v1 = 1 ∧ hermForm conj9 v1 v0 = 1 := by
  have ha0 : p.1.rep ≠ 0 := Projectivization.rep_nonzero p.1
  have hb0 : q.1.rep ≠ 0 := Projectivization.rep_nonzero q.1
  have hai : hermForm conj9 p.1.rep p.1.rep = 0 := p.2
  have hbi : hermForm conj9 q.1.rep q.1.rep = 0 := q.2
  have hne : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
  set d := hermForm conj9 p.1.rep q.1.rep with hd
  have hdne : d ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := exists_smul_of_isotropic_perp p.1.rep q.1.rep ha0 hai hbi (hd ▸ h0)
    have hcne : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hb0 hc
    have hqp : q.1 = p.1 := by
      rw [← Projectivization.mk_rep q.1, ← Projectivization.mk_rep p.1,
        Projectivization.mk_eq_mk_iff]
      exact ⟨Units.mk0 c hcne, by
        rw [Units.smul_mk0]
        exact hc.symm⟩
    exact hne hqp.symm
  set t := conj9 (d⁻¹) with ht
  have htne : t ≠ 0 := by
    rw [ht]
    simp [map_eq_zero_iff conj9 conj9.injective, inv_eq_zero, hdne]
  refine ⟨p.1.rep, t • q.1.rep, ha0, smul_ne_zero htne hb0, Projectivization.mk_rep p.1,
    ?_, hai, ?_, ?_, ?_⟩
  · conv_rhs => rw [← Projectivization.mk_rep q.1]
    rw [Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 t htne, by rw [Units.smul_mk0]⟩
  · rw [hermForm_smul_self, show conj9 t = d⁻¹ by rw [ht, conj9_involutive], hbi]
    ring
  · rw [hermForm_smul_right, ← hd, show conj9 t = d⁻¹ by rw [ht, conj9_involutive]]
    field_simp
  · rw [hermForm_smul_left, ht,
      show hermForm conj9 q.1.rep p.1.rep = conj9 d by
        rw [hd, hermForm_conj_symm conj9_involutive],
      ← map_mul, show d⁻¹ * d = 1 by field_simp]
    simp

/-- Witt extension step: a normalized hyperbolic pair `v0, v1` can be completed
to a Hermitian frame by a unit anisotropic vector `w` orthogonal to both, with
`{v0, v1, w}` linearly independent. -/
lemma exists_orthogonal_unit (v0 v1 : Fin 3 → F9) (hv0 : v0 ≠ 0)
    (hv0iso : hermForm conj9 v0 v0 = 0) (hv1iso : hermForm conj9 v1 v1 = 0)
    (h01 : hermForm conj9 v0 v1 = 1) (h10 : hermForm conj9 v1 v0 = 1) :
    ∃ w : Fin 3 → F9,
      hermForm conj9 v0 w = 0 ∧ hermForm conj9 w v0 = 0 ∧
      hermForm conj9 v1 w = 0 ∧ hermForm conj9 w v1 = 0 ∧
      hermForm conj9 w w = 1 ∧ LinearIndependent F9 ![v0, v1, w] := by
  -- The conjugated cross product of `v0` and `v1`.
  set c : Fin 3 → F9 :=
    ![v0 1 * v1 2 - v0 2 * v1 1,
      v0 2 * v1 0 - v0 0 * v1 2,
      v0 0 * v1 1 - v0 1 * v1 0] with hc
  set w0 : Fin 3 → F9 := fun i => conj9 (c i) with hw0
  have hinv : ∀ x : F9, conj9 (conj9 x) = x := conj9_involutive
  have hv0w0 : hermForm conj9 v0 w0 = 0 := by
    simp only [hermForm_apply, hw0, Fin.sum_univ_three, hinv, hc,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hv1w0 : hermForm conj9 v1 w0 = 0 := by
    simp only [hermForm_apply, hw0, Fin.sum_univ_three, hinv, hc,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hw0v0 : hermForm conj9 w0 v0 = 0 := by
    rw [← hermForm_conj_symm conj9_involutive, hv0w0, map_zero]
  have hw0v1 : hermForm conj9 w0 v1 = 0 := by
    rw [← hermForm_conj_symm conj9_involutive, hv1w0, map_zero]
  -- `c ≠ 0`: otherwise `v1` would be a scalar multiple of `v0`, forcing `h v0 v1 = 0`.
  have hcne : c ≠ 0 := by
    intro hc0
    have eq0 : v0 1 * v1 2 - v0 2 * v1 1 = 0 := by simpa [hc] using congrFun hc0 0
    have eq1 : v0 2 * v1 0 - v0 0 * v1 2 = 0 := by simpa [hc] using congrFun hc0 1
    have eq2 : v0 0 * v1 1 - v0 1 * v1 0 = 0 := by simpa [hc] using congrFun hc0 2
    obtain ⟨lam, hlam⟩ : ∃ lam : F9, v1 = lam • v0 := by
      obtain ⟨m, hm⟩ : ∃ m, v0 m ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv0 (funext fun i => by simp [h i])
      fin_cases m
      · have h0 : v0 0 ≠ 0 := hm
        refine ⟨v1 0 * (v0 0)⁻¹, funext fun i => ?_⟩
        fin_cases i
        · show v1 0 = v1 0 * (v0 0)⁻¹ * v0 0
          field_simp
        · show v1 1 = v1 0 * (v0 0)⁻¹ * v0 1
          field_simp
          linear_combination eq2
        · show v1 2 = v1 0 * (v0 0)⁻¹ * v0 2
          field_simp
          linear_combination -eq1
      · have h1 : v0 1 ≠ 0 := hm
        refine ⟨v1 1 * (v0 1)⁻¹, funext fun i => ?_⟩
        fin_cases i
        · show v1 0 = v1 1 * (v0 1)⁻¹ * v0 0
          field_simp
          linear_combination -eq2
        · show v1 1 = v1 1 * (v0 1)⁻¹ * v0 1
          field_simp
        · show v1 2 = v1 1 * (v0 1)⁻¹ * v0 2
          field_simp
          linear_combination eq0
      · have h2 : v0 2 ≠ 0 := hm
        refine ⟨v1 2 * (v0 2)⁻¹, funext fun i => ?_⟩
        fin_cases i
        · show v1 0 = v1 2 * (v0 2)⁻¹ * v0 0
          field_simp
          linear_combination eq1
        · show v1 1 = v1 2 * (v0 2)⁻¹ * v0 1
          field_simp
          linear_combination -eq0
        · show v1 2 = v1 2 * (v0 2)⁻¹ * v0 2
          field_simp
    have hcontra : hermForm conj9 v0 v1 = 0 := by
      rw [hlam, hermForm_smul_right, hv0iso, mul_zero]
    rw [h01] at hcontra
    exact one_ne_zero hcontra
  -- hence `w0 ≠ 0`.
  have hw0ne : w0 ≠ 0 := by
    intro h0
    apply hcne
    funext i
    have hi : conj9 (c i) = 0 := by
      have := congrFun h0 i
      rwa [hw0] at this
    have := congrArg conj9 hi
    rwa [hinv, map_zero] at this
  -- `w0` is anisotropic: an isotropic vector perpendicular to `v0` and `v1` would be zero.
  have hw0w0ne : hermForm conj9 w0 w0 ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := exists_smul_of_isotropic_perp v0 w0 hv0 hv0iso h0 hv0w0
    have hvk : hermForm conj9 v1 w0 = conj9 k := by
      rw [hk, hermForm_smul_right, h10, mul_one]
    rw [hv1w0] at hvk
    have hk0 : k = 0 := (map_eq_zero_iff conj9 conj9.injective).mp hvk.symm
    exact hw0ne (by rw [hk, hk0, zero_smul])
  -- normalize `w0` to a unit vector by a fourth root of `±1`.
  obtain ⟨e, hee, hesign⟩ : ∃ e, hermForm conj9 w0 w0 = e ∧ (e = 1 ∨ e = -1) := by
    rcases hermForm_self_cases w0 with h | h | h
    · exact absurd h hw0w0ne
    · exact ⟨1, h, Or.inl rfl⟩
    · exact ⟨-1, h, Or.inr rfl⟩
  obtain ⟨s, hs4, hsne⟩ := exists_fourth_root e hesign
  have hww : hermForm conj9 (s • w0) (s • w0) = 1 := by
    rw [hermForm_smul_self, hee, conj9_apply, show s * s ^ 3 = s ^ 4 by ring, hs4]
    rcases hesign with h | h <;> rw [h] <;> ring
  refine ⟨s • w0, ?_, ?_, ?_, ?_, hww, ?_⟩
  · rw [hermForm_smul_right, hv0w0, mul_zero]
  · rw [hermForm_smul_left, hw0v0, mul_zero]
  · rw [hermForm_smul_right, hv1w0, mul_zero]
  · rw [hermForm_smul_left, hw0v1, mul_zero]
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    have key : ∀ X : Fin 3 → F9,
        conj9 (g 0) * hermForm conj9 X v0 + conj9 (g 1) * hermForm conj9 X v1
          + conj9 (g 2) * hermForm conj9 X (s • w0) = 0 := by
      intro X
      have h2 := congrArg (hermForm conj9 X) hg
      rw [hermForm_add_right, hermForm_add_right, hermForm_smul_right,
        hermForm_smul_right, hermForm_smul_right,
        show hermForm conj9 X 0 = 0 by simp [hermForm_apply]] at h2
      exact h2
    have hg0 : g 0 = 0 := by
      have hk := key v1
      simp only [h10, hv1iso, hermForm_smul_right, hv1w0, mul_zero, mul_one, add_zero] at hk
      exact (map_eq_zero_iff conj9 conj9.injective).mp hk
    have hg1 : g 1 = 0 := by
      have hk := key v0
      simp only [hv0iso, h01, hermForm_smul_right, hv0w0, mul_zero, mul_one, zero_add,
        add_zero] at hk
      exact (map_eq_zero_iff conj9 conj9.injective).mp hk
    have hg2 : g 2 = 0 := by
      have hk := key (s • w0)
      simp only [hermForm_smul_left, hw0v0, hw0v1, hww, mul_zero, mul_one, zero_add] at hk
      exact (map_eq_zero_iff conj9 conj9.injective).mp hk
    intro i
    fin_cases i <;> assumption

/-- A canonical Hermitian frame attached to an ordered pair of distinct isotropic
points: the first two basis vectors represent the two points and form a
normalized hyperbolic pair, while the third is a unit anisotropic vector
orthogonal to them. -/
lemma exists_frame (p q : IsotropicPoint) (hpq : p ≠ q) :
    ∃ (b : Basis (Fin 3) F9 (Fin 3 → F9)),
      Projectivization.mk F9 (b 0) (b.ne_zero 0) = p.1 ∧
      Projectivization.mk F9 (b 1) (b.ne_zero 1) = q.1 ∧
      hermForm conj9 (b 0) (b 0) = 0 ∧
      hermForm conj9 (b 1) (b 1) = 0 ∧
      hermForm conj9 (b 0) (b 1) = 1 ∧
      hermForm conj9 (b 1) (b 0) = 1 ∧
      hermForm conj9 (b 0) (b 2) = 0 ∧
      hermForm conj9 (b 2) (b 0) = 0 ∧
      hermForm conj9 (b 1) (b 2) = 0 ∧
      hermForm conj9 (b 2) (b 1) = 0 ∧
      hermForm conj9 (b 2) (b 2) = 1 := by
  obtain ⟨v0, v1, h0, h1, hmk0, hmk1, hi0, hi1, h01, h10⟩ := exists_hyperbolic_pair p q hpq
  obtain ⟨w, hw0r, hw0l, hw1r, hw1l, hww, hindep⟩ :=
    exists_orthogonal_unit v0 v1 h0 hi0 hi1 h01 h10
  have hcard : Fintype.card (Fin 3) = finrank F9 (Fin 3 → F9) := by simp
  set b := basisOfLinearIndependentOfCardEqFinrank hindep hcard with hb
  have hbe : ⇑b = ![v0, v1, w] := coe_basisOfLinearIndependentOfCardEqFinrank hindep hcard
  have e0 : b 0 = v0 := by
    rw [hbe]
    rfl
  have e1 : b 1 = v1 := by
    rw [hbe]
    rfl
  have e2 : b 2 = w := by
    rw [hbe]
    rfl
  refine ⟨b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [e0, e1, e2]
  exacts [hmk0, hmk1, hi0, hi1, h01, h10, hw0r, hw0l, hw1r, hw1l, hww]

/-- **Ordered-pair transitivity.** Any ordered pair of distinct isotropic points
is carried to any other ordered pair of distinct isotropic points by a special
unitary transformation. -/
theorem exists_specialUnitaryGroup_map_isotropic_pair
    (p q r s : IsotropicPoint) (hpq : p ≠ q) (hrs : r ≠ s) :
    ∃ g : specialUnitaryGroup, g • p = r ∧ g • q = s := by
  obtain
    ⟨b1, hb1p, hb1q, g1_00, g1_11, g1_01, g1_10, g1_02, g1_20, g1_12, g1_21, g1_22⟩ :=
      exists_frame p q hpq
  obtain
    ⟨b2, hb2r, hb2s, g2_00, g2_11, g2_01, g2_10, g2_02, g2_20, g2_12, g2_21, g2_22⟩ :=
      exists_frame r s hrs
  have hf0b : ∀ i, (b1.equiv b2 (Equiv.refl (Fin 3))) (b1 i) = b2 i := fun i => by
    rw [Basis.equiv_apply]
    rfl
  have hgram12 : ∀ i j, hermForm conj9 (b2 i) (b2 j) = hermForm conj9 (b1 i) (b1 j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  have hu0 := unitary_of_basis_gram b1 b2 _ hf0b hgram12
  set δ : F9ˣ := LinearEquiv.det (b1.equiv b2 (Equiv.refl (Fin 3))) with hδ
  have hnorm : (δ : F9) * conj9 (δ : F9) = 1 := by
    rw [conj9_apply]
    linear_combination det_pow_four_of_unitary _ hu0
  have hnorminv : ((δ⁻¹ : F9ˣ) : F9) * conj9 ((δ⁻¹ : F9ˣ) : F9) = 1 := by
    rw [show ((δ⁻¹ : F9ˣ) : F9) = ((δ : F9))⁻¹ by simp, map_inv₀, ← mul_inv, hnorm, inv_one]
  set w : Fin 3 → F9ˣ := fun i => if i = 2 then δ⁻¹ else 1 with hw
  set b2' := b2.unitsSMul w with hb2'
  set f := b1.equiv b2' (Equiv.refl (Fin 3)) with hf
  have hfb : ∀ i, f (b1 i) = b2' i := fun i => by
    rw [hf, Basis.equiv_apply]
    rfl
  have hgram : ∀ i j, hermForm conj9 (b2' i) (b2' j) = hermForm conj9 (b1 i) (b1 j) := by
    intro i j
    rw [hb2', gram_unitsSMul, hgram12 i j]
    fin_cases i <;> fin_cases j <;>
      simp only [hw, Fin.isValue, show ((⟨0, by omega⟩ : Fin 3) = 2) = False by decide,
        show ((⟨1, by omega⟩ : Fin 3) = 2) = False by decide,
        show ((⟨2, by omega⟩ : Fin 3) = 2) = True by decide,
        if_true, if_false, Units.val_one, map_one, one_mul, mul_one]
    · show
        conj9 (δ⁻¹ : F9ˣ) * hermForm conj9 (b1 0) (b1 2) =
          hermForm conj9 (b1 0) (b1 2)
      rw [g1_02, mul_zero]
    · show
        conj9 (δ⁻¹ : F9ˣ) * hermForm conj9 (b1 1) (b1 2) =
          hermForm conj9 (b1 1) (b1 2)
      rw [g1_12, mul_zero]
    · show
        ((δ⁻¹ : F9ˣ) : F9) * hermForm conj9 (b1 2) (b1 0) =
          hermForm conj9 (b1 2) (b1 0)
      rw [g1_20]
      ring
    · show
        ((δ⁻¹ : F9ˣ) : F9) * hermForm conj9 (b1 2) (b1 1) =
          hermForm conj9 (b1 2) (b1 1)
      rw [g1_21]
      ring
    · show
        ((δ⁻¹ : F9ˣ) : F9) * conj9 (δ⁻¹ : F9ˣ) * hermForm conj9 (b1 2) (b1 2) =
          hermForm conj9 (b1 2) (b1 2)
      rw [g1_22, mul_one]
      exact hnorminv
  have hu := unitary_of_basis_gram b1 b2' f hfb hgram
  have hdet : LinearEquiv.det f = 1 := by
    rw [hf, hb2', det_equiv_unitsSMul b1 b2 w, ← hδ,
      show (∏ i, w i) = δ⁻¹ by
        rw [Fin.prod_univ_three]
        simp [hw], inv_mul_cancel]
  refine ⟨mkSpecialUnitary f hu hdet, ?_, ?_⟩
  · apply Subtype.ext
    rw [su_smul_fst, toLinearEquiv_mkSpecialUnitary, ← hb1p,
      Projectivization.smul_mk, ← hb2r, Projectivization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    rw [one_smul]
    show b2 0 = f (b1 0)
    rw [hfb, hb2', Basis.unitsSMul_apply]
    simp [hw]
  · apply Subtype.ext
    rw [su_smul_fst, toLinearEquiv_mkSpecialUnitary, ← hb1q,
      Projectivization.smul_mk, ← hb2s, Projectivization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    rw [one_smul]
    show b2 1 = f (b1 1)
    rw [hfb, hb2', Basis.unitsSMul_apply]
    simp [hw]

/-- **Geometric two-transitivity.** `specialUnitaryGroup` acts
`2`-transitively on `IsotropicPoint`. -/
theorem specialUnitaryGroup_twoTransitive :
    MulAction.IsMultiplyPretransitive specialUnitaryGroup IsotropicPoint 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  exact exists_specialUnitaryGroup_map_isotropic_pair a b c d hab hcd

end TwoTransitive

end PSU33

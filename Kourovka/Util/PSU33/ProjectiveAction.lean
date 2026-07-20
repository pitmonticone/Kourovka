/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.HermitianGeometry
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Tactic.LinearCombination'

/-!
# Basic action lemmas for the geometric `PSU(3,3)` model

This file contains the low-level API for the action of `SU(3,3)` on isotropic
points: linear-map helper lemmas, freeness on hyperbolic pairs, existence of
hyperbolic partners, and the corestricted homomorphism `toPsu`.
-/

namespace PSU33

open PSU33.HermitianForm

/-- The underlying linear map of a special-unitary element preserves the
Hermitian form. -/
lemma toLinearEquiv_hermForm (g : specialUnitaryGroup) (x y : Fin 3 → F9) :
    hermForm conj9 (toLinearEquiv g x) (toLinearEquiv g y) = hermForm conj9 x y :=
  (g : unitaryGroup).2 x y

/-- The linear map of the identity element is the identity linear equivalence. -/
@[simp] lemma toLinearEquiv_one :
    toLinearEquiv (1 : specialUnitaryGroup) = LinearEquiv.refl F9 (Fin 3 → F9) := rfl

/-- `toLinearEquiv` sends a product to the product of the underlying linear maps. -/
lemma toLinearEquiv_mul (g h : specialUnitaryGroup) :
    toLinearEquiv (g * h) = toLinearEquiv g * toLinearEquiv h := rfl

/-- Applying the linear map of a product is applying the two linear maps in turn. -/
lemma toLinearEquiv_mul_apply (g h : specialUnitaryGroup) (x : Fin 3 → F9) :
    toLinearEquiv (g * h) x = toLinearEquiv g (toLinearEquiv h x) := rfl

/-- Applying the linear map of an inverse is applying the inverse linear map. -/
lemma toLinearEquiv_inv_apply (g : specialUnitaryGroup) (x : Fin 3 → F9) :
    toLinearEquiv g⁻¹ x = (toLinearEquiv g).symm x := rfl

/-- The linear map of an inverse is the inverse of the linear map. -/
lemma toLinearEquiv_inv (g : specialUnitaryGroup) :
    toLinearEquiv g⁻¹ = (toLinearEquiv g)⁻¹ := rfl

/-- The linear map of a transvection is the corresponding Eichler transvection. -/
@[simp] lemma toLinearEquiv_transvection (u : Fin 3 → F9) (hu : hermForm conj9 u u = 0)
    (a : F9) (ha : a + a ^ 3 = 0) :
    toLinearEquiv (transvection u hu a ha) = eichlerTransvection u hu a := rfl

/-- Two special-unitary elements are equal once their underlying linear maps agree. -/
lemma specialUnitaryGroup_ext {g h : specialUnitaryGroup}
    (he : toLinearEquiv g = toLinearEquiv h) : g = h := Subtype.ext (Subtype.ext he)

/-- The determinant of the linear map of a special-unitary element is `1`. -/
lemma toLinearEquiv_det (g : specialUnitaryGroup) : LinearEquiv.det (toLinearEquiv g) = 1 := by
  simpa using (mem_specialUnitaryGroup_iff _).mp g.2

/-- A special-unitary element is `1` as soon as its linear map is the identity. -/
lemma toLinearEquiv_eq_refl_iff_one (g : specialUnitaryGroup) :
    toLinearEquiv g = LinearEquiv.refl F9 (Fin 3 → F9) ↔ g = 1 :=
  ⟨fun h ↦ Subtype.ext (Subtype.ext h), fun h ↦ h ▸ toLinearEquiv_one⟩

/-- There exists a nonzero isotropic vector. -/
lemma exists_isotropic_ne : ∃ u : Fin 3 → F9, u ≠ 0 ∧ hermForm conj9 u u = 0 := by
  obtain ⟨p⟩ : Nonempty IsotropicPoint := Fintype.card_pos_iff.mp <| by
    simp [card_isotropicPoint]
  exact ⟨p.1.rep, Projectivization.rep_nonzero p.1, by simpa using p.2⟩

/-- A fixed nonzero isotropic vector. -/
noncomputable def baseVec : Fin 3 → F9 := exists_isotropic_ne.choose

/-- `baseVec` is nonzero. -/
lemma baseVec_ne : baseVec ≠ 0 := exists_isotropic_ne.choose_spec.1

/-- `baseVec` is isotropic. -/
lemma baseVec_iso : hermForm conj9 baseVec baseVec = 0 := exists_isotropic_ne.choose_spec.2

/-- The isotropic projective point represented by `baseVec`. -/
noncomputable def a0Pt : IsotropicPoint :=
  ⟨Projectivization.mk F9 baseVec baseVec_ne,
    (isotropicProj_mk_iff baseVec baseVec_ne).2 baseVec_iso⟩

/-! ## Freeness of the action on hyperbolic pairs -/

/-- A special-unitary element fixing both vectors of a hyperbolic pair `(v0, v1)`
(where `h v0 v0 = 0`, `h v1 v1 = 0`, and `h v0 v1 = h v1 v0 = 1`) is the identity. -/
lemma su_fixing_hyperbolic_pair_eq_one
    (g : specialUnitaryGroup) (v0 v1 : Fin 3 → F9)
    (hi0 : hermForm conj9 v0 v0 = 0) (hi1 : hermForm conj9 v1 v1 = 0)
    (h01 : hermForm conj9 v0 v1 = 1) (h10 : hermForm conj9 v1 v0 = 1)
    (g0 : toLinearEquiv g v0 = v0) (g1 : toLinearEquiv g v1 = v1) : g = 1 := by
  obtain ⟨w, h0w, hw0, h1w, hw1, hww, hli⟩ := exists_orthogonal_unit v0 v1
    (by
      rintro rfl
      simp_all [hermForm_apply])
    hi0 hi1 h01 h10
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by norm_num)
  have hspan (x) : ∃ a b c : F9, x = a • v0 + b • v1 + c • w :=
    ⟨b.repr x 0, b.repr x 1, b.repr x 2, by
      simpa [b, Fin.sum_univ_three] using (b.sum_repr x).symm⟩
  suffices toLinearEquiv g w = w by
    rw [← toLinearEquiv_eq_refl_iff_one]
    ext1 x
    obtain ⟨a, b, c, rfl⟩ := hspan x
    simp [g0, g1, this]
  obtain ⟨a, b, c, hgw⟩ := hspan (toLinearEquiv g w)
  obtain rfl : a = 0 := by
    simpa [hermForm_add_left, hermForm_smul_left, hgw, g0, g1, h01, hi1, hw1] using
      toLinearEquiv_hermForm g w v1
  obtain rfl : b = 0 := by
    simpa [hermForm_add_left, hermForm_smul_left, hgw, g0, g1, h10, hw0] using
      toLinearEquiv_hermForm g w v0
  simp only [zero_smul, zero_add] at hgw
  suffices LinearEquiv.det (toLinearEquiv g) = c by
    rw [hgw, ← this, toLinearEquiv_det, Units.val_one, one_smul]
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b _, Matrix.det_fin_three]
  simp [b, LinearMap.toMatrix_apply, g0, g1, hgw, LinearMap.codRestrict,
    hli.repr_eq_single 0, hli.repr_eq_single 1, hli.repr_eq_single 2]

/-- Every nonzero isotropic vector has a hyperbolic partner `p`, that is, an
isotropic vector with `h u p = h p u = 1`. -/
lemma exists_isotropic_partner (u : Fin 3 → F9) (hu : u ≠ 0) (hui : hermForm conj9 u u = 0) :
    ∃ p : Fin 3 → F9,
    hermForm conj9 p p = 0 ∧ hermForm conj9 u p = 1 ∧ hermForm conj9 p u = 1 := by
  let p : IsotropicPoint :=
    ⟨Projectivization.mk F9 u hu, (isotropicProj_mk_iff u hu).2 hui⟩
  obtain ⟨q, hpq⟩ := Fintype.exists_ne_of_one_lt_card (by simp [card_isotropicPoint]) p
  obtain ⟨v0, v1, hv0, hv1, hv0p, _, hv0i, hv1i, h01, h10⟩ :=
    exists_hyperbolic_pair p q hpq.symm
  obtain ⟨μ, rfl⟩ := (Projectivization.mk_eq_mk_iff' F9 v0 u hv0 hu).mp <| by
    simpa [p] using hv0p
  refine ⟨(conj9 μ : F9) • v1, ?_, ?_, ?_⟩ <;> simp_all
  simpa only [conj9_involutive μ] using h01

/-! ## The corestricted permutation action -/

/-- The corestricted permutation homomorphism onto `psuPerm`. -/
noncomputable def toPsu : specialUnitaryGroup →* psuPerm :=
  (MulAction.toPermHom specialUnitaryGroup IsotropicPoint).rangeRestrict

/-- `toPsu` acts on isotropic points via the special-unitary action. -/
lemma toPsu_smul (s : specialUnitaryGroup) (p : IsotropicPoint) :
    (toPsu s) • p = s • p := rfl

/-- `toPsu` is surjective. -/
lemma toPsu_surjective : Function.Surjective toPsu :=
  MonoidHom.rangeRestrict_surjective _

end PSU33

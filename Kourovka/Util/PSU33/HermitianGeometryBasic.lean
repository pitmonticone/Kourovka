/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic.NormNum.Prime

/-!
# Hermitian geometry for the `PSU(3,3)` formalization

This file contains the field-independent Hermitian polarity API used by the
project-specific `PSU(3,3)` modules.
-/

namespace PSU33.HermitianForm

variable {K : Type*} [Field K]

/-- The standard Hermitian form on `Fin 3 → K` relative to the conjugation
`σ : K →+* K`, as a native sesquilinear map: `K`-linear in the first argument
and `σ`-semilinear in the second. -/
def hermForm (σ : K →+* K) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) →ₛₗ[σ] K :=
  LinearMap.mk₂'ₛₗ (RingHom.id K) σ (fun u v => ∑ i, u i * σ (v i))
    (fun u u' v => by simp [add_mul, Finset.sum_add_distrib])
    (fun c u v => by simp [Finset.mul_sum, mul_assoc])
    (fun u v v' => by simp [map_add, mul_add, Finset.sum_add_distrib])
    (fun c u v => by simp [Finset.mul_sum, mul_left_comm])

variable {σ : K →+* K}

/-- Evaluation of `hermForm`: the standard Hermitian pairing is `∑ i, u i * σ (v i)`. -/
lemma hermForm_apply (u v : Fin 3 → K) : hermForm σ u v = ∑ i, u i * σ (v i) := rfl

/-- Additivity of `hermForm` in the first argument. -/
lemma hermForm_add_left (u u' v : Fin 3 → K) :
    hermForm σ (u + u') v = hermForm σ u v + hermForm σ u' v := by simp

/-- `K`-linearity of `hermForm` in the first argument. -/
lemma hermForm_smul_left (a : K) (u v : Fin 3 → K) :
    hermForm σ (a • u) v = a * hermForm σ u v := by simp

/-- Additivity of `hermForm` in the second argument. -/
lemma hermForm_add_right (u v v' : Fin 3 → K) :
    hermForm σ u (v + v') = hermForm σ u v + hermForm σ u v' := by simp

/-- `σ`-semilinearity of `hermForm` in the second argument. -/
lemma hermForm_smul_right (a : K) (u v : Fin 3 → K) :
    hermForm σ u (a • v) = σ a * hermForm σ u v := by simp

/-- Hermitian symmetry of the form, given that the conjugation is involutive. -/
lemma hermForm_conj_symm (hσ : Function.Involutive σ) (u v : Fin 3 → K) :
    σ (hermForm σ u v) = hermForm σ v u := by
  simp only [hermForm_apply, map_sum, map_mul, hσ _]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Diagonal scaling law: `h (a • v) (a • v) = a * σ a * h v v`. -/
lemma hermForm_smul_self (a : K) (v : Fin 3 → K) :
    hermForm σ (a • v) (a • v) = a * σ a * hermForm σ v v := by
  rw [hermForm_smul_left, hermForm_smul_right]
  ring

/-- A projective point of `ℙ K (Fin 3 → K)` is isotropic when (any, equivalently
some) representative is isotropic for `hermForm`. -/
def IsotropicProj (σ : K →+* K) (p : Projectivization K (Fin 3 → K)) : Prop :=
  hermForm σ p.rep p.rep = 0

/-- Isotropy is a property of the projective point: it does not depend on the
chosen representative. -/
lemma isotropicProj_mk_iff (v : Fin 3 → K) (hv : v ≠ 0) :
    IsotropicProj σ (Projectivization.mk K v hv) ↔ hermForm σ v v = 0 := by
  unfold IsotropicProj
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ v (Projectivization.rep_nonzero _) hv).mp
    (Projectivization.mk_rep _)
  rw [← ha, Units.smul_def, hermForm_smul_self]
  simp [map_eq_zero_iff σ σ.injective, a.ne_zero]

/-- The unitary group of the Hermitian form: `K`-linear automorphisms of
`Fin 3 → K` preserving `hermForm`. -/
def unitaryGroup (σ : K →+* K) : Subgroup ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) where
  carrier := {f | ∀ u v, hermForm σ (f u) (f v) = hermForm σ u v}
  one_mem' := by
    intro u v
    rfl
  mul_mem' := by
    intro f g hf hg u v
    simpa using (hf (g u) (g v)).trans (hg u v)
  inv_mem' := by
    intro f hf u v
    simpa using (hf (f⁻¹ u) (f⁻¹ v)).symm

/-- Membership in the unitary group unfolds to preservation of `hermForm`. -/
lemma mem_unitaryGroup_iff (f : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :
    f ∈ unitaryGroup σ ↔ ∀ u v, hermForm σ (f u) (f v) = hermForm σ u v := Iff.rfl

/-- A unitary map sends isotropic projective points to isotropic projective
points. -/
lemma isotropicProj_smul (g : unitaryGroup σ) (p : Projectivization K (Fin 3 → K))
    (hp : IsotropicProj σ p) :
    IsotropicProj σ ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) • p) := by
  induction p using Projectivization.ind with
  | _ v hv =>
    rw [Projectivization.smul_mk]
    rw [isotropicProj_mk_iff] at hp ⊢
    simpa using (g.2 v v).trans hp

/-- The set of isotropic projective points of the polarity. -/
def IsotropicPoint (σ : K →+* K) := {p : Projectivization K (Fin 3 → K) // IsotropicProj σ p}

/-- The geometric action of the unitary group on the isotropic points. -/
instance : MulAction (unitaryGroup σ) (IsotropicPoint σ) where
  smul g p :=
    ⟨(g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) • p.1,
      isotropicProj_smul g p.1 p.2⟩
  one_smul p := by
    apply Subtype.ext
    show ((1 : unitaryGroup σ) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) • p.1 = p.1
    rw [Subgroup.coe_one, one_smul]
  mul_smul g g' p := by
    apply Subtype.ext
    show ((g * g' : unitaryGroup σ) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) • p.1 =
      (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) •
      ((g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) • p.1)
    rw [Subgroup.coe_mul, mul_smul]

/-- The special unitary group: unitary maps of determinant `1`, as a subgroup of
the unitary group. -/
def specialUnitaryGroup (σ : K →+* K) : Subgroup (unitaryGroup σ) :=
  (LinearEquiv.det.comp (unitaryGroup σ).subtype).ker

/-- The permutation image of the special unitary group acting on the isotropic
points. The kernel must be identified separately in each specialization before
interpreting this image as a projective special unitary group. -/
noncomputable def psuPerm (σ : K →+* K) : Subgroup (Equiv.Perm (IsotropicPoint σ)) :=
  (MulAction.toPermHom (specialUnitaryGroup σ) (IsotropicPoint σ)).range

/-!
### Isotropic points by normalized representatives

The isotropic projective points carry a canonical normalized representative: the
unique scalar multiple whose first nonzero coordinate is `1`.  This gives a
reusable geometric bijection between the isotropic points and concrete vector
representatives.
-/

/-- A vector of `Fin 3 → K` is normalized when its first nonzero coordinate is
`1`. -/
def IsNormalized (v : Fin 3 → K) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

/-- A normalized vector is nonzero. -/
lemma IsNormalized.ne_zero {v : Fin 3 → K} (h : IsNormalized v) : v ≠ 0 := by
  rintro rfl
  simp [IsNormalized] at h

/-- Every nonzero vector is a unit multiple of a normalized vector. -/
lemma exists_isNormalized_smul {r : Fin 3 → K} (hr : r ≠ 0) :
    ∃ v : Fin 3 → K, IsNormalized v ∧ ∃ a : Kˣ, a • v = r := by
  by_cases h0 : r 0 ≠ 0
  · refine ⟨(r 0)⁻¹ • r, ?_, ⟨Units.mk0 (r 0) h0, ?_⟩⟩ <;>
      simp_all +decide [IsNormalized]
  · by_cases h1 : r 1 ≠ 0
    · refine ⟨fun i => if i = 1 then 1 else r i / r 1, ?_, ?_⟩
      · simp_all +decide [IsNormalized]
      · refine ⟨Units.mk0 (r 1) h1, ?_⟩
        ext i
        fin_cases i <;> simp +decide [*, mul_div_cancel₀]
    · refine ⟨fun i => if i = 2 then 1 else 0, ?_, ?_⟩
      · simp_all +decide [IsNormalized]
      · push_neg at h0 h1
        refine ⟨Units.mk0 (r 2) ?_, ?_⟩
        · contrapose! hr
          ext i
          fin_cases i <;> simp_all +decide
        · ext i
          fin_cases i <;> simp +decide [h0, h1]

/-- Normalized representatives are unique up to scalar equivalence. -/
lemma IsNormalized.eq_of_smul {v w : Fin 3 → K} (hv : IsNormalized v)
    (hw : IsNormalized w) (a : Kˣ) (h : a • w = v) : v = w := by
  rcases hv with hv | hv | hv <;>
    rcases hw with hw | hw | hw <;>
    simp_all +decide [Units.smul_def] <;> aesop

/-- Isotropic points described by normalized isotropic vector representatives. -/
noncomputable def isotropicNormEquiv (σ : K →+* K) :
    {v : Fin 3 → K // IsNormalized v ∧ hermForm σ v v = 0} ≃ IsotropicPoint σ :=
  Equiv.ofBijective
    (fun v => ⟨Projectivization.mk K v.1 v.2.1.ne_zero,
      (isotropicProj_mk_iff v.1 v.2.1.ne_zero).2 v.2.2⟩)
    (by
      constructor
      · rintro ⟨v, hv, _⟩ ⟨w, hw, _⟩ h
        obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv.ne_zero
          hw.ne_zero).1 (congrArg Subtype.val h)
        exact Subtype.ext (IsNormalized.eq_of_smul hv hw a ha)
      · rintro ⟨q, hq⟩
        obtain ⟨v, hvN, a, hav⟩ := exists_isNormalized_smul (Projectivization.rep_nonzero q)
        have hmkv : Projectivization.mk K v hvN.ne_zero = q := by
          rw [← Projectivization.mk_rep q]
          exact (Projectivization.mk_eq_mk_iff K v q.rep hvN.ne_zero
            (Projectivization.rep_nonzero q)).2 ⟨a⁻¹, by
              simpa only [inv_smul_eq_iff] using hav.symm⟩
        refine ⟨⟨v, hvN, ?_⟩, Subtype.ext hmkv⟩
        rwa [← isotropicProj_mk_iff (σ := σ) v hvN.ne_zero, hmkv])

/-- If `S` generates the special unitary group, then its image under the natural
permutation representation generates the projective special unitary permutation
group. -/
theorem psuPerm_eq_closure_image (S : Set (specialUnitaryGroup σ))
    (hS : Subgroup.closure S = ⊤) :
    psuPerm σ = Subgroup.closure
      ((MulAction.toPermHom (specialUnitaryGroup σ) (IsotropicPoint σ)) '' S) := by
  show (MulAction.toPermHom (specialUnitaryGroup σ) (IsotropicPoint σ)).range = _
  rw [MonoidHom.range_eq_map, ← hS, MonoidHom.map_closure]

/-- The two-generator specialization of `psuPerm_eq_closure_image`. -/
theorem psuPerm_eq_closure_pair (g h : specialUnitaryGroup σ)
    (hgh : Subgroup.closure ({g, h} : Set (specialUnitaryGroup σ)) = ⊤) :
    psuPerm σ = Subgroup.closure
      ({MulAction.toPermHom (specialUnitaryGroup σ) (IsotropicPoint σ) g,
        MulAction.toPermHom (specialUnitaryGroup σ) (IsotropicPoint σ) h} :
        Set (Equiv.Perm (IsotropicPoint σ))) := by
  rw [psuPerm_eq_closure_image _ hgh, Set.image_pair]

/-- Restricting `Projectivization.nonZeroEquivProjectivizationProdUnits` to the
isotropic locus: nonzero isotropic vectors correspond bijectively to isotropic
projective points paired with a nonzero scalar.  This is the structural input to
the `q³ + 1` count of isotropic points. -/
noncomputable def isoEquiv :
    {v : Fin 3 → K // v ≠ 0 ∧ hermForm σ v v = 0} ≃ IsotropicPoint σ × Kˣ :=
  let e := Projectivization.nonZeroEquivProjectivizationProdUnits K (Fin 3 → K)
  (Equiv.subtypeSubtypeEquivSubtypeInter (· ≠ 0)
    (fun v => hermForm σ v v = 0)).symm.trans <|
  (Equiv.subtypeEquiv e (fun w => by
    rw [show (e w).1 = Projectivization.mk K w.1 w.2 from rfl,
      isotropicProj_mk_iff])).trans
  (Equiv.prodSubtypeFstEquivSubtypeProd (p := IsotropicProj σ))

/-- The number of nonzero isotropic vectors equals the number of isotropic
projective points times the number of nonzero scalars. -/
lemma card_isotropic_eq_mul :
    Nat.card {v : Fin 3 → K // v ≠ 0 ∧ hermForm σ v v = 0}
      = Nat.card (IsotropicPoint σ) * Nat.card Kˣ := by
  rw [Nat.card_congr isoEquiv, Nat.card_prod]

/-!
### Explicit torus and Weyl elements

We provide a small API of explicit unitary maps and their membership in the
unitary / special unitary groups, for the standard Hermitian form
`hermForm σ u v = ∑ i, u i * σ (v i)` on `Fin 3 → K`.
-/

/-- The diagonal linear automorphism of `Fin 3 → K` scaling coordinate `i` by the
unit `d i`. -/
noncomputable def diagEquiv (d : Fin 3 → Kˣ) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun v := fun i => (d i : K) * v i
  map_add' u v := by
    funext i
    simp [mul_add]
  map_smul' a v := by
    funext i
    simp
    ring
  invFun v := fun i => ((d i)⁻¹ : K) * v i
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp

/-- The coordinate-permutation linear automorphism of `Fin 3 → K` induced by
`p : Equiv.Perm (Fin 3)`. -/
noncomputable def permEquiv
    (p : Equiv.Perm (Fin 3)) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun v := fun i => v (p i)
  map_add' u v := by
    funext i
    simp
  map_smul' a v := by
    funext i
    simp
  invFun v := fun i => v (p.symm i)
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp

/-- A diagonal map with norm-one entries (`d i * σ (d i) = 1`) is unitary. -/
lemma diagEquiv_mem_unitaryGroup (d : Fin 3 → Kˣ)
    (h : ∀ i, (d i : K) * σ (d i) = 1) : diagEquiv d ∈ unitaryGroup σ := by
  intro u v
  simp only [hermForm_apply, diagEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul]
  linear_combination (u i * σ (v i)) * h i

/-- A coordinate permutation is always unitary for the standard Hermitian form. -/
lemma permEquiv_mem_unitaryGroup (p : Equiv.Perm (Fin 3)) :
    permEquiv p ∈ unitaryGroup σ := by
  intro u v
  simpa only [hermForm_apply, permEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk] using Equiv.sum_comp p (fun i => u i * σ (v i))

/-- The determinant of a diagonal torus element is the product of its entries. -/
lemma det_diagEquiv (d : Fin 3 → Kˣ) :
    LinearEquiv.det (diagEquiv d) = ∏ i, d i := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  push_cast
  rw [← LinearMap.det_toMatrix (Pi.basisFun K (Fin 3))]
  have hmat :
      LinearMap.toMatrix (Pi.basisFun K (Fin 3)) (Pi.basisFun K (Fin 3))
        (diagEquiv d : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) =
      Matrix.diagonal (fun i => (d i : K)) := by
    ext i j
    by_cases h : i = j <;> simp [diagEquiv, Matrix.diagonal, h]
  rw [hmat, Matrix.det_diagonal]

/-- The determinant of an even coordinate permutation is `1`. -/
lemma det_permEquiv_eq_one (p : Equiv.Perm (Fin 3)) (h : Equiv.Perm.sign p = 1) :
    LinearEquiv.det (permEquiv (K := K) p) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (Pi.basisFun K (Fin 3))]
  have hmat :
      LinearMap.toMatrix (Pi.basisFun K (Fin 3)) (Pi.basisFun K (Fin 3))
        (permEquiv p : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)).toLinearMap =
      Equiv.Perm.permMatrix K p := by
    ext i j
    simp [permEquiv, Equiv.Perm.permMatrix, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, eq_comm]
  rw [hmat, Matrix.det_permutation, h]
  simp

/-- Membership in the special unitary group is exactly the determinant-one
condition on the underlying linear automorphism. -/
lemma mem_specialUnitaryGroup_iff (g : unitaryGroup σ) :
    g ∈ specialUnitaryGroup σ ↔
      LinearEquiv.det (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) = 1 := by
  rw [specialUnitaryGroup, MonoidHom.mem_ker]
  rfl

/-- An explicit diagonal torus element of the special unitary group. -/
noncomputable def diagSpecialUnitary (d : Fin 3 → Kˣ)
    (hnorm : ∀ i, (d i : K) * σ (d i) = 1) (hdet : ∏ i, d i = 1) :
    specialUnitaryGroup σ :=
  ⟨⟨diagEquiv d, diagEquiv_mem_unitaryGroup d hnorm⟩,
    (mem_specialUnitaryGroup_iff _).mpr ((det_diagEquiv d).trans hdet)⟩

/-- An explicit Weyl/monomial element of the special unitary group. -/
noncomputable def permSpecialUnitary (p : Equiv.Perm (Fin 3))
    (hp : Equiv.Perm.sign p = 1) : specialUnitaryGroup σ :=
  ⟨⟨permEquiv p, permEquiv_mem_unitaryGroup p⟩,
    (mem_specialUnitaryGroup_iff _).mpr (det_permEquiv_eq_one p hp)⟩

/-- The underlying linear map of `diagSpecialUnitary` is `diagEquiv d`. -/
@[simp] lemma coe_diagSpecialUnitary (d : Fin 3 → Kˣ)
    (hnorm : ∀ i, (d i : K) * σ (d i) = 1) (hdet : ∏ i, d i = 1) :
    ((diagSpecialUnitary d hnorm hdet).1.1 :
      (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) = diagEquiv d := rfl

/-- The underlying linear map of `permSpecialUnitary` is `permEquiv p`. -/
@[simp] lemma coe_permSpecialUnitary (p : Equiv.Perm (Fin 3))
    (hp : Equiv.Perm.sign p = 1) :
    ((permSpecialUnitary (σ := σ) p hp).1.1 :
      (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) = permEquiv p := rfl

/-!
### Root-unipotent (Eichler/Siegel transvection) family

This is the third explicit family: the **root-unipotent / transvection**
elements `E_{u,a}` attached to an *isotropic* vector `u` (`hermForm σ u u = 0`)
and a parameter `a`,

  `E_{u,a}(x) = x + a * hermForm σ x u • u`.

These are the unipotent root elements of the Hermitian unitary geometry. Every
membership/determinant fact below is proved directly from the sesquilinearity of
`hermForm`, the isotropy `hermForm σ u u = 0`, the Hermitian symmetry
`hermForm_conj_symm` and standard linear/matrix algebra:

* `transvectionMap u a` is the underlying linear map (defined for any `u`, `a`).
* `eichlerTransvection u hu a` upgrades it to a `LinearEquiv` once `u` is
  isotropic (its inverse is `E_{u,-a}`).
* `eichlerTransvection_mem_unitaryGroup`: `E_{u,a}` is unitary exactly when the
  parameter is *skew*, `a + σ a = 0` (the conjugation maps `a ↦ -a`).
* `det_eichlerTransvection`: `E_{u,a}` always has determinant `1` (it is `1 + N`
  with `N` a rank-one nilpotent of trace `a * hermForm σ u u = 0`), so a skew
  transvection lies in the *special* unitary group `eichlerSpecialUnitary`. -/

/-- The underlying linear map of the Eichler/Siegel transvection along a vector
`u` with parameter `a`: `x ↦ x + a * hermForm σ x u • u`. -/
noncomputable def transvectionMap (u : Fin 3 → K) (a : K) :
    (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun x := x + (a * hermForm σ x u) • u
  map_add' x y := by
    rw [hermForm_add_left, mul_add, add_smul]
    abel
  map_smul' c x := by
    ext i
    simp
    ring

/-- Evaluation of the transvection linear map. -/
@[simp] lemma transvectionMap_apply (u : Fin 3 → K) (a : K) (x : Fin 3 → K) :
    transvectionMap (σ := σ) u a x = x + (a * hermForm σ x u) • u := rfl

/-- For an isotropic vector `u`, the transvections compose additively, so
`transvectionMap u a` and `transvectionMap u (-a)` are mutually inverse. -/
lemma transvection_comp (u : Fin 3 → K) (hu : hermForm σ u u = 0) (a : K) :
    transvectionMap (σ := σ) u a ∘ₗ transvectionMap (σ := σ) u (-a) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp [hu]

/-- The **Eichler/Siegel transvection** `E_{u,a}` along an isotropic vector `u`:
the linear automorphism `x ↦ x + a * hermForm σ x u • u`.  This is the explicit
root-unipotent element of the Hermitian geometry. -/
noncomputable def eichlerTransvection (u : Fin 3 → K) (hu : hermForm σ u u = 0) (a : K) :
    (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
  LinearEquiv.ofLinear (transvectionMap u a) (transvectionMap u (-a))
    (transvection_comp (σ := σ) u hu a)
    (by simpa using transvection_comp (σ := σ) u hu (-a))

/-- Evaluation of the Eichler/Siegel transvection `E_{u,a}`. -/
@[simp] lemma eichlerTransvection_apply (u : Fin 3 → K) (hu : hermForm σ u u = 0)
    (a : K) (x : Fin 3 → K) :
    eichlerTransvection (σ := σ) u hu a x = x + (a * hermForm σ x u) • u := rfl

/-- A skew transvection (`a + σ a = 0`) along an isotropic vector is unitary. -/
lemma eichlerTransvection_mem_unitaryGroup (hσ : Function.Involutive σ)
    (u : Fin 3 → K) (hu : hermForm σ u u = 0) (a : K) (ha : a + σ a = 0) :
    eichlerTransvection u hu a ∈ unitaryGroup σ := by
  intro x y
  rw [eichlerTransvection_apply, eichlerTransvection_apply,
    hermForm_add_left, hermForm_add_right, hermForm_add_right,
    hermForm_smul_left, hermForm_smul_left, hermForm_smul_right, hermForm_smul_right, hu,
    map_mul, hermForm_conj_symm hσ y u]
  linear_combination (hermForm σ x u * hermForm σ u y) * ha

/-- An Eichler transvection along an isotropic vector always has determinant
`1`: it is `1 + N` with `N` a rank-one nilpotent of trace `a * hermForm σ u u
= 0`. -/
lemma det_eichlerTransvection (u : Fin 3 → K) (hu : hermForm σ u u = 0) (a : K) :
    LinearEquiv.det (eichlerTransvection u hu a) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  push_cast
  rw [show (eichlerTransvection (σ := σ) u hu a : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
    = transvectionMap (σ := σ) u a from rfl,
    ← LinearMap.det_toMatrix (Pi.basisFun K (Fin 3))]
  have hmat :
      LinearMap.toMatrix (Pi.basisFun K (Fin 3)) (Pi.basisFun K (Fin 3))
        (transvectionMap (σ := σ) u a) =
      Matrix.of (fun i j => (1 : Matrix (Fin 3) (Fin 3) K) i j + a * σ (u j) * u i) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, transvectionMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.basisFun_apply, Pi.basisFun_repr, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [show hermForm σ (Pi.single j (1 : K)) u = σ (u j) by
      simp [hermForm_apply, Pi.single_apply]]
    by_cases h : i = j <;> simp [Matrix.one_apply, Pi.single_apply, h]
  rw [hmat, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.one_apply, Fin.reduceEq, ↓reduceIte]
  have hu' : u 0 * σ (u 0) + u 1 * σ (u 1) + u 2 * σ (u 2) = 0 := by
    simpa only [hermForm_apply, Fin.sum_univ_three] using hu
  linear_combination a * hu'

/-- An explicit **root-unipotent (transvection) element** of the special unitary
group: the skew Eichler transvection `E_{u,a}` (with `a + σ a = 0`) along an
isotropic vector `u`. -/
noncomputable def eichlerSpecialUnitary (hσ : Function.Involutive σ)
    (u : Fin 3 → K) (hu : hermForm σ u u = 0) (a : K) (ha : a + σ a = 0) :
    specialUnitaryGroup σ :=
  ⟨⟨eichlerTransvection u hu a, eichlerTransvection_mem_unitaryGroup hσ u hu a ha⟩,
    (mem_specialUnitaryGroup_iff _).mpr (det_eichlerTransvection u hu a)⟩

/-- The underlying linear map of `eichlerSpecialUnitary` is the transvection. -/
@[simp] lemma coe_eichlerSpecialUnitary (hσ : Function.Involutive σ)
    (u : Fin 3 → K) (hu : hermForm σ u u = 0) (a : K) (ha : a + σ a = 0) :
    ((eichlerSpecialUnitary hσ u hu a ha).1.1 :
      (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) = eichlerTransvection u hu a := rfl

/-!
### Conjugation and additivity relations; the root-generated subgroup

These are the structural relations toward the generation theorem
`Subgroup.closure {transvections} = ⊤`.  The family of Eichler/Siegel
transvections is closed under conjugation by the whole unitary group: the
conjugate of `E_{u,a}` by a unitary map `g` is `E_{g u, a}`.  Along a fixed
isotropic vector the transvections add (`E_{u,a} · E_{u,b} = E_{u,a+b}`).  Hence
the subgroup of `specialUnitaryGroup σ` generated by all skew transvections is
*normal* — the strongest reusable intermediate fact below the still-open full
generation statement.
-/

/-- A unitary map preserves isotropy of vectors. -/
lemma hermForm_self_image_eq_zero (g : unitaryGroup σ) (u : Fin 3 → K)
    (hu : hermForm σ u u = 0) :
    hermForm σ ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) u)
      ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) u) = 0 := by rwa [g.2 u u]

/-- **Conjugation formula for transvections.**  Conjugating the Eichler/Siegel
transvection `E_{u,a}` by a unitary map `g` gives the transvection `E_{g u, a}`
along the image vector, with the same parameter. -/
lemma eichlerTransvection_conj (g : unitaryGroup σ) (u : Fin 3 → K)
    (hu : hermForm σ u u = 0) (a : K) :
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) * eichlerTransvection u hu a
      * (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))⁻¹ =
      eichlerTransvection ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) u)
      (hermForm_self_image_eq_zero g u hu) a := by
  ext x
  have := g.2 (g.1.symm x) u
  aesop

/-- **Additivity of transvections along a fixed isotropic vector**:
`E_{u,a} · E_{u,b} = E_{u,a+b}`. -/
lemma eichlerTransvection_mul (u : Fin 3 → K) (hu : hermForm σ u u = 0) (a b : K) :
    eichlerTransvection u hu a * eichlerTransvection u hu b
      = eichlerTransvection u hu (a + b) := by
  ext x
  simp +decide [hu]
  ring

/-- The set of all skew Eichler/Siegel transvections inside the special unitary
group (the union of all root subgroups). -/
def transvectionSet (hσ : Function.Involutive σ) : Set (specialUnitaryGroup σ) :=
  {g | ∃ (u : Fin 3 → K) (hu : hermForm σ u u = 0) (a : K) (ha : a + σ a = 0),
    g = eichlerSpecialUnitary hσ u hu a ha}

/-- The root-generated subgroup of the special unitary group: the subgroup
generated by all skew transvections. -/
def rootGenerated (hσ : Function.Involutive σ) : Subgroup (specialUnitaryGroup σ) :=
  Subgroup.closure (transvectionSet hσ)

/-- Conjugating a transvection (as a special-unitary element) by any special
unitary element gives another transvection: the transvection set is stable under
conjugation. -/
lemma transvectionSet_conj_mem (hσ : Function.Involutive σ)
    (p : specialUnitaryGroup σ) (x : specialUnitaryGroup σ)
    (hx : x ∈ transvectionSet hσ) : p * x * p⁻¹ ∈ transvectionSet hσ := by
  obtain ⟨u, hu, a, ha, rfl⟩ := hx
  exact ⟨p.1.1 u, hermForm_self_image_eq_zero p.1 u hu, a, ha,
    by
      ext
      simp [eichlerTransvection_conj]⟩

/-- **The root-generated subgroup is normal in the special unitary group.**
This is the strongest reusable intermediate theorem toward the full generation
statement `rootGenerated hσ = ⊤`. -/
theorem rootGenerated_normal (hσ : Function.Involutive σ) :
    (rootGenerated hσ).Normal := by
  refine ⟨fun x hx g => Subgroup.closure_induction
    (fun y hy => Subgroup.subset_closure (transvectionSet_conj_mem hσ g y hy)) (by simp)
    (fun _ _ _ _ hx' hy' => by simpa [mul_assoc] using Subgroup.mul_mem _ hx' hy')
    (fun _ _ hx' => by simpa [mul_assoc] using Subgroup.inv_mem _ hx') hx⟩

end PSU33.HermitianForm

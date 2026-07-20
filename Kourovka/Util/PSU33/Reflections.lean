/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.RootGeneration
import Kourovka.Util.PSU33.Cardinality
import Mathlib.Tactic.LinearCombination'
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime

/-!
# Involution counts for `PSU(3,3)`

Anisotropic-point reflections and the order `2` and order `4` counts for the
geometric `SU(3,3)` model.
-/

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

section InvolutionOrderFourCount

/-- The **anisotropic** projective points of the `PSU(3,3)` polarity: the
projective points that are *not* isotropic. -/
abbrev AnisotropicPoint : Type :=
  {p : Projectivization F9 (Fin 3 → F9) // ¬ IsotropicProj conj9 p}

/-- `Projectivization F9 (Fin 3 → F9)` is a finite type. -/
noncomputable instance instFintypeProjectivizationF9 :
    Fintype (Projectivization F9 (Fin 3 → F9)) :=
  Fintype.ofFinite _

/-- The anisotropic projective points form a finite type. -/
noncomputable instance instFintypeAnisotropicPoint :
    Fintype AnisotropicPoint :=
  Fintype.ofFinite _

/-- There are `91` projective points of `ℙ²(GF(9))` (`q² + q + 1 = 91`). -/
theorem card_projectivization_F9 :
    Nat.card (Projectivization F9 (Fin 3 → F9)) = 91 := by
  simpa [card_f9] using
    Projectivization.card_of_finrank F9 (Fin 3 → F9) (n := 3) (by norm_num)

/-- **There are `63` anisotropic projective points for the `PSU(3,3)` polarity**
(`91 - 28 = 63`). -/
theorem card_anisotropicPoint : Fintype.card AnisotropicPoint = 63 := by
  rw [show Fintype.card AnisotropicPoint =
      Fintype.card (Projectivization F9 (Fin 3 → F9)) - Fintype.card IsotropicPoint by
    convert Fintype.card_subtype_compl
      (p := fun p : Projectivization F9 (Fin 3 → F9) => IsotropicProj conj9 p) using 1
    convert rfl]
  rw [← Nat.card_eq_fintype_card, card_projectivization_F9, card_isotropicPoint]

/-!
## The Hermitian reflection in an anisotropic vector

For an anisotropic vector `w` (i.e. `⟨w,w⟩ ≠ 0`) the **Hermitian reflection**
`r_w : x ↦ -x - (⟨x,w⟩ / ⟨w,w⟩) • w` is the linear map fixing `w` and acting as
`-1` on `w^⊥`.  It is a unitary involution of determinant `1`, hence an element
of `SU(3,3)` of order `2`.
-/

/-- The underlying linear map of the Hermitian reflection in `w`:
`x ↦ -x - (⟨x,w⟩ * ⟨w,w⟩⁻¹) • w`. -/
noncomputable def reflMap (w : Fin 3 → F9) :
    (Fin 3 → F9) →ₗ[F9] (Fin 3 → F9) where
  toFun x := -x - (hermForm conj9 x w * (hermForm conj9 w w)⁻¹) • w
  map_add' x y := by
    simp only [hermForm_add_left, add_mul, add_smul]
    abel
  map_smul' c x := by
    simp only [hermForm_smul_left, RingHom.id_apply, smul_sub, smul_neg, smul_smul,
      mul_assoc]

/-- `reflMap w x = -x - (⟨x, w⟩ * ⟨w, w⟩⁻¹) • w`. -/
@[simp] lemma reflMap_apply (w x : Fin 3 → F9) :
    reflMap w x = -x - (hermForm conj9 x w * (hermForm conj9 w w)⁻¹) • w := rfl

/-- The reflection in an anisotropic vector is an involution. -/
lemma reflMap_reflMap (w x : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    reflMap w (reflMap w x) = x := by
  have hkey : hermForm conj9 (reflMap w x) w =
      -(2 : F9) * hermForm conj9 x w := by
    rw [reflMap_apply, sub_eq_add_neg,
      show (-x : Fin 3 → F9) = (-1 : F9) • x by module,
      show -((hermForm conj9 x w * (hermForm conj9 w w)⁻¹) • w) =
        (-(hermForm conj9 x w * (hermForm conj9 w w)⁻¹)) • w by module,
      hermForm_add_left, hermForm_smul_left, hermForm_smul_left]
    field_simp
    ring
  rw [reflMap_apply, hkey, reflMap_apply,
    show (-(2 : F9) * hermForm conj9 x w) * (hermForm conj9 w w)⁻¹ =
      (-(2 : F9)) * (hermForm conj9 x w * (hermForm conj9 w w)⁻¹) by ring,
    show (-(2 : F9)) = (1 : F9) by linear_combination -three_eq_zero]
  module

/-- The Hermitian reflection in an anisotropic vector `w`, as a linear
equivalence. -/
noncomputable def reflEquiv (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    (Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9) :=
  LinearEquiv.ofLinear (reflMap w) (reflMap w)
    (LinearMap.ext fun x => reflMap_reflMap w x hn)
    (LinearMap.ext fun x => reflMap_reflMap w x hn)

/-- Evaluation lemma for `reflEquiv`. -/
@[simp] lemma reflEquiv_apply (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0)
    (x : Fin 3 → F9) : reflEquiv w hn x = reflMap w x := rfl

/-- The Hermitian reflection preserves the Hermitian form: it is unitary. -/
lemma reflEquiv_mem_unitary (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    ∀ u v, hermForm conj9 (reflEquiv w hn u) (reflEquiv w hn v) = hermForm conj9 u v := by
  simp +decide [sub_eq_add_neg, add_assoc, hermForm_add_right]
  ring_nf
  simp +decide [hn, mul_left_comm, mul_comm, hermForm_conj_symm conj9_involutive]
  ring_nf
  grind +ring

/-- The Hermitian reflection has determinant `1`. -/
lemma det_reflEquiv (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    LinearEquiv.det (reflEquiv w hn) = 1 := by
  rw [← Units.val_inj]
  simp +decide [LinearEquiv.coe_det]
  rw [← LinearMap.det_toMatrix (Pi.basisFun F9 (Fin 3))]
  convert Matrix.det_fin_three _
  simp +decide [reflEquiv_apply, reflMap_apply]
  simp +decide [Fin.sum_univ_three, hermForm_apply] at *
  grind +ring

/-- The Hermitian reflection in an anisotropic vector, as an element of
`SU(3,3)`. -/
noncomputable def reflSU (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    specialUnitaryGroup :=
  mkSpecialUnitary (reflEquiv w hn) (reflEquiv_mem_unitary w hn) (det_reflEquiv w hn)

/-- Evaluation lemma: the linear equivalence underlying `reflSU w hn` is
`reflEquiv w hn`. -/
@[simp] lemma toLinearEquiv_reflSU (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    toLinearEquiv (reflSU w hn) = reflEquiv w hn := rfl

/-- The reflection squares to the identity in `SU(3,3)`. -/
lemma reflSU_mul_self (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    reflSU w hn * reflSU w hn = 1 := by
  ext x
  convert congr_fun (reflMap_reflMap w x hn) ‹_› using 1

/-- A vector is fixed by the reflection in `w` iff it lies on the line `⟨w⟩`. -/
lemma reflMap_eq_self_iff (w x : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    reflMap w x = x ↔ ∃ c : F9, x = c • w := by
  constructor
  · intro h
    simp_all +decide [reflMap_apply, funext_iff]
    use (hermForm conj9 x w * (hermForm conj9 w w)⁻¹) * (1 / (-2))
    grind +ring
  · rintro ⟨c, rfl⟩
    ext i
    fin_cases i <;> simp_all +decide [reflMap_apply] <;> ring_nf <;> grind +ring

/-- The reflection is not the identity. -/
lemma reflSU_ne_one (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    reflSU w hn ≠ 1 := by
  by_contra h_contra
  have h_basis (x : Fin 3 → F9) : reflMap w x = x := by
    change toLinearEquiv (reflSU w hn) x = x
    simp [h_contra]
  have h_span (i : Fin 3) : ∃ c : F9, Pi.single i 1 = c • w :=
    reflMap_eq_self_iff w (Pi.single i 1) hn |>.1 (h_basis _)
  obtain ⟨c₀, hc₀⟩ := h_span 0
  obtain ⟨c₁, hc₁⟩ := h_span 1
  obtain ⟨c₂, hc₂⟩ := h_span 2
  simp_all +decide [funext_iff, Fin.forall_fin_succ]

/-- The reflection in an anisotropic vector has order `2`. -/
lemma orderOf_reflSU (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    orderOf (reflSU w hn) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by simpa [pow_two] using reflSU_mul_self w hn) (reflSU_ne_one w hn)

/-- Rescaling the anisotropic vector by a nonzero scalar does not change the
reflection: it depends only on the line `⟨w⟩`. -/
lemma reflMap_smul (w : Fin 3 → F9) (c : F9) (hc : c ≠ 0) :
    reflMap (c • w) = reflMap w := by
  ext x
  simp +decide [reflMap_apply, smul_smul]
  by_cases h : conj9 c = 0 <;> simp_all +decide [mul_assoc, mul_comm, mul_left_comm]

/-- The reflection in `w` fixes `w`. -/
lemma reflMap_self (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0) :
    reflMap w w = w :=
  (reflMap_eq_self_iff w w hn).2 ⟨1, by simp⟩

/-- Rescaling the anisotropic vector by a nonzero scalar does not change the
special-unitary reflection. -/
lemma reflSU_smul (w : Fin 3 → F9) (c : F9) (hc : c ≠ 0)
    (hn1 : hermForm conj9 (c • w) (c • w) ≠ 0) (hn2 : hermForm conj9 w w ≠ 0) :
    reflSU (c • w) hn1 = reflSU w hn2 :=
  specialUnitaryGroup_ext <| LinearEquiv.toLinearMap_injective <| reflMap_smul w c hc

/-!
## The bijection between order-two elements and anisotropic points

The map sending an anisotropic point `p` to the Hermitian reflection in (any
representative of) `p` is a bijection onto the order-two elements of `SU(3,3)`.
The injectivity is the fixed-line characterization `reflMap_eq_self_iff`; the
surjectivity is the classification `involution_eq_reflSU` (every nontrivial
involution is a Hermitian reflection in its anisotropic `+1`-eigenline).
-/

/-- The chosen representative of an anisotropic point is anisotropic. -/
lemma aniso_rep (p : AnisotropicPoint) :
    hermForm conj9 p.1.rep p.1.rep ≠ 0 := p.2

/-- The map sending an anisotropic point to the special-unitary reflection in
it, packaged as an order-two element. -/
noncomputable def anisoToInvol (p : AnisotropicPoint) :
    {g : specialUnitaryGroup // orderOf g = 2} :=
  ⟨reflSU p.1.rep (aniso_rep p), orderOf_reflSU _ _⟩

/-- For an involution `L` (i.e. `L * L = 1`) on the `3`-dimensional space over
`F9` with `det L = 1` and `L ≠ 1`, the fixed subspace `ker (L - 1)` is a line.
This is the determinant/eigenvalue dimension count: the quotient by the fixed
space is `-1`, so `det L = (-1) ^ finrank (V ⧸ fixed)`, forcing the codimension
of the fixed space to be even, hence (being `≤ 3` and `≠ 0`, since `L ≠ 1`) equal
to `2`. -/
lemma finrank_ker_sub_one_eq_one
    (L : Module.End F9 (Fin 3 → F9)) (hL : L * L = 1) (hne : L ≠ 1)
    (hdet : LinearMap.det L = 1) :
    Module.finrank F9 (LinearMap.ker (L - 1)) = 1 := by
  have hle : LinearMap.ker (L - 1) ≤ Submodule.comap L (LinearMap.ker (L - 1)) := by
    intro x hx
    simp_all +decide [sub_eq_iff_eq_add]
  have h_det : LinearMap.det L =
      (-1 : F9) ^ Module.finrank F9
        ((Fin 3 → F9) ⧸ LinearMap.ker (L - 1)) := by
    rw [
      LinearMap.det_eq_det_mul_det (L - 1).ker L hle,
      show LinearMap.det (LinearMap.restrict L hle) = 1 from ?_,
      show LinearMap.det (Submodule.mapQ (LinearMap.ker (L - 1))
        (LinearMap.ker (L - 1)) L hle) =
        (-1 : F9) ^ Module.finrank F9
        ((Fin 3 → F9) ⧸ LinearMap.ker (L - 1)) from ?_]
    · norm_num
    · convert LinearMap.det_smul (-1 : F9)
        (LinearMap.id :
          ((Fin 3 → F9) ⧸ LinearMap.ker (L - 1)) →ₗ[F9]
          ((Fin 3 → F9) ⧸ LinearMap.ker (L - 1))) using 1
      · congr 1
        ext ⟨x⟩
        simp +decide [Submodule.mapQ]
        erw [Submodule.Quotient.eq]
        simp_all +decide [add_comm, LinearMap.ext_iff]
      · norm_num
    · convert LinearMap.det_id
      ext x
      simp +decide [sub_eq_zero.mp (LinearMap.mem_ker.mp x.2)]
  have := Submodule.finrank_quotient_add_finrank (LinearMap.ker (L - 1))
  simp_all +decide
  by_cases h : Even (Module.finrank F9
    ((Fin 3 → F9) ⧸ (L - 1 |> LinearMap.ker))) <;>
    simp_all +decide
  · rcases n : Module.finrank F9 ((Fin 3 → F9) ⧸ (L - 1 |> LinearMap.ker)) with
      (_ | _ | _ | _ | n) <;> simp_all +arith +decide
    have h_contra : LinearMap.ker (L - 1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by aesop)
    simp_all +decide [LinearMap.ext_iff, Submodule.eq_top_iff']
    exact hne.elim fun x hx => hx <| sub_eq_zero.mp <| h_contra x
  · exact (one_ne_negone_F9.symm hdet).elim

/-- The Hermitian form is nondegenerate: if `hermForm conj9 x w = 0` for all `x`
then `w = 0`. -/
lemma hermForm_right_nondegen (w : Fin 3 → F9)
    (h : ∀ x, hermForm conj9 x w = 0) : w = 0 := by
  simp_all +decide [funext_iff, Fin.forall_fin_succ]
  have h0 := h (Pi.single 0 1)
  have h1 := h (Pi.single 1 1)
  have h2 := h (Pi.single 2 1)
  simp_all +decide [Fin.sum_univ_three, hermForm_apply]

/-- **Every nontrivial involution of `SU(3,3)` is a Hermitian reflection.**
An order-two element is semisimple in characteristic `3` with determinant `1`,
so its eigenvalues are `1, -1, -1` and its `1`-eigenspace is an anisotropic
line; it is the reflection in that line. -/
lemma involution_eq_reflSU (g : specialUnitaryGroup) (hg : orderOf g = 2) :
    ∃ (w : Fin 3 → F9) (hn : hermForm conj9 w w ≠ 0), g = reflSU w hn := by
  obtain ⟨L, hL⟩ :
      ∃ L : Module.End F9 (Fin 3 → F9),
        (toLinearEquiv g).toLinearMap = L ∧ L * L = 1 ∧ L ≠ 1 ∧ LinearMap.det L = 1 := by
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · have := pow_orderOf_eq_one g
      simp_all +decide [pow_succ]
      convert congr_arg (fun f : specialUnitaryGroup =>
        (toLinearEquiv f : (Fin 3 → F9) →ₗ[F9] (Fin 3 → F9))) this using 1
    · have h_g_ne_one : g ≠ 1 := by
        aesop
      contrapose! h_g_ne_one
      exact Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun x => by
        simpa using congr_arg (fun f => f x) h_g_ne_one
    · convert toLinearEquiv_det g
      rw [← Units.val_inj]
      simp +decide [LinearEquiv.coe_det]
  obtain ⟨w, hw⟩ :
      ∃ w : Fin 3 → F9,
        w ≠ 0 ∧ L w = w ∧ ∀ y : Fin 3 → F9, L y = y → ∃ c : F9, y = c • w := by
    obtain ⟨w, hw⟩ := finrank_eq_one_iff'.mp <|
      finrank_ker_sub_one_eq_one L hL.2.1 hL.2.2.1 hL.2.2.2
    refine ⟨w, ?_, ?_, ?_⟩ <;> simp_all +decide [sub_eq_iff_eq_add]
    · exact sub_eq_zero.mp (LinearMap.mem_ker.mp w.2)
    · exact fun y hy => by
        obtain ⟨c, hc⟩ := hw.2 y hy
        exact ⟨c, by simpa [Subtype.ext_iff] using hc.symm⟩
  obtain ⟨hw_ne_zero, hw_fixed, hw_span⟩ := hw
  have h2 : (2 : F9) ≠ 0 := fun h =>
    one_ne_zero (α := F9) (by linear_combination three_eq_zero - h)
  have hLy : ∀ y, L y = toLinearEquiv g y := fun y => (DFunLike.congr_fun hL.1 y).symm
  have hTT : ∀ x, L (L x) = x := fun x => DFunLike.congr_fun hL.2.1 x
  have hfix : ∀ y, L (-(y + L y)) = -(y + L y) := fun y => by
    rw [map_neg, map_add, hTT]
    abel
  have hanti : ∀ y, L (L y - y) = -(L y - y) := fun y => by
    rw [map_sub, hTT]
    abel
  have hsum : ∀ y : Fin 3 → F9, (-(y + L y)) + (L y - y) = y := fun y => by
    rw [show (-(y + L y)) + (L y - y) = (-(2 : F9)) • y by module,
      show (-(2 : F9)) = (1 : F9) by linear_combination -three_eq_zero, one_smul]
  have horth : ∀ y, L y = -y → hermForm conj9 y w = 0 := by
    intro y hy
    have hu := toLinearEquiv_hermForm g y w
    rw [← hLy, ← hLy, hy, hw_fixed,
      show (-y : Fin 3 → F9) = (-1 : F9) • y by module, hermForm_smul_left] at hu
    exact (mul_eq_zero.mp (by linear_combination -hu)).resolve_left h2
  have hw_aniso : hermForm conj9 w w ≠ 0 := by
    intro hw_iso
    refine hw_ne_zero <| hermForm_right_nondegen w fun x => ?_
    obtain ⟨c, hc⟩ := hw_span _ (hfix x)
    have hymw := horth _ (hanti x)
    rw [← hsum x, hermForm_add_left, hc, hermForm_smul_left, hw_iso, mul_zero, hymw,
      add_zero]
  refine ⟨w, hw_aniso, ?_⟩
  have key : ∀ y, hermForm conj9 y w = 0 → L y = -y := by
    intro y hy
    obtain ⟨c, hc⟩ := hw_span _ (hfix y)
    have hymw := horth _ (hanti y)
    have hypw : hermForm conj9 (-(y + L y)) w = 0 := by
      rw [← hsum y, hermForm_add_left, hymw, add_zero] at hy
      exact hy
    rw [hc, hermForm_smul_left] at hypw
    have hc0 := (mul_eq_zero.mp hypw).resolve_right hw_aniso
    rw [hc0, zero_smul] at hc
    exact eq_neg_of_add_eq_zero_right <| neg_eq_zero.mp hc
  refine Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun x => ?_
  change toLinearEquiv g x = reflEquiv w hw_aniso x
  rw [reflEquiv_apply, reflMap_apply, ← hLy]
  set c : F9 := hermForm conj9 x w * (hermForm conj9 w w)⁻¹ with hcdef
  have hx'w : hermForm conj9 (x - c • w) w = 0 := by
    rw [sub_eq_add_neg, hermForm_add_left,
      show (-(c • w)) = (-c) • w by module, hermForm_smul_left, hcdef]
    field_simp
    ring
  have hgx' : L (x - c • w) = -(x - c • w) := key _ hx'w
  have hsplit : L x = c • w - (x - c • w) := by
    rw [← show c • w + (x - c • w) = x by abel, map_add, map_smul, hw_fixed, hgx']
    abel
  rw [hsplit,
    show c • w - (x - c • w) = -x - c • w + (3 : F9) • (c • w) by module,
    show (3 : F9) • (c • w) = (0 : Fin 3 → F9) by
      rw [smul_smul, three_eq_zero, zero_mul, zero_smul],
    add_zero]

/-- The reflection map is injective on anisotropic points. -/
lemma anisoToInvol_injective : Function.Injective anisoToInvol := by
  intro p q h_eq
  have h_reflMap : reflMap q.1.rep p.1.rep = p.1.rep := by
    conv_rhs => rw [← reflMap_self p.1.rep (aniso_rep p)]
    exact congr_arg (fun f => toLinearEquiv f p.1.rep) (congr_arg Subtype.val h_eq) |>.symm
  obtain ⟨c, hc⟩ := reflMap_eq_self_iff _ _ (aniso_rep q) |>.1 h_reflMap
  have hc_nonzero : c ≠ 0 := fun hc_zero =>
    p.1.rep_nonzero <| by simpa [hc_zero] using hc
  apply Subtype.ext
  rw [← Projectivization.mk_rep p.1, ← Projectivization.mk_rep q.1,
    Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 c hc_nonzero, by simpa [Units.smul_def] using hc.symm⟩

/-- The reflection map is surjective onto order-two elements. -/
lemma anisoToInvol_surjective : Function.Surjective anisoToInvol := by
  intro g
  obtain ⟨w, hn, hg⟩ :
      ∃ w : Fin 3 → F9, ∃ hn : hermForm conj9 w w ≠ 0, g.val = reflSU w hn :=
    involution_eq_reflSU _ g.2
  obtain ⟨hw, pt⟩ :
      ∃ hw : w ≠ 0, ∃ pt : Projectivization F9 (Fin 3 → F9),
        pt = Projectivization.mk F9 w hw ∧ ¬ IsotropicProj conj9 pt := by
    exact ⟨fun h => hn (by simp +decide [h]), _, rfl, by
      simpa [isotropicProj_mk_iff] using hn⟩
  obtain ⟨pt, hpt⟩ := pt
  use ⟨pt, hpt.right⟩
  obtain ⟨a, ha⟩ : ∃ a : F9ˣ, pt.rep = a • w := by
    have := Projectivization.mk_rep pt
    rw [hpt.1, Projectivization.mk_eq_mk_iff] at this
    exact ⟨this.choose, hpt.1 ▸ this.choose_spec.symm⟩
  apply Subtype.ext
  simp [anisoToInvol, ha]
  convert reflSU_smul w a.val a.ne_zero _ _ using 1
  aesop (simp_config := { singlePass := true })

/-- **The bijection between anisotropic points and order-two elements of
`SU(3,3)`.** -/
noncomputable def anisoInvolEquiv :
    AnisotropicPoint ≃ {g : specialUnitaryGroup // orderOf g = 2} :=
  Equiv.ofBijective anisoToInvol ⟨anisoToInvol_injective, anisoToInvol_surjective⟩

/-- **There are exactly `63` elements of order `2` in `SU(3,3)`.** -/
theorem card_orderOf_eq_two_su :
    (Finset.univ.filter fun g : specialUnitaryGroup => orderOf g = 2).card = 63 := by
  simpa only [Fintype.card_subtype] using
    (Fintype.card_congr anisoInvolEquiv.symm).trans card_anisotropicPoint

end InvolutionOrderFourCount

end PSU33

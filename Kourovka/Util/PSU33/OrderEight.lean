/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.RootGeneration
import Kourovka.Util.PSU33.Cardinality
import Kourovka.Util.PSU33.PointStabilizer
import Kourovka.Util.PSU33.Involutions
import Mathlib.Algebra.CharP.Pi
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime

/-!
# Order-eight count for `PSU(3,3)`

Fixed-point geometry and double counting for order-eight elements in the
geometric `SU(3,3)` model.
-/

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

section OrderEightCount

/-- The (finite) set of isotropic points fixed by `g`. -/
noncomputable def fixedPts (g : specialUnitaryGroup) : Finset IsotropicPoint :=
  univ.filter (fun p : IsotropicPoint => g • p = p)

/-! ## Eigenvector helpers -/

/-- The chosen representative of an isotropic point is nonzero. -/
lemma rep_ne (p : IsotropicPoint) : p.1.rep ≠ 0 := p.1.rep_nonzero

/-- The chosen representative of an isotropic point is isotropic. -/
lemma rep_iso (p : IsotropicPoint) : hermForm conj9 p.1.rep p.1.rep = 0 := p.2

/-- `mkIso` of the representative recovers the point. -/
lemma mkIso_rep (p : IsotropicPoint) :
    mkIso p.1.rep (rep_ne p) (rep_iso p) = p :=
  Subtype.ext (Projectivization.mk_rep p.1)

/-- A fixed isotropic point yields an eigenvector of `toLinearEquiv g`: its representative
is scaled by a nonzero eigenvalue. -/
lemma eigen_of_fixed (g : specialUnitaryGroup) (p : IsotropicPoint)
    (hgp : g • p = p) :
    ∃ μ : F9, μ ≠ 0 ∧ toLinearEquiv g p.1.rep = μ • p.1.rep :=
  su_stab_point_scales g p.1.rep (rep_ne p) (rep_iso p) (by
    rw [mkIso_rep]
    exact hgp)

/-- Distinct isotropic points have non-perpendicular representatives (Witt index
one: there is no totally isotropic plane). -/
lemma reps_not_perp (p q : IsotropicPoint) (hpq : p ≠ q) :
    hermForm conj9 p.1.rep q.1.rep ≠ 0 := by
  intro hperp
  obtain ⟨c, hc⟩ := exists_smul_of_isotropic_perp p.1.rep q.1.rep (rep_ne p)
    (rep_iso p) (rep_iso q) hperp
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hc
    exact rep_ne q hc
  refine hpq (Subtype.ext ?_)
  conv_lhs => rw [← Projectivization.mk_rep p.1]
  conv_rhs => rw [← Projectivization.mk_rep q.1]
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨(Units.mk0 c hc0)⁻¹, ?_⟩
  rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, hc, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]

/-! ## The key geometric lemma: an order-eight element fixes exactly two points -/

/-- **At most two fixed isotropic points.** An order-eight element cannot fix three
distinct isotropic points: if it did, an eigenvalue computation would force
`g ^ 4 = 1`, contradicting `orderOf g = 8`. -/
theorem orderEight_atMostTwo_fixed
    (g : specialUnitaryGroup) (hg : orderOf g = 8)
    {p q r : IsotropicPoint} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : g • p = p) (hq : g • q = q) (hr : g • r = r) : False := by
  obtain ⟨α, hα⟩ := eigen_of_fixed g p hp
  obtain ⟨β, hβ⟩ := eigen_of_fixed g q hq
  obtain ⟨γ, hγ⟩ := eigen_of_fixed g r hr
  have hg4_order : orderOf (g ^ 4) = 2 := by rw [orderOf_pow'] <;> norm_num [hg]
  obtain ⟨z, hn, hz⟩ := involution_eq_reflSU (g ^ 4) hg4_order
  have hu_fixed : toLinearEquiv (g ^ 4) p.1.rep = p.1.rep := by
    have hu_fixed : α ^ 4 = 1 := by
      have hαβ : α * β ^ 3 = 1 := by
        have hαβ :
            hermForm conj9 (toLinearEquiv g p.1.rep) (toLinearEquiv g q.1.rep) =
            hermForm conj9 p.1.rep q.1.rep :=
          toLinearEquiv_hermForm g _ _
        simp_all +decide [conj9_apply]
        exact mul_left_cancel₀
          (show hermForm conj9 p.1.rep q.1.rep ≠ 0 from reps_not_perp p q hpq)
          (by linear_combination' hαβ)
      have hαγ : α * γ ^ 3 = 1 := by
        have hαγ :
            α * γ ^ 3 * hermForm conj9 p.1.rep r.1.rep =
            hermForm conj9 p.1.rep r.1.rep := by
          have hαγ :
              hermForm conj9 (toLinearEquiv g p.1.rep) (toLinearEquiv g r.1.rep) =
              hermForm conj9 p.1.rep r.1.rep :=
            toLinearEquiv_hermForm g _ _
          convert hαγ using 1
          simp +decide [hα.2, hγ.2, conj9_apply]
          ring
        exact mul_left_cancel₀
          (show hermForm conj9 p.1.rep r.1.rep ≠ 0 from reps_not_perp p r hpr)
          (by linear_combination' hαγ)
      have hβγ : β * γ ^ 3 = 1 := by
        have hβγ :
            hermForm conj9 (toLinearEquiv g q.1.rep) (toLinearEquiv g r.1.rep) =
            hermForm conj9 q.1.rep r.1.rep :=
          toLinearEquiv_hermForm g _ _
        simp_all +decide [conj9_apply]
        exact mul_left_cancel₀
          (show hermForm conj9 q.1.rep r.1.rep ≠ 0 from reps_not_perp q r hqr)
          (by linear_combination' hβγ)
      grind
    have hu_fixed :
        toLinearEquiv (g ^ 4) p.1.rep = (toLinearEquiv g)^[4] p.1.rep := by
      simp +decide [pow_succ, toLinearEquiv_mul]
    simp_all +decide [Function.iterate_succ_apply', smul_smul]
    simp_all +decide [mul_assoc, pow_succ]
  obtain ⟨c, hc⟩ : ∃ c : F9, p.1.rep = c • z := by
    have := reflMap_eq_self_iff z p.1.rep hn
    aesop
  have := rep_iso p
  simp_all +decide
  exact absurd hc (rep_ne p)

/-- An eigenvector whose eigenvalue has order `8` (i.e. `c ^ 4 = -1`) is isotropic:
unitarity gives `c ^ 4 * ⟨v,v⟩ = ⟨v,v⟩`, and `c ^ 4 = -1` forces `2⟨v,v⟩ = 0`,
hence `⟨v,v⟩ = 0` since `2 ≠ 0` in `GF(9)`. -/
lemma eigenvector_isotropic (g : specialUnitaryGroup) (c : F9) (v : Fin 3 → F9)
    (hc4 : c ^ 4 = -1) (hev : toLinearEquiv g v = c • v) :
    hermForm conj9 v v = 0 := by
  have h := toLinearEquiv_hermForm g v v
  rw [hev, hermForm_smul_left, hermForm_smul_right, conj9_apply] at h
  -- h : c * (c ^ 3 * hermForm conj9 v v) = hermForm conj9 v v
  have htwo : (2 : F9) * hermForm conj9 v v = 0 := by
    linear_combination -h + hermForm conj9 v v * hc4
  have h2ne : (2 : F9) ≠ 0 := fun hh =>
    one_ne_zero (show (1 : F9) = 0 by linear_combination three_eq_zero - hh)
  exact (mul_eq_zero.mp htwo).resolve_left h2ne

/-- **One order-eight eigenvalue.** An order-eight element `g` has an eigenvector
with eigenvalue `c` of order `8` (`c ^ 4 = -1`). Reason: `g ^ 4` is an involution,
the Hermitian reflection in an anisotropic line; its `-1`-eigenspace `H = z^⊥` is a
`2`-dimensional plane and `(toLinearEquiv g) ^ 4 = -1` on `H`, so on `H` the map factors
through `∏_{c^4 = -1} (toLinearEquiv g - c)`, forcing one factor `toLinearEquiv g - c` (with
`c ^ 4 = -1`) to be non-injective. -/
lemma exists_orderEight_eigenvector (g : specialUnitaryGroup) (hg : orderOf g = 8) :
    ∃ (c : F9) (v : Fin 3 → F9), v ≠ 0 ∧ c ^ 4 = -1 ∧ toLinearEquiv g v = c • v := by
  obtain ⟨w, hn⟩ :
      ∃ w : Fin 3 → F9,
      ∃ hn : hermForm conj9 w w ≠ 0, (toLinearEquiv g) ^ 4 = reflEquiv w hn := by
    convert involution_eq_reflSU (g ^ 4) _
    · rw [← toLinearEquiv_injective_stab.eq_iff]
      aesop
    · rw [orderOf_pow'] <;> norm_num [hg]
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → F9, v ≠ 0 ∧ hermForm conj9 v w = 0 := by
    by_contra! h_contra
    have h_kernel :
        LinearMap.ker (show (Fin 3 → F9) →ₗ[F9] F9 from
          { toFun := fun v => hermForm conj9 v w
            map_add' := fun x y => by simp +decide
            map_smul' := by simp +decide }) = ⊥ := by
      exact LinearMap.ker_eq_bot'.mpr fun v hv =>
        Classical.not_not.1 fun hv' => h_contra v hv' hv
    generalize_proofs at *
    have := LinearMap.finrank_range_add_finrank_ker
      (show (Fin 3 → F9) →ₗ[F9] F9 from
        { toFun := fun v => hermForm conj9 v w
          map_add' := by assumption
          map_smul' := by assumption })
    simp_all +decide
    rw [h_kernel] at this
    simp_all +decide
    exact absurd this (ne_of_lt (lt_of_le_of_lt (Submodule.finrank_le _) (by norm_num)))
  have h_eigenvalue : (toLinearEquiv g)^[4] v = -v := by
    obtain ⟨hn, hn'⟩ := hn
    replace hn' := congr_arg (fun f => f v) hn'
    simp_all +decide [pow_succ, mul_assoc]
  obtain ⟨c1, c2, c3, c4, hc⟩ :
      ∃ c1 c2 c3 c4 : F9,
        c1 ^ 4 = -1 ∧ c2 ^ 4 = -1 ∧ c3 ^ 4 = -1 ∧ c4 ^ 4 = -1 ∧
        (Polynomial.X ^ 4 + 1 : Polynomial F9) =
          (Polynomial.X - Polynomial.C c1) * (Polynomial.X - Polynomial.C c2) *
          (Polynomial.X - Polynomial.C c3) * (Polynomial.X - Polynomial.C c4) := by
    have h_roots :
        ∃ c1 c2 c3 c4 : F9,
          c1 ^ 4 = -1 ∧ c2 ^ 4 = -1 ∧ c3 ^ 4 = -1 ∧ c4 ^ 4 = -1 ∧
          c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c4 ∧ c2 ≠ c3 ∧ c2 ≠ c4 ∧ c3 ≠ c4 := by
      have h_roots :
          Finset.card (Finset.filter (fun c : F9 => c ^ 4 = -1) Finset.univ) = 4 := by
        have h_roots :
            Finset.card (Finset.filter (fun c : F9 => c ^ 4 = -1) Finset.univ) =
            Finset.card (Finset.filter (fun c : F9ˣ => c ^ 4 = -1) Finset.univ) := by
          refine Finset.card_bij (fun x hx => Units.mk0 x ?_) ?_ ?_ ?_ <;>
            simp_all +decide [Units.ext_iff]
          rintro rfl
          simp_all +decide
        convert Fintype.card_subtype (fun c : F9ˣ => c ^ 4 = -1) using 1
        · rw [Fintype.card_subtype]
          convert h_roots using 1
        · exact Eq.symm units_pow_eq_negone
      obtain ⟨s, hs⟩ := Finset.card_eq_succ.mp h_roots
      obtain ⟨t, ht₁, ht₂, ht₃⟩ := hs
      obtain ⟨a, b, c, ha, hb, hc⟩ := Finset.card_eq_three.mp ht₃
      use s, a, b, c
      simp_all +decide [Finset.ext_iff]
      exact ⟨
        ht₂ s |>.1 (Or.inl rfl),
        ht₂ a |>.1 (Or.inr (Or.inl rfl)),
        ht₂ b |>.1 (Or.inr (Or.inr (Or.inl rfl))),
        ht₂ c |>.1 (Or.inr (Or.inr (Or.inr rfl)))⟩
    obtain ⟨c1, c2, c3, c4, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h_roots
    refine ⟨c1, c2, c3, c4, h1, h2, h3, h4, ?_⟩
    refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ?_ ?_ ?_
    exact {c1, c2, c3, c4}
    · refine lt_of_lt_of_le (Polynomial.degree_sub_lt ?_ ?_ ?_) ?_ <;>
        norm_num [
          Polynomial.degree_add_eq_left_of_degree_lt,
          Polynomial.degree_sub_eq_left_of_degree_lt, h1, h2, h3, h4]
      · exact ne_of_apply_ne (Polynomial.eval 0) (by simp +decide)
      · simp +decide [*]
    · simp_all +decide
  obtain ⟨i, hi⟩ :
      ∃ i ∈ [c1, c2, c3, c4],
        (toLinearEquiv g - i • 1 : Module.End F9 (Fin 3 → F9)).ker ≠ ⊥ := by
    simp_all +decide [Submodule.ne_bot_iff]
    contrapose! hv
    intro hv_nonzero
    have h_injective :
        Function.Injective (toLinearEquiv g - c1 • 1 : Module.End F9 (Fin 3 → F9)) ∧
        Function.Injective (toLinearEquiv g - c2 • 1 : Module.End F9 (Fin 3 → F9)) ∧
        Function.Injective (toLinearEquiv g - c3 • 1 : Module.End F9 (Fin 3 → F9)) ∧
        Function.Injective (toLinearEquiv g - c4 • 1 : Module.End F9 (Fin 3 → F9)) :=
      ⟨
        LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx =>
          hv.1 x <| by simpa [sub_eq_zero] using hx),
        LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx =>
          hv.2.1 x <| by simpa [sub_eq_zero] using hx),
        LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx =>
          hv.2.2.1 x <| by simpa [sub_eq_zero] using hx),
        LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx =>
          hv.2.2.2 x <| by simpa [sub_eq_zero] using hx)⟩
    have h_injective :
        Function.Injective (toLinearEquiv g - c1 • 1 : Module.End F9 (Fin 3 → F9)) ∧
        Function.Injective (toLinearEquiv g - c2 • 1 : Module.End F9 (Fin 3 → F9)) ∧
        Function.Injective (toLinearEquiv g - c3 • 1 : Module.End F9 (Fin 3 → F9)) ∧
        Function.Injective (toLinearEquiv g - c4 • 1 : Module.End F9 (Fin 3 → F9)) →
        Function.Injective
          (Polynomial.aeval (R := F9) (toLinearEquiv g : Module.End F9 (Fin 3 → F9))
            (Polynomial.X ^ 4 + 1)) := by
      simp +decide [
        hc.2.2.2.2, Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      exact fun h1 h2 h3 h4 => h1.comp (h2.comp (h3.comp h4))
    have := h_injective ‹_›
    exact absurd
      (this (show
        (Polynomial.aeval (R := F9) (toLinearEquiv g : Module.End F9 (Fin 3 → F9))
          (Polynomial.X ^ 4 + 1)) v =
        (Polynomial.aeval (R := F9) (toLinearEquiv g : Module.End F9 (Fin 3 → F9))
          (Polynomial.X ^ 4 + 1)) 0 by
          simp +decide [pow_succ, mul_assoc,
            ‹toLinearEquiv g
              (toLinearEquiv g (toLinearEquiv g (toLinearEquiv g v))) = -v›]))
      (by simp +decide [hv_nonzero])
  simp_all +decide [Submodule.ne_bot_iff]
  rcases hi with ⟨rfl | rfl | rfl | rfl, x, hx, hx'⟩ <;>
    [exact ⟨_, _, hx', hc.1, sub_eq_zero.mp hx⟩;
      exact ⟨_, _, hx', hc.2.1, sub_eq_zero.mp hx⟩;
      exact ⟨_, _, hx', hc.2.2.1, sub_eq_zero.mp hx⟩;
      exact ⟨_, _, hx', hc.2.2.2.1, sub_eq_zero.mp hx⟩]

/-- **The dual order-eight eigenvalue.** From an eigenvector `v` with eigenvalue
`c` of order `8`, unitarity produces a second eigenvector with the distinct
order-`8` eigenvalue `c ^ 5 = c⁻³`. Indeed `x ↦ ⟨x, v⟩` is a nonzero linear
functional with `⟨toLinearEquiv g x, v⟩ = c⁻³ ⟨x, v⟩`, so
`toLinearEquiv g - c ^ 5` is not surjective, hence (finite dimension) not
injective. -/
lemma exists_dual_eigenvector (g : specialUnitaryGroup) (c : F9) (v : Fin 3 → F9)
    (hv : v ≠ 0) (hc4 : c ^ 4 = -1) (hev : toLinearEquiv g v = c • v) :
    ∃ (c' : F9) (v' : Fin 3 → F9),
      v' ≠ 0 ∧ c' ^ 4 = -1 ∧ c' ≠ c ∧ toLinearEquiv g v' = c' • v' := by
  -- Take `c' := c ^ 5`.
  set c' : F9 := c ^ 5
  have hc'_ne_c : c' ≠ c := by grind +ring
  have hc'_pow : c' ^ 4 = -1 := by grind
  have hc'_order : c' ^ 8 = 1 := by grobner
  have hc'_inv : c'⁻¹ = c ^ 3 := by grind
  -- The Hermitian pairing with `v`, viewed as an `F9`-linear functional.
  set φ : (Fin 3 → F9) →ₗ[F9] F9 :=
    { toFun := fun x => hermForm conj9 x v
      map_add' := fun x y => hermForm_add_left x y v
      map_smul' := fun m x => hermForm_smul_left m x v }
  generalize_proofs at *
  -- The range of `T` lies in `ker φ`.
  have hT_le_ker :
      LinearMap.range (toLinearEquiv g - c' • 1 : Module.End F9 (Fin 3 → F9)) ≤
      LinearMap.ker φ := by
    have hT_le_ker : ∀ x : Fin 3 → F9, φ (toLinearEquiv g x) = c' * φ x := by
      intro x
      have hφ_step :
          hermForm conj9 (toLinearEquiv g x) v =
            hermForm conj9 x ((toLinearEquiv g).symm v) := by
        convert toLinearEquiv_hermForm g x ((toLinearEquiv g).symm v) using 1
        simp +decide
      generalize_proofs at *
      -- From `hev`, we get `(toLinearEquiv g).symm v = c⁻¹ • v`.
      have h_inv : (toLinearEquiv g).symm v = c⁻¹ • v := by
        have h_inv : (toLinearEquiv g).symm (c • v) = v := by
          rw [← hev, LinearEquiv.symm_apply_apply]
        generalize_proofs at *
        convert congr_arg (fun x => c⁻¹ • x) h_inv using 1
        simp +decide [smul_smul, show c ≠ 0 by
          rintro rfl
          simp +decide at hc4]
      generalize_proofs at *
      simp_all +decide [conj9_apply]
      convert hφ_step using 1
      rw [← hc'_inv, inv_inv]
      rfl
    rintro _ ⟨x, rfl⟩
    simp +decide [hT_le_ker]
  -- Since `φ ≠ 0`, `LinearMap.ker φ ≠ ⊤`, so `T` is not surjective.
  have hT_not_surjective :
      ¬ Function.Surjective (toLinearEquiv g - c' • 1 : Module.End F9 (Fin 3 → F9)) := by
    intro h_surjective
    have h_ker_top : LinearMap.ker φ = ⊤ := eq_top_iff.mpr fun x hx => by
      obtain ⟨y, rfl⟩ := h_surjective x
      exact hT_le_ker <| LinearMap.mem_range_self _ _
    exact hv (hermForm_right_nondegen v fun x => by
      simpa using LinearMap.mem_ker.mp (h_ker_top.ge Submodule.mem_top))
  -- Since `T` is not surjective, it is not injective, so there exists `v' ≠ 0` with `T v' = 0`.
  obtain ⟨v', hv'⟩ :
      ∃ v' : Fin 3 → F9,
        v' ≠ 0 ∧ (toLinearEquiv g - c' • 1 : Module.End F9 (Fin 3 → F9)) v' = 0 := by
    contrapose! hT_not_surjective
    exact LinearMap.surjective_of_injective
      (LinearMap.ker_eq_bot.mp <| eq_bot_iff.mpr fun x hx =>
        Classical.not_not.1 fun hx' => hT_not_surjective x hx' hx)
  exact ⟨c', v', hv'.1, hc'_pow, hc'_ne_c, by simpa [sub_eq_zero] using hv'.2⟩

/-- **At least two fixed isotropic points.** An order-eight element fixes at least
two distinct isotropic points: the two eigenlines whose eigenvalue has order `8`. -/
theorem orderEight_atLeastTwo_fixed
    (g : specialUnitaryGroup) (hg : orderOf g = 8) :
    2 ≤ (fixedPts g).card := by
  obtain ⟨c, v, hv, hc4, hev⟩ := exists_orderEight_eigenvector g hg
  obtain ⟨c', v', hv', hc4', hcc', hev'⟩ := exists_dual_eigenvector g c v hv hc4 hev
  -- the two eigenvectors are isotropic
  have hvi : hermForm conj9 v v = 0 := eigenvector_isotropic g c v hc4 hev
  have hvi' : hermForm conj9 v' v' = 0 := eigenvector_isotropic g c' v' hc4' hev'
  -- the two corresponding points
  set P : IsotropicPoint := mkIso v hv hvi with hP
  set P' : IsotropicPoint := mkIso v' hv' hvi' with hP'
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc4
  have hc0' : c' ≠ 0 := by
    rintro rfl
    simp at hc4'
  have hPfix : g • P = P := su_smul_mkIso_of_scale g v hv hvi c hc0 hev
  have hP'fix : g • P' = P' := su_smul_mkIso_of_scale g v' hv' hvi' c' hc0' hev'
  -- the two points are distinct
  have hPne : P ≠ P' := by
    intro hPP
    -- `P = P'` means `v, v'` are proportional, forcing `c = c'`
    have h1 : Projectivization.mk F9 v hv = Projectivization.mk F9 v' hv' :=
      congrArg Subtype.val hPP
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F9 v v' hv hv').mp h1
    -- ha : (a : F9) • v' = v
    rw [Units.smul_def] at ha
    have e2 : toLinearEquiv g v = c' • v := by
      conv_lhs => rw [← ha]
      rw [map_smul, hev', smul_smul, mul_comm, ← smul_smul, ha]
    have hcv : c • v = c' • v := by rw [← hev, e2]
    have hsub0 : (c - c') • v = 0 := by rw [sub_smul, hcv, sub_self]
    rcases smul_eq_zero.mp hsub0 with h | h
    · exact hcc' (sub_eq_zero.mp h).symm
    · exact hv h
  -- conclude card ≥ 2
  have hsub : ({P, P'} : Finset IsotropicPoint) ⊆ fixedPts g := by
    intro x hx
    simp only [fixedPts, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | rfl
    exacts [hPfix, hP'fix]
  rw [← Finset.card_pair hPne]
  exact Finset.card_le_card hsub

/-- **An order-eight element fixes exactly two isotropic points.** -/
theorem orderEight_fixes_two (g : specialUnitaryGroup) (hg : orderOf g = 8) :
    (fixedPts g).card = 2 := by
  refine le_antisymm ?_ (orderEight_atLeastTwo_fixed g hg)
  by_contra h
  push_neg at h
  obtain ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr⟩ :
      ∃ p q r, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        p ∈ fixedPts g ∧ q ∈ fixedPts g ∧ r ∈ fixedPts g := by
    obtain ⟨s, hs, hsub⟩ := Finset.exists_subset_card_eq (show 3 ≤ (fixedPts g).card by omega)
    obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hsub
    exact ⟨p, q, r, hpq, hpr, hqr, hs (by simp), hs (by simp), hs (by simp)⟩
  exact orderEight_atMostTwo_fixed g hg hpq hpr hqr
    (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hr).2

/-! ## The per-pair count: four order-eight elements per hyperbolic pair -/

/-- The order-eight elements fixing both points of an ordered pair. -/
noncomputable def orderEightPairFix (p q : IsotropicPoint) : Finset specialUnitaryGroup :=
  univ.filter (fun g => orderOf g = 8 ∧ g • p = p ∧ g • q = q)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Base count.** There are exactly `4` order-eight elements fixing the base
hyperbolic pair `(p0, p1)`. These are the four generators of the cyclic
rescaling torus `≅ GF(9)ˣ` (`card_fixingSubgroup_two_eq_eight`). -/
theorem card_orderEightPairFix_base : (orderEightPairFix p0 p1).card = 4 := by
  have h_cyclic :
      IsCyclic (fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)) := by
    have h_cyclic :
        ∃ g : specialUnitaryGroup,
          orderOf g = 8 ∧
          g ∈ fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint) := by
      obtain ⟨a, ha⟩ : ∃ a : F9ˣ, orderOf a = 8 := by
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F9ˣ)
        use g
        rw [orderOf_eq_card_of_forall_mem_zpowers hg]
        convert card_units_F9
      obtain ⟨g, hg⟩ := exists_su_frame_diag a
      refine ⟨g, ?_, ?_⟩
      · rw [show orderOf g = orderOf (toLinearEquiv g) from
          (orderOf_injective toLinearEquivHomStab toLinearEquiv_injective_stab g).symm]
        refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_
        · decide +revert
        · ext x
          obtain ⟨a, b, c, rfl⟩ := frame_coords x
          have := pow_orderOf_eq_one (‹F9ˣ› : F9ˣ)
          simp_all +decide [pow_succ, mul_assoc]
          simp_all +decide [← mul_assoc, Units.ext_iff]
          grind
        · intro p pp dp
          have := Nat.le_of_dvd (by decide) dp
          interval_cases p <;> norm_num at *
          intro h
          have := congr_arg (fun f => f fv0) h
          norm_num [hg, pow_succ] at this
          simp_all +decide [← smul_assoc, orderOf_eq_iff]
          have := ha.2 4 (by decide) (by decide)
          simp_all +decide [pow_succ, mul_assoc]
          exact this (Units.ext <| by
            simpa [← mul_assoc] using smul_left_injective _ fv0_ne <| by
              simpa [← mul_assoc] using
                ‹(a * (a * (a * a)) : F9) • fv0 = fv0›)
      · simp +decide [mem_fixingSubgroup_iff]
        exact ⟨
          su_smul_mkIso_of_scale g fv0 fv0_ne fv0_iso _ (by aesop) hg.1,
          su_smul_mkIso_of_scale g fv1 fv1_ne fv1_iso _ (by aesop) hg.2.1⟩
    obtain ⟨g, hg₁, hg₂⟩ := h_cyclic
    have h_card :
        Nat.card
          (fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)) = 8 := by
      convert card_fixingSubgroup_two_eq_eight using 1
    have h_cyclic :
        IsCyclic (fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)) := by
      have h_order :
          orderOf
            (⟨g, hg₂⟩ :
              fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)) = 8 := by
        rw [← hg₁, orderOf_eq_orderOf_iff]
        simp +decide [Subtype.ext_iff]
      exact isCyclic_of_orderOf_eq_card
        (⟨g, hg₂⟩ : fixingSubgroup specialUnitaryGroup {p0, p1}) (by aesop)
    exact h_cyclic
  have h_card :
      (Finset.univ.filter
        (fun h : fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint) =>
          orderOf h = 8)).card = 4 := by
    have h_card :
        Fintype.card
          (fixingSubgroup specialUnitaryGroup ({p0, p1} : Set IsotropicPoint)) = 8 := by
      convert card_fixingSubgroup_two_eq_eight using 1
      rw [Nat.card_eq_fintype_card]
    have := @IsCyclic.card_orderOf_eq_totient
      (fixingSubgroup specialUnitaryGroup {p0, p1}) _ _
    exact this (h_card.symm ▸ dvd_rfl)
  rw [← h_card, eq_comm]
  refine Finset.card_bij (fun h hh => h.val) ?_ ?_ ?_ <;> simp +decide [orderEightPairFix]
  · intro a ha ha' ha'' ha'''
    refine ⟨?_, ?_⟩
    · rw [orderOf_eq_iff] at * <;> aesop
    · simp_all +decide [mem_fixingSubgroup_iff]
  · simp +contextual [mem_fixingSubgroup_iff]

/-- **Equidistribution.** By two-transitivity, every ordered pair of distinct
isotropic points carries the same number `4` of order-eight elements fixing it. -/
theorem card_orderEightPairFix (p q : IsotropicPoint) (hpq : p ≠ q) :
    (orderEightPairFix p q).card = 4 := by
  rw [← card_orderEightPairFix_base]
  obtain ⟨h, hh0, hh1⟩ :=
    exists_specialUnitaryGroup_map_isotropic_pair p0 p1 p q p0_ne_p1 hpq
  have horder : ∀ x : specialUnitaryGroup, orderOf (h * x * h⁻¹) = orderOf x := fun x => by
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj h) x
  have hfix : ∀ (x : specialUnitaryGroup) (a b : IsotropicPoint),
      h • a = b → ((h * x * h⁻¹) • b = b ↔ x • a = a) := by
    intro x a b hab
    rw [← hab, SemigroupAction.mul_smul, SemigroupAction.mul_smul, inv_smul_smul]
    constructor
    · intro hxa
      have := congrArg (fun z => h⁻¹ • z) hxa
      simpa [inv_smul_smul] using this
    · intro hxa
      rw [hxa]
  have hmem : ∀ x : specialUnitaryGroup,
      x ∈ orderEightPairFix p0 p1 ↔ h * x * h⁻¹ ∈ orderEightPairFix p q := by
    intro x
    simp only [orderEightPairFix, mem_filter, mem_univ, true_and, horder,
      hfix x p0 p hh0, hfix x p1 q hh1]
  refine (Finset.card_bij (fun x _ => h * x * h⁻¹) (fun x hx => (hmem x).mp hx)
    (fun a _ b _ hab => mul_left_cancel (mul_right_cancel hab)) (fun y hy => ?_)).symm
  refine ⟨h⁻¹ * y * h, (hmem _).mpr ?_, by group⟩
  have hyy : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
  rw [hyy]
  exact hy

/-! ## Assembly: double counting the incidences -/

/-- For an order-eight element `g`, the set of ordered pairs of distinct isotropic
points both fixed by `g` is the off-diagonal of its (two-element) fixed set, of
cardinality `2`. -/
theorem card_pairs_fixed_of_orderEight (g : specialUnitaryGroup) (hg : orderOf g = 8) :
    (univ.filter (fun pq : IsotropicPoint × IsotropicPoint =>
      pq.1 ≠ pq.2 ∧ g • pq.1 = pq.1 ∧ g • pq.2 = pq.2)).card = 2 := by
  have hset : (univ.filter (fun pq : IsotropicPoint × IsotropicPoint =>
      pq.1 ≠ pq.2 ∧ g • pq.1 = pq.1 ∧ g • pq.2 = pq.2)) = (fixedPts g).offDiag := by
    ext pq
    simp only [mem_filter, mem_univ, true_and, Finset.mem_offDiag, fixedPts]
    tauto
  rw [hset, Finset.offDiag_card, orderEight_fixes_two g hg]

/-- **The order-eight entry of the element-order histogram of `SU(3,3)` is `1512`.**

The proof double-counts the incidence triples `(g, p, q)` with `orderOf g = 8`,
`p ≠ q`, and `g` fixing both `p` and `q`. Summing over `g` first gives `2` per
order-eight element (`card_pairs_fixed_of_orderEight`); summing over the pair
`(p, q)` first gives `4` per ordered distinct pair (`card_orderEightPairFix`),
and there are `756 = 28 · 27` such pairs (`card_isotropicPoint`). -/
theorem card_orderOf_eq_eight_su :
    (Finset.univ.filter
      (fun g : specialUnitaryGroup => orderOf g = 8)).card = 1512 := by
  suffices h_suff :
      2 * (Finset.univ.filter (fun g : specialUnitaryGroup => orderOf g = 8)).card =
        3024 by
    grind
  have h_card_eq :
      (Finset.univ.filter (fun g : specialUnitaryGroup => orderOf g = 8)).card * 2 =
        (Finset.univ.filter
          (fun pq : IsotropicPoint × IsotropicPoint => pq.1 ≠ pq.2)).card * 4 := by
    have h_double_count :
        (Finset.univ.filter (fun g : specialUnitaryGroup => orderOf g = 8)).sum
          (fun g => (Finset.univ.filter
            (fun pq : IsotropicPoint × IsotropicPoint =>
              pq.1 ≠ pq.2 ∧ g • pq.1 = pq.1 ∧ g • pq.2 = pq.2)).card) =
        (Finset.univ.filter
          (fun pq : IsotropicPoint × IsotropicPoint => pq.1 ≠ pq.2)).sum
          (fun pq => (Finset.univ.filter
            (fun g : specialUnitaryGroup =>
              orderOf g = 8 ∧ g • pq.1 = pq.1 ∧ g • pq.2 = pq.2)).card) := by
      simp +decide only [card_filter]
      rw [Finset.sum_comm, Finset.sum_filter]
      exact Finset.sum_congr rfl fun x hx => by
        split_ifs <;> simp +decide [*, Finset.filter_filter]
    convert h_double_count using 1
    · rw [Finset.sum_const_nat]
      intro g hg
      convert card_pairs_fixed_of_orderEight g (Finset.mem_filter.mp hg |>.2) using 1
    · rw [Finset.sum_const_nat]
      simp +zetaDelta at *
      exact fun p q hpq => PSU33.card_orderEightPairFix p q hpq
  rw [mul_comm, h_card_eq, show
    (Finset.univ.filter fun pq : IsotropicPoint × IsotropicPoint => ¬ pq.1 = pq.2) =
      Finset.offDiag Finset.univ by
        ext
        aesop]
  simp +decide [Finset.card_univ, card_isotropicPoint]

end OrderEightCount

end PSU33

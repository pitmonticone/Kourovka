/-
Copyright (c) 2026 Aristotle (Harmonic). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.ProjectiveAction
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Tactic.LinearCombination'

/-!
# Generation of `SU(3,3)` by its Hermitian transvections

This file proves the structural Iwasawa input

`PSU33.rootGenerated_eq_top :
   rootGenerated = (⊤ : Subgroup specialUnitaryGroup)`,

i.e. that the skew Eichler/Siegel transvections generate the whole special
unitary group `SU(3,3)` of the Hermitian polarity over `GF(9)`.

The proof is purely geometric, with no finite group enumeration and no word,
class, or order tables.  The strategy is the *simply transitive frame torsor*:

* **Freeness** (`su_fixing_hyperbolic_pair_eq_one`): a special unitary element
  fixing the two vectors of a hyperbolic pair is the identity (the determinant
  forces the action on the anisotropic complement to be trivial).

* **Transitivity** (`rootGenerated_hyp_pair_transitive`): the root-generated
  subgroup acts transitively on hyperbolic vector pairs, decomposed into
  transitivity on isotropic vectors and transitivity of the vector stabilizer on
  the hyperbolic partners.

Combining the two: `SU(3,3)` acts freely and transitively on hyperbolic pairs,
and the root subgroup already acts transitively, so it is everything.
-/

namespace PSU33

open PSU33.HermitianForm
open scoped Pointwise
open MulAction

/-! ## Transitivity of the root subgroup on hyperbolic pairs -/

/-- A skew Eichler transvection lies in the root-generated subgroup. -/
lemma transvection_mem (u : Fin 3 → F9) (hu : hermForm conj9 u u = 0)
    (a : F9) (ha : a + a ^ 3 = 0) : transvection u hu a ha ∈ rootGenerated :=
  Subgroup.subset_closure ⟨u, hu, a, by
    rw [conj9_apply]
    exact ha, rfl⟩

/-- **One-transvection move.**  If `u` and `target` are isotropic and the form
value `γ = h u target` is a nonzero skew (trace-zero) element, then the single
skew transvection along `target - u` maps `u` to `target`. -/
lemma rootGenerated_transvection_move
    (u target : Fin 3 → F9)
    (hu : hermForm conj9 u u = 0) (htarget : hermForm conj9 target target = 0)
    (hγ : hermForm conj9 u target ≠ 0)
    (hskew : hermForm conj9 u target + (hermForm conj9 u target) ^ 3 = 0) :
    ∃ h ∈ rootGenerated, toLinearEquiv h u = target := by
  -- Set w := target - u and a := γ⁻¹.
  set w : Fin 3 → F9 := target - u
  set a : F9 := (hermForm conj9 u target)⁻¹
  -- Show that w is isotropic.
  have hw : hermForm conj9 w w = 0 := by
    have hw_iso :
        hermForm conj9 w w =
          hermForm conj9 target target - hermForm conj9 target u -
          hermForm conj9 u target + hermForm conj9 u u := by
      simp +decide [w, hermForm_apply, Fin.sum_univ_three]
      ring_nf
    have h_conj : hermForm conj9 target u = conj9 (hermForm conj9 u target) :=
      PSU33.HermitianForm.hermForm_conj_symm conj9_involutive u target ▸ rfl
    rw [hw_iso, htarget, h_conj, hu]
    ring_nf
    rw [show conj9 (hermForm conj9 u target) = (hermForm conj9 u target) ^ 3 by
      rw [conj9_apply]]
    linear_combination' -hskew
  -- Show that a satisfies the condition a + a ^ 3 = 0.
  have ha : a + a ^ 3 = 0 := by grind +qlia
  refine ⟨transvection w hw a ha, transvection_mem _ _ _ _, ?_⟩
  convert eichlerTransvection_apply w hw a u using 1
  simp +zetaDelta at *
  simp_all +decide [hermForm_apply]

/-- There is a nonzero *skew* (trace-zero) element of `GF(9)`: a square root of
`-1`.  Skew elements are exactly the valid transvection parameters. -/
lemma exists_skew_unit : ∃ t : F9, t ≠ 0 ∧ t + t ^ 3 = 0 := by
  obtain ⟨s, hs4, hs0⟩ := exists_fourth_root (-1) (Or.inr rfl)
  exact ⟨s ^ 2, pow_ne_zero 2 hs0, by linear_combination (s ^ 2) * hs4⟩

/-- A nonzero isotropic vector cannot be orthogonal to both members of a
hyperbolic pair `(u, p)` completed to a frame by a unit `w`: its orthogonal
complement is the anisotropic line `⟨w⟩`, which has no nonzero isotropic vector. -/
lemma isotropic_not_perp_pair (u p w u' : Fin 3 → F9)
    (hup : hermForm conj9 u p = 1) (hpu : hermForm conj9 p u = 1)
    (huu : hermForm conj9 u u = 0) (hpp : hermForm conj9 p p = 0)
    (hww : hermForm conj9 w w = 1)
    (huw : hermForm conj9 u w = 0) (hwu : hermForm conj9 w u = 0)
    (hpw : hermForm conj9 p w = 0) (hwp : hermForm conj9 w p = 0)
    (hindep : LinearIndependent F9 ![u, p, w])
    (hu'0 : u' ≠ 0) (hu'iso : hermForm conj9 u' u' = 0) :
    hermForm conj9 u u' ≠ 0 ∨ hermForm conj9 p u' ≠ 0 := by
  have h_basis : Submodule.span F9 (Set.range ![u, p, w]) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card] <;> aesop
  generalize_proofs at *
  -- Write `u'` as a linear combination of `u`, `p`, and `w`.
  obtain ⟨a, b, c, hu'⟩ : ∃ a b c : F9, u' = a • u + b • p + c • w := by
    have := h_basis.ge (Submodule.mem_top : u' ∈ ⊤)
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨f, hf⟩ := this
    use f 0, f 1, f 2
    simp_all +decide [Fin.sum_univ_three]
  generalize_proofs at *
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp_all +decide [hermForm_add_right]

/-- **Torus generator as a product of skew transvections.**  In a frame
`(v0, v1, w)` (hyperbolic pair plus a unit `w`), an explicit product of three
skew Eichler transvections scales `v0` by the field generator `1 + t`
(`t` a nonzero skew element, so `t² = -1`).  Since `1 + t` generates `F9ˣ`
(its order is `8`), this realises the whole rescaling torus inside the
root-generated subgroup. -/
lemma rootGenerated_scale_gen
    (v0 v1 w : Fin 3 → F9) (t : F9) (ht0 : t ≠ 0) (hts : t + t ^ 3 = 0)
    (h00 : hermForm conj9 v0 v0 = 0) (h11 : hermForm conj9 v1 v1 = 0)
    (hww : hermForm conj9 w w = 1)
    (h01 : hermForm conj9 v0 v1 = 1) (h10 : hermForm conj9 v1 v0 = 1)
    (h0w : hermForm conj9 v0 w = 0) (hw0 : hermForm conj9 w v0 = 0)
    (h1w : hermForm conj9 v1 w = 0) (hw1 : hermForm conj9 w v1 = 0) :
    ∃ h ∈ rootGenerated, toLinearEquiv h v0 = (1 + t) • v0 := by
  use transvection (t • v0 + (-t) • v1 + (-1 + t) • w) (by
    simp +decide only [hermForm_add_right, hermForm_smul_right, hermForm_add_left,
      hermForm_smul_left]
    simp_all +decide [conj9_apply]
    grind) t hts *
    transvection (t • v0 + (-t) • v1 + (1 + t) • w) (by
      simp +decide only [hermForm_add_right, hermForm_smul_right, hermForm_add_left,
        hermForm_smul_left]
      simp_all +decide [conj9_apply]
      grind +ring) t hts *
    transvection (t • v1) (by simp_all +decide) t hts
  generalize_proofs at *
  refine ⟨Subgroup.mul_mem _
      (Subgroup.mul_mem _ (transvection_mem _ _ _ _) (transvection_mem _ _ _ _))
      (transvection_mem _ _ _ _), ?_⟩
  simp +decide only [toLinearEquiv_mul_apply, toLinearEquiv_transvection,
    eichlerTransvection_apply, map_add]
  simp +decide only [hermForm_smul_right, h00, map_neg, h01,
    map_add, map_one, h0w, hermForm_smul_left, h10, h11, h1w]
  rw [show conj9 t = -t by
    rw [conj9_apply]
    linear_combination hts]
  ring_nf
  ext i
  norm_num
  ring_nf
  grobner

/-- **Rescaling torus inside the root-generated subgroup.**  For any nonzero
isotropic vector `w0` and any nonzero scalar `c`, there is a root-generated
element scaling `w0` by `c`. -/
lemma rootGenerated_torus (w0 : Fin 3 → F9) (hw0 : w0 ≠ 0)
    (hiso : hermForm conj9 w0 w0 = 0) (c : F9) (hc : c ≠ 0) :
    ∃ k ∈ rootGenerated, toLinearEquiv k w0 = c • w0 := by
  obtain ⟨p, hp⟩ := exists_isotropic_partner w0 hw0 hiso
  obtain ⟨w, hw⟩ := exists_orthogonal_unit w0 p hw0 hiso hp.1 hp.2.1 hp.2.2
  obtain ⟨t, ht⟩ := exists_skew_unit
  obtain ⟨K0, hK0⟩ := rootGenerated_scale_gen w0 p w t ht.1 ht.2
    hiso hp.1 hw.2.2.2.2.1 hp.2.1 hp.2.2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 + t) ^ n = c := by
    have h_order : orderOf (Units.mk0 (1 + t) (by grind +qlia)) = 8 := by
      have h_order : (1 + t) ^ 8 = 1 ∧ (1 + t) ^ 4 ≠ 1 := by
        grind
      refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_ <;> simp_all +decide [pow_succ]
      · exact Units.ext h_order.1
      · intro p pp dp
        have := Nat.le_of_dvd (by decide) dp
        interval_cases p <;> simp_all +decide
        simp_all +decide [Units.ext_iff, pow_succ]
    generalize_proofs at *
    have h_gen : ∀ x : F9ˣ, ∃ n : ℕ, (Units.mk0 (1 + t) ‹_›) ^ n = x := by
      have h_gen : Subgroup.zpowers (Units.mk0 (1 + t) ‹_›) = ⊤ := by
        refine Subgroup.eq_top_of_card_eq _ ?_
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_zpowers,
          h_order]
        convert card_units_F9.symm
        rw [Nat.card_eq_fintype_card]
      intro x
      replace h_gen := SetLike.ext_iff.mp h_gen x
      simp_all +decide [Subgroup.mem_zpowers_iff]
      obtain ⟨k, rfl⟩ := h_gen
      use Int.toNat (k % orderOf (Units.mk0 (1 + t) ‹_›))
      simp +decide [← zpow_natCast,
        Int.toNat_of_nonneg (Int.emod_nonneg _ <|
          Nat.cast_ne_zero.mpr <| ne_of_gt <| orderOf_pos _),
        zpow_mod_orderOf]
    obtain ⟨n, hn⟩ := h_gen (Units.mk0 c hc)
    use n
    simpa [Units.ext_iff] using hn
  have h_ind : ∀ n : ℕ, (toLinearEquiv (K0 ^ n)) w0 = (1 + t) ^ n • w0 := by
    intro n
    induction n <;> simp_all +decide [pow_succ']
    convert congr_arg (fun x => toLinearEquiv K0 x) ‹(toLinearEquiv (K0 ^ _)) w0 = _› using 1
    rw [LinearEquiv.map_smul, hK0.2, smul_smul, mul_comm]
  exact ⟨K0 ^ n, Subgroup.pow_mem _ hK0.1 _, by rw [h_ind, hn]⟩

set_option maxHeartbeats 1000000 in
/-- **Transitivity on isotropic vectors.**  The root-generated subgroup maps any
nonzero isotropic vector to any other.

Mapping `u` to a scalar multiple `c • u` requires a *torus* element of
`SU(3,3)` realised as a product of skew transvections (the `2`-part of the group,
`q² - 1 = 8`); this supplies the scalar part of the transitivity argument beyond
the skew transvection moves of `rootGenerated_transvection_move`. -/
lemma rootGenerated_transitive_isotropic
    (u u' : Fin 3 → F9) (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hui : hermForm conj9 u u = 0) (hui' : hermForm conj9 u' u' = 0) :
    ∃ h ∈ rootGenerated, toLinearEquiv h u = u' := by
  obtain ⟨p, hpp, hup, hpu⟩ := exists_isotropic_partner u hu hui
  obtain ⟨w, hv0w, hwv0, hv1w, hwv1, hww, hindep⟩ :=
    exists_orthogonal_unit u p hu hui hpp hup hpu
  have := isotropic_not_perp_pair u p w u' hup hpu hui hpp hww hv0w hwv0
    hv1w hwv1 hindep hu' hui'
  obtain ⟨t, ht0, hts⟩ : ∃ t : F9, t ≠ 0 ∧ t + t ^ 3 = 0 := exists_skew_unit
  set s := if hermForm conj9 p u' = 0 then 1 else 0
  set x := (-t) • p + s • u
  have hx_iso : hermForm conj9 x x = 0 := by
    have hx_iso :
        hermForm conj9 x x =
          (-t) * conj9 (-t) * hermForm conj9 p p +
          s * conj9 s * hermForm conj9 u u +
          (-t) * conj9 s * hermForm conj9 p u +
          s * conj9 (-t) * hermForm conj9 u p := by
      unfold x
      simp +decide
      ring_nf
      simp only [hermForm_apply]
      simp +decide [Fin.sum_univ_three]
      ring_nf
    generalize_proofs at *
    simp_all +decide [conj9_apply]
    grind
  have hx_u : hermForm conj9 u x = t := by
    simp +zetaDelta at *
    split_ifs <;> simp_all +decide
    · have h_conj : conj9 (-t) = t := by
        rw [conj9_apply]
        grind
      have h_conj : hermForm conj9 u (-(t • p)) = -conj9 t * hermForm conj9 u p := by
        rw [map_neg, hermForm_smul_right]
        ring!
      generalize_proofs at *
      aesop
    · have h_conj : conj9 t = -t := by
        rw [conj9_apply]
        linear_combination' hts
      generalize_proofs at *
      simp only [hermForm_apply] at *
      simp_all +decide [Fin.sum_univ_three]
  have hx_u'_ne_zero : hermForm conj9 x u' ≠ 0 := by
    simp +zetaDelta at *
    split_ifs at * <;> simp_all +decide
  generalize_proofs at *
  obtain ⟨h1, hh1, hh1u⟩ : ∃ h1 ∈ rootGenerated, toLinearEquiv h1 u = x :=
    rootGenerated_transvection_move u x hui hx_iso (hx_u.symm ▸ ht0) (by rw [hx_u, hts])
  generalize_proofs at *
  obtain ⟨h2, hh2, hh2x⟩ :
      ∃ h2 ∈ rootGenerated,
        toLinearEquiv h2 x = (conj9 t * (conj9 (hermForm conj9 x u'))⁻¹) • u' := by
    apply rootGenerated_transvection_move x
      ((conj9 t * (conj9 (hermForm conj9 x u'))⁻¹) • u') hx_iso (by
        simp +decide [hui']) (by
        simp_all +decide) (by
        simp +decide
        rw [show conj9 (conj9 t) = t from ?_,
          show conj9 (conj9 (hermForm conj9 x u')) = hermForm conj9 x u' from ?_]
        · grind
        · exact conj9_involutive _
        · exact conj9_involutive t)
  generalize_proofs at *
  obtain ⟨k, hk, hku'⟩ :
      ∃ k ∈ rootGenerated,
        toLinearEquiv k u' = (conj9 t * (conj9 (hermForm conj9 x u'))⁻¹)⁻¹ • u' := by
    apply rootGenerated_torus u' hu' hui'
      ((conj9 t * (conj9 (hermForm conj9 x u'))⁻¹)⁻¹)
      (inv_ne_zero (mul_ne_zero
        (by simp_all +decide [conj9_apply])
        (inv_ne_zero (by
          exact fun h => hx_u'_ne_zero <| by simpa [conj9_apply] using h))))
  generalize_proofs at *
  use k * h2 * h1
  simp_all +decide [mul_assoc, Subgroup.mul_mem]
  simp_all +decide [toLinearEquiv_mul_apply]
  simp +decide [← smul_assoc, mul_comm, mul_left_comm, ht0, hx_u'_ne_zero]

/-- **Explicit short-root (Heisenberg) element.**  In a Hermitian frame
`(v0, v1, w)` (hyperbolic pair `v0, v1` plus a unit `w` orthogonal to both), the
following product of four skew Eichler transvections fixes `v0` and sends `v1` to
`v0 + v1 + w`.  It is a genuine root-unipotent element of the unipotent radical
that is *not* itself a transvection; it is found by an explicit word over
`GF(9)`.  Here `t` is any nonzero skew element (so `t^2 = -1`). -/
lemma short_root_one
    (v0 v1 w : Fin 3 → F9) (t : F9) (ht0 : t ≠ 0) (hts : t + t ^ 3 = 0)
    (h00 : hermForm conj9 v0 v0 = 0) (h11 : hermForm conj9 v1 v1 = 0)
    (hww : hermForm conj9 w w = 1)
    (h01 : hermForm conj9 v0 v1 = 1) (h10 : hermForm conj9 v1 v0 = 1)
    (h0w : hermForm conj9 v0 w = 0) (hw0 : hermForm conj9 w v0 = 0)
    (h1w : hermForm conj9 v1 w = 0) (hw1 : hermForm conj9 w v1 = 0) :
    ∃ h ∈ rootGenerated, toLinearEquiv h v0 = v0 ∧ toLinearEquiv h v1 = v0 + v1 + w := by
  have ht2 : t ^ 2 = -1 := mul_left_cancel₀ ht0 (by linear_combination hts)
  have hct : conj9 t = -t := by
    rw [conj9_apply]
    linear_combination hts
  have h3 : (3 : F9) = 0 := three_eq_zero
  have hsk : (-t) + (-t) ^ 3 = 0 := by linear_combination -hts
  have hna :
      hermForm conj9 (v0 + (1 - t) • v1 + (-t) • w)
        (v0 + (1 - t) • v1 + (-t) • w) = 0 := by
    simp only [hermForm_add_left, hermForm_add_right, LinearMap.smul_apply, map_smul,
      map_smulₛₗ, smul_eq_mul,
      h00, h11, hww, h01, h10, h0w, hw0, h1w, hw1, map_sub, map_neg, map_one, hct,
      mul_zero, add_zero, zero_add, mul_one]
    first
      | linear_combination ht2 | linear_combination -ht2 | linear_combination h3
      | linear_combination ht2 + h3 | linear_combination -ht2 + h3
  have hnb :
      hermForm conj9 (v0 + (-1 + t) • v1 + (-1 + t) • w)
        (v0 + (-1 + t) • v1 + (-1 + t) • w) = 0 := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_smulₛₗ, smul_eq_mul,
      h00, h11, hww, h01, h10, h0w, hw0, h1w, hw1, map_add, map_neg, map_one, hct,
      mul_zero, add_zero, zero_add, mul_one]
    first
      | linear_combination ht2 | linear_combination -ht2
  have hnc :
      hermForm conj9 (v0 + (1 + t) • v1 + (-1 : F9) • w)
        (v0 + (1 + t) • v1 + (-1 : F9) • w) = 0 := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_smulₛₗ, smul_eq_mul,
      h00, h11, hww, h01, h10, h0w, hw0, h1w, hw1, map_add, map_neg, map_one, hct,
      mul_zero, add_zero, zero_add, mul_one]
    first
      | linear_combination ht2 | linear_combination -ht2 | linear_combination h3
  refine ⟨
    transvection v1 h11 (-t) hsk *
      transvection (v0 + (1 + t) • v1 + (-1 : F9) • w) hnc t hts *
      transvection (v0 + (-1 + t) • v1 + (-1 + t) • w) hnb (-t) hsk *
      transvection (v0 + (1 - t) • v1 + (-t) • w) hna (-t) hsk,
    ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (transvection_mem _ _ _ _) (transvection_mem _ _ _ _))
        (transvection_mem _ _ _ _))
      (transvection_mem _ _ _ _)
  · simp only [toLinearEquiv_mul_apply, toLinearEquiv_transvection, eichlerTransvection_apply,
      map_smul, map_smulₛₗ, smul_eq_mul,
      h00, h11, hww, h01, h10, h0w, hw0, h1w, hw1, map_add, map_sub, map_neg, map_one, hct,
      mul_zero, add_zero, zero_add, mul_one]
    match_scalars <;>
      first
      | linear_combination (-t ^ 4 + 2 * t ^ 3 - t ^ 2 + t) * ht2
      | linear_combination (-t ^ 4 + 2 * t ^ 3 + t ^ 2 - t - 4) * ht2 + h3
      | linear_combination (t ^ 4 - t ^ 3 - 2 * t ^ 2 + 5) * ht2 - 2 * h3
      | linear_combination (-t ^ 5 + t ^ 4 + 3 * t ^ 3 - 2 * t ^ 2 - 5 * t) * ht2 +
          2 * t * h3
      | linear_combination (-t ^ 5 + t ^ 4 + t ^ 3 - 2 * t ^ 2 + t) * ht2 - t * h3
      | linear_combination (t ^ 5 - 3 * t ^ 3 + 7 * t + 3) * ht2 + (-3 * t - 1) * h3
  · simp only [toLinearEquiv_mul_apply, toLinearEquiv_transvection, eichlerTransvection_apply,
      map_smul, map_smulₛₗ, smul_eq_mul,
      h00, h11, hww, h01, h10, h0w, hw0, h1w, hw1, map_add, map_sub, map_neg, map_one, hct,
      mul_zero, add_zero, zero_add, mul_one]
    match_scalars <;>
      first
      | linear_combination (-t ^ 4 + 2 * t ^ 3 - t ^ 2 + t) * ht2
      | linear_combination (-t ^ 4 + 2 * t ^ 3 + t ^ 2 - t - 4) * ht2 + h3
      | linear_combination (t ^ 4 - t ^ 3 - 2 * t ^ 2 + 5) * ht2 - 2 * h3

/-- **Explicit norm-`(-1)` short-root element.**  The analogue of `short_root_one`
when the anisotropic frame vector `w` has Hermitian norm `-1` instead of `1`.
It fixes `v0` and sends `v1 ↦ -v0 + v1 + w` (the `v0`-coefficient is `-1` here,
forced by the isotropy of the image), via an explicit product of four skew
Eichler transvections. -/
lemma short_root_negone
    (v0 v1 w : Fin 3 → F9) (t : F9) (ht0 : t ≠ 0) (hts : t + t ^ 3 = 0)
    (h00 : hermForm conj9 v0 v0 = 0) (h11 : hermForm conj9 v1 v1 = 0)
    (hww : hermForm conj9 w w = -1)
    (h01 : hermForm conj9 v0 v1 = 1) (h10 : hermForm conj9 v1 v0 = 1)
    (h0w : hermForm conj9 v0 w = 0) (hw0 : hermForm conj9 w v0 = 0)
    (h1w : hermForm conj9 v1 w = 0) (hw1 : hermForm conj9 w v1 = 0) :
    ∃ h ∈ rootGenerated, toLinearEquiv h v0 = v0 ∧ toLinearEquiv h v1 = -v0 + v1 + w := by
  revert t
  intro t ht ht3
  have ht2 : t ^ 2 = -1 := by
    exact mul_left_cancel₀ ht <| by linear_combination' ht3
  have hct : conj9 t = -t := by
    rw [conj9_apply]
    linear_combination' ht3
  have h3 : (3 : F9) = 0 := three_eq_zero
  have hsk : (-t) + (-t) ^ 3 = 0 := by
    linear_combination -ht3
  have hna : hermForm conj9 (t • v1) (t • v1) = 0 := by
    simp_all +decide
  have hnb :
      hermForm conj9 (t • v0 + t • v1 + (1 + t) • w)
        (t • v0 + t • v1 + (1 + t) • w) = 0 := by
    simp_all +decide [hermForm_add_right]
    grind
  have hnc :
      hermForm conj9 (t • v0 + (-t) • v1 + t • w)
        (t • v0 + (-t) • v1 + t • w) = 0 := by
    simp only [hermForm_apply] at *
    simp_all +decide [Fin.sum_univ_three]
    ring_nf
    grind
  have hnd :
      hermForm conj9 (t • v0 + (1 + t) • v1 + (-1 + t) • w)
        (t • v0 + (1 + t) • v1 + (-1 + t) • w) = 0 := by
    simp_all +decide [hermForm_add_right]
    grind +splitIndPred
  refine ⟨
    transvection (t • v0 + (1 + t) • v1 + (-1 + t) • w) hnd t ht3 *
      transvection (t • v0 + (-t) • v1 + t • w) hnc (-t) hsk *
      transvection (t • v0 + t • v1 + (1 + t) • w) hnb t ht3 *
      transvection (t • v1) hna t ht3, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (transvection_mem _ _ _ _) (transvection_mem _ _ _ _))
        (transvection_mem _ _ _ _))
      (transvection_mem _ _ _ _)
  · simp +decide only [toLinearEquiv_mul_apply, toLinearEquiv_transvection,
      eichlerTransvection_apply]
    simp +decide only [LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_smulₛₗ,
      smul_eq_mul, hct, h01, mul_one, h10, map_add, map_one, h0w, h1w,
      mul_zero, add_zero, hw0, map_neg, hw1, zero_add]
    simp +decide [h00, h11, hww]
    ext i
    norm_num
    ring_nf
    grind
  · simp +decide only [toLinearEquiv_mul_apply, toLinearEquiv_transvection,
      eichlerTransvection_apply]
    simp +decide only [LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_smulₛₗ,
      smul_eq_mul, hct, h11, mul_zero,
      h10, mul_one, add_zero, map_add,
      map_one, h1w, h00, zero_add, hw0, map_neg, h01, hw1, h0w, hww]
    ext i
    norm_num
    ring_nf
    grind +ring

/-- Skew-difference extraction: two isotropic hyperbolic partners `p`, `q` of
`v0` that have the same `w`-coordinate (`⟨w,p⟩ = ⟨w,q⟩`) differ by a *skew*
multiple of `v0`. -/
lemma exists_skew_diff (v0 v1 w p q : Fin 3 → F9)
    (h00 : hermForm conj9 v0 v0 = 0)
    (hww : hermForm conj9 w w = 1)
    (h01 : hermForm conj9 v0 v1 = 1)
    (h0w : hermForm conj9 v0 w = 0) (hw0 : hermForm conj9 w v0 = 0)
    (hindep : LinearIndependent F9 ![v0, v1, w])
    (hpp : hermForm conj9 p p = 0) (hqq : hermForm conj9 q q = 0)
    (h0p : hermForm conj9 v0 p = 1) (h0q : hermForm conj9 v0 q = 1)
    (hwpq : hermForm conj9 w p = hermForm conj9 w q) :
    ∃ b : F9, q = p + b • v0 ∧ b + b ^ 3 = 0 := by
  obtain ⟨z0, z1, z2, hz⟩ :
      ∃ z0 z1 z2 : F9, q - p = z0 • v0 + z1 • v1 + z2 • w := by
    have h_span : Submodule.span F9 (Set.range ![v0, v1, w]) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_eq_card] <;> norm_num [hindep]
    have := h_span.ge (Submodule.mem_top : q - p ∈ ⊤)
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨f, hf⟩ := this
    use f 0, f 1, f 2
    simp_all +decide [Fin.sum_univ_three]
  have hz1 : z1 = 0 := by
    have hz1 : hermForm conj9 v0 (q - p) = 0 := by
      simp only [hermForm_apply] at *
      simp_all +decide [Fin.sum_univ_three]
      linear_combination' h0q - h0p
    simp_all +decide [hermForm_add_right]
  have hz2 : z2 = 0 := by
    have hz2 : hermForm conj9 w (q - p) = 0 := by
      simp +decide [hermForm_apply]
      simp_all +decide [mul_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero_of_eq <| by simpa [hermForm_apply] using hwpq.symm
    simp_all +decide [hermForm_add_right]
  have hz0 : z0 + z0 ^ 3 = 0 := by
    have hz0 :
        hermForm conj9 q q =
          hermForm conj9 p p + z0 * hermForm conj9 v0 p +
          conj9 z0 * hermForm conj9 p v0 +
          z0 * conj9 z0 * hermForm conj9 v0 v0 := by
      rw [show q = p + z0 • v0 by simpa [hz1, hz2] using eq_add_of_sub_eq' hz]
      simp +decide [hermForm_add_right]
      ring_nf
    have hz0 : hermForm conj9 p v0 = 1 := by
      rw [← hermForm_conj_symm conj9_involutive]
      aesop
    simp_all +decide [conj9_apply]
  exact ⟨z0, by simpa [hz1, hz2] using eq_add_of_sub_eq' hz, hz0⟩

/-- **Transitivity of the vector stabilizer on hyperbolic partners.**  Fixing a
nonzero isotropic vector `v0`, the root-generated subgroup moves any hyperbolic
partner of `v0` to any other while fixing `v0`.

The `w`-direction of the move requires the short-root (Heisenberg) elements:
`short_root_one` provides the explicit norm-`1` case `v1 ↦ v0 + v1 + w`, and the
general partner is reached by a trichotomy on the norm
`γ * γ³ ∈ {0, 1, -1}` of the `w`-coefficient `γ`; the norm-`(-1)` case uses the
analogous norm-`(-1)` short-root element. -/
lemma rootGenerated_stab_transitive_partner
    (v0 v1 v1' : Fin 3 → F9)
    (hv0i : hermForm conj9 v0 v0 = 0)
    (hv1i : hermForm conj9 v1 v1 = 0) (hv1'i : hermForm conj9 v1' v1' = 0)
    (h01 : hermForm conj9 v0 v1 = 1) (h01' : hermForm conj9 v0 v1' = 1) :
    ∃ h ∈ rootGenerated, toLinearEquiv h v0 = v0 ∧ toLinearEquiv h v1 = v1' := by
  obtain ⟨w, hv0w, hwv0, hv1w, hwv1, hww, hindep⟩ :
      ∃ w : Fin 3 → F9,
        hermForm conj9 v0 w = 0 ∧ hermForm conj9 w v0 = 0 ∧
        hermForm conj9 v1 w = 0 ∧ hermForm conj9 w v1 = 0 ∧
        hermForm conj9 w w = 1 ∧ LinearIndependent F9 ![v0, v1, w] := by
    apply exists_orthogonal_unit v0 v1 (by
      rintro rfl
      simp_all +decide [hermForm_apply]) hv0i hv1i h01 (by
      rw [← hermForm_conj_symm conj9_involutive, h01]
      exact map_one _)
  obtain ⟨t, ht0, hts⟩ : ∃ t : F9, t ≠ 0 ∧ t + t ^ 3 = 0 := exists_skew_unit
  -- Let γ := hermForm conj9 v1' w.
  set γ := hermForm conj9 v1' w
  -- Trichotomy via `fourth_pow_cases γ` (`γ ^ 4 ∈ {0, 1, -1}`).
  obtain hγ | hγ | hγ : γ ^ 4 = 0 ∨ γ ^ 4 = 1 ∨ γ ^ 4 = -1 :=
    fourth_pow_cases γ
  · obtain ⟨b, hb⟩ : ∃ b : F9, v1' = v1 + b • v0 ∧ b + b ^ 3 = 0 := by
      apply exists_skew_diff v0 v1 w v1 v1' hv0i hww h01 hv0w hwv0 hindep
        hv1i hv1'i h01 h01' (by
          have := hermForm_conj_symm conj9_involutive v1' w
          aesop)
    use transvection v0 hv0i b hb.right * 1
    simp_all +decide
    exact ⟨transvection_mem _ _ _ _, by
      rw [show hermForm conj9 v1 v0 = 1 by
        rw [← hermForm_conj_symm conj9_involutive]
        simp +decide [*]]
      simp +decide⟩
  · -- Apply `short_root_one` to obtain `S` in the norm-`1` case.
    obtain ⟨S, hS⟩ :
        ∃ S ∈ rootGenerated,
          toLinearEquiv S v0 = v0 ∧ toLinearEquiv S v1 = v0 + v1 + γ • w := by
      apply short_root_one v0 v1 (γ • w) t ht0 hts hv0i hv1i (by
        rw [hermForm_smul_self]
        rw [conj9_apply]
        grind) h01 (by
          rw [← hermForm_conj_symm conj9_involutive]
          aesop) (by
          rw [hermForm_smul_right, hv0w, MulZeroClass.mul_zero]) (by
          rw [hermForm_smul_left, hwv0, MulZeroClass.mul_zero]) (by
          rw [hermForm_smul_right, hv1w, MulZeroClass.mul_zero]) (by
          rw [hermForm_smul_left, hwv1, MulZeroClass.mul_zero])
    obtain ⟨b, hb⟩ :
        ∃ b : F9, v1' = (v0 + v1 + γ • w) + b • v0 ∧ b + b ^ 3 = 0 :=
      exists_skew_diff v0 v1 w (v0 + v1 + γ • w) v1' hv0i hww h01
        hv0w hwv0 hindep (by
          have := toLinearEquiv_hermForm S v1 v1
          simp_all +decide [hermForm_add_right]) hv1'i (by
          simp_all +decide [hermForm_add_right]) h01' (by
          simp_all +decide [hermForm_add_right]
          rw [← hermForm_conj_symm conj9_involutive])
    refine ⟨transvection v0 hv0i b hb.2 * S, ?_, ?_, ?_⟩ <;>
      simp_all +decide [toLinearEquiv_mul_apply, toLinearEquiv_transvection,
        eichlerTransvection_apply]
    · exact Subgroup.mul_mem _ (transvection_mem _ _ _ _) hS.1
    · rw [show hermForm conj9 v1 v0 = 1 by
        rw [← hermForm_conj_symm conj9_involutive]
        simp +decide [*]]
      simp
  · -- Apply `short_root_negone` to obtain `S` in the norm-`(-1)` case.
    obtain ⟨S, hS⟩ :
        ∃ S ∈ rootGenerated,
          toLinearEquiv S v0 = v0 ∧ toLinearEquiv S v1 = -v0 + v1 + γ • w :=
      short_root_negone v0 v1 (γ • w) t ht0 hts hv0i hv1i (by
        rw [hermForm_smul_self, hww]
        rw [← hγ, conj9_apply]
        ring_nf) h01 (by
          rw [← hermForm_conj_symm conj9_involutive]
          aesop) (by
          rw [hermForm_smul_right, hv0w, MulZeroClass.mul_zero]) (by
          simp_all +decide) (by
          rw [hermForm_smul_right, hv1w, MulZeroClass.mul_zero]) (by
          rw [hermForm_smul_left, hwv1, MulZeroClass.mul_zero])
    obtain ⟨b, hb⟩ :
        ∃ b : F9, v1' = (-v0 + v1 + γ • w) + b • v0 ∧ b + b ^ 3 = 0 :=
      exists_skew_diff v0 v1 w (-v0 + v1 + γ • w) v1' hv0i hww h01
        hv0w hwv0 hindep (by
          have := toLinearEquiv_hermForm S v1 v1
          aesop) hv1'i (by
          simp_all +decide [hermForm_add_right]) h01' (by
          simp only [map_add, map_neg, map_smulₛₗ, smul_eq_mul, hwv0, hwv1, hww,
            neg_zero, zero_add, add_zero, mul_one]
          exact hermForm_conj_symm conj9_involutive v1' w)
    refine ⟨transvection v0 hv0i b hb.2 * S, ?_, ?_, ?_⟩ <;>
      simp_all +decide [toLinearEquiv_mul_apply, toLinearEquiv_transvection,
        eichlerTransvection_apply]
    · exact Subgroup.mul_mem _ (transvection_mem _ _ _ _) hS.1
    · rw [show hermForm conj9 v1 v0 = 1 by
        rw [← hermForm_conj_symm conj9_involutive]
        simp +decide [h01, conj9_apply]]
      simp

/-- **Transitivity on hyperbolic pairs.**  The root-generated subgroup acts
transitively on hyperbolic vector pairs. -/
lemma rootGenerated_hyp_pair_transitive
    (v0 v1 w0 w1 : Fin 3 → F9)
    (hv0i : hermForm conj9 v0 v0 = 0) (hv1i : hermForm conj9 v1 v1 = 0)
    (hv01 : hermForm conj9 v0 v1 = 1) (hv10 : hermForm conj9 v1 v0 = 1)
    (hw0i : hermForm conj9 w0 w0 = 0) (hw1i : hermForm conj9 w1 w1 = 0)
    (hw01 : hermForm conj9 w0 w1 = 1) (hw10 : hermForm conj9 w1 w0 = 1) :
    ∃ h ∈ rootGenerated, toLinearEquiv h v0 = w0 ∧ toLinearEquiv h v1 = w1 := by
  -- `v0 ≠ 0`, `w0 ≠ 0` since `h v0 v1 = 1 ≠ 0`.
  have hv0 : v0 ≠ 0 := by
    rintro rfl
    simp at hv01
  have hw0 : w0 ≠ 0 := by
    rintro rfl
    simp at hw01
  -- Step 1: map `v0` to `w0`.
  obtain ⟨h1, hh1, hh1v0⟩ := rootGenerated_transitive_isotropic v0 w0 hv0 hw0 hv0i hw0i
  -- Now `(w0, toLinearEquiv h1 v1)` is a hyperbolic pair, as is `(w0, w1)`.
  -- Step 2: fixing `w0`, map `toLinearEquiv h1 v1` to `w1`.
  have hb1i : hermForm conj9 (toLinearEquiv h1 v1) (toLinearEquiv h1 v1) = 0 := by
    rw [toLinearEquiv_hermForm]
    exact hv1i
  have hb01 : hermForm conj9 w0 (toLinearEquiv h1 v1) = 1 := by
    rw [← hh1v0, toLinearEquiv_hermForm]
    exact hv01
  obtain ⟨h2, hh2, hh2w0, hh2b1⟩ :=
    rootGenerated_stab_transitive_partner w0 (toLinearEquiv h1 v1) w1 hw0i hb1i hw1i hb01 hw01
  refine ⟨h2 * h1, Subgroup.mul_mem _ hh2 hh1, ?_, ?_⟩
  · rw [toLinearEquiv_mul_apply, hh1v0, hh2w0]
  · rw [toLinearEquiv_mul_apply, hh2b1]

/-! ## Main theorem -/

/-- **`SU(3,3)` is generated by its Hermitian transvections.**

The skew Eichler/Siegel transvections generate the whole special unitary group of
the `PSU(3,3)` Hermitian polarity over `GF(9)`. This is the geometric input
used in the Iwasawa simplicity route via `psuPerm_eq_closure_transvections`. -/
theorem rootGenerated_eq_top :
    rootGenerated = (⊤ : Subgroup specialUnitaryGroup) := by
  rw [eq_top_iff]
  intro g _
  -- Fix a base hyperbolic pair `(v0, v1)` from two distinct isotropic points.
  obtain ⟨p, q, hpq⟩ : ∃ p q : IsotropicPoint, p ≠ q := by
    have : Nontrivial IsotropicPoint := by
      rw [← Fintype.one_lt_card_iff_nontrivial, card_isotropicPoint]
      norm_num
    exact exists_pair_ne IsotropicPoint
  obtain ⟨v0, v1, _, _, _, _, hi0, hi1, h01, h10⟩ := exists_hyperbolic_pair p q hpq
  -- The image pair `(g v0, g v1)` is also hyperbolic.
  have gi0 : hermForm conj9 (toLinearEquiv g v0) (toLinearEquiv g v0) = 0 := by
    rw [toLinearEquiv_hermForm]
    exact hi0
  have gi1 : hermForm conj9 (toLinearEquiv g v1) (toLinearEquiv g v1) = 0 := by
    rw [toLinearEquiv_hermForm]
    exact hi1
  have g01 : hermForm conj9 (toLinearEquiv g v0) (toLinearEquiv g v1) = 1 := by
    rw [toLinearEquiv_hermForm]
    exact h01
  have g10 : hermForm conj9 (toLinearEquiv g v1) (toLinearEquiv g v0) = 1 := by
    rw [toLinearEquiv_hermForm]
    exact h10
  -- Move the base pair onto its image by a root element `h`.
  obtain ⟨h, hH, hhv0, hhv1⟩ :=
    rootGenerated_hyp_pair_transitive v0 v1 (toLinearEquiv g v0) (toLinearEquiv g v1)
      hi0 hi1 h01 h10 gi0 gi1 g01 g10
  -- Then `h⁻¹ * g` fixes the base pair, hence is the identity.
  have k0 : toLinearEquiv (h⁻¹ * g) v0 = v0 := by
    rw [toLinearEquiv_mul_apply, toLinearEquiv_inv_apply, ← hhv0, LinearEquiv.symm_apply_apply]
  have k1 : toLinearEquiv (h⁻¹ * g) v1 = v1 := by
    rw [toLinearEquiv_mul_apply, toLinearEquiv_inv_apply, ← hhv1, LinearEquiv.symm_apply_apply]
  have hk : h⁻¹ * g = 1 :=
    su_fixing_hyperbolic_pair_eq_one (h⁻¹ * g) v0 v1 hi0 hi1 h01 h10 k0 k1
  exact inv_mul_eq_one.mp hk ▸ hH

/-! ## Simplicity of `psuPerm` via the geometric Iwasawa route -/

/-- Transvections along a fixed isotropic vector multiply by adding their skew
parameters. -/
lemma transvection_mul' (u : Fin 3 → F9) (hu : hermForm conj9 u u = 0)
    (a b : F9) (ha : a + a ^ 3 = 0) (hb : b + b ^ 3 = 0)
    (hab : (a + b) + (a + b) ^ 3 = 0) :
    transvection u hu a ha * transvection u hu b hb = transvection u hu (a + b) hab := by
  apply specialUnitaryGroup_ext
  rw [toLinearEquiv_mul, toLinearEquiv_transvection, toLinearEquiv_transvection,
    toLinearEquiv_transvection, eichlerTransvection_mul]
/-- The transvection with zero parameter is the identity. -/
lemma transvection_zero' (u : Fin 3 → F9) (hu : hermForm conj9 u u = 0)
    (h0 : (0 : F9) + (0 : F9) ^ 3 = 0) : transvection u hu 0 h0 = 1 := by
  apply specialUnitaryGroup_ext
  rw [toLinearEquiv_transvection]
  ext x
  simp [eichlerTransvection_apply]
/-- Equal skew parameters yield equal transvections along a fixed isotropic
vector. -/
lemma transvection_param_congr (u : Fin 3 → F9) (hu : hermForm conj9 u u = 0)
    (a b : F9) (ha : a + a ^ 3 = 0) (hb : b + b ^ 3 = 0) (hab : a = b) :
    transvection u hu a ha = transvection u hu b hb := by
  subst hab
  rfl
/-- The inverse of a transvection is the transvection with negated parameter. -/
lemma transvection_inv' (u : Fin 3 → F9) (hu : hermForm conj9 u u = 0)
    (a : F9) (ha : a + a ^ 3 = 0) (hna : (-a) + (-a) ^ 3 = 0) :
    (transvection u hu a ha)⁻¹ = transvection u hu (-a) hna := by
  have hsk0 : (a + -a) + (a + -a) ^ 3 = 0 := by
    rw [add_neg_cancel]
    ring_nf
  have hmul : transvection u hu a ha * transvection u hu (-a) hna = 1 := by
    rw [transvection_mul' u hu a (-a) ha hna hsk0,
      transvection_param_congr u hu (a + -a) 0 hsk0 (by ring_nf) (by ring_nf),
      transvection_zero']
  exact inv_eq_of_mul_eq_one_right hmul
/-- Rescaling the isotropic vector of a transvection by `lam` rescales its
parameter by the Hermitian norm `lam * conj9 lam`. -/
lemma transvection_smul_vec' (u : Fin 3 → F9) (hu : hermForm conj9 u u = 0)
    (lam : F9) (hlu : hermForm conj9 (lam • u) (lam • u) = 0)
    (a : F9) (ha : a + a ^ 3 = 0)
    (ha' : (a * (lam * conj9 lam)) + (a * (lam * conj9 lam)) ^ 3 = 0) :
    transvection (lam • u) hlu a ha =
      transvection u hu (a * (lam * conj9 lam)) ha' := by
  apply specialUnitaryGroup_ext
  rw [toLinearEquiv_transvection, toLinearEquiv_transvection]
  refine LinearEquiv.ext (fun x => ?_)
  simp only [eichlerTransvection_apply, hermForm_smul_right, smul_smul]
  congr 2
  ring_nf
/-- Conjugating a transvection by `h` gives the transvection along the image
`h • u`, with the same skew parameter. -/
lemma transvection_conj_eq (h : specialUnitaryGroup) (u : Fin 3 → F9)
    (hu : hermForm conj9 u u = 0) (a : F9) (ha : a + a ^ 3 = 0)
    (v : Fin 3 → F9) (hv : toLinearEquiv h u = v) (hvu : hermForm conj9 v v = 0) :
    h * transvection u hu a ha * h⁻¹ = transvection v hvu a ha := by
  apply specialUnitaryGroup_ext
  rw [toLinearEquiv_mul, toLinearEquiv_mul, toLinearEquiv_transvection,
    toLinearEquiv_transvection, toLinearEquiv_inv]
  have hc := eichlerTransvection_conj (h : unitaryGroup) u hu a
  subst hv
  exact hc
/-- For a nonzero skew element `t`, the field generator `1 + t` has Hermitian
norm `(1 + t) * conj9 (1 + t) = -1`. -/
lemma skew_one_add_norm (t : F9) (ht0 : t ≠ 0) (hts : t + t ^ 3 = 0) :
    (1 + t) * conj9 (1 + t) = -1 := by
  have htsq : t ^ 2 = -1 := mul_left_cancel₀ ht0 (by linear_combination hts)
  have h3 : (3 : F9) = 0 := three_eq_zero
  rw [conj9_apply]
  have hsq : (1 + t) ^ 2 = 2 * t := by linear_combination htsq
  have he : (1 + t) * (1 + t) ^ 3 = ((1 + t) ^ 2) ^ 2 := by ring_nf
  rw [he, hsq]
  linear_combination (4 : F9) * htsq - h3

/-- Every skew transvection lies in the commutator subgroup of `SU(3,3)`. -/
lemma transvection_isCommutator (u : Fin 3 → F9) (hu : hermForm conj9 u u = 0)
    (a : F9) (ha : a + a ^ 3 = 0) :
    transvection u hu a ha ∈ commutator specialUnitaryGroup := by
  rcases eq_or_ne u 0 with rfl | hune
  · have h1 : transvection (0 : Fin 3 → F9) hu a ha = 1 := by
      apply specialUnitaryGroup_ext
      rw [toLinearEquiv_transvection]
      refine LinearEquiv.ext (fun x => ?_)
      simp [eichlerTransvection_apply, hermForm_apply]
    rw [h1]
    exact Subgroup.one_mem _
  · obtain ⟨p, hpp, hup, hpu⟩ := exists_isotropic_partner u hune hu
    obtain ⟨w, h0w, hw0, h1w, hw1, hww, hindep⟩ :=
      exists_orthogonal_unit u p hune hu hpp hup hpu
    obtain ⟨t, ht0, hts⟩ := exists_skew_unit
    obtain ⟨H, hHmem, hHu⟩ :=
      rootGenerated_scale_gen u p w t ht0 hts hu hpp hww hup hpu h0w hw0 h1w hw1
    have hnorm : (1 + t) * conj9 (1 + t) = -1 := skew_one_add_norm t ht0 hts
    have hvu : hermForm conj9 ((1 + t) • u) ((1 + t) • u) = 0 := by
      rw [← hHu, toLinearEquiv_hermForm]
      exact hu
    have hna : (-a) + (-a) ^ 3 = 0 := by linear_combination -ha
    have hskew2 :
        (a * ((1 + t) * conj9 (1 + t))) + (a * ((1 + t) * conj9 (1 + t))) ^ 3 = 0 := by
      rw [hnorm]
      linear_combination -ha
    have step1 : H * transvection u hu a ha * H⁻¹
        = transvection ((1 + t) • u) hvu a ha :=
      transvection_conj_eq H u hu a ha ((1 + t) • u) hHu hvu
    have step2 : transvection ((1 + t) • u) hvu a ha
        = transvection u hu (-a) hna :=
      (transvection_smul_vec' u hu (1 + t) hvu a ha hskew2).trans
        (transvection_param_congr u hu (a * ((1 + t) * conj9 (1 + t))) (-a)
          hskew2 hna (by
            rw [hnorm]
            ring_nf))
    have hkey : ⁅H, transvection u hu a ha⁆ = transvection u hu a ha := by
      rw [commutatorElement_def, step1, step2, transvection_inv' u hu a ha hna,
        transvection_mul' u hu (-a) (-a) hna hna
          (by linear_combination (-8 : F9) * ha + (2 * a) * three_eq_zero),
        transvection_param_congr u hu (-a + -a) a _ ha
          (by linear_combination (-a : F9) * three_eq_zero)]
    rw [← hkey, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top H) (Subgroup.mem_top _)

/-- `SU(3,3)` is perfect: its commutator subgroup is the whole group. -/
lemma commutator_specialUnitaryGroup_eq_top : commutator specialUnitaryGroup = ⊤ := by
  rw [eq_top_iff, ← rootGenerated_eq_top]
  simp only [rootGenerated, HermitianForm.rootGenerated, Subgroup.closure_le]
  intro g hg
  obtain ⟨u, hu, a, ha', rfl⟩ := hg
  exact transvection_isCommutator u hu a (by
    rw [← conj9_apply]
    exact ha')

/-- The equivariant identity map for transferring transitivity from `SU` to its
permutation image. -/
noncomputable def toPsuEquiv :
    IsotropicPoint →ₑ[(toPsu : specialUnitaryGroup → psuPerm)]
      IsotropicPoint where
  toFun := id
  map_smul' s p := (toPsu_smul s p).symm

/-- `psuPerm` acts `2`-transitively on the isotropic points. -/
lemma psuPerm_twoTransitive :
    MulAction.IsMultiplyPretransitive psuPerm IsotropicPoint 2 :=
  have : MulAction.IsMultiplyPretransitive specialUnitaryGroup IsotropicPoint 2 :=
    specialUnitaryGroup_twoTransitive
  IsPretransitive.of_embedding (f := toPsuEquiv) (Function.surjective_id)

/-- `psuPerm` is perfect: its commutator subgroup is the whole group. -/
lemma psuPerm_perfect : commutator psuPerm = ⊤ := by
  have h := map_commutator_eq (f := toPsu)
  rw [commutator_specialUnitaryGroup_eq_top, Subgroup.map_top_of_surjective _ toPsu_surjective,
    MonoidHom.range_eq_top.mpr toPsu_surjective] at h
  exact h.symm

/-- The abelian root subgroup of `SU` at the base isotropic vector. -/
def rootSubgroup : Subgroup specialUnitaryGroup where
  carrier := {g | ∃ (a : F9) (ha : a + a ^ 3 = 0), g = transvection baseVec baseVec_iso a ha}
  one_mem' := ⟨0, by ring_nf, (transvection_zero' baseVec baseVec_iso (by ring_nf)).symm⟩
  mul_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, by
      linear_combination ha + hb + (a ^ 2 * b + a * b ^ 2) * three_eq_zero,
      transvection_mul' baseVec baseVec_iso a b ha hb _⟩
  inv_mem' := by
    rintro x ⟨a, ha, rfl⟩
    exact ⟨-a, by linear_combination -ha,
      transvection_inv' baseVec baseVec_iso a ha _⟩

/-- The base root subgroup is abelian: any two of its elements commute. -/
lemma rootSubgroup_comm (x y : specialUnitaryGroup)
    (hx : x ∈ rootSubgroup) (hy : y ∈ rootSubgroup) :
    x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [transvection_mul' baseVec baseVec_iso a b ha hb
      (by linear_combination ha + hb + (a ^ 2 * b + a * b ^ 2) * three_eq_zero),
    transvection_mul' baseVec baseVec_iso b a hb ha
      (by linear_combination ha + hb + (b ^ 2 * a + b * a ^ 2) * three_eq_zero),
    transvection_param_congr baseVec baseVec_iso (a + b) (b + a) _ _ (add_comm a b)]

/-- The image of the base root subgroup in `psuPerm` is abelian. -/
instance : IsMulCommutative (rootSubgroup.map toPsu) := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨x', hx', hxeq⟩ := x.2
  obtain ⟨y', hy', hyeq⟩ := y.2
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← hxeq, ← hyeq, ← map_mul, ← map_mul,
    rootSubgroup_comm x' y' hx' hy']

/-- `psuPerm` is nontrivial. -/
instance : Nontrivial psuPerm := by
  have h2 := psuPerm_twoTransitive
  have : MulAction.IsPretransitive psuPerm IsotropicPoint :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : Nontrivial IsotropicPoint := by
    rw [← Fintype.one_lt_card_iff_nontrivial, card_isotropicPoint]
    norm_num
  obtain ⟨p, q, hpq⟩ := exists_pair_ne IsotropicPoint
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq psuPerm p q
  refine ⟨g, 1, ?_⟩
  intro hcontra
  rw [hcontra, one_smul] at hg
  exact hpq hg

/-- A special-unitary element fixing the base isotropic point scales the base
isotropic vector by a nonzero scalar. -/
lemma stab_scales_baseVec (s : specialUnitaryGroup) (hs : s • a0Pt = a0Pt) :
    ∃ μ : F9, μ ≠ 0 ∧ toLinearEquiv s baseVec = μ • baseVec := by
  have h1 : (s • a0Pt).1 = a0Pt.1 := congrArg Subtype.val hs
  rw [su_smul_fst] at h1
  simp only [a0Pt] at h1
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h1
  obtain ⟨c, hc⟩ := h1
  rw [Units.smul_def] at hc
  exact ⟨(c : F9), c.ne_zero, hc.symm⟩

/-- The Hermitian norm `μ * conj9 μ = μ⁴` of a nonzero scalar is `±1`. -/
lemma norm_self_cases (μ : F9) (hμ : μ ≠ 0) :
    (μ * conj9 μ) = 1 ∨ (μ * conj9 μ) = -1 := by
  have hn8 : μ ^ 8 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one μ hμ
    rwa [card_f9] at h
  exact mul_self_eq_one_iff.mp (by
    rw [conj9_apply]
    linear_combination hn8)

/-- The base root subgroup is stable under conjugation by stabilizer elements. -/
lemma rootSubgroup_conj_mem (s : specialUnitaryGroup) (hs : s • a0Pt = a0Pt)
    (x : specialUnitaryGroup) (hx : x ∈ rootSubgroup) : s * x * s⁻¹ ∈ rootSubgroup := by
  obtain ⟨μ, hμ, hsb⟩ := stab_scales_baseVec s hs
  obtain ⟨a, ha, rfl⟩ := hx
  have hN : (μ * conj9 μ) = 1 ∨ (μ * conj9 μ) = -1 := norm_self_cases μ hμ
  have hskew : (a * (μ * conj9 μ)) + (a * (μ * conj9 μ)) ^ 3 = 0 := by
    rcases hN with h | h <;> rw [h]
    · linear_combination ha
    · linear_combination -ha
  have hvu : hermForm conj9 (μ • baseVec) (μ • baseVec) = 0 := by
    rw [← hsb, toLinearEquiv_hermForm]
    exact baseVec_iso
  rw [transvection_conj_eq s baseVec baseVec_iso a ha (μ • baseVec) hsb hvu,
      transvection_smul_vec' baseVec baseVec_iso μ hvu a ha hskew]
  exact ⟨a * (μ * conj9 μ), hskew, rfl⟩

/-- One direction of stabilizer-invariance of the base root subgroup image. -/
lemma rootSubgroup_map_conj_le (g : psuPerm)
    (hg : g ∈ MulAction.stabilizer psuPerm a0Pt) :
    MulAut.conj g • (rootSubgroup.map toPsu) ≤ rootSubgroup.map toPsu := by
  obtain ⟨s, hs⟩ := toPsu_surjective g
  have hsa : s • a0Pt = a0Pt := by
    rwa [MulAction.mem_stabilizer_iff, ← hs, toPsu_smul] at hg
  intro y hy
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
  obtain ⟨x', hx', hxeq⟩ := Subgroup.mem_map.mp hy
  have hyeq : y = MulAut.conj g • ((MulAut.conj g)⁻¹ • y) := (smul_inv_smul _ _).symm
  rw [hyeq, ← hxeq]
  have hconj : MulAut.conj g • toPsu x' = toPsu (s * x' * s⁻¹) := by
    rw [MulAut.smul_def, MulAut.conj_apply, ← hs, ← map_inv, ← map_mul, ← map_mul]
  rw [hconj]
  exact Subgroup.mem_map_of_mem _ (rootSubgroup_conj_mem s hsa x' hx')

/-- The base root subgroup image is normalized by the stabilizer of the base
isotropic point. -/
lemma rootSubgroup_map_conj_eq (g : psuPerm)
    (hg : g ∈ MulAction.stabilizer psuPerm a0Pt) :
    MulAut.conj g • (rootSubgroup.map toPsu) = rootSubgroup.map toPsu := by
  refine le_antisymm (rootSubgroup_map_conj_le g hg) ?_
  have hg' : g⁻¹ ∈ MulAction.stabilizer psuPerm a0Pt := Subgroup.inv_mem _ hg
  have h2 := rootSubgroup_map_conj_le g⁻¹ hg'
  have hcalc : MulAut.conj g • (MulAut.conj g⁻¹ • (rootSubgroup.map toPsu))
      = rootSubgroup.map toPsu := by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  calc
    rootSubgroup.map toPsu =
        MulAut.conj g • (MulAut.conj g⁻¹ • (rootSubgroup.map toPsu)) := hcalc.symm
    _ ≤ MulAut.conj g • (rootSubgroup.map toPsu) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h2

/-- Each transvection image lies in the normal closure of the base root subgroup
image: conjugating the base root subgroup over all isotropic vectors. -/
lemma toPsu_transvection_mem_normalClosure (u : Fin 3 → F9)
    (hu : hermForm conj9 u u = 0) (a : F9) (ha : a + a ^ 3 = 0) :
    toPsu (transvection u hu a ha)
      ∈ Subgroup.normalClosure (↑(rootSubgroup.map toPsu) : Set psuPerm) := by
  rcases eq_or_ne u 0 with rfl | hune
  · have h1 : transvection (0 : Fin 3 → F9) hu a ha = 1 := by
      apply specialUnitaryGroup_ext
      rw [toLinearEquiv_transvection]
      refine LinearEquiv.ext (fun x => ?_)
      simp [eichlerTransvection_apply, hermForm_apply]
    rw [h1, map_one]
    exact one_mem _
  · obtain ⟨S, hSmem, hSb⟩ :=
      rootGenerated_transitive_isotropic baseVec u baseVec_ne hune baseVec_iso hu
    have hconj : S * transvection baseVec baseVec_iso a ha * S⁻¹
        = transvection u hu a ha :=
      transvection_conj_eq S baseVec baseVec_iso a ha u hSb hu
    rw [← hconj, map_mul, map_mul, map_inv]
    exact (Subgroup.normalClosure_normal).conj_mem _
      (Subgroup.subset_normalClosure (Subgroup.mem_map_of_mem _
        (show transvection baseVec baseVec_iso a ha ∈ rootSubgroup from ⟨a, ha, rfl⟩))) _

/-- The normal closure of the base root subgroup image is everything. -/
lemma rootSubgroup_map_normalClosure :
    Subgroup.normalClosure (↑(rootSubgroup.map toPsu) : Set psuPerm) = ⊤ := by
  rw [eq_top_iff]
  intro z hz
  clear hz
  obtain ⟨s, rfl⟩ := toPsu_surjective z
  have hs : s ∈ rootGenerated := by
    rw [rootGenerated_eq_top]
    trivial
  rw [rootGenerated, HermitianForm.rootGenerated] at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨u, hu, a, ha', rfl⟩ := hx
      exact toPsu_transvection_mem_normalClosure u hu a (by
        rw [← conj9_apply]
        exact ha')
  | one =>
      rw [map_one]
      exact one_mem _
  | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
  | inv x _ hx =>
      rw [map_inv]
      exact inv_mem hx

/-- **`PSU(3,3)` is simple.**  The projective special unitary permutation group
`psuPerm` on the `28` isotropic points is a simple group, via the geometric
Iwasawa criterion: it is perfect, acts faithfully and `2`-transitively, and the
abelian root subgroup at the base point is normalized by the point stabilizer
with full normal closure. -/
theorem isSimpleGroup_psuPerm : IsSimpleGroup psuPerm :=
  have h2 : MulAction.IsMultiplyPretransitive psuPerm IsotropicPoint 2 :=
    psuPerm_twoTransitive
  have : MulAction.IsPretransitive psuPerm IsotropicPoint :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : MulAction.IsPreprimitive psuPerm IsotropicPoint :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  let A : Subgroup psuPerm := rootSubgroup.map toPsu
  let pick : IsotropicPoint → psuPerm := fun x ↦
    (MulAction.exists_smul_eq psuPerm a0Pt x).choose
  have pick_spec : ∀ x, pick x • a0Pt = x :=
    fun x ↦ (MulAction.exists_smul_eq psuPerm a0Pt x).choose_spec
  let T : IsotropicPoint → Subgroup psuPerm := fun x ↦ MulAut.conj (pick x) • A
  have key : ∀ (h : psuPerm) (x : IsotropicPoint), h • a0Pt = x →
      MulAut.conj h • A = T x := by
    intro h x hx
    set g := pick x
    have hg : g • a0Pt = x := pick_spec x
    have hmem : g⁻¹ * h ∈ MulAction.stabilizer psuPerm a0Pt := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hx, ← hg, inv_smul_smul]
    have hconj : MulAut.conj (g⁻¹ * h) • A = A := rootSubgroup_map_conj_eq _ hmem
    have hsplit : h = g * (g⁻¹ * h) := (mul_inv_cancel_left _ _).symm
    rw [show T x = MulAut.conj g • A by rfl]
    calc
      MulAut.conj h • A = MulAut.conj (g * (g⁻¹ * h)) • A := by rw [← hsplit]
      _ = (MulAut.conj g * MulAut.conj (g⁻¹ * h)) • A := by rw [map_mul]
      _ = MulAut.conj g • (MulAut.conj (g⁻¹ * h) • A) := by rw [mul_smul]
      _ = MulAut.conj g • A := by rw [hconj]
  let I : MulAction.IwasawaStructure psuPerm IsotropicPoint := by
    refine { T := T, is_comm := ?_, is_conj := ?_, is_generator := ?_ }
    · intro x
      have hx : T x =
          A.map (MulDistribMulAction.toMonoidEnd (MulAut psuPerm) psuPerm
            (MulAut.conj (pick x))) := Subgroup.pointwise_smul_def A
      rw [hx]
      infer_instance
    · intro g x
      rw [← key (g * pick x) _ (by rw [mul_smul, pick_spec]), ← key (pick x) _
        (pick_spec x), map_mul, mul_smul]
    · rw [eq_top_iff, ← rootSubgroup_map_normalClosure, Subgroup.normalClosure,
        Subgroup.closure_le]
      intro y hy
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      apply le_iSup T (c • a0Pt)
      rw [← MulAut.conj_apply, ← MulAut.smul_def, ← key c (c • a0Pt) rfl]
      exact Subgroup.smul_mem_pointwise_smul_iff.mpr ha
  I.isSimpleGroup psuPerm_perfect inferInstance

end PSU33

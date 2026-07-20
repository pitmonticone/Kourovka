/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/

import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.Group
import Mathlib.Topology.Order.MonotoneConvergence

import Kourovka.Util.Algebra.Order.Group.Dlab

/-!
# Kourovka Notebook Problem 21.149

In its original form, Problem 21.149 asked whether there are order automorphisms of Dlab groups
that are not inner automorphisms.

We answer the question affirmatively for `H = ⟨2⟩ ≤ ℝ_{>0}`. A piecewise-linear homeomorphism
with slopes `2` on `[0, 1/3]` and `1/2` on `[1/3, 1]` normalizes `G_⟨2⟩` by conjugation,
preserves its bi-invariant first-disagreement order, and induces an order automorphism that is
not inner.

## Main definitions

* `rankOneDlabOrder`: a bi-invariant linear order on `G_⟨2⟩`.
* `rankOneConjOrderAut`: the order automorphism induced by conjugation by the
  rank-one PL homeomorphism with slopes `2` and `1/2`.

## Main results

* `rankOneConjOrderAut_not_inner`: `rankOneConjOrderAut` is not inner.
* `kourovka_21_149`: there exists a Dlab group with a non-inner order automorphism.

## Proof outline

1. Set up `IntervalAut` and the subgroup `DlabGroup H` of locally right
   `H`-linear elements that are the identity near the boundary.
2. Construct `conjAut : IntervalAut`, a piecewise-linear homeomorphism with
   slopes `2` and `1/2`, and check that conjugation by it preserves `G_⟨2⟩`,
   yielding the group automorphism `conjMulEquiv`.
3. Show that any element of `G_⟨2⟩` fixed by `conjMulEquiv` is the identity, by
   an orbit-growth argument: from the identity-near-`0` condition, the fixed
   set already contains an interval `[0, r]` with `r > 0`, and conjugation by
   `conjAut` enlarges it to `[0, conjAut r]`. Iterating gives a sequence
   `r, conjAut r, conjAut² r, …` increasing to the unique fixed point `1` of
   `conjReal` in `(0, 1]`, whence the fixed set fills `[0, 1]`.
4. Equip `G_⟨2⟩` with the *first-disagreement* relation `fd_lt`: declare
   `f < g` if there is a point `x` such that `f x < g x` and `g y ≥ f y` for
   all `y < x`. Verify that `fd_lt` is irreflexive, transitive, trichotomous,
   and bi-translation-invariant, hence defines a bi-invariant linear order
   `rankOneDlabOrder` on `G_⟨2⟩`. Show that `conjMulEquiv` preserves it.
5. Conclude that `conjMulEquiv` is an order automorphism. By step 3, no inner
   automorphism can equal `conjMulEquiv` (else the conjugating element would be
   fixed, hence trivial, contradicting that `conjMulEquiv` moves a chosen
   bump witness). This gives `rankOneConjOrderAut_not_inner`, and packaging
   yields `kourovka_21_149`.
-/

namespace MulAut

variable (G : Type*) [Group G]

/-- The subgroup of inner automorphisms of `G`. -/
def innerSubgroup : Subgroup (MulAut G) := (conj : G →* MulAut G).range

end MulAut

open scoped unitInterval Topology
open IntervalAut

namespace KourovkaNotebook
namespace Solution21_149

/-- The slope subgroup used in the witness: the rank-one group `⟨2⟩`. -/
noncomputable def witnessH : Subgroup PositiveSlopeGroup := rankOneSlopeGroup

/-- Build an `IntervalAut` from a pair of inverse monotone functions on `ℝ`. -/
noncomputable def mkIntervalAut (fR : ℝ → ℝ) (gR : ℝ → ℝ)
    (hf_maps : ∀ x, x ∈ Set.Icc 0 1 → fR x ∈ Set.Icc 0 1)
    (hg_maps : ∀ y, y ∈ Set.Icc 0 1 → gR y ∈ Set.Icc 0 1)
    (hfg : ∀ x, x ∈ Set.Icc 0 1 → gR (fR x) = x)
    (hgf : ∀ y, y ∈ Set.Icc 0 1 → fR (gR y) = y)
    (hmono : StrictMonoOn fR (Set.Icc 0 1)) : IntervalAut where
  toEquiv :=
    { toFun := fun x ↦ ⟨fR x, hf_maps x x.2⟩
      invFun := fun y ↦ ⟨gR y, hg_maps y y.2⟩
      left_inv := fun x ↦ Subtype.ext (hfg x x.2)
      right_inv := fun y ↦ Subtype.ext (hgf y y.2) }
  map_rel_iff' := by
    intro a b
    exact (show StrictMono (fun x : IntervalPoint ↦ fR x) from
      fun x y hxy ↦ hmono x.2 y.2 hxy).le_iff_le

/-- The real-valued formula for the conjugating PL homeomorphism. -/
noncomputable def conjReal (x : ℝ) : ℝ :=
  if x ≤ 1 / 3 then 2 * x else 2 / 3 + (x - 1 / 3) / 2

/-- The real-valued formula for the inverse of the conjugating PL homeomorphism. -/
noncomputable def conjRealInv (y : ℝ) : ℝ :=
  if y ≤ 2 / 3 then y / 2 else 1 / 3 + 2 * (y - 2 / 3)

/-- The conjugating PL formula `conjReal` maps `[0,1]` into itself. -/
lemma conjReal_maps : ∀ x, x ∈ Set.Icc 0 1 → conjReal x ∈ Set.Icc 0 1 := by
  intro x ⟨h0, h1⟩
  simp only [conjReal]
  split_ifs <;> refine ⟨?_, ?_⟩ <;> nlinarith

/-- The inverse formula `conjRealInv` maps `[0,1]` into itself. -/
lemma conjRealInv_maps : ∀ y, y ∈ Set.Icc 0 1 → conjRealInv y ∈ Set.Icc 0 1 := by
  intro y ⟨h0, h1⟩
  simp only [conjRealInv]
  split_ifs <;> refine ⟨?_, ?_⟩ <;> nlinarith

/-- `conjRealInv` is a left inverse of `conjReal` on `[0,1]`. -/
lemma conjRealInv_conjReal : ∀ x, x ∈ Set.Icc 0 1 → conjRealInv (conjReal x) = x := by
  intro x ⟨h0, h1⟩
  simp only [conjRealInv, conjReal]
  split_ifs <;> nlinarith

/-- `conjRealInv` is a right inverse of `conjReal` on `[0,1]`. -/
lemma conjReal_conjRealInv : ∀ y, y ∈ Set.Icc 0 1 → conjReal (conjRealInv y) = y := by
  intro y ⟨h0, h1⟩
  simp only [conjReal, conjRealInv]
  split_ifs <;> nlinarith

/-- `conjReal` is strictly monotone on `[0,1]`. -/
lemma conjReal_strictMono : StrictMonoOn conjReal (Set.Icc 0 1) := by
  intro a ⟨ha0, ha1⟩ b ⟨hb0, hb1⟩ hab
  simp only [conjReal]
  split_ifs <;> nlinarith

/-- The conjugating PL homeomorphism: slope `2` on `[0, 1/3]`,
slope `1/2` on `[1/3, 1]`. -/
noncomputable def conjAut : IntervalAut :=
  mkIntervalAut conjReal conjRealInv conjReal_maps conjRealInv_maps conjRealInv_conjReal
    conjReal_conjRealInv conjReal_strictMono

/-- The real-valued formula for the bump automorphism used to witness
non-innerness. -/
noncomputable def bumpReal (x : ℝ) : ℝ :=
  if x ≤ 1 / 4 then x
  else
    if x ≤ 3 / 8 then 1 / 4 + 2 * (x - 1 / 4) else if x ≤ 5 / 8 then 1 / 2 + (x - 3 / 8) / 2 else x

/-- The real-valued formula for the inverse of the bump automorphism. -/
noncomputable def bumpRealInv (y : ℝ) : ℝ :=
  if y ≤ 1 / 4 then y
  else
    if y ≤ 1 / 2 then 1 / 4 + (y - 1 / 4) / 2 else if y ≤ 5 / 8 then 3 / 8 + 2 * (y - 1 / 2) else y

/-- The bump PL formula `bumpReal` maps `[0,1]` into itself. -/
lemma bumpReal_maps : ∀ x, x ∈ Set.Icc 0 1 → bumpReal x ∈ Set.Icc 0 1 := by
  intro x ⟨h0, h1⟩
  simp only [bumpReal]
  split_ifs <;> refine ⟨?_, ?_⟩ <;> nlinarith

/-- The inverse formula `bumpRealInv` maps `[0,1]` into itself. -/
lemma bumpRealInv_maps : ∀ y, y ∈ Set.Icc 0 1 → bumpRealInv y ∈ Set.Icc 0 1 := by
  intro y ⟨h0, h1⟩
  simp only [bumpRealInv]
  split_ifs <;> refine ⟨?_, ?_⟩ <;> nlinarith

/-- `bumpRealInv` is a left inverse of `bumpReal` on `[0,1]`. -/
lemma bumpRealInv_bumpReal : ∀ x, x ∈ Set.Icc 0 1 → bumpRealInv (bumpReal x) = x := by
  intro x ⟨h0, h1⟩
  simp only [bumpRealInv, bumpReal]
  split_ifs <;> nlinarith

/-- `bumpRealInv` is a right inverse of `bumpReal` on `[0,1]`. -/
lemma bumpReal_bumpRealInv : ∀ y, y ∈ Set.Icc 0 1 → bumpReal (bumpRealInv y) = y := by
  intro y ⟨h0, h1⟩
  simp only [bumpReal, bumpRealInv]
  split_ifs <;> nlinarith

/-- `bumpReal` is strictly monotone on `[0,1]`. -/
lemma bumpReal_strictMono : StrictMonoOn bumpReal (Set.Icc 0 1) := by
  intro a ⟨ha0, ha1⟩ b ⟨hb0, hb1⟩ hab
  simp only [bumpReal]
  split_ifs <;> nlinarith

/-- Nontrivial PL homeomorphism in `DlabGroup ⟨2⟩`, used as a test element for
non-innerness. -/
noncomputable def bumpAut : IntervalAut :=
  mkIntervalAut bumpReal bumpRealInv bumpReal_maps bumpRealInv_maps bumpRealInv_bumpReal
    bumpReal_bumpRealInv bumpReal_strictMono

set_option maxHeartbeats 800000 in
/-- The bump automorphism satisfies all Dlab conditions for `H = ⟨2⟩`. -/
lemma bumpAut_isDlab : IsDlabElement witnessH bumpAut := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    by_cases ha1 : a.val < 1 / 4
    · refine ⟨(1 / 4 - a.val) / 2, by linarith, ⟨1, witnessH.one_mem⟩, ?_⟩
      intro x hx₁ hx₂
      change bumpReal x = bumpReal a + slopeToReal 1 * ((x : ℝ) - a)
      norm_num [slopeToReal, Dlab.slopeToReal]
      unfold bumpReal
      split_ifs <;> nlinarith [show (x : ℝ) < 1 / 4 by linarith]
    · by_cases ha2 : a.val < 3 / 8
      · refine ⟨3 / 8 - a.val, by linarith,
          ⟨twoSlope, by simpa [witnessH] using twoSlope_mem_rankOne⟩, ?_⟩
        intro x hx₁ hx₂
        change bumpReal x = bumpReal a + slopeToReal twoSlope * ((x : ℝ) - a)
        norm_num [slopeToReal, Dlab.slopeToReal, twoSlope]
        unfold bumpReal
        split_ifs <;> nlinarith
      · by_cases ha3 : a.val < 5 / 8
        · refine ⟨(5 / 8 - a.val) / 2, by linarith,
            ⟨twoSlope⁻¹, by simpa [witnessH] using twoSlope_inv_mem_rankOne⟩, ?_⟩
          intro x hx₁ hx₂
          change bumpReal x = bumpReal a + slopeToReal twoSlope⁻¹ * ((x : ℝ) - a)
          norm_num [slopeToReal, Dlab.slopeToReal, twoSlope]
          unfold bumpReal
          split_ifs <;> nlinarith
        · refine ⟨1 - a.val, sub_pos.mpr (by simpa using ha), ⟨1, witnessH.one_mem⟩, ?_⟩
          intro x hx₁ hx₂
          change bumpReal x = bumpReal a + slopeToReal 1 * ((x : ℝ) - a)
          norm_num [slopeToReal, Dlab.slopeToReal]
          unfold bumpReal
          split_ifs <;> nlinarith
  · have hs : {x : IntervalPoint | x.1 ≤ 1 / 4} ∈ 𝓝 (0 : IntervalPoint) := by
      rw [Metric.mem_nhds_iff]
      norm_num [Set.subset_def, Metric.mem_ball, Subtype.dist_eq]
      refine ⟨1 / 4, by norm_num, fun a ha₁ ha₂ ha₃ ↦ ?_⟩
      linarith [abs_lt.mp ha₃]
    filter_upwards [hs] with x hx
    exact Subtype.ext <| show (bumpReal x : ℝ) = x by
      unfold bumpReal
      split_ifs <;> linarith [hx]
  · have hs : {x : IntervalPoint | x.val > 5 / 8} ∈ 𝓝 (1 : IntervalPoint) :=
      IsOpen.mem_nhds (isOpen_lt continuous_const continuous_subtype_val) (by norm_num)
    filter_upwards [hs] with x hx
    exact Subtype.ext <| show (bumpReal x : ℝ) = x by
      unfold bumpReal
      split_ifs <;> linarith [hx, x.2.1, x.2.2]

/-- The bump automorphism is not the identity. -/
lemma bumpAut_ne_one : bumpAut ≠ 1 := by
  intro h
  have h_eval := congrArg
    (fun f : IntervalAut ↦ (f (⟨5 / 16, by norm_num⟩ : IntervalPoint) : ℝ)) h
  norm_num [bumpAut, mkIntervalAut, bumpReal] at h_eval

/-- `conjAut⁻¹` is locally right `⟨2⟩`-linear. -/
lemma conjAut_inv_locallyRightHLinear : IsLocallyRightHLinear witnessH conjAut⁻¹ := by
  intro a ha
  by_cases ha' : a.val < 2 / 3
  · refine ⟨2 / 3 - a.val, ?_, ?_⟩
    · linarith
    · refine ⟨⟨twoSlope⁻¹, by simpa [witnessH] using twoSlope_inv_mem_rankOne⟩,
        fun {x} hx₁ hx₂ ↦ ?_⟩
      change conjRealInv x = conjRealInv a + slopeToReal twoSlope⁻¹ * ((x : ℝ) - a)
      norm_num [conjRealInv, slopeToReal, Dlab.slopeToReal, twoSlope]
      split_ifs <;> nlinarith
  · refine ⟨1 / 3, by norm_num, ?_⟩
    refine ⟨⟨twoSlope, by simpa [witnessH] using twoSlope_mem_rankOne⟩, ?_⟩
    intro x hx₁ hx₂
    change conjRealInv (x : ℝ) = conjRealInv (a : ℝ) + slopeToReal twoSlope * ((x : ℝ) - (a : ℝ))
    norm_num [slopeToReal, Dlab.slopeToReal, twoSlope, conjRealInv]
    split_ifs <;> nlinarith

/-- `conjAut` is locally right `⟨2⟩`-linear. -/
lemma conjAut_locallyRightHLinear : IsLocallyRightHLinear witnessH conjAut := by
  intro x hx
  by_cases hx' : x.val < 1 / 3
  · refine ⟨1 / 3 - x.val, ?_, ?_⟩
    · linarith
    · refine ⟨⟨twoSlope, by simpa [witnessH] using twoSlope_mem_rankOne⟩,
        fun {y} hy₁ hy₂ ↦ ?_⟩
      change conjReal y = conjReal x + slopeToReal twoSlope * ((y : ℝ) - x)
      norm_num [slopeToReal, Dlab.slopeToReal, twoSlope, conjReal]
      split_ifs <;> nlinarith
  · refine ⟨1 / 3, by norm_num,
      ⟨⟨twoSlope⁻¹, by simpa [witnessH] using twoSlope_inv_mem_rankOne⟩, ?_⟩⟩
    intro a ha₁ ha₂
    change conjReal a = conjReal x + slopeToReal twoSlope⁻¹ * ((a : ℝ) - x)
    norm_num [slopeToReal, Dlab.slopeToReal, twoSlope, conjReal]
    split_ifs <;> nlinarith

/-- The conjugating homeomorphism lies in the ambient locally `⟨2⟩`-linear group, but
not in Dlab's compact-support subgroup: it is not the identity on any neighborhood of
`0`. -/
lemma conjAut_not_isDlabElement : ¬IsDlabElement witnessH conjAut := by
  rintro ⟨_, hs, _⟩
  obtain ⟨ε, hε_pos, hε⟩ := Metric.mem_nhds_iff.mp hs
  let xval : ℝ := min (ε / 2) (1 / 6)
  have hx_pos : 0 < xval := lt_min (by linarith) (by norm_num)
  have hx_le_one : xval ≤ 1 := by linarith [min_le_right (ε / 2) (1 / 6)]
  let x : IntervalPoint := ⟨xval, ⟨le_of_lt hx_pos, hx_le_one⟩⟩
  have hx_fixed : conjAut x = x := by
    apply hε
    change dist x 0 < ε
    rw [Subtype.dist_eq]
    change |xval - 0| < ε
    rw [sub_zero, abs_of_nonneg (le_of_lt hx_pos)]
    linarith [min_le_left (ε / 2) (1 / 6)]
  have hx_fixed' : (conjAut x : ℝ) = x := congrArg Subtype.val hx_fixed
  have hx_small : xval ≤ 1 / 3 := by linarith [min_le_right (ε / 2) (1 / 6)]
  have hx_conj : (conjAut x : ℝ) = 2 * xval := by
    change conjReal xval = 2 * xval
    rw [conjReal, if_pos hx_small]
  change (conjAut x : ℝ) = xval at hx_fixed'
  linarith [hx_fixed', hx_conj, hx_pos]

/-- Conjugation by `conjAut` preserves the Dlab predicate. -/
lemma isDlabElement_conj (f : IntervalAut) (hf : IsDlabElement witnessH f) :
    IsDlabElement witnessH (conjAut⁻¹ * f * conjAut) := by
  refine ⟨isLocallyRightHLinear_mul
    (isLocallyRightHLinear_mul conjAut_inv_locallyRightHLinear hf.1)
    conjAut_locallyRightHLinear, ?_, ?_⟩
  · have hc : Filter.Tendsto conjAut (𝓝 (0 : IntervalPoint)) (𝓝 (0 : IntervalPoint)) := by
      have hcont : ContinuousAt (fun x : IntervalPoint ↦ conjAut x) 0 :=
        conjAut.toHomeomorph.continuous.continuousAt
      change Filter.Tendsto conjAut (𝓝 (0 : IntervalPoint)) (𝓝 (conjAut 0)) at hcont
      rw [IntervalAut.map_zero] at hcont
      exact hcont
    filter_upwards [hf.2.1.comp_tendsto hc] with x hx
    have hx' : f (conjAut x) = conjAut x := by simpa using hx
    simpa using congrArg (fun y ↦ conjAut⁻¹ y) hx'
  · have hc : Filter.Tendsto conjAut (𝓝 (1 : IntervalPoint)) (𝓝 (1 : IntervalPoint)) := by
      have hcont : ContinuousAt (fun x : IntervalPoint ↦ conjAut x) 1 :=
        conjAut.toHomeomorph.continuous.continuousAt
      change Filter.Tendsto conjAut (𝓝 (1 : IntervalPoint)) (𝓝 (conjAut 1)) at hcont
      rw [IntervalAut.map_one] at hcont
      exact hcont
    filter_upwards [hf.2.2.comp_tendsto hc] with x hx
    have hx' : f (conjAut x) = conjAut x := by simpa using hx
    simpa using congrArg (fun y ↦ conjAut⁻¹ y) hx'

/-- Conjugation by `conjAut⁻¹` preserves the Dlab predicate. -/
lemma isDlabElement_conj_inv (f : IntervalAut) (hf : IsDlabElement witnessH f) :
    IsDlabElement witnessH (conjAut * f * conjAut⁻¹) := by
  refine ⟨isLocallyRightHLinear_mul
    (isLocallyRightHLinear_mul conjAut_locallyRightHLinear hf.1)
    conjAut_inv_locallyRightHLinear, ?_, ?_⟩
  · have hc : Filter.Tendsto (fun x ↦ conjAut⁻¹ x) (𝓝 (0 : IntervalPoint))
        (𝓝 (0 : IntervalPoint)) := by
      have hcont : ContinuousAt (fun x : IntervalPoint ↦ conjAut⁻¹ x) 0 :=
        conjAut⁻¹.toHomeomorph.continuous.continuousAt
      change Filter.Tendsto (fun x ↦ conjAut⁻¹ x) (𝓝 (0 : IntervalPoint))
        (𝓝 (conjAut⁻¹ 0)) at hcont
      rw [IntervalAut.map_zero] at hcont
      exact hcont
    filter_upwards [hf.2.1.comp_tendsto hc] with x hx
    have hx' : f (conjAut⁻¹ x) = conjAut⁻¹ x := by simpa using hx
    simpa using congrArg conjAut.toHomeomorph hx'
  · have hc : Filter.Tendsto (fun x ↦ conjAut⁻¹ x) (𝓝 (1 : IntervalPoint))
        (𝓝 (1 : IntervalPoint)) := by
      have hcont : ContinuousAt (fun x : IntervalPoint ↦ conjAut⁻¹ x) 1 :=
        conjAut⁻¹.toHomeomorph.continuous.continuousAt
      change Filter.Tendsto (fun x ↦ conjAut⁻¹ x) (𝓝 (1 : IntervalPoint))
        (𝓝 (conjAut⁻¹ 1)) at hcont
      rw [IntervalAut.map_one] at hcont
      exact hcont
    filter_upwards [hf.2.2.comp_tendsto hc] with x hx
    have hx' : f (conjAut⁻¹ x) = conjAut⁻¹ x := by simpa using hx
    simpa using congrArg conjAut.toHomeomorph hx'

/-- Conjugation by `conjAut` as a group automorphism of the rank-one Dlab group. -/
noncomputable def conjMulEquiv : DlabGroup witnessH ≃* DlabGroup witnessH where
  toFun := fun ⟨f, hf⟩ ↦ ⟨conjAut⁻¹ * f * conjAut, isDlabElement_conj f hf⟩
  invFun := fun ⟨f, hf⟩ ↦ ⟨conjAut * f * conjAut⁻¹, isDlabElement_conj_inv f hf⟩
  left_inv := fun ⟨_, _⟩ ↦ Subtype.ext (by group)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext (by group)
  map_mul' := fun ⟨f, _⟩ ⟨g, _⟩ ↦ Subtype.ext <| by
    change conjAut⁻¹ * (f * g) * conjAut =
      (conjAut⁻¹ * f * conjAut) * (conjAut⁻¹ * g * conjAut)
    group

/-- A nonidentity element of the rank-one Dlab group. -/
noncomputable def witnessElement : DlabGroup witnessH := ⟨bumpAut, bumpAut_isDlab⟩

/-- The witness element is not the identity. -/
lemma witnessElement_ne_one : witnessElement ≠ 1 := fun h ↦ bumpAut_ne_one (congr_arg Subtype.val h)

/-- An element of the rank-one Dlab group fixed by conjugation with `conjAut` is the identity. -/
theorem eq_one_of_conjMulEquiv_eq_self (f : DlabGroup witnessH) (hfix : conjMulEquiv f = f) :
    f = 1 := by
  have h_eq : ∀ x : IntervalPoint, f.1 (conjAut x) = conjAut (f.1 x) := by
    intro x
    have hpoint : conjAut⁻¹ (f.1 (conjAut x)) = f.1 x := by
      simpa [conjMulEquiv] using congrArg (fun g : DlabGroup witnessH ↦ g.1 x) hfix
    simpa using congrArg conjAut.toHomeomorph hpoint
  obtain ⟨r, hr₀, hr₁⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x : IntervalPoint, x.val ≤ r → f.1 x = x := by
    obtain ⟨ε, εpos, hε⟩ := Metric.mem_nhds_iff.mp f.2.2.1
    refine ⟨min (ε / 2) (1 / 2), ?_, ?_, ?_⟩ <;> norm_num [εpos]
    intro a ha₁ ha₂ ha₃ ha₄
    apply hε
    change dist (⟨a, ⟨ha₁, ha₂⟩⟩ : IntervalPoint) 0 < ε
    rw [Subtype.dist_eq]
    simpa [abs_of_nonneg ha₁] using by linarith
  let iter : ℕ → ℝ := fun n ↦ Nat.rec r (fun _ r' ↦ conjReal r') n
  have h_ind : ∀ n : ℕ, ∀ x : IntervalPoint, x.val ≤ iter n → f.1 x = x := by
    intro n
    induction n with
    | zero => exact hr₁.2
    | succ n ih =>
      intro x hx
      have h_preimage : conjAut⁻¹ x ∈ {y : IntervalPoint | y.val ≤ iter n} := by
        have h_preimage_le : conjRealInv x.val ≤ iter n := by
          have h_conjRealInv_x_le : conjReal (conjRealInv x.val) = x.val :=
            conjReal_conjRealInv x x.2
          contrapose! hx
          simp_all only [Subtype.forall, Set.mem_Icc, forall_and_index, conjReal, one_div, iter]
          split_ifs at * <;> linarith [show (x : ℝ) ≤ 1 from x.2.2]
        exact h_preimage_le
      have h_preimage_fixed : f.1 (conjAut⁻¹ x) = conjAut⁻¹ x := ih _ h_preimage
      simpa [h_preimage_fixed] using h_eq (conjAut⁻¹.toHomeomorph x)
  have h_lim : Filter.Tendsto iter Filter.atTop (nhds 1) := by
    have h_inc : StrictMono iter := by
      refine strictMono_nat_of_lt_succ ?_
      intro n
      refine Nat.recOn n ?_ ?_ <;> norm_num [iter, conjReal]
      · split_ifs <;> linarith
      · grind
    obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto iter Filter.atTop (nhds L) := by
      have h_bound : ∀ n, (iter n : ℝ) ≤ 1 := by
        intro n
        induction n <;> norm_num [iter, conjReal]
        · linarith
        · split_ifs <;> linarith!
      exact ⟨_, tendsto_atTop_isLUB h_inc.monotone <|
        isLUB_ciSup ⟨1, Set.forall_mem_range.mpr h_bound⟩⟩
    have hL_fixed : conjReal L = L := by
      have h_conj_tendsto :
        Filter.Tendsto (fun n ↦ conjReal (iter n : ℝ)) Filter.atTop (nhds (conjReal L)) := by
        refine Continuous.continuousAt ?_ |>.tendsto.comp hL
        apply_rules [Continuous.if_le, Continuous.add, Continuous.mul, continuous_id,
          continuous_const]
        norm_num
      exact tendsto_nhds_unique h_conj_tendsto (hL.comp (Filter.tendsto_add_atTop_nat 1))
    convert hL
    unfold conjReal at hL_fixed
    have hL_pos : 0 < L := lt_of_lt_of_le hr₀ <|
      le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun n ↦ h_inc.monotone n.zero_le
    split_ifs at hL_fixed <;> linarith
  have h_id : ∀ x : IntervalPoint, f.1 x = x := by
    intro x
    by_cases hx : x.val < 1
    · obtain ⟨n, hn⟩ := (h_lim.eventually (lt_mem_nhds hx)).exists
      exact h_ind n x hn.le
    · cases eq_or_lt_of_le x.2.2 <;> aesop
  exact Subtype.ext <| ext _ _ h_id

/-- The conjugation automorphism `conjMulEquiv` is not inner. -/
theorem conjMulEquiv_not_inner : conjMulEquiv ∉ MulAut.innerSubgroup (DlabGroup witnessH) := by
  intro ⟨h, hh⟩
  have hfixed : conjMulEquiv h = h := by
    rw [← hh]
    simp [MulAut.conj_apply]
  have h1 : h = 1 := eq_one_of_conjMulEquiv_eq_self h hfixed
  apply witnessElement_ne_one
  apply eq_one_of_conjMulEquiv_eq_self
  rw [← hh, h1]
  simp

/-- The *first-disagreement* strict relation: `f` is below `g` iff there exists a point
`x` where `f(x) < g(x)` and every point where `g(y) < f(y)` lies to its right. -/
def FirstDisagreementLt (H : Subgroup PositiveSlopeGroup) (f g : DlabGroup H) : Prop :=
  ∃ x : IntervalPoint,
    (f.1 x : ℝ) < (g.1 x : ℝ) ∧ ∀ y : IntervalPoint, (g.1 y : ℝ) < (f.1 y : ℝ) → (x : ℝ) < (y : ℝ)

/-- The rank-one first-disagreement relation used to build the witness order. -/
def fd_lt (f g : DlabGroup witnessH) : Prop :=
  ∃ x : IntervalPoint,
    (f.1 x : ℝ) < (g.1 x : ℝ) ∧ ∀ y : IntervalPoint, (g.1 y : ℝ) < (f.1 y : ℝ) → (x : ℝ) < (y : ℝ)

/-- `fd_lt` is irreflexive. -/
lemma fd_lt_irrefl (f : DlabGroup witnessH) : ¬fd_lt f f := fun ⟨_, hlt, _⟩ ↦ lt_irrefl _ hlt

/-- `fd_lt` is asymmetric. -/
lemma fd_lt_asymm {f g : DlabGroup witnessH} (h : fd_lt f g) : ¬fd_lt g f := fun ⟨y, hgy, hy⟩ ↦ by
  obtain ⟨x, hfx, hx⟩ := h
  linarith [hx y hgy, hy x hfx]

/-- `fd_lt` is transitive. -/
lemma fd_lt_trans {f g h : DlabGroup witnessH} (hfg : fd_lt f g) (hgh : fd_lt g h) : fd_lt f h := by
  obtain ⟨x, hx₁, hx₂⟩ := hfg
  obtain ⟨y, hy₁, hy₂⟩ := hgh
  by_cases hxy : (x : ℝ) ≤ (y : ℝ) <;> grind +locals

set_option maxHeartbeats 400000 in
/-- `fd_lt` satisfies trichotomy: for any `f g`, exactly one of `f = g`, `fd_lt f g`,
or `fd_lt g f` holds. -/
lemma fd_lt_trichotomy (f g : DlabGroup witnessH) : f = g ∨ fd_lt f g ∨ fd_lt g f := by
  by_contra! h_contra
  have h_inf :
      ∀ x : IntervalPoint, (f.1 x : ℝ) < (g.1 x : ℝ) →
        ∃ y : IntervalPoint, (g.1 y : ℝ) < (f.1 y : ℝ) ∧ (y : ℝ) ≤ (x : ℝ) :=
    fun x hx ↦ not_not.1 fun h ↦ h_contra.2.1 ⟨x, hx, fun y hy ↦ not_le.1 fun hxy ↦ h ⟨y, hy, hxy⟩⟩
  have h_inf_rev :
      ∀ x : IntervalPoint, (g.1 x : ℝ) < (f.1 x : ℝ) →
        ∃ y : IntervalPoint, (f.1 y : ℝ) < (g.1 y : ℝ) ∧ (y : ℝ) ≤ (x : ℝ) :=
    fun x hx ↦
    not_forall_not.mp fun h ↦ h_contra.2.2 ⟨x, hx, fun y hy ↦ not_le.mp fun hxy ↦ h y <| by tauto⟩
  obtain ⟨L, hL⟩ :
      ∃ L : ℝ, L ∈ Set.Icc 0 1 ∧
        (∀ x : IntervalPoint, (f.1 x : ℝ) ≠ (g.1 x : ℝ) → L ≤ (x : ℝ)) ∧
        ∀ ε > 0, ∃ x : IntervalPoint, (f.1 x : ℝ) ≠ (g.1 x : ℝ) ∧ (x : ℝ) < L + ε := by
    have h_nonempty : ∃ x : IntervalPoint, (f.1 x : ℝ) ≠ (g.1 x : ℝ) :=
      not_forall.mp fun h ↦
        h_contra.1 <| Subtype.ext <| by
          ext
          exact h _
    have hs : {x : ℝ | ∃ p : IntervalPoint,
        p.val = x ∧ (f.1 p : ℝ) ≠ (g.1 p : ℝ)}.Nonempty :=
      ⟨_, h_nonempty.choose, rfl, h_nonempty.choose_spec⟩
    have hs_lower : ∀ x ∈ {x : ℝ | ∃ p : IntervalPoint,
        p.val = x ∧ (f.1 p : ℝ) ≠ (g.1 p : ℝ)}, 0 ≤ x := by
      rintro x ⟨p, rfl, _⟩
      exact p.2.1
    have hs_bdd : BddBelow {x : ℝ | ∃ p : IntervalPoint,
        p.val = x ∧ (f.1 p : ℝ) ≠ (g.1 p : ℝ)} := ⟨0, hs_lower⟩
    use sInf {x : ℝ | ∃ p : IntervalPoint, p.val = x ∧ (f.1 p : ℝ) ≠ (g.1 p : ℝ)}
    refine ⟨⟨le_csInf hs hs_lower, ?_⟩, ?_, ?_⟩
    · exact le_trans
        (csInf_le hs_bdd ⟨h_nonempty.choose, rfl, h_nonempty.choose_spec⟩)
        h_nonempty.choose.2.2
    · exact fun x hx ↦ csInf_le hs_bdd ⟨x, rfl, hx⟩
    · intro ε ε_pos
      obtain ⟨_, ⟨p, rfl, hp⟩, hlt⟩ :=
        exists_lt_of_csInf_lt hs (lt_add_of_pos_right _ ε_pos)
      exact ⟨p, hp, hlt⟩
  have h_eq : (f.1 ⟨L, hL.left⟩ : ℝ) = (g.1 ⟨L, hL.left⟩ : ℝ) := by
    by_contra h_eq'
    obtain ⟨ε, hε_pos, hε⟩ :
      ∃ ε > 0, ∀ x : IntervalPoint, abs ((x : ℝ) - L) < ε → (f.1 x : ℝ) ≠ (g.1 x : ℝ) := by
      have h_cont : Continuous (fun x : IntervalPoint ↦ (f.1 x : ℝ) - (g.1 x : ℝ)) := by fun_prop
      have := Metric.continuous_iff.mp h_cont ⟨L, hL.1⟩
      obtain ⟨δ, hδ⟩ := this (|(f.1 ⟨L, hL.1⟩ : ℝ) - (g.1 ⟨L, hL.1⟩ : ℝ)|)
        (abs_pos.mpr (sub_ne_zero.mpr h_eq'))
      refine ⟨δ, hδ.1, fun x hx hx' ↦ h_eq' <| ?_⟩
      cases abs_cases ((f.1 ⟨L, hL.1⟩ : ℝ) - (g.1 ⟨L, hL.1⟩ : ℝ)) <;>
        linarith [abs_lt.mp (hδ.2 x <| by simpa [Subtype.dist_eq] using hx)]
    obtain ⟨x, hx₁, hx₂⟩ : ∃ x : IntervalPoint, (f.1 x : ℝ) ≠ (g.1 x : ℝ) ∧ (x : ℝ) < L := by
      by_cases hL_zero : L = 0
      · simp_all
      · use ⟨max 0 (L - ε / 2),
            ⟨le_max_left _ _, max_le (by linarith [hL.1.1]) (by linarith [hL.1.2])⟩⟩
        refine ⟨hε _ <| abs_lt.mpr ⟨?_, ?_⟩, ?_⟩
        · cases max_cases 0 (L - ε / 2) <;> linarith [hL.1.1, hL.1.2]
        · cases max_cases 0 (L - ε / 2) <;> linarith [hL.1.1, hL.1.2]
        · cases max_cases 0 (L - ε / 2) <;>
            linarith [hL.1.1, hL.1.2, show L > 0 from lt_of_le_of_ne hL.1.1 (Ne.symm hL_zero)]
    linarith [hL.2.1 x hx₁]
  obtain ⟨ε, hε_pos, hε⟩ :
      ∃ ε > 0, ∃ h_f h_g : PositiveSlopeGroup, ∀ x : IntervalPoint,
        L < (x : ℝ) → (x : ℝ) < L + ε →
        (f.1 x : ℝ) = (f.1 ⟨L, hL.left⟩ : ℝ) + slopeToReal h_f * ((x : ℝ) - L) ∧
        (g.1 x : ℝ) = (g.1 ⟨L, hL.left⟩ : ℝ) + slopeToReal h_g * ((x : ℝ) - L) := by
    have h_locally_right_linear :
        ∀ f : DlabGroup witnessH, ∀ a : IntervalPoint, a < 1 →
        ∃ ε > 0, ∃ h : PositiveSlopeGroup, ∀ x : IntervalPoint,
        (a : ℝ) < x → (x : ℝ) < (a : ℝ) + ε →
        (f.1 x : ℝ) = (f.1 a : ℝ) + slopeToReal h * ((x : ℝ) - (a : ℝ)) := by
      intro f a ha
      obtain ⟨ε, hε, h, hh⟩ := f.2.1 a ha
      exact ⟨ε, hε, h, hh⟩
    by_cases hL1 : L = 1
    · refine ⟨1, by norm_num, 1, 1, ?_⟩
      intro x hx _
      exfalso
      linarith [hL1, x.2.2]
    · obtain ⟨ε_f, hε_f_pos, hε_f⟩ :=
        h_locally_right_linear f ⟨L, hL.left⟩ (Subtype.mk_lt_mk.mpr (lt_of_le_of_ne hL.1.2 hL1))
      obtain ⟨ε_g, hε_g_pos, hε_g⟩ :=
        h_locally_right_linear g ⟨L, hL.left⟩ (Subtype.mk_lt_mk.mpr (lt_of_le_of_ne hL.1.2 hL1))
      exact ⟨min ε_f ε_g, lt_min hε_f_pos hε_g_pos, hε_f.choose, hε_g.choose,
        fun x hx₁ hx₂ ↦ ⟨hε_f.choose_spec x hx₁ (by linarith [min_le_left ε_f ε_g]),
          hε_g.choose_spec x hx₁ (by linarith [min_le_right ε_f ε_g])⟩⟩
  obtain ⟨h_f, h_g, hε⟩ := hε
  have h_neq : h_f ≠ h_g := by
    intro h_eq_hg
    have h_eq_fg : ∀ x : IntervalPoint, L < (x : ℝ) → (x : ℝ) < L + ε → (f.1 x : ℝ) = (g.1 x : ℝ) :=
      by grind
    obtain ⟨x, hx₁, hx₂⟩ := hL.2.2 ε hε_pos
    by_cases hx₃ : L < (x : ℝ)
    · exact hx₁ <| h_eq_fg x hx₃ hx₂
    · exact hx₁ <| by
        rwa [show x = ⟨L, hL.1⟩ from
          Subtype.ext <| le_antisymm (le_of_not_gt hx₃) (hL.2.1 x hx₁)]
  by_cases h_cases : slopeToReal h_f < slopeToReal h_g
  · have h_lt : ∀ x : IntervalPoint, L < (x : ℝ) → (x : ℝ) < L + ε → (f.1 x : ℝ) < (g.1 x : ℝ) :=
      fun x hx₁ hx₂ ↦ by nlinarith [hε x hx₁ hx₂]
    obtain ⟨x, hx⟩ :
      ∃ x : IntervalPoint, L < (x : ℝ) ∧ (x : ℝ) < L + ε ∧ (f.1 x : ℝ) < (g.1 x : ℝ) := by
      obtain ⟨x, hx₁, hx₂⟩ := hL.2.2 ε hε_pos
      grind
    obtain ⟨y, hy₁, hy₂⟩ := h_inf x hx.2.2
    grind
  · have h_gt : slopeToReal h_f > slopeToReal h_g :=
      lt_of_le_of_ne (le_of_not_gt h_cases) (Ne.symm <| by simpa [Units.ext_iff] using h_neq)
    obtain ⟨x, hx₁, hx₂⟩ :
      ∃ x : IntervalPoint, L < (x : ℝ) ∧ (x : ℝ) < L + ε ∧ (g.1 x : ℝ) < (f.1 x : ℝ) := by
      obtain ⟨x, hx₁, hx₂⟩ : ∃ x : ℝ, L < x ∧ x < L + ε ∧ x ∈ Set.Icc 0 1 := by
        by_cases hL1 : L = 1
        · obtain ⟨x, hx₁, hx₂⟩ := hL.2.2 1 zero_lt_one
          have := hL.2.1 x hx₁
          norm_num [hL1] at this
          refine False.elim <| hx₁ <| ?_
          rw [show x = ⟨1, by norm_num⟩ from Subtype.ext <| le_antisymm (by linarith [x.2.2]) this]
          simp [IntervalAut.map_one]
        · by_cases hL2 : L + ε > 1
          · exact ⟨1, lt_of_le_of_ne hL.1.2 hL1, hL2, by norm_num⟩
          · exact ⟨L + ε / 2, by linarith, by linarith,
              ⟨by linarith [hL.1.1], by linarith [hL.1.2]⟩⟩
      exact ⟨⟨x, hx₂.2⟩, hx₁, hx₂.1, by nlinarith [hε ⟨x, hx₂.2⟩ hx₁ hx₂.1]⟩
    obtain ⟨y, hy₁, hy₂⟩ := h_inf_rev x hx₂.2
    have := hL.2.1 y (by linarith)
    by_cases hy₃ : y.val = L
    · grind
    · have := hε y (lt_of_le_of_ne this (Ne.symm hy₃)) (by linarith)
      nlinarith [show (y : ℝ) > L from lt_of_le_of_ne ‹_› (Ne.symm hy₃)]

/-- Evaluate the conjugation equivalence pointwise on `[0,1]`. -/
lemma conjMulEquiv_val_apply (f : DlabGroup witnessH) (x : IntervalPoint) :
    (conjMulEquiv f).1 x = conjAut⁻¹ (f.1 (conjAut x)) :=
  rfl

/-- The first-disagreement order is preserved by `conjMulEquiv`. -/
lemma fd_lt_conj_iff (f g : DlabGroup witnessH) :
    fd_lt f g ↔ fd_lt (conjMulEquiv f) (conjMulEquiv g) := by
  constructor <;> rintro ⟨x, hx₁, hx₂⟩
  · refine ⟨conjAut⁻¹ x, ?_, ?_⟩
    · simpa [conjMulEquiv_val_apply] using conjAut⁻¹.strictMono hx₁
    · intro y hy
      simpa using conjAut⁻¹.strictMono <| hx₂ (conjAut y) <|
        conjAut⁻¹.strictMono.lt_iff_lt.mp <| by simpa [conjMulEquiv_val_apply] using hy
  · refine ⟨conjAut x, ?_, ?_⟩
    · simpa [conjMulEquiv_val_apply] using conjAut.strictMono hx₁
    · intro y hy
      have hgf : ((conjMulEquiv g).1 (conjAut⁻¹ y) : ℝ) <
          (conjMulEquiv f).1 (conjAut⁻¹ y) := by
        simpa [conjMulEquiv_val_apply] using conjAut⁻¹.strictMono hy
      simpa using conjAut.strictMono (hx₂ (conjAut⁻¹ y) hgf)

/-- The first-disagreement strict order is left-translation invariant: if `fd_lt f g`,
then `fd_lt (c * f) (c * g)`. -/
lemma fd_lt_mul_left (c f g : DlabGroup witnessH) (hfg : fd_lt f g) : fd_lt (c * f) (c * g) := by
  obtain ⟨x, hx₁, hx₂⟩ := hfg
  refine ⟨x, by simpa using c.1.strictMono hx₁, fun y hy ↦ ?_⟩
  exact hx₂ y (c.1.strictMono.lt_iff_lt.mp (by simpa using hy))

/-- Left-translation invariance of `fd_lt` as an `iff`: `fd_lt f g ↔ fd_lt (c * f) (c * g)`. -/
lemma fd_lt_mul_left_iff (c f g : DlabGroup witnessH) : fd_lt f g ↔ fd_lt (c * f) (c * g) :=
  ⟨fd_lt_mul_left c f g, fun h ↦ by simpa [mul_assoc] using fd_lt_mul_left c⁻¹ (c * f) (c * g) h⟩

/-- The first-disagreement strict order is right-translation invariant: if `fd_lt f g`,
then `fd_lt (f * c) (g * c)`. -/
lemma fd_lt_mul_right (c f g : DlabGroup witnessH) (hfg : fd_lt f g) : fd_lt (f * c) (g * c) := by
  obtain ⟨x, hx₁, hx₂⟩ := hfg
  exact ⟨c.1⁻¹ x, by simpa using hx₁,
    fun y hy ↦ by simpa using c.1⁻¹.strictMono (hx₂ (c.1 y) (by simpa using hy))⟩

/-- Right-translation invariance of `fd_lt` as an `iff`: `fd_lt f g ↔ fd_lt (f * c) (g * c)`. -/
lemma fd_lt_mul_right_iff (c f g : DlabGroup witnessH) : fd_lt f g ↔ fd_lt (f * c) (g * c) :=
  ⟨fd_lt_mul_right c f g, fun h ↦ by simpa [mul_assoc] using fd_lt_mul_right c⁻¹ (f * c) (g * c) h⟩

/-- An explicit linear order on the rank-one Dlab group via first disagreement. -/
noncomputable def witnessLinearOrder : LinearOrder (DlabGroup witnessH) := by
  have : Std.Trichotomous (r := fd_lt) :=
    ⟨fun a b h₁ h₂ ↦ (fd_lt_trichotomy a b).resolve_right fun h ↦ h.elim h₁ h₂⟩
  have : Std.Irrefl (α := DlabGroup witnessH) fd_lt := ⟨fd_lt_irrefl⟩
  have : IsTrans (DlabGroup witnessH) fd_lt := ⟨@fd_lt_trans⟩
  have : DecidableRel (α := DlabGroup witnessH) fd_lt := Classical.decRel _
  have : IsStrictTotalOrder (DlabGroup witnessH) fd_lt := {}
  exact linearOrderOfSTO fd_lt

/-- The local first-disagreement order on the witness group. -/
noncomputable local instance : LinearOrder (DlabGroup witnessH) :=
  witnessLinearOrder

/-- The linear order agrees with `fd_lt` on `≤`. -/
lemma witnessLinearOrder_le_iff (a b : DlabGroup witnessH) :
    @LE.le _ witnessLinearOrder.toLE a b ↔ (a = b ∨ fd_lt a b) := Eq.to_iff rfl

/-- The rank-one relation is the general first-disagreement relation. -/
lemma fd_lt_iff_firstDisagreement (a b : DlabGroup witnessH) :
    fd_lt a b ↔ FirstDisagreementLt witnessH a b := Iff.rfl

/-- The linear order agrees with `fd_lt` on `<`. -/
lemma witnessLinearOrder_lt_iff (a b : DlabGroup witnessH) :
    @LT.lt _ witnessLinearOrder.toLT a b ↔ fd_lt a b := Eq.to_iff rfl

/-- A linear order on a group is bi-invariant if multiplication on both sides preserves
the order. -/
structure IsBiInvariantLinearOrder (G : Type*) [Group G] (o : LinearOrder G) : Prop where
  /-- Left multiplication preserves the order. -/
  le_mul_left : ∀ a b c : G, @LE.le _ o.toLE a b → @LE.le _ o.toLE (c * a) (c * b)
  /-- Right multiplication preserves the order. -/
  le_mul_right : ∀ a b c : G, @LE.le _ o.toLE a b → @LE.le _ o.toLE (a * c) (b * c)

/-- A Dlab bi-order is the first-disagreement Dlab order, compatible with multiplication
on both sides. -/
structure IsDlabBiOrder (H : Subgroup PositiveSlopeGroup) (o : LinearOrder (DlabGroup H)) :
    Prop extends IsBiInvariantLinearOrder (DlabGroup H) o where
  /-- The strict order is the first-disagreement relation. -/
  lt_iff_firstDisagreement : ∀ a b : DlabGroup H, @LT.lt _ o.toLT a b ↔ FirstDisagreementLt H a b

/-- The first-disagreement order is a bi-order on the rank-one Dlab group. -/
theorem witnessLinearOrder_isDlabBiOrder : IsDlabBiOrder witnessH witnessLinearOrder where
  le_mul_left a b c hab := by
    rw [witnessLinearOrder_le_iff] at hab ⊢
    exact hab.imp (congrArg (c * ·)) (fd_lt_mul_left c a b)
  le_mul_right a b c hab := by
    rw [witnessLinearOrder_le_iff] at hab ⊢
    exact hab.imp (congrArg (· * c)) (fd_lt_mul_right c a b)
  lt_iff_firstDisagreement := fun a b ↦
    (witnessLinearOrder_lt_iff a b).trans (fd_lt_iff_firstDisagreement a b)

/-- The order automorphism induced by conjugation with `conjAut`. -/
noncomputable def witnessOrderAut : DlabGroup witnessH ≃*o DlabGroup witnessH where
  toMulEquiv := conjMulEquiv
  map_le_map_iff' := by
    intro a b
    simpa only [witnessLinearOrder_le_iff] using
      or_congr conjMulEquiv.injective.eq_iff (fd_lt_conj_iff a b).symm

/-- The explicit ordered Dlab witness has a non-inner order automorphism. -/
theorem witnessOrderAut_not_inner :
    witnessOrderAut.toMulEquiv ∉ MulAut.innerSubgroup (DlabGroup witnessH) :=
  conjMulEquiv_not_inner

/-- The rank-one conjugating interval automorphism. -/
noncomputable def rankOneConjAut : IntervalAut := conjAut

/-- The rank-one Dlab group automorphism induced by the conjugating PL map. -/
noncomputable def rankOneConjMulEquiv :
    DlabGroup rankOneSlopeGroup ≃* DlabGroup rankOneSlopeGroup :=
  conjMulEquiv

/-- The first-disagreement Dlab order used by the rank-one witness. -/
noncomputable def rankOneDlabOrder : LinearOrder (DlabGroup rankOneSlopeGroup) :=
  witnessLinearOrder

/-- The local rank-one Dlab order. -/
noncomputable local instance : LinearOrder (DlabGroup rankOneSlopeGroup) :=
  rankOneDlabOrder

/-- The rank-one Dlab order is compatible with multiplication on both sides. -/
theorem rankOneDlabOrder_isDlabBiOrder : IsDlabBiOrder rankOneSlopeGroup rankOneDlabOrder :=
  witnessLinearOrder_isDlabBiOrder

/-- The order automorphism of the rank-one Dlab group induced by the conjugating PL map. -/
noncomputable def rankOneConjOrderAut :
    DlabGroup rankOneSlopeGroup ≃*o DlabGroup rankOneSlopeGroup :=
  witnessOrderAut

/-- The rank-one conjugation order automorphism is not inner. -/
theorem rankOneConjOrderAut_not_inner :
    rankOneConjOrderAut.toMulEquiv ∉ MulAut.innerSubgroup (DlabGroup rankOneSlopeGroup) :=
  witnessOrderAut_not_inner

/-- A group has a bi-invariant linear order with a non-inner order automorphism. -/
def HasNonInnerOrderAutomorphism (G : Type*) [Group G] : Prop :=
  ∃ o : LinearOrder G, IsBiInvariantLinearOrder G o ∧
    let _ : LinearOrder G := o
    ∃ φ : G ≃*o G, φ.toMulEquiv ∉ MulAut.innerSubgroup G

/-- The compact interval rank-one witness satisfies the generic ordered-group target. -/
theorem rankOneCompactInterval_hasOrderAutNotInner :
    HasNonInnerOrderAutomorphism (DlabGroup rankOneSlopeGroup) :=
  ⟨rankOneDlabOrder, rankOneDlabOrder_isDlabBiOrder.toIsBiInvariantLinearOrder, rankOneConjOrderAut,
    rankOneConjOrderAut_not_inner⟩

/-- **Kourovka 21.149 (original formulation)**: there exists a Dlab group with an order
automorphism that is not inner. -/
theorem _root_.kourovka_21_149 :
    ∃ H : Subgroup PositiveSlopeGroup, ∃ o : LinearOrder (DlabGroup H), IsDlabBiOrder H o ∧
      let _ : LinearOrder (DlabGroup H) := o
      ∃ φ : DlabGroup H ≃*o DlabGroup H, φ.toMulEquiv ∉ MulAut.innerSubgroup (DlabGroup H) :=
  ⟨rankOneSlopeGroup, rankOneDlabOrder, rankOneDlabOrder_isDlabBiOrder, rankOneConjOrderAut,
    rankOneConjOrderAut_not_inner⟩

end Solution21_149
end KourovkaNotebook

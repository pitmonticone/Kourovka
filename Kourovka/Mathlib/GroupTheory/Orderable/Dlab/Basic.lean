/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone, Daniel Morrison
-/

import Mathlib.Algebra.Order.Group.End
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UnitInterval

/-!
# Dlab groups on the unit interval

For a subgroup `H` of the positive real numbers, this file defines Dlab's group of locally right
`H`-linear order automorphisms of the unit interval whose support is bounded away from both
endpoints.

The paper also studies variants obtained by dropping one or both endpoint conditions. `DlabGroup`
denotes the variant that is the identity near both endpoints.

## Main definitions

* `Dlab.IsLocallyRightHLinear`: the local right-affinity condition with slopes in `H`.
* `Dlab.IsElement`: the predicate defining the compact-support interval Dlab group.
* `Dlab.subgroup`: the Dlab group as a subgroup of the order automorphisms of `[0, 1]`.
* `DlabGroup`: the corresponding bundled group type.

## Implementation notes

The positive real numbers are represented by the units `NNRealˣ`. Multiplication of interval order
automorphisms uses mathlib's standard relation-isomorphism convention, `(f * g) x = f (g x)`.

## References

* [V. Dlab, *On a Family of Simple Ordered Groups*](https://doi.org/10.1017/S1446788700006261)
-/

open scoped unitInterval Topology

namespace Dlab

/-- The order automorphisms of the closed unit interval. -/
abbrev IntervalAut := unitInterval ≃o unitInterval

/-- Coerce a positive real unit to a real number. -/
abbrev slopeToReal (h : NNRealˣ) : ℝ := ((h : NNReal) : ℝ)

/-- An interval automorphism is *locally right `H`-linear* if its germ to the right of each point
other than `1` is affine with slope in `H`. -/
def IsLocallyRightHLinear (H : Subgroup NNRealˣ) (f : IntervalAut) : Prop :=
  ∀ a : unitInterval, a < 1 → ∃ ε : ℝ, 0 < ε ∧ ∃ h : H, ∀ ⦃x : unitInterval⦄,
    (a : ℝ) < x → (x : ℝ) < (a : ℝ) + ε →
    (f x : ℝ) = (f a : ℝ) + slopeToReal h.1 * ((x : ℝ) - (a : ℝ))

/-- `f` is the identity on some neighborhood of `0`. -/
def IsIdentityNearZero (f : IntervalAut) : Prop :=
  f =ᶠ[𝓝 (0 : unitInterval)] id

/-- `f` is the identity on some neighborhood of `1`. -/
def IsIdentityNearOne (f : IntervalAut) : Prop :=
  f =ᶠ[𝓝 (1 : unitInterval)] id

/-- An interval automorphism is a Dlab element if it is locally right `H`-linear and is the
identity near both endpoints. -/
def IsElement (H : Subgroup NNRealˣ) (f : IntervalAut) : Prop :=
  IsLocallyRightHLinear H f ∧ IsIdentityNearZero f ∧ IsIdentityNearOne f

/-- Local right-linearity is monotone in the allowed slope subgroup. -/
theorem IsLocallyRightHLinear.mono {H K : Subgroup NNRealˣ} {f : IntervalAut}
    (hf : IsLocallyRightHLinear H f) (hHK : H ≤ K) : IsLocallyRightHLinear K f := by
  intro a ha
  obtain ⟨ε, hε, h, hh⟩ := hf a ha
  exact ⟨ε, hε, ⟨h, hHK h.2⟩, hh⟩

/-- The Dlab-element predicate is monotone in the allowed slope subgroup. -/
theorem IsElement.mono {H K : Subgroup NNRealˣ} {f : IntervalAut} (hf : IsElement H f)
    (hHK : H ≤ K) : IsElement K f :=
  ⟨hf.1.mono hHK, hf.2⟩

/-- The identity is a Dlab element for every slope subgroup. -/
theorem isElement_one (H : Subgroup NNRealˣ) : IsElement H (1 : IntervalAut) :=
  ⟨fun a _ ↦ ⟨1, zero_lt_one, 1, fun _ _ ↦ by norm_num [slopeToReal]⟩,
    by simp [IsIdentityNearZero], by simp [IsIdentityNearOne]⟩

/-- Composition preserves local right `H`-linearity. -/
theorem isLocallyRightHLinear_mul {H : Subgroup NNRealˣ} {f g : IntervalAut}
    (hf : IsLocallyRightHLinear H f) (hg : IsLocallyRightHLinear H g) :
    IsLocallyRightHLinear H (f * g) := by
  intro a ha
  obtain ⟨ε₁, hε₁, h₁, hh₁⟩ := hg a ha
  obtain ⟨ε₂, hε₂, h₂, hh₂⟩ := hf (g a) (by
    simpa only [show g 1 = 1 from g.map_top] using g.strictMono ha)
  have h₁_pos : 0 < slopeToReal h₁ := by simp [slopeToReal]
  refine ⟨min ε₁ (ε₂ / slopeToReal h₁), lt_min hε₁ (div_pos hε₂ h₁_pos), h₂ * h₁,
    fun x hx₁ hx₂ ↦ ?_⟩
  have hg_eq := hh₁ hx₁ (by linarith [min_le_left ε₁ (ε₂ / slopeToReal h₁)])
  have hf_eq :=
    hh₂ (g.strictMono hx₁) (by
      nlinarith [min_le_right ε₁ (ε₂ / slopeToReal h₁),
        mul_div_cancel₀ ε₂ (ne_of_gt h₁_pos)])
  simp only [RelIso.mul_apply, slopeToReal, Subgroup.coe_mul, Units.val_mul, NNReal.coe_mul,
    hg_eq, hf_eq]
  ring

/-- The product of two Dlab elements is a Dlab element. -/
theorem isElement_mul {H : Subgroup NNRealˣ} {f g : IntervalAut}
    (hf : IsElement H f) (hg : IsElement H g) : IsElement H (f * g) := by
  refine ⟨isLocallyRightHLinear_mul hf.1 hg.1, ?_, ?_⟩
  · filter_upwards [hf.2.1, hg.2.1] with x hfx hgx
    simp only [RelIso.mul_apply, id_eq, hgx, hfx]
  · filter_upwards [hf.2.2, hg.2.2] with x hfx hgx
    simp only [RelIso.mul_apply, id_eq, hgx, hfx]

/-- Inversion preserves local right `H`-linearity. -/
theorem isLocallyRightHLinear_inv {H : Subgroup NNRealˣ} {f : IntervalAut}
    (hf : IsLocallyRightHLinear H f) : IsLocallyRightHLinear H f⁻¹ := by
  intro a ha
  obtain ⟨ε, hε_pos, h, hh⟩ := hf (f⁻¹ a) (by
    simpa only [show f⁻¹ 1 = 1 from f⁻¹.map_top] using f⁻¹.strictMono ha)
  obtain ⟨hε', hε'_pos, hε'_eq⟩ : ∃ ε' > 0, ∀ x : unitInterval, (a : ℝ) < x →
      (x : ℝ) < (a : ℝ) + ε' → (f⁻¹ x : ℝ) < (f⁻¹ a : ℝ) + ε := by
    have hcont : Continuous fun x : unitInterval ↦ (f⁻¹ x : ℝ) := by continuity
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuous_iff.mp hcont a ε hε_pos
    refine ⟨δ, hδ_pos, fun x hx₁ hx₂ ↦ ?_⟩
    have hout := hδ x (by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx₁.le)]
      exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hx₂))
    rw [Real.dist_eq] at hout
    simpa [add_comm] using (sub_lt_iff_lt_add.mp (abs_lt.mp hout).2)
  refine ⟨hε', hε'_pos, h⁻¹, fun x hx₁ hx₂ ↦ ?_⟩
  have hfx := hh (f⁻¹.strictMono hx₁) (hε'_eq x hx₁ hx₂)
  simp_all [slopeToReal]

/-- Being the identity near `0` is preserved by inversion. -/
theorem isIdentityNearZero_inv {f : IntervalAut} (hf : IsIdentityNearZero f) :
    IsIdentityNearZero f⁻¹ := by
  filter_upwards [hf] with x hx
  change f.symm x = x
  simpa only [OrderIso.symm_apply_eq, id_eq] using hx.symm

/-- Being the identity near `1` is preserved by inversion. -/
theorem isIdentityNearOne_inv {f : IntervalAut} (hf : IsIdentityNearOne f) :
    IsIdentityNearOne f⁻¹ := by
  filter_upwards [hf] with x hx
  change f.symm x = x
  simpa only [OrderIso.symm_apply_eq, id_eq] using hx.symm

/-- The inverse of a Dlab element is a Dlab element. -/
theorem isElement_inv {H : Subgroup NNRealˣ} {f : IntervalAut} (hf : IsElement H f) :
    IsElement H f⁻¹ :=
  ⟨isLocallyRightHLinear_inv hf.1, isIdentityNearZero_inv hf.2.1, isIdentityNearOne_inv hf.2.2⟩

/-- Dlab's compact-support interval group with slopes in `H`, as a subgroup of the order
automorphisms of `[0, 1]`. -/
def subgroup (H : Subgroup NNRealˣ) : Subgroup IntervalAut where
  carrier := {f | IsElement H f}
  one_mem' := isElement_one H
  mul_mem' := isElement_mul
  inv_mem' := isElement_inv

/-- Membership in `subgroup H` is the Dlab-element predicate for `H`. -/
@[simp]
theorem mem_subgroup {H : Subgroup NNRealˣ} {f : IntervalAut} :
    f ∈ subgroup H ↔ IsElement H f := Iff.rfl

/-- The Dlab subgroup is monotone in the allowed slope subgroup. -/
theorem subgroup_mono : Monotone subgroup :=
  fun _ _ hHK _ hf ↦ hf.mono hHK

end Dlab

/-- Dlab's compact-support interval group with slopes in `H`, as a bundled group type. -/
abbrev DlabGroup (H : Subgroup NNRealˣ) := ↥(Dlab.subgroup H)

/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.PointStabilizerParametrization

/-!
# Order-twelve point-stabilizer count for `PSU(3,3)`

This file isolates the order-twelve condition in the point-stabilizer
parametrization and counts the corresponding parameters.
-/

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

section PointStabilizerCounts

-- The finite-field parametrization proofs below expand deeply nested triples.
set_option maxRecDepth 1000000

/-! ## Problem-specific point-stabilizer counts for `PSU(3,3)` -/

/-! ### The matrix action of a stabilizer element on the Hermitian frame -/

/-- The coordinate action of `toLinearEquiv g` on a vector written in the
Hermitian frame. -/
lemma param_M_action (g : specialUnitaryGroup) (μ a c : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (α β γ : F9) :
    toLinearEquiv g (α • fv0 + β • fv1 + γ • fw) =
      (α * μ + β * a + γ * (-(c ^ 3) * μ ^ 3)) • fv0 +
      (β * (μ ^ 3)⁻¹) • fv1 + (β * c + γ * μ ^ 2) • fw := by
  simp [e0, e1, e2, add_smul, smul_add, smul_smul]
  module

/-- The image of `fv0` under the `n`-th power scales by `μ ^ n`. -/
lemma param_pow_fv0 (g : specialUnitaryGroup) (μ : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0) :
    ∀ n : ℕ, toLinearEquiv (g ^ n) fv0 = (μ ^ n) • fv0 := by
  intro n
  induction n with
  | zero => simp +decide [toLinearEquiv_one]
  | succ n ih =>
    simp +decide [pow_succ', toLinearEquiv_mul_apply, ih, e0, smul_smul, mul_comm]

/-- A special-unitary element fixing the whole Hermitian frame is the identity. -/
lemma su_eq_one_of_frame_fix (h : specialUnitaryGroup)
    (h0 : toLinearEquiv h fv0 = fv0) (h1 : toLinearEquiv h fv1 = fv1)
    (h2 : toLinearEquiv h fw = fw) :
    h = 1 := by
  rw [← toLinearEquiv_eq_refl_iff_one]
  ext x
  obtain ⟨a, b, c, rfl⟩ := frame_coords x
  simp only [map_add, map_smul, h0, h1, h2, LinearEquiv.refl_apply]

/-- The abbreviation `q₄` for the off-diagonal coefficient of `g ^ 4` on `fv1`. -/
noncomputable def q_four (μ a c : F9) : F9 := μ ^ 3 * (a - c ^ 4 * (1 + μ))

/-- The fourth power fixes `fv0` when `μ ^ 2 = -1`. -/
lemma param_g4_fv0 (g : specialUnitaryGroup) (μ : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (hμ2 : μ ^ 2 = -1) :
    toLinearEquiv (g ^ 4) fv0 = fv0 := by
  rw [param_pow_fv0 g μ e0 4, show μ ^ 4 = 1 by linear_combination' hμ2 * hμ2, one_smul]

/-- The fourth power fixes `fw` when `μ ^ 2 = -1`. -/
lemma param_g4_fw (g : specialUnitaryGroup) (μ c : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ2 : μ ^ 2 = -1) :
    toLinearEquiv (g ^ 4) fw = fw := by
  rw [show g ^ 4 = g * (g * (g * g)) by simp +decide [pow_succ, mul_assoc]]
  simp_all +decide [pow_succ, mul_assoc, toLinearEquiv_mul_apply]
  simp_all +decide [smul_smul, mul_assoc]
  abel1

/-- The fourth power acts on `fv1` as a transvection when `μ ^ 2 = -1`. -/
lemma param_g4_fv1 (g : specialUnitaryGroup) (μ a c : F9) (hμ0 : μ ≠ 0)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ2 : μ ^ 2 = -1) :
    toLinearEquiv (g ^ 4) fv1 = fv1 + q_four μ a c • fv0 := by
  unfold q_four
  rw [show toLinearEquiv (g ^ 4) fv1 =
      toLinearEquiv g (toLinearEquiv g (toLinearEquiv g (toLinearEquiv g fv1))) by
    convert toLinearEquiv_mul_apply g (g * (g * g)) fv1 using 1,
    e1, param_M_action g μ a c e0 e1 e2, param_M_action g μ a c e0 e1 e2,
    param_M_action g μ a c e0 e1 e2]
  rw [show μ ^ 3 = μ * μ ^ 2 by ring_nf, hμ2]
  ring_nf
  rw [show μ⁻¹ ^ 4 = (μ⁻¹ ^ 2) ^ 2 by ring_nf,
    show μ⁻¹ ^ 3 = μ⁻¹ * μ⁻¹ ^ 2 by ring_nf,
    show μ⁻¹ ^ 2 = (μ ^ 2)⁻¹ by group]
  norm_num [hμ2, hμ0]
  ring_nf
  grobner

/-- The twelfth power is the identity (when `μ² = -1`). -/
lemma param_g12 (g : specialUnitaryGroup) (μ a c : F9) (hμ0 : μ ≠ 0)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ2 : μ ^ 2 = -1) :
    g ^ 12 = 1 := by
  apply su_eq_one_of_frame_fix
  · rw [show g ^ 12 = g ^ 4 * g ^ 4 * g ^ 4 by group,
      toLinearEquiv_mul_apply, toLinearEquiv_mul_apply]
    norm_num [param_g4_fv0 g μ e0 hμ2]
  · have h_g4 : toLinearEquiv (g ^ 4) fv1 = fv1 + q_four μ a c • fv0 :=
      param_g4_fv1 g μ a c hμ0 e0 e1 e2 hμ2
    have h_g12 : toLinearEquiv (g ^ 12) fv1 = fv1 + (3 • q_four μ a c) • fv0 := by
      convert congr_arg
        (fun x => toLinearEquiv (g ^ 4)
          (toLinearEquiv (g ^ 4) (toLinearEquiv (g ^ 4) fv1)))
        h_g4 using 1
      rw [h_g4, map_add, map_smul, map_add, map_smul]
      norm_num [h_g4, param_g4_fv0 g μ e0 hμ2]
      ring_nf
      ext i
      norm_num [mul_comm]
      ring
    simpa +decide [show (3 : F9) = 0 from three_eq_zero] using h_g12
  · rw [show g ^ 12 = g ^ 4 * g ^ 4 * g ^ 4 by group,
      toLinearEquiv_mul_apply, toLinearEquiv_mul_apply, param_g4_fw g μ c e0 e2 hμ2]
    norm_num [param_g4_fw g μ c e0 e2 hμ2]

/-- The fourth power is trivial iff `q₄ = 0` (when `μ² = -1`). -/
lemma param_g4_eq_one_iff (g : specialUnitaryGroup) (μ a c : F9) (hμ0 : μ ≠ 0)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ2 : μ ^ 2 = -1) :
    g ^ 4 = 1 ↔ q_four μ a c = 0 := by
  constructor <;> intro h
  · have h_g4_fv1 := congr_arg (fun x => x - fv1) <|
      param_g4_fv1 g μ a c hμ0 e0 e1 e2 hμ2
    simp_all +decide
    exact smul_eq_zero.mp h_g4_fv1.symm |> Or.resolve_right <| by simpa using fv0_ne
  · exact su_eq_one_of_frame_fix (g ^ 4) (param_g4_fv0 g μ e0 hμ2)
      (by simpa [h] using param_g4_fv1 g μ a c hμ0 e0 e1 e2 hμ2)
      (param_g4_fw g μ c e0 e2 hμ2)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The sixth power is nontrivial (when `μ² = -1`), since it negates `fv0`. -/
lemma param_g6_ne (g : specialUnitaryGroup) (μ : F9)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (hμ2 : μ ^ 2 = -1) :
    g ^ 6 ≠ 1 := by
  intro h
  have hμ6 : μ ^ 6 = 1 := smul_left_injective _ fv0_ne <| by
    change μ ^ 6 • fv0 = (1 : F9) • fv0
    rw [← param_pow_fv0 g μ e0 6, h]
    simp +decide [toLinearEquiv_one]
  rw [show μ ^ 6 = (μ ^ 2) ^ 3 by ring, hμ2] at hμ6
  norm_num at hμ6
  exact one_ne_negone_F9 hμ6.symm

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The sixth power is trivial when `μ² = 1`. -/
lemma param_g6_eq_one_of_sq_one (g : specialUnitaryGroup) (μ a c : F9) (hμ0 : μ ≠ 0)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw)
    (hμ1 : μ ^ 2 = 1) :
    g ^ 6 = 1 := by
  apply su_eq_one_of_frame_fix
  · rw [param_pow_fv0 g μ e0 6, show μ ^ 6 = (μ ^ 2) ^ 3 by ring, hμ1]
    norm_num
  · have h6 : g ^ 6 = g * (g * (g * (g * (g * g)))) := by
      rw [pow_succ', pow_succ', pow_succ', pow_succ', pow_succ', pow_one]
    simp_all +decide [toLinearEquiv_mul_apply]
    rcases hμ1 with (rfl | rfl) <;> norm_num [pow_succ, mul_assoc, mul_left_comm] at *
    · ext i
      fin_cases i <;> simp +decide <;> ring_nf <;> grind
    · ext i
      fin_cases i <;> simp +decide <;> ring_nf! <;> grind
  · simp +decide [*, pow_succ, mul_assoc, toLinearEquiv_mul_apply]
    simp_all +decide [pow_succ, mul_assoc, smul_smul]
    rw [show μ = μ⁻¹ from eq_inv_of_mul_eq_one_left hμ1]
    ring_nf
    simp +decide
    rw [show (fv0 * 3 : Fin 3 → F9) = 0 by
      ext i
      fin_cases i <;> simp +decide [show (3 : F9) = 0 from three_eq_zero]]
    norm_num

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The field identity characterizing `q₄ = 0` via the cubic constraint (when `μ² = -1`). -/
lemma q_four_zero_iff (μ a c : F9) (hμ0 : μ ≠ 0) (hμ2 : μ ^ 2 = -1)
    (hcon : a ^ 3 + μ ^ 2 * a + c ^ 4 * μ ^ 3 = 0) :
    q_four μ a c = 0 ↔ (a = 0 ∨ a ^ 2 = -μ) := by
  by_cases ha : a = 0 <;> simp_all +decide [q_four]
  grind +locals

/-! ### Private finite-field enumeration model for the stabilizer counts -/

/-- There is a square root of `-1` in `F9`. -/
lemma exists_square_root_neg_one_f9 : ∃ x : F9, x ^ 2 = -1 := by
  obtain ⟨s, hs, _hs0⟩ := exists_fourth_root (-1 : F9) (Or.inr rfl)
  exact ⟨s ^ 2, by rw [← pow_mul, hs]⟩

/-- A fixed square root of `-1` in `F9`. -/
noncomputable def i_f9 : F9 :=
  exists_square_root_neg_one_f9.choose

/-- The chosen square root of `-1` squares to `-1`. -/
lemma i_f9_sq : i_f9 ^ 2 = -1 := exists_square_root_neg_one_f9.choose_spec

/-- The canonical ring homomorphism from `ZMod 3` to `F9`. -/
noncomputable def zmod_cast_to_f9 : ZMod 3 →+* F9 :=
  ZMod.castHom (dvd_refl 3) F9

/-- The two-coordinate model of `F9` over `ZMod 3`. -/
abbrev f9_pair :=
  ZMod 3 × ZMod 3

/-- Multiplication in the two-coordinate model of `F9`. -/
def f9_pair_mul (p q : f9_pair) : f9_pair :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- Interpret a coordinate pair as an element of `F9`. -/
noncomputable def to_f9 (p : f9_pair) : F9 :=
  zmod_cast_to_f9 p.1 + zmod_cast_to_f9 p.2 * i_f9

/-- The pair `(0, 0)` interprets as `0` in `F9`. -/
@[simp] lemma to_f9_zero : to_f9 (0, 0) = 0 := by simp [to_f9]

/-- The pair `(1, 0)` interprets as `1` in `F9`. -/
@[simp] lemma to_f9_one : to_f9 (1, 0) = 1 := by simp [to_f9]

/-- The interpretation map is additive. -/
lemma to_f9_add (p q : f9_pair) : to_f9 (p + q) = to_f9 p + to_f9 q := by
  simp only [to_f9, Prod.fst_add, Prod.snd_add, map_add]
  ring

/-- The interpretation map preserves negation. -/
lemma to_f9_neg (p : f9_pair) : to_f9 (-p) = -to_f9 p := by
  simp only [to_f9, Prod.fst_neg, Prod.snd_neg, map_neg]
  ring

/-- The interpretation map turns the coordinate-pair product into multiplication in `F9`. -/
lemma to_f9_mul (p q : f9_pair) :
    to_f9 (f9_pair_mul p q) = to_f9 p * to_f9 q := by
  simp only [to_f9, f9_pair_mul, map_add, map_sub, map_mul]
  linear_combination (-(zmod_cast_to_f9 p.2 * zmod_cast_to_f9 q.2)) * i_f9_sq

/-- The interpretation map is injective. -/
lemma to_f9_injective : Function.Injective to_f9 := by
  intros p q h_eq
  have h_aux :
      ∀ x y : ZMod 3, zmod_cast_to_f9 x + zmod_cast_to_f9 y * i_f9 = 0 →
      x = 0 ∧ y = 0 := by
    intros x y h_eq
    by_cases hy : y = 0
    · fin_cases x <;> simp_all +decide
    · have h_i_f9_range : i_f9 = -zmod_cast_to_f9 (x / y) := by
        have h_i_f9_range : i_f9 = -zmod_cast_to_f9 x / zmod_cast_to_f9 y := by
          rw [eq_div_iff] <;> norm_num [hy]
          linear_combination' h_eq
        simp_all +decide [div_eq_mul_inv]
      obtain ⟨z, hz⟩ : i_f9 ^ 2 ∈ Set.range zmod_cast_to_f9 :=
        ⟨(x / y) ^ 2, by simp +decide [h_i_f9_range, map_pow]⟩
      have := i_f9_sq
      simp_all +decide
      fin_cases x <;> fin_cases y <;> simp +decide at hy this ⊢
      all_goals try grind
      · erw [show (zmod_cast_to_f9 2 : F9) = 2 by rfl] at this
        norm_num at this
        grind
      · erw [show (zmod_cast_to_f9 2 : F9) = 2 by rfl] at this
        simp_all +decide
        grind
  have h := h_aux (p.1 - q.1) (p.2 - q.2) <| by
    unfold to_f9 at h_eq
    rw [map_sub, map_sub]
    linear_combination' h_eq
  exact Prod.ext (sub_eq_zero.mp h.1) (sub_eq_zero.mp h.2)

/-- The interpretation map is bijective. -/
lemma to_f9_bijective : Function.Bijective to_f9 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨to_f9_injective, ?_⟩
  simp only [card_f9]
  decide

/-- The coordinate-pair equivalence with `F9`. -/
noncomputable def f9_pair_equiv : f9_pair ≃ F9 :=
  Equiv.ofBijective to_f9 to_f9_bijective

/-- The coordinate-pair equivalence acts by interpretation. -/
@[simp] lemma f9_pair_equiv_apply (p : f9_pair) : f9_pair_equiv p = to_f9 p := rfl

/-- The componentwise equivalence between coordinate-pair triples and `F9` triples. -/
noncomputable def f9_pair_triple_equiv :
    f9_pair × f9_pair × f9_pair ≃ F9 × F9 × F9 :=
  f9_pair_equiv.prodCongr (f9_pair_equiv.prodCongr f9_pair_equiv)

/-- The triple equivalence acts componentwise by interpretation. -/
@[simp] lemma f9_pair_triple_equiv_apply (t : f9_pair × f9_pair × f9_pair) :
    f9_pair_triple_equiv t = (to_f9 t.1, to_f9 t.2.1, to_f9 t.2.2) := rfl

/-- The square of a coordinate pair. -/
def f9_pair_sq (p : f9_pair) : f9_pair :=
  f9_pair_mul p p

/-- The cube of a coordinate pair. -/
def f9_pair_cube (p : f9_pair) : f9_pair :=
  f9_pair_mul (f9_pair_sq p) p

/-- The fourth power of a coordinate pair. -/
def f9_pair_fourth (p : f9_pair) : f9_pair :=
  f9_pair_mul (f9_pair_sq p) (f9_pair_sq p)

/-- Interpretation commutes with squaring. -/
lemma to_f9_sq (p : f9_pair) : to_f9 (f9_pair_sq p) = to_f9 p ^ 2 := by
  rw [f9_pair_sq, to_f9_mul, sq]

/-- Interpretation commutes with cubing. -/
lemma to_f9_cube (p : f9_pair) : to_f9 (f9_pair_cube p) = to_f9 p ^ 3 := by
  rw [f9_pair_cube, to_f9_mul, to_f9_sq]
  ring

/-- Interpretation commutes with taking fourth powers. -/
lemma to_f9_fourth (p : f9_pair) : to_f9 (f9_pair_fourth p) = to_f9 p ^ 4 := by
  rw [f9_pair_fourth, to_f9_mul, to_f9_sq]
  ring

/-- The Borel-parameter constraint over `F9`. -/
def param_pred_f9 (t : F9 × F9 × F9) : Prop :=
  t.1 ≠ 0 ∧ t.2.1 ^ 3 + t.1 ^ 2 * t.2.1 + t.2.2 ^ 4 * t.1 ^ 3 = 0

/-- The Borel-parameter constraint in the computable coordinate-pair model. -/
def param_pred_model (t : f9_pair × f9_pair × f9_pair) : Prop :=
  t.1 ≠ (0, 0) ∧
    f9_pair_cube t.2.1 + f9_pair_mul (f9_pair_sq t.1) t.2.1 +
    f9_pair_mul (f9_pair_fourth t.2.2) (f9_pair_cube t.1) = (0, 0)

/-- The model parameter constraint is decidable. -/
instance : DecidablePred param_pred_model := fun t => by
  unfold param_pred_model
  infer_instance

/-- The model parameter constraint matches the `F9` constraint under the triple equivalence. -/
lemma param_pred_model_iff (t : f9_pair × f9_pair × f9_pair) :
    param_pred_model t ↔ param_pred_f9 (f9_pair_triple_equiv t) := by
  constructor <;> intro h <;>
    simp_all +decide [param_pred_model, param_pred_f9, f9_pair_triple_equiv_apply]
  · convert h using 1
    · rw [← to_f9_zero, to_f9_injective.eq_iff]
    · rw [← to_f9_zero, ← to_f9_injective.eq_iff]
      simp +decide [to_f9_cube, to_f9_sq, to_f9_fourth, to_f9_mul, to_f9_add]
  · refine ⟨?_, to_f9_injective ?_⟩
    · rintro h'
      simp_all +decide [to_f9]
    · simp +decide [*, to_f9_cube, to_f9_sq, to_f9_fourth, to_f9_add, to_f9_mul,
        to_f9_zero]

/-- The order-twelve refinement over the computable model. -/
def order_twelve_pred_model (t : f9_pair × f9_pair × f9_pair) : Prop :=
  param_pred_model t ∧ f9_pair_sq t.1 = ((-1 : ZMod 3), 0) ∧ t.2.1 ≠ (0, 0) ∧
    f9_pair_sq t.2.1 ≠ (-t.1.1, -t.1.2)

/-- The order-twelve model refinement is decidable. -/
instance : DecidablePred order_twelve_pred_model := fun t => by
  unfold order_twelve_pred_model
  infer_instance

/-- The order-six refinement over the computable model. -/
def order_six_pred_model (t : f9_pair × f9_pair × f9_pair) : Prop :=
  param_pred_model t ∧ t.1 = ((-1 : ZMod 3), 0) ∧ t.2.1 + f9_pair_fourth t.2.2 ≠ (0, 0)

/-- The order-six model refinement is decidable. -/
instance : DecidablePred order_six_pred_model := fun t => by
  unfold order_six_pred_model
  infer_instance

/-- A single finite enumeration over the computable-model triples, tallying the base
parameters and both order refinements. -/
noncomputable def modelCounts : ℕ × ℕ × ℕ :=
  ∑ t : f9_pair × f9_pair × f9_pair,
    (if param_pred_model t then 1 else 0,
      if order_twelve_pred_model t then 1 else 0,
      if order_six_pred_model t then 1 else 0)

/-- The enumerated tallies: `216` base parameters, `36` of order twelve, `18` of order six. -/
lemma modelCounts_eq : modelCounts = (216, 36, 18) := by
  unfold modelCounts
  decide

/-- There are `216` parameter triples in the computable model. -/
lemma card_param_model :
    Fintype.card {t : f9_pair × f9_pair × f9_pair // param_pred_model t} = 216 := by
  rw [Fintype.card_subtype, Finset.card_filter]
  simpa only [modelCounts, Prod.fst_sum] using congrArg Prod.fst modelCounts_eq

/-- There are `216` Borel-parameter triples over `F9`. -/
lemma card_param_f9 :
    Nat.card {t : F9 × F9 × F9 // param_pred_f9 t} = 216 := by
  rw [← Nat.card_congr (f9_pair_triple_equiv.subtypeEquiv param_pred_model_iff),
    Nat.card_eq_fintype_card, card_param_model]

/-! ### The order-twelve criterion -/

/-- The order-twelve refinement over `F9`. -/
def order_twelve_pred_f9 (t : F9 × F9 × F9) : Prop :=
  param_pred_f9 t ∧ t.1 ^ 2 = -1 ∧ t.2.1 ≠ 0 ∧ t.2.1 ^ 2 ≠ -t.1

/-- The order-twelve refinements agree under the triple equivalence. -/
lemma order_twelve_pred_iff (t : f9_pair × f9_pair × f9_pair) :
    order_twelve_pred_model t ↔ order_twelve_pred_f9 (f9_pair_triple_equiv t) := by
  constructor <;> intro h <;>
    simp_all +decide [order_twelve_pred_model, order_twelve_pred_f9, f9_pair_triple_equiv_apply]
  · refine ⟨param_pred_model_iff t |>.1 h.1, ?_, ?_, ?_⟩
    · rw [← to_f9_sq, h.2.1]
      simp +decide [to_f9]
    · exact fun h' => h.2.2.1 <| to_f9_injective <| by simp +decide [h']
    · rw [← to_f9_sq, ← to_f9_neg]
      exact fun h' => h.2.2.2 <| to_f9_injective <| by aesop
  · refine ⟨param_pred_model_iff t |>.2 h.1, ?_, ?_, ?_⟩
    · rw [← to_f9_injective.eq_iff]
      simp +decide [*, to_f9_sq]
      simp +decide [to_f9]
    · exact fun h' => h.2.2.1 <| by simp +decide [h', to_f9]
    · intro h_eq
      exact h.2.2.2 <| by
        rw [← to_f9_sq,
          congr_arg to_f9 (show f9_pair_sq t.2.1 = -t.1 by
            ext <;> simp +decide [h_eq]),
          to_f9_neg]

/-- There are `36` order-twelve triples in the computable model. -/
lemma card_order_twelve_model :
    Fintype.card {t : f9_pair × f9_pair × f9_pair // order_twelve_pred_model t} = 36 := by
  rw [Fintype.card_subtype, Finset.card_filter]
  simpa only [modelCounts, Prod.snd_sum, Prod.fst_sum] using
    congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) modelCounts_eq

/-- **The order-twelve parameter count.** -/
lemma card_order_twelve_f9 :
    Nat.card {t : F9 × F9 × F9 // order_twelve_pred_f9 t} = 36 := by
  rw [← Nat.card_congr (f9_pair_triple_equiv.subtypeEquiv order_twelve_pred_iff),
    Nat.card_eq_fintype_card, card_order_twelve_model]

/-- **Order-twelve criterion.** A stabilizer element of `p0` with Borel parameters
`(μ, a, c)` has order `12` iff `μ² = -1`, `a ≠ 0` and `a² ≠ -μ`. -/
lemma orderOf_twelve_iff_of_param (g : specialUnitaryGroup) (μ a c : F9) (hμ0 : μ ≠ 0)
    (hcon : a ^ 3 + μ ^ 2 * a + c ^ 4 * μ ^ 3 = 0)
    (e0 : toLinearEquiv g fv0 = μ • fv0)
    (e1 : toLinearEquiv g fv1 = a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw)
    (e2 : toLinearEquiv g fw = (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw) :
    orderOf g = 12 ↔ (μ ^ 2 = -1 ∧ a ≠ 0 ∧ a ^ 2 ≠ -μ) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hμ2 : μ ^ 2 = -1 := by
      have hμ12 : μ ^ 12 = 1 := by
        have h_mu12 := param_pow_fv0 g μ e0 12
        rw [← h, pow_orderOf_eq_one, toLinearEquiv_one] at h_mu12
        exact smul_left_injective _ fv0_ne <| by simpa [h] using h_mu12.symm
      have hμ8 : μ ^ 8 = 1 := by grobner
      have hμ4 : μ ^ 4 = 1 := by grind
      exact (eq_or_eq_neg_of_sq_eq_sq _ _ <| by linear_combination' hμ4).resolve_left fun h => by
        have := param_g6_eq_one_of_sq_one g μ a c hμ0 e0 e1 e2 h
        simp_all +decide [orderOf_eq_iff]
    have hqfour : q_four μ a c ≠ 0 := fun hqfour_zero =>
      absurd (orderOf_dvd_iff_pow_eq_one.mpr <|
        (param_g4_eq_one_iff g μ a c hμ0 e0 e1 e2 hμ2).mpr hqfour_zero) (by simp +decide [h])
    refine ⟨hμ2, ?_, ?_⟩
    · exact fun ha => hqfour <| (q_four_zero_iff μ a c hμ0 hμ2 hcon).2 <| Or.inl ha
    · exact fun ha => hqfour <| (q_four_zero_iff μ a c hμ0 hμ2 hcon).2 <| Or.inr ha
  · have h_order : orderOf g ∣ 12 :=
      orderOf_dvd_iff_pow_eq_one.mpr (param_g12 g μ a c hμ0 e0 e1 e2 h.1)
    have h_not_div_4 : ¬ (orderOf g ∣ 4) := fun hdvd =>
      ((q_four_zero_iff μ a c hμ0 h.1 hcon).mp
        ((param_g4_eq_one_iff g μ a c hμ0 e0 e1 e2 h.1).mp
          (orderOf_dvd_iff_pow_eq_one.mp hdvd))).elim h.2.1 h.2.2
    have h_not_div_6 : ¬ (orderOf g ∣ 6) := fun hdvd =>
      param_g6_ne g μ e0 h.1 <| orderOf_dvd_iff_pow_eq_one.mp hdvd
    have := Nat.le_of_dvd (by decide) h_order
    interval_cases orderOf g <;> trivial

/-! ### The Borel parametrization as a bijection, and the counts -/

/-- The existence statement of `stab_p0_param` for a stabilizer element. -/
lemma stab_hyp (s : stabilizer specialUnitaryGroup p0) :
    ∃ μ a c : F9, μ ≠ 0 ∧ a ^ 3 + μ ^ 2 * a + c ^ 4 * μ ^ 3 = 0 ∧
      toLinearEquiv (s : specialUnitaryGroup) fv0 = μ • fv0 ∧
      toLinearEquiv (s : specialUnitaryGroup) fv1 =
        a • fv0 + (μ ^ 3)⁻¹ • fv1 + c • fw ∧
      toLinearEquiv (s : specialUnitaryGroup) fw =
        (-(c ^ 3) * μ ^ 3) • fv0 + μ ^ 2 • fw :=
  stab_p0_param (s : specialUnitaryGroup) ((mem_stabilizer_iff).1 s.2)

/-- The Borel parameters `(μ, a, c)` of a stabilizer element of `p0`. -/
noncomputable def stab_param (s : stabilizer specialUnitaryGroup p0) :
    {t : F9 × F9 × F9 // param_pred_f9 t} :=
  ⟨((stab_hyp s).choose, (stab_hyp s).choose_spec.choose,
    (stab_hyp s).choose_spec.choose_spec.choose),
    ⟨(stab_hyp s).choose_spec.choose_spec.choose_spec.1,
      (stab_hyp s).choose_spec.choose_spec.choose_spec.2.1⟩⟩

/-- The defining properties of the Borel parameters of a stabilizer element. -/
lemma stab_param_spec (s : stabilizer specialUnitaryGroup p0) :
    (stab_param s).1.1 ≠ 0 ∧
    (stab_param s).1.2.1 ^ 3 +
    (stab_param s).1.1 ^ 2 * (stab_param s).1.2.1 +
    (stab_param s).1.2.2 ^ 4 * (stab_param s).1.1 ^ 3 = 0 ∧
    toLinearEquiv (s : specialUnitaryGroup) fv0 = (stab_param s).1.1 • fv0 ∧
    toLinearEquiv (s : specialUnitaryGroup) fv1 =
      (stab_param s).1.2.1 • fv0 +
      ((stab_param s).1.1 ^ 3)⁻¹ • fv1 + (stab_param s).1.2.2 • fw ∧
    toLinearEquiv (s : specialUnitaryGroup) fw =
      (-((stab_param s).1.2.2 ^ 3) * (stab_param s).1.1 ^ 3) • fv0 +
      (stab_param s).1.1 ^ 2 • fw :=
  (stab_hyp s).choose_spec.choose_spec.choose_spec

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- A stabilizer element has order `12` iff its Borel parameters satisfy the
order-twelve refinement. -/
lemma orderOf_stab_twelve_iff (s : stabilizer specialUnitaryGroup p0) :
    orderOf s = 12 ↔ order_twelve_pred_f9 (stab_param s).1 := by
  obtain ⟨hμ0, hcon, e0, e1, e2⟩ := stab_param_spec s
  rw [← show orderOf (s : specialUnitaryGroup) = orderOf s from
      orderOf_injective (stabilizer specialUnitaryGroup p0).subtype Subtype.coe_injective s,
    orderOf_twelve_iff_of_param (s : specialUnitaryGroup) _ _ _ hμ0 hcon e0 e1 e2,
    order_twelve_pred_f9]
  exact (and_iff_right (stab_param s).2).symm

/-- The Borel-parameter map on stabilizer elements is injective. -/
lemma stab_param_injective : Function.Injective stab_param := by
  intro s s' h
  obtain ⟨_, _, e0, e1, e2⟩ := stab_param_spec s
  obtain ⟨_, _, e0', e1', e2'⟩ := stab_param_spec s'
  have ht : (stab_param s).1 = (stab_param s').1 := congrArg Subtype.val h
  apply Subtype.ext
  apply stab_p0_param_injective
  · rw [e0, e0', congrArg Prod.fst ht]
  · rw [e1, e1', congrArg Prod.fst ht, congrArg (fun x => x.2.1) ht,
      congrArg (fun x => x.2.2) ht]
  · rw [e2, e2', congrArg Prod.fst ht, congrArg (fun x => x.2.2) ht]

/-- The Borel-parameter map on stabilizer elements is bijective. -/
lemma stab_param_bijective : Function.Bijective stab_param := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨stab_param_injective, by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_stabilizer_p0,
      card_param_f9]⟩

/-- The Borel parametrization bijection. -/
noncomputable def stab_param_equiv :
    stabilizer specialUnitaryGroup p0 ≃ {t : F9 × F9 × F9 // param_pred_f9 t} :=
  Equiv.ofBijective stab_param stab_param_bijective

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The order-twelve count in the point stabilizer of `p0` is `36`.** -/
theorem card_orderOf_eq_twelve_stab_p0 :
    (Finset.univ.filter fun g : MulAction.stabilizer specialUnitaryGroup p0 =>
      orderOf g = 12).card = 36 := by
  rw [← Fintype.card_subtype]
  have e1 : {s : stabilizer specialUnitaryGroup p0 // orderOf s = 12}
      ≃ {t : F9 × F9 × F9 // order_twelve_pred_f9 t} := by
    refine (stab_param_equiv.subtypeEquiv (fun s => ?_)).trans
      (Equiv.subtypeSubtypeEquivSubtype (fun {t} ht => ht.1))
    simpa [stab_param_equiv] using orderOf_stab_twelve_iff s
  rw [Fintype.card_congr e1, ← Nat.card_eq_fintype_card, card_order_twelve_f9]

end PointStabilizerCounts

end PSU33

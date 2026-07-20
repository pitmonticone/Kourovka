/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.HermitianGeometryBasic

/-!
# The `GF(9)` Hermitian polarity

This file specializes the Hermitian geometry API to `GF(9)` and computes the
number of isotropic projective points.
-/

namespace PSU33

open PSU33.HermitianForm

/-- The field `GF(9) = F_{3²}`, the natural field of definition for `PSU(3,3)`. -/
abbrev F9 := GaloisField 3 2

/-- The characteristic `3` of `GF(9)` is a prime. -/
local instance fact_three_prime : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- `GF(9)` is a finite type. -/
noncomputable instance : Fintype F9 := Fintype.ofFinite _

/-- The endomorphism ring of `GF(9)³` is finite. -/
instance : Finite (Module.End F9 (Fin 3 → F9)) :=
  Finite.of_injective _ DFunLike.coe_injective

/-- The linear automorphism group of `GF(9)³` is finite. -/
instance : Finite ((Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9)) :=
  Finite.of_injective _ LinearEquiv.toLinearMap_injective

/-- The field `GF(9)` has exactly `9` elements. -/
lemma card_f9 : Fintype.card F9 = 9 := by
  simpa [Nat.card_eq_fintype_card] using GaloisField.card 3 2 (by norm_num)

/-- The conjugation (Frobenius) automorphism `x ↦ x³` of `GF(9)`; it is the
involution defining the Hermitian polarity for `PSU(3,3)`. -/
noncomputable def conj9 : F9 →+* F9 := frobenius F9 3

/-- The conjugation of `GF(9)` sends `x` to `x ^ 3`. -/
lemma conj9_apply (x : F9) : conj9 x = x ^ 3 := by
  rfl

/-- The conjugation of `GF(9)` is an involution (it has order two). -/
lemma conj9_involutive : Function.Involutive conj9 := by
  intro x
  simpa [conj9_apply, ← pow_mul, card_f9] using FiniteField.pow_card x

/-- The unitary group `GU(3,3)` of the Hermitian polarity over `GF(9)`. -/
noncomputable abbrev unitaryGroup : Subgroup ((Fin 3 → F9) ≃ₗ[F9] (Fin 3 → F9)) :=
  HermitianForm.unitaryGroup conj9

/-- The special unitary group `SU(3,3)` of the Hermitian polarity over `GF(9)`. -/
noncomputable abbrev specialUnitaryGroup : Subgroup unitaryGroup :=
  HermitianForm.specialUnitaryGroup conj9

/-- The isotropic projective points of the `PSU(3,3)` polarity. -/
abbrev IsotropicPoint : Type := HermitianForm.IsotropicPoint conj9

/-- The permutation image of `SU(3,3)` on its isotropic points. The action is
proved faithful in `toPsu_injective`; since the scalar centre of `SU(3,3)` has
order `gcd(3, 4) = 1`, this image realises `PSU(3,3)`. -/
noncomputable abbrev psuPerm : Subgroup (Equiv.Perm IsotropicPoint) :=
  HermitianForm.psuPerm conj9

/-- The `PSU(3,3)` isotropic points, described by normalized isotropic vector
representatives over `GF(9)`. -/
noncomputable def isotropicNormEquiv :
    {v : Fin 3 → F9 // IsNormalized v ∧ hermForm conj9 v v = 0} ≃ IsotropicPoint :=
  HermitianForm.isotropicNormEquiv conj9

/-- If `S` generates `specialUnitaryGroup`, then its permutation images
generate `psuPerm`. -/
theorem psuPerm_eq_closure_image (S : Set specialUnitaryGroup)
    (hS : Subgroup.closure S = ⊤) :
    psuPerm =
    Subgroup.closure ((MulAction.toPermHom specialUnitaryGroup IsotropicPoint) '' S) :=
  HermitianForm.psuPerm_eq_closure_image S hS

/-- The two-generator specialization of `psuPerm_eq_closure_image`. -/
theorem psuPerm_eq_closure_pair (g h : specialUnitaryGroup)
    (hgh : Subgroup.closure ({g, h} : Set specialUnitaryGroup) = ⊤) :
    psuPerm = Subgroup.closure
    ({MulAction.toPermHom specialUnitaryGroup IsotropicPoint g,
      MulAction.toPermHom specialUnitaryGroup IsotropicPoint h} :
      Set (Equiv.Perm IsotropicPoint)) :=
  HermitianForm.psuPerm_eq_closure_pair g h hgh

/-!
## The isotropic-point count `q³ + 1 = 28`

We now prove `Fintype.card IsotropicPoint = 28`.  The Hermitian self-form of
a vector is the sum of the fourth powers of its coordinates, so a vector is
isotropic iff `v 0 ^ 4 + v 1 ^ 4 + v 2 ^ 4 = 0`.  Over `GF(9)` the fourth power
of a nonzero element is `±1` (it is the norm down to `GF(3)`), with `4` preimages
each, while `0 ^ 4 = 0`.  A finite-field root count then gives `225` isotropic
vectors, `224` of them nonzero, and dividing by the `8` nonzero scalars yields
`28` projective isotropic points. -/

open Finset

/-- Equality on `GF(9)` is decidable. -/
noncomputable instance : DecidableEq F9 := Classical.decEq _

/-- `GF(9)` has `8` units. -/
lemma card_units_F9 : Nat.card F9ˣ = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units, card_f9]

/-- The characteristic identity `3 = 0` in `GF(9)`. -/
lemma three_eq_zero : (3 : F9) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F9 3

/-- The Hermitian self-form is the sum of fourth powers of the coordinates. -/
lemma hermForm_self_eq (v : Fin 3 → F9) :
    hermForm conj9 v v = v 0 ^ 4 + v 1 ^ 4 + v 2 ^ 4 := by
  simp only [hermForm_apply, Fin.sum_univ_three, conj9_apply]
  ring

/-- Over `GF(9)`, the fourth power of any element is `0`, `1`, or `-1`. -/
lemma fourth_pow_cases (x : F9) : x ^ 4 = 0 ∨ x ^ 4 = 1 ∨ x ^ 4 = -1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact Or.inr <| mul_self_eq_one_iff.mp <| by
      simpa [← pow_add, card_f9] using FiniteField.pow_card_sub_one_eq_one x hx

/-- A sum of two fourth powers lies in `{0, 1, -1}` (using `3 = 0`). -/
lemma sum_fourth_mem (a b : F9) :
    a ^ 4 + b ^ 4 = 0 ∨ a ^ 4 + b ^ 4 = 1 ∨ a ^ 4 + b ^ 4 = -1 := by
  rcases fourth_pow_cases a with ha | ha | ha <;>
    rcases fourth_pow_cases b with hb | hb | hb <;> norm_num [ha, hb] <;>
    first
      | (right; right; linear_combination three_eq_zero)
      | (right; left; linear_combination -three_eq_zero)

/-- In `GF(9)`, `1` and `-1` are distinct. -/
lemma one_ne_negone_F9 : (1 : F9) ≠ -1 := by
  intro h
  exact one_ne_zero (show (1 : F9) = 0 by linear_combination three_eq_zero - h)

/-- There are exactly `4` fourth roots of unity in `GF(9)ˣ` (orders `1, 2, 4`). -/
lemma units_pow_eq_one : #{u : F9ˣ | u ^ 4 = 1} = 4 := by
  rw [← sum_card_orderOf_eq_card_pow_eq_one (by norm_num : (4 : Nat) ≠ 0),
    show (4 : Nat).divisors = {1, 2, 4} by decide,
    show ({1, 2, 4} : Finset Nat) = insert 1 (insert 2 {4}) from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_singleton,
    IsCyclic.card_orderOf_eq_totient (by
      rw [Fintype.card_units, card_f9]
      norm_num),
    IsCyclic.card_orderOf_eq_totient (by
      rw [Fintype.card_units, card_f9]
      norm_num),
    IsCyclic.card_orderOf_eq_totient (by
      rw [Fintype.card_units, card_f9]
      norm_num)]
  decide

/-- There are exactly `4` solutions of `u ^ 4 = -1` in `GF(9)ˣ` (the primitive
`8`-th roots of unity). -/
lemma units_pow_eq_negone : #{u : F9ˣ | u ^ 4 = -1} = 4 := by
  have e1 (u : F9ˣ) : (u ^ 4 = 1) ↔ ((u : F9) ^ 4 = 1) := by
    rw [← Units.val_eq_one, Units.val_pow_eq_pow_val]
  have e2 (u : F9ˣ) : (u ^ 4 = -1) ↔ ((u : F9) ^ 4 = -1) := by
    rw [← Units.val_inj, Units.val_pow_eq_pow_val]
    norm_num
  have hu (u : F9ˣ) : (u ^ 4 = -1) ↔ ¬ u ^ 4 = 1 := by
    rw [e1 u, e2 u]
    rcases fourth_pow_cases (u : F9) with h | h | h <;>
      simp_all [pow_eq_zero_iff, one_ne_negone_F9, one_ne_negone_F9.symm, u.ne_zero]
  calc
    #{u : F9ˣ | u ^ 4 = -1} = #{u : F9ˣ | ¬ u ^ 4 = 1} := by
      exact congrArg Finset.card (Finset.filter_congr fun u _ => hu u)
    _ = 4 := by
      rw [Finset.filter_not, Finset.card_univ_diff, units_pow_eq_one,
        Fintype.card_units, card_f9]

/-- There are exactly `4` elements of `GF(9)` with fourth power `1`. -/
lemma card_fourth_one : Nat.card {x : F9 // x ^ 4 = 1} = 4 := by
  have e : {x : F9 // x ^ 4 = 1} ≃ {u : F9ˣ // u ^ 4 = 1} :=
    { toFun := fun x =>
        ⟨Units.mk0 x.1 (fun h => by simpa [h] using x.2),
          Units.ext (by simpa using x.2)⟩
      invFun := fun u => ⟨(u.1 : F9), by simpa using congrArg Units.val u.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun u => by ext; rfl
    }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, units_pow_eq_one]

/-- There are exactly `4` elements of `GF(9)` with fourth power `-1`. -/
lemma card_fourth_negone : Nat.card {x : F9 // x ^ 4 = -1} = 4 := by
  have e : {x : F9 // x ^ 4 = -1} ≃ {u : F9ˣ // u ^ 4 = -1} :=
    { toFun := fun x =>
        ⟨Units.mk0 x.1 (fun h => by simpa [h] using x.2),
          Units.ext (by simpa using x.2)⟩
      invFun := fun u => ⟨(u.1 : F9), by simpa using congrArg Units.val u.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun u => by ext; rfl
    }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    units_pow_eq_negone]

/-- Only `0` has fourth power `0` in `GF(9)`. -/
lemma card_fourth_zero : Nat.card {x : F9 // x ^ 4 = 0} = 1 := by
  simp [pow_eq_zero_iff]

/-- The fiber count of the fourth-power map at a value in `{0, 1, -1}`. -/
lemma card_fiber_of_mem (d : F9) (hd : d = 0 ∨ d = 1 ∨ d = -1) :
    Nat.card {c : F9 // c ^ 4 = d} = if d = 0 then 1 else 4 := by
  rcases hd with rfl | rfl | rfl
  · simp
  · simpa using card_fourth_one
  · simpa using card_fourth_negone

/-- Fibering a product subtype over its first coordinate. -/
def prodSubtypeSigma {A B : Type*} (R : A → B → Prop) :
    {p : A × B // R p.1 p.2} ≃ Σ a : A, {b : B // R a b} where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cardinality of a product subtype is the sum of the fiber cardinalities over
the first coordinate. -/
lemma card_prod_fiber {A B : Type*} [Fintype A] [Finite B] (R : A → B → Prop) :
    Nat.card {p : A × B // R p.1 p.2} = ∑ a : A, Nat.card {b : B // R a b} := by
  rw [Nat.card_congr (prodSubtypeSigma R), Nat.card_sigma]

/-- The negation of a fourth power lies in `{0, 1, -1}`. -/
lemma neg_fourth_mem (a : F9) : -a ^ 4 = 0 ∨ -a ^ 4 = 1 ∨ -a ^ 4 = -1 := by
  rcases fourth_pow_cases a with h | h | h <;> simp [h]

/-- The negation of a sum of two fourth powers lies in `{0, 1, -1}`. -/
lemma neg_sum_fourth_mem (a b : F9) :
    -(a ^ 4 + b ^ 4) = 0 ∨ -(a ^ 4 + b ^ 4) = 1 ∨ -(a ^ 4 + b ^ 4) = -1 := by
  rcases sum_fourth_mem a b with h | h | h <;> simp [h]

/-- Summing the fiber sizes `1` (at `0`) and `4` (at each nonzero element) over `GF(9)`
gives `33`. -/
lemma sum_ite_F9 : ∑ a : F9, (if a = 0 then 1 else 4) = 33 := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.filter_eq' univ 0, Finset.filter_not, Finset.card_univ_diff,
    Finset.filter_eq' univ 0]
  simp [card_f9]

/-- The number of pairs `(a, b)` with `a^4 + b^4 = 0` is `33`. -/
lemma card_pair_zero : Nat.card {p : F9 × F9 // p.1 ^ 4 + p.2 ^ 4 = 0} = 33 := by
  rw [card_prod_fiber (fun a b => a ^ 4 + b ^ 4 = 0)]
  have hfib (a : F9) :
      Nat.card {b : F9 // a ^ 4 + b ^ 4 = 0} = if a = 0 then 1 else 4 := by
    have e : {b : F9 // a ^ 4 + b ^ 4 = 0} ≃ {b : F9 // b ^ 4 = -a ^ 4} :=
      Equiv.subtypeEquivRight (fun b => by constructor <;> intro h <;> linear_combination h)
    rw [Nat.card_congr e, card_fiber_of_mem _ (neg_fourth_mem a)]
    simp [neg_eq_zero, pow_eq_zero_iff]
  simpa only [hfib] using sum_ite_F9

/-- Summing the third-coordinate fiber sizes over all pairs `(a, b)` gives `225`. -/
lemma sum_ite_pair :
    ∑ ab : F9 × F9, (if ab.1 ^ 4 + ab.2 ^ 4 = 0 then 1 else 4) = 225 := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  have hp :
      (univ.filter (fun ab : F9 × F9 => ab.1 ^ 4 + ab.2 ^ 4 = 0)).card = 33 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using card_pair_zero
  rw [hp, Finset.filter_not, Finset.card_univ_diff, hp]
  norm_num [Fintype.card_prod, card_f9]

/-- The number of triples `(a, b, c)` with `a^4 + b^4 + c^4 = 0` is `225`. -/
lemma card_triple_zero :
    Nat.card {p : F9 × F9 × F9 // p.1 ^ 4 + p.2.1 ^ 4 + p.2.2 ^ 4 = 0} = 225 := by
  have eassoc :
      {p : F9 × F9 × F9 // p.1 ^ 4 + p.2.1 ^ 4 + p.2.2 ^ 4 = 0} ≃
      {p : (F9 × F9) × F9 // p.1.1 ^ 4 + p.1.2 ^ 4 + p.2 ^ 4 = 0} :=
    Equiv.subtypeEquiv (Equiv.prodAssoc F9 F9 F9).symm fun _ => Iff.rfl
  rw [Nat.card_congr eassoc,
    card_prod_fiber (fun (ab : F9 × F9) (c : F9) =>
      ab.1 ^ 4 + ab.2 ^ 4 + c ^ 4 = 0)]
  have hfib (ab : F9 × F9) :
      Nat.card {c : F9 // ab.1 ^ 4 + ab.2 ^ 4 + c ^ 4 = 0} =
      if ab.1 ^ 4 + ab.2 ^ 4 = 0 then 1 else 4 := by
    have e :
        {c : F9 // ab.1 ^ 4 + ab.2 ^ 4 + c ^ 4 = 0} ≃
        {c : F9 // c ^ 4 = -(ab.1 ^ 4 + ab.2 ^ 4)} :=
      Equiv.subtypeEquivRight (fun c => by constructor <;> intro h <;> linear_combination h)
    rw [Nat.card_congr e, card_fiber_of_mem _ (neg_sum_fourth_mem ab.1 ab.2)]
    exact if_congr neg_eq_zero rfl rfl
  simpa only [hfib] using sum_ite_pair

/-- Coordinatewise identification of `Fin 3 → F9` with triples. -/
def vecEquivTriple : (Fin 3 → F9) ≃ F9 × F9 × F9 where
  toFun v := (v 0, v 1, v 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

/-- There are `225` isotropic vectors (including the zero vector). -/
lemma card_isotropic_all : Nat.card {v : Fin 3 → F9 // hermForm conj9 v v = 0} = 225 := by
  let e :
      {v : Fin 3 → F9 // hermForm conj9 v v = 0} ≃
      {p : F9 × F9 × F9 // p.1 ^ 4 + p.2.1 ^ 4 + p.2.2 ^ 4 = 0} :=
    (Equiv.subtypeEquivRight (fun v => by rw [hermForm_self_eq])).trans
      (Equiv.subtypeEquiv vecEquivTriple fun _ => by rfl)
  rw [Nat.card_congr e, card_triple_zero]

/-- There are `224` nonzero isotropic vectors. -/
lemma card_isotropic_nonzero :
    Nat.card {v : Fin 3 → F9 // v ≠ 0 ∧ hermForm conj9 v v = 0} = 224 := by
  classical
  have key :
      univ.filter (fun v : Fin 3 → F9 => hermForm conj9 v v = 0) =
      insert (0 : Fin 3 → F9) (univ.filter (fun v => v ≠ 0 ∧ hermForm conj9 v v = 0)) := by
    ext v
    by_cases hv : v = 0 <;> simp [hv, hermForm_self_eq]
  have hall : (univ.filter (fun v : Fin 3 → F9 => hermForm conj9 v v = 0)).card = 225 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using card_isotropic_all
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [key, Finset.card_insert_of_notMem (by simp)] at hall
  omega

/-- The isotropic projective points form a finite type. -/
instance : Finite IsotropicPoint :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The isotropic projective points are equipped with a `Fintype` structure. -/
noncomputable instance : Fintype IsotropicPoint := Fintype.ofFinite _

/-- **There are `28` isotropic projective points for the `PSU(3,3)` polarity**
(`q³ + 1 = 3³ + 1 = 28`). -/
theorem card_isotropicPoint : Fintype.card IsotropicPoint = 28 := by
  have h := card_isotropic_eq_mul (σ := conj9)
  rw [card_isotropic_nonzero, card_units_F9] at h
  rw [Fintype.card_eq_nat_card]
  change Nat.card (HermitianForm.IsotropicPoint conj9) = 28
  omega

end PSU33

/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Util.PSU33.RootGeneration
import Kourovka.Util.PSU33.Cardinality
import Kourovka.Util.PSU33.PointStabilizer
import Mathlib.Algebra.CharP.Pi
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Algebra.Group.Equiv.Finite
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

/-!
# Sylow-seven count for `PSU(3,3)`

The Sylow `7` and centralizer argument giving the order-seven element count in
the geometric `SU(3,3)` model.
-/

namespace PSU33

open PSU33.HermitianForm Finset MulAction
open scoped Classical

section SylowSevenCount
/-- `7` is prime. -/
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The structural Sylow input used in the order-seven count: every Sylow
`7`-subgroup is self-centralizing. -/
def HasSelfCentralizingSylow7 (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow 7 G,
    Nat.card (Subgroup.centralizer ((P : Subgroup G) : Set G)) = 7

variable {G : Type*} [Group G] [Fintype G]

/-- The factorization of `6048` at `7` is `1`. -/
lemma factorization_6048_seven : Nat.factorization 6048 7 = 1 := by
  rw [show (6048 : ℕ) = 7 ^ 1 * 864 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow (by norm_num)]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 864 by norm_num)]

/-- A Sylow `7`-subgroup of a group of order `6048` has order `7`. -/
lemma sylow7_card (hcard : Fintype.card G = 6048) (P : Sylow 7 G) :
    Nat.card (P : Subgroup G) = 7 := by
  rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard, factorization_6048_seven,
    pow_one]

/-- In a Sylow `7`-subgroup of order `7`, exactly `6` elements have order `7`
(every non-identity element). -/
lemma card_order_seven_in_sylow (hcard : Fintype.card G = 6048) (P : Sylow 7 G) :
    (Finset.univ.filter
      (fun g : G => g ∈ (P : Subgroup G) ∧ orderOf g = 7)).card = 6 := by
  have hP_card : Nat.card (P : Subgroup G) = 7 := sylow7_card hcard P
  have hP_order : ∀ g ∈ (P : Subgroup G), g ≠ 1 → orderOf g = 7 := by
    intro g hg hg_ne_one
    have h_div : orderOf g ∣ 7 :=
      (Nat.card_zpowers g).symm.dvd.trans
        (hP_card ▸ Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hg))
    simp_all +decide [Nat.dvd_prime]
  rw [show
      (Finset.filter (fun g => g ∈ (P : Subgroup G) ∧ orderOf g = 7)
        Finset.univ) =
      Finset.filter (fun g => g ∈ (P : Subgroup G) ∧ g ≠ 1) Finset.univ from ?_]
  · simp_all +decide [Fintype.card_subtype]
    rw [show
        (Finset.filter
          (fun g => g ∈ (P : Subgroup G) ∧ ¬ g = 1) Finset.univ : Finset G) =
        Finset.filter (fun g => g ∈ (P : Subgroup G)) Finset.univ \ {1} by
          ext
          aesop]
    rw [Finset.card_sdiff]
    aesop
  · ext g
    aesop

/-- The order-seven elements are partitioned by the Sylow `7`-subgroups, giving
the count `6 * n₇`. -/
lemma count_order_seven_eq_six_mul_card_sylow (hcard : Fintype.card G = 6048) :
    (Finset.univ.filter (fun g : G => orderOf g = 7)).card
      = 6 * Nat.card (Sylow 7 G) := by
  -- By Sylow's theorems, each Sylow 7-subgroup contains exactly 6 elements of order 7.
  have h_sylow_elements :
      ∀ P : Sylow 7 G,
        (Finset.filter (fun g => orderOf g = 7)
          (Finset.univ.filter (fun g => g ∈ (P : Subgroup G)))).card = 6 := by
    convert card_order_seven_in_sylow hcard using 1
    simp +decide only [filter_filter]
  have h_partition :
      Finset.biUnion (Finset.univ : Finset (Sylow 7 G))
        (fun P => Finset.filter (fun g => orderOf g = 7)
          (Finset.univ.filter (fun g => g ∈ (P : Subgroup G)))) =
      Finset.filter (fun g => orderOf g = 7) (Finset.univ : Finset G) := by
    ext g
    simp
    intro hg
    obtain ⟨P, hP⟩ : ∃ P : Subgroup G, Nat.card P = 7 ∧ g ∈ P :=
      ⟨Subgroup.zpowers g, (Nat.card_zpowers g).trans hg, Subgroup.mem_zpowers g⟩
    have hP_sylow : IsPGroup 7 P := fun x =>
      ⟨1, by rw [← hP.1, Nat.card_eq_fintype_card, pow_one, pow_card_eq_one]⟩
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP_sylow
    exact ⟨Q, hQ hP.2⟩
  rw [← h_partition, Finset.card_biUnion]
  simp_all +decide [mul_comm]
  intro P hP Q hQ hPQ
  simp_all +decide [Finset.disjoint_left]
  intro g hgP hg_order hgQ
  have h_subgroup :
      Subgroup.zpowers g ≤ (P : Subgroup G) ∧
      Subgroup.zpowers g ≤ (Q : Subgroup G) :=
    ⟨Subgroup.zpowers_le.mpr hgP, Subgroup.zpowers_le.mpr hgQ⟩
  have h_card : Nat.card (Subgroup.zpowers g) = 7 := (Nat.card_zpowers g).trans hg_order
  have h_card_P : Nat.card (P : Subgroup G) = 7 := sylow7_card hcard P
  have h_card_Q : Nat.card (Q : Subgroup G) = 7 := sylow7_card hcard Q
  have h_eq :
      (Subgroup.zpowers g : Subgroup G) = (P : Subgroup G) ∧
      (Subgroup.zpowers g : Subgroup G) = (Q : Subgroup G) :=
    ⟨SetLike.ext' <| Set.eq_of_subset_of_card_le h_subgroup.1 <| by aesop,
      SetLike.ext' <| Set.eq_of_subset_of_card_le h_subgroup.2 <| by aesop⟩
  exact hPQ (Sylow.ext (by aesop))

omit [Fintype G] in
/-- The centralizer of a Sylow `7`-subgroup is contained in its normalizer. -/
lemma centralizer_le_normalizer_sylow7 (P : Sylow 7 G) :
    Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ (P : Subgroup G).normalizer := by
  intro g hg
  simp_all +decide [Subgroup.mem_centralizer_iff, Subgroup.mem_normalizer_iff]
  intro h
  exact ⟨
    fun hh => by simp +decide [← hg h hh, hh],
    fun hh => by
      have h_comm : ∀ x : P, g * x.val * g⁻¹ = x.val := by
        simp_all +decide [mul_inv_eq_iff_eq_mul]
      specialize h_comm ⟨g * h * g⁻¹, hh⟩
      aesop⟩

/-- **Normalizer divides 42.**  With the self-centralizing hypothesis
`hcent : |C_G(P)| = 7`, the embedding `N_G(P)/C_G(P) ↪ Aut(C₇)` (of order `6`)
gives `|N_G(P)| ∣ 42`. -/
lemma normalizer_sylow7_card_dvd (hcard : Fintype.card G = 6048)
    (P : Sylow 7 G)
    (hcent : Nat.card (Subgroup.centralizer ((P : Subgroup G) : Set G)) = 7) :
    Nat.card ((P : Subgroup G).normalizer) ∣ 42 := by
  have hC_le_N :
      Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ (P : Subgroup G).normalizer :=
    centralizer_le_normalizer_sylow7 P
  have hN_card :
      Nat.card (↥(P : Subgroup G).normalizer) =
      Nat.card
        (↥(Subgroup.centralizer ((P : Subgroup G) : Set G) ⊓
          (P : Subgroup G).normalizer)) *
        Nat.card (↥(Subgroup.normalizerMonoidHom (P : Subgroup G)).range) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MonoidHom.ker (Subgroup.normalizerMonoidHom (P : Subgroup G)))
    rw [this, mul_comm]
    congr! 1
    · rw [Subgroup.normalizerMonoidHom_ker, ← Nat.card_congr]
      exact ⟨
        fun x => ⟨⟨x.val, x.2.2⟩, x.2.1⟩,
        fun x => ⟨x.val, x.2, x.val.2⟩,
        fun x => rfl,
        fun x => rfl⟩
    · exact Nat.card_congr
        (QuotientGroup.quotientKerEquivRange
          (Subgroup.normalizerMonoidHom (P : Subgroup G)))
  have hC_card :
      Nat.card
        (↥(Subgroup.centralizer ((P : Subgroup G) : Set G) ⊓
          (P : Subgroup G).normalizer)) = 7 := by
    rw [inf_eq_left.mpr hC_le_N]
    exact hcent
  have h_range_card :
      Nat.card (↥(Subgroup.normalizerMonoidHom (P : Subgroup G)).range) ∣
        Nat.card (MulAut (↥(P : Subgroup G))) :=
    Subgroup.card_subgroup_dvd_card _
  have h_aut_card : Nat.card (MulAut (↥(P : Subgroup G))) = Nat.totient 7 := by
    convert IsCyclic.card_mulAut (P : Subgroup G) using 1
    · rw [sylow7_card hcard P]
    · convert isCyclic_of_prime_card (sylow7_card hcard P)
  simp_all +decide [Nat.totient_prime]
  exact mul_dvd_mul_left 7 h_range_card

/-- **The normalizer of a Sylow `7`-subgroup has order exactly `21`.**  The loose
bound `∣ 42` is sharpened using Sylow's third theorem. -/
lemma normalizer_sylow7_card_eq (hcard : Fintype.card G = 6048)
    (P : Sylow 7 G)
    (hcent : Nat.card (Subgroup.centralizer ((P : Subgroup G) : Set G)) = 7) :
    Nat.card ((P : Subgroup G).normalizer) = 21 := by
  -- Sylow's third theorem gives `n₇ ≡ 1 (mod 7)` and `n₇ ∣ 6048 / 7 = 864`.
  have h_n7 : (Nat.card (Sylow 7 G)) ≡ 1 [MOD 7] ∧
      (Nat.card (Sylow 7 G)) ∣ 864 := by
    have h_n7 : (Nat.card (Sylow 7 G)) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 G
    have h_n7_div : (Nat.card (Sylow 7 G)) ∣ 6048 := by
      convert Subgroup.card_quotient_dvd_card
        (Subgroup.normalizer (P : Subgroup G)) using 1
      · convert Nat.card_congr (Sylow.equivQuotientNormalizer P) using 1
      · rw [← hcard, Nat.card_eq_fintype_card]
    have hcop : Nat.Coprime (Nat.card (Sylow 7 G)) 7 :=
      Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd (by decide)).2 fun h => by
        have := Nat.modEq_zero_iff_dvd.1 (h_n7.symm.trans (Nat.modEq_zero_iff_dvd.2 h))
        contradiction
    exact ⟨h_n7, Nat.Coprime.dvd_of_dvd_mul_left hcop h_n7_div⟩
  -- The number of Sylow `7`-subgroups is the normalizer index.
  have h_index :
      Nat.card (Sylow 7 G) = Nat.card G / Nat.card ((P : Subgroup G).normalizer) := by
    convert Nat.card_congr (Sylow.equivQuotientNormalizer P) using 1
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.normalizer (P : Subgroup G))
    aesop
  have := normalizer_sylow7_card_dvd hcard P hcent
  have := Nat.le_of_dvd (by decide) this
  interval_cases _ : Nat.card ↥((P : Subgroup G).normalizer) <;>
    simp_all +decide only
  all_goals simp_all +decide only [Nat.card_eq_fintype_card]

/-- The number of Sylow `7`-subgroups is `288`. -/
lemma card_sylow7_eq (hcard : Fintype.card G = 6048)
    (hcent : HasSelfCentralizingSylow7 G) :
    Nat.card (Sylow 7 G) = 288 := by
  have h_index :
      ∀ P : Sylow 7 G,
        Nat.card (Sylow 7 G) =
        Nat.card G / Nat.card ((P : Subgroup G).normalizer) := by
    intro P
    have := Sylow.card_eq_index_normalizer P
    simp_all +decide [Nat.card_eq_fintype_card]
    rw [← hcard, Subgroup.index_eq_card]
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.normalizer (P : Subgroup G))
    aesop
  convert h_index (default : Sylow 7 G) using 1
  rw [normalizer_sylow7_card_eq hcard _ (hcent _), Nat.card_eq_fintype_card, hcard]

/-- **Order-seven count for finite groups of order `6048` with self-centralizing
Sylow `7`-subgroups.**  Sylow-counting core of the order-seven histogram entry. -/
theorem count_order_seven_eq_1728
    (hcard : Fintype.card G = 6048)
    (hcent : HasSelfCentralizingSylow7 G) :
    (Finset.univ.filter (fun g : G => orderOf g = 7)).card = 1728 := by
  rw [count_order_seven_eq_six_mul_card_sylow hcard, card_sylow7_eq hcard hcent]

end SylowSevenCount

/-- `Fintype.card specialUnitaryGroup = 6048` (from `card_specialUnitaryGroup`). -/
lemma card_specialUnitaryGroup_fintype : Fintype.card specialUnitaryGroup = 6048 :=
  Nat.card_eq_fintype_card.symm.trans card_specialUnitaryGroup

/-- **Order-seven count in geometric `SU(3,3)`.**  If Sylow `7`-subgroups are
self-centralizing, there are exactly `1728` elements of order `7`. -/
theorem card_orderOf_eq_seven_su_of_hasSelfCentralizingSylow7
    (hcent : HasSelfCentralizingSylow7 specialUnitaryGroup) :
    (Finset.univ.filter
      (fun g : specialUnitaryGroup => orderOf g = 7)).card = 1728 :=
  count_order_seven_eq_1728 card_specialUnitaryGroup_fintype hcent

open Polynomial
open PSU33.HermitianForm

/-- The underlying `GF(9)`-linear endomorphism of an element of
`specialUnitaryGroup`, packaged as a monoid homomorphism into
`Module.End F9 (Fin 3 → F9)`. -/
noncomputable def suEndHom : specialUnitaryGroup →* Module.End F9 (Fin 3 → F9) where
  toFun g := (toLinearEquiv g).toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `suEndHom g` is the linear map underlying `toLinearEquiv g`. -/
@[simp] lemma suEndHom_apply (g : specialUnitaryGroup) :
    suEndHom g = (toLinearEquiv g).toLinearMap := rfl

/-- `suEndHom` is injective. -/
lemma suEndHom_injective : Function.Injective suEndHom := fun a b h =>
  toLinearEquiv_injective_stab (LinearEquiv.toLinearMap_injective (by simpa [suEndHom] using h))

/-- In a finite field whose order satisfies `7 ∤ |L| - 1`, the only `7`-th root
of unity is `1`. -/
lemma seventh_root_eq_one {L : Type*} [Field L] [Finite L]
    (hL : ¬ (7 ∣ (Nat.card L - 1))) (ρ : L) (hρ : ρ ^ 7 = 1) : ρ = 1 := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, Nat.card L = q ∧ ρ ^ (q - 1) = 1 := by
    have := Fintype.ofFinite L
    simp_all +decide
    rw [FiniteField.pow_card_sub_one_eq_one]
    aesop
  have h_order : orderOf ρ ∣ 7 ∧ orderOf ρ ∣ q - 1 :=
    ⟨orderOf_dvd_of_pow_eq_one hρ, orderOf_dvd_of_pow_eq_one hq.2⟩
  simp_all +decide [Nat.dvd_prime]
  aesop

/-- The number of elements of `AdjoinRoot q` for an irreducible `q` over `F9` is
`9 ^ (natDegree q)`. -/
lemma card_adjoinRoot_irreducible (q : F9[X]) (hq : Irreducible q) :
    Nat.card (AdjoinRoot q) = 9 ^ q.natDegree := by
  have h_card :
      Nat.card (AdjoinRoot q) = Nat.card (Fin (Polynomial.natDegree q) → F9) := by
    have h_card :
        Nonempty (AdjoinRoot q ≃ₗ[F9] Fin (Polynomial.natDegree q) → F9) := by
      refine ⟨?_⟩
      convert (AdjoinRoot.powerBasis hq.ne_zero).basis.equivFun
    exact Nat.card_congr h_card.some.toEquiv
  convert h_card using 1
  norm_num [Nat.card_pi, Nat.card_eq_fintype_card]
  convert rfl
  convert card_f9

/-- **Factor-degree dichotomy.** A monic irreducible divisor `q` of `X^7 - 1`
over `GF(9)` is either `X - 1` or has degree `≥ 3`.  Indeed if `1 ≤ deg q ≤ 2`
then `AdjoinRoot q` is a field with `9` or `81` elements, in which the root of
`q` is a `7`-th root of unity; since `7 ∤ 8` and `7 ∤ 80` that root is `1`, forcing
`q = X - 1`. -/
lemma irr_factor_X7_deg (q : F9[X]) (hq : Irreducible q) (hqm : q.Monic)
    (hdvd : q ∣ (X ^ 7 - 1)) : q = X - 1 ∨ 3 ≤ q.natDegree := by
  by_contra! h_contra
  obtain ⟨ρ, hρ⟩ : ∃ ρ : AdjoinRoot q, ρ ^ 7 = 1 ∧ ρ ≠ 1 := by
    have h_root : (AdjoinRoot.mk q (X ^ 7 - 1)) = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd
    have h_root_ne_one : (AdjoinRoot.mk q X) ≠ 1 := by
      erw [Ne.eq_def, AdjoinRoot.mk_eq_mk]
      intro h
      have := Polynomial.degree_le_of_dvd h
      simp_all +decide [Polynomial.degree_sub_eq_left_of_degree_lt]
      have := this (Polynomial.X_sub_C_ne_zero 1)
      rw [Polynomial.degree_eq_natDegree hq.ne_zero] at this
      norm_cast at this
      interval_cases _ : q.natDegree <;> simp_all +decide
      obtain ⟨a, ha⟩ : ∃ a : F9, q = Polynomial.X - Polynomial.C a := by
        rw [Polynomial.eq_X_add_C_of_natDegree_le_one
          (le_of_eq ‹q.natDegree = 1›)] at hq ⊢
        simp_all +decide [Polynomial.Monic.def, Polynomial.leadingCoeff]
        exact ⟨-q.coeff 0, by simp +decide [sub_eq_add_neg]⟩
      simp_all +decide [Polynomial.dvd_iff_isRoot]
      exact h_contra (by
        rw [sub_eq_zero.mp h]
        norm_num)
    exact ⟨AdjoinRoot.mk q X, by simpa [sub_eq_iff_eq_add] using h_root, h_root_ne_one⟩
  have : Fact (Irreducible q) := ⟨hq⟩
  have : Finite (AdjoinRoot q) :=
    Finite.of_equiv (Fin (Polynomial.natDegree q) → F9) <|
      (LinearEquiv.toEquiv (AdjoinRoot.powerBasis hq.ne_zero).basis.equivFun).symm
  have h_card : Nat.card (AdjoinRoot q) = 9 ^ q.natDegree := card_adjoinRoot_irreducible q hq
  have h_card : ¬ (7 ∣ (Nat.card (AdjoinRoot q) - 1)) := by
    have : q.natDegree ≤ 2 := Nat.le_of_lt_succ h_contra.2
    interval_cases _ : q.natDegree <;> simp_all +decide
  exact hρ.2 (seventh_root_eq_one h_card ρ hρ.1)

section FixedElement

variable (g : specialUnitaryGroup)

/-- The `7`-th power of the underlying endomorphism of an order-dividing-`7`
element is the identity. -/
lemma suEnd_pow7 (hg7 : g ^ 7 = 1) : (suEndHom g) ^ 7 = 1 := by
  rw [← map_pow, hg7, map_one]

/-- The underlying endomorphism of a non-identity element is not the identity. -/
lemma suEnd_ne_one (hg1 : g ≠ 1) : suEndHom g ≠ 1 :=
  fun h => hg1 (suEndHom_injective (by rw [h, map_one]))

/-- The minimal polynomial of the underlying endomorphism divides `X^7 - 1`. -/
lemma minpoly_dvd_X7 (hg7 : g ^ 7 = 1) :
    minpoly F9 (suEndHom g) ∣ (X ^ 7 - 1) :=
  minpoly.dvd _ _ (by rw [map_sub, map_pow, aeval_X, map_one, suEnd_pow7 g hg7, sub_self])

/-- `T = suEndHom g` is integral over `F9` (the endomorphism algebra is
finite-dimensional). -/
lemma suEnd_isIntegral : IsIntegral F9 (suEndHom g) := IsIntegral.of_finite F9 _

/-- The minimal polynomial of `T = suEndHom g` has degree at most `3`
(Cayley–Hamilton: it divides the characteristic polynomial, of degree
`finrank = 3`). -/
lemma minpoly_natDegree_le_three :
    (minpoly F9 (suEndHom g)).natDegree ≤ 3 := by
  have hfin : Module.finrank F9 (Fin 3 → F9) = 3 := by
    rw [Module.finrank_pi]
    simp
  have hdvd : minpoly F9 (suEndHom g) ∣ (suEndHom g).charpoly :=
    minpoly.dvd _ _ (LinearMap.aeval_self_charpoly _)
  have hle := Polynomial.natDegree_le_of_dvd hdvd (suEndHom g).charpoly_monic.ne_zero
  rwa [LinearMap.charpoly_natDegree, hfin] at hle

/-- The minimal polynomial of `T = suEndHom g` is separable (it divides the
separable polynomial `X^7 - 1`). -/
lemma minpoly_separable (hg7 : g ^ 7 = 1) :
    (minpoly F9 (suEndHom g)).Separable :=
  (Polynomial.X_pow_sub_one_separable_iff.mpr
    (by
      rw [Ne, CharP.cast_eq_zero_iff F9 3]
      decide)).of_dvd (minpoly_dvd_X7 g hg7)

/-- **No eigenvalue `1`.** For an order-`7` element `g`, `X - 1` does not divide
the minimal polynomial of `T = suEndHom g` (equivalently `1` is not an
eigenvalue).  Otherwise the separable cofactor `minpoly / (X - 1)` would (being a
degree-`≤ 2` divisor of `X^7 - 1` with no monic irreducible factor other than
`X - 1`, excluded by squarefreeness) be a unit, forcing `minpoly = X - 1` and
`T = 1`. -/
lemma not_X_sub_one_dvd_minpoly (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) :
    ¬ ((X - 1 : F9[X]) ∣ minpoly F9 (suEndHom g)) := by
  intro h_div
  obtain ⟨p1, hp1⟩ := h_div
  have hXm : (X - 1 : F9[X]).Monic := by simpa using monic_X_sub_C (1 : F9)
  have hpmonic : (minpoly F9 (suEndHom g)).Monic := minpoly.monic (suEnd_isIntegral g)
  have hp1_monic : p1.Monic := hXm.of_mul_monic_left (hp1 ▸ hpmonic)
  have hp1_dvd_min : p1 ∣ minpoly F9 (suEndHom g) := ⟨X - 1, by
    rw [hp1]
    ring⟩
  have hp1_div : p1 ∣ (X ^ 7 - 1) := hp1_dvd_min.trans (minpoly_dvd_X7 g hg7)
  have hsqfree : Squarefree (minpoly F9 (suEndHom g)) :=
    (minpoly_separable g hg7).squarefree
  have hp1_not_div : ¬ (X - 1 : F9[X]) ∣ p1 := by
    intro hd
    have hu : IsUnit (X - 1 : F9[X]) :=
      hsqfree (X - 1) (by
        rw [hp1]
        exact mul_dvd_mul_left _ hd)
    have hXdeg : (X - 1 : F9[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : F9)
    rw [hXm.eq_one_of_isUnit hu, natDegree_one] at hXdeg
    exact absurd hXdeg (by norm_num)
  by_cases hp1u : IsUnit p1
  · rw [hp1_monic.eq_one_of_isUnit hp1u, mul_one] at hp1
    have ha := minpoly.aeval F9 (suEndHom g)
    rw [hp1, map_sub, aeval_X, map_one] at ha
    exact suEnd_ne_one g hg1 (sub_eq_zero.mp ha)
  · obtain ⟨q1, hq1m, hq1irr, hq1dvd⟩ := exists_monic_irreducible_factor p1 hp1u
    have hq1dvdX7 : q1 ∣ (X ^ 7 - 1) := hq1dvd.trans hp1_div
    have hp1deg : p1.natDegree ≤ 2 := by
      have hle3 := minpoly_natDegree_le_three g
      have hXdeg : (X - 1 : F9[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : F9)
      rw [hp1, natDegree_mul hXm.ne_zero hp1_monic.ne_zero, hXdeg] at hle3
      omega
    have hq1deg : q1.natDegree ≤ 2 :=
      (natDegree_le_of_dvd hq1dvd hp1_monic.ne_zero).trans hp1deg
    have hq1eq : q1 = X - 1 :=
      (irr_factor_X7_deg q1 hq1irr hq1m hq1dvdX7).resolve_right (by omega)
    exact hp1_not_div (hq1eq ▸ hq1dvd)

/-- **Crux.** For an order-`7` element `g`, the minimal polynomial of the
underlying endomorphism `T` is an irreducible cubic.  This is the regular
semisimplicity of the Singer element: `T` has no eigenvector over `GF(9)` (the
only `7`-th root of unity in `GF(9)` or `GF(81)` is `1`), so `minpoly` has no
irreducible factor of degree `1` (other than `X - 1`, excluded since `T ≠ 1`) or
`2`; being a separable divisor of `X^7 - 1` of degree `≤ 3`, it is a single
irreducible cubic. -/
lemma minpoly_irr_deg3 (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) :
    Irreducible (minpoly F9 (suEndHom g)) ∧
    (minpoly F9 (suEndHom g)).natDegree = 3 := by
  have hpmonic : (minpoly F9 (suEndHom g)).Monic := minpoly.monic (suEnd_isIntegral g)
  have hle3 : (minpoly F9 (suEndHom g)).natDegree ≤ 3 := minpoly_natDegree_le_three g
  have hpnu : ¬ IsUnit (minpoly F9 (suEndHom g)) := minpoly.not_isUnit F9 (suEndHom g)
  obtain ⟨q, hqm, hqirr, hqdvd⟩ := exists_monic_irreducible_factor _ hpnu
  have hqdvdX7 : q ∣ (X ^ 7 - 1) := hqdvd.trans (minpoly_dvd_X7 g hg7)
  have hqne : q ≠ X - 1 := fun h => not_X_sub_one_dvd_minpoly g hg7 hg1 (h ▸ hqdvd)
  have hqdeg3 : 3 ≤ q.natDegree :=
    (irr_factor_X7_deg q hqirr hqm hqdvdX7).resolve_left hqne
  have hqle : q.natDegree ≤ (minpoly F9 (suEndHom g)).natDegree :=
    natDegree_le_of_dvd hqdvd hpmonic.ne_zero
  have hpdeg : (minpoly F9 (suEndHom g)).natDegree = 3 :=
    le_antisymm hle3 (le_trans hqdeg3 hqle)
  -- p = q because the cofactor is monic of degree 0
  obtain ⟨c, hc⟩ := hqdvd
  have hcmonic : c.Monic := hqm.of_mul_monic_left (hc ▸ hpmonic)
  have hcdeg : c.natDegree = 0 := by
    have hmul := natDegree_mul hqm.ne_zero hcmonic.ne_zero
    rw [← hc, hpdeg] at hmul
    omega
  have hc1 : c = 1 := eq_one_of_monic_natDegree_zero hcmonic hcdeg
  rw [hc1, mul_one] at hc
  refine ⟨?_, hpdeg⟩
  rw [hc]
  exact hqirr

/-- **Crux (irreducibility).** For an order-`7` element `g`, the minimal
polynomial of the underlying endomorphism is irreducible. -/
lemma minpoly_irreducible_su (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) :
    Irreducible (minpoly F9 (suEndHom g)) := (minpoly_irr_deg3 g hg7 hg1).1

/-- **Crux (degree).** For an order-`7` element `g`, the minimal polynomial of the
underlying endomorphism has degree `3`. -/
lemma minpoly_natDegree_su (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) :
    (minpoly F9 (suEndHom g)).natDegree = 3 := (minpoly_irr_deg3 g hg7 hg1).2

/-- If `(aeval T r) v₀ = 0` for the cyclic vector `v₀ = Pi.single 0 1`, then the
minimal polynomial divides `r` (so the class of `r` in `AdjoinRoot` is zero). -/
lemma aeval_v0_eq_zero_dvd (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) (r : F9[X])
    (hr : (aeval (suEndHom g) r) (Pi.single 0 1 : Fin 3 → F9) = 0) :
    minpoly F9 (suEndHom g) ∣ r := by
  set T := suEndHom g
  have hv0 : (Pi.single 0 1 : Fin 3 → F9) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hpa : (aeval T (minpoly F9 T)) = 0 := minpoly.aeval F9 T
  by_contra hndvd
  obtain ⟨a, b, hab⟩ :=
    (minpoly_irreducible_su g hg7 hg1).coprime_iff_not_dvd.mpr hndvd
  apply hv0
  have hzero : (aeval T (a * minpoly F9 T + b * r)) (Pi.single 0 1 : Fin 3 → F9) = 0 := by
    simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hpa,
      LinearMap.zero_apply, hr, map_zero, add_zero]
  rw [hab, map_one, Module.End.one_apply] at hzero
  exact hzero

set_option maxHeartbeats 800000 in
/-- **Cyclic `F9`-linear equivalence.** `AdjoinRoot (minpoly F9 T) ≃ₗ[F9] (Fin 3 → F9)`
sending the class of a polynomial `r` to `(aeval T r) v₀`, where
`v₀ = Pi.single 0 1` is a cyclic vector.  This identifies the commutant field
`K = GF(729)` with the space via the cyclic-module structure. -/
lemma exists_cyclic_equiv (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) :
    ∃ e : (AdjoinRoot (minpoly F9 (suEndHom g))) ≃ₗ[F9] (Fin 3 → F9),
      ∀ r : F9[X],
        e (AdjoinRoot.mk _ r) = (aeval (suEndHom g) r) (Pi.single 0 1 : Fin 3 → F9) := by
  set T := suEndHom g with hT
  have hpa : (aeval T (minpoly F9 T)) = 0 := minpoly.aeval F9 T
  have hwd :
      ∀ a b : F9[X], AdjoinRoot.mk (minpoly F9 T) a = AdjoinRoot.mk (minpoly F9 T) b →
        (aeval T a) (Pi.single 0 1 : Fin 3 → F9) =
        (aeval T b) (Pi.single 0 1 : Fin 3 → F9) := by
    intro a b hab
    rw [AdjoinRoot.mk_eq_mk] at hab
    obtain ⟨s, hs⟩ := hab
    have hab2 : a = b + minpoly F9 T * s := by linear_combination hs
    rw [hab2, map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hpa,
      LinearMap.zero_apply, add_zero]
  let e0 : AdjoinRoot (minpoly F9 T) →ₗ[F9] (Fin 3 → F9) :=
    { toFun := fun x => Quotient.liftOn' x
        (fun r => (aeval T r) (Pi.single 0 1 : Fin 3 → F9))
        (fun a b hab => hwd a b (Quotient.sound hab))
      map_add' := by
        rintro x y
        induction x using AdjoinRoot.induction_on with | _ a =>
        induction y using AdjoinRoot.induction_on with | _ b =>
        show
          (aeval T (a + b)) (Pi.single 0 1) =
            (aeval T a) (Pi.single 0 1) + (aeval T b) (Pi.single 0 1)
        rw [map_add, LinearMap.add_apply]
      map_smul' := by
        rintro c x
        induction x using AdjoinRoot.induction_on with | _ a =>
        have key :
            c • AdjoinRoot.mk (minpoly F9 T) a =
              AdjoinRoot.mk (minpoly F9 T) (C c * a) := by
          rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply,
            ← map_mul]
        show Quotient.liftOn' (c • AdjoinRoot.mk (minpoly F9 T) a)
          (fun r => (aeval T r) (Pi.single 0 1 : Fin 3 → F9)) _ = _
        rw [key]
        show (aeval T (C c * a)) (Pi.single 0 1) = c • (aeval T a) (Pi.single 0 1)
        rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply] }
  have he0 : ∀ r : F9[X], e0 (AdjoinRoot.mk (minpoly F9 T) r)
      = (aeval T r) (Pi.single 0 1 : Fin 3 → F9) := fun r => rfl
  have hinj : Function.Injective e0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using AdjoinRoot.induction_on with | _ r =>
    rw [he0] at hx
    exact AdjoinRoot.mk_eq_zero.mpr (aeval_v0_eq_zero_dvd g hg7 hg1 r hx)
  have hfr :
      Module.finrank F9 (AdjoinRoot (minpoly F9 T)) =
      Module.finrank F9 (Fin 3 → F9) := by
    have h1 : Module.finrank F9 (AdjoinRoot (minpoly F9 T)) = (minpoly F9 T).natDegree := by
      rw [(AdjoinRoot.powerBasis (minpoly.ne_zero (suEnd_isIntegral g))).finrank,
        AdjoinRoot.powerBasis_dim]
    rw [h1, Module.finrank_pi, Fintype.card_fin, minpoly_natDegree_su g hg7 hg1]
  have : FiniteDimensional F9 (AdjoinRoot (minpoly F9 T)) :=
    Module.Basis.finiteDimensional_of_finite
      (AdjoinRoot.powerBasis (minpoly.ne_zero (suEnd_isIntegral g))).basis
  exact ⟨LinearMap.linearEquivOfInjective e0 hinj hfr, fun r => he0 r⟩

/-- An endomorphism commuting with `T` commutes with every polynomial in `T`. -/
lemma commute_aeval_aux (S T : Module.End F9 (Fin 3 → F9))
    (hc : Commute S T) (r : F9[X]) :
    Commute S (aeval T r) := by
  induction r using Polynomial.induction_on with
  | C a =>
      rw [aeval_C]
      exact Algebra.commute_algebraMap_right a S
  | add p q hp hq =>
      rw [map_add]
      exact hp.add_right hq
  | monomial n a _ =>
      rw [map_mul, aeval_C, map_pow, aeval_X]
      exact (Algebra.commute_algebraMap_right a S).mul_right (hc.pow_right (n + 1))

/-- **Intertwining (abstract).** Via the cyclic equivalence `e`, an endomorphism
`S` commuting with `T` acts as multiplication by the scalar `c = e.symm (S (e 1))`
in the commutant field: `S (e k) = e (k * c)`. -/
lemma intertwine_aux (T S : Module.End F9 (Fin 3 → F9)) (v0 : Fin 3 → F9)
    (e : AdjoinRoot (minpoly F9 T) ≃ₗ[F9] (Fin 3 → F9))
    (he : ∀ r : F9[X], e (AdjoinRoot.mk _ r) = (aeval T r) v0)
    (hc : Commute S T) (k : AdjoinRoot (minpoly F9 T)) :
    S (e k) = e (k * e.symm (S (e 1))) := by
  have he1 : e 1 = v0 := by
    simpa only [map_one, Module.End.one_apply] using he (1 : F9[X])
  obtain ⟨s, hs⟩ := AdjoinRoot.mk_surjective (e.symm (S (e 1)))
  have hSv0 : S v0 = (aeval T s) v0 := by
    have h1 : e (AdjoinRoot.mk (minpoly F9 T) s) = S (e 1) := by
      rw [hs, LinearEquiv.apply_symm_apply]
    rw [he s, he1] at h1
    exact h1.symm
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective k
  rw [he r]
  have hcomm : Commute S (aeval T r) := commute_aeval_aux S T hc r
  have hstep : S ((aeval T r) v0) = (aeval T r) (S v0) := by
    have := DFunLike.congr_fun hcomm.eq v0
    simpa only [Module.End.mul_apply] using this
  rw [hstep, hSv0, ← Module.End.mul_apply, ← map_mul, ← he (r * s), map_mul, hs]

set_option maxHeartbeats 800000 in
/-- **Abstract centralizer cardinality bound.**  For a faithful representation
`ψ : Γ →* End_{F9}(F9³)` of a finite group and an element `g₀` whose minimal
polynomial is irreducible (so the commutant `K = F9[ψ g₀]` is a field), with a
cyclic equivalence `e`, the centralizer of `g₀` embeds into `Kˣ`. -/
lemma card_dvd_aux {Γ : Type*} [Group Γ] [Finite Γ]
    (ψ : Γ →* Module.End F9 (Fin 3 → F9)) (hψ : Function.Injective ψ)
    (g₀ : Γ) (v0 : Fin 3 → F9)
    [Fact (Irreducible (minpoly F9 (ψ g₀)))]
    (e : AdjoinRoot (minpoly F9 (ψ g₀)) ≃ₗ[F9] (Fin 3 → F9))
    (he : ∀ r : F9[X], e (AdjoinRoot.mk _ r) = (aeval (ψ g₀) r) v0) :
    Nat.card (Subgroup.centralizer ({g₀} : Set Γ))
      ∣ Nat.card (AdjoinRoot (minpoly F9 (ψ g₀)))ˣ := by
  have : FiniteDimensional F9 (AdjoinRoot (minpoly F9 (ψ g₀))) :=
    Module.Basis.finiteDimensional_of_finite
      (AdjoinRoot.powerBasis (Fact.out (p := Irreducible (minpoly F9 (ψ g₀)))).ne_zero).basis
  have : Finite (AdjoinRoot (minpoly F9 (ψ g₀))) := Module.finite_of_finite F9
  have hcomm : ∀ h : Subgroup.centralizer ({g₀} : Set Γ), Commute (ψ (h : Γ)) (ψ g₀) := by
    intro h
    have hh : (h : Γ) * g₀ = g₀ * (h : Γ) := by
      have := h.2
      rw [Subgroup.mem_centralizer_iff] at this
      exact (this g₀ (Set.mem_singleton g₀)).symm
    have := congrArg ψ hh
    rwa [map_mul, map_mul] at this
  let φ : Subgroup.centralizer ({g₀} : Set Γ) →* AdjoinRoot (minpoly F9 (ψ g₀)) :=
    { toFun := fun h => e.symm ((ψ (h : Γ)) (e 1))
      map_one' := by simp
      map_mul' := fun h1 h2 => by
        have hi := intertwine_aux (ψ g₀) (ψ (h1 : Γ)) v0 e he (hcomm h1)
          (e.symm ((ψ (h2 : Γ)) (e 1)))
        rw [LinearEquiv.apply_symm_apply] at hi
        show e.symm ((ψ ((h1 * h2 : Subgroup.centralizer _) : Γ)) (e 1)) = _
        rw [Subgroup.coe_mul, map_mul]
        show e.symm ((ψ (h1 : Γ)) ((ψ (h2 : Γ)) (e 1))) = _
        rw [hi, LinearEquiv.symm_apply_apply, mul_comm] }
  have hφinj : Function.Injective φ := by
    intro h1 h2 hheq
    have hval : e.symm ((ψ (h1 : Γ)) (e 1)) = e.symm ((ψ (h2 : Γ)) (e 1)) := hheq
    apply Subtype.ext
    apply hψ
    refine LinearMap.ext fun w => ?_
    obtain ⟨k, rfl⟩ := e.surjective w
    rw [intertwine_aux (ψ g₀) (ψ (h1 : Γ)) v0 e he (hcomm h1) k,
      intertwine_aux (ψ g₀) (ψ (h2 : Γ)) v0 e he (hcomm h2) k, hval]
  have hinju : Function.Injective φ.toHomUnits := by
    intro a b hab
    apply hφinj
    have := congrArg Units.val hab
    rwa [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits] at this
  exact Subgroup.card_dvd_of_injective φ.toHomUnits hinju

set_option maxHeartbeats 800000 in
/-- **Abstract involution dichotomy.**  An element `h` with `ψ h` commuting with
`ψ g₀` and `(ψ h)² = 1` has `ψ h = ±1` (the only involutions in the commutant
field). -/
lemma involution_aux {Γ : Type*} [Group Γ]
    (ψ : Γ →* Module.End F9 (Fin 3 → F9))
    (g₀ : Γ) (v0 : Fin 3 → F9)
    [Fact (Irreducible (minpoly F9 (ψ g₀)))]
    (e : AdjoinRoot (minpoly F9 (ψ g₀)) ≃ₗ[F9] (Fin 3 → F9))
    (he : ∀ r : F9[X], e (AdjoinRoot.mk _ r) = (aeval (ψ g₀) r) v0)
    (h : Γ) (hc : Commute (ψ h) (ψ g₀)) (h2 : (ψ h) ^ 2 = 1) :
    ψ h = 1 ∨ ψ h = -1 := by
  set c := e.symm ((ψ h) (e 1)) with hcdef
  have hint : ∀ k, (ψ h) (e k) = e (k * c) := intertwine_aux (ψ g₀) (ψ h) v0 e he hc
  have hc2 : c * c = 1 := by
    have e1 : (ψ h) ((ψ h) (e 1)) = e (1 * c * c) := by rw [hint 1, hint (1 * c)]
    have e2 : (ψ h) ((ψ h) (e 1)) = e 1 := by
      have : ((ψ h) ^ 2) (e 1) = e 1 := by
        rw [h2]
        rfl
      rwa [sq, Module.End.mul_apply] at this
    rw [e2] at e1
    have : (1 : AdjoinRoot (minpoly F9 (ψ g₀))) = 1 * c * c := e.injective e1
    linear_combination -this
  rcases mul_self_eq_one_iff.mp hc2 with hc1 | hcm1
  · left
    refine LinearMap.ext fun w => ?_
    obtain ⟨k, rfl⟩ := e.surjective w
    rw [hint k, hc1, mul_one]
    rfl
  · right
    refine LinearMap.ext fun w => ?_
    obtain ⟨k, rfl⟩ := e.surjective w
    rw [hint k, hcm1, mul_neg, mul_one, map_neg]
    rfl

/-- **Core upper bound.** The centralizer of an order-`7` element has cardinality
dividing `728 = |GF(729)^×|`, via the injection into the multiplicative group of
the commutant field. -/
lemma centralizer_card_dvd_728 (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) :
    Nat.card (Subgroup.centralizer ({g} : Set specialUnitaryGroup)) ∣ 728 := by
  have : Fact (Irreducible (minpoly F9 (suEndHom g))) := ⟨minpoly_irreducible_su g hg7 hg1⟩
  obtain ⟨e, he⟩ := exists_cyclic_equiv g hg7 hg1
  have hdvd := card_dvd_aux suEndHom suEndHom_injective g (Pi.single 0 1) e he
  have hcardK : Nat.card (AdjoinRoot (minpoly F9 (suEndHom g))) = 729 := by
    rw [card_adjoinRoot_irreducible _ (minpoly_irreducible_su g hg7 hg1),
      minpoly_natDegree_su g hg7 hg1]
    norm_num
  have hcardKu : Nat.card (AdjoinRoot (minpoly F9 (suEndHom g)))ˣ = 728 := by
    rw [Nat.card_units, hcardK]
  rwa [hcardKu] at hdvd

/-- **No involution.** Any element of the centralizer of an order-`7` element
whose square is the identity is itself the identity (the unique involution `-id`
of the commutant field is not special unitary). -/
lemma centralizer_no_involution (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1)
    (h : specialUnitaryGroup)
    (hh : h ∈ Subgroup.centralizer ({g} : Set specialUnitaryGroup))
    (h2 : h ^ 2 = 1) : h = 1 := by
  have : Fact (Irreducible (minpoly F9 (suEndHom g))) := ⟨minpoly_irreducible_su g hg7 hg1⟩
  obtain ⟨e, he⟩ := exists_cyclic_equiv g hg7 hg1
  have hc : Commute (suEndHom h) (suEndHom g) := by
    rw [Subgroup.mem_centralizer_iff] at hh
    have hcomm := (hh g (Set.mem_singleton g)).symm
    have := congrArg suEndHom hcomm
    rwa [map_mul, map_mul] at this
  have hsq : (suEndHom h) ^ 2 = 1 := by rw [← map_pow, h2, map_one]
  rcases involution_aux suEndHom g (Pi.single 0 1) e he h hc hsq with hone | hneg
  · exact suEndHom_injective (by rw [hone, map_one])
  · exfalso
    -- `suEndHom h = -1` would force `det = (-1)³ = -1 ≠ 1`, contradicting `h ∈ SU`.
    have hdet1 : LinearEquiv.det (toLinearEquiv h) = 1 :=
      (mem_specialUnitaryGroup_iff (h : unitaryGroup)).mp h.2
    have hcoe := LinearEquiv.coe_det (toLinearEquiv h)
    rw [hdet1] at hcoe
    have hdetneg : LinearMap.det (suEndHom h) = -1 := by
      rw [hneg, show (-1 : Module.End F9 (Fin 3 → F9)) = (-1 : F9) • LinearMap.id by
        ext x
        simp, LinearMap.det_smul, LinearMap.det_id, mul_one,
        Module.finrank_pi, Fintype.card_fin, Odd.neg_one_pow (by decide : Odd 3)]
    rw [show (toLinearEquiv h).toLinearMap = suEndHom h from rfl, hdetneg, Units.val_one] at hcoe
    have h2ne : (2 : F9) ≠ 0 := by
      have : ((2 : ℕ) : F9) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff F9 3]
        decide
      simpa using this
    exact h2ne (by linear_combination hcoe)

end FixedElement

/-- **Centralizer of an order-seven element (cyclic-generator version).** -/
theorem centralizer_order_seven_eq_seven
    (g : specialUnitaryGroup) (hg : orderOf g = 7) :
    Nat.card (Subgroup.centralizer ({g} : Set specialUnitaryGroup)) = 7 := by
  have hg7 : g ^ 7 = 1 := hg ▸ pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    norm_num at hg
  set C := Subgroup.centralizer ({g} : Set specialUnitaryGroup) with hC
  -- lower bound: 7 ∣ |C|
  have h_lower : 7 ∣ Nat.card C := by
    have hle : Subgroup.zpowers g ≤ C := by
      rw [hC, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      subst hm
      rfl
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hg] at hdvd
  -- |C| ∣ 728 (commutant field units)
  have h728 : Nat.card C ∣ 728 := centralizer_card_dvd_728 g hg7 hg1
  -- |C| ∣ 6048 (Lagrange)
  have h6048 : Nat.card C ∣ 6048 := by
    have hdvd := Subgroup.card_subgroup_dvd_card C
    rwa [card_specialUnitaryGroup] at hdvd
  -- hence |C| ∣ 56
  have h56 : Nat.card C ∣ 56 := (Nat.dvd_gcd h728 h6048).trans (by norm_num)
  -- no involution ⇒ |C| odd
  have h_no_even : ¬ (2 ∣ Nat.card C) := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    have : Fintype C := Fintype.ofFinite _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := C) 2
      (by
        rw [← Nat.card_eq_fintype_card]
        exact h2)
    have hxx : x ^ 2 = 1 := by
      have hpow := pow_orderOf_eq_one x
      rwa [hx] at hpow
    have hx2 : (x : specialUnitaryGroup) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, hxx, OneMemClass.coe_one]
    have hxne1 : x ≠ 1 := by
      intro hx1
      rw [hx1, orderOf_one] at hx
      norm_num at hx
    have hxne : (x : specialUnitaryGroup) ≠ 1 :=
      fun h => hxne1 (OneMemClass.coe_eq_one.mp h)
    exact hxne (centralizer_no_involution g hg7 hg1 (x : specialUnitaryGroup) x.2 hx2)
  -- finite divisor endgame
  have hle56 : Nat.card C ≤ 56 := Nat.le_of_dvd (by norm_num) h56
  interval_cases hN : Nat.card C <;> omega

set_option synthInstance.maxHeartbeats 400000 in
/-- **Self-centralizing Sylow `7`-torus.**  Each Sylow `7`-subgroup of geometric
`SU(3,3)` has a centralizer of order exactly `7`. -/
theorem card_sylow7_centralizer_su
    (P : Sylow 7 specialUnitaryGroup) :
    Nat.card (Subgroup.centralizer
      ((P : Subgroup specialUnitaryGroup) : Set specialUnitaryGroup)) = 7 := by
  obtain ⟨g, hg⟩ :
      ∃ g : specialUnitaryGroup,
        Subgroup.zpowers g = (P : Subgroup specialUnitaryGroup) ∧ orderOf g = 7 := by
    -- Since `P` is a Sylow `7`-subgroup, it is cyclic of order `7`.
    have h_card : Nat.card (P : Subgroup specialUnitaryGroup) = 7 :=
      sylow7_card card_specialUnitaryGroup_fintype P
    have hP_cyclic : IsCyclic (P : Subgroup specialUnitaryGroup) :=
      isCyclic_of_prime_card h_card
    obtain ⟨γ, hγ⟩ := hP_cyclic.exists_generator
    have hord : orderOf γ = 7 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hγ, h_card]
    refine ⟨(γ : specialUnitaryGroup), ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨n, rfl⟩
        exact Subgroup.zpow_mem _ γ.2 _
      · intro hx
        obtain ⟨n, hn⟩ := hγ ⟨x, hx⟩
        exact ⟨n, by simpa [Subtype.ext_iff] using hn⟩
    · have hcoe : orderOf ((γ : specialUnitaryGroup)) = orderOf γ :=
        orderOf_injective (P : Subgroup specialUnitaryGroup).subtype Subtype.coe_injective γ
      rw [hcoe, hord]
  convert centralizer_order_seven_eq_seven g hg.2 using 1
  rw [← hg.1, Subgroup.coe_zpowers]
  congr! 2
  ext
  simp +decide [Subgroup.mem_centralizer_iff]
  exact ⟨fun h => by simpa using h 1, fun h a => Commute.zpow_left (by simpa using h) a⟩

/-- Sylow `7`-subgroups of geometric `SU(3,3)` are self-centralizing. -/
theorem hasSelfCentralizingSylow7_specialUnitaryGroup :
    HasSelfCentralizingSylow7 specialUnitaryGroup :=
  card_sylow7_centralizer_su

/-- **Order-seven count in geometric `SU(3,3)`.** -/
theorem card_orderOf_eq_seven_su :
    (Finset.univ.filter
      (fun g : specialUnitaryGroup => orderOf g = 7)).card = 1728 :=
  card_orderOf_eq_seven_su_of_hasSelfCentralizingSylow7
    hasSelfCentralizingSylow7_specialUnitaryGroup

end PSU33

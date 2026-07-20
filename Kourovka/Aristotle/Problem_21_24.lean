/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.BourbakiWitt
import Mathlib.Tactic.Bound

/-!
# Kourovka Notebook Problem 21.24

## Problem Statement

For a finite group `G`, the **power graph** `P(G)` has vertex set `G`
with edges `{x, y}` for all `x ≠ y ∈ G` such that either
`x ∈ ⟨y⟩` or `y ∈ ⟨x⟩`.

**Question**: Is it true that, for every finite group `G`, if `P(G)` is a cograph,
then `P(G)` is chordal?

**Answer**: Yes.

## Proof Outline

A cograph has no induced `P₄`. Being chordal means no induced cycle of length `≥ 4`.
Since any induced cycle of length `≥ 5` contains an induced `P₄` (general graph theory),
it suffices to show that an induced `C₄` in the power graph always yields an induced P₄.

Given a `C₄` `a-b-c-d` in the power graph with `a ≁ c` and `b ≁ d`, case analysis on
the containment of cyclic subgroups shows that (up to symmetry) both `⟨a⟩` and `⟨c⟩`
are contained in both `⟨b⟩` and `⟨d⟩`, while `⟨b⟩` and `⟨d⟩` are incomparable.
A number-theoretic argument using prime factorizations then produces a fifth element
`b' ∈ ⟨b⟩` such that `b' ∉ ⟨d⟩` and one of `a, c` is not in `⟨b'⟩`, yielding a `P₄`.
-/

open Subgroup

/-- The power graph of a group `G`: distinct elements `x, y` are adjacent iff one is a power of
the other. -/
def powerGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj x y := x ≠ y ∧ (x ∈ zpowers y ∨ y ∈ zpowers x)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ ⟨h, _⟩ ↦ h rfl⟩

/-! ### Graph Theory Definitions -/

/-- A graph has an induced `P₄` (path on 4 vertices `a-b-c-d`). -/
def HasInducedP4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b c d : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧
    ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b d

/-- A graph is a **cograph** if it has no induced `P₄`. -/
def IsCograph {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬HasInducedP4 G

/-- A graph has an induced cycle of length `n` (for `n ≥ 3`). -/
def HasInducedCycle {V : Type*} (G : SimpleGraph V) (n : ℕ) (hn : 3 ≤ n) : Prop :=
  ∃ f : Fin n → V,
    Function.Injective f ∧
    (∀ i : Fin n, G.Adj (f i) (f ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩)) ∧
    ∀ i j : Fin n, G.Adj (f i) (f j) →
      j.val = (i.val + 1) % n ∨ i.val = (j.val + 1) % n

/-- A graph is **chordal** if it has no induced cycle of length `≥ 4`. -/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, ∀ hn : 4 ≤ n, ¬HasInducedCycle G n (by omega)

/-! ### General Graph Theory -/

/-- An induced cycle of length `n ≥ 5` contains an induced `P₄`. -/
theorem hasInducedP4_of_hasInducedCycle_ge5 {V : Type*} (G : SimpleGraph V)
    {n : ℕ} (hn : 5 ≤ n) (hcycle : HasInducedCycle G n (by omega)) :
    HasInducedP4 G := by
  obtain ⟨f, hf_inj, hf_adj, hf_only⟩ := hcycle
  refine ⟨f ⟨0, by linarith⟩, f ⟨1, by linarith⟩, f ⟨2, by linarith⟩,
    f ⟨3, by linarith⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  any_goals
    have := hf_adj ⟨0, by linarith⟩; have := hf_adj ⟨1, by linarith⟩
    have := hf_adj ⟨2, by linarith⟩; have := hf_adj ⟨3, by linarith⟩
    norm_num [Nat.mod_eq_of_lt (by linarith : 1 < n),
      Nat.mod_eq_of_lt (by linarith : 2 < n),
      Nat.mod_eq_of_lt (by linarith : 3 < n)] at *; tauto
  · by_contra h_contra
    have := hf_only ⟨0, by linarith⟩ ⟨2, by linarith⟩ h_contra
    norm_num at this
    rcases n with (_ | _ | _ | _ | _ | n) <;> cases this <;> cases ‹_› <;> contradiction
  · intro h; specialize hf_only _ _ h
    rcases n with (_ | _ | _ | _ | _ | n) <;> norm_num [Nat.mod_eq_of_lt] at * <;> contradiction
  · intro h; specialize hf_only _ _ h; norm_num at hf_only
    rcases n with (_ | _ | _ | _ | _ | n) <;>
      simp +arith +decide [Nat.mod_eq_of_lt] at hf_only hn ⊢

/-- A cograph has no induced cycle of length `≥ 5`. -/
theorem isCograph_imp_no_cycle_ge5 {V : Type*} (G : SimpleGraph V)
    (hco : IsCograph G) (n : ℕ) (hn : 5 ≤ n) : ¬HasInducedCycle G n (by omega) :=
  fun hcycle ↦ hco (hasInducedP4_of_hasInducedCycle_ge5 G hn hcycle)

/-! ### Number Theory Helpers -/

/-- If `α` and `γ` are incomparable under divisibility, there exist distinct primes `p ∣ α` and
 `q ∣ γ`. -/
lemma exists_distinct_prime_dvd_of_incomparable {α γ : ℕ}
    (hαγ : ¬(α ∣ γ)) (hγα : ¬(γ ∣ α)) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ p ∣ α ∧ q ∣ γ := by
  obtain ⟨p, k, hp_prime, hp_k_alpha, hp_k_gamma⟩ :
      ∃ p k : ℕ, Nat.Prime p ∧ p ^ k ∣ α ∧ ¬(p ^ k ∣ γ) := by
    by_contra h_contra
    push_neg at h_contra
    exact hαγ ((Nat.dvd_iff_prime_pow_dvd_dvd γ α).mpr h_contra)
  obtain ⟨q, e, hq_prime, hq_e_gamma, hq_e_alpha⟩ :
      ∃ q e : ℕ, Nat.Prime q ∧ q ^ e ∣ γ ∧ ¬(q ^ e ∣ α) := by
    have := Nat.dvd_iff_prime_pow_dvd_dvd α γ; simp_all
  refine ⟨p, q, hp_prime, hq_prime, ?_, ?_, ?_⟩
  · rintro rfl
    exact hq_e_alpha (dvd_trans (pow_dvd_pow _ (show e ≤ k from le_of_not_gt fun h ↦
      hp_k_gamma <| dvd_trans (pow_dvd_pow _ h.le) hq_e_gamma)) hp_k_alpha)
  · exact dvd_trans (dvd_pow_self _ (by aesop)) hp_k_alpha
  · exact dvd_trans (dvd_pow_self _ (by aesop)) hq_e_gamma

/-- Given incomparable divisors `α, γ` of `k ∣ n` with `k < n`, there exists `d ∣ n`
with `d ∤ k` and `¬(α ∣ d) ∨ ¬(γ ∣ d)`. -/
lemma exists_dvd_not_dvd_incompatible {n k α γ : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hk_dvd : k ∣ n) (hk_lt : k < n)
    (hα_dvd : α ∣ k) (hγ_dvd : γ ∣ k)
    (hαγ : ¬(α ∣ γ)) (hγα : ¬(γ ∣ α)) :
    ∃ d : ℕ, d ∣ n ∧ ¬(d ∣ k) ∧ (¬(α ∣ d) ∨ ¬(γ ∣ d)) := by
  obtain ⟨p, q, hp, hq, hpq, hpα, hqγ⟩ := exists_distinct_prime_dvd_of_incomparable hαγ hγα
  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : ℕ, Nat.Prime r ∧ n.factorization r > k.factorization r := by
    contrapose! hk_lt
    refine Nat.le_of_dvd hk ?_
    exact Nat.factorization_le_iff_dvd (by positivity) (by positivity) |>.1 fun r ↦ by
      by_cases hr : Nat.Prime r <;> aesop
  refine ⟨r ^ (n.factorization r), Nat.ordProj_dvd _ _, ?_, ?_⟩ <;> simp_all
  · rw [Nat.Prime.pow_dvd_iff_le_factorization] <;> aesop
  · contrapose! hpq; simp_all [Nat.Prime.dvd_iff_not_coprime]
    have := Nat.Prime.dvd_of_dvd_pow hp (dvd_trans (Nat.dvd_of_mod_eq_zero
      (Nat.mod_eq_zero_of_dvd <| Nat.Prime.dvd_iff_not_coprime hp |>.2 hpα)) hpq.1)
    have := Nat.Prime.dvd_of_dvd_pow hq (dvd_trans (Nat.dvd_of_mod_eq_zero
      (Nat.mod_eq_zero_of_dvd <| Nat.Prime.dvd_iff_not_coprime hq |>.2 hqγ)) hpq.2)
    simp_all [Nat.prime_dvd_prime_iff_eq]

/-! ### Group Theory Helpers -/

/-- If `x ∈ zpowers b` and `zpowers b ≤ H`, then `x ∈ H`. -/
lemma mem_of_mem_zpowers_of_le {G : Type*} [Group G]
    {x b : G} {H : Subgroup G} (hx : x ∈ zpowers b)
    (hle : zpowers b ≤ H) : x ∈ H :=
  hle hx

/-- In a finite cyclic group, for any `d ∣ Nat.card G` with `0 < d`, there exists an element of
order `d`. -/
lemma exists_orderOf_eq_of_dvd_of_isCyclic {G : Type*} [Group G] [Finite G]
    [IsCyclic G] {d : ℕ} (hd : d ∣ Nat.card G) (hd_pos : 0 < d) :
    ∃ g : G, orderOf g = d := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k * d = Nat.card G := ⟨Nat.card G / d, Nat.div_mul_cancel hd⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  use g ^ k
  have hd_ne : d ≠ 0 := hd_pos.ne'
  rw [orderOf_pow'] <;> norm_num [hd_ne, hk.symm]
  · rw [show orderOf g = Nat.card G from ?_, Nat.gcd_comm]
    · rw [Nat.gcd_eq_left (dvd_of_mul_right_eq _ hk), Nat.div_eq_of_eq_mul_left] <;>
        nlinarith [Nat.pos_of_ne_zero (show Nat.card G ≠ 0 from Nat.ne_of_gt Nat.card_pos)]
    · rw [orderOf_eq_card_of_forall_mem_zpowers hg]
  · nlinarith [show 0 < Nat.card G from Nat.card_pos]

/-- In `zpowers b`, there exists an element of order `d` whenever `d ∣ orderOf b` and `d > 0`. -/
lemma exists_mem_zpowers_orderOf_eq {G : Type*} [Group G] [Finite G]
    {b : G} {d : ℕ} (hd : d ∣ orderOf b) (hd_pos : 0 < d) :
    ∃ g : G, g ∈ zpowers b ∧ orderOf g = d := by
  have h_subgroup : ∃ g : zpowers b, orderOf g = d := by
    have h_card : Nat.card (zpowers b) = orderOf b := by rw [Nat.card_zpowers]
    have := exists_orderOf_eq_of_dvd_of_isCyclic
      (show d ∣ Nat.card (zpowers b) from h_card.symm ▸ hd) hd_pos
    aesop
  obtain ⟨g, hg⟩ := h_subgroup; use g; aesop

/-! ### Power Graph: C₄ implies P₄ -/

/-- From a path `a — b — c` in the power graph with `a ≁ c`, conclude that `a, c ∈ ⟨b⟩` or
`b ∈ ⟨a⟩ ∧ b ∈ ⟨c⟩`. -/
lemma powerGraph_path_fork {G : Type*} [Group G]
    {a b c : G}
    (hab : a ∈ zpowers b ∨ b ∈ zpowers a)
    (hbc : b ∈ zpowers c ∨ c ∈ zpowers b)
    (hac : ¬(a ∈ zpowers c ∨ c ∈ zpowers a)) :
    (a ∈ zpowers b ∧ c ∈ zpowers b) ∨
    (b ∈ zpowers a ∧ b ∈ zpowers c) := by
  grind +suggestions

/-- In a cyclic group `⟨b⟩`, if `a, c ∈ ⟨b⟩` and `a ∉ ⟨c⟩`, then `orderOf a ∤ orderOf c`. -/
lemma not_dvd_orderOf_of_not_mem_zpowers {G : Type*} [Group G] [Finite G]
    {a c b : G} (ha : a ∈ zpowers b) (hc : c ∈ zpowers b)
    (h : a ∉ zpowers c) : ¬(orderOf a ∣ orderOf c) := by
  obtain ⟨i, hi⟩ : ∃ i : ℤ, a = b ^ i :=
    mem_zpowers_iff.mp ha |>.imp fun _ ↦ Eq.symm
  obtain ⟨j, hj⟩ : ∃ j : ℤ, c = b ^ j :=
    mem_zpowers_iff.mp hc |>.imp fun j hj ↦ hj.symm
  contrapose! h; simp_all [orderOf_dvd_iff_pow_eq_one]
  have h_cong : i * orderOf (b ^ j) ≡ 0 [ZMOD orderOf b] := by
    rw [← zpow_natCast, ← zpow_mul] at h
    exact zpow_eq_one_iff_modEq.mp h
  have h_cong' : i * (orderOf b / Nat.gcd (orderOf b) (Int.natAbs j)) ≡ 0
      [ZMOD orderOf b] := by
    have h_order_gj : ∀ m : ℕ, orderOf (b ^ m) = orderOf b / Nat.gcd (orderOf b) m :=
      fun m ↦ orderOf_pow b
    cases j <;> simp_all
  have h_div : i ≡ 0 [ZMOD Nat.gcd (orderOf b) (Int.natAbs j)] := by
    rw [Int.modEq_zero_iff_dvd] at *
    refine Int.dvd_of_mul_dvd_mul_right (show ((orderOf b) : ℤ) / (Nat.gcd (orderOf b)
      (Int.natAbs j)) ≠ 0 from ?_) ?_
    · have := Nat.le_of_dvd (orderOf_pos _) (Nat.gcd_dvd_left (orderOf b) (Int.natAbs j))
      exact ne_of_gt (Int.le_ediv_of_mul_le
        (Nat.cast_pos.mpr (Nat.gcd_pos_of_pos_left _ (orderOf_pos _))) (by nlinarith))
    · rw [Int.mul_ediv_cancel' (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))]; aesop
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h_div
  have h_exp : b ^ i = (b ^ (Nat.gcd (orderOf b) (Int.natAbs j))) ^ k := by rw [hk, zpow_mul]; norm_cast
  have h_pow : ∃ m : ℤ, b ^ (Nat.gcd (orderOf b) (Int.natAbs j)) = (b ^ j) ^ m := by
    have := Nat.gcd_eq_gcd_ab (orderOf b) (Int.natAbs j)
    use Nat.gcdB (orderOf b) (Int.natAbs j) * (if j < 0 then -1 else 1)
    split_ifs <;> simp_all [← zpow_mul, ← zpow_natCast]
    · simp [zpow_add, zpow_mul, abs_of_neg ‹_›]
    · simp [abs_of_nonneg ‹_›, zpow_add, zpow_mul]
  aesop

/-- If `b ∉ zpowers d`, then `Nat.card (zpowers b ⊓ zpowers d) < Nat.card (zpowers b)`. -/
lemma natCard_inf_zpowers_lt {G : Type*} [Group G] [Finite G]
    {b d : G} (hbd : b ∉ zpowers d) :
    Nat.card ↑(zpowers b ⊓ zpowers d) <
      Nat.card ↑(zpowers b) := by
  convert Set.ncard_lt_ncard (show (zpowers b ⊓ zpowers d : Set G) <
    zpowers b from Set.ssubset_iff_subset_ne.2 ⟨by aesop, by aesop⟩)

/-- A witness element `b'` gives a `P₄` `b'-b-x-d`. -/
lemma P4_from_witness_left {G : Type*} [Group G] [Finite G]
    {x b d b' : G}
    (hb'_mem : b' ∈ zpowers b)
    (hx_b : x ∈ zpowers b)
    (hx_d : x ∈ zpowers d)
    (hb'_not_d : b' ∉ zpowers d)
    (hd_not_b : d ∉ zpowers b)
    (hb_not_d : b ∉ zpowers d)
    (hx_not_b' : x ∉ zpowers b')
    (hb'_not_x : b' ∉ zpowers x)
    (hxb : x ≠ b) (hxd : x ≠ d) (hb'b : b' ≠ b) (hb'd : b' ≠ d)
    (hbd : b ≠ d) :
    HasInducedP4 (powerGraph G) := by
  refine ⟨b', b, x, d, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
  all_goals unfold powerGraph; simp [*, mem_zpowers_iff]
  · grind
  · bound

/-- Given the "Case I" configuration of a `C₄` (both `a, c ∈ ⟨b⟩` and `a, c ∈ ⟨d⟩`),
construct an element `b'` yielding an induced `P₄`. -/
lemma powerGraph_C4_case_I_witness {G : Type*} [Group G] [Finite G]
    {a b c d : G}
    (ha_b : a ∈ zpowers b) (hc_b : c ∈ zpowers b)
    (hc_d : c ∈ zpowers d) (ha_d : a ∈ zpowers d)
    (hac₁ : a ∉ zpowers c) (hac₂ : c ∉ zpowers a)
    (hbd₁ : b ∉ zpowers d) (hbd₂ : d ∉ zpowers b)
    (hab : a ≠ b) (hcd : c ≠ d) (hcb : c ≠ b) (had : a ≠ d) :
    HasInducedP4 (powerGraph G) := by
  set H := zpowers b ⊓ zpowers d
  have ha_H : a ∈ H := ⟨ha_b, ha_d⟩
  have hc_H : c ∈ H := ⟨hc_b, hc_d⟩
  have hα_dvd : orderOf a ∣ Nat.card H := orderOf_dvd_natCard H ha_H
  have hγ_dvd : orderOf c ∣ Nat.card H := orderOf_dvd_natCard H hc_H
  have hH_dvd : Nat.card H ∣ orderOf b := by rw [← Nat.card_zpowers]; exact card_dvd_of_le inf_le_left
  have hH_lt : Nat.card H < orderOf b := by
    convert natCard_inf_zpowers_lt hbd₁ using 1; aesop
  obtain ⟨d₀, hd₀_dvd, hd₀_not, hd₀_cases⟩ :
      ∃ d₀ : ℕ, d₀ ∣ orderOf b ∧ ¬(d₀ ∣ Nat.card H) ∧
        (¬(orderOf a ∣ d₀) ∨ ¬(orderOf c ∣ d₀)) := by
    exact exists_dvd_not_dvd_incompatible (orderOf_pos b) Nat.card_pos hH_dvd hH_lt
      hα_dvd hγ_dvd (not_dvd_orderOf_of_not_mem_zpowers ha_b hc_b hac₁)
        (not_dvd_orderOf_of_not_mem_zpowers hc_b ha_b hac₂)
  have hd₀_pos : 0 < d₀ := Nat.pos_of_dvd_of_pos hd₀_dvd (pos_of_gt hH_lt)
  obtain ⟨b', hb'_mem, hb'_ord⟩ := exists_mem_zpowers_orderOf_eq hd₀_dvd hd₀_pos
  have hb'_not_d : b' ∉ zpowers d := fun h ↦ hd₀_not (hb'_ord ▸ orderOf_dvd_natCard H ⟨hb'_mem, h⟩)
  have hb'_not_x (x : G) (hx_d : x ∈ zpowers d) : b' ∉ zpowers x :=
    fun h ↦ hb'_not_d <| zpowers_le_of_mem hx_d h
  have hd_not_b' : d ∉ zpowers b' := fun h ↦ hbd₂ <| zpowers_le_of_mem hb'_mem h
  rcases hd₀_cases with hα_not | hγ_not
  · have ha_not_b' : a ∉ zpowers b' := fun h ↦ hα_not <| hb'_ord ▸ orderOf_dvd_of_mem_zpowers h |>
      fun x ↦ dvd_trans x (by simp)
    have hb'_not_a : b' ∉ zpowers a := hb'_not_x a ha_d |> fun h ↦ by simpa using h
    have hb'_ne_b : b' ≠ b := by grind +ring
    have hb'_ne_d : b' ≠ d := fun h ↦ hb'_not_d <| h.symm ▸ mem_zpowers _
    have hb_ne_d : b ≠ d := fun h ↦ hbd₁ <| h.symm ▸ mem_zpowers _
    exact P4_from_witness_left hb'_mem ha_b ha_d hb'_not_d hbd₂ hbd₁ ha_not_b' hb'_not_a hab had
      hb'_ne_b hb'_ne_d hb_ne_d
  · have hc_not_b' : c ∉ zpowers b' := fun h ↦
      hγ_not <| hb'_ord ▸ orderOf_dvd_of_mem_zpowers h |> dvd_trans <| by aesop
    have hb'_not_c : b' ∉ zpowers c := hb'_not_x c hc_d
    exact P4_from_witness_left hb'_mem hc_b hc_d hb'_not_d hbd₂ hbd₁ hc_not_b' hb'_not_c hcb hcd
      (by rintro rfl; simp_all) (fun h ↦ hb'_not_d <| h.symm ▸ mem_zpowers _) (by grind)

/-- An induced `C₄` in the power graph of a finite group implies an induced `P₄`. -/
theorem hasInducedP4_of_hasInducedC4_power {G : Type*} [Group G] [Finite G]
    (hcycle : HasInducedCycle (powerGraph G) 4 (by omega)) :
    HasInducedP4 (powerGraph G) := by
  obtain ⟨f, hf⟩ := hcycle
  simp_all only [Function.Injective, Fin.forall_fin_succ, Fin.reduceSucc, powerGraph, Fin.coe_ofNat_eq_mod]
  have h1 : (f 0 ∈ zpowers (f 1) ∧ f 2 ∈ zpowers (f 1)) ∨ (f 1 ∈ zpowers (f 0) ∧ f 1 ∈ zpowers (f 2)) :=
    powerGraph_path_fork (by aesop) (by aesop) (by aesop)
  have h2 : (f 2 ∈ zpowers (f 3) ∧ f 0 ∈ zpowers (f 3)) ∨ (f 3 ∈ zpowers (f 2) ∧ f 3 ∈ zpowers (f 0)) := by
    grind +suggestions
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
  · apply powerGraph_C4_case_I_witness h1.1 h1.2 h2.1 h2.2 <;> aesop
  · have : f 3 ∈ zpowers (f 1) := zpowers_le.mpr h1.2 h2.1 |> fun h ↦ by simpa using h
    grind
  · have : f 1 ∈ zpowers (f 3) := zpowers_le.mpr h2.2 h1.1 |> fun h ↦ by simpa using h
    grind
  · apply powerGraph_C4_case_I_witness h1.2 <;> tauto

/-! ### Main Theorem -/

/-- For any finite group `G`, if the power graph `P(G)` is a cograph then `P(G)` is chordal. -/
theorem cograph_imp_chordal_powerGraph {G : Type*} [Group G] [Finite G] {hco : IsCograph (powerGraph G)} :
    IsChordal (powerGraph G) := by
  intro n hn
  by_cases h5 : 5 ≤ n
  · exact isCograph_imp_no_cycle_ge5 _ hco n h5
  · have h4 : n = 4 := by omega
    subst h4
    exact fun hcycle ↦ hco <| hasInducedP4_of_hasInducedC4_power hcycle

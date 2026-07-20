/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone
-/
import Kourovka.Mathlib.InducedGraph
import Kourovka.Mathlib.PowerGraph
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.BourbakiWitt
import Mathlib.Tactic.Bound
import Mathlib.Order.Comparable

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

open Subgroup SimpleGraph

/-! ### Number Theory Helpers -/

variable {α γ n k : ℕ}

/-- If `α` and `γ` are incomparable under divisibility, there exist distinct primes `p ∣ α`
and `q ∣ γ`. -/
lemma exists_distinct_prime_dvd_of_incompRel_dvd (hαγ : IncompRel (· ∣ ·) α γ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ α ∧ q ∣ γ := by
  obtain ⟨p, k, hp, hpα, hpγ⟩ : ∃ p k : ℕ, p.Prime ∧ p ^ k ∣ α ∧ ¬ p ^ k ∣ γ := by
    by_contra! h
    exact hαγ.1 <| (γ.dvd_iff_prime_pow_dvd_dvd α).2 h
  obtain ⟨q, e, hq, hqγ, hqα⟩ : ∃ q e : ℕ, q.Prime ∧ q ^ e ∣ γ ∧ ¬ q ^ e ∣ α := by
    by_contra! h
    exact hαγ.2 <| (α.dvd_iff_prime_pow_dvd_dvd γ).2 h
  refine ⟨p, q, hp, hq, ?_, ?_, ?_⟩
  · rintro rfl
    have hek : e ≤ k := le_of_not_gt fun h ↦ hpγ <| (pow_dvd_pow p h.le).trans hqγ
    exact hqα <| (pow_dvd_pow p hek).trans hpα
  · exact (dvd_pow_self p <| by rintro rfl; simp_all).trans hpα
  · exact (dvd_pow_self q <| by rintro rfl; simp_all).trans hqγ

/-- If `α` and `γ` are incomparable under divisibility and `0 < k < n`, there exists `d ∣ n`
with `d ∤ k` and `α ∤ d` or `γ ∤ d`. -/
lemma exists_dvd_not_dvd_incompRel_dvd (hk : 0 < k) (hk_lt : k < n)
    (hαγ : IncompRel (· ∣ ·) α γ) :
    ∃ d : ℕ, d ∣ n ∧ ¬(d ∣ k) ∧ (¬(α ∣ d) ∨ ¬(γ ∣ d)) := by
  obtain ⟨p, q, hp, hq, hpq, hpα, hqγ⟩ := exists_distinct_prime_dvd_of_incompRel_dvd hαγ
  obtain ⟨r, hrkn⟩ := Nat.exists_factorization_lt_of_lt hk.ne' hk_lt
  have hr : r.Prime := by
    by_contra h
    simp [Nat.factorization_eq_zero_of_not_prime k h,
      Nat.factorization_eq_zero_of_not_prime n h] at hrkn
  refine ⟨r ^ n.factorization r, Nat.ordProj_dvd n r, ?_, ?_⟩
  · exact fun h ↦ not_le_of_gt hrkn <| (hr.pow_dvd_iff_le_factorization hk.ne').1 h
  · by_contra! h
    exact hpq <| (Nat.prime_eq_prime_of_dvd_pow hp hr (hpα.trans h.1)).trans
      (Nat.prime_eq_prime_of_dvd_pow hq hr (hqγ.trans h.2)).symm

/-! ### Group Theory Helpers -/

variable {G : Type*} [Group G] [Finite G]

/-- In a finite cyclic group, for any `d ∣ Nat.card G` with `0 < d`, there exists an element of
order `d`. -/
lemma exists_orderOf_eq_of_dvd_of_isCyclic [IsCyclic G] {d : ℕ}
    (hd : d ∣ Nat.card G) (hd_pos : 0 < d) : ∃ g : G, orderOf g = d := by
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
lemma exists_mem_zpowers_orderOf_eq {b : G} {d : ℕ}
    (hd : d ∣ orderOf b) (hd_pos : 0 < d) : ∃ g : G, g ∈ zpowers b ∧ orderOf g = d := by
  obtain ⟨g, hg⟩ : ∃ g : zpowers b, orderOf g = d :=
    exists_orderOf_eq_of_dvd_of_isCyclic (by rw [Nat.card_zpowers]; exact hd) hd_pos
  use g
  aesop

/-! ### Power Graph: C₄ implies P₄ -/

/-- In a cyclic group `⟨b⟩`, if `a, c ∈ ⟨b⟩` and `a ∉ ⟨c⟩`, then `orderOf a ∤ orderOf c`. -/
lemma not_dvd_orderOf_of_not_mem_zpowers {a c b : G}
    (ha : a ∈ zpowers b) (hc : c ∈ zpowers b) (h : a ∉ zpowers c) : ¬(orderOf a ∣ orderOf c) := by
  obtain ⟨i, hi⟩ : ∃ i : ℤ, a = b ^ i := mem_zpowers_iff.mp ha |>.imp fun _ ↦ Eq.symm
  obtain ⟨j, hj⟩ : ∃ j : ℤ, c = b ^ j := mem_zpowers_iff.mp hc |>.imp fun j hj ↦ hj.symm
  contrapose! h
  simp_all only [zpow_mem_zpowers, orderOf_dvd_iff_pow_eq_one]
  have h_cong : i * orderOf (b ^ j) ≡ 0 [ZMOD orderOf b] := by
    rw [← zpow_natCast, ← zpow_mul] at h
    exact zpow_eq_one_iff_modEq.mp h
  have h_cong' : i * (orderOf b / (orderOf b).gcd (j.natAbs)) ≡ 0 [ZMOD orderOf b] := by
    have h_order_gj : ∀ m : ℕ, orderOf (b ^ m) = orderOf b / (orderOf b).gcd m := fun m ↦
      orderOf_pow b
    cases j <;> simp_all
  have h_div : i ≡ 0 [ZMOD (orderOf b).gcd (j.natAbs)] := by
    rw [Int.modEq_zero_iff_dvd] at *
    refine Int.dvd_of_mul_dvd_mul_right
        (show ((orderOf b) : ℤ) / ((orderOf b).gcd (j.natAbs)) ≠ 0 from ?_) ?_
    · have := Nat.le_of_dvd (orderOf_pos _) ((orderOf b).gcd_dvd_left (j.natAbs))
      refine ne_of_gt
          (Int.le_ediv_of_mul_le (Nat.cast_pos.mpr (Nat.gcd_pos_of_pos_left _ (orderOf_pos _))) ?_)
      nlinarith
    · rw [Int.mul_ediv_cancel' (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))]
      aesop
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h_div
  have h_exp : b ^ i = (b ^ ((orderOf b).gcd (j.natAbs))) ^ k := by
    rw [hk, zpow_mul]
    norm_cast
  have h_pow : ∃ m : ℤ, b ^ ((orderOf b).gcd (j.natAbs)) = (b ^ j) ^ m := by
    have := (orderOf b).gcd_eq_gcd_ab (j.natAbs)
    use (orderOf b).gcdB (j.natAbs) * (if j < 0 then -1 else 1)
    split_ifs <;> simp_all [← zpow_mul, ← zpow_natCast]
    · simp [zpow_add, zpow_mul, abs_of_neg ‹_›]
    · simp [abs_of_nonneg ‹_›, zpow_add, zpow_mul]
  aesop

/-- If `b ∉ zpowers d`, then `Nat.card (zpowers b ⊓ zpowers d) < Nat.card (zpowers b)`. -/
lemma natCard_inf_zpowers_lt {b d : G} (hbd : b ∉ zpowers d) :
    Nat.card ↑(zpowers b ⊓ zpowers d) < Nat.card ↑(zpowers b) := by
  convert Set.ncard_lt_ncard
      (show (zpowers b ⊓ zpowers d : Set G) < zpowers b from
        Set.ssubset_iff_subset_ne.2 ⟨by aesop, by aesop⟩)

omit [Finite G] in
/-- A witness element `b'` gives a `P₄` `b'-b-x-d`. -/
lemma P4_from_witness_left {x b d b' : G}
    (hb'_mem : b' ∈ zpowers b) (hx_b : x ∈ zpowers b) (hx_d : x ∈ zpowers d)
    (hb'_not_d : b' ∉ zpowers d) (hd_not_b : d ∉ zpowers b) (hb_not_d : b ∉ zpowers d)
    (hx_not_b' : x ∉ zpowers b') (hb'_not_x : b' ∉ zpowers x) (hxb : x ≠ b) (hxd : x ≠ d)
    (hb'b : b' ≠ b) (hb'd : b' ≠ d) (hbd : b ≠ d) :
    (PowerGraph G).HasIndPath 4 := by
  have hd_not_b' : d ∉ zpowers b' := fun h ↦ hd_not_b (zpowers_le_of_mem hb'_mem h)
  have hb'x : b' ≠ x := fun h ↦ hb'_not_x (h ▸ mem_zpowers _)
  refine isIndContained_iff_exists_comap_eq.mpr ⟨⟨![b', b, x, d], ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  · ext i j
    simp only [comap_adj, pathGraph_adj, PowerGraph]
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm, mem_zpowers] <;>
      tauto

/-- Given the "Case I" configuration of a `C₄` (both `a, c ∈ ⟨b⟩` and `a, c ∈ ⟨d⟩`),
construct an element `b'` yielding an induced `P₄`. -/
lemma powerGraph_C4_case_I_witness {a b c d : G}
    (ha_b : a ∈ zpowers b) (hc_b : c ∈ zpowers b) (hc_d : c ∈ zpowers d) (ha_d : a ∈ zpowers d)
    (hac₁ : a ∉ zpowers c) (hac₂ : c ∉ zpowers a) (hbd₁ : b ∉ zpowers d) (hbd₂ : d ∉ zpowers b)
    (hab : a ≠ b) (hcd : c ≠ d) (hcb : c ≠ b) (had : a ≠ d) :
    (PowerGraph G).HasIndPath 4 := by
  set H := zpowers b ⊓ zpowers d
  have hH_lt : Nat.card H < orderOf b := by
    convert natCard_inf_zpowers_lt hbd₁ using 1
    aesop
  obtain ⟨d₀, hd₀_dvd, hd₀_not, hd₀_cases⟩ :
    ∃ d₀ : ℕ, d₀ ∣ orderOf b ∧ ¬(d₀ ∣ Nat.card H) ∧ (¬(orderOf a ∣ d₀) ∨ ¬(orderOf c ∣ d₀)) :=
    exists_dvd_not_dvd_incompRel_dvd Nat.card_pos hH_lt
      ⟨not_dvd_orderOf_of_not_mem_zpowers ha_b hc_b hac₁,
        not_dvd_orderOf_of_not_mem_zpowers hc_b ha_b hac₂⟩
  have hd₀_pos : 0 < d₀ := Nat.pos_of_dvd_of_pos hd₀_dvd (pos_of_gt hH_lt)
  obtain ⟨b', hb'_mem, hb'_ord⟩ := exists_mem_zpowers_orderOf_eq hd₀_dvd hd₀_pos
  have hb'_not_d : b' ∉ zpowers d := fun h ↦ hd₀_not (hb'_ord ▸ H.orderOf_dvd_natCard ⟨hb'_mem, h⟩)
  have hb'_not_x (x : G) (hx_d : x ∈ zpowers d) : b' ∉ zpowers x := fun h ↦
    hb'_not_d <| zpowers_le_of_mem hx_d h
  have hd_not_b' : d ∉ zpowers b' := fun h ↦ hbd₂ <| zpowers_le_of_mem hb'_mem h
  rcases hd₀_cases with hα_not | hγ_not
  · have ha_not_b' : a ∉ zpowers b' := fun h ↦ hα_not (hb'_ord ▸ orderOf_dvd_of_mem_zpowers h)
    have hb'_not_a : b' ∉ zpowers a := hb'_not_x a ha_d
    have hb'_ne_b : b' ≠ b := by grind
    have hb'_ne_d : b' ≠ d := fun h ↦ hb'_not_d <| h.symm ▸ mem_zpowers _
    have hb_ne_d : b ≠ d := fun h ↦ hbd₁ <| h.symm ▸ mem_zpowers _
    exact P4_from_witness_left hb'_mem ha_b ha_d hb'_not_d hbd₂ hbd₁ ha_not_b' hb'_not_a hab had
        hb'_ne_b hb'_ne_d hb_ne_d
  · have hc_not_b' : c ∉ zpowers b' := fun h ↦ hγ_not (hb'_ord ▸ orderOf_dvd_of_mem_zpowers h)
    have hb'_not_c : b' ∉ zpowers c := hb'_not_x c hc_d
    refine P4_from_witness_left hb'_mem hc_b hc_d hb'_not_d hbd₂ hbd₁ hc_not_b' hb'_not_c hcb hcd ?_
        (fun h ↦ hb'_not_d <| h.symm ▸ mem_zpowers _) ?_
    · rintro rfl
      simp_all
    · grind

/-- An induced `C₄` in the power graph of a finite group implies an induced `P₄`. -/
theorem PowerGraph.hasIndPath_of_hasIndCycle_four (hG : (PowerGraph G).HasIndCycle 4) :
    (PowerGraph G).HasIndPath 4 := by
  rcases hG with ⟨f⟩
  have hf : Function.Injective f := f.injective
  have hadj {i j : Fin 4} :
      (PowerGraph G).Adj (f i) (f j) ↔ (cycleGraph 4).Adj i j := f.map_adj_iff
  have adj01 : f 0 ∈ zpowers (f 1) ∨ f 1 ∈ zpowers (f 0) := (hadj.mpr (by decide)).2
  have adj12 : f 1 ∈ zpowers (f 2) ∨ f 2 ∈ zpowers (f 1) := (hadj.mpr (by decide)).2
  have adj23 : f 2 ∈ zpowers (f 3) ∨ f 3 ∈ zpowers (f 2) := (hadj.mpr (by decide)).2
  have adj30 : f 3 ∈ zpowers (f 0) ∨ f 0 ∈ zpowers (f 3) := (hadj.mpr (by decide)).2
  have n02 : ¬(f 0 ∈ zpowers (f 2) ∨ f 2 ∈ zpowers (f 0)) :=
    fun h ↦ absurd (hadj.mp ⟨hf.ne (by decide), h⟩) (by decide)
  have n13 : ¬(f 1 ∈ zpowers (f 3) ∨ f 3 ∈ zpowers (f 1)) :=
    fun h ↦ absurd (hadj.mp ⟨hf.ne (by decide), h⟩) (by decide)
  have h1 := PowerGraph.path_fork adj01 adj12 n02
  have h₂ := PowerGraph.path_fork adj23 adj30 (fun h ↦ n02 h.symm)
  rcases h1 with h1 | h1 <;> rcases h₂ with h2 | h2
  · exact powerGraph_C4_case_I_witness h1.1 h1.2 h2.1 h2.2
      (fun h ↦ n02 (.inl h)) (fun h ↦ n02 (.inr h))
      (fun h ↦ n13 (.inl h)) (fun h ↦ n13 (.inr h))
      (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide))
  · exact absurd (.inr (zpowers_le.mpr h1.2 h2.1)) n13
  · exact absurd (.inl (zpowers_le.mpr h2.2 h1.1)) n13
  · exact powerGraph_C4_case_I_witness h1.2 h2.1 h2.2 h1.1
      (fun h ↦ n13 (.inl h)) (fun h ↦ n13 (.inr h))
      (fun h ↦ n02 (.inr h)) (fun h ↦ n02 (.inl h))
      (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide))

/-- **Kourovka Notebook, Problem 21.24.** For any finite group `G`, if the power graph `P(G)`
is a cograph then `P(G)` is chordal. -/
theorem kourovka_21_24 (hG : (PowerGraph G).IsCograph) : (PowerGraph G).IsChordal := by
  intro n hn
  by_cases h : 5 ≤ n
  · exact fun hC ↦ hG <| hC.hasIndPath_of_lt h
  · obtain rfl : n = 4 := by omega
    exact fun hC ↦ hG <| PowerGraph.hasIndPath_of_hasIndCycle_four hC

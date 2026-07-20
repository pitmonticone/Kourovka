/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith

/-!
# The running least common multiple `Nat.lcmSeq`

`Nat.lcmSeq k` is the least common multiple of `1, 2, …, k`. This file develops its basic
arithmetic: positivity, monotonicity, the divisibility recurrence `lcmSeq_succ`, and the fact
that `lcmSeq` strictly increases at `k + 1` exactly when `k + 1` is a prime power.
-/

namespace Nat

/-- The lcm of the numbers `1, 2, 3, …, k`. -/
def lcmSeq (k : ℕ) : ℕ :=
  (Finset.Ioc 0 k).lcm id

/-- The empty running lcm is `1`: `lcmSeq 0 = 1`. -/
lemma lcmSeq_zero : lcmSeq 0 = 1 :=
  rfl

/-- The running lcm up to `1` is `1`: `lcmSeq 1 = 1`. -/
lemma lcmSeq_one : lcmSeq 1 = 1 :=
  rfl

/-- The running lcm `k.lcmSeq` is never zero. -/
lemma lcmSeq_ne_zero (k : ℕ) : k.lcmSeq ≠ 0 := by
  simp [lcmSeq, Finset.lcm_eq_zero_iff]

/-- `k.lcmSeq` is a nonzero natural number. -/
instance {k : ℕ} : NeZero (k.lcmSeq) :=
  NeZero.mk <| lcmSeq_ne_zero _

/-- The running lcm `k.lcmSeq` is positive. -/
lemma lcmSeq_pos (k : ℕ) : 0 < k.lcmSeq :=
  k.lcmSeq.pos_of_neZero

/-- Recurrence for the running lcm: `(k + 1).lcmSeq = (k + 1).lcm k.lcmSeq`. -/
lemma lcmSeq_succ (k : ℕ) : (k + 1).lcmSeq = (k + 1).lcm (k.lcmSeq) := by
  unfold lcmSeq
  have : Finset.Ioc 0 (k + 1) = insert (k + 1) (Finset.Ioc 0 k) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [this, Finset.lcm_insert, id_eq, lcm_eq_nat_lcm]

/-- The running lcm `lcmSeq` is monotone in `k`. -/
lemma lcmSeq_mono : Monotone lcmSeq :=
  monotone_nat_of_le_succ fun n ↦ le_of_dvd (n + 1).lcmSeq_pos (lcmSeq_succ n ▸ dvd_lcm_right _ _)

/-- Each term of the running lcm divides the next: `k.lcmSeq ∣ (k + 1).lcmSeq`. -/
lemma lcmSeq_dvd_lcmSeq_succ (k : ℕ) : k.lcmSeq ∣ (k + 1).lcmSeq :=
  k.lcmSeq_succ ▸ dvd_lcm_right _ _

/-- Every `d` with `d ∈ Finset.Ioc 0 k` divides the running lcm `k.lcmSeq`. -/
lemma dvd_lcmSeq_of_mem {d k : ℕ} (h : d ∈ Finset.Ioc 0 k) : d ∣ k.lcmSeq :=
  Finset.dvd_lcm h

/-- A nonzero `k` divides its own running lcm: `k ∣ k.lcmSeq`. -/
lemma dvd_lcmseq_self (k : ℕ) [NeZero k] : k ∣ k.lcmSeq :=
  dvd_lcmSeq_of_mem (Finset.right_mem_Ioc.mpr (Nat.pos_of_ne_zero (NeZero.ne k)))

/-- The running lcm stays the same at `k + 1` exactly when `k + 1 ∣ k.lcmSeq`. -/
lemma lcmSeq_succ_eq_iff_dvd {k : ℕ} : (k + 1).lcmSeq = k.lcmSeq ↔ k + 1 ∣ k.lcmSeq := by
  constructor <;> intro h
  · rw [← h]
    exact dvd_lcmSeq_of_mem (Finset.right_mem_Ioc.mpr k.zero_lt_succ)
  · apply dvd_antisymm _ (k.lcmSeq_dvd_lcmSeq_succ)
    rw [lcmSeq_succ]
    exact lcm_dvd h (Nat.dvd_refl _)

/-- If `k + 1` is not a prime power, then for each of its prime factors `p` the full prime power
`p ^ (k + 1).factorization p` already divides `k.lcmSeq`. -/
lemma factor_pow_dvd_lcmSeq_of_not_prime_pow {k : ℕ} {p : ℕ} (hp : p ∈ (k + 1).primeFactors)
    (hk : ¬IsPrimePow (k + 1)) : p ^ (factorization (k + 1) p) ∣ k.lcmSeq := by
  rw [isPrimePow_nat_iff] at hk
  push_neg at hk
  apply dvd_lcmSeq_of_mem
  rw [Finset.mem_Ioc]
  refine ⟨(k + 1).ordProj_pos p, ?_⟩
  apply le_of_lt_add_one
  apply lt_of_le_of_ne (ordProj_le _ (k.zero_ne_add_one).symm)
  apply hk _ _ (prime_of_mem_primeFactors hp)
  apply (prime_of_mem_primeFactors hp).factorization_pos_of_dvd (k.zero_ne_add_one).symm
  exact dvd_of_mem_primeFactors hp

/-- The `p`-adic valuation of a `Finset.lcm` of nonzero naturals is the supremum of the
valuations of the individual terms. -/
theorem _root_.Finset.factorization_lcm {ι : Type*} {f : ι → ℕ} {s : Finset ι}
    (hf : ∀ k ∈ s, f k ≠ 0) (p : ℕ) :
    (s.lcm f).factorization p = s.sup fun a ↦ (f a).factorization p := by
  classical
    induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ _ => simp_all [lcm_eq_nat_lcm, Nat.factorization_lcm]

/-- The running lcm strictly increases at `k + 1` exactly when `k + 1` is a prime power. -/
lemma lcmSeq_succ_ne_iff_prime_pow {k : ℕ} : (k + 1).lcmSeq ≠ k.lcmSeq ↔ IsPrimePow (k + 1) := by
  constructor
  · contrapose
    intro h
    rw [lcmSeq_succ_eq_iff_dvd, ←
      factorization_prime_le_iff_dvd ((k.zero_ne_add_one).symm) (k.lcmSeq_ne_zero)]
    intro p p_prime
    by_cases hp : p ∈ (k + 1).primeFactors
    · have := factor_pow_dvd_lcmSeq_of_not_prime_pow hp h
      rw [← factorization_le_iff_dvd (pow_ne_zero _ p_prime.ne_zero) (lcmSeq_ne_zero _)] at this
      simp_all
    · rw [factorization_eq_zero_of_not_dvd]
      · exact (k.lcmSeq.factorization p).zero_le
      · contrapose! hp
        exact p_prime.mem_primeFactors' hp
  · intro h_ppow h_lcm
    obtain ⟨p, e, p_prime, e_pos, hpe⟩ := (isPrimePow_nat_iff _).mp h_ppow
    rw [lcmSeq_succ_eq_iff_dvd, lcmSeq, ← factorization_prime_le_iff_dvd] at h_lcm
    · specialize h_lcm p p_prime
      rw [← hpe, factorization_pow_self p_prime, Finset.factorization_lcm] at h_lcm
      · rw [Finset.le_sup_iff] at h_lcm
        · obtain ⟨b, b_mem, hb⟩ := h_lcm
          rw [← Prime.pow_dvd_iff_le_factorization p_prime (by aesop), id_eq, hpe] at hb
          rw [Finset.mem_Ioc] at b_mem
          have := le_of_dvd b_mem.1 hb
          linarith
        · simp_all
      · aesop
    · exact (k.zero_ne_add_one).symm
    · by_contra! h
      rw [Finset.lcm_eq_zero_iff] at h
      aesop

/-- When the running lcm increases at `k + 1`, there is a prime `p` with `k + 1 = p ^ (m + 1)` and
`(k + 1).lcmSeq = p * k.lcmSeq`. -/
lemma exist_prime_of_lcmSeq_ne_succ {k : ℕ} (h : (k + 1).lcmSeq ≠ k.lcmSeq) :
    ∃ p m, p.Prime ∧ (k + 1) = p ^ (m + 1) ∧ (k + 1).lcmSeq = p * k.lcmSeq := by
  obtain ⟨p, m, p_prime, m_pos, k_succ_eq⟩ := lcmSeq_succ_ne_iff_prime_pow.mp h
  rw [← prime_iff] at p_prime
  use p
  use m - 1
  refine ⟨p_prime, (sub_one_add_one_eq_of_pos m_pos) ▸ k_succ_eq.symm, ?_⟩
  apply dvd_antisymm
  · have h_lcmSeq_dvd : (k + 1).lcmSeq = (p ^ m).lcm (k.lcmSeq) := by rw [k_succ_eq, lcmSeq_succ]
    rcases m with (_ | _ | m)
    · rw [h_lcmSeq_dvd]
      simp
    · rw [h_lcmSeq_dvd]
      simp
    · simp_all only [ne_eq, lt_add_iff_pos_left, add_pos_iff, ofNat_pos, or_true, pow_succ',
        lcm_dvd_iff, dvd_mul_left, and_true]
      rw [← k_succ_eq]
      apply Nat.mul_dvd_mul_left p
      apply dvd_lcmSeq_of_mem
      refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
      · exact (Nat.mul_pos p_prime.pos (pow_pos p_prime.pos _))
      · nlinarith [p_prime.two_le]
  · apply mul_dvd_of_dvd_div
    · trans p ^ m
      · exact p.div_pow_of_pos m m_pos
      · apply dvd_lcmSeq_of_mem
        rw [k_succ_eq, Finset.right_mem_Ioc]
        exact k.zero_lt_succ
    · rw [lcmSeq_succ, ← factorization_prime_le_iff_dvd (k.lcmSeq_ne_zero)]
      · intro q q_prime
        rw [factorization_div (dvd_lcm_of_dvd_left (k_succ_eq ▸ p.div_pow_of_pos m m_pos) _),
          Finsupp.coe_tsub, Pi.sub_apply, ← k_succ_eq,
          factorization_lcm (k_succ_eq ▸ (k.zero_ne_add_one).symm) (k.lcmSeq_ne_zero),
          Finsupp.sup_apply]
        by_cases hpq : p = q
        · subst hpq
          suffices k.lcmSeq.factorization p ≤ m - 1 by
            rw [factorization_pow, max_eq_left]
            all_goals simp_all
            apply le_trans this
            omega
          apply le_sub_one_of_lt
          apply Nat.lt_of_not_ge
          contrapose h
          rw [lcmSeq_succ_eq_iff_dvd, ← k_succ_eq]
          apply dvd_trans _ (ordProj_dvd _ p)
          exact Nat.pow_dvd_pow p h
        · simp_all
      · apply ne_of_gt
        apply div_pos _ p_prime.pos
        apply le_of_dvd (lcm_pos (k.zero_lt_succ) k.lcmSeq_pos)
        apply dvd_trans (dvd_pow_self p (Nat.ne_zero_of_lt m_pos))
        apply dvd_lcm_of_dvd_left
        rw [k_succ_eq]

end Nat

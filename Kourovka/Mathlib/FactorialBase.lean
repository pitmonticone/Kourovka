/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Cases

open Finset BigOperators Equiv

/-! ## Factorial Base Properties -/

/-- The telescoping identity `∑_{j=0}^{n-1} j · j! = n! − 1`, proved by induction on `n`. -/
lemma sum_id_mul_factorial : ∀ n : ℕ, ∑ j : Fin n, j.val * j.val.factorial = n.factorial - 1 := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, Nat.factorial_succ,
      Nat.succ_mul, ih]
    grind

/-- Bound on a factorial-base sum: if `0 ≤ aⱼ ≤ j` for all `j`, then
`∑ aⱼ · j! ≤ n! − 1`. -/
lemma sum_bounded_factorial_le (n : ℕ) (a : Fin n → ℕ) (ha : ∀ j, a j ≤ j.val) :
    ∑ j : Fin n, a j * j.val.factorial ≤ n.factorial - 1 :=
  (sum_le_sum fun j _ ↦ Nat.mul_le_mul_right _ (ha j)).trans (sum_id_mul_factorial n).le

/-- Strict bound on a factorial-base sum: if `0 ≤ aⱼ ≤ j` for all `j`, then
`∑ aⱼ · j! < n!`. -/
lemma sum_bounded_factorial_lt (n : ℕ) (a : Fin n → ℕ) (ha : ∀ j, a j ≤ j.val) :
    ∑ j : Fin n, a j * j.val.factorial < n.factorial :=
  lt_of_le_of_lt (sum_bounded_factorial_le n a ha) (Nat.sub_lt (Nat.factorial_pos _) zero_lt_one)

/-- Splitting a `Fin (n + 1)` sum into the last term plus a `Fin n` sum. -/
lemma fin_sum_snoc {n : ℕ} (f : Fin (n + 1) → ℕ) :
    ∑ j : Fin (n + 1), f j = f ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ + ∑ j : Fin n, f (j.castSucc) := by
  rw [Fin.sum_univ_castSucc, add_comm]
  rfl

/-- The highest factorial-base digit is recovered by division: if `aⱼ ≤ j` and
`S = ∑ aⱼ · j!`, then `S / n! = aₙ`. -/
lemma factorial_base_top_digit {n : ℕ} (a : Fin (n + 1) → ℕ) (ha : ∀ j, a j ≤ j.val) :
    (∑ j : Fin (n + 1), a j * j.val.factorial) / n.factorial = a ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
  have h_split :
      ∑ j : Fin (n + 1), a j * j.val.factorial =
        a ⟨n, n.lt_succ_self⟩ * n.factorial +
          ∑ j : Fin n, a (Fin.castSucc j) * j.val.factorial := by
    convert fin_sum_snoc _ using 2
  rw [h_split, add_comm, Nat.add_mul_div_right _ _ (Nat.factorial_pos n),
    Nat.div_eq_of_lt (sum_bounded_factorial_lt n _ fun j ↦ ha j.castSucc), zero_add]

/-- **Uniqueness of factorial base representation.** If two sequences of digits (each bounded
by their index) give the same weighted sum, they are equal. The proof is by induction on `n`,
extracting the top digit via division. -/
lemma factorial_base_unique :
    ∀ (n : ℕ) (a b : Fin n → ℕ), (∀ j, a j ≤ j.val) → (∀ j, b j ≤ j.val) →
      (∑ j : Fin n, a j * j.val.factorial = ∑ j : Fin n, b j * j.val.factorial) → a = b := by
  intro n b ha hb h
  induction' n with n ih
  · grind
  · intro h_eq
    have h_top : b ⟨n, n.lt_succ_self⟩ = ha ⟨n, n.lt_succ_self⟩ := by
      grind [factorial_base_top_digit ha h, factorial_base_top_digit b hb]
    have h_remainder :
      ∑ j : Fin n, b (Fin.castSucc j) * (j.val).factorial =
        ∑ j : Fin n, ha (Fin.castSucc j) * (j.val).factorial := by
      simp_all [Fin.sum_univ_castSucc, Fin.last]
    have h_eq' : b ∘ Fin.castSucc = ha ∘ Fin.castSucc :=
      ih _ _ (fun j ↦ hb _) (fun j ↦ h _) h_remainder
    refine funext fun x ↦ if hx : x.val < n then congr_fun h_eq' ⟨x.val, hx⟩ else ?_
    rw [show x = ⟨n, n.lt_succ_self⟩ from le_antisymm (Fin.le_last _) (not_lt.mp hx)]
    grind

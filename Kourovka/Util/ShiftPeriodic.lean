/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Kourovka.Util.ClassTransposition
import Kourovka.Util.LCMSeq
import Mathlib.Data.ZMod.Defs

/-! ## Shift Periodicity Framework

A permutation `σ` of `ℤ` is *N-shift-periodic* if `σ(n + N) = σ(n) + N` for all `n`.
-/

namespace Equiv

/-- A permutation `σ` of `ℤ` is `N`-shift-periodic if `σ(n + N) = σ(n) + N` for all `n`. -/
def IsShiftPeriodic (σ : Perm ℤ) (N : ℤ) : Prop :=
  ∀ n : ℤ, σ (n + N) = σ n + N

namespace IsShiftPeriodic

/-- The identity element of `Perm ℤ` is `N`-shift-periodic for every `N`. -/
lemma refl (N : ℤ) : (Equiv.refl ℤ).IsShiftPeriodic N := by
  intro
  simp

/-- The inverse of an `N`-shift-periodic permutation is `N`-shift-periodic. -/
lemma symm {σ : Perm ℤ} {N : ℤ} (h : IsShiftPeriodic σ N) : σ.symm.IsShiftPeriodic N := by
  intro n
  apply σ.injective
  simp only [apply_symm_apply, h (σ.symm n)]

/-- The composition of two `N`-shift-periodic permutations is `N`-shift-periodic. -/
lemma trans {σ₁ σ₂ : Perm ℤ} {N : ℤ} (h₁ : IsShiftPeriodic σ₁ N) (h₂ : IsShiftPeriodic σ₂ N) :
    (σ₁.trans σ₂).IsShiftPeriodic N := by
  intro n
  simp only [trans_apply, h₁ n, h₂ (σ₁ n)]

/-- If `σ` is `M`-shift-periodic and `M ∣ N`, then `σ` is `N`-shift-periodic. -/
lemma of_dvd {σ : Perm ℤ} {M N : ℤ} (h : IsShiftPeriodic σ M) (hdvd : M ∣ N) :
    IsShiftPeriodic σ N := by
  intro n
  obtain ⟨k, rfl⟩ := hdvd
  induction k using Int.induction_on with
  | zero => simp only [mul_zero, add_zero]
  | succ k ih => rw [mul_add, mul_one, ← add_assoc, h, ih, add_assoc]
  | pred k ih =>
    specialize h (n + M * (-k - 1))
    ring_nf at *
    linarith

/-- An `N`-shift-periodic permutation commutes with adding any integer multiple of `N`:
`σ (k + N * n) = σ k + N * n`. -/
lemma add_mul_eq {σ : Perm ℤ} {N : ℤ} (h : IsShiftPeriodic σ N) (k n : ℤ) :
    σ (k + N * n) = σ k + N * n := by
  induction n with
  | zero => rw [mul_zero, add_zero, add_zero]
  | succ n ih => rw [mul_add, mul_one, ← add_assoc, h, ih, add_assoc]
  | pred n ih =>
    nth_rw 1 [← sub_add_cancel (_ * _) N, ← add_assoc, h, ← eq_sub_iff_add_eq] at ih
    rw [mul_sub, mul_one, ih]
    ring

/-- An `N`-shift-periodic permutation is determined by its values on residues:
`σ n = σ (n % N) + N * (n / N)`. -/
lemma eq_apply_mod {σ : Perm ℤ} {N : ℤ} (h : IsShiftPeriodic σ N) (n : ℤ) :
    σ n = σ (n % N) + N * (n / N) := by nth_rw 1 [← n.emod_add_mul_ediv N, h.add_mul_eq]

/-- For a shift-periodic permutation, `σ(n) mod N = σ(n mod N) mod N`. -/
lemma emod_eq {σ : Perm ℤ} {N : ℤ} (h : IsShiftPeriodic σ N) (n : ℤ) : σ n % N = σ (n % N) % N := by
  rw [h.eq_apply_mod]
  simp

/-- Two `N`-shift-periodic permutations (with `0 < N`) are equal iff they agree on the
fundamental block `Finset.Ico 0 N`. -/
lemma ext_iff {σ τ : Perm ℤ} {N : ℤ} (N_pos : 0 < N) (hσ : IsShiftPeriodic σ N)
    (hτ : IsShiftPeriodic τ N) : σ = τ ↔ (∀ n ∈ Finset.Ico 0 N, σ n = τ n) := by
  refine ⟨fun h _ _ ↦ Perm.congr_fun h _, ?_⟩
  intro h
  ext n
  rw [hσ.eq_apply_mod, hτ.eq_apply_mod, h (n % N)]
  exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt N_pos), Int.emod_lt_of_pos _ N_pos⟩

/-- A `k`-shift-periodic permutation that maps `Finset.Ico 0 k` into itself maps every block
`Finset.Ico (j * k) ((j + 1) * k)` into itself. -/
theorem isPeriodic_mapsTo_block {σ : Perm ℤ} {k : ℤ} (hper : σ.IsShiftPeriodic k)
    (hbase : ∀ n : ℤ, n ∈ Finset.Ico 0 k → σ n ∈ Finset.Ico 0 k) (j : ℤ) {n : ℤ}
    (hn : n ∈ Finset.Ico (j * k) ((j + 1) * k)) : σ n ∈ Finset.Ico (j * k) ((j + 1) * k) := by
  obtain ⟨m, hm, m_nonneg, m_lt⟩ : ∃ m : ℤ, n = m + j * k ∧ 0 ≤ m ∧ m < k := by
    use n - j * k
    rw [Finset.mem_Ico] at hn
    refine ⟨?_, ?_, ?_⟩
    · ring
    · linarith
    · linarith
  have h_periodic : σ (m + j * k) = σ m + j * k := hper.of_dvd (dvd_mul_left k j) m
  grind

section reduction

open Fin.IntCast

/-- Restriction of an `N`-shift-periodic permutation of `ℤ` to a permutation of `Fin N`,
obtained by reducing modulo `N`. -/
noncomputable def reduce {N : ℕ} [NeZero N] {σ : Perm ℤ} (hσ : IsShiftPeriodic σ N) : Perm (Fin N) where
  toFun i := σ i
  invFun i := σ.symm i
  left_inv := by
    intro i
    ext
    simp only [Fin.val_intCast]
    rw [Int.toNat_of_nonneg, ← hσ.symm.emod_eq, symm_apply_apply, Int.emod_eq_of_lt,
      Int.toNat_natCast]
    · exact Int.natCast_nonneg ↑i
    · norm_cast
      exact i.isLt
    · apply Int.emod_nonneg
      norm_cast
      exact NeZero.ne N
  right_inv := by
    intro i
    ext
    simp only [Fin.val_intCast]
    rw [Int.toNat_of_nonneg, ← hσ.emod_eq, apply_symm_apply, Int.emod_eq_of_lt, Int.toNat_natCast]
    · exact Int.natCast_nonneg ↑i
    · norm_cast
      exact i.isLt
    · apply Int.emod_nonneg
      norm_cast
      exact NeZero.ne N

/-- Evaluating the reduced permutation at `i : Fin N` gives `σ i`, cast back into `Fin N`. -/
@[simp]
lemma reduce_apply {N : ℕ} [NeZero N] {σ : Perm ℤ} (hσ : IsShiftPeriodic σ N) (i : Fin N) :
    hσ.reduce i = σ i :=
  rfl

/-- On an integer `x`, the reduced permutation satisfies `hσ.reduce x = σ (x % N)`. -/
@[simp]
lemma val_reduce_intCast {N : ℕ} [NeZero N] {σ : Perm ℤ} (hσ : IsShiftPeriodic σ N) (x : ℤ) :
    hσ.reduce x = σ (x % N) := by
  rw [reduce_apply]
  ext
  simp only [Fin.val_intCast]
  rw [Int.toNat_of_nonneg]
  apply Int.emod_nonneg
  norm_cast
  exact NeZero.ne N

/-- Reducing the identity permutation gives the identity on `Fin N`. -/
@[simp]
lemma reduce_refl {N : ℕ} [NeZero N] : (refl N).reduce = Equiv.refl _ := by
  ext i
  zify
  rw [reduce_apply, refl_apply, Fin.val_intCast, Int.toNat_of_nonneg, Int.emod_eq_of_lt]
  · rfl
  · norm_cast
    exact Nat.zero_le _
  · norm_cast
    exact i.isLt
  · exact Int.zero_le_ofNat _

/-- The inverse of the reduced permutation acts by `σ.symm`: `hσ.reduce.symm i = σ.symm i`. -/
@[simp]
lemma reduce_symm_apply {N : ℕ} [NeZero N] {σ : Perm ℤ} (hσ : IsShiftPeriodic σ N) (i : Fin N) :
    hσ.reduce.symm i = σ.symm i :=
  rfl

/-- Reduction commutes with taking inverses: `hσ.reduce.symm = hσ.symm.reduce`. -/
@[simp]
lemma reduce_symm_eq {N : ℕ} [NeZero N] {σ : Perm ℤ} (hσ : IsShiftPeriodic σ N) :
    hσ.reduce.symm = hσ.symm.reduce :=
  rfl

/-- Reduction commutes with composition: `hσ.reduce.trans hτ.reduce = (hσ.trans hτ).reduce`. -/
@[simp]
lemma reduce_trans_eq {N : ℕ} [NeZero N] {σ τ : Perm ℤ} (hσ : IsShiftPeriodic σ N)
    (hτ : IsShiftPeriodic τ N) : hσ.reduce.trans hτ.reduce = (hσ.trans hτ).reduce := by
  ext
  simp only [trans_apply, reduce_apply, Fin.val_intCast]
  congr 1
  rw [Int.toNat_of_nonneg, ← hτ.emod_eq]
  apply Int.emod_nonneg
  norm_cast
  exact NeZero.ne N

/-- If two `N`-shift-periodic permutations have equal reductions, they agree modulo `N`:
`σ n % N = τ n % N`. -/
lemma mod_eq_of_reduce_eq {N : ℕ} [NeZero N] {σ τ : Perm ℤ} (hσ : IsShiftPeriodic σ N)
    (hτ : IsShiftPeriodic τ N) (h_eq : hσ.reduce = hτ.reduce) (n : ℤ) : σ n % N = τ n % N := by
  rw [hσ.eq_apply_mod, hτ.eq_apply_mod, Int.add_mul_emod_self_left, Int.add_mul_emod_self_left]
  apply Perm.congr_fun at h_eq
  specialize h_eq n
  rw [← Fin.val_eq_val, hσ.val_reduce_intCast, hτ.val_reduce_intCast] at h_eq
  zify at h_eq
  simp only [Fin.val_intCast] at h_eq
  rw [Int.toNat_of_nonneg, Int.toNat_of_nonneg] at h_eq
  · exact h_eq
  · apply Int.emod_nonneg
    norm_cast
    exact NeZero.ne N
  · apply Int.emod_nonneg
    norm_cast
    exact NeZero.ne N

end reduction

end IsShiftPeriodic

/-- The class-transposition function with equal moduli is `k`-shift-periodic:
`τFun r₁ k r₂ k (n + k) = τFun r₁ k r₂ k n + k`. -/
lemma τFun_same_isShiftPeriodic {k r₁ r₂ : ℤ} (n : ℤ) :
    τFun r₁ k r₂ k (n + k) = τFun r₁ k r₂ k n + k := by
  unfold τFun
  split_ifs <;>
    simp_all only [add_sub_right_comm, dvd_add_self_right, not_true_eq_false] <;>
    rw [Int.ediv_mul_cancel_of_dvd (dvd_add_self_right.mpr ‹_›),
      Int.ediv_mul_cancel_of_dvd ‹_›] <;>
    ring

/-- The class transposition `τ k r₁ r₂` is `k`-shift-periodic. -/
lemma τ_same_isShiftPeriodic {k r₁ r₂ : ℤ} : IsShiftPeriodic (τ r₁ k r₂ k) k := by
  unfold τ IsShiftPeriodic
  split_ifs <;> simp [Function.Involutive.toPerm, τFun_same_isShiftPeriodic]

/-- Every element of `CT_pair k k` is `k`-shift-periodic. -/
lemma CT_pair_isShiftPeriodic {k : ℤ} {σ : Perm ℤ} (hσ : σ ∈ CT_pair k k) : σ.IsShiftPeriodic k := by
  rw [CT_pair_def] at hσ
  induction hσ using Subgroup.closure_induction with
  | mem _ hσ =>
    obtain ⟨_, _, _, _, rfl⟩ := hσ
    exact τ_same_isShiftPeriodic
  | one => exact IsShiftPeriodic.refl k
  | mul _ _ _ _ h₁ h₂ => exact h₂.trans h₁
  | inv _ _ h => exact h.symm

/-- Every element of `CT_same k` is `k.lcmSeq`-shift-periodic. -/
lemma CT_same_isShiftPeriodic_lcmSeq {k : ℕ} {σ : Perm ℤ} (hσ : σ ∈ CT_same k) :
    σ.IsShiftPeriodic k.lcmSeq := by
  rw [CT_same] at hσ
  induction hσ using Subgroup.iSup_induction' with
  | hp d _ hσ =>
    induction hσ using Subgroup.iSup_induction' with
    | hp hd σ hσ =>
      apply (CT_pair_isShiftPeriodic hσ).of_dvd
      rw [Int.dvd_natCast]
      apply Nat.dvd_lcmSeq_of_mem
      simp_all only [Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rw [Int.natAbs_pos]
        linarith
      · zify
        rw [abs_of_nonneg]
        · exact hd.2
        · linarith
    | h1 => exact IsShiftPeriodic.refl _
    | hmul _ _ _ _ h₁ h₂ => exact h₂.trans h₁
  | h1 => exact IsShiftPeriodic.refl _
  | hmul _ _ _ _ h₁ h₂ => exact h₂.trans h₁

/-- For `0 < k`, the class transposition `τ r₁ k r₂ k` maps the block `Finset.Ico 0 k`
into itself. -/
theorem τ_same_mod_mapsTo_Ico {r₁ r₂ k : ℤ} (hk : 0 < k) (hr₁ : r₁ ∈ Set.Ico 0 k)
    (hr₂ : r₂ ∈ Set.Ico 0 k) {n : ℤ} (hn : n ∈ Finset.Ico 0 k) : τ r₁ k r₂ k n ∈ Finset.Ico 0 k := by
  by_cases h : (k.gcd k : ℤ) ∣ (r₁ - r₂) <;> simp_all [τ]
  split_ifs <;> simp_all [τFun]
  split_ifs <;> simp_all [Int.ediv_mul_cancel]
  · obtain ⟨a, ha⟩ := ‹k ∣ n - r₁›
    constructor <;> nlinarith [show a = 0 by nlinarith]
  · obtain ⟨a, ha⟩ := ‹k ∣ n - r₂›
    constructor <;> nlinarith [show a = 0 by nlinarith]

/-- For `0 < k`, the class transposition `τ r₁ k r₂ k` permutes the block `Finset.Ico 0 k`
setwise. -/
theorem τ_same_mod_setwise_Ico {r₁ r₂ k : ℤ} (hk : 0 < k) (hr₁ : r₁ ∈ Set.Ico 0 k)
    (hr₂ : r₂ ∈ Set.Ico 0 k) : (Finset.Ico 0 k).image (τ r₁ k r₂ k) = Finset.Ico 0 k := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    exact fun n hn ↦ τ_same_mod_mapsTo_Ico hk hr₁ hr₂ hn
  · rw [Finset.card_image_of_injective _ (Equiv.injective _)]

/-- For `0 < k`, the class transposition `τ r₁ k r₂ k` maps each block
`Finset.Ico (j * k) ((j + 1) * k)` into itself. -/
theorem τ_same_mod_mapsTo_block {r₁ r₂ k : ℤ} (hk : 0 < k) (hr₁ : r₁ ∈ Set.Ico 0 k)
    (hr₂ : r₂ ∈ Set.Ico 0 k) (j : ℤ) {n : ℤ} (hn : n ∈ Finset.Ico (j * k) ((j + 1) * k)) :
    τ r₁ k r₂ k n ∈ Finset.Ico (j * k) ((j + 1) * k) := by
  exact τ_same_isShiftPeriodic.isPeriodic_mapsTo_block
    (fun n hn ↦ τ_same_mod_mapsTo_Ico hk hr₁ hr₂ hn) j hn

/-- For `0 < k`, the class transposition `τ r₁ k r₂ k` permutes each block
`Finset.Ico (j * k) ((j + 1) * k)` setwise. -/
theorem τ_same_mod_setwise_block {r₁ r₂ k : ℤ} (hk : 0 < k) (hr₁ : r₁ ∈ Set.Ico 0 k)
    (hr₂ : r₂ ∈ Set.Ico 0 k) (j : ℤ) :
    (Finset.Ico (j * k) ((j + 1) * k)).image (τ r₁ k r₂ k) = Finset.Ico (j * k) ((j + 1) * k) := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    exact fun n hn ↦ τ_same_mod_mapsTo_block hk hr₁ hr₂ j hn
  · rw [Finset.card_image_of_injective _ (Equiv.injective _)]

/-- For `0 < k` and `0 ≤ N`, the class transposition `τ r₁ k r₂ k` maps `Finset.Ico 0 (N * k)`
into itself. -/
theorem τ_same_mod_mapsTo_Ico_mul {r₁ r₂ k : ℤ} (hk : 0 < k) (hr₁ : r₁ ∈ Set.Ico 0 k)
    (hr₂ : r₂ ∈ Set.Ico 0 k) {N : ℤ} (_hN : 0 ≤ N) {n : ℤ} (hn : n ∈ Finset.Ico 0 (N * k)) :
    τ r₁ k r₂ k n ∈ Finset.Ico 0 (N * k) := by
  obtain ⟨m, j, hm, hj⟩ : ∃ m j : ℤ, 0 ≤ m ∧ m < k ∧ 0 ≤ j ∧ j < N ∧ n = m + k * j := by
    refine ⟨n % k, n / k, ?_, ?_, ?_, ?_, ?_⟩
    · exact Int.emod_nonneg _ hk.ne'
    · exact Int.emod_lt_of_pos _ hk
    · exact Int.ediv_nonneg (Finset.mem_Ico.mp hn |>.1) hk.le
    · apply Int.ediv_lt_of_lt_mul hk
      linarith [Finset.mem_Ico.mp hn |>.2]
    · rw [Int.emod_add_mul_ediv]
  have hτm : (τ r₁ k r₂ k) m ∈ Finset.Ico 0 k :=
    τ_same_mod_mapsTo_Ico hk hr₁ hr₂ (Finset.mem_Ico.mpr ⟨hm, hj.1⟩)
  have hτn : (τ r₁ k r₂ k) (m + k * j) = (τ r₁ k r₂ k) m + k * j :=
    τ_same_isShiftPeriodic.add_mul_eq m j
  simp_all only [Set.mem_Ico, Finset.mem_Ico]
  constructor <;> nlinarith only [hτm, hj]

/-- For `0 < k` and `0 ≤ N`, the class transposition `τ r₁ k r₂ k` permutes `Finset.Ico 0 (N * k)`
setwise. -/
theorem τ_same_mod_setwise_Ico_mul {r₁ r₂ k : ℤ} (hk : 0 < k) (hr₁ : r₁ ∈ Set.Ico 0 k)
    (hr₂ : r₂ ∈ Set.Ico 0 k) {N : ℤ} (hN : 0 ≤ N) :
    (Finset.Ico 0 (N * k)).image (τ r₁ k r₂ k) = Finset.Ico 0 (N * k) := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    exact fun x hx ↦ τ_same_mod_mapsTo_Ico_mul hk hr₁ hr₂ hN hx
  · rw [Finset.card_image_of_injective _ (Equiv.injective _)]

end Equiv

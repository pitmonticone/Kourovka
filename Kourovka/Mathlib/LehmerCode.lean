/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Kourovka.Mathlib.FactorialBase
import Mathlib.Data.Fintype.Perm

open Finset BigOperators Equiv

/-! ## Lehmer Code and Factorial Rank -/

/-- The inversion count at position j: number of elements i < j such that
    j appears before i in the permutation σ. -/
def invCount {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) : ℕ :=
  (univ.filter (fun i : Fin n ↦ i.val < j.val ∧ (σ⁻¹ j).val < (σ⁻¹ i).val)).card

/-- The factorial rank: ∑ invCount(σ, j) * j!. -/
def factRank {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ∑ j : Fin n, invCount σ j * j.val.factorial

/-- The Lehmer-code bound: `invCount σ j ≤ j`. -/
lemma invCount_le {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) : invCount σ j ≤ j.val :=
  (card_le_card (t := Iio j) fun x hx ↦ mem_Iio.mpr (mem_filter.mp hx).2.1).trans (by simp)

/-- factRank is bounded: factRank(σ) < n!. -/
lemma factRank_lt {n : ℕ} (σ : Perm (Fin n)) : factRank σ < n.factorial :=
  sum_bounded_factorial_lt n _ (invCount_le σ)

/-! ## Injectivity of Factorial Rank -/

/-- If `σ₁⁻¹` and `σ₂⁻¹` agree on all elements `j'` with `j'.val > j.val`, then `σ₁` and `σ₂`
agree on all positions occupied by elements `> j`; equivalently, the set of positions
occupied by elements `≤ j` is the same. -/
lemma avail_set_eq {n : ℕ} (σ₁ σ₂ : Perm (Fin n)) (j : Fin n)
    (hinv : ∀ j' : Fin n, j.val < j'.val → σ₁⁻¹ j' = σ₂⁻¹ j') :
    (univ.filter (fun p : Fin n ↦ (σ₁ p).val ≤ j.val)) =
      (univ.filter (fun p : Fin n ↦ (σ₂ p).val ≤ j.val)) := by
  ext p
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h1
    by_contra h2
    push_neg at h2
    have heq := hinv (σ₂ p) h2
    simp only [Perm.coe_inv, symm_apply_apply] at heq
    have hpp : σ₁ p = σ₂ p := by rw [← σ₁.apply_symm_apply (σ₂ p), heq]
    rw [hpp] at h1
    omega
  · intro h1
    by_contra h2
    push_neg at h2
    have heq := hinv (σ₁ p) h2
    simp only [Perm.coe_inv, symm_apply_apply] at heq
    have hpp : σ₂ p = σ₁ p := by rw [← σ₂.apply_symm_apply (σ₁ p), ← heq]
    rw [hpp] at h1
    omega

/-- `invCount` decomposition: it counts positions `p > σ⁻¹(j)` with `σ(p) < j`, equivalently
the elements of the "available set" (positions with `σ(p) ≤ j`, excluding `σ⁻¹(j)`) that are
strictly above `σ⁻¹(j)`. -/
lemma invCount_eq_card_avail_gt {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) :
    invCount σ j =
      ((univ.filter (fun p : Fin n ↦ (σ p).val ≤ j.val)).filter
          (fun p ↦ (σ⁻¹ j).val < p.val)).card := by
  refine card_bij (fun p hp ↦ σ⁻¹ p) ?_ ?_ ?_ <;> simp
  · exact fun a ha₁ ha₂ ↦ ⟨le_of_lt ha₁, ha₂⟩
  · refine fun b hb₁ hb₂ ↦ ⟨σ b, ⟨lt_of_le_of_ne hb₁ fun h ↦ hb₂.ne <| ?_, ?_⟩, ?_⟩
    · simp_all [symm_apply_eq]
    · simpa using hb₂
    · simp

/-- Helper for `lehmer_determines_perm`: given that all elements larger than `j` occupy the
same positions in `σ₁` and `σ₂`, equal `invCount` at `j` implies equal position of `j`. -/
lemma inv_eq_of_invCount_eq_above {n : ℕ} (σ₁ σ₂ : Perm (Fin n)) (j : Fin n)
    (hinv : ∀ j' : Fin n, j.val < j'.val → σ₁⁻¹ j' = σ₂⁻¹ j')
    (hcount : invCount σ₁ j = invCount σ₂ j) : σ₁⁻¹ j = σ₂⁻¹ j := by
  rw [invCount_eq_card_avail_gt σ₁ j, invCount_eq_card_avail_gt σ₂ j] at hcount
  have h_avail_eq := avail_set_eq σ₁ σ₂ j hinv
  simp_all only [Fin.val_fin_lt, Perm.coe_inv, Fin.val_fin_le, Finset.ext_iff, mem_filter, mem_univ,
    true_and]
  apply Fin.ext_iff.mpr
  contrapose! hcount
  cases lt_or_gt_of_ne hcount <;> simp_all [filter_filter]
  · refine ne_of_gt (card_lt_card ?_)
    simp_all [ssubset_def, subset_iff]
    grind
  · refine ne_of_lt (card_lt_card ?_)
    simp_all only [ssubset_def, subset_iff, mem_filter]
    grind

/-- A permutation is determined by its Lehmer code: if `invCount σ₁ = invCount σ₂` pointwise,
then `σ₁ = σ₂`. -/
lemma lehmer_determines_perm {n : ℕ} (σ₁ σ₂ : Perm (Fin n))
    (h : ∀ j, invCount σ₁ j = invCount σ₂ j) : σ₁ = σ₂ := by
  have h_ind : ∀ j : Fin n, (∀ j' : Fin n, j.val < j'.val → σ₁⁻¹ j' = σ₂⁻¹ j') → σ₁⁻¹ j = σ₂⁻¹ j :=
    fun j hj ↦ inv_eq_of_invCount_eq_above σ₁ σ₂ j hj (h j)
  have h_all : ∀ j : Fin n, σ₁⁻¹ j = σ₂⁻¹ j := by
    have h_induction : ∀ k : ℕ, k ≤ n → ∀ j : Fin n, n - j.val = k → σ₁⁻¹ j = σ₂⁻¹ j := by
      intro k hk
      induction' k using Nat.strong_induction_on with k ih
      apply fun j hj ↦ h_ind _ fun j' hj' ↦ ih (n - j'.val) _ (n.sub_le j'.val) j' rfl
      omega
    exact fun j ↦ h_induction _ (Nat.sub_le _ _) _ rfl
  exact inv_injective (Equiv.ext h_all)

/-- `invCount σ j` equals the number of positions strictly after `σ⁻¹(j)` whose images under
`σ` are strictly below `j`. -/
lemma invCount_eq_card_avail_after {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) :
    invCount σ j = (univ.filter (fun p : Fin n ↦ (σ⁻¹ j).val < p.val ∧ (σ p).val < j.val)).card :=
  by refine card_bij (fun i hi ↦ σ⁻¹ i) ?_ ?_ ?_ <;> simp <;> grind

/-- factRank is injective. Proof: if factRank σ₁ = factRank σ₂, then by
    factorial_base_unique the Lehmer codes agree, and by lehmer_determines_perm
    the permutations are equal. -/
lemma factRank_injective {n : ℕ} : (factRank (n := n)).Injective := fun σ₁ σ₂ heq ↦
  lehmer_determines_perm _ _ fun j ↦
    congr_fun (factorial_base_unique n _ _ (invCount_le σ₁) (invCount_le σ₂) heq) j

/-! ## Surjectivity of Factorial Rank -/

/-- The image of `factRank` over `Sₙ` is exactly `{0, …, n! − 1}`. -/
lemma factRank_image (n : ℕ) : (univ : Finset (Perm (Fin n))).image factRank = range n.factorial := by
  refine eq_of_subset_of_card_le ?_ ?_
  · exact Finset.image_subset_iff.mpr fun σ _ ↦ Finset.mem_range.mpr (factRank_lt σ)
  · simp [card_image_of_injective _ factRank_injective, Fintype.card_perm]

/-- For each `r < n!`, there exists a permutation with `factRank σ = r`. -/
lemma factRank_surj {n : ℕ} (r : ℕ) (hr : r < n.factorial) : ∃ σ : Perm (Fin n), factRank σ = r :=
  Finset.mem_image.mp ((factRank_image n).symm ▸ Finset.mem_range.mpr hr) |>
    Exists.imp fun _ hx ↦ hx.2

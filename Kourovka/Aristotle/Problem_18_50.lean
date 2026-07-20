/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Cases

/-!
# Kourovka Notebook Problem 18.50

For every `n` and every `k` with `1 ≤ k ≤ n!`, there exists a group `G` with `n` pairwise
distinct elements `g₀, …, gₙ₋₁` whose permuted products `g_{σ(0)} · … · g_{σ(n-1)}` over
`σ ∈ Sₙ` realise *exactly* `k` distinct values.

The witness is a twisted group `G = ℤⁿ × ℤ/kℤ` whose central component records the
factorial rank of a permutation modulo `k`; surjectivity of the factorial rank
`Sₙ → {0, …, n!−1}` then exhibits all `k` residues, while no other product values can
appear because of the product formula `P(σ) = ((1, …, 1), factRank(σ) mod k)`.

## Main results

* `TwGrp` : the twisted group `ℤⁿ × ℤ/kℤ`.
* `gElem` : the distinguished elements `gⱼ = (eⱼ, 0)`.
* `factRank_injective`, `factRank_surj` : the factorial rank is a bijection
  `Sₙ → {0, …, n!−1}`.
* `permProd_eq` : the product formula `permProd n k σ = ((1,…,1), factRank σ mod k)`.
* `products_card` : the number of distinct permuted products equals `k`.
* `kourovka_18_50` : the main theorem.

## Structure

1. **Factorial base representation**: uniqueness and bounds.
2. **Lehmer code**: inversion count and factorial rank of permutations.
3. **Injectivity and surjectivity** of the factorial rank.
4. **Bilinear form** `B` and its properties.
5. **Twisted group** `G = ℤⁿ × ℤ/kℤ` with the modified multiplication.
6. **Distinguished elements** `gⱼ = (eⱼ, 0)`.
7. **Product formula** `P(σ) = ((1, …, 1), factRank(σ) mod k)`.
8. **Counting argument** and the main theorem.
-/

open Finset BigOperators Equiv

/-! ## Part 1: Factorial Base Properties -/

/-- The telescoping identity `∑_{j=0}^{n-1} j · j! = n! − 1`, proved by induction on `n`. -/
lemma sum_id_mul_factorial : ∀ n : ℕ, ∑ j : Fin n, j.val * j.val.factorial = n.factorial - 1 := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    simp_all [Fin.sum_univ_castSucc, Nat.factorial_succ]
    exact eq_tsub_of_add_eq (by
          rw [show (m + 1) * m.factorial = m.factorial + m * m.factorial from by ring]
          have := Nat.factorial_pos m
          omega)

/-- Bound on a factorial-base sum: if `0 ≤ aⱼ ≤ j` for all `j`, then
`∑ aⱼ · j! ≤ n! − 1`. -/
lemma sum_bounded_factorial_le (n : ℕ) (a : Fin n → ℕ) (ha : ∀ j, a j ≤ j.val) :
    ∑ j : Fin n, a j * j.val.factorial ≤ n.factorial - 1 := by
  exact le_trans (Finset.sum_le_sum fun _ _ ↦ Nat.mul_le_mul_right _ (ha _))
      (sum_id_mul_factorial _ ▸ le_rfl)

/-- Strict bound on a factorial-base sum: if `0 ≤ aⱼ ≤ j` for all `j`, then
`∑ aⱼ · j! < n!`. -/
lemma sum_bounded_factorial_lt (n : ℕ) (a : Fin n → ℕ) (ha : ∀ j, a j ≤ j.val) :
    ∑ j : Fin n, a j * j.val.factorial < n.factorial := by
  exact lt_of_le_of_lt (sum_bounded_factorial_le n a ha)
      (Nat.sub_lt (Nat.factorial_pos _) zero_lt_one)

/-- Splitting a `Fin (n + 1)` sum into the last term plus a `Fin n` sum. -/
lemma fin_sum_snoc {n : ℕ} (f : Fin (n + 1) → ℕ) :
    ∑ j : Fin (n + 1), f j =
      f ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ + ∑ j : Fin n, f (Fin.castSucc j) := by
  rw [Fin.sum_univ_castSucc, add_comm]
  rfl

/-- The highest factorial-base digit is recovered by division: if `aⱼ ≤ j` and
`S = ∑ aⱼ · j!`, then `S / n! = aₙ`. -/
lemma factorial_base_top_digit {n : ℕ} (a : Fin (n + 1) → ℕ) (ha : ∀ j, a j ≤ j.val) :
    (∑ j : Fin (n + 1), a j * j.val.factorial) / n.factorial =
      a ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
  have h_split :
    ∑ j : Fin (n + 1), a j * (Nat.factorial j.val) =
      a ⟨n, Nat.lt_succ_self n⟩ * (Nat.factorial n) +
        ∑ j : Fin n, a (Fin.castSucc j) * (Nat.factorial j.val) :=
    by convert fin_sum_snoc _ using 2
  rw [h_split, Nat.add_div] <;> norm_num [Nat.factorial_pos]
  rw [Nat.div_eq_of_lt, if_neg] <;> norm_num
  · exact Nat.mod_lt _ (Nat.factorial_pos _)
  · convert sum_bounded_factorial_lt n (fun j ↦ a (Fin.castSucc j))
        (fun j ↦ ha (Fin.castSucc j)) using 1

/-- **Uniqueness of factorial base representation.** If two sequences of digits (each bounded
by their index) give the same weighted sum, they are equal. The proof is by induction on `n`,
extracting the top digit via division. -/
lemma factorial_base_unique :
    ∀ (n : ℕ) (a b : Fin n → ℕ),
      (∀ j, a j ≤ j.val) →
        (∀ j, b j ≤ j.val) →
          (∑ j : Fin n, a j * j.val.factorial = ∑ j : Fin n, b j * j.val.factorial) → a = b := by
  intros n b ha hb h
  induction' n with n ih
  · intro _
    exact funext (fun x ↦ Fin.elim0 x)
  · intro h_eq
    have h_top : b ⟨n, Nat.lt_succ_self n⟩ = ha ⟨n, Nat.lt_succ_self n⟩ := by
      have h1 := factorial_base_top_digit b hb
      have h2 := factorial_base_top_digit ha h
      rw [h_eq] at h1
      omega
    have h_remainder :
      ∑ j : Fin n, b (Fin.castSucc j) * (j.val).factorial =
        ∑ j : Fin n, ha (Fin.castSucc j) * (j.val).factorial := by
      simp_all [Fin.sum_univ_castSucc]
      simp_all [Fin.last]
    have h_eq' : b ∘ Fin.castSucc = ha ∘ Fin.castSucc := by
      exact ih _ _ (fun j ↦ hb _) (fun j ↦ h _) h_remainder
    exact funext (by
          exact fun x ↦
            if hx : x.val < n then congr_fun h_eq' ⟨x.val, hx⟩
            else by
              rw [show x = ⟨n, Nat.lt_succ_self n⟩ from
                  le_antisymm (Fin.le_last _) (not_lt.mp hx)]
              exact h_top)

/-! ## Part 2: Lehmer Code and Factorial Rank -/

/-- The inversion count at position j: number of elements i < j such that
    j appears before i in the permutation σ. -/
def invCount {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) : ℕ :=
  (univ.filter (fun i : Fin n ↦ i.val < j.val ∧ (σ⁻¹ j).val < (σ⁻¹ i).val)).card

/-- The factorial rank: ∑ invCount(σ, j) * j!. -/
def factRank {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ∑ j : Fin n, invCount σ j * j.val.factorial

/-- The Lehmer-code bound: `invCount σ j ≤ j`. -/
lemma invCount_le {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) : invCount σ j ≤ j.val := by
  refine' le_trans (Finset.card_le_card _) _
  exact Finset.Iio j
  · exact fun x hx ↦ Finset.mem_Iio.mpr <| Finset.mem_filter.mp hx |>.2.1
  · simp

/-- factRank is bounded: factRank(σ) < n!. -/
lemma factRank_lt {n : ℕ} (σ : Perm (Fin n)) : factRank σ < n.factorial :=
  sum_bounded_factorial_lt n _ (invCount_le σ)

/-! ## Part 3: Injectivity of Factorial Rank -/

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
    have : σ₁ p = σ₂ p := by
      have := σ₁.apply_symm_apply (σ₂ p)
      rw [heq] at this
      exact this
    rw [this] at h1
    omega
  · intro h1
    by_contra h2
    push_neg at h2
    have heq := hinv (σ₁ p) h2
    simp only [Perm.coe_inv, symm_apply_apply] at heq
    have : σ₂ p = σ₁ p := by conv_lhs => rw [heq]; simp
    rw [this] at h1
    omega

/-- `invCount` decomposition: it counts positions `p > σ⁻¹(j)` with `σ(p) < j`, equivalently
the elements of the "available set" (positions with `σ(p) ≤ j`, excluding `σ⁻¹(j)`) that are
strictly above `σ⁻¹(j)`. -/
lemma invCount_eq_card_avail_gt {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) :
    invCount σ j =
      ((univ.filter (fun p : Fin n ↦ (σ p).val ≤ j.val)).filter
          (fun p ↦ (σ⁻¹ j).val < p.val)).card := by
  refine' Finset.card_bij (fun p hp ↦ σ⁻¹ p) _ _ _ <;> simp
  · exact fun a ha₁ ha₂ ↦ ⟨le_of_lt ha₁, ha₂⟩
  · exact fun b hb₁ hb₂ ↦
      ⟨σ b,
        ⟨lt_of_le_of_ne hb₁ fun h ↦ hb₂.ne <| by simp_all [Equiv.symm_apply_eq], by
          simpa using hb₂⟩,
        by simp⟩

/-- Helper for `lehmer_determines_perm`: given that all elements larger than `j` occupy the
same positions in `σ₁` and `σ₂`, equal `invCount` at `j` implies equal position of `j`. -/
lemma inv_eq_of_invCount_eq_above {n : ℕ} (σ₁ σ₂ : Perm (Fin n)) (j : Fin n)
    (hinv : ∀ j' : Fin n, j.val < j'.val → σ₁⁻¹ j' = σ₂⁻¹ j')
    (hcount : invCount σ₁ j = invCount σ₂ j) : σ₁⁻¹ j = σ₂⁻¹ j := by
  have h_av1 :
    invCount σ₁ j =
      ((Finset.univ.filter (fun p : Fin n ↦ (σ₁ p).val ≤ j.val)).filter
          (fun p ↦ (σ₁⁻¹ j).val < p.val)).card := invCount_eq_card_avail_gt σ₁ j
  have h_av2 :
    invCount σ₂ j =
      ((Finset.univ.filter (fun p : Fin n ↦ (σ₂ p).val ≤ j.val)).filter
          (fun p ↦ (σ₂⁻¹ j).val < p.val)).card :=
    by convert invCount_eq_card_avail_gt σ₂ j using 1
  rw [h_av1, h_av2] at hcount
  have h_avail_eq :
    (Finset.univ.filter (fun p : Fin n ↦ (σ₁ p).val ≤ j.val)) =
      (Finset.univ.filter (fun p : Fin n ↦ (σ₂ p).val ≤ j.val)) := avail_set_eq σ₁ σ₂ j hinv
  simp_all [Finset.ext_iff]
  apply Fin.ext_iff.mpr
  contrapose! hcount
  cases lt_or_gt_of_ne hcount <;> simp_all [Finset.filter_filter]
  · refine ne_of_gt (Finset.card_lt_card ?_)
    simp_all [Finset.ssubset_def, Finset.subset_iff]
    grind
  · refine ne_of_lt (Finset.card_lt_card ?_)
    simp_all only [ssubset_def, subset_iff, mem_filter]
    grind +revert

/-- A permutation is determined by its Lehmer code: if `invCount σ₁ = invCount σ₂` pointwise,
then `σ₁ = σ₂`. -/
lemma lehmer_determines_perm {n : ℕ} (σ₁ σ₂ : Perm (Fin n))
    (h : ∀ j, invCount σ₁ j = invCount σ₂ j) : σ₁ = σ₂ := by
  have h_ind :
    ∀ j : Fin n, (∀ j' : Fin n, j.val < j'.val → σ₁⁻¹ j' = σ₂⁻¹ j') → σ₁⁻¹ j = σ₂⁻¹ j := by
    exact fun j hj ↦ inv_eq_of_invCount_eq_above σ₁ σ₂ j hj (h j)
  have h_all : ∀ j : Fin n, σ₁⁻¹ j = σ₂⁻¹ j := by
    have h_induction : ∀ k : ℕ, k ≤ n → ∀ j : Fin n, n - j.val = k → σ₁⁻¹ j = σ₂⁻¹ j := by
      intro k hk
      induction' k using Nat.strong_induction_on with k ih
      apply fun j hj ↦ h_ind _ fun j' hj' ↦ ih (n - j'.val) _ (Nat.sub_le n j'.val) j' rfl
      omega
    exact fun j ↦ h_induction _ (Nat.sub_le _ _) _ rfl
  exact inv_injective (Equiv.ext h_all)

/-- `invCount σ j` equals the number of positions strictly after `σ⁻¹(j)` whose images under
`σ` are strictly below `j`. -/
lemma invCount_eq_card_avail_after {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) :
    invCount σ j =
      (univ.filter (fun p : Fin n ↦ (σ⁻¹ j).val < p.val ∧ (σ p).val < j.val)).card := by
  refine Finset.card_bij (fun i hi ↦ σ⁻¹ i) ?_ ?_ ?_ <;> simp <;> grind

/-- factRank is injective. Proof: if factRank σ₁ = factRank σ₂, then by
    factorial_base_unique the Lehmer codes agree, and by lehmer_determines_perm
    the permutations are equal. -/
lemma factRank_injective {n : ℕ} : Function.Injective (factRank (n := n)) :=
  fun σ₁ σ₂ heq ↦ lehmer_determines_perm _ _
    fun j ↦ congr_fun (factorial_base_unique n _ _ (invCount_le σ₁) (invCount_le σ₂) heq) j

/-! ## Part 4: Surjectivity of Factorial Rank -/

/-- The image of `factRank` over `Sₙ` is exactly `{0, …, n! − 1}`. -/
lemma factRank_image (n : ℕ) :
    (univ : Finset (Perm (Fin n))).image factRank = Finset.range n.factorial := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · exact Finset.image_subset_iff.mpr fun σ _ ↦ Finset.mem_range.mpr (factRank_lt σ)
  · simp [Finset.card_image_of_injective _ factRank_injective, Fintype.card_perm]

/-- For each `r < n!`, there exists a permutation with `factRank σ = r`. -/
lemma factRank_surj {n : ℕ} (r : ℕ) (hr : r < n.factorial) :
    ∃ σ : Perm (Fin n), factRank σ = r :=
  Finset.mem_image.mp ((factRank_image n).symm ▸ Finset.mem_range.mpr hr) |> Exists.imp fun _ hx ↦ hx.2

/-! ## Part 5: The Bilinear Form -/

/-- The bilinear form B as an integer:
    B(u, v) = ∑_{i < j} u_j * v_i * j! -/
def B_int (n : ℕ) (u v : Fin n → ℤ) : ℤ :=
  ∑ j : Fin n, ∑ i : Fin n, if i.val < j.val then u j * v i * (j.val.factorial : ℤ) else 0

/-- `B` is left-additive: `B(u₁ + u₂, v) = B(u₁, v) + B(u₂, v)`. -/
lemma B_int_add_left (n : ℕ) (u₁ u₂ v : Fin n → ℤ) :
    B_int n (u₁ + u₂) v = B_int n u₁ v + B_int n u₂ v := by
  simp only [B_int, Fin.val_fin_lt, Pi.add_apply, add_mul]
  simpa only [← Finset.sum_add_distrib] using
    Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ by split_ifs <;> ring

/-- `B` is right-additive: `B(u, v₁ + v₂) = B(u, v₁) + B(u, v₂)`. -/
lemma B_int_add_right (n : ℕ) (u v₁ v₂ : Fin n → ℤ) :
    B_int n u (v₁ + v₂) = B_int n u v₁ + B_int n u v₂ := by
  simp only [B_int, Fin.val_fin_lt, Pi.add_apply]
  simpa only [← Finset.sum_add_distrib] using
    Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ by split_ifs <;> ring

/-- `B` vanishes on the left zero: `B(0, v) = 0`. -/
lemma B_int_zero_left (n : ℕ) (v : Fin n → ℤ) : B_int n 0 v = 0 :=
  Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ by simp

/-- `B` vanishes on the right zero: `B(u, 0) = 0`. -/
lemma B_int_zero_right (n : ℕ) (u : Fin n → ℤ) : B_int n u 0 = 0 := by simp [B_int, mul_zero]

/-- `B` is left-antilinear with respect to negation: `B(-u, v) = -B(u, v)`. -/
lemma B_int_neg_left (n : ℕ) (u v : Fin n → ℤ) : B_int n (-u) v = -B_int n u v := by
  simp only [B_int, Fin.val_fin_lt, Pi.neg_apply, neg_mul, ← sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring

/-! ## Part 6: The Twisted Group -/

/-- The twisted group: G = ℤⁿ × ℤ/kℤ with multiplication
    (u, r)(v, s) = (u + v, r + s + B(u, v)). -/
@[ext]
structure TwGrp (n : ℕ) (k : ℕ) where
  vec : Fin n → ℤ
  cent : ZMod k

/-- Decidable equality on the twisted group, derived componentwise. -/
instance instDecidableEqTwGrp (n k : ℕ) : DecidableEq (TwGrp n k) := fun a b ↦ by
  cases a with
  | mk va ca =>
    cases b with
    | mk vb cb =>
      rw [TwGrp.mk.injEq]
      exact instDecidableAnd

/-- The group structure on `TwGrp n k`. Associativity reduces to the bilinearity identity
`B(u, v) + B(u + v, w) = B(v, w) + B(u, v + w)`; the left inverse is
`(-u, -r + B(u, u)) · (u, r) = (0, B(u, u) + B(-u, u)) = (0, 0)` since `B(-u, u) = -B(u, u)`. -/
instance instGroupTwGrp (n k : ℕ) : Group (TwGrp n k) where
  mul a b := ⟨a.vec + b.vec, a.cent + b.cent + Int.cast (B_int n a.vec b.vec)⟩
  one := ⟨0, 0⟩
  inv a := ⟨-a.vec, -a.cent + Int.cast (B_int n a.vec a.vec)⟩
  mul_assoc := by
    intros a b c
    apply TwGrp.ext
    · exact add_assoc _ _ _
    · have h_assoc :
        B_int n (a.vec + b.vec) c.vec = B_int n a.vec c.vec + B_int n b.vec c.vec ∧
          B_int n a.vec (b.vec + c.vec) = B_int n a.vec b.vec + B_int n a.vec c.vec :=
        by exact ⟨B_int_add_left n a.vec b.vec c.vec, B_int_add_right n a.vec b.vec c.vec⟩
      exact show
          (a.cent + b.cent + ↑(B_int n a.vec b.vec) + c.cent +
                ↑(B_int n (a.vec + b.vec) c.vec) :
              ZMod k) =
            (a.cent + (b.cent + c.cent + ↑(B_int n b.vec c.vec)) +
                ↑(B_int n a.vec (b.vec + c.vec)) :
              ZMod k)
          from by
          push_cast [h_assoc]
          ring
  one_mul := by
    intro a
    ext
    · exact zero_add _
    · exact show (0 + a.cent + B_int n 0 a.vec : ZMod k) = a.cent from by simp [B_int_zero_left]
  mul_one := by
    intro a
    convert congr_arg _ ?_
    convert rfl
    swap
    exact ⟨0, 0⟩
    · exact congr_arg₂ _ (add_zero _) (by simp [B_int_zero_right])
    · rfl
  inv_mul_cancel := by
    intro a
    convert @TwGrp.ext _ _ _ _ _ _
    · exact neg_add_cancel _
    · exact show (-a.cent + B_int n a.vec a.vec : ZMod k) + a.cent + B_int n (-a.vec) a.vec = 0 from by
          rw [show B_int n (-a.vec) a.vec = -B_int n a.vec a.vec from B_int_neg_left n a.vec a.vec]
          push_cast
          ring

/-! ## Part 7: Distinguished Elements -/

/-- Standard basis vector e_j ∈ ℤⁿ. -/
def stdBasisInt (n : ℕ) (j : Fin n) : Fin n → ℤ := fun i ↦ if i = j then 1 else 0

/-- The j-th distinguished element g_j = (e_j, 0). -/
def gElem (n k : ℕ) (j : Fin n) : TwGrp n k :=
  ⟨stdBasisInt n j, 0⟩

/-- Standard basis vectors `eⱼ` are pairwise distinct. -/
lemma stdBasisInt_injective (n : ℕ) : Function.Injective (stdBasisInt n) := by
  unfold stdBasisInt
  intro i j hij
  have := congr_fun hij i
  simp only [↓reduceIte, left_eq_ite_iff, one_ne_zero, imp_false, Decidable.not_not] at this
  exact this

/-- The distinguished elements are pairwise distinct. -/
lemma gElem_injective (n k : ℕ) : Function.Injective (gElem n k) := by
  intro j₁ j₂ h
  exact stdBasisInt_injective n (TwGrp.mk.inj h).1

/-- Evaluation of `B` on standard basis vectors: `B(e_a, e_b) = a!` if `b < a`, else `0`. -/
lemma B_int_stdBasis (n : ℕ) (a b : Fin n) :
    B_int n (stdBasisInt n a) (stdBasisInt n b) =
      if b.val < a.val then (a.val.factorial : ℤ) else 0 := by
  unfold B_int
  unfold stdBasisInt
  split_ifs <;> simp_all [Finset.sum_ite, Finset.filter_lt_eq_Ioi]

/-- The sum of all standard basis vectors is the all-ones function. -/
lemma sum_stdBasisInt (n : ℕ) : ∑ j : Fin n, stdBasisInt n j = fun _ ↦ 1 := by
  funext i
  unfold stdBasisInt
  have :
    ∀ (s : Finset (Fin n)),
      (∑ j ∈ s, fun (k : Fin n) ↦ if k = j then (1 : ℤ) else 0) i =
        ∑ j ∈ s, if i = j then (1 : ℤ) else 0 := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Pi.add_apply, ih]
  rw [this]
  simp

/-- Permutation invariance of the sum of standard basis vectors. -/
lemma sum_stdBasisInt_perm (n : ℕ) (σ : Perm (Fin n)) :
    ∑ j : Fin n, stdBasisInt n (σ j) = fun _ ↦ 1 := by
  convert sum_stdBasisInt n using 1
  conv_rhs => rw [← Equiv.sum_comp σ]

/-! ## Part 8: Product Formula -/

/-- The product g_{σ(0)} * g_{σ(1)} * ... * g_{σ(n-1)}. -/
def permProd (n k : ℕ) (σ : Perm (Fin n)) : TwGrp n k :=
  (List.ofFn (fun i : Fin n ↦ gElem n k (σ i))).prod

/-- The `vec` component of a list product is the sum of the `vec` components, by induction
on the list using the definitional unfolding `(a * b).vec = a.vec + b.vec` at each `cons` step. -/
lemma list_prod_vec {n k : ℕ} :
    ∀ (l : List (TwGrp n k)), l.prod.vec = (l.map TwGrp.vec).foldr (· + ·) 0
  | [] => by simp [List.prod_nil, show (1 : TwGrp n k).vec = 0 from rfl]
  | a :: l => by
    induction l generalizing a <;>
      simp_all [List.prod_cons, show ∀ (x y : TwGrp n k), (x * y).vec = x.vec + y.vec from fun _ _ => rfl]

/-- The vector component of `permProd n k σ` is the all-ones function. -/
lemma permProd_vec (n k : ℕ) (σ : Perm (Fin n)) : (permProd n k σ).vec = fun _ ↦ 1 := by
  have h_map :
    (List.ofFn (fun i : Fin n ↦ gElem n k (σ i))).map TwGrp.vec =
      List.ofFn (fun i : Fin n ↦ stdBasisInt n (σ i)) := by
    simp [gElem]
    rfl
  convert list_prod_vec _ using 1
  rw [h_map, List.ofFn_eq_map]
  convert sum_stdBasisInt_perm n σ |> Eq.symm using 1

/-- The pairwise sum of B_int values over position pairs with l < m. -/
def pairwiseB (n : ℕ) (σ : Perm (Fin n)) : ℤ :=
  ∑ l : Fin n,
    ∑ m : Fin n,
      if l.val < m.val then B_int n (stdBasisInt n (σ l)) (stdBasisInt n (σ m)) else 0

set_option maxHeartbeats 800000 in
/-- The `cent` component of a list product whose terms all have zero `cent` equals the sum of
pairwise `B` values. The proof is by induction on the list, applying bilinearity of `B` at
each `cons` step. -/
lemma list_prod_cent_zero {n k : ℕ} :
    ∀ (l : List (TwGrp n k)) (_ : ∀ a ∈ l, a.cent = 0),
      ∃ (s : ℤ),
        l.prod.cent = Int.cast s ∧
          s =
            ∑ i : Fin l.length,
              ∑ j : Fin l.length,
                if i.val < j.val then B_int n (l.get i).vec (l.get j).vec else 0
  | [], _ => ⟨0, by simp [show (1 : TwGrp n k).cent = 0 from rfl], by simp⟩
  | a :: l, h => by
    induction' l with b l ih generalizing a <;> simp_all [Fin.sum_univ_succ,
      show ∀ (x y : TwGrp n k), (x * y).cent = x.cent + y.cent + Int.cast (B_int n x.vec y.vec) from fun _ _ => rfl]
    · show _ = _
      rw [show (b * l.prod).vec = b.vec + l.prod.vec from rfl, B_int_add_right]
      ring_nf
      rw [show B_int n a.vec l.prod.vec = ∑ x : Fin l.length, B_int n a.vec l[↑x].vec from ?_]
      push_cast
      ring_nf
      · congr! 2
      · have h_sum : l.prod.vec = List.foldr (· + ·) 0 (List.map TwGrp.vec l) := list_prod_vec l
        have h_sum :
          ∀ (l : List (Fin n → ℤ)),
            B_int n a.vec (List.foldr (· + ·) 0 l) = ∑ x : Fin l.length, B_int n a.vec l[x] := by
          intro l
          induction l <;> simp_all [Fin.sum_univ_succ]
          ring_nf
          · exact B_int_zero_right n a.vec
          · rw [← ‹B_int n a.vec (List.foldr (fun x1 x2 ↦ x1 + x2) 0 _) =
              (List.map (B_int n a.vec) _).sum›, B_int_add_right]
        convert h_sum (List.map TwGrp.vec l) using 1
        · congr! 1
        · simp only [Fin.getElem_fin, List.getElem_map]
          convert rfl <;> grind

/-- The pairwise `B` sum equals `factRank` (cast to `ℤ`). This is a sum rearrangement: group
inversions by their larger element `j`, noting that each inversion `(j, i)` with `i < j`
contributes `j!` to the sum. -/
lemma pairwiseB_eq_factRank (n : ℕ) (σ : Perm (Fin n)) : pairwiseB n σ = (factRank σ : ℤ) := by
  unfold pairwiseB factRank
  simp [invCount_eq_card_avail_after, B_int_stdBasis]
  simp [Finset.sum_ite, Finset.filter_filter]
  refine' Finset.sum_bij (fun x _ ↦ σ x) _ _ _ _ <;> simp
  exact σ.surjective

/-- The central component of `permProd n k σ` equals `factRank σ` reduced modulo `k`. -/
lemma permProd_cent (n k : ℕ) (σ : Perm (Fin n)) :
    (permProd n k σ).cent = (factRank σ : ZMod k) := by
  obtain ⟨s, hs⟩ :=
    list_prod_cent_zero (List.ofFn fun i ↦ gElem n k (σ i)) (by simp [gElem])
  convert hs.1 using 1
  convert congr_arg ((↑) : ℤ → ZMod k) (pairwiseB_eq_factRank n σ |> Eq.symm) using 1
  · norm_cast
  · convert congr_arg ((↑) : ℤ → ZMod k) hs.2 using 1
    simp [pairwiseB, gElem]
    convert rfl <;> grind

/-- Full characterization: permProd equals the explicit pair. -/
lemma permProd_eq (n k : ℕ) (σ : Perm (Fin n)) :
    permProd n k σ = ⟨fun _ ↦ 1, (factRank σ : ZMod k)⟩ := by
  ext
  · exact congr_fun (permProd_vec n k σ) _
  · exact permProd_cent n k σ

/-! ## Part 9: Counting Argument -/

/-- The natural-number range `{0, …, m − 1}` surjects onto `ZMod k` whenever `k ≤ m`. -/
lemma natCast_range_surj_zmod (k m : ℕ) (hk : 0 < k) (hm : k ≤ m) :
    ∀ r : ZMod k, ∃ i ∈ Finset.range m, (i : ZMod k) = r := by
  rcases k with (_ | _ | k) <;> simp_all [ZMod]
  · exact ⟨0, hm⟩
  · exact fun r ↦ ⟨r, by omega, by simp⟩

/-- The composition `factRank` followed by `Nat.cast : ℕ → ZMod k` covers all of `ZMod k`. -/
lemma factRank_mod_surj (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n.factorial) :
    ∀ r : ZMod k, ∃ σ : Perm (Fin n), (factRank σ : ZMod k) = r := by
  intro r
  obtain ⟨r', hr', hr⟩ : ∃ r' ∈ Finset.range (n.factorial), (r' : ZMod k) = r :=
    natCast_range_surj_zmod k n.factorial hk hkn r
  exact Exists.elim (factRank_surj r' (Finset.mem_range.mp hr')) fun σ hσ ↦ ⟨σ, hσ.symm ▸ hr⟩

/-- The image of `σ ↦ permProd n k σ` has cardinality exactly `k`, the counting argument
that produces the required `k` distinct permuted products. -/
lemma products_card (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n.factorial) :
    (univ.image (fun σ : Perm (Fin n) ↦ permProd n k σ)).card = k := by
  have h_image :
      Finset.image (fun σ : Perm (Fin n) ↦ permProd n k σ) Finset.univ =
        Finset.image (fun σ : Perm (Fin n) ↦ ⟨fun _ ↦ 1, (factRank σ : ZMod k)⟩) Finset.univ :=
    Finset.image_congr fun σ _ ↦ permProd_eq n k σ ▸ rfl
  rcases k with (_ | _ | k) <;> simp_all
  · simp only [card_eq_one, Finset.ext_iff, mem_image, mem_univ, true_and, mem_singleton]
    refine ⟨⟨fun _ ↦ 1, 0⟩, fun a ↦ ?_⟩
    constructor <;> intro h <;> rcases a with ⟨a, b⟩ <;> simp_all [ZMod]
    grind
  · rw [Finset.card_eq_of_bijective]
    use fun i hi ↦ ⟨fun _ ↦ 1, i⟩
    · simp only [mem_image, mem_univ, true_and, Order.lt_add_one_iff, exists_prop,
        forall_exists_index, forall_apply_eq_imp_iff, TwGrp.mk.injEq] at *
      exact fun σ ↦
        ⟨factRank σ % (k + 1 + 1), Nat.le_of_lt_succ <| Nat.mod_lt _ <| Nat.succ_pos _, by
          simp [ZMod.natCast_mod]⟩
    · intro i hi
      have := factRank_mod_surj n (k + 1 + 1) (by omega) (by omega) (i : ZMod (k + 1 + 1))
      aesop
    · exact fun i j hi hj h ↦ Nat.mod_eq_of_lt (by omega : i < k + 2) ▸
        Nat.mod_eq_of_lt (by omega : j < k + 2) ▸ by
          simpa [ZMod.natCast_eq_natCast_iff'] using h

/-! ## Part 10: Main Theorem -/

/-- **Kourovka Notebook Problem 18.50.**

For every `n` and every `k` with `1 ≤ k ≤ n!`, there exists a (decidable) group `G` together
with `n` pairwise distinct elements `g₀, …, gₙ₋₁ ∈ G` whose permuted products
`g_{σ(0)} · … · g_{σ(n−1)}` over `σ ∈ Sₙ` realise *exactly* `k` distinct values.

The witness is the twisted group `TwGrp n k = ℤⁿ × ℤ/kℤ` with the cocycle
`B(u, v) = ∑_{i < j} u_j · v_i · j!`, taking `gⱼ = (eⱼ, 0)`. -/
theorem kourovka_18_50 (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n.factorial) :
    ∃ (G : Type) (_ : Group G) (_ : DecidableEq G) (g : Fin n → G),
      Function.Injective g ∧
      (univ.image (fun σ : Perm (Fin n) ↦ (List.ofFn (fun i : Fin n ↦ g (σ i))).prod)).card = k :=
  ⟨TwGrp n k, instGroupTwGrp n k, instDecidableEqTwGrp n k,
    gElem n k, gElem_injective n k, products_card n k hk1 hkn⟩

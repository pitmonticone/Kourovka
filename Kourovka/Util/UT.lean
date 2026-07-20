/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Cases
import Mathlib.LinearAlgebra.Matrix.Defs

/-! ## UT Group -/

/-- The underlying space of "matrices": finitely-supported integer-valued functions on pairs
of lattice points `(ℤ × ℤ) × (ℤ × ℤ)`. An element `f` represents the off-diagonal part of a
unipotent matrix `I + f` whose `(p, q)` entry is `f (p, q)`. -/
abbrev UTBase :=
  ((ℤ × ℤ) × (ℤ × ℤ)) →₀ ℤ

/-- Matrix multiplication of two `UTBase` elements: `(matMul f g) (p, q) = ∑ₖ f (p, k) · g (k, q)`,
realised as a double `Finsupp.sum` over the supports. -/
noncomputable def matMul (f g : UTBase) : UTBase :=
  f.sum fun pk a ↦ g.sum fun kq b ↦ if pk.2 = kq.1 then Finsupp.single (pk.1, kq.2) (a * b) else 0

/-- The group law on unipotent matrices `I + f`: since `(I + f)(I + g) = I + (f + g + fg)`, the
product of the off-diagonal parts is `utMul f g = f + g + matMul f g`. -/
noncomputable def utMul (f g : UTBase) : UTBase :=
  f + g + matMul f g

/-- Definitional unfolding of the group law: `utMul f g = f + g + matMul f g`. -/
lemma utMul_eq_add_matMul (f g : UTBase) : utMul f g = f + g + matMul f g :=
  rfl

/-- Iterated matrix power: `matPow f n = matMul f (matMul f (… f))` is the `(n+1)`-fold matrix
product of `f` with itself (so `matPow f 0 = f`). -/
noncomputable def matPow : UTBase → ℕ → UTBase
  | f, 0 => f
  | f, n + 1 => matMul f (matPow f n)

/-- The unipotent inverse of `I + f`, given by the finite Neumann series
`(I + f)⁻¹ = I + (-f + f² - f³ + …)`. The sum is finite because `f` is nilpotent under `matMul`. -/
noncomputable def utInv (f : UTBase) : UTBase :=
  (Finset.range f.support.card).sum fun k ↦ ((-1 : ℤ) ^ (k + 1)) • matPow f k

/-- The strict upper-triangularity condition for the product order: every entry `(p, q)` in the
support satisfies `p.1 < q.1` and `p.2 < q.2`. -/
def isValidProd (f : UTBase) : Prop :=
  ∀ pq ∈ f.support, pq.1.1 < pq.2.1 ∧ pq.1.2 < pq.2.2

/-- The strict anti-triangularity condition: every entry `(p, q)` in the support satisfies
`p.1 < q.1` and `q.2 < p.2` (increasing in the first coordinate, decreasing in the second). -/
def isValidAnti (f : UTBase) : Prop :=
  ∀ pq ∈ f.support, pq.1.1 < pq.2.1 ∧ pq.2.2 < pq.1.2

/-- The group `UT₁` of strictly upper-triangular unipotent matrices: `UTBase` elements satisfying
`isValidProd`. -/
def UT₁ :=
  Subtype isValidProd

/-- The group `UT₂` of strictly anti-triangular unipotent matrices: `UTBase` elements satisfying
`isValidAnti`. -/
def UT₂ :=
  Subtype isValidAnti

/-- The identity has the product order validity condition. -/
lemma zero_isValidProd : isValidProd 0 := by simp [isValidProd]

/-- The product order validity condition is preserved by scalar multiplication. -/
lemma smul_isValidProd {f} (hf : isValidProd f) (z : ℤ) : isValidProd (z • f) :=
  fun _ hpq ↦ hf _ (Finsupp.support_smul hpq)

/-- The product order validity condition is preserved by addition. -/
lemma add_isValidProd {f g} (hf : isValidProd f) (hg : isValidProd g) : isValidProd (f + g) := by
  intro pq hpq
  rcases Finset.mem_union.mp (Finsupp.support_add hpq) with hpq | hpq
  · exact hf _ hpq
  · exact hg _ hpq

lemma mem_support_matMul {f g} (pq : (ℤ × ℤ) × ℤ × ℤ) (h : pq ∈ (matMul f g).support) :
    ∃ k : ℤ × ℤ, (pq.1, k) ∈ f.support ∧ (k, pq.2) ∈ g.support := by
  simp only [Finsupp.mem_support_iff, matMul, Finsupp.sum, Finset.sum_apply'] at h
  obtain ⟨k, k_mem_f_supp, h_sum₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨l, l_mem_g_supp, h_sum₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_sum₁
  rw [DFunLike.ite_apply, Finsupp.coe_zero, Pi.zero_apply, ite_ne_right_iff,
    Finsupp.single_apply_ne_zero] at h_sum₂
  refine ⟨k.2, ?_, ?_⟩
  · simpa only [h_sum₂.2.1] using k_mem_f_supp
  · simpa only [h_sum₂.1, h_sum₂.2.1] using l_mem_g_supp

/-- The product order validity condition is preserved by `matMul`. -/
lemma matMul_isValidProd {f g} (hf : isValidProd f) (hg : isValidProd g) :
    isValidProd (matMul f g) := by
  intro pq hpq
  obtain ⟨k, hfk, hgk⟩ := mem_support_matMul pq hpq
  exact ⟨lt_trans (hf _ hfk).1 (hg _ hgk).1, lt_trans (hf _ hfk).2 (hg _ hgk).2⟩

/-- The product order validity condition is preserved by `utMul`. -/
lemma utMul_isValidProd {f g} (hf : isValidProd f) (hg : isValidProd g) : isValidProd (utMul f g) :=
  add_isValidProd (add_isValidProd hf hg) (matMul_isValidProd hf hg)

/-- The product order validity condition is preserved by `matPow`. -/
lemma matPow_isValidProd {f} (hf : isValidProd f) (n : ℕ) : isValidProd (matPow f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact matMul_isValidProd hf ih

/-- The product order validity condition is preserved by `utInv`. -/
lemma utInv_isValidProd {f} (hf : isValidProd f) : isValidProd (utInv f) := by
  unfold utInv
  induction f.support.card with
  | zero => exact zero_isValidProd
  | succ n ih =>
    rw [Finset.sum_range_succ]
    apply add_isValidProd ih
    apply smul_isValidProd
    exact matPow_isValidProd hf n

/-- The identity has the anti-triangularity validity condition. -/
lemma zero_isValidAnti : isValidAnti 0 := by simp [isValidAnti]

/-- The anti-triangularity validity condition is preserved by scalar multiplication. -/
lemma smul_isValidAnti {f} (hf : isValidAnti f) (z : ℤ) : isValidAnti (z • f) :=
  fun _ hpq ↦ hf _ (Finsupp.support_smul hpq)

/-- The anti-triangularity validity condition is preserved by addition. -/
lemma add_isValidAnti {f g} (hf : isValidAnti f) (hg : isValidAnti g) : isValidAnti (f + g) := by
  intro pq hpq
  rcases Finset.mem_union.mp (Finsupp.support_add hpq) with hpq | hpq
  · exact hf _ hpq
  · exact hg _ hpq

/-- The anti-triangularity validity condition is preserved by `matMul`. -/
lemma matMul_isValidAnti {f g} (hf : isValidAnti f) (hg : isValidAnti g) :
    isValidAnti (matMul f g) := by
  intro pq hpq
  obtain ⟨k, hfk, hgk⟩ := mem_support_matMul pq hpq
  exact ⟨lt_trans (hf _ hfk).1 (hg _ hgk).1, lt_trans (hg _ hgk).2 (hf _ hfk).2⟩

/-- The anti-triangularity validity condition is preserved by `utMul`. -/
lemma utMul_isValidAnti {f g} (hf : isValidAnti f) (hg : isValidAnti g) : isValidAnti (utMul f g) :=
  add_isValidAnti (add_isValidAnti hf hg) (matMul_isValidAnti hf hg)

/-- The anti-triangularity validity condition is preserved by `matPow`. -/
lemma matPow_isValidAnti {f} (hf : isValidAnti f) (n : ℕ) : isValidAnti (matPow f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact matMul_isValidAnti hf ih

/-- The anti-triangularity validity condition is preserved by `utInv`. -/
lemma utInv_isValidAnti {f} (hf : isValidAnti f) : isValidAnti (utInv f) := by
  unfold utInv
  induction f.support.card with
  | zero => exact zero_isValidAnti
  | succ n ih =>
    rw [Finset.sum_range_succ]
    apply add_isValidAnti ih
    apply smul_isValidAnti
    exact matPow_isValidAnti hf n

/-- Matrix multiplication is left-distributive over addition. -/
lemma matMul_add_left (f g h : UTBase) : matMul (f + g) h = matMul f h + matMul g h := by
  convert Finsupp.sum_add_index' _ _
  · simp
  · intros
    simp_rw [Finsupp.sum, add_mul, Finsupp.single_mul, Finsupp.single_add, ← Finset.sum_add_distrib]
    congr
    aesop

/-- Matrix multiplication is right-distributive over addition. -/
lemma matMul_add_right (f g h : UTBase) : matMul f (g + h) = matMul f g + matMul f h := by
  unfold matMul
  rw [← Finsupp.sum_add]
  congr
  ext
  rw [Finsupp.sum_add_index']
  · simp
  · simp [ite_add_ite, mul_add]

/-- Matrix multiplication is associative. -/
lemma matMul_assoc (f g h : UTBase) : matMul (matMul f g) h = matMul f (matMul g h) := by
  unfold matMul
  rw [Finsupp.sum_sum_index]
  · apply Finset.sum_congr rfl
    intro i hfi
    simp only [Finsupp.single_mul]
    rw [Finsupp.sum_sum_index, Finsupp.sum_sum_index]
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      simp only [Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply]
      split_ifs <;> simp_all [Finsupp.single_apply, Finset.sum_ite]
      · rw [Finset.sum_eq_single (i.1, j.2)] <;> simp_all [Finsupp.single_apply]
        refine Finset.sum_bij (fun x hx ↦ (j.1, x.2)) ?_ ?_ ?_ ?_ <;>
          simp_all [Finsupp.single_apply, Finset.sum_ite]
        · intro a b c d h₁ h₂
          rw [Finset.sum_eq_single ((a, b), c, d)] <;> aesop
        · intro a b c d h₁ h₂
          contrapose! h₁
          simp_all only [ne_eq, true_and, Finset.sum_filter]
          refine Finset.sum_eq_zero fun x hx ↦ ?_
          specialize h₁ x.1.1 x.1.2
          aesop
        · intro a b c d h₁ h₂
          simp_all only [mul_assoc]
          rw [Finset.sum_eq_single ((a, b), c, d)] <;> aesop
      · rw [Finset.sum_eq_zero]
        aesop
    · aesop
    · intros
      split_ifs
      · simp [Finsupp.single_add, mul_add]
      · rfl
    · aesop
    · intros
      rw [← Finsupp.sum_add]
      congr
      ext
      split_ifs <;> simp [*, Finsupp.single_apply]
      split_ifs <;> ring
  · aesop
  · intros
    rw [← Finsupp.sum_add]
    congr
    ext
    split_ifs <;> simp [*, add_mul]

/-- The unipotent group law `utMul` is associative. -/
lemma utMul_assoc' (f g h : UTBase) : utMul (utMul f g) h = utMul f (utMul g h) := by
  simp only [utMul, matMul_add_left, matMul_add_right, matMul_assoc]
  abel

/-- `0` (the identity matrix `I`) is a right identity for `utMul`. -/
lemma utMul_zero' (f : UTBase) : utMul f 0 = f := by simp [utMul, matMul]

/-- `0` (the identity matrix `I`) is a left identity for `utMul`. -/
lemma zero_utMul' (f : UTBase) : utMul 0 f = f := by simp [utMul, matMul, Finsupp.sum]

/--
Matrix multiplication is homogeneous in its left argument: `matMul (c • f) g = c • matMul f g`. -/
lemma matMul_smul_left (c : ℤ) (f g : UTBase) : matMul (c • f) g = c • matMul f g := by
  ext
  unfold matMul
  simp only [Finsupp.single_mul, Finsupp.single_zero, zero_mul, ite_self, Finsupp.sum_fun_zero,
    implies_true, Finsupp.sum_smul_index, Finsupp.sum_apply, Finsupp.coe_smul, Finsupp.coe_sum,
    Pi.smul_apply, Int.zsmul_eq_mul]
  simp only [Finsupp.sum, Finset.sum_apply, Finset.mul_sum _ _ _]
  congr! 2
  split_ifs <;> simp [*, Finsupp.single_apply, mul_assoc]
  aesop

/-- Multiplying `matPow f n` by `f` on the right gives `matPow f (n + 1)`; that is, `matMul` and
`matPow` commute the way ordinary powers do. -/
lemma matMul_matPow (f : UTBase) (n : ℕ) : matMul (matPow f n) f = matPow f (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [matPow] at ih ⊢
    rw [matMul_assoc, ih]

lemma mem_support_matPow (f : UTBase) :
    ∀ (n : ℕ) (p : (ℤ × ℤ) × (ℤ × ℤ)) (_ : p ∈ (matPow f n).support),
      ∃ q : ℕ → (ℤ × ℤ), q 0 = p.1 ∧ q (n + 1) = p.2 ∧ ∀ i < n + 1, (q i, q (i + 1)) ∈ f.support := by
  intro n
  induction n with
  | zero =>
    refine fun p hp ↦ ⟨fun i ↦ if i = 0 then p.1 else p.2, rfl, rfl, ?_⟩
    simp_all [matPow]
  | succ n ih =>
    intro p hp
    obtain ⟨k, hk₁, hk₂⟩ := mem_support_matMul _ hp
    obtain ⟨q', hq'₁, hq'₂, hq'₃⟩ := ih _ hk₂
    refine ⟨fun
        | 0 => p.1
        | i + 1 => q' i, ?_⟩
    simp only [Order.lt_add_one_iff, true_and, hq'₂]
    intro i i_le
    rcases i with _ | i
    · rw [hq'₁]
      exact hk₁
    · exact hq'₃ i (Nat.lt_of_succ_le i_le)

/-- Nilpotency for product-order valid elements: a chain of matched entries cannot be longer than
the support, so `matPow f (#support) = 0`. -/
lemma matPow_nilpotent_prod (f : UTBase) (hf : isValidProd f) : matPow f f.support.card = 0 := by
  have := mem_support_matPow f
  contrapose! this
  obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp this
  refine ⟨f.support.card, p, ?_, ?_⟩ <;> simp_all [Finsupp.mem_support_iff]
  intro q hq₁ hq₂
  by_contra! h
  have : (Finset.image (fun i ↦ (q i, q (i + 1))) (Finset.range (f.support.card + 1))).card ≤
      f.support.card := by
    apply Finset.card_le_card
    rw [Finset.image_subset_iff]
    intro i hi
    rw [Finsupp.mem_support_iff]
    apply h
    simpa using hi
  simp_all only [ne_eq]
  rw [Finset.card_image_of_injOn] at this <;> norm_num at *
  intro i hi j hj hij
  have := hf (q i, q (i + 1))
  have := hf (q j, q (j + 1))
  simp_all only [Set.mem_Iio, Order.lt_add_one_iff, Prod.mk.injEq, Finsupp.mem_support_iff, ne_eq,
    not_false_eq_true, and_self, imp_self, forall_const]
  have h_chain : ∀ i ≤ f.support.card, (q i).1 < (q (i + 1)).1 ∧ (q i).2 < (q (i + 1)).2 :=
    fun i hi ↦ hf (q i, q (i + 1)) (Finsupp.mem_support_iff.mpr (h i hi))
  have h_chain :
      ∀ i j : ℕ, i ≤ f.support.card → j ≤ f.support.card → i < j → (q i).1 < (q j).1 ∧
        (q i).2 < (q j).2 := by
    intro i j hi hj hij
    induction hij with
    | refl => exact h_chain i hi
    | step i_le ih =>
      constructor
      · apply lt_trans (ih (by linarith)).1
        refine (h_chain _ ?_).1
        linarith
      · apply lt_trans (ih (by linarith)).2
        refine (h_chain _ ?_).2
        linarith
  grind

/-- Nilpotency for anti-triangular valid elements: as in the product-order case, the strictly
increasing first coordinate forces `matPow f (#support) = 0`. -/
lemma matPow_nilpotent_anti (f : UTBase) (hf : isValidAnti f) : matPow f f.support.card = 0 := by
  have := mem_support_matPow f
  contrapose! this
  obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp this
  refine ⟨f.support.card, p, ?_, ?_⟩ <;> simp_all [Finsupp.mem_support_iff]
  intro q hq₁ hq₂
  by_contra! h
  have : (Finset.image (fun i ↦ (q i, q (i + 1))) (Finset.range (f.support.card + 1))).card ≤
      f.support.card := by
    apply Finset.card_le_card
    rw [Finset.image_subset_iff]
    intro i hi
    rw [Finsupp.mem_support_iff]
    apply h
    simpa using hi
  simp_all only [ne_eq]
  rw [Finset.card_image_of_injOn] at this <;> norm_num at *
  intro i hi j hj hij
  have := hf (q i, q (i + 1))
  have := hf (q j, q (j + 1))
  simp_all only [Set.mem_Iio, Order.lt_add_one_iff, Prod.mk.injEq, Finsupp.mem_support_iff, ne_eq,
    not_false_eq_true, and_self, imp_self, forall_const]
  have h_chain : ∀ i ≤ f.support.card, (q i).1 < (q (i + 1)).1 ∧ (q i).2 > (q (i + 1)).2 :=
    fun i hi ↦ hf (q i, q (i + 1)) (Finsupp.mem_support_iff.mpr (h i hi))
  have h_chain :
    ∀ i j : ℕ,
      i ≤ f.support.card → j ≤ f.support.card → i < j → (q i).1 < (q j).1 ∧ (q i).2 > (q j).2 := by
    intro i j hi hj hij
    induction hij with
    | refl => exact h_chain i hi
    | step i_le ih =>
      constructor
      · apply lt_trans (ih (by linarith)).1
        refine (h_chain _ ?_).1
        linarith
      · apply lt_trans (h_chain _ (by linarith)).2
        refine (ih ?_).2
        linarith
  grind

/-- `utInv f` is a left inverse of `f` under `utMul` for product-order valid elements. -/
lemma utInv_utMul_prod (f : UTBase) (hf : isValidProd f) : utMul (utInv f) f = 0 := by
  unfold utMul utInv
  have h_matMul :
    matMul (∑ k ∈ Finset.range f.support.card, (-1 : ℤ) ^ (k + 1) • matPow f k) f =
      ∑ k ∈ Finset.range f.support.card, (-1 : ℤ) ^ (k + 1) • matPow f (k + 1) := by
    induction' (Finset.range f.support.card) using Finset.induction <;>
      simp_all [pow_succ', matMul_add_left]
    · simp [matMul]
    · convert matMul_smul_left (-((-1 : ℤ) ^ ‹_›)) (matPow f ‹_›) f using 1
      norm_num
      rw [matMul_matPow]
      norm_num [pow_succ', mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib]
  have := Finset.sum_range_sub (fun x ↦ (-1 : ℤ) ^ x • matPow f x) (f.support.card)
  simp_all only [Int.reduceNeg, pow_succ', neg_mul, one_mul, neg_smul, Finset.sum_neg_distrib,
    Finset.sum_sub_distrib, pow_zero, one_smul]
  simp_all only [Int.reduceNeg, sub_eq_iff_eq_add', add_comm, add_left_comm, add_assoc,
    add_neg_cancel, add_zero]
  rw [matPow_nilpotent_prod f hf]
  simp [matPow]

/-- `utInv f` is a left inverse of `f` under `utMul` for anti-triangular valid elements. -/
lemma utInv_utMul_anti (f : UTBase) (hf : isValidAnti f) : utMul (utInv f) f = 0 := by
  unfold utMul utInv
  have : ∑ k ∈ Finset.range f.support.card, (-1 : ℤ) ^ (k + 1) • matPow f k + f +
      ∑ k ∈ Finset.range f.support.card, (-1 : ℤ) ^ (k + 1) • matPow f (k + 1) = 0 := by
    have := Finset.sum_range_sub (fun x ↦ (-1 : ℤ) ^ x • matPow f x) f.support.card
    simp_all only [Int.reduceNeg, pow_succ', neg_mul, one_mul, neg_smul, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, pow_zero, one_smul]
    simp_all only [Int.reduceNeg, sub_eq_add_neg, add_comm, add_assoc, matPow_nilpotent_anti f hf]
    norm_num [matPow]
  convert this using 2
  induction' (Finset.range f.support.card) using Finset.induction with a <;>
    simp_all [matMul_add_left, matMul_smul_left]
  · simp [matMul]
  · exact matMul_matPow f a

/-- Two elements of `UT₁` are equal iff their underlying `UTBase` values are equal. -/
@[ext]
lemma UT₁.ext {a b : UT₁} (h : a.val = b.val) : a = b :=
  Subtype.ext h

/-- Two elements of `UT₂` are equal iff their underlying `UTBase` values are equal. -/
@[ext]
lemma UT₂.ext {a b : UT₂} (h : a.val = b.val) : a = b :=
  Subtype.ext h

/-- The group structure on `UT₁`: multiplication is `utMul`, the identity is `0` (the matrix `I`),
and inversion is `utInv`, all restricted to product-order valid elements. -/
noncomputable instance : Group UT₁ where
  mul f g := ⟨utMul f.val g.val, utMul_isValidProd f.prop g.prop⟩
  one := ⟨0, fun _ h ↦ by simp at h⟩
  inv f := ⟨utInv f.val, utInv_isValidProd f.prop⟩
  mul_assoc f g h := UT₁.ext (utMul_assoc' f.val g.val h.val)
  one_mul f := UT₁.ext (zero_utMul' f.val)
  mul_one f := UT₁.ext (utMul_zero' f.val)
  inv_mul_cancel f := UT₁.ext (utInv_utMul_prod f.val f.prop)

/-- The group structure on `UT₂`: multiplication is `utMul`, the identity is `0`, and inversion is
`utInv`, all restricted to anti-triangular valid elements. -/
noncomputable instance : Group UT₂ where
  mul f g := ⟨utMul f.val g.val, utMul_isValidAnti f.prop g.prop⟩
  one := ⟨0, fun _ h ↦ by simp at h⟩
  inv f := ⟨utInv f.val, utInv_isValidAnti f.prop⟩
  mul_assoc f g h := UT₂.ext (utMul_assoc' f.val g.val h.val)
  one_mul f := UT₂.ext (zero_utMul' f.val)
  mul_one f := UT₂.ext (utMul_zero' f.val)
  inv_mul_cancel f := UT₂.ext (utInv_utMul_anti f.val f.prop)

/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib

set_option maxHeartbeats 6400000

/-!
# Kourovka Notebook Problem 3.46

B. I. Plotkin asked whether there exists a group having more than one, but only
finitely many, maximal locally soluble normal subgroups. This is Problem 3.46 in
the Kourovka Notebook (https://arxiv.org/pdf/1401.0300). The answer is **yes**,
and this file constructs an explicit witness with **exactly two** such subgroups.

A group is *locally solvable* if every finitely generated subgroup is solvable.
The witness `MyG = MyK ⋊ ℤ²` is a semidirect product in which `ℤ²` acts on a
group `MyK = UT₁ × UT₂` of finitely-supported strictly (anti-)upper-triangular
integer "matrices" indexed by pairs of lattice points; the two coordinates of
`ℤ²` shift the lattice indices in the first, respectively second, direction. The
two distinguished subgroups are `M₁ = {g | g.b = 0}` and `M₂ = {g | g.a = 0}`.

Each `Mᵢ` is locally solvable: a finitely generated subgroup only involves
finitely many shifts, so its `MyK`-part lives in a finite unitriangular (hence
nilpotent, hence solvable) matrix group, extended by an abelian copy of `ℤ`.
Conversely, any normal locally solvable subgroup `N` lies in `M₁` or `M₂`:
otherwise `N` contains an element with `a > 0` and `b ≠ 0`, and conjugating a
single-entry generator by it *doubles* an index gap at each step of the derived
series, producing unbounded derived length and contradicting local solvability.
Together these facts show `M₁` and `M₂` are the only maximal locally solvable
normal subgroups.

## Main results

* `IsLocallySolvable`, `IsMaxLocSolvNormal` : the basic definitions.
* `MyG` : the witness group `MyK ⋊ ℤ²`, with subgroups `M₁` and `M₂`.
* `M₁_locally_solvable`, `M₂_locally_solvable` : both subgroups are locally solvable.
* `loc_solv_normal_le` : every normal locally solvable subgroup is `≤ M₁` or `≤ M₂`.
* `main_theorem` : there exists a group with exactly two maximal locally solvable
  normal subgroups.

## Structure

1. **The unipotent matrix calculus** (`matMul`, `utMul`, `matPow`, `utInv`):
   strictly (anti-)upper-triangular finitely-supported matrices and the group
   law `I + f` on them, with nilpotency and inverse formulas (`UT₁`, `UT₂`).
2. **The shift action and the group `MyG`**: index shifts `shiftUTBase₁/₂`, the
   `ℤ²`-action `phiAction`, and the semidirect product `MyG` with its subgroups
   `M₁`, `M₂`.
3. **Local solvability of `M₁`, `M₂`**: coordinate-boundedness and gap filtrations
   show finitely generated subgroups embed into finite solvable groups.
4. **The non-solvability engine**: single-entry generators (`singleElt`,
   `singleEltAnti`) whose index gap doubles under iterated conjugation, giving
   unbounded derived length when `a > 0` and `b ≠ 0`.
5. **The classification** (`loc_solv_normal_le`) and the **main theorem**.
-/

/-- A group is locally solvable if every finitely generated subgroup is solvable. -/
def IsLocallySolvable (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → IsSolvable H

/-- A maximal locally solvable normal subgroup of `G` is a normal subgroup `M` that
    is locally solvable and maximal among locally solvable normal subgroups. -/
def IsMaxLocSolvNormal (G : Type*) [Group G] (M : Subgroup G) : Prop :=
  M.Normal ∧ IsLocallySolvable M ∧ ∀ N : Subgroup G, N.Normal → IsLocallySolvable N → M ≤ N → N = M

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

/-- The product order validity condition is preserved by `utMul`. -/
lemma utMul_isValidProd {f g} (hf : isValidProd f) (hg : isValidProd g) : isValidProd (utMul f g) := by
  intros pq hpq
  simp [utMul] at hpq ⊢
  by_cases h : pq ∈ f.support <;> by_cases h' : pq ∈ g.support <;>
    simp_all +decide [Finsupp.mem_support_iff, matMul]
  · exact hf pq (Finsupp.mem_support_iff.mpr h)
  · exact hf pq (by aesop)
  · exact hg pq (by aesop)
  · contrapose! hpq
    simp_all +decide [Finsupp.sum]
    refine' Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ _
    split_ifs <;> simp_all +decide [Finsupp.single_apply]
    intro H
    have := hf x
    have := hg y
    simp_all +decide
    grind

/-- The product order validity condition is preserved by `utInv`. -/
lemma utInv_isValidProd {f} (hf : isValidProd f) : isValidProd (utInv f) := by
  have h_support : ∀ k, ∀ pq ∈ (matPow f k).support, pq.1.1 < pq.2.1 ∧ pq.1.2 < pq.2.2 := by
    intro k pq hpq
    induction' k with k ih generalizing pq
    · exact hf pq hpq
    · contrapose! hpq
      simp_all +decide
      have h_matMul :
        matMul f (matPow f k) pq =
          ∑ p ∈ f.support,
            ∑ q ∈ (matPow f k).support,
              if p.2 = q.1 then f p * (matPow f k) q * (if p.1 = pq.1 ∧ q.2 = pq.2 then 1 else 0)
              else 0 := by
        unfold matMul
        simp +decide [Finsupp.sum]
        refine' Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ _
        aesop
      convert h_matMul using 1
      refine' Eq.symm (Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun q hq ↦ _)
      grind +locals
  intro pq hpq
  contrapose! hpq
  simp_all +decide [utInv]
  exact Finset.sum_eq_zero fun i hi ↦
      mul_eq_zero_of_right _ <|
        not_not.1 fun hi' ↦ by
          have := h_support i _ _ _ _ hi'
          exact not_lt_of_ge (hpq this.1) this.2

/-- The anti-triangularity validity condition is preserved by `utMul`. -/
lemma utMul_isValidAnti {f g} (hf : isValidAnti f) (hg : isValidAnti g) : isValidAnti (utMul f g) := by
  intro pq hpq
  by_cases hfg : pq ∈ (matMul f g).support
  · contrapose! hfg
    simp_all +decide [matMul]
    refine' Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ _
    by_cases h : x.2 = y.1 <;> simp_all +decide [Finsupp.single_apply]
    grind +locals
  · by_cases hfg : pq ∈ f.support ∨ pq ∈ g.support <;> simp_all +decide [utMul]
    cases hfg <;> [exact hf pq (by aesop); exact hg pq (by aesop)]

/-- The anti-triangularity validity condition is preserved by `utInv`. -/
lemma utInv_isValidAnti {f} (hf : isValidAnti f) : isValidAnti (utInv f) := by
  have h_matPow_valid : ∀ k, isValidAnti (matPow f k) := by
    intro k
    induction' k with k ih
    · exact hf
    · have h_matMul_valid :
        ∀ f g : UTBase, isValidAnti f → isValidAnti g → isValidAnti (matMul f g) := by
        intros f g hf hg
        intro pq hpq
        contrapose! hpq
        unfold matMul
        simp +decide [Finsupp.sum]
        refine' Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ _
        split_ifs <;> simp_all +decide [Finsupp.single_apply]
        grind +locals
      exact h_matMul_valid _ _ hf ih
  have h_utInv_sum :
    ∀ pq ∈ (utInv f).support,
      pq ∈
        Finset.biUnion (Finset.range (Finset.card (Finsupp.support f)))
          (fun k ↦ (Finsupp.support (matPow f k))) := by
    intro pq hpq
    contrapose! hpq
    simp_all +decide [utInv]
    exact Finset.sum_eq_zero fun x hx ↦ by
        rw [hpq x (Finset.mem_range.mp hx)]
        ring
  grind +locals

/-- Matrix multiplication is left-distributive over addition. -/
lemma matMul_add_left (f g h : UTBase) : matMul (f + g) h = matMul f h + matMul g h := by
  convert Finsupp.sum_add_index' _ _
  · aesop
  · simp +decide [add_mul, Finsupp.sum]
    exact fun a b c d e f ↦ by
      rw [← Finset.sum_add_distrib]
      congr
      ext
      aesop

/-- Matrix multiplication is right-distributive over addition. -/
lemma matMul_add_right (f g h : UTBase) : matMul f (g + h) = matMul f g + matMul f h := by
  unfold matMul
  rw [← Finsupp.sum_add]
  congr! 1
  ext
  rw [Finsupp.sum_add_index'] <;> aesop

/-- Matrix multiplication is associative. -/
lemma matMul_assoc (f g h : UTBase) : matMul (matMul f g) h = matMul f (matMul g h) := by
  unfold matMul
  rw [Finsupp.sum_sum_index]
  · refine' Finset.sum_congr rfl fun i hi ↦ _
    simp +decide
    rw [Finsupp.sum_sum_index, Finsupp.sum_sum_index]
    · refine' Finset.sum_congr rfl fun j hj ↦ _
      simp +decide [Finsupp.sum]
      split_ifs <;> simp_all +decide [Finsupp.single_apply, Finset.sum_ite]
      · rw [Finset.sum_eq_single (i.1, j.2)] <;> simp_all +decide [Finsupp.single_apply]
        refine' Finset.sum_bij (fun x hx ↦ (j.1, x.2)) _ _ _ _ <;>
          simp_all +decide [Finsupp.single_apply, Finset.sum_ite]
        · intro a b c d h₁ h₂
          rw [Finset.sum_eq_single ((a, b), c, d)] <;> aesop
        · intro a b c d h₁ h₂
          contrapose! h₁
          simp_all +decide [Finset.sum_filter]
          exact Finset.sum_eq_zero fun x hx ↦ by
              specialize h₁ x.1.1 x.1.2
              aesop
        · intro a b c d h₁ h₂
          simp_all +decide [mul_assoc]
          rw [Finset.sum_eq_single ((a, b), c, d)] <;> aesop
      · rw [Finset.sum_eq_zero]
        aesop
    · aesop
    · aesop
    · aesop
    · intro a b₁ b₂
      rw [← Finsupp.sum_add]
      congr
      ext
      split_ifs <;> simp +decide [*, Finsupp.single_apply]
      split_ifs <;> ring
  · aesop
  · intro a b₁ b₂
    rw [← Finsupp.sum_add]
    congr
    ext
    split_ifs <;> simp +decide [*, add_mul]

/-- The unipotent group law `utMul` is associative. -/
lemma utMul_assoc' (f g h : UTBase) : utMul (utMul f g) h = utMul f (utMul g h) := by
  simp only [utMul]
  rw [matMul_add_left, matMul_add_left, matMul_add_right, matMul_add_right]
  rw [matMul_assoc]
  abel

/-- `0` (the identity matrix `I`) is a right identity for `utMul`. -/
lemma utMul_zero' (f : UTBase) : utMul f 0 = f := by simp [utMul, matMul]

/-- `0` (the identity matrix `I`) is a left identity for `utMul`. -/
lemma zero_utMul' (f : UTBase) : utMul 0 f = f := by
  unfold utMul matMul
  simp +decide [Finsupp.sum]

/-- Matrix multiplication is homogeneous in its left argument: `matMul (c • f) g = c • matMul f g`. -/
lemma matMul_smul_left (c : ℤ) (f g : UTBase) : matMul (c • f) g = c • matMul f g := by
  ext
  unfold matMul
  simp +decide [Finsupp.sum_smul_index]
  simp +decide [Finsupp.sum, Finset.mul_sum _ _ _]
  congr! 2
  split_ifs <;> simp +decide [*, Finsupp.single_apply, mul_assoc]
  grind

/-- Multiplying `matPow f n` by `f` on the right gives `matPow f (n + 1)`; that is, `matMul` and
`matPow` commute the way ordinary powers do. -/
lemma matMul_matPow (f : UTBase) (n : ℕ) : matMul (matPow f n) f = matPow f (n + 1) := by
  induction n <;> simp_all +decide [matMul_assoc, matPow]

/-- Nilpotency for product-order valid elements: a chain of matched entries cannot be longer than
the support, so `matPow f (#support) = 0`. -/
lemma matPow_nilpotent_prod (f : UTBase) (hf : isValidProd f) : matPow f f.support.card = 0 := by
  have h_matPow_support :
    ∀ n : ℕ,
      ∀ p : (ℤ × ℤ) × (ℤ × ℤ),
        p ∈ (matPow f n).support →
          ∃ q : ℕ → (ℤ × ℤ),
            q 0 = p.1 ∧ q (n + 1) = p.2 ∧ ∀ i < n + 1, (q i, q (i + 1)) ∈ f.support := by
    intro n
    induction' n with n ih
    · exact fun p hp ↦ ⟨fun i ↦ if i = 0 then p.1 else p.2, rfl, rfl, by aesop⟩
    · intro p hp
      obtain ⟨pq, hpq⟩ :
        ∃ pq ∈ f.support, ∃ q ∈ (matPow f n).support, p = (pq.1, q.2) ∧ pq.2 = q.1 := by
        contrapose! hp
        simp_all +decide [matPow, matMul]
        refine' Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ _
        specialize
          hp _ _ _ _ (Finsupp.mem_support_iff.mp hx) _ _ _ _ (Finsupp.mem_support_iff.mp hy)
        aesop
      obtain ⟨q, hq⟩ := hpq.2
      obtain ⟨r, hr⟩ := ih q hq.1
      use fun i ↦ if i = 0 then pq.1 else r (i - 1)
      simp_all +decide
      grind +splitIndPred
  contrapose! h_matPow_support
  obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp h_matPow_support
  refine' ⟨f.support.card, p, _, _⟩ <;> simp_all +decide [Finsupp.mem_support_iff]
  intro q hq₁ hq₂
  by_contra! h
  have :=
    Finset.card_le_card
      (show Finset.image (fun i ↦ (q i, q (i + 1))) (Finset.range (f.support.card + 1)) ⊆ f.support
        from ?_)
  simp_all +decide
  · rw [Finset.card_image_of_injOn] at this <;> norm_num at *
    intros i hi j hj hij
    have := hf (q i, q (i + 1))
    have := hf (q j, q (j + 1))
    simp_all +decide
    have h_chain : ∀ i ≤ f.support.card, (q i).1 < (q (i + 1)).1 ∧ (q i).2 < (q (i + 1)).2 := by
      intros i hi
      exact hf (q i, q (i + 1)) (Finsupp.mem_support_iff.mpr (h i hi))
    have h_chain :
      ∀ i j : ℕ,
        i ≤ f.support.card → j ≤ f.support.card → i < j → (q i).1 < (q j).1 ∧ (q i).2 < (q j).2 := by
      intros i j hi hj hij
      induction hij <;> simp_all +decide [Nat.succ_eq_add_one]
      grind
    grind
  · exact Finset.image_subset_iff.mpr fun i hi ↦ by aesop

/-- Nilpotency for anti-triangular valid elements: as in the product-order case, the strictly
increasing first coordinate forces `matPow f (#support) = 0`. -/
lemma matPow_nilpotent_anti (f : UTBase) (hf : isValidAnti f) : matPow f f.support.card = 0 := by
  revert f
  intro f hf
  have h_pow : ∀ n ≥ f.support.card, matPow f n = 0 := by
    intro n hn
    have h_chain :
      ∀ (r : List ((ℤ × ℤ) × (ℤ × ℤ))),
        r.length = n + 1 →
          (∀ i < r.length - 1, r[i]!.2 = r[i + 1]!.1) →
            (∀ i < r.length, r[i]! ∈ f.support) → False := by
      intros r hr_len hr_chain hr_support
      have h_chain : ∀ i < r.length - 1, r[i]!.1.1 < r[i + 1]!.1.1 := by
        intros i hi
        have h_chain : r[i]!.1.1 < r[i]!.2.1 :=
          hf _ (hr_support i (Nat.lt_of_lt_of_le hi (Nat.pred_le _))) |>.1
        aesop
      have h_chain :
        Finset.card (Finset.image (fun i ↦ r[i]!.1.1) (Finset.range (r.length))) ≤ f.support.card := by
        have h_chain :
          Finset.image (fun i ↦ r[i]!.1.1) (Finset.range (r.length)) ⊆
            Finset.image (fun p ↦ p.1.1) f.support :=
          Finset.image_subset_iff.mpr fun i hi ↦
            Finset.mem_image.mpr ⟨_, hr_support i (Finset.mem_range.mp hi), rfl⟩
        exact le_trans (Finset.card_le_card h_chain) (Finset.card_image_le)
      rw [Finset.card_image_of_injOn] at h_chain
      · grind
      · intros i hi j hj hij
        have h_chain : ∀ i j : ℕ, i < j → j < r.length → r[i]!.1.1 < r[j]!.1.1 := by
          intros i j hij hj_lt_len
          induction' hij with j hj ih
          · exact ‹∀ i < r.length - 1, r[i]!.1.1 < r[i + 1]!.1.1› i (Nat.lt_pred_iff.mpr hj_lt_len)
          · grind
        exact le_antisymm
            (le_of_not_gt fun hi' ↦ by
              linarith [h_chain _ _ hi'
                  (by linarith [Finset.mem_range.mp hi, Finset.mem_range.mp hj])])
            (le_of_not_gt fun hj' ↦ by
              linarith [h_chain _ _ hj'
                  (by linarith [Finset.mem_range.mp hi, Finset.mem_range.mp hj])])
    contrapose! h_chain
    obtain ⟨r, hr⟩ : ∃ r : ((ℤ × ℤ) × (ℤ × ℤ)), r ∈ (matPow f n).support :=
      Finset.nonempty_of_ne_empty (by aesop)
    have h_chain :
      ∀ (n : ℕ) (r : ((ℤ × ℤ) × (ℤ × ℤ))),
        r ∈ (matPow f n).support →
          ∃ (s : List ((ℤ × ℤ) × (ℤ × ℤ))),
            s.length = n + 1 ∧
              (∀ i < s.length - 1, s[i]!.2 = s[i + 1]!.1) ∧
                (∀ i < s.length, s[i]! ∈ f.support) ∧ s[0]!.1 = r.1 ∧ s[n]!.2 = r.2 := by
      intro n r hr
      induction' n with n ih generalizing r
      · exact ⟨[r], by aesop⟩
      · obtain ⟨p, hp, q, hq, hpq⟩ :
          ∃ p ∈ f.support, ∃ q ∈ (matPow f n).support, p.2 = q.1 ∧ r = (p.1, q.2) := by
          simp_all +decide [matPow, matMul]
          simp_all +decide [Finsupp.sum]
          obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
          obtain ⟨y, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx.2
          split_ifs at hy <;> simp_all +decide [Finsupp.single_apply]
          grind
        obtain ⟨s, hs₁, hs₂, hs₃, hs₄, hs₅⟩ := ih q hq
        use p :: s
        simp_all +decide [List.getElem?_cons]
        constructor
        all_goals grind
    exact Exists.elim (h_chain n r hr) fun s hs ↦ ⟨s, hs.1, hs.2.1, hs.2.2.1, trivial⟩
  exact h_pow _ le_rfl

/-- `utInv f` is a left inverse of `f` under `utMul` for product-order valid elements. -/
lemma utInv_utMul_prod (f : UTBase) (hf : isValidProd f) : utMul (utInv f) f = 0 := by
  unfold utMul utInv
  have h_matMul :
    matMul (∑ k ∈ Finset.range f.support.card, (-1 : ℤ) ^ (k + 1) • matPow f k) f =
      ∑ k ∈ Finset.range f.support.card, (-1 : ℤ) ^ (k + 1) • matPow f (k + 1) := by
    induction' (Finset.range f.support.card) using Finset.induction <;>
      simp_all +decide [pow_succ', matMul_add_left]
    · unfold matMul
      aesop
    · convert matMul_smul_left (-((-1 : ℤ) ^ ‹_›)) (matPow f ‹_›) f using 1
      norm_num [matMul_matPow]
      rw [matMul_matPow]
      norm_num [pow_succ', mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib]
  have := Finset.sum_range_sub (fun x ↦ (-1 : ℤ) ^ x • matPow f x) (Finset.card f.support)
  simp_all +decide [pow_succ']
  simp_all +decide [sub_eq_iff_eq_add', add_comm, add_left_comm, add_assoc]
  rw [matPow_nilpotent_prod f hf]
  simp +decide [matPow]

/-- `utInv f` is a left inverse of `f` under `utMul` for anti-triangular valid elements. -/
lemma utInv_utMul_anti (f : UTBase) (hf : isValidAnti f) : utMul (utInv f) f = 0 := by
  unfold utMul utInv
  have h_simp :
    ∑ k ∈ Finset.range f.support.card, (-1 : ℤ) ^ (k + 1) • matPow f k + f +
        ∑ k ∈ Finset.range f.support.card, (-1 : ℤ) ^ (k + 1) • matPow f (k + 1) =
      0 := by
    have := Finset.sum_range_sub (fun x ↦ (-1 : ℤ) ^ x • matPow f x) f.support.card
    simp_all +decide [pow_succ']
    simp_all +decide [sub_eq_add_neg, add_comm, add_assoc]
    rw [matPow_nilpotent_anti f hf]
    norm_num [matPow]
  convert h_simp using 2
  induction' (Finset.range f.support.card) using Finset.induction <;>
    simp_all +decide [matMul_add_left, matMul_smul_left]
  · unfold matMul
    aesop
  · expose_names
    exact matMul_matPow f a

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

/-- The matrix part of the construction: the direct product `MyK = UT₁ × UT₂` of the two unipotent
groups. The `ℤ²`-shift action will act diagonally on the two factors. -/
abbrev MyK :=
  UT₁ × UT₂

/-! ## Shifts -/

/-- Shift the **first** coordinate of every lattice index by `n`: relabels each entry
`((p₁, p₂), (q₁, q₂))` to `((p₁ + n, p₂), (q₁ + n, q₂))`. This is the matrix conjugation induced by
the first generator of `ℤ²`. -/
noncomputable def shiftUTBase₁ (n : ℤ) (f : UTBase) : UTBase :=
  f.equivMapDomain
    { toFun := fun pq ↦ ((pq.1.1 + n, pq.1.2), (pq.2.1 + n, pq.2.2))
      invFun := fun pq ↦ ((pq.1.1 - n, pq.1.2), (pq.2.1 - n, pq.2.2))
      left_inv := by
        intro ⟨⟨a, b⟩, ⟨c, d⟩⟩
        simp
      right_inv := by
        intro ⟨⟨a, b⟩, ⟨c, d⟩⟩
        simp }

/-- Shift the **second** coordinate of every lattice index by `n`: relabels each entry
`((p₁, p₂), (q₁, q₂))` to `((p₁, p₂ + n), (q₁, q₂ + n))`. This is the matrix conjugation induced by
the second generator of `ℤ²`. -/
noncomputable def shiftUTBase₂ (n : ℤ) (f : UTBase) : UTBase :=
  f.equivMapDomain
    { toFun := fun pq ↦ ((pq.1.1, pq.1.2 + n), (pq.2.1, pq.2.2 + n))
      invFun := fun pq ↦ ((pq.1.1, pq.1.2 - n), (pq.2.1, pq.2.2 - n))
      left_inv := by
        intro ⟨⟨a, b⟩, ⟨c, d⟩⟩
        simp
      right_inv := by
        intro ⟨⟨a, b⟩, ⟨c, d⟩⟩
        simp }

/-- A first-coordinate shift preserves product-order validity. -/
lemma shift₁_validProd (n : ℤ) (f : UTBase) (hf : isValidProd f) : isValidProd (shiftUTBase₁ n f) := by
  intro pq hpq
  rw [shiftUTBase₁] at hpq
  simp_all +decide [Finsupp.mem_support_iff]
  have := hf ((pq.1.1 - n, pq.1.2), pq.2.1 - n, pq.2.2)
  aesop

/-- A first-coordinate shift preserves anti-triangularity validity. -/
lemma shift₁_validAnti (n : ℤ) (f : UTBase) (hf : isValidAnti f) : isValidAnti (shiftUTBase₁ n f) := by
  unfold isValidAnti at *
  simp_all +decide [shiftUTBase₁]
  grind

/-- A second-coordinate shift preserves product-order validity. -/
lemma shift₂_validProd (n : ℤ) (f : UTBase) (hf : isValidProd f) : isValidProd (shiftUTBase₂ n f) := by
  intro pq hpq
  unfold shiftUTBase₂ at hpq
  specialize hf ((pq.1.1, pq.1.2 - n), (pq.2.1, pq.2.2 - n))
  aesop

/-- A second-coordinate shift preserves anti-triangularity validity. -/
lemma shift₂_validAnti (n : ℤ) (f : UTBase) (hf : isValidAnti f) : isValidAnti (shiftUTBase₂ n f) := by
  intro pq hpq
  rw [shiftUTBase₂] at hpq
  simp_all +decide [Finsupp.mem_support_iff]
  have := hf ((pq.1.1, pq.1.2 - n), pq.2.1, pq.2.2 - n)
  aesop

/-- The action of `(a, b) ∈ ℤ²` on `MyK`: shift the first coordinate of all indices by `a` and the
second by `b`, applied to both the `UT₁` and `UT₂` components. This is the homomorphism defining the
semidirect product. -/
noncomputable def phiAction (a b : ℤ) (k : MyK) : MyK :=
  (⟨shiftUTBase₁ a (shiftUTBase₂ b k.1.val), shift₁_validProd a _ (shift₂_validProd b _ k.1.prop)⟩,
    ⟨shiftUTBase₁ a (shiftUTBase₂ b k.2.val), shift₁_validAnti a _ (shift₂_validAnti b _ k.2.prop)⟩)

/-- A first-coordinate shift of the zero matrix is zero. -/
lemma shiftUTBase₁_zero (n : ℤ) : shiftUTBase₁ n 0 = 0 := by
  ext
  simp [shiftUTBase₁, Finsupp.equivMapDomain]

/-- A second-coordinate shift of the zero matrix is zero. -/
lemma shiftUTBase₂_zero (n : ℤ) : shiftUTBase₂ n 0 = 0 := by
  ext
  simp [shiftUTBase₂, Finsupp.equivMapDomain]

/-- The `ℤ²`-action fixes the identity of `MyK`. -/
lemma phiAction_one (a b : ℤ) : phiAction a b 1 = 1 := by
  show phiAction a b (1, 1) = (1, 1)
  unfold phiAction
  apply Prod.ext <;>
      ( apply Subtype.ext
        show shiftUTBase₁ a (shiftUTBase₂ b 0) = 0) <;>
    rw [shiftUTBase₂_zero, shiftUTBase₁_zero]

/-- For each `(a, b)`, the action `phiAction a b` is a group homomorphism of `MyK`. -/
lemma phiAction_mul (a b : ℤ) (k₁ k₂ : MyK) :
    phiAction a b (k₁ * k₂) = phiAction a b k₁ * phiAction a b k₂ := by
  apply Prod.ext
  · apply Subtype.ext
    have h_expand :
      matMul (shiftUTBase₁ a (shiftUTBase₂ b k₁.1.val)) (shiftUTBase₁ a (shiftUTBase₂ b k₂.1.val)) =
        shiftUTBase₁ a (shiftUTBase₂ b (matMul k₁.1.val k₂.1.val)) := by
      ext ⟨x, y⟩
      simp [matMul, shiftUTBase₁, shiftUTBase₂]
      refine' Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ _
      simp +decide [Prod.ext_iff]
      split_ifs <;> simp +decide [*, Finsupp.single_apply, Finsupp.mul_apply]
      grind
    convert congr_arg
        (fun x ↦
          shiftUTBase₁ a (shiftUTBase₂ b k₁.1.val) + shiftUTBase₁ a (shiftUTBase₂ b k₂.1.val) + x)
        h_expand using 1
    · exact h_expand.symm ▸ by
          unfold phiAction
          aesop
    · exact h_expand ▸ rfl
  · have h_shift_mul :
      ∀ (f g : UTBase),
        shiftUTBase₁ a (shiftUTBase₂ b (f + g + matMul f g)) =
          shiftUTBase₁ a (shiftUTBase₂ b f) + shiftUTBase₁ a (shiftUTBase₂ b g) +
            matMul (shiftUTBase₁ a (shiftUTBase₂ b f)) (shiftUTBase₁ a (shiftUTBase₂ b g)) := by
      intro f g
      ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
      simp +decide [shiftUTBase₁, shiftUTBase₂, matMul]
      ring_nf
      simp +decide [Finsupp.sum]
      refine' Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ _
      split_ifs <;> simp_all +decide [Finsupp.single_apply]
      ring_nf
      · grind
      · grind
    exact Subtype.ext (h_shift_mul _ _)

/-- The action respects addition in `ℤ²`: composing the actions of `(a₂, b₂)` and `(a₁, b₁)` equals
the action of their sum. -/
lemma phiAction_comp (a₁ b₁ a₂ b₂ : ℤ) (k : MyK) :
    phiAction a₁ b₁ (phiAction a₂ b₂ k) = phiAction (a₁ + a₂) (b₁ + b₂) k := by
  unfold phiAction
  simp +decide
  ring_nf
  constructor <;> congr 1 <;> ext ⟨⟨x, y⟩, ⟨z, w⟩⟩ <;> simp +decide [shiftUTBase₁, shiftUTBase₂] <;>
    ring_nf!

/-- The action of `(0, 0)` is the identity on `MyK`. -/
lemma phiAction_zero (k : MyK) : phiAction 0 0 k = k := by
  ext
  · simp [phiAction, shiftUTBase₁, shiftUTBase₂]
  · unfold phiAction shiftUTBase₁ shiftUTBase₂
    simp +decide [Finsupp.equivMapDomain]

/-! ## Group G -/

/-- The witness group, as a set: `MyG = MyK × ℤ × ℤ`, carrying the semidirect product
`MyK ⋊ ℤ²` structure. -/
def MyG :=
  MyK × ℤ × ℤ

/-- The `MyK`-component (the "matrix part") of an element of `MyG`. -/
def MyG.k (g : MyG) : MyK :=
  g.1
/-- The first `ℤ`-component (the first shift exponent) of an element of `MyG`. -/
def MyG.a (g : MyG) : ℤ :=
  g.2.1
/-- The second `ℤ`-component (the second shift exponent) of an element of `MyG`. -/
def MyG.b (g : MyG) : ℤ :=
  g.2.2

/-- The semidirect product multiplication on `MyG`: the matrix parts multiply after twisting the
second factor by the action of the first factor's `ℤ²`-component, and the `ℤ²`-components add. -/
noncomputable def myG_mul (g₁ g₂ : MyG) : MyG :=
  (g₁.k * phiAction g₁.a g₁.b g₂.k, g₁.a + g₂.a, g₁.b + g₂.b)

/-- The inverse in the semidirect product `MyG`. -/
noncomputable def myG_inv (g : MyG) : MyG :=
  (phiAction (-g.a) (-g.b) g.k⁻¹, -g.a, -g.b)

/-- The identity element `(1, 0, 0)` of `MyG`. -/
noncomputable def myG_one : MyG :=
  (1, 0, 0)

/-- The group structure on `MyG = MyK ⋊ ℤ²` given by `myG_mul`, `myG_one` and `myG_inv`. -/
noncomputable instance : Group MyG where
  mul := myG_mul
  one := myG_one
  inv := myG_inv
  mul_assoc := by
    intro a b c
    show myG_mul (myG_mul a b) c = myG_mul a (myG_mul b c)
    unfold myG_mul MyG.k MyG.a MyG.b
    apply Prod.ext
    · simp only
      rw [mul_assoc, phiAction_mul, phiAction_comp]
    · apply Prod.ext <;> simp only <;> ring
  one_mul := by
    intro a
    show myG_mul myG_one a = a
    unfold myG_mul myG_one MyG.k MyG.a MyG.b
    apply Prod.ext
    · simp [phiAction_zero]
    · apply Prod.ext <;> simp
  mul_one := by
    intro a
    show myG_mul a myG_one = a
    unfold myG_mul myG_one MyG.k MyG.a MyG.b
    apply Prod.ext
    · simp [phiAction_one]
    · apply Prod.ext <;> simp
  inv_mul_cancel := by
    intro a
    show myG_mul (myG_inv a) a = myG_one
    unfold myG_mul myG_inv myG_one MyG.k MyG.a MyG.b
    apply Prod.ext
    · rw [← phiAction_mul, inv_mul_cancel, phiAction_one]
    · apply Prod.ext <;> simp

/-! ## Subgroups -/

/-- The first shift exponent is additive: `(g₁ * g₂).a = g₁.a + g₂.a`. -/
@[simp]
lemma MyG.mul_a (g₁ g₂ : MyG) : (g₁ * g₂).a = g₁.a + g₂.a := by
  show (myG_mul g₁ g₂).2.1 = g₁.2.1 + g₂.2.1
  rfl
/-- The second shift exponent is additive: `(g₁ * g₂).b = g₁.b + g₂.b`. -/
@[simp]
lemma MyG.mul_b (g₁ g₂ : MyG) : (g₁ * g₂).b = g₁.b + g₂.b := by
  show (myG_mul g₁ g₂).2.2 = g₁.2.2 + g₂.2.2
  rfl
/-- Inversion negates the first shift exponent: `g⁻¹.a = -g.a`. -/
@[simp]
lemma MyG.inv_a (g : MyG) : g⁻¹.a = -g.a := by
  show (myG_inv g).2.1 = -g.2.1
  rfl
/-- Inversion negates the second shift exponent: `g⁻¹.b = -g.b`. -/
@[simp]
lemma MyG.inv_b (g : MyG) : g⁻¹.b = -g.b := by
  show (myG_inv g).2.2 = -g.2.2
  rfl

/-- The first distinguished subgroup `M₁ = {g | g.b = 0}` (the kernel of the second shift exponent),
one of the two maximal locally solvable normal subgroups. -/
noncomputable def M₁ : Subgroup MyG where
  carrier := {g : MyG | g.b = 0}
  mul_mem' ha hb := by
    simp [Set.mem_setOf_eq] at *
    omega
  one_mem' := rfl
  inv_mem' ha := by
    simp [Set.mem_setOf_eq] at *
    omega

/-- The second distinguished subgroup `M₂ = {g | g.a = 0}` (the kernel of the first shift exponent),
the other maximal locally solvable normal subgroup. -/
noncomputable def M₂ : Subgroup MyG where
  carrier := {g : MyG | g.a = 0}
  mul_mem' ha hb := by
    simp [Set.mem_setOf_eq] at *
    omega
  one_mem' := rfl
  inv_mem' ha := by
    simp [Set.mem_setOf_eq] at *
    omega

/-- `M₁` is a normal subgroup of `MyG`. -/
instance M₁_normal : M₁.Normal := by
  constructor
  intro n hn g
  have := hn
  simp_all +decide [M₁]

/-- `M₂` is a normal subgroup of `MyG`. -/
instance M₂_normal : M₂.Normal := by
  constructor
  simp +decide [M₂]

/-- The two distinguished subgroups are distinct. -/
lemma M₁_ne_M₂ : M₁ ≠ M₂ := by
  intro h
  have h1 : ((1 : MyK), (1 : ℤ), (0 : ℤ)) ∈ M₁ := rfl
  rw [h] at h1
  change (1 : ℤ) = 0 at h1
  exact one_ne_zero h1

/-!
{Pr}operties needed:
1. Second coordinates are preserved by group operations and σ-shifts
2. The gap filtration shows the derived series terminates
3. M₁ and M₂ are locally solvable
4. Every locally solvable normal subgroup is in M₁ or M₂
-/

/-! ## Second-coordinate preservation -/

/-- `f` "has second coordinates in `S`": every entry index `(p, q)` in the support of `f` has both
`p.2 ∈ S` and `q.2 ∈ S`. -/
def hasSecCoordsIn (f : UTBase) (S : Finset ℤ) : Prop :=
  ∀ pq ∈ f.support, pq.1.2 ∈ S ∧ pq.2.2 ∈ S

/-- The zero matrix has second coordinates in any set. -/
lemma hasSecCoordsIn_zero (S : Finset ℤ) : hasSecCoordsIn 0 S := by
  intro pq hpq
  simp at hpq

/-- Having second coordinates in `S` is closed under addition. -/
lemma hasSecCoordsIn_add {f g : UTBase} {S : Finset ℤ} (hf : hasSecCoordsIn f S)
    (hg : hasSecCoordsIn g S) : hasSecCoordsIn (f + g) S := by
  intro pq hpq
  by_cases hf' : pq ∈ f.support
  · exact hf pq hf'
  · have : pq ∈ g.support := by
      simp [Finsupp.mem_support_iff] at hpq hf' ⊢
      intro h
      simp [h, hf'] at hpq
    exact hg pq this

/-- Having second coordinates in `S` is closed under scalar multiplication. -/
lemma hasSecCoordsIn_smul {c : ℤ} {f : UTBase} {S : Finset ℤ} (hf : hasSecCoordsIn f S) :
    hasSecCoordsIn (c • f) S := by
  intro pq hpq
  exact hf pq (by
        simp [Finsupp.mem_support_iff] at hpq ⊢
        exact fun h ↦ by simp [h] at hpq)

/-- Having second coordinates in `S` is closed under matrix multiplication. -/
lemma hasSecCoordsIn_matMul {f g : UTBase} {S : Finset ℤ} (hf : hasSecCoordsIn f S)
    (hg : hasSecCoordsIn g S) : hasSecCoordsIn (matMul f g) S := by
  intros pq hpq
  contrapose! hpq
  simp_all +decide [matMul]
  simp +decide [Finsupp.sum]
  refine' Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ _
  split_ifs <;> simp_all +decide [Finsupp.single_apply]
  have := hf x
  have := hg y
  aesop

/-- Having second coordinates in `S` is closed under matrix powers. -/
lemma hasSecCoordsIn_matPow {f : UTBase} {S : Finset ℤ} (n : ℕ) (hf : hasSecCoordsIn f S) :
    hasSecCoordsIn (matPow f n) S := by
  induction n with
  | zero => exact hf
  | succ n ih => exact hasSecCoordsIn_matMul hf ih

/-- Having second coordinates in `S` is closed under the unipotent group law. -/
lemma hasSecCoordsIn_utMul {f g : UTBase} {S : Finset ℤ} (hf : hasSecCoordsIn f S)
    (hg : hasSecCoordsIn g S) : hasSecCoordsIn (utMul f g) S :=
  hasSecCoordsIn_add (hasSecCoordsIn_add hf hg) (hasSecCoordsIn_matMul hf hg)

/-- Having second coordinates in `S` is closed under the unipotent inverse. -/
lemma hasSecCoordsIn_utInv {f : UTBase} {S : Finset ℤ} (hf : hasSecCoordsIn f S) :
    hasSecCoordsIn (utInv f) S := by
  have h_sum :
    ∀ (s : Finset ℕ) (g : ℕ → UTBase),
      (∀ k ∈ s, hasSecCoordsIn (g k) S) → hasSecCoordsIn (∑ k ∈ s, g k) S := by
    intros s g hg
    induction s using Finset.induction <;> simp_all +decide [hasSecCoordsIn_add]
    exact hasSecCoordsIn_zero S
  exact h_sum _ _ fun k _ ↦ hasSecCoordsIn_smul (hasSecCoordsIn_matPow k hf)

/-- A first-coordinate shift leaves the second coordinates unchanged, so it preserves
`hasSecCoordsIn S`. -/
lemma hasSecCoordsIn_shift₁ {f : UTBase} {S : Finset ℤ} (n : ℤ) (hf : hasSecCoordsIn f S) :
    hasSecCoordsIn (shiftUTBase₁ n f) S := by
  intro pq hpq
  rw [shiftUTBase₁] at hpq
  simp_all +decide [Finsupp.equivMapDomain_apply]
  specialize hf ((pq.1.1 - n, pq.1.2), pq.2.1 - n, pq.2.2)
  aesop

/-! ## Gap filtration (using ℤ for arithmetic) -/

/-- `f` has "minimum second-coordinate gap `≥ d`": every entry `(p, q)` in the support satisfies
`p.2 + d ≤ q.2`. This filtration drives the derived-series doubling argument. -/
def hasMinGapZ (f : UTBase) (d : ℤ) : Prop :=
  ∀ pq ∈ f.support, pq.1.2 + d ≤ pq.2.2

/-- The zero matrix has gap `≥ d` for every `d`. -/
lemma hasMinGapZ_zero (d : ℤ) : hasMinGapZ 0 d := by
  intro pq hpq
  simp at hpq

/-- The gap bound is monotone: a gap `≥ d₂` implies a gap `≥ d₁` whenever `d₁ ≤ d₂`. -/
lemma hasMinGapZ_mono {f : UTBase} {d₁ d₂ : ℤ} (h : d₁ ≤ d₂) (hf : hasMinGapZ f d₂) :
    hasMinGapZ f d₁ := fun pq hpq ↦ le_trans (by omega) (hf pq hpq)

/-- A gap `≥ d` is preserved by addition. -/
lemma hasMinGapZ_add {f g : UTBase} {d : ℤ} (hf : hasMinGapZ f d) (hg : hasMinGapZ g d) :
    hasMinGapZ (f + g) d := by
  intro pq hpq
  by_cases h : pq ∈ f.support
  · exact hf pq h
  · exact hg pq (by
          simp [Finsupp.mem_support_iff] at hpq h ⊢
          intro hg'
          simp [hg', h] at hpq)

/-- Matrix multiplication adds gaps: if `f` has gap `≥ a` and `g` has gap `≥ b`, then `matMul f g`
has gap `≥ a + b`. -/
lemma matMul_hasMinGapZ {f g : UTBase} {a b : ℤ} (hf : hasMinGapZ f a) (hg : hasMinGapZ g b) :
    hasMinGapZ (matMul f g) (a + b) := by
  intro pq hq
  unfold matMul at hq
  contrapose! hq
  simp_all +decide [Finsupp.mem_support_iff]
  simp_all +decide [Finsupp.sum]
  refine Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ ?_
  split_ifs <;> simp_all +decide [Finsupp.single_apply]
  grind +locals

/-- A gap `≥ d` is preserved by scalar multiplication. -/
lemma hasMinGapZ_smul {c : ℤ} {f : UTBase} {d : ℤ} (hf : hasMinGapZ f d) : hasMinGapZ (c • f) d := by
  intro pq hpq
  exact hf pq (by
        simp [Finsupp.mem_support_iff] at hpq ⊢
        exact fun h ↦ by simp [h] at hpq)

/-- A nonnegative gap `≥ d` is preserved by matrix powers. -/
lemma hasMinGapZ_matPow {f : UTBase} {d : ℤ} (n : ℕ) (hf : hasMinGapZ f d) (hd : 0 ≤ d) :
    hasMinGapZ (matPow f n) d := by
  induction' n with n ih
  · exact hf
  · exact hasMinGapZ_mono (by linarith) (matMul_hasMinGapZ hf ih)

/-- A finite sum of elements each having gap `≥ d` again has gap `≥ d`. -/
lemma hasMinGapZ_finset_sum {s : Finset ℕ} {g : ℕ → UTBase} {d : ℤ}
    (hg : ∀ k ∈ s, hasMinGapZ (g k) d) : hasMinGapZ (∑ k ∈ s, g k) d := by
  induction' s using Finset.induction with k s ih
  · exact hasMinGapZ_zero d
  · rw [Finset.sum_insert ih]
    exact hasMinGapZ_add (hg k (Finset.mem_insert_self _ _)) (by
          apply_assumption
          aesop)

/-- A nonnegative gap `≥ d` is preserved by the unipotent inverse. -/
lemma hasMinGapZ_utInv {f : UTBase} {d : ℤ} (hd : 0 ≤ d) (hf : hasMinGapZ f d) :
    hasMinGapZ (utInv f) d := by
  apply hasMinGapZ_finset_sum
  exact fun k hk ↦ hasMinGapZ_smul (hasMinGapZ_matPow k hf hd)

/-- If all second coordinates lie in `S` and the gap `d` exceeds the diameter of `S` (in the sense
`s₁ + d > s₂` for all `s₁, s₂ ∈ S`), then the element must be zero. -/
lemma gap_exceeds_range_is_zero {f : UTBase} {S : Finset ℤ} {d : ℤ} (hf_sec : hasSecCoordsIn f S)
    (hf_gap : hasMinGapZ f d) (hd : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ + d > s₂) : f = 0 := by
  by_contra h_nonzero
  exact absurd (Finset.nonempty_of_ne_empty (show f.support ≠ ∅ by aesop)) (by
        rintro ⟨x, hx⟩
        linarith [hd _ (hf_sec x hx |>.1) _ (hf_sec x hx |>.2), hf_gap x hx])

/-! ## Solvability of restricted UT groups -/

-- The key property: in UT with product order, if matMul of gap-d elements
-- has gap ≥ 2d, then the quotient mod gap ≥ 2d is abelian.
-- This means [G_d, G_d] ⊆ G_{2d}, so the derived series doubles the gap.

/-- Definitional unfolding of the group law: `utMul f g = f + g + matMul f g`. -/
lemma utMul_eq_add_matMul (f g : UTBase) : utMul f g = f + g + matMul f g :=
  rfl

/-- **Gap doubling.** The group commutator of two product-order elements of gap `≥ d` (with
`d ≥ 1`) has gap `≥ 2d`. This is the key estimate making the derived series of a `UT₁`-subgroup
terminate. -/
lemma commutator_gap_doubling {f g : UTBase} {d : ℤ} (hd : 1 ≤ d) (hf_gap : hasMinGapZ f d)
    (hg_gap : hasMinGapZ g d) (hf_valid : isValidProd f) (hg_valid : isValidProd g)
    (_hfg_valid : isValidProd (utMul (utMul (utMul f g) (utInv f)) (utInv g))) :
    hasMinGapZ (utMul (utMul (utMul f g) (utInv f)) (utInv g)) (2 * d) := by
  have h_comm_def :
    utMul (utMul (utMul f g) (utInv f)) (utInv g) =
      (f + utInv f) + (g + utInv g) + matMul f g + matMul (utMul f g) (utInv f) +
        matMul (utMul (utMul f g) (utInv f)) (utInv g) := by
    unfold utMul
    abel
  have h_inv_def : matMul f (utInv f) = -(f + utInv f) ∧ matMul g (utInv g) = -(g + utInv g) := by
    have h_inv_def : ∀ f : UTBase, isValidProd f → matMul f (utInv f) = -(f + utInv f) := by
      intros f hf_valid
      have h_inv_def : utMul f (utInv f) = 0 := by
        have h_inv_def : ∀ f : UT₁, f * f⁻¹ = 1 := fun f ↦ mul_inv_cancel f
        convert congr_arg Subtype.val (h_inv_def ⟨f, hf_valid⟩) using 1
      exact eq_neg_of_add_eq_zero_right (by rw [← h_inv_def, utMul_eq_add_matMul])
    exact ⟨h_inv_def f hf_valid, h_inv_def g hg_valid⟩
  have h_gap_f_inv : hasMinGapZ (f + utInv f) (2 * d) := by
    have h_gap_f_inv : hasMinGapZ (-(matMul f (utInv f))) (2 * d) := by
      have h_gap_f_inv : hasMinGapZ (matMul f (utInv f)) (2 * d) := by
        convert matMul_hasMinGapZ hf_gap (hasMinGapZ_utInv (by linarith) hf_gap) using 1
        ring
      convert hasMinGapZ_smul (show hasMinGapZ (matMul f (utInv f)) (2 * d) from h_gap_f_inv) using 1
      swap
      exacts [-1, by norm_num]
    aesop
  have h_gap_g_inv : hasMinGapZ (g + utInv g) (2 * d) := by
    have h_gap_g_inv : hasMinGapZ (matMul g (utInv g)) (2 * d) := by
      convert matMul_hasMinGapZ hg_gap (hasMinGapZ_utInv (by linarith) hg_gap) using 1
      ring
    simp_all +decide [hasMinGapZ]
    grind
  have h_gap_matMul_fg : hasMinGapZ (matMul f g) (2 * d) := by
    convert matMul_hasMinGapZ hf_gap hg_gap using 1
    ring
  have h_gap_matMul_uf_fg : hasMinGapZ (matMul (utMul f g) (utInv f)) (2 * d) := by
    convert matMul_hasMinGapZ _ _ using 1
    rw [two_mul]
    · convert hasMinGapZ_add _ _ using 1
      · exact hasMinGapZ_add hf_gap hg_gap
      · exact hasMinGapZ_mono (by linarith) h_gap_matMul_fg
    · exact hasMinGapZ_utInv (by linarith) hf_gap
  have h_gap_matMul_uf_uf_fg :
    hasMinGapZ (matMul (utMul (utMul f g) (utInv f)) (utInv g)) (2 * d) := by
    convert matMul_hasMinGapZ _ _ using 1
    rw [two_mul]
    · convert hasMinGapZ_add _ _ using 1
      · convert hasMinGapZ_add _ _ using 1
        · convert hasMinGapZ_add _ _ using 1
          · exact hasMinGapZ_add hf_gap hg_gap
          · exact hasMinGapZ_mono (by linarith) h_gap_matMul_fg
        · exact hasMinGapZ_utInv (by linarith) hf_gap
      · exact hasMinGapZ_mono (by linarith) h_gap_matMul_uf_fg
    · exact hasMinGapZ_utInv (by linarith) hg_gap
  convert hasMinGapZ_add
      (hasMinGapZ_add (hasMinGapZ_add (hasMinGapZ_add h_gap_f_inv h_gap_g_inv) h_gap_matMul_fg)
        h_gap_matMul_uf_fg)
      h_gap_matMul_uf_uf_fg using 1

/-- The `UT₁`-group commutator `⁅x, y⁆` of elements with second-coordinate gap `≥ d` has gap `≥ 2d`
(for `d ≥ 1`); the `UT₁` repackaging of `commutator_gap_doubling`. -/
lemma ut1_commutator_gap {x y : UT₁} {d : ℤ} (hd : 1 ≤ d) (hx : hasMinGapZ x.val d)
    (hy : hasMinGapZ y.val d) : hasMinGapZ (⁅x, y⁆ : UT₁).val (2 * d) := by
  convert commutator_gap_doubling hd hx hy x.prop y.prop _ using 1
  exact utMul_isValidProd (utMul_isValidProd (utMul_isValidProd x.2 y.2) (utInv_isValidProd x.2))
      (utInv_isValidProd y.2)

/-- Any subgroup of `UT₁` whose elements all have second coordinates in a fixed finite set `S` is
solvable: the gap doubles along the derived series until it exceeds the diameter of `S`. -/
lemma ut1_restricted_solvable (K : Subgroup UT₁) (S : Finset ℤ)
    (hK : ∀ x ∈ K, hasSecCoordsIn x.val S) : IsSolvable K := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ + 2 ^ n > s₂ := by
    obtain ⟨M, hM⟩ := Finset.bddAbove (S.image (fun x ↦ |x|))
    exact ⟨⌈M⌉₊ + ⌈M⌉₊, fun s₁ hs₁ s₂ hs₂ ↦ by
        linarith [Nat.le_ceil M,
          show (2 : ℤ) ^ (⌈M⌉₊ + ⌈M⌉₊) ≥ 2 * ⌈M⌉₊ + 1 from
            mod_cast
              Nat.recOn ⌈M⌉₊ (by norm_num) fun n ihn ↦ by
                norm_num [Nat.pow_succ', Nat.pow_add] at *
                nlinarith,
          abs_le.mp (hM <| Finset.mem_image_of_mem _ hs₁),
          abs_le.mp (hM <| Finset.mem_image_of_mem _ hs₂)]⟩
  have h_derived_gap (i : ℕ) : ∀ x ∈ derivedSeries UT₁ i, hasMinGapZ x.val (2 ^ i) := by
    induction' i with i ih <;> simp_all +decide [derivedSeries]
    · intro x pq hpq
      have := x.2 pq hpq
      aesop
    · intro x hx
      rw [Subgroup.commutator_def] at hx
      simp_all +decide [Subgroup.closure]
      specialize hx (Subgroup.closure {g : UT₁ | hasMinGapZ g.val (2 ^ (i + 1))}) ?_ <;>
        simp_all +decide [Subgroup.closure]
      · intro p hp g hg
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hg
        exact hp <| by
            convert ut1_commutator_gap (show 1 ≤ 2 ^ i from one_le_pow₀ (by norm_num)) (ih g₁ hg₁)
                (ih g₂ hg₂) using 1
            ring_nf
            rfl
      · contrapose! hx
        refine' ⟨_, _, _⟩
        refine' { .. }
        exact {g : UT₁ | hasMinGapZ g.val (2 ^ (i + 1))}
        all_goals norm_num +zetaDelta at *
        · intro a b ha hb
          exact (by
              apply_rules [hasMinGapZ_add, matMul_hasMinGapZ]
              have h_comm : hasMinGapZ (matMul a.val b.val) (2 ^ (i + 1) + 2 ^ (i + 1)) :=
                matMul_hasMinGapZ ha hb
              exact hasMinGapZ_mono (by linarith [pow_pos (zero_lt_two' ℤ) (i + 1)]) h_comm)
        · exact hasMinGapZ_zero _
        · intro x hx
          exact (by convert hasMinGapZ_utInv (show 0 ≤ 2 ^ (i + 1) by positivity) hx using 1)
        · exact hx
  have h_derived_le :
    derivedSeries K n ≤ Subgroup.comap (Subgroup.subtype K) (derivedSeries UT₁ n) := by
    refine' Nat.recOn n _ _ <;> simp_all +decide [derivedSeries]
    intro n hn
    simp_all +decide [Subgroup.commutator_def]
    rintro _ ⟨a, ha, ha', b, hb, hb', rfl⟩
    exact Subgroup.subset_closure ⟨_, hn ha', _, hn hb', rfl⟩
  use n
  simp_all +decide [Subgroup.eq_bot_iff_forall]
  intro x hx hx'
  specialize h_derived_le hx'
  simp_all +decide [Subgroup.mem_subgroupOf]
  exact Subtype.ext <|
      gap_exceeds_range_is_zero (hK x hx) (h_derived_gap n x h_derived_le) fun s₁ hs₁ s₂ hs₂ ↦
        hn s₁ hs₁ s₂ hs₂

/-- The anti-order gap: `f` has "minimum anti-gap `≥ d`" when every entry `(p, q)` satisfies
`q.2 + d ≤ p.2` (the second coordinate is decreasing by at least `d`). -/
def hasMinAntiGapZ (f : UTBase) (d : ℤ) : Prop :=
  ∀ pq ∈ f.support, pq.2.2 + d ≤ pq.1.2

/-- Matrix multiplication adds anti-gaps: `matMul f g` has anti-gap `≥ a + b` when `f, g` have
anti-gaps `≥ a, ≥ b`. -/
lemma matMul_hasMinAntiGapZ {f g : UTBase} {a b : ℤ} (hf : hasMinAntiGapZ f a)
    (hg : hasMinAntiGapZ g b) : hasMinAntiGapZ (matMul f g) (a + b) := by
  intro pq hpq
  by_contra h_contra
  simp [matMul] at hpq h_contra
  contrapose! hpq
  simp_all +decide [Finsupp.sum]
  refine Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ ?_
  split_ifs <;> simp_all +decide [Finsupp.single_apply]
  grind +locals

/-- A nonnegative anti-gap `≥ d` is preserved by the unipotent inverse. -/
lemma hasMinAntiGapZ_utInv {f : UTBase} {d : ℤ} (hd : 0 ≤ d) (hf : hasMinAntiGapZ f d) :
    hasMinAntiGapZ (utInv f) d := by
  have h_matPow_gap (n : ℕ) : hasMinAntiGapZ (matPow f n) d := by
    induction' n with n ih
    · exact hf
    · have h_matPow : hasMinAntiGapZ (matMul f (matPow f n)) (d + d) := matMul_hasMinAntiGapZ hf ih
      exact fun pq hpq ↦ by
        have := h_matPow pq hpq
        linarith
  unfold utInv
  induction' f.support.card with n ih <;> simp_all +decide [Finset.sum_range_succ]
  · exact fun pq hpq ↦ by simp at hpq
  · intro pq hpq
    simp [hasMinAntiGapZ] at *
    contrapose! hpq
    rw [Finset.sum_eq_zero] <;> norm_num
    · exact not_not.1 fun h ↦ by linarith [h_matPow_gap n _ _ _ _ h]
    · exact fun x hx ↦ not_not.1 fun hx' ↦ by linarith [h_matPow_gap x _ _ _ _ hx']

/-- An anti-gap `≥ d` is preserved by addition. -/
lemma hasMinAntiGapZ_add {f g : UTBase} {d : ℤ} (hf : hasMinAntiGapZ f d)
    (hg : hasMinAntiGapZ g d) : hasMinAntiGapZ (f + g) d := by
  intro pq hpq
  by_cases h : pq ∈ f.support
  · exact hf pq h
  · exact hg pq (by
          simp [Finsupp.mem_support_iff] at hpq h ⊢
          intro hg'
          simp [hg', h] at hpq)

/-- An anti-gap `≥ d` is preserved by scalar multiplication. -/
lemma hasMinAntiGapZ_smul {c : ℤ} {f : UTBase} {d : ℤ} (hf : hasMinAntiGapZ f d) :
    hasMinAntiGapZ (c • f) d := by
  intro pq hpq
  exact hf pq (by
        simp [Finsupp.mem_support_iff] at hpq ⊢
        exact fun h ↦ by simp [h] at hpq)

/-- The anti-gap bound is monotone in `d`. -/
lemma hasMinAntiGapZ_mono {f : UTBase} {d₁ d₂ : ℤ} (h : d₁ ≤ d₂) (hf : hasMinAntiGapZ f d₂) :
    hasMinAntiGapZ f d₁ := fun pq hpq ↦ le_trans (by omega) (hf pq hpq)

/-- **Anti-gap doubling.** The group commutator of two anti-triangular elements of anti-gap `≥ d`
(with `d ≥ 1`) has anti-gap `≥ 2d`; the `UT₂` analogue of `commutator_gap_doubling`. -/
lemma commutator_anti_gap_doubling {f g : UTBase} {d : ℤ} (hd : 1 ≤ d) (hf_gap : hasMinAntiGapZ f d)
    (hg_gap : hasMinAntiGapZ g d) (hf_valid : isValidAnti f) (hg_valid : isValidAnti g)
    (_hfg_valid : isValidAnti (utMul (utMul (utMul f g) (utInv f)) (utInv g))) :
    hasMinAntiGapZ (utMul (utMul (utMul f g) (utInv f)) (utInv g)) (2 * d) := by
  have h_f_utInv_f : hasMinAntiGapZ (f + utInv f) (2 * d) := by
    have h_f_utInv_f : f + utInv f = -matMul f (utInv f) := by
      have h_cancel : utMul f (utInv f) = 0 := by
        have h_comm : ∀ f : UT₂, f * f⁻¹ = 1 := fun f ↦ mul_inv_cancel f
        convert congr_arg Subtype.val (h_comm ⟨f, hf_valid⟩) using 1
      exact eq_neg_of_add_eq_zero_left (by rw [← h_cancel, utMul_eq_add_matMul])
    have h_matMul_f_utInv_f : hasMinAntiGapZ (matMul f (utInv f)) (2 * d) := by
      convert matMul_hasMinAntiGapZ hf_gap (hasMinAntiGapZ_utInv (by linarith) hf_gap) using 1
      ring
    convert hasMinAntiGapZ_smul
        (show hasMinAntiGapZ (matMul f (utInv f)) (2 * d) from h_matMul_f_utInv_f) using 1
    norm_num [h_f_utInv_f]
    swap
    exacts [-1, by norm_num]
  have h_g_utInv_g : hasMinAntiGapZ (g + utInv g) (2 * d) := by
    have := utInv_utMul_anti g hg_valid
    rw [utMul_eq_add_matMul] at this
    rw [add_comm] at this
    rw [add_comm, eq_neg_of_add_eq_zero_right this]
    convert hasMinAntiGapZ_smul (show hasMinAntiGapZ (matMul (utInv g) g) (2 * d) from ?_) using 1
    rotate_left
    exact -1
    · convert matMul_hasMinAntiGapZ (hasMinAntiGapZ_utInv (by linarith) hg_gap) hg_gap using 1
      ring
    · norm_num
  have h_matMul_f_g : hasMinAntiGapZ (matMul f g) (2 * d) := by
    convert matMul_hasMinAntiGapZ hf_gap hg_gap using 1
    ring
  have h_matMul_utMul_f_g_utInv_f : hasMinAntiGapZ (matMul (utMul f g) (utInv f)) (2 * d) := by
    convert matMul_hasMinAntiGapZ _ _ using 1
    rw [two_mul]
    · exact hasMinAntiGapZ_add (hf_gap) (hg_gap) |> fun h ↦
          hasMinAntiGapZ_mono (by linarith) (matMul_hasMinAntiGapZ hf_gap hg_gap) |> fun h' ↦
            hasMinAntiGapZ_add h h'
    · exact hasMinAntiGapZ_utInv (by linarith) hf_gap
  have h_matMul_utMul_utMul_f_g_utInv_f_utInv_g :
    hasMinAntiGapZ (matMul (utMul (utMul f g) (utInv f)) (utInv g)) (2 * d) := by
    have h_matMul_utMul_utMul_f_g_utInv_f_utInv_g :
      hasMinAntiGapZ (utMul (utMul f g) (utInv f)) (d) := by
      apply hasMinAntiGapZ_add
      · apply hasMinAntiGapZ_add
        · have h_matMul_utMul_f_g : hasMinAntiGapZ (matMul f g) d :=
            hasMinAntiGapZ_mono (by linarith) h_matMul_f_g
          exact hasMinAntiGapZ_add (hasMinAntiGapZ_add hf_gap hg_gap) h_matMul_utMul_f_g
        · exact hasMinAntiGapZ_utInv (by linarith) hf_gap
      · exact hasMinAntiGapZ_mono (by linarith) h_matMul_utMul_f_g_utInv_f
    convert matMul_hasMinAntiGapZ h_matMul_utMul_utMul_f_g_utInv_f_utInv_g
        (hasMinAntiGapZ_utInv (by linarith) hg_gap) using 1
    ring
  convert hasMinAntiGapZ_add
      (hasMinAntiGapZ_add (hasMinAntiGapZ_add h_f_utInv_f h_g_utInv_g) h_matMul_f_g |>
          hasMinAntiGapZ_add <|
        h_matMul_utMul_f_g_utInv_f)
      h_matMul_utMul_utMul_f_g_utInv_f_utInv_g using 1
  unfold utMul
  abel

/-- Anti-order version of `gap_exceeds_range_is_zero`: an element with second coordinates in `S` and
anti-gap exceeding the diameter of `S` must be zero. -/
lemma gap_exceeds_range_is_zero_anti {f : UTBase} {S : Finset ℤ} {d : ℤ}
    (hf_sec : hasSecCoordsIn f S) (hf_gap : hasMinAntiGapZ f d)
    (hd : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ + d > s₂) : f = 0 := by
  by_contra h_nonzero
  obtain ⟨pq, hpq⟩ : ∃ pq ∈ f.support, pq.2.2 + d ≤ pq.1.2 :=
    Exists.elim (Finset.nonempty_of_ne_empty (by aesop)) fun x hx ↦ ⟨x, hx, hf_gap x hx⟩
  linarith [hd _ (hf_sec _ hpq.1 |>.2) _ (hf_sec _ hpq.1 |>.1)]

/-- Any subgroup of `UT₂` whose elements all have second coordinates in a fixed finite set `S` is
solvable; the anti-order analogue of `ut1_restricted_solvable`. -/
lemma ut2_restricted_solvable (K : Subgroup UT₂) (S : Finset ℤ)
    (hK : ∀ x ∈ K, hasSecCoordsIn x.val S) : IsSolvable K := by
  obtain ⟨n, hn⟩ := Finset.bddAbove S
  obtain ⟨m, hm⟩ := Finset.bddBelow S
  obtain ⟨d, hd⟩ : ∃ d : ℕ, 2 ^ d > n - m := pow_unbounded_of_one_lt _ one_lt_two
  have h_derived_series : ∀ i ≤ d, ∀ x ∈ derivedSeries (↥K) i, hasMinAntiGapZ (x.val.val) (2 ^ i) := by
    intro i hi
    induction' i with i ih
    · intro x hx pq hpq
      have := x.1.2 pq
      aesop
    · intro x hx
      have h_comm :
        ∀ y z : ↥K,
          hasMinAntiGapZ (y.val.val) (2 ^ i) →
            hasMinAntiGapZ (z.val.val) (2 ^ i) → hasMinAntiGapZ (⁅y, z⁆.val.val) (2 ^ (i + 1)) := by
        intros y z hy hz
        convert commutator_anti_gap_doubling _ _ _ _ _ using 1
        rotate_left
        exact y.val.val
        exact z.val.val
        exact 2 ^ i
        exact one_le_pow₀ (by norm_num)
        · exact hy
        · exact hz
        · exact y.1.2
        · exact z.1.2
        · simp +decide [pow_succ']
          exact ⟨fun h ↦ fun _ ↦ h, fun h ↦
              h <|
                utMul_isValidAnti
                  (utMul_isValidAnti (utMul_isValidAnti y.1.2 z.1.2) (utInv_isValidAnti y.1.2))
                  (utInv_isValidAnti z.1.2)⟩
      have h_comm : ∀ y ∈ derivedSeries (↥K) (i + 1), hasMinAntiGapZ (y.val.val) (2 ^ (i + 1)) := by
        intro y hy
        induction' hy using Subgroup.closure_induction with y hy ih
        · rcases hy with ⟨g₁, hg₁, g₂, hg₂, rfl⟩
          exact h_comm g₁ g₂ (ih (Nat.le_of_succ_le hi) g₁ hg₁) (ih (Nat.le_of_succ_le hi) g₂ hg₂)
        · simp +decide [hasMinAntiGapZ]
          exact fun a b c d h ↦ False.elim <| h <| by rfl
        · rename_i _el1 _el2 _ih1 _ih2
          exact hasMinAntiGapZ_add (hasMinAntiGapZ_add _ih1 _ih2)
              (hasMinAntiGapZ_mono (by linarith [pow_pos (zero_lt_two' ℤ) (i + 1)])
                (matMul_hasMinAntiGapZ _ih1 _ih2))
        · convert hasMinAntiGapZ_utInv _ _ using 1
          · positivity
          · assumption
      exact h_comm x hx
  have h_derived_series_zero : ∀ x ∈ derivedSeries (↥K) d, x.val.val = 0 := by
    intros x hx
    have h_gap : hasMinAntiGapZ (x.val.val) (2 ^ d) := h_derived_series d le_rfl x hx
    have h_zero : x.val.val = 0 := by
      apply gap_exceeds_range_is_zero_anti
      exacts [hK x x.2, h_gap, fun s₁ hs₁ s₂ hs₂ ↦ by linarith [hn hs₁, hm hs₁, hn hs₂, hm hs₂]]
    exact h_zero
  use d
  rw [eq_bot_iff]
  intro x hx
  specialize h_derived_series_zero x hx
  aesop

/-- A subgroup of `MyK = UT₁ × UT₂` whose elements all have second coordinates in a fixed finite set
`S` is solvable, by combining solvability of its `UT₁`- and `UT₂`-projections. -/
lemma myK_restricted_solvable (K : Subgroup MyK) (S : Finset ℤ)
    (hK : ∀ (x : MyK), x ∈ K → hasSecCoordsIn x.1.val S ∧ hasSecCoordsIn x.2.val S) :
    IsSolvable K := by
  set K₁ : Subgroup UT₁ := K.map (MonoidHom.fst UT₁ UT₂)
  set K₂ : Subgroup UT₂ := K.map (MonoidHom.snd UT₁ UT₂)
  have hK₁ : ∀ x ∈ K₁, hasSecCoordsIn x.val S := by
    rintro x ⟨y, hy, rfl⟩
    exact hK y hy |>.1
  have hK₂ : ∀ x ∈ K₂, hasSecCoordsIn x.val S := by
    rintro x ⟨y, hy, rfl⟩
    exact hK y hy |>.2
  have hK₁_solvable : IsSolvable K₁ := by convert ut1_restricted_solvable K₁ S hK₁
  have hK₂_solvable : IsSolvable K₂ := by convert ut2_restricted_solvable K₂ S hK₂
  have hK_embedding : ∃ f : K →* K₁ × K₂, Function.Injective f := by
    refine' ⟨_, _⟩
    refine'
      MonoidHom.prod
        (MonoidHom.codRestrict (MonoidHom.fst UT₁ UT₂ |> MonoidHom.comp <| Subgroup.subtype K) K₁ _)
        (MonoidHom.codRestrict (MonoidHom.snd UT₁ UT₂ |> MonoidHom.comp <| Subgroup.subtype K) K₂ _)
    all_goals norm_num [Function.Injective]
    · exact fun a b hab ↦ Subgroup.mem_map_of_mem _ hab
    · exact fun a b hab ↦ Subgroup.mem_map_of_mem _ hab
    · aesop
  grind +suggestions

/-! ## Identities for connecting MyG operations to UTBase operations -/

/-- Shifting the second coordinate by `0` is the identity. -/
lemma shiftUTBase₂_zero_id (f : UTBase) : shiftUTBase₂ 0 f = f := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [shiftUTBase₂, Finsupp.equivMapDomain]

/-- Shifting the first coordinate by `0` is the identity. -/
lemma shiftUTBase₁_zero_id (f : UTBase) : shiftUTBase₁ 0 f = f := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [shiftUTBase₁, Finsupp.equivMapDomain]

/-- For M₁ elements (b=0), the product's UT₁ component has second coords preserved -/
lemma M₁_mul_secCoords_fst {g₁ g₂ : MyG} (hb₁ : g₁.b = 0) {S : Finset ℤ}
    (h₁ : hasSecCoordsIn g₁.k.1.val S) (h₂ : hasSecCoordsIn g₂.k.1.val S) :
    hasSecCoordsIn (g₁ * g₂).k.1.val S := by
  show hasSecCoordsIn (g₁.k * phiAction g₁.a g₁.b g₂.k).1.val S
  show hasSecCoordsIn (utMul g₁.k.1.val (phiAction g₁.a g₁.b g₂.k).1.val) S
  apply hasSecCoordsIn_utMul h₁
  show hasSecCoordsIn (shiftUTBase₁ g₁.a (shiftUTBase₂ g₁.b g₂.k.1.val)) S
  rw [hb₁, shiftUTBase₂_zero_id]
  exact hasSecCoordsIn_shift₁ _ h₂

/-- For M₁ elements (b=0), the product's UT₂ component has second coords preserved -/
lemma M₁_mul_secCoords_snd {g₁ g₂ : MyG} (hb₁ : g₁.b = 0) {S : Finset ℤ}
    (h₁ : hasSecCoordsIn g₁.k.2.val S) (h₂ : hasSecCoordsIn g₂.k.2.val S) :
    hasSecCoordsIn (g₁ * g₂).k.2.val S := by
  show hasSecCoordsIn (g₁.k * phiAction g₁.a g₁.b g₂.k).2.val S
  show hasSecCoordsIn (utMul g₁.k.2.val (phiAction g₁.a g₁.b g₂.k).2.val) S
  apply hasSecCoordsIn_utMul h₁
  show hasSecCoordsIn (shiftUTBase₁ g₁.a (shiftUTBase₂ g₁.b g₂.k.2.val)) S
  rw [hb₁, shiftUTBase₂_zero_id]
  exact hasSecCoordsIn_shift₁ _ h₂

/-- For M₁ elements (b=0), the inverse's UT₁ component has second coords preserved -/
lemma M₁_inv_secCoords_fst {g : MyG} (hb : g.b = 0) {S : Finset ℤ}
    (h : hasSecCoordsIn g.k.1.val S) : hasSecCoordsIn g⁻¹.k.1.val S := by
  show hasSecCoordsIn (phiAction (-g.a) (-g.b) g.k⁻¹).1.val S
  show hasSecCoordsIn (shiftUTBase₁ (-g.a) (shiftUTBase₂ (-g.b) g.k⁻¹.1.val)) S
  rw [hb, neg_zero, shiftUTBase₂_zero_id]
  exact hasSecCoordsIn_shift₁ _ (hasSecCoordsIn_utInv h)

/-- For M₁ elements (b=0), the inverse's UT₂ component has second coords preserved -/
lemma M₁_inv_secCoords_snd {g : MyG} (hb : g.b = 0) {S : Finset ℤ}
    (h : hasSecCoordsIn g.k.2.val S) : hasSecCoordsIn g⁻¹.k.2.val S := by
  show hasSecCoordsIn (phiAction (-g.a) (-g.b) g.k⁻¹).2.val S
  show hasSecCoordsIn (shiftUTBase₁ (-g.a) (shiftUTBase₂ (-g.b) g.k⁻¹.2.val)) S
  rw [hb, neg_zero, shiftUTBase₂_zero_id]
  exact hasSecCoordsIn_shift₁ _ (hasSecCoordsIn_utInv h)

/-! ## Analogous lemmas for M₂ (a=0): first-coordinate preservation -/

/-- `f` "has first coordinates in `S`": every entry index `(p, q)` in the support of `f` has both
`p.1 ∈ S` and `q.1 ∈ S`. The first-coordinate analogue of `hasSecCoordsIn`, used for `M₂`. -/
def hasFirstCoordsIn (f : UTBase) (S : Finset ℤ) : Prop :=
  ∀ pq ∈ f.support, pq.1.1 ∈ S ∧ pq.2.1 ∈ S

/-- The zero matrix has first coordinates in any set. -/
lemma hasFirstCoordsIn_zero (S : Finset ℤ) : hasFirstCoordsIn 0 S := by
  intro pq hpq
  simp at hpq

/-- Having first coordinates in `S` is closed under addition. -/
lemma hasFirstCoordsIn_add {f g : UTBase} {S : Finset ℤ} (hf : hasFirstCoordsIn f S)
    (hg : hasFirstCoordsIn g S) : hasFirstCoordsIn (f + g) S := by
  intro pq hpq
  by_cases hf' : pq ∈ f.support
  · exact hf pq hf'
  · have : pq ∈ g.support := by
      simp [Finsupp.mem_support_iff] at hpq hf' ⊢
      intro h
      simp [h, hf'] at hpq
    exact hg pq this

/-- Having first coordinates in `S` is closed under scalar multiplication. -/
lemma hasFirstCoordsIn_smul {c : ℤ} {f : UTBase} {S : Finset ℤ} (hf : hasFirstCoordsIn f S) :
    hasFirstCoordsIn (c • f) S := by
  intro pq hpq
  exact hf pq (by
        simp [Finsupp.mem_support_iff] at hpq ⊢
        exact fun h ↦ by simp [h] at hpq)

/-- Having first coordinates in `S` is closed under matrix multiplication. -/
lemma hasFirstCoordsIn_matMul {f g : UTBase} {S : Finset ℤ} (hf : hasFirstCoordsIn f S)
    (hg : hasFirstCoordsIn g S) : hasFirstCoordsIn (matMul f g) S := by
  intros pq hpq
  contrapose! hpq
  simp_all +decide [matMul]
  simp +decide [Finsupp.sum]
  refine' Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ _
  split_ifs <;> simp_all +decide [Finsupp.single_apply]
  have := hf x
  have := hg y
  aesop

/-- Having first coordinates in `S` is closed under matrix powers. -/
lemma hasFirstCoordsIn_matPow {f : UTBase} {S : Finset ℤ} (n : ℕ) (hf : hasFirstCoordsIn f S) :
    hasFirstCoordsIn (matPow f n) S := by
  induction n with
  | zero => exact hf
  | succ n ih => exact hasFirstCoordsIn_matMul hf ih

/-- Having first coordinates in `S` is closed under the unipotent group law. -/
lemma hasFirstCoordsIn_utMul {f g : UTBase} {S : Finset ℤ} (hf : hasFirstCoordsIn f S)
    (hg : hasFirstCoordsIn g S) : hasFirstCoordsIn (utMul f g) S :=
  hasFirstCoordsIn_add (hasFirstCoordsIn_add hf hg) (hasFirstCoordsIn_matMul hf hg)

/-- Having first coordinates in `S` is closed under the unipotent inverse. -/
lemma hasFirstCoordsIn_utInv {f : UTBase} {S : Finset ℤ} (hf : hasFirstCoordsIn f S) :
    hasFirstCoordsIn (utInv f) S := by
  have h_sum :
    ∀ (s : Finset ℕ) (g : ℕ → UTBase),
      (∀ k ∈ s, hasFirstCoordsIn (g k) S) → hasFirstCoordsIn (∑ k ∈ s, g k) S := by
    intros s g hg
    induction s using Finset.induction <;> simp_all +decide [hasFirstCoordsIn_add]
    exact hasFirstCoordsIn_zero S
  exact h_sum _ _ fun k _ ↦ hasFirstCoordsIn_smul (hasFirstCoordsIn_matPow k hf)

/-- A second-coordinate shift leaves the first coordinates unchanged, so it preserves
`hasFirstCoordsIn S`. -/
lemma hasFirstCoordsIn_shift₂ {f : UTBase} {S : Finset ℤ} (n : ℤ) (hf : hasFirstCoordsIn f S) :
    hasFirstCoordsIn (shiftUTBase₂ n f) S := by
  intro pq hpq
  rw [shiftUTBase₂] at hpq
  simp_all +decide [Finsupp.equivMapDomain_apply]
  specialize hf ((pq.1.1, pq.1.2 - n), pq.2.1, pq.2.2 - n)
  aesop

/-- For M₂ elements (a=0), the product's UT₁ component has first coords preserved -/
lemma M₂_mul_firstCoords_fst {g₁ g₂ : MyG} (ha₁ : g₁.a = 0) {S : Finset ℤ}
    (h₁ : hasFirstCoordsIn g₁.k.1.val S) (h₂ : hasFirstCoordsIn g₂.k.1.val S) :
    hasFirstCoordsIn (g₁ * g₂).k.1.val S := by
  show hasFirstCoordsIn (g₁.k * phiAction g₁.a g₁.b g₂.k).1.val S
  show hasFirstCoordsIn (utMul g₁.k.1.val (phiAction g₁.a g₁.b g₂.k).1.val) S
  apply hasFirstCoordsIn_utMul h₁
  show hasFirstCoordsIn (shiftUTBase₁ g₁.a (shiftUTBase₂ g₁.b g₂.k.1.val)) S
  rw [ha₁, shiftUTBase₁_zero_id]
  exact hasFirstCoordsIn_shift₂ _ h₂

/-- For M₂ elements (a=0), the product's UT₂ component has first coords preserved -/
lemma M₂_mul_firstCoords_snd {g₁ g₂ : MyG} (ha₁ : g₁.a = 0) {S : Finset ℤ}
    (h₁ : hasFirstCoordsIn g₁.k.2.val S) (h₂ : hasFirstCoordsIn g₂.k.2.val S) :
    hasFirstCoordsIn (g₁ * g₂).k.2.val S := by
  show hasFirstCoordsIn (g₁.k * phiAction g₁.a g₁.b g₂.k).2.val S
  show hasFirstCoordsIn (utMul g₁.k.2.val (phiAction g₁.a g₁.b g₂.k).2.val) S
  apply hasFirstCoordsIn_utMul h₁
  show hasFirstCoordsIn (shiftUTBase₁ g₁.a (shiftUTBase₂ g₁.b g₂.k.2.val)) S
  rw [ha₁, shiftUTBase₁_zero_id]
  exact hasFirstCoordsIn_shift₂ _ h₂

/-- For M₂ elements (a=0), the inverse's UT₁ component has first coords preserved -/
lemma M₂_inv_firstCoords_fst {g : MyG} (ha : g.a = 0) {S : Finset ℤ}
    (h : hasFirstCoordsIn g.k.1.val S) : hasFirstCoordsIn g⁻¹.k.1.val S := by
  show hasFirstCoordsIn (phiAction (-g.a) (-g.b) g.k⁻¹).1.val S
  show hasFirstCoordsIn (shiftUTBase₁ (-g.a) (shiftUTBase₂ (-g.b) g.k⁻¹.1.val)) S
  rw [ha, neg_zero, shiftUTBase₁_zero_id]
  exact hasFirstCoordsIn_shift₂ _ (hasFirstCoordsIn_utInv h)

/-- For M₂ elements (a=0), the inverse's UT₂ component has first coords preserved -/
lemma M₂_inv_firstCoords_snd {g : MyG} (ha : g.a = 0) {S : Finset ℤ}
    (h : hasFirstCoordsIn g.k.2.val S) : hasFirstCoordsIn g⁻¹.k.2.val S := by
  show hasFirstCoordsIn (phiAction (-g.a) (-g.b) g.k⁻¹).2.val S
  show hasFirstCoordsIn (shiftUTBase₁ (-g.a) (shiftUTBase₂ (-g.b) g.k⁻¹.2.val)) S
  rw [ha, neg_zero, shiftUTBase₁_zero_id]
  exact hasFirstCoordsIn_shift₂ _ (hasFirstCoordsIn_utInv h)

/-! ## Gap theory for first coordinates (for M₂) -/

/-- `f` has "minimum first-coordinate gap `≥ d`": every entry `(p, q)` satisfies `p.1 + d ≤ q.1`.
The first-coordinate analogue of `hasMinGapZ`, used to make `M₂`-subgroups solvable. -/
def hasMinFirstGapZ (f : UTBase) (d : ℤ) : Prop :=
  ∀ pq ∈ f.support, pq.1.1 + d ≤ pq.2.1

/-- Matrix multiplication adds first-coordinate gaps. -/
lemma matMul_hasMinFirstGapZ {f g : UTBase} {a b : ℤ} (hf : hasMinFirstGapZ f a)
    (hg : hasMinFirstGapZ g b) : hasMinFirstGapZ (matMul f g) (a + b) := by
  intro pq hq
  unfold matMul at hq
  contrapose! hq
  simp_all +decide [Finsupp.mem_support_iff]
  simp_all +decide [Finsupp.sum]
  refine Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ ?_
  split_ifs <;> simp_all +decide [Finsupp.single_apply]
  grind +locals

/-- The zero matrix has first-coordinate gap `≥ d` for every `d`. -/
lemma hasMinFirstGapZ_zero (d : ℤ) : hasMinFirstGapZ 0 d := by
  intro pq hpq
  simp at hpq

/-- The first-coordinate gap bound is monotone in `d`. -/
lemma hasMinFirstGapZ_mono {f : UTBase} {d₁ d₂ : ℤ} (h : d₁ ≤ d₂) (hf : hasMinFirstGapZ f d₂) :
    hasMinFirstGapZ f d₁ := fun pq hpq ↦ le_trans (by omega) (hf pq hpq)

/-- A first-coordinate gap `≥ d` is preserved by addition. -/
lemma hasMinFirstGapZ_add {f g : UTBase} {d : ℤ} (hf : hasMinFirstGapZ f d)
    (hg : hasMinFirstGapZ g d) : hasMinFirstGapZ (f + g) d := by
  intro pq hpq
  by_cases h : pq ∈ f.support
  · exact hf pq h
  · exact hg pq (by
          simp [Finsupp.mem_support_iff] at hpq h ⊢
          intro hg'
          simp [hg', h] at hpq)

/-- A first-coordinate gap `≥ d` is preserved by scalar multiplication. -/
lemma hasMinFirstGapZ_smul {c : ℤ} {f : UTBase} {d : ℤ} (hf : hasMinFirstGapZ f d) :
    hasMinFirstGapZ (c • f) d := by
  intro pq hpq
  exact hf pq (by
        simp [Finsupp.mem_support_iff] at hpq ⊢
        exact fun h ↦ by simp [h] at hpq)

/-- A nonnegative first-coordinate gap `≥ d` is preserved by matrix powers. -/
lemma hasMinFirstGapZ_matPow {f : UTBase} {d : ℤ} (n : ℕ) (hf : hasMinFirstGapZ f d) (hd : 0 ≤ d) :
    hasMinFirstGapZ (matPow f n) d := by
  induction' n with n ih
  · exact hf
  · exact hasMinFirstGapZ_mono (by linarith) (matMul_hasMinFirstGapZ hf ih)

/-- A finite sum of elements each having first-coordinate gap `≥ d` again has gap `≥ d`. -/
lemma hasMinFirstGapZ_finset_sum {s : Finset ℕ} {g : ℕ → UTBase} {d : ℤ}
    (hg : ∀ k ∈ s, hasMinFirstGapZ (g k) d) : hasMinFirstGapZ (∑ k ∈ s, g k) d := by
  induction' s using Finset.induction with k s ih
  · exact hasMinFirstGapZ_zero d
  · rw [Finset.sum_insert ih]
    exact hasMinFirstGapZ_add (hg k (Finset.mem_insert_self _ _)) (by
          apply_assumption
          aesop)

/-- A nonnegative first-coordinate gap `≥ d` is preserved by the unipotent inverse. -/
lemma hasMinFirstGapZ_utInv {f : UTBase} {d : ℤ} (hd : 0 ≤ d) (hf : hasMinFirstGapZ f d) :
    hasMinFirstGapZ (utInv f) d := by
  apply hasMinFirstGapZ_finset_sum
  exact fun k _ ↦ hasMinFirstGapZ_smul (hasMinFirstGapZ_matPow k hf hd)

/-- If all first coordinates lie in `S` and the first-coordinate gap exceeds the diameter of `S`,
then the element must be zero; the first-coordinate analogue of `gap_exceeds_range_is_zero`. -/
lemma firstGap_exceeds_range_is_zero {f : UTBase} {S : Finset ℤ} {d : ℤ}
    (hf_first : hasFirstCoordsIn f S) (hf_gap : hasMinFirstGapZ f d)
    (hd : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ + d > s₂) : f = 0 := by
  by_contra h_nonzero
  exact absurd (Finset.nonempty_of_ne_empty (show f.support ≠ ∅ by aesop)) (by
        rintro ⟨x, hx⟩
        linarith [hd _ (hf_first x hx |>.1) _ (hf_first x hx |>.2), hf_gap x hx])

/-- **First-coordinate gap doubling (product order).** The group commutator of two product-order
elements with first-coordinate gap `≥ d` (and `d ≥ 1`) has first-coordinate gap `≥ 2d`. -/
lemma commutator_firstGap_doubling {f g : UTBase} {d : ℤ} (hd : 1 ≤ d)
    (hf_gap : hasMinFirstGapZ f d) (hg_gap : hasMinFirstGapZ g d) (hf_valid : isValidProd f)
    (hg_valid : isValidProd g)
    (_hfg_valid : isValidProd (utMul (utMul (utMul f g) (utInv f)) (utInv g))) :
    hasMinFirstGapZ (utMul (utMul (utMul f g) (utInv f)) (utInv g)) (2 * d) := by
  have h_inv : ∀ f : UT₁, isValidProd f.val → f * f⁻¹ = 1 := fun f hf ↦ mul_inv_cancel f
  have h_sum : ∀ f : UT₁, isValidProd f.val → utMul f.val (utInv f.val) = 0 := by
    intro f hf_valid
    have h_inv : f * f⁻¹ = 1 := h_inv f hf_valid
    have h_eq : utMul f.val (utInv f.val) = 0 := by convert congr_arg Subtype.val h_inv using 1
    exact h_eq
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : UT₁, f₁.val = f := ⟨⟨f, hf_valid⟩, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : UT₁, g₁.val = g := ⟨⟨g, hg_valid⟩, rfl⟩
  have h_sum_f : f + utInv f = -matMul f (utInv f) := by
    have := h_sum f₁ (by simpa [hf₁] using hf_valid)
    simp_all +decide [utMul]
    exact eq_neg_of_add_eq_zero_left this
  have h_sum_g : g + utInv g = -matMul g (utInv g) := by
    have := h_sum g₁ (hg₁.symm ▸ hg_valid)
    simp_all +decide [utMul_eq_add_matMul]
    exact eq_neg_of_add_eq_zero_left this
  have h_matMul_f : hasMinFirstGapZ (matMul f (utInv f)) (2 * d) := by
    convert matMul_hasMinFirstGapZ hf_gap (hasMinFirstGapZ_utInv (by linarith) hf_gap) using 1
    ring
  have h_matMul_g : hasMinFirstGapZ (matMul g (utInv g)) (2 * d) := by
    convert matMul_hasMinFirstGapZ hg_gap (hasMinFirstGapZ_utInv (by linarith) hg_gap) using 1
    ring
  have h_matMul_fg : hasMinFirstGapZ (matMul f g) (2 * d) := by
    convert matMul_hasMinFirstGapZ hf_gap hg_gap using 1
    ring
  have h_matMul_fg_inv : hasMinFirstGapZ (matMul (utMul f g) (utInv f)) (2 * d) := by
    convert matMul_hasMinFirstGapZ _ _ using 1
    rw [two_mul]
    · convert hasMinFirstGapZ_add _ _ using 1
      · exact hasMinFirstGapZ_add hf_gap hg_gap
      · exact hasMinFirstGapZ_mono (by linarith) h_matMul_fg
    · exact hasMinFirstGapZ_utInv (by linarith) hf_gap
  have h_matMul_fg_inv_g :
    hasMinFirstGapZ (matMul (utMul (utMul f g) (utInv f)) (utInv g)) (2 * d) := by
    have h_matMul_fg_inv_g :
      hasMinFirstGapZ (utMul (utMul f g) (utInv f)) d ∧ hasMinFirstGapZ (utInv g) d := by
      apply And.intro
      · apply hasMinFirstGapZ_add
        · apply hasMinFirstGapZ_add
          · apply hasMinFirstGapZ_add
            · exact hasMinFirstGapZ_add hf_gap hg_gap
            · exact hasMinFirstGapZ_mono (by linarith) h_matMul_fg
          · exact hasMinFirstGapZ_utInv (by linarith) hf_gap
        · exact hasMinFirstGapZ_mono (by linarith) h_matMul_fg_inv
      · exact hasMinFirstGapZ_utInv (by linarith) hg_gap
    convert matMul_hasMinFirstGapZ h_matMul_fg_inv_g.1 h_matMul_fg_inv_g.2 using 1
    ring
  have h_sum_fg :
    utMul (utMul (utMul f g) (utInv f)) (utInv g) =
      f + g + utInv f + utInv g + matMul f g + matMul (utMul f g) (utInv f) +
        matMul (utMul (utMul f g) (utInv f)) (utInv g) := by
    unfold utMul
    simp +decide [add_assoc]
    grind
  rw [h_sum_fg]
  rw [show f + g + utInv f + utInv g = -matMul f (utInv f) + -matMul g (utInv g) by
      rw [← h_sum_f, ← h_sum_g]
      abel1]
  apply_rules [hasMinFirstGapZ_add, hasMinFirstGapZ_smul]
  · convert
      hasMinFirstGapZ_smul (show hasMinFirstGapZ (matMul f (utInv f)) (2 * d) from h_matMul_f) using 1
    swap
    exacts [-1, by norm_num]
  · convert
      hasMinFirstGapZ_smul (show hasMinFirstGapZ (matMul g (utInv g)) (2 * d) from h_matMul_g) using 1
    swap
    exacts [-1, by norm_num]

/-- **First-coordinate gap doubling (anti order).** The same first-coordinate gap doubling for the
group commutator, but for anti-triangular elements. -/
lemma commutator_firstGap_doubling_anti {f g : UTBase} {d : ℤ} (hd : 1 ≤ d)
    (hf_gap : hasMinFirstGapZ f d) (hg_gap : hasMinFirstGapZ g d) (hf_valid : isValidAnti f)
    (hg_valid : isValidAnti g)
    (_hfg_valid : isValidAnti (utMul (utMul (utMul f g) (utInv f)) (utInv g))) :
    hasMinFirstGapZ (utMul (utMul (utMul f g) (utInv f)) (utInv g)) (2 * d) := by
  have h_sum : ∀ f : UT₂, isValidAnti f.val → utMul f.val (utInv f.val) = 0 := by
    intro f hf_valid
    have : f * f⁻¹ = 1 := mul_inv_cancel f
    convert congr_arg Subtype.val this using 1
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : UT₂, f₁.val = f := ⟨⟨f, hf_valid⟩, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : UT₂, g₁.val = g := ⟨⟨g, hg_valid⟩, rfl⟩
  have h_sum_f : f + utInv f = -matMul f (utInv f) := by
    have := h_sum f₁ (by simpa [hf₁] using hf_valid)
    simp_all +decide [utMul]
    exact eq_neg_of_add_eq_zero_left this
  have h_sum_g : g + utInv g = -matMul g (utInv g) := by
    have := h_sum g₁ (hg₁.symm ▸ hg_valid)
    simp_all +decide [utMul_eq_add_matMul]
    exact eq_neg_of_add_eq_zero_left this
  have h_matMul_f : hasMinFirstGapZ (matMul f (utInv f)) (2 * d) := by
    convert matMul_hasMinFirstGapZ hf_gap (hasMinFirstGapZ_utInv (by linarith) hf_gap) using 1
    ring
  have h_matMul_g : hasMinFirstGapZ (matMul g (utInv g)) (2 * d) := by
    convert matMul_hasMinFirstGapZ hg_gap (hasMinFirstGapZ_utInv (by linarith) hg_gap) using 1
    ring
  have h_matMul_fg : hasMinFirstGapZ (matMul f g) (2 * d) := by
    convert matMul_hasMinFirstGapZ hf_gap hg_gap using 1
    ring
  have h_matMul_fg_inv : hasMinFirstGapZ (matMul (utMul f g) (utInv f)) (2 * d) := by
    convert matMul_hasMinFirstGapZ _ _ using 1
    rw [two_mul]
    · convert hasMinFirstGapZ_add _ _ using 1
      · exact hasMinFirstGapZ_add hf_gap hg_gap
      · exact hasMinFirstGapZ_mono (by linarith) h_matMul_fg
    · exact hasMinFirstGapZ_utInv (by linarith) hf_gap
  have h_matMul_fg_inv_g :
    hasMinFirstGapZ (matMul (utMul (utMul f g) (utInv f)) (utInv g)) (2 * d) := by
    have h_both : hasMinFirstGapZ (utMul (utMul f g) (utInv f)) d ∧ hasMinFirstGapZ (utInv g) d :=
      ⟨hasMinFirstGapZ_add
          (hasMinFirstGapZ_add
            (hasMinFirstGapZ_add (hasMinFirstGapZ_add hf_gap hg_gap)
              (hasMinFirstGapZ_mono (by linarith) h_matMul_fg))
            (hasMinFirstGapZ_utInv (by linarith) hf_gap))
          (hasMinFirstGapZ_mono (by linarith) h_matMul_fg_inv),
        hasMinFirstGapZ_utInv (by linarith) hg_gap⟩
    convert matMul_hasMinFirstGapZ h_both.1 h_both.2 using 1
    ring
  have h_sum_fg :
    utMul (utMul (utMul f g) (utInv f)) (utInv g) =
      f + g + utInv f + utInv g + matMul f g + matMul (utMul f g) (utInv f) +
        matMul (utMul (utMul f g) (utInv f)) (utInv g) := by
    unfold utMul
    simp +decide [add_assoc]
    grind
  rw [h_sum_fg]
  rw [show f + g + utInv f + utInv g = -matMul f (utInv f) + -matMul g (utInv g) by
      rw [← h_sum_f, ← h_sum_g]
      abel1]
  apply_rules [hasMinFirstGapZ_add, hasMinFirstGapZ_smul]
  · convert
      hasMinFirstGapZ_smul (show hasMinFirstGapZ (matMul f (utInv f)) (2 * d) from h_matMul_f) using 1
    swap
    exacts [-1, by norm_num]
  · convert
      hasMinFirstGapZ_smul (show hasMinFirstGapZ (matMul g (utInv g)) (2 * d) from h_matMul_g) using 1
    swap
    exacts [-1, by norm_num]

/-! ## First-coordinate restricted solvability for UT₁ and UT₂ -/

/-- The `UT₁`-commutator of elements with first-coordinate gap `≥ d` has gap `≥ 2d` (for `d ≥ 1`). -/
lemma ut1_firstCoord_commutator_gap {x y : UT₁} {d : ℤ} (hd : 1 ≤ d) (hx : hasMinFirstGapZ x.val d)
    (hy : hasMinFirstGapZ y.val d) : hasMinFirstGapZ (⁅x, y⁆ : UT₁).val (2 * d) := by
  convert commutator_firstGap_doubling hd hx hy x.prop y.prop _ using 1
  exact utMul_isValidProd (utMul_isValidProd (utMul_isValidProd x.2 y.2) (utInv_isValidProd x.2))
      (utInv_isValidProd y.2)

/-- The `UT₂`-commutator of elements with first-coordinate gap `≥ d` has gap `≥ 2d` (for `d ≥ 1`). -/
lemma ut2_firstCoord_commutator_gap {x y : UT₂} {d : ℤ} (hd : 1 ≤ d) (hx : hasMinFirstGapZ x.val d)
    (hy : hasMinFirstGapZ y.val d) : hasMinFirstGapZ (⁅x, y⁆ : UT₂).val (2 * d) := by
  convert commutator_firstGap_doubling_anti hd hx hy x.prop y.prop _ using 1
  exact utMul_isValidAnti (utMul_isValidAnti (utMul_isValidAnti x.2 y.2) (utInv_isValidAnti x.2))
      (utInv_isValidAnti y.2)

/-- A subgroup of `UT₁` whose elements all have first coordinates in a fixed finite set `S` is
solvable. -/
lemma ut1_firstCoord_restricted_solvable (K : Subgroup UT₁) (S : Finset ℤ)
    (hK : ∀ x ∈ K, hasFirstCoordsIn x.val S) : IsSolvable K := by
  revert hK K S
  intro K S hK
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ x ∈ K, hasMinFirstGapZ x.val (2 ^ n) → x = 1 := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ + 2 ^ n > s₂ := by
      obtain ⟨M, hM⟩ := Finset.bddAbove S
      cases' pow_unbounded_of_one_lt (M - (sInf S) + 1) one_lt_two with n hn
      use n
      intros s₁ hs₁ s₂ hs₂
      linarith [hM hs₁, hM hs₂, (csInf_le (Finset.bddBelow S) hs₁),
        (csInf_le (Finset.bddBelow S) hs₂), pow_pos (zero_lt_two' ℤ) n]
    use n
    intro x hx hx'
    specialize hn
    have := firstGap_exceeds_range_is_zero (hK x hx) hx' hn
    aesop
  use n + 1
  have h_derived_series :
    ∀ i : ℕ, derivedSeries K i ≤ Subgroup.comap (Subgroup.subtype K) (derivedSeries UT₁ i) := by
    intro i
    induction i <;> simp_all +decide [derivedSeries]
    refine' le_trans (Subgroup.commutator_mono ‹_› ‹_›) _
    simp +decide [Subgroup.commutator_def]
    rintro _ ⟨a, ha, ha', b, hb, hb', rfl⟩
    exact Subgroup.subset_closure ⟨_, ha', _, hb', rfl⟩
  generalize_proofs at *
  have h_derived_series_gap : ∀ i : ℕ, ∀ x ∈ derivedSeries UT₁ i, hasMinFirstGapZ x.val (2 ^ i) := by
    intro i x hx
    induction' i with i ih generalizing x
    generalize_proofs at *
    · exact fun pq hpq ↦ by linarith [x.2 pq hpq]
    · refine' Subgroup.closure_induction _ _ _ _ hx
      generalize_proofs at *
      · rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
        convert ut1_firstCoord_commutator_gap _ (ih g₁ hg₁) (ih g₂ hg₂) using 1
        ring
        exact one_le_pow₀ (by norm_num)
      · exact hasMinFirstGapZ_zero _
      · intro x y hx hy hx' hy'
        have h_comm : hasMinFirstGapZ (x.val + y.val + matMul x.val y.val) (2 ^ (i + 1)) := by
          have h_comm : hasMinFirstGapZ (matMul x.val y.val) (2 ^ (i + 1) + 2 ^ (i + 1)) :=
            matMul_hasMinFirstGapZ hx' hy'
          generalize_proofs at *
          exact hasMinFirstGapZ_add (hasMinFirstGapZ_add hx' hy')
              (hasMinFirstGapZ_mono (by linarith [pow_pos (zero_lt_two' ℤ) (i + 1)]) h_comm)
        generalize_proofs at *
        convert h_comm using 1
      · intro x hx hx'
        exact hasMinFirstGapZ_utInv (by positivity) hx'
  generalize_proofs at *
  simp_all +decide [Subgroup.eq_bot_iff_forall]
  intro x hx hx'
  specialize h_derived_series (n + 1)
  simp_all +decide
  have := h_derived_series hx'
  simp_all +decide [Subgroup.mem_subgroupOf]
  exact hn x hx (h_derived_series_gap n x (Subgroup.commutator_le_left _ _ this))

/-- A subgroup of `UT₂` whose elements all have first coordinates in a fixed finite set `S` is
solvable. -/
lemma ut2_firstCoord_restricted_solvable (K : Subgroup UT₂) (S : Finset ℤ)
    (hK : ∀ x ∈ K, hasFirstCoordsIn x.val S) : IsSolvable K := by
  have h_bound :
    ∀ n, ∀ x ∈ derivedSeries UT₂ n, isValidAnti x.val → hasMinFirstGapZ x.val (2 ^ n) := by
    intro n x hx hx_valid
    induction' n with n ih generalizing x <;> simp_all +decide [pow_succ']
    · exact fun pq hpq ↦ by linarith [hx_valid pq hpq]
    · refine' Subgroup.closure_induction (fun y hy ↦ _) _ _ _ hx
      · obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hy
        convert ut2_firstCoord_commutator_gap _ _ _ using 1
        · exact one_le_pow₀ (by norm_num)
        · exact ih g₁ hg₁ g₁.2
        · apply ih g₂ hg₂
          exact g₂.2
      · exact hasMinFirstGapZ_zero _
      · intro x y hx hy hx' hy'
        refine' hasMinFirstGapZ_add _ _
        · exact hasMinFirstGapZ_add hx' hy'
        · have := matMul_hasMinFirstGapZ hx' hy'
          exact hasMinFirstGapZ_mono (by linarith [pow_pos (zero_lt_two' ℤ) n]) this
      · intro x hx hx_gap
        convert hasMinFirstGapZ_utInv (show 0 ≤ 2 * 2 ^ n by positivity) hx_gap using 1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ + 2 ^ n > s₂ := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ s ∈ S, |s| + ∑ s ∈ S, |s| + 1) one_lt_two
    exact ⟨n, fun s₁ hs₁ s₂ hs₂ ↦ by
        cases abs_cases s₁ <;> cases abs_cases s₂ <;>
          linarith [Finset.single_le_sum (fun x _ ↦ abs_nonneg x) hs₁,
            Finset.single_le_sum (fun x _ ↦ abs_nonneg x) hs₂]⟩
  refine' ⟨n, _⟩
  have h_subgroup : (derivedSeries K n).map (Subgroup.subtype K) ≤ derivedSeries UT₂ n := by
    grind +suggestions
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  specialize h_subgroup (Subgroup.mem_map_of_mem _ hx)
  simp_all +decide
  have := h_bound n x h_subgroup (x.1.2)
  have := firstGap_exceeds_range_is_zero (hK x x.2) this (by aesop)
  aesop

/-- A subgroup of `MyK = UT₁ × UT₂` whose elements all have first coordinates in a fixed finite set
`S` is solvable; the first-coordinate analogue of `myK_restricted_solvable`. -/
lemma myK_firstCoord_restricted_solvable (K : Subgroup MyK) (S : Finset ℤ)
    (hK : ∀ (x : MyK), x ∈ K → hasFirstCoordsIn x.1.val S ∧ hasFirstCoordsIn x.2.val S) :
    IsSolvable K := by
  set K₁ : Subgroup UT₁ := K.map (MonoidHom.fst UT₁ UT₂)
  set K₂ : Subgroup UT₂ := K.map (MonoidHom.snd UT₁ UT₂)
  have hK₁_solvable : IsSolvable K₁ := by
    apply ut1_firstCoord_restricted_solvable
    rintro x ⟨y, hy, rfl⟩
    exact hK y hy |>.1
  have hK_embedding : ∃ (f : K →* K₁ × K₂), Function.Injective f := by
    refine' ⟨_, _⟩
    refine' MonoidHom.mk' _ _
    exact fun x ↦
      ⟨⟨x.val.1, Subgroup.mem_map_of_mem _ x.2⟩, ⟨x.val.2, Subgroup.mem_map_of_mem _ x.2⟩⟩
    all_goals norm_num [Function.Injective]
    grind
  obtain ⟨f, hf⟩ := hK_embedding
  have hK₂_solvable : IsSolvable (K₁ × K₂) := by
    obtain ⟨n₁, hn₁⟩ := hK₁_solvable
    obtain ⟨n₂, hn₂⟩ :=
      ut2_firstCoord_restricted_solvable K₂ S (by
          rintro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          exact hK y hy |>.2)
    use max n₁ n₂
    have h_prod_solvable :
      ∀ n, derivedSeries (K₁ × K₂) n = Subgroup.prod (derivedSeries K₁ n) (derivedSeries K₂ n) := by
      intro n
      induction n <;> simp_all +decide [derivedSeries]
      grind +suggestions
    simp_all +decide [Subgroup.prod_eq_bot_iff]
    exact ⟨Nat.le_induction (by aesop) (fun k hk ih ↦ by simp_all +decide [derivedSeries]) _
          (le_max_left n₁ n₂),
        Nat.le_induction (by aesop) (fun k hk ih ↦ by simp_all +decide [derivedSeries]) _
          (le_max_right n₁ n₂)⟩
  grind +suggestions

/-- Every finitely generated subgroup of `M₁` has all its matrix-part second coordinates inside a
single finite set `S` (the union of the second coordinates appearing in a finite generating set). -/
lemma M₁_fg_bounded_secCoords (H : Subgroup M₁) (hH : H.FG) :
    ∃ S : Finset ℤ,
      ∀ g ∈ H, hasSecCoordsIn (g : M₁).val.k.1.val S ∧ hasSecCoordsIn (g : M₁).val.k.2.val S := by
  obtain ⟨S, hS⟩ := hH
  refine'
    ⟨S.biUnion
        (fun g ↦
          g.val.k.1.val.support.image (fun pq ↦ pq.1.2) ∪
                g.val.k.1.val.support.image (fun pq ↦ pq.2.2) ∪
              g.val.k.2.val.support.image (fun pq ↦ pq.1.2) ∪
            g.val.k.2.val.support.image (fun pq ↦ pq.2.2)),
      _⟩
  intro g hg
  rw [← hS, Subgroup.mem_closure] at hg
  refine'
    hg
        (Subgroup.closure
          {g : M₁ | hasSecCoordsIn (g.val.k.1.val) _ ∧ hasSecCoordsIn (g.val.k.2.val) _})
        _ |>
      fun h ↦ _
  refine' Subgroup.closure_induction (fun x hx ↦ _) _ _ _ h
  any_goals
    exact Finset.biUnion S fun g ↦
        Finset.image (fun pq ↦ pq.1.2) (g.val.k.1.val.support) ∪
              Finset.image (fun pq ↦ pq.2.2) (g.val.k.1.val.support) ∪
            Finset.image (fun pq ↦ pq.1.2) (g.val.k.2.val.support) ∪
          Finset.image (fun pq ↦ pq.2.2) (g.val.k.2.val.support)
  · exact hx
  · exact ⟨hasSecCoordsIn_zero _, hasSecCoordsIn_zero _⟩
  · intro x y hx hy hx' hy'
    exact ⟨M₁_mul_secCoords_fst (show x.val.b = 0 from x.2) hx'.1 hy'.1,
        M₁_mul_secCoords_snd (show x.val.b = 0 from x.2) hx'.2 hy'.2⟩
  · intro x hx hx'
    exact ⟨M₁_inv_secCoords_fst x.2 hx'.1, M₁_inv_secCoords_snd x.2 hx'.2⟩
  · intro x hx
    exact Subgroup.subset_closure ⟨fun pq hpq ↦ by grind +revert, fun pq hpq ↦ by grind +splitImp⟩

/-- Every finitely generated subgroup of `M₂` has all its matrix-part first coordinates inside a
single finite set `S`; the first-coordinate analogue of `M₁_fg_bounded_secCoords`. -/
lemma M₂_fg_bounded_firstCoords (H : Subgroup M₂) (hH : H.FG) :
    ∃ S : Finset ℤ,
      ∀ g ∈ H, hasFirstCoordsIn (g : M₂).val.k.1.val S ∧ hasFirstCoordsIn (g : M₂).val.k.2.val S := by
  obtain ⟨S, hS⟩ := hH
  set S' : Finset ℤ :=
    Finset.biUnion S
      (fun g ↦
        g.val.k.1.val.support.image (fun pq ↦ pq.1.1) ∪
              g.val.k.1.val.support.image (fun pq ↦ pq.2.1) ∪
            g.val.k.2.val.support.image (fun pq ↦ pq.1.1) ∪
          g.val.k.2.val.support.image (fun pq ↦ pq.2.1)) with
    hS'
  refine' ⟨S', _⟩
  rw [← hS]
  refine' fun g hg ↦ Subgroup.closure_induction _ _ _ _ hg
  · intro x hx
    exact ⟨fun pq hpq ↦ by grind, fun pq hpq ↦ by grind +splitImp⟩
  · exact ⟨hasFirstCoordsIn_zero _, hasFirstCoordsIn_zero _⟩
  · intro x y hx hy hx' hy'
    exact ⟨M₂_mul_firstCoords_fst (show x.val.a = 0 from x.2) hx'.1 hy'.1,
        M₂_mul_firstCoords_snd (show x.val.a = 0 from x.2) hx'.2 hy'.2⟩
  · simp +decide [M₂]
    exact fun a ha₁ ha₂ ha₃ ha₄ ↦ ⟨M₂_inv_firstCoords_fst ha₁ ha₃, M₂_inv_firstCoords_snd ha₁ ha₄⟩

/-- The a-projection from M₁ to ℤ (as Multiplicative ℤ) is a homomorphism -/
noncomputable def M₁_a_hom : M₁ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd g.val.a) (by
      intro x y
      exact ofAdd_add _ _)

/-- The homomorphism sending an element of `ker(M₁_a_hom)` (an element of `M₁` with `a = 0`, hence
with trivial shift action) to its `MyK`-component. -/
noncomputable def M₁_ker_to_MyK : M₁_a_hom.ker →* MyK := by
  refine MonoidHom.mk' (fun g ↦ g.val.val.k) ?_
  intro x y
  have hxa : x.val.val.a = 0 := by
    have := x.prop
    simp only [MonoidHom.mem_ker] at this
    change Multiplicative.ofAdd x.val.val.a = 1 at this
    exact Multiplicative.ofAdd.injective (this.trans (ofAdd_zero).symm)
  have hxb : x.val.val.b = 0 := x.val.prop
  have hya : y.val.val.a = 0 := by
    have := y.prop
    simp only [MonoidHom.mem_ker] at this
    change Multiplicative.ofAdd y.val.val.a = 1 at this
    exact Multiplicative.ofAdd.injective (this.trans (ofAdd_zero).symm)
  have hyb : y.val.val.b = 0 := y.val.prop
  show (myG_mul x.val.val y.val.val).1 = x.val.val.1 * y.val.val.1
  unfold myG_mul MyG.k MyG.a MyG.b
  change x.val.val.1 * phiAction x.val.val.2.1 x.val.val.2.2 y.val.val.1 = x.val.val.1 * y.val.val.1
  congr 1
  rw [show x.val.val.2.1 = 0 from hxa, show x.val.val.2.2 = 0 from hxb, phiAction_zero]

/-- If a subgroup `H ≤ M₁` has all second coordinates bounded by `S`, then the kernel of the
`a`-projection on `H` is solvable: it injects into `MyK` with image of bounded second coordinates,
which is solvable by `myK_restricted_solvable`. -/
lemma M₁_ker_solvable_of_bounded (H : Subgroup M₁) (S : Finset ℤ)
    (hS : ∀ g ∈ H, hasSecCoordsIn (g : M₁).val.k.1.val S ∧ hasSecCoordsIn (g : M₁).val.k.2.val S) :
    IsSolvable ((M₁_a_hom.comp (Subgroup.subtype H)).ker) := by
  let phi : (↥(MonoidHom.ker (M₁_a_hom.comp (Subgroup.subtype H)))) →* MyK :=
    MonoidHom.mk' (fun g ↦ g.val.val.val.k) (by
        simp +decide [MonoidHom.mem_ker]
        intro a ha ha' ha'' b hb hb' hb''
        have := ha''
        have := hb''
        simp_all +decide [M₁_a_hom]
        convert M₁_ker_to_MyK.map_mul ⟨⟨a, ha⟩, ?_⟩ ⟨⟨b, hb⟩, ?_⟩ using 1 <;>
          simp +decide [*, M₁_a_hom])
  have h_image_solvable : IsSolvable (MonoidHom.range phi) := by
    apply myK_restricted_solvable
    rintro x ⟨g, rfl⟩
    exact hS _ (Subtype.mem _)
  have h_kernel_iso : Function.Injective phi := by
    intro g₁ g₂ h_eq
    have h_eq_a : g₁.val.val.val.a = 0 ∧ g₂.val.val.val.a = 0 :=
      ⟨by simpa using congr_arg Multiplicative.toAdd g₁.2, by
        simpa using congr_arg Multiplicative.toAdd g₂.2⟩
    have h_eq_b : g₁.val.val.val.b = 0 ∧ g₂.val.val.val.b = 0 := ⟨g₁.val.val.prop, g₂.val.val.prop⟩
    generalize_proofs at *
    cases h : (g₁ : M₁).val
    cases h' : (g₂ : M₁).val
    aesop
  obtain ⟨n, hn⟩ := h_image_solvable
  use n
  have h_kernel_iso :
    derivedSeries (↥(MonoidHom.ker (M₁_a_hom.comp (Subgroup.subtype H)))) n ≤ MonoidHom.ker phi := by
    have h_kernel_iso :
      derivedSeries (↥(MonoidHom.range phi)) n =
        Subgroup.map (MonoidHom.rangeRestrict phi)
          (derivedSeries (↥(MonoidHom.ker (M₁_a_hom.comp (Subgroup.subtype H)))) n) :=
      by grind +suggestions
    simp_all +decide [Subgroup.map_eq_bot_iff]
  exact eq_bot_iff.mpr
      (h_kernel_iso.trans (by simp +decide [MonoidHom.ker_eq_bot_iff, ‹Function.Injective phi›]))

/-- `M₁` is locally solvable: every finitely generated subgroup is solvable, being an extension of a
solvable kernel (with bounded second coordinates) by the abelian group `Multiplicative ℤ`. -/
lemma M₁_locally_solvable : IsLocallySolvable M₁ := by
  intro H hH
  obtain ⟨S, hS⟩ := M₁_fg_bounded_secCoords H hH
  set g := M₁_a_hom.comp (Subgroup.subtype H) with hg_def
  have h_ker_solv : IsSolvable g.ker := M₁_ker_solvable_of_bounded H S hS
  have h_quot_solv : IsSolvable (Multiplicative ℤ) := inferInstance
  exact @solvable_of_ker_le_range _ _ _ _ _ _ (Subgroup.subtype g.ker) g (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩)
      h_ker_solv h_quot_solv

/-- The b-projection from M₂ to ℤ -/
noncomputable def M₂_b_hom : M₂ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd g.val.b) (by
      intro x y
      exact ofAdd_add _ _)

/-- If a subgroup `H ≤ M₂` has all first coordinates bounded by `S`, then the kernel of the
`b`-projection on `H` is solvable; the first-coordinate analogue of `M₁_ker_solvable_of_bounded`. -/
lemma M₂_ker_solvable_of_bounded (H : Subgroup M₂) (S : Finset ℤ)
    (hS :
      ∀ g ∈ H, hasFirstCoordsIn (g : M₂).val.k.1.val S ∧ hasFirstCoordsIn (g : M₂).val.k.2.val S) :
    IsSolvable ((M₂_b_hom.comp (Subgroup.subtype H)).ker) := by
  let phi : (M₂_b_hom.comp (Subgroup.subtype H)).ker →* MyK :=
    MonoidHom.mk' (fun g ↦ g.val.val.val.k) (by
        intro a b
        have ha_a : a.val.val.val.a = 0 := a.val.val.prop
        have ha_b : a.val.val.val.b = 0 := by simpa using congr_arg Multiplicative.toAdd a.prop
        have hb_a : b.val.val.val.a = 0 := b.val.val.prop
        have hb_b : b.val.val.val.b = 0 := by simpa using congr_arg Multiplicative.toAdd b.prop
        show (myG_mul a.val.val.val b.val.val.val).1 = a.val.val.val.1 * b.val.val.val.1
        unfold myG_mul MyG.k MyG.a MyG.b
        change a.val.val.val.1 * phiAction a.val.val.val.2.1 a.val.val.val.2.2 b.val.val.val.1 =
            a.val.val.val.1 * b.val.val.val.1
        congr 1
        rw [show a.val.val.val.2.1 = 0 from ha_a, show a.val.val.val.2.2 = 0 from ha_b,
          phiAction_zero])
  have h_inj : Function.Injective phi := by
    intro g₁ g₂ h
    have h1a : g₁.val.val.val.a = 0 := g₁.val.val.prop
    have h1b : g₁.val.val.val.b = 0 := by simpa using congr_arg Multiplicative.toAdd g₁.prop
    have h2a : g₂.val.val.val.a = 0 := g₂.val.val.prop
    have h2b : g₂.val.val.val.b = 0 := by simpa using congr_arg Multiplicative.toAdd g₂.prop
    cases h₁ : (g₁ : M₂).val
    cases h₂ : (g₂ : M₂).val
    aesop
  have h_image_solv : IsSolvable phi.range := by
    apply myK_firstCoord_restricted_solvable
    rintro x ⟨g, rfl⟩
    exact hS _ (Subtype.mem _)
  exact solvable_of_solvable_injective (f := phi.rangeRestrict)
      (MonoidHom.rangeRestrict_injective_iff.mpr h_inj)

/-- `M₂` is locally solvable; the first-coordinate analogue of `M₁_locally_solvable`. -/
lemma M₂_locally_solvable : IsLocallySolvable M₂ := by
  intro H hH
  obtain ⟨S, hS⟩ := M₂_fg_bounded_firstCoords H hH
  set g := M₂_b_hom.comp (Subgroup.subtype H) with hg_def
  have h_ker_solv : IsSolvable g.ker := M₂_ker_solvable_of_bounded H S hS
  have h_quot_solv : IsSolvable (Multiplicative ℤ) := inferInstance
  exact @solvable_of_ker_le_range _ _ _ _ _ _ (Subgroup.subtype g.ker) g (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩)
      h_ker_solv h_quot_solv

/-- Conjugation formula for kernel elements: conjugating the kernel element `(k, 0, 0)` by `g`
yields `(g.k · φ_{g.a, g.b}(k) · g.k⁻¹, 0, 0)`, staying inside the kernel `MyK × {(0, 0)}`. -/
lemma kernel_conj_formula (g : MyG) (k : MyK) :
    g * (show MyG from (k, 0, 0)) * g⁻¹ =
      (show MyG from (g.k * phiAction g.a g.b k * g.k⁻¹, 0, 0)) := by
  erw [Prod.mk_inj]
  simp +decide [show ∀ g₁ g₂ : MyG, (g₁ * g₂).k = g₁.k * phiAction g₁.a g₁.b g₂.k from fun _ _ ↦
        rfl,
    show ∀ g : MyG, g⁻¹.k = phiAction (-g.a) (-g.b) g.k⁻¹ from fun _ ↦ rfl]
  ring_nf
  simp +decide [MyG.a, MyG.b, MyG.k, phiAction_comp]
  exact phiAction_zero _

/-! ## Single UT₁ entry elements -/

/-- Validity of a single UT₁ entry for gap > 0. -/
lemma single_validProd (p q : ℤ × ℤ) (hp : p.1 < q.1) (hq : p.2 < q.2) :
    isValidProd (Finsupp.single (p, q) 1) := by
  intro pq hpq
  simp [Finsupp.support_single_ne_zero] at hpq
  subst hpq
  exact ⟨hp, hq⟩

/-- The zero matrix is product-order valid (its support is empty). -/
lemma zero_validProd : isValidProd (0 : UTBase) := fun _ h ↦ absurd h (by simp)
/-- The zero matrix is anti-triangularity valid (its support is empty). -/
lemma zero_validAnti : isValidAnti (0 : UTBase) := fun _ h ↦ absurd h (by simp)

/-- Construct a MyG kernel element from a valid UT₁ entry. -/
noncomputable def mkUT1 (f : UTBase) (hf : isValidProd f) : MyG :=
  ((⟨f, hf⟩, ⟨0, zero_validAnti⟩), 0, 0)

/-- mkUT1 of a single entry at positions (m*a, m*b) → (n*a, n*b). -/
noncomputable def singleElt (m n a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hmn : m < n) : MyG :=
  mkUT1 (Finsupp.single ((m * a, m * b), (n * a, n * b)) 1)
    (single_validProd _ _ (by nlinarith) (by nlinarith))

/-- A single-entry generator `singleElt m n a b` is never the identity. -/
lemma singleElt_ne_one (m n a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hmn : m < n) :
    singleElt m n a b ha hb hmn ≠ 1 := by
  simp +decide [Prod.ext_iff, MyG]
  erw [Subtype.mk.injEq]
  norm_num

/-- Multiplication of `mkUT1` elements reduces to `utMul` of their `UT₁` data. -/
lemma mkUT1_mul (f₁ f₂ : UTBase) (hf₁ : isValidProd f₁) (hf₂ : isValidProd f₂) :
    mkUT1 f₁ hf₁ * mkUT1 f₂ hf₂ = mkUT1 (utMul f₁ f₂) (utMul_isValidProd hf₁ hf₂) := by
  unfold mkUT1
  erw [Prod.mk_inj]
  norm_num
  unfold MyG.k MyG.a MyG.b
  simp +decide [phiAction_zero]
  exact ⟨rfl, rfl⟩

/-- The inverse of a `mkUT1` element reduces to `utInv` of its `UT₁` data. -/
lemma mkUT1_inv (f : UTBase) (hf : isValidProd f) :
    (mkUT1 f hf)⁻¹ = mkUT1 (utInv f) (utInv_isValidProd hf) := by
  unfold mkUT1
  rw [eq_comm]
  apply Prod.ext
  · apply Prod.ext
    apply Subtype.ext
    exact (by
        convert rfl using 1
        convert shiftUTBase₁_zero_id (shiftUTBase₂ 0 (utInv f)) using 1
        exact Eq.symm (shiftUTBase₂_zero_id (utInv f)))
    apply Subtype.ext
    apply Eq.symm
    exact (by
        have := @utInv_utMul_prod f hf
        convert congr_arg (fun x : UTBase ↦ x) this.symm using 1
        grind)
  · rfl

/-- `mkUT1` is injective: two `mkUT1` elements are equal iff their underlying `UTBase` values are. -/
lemma mkUT1_eq_iff (f₁ f₂ : UTBase) (hf₁ : isValidProd f₁) (hf₂ : isValidProd f₂) :
    mkUT1 f₁ hf₁ = mkUT1 f₂ hf₂ ↔ f₁ = f₂ := by grind +locals

/-- The commutator of two adjacent single-entry generators combines them: in `MyG`,
`⁅e_{m,k}, e_{k,n}⁆ = e_{m,n}`. -/
lemma singleElt_comm (m k n a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hmk : m < k) (hkn : k < n) :
    singleElt m k a b ha hb hmk * singleElt k n a b ha hb hkn * (singleElt m k a b ha hb hmk)⁻¹ *
        (singleElt k n a b ha hb hkn)⁻¹ =
      singleElt m n a b ha hb (lt_trans hmk hkn) := by
  unfold singleElt
  simp +decide [mkUT1_mul, mkUT1_inv]
  apply (mkUT1_eq_iff _ _ _ _).mpr
  unfold utMul utInv
  simp +decide [Finsupp.support_single_ne_zero]
  unfold matMul matPow
  simp +decide [Finsupp.sum_single_index]
  simp +decide [Finsupp.sum_neg_index, Finsupp.sum_single_index]
  rw [Finsupp.sum_of_support_subset]
  case s =>
    exact {((m * a, m * b), k * a, k * b), ((k * a, k * b), n * a, n * b),
        ((m * a, m * b), n * a, n * b)}
  · rw [Finset.sum_insert, Finset.sum_insert] <;> simp +decide [Finsupp.single_apply]
    · rw [Finsupp.sum_of_support_subset] <;> norm_num [Finsupp.single_apply]
      case s =>
        exact {((m * a, m * b), k * a, k * b), ((k * a, k * b), n * a, n * b),
            ((m * a, m * b), n * a, n * b)}
      · rw [Finset.sum_insert, Finset.sum_insert] <;> simp +decide
        · simp +decide [Finsupp.single_apply, Finsupp.ext_iff]
          grind +revert
        · grind
        · grind
      · intro x hx
        simp_all +decide [Finsupp.single_apply]
        grind
    · grind
    · grind
  · intro x hx
    contrapose! hx
    simp_all +decide
  · simp +decide

/-! ## UT₁ right inverse -/

/-- `utInv f` is also a right inverse of `f` under `utMul` for product-order valid elements. -/
lemma utMul_utInv_prod (f : UTBase) (hf : isValidProd f) : utMul f (utInv f) = 0 :=
  congr_arg Subtype.val (@mul_inv_cancel UT₁ _ ⟨f, hf⟩)

/-- Conjugating a single entry `e_{p,q}` by a valid `UT₁` element `f` whose support is disjoint from
the relevant indices leaves it unchanged: `f · e_{p,q} · f⁻¹ = e_{p,q}`. -/
lemma ut1_conj_single_disjoint (f : UTBase) (hf : isValidProd f) (p q : ℤ × ℤ)
    (hp : ∀ pq ∈ f.support, p ≠ pq.2) (hq' : ∀ pq ∈ (utInv f).support, q ≠ pq.1) :
    utMul (utMul f (Finsupp.single (p, q) 1)) (utInv f) = Finsupp.single (p, q) 1 := by
  unfold utMul
  have h_inner_zero : matMul f (Finsupp.single (p, q) 1) = 0 := by
    apply Finset.sum_eq_zero
    intro pq hpq
    simp_all +decide
    grind +ring
  simp_all +decide [matMul_add_left]
  rw [show matMul (fun₀ | (p, q) => 1) (utInv f) = 0 by
      refine' Finsupp.ext fun x ↦ _
      unfold matMul
      simp +decide
      exact Finset.sum_eq_zero fun y hy ↦ by
          specialize hq' y.1.1 y.1.2 y.2.1 y.2.2
          aesop]
  convert congr_arg (fun x ↦ x + Finsupp.single (p, q) 1) (utMul_utInv_prod f hf) using 1
  abel_nf
  · unfold utMul
    abel
  · norm_num

/-! ## Conjugation shifts single entries (far from support) -/

/-- The "index set" of a UTBase element: all ℤ×ℤ values appearing as
    first or second component of entries in support. -/
def utIndices (f : UTBase) : Finset (ℤ × ℤ) :=
  f.support.image Prod.fst ∪ f.support.image Prod.snd

/-- When the shifted target indices `(m+1)·(a,b)` and `(n+1)·(a,b)` avoid the support of `g.k.1`
and of its inverse, conjugating `singleElt m n` by `g` is exactly the index shift by one:
`g · e_{m,n} · g⁻¹ = e_{m+1, n+1}`. -/
lemma conj_singleElt_shift (g : MyG) (m n : ℤ) (ha : 0 < g.a) (hb : 0 < g.b) (hmn : m < n)
    (h1 :
      ∀ pq ∈ g.k.1.val.support,
        ((m + 1) * g.a, (m + 1) * g.b) ≠ pq.2 ∧ ((n + 1) * g.a, (n + 1) * g.b) ≠ pq.1)
    (_h2 :
      ∀ pq ∈ g.k.1.val.support,
        ((m + 1) * g.a, (m + 1) * g.b) ≠ pq.1 ∧ ((n + 1) * g.a, (n + 1) * g.b) ≠ pq.2)
    (h3 :
      ∀ pq ∈ (utInv g.k.1.val).support,
        ((m + 1) * g.a, (m + 1) * g.b) ≠ pq.2 ∧ ((n + 1) * g.a, (n + 1) * g.b) ≠ pq.1)
    (_h4 :
      ∀ pq ∈ (utInv g.k.1.val).support,
        ((m + 1) * g.a, (m + 1) * g.b) ≠ pq.1 ∧ ((n + 1) * g.a, (n + 1) * g.b) ≠ pq.2) :
    g * singleElt m n g.a g.b ha hb hmn * g⁻¹ =
      singleElt (m + 1) (n + 1) g.a g.b ha hb (by omega) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      simp +decide [singleElt]
      simp +decide [kernel_conj_formula, mkUT1]
      unfold phiAction
      simp +decide [shiftUTBase₁, shiftUTBase₂]
      ring_nf
      convert ut1_conj_single_disjoint _ _ _ _ _ _ using 1
      · exact g.k.1.2
      · exact fun pq hpq ↦ by
          convert h1 pq hpq |>.1 using 1
          ring_nf
      · grind
    · erw [kernel_conj_formula]
      simp +decide [MyG.k, MyG.a, MyG.b, phiAction]
      erw [mul_one]
      aesop
  · show (myG_mul _ (myG_inv _)).2 = (0, 0)
    unfold myG_mul myG_inv
    simp +decide [*]
    unfold MyG.a MyG.b
    simp +decide [*]
    exact ⟨rfl, rfl⟩

/-- For `a, b > 0` and any finite set `S` of lattice points, there is a threshold `m₀` beyond which
the points `m·(a, b)` all avoid `S`. -/
lemma exists_far_threshold (S : Finset (ℤ × ℤ)) (a b : ℤ) (ha : 0 < a) (_hb : 0 < b) :
    ∃ m₀ : ℕ, ∀ m : ℤ, (m₀ : ℤ) ≤ m → (m * a, m * b) ∉ S := by
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ (x y : ℤ), (x, y) ∈ S → |x| ≤ M ∧ |y| ≤ M := by
    have h_finite : ∃ M : ℤ, ∀ p ∈ S, |p.1| ≤ M ∧ |p.2| ≤ M := by
      have h_abs_finite : Set.Finite (Set.image (fun p : ℤ × ℤ ↦ max (|p.1|) (|p.2|)) S) :=
        S.finite_toSet.image _
      exact ⟨h_abs_finite.bddAbove.choose, fun p hp ↦
          ⟨le_trans (le_max_left _ _)
              (h_abs_finite.bddAbove.choose_spec (Set.mem_image_of_mem _ hp)),
            le_trans (le_max_right _ _)
              (h_abs_finite.bddAbove.choose_spec (Set.mem_image_of_mem _ hp))⟩⟩
    exact ⟨h_finite.choose, fun x y hxy ↦ h_finite.choose_spec (x, y) hxy⟩
  exact ⟨Int.toNat (M + 1), fun m hm h ↦ by
      cases abs_cases (m * a) <;> cases abs_cases (m * b) <;>
        nlinarith [Int.self_le_toNat (M + 1), hM _ _ h]⟩

/-- The commutator [h, g] can be rewritten as h * (g * h * g⁻¹)⁻¹. -/
lemma commutator_eq_mul_conj_inv (h g : MyG) : h * g * h⁻¹ * g⁻¹ = h * (g * h * g⁻¹)⁻¹ := by group

/-- The product `e_{p,k} · (e_{k,q})⁻¹` of adjacent single entries (with `p, k, q` the consecutive
points `m, m+1, m+2` scaled by `(a, b)`) is the "coboundary" `e_{p,k} - e_{k,q} - e_{p,q}`. -/
lemma coboundary_formula (m a b : ℤ) :
    let p := (m * a, m * b)
    let k := ((m + 1) * a, (m + 1) * b)
    let q := ((m + 2) * a, (m + 2) * b)
    utMul (Finsupp.single (p, k) 1) (-(Finsupp.single (k, q) 1)) =
      Finsupp.single (p, k) 1 - Finsupp.single (k, q) 1 - Finsupp.single (p, q) 1 := by
  unfold utMul
  simp +decide [sub_eq_add_neg, matMul]
  rw [Finsupp.sum_neg_index]
  norm_num
  · ext
    simp [Finsupp.single_apply]
  · aesop

/-- matMul distributes over negation on the right. -/
lemma matMul_neg_right (f g : UTBase) : matMul f (-g) = -matMul f g := by
  have h : matMul f g + matMul f (-g) = 0 := by
    rw [← matMul_add_right]
    simp
    unfold matMul
    simp [Finsupp.sum]
  exact eq_neg_of_add_eq_zero_right h

/-- matMul distributes over negation on the left. -/
lemma matMul_neg_left (f g : UTBase) : matMul (-f) g = -matMul f g := by
  have h : matMul f g + matMul (-f) g = 0 := by
    rw [← matMul_add_left]
    simp
    unfold matMul
    simp [Finsupp.sum]
  exact eq_neg_of_add_eq_zero_right h

/-- matMul distributes over subtraction on the right. -/
lemma matMul_sub_right (f g h : UTBase) : matMul f (g - h) = matMul f g - matMul f h := by
  rw [sub_eq_add_neg, matMul_add_right, matMul_neg_right, sub_eq_add_neg]

/-- matMul distributes over subtraction on the left. -/
lemma matMul_sub_left (f g h : UTBase) : matMul (f - g) h = matMul f h - matMul g h := by
  rw [sub_eq_add_neg, matMul_add_left, matMul_neg_left, sub_eq_add_neg]

/-- Inverse of the coboundary `c = e_{p,k} - e_{k,q} - e_{p,q}`: `utInv c = -e_{p,k} + e_{k,q}`. -/
lemma utInv_coboundary (p k q : ℤ × ℤ) (hpk : k ≠ p) (hkq : q ≠ k) (hpq : q ≠ p) :
    utInv (Finsupp.single (p, k) 1 - Finsupp.single (k, q) 1 - Finsupp.single (p, q) 1) =
      -(Finsupp.single (p, k) 1) + Finsupp.single (k, q) 1 := by
  set c : UTBase := Finsupp.single (p, k) 1 - Finsupp.single (k, q) 1 - Finsupp.single (p, q) 1
  have h_inv : utInv c = -c + matPow c 1 - matPow c 2 := by
    have h_card : c.support.card = 3 := by
      rw [show c.support = {(p, k), (k, q), (p, q)} from ?_]
      · grind
      · ext ⟨x, y⟩
        simp +decide [c, Finsupp.single_apply, sub_eq_add_neg]
        aesop
    unfold utInv
    simp +decide [h_card]
    norm_num [Finset.sum_range_succ, matPow]
    ring_nf!
    abel1
  have h_pow1 : matPow c 1 = -Finsupp.single (p, q) 1 := by
    simp +decide [matPow, matMul]
    simp +decide [c]
    simp +decide [Finsupp.sum, Finsupp.single_apply]
    rw [Finset.sum_eq_single (p, k), Finset.sum_eq_single (k, q)] <;>
      simp +decide [*, Finsupp.single_apply]
    · ext
      simp +decide [Finsupp.single_apply]
      aesop
    · aesop
    · intro a b a_1 b_1 h₁ h₂
      split_ifs at h₁ <;> simp_all +decide
      · rw [Finset.sum_eq_zero]
        aesop
      · rw [Finset.sum_eq_zero]
        aesop
  have h_pow2 : matPow c 2 = matMul c (-Finsupp.single (p, q) 1) := h_pow1 ▸ rfl
  simp_all +decide
  rw [matMul_neg_right]
  ring_nf!
  ext
  simp [matMul]
  simp +decide [Finsupp.sum, Finsupp.single_apply]
  ring_nf
  rw [Finset.sum_eq_zero] <;> aesop

/-- The `UT₁`-commutator of `f = e_{m,m+1}` with the coboundary
`c = e_{m,m+1} - e_{m+1,m+2} - e_{m,m+2}` equals `-e_{m,m+2}` (a single gap-`2·(a,b)` entry). This is
the algebraic core of the gap-doubling step. -/
lemma double_comm_extraction (m a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    let p := (m * a, m * b)
    let k := ((m + 1) * a, (m + 1) * b)
    let q := ((m + 2) * a, (m + 2) * b)
    let f := Finsupp.single (p, k) 1
    let c := Finsupp.single (p, k) 1 - Finsupp.single (k, q) 1 - Finsupp.single (p, q) 1
    utMul (utMul (utMul f c) (utInv f)) (utInv c) = -(Finsupp.single (p, q) 1) := by
  have h_distinct :
    (m + 1) * a ≠ m * a ∧
      (m + 2) * a ≠ (m + 1) * a ∧
        (m + 2) * a ≠ m * a ∧
          (m + 1) * b ≠ m * b ∧ (m + 2) * b ≠ (m + 1) * b ∧ (m + 2) * b ≠ m * b :=
    ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have h_coboundary :
    utInv
        (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 -
            Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 -
          Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1) =
      -Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 +
        Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 := by
    apply utInv_coboundary
    aesop
    aesop
    aesop
  have h_inv_single :
    ∀ p q : ℤ × ℤ, p ≠ q → ∀ a : ℤ, utInv (Finsupp.single (p, q) a) = -Finsupp.single (p, q) a := by
    intros p q hpq a
    simp [utInv, Finsupp.single]
    split_ifs <;> simp_all +decide [matPow]
    rfl
  have h_matMul_single :
    ∀ p q r : ℤ × ℤ,
      p ≠ q ∧ q ≠ r ∧ p ≠ r →
        ∀ a b : ℤ,
          matMul (Finsupp.single (p, q) a) (Finsupp.single (q, r) b) =
            Finsupp.single (p, r) (a * b) := by
    intros p q r h_distinct a b
    simp [matMul]
  have h_matMul_single_ne :
    ∀ p q r s : ℤ × ℤ,
      q ≠ r → ∀ a b : ℤ, matMul (Finsupp.single (p, q) a) (Finsupp.single (r, s) b) = 0 := by
    intros p q r s hqr a b
    simp [matMul, hqr]
  simp +decide [*, utMul]
  rw [h_inv_single]
  · simp +decide [matMul_add_left, matMul_add_right, matMul_neg_left, matMul_neg_right,
      matMul_sub_left, matMul_sub_right]
    simp +decide [h_matMul_single_ne, h_distinct]
    rw [h_matMul_single] <;> simp +decide
    · rw [h_matMul_single_ne] <;> simp +decide [h_distinct]
      rw [h_matMul_single_ne] <;> simp +decide [h_distinct]
      abel1
    · grind
  · grind

/-- The coboundary `e_{p,k} - e_{k,q} - e_{p,q}` is product-order valid. -/
lemma coboundary_isValidProd (m a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    isValidProd
      (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 -
          Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 -
        Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1) := by
  intro pq hpq
  simp +decide [Finsupp.sub_apply, Finsupp.single_apply] at hpq ⊢
  grind

/-- Validity of negative single entry. -/
lemma neg_single_isValidProd (p q : ℤ × ℤ) (hp : p.1 < q.1) (hq : p.2 < q.2) :
    isValidProd (-(Finsupp.single (p, q) 1)) := by
  intro pq hpq
  simp [Finsupp.support_neg, Finsupp.support_single_ne_zero] at hpq
  subst hpq
  exact ⟨hp, hq⟩

/-- Group commutator of two mkUT1 elements is mkUT1 of the UT commutator. -/
lemma mkUT1_commutator (f₁ f₂ : UTBase) (hf₁ : isValidProd f₁) (hf₂ : isValidProd f₂) :
    mkUT1 f₁ hf₁ * mkUT1 f₂ hf₂ * (mkUT1 f₁ hf₁)⁻¹ * (mkUT1 f₂ hf₂)⁻¹ =
      mkUT1 (utMul (utMul (utMul f₁ f₂) (utInv f₁)) (utInv f₂))
        (utMul_isValidProd (utMul_isValidProd (utMul_isValidProd hf₁ hf₂) (utInv_isValidProd hf₁))
          (utInv_isValidProd hf₂)) :=
  by simp [mkUT1_mul, mkUT1_inv]

/-- The commutator [h₁, g] = h₁ * (g*h₁*g⁻¹)⁻¹ when written in terms of singleElt. -/
lemma commutator_singleElt_g (g : MyG) (m₀ : ℤ) (ha : 0 < g.a) (hb : 0 < g.b)
    (hshift :
      g * singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega) * g⁻¹ =
        singleElt (m₀ + 1) (m₀ + 2) g.a g.b ha hb (by omega)) :
    singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega) * g *
          (singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega))⁻¹ *
        g⁻¹ =
      singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega) *
        (singleElt (m₀ + 1) (m₀ + 2) g.a g.b ha hb (by omega))⁻¹ := by
  rw [commutator_eq_mul_conj_inv]
  congr 1
  rw [← hshift]

/-- The product of adjacent single-entry generators `e_{m,m+1} · (e_{m+1,m+2})⁻¹` equals `mkUT1` of
the coboundary `e_{p,k} - e_{k,q} - e_{p,q}`. -/
lemma singleElt_mul_inv_singleElt (m a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    singleElt m (m + 1) a b ha hb (by omega) * (singleElt (m + 1) (m + 2) a b ha hb (by omega))⁻¹ =
      mkUT1
        (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 -
            Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 -
          Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1)
        (coboundary_isValidProd m a b ha hb) := by
  unfold singleElt
  rw [mkUT1_inv, mkUT1_mul]
  apply (mkUT1_eq_iff _ _ _ _).mpr
  convert coboundary_formula m a b using 1
  ext
  simp [utInv]
  rw [Finsupp.support_single_ne_zero] <;> norm_num [matPow]

/-- Iterating commutators on single entries: with `h₁ = e_{m,m+1}` and `c₁ = h₁ · (e_{m+1,m+2})⁻¹`,
the commutator `⁅h₁, c₁⁆` equals `(e_{m,m+2})⁻¹`, the inverse of the gap-`2` generator. -/
lemma double_comm_singleElt (m a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    let h₁ := singleElt m (m + 1) a b ha hb (by omega)
    let c₁ := h₁ * (singleElt (m + 1) (m + 2) a b ha hb (by omega))⁻¹
    h₁ * c₁ * h₁⁻¹ * c₁⁻¹ = (singleElt m (m + 2) a b ha hb (by omega))⁻¹ := by
  have h_c₁_def :
    singleElt m (m + 1) a b ha hb (by omega) * (singleElt (m + 1) (m + 2) a b ha hb (by omega))⁻¹ =
      mkUT1
        (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 -
            Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 -
          Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1)
        (coboundary_isValidProd m a b ha hb) :=
    by convert singleElt_mul_inv_singleElt m a b ha hb using 1
  have h_double_comm :
    mkUT1 (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1)
              (single_validProd _ _ (by nlinarith) (by nlinarith)) *
            mkUT1
              (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 -
                  Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 -
                Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1)
              (coboundary_isValidProd m a b ha hb) *
          (mkUT1 (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1)
              (single_validProd _ _ (by nlinarith) (by nlinarith)))⁻¹ *
        (mkUT1
            (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 -
                Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 -
              Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1)
            (coboundary_isValidProd m a b ha hb))⁻¹ =
      mkUT1 (-(Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1))
        (neg_single_isValidProd ((m * a, m * b)) (((m + 2) * a, (m + 2) * b)) (by nlinarith)
          (by nlinarith)) := by
    convert mkUT1_commutator _ _ _ _ using 1
    congr! 1
    convert double_comm_extraction m a b ha hb |> Eq.symm using 1
  have h_mkUT1_inv :
    mkUT1 (-(Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1))
        (neg_single_isValidProd ((m * a, m * b)) (((m + 2) * a, (m + 2) * b)) (by nlinarith)
          (by nlinarith)) =
      (mkUT1 (Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1)
          (single_validProd _ _ (by nlinarith) (by nlinarith)))⁻¹ := by
    rw [mkUT1_inv]
    congr
    ext
    simp [utInv]
    rw [Finset.sum_eq_single 0] <;> simp +decide [matPow]
    intro n hn hn'
    rcases n with (_ | _ | n) <;> simp_all +decide [Finsupp.support_single_ne_zero]
  unfold singleElt at *
  aesop

/-- If `g ∈ N` (normal) with `a, b > 0` and conjugation by `g` shifts single entries beyond `m₀`,
then the gap-`2` generator `e_{m₀, m₀+2}` lies in `N`, extracted via a double commutator. -/
lemma extraction_from_shift (N : Subgroup MyG) (hN : N.Normal) (g : MyG) (hg : g ∈ N) (ha : 0 < g.a)
    (hb : 0 < g.b) (m₀ : ℤ)
    (hshift :
      ∀ (m n : ℤ) (hmn : m < n),
        m₀ ≤ m →
          g * singleElt m n g.a g.b ha hb hmn * g⁻¹ =
            singleElt (m + 1) (n + 1) g.a g.b ha hb (by omega)) :
    singleElt m₀ (m₀ + 2) g.a g.b ha hb (by omega) ∈ N := by
  have hc₂_eq :
    (singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega)) *
        (singleElt (m₀ + 1) (m₀ + 2) g.a g.b ha hb (by omega))⁻¹ ∈
      N := by
    have hc₁_mem :
      singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega) * g *
            (singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega))⁻¹ *
          g⁻¹ ∈
        N := by
      have hc₁_mem :
        singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega) * g *
            (singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega))⁻¹ ∈
          N :=
        hN.conj_mem _ hg _
      exact N.mul_mem hc₁_mem (N.inv_mem hg)
    have h_prod :
      singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega) * g *
            (singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega))⁻¹ *
          g⁻¹ =
        singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega) *
          (singleElt (m₀ + 1) (m₀ + 2) g.a g.b ha hb (by omega))⁻¹ := by
      convert commutator_singleElt_g g m₀ ha hb _ using 1
      grind
    exact h_prod ▸ hc₁_mem
  have hc₂_mem :
    (singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega)) *
        (singleElt (m₀ + 1) (m₀ + 2) g.a g.b ha hb (by omega))⁻¹ ∈
      N :=
    hc₂_eq
  convert N.inv_mem
      (N.mul_mem (hN.conj_mem _ hc₂_mem (singleElt m₀ (m₀ + 1) g.a g.b ha hb (by omega)))
        (N.inv_mem hc₂_mem)) using 1
  convert congr_arg Inv.inv (double_comm_singleElt m₀ g.a g.b ha hb) |> Eq.symm using 1
  norm_num

/-- For `g ∈ N` (normal) with `a, b > 0`, there is a threshold `m₀` such that `N` contains the
gap-`2` generator `e_{m₀, m₀+2}` and conjugation by `g` shifts every single entry beyond `m₀` by
one. Combines `exists_far_threshold`, `conj_singleElt_shift`, and `extraction_from_shift`. -/
lemma singleElt_in_N_and_shift (N : Subgroup MyG) (hN : N.Normal) (g : MyG) (hg : g ∈ N)
    (ha : 0 < g.a) (hb : 0 < g.b) :
    ∃ m₀ : ℤ,
      singleElt m₀ (m₀ + 2) g.a g.b ha hb (by omega) ∈ N ∧
        ∀ (m n : ℤ) (hmn : m < n),
          m₀ ≤ m →
            g * singleElt m n g.a g.b ha hb hmn * g⁻¹ =
              singleElt (m + 1) (n + 1) g.a g.b ha hb (by omega) := by
  obtain ⟨m₀, hm₀⟩ :=
    exists_far_threshold (utIndices g.k.1.val ∪ utIndices (utInv g.k.1.val)) g.a g.b ha hb
  refine' ⟨m₀, _, _⟩
  · apply extraction_from_shift N hN g hg ha hb m₀
    intro m n hmn hm
    apply conj_singleElt_shift
    all_goals generalize_proofs at *
    · grind +locals
    · simp_all +decide [utIndices]
      grind +ring
    · simp_all +decide [utIndices]
      grind
    · grind +locals
  · intro m n hmn hm₀m
    apply conj_singleElt_shift g m n ha hb hmn
    · unfold utIndices at hm₀
      simp_all +decide [Finset.mem_union, Finset.mem_image]
      grind
    · grind +locals
    · intro pq hpq
      constructor <;> intro h <;> have := hm₀ (m + 1) (by linarith) <;> simp_all +decide [utIndices]
      grind +suggestions
    · unfold utIndices at hm₀
      simp_all +decide [Finset.mem_union, Finset.mem_image]
      grind +qlia

/-! ## matMul of single (Kronecker delta) entries -/

/-- Matrix product of two matching single entries: `e_{p,k}(a) · e_{k,q}(b) = e_{p,q}(a·b)`. -/
lemma matMul_single_match (p k q : ℤ × ℤ) (a b : ℤ) :
    matMul (Finsupp.single (p, k) a) (Finsupp.single (k, q) b) = Finsupp.single (p, q) (a * b) := by
  ext ⟨x, y⟩
  simp [matMul, Finsupp.sum_single_index, Finsupp.single_apply]

/-- Matrix product of two non-matching single entries (middle indices differ) is zero. -/
lemma matMul_single_ne (p₁ k₁ p₂ k₂ : ℤ × ℤ) (a b : ℤ) (h : k₁ ≠ p₂) :
    matMul (Finsupp.single (p₁, k₁) a) (Finsupp.single (p₂, k₂) b) = 0 := by
  ext ⟨x, y⟩
  simp [matMul, Finsupp.sum_single_index, h]

/-- The unipotent inverse of a single entry is its negation: `utInv (e_{p,q}(a)) = -e_{p,q}(a)`
(higher matrix powers vanish). -/
lemma utInv_single' (p q : ℤ × ℤ) (a : ℤ) :
    utInv (Finsupp.single (p, q) a) = -Finsupp.single (p, q) a := by
  unfold utInv
  by_cases ha : a = 0 <;> simp [ha, Finsupp.support_single_ne_zero, matPow]

/-! ## Commutator of single entries: [e_{p,k}, e_{k,q}] = e_{p,q} -/

/-- The `utMul`-commutator of two matching single entries: `⁅e_{p,k}(a), e_{k,q}(b)⁆ = e_{p,q}(a·b)`
when `p, k, q` are pairwise distinct. The basic relation generating combined entries. -/
lemma ut_commutator_single (p k q : ℤ × ℤ) (a b : ℤ) (hpk : k ≠ p) (hkq : q ≠ k) (hpq : q ≠ p) :
    utMul
        (utMul (utMul (Finsupp.single (p, k) a) (Finsupp.single (k, q) b))
          (utInv (Finsupp.single (p, k) a)))
        (utInv (Finsupp.single (k, q) b)) =
      Finsupp.single (p, q) (a * b) := by
  unfold utMul
  simp +decide [matMul_add_left, matMul_single_match, utInv_single']
  unfold matMul
  simp +decide
  simp +decide [Finsupp.sum, Finsupp.single_apply]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp +decide [ha, hb, Finsupp.support_single_ne_zero] at *
  · grind +splitImp
  · aesop
  · rw [Finset.sum_eq_zero] <;> simp +decide [*, Finsupp.single_apply, Finsupp.mul_apply]
    rw [Finset.sum_eq_zero] <;> simp +decide
    · abel1
    · grind +ring

/-! ## Finding elements -/

/-- If a subgroup `N` is contained in neither `M₁` nor `M₂`, it contains an element with both
`a ≠ 0` and `b ≠ 0` (built from one element with `b ≠ 0` and one with `a ≠ 0`). -/
lemma exists_ab_nonzero (N : Subgroup MyG) (hNM₁ : ¬(N ≤ M₁)) (hNM₂ : ¬(N ≤ M₂)) :
    ∃ g ∈ N, (g : MyG).a ≠ 0 ∧ (g : MyG).b ≠ 0 := by
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ ∈ N, g₁.b ≠ 0 := by
    contrapose! hNM₁
    aesop
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ ∈ N, g₂.a ≠ 0 := by
    contrapose! hNM₂
    aesop
  have h_elements : g₂ ∈ N ∧ g₂ * g₁ ∈ N ∧ g₂ ^ 2 * g₁ ∈ N :=
    ⟨hg₂.1, N.mul_mem hg₂.1 hg₁.1, N.mul_mem (N.pow_mem hg₂.1 2) hg₁.1⟩
  by_cases h1 : g₂.b ≠ 0
  · exact ⟨g₂, hg₂.1, hg₂.2, h1⟩
  · push_neg at h1
    by_cases h2 : (g₂ * g₁).a ≠ 0
    · exact ⟨g₂ * g₁, h_elements.2.1, h2, by
          simp [MyG.mul_b, h1]
          exact hg₁.2⟩
    · push_neg at h2
      simp [MyG.mul_a] at h2
      exact ⟨g₂ ^ 2 * g₁, h_elements.2.2, by
          simp [MyG.mul_a, sq]
          omega, by
          simp [MyG.mul_b, sq, h1]
          exact hg₁.2⟩

/-- Strengthening of `exists_ab_nonzero`: such an `N` contains an element with `a > 0` and `b ≠ 0`
(replace `g` by `g⁻¹` if needed). This is the element fed into the non-solvability engine. -/
lemma exists_a_pos_b_ne (N : Subgroup MyG) (hNM₁ : ¬(N ≤ M₁)) (hNM₂ : ¬(N ≤ M₂)) :
    ∃ g ∈ N, 0 < (g : MyG).a ∧ (g : MyG).b ≠ 0 := by
  obtain ⟨g, hgN, hg⟩ : ∃ g ∈ N, g.a ≠ 0 ∧ g.b ≠ 0 := exists_ab_nonzero N hNM₁ hNM₂
  cases lt_or_gt_of_ne hg.1 <;> [exact ⟨g⁻¹, N.inv_mem hgN, by aesop⟩; exact ⟨g, hgN, by aesop⟩]

/-- `matMul (e_{p,q}(c)) g = 0` when the index `q` matches no first index of `g`. -/
lemma matMul_single_left_zero (p q : ℤ × ℤ) (c : ℤ) (g : UTBase) (hq : ∀ pq ∈ g.support, q ≠ pq.1) :
    matMul (Finsupp.single (p, q) c) g = 0 := by
  ext ⟨x, y⟩
  simp [matMul]
  rw [Finsupp.sum]
  exact Finset.sum_eq_zero fun pq hpq ↦ if_neg (hq pq hpq) |> fun h ↦ h.symm ▸ rfl

/-- `matMul g (e_{p,q}(c)) = 0` when the index `p` matches no second index of `g`. -/
lemma matMul_single_right_zero (p q : ℤ × ℤ) (c : ℤ) (g : UTBase)
    (hp : ∀ pq ∈ g.support, p ≠ pq.2) : matMul g (Finsupp.single (p, q) c) = 0 :=
  Finset.sum_eq_zero fun pq hpq ↦ by
    specialize hp pq
    aesop

/-- **Non-solvability engine (case `b > 0`).** If conjugation by `g` shifts single-entry generators
beyond `m₀` by one, then the subgroup generated by `g` and the gap-`2` generator
`singleElt m₀ (m₀+2)` is **not** solvable. The reason: at the `k`-th level of the derived series one
finds the single entry `e_{m₀, m₀ + 2^(k+1)}`, whose index gap doubles at every step (via
`ut_commutator_single` and conjugation by powers of `g`); since these are all nonzero, no derived
subgroup is trivial. -/
lemma closure_not_solvable_of_shift (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (g : MyG) (m₀ : ℤ)
    (hshift :
      ∀ (m n : ℤ) (hmn : m < n),
        m₀ ≤ m →
          g * singleElt m n a b ha hb hmn * g⁻¹ = singleElt (m + 1) (n + 1) a b ha hb (by omega)) :
    ¬IsSolvable (↑(Subgroup.closure ({g, singleElt m₀ (m₀ + 2) a b ha hb (by omega)} : Set MyG))) := by
  intro h_solvable
  obtain ⟨n, hn⟩ :
    ∃ n,
      derivedSeries (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)}) n = ⊥ := by
    obtain ⟨n, hn⟩ := h_solvable
    use n
  have h_ind :
    ∀ k ≤ n,
      singleElt m₀ (m₀ + 2 ^ (k + 1)) a b ha hb
          (by linarith [Nat.one_le_pow (k + 1) 2 zero_lt_two]) ∈
        Subgroup.map
          (Subgroup.subtype (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)}))
          (derivedSeries (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)}) k) := by
    intro k hk
    induction' k with k ih
    · simp +zetaDelta at *
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · obtain ⟨x, hx⟩ := ih (Nat.le_of_succ_le hk)
      have h_comm :
        singleElt m₀ (m₀ + 2 ^ (k + 2)) a b ha hb
            (by linarith [Nat.one_le_pow (k + 2) 2 zero_lt_two]) =
          x.val * (g ^ (2 ^ (k + 1)) * x.val * (g⁻¹) ^ (2 ^ (k + 1))) * x.val⁻¹ *
            (g ^ (2 ^ (k + 1)) * x.val * (g⁻¹) ^ (2 ^ (k + 1)))⁻¹ := by
        have h_comm :
          ∀ j : ℕ,
            g ^ j * x.val * (g⁻¹) ^ j =
              singleElt (m₀ + j) (m₀ + j + 2 ^ (k + 1)) a b ha hb
                (by linarith [Nat.one_le_pow (k + 1) 2 zero_lt_two]) := by
          intro j
          induction j <;> simp_all +decide [pow_succ', mul_assoc]
          rename_i n ih
          convert congr_arg (fun x ↦ g * x * g⁻¹) ih using 1 <;> group
          convert hshift (m₀ + n) (m₀ + n + 2 ^ k * 2) (by linarith [pow_pos (zero_lt_two' ℤ) k])
                (by linarith) |>
              Eq.symm using 1
          ring_nf
          norm_num [mul_assoc]
        rw [h_comm]
        rw [show
            (x : MyG) =
              singleElt m₀ (m₀ + 2 ^ (k + 1)) a b ha hb
                (by linarith [Nat.one_le_pow (k + 1) 2 zero_lt_two])
            from hx.2]
        convert singleElt_comm m₀ (m₀ + 2 ^ (k + 1)) (m₀ + 2 ^ (k + 1) + 2 ^ (k + 1)) a b ha hb
              (by linarith [pow_pos (zero_lt_two' ℤ) (k + 1)])
              (by linarith [pow_pos (zero_lt_two' ℤ) (k + 1)]) |>
            Eq.symm using 1
        ring_nf
      have h_comm_mem :
        (g ^ (2 ^ (k + 1)) * x.val * (g⁻¹) ^ (2 ^ (k + 1))) ∈
          Subgroup.map
            (Subgroup.subtype (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)}))
            (derivedSeries (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)})
              k) := by
        have h_comm_mem :
          ∀
            y ∈
              Subgroup.map
                (Subgroup.subtype
                  (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)}))
                (derivedSeries (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)})
                  k),
            g ^ (2 ^ (k + 1)) * y * (g⁻¹) ^ (2 ^ (k + 1)) ∈
              Subgroup.map
                (Subgroup.subtype
                  (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)}))
                (derivedSeries (Subgroup.closure {g, singleElt m₀ (m₀ + 2) a b ha hb (by linarith)})
                  k) := by
          intro y hy
          obtain ⟨z, hz⟩ := hy
          use (⟨g, Subgroup.subset_closure (Set.mem_insert _ _)⟩ ^ 2 ^ (k + 1)) * z *
              (⟨g, Subgroup.subset_closure (Set.mem_insert _ _)⟩⁻¹ ^ 2 ^ (k + 1))
          simp +decide [← hz.2]
          exact Subgroup.Normal.mem_comm inferInstance (by simpa using hz.1)
        exact h_comm_mem _ ⟨x, hx.1, rfl⟩
      obtain ⟨y, hy⟩ := h_comm_mem
      use x * y * x⁻¹ * y⁻¹
      simp_all +decide [Subgroup.mem_map]
      exact Subgroup.commutator_mem_commutator hx.1 hy.1
  specialize h_ind n le_rfl
  simp_all +decide
  exact absurd h_ind
      (singleElt_ne_one _ _ _ _ ha hb (by linarith [Nat.one_le_pow (n + 1) 2 zero_lt_two]))

/-- A normal subgroup containing an element `g` with `a > 0` and `b > 0` is not locally solvable:
it contains the finitely generated non-solvable subgroup of `closure_not_solvable_of_shift`. -/
lemma not_locally_solvable_of_ab_pos (N : Subgroup MyG) (hN : N.Normal) (g : MyG) (hg : g ∈ N)
    (ha : 0 < g.a) (hb : 0 < g.b) : ¬IsLocallySolvable N := by
  intro hLS
  obtain ⟨m₀, hm₀, hshift⟩ := singleElt_in_N_and_shift N hN g hg ha hb
  set e := singleElt m₀ (m₀ + 2) g.a g.b ha hb (by omega)
  set H := Subgroup.closure ({g, e} : Set MyG) with hH_def
  have hH_le_N : H ≤ N := sInf_le (Set.insert_subset_iff.mpr ⟨hg, Set.singleton_subset_iff.mpr hm₀⟩)
  have hH_fg : H.FG := by
    have h_finite : Set.Finite {g, e} := Set.toFinite {g, e}
    generalize_proofs at *
    exact ⟨h_finite.toFinset, by aesop⟩
  have hH_not_solvable : ¬IsSolvable H := by
    convert closure_not_solvable_of_shift g.a g.b ha hb g m₀ hshift using 1
  contrapose! hH_not_solvable
  obtain ⟨K, hK⟩ := hH_fg
  have := hLS (Subgroup.comap N.subtype H) ?_
  · have h_iso : H ≃* Subgroup.comap N.subtype H := by
      refine'
          {
            Equiv.ofBijective (fun x ↦ ⟨⟨x, hH_le_N x.2⟩, x.2⟩)
              ⟨fun x y hxy ↦ _, fun x ↦ _⟩ with .. } <;>
        aesop
    obtain ⟨n, hn⟩ := this
    use n
    convert congr_arg (fun s ↦ s.map h_iso.symm.toMonoidHom) hn using 1
    · refine' Nat.recOn n _ _ <;> simp_all +decide [derivedSeries]
      simp +decide [Subgroup.map_commutator]
    · simp +decide [Subgroup.map_bot]
  · refine' ⟨K.preimage (fun x : ↥N ↦ x.val) _, _⟩
    exact fun x hx y hy hxy ↦ Subtype.ext hxy
    simp +decide [← hK, Subgroup.closure]
    ext
    simp [Subgroup.mem_subgroupOf]
    constructor <;> intro h p hp
    · exact h (p.subgroupOf N) (fun x hx ↦ hp hx) |> fun hx ↦ by simpa using hx
    · convert h (p.map N.subtype) _
      · simp +decide [Subgroup.mem_map]
      · exact fun x hx ↦ ⟨⟨x, hH_le_N <| hK.symm ▸ Subgroup.subset_closure hx⟩, hp hx, rfl⟩

-- For b < 0: The argument is completely symmetric using UT₂ entries instead of UT₁.
-- We define singleEltAnti for UT₂ and prove the same chain of lemmas.

/-- Construct a `MyG` kernel element `((0, f), 0, 0)` from a valid `UT₂` (anti-triangular) entry. -/
noncomputable def mkUT2 (f : UTBase) (hf : isValidAnti f) : MyG :=
  ((⟨0, zero_validProd⟩, ⟨f, hf⟩), 0, 0)

/-- The `singleElt` analogue for `UT₂` (anti order, `a > 0`, `b < 0`): the single-entry generator at
positions `(m·a, m·b) → (n·a, n·b)`. -/
noncomputable def singleEltAnti (m n a b : ℤ) (ha : 0 < a) (hb : b < 0) (hmn : m < n) : MyG :=
  mkUT2 (Finsupp.single ((m * a, m * b), (n * a, n * b)) 1) (by
      intro pq hpq
      simp [Finsupp.support_single_ne_zero] at hpq
      subst hpq
      exact ⟨by nlinarith, by nlinarith⟩)

/-- An anti single-entry generator is never the identity. -/
lemma singleEltAnti_ne_one (m n a b : ℤ) (ha : 0 < a) (hb : b < 0) (hmn : m < n) :
    singleEltAnti m n a b ha hb hmn ≠ 1 := by
  unfold singleEltAnti
  simp +decide
  erw [Prod.mk_inj]
  norm_num
  repeat
    erw [Subtype.mk_eq_mk]
    norm_num

/-- Multiplication of `mkUT2` elements reduces to `utMul` of their `UT₂` data. -/
lemma mkUT2_mul (f₁ f₂ : UTBase) (hf₁ : isValidAnti f₁) (hf₂ : isValidAnti f₂) :
    mkUT2 f₁ hf₁ * mkUT2 f₂ hf₂ = mkUT2 (utMul f₁ f₂) (utMul_isValidAnti hf₁ hf₂) := by
  unfold mkUT2
  simp +decide [utMul]
  erw [Prod.mk_inj]
  simp +decide [UTBase, UT₁, UT₂]
  erw [phiAction_zero]
  simp +decide [MyG.k, MyG.a, MyG.b]
  exact Subtype.ext (utMul_eq_add_matMul f₁ f₂)

/-- The inverse of a `mkUT2` element reduces to `utInv` of its `UT₂` data. -/
lemma mkUT2_inv (f : UTBase) (hf : isValidAnti f) :
    (mkUT2 f hf)⁻¹ = mkUT2 (utInv f) (utInv_isValidAnti hf) := by
  generalize_proofs at *
  unfold mkUT2
  erw [Prod.mk_inj]
  simp +decide
  erw [phiAction_zero]
  aesop

/-- `mkUT2` is injective: two `mkUT2` elements are equal iff their underlying values are. -/
lemma mkUT2_eq_iff (f₁ f₂ : UTBase) (hf₁ : isValidAnti f₁) (hf₂ : isValidAnti f₂) :
    mkUT2 f₁ hf₁ = mkUT2 f₂ hf₂ ↔ f₁ = f₂ := by grind +locals

/-- Commutator identity for anti single entries: `⁅e_{m,k}, e_{k,n}⁆ = e_{m,n}`; the `UT₂` analogue
of `singleElt_comm`. -/
lemma singleEltAnti_comm (m k n a b : ℤ) (ha : 0 < a) (hb : b < 0) (hmk : m < k) (hkn : k < n) :
    singleEltAnti m k a b ha hb hmk * singleEltAnti k n a b ha hb hkn *
          (singleEltAnti m k a b ha hb hmk)⁻¹ *
        (singleEltAnti k n a b ha hb hkn)⁻¹ =
      singleEltAnti m n a b ha hb (lt_trans hmk hkn) := by
  unfold singleEltAnti
  simp +decide [mkUT2_mul, mkUT2_inv, mkUT2_eq_iff]
  convert ut_commutator_single (m * a, m * b) (k * a, k * b) (n * a, n * b) 1 1 _ _ _ using 1 <;>
    norm_num
  · grind
  · grind +ring
  · grind

/-! ## UT₂ infrastructure for extraction (anti case, b < 0) -/

/-- `utInv f` is a right inverse of `f` under `utMul` for anti-triangular valid elements. -/
lemma utMul_utInv_anti (f : UTBase) (hf : isValidAnti f) : utMul f (utInv f) = 0 :=
  congr_arg Subtype.val (@mul_inv_cancel UT₂ _ ⟨f, hf⟩)

/-- Conjugating a single entry by a valid `UT₂` element with disjoint support leaves it unchanged;
the anti-order analogue of `ut1_conj_single_disjoint`. -/
lemma ut2_conj_single_disjoint (f : UTBase) (hf : isValidAnti f) (p q : ℤ × ℤ)
    (hp : ∀ pq ∈ f.support, p ≠ pq.2) (hq' : ∀ pq ∈ (utInv f).support, q ≠ pq.1) :
    utMul (utMul f (Finsupp.single (p, q) 1)) (utInv f) = Finsupp.single (p, q) 1 := by
  have h_inner_zero : matMul f (Finsupp.single (p, q) 1) = 0 := matMul_single_right_zero p q 1 f hp
  have h_sum_zero : matMul (fun₀ | (p, q) => 1) (utInv f) = 0 :=
    matMul_single_left_zero p q 1 (utInv f) hq'
  unfold utMul at *
  simp_all +decide [matMul_add_left]
  convert congr_arg (fun x ↦ x + Finsupp.single (p, q) 1) (utMul_utInv_anti f hf) using 1
  abel_nf
  · unfold utMul
    abel
  · norm_num

/-- For `a > 0`, `b < 0` and any finite set `S`, the points `m·(a, b)` eventually avoid `S`; the
anti-order analogue of `exists_far_threshold`. -/
lemma exists_far_threshold_neg (S : Finset (ℤ × ℤ)) (a b : ℤ) (ha : 0 < a) (hb : b < 0) :
    ∃ m₀ : ℕ, ∀ m : ℤ, (m₀ : ℤ) ≤ m → (m * a, m * b) ∉ S := by
  obtain ⟨M, hM⟩ :=
    exists_far_threshold (S.image (fun p : ℤ × ℤ ↦ (p.1, -p.2))) a (-b) ha (neg_pos.mpr hb)
  exact ⟨M, fun m hm h ↦ hM m hm <| Finset.mem_image.mpr ⟨_, h, by simp +decide⟩⟩

/-- When the shifted target indices avoid the support of `g.k.2` and its inverse, conjugating
`singleEltAnti m n` by `g` shifts indices by one; the anti-order analogue of `conj_singleElt_shift`. -/
lemma conj_singleEltAnti_shift (g : MyG) (m n : ℤ) (ha : 0 < g.a) (hb : g.b < 0) (hmn : m < n)
    (h1 :
      ∀ pq ∈ g.k.2.val.support,
        ((m + 1) * g.a, (m + 1) * g.b) ≠ pq.2 ∧ ((n + 1) * g.a, (n + 1) * g.b) ≠ pq.1)
    (_h2 :
      ∀ pq ∈ g.k.2.val.support,
        ((m + 1) * g.a, (m + 1) * g.b) ≠ pq.1 ∧ ((n + 1) * g.a, (n + 1) * g.b) ≠ pq.2)
    (h3 :
      ∀ pq ∈ (utInv g.k.2.val).support,
        ((m + 1) * g.a, (m + 1) * g.b) ≠ pq.2 ∧ ((n + 1) * g.a, (n + 1) * g.b) ≠ pq.1)
    (_h4 :
      ∀ pq ∈ (utInv g.k.2.val).support,
        ((m + 1) * g.a, (m + 1) * g.b) ≠ pq.1 ∧ ((n + 1) * g.a, (n + 1) * g.b) ≠ pq.2) :
    g * singleEltAnti m n g.a g.b ha hb hmn * g⁻¹ =
      singleEltAnti (m + 1) (n + 1) g.a g.b ha hb (by omega) := by
  unfold singleEltAnti mkUT2
  simp +decide [kernel_conj_formula, phiAction]
  apply Prod.ext
  apply Prod.ext
  apply Subtype.ext
  simp +decide
  · erw [mul_one]
    aesop
  · ext ⟨p, q⟩
    simp +decide [shiftUTBase₁, shiftUTBase₂, Finsupp.single_apply]
    ring_nf
    convert ut2_conj_single_disjoint _ _ _ _ _ _ |> fun h ↦ congr_arg (fun f ↦ f (p, q)) h using 1
    grind
    · exact g.k.2.2
    · grind
    · grind
  · rfl

/-- The coboundary `e_{p,k} - e_{k,q} - e_{p,q}` is anti-triangularity valid (for `a > 0`, `b < 0`). -/
lemma coboundary_isValidAnti (m a b : ℤ) (ha : 0 < a) (hb : b < 0) :
    isValidAnti
      (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 -
          Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 -
        Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1) := by
  intro pq hpq
  simp +decide [Finsupp.sub_apply, Finsupp.single_apply] at hpq ⊢
  grind

/-- The negation of a single anti-triangular entry is anti-triangularity valid. -/
lemma neg_single_isValidAnti (p q : ℤ × ℤ) (hp : p.1 < q.1) (hq : q.2 < p.2) :
    isValidAnti (-(Finsupp.single (p, q) 1)) := by
  intro pq hpq
  simp [Finsupp.support_neg, Finsupp.support_single_ne_zero] at hpq
  subst hpq
  exact ⟨hp, hq⟩

/-- A single anti-triangular entry `e_{p,q}` (with `p.1 < q.1` and `q.2 < p.2`) is valid. -/
lemma single_validAnti (p q : ℤ × ℤ) (hp : p.1 < q.1) (hq : q.2 < p.2) :
    isValidAnti (Finsupp.single (p, q) 1) := by
  intro pq hpq
  simp [Finsupp.support_single_ne_zero] at hpq
  subst hpq
  exact ⟨hp, hq⟩

/-- Group commutator of two `mkUT2` elements is `mkUT2` of the `utMul`-commutator. -/
lemma mkUT2_commutator (f₁ f₂ : UTBase) (hf₁ : isValidAnti f₁) (hf₂ : isValidAnti f₂) :
    mkUT2 f₁ hf₁ * mkUT2 f₂ hf₂ * (mkUT2 f₁ hf₁)⁻¹ * (mkUT2 f₂ hf₂)⁻¹ =
      mkUT2 (utMul (utMul (utMul f₁ f₂) (utInv f₁)) (utInv f₂))
        (utMul_isValidAnti (utMul_isValidAnti (utMul_isValidAnti hf₁ hf₂) (utInv_isValidAnti hf₁))
          (utInv_isValidAnti hf₂)) :=
  by simp [mkUT2_mul, mkUT2_inv]

/-- Product of adjacent anti single-entry generators `e_{m,m+1} · (e_{m+1,m+2})⁻¹` equals `mkUT2` of
the coboundary; the anti-order analogue of `singleElt_mul_inv_singleElt`. -/
lemma singleEltAnti_mul_inv_singleEltAnti (m a b : ℤ) (ha : 0 < a) (hb : b < 0) :
    singleEltAnti m (m + 1) a b ha hb (by omega) *
        (singleEltAnti (m + 1) (m + 2) a b ha hb (by omega))⁻¹ =
      mkUT2
        (Finsupp.single ((m * a, m * b), ((m + 1) * a, (m + 1) * b)) 1 -
            Finsupp.single (((m + 1) * a, (m + 1) * b), ((m + 2) * a, (m + 2) * b)) 1 -
          Finsupp.single ((m * a, m * b), ((m + 2) * a, (m + 2) * b)) 1)
        (coboundary_isValidAnti m a b ha hb) := by
  simp [singleEltAnti] at *
  rw [mkUT2_inv, mkUT2_mul]
  apply (mkUT2_eq_iff _ _ _ _).mpr
  rw [utMul_eq_add_matMul]
  rw [utInv_single', sub_eq_add_neg, sub_eq_add_neg]
  simp +decide [matMul]
  rw [Finsupp.sum_neg_index]
  norm_num
  · ext
    simp [Finsupp.single_apply]
  · aesop

/-- The `UT₂`-commutator of `f = e_{m,m+1}` with the coboundary equals `-e_{m,m+2}`; the anti-order
analogue of `double_comm_extraction`. -/
lemma double_comm_extraction_neg (m a b : ℤ) (ha : 0 < a) (hb : b < 0) :
    let p := (m * a, m * b)
    let k := ((m + 1) * a, (m + 1) * b)
    let q := ((m + 2) * a, (m + 2) * b)
    let f := Finsupp.single (p, k) 1
    let c := Finsupp.single (p, k) 1 - Finsupp.single (k, q) 1 - Finsupp.single (p, q) 1
    utMul (utMul (utMul f c) (utInv f)) (utInv c) = -(Finsupp.single (p, q) 1) := by
  have :
    ∀ p q : ℤ × ℤ, p ≠ q → ∀ a : ℤ, utInv (Finsupp.single (p, q) a) = -Finsupp.single (p, q) a := by
    intros p q hpq a
    exact utInv_single' p q a
  unfold utMul
  simp +decide [matMul_add_left, matMul_neg_left, matMul_neg_right, matMul_sub_left,
    matMul_sub_right, this, ha.ne', hb.ne]
  rw [utInv_coboundary]
  ring_nf
  · simp +decide [matMul_single_match, matMul_single_ne, matMul_single_right_zero, matMul_add_right,
      matMul_neg_right, ha.ne', hb.ne]
    abel1
  · grind
  · grind
  · grind +splitImp

/-- `mkUT2` of a negated single entry is the inverse of `mkUT2` of the entry. -/
lemma mkUT2_neg_single_eq_inv (p q : ℤ × ℤ) (hp : p.1 < q.1) (hq : q.2 < p.2) :
    mkUT2 (-(Finsupp.single (p, q) 1)) (neg_single_isValidAnti p q hp hq) =
      (mkUT2 (Finsupp.single (p, q) 1) (single_validAnti p q hp hq))⁻¹ := by
  rw [mkUT2_inv, mkUT2_eq_iff]
  exact (utInv_single' p q 1).symm

/-- Iterated commutator on anti single entries yields the inverse of the gap-`2` generator; the
anti-order analogue of `double_comm_singleElt`. -/
lemma double_comm_singleEltAnti (m a b : ℤ) (ha : 0 < a) (hb : b < 0) :
    let h₁ := singleEltAnti m (m + 1) a b ha hb (by omega)
    let c₁ := h₁ * (singleEltAnti (m + 1) (m + 2) a b ha hb (by omega))⁻¹
    h₁ * c₁ * h₁⁻¹ * c₁⁻¹ = (singleEltAnti m (m + 2) a b ha hb (by omega))⁻¹ := by
  refine' mkUT2_commutator _ _ _ _ |> Eq.trans <| _
  convert mkUT2_neg_single_eq_inv _ _ _ _ using 1
  convert double_comm_extraction_neg m a b ha hb using 1
  all_goals
    norm_num
    try nlinarith
  rw [mkUT2_eq_iff]
  convert Iff.rfl using 3
  · congr! 2
    convert singleEltAnti_mul_inv_singleEltAnti m a b ha hb |> Eq.symm using 1
    convert Iff.rfl using 1
    convert mkUT2_eq_iff _ _ _ _ using 2
  · congr! 1
    convert singleEltAnti_mul_inv_singleEltAnti m a b ha hb |> Eq.symm using 1
    convert Iff.rfl using 1
    convert mkUT2_eq_iff _ _ _ _ using 2

/-- If `g ∈ N` (normal) with `a > 0`, `b < 0` and conjugation by `g` shifts anti single entries
beyond `m₀`, then the gap-`2` generator `singleEltAnti m₀ (m₀+2)` lies in `N`; the anti-order
analogue of `extraction_from_shift`. -/
lemma extraction_from_shift_anti (N : Subgroup MyG) (hN : N.Normal) (g : MyG) (hg : g ∈ N)
    (ha : 0 < g.a) (hb : g.b < 0) (m₀ : ℤ)
    (hshift :
      ∀ (m n : ℤ) (hmn : m < n),
        m₀ ≤ m →
          g * singleEltAnti m n g.a g.b ha hb hmn * g⁻¹ =
            singleEltAnti (m + 1) (n + 1) g.a g.b ha hb (by omega)) :
    singleEltAnti m₀ (m₀ + 2) g.a g.b ha hb (by omega) ∈ N := by
  set c₁ := singleEltAnti m₀ (m₀ + 1) g.a g.b ha hb (by omega)
  set c₂ := c₁ * g * c₁⁻¹ * g⁻¹
  have hc₂_eq : c₂ = c₁ * (singleEltAnti (m₀ + 1) (m₀ + 2) g.a g.b ha hb (by omega))⁻¹ := by
    show c₁ * g * c₁⁻¹ * g⁻¹ = c₁ * (singleEltAnti (m₀ + 1) (m₀ + 2) g.a g.b ha hb (by omega))⁻¹
    have h_c₂ : g * c₁⁻¹ * g⁻¹ = (singleEltAnti (m₀ + 1) (m₀ + 2) g.a g.b ha hb (by omega))⁻¹ := by
      convert congr_arg Inv.inv (hshift m₀ (m₀ + 1) (by omega) (by omega)) using 1
      group
      · grind +splitIndPred
      · ring_nf
    simp +decide only [mul_assoc, ← h_c₂]
  convert N.inv_mem
      (N.mul_mem (hN.conj_mem _ (show c₂ ∈ N from ?_) c₁) (N.inv_mem (show c₂ ∈ N from ?_))) using 1
  · rw [hc₂_eq, double_comm_singleEltAnti]
    norm_num
  · convert N.mul_mem (hN.conj_mem _ hg c₁) (N.inv_mem hg) using 1
  · convert N.mul_mem (hN.conj_mem _ hg c₁) (N.inv_mem hg) using 1

/-- For `g ∈ N` (normal) with `a > 0`, `b < 0`, there is a threshold `m₀` such that `N` contains the
gap-`2` anti generator and conjugation by `g` shifts every anti single entry beyond `m₀`; the
anti-order analogue of `singleElt_in_N_and_shift`. -/
lemma singleEltAnti_in_N_and_shift (N : Subgroup MyG) (hN : N.Normal) (g : MyG) (hg : g ∈ N)
    (ha : 0 < g.a) (hb : g.b < 0) :
    ∃ m₀ : ℤ,
      singleEltAnti m₀ (m₀ + 2) g.a g.b ha hb (by omega) ∈ N ∧
        ∀ (m n : ℤ) (hmn : m < n),
          m₀ ≤ m →
            g * singleEltAnti m n g.a g.b ha hb hmn * g⁻¹ =
              singleEltAnti (m + 1) (n + 1) g.a g.b ha hb (by omega) := by
  obtain ⟨m₀, hm₀⟩ :=
    exists_far_threshold_neg (utIndices g.k.2.val ∪ utIndices (utInv g.k.2.val)) g.a g.b ha hb
  refine' ⟨m₀, _, _⟩
  · apply extraction_from_shift_anti N hN g hg ha hb m₀
    intro m n hmn hm
    apply conj_singleEltAnti_shift g m n ha hb hmn
    generalize_proofs at *
    · intro pq hpq
      constructor <;> intro h <;> have := hm₀ (m + 1) (by linarith) <;> simp_all +decide [utIndices]
      grind +suggestions
    · simp_all +decide [utIndices]
      grind +locals
    · intro pq hpq
      constructor <;> intro h <;> have := hm₀ (m + 1) (by linarith) <;> simp_all +decide [utIndices]
      specialize hm₀ (n + 1) (by linarith)
      aesop
    · intro pq hpq
      constructor <;> intro h <;> have := hm₀ (m + 1) (by linarith) <;> simp_all +decide [utIndices]
      grind +suggestions
  · intro m n hmn hm
    apply conj_singleEltAnti_shift g m n ha hb hmn
    all_goals generalize_proofs at *
    · unfold utIndices at hm₀
      simp_all +decide [Finset.mem_union, Finset.mem_image]
      grind +locals
    · simp_all +decide [utIndices]
      grind +locals
    · simp_all +decide [utIndices]
      grind
    · intro pq hpq
      constructor <;> intro h <;> have := hm₀ (m + 1) (by linarith) <;> simp_all +decide [utIndices]
      specialize hm₀ (n + 1) (by linarith)
      aesop

/-- **Non-solvability engine (case `b < 0`).** The subgroup generated by `g` and the gap-`2` anti
generator is not solvable, by the same gap-doubling argument as `closure_not_solvable_of_shift`. -/
lemma closure_not_solvable_of_shift_anti (a b : ℤ) (ha : 0 < a) (hb : b < 0) (g : MyG) (m₀ : ℤ)
    (hshift :
      ∀ (m n : ℤ) (hmn : m < n),
        m₀ ≤ m →
          g * singleEltAnti m n a b ha hb hmn * g⁻¹ =
            singleEltAnti (m + 1) (n + 1) a b ha hb (by omega)) :
    ¬IsSolvable
        (↑(Subgroup.closure ({g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by omega)} : Set MyG))) := by
  intro h_solvable
  obtain ⟨n, hn⟩ :
    ∃ n,
      derivedSeries (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)}) n =
        ⊥ := by
    obtain ⟨n, hn⟩ := h_solvable
    use n
  have h_ind :
    ∀ k ≤ n,
      singleEltAnti m₀ (m₀ + 2 ^ (k + 1)) a b ha hb
          (by linarith [Nat.one_le_pow (k + 1) 2 zero_lt_two]) ∈
        Subgroup.map
          (Subgroup.subtype
            (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)}))
          (derivedSeries (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)})
            k) := by
    intro k hk
    induction' k with k ih
    · simp +zetaDelta at *
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · obtain ⟨x, hx⟩ := ih (Nat.le_of_succ_le hk)
      have h_comm :
        singleEltAnti m₀ (m₀ + 2 ^ (k + 2)) a b ha hb
            (by linarith [Nat.one_le_pow (k + 2) 2 zero_lt_two]) =
          x.val * (g ^ (2 ^ (k + 1)) * x.val * (g⁻¹) ^ (2 ^ (k + 1))) * x.val⁻¹ *
            (g ^ (2 ^ (k + 1)) * x.val * (g⁻¹) ^ (2 ^ (k + 1)))⁻¹ := by
        have h_comm :
          ∀ j : ℕ,
            g ^ j * x.val * (g⁻¹) ^ j =
              singleEltAnti (m₀ + j) (m₀ + j + 2 ^ (k + 1)) a b ha hb
                (by linarith [Nat.one_le_pow (k + 1) 2 zero_lt_two]) := by
          intro j
          induction j <;> simp_all +decide [pow_succ', mul_assoc]
          rename_i n ih
          convert congr_arg (fun x ↦ g * x * g⁻¹) ih using 1 <;> group
          convert hshift (m₀ + n) (m₀ + n + 2 ^ k * 2) (by linarith [pow_pos (zero_lt_two' ℤ) k])
                (by linarith) |>
              Eq.symm using 1
          ring_nf
          norm_num [mul_assoc]
        rw [h_comm]
        rw [show
            (x : MyG) =
              singleEltAnti m₀ (m₀ + 2 ^ (k + 1)) a b ha hb
                (by linarith [Nat.one_le_pow (k + 1) 2 zero_lt_two])
            from hx.2]
        convert singleEltAnti_comm m₀ (m₀ + 2 ^ (k + 1)) (m₀ + 2 ^ (k + 1) + 2 ^ (k + 1)) a b ha hb
              (by linarith [pow_pos (zero_lt_two' ℤ) (k + 1)])
              (by linarith [pow_pos (zero_lt_two' ℤ) (k + 1)]) |>
            Eq.symm using 1
        ring_nf
      have h_comm_mem :
        (g ^ (2 ^ (k + 1)) * x.val * (g⁻¹) ^ (2 ^ (k + 1))) ∈
          Subgroup.map
            (Subgroup.subtype
              (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)}))
            (derivedSeries (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)})
              k) := by
        have h_comm_mem :
          ∀
            y ∈
              Subgroup.map
                (Subgroup.subtype
                  (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)}))
                (derivedSeries
                  (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)}) k),
            g ^ (2 ^ (k + 1)) * y * (g⁻¹) ^ (2 ^ (k + 1)) ∈
              Subgroup.map
                (Subgroup.subtype
                  (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)}))
                (derivedSeries
                  (Subgroup.closure {g, singleEltAnti m₀ (m₀ + 2) a b ha hb (by linarith)}) k) := by
          intro y hy
          obtain ⟨z, hz⟩ := hy
          use (⟨g, Subgroup.subset_closure (Set.mem_insert _ _)⟩ ^ 2 ^ (k + 1)) * z *
              (⟨g, Subgroup.subset_closure (Set.mem_insert _ _)⟩⁻¹ ^ 2 ^ (k + 1))
          simp +decide [← hz.2]
          exact Subgroup.Normal.mem_comm inferInstance (by simpa using hz.1)
        exact h_comm_mem _ ⟨x, hx.1, rfl⟩
      obtain ⟨y, hy⟩ := h_comm_mem
      use x * y * x⁻¹ * y⁻¹
      simp_all +decide [Subgroup.mem_map]
      exact Subgroup.commutator_mem_commutator hx.1 hy.1
  specialize h_ind n le_rfl
  simp_all +decide
  exact absurd h_ind
      (singleEltAnti_ne_one _ _ _ _ ha hb (by linarith [Nat.one_le_pow (n + 1) 2 zero_lt_two]))

/-- A normal subgroup containing an element with `a > 0` and `b < 0` is not locally solvable; the
anti-order analogue of `not_locally_solvable_of_ab_pos`. -/
lemma not_locally_solvable_of_ab_neg (N : Subgroup MyG) (hN : N.Normal) (g : MyG) (hg : g ∈ N)
    (ha : 0 < g.a) (hb : g.b < 0) : ¬IsLocallySolvable N := by
  intro hLS
  obtain ⟨m₀, hm₀, hshift⟩ := singleEltAnti_in_N_and_shift N hN g hg ha hb
  set e := singleEltAnti m₀ (m₀ + 2) g.a g.b ha hb (by omega)
  set H := Subgroup.closure ({g, e} : Set MyG) with hH_def
  have hH_le_N : H ≤ N := sInf_le (Set.insert_subset_iff.mpr ⟨hg, Set.singleton_subset_iff.mpr hm₀⟩)
  have hH_fg : H.FG := by
    have h_finite : Set.Finite {g, e} := Set.toFinite _
    exact ⟨h_finite.toFinset, by aesop⟩
  have hH_not_solvable : ¬IsSolvable H := by
    convert closure_not_solvable_of_shift_anti g.a g.b ha hb g m₀ hshift using 1
  contrapose! hH_not_solvable
  obtain ⟨K, hK⟩ := hH_fg
  have := hLS (Subgroup.comap N.subtype H) ?_
  · have h_iso : H ≃* Subgroup.comap N.subtype H := by
      refine'
          {
            Equiv.ofBijective (fun x ↦ ⟨⟨x, hH_le_N x.2⟩, x.2⟩)
              ⟨fun x y hxy ↦ _, fun x ↦ _⟩ with .. } <;>
        aesop
    obtain ⟨n, hn⟩ := this
    use n
    convert congr_arg (fun s ↦ s.map h_iso.symm.toMonoidHom) hn using 1
    · refine' Nat.recOn n _ _ <;> simp_all +decide [derivedSeries]
      simp +decide [Subgroup.map_commutator]
    · simp +decide [Subgroup.map_bot]
  · refine' ⟨K.preimage (fun x : ↑N ↦ x.val) _, _⟩
    exact fun x hx y hy hxy ↦ Subtype.ext hxy
    simp +decide [← hK, Subgroup.closure]
    ext
    simp [Subgroup.mem_subgroupOf]
    constructor <;> intro h p hp
    · exact h (p.subgroupOf N) (fun x hx ↦ hp hx) |> fun hx ↦ by simpa using hx
    · convert h (p.map N.subtype) _
      · simp +decide [Subgroup.mem_map]
      · exact fun x hx ↦ ⟨⟨x, hH_le_N <| hK.symm ▸ Subgroup.subset_closure hx⟩, hp hx, rfl⟩

/-- A normal subgroup containing an element with `a > 0` and `b ≠ 0` is not locally solvable; case
split on the sign of `b` combining the two `not_locally_solvable_of_ab_*` lemmas. -/
lemma not_locally_solvable_of_ab (N : Subgroup MyG) (hN : N.Normal) (g : MyG) (hg : g ∈ N)
    (ha : 0 < g.a) (hb : g.b ≠ 0) : ¬IsLocallySolvable N := by
  rcases lt_or_gt_of_ne hb with h | h
  · exact not_locally_solvable_of_ab_neg N hN g hg ha h
  · exact not_locally_solvable_of_ab_pos N hN g hg ha h

/-- **Classification.** Every normal locally solvable subgroup of `MyG` is contained in `M₁` or in
`M₂`: otherwise it contains an element with `a > 0`, `b ≠ 0`, contradicting local solvability. -/
lemma loc_solv_normal_le (N : Subgroup MyG) (hN : N.Normal) (hLS : IsLocallySolvable N) :
    N ≤ M₁ ∨ N ≤ M₂ := by
  by_contra h
  push_neg at h
  obtain ⟨hNM₁, hNM₂⟩ := h
  obtain ⟨g, hg, ha, hb⟩ := exists_a_pos_b_ne N hNM₁ hNM₂
  exact not_locally_solvable_of_ab N hN g hg ha hb hLS

/-- `M₁` is not contained in `M₂` (it contains an element with `a = 1 ≠ 0`). -/
lemma M₁_not_le_M₂ : ¬(M₁ ≤ M₂) := by
  intro h
  have h1 : ((1 : MyK), (1 : ℤ), (0 : ℤ)) ∈ M₁ := rfl
  have h2 := h h1
  change (1 : ℤ) = 0 at h2
  exact one_ne_zero h2

/-- `M₂` is not contained in `M₁` (it contains an element with `b = 1 ≠ 0`). -/
lemma M₂_not_le_M₁ : ¬(M₂ ≤ M₁) := by
  intro h
  have h1 : ((1 : MyK), (0 : ℤ), (1 : ℤ)) ∈ M₂ := rfl
  have h2 := h h1
  change (1 : ℤ) = 0 at h2
  exact one_ne_zero h2

/-- There exists a group with exactly two maximal locally solvable normal subgroups. -/
theorem main_theorem :
    ∃ (G : Type) (_ : Group G) (M₁ M₂ : Subgroup G),
      M₁ ≠ M₂ ∧
        IsMaxLocSolvNormal G M₁ ∧
          IsMaxLocSolvNormal G M₂ ∧ ∀ M : Subgroup G, IsMaxLocSolvNormal G M → M = M₁ ∨ M = M₂ := by
  refine ⟨MyG, inferInstance, M₁, M₂, ?_, ?_, ?_, ?_⟩
  · exact M₁_ne_M₂
  · refine ⟨M₁_normal, M₁_locally_solvable, ?_⟩
    intro N hN hLS hle
    rcases loc_solv_normal_le N hN hLS with h | h
    · exact le_antisymm h hle
    · exact absurd (le_trans hle h) M₁_not_le_M₂
  · refine ⟨M₂_normal, M₂_locally_solvable, ?_⟩
    intro N hN hLS hle
    rcases loc_solv_normal_le N hN hLS with h | h
    · exact absurd (le_trans hle h) M₂_not_le_M₁
    · exact le_antisymm h hle
  · intro M hM
    rcases loc_solv_normal_le M hM.1 hM.2.1 with h | h
    · left
      exact (hM.2.2 M₁ M₁_normal M₁_locally_solvable h).symm
    · right
      exact (hM.2.2 M₂ M₂_normal M₂_locally_solvable h).symm

#print axioms main_theorem

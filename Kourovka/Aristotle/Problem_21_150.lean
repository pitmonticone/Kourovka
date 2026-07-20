/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Kourovka Notebook Problem 21.150 (V.I. Zenkov)

Let `G` be an extension of a normal elementary abelian subgroup `A` by an elementary
abelian group `B ≅ G/A` such that `A` contains an element `a` with `C_B(a) = 1`.
Is it true that the rank of `Z(⟨a,B⟩) ∩ ⟨a,B⟩'` is at most the rank of `B`?

## Answer: **No.**

We exhibit a counterexample with `p = 3`, `B ≅ (ℤ/3ℤ)²`, `A ≅ (ℤ/3ℤ)⁶`.

The counterexample group is `G = A ⋊ B` where `B` acts on `A` via the truncated
polynomial representation: `A` corresponds to `𝔽₃[x,y]/(x³,y³,𝔪³)` where `𝔪 = (x,y)`,
and `B` acts by multiplication by `(1+x)` and `(1+y)`.

### Key computation (verified by `native_decide`)

- `Z(H) = ker(T₁) ∩ ker(T₂) = span{x², xy, y²}` has rank 3
- `H' = Im(T₁) + Im(T₂) = span{x, y, x², xy, y²}` has rank 5
- `Z(H) ∩ H' = span{x², xy, y²}` has rank `3 > 2 = rank(B)`

## Main result

`kourovka_21_150_is_false` : the conjecture of Problem 21.150 is false.
-/

open Classical Matrix Nat Subgroup

/-! ## Linear algebra: nilpotent action matrices -/

section LinearAlgebra

/-- Nilpotent action matrix for multiplication by `x` in `𝔽₃[x,y]/(x³,y³,𝔪³)`,
with respect to the basis `{1, x, y, x², xy, y²}`. -/
def T₁ : Matrix (Fin 6) (Fin 6) (ZMod 3) := !![
  0, 0, 0, 0, 0, 0;
  1, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 0, 0
]

/-- Nilpotent action matrix for multiplication by `y` in `𝔽₃[x,y]/(x³,y³,𝔪³)`,
with respect to the basis `{1, x, y, x², xy, y²}`. -/
def T₂ : Matrix (Fin 6) (Fin 6) (ZMod 3) := !![
  0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0;
  1, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0
]

/-- The generator element `a₀ = (1,0,0,0,0,0)`, corresponding to `1 ∈ 𝔽₃[x,y]/(x³,y³,𝔪³)`. -/
def a₀ : Fin 6 → ZMod 3 := ![1, 0, 0, 0, 0, 0]

/-- The basis vector `e₃ = x²` lies in `ker(T₁) ∩ ker(T₂)`. -/
theorem ker_e3 : T₁.mulVec ![0, 0, 0, 1, 0, 0] = 0 ∧ T₂.mulVec ![0, 0, 0, 1, 0, 0] = 0 :=
  ⟨by decide, by decide⟩

/-- The basis vector `e₄ = xy` lies in `ker(T₁) ∩ ker(T₂)`. -/
theorem ker_e4 : T₁.mulVec ![0, 0, 0, 0, 1, 0] = 0 ∧ T₂.mulVec ![0, 0, 0, 0, 1, 0] = 0 :=
  ⟨by decide, by decide⟩

/-- The basis vector `e₅ = y²` lies in `ker(T₁) ∩ ker(T₂)`. -/
theorem ker_e5 : T₁.mulVec ![0, 0, 0, 0, 0, 1] = 0 ∧ T₂.mulVec ![0, 0, 0, 0, 0, 1] = 0 :=
  ⟨by decide, by decide⟩

end LinearAlgebra

/-! ## Group construction: the semidirect product `G₀ = A ⋊ B` -/

section GroupConstruction

/-- The truncated binomial expansion `(I + T)^c = I + cT + (c(c-1)/2)T²`,
valid when `T³ = 0` over `𝔽₃`. -/
def powNilp (T : Matrix (Fin 6) (Fin 6) (ZMod 3)) (c : ZMod 3) :
    Matrix (Fin 6) (Fin 6) (ZMod 3) := 1 + c • T + (c * (c - 1) / 2) • (T * T)

/-- The action matrix `(I + T₁)^{b₁} · (I + T₂)^{b₂}` for `b = (b₁, b₂) ∈ B`. -/
def actionMatrix (b : Fin 2 → ZMod 3) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  powNilp T₁ (b 0) * powNilp T₂ (b 1)

/-- The action matrix at `b = 0` is the identity. -/
theorem am_zero : actionMatrix 0 = 1 := by decide

/-- The action matrix is a group homomorphism: `M(b + b') = M(b) · M(b')`. -/
theorem am_add : ∀ b b' : Fin 2 → ZMod 3,
    actionMatrix (b + b') = actionMatrix b * actionMatrix b' := by decide

/-- `M(-b) · M(b) = I`. -/
theorem am_neg_mul : ∀ b : Fin 2 → ZMod 3,
    actionMatrix (-b) * actionMatrix b = 1 := by decide

/-- `M(b) · M(-b) = I`. -/
theorem am_mul_neg : ∀ b : Fin 2 → ZMod 3,
    actionMatrix b * actionMatrix (-b) = 1 := by decide

/-- The centralizer of `a₀` in `B` is trivial: `b ≠ 0 → M(b) · a₀ ≠ a₀`. -/
theorem centralizer_trivial :
    ∀ b : Fin 2 → ZMod 3, b ≠ 0 → (actionMatrix b).mulVec a₀ ≠ a₀ := by decide

/-- Elements of `ker(T₁) ∩ ker(T₂)` are fixed by every action matrix. -/
theorem am_fixes_ker : ∀ (b : Fin 2 → ZMod 3) (v : Fin 6 → ZMod 3),
    T₁.mulVec v = 0 → T₂.mulVec v = 0 → (actionMatrix b).mulVec v = v := by native_decide

/-- The multiplicative automorphism of `A` induced by the action of `b ∈ B`. -/
def actMulAut (b : Fin 2 → ZMod 3) :
    MulAut (Multiplicative (Fin 6 → ZMod 3)) where
  toFun v := Multiplicative.ofAdd ((actionMatrix b).mulVec (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd ((actionMatrix (-b)).mulVec (Multiplicative.toAdd v))
  left_inv v := by
    simp only [toAdd_ofAdd]
    rw [mulVec_mulVec, am_neg_mul, one_mulVec, ofAdd_toAdd]
  right_inv v := by
    simp only [toAdd_ofAdd]
    rw [mulVec_mulVec, am_mul_neg, one_mulVec, ofAdd_toAdd]
  map_mul' x y := by
    show Multiplicative.ofAdd (actionMatrix b *ᵥ
      (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
      Multiplicative.ofAdd (actionMatrix b *ᵥ Multiplicative.toAdd x) *
      Multiplicative.ofAdd (actionMatrix b *ᵥ Multiplicative.toAdd y)
    rw [mulVec_add, ← ofAdd_add]

/-- The group homomorphism `φ : B →* Aut(A)` defining the semidirect product action. -/
def phi : Multiplicative (Fin 2 → ZMod 3) →*
    MulAut (Multiplicative (Fin 6 → ZMod 3)) where
  toFun b := actMulAut (Multiplicative.toAdd b)
  map_one' := by
    apply MulEquiv.ext; intro v
    show Multiplicative.ofAdd ((actionMatrix 0).mulVec (Multiplicative.toAdd v)) = v
    rw [am_zero, one_mulVec, ofAdd_toAdd]
  map_mul' b₁ b₂ := by
    apply MulEquiv.ext; intro v
    change Multiplicative.ofAdd (actionMatrix (Multiplicative.toAdd b₁ +
      Multiplicative.toAdd b₂) *ᵥ Multiplicative.toAdd v) =
      Multiplicative.ofAdd (actionMatrix (Multiplicative.toAdd b₁) *ᵥ
      Multiplicative.toAdd (Multiplicative.ofAdd (actionMatrix (Multiplicative.toAdd b₂) *ᵥ
      Multiplicative.toAdd v)))
    rw [toAdd_ofAdd, am_add, mulVec_mulVec]

/-- The counterexample group `G₀ = (ℤ/3ℤ)⁶ ⋊_φ (ℤ/3ℤ)²`. -/
abbrev G₀ := Multiplicative (Fin 6 → ZMod 3) ⋊[phi]
  Multiplicative (Fin 2 → ZMod 3)

/-- `G₀` is finite. -/
noncomputable instance : Fintype G₀ :=
  Fintype.ofEquiv (Multiplicative (Fin 6 → ZMod 3) × Multiplicative (Fin 2 → ZMod 3))
    ⟨fun p ↦ ⟨p.1, p.2⟩, fun s ↦ ⟨s.left, s.right⟩, fun _ ↦ rfl, fun ⟨_, _⟩ ↦ rfl⟩

end GroupConstruction

/-! ## Verification of the counterexample hypotheses -/

section Helpers

open SemidirectProduct

/-- The normal subgroup `A = inl.range ≤ G₀`, corresponding to `(ℤ/3ℤ)⁶`. -/
private abbrev AA : Subgroup G₀ := SemidirectProduct.inl.range

/-- The complement `B = inr.range ≤ G₀`, corresponding to `(ℤ/3ℤ)²`. -/
private abbrev BB : Subgroup G₀ := SemidirectProduct.inr.range

/-- The distinguished element `a = inl(1) ∈ A` with trivial `B`-centralizer. -/
private abbrev aa : G₀ := SemidirectProduct.inl (Multiplicative.ofAdd a₀)

/-- The subgroup `H = ⟨a, B⟩ ≤ G₀`. -/
private abbrev HH : Subgroup G₀ := closure ({aa} ∪ (BB : Set G₀))

/-- The center of `H` intersected with `H`: `Z(H) ∩ H`. -/
private abbrev ZHH : Subgroup G₀ := centralizer (HH : Set G₀) ⊓ HH

/-- The derived subgroup `H' = [H, H]`. -/
private abbrev DHH : Subgroup G₀ := ⁅HH, HH⁆

/-- `A` is normal in `G₀`. -/
lemma hyp_normal : AA.Normal := by
  refine ⟨fun x hx y ↦ ?_⟩
  obtain ⟨n, rfl⟩ := hx
  simp [SemidirectProduct.ext_iff, mul_assoc]

/-- Elements of `A` commute with each other. -/
lemma hyp_A_comm : ∀ (x y : AA), (x : G₀) * y = y * x := by
  intro x y
  obtain ⟨n₁, hn₁⟩ := x.2
  obtain ⟨n₂, hn₂⟩ := y.2
  rw [← hn₁, ← hn₂, ← map_mul, ← map_mul]; ac_rfl

/-- Every element of `A` has exponent `3`. -/
lemma hyp_A_exp : ∀ (x : AA), (x : G₀) ^ 3 = 1 := by
  simp only [Subtype.forall, MonoidHom.mem_range, Multiplicative.exists, forall_exists_index,
    forall_apply_eq_imp_iff] at *
  intro a
  simp only [SemidirectProduct.ext_iff]
  native_decide +revert

/-- Elements of `B` commute with each other. -/
lemma hyp_B_comm : ∀ (x y : BB), (x : G₀) * y = y * x := by
  intro x y
  have h_comm : ∀ (x y : Multiplicative (Fin 2 → ZMod 3)), x * y = y * x := by native_decide
  convert h_comm _ _ using 1
  convert Iff.rfl
  rotate_left
  · exact Multiplicative.ofAdd (x.val.2)
  · exact Multiplicative.ofAdd (y.val.2)
  native_decide +revert

/-- Every element of `B` has exponent `3`. -/
lemma hyp_B_exp : ∀ (x : BB), (x : G₀) ^ 3 = 1 := by
  native_decide +revert

/-- `A` and `B` together generate `G₀`: `A ⊔ B = ⊤`. -/
lemma hyp_sup : AA ⊔ BB = ⊤ := by
  ext ⟨x, y⟩
  simp [AA, BB]
  exact mul_mem_sup (Set.mem_range_self _) (Set.mem_range_self _)

/-- `A` and `B` intersect trivially: `A ⊓ B = ⊥`. -/
lemma hyp_inf : AA ⊓ BB = ⊥ := by
  have h_inter : ∀ x : G₀, x ∈ AA → x ∈ BB → x = 1 := by
    simp +zetaDelta at *
    simp_all [SemidirectProduct.ext_iff]
  exact eq_bot_iff.mpr fun x hx ↦ h_inter x hx.1 hx.2

/-- `a ∈ A`. -/
lemma hyp_a_mem : aa ∈ AA := ⟨_, rfl⟩

/-- The centralizer of `a` in `B` is trivial: if `b ∈ B` commutes with `a`, then `b = 1`. -/
lemma hyp_centralizer : ∀ b : G₀, b ∈ BB →
    b * aa = aa * b → b ∈ (⊥ : Subgroup G₀) := by
  intro b hb hba
  obtain ⟨g, hg⟩ : ∃ g : Fin 2 → ZMod 3,
      b = SemidirectProduct.inr (Multiplicative.ofAdd g) := by
    obtain ⟨g, rfl⟩ := hb
    use g; simp
    exact (Equiv.symm_apply_eq Multiplicative.ofAdd).mp rfl
  have h_comm : (actionMatrix g).mulVec a₀ = a₀ := by
    rw [SemidirectProduct.ext_iff] at hba; aesop
  have h_g_zero : g = 0 :=
    Classical.not_not.1 fun hg' ↦ centralizer_trivial g hg' h_comm
  aesop

/-- `|B| = 9`. -/
lemma card_BB : Fintype.card ↥BB = 9 := by
  native_decide +revert

/-- Commutator formula: `⁅inr(b), inl(v)⁆ = inl(M(b) · v - v)`. -/
lemma comm_formula (b : Fin 2 → ZMod 3) (v : Fin 6 → ZMod 3) :
    ⁅(inr (Multiplicative.ofAdd b) : G₀),
     inl (Multiplicative.ofAdd v)⁆ =
    (inl (Multiplicative.ofAdd ((actionMatrix b).mulVec v - v)) : G₀) := by
  rw [commutatorElement_def]
  ext
  · have h_expand : (inr (Multiplicative.ofAdd b) * inl (Multiplicative.ofAdd v) *
        (inr (Multiplicative.ofAdd b))⁻¹ *
        (inl (Multiplicative.ofAdd v))⁻¹ : G₀).left =
        Multiplicative.ofAdd ((actionMatrix b).mulVec v) *
        (Multiplicative.ofAdd v)⁻¹ := by
      simp [mul_assoc]
      exact (Equiv.symm_apply_eq Multiplicative.ofAdd).mp rfl
    have h_diff : Multiplicative.ofAdd ((actionMatrix b).mulVec v) *
        (Multiplicative.ofAdd v)⁻¹ =
        Multiplicative.ofAdd ((actionMatrix b).mulVec v - v) := by
      simp [sub_eq_add_neg]
    rw [h_expand, h_diff]; rfl
  · native_decide +revert

/-- Elements of `ker(T₁) ∩ ker(T₂)` centralize all of `G₀`. -/
lemma centralizes_all (v : Fin 6 → ZMod 3)
    (h1 : T₁.mulVec v = 0) (h2 : T₂.mulVec v = 0) :
    ∀ g : G₀, inl (Multiplicative.ofAdd v) * g = g * inl (Multiplicative.ofAdd v) := by
  intro g
  obtain ⟨a, b⟩ := g
  erw [SemidirectProduct.ext_iff]
  simp only [mk_eq_inl_mul_inr, mul_left, left_inl, right_inl, map_one, left_inr, MulAut.one_apply,
    mul_one, mul_right, right_inr, one_mul, and_true]
  have h_phi_v : (phi b) (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
    convert am_fixes_ker (Multiplicative.toAdd b) v h1 h2 using 1
  rw [h_phi_v, mul_comm]

/-- The commutator subgroup `[H, H]` is contained in `H`. -/
lemma DH_le_HH : DHH ≤ HH := by
  refine commutator_le.mpr fun g₁ hg₁ g₂ hg₂ ↦ ?_
  rw [commutatorElement_def]
  exact HH.mul_mem (HH.mul_mem (HH.mul_mem hg₁ hg₂) (HH.inv_mem hg₁)) (HH.inv_mem hg₂)

/-- The first generator of `B` lies in `H`. -/
lemma inr_f1_mem_HH : (inr (Multiplicative.ofAdd (![1,0] : Fin 2 → ZMod 3)) : G₀) ∈ HH :=
  subset_closure (Or.inr ⟨_, rfl⟩)

/-- The second generator of `B` lies in `H`. -/
lemma inr_f2_mem_HH : (inr (Multiplicative.ofAdd (![0,1] : Fin 2 → ZMod 3)) : G₀) ∈ HH :=
  subset_closure (Or.inr ⟨_, rfl⟩)

/-- `a ∈ H`. -/
lemma aa_mem_HH : aa ∈ HH := subset_closure (Or.inl rfl)

/-- `⁅b₁, a⁆ = inl(e₁)`, the commutator of the first `B`-generator with `a`. -/
lemma comm_f1_a0 :
    ⁅(inr (Multiplicative.ofAdd (![1,0] : Fin 2 → ZMod 3)) : G₀),
     inl (Multiplicative.ofAdd a₀)⁆ =
    (inl (Multiplicative.ofAdd (![0,1,0,0,0,0] : Fin 6 → ZMod 3)) : G₀) := by
  rw [comm_formula]; congr; decide

/-- `⁅b₂, a⁆ = inl(e₂)`, the commutator of the second `B`-generator with `a`. -/
lemma comm_f2_a0 :
    ⁅(inr (Multiplicative.ofAdd (![0,1] : Fin 2 → ZMod 3)) : G₀),
     inl (Multiplicative.ofAdd a₀)⁆ =
    (inl (Multiplicative.ofAdd (![0,0,1,0,0,0] : Fin 6 → ZMod 3)) : G₀) := by
  rw [comm_formula]; congr; decide

set_option maxHeartbeats 400000 in
/-- `⁅b₁, e₁⁆ = inl(e₃)`, a double commutator giving the basis vector for `x²`. -/
lemma comm_f1_e1 :
    ⁅(inr (Multiplicative.ofAdd (![1,0] : Fin 2 → ZMod 3)) : G₀),
     (inl (Multiplicative.ofAdd (![0,1,0,0,0,0] : Fin 6 → ZMod 3)) : G₀)⁆ =
    (inl (Multiplicative.ofAdd (![0,0,0,1,0,0] : Fin 6 → ZMod 3)) : G₀) := by
  rw [comm_formula]; congr; decide

set_option maxHeartbeats 400000 in
/-- `⁅b₁, e₂⁆ = inl(e₄)`, a mixed double commutator giving the basis vector for `xy`. -/
lemma comm_f1_e2 :
    ⁅(inr (Multiplicative.ofAdd (![1,0] : Fin 2 → ZMod 3)) : G₀),
     (inl (Multiplicative.ofAdd (![0,0,1,0,0,0] : Fin 6 → ZMod 3)) : G₀)⁆ =
    (inl (Multiplicative.ofAdd (![0,0,0,0,1,0] : Fin 6 → ZMod 3)) : G₀) := by
  rw [comm_formula]; congr; decide

/-- `⁅b₂, e₂⁆ = inl(e₅)`, a double commutator giving the basis vector for `y²`. -/
lemma comm_f2_e2 :
    ⁅(inr (Multiplicative.ofAdd (![0,1] : Fin 2 → ZMod 3)) : G₀),
     (inl (Multiplicative.ofAdd (![0,0,1,0,0,0] : Fin 6 → ZMod 3)) : G₀)⁆ =
    (inl (Multiplicative.ofAdd (![0,0,0,0,0,1] : Fin 6 → ZMod 3)) : G₀) := by
  have h := comm_formula ![0,1] ![0,0,1,0,0,0]
  have : (actionMatrix ![0,1]).mulVec ![0,0,1,0,0,0] - ![0,0,1,0,0,0] = ![0,0,0,0,0,1] := by decide
  rw [this] at h; exact h

/-- `e₁ ∈ [H, H]`, since `e₁ = ⁅b₁, a⁆`. -/
lemma e1_mem_DH :
    (inl (Multiplicative.ofAdd (![0,1,0,0,0,0] : Fin 6 → ZMod 3)) : G₀) ∈ DHH := by
  rw [← comm_f1_a0]
  exact commutator_mem_commutator inr_f1_mem_HH aa_mem_HH

/-- `e₂ ∈ [H, H]`, since `e₂ = ⁅b₂, a⁆`. -/
lemma e2_mem_DH :
    (inl (Multiplicative.ofAdd (![0,0,1,0,0,0] : Fin 6 → ZMod 3)) : G₀) ∈ DHH := by
  rw [← comm_f2_a0]
  exact commutator_mem_commutator inr_f2_mem_HH aa_mem_HH

/-- `e₁ ∈ H`. -/
lemma e1_mem_HH :
    (inl (Multiplicative.ofAdd (![0,1,0,0,0,0] : Fin 6 → ZMod 3)) : G₀) ∈ HH :=
  DH_le_HH e1_mem_DH

/-- `e₂ ∈ H`. -/
lemma e2_mem_HH :
    (inl (Multiplicative.ofAdd (![0,0,1,0,0,0] : Fin 6 → ZMod 3)) : G₀) ∈ HH :=
  DH_le_HH e2_mem_DH

/-- `e₃ = x² ∈ [H, H]`, since `e₃ = ⁅b₁, e₁⁆`. -/
lemma e3_mem_DH :
    (inl (Multiplicative.ofAdd (![0,0,0,1,0,0] : Fin 6 → ZMod 3)) : G₀) ∈ DHH := by
  rw [← comm_f1_e1]
  exact commutator_mem_commutator inr_f1_mem_HH e1_mem_HH

/-- `e₄ = xy ∈ [H, H]`, since `e₄ = ⁅b₁, e₂⁆`. -/
lemma e4_mem_DH :
    (inl (Multiplicative.ofAdd (![0,0,0,0,1,0] : Fin 6 → ZMod 3)) : G₀) ∈ DHH := by
  rw [← comm_f1_e2]
  exact commutator_mem_commutator inr_f1_mem_HH e2_mem_HH

/-- `e₅ = y² ∈ [H, H]`, since `e₅ = ⁅b₂, e₂⁆`. -/
lemma e5_mem_DH :
    (inl (Multiplicative.ofAdd (![0,0,0,0,0,1] : Fin 6 → ZMod 3)) : G₀) ∈ DHH := by
  rw [← comm_f2_e2]
  exact commutator_mem_commutator inr_f2_mem_HH e2_mem_HH

/-- `e₃ = x²` centralizes `H`, since `e₃ ∈ ker(T₁) ∩ ker(T₂)`. -/
lemma e3_centralizes_HH :
    (inl (Multiplicative.ofAdd (![0,0,0,1,0,0] : Fin 6 → ZMod 3)) : G₀) ∈
      centralizer (HH : Set G₀) := by
  rw [mem_centralizer_iff]
  exact fun g _ ↦ (centralizes_all _ ker_e3.1 ker_e3.2 g).symm

/-- `e₄ = xy` centralizes `H`, since `e₄ ∈ ker(T₁) ∩ ker(T₂)`. -/
lemma e4_centralizes_HH :
    (inl (Multiplicative.ofAdd (![0,0,0,0,1,0] : Fin 6 → ZMod 3)) : G₀) ∈
      centralizer (HH : Set G₀) := by
  rw [mem_centralizer_iff]
  exact fun g _ ↦ (centralizes_all _ ker_e4.1 ker_e4.2 g).symm

/-- `e₅ = y²` centralizes `H`, since `e₅ ∈ ker(T₁) ∩ ker(T₂)`. -/
lemma e5_centralizes_HH :
    (inl (Multiplicative.ofAdd (![0,0,0,0,0,1] : Fin 6 → ZMod 3)) : G₀) ∈
      centralizer (HH : Set G₀) := by
  rw [mem_centralizer_iff]
  exact fun g _ ↦ (centralizes_all _ ker_e5.1 ker_e5.2 g).symm

/-- `e₃ = x² ∈ Z(H) ∩ [H, H]`. -/
lemma e3_mem_ZHDH :
    (inl (Multiplicative.ofAdd (![0,0,0,1,0,0] : Fin 6 → ZMod 3)) : G₀) ∈ ZHH ⊓ DHH :=
  ⟨⟨e3_centralizes_HH, DH_le_HH e3_mem_DH⟩, e3_mem_DH⟩

/-- `e₄ = xy ∈ Z(H) ∩ [H, H]`. -/
lemma e4_mem_ZHDH :
    (inl (Multiplicative.ofAdd (![0,0,0,0,1,0] : Fin 6 → ZMod 3)) : G₀) ∈ ZHH ⊓ DHH :=
  ⟨⟨e4_centralizes_HH, DH_le_HH e4_mem_DH⟩, e4_mem_DH⟩

/-- `e₅ = y² ∈ Z(H) ∩ [H, H]`. -/
lemma e5_mem_ZHDH :
    (inl (Multiplicative.ofAdd (![0,0,0,0,0,1] : Fin 6 → ZMod 3)) : G₀) ∈ ZHH ⊓ DHH :=
  ⟨⟨e5_centralizes_HH, DH_le_HH e5_mem_DH⟩, e5_mem_DH⟩

/-- Every linear combination `c₀ e₃ + c₁ e₄ + c₂ e₅` lies in `Z(H) ∩ [H, H]`. -/
lemma gen_mem_ZHDH (c : Fin 3 → ZMod 3) :
    (inl (Multiplicative.ofAdd (![0,0,0,c 0,c 1,c 2] : Fin 6 → ZMod 3)) : G₀) ∈ ZHH ⊓ DHH := by
  convert Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ e3_mem_ZHDH (c 0).val)
    (Subgroup.pow_mem _ e4_mem_ZHDH (c 1).val)) (Subgroup.pow_mem _ e5_mem_ZHDH (c 2).val) using 1
  rw [← inl.map_pow, ← inl.map_pow, ← inl.map_pow]
  native_decide +revert

/-- The map `c ↦ inl(0,0,0,c₀,c₁,c₂)` is injective. -/
lemma gen_injective : (fun c : Fin 3 → ZMod 3 ↦
    (inl (Multiplicative.ofAdd (![0,0,0,c 0,c 1,c 2] : Fin 6 → ZMod 3)) : G₀)).Injective := by
  native_decide +revert

/-- `|Z(H) ∩ [H, H]| ≥ 27 = 3³`, witnessing that the rank is at least 3. -/
lemma card_ZHDH_ge : 27 ≤ Fintype.card ↥(ZHH ⊓ DHH) := by
  have : Fintype.card (Fin 3 → ZMod 3) ≤ Fintype.card ↥(ZHH ⊓ DHH) := by
    apply Fintype.card_le_of_injective (fun c ↦ ⟨_, gen_mem_ZHDH c⟩)
    exact fun a b hab ↦ gen_injective (congr_arg Subtype.val hab)
  have : Fintype.card (Fin 3 → ZMod 3) = 27 := by decide
  linarith

end Helpers

/-! ## Main theorem -/

section Conclusion

open SemidirectProduct

set_option maxRecDepth 10000 in
/-- The conjecture of Kourovka Problem 21.150 is false.

There exist a prime `p`, a finite group `G`, and subgroups `A ◁ G`, `B ≤ G` with
`A` and `B` elementary abelian of exponent `p`, `G = A · B`, `A ∩ B = 1`,
and an element `a ∈ A` with `C_B(a) = 1`, such that the `p`-rank of
`Z(⟨a,B⟩) ∩ [⟨a,B⟩, ⟨a,B⟩]` exceeds the `p`-rank of `B`.

The counterexample uses `p = 3`, `B ≅ (ℤ/3ℤ)²`, `A ≅ (ℤ/3ℤ)⁶`, with
`rank(Z(H) ∩ H') = 3 > 2 = rank(B)`. -/
theorem kourovka_21_150_is_false :
    ¬ (∀ (G : Type) [Group G] [Fintype G]
      (p : ℕ) (_ : p.Prime)
      (A B : Subgroup G)
      (_ : A.Normal)
      (_ : ∀ (x y : A), (x : G) * y = y * x)
      (_ : ∀ (x : A), (x : G) ^ p = 1)
      (_ : ∀ (x y : B), (x : G) * y = y * x)
      (_ : ∀ (x : B), (x : G) ^ p = 1)
      (_ : A ⊔ B = ⊤)
      (_ : A ⊓ B = ⊥)
      (a : G) (_ : a ∈ A)
      (_ : ∀ b : G, b ∈ B → b * a = a * b → b ∈ (⊥ : Subgroup G)),
      let H := closure ({a} ∪ (B : Set G))
      let ZH := centralizer (H : Set G) ⊓ H
      let DH := ⁅H, H⁆
      log p (Fintype.card ↥(ZH ⊓ DH)) ≤ log p (Fintype.card ↥B)) := by
  field_simp
  intro h
  have h_apply : log 3 (Fintype.card ↥(ZHH ⊓ DHH)) ≤ log 3 (Fintype.card ↥BB) := by
    convert h G₀ 3 prime_three AA BB hyp_normal hyp_A_comm hyp_A_exp hyp_B_comm
      hyp_B_exp hyp_sup hyp_inf aa hyp_a_mem hyp_centralizer using 1
    convert rfl
  refine absurd h_apply ?_
  rw [card_BB]
  exact not_le_of_gt <| le_log_of_pow_le (by decide) (le_trans (by decide) card_ZHDH_ge)

end Conclusion

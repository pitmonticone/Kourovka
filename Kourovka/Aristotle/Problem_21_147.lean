/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.Subgroup.Saturated
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Kourovka Notebook Problem 21.147 — Counterexample

We construct a counterexample showing that the lattice of right-relatively convex (RRC) subgroups
of a right-orderable group is not always a sublattice of the subgroup lattice.

## The group

We use the **Heisenberg group** `Heis` over `ℤ`, the simplest non-abelian torsion-free nilpotent
group. As a set it is `ℤ³`; the group law is
`(x₁, y₁, z₁) + (x₂, y₂, z₂) = (x₁ + x₂, y₁ + y₂, z₁ + z₂ + x₁ y₂)`.

This is a genuinely non-abelian counterexample: unlike `ℤ³`, the Heisenberg group admits right
orderings that are not bi-invariant, so right-relatively convex subgroups are a strictly broader
class than relatively convex ones.

## The subgroups

- `H₁ = ℤ · (1, 0, 1) = {(n, 0, n) | n ∈ ℤ}`
- `H₂ = ℤ · (1, 0, −1) = {(n, 0, −n) | n ∈ ℤ}`

Both live in the abelian subgroup `{(x, 0, z)}` of `Heis`.

## The orderings

Each subgroup is convex under a right ordering built from a positive cone:
- For `H₁`: the cone `P₁ = {g | (g.y, g.x − g.z, g.z) >_lex 0}`.
- For `H₂`: the cone `P₂ = {g | (g.y, g.x + g.z, g.z) >_lex 0}`.

Both are subsemigroups of `(Heis, +)`, and right-invariance is automatic from the identity
`(b + c) − (a + c) = b − a`.

The formalization is additive: `RightOrdering` is the additive form of the usual multiplicative
right order. The RRC predicate is existential in this order witness, so `H₁`, `H₂`, and `C` may
use different right orderings.

## The join is not RRC

The element `(2, 0, 0) = (1, 0, 1) + (1, 0, −1)` belongs to `H₁ ⊔ H₂`, but `(1, 0, 0) ∉ H₁ ⊔ H₂`
(parity obstruction: `x + z` must be even in the join). Since every RRC subgroup is saturated,
the join cannot be RRC: it contains `2 • (1, 0, 0)` but not `(1, 0, 0)`.

## The RRC-join is strictly larger

The subgroup `C = {(a, 0, b) | a, b ∈ ℤ}` (kernel of the `y`-projection) is RRC: it is convex
under the lexicographic right ordering on `(y, x, z)`. Since `C` contains both `H₁` and `H₂`
but `H₁ ⊔ H₂ ⊊ C`, the smallest RRC subgroup containing both — the RRC-join — is strictly
larger than the subgroup join `H₁ ⊔ H₂`. This proves the lattice of RRC subgroups is not a
sublattice of the subgroup lattice.

## Main results

* `Heis.noncommutative`: the Heisenberg group is non-abelian.
* `join_not_rrc`: `H₁ ⊔ H₂` is not RRC.
* `C_rrc`: the subgroup `C = ker(y)` is RRC.
* `kourovka_21_147_counterexample`: there exist RRC subgroups of a non-abelian group whose
  subgroup join is not RRC, yet a strictly larger RRC subgroup contains both.
-/

/-! ### The Heisenberg group -/

/-- The **Heisenberg group** over `ℤ`: triples `(x, y, z)` with group law
`(x₁, y₁, z₁) + (x₂, y₂, z₂) = (x₁ + x₂, y₁ + y₂, z₁ + z₂ + x₁ · y₂)`. -/
@[ext]
structure Heis where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq

namespace Heis

/-- The zero of the Heisenberg group is the triple `(0, 0, 0)`. -/
instance : Zero Heis :=
  ⟨⟨0, 0, 0⟩⟩

/-- Heisenberg addition with the cross-term `x₁ · y₂`:
`(x₁, y₁, z₁) + (x₂, y₂, z₂) = (x₁ + x₂, y₁ + y₂, z₁ + z₂ + x₁ · y₂)`. -/
instance : Add Heis := ⟨fun a b ↦ ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩⟩

/-- The Heisenberg inverse: `-(x, y, z) = (-x, -y, -z + x · y)`.
The `x · y` correction cancels the cross-term in `a + (-a)`. -/
instance : Neg Heis := ⟨fun a ↦ ⟨-a.x, -a.y, -a.z + a.x * a.y⟩⟩

/-- The `x`-coordinate of `0 : Heis` is `0`. -/
@[simp]
lemma zero_x : (0 : Heis).x = 0 := rfl

/-- The `y`-coordinate of `0 : Heis` is `0`. -/
@[simp]
lemma zero_y : (0 : Heis).y = 0 := rfl

/-- The `z`-coordinate of `0 : Heis` is `0`. -/
@[simp]
lemma zero_z : (0 : Heis).z = 0 := rfl

/-- The `x`-coordinate is additive: `(a + b).x = a.x + b.x`. -/
@[simp]
lemma add_x (a b : Heis) : (a + b).x = a.x + b.x := rfl

/-- The `y`-coordinate is additive: `(a + b).y = a.y + b.y`. -/
@[simp]
lemma add_y (a b : Heis) : (a + b).y = a.y + b.y := rfl

/-- The `z`-coordinate of a Heisenberg sum, including the cross-term:
`(a + b).z = a.z + b.z + a.x · b.y`. -/
@[simp]
lemma add_z (a b : Heis) : (a + b).z = a.z + b.z + a.x * b.y := rfl

/-- The `x`-coordinate of the inverse: `(-a).x = -a.x`. -/
@[simp]
lemma neg_x (a : Heis) : (-a).x = -a.x := rfl

/-- The `y`-coordinate of the inverse: `(-a).y = -a.y`. -/
@[simp]
lemma neg_y (a : Heis) : (-a).y = -a.y := rfl

/-- The `z`-coordinate of the inverse, with the cross-term correction:
`(-a).z = -a.z + a.x · a.y`. -/
@[simp]
lemma neg_z (a : Heis) : (-a).z = -a.z + a.x * a.y := rfl

/-- The Heisenberg group `Heis` is an additive group under componentwise addition
with the cross-term `x₁ · y₂` in the third coordinate. -/
instance addGroup : AddGroup Heis :=
  AddGroup.ofLeftAxioms (fun a b c ↦ by ext <;> simp <;> ring) (fun a ↦ by ext <;> simp)
    (fun a ↦ by ext <;> simp)

/-- The `x`-coordinate of a Heisenberg difference: `(a - b).x = a.x - b.x`. -/
@[simp]
lemma sub_x (a b : Heis) : (a - b).x = a.x - b.x := by
  show (a + -b).x = _
  simp only [add_x, neg_x]
  ring

/-- The `y`-coordinate of a Heisenberg difference: `(a - b).y = a.y - b.y`. -/
@[simp]
lemma sub_y (a b : Heis) : (a - b).y = a.y - b.y := by
  show (a + -b).y = _
  simp only [add_y, neg_y]
  ring

/-- The `z`-coordinate of a Heisenberg difference, accounting for the cross-term:
`(a - b).z = a.z - b.z - (a.x - b.x) · b.y`. -/
@[simp]
lemma sub_z (a b : Heis) : (a - b).z = a.z - b.z - (a.x - b.x) * b.y := by
  show (a + -b).z = _
  simp only [add_z, neg_z, neg_y, mul_neg]
  ring

/-- The Heisenberg group is non-abelian: `(1,0,0) + (0,1,0) ≠ (0,1,0) + (1,0,0)`. -/
lemma noncommutative : ∃ a b : Heis, a + b ≠ b + a :=
  ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, by intro h; have := congr_arg Heis.z h; simp at this⟩

end Heis

/-! ### Right orderings and convexity -/

/-- A right-ordering on an additive group: a total, strict order that is right-invariant
under addition. -/
structure RightOrdering (A : Type*) [AddGroup A] where
  /-- The strict order relation. -/
  lt : A → A → Prop
  /-- Irreflexivity. -/
  lt_irrefl : ∀ a, ¬lt a a
  /-- Transitivity. -/
  lt_trans : ∀ a b c, lt a b → lt b c → lt a c
  /-- Trichotomy. -/
  lt_trichotomy : ∀ a b, lt a b ∨ a = b ∨ lt b a
  /-- Right-invariance under addition. -/
  lt_add_right : ∀ a b c, lt a b → lt (a + c) (b + c)

namespace RightOrdering

/-- The non-strict order associated with a `RightOrdering`. -/
def le {A : Type*} [AddGroup A] (o : RightOrdering A) (a b : A) : Prop :=
  o.lt a b ∨ a = b

/-- A subgroup `H` is *convex* with respect to a right-ordering if for every `a, b ∈ H` and
every `g` with `a ≤ g ≤ b`, we have `g ∈ H`. -/
def IsConvex {A : Type*} [AddGroup A] (o : RightOrdering A) (H : AddSubgroup A) : Prop :=
  ∀ a b g, a ∈ H → b ∈ H → o.le a g → o.le g b → g ∈ H

/-- A strict comparison gives the associated non-strict comparison. -/
lemma le_of_lt {A : Type*} [AddGroup A] (o : RightOrdering A) {a b : A} (h : o.lt a b) :
    o.le a b :=
  Or.inl h

/-- If `0 < g` for a right-ordering, then `n • g < (n + 1) • g` for every `n : ℕ`. -/
lemma nsmul_lt_succ_nsmul {A : Type*} [AddGroup A] (o : RightOrdering A) {g : A}
    (hg : o.lt 0 g) (n : ℕ) : o.lt (n • g) ((n + 1) • g) := by
  simpa [succ_nsmul'] using o.lt_add_right 0 g (n • g) hg

/-- If `g < 0` for a right-ordering, then `(n + 1) • g < n • g` for every `n : ℕ`. -/
lemma succ_nsmul_lt_nsmul {A : Type*} [AddGroup A] (o : RightOrdering A) {g : A}
    (hg : o.lt g 0) (n : ℕ) : o.lt ((n + 1) • g) (n • g) := by
  simpa [succ_nsmul'] using o.lt_add_right g 0 (n • g) hg

/-- If `0 < g` for a right-ordering and `n ≥ 2`, then `g < n • g`. -/
lemma lt_nsmul_of_pos {A : Type*} [AddGroup A] (o : RightOrdering A) {g : A}
    (hg : o.lt 0 g) : ∀ {n : ℕ}, 2 ≤ n → o.lt g (n • g) := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => simpa [one_nsmul, two_nsmul] using o.nsmul_lt_succ_nsmul hg 1
  | succ m ih =>
    have ih' : o.lt g ((m + 2) • g) := by simpa [Nat.add_comm] using ih (by omega)
    have hstep : o.lt ((m + 2) • g) ((m + 3) • g) := by
      simpa [Nat.add_assoc] using o.nsmul_lt_succ_nsmul hg (m + 2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      o.lt_trans g ((m + 2) • g) ((m + 3) • g) ih' hstep

/-- If `g < 0` for a right-ordering and `n ≥ 2`, then `n • g < g`. -/
lemma nsmul_lt_of_neg {A : Type*} [AddGroup A] (o : RightOrdering A) {g : A}
    (hg : o.lt g 0) : ∀ {n : ℕ}, 2 ≤ n → o.lt (n • g) g := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => simpa [one_nsmul, two_nsmul] using o.succ_nsmul_lt_nsmul hg 1
  | succ m ih =>
    have ih' : o.lt ((m + 2) • g) g := by simpa [Nat.add_comm] using ih (by omega)
    have hstep : o.lt ((m + 3) • g) ((m + 2) • g) := by
      simpa [Nat.add_assoc] using o.succ_nsmul_lt_nsmul hg (m + 2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      o.lt_trans ((m + 3) • g) ((m + 2) • g) g hstep ih'

end RightOrdering

/-- A subgroup is *right-relatively convex* (RRC) if it is convex with respect to some
right-ordering on the ambient group. -/
def IsRRC {A : Type*} [AddGroup A] (H : AddSubgroup A) : Prop :=
  ∃ o : RightOrdering A, o.IsConvex H

/-- Every right-relatively convex subgroup is saturated. -/
theorem IsRRC.saturated {A : Type*} [AddGroup A] {H : AddSubgroup A} (hH : IsRRC H) :
    H.Saturated := by
  obtain ⟨o, hconv⟩ := hH
  rw [AddSubgroup.saturated_iff_nsmul]
  intro n g hng
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    cases n with
    | zero => exact Or.inr <| by simpa [one_nsmul] using hng
    | succ n =>
      rcases o.lt_trichotomy 0 g with hlt | hzero | hgt
      · refine Or.inr ?_
        have hupper : o.lt g ((Nat.succ (Nat.succ n)) • g) := o.lt_nsmul_of_pos hlt (by omega)
        exact hconv 0 ((Nat.succ (Nat.succ n)) • g) g H.zero_mem hng (o.le_of_lt hlt)
            (o.le_of_lt hupper)
      · subst hzero
        exact Or.inr H.zero_mem
      · refine Or.inr ?_
        have hlower : o.lt ((Nat.succ (Nat.succ n)) • g) g := o.nsmul_lt_of_neg hgt (by omega)
        exact hconv ((Nat.succ (Nat.succ n)) • g) 0 g hng H.zero_mem (o.le_of_lt hlower)
            (o.le_of_lt hgt)

/-! ### Positive cones and right orderings on the Heisenberg group -/

/-- Positive cone for the first ordering: lexicographic on `(y, x − z, z)`.
This is a subsemigroup of `(Heis, +)` and defines a right ordering making `H₁` convex. -/
def Heis.pos₁ (g : Heis) : Prop :=
  0 < g.y ∨ (g.y = 0 ∧ 0 < g.x - g.z) ∨ (g.y = 0 ∧ g.x = g.z ∧ 0 < g.z)

/-- Positive cone for the second ordering: lexicographic on `(y, x + z, z)`.
This is a subsemigroup of `(Heis, +)` and defines a right ordering making `H₂` convex. -/
def Heis.pos₂ (g : Heis) : Prop :=
  0 < g.y ∨ (g.y = 0 ∧ 0 < g.x + g.z) ∨ (g.y = 0 ∧ g.x + g.z = 0 ∧ 0 < g.z)

/-- Positive cone for the `C`-ordering: lexicographic on `(y, x, z)`.
This defines a right ordering making the subgroup `C = ker(y)` convex. -/
def Heis.posC (g : Heis) : Prop :=
  0 < g.y ∨ (g.y = 0 ∧ 0 < g.x) ∨ (g.y = 0 ∧ g.x = 0 ∧ 0 < g.z)

/-- The zero element does not lie in the positive cone `P₁`. -/
lemma Heis.not_pos₁_zero : ¬(0 : Heis).pos₁ := by simp [pos₁]

/-- The zero element does not lie in the positive cone `P₂`. -/
lemma Heis.not_pos₂_zero : ¬(0 : Heis).pos₂ := by simp [pos₂]

/-- The zero element does not lie in the positive cone `P_C`. -/
lemma Heis.not_posC_zero : ¬(0 : Heis).posC := by simp [posC]

/-- `P₁` is closed under Heisenberg addition. When both summands have `y = 0`,
the cross-term `x₁ · y₂ = 0` vanishes and the addition is componentwise. -/
lemma Heis.pos₁_add {g h : Heis} (hg : g.pos₁) (hh : h.pos₁) : (g + h).pos₁ := by
  unfold Heis.pos₁ at *
  rcases hg with hg | hg | hg <;> rcases hh with hh | hh | hh <;> simp_all +decide [add_pos]
  all_goals exact Or.inl (by linarith)

/-- `P₂` is closed under Heisenberg addition. -/
lemma Heis.pos₂_add {g h : Heis} (hg : g.pos₂) (hh : h.pos₂) : (g + h).pos₂ := by
  unfold Heis.pos₂ at *
  rcases hg with hg | hg | hg <;> rcases hh with hh | hh | hh <;>
    simp_all +decide [add_comm, add_left_comm, add_assoc]
  · exact Or.inl (add_pos hg hh)
  all_goals
    first
    | exact Or.inl (by linarith)
    | linarith

/-- `P_C` is closed under Heisenberg addition. When both summands have `y = 0`,
the cross-term `x₁ · y₂ = 0` vanishes and the addition is componentwise. -/
lemma Heis.posC_add {g h : Heis} (hg : g.posC) (hh : h.posC) : (g + h).posC := by
  simp only [Heis.posC] at *
  rcases hg with hg | ⟨hgy, hg⟩ | ⟨hgy, hgx, hg⟩ <;>
    rcases hh with hh | ⟨hhy, hh⟩ | ⟨hhy, hhx, hh⟩ <;>
    simp_all <;> omega

/-- `P₁` satisfies trichotomy: for `g ≠ 0`, either `g ∈ P₁` or `−g ∈ P₁`. -/
lemma Heis.pos₁_trichotomy {g : Heis} (hg : g ≠ 0) : g.pos₁ ∨ (-g).pos₁ := by
  by_cases hg_y : g.y = 0 <;> simp_all +decide [Heis.pos₁]
  · by_cases h : g.z < g.x <;> by_cases h' : g.x = g.z <;> simp [h, h']
    omega
    · contrapose! hg
      aesop
    · exact lt_of_le_of_ne (le_of_not_gt h) h'
  · exact Ne.symm hg_y

/-- `P₂` satisfies trichotomy: for `g ≠ 0`, either `g ∈ P₂` or `−g ∈ P₂`. -/
lemma Heis.pos₂_trichotomy {g : Heis} (hg : g ≠ 0) : g.pos₂ ∨ (-g).pos₂ := by
  by_cases hy : g.y = 0
  · by_cases h : 0 < g.x + g.z <;> simp_all +decide [Heis.pos₂]
    cases lt_or_eq_of_le h <;> simp_all +decide [add_eq_zero_iff_eq_neg]
    · exact Or.inr <| Or.inl <| by linarith
    · contrapose! hg
      ext <;> simp_all +decide
      grind
  · cases lt_or_gt_of_ne hy <;> simp_all +decide [Heis.pos₂]

/-- `P_C` satisfies trichotomy: for `g ≠ 0`, either `g ∈ P_C` or `−g ∈ P_C`. -/
lemma Heis.posC_trichotomy {g : Heis} (hg : g ≠ 0) : g.posC ∨ (-g).posC := by
  by_cases hy : g.y = 0
  · by_cases hx : g.x = 0
    · have hz : g.z ≠ 0 := by
        intro h
        exact hg (by ext <;> simp_all)
      cases lt_or_gt_of_ne hz <;> simp_all +decide [Heis.posC]
    · cases lt_or_gt_of_ne hx <;> simp_all +decide [Heis.posC]
  · cases lt_or_gt_of_ne hy <;> simp_all +decide [Heis.posC]

/-! ### Right orderings from positive cones

For any positive cone `P` (subsemigroup with trichotomy), defining `a < b ↔ b − a ∈ P`
gives a right-ordering. Right-invariance follows from the identity
`(b + c) − (a + c) = b − a`, which holds in any group. -/

/-- Right-ordering on `Heis` making `H₁` convex: `a < b ↔ b − a ∈ P₁`. -/
def ord₁ : RightOrdering Heis where
  lt a b := (b - a).pos₁
  lt_irrefl a h := Heis.not_pos₁_zero (by rwa [sub_self] at h)
  lt_trans a b c hab hbc := by
    rw [show c - a = (c - b) + (b - a) from (sub_add_sub_cancel c b a).symm]
    exact Heis.pos₁_add hbc hab
  lt_trichotomy a b := by
    by_cases h : b - a = 0
    · exact Or.inr (Or.inl (sub_eq_zero.mp h).symm)
    · exact (Heis.pos₁_trichotomy h).elim Or.inl fun hp ↦ Or.inr (Or.inr (by rwa [neg_sub] at hp))
  lt_add_right a b c h := by rwa [add_sub_add_right_eq_sub]

/-- Right-ordering on `Heis` making `H₂` convex: `a < b ↔ b − a ∈ P₂`. -/
def ord₂ : RightOrdering Heis where
  lt a b := (b - a).pos₂
  lt_irrefl a h := Heis.not_pos₂_zero (by rwa [sub_self] at h)
  lt_trans a b c hab hbc := by
    rw [show c - a = (c - b) + (b - a) from (sub_add_sub_cancel c b a).symm]
    exact Heis.pos₂_add hbc hab
  lt_trichotomy a b := by
    by_cases h : b - a = 0
    · exact Or.inr (Or.inl (sub_eq_zero.mp h).symm)
    · exact (Heis.pos₂_trichotomy h).elim Or.inl fun hp ↦ Or.inr (Or.inr (by rwa [neg_sub] at hp))
  lt_add_right a b c h := by rwa [add_sub_add_right_eq_sub]

/-- Right-ordering on `Heis` making `C = ker(y)` convex: `a < b ↔ b − a ∈ P_C`. -/
def ordC : RightOrdering Heis where
  lt a b := (b - a).posC
  lt_irrefl a h := Heis.not_posC_zero (by rwa [sub_self] at h)
  lt_trans a b c hab hbc := by
    rw [show c - a = (c - b) + (b - a) from (sub_add_sub_cancel c b a).symm]
    exact Heis.posC_add hbc hab
  lt_trichotomy a b := by
    by_cases h : b - a = 0
    · exact Or.inr (Or.inl (sub_eq_zero.mp h).symm)
    · exact (Heis.posC_trichotomy h).elim Or.inl fun hp ↦ Or.inr (Or.inr (by rwa [neg_sub] at hp))
  lt_add_right a b c h := by rwa [add_sub_add_right_eq_sub]

/-! ### Subgroups -/

/-- The cyclic subgroup `ℤ · (1, 0, 1)` of `Heis`. -/
def H₁ : AddSubgroup Heis :=
  .zmultiples ⟨1, 0, 1⟩

/-- The cyclic subgroup `ℤ · (1, 0, −1)` of `Heis`. -/
def H₂ : AddSubgroup Heis :=
  .zmultiples ⟨1, 0, -1⟩

/-- The subgroup `C = {(a, 0, b) | a, b ∈ ℤ} = ker(y)` of `Heis`. This is the kernel of the
group homomorphism `(x, y, z) ↦ y` and is abelian (the cross-term `x₁ · y₂` vanishes). -/
def C : AddSubgroup Heis where
  carrier := {g | g.y = 0}
  zero_mem' := rfl
  add_mem' { a b } ( ha : a.y = 0 ) ( hb : b.y = 0 ) := show (a + b).y = 0 by
    simp [Heis.add_y, ha, hb]
  neg_mem' { a } ( ha : a.y = 0 ) := show (-a).y = 0 by simp [Heis.neg_y, ha]

/-- In `Heis`, `n • (a, 0, c) = (n·a, 0, n·c)` because the cross-term vanishes. -/
lemma zsmul_y_zero (n : ℤ) (a c : ℤ) : n • (⟨a, 0, c⟩ : Heis) = ⟨n * a, 0, n * c⟩ := by
  induction n using Int.induction_on with
  | zero => ext <;> simp
  | succ n ih =>
    rw [add_zsmul, ih, one_zsmul]
    ext <;> simp <;> ring
  | pred n ih =>
    rw [sub_zsmul, ih, one_zsmul]
    ext <;> simp <;> ring

/-- Membership in `H₁`: `g ∈ H₁` iff `g.y = 0` and `g.x = g.z`. -/
lemma mem_H₁_iff (g : Heis) : g ∈ H₁ ↔ g.y = 0 ∧ g.x = g.z := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [zsmul_y_zero]
  · rintro ⟨hy, hxz⟩
    exact ⟨g.x, by ext <;> simp [zsmul_y_zero] <;> omega⟩

/-- Membership in `H₂`: `g ∈ H₂` iff `g.y = 0` and `g.x = -g.z`. -/
lemma mem_H₂_iff (g : Heis) : g ∈ H₂ ↔ g.y = 0 ∧ g.x = -g.z := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [zsmul_y_zero]
  · rintro ⟨hy, hxz⟩
    exact ⟨g.x, by ext <;> simp [zsmul_y_zero] <;> omega⟩

/-! ### Convexity -/

/-- `H₁` is convex under `ord₁`. Elements of `H₁` have `y = 0` and `x = z`, so
`x − z = 0`; the `P₁`-lex constraint forces any sandwiched element to satisfy `y = 0`
and `x − z = 0`, hence `g ∈ H₁`. -/
lemma H₁_convex : ord₁.IsConvex H₁ := by
  unfold ord₁
  intros a b g ha hb hab hba
  cases hab <;> cases hba <;> simp_all +decide [sub_eq_iff_eq_add, Heis.pos₁]
  rw [mem_H₁_iff] at *
  grind +ring

/-- `H₂` is convex under `ord₂`. Elements of `H₂` have `y = 0` and `x = −z`, so
`x + z = 0`; the `P₂`-lex constraint forces any sandwiched element to satisfy `y = 0`
and `x + z = 0`, hence `g ∈ H₂`. -/
lemma H₂_convex : ord₂.IsConvex H₂ := by
  unfold RightOrdering.IsConvex ord₂ RightOrdering.le
  simp +zetaDelta only at *
  unfold Heis.pos₂ at *
  intro a b g ha hb hab hba
  rcases hab with hab | rfl <;> rcases hba with hba | rfl <;> simp_all +decide
  rw [mem_H₂_iff] at *
  grind +ring

/-- `C = ker(y)` is convex under `ordC`. Elements of `C` have `y = 0`; the `P_C`-lex
constraint (first comparing `y`) forces any sandwiched element to have `y = 0`. -/
lemma C_convex : ordC.IsConvex C := by
  intro a b g (ha : a.y = 0) (hb : b.y = 0) hag hgb
  show g.y = 0
  rcases hag with ⟨hag⟩ | rfl
  · rcases hgb with ⟨hgb⟩ | rfl
    · simp only [ordC, Heis.posC] at hag hgb
      simp_all only [Heis.sub_y, sub_zero, Heis.sub_x, Int.sub_pos, Heis.sub_z, mul_zero,
        zero_sub, Int.neg_pos, neg_eq_zero]
      omega
    · exact hb
  · exact ha

/-- `H₁` is right-relatively convex. -/
lemma H₁_rrc : IsRRC H₁ :=
  ⟨ord₁, H₁_convex⟩

/-- `H₂` is right-relatively convex. -/
lemma H₂_rrc : IsRRC H₂ :=
  ⟨ord₂, H₂_convex⟩

/-- `C = ker(y)` is right-relatively convex. -/
lemma C_rrc : IsRRC C :=
  ⟨ordC, C_convex⟩

/-! ### The join is not right-relatively convex -/

/-- The parity subgroup: elements with `y = 0` and `x + z` even. This contains `H₁ ⊔ H₂`
and excludes `(1, 0, 0)`. -/
def B : AddSubgroup Heis where
  carrier := {g | g.y = 0 ∧ Even (g.x + g.z)}
  zero_mem' := ⟨rfl, ⟨0, by simp [Heis.zero_x, Heis.zero_z]⟩⟩
  add_mem' := by
    intro a b ⟨hay, hae⟩ ⟨hby, hbe⟩
    simp only [Set.mem_setOf_eq, Heis.add_x, Heis.add_y, Heis.add_z]
    refine ⟨by omega, ?_⟩
    rw [hby, mul_zero, add_zero,
      show a.x + b.x + (a.z + b.z) = (a.x + a.z) + (b.x + b.z) from by ring]
    exact hae.add hbe
  neg_mem' := by
    intro a ⟨hay, hae⟩
    simp only [Set.mem_setOf_eq, Heis.neg_x, Heis.neg_y, Heis.neg_z]
    refine ⟨by omega, ?_⟩
    rw [hay, mul_zero, add_zero, show -a.x + -a.z = -(a.x + a.z) from by ring]
    exact hae.neg

/-- `H₁ ≤ B`: elements of `H₁` satisfy `y = 0` and have `x + z` even (since `x = z`). -/
lemma H₁_le_B : H₁ ≤ B := by
  intro g hg
  rw [mem_H₁_iff] at hg
  exact ⟨hg.1, ⟨g.x, by omega⟩⟩

/-- `H₂ ≤ B`: elements of `H₂` satisfy `y = 0` and have `x + z = 0`, hence even. -/
lemma H₂_le_B : H₂ ≤ B := by
  intro g hg
  rw [mem_H₂_iff] at hg
  exact ⟨hg.1, by simp [hg.2]⟩

/-- `H₁ ≤ C`: elements of `H₁` have `y = 0`. -/
lemma H₁_le_C : H₁ ≤ C := fun g hg ↦ ((mem_H₁_iff g).mp hg).1

/-- `H₂ ≤ C`: elements of `H₂` have `y = 0`. -/
lemma H₂_le_C : H₂ ≤ C := fun g hg ↦ ((mem_H₂_iff g).mp hg).1

/-- `(2, 0, 0) = (1, 0, 1) + (1, 0, −1) ∈ H₁ ⊔ H₂`. -/
lemma two_mem_join : (⟨2, 0, 0⟩ : Heis) ∈ H₁ ⊔ H₂ := by
  have : (⟨1, 0, 1⟩ : Heis) + ⟨1, 0, -1⟩ = ⟨2, 0, 0⟩ := by ext <;> simp
  exact this ▸ AddSubgroup.add_mem_sup (AddSubgroup.mem_zmultiples _) (AddSubgroup.mem_zmultiples _)

/-- `(1, 0, 0) ∉ H₁ ⊔ H₂` because `x + z` must be even in the join. -/
lemma one_not_mem_join : (⟨1, 0, 0⟩ : Heis) ∉ H₁ ⊔ H₂ :=
  fun h ↦ absurd (sup_le H₁_le_B H₂_le_B h).2 (by norm_num)

/-- `(1, 0, 0) ∈ C \ (H₁ ⊔ H₂)`, witnessing that `H₁ ⊔ H₂ < C`. -/
lemma one_mem_C : (⟨1, 0, 0⟩ : Heis) ∈ C := rfl

/-- The subgroup join is not saturated: it contains `2 • (1, 0, 0)` but not `(1, 0, 0)`. -/
lemma join_not_saturated : ¬(H₁ ⊔ H₂).Saturated := by
  intro hsat
  have htwo : (2 : ℕ) • (⟨1, 0, 0⟩ : Heis) ∈ H₁ ⊔ H₂ := by simpa [two_nsmul] using two_mem_join
  exact one_not_mem_join ((hsat htwo).resolve_left (by norm_num))

/--
The join `H₁ ⊔ H₂` is not RRC because every RRC subgroup is saturated, while this join is not
saturated. -/
lemma join_not_rrc : ¬IsRRC (H₁ ⊔ H₂) := fun hrrc ↦ join_not_saturated hrrc.saturated

/-- The subgroup join `H₁ ⊔ H₂` is strictly contained in `C`. -/
lemma join_lt_C : H₁ ⊔ H₂ < C :=
  lt_of_le_of_ne (sup_le H₁_le_C H₂_le_C) fun h ↦ one_not_mem_join (h ▸ one_mem_C)

/-! ### `C` is the smallest RRC subgroup containing `H₁` and `H₂`

We show that every RRC subgroup containing both `H₁` and `H₂` must contain `C = ker(y)`.
This proves the RRC-join of `H₁` and `H₂` equals `C`, which is strictly larger than the
subgroup join `H₁ ⊔ H₂`, completing the counterexample.
-/

/--
Any RRC subgroup containing both `H₁` and `H₂` must contain `(1, 0, 0)`, by saturatedness. -/
lemma one_mem_of_rrc_containing {L : AddSubgroup Heis} (hL : IsRRC L) (h1 : H₁ ≤ L)
    (h2 : H₂ ≤ L) : (⟨1, 0, 0⟩ : Heis) ∈ L := by
  have h2mem : (⟨2, 0, 0⟩ : Heis) ∈ L := by
    have : (⟨1, 0, 1⟩ : Heis) + ⟨1, 0, -1⟩ = ⟨2, 0, 0⟩ := by ext <;> simp
    exact this ▸ L.add_mem (h1 (AddSubgroup.mem_zmultiples _)) (h2 (AddSubgroup.mem_zmultiples _))
  have htwo : (2 : ℕ) • (⟨1, 0, 0⟩ : Heis) ∈ L := by simpa [two_nsmul] using h2mem
  exact (hL.saturated htwo).resolve_left (by norm_num)

/-- `C = ker(y)` is the smallest RRC subgroup containing both `H₁` and `H₂`: if `L` is any
RRC subgroup with `H₁ ≤ L` and `H₂ ≤ L`, then `C ≤ L`.

Once `(1, 0, 0) ∈ L` (from `one_mem_of_rrc_containing`), we get
`(0, 0, 1) = −(1, 0, 0) + (1, 0, 1) ∈ L`, and every element `(a, 0, b) ∈ C` is
`a • (1, 0, 0) + b • (0, 0, 1) ∈ L`. -/
lemma C_le_of_rrc_containing {L : AddSubgroup Heis} (hL : IsRRC L) (h1 : H₁ ≤ L) (h2 : H₂ ≤ L) :
    C ≤ L := by
  have h100 := one_mem_of_rrc_containing hL h1 h2
  have h001 : (⟨0, 0, 1⟩ : Heis) ∈ L := by
    have : (⟨0, 0, 1⟩ : Heis) = -⟨1, 0, 0⟩ + ⟨1, 0, 1⟩ := by ext <;> simp
    exact this ▸ L.add_mem (L.neg_mem h100) (h1 (AddSubgroup.mem_zmultiples _))
  intro g (hg : g.y = 0)
  have : g = g.x • (⟨1, 0, 0⟩ : Heis) + g.z • ⟨0, 0, 1⟩ := by ext <;> simp [zsmul_y_zero, hg]
  exact this ▸ L.add_mem (L.zsmul_mem h100 _) (L.zsmul_mem h001 _)

/-! ### Main result -/

/-- **Kourovka Notebook Problem 21.147 — Counterexample.**

The lattice of right-relatively convex (RRC) subgroups of a right-orderable group is **not**
always a sublattice of the subgroup lattice. In the (non-abelian) Heisenberg group over `ℤ`:

1. `H₁ = ℤ·(1,0,1)` and `H₂ = ℤ·(1,0,−1)` are both RRC (`H₁_rrc`, `H₂_rrc`).
2. Their subgroup join `H₁ ⊔ H₂` is **not** RRC (`join_not_rrc`).
3. `C = ker(y)` is the RRC-join of `H₁` and `H₂` — the smallest RRC subgroup containing
   both (`C_rrc`, `H₁_le_C`, `H₂_le_C`, `C_le_of_rrc_containing`), and
   `H₁ ⊔ H₂ < C` (`join_lt_C`).

Therefore the RRC-join of `H₁` and `H₂` differs from the subgroup join, proving the RRC
subgroups do not form a sublattice of the subgroup lattice. -/
theorem kourovka_21_147_counterexample :
    (∃ a b : Heis, a + b ≠ b + a) ∧
    IsRRC H₁ ∧ IsRRC H₂ ∧ ¬ IsRRC (H₁ ⊔ H₂) ∧
    IsRRC C ∧ H₁ ⊔ H₂ < C ∧ H₁ ≤ C ∧ H₂ ≤ C ∧
    (∀ L : AddSubgroup Heis, IsRRC L → H₁ ≤ L → H₂ ≤ L → C ≤ L) :=
  ⟨Heis.noncommutative, H₁_rrc, H₂_rrc, join_not_rrc, C_rrc, join_lt_C,
    H₁_le_C, H₂_le_C, fun _ hL h1 h2 ↦ C_le_of_rrc_containing hL h1 h2⟩

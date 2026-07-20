/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone, Daniel Morrison
-/
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.GroupTheory.Subgroup.Saturated
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Right orderings and right-relative convexity

This file defines bundled right-ordering witnesses and right-relatively convex
subgroups. It also proves that every right-relatively convex subgroup is saturated.
-/

/-! ## Right-ordering witnesses -/

/-- A bundled right-ordering witness on a group, stored as data rather than a global instance. -/
structure RightOrdering (G : Type*) [Group G] where
  /-- The bundled linear order. -/
  toLinearOrder : LinearOrder G
  /-- Right multiplication is strictly monotone for the bundled order. -/
  toMulRightStrictMono : @MulRightStrictMono G _ toLinearOrder.toLT

/-- A bundled additive right-ordering witness, stored as data rather than a global instance. -/
structure AddRightOrdering (A : Type*) [AddGroup A] where
  /-- The bundled linear order. -/
  toLinearOrder : LinearOrder A
  /-- Right addition is strictly monotone for the bundled order. -/
  toAddRightStrictMono : @AddRightStrictMono A _ toLinearOrder.toLT

attribute [to_additive existing AddRightOrdering] RightOrdering

/-! ## Right-relatively convex subgroups -/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Powers of an element greater than one strictly increase at each successor. -/
@[to_additive
/-- Natural multiples of a positive element strictly increase at each successor. -/]
lemma pow_lt_succ_pow_of_one_lt [LinearOrder G] [MulRightStrictMono G] {g : G}
    (hg : 1 < g) (n : ℕ) : g ^ n < g ^ (n + 1) := by
  simpa [pow_succ'] using mul_lt_mul_left hg (g ^ n)

/-- Powers of an element less than one strictly decrease at each successor. -/
@[to_additive
/-- Natural multiples of a negative element strictly decrease at each successor. -/]
lemma succ_pow_lt_pow_of_lt_one [LinearOrder G] [MulRightStrictMono G] {g : G}
    (hg : g < 1) (n : ℕ) : g ^ (n + 1) < g ^ n := by
  simpa [pow_succ'] using mul_lt_mul_left hg (g ^ n)

/-- An element greater than one is less than each of its powers with exponent at least two. -/
@[to_additive
/-- A positive element is less than each of its natural multiples by at least two. -/]
lemma lt_pow_of_one_lt [LinearOrder G] [MulRightStrictMono G] {g : G} (hg : 1 < g) :
    ∀ {n : ℕ}, 2 ≤ n → g < g ^ n := by
  intro n hn
  exact Nat.le_induction (by simpa using pow_lt_succ_pow_of_one_lt hg 1)
    (fun n _ ih ↦ ih.trans (pow_lt_succ_pow_of_one_lt hg n)) n hn

/-- Each power with exponent at least two of an element less than one is less than the element. -/
@[to_additive
/-- Each natural multiple by at least two of a negative element is less than the element. -/]
lemma pow_lt_of_lt_one [LinearOrder G] [MulRightStrictMono G] {g : G} (hg : g < 1) :
    ∀ {n : ℕ}, 2 ≤ n → g ^ n < g := by
  intro n hn
  exact Nat.le_induction (by simpa using succ_pow_lt_pow_of_lt_one hg 1)
    (fun n _ ih ↦ (succ_pow_lt_pow_of_lt_one hg n).trans ih) n hn

/-- An order-convex subgroup of a right-ordered group is saturated. -/
@[to_additive
/-- An order-convex additive subgroup of a right-ordered additive group is saturated. -/]
theorem saturated_of_ordConnected [LinearOrder G] [MulRightStrictMono G] {H : Subgroup G}
    (hH : (H : Set G).OrdConnected) : H.Saturated := by
  rw [Subgroup.saturated_iff_npow]
  rintro (_ | _ | n) g hng
  · exact Or.inl rfl
  · exact Or.inr (by simpa using hng)
  · right
    rcases lt_trichotomy 1 g with hlt | rfl | hgt
    · exact hH.out H.one_mem hng
        ⟨hlt.le, (lt_pow_of_one_lt hlt (by omega)).le⟩
    · exact H.one_mem
    · exact hH.out hng H.one_mem
        ⟨(pow_lt_of_lt_one hgt (by omega)).le, hgt.le⟩

/-- A subgroup is *right-relatively convex* if it is convex with respect to some right-ordering on
the ambient group. -/
@[to_additive
/-- An additive subgroup is *right-relatively convex* if it is convex with respect to some
right-ordering on the ambient additive group. -/]
def IsRightRelativelyConvex (H : Subgroup G) : Prop :=
  ∃ o : RightOrdering G,
    let : LinearOrder G := o.toLinearOrder
    let : MulRightStrictMono G := o.toMulRightStrictMono
    (H : Set G).OrdConnected

/-- Every right-relatively convex subgroup is saturated. -/
@[to_additive
/-- Every right-relatively convex additive subgroup is saturated. -/]
theorem IsRightRelativelyConvex.saturated {H : Subgroup G} (hH : H.IsRightRelativelyConvex) :
    H.Saturated := by
  obtain ⟨o, hconv⟩ := hH
  exact @saturated_of_ordConnected G _ o.toLinearOrder o.toMulRightStrictMono H hconv

end Subgroup

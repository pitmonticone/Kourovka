/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone
-/
import Kourovka.Mathlib.Algebra.Order.Group.RightOrdering
import Kourovka.Mathlib.GroupTheory.SpecificGroups.Heisenberg
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Kourovka Notebook Problem 21.147

## Problem Statement

Let `G` be a right-orderable group. A subgroup is **right-relatively convex** (RRC)
if it is convex with respect to some right ordering of `G`.

**Question.** Is the lattice of RRC subgroups of a right-orderable group always a
sublattice of the lattice of its subgroups?

**Answer.** No.

## Proof Outline

We construct a counterexample in the integer Heisenberg group. Let
`H₁ = ℤ · (1, 0, 1)` and `H₂ = ℤ · (1, 0, -1)`. Each is RRC for a suitable
lexicographic right ordering: `H₁` is convex for `ord₁`, and `H₂` is convex for
`ord₂`; no common right-order witness is asserted. Their subgroup join contains
`(2, 0, 0)` and not `(1, 0, 0)`, so it is not saturated and hence not RRC. This
refutes closure under subgroup joins. The larger subgroup `C = ker(y)` is RRC,
contains both `H₁` and `H₂`, and strictly contains their subgroup join.
-/

/-! ## Positive cones and right orderings on the Heisenberg group -/

/-- Positive cone for the lexicographic ordering on `(y, x − z, z)`. -/
def HeisenbergGroup.pos₁ (g : HeisenbergGroup) : Prop :=
  0 < g.y ∨ (g.y = 0 ∧ 0 < g.x - g.z) ∨ (g.y = 0 ∧ g.x = g.z ∧ 0 < g.z)

/-- Positive cone for the lexicographic ordering on `(y, x + z, z)`. -/
def HeisenbergGroup.pos₂ (g : HeisenbergGroup) : Prop :=
  0 < g.y ∨ (g.y = 0 ∧ 0 < g.x + g.z) ∨ (g.y = 0 ∧ g.x + g.z = 0 ∧ 0 < g.z)

/-- Positive cone for the lexicographic ordering on `(y, x, z)`. -/
def HeisenbergGroup.posC (g : HeisenbergGroup) : Prop :=
  0 < g.y ∨ (g.y = 0 ∧ 0 < g.x) ∨ (g.y = 0 ∧ g.x = 0 ∧ 0 < g.z)

/-- The zero element does not satisfy `HeisenbergGroup.pos₁`. -/
lemma HeisenbergGroup.not_pos₁_zero : ¬(0 : HeisenbergGroup).pos₁ := by simp [pos₁]

/-- The zero element does not satisfy `HeisenbergGroup.pos₂`. -/
lemma HeisenbergGroup.not_pos₂_zero : ¬(0 : HeisenbergGroup).pos₂ := by simp [pos₂]

/-- The zero element does not satisfy `HeisenbergGroup.posC`. -/
lemma HeisenbergGroup.not_posC_zero : ¬(0 : HeisenbergGroup).posC := by simp [posC]

/-- `HeisenbergGroup.pos₁` is closed under Heisenberg addition. -/
lemma HeisenbergGroup.pos₁_add {g h : HeisenbergGroup} (hg : g.pos₁) (hh : h.pos₁) :
    (g + h).pos₁ := by
  unfold HeisenbergGroup.pos₁ at *
  rcases hg with hg | hg | hg <;> rcases hh with hh | hh | hh <;> simp_all <;> omega

/-- `HeisenbergGroup.pos₂` is closed under Heisenberg addition. -/
lemma HeisenbergGroup.pos₂_add {g h : HeisenbergGroup} (hg : g.pos₂) (hh : h.pos₂) :
    (g + h).pos₂ := by
  unfold HeisenbergGroup.pos₂ at *
  rcases hg with hg | hg | hg <;> rcases hh with hh | hh | hh <;> simp_all <;> omega

/-- `HeisenbergGroup.posC` is closed under Heisenberg addition. -/
lemma HeisenbergGroup.posC_add {g h : HeisenbergGroup} (hg : g.posC) (hh : h.posC) :
    (g + h).posC := by
  unfold HeisenbergGroup.posC at *
  rcases hg with hg | hg | hg <;> rcases hh with hh | hh | hh <;> simp_all <;> omega

/-- A nonzero element or its negation satisfies `HeisenbergGroup.pos₁`. -/
lemma HeisenbergGroup.pos₁_trichotomy {g : HeisenbergGroup} (hg : g ≠ 0) :
    g.pos₁ ∨ (-g).pos₁ := by
  by_cases hy : g.y = 0 <;> simp_all [pos₁, HeisenbergGroup.ext_iff] <;> omega

/-- A nonzero element or its negation satisfies `HeisenbergGroup.pos₂`. -/
lemma HeisenbergGroup.pos₂_trichotomy {g : HeisenbergGroup} (hg : g ≠ 0) :
    g.pos₂ ∨ (-g).pos₂ := by
  by_cases hy : g.y = 0 <;> simp_all [pos₂, HeisenbergGroup.ext_iff] <;> omega

/-- A nonzero element or its negation satisfies `HeisenbergGroup.posC`. -/
lemma HeisenbergGroup.posC_trichotomy {g : HeisenbergGroup} (hg : g ≠ 0) :
    g.posC ∨ (-g).posC := by
  by_cases hy : g.y = 0 <;> simp_all [posC, HeisenbergGroup.ext_iff] <;> omega

/-! ## Right orderings from positive cones -/

/-- The strict relation induced by `pos₁`: `a < b` when `b - a` lies in `pos₁`. -/
abbrev HeisenbergGroup.lt₁ (a b : HeisenbergGroup) : Prop :=
  (b - a).pos₁

/-- The strict relation induced by `pos₂`: `a < b` when `b - a` lies in `pos₂`. -/
abbrev HeisenbergGroup.lt₂ (a b : HeisenbergGroup) : Prop :=
  (b - a).pos₂

/-- The strict relation induced by `posC`: `a < b` when `b - a` lies in `posC`. -/
abbrev HeisenbergGroup.ltC (a b : HeisenbergGroup) : Prop :=
  (b - a).posC

/-- The classical decidability instance for `HeisenbergGroup.lt₁`. -/
noncomputable instance HeisenbergGroup.instDecidableRelLt₁ :
    DecidableRel HeisenbergGroup.lt₁ :=
  Classical.decRel HeisenbergGroup.lt₁

/-- The classical decidability instance for `HeisenbergGroup.lt₂`. -/
noncomputable instance HeisenbergGroup.instDecidableRelLt₂ :
    DecidableRel HeisenbergGroup.lt₂ :=
  Classical.decRel HeisenbergGroup.lt₂

/-- The classical decidability instance for `HeisenbergGroup.ltC`. -/
noncomputable instance HeisenbergGroup.instDecidableRelLtC :
    DecidableRel HeisenbergGroup.ltC :=
  Classical.decRel HeisenbergGroup.ltC

/-- `HeisenbergGroup.lt₁` is a strict total order. -/
instance HeisenbergGroup.instIsStrictTotalOrderLt₁ :
    IsStrictTotalOrder HeisenbergGroup HeisenbergGroup.lt₁ where
  irrefl a := by simpa [HeisenbergGroup.lt₁] using HeisenbergGroup.not_pos₁_zero
  trans a b c hab hbc := by
    change (c - a).pos₁
    exact sub_add_sub_cancel c b a ▸ HeisenbergGroup.pos₁_add hbc hab
  trichotomous a b hab hba := by
    by_cases h : b - a = 0
    · exact (sub_eq_zero.mp h).symm
    · rcases HeisenbergGroup.pos₁_trichotomy h with hpos | hneg
      · exact (hab hpos).elim
      · exact (hba (by simpa [HeisenbergGroup.lt₁, neg_sub] using hneg)).elim

/-- `HeisenbergGroup.lt₂` is a strict total order. -/
instance HeisenbergGroup.instIsStrictTotalOrderLt₂ :
    IsStrictTotalOrder HeisenbergGroup HeisenbergGroup.lt₂ where
  irrefl a := by simpa [HeisenbergGroup.lt₂] using HeisenbergGroup.not_pos₂_zero
  trans a b c hab hbc := by
    change (c - a).pos₂
    exact sub_add_sub_cancel c b a ▸ HeisenbergGroup.pos₂_add hbc hab
  trichotomous a b hab hba := by
    by_cases h : b - a = 0
    · exact (sub_eq_zero.mp h).symm
    · rcases HeisenbergGroup.pos₂_trichotomy h with hpos | hneg
      · exact (hab hpos).elim
      · exact (hba (by simpa [HeisenbergGroup.lt₂, neg_sub] using hneg)).elim

/-- `HeisenbergGroup.ltC` is a strict total order. -/
instance HeisenbergGroup.instIsStrictTotalOrderLtC :
    IsStrictTotalOrder HeisenbergGroup HeisenbergGroup.ltC where
  irrefl a := by simpa [HeisenbergGroup.ltC] using HeisenbergGroup.not_posC_zero
  trans a b c hab hbc := by
    change (c - a).posC
    exact sub_add_sub_cancel c b a ▸ HeisenbergGroup.posC_add hbc hab
  trichotomous a b hab hba := by
    by_cases h : b - a = 0
    · exact (sub_eq_zero.mp h).symm
    · rcases HeisenbergGroup.posC_trichotomy h with hpos | hneg
      · exact (hab hpos).elim
      · exact (hba (by simpa [HeisenbergGroup.ltC, neg_sub] using hneg)).elim

/-- The linear order on `HeisenbergGroup` induced by `HeisenbergGroup.lt₁`. -/
noncomputable abbrev ord₁LinearOrder : LinearOrder HeisenbergGroup :=
  linearOrderOfSTO HeisenbergGroup.lt₁

/-- The linear order on `HeisenbergGroup` induced by `HeisenbergGroup.lt₂`. -/
noncomputable abbrev ord₂LinearOrder : LinearOrder HeisenbergGroup :=
  linearOrderOfSTO HeisenbergGroup.lt₂

/-- The linear order on `HeisenbergGroup` induced by `HeisenbergGroup.ltC`. -/
noncomputable abbrev ordCLinearOrder : LinearOrder HeisenbergGroup :=
  linearOrderOfSTO HeisenbergGroup.ltC

/-- Right addition is strictly monotone for `ord₁LinearOrder`. -/
lemma ord₁AddRightStrictMono :
    @AddRightStrictMono HeisenbergGroup _ ord₁LinearOrder.toLT where
  elim c {a b} h := by
    change HeisenbergGroup.lt₁ (a + c) (b + c)
    rwa [HeisenbergGroup.lt₁, add_sub_add_right_eq_sub]

/-- Right addition is strictly monotone for `ord₂LinearOrder`. -/
lemma ord₂AddRightStrictMono :
    @AddRightStrictMono HeisenbergGroup _ ord₂LinearOrder.toLT where
  elim c {a b} h := by
    change HeisenbergGroup.lt₂ (a + c) (b + c)
    rwa [HeisenbergGroup.lt₂, add_sub_add_right_eq_sub]

/-- Right addition is strictly monotone for `ordCLinearOrder`. -/
lemma ordCAddRightStrictMono :
    @AddRightStrictMono HeisenbergGroup _ ordCLinearOrder.toLT where
  elim c {a b} h := by
    change HeisenbergGroup.ltC (a + c) (b + c)
    rwa [HeisenbergGroup.ltC, add_sub_add_right_eq_sub]

/-- Right-ordering making `H₁` convex, with `a < b` defined by `pos₁ (b - a)`. -/
noncomputable def ord₁ : AddRightOrdering HeisenbergGroup :=
  ⟨ord₁LinearOrder, ord₁AddRightStrictMono⟩

/-- Right-ordering making `H₂` convex, with `a < b` defined by `pos₂ (b - a)`. -/
noncomputable def ord₂ : AddRightOrdering HeisenbergGroup :=
  ⟨ord₂LinearOrder, ord₂AddRightStrictMono⟩

/-- Right-ordering making `C = ker(y)` convex, with `a < b` defined by `posC (b - a)`. -/
noncomputable def ordC : AddRightOrdering HeisenbergGroup :=
  ⟨ordCLinearOrder, ordCAddRightStrictMono⟩

/-! ## Subgroups -/

/-- The cyclic subgroup `ℤ · (1, 0, 1)` of `HeisenbergGroup`. -/
def H₁ : AddSubgroup HeisenbergGroup :=
  .zmultiples ⟨1, 0, 1⟩

/-- The cyclic subgroup `ℤ · (1, 0, −1)` of `HeisenbergGroup`. -/
def H₂ : AddSubgroup HeisenbergGroup :=
  .zmultiples ⟨1, 0, -1⟩

/-- The subgroup `C = ker(y)` of elements with `y = 0`, realised as the kernel of the
`y`-coordinate homomorphism `HeisenbergGroup.yHom`. -/
def C : AddSubgroup HeisenbergGroup :=
  HeisenbergGroup.yHom.ker

/-- Membership in `C`: `g ∈ C` iff `g.y = 0`. -/
lemma mem_C_iff (g : HeisenbergGroup) : g ∈ C ↔ g.y = 0 := by simp [C]

/-- Membership in `H₁`: `g ∈ H₁` iff `g.y = 0` and `g.x = g.z`. -/
lemma mem_H₁_iff (g : HeisenbergGroup) : g ∈ H₁ ↔ g.y = 0 ∧ g.x = g.z := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [HeisenbergGroup.zsmul_y_zero]
  · rintro ⟨hy, hxz⟩
    exact ⟨g.x, by ext <;> simp [HeisenbergGroup.zsmul_y_zero] <;> omega⟩

/-- Membership in `H₂`: `g ∈ H₂` iff `g.y = 0` and `g.x = -g.z`. -/
lemma mem_H₂_iff (g : HeisenbergGroup) : g ∈ H₂ ↔ g.y = 0 ∧ g.x = -g.z := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [HeisenbergGroup.zsmul_y_zero]
  · rintro ⟨hy, hxz⟩
    exact ⟨g.x, by ext <;> simp [HeisenbergGroup.zsmul_y_zero] <;> omega⟩

/-! ## Convexity -/

/-- `H₁` is convex under `ord₁`. Elements of `H₁` have `y = 0` and `x = z`, so
`x - z = 0`; the lexicographic sandwich inequalities for `P₁` force every
sandwiched element to satisfy the same two equations. -/
lemma H₁_convex :
    let : LinearOrder HeisenbergGroup := ord₁.toLinearOrder
    (H₁ : Set HeisenbergGroup).OrdConnected := by
  let : LinearOrder HeisenbergGroup := ord₁.toLinearOrder
  rw [Set.ordConnected_iff]
  intro a ha b hb _hab g hg
  rcases lt_or_eq_of_le hg.1 with hag | rfl
  · rcases lt_or_eq_of_le hg.2 with hgb | rfl
    · change (g - a).pos₁ at hag
      change (b - g).pos₁ at hgb
      simp_all [sub_eq_iff_eq_add, HeisenbergGroup.pos₁, mem_H₁_iff]
      grind
    · exact hb
  · exact ha

/-- `H₂` is convex under `ord₂`. Elements of `H₂` have `y = 0` and `x = -z`, so
`x + z = 0`; the lexicographic sandwich inequalities for `P₂` force every
sandwiched element to satisfy the same two equations. -/
lemma H₂_convex :
    let : LinearOrder HeisenbergGroup := ord₂.toLinearOrder
    (H₂ : Set HeisenbergGroup).OrdConnected := by
  let : LinearOrder HeisenbergGroup := ord₂.toLinearOrder
  rw [Set.ordConnected_iff]
  intro a ha b hb _hab g hg
  rcases lt_or_eq_of_le hg.1 with hag | rfl
  · rcases lt_or_eq_of_le hg.2 with hgb | rfl
    · change (g - a).pos₂ at hag
      change (b - g).pos₂ at hgb
      simp_all [HeisenbergGroup.pos₂, mem_H₂_iff]
      grind
    · exact hb
  · exact ha

/-- `C = ker(y)` is convex under `ordC`. -/
lemma C_convex :
    let : LinearOrder HeisenbergGroup := ordC.toLinearOrder
    (C : Set HeisenbergGroup).OrdConnected := by
  let : LinearOrder HeisenbergGroup := ordC.toLinearOrder
  rw [Set.ordConnected_iff]
  intro a ha b hb _hab g hg
  simp only [SetLike.mem_coe, mem_C_iff] at ha hb ⊢
  rcases lt_or_eq_of_le hg.1 with hag | rfl
  · rcases lt_or_eq_of_le hg.2 with hgb | rfl
    · change (g - a).posC at hag
      change (b - g).posC at hgb
      simp_all [HeisenbergGroup.posC]
      omega
    · exact hb
  · exact ha

/-- `H₁` is right-relatively convex. -/
lemma H₁_rrc : H₁.IsRightRelativelyConvex :=
  ⟨ord₁, H₁_convex⟩

/-- `H₂` is right-relatively convex. -/
lemma H₂_rrc : H₂.IsRightRelativelyConvex :=
  ⟨ord₂, H₂_convex⟩

/-- `C = ker(y)` is right-relatively convex. -/
lemma C_rrc : C.IsRightRelativelyConvex :=
  ⟨ordC, C_convex⟩

/-! ## The join is not right-relatively convex -/

/-- The parity subgroup: elements with `y = 0` and `x + z` even. -/
def B : AddSubgroup HeisenbergGroup where
  carrier := {g | g.y = 0 ∧ Even (g.x + g.z)}
  zero_mem' := ⟨rfl, 0, rfl⟩
  add_mem' := by
    rintro a b ⟨hay, k, hk⟩ ⟨hby, l, hl⟩
    exact ⟨by simp [hay, hby], k + l, by
      simp [hby]
      omega⟩
  neg_mem' := by
    rintro a ⟨hay, k, hk⟩
    exact ⟨by simp [hay], -k, by
      simp [hay]
      omega⟩

/-- `H₁ ≤ B`. -/
lemma H₁_le_B : H₁ ≤ B := fun g hg ↦ by
  rw [mem_H₁_iff] at hg
  exact ⟨hg.1, g.x, by omega⟩

/-- `H₂ ≤ B`. -/
lemma H₂_le_B : H₂ ≤ B := fun g hg ↦ by
  rw [mem_H₂_iff] at hg
  exact ⟨hg.1, 0, by omega⟩

/-- The parity subgroup is contained in the subgroup join `H₁ ⊔ H₂`. -/
lemma B_le_join : B ≤ H₁ ⊔ H₂ := by
  rintro g ⟨hy, k, hk⟩
  have hrepr : g = k • (⟨1, 0, 1⟩ : HeisenbergGroup) +
      (g.x - k) • (⟨1, 0, -1⟩ : HeisenbergGroup) := by
    ext <;> simp [HeisenbergGroup.zsmul_y_zero, hy]
    omega
  rw [hrepr]
  exact AddSubgroup.add_mem_sup ⟨k, rfl⟩ ⟨g.x - k, rfl⟩

/-- The subgroup join `H₁ ⊔ H₂` is exactly the parity subgroup `B`. -/
lemma join_eq_B : H₁ ⊔ H₂ = B :=
  le_antisymm (sup_le H₁_le_B H₂_le_B) B_le_join

/-- Membership in the subgroup join `H₁ ⊔ H₂` is the parity condition inside `C`. -/
lemma mem_join_iff (g : HeisenbergGroup) :
    g ∈ H₁ ⊔ H₂ ↔ g.y = 0 ∧ Even (g.x + g.z) := by simp [join_eq_B, B]

/-- `H₁ ≤ C`: elements of `H₁` have `y = 0`. -/
lemma H₁_le_C : H₁ ≤ C := fun g hg ↦ (mem_C_iff g).mpr ((mem_H₁_iff g).mp hg).1

/-- `H₂ ≤ C`: elements of `H₂` have `y = 0`. -/
lemma H₂_le_C : H₂ ≤ C := fun g hg ↦ (mem_C_iff g).mpr ((mem_H₂_iff g).mp hg).1

/-- `(2, 0, 0) = (1, 0, 1) + (1, 0, −1) ∈ H₁ ⊔ H₂`. -/
lemma two_mem_join : (⟨2, 0, 0⟩ : HeisenbergGroup) ∈ H₁ ⊔ H₂ := by
  exact (mem_join_iff _).2 ⟨rfl, 1, by norm_num⟩

/-- `(1, 0, 0) ∉ H₁ ⊔ H₂` because `x + z` must be even in the join. -/
lemma one_not_mem_join : (⟨1, 0, 0⟩ : HeisenbergGroup) ∉ H₁ ⊔ H₂ := fun h ↦
  absurd (sup_le H₁_le_B H₂_le_B h).2 (by norm_num)

/-- `(1, 0, 0) ∈ C \ (H₁ ⊔ H₂)`, witnessing that `H₁ ⊔ H₂ < C`. -/
lemma one_mem_C : (⟨1, 0, 0⟩ : HeisenbergGroup) ∈ C :=
  (mem_C_iff _).mpr rfl

/-- The subgroup join is not saturated: it contains `2 • (1, 0, 0)` but not `(1, 0, 0)`. -/
lemma join_not_saturated : ¬(H₁ ⊔ H₂).Saturated := by
  intro hsat
  have htwo : (2 : ℕ) • (⟨1, 0, 0⟩ : HeisenbergGroup) ∈ H₁ ⊔ H₂ := by
    simpa [two_nsmul] using two_mem_join
  exact one_not_mem_join ((hsat htwo).resolve_left (by norm_num))

/-- The join `H₁ ⊔ H₂` is not right-relatively convex. -/
lemma join_not_rrc : ¬(H₁ ⊔ H₂).IsRightRelativelyConvex := fun hrrc ↦
  join_not_saturated hrrc.saturated

/-- The subgroup join `H₁ ⊔ H₂` is strictly contained in `C`. -/
lemma join_lt_C : H₁ ⊔ H₂ < C :=
  lt_of_le_of_ne (sup_le H₁_le_C H₂_le_C) fun h ↦ one_not_mem_join (h ▸ one_mem_C)

/-! ## Least right-relatively convex subgroup -/

/-- Any RRC subgroup containing both `H₁` and `H₂` contains `(1, 0, 0)`. -/
lemma one_mem_of_rrc_containing {L : AddSubgroup HeisenbergGroup} (hL : L.IsRightRelativelyConvex)
    (h1 : H₁ ≤ L) (h2 : H₂ ≤ L) :
    (⟨1, 0, 0⟩ : HeisenbergGroup) ∈ L := by
  have htwo : (2 : ℕ) • (⟨1, 0, 0⟩ : HeisenbergGroup) ∈ L := by
    simpa [two_nsmul] using sup_le h1 h2 two_mem_join
  exact (hL.saturated htwo).resolve_left (by norm_num)

/-- Every RRC subgroup containing both `H₁` and `H₂` contains `C`. -/
lemma C_le_of_rrc_containing {L : AddSubgroup HeisenbergGroup} (hL : L.IsRightRelativelyConvex)
    (h1 : H₁ ≤ L) (h2 : H₂ ≤ L) :
    C ≤ L := by
  have h100 := one_mem_of_rrc_containing hL h1 h2
  have h001 : (⟨0, 0, 1⟩ : HeisenbergGroup) ∈ L :=
    L.sub_mem (h1 (AddSubgroup.mem_zmultiples _)) h100
  intro g hg
  rw [mem_C_iff] at hg
  convert L.add_mem (L.zsmul_mem h100 g.x) (L.zsmul_mem h001 g.z) using 1
  ext <;> simp [HeisenbergGroup.zsmul_y_zero, hg]

/-! ## Main theorem -/

/-- `C` is the least right-relatively convex subgroup containing `H₁` and `H₂`. -/
theorem C_isLeast_rrc_containing :
    C.IsRightRelativelyConvex ∧ H₁ ≤ C ∧ H₂ ≤ C ∧
    ∀ L : AddSubgroup HeisenbergGroup, L.IsRightRelativelyConvex →
    H₁ ≤ L → H₂ ≤ L → C ≤ L :=
  ⟨C_rrc, H₁_le_C, H₂_le_C, fun _ hL h1 h2 ↦ C_le_of_rrc_containing hL h1 h2⟩

/-- Concrete Heisenberg-group witness for the failure of closure of right-relatively convex
subgroups under subgroup joins. -/
theorem HeisenbergGroup.rrc_join_counterexample :
    (let : LinearOrder HeisenbergGroup := ord₁.toLinearOrder;
    (H₁ : Set HeisenbergGroup).OrdConnected) ∧
    (let : LinearOrder HeisenbergGroup := ord₂.toLinearOrder;
    (H₂ : Set HeisenbergGroup).OrdConnected) ∧
    (let : LinearOrder HeisenbergGroup := ordC.toLinearOrder;
    (C : Set HeisenbergGroup).OrdConnected) ∧
    H₁.IsRightRelativelyConvex ∧ H₂.IsRightRelativelyConvex ∧
    C.IsRightRelativelyConvex ∧ H₁ ⊔ H₂ = B ∧
    ¬(H₁ ⊔ H₂).IsRightRelativelyConvex ∧ H₁ ⊔ H₂ < C ∧
    H₁ ≤ C ∧ H₂ ≤ C ∧
    ∀ L : AddSubgroup HeisenbergGroup, L.IsRightRelativelyConvex →
    H₁ ≤ L → H₂ ≤ L → C ≤ L :=
  ⟨H₁_convex, H₂_convex, C_convex, H₁_rrc, H₂_rrc, C_rrc, join_eq_B, join_not_rrc,
    join_lt_C, H₁_le_C, H₂_le_C,
    fun _ hL h1 h2 ↦ C_le_of_rrc_containing hL h1 h2⟩

/-- **Kourovka Notebook, Problem 21.147.** There is a right-orderable group whose
right-relatively convex subgroups do not form a sublattice of the subgroup lattice. -/
theorem kourovka_21_147 :
    ∃ G : Type, ∃ _ : AddGroup G, ∃ _ : AddRightOrdering G,
    ∃ H K : AddSubgroup G,
    H.IsRightRelativelyConvex ∧ K.IsRightRelativelyConvex ∧
    ¬(H ⊔ K).IsRightRelativelyConvex :=
  ⟨HeisenbergGroup, inferInstance, ordC, H₁, H₂, H₁_rrc, H₂_rrc, join_not_rrc⟩

/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone, Daniel Morrison
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic.Ring

/-!
# The integer Heisenberg group

This file defines the integer Heisenberg group `HeisenbergGroup`, records its coordinate
formulas, and proves that it is noncommutative.
-/

/-- The integer Heisenberg group, consisting of triples `(x, y, z)` with group law
`(x₁, y₁, z₁) + (x₂, y₂, z₂) = (x₁ + x₂, y₁ + y₂, z₁ + z₂ + x₁ * y₂)`. -/
@[ext]
structure HeisenbergGroup where
  /-- The first coordinate. -/
  x : ℤ
  /-- The second coordinate. -/
  y : ℤ
  /-- The central coordinate. -/
  z : ℤ
  deriving DecidableEq

namespace HeisenbergGroup

/-- The zero element of `HeisenbergGroup`. -/
instance : Zero HeisenbergGroup := ⟨⟨0, 0, 0⟩⟩

/-- Heisenberg addition, with cross-term `x₁ * y₂` in the third coordinate. -/
instance : Add HeisenbergGroup :=
  ⟨fun a b ↦ ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩⟩

/-- The Heisenberg inverse: `-(x, y, z) = (-x, -y, -z + x * y)`. -/
instance : Neg HeisenbergGroup := ⟨fun a ↦ ⟨-a.x, -a.y, -a.z + a.x * a.y⟩⟩

/-- The `x`-coordinate of `0 : HeisenbergGroup` is `0`. -/
@[simp]
lemma zero_x : (0 : HeisenbergGroup).x = 0 := rfl

/-- The `y`-coordinate of `0 : HeisenbergGroup` is `0`. -/
@[simp]
lemma zero_y : (0 : HeisenbergGroup).y = 0 := rfl

/-- The `z`-coordinate of `0 : HeisenbergGroup` is `0`. -/
@[simp]
lemma zero_z : (0 : HeisenbergGroup).z = 0 := rfl

/-- The `x`-coordinate is additive: `(a + b).x = a.x + b.x`. -/
@[simp]
lemma add_x (a b : HeisenbergGroup) : (a + b).x = a.x + b.x := rfl

/-- The `y`-coordinate is additive: `(a + b).y = a.y + b.y`. -/
@[simp]
lemma add_y (a b : HeisenbergGroup) : (a + b).y = a.y + b.y := rfl

/-- The `z`-coordinate of a Heisenberg sum. -/
@[simp]
lemma add_z (a b : HeisenbergGroup) : (a + b).z = a.z + b.z + a.x * b.y := rfl

/-- The `x`-coordinate of the inverse: `(-a).x = -a.x`. -/
@[simp]
lemma neg_x (a : HeisenbergGroup) : (-a).x = -a.x := rfl

/-- The `y`-coordinate of the inverse: `(-a).y = -a.y`. -/
@[simp]
lemma neg_y (a : HeisenbergGroup) : (-a).y = -a.y := rfl

/-- The `z`-coordinate of the inverse. -/
@[simp]
lemma neg_z (a : HeisenbergGroup) : (-a).z = -a.z + a.x * a.y := rfl

/-- The integer Heisenberg group is an additive group. -/
instance : AddGroup HeisenbergGroup :=
  AddGroup.ofLeftAxioms (by intros; ext <;> simp <;> ring) (by intro; ext <;> simp)
    (by intro; ext <;> simp)

/-- The `x`-coordinate of a Heisenberg difference: `(a - b).x = a.x - b.x`. -/
@[simp]
lemma sub_x (a b : HeisenbergGroup) : (a - b).x = a.x - b.x := rfl

/-- The `y`-coordinate of a Heisenberg difference: `(a - b).y = a.y - b.y`. -/
@[simp]
lemma sub_y (a b : HeisenbergGroup) : (a - b).y = a.y - b.y := rfl

/-- The `z`-coordinate of a Heisenberg difference. -/
@[simp]
lemma sub_z (a b : HeisenbergGroup) : (a - b).z = a.z - b.z - (a.x - b.x) * b.y := by
  simp [sub_eq_add_neg]; ring

/-- The Heisenberg group is non-abelian. -/
lemma exists_add_ne_add_comm : ∃ a b : HeisenbergGroup, a + b ≠ b + a :=
  ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, by simp [HeisenbergGroup.ext_iff]⟩

/-- The `y`-coordinate projection `(x, y, z) ↦ y` as an additive group homomorphism. -/
def yHom : HeisenbergGroup →+ ℤ where
  toFun g := g.y
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value of `yHom` is the `y`-coordinate. -/
@[simp]
lemma yHom_apply (g : HeisenbergGroup) : yHom g = g.y := rfl

/-- In `HeisenbergGroup`, `n • (a, 0, c) = (n * a, 0, n * c)` because the cross-term vanishes. -/
lemma zsmul_y_zero (n : ℤ) (a c : ℤ) :
    n • (⟨a, 0, c⟩ : HeisenbergGroup) = ⟨n * a, 0, n * c⟩ := by
  induction n using Int.induction_on with
  | zero => ext <;> simp
  | succ n ih | pred n ih => ext <;> simp_all [add_zsmul, sub_zsmul] <;> ring

end HeisenbergGroup

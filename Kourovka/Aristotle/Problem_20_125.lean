/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Kourovka Notebook Problem 20.125

We prove the existence of a non-abelian group `G` and a Rota–Baxter operator `B : G → G`
that is surjective but not injective.

## Construction

The witness is `G = S₃ × ℤ^ℕ` (the direct product of the symmetric group on three elements
with the countable direct product of copies of `ℤ`), equipped with the operator
`B(σ, f) = (σ⁻¹, shift f)` where `shift f(n) = f(n + 1)`.

- **Rota–Baxter equation**: In a direct product `H × A` with `A` abelian, the conjugation
  terms in the `A`-component cancel by commutativity, and the `H`-component gives
  `σ⁻¹ τ⁻¹ = (τ σ)⁻¹ = B(τ σ, ...)₁`.

- **Surjectivity**: Given any `(τ, g)`, the preimage `(τ⁻¹, (1, g 0, g 1, …))` maps
  to it under `B`.

- **Non-injectivity**: Two sequences differing only at index 0 have the same shift.

- **Non-abelian**: `S₃` is non-abelian.
-/

open Equiv

/-- A **Rota–Baxter operator** on a group `G` is a map `B : G → G` satisfying
`B(a) * B(b) = B(a * B(a) * b * B(a)⁻¹)` for all `a, b ∈ G`. -/
def IsRotaBaxter {G : Type*} [Group G] (B : G → G) : Prop :=
  ∀ a b, B a * B b = B (a * B a * b * (B a)⁻¹)

/-- The witness group for Kourovka Problem 20.125: `S₃ × ℤ^ℕ`, i.e. the direct product
of the symmetric group on three elements with the countable product of copies of `ℤ`. -/
abbrev KG := Perm (Fin 3) × (ℕ → Multiplicative ℤ)

/-- The Rota–Baxter operator on `KG`: invert the permutation and shift the sequence. -/
def KB : KG → KG := fun p ↦ (p.1⁻¹, fun n ↦ p.2 (n + 1))

/-- `KB` satisfies the Rota–Baxter equation. The permutation component follows from
`inv_mul_cancel` and the `ℤ^ℕ` component from commutativity of `ℤ`. -/
lemma KB_isRotaBaxter : IsRotaBaxter KB :=
  fun a b ↦ by ext <;> simp [KB]; abel

/-- `KB` is surjective: any `(τ, g)` is the image of `(τ⁻¹, (1, g 0, g 1, …))`. -/
lemma KB_surjective : KB.Surjective := fun x ↦
  ⟨⟨x.1⁻¹, fun n ↦ if n = 0 then 1 else x.2 (n - 1)⟩, by simp [KB]⟩

/-- `KB` is not injective: sequences differing only at index 0 have the same shift. -/
lemma KB_not_injective : ¬KB.Injective := by
  norm_num [Function.Injective]
  exact ⟨1, fun n ↦ if n = 0 then .ofAdd 1 else 1, 1, fun _ ↦ 1, by ext <;> simp [KB], by
    simp [funext_iff]⟩

/-- `KG` is non-abelian: the transpositions `(0 1)` and `(0 2)` in `S₃` do not commute. -/
lemma KG_nonabelian : ∃ a b : KG, a * b ≠ b * a :=
  ⟨(swap 0 1, 1), (swap 0 2, 1), by simp only [ne_eq, Prod.mk_mul_mk, Prod.mk.injEq]; decide⟩

/-- **Kourovka Notebook, Problem 20.125.** There exists a non-abelian group and a
Rota–Baxter operator on it that is surjective but not injective. The witness is
`G = S₃ × ℤ^ℕ` with `B(σ, f) = (σ⁻¹, shift f)`. -/
theorem kourovka_20_125 :
    IsRotaBaxter KB ∧ KB.Surjective ∧ ¬KB.Injective ∧ (∃ a b : KG, a * b ≠ b * a) :=
  ⟨KB_isRotaBaxter, KB_surjective, KB_not_injective, KG_nonabelian⟩

/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone
-/
import Kourovka.Mathlib.RotaBaxter
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

/-!
# Kourovka Notebook Problem 20.125

We prove the existence of a non-abelian group `G` and a Rota–Baxter operator `B : G → G`
that is surjective but not injective.

## Construction

Consider `G := S₃ × ℤ^ℕ` (the direct product of the symmetric group on three elements
with the sequences of integers inheriting the group structure from `ℤ`), and the map
`B(σ, f) := (σ⁻¹, shift f)` where `(shift f)(n) = f(n + 1)`.

- **Non-abelian**: `S₃` is non-abelian, therefore the cartesian product is.

- **Rota–Baxter equation**: In a direct product `H × A` with `A` abelian, the conjugation
  terms in the `A`-component cancel by commutativity, and the `H`-component gives
  `σ⁻¹ τ⁻¹ = (τ σ)⁻¹ = B(τ σ, ...)₁`.

- **Surjectivity**: Given any `(τ, g)`, the preimage `(τ⁻¹, (0, g 0, g 1, …))` maps
  to it under `B`.

- **Non-injectivity**: Two sequences differing only at index 0 have the same shift.

-/

open Equiv Function

section Shift

/-- `shift` applied to a sequence `f` forgets `f(0)` and reindexes the tail of the sequence. -/
def shift : (ℕ → ℤ) →+ (ℕ → ℤ) where
  toFun f := fun n ↦ f (n + 1)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `shift` is an endomorphism in the abelian group of integer sequences,
hence it is a Rota-Baxter operator. -/
theorem shift_isAddRotaBaxter : IsAddRotaBaxter shift := by
  simp only [isAddRotaBaxter_iff_add, map_add, implies_true]

/-- Given a sequence `g`, prepending `0` produces a sequence `f` so that `shift f = g`. -/
theorem shift_surjective : Surjective shift :=
  fun g ↦ ⟨fun n ↦ if n = 0 then 0 else g (n - 1), funext fun n ↦ by cases n <;> rfl⟩

/-- Two sequences differing only at index 0 have the same shift, hence `shift` is not injective. -/
theorem shift_not_injective : ¬Injective shift := by
  intro h
  simpa using congr_fun (h (by ext n; cases n <;> rfl : shift 0 = shift (Pi.single 0 1))) 0

end Shift


/-- The witness group for Kourovka Problem 20.125: `S₃ × ℤ^ℕ`, i.e. the direct product
of the symmetric group on three elements with the countable product of copies of `ℤ`. -/
abbrev KG := Perm (Fin 3) × Multiplicative (ℕ → ℤ)

/-- The map `KB` inverts the permutation on the first factor of `KG` and applies `shift`
on the second factor of `KG`. -/
def KB : KG → KG := Prod.map Inv.inv shift

/-- `S₃ × ℤ^ℕ` is non-abelian because `S₃` is. -/
theorem KG_nonabelian : ∃ a b : KG, a * b ≠ b * a := by
  refine ⟨(swap 0 1, 1), (swap 0 2, 1), fun h ↦ ?_⟩
  simpa [Prod.mk_mul_mk, swap_apply_def] using Perm.congr_fun (congrArg Prod.fst h) 1

/-- **Kourovka Notebook, Problem 20.125.** There exists a non-abelian group and a Rota–Baxter
operator on it that is surjective but not injective. The witness is `G := S₃ × ℤ^ℕ` with
`B(σ, f) := (σ⁻¹, shift f)`. -/
theorem kourovka_20_125 :
  ∃ (G : Type) (_ : Group G) (B : G → G),
    (∃ a b : G, a * b ≠ b * a) ∧ IsRotaBaxter B ∧ Surjective B ∧ ¬Injective B := by
  refine ⟨KG, inferInstance, KB, KG_nonabelian, ?_, ?_, ?_⟩
  · exact inv_isRotaBaxter.prodMap shift_isAddRotaBaxter
  · exact inv_surjective.prodMap shift_surjective
  · rw [KB, Prod.map_injective, not_and_or]; exact Or.inr shift_not_injective

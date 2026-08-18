/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Mathlib.Data.Fintype.Perm

/-!
# Kourovka Notebook Problem 18.50

The statement of record for the Palomar submission: it uses Mathlib alone and introduces no
definitions of its own. The proof is in `Kourovka/Problem_18_50.lean`, and the `sorry` below marks
where Comparator checks it against this statement.

For every `n` and every `k` with `1 ≤ k ≤ n!`, there exists a group `G` with `n` pairwise distinct
elements `g₀, …, gₙ₋₁` whose permuted products `g_{σ(0)} · … · g_{σ(n-1)}` over `σ ∈ Sₙ` realise
*exactly* `k` distinct values. Problem 18.50, proposed by S. Kohl, asks whether every such `k`
occurs; it does.

## Reading the statement

* `g : Fin n → G` with `g.Injective` is the `n` pairwise distinct elements, indexed from `0` where
  the informal account counts from `1`.
* `(univ.image …).card` counts the *set* of permuted products, so coincidences collapse.
* The existential supplies `DecidableEq G` only so that `Finset.image` can be formed. It comes with
  the witness rather than being assumed of an arbitrary group, so it weakens nothing.
* `∃ (G : Type)` places the witness in the smallest universe, which is the stronger claim.
* `n = 0` holds for the right reason: `0! = 1` forces `k = 1`, and the empty product is the only
  permuted product.

## Provenance

Discovered and formalised in Lean by Aristotle (Harmonic); the informal account was written from
the formal proof afterwards. Accepted into issue 21 of the Kourovka Notebook, and recorded by Kohl
as the accepted answer to his own 2013 MathOverflow question 123890. Companion preprint:
arXiv:2607.17477.

`Palomar/Problem_18_50/formalization.yaml` holds the full record: sources, authorship, review, and
the divergences between this statement and the informal account. The repository-root
`formalization.yaml` covers all nine results in this repository.
-/

open Finset Equiv

/-- **Kourovka Notebook Problem 18.50.**

For every `n` and every `k` with `1 ≤ k ≤ n!`, there is a group `G` together with `n` pairwise
distinct elements `g₀, …, gₙ₋₁ ∈ G` whose permuted products `g_{σ(0)} * ⋯ * g_{σ(n-1)}`, taken
over all `σ ∈ Sₙ`, realise exactly `k` distinct values. -/
theorem kourovka_18_50 (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n.factorial) :
    ∃ (G : Type) (_ : Group G) (_ : DecidableEq G) (g : Fin n → G),
      g.Injective ∧
        (univ.image (fun σ : Perm (Fin n) ↦ (List.ofFn (fun i : Fin n ↦ g (σ i))).prod)).card = k :=
  sorry

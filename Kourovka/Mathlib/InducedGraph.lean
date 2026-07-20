/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic.Zify

/-!
# Induced paths and cycles in graphs

This file develops the basic theory of induced paths and cycles in a `SimpleGraph`, phrased through
the induced-containment relation `⊴`. `HasIndPath` and `HasIndCycle` record the existence of an
induced `pathGraph` or `cycleGraph`, while `IsCograph` and `IsChordal` are the associated
forbidden-subgraph properties: a cograph has no induced `P₄`, and a chordal graph has no induced
cycle of length at least `4`. The main results are monotonicity of these notions along `⊴` and the
fact that an induced `n`-cycle contains an induced `m`-path whenever `m < n`.
-/

namespace SimpleGraph

variable {V : Type*}

/-! ## Definitions -/

/-- `G` has an induced path on `n` vertices. -/
abbrev HasIndPath (G : SimpleGraph V) (n : ℕ) : Prop :=
  pathGraph n ⊴ G

/-- A cograph is a graph with no induced `P₄`. -/
def IsCograph (G : SimpleGraph V) : Prop :=
  ¬G.HasIndPath 4

/-- `G` has an induced cycle on `n` vertices. -/
abbrev HasIndCycle (G : SimpleGraph V) (n : ℕ) : Prop :=
  cycleGraph n ⊴ G

/-- A chordal graph is a graph with no induced cycle of length at least `4`. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, 4 ≤ n → ¬G.HasIndCycle n

/-! ## Properties -/

variable {G H : SimpleGraph V} {n m : ℕ}

/-- If `G ⊴ H` and `G` has an induced path on `n` vertices, then so does `H`. -/
theorem HasIndPath.mono (hGH : G ⊴ H) (hG : G.HasIndPath n) : H.HasIndPath n :=
  hG.trans hGH

/-- If `G ⊴ H` and `H` is a cograph, then so is `G`. -/
theorem IsCograph.anti (hGH : G ⊴ H) (hH : H.IsCograph) : G.IsCograph :=
  fun hP ↦ hH <| hP.trans hGH

/-- If `G ⊴ H` and `G` has an induced cycle on `n` vertices, then so does `H`. -/
theorem HasIndCycle.mono (hGH : G ⊴ H) (hG : G.HasIndCycle n) : H.HasIndCycle n :=
  hG.trans hGH

/-- If `G ⊴ H` and `H` is chordal, then so is `G`. -/
theorem IsChordal.anti (hGH : G ⊴ H) (hH : H.IsChordal) : G.IsChordal :=
  fun n hn hC ↦ hH n hn <| hC.trans hGH

/-- `H'` is induced-contained in `G` exactly when `G` is the comap of some vertex embedding. -/
theorem isIndContained_iff_exists_comap_eq {W : Type*} {H' : SimpleGraph W} :
    H' ⊴ G ↔ ∃ (f : W ↪ V), G.comap f = H' := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toEmbedding, by ext a b; simpa only [comap_adj] using e.map_adj_iff⟩
  · rintro ⟨f, rfl⟩
    exact ⟨Embedding.comap f G⟩

/-- The path on `m` vertices is an induced subgraph of the cycle on `n` vertices whenever
`m < n`. -/
theorem pathGraph_isIndContained_cycleGraph_of_lt (h : m < n) :
    pathGraph m ⊴ cycleGraph n := by
  rw [isIndContained_iff_exists_comap_eq]
  use Fin.castLEEmb h.le
  ext x y
  simp_rw [comap_adj, cycleGraph_adj', pathGraph_adj,
    Fin.castLEEmb_apply, Fin.val_sub, Fin.val_castLE, or_comm]
  refine or_congr ?_ ?_
  all_goals constructor <;> intro hmod
  · by_cases hxy : x.val ≤ y.val
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
      omega
    · rw [Nat.mod_eq_of_lt (by omega : n - x.val + y.val < n)] at hmod
      omega
  · simp [show n - x + y = n + 1 by omega, Nat.mod_eq_of_lt (by omega : 1 < n)]
  · by_cases hyx : y.val ≤ x.val
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
      omega
    · rw [Nat.mod_eq_of_lt (by omega : n - y.val + x.val < n)] at hmod
      omega
  · simp [show n - y + x = n + 1 by omega, Nat.mod_eq_of_lt (by omega : 1 < n)]

/-- An induced `n`-cycle contains an induced `m`-path for every `m < n`. -/
theorem HasIndCycle.hasIndPath_of_lt (hG : G.HasIndCycle n) (h : m < n) :
    G.HasIndPath m :=
  (pathGraph_isIndContained_cycleGraph_of_lt h).trans hG

end SimpleGraph

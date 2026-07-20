/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Kourovka.Mathlib.LehmerCode
import Mathlib.Data.ZMod.Basic

/-!
# Kourovka Notebook Problem 18.50

For every `n` and every `k` with `1 ≤ k ≤ n!`, there exists a group `G` with `n` pairwise
distinct elements `g₀, …, gₙ₋₁` whose permuted products `g_{σ(0)} · … · g_{σ(n-1)}` over
`σ ∈ Sₙ` realise *exactly* `k` distinct values.

The witness is a twisted group `G = ℤⁿ × ℤ/kℤ` whose central component records the
factorial rank of a permutation modulo `k`; surjectivity of the factorial rank
`Sₙ → {0, …, n!−1}` then exhibits all `k` residues, while no other product values can
appear because of the product formula `P(σ) = ((1, …, 1), factRank(σ) mod k)`.

## Main results

* `TwGrp` : the twisted group `ℤⁿ × ℤ/kℤ`.
* `gElem` : the distinguished elements `gⱼ = (eⱼ, 0)`.
* `factRank_injective`, `factRank_surj` : the factorial rank is a bijection
  `Sₙ → {0, …, n!−1}`.
* `permProd_eq` : the product formula `permProd n k σ = ((1,…,1), factRank σ mod k)`.
* `products_card` : the number of distinct permuted products equals `k`.
* `kourovka_18_50` : the main theorem.

## Structure

1. **Bilinear form** `B` and its properties.
2. **Twisted group** `G = ℤⁿ × ℤ/kℤ` with the modified multiplication.
3. **Distinguished elements** `gⱼ = (eⱼ, 0)`.
4. **Product formula** `P(σ) = ((1, …, 1), factRank(σ) mod k)`.
5. **Counting argument** and the main theorem.
-/

open Finset BigOperators Equiv

/-! ## Part 1: The Bilinear Form -/

/-- The bilinear form B as an integer:
    B(u, v) = ∑_{i < j} u_j * v_i * j! -/
def B_int (n : ℕ) (u v : Fin n → ℤ) : ℤ :=
  ∑ j : Fin n, ∑ i : Fin n, if i.val < j.val then u j * v i * (j.val.factorial : ℤ) else 0

/-- `B` is left-additive: `B(u₁ + u₂, v) = B(u₁, v) + B(u₂, v)`. -/
lemma B_int_add_left (n : ℕ) (u₁ u₂ v : Fin n → ℤ) :
    B_int n (u₁ + u₂) v = B_int n u₁ v + B_int n u₂ v := by
  simp only [B_int, Fin.val_fin_lt, Pi.add_apply, add_mul]
  simpa only [← sum_add_distrib] using
    sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by split_ifs <;> ring

/-- `B` is right-additive: `B(u, v₁ + v₂) = B(u, v₁) + B(u, v₂)`. -/
lemma B_int_add_right (n : ℕ) (u v₁ v₂ : Fin n → ℤ) :
    B_int n u (v₁ + v₂) = B_int n u v₁ + B_int n u v₂ := by
  simp only [B_int, Fin.val_fin_lt, Pi.add_apply]
  simpa only [← sum_add_distrib] using
    sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by split_ifs <;> ring

/-- `B` vanishes on the left zero: `B(0, v) = 0`. -/
lemma B_int_zero_left (n : ℕ) (v : Fin n → ℤ) : B_int n 0 v = 0 :=
  sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ by simp

/-- `B` vanishes on the right zero: `B(u, 0) = 0`. -/
lemma B_int_zero_right (n : ℕ) (u : Fin n → ℤ) : B_int n u 0 = 0 := by simp [B_int, mul_zero]

/-- `B` is left-antilinear with respect to negation: `B(-u, v) = -B(u, v)`. -/
lemma B_int_neg_left (n : ℕ) (u v : Fin n → ℤ) : B_int n (-u) v = -B_int n u v := by
  simp only [B_int, Fin.val_fin_lt, Pi.neg_apply, neg_mul, ← sum_neg_distrib]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by split_ifs <;> ring

/-! ## Part 2: The Twisted Group -/

/-- The twisted group: G = ℤⁿ × ℤ/kℤ with multiplication
    (u, r)(v, s) = (u + v, r + s + B(u, v)). -/
@[ext]
structure TwGrp (n : ℕ) (k : ℕ) where
  vec : Fin n → ℤ
  cent : ZMod k

/-- Decidable equality on the twisted group, derived componentwise. -/
instance instDecidableEqTwGrp (n k : ℕ) : DecidableEq (TwGrp n k) := fun a b ↦ by
  cases a with
  | mk va ca =>
    cases b with
    | mk vb cb =>
      rw [TwGrp.mk.injEq]
      exact instDecidableAnd

/-- The group structure on `TwGrp n k`. Associativity reduces to the bilinearity identity
`B(u, v) + B(u + v, w) = B(v, w) + B(u, v + w)`; the left inverse is
`(-u, -r + B(u, u)) · (u, r) = (0, B(u, u) + B(-u, u)) = (0, 0)` since `B(-u, u) = -B(u, u)`. -/
instance instGroupTwGrp (n k : ℕ) : Group (TwGrp n k) where
  mul a b := ⟨a.vec + b.vec, a.cent + b.cent + Int.cast (B_int n a.vec b.vec)⟩
  one := ⟨0, 0⟩
  inv a := ⟨-a.vec, -a.cent + Int.cast (B_int n a.vec a.vec)⟩
  mul_assoc := by
    intros a b c
    apply TwGrp.ext
    · exact add_assoc _ _ _
    · show
        (a.cent + b.cent + ↑(B_int n a.vec b.vec) + c.cent + ↑(B_int n (a.vec + b.vec) c.vec) :
            ZMod k) =
          (a.cent + (b.cent + c.cent + ↑(B_int n b.vec c.vec)) +
              ↑(B_int n a.vec (b.vec + c.vec)) :
            ZMod k)
      push_cast [B_int_add_left, B_int_add_right]
      ring
  one_mul := by
    intro a
    ext
    · exact zero_add _
    · show (0 + a.cent + B_int n 0 a.vec : ZMod k) = a.cent
      simp [B_int_zero_left]
  mul_one := by
    intro a
    ext
    · exact add_zero _
    · show (a.cent + 0 + B_int n a.vec 0 : ZMod k) = a.cent
      simp [B_int_zero_right]
  inv_mul_cancel := by
    intro a
    ext
    · exact neg_add_cancel _
    · show (-a.cent + B_int n a.vec a.vec : ZMod k) + a.cent + B_int n (-a.vec) a.vec = 0
      simp only [B_int_neg_left]; push_cast; ring

/-! ## Part 3: Distinguished Elements -/

/-- Standard basis vector e_j ∈ ℤⁿ. -/
def stdBasisInt (n : ℕ) (j : Fin n) : Fin n → ℤ := fun i ↦ if i = j then 1 else 0

/-- The j-th distinguished element g_j = (e_j, 0). -/
def gElem (n k : ℕ) (j : Fin n) : TwGrp n k :=
  ⟨stdBasisInt n j, 0⟩

/-- Standard basis vectors `eⱼ` are pairwise distinct. -/
lemma stdBasisInt_injective (n : ℕ) : (stdBasisInt n).Injective := fun i j hij ↦ by
  simpa [stdBasisInt] using congr_fun hij i

/-- The distinguished elements are pairwise distinct. -/
lemma gElem_injective (n k : ℕ) : (gElem n k).Injective := fun _ _ h ↦
  stdBasisInt_injective n (TwGrp.mk.inj h).1

/-- Evaluation of `B` on standard basis vectors: `B(e_a, e_b) = a!` if `b < a`, else `0`. -/
lemma B_int_stdBasis (n : ℕ) (a b : Fin n) :
    B_int n (stdBasisInt n a) (stdBasisInt n b) =
      if b.val < a.val then (a.val.factorial : ℤ) else 0 := by
  unfold B_int stdBasisInt
  split_ifs <;> simp_all [sum_ite, filter_lt_eq_Ioi]

/-- The sum of all standard basis vectors is the all-ones function. -/
lemma sum_stdBasisInt (n : ℕ) : ∑ j : Fin n, stdBasisInt n j = fun _ ↦ 1 := by
  funext i
  unfold stdBasisInt
  have :
    ∀ (s : Finset (Fin n)),
      (∑ j ∈ s, fun (k : Fin n) ↦ if k = j then (1 : ℤ) else 0) i =
        ∑ j ∈ s, if i = j then (1 : ℤ) else 0 := by
    intro s
    induction s using cons_induction with
    | empty => simp
    | cons a s ha ih => rw [sum_cons, sum_cons, Pi.add_apply, ih]
  rw [this]
  simp

/-- Permutation invariance of the sum of standard basis vectors. -/
lemma sum_stdBasisInt_perm (n : ℕ) (σ : Perm (Fin n)) :
    ∑ j : Fin n, stdBasisInt n (σ j) = fun _ ↦ 1 := by
  convert sum_stdBasisInt n using 1
  conv_rhs => rw [← Equiv.sum_comp σ]

/-! ## Part 4: Product Formula -/

/-- The product g_{σ(0)} * g_{σ(1)} * ... * g_{σ(n-1)}. -/
def permProd (n k : ℕ) (σ : Perm (Fin n)) : TwGrp n k :=
  (List.ofFn (fun i : Fin n ↦ gElem n k (σ i))).prod

/-- The `vec` component of a list product is the sum of the `vec` components, by induction
on the list using the definitional unfolding `(a * b).vec = a.vec + b.vec` at each `cons` step. -/
lemma list_prod_vec {n k : ℕ} :
    ∀ (l : List (TwGrp n k)), l.prod.vec = (l.map TwGrp.vec).foldr (· + ·) 0
  | [] => by simp [List.prod_nil, show (1 : TwGrp n k).vec = 0 from rfl]
  | a :: l => by
    induction l generalizing a <;>
      simp_all [List.prod_cons,
        show ∀ (x y : TwGrp n k), (x * y).vec = x.vec + y.vec from fun _ _ ↦ rfl]

/-- The vector component of `permProd n k σ` is the all-ones function. -/
lemma permProd_vec (n k : ℕ) (σ : Perm (Fin n)) : (permProd n k σ).vec = fun _ ↦ 1 := by
  have h_map :
    (List.ofFn (fun i : Fin n ↦ gElem n k (σ i))).map TwGrp.vec =
      List.ofFn (fun i : Fin n ↦ stdBasisInt n (σ i)) := by
    simp only [gElem, List.map_ofFn, List.ofFn_inj]
    rfl
  convert list_prod_vec _ using 1
  rw [h_map, List.ofFn_eq_map]
  convert sum_stdBasisInt_perm n σ |> Eq.symm using 1

/-- The pairwise sum of B_int values over position pairs with l < m. -/
def pairwiseB (n : ℕ) (σ : Perm (Fin n)) : ℤ :=
  ∑ l : Fin n,
    ∑ m : Fin n, if l.val < m.val then B_int n (stdBasisInt n (σ l)) (stdBasisInt n (σ m)) else 0

set_option maxHeartbeats 800000 in
/-- The `cent` component of a list product whose terms all have zero `cent` equals the sum of
pairwise `B` values. The proof is by induction on the list, applying bilinearity of `B` at
each `cons` step. -/
lemma list_prod_cent_zero {n k : ℕ} :
    ∀ (l : List (TwGrp n k)) (_ : ∀ a ∈ l, a.cent = 0), ∃ (s : ℤ), l.prod.cent = Int.cast s ∧
      s = ∑ i : Fin l.length,
        ∑ j : Fin l.length, if i.val < j.val then B_int n (l.get i).vec (l.get j).vec else 0
  | [], _ => ⟨0, by simp [show (1 : TwGrp n k).cent = 0 from rfl], by simp⟩
  | a :: l, h => by
    induction' l with b l ih generalizing a <;>
      simp_all [Fin.sum_univ_succ,
        show ∀ (x y : TwGrp n k), (x * y).cent = x.cent + y.cent + Int.cast (B_int n x.vec y.vec)
            from fun _ _ ↦ rfl]
    · show _ = _
      rw [show (b * l.prod).vec = b.vec + l.prod.vec from rfl, B_int_add_right]
      ring_nf
      rw [show B_int n a.vec l.prod.vec = ∑ x : Fin l.length, B_int n a.vec l[↑x].vec from ?_]
      push_cast
      ring_nf
      · congr! 2
      · have h_sum : l.prod.vec = List.foldr (· + ·) 0 (List.map TwGrp.vec l) := list_prod_vec l
        have h_sum :
          ∀ (l : List (Fin n → ℤ)),
            B_int n a.vec (List.foldr (· + ·) 0 l) = ∑ x : Fin l.length, B_int n a.vec l[x] := by
          intro l
          induction l <;> simp_all [Fin.sum_univ_succ]
          ring_nf
          · exact B_int_zero_right n a.vec
          · rw [←
              ‹B_int n a.vec (List.foldr (fun x1 x2 ↦ x1 + x2) 0 _) =
                  (List.map (B_int n a.vec) _).sum›,
              B_int_add_right]
        convert h_sum (List.map TwGrp.vec l) using 1
        · congr! 1
        · simp only [Fin.getElem_fin, List.getElem_map]
          convert rfl <;> grind

/-- The pairwise `B` sum equals `factRank` (cast to `ℤ`). This is a sum rearrangement: group
inversions by their larger element `j`, noting that each inversion `(j, i)` with `i < j`
contributes `j!` to the sum. -/
lemma pairwiseB_eq_factRank (n : ℕ) (σ : Perm (Fin n)) : pairwiseB n σ = (factRank σ : ℤ) := by
  unfold pairwiseB factRank
  simp only [Fin.val_fin_lt, B_int_stdBasis, invCount_eq_card_avail_after, Perm.coe_inv,
    Nat.cast_sum, Nat.cast_mul]
  simp [sum_ite, filter_filter]
  refine sum_bij (fun x _ ↦ σ x) ?_ ?_ ?_ ?_ <;> simp
  exact σ.surjective

/-- The central component of `permProd n k σ` equals `factRank σ` reduced modulo `k`. -/
lemma permProd_cent (n k : ℕ) (σ : Perm (Fin n)) : (permProd n k σ).cent = (factRank σ : ZMod k) := by
  obtain ⟨s, hs⟩ := list_prod_cent_zero (List.ofFn fun i ↦ gElem n k (σ i)) (by simp [gElem])
  convert hs.1 using 1
  convert congr_arg ((↑) : ℤ → ZMod k) (pairwiseB_eq_factRank n σ |> Eq.symm) using 1
  · norm_cast
  · convert congr_arg ((↑) : ℤ → ZMod k) hs.2 using 1
    simp only [pairwiseB, Fin.val_fin_lt, Int.cast_sum, Int.cast_ite, Int.cast_zero, gElem,
      List.get_eq_getElem, List.getElem_ofFn]
    convert rfl <;> grind

/-- Full characterization: permProd equals the explicit pair. -/
lemma permProd_eq (n k : ℕ) (σ : Perm (Fin n)) :
    permProd n k σ = ⟨fun _ ↦ 1, (factRank σ : ZMod k)⟩ := by
  ext
  · exact congr_fun (permProd_vec n k σ) _
  · exact permProd_cent n k σ

/-! ## Part 5: Counting Argument -/

/-- The natural-number range `{0, …, m − 1}` surjects onto `ZMod k` whenever `k ≤ m`. -/
lemma natCast_range_surj_zmod (k m : ℕ) (hk : 0 < k) (hm : k ≤ m) :
    ∀ r : ZMod k, ∃ i ∈ range m, (i : ZMod k) = r := by
  rcases k with (_ | _ | k) <;> simp_all [ZMod]
  · exact ⟨0, hm⟩
  · exact fun r ↦ ⟨r, by omega, by simp⟩

/-- The composition `factRank` followed by `Nat.cast : ℕ → ZMod k` covers all of `ZMod k`. -/
lemma factRank_mod_surj (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n.factorial) :
    ∀ r : ZMod k, ∃ σ : Perm (Fin n), (factRank σ : ZMod k) = r := by
  intro r
  obtain ⟨r', hr', hr⟩ : ∃ r' ∈ range (n.factorial), (r' : ZMod k) = r :=
    natCast_range_surj_zmod k n.factorial hk hkn r
  exact (factRank_surj r' (Finset.mem_range.mp hr')).elim fun σ hσ ↦ ⟨σ, hσ.symm ▸ hr⟩

/-- The image of `σ ↦ permProd n k σ` has cardinality exactly `k`, the counting argument
that produces the required `k` distinct permuted products. -/
lemma products_card (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n.factorial) :
    (univ.image (fun σ : Perm (Fin n) ↦ permProd n k σ)).card = k := by
  have h_image :
    Finset.image (fun σ : Perm (Fin n) ↦ permProd n k σ) univ =
      Finset.image (fun σ : Perm (Fin n) ↦ ⟨fun _ ↦ 1, (factRank σ : ZMod k)⟩) univ :=
    image_congr fun σ _ ↦ permProd_eq n k σ ▸ rfl
  rcases k with (_ | _ | k) <;> simp_all
  · simp only [card_eq_one, Finset.ext_iff, mem_image, mem_univ, true_and, mem_singleton]
    refine ⟨⟨fun _ ↦ 1, 0⟩, fun a ↦ ?_⟩
    constructor <;> intro h <;> rcases a with ⟨a, b⟩ <;> simp_all [ZMod]
    grind
  · rw [card_eq_of_bijective]
    use fun i hi ↦ ⟨fun _ ↦ 1, i⟩
    · simp only [mem_image, mem_univ, true_and, Order.lt_add_one_iff, exists_prop,
        forall_exists_index, forall_apply_eq_imp_iff, TwGrp.mk.injEq] at *
      refine fun σ ↦
        ⟨factRank σ % (k + 1 + 1), Nat.le_of_lt_succ <| Nat.mod_lt _ <| Nat.succ_pos _, ?_⟩
      simp [ZMod.natCast_mod]
    · intro i hi
      have := factRank_mod_surj n (k + 1 + 1) (by omega) (by omega) (i : ZMod (k + 1 + 1))
      aesop
    · refine fun i j hi hj h ↦
        Nat.mod_eq_of_lt (?_ : i < k + 2) ▸ Nat.mod_eq_of_lt (?_ : j < k + 2) ▸ ?_
      · omega
      · omega
      · simpa [ZMod.natCast_eq_natCast_iff'] using h

/-- **Kourovka Notebook Problem 18.50.**

For every `n` and every `k` with `1 ≤ k ≤ n!`, there exists a (decidable) group `G` together
with `n` pairwise distinct elements `g₀, …, gₙ₋₁ ∈ G` whose permuted products
`g_{σ(0)} · … · g_{σ(n−1)}` over `σ ∈ Sₙ` realise *exactly* `k` distinct values.

The witness is the twisted group `TwGrp n k = ℤⁿ × ℤ/kℤ` with the cocycle
`B(u, v) = ∑_{i < j} u_j · v_i · j!`, taking `gⱼ = (eⱼ, 0)`. -/
theorem kourovka_18_50 (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n.factorial) :
    ∃ (G : Type) (_ : Group G) (_ : DecidableEq G) (g : Fin n → G),
      g.Injective ∧
        (univ.image (fun σ : Perm (Fin n) ↦ (List.ofFn (fun i : Fin n ↦ g (σ i))).prod)).card = k :=
  ⟨TwGrp n k, instGroupTwGrp n k, instDecidableEqTwGrp n k, gElem n k, gElem_injective n k,
    products_card n k hk1 hkn⟩

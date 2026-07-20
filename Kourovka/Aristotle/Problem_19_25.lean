/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Aut
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.GCD

/-!
# Kourovka Notebook Problem 19.25

The Kourovka Notebook problem 19.25 of B. Curtin and G. R. Pourgholi asks whether two
finite groups `G` and `H` of the same order with the same element-totient sum
`∑_{g ∈ G} φ(|g|) = ∑_{h ∈ H} φ(|h|)` must both be simple if one of them is. We give a
negative answer: there exist two finite groups of order `6048` with totient sum `23984`,
one of which is the simple group `PSU(3, 3)` and the other a non-simple direct product.

## Main results

* `kourovka_19_25`: the negative resolution of the question, formulated as the negation
  of the predicate `SameCardTotientSumSimpleTransfer`.
* `not_same_card_totient_sum_simple_transfer`: same statement, exhibiting `G` and the
  original counterexample `H = C₆ × S₄ × (C₇ ⋊ C₆)`.
* `exists_wreath_counterexample`: same conclusion using the alternative non-simple
  partner `H' = C₂ × (C₆ ≀ S₂) × (C₇ ⋊ C₆)`.

## Outline

1. **Simple-group normal-closure criterion** (`SimpleGroupCriterion`,
   `FinsetSimpleGroupCriterion`): a reusable interface for proving simplicity by checking
   that a generating set lies in the normal closure of every nontrivial conjugacy-class
   representative.
2. **The simple group `PSU(3, 3)` as a permutation subgroup of `S₂₈`** (namespace
   `KourovkaNotebook.PSU33Perm`): an explicit Cayley-style enumeration of the 6048
   elements of `G = ⟨a, b⟩ ≤ S₂₈`, together with the GAP-derived class-representative and
   normal-closure data.
3. **Element-order spectrum** (namespace `SameCardTotientSum`): definitions and
   computability lemmas used to evaluate `∑ φ(|g|)` on direct products and semidirect
   products.
4. **The non-simple partner `H` and the wreath-decomposed partner `H'`**
   (`CounterexampleH`, `WreathDecomposition.NewCounterexampleH`).
-/

/-! ## Simple-group normal-closure criterion -/

universe u

namespace KourovkaNotebook

open Subgroup

variable {G : Type u} [Group G]

/-- If the normal closure of `t` contains a set that generates the whole group,
then that normal closure is the whole group. -/
theorem normalClosure_eq_top_of_closure_le {s t : Set G} (hgen : Subgroup.closure s = ⊤)
    (hst : s ⊆ Subgroup.normalClosure t) : Subgroup.normalClosure t = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hgen]
  exact (Subgroup.closure_le (Subgroup.normalClosure t)).2 hst

/-- A conjugate of an element lies in the normal closure of that element. -/
theorem mem_normalClosure_singleton_of_isConj {x y : G} (hxy : IsConj x y) :
    y ∈ Subgroup.normalClosure ({ x } : Set G) := by
  rw [isConj_iff] at hxy
  obtain ⟨c, hc⟩ := hxy
  rw [← hc]
  exact
    Subgroup.normalClosure_normal.conj_mem x
      (Subgroup.subset_normalClosure (Set.mem_singleton x)) c

/-- Conjugate elements have the same normal closure. -/
theorem normalClosure_singleton_eq_of_isConj {x y : G} (hxy : IsConj x y) :
    Subgroup.normalClosure ({ x } : Set G) = Subgroup.normalClosure ({ y } : Set G) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact mem_normalClosure_singleton_of_isConj hxy.symm
  · refine Subgroup.normalClosure_le_normal ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact mem_normalClosure_singleton_of_isConj hxy

/-- A normal-closure criterion for simplicity.

It is enough to give a generating set `s` such that, for every nonidentity
element `g`, the normal closure of `{g}` contains `s`. Then every nontrivial
normal subgroup contains a nonidentity element, hence contains `s`, hence is
top. -/
theorem isSimpleGroup_of_normalClosure_generators [Nontrivial G] {s : Set G}
    (hgen : Subgroup.closure s = ⊤)
    (hnormal : ∀ g : G, g ≠ 1 → s ⊆ Subgroup.normalClosure ({ g } : Set G)) : IsSimpleGroup G := by
  refine ⟨fun N hN ↦ ?_⟩
  rcases Subgroup.bot_or_exists_ne_one N with hbot | ⟨g, hgN, hg_ne_one⟩
  · exact Or.inl hbot
  · right
    have : N.Normal := hN
    have hnc_le_N : Subgroup.normalClosure ({ g } : Set G) ≤ N := by
      refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hgN
    refine le_antisymm le_top ?_
    rw [← hgen]
    refine (Subgroup.closure_le N).2 ?_
    intro x hx
    exact hnc_le_N (hnormal g hg_ne_one hx)

/-- A conjugacy-class version of `isSimpleGroup_of_normalClosure_generators`.

It is enough to check one representative from every nonidentity conjugacy class:
if each such representative normally generates a fixed generating set `s`, then
the group is simple. -/
theorem isSimpleGroup_of_normalClosure_class_reps [Nontrivial G] {s reps : Set G}
    (hgen : Subgroup.closure s = ⊤) (hclass : ∀ g : G, g ≠ 1 → ∃ r ∈ reps, IsConj g r)
    (hnormal : ∀ r ∈ reps, s ⊆ Subgroup.normalClosure ({ r } : Set G)) : IsSimpleGroup G := by
  refine isSimpleGroup_of_normalClosure_generators hgen ?_
  intro g hg
  obtain ⟨r, hr, hgr⟩ := hclass g hg
  rw [normalClosure_singleton_eq_of_isConj hgr]
  exact hnormal r hr

/-- Finite-set version of `isSimpleGroup_of_normalClosure_class_reps`. -/
theorem isSimpleGroup_of_normalClosure_finset_class_reps [Nontrivial G] {s : Set G}
    (reps : Finset G) (hgen : Subgroup.closure s = ⊤)
    (hclass : ∀ g : G, g ≠ 1 → ∃ r ∈ reps, IsConj g r)
    (hnormal : ∀ r ∈ reps, s ⊆ Subgroup.normalClosure ({ r } : Set G)) : IsSimpleGroup G :=
  isSimpleGroup_of_normalClosure_class_reps hgen hclass hnormal

/-- A generator-family version of `isSimpleGroup_of_normalClosure_generators`. -/
theorem isSimpleGroup_of_normalClosure_generator_family {ι : Type*} [Nontrivial G] (gen : ι → G)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hnormal : ∀ g : G, g ≠ 1 → ∀ i : ι, gen i ∈ Subgroup.normalClosure ({ g } : Set G)) :
    IsSimpleGroup G := by
  refine isSimpleGroup_of_normalClosure_generators hgen ?_
  intro g hg y hy
  obtain ⟨i, rfl⟩ := hy
  exact hnormal g hg i

/-- A finite conjugacy-class criterion for a generator family. -/
theorem isSimpleGroup_of_normalClosure_generator_family_class_reps {ι : Type*} [Nontrivial G]
    (gen : ι → G) (reps : Finset G) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hclass : ∀ g : G, g ≠ 1 → ∃ r ∈ reps, IsConj g r)
    (hnormal : ∀ r ∈ reps, ∀ i : ι, gen i ∈ Subgroup.normalClosure ({ r } : Set G)) :
    IsSimpleGroup G := by
  refine isSimpleGroup_of_normalClosure_finset_class_reps reps hgen hclass ?_
  intro r hr y hy
  obtain ⟨i, rfl⟩ := hy
  exact hnormal r hr i

/-- A nontrivial direct product is not simple. -/
theorem not_isSimpleGroup_prod (A B : Type*) [Group A] [Group B] [Nontrivial A] [Nontrivial B] :
    ¬IsSimpleGroup (A × B) := by
  rintro ⟨h⟩
  contrapose! h
  refine ⟨Subgroup.prod ⊤ ⊥, ?_, ?_, ?_⟩
  · infer_instance
  · simp only [ne_eq, eq_bot_iff_forall, Prod.forall, Prod.mk_eq_one, not_forall, not_and]
    exact
      ⟨Classical.choose (exists_ne (1 : A)), 1, ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩, by
        simpa only [ne_eq, not_true_eq_false, imp_false] using
          Classical.choose_spec (exists_ne (1 : A))⟩
  · simp only [ne_eq, eq_top_iff', mem_prod, mem_top, mem_bot, true_and, Prod.forall,
      forall_const, not_forall]
    exact exists_ne 1

section FinsetCarrier

variable {ι : Type*}

/-- A finite carrier equals the subgroup generated by `gen` if it contains `1`,
is stable under left multiplication by each generator and its inverse, and every
carrier element is already in the generated subgroup.

This is designed for imported permutation-group data: the expensive
closure proof can be reduced to a generator-stability table plus word witnesses
for the carrier elements. -/
theorem closure_eq_finset_of_left_stable (gen : ι → G) (carrier : Finset G)
    (hone : (1 : G) ∈ carrier) (hmul : ∀ i y, y ∈ carrier → gen i * y ∈ carrier)
    (hinv : ∀ i y, y ∈ carrier → (gen i)⁻¹ * y ∈ carrier)
    (hcarrier : ∀ y, y ∈ carrier → y ∈ Subgroup.closure (Set.range gen)) :
    ∀ y : G, y ∈ Subgroup.closure (Set.range gen) ↔ y ∈ carrier := by
  intro y
  constructor
  · intro hy
    refine
      Subgroup.closure_induction_left (s := Set.range gen) (p := fun x _ ↦ x ∈ carrier) ?one
        ?mul ?inv hy
    · exact hone
    · intro x hx z _ hzcarrier
      obtain ⟨i, rfl⟩ := hx
      exact hmul i z hzcarrier
    · intro x hx z _ hzcarrier
      obtain ⟨i, rfl⟩ := hx
      exact hinv i z hzcarrier
  · exact hcarrier y

/-- A `Fintype` for a generated subgroup from a finite carrier with exactly the
same elements. -/
noncomputable def closureFintypeOfFinset (gen : ι → G) (carrier : Finset G)
    (hmem : ∀ y : G, y ∈ Subgroup.closure (Set.range gen) ↔ y ∈ carrier) :
    Fintype (Subgroup.closure (Set.range gen)) :=
  Fintype.subtype carrier (by
      intro y
      exact (hmem y).symm)

/-- The generated subgroup has the same cardinality as its certified carrier. -/
theorem card_closureFintypeOfFinset (gen : ι → G) (carrier : Finset G)
    (hmem : ∀ y : G, y ∈ Subgroup.closure (Set.range gen) ↔ y ∈ carrier) :
    @Fintype.card (Subgroup.closure (Set.range gen)) (closureFintypeOfFinset gen carrier hmem) =
      carrier.card := by
  let := closureFintypeOfFinset gen carrier hmem
  exact
    Fintype.card_of_subtype carrier (by
        intro y
        exact (hmem y).symm)

end FinsetCarrier

/-- Data-only wrapper for the normal-closure simplicity criterion. -/
structure SimpleGroupCriterion (G : Type u) [Group G] where
  /-- A set of certified generators. -/
  generators : Set G
  /-- A witness that the group is not trivial. -/
  nontrivial : Nontrivial G
  /-- The certified generators generate the whole group. -/
  generates : Subgroup.closure generators = ⊤
  /-- Every nonidentity element normally generates all certified generators. -/
  normalClosure_generators :
    ∀ g : G, g ≠ 1 → generators ⊆ Subgroup.normalClosure ({ g } : Set G)

namespace SimpleGroupCriterion

/-- A normal-closure criterion proves that the group is simple. -/
theorem isSimpleGroup (C : SimpleGroupCriterion G) : IsSimpleGroup G := by
  have : Nontrivial G := C.nontrivial
  exact isSimpleGroup_of_normalClosure_generators C.generates C.normalClosure_generators

end SimpleGroupCriterion

section FinsetSubgroup

variable [DecidableEq G]

/-- A finite carrier closed under the group operations, packaged as data for a concrete
subgroup. -/
structure FinsetSubgroup (G : Type u) [Group G] [DecidableEq G] where
  /-- The finite carrier set. -/
  carrier : Finset G
  /-- The carrier contains the identity. -/
  one_mem : (1 : G) ∈ carrier
  /-- The carrier is closed under multiplication. -/
  mul_mem : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The carrier is closed under inverse. -/
  inv_mem : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier

namespace FinsetSubgroup

variable (C : FinsetSubgroup G)

/-- The subgroup certified by a finite closed carrier. -/
def toSubgroup : Subgroup G where
  carrier := {g | g ∈ C.carrier}
  one_mem' := C.one_mem
  mul_mem' := C.mul_mem
  inv_mem' := C.inv_mem

/-- Membership in the subgroup certified by a finite closed carrier. -/
@[simp]
theorem mem_toSubgroup_iff {g : G} : g ∈ C.toSubgroup ↔ g ∈ C.carrier :=
  Iff.rfl

/-- The finite carrier gives a `Fintype` for the certified subgroup. -/
def fintype : Fintype C.toSubgroup :=
  Fintype.subtype C.carrier (fun _ ↦ Iff.rfl)

/-- The certified subgroup has the same cardinality as its carrier finset. -/
theorem card_toSubgroup : @Fintype.card C.toSubgroup C.fintype = C.carrier.card := by
  exact Fintype.card_of_subtype C.carrier (fun _ ↦ Iff.rfl)

/-- A canonical equivalence to `Fin n` once the carrier cardinality is known. -/
noncomputable def equivFinOfCardEq {n : ℕ} (hcard : C.carrier.card = n) :
    C.toSubgroup ≃ Fin n :=
  let := C.fintype
  Fintype.equivFinOfCardEq (C.card_toSubgroup.trans hcard)

end FinsetSubgroup

end FinsetSubgroup

variable (G) in
/-- Finite-generator version of `SimpleGroupCriterion`, useful for imported
GAP data whose generator list is a `Finset`. -/
structure FinsetSimpleGroupCriterion where
  /-- A finite set of certified generators. -/
  generators : Finset G
  /-- A witness that the group is not trivial. -/
  nontrivial : Nontrivial G
  /-- The certified generators generate the whole group. -/
  generates : Subgroup.closure (generators : Set G) = ⊤
  /-- Every nonidentity element normally generates all certified generators. -/
  normalClosure_generators :
    ∀ g : G, g ≠ 1 → (generators : Set G) ⊆ Subgroup.normalClosure ({ g } : Set G)

namespace FinsetSimpleGroupCriterion

/-- Forget the finite representation of the generator set. -/
def toSimpleGroupCriterion (C : FinsetSimpleGroupCriterion G) : SimpleGroupCriterion G where
  generators := C.generators
  nontrivial := C.nontrivial
  generates := C.generates
  normalClosure_generators := C.normalClosure_generators

/-- A finite normal-closure criterion proves that the group is simple. -/
theorem isSimpleGroup (C : FinsetSimpleGroupCriterion G) : IsSimpleGroup G :=
  C.toSimpleGroupCriterion.isSimpleGroup

end FinsetSimpleGroupCriterion

end KourovkaNotebook


/-! ## The simple group `PSU(3,3)` as a degree-28 permutation group

This section provides an explicit Cayley-style enumeration of the 6048 elements of the
simple group `G = ⟨a, b⟩ ≤ S₂₈`, together with the data needed to verify its order, its
element-order spectrum, and a normal-closure simplicity certificate. All combinatorial
data is supplied as `Array`s of `Nat`s and verified once via `native_decide`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

namespace KourovkaNotebook.PSU33Perm

open Finset

/-- The 28-point set on which `PSU(3,3)` acts as a permutation group. -/
abbrev Point :=
  Fin 28

/-- Permutations of the 28-point set. -/
abbrev Perm28 :=
  Equiv.Perm Point

/-- Read a function `Point → Point` from a length-28 array of targets, defaulting to `0`
on out-of-range indices. -/
def permFun (data : Array Point) : Point → Point := fun i ↦ data.getD i.val 0

/-- Build a permutation of `Point` from a pair of arrays representing a function and its
inverse, together with verified left- and right-inverse properties. -/
def permOfArrays (data invData : Array Point)
    (left : Function.LeftInverse (permFun invData) (permFun data))
    (right : Function.RightInverse (permFun invData) (permFun data)) : Perm28 where
  toFun := permFun data
  invFun := permFun invData
  left_inv := left
  right_inv := right

/-- Array of targets for the generator `a` of `G`. -/
def aData : Array Point :=
  #[3, 2, 0, 1, 20, 18, 15, 25, 14, 21, 24, 19, 12, 26, 4, 10, 23, 17, 9, 7, 8, 5, 22, 13, 6,
    11, 16, 27]

/-- Array of targets for the inverse `a⁻¹`. -/
def aInvData : Array Point :=
  #[2, 3, 1, 0, 14, 21, 24, 19, 20, 18, 15, 25, 12, 23, 8, 6, 26, 17, 5, 11, 4, 9, 22, 16, 10,
    7, 13, 27]

/-- Array of targets for the generator `b` of `G`. -/
def bData : Array Point :=
  #[6, 7, 4, 5, 10, 11, 8, 9, 0, 1, 2, 3, 17, 12, 22, 27, 16, 13, 23, 26, 19, 14, 21, 24, 18,
    15, 20, 25]

/-- Array of targets for the inverse `b⁻¹`. -/
def bInvData : Array Point :=
  #[8, 9, 10, 11, 2, 3, 0, 1, 6, 7, 4, 5, 13, 17, 21, 25, 16, 12, 24, 20, 26, 22, 14, 18, 23,
    27, 19, 15]

/-- The first generator of `G`, of cycle type `(1 4 2 3)(5 21 9 15)(6 19 10 22)(7 16 11
25)(8 26 12 20)(14 27 17 24)`. -/
def a : Perm28 :=
  permOfArrays aData aInvData (by native_decide) (by native_decide)

/-- The second generator of `G`, of cycle type `(1 7 9)(2 8 10)(3 5 11)(4 6 12)(13 18
14)(15 23 22)(16 28 26)(19 24 25)(20 27 21)`. -/
def b : Perm28 :=
  permOfArrays bData bInvData (by native_decide) (by native_decide)

/-- Letters in the four-symbol alphabet `{a, b, A, B}` used to write words representing
elements of `G`, where capitals stand for inverses. -/
inductive Step where
  | a
  | b
  | A
  | B
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Interpret a single letter as the corresponding permutation. -/
def stepPerm : Step → Perm28
  | .a => a
  | .b => b
  | .A => a⁻¹
  | .B => b⁻¹

/-- The two-element generator family of `G`, sending `0 ↦ a` and `1 ↦ b`. -/
def gen : Fin 2 → Perm28
  | 0 => a
  | 1 => b

/-- The letter representing the `i`-th generator. -/
def genStep : Fin 2 → Step
  | 0 => .a
  | 1 => .b

/-- The letter representing the inverse of the `i`-th generator. -/
def invGenStep : Fin 2 → Step
  | 0 => .A
  | 1 => .B

/-- The `i`-th generator letter evaluates to the `i`-th generator. -/
theorem stepPerm_genStep (i : Fin 2) : stepPerm (genStep i) = gen i := by fin_cases i <;> rfl

/-- The inverse of the `i`-th generator letter evaluates to the `i`-th generator's
inverse. -/
theorem stepPerm_invGenStep (i : Fin 2) : stepPerm (invGenStep i) = (gen i)⁻¹ := by
  fin_cases i <;> rfl

/-- Decode a 2-bit code `0,1,2,3` to a letter `a,b,A,B`. -/
def stepOfNat : Nat → Step
  | 0 => .a
  | 1 => .b
  | 2 => .A
  | _ => .B

/-- Auxiliary recursion: decode `n` letters from the 2-bit chunks of `code`. -/
def decodeWordAux : Nat → Nat → List Step
  | 0, _ => []
  | n + 1, code => stepOfNat (code % 4) :: decodeWordAux n (code / 4)

/-- Decode a packed natural number to a word: the low 4 bits give the length, the
remaining bits give the 2-bit chunks for the letters. -/
def decodeWord (packed : Nat) : List Step :=
  decodeWordAux (packed % 16) (packed / 16)

/-- Evaluate a word in `Step`s as the corresponding product of permutations. -/
def evalWord : List Step → Perm28
  | [] => 1
  | s :: w => stepPerm s * evalWord w

/-- Packed representatives `wordCodeArray[i]` for the 6048 elements of `G`, encoded
as (length, letters) pairs. The `i`-th element is `evalWord (decodeWord wordCodeArray[i])`. -/
def wordCodeArray : Array Nat :=
  #[0, 1, 17, 33, 49, 2, 18, 50, 66, 98, 146, 178, 194, 226, 19, 51, 67, 99, 195, 227, 259, 275,
    307, 403, 435, 579, 611, 707, 739, 771, 787, 819, 915, 947, 68, 100, 196, 228, 260, 276,
    308, 404, 436, 772, 788, 820, 916, 948, 1044, 1076, 1092, 1124, 1220, 1252, 1604, 1636,
    1732, 1764, 2308, 2324, 2356, 2452, 2484, 2820, 2836, 2868, 2964, 2996, 3092, 3124, 3140,
    3172, 3268, 3300, 3652, 3684, 3780, 3812, 261, 277, 309, 405, 437, 773, 789, 821, 917, 949,
    1045, 1077, 1093, 1125, 1221, 1253, 1605, 1637, 1733, 1765, 3093, 3125, 3141, 3173, 3269,
    3301, 3653, 3685, 3781, 3813, 4165, 4197, 4293, 4325, 4357, 4373, 4405, 4501, 4533, 4869,
    4885, 4917, 5013, 5045, 6405, 6421, 6453, 6549, 6581, 6917, 6933, 6965, 7061, 7093, 9237,
    9269, 9285, 9317, 9413, 9445, 9797, 9829, 9925, 9957, 11285, 11317, 11333, 11365, 11461,
    11493, 11845, 11877, 11973, 12005, 12357, 12389, 12485, 12517, 12549, 12565, 12597, 12693,
    12725, 13061, 13077, 13109, 13205, 13237, 14597, 14613, 14645, 14741, 14773, 15109, 15125,
    15157, 15253, 15285, 1046, 1078, 1094, 1126, 1222, 1254, 1606, 1638, 1734, 1766, 3094, 3126,
    3142, 3174, 3270, 3302, 3654, 3686, 3782, 3814, 4166, 4198, 4294, 4326, 4358, 4374, 4406,
    4502, 4534, 4870, 4886, 4918, 5014, 5046, 6406, 6422, 6454, 6550, 6582, 6918, 6934, 6966,
    7062, 7094, 12358, 12390, 12486, 12518, 12550, 12566, 12598, 12694, 12726, 13062, 13078,
    13110, 13206, 13238, 14598, 14614, 14646, 14742, 14774, 15110, 15126, 15158, 15254, 15286,
    16662, 16694, 16790, 16822, 17158, 17174, 17206, 17302, 17334, 17430, 17462, 17478, 17510,
    17606, 17638, 17990, 18022, 18118, 18150, 19478, 19510, 19526, 19558, 19654, 19686, 20070,
    20166, 20198, 25622, 25654, 25670, 25702, 25798, 25830, 26182, 26214, 26310, 26342, 27670,
    27702, 27718, 27750, 27846, 27878, 28230, 28262, 28358, 28390, 37062, 37094, 37126, 37142,
    37174, 37270, 37302, 37638, 37654, 37686, 37814, 39174, 39190, 39222, 39318, 39350, 39686,
    39702, 39734, 39830, 39862, 45126, 45158, 45318, 45334, 45366, 45462, 45494, 45830, 45846,
    45878, 45974, 46006, 47366, 47382, 47414, 47510, 47542, 47878, 47894, 47926, 48022, 48054,
    49414, 49430, 49462, 49558, 49590, 49942, 49974, 50070, 50102, 50198, 50230, 50246, 50278,
    50374, 50406, 50758, 50790, 50918, 52246, 52278, 52294, 52326, 52422, 52454, 52806, 52838,
    52934, 52966, 58390, 58422, 58438, 58470, 58566, 58950, 58982, 59078, 59110, 60438, 60470,
    60486, 60518, 60614, 60646, 60998, 61030, 61126, 61158, 4295, 4327, 4359, 4375, 4407, 4503,
    4535, 4871, 4887, 4919, 5015, 5047, 6407, 6423, 6455, 6551, 6583, 6919, 6935, 6967, 7063,
    7095, 12359, 12391, 12551, 12567, 12599, 12695, 12727, 13063, 13079, 13111, 13207, 13239,
    14599, 14615, 14647, 14743, 14775, 15111, 15127, 15159, 15255, 15287, 16663, 16695, 16791,
    16823, 17159, 17175, 17207, 17303, 17335, 17431, 17463, 17479, 17511, 17607, 17639, 17991,
    18023, 18119, 18151, 19479, 19511, 19527, 19559, 19655, 19687, 20071, 20167, 20199, 25623,
    25655, 25671, 25703, 25799, 25831, 26183, 26215, 26311, 26343, 27671, 27703, 27719, 27847,
    27879, 28231, 28263, 28359, 28391, 49415, 49431, 49463, 49559, 49591, 49943, 49975, 50071,
    50103, 50199, 50231, 50247, 50279, 50375, 50407, 50759, 50791, 50919, 52247, 52279, 52295,
    52327, 52423, 52455, 52807, 52839, 52935, 52967, 58391, 58423, 58439, 58471, 58567, 58951,
    58983, 59079, 59111, 60439, 60471, 60487, 60519, 60615, 60647, 60999, 61031, 61127, 61159,
    66631, 66663, 66759, 66791, 67143, 67175, 67271, 67303, 68631, 68679, 68711, 68807, 68839,
    69191, 69223, 69319, 69351, 69703, 69735, 69831, 69863, 69895, 69911, 69943, 70039, 70071,
    70407, 70423, 70455, 70551, 70583, 71943, 71959, 71991, 72087, 72119, 72455, 72503, 72599,
    72631, 77895, 77927, 78023, 78055, 78087, 78103, 78135, 78231, 78263, 78599, 78615, 78647,
    78743, 78775, 80279, 80311, 80647, 80663, 80695, 80791, 80823, 102599, 102631, 102663,
    102679, 102711, 102807, 102839, 103175, 103191, 103223, 103351, 104711, 104727, 104759,
    104887, 105223, 105239, 105271, 105367, 105399, 110663, 110695, 110855, 110871, 110903,
    111367, 111383, 111415, 111511, 111543, 112903, 112919, 112951, 113047, 113079, 113415,
    113431, 113463, 113559, 113591, 148231, 148247, 148279, 148375, 148407, 148503, 148535,
    148551, 148583, 148679, 148711, 149063, 149095, 149191, 149223, 150551, 150583, 150599,
    150631, 150727, 150759, 151239, 151271, 156695, 156727, 156743, 156775, 156871, 156903,
    157255, 157287, 157383, 157415, 158743, 158775, 158791, 158919, 158951, 159303, 159335,
    159431, 159463, 180487, 180503, 180535, 180631, 180663, 181271, 181303, 181319, 181351,
    181447, 181479, 181831, 181863, 181991, 183319, 183351, 183367, 183399, 183495, 183527,
    183879, 183911, 184007, 184039, 189463, 189495, 189511, 189543, 189639, 190023, 190055,
    190151, 190183, 191511, 191543, 191559, 191591, 191687, 191719, 192071, 192103, 192199,
    197703, 197735, 197831, 197863, 198215, 198247, 198343, 198375, 199751, 199783, 199879,
    199911, 200263, 200295, 200391, 200423, 200775, 200807, 200903, 200935, 200967, 200983,
    201015, 201111, 201143, 201479, 201495, 201527, 201623, 201655, 203015, 203031, 203063,
    203159, 203191, 203671, 203703, 208967, 208999, 209095, 209127, 209159, 209175, 209207,
    209303, 209335, 209671, 209687, 209815, 209847, 211207, 211351, 211383, 211719, 211735,
    211767, 211863, 211895, 233671, 233703, 233735, 233751, 233783, 233879, 233911, 234263,
    234295, 235783, 235799, 235831, 235927, 235959, 236295, 236311, 236343, 236439, 236471,
    241735, 241767, 241927, 241943, 241975, 242439, 242455, 242487, 242583, 242615, 243975,
    243991, 244023, 244119, 244151, 244487, 244503, 244535, 244631, 17160, 17176, 17208, 17304,
    17336, 17432, 17464, 17480, 17512, 17608, 17640, 17992, 18024, 18120, 18152, 19480, 19512,
    19528, 19560, 19656, 19688, 20072, 20168, 20200, 25624, 25656, 25672, 25704, 25800, 25832,
    26184, 26216, 26312, 26344, 27672, 27704, 27720, 27848, 27880, 28232, 28264, 28360, 28392,
    49416, 49432, 49464, 49560, 49592, 50200, 50232, 50248, 50280, 50376, 50408, 50760, 50792,
    50920, 52248, 52280, 52296, 52328, 52424, 52456, 52808, 52840, 52936, 52968, 58392, 58424,
    58440, 58472, 58568, 58952, 58984, 59080, 59112, 60440, 60472, 60488, 60520, 60616, 60648,
    61000, 61032, 61128, 61160, 66632, 66664, 66760, 66792, 67144, 67176, 67272, 67304, 68632,
    68680, 68712, 68808, 68840, 69192, 69224, 69320, 69352, 69704, 69736, 69832, 69864, 69896,
    70040, 70072, 70408, 70424, 70456, 70552, 70584, 71944, 71960, 71992, 72088, 72120, 72456,
    72504, 72600, 72632, 77896, 77928, 78024, 78056, 78088, 78104, 78136, 78232, 78264, 78600,
    78616, 78648, 78744, 78776, 80280, 80312, 80648, 80664, 80696, 80792, 80824, 102600, 102632,
    102664, 102680, 102712, 102808, 102840, 103176, 103192, 103224, 103352, 104712, 104728,
    104760, 104888, 105224, 105240, 105272, 105368, 105400, 110664, 110696, 110872, 110904,
    111368, 111384, 111416, 111512, 111544, 112904, 112920, 112952, 113048, 113080, 113416,
    113432, 113464, 113560, 113592, 197704, 197736, 197832, 197864, 198216, 198248, 198344,
    198376, 199752, 199784, 199880, 199912, 200264, 200296, 200392, 200424, 200776, 200808,
    200904, 200936, 200968, 200984, 201016, 201112, 201144, 201480, 201496, 201528, 201624,
    201656, 203016, 203032, 203064, 203160, 203192, 203672, 203704, 208968, 209000, 209096,
    209128, 209160, 209176, 209208, 209304, 209336, 209672, 209816, 209848, 211208, 211352,
    211384, 211720, 211736, 211768, 211864, 211896, 233672, 233704, 233736, 233752, 233784,
    233880, 233912, 234264, 234296, 235784, 235800, 235832, 235928, 235960, 236296, 236312,
    236344, 236440, 236472, 241736, 241768, 241928, 241944, 241976, 242440, 242456, 242488,
    242584, 242616, 243976, 243992, 244024, 244120, 244152, 244488, 244504, 244536, 244632,
    266504, 266520, 266552, 266648, 266680, 267016, 267032, 267064, 267160, 267192, 268552,
    268568, 268600, 268696, 268728, 269064, 269080, 269112, 269208, 269240, 274536, 274712,
    274744, 274840, 274872, 275224, 275256, 275352, 275384, 276760, 276792, 276888, 276920,
    277272, 277304, 277400, 277432, 278808, 278840, 278936, 278968, 279320, 279352, 279448,
    279480, 279576, 279608, 279656, 279752, 279784, 280136, 280168, 280264, 280296, 281624,
    281656, 281672, 281704, 281800, 281832, 282216, 282312, 282344, 287768, 287800, 287816,
    287944, 287976, 288328, 288360, 288456, 288488, 289816, 289848, 289992, 290024, 290376,
    290408, 290504, 290536, 311576, 311608, 311704, 311736, 312088, 312120, 312216, 312248,
    312344, 312376, 312392, 312424, 312552, 312904, 312936, 313064, 314392, 314424, 314440,
    314472, 314600, 314952, 314984, 315080, 315112, 321096, 321128, 321224, 321256, 322584,
    322616, 322632, 322664, 322760, 322792, 323144, 323176, 323272, 323304, 410392, 410424,
    410520, 410552, 410648, 410680, 410696, 410728, 410824, 410856, 411208, 411240, 411336,
    411368, 412696, 412728, 412744, 412776, 412872, 412904, 413384, 413416, 418840, 418872,
    418888, 418920, 419016, 419048, 419528, 419560, 420888, 420920, 420936, 421064, 421096,
    421448, 421480, 421576, 421608, 442648, 442680, 442776, 442808, 443416, 443448, 443464,
    443496, 443624, 445464, 445496, 445512, 445544, 445640, 445672, 446024, 446056, 446152,
    446184, 451608, 451640, 451656, 451688, 452168, 452200, 452328, 453656, 453688, 453704,
    453736, 453832, 453864, 454216, 454248, 454344, 593992, 594024, 594184, 594232, 594328,
    594360, 594696, 594712, 594744, 594840, 594872, 596232, 596248, 596280, 596376, 596408,
    596744, 596792, 596888, 596920, 602312, 602344, 602376, 602392, 602520, 602552, 602888,
    602904, 602936, 603032, 603064, 604936, 604952, 604984, 605080, 605112, 626952, 626968,
    627000, 627096, 627128, 627464, 627480, 627512, 627640, 629000, 629016, 629048, 629512,
    629528, 629560, 629656, 629688, 635160, 635656, 635672, 635704, 635800, 635832, 637192,
    637208, 637336, 637704, 637720, 637752, 637848, 637880, 725064, 725096, 725256, 725272,
    725304, 725400, 725432, 725768, 725784, 725816, 725912, 725944, 727304, 727320, 727352,
    727448, 727480, 727960, 727992, 733384, 733416, 733448, 733464, 733496, 733592, 733624,
    733960, 733976, 734104, 734136, 735496, 735640, 735672, 736008, 736024, 736152, 736184,
    758024, 758040, 758072, 758168, 758200, 758552, 758584, 760072, 760088, 760120, 760216,
    760248, 760584, 760600, 760632, 760728, 760760, 766216, 766232, 766264, 766728, 766744,
    766776, 766872, 766904, 768264, 768280, 768312, 768408, 768440, 768792, 768824, 790808,
    790840, 790936, 790968, 791320, 791352, 791448, 791480, 792856, 792888, 792984, 793016,
    793368, 793400, 793496, 793528, 798984, 799000, 799032, 799128, 799160, 799496, 799512,
    799544, 799640, 799672, 801032, 801048, 801080, 801176, 801208, 801544, 801560, 801592,
    801688, 801720, 803096, 803128, 803224, 803256, 803608, 803640, 803736, 803768, 803864,
    803896, 803944, 804040, 804072, 804424, 804456, 804552, 804584, 805912, 805944, 806088,
    806120, 806600, 806632, 812056, 812088, 812104, 812136, 812232, 812264, 812616, 812648,
    812744, 812776, 814664, 814792, 814824, 835864, 835896, 835992, 836024, 836376, 836408,
    836504, 836536, 836632, 836664, 836680, 836712, 836808, 836840, 837192, 837224, 837352,
    838680, 838712, 838728, 838760, 839240, 839272, 839368, 839400, 844824, 844856, 845384,
    845416, 845512, 845544, 846872, 846904, 846920, 846952, 847048, 847432, 847464, 847560,
    847592, 934680, 934712, 934808, 934840, 934936, 934968, 934984, 935016, 935112, 935144,
    935496, 935528, 935624, 935656, 937064, 937160, 937192, 943128, 943160, 943176, 943208,
    943304, 943336, 943688, 943816, 943848, 945176, 945208, 945352, 945384, 945864, 945896,
    966936, 966968, 967064, 967096, 967704, 967736, 967752, 967784, 967880, 967912, 969752,
    969784, 969800, 969832, 969928, 969960, 970312, 970344, 970472, 975896, 975928, 975944,
    975976, 976072, 976456, 976488, 976584, 976616, 977944, 977976, 977992, 978024, 978120,
    978152, 978504, 978536, 68633, 69705, 69737, 69897, 70041, 70073, 70409, 70425, 70457,
    70553, 70585, 71945, 71961, 71993, 72089, 72121, 72457, 72505, 72601, 72633, 78025, 78057,
    78089, 78105, 78137, 78233, 78265, 78601, 78617, 78649, 78745, 78777, 80281, 80313, 80649,
    80665, 80697, 80793, 80825, 102665, 102681, 102713, 102809, 102841, 103177, 103193, 103225,
    103353, 104713, 104729, 104761, 105225, 105241, 105273, 105369, 105401, 110873, 110905,
    111369, 111385, 111417, 111513, 111545, 112905, 112921, 112953, 113049, 113081, 113417,
    113433, 113465, 113561, 113593, 200777, 200809, 200969, 200985, 201017, 201113, 201145,
    201481, 201497, 201529, 201625, 201657, 203017, 203033, 203065, 203161, 203193, 203673,
    203705, 209097, 209129, 209161, 209177, 209209, 209305, 209337, 209673, 209817, 209849,
    211209, 211353, 211385, 211721, 211737, 211769, 211865, 211897, 233737, 233753, 233785,
    233881, 233913, 234265, 234297, 235785, 235801, 235833, 235929, 235961, 236297, 236313,
    236345, 236441, 236473, 241929, 241945, 241977, 242441, 242457, 242489, 242585, 242617,
    243977, 243993, 244025, 244121, 244153, 244489, 244505, 244537, 266505, 266521, 266553,
    266649, 266681, 267017, 267033, 267065, 267161, 267193, 268553, 268569, 268601, 268697,
    268729, 269065, 269081, 269113, 269209, 269241, 274713, 274745, 274841, 274873, 275225,
    275257, 275353, 275385, 276761, 276793, 276889, 276921, 277273, 277305, 277401, 277433,
    278809, 278841, 278937, 278969, 279321, 279353, 279449, 279481, 279577, 279609, 280137,
    280169, 280265, 280297, 281625, 281657, 281673, 281705, 281801, 281833, 282217, 282313,
    282345, 287769, 287801, 287817, 287945, 287977, 288329, 288361, 288457, 288489, 289817,
    289849, 289993, 290025, 290377, 290409, 290505, 290537, 311577, 311609, 311705, 311737,
    312089, 312121, 312217, 312249, 312345, 312377, 312393, 312425, 312905, 312937, 314393,
    314425, 314441, 314473, 314601, 314953, 314985, 315081, 315113, 321097, 321129, 321225,
    322585, 322617, 322633, 322665, 322761, 322793, 323145, 323177, 323273, 323305, 410393,
    410425, 410521, 410553, 410649, 410681, 410697, 410729, 410825, 410857, 411241, 411337,
    411369, 412697, 412729, 412745, 412777, 412873, 412905, 413385, 413417, 418841, 418873,
    418889, 418921, 419017, 419049, 419529, 419561, 420889, 420921, 420937, 421065, 421097,
    421449, 421481, 421577, 421609, 442649, 442681, 442777, 442809, 443465, 443497, 443625,
    445465, 445497, 445513, 445545, 445641, 445673, 446025, 446057, 446153, 446185, 451609,
    451641, 451657, 451689, 452169, 452201, 453657, 453689, 453705, 453737, 453833, 453865,
    454217, 454249, 454345, 790809, 790841, 790937, 790969, 791321, 791353, 791449, 791481,
    792857, 792889, 792985, 793017, 793369, 793401, 793497, 793529, 798985, 799001, 799033,
    799129, 799161, 799497, 799513, 799545, 799641, 799673, 801033, 801049, 801081, 801177,
    801209, 801545, 801561, 801593, 801689, 801721, 803097, 803129, 803225, 803257, 803609,
    803641, 803737, 803769, 803865, 803897, 803945, 804041, 804073, 804425, 804457, 804553,
    804585, 805913, 805945, 806089, 806121, 806601, 806633, 812057, 812089, 812105, 812137,
    812233, 812265, 812617, 812649, 812745, 812777, 814665, 814793, 814825, 835865, 835897,
    835993, 836025, 836377, 836409, 836505, 836537, 836633, 836665, 836681, 836713, 836809,
    836841, 837193, 837225, 837353, 838681, 838713, 839241, 839273, 839369, 839401, 844825,
    844857, 845385, 845417, 845513, 845545, 846873, 846905, 846921, 846953, 847049, 847433,
    847465, 847561, 847593, 934681, 934713, 934809, 934841, 934937, 934969, 934985, 935017,
    935113, 935145, 935497, 935529, 935625, 935657, 937065, 937161, 937193, 943129, 943161,
    943177, 943209, 943305, 943337, 943689, 943817, 943849, 945177, 945209, 945353, 945385,
    945865, 945897, 966937, 966969, 967065, 967097, 967705, 967737, 967753, 967785, 967881,
    967913, 969753, 969785, 969801, 969833, 969929, 969961, 970313, 970345, 970473, 975897,
    975929, 975945, 975977, 976073, 976457, 976489, 976585, 976617, 977945, 977977, 977993,
    978025, 978121, 978153, 978505, 978537, 1066009, 1066057, 1066089, 1066185, 1066569,
    1066601, 1066697, 1066729, 1068089, 1068105, 1068137, 1068233, 1068265, 1068649, 1068745,
    1068777, 1074201, 1074249, 1074281, 1074377, 1074409, 1074761, 1074793, 1074921, 1076281,
    1076297, 1076425, 1076457, 1076809, 1076841, 1076937, 1076969, 1098825, 1098857, 1099337,
    1099369, 1100873, 1100905, 1101001, 1101033, 1101385, 1101417, 1101513, 1101545, 1107017,
    1107049, 1107145, 1107529, 1107561, 1107689, 1109065, 1109097, 1109193, 1109225, 1109577,
    1109609, 1109705, 1109737, 1115209, 1115241, 1115337, 1115369, 1115721, 1115753, 1115849,
    1115881, 1117257, 1117289, 1117385, 1117417, 1117769, 1117801, 1117897, 1117929, 1118281,
    1118313, 1118409, 1118441, 1118617, 1118649, 1118985, 1119001, 1119033, 1119129, 1119161,
    1120521, 1120569, 1120665, 1120697, 1121033, 1121081, 1121177, 1121209, 1126473, 1126505,
    1126601, 1126633, 1126665, 1126681, 1126809, 1127177, 1127193, 1127225, 1127321, 1127353,
    1128857, 1129225, 1129241, 1129273, 1129369, 1129401, 1151177, 1151209, 1151257, 1151289,
    1151753, 1151769, 1151801, 1151929, 1153289, 1153337, 1153465, 1153801, 1153817, 1153849,
    1153945, 1153977, 1159241, 1159273, 1159945, 1159961, 1159993, 1160089, 1160121, 1161481,
    1161497, 1161529, 1161625, 1161993, 1162009, 1162041, 1162137, 1162169, 1246281, 1246313,
    1246441, 1246793, 1246825, 1246921, 1248329, 1248361, 1248457, 1248489, 1248841, 1248873,
    1248969, 1249001, 1249353, 1249385, 1249545, 1249561, 1249593, 1249689, 1249721, 1251593,
    1251609, 1251641, 1251737, 1251769, 1257545, 1257577, 1257737, 1257753, 1257785, 1257881,
    1257913, 1258393, 1258425, 1259785, 1259929, 1259961, 1260297, 1260313, 1260345, 1260441,
    1260473, 1284377, 1284409, 1284505, 1284537, 1284889, 1284921, 1290313, 1290345, 1290505,
    1290521, 1290553, 1291017, 1291033, 1291065, 1291161, 1292553, 1292569, 1292601, 1292697,
    1292729, 1293065, 1293081, 1293113, 1293209, 1642569, 1642601, 1642761, 1642809, 1642905,
    1642937, 1643273, 1643289, 1643321, 1643417, 1643449, 1644809, 1644985, 1645321, 1645369,
    1645465, 1645497, 1650889, 1650921, 1650953, 1650969, 1651097, 1651129, 1651465, 1651481,
    1651513, 1651609, 1651641, 1653513, 1653529, 1653561, 1653657, 1653689, 1675529, 1675545,
    1675577, 1675673, 1675705, 1676041, 1676057, 1676089, 1676217, 1678089, 1678105, 1678137,
    1678233, 1678265, 1683737, 1684233, 1684249, 1684281, 1684377, 1684409, 1685769, 1685785,
    1685913, 1686281, 1686297, 1686329, 1686425, 1686457, 1773641, 1773673, 1773833, 1773849,
    1773881, 1773977, 1774009, 1774489, 1774521, 1781961, 1781993, 1782025, 1782041, 1782073,
    1782169, 1782201, 1782537, 1782553, 1782681, 1782713, 1784073, 1784217, 1784249, 1784585,
    1784601, 1784729, 1784761, 1806601, 1806617, 1806649, 1806745, 1806777, 1808649, 1808665,
    1808697, 1808793, 1808825, 1814793, 1814809, 1814841, 1815305, 1815321, 1815353, 1815449,
    1815481, 1816841, 1816857, 1816889, 1816985, 1817017, 1817369, 1817401, 2375961, 2375993,
    2376089, 2376121, 2376729, 2376761, 2376905, 2376937, 2377289, 2377321, 2377417, 2377449,
    2378777, 2378809, 2378825, 2378857, 2378953, 2378985, 2379369, 2379465, 2379497, 2384921,
    2384953, 2384969, 2385097, 2385129, 2385481, 2385513, 2385609, 2385641, 2386969, 2387001,
    2387145, 2387177, 2387529, 2387561, 2387657, 2387689, 2409241, 2409273, 2409369, 2409401,
    2409497, 2409545, 2409577, 2410057, 2410089, 2411545, 2411593, 2411625, 2411753, 2412105,
    2412137, 2412233, 2412265, 2419737, 2419769, 2419785, 2419817, 2419913, 2419945, 2420297,
    2420329, 2420425, 2420457, 2507801, 2507833, 2507849, 2507881, 2507977, 2508009, 2508393,
    2508489, 2508521, 2509849, 2509881, 2509897, 2509929, 2510025, 2510057, 2510537, 2510569,
    2515993, 2516025, 2516041, 2516073, 2516169, 2516201, 2518041, 2518073, 2518089, 2518217,
    2518249, 2518601, 2518633, 2518729, 2518761, 2540617, 2540649, 2542617, 2542649, 2542665,
    2542697, 2542793, 2542825, 2543177, 2543209, 2543305, 2543337, 2548761, 2548809, 2548841,
    2549321, 2549353, 2550809, 2550841, 2550857, 2550889, 2550985, 2551017, 2551369, 2551401,
    2551497, 2900249, 2900281, 2900377, 2900409, 2901017, 2901049, 2901097, 2901193, 2901225,
    2901577, 2901609, 2901705, 2901737, 2903065, 2903097, 2903241, 2903273, 2903753, 2903785,
    2909209, 2909241, 2909257, 2909289, 2909385, 2909417, 2909769, 2909801, 2909897, 2909929,
    2911817, 2911945, 2911977, 2933529, 2933561, 2933657, 2933689, 2933785, 2933817, 2933833,
    2933865, 2933961, 2933993, 2934345, 2934377, 2934505, 2935833, 2935865, 2935881, 2935913,
    2936393, 2936425, 2936553, 2941977, 2942009, 2942537, 2942569, 2942665, 2942697, 2944025,
    2944057, 2944073, 2944105, 2944585, 2944617, 2944745, 3032089, 3032121, 3032137, 3032169,
    3032265, 3032297, 3032649, 3032681, 3032777, 3032809, 3034217, 3034313, 3034345, 3040281,
    3040313, 3040329, 3040361, 3040457, 3040489, 3040841, 3040969, 3041001, 3042329, 3042361,
    3042505, 3042537, 3043017, 3043049, 3064857, 3064889, 3064905, 3064937, 3065033, 3065065,
    3066905, 3066937, 3066953, 3066985, 3067081, 3067113, 3067465, 3067497, 3073049, 3073081,
    3073097, 3073129, 3073225, 3073609, 3073641, 3073737, 3073769, 3075145, 3075177, 3075273,
    3075305, 3163209, 3163241, 3163337, 3163369, 3163721, 3163753, 3163849, 3163881, 3165385,
    3165417, 3165897, 3165929, 3171401, 3171433, 3171529, 3171561, 3171913, 3171945, 3172041,
    3172073, 3173577, 3173609, 3174089, 3174121, 3195977, 3196009, 3196105, 3196137, 3196489,
    3196521, 3196649, 3198025, 3198153, 3198185, 3198537, 3198569, 3198665, 3198697, 3204169,
    3204201, 3204297, 3204681, 3204713, 3204809, 3204841, 3206217, 3206249, 3206345, 3206377,
    3206761, 3206857, 3206889, 3212361, 3212393, 3212489, 3212521, 3212873, 3212905, 3213001,
    3213033, 3214537, 3214569, 3215049, 3215081, 3215561, 3215593, 3215769, 3215801, 3216137,
    3216153, 3216185, 3216281, 3216313, 3217673, 3217689, 3217721, 3217817, 3217849, 3218185,
    3218233, 3218329, 3218361, 3223753, 3223785, 3224329, 3224345, 3224377, 3224473, 3224505,
    3226377, 3226393, 3226425, 3226521, 3226553, 3248329, 3248361, 3248393, 3248409, 3248441,
    3248905, 3248921, 3248953, 3249081, 3250441, 3250457, 3250489, 3250617, 3250953, 3250969,
    3251001, 3251097, 3251129, 3258649, 3258681, 3259161, 3259193, 3259289, 3259321, 3343433,
    3343465, 3343561, 3343593, 3343945, 3343977, 3344073, 3344105, 3345481, 3345513, 3345609,
    3345641, 3345993, 3346025, 3346121, 3346153, 3346505, 3346537, 3346633, 3346665, 3346697,
    3346713, 3346745, 3346841, 3346873, 3347209, 3348745, 3348761, 3348793, 3348889, 3348921,
    3354697, 3354729, 3354825, 3354857, 3354889, 3354905, 3354937, 3355033, 3355065, 3356937,
    3357081, 3357113, 3357449, 3357465, 3357593, 3357625, 3379401, 3379433, 3381513, 3381529,
    3381561, 3381657, 3381689, 3382025, 3382041, 3382073, 3387465, 3387497, 3387657, 3387673,
    3387705, 3388185, 3389705, 3389721, 3389753, 3389849, 3389881, 3390217, 3390233, 3390361,
    3739721, 3739753, 3739913, 3739961, 3740057, 3740089, 3740425, 3740441, 3740473, 3740569,
    3740601, 3741961, 3742105, 3742137, 3742473, 3742521, 3742617, 3742649, 3748249, 3748281,
    3748633, 3748665, 3748761, 3748793, 3772681, 3772697, 3772729, 3772825, 3772857, 3773193,
    3773209, 3773241, 3773369, 3774745, 3774777, 3775241, 3775257, 3775289, 3775385, 3775417,
    3781385, 3781401, 3781433, 3781529, 3781561, 3783433, 3783449, 3783481, 3783577, 3783609,
    3870793, 3870825, 3870985, 3871001, 3871033, 3871129, 3871161, 3871497, 3871641, 3871673,
    3879113, 3879145, 3879177, 3879193, 3879225, 3879321, 3879353, 3879689, 3879705, 3879833,
    3881225, 3881369, 3881401, 3881881, 3903753, 3903769, 3903801, 3903897, 3903929, 3905801,
    3905817, 3905849, 3905945, 3905977, 3906313, 3911945, 3911961, 3911993, 3912457, 3912473,
    3912505, 3912601, 3913993, 3914009, 3914041, 3914137, 3914169, 278810, 278842, 278938,
    278970, 279578, 279610, 280138, 280266, 280298, 281626, 281658, 281674, 281706, 281834,
    282218, 282314, 282346, 287770, 287802, 287818, 287946, 287978, 288330, 288362, 288458,
    288490, 289818, 289850, 289994, 290026, 290378, 290410, 290506, 290538, 312090, 312122,
    312218, 312250, 312346, 312378, 312394, 312426, 312906, 312938, 314394, 314426, 314442,
    314474, 314602, 314954, 314986, 315082, 315114, 321098, 321226, 322586, 322618, 322634,
    322666, 322794, 323146, 323178, 323274, 323306, 410650, 410682, 410698, 410730, 410826,
    410858, 411242, 411338, 411370, 412698, 412730, 412746, 412778, 412874, 412906, 413386,
    413418, 418842, 418874, 418922, 419018, 419050, 420890, 420922, 420938, 421066, 421098,
    421450, 421482, 421578, 443498, 443626, 445466, 445498, 445514, 445546, 445642, 445674,
    446026, 446058, 446154, 451610, 451642, 451658, 451690, 452170, 452202, 453658, 453690,
    453706, 453738, 453834, 453866, 454218, 454250, 454346, 803098, 803130, 803226, 803258,
    803866, 803898, 803946, 804042, 804074, 804426, 804458, 804554, 804586, 805914, 805946,
    806090, 806122, 806602, 806634, 812058, 812090, 812138, 812234, 812266, 812618, 812650,
    812746, 812778, 814666, 814794, 836378, 836410, 836506, 836538, 836634, 836666, 836714,
    836810, 836842, 837194, 837226, 837354, 838682, 838714, 839242, 839274, 839370, 844826,
    844858, 845386, 845418, 845514, 845546, 846874, 846906, 846922, 846954, 847050, 847434,
    847466, 847562, 847594, 934938, 934970, 934986, 935018, 935114, 935146, 935498, 935626,
    935658, 937066, 937194, 943130, 943162, 943178, 943210, 943306, 943338, 943690, 943818,
    943850, 945178, 945210, 945354, 945386, 945866, 945898, 967706, 967738, 967754, 967786,
    967882, 967914, 969754, 969786, 969802, 969834, 969930, 969962, 970314, 970346, 970474,
    975898, 975930, 975946, 975978, 976074, 976458, 976586, 976618, 977946, 977978, 977994,
    978026, 978154, 1066010, 1066058, 1066090, 1066186, 1066570, 1066602, 1066698, 1066730,
    1068090, 1068106, 1068138, 1068234, 1068266, 1068650, 1068746, 1068778, 1074202, 1074250,
    1074282, 1074378, 1074410, 1074794, 1076282, 1076426, 1076810, 1076842, 1076938, 1076970,
    1098826, 1098858, 1099338, 1099370, 1100874, 1100906, 1101002, 1101034, 1101386, 1101418,
    1101514, 1101546, 1107018, 1107050, 1107530, 1107562, 1109066, 1109098, 1109194, 1109226,
    1109578, 1109610, 1109706, 1109738, 1115210, 1115242, 1115338, 1115370, 1115722, 1115850,
    1115882, 1117258, 1117290, 1117386, 1117418, 1117770, 1117802, 1117898, 1117930, 1118282,
    1118314, 1118410, 1118442, 1120522, 1120570, 1120666, 1121034, 1121082, 1121178, 1121210,
    1126474, 1126506, 1126602, 1126634, 1126666, 1126682, 1126810, 1127226, 1127322, 1127354,
    1129226, 1129242, 1129274, 1129370, 1129402, 1151178, 1151210, 1151770, 1151802, 1151930,
    1153338, 1153466, 1153802, 1153850, 1153946, 1153978, 1159242, 1159274, 1159946, 1159962,
    1159994, 1160090, 1160122, 1161482, 1161498, 1161530, 1161626, 1161994, 1162010, 1162042,
    1162138, 1162170, 1246282, 1246314, 1246794, 1246826, 1248330, 1248362, 1248458, 1248490,
    1248842, 1248874, 1248970, 1249002, 1249354, 1249386, 1249546, 1249562, 1249594, 1249690,
    1249722, 1251594, 1251610, 1251642, 1251738, 1251770, 1257546, 1257578, 1257738, 1257754,
    1257786, 1257882, 1258394, 1258426, 1259786, 1259930, 1259962, 1260298, 1260314, 1260346,
    1260442, 1260474, 1284410, 1284506, 1284890, 1284922, 1290314, 1290346, 1290506, 1290522,
    1290554, 1291018, 1291066, 1291162, 1292554, 1292570, 1292602, 1292698, 1292730, 1293066,
    1293082, 1293114, 1293210, 1642570, 1642602, 1642762, 1642810, 1643274, 1643290, 1643322,
    1643450, 1644986, 1645322, 1645370, 1645466, 1645498, 1650890, 1650954, 1650970, 1651098,
    1651130, 1651466, 1651482, 1651514, 1651610, 1651642, 1653514, 1653530, 1653562, 1653658,
    1653690, 1675530, 1675546, 1676042, 1676058, 1676090, 1676218, 1678090, 1678106, 1678138,
    1678234, 1678266, 1684234, 1684250, 1684282, 1684378, 1684410, 1685770, 1685786, 1685914,
    1686282, 1686298, 1686330, 1686458, 1773850, 1773978, 1774010, 1774490, 1774522, 1781962,
    1781994, 1782026, 1782042, 1782074, 1782170, 1782202, 1782538, 1782554, 1782682, 1782714,
    1784074, 1784218, 1784250, 1784586, 1784602, 1784762, 1806602, 1806618, 1806650, 1806746,
    1806778, 1808650, 1808666, 1808698, 1808794, 1808826, 1814794, 1814810, 1814842, 1815306,
    1815322, 1815482, 1816842, 1816858, 1817018, 1817370, 1817402, 3163210, 3163242, 3163338,
    3163370, 3163722, 3163754, 3163850, 3163882, 3165386, 3165418, 3165898, 3165930, 3171402,
    3171434, 3171530, 3171562, 3171914, 3171946, 3172042, 3172074, 3173578, 3173610, 3174090,
    3174122, 3195978, 3196010, 3196106, 3196138, 3196490, 3196522, 3196650, 3198026, 3198154,
    3198186, 3198538, 3198570, 3198666, 3198698, 3204170, 3204682, 3204714, 3204810, 3204842,
    3206218, 3206250, 3206346, 3206378, 3206890, 3212362, 3212394, 3212490, 3212522, 3212874,
    3212906, 3213002, 3213034, 3214538, 3214570, 3215050, 3215082, 3215562, 3215594, 3215770,
    3215802, 3216138, 3216154, 3216186, 3216314, 3217674, 3217690, 3217722, 3217818, 3217850,
    3218186, 3218234, 3218330, 3218362, 3223754, 3223786, 3224330, 3224346, 3224378, 3224474,
    3224506, 3226378, 3226394, 3226426, 3226522, 3226554, 3248330, 3248362, 3248394, 3248410,
    3248906, 3248922, 3248954, 3249082, 3250442, 3250458, 3250490, 3250618, 3250954, 3250970,
    3251002, 3251098, 3251130, 3258650, 3258682, 3259162, 3259322, 3343434, 3343466, 3343562,
    3343594, 3343946, 3343978, 3344074, 3344106, 3345482, 3345514, 3345610, 3345642, 3345994,
    3346026, 3346122, 3346506, 3346538, 3346634, 3346666, 3346714, 3346842, 3346874, 3347210,
    3348746, 3348762, 3348794, 3348890, 3348922, 3354698, 3354730, 3354826, 3354858, 3356938,
    3357082, 3357114, 3357450, 3357466, 3357626, 3379402, 3379434, 3381514, 3381530, 3381562,
    3381658, 3381690, 3382026, 3382042, 3382074, 3387466, 3387498, 3387674, 3387706, 3389706,
    3389722, 3389850, 3389882, 3390234, 3390362, 3739722, 3739754, 3739914, 3739962, 3740058,
    3740090, 3740426, 3740442, 3740474, 3740570, 3740602, 3741962, 3742106, 3742474, 3742522,
    3742618, 3742650, 3748250, 3748282, 3748666, 3748762, 3748794, 3772682, 3772730, 3772826,
    3773194, 3773210, 3773242, 3773370, 3774746, 3774778, 3775242, 3775290, 3775386, 3781386,
    3781402, 3781434, 3781530, 3781562, 3783434, 3783450, 3783482, 3783578, 3783610, 3870794,
    3870986, 3871002, 3871034, 3871130, 3871162, 3871498, 3871642, 3871674, 3879114, 3879146,
    3879178, 3879194, 3879226, 3879322, 3879690, 3879706, 3881226, 3881370, 3881402, 3881882,
    3903754, 3903770, 3903802, 3903898, 3903930, 3905802, 3905818, 3905850, 3905946, 3906314,
    3911946, 3911962, 3911994, 3912458, 3912506, 3913994, 3914010, 3914042, 3914138, 3914170,
    4264202, 4266250, 4266266, 4266298, 4266394, 4266426, 4266762, 4266810, 4266906, 4266938,
    4272394, 4272410, 4272538, 4272906, 4272922, 4272954, 4273050, 4273082, 4274954, 4275098,
    4296970, 4296986, 4297018, 4297114, 4297146, 4297482, 4297498, 4297530, 4297658, 4299018,
    4299066, 4299674, 4305210, 4305674, 4305690, 4305818, 4307210, 4307226, 4307354, 4307722,
    4307738, 4307770, 4307866, 4307898, 4395290, 4395322, 4395418, 4395450, 4397338, 4397370,
    4397466, 4397498, 4403482, 4403514, 4403610, 4404122, 4404154, 4405658, 4405690, 4406042,
    4406074, 4406170, 4428058, 4428090, 4428186, 4428218, 4428570, 4428602, 4430106, 4430138,
    4430234, 4430266, 4436250, 4436282, 4436762, 4436890, 4438298, 4438426, 4438458, 4438810,
    4438842, 4460826, 4460858, 4460954, 4460986, 4461338, 4461370, 4461466, 4461498, 4462874,
    4462906, 4463386, 4463418, 4463514, 4463546, 4469018, 4469146, 4469178, 4469530, 4469658,
    4471066, 4471194, 4471578, 4471706, 4471738, 4473114, 4473146, 4473626, 4473754, 4473786,
    4474570, 4474602, 4475930, 4475962, 4475978, 4476010, 4476106, 4476138, 4476522, 4476618,
    4482074, 4482250, 4482282, 4482794, 4484122, 4484154, 4484298, 4484330, 4484682, 4484714,
    4484810, 4505882, 4506010, 4506394, 4506426, 4506522, 4506554, 4506650, 4506698, 4506730,
    4507210, 4507242, 4508698, 4508906, 4509258, 4509290, 4509386, 4509418, 4516890, 4516922,
    4516938, 4516970, 4517066, 4517098, 4517450, 4517482, 4517578, 4517610, 4604698, 4604730,
    4604826, 4605002, 4605130, 4605162, 4607002, 4607050, 4607082, 4607178, 4607210, 4607722,
    4613178, 4613322, 4613354, 4613834, 4613866, 4615194, 4615226, 4615370, 4615402, 4615754,
    4615786, 4615882, 4615914, 4636954, 4637082, 4637114, 4639770, 4639802, 4639818, 4639850,
    4639946, 4639978, 4640362, 4640490, 4645914, 4645962, 4645994, 4646474, 4646506, 4647962,
    4648010, 4648042, 4648138, 4648170, 4648554, 4648650, 4985114, 4985146, 4985242, 4985274,
    4985754, 4985786, 4987162, 4987194, 4987290, 4987322, 4993306, 4993338, 4993434, 4993466,
    4993818, 4993850, 4993946, 4993978, 4995482, 4995514, 4995866, 4995898, 4995994, 4996026,
    4997402, 4997434, 4997530, 4997562, 4998170, 4998202, 4998250, 4998346, 4998378, 4998730,
    4998762, 4998858, 4998890, 5006362, 5006394, 5006410, 5006442, 5006538, 5006922, 5006954,
    5007050, 5007082, 5030170, 5030202, 5030298, 5030330, 5030938, 5030970, 5031114, 5031146,
    5031530, 5033546, 5033578, 5033674, 5039130, 5039162, 5039690, 5039722, 5039818, 5039850,
    5041178, 5041210, 5041738, 5041770, 5137610, 5137642, 5137994, 5139658, 5139690, 5161242,
    5161274, 5161370, 5161402, 5162010, 5162042, 5162058, 5162090, 5162186, 5164058, 5164090,
    5164106, 5164234, 5164650, 5170202, 5170234, 5170250, 5170282, 5170378, 5170762, 5170794,
    5170890, 5170922, 5172250, 5172282, 5172298, 5172330, 5172426, 5172810, 5172842, 6570266,
    6570298, 6570394, 6570426, 6571210, 6571722, 6573082, 6573114, 6573130, 6573162, 6573290,
    6573770, 6573802, 6579226, 6579914, 6579946, 6581450, 6581482, 6581834, 6581866, 6581962,
    6603546, 6603578, 6603706, 6603802, 6603850, 6603882, 6604362, 6604394, 6605850, 6605898,
    6605930, 6606410, 6606442, 6606538, 6606570, 6614042, 6614074, 6614090, 6614122, 6614218,
    6614250, 6614602, 6614634, 6614730, 6614762, 6702106, 6702282, 6702794, 6702826, 6704154,
    6704202, 6704234, 6704330, 6704362, 6704842, 6704874, 6712346, 6712378, 6712394, 6712522,
    6712554, 6712906, 6712938, 6713034, 6713066, 6736922, 6736954, 6736970, 6737002, 6737098,
    6737482, 6737514, 6737610, 6743066, 6743114, 6743146, 6743626, 6743658, 6745162, 6745194,
    6745322, 6745706, 6745802, 7094554, 7094586, 7095402, 7096010, 7096042, 7098090, 7127834,
    7127866, 7127962, 7127994, 7128090, 7128122, 7128138, 7128170, 7128266, 7128298, 7128650,
    7128682, 7128810, 7130138, 7130170, 7130186, 7130218, 7130698, 7130730, 7136282, 7136314,
    7136842, 7136874, 7136970, 7137002, 7138330, 7138362, 7138378, 7138410, 7138922, 7139050,
    7226394, 7226426, 7226442, 7226474, 7226570, 7226602, 7226954, 7226986, 7227082, 7227114,
    7234586, 7234618, 7234634, 7234666, 7234762, 7234794, 7235146, 7235274, 7235306, 7259162,
    7259194, 7259210, 7259242, 7259338, 7259370, 7261210, 7261242, 7261290, 7267354, 7267386,
    7267402, 7267434, 7268042, 7268074, 7269450, 7269482, 7269578, 7269610, 9506890, 9507594,
    9507610, 9507642, 9507738, 9507770, 9509130, 9509642, 9509690, 9509786, 9509818, 9515210,
    9515242, 9515274, 9515290, 9515418, 9515786, 9515930, 9515962, 9517834, 9517850, 9517882,
    9517978, 9518010, 9539898, 9540362, 9540378, 9540410, 9541898, 9542074, 9542410, 9542554,
    9542586, 9548554, 9548570, 9548602, 9548698, 9550090, 9550106, 9550234, 9550602, 9550618,
    9550650, 9550746, 9550778, 9637962, 9637994, 9638154, 9638170, 9638202, 9638298, 9638330,
    9640202, 9640218, 9640346, 9640378, 9646346, 9647002, 9647034, 9648394, 9648538, 9648570,
    9648906, 9679114, 9679130, 9679626, 9681162, 9681178, 9681210, 9681306, 9681338, 9681674,
    9681690, 9681722, 9681818, 10031178, 10031210, 10031418, 10031546, 10031882, 10031898,
    10032058, 10033978, 10034074, 10039498, 10039530, 10039562, 10039578, 10039706, 10039738,
    10040074, 10040090, 10040122, 10040218, 10040250, 10042122, 10042138, 10042170, 10042266,
    10042298, 10064138, 10064314, 10064650, 10064666, 10064698, 10064826, 10072842, 10072858,
    10072890, 10072986, 10074378, 10074394, 10074522, 10074906, 10162618, 10170570, 10170602,
    10170634, 10170650, 10170682, 10170778, 10170810, 10171146, 10171162, 10171290, 10171322,
    10172682, 10172826, 10172858, 10173194, 10173210, 10195210, 10195226, 10195258, 10195354,
    10195386, 10197258, 10197274, 10197306, 10197402, 10197434, 10203402, 10203418, 10203450,
    10203914, 10203930, 10203962, 10204058, 10204090, 10205450, 10205466, 10205594, 10205626,
    10205978, 10206010, 11604410, 11604746, 11604762, 11604922, 11606282, 11606298, 11606458,
    11606794, 11606842, 11606938, 11606970, 11612362, 11612394, 11612938, 11612954, 11612986,
    11613082, 11613114, 11614986, 11615002, 11615034, 11615130, 11615162, 11637002, 11637514,
    11637530, 11637562, 11639050, 11639066, 11639098, 11639226, 11639562, 11639578, 11639610,
    11639706, 11639738, 11647258, 11647290, 11647770, 11647802, 11735114, 11735146, 11735306,
    11735450, 11735482, 11735818, 11737354, 11737370, 11737402, 11737498, 11737530, 11743434,
    11743498, 11743514, 11743546, 11743674, 11745546, 11745722, 11770122, 11770138, 11770170,
    11770266, 11770634, 11770650, 11770682, 11776266, 11776282, 11776314, 11778314, 11778330,
    11778458, 11778490, 11778970, 12128330, 12128362, 12128522, 12128570, 12128698, 12129034,
    12129050, 12129082, 12129178, 12129210, 12130570, 12131082, 12131130, 12131226, 12131258,
    12136890, 12161290, 12161306, 12161434, 12161466, 12161802, 12161818, 12161850, 12161978,
    12163354, 12163386, 12163850, 12163994, 12169994, 12170010, 12170042, 12170138, 12170170,
    12172042, 12172058, 12172090, 12172186, 12172218, 12259594, 12259642, 12259738, 12259770,
    12260106, 12260250, 12260282, 12267722, 12267754, 12267786, 12267802, 12267834, 12269978,
    12270010, 12292362, 12292410, 12292506, 12292538, 12294426, 12294458, 12294922, 12300570,
    12300602, 12301210, 12652986, 12653338, 12654906, 12655034, 12655418, 12655514, 12655546,
    12661530, 12661562, 12661658, 12661690, 12663578, 12663706, 12663738, 12685626, 12685754,
    12686106, 12686138, 12686266, 12687674, 12688282, 12694298, 12694330, 12694426, 12696346,
    12696378, 12696474, 12696506, 12783882, 12783898, 12783930, 12784026, 12784058, 12784394,
    12785930, 12786106, 12792586, 12794122, 12794266, 12794298, 12794634, 12794650, 12794682,
    12794778, 12794810, 12816650, 12816698, 12818698, 12818714, 12818746, 12818842, 12818874,
    12819210, 12824842, 12824858, 12824890, 12825354, 12825370, 12825402, 12825498, 12825530,
    12827402, 12849434, 12849466, 12849562, 12849594, 12849946, 12849978, 12850074, 12850106,
    12851482, 12851514, 12852122, 12852154, 12858138, 12858170, 12858266, 12858298, 12860186,
    12860218, 12860314, 12860346, 12862234, 12862266, 12862362, 12862394, 12863050, 12863178,
    12863210, 12864538, 12864570, 12864586, 12864618, 12865258, 12870682, 12870714, 12872730,
    12872762, 12872906, 12872938, 12873290, 12873322, 12873418, 12873450, 12895002, 12895034,
    12895130, 12895162, 12897306, 12897354, 12897514, 12897866, 12897898, 12897994, 12898026,
    12905498, 12905530, 12905546, 12905674, 12905706, 12906058, 12906090, 12906186, 12906218,
    12993306, 12993338, 12993434, 12993466, 12993562, 12993594, 12993610, 12993738, 12995610,
    12995658, 12995786, 12995818, 12996330, 13001786, 13001930, 13001962, 13002442, 13002474,
    13003802, 13003834, 13003978, 13004010, 13004362, 13004394, 13004490, 13004522, 13034570,
    13036618, 13036650, 13037258, 13373754, 13373882, 13374362, 13374394, 13375802, 13375898,
    13375930, 13381914, 13381946, 13382042, 13382074, 13382426, 13382458, 13382554, 13382586,
    13384090, 13384122, 13384474, 13384506, 13386010, 13386042, 13386138, 13386170, 13386858,
    13387338, 13387466, 13387498, 13394970, 13395002, 13395050, 13395146, 13395178, 13395562,
    13395658, 13395690, 13418810, 13418906, 13418938, 13419290, 13419322, 13419546, 13419578,
    13419722, 13419754, 13420106, 13427770, 13428298, 13428426, 13428458, 13429818, 13430378,
    13517722, 13517754, 13526218, 13526250, 13528266, 13528298, 13549882, 13550010, 13550698,
    13550794, 13550826, 13552714, 13558810, 13558842, 13558858, 13558890, 13559370, 13559498,
    13559530, 13560938, 13561450, 14958874, 14958906, 14959002, 14959034, 14959674, 14959818,
    14959850, 14960330, 14960362, 14961690, 14961722, 14961738, 14961770, 14961866, 14961898,
    14962378, 14962410, 14967834, 14967866, 14968426, 14968554, 14969882, 14970058, 14970474,
    14970570, 14970602, 14993002, 14994666, 14995018, 14995050, 15090714, 15090746, 15092762,
    15092794, 15092810, 15092842, 15092938, 15092970, 15093450, 15093482, 15098986, 15099082,
    15099114, 15100954, 15100986, 15101130, 15101514, 15101546, 15125530, 15125562, 15125578,
    15125610, 15125706, 15125738, 15126122, 15126218, 15126250, 15133722, 15133770, 15133802,
    15133898, 15133930, 15134314, 15134410, 15483162, 15483194, 15484618, 15484650, 15486666,
    15486698, 15516442, 15516474, 15516570, 15516602, 15516698, 15516730, 15516778, 15516874,
    15516906, 15517258, 15517290, 15518794, 15519306, 15525450, 15525578, 15525610, 15527530,
    15615002, 15615034, 15615050, 15615178, 15615210, 15615562, 15615690, 15615722, 15623274,
    15623370, 15623402, 15623754, 15647802, 15647850, 15647946, 15647978, 15649850, 15649866,
    15655962, 15655994, 15656042, 15656650, 15656682, 1121035, 1121179, 1121211, 1126683,
    1127355, 1129227, 1129243, 1129275, 1151771, 1151803, 1153803, 1153947, 1153979, 1159947,
    1160091, 1160123, 1161499, 1161531, 1161995, 1162011, 1162043, 1162139, 1162171, 1249563,
    1249595, 1249691, 1249723, 1251611, 1251643, 1251771, 1257739, 1258395, 1259787, 1259931,
    1259963, 1260299, 1260347, 1260443, 1284891, 1290507, 1290555, 1291163, 1292555, 1292571,
    1292603, 1292699, 1292731, 1293067, 1293083, 1293115, 1643275, 1643291, 1643323, 1645467,
    1645499, 1651099, 1651131, 1651467, 1651483, 1651515, 1651611, 1651643, 1653515, 1653531,
    1653563, 1676043, 1676059, 1676091, 1684235, 1684379, 1684411, 1685915, 1686331, 1774491,
    1782027, 1782043, 1782075, 1782171, 1782203, 1782539, 1782683, 1782715, 1784075, 1784251,
    1784603, 1806651, 1806747, 1806779, 1808667, 1808699, 1808795, 1808827, 1814795, 1814811,
    1814843, 1815307, 1815323, 1815483, 1816843, 1817371, 3215803, 3216139, 3217675, 3217691,
    3217851, 3218187, 3218331, 3218363, 3224347, 3224379, 3224475, 3224507, 3226395, 3226427,
    3226523, 3248907, 3248923, 3250443, 3250459, 3250491, 3250955, 3250971, 3251003, 3251099,
    3251131, 3258683, 3346843, 3348747, 3348763, 3348795, 3356939, 3357083, 3357115, 3381515,
    3381531, 3381563, 3381659, 3381691, 3382043, 3382075, 3387675, 3387707, 3389707, 3389851,
    3389883, 3739915, 3740059, 3740091, 3740427, 3740443, 3740475, 3740571, 3740603, 3742475,
    3742619, 3748283, 3772683, 3772731, 3772827, 3773195, 3773211, 3773243, 3774779, 3775243,
    3781403, 3781531, 3781563, 3783451, 3783483, 3783579, 3783611, 3870987, 3871003, 3871035,
    3871131, 3871163, 3871643, 3871675, 3879179, 3879195, 3879227, 3881371, 3881403, 3903755,
    3903899, 3903931, 3905819, 3911947, 3911963, 3911995, 4266267, 4266395, 4266427, 4266811,
    4266939, 4272411, 4272539, 4272923, 4272955, 4273083, 4296987, 4297147, 4297531, 4307355,
    4307739, 4307899, 4395291, 4395419, 4395451, 4397467, 4397499, 4404123, 4404155, 4405659,
    4405691, 4428059, 4428091, 4428187, 4430107, 4430139, 4436251, 4438299, 4438427, 4438811,
    4438843, 4460827, 4460859, 4460987, 4463515, 4463547, 4469147, 4471067, 4471195, 4471707,
    4471739, 4473115, 4473755, 4473787, 4482251, 4482283, 4484811, 4506395, 4506651, 4506699,
    4507211, 4509387, 4516891, 4516923, 4516939, 4516971, 4517099, 4517611, 4607051, 4607083,
    4607211, 4615195, 4615403, 4615883, 4636955, 4637083, 4637115, 4645963, 4645995, 4985115,
    4985243, 4985275, 4987291, 4987323, 4993307, 4993339, 4993435, 4995995, 4996027, 4997435,
    4997531, 4998171, 5006411, 5006443, 5006539, 5006923, 5007051, 5030171, 5030299, 5030331,
    5030939, 5031147, 5039131, 5039163, 5041179, 5041211, 5041739, 5137643, 5137995, 5161371,
    5161403, 5162011, 5162059, 5162187, 5164059, 5164091, 5164235, 5164651, 5170203, 5170235,
    5170283, 5172251, 5172283, 5172299, 5172331, 5172811, 6573083, 6573115, 6573163, 6573291,
    6573771, 6579915, 6581835, 6581867, 6581963, 6603547, 6603803, 6603851, 6604363, 6604395,
    6605851, 6605899, 6606443, 6606539, 6606571, 6614043, 6614075, 6614091, 6614219, 6704155,
    6704203, 6704235, 6712379, 6712395, 6712555, 6712907, 6736923, 6736955, 6737099, 6737611,
    6743067, 6745323, 7095403, 7096011, 7127867, 7128123, 7128299, 7128811, 7130139, 7130219,
    7130699, 7130731, 7136875, 7137003, 7138379, 7139051, 7226427, 7226475, 7226603, 7226955,
    7226987, 7227115, 7234667, 7234795, 7235147, 7235275, 7235307, 7259163, 7259195, 7259339,
    7259371, 7261211, 7261291, 7268043, 7269451, 7269483, 7269611, 12652987, 12655419, 12655515,
    12655547, 12661563, 12661659, 12661691, 12663707, 12663739, 12686139, 12687675, 12694299,
    12694331, 12696347, 12696379, 12783899, 12783931, 12784027, 12794267, 12794683, 12794779,
    12794811, 12818747, 12818843, 12824859, 12825403, 12825499, 12849947, 12849979, 12850107,
    12858171, 12858267, 12858299, 12860315, 12860347, 12862267, 12862363, 12862395, 12864571,
    12864619, 12870683, 12870715, 12872731, 12872763, 12895003, 12895163, 12905547, 12905675,
    12905707, 12906059, 12906187, 12993435, 12993467, 12993563, 12993595, 12993611, 12995659,
    12995787, 13001787, 13001931, 13001963, 13002443, 13003803, 13003835, 13004011, 13036651,
    13037259, 13374395, 13375899, 13375931, 13382427, 13382459, 13382555, 13384091, 13384123,
    13386043, 13387339, 13394971, 13395003, 13395051, 13395147, 13395179, 13395563, 13418907,
    13418939, 13419323, 13428299, 13517723, 13517755, 13528267, 13528299, 13550699, 13550795,
    13550827, 13558843, 13558891, 13559371, 14958875, 14959675, 14959851, 14960331, 14960363,
    14961691, 14961771, 14968427, 14970475, 14970603, 14994667, 14995019, 15090747, 15092763,
    15092795, 15092811, 15092843, 15098987, 15099083, 15099115, 15101515, 15125531, 15125611,
    15125739, 15126123, 15126219, 15126251, 15133803, 15133931, 15134315, 15134411, 15483195,
    15484651, 15486667, 15486699, 15516699, 15516731, 15516779, 15516907, 15517259, 15525451,
    15525579, 15525611, 15615003, 15615035, 15615051, 15615563, 15623275, 15647803, 15647947,
    15647979, 15655963, 15656043, 15656651, 17065163, 17065707, 17067243, 17067723, 17089643,
    17090123, 17091659, 17091819, 17092203, 17100395, 17188043, 17188587, 17196235, 17222731,
    17223275, 17230923, 17231467, 17581643, 17581675, 17581771, 17581803, 17589835, 17614411,
    17616459, 17616491, 17622603, 17622635, 17624139, 17624651, 17624683, 17712235, 17712331,
    17712715, 17720395, 17720427, 17720523, 17720555, 17744971, 17745003, 17747019, 17747051,
    17747563, 17753195, 17755211, 17755243, 17843275, 17843307, 17843915, 17843947, 17876555,
    17876587, 17878091, 17878603, 17878635, 17884747, 17886795, 17886827, 17892427, 17892459,
    17894987, 17895019, 17903691, 17903851, 17903883, 17904027, 17906459, 17928987, 17929147,
    17936459, 17936491, 17938715, 17939227, 17939259, 18024043, 18025547, 18026603, 18026763,
    18028827, 18034795, 18037003, 18037515, 18037531, 18037563, 18067531, 18067563, 18067739,
    18067771, 18068235, 18068379, 18069771, 18070283, 18070427, 18428171, 18428187, 18428315,
    18428683, 18428827, 18428859, 18453259, 18461451, 18461627, 18463499, 18463515, 18463547,
    18561435, 18561979, 18583819, 18583835, 18583867, 18586011, 18586043, 18592059, 19941099,
    19949131, 19949163, 19949259, 19949291, 19973323, 19973355, 19973707, 19973739, 19989707,
    19989739, 19990123, 19992987, 19993019, 19994891, 20025611, 20025627, 20026139, 20026171,
    20027659, 20027707, 20028171, 20028187, 20028219, 20121163, 20121195, 20121291, 20121323,
    20134299, 20134683, 20159243, 20159291, 20550587, 20551995, 20648203, 20648219, 20656363,
    20656411, 20656443, 20656923, 20658587, 20658619, 20689163, 20689211, 20691211, 20691259,
    26293147, 26293179, 26295051, 26295067, 26295099, 26319627, 26325771, 26327307, 26327451,
    26327867, 26415419, 26417419, 26417435, 26417563, 26417595, 26456347, 26808427, 26811195,
    26811291, 26817435, 26817467, 26850059, 26851595, 26947851, 26948379, 26950043, 26950427,
    26972571, 26972603, 26974475, 26980619, 26981307, 28381627, 28384059, 28512363, 28514587,
    28520715, 28520891, 28522763, 28522939, 28547339, 28547851, 28553483, 28553499, 28553531,
    28556187, 28905739, 28905915, 28906251, 28906427, 28907787, 28908299, 28938507, 28940571,
    28940603, 29037323, 29044939, 38030443, 38031051, 38038555, 38039115, 38039147, 38063819,
    38071323, 38071531, 38072043, 38161483, 38161515, 38161643, 38169627, 38170315, 38194795,
    38200395, 38200427, 38200939, 38202395, 38202571, 38552683, 38560875, 38561355, 38561483,
    38587979, 38588011, 38588107, 38594251, 38595611, 38716491, 38724667, 38726683, 38726731,
    38726763, 38727243, 40127515, 40128203, 40136299, 40158795, 40158827, 40257227, 40257259,
    40258795, 40291355, 40291531, 40291915, 40291947, 40297579, 40298091, 40650443, 40682523,
    40682555, 40684571, 40684603, 40684651, 40685131, 40685163, 40690715, 40692763, 40692795,
    40692811, 40780907, 40781035, 40781387, 40781419, 40813595, 40815643, 40815675, 46417611,
    46417643, 46427195, 46427723, 46427755, 46451947, 46459979, 46460139, 46460491, 46460619,
    46550091, 46550219, 46556363, 46556395, 46556875, 46591083, 46941771, 46949403, 46949435,
    46949483, 46949995, 46974187, 46982203, 46982859, 46982891, 47082699, 47105131, 47105227,
    47105259, 47113275, 47113803, 48514107, 48514283, 48514763, 48514795, 48516123, 48516155,
    48522267, 48522299, 48525035, 48645147, 48645179, 48647195, 48647227, 48655419, 48655947,
    48680171, 48680651, 48680683, 49041099, 49041131, 49071211, 49080011, 49080043, 49169435,
    49169467, 49169995, 49170123, 49202283, 50611947, 50619595, 50620139, 50622155, 50622187,
    50646635, 50646731, 50654923, 50742475, 50743019, 50744523, 50744555, 50750667, 50777323,
    50785355, 50785515, 51136235, 51144427, 51178571, 51179115, 51266763, 51274955, 51301451,
    51301995, 51441227, 51441259, 51441355, 51441387, 51449419, 51449451, 51449547, 51449579,
    51458459, 51579979, 51591947, 51622667, 51622811, 51624203, 51624715, 51983115, 52007691,
    53495499, 53495531, 53497579, 53503691, 53503723, 53549835, 53580011, 53580603, 53582603,
    53675723, 53675755, 53677259, 53678859, 53711051, 53711083, 54113035, 54202779, 54203147,
    54235403, 54235547, 54237467, 59841291, 59882251, 60406043, 60502283, 60502795, 60504843,
    60504859, 60535563, 61946635, 62067099, 62069003, 62069019, 62101787, 62102283, 62460683,
    62462907, 62493451, 62626571, 4509388, 4516892, 4516924, 4517100, 4607052, 4607084, 4607212,
    4615196, 4645964, 4645996, 5006412, 5006444, 5006540, 5007052, 5039132, 5039164, 5162188,
    5164652, 5170236, 5172252, 5172332, 6573084, 6581836, 6581868, 6581964, 6604364, 6604396,
    6736924, 6736956, 6737612, 6745324, 7128124, 7130140, 7130700, 7137004, 7138380, 7226604,
    7226956, 7226988, 7227116, 7259164, 7259196, 12872732, 12872764, 12905548, 12905676,
    12905708, 12906060, 12995660, 13001788, 13001964, 13003804, 13387340, 13394972, 13395004,
    13395052, 13528268, 13528300, 13550700, 13550796, 13550828, 13558844, 14959676, 14960332,
    14961692, 14970476, 15092764, 15092796, 15125612, 15126124, 15126220, 15126252, 15486668,
    15486700, 15516732, 15525452, 15525580, 15525612, 15615004, 15615036, 15615564, 15623276,
    17065708, 17091660, 17188588, 17230924, 17581676, 17581772, 17581804, 17616460, 17616492,
    17622604, 17622636, 17720396, 17720428, 17720524, 17720556, 17744972, 17745004, 17753196,
    17755244, 17843276, 17843308, 17843916, 17843948, 17876556, 17876588, 17884748, 17886796,
    17892428, 17892460, 17894988, 17895020, 17928988, 17929148, 17939260, 18028828, 18067532,
    18067564, 18428172, 18428188, 18461628, 18463516, 18583820, 18583836, 18583868, 19949132,
    19949164, 19949260, 19949292, 19973324, 19973356, 19973708, 19973740, 19989708, 19989740,
    20025612, 20025628, 20027708, 20121164, 20121292, 20121324, 20550588, 20656364, 20656924,
    26293148, 26327308, 26327452, 26327868, 26415420, 26417420, 26417564, 26417596, 26456348,
    28384060, 28520892, 28522764, 28556188, 28906428, 28907788, 28940572, 29037324, 50611948,
    50622156, 50622188, 50646636, 50744524, 50744556, 50785356, 50785516, 51179116, 51274956,
    51301996, 51441228, 51441260, 51441356, 51441388, 51449420, 51449452, 51449548, 51458460,
    51579980, 51622668, 53497580, 53503692, 53580012, 53675724, 53675756, 53677260, 54113036,
    54203148, 54235548, 59841292, 60406044, 60504844, 61946636, 62101788, 62102284, 68260636,
    68268988, 68360476, 68368828, 68401564, 68754332, 68754364, 68784924, 68923676, 68923708,
    70327196, 70327228, 70457628, 70457660, 70496572, 70882076, 70882108, 71616076, 72096156,
    72096188, 72115308, 72139196, 72279100, 73712668, 73712716, 73715436, 73845788, 74245740,
    74247916, 74344012, 74344140, 74344172, 79979548, 80102428, 80102476, 80112668, 80112700,
    82207980, 82625644, 105180396, 105309804, 105825356, 107245164, 107791420, 107890252,
    107890284, 114091756, 115624988, 115625020, 115631132, 152645900, 152803772, 161028924,
    161029020, 161190300, 162730092, 188420508, 188420876, 194722572, 196320012, 202586524,
    202586556, 203141404, 203141436, 204544924, 204714300, 205099804, 205207996, 205833804,
    206490684, 206496796, 206496828, 214330396, 241624172, 242009116, 242009148, 242019388,
    249842716, 18583821, 26417421, 54113037, 61946637, 70327229, 72115309, 73712669, 105309805,
    202586525, 241624173, 273441869, 288556749, 294850877, 421239229, 823335197, 966496669]

/-- Packed-word representative for the `i`-th element of `G` (`i ∈ Fin 6048`). -/
def word (i : Fin 6048) : List Step :=
  decodeWord (wordCodeArray.getD i.val 0)

/-- Cayley-table column for left multiplication by `a`: `nextA[i]` is the index of the
element `a · evalWord (word i)`. -/
def nextA : Array Nat :=
  #[1, 5, 8, 0, 12, 3, 16, 18, 20, 2, 25, 27, 29, 4, 34, 36, 38, 6, 43, 7, 9, 50, 52, 54, 56,
    58, 10, 63, 11, 13, 70, 72, 74, 76, 78, 14, 83, 15, 17, 90, 92, 94, 96, 19, 100, 102, 104,
    106, 108, 110, 112, 21, 117, 22, 122, 23, 127, 24, 26, 134, 136, 138, 140, 28, 144, 146,
    148, 150, 152, 154, 156, 30, 161, 31, 166, 32, 171, 33, 35, 178, 180, 182, 184, 37, 188,
    190, 192, 194, 196, 198, 200, 39, 205, 40, 210, 41, 215, 42, 220, 222, 224, 44, 229, 45,
    234, 46, 239, 47, 187, 48, 248, 49, 51, 255, 257, 259, 261, 53, 265, 267, 216, 270, 55, 274,
    276, 278, 280, 57, 284, 286, 288, 290, 223, 292, 294, 59, 299, 60, 303, 61, 308, 62, 313,
    197, 315, 64, 320, 65, 325, 66, 330, 67, 335, 68, 176, 69, 71, 346, 348, 350, 236, 73, 355,
    357, 359, 361, 75, 365, 367, 368, 370, 77, 374, 376, 378, 380, 155, 382, 384, 79, 389, 80,
    394, 81, 399, 82, 404, 109, 406, 84, 411, 85, 416, 86, 421, 87, 143, 88, 430, 89, 91, 437,
    439, 441, 443, 93, 447, 449, 400, 452, 95, 456, 458, 460, 462, 97, 466, 467, 469, 471, 473,
    98, 132, 99, 101, 484, 486, 488, 418, 103, 493, 495, 497, 499, 105, 503, 505, 506, 508, 107,
    512, 514, 516, 518, 520, 522, 524, 526, 111, 529, 531, 533, 535, 537, 539, 541, 113, 546,
    114, 551, 115, 556, 116, 560, 562, 564, 118, 569, 119, 120, 576, 121, 563, 581, 583, 123,
    588, 124, 592, 125, 596, 126, 601, 538, 603, 128, 606, 129, 611, 130, 616, 131, 621, 133,
    135, 628, 630, 632, 634, 137, 638, 640, 642, 139, 646, 648, 650, 652, 141, 656, 657, 659,
    661, 663, 142, 145, 670, 672, 674, 168, 147, 679, 681, 683, 685, 149, 689, 691, 692, 694,
    151, 698, 700, 702, 704, 153, 705, 707, 709, 711, 713, 715, 717, 719, 721, 723, 725, 157,
    730, 158, 735, 159, 160, 742, 744, 746, 162, 751, 163, 755, 164, 758, 165, 745, 763, 765,
    167, 676, 772, 169, 777, 170, 782, 722, 784, 172, 787, 173, 792, 174, 797, 175, 801, 177,
    179, 808, 810, 812, 814, 181, 818, 820, 309, 823, 183, 827, 829, 831, 833, 185, 837, 838,
    840, 842, 844, 186, 189, 851, 853, 855, 327, 191, 860, 862, 864, 866, 193, 870, 872, 873,
    875, 195, 879, 881, 883, 885, 887, 889, 891, 893, 199, 896, 898, 900, 902, 904, 906, 908,
    201, 911, 202, 916, 203, 921, 204, 925, 927, 929, 206, 934, 207, 208, 941, 209, 928, 946,
    948, 211, 953, 212, 957, 213, 961, 214, 966, 905, 269, 970, 217, 975, 218, 980, 219, 221,
    985, 987, 989, 991, 993, 995, 997, 999, 1001, 1003, 1005, 225, 1010, 226, 1015, 227, 228,
    1022, 1024, 1026, 230, 1031, 231, 1034, 232, 1037, 233, 1025, 1042, 1044, 235, 352, 1051,
    237, 1056, 238, 1061, 1002, 1063, 240, 1066, 241, 1071, 242, 1076, 243, 1080, 244, 1085,
    245, 1090, 246, 1095, 247, 895, 816, 249, 807, 250, 835, 251, 826, 252, 283, 253, 803, 254,
    256, 334, 1128, 1130, 1132, 258, 1136, 1138, 1096, 1141, 260, 1145, 1146, 1148, 1150, 262,
    1154, 1156, 1158, 802, 263, 272, 264, 266, 1170, 931, 1173, 1110, 268, 1178, 775, 1181,
    1183, 1185, 1187, 271, 1191, 1193, 1195, 1197, 805, 273, 275, 1205, 1207, 1209, 1211, 277,
    1215, 1217, 1219, 279, 1223, 1225, 1227, 281, 1231, 1232, 1234, 1236, 804, 282, 285, 1244,
    933, 287, 1249, 1251, 1253, 1255, 289, 1259, 940, 1261, 979, 291, 1266, 1268, 1270, 1272,
    293, 926, 907, 967, 947, 1273, 899, 1275, 295, 1279, 296, 1284, 297, 1289, 298, 897, 1293,
    1295, 300, 1299, 301, 1304, 302, 1294, 903, 1309, 304, 1314, 305, 1318, 306, 1321, 307, 901,
    1274, 822, 1327, 310, 1332, 311, 1335, 312, 314, 1023, 1004, 1062, 1043, 1340, 988, 1342,
    316, 1347, 317, 1352, 318, 319, 986, 1359, 1361, 321, 1366, 322, 1370, 323, 1373, 324, 1360,
    992, 1377, 326, 857, 1384, 328, 1389, 329, 990, 1341, 1394, 331, 1397, 332, 1402, 333, 1127,
    858, 336, 850, 337, 877, 338, 869, 339, 1425, 340, 1430, 341, 1435, 342, 1440, 343, 373,
    344, 846, 345, 347, 620, 1456, 1458, 1460, 349, 1011, 1464, 1421, 1466, 351, 1470, 1472,
    1474, 1476, 1478, 1479, 845, 353, 363, 354, 356, 1491, 1493, 1495, 1437, 358, 1500, 1502,
    1504, 360, 1508, 1510, 362, 1514, 1516, 1517, 1519, 848, 364, 366, 1527, 1529, 1531, 1533,
    1013, 1536, 369, 1540, 1542, 1544, 1545, 371, 1020, 1549, 1059, 1551, 847, 372, 375, 1559,
    1561, 377, 1565, 1567, 1569, 1285, 379, 1574, 1576, 1577, 1579, 381, 1583, 1585, 1587, 383,
    561, 540, 602, 582, 1590, 532, 1592, 385, 1595, 386, 1600, 387, 1605, 388, 530, 1609, 1611,
    390, 1616, 391, 392, 1623, 393, 1610, 536, 1628, 395, 1633, 396, 1637, 397, 1640, 398, 534,
    1591, 451, 1647, 401, 1652, 402, 1657, 403, 405, 743, 724, 783, 764, 1662, 708, 1664, 407,
    1669, 408, 1674, 409, 410, 706, 1681, 1683, 412, 1688, 413, 1691, 414, 1694, 415, 1682, 712,
    1699, 417, 490, 1706, 419, 1711, 420, 710, 1663, 1716, 422, 1719, 423, 1724, 424, 1729, 425,
    1732, 426, 1737, 427, 1742, 428, 1747, 429, 1589, 636, 431, 627, 432, 654, 433, 645, 434,
    465, 435, 623, 436, 438, 1778, 1780, 440, 1784, 1786, 1748, 1789, 442, 1793, 1794, 1796,
    1798, 444, 1802, 1804, 1806, 622, 445, 454, 446, 448, 1818, 1613, 1820, 1761, 450, 1824,
    1054, 1827, 1829, 1831, 1833, 453, 1836, 1838, 1840, 1842, 625, 455, 457, 1850, 1852, 760,
    1855, 459, 1859, 1861, 1863, 461, 1867, 1869, 1871, 463, 1875, 1876, 1878, 1880, 624, 464,
    1886, 1615, 468, 1891, 1893, 1895, 1897, 470, 1901, 1622, 1903, 1656, 472, 1907, 1909, 1911,
    1913, 677, 474, 669, 475, 696, 476, 688, 477, 1930, 478, 1935, 479, 1940, 480, 1945, 481,
    511, 482, 665, 483, 485, 984, 1961, 1963, 1965, 487, 1670, 1969, 1926, 1971, 489, 1975,
    1977, 1979, 1981, 1983, 1984, 664, 491, 501, 492, 494, 1996, 1998, 2000, 1942, 496, 2005,
    2007, 498, 2011, 2013, 500, 2017, 2019, 2020, 2022, 667, 502, 504, 2030, 2032, 2034, 2036,
    1672, 2039, 507, 2043, 2045, 2047, 2048, 509, 1679, 2052, 1714, 2054, 666, 510, 513, 2062,
    2064, 515, 2068, 2070, 2072, 552, 517, 2077, 2079, 2080, 2082, 519, 2086, 2088, 2090, 521,
    2093, 2095, 2096, 2098, 523, 2101, 2103, 597, 2106, 525, 2109, 2111, 2113, 1726, 527, 2117,
    2118, 2120, 2122, 528, 2124, 1817, 2126, 613, 2128, 2130, 2132, 2134, 2136, 2138, 2139,
    1753, 2142, 2144, 2146, 2148, 2150, 2152, 2154, 2156, 2158, 2160, 2162, 2164, 2166, 2168,
    542, 2172, 543, 2177, 544, 2181, 545, 2185, 2187, 2189, 547, 2192, 548, 549, 2198, 550,
    2188, 2203, 2074, 2207, 553, 2211, 554, 2214, 555, 2219, 2167, 2221, 557, 2226, 558, 2230,
    559, 2235, 1654, 2238, 2240, 2241, 2243, 2245, 2247, 2249, 1900, 2251, 565, 566, 2256, 567,
    568, 2261, 1887, 2263, 570, 571, 2270, 572, 2273, 573, 1906, 574, 1809, 575, 2284, 2250,
    2286, 577, 2289, 578, 2293, 579, 2298, 580, 2186, 2169, 2220, 2204, 2302, 2161, 2304, 584,
    2308, 585, 2313, 586, 2315, 587, 2159, 2319, 2321, 589, 2325, 590, 2330, 591, 2320, 2165,
    2335, 593, 2340, 594, 2344, 595, 2163, 2303, 2105, 2350, 598, 2355, 599, 2358, 600, 2262,
    1811, 2285, 1888, 2363, 2237, 2365, 604, 605, 2236, 2372, 2374, 607, 2379, 608, 2383, 609,
    2386, 610, 2373, 1763, 2390, 612, 2395, 614, 615, 2239, 2364, 2400, 617, 2403, 618, 2408,
    619, 1455, 655, 626, 629, 2421, 2423, 2425, 631, 2429, 2431, 1936, 2434, 633, 2438, 2439,
    2441, 2443, 635, 2447, 2449, 2451, 644, 637, 639, 2458, 2460, 1885, 641, 2463, 1387, 2466,
    2468, 643, 2472, 2474, 2476, 2478, 647, 2482, 2484, 1696, 2487, 649, 2491, 2493, 2495, 651,
    2499, 2501, 653, 2505, 2506, 2508, 2510, 2512, 658, 2516, 2518, 2520, 2522, 660, 2525, 2527,
    662, 2531, 2533, 2535, 2537, 697, 668, 671, 1339, 2545, 2547, 2549, 673, 731, 2553, 2026,
    2555, 675, 2559, 2561, 2563, 2565, 2567, 2568, 687, 678, 680, 2576, 2578, 2580, 1734, 682,
    2585, 2587, 2338, 684, 2592, 2594, 686, 2598, 2600, 2205, 690, 2605, 2607, 2609, 2611, 733,
    2614, 693, 2618, 2620, 2622, 2623, 695, 740, 2627, 780, 2629, 699, 2633, 2635, 701, 2639,
    2641, 2643, 1601, 703, 2647, 2649, 2650, 2652, 2654, 2656, 2658, 2660, 2662, 2664, 1967,
    2666, 778, 2668, 2670, 2672, 2674, 2676, 2613, 2678, 1918, 2680, 714, 2682, 2684, 2686, 794,
    716, 2689, 2690, 2692, 2694, 718, 2696, 2698, 2699, 2701, 720, 2703, 2705, 1641, 2708, 2710,
    2712, 2714, 2716, 1712, 2718, 2551, 2720, 2040, 2722, 726, 2726, 727, 2731, 728, 2736, 729,
    2050, 2740, 2742, 732, 2747, 734, 2741, 2752, 2754, 736, 2757, 737, 2761, 738, 2765, 739,
    1954, 2041, 741, 2776, 2778, 2780, 2782, 2784, 2786, 2788, 2790, 2792, 2794, 2796, 747,
    2801, 748, 2802, 749, 750, 2807, 2809, 2811, 752, 2816, 753, 2819, 754, 2810, 2823, 2825,
    756, 2830, 757, 2833, 2793, 2835, 759, 1854, 2839, 761, 2844, 762, 1956, 2723, 2038, 2753,
    2847, 2719, 2849, 766, 2853, 767, 2858, 768, 2861, 769, 770, 2542, 771, 2569, 2721, 2871,
    773, 2876, 774, 1180, 2882, 776, 1928, 2848, 2887, 779, 2892, 781, 2808, 2795, 2834, 2824,
    2897, 2779, 2899, 785, 2904, 786, 2777, 2907, 2909, 788, 2914, 789, 2917, 790, 791, 2908,
    2783, 2921, 793, 2688, 2926, 795, 2931, 796, 2781, 2898, 2932, 798, 2935, 799, 2939, 800,
    1100, 836, 806, 809, 2950, 2951, 811, 2955, 2798, 1431, 2959, 813, 2963, 2964, 2966, 2968,
    815, 2972, 2974, 2976, 825, 817, 819, 2984, 1172, 2986, 1241, 821, 2990, 1709, 2993, 2995,
    2997, 2998, 824, 3001, 2756, 3004, 3006, 828, 3010, 3012, 1039, 3015, 830, 3019, 3021, 3023,
    832, 2936, 3028, 834, 3032, 3033, 3035, 3037, 2867, 1298, 839, 3042, 3044, 3046, 3048, 841,
    3051, 1243, 3053, 1263, 843, 3057, 3059, 3061, 3063, 878, 849, 852, 1661, 3071, 3073, 3075,
    854, 1348, 3079, 1523, 3081, 856, 2290, 3086, 3088, 3090, 3092, 3093, 868, 859, 861, 2193,
    3101, 3103, 1082, 863, 3108, 3110, 865, 3113, 3115, 867, 3119, 3121, 3122, 3124, 871, 3128,
    3130, 3132, 3133, 1350, 2367, 874, 3139, 3141, 3143, 3144, 876, 1357, 3148, 1392, 3150, 880,
    3154, 3156, 882, 3160, 3162, 3164, 917, 884, 3169, 3171, 3172, 3173, 886, 3177, 2337, 888,
    3181, 3183, 3184, 3186, 890, 3189, 3191, 962, 3194, 892, 3197, 3199, 2913, 1404, 894, 2267,
    3203, 3204, 3206, 3208, 2983, 3210, 977, 3212, 3214, 3216, 3218, 3220, 1246, 3222, 1163,
    3224, 3226, 3228, 3230, 3232, 3234, 3236, 3237, 3239, 3241, 3243, 3245, 3247, 3249, 3251,
    909, 3254, 910, 3258, 3260, 3262, 912, 2264, 913, 914, 3268, 915, 3261, 3273, 3166, 2274,
    918, 2277, 919, 3280, 920, 3284, 3248, 3286, 922, 3291, 923, 3295, 924, 3300, 1188, 3302,
    1169, 3304, 3306, 3308, 3310, 3312, 3050, 3314, 930, 3319, 932, 3324, 3038, 3326, 935, 936,
    3332, 937, 3335, 938, 3056, 939, 1104, 3344, 3313, 3346, 942, 3349, 943, 3352, 944, 3357,
    945, 3259, 3250, 3285, 3274, 3361, 3242, 3363, 949, 3365, 950, 951, 3370, 952, 3240, 3374,
    3375, 954, 3379, 955, 3384, 956, 2870, 3246, 3389, 958, 3391, 959, 3395, 960, 3244, 3362,
    3193, 3400, 963, 3405, 964, 3408, 965, 3325, 1102, 3345, 3039, 1177, 968, 969, 3301, 3417,
    3419, 971, 3424, 972, 3428, 973, 3431, 974, 3418, 1239, 3434, 976, 3439, 978, 3303, 1186,
    3444, 981, 3447, 982, 3450, 983, 1960, 3455, 3457, 3459, 3461, 3077, 3463, 1057, 3465, 3467,
    3469, 3471, 3473, 1535, 3475, 1451, 3477, 994, 3479, 3481, 3483, 1073, 996, 3486, 3487,
    3489, 3491, 998, 3493, 2729, 3494, 3496, 1000, 3498, 3500, 1322, 2311, 3503, 3505, 3507,
    3509, 1390, 3511, 1462, 3513, 3136, 3515, 1006, 3519, 1007, 3523, 1008, 3528, 1009, 3146,
    3532, 3534, 1012, 3539, 1014, 3533, 3544, 3546, 1016, 3548, 1017, 3552, 1018, 3556, 1019,
    1415, 3137, 1021, 3565, 3567, 3569, 3571, 3573, 3575, 3577, 3579, 3580, 3582, 2728, 1027,
    3587, 1028, 3588, 1029, 1030, 3593, 3595, 3597, 1032, 3600, 1033, 3596, 3603, 3605, 1035,
    3610, 1036, 3613, 3581, 2733, 1038, 3014, 3617, 1040, 2734, 1041, 1413, 3516, 3135, 3545,
    3623, 3512, 3625, 1045, 3629, 1046, 3634, 1047, 3636, 1048, 1049, 1453, 1050, 1480, 3514,
    3645, 1052, 3648, 1053, 1826, 3654, 1055, 1521, 3624, 3657, 1058, 3662, 1060, 3594, 3583,
    3614, 3604, 3667, 3568, 3668, 1064, 3673, 1065, 3566, 3676, 3678, 1067, 3682, 1068, 3684,
    1069, 1070, 3677, 3572, 3688, 1072, 3485, 3693, 1074, 3697, 1075, 3570, 2368, 3698, 1077,
    3701, 1078, 3703, 1079, 3180, 3708, 1081, 3105, 3709, 1083, 3714, 1084, 3188, 3718, 1086,
    3721, 1087, 1088, 3726, 1089, 3196, 3728, 1091, 3733, 1092, 3737, 1093, 1094, 3202, 1140,
    3741, 1097, 3744, 1098, 3747, 1099, 3055, 1101, 3040, 1103, 3030, 1105, 3026, 1106, 3017,
    1107, 3009, 1108, 2999, 1109, 1175, 2988, 1111, 1112, 2970, 1113, 2962, 1114, 2953, 1115,
    2949, 1116, 3095, 1117, 3064, 1118, 3067, 1119, 3096, 1120, 1213, 1121, 1204, 1122, 1229,
    1123, 1222, 1124, 1153, 1125, 1200, 1126, 3456, 3818, 1129, 3822, 3824, 3799, 3827, 1131,
    3829, 3253, 1690, 1133, 3834, 3836, 3838, 1199, 1134, 1143, 1135, 1137, 3846, 3848, 1139,
    3521, 2280, 3852, 3854, 1993, 1142, 3858, 3860, 3862, 3864, 1202, 1144, 3869, 3870, 1147,
    3873, 3875, 3386, 1149, 3879, 3881, 1151, 1749, 3885, 3887, 3889, 1201, 1152, 1155, 3896,
    3898, 3637, 3371, 1157, 3903, 3451, 3905, 1159, 3908, 3910, 3561, 3913, 1247, 1160, 1161,
    1264, 1162, 1258, 3065, 1164, 3094, 1165, 3097, 1166, 3066, 1167, 1190, 1168, 1171, 2234,
    3945, 3947, 3949, 1174, 3953, 3955, 3956, 3958, 1238, 1176, 1179, 1787, 3966, 3378, 1788,
    3969, 3971, 1182, 3974, 3976, 1184, 1795, 2762, 3980, 1797, 2584, 3982, 3984, 1680, 3342,
    3985, 1240, 1189, 1192, 3993, 3995, 1194, 3998, 3999, 3432, 1196, 4003, 4005, 4006, 4008,
    1198, 4012, 4014, 4015, 1230, 1203, 1206, 4021, 1401, 4022, 1208, 4025, 3267, 3928, 4028,
    1210, 4031, 1212, 4033, 4035, 4037, 1221, 1214, 1216, 4042, 4044, 3893, 1218, 4047, 2398,
    4049, 4051, 1220, 4055, 4057, 4059, 4061, 1224, 3390, 4064, 3768, 4065, 1226, 4068, 4070,
    4072, 1228, 4076, 4077, 4079, 4081, 1770, 1233, 4085, 4087, 4088, 4090, 1235, 4092, 4094,
    1237, 4096, 3283, 1727, 4100, 1265, 1242, 1245, 2362, 1958, 2060, 4104, 3415, 3670, 1257,
    1248, 1250, 4113, 4115, 4117, 3790, 1252, 4122, 4124, 2874, 1254, 4128, 4130, 1256, 4134,
    1702, 2755, 1260, 4140, 4142, 4144, 4146, 1262, 4150, 4152, 4154, 4155, 1267, 4159, 4161,
    1269, 3527, 2483, 2488, 3710, 1271, 4168, 1948, 2511, 4170, 4172, 4174, 3576, 3504, 3510,
    3578, 4176, 3231, 4177, 1276, 4182, 1277, 4183, 1278, 3229, 4187, 4189, 1280, 4192, 1281,
    1282, 4195, 1283, 4188, 3227, 1571, 4201, 1286, 4204, 1287, 4206, 1288, 3225, 2773, 4209,
    1290, 4213, 1291, 4216, 1292, 3506, 3574, 2197, 3508, 4221, 4223, 1296, 4228, 1297, 3223,
    4232, 1300, 1301, 4235, 1302, 4238, 1303, 3221, 4222, 4239, 1305, 4241, 1306, 4242, 1307,
    4247, 1308, 4251, 3219, 2405, 1310, 4255, 1311, 1312, 2406, 1313, 3217, 4260, 4262, 1315,
    4266, 1316, 4271, 1317, 4261, 3215, 4276, 1319, 4278, 1320, 3213, 4252, 2410, 4282, 1323,
    4286, 1324, 2411, 1325, 2989, 1326, 3211, 4291, 4293, 1328, 4298, 1329, 4302, 1330, 4305,
    1331, 4292, 4307, 1333, 4312, 1334, 3209, 2774, 4317, 1336, 4320, 1337, 4325, 1338, 2544,
    3235, 3305, 3311, 2349, 1537, 3478, 1343, 4332, 1344, 4335, 1345, 4338, 1346, 1547, 4342,
    4344, 1349, 4349, 1351, 4343, 3476, 4354, 1353, 4355, 1354, 4358, 1355, 4362, 1356, 1449,
    1538, 1358, 3307, 3233, 3238, 3309, 4371, 3474, 4373, 1362, 4376, 1363, 4377, 1364, 1365,
    3472, 4382, 4383, 1367, 4387, 1368, 1369, 2278, 3470, 4389, 1371, 4393, 1372, 3468, 4372,
    4396, 1374, 4399, 1375, 1376, 4404, 3466, 4406, 1378, 4409, 1379, 4414, 1380, 4415, 1381,
    1382, 3068, 1383, 2281, 3464, 4420, 1385, 4424, 1386, 2465, 4430, 1388, 1423, 4405, 4432,
    1391, 4437, 1393, 3819, 3462, 4442, 1395, 4446, 1396, 3460, 4449, 4451, 1398, 2872, 1399,
    2875, 1400, 4450, 3458, 4456, 1403, 2883, 2886, 1405, 4462, 1406, 3833, 1407, 3867, 1408,
    3175, 1409, 3168, 1410, 3158, 1411, 3153, 1412, 3138, 1414, 3127, 1416, 3117, 1417, 3112,
    1418, 3106, 1419, 3099, 1420, 3084, 1422, 3069, 1424, 4494, 1426, 4499, 1427, 4500, 1428,
    1429, 2958, 4502, 1432, 4503, 1433, 4506, 1434, 4511, 1436, 1497, 4513, 1438, 4518, 1439,
    4519, 1441, 4522, 1442, 1443, 4527, 1444, 2945, 1445, 2978, 1446, 2981, 1447, 2946, 1448,
    1526, 1450, 1539, 1452, 1522, 1454, 4552, 4553, 1457, 4557, 1997, 2002, 3674, 1459, 2300,
    2018, 2023, 3764, 1461, 4564, 4566, 4568, 1468, 1463, 1465, 4575, 2828, 4577, 4579, 1467,
    4583, 4584, 4586, 4588, 1524, 1469, 1471, 4596, 4597, 1473, 4599, 4600, 3385, 1475, 4253,
    4604, 4606, 1477, 3800, 4610, 4612, 4614, 4616, 3562, 4617, 2419, 1621, 4619, 1563, 1481,
    1558, 1482, 1581, 1483, 1573, 1484, 2979, 1485, 2944, 1486, 2947, 1487, 2980, 1488, 1513,
    1489, 1554, 1490, 1492, 2775, 3327, 4644, 4645, 1494, 1496, 4356, 4650, 4181, 4653, 1553,
    1498, 1506, 1499, 1501, 3825, 4662, 4664, 3826, 1503, 4666, 4667, 1505, 3830, 1593, 3602,
    1556, 1507, 1509, 4121, 4673, 4186, 3343, 1511, 3655, 4675, 1555, 1512, 1515, 4350, 4680,
    4682, 1518, 4685, 1941, 4687, 4688, 1520, 4234, 4301, 1548, 1525, 1528, 4697, 2407, 4699,
    1530, 4703, 4705, 4631, 4707, 1532, 2291, 1651, 1534, 4714, 4458, 4716, 3380, 3641, 1823,
    2929, 4720, 1858, 1541, 2642, 3338, 4508, 2644, 1543, 4726, 4728, 4730, 4254, 4733, 1546,
    1746, 4737, 4738, 2651, 1550, 4742, 4744, 4454, 4747, 1552, 4750, 4752, 3785, 4755, 1582,
    1557, 1560, 2896, 3942, 3991, 4758, 1562, 4671, 4760, 1572, 1564, 1566, 3585, 4769, 4771,
    4529, 1568, 4773, 4774, 1570, 4775, 4776, 3772, 1575, 4781, 4782, 4784, 4785, 1578, 3619,
    4788, 4790, 1644, 1580, 1584, 4268, 4793, 1586, 4796, 3702, 4066, 1588, 4284, 3936, 4082,
    4800, 2787, 2711, 2717, 2789, 4658, 2149, 4670, 4802, 1594, 2147, 4694, 3734, 1596, 1597,
    1598, 4807, 1599, 4642, 2145, 2306, 3336, 1602, 3339, 1603, 4812, 1604, 2143, 4370, 4815,
    1606, 4486, 1607, 4820, 1608, 2713, 2785, 2791, 2715, 4571, 2141, 3951, 1612, 3943, 1614,
    2140, 2513, 4832, 1617, 1618, 4834, 1619, 4837, 1620, 2530, 1755, 2137, 4762, 4841, 1624,
    1625, 4844, 1626, 4849, 1627, 4572, 2135, 4322, 1629, 4852, 1630, 1631, 4323, 1632, 2133,
    4756, 4467, 1634, 4859, 1635, 4864, 1636, 3644, 2131, 1638, 4867, 1639, 2129, 4765, 2707,
    4870, 1642, 3716, 1643, 4327, 1645, 1646, 2127, 4693, 4876, 1648, 4881, 1649, 4884, 1650,
    4712, 4639, 1883, 4149, 1653, 4138, 1655, 2125, 1832, 4894, 1658, 4897, 1659, 4900, 1660,
    3070, 2153, 2242, 2248, 2155, 2615, 2681, 1665, 4903, 1666, 4904, 1667, 4907, 1668, 2625,
    3938, 4582, 1671, 4574, 1673, 4018, 2679, 1675, 4917, 1676, 4919, 1677, 4922, 1678, 1920,
    2616, 2244, 2151, 2157, 2246, 4110, 2677, 1684, 4521, 1685, 4929, 1686, 1687, 2675, 3814,
    4932, 1689, 3831, 4101, 2673, 4935, 1692, 3786, 1693, 2671, 3843, 3525, 1695, 2486, 4944,
    1697, 3526, 1698, 4107, 2669, 4947, 1700, 4950, 1701, 4136, 4955, 1703, 1704, 1705, 1985,
    2667, 4958, 1707, 4961, 1708, 2992, 4965, 1710, 2024, 3842, 4749, 1713, 4741, 1715, 4039,
    2665, 4973, 1717, 3761, 1718, 2663, 3941, 4980, 1720, 4421, 1721, 4423, 1722, 1723, 4019,
    2661, 4985, 1725, 2115, 4099, 4505, 1728, 2659, 3413, 4989, 1730, 1731, 2116, 3929, 1733,
    2582, 3798, 1735, 3930, 1736, 2108, 4628, 1738, 4538, 1739, 1740, 4629, 1741, 2100, 4638,
    1743, 4530, 1744, 1745, 2092, 3795, 3794, 1750, 3932, 1751, 2529, 1752, 2514, 1754, 2503,
    1756, 2498, 1757, 2489, 1758, 2481, 1759, 2470, 1760, 2462, 1762, 2445, 1764, 2437, 1765,
    2427, 1766, 2420, 1767, 2571, 1768, 2538, 1769, 2541, 2572, 1771, 1857, 1772, 1849, 1773,
    1873, 1774, 1866, 1775, 1801, 1776, 1845, 1777, 1779, 5040, 2822, 1781, 4048, 4052, 5042,
    1844, 1782, 1791, 1783, 1785, 5045, 5046, 3341, 4290, 5047, 1790, 5050, 2288, 4328, 2814,
    1847, 1792, 5054, 2258, 4866, 2724, 2851, 1799, 4353, 4595, 5059, 1846, 1800, 1803, 3740,
    4334, 3849, 4043, 1805, 5063, 4060, 4058, 1807, 4167, 4069, 4073, 2817, 1889, 1808, 1905,
    1810, 2539, 1812, 2570, 1813, 2573, 1814, 2540, 1815, 1835, 1816, 1819, 3299, 4569, 4661,
    4555, 1821, 5078, 5080, 5081, 5082, 1882, 1822, 1825, 2957, 4283, 4858, 4556, 4766, 1828,
    3808, 4609, 1830, 2965, 3553, 5092, 2967, 4289, 5094, 4840, 4427, 1884, 1834, 1837, 5098,
    5099, 1839, 5102, 4886, 1841, 4492, 4615, 3924, 4598, 1843, 5109, 2915, 5111, 1874, 1848,
    1851, 4497, 1853, 4474, 4806, 5116, 5117, 1856, 4263, 5118, 5120, 1865, 1860, 5123, 5124,
    5062, 1862, 5127, 3442, 3773, 5129, 1864, 5133, 5134, 3766, 4471, 1868, 2937, 1870, 5136,
    2900, 4740, 1872, 5139, 2922, 5141, 3802, 1877, 3891, 5144, 3859, 5145, 1879, 4056, 3809,
    1881, 3841, 4814, 4020, 3411, 3152, 5149, 4875, 4975, 1899, 1890, 1892, 3937, 4473, 4713,
    5028, 1894, 4496, 5156, 3647, 1896, 4240, 2354, 1898, 5160, 3547, 1902, 3738, 3748, 5165,
    2318, 1904, 4468, 4477, 5170, 5171, 1908, 4754, 5175, 1910, 4906, 4992, 1912, 4274, 5179,
    5180, 2916, 2170, 1914, 2646, 1915, 2637, 1916, 2632, 1917, 2617, 1919, 2604, 1921, 2596,
    1922, 2591, 1923, 2583, 1924, 2575, 1925, 2558, 1927, 2543, 1929, 3933, 1931, 3793, 1932,
    3796, 1933, 1934, 2433, 4528, 1937, 4531, 1938, 4637, 1939, 4630, 4539, 1943, 4627, 1944,
    3931, 1946, 3797, 1947, 1949, 2416, 1950, 2453, 1951, 2456, 1952, 2417, 1953, 2029, 1955,
    2042, 1957, 2025, 1959, 4024, 3964, 1962, 4457, 3100, 4978, 1964, 3359, 3120, 3125, 5014,
    1966, 3775, 4001, 4041, 1973, 1968, 1970, 3975, 3608, 3965, 3820, 1972, 5229, 5230, 5232,
    5233, 2027, 1974, 1976, 5238, 1978, 5239, 5240, 4865, 1980, 2305, 5242, 5244, 1982, 4007,
    3779, 3992, 4533, 4281, 4927, 4461, 5249, 2066, 1986, 2061, 1987, 2084, 1988, 2076, 1989,
    2454, 1990, 2415, 1991, 2418, 1992, 2455, 2016, 1994, 2057, 1995, 3564, 5259, 4040, 1999,
    2001, 2758, 5263, 2176, 4431, 2056, 2003, 2009, 2004, 2006, 5269, 4011, 2008, 5041, 2179,
    2059, 2010, 2012, 4794, 4735, 2184, 4731, 2014, 4062, 5272, 2058, 2015, 2748, 5275, 2021,
    4230, 5279, 3996, 2269, 2382, 2051, 2028, 2031, 3722, 3449, 5283, 2033, 3753, 4119, 5253,
    4127, 2035, 3350, 2037, 4191, 2924, 4357, 4860, 4957, 3696, 5291, 3018, 2044, 4839, 5202,
    2046, 5295, 4156, 4139, 2307, 5298, 2049, 4275, 5300, 2053, 4515, 4257, 2918, 5305, 2055,
    3757, 3767, 5024, 5310, 2085, 2063, 3666, 5077, 5097, 4489, 2065, 5270, 5313, 2075, 2067,
    2069, 4928, 3752, 5319, 2071, 3725, 2073, 5320, 5321, 5019, 2078, 5325, 3720, 5326, 4651,
    2081, 4945, 4640, 4764, 2083, 2087, 2327, 5329, 2089, 2336, 2091, 2352, 5073, 4635, 5333,
    2094, 2097, 3279, 5334, 4710, 3360, 2099, 3271, 3036, 5337, 2102, 5194, 5339, 2104, 5340,
    3778, 4231, 4905, 2107, 4999, 2110, 4549, 5344, 2275, 3542, 2112, 2956, 5096, 5087, 2114,
    5346, 3388, 2324, 2119, 5347, 3543, 2121, 4381, 5293, 2123, 5349, 4403, 4361, 5318, 3751,
    4413, 5351, 5353, 2838, 4217, 5355, 5146, 2743, 3157, 5356, 5357, 5266, 5359, 4819, 5361,
    2589, 5362, 4479, 5365, 5366, 4347, 2370, 2901, 5367, 5369, 4402, 4365, 5371, 4210, 5373,
    4348, 3263, 3445, 3116, 5377, 2873, 5379, 3631, 4294, 5381, 3482, 3205, 2215, 3484, 3501,
    3185, 2815, 4245, 3560, 3706, 4198, 5383, 2228, 5385, 5386, 4910, 5388, 3627, 5389, 5178,
    5391, 3111, 5200, 5393, 4959, 2631, 2171, 5395, 4890, 5397, 2173, 2812, 2174, 2175, 5265,
    5396, 2820, 2178, 2180, 5402, 2655, 4267, 2182, 4270, 2183, 3536, 4318, 4190, 5408, 3126,
    3098, 3584, 5018, 5410, 2190, 3289, 2191, 3401, 2194, 5413, 2195, 5414, 2196, 5417, 5409,
    3403, 2199, 5421, 2200, 5423, 2201, 5424, 2202, 3538, 2657, 5403, 2602, 5315, 2206, 4359,
    5426, 2208, 5429, 2209, 2210, 5251, 5432, 2212, 4324, 2213, 5394, 4428, 5433, 2216, 5198,
    2217, 5435, 2218, 5412, 5418, 3287, 4971, 4893, 4265, 2222, 4447, 2223, 2224, 2225, 4426,
    5440, 2227, 4273, 2229, 5407, 4969, 2231, 4279, 2232, 2233, 3944, 3278, 3296, 4561, 4996,
    2282, 3651, 4510, 3633, 5447, 5449, 4923, 5451, 5453, 2295, 3502, 3182, 3187, 3499, 3207,
    3480, 4880, 4179, 2345, 2856, 3083, 5455, 3586, 3167, 3529, 2987, 2252, 4341, 2253, 5460,
    2254, 4977, 2255, 2985, 4339, 5461, 2257, 5056, 5465, 2259, 5467, 2260, 3620, 3559, 5470,
    5472, 5173, 4269, 5060, 2265, 2266, 4725, 2268, 4541, 4734, 5044, 3535, 2271, 5476, 2272,
    4723, 3518, 5039, 2276, 5043, 2279, 3851, 5162, 2283, 4732, 3537, 4543, 5049, 3599, 4364,
    5480, 2287, 5052, 4524, 3530, 3085, 4711, 2292, 5482, 5473, 4848, 2294, 4366, 3557, 2296,
    4845, 2297, 5471, 2902, 5488, 2299, 4526, 5490, 2301, 4193, 3078, 3159, 5148, 3337, 5297,
    5390, 5065, 4993, 2309, 2310, 5494, 2312, 3517, 5497, 2314, 5498, 2316, 5499, 2317, 5167,
    5456, 3176, 5457, 4826, 3290, 2322, 5503, 2323, 3407, 3255, 2326, 4912, 2328, 3256, 2329,
    3333, 3531, 3406, 2331, 3294, 2332, 3293, 2333, 3611, 2334, 4827, 3179, 2938, 2339, 5387,
    3297, 2341, 4441, 2342, 3298, 2343, 4439, 5508, 2941, 5513, 2346, 5514, 2347, 2942, 2348,
    5384, 5067, 5515, 2351, 5332, 4196, 2353, 5159, 5174, 4272, 2356, 5521, 2357, 5522, 2359,
    2360, 2361, 4103, 3107, 3409, 2366, 5228, 2369, 2371, 3147, 5392, 5248, 3118, 4425, 5450,
    4412, 2375, 4879, 2376, 4878, 2377, 2378, 5448, 4464, 5528, 2380, 5530, 2381, 2826, 4410,
    5532, 2384, 5533, 2385, 4453, 5526, 5534, 2387, 2388, 2389, 3054, 4939, 5538, 2391, 5540,
    2392, 5542, 2393, 5543, 2394, 2829, 3052, 5544, 2396, 4937, 2397, 3699, 3650, 2399, 4554,
    5446, 4440, 2401, 5547, 2402, 4593, 5548, 2404, 4429, 4438, 5016, 2409, 4995, 2412, 4563,
    2413, 4591, 2414, 2446, 2422, 3402, 4536, 5256, 5550, 2424, 2426, 3640, 5552, 4576, 2436,
    2428, 2430, 3907, 3900, 2432, 3414, 5554, 2435, 4089, 4842, 3452, 3398, 3331, 2440, 5558,
    4830, 2442, 4948, 2444, 5484, 5562, 2448, 3329, 3522, 2862, 2450, 5564, 3277, 2452, 5307,
    5568, 2770, 4933, 2471, 2457, 2459, 4220, 5132, 5138, 5312, 2461, 5443, 5571, 5572, 2464,
    5573, 5575, 2467, 3760, 5576, 2469, 2473, 5578, 2475, 2477, 4548, 5030, 4534, 5106, 2479,
    5581, 4655, 5583, 2504, 2480, 3731, 3987, 2485, 4545, 5585, 3376, 5398, 2497, 2490, 2492,
    3901, 5587, 3897, 2494, 3835, 4315, 3988, 3837, 2496, 4093, 3906, 3805, 4622, 2500, 5589,
    2502, 3911, 4974, 3912, 2507, 3736, 5593, 5594, 2509, 3551, 3762, 4695, 5598, 2524, 2515,
    2517, 4537, 4544, 5152, 4706, 2519, 3730, 5604, 4422, 2521, 3347, 4872, 2523, 5609, 2526,
    3681, 4507, 5612, 4856, 2528, 4620, 4540, 4792, 4729, 2532, 3894, 4709, 2534, 2735, 3011,
    3016, 3882, 2536, 3387, 2930, 5336, 4722, 3369, 5617, 2546, 3690, 2905, 2548, 4249, 5036,
    2550, 3416, 5620, 3946, 2557, 2552, 2554, 5131, 4392, 5128, 5331, 2556, 5623, 5520, 5625,
    5626, 2560, 2562, 5627, 5628, 2564, 3815, 5629, 5631, 2566, 5257, 3961, 5247, 3927, 3394,
    2771, 3695, 2948, 2597, 2574, 2577, 5633, 3643, 2579, 2581, 4918, 4786, 3707, 3656, 2590,
    2586, 3935, 3689, 5031, 2588, 5640, 2593, 5602, 5169, 4804, 2595, 2884, 5642, 2599, 4914,
    5644, 2601, 3322, 5647, 5341, 4883, 2626, 2603, 2606, 4523, 5650, 2608, 3921, 3934, 4114,
    5286, 2610, 2612, 3264, 4986, 3550, 2866, 2619, 3163, 4691, 3165, 2621, 4133, 3895, 4148,
    3687, 4164, 2624, 5662, 2628, 3711, 3368, 4983, 5664, 2630, 3915, 3806, 4160, 4071, 2634,
    4565, 4668, 4590, 2636, 3899, 5666, 2645, 2638, 2640, 2799, 3920, 5495, 5669, 2648, 4484,
    5673, 5674, 2842, 4109, 2653, 4861, 4126, 5590, 5505, 3020, 5677, 5425, 3592, 4940, 5679,
    4296, 4516, 5506, 5682, 4391, 5005, 5683, 5684, 4226, 4211, 5686, 5222, 5688, 2975, 5634,
    3758, 4227, 5690, 5537, 4246, 4207, 2683, 4493, 5541, 4838, 4352, 2685, 2687, 5199, 2691,
    2693, 5659, 3174, 2695, 5694, 3622, 3555, 4132, 2697, 5696, 2700, 4205, 5697, 5114, 4250,
    2702, 2704, 5234, 3102, 2706, 5698, 3960, 3323, 2732, 2709, 3488, 3201, 3200, 3490, 5452,
    4846, 2766, 5454, 4384, 4953, 3192, 3495, 3607, 3621, 5201, 3978, 3422, 3712, 5700, 5702,
    3356, 3282, 5704, 5706, 3914, 4157, 2725, 4445, 5294, 4998, 2727, 2730, 3330, 4163, 4997,
    4173, 4443, 2737, 5512, 2738, 3316, 2739, 5709, 3000, 3031, 3266, 3082, 4236, 2744, 4862,
    2745, 5710, 2746, 4184, 3080, 5274, 5711, 2749, 5713, 2750, 5714, 2751, 3318, 4175, 5260,
    3916, 3334, 3729, 4137, 3003, 4243, 5262, 5715, 2759, 2760, 5707, 5716, 2763, 5523, 2764,
    5705, 5545, 4925, 2767, 4924, 2768, 3354, 2769, 5301, 5258, 2772, 4643, 5405, 5717, 2831,
    5478, 3427, 5026, 5720, 3497, 3190, 3195, 2841, 3420, 5380, 5382, 4411, 3399, 3355, 3492,
    3198, 3041, 5632, 3265, 2954, 2797, 5668, 5722, 2800, 5338, 5525, 2803, 3692, 2804, 2805,
    5725, 2806, 5001, 4898, 5726, 2971, 5728, 4970, 5511, 5729, 2813, 5053, 5730, 3315, 4444,
    2818, 5459, 2821, 3288, 5723, 4891, 2827, 5732, 2832, 3317, 5731, 2836, 5734, 2837, 5113,
    4330, 5727, 5735, 2840, 5468, 5000, 2843, 2845, 2846, 5492, 3049, 2961, 5093, 5703, 5416,
    2850, 5738, 2852, 5701, 4319, 4954, 2854, 4297, 2855, 4951, 2857, 5458, 4256, 2859, 2860,
    4295, 5563, 2863, 5739, 2864, 2865, 2868, 5076, 2869, 5619, 3989, 5671, 3970, 5406, 2877,
    4316, 2878, 3609, 2879, 2880, 3972, 2881, 4314, 4329, 5185, 5184, 2885, 4823, 3151, 5741,
    2888, 5742, 2889, 2890, 5743, 2891, 3149, 4821, 2893, 5745, 2894, 2895, 3393, 3025, 5436,
    4828, 2903, 5746, 2906, 2982, 4375, 5290, 3008, 5213, 5721, 2910, 5204, 2911, 5748, 2912,
    3524, 5182, 5304, 5751, 2919, 2920, 5214, 5719, 5140, 5752, 2923, 5288, 4379, 2925, 2927,
    5754, 2928, 4719, 5718, 2933, 3606, 2934, 4913, 3027, 5546, 4313, 2940, 5755, 2943, 2952,
    5130, 5622, 5567, 5756, 2960, 5595, 3348, 5760, 3321, 2969, 5237, 5737, 2973, 4416, 4258,
    5764, 4326, 2977, 4751, 5137, 4367, 3598, 4824, 4054, 4075, 4759, 5766, 5768, 5769, 2991,
    5221, 2994, 5033, 5246, 2996, 4920, 4625, 3918, 3002, 5772, 4306, 3005, 4009, 3801, 5070,
    4004, 3007, 5524, 3683, 3013, 5187, 4194, 5778, 5780, 5781, 3781, 3022, 4581, 4892, 4578,
    5553, 3024, 5596, 5566, 3029, 5527, 3669, 3034, 5051, 5785, 5034, 4208, 3774, 3043, 5074,
    4118, 4116, 4634, 3045, 5789, 4960, 3047, 3404, 5791, 5006, 5793, 3373, 3828, 4674, 5675,
    3902, 3058, 5309, 5654, 3060, 4337, 4514, 3062, 5657, 5086, 3072, 3074, 4851, 3812, 3076,
    5104, 5122, 4053, 4938, 4050, 4797, 5800, 5801, 5803, 3087, 5804, 3089, 3364, 5489, 3091,
    4636, 4613, 4611, 5211, 4368, 5808, 3104, 3549, 5420, 3109, 5569, 5108, 3114, 5330, 4153,
    3257, 3919, 3739, 5812, 3540, 5815, 3123, 5437, 5100, 3129, 4899, 5819, 3131, 4708, 5153,
    3791, 4704, 3134, 3691, 4419, 3140, 3878, 3749, 3142, 5608, 5172, 5616, 3145, 5205, 3685,
    5826, 3909, 4669, 3839, 5591, 3155, 4972, 3952, 5641, 3950, 4482, 5828, 3161, 4374, 5008,
    5831, 5832, 3170, 5836, 5264, 4401, 3178, 3381, 5606, 3810, 4026, 4512, 4171, 4158, 4592,
    4558, 5839, 4689, 4336, 5218, 4916, 3771, 5822, 5841, 5607, 5007, 5486, 5843, 5474, 3717,
    5845, 4165, 5847, 4169, 5191, 3857, 3884, 5849, 5851, 5853, 4805, 4895, 5422, 3646, 5857,
    4952, 5859, 4926, 4180, 5861, 4345, 5863, 5864, 4656, 5865, 5867, 3981, 3601, 3252, 4911,
    3983, 3990, 5376, 4816, 4027, 5873, 3973, 4871, 3269, 3270, 3272, 5875, 3275, 3276, 5868,
    3281, 4098, 3967, 5874, 3968, 5879, 3292, 4030, 5224, 4091, 5882, 5884, 4363, 5886, 5888,
    3396, 3632, 5890, 4721, 4106, 5892, 3320, 5762, 5430, 5699, 4946, 5895, 5896, 5796, 3328,
    5299, 3735, 5292, 4902, 3788, 3340, 4641, 5215, 5758, 4934, 5464, 5759, 5208, 4908, 5287,
    3351, 5899, 5897, 3353, 5535, 3671, 5466, 3358, 5335, 5518, 3756, 3366, 3367, 5663, 4683,
    5902, 3372, 5795, 5891, 4225, 4817, 5906, 3377, 4873, 4718, 3382, 4803, 3383, 4835, 4909,
    4602, 3877, 5516, 4822, 3392, 5685, 3705, 3397, 5557, 5862, 3759, 5549, 5790, 5797, 3410,
    3412, 4017, 5866, 5885, 3421, 3423, 5883, 3425, 5912, 3426, 3429, 3430, 4000, 3433, 3986,
    3435, 3436, 5915, 3437, 3438, 3440, 3441, 4990, 4963, 3443, 3979, 4084, 5917, 3446, 5235,
    3448, 3803, 5226, 3453, 3454, 5907, 4739, 4394, 5919, 5206, 5908, 5487, 4504, 5577, 5922,
    5712, 4647, 5011, 5924, 5913, 3888, 5914, 3872, 4724, 4624, 3742, 4770, 5927, 5655, 4487,
    5083, 4831, 5887, 4244, 5889, 4200, 3746, 5090, 5929, 5931, 4813, 5933, 5935, 5823, 3520,
    4833, 5177, 4520, 5181, 5937, 4105, 5814, 5938, 3541, 5345, 5348, 5809, 5066, 4836, 5002,
    5161, 5811, 5656, 5536, 5529, 3554, 5695, 5934, 5916, 3558, 3563, 3844, 5898, 3817, 5940,
    4877, 5858, 5860, 4386, 4847, 4618, 4768, 4562, 5910, 3589, 4987, 3590, 3591, 4321, 5942,
    5944, 4825, 4559, 5941, 5945, 3612, 3615, 5946, 3616, 5943, 3618, 4787, 5901, 5932, 3626,
    5948, 3628, 5930, 3630, 3635, 3638, 3639, 3642, 4763, 5095, 4779, 4560, 5871, 3649, 3652,
    5088, 3653, 3745, 4219, 3658, 3659, 3660, 5950, 3661, 3663, 3664, 3665, 4869, 5878, 3672,
    5951, 3675, 3871, 5744, 3679, 3680, 5610, 5825, 5953, 3686, 4478, 5939, 5638, 5821, 3694,
    5374, 4936, 3700, 5375, 3704, 5637, 5415, 3713, 3715, 5784, 3719, 4333, 5282, 3723, 3724,
    3727, 5603, 3732, 5163, 5926, 3743, 5164, 3750, 5788, 3754, 5787, 3755, 5689, 5597, 5777,
    3763, 5783, 3765, 5308, 5639, 3769, 3770, 5771, 4778, 5775, 3776, 5774, 3777, 5757, 3780,
    5328, 3782, 3783, 3784, 5763, 3787, 4632, 3789, 4633, 3792, 4083, 3804, 4074, 4067, 3807,
    4046, 4023, 3811, 4108, 3813, 3883, 3816, 3866, 3821, 3823, 5971, 4417, 5936, 5876, 3868,
    3832, 5925, 4798, 4727, 3840, 4102, 3845, 3847, 5909, 3850, 3853, 3855, 4433, 4698, 3892,
    3856, 5753, 4459, 3861, 5561, 3863, 3865, 5551, 3874, 5978, 4304, 3876, 4400, 5736, 3880,
    3886, 5877, 3890, 4570, 5327, 5507, 5462, 3904, 4485, 4490, 5983, 5984, 4964, 3917, 4120,
    3922, 4112, 3923, 4532, 3925, 4535, 3926, 4038, 3939, 3940, 4702, 4660, 3948, 3954, 5988,
    4395, 4303, 3957, 5110, 3959, 4460, 4517, 4010, 3962, 4002, 3963, 5615, 5918, 3977, 5881,
    4780, 4882, 3994, 4311, 3997, 4237, 4495, 4476, 5601, 5648, 4013, 5911, 4016, 5651, 4659,
    4981, 4029, 4746, 5750, 4032, 4034, 4036, 5401, 5904, 5893, 4045, 4435, 5830, 5820, 5995,
    4063, 5427, 5708, 4677, 4567, 4078, 4080, 4086, 4480, 5419, 5035, 5998, 5960, 4095, 4097,
    4607, 5894, 4672, 4111, 4218, 4123, 5243, 4125, 4949, 4129, 4131, 4135, 5084, 5220, 5805,
    4141, 5605, 4143, 5155, 4145, 4147, 4151, 4594, 4795, 4162, 4166, 4178, 4652, 5678, 4863,
    4185, 5747, 5854, 4197, 4199, 6004, 4202, 4203, 5856, 5786, 4212, 5967, 4214, 4215, 5855,
    4868, 4224, 4229, 5278, 5342, 5660, 4233, 4690, 5992, 5658, 5158, 5852, 5850, 5958, 4248,
    5469, 5846, 5303, 4259, 5973, 4264, 4465, 4277, 4280, 5848, 4799, 4808, 4285, 4287, 4288,
    4573, 4962, 5844, 5842, 4991, 4299, 5539, 4300, 4390, 4982, 6009, 5773, 4308, 4309, 5962,
    4310, 5618, 5195, 5770, 5614, 4331, 4736, 5986, 4340, 4346, 4679, 4351, 5692, 5058, 4649,
    5289, 5980, 4360, 5350, 4369, 5493, 5798, 5923, 4378, 4380, 4385, 5363, 4976, 4388, 5966,
    4397, 6011, 4398, 5880, 5837, 5900, 4407, 5491, 4408, 5921, 4896, 5968, 4853, 4418, 5799,
    5017, 5834, 5574, 4901, 4470, 4434, 6012, 4436, 5972, 4448, 4452, 6013, 4455, 4542, 5920,
    4715, 4931, 4463, 4466, 5168, 4469, 5835, 4472, 4475, 5818, 5364, 5135, 4481, 5810, 4483,
    5817, 4488, 5807, 4491, 4498, 4501, 5611, 4509, 5838, 5302, 5649, 4525, 4701, 4546, 4696,
    4547, 4608, 4550, 4603, 4551, 6022, 4757, 4580, 4585, 5646, 4587, 4589, 4601, 4605, 4791,
    4621, 4623, 4767, 4626, 4646, 4648, 5517, 4654, 4684, 4657, 4692, 4663, 4678, 4665, 4676,
    5434, 4681, 4686, 5947, 5147, 4700, 4717, 5400, 4743, 4745, 4748, 5252, 4753, 4761, 4854,
    4772, 5501, 5952, 4777, 4783, 5724, 4789, 4801, 5115, 5372, 5089, 4809, 5969, 4810, 4811,
    5378, 6032, 4818, 5989, 4829, 5560, 5928, 5445, 5004, 5556, 4843, 5370, 5368, 4850, 5358,
    5964, 4855, 5481, 6033, 4857, 5360, 5012, 5428, 4874, 5354, 5352, 5991, 4885, 5103, 4887,
    6001, 4888, 4889, 5091, 5143, 5207, 5661, 5643, 6025, 4915, 5840, 5636, 5691, 4921, 5442,
    5317, 5225, 5687, 4930, 6034, 4941, 4942, 6017, 4943, 5441, 5485, 6000, 5681, 4956, 5323,
    5223, 4966, 4967, 6029, 4968, 6035, 4979, 5676, 5504, 6015, 4984, 5190, 5680, 5399, 4988,
    4994, 5343, 5003, 5792, 5009, 5600, 5010, 5584, 5013, 5592, 5015, 5580, 5020, 5579, 5021,
    5555, 5022, 5023, 5025, 5254, 5027, 5255, 5029, 5142, 5032, 5126, 5112, 5150, 5037, 5057,
    5038, 6031, 5997, 5296, 6008, 5061, 5048, 5055, 5994, 6010, 5227, 5064, 5193, 5196, 5154,
    5068, 5151, 5069, 5210, 5071, 5212, 5072, 5121, 5075, 5079, 5965, 5776, 5107, 5105, 5085,
    5324, 5101, 5189, 5268, 5119, 5870, 5961, 6005, 5125, 5475, 5652, 6014, 5271, 5806, 5157,
    5404, 5693, 5166, 5236, 5176, 5183, 5672, 5186, 5188, 5635, 5192, 5477, 5197, 5203, 5824,
    5209, 5285, 5216, 5281, 5217, 5245, 5219, 5241, 6027, 5311, 5231, 5250, 5316, 5261, 5277,
    5267, 5280, 5273, 5276, 5979, 5284, 5869, 5306, 5314, 5993, 5322, 6028, 5509, 6042, 5990,
    5582, 6023, 5624, 5749, 5613, 6003, 5779, 5977, 5463, 5565, 5653, 5761, 5985, 5586, 5667,
    5588, 5411, 6043, 6006, 5502, 5955, 5431, 5630, 5438, 5439, 5570, 5970, 5444, 5621, 5957,
    5982, 5767, 6021, 5479, 5483, 5496, 5500, 5981, 5510, 6039, 6016, 5519, 5531, 5794, 5963,
    6019, 5559, 6036, 5975, 5956, 6040, 5599, 5733, 5645, 5665, 5670, 5974, 5833, 5999, 5816,
    6024, 6002, 6030, 5987, 5996, 6018, 5959, 5802, 6007, 5740, 6020, 5827, 5954, 6041, 5765,
    5782, 5813, 5829, 6038, 5872, 5905, 5903, 6037, 5949, 6026, 5976, 6045, 6046, 6047, 6044]

/-- Cayley-table column for left multiplication by `b`: `nextB[i]` is the index of the
element `b · evalWord (word i)`. -/
def nextB : Array Nat :=
  #[2, 6, 4, 10, 0, 14, 7, 1, 21, 23, 11, 3, 30, 32, 15, 5, 39, 41, 44, 46, 48, 22, 8, 24, 9,
    59, 61, 64, 66, 68, 31, 12, 33, 13, 79, 81, 84, 86, 88, 40, 16, 42, 17, 98, 45, 18, 47, 19,
    49, 20, 113, 115, 118, 120, 123, 125, 128, 130, 132, 60, 25, 62, 26, 142, 65, 27, 67, 28,
    69, 29, 157, 159, 162, 164, 167, 169, 172, 174, 176, 80, 34, 82, 35, 186, 85, 36, 87, 37,
    89, 38, 201, 203, 206, 208, 211, 213, 216, 218, 99, 43, 225, 227, 230, 232, 235, 237, 240,
    242, 244, 246, 249, 251, 253, 114, 50, 116, 51, 263, 119, 52, 121, 53, 272, 124, 54, 126,
    55, 282, 129, 56, 131, 57, 133, 58, 295, 297, 300, 285, 304, 306, 309, 311, 143, 63, 316,
    318, 321, 323, 326, 328, 331, 333, 336, 338, 340, 342, 344, 158, 70, 160, 71, 353, 163, 72,
    165, 73, 363, 168, 74, 170, 75, 372, 173, 76, 175, 77, 177, 78, 385, 387, 390, 392, 395,
    397, 400, 402, 187, 83, 407, 409, 412, 414, 417, 419, 422, 424, 426, 428, 431, 433, 435,
    202, 90, 204, 91, 445, 207, 92, 209, 93, 454, 212, 94, 214, 95, 464, 217, 96, 219, 97, 474,
    476, 478, 480, 482, 226, 100, 228, 101, 491, 231, 102, 233, 103, 501, 236, 104, 238, 105,
    510, 241, 106, 243, 107, 245, 108, 247, 109, 528, 250, 110, 252, 111, 254, 112, 542, 544,
    547, 549, 552, 554, 359, 558, 264, 117, 565, 567, 570, 572, 574, 577, 579, 273, 122, 584,
    586, 589, 375, 593, 495, 597, 599, 283, 127, 604, 302, 607, 609, 612, 614, 617, 619, 622,
    624, 626, 296, 134, 298, 135, 636, 301, 136, 137, 644, 305, 138, 307, 139, 654, 310, 140,
    312, 141, 664, 666, 668, 317, 144, 319, 145, 677, 322, 146, 324, 147, 687, 327, 148, 329,
    149, 696, 332, 150, 334, 151, 248, 337, 152, 339, 153, 341, 154, 343, 155, 345, 156, 726,
    728, 731, 733, 736, 738, 740, 354, 161, 747, 749, 752, 753, 557, 756, 759, 761, 364, 166,
    766, 768, 770, 773, 775, 778, 780, 373, 171, 785, 591, 788, 790, 793, 795, 798, 800, 802,
    804, 806, 386, 178, 388, 179, 816, 391, 180, 393, 181, 825, 396, 182, 398, 183, 835, 401,
    184, 403, 185, 845, 847, 849, 408, 188, 410, 189, 858, 413, 190, 415, 191, 868, 418, 192,
    420, 193, 877, 423, 194, 425, 195, 427, 196, 429, 197, 895, 432, 198, 434, 199, 436, 200,
    381, 909, 912, 914, 917, 919, 497, 923, 446, 205, 930, 932, 935, 937, 939, 942, 944, 455,
    210, 949, 951, 954, 513, 958, 862, 962, 964, 465, 215, 968, 971, 973, 976, 978, 981, 983,
    430, 475, 220, 477, 221, 479, 222, 481, 223, 483, 224, 1006, 1008, 1011, 1013, 1016, 1018,
    1020, 492, 229, 1027, 1029, 595, 1032, 922, 1035, 1038, 1040, 502, 234, 1045, 1047, 1049,
    1052, 1054, 1057, 1059, 511, 239, 1064, 956, 1067, 1069, 1072, 1074, 1077, 1079, 1081, 1083,
    1086, 1088, 1091, 1093, 1096, 1098, 335, 1101, 1103, 1105, 1107, 1109, 1111, 1113, 1115,
    1117, 1119, 1121, 1123, 1125, 543, 255, 545, 256, 1134, 548, 257, 550, 258, 1143, 553, 259,
    555, 260, 1152, 261, 559, 262, 1160, 1162, 1164, 1166, 1168, 566, 265, 568, 266, 1176, 571,
    267, 573, 268, 575, 269, 1189, 578, 270, 580, 271, 1199, 1201, 1203, 585, 274, 587, 275,
    1213, 590, 276, 277, 1221, 594, 278, 279, 1229, 598, 280, 600, 281, 1238, 1240, 1242, 605,
    284, 1247, 608, 286, 610, 287, 1257, 613, 288, 615, 289, 1264, 618, 290, 620, 291, 1100,
    623, 292, 625, 293, 627, 294, 886, 1277, 1280, 1282, 1285, 1287, 683, 1291, 637, 299, 1296,
    1297, 1300, 1302, 1305, 1307, 645, 303, 1310, 1312, 1315, 699, 1319, 357, 1322, 1324, 655,
    308, 1326, 1328, 1330, 1333, 1334, 1336, 1338, 621, 665, 313, 667, 314, 669, 315, 1343,
    1345, 1348, 1350, 1353, 1355, 1357, 678, 320, 1362, 1364, 1367, 1368, 1290, 1371, 1374,
    1375, 688, 325, 1378, 1380, 1382, 1385, 1387, 1390, 1392, 697, 330, 1395, 1317, 1398, 1400,
    1403, 1405, 1407, 1409, 1411, 1413, 1415, 1417, 1419, 1421, 1423, 1426, 1428, 1431, 1433,
    1436, 1438, 1441, 1443, 1445, 1447, 1449, 1451, 1453, 727, 346, 729, 347, 1462, 732, 348,
    734, 349, 1468, 737, 350, 739, 351, 741, 352, 1481, 1483, 1485, 1487, 1489, 748, 355, 750,
    356, 1498, 651, 754, 358, 1506, 757, 360, 1512, 760, 361, 762, 362, 1521, 1523, 1525, 767,
    365, 769, 366, 771, 367, 1538, 774, 368, 776, 369, 1547, 779, 370, 781, 371, 1553, 1555,
    1557, 786, 374, 1563, 789, 376, 791, 377, 1572, 794, 378, 796, 379, 1581, 799, 380, 437,
    1589, 803, 382, 805, 383, 807, 384, 519, 1593, 1596, 1598, 1601, 1603, 864, 1607, 817, 389,
    1612, 1614, 1617, 1619, 1621, 1624, 1626, 826, 394, 1629, 1631, 1634, 880, 1638, 681, 1641,
    1643, 836, 399, 1645, 1648, 1650, 1653, 1655, 1658, 1660, 801, 846, 404, 848, 405, 850, 406,
    1665, 1667, 1670, 1672, 1675, 1677, 1679, 859, 411, 1684, 1686, 960, 1689, 1606, 1692, 1695,
    1697, 869, 416, 1700, 1702, 1704, 1707, 1709, 1712, 1714, 878, 421, 1717, 1636, 1720, 1722,
    1725, 1727, 1730, 1276, 1733, 1735, 1738, 1740, 1743, 1745, 1748, 1750, 473, 1752, 1754,
    1756, 1758, 1760, 1762, 1764, 1766, 1768, 1770, 1772, 1774, 1776, 910, 438, 1782, 913, 439,
    915, 440, 1791, 918, 441, 920, 442, 1800, 443, 924, 444, 1808, 1810, 1812, 1814, 1816, 931,
    447, 933, 448, 1822, 936, 449, 938, 450, 940, 451, 1834, 943, 452, 945, 453, 1844, 1846,
    1848, 950, 456, 952, 457, 1857, 955, 458, 459, 1865, 959, 460, 461, 1873, 963, 462, 965,
    463, 1882, 1884, 969, 466, 1889, 972, 467, 974, 468, 1899, 977, 469, 979, 470, 1905, 982,
    471, 984, 472, 1914, 1916, 1918, 1920, 1922, 1924, 1926, 1928, 1931, 1933, 1936, 1938, 1941,
    1943, 1946, 1948, 1950, 1952, 1954, 1956, 1958, 1007, 484, 1009, 485, 1967, 1012, 486, 1014,
    487, 1973, 1017, 488, 1019, 489, 1021, 490, 1986, 1988, 1990, 1992, 1994, 1028, 493, 1030,
    494, 2003, 1033, 496, 2009, 1036, 498, 2015, 1039, 499, 1041, 500, 2024, 2026, 2028, 1046,
    503, 1048, 504, 1050, 505, 2041, 1053, 506, 1055, 507, 2050, 1058, 508, 1060, 509, 2056,
    2058, 2060, 1065, 512, 2066, 1068, 514, 1070, 515, 2075, 1073, 516, 1075, 517, 2084, 1078,
    518, 808, 2092, 1082, 520, 1084, 521, 1425, 1087, 522, 1089, 523, 2108, 1092, 524, 1094,
    525, 1435, 1097, 526, 1099, 527, 663, 1102, 529, 1104, 530, 1106, 531, 1108, 532, 1110, 533,
    1112, 534, 1114, 535, 1116, 536, 1118, 537, 1120, 538, 1122, 539, 1124, 540, 1126, 541,
    2170, 2173, 2175, 2089, 2179, 1181, 2183, 1135, 546, 2190, 2191, 2193, 2195, 2197, 2199,
    2201, 1144, 551, 2205, 2208, 1192, 2019, 2130, 2215, 2217, 1153, 556, 2222, 2224, 2227,
    2229, 2231, 2233, 1161, 560, 1163, 561, 1165, 562, 1167, 563, 1169, 564, 2252, 2254, 638,
    2257, 2259, 656, 1177, 569, 2264, 2266, 2268, 2182, 2271, 2274, 2276, 2278, 2280, 2282, 659,
    1190, 576, 2287, 2210, 2290, 2292, 2294, 2296, 2299, 2301, 1200, 581, 1202, 582, 1204, 583,
    2149, 2306, 2309, 2311, 685, 2071, 1253, 2317, 1214, 588, 2322, 2323, 2326, 2328, 2331,
    2333, 1222, 592, 2336, 2338, 2341, 1267, 2345, 2347, 1230, 596, 2349, 2351, 2353, 2356,
    2357, 2359, 2361, 1239, 601, 1241, 602, 1243, 603, 2366, 2368, 2370, 1248, 606, 2375, 2377,
    2380, 2381, 2316, 2384, 2387, 2388, 1258, 611, 2391, 2393, 2396, 2398, 660, 1265, 616, 2401,
    2343, 2404, 2406, 2409, 2411, 2413, 2415, 2417, 2419, 628, 1278, 629, 2427, 1281, 630, 1283,
    631, 2436, 1286, 632, 1288, 633, 2445, 634, 1292, 635, 2453, 2455, 2457, 1172, 1298, 639,
    2462, 1301, 640, 1303, 641, 2470, 1306, 642, 1308, 643, 2480, 1311, 646, 1313, 647, 2489,
    1316, 648, 649, 2497, 1320, 650, 2503, 1323, 652, 1325, 653, 1175, 2514, 1329, 657, 1331,
    658, 2524, 1188, 1263, 2529, 1337, 661, 1339, 662, 2538, 2540, 2542, 1344, 670, 1346, 671,
    2551, 1349, 672, 1351, 673, 2557, 1354, 674, 1356, 675, 1358, 676, 2570, 2572, 2574, 1363,
    679, 1365, 680, 2583, 832, 1369, 682, 2590, 1372, 684, 2596, 1209, 1376, 686, 2603, 1379,
    689, 1381, 690, 1383, 691, 2616, 1386, 692, 1388, 693, 2625, 1391, 694, 1393, 695, 2631,
    1396, 698, 2637, 1399, 700, 1401, 701, 2645, 1404, 702, 1406, 703, 1408, 704, 1410, 705,
    1412, 706, 1414, 707, 1416, 708, 1418, 709, 1420, 710, 1422, 711, 1424, 712, 2100, 1427,
    713, 1429, 714, 1080, 1432, 715, 1434, 716, 2116, 1437, 717, 1439, 718, 1090, 1442, 719,
    1444, 720, 1446, 721, 1448, 722, 1450, 723, 1452, 724, 1454, 725, 2724, 2727, 2729, 2732,
    2734, 1502, 2738, 1463, 730, 2743, 2745, 2748, 2750, 1469, 735, 2755, 1194, 2758, 1515,
    2762, 2690, 2766, 2768, 2770, 2772, 2774, 1482, 742, 1484, 743, 1486, 744, 1488, 745, 1490,
    746, 2797, 2799, 1136, 1215, 2803, 2805, 1231, 1499, 751, 2812, 2814, 2737, 2817, 2820,
    2821, 1507, 755, 2826, 2828, 2831, 1234, 1513, 758, 2836, 2760, 2838, 2840, 2842, 2845,
    2846, 1522, 763, 1524, 764, 1526, 765, 2709, 2851, 2854, 2856, 1255, 2859, 1569, 2863, 2865,
    2867, 2869, 1539, 772, 2872, 2874, 2877, 1584, 2880, 2883, 2885, 1548, 777, 2888, 2890,
    2893, 2895, 1554, 782, 1556, 783, 1558, 784, 2900, 2902, 1137, 2905, 1564, 787, 2910, 2912,
    2915, 2916, 2862, 2918, 2920, 1573, 792, 2922, 2924, 1140, 2927, 2929, 1157, 1235, 1582,
    797, 2933, 2879, 2936, 2938, 2940, 2942, 844, 2944, 2946, 2948, 1594, 809, 2953, 1597, 810,
    1599, 811, 2961, 1602, 812, 1604, 813, 2970, 814, 1608, 815, 2978, 2980, 2982, 1613, 818,
    1615, 819, 2988, 1618, 820, 1620, 821, 1622, 822, 2999, 1625, 823, 1627, 824, 3008, 1630,
    827, 1632, 828, 3017, 1635, 829, 830, 3025, 1639, 831, 3030, 1642, 833, 1644, 834, 1646,
    837, 3040, 1649, 838, 1651, 839, 3049, 1654, 840, 1656, 841, 3055, 1659, 842, 1661, 843,
    3064, 3066, 3068, 1666, 851, 1668, 852, 3077, 1671, 853, 1673, 854, 3083, 1676, 855, 1678,
    856, 1680, 857, 3094, 3096, 3098, 1685, 860, 1687, 861, 3106, 1690, 863, 3111, 1693, 865,
    3117, 1696, 866, 1698, 867, 3126, 1701, 870, 1703, 871, 1705, 872, 3137, 1708, 873, 1710,
    874, 3146, 1713, 875, 1715, 876, 3152, 1718, 879, 3158, 1721, 881, 1723, 882, 3167, 1726,
    883, 1728, 884, 3175, 1731, 885, 3180, 1734, 887, 1736, 888, 1930, 1739, 889, 1741, 890,
    3196, 1744, 891, 1746, 892, 1940, 1749, 893, 1751, 894, 1753, 896, 1755, 897, 1757, 898,
    1759, 899, 1761, 900, 1763, 901, 1765, 902, 1767, 903, 1769, 904, 1771, 905, 1773, 906,
    1775, 907, 1777, 908, 3179, 3253, 1827, 3256, 1783, 911, 3263, 3264, 2576, 3266, 2245, 3269,
    3271, 1792, 916, 1519, 3275, 1837, 3121, 3214, 2691, 3282, 1801, 921, 3287, 3289, 3292,
    3294, 3296, 3298, 1809, 925, 1811, 926, 1813, 927, 1815, 928, 1817, 929, 3315, 3317, 3320,
    3322, 1823, 934, 3327, 3329, 3330, 3255, 3333, 3336, 3338, 2810, 3341, 3342, 1835, 941,
    3347, 3277, 2559, 3351, 3353, 3355, 3358, 3360, 1845, 946, 1847, 947, 1849, 948, 3231, 1571,
    3366, 2106, 3163, 1895, 3372, 1858, 953, 3376, 3377, 3380, 3382, 3385, 3387, 1866, 957,
    3390, 1504, 3392, 1908, 3396, 3398, 1874, 961, 2716, 3401, 3403, 3406, 3407, 3409, 2651,
    1883, 966, 1885, 967, 3412, 3413, 3415, 1890, 970, 3420, 3422, 3425, 3426, 3371, 3429, 3432,
    2610, 1900, 975, 3435, 3437, 3440, 3442, 1906, 980, 3445, 3394, 3448, 2315, 3451, 2358,
    3453, 1915, 985, 1917, 986, 1919, 987, 1921, 988, 1923, 989, 1925, 990, 1927, 991, 1929,
    992, 3188, 1932, 993, 1934, 994, 1732, 1937, 995, 1939, 996, 3202, 1942, 997, 1944, 998,
    1742, 1947, 999, 1949, 1000, 1951, 1001, 1953, 1002, 1955, 1003, 1957, 1004, 1959, 1005,
    3517, 3520, 2095, 3524, 3526, 2005, 3530, 1968, 1010, 3535, 3537, 3540, 3542, 1974, 1015,
    3547, 1839, 3549, 2018, 3553, 3487, 3557, 3559, 3561, 3563, 2364, 1987, 1022, 1989, 1023,
    1991, 1024, 1993, 1025, 1995, 1026, 3584, 3585, 1784, 1859, 3589, 3591, 1875, 2004, 1031,
    3529, 3598, 3601, 2424, 2010, 1034, 3606, 3608, 3611, 1878, 2016, 1037, 3615, 3551, 2212,
    3618, 3619, 3621, 3622, 2025, 1042, 2027, 1043, 2029, 1044, 3502, 3627, 3630, 3632, 1897,
    3635, 2072, 3638, 3640, 2512, 3643, 2042, 1051, 2914, 3647, 3649, 2087, 3652, 2688, 3656,
    2051, 1056, 3658, 3660, 3663, 3665, 2057, 1061, 2059, 1062, 2061, 1063, 3669, 3671, 1785,
    3674, 2067, 1066, 3679, 3681, 3683, 2314, 3637, 3685, 3687, 2076, 1071, 3689, 3691, 1788,
    3694, 3696, 1805, 1879, 2085, 1076, 3699, 3651, 2499, 2178, 3704, 3706, 1430, 1198, 2020,
    3522, 3710, 3712, 2132, 3716, 1085, 3719, 3720, 3722, 3724, 1911, 3368, 3727, 1440, 3729,
    3731, 3734, 2143, 2640, 1251, 3739, 1095, 2464, 3742, 3743, 3745, 3746, 3748, 3750, 3752,
    3754, 3756, 3758, 3760, 3762, 2213, 3763, 3715, 3765, 3767, 3769, 3770, 3772, 3774, 3776,
    3778, 1332, 3780, 3736, 3782, 3783, 3784, 3785, 3787, 2305, 3789, 3791, 3793, 3795, 3797,
    2582, 3799, 3801, 3803, 3804, 3806, 3807, 3808, 3809, 3810, 3811, 3813, 1984, 3815, 3816,
    2171, 1127, 3820, 2174, 1128, 2176, 1129, 3828, 1130, 2180, 1131, 3832, 1132, 2184, 1133,
    3839, 3840, 3841, 3843, 3845, 1493, 1561, 3850, 2194, 1138, 2196, 1139, 1576, 3856, 2200,
    1141, 2202, 1142, 3866, 3868, 2206, 1145, 3872, 2209, 1146, 1147, 2469, 1148, 1149, 3883,
    2216, 1150, 2218, 1151, 3891, 3892, 3894, 2223, 1154, 2225, 1155, 3902, 2228, 1156, 1579,
    3907, 2232, 1158, 2234, 1159, 3914, 3916, 3918, 3920, 3922, 1295, 3924, 3926, 3928, 3930,
    2079, 3932, 3934, 3936, 3938, 3940, 3942, 2253, 1170, 2255, 1171, 3951, 2258, 1173, 2260,
    1174, 3960, 3962, 3964, 2265, 1178, 2267, 1179, 2269, 1180, 3972, 2272, 1182, 3978, 2275,
    1183, 2277, 1184, 2279, 1185, 2281, 1186, 2283, 1187, 3987, 3989, 3991, 2288, 1191, 3996,
    2291, 1193, 1471, 4001, 2295, 1195, 2297, 1196, 4010, 2300, 1197, 2093, 4017, 4019, 1909,
    1205, 2307, 1206, 4023, 2310, 1207, 2312, 1208, 4030, 1210, 3449, 1211, 2318, 1212, 4038,
    2615, 4041, 1494, 2324, 1216, 4046, 2327, 1217, 2329, 1218, 4053, 2332, 1219, 2334, 1220,
    4063, 2337, 1223, 2339, 1224, 4067, 2342, 1225, 1226, 4074, 2346, 1227, 2348, 1228, 1497,
    4083, 2352, 1232, 2354, 1233, 4091, 1511, 1580, 3452, 2360, 1236, 2362, 1237, 4101, 3564,
    1299, 2367, 1244, 2369, 1245, 2371, 1246, 4107, 4109, 4111, 2376, 1249, 2378, 1250, 4120,
    2114, 2382, 1252, 4126, 2385, 1254, 4132, 1531, 2389, 1256, 4138, 2392, 1259, 2394, 1260,
    4148, 2397, 1261, 2399, 1262, 4157, 2402, 1266, 4163, 2405, 1268, 2407, 1269, 4166, 2410,
    1270, 2412, 1271, 2414, 1272, 2416, 1273, 2418, 1274, 2420, 1275, 4178, 4180, 1586, 3602,
    2466, 4185, 2428, 1279, 4190, 4191, 1996, 4193, 2791, 4196, 4198, 2437, 1284, 3124, 4202,
    2473, 1516, 3245, 2119, 4207, 2446, 1289, 4210, 4212, 4214, 4215, 4217, 4219, 2454, 1293,
    2456, 1294, 2240, 4224, 4226, 4229, 4230, 2365, 2192, 3740, 4233, 4184, 4236, 2207, 3878,
    2471, 1304, 4240, 4058, 1975, 4135, 4243, 4245, 4248, 4250, 2481, 1309, 3249, 3166, 4256,
    2708, 1568, 2520, 4259, 2490, 1314, 4263, 4264, 4267, 4269, 4272, 4274, 2498, 1318, 3702,
    3110, 4279, 2532, 2504, 1321, 2155, 4283, 4285, 4287, 4288, 4289, 2081, 3642, 2898, 2515,
    1327, 4294, 4296, 4299, 4300, 4258, 4303, 4306, 2035, 2141, 4308, 4310, 4313, 4315, 2530,
    1335, 4318, 4281, 4321, 4323, 4326, 4327, 4329, 2539, 1340, 2541, 1341, 2543, 1342, 3879,
    4333, 2698, 4336, 2844, 2587, 4340, 2552, 1347, 4345, 4347, 4350, 4352, 2558, 1352, 3350,
    2475, 4356, 2599, 4359, 3203, 4363, 4365, 4367, 4369, 1832, 2571, 1359, 2573, 1360, 2575,
    1361, 3265, 4374, 2429, 2491, 4378, 4380, 2505, 2584, 1366, 4384, 3864, 4339, 3913, 1779,
    2591, 1370, 4390, 4392, 4394, 2508, 2597, 1373, 4397, 4056, 4400, 4401, 4403, 2604, 1377,
    3195, 3881, 4410, 4412, 2522, 3433, 2643, 4417, 4048, 1886, 4040, 2617, 1384, 4421, 4422,
    4425, 2655, 4428, 2115, 4431, 2626, 1389, 4433, 4435, 4438, 4440, 2632, 1394, 4070, 4444,
    2430, 4447, 2638, 1397, 4452, 3738, 4014, 4174, 4416, 4454, 2646, 1402, 4077, 4458, 2433,
    4460, 3411, 2450, 2509, 4463, 4427, 1867, 4465, 1520, 3980, 4467, 2129, 4182, 3226, 2692,
    4471, 4473, 4475, 4477, 4478, 3242, 3389, 4482, 2704, 4165, 1567, 2146, 4486, 4487, 4489,
    4490, 4492, 4495, 4497, 2189, 2219, 2069, 3044, 3655, 1825, 2764, 3281, 4470, 4504, 4507,
    4509, 3007, 2600, 4334, 4514, 4516, 2158, 2355, 4520, 4484, 4523, 4525, 2535, 4257, 2850,
    4528, 4530, 4532, 4534, 4536, 4119, 2002, 4538, 4540, 4542, 4544, 4546, 4548, 4550, 2725,
    1455, 4555, 2728, 1456, 2730, 1457, 4560, 2733, 1458, 2735, 1459, 4562, 1460, 2739, 1461,
    4570, 4572, 4574, 2744, 1464, 2746, 1465, 4581, 2749, 1466, 2751, 1467, 4590, 4592, 4594,
    2756, 1470, 4598, 2759, 1472, 1473, 4052, 2763, 1474, 1475, 4608, 2767, 1476, 2769, 1477,
    2771, 1478, 2773, 1479, 2775, 1480, 3251, 3274, 2120, 4622, 3125, 4625, 2321, 2163, 4627,
    4629, 4631, 4633, 4005, 4635, 4637, 2649, 4639, 4641, 2226, 2186, 2545, 2798, 1491, 2800,
    1492, 2101, 4647, 2804, 1495, 2806, 1496, 3162, 4656, 4658, 3340, 4660, 2813, 1500, 2815,
    1501, 4278, 2818, 1503, 3218, 1868, 2822, 1505, 2102, 4671, 2230, 2827, 1508, 2829, 1509,
    2185, 2832, 1510, 4276, 3219, 2547, 2837, 1514, 2441, 4683, 2841, 1517, 2843, 1518, 4337,
    1793, 2658, 4692, 4694, 3910, 1527, 2852, 1528, 4701, 2855, 1529, 2857, 1530, 4709, 2860,
    1532, 4713, 1533, 2864, 1534, 2866, 1535, 2868, 1536, 2870, 1537, 4722, 2873, 1540, 2875,
    1541, 4724, 2878, 1542, 1543, 2881, 1544, 4735, 2884, 1545, 2886, 1546, 4740, 2889, 1549,
    2891, 1550, 4749, 2894, 1551, 2896, 1552, 4756, 4290, 2325, 2901, 1559, 2903, 1560, 2162,
    2906, 1562, 4762, 4764, 4766, 2911, 1565, 2913, 1566, 3646, 2675, 2486, 2044, 2919, 1570,
    1851, 4779, 2923, 1574, 2925, 1575, 2049, 2928, 1577, 2930, 1578, 2121, 3254, 2934, 1583,
    3273, 2937, 1585, 2423, 4797, 2941, 1587, 2943, 1588, 2945, 1590, 2947, 1591, 2949, 1592,
    2657, 2993, 4803, 2954, 1595, 4805, 4714, 4105, 3308, 4808, 4171, 2962, 1600, 2022, 4810,
    3002, 2313, 2164, 3488, 4813, 2971, 1605, 3968, 4816, 4818, 3877, 4821, 4823, 2979, 1609,
    2981, 1610, 2983, 1611, 4825, 4827, 4829, 4685, 2989, 1616, 4192, 3896, 4833, 4718, 4835,
    4201, 4839, 3596, 4840, 3000, 1623, 4128, 3905, 4843, 4845, 4847, 4850, 4512, 3009, 1628,
    2168, 2074, 4853, 3194, 2642, 3046, 4855, 3018, 1633, 4033, 4857, 4860, 4862, 4865, 4168,
    3026, 1637, 2007, 4868, 3058, 3031, 1640, 3509, 3966, 4871, 4602, 4873, 3982, 3818, 4875,
    3041, 1647, 4877, 4879, 4501, 4882, 4043, 3994, 4886, 3050, 1652, 4772, 4888, 4890, 4892,
    3056, 1657, 4895, 4616, 4898, 3370, 4060, 3408, 4901, 3065, 1662, 3067, 1663, 3069, 1664,
    4682, 4783, 3183, 4905, 3869, 3108, 4908, 3078, 1669, 4910, 4912, 4914, 4916, 3084, 1674,
    3003, 4918, 3120, 4920, 2118, 4923, 4925, 4073, 4789, 3095, 1681, 3097, 1682, 3099, 1683,
    4928, 2955, 3019, 4930, 4801, 3032, 3107, 1688, 4106, 4933, 4277, 3112, 1691, 4936, 4938,
    4940, 3035, 3118, 1694, 4942, 4092, 3278, 3957, 4945, 4200, 4624, 3127, 1699, 2107, 4948,
    4951, 4953, 3048, 3164, 4956, 3834, 4645, 3138, 1706, 3682, 4960, 4962, 3178, 4778, 3485,
    4653, 3147, 1711, 4966, 4967, 4969, 4971, 3153, 1716, 4974, 4976, 2956, 4978, 3159, 1719,
    4981, 4140, 4655, 3369, 3849, 4983, 4254, 3168, 1724, 4662, 4986, 2958, 4988, 2975, 3036,
    3176, 1729, 4990, 3985, 3252, 1935, 1843, 3122, 3898, 4992, 4993, 3216, 4286, 1737, 4997,
    4998, 4999, 3959, 3061, 4744, 4407, 1945, 5002, 4021, 4189, 3225, 1893, 1747, 4361, 4654,
    5005, 5006, 4607, 5008, 5009, 3880, 5011, 3974, 4094, 3279, 5013, 4995, 5015, 4669, 4678,
    5017, 5019, 5020, 4689, 5022, 4085, 4469, 4580, 5023, 5024, 5025, 3364, 5027, 4114, 3733,
    4502, 3721, 4082, 5030, 3863, 5032, 4752, 4480, 5033, 5034, 4205, 5035, 5037, 3093, 4253,
    5038, 4620, 1778, 2589, 4791, 1780, 3257, 1781, 4160, 3847, 5043, 4372, 5044, 1998, 2064,
    1786, 3267, 1787, 5048, 3270, 1789, 3272, 1790, 4795, 4621, 3276, 1794, 1795, 1796, 1797,
    5057, 1798, 3283, 1799, 5060, 5061, 4159, 3288, 1802, 3290, 1803, 4729, 3293, 1804, 2082,
    3846, 3297, 1806, 3299, 1807, 5065, 5066, 4769, 5068, 5070, 5072, 3726, 4518, 3171, 4506,
    4705, 5073, 4342, 5076, 5077, 3316, 1818, 3318, 1819, 4223, 3321, 1820, 3323, 1821, 5083,
    5084, 5086, 3328, 1824, 2689, 3331, 1826, 5088, 3334, 1828, 5090, 3337, 1829, 3339, 1830,
    1831, 2569, 3343, 1833, 4022, 5095, 5097, 3348, 1836, 5100, 1838, 1976, 5104, 3354, 1840,
    3356, 1841, 5107, 3359, 1842, 3181, 3853, 4450, 3059, 1850, 5112, 3367, 1852, 1853, 1854,
    4899, 1855, 3373, 1856, 5121, 5122, 1999, 3378, 1860, 5126, 3381, 1861, 3383, 1862, 5131,
    3386, 1863, 3388, 1864, 4481, 2656, 5135, 3393, 1869, 1870, 4753, 3397, 1871, 3399, 1872,
    5142, 3402, 1876, 3404, 1877, 5146, 2014, 2083, 3862, 3410, 1880, 1881, 2614, 3414, 1887,
    3416, 1888, 4404, 4788, 4727, 3421, 1891, 3423, 1892, 5154, 3201, 3427, 1894, 4793, 3430,
    1896, 4770, 2034, 1898, 4312, 3436, 1901, 3438, 1902, 4730, 3441, 1903, 3443, 1904, 5173,
    3446, 1907, 5177, 2304, 1910, 4734, 2105, 1912, 3454, 1913, 2023, 5092, 4262, 3213, 2177,
    2204, 3489, 5185, 4118, 5188, 4674, 5190, 2135, 4796, 3899, 3499, 5178, 2070, 3228, 4213,
    5194, 3950, 5196, 4009, 5198, 5200, 3262, 3284, 3161, 2518, 4062, 2991, 3555, 4589, 5184,
    5201, 4142, 5203, 2479, 3882, 5206, 3239, 3405, 5207, 4782, 4697, 5209, 3626, 3741, 4499,
    5210, 4006, 3824, 5153, 3105, 4522, 4152, 5214, 4115, 5216, 4003, 5219, 3518, 1960, 4759,
    3521, 1961, 1962, 5223, 3525, 1963, 3527, 1964, 5225, 1965, 3531, 1966, 5227, 4251, 4349,
    3536, 1969, 3538, 1970, 3835, 3541, 1971, 3543, 1972, 4758, 5234, 5236, 2474, 4004, 3550,
    1977, 1978, 5130, 3554, 1979, 1980, 5245, 3558, 1981, 3560, 1982, 3562, 1983, 2167, 1985,
    4670, 2144, 3204, 4061, 2602, 5251, 3375, 3244, 3714, 4527, 5253, 5255, 4615, 5256, 3747,
    4292, 4643, 3291, 3259, 2431, 3586, 1997, 3189, 5260, 3590, 2000, 3592, 2001, 2641, 5266,
    4176, 4097, 2340, 3599, 2006, 2160, 3027, 2008, 3190, 5270, 3295, 3607, 2011, 3609, 2012,
    3258, 3612, 2013, 2335, 2161, 3616, 2017, 4175, 2094, 3620, 2021, 2963, 3455, 5280, 4187,
    4069, 2030, 3628, 2031, 5285, 3631, 2032, 3633, 2033, 4161, 2523, 4116, 2036, 3639, 2037,
    3641, 2038, 2039, 3644, 2040, 4172, 2043, 2917, 5293, 3650, 2045, 2046, 3653, 2047, 4153,
    2048, 2926, 5301, 3659, 2052, 3661, 2053, 4432, 3664, 2054, 3666, 2055, 4260, 3379, 3670,
    2062, 3672, 2063, 3243, 3675, 2065, 4222, 4100, 5315, 3680, 2068, 2686, 4959, 3472, 3140,
    3686, 2073, 3011, 5323, 3690, 2077, 3692, 2078, 3145, 3695, 2080, 2511, 3205, 4802, 3700,
    2086, 2145, 2088, 5331, 3705, 2090, 3707, 2091, 3574, 3510, 3711, 2096, 3713, 2097, 4519,
    2098, 3717, 2099, 3307, 2801, 2823, 4513, 3723, 2103, 3725, 2104, 4511, 3128, 3309, 3730,
    2109, 3732, 2110, 4503, 3735, 2111, 2112, 3235, 2113, 2623, 2117, 4500, 3089, 2443, 3504,
    2778, 2931, 4494, 3749, 2122, 3751, 2123, 3753, 2124, 3755, 2125, 3757, 2126, 3759, 2127,
    3761, 2128, 2661, 3764, 2131, 3766, 2133, 3768, 2134, 3467, 3771, 2136, 3773, 2137, 3775,
    2138, 3777, 2139, 3779, 2140, 3781, 2142, 3566, 3701, 2676, 3786, 2147, 3788, 2148, 3790,
    2150, 3792, 2151, 3794, 2152, 3796, 2153, 3798, 2154, 3800, 2156, 3802, 2157, 2701, 3805,
    2159, 3600, 3614, 2904, 2783, 2967, 3812, 2165, 3814, 2166, 3010, 3817, 2169, 3852, 3374,
    3821, 2172, 3033, 5398, 4113, 3310, 2788, 5399, 3459, 5400, 3859, 3241, 3833, 2181, 4957,
    4344, 5404, 4355, 5405, 2830, 2795, 3842, 2187, 3844, 2188, 2684, 3605, 3583, 5411, 3133,
    2463, 3261, 3038, 4343, 5415, 2484, 3857, 2198, 5419, 5401, 2472, 5422, 3062, 3496, 4386,
    5425, 3867, 2203, 3460, 4906, 2992, 2668, 2468, 5427, 5428, 2460, 5430, 3173, 2211, 4331,
    3909, 4408, 5205, 3884, 2214, 3082, 5274, 4354, 3478, 5436, 2510, 2685, 3893, 2220, 3895,
    2221, 3486, 3224, 3072, 5192, 5438, 4145, 2794, 5441, 5229, 2965, 5443, 2825, 4325, 3210,
    4696, 2861, 2892, 4388, 3915, 2235, 3917, 2236, 3919, 2237, 3921, 2238, 3923, 2239, 3925,
    2241, 3927, 2242, 3929, 2243, 3931, 2244, 3933, 2246, 3935, 2247, 3937, 2248, 3939, 2249,
    3941, 2250, 3943, 2251, 5458, 4864, 2660, 4383, 3468, 3969, 5117, 3952, 2256, 5462, 3861,
    5463, 4698, 3182, 5468, 5001, 3961, 2261, 3963, 2262, 3965, 2263, 3822, 3873, 4559, 4332,
    5474, 5475, 3973, 2270, 4446, 4569, 4362, 3887, 3979, 2273, 4466, 2618, 4874, 4013, 4700,
    3142, 2593, 3988, 2284, 3990, 2285, 3992, 2286, 5481, 4885, 3823, 3997, 2289, 5483, 5485,
    5486, 4002, 2293, 5218, 5129, 3826, 5212, 3237, 3837, 3888, 4011, 2298, 4719, 5478, 3593,
    4745, 3495, 4018, 2302, 4020, 2303, 5003, 4049, 4024, 2308, 3513, 3634, 5492, 5495, 3148,
    2966, 2679, 3063, 3102, 2448, 5099, 5500, 5319, 4039, 2319, 2320, 2782, 5166, 3015, 5504,
    5505, 2899, 2742, 4419, 3344, 3326, 2757, 4603, 4054, 2330, 5507, 2562, 3953, 2440, 3240,
    3193, 5250, 3144, 3613, 3227, 4088, 5510, 3597, 3636, 5281, 4443, 5511, 3662, 4927, 4075,
    2344, 2715, 4457, 5239, 5055, 2960, 3577, 4007, 4084, 2350, 3200, 2990, 5516, 5509, 5517,
    5518, 2702, 3087, 5519, 3458, 4442, 3624, 2997, 5232, 2624, 4252, 4102, 2363, 4604, 4124,
    4806, 3075, 4108, 2372, 4110, 2373, 4112, 2374, 3507, 5029, 4025, 4068, 5527, 5187, 4076,
    4121, 2379, 3197, 4588, 5525, 4619, 4127, 2383, 4842, 5080, 2507, 4079, 4133, 2386, 5535,
    2560, 5175, 5537, 4139, 2390, 3483, 4606, 5202, 5259, 4090, 5439, 2488, 5313, 4149, 2395,
    3565, 3703, 5213, 4173, 5545, 2677, 4815, 4158, 2400, 4728, 3610, 4026, 3629, 4164, 2403,
    4485, 4167, 2408, 4737, 2449, 4036, 4080, 5292, 3654, 3014, 5277, 5268, 4579, 4179, 2421,
    4181, 2422, 4468, 5551, 2425, 4186, 2426, 4096, 3581, 5004, 2578, 2635, 4086, 4194, 2432,
    5555, 4197, 2434, 4199, 2435, 2438, 4838, 4203, 2439, 2996, 2442, 5561, 4208, 2444, 5309,
    4211, 2447, 4034, 5171, 4169, 2652, 5567, 4218, 2451, 4220, 2452, 3532, 4646, 4565, 4225,
    2458, 4227, 2459, 3314, 3875, 4231, 2461, 4553, 4234, 2465, 5548, 4237, 2467, 5577, 4668,
    3860, 4688, 4566, 4244, 2476, 4246, 2477, 5580, 4249, 2478, 3493, 5228, 3677, 2482, 2483,
    5584, 3855, 2485, 2487, 4146, 5311, 3136, 4568, 2579, 4265, 2492, 4095, 4268, 2493, 4270,
    2494, 3975, 4273, 2495, 4275, 2496, 4677, 2500, 4665, 4280, 2501, 2502, 5592, 4284, 2506,
    4130, 4996, 2595, 2653, 3890, 2513, 3623, 5258, 5599, 4295, 2516, 4297, 2517, 5601, 3484,
    4301, 2519, 5606, 4304, 2521, 5607, 2609, 3439, 4309, 2525, 4311, 2526, 5162, 4314, 2527,
    4316, 2528, 5614, 4319, 2531, 5615, 4322, 2533, 4324, 2534, 5445, 2707, 4328, 2536, 4330,
    2537, 2544, 3949, 2796, 2546, 3970, 2835, 2548, 5338, 2549, 4341, 2550, 5075, 3361, 3539,
    4346, 2553, 4348, 2554, 5127, 4351, 2555, 4353, 2556, 3977, 4008, 4357, 2561, 3836, 4360,
    2563, 2564, 5477, 4364, 2565, 4366, 2566, 4368, 2567, 4370, 2568, 3418, 3851, 3071, 4375,
    2577, 3498, 5634, 4379, 2580, 4381, 2581, 3247, 5308, 4385, 2585, 2586, 4867, 2588, 4216,
    4391, 2592, 3986, 3229, 4395, 2594, 3073, 4398, 2598, 5497, 2697, 4402, 2601, 3569, 5150,
    3260, 5568, 2605, 2606, 5652, 4411, 2607, 4413, 2608, 5654, 4117, 2611, 4418, 2612, 2613,
    5657, 3981, 4423, 2619, 5659, 4426, 2620, 2621, 4429, 2622, 4673, 4099, 4072, 4434, 2627,
    4436, 2628, 3657, 4439, 2629, 4441, 2630, 4266, 2633, 4445, 2634, 3212, 4448, 2636, 3313,
    4790, 3971, 4453, 2639, 4455, 2644, 5671, 2647, 4459, 2648, 4461, 2650, 3490, 4464, 2654,
    2950, 2659, 3946, 2662, 2663, 2664, 4472, 2665, 4474, 2666, 4476, 2667, 3871, 4479, 2669,
    2670, 2671, 4483, 2672, 2673, 2674, 4155, 4488, 2678, 4031, 4491, 2680, 4493, 2681, 3579,
    4496, 2682, 4498, 2683, 3744, 3503, 2687, 3737, 3234, 4505, 2693, 3728, 4508, 2694, 4510,
    2695, 3306, 2696, 3236, 4515, 2699, 4517, 2700, 3718, 3573, 4521, 2703, 3709, 4524, 2705,
    4526, 2706, 3708, 4529, 2710, 4531, 2711, 4533, 2712, 4535, 2713, 4537, 2714, 4539, 2717,
    4541, 2718, 4543, 2719, 4545, 2720, 4547, 2721, 4549, 2722, 4551, 2723, 4255, 4577, 4238,
    4556, 2726, 3169, 5708, 2972, 4561, 2731, 4563, 2736, 3039, 3319, 5579, 4241, 3457, 4271,
    4571, 2740, 4573, 2741, 4047, 3945, 5396, 4232, 3221, 5168, 4064, 4582, 2747, 5656, 4055,
    5712, 5350, 3480, 5529, 2968, 4591, 2752, 4593, 2753, 4595, 2754, 5703, 5341, 4051, 5669,
    4044, 3134, 3116, 2761, 5524, 4618, 5539, 5007, 4609, 2765, 3324, 3346, 4239, 3223, 3305,
    4081, 3029, 3172, 5383, 5531, 2776, 2777, 4623, 2779, 2780, 4626, 2781, 4628, 2784, 4630,
    2785, 4632, 2786, 4634, 2787, 4636, 2789, 4638, 2790, 4640, 2792, 4642, 2793, 4188, 5528,
    4261, 3676, 4648, 2802, 4585, 5595, 3829, 5380, 3693, 3567, 2807, 4657, 2808, 4659, 2809,
    4661, 2811, 4557, 4599, 3874, 2816, 5547, 4247, 4612, 2819, 4150, 4672, 2824, 5661, 4690,
    5370, 4129, 2833, 2834, 5733, 4558, 3827, 4902, 4684, 2839, 4831, 5736, 5737, 4567, 4613,
    3465, 3206, 4693, 2847, 4695, 2848, 2849, 5208, 5466, 4720, 5479, 4702, 2853, 3302, 3428,
    3825, 3576, 4302, 3208, 4710, 2858, 5706, 5318, 3911, 3156, 5276, 3086, 3904, 2951, 5489,
    5417, 3100, 4723, 2871, 4725, 2876, 3431, 5151, 3286, 3582, 4307, 2998, 3280, 3447, 4751,
    4736, 2882, 3024, 5740, 3104, 4741, 2887, 3184, 5340, 3013, 5491, 5240, 5744, 3900, 3912,
    3300, 3450, 3831, 5138, 4156, 5508, 4757, 2897, 4774, 5221, 3993, 5353, 4763, 2907, 4765,
    2908, 4767, 2909, 5747, 4703, 4726, 5749, 4887, 3501, 3544, 5750, 4078, 4738, 4964, 4780,
    2921, 5453, 3470, 4373, 4747, 4066, 5050, 5490, 4371, 3248, 3362, 2932, 5476, 4704, 3424,
    2935, 3948, 4798, 2939, 4035, 4715, 4739, 5328, 4804, 2952, 3101, 2957, 5757, 4809, 2959,
    4811, 2964, 5763, 4814, 2969, 4754, 4817, 2973, 4819, 2974, 5045, 4822, 2976, 4824, 2977,
    4826, 2984, 4828, 2985, 4830, 2986, 2987, 5617, 3870, 5770, 4836, 2994, 5683, 2995, 4204,
    4731, 5641, 3001, 3085, 5620, 4846, 3004, 4848, 3005, 5775, 4851, 3006, 5777, 4854, 3012,
    4856, 3016, 4858, 3020, 5597, 4861, 3021, 4863, 3022, 4575, 4866, 3023, 5639, 4869, 3028,
    5783, 4872, 3034, 3174, 3037, 4564, 5296, 4878, 3042, 4880, 3043, 5788, 4883, 3045, 5329,
    3047, 3132, 3051, 4889, 3052, 4891, 3053, 4893, 3054, 5796, 4896, 3057, 5689, 3363, 3060,
    5299, 4032, 3070, 5312, 5574, 4396, 3074, 5798, 4909, 3076, 4911, 3079, 4913, 3080, 4915,
    3081, 3885, 5106, 4716, 5552, 4921, 3088, 5807, 4924, 3090, 4926, 3091, 3092, 4721, 5809,
    4931, 3103, 3391, 4934, 3109, 4820, 4937, 3113, 4939, 3114, 4941, 3115, 4943, 3119, 5182,
    4946, 3123, 5137, 4949, 3129, 5820, 4952, 3130, 4954, 3131, 5152, 4601, 3135, 5180, 3139,
    3684, 5822, 4963, 3141, 3143, 5169, 4029, 4968, 3149, 4970, 3150, 4972, 3151, 4859, 4975,
    3154, 4977, 3155, 4979, 3157, 5575, 4982, 3160, 4984, 3165, 5834, 4987, 3170, 4617, 4183,
    4991, 3177, 4742, 4994, 3185, 3186, 3187, 3587, 3603, 5000, 3191, 3192, 4122, 3198, 3199,
    3697, 4691, 3207, 4708, 5010, 3209, 5012, 3211, 5014, 3215, 5016, 3217, 5018, 3220, 4578,
    5021, 3222, 3897, 3473, 4393, 5026, 3230, 5028, 3232, 3233, 5031, 3238, 4059, 3673, 3572,
    5036, 3246, 4382, 5039, 3250, 5869, 5051, 5544, 4405, 3481, 4935, 5872, 4743, 5049, 3268,
    5753, 5870, 5393, 5403, 5876, 4131, 4686, 4732, 5814, 5878, 3482, 5062, 3285, 5880, 5800,
    4750, 5067, 3301, 5069, 3303, 5071, 3304, 4614, 5074, 3311, 3312, 4449, 4228, 5893, 5052,
    4676, 5282, 4787, 4610, 5085, 3325, 4050, 5054, 5089, 3332, 5091, 3335, 5183, 5110, 5284,
    5096, 3345, 4611, 4147, 4799, 5101, 3349, 5900, 5447, 5105, 3352, 5553, 5108, 3357, 5290,
    5898, 5303, 5113, 3365, 4136, 5901, 4775, 3476, 5772, 5903, 5538, 3819, 3571, 5794, 4746,
    5907, 3668, 3534, 4832, 3548, 5241, 5132, 3384, 5909, 5078, 4932, 4955, 5818, 3395, 3508,
    5804, 5761, 5143, 3400, 5363, 5358, 3497, 5803, 5242, 5156, 3417, 3419, 5136, 5139, 4794,
    5233, 5910, 5249, 5768, 5141, 5368, 5913, 3434, 5244, 5808, 5145, 5502, 5828, 4177, 5181,
    5916, 3474, 4209, 5174, 3444, 5114, 4950, 4733, 5193, 5119, 5364, 4965, 5817, 3456, 3461,
    5186, 3462, 3463, 5189, 3464, 5191, 3466, 3469, 3471, 5195, 3475, 5197, 3477, 5199, 3479,
    4587, 4462, 3491, 5204, 3492, 3494, 4016, 4376, 3500, 4773, 5211, 3505, 3506, 3511, 5215,
    3512, 5217, 3514, 3515, 5220, 3516, 3519, 5936, 5224, 3523, 5226, 3528, 4221, 3533, 4717,
    5133, 5726, 5523, 5911, 5235, 3545, 5237, 3546, 5932, 4776, 5124, 3552, 5581, 5248, 5530,
    5246, 3556, 4841, 5861, 5651, 3568, 5252, 3570, 5254, 3575, 4706, 5257, 3578, 3580, 5541,
    5261, 3588, 5231, 4089, 5040, 5858, 5267, 3594, 3595, 5917, 5271, 3604, 5852, 5158, 5434,
    5222, 4800, 3617, 5947, 5562, 4291, 3625, 5894, 5291, 5605, 4162, 4884, 5935, 5816, 5064,
    5629, 5873, 3645, 5294, 3648, 4712, 5787, 4812, 4897, 5307, 5949, 4437, 5839, 5738, 5739,
    5676, 3848, 4900, 3947, 5172, 5685, 3667, 5573, 5098, 5843, 5316, 3678, 5414, 5295, 5501,
    5952, 5140, 5300, 5324, 3688, 5888, 5305, 5335, 3698, 5286, 4881, 4151, 5118, 5288, 5954,
    5769, 5586, 4317, 5619, 5956, 5047, 5621, 5892, 5958, 5792, 5959, 5961, 5912, 4679, 5962,
    5435, 5682, 4596, 5357, 5964, 4904, 5966, 4761, 5165, 5806, 5890, 5569, 4652, 5889, 4958,
    4195, 4206, 4711, 5691, 5969, 5378, 5944, 5819, 5860, 4781, 5170, 5951, 5570, 4675, 3865,
    5362, 5386, 5514, 4605, 5937, 4666, 5755, 5886, 5945, 5829, 5612, 5941, 4768, 5079, 5812,
    4792, 5526, 5730, 3995, 4681, 4651, 3830, 5729, 5857, 4358, 5406, 3838, 5972, 5582, 4235,
    5746, 5306, 5558, 5789, 5866, 5416, 3854, 4699, 5865, 5420, 3858, 5549, 3954, 5779, 5559,
    5379, 5977, 3967, 4664, 5813, 5431, 3876, 4852, 5980, 3886, 4586, 5437, 3889, 4748, 3901,
    5521, 5442, 3903, 5444, 3906, 3908, 4282, 5702, 3999, 5389, 5499, 5397, 5402, 5374, 4087,
    5920, 4687, 5854, 5459, 3944, 5986, 5987, 4057, 5464, 3955, 5979, 3956, 5989, 5469, 3958,
    4137, 5707, 5426, 5394, 4335, 4451, 5395, 3976, 3983, 3984, 5429, 4760, 4755, 5484, 3998,
    5448, 5487, 4000, 5571, 4012, 5082, 4015, 5493, 4027, 5948, 5496, 4028, 5646, 5613, 5984,
    4170, 4037, 4042, 5410, 4600, 5506, 4045, 4584, 5482, 4065, 4785, 5512, 4071, 5887, 5717,
    5760, 5454, 5263, 4144, 5520, 4093, 5732, 5776, 4098, 4103, 4104, 4576, 4415, 5611, 4123,
    5163, 4125, 5167, 5390, 5351, 5536, 4134, 5470, 5904, 4141, 6001, 4143, 6003, 4771, 5871,
    5546, 4154, 5385, 5409, 5778, 5821, 4989, 5805, 4917, 5824, 5365, 5377, 5373, 5975, 5790,
    5465, 5366, 5891, 5999, 5943, 4583, 5766, 4389, 5648, 5968, 5556, 5649, 5837, 4903, 5355,
    5830, 4922, 4554, 5795, 4242, 4667, 5148, 5919, 5663, 4552, 5831, 5955, 5825, 5940, 5594,
    6007, 5460, 5446, 5387, 6006, 5724, 6008, 4973, 5604, 5600, 4293, 5602, 4298, 5626, 5923,
    5094, 4707, 5608, 4305, 5471, 5631, 4644, 5533, 5985, 5337, 5616, 4320, 5128, 4837, 4338,
    5774, 4597, 5677, 5715, 5688, 5926, 5716, 5832, 5587, 5109, 5632, 5991, 5847, 5344, 5635,
    4377, 5624, 5859, 5627, 4387, 4849, 5247, 5897, 6010, 5339, 5550, 4399, 5059, 4406, 5488,
    5457, 5157, 5653, 4409, 5655, 4414, 5565, 5658, 4420, 5660, 4424, 4430, 5996, 6000, 5721,
    5563, 5578, 5884, 5115, 4663, 5662, 5672, 4456, 5664, 5590, 5992, 5326, 6009, 5325, 5522,
    5384, 6014, 5534, 5618, 5637, 5899, 5418, 5413, 5636, 5298, 6016, 5160, 6018, 5433, 5915,
    5147, 5494, 6020, 5554, 5983, 5782, 5998, 5103, 5352, 5974, 5764, 5367, 5609, 4680, 5939,
    5675, 5840, 4649, 6024, 5643, 5765, 5603, 5382, 5513, 5360, 5700, 5673, 5372, 5371, 4650,
    6026, 5262, 5705, 5922, 5452, 5451, 5265, 5440, 5348, 5704, 5343, 5056, 5456, 5111, 5781,
    4777, 6028, 5320, 5927, 4784, 5269, 5503, 5392, 5347, 5543, 5116, 5701, 6031, 4786, 5359,
    5381, 5302, 5758, 4807, 5867, 5997, 5159, 5278, 5297, 5727, 5623, 6005, 5759, 5273, 5327,
    5771, 4834, 5332, 5882, 4844, 5640, 5679, 5432, 5421, 5976, 5346, 5304, 5720, 5784, 4870,
    5846, 5625, 4876, 5330, 5687, 5424, 5850, 5633, 5785, 5905, 5666, 5797, 4894, 5799, 4907,
    5289, 5596, 5942, 5695, 5321, 4919, 5754, 5576, 5914, 5810, 4929, 5802, 5473, 5480, 5877,
    5752, 5333, 4944, 4947, 5722, 5176, 5645, 5823, 4961, 5698, 5628, 5918, 5046, 5532, 5449,
    4980, 5993, 5638, 5725, 5835, 4985, 5826, 5838, 5572, 5756, 6023, 5542, 5238, 5845, 5971,
    5314, 5793, 5630, 5709, 5287, 5925, 6004, 5856, 5391, 5650, 6035, 5272, 5053, 5731, 5684,
    5557, 5243, 5455, 6034, 5667, 5686, 5317, 5767, 5642, 5264, 5041, 5042, 5827, 5283, 5728,
    6038, 5087, 5058, 5647, 5388, 5881, 5063, 5931, 5102, 5864, 5902, 5593, 5718, 5678, 5144,
    5719, 5279, 5957, 5134, 5081, 5161, 5875, 5868, 5093, 5310, 5883, 5668, 5988, 5179, 5120,
    5123, 5376, 5908, 5125, 5230, 5149, 5155, 5748, 5895, 5164, 6019, 5375, 5745, 5836, 5408,
    5862, 6040, 5874, 5598, 5981, 5791, 5786, 6030, 5461, 5588, 5995, 5773, 5842, 6037, 5564,
    5849, 5275, 5680, 5692, 5848, 5929, 5853, 5811, 5934, 5723, 5879, 5933, 5762, 5696, 5322,
    5334, 5906, 5742, 5930, 5950, 5336, 5644, 5342, 5735, 5960, 5345, 5780, 5963, 5349, 5965,
    5354, 5967, 5356, 5361, 5970, 5369, 6036, 5973, 5407, 5734, 5412, 5423, 5472, 6041, 5560,
    5693, 6011, 5851, 6021, 5450, 5498, 5591, 5928, 5885, 5990, 5467, 5610, 5710, 5585, 6042,
    5953, 5670, 5515, 5751, 5665, 5583, 6002, 5540, 5841, 5982, 5566, 5589, 5674, 5801, 5622,
    5714, 5924, 5697, 5921, 6015, 5681, 6017, 5690, 5938, 5694, 6012, 5699, 6046, 5711, 6025,
    5713, 5833, 6047, 6029, 5741, 5743, 5815, 5863, 5855, 6032, 6033, 5844, 5946, 5896, 6022,
    6013, 6044, 6045, 6027, 5978, 5994, 6039, 6043]

/-- Cayley-table column for left multiplication by `a⁻¹`: `nextAI[i]` is the index of
the element `a⁻¹ · evalWord (word i)`. -/
def nextAI : Array Nat :=
  #[3, 0, 9, 5, 13, 1, 17, 19, 2, 20, 26, 28, 4, 29, 35, 37, 6, 38, 7, 43, 8, 51, 53, 55, 57,
    10, 58, 11, 63, 12, 71, 73, 75, 77, 14, 78, 15, 83, 16, 91, 93, 95, 97, 18, 101, 103, 105,
    107, 109, 111, 21, 112, 22, 117, 23, 122, 24, 127, 25, 135, 137, 139, 141, 27, 145, 147,
    149, 151, 153, 155, 30, 156, 31, 161, 32, 166, 33, 171, 34, 179, 181, 183, 185, 36, 189,
    191, 193, 195, 197, 199, 39, 200, 40, 205, 41, 210, 42, 215, 221, 223, 44, 224, 45, 229, 46,
    234, 47, 239, 48, 187, 49, 248, 50, 256, 258, 260, 262, 52, 266, 268, 269, 271, 54, 275,
    277, 279, 281, 56, 285, 287, 289, 291, 222, 293, 59, 294, 60, 299, 61, 303, 62, 308, 314,
    196, 64, 315, 65, 320, 66, 325, 67, 330, 68, 335, 69, 176, 70, 347, 349, 351, 352, 72, 356,
    358, 360, 362, 74, 366, 319, 369, 371, 76, 375, 377, 379, 381, 154, 383, 79, 384, 80, 389,
    81, 394, 82, 399, 405, 108, 84, 406, 85, 411, 86, 416, 87, 421, 88, 143, 89, 430, 90, 438,
    440, 442, 444, 92, 448, 450, 451, 453, 94, 457, 459, 461, 463, 96, 120, 468, 470, 472, 98,
    473, 99, 132, 100, 485, 487, 489, 490, 102, 494, 496, 498, 500, 104, 504, 160, 507, 509,
    106, 513, 515, 517, 519, 521, 523, 525, 527, 110, 530, 532, 534, 536, 538, 540, 113, 541,
    114, 546, 115, 551, 116, 556, 561, 563, 118, 564, 119, 569, 466, 121, 576, 562, 582, 123,
    583, 124, 588, 125, 592, 126, 596, 602, 537, 128, 603, 129, 606, 130, 611, 131, 616, 133,
    621, 134, 629, 631, 633, 635, 136, 639, 641, 643, 138, 647, 649, 651, 653, 140, 392, 658,
    660, 662, 142, 663, 144, 671, 673, 675, 676, 146, 680, 682, 684, 686, 148, 690, 410, 693,
    695, 150, 699, 701, 703, 542, 152, 706, 708, 710, 712, 714, 716, 718, 720, 722, 724, 157,
    725, 158, 730, 159, 735, 505, 743, 745, 162, 746, 163, 751, 164, 755, 165, 758, 744, 764,
    167, 765, 168, 169, 772, 170, 777, 783, 721, 172, 784, 173, 787, 174, 792, 175, 797, 177,
    801, 178, 809, 811, 813, 815, 180, 819, 821, 822, 824, 182, 828, 830, 832, 834, 184, 208,
    839, 841, 843, 186, 844, 188, 852, 854, 856, 857, 190, 861, 863, 865, 867, 192, 871, 228,
    874, 876, 194, 880, 882, 884, 886, 888, 890, 892, 894, 198, 897, 899, 901, 903, 905, 907,
    201, 908, 202, 911, 203, 916, 204, 921, 926, 928, 206, 929, 207, 934, 837, 209, 941, 927,
    947, 211, 948, 212, 953, 213, 957, 214, 961, 967, 904, 216, 217, 970, 218, 975, 219, 980,
    220, 986, 988, 990, 992, 994, 996, 998, 1000, 1002, 1004, 225, 1005, 226, 1010, 227, 1015,
    872, 1023, 1025, 230, 1026, 231, 1031, 232, 1034, 233, 1037, 1024, 1043, 235, 1044, 236,
    237, 1051, 238, 1056, 1062, 1001, 240, 1063, 241, 1066, 242, 1071, 243, 1076, 244, 1080,
    245, 1085, 246, 1090, 247, 1095, 1100, 249, 816, 250, 807, 251, 835, 252, 826, 253, 283,
    254, 803, 255, 1127, 1129, 1131, 1133, 257, 1137, 1139, 1140, 1142, 259, 1070, 1147, 1149,
    1151, 261, 1155, 1157, 1159, 263, 802, 264, 272, 265, 1171, 1172, 1174, 1175, 267, 1179,
    1180, 1182, 1184, 1186, 1188, 270, 1192, 1194, 1196, 1198, 273, 805, 274, 1206, 1208, 1210,
    1212, 276, 1216, 1218, 1220, 278, 1224, 1226, 1228, 280, 1088, 1233, 1235, 1237, 282, 804,
    284, 1245, 1246, 286, 1250, 1252, 1254, 1256, 288, 1260, 1104, 1262, 1263, 290, 1267, 1269,
    1271, 726, 292, 925, 906, 966, 946, 1274, 898, 295, 1275, 296, 1279, 297, 1284, 298, 1289,
    896, 1294, 300, 1295, 301, 1299, 302, 1304, 1293, 902, 304, 1309, 305, 1314, 306, 1318, 307,
    1321, 900, 1273, 309, 310, 1327, 311, 1332, 312, 1335, 313, 1022, 1003, 1061, 1042, 1341,
    987, 316, 1342, 317, 1347, 318, 1352, 367, 985, 1360, 321, 1361, 322, 1366, 323, 1370, 324,
    1373, 1359, 991, 326, 1377, 327, 328, 1384, 329, 1389, 989, 1340, 331, 1394, 332, 1397, 333,
    1402, 334, 336, 858, 337, 850, 338, 877, 339, 869, 340, 1425, 341, 1430, 342, 1435, 343,
    1440, 344, 373, 345, 846, 346, 1455, 1457, 1459, 1461, 348, 1348, 1465, 1382, 1467, 350,
    1471, 1473, 1475, 1477, 1390, 1480, 353, 845, 354, 363, 355, 1492, 1494, 1496, 1497, 357,
    1501, 1503, 1505, 359, 1509, 1511, 361, 1515, 951, 1518, 1520, 364, 848, 365, 1528, 1530,
    1532, 1534, 1535, 1537, 368, 1541, 1543, 571, 1546, 370, 1415, 1550, 1392, 1552, 372, 847,
    374, 1560, 1562, 376, 1566, 1568, 1570, 1571, 378, 1575, 1429, 1578, 1580, 380, 1584, 1586,
    1588, 382, 560, 539, 601, 581, 1591, 531, 385, 1592, 386, 1595, 387, 1600, 388, 1605, 529,
    1610, 390, 1611, 391, 1616, 656, 393, 1623, 1609, 535, 395, 1628, 396, 1633, 397, 1637, 398,
    1640, 533, 1590, 400, 401, 1647, 402, 1652, 403, 1657, 404, 742, 723, 782, 763, 1663, 707,
    407, 1664, 408, 1669, 409, 1674, 691, 705, 1682, 412, 1683, 413, 1688, 414, 1691, 415, 1694,
    1681, 711, 417, 1699, 418, 419, 1706, 420, 1711, 709, 1662, 422, 1716, 423, 1719, 424, 1724,
    425, 1729, 426, 1732, 427, 1737, 428, 1742, 429, 1747, 528, 431, 636, 432, 627, 433, 654,
    434, 645, 435, 465, 436, 623, 437, 1779, 1781, 439, 1785, 1787, 1788, 1790, 441, 1723, 1795,
    1797, 1799, 443, 1803, 1805, 1807, 445, 622, 446, 454, 447, 1819, 566, 1821, 605, 449, 1825,
    1826, 1828, 1830, 1832, 613, 452, 1837, 1839, 1841, 1843, 455, 625, 456, 1851, 1853, 1854,
    1856, 458, 1860, 1862, 1864, 460, 1868, 1870, 1872, 462, 1740, 1877, 1879, 1881, 464, 624,
    1887, 1888, 467, 1892, 1894, 1896, 1898, 469, 1902, 1755, 1904, 615, 471, 1908, 1910, 1912,
    1006, 474, 677, 475, 669, 476, 696, 477, 688, 478, 1930, 479, 1935, 480, 1940, 481, 1945,
    482, 511, 483, 665, 484, 1960, 1962, 1964, 1966, 486, 731, 1970, 770, 1972, 488, 1976, 1978,
    1980, 1982, 778, 1985, 491, 664, 492, 501, 493, 1997, 1999, 2001, 2002, 495, 2006, 2008,
    497, 2012, 2014, 499, 2018, 1631, 2021, 2023, 502, 667, 503, 2031, 2033, 2035, 2037, 2038,
    2040, 506, 2044, 2046, 936, 2049, 508, 1920, 2053, 780, 2055, 510, 666, 512, 2063, 2065,
    514, 2069, 2071, 2073, 2074, 516, 2078, 1934, 2081, 2083, 518, 2087, 2089, 2091, 520, 2094,
    1687, 2097, 2099, 522, 2102, 2104, 2105, 2107, 524, 2110, 2112, 2114, 2115, 526, 549, 2119,
    2121, 2123, 1589, 2125, 1883, 2127, 1833, 2129, 2131, 2133, 2135, 2137, 568, 2140, 2141,
    2143, 2145, 2147, 2149, 2151, 2153, 2155, 2157, 2159, 2161, 2163, 2165, 2167, 2169, 704,
    543, 2172, 544, 2177, 545, 2181, 2186, 2188, 547, 2189, 548, 2192, 2117, 550, 2198, 2187,
    2204, 552, 553, 2207, 554, 2211, 555, 2214, 2220, 2166, 557, 2221, 558, 2226, 559, 2230,
    2236, 2237, 2239, 1763, 2242, 2244, 2246, 2248, 2250, 1811, 565, 2251, 1613, 567, 2256,
    2138, 2262, 1886, 570, 2263, 1544, 572, 2270, 573, 2273, 574, 1906, 575, 1809, 2285, 2249,
    577, 2286, 578, 2289, 579, 2293, 580, 2298, 2185, 2168, 2219, 2203, 2303, 2160, 584, 2304,
    585, 2308, 586, 2313, 587, 2315, 2158, 2320, 589, 2321, 590, 2325, 591, 2330, 2319, 2164,
    593, 2335, 594, 2340, 595, 2344, 2162, 2302, 597, 598, 2350, 599, 2355, 600, 2358, 2261,
    1900, 2284, 1615, 2364, 1654, 604, 2365, 1761, 2235, 2373, 607, 2374, 608, 2379, 609, 2383,
    610, 2386, 2372, 2240, 612, 2390, 614, 2395, 1656, 2238, 2363, 617, 2400, 618, 2403, 619,
    2408, 620, 626, 655, 628, 2422, 2424, 2426, 630, 2430, 2432, 2433, 2435, 632, 791, 2440,
    2442, 2444, 634, 2448, 2450, 2452, 637, 644, 638, 2459, 2461, 1646, 640, 2464, 2465, 2467,
    2469, 642, 2473, 2475, 2477, 2479, 646, 2483, 2485, 2486, 2488, 648, 2492, 2494, 2496, 650,
    2500, 2502, 652, 1948, 2507, 2509, 2511, 2513, 657, 2517, 2519, 2521, 2523, 659, 2526, 2528,
    661, 2532, 2534, 2536, 1343, 668, 697, 670, 2544, 2546, 2548, 2550, 672, 1670, 2554, 1704,
    2556, 674, 2560, 2562, 2564, 2566, 1712, 2569, 678, 687, 679, 2577, 2579, 2581, 2582, 681,
    2586, 2588, 2589, 683, 2593, 2595, 685, 2599, 2601, 2602, 689, 2606, 2608, 2610, 2612, 2613,
    2615, 692, 2619, 2621, 1301, 2624, 694, 1954, 2628, 1714, 2630, 698, 2634, 2636, 700, 2640,
    2642, 2644, 2306, 702, 2648, 1746, 2651, 2653, 2655, 2657, 2659, 2661, 2663, 2665, 2024,
    2667, 1983, 2669, 2671, 2673, 2675, 2677, 733, 2679, 2625, 2681, 713, 2683, 2685, 2687,
    2688, 715, 1598, 2691, 2693, 2695, 717, 2697, 750, 2700, 2702, 719, 2704, 2706, 2707, 2709,
    2711, 2713, 2715, 2717, 2567, 2719, 1928, 2721, 2039, 2723, 1272, 727, 2726, 728, 2731, 729,
    2736, 1956, 2741, 732, 2742, 734, 2747, 2740, 2753, 736, 2754, 737, 2757, 738, 2761, 739,
    2765, 740, 741, 2041, 2777, 2779, 2781, 2783, 2785, 2787, 2789, 2791, 2793, 2795, 747, 2796,
    748, 2801, 749, 2802, 2698, 2808, 2810, 752, 2811, 753, 2816, 754, 2819, 2809, 2824, 756,
    2825, 757, 2830, 2834, 2792, 759, 2835, 760, 761, 2839, 762, 2844, 2050, 2722, 1672, 2752,
    2848, 2718, 766, 2849, 767, 2853, 768, 2858, 769, 2861, 1926, 771, 2542, 2568, 2720, 773,
    2871, 774, 2876, 775, 776, 2882, 2551, 2847, 779, 2887, 781, 2892, 2807, 2794, 2833, 2823,
    2898, 2778, 785, 2899, 786, 2904, 2776, 2908, 788, 2909, 789, 2914, 790, 2917, 2438, 2907,
    2782, 793, 2921, 794, 795, 2926, 796, 2931, 2780, 2897, 798, 2932, 799, 2935, 800, 2939,
    895, 806, 836, 808, 2821, 2952, 810, 2956, 2957, 2958, 2960, 812, 1401, 2965, 2967, 2969,
    814, 2973, 2975, 2977, 817, 825, 818, 2985, 931, 2987, 969, 820, 2991, 2992, 2994, 2996,
    2774, 977, 823, 3002, 3003, 3005, 3007, 827, 3011, 3013, 3014, 3016, 829, 3020, 3022, 3024,
    831, 3027, 3029, 833, 1443, 3034, 3036, 2930, 3038, 3039, 838, 3043, 3045, 3047, 2860, 840,
    3052, 1161, 3054, 979, 842, 3058, 3060, 3062, 1665, 849, 878, 851, 3070, 3072, 3074, 3076,
    853, 1011, 3080, 1049, 3082, 855, 3085, 3087, 3089, 3091, 1057, 2281, 859, 868, 860, 3100,
    3102, 3104, 3105, 862, 3109, 2180, 864, 3114, 3116, 866, 3120, 1312, 3123, 3125, 870, 3129,
    3131, 2388, 3134, 3135, 3136, 873, 3140, 3142, 1618, 3145, 875, 1449, 3149, 1059, 3151, 879,
    3155, 3157, 881, 3161, 3163, 3165, 3166, 883, 3170, 1094, 2361, 3174, 885, 3178, 3179, 887,
    3182, 1365, 3185, 3187, 889, 3190, 3192, 3193, 3195, 891, 3198, 3200, 3201, 2883, 893, 914,
    2215, 3205, 3207, 3209, 1112, 3211, 2998, 3213, 3215, 3217, 3219, 3221, 933, 3223, 1258,
    3225, 3227, 3229, 3231, 3233, 3235, 2349, 3238, 3240, 3242, 3244, 3246, 3248, 3250, 909,
    3251, 910, 3254, 3259, 3261, 912, 3262, 913, 2264, 2267, 915, 3268, 3260, 3274, 917, 918,
    2274, 919, 2277, 920, 3280, 3285, 3247, 922, 3286, 923, 3291, 924, 3295, 3301, 1187, 3303,
    1239, 3305, 3307, 3309, 3311, 3313, 1102, 930, 3314, 932, 3319, 3325, 2867, 935, 3326, 2047,
    937, 3332, 938, 3335, 939, 3056, 940, 3345, 3312, 942, 3346, 943, 3349, 944, 3352, 945,
    3357, 3258, 3249, 3284, 3273, 3362, 3241, 949, 3363, 950, 3365, 1516, 952, 3370, 3239, 2870,
    954, 3375, 955, 3379, 956, 3384, 3374, 3245, 958, 3389, 959, 3391, 960, 3395, 3243, 3361,
    962, 963, 3400, 964, 3405, 965, 3408, 3324, 3050, 3344, 1298, 968, 1177, 1241, 3300, 3418,
    971, 3419, 972, 3424, 973, 3428, 974, 3431, 3417, 1169, 976, 3434, 978, 3439, 3302, 1185,
    981, 3444, 982, 3447, 983, 3450, 984, 3456, 3458, 3460, 3462, 1423, 3464, 3092, 3466, 3468,
    3470, 3472, 3474, 1013, 3476, 1547, 3478, 993, 3480, 3482, 3484, 3485, 995, 1282, 3488,
    3490, 3492, 997, 2841, 1030, 3495, 3497, 999, 3499, 3501, 2410, 3502, 3504, 3506, 3508,
    3510, 1478, 3512, 1521, 3514, 2367, 3516, 1913, 1007, 3519, 1008, 3523, 1009, 3528, 1413,
    3533, 1012, 3534, 1014, 3539, 3532, 3545, 1016, 3546, 1017, 3548, 1018, 3552, 1019, 3556,
    1020, 1021, 3137, 3566, 3568, 3570, 3572, 3574, 3576, 3578, 2197, 3581, 3583, 1027, 2728,
    1028, 3587, 1029, 3588, 2729, 3594, 3596, 1032, 3597, 1033, 3600, 3595, 3604, 1035, 3605,
    1036, 3610, 3614, 3580, 1038, 2733, 1039, 1040, 3617, 1041, 2734, 3146, 3515, 1350, 3544,
    3624, 3511, 1045, 3625, 1046, 3629, 1047, 3634, 1048, 3636, 1523, 1050, 1453, 1479, 3513,
    1052, 3645, 1053, 3648, 1054, 1055, 3654, 1462, 3623, 1058, 3657, 1060, 3662, 3593, 3582,
    3613, 3603, 2368, 3567, 1064, 3668, 1065, 3673, 3565, 3677, 1067, 3678, 1068, 3682, 1069,
    3684, 1145, 3676, 3571, 1072, 3688, 1073, 1074, 3693, 1075, 3697, 3569, 3667, 1077, 3698,
    1078, 3701, 1079, 3703, 3202, 1081, 3708, 1082, 1083, 3709, 1084, 3714, 3196, 1086, 3718,
    1087, 3721, 1231, 1089, 3726, 3188, 1091, 3728, 1092, 3733, 1093, 3737, 3171, 3180, 1096,
    1097, 3741, 1098, 3744, 1099, 3747, 1101, 3055, 1103, 3040, 1105, 3030, 1106, 3026, 1107,
    3017, 1108, 3009, 1109, 2999, 1110, 1111, 2988, 2983, 1113, 2970, 1114, 2962, 1115, 2953,
    1116, 2949, 1117, 3095, 1118, 3064, 1119, 3067, 1120, 3096, 1121, 1213, 1122, 1204, 1123,
    1229, 1124, 1222, 1125, 1153, 1126, 1200, 3455, 3819, 1128, 3823, 3825, 3826, 3591, 1130,
    3830, 3602, 3831, 1132, 3835, 3837, 3608, 1134, 1199, 1135, 1143, 1136, 3847, 3849, 1138,
    1684, 3851, 3853, 3855, 2455, 1141, 3859, 3861, 3863, 3865, 1144, 1202, 1376, 3871, 1146,
    3874, 3876, 3877, 1148, 3880, 3882, 1150, 3795, 3886, 3888, 3890, 1152, 1201, 1154, 3897,
    3899, 3900, 3901, 1156, 3904, 3805, 3906, 1158, 3909, 3911, 3912, 2252, 1160, 1247, 1243,
    1162, 1264, 1163, 1164, 3065, 1165, 3094, 1166, 3097, 1167, 3066, 1168, 1190, 1170, 3944,
    3946, 3948, 3950, 1173, 3954, 3276, 3957, 3959, 1176, 1238, 1178, 1786, 3967, 3968, 1748,
    3970, 3621, 1181, 3975, 3977, 1183, 1794, 3731, 3981, 1796, 2590, 3983, 2194, 2616, 3918,
    3986, 1189, 1240, 1191, 3994, 3270, 1193, 1675, 2859, 4000, 1195, 4004, 3927, 4007, 4009,
    1197, 4013, 2732, 4016, 1203, 1230, 1205, 3553, 2963, 3652, 1207, 4026, 4027, 1949, 4029,
    1209, 4032, 1211, 4034, 4036, 3438, 1214, 1221, 1215, 4043, 4045, 3740, 1217, 4048, 3699,
    4050, 4052, 1219, 4056, 4058, 4060, 4062, 1223, 3702, 1731, 1369, 4066, 1225, 4069, 4071,
    4073, 1227, 3936, 4078, 4080, 4082, 2541, 1232, 4086, 3704, 4089, 3430, 1234, 4093, 4095,
    1236, 4097, 4098, 4099, 2366, 1242, 1265, 1244, 4103, 1705, 2085, 4105, 3774, 4106, 1248,
    1257, 1249, 4114, 4116, 4118, 4119, 1251, 4123, 4125, 3622, 1253, 4129, 4131, 1255, 4135,
    4136, 4137, 1259, 4141, 4143, 4145, 4147, 1261, 4151, 4153, 2327, 4156, 1266, 4160, 4162,
    1268, 4165, 2482, 2487, 2851, 1270, 4169, 2505, 2510, 4171, 4173, 4175, 3575, 3503, 3509,
    3577, 2773, 3230, 1276, 4177, 1277, 4182, 1278, 4183, 3228, 4188, 1280, 4189, 1281, 4192,
    3486, 1283, 4195, 4187, 3226, 1285, 1286, 4201, 1287, 4204, 1288, 4206, 3224, 4176, 1290,
    4209, 1291, 4213, 1292, 4216, 3505, 3573, 3579, 3507, 4222, 1296, 4223, 1297, 4228, 3222,
    1300, 4232, 2622, 1302, 4235, 1303, 4238, 3220, 4221, 1305, 4239, 1306, 4241, 1307, 4242,
    1308, 4247, 4252, 3218, 1310, 2405, 1311, 4255, 3121, 1313, 2406, 3216, 4261, 1315, 4262,
    1316, 4266, 1317, 4271, 4260, 3214, 1319, 4276, 1320, 4278, 3212, 4251, 1322, 1323, 4282,
    1324, 4286, 1325, 2411, 1326, 2989, 3210, 4292, 1328, 4293, 1329, 4298, 1330, 4302, 1331,
    4305, 4291, 1333, 4307, 1334, 4312, 3208, 2997, 1336, 4317, 1337, 4320, 1338, 4325, 1339,
    3234, 3304, 3310, 3236, 1536, 3477, 2537, 1344, 4332, 1345, 4335, 1346, 4338, 1451, 4343,
    1349, 4344, 1351, 4349, 4342, 3475, 1353, 4354, 1354, 4355, 1355, 4358, 1356, 4362, 1357,
    1358, 1538, 3306, 3232, 3237, 3308, 4372, 3473, 1362, 4373, 1363, 4376, 1364, 4377, 3183,
    3471, 2278, 1367, 4383, 1368, 4387, 3768, 4382, 3469, 1371, 4389, 1372, 4393, 3467, 4371,
    1374, 4396, 1375, 4399, 3869, 4405, 3465, 1378, 4406, 1379, 4409, 1380, 4414, 1381, 4415,
    1421, 1383, 3068, 3093, 3463, 1385, 4420, 1386, 4424, 1387, 1388, 4430, 3077, 4404, 1391,
    4432, 1393, 4437, 3818, 3461, 1395, 4442, 1396, 4446, 3459, 4450, 1398, 4451, 1399, 2872,
    1400, 2875, 4449, 3457, 1403, 4456, 1404, 1405, 2886, 1406, 4462, 1407, 3833, 1408, 3867,
    1409, 3175, 1410, 3168, 1411, 3158, 1412, 3153, 1414, 3138, 1416, 3127, 1417, 3117, 1418,
    3112, 1419, 3106, 1420, 3099, 1422, 3084, 1424, 3069, 1426, 4494, 1427, 4499, 1428, 4500,
    1576, 1431, 1432, 4502, 1433, 4503, 1434, 4506, 1436, 4511, 1437, 1438, 4513, 1439, 4518,
    1441, 4519, 1442, 4522, 3032, 1444, 4527, 1445, 2945, 1446, 2978, 1447, 2981, 1448, 2946,
    1450, 1526, 1452, 1539, 1454, 1522, 3278, 4554, 1456, 4558, 1996, 1942, 4559, 1458, 4526,
    2017, 2022, 4321, 1460, 4565, 4567, 4569, 1463, 1468, 1464, 3760, 4576, 4578, 4580, 1466,
    3615, 4585, 4587, 4589, 1469, 1524, 1470, 2389, 1625, 1472, 3589, 4601, 4602, 1474, 2275,
    4605, 4607, 1476, 4534, 4611, 4613, 4615, 4219, 4368, 4618, 2446, 2530, 2797, 1481, 1563,
    1482, 1558, 1483, 1581, 1484, 1573, 1485, 2979, 1486, 2944, 1487, 2947, 1488, 2980, 1489,
    1513, 1490, 1554, 1491, 4643, 1597, 4452, 4646, 1493, 1495, 4649, 4651, 4652, 4654, 1498,
    1553, 1499, 1506, 1500, 3824, 4663, 3272, 3799, 1502, 3299, 4668, 1504, 3829, 4670, 3253,
    1507, 1556, 1508, 4126, 4674, 2744, 4148, 1510, 4622, 4676, 1512, 1555, 1514, 4679, 4681,
    3756, 1517, 4686, 4630, 4460, 4689, 1519, 4690, 4691, 1525, 1548, 1527, 4698, 3279, 4700,
    1529, 4704, 4706, 3937, 4708, 1531, 4711, 4712, 1533, 4212, 4715, 4717, 4718, 4419, 1645,
    4719, 4721, 1865, 1540, 2641, 3788, 2382, 2643, 1542, 4727, 4729, 4731, 4732, 4734, 1545,
    2649, 4394, 4739, 2650, 1549, 4743, 4745, 4746, 4748, 1551, 4751, 4753, 4754, 2900, 1557,
    1582, 1559, 3393, 3775, 4011, 4759, 1561, 4334, 4761, 1564, 1572, 1565, 4768, 4770, 4772,
    1745, 1567, 3359, 3454, 1569, 3660, 4777, 4778, 1574, 3397, 4783, 3638, 4786, 1577, 4787,
    4789, 2868, 4327, 1579, 1583, 4792, 4794, 1585, 1638, 3390, 4065, 1587, 4799, 4076, 4081,
    4801, 2786, 2710, 2716, 2788, 4370, 2148, 1593, 1594, 4802, 2146, 4642, 1596, 3734, 3327,
    2689, 1599, 4807, 4694, 2144, 1601, 1602, 3336, 1603, 3339, 1604, 4812, 2142, 4658, 1606,
    4815, 1607, 4486, 1608, 4820, 2712, 2784, 2790, 2714, 4762, 1753, 1612, 3951, 1614, 3943,
    2139, 2512, 1617, 4832, 3143, 1619, 4834, 1620, 4837, 1621, 1622, 2136, 4571, 1624, 4841,
    4597, 1626, 4844, 1627, 4849, 4765, 2134, 1629, 4322, 1630, 4852, 2019, 1632, 4323, 2132,
    3644, 1634, 4467, 1635, 4859, 1636, 4864, 4756, 2130, 4796, 1639, 4867, 2128, 4572, 1641,
    1642, 4870, 1643, 3716, 1644, 1823, 1885, 2126, 4639, 1648, 4876, 1649, 4881, 1650, 4884,
    1651, 4693, 1817, 1653, 4149, 1655, 4138, 2124, 1831, 1658, 4894, 1659, 4897, 1660, 4900,
    1661, 2152, 2241, 2247, 2154, 2614, 2680, 3063, 1666, 4903, 1667, 4904, 1668, 4907, 1918,
    4018, 1671, 4582, 1673, 4574, 3938, 2678, 3998, 1676, 4917, 1677, 4919, 1678, 4922, 1679,
    1680, 2243, 2150, 2156, 2245, 3843, 2676, 3521, 1685, 4521, 1686, 4929, 2095, 2674, 4101,
    1689, 4932, 1690, 3814, 2672, 1692, 4935, 1693, 3786, 2670, 4110, 1695, 3525, 1696, 1697,
    4944, 1698, 3526, 3842, 2668, 1700, 4947, 1701, 4950, 1702, 1703, 4955, 2026, 1958, 1984,
    2666, 1707, 4958, 1708, 4961, 1709, 1710, 4965, 1967, 4107, 1713, 4749, 1715, 4741, 3413,
    2664, 1717, 4973, 1718, 3761, 2662, 4019, 1720, 4980, 1721, 4421, 1722, 4423, 1793, 3941,
    2660, 1725, 4985, 1726, 1727, 1728, 4505, 2658, 4039, 1730, 4989, 4064, 2092, 1733, 3929,
    1734, 1735, 3798, 1736, 3930, 2100, 1738, 4628, 1739, 4538, 1875, 1741, 4629, 2108, 1743,
    4638, 1744, 4530, 4529, 2116, 1749, 1750, 3794, 1751, 3932, 1752, 2529, 1754, 2514, 1756,
    2503, 1757, 2498, 1758, 2489, 1759, 2481, 1760, 2470, 1762, 2462, 1764, 2445, 1765, 2437,
    1766, 2427, 1767, 2420, 1768, 2571, 1769, 2538, 1770, 1771, 2572, 1772, 1857, 1773, 1849,
    1774, 1873, 1775, 1866, 1776, 1801, 1777, 1845, 1778, 5041, 2179, 1780, 4047, 4051, 4938,
    1782, 1844, 1783, 1791, 1784, 3784, 4416, 4641, 4573, 2310, 1789, 5051, 5052, 3715, 5053,
    1792, 1847, 5055, 5056, 4215, 3914, 3710, 1798, 5058, 4549, 2360, 1800, 1846, 1802, 3893,
    4671, 3848, 4042, 1804, 5064, 4059, 4057, 1806, 3915, 4068, 4072, 3315, 1808, 1889, 1810,
    1905, 1812, 2539, 1813, 2570, 1814, 2573, 1815, 2540, 1816, 1835, 1818, 4666, 4568, 4677,
    4590, 1820, 5079, 4811, 4400, 4525, 1822, 1882, 1824, 2798, 5087, 4210, 4560, 4200, 1827,
    4053, 4594, 1829, 2964, 4021, 2873, 2966, 5093, 3265, 2282, 2829, 1834, 1884, 1836, 4303,
    4809, 1838, 3635, 5103, 1840, 5106, 4614, 4636, 4548, 1842, 5110, 3524, 3713, 1848, 1874,
    1850, 4920, 1852, 5114, 5115, 4434, 4330, 1855, 2225, 5119, 4889, 1858, 1859, 4258, 5125,
    2266, 1861, 2865, 4990, 5128, 5130, 1863, 2760, 2210, 4326, 3739, 1867, 2336, 1869, 5137,
    4755, 4367, 1871, 5073, 5140, 4199, 4635, 1876, 3850, 4178, 3858, 4885, 1878, 4055, 4046,
    1880, 4102, 5147, 3412, 5148, 3176, 4193, 2370, 4339, 1890, 1899, 1891, 4631, 5152, 4544,
    5153, 1893, 5155, 5157, 4624, 1895, 5158, 5159, 1897, 2292, 5161, 1901, 5163, 5164, 5166,
    5167, 1903, 5168, 5169, 3381, 5172, 1907, 3785, 5176, 1909, 5178, 3627, 1911, 2228, 4198,
    5181, 5182, 1914, 2170, 1915, 2646, 1916, 2637, 1917, 2632, 1919, 2617, 1921, 2604, 1922,
    2596, 1923, 2591, 1924, 2583, 1925, 2575, 1927, 2558, 1929, 2543, 1931, 3933, 1932, 3793,
    1933, 3796, 2079, 1936, 1937, 4528, 1938, 4531, 1939, 4637, 1941, 1943, 4539, 1944, 4627,
    1946, 3931, 1947, 3797, 3928, 1950, 2416, 1951, 2453, 1952, 2456, 1953, 2417, 1955, 2029,
    1957, 2042, 1959, 2025, 4030, 3979, 1961, 5222, 2193, 4211, 1963, 4773, 3119, 3124, 2404,
    1965, 3942, 3997, 4054, 1968, 1973, 1969, 3974, 3838, 3988, 3866, 1971, 4942, 5231, 3732,
    3743, 1974, 2027, 1975, 3433, 1977, 4930, 4418, 4287, 1979, 3337, 5243, 4509, 1981, 4006,
    5247, 3961, 3801, 2233, 2771, 5248, 3584, 1986, 2066, 1987, 2061, 1988, 2084, 1989, 2076,
    1990, 2454, 1991, 2415, 1992, 2418, 1993, 1994, 2016, 1995, 2057, 3844, 2910, 3940, 1998,
    2000, 5262, 5264, 5265, 4470, 2003, 2056, 2004, 2009, 2005, 4824, 3991, 2007, 5040, 2822,
    2010, 2059, 2011, 4793, 4540, 3536, 4730, 2013, 4061, 5273, 2015, 2058, 5274, 5276, 2020,
    5278, 2927, 3960, 4541, 4508, 2028, 2051, 2030, 5282, 3810, 5284, 2032, 5286, 3790, 5074,
    3921, 2034, 5287, 2036, 2224, 5288, 5289, 4184, 2866, 5290, 4375, 3025, 2043, 5026, 3427,
    2045, 5296, 4155, 3919, 5297, 5299, 2048, 2831, 4381, 2052, 5302, 5303, 5304, 5306, 2054,
    5307, 5308, 5309, 3669, 2060, 2062, 4869, 2371, 5108, 5312, 2064, 2730, 5314, 2067, 2075,
    2068, 5317, 5318, 4308, 2070, 4851, 2072, 4967, 5322, 4428, 2077, 4385, 4333, 4956, 4650,
    2080, 5327, 4369, 3642, 2082, 2086, 4154, 5330, 2088, 2937, 2090, 5332, 5139, 3802, 4380,
    2093, 2096, 2407, 4433, 4545, 5335, 2098, 5336, 3035, 5012, 2101, 5338, 3690, 2103, 3626,
    5341, 5342, 3683, 2106, 5343, 2109, 4595, 4299, 4253, 5345, 2111, 2955, 5089, 4283, 2113,
    3435, 4940, 3287, 2118, 5203, 5348, 2120, 5300, 5214, 2122, 3436, 4960, 5350, 3752, 3680,
    3630, 5352, 5354, 5113, 3663, 4488, 5143, 4236, 3156, 4288, 5358, 2735, 5360, 3387, 3664,
    2338, 5363, 5364, 5004, 2920, 3382, 4875, 3529, 5368, 5370, 3723, 3558, 5372, 4858, 5374,
    5375, 5376, 2895, 3115, 5378, 5092, 5380, 2378, 4953, 5382, 3481, 3204, 3203, 3483, 3500,
    3184, 2175, 2766, 4846, 3399, 5179, 5384, 4274, 4439, 5387, 3333, 3407, 4992, 5390, 4906,
    5392, 3107, 4359, 5394, 5251, 2171, 2631, 3538, 5396, 2173, 5397, 2174, 2812, 2815, 2176,
    4890, 2178, 2820, 3110, 5403, 2654, 2182, 4267, 2183, 4270, 2184, 4971, 5407, 3409, 3147,
    3118, 5249, 5409, 2190, 5410, 2191, 3289, 5412, 3984, 2195, 5413, 2196, 5414, 5418, 5018,
    2199, 3403, 2200, 5421, 2201, 5423, 2202, 5424, 5395, 2656, 5402, 2205, 2206, 5315, 5200,
    2208, 5426, 2209, 5429, 5134, 4959, 2212, 5432, 2213, 4324, 5393, 5019, 2216, 5433, 2217,
    5198, 2218, 5435, 3401, 5417, 2324, 4318, 4426, 2222, 4265, 2223, 4447, 4191, 4263, 4893,
    2227, 5440, 2229, 4273, 4190, 2231, 4969, 2232, 4279, 4281, 2234, 4552, 4438, 4593, 5446,
    4840, 4939, 4453, 4410, 5448, 5450, 3355, 5452, 5454, 4366, 2311, 3181, 3186, 3498, 3206,
    3479, 4411, 4384, 2941, 3420, 3078, 5456, 5457, 3159, 2901, 2986, 3913, 2253, 4341, 2254,
    5460, 2255, 4977, 2984, 4975, 2257, 5461, 2258, 2259, 5465, 2260, 5467, 4524, 4364, 5471,
    5473, 3518, 3537, 2265, 5060, 5062, 2268, 4725, 2269, 4733, 5049, 2271, 3535, 2272, 5476,
    4543, 5173, 2276, 5039, 2279, 5043, 2280, 2283, 5162, 4254, 4269, 4723, 5044, 2902, 3559,
    2287, 5480, 2288, 3620, 5482, 2290, 2291, 5160, 3530, 5472, 2294, 4848, 2295, 2296, 3557,
    2297, 4845, 5470, 3599, 2299, 5488, 2300, 2301, 5490, 5149, 3083, 3167, 3411, 2305, 2307,
    5389, 3517, 2309, 4993, 5047, 2312, 5494, 5065, 2314, 5497, 2316, 5498, 2317, 5499, 2318,
    5455, 3152, 3586, 3531, 2322, 3290, 2323, 5503, 5388, 2326, 3255, 2328, 4912, 2329, 3256,
    4910, 4826, 2331, 3406, 2332, 3294, 2333, 3293, 2334, 3611, 5508, 2337, 2339, 2938, 5386,
    2341, 3297, 2342, 4441, 2343, 3298, 5385, 4827, 2345, 2346, 5513, 2347, 5514, 2348, 2942,
    5383, 5174, 2351, 5515, 2352, 2353, 4196, 2354, 5067, 2356, 4272, 2357, 5521, 2359, 5522,
    5059, 3172, 2362, 3111, 5408, 4100, 2369, 5228, 5077, 3126, 5391, 4461, 3098, 5526, 5449,
    2375, 4412, 2376, 4879, 2377, 4878, 3631, 5447, 2826, 2380, 5528, 2381, 5530, 4464, 3633,
    2384, 5532, 2385, 5533, 4510, 4425, 2387, 5534, 3132, 4596, 3053, 3651, 2391, 5538, 2392,
    5540, 2393, 5542, 2394, 5543, 4427, 3051, 2396, 5544, 2397, 4937, 2398, 2399, 3650, 4553,
    4996, 2401, 4440, 2402, 5547, 4561, 4429, 5014, 5548, 3296, 2409, 5016, 2412, 4995, 2413,
    4563, 2414, 4591, 2419, 2421, 5549, 3935, 5031, 2805, 2423, 2425, 4581, 5553, 2828, 2428,
    2436, 2429, 3840, 3637, 2431, 4017, 4854, 2434, 4088, 5556, 3803, 5557, 5213, 2439, 5559,
    5560, 2441, 4514, 2443, 4493, 4874, 2447, 3781, 4482, 5563, 2449, 5565, 5566, 2451, 3757,
    5527, 5301, 4224, 2457, 2471, 2458, 5569, 5122, 4481, 4489, 2460, 5570, 3618, 3724, 2463,
    5574, 2845, 2466, 4575, 5483, 2468, 2472, 3429, 2474, 2476, 4598, 5211, 3800, 4492, 2478,
    5582, 4336, 4517, 2480, 2504, 2762, 2880, 2484, 4710, 3659, 4817, 5586, 2490, 2497, 2491,
    3371, 5588, 3896, 2493, 3834, 2933, 3965, 3836, 2495, 4092, 3905, 3451, 3655, 2499, 5590,
    2501, 3910, 5591, 3561, 2506, 3328, 2940, 5595, 2508, 5596, 5597, 3340, 3266, 2515, 2524,
    2516, 3791, 4713, 4473, 4705, 2518, 5603, 5605, 2846, 2520, 5464, 5428, 2522, 4843, 2525,
    5610, 5611, 5613, 5481, 2527, 4798, 4735, 4268, 4728, 2531, 3839, 4702, 2533, 5266, 3010,
    3015, 3881, 2535, 4819, 3037, 3271, 4736, 4683, 5618, 2545, 5339, 3288, 2547, 5001, 4898,
    2549, 3952, 5621, 3945, 2552, 2557, 2553, 5033, 5622, 3773, 3783, 2555, 2836, 5624, 4498,
    3281, 2559, 2561, 2803, 3639, 2563, 3872, 5630, 3750, 2565, 5070, 3992, 3779, 4005, 4823,
    4927, 5632, 2971, 2574, 2597, 2576, 4981, 4763, 2578, 2580, 5636, 4785, 5637, 3745, 2584,
    2585, 4536, 5638, 5256, 2587, 5641, 2592, 5606, 4477, 4346, 2594, 5185, 5463, 2598, 5643,
    5645, 2600, 5430, 4988, 3778, 3749, 2603, 2626, 2605, 5649, 5651, 2607, 4127, 4634, 4113,
    3753, 2609, 2611, 4816, 5399, 5656, 4957, 2618, 3162, 4301, 3164, 2620, 4111, 3902, 3343,
    3884, 4166, 2623, 3592, 2627, 5415, 5663, 5504, 5665, 2629, 4167, 4074, 4159, 4070, 2633,
    4564, 4667, 4555, 2635, 3898, 5667, 2638, 2645, 2639, 5668, 4132, 2890, 5670, 2647, 3520,
    2863, 5420, 5468, 3563, 2652, 5675, 4121, 5589, 5676, 3019, 3440, 5678, 5662, 3388, 5680,
    3421, 3366, 5681, 5485, 3441, 5323, 3770, 5516, 5685, 4978, 5687, 4457, 5441, 2974, 5207,
    5689, 3672, 5442, 5691, 3353, 4495, 2682, 5484, 3425, 3364, 5692, 2684, 2686, 5693, 2690,
    2692, 5190, 3173, 2694, 4309, 2874, 5695, 3920, 2696, 4994, 2699, 4899, 3658, 4474, 5469,
    2701, 2703, 5225, 3101, 2705, 4407, 3996, 5699, 4014, 2708, 3487, 2913, 3199, 3489, 5451,
    3560, 4245, 5453, 4179, 4294, 3191, 3494, 4314, 3971, 5671, 3989, 4295, 4256, 5701, 5703,
    4243, 3729, 5705, 5707, 2724, 2725, 4157, 3318, 3330, 2727, 4998, 5270, 5294, 3916, 5260,
    4172, 2737, 4443, 2738, 5512, 2739, 3316, 5436, 2982, 3008, 5598, 3081, 2743, 4186, 2745,
    4862, 2746, 5710, 4860, 3079, 2748, 2749, 5711, 2750, 5713, 2751, 5714, 4445, 4174, 4997,
    4163, 5545, 3282, 2755, 2756, 3356, 2758, 2759, 5715, 5133, 5706, 2763, 5716, 2764, 5523,
    5704, 3334, 2767, 4925, 2768, 4924, 2769, 3354, 2770, 2772, 5258, 2775, 4313, 5718, 4275,
    5719, 5202, 4839, 5721, 3496, 3189, 3194, 3493, 2856, 5379, 5381, 4880, 3706, 4923, 3491,
    3197, 3049, 3695, 5094, 2961, 4619, 2799, 2800, 5722, 5194, 5723, 5627, 2804, 3692, 5550,
    2806, 5725, 4249, 5036, 5727, 2948, 5492, 5459, 3317, 2813, 5729, 2814, 5731, 2817, 2818,
    4444, 4970, 2950, 2905, 5525, 2827, 4891, 2832, 5732, 5511, 5730, 5623, 2837, 5734, 2838,
    5117, 5726, 2840, 5735, 2842, 2843, 5000, 5575, 4422, 5728, 3041, 2954, 4289, 5702, 2850,
    5416, 2852, 5738, 5700, 5458, 2854, 4954, 2855, 4297, 2857, 4951, 4319, 3712, 3999, 3048,
    3422, 2862, 5673, 2864, 5739, 5127, 4790, 2869, 5076, 4329, 3978, 5201, 3969, 2877, 5406,
    2878, 4316, 2879, 3609, 3987, 2881, 3972, 3607, 5619, 2884, 2885, 5184, 3394, 3150, 2888,
    5741, 2889, 5742, 5495, 2891, 5743, 3148, 2893, 4821, 2894, 5745, 3445, 2896, 3018, 5709,
    2903, 4828, 2906, 5746, 3000, 5291, 3696, 3031, 3331, 5720, 5259, 2911, 5204, 2912, 5748,
    2915, 2916, 2918, 2919, 5751, 5366, 5293, 5478, 2922, 2923, 5752, 2924, 2925, 4379, 5279,
    2928, 5754, 2929, 5717, 4315, 2934, 3606, 5546, 2936, 4913, 5405, 5593, 2943, 5755, 2951,
    5129, 4392, 5023, 3367, 2959, 5594, 5759, 5761, 5762, 2968, 5218, 3410, 2972, 5046, 5123,
    5765, 3766, 2976, 4750, 5136, 4740, 4825, 5269, 4041, 4063, 4758, 5767, 4203, 5209, 2990,
    5223, 2993, 5131, 5236, 2995, 4497, 3646, 3342, 3001, 4197, 5773, 3004, 4008, 4533, 5257,
    4003, 3006, 5776, 4905, 3012, 5655, 5747, 5779, 4311, 5782, 3329, 3021, 3640, 4463, 4577,
    5552, 3023, 3551, 3277, 3028, 5568, 5310, 3033, 5050, 4304, 5126, 5786, 3415, 3042, 5253,
    4117, 4115, 3934, 3044, 5479, 4403, 3046, 5790, 3351, 5792, 5794, 5795, 3821, 4673, 4861,
    3895, 3057, 5024, 5653, 3059, 4656, 4948, 3061, 5661, 5091, 3071, 3073, 3725, 3448, 3075,
    5101, 5132, 3808, 5042, 4049, 4795, 4397, 5802, 5003, 3086, 4378, 3088, 4838, 5806, 3090,
    3924, 4612, 4610, 5030, 3562, 3679, 3103, 5811, 5674, 3108, 4220, 5097, 3113, 5329, 4152,
    4911, 4139, 4471, 5813, 5814, 5816, 3122, 3694, 5083, 3128, 4205, 5531, 3130, 4707, 5028,
    4537, 4703, 3133, 5821, 3641, 3139, 3817, 4883, 3141, 5599, 5171, 5445, 3144, 5824, 5825,
    5827, 3908, 4660, 3894, 4974, 3154, 4280, 3416, 5640, 3949, 3522, 5829, 3160, 5493, 5607,
    4435, 5833, 3169, 4417, 5263, 5837, 3177, 5170, 5602, 3449, 4025, 5838, 4170, 3917, 4562,
    4557, 3727, 4688, 4655, 5237, 5840, 5771, 4478, 4887, 5008, 4982, 5842, 5844, 5195, 5784,
    5846, 3527, 5848, 4168, 5658, 3845, 3687, 5850, 5852, 5854, 5855, 3665, 5856, 4625, 5858,
    3423, 5860, 4244, 4386, 5862, 4835, 4873, 5518, 4337, 5866, 5868, 3980, 3252, 3601, 3257,
    3982, 3973, 3263, 3264, 3267, 5874, 3990, 3269, 4871, 3995, 4664, 3275, 5875, 3955, 5867,
    5626, 3283, 3966, 5873, 3378, 3292, 5879, 4024, 5235, 4084, 5883, 5885, 4847, 5887, 5889,
    3705, 4877, 5891, 4720, 3670, 3320, 5892, 3321, 3322, 3323, 5208, 5535, 5897, 4902, 3736,
    5298, 5758, 5215, 5796, 3338, 4695, 3341, 5292, 3735, 3671, 3347, 3348, 4946, 5899, 3350,
    5791, 4908, 5896, 4246, 5895, 4934, 3358, 5466, 3360, 5864, 4682, 4516, 5756, 3368, 3369,
    3372, 5902, 3373, 5890, 4909, 3376, 3377, 5906, 5863, 3380, 4347, 3383, 4803, 4345, 4225,
    3385, 3386, 5684, 3392, 4822, 4226, 3396, 4781, 3398, 5861, 5797, 3402, 3404, 3759, 5737,
    4020, 3414, 5865, 5884, 4296, 4952, 5882, 5541, 3426, 5912, 5578, 4090, 3432, 5238, 3985,
    5346, 5349, 3437, 5915, 4037, 5677, 4391, 3442, 3443, 4963, 3964, 4091, 3446, 5917, 5224,
    3812, 3452, 3453, 5226, 4774, 5918, 4738, 4737, 5920, 4853, 5921, 5900, 5834, 5017, 5923,
    5880, 3719, 5615, 5881, 5925, 3887, 4501, 3815, 4542, 3647, 5926, 4769, 4966, 5187, 5798,
    5100, 5928, 5886, 4926, 5888, 4766, 4779, 5095, 5930, 5932, 5002, 5934, 5536, 4833, 4484,
    5823, 5066, 5809, 5180, 5878, 4104, 3540, 3541, 5938, 3542, 3543, 4520, 5177, 5916, 4813,
    3547, 3549, 3550, 5935, 3554, 5529, 3555, 5933, 4836, 4365, 4109, 3564, 5939, 3878, 5744,
    3632, 5857, 5859, 4180, 4363, 4617, 3585, 4592, 5941, 4599, 3590, 4987, 3827, 3764, 5943,
    5901, 3598, 3674, 5910, 3612, 5945, 4583, 3616, 5946, 5942, 5571, 3619, 5944, 5931, 5340,
    3628, 5948, 5929, 4413, 5102, 4784, 5628, 4764, 3643, 5090, 3746, 4556, 3649, 5871, 4022,
    3653, 5088, 3656, 4616, 5697, 5585, 4775, 3661, 5950, 4217, 5361, 4895, 3666, 5937, 4227,
    3675, 5951, 3870, 5940, 5808, 3751, 3681, 3685, 3686, 5953, 5822, 5898, 3689, 3691, 5437,
    5373, 3700, 4936, 4348, 4087, 3707, 3711, 5111, 4328, 3717, 4647, 3720, 3722, 4402, 5572,
    5839, 3730, 5232, 3738, 3742, 5233, 3748, 5631, 3754, 5788, 3755, 5787, 3758, 3762, 3763,
    5777, 3765, 5783, 3767, 3769, 5639, 5683, 3771, 3772, 3776, 5775, 3777, 5774, 3780, 5757,
    3782, 5328, 5331, 5045, 3787, 5763, 3789, 4632, 3792, 4633, 3804, 4083, 3806, 3807, 4067,
    3809, 3811, 4023, 3813, 4108, 3816, 3883, 3820, 3828, 3822, 4259, 5836, 5740, 5500, 3832,
    3868, 5913, 4620, 4726, 3907, 3841, 3857, 3846, 5974, 3891, 3852, 3854, 5334, 4697, 3856,
    3892, 5517, 4931, 3860, 5025, 3862, 3864, 4469, 3873, 5509, 5785, 3875, 5081, 5979, 3879,
    3885, 5733, 3889, 4757, 4945, 5981, 5982, 3903, 5817, 5807, 4229, 5985, 5770, 4158, 3922,
    4120, 3923, 4112, 3925, 4532, 3926, 4535, 3939, 4038, 4040, 4709, 4669, 3947, 3953, 5439,
    5966, 5098, 3956, 5109, 3958, 4687, 5583, 3962, 4010, 3963, 4002, 5011, 5907, 3976, 5924,
    4623, 5991, 3993, 5780, 4001, 5992, 4207, 5818, 5009, 5189, 4012, 4921, 4015, 5650, 4692,
    5633, 4028, 4454, 5993, 4031, 4033, 4035, 5994, 5749, 5977, 4044, 5831, 4466, 4475, 5438,
    4075, 5955, 5996, 4661, 4566, 4077, 4079, 4085, 5135, 5724, 5112, 5999, 4351, 4094, 4096,
    4606, 4850, 4648, 4133, 4868, 4122, 5242, 4124, 6000, 4128, 4130, 4134, 5107, 5241, 4491,
    4140, 5604, 4142, 4496, 4144, 4146, 4150, 4609, 4797, 4161, 4164, 5144, 4181, 5425, 4185,
    4863, 4194, 5853, 5772, 5141, 4202, 6004, 5768, 5422, 4208, 4714, 4214, 5967, 4866, 4805,
    4218, 4933, 5983, 4230, 4231, 4233, 5660, 4234, 4237, 5191, 4240, 5851, 5849, 4248, 5958,
    4250, 5845, 4257, 5971, 4264, 5973, 4277, 4465, 4972, 5847, 4284, 4285, 4808, 4865, 5356,
    4290, 6009, 5843, 5486, 4390, 5344, 4300, 5539, 4991, 5007, 4962, 4306, 5319, 5694, 4310,
    5962, 5617, 5474, 4964, 4331, 5614, 4722, 4340, 5986, 4804, 4350, 5960, 4352, 4353, 4356,
    4357, 4360, 5980, 4361, 4640, 4374, 4487, 5922, 5804, 5333, 5325, 5362, 4388, 4976, 4395,
    5800, 4398, 6011, 5712, 4401, 5487, 5698, 4408, 5491, 5908, 5968, 4896, 5206, 5240, 4901,
    5577, 4504, 5573, 5799, 4431, 5116, 4436, 6012, 4448, 5972, 4644, 4455, 6013, 4724, 5919,
    4458, 4459, 4892, 5830, 4468, 5551, 4472, 5835, 5820, 4476, 4479, 4480, 5138, 4483, 5810,
    4485, 5355, 4490, 5805, 5625, 5914, 4507, 5244, 4512, 4515, 4523, 5082, 4546, 4701, 4547,
    4696, 4550, 4608, 4551, 4603, 5510, 4570, 4579, 4584, 5193, 4586, 4588, 4600, 4604, 4621,
    4791, 4780, 4626, 4767, 4645, 4672, 5753, 4653, 4657, 4684, 4659, 4662, 4665, 4678, 4675,
    6010, 4680, 4685, 5431, 4814, 4699, 4716, 6027, 4742, 4744, 4747, 5316, 4752, 4760, 5554,
    4771, 5961, 5496, 4776, 4782, 5419, 4788, 4800, 4806, 5371, 5096, 5099, 4810, 5969, 5080,
    5377, 4818, 6032, 4829, 5989, 4830, 4831, 5616, 5365, 4842, 5609, 5369, 5367, 5894, 5357,
    4855, 5964, 4856, 4857, 6033, 5359, 5337, 4872, 5562, 5353, 5351, 4882, 5145, 4886, 5841,
    4888, 6001, 5120, 5086, 5146, 5634, 5657, 4914, 4915, 6025, 4916, 4918, 5537, 5911, 5690,
    4928, 5234, 5686, 5239, 4941, 6034, 5229, 4943, 6017, 5688, 5682, 4949, 5506, 5326, 5005,
    5221, 5927, 5320, 4968, 6029, 4979, 6035, 5505, 4983, 4984, 6015, 5659, 5679, 4986, 5647,
    5696, 4999, 5803, 5006, 5601, 5010, 5600, 5013, 5584, 5015, 5592, 5020, 5580, 5021, 5579,
    5022, 5555, 5567, 5561, 5027, 5254, 5029, 5255, 5032, 5142, 5034, 5035, 5037, 5150, 5038,
    5057, 5949, 5903, 5295, 6037, 5048, 5061, 5054, 5401, 5434, 5311, 5063, 5646, 5477, 5068,
    5154, 5069, 5151, 5071, 5210, 5072, 5212, 5075, 5121, 5078, 5502, 5524, 5084, 5085, 5105,
    5250, 5104, 5648, 5280, 5118, 6039, 5501, 6038, 5124, 5183, 5188, 5411, 5261, 5489, 5156,
    5197, 5199, 5165, 5246, 5175, 5475, 5186, 5672, 5652, 5192, 5635, 5196, 5404, 5347, 5205,
    5769, 5216, 5285, 5217, 5281, 5219, 5245, 5220, 5400, 5227, 5230, 5324, 5252, 5271, 5267,
    5277, 5268, 5272, 5275, 5736, 5283, 6041, 5305, 5313, 5750, 5321, 6030, 5978, 6007, 5987,
    5581, 6024, 5520, 5904, 5612, 6002, 5778, 5893, 5642, 5564, 5654, 5760, 5984, 5398, 5666,
    5587, 6014, 6006, 6043, 5965, 5427, 5947, 5629, 5995, 5988, 5443, 5444, 5970, 5620, 6021,
    5462, 5766, 5957, 5789, 5576, 5952, 5876, 5507, 6022, 5870, 5519, 6016, 5819, 5793, 6019,
    5963, 5558, 5905, 5976, 6026, 5872, 5608, 5877, 5644, 5664, 5669, 5909, 5832, 5998, 5815,
    6023, 6003, 6028, 5990, 5708, 5959, 6018, 5801, 6042, 5936, 5954, 5826, 6020, 5869, 5764,
    5781, 5812, 5828, 6005, 6040, 6036, 5997, 6008, 6031, 5956, 5975, 6047, 6044, 6045, 6046]

/-- Cayley-table column for left multiplication by `b⁻¹`: `nextBI[i]` is the index of
the element `b⁻¹ · evalWord (word i)`. -/
def nextBI : Array Nat :=
  #[4, 7, 0, 11, 2, 15, 1, 6, 22, 24, 3, 10, 31, 33, 5, 14, 40, 42, 45, 47, 49, 8, 21, 9, 23,
    60, 62, 65, 67, 69, 12, 30, 13, 32, 80, 82, 85, 87, 89, 16, 39, 17, 41, 99, 18, 44, 19, 46,
    20, 48, 114, 116, 119, 121, 124, 126, 129, 131, 133, 25, 59, 26, 61, 143, 27, 64, 28, 66,
    29, 68, 158, 160, 163, 165, 168, 170, 173, 175, 177, 34, 79, 35, 81, 187, 36, 84, 37, 86,
    38, 88, 202, 204, 207, 209, 212, 214, 217, 219, 43, 98, 226, 228, 231, 233, 236, 238, 241,
    243, 245, 247, 250, 252, 254, 50, 113, 51, 115, 264, 52, 118, 53, 120, 273, 54, 123, 55,
    125, 283, 56, 128, 57, 130, 58, 132, 296, 298, 301, 302, 305, 307, 310, 312, 63, 142, 317,
    319, 322, 324, 327, 329, 332, 334, 337, 339, 341, 343, 345, 70, 157, 71, 159, 354, 72, 162,
    73, 164, 364, 74, 167, 75, 169, 373, 76, 172, 77, 174, 78, 176, 386, 388, 391, 393, 396,
    398, 401, 403, 83, 186, 408, 410, 413, 415, 418, 420, 423, 425, 427, 429, 432, 434, 436, 90,
    201, 91, 203, 446, 92, 206, 93, 208, 455, 94, 211, 95, 213, 465, 96, 216, 97, 218, 475, 477,
    479, 481, 483, 100, 225, 101, 227, 492, 102, 230, 103, 232, 502, 104, 235, 105, 237, 511,
    106, 240, 107, 242, 108, 244, 109, 246, 335, 110, 249, 111, 251, 112, 253, 543, 545, 548,
    550, 553, 555, 557, 559, 117, 263, 566, 568, 571, 573, 575, 578, 580, 122, 272, 585, 587,
    590, 591, 594, 595, 598, 600, 127, 282, 605, 137, 608, 610, 613, 615, 618, 620, 623, 625,
    627, 134, 295, 135, 297, 637, 136, 300, 285, 645, 138, 304, 139, 306, 655, 140, 309, 141,
    311, 665, 667, 669, 144, 316, 145, 318, 678, 146, 321, 147, 323, 688, 148, 326, 149, 328,
    697, 150, 331, 151, 333, 528, 152, 336, 153, 338, 154, 340, 155, 342, 156, 344, 727, 729,
    732, 734, 737, 739, 741, 161, 353, 748, 750, 651, 754, 261, 757, 760, 762, 166, 363, 767,
    769, 771, 774, 776, 779, 781, 171, 372, 786, 277, 789, 791, 794, 796, 799, 437, 803, 805,
    807, 178, 385, 179, 387, 817, 180, 390, 181, 392, 826, 182, 395, 183, 397, 836, 184, 400,
    185, 402, 846, 848, 850, 188, 407, 189, 409, 859, 190, 412, 191, 414, 869, 192, 417, 193,
    419, 878, 194, 422, 195, 424, 196, 426, 197, 428, 473, 198, 431, 199, 433, 200, 435, 800,
    910, 913, 915, 918, 920, 922, 924, 205, 445, 931, 933, 936, 938, 940, 943, 945, 210, 454,
    950, 952, 955, 956, 959, 960, 963, 965, 215, 464, 969, 972, 974, 977, 979, 982, 984, 895,
    220, 474, 221, 476, 222, 478, 223, 480, 224, 482, 1007, 1009, 1012, 1014, 1017, 1019, 1021,
    229, 491, 1028, 1030, 279, 1033, 443, 1036, 1039, 1041, 234, 501, 1046, 1048, 1050, 1053,
    1055, 1058, 1060, 239, 510, 1065, 459, 1068, 1070, 1073, 1075, 1078, 808, 1082, 1084, 1087,
    1089, 1092, 1094, 1097, 1099, 248, 1102, 1104, 1106, 1108, 1110, 1112, 1114, 1116, 1118,
    1120, 1122, 1124, 1126, 255, 542, 256, 544, 1135, 257, 547, 258, 549, 1144, 259, 552, 260,
    554, 1153, 359, 262, 558, 1161, 1163, 1165, 1167, 1169, 265, 565, 266, 567, 1177, 267, 570,
    268, 572, 269, 574, 1190, 270, 577, 271, 579, 1200, 1202, 1204, 274, 584, 275, 586, 1214,
    276, 589, 375, 1222, 278, 593, 495, 1230, 280, 597, 281, 599, 1239, 1241, 1243, 284, 604,
    1248, 286, 607, 287, 609, 1258, 288, 612, 289, 614, 1265, 290, 617, 291, 619, 663, 292, 622,
    293, 624, 294, 626, 1276, 1278, 1281, 1283, 1286, 1288, 1290, 1292, 299, 636, 1172, 1298,
    1301, 1303, 1306, 1308, 303, 644, 1311, 1313, 1316, 1317, 1320, 752, 1323, 1325, 308, 654,
    1175, 1329, 1331, 1188, 1263, 1337, 1339, 1100, 313, 664, 314, 666, 315, 668, 1344, 1346,
    1349, 1351, 1354, 1356, 1358, 320, 677, 1363, 1365, 832, 1369, 634, 1372, 1209, 1376, 325,
    687, 1379, 1381, 1383, 1386, 1388, 1391, 1393, 330, 696, 1396, 649, 1399, 1401, 1404, 1406,
    1408, 1410, 1412, 1414, 1416, 1418, 1420, 1422, 1424, 1427, 1429, 1432, 1434, 1437, 1439,
    1442, 1444, 1446, 1448, 1450, 1452, 1454, 346, 726, 347, 728, 1463, 348, 731, 349, 733,
    1469, 350, 736, 351, 738, 352, 740, 1482, 1484, 1486, 1488, 1490, 355, 747, 356, 749, 1499,
    357, 358, 753, 1507, 360, 756, 1513, 361, 759, 362, 761, 1522, 1524, 1526, 365, 766, 366,
    768, 367, 770, 1539, 368, 773, 369, 775, 1548, 370, 778, 371, 780, 1554, 1556, 1558, 374,
    785, 1564, 376, 788, 377, 790, 1573, 378, 793, 379, 795, 1582, 380, 798, 381, 844, 382, 802,
    383, 804, 384, 806, 1079, 1594, 1597, 1599, 1602, 1604, 1606, 1608, 389, 816, 1613, 1615,
    1618, 1620, 1622, 1625, 1627, 394, 825, 1630, 1632, 1635, 1636, 1639, 1367, 1642, 1644, 399,
    835, 1646, 1649, 1651, 1654, 1656, 1659, 1661, 1589, 404, 845, 405, 847, 406, 849, 1666,
    1668, 1671, 1673, 1676, 1678, 1680, 411, 858, 1685, 1687, 461, 1690, 814, 1693, 1696, 1698,
    416, 868, 1701, 1703, 1705, 1708, 1710, 1713, 1715, 421, 877, 1718, 830, 1721, 1723, 1726,
    1728, 1731, 628, 1734, 1736, 1739, 1741, 1744, 1746, 1749, 1751, 430, 1753, 1755, 1757,
    1759, 1761, 1763, 1765, 1767, 1769, 1771, 1773, 1775, 1777, 438, 909, 1783, 439, 912, 440,
    914, 1792, 441, 917, 442, 919, 1801, 497, 444, 923, 1809, 1811, 1813, 1815, 1817, 447, 930,
    448, 932, 1823, 449, 935, 450, 937, 451, 939, 1835, 452, 942, 453, 944, 1845, 1847, 1849,
    456, 949, 457, 951, 1858, 458, 954, 513, 1866, 460, 958, 862, 1874, 462, 962, 463, 964,
    1883, 1885, 466, 968, 1890, 467, 971, 468, 973, 1900, 469, 976, 470, 978, 1906, 471, 981,
    472, 983, 1915, 1917, 1919, 1921, 1923, 1925, 1927, 1929, 1932, 1934, 1937, 1939, 1942,
    1944, 1947, 1949, 1951, 1953, 1955, 1957, 1959, 484, 1006, 485, 1008, 1968, 486, 1011, 487,
    1013, 1974, 488, 1016, 489, 1018, 490, 1020, 1987, 1989, 1991, 1993, 1995, 493, 1027, 494,
    1029, 2004, 496, 1032, 2010, 498, 1035, 2016, 499, 1038, 500, 1040, 2025, 2027, 2029, 503,
    1045, 504, 1047, 505, 1049, 2042, 506, 1052, 507, 1054, 2051, 508, 1057, 509, 1059, 2057,
    2059, 2061, 512, 1064, 2067, 514, 1067, 515, 1069, 2076, 516, 1072, 517, 1074, 2085, 518,
    1077, 519, 1430, 520, 1081, 521, 1083, 2100, 522, 1086, 523, 1088, 1440, 524, 1091, 525,
    1093, 2116, 526, 1096, 527, 1098, 621, 529, 1101, 530, 1103, 531, 1105, 532, 1107, 533,
    1109, 534, 1111, 535, 1113, 536, 1115, 537, 1117, 538, 1119, 539, 1121, 540, 1123, 541,
    1125, 2171, 2174, 2176, 2178, 2180, 2182, 2184, 546, 1134, 1493, 1561, 2194, 2196, 1576,
    2200, 2202, 551, 1143, 2206, 2209, 2210, 2212, 2213, 2216, 2218, 556, 1152, 2223, 2225,
    2228, 1579, 2232, 2234, 560, 1160, 561, 1162, 562, 1164, 563, 1166, 564, 1168, 2253, 2255,
    1296, 2258, 2260, 1326, 569, 1176, 2265, 2267, 2269, 1132, 2272, 2275, 2277, 2279, 2281,
    2283, 1333, 576, 1189, 2288, 1147, 2291, 1471, 2295, 2297, 2300, 2093, 581, 1199, 582, 1201,
    583, 1203, 2305, 2307, 2310, 2312, 1374, 2314, 2316, 2318, 588, 1213, 1494, 2324, 2327,
    2329, 2332, 2334, 592, 1221, 2337, 2339, 2342, 2343, 2346, 2348, 596, 1229, 1497, 2352,
    2354, 1511, 1580, 2360, 2362, 601, 1238, 602, 1240, 603, 1242, 2367, 2369, 2371, 606, 1247,
    2376, 2378, 2114, 2382, 1211, 2385, 1531, 2389, 611, 1257, 2392, 2394, 2397, 2399, 1334,
    616, 1264, 2402, 1226, 2405, 2407, 2410, 2412, 2414, 2416, 2418, 2420, 886, 629, 1277, 2428,
    630, 1280, 631, 1282, 2437, 632, 1285, 633, 1287, 2446, 683, 635, 1291, 2454, 2456, 2240,
    638, 639, 1297, 2365, 640, 1300, 641, 1302, 2471, 642, 1305, 643, 1307, 2481, 646, 1310,
    647, 1312, 2490, 648, 1315, 699, 2498, 650, 1319, 2504, 652, 1322, 653, 1324, 656, 2515,
    657, 1328, 658, 1330, 2141, 659, 660, 2530, 661, 1336, 662, 1338, 2539, 2541, 2543, 670,
    1343, 671, 1345, 2552, 672, 1348, 673, 1350, 2558, 674, 1353, 675, 1355, 676, 1357, 2571,
    2573, 2575, 679, 1362, 680, 1364, 2584, 681, 682, 1368, 2591, 684, 1371, 2597, 685, 686,
    1375, 2604, 689, 1378, 690, 1380, 691, 1382, 2617, 692, 1385, 693, 1387, 2626, 694, 1390,
    695, 1392, 2632, 698, 1395, 2638, 700, 1398, 701, 1400, 2646, 702, 1403, 703, 1405, 704,
    1407, 705, 1409, 706, 1411, 707, 1413, 708, 1415, 709, 1417, 710, 1419, 711, 1421, 712,
    1423, 1085, 713, 1426, 714, 1428, 2092, 715, 1431, 716, 1433, 1095, 717, 1436, 718, 1438,
    2108, 719, 1441, 720, 1443, 721, 1445, 722, 1447, 723, 1449, 724, 1451, 725, 1453, 2725,
    2728, 2730, 2733, 2735, 2737, 2739, 730, 1462, 2744, 2746, 2749, 2751, 735, 1468, 2756,
    2292, 2759, 2760, 2763, 2764, 2767, 2769, 2771, 2773, 2775, 742, 1481, 743, 1483, 744, 1485,
    745, 1487, 746, 1489, 2798, 2800, 2190, 2322, 2804, 2806, 2349, 751, 1498, 2813, 2815, 1460,
    2818, 1868, 2822, 755, 1506, 2827, 2829, 2832, 2356, 758, 1512, 2837, 1473, 2441, 2841,
    2843, 1793, 2658, 763, 1521, 764, 1523, 765, 1525, 2850, 2852, 2855, 2857, 2387, 2860, 2862,
    2864, 2866, 2868, 2870, 772, 1538, 2873, 2875, 2878, 2879, 2881, 2884, 2886, 777, 1547,
    2889, 2891, 2894, 2896, 782, 1553, 783, 1555, 784, 1557, 2901, 2903, 2191, 2906, 787, 1563,
    2911, 2913, 2675, 2486, 1533, 2919, 1851, 792, 1572, 2923, 2925, 2197, 2928, 2930, 2229,
    2357, 797, 1581, 2934, 1543, 2937, 2423, 2941, 2943, 801, 2945, 2947, 2949, 809, 1593, 2954,
    810, 1596, 811, 1598, 2962, 812, 1601, 813, 1603, 2971, 864, 815, 1607, 2979, 2981, 2983,
    818, 1612, 819, 1614, 2989, 820, 1617, 821, 1619, 822, 1621, 3000, 823, 1624, 824, 1626,
    3009, 827, 1629, 828, 1631, 3018, 829, 1634, 880, 3026, 831, 1638, 3031, 833, 1641, 834,
    1643, 837, 1645, 3041, 838, 1648, 839, 1650, 3050, 840, 1653, 841, 1655, 3056, 842, 1658,
    843, 1660, 3065, 3067, 3069, 851, 1665, 852, 1667, 3078, 853, 1670, 854, 1672, 3084, 855,
    1675, 856, 1677, 857, 1679, 3095, 3097, 3099, 860, 1684, 861, 1686, 3107, 863, 1689, 3112,
    865, 1692, 3118, 866, 1695, 867, 1697, 3127, 870, 1700, 871, 1702, 872, 1704, 3138, 873,
    1707, 874, 1709, 3147, 875, 1712, 876, 1714, 3153, 879, 1717, 3159, 881, 1720, 882, 1722,
    3168, 883, 1725, 884, 1727, 3176, 885, 1730, 1935, 887, 1733, 888, 1735, 3188, 889, 1738,
    890, 1740, 1945, 891, 1743, 892, 1745, 3202, 893, 1748, 894, 1750, 896, 1752, 897, 1754,
    898, 1756, 899, 1758, 900, 1760, 901, 1762, 902, 1764, 903, 1766, 904, 1768, 905, 1770, 906,
    1772, 907, 1774, 908, 1776, 3252, 2589, 3255, 3257, 911, 1782, 1998, 2064, 3265, 3267, 2079,
    3270, 3272, 916, 1791, 2845, 3276, 3277, 3278, 3279, 3281, 3283, 921, 1800, 3288, 3290,
    3293, 2082, 3297, 3299, 925, 1808, 926, 1810, 927, 1812, 928, 1814, 929, 1816, 3316, 3318,
    3321, 3323, 934, 1822, 3328, 2689, 3331, 1780, 3334, 3337, 3339, 3340, 2569, 3343, 941,
    1834, 3348, 1795, 3350, 1976, 3354, 3356, 3359, 3181, 946, 1844, 947, 1846, 948, 1848, 3364,
    2920, 3367, 3368, 3369, 3371, 3373, 953, 1857, 1999, 3378, 3381, 3383, 3386, 3388, 957,
    1865, 2656, 2820, 3393, 3394, 3397, 3399, 961, 1873, 2002, 3402, 3404, 2014, 2083, 3410,
    3411, 966, 1882, 967, 1884, 2614, 3414, 3416, 970, 1889, 3421, 3423, 3201, 3427, 1855, 3430,
    2034, 3433, 975, 1899, 3436, 3438, 3441, 3443, 980, 1905, 3446, 1870, 2304, 3449, 2105,
    3452, 3454, 985, 1914, 986, 1916, 987, 1918, 988, 1920, 989, 1922, 990, 1924, 991, 1926,
    992, 1928, 1737, 993, 1931, 994, 1933, 3180, 995, 1936, 996, 1938, 1747, 997, 1941, 998,
    1943, 3196, 999, 1946, 1000, 1948, 1001, 1950, 1002, 1952, 1003, 1954, 1004, 1956, 1005,
    1958, 3518, 3521, 3522, 3525, 3527, 3529, 3531, 1010, 1967, 3536, 3538, 3541, 3543, 1015,
    1973, 2474, 3351, 3550, 3551, 3554, 3555, 3558, 3560, 3562, 2167, 3564, 1022, 1986, 1023,
    1988, 1024, 1990, 1025, 1992, 1026, 1994, 2431, 3586, 3263, 3376, 3590, 3592, 2716, 1031,
    2003, 1965, 3599, 3027, 3602, 1034, 2009, 3607, 3609, 3612, 3406, 1037, 2015, 3616, 1978,
    1148, 2094, 3620, 2963, 3455, 1042, 2024, 1043, 2026, 1044, 2028, 3626, 3628, 3631, 3633,
    3432, 2523, 3637, 3639, 3641, 3642, 3644, 1051, 2041, 3646, 2917, 3650, 3651, 3653, 3655,
    2926, 1056, 2050, 3659, 3661, 3664, 3666, 1061, 2056, 1062, 2058, 1063, 2060, 3670, 3672,
    3264, 3675, 1066, 2066, 3680, 2686, 3472, 1210, 2036, 3686, 3011, 1071, 2075, 3690, 3692,
    2245, 3695, 2511, 3294, 3407, 1076, 2084, 3700, 2046, 3702, 1130, 3705, 3707, 1080, 2301,
    3618, 1962, 3711, 3713, 3715, 3717, 1425, 2801, 2823, 3723, 3725, 3451, 1853, 3128, 1090,
    3730, 3732, 3735, 3736, 3738, 2380, 2623, 1435, 3740, 3089, 2443, 2778, 2931, 3749, 3751,
    3753, 3755, 3757, 3759, 3761, 2661, 1149, 3764, 2098, 3766, 3768, 3467, 3771, 3773, 3775,
    3777, 3779, 2524, 3781, 2112, 3566, 3701, 2676, 3786, 3788, 1205, 3790, 3792, 3794, 3796,
    3798, 2505, 3800, 3802, 2701, 3805, 3600, 3614, 2904, 2783, 2967, 3812, 3814, 3563, 3010,
    3817, 1127, 2170, 3821, 1128, 2173, 1129, 2175, 3459, 2089, 1131, 2179, 3833, 1181, 1133,
    2183, 2830, 2795, 3842, 3844, 2684, 1136, 1137, 2463, 1138, 2193, 1139, 2195, 1140, 3857,
    1141, 2199, 1142, 2201, 3867, 3460, 1145, 2205, 2468, 1146, 2208, 1192, 3878, 2019, 2130,
    3884, 1150, 2215, 1151, 2217, 2685, 3893, 3895, 1154, 2222, 1155, 2224, 2794, 1156, 2227,
    1157, 2825, 1158, 2231, 1159, 2233, 3915, 3917, 3919, 3921, 3923, 2457, 3925, 3927, 3929,
    3931, 1788, 3933, 3935, 3937, 3939, 3941, 3943, 1170, 2252, 1171, 2254, 3952, 1173, 2257,
    1174, 2259, 3961, 3963, 3965, 1178, 2264, 1179, 2266, 1180, 2268, 3973, 1182, 2271, 3979,
    1183, 2274, 1184, 2276, 1185, 2278, 1186, 2280, 1187, 2282, 3988, 3990, 3992, 1191, 2287,
    3997, 1193, 2290, 1194, 4002, 1195, 2294, 1196, 2296, 4011, 1197, 2299, 1198, 4018, 4020,
    3448, 2149, 1206, 2306, 4024, 1207, 2309, 1208, 2311, 2966, 2071, 1910, 1253, 1212, 2317,
    4039, 4040, 2782, 1215, 1216, 2323, 2899, 1217, 2326, 1218, 2328, 4054, 1219, 2331, 1220,
    2333, 3613, 1223, 2336, 1224, 2338, 3597, 1225, 2341, 1267, 4075, 1227, 2345, 1228, 2347,
    1231, 4084, 1232, 2351, 1233, 2353, 2702, 1234, 1235, 1912, 1236, 2359, 1237, 2361, 4102,
    1985, 2462, 1244, 2366, 1245, 2368, 1246, 2370, 4108, 4110, 4112, 1249, 2375, 1250, 2377,
    4121, 1251, 1252, 2381, 4127, 1254, 2384, 4133, 1255, 1256, 2388, 4139, 1259, 2391, 1260,
    2393, 4149, 1261, 2396, 1262, 2398, 4158, 1266, 2401, 4164, 1268, 2404, 1269, 2406, 4167,
    1270, 2409, 1271, 2411, 1272, 2413, 1273, 2415, 1274, 2417, 1275, 2419, 4179, 4181, 2938,
    2008, 4184, 4186, 1279, 2427, 2578, 2635, 3584, 4194, 2649, 4197, 4199, 1284, 2436, 4200,
    4203, 4058, 2838, 4205, 3743, 4208, 1289, 2445, 4211, 4034, 4169, 2652, 4218, 4220, 1293,
    2453, 1294, 2455, 1295, 4225, 4227, 3875, 4231, 1299, 3850, 2117, 4234, 2425, 4237, 3872,
    2211, 1304, 2470, 3860, 2440, 3547, 2560, 4244, 4246, 4249, 3493, 1309, 2480, 4253, 4254,
    3855, 4257, 2916, 4258, 4146, 1314, 2489, 2579, 4265, 4268, 4270, 4273, 4275, 1318, 2497,
    2088, 4277, 4280, 4281, 1321, 2503, 2582, 4284, 4130, 2595, 2653, 3890, 3696, 2039, 4290,
    1327, 2514, 4295, 4297, 3484, 4301, 2487, 4304, 2609, 3635, 1332, 4309, 4311, 4314, 4316,
    1335, 2529, 4319, 2502, 4322, 4324, 2707, 4328, 4330, 1340, 2538, 1341, 2540, 1342, 2542,
    4331, 2796, 4334, 2835, 4337, 4339, 4341, 1347, 2551, 4346, 4348, 4351, 4353, 1352, 2557,
    1838, 4135, 4357, 4056, 4360, 4361, 4364, 4366, 4368, 4370, 3341, 1359, 2570, 1360, 2572,
    1361, 2574, 1786, 4375, 4190, 4263, 4379, 4381, 2155, 1366, 2583, 4385, 4386, 2549, 4388,
    3253, 1370, 2590, 4391, 3986, 4395, 4287, 1373, 2596, 4398, 2562, 2697, 4402, 3569, 1377,
    2603, 4407, 4408, 4411, 4413, 4306, 1898, 4416, 4418, 4419, 3412, 2320, 1384, 2616, 3981,
    4423, 4426, 4427, 4429, 3739, 4099, 1389, 2625, 4434, 4436, 4439, 4441, 1394, 2631, 4443,
    4445, 4191, 4448, 1397, 2637, 4453, 2113, 3593, 3014, 2611, 4455, 1402, 2645, 4457, 4459,
    2791, 4461, 1881, 4215, 4288, 4464, 2621, 3390, 2950, 2846, 4466, 3946, 3762, 4468, 4469,
    4470, 4472, 4474, 4476, 3871, 4479, 4480, 4481, 4483, 4484, 4485, 2915, 3784, 4155, 4488,
    4031, 4491, 4493, 4496, 4498, 3845, 3891, 3681, 4501, 2048, 3329, 1475, 1798, 2664, 4505,
    4508, 4510, 4512, 4400, 2546, 4515, 4517, 3803, 4091, 4521, 2673, 4524, 4526, 4326, 2485,
    1527, 4529, 4531, 4533, 4535, 4537, 4076, 1875, 4539, 4541, 4543, 4545, 4547, 4549, 4551,
    1455, 2724, 4556, 1456, 2727, 1457, 2729, 4561, 1458, 2732, 1459, 2734, 4563, 1502, 1461,
    2738, 4571, 4573, 4047, 1464, 2743, 1465, 2745, 4582, 1466, 2748, 1467, 2750, 4591, 4593,
    4595, 1470, 2755, 4051, 1472, 2758, 1515, 4603, 1474, 2762, 2690, 4609, 1476, 2766, 1477,
    2768, 1478, 2770, 1479, 2772, 1480, 2774, 4620, 4621, 3745, 4623, 4624, 4626, 4041, 3809,
    4628, 4630, 4632, 4634, 3826, 4636, 4638, 2433, 4640, 4642, 3902, 3840, 4333, 1491, 2797,
    1492, 2799, 3719, 4648, 1495, 2803, 1496, 2805, 4655, 4657, 4659, 1831, 4661, 1500, 2812,
    1501, 2814, 4665, 1503, 2817, 4669, 1504, 1505, 2821, 3720, 4672, 3907, 1508, 2826, 1509,
    2828, 3839, 1510, 2831, 4677, 4678, 4336, 1514, 2836, 1516, 4684, 1517, 2840, 1518, 2842,
    2548, 1519, 1520, 4693, 4695, 4696, 2709, 1528, 2851, 4702, 1529, 2854, 1530, 2856, 4710,
    1532, 2859, 3911, 1569, 1534, 2863, 1535, 2865, 1536, 2867, 1537, 2869, 4723, 1540, 2872,
    1541, 2874, 4725, 1542, 2877, 1584, 1544, 2880, 4736, 1545, 2883, 1546, 2885, 4741, 1549,
    2888, 1550, 2890, 3912, 1551, 2893, 1552, 2895, 4757, 2513, 4046, 1559, 2900, 1560, 2902,
    3808, 1562, 2905, 4763, 4765, 4767, 1565, 2910, 1566, 2912, 2043, 1567, 1568, 3647, 1570,
    2918, 1571, 4780, 1574, 2922, 1575, 2924, 3656, 1577, 2927, 1578, 2929, 3746, 4791, 1583,
    2933, 4795, 1585, 2936, 1586, 4798, 1587, 2940, 1588, 2942, 1590, 2944, 1591, 2946, 1592,
    2948, 4465, 4718, 4804, 1595, 2953, 3101, 3156, 4806, 3171, 4809, 4080, 1600, 2961, 3621,
    4811, 3905, 4030, 3810, 4589, 4814, 1605, 2970, 4559, 4817, 4819, 3173, 4822, 4824, 1609,
    2978, 1610, 2980, 1611, 2982, 4826, 4828, 4830, 4831, 1616, 2988, 4086, 3486, 3870, 2951,
    4836, 4838, 4204, 4097, 4731, 1623, 2999, 4842, 2965, 3085, 4846, 4848, 4851, 2696, 1628,
    3008, 3815, 3687, 4854, 4744, 4174, 4043, 4856, 1633, 3017, 3102, 4858, 4861, 4863, 4866,
    4737, 1637, 3025, 3601, 4869, 4616, 1640, 3030, 3105, 3822, 4872, 3116, 3174, 4874, 3852,
    4564, 1647, 3040, 4878, 4880, 2687, 4883, 3015, 4885, 3132, 1652, 3049, 4887, 4889, 4891,
    4893, 1657, 3055, 4896, 3029, 3363, 4899, 3193, 3862, 4032, 1662, 3064, 1663, 3066, 1664,
    3068, 4902, 4373, 3898, 4396, 4906, 4106, 4909, 1669, 3077, 4911, 4913, 4915, 3885, 1674,
    3083, 4843, 4716, 4092, 4921, 3742, 4924, 4926, 4927, 3248, 1681, 3094, 1682, 3096, 1683,
    3098, 4721, 4805, 4033, 4931, 4739, 3509, 1688, 3106, 3075, 4934, 2500, 1691, 3111, 4937,
    4939, 4941, 4602, 1694, 3117, 4943, 3087, 1796, 3182, 4946, 2438, 2780, 1699, 3126, 3727,
    4949, 4952, 4954, 4886, 3849, 4601, 4957, 4261, 1706, 3137, 4959, 3684, 4963, 3985, 4964,
    4062, 3693, 1711, 3146, 4029, 4968, 4970, 4972, 1716, 3152, 4975, 4977, 4714, 4979, 1719,
    3158, 4982, 3483, 2807, 1854, 3133, 4984, 2483, 1724, 3167, 4557, 4987, 3308, 4617, 3877,
    4873, 1729, 3175, 4991, 3142, 1778, 1732, 3360, 3957, 3072, 4742, 4994, 4995, 4996, 1930,
    3587, 3603, 5000, 5001, 4060, 3013, 2605, 1742, 4122, 5003, 5004, 4085, 3425, 1940, 2564,
    3567, 3697, 4691, 5007, 4708, 5010, 3909, 5012, 4446, 3458, 1797, 5014, 3186, 5016, 2819,
    2834, 5018, 4578, 5021, 4613, 3897, 3200, 2663, 4064, 3473, 4393, 5026, 1850, 5028, 5029,
    4503, 3737, 4513, 4007, 5031, 3496, 4059, 3831, 2670, 3673, 3572, 2442, 5036, 4382, 4789,
    2482, 5039, 2776, 3179, 1779, 2932, 1827, 1781, 3256, 3610, 3583, 4405, 3851, 3481, 1784,
    1785, 2576, 1787, 3266, 5049, 1789, 3269, 1790, 3271, 2935, 2777, 1794, 3275, 1837, 3121,
    3214, 4732, 2691, 1799, 3282, 3482, 5062, 4728, 1802, 3287, 1803, 3289, 3582, 1804, 3292,
    1805, 3605, 1806, 3296, 1807, 3298, 4750, 5067, 4703, 5069, 5071, 4614, 4511, 3718, 2958,
    3728, 3825, 5074, 5075, 4449, 4228, 1818, 3315, 1819, 3317, 4565, 1820, 3320, 1821, 3322,
    4610, 5085, 4050, 1824, 3327, 1825, 1826, 3330, 5089, 1828, 3333, 5091, 1829, 3336, 1830,
    3338, 2810, 1832, 1833, 3342, 4049, 5096, 4611, 1836, 3347, 5101, 2559, 1839, 5105, 1840,
    3353, 1841, 3355, 5108, 1842, 3358, 1843, 4343, 4790, 4898, 3231, 5113, 1852, 3366, 2106,
    3163, 3060, 1895, 1856, 3372, 3819, 3571, 1859, 1860, 3377, 3668, 1861, 3380, 1862, 3382,
    5132, 1863, 3385, 1864, 3387, 2671, 1867, 4932, 1869, 3392, 1908, 5138, 1871, 3396, 1872,
    3398, 5143, 1876, 3401, 1877, 3403, 3497, 1878, 1879, 3062, 1880, 3409, 2651, 1886, 1887,
    3413, 1888, 3415, 5150, 4371, 5151, 1891, 3420, 1892, 3422, 4794, 1893, 1894, 3426, 4704,
    1896, 3429, 4726, 1897, 2610, 5162, 1901, 3435, 1902, 3437, 4307, 1903, 3440, 1904, 3442,
    5174, 1907, 3445, 4733, 1909, 2315, 4751, 1911, 2358, 1913, 3453, 3622, 5183, 4568, 4094,
    3828, 3868, 5184, 5186, 5187, 5189, 4690, 5191, 3769, 3948, 5192, 4782, 5193, 3683, 5023,
    5171, 5195, 5117, 5197, 3888, 5199, 4587, 5044, 5060, 4140, 4299, 3144, 3896, 1980, 2968,
    3461, 4462, 5202, 5204, 4250, 5205, 4016, 3863, 5146, 4376, 3470, 5208, 4773, 2030, 4500,
    3744, 5211, 5212, 4113, 5139, 3032, 3709, 5213, 5215, 4025, 5217, 5218, 5220, 1960, 3517,
    5221, 1961, 3520, 2095, 5224, 1963, 3524, 1964, 3526, 5226, 2005, 1966, 3530, 4221, 5228,
    5127, 1969, 3535, 1970, 3537, 4344, 1971, 3540, 1972, 3542, 4774, 5235, 5237, 1975, 5129,
    1977, 3549, 2018, 5241, 1979, 3553, 3487, 5246, 1981, 3557, 1982, 3559, 1983, 3561, 1984,
    2364, 4150, 3782, 4654, 5250, 4403, 5252, 5122, 5034, 4519, 3708, 5254, 4706, 4081, 5257,
    4494, 5258, 4188, 4729, 3847, 1996, 1997, 3585, 4997, 5261, 2000, 3589, 2001, 3591, 4014,
    5267, 5268, 2997, 4067, 2006, 3598, 3806, 2007, 2424, 4998, 5271, 3846, 2011, 3606, 2012,
    3608, 4160, 2013, 3611, 4063, 3807, 2017, 3615, 5277, 2020, 2021, 3619, 2022, 2023, 4291,
    4096, 5281, 3502, 2031, 3627, 4162, 2032, 3630, 2033, 3632, 4026, 2035, 4068, 2072, 2037,
    3638, 2038, 3640, 2512, 2040, 3643, 5292, 2914, 2044, 5294, 2045, 3649, 2087, 2047, 3652,
    4173, 2688, 2049, 4437, 2052, 3658, 2053, 3660, 4072, 2054, 3663, 2055, 3665, 5311, 5126,
    2062, 3669, 2063, 3671, 5033, 2065, 3674, 4646, 4252, 5316, 2068, 3679, 2069, 3139, 2070,
    4960, 2073, 3685, 2074, 5324, 2077, 3689, 2078, 3691, 4653, 2080, 3694, 2081, 5005, 5328,
    2086, 3699, 3783, 2499, 4151, 2090, 3704, 2091, 3706, 4527, 4522, 2096, 3710, 2097, 3712,
    3573, 2132, 2099, 3716, 4518, 2101, 2102, 3236, 2103, 3722, 2104, 3724, 3306, 2107, 4506,
    2109, 3729, 2110, 3731, 3234, 2111, 3734, 2143, 4502, 2640, 2115, 2464, 3503, 2118, 2119,
    4499, 2120, 2121, 3579, 2122, 3748, 2123, 3750, 2124, 3752, 2125, 3754, 2126, 3756, 2127,
    3758, 2128, 3760, 2129, 2131, 3763, 2133, 3765, 2134, 3767, 2135, 2136, 3770, 2137, 3772,
    2138, 3774, 2139, 3776, 2140, 3778, 2142, 3780, 2144, 2145, 2146, 2147, 3785, 2148, 3787,
    2150, 3789, 2151, 3791, 2152, 3793, 2153, 3795, 2154, 3797, 2156, 3799, 2157, 3801, 2158,
    2159, 3804, 2160, 2161, 2162, 2163, 2164, 2165, 3811, 2166, 3813, 2168, 2169, 3816, 3038,
    5121, 2172, 3820, 3966, 3995, 3507, 4705, 4005, 4681, 2177, 4651, 5401, 4752, 2181, 3832,
    3135, 3539, 4358, 4008, 5406, 2185, 2186, 2187, 3841, 2188, 3843, 2189, 3295, 3259, 5306,
    3164, 2192, 4372, 3818, 3361, 5416, 4256, 2198, 3856, 5420, 3830, 4240, 3954, 3408, 3239,
    2586, 5379, 2203, 3866, 2204, 3074, 4833, 4477, 2207, 3967, 4664, 4229, 5431, 2975, 2469,
    2544, 3210, 2606, 3494, 2214, 3883, 4916, 5434, 3977, 4009, 5437, 4289, 2219, 2220, 3892,
    2221, 3894, 2991, 5022, 3183, 3469, 4748, 5439, 2226, 5442, 4717, 3002, 5444, 2230, 5445,
    3880, 2849, 4713, 4749, 2588, 2235, 3914, 2236, 3916, 2237, 3918, 2238, 3920, 2239, 3922,
    2241, 3924, 2242, 3926, 2243, 3928, 2244, 3930, 2246, 3932, 2247, 3934, 2248, 3936, 2249,
    3938, 2250, 3940, 2251, 3942, 5459, 4575, 4467, 5308, 4796, 4332, 3476, 2256, 3951, 4057,
    5422, 5464, 5466, 3122, 5469, 3192, 2261, 3960, 2262, 3962, 2263, 3964, 3033, 5427, 2972,
    3949, 4335, 4451, 2270, 3972, 3212, 4271, 5477, 4354, 2273, 3978, 2659, 4421, 3037, 5478,
    5479, 3178, 4392, 2284, 3987, 2285, 3989, 2286, 3991, 4760, 3047, 5398, 2289, 3996, 5484,
    5448, 5487, 2293, 4001, 3515, 3548, 2788, 3506, 4082, 4355, 3478, 2298, 4010, 5489, 3983,
    2641, 5491, 5206, 2302, 4017, 2303, 4019, 3198, 3344, 2308, 4023, 4115, 4161, 5493, 5496,
    4966, 2313, 4489, 4901, 3019, 4212, 4799, 4170, 5501, 2319, 4038, 2615, 2321, 5502, 3046,
    4600, 5506, 2325, 4574, 2613, 4022, 5086, 4598, 2761, 2330, 4053, 4584, 2599, 5462, 2473,
    5032, 3061, 3568, 3485, 2335, 4580, 5509, 4785, 2340, 4116, 3625, 2633, 5512, 4432, 3092,
    2344, 4074, 4119, 2647, 4776, 4131, 4171, 4615, 3237, 2350, 4083, 3225, 4192, 5454, 4065,
    5263, 4144, 2355, 3120, 5520, 3213, 4266, 4187, 3596, 5523, 4431, 3677, 2363, 4101, 5524,
    5525, 2957, 3108, 2372, 4107, 2373, 4109, 2374, 4111, 3824, 3233, 3513, 3636, 4415, 3463,
    2715, 2379, 4120, 5002, 5529, 4104, 5531, 2383, 4126, 3001, 4676, 4285, 5055, 2386, 4132,
    5536, 2475, 5114, 5470, 2390, 4138, 3161, 5539, 3491, 5541, 5518, 3901, 4259, 5098, 2395,
    4148, 4670, 5331, 3511, 3654, 5546, 4486, 4754, 2400, 4157, 3286, 3258, 3634, 5285, 2403,
    4163, 2674, 2408, 4166, 3024, 4214, 5500, 2960, 3645, 4153, 2642, 3617, 3595, 5168, 2421,
    4178, 2422, 4180, 2662, 4989, 2466, 2426, 4185, 3624, 4643, 3199, 2429, 2430, 2990, 2432,
    4193, 5365, 2434, 4196, 2435, 4198, 3124, 2995, 2439, 4202, 4839, 3245, 5366, 2444, 4207,
    5172, 2447, 4210, 2448, 3474, 2449, 2450, 4389, 2451, 4217, 2452, 4219, 5227, 3676, 3319,
    2458, 4224, 2459, 4226, 5077, 2460, 2461, 4230, 4577, 2465, 4233, 5409, 2467, 4236, 4554,
    4612, 2472, 4567, 5579, 2476, 4243, 2477, 4245, 4667, 2478, 4248, 2479, 3533, 4100, 3249,
    3166, 4552, 2484, 2708, 2520, 2488, 3667, 4645, 3457, 2491, 2492, 4264, 4442, 2493, 4267,
    2494, 4269, 4569, 2495, 4272, 2496, 4274, 2833, 3110, 2816, 2501, 4279, 2532, 5446, 2506,
    4283, 2507, 3187, 2508, 2509, 2510, 2898, 5280, 3580, 5600, 2516, 4294, 2517, 4296, 5602,
    2518, 2519, 4300, 4707, 2521, 4303, 5608, 2522, 4730, 2525, 4308, 2526, 4310, 3434, 2527,
    4313, 2528, 4315, 5337, 2531, 4318, 5616, 2533, 4321, 2534, 4323, 3908, 2535, 2536, 4327,
    2537, 4329, 3879, 3969, 2545, 2698, 5474, 2547, 2844, 5619, 2587, 2550, 4340, 3312, 3853,
    3835, 2553, 4345, 2554, 4347, 3534, 2555, 4350, 2556, 4352, 3887, 3837, 2561, 4356, 5404,
    2563, 4359, 3203, 3976, 2565, 4363, 2566, 4365, 2567, 4367, 2568, 4369, 4788, 3261, 4783,
    2577, 4374, 5207, 5635, 2580, 4378, 2581, 4380, 5037, 3947, 2585, 4384, 3864, 5639, 3913,
    5567, 2592, 4390, 2593, 5024, 2594, 4394, 4905, 2598, 4397, 5646, 2600, 2601, 4401, 2602,
    3417, 5043, 5648, 3195, 3881, 5653, 2607, 4410, 2608, 4412, 5655, 5527, 2643, 2612, 4417,
    4048, 5658, 2618, 2619, 4422, 5660, 2620, 4425, 2655, 2622, 4428, 5661, 2624, 3662, 2627,
    4433, 2628, 4435, 5301, 2629, 4438, 2630, 4440, 4095, 4070, 2634, 4444, 3974, 2636, 4447,
    5076, 3362, 5475, 2639, 4452, 2644, 4454, 5672, 4077, 2648, 4458, 2650, 4460, 5201, 2654,
    4463, 2657, 3980, 2660, 4182, 3226, 2692, 2665, 4471, 2666, 4473, 2667, 4475, 2668, 2669,
    4478, 3242, 3389, 2672, 4482, 2704, 4165, 2677, 2678, 4487, 2679, 2680, 4490, 2681, 4492,
    3747, 2682, 4495, 2683, 4497, 3504, 3741, 3044, 3235, 3733, 2693, 4504, 3309, 2694, 4507,
    2695, 4509, 3726, 3007, 3721, 2699, 4514, 2700, 4516, 3307, 3714, 2703, 4520, 3510, 2705,
    4523, 2706, 4525, 3574, 2710, 4528, 2711, 4530, 2712, 4532, 2713, 4534, 2714, 4536, 2717,
    4538, 2718, 4540, 2719, 4542, 2720, 4544, 2721, 4546, 2722, 4548, 2723, 4550, 5584, 4232,
    5577, 2726, 4555, 4662, 4680, 3968, 2731, 4560, 2736, 4562, 4875, 4223, 4242, 4688, 4262,
    3975, 2740, 4570, 2741, 4572, 2742, 4864, 5526, 4553, 5019, 4177, 3227, 2747, 4581, 5565,
    5507, 4649, 5435, 5200, 4123, 3488, 2752, 4590, 2753, 4592, 2754, 4594, 5352, 5621, 2757,
    4663, 5504, 4956, 3035, 4052, 4103, 5383, 4141, 3207, 2765, 4608, 5083, 5097, 4668, 4689,
    5072, 3577, 3058, 4988, 4605, 4125, 3251, 3274, 2779, 4622, 3125, 2781, 4625, 2784, 4627,
    2785, 4629, 2786, 4631, 2787, 4633, 2789, 4635, 2790, 4637, 2792, 4639, 2793, 4641, 3581,
    5611, 3136, 4222, 2802, 4647, 5712, 5724, 5400, 5362, 3145, 3204, 3162, 2808, 4656, 2809,
    4658, 2811, 4660, 3169, 5669, 5428, 4278, 5385, 5580, 4239, 3218, 3565, 2824, 4671, 4430,
    3465, 5378, 5080, 4276, 3219, 5348, 5708, 5399, 3070, 2839, 4683, 2987, 5056, 5456, 4241,
    3223, 4674, 5006, 2847, 4692, 2848, 4694, 3910, 3500, 3956, 5417, 3984, 2853, 4701, 4769,
    4793, 3310, 5255, 5606, 5008, 2858, 4709, 5367, 5295, 2861, 2956, 4800, 4918, 5229, 2993,
    4012, 4699, 4928, 2871, 4722, 2876, 4724, 4770, 3419, 4159, 3291, 3439, 4840, 5057, 5177,
    3450, 2882, 4735, 4168, 4777, 4801, 2887, 4740, 4992, 5047, 3194, 4015, 5124, 4784, 5438,
    2892, 5065, 4734, 3241, 3395, 4815, 5482, 2897, 4756, 3544, 3519, 5481, 5357, 2907, 4762,
    2908, 4764, 2909, 4766, 5392, 3302, 3431, 5543, 3051, 5209, 4758, 5116, 5239, 5740, 3143,
    2921, 4779, 5374, 3499, 3071, 5744, 5510, 5753, 5082, 3418, 3093, 4450, 3254, 5395, 3428,
    5154, 3273, 3468, 2939, 4797, 5099, 5276, 3104, 3698, 2952, 4803, 2955, 4105, 5758, 2959,
    4808, 2964, 4810, 5297, 2969, 4813, 4156, 2973, 4816, 2974, 4818, 4935, 2976, 4821, 2977,
    4823, 2984, 4825, 2985, 4827, 2986, 4829, 4685, 5128, 2992, 5771, 2994, 4835, 5618, 4201,
    2996, 2998, 5247, 4128, 3003, 5774, 3004, 4845, 3005, 4847, 5640, 3006, 4850, 5432, 3012,
    4853, 3016, 4855, 3020, 4857, 4973, 3021, 4860, 3022, 4862, 3945, 3023, 4865, 4387, 3028,
    4868, 5784, 3034, 4871, 3036, 3982, 3039, 5787, 3042, 4877, 3043, 4879, 5330, 3045, 4882,
    5286, 3994, 3048, 4772, 3052, 4888, 3053, 4890, 3054, 4892, 5797, 3057, 4895, 5298, 3059,
    3370, 5307, 3063, 4682, 5573, 5355, 3073, 3869, 5799, 3076, 4908, 3079, 4910, 3080, 4912,
    3081, 4914, 3082, 5553, 3086, 5805, 3088, 4920, 5576, 3090, 4923, 3091, 4925, 4073, 3100,
    5810, 3103, 4930, 5135, 3109, 4933, 5045, 3113, 4936, 3114, 4938, 3115, 4940, 3119, 4942,
    5817, 3123, 4945, 5818, 3129, 4948, 5176, 3130, 4951, 3131, 4953, 5136, 3134, 3834, 5364,
    3682, 3140, 5823, 3141, 4962, 4778, 5181, 3148, 3149, 4967, 3150, 4969, 3151, 4971, 5597,
    3154, 4974, 3155, 4976, 3157, 4978, 5830, 3160, 4981, 3165, 4983, 5835, 3170, 4986, 3172,
    5551, 3177, 4990, 3184, 3185, 4993, 3216, 4286, 3189, 3190, 3191, 4999, 3959, 3197, 4021,
    4189, 3205, 3206, 4607, 3208, 3209, 5009, 3211, 5011, 3215, 5013, 3217, 5015, 3220, 5017,
    3221, 3222, 5020, 3224, 3228, 3229, 3230, 5025, 3232, 5027, 4114, 3238, 5030, 3240, 3243,
    3244, 3246, 5035, 3247, 3250, 5038, 5264, 5870, 5871, 3260, 3262, 4820, 5827, 5340, 3268,
    5048, 4786, 5041, 5079, 5857, 5087, 4079, 5736, 3280, 5877, 5647, 3284, 3285, 5061, 5881,
    5289, 3300, 3301, 5066, 3303, 5068, 3304, 5070, 3305, 3311, 5073, 4342, 3313, 3314, 5134,
    5393, 4129, 5894, 5490, 3324, 3325, 5084, 3326, 5876, 3332, 5088, 3335, 5090, 3456, 5898,
    5605, 3345, 5095, 3346, 5313, 4035, 3349, 5100, 5883, 5702, 3352, 5104, 4917, 3357, 5107,
    5629, 5093, 5738, 3365, 5112, 5175, 5668, 5750, 3950, 5332, 5179, 5904, 3374, 3375, 5905,
    5240, 5908, 3379, 4349, 5617, 4004, 3552, 3384, 5131, 5230, 5893, 3391, 5152, 4947, 4753,
    5153, 5321, 5159, 3400, 5142, 5889, 5165, 3405, 5695, 5581, 5910, 4404, 4727, 4955, 3508,
    3424, 5911, 5149, 5651, 5273, 5761, 5691, 5895, 4312, 5530, 5914, 5358, 4042, 5532, 4579,
    4965, 5375, 4213, 5309, 3444, 5173, 4136, 5820, 3447, 3471, 5903, 4958, 5169, 4944, 5092,
    3489, 3462, 5185, 4118, 3464, 5188, 3466, 5190, 3899, 5178, 3475, 5194, 3477, 5196, 3479,
    5198, 3480, 3490, 4142, 3492, 5203, 3882, 3495, 3498, 4697, 3501, 3505, 5210, 4006, 4152,
    3512, 5214, 3514, 5216, 4003, 3516, 5219, 4759, 5275, 3523, 5223, 3528, 5225, 3532, 4251,
    3904, 5909, 5262, 4098, 5155, 3545, 5234, 3546, 5236, 5842, 4078, 4746, 5130, 5148, 5861,
    5163, 3556, 5245, 5641, 5243, 5157, 4061, 3570, 5251, 3575, 5253, 3576, 3578, 5256, 4292,
    4143, 3588, 5260, 5726, 5517, 5869, 5731, 3594, 5266, 4176, 5745, 3604, 5270, 5856, 5768,
    3886, 5936, 4715, 4175, 5762, 5891, 3623, 4069, 5081, 5873, 5094, 3629, 5329, 5849, 5333,
    5800, 5109, 5283, 4172, 3648, 5293, 5318, 4876, 5763, 5689, 4900, 5322, 3657, 5756, 5111,
    5781, 5326, 5411, 5299, 4383, 4209, 5899, 4260, 4903, 4147, 5845, 3678, 5315, 5866, 4712,
    4037, 5742, 5804, 5949, 3688, 5323, 5678, 5676, 5769, 4802, 4884, 5788, 3703, 5772, 5816,
    5950, 5327, 5955, 5614, 4338, 5644, 4743, 4597, 5957, 5735, 5633, 5960, 5780, 5748, 5733,
    5963, 4586, 5534, 5703, 4761, 5965, 5574, 5967, 5353, 5145, 5754, 5719, 5968, 5380, 5144,
    5180, 5555, 5561, 5706, 5160, 5970, 4675, 5723, 5722, 5557, 5453, 5916, 5906, 5556, 5370,
    5425, 4652, 5755, 5717, 4618, 5680, 5547, 5381, 5593, 5879, 5449, 5533, 5853, 5747, 5052,
    5473, 5476, 4576, 5451, 3823, 3827, 3829, 3859, 5452, 5053, 3836, 3838, 5405, 5973, 5919,
    5548, 5503, 3848, 5975, 5687, 5317, 3854, 5415, 4720, 5686, 3858, 5419, 5778, 3861, 5976,
    5790, 3865, 5472, 3873, 3874, 5480, 3876, 5430, 5777, 5693, 5274, 5350, 3889, 5436, 3900,
    4145, 5732, 3903, 5441, 3906, 5443, 4325, 5592, 5103, 5485, 5829, 5984, 5730, 5729, 4781,
    5516, 5862, 5737, 5650, 3944, 5458, 5591, 5928, 3953, 3955, 5463, 5560, 4698, 5990, 3958,
    5468, 5537, 5609, 5977, 5812, 3970, 3971, 4792, 4362, 4013, 4700, 5813, 3993, 5508, 3998,
    5483, 3999, 4000, 5486, 5649, 4719, 4787, 4745, 4027, 5492, 5696, 4028, 5495, 4399, 5985,
    5450, 4036, 5319, 5166, 5746, 4044, 4045, 5505, 4055, 4755, 4088, 4066, 4071, 5511, 5718,
    5382, 5997, 4087, 4089, 4090, 4093, 5519, 5440, 5679, 5232, 4604, 4124, 5396, 4117, 4644,
    4588, 5244, 4619, 5828, 5612, 5682, 4134, 5535, 4137, 5120, 4606, 6002, 5259, 5841, 5749,
    5042, 4154, 5545, 4666, 4235, 5421, 5645, 4183, 4919, 5106, 5698, 4195, 5570, 5860, 5412,
    5424, 5979, 4206, 5279, 5665, 5934, 5656, 6005, 4216, 4406, 5361, 5377, 5488, 5838, 5312,
    4904, 4980, 5807, 4238, 5666, 4566, 4247, 5242, 5408, 6000, 4255, 5993, 5336, 5628, 5929,
    6006, 5674, 5986, 4282, 5886, 5589, 4650, 5801, 4859, 5923, 4293, 5599, 4298, 5601, 5716,
    5598, 5284, 4302, 4305, 5607, 5707, 5991, 5528, 5390, 5498, 4317, 4320, 5615, 4832, 5683,
    5338, 4844, 5341, 6009, 5765, 5636, 5786, 5603, 5638, 5825, 5290, 5847, 5610, 5630, 5792,
    4377, 5634, 5688, 5684, 5832, 4867, 5775, 4841, 5868, 5714, 5956, 5821, 5497, 5878, 5568,
    5571, 5854, 5249, 4409, 5652, 4414, 5654, 4583, 4420, 5657, 4424, 5659, 4673, 5670, 5583,
    5673, 5999, 5795, 5864, 5901, 4599, 5996, 4456, 5671, 5721, 6007, 5710, 5305, 5622, 5888,
    5776, 5937, 6015, 5351, 4837, 5859, 5310, 5865, 5789, 5624, 4897, 6017, 5368, 5938, 5980,
    6019, 5803, 5948, 6012, 5824, 6021, 5720, 5751, 5447, 4596, 5734, 5727, 4711, 5471, 4558,
    5848, 5992, 6023, 4585, 6025, 6010, 5623, 5626, 5514, 5887, 5890, 5782, 5664, 5819, 5944,
    5595, 5833, 5231, 5764, 5874, 5402, 5397, 5858, 5521, 4679, 5974, 5958, 4686, 4687, 5303,
    5304, 4738, 6029, 5952, 6030, 4747, 5917, 5410, 4768, 5912, 4771, 4775, 5998, 5815, 5050,
    5806, 5386, 5839, 4807, 5757, 5767, 5515, 5141, 5947, 4812, 5705, 5715, 5566, 5867, 5158,
    5335, 4834, 5770, 5118, 5931, 5620, 4849, 5522, 4852, 5549, 5423, 5961, 5739, 5700, 4870,
    5783, 5793, 5926, 5296, 4881, 5413, 5559, 5925, 5344, 5846, 5123, 5578, 4894, 5796, 4907,
    5798, 5064, 6008, 5811, 5147, 5140, 5552, 5359, 4922, 5164, 4929, 5809, 5942, 5394, 5429,
    5058, 6031, 5288, 5182, 5137, 5372, 4950, 5550, 4961, 5822, 5554, 5587, 5836, 5872, 5167,
    5389, 5575, 5585, 5627, 6026, 4985, 5834, 5918, 5572, 5837, 5302, 5711, 6003, 5932, 5314,
    6036, 5843, 5785, 5632, 5939, 5935, 5791, 5982, 5272, 5941, 5457, 6033, 5852, 5403, 5265,
    5637, 5373, 5248, 5920, 6032, 5884, 5418, 5414, 5759, 5897, 5040, 5051, 5544, 5046, 5291,
    5922, 5896, 5054, 5814, 5059, 5945, 5063, 5880, 5773, 5900, 5667, 5988, 5387, 5513, 5325,
    5363, 5360, 5562, 5342, 5078, 5282, 5913, 6038, 5642, 5110, 5685, 5102, 5115, 5885, 5119,
    5538, 5794, 5951, 5125, 5907, 5133, 5156, 5233, 5347, 5161, 5808, 5694, 5170, 5269, 5826,
    5582, 5455, 6013, 5728, 5604, 6011, 5850, 5625, 5743, 5987, 5940, 5953, 5882, 5238, 5946,
    5943, 5287, 5222, 5384, 6018, 5709, 5588, 5391, 5802, 5564, 5371, 5388, 6037, 5278, 5494,
    5300, 5954, 5376, 5320, 5995, 5334, 5586, 5339, 5892, 5343, 5345, 5959, 5346, 5349, 5962,
    5354, 5964, 5356, 5966, 5569, 5369, 5969, 5844, 5407, 5972, 5704, 5558, 5779, 5426, 6044,
    5465, 5433, 5924, 6004, 5699, 5499, 5613, 5460, 5461, 5902, 5467, 5989, 5631, 5675, 5831,
    6045, 5930, 5662, 5760, 5701, 5563, 5663, 5540, 6001, 5542, 5851, 5766, 5594, 5590, 5596,
    5677, 5643, 5981, 6020, 6040, 5681, 6014, 5690, 6016, 5692, 5915, 5697, 5983, 6039, 5840,
    5713, 6024, 5725, 6043, 5741, 6028, 5927, 5752, 6034, 6035, 5863, 5855, 5971, 5933, 5875,
    6046, 5921, 5978, 5994, 6047, 6041, 6042, 6022, 6027]

/-- Reduce a natural number modulo `6048` to land in `Fin 6048`. -/
def fin6048 (n : Nat) : Fin 6048 :=
  ⟨n % 6048, Nat.mod_lt _ (by decide)⟩

/-- Cayley-table successor function: `nextIndex s i` is the index `j` such that
`evalWord (word j) = stepPerm s * evalWord (word i)`. -/
def nextIndex : Step → Fin 6048 → Fin 6048
  | .a, i => fin6048 (nextA.getD i.val 0)
  | .b, i => fin6048 (nextB.getD i.val 0)
  | .A, i => fin6048 (nextAI.getD i.val 0)
  | .B, i => fin6048 (nextBI.getD i.val 0)

/-- The packed-word table has exactly 6048 entries, one per element of `G`. -/
theorem wordCodeArray_size : wordCodeArray.size = 6048 := by native_decide

/-- Compatibility between the indexed enumeration and the Cayley-table successor
`nextIndex`. Verified by `native_decide`. -/
theorem step_evalWord_eq (s : Step) (i : Fin 6048) :
    evalWord (word (nextIndex s i)) = stepPerm s * evalWord (word i) := by native_decide +revert

/-- The certified carrier `{evalWord (word i) : i ∈ Fin 6048}` of the simple group `G`. -/
def carrier : Finset Perm28 :=
  Finset.univ.image (fun i : Fin 6048 ↦ evalWord (word i))

/-- The carrier has cardinality `6048`. -/
theorem carrier_card : carrier.card = 6048 := by native_decide

/-- The identity permutation belongs to the carrier (it is the image of index `0`). -/
theorem one_mem_carrier : (1 : Perm28) ∈ carrier := by
  rw [carrier]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by native_decide⟩

/-- Each generator belongs to the subgroup it generates. -/
theorem gen_mem_closure (i : Fin 2) : gen i ∈ Subgroup.closure (Set.range gen) :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Every letter `a, b, A, B` evaluates to an element of the generated subgroup. -/
theorem stepPerm_mem_closure (s : Step) : stepPerm s ∈ Subgroup.closure (Set.range gen) := by
  cases s
  · exact gen_mem_closure 0
  · exact gen_mem_closure 1
  · exact (Subgroup.closure (Set.range gen)).inv_mem (gen_mem_closure 0)
  · exact (Subgroup.closure (Set.range gen)).inv_mem (gen_mem_closure 1)

/-- Every carrier element belongs to the generated subgroup. -/
theorem carrier_subset_closure (y : Perm28) (hy : y ∈ carrier) :
    y ∈ Subgroup.closure (Set.range gen) := by
  rw [carrier] at hy
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
  induction word i with
  | nil => simp only [evalWord, one_mem]
  | cons s w ih =>
    simp only [evalWord]
    exact Subgroup.mul_mem _ (stepPerm_mem_closure s) ih

/-- The carrier is closed under left multiplication by a generator. -/
theorem gen_mul_mem_carrier (i : Fin 2) (y : Perm28) (hy : y ∈ carrier) : gen i * y ∈ carrier := by
  rw [carrier] at hy ⊢
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨nextIndex (genStep i) j, Finset.mem_univ _, ?_⟩
  rw [step_evalWord_eq, stepPerm_genStep]

/-- The carrier is closed under left multiplication by an inverse generator. -/
theorem gen_inv_mul_mem_carrier (i : Fin 2) (y : Perm28) (hy : y ∈ carrier) :
    (gen i)⁻¹ * y ∈ carrier := by
  rw [carrier] at hy ⊢
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨nextIndex (invGenStep i) j, Finset.mem_univ _, ?_⟩
  rw [step_evalWord_eq, stepPerm_invGenStep]

/-- The carrier coincides with the generated subgroup. -/
theorem closure_mem_iff_carrier :
    ∀ y : Perm28, y ∈ Subgroup.closure (Set.range gen) ↔ y ∈ carrier :=
  KourovkaNotebook.closure_eq_finset_of_left_stable gen carrier one_mem_carrier
    gen_mul_mem_carrier gen_inv_mul_mem_carrier carrier_subset_closure

/-- The simple group `G = ⟨a, b⟩ ≤ S₂₈`, isomorphic to `PSU(3, 3)`. -/
abbrev G :=
  Subgroup.closure (Set.range gen)

/-- A `Fintype` instance for `G`, witnessed by the certified carrier. -/
noncomputable instance : Fintype G :=
  KourovkaNotebook.closureFintypeOfFinset gen carrier closure_mem_iff_carrier

/-- `|G| = 6048`. -/
theorem card_G : Fintype.card G = 6048 := by
  rw [show Fintype.card G = carrier.card from
      KourovkaNotebook.card_closureFintypeOfFinset gen carrier closure_mem_iff_carrier]
  exact carrier_card

/-- Tabulated order of an element of `Perm28`, knowing a priori that the order divides
one of `1, 2, 3, 4, 6, 7, 8, 12` (the element-order spectrum of `PSU(3, 3)`). -/
def orderCodeOf (g : Perm28) : Nat :=
  if g ^ 1 = 1 then 1
  else
    if g ^ 2 = 1 then 2
    else
      if g ^ 3 = 1 then 3
      else
        if g ^ 4 = 1 then 4
        else if g ^ 6 = 1 then 6 else if g ^ 7 = 1 then 7 else if g ^ 8 = 1 then 8 else 12

/-- The tabulated order of the `i`-th element of `G`. -/
def orderCode (i : Fin 6048) : Nat :=
  orderCodeOf (evalWord (word i))

/-- `orderCode i > 0` for every index `i`. -/
theorem orderCode_pos (i : Fin 6048) : 0 < orderCode i := by native_decide +revert

/-- `orderCode i ≤ 12` for every index `i`. -/
theorem orderCode_le_twelve (i : Fin 6048) : orderCode i ≤ 12 := by native_decide +revert

/-- `(evalWord (word i)) ^ orderCode i = 1`: the tabulated exponent is a multiple of
the true order. -/
theorem evalWord_pow_orderCode (i : Fin 6048) : (evalWord (word i)) ^ (orderCode i) = 1 := by
  native_decide +revert

/-- For `0 < m < orderCode i`, `(evalWord (word i)) ^ m ≠ 1`: the tabulated exponent is
minimal. -/
theorem evalWord_pow_lt_orderCode_ne_one (i : Fin 6048) (m : Nat) (hm : m < orderCode i)
    (hmpos : 0 < m) : (evalWord (word i)) ^ m ≠ 1 := by
  have hle : m ≤ 11 := by
    have hcode := orderCode_le_twelve i
    omega
  interval_cases m <;> native_decide +revert

/-- The actual order of the `i`-th element of `G` agrees with the tabulated value. -/
theorem order_evalWord (i : Fin 6048) : orderOf (evalWord (word i)) = orderCode i := by
  rw [orderOf_eq_iff (orderCode_pos i)]
  exact ⟨evalWord_pow_orderCode i, evalWord_pow_lt_orderCode_ne_one i⟩

/-- The indexed data has the element-order histogram of `PSU(3,3)`. -/
theorem orderCode_histogram :
    (Finset.univ.filter (fun i : Fin 6048 ↦ orderCode i = 1)).card = 1 ∧
      (Finset.univ.filter (fun i : Fin 6048 ↦ orderCode i = 2)).card = 63 ∧
        (Finset.univ.filter (fun i : Fin 6048 ↦ orderCode i = 3)).card = 728 ∧
          (Finset.univ.filter (fun i : Fin 6048 ↦ orderCode i = 4)).card = 504 ∧
            (Finset.univ.filter (fun i : Fin 6048 ↦ orderCode i = 6)).card = 504 ∧
              (Finset.univ.filter (fun i : Fin 6048 ↦ orderCode i = 7)).card = 1728 ∧
                (Finset.univ.filter (fun i : Fin 6048 ↦ orderCode i = 8)).card = 1512 ∧
                  (Finset.univ.filter (fun i : Fin 6048 ↦ orderCode i = 12)).card = 1008 :=
  by native_decide

/-- The indexed enumeration of `G` is injective on `Fin 6048`, by the cardinality
argument applied to the certified carrier. -/
theorem evalWord_injective : Function.Injective (fun i : Fin 6048 ↦ evalWord (word i)) := by
  intro i j hij
  have hcard :
    (Finset.univ.image (fun i : Fin 6048 ↦ evalWord (word i))).card =
      (Finset.univ : Finset (Fin 6048)).card := by
    rw [← carrier]
    simp only [carrier_card, card_univ, Fintype.card_fin]
  have hinjOn := Finset.card_image_iff.mp hcard
  exact
    hinjOn (by simp only [coe_univ, Set.mem_univ]) (by simp only [coe_univ, Set.mem_univ]) hij

/-- The element-totient sum of `G` can be computed by summing over the certified
carrier instead of the abstract `Finset` of `G`. -/
theorem sum_carrier_totient_orderOf :
    (∑ g : G, Nat.totient (orderOf g)) = ∑ x ∈ carrier, Nat.totient (orderOf x) := by
  trans ∑ g : G, Nat.totient (orderOf (g : Perm28))
  · simp only [orderOf_submonoid]
  · exact
      (Finset.sum_subtype carrier (fun x ↦ (closure_mem_iff_carrier x).symm)
          (fun x ↦ Nat.totient (orderOf x))).symm

/-- `∑_{g ∈ G} φ(|g|) = 23984`, evaluated by tabulating the orders of all 6048
elements of `G`. -/
theorem sum_totient_orderOf_G : (∑ g : G, Nat.totient (orderOf g)) = 23984 := by
  rw [sum_carrier_totient_orderOf]
  rw [carrier]
  rw [Finset.sum_image]
  · simp only [order_evalWord, orderCode]
    native_decide
  · intro x _hx y _hy hxy
    exact evalWord_injective hxy

/-! ### Simplicity certificate for the degree-28 model

We assemble a `FinsetSimpleGroupCriterion` from the data above: the 13 listed class
representatives `classRepG` cover every nontrivial conjugacy class of `G`, and for each
representative the pre-tabulated `normalWord` recovers both generators `a` and `b`
inside the normal closure. This proves `IsSimpleGroup G`. -/

/-- The two generators of `G`, viewed as elements of the subgroup `G`. -/
def genG (i : Fin 2) : G :=
  ⟨gen i, gen_mem_closure i⟩

/-- A letter `a, b, A, B` interpreted as an element of `G` (rather than `Perm28`). -/
def stepG (s : Step) : G :=
  ⟨stepPerm s, stepPerm_mem_closure s⟩

/-- `stepG` agrees with `stepPerm` after forgetting the subgroup membership. -/
@[simp]
theorem stepG_coe (s : Step) : (stepG s : Perm28) = stepPerm s :=
  rfl

/-- Evaluate a word in `Step`s as an element of `G`. -/
def evalWordG : List Step → G
  | [] => 1
  | s :: w => stepG s * evalWordG w

/-- `evalWordG w` agrees with `evalWord w` after forgetting the subgroup membership. -/
@[simp]
theorem evalWordG_coe : ∀ w : List Step, (evalWordG w : Perm28) = evalWord w
  | [] => rfl
  | s :: w => by simp only [evalWordG, Subgroup.coe_mul, stepG_coe, evalWordG_coe w, evalWord]

/-- Every letter `a, b, A, B` belongs to the subgroup of `G` generated by `genG`. -/
theorem stepG_mem_closure (s : Step) : stepG s ∈ Subgroup.closure (Set.range genG) := by
  cases s
  · rw [show stepG .a = genG 0 by
        ext p
        rfl]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  · rw [show stepG .b = genG 1 by
        ext p
        rfl]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  · rw [show stepG .A = (genG 0)⁻¹ by
        ext p
        rfl]
    exact (Subgroup.closure (Set.range genG)).inv_mem (Subgroup.subset_closure ⟨0, rfl⟩)
  · rw [show stepG .B = (genG 1)⁻¹ by
        ext p
        rfl]
    exact (Subgroup.closure (Set.range genG)).inv_mem (Subgroup.subset_closure ⟨1, rfl⟩)

/-- The image of any word lies in the subgroup of `G` generated by `genG`. -/
theorem evalWordG_mem_closure : ∀ w : List Step, evalWordG w ∈ Subgroup.closure (Set.range genG)
  | [] => by simp only [evalWordG, one_mem]
  | s :: w => by exact Subgroup.mul_mem _ (stepG_mem_closure s) (evalWordG_mem_closure w)

/-- The `i`-th element of `G` (`i ∈ Fin 6048`), as an element of `G` itself. -/
def element (i : Fin 6048) : G :=
  evalWordG (word i)

/-- The indexed enumeration of `G` covers every element. -/
theorem element_surjective : Function.Surjective element := by
  intro x
  have hxcarrier : (x : Perm28) ∈ carrier := (closure_mem_iff_carrier x).1 x.2
  rw [carrier] at hxcarrier
  obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp hxcarrier
  refine ⟨i, ?_⟩
  apply Subtype.ext
  simpa only [element, evalWordG_coe] using hix

/-- Every enumerated element of `G` belongs to the subgroup generated by `genG`. -/
theorem element_mem_closure_range_genG (i : Fin 6048) :
    element i ∈ Subgroup.closure (Set.range genG) := by exact evalWordG_mem_closure (word i)

/-- `genG` generates all of `G`. -/
theorem closure_range_genG : Subgroup.closure (Set.range genG) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  obtain ⟨i, rfl⟩ := element_surjective x
  exact element_mem_closure_range_genG i

/-- `G` is nontrivial: it has order `6048 > 1`. -/
instance instNontrivialG : Nontrivial G :=
  Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [card_G]
      norm_num)

/-- Indices of the 13 nonidentity conjugacy-class representatives `r₁, …, r₁₃`. -/
def repIndexArray : Array Nat :=
  #[5, 2, 931, 1, 3, 14, 40, 6, 9, 79, 81, 80, 82]

/-- The `i`-th nonidentity conjugacy-class representative, as an index into the
enumeration of `G`. -/
def repIndex (i : Fin 13) : Fin 6048 :=
  fin6048 (repIndexArray.getD i.val 0)

/-- The `i`-th nonidentity conjugacy-class representative, as an element of `G`. -/
def classRepG (i : Fin 13) : G :=
  element (repIndex i)

/-- Packed class data.  At index `i`, `code % 13` is the representative index
and `code / 13` is a conjugating element index.  The identity slot is unused. -/
def classCodeArray : Array Nat :=
  #[
    -- entry `i`: low part `% 13` is the class index, high part `/ 13` is the conjugator index.
    0, 3, 1, 4, 10414, 0, 7, 5259, 20, 8, 21, 4090, 3816, 4974, 5, 629, 18, 40, 1409, 4967, 57,
    8119, 55, 8081, 56, 14, 44, 4980, 1422, 642, 29, 33, 30, 60, 73, 46, 1854, 2425, 47, 11460,
    6, 8715, 12650, 2309, 84, 8171, 32176, 12251, 265, 52, 8236, 5842, 19, 32150, 8611, 10759,
    24636, 46663, 72, 6596, 16966, 8926, 35730, 1736, 23492, 13616, 46676, 10824, 26, 31, 32,
    12663, 11525, 12264, 16979, 35743, 13629, 8861, 66, 9, 11, 10, 12, 2302, 336, 906, 233, 907,
    178, 687, 22, 4076, 24, 172, 23, 3804, 25, 173, 128, 165, 765, 120, 932, 124, 90, 121, 985,
    177, 61, 62, 791, 558, 74, 58, 96, 6085, 144, 76, 16595, 3190, 5881, 5591, 75, 8347, 92,
    19064, 148, 77, 6557, 8074, 17779, 3216, 166, 532, 4089, 48, 159, 50, 3817, 49, 160, 51,
    116, 179, 107, 141, 111, 919, 108, 506, 164, 972, 37, 38, 386, 387, 349, 83, 16751, 131,
    12173, 399, 3177, 97, 5968, 31721, 220, 79, 13707, 135, 17883, 426, 8243, 24116, 3203,
    26006, 15522, 1015, 3086, 5506, 32137, 45, 4220, 4113, 37225, 24649, 196, 15509, 12013, 227,
    25420, 3842, 47924, 17109, 5169, 23613, 7514, 109, 456, 169, 2696, 9160, 23475, 10661, 9823,
    18136, 12022, 16468, 19625, 2117, 5143, 22179, 11503, 21646, 14996, 46143, 9836, 21484,
    5381, 30843, 469, 117, 7891, 122, 23479, 13855, 30144, 10060, 56467, 23912, 25529, 10564,
    8744, 11311, 36887, 4779, 33184, 29036, 4965, 4194, 4756, 8594, 14762, 21438, 63, 203, 64,
    150, 183, 893, 827, 894, 1086, 804, 151, 10525, 21035, 12009, 33405, 21009, 11064, 4688,
    5368, 412, 2296, 13842, 4795, 24190, 17545, 15074, 4626, 8301, 519, 202, 11363, 21542, 5523,
    3699, 21594, 8457, 28178, 17104, 439, 1723, 19612, 7274, 10941, 4939, 4523, 17832, 16348,
    29519, 156, 443, 3868, 22218, 17662, 21633, 11192, 71, 5536, 33197, 16842, 4061, 10960,
    7846, 11226, 32392, 13456, 15061, 2274, 17117, 15375, 104, 482, 110, 36538, 4652, 3413,
    31948, 5532, 20132, 21152, 4575, 5851, 32163, 9476, 49953, 17845, 28726, 22807, 11395,
    11129, 28700, 8418, 1080, 190, 35, 137, 36, 1867, 778, 2438, 545, 138, 204, 26842, 19586,
    31223, 2130, 11139, 7235, 53398, 1022, 206, 15766, 37019, 9121, 22101, 17519, 9567, 6306,
    10895, 189, 205, 8796, 11322, 56454, 16153, 33744, 2287, 29532, 761, 207, 9787, 22250,
    10713, 8997, 28438, 14907, 21802, 11265, 324, 297, 1853, 30065, 34783, 11870, 4339, 380,
    8499, 8419, 18253, 3623, 1737, 17226, 2999, 28818, 27216, 381, 13391, 3338, 5716, 10563,
    272, 271, 263, 34991, 13946, 12502, 25117, 267, 11279, 14959, 3533, 25312, 264, 16637,
    22569, 27931, 17741, 385, 3727, 22764, 9107, 11866, 22551, 22760, 25091, 25286, 649, 9615,
    19170, 16611, 12450, 31339, 19183, 50345, 175, 18455, 252, 11935, 12091, 9136, 365, 20366,
    11892, 4001, 21574, 3960, 2995, 2722, 7705, 2575, 12936, 2778, 18201, 3927, 6418, 248,
    30352, 9548, 28217, 369, 34395, 11558, 17187, 1479, 3797, 11852, 22199, 20807, 2579, 129,
    10265, 32326, 6457, 14713, 22747, 22564, 22517, 22712, 17196, 22056, 18624, 226, 17287,
    31779, 6028, 339, 23743, 17038, 17715, 5403, 4074, 28791, 253, 1583, 2861, 41575, 23427,
    12962, 7524, 8213, 222, 22595, 31389, 343, 23409, 33821, 6444, 11584, 7887, 3875, 41679,
    12377, 18168, 2865, 7615, 13383, 30052, 11532, 17235, 11610, 12923, 28805, 13001, 11878,
    29783, 19196, 24293, 22082, 7550, 31509, 15711, 6002, 18194, 22538, 22582, 9602, 8187,
    31326, 23215, 100, 19599, 8652, 34770, 31236, 102, 947, 432, 13352, 20551, 101, 14983, 8107,
    18236, 103, 39995, 433, 10252, 13438, 22734, 25156, 8486, 30131, 1740, 38930, 315, 8406,
    18208, 2089, 22114, 319, 5693, 316, 3636, 13105, 2220, 21425, 437, 5989, 7599, 18266, 17649,
    8678, 19421, 152, 13347, 34068, 406, 154, 29468, 16166, 8133, 153, 27229, 1013, 407, 29545,
    155, 18314, 7534, 11883, 8474, 289, 3325, 21139, 293, 12195, 2063, 5729, 32910, 290, 28713,
    1169, 10576, 21815, 411, 17076, 2194, 648, 12463, 15571, 7612, 15685, 11571, 3845, 162,
    28908, 239, 37448, 2822, 13495, 352, 9149, 25931, 12949, 17492, 17183, 3814, 17025, 2588,
    1634, 29481, 15672, 16953, 17070, 235, 6431, 10276, 43924, 356, 14060, 15542, 17195, 3060,
    3810, 7043, 16947, 2635, 2592, 5038, 115, 9162, 15908, 7547, 29907, 11597, 7939, 213, 32482,
    31766, 23267, 326, 6015, 25195, 7056, 12975, 2787, 22030, 240, 7224, 2757, 7498, 16719,
    41562, 11891, 18220, 209, 8200, 22781, 330, 14515, 33808, 12294, 20846, 13972, 4083, 1686,
    32007, 41692, 2878, 4323, 13630, 20379, 4352, 17064, 7718, 3012, 15581, 7082, 20820, 13959,
    12910, 17234, 12988, 11545, 17754, 11623, 11879, 22773, 22647, 35914, 16337, 34978, 87,
    18299, 8639, 13196, 11905, 89, 5782, 419, 33964, 2791, 88, 24311, 8094, 12234, 420, 2482,
    20392, 14661, 22577, 25221, 11266, 1727, 6666, 302, 8175, 14972, 2076, 306, 9706, 3520, 303,
    29049, 22660, 2207, 9735, 424, 7105, 15519, 29985, 3858, 8665, 17252, 139, 27132, 393, 2546,
    27944, 8120, 17902, 140, 17167, 17208, 394, 29010, 142, 8433, 13412, 15568, 3740, 276,
    36759, 25260, 280, 10109, 2050, 9606, 9120, 277, 6005, 1156, 8901, 13985, 398, 7950, 2181,
    377, 636, 8338, 635, 6128, 644, 8325, 20957, 4350, 33392, 42793, 11077, 5084, 12440, 4675,
    2443, 896, 4808, 12802, 19677, 8031, 33054, 8314, 4639, 905, 6141, 5240, 11350, 3712, 16781,
    5376, 21516, 44742, 28165, 2442, 895, 28997, 4926, 10928, 13087, 4510, 7445, 16231, 260,
    9001, 311, 6310, 284, 1091, 909, 19495, 26855, 5302, 44704, 1515, 11126, 33249, 9014, 1021,
    37032, 13114, 12780, 5039, 2079, 4129, 2692, 5422, 1090, 908, 11335, 2192, 32130, 28934,
    16452, 44586, 5459, 6297, 762, 5467, 2182, 5318, 4057, 14920, 28451, 3959, 16901, 1424, 180,
    1234, 489, 1997, 181, 1753, 371, 16931, 1416, 945, 3918, 359, 1415, 998, 12472, 475, 1437,
    1818, 16619, 372, 22296, 6592, 3507, 20002, 4040, 39163, 8252, 4250, 5292, 3095, 7807,
    15423, 8221, 11205, 17469, 1961, 7221, 1429, 958, 1195, 2010, 2208, 8785, 2, 39917, 36445,
    33210, 39085, 348, 4118, 5233, 11653, 5344, 3907, 10152, 17271, 4140, 3145, 2852, 488,
    10947, 3914, 3452, 4667, 5942, 1671, 17414, 8787, 3345, 3985, 7480, 6512, 7809, 29350, 8949,
    21937, 18416, 3051, 1428, 1011, 7511, 36874, 10308, 8616, 10384, 3396, 547, 12801, 4106,
    2471, 35069, 786, 15362, 9132, 8520, 3079, 24670, 17997, 463, 714, 126, 2930, 345, 661, 127,
    168, 1984, 358, 1766, 167, 1411, 476, 1247, 493, 346, 727, 113, 36525, 2584, 33781, 7755,
    8525, 4665, 28, 1817, 37589, 17505, 3400, 14853, 13155, 3067, 12434, 5123, 1825, 4269, 450,
    462, 492, 19833, 33924, 855, 17653, 41974, 17473, 6614, 12078, 4562, 5518, 1935, 5214,
    21496, 8737, 17438, 6323, 674, 114, 5433, 1492, 17404, 4213, 4670, 46156, 34408, 43832,
    8286, 11329, 11995, 6381, 44768, 2367, 4171, 1566, 8341, 13070, 332, 11382, 13792, 21808,
    4265, 8756, 9023, 1886, 3393, 7198, 8846, 4100, 1205, 5455, 5402, 6369, 7350, 17338, 631,
    35810, 1370, 1973, 5493, 2430, 17077, 23895, 7731, 149, 892, 1335, 4207, 29920, 1877, 2429,
    7095, 19948, 16244, 32800, 12758, 6718, 12000, 25104, 552, 8498, 17321, 25299, 1749, 22556,
    47911, 8849, 17096, 22751, 2387, 5717, 12082, 11632, 3523, 20931, 291, 34666, 1067, 14712,
    429, 31702, 2683, 13716, 2883, 14817, 3082, 14916, 1570, 4327, 5730, 9075, 8551, 27554,
    39046, 1882, 13057, 4835, 1891, 1244, 2374, 3901, 16075, 3862, 7467, 6137, 8936, 10304,
    22608, 25707, 17417, 3344, 4301, 38904, 14956, 3066, 35108, 1106, 16338, 312, 11553, 3718,
    20684, 317, 19885, 23453, 4144, 14346, 37576, 21652, 1364, 5474, 8836, 12576, 33885, 8800,
    13764, 8720, 2541, 10927, 12069, 8273, 6470, 2484, 695, 22673, 4181, 13779, 4671, 17570,
    1782, 8768, 2700, 6694, 8576, 15909, 403, 27606, 1041, 1752, 1762, 8321, 7181, 7339, 6271,
    3601, 2835, 2744, 19053, 25208, 201, 32988, 2989, 4146, 1124, 3657, 12177, 29764, 4048,
    15436, 4109, 3041, 1673, 12437, 2713, 8485, 6475, 12901, 12356, 4535, 34692, 5898, 1374,
    32794, 15518, 286, 27619, 1132, 7926, 292, 9097, 6037, 2523, 25273, 5519, 4066, 2749, 5834,
    8929, 4878, 17535, 1249, 22277, 14970, 32397, 1896, 18039, 18676, 3064, 35726, 6731, 11666,
    7247, 6600, 16567, 8315, 6576, 40152, 17572, 1805, 1450, 5013, 7134, 7194, 9111, 23462,
    14268, 4105, 6284, 838, 10674, 4875, 8217, 2848, 4935, 2140, 3656, 21042, 6550, 2023, 1182,
    13088, 27645, 3054, 2536, 12412, 4159, 26686, 1137, 5803, 9709, 3605, 781, 5846, 9798, 5448,
    14890, 5946, 4122, 9524, 11490, 1351, 2502, 13711, 21724, 8711, 3701, 14632, 5976, 2962,
    2726, 31780, 12563, 5234, 5934, 4223, 9514, 21146, 2053, 34094, 6548, 30856, 3090, 3908,
    32755, 217, 333, 480, 47759, 15415, 8995, 6050, 1501, 44587, 36458, 10953, 2328, 3119, 5328,
    3134, 4879, 1647, 12164, 188, 25944, 479, 449, 7641, 1843, 4115, 2762, 3047, 4324, 12126,
    8968, 7077, 8757, 17548, 17922, 2926, 1353, 11383, 6332, 4155, 4145, 1904, 18052, 18107,
    4993, 1214, 30726, 9498, 5807, 3077, 41153, 4952, 331, 22212, 35739, 1179, 4769, 3399, 1325,
    5110, 13330, 9040, 16869, 6618, 14866, 13648, 42181, 40113, 620, 8758, 17317, 3099, 15713,
    2529, 5708, 34269, 15324, 136, 9127, 1919, 8490, 4126, 14960, 37238, 6423, 26170, 11865,
    389, 5773, 35979, 539, 24358, 826, 13044, 22069, 3855, 7537, 388, 26955, 31561, 8425, 30063,
    1087, 5182, 7900, 12888, 18181, 3510, 11540, 278, 20918, 1054, 4571, 416, 16624, 1201,
    16519, 7472, 39215, 4263, 3660, 6492, 16572, 3386, 18149, 37864, 803, 5246, 17284, 1390,
    5156, 6410, 7157, 6696, 13987, 3397, 6551, 3662, 11199, 6522, 2380, 4009, 44625, 1093, 4896,
    299, 12333, 3731, 11619, 304, 20671, 33931, 14973, 33820, 4014, 1908, 8730, 13168, 5973,
    1357, 17516, 17051, 361, 23683, 10358, 4249, 5825, 8299, 19688, 8477, 11485, 13271, 4236,
    16934, 1906, 7744, 21821, 599, 6111, 8689, 5468, 7363, 13131, 390, 12476, 1028, 3569, 3881,
    9140, 3351, 8786, 8694, 851, 8906, 10135, 3604, 13596, 2315, 44964, 2670, 1838, 15337, 9118,
    4532, 5427, 12073, 7861, 2975, 31715, 13469, 29829, 1922, 21159, 3921, 516, 273, 16702,
    1119, 3530, 279, 5721, 17978, 1514, 21561, 2924, 2542, 7069, 4128, 6518, 18058, 7090, 833,
    17935, 8295, 25676, 11904, 4179, 18120, 1890, 2674, 41088, 11357, 1400, 13733, 20859, 2963,
    9733, 6115, 8568, 25697, 256, 624, 5552, 22772, 383, 4180, 29689, 564, 16612, 3299, 4903,
    6484, 6072, 18199, 15528, 16635, 7758, 820, 21794, 7708, 13126, 6228, 22578, 31805, 9813,
    38024, 1519, 35735, 1734, 35540, 23448, 4245, 9850, 2030, 57914, 1158, 4478, 15580, 17259,
    24787, 8360, 14151, 6379, 13544, 2112, 560, 7044, 18028, 1800, 19077, 5520, 25593, 824, 431,
    9083, 12466, 3545, 4526, 47006, 1730, 14216, 30755, 9509, 13929, 32092, 1624, 37582, 10399,
    36450, 1162, 5325, 10228, 37387, 24788, 5565, 22539, 499, 12671, 10320, 1569, 14138, 31571,
    35879, 2221, 47604, 3209, 755, 8235, 4725, 16987, 5507, 36464, 2095, 6241, 22733, 1851,
    3546, 2156, 34369, 4760, 565, 7810, 14203, 1275, 8251, 14247, 11987, 8183, 26311, 15779,
    5312, 495, 12672, 4219, 10107, 13370, 38036, 4617, 759, 1674, 16700, 16988, 9749, 33470,
    46682, 3184, 37243, 2066, 1847, 5977, 14116, 17122, 14985, 4284, 2944, 33330, 1279, 26243,
    418, 3298, 2261, 26019, 7133, 17324, 5539, 3035, 4847, 7617, 2040, 5578, 4496, 14285, 2235,
    916, 22565, 7482, 6849, 5481, 977, 22746, 2251, 9055, 3587, 5286, 24657, 46669, 8963, 693,
    712, 2843, 7156, 12512, 24658, 47305, 322, 36880, 12698, 3402, 12723, 3909, 3074, 9397,
    10732, 2134, 16870, 3611, 16858, 2844, 6558, 14777, 7391, 16687, 18145, 7014, 13230, 14792,
    11113, 25867, 5561, 258, 414, 3026, 1004, 6936, 3415, 13246, 7520, 257, 8211, 17739, 3663,
    9407, 13231, 2373, 33962, 259, 3639, 56570, 12385, 1005, 32145, 47592, 295, 37945, 7135,
    9696, 7677, 14103, 2455, 35866, 11477, 23176, 3404, 54985, 1661, 8461, 26245, 34380, 3805,
    8964, 26118, 19639, 748, 925, 2625, 36451, 11996, 7109, 9379, 23570, 7546, 3806, 8562,
    23414, 15427, 1009, 672, 3910, 8430, 6298, 16028, 14826, 7768, 22264, 2973, 7560, 9736,
    4621, 373, 28580, 3048, 3339, 18026, 23072, 952, 3945, 375, 1750, 12684, 11487, 21509,
    33939, 9927, 23670, 374, 725, 9277, 990, 7510, 953, 11400, 25528, 6249, 376, 32146, 47591,
    17140, 731, 2069, 11165, 692, 8976, 2508, 10719, 13417, 16195, 696, 13149, 23791, 6727,
    2583, 1650, 35736, 3600, 17375, 9983, 22837, 24644, 392, 11123, 11831, 20303, 957, 34384,
    32351, 15428, 9031, 4898, 4257, 5323, 37595, 8329, 927, 21820, 1543, 4274, 6327, 4273,
    35878, 8330, 36893, 2246, 6215, 7226, 2169, 1332, 4601, 6254, 2104, 2073, 4744, 14130,
    22759, 4167, 2173, 10226, 6811, 22552, 3378, 4232, 1003, 11162, 9384, 14064, 7148, 10628,
    35749, 6145, 37958, 2141, 2533, 3429, 230, 20473, 34523, 2817, 7287, 10771, 6345, 38037,
    8435, 4821, 11983, 6823, 35680, 14051, 8343, 3867, 231, 9691, 17785, 32171, 9654, 11461,
    5877, 57927, 951, 1117, 1700, 2934, 9045, 2935, 9683, 2242, 2082, 10485, 13518, 18001, 6250,
    2897, 4704, 3130, 26751, 718, 3846, 6340, 4907, 16078, 722, 10654, 4623, 6910, 18002, 7094,
    719, 6863, 28594, 7341, 2347, 3841, 4079, 13545, 20420, 983, 9732, 3348, 35748, 6146, 965,
    17179, 5771, 17946, 16806, 7820, 8912, 8542, 4829, 347, 9730, 16615, 926, 2147, 5484, 405,
    8342, 3702, 10174, 8237, 8958, 26699, 19447, 32533, 47605, 3210, 6772, 21795, 4536, 3974,
    6341, 4715, 4647, 8404, 2229, 16594, 2766, 666, 6810, 21120, 11147, 9723, 19704, 670, 9029,
    4818, 6324, 2869, 19187, 1828, 4911, 13503, 667, 964, 5560, 2573, 4900, 17819, 7484, 9355,
    14803, 931, 8588, 3751, 14804, 2870, 16918, 6428, 1905, 8188, 15703, 9251, 935, 14117, 627,
    8266, 1506, 27558, 1931, 2225, 2034, 9173, 12797, 6806, 13531, 14246, 973, 2543, 591, 5992,
    628, 4890, 6832, 4530, 1611, 5966, 2465, 27338, 12658, 698, 16750, 16974, 1596, 31977, 6106,
    6120, 14839, 16779, 16620, 7654, 12659, 8456, 38023, 738, 16975, 37230, 12438, 3971, 7237,
    2931, 24748, 1465, 7120, 7121, 3022, 7604, 4483, 4861, 7469, 11422, 2238, 7643, 31989,
    14852, 1622, 7143, 31964, 309, 6107, 6119, 3061, 5129, 8316, 8304, 7485, 435, 13217, 39956,
    9238, 1936, 616, 14437, 11922, 13499, 5812, 13218, 4937, 7208, 872, 24761, 282, 7122, 7664,
    5315, 54, 19441, 3689, 816, 1802, 2412, 1331, 10479, 6471, 8548, 8459, 3132, 5617, 1517,
    4803, 3361, 9114, 15515, 6733, 8017, 612, 3856, 16377, 9535, 1648, 21924, 14658, 6535, 876,
    24736, 17088, 17959, 4950, 660, 534, 1912, 1637, 5162, 23188, 773, 24124, 8507, 29530,
    26451, 5621, 18092, 4244, 732, 685, 13165, 35865, 7213, 3009, 4613, 4731, 8821, 10213, 7200,
    2277, 5289, 3365, 5510, 32949, 18611, 8512, 551, 7239, 6330, 12554, 6675, 807, 751, 18119,
    13505, 842, 5390, 32796, 8650, 11090, 617, 14385, 4262, 6176, 15206, 8230, 34542, 13161,
    12741, 22145, 29166, 12946, 811, 8825, 11982, 13192, 8469, 4855, 11135, 16233, 15567, 6683,
    27184, 3341, 4038, 8702, 15932, 2517, 3840, 7471, 3450, 3793, 10635, 7799, 8276, 5181, 409,
    17626, 15271, 1491, 8707, 590, 357, 20080, 19420, 6488, 9704, 846, 8838, 7407, 1371, 3830,
    1480, 20156, 5006, 32562, 31730, 33290, 5725, 5790, 32261, 1813, 768, 1379, 4663, 724,
    18585, 12381, 8581, 4636, 17057, 17949, 5440, 586, 4624, 17950, 1324, 850, 34055, 6767,
    10726, 9096, 4210, 8126, 10720, 5704, 5472, 1579, 19060, 3441, 1776, 1968, 529, 2334, 11413,
    912, 4539, 11582, 525, 669, 32469, 6278, 17092, 5420, 3652, 5116, 1879, 2774, 6531, 19001,
    7862, 10934, 3333, 3480, 10263, 8965, 13673, 3152, 3653, 8919, 33606, 7656, 4192, 521, 9046,
    14869, 5407, 5794, 785, 38943, 14502, 18780, 2976, 8672, 16364, 12719, 16888, 5929, 26092,
    18212, 23916, 6206, 607, 4310, 11389, 13617, 7812, 9398, 8289, 14208, 2386, 14791, 243,
    25684, 16882, 8847, 7027, 25685, 659, 6949, 26998, 11100, 245, 5574, 2264, 991, 7927, 14779,
    2203, 10359, 244, 19311, 17557, 8198, 9420, 3650, 8443, 6545, 246, 33949, 21691, 3626, 992,
    22967, 3087, 9697, 8146, 2121, 1493, 23982, 9618, 21055, 3417, 32159, 34367, 26232, 16181,
    17161, 8977, 735, 19652, 3984, 2468, 25520, 9392, 3819, 18817, 18292, 8549, 996, 15414,
    9290, 3598, 17207, 10836, 7573, 3350, 17899, 360, 4634, 17962, 1763, 57104, 3326, 939,
    16728, 362, 799, 604, 12685, 18246, 10330, 9940, 13464, 17963, 16041, 441, 940, 4312, 25034,
    11387, 363, 6236, 3989, 2056, 17130, 7760, 32371, 10706, 683, 16182, 23778, 17530, 2596,
    6714, 2521, 54867, 3613, 24839, 11270, 1530, 5706, 34204, 11136, 944, 20316, 32338, 34371,
    2597, 9385, 2281, 2043, 8380, 4630, 6133, 24683, 34510, 20486, 7300, 3506, 6358, 10758,
    47318, 3183, 2662, 4834, 17961, 6836, 8448, 3997, 218, 16698, 12468, 9678, 9667, 12424,
    5890, 11474, 966, 5355, 938, 9684, 14221, 7773, 8523, 2360, 4702, 2910, 6237, 13829, 4717,
    705, 18210, 2212, 6328, 6923, 4091, 16090, 709, 16091, 7118, 4894, 8417, 706, 3883, 17297,
    6850, 3165, 10346, 4092, 16581, 970, 20407, 11110, 14182, 6132, 7833, 24684, 8555, 8925,
    334, 4816, 14002, 22080, 47019, 1142, 2108, 2495, 3675, 10187, 3715, 8971, 8224, 335, 32520,
    19460, 36463, 5784, 30713, 6785, 17091, 4549, 9368, 13074, 653, 7732, 37578, 6797, 7953,
    1841, 657, 19691, 4831, 8002, 2882, 6337, 18225, 13075, 654, 24800, 2781, 2560, 5573, 4208,
    4913, 918, 14816, 3764, 8575, 15453, 15441, 3312, 6315, 8989, 3767, 11121, 6314, 16896,
    4689, 29919, 12749, 3454, 2125, 9006, 3958, 13139, 12139, 9005, 3558, 16897, 8482, 4872,
    12750, 10333, 6793, 986, 3222, 2983, 2530, 2160, 960, 4543, 6819, 5979, 7591, 27325, 2452,
    1918, 6415, 4747, 9264, 9762, 3197, 922, 7174, 8253, 1944, 27545, 1000, 9186, 396, 4860,
    4484, 14298, 2047, 14259, 2199, 9068, 11045, 2856, 12525, 4676, 3922, 4885, 2857, 422,
    10882, 28494, 18468, 1830, 603, 8889, 6067, 5734, 1366, 6319, 24744, 5142, 699, 859, 4314,
    11308, 6784, 10112, 3973, 40112, 3008, 3897, 14181, 15882, 6421, 5604, 4153, 3923, 8495,
    8222, 18214, 1769, 4608, 13360, 8613, 1756, 24215, 15870, 3502, 11337, 18091, 28230, 4230,
    863, 9212, 23175, 8695, 15373, 18245, 5608, 1363, 3754, 5336, 6301, 11134, 4287, 4286, 6302,
    2259, 4730, 4614, 2086, 14143, 2186, 14156, 8938, 11175, 14077, 5064, 9018, 2154, 3442,
    9303, 1895, 538, 6897, 9865, 16936, 7588, 11070, 794, 3080, 2947, 2948, 2255, 10498, 24228,
    2491, 32793, 6713, 11621, 30664, 6163, 5531, 5077, 31474, 13664, 23600, 9019, 17023, 8264,
    16543, 3892, 798, 5768, 3223, 13828, 5136, 3467, 6753, 8170, 8875, 6629, 23115, 10280,
    30453, 17608, 1747, 2687, 18741, 3572, 11108, 11062, 6824, 28493, 11142, 15011, 3372, 14450,
    577, 6845, 35238, 2917, 2216, 13508, 1262, 13591, 1223, 15311, 10668, 32549, 6408, 8117,
    1897, 20587, 487, 7667, 9036, 23353, 8412, 1873, 3869, 573, 3028, 737, 9028, 10687, 30601,
    837, 6678, 14073, 1218, 14052, 8113, 9002, 11840, 9150, 9502, 4347, 2804, 5051, 33925, 1007,
    8393, 5964, 512, 8447, 17142, 2800, 3196, 17820, 5032, 14234, 4012, 9876, 1240, 4053, 35615,
    1228, 14398, 578, 3389, 13136, 6744, 8747, 32501, 12762, 508, 4158, 7173, 9017, 3688, 772,
    9329, 6975, 1361, 9463, 25463, 8659, 4673, 4051, 17447, 25901, 24337, 25464, 6193, 13011,
    1957, 39047, 15512, 2900, 2891, 11618, 25720, 2093, 11926, 7265, 6068, 15922, 1231, 27541,
    8564, 21197, 3884, 1878, 4822, 9088, 5058, 2236, 6280, 16088, 6124, 12459, 2270, 3866,
    27593, 10291, 1641, 22994, 22225, 882, 5471, 9899, 15513, 2562, 2553, 11541, 17701, 728,
    15646, 8161, 1377, 39826, 15531, 4313, 2196, 21158, 764, 2528, 8733, 12056, 10940, 6483,
    682, 27632, 9589, 1616, 9970, 32728, 6652, 8781, 8589, 6707, 6462, 5188, 16606, 8334, 2748,
    1541, 2132, 19040, 8945, 34679, 7521, 597, 17466, 5414, 5316, 26620, 1486, 1085, 2223,
    15449, 7848, 7669, 14699, 1765, 2765, 4548, 26890, 5885, 34705, 16752, 9084, 57427, 35095,
    7638, 9054, 8824, 8916, 5821, 9605, 1511, 39060, 22419, 689, 32053, 1883, 5924, 19092,
    16325, 3025, 6587, 4335, 8302, 16554, 17285, 2091, 503, 2887, 15526, 11554, 2904, 24905,
    3038, 1167, 11153, 17869, 6505, 3647, 3373, 16559, 962, 21237, 15880, 3949, 1403, 33157,
    55843, 3582, 20768, 2240, 9515, 3649, 6564, 6405, 11186, 344, 28544, 2549, 15525, 11631,
    2566, 11800, 3871, 17947, 8717, 1921, 5960, 19564, 22968, 1456, 19701, 14233, 3104, 8312,
    40191, 3517, 17223, 11498, 33873, 869, 5409, 16992, 3043, 39683, 1612, 19274, 9066, 2939,
    2943, 48809, 4558, 8773, 2974, 4166, 9071, 17233, 10151, 2135, 57440, 30677, 26750, 4326,
    4545, 9105, 12060, 12486, 1738, 22394, 11347, 923, 16764, 40841, 1909, 2609, 16895, 33898,
    4909, 7234, 11868, 584, 40164, 5279, 12624, 6401, 16140, 4282, 4278, 31988, 4096, 1508,
    11749, 2752, 20629, 16685, 23071, 21783, 1387, 11370, 1586, 890, 4130, 13207, 6102, 29786,
    13903, 19118, 30807, 17083, 4300, 52371, 11447, 29787, 10837, 20405, 6639, 12260, 5963,
    34314, 370, 5556, 2653, 594, 56597, 8900, 15724, 5569, 17272, 8197, 7898, 6172, 22829, 7940,
    3156, 18702, 24922, 7081, 17182, 988, 8572, 20561, 23999, 2393, 774, 15893, 26131, 28232,
    17702, 14294, 32358, 2341, 5130, 24255, 2636, 936, 5816, 7894, 6224, 1288, 3289, 1721, 6223,
    694, 23401, 18390, 3829, 2406, 4000, 28310, 8585, 1001, 13227, 16713, 949, 5829, 18309,
    33658, 1599, 9124, 3001, 1475, 28763, 7719, 11853, 2739, 4304, 15477, 4191, 2731, 6238, 596,
    2909, 4101, 10707, 1219, 22211, 16985, 2354, 1061, 8867, 8655, 1748, 7131, 9719, 4922, 5052,
    2127, 8145, 15295, 22855, 1485, 13362, 4899, 17612, 3962, 40867, 7052, 8718, 20106, 6563,
    31870, 10057, 10954, 17597, 34217, 18910, 13933, 26062, 7895, 6262, 1145, 1677, 1864, 10869,
    6263, 655, 8848, 9979, 27658, 3996, 10138, 15831, 23423, 610, 2770, 2649, 27268, 10164,
    7523, 4182, 4783, 570, 26687, 3559, 3092, 4317, 5479, 17090, 21250, 5907, 569, 16221, 4298,
    15620, 1129, 8159, 4604, 17584, 14320, 26768, 2136, 17909, 46420, 3888, 23388, 13894, 5859,
    64513, 934, 29140, 22328, 4052, 14892, 4336, 57481, 13443, 777, 13746, 34529, 5933, 12555,
    1726, 17998, 19051, 21900, 8408, 6171, 8407, 15516, 1338, 1899, 26738, 4963, 2515, 4924,
    21068, 7199, 11069, 23747, 7494, 3828, 12268, 3129, 8724, 2145, 3714, 14489, 32104, 26464,
    1855, 9225, 33132, 11675, 1949, 2065, 11240, 54529, 5401, 33588, 6392, 9784, 29285, 17311,
    31402, 7716, 844, 4999, 994, 1073, 32246, 296, 15750, 11499, 5947, 12933, 15363, 15376,
    6858, 14129, 3170, 17833, 17018, 19173, 11381, 815, 40945, 17040, 16602, 16921, 1969, 21601,
    11748, 9759, 6561, 4805, 30700, 6631, 13454, 5664, 32078, 9631, 16843, 2322, 13604, 21809,
    17454, 6668, 31741, 3999, 702, 6622, 5950, 23266, 2445, 1138, 10239, 2627, 9123, 7420, 2075,
    4330, 2497, 4168, 1580, 17174, 650, 8754, 8239, 7225, 7586, 13222, 6509, 23214, 2986, 11974,
    8887, 56376, 15737, 1241, 29636, 8265, 10003, 40607, 15503, 8210, 17304, 8811, 19131, 881,
    3966, 11434, 50980, 9901, 10850, 23973, 8667, 21145, 1717, 1573, 7518, 5547, 5548, 668,
    1292, 10622, 17954, 9563, 26803, 9110, 6496, 8056, 24883, 6459, 5342, 19082, 1298, 1466,
    3034, 8018, 1856, 1489, 5000, 7169, 13687, 17727, 20067, 10798, 54673, 10966, 13635, 1812,
    23189, 30248, 623, 23384, 8815, 4574, 7053, 1606, 2991, 8503, 12455, 1512, 6705, 21016,
    3516, 7757, 14099, 53567, 19755, 13321, 8214, 50187, 16660, 15945, 21549, 4474, 4002, 3947,
    5480, 2458, 11844, 2257, 6609, 715, 7614, 5937, 1860, 3536, 7517, 5587, 5586, 681, 1149,
    5677, 24896, 8226, 23410, 609, 2558, 6251, 15308, 8950, 10410, 9004, 22198, 16972, 663,
    8741, 9873, 21822, 8981, 32936, 1111, 3905, 18175, 2249, 7495, 3992, 10125, 9095, 41243,
    21575, 8770, 32079, 10902, 5375, 2510, 853, 608, 12052, 11396, 4337, 8379, 20223, 10550,
    11201, 50343, 8262, 7070, 6316, 13430, 29533, 1917, 30794, 1402, 1567, 17846, 20158, 25364,
    9917, 8928, 5612, 9119, 2272, 32376, 10745, 3244, 1358, 2062, 1958, 10250, 5911, 5432,
    40749, 5781, 18637, 37045, 16726, 21419, 5394, 39099, 17623, 5999, 1699, 1764, 1192, 31883,
    35355, 4887, 2978, 38604, 3412, 17948, 686, 14800, 23098, 1312, 673, 3039, 13209, 5652,
    12355, 1154, 15883, 8859, 9027, 5747, 33912, 17052, 880, 16711, 10398, 52423, 9797, 8043,
    7078, 22368, 16816, 7443, 5563, 3116, 8745, 31051, 5012, 4044, 1495, 568, 37188, 2478,
    11634, 1795, 26942, 8438, 17972, 12572, 7992, 5071, 48744, 6681, 13113, 2400, 21328, 20487,
    19069, 13802, 32015, 19664, 9135, 3780, 39072, 24774, 5760, 7354, 5227, 942, 11662, 58196,
    18015, 1788, 8890, 1280, 5363, 1595, 22185, 32716, 26725, 8794, 16634, 20162, 19446, 12815,
    6432, 3493, 24775, 16218, 4925, 19482, 8574, 30079, 2164, 1502, 5494, 17873, 2143, 39034,
    9999, 11096, 2335, 15651, 4116, 19642, 2679, 5299, 4206, 13909, 9041, 2179, 9726, 22094,
    10655, 26971, 4640, 16439, 13336, 5454, 4271, 20317, 171, 2248, 32767, 9043, 1801, 2234,
    3218, 4497, 440, 6862, 2768, 2060, 1139, 14272, 4415, 4297, 3859, 11058, 878, 26012, 1577,
    2128, 1270, 6012, 26492, 19694, 7250, 1777, 1112, 11412, 3257, 7693, 1271, 879, 17934, 656,
    20304, 10044, 4178, 5916, 6264, 583, 8808, 21133, 7276, 17798, 23557, 2114, 5155, 6356,
    6420, 17599, 3321, 35043, 50434, 26701, 20421, 5419, 2664, 14090, 4441, 19148, 3983, 26621,
    1236, 16530, 8903, 1376, 1337, 32378, 1297, 9069, 13323, 1775, 21107, 3854, 530, 13881,
    40840, 18129, 28685, 34042, 1778, 2839, 13097, 6336, 7589, 3113, 2099, 4187, 13803, 10332,
    7186, 11917, 1814, 14476, 11818, 18442, 22842, 9030, 15258, 10590, 4777, 4649, 15219, 16556,
    2570, 26700, 1680, 2285, 5446, 6473, 13115, 29546, 3157, 8902, 13942, 10133, 19070, 4348,
    22980, 10096, 3108, 158, 54815, 15765, 5026, 9093, 3428, 33275, 7966, 9157, 2463, 1074,
    21807, 321, 1947, 1305, 1946, 813, 4743, 415, 2105, 4389, 929, 852, 6798, 3885, 14169, 3192,
    8951, 1113, 5351, 2794, 6771, 1143, 10615, 814, 1531, 38917, 12806, 19160, 9085, 13361,
    1476, 30690, 17714, 16949, 5428, 5981, 8109, 5743, 14086, 9990, 16690, 16647, 1309, 1942,
    1310, 1048, 34030, 9953, 21760, 7096, 11356, 6589, 53788, 9101, 23644, 9593, 8445, 21562,
    21445, 19967, 5090, 5201, 1971, 3946, 2507, 1789, 9316, 8783, 750, 7380, 6453, 13201, 787,
    11524, 15113, 8978, 15554, 25854, 4627, 1938, 504, 11961, 17039, 6016, 7185, 41022, 8030,
    401, 31909, 5550, 41009, 24189, 10642, 5389, 16335, 12021, 9133, 37175, 8878, 5290, 3976,
    14195, 3283, 23986, 17148, 11109, 16390, 16416, 3790, 17428, 9015, 8444, 981, 9522, 7172,
    17027, 20143, 12814, 3160, 7627, 11166, 4467, 2638, 19147, 4161, 7066, 23085, 5492, 9544,
    3676, 16894, 14908, 63175, 14943, 3998, 5341, 9098, 3529, 6691, 1761, 5755, 23903, 18017,
    6665, 4185, 7680, 1697, 26274, 14015, 3882, 27879, 12369, 16946, 57390, 13620, 9151, 19655,
    7040, 11409, 17493, 17310, 8152, 3151, 870, 5589, 16002, 2413, 21991, 33158, 39969, 11264,
    17258, 17884, 19953, 19508, 1743, 29051, 2618, 28542, 1975, 1868, 1286, 1884, 2268, 788,
    6962, 1619, 2469, 11317, 6837, 1116, 8510, 1047, 8212, 7628, 6225, 33431, 26985, 33717,
    7446, 33704, 428, 8587, 4311, 6745, 28672, 17118, 19716, 9821, 17571, 9847, 11122, 1621,
    25021, 4938, 1301, 11957, 11956, 763, 17044, 12775, 4142, 877, 18429, 21367, 12531, 5651,
    8178, 6210, 8420, 1660, 32923, 2205, 15310, 22458, 28557, 13794, 6486, 19083, 25476, 10008,
    16933, 10589, 19225, 17011, 4064, 5097, 2477, 25477, 7170, 8731, 4650, 7734, 22281, 54660,
    8735, 8484, 6501, 20431, 1284, 12299, 1311, 6780, 40814, 6579, 2818, 28714, 18650, 39775,
    18123, 542, 9058, 23748, 8054, 21132, 33002, 9472, 2222, 8196, 26894, 9094, 57468, 1397,
    18272, 8668, 5756, 15410, 26105, 8234, 14868, 1153, 25373, 17313, 4209, 19454, 1974, 24891,
    1392, 19740, 7640, 4309, 4637, 17388, 19157, 8835, 8772, 8802, 14207, 3322, 33496, 21600,
    11801, 5505, 16920, 17921, 31064, 5025, 8382, 39749, 10022, 14580, 19876, 7533, 33222, 7065,
    16467, 9199, 11543, 12411, 13103, 13841, 11909, 4198, 3832, 3017, 7989, 10161, 3465, 1710,
    3972, 13188, 6735, 474, 15529, 33079, 14671, 11433, 11369, 8774, 8340, 22133, 39294, 7079,
    1642, 13633, 2648, 18277, 4718, 13434, 27145, 6499, 9886, 33938, 4341, 13877, 17506, 21471,
    8561, 20340, 3823, 3164, 883, 1104, 11486, 7222, 8603, 35251, 17831, 56428, 974, 2688,
    50304, 19924, 5364, 2239, 21769, 45132, 2796, 17897, 843, 34718, 9528, 3836, 3961, 35056,
    15076, 23474, 2631, 9554, 9145, 20872, 16790, 8143, 5350, 18845, 828, 15466, 4587, 3311,
    831, 26025, 4120, 3030, 28750, 21223, 5497, 16959, 1645, 2918, 2490, 8148, 8434, 5329,
    33301, 61277, 10785, 1804, 4678, 2783, 39281, 28659, 32741, 1362, 1232, 22107, 7182, 14840,
    10269, 8122, 3880, 7747, 18305, 31222, 9008, 5362, 2244, 13854, 29623, 1910, 2115, 17920,
    4454, 3100, 17941, 8108, 17882, 17675, 10382, 4170, 9814, 7459, 15489, 55050, 8028, 32300,
    829, 12998, 1184, 1970, 6627, 3986, 16776, 4686, 23461, 21782, 1948, 711, 4325, 40177,
    11970, 595, 16749, 13825, 1725, 14634, 8399, 8249, 49602, 6380, 16283, 55947, 17430, 21380,
    18988, 6018, 56259, 5786, 1615, 9743, 8914, 17362, 9505, 4321, 2218, 7406, 1283, 11316,
    22471, 14723, 17497, 26729, 9164, 5445, 20149, 856, 4757, 10083, 22850, 6644, 8328, 26178,
    29038, 17614, 1175, 9541, 11330, 11239, 33509, 39748, 8366, 4205, 8395, 24597, 8743, 8822,
    15087, 841, 16550, 8833, 21458, 9785, 11083, 2895, 5576, 20574, 38956, 8911, 13521, 4193,
    34081, 9112, 18494, 2092, 5221, 15885, 9862, 18965, 8044, 4258, 15607, 9748, 18338, 14164,
    6511, 3933, 13024, 2195, 5533, 39982, 10321, 14229, 18884, 7458, 5338, 7885, 20045, 1348,
    9771, 6093, 15857, 1582, 17818, 7625, 8355, 19935, 7508, 1880, 8888, 17005, 1197, 16607,
    5435, 15792, 9576, 6094, 1960, 15024, 1687, 8015, 8356, 22315, 10278, 2516, 6679, 12637,
    5331, 14998, 1834, 1306, 825, 3205, 1345, 427, 3574, 2755, 2039, 1126, 4848, 4402, 3504,
    865, 7630, 1773, 1609, 840, 3360, 5985, 12711, 1099, 12736, 8182, 13568, 866, 13569, 23128,
    3014, 14931, 20015, 6353, 9553, 4782, 8353, 5305, 14424, 13233, 6354, 10255, 3975, 17467,
    8748, 10070, 17610, 2651, 3352, 4428, 3595, 33951, 26479, 1951, 14921, 21263, 16234, 15633,
    3920, 5769, 42260, 17668, 543, 2078, 22341, 4349, 13916, 1266, 1504, 1125, 9860, 12845,
    20032, 24272, 1739, 1684, 3143, 10681, 8261, 3142, 3843, 50395, 30143, 32781, 4276, 23318,
    1635, 31623, 26854, 28607, 26841, 7729, 857, 10967, 8487, 9342, 1815, 12034, 1930, 308,
    1681, 1556, 800, 11709, 402, 3391, 4376, 2996, 839, 4600, 3872, 2170, 3179, 4870, 1100,
    7187, 1130, 11061, 801, 7161, 12959, 1869, 12972, 20600, 2503, 13037, 6692, 18000, 7507,
    35836, 32143, 16478, 1713, 1035, 12035, 1060, 5354, 19846, 6498, 1903, 2601, 18013, 14372,
    56167, 2476, 8471, 15193, 20236, 283, 1576, 53294, 12008, 8729, 3870, 11710, 9782, 23111,
    5903, 1349, 15896, 3376, 4025, 9134, 6662, 7456, 36850, 28180, 17915, 3953, 3963, 3665,
    3270, 3895, 5168, 2936, 30934, 28727, 61056, 31132, 1478, 26790, 37591, 622, 9485, 27115,
    39489, 12767, 18978, 31513, 1166, 2153, 4222, 4221, 4322, 8600, 8327, 2321, 6884, 5732,
    5461, 18572, 17964, 8979, 6628, 22224, 22146, 7092, 2661, 9905, 32488, 19872, 4354, 14645,
    8980, 10915, 4588, 10139, 5247, 8446, 17844, 2183, 2775, 5377, 41804, 776, 13014, 40138,
    16803, 13477, 18858, 15479, 26688, 1340, 775, 5485, 17105, 54842, 2753, 7195, 1103, 11309,
    1034, 7786, 3585, 5103, 10395, 30170, 28256, 17764, 8041, 2640, 13235, 32301, 1959, 8139,
    14647, 1893, 15794, 30089, 19534, 39619, 8927, 8755, 21639, 1296, 15360, 11608, 11569,
    18767, 55089, 8067, 4218, 16351, 15100, 14879, 9125, 21678, 3147, 1396, 3309, 8496, 1799,
    10281, 31871, 2226, 12408, 8719, 32521, 24462, 4493, 10061, 18051, 571, 18142, 14684, 57260,
    9892, 2227, 3374, 18271, 5511, 12819, 33288, 17376, 3040, 35368, 34263, 3792, 13516, 34393,
    2960, 20983, 17574, 3637, 1658, 27294, 11948, 18290, 38767, 17143, 12342, 21750, 3725, 1923,
    8201, 3738, 2231, 3686, 1319, 3556, 9475, 16804, 32403, 25815, 48653, 10294, 2096, 5406,
    13807, 4766, 7039, 830, 22004, 20093, 4740, 10538, 1188, 2097, 8209, 6601, 9879, 34119,
    13375, 22270, 6031, 4701, 4714, 1389, 1528, 4610, 5310, 39638, 11814, 16736, 13348, 30583,
    3481, 4328, 28191, 30115, 16777, 21490, 13766, 3324, 2101, 17031, 34744, 28321, 4248, 26334,
    34211, 3426, 9146, 32267, 2952, 2792, 9592, 17740, 39788, 4753, 10229, 4195, 32404, 3519,
    13274, 3584, 4597, 955, 3439, 2718, 11556, 29101, 28711, 921, 9918, 56233, 1589, 17481,
    4127, 1593, 11679, 11252, 1590, 8924, 28204, 1964, 11933, 4705, 22238, 8602, 34484, 2166,
    33716, 2118, 3673, 7117, 4857, 4031, 33223, 987, 12920, 33236, 12208, 3377, 10268, 4844,
    23362, 11188, 4239, 3857, 10009, 23657, 32377, 3741, 3169, 32624, 3387, 9853, 22432, 32091,
    1459, 1327, 13856, 5349, 35381, 4912, 17479, 1463, 32963, 2273, 5860, 34262, 1460, 13725,
    15502, 55075, 2036, 11848, 9082, 19404, 20265, 41114, 16686, 14918, 36863, 16778, 7911,
    4224, 18233, 8680, 2949, 10203, 4211, 17809, 868, 17128, 34158, 4197, 4712, 4679, 17544,
    18188, 9964, 12375, 17753, 37201, 20171, 11822, 8186, 6449, 8871, 41204, 27149, 11952, 4961,
    3118, 4948, 14567, 8709, 9153, 33561, 6739, 33662, 13889, 2049, 17337, 13534, 16589, 20853,
    3944, 1962, 19937, 20408, 8915, 54816, 3979, 2247, 11277, 4037, 3987, 11688, 37500, 9632,
    3779, 16866, 9159, 34106, 21354, 8937, 13479, 34146, 10817, 14814, 22445, 28698, 17152,
    5990, 9060, 14528, 29699, 2923, 18793, 7703, 10216, 13401, 36590, 2950, 1712, 18234, 9148,
    20886, 31975, 3171, 14944, 11253, 5303, 10005, 34588, 11360, 23349, 15152, 3053, 7104, 4886,
    2489, 11394, 8472, 17494, 32989, 20814, 1482, 8761, 7549, 7064, 25849, 8458, 7001, 1539,
    2831, 20755, 27853, 12841, 1344, 5986, 17181, 17102, 4184, 13283, 14593, 32924, 8421, 32702,
    10518, 17416, 6433, 6440, 3334, 18273, 8432, 34965, 19521, 17116, 2177, 20041, 2970, 11723,
    6537, 1916, 50317, 19766, 14905, 8832, 3091, 9827, 4295, 8956, 2988, 19105, 7057, 5998,
    19352, 16998, 21477, 9680, 1487, 4246, 6588, 18192, 17772, 18264, 8872, 1210, 18298, 14194,
    12165, 12047, 1786, 52436, 29387, 27918, 7209, 4692, 7042, 13547, 4699, 24757, 31662, 2961,
    22244, 12538, 7378, 18025, 2157, 13890, 3777, 4119, 16023, 8904, 6363, 17265, 5751, 19703,
    8601, 14660, 11835, 19603, 33833, 16400, 30986, 21887, 9914, 3144, 4289, 6185, 3131, 581,
    14025, 3478, 4172, 3491, 20742, 16296, 8886, 13413, 17165, 4662, 3093, 19079, 21184, 34809,
    5380, 8614, 19690, 11517, 15659, 1350, 8862, 17103, 3002, 7497, 20873, 6667, 5284, 39268,
    15232, 14028, 1608, 9106, 3138, 7313, 1578, 13790, 4351, 13181, 1929, 14554, 6290, 12273,
    23366, 8403, 6394, 19313, 33015, 4237, 15139, 9840, 32976, 6485, 22868, 3571, 8742, 5298,
    1808, 32280, 10317, 19820, 8156, 2260, 8690, 16596, 10765, 17767, 22017, 7721, 5738, 17232,
    17830, 9433, 16036, 8984, 9394, 1500, 9020, 1318, 21204, 24528, 5091, 4107, 6641, 6350,
    4315, 39137, 8199, 1314, 4283, 12100, 8529, 30570, 9138, 12559, 4270, 5847, 17219, 7252,
    7051, 1257, 10602, 55101, 1632, 1253, 32897, 10570, 10537, 29335, 2735, 1934, 1956, 2701,
    21912, 4132, 7924, 17621, 3879, 12594, 1760, 3139, 18130, 2138, 1791, 12875, 54789, 33730,
    4796, 9081, 7196, 3027, 31819, 16270, 1322, 17561, 4951, 4522, 41048, 20769, 4666, 26968,
    13753, 17298, 18285, 12095, 8864, 2779, 2151, 17468, 22120, 22846, 17894, 4343, 17390, 4764,
    27398, 3347, 19950, 35017, 17347, 21913, 3844, 6759, 3004, 11173, 34822, 864, 12204, 13712,
    23184, 17636, 2283, 19261, 10369, 20327, 5695, 9912, 17129, 16673, 4751, 5699, 17802, 33209,
    4506, 33418, 32625, 14019, 20885, 8095, 37214, 10021, 1505, 8642, 621, 21341, 4231, 17480,
    4792, 12372, 8455, 4302, 4873, 13388, 1193, 39437, 2456, 31884, 7888, 23539, 8451, 11290,
    65504, 18804, 8732, 556, 13389, 13304, 6701, 32534, 1388, 5691, 17403, 16789, 2148, 968,
    14891, 2149, 57597, 3621, 2908, 802, 5625, 57273, 20483, 6603, 13142, 11683, 19859, 2144,
    32492, 18090, 12451, 4353, 15464, 7404, 16127, 1554, 3634, 28087, 19339, 13440, 555, 5367,
    34276, 8135, 32027, 19350, 9147, 23500, 4338, 33703, 22381, 16856, 23132, 3015, 15570, 1098,
    8416, 3624, 6304, 17928, 33719, 5466, 1557, 4133, 7706, 13555, 8910, 867, 6184, 3296, 28531,
    3936, 28532, 4519, 2571, 8807, 13998, 2252, 8497, 20911, 29374, 1920, 2253, 12308, 48874,
    6757, 15256, 7278, 517, 5639, 854, 6197, 3335, 12503, 1171, 28737, 13765, 2788, 65178, 789,
    1803, 7695, 18251, 2520, 22916, 26815, 13248, 3105, 19714, 2830, 29649, 4727, 29650, 15541,
    2623, 13538, 582, 8681, 6700, 11187, 32419, 3000, 17895, 34509, 3494, 5524, 18316, 790,
    3337, 9966, 55427, 1383, 1943, 5297, 14697, 2982, 8820, 4117, 6388, 3158, 17168, 15999,
    17220, 1955, 16517, 10804, 33847, 5742, 12178, 21899, 54803, 18156, 3126, 1821, 21698, 4247,
    1384, 12832, 1488, 5324, 6447, 21432, 1552, 6988, 20944, 12693, 11227, 28295, 10505, 32819,
    21191, 12481, 2605, 2614, 12312, 5117, 16633, 6704, 19707, 18806, 6615, 6003, 23652, 10524,
    3935, 1474, 9693, 16646, 13686, 33742, 1638, 16504, 6419, 4288, 31324, 5458, 27502, 11088,
    5864, 17351, 31754, 1925, 6029, 55635, 8615, 20756, 11649, 2190, 25957, 4063, 1565, 7326,
    6371, 8813, 1227, 9875, 9067, 16155, 2761, 56363, 6025, 7130, 21990, 10752, 4065, 3106,
    18286, 37981, 3827, 4217, 17546, 1513, 9381, 3013, 18081, 31844, 16403, 16763, 5537, 8899,
    16309, 11230, 16739, 27242, 17089, 4340, 20898, 10557, 17778, 17402, 7083, 18155, 9086,
    24012, 3390, 4272, 5712, 3957, 15063, 9016, 18284, 23934, 6445, 30557, 2957, 8263, 15844,
    26755, 11420, 2644, 2450, 7055, 33093, 4561, 2052, 31858, 2131, 2209, 4770, 2286, 31597,
    6458, 4275, 8923, 7781, 2937, 9161, 9550, 6687, 13309, 14541, 17054, 32391, 8096, 3532,
    10603, 7260, 3543, 9003, 6688, 13240, 17022, 15269, 5719, 11043, 11944, 13194, 20470, 11913,
    19326, 33119, 8250, 8703, 16908, 1498, 34497, 11459, 1499, 2557, 4480, 8248, 12879, 3728,
    8431, 32611, 5638, 11972, 21587, 2896, 4296, 1602, 1603, 34275, 18094, 17078, 8500, 40827,
    8692, 3539, 19161, 2675, 7901, 6046, 12607, 1258, 29909, 5453, 5678, 5994, 6289, 18038,
    4018, 3894, 1206, 23358, 5065, 1323, 7183, 1790, 8282, 7536, 12892, 22314, 24268, 3293,
    19940, 3597, 8522, 4011, 1933, 9992, 1842, 28674, 16791, 8165, 8394, 8953, 2705, 5195, 5415,
    11376, 3052, 2740, 17681, 40671, 12581, 12113, 30999, 4233, 8939, 20474, 3292, 6042, 9109,
    7273, 1375, 1336, 5799, 12048, 12840, 36876, 5285, 11670, 4103, 11103, 33340, 3766, 13027,
    3831, 8885, 6510, 11722, 1881, 8516, 1972, 19459, 3540, 8277, 8288, 10648, 4252, 8269, 2666,
    4050, 1827, 15727, 3896, 5311, 3514, 9073, 2922, 20951, 2348, 14894, 3721, 6524, 379, 18065,
    8227, 999, 8240, 1012, 8696, 3527, 19073, 21704, 2494, 8409, 4285, 2805, 7679, 8290, 17843,
    8823, 3734, 6407, 6640, 16818, 22833, 5758, 28219, 8536, 15401, 17323, 4234, 15740, 1840,
    5953, 961, 5940, 948, 5745, 2547, 7745, 16415, 3463, 5078, 13919, 2361, 8943, 4226, 5337,
    2481, 6748, 1401, 4204, 9070, 11446, 7666, 2451, 17676, 3526, 2813, 9888, 6536, 10921, 6514,
    8698, 32234, 4024, 3722, 8826, 16507, 3513, 6277, 1932, 8172, 2965, 6033, 4005, 16494, 2464,
    8990, 8004, 11930, 1945, 4259, 15830, 2534, 1245, 3735, 8860, 6654, 5104, 5795, 8422, 8238,
    2987, 3970, 37240, 7433, 6267, 14917, 25030, 16563, 29012, 11762, 8069, 17508, 7937, 30274,
    8932, 2657, 7068, 13698, 8851, 13322, 4114, 9158, 6527, 6720, 16402, 8810, 5938, 26049,
    1816, 1907, 12203, 7601, 8381, 3125, 28724, 6276, 6523, 8685, 7212, 13335, 17415, 29324,
    7991, 6343, 25892, 3320, 39580, 23171, 5665, 8940, 12074, 11775, 1180, 13023, 3385, 9033,
    23566, 31171, 8854, 6406, 6055, 5808, 6653, 2913, 25862, 12065, 1751, 4299, 13036, 8760,
    13685, 6616, 25893, 17377, 23565, 12191, 8147, 17507, 12190, 6434, 15843, 5912, 17378, 9137,
    13699, 12061, 21282, 20697, 21165, 20801, 8160, 2610, 5925, 4169, 3948, 9057, 6393, 3117,
    17079, 11943, 17872, 13906]

/-- The class-representative index for the `i`-th element of `G`, packed in the low
residue mod `13` of `classCodeArray[i]`. -/
def classRepIndex (i : Fin 6048) : Fin 13 :=
  ⟨(classCodeArray.getD i.val 0) % 13, Nat.mod_lt _ (by decide)⟩

/-- The conjugator index for the `i`-th element of `G`, packed in the high part of
`classCodeArray[i]`. -/
def classConjIndex (i : Fin 6048) : Fin 6048 :=
  fin6048 ((classCodeArray.getD i.val 0) / 13)

/-- For every nonidentity element `g = element i`, conjugating the listed class
representative `classRepG (classRepIndex i)` by the listed conjugator `element
(classConjIndex i)` yields `g` exactly. -/
theorem class_conj_eq_element (i : Fin 6048) (hi : element i ≠ 1) :
    element (classConjIndex i) * classRepG (classRepIndex i) * (element (classConjIndex i))⁻¹ =
      element i :=
  by native_decide +revert

/-- Every nonidentity element of `G` is conjugate to its listed class representative. -/
theorem element_isConj_classRep (i : Fin 6048) (hi : element i ≠ 1) :
    IsConj (element i) (classRepG (classRepIndex i)) := by
  have h : IsConj (classRepG (classRepIndex i)) (element i) := by
    rw [isConj_iff]
    exact ⟨element (classConjIndex i), class_conj_eq_element i hi⟩
  exact h.symm

/-- A signed conjugation step: a conjugator (by index) together with a flag indicating
whether to invert after conjugating. Used to describe the words in `normalWord`. -/
structure SignedConj where
  /-- Index of the conjugating element. -/
  conjugator : Fin 6048
  /-- If `true`, invert after conjugating. -/
  invFlag : Bool
  deriving DecidableEq, Repr

/-- Convenience constructor for a `SignedConj` from a raw natural number. -/
def sc (n : Nat) (invFlag : Bool) : SignedConj where
  conjugator := fin6048 n
  invFlag := invFlag

/-- Apply a signed conjugation step `f` to the group element `r`. -/
def signedConj (r : G) (f : SignedConj) : G :=
  let y := element f.conjugator * r * (element f.conjugator)⁻¹
  if f.invFlag then y⁻¹ else y

/-- Evaluate a list of signed-conjugation steps applied to `r`, taking the product. -/
def evalSignedConjWord (r : G) : List SignedConj → G
  | [] => 1
  | f :: w => signedConj r f * evalSignedConjWord r w

/-- Explicit normal-closure word: `evalSignedConjWord (classRepG k) (normalWord k i)`
equals the `i`-th generator `genG i` of `G`. The data realises Table 2 of the manuscript:
for every nonidentity class `k` we exhibit two products of conjugates of `r_k` and their
inverses that recover the generators `a` and `b`. -/
def normalWord (k : Fin 13) (i : Fin 2) : List SignedConj :=
  match k.val, i.val with
  | 0, 0 => [sc 48 false, sc 123 false, sc 165 false]
  | 0, 1 => [sc 29 false, sc 20 false]
  | 1, 0 => [sc 225 false, sc 217 false]
  | 1, 1 => [sc 801 true]
  | 2, 0 => [sc 71 false, sc 32 false, sc 13 true]
  | 2, 1 => [sc 366 false, sc 2749 false, sc 13 true, sc 354 true]
  | 3, 0 => [sc 0 false]
  | 3, 1 => [sc 272 false, sc 171 true]
  | 4, 0 => [sc 0 true]
  | 4, 1 => [sc 122 true, sc 253 false]
  | 5, 0 => [sc 1301 false, sc 428 true]
  | 5, 1 => [sc 992 false, sc 104 true]
  | 6, 0 => [sc 173 true, sc 95 true]
  | 6, 1 => [sc 1447 false, sc 1284 true]
  | 7, 0 => [sc 142 true, sc 297 false]
  | 7, 1 => [sc 873 true, sc 1306 false]
  | 8, 0 => [sc 702 false, sc 1318 false]
  | 8, 1 => [sc 738 true, sc 2762 false]
  | 9, 0 => [sc 54 true, sc 1063 false]
  | 9, 1 => [sc 2025 false, sc 569 false]
  | 10, 0 => [sc 455 false, sc 239 false]
  | 10, 1 => [sc 1209 false, sc 239 false]
  | 11, 0 => [sc 352 true, sc 793 true]
  | 11, 1 => [sc 19 true, sc 44 false]
  | 12, 0 => [sc 189 false, sc 147 false]
  | 12, 1 => [sc 28 false, sc 64 true]
  | _, _ => []

/-- Every signed conjugate of `r` lies in the normal closure `⟨⟨r⟩⟩_G`. -/
theorem signedConj_mem_normalClosure (r : G) (f : SignedConj) :
    signedConj r f ∈ Subgroup.normalClosure ({ r } : Set G) := by
  have hr : r ∈ Subgroup.normalClosure ({ r } : Set G) :=
    Subgroup.subset_normalClosure (Set.mem_singleton r)
  have hc :
    element f.conjugator * r * (element f.conjugator)⁻¹ ∈
      Subgroup.normalClosure ({ r } : Set G) :=
    Subgroup.normalClosure_normal.conj_mem r hr (element f.conjugator)
  unfold signedConj
  split
  · exact (Subgroup.normalClosure ({ r } : Set G)).inv_mem hc
  · exact hc

/-- A product of signed conjugates of `r` lies in the normal closure `⟨⟨r⟩⟩_G`. -/
theorem evalSignedConjWord_mem_normalClosure (r : G) :
    ∀ w : List SignedConj, evalSignedConjWord r w ∈ Subgroup.normalClosure ({ r } : Set G)
  | [] => by simp only [evalSignedConjWord, one_mem]
  | f :: w => by
    exact
      Subgroup.mul_mem _ (signedConj_mem_normalClosure r f)
        (evalSignedConjWord_mem_normalClosure r w)

/-- The pre-tabulated `normalWord k i` recovers the generator `genG i` from the class
representative `classRepG k`. -/
theorem normalWord_eval_eq_genG (k : Fin 13) (i : Fin 2) :
    evalSignedConjWord (classRepG k) (normalWord k i) = genG i := by native_decide +revert

/-- Every generator `genG i` lies in the normal closure of every nonidentity class
representative `classRepG k`. -/
theorem genG_mem_normalClosure_classRep (k : Fin 13) (i : Fin 2) :
    genG i ∈ Subgroup.normalClosure ({classRepG k} : Set G) := by
  rw [← normalWord_eval_eq_genG k i]
  exact evalSignedConjWord_mem_normalClosure (classRepG k) (normalWord k i)

/-- The simple group `G = ⟨a, b⟩ ≤ S₂₈` is a simple group. -/
theorem isSimpleGroup_G : IsSimpleGroup G := by
  let reps : Finset G := Finset.univ.image classRepG
  refine
    KourovkaNotebook.isSimpleGroup_of_normalClosure_finset_class_reps (G := G) (s :=
      Set.range genG) reps closure_range_genG ?_ ?_
  · intro g hg
    obtain ⟨i, rfl⟩ := element_surjective g
    refine ⟨classRepG (classRepIndex i), ?_, element_isConj_classRep i hg⟩
    exact Finset.mem_image.mpr ⟨classRepIndex i, Finset.mem_univ _, rfl⟩
  · intro r hr y hy
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i, rfl⟩ := hy
    exact genG_mem_normalClosure_classRep k i


end KourovkaNotebook.PSU33Perm


/-! ## The non-simple partner `H = C₆ × S₄ × (C₇ ⋊ C₆)` and the negative resolution

We construct the original non-simple counterexample `H = C₆ × S₄ × (C₇ ⋊ C₆)`, where
`C₆` acts on `C₇` by multiplication by `3` modulo `7`, verify it has order `6048` and
totient sum `23984`, and assemble the negative resolution `kourovka_19_25` together with
an existential form `exists_same_card_totient_sum_simple_not_simple`.
-/

open Finset in
/-- The totient sum of a finite group: `∑ g : G, φ (orderOf g)`. -/
noncomputable def totientSum (G : Type*) [Group G] [Fintype G] : ℕ :=
  ∑ g : G, Nat.totient (orderOf g)

namespace SameCardTotientSum

/-- The listed element-order histogram for `PSU(3,3)` gives totient sum `23984`. -/
theorem totient_sum_psu33_histogram :
    1 * Nat.totient 1 + 63 * Nat.totient 2 + 728 * Nat.totient 3 + 504 * Nat.totient 4 +
              504 * Nat.totient 6 +
            1728 * Nat.totient 7 +
          1512 * Nat.totient 8 +
        1008 * Nat.totient 12 =
      23984 :=
  by native_decide

/-- The listed element-order histogram for `C6 × (S4 × (C7 : C6))` gives totient
sum `23984`. -/
theorem totient_sum_counterexample_h_histogram :
    1 * Nat.totient 1 + 159 * Nat.totient 2 + 404 * Nat.totient 3 + 96 * Nat.totient 4 +
                      3324 * Nat.totient 6 +
                    6 * Nat.totient 7 +
                  1200 * Nat.totient 12 +
                114 * Nat.totient 14 +
              156 * Nat.totient 21 +
            72 * Nat.totient 28 +
          372 * Nat.totient 42 +
        144 * Nat.totient 84 =
      23984 :=
  by native_decide

/-- Both listed histograms have total mass `6048`. -/
theorem card_histograms :
    1 + 63 + 728 + 504 + 504 + 1728 + 1512 + 1008 = (6048 : ℕ) ∧
      1 + 159 + 404 + 96 + 3324 + 6 + 1200 + 114 + 156 + 72 + 372 + 144 = (6048 : ℕ) :=
  ⟨rfl, rfl⟩

/-! ### The non-simple comparison group `H = C₆ × (S₄ × (C₇ ⋊ C₆))`

The cyclic group `C₆` acts on `C₇` by multiplication by `3` modulo `7`. -/

/-- A computable bounded element order.  The proof bridge below rewrites it back
to mathlib's noncomputable `orderOf` once a positive exponent bound is known. -/
def computableOrder (G : Type*) [Group G] [DecidableEq G] (bound : ℕ) (g : G) : ℕ :=
  if h : ∃ n : Fin (bound + 1), 0 < n.1 ∧ g ^ n.1 = 1 then
    (Fin.find (fun n : Fin (bound + 1) ↦ 0 < n.1 ∧ g ^ n.1 = 1) h).1
  else 0

/-- Bridge lemma: if `g ^ bound = 1` for some positive `bound`, then `orderOf g`
agrees with the computable bounded variant `computableOrder G bound g`. -/
lemma orderOf_eq_computableOrder_of_pow_bound (G : Type*) [Group G] [DecidableEq G] (bound : ℕ)
    (g : G) (hbound_pos : 0 < bound) (hbound : g ^ bound = 1) :
    orderOf g = computableOrder G bound g := by
  let p : Fin (bound + 1) → Prop := fun n ↦ 0 < n.1 ∧ g ^ n.1 = 1
  have hex : ∃ n : Fin (bound + 1), p n :=
    ⟨⟨bound, Nat.lt_succ_self bound⟩, hbound_pos, by simpa only using hbound⟩
  have hcomp : computableOrder G bound g = (Fin.find p hex).1 := by
    dsimp [computableOrder, p]
    rw [dif_pos hex]
  rw [hcomp]
  have hspec := Fin.find_spec (p := p) hex
  rw [orderOf_eq_iff hspec.1]
  constructor
  · exact hspec.2
  · intro m hm hmpos hpow
    let j : Fin (bound + 1) := ⟨m, lt_trans hm (Fin.find p hex).2⟩
    have hjlt : j < Fin.find p hex := hm
    have hjp : p j := ⟨hmpos, hpow⟩
    exact (Fin.find_min (p := p) hex hjlt) hjp

/-- The order-six unit defining the nontrivial action in `C7 : C6`. -/
def unitThreeModSeven : (ZMod 7)ˣ :=
  ZMod.unitOfCoprime 3 (by norm_num)

/-- Multiplication by `3` on the additive group of `ZMod 7`, transferred to the
multiplicative notation used by `SemidirectProduct`. -/
def frobeniusAut : MulAut (Multiplicative (ZMod 7)) :=
  (MulAutMultiplicative (ZMod 7)).symm ((ZMod.AddAutEquivUnits 7).symm unitThreeModSeven)

/-- The automorphism `frobeniusAut` has order dividing `6`. -/
lemma frobeniusAut_pow_six : frobeniusAut ^ 6 = 1 := by
  ext x
  native_decide +revert

/-- The action of `C6` on `C7` used in the Frobenius group `C7 : C6`. -/
def frobeniusAction : Multiplicative (ZMod 6) →* MulAut (Multiplicative (ZMod 7)) where
  toFun x := frobeniusAut ^ (Multiplicative.toAdd x).val
  map_one' := by simp only [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' := by
    intro x y
    change
      frobeniusAut ^ (Multiplicative.toAdd (x * y)).val =
        frobeniusAut ^ (Multiplicative.toAdd x).val *
          frobeniusAut ^ (Multiplicative.toAdd y).val
    rw [show Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y from
        rfl]
    rw [ZMod.val_add]
    rw [← pow_add]
    exact
      (pow_eq_pow_mod ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val)
          frobeniusAut_pow_six).symm

/-- The cyclic group `C₆`, written multiplicatively. -/
abbrev CyclicSix :=
  Multiplicative (ZMod 6)

/-- The symmetric group `S₄`. -/
abbrev SymmetricFour :=
  Equiv.Perm (Fin 4)

/-- The Frobenius group `C7 : C6`. -/
abbrev FrobeniusFortyTwo :=
  Multiplicative (ZMod 7) ⋊[frobeniusAction] Multiplicative (ZMod 6)

/-- The Frobenius group `C₇ ⋊ C₆` is finite, with the underlying type `C₇ × C₆`. -/
instance instFintypeFrobeniusFortyTwo : Fintype FrobeniusFortyTwo :=
  Fintype.ofEquiv (Multiplicative (ZMod 7) × Multiplicative (ZMod 6))
    ⟨fun p ↦ ⟨p.1, p.2⟩, fun s ↦ ⟨s.1, s.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The nonsimple candidate `H = C6 × (S4 × (C7 : C6))`. -/
abbrev CounterexampleH :=
  CyclicSix × (SymmetricFour × FrobeniusFortyTwo)

/-- For `g ∈ C₆`, `orderOf g` is the computable bounded variant with bound `6`. -/
lemma orderOf_cyclicSix_eq_computableOrder (g : CyclicSix) :
    orderOf g = computableOrder CyclicSix 6 g := by
  have hcard : Fintype.card CyclicSix = 6 := by native_decide
  have h := pow_card_eq_one (G := CyclicSix) (x := g)
  rw [hcard] at h
  exact orderOf_eq_computableOrder_of_pow_bound _ 6 g (by norm_num) h

/-- For `g ∈ S₄`, `orderOf g` is the computable bounded variant with bound `24`. -/
lemma orderOf_symmetricFour_eq_computableOrder (g : SymmetricFour) :
    orderOf g = computableOrder SymmetricFour 24 g := by
  have hcard : Fintype.card SymmetricFour = 24 := by native_decide
  have h := pow_card_eq_one (G := SymmetricFour) (x := g)
  rw [hcard] at h
  exact orderOf_eq_computableOrder_of_pow_bound _ 24 g (by norm_num) h

/-- `|C₇ ⋊ C₆| = 42`. -/
lemma card_frobenius_forty_two : Fintype.card FrobeniusFortyTwo = 42 := by native_decide

/-- For `g ∈ C₇ ⋊ C₆`, `orderOf g` is the computable bounded variant with bound `42`. -/
lemma orderOf_frobenius_forty_two_eq_computableOrder (g : FrobeniusFortyTwo) :
    orderOf g = computableOrder FrobeniusFortyTwo 42 g := by
  have h := pow_card_eq_one (G := FrobeniusFortyTwo) (x := g)
  rw [card_frobenius_forty_two] at h
  exact orderOf_eq_computableOrder_of_pow_bound _ 42 g (by norm_num) h

/-- `|H| = 6048`. -/
theorem card_counterexample_h : Fintype.card CounterexampleH = 6048 := by native_decide

/-- The concrete candidate `H = C6 × (S4 × (C7 : C6))` has `T(H) = 23984`. -/
theorem totient_sum_counterexample_h : totientSum CounterexampleH = 23984 := by
  simp only [totientSum, CounterexampleH, Prod.orderOf, orderOf_cyclicSix_eq_computableOrder,
    orderOf_symmetricFour_eq_computableOrder, orderOf_frobenius_forty_two_eq_computableOrder]
  native_decide

/-- The concrete candidate `H = C6 × (S4 × (C7 : C6))` has the listed
element-order histogram. -/
theorem order_histogram_counterexample_h :
    (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 1)).card = 1 ∧
      (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 2)).card = 159 ∧
        (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 3)).card = 404 ∧
          (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 4)).card = 96 ∧
            (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 6)).card = 3324 ∧
              (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 7)).card = 6 ∧
                (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 12)).card = 1200 ∧
                  (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 14)).card = 114 ∧
                    (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 21)).card = 156 ∧
                      (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 28)).card =
                          72 ∧
                        (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 42)).card =
                            372 ∧
                          (Finset.univ.filter (fun h : CounterexampleH ↦ orderOf h = 84)).card =
                            144 := by
  simp only [CounterexampleH, Prod.orderOf, orderOf_cyclicSix_eq_computableOrder,
    orderOf_symmetricFour_eq_computableOrder, orderOf_frobenius_forty_two_eq_computableOrder,
    Nat.lcm_eq_one_iff]
  native_decide

/-- `H = C₆ × (S₄ × (C₇ ⋊ C₆))` is not simple, since it factors as a nontrivial
direct product with a `C₆` factor. -/
theorem not_isSimpleGroup_counterexample_h : ¬IsSimpleGroup CounterexampleH := by
  have : Nontrivial CyclicSix := by
    have h : 1 < Fintype.card CyclicSix := by native_decide
    exact Fintype.one_lt_card_iff_nontrivial.mp h
  exact KourovkaNotebook.not_isSimpleGroup_prod CyclicSix (SymmetricFour × FrobeniusFortyTwo)

end SameCardTotientSum

/-- The universal assertion asked in Kourovka 19.25: same order and same totient sum transfer
simplicity from `G` to `H`. -/
def SameCardTotientSumSimpleTransfer : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (H : Type) [Group H] [Fintype H],
    Fintype.card G = Fintype.card H →
      totientSum G = totientSum H → IsSimpleGroup G → IsSimpleGroup H

/-- Conditional counterexample using the concrete degree-28 permutation model of
`PSU(3,3)`, with the order data supplied by
`KourovkaNotebook.PSU33Perm.card_G`. -/
theorem not_same_card_totient_sum_simple_transfer_of_psu33_perm
    (hGtot : totientSum KourovkaNotebook.PSU33Perm.G = 23984)
    (hGsimple : IsSimpleGroup KourovkaNotebook.PSU33Perm.G) :
    ¬SameCardTotientSumSimpleTransfer := by
  intro h
  exact
    SameCardTotientSum.not_isSimpleGroup_counterexample_h
      (h KourovkaNotebook.PSU33Perm.G SameCardTotientSum.CounterexampleH
        (by rw [KourovkaNotebook.PSU33Perm.card_G, SameCardTotientSum.card_counterexample_h])
        (by rw [hGtot, SameCardTotientSum.totient_sum_counterexample_h]) hGsimple)

/-- The degree-28 permutation model closes the order and totient-sum sides of
the counterexample. -/
theorem not_same_card_totient_sum_simple_transfer_of_psu33_perm_simple
    (hGsimple : IsSimpleGroup KourovkaNotebook.PSU33Perm.G) :
    ¬SameCardTotientSumSimpleTransfer := by
  exact
    not_same_card_totient_sum_simple_transfer_of_psu33_perm
      (by simpa only [totientSum] using KourovkaNotebook.PSU33Perm.sum_totient_orderOf_G)
      hGsimple

/-- A concrete counterexample to the universal implication in Kourovka 19.25. -/
theorem exists_same_card_totient_sum_simple_not_simple :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (H : Type) (_ : Group H) (_ : Fintype H),
      Fintype.card G = Fintype.card H ∧
        @totientSum G _ _ = @totientSum H _ _ ∧ @IsSimpleGroup G _ ∧ ¬@IsSimpleGroup H _ := by
  refine
    ⟨KourovkaNotebook.PSU33Perm.G, inferInstance, inferInstance,
      SameCardTotientSum.CounterexampleH, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [KourovkaNotebook.PSU33Perm.card_G, SameCardTotientSum.card_counterexample_h]
  · rw [SameCardTotientSum.totient_sum_counterexample_h]
    simpa only [totientSum] using KourovkaNotebook.PSU33Perm.sum_totient_orderOf_G
  · exact KourovkaNotebook.PSU33Perm.isSimpleGroup_G
  · exact SameCardTotientSum.not_isSimpleGroup_counterexample_h

/-- Negative resolution of Kourovka 19.25. -/
theorem not_same_card_totient_sum_simple_transfer : ¬SameCardTotientSumSimpleTransfer :=
  not_same_card_totient_sum_simple_transfer_of_psu33_perm_simple
    KourovkaNotebook.PSU33Perm.isSimpleGroup_G

/-! ## The wreath-decomposed partner `H' = C₂ × (C₆ ≀ C₂) × (C₇ ⋊ C₆)`

The same simple group `PSU(3, 3)` also pairs with the structurally distinct non-simple
group `H' = C₂ × ((C₆ ≀ C₂) × (C₇ ⋊ C₆))`, where `C₆ ≀ C₂` denotes the regular wreath
product. The two non-simple partners `H` and `H'` are not isomorphic: their numbers of
elements of order `3` differ. -/

/-- A `DecidableEq` instance for a semidirect product, given decidable equality on each
factor. -/
instance SemidirectProduct.instDecidableEq' {N G : Type*} [Group N] [Group G]
    {φ : G →* MulAut N} [DecidableEq N] [DecidableEq G] : DecidableEq (N ⋊[φ] G) :=
  fun ⟨n1, g1⟩ ⟨n2, g2⟩ ↦
  if hn : n1 = n2 then
    if hg : g1 = g2 then
      isTrue (by
          subst hn
          subst hg
          rfl)
    else
      isFalse (by
          intro h
          exact hg (SemidirectProduct.ext_iff.mp h).2)
  else
    isFalse (by
        intro h
        exact hn (SemidirectProduct.ext_iff.mp h).1)

namespace WreathDecomposition

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

/-- The base group of the wreath product `C₆ ≀ C₂` is `C₆ × C₆`. -/
abbrev C6Squared :=
  Multiplicative (ZMod 6) × Multiplicative (ZMod 6)

/-- The swap automorphism on `C₆ × C₆`. -/
def swapAut : MulAut C6Squared where
  toFun := fun ⟨a, b⟩ ↦ ⟨b, a⟩
  invFun := fun ⟨a, b⟩ ↦ ⟨b, a⟩
  left_inv := by
    intro ⟨a, b⟩
    rfl
  right_inv := by
    intro ⟨a, b⟩
    rfl
  map_mul' := by
    intro ⟨a1, b1⟩ ⟨a2, b2⟩
    rfl

/-- The swap automorphism on `C₆ × C₆` has order `2`. -/
lemma swapAut_sq : swapAut ^ 2 = 1 := by ext ⟨a, b⟩ <;> simp [swapAut, MulAut.one_apply] <;> rfl

/-- The action of `C₂` on `C₆ × C₆` by swapping factors. -/
def wreathSwapAction : Multiplicative (ZMod 2) →* MulAut C6Squared where
  toFun x := swapAut ^ (Multiplicative.toAdd x).val
  map_one' := by simp only [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' := by
    intro x y
    change
      swapAut ^ (Multiplicative.toAdd (x * y)).val =
        swapAut ^ (Multiplicative.toAdd x).val * swapAut ^ (Multiplicative.toAdd y).val
    rw [show Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y from
        rfl]
    rw [ZMod.val_add]
    rw [← pow_add]
    exact (pow_eq_pow_mod _ swapAut_sq).symm

/-- The regular wreath product `C₆ ≀ C₂ = (C₆ × C₆) ⋊ C₂`. -/
abbrev WreathC6C2 :=
  C6Squared ⋊[wreathSwapAction] Multiplicative (ZMod 2)

/-- `C₆ ≀ C₂` is finite, with the underlying type `(C₆ × C₆) × C₂`. -/
instance instFintypeWreathC6C2 : Fintype WreathC6C2 :=
  Fintype.ofEquiv (C6Squared × Multiplicative (ZMod 2))
    ⟨fun p ↦ ⟨p.1, p.2⟩, fun s ↦ ⟨s.1, s.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- `|C₆ ≀ C₂| = 72`. -/
lemma card_wreathC6C2 : Fintype.card WreathC6C2 = 72 := by native_decide

/-- The cyclic group `C₂`. -/
abbrev CyclicTwo :=
  Multiplicative (ZMod 2)

/-- The Frobenius group `C₇ ⋊ C₆` of order `42`. -/
abbrev FrobeniusFortyTwo :=
  SameCardTotientSum.FrobeniusFortyTwo

/-- The decomposed nonsimple comparison group
`C₂ × ((C₆ ≀ C₂) × (C₇ ⋊ C₆))`. -/
abbrev NewCounterexampleH :=
  CyclicTwo × (WreathC6C2 × FrobeniusFortyTwo)

/-- `|H'| = 6048`. -/
theorem card_newCounterexampleH : Fintype.card NewCounterexampleH = 6048 := by native_decide

/-- For `g ∈ C₂`, `orderOf g` is the computable bounded variant with bound `2`. -/
lemma orderOf_cyclicTwo_eq_computableOrder (g : CyclicTwo) :
    orderOf g = SameCardTotientSum.computableOrder CyclicTwo 2 g := by
  have hcard : Fintype.card CyclicTwo = 2 := by native_decide
  have h := pow_card_eq_one (G := CyclicTwo) (x := g)
  rw [hcard] at h
  exact SameCardTotientSum.orderOf_eq_computableOrder_of_pow_bound _ 2 g (by norm_num) h

/-- For `g ∈ C₆ ≀ C₂`, `orderOf g` is the computable bounded variant with bound `72`. -/
lemma orderOf_wreathC6C2_eq_computableOrder (g : WreathC6C2) :
    orderOf g = SameCardTotientSum.computableOrder WreathC6C2 72 g := by
  have h := pow_card_eq_one (G := WreathC6C2) (x := g)
  rw [card_wreathC6C2] at h
  exact SameCardTotientSum.orderOf_eq_computableOrder_of_pow_bound _ 72 g (by norm_num) h

/-- The decomposed comparison group has the same totient sum as `PSU(3,3)`. -/
theorem totient_sum_newCounterexampleH : totientSum NewCounterexampleH = 23984 := by
  simp only [totientSum, NewCounterexampleH, Prod.orderOf, orderOf_cyclicTwo_eq_computableOrder,
    orderOf_wreathC6C2_eq_computableOrder,
    SameCardTotientSum.orderOf_frobenius_forty_two_eq_computableOrder]
  native_decide

/-- The decomposed comparison group is not simple. -/
theorem not_isSimpleGroup_newCounterexampleH : ¬IsSimpleGroup NewCounterexampleH := by
  have : Nontrivial CyclicTwo := Fintype.one_lt_card_iff_nontrivial.mp <| by native_decide
  have : Nontrivial (WreathC6C2 × FrobeniusFortyTwo) :=
    Fintype.one_lt_card_iff_nontrivial.mp <| by native_decide
  exact KourovkaNotebook.not_isSimpleGroup_prod CyclicTwo (WreathC6C2 × FrobeniusFortyTwo)

/-- The number of elements of order `3` in the original nonsimple comparison
group. -/
theorem order3_count_orig :
    (Finset.univ.filter (fun h : SameCardTotientSum.CounterexampleH ↦ orderOf h = 3)).card =
      404 := by
  simp only [SameCardTotientSum.CounterexampleH, Prod.orderOf,
    SameCardTotientSum.orderOf_cyclicSix_eq_computableOrder,
    SameCardTotientSum.orderOf_symmetricFour_eq_computableOrder,
    SameCardTotientSum.orderOf_frobenius_forty_two_eq_computableOrder]
  native_decide

/-- The number of elements of order `3` in the decomposed comparison group. -/
theorem order3_count_new :
    (Finset.univ.filter (fun h : NewCounterexampleH ↦ orderOf h = 3)).card = 134 := by
  simp only [NewCounterexampleH, Prod.orderOf, orderOf_cyclicTwo_eq_computableOrder,
    orderOf_wreathC6C2_eq_computableOrder,
    SameCardTotientSum.orderOf_frobenius_forty_two_eq_computableOrder]
  native_decide

/-- The two nonsimple comparison groups are not isomorphic; the number of
elements of order `3` is different. -/
theorem not_isomorphic_counterexamples :
    IsEmpty (SameCardTotientSum.CounterexampleH ≃* NewCounterexampleH) := by
  constructor
  intro f
  have h1 := order3_count_orig
  have h2 := order3_count_new
  have hpres :
    (Finset.univ.filter (fun h : SameCardTotientSum.CounterexampleH ↦ orderOf h = 3)).card =
      (Finset.univ.filter (fun h : NewCounterexampleH ↦ orderOf h = 3)).card := by
    apply Finset.card_bij (fun g _ ↦ f g)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [MulEquiv.orderOf_eq f a]
      exact ha
    · intro a₁ a₂ _ _ h
      exact f.injective h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine ⟨f.symm b, ?_, by simp only [MulEquiv.apply_symm_apply]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := MulEquiv.orderOf_eq f.symm b
      rw [this]
      exact hb
  rw [h1, h2] at hpres
  exact absurd hpres (by omega)

/-- A concrete counterexample using the decomposed nonsimple group
`C₂ × ((C₆ ≀ C₂) × (C₇ ⋊ C₆))`. -/
theorem exists_wreath_counterexample :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (H : Type) (_ : Group H) (_ : Fintype H),
      Fintype.card G = Fintype.card H ∧
        @totientSum G _ _ = @totientSum H _ _ ∧ @IsSimpleGroup G _ ∧ ¬@IsSimpleGroup H _ := by
  refine
    ⟨KourovkaNotebook.PSU33Perm.G, inferInstance, inferInstance, NewCounterexampleH,
      inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [KourovkaNotebook.PSU33Perm.card_G, card_newCounterexampleH]
  · rw [totient_sum_newCounterexampleH]
    simpa only [totientSum] using KourovkaNotebook.PSU33Perm.sum_totient_orderOf_G
  · exact KourovkaNotebook.PSU33Perm.isSimpleGroup_G
  · exact not_isSimpleGroup_newCounterexampleH

end WreathDecomposition

/-- Canonical negative resolution of Kourovka 19.25. -/
theorem kourovka_19_25 : ¬SameCardTotientSumSimpleTransfer :=
  not_same_card_totient_sum_simple_transfer

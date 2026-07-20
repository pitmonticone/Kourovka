/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Pietro Monticone, Daniel Morrison
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Repeating permutations

This file extends permutations of a small index type to a larger one by repetition.
`Equiv.classRepeat` extends a permutation of `Fin n` to `Fin (m * n)` by acting on residues
modulo `n`, and `Equiv.dvdRepeat` extends a permutation of `Fin m` to `Fin n` whenever `m ∣ n`,
packaged as the monoid homomorphism `Equiv.dvdRepeatHom`.
-/

namespace Equiv

/-- Extend a permutation `σ` of `α` to `α × β`, acting as `σ` on the first coordinate and
fixing the second. -/
def extendRepeatLeft {α : Type*} (β : Type*) (σ : Perm α) : Perm (α × β) :=
  σ.prodCongr (Equiv.refl β)

/-- `extendRepeatLeft` sends `(a, b)` to `(σ a, b)`. -/
@[simp]
lemma extendRepeatLeft_apply {α : Type*} (β : Type*) (σ : Perm α) (p : α × β) :
    σ.extendRepeatLeft β p = (σ p.1, p.2) :=
  rfl

/-- `extendRepeatLeft` of the identity permutation is the identity. -/
@[simp]
lemma extendRepeatLeft_refl {α : Type*} (β : Type*) :
    (Equiv.refl α).extendRepeatLeft β = Equiv.refl (α × β) :=
  rfl

/-- `extendRepeatLeft` commutes with taking the inverse permutation. -/
@[simp]
lemma extendRepeatLeft_symm {α : Type*} (β : Type*) (σ : Perm α) :
    (σ.symm).extendRepeatLeft β = (σ.extendRepeatLeft β).symm :=
  rfl

/-- `extendRepeatLeft` distributes over composition of permutations. -/
@[simp]
lemma extendRepeatLeft_trans {α : Type*} (β : Type*) (σ τ : Perm α) :
    (σ.trans τ).extendRepeatLeft β = (σ.extendRepeatLeft β).trans (τ.extendRepeatLeft β) :=
  rfl

/-- Extend a permutation `σ` of `β` to `α × β`, fixing the first coordinate and acting as `σ`
on the second. -/
def extendRepeatRight (α : Type*) {β : Type*} (σ : Perm β) : Perm (α × β) :=
  (Equiv.refl α).prodCongr σ

/-- `extendRepeatRight` sends `(a, b)` to `(a, σ b)`. -/
@[simp]
lemma extendRepeatRight_apply (α : Type*) {β : Type*} (σ : Perm β) (p : α × β) :
    σ.extendRepeatRight α p = (p.1, σ p.2) :=
  rfl

/-- `extendRepeatRight` of the identity permutation is the identity. -/
@[simp]
lemma extendRepeatRight_refl (α : Type*) {β : Type*} :
    (Equiv.refl β).extendRepeatRight α = Equiv.refl (α × β) :=
  rfl

/-- Extending `σ.symm` gives the inverse of the extension of `σ`. -/
@[simp]
lemma extendRepeatRight_symm (α : Type*) {β : Type*} (σ : Perm β) :
    (σ.symm).extendRepeatLeft α = (σ.extendRepeatLeft α).symm :=
  rfl

/-- Extending `σ.trans τ` gives the composition of the extensions of `σ` and `τ`. -/
@[simp]
lemma extendRepeatRight_trans (α : Type*) {β : Type*} (σ τ : Perm β) :
    (σ.trans τ).extendRepeatLeft α = (σ.extendRepeatLeft α).trans (τ.extendRepeatLeft α) :=
  rfl

/-- Extend a permutation of `Fin n` to `Fin (m * n)` by acting on residue classes mod `n`.
Explicitly, `k` is mapped to `σ(k % n) + (k / m) * m`. -/
def classRepeat (m : ℕ) {n : ℕ} (σ : Perm (Fin n)) : Perm (Fin (m * n)) :=
  finProdFinEquiv.permCongr (σ.extendRepeatRight _)

/-- The natural-number value of `σ.classRepeat m k` is `σ k.modNat + n * k.divNat`. -/
@[simp]
lemma classRepeat_apply_val {m n : ℕ} (σ : Perm (Fin n)) (k : Fin (m * n)) :
    (σ.classRepeat m k : ℕ) = σ k.modNat + n * k.divNat :=
  rfl

/-- `classRepeat` of the identity permutation is the identity. -/
@[simp]
lemma classRepeat_refl (m : ℕ) {n : ℕ} : (Equiv.refl (Fin n)).classRepeat m = Equiv.refl _ := by
  simp [classRepeat]

/-- `classRepeat` commutes with taking the inverse permutation. -/
@[simp]
lemma classRepeat_symm (m : ℕ) {n : ℕ} (σ : Perm (Fin n)) :
    σ.symm.classRepeat m = (σ.classRepeat m).symm :=
  rfl

/-- `classRepeat` distributes over composition of permutations. -/
@[simp]
lemma classRepeat_trans (m : ℕ) {n : ℕ} (σ τ : Perm (Fin n)) :
    (σ.trans τ).classRepeat m = (σ.classRepeat m).trans (τ.classRepeat m) := by
  ext
  simp [classRepeat]

/-- Tower law for `classRepeat`: when `m ∣ n`, `n ∣ o` and `m ∣ o`, repeating by `o / m`
agrees with repeating by `n / m` and then by `o / n`, up to the relevant `finCongr`. -/
@[simp]
lemma classRepeat_dvd_trans {m n o : ℕ} (hmn : m ∣ n) (hno : n ∣ o) (hmo : m ∣ o)
    (σ : Perm (Fin m)) :
    (finCongr (Nat.div_mul_cancel hmo)).permCongr (σ.classRepeat (o / m)) =
      (finCongr (Nat.div_mul_cancel hno)).permCongr
        (((finCongr (Nat.div_mul_cancel hmn)).permCongr (σ.classRepeat (n / m))).classRepeat
          (o / n)) := by
  ext k
  simp only [permCongr_apply, finCongr_symm, finCongr_apply, Fin.val_cast, classRepeat_apply_val,
    Fin.coe_divNat, Fin.coe_modNat]
  suffices
    (Fin.cast (Nat.div_mul_cancel hmo).symm k).modNat =
      (Fin.cast (Nat.div_mul_cancel hmn).symm
          (Fin.cast (Nat.div_mul_cancel hno).symm k).modNat).modNat by
    rw [this, add_assoc, Nat.add_left_cancel_iff]
    simp only [Nat.mul_div_self_eq_mod_sub_self]
    rw [Nat.mod_mod_of_dvd _ hmn, add_comm, ← Nat.add_sub_assoc, Nat.sub_add_cancel]
    · exact Nat.mod_le (↑k) n
    · rw [← Nat.mod_mod_of_dvd _ hmn]
      exact (↑k % n).mod_le m
  ext
  simp [Nat.mod_mod_of_dvd _ hmn]

open Nat

/-- Extend a permutation of `Fin m` to `Fin n` where `m ∣ n` by repeating the permutaion. -/
def dvdRepeat {m n : ℕ} (hm : m ∣ n) (σ : Perm (Fin m)) : Perm (Fin n) :=
  (finCongr (Nat.div_mul_cancel hm)).permCongr (σ.classRepeat (n / m))

/-- The natural-number value of `σ.dvdRepeat hm k` is `σ` applied to the residue of `k`
modulo `m`, plus `m * (k / m)`. -/
@[simp]
lemma dvdRepeat_apply_val {m n : ℕ} (hm : m ∣ n) (σ : Perm (Fin m)) (k : Fin n) :
    (σ.dvdRepeat hm k : ℕ) = σ (Fin.cast (Nat.div_mul_cancel hm).symm k).modNat + m * (k.val / m) :=
  rfl

/-- `dvdRepeat` of the identity permutation is the identity. -/
@[simp]
lemma dvdRepeat_refl {m n : ℕ} (hm : m ∣ n) : (Equiv.refl (Fin m)).dvdRepeat hm = Equiv.refl _ := by
  simp [dvdRepeat]

/-- `dvdRepeat` commutes with taking the inverse permutation. -/
@[simp]
lemma dvdRepeat_symm {m n : ℕ} (hm : m ∣ n) (σ : Perm (Fin m)) :
    σ.symm.dvdRepeat hm = (σ.dvdRepeat hm).symm :=
  rfl

/-- `dvdRepeat` distributes over composition of permutations. -/
@[simp]
lemma dvdRepeat_trans {m n : ℕ} (hm : m ∣ n) (σ τ : Perm (Fin m)) :
    (σ.trans τ).dvdRepeat hm = (σ.dvdRepeat hm).trans (τ.dvdRepeat hm) := by
  ext
  simp [dvdRepeat]

/-- `dvdRepeat` as a monoid homomorphism `Perm (Fin m) →* Perm (Fin n)` when `m ∣ n`. -/
def dvdRepeatHom {m n : ℕ} (hm : m ∣ n) : Perm (Fin m) →* Perm (Fin n) where
  toFun := dvdRepeat hm
  map_one' := dvdRepeat_refl hm
  map_mul' σ τ := dvdRepeat_trans hm τ σ

/-- `dvdRepeatHom hm` agrees with `dvdRepeat hm` on every permutation. -/
lemma dvdRepeatHom_apply {m n : ℕ} (hm : m ∣ n) (σ : Perm (Fin m)) :
    dvdRepeatHom hm σ = dvdRepeat hm σ :=
  rfl

/-- Tower law for `dvdRepeat`: when `m ∣ n`, `n ∣ o` and `m ∣ o`, extending from `Fin m`
to `Fin o` equals extending to `Fin n` first and then to `Fin o`. -/
lemma dvdRepeat_dvd {m n o : ℕ} (hmn : m ∣ n) (hno : n ∣ o) (hmo : m ∣ o) (σ : Perm (Fin m)) :
    σ.dvdRepeat hmo = (σ.dvdRepeat hmn).dvdRepeat hno := by
  simpa using classRepeat_dvd_trans hmn hno hmo σ

end Equiv

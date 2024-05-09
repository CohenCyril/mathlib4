/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma, Oliver Nash
-/
import Mathlib.Algebra.Associated
import Mathlib.Algebra.Ring.Opposite
import Mathlib.GroupTheory.GroupAction.Opposite
import Mathlib.Algebra.Group.Submonoid.Membership

#align_import ring_theory.non_zero_divisors from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Non-zero divisors and smul-divisors

In this file we define the submonoid `nonZeroDivisors` and `nonZeroSMulDivisors` of a
`MonoidWithZero`. We also define `nonZeroDivisorsLeft` and `nonZeroDivisorsRight` for
non-commutative monoids.

## Notations

This file declares the notations:
- `R⁰` for the submonoid of non-zero-divisors of `R`, in the locale `nonZeroDivisors`.
- `R⁰[M]` for the submonoid of non-zero smul-divisors of `R` with respect to `M`, in the locale
  `nonZeroSMulDivisors`

Use the statement `open scoped nonZeroDivisors nonZeroSMulDivisors` to access this notation in
your own code.

-/

variable (M₀ : Type*) [MonoidWithZero M₀]

/-- The collection of elements of a `MonoidWithZero` that are not left zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsLeft : Submonoid M₀ where
  carrier := {x | ∀ y, y * x = 0 → y = 0}
  one_mem' := by simp
  mul_mem' {x} {y} hx hy := fun z hz ↦ hx _ <| hy _ (mul_assoc z x y ▸ hz)

@[simp] lemma mem_nonZeroDivisorsLeft_iff {x : M₀} :
    x ∈ nonZeroDivisorsLeft M₀ ↔ ∀ y, y * x = 0 → y = 0 :=
  Iff.rfl

/-- The collection of elements of a `MonoidWithZero` that are not right zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsRight : Submonoid M₀ where
  carrier := {x | ∀ y, x * y = 0 → y = 0}
  one_mem' := by simp
  mul_mem' := fun {x} {y} hx hy z hz ↦ hy _ (hx _ ((mul_assoc x y z).symm ▸ hz))

@[simp] lemma mem_nonZeroDivisorsRight_iff {x : M₀} :
    x ∈ nonZeroDivisorsRight M₀ ↔ ∀ y, x * y = 0 → y = 0 :=
  Iff.rfl

lemma nonZeroDivisorsLeft_eq_right (M₀ : Type*) [CommMonoidWithZero M₀] :
    nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀ := by
  ext x; simp [mul_comm x]

@[simp] lemma coe_nonZeroDivisorsLeft_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsLeft M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsLeft_iff, mul_eq_zero, forall_eq_or_imp, true_and,
    Set.mem_setOf_eq]
  refine' ⟨fun h ↦ _, fun hx y hx' ↦ by contradiction⟩
  contrapose! h
  exact ⟨1, h, one_ne_zero⟩

@[simp] lemma coe_nonZeroDivisorsRight_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsRight M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsRight_iff, mul_eq_zero, Set.mem_setOf_eq]
  refine' ⟨fun h ↦ _, fun hx y hx' ↦ by aesop⟩
  contrapose! h
  exact ⟨1, Or.inl h, one_ne_zero⟩

/-- The submonoid of non-zero-divisors of a `MonoidWithZero` `R`. -/
def nonZeroDivisors (R : Type*) [MonoidWithZero R] : Submonoid R where
  carrier := { x | ∀ z, z * x = 0 → z = 0 }
  one_mem' _ hz := by rwa [mul_one] at hz
  mul_mem' hx₁ hx₂ _ hz := by
    rw [← mul_assoc] at hz
    exact hx₁ _ (hx₂ _ hz)
#align non_zero_divisors nonZeroDivisors

/-- The notation for the submonoid of non-zerodivisors. -/
scoped[nonZeroDivisors] notation:9000 R "⁰" => nonZeroDivisors R

/-- Let `R` be a monoid with zero and `M` an additive monoid with an `R`-action, then the collection
of non-zero smul-divisors forms a submonoid. These elements are also called `M`-regular. -/
def nonZeroSMulDivisors (R : Type*) [MonoidWithZero R] (M : Type _) [Zero M] [MulAction R M] :
    Submonoid R where
  carrier := { r | ∀ m : M, r • m = 0 → m = 0}
  one_mem' m h := (one_smul R m) ▸ h
  mul_mem' {r₁ r₂} h₁ h₂ m H := h₂ _ <| h₁ _ <| mul_smul r₁ r₂ m ▸ H

/-- The notation for the submonoid of non-zero smul-divisors. -/
scoped[nonZeroSMulDivisors] notation:9000 R "⁰[" M "]" => nonZeroSMulDivisors R M

section nonZeroDivisors

open nonZeroDivisors

variable {M M' M₁ R R' F : Type*} [MonoidWithZero M] [MonoidWithZero M'] [CommMonoidWithZero M₁]
  [Ring R] [CommRing R']

theorem mem_nonZeroDivisors_iff {r : M} : r ∈ M⁰ ↔ ∀ x, x * r = 0 → x = 0 := Iff.rfl
#align mem_non_zero_divisors_iff mem_nonZeroDivisors_iff

theorem mul_right_mem_nonZeroDivisors_eq_zero_iff {x r : M} (hr : r ∈ M⁰) : x * r = 0 ↔ x = 0 :=
  ⟨hr _, by simp (config := { contextual := true })⟩
#align mul_right_mem_non_zero_divisors_eq_zero_iff mul_right_mem_nonZeroDivisors_eq_zero_iff
@[simp]
theorem mul_right_coe_nonZeroDivisors_eq_zero_iff {x : M} {c : M⁰} : x * c = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisors_eq_zero_iff c.prop
#align mul_right_coe_non_zero_divisors_eq_zero_iff mul_right_coe_nonZeroDivisors_eq_zero_iff

theorem mul_left_mem_nonZeroDivisors_eq_zero_iff {r x : M₁} (hr : r ∈ M₁⁰) : r * x = 0 ↔ x = 0 := by
  rw [mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff hr]
#align mul_left_mem_non_zero_divisors_eq_zero_iff mul_left_mem_nonZeroDivisors_eq_zero_iff

@[simp]
theorem mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₁⁰} {x : M₁} : (c : M₁) * x = 0 ↔ x = 0 :=
  mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop
#align mul_left_coe_non_zero_divisors_eq_zero_iff mul_left_coe_nonZeroDivisors_eq_zero_iff

theorem mul_cancel_right_mem_nonZeroDivisors {x y r : R} (hr : r ∈ R⁰) : x * r = y * r ↔ x = y := by
  refine ⟨fun h ↦ ?_, congrArg (· * r)⟩
  rw [← sub_eq_zero, ← mul_right_mem_nonZeroDivisors_eq_zero_iff hr, sub_mul, h, sub_self]
#align mul_cancel_right_mem_non_zero_divisor mul_cancel_right_mem_nonZeroDivisors

theorem mul_cancel_right_coe_nonZeroDivisors {x y : R} {c : R⁰} : x * c = y * c ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisors c.prop
#align mul_cancel_right_coe_non_zero_divisor mul_cancel_right_coe_nonZeroDivisors

@[simp]
theorem mul_cancel_left_mem_nonZeroDivisors {x y r : R'} (hr : r ∈ R'⁰) : r * x = r * y ↔ x = y :=
  by simp_rw [mul_comm r, mul_cancel_right_mem_nonZeroDivisors hr]
#align mul_cancel_left_mem_non_zero_divisor mul_cancel_left_mem_nonZeroDivisors

theorem mul_cancel_left_coe_nonZeroDivisors {x y : R'} {c : R'⁰} : (c : R') * x = c * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisors c.prop
#align mul_cancel_left_coe_non_zero_divisor mul_cancel_left_coe_nonZeroDivisors

theorem dvd_cancel_right_mem_nonZeroDivisors {x y r : R'} (hr : r ∈ R'⁰) : x * r ∣ y * r ↔ x ∣ y :=
  ⟨fun ⟨z, _⟩ ↦ ⟨z, by rwa [← mul_cancel_right_mem_nonZeroDivisors hr, mul_assoc, mul_comm z r,
    ← mul_assoc]⟩, fun ⟨z, h⟩ ↦ ⟨z, by rw [h, mul_assoc, mul_comm z r, ← mul_assoc]⟩⟩

theorem dvd_cancel_right_coe_nonZeroDivisors {x y : R'} {c : R'⁰} : x * c ∣ y * c ↔ x ∣ y :=
  dvd_cancel_right_mem_nonZeroDivisors c.prop

theorem dvd_cancel_left_mem_nonZeroDivisors {x y r : R'} (hr : r ∈ R'⁰) : r * x ∣ r * y ↔ x ∣ y :=
  ⟨fun ⟨z, _⟩ ↦ ⟨z, by rwa [← mul_cancel_left_mem_nonZeroDivisors hr, ← mul_assoc]⟩,
    fun ⟨z, h⟩ ↦ ⟨z, by rw [h, ← mul_assoc]⟩⟩

theorem dvd_cancel_left_coe_nonZeroDivisors {x y : R'} {c : R'⁰} : c * x ∣ c * y ↔ x ∣ y :=
  dvd_cancel_left_mem_nonZeroDivisors c.prop

theorem zero_not_mem_nonZeroDivisors [Nontrivial M] : 0 ∉ M⁰ :=
  fun h ↦ one_ne_zero <| h 1 <| mul_zero _

theorem nonZeroDivisors.ne_zero [Nontrivial M] {x} (hx : x ∈ M⁰) : x ≠ 0 :=
  ne_of_mem_of_not_mem hx zero_not_mem_nonZeroDivisors
#align non_zero_divisors.ne_zero nonZeroDivisors.ne_zero

theorem nonZeroDivisors.coe_ne_zero [Nontrivial M] (x : M⁰) : (x : M) ≠ 0 :=
  nonZeroDivisors.ne_zero x.2
#align non_zero_divisors.coe_ne_zero nonZeroDivisors.coe_ne_zero

theorem mul_mem_nonZeroDivisors {a b : M₁} : a * b ∈ M₁⁰ ↔ a ∈ M₁⁰ ∧ b ∈ M₁⁰ := by
  constructor
  · intro h
    constructor <;> intro x h' <;> apply h
    · rw [← mul_assoc, h', zero_mul]
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
  · rintro ⟨ha, hb⟩ x hx
    apply ha
    apply hb
    rw [mul_assoc, hx]
#align mul_mem_non_zero_divisors mul_mem_nonZeroDivisors

theorem isUnit_of_mem_nonZeroDivisors {G₀ : Type*} [GroupWithZero G₀] {x : G₀}
    (hx : x ∈ nonZeroDivisors G₀) : IsUnit x :=
  ⟨⟨x, x⁻¹, mul_inv_cancel (nonZeroDivisors.ne_zero hx),
    inv_mul_cancel (nonZeroDivisors.ne_zero hx)⟩, rfl⟩
#align is_unit_of_mem_non_zero_divisors isUnit_of_mem_nonZeroDivisors

lemma IsUnit.mem_nonZeroDivisors {a : M} (ha : IsUnit a) : a ∈ M⁰ :=
  fun _ h ↦ ha.mul_left_eq_zero.mp h

theorem eq_zero_of_ne_zero_of_mul_right_eq_zero [NoZeroDivisors M] {x y : M} (hnx : x ≠ 0)
    (hxy : y * x = 0) : y = 0 :=
  Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx
#align eq_zero_of_ne_zero_of_mul_right_eq_zero eq_zero_of_ne_zero_of_mul_right_eq_zero

theorem eq_zero_of_ne_zero_of_mul_left_eq_zero [NoZeroDivisors M] {x y : M} (hnx : x ≠ 0)
    (hxy : x * y = 0) : y = 0 :=
  Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx
#align eq_zero_of_ne_zero_of_mul_left_eq_zero eq_zero_of_ne_zero_of_mul_left_eq_zero

theorem mem_nonZeroDivisors_of_ne_zero [NoZeroDivisors M] {x : M} (hx : x ≠ 0) : x ∈ M⁰ := fun _ ↦
  eq_zero_of_ne_zero_of_mul_right_eq_zero hx
#align mem_non_zero_divisors_of_ne_zero mem_nonZeroDivisors_of_ne_zero

theorem mem_nonZeroDivisors_iff_ne_zero [NoZeroDivisors M] [Nontrivial M] {x : M} :
    x ∈ M⁰ ↔ x ≠ 0 := ⟨nonZeroDivisors.ne_zero, mem_nonZeroDivisors_of_ne_zero⟩
#align mem_non_zero_divisors_iff_ne_zero mem_nonZeroDivisors_iff_ne_zero

variable [FunLike F M M']

theorem map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M] [ZeroHomClass F M M'] (g : F)
    (hg : Function.Injective (g : M → M')) {x : M} (h : x ∈ M⁰) : g x ≠ 0 := fun h0 ↦
  one_ne_zero (h 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))
#align map_ne_zero_of_mem_non_zero_divisors map_ne_zero_of_mem_nonZeroDivisors

theorem map_mem_nonZeroDivisors [Nontrivial M] [NoZeroDivisors M'] [ZeroHomClass F M M'] (g : F)
    (hg : Function.Injective g) {x : M} (h : x ∈ M⁰) : g x ∈ M'⁰ := fun _ hz ↦
  eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h) hz
#align map_mem_non_zero_divisors map_mem_nonZeroDivisors

theorem le_nonZeroDivisors_of_noZeroDivisors [NoZeroDivisors M] {S : Submonoid M}
    (hS : (0 : M) ∉ S) : S ≤ M⁰ := fun _ hx _ hy ↦
  Or.recOn (eq_zero_or_eq_zero_of_mul_eq_zero hy) (fun h ↦ h) fun h ↦
    absurd (h ▸ hx : (0 : M) ∈ S) hS
#align le_non_zero_divisors_of_no_zero_divisors le_nonZeroDivisors_of_noZeroDivisors

theorem powers_le_nonZeroDivisors_of_noZeroDivisors [NoZeroDivisors M] {a : M} (ha : a ≠ 0) :
    Submonoid.powers a ≤ M⁰ :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦ absurd (h.recOn fun _ hn ↦ pow_eq_zero hn) ha
#align powers_le_non_zero_divisors_of_no_zero_divisors powers_le_nonZeroDivisors_of_noZeroDivisors

theorem map_le_nonZeroDivisors_of_injective [NoZeroDivisors M'] [MonoidWithZeroHomClass F M M']
    (f : F) (hf : Function.Injective f) {S : Submonoid M} (hS : S ≤ M⁰) : S.map f ≤ M'⁰ := by
  cases subsingleton_or_nontrivial M
  · simp [Subsingleton.elim S ⊥]
  · exact le_nonZeroDivisors_of_noZeroDivisors fun h ↦
      let ⟨x, hx, hx0⟩ := h
      zero_ne_one (hS (hf (hx0.trans (map_zero f).symm) ▸ hx : 0 ∈ S) 1 (mul_zero 1)).symm
#align map_le_non_zero_divisors_of_injective map_le_nonZeroDivisors_of_injective

theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M']
    [MonoidWithZeroHomClass F M M'] (f : F) (hf : Function.Injective f) : M⁰ ≤ M'⁰.comap f :=
  Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)
#align non_zero_divisors_le_comap_non_zero_divisors_of_injective nonZeroDivisors_le_comap_nonZeroDivisors_of_injective

/-- In a finite ring, an element is a unit iff it is a non-zero-divisor. -/
lemma isUnit_iff_mem_nonZeroDivisors_of_finite [Finite R] {a : R} :
    IsUnit a ↔ a ∈ nonZeroDivisors R := by
  refine ⟨IsUnit.mem_nonZeroDivisors, fun ha ↦ ?_⟩
  rw [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]
  intro b c hbc
  rw [← sub_eq_zero, ← sub_mul] at hbc
  exact sub_eq_zero.mp (ha _ hbc)

end nonZeroDivisors

section nonZeroSMulDivisors

open nonZeroSMulDivisors nonZeroDivisors

variable {R M : Type*} [MonoidWithZero R] [Zero M] [MulAction R M]

lemma mem_nonZeroSMulDivisors_iff {x : R} : x ∈ R⁰[M] ↔ ∀ (m : M), x • m = 0 → m = 0 := Iff.rfl

variable (R)

@[simp]
lemma unop_nonZeroSMulDivisors_mulOpposite_eq_nonZeroDivisors :
    (Rᵐᵒᵖ ⁰[R]).unop = R⁰ := rfl

/-- The non-zero `•`-divisors with `•` as right multiplication correspond with the non-zero
divisors. Note that the `MulOpposite` is needed because we defined `nonZeroDivisors` with
multiplication on the right. -/
lemma nonZeroSMulDivisors_mulOpposite_eq_op_nonZeroDivisors :
    Rᵐᵒᵖ ⁰[R] = R⁰.op := rfl

end nonZeroSMulDivisors

noncomputable section Associated

open nonZeroDivisors

/-- The units of the monoid of non zero divisors of `α` are equivalent to the units of `α`. -/
def nonZeroDivisorsUnitsEquiv (α : Type*) [MonoidWithZero α] :
    (α⁰)ˣ ≃* αˣ :=
  MulEquiv.ofBijective (Units.map α⁰.subtype) ⟨Units.map_injective Subtype.val_injective,
    fun u ↦ ⟨IsUnit.unit ⟨⟨⟨u, IsUnit.mem_nonZeroDivisors u.isUnit⟩, ⟨(u⁻¹ : αˣ),
        IsUnit.mem_nonZeroDivisors u⁻¹.isUnit⟩, by simp, by simp⟩, rfl⟩,
      by rw [Units.ext_iff, IsUnit.unit_of_val_units, Units.coe_map, Submonoid.coe_subtype]⟩⟩

@[simp]
theorem nonZeroDivisorsUnitsEquiv_apply (α : Type*) [MonoidWithZero α] (u : (α⁰)ˣ) :
    nonZeroDivisorsUnitsEquiv α u = (u : α) := rfl

@[simp]
theorem nonZeroDivisorsUnitsEquiv_symm_apply (α : Type*) [MonoidWithZero α] (u : αˣ) :
    ((nonZeroDivisorsUnitsEquiv α).symm u : α) = (u : α) := by
  obtain ⟨v, rfl⟩ := (nonZeroDivisorsUnitsEquiv α).surjective u
  rw [MulEquiv.symm_apply_apply, nonZeroDivisorsUnitsEquiv_apply]

theorem Associates_mk_mem_nonZeroDivisors_iff {α : Type*} [CommMonoidWithZero α] (a : α) :
    Associates.mk a ∈ (Associates α)⁰ ↔ a ∈ α⁰ := by
  rw [mem_nonZeroDivisors_iff, mem_nonZeroDivisors_iff, ← not_iff_not]
  push_neg
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_eq_mk]
  · refine fun ⟨b, hb₁, hb₂⟩ ↦ ⟨Associates.mk b, ?_, by rwa [Associates.mk_ne_zero]⟩
    rw [Associates.mk_mul_mk, hb₁, Associates.mk_zero]

/-- To any class in `Associates α⁰`, one can associate a class in `(Associates α)⁰` by sending a
representative `a : α⁰` of the class to the class of `(a : α)`. The map obtained is in fact a
`MulEquiv`, see `AssociatesNonZeroDivisorsMulEquiv`. -/
def AssociatesNonZeroDivisorsMonoidHom (α : Type*) [CommMonoidWithZero α] :
    Associates α⁰ →* (Associates α)⁰ where
  toFun := Quotient.lift (fun ⟨x, _⟩ ↦  ⟨Associates.mk x, by
      rwa [Associates_mk_mem_nonZeroDivisors_iff]⟩) (by
    rintro _ _ ⟨v, hv⟩
    rw [Subtype.mk.injEq, Associates.mk_eq_mk_iff_associated]
    exact ⟨nonZeroDivisorsUnitsEquiv α v, by
      rw [nonZeroDivisorsUnitsEquiv_apply, ← hv, Submonoid.coe_mul]⟩)
  map_one' := rfl
  map_mul' x y := Quotient.inductionOn₂ x y fun _ _ ↦ rfl

@[simp]
theorem AssociatesNonZeroDivisorsMonoidHom_apply (α : Type*) [CommMonoidWithZero α] (a : α⁰) :
    (AssociatesNonZeroDivisorsMonoidHom α ⟦a⟧ : Associates α) = Associates.mk (a : α) := rfl

/-- This is the `MulEquiv` version of `AssociatesNonZeroDivisorsMonoidHom`. -/
def AssociatesNonZeroDivisorsMulEquiv (α : Type*) [CommMonoidWithZero α] :
    Associates α⁰ ≃* (Associates α)⁰  := by
  refine MulEquiv.ofBijective (AssociatesNonZeroDivisorsMonoidHom α) ⟨?_, ?_⟩
  · rintro ⟨_⟩ ⟨_⟩ h
    rw [Subtype.ext_iff, Associates.quot_mk_eq_mk, Associates.quot_mk_eq_mk,
      AssociatesNonZeroDivisorsMonoidHom_apply, AssociatesNonZeroDivisorsMonoidHom_apply] at h
    obtain ⟨u, hu⟩ := Associates.mk_eq_mk_iff_associated.mp h
    rw [Associates.quot_mk_eq_mk, Associates.quot_mk_eq_mk]
    refine Associates.mk_eq_mk_iff_associated.mpr ⟨?_, ?_⟩
    · exact (nonZeroDivisorsUnitsEquiv α).symm u
    · rwa [Subtype.ext_iff, Submonoid.coe_mul, nonZeroDivisorsUnitsEquiv_symm_apply]
  · rintro ⟨⟨y⟩, hy⟩
    refine ⟨⟦⟨y, ?_⟩⟧, ?_⟩
    · rwa [← Associates_mk_mem_nonZeroDivisors_iff, ← Associates.quot_mk_eq_mk]
    · rw [Subtype.ext_iff, AssociatesNonZeroDivisorsMonoidHom_apply, ← Associates.quot_mk_eq_mk]

@[simp]
theorem AssociatesNonZeroDivisorsMulEquiv_apply (α : Type*) [CommMonoidWithZero α] (a : α⁰) :
    (AssociatesNonZeroDivisorsMulEquiv α ⟦a⟧ : Associates α) = Associates.mk (a : α) := rfl

end Associated

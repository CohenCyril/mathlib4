/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

#align_import group_theory.subsemigroup.center from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Set.addCenter`: the center of an additive magma
* `Set.centralizer`: the centralizer of a subset of a magma
* `Set.addCentralizer`: the centralizer of a subset of an additive magma

## See also

See `Mathlib.GroupTheory.Subsemigroup.Center` for the definition of the center as a subsemigroup:
* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

See `Mathlib.GroupTheory.Subsemigroup.Centralizer` for the definition of the centralizer
as a subsemigroup:
* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/

assert_not_exists Finset
assert_not_exists MonoidWithZero
assert_not_exists Subsemigroup

variable {M : Type*} {S T : Set M}

/-- Conditions for an element to be additively central -/
structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : z + a = a + z
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- middle associative addition property -/
  mid_assoc (a c : M) : (a + z) + c = a + (z + c)
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)

/-- Conditions for an element to be multiplicatively central -/
@[to_additive]
structure IsMulCentral [Mul M] (z : M) : Prop where
  /-- multiplication commutes -/
  comm (a : M) : z * a = a * z
  /-- associative property for left multiplication -/
  left_assoc (b c : M) : z * (b * c) = (z * b) * c
  /-- middle associative multiplication property -/
  mid_assoc (a c : M) : (a * z) * c = a * (z * c)
  /-- associative property for right multiplication -/
  right_assoc (a b : M) : (a * b) * z = a * (b * z)

attribute [mk_iff] IsMulCentral IsAddCentral
attribute [to_additive existing] isMulCentral_iff

namespace IsMulCentral

variable {a b c : M} [Mul M]

-- cf. `Commute.left_comm`
@[to_additive]
protected theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [h.comm, h.right_assoc]

-- cf. `Commute.right_comm`
@[to_additive]
protected theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, h.mid_assoc, h.comm]

end IsMulCentral

namespace Set

/-! ### Center -/

section Mul
variable [Mul M]

variable (M) in
/-- The center of a magma. -/
@[to_additive addCenter " The center of an additive magma. "]
def center : Set M :=
  { z | IsMulCentral z }
#align set.center Set.center
#align set.add_center Set.addCenter

variable (S) in
/-- The centralizer of a subset of a magma. -/
@[to_additive addCentralizer " The centralizer of a subset of an additive magma. "]
def centralizer [Mul M] : Set M := {c | ∀ m ∈ S, m * c = c * m}
#align set.centralizer Set.centralizer
#align set.add_centralizer Set.addCentralizer

-- Porting note: The `to_additive` version used to be `mem_addCenter` without the iff
@[to_additive mem_addCenter_iff]
theorem mem_center_iff {z : M} : z ∈ center M ↔ IsMulCentral z :=
  Iff.rfl
#align set.mem_center_iff Set.mem_center_iff
#align set.mem_add_center Set.mem_addCenter_iff

@[to_additive mem_addCentralizer]
lemma mem_centralizer_iff [Mul M] {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m := Iff.rfl
#align set.mem_centralizer_iff Set.mem_centralizer_iff
#align set.mem_add_centralizer Set.mem_addCentralizer

@[to_additive (attr := simp) add_mem_addCenter]
theorem mul_mem_center [Mul M] {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M where
  comm a := calc
    z₁ * z₂ * a = z₂ * z₁ * a := by rw [hz₁.comm]
    _ = z₂ * (z₁ * a) := by rw [hz₁.mid_assoc z₂]
    _ = (a * z₁) * z₂ := by rw [hz₁.comm, hz₂.comm]
    _ = a * (z₁ * z₂) := by rw [hz₂.right_assoc a z₁]
  left_assoc (b c : M) := calc
    z₁ * z₂ * (b * c) = z₁ * (z₂ * (b * c)) := by rw [hz₂.mid_assoc]
    _ = z₁ * ((z₂ * b) * c) := by rw [hz₂.left_assoc]
    _ = (z₁ * (z₂ * b)) * c := by rw [hz₁.left_assoc]
    _ = z₁ * z₂ * b * c := by rw [hz₂.mid_assoc]
  mid_assoc (a c : M) := calc
    a * (z₁ * z₂) * c = ((a * z₁) * z₂) * c := by rw [hz₁.mid_assoc]
    _ = (a * z₁) * (z₂ * c) := by rw [hz₂.mid_assoc]
    _ = a * (z₁ * (z₂ * c)) := by rw [hz₁.mid_assoc]
    _ = a * (z₁ * z₂ * c) := by rw [hz₂.mid_assoc]
  right_assoc (a b : M) := calc
    a * b * (z₁ * z₂) = ((a * b) * z₁) * z₂ := by rw [hz₂.right_assoc]
    _ = (a * (b * z₁)) * z₂ := by rw [hz₁.right_assoc]
    _ =  a * ((b * z₁) * z₂) := by rw [hz₂.right_assoc]
    _ = a * (b * (z₁ * z₂)) := by rw [hz₁.mid_assoc]
#align set.mul_mem_center Set.mul_mem_center
#align set.add_mem_add_center Set.add_mem_addCenter

@[to_additive addCenter_subset_addCentralizer]
lemma center_subset_centralizer (S : Set M) : Set.center M ⊆ S.centralizer :=
  fun _ hx m _ ↦ (hx.comm m).symm
#align set.center_subset_centralizer Set.center_subset_centralizer
#align set.add_center_subset_add_centralizer Set.addCenter_subset_addCentralizer

@[to_additive (attr := gcongr) addCentralizer_subset]
lemma centralizer_subset (h : S ⊆ T) : centralizer T ⊆ centralizer S := fun _ ht s hs ↦ ht s (h hs)
#align set.centralizer_subset Set.centralizer_subset
#align set.add_centralizer_subset Set.addCentralizer_subset

@[to_additive subset_addCentralizer_addCentralizer]
lemma subset_centralizer_centralizer : S ⊆ S.centralizer.centralizer := by
  intro x hx
  simp only [Set.mem_centralizer_iff]
  exact fun y hy => (hy x hx).symm

@[to_additive (attr := simp) addCentralizer_addCentralizer_addCentralizer]
lemma centralizer_centralizer_centralizer (S : Set M) :
    S.centralizer.centralizer.centralizer = S.centralizer := by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
  intro x hx
  rw [Set.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_centralizer_iff] at hx
  exact hx y <| Set.subset_centralizer_centralizer hy

end Mul

section Semigroup
variable [Semigroup M] {a b : M}

@[to_additive]
theorem _root_.Semigroup.mem_center_iff {z : M} :
    z ∈ Set.center M ↔ ∀ g, g * z = z * g := ⟨fun a g ↦ by rw [IsMulCentral.comm a g],
  fun h ↦ ⟨fun _ ↦ (Commute.eq (h _)).symm, fun _ _ ↦ (mul_assoc z _ _).symm,
  fun _ _ ↦ mul_assoc _ z _, fun _ _ ↦ mul_assoc _ _ z⟩ ⟩

@[to_additive (attr := simp) add_mem_addCentralizer]
lemma mul_mem_centralizer (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S := fun g hg ↦ by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]
#align set.mul_mem_centralizer Set.mul_mem_centralizer
#align set.add_mem_add_centralizer Set.add_mem_addCentralizer

@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]
theorem centralizer_eq_top_iff_subset : centralizer S = Set.univ ↔ S ⊆ center M :=
  eq_top_iff.trans <| ⟨
    fun h _ hx ↦ Semigroup.mem_center_iff.mpr fun _ ↦ by rw [h trivial _ hx],
    fun h _ _ _ hm ↦ (h hm).comm _⟩
#align set.centralizer_eq_top_iff_subset Set.centralizer_eq_top_iff_subset
#align set.add_centralizer_eq_top_iff_subset Set.addCentralizer_eq_top_iff_subset

variable (M) in
@[to_additive (attr := simp) addCentralizer_univ]
lemma centralizer_univ : centralizer univ = center M :=
  Subset.antisymm (fun _ ha ↦ Semigroup.mem_center_iff.mpr fun b ↦ ha b (Set.mem_univ b))
  fun _ ha b _ ↦ (ha.comm b).symm
#align set.centralizer_univ Set.centralizer_univ
#align set.add_centralizer_univ Set.addCentralizer_univ

-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`
@[to_additive decidableMemAddCenter]
instance decidableMemCenter [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)
#align set.decidable_mem_center Set.decidableMemCenter

@[to_additive decidableMemAddCentralizer]
instance decidableMemCentralizer [Mul M] [∀ a : M, Decidable <| ∀ b ∈ S, b * a = a * b] :
    DecidablePred (· ∈ centralizer S) := fun _ ↦ decidable_of_iff' _ mem_centralizer_iff
#align set.decidable_mem_centralizer Set.decidableMemCentralizer
#align set.decidable_mem_add_centralizer Set.decidableMemAddCentralizer

end Semigroup

section CommSemigroup
variable (M)

@[to_additive (attr := simp) addCenter_eq_univ]
theorem center_eq_univ [CommSemigroup M] : center M = univ :=
  (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)
#align set.center_eq_univ Set.center_eq_univ
#align set.add_center_eq_univ Set.addCenter_eq_univ

@[to_additive (attr := simp) addCentralizer_eq_univ]
lemma centralizer_eq_univ [CommSemigroup M] : centralizer S = univ :=
  eq_univ_of_forall fun _ _ _ ↦ mul_comm _ _
#align set.centralizer_eq_univ Set.centralizer_eq_univ
#align set.add_centralizer_eq_univ Set.addCentralizer_eq_univ

end CommSemigroup

section MulOneClass
variable [MulOneClass M]

@[to_additive (attr := simp) zero_mem_addCenter]
theorem one_mem_center [MulOneClass M] : (1 : M) ∈ Set.center M where
  comm _  := by rw [one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  mid_assoc _ _ := by rw [mul_one, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]
#align set.one_mem_center Set.one_mem_center
#align set.zero_mem_add_center Set.zero_mem_addCenter

@[to_additive (attr := simp) zero_mem_addCentralizer]
lemma one_mem_centralizer : (1 : M) ∈ centralizer S := by simp [mem_centralizer_iff]
#align set.one_mem_centralizer Set.one_mem_centralizer
#align set.zero_mem_add_centralizer Set.zero_mem_addCentralizer

end MulOneClass

section Monoid
variable [Monoid M]

@[to_additive subset_addCenter_add_units]
theorem subset_center_units : ((↑) : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun _ ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← Units.eq_iff, Units.val_mul, Units.val_mul, ha.comm]
#align set.subset_center_units Set.subset_center_units
#align set.subset_add_center_add_units Set.subset_addCenter_add_units

@[to_additive (attr := simp)]
theorem units_inv_mem_center {a : Mˣ} (ha : ↑a ∈ Set.center M) : ↑a⁻¹ ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

@[simp]
theorem invOf_mem_center {a : M} [Invertible a] (ha : a ∈ Set.center M) : ⅟a ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

end Monoid

section DivisionMonoid
variable [DivisionMonoid M] {a b : M}

@[to_additive (attr := simp) neg_mem_addCenter]
theorem inv_mem_center (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj, mul_inv_rev, inv_inv, ha.comm, mul_inv_rev, inv_inv]
#align set.inv_mem_center Set.inv_mem_center
#align set.neg_mem_add_center Set.neg_mem_addCenter
#align set.inv_mem_center₀ Set.inv_mem_center

@[to_additive (attr := simp) sub_mem_addCenter]
theorem div_mem_center (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)
#align set.div_mem_center Set.div_mem_center
#align set.sub_mem_add_center Set.sub_mem_addCenter
#align set.div_mem_center₀ Set.div_mem_center

@[deprecated (since := "2024-05-19")] alias inv_mem_center₀ := inv_mem_center
@[deprecated (since := "2024-05-19")] alias div_mem_center₀ := div_mem_center

end DivisionMonoid

section Group
variable [Group M] {a b : M}

@[to_additive (attr := simp) neg_mem_addCentralizer]
lemma inv_mem_centralizer (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  fun g hg ↦ by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]
#align set.inv_mem_centralizer Set.inv_mem_centralizer
#align set.neg_mem_add_centralizer Set.neg_mem_addCentralizer

@[to_additive (attr := simp) sub_mem_addCentralizer]
lemma div_mem_centralizer (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer hb)
#align set.div_mem_centralizer Set.div_mem_centralizer
#align set.sub_mem_add_centralizer Set.sub_mem_addCentralizer

end Group
end Set

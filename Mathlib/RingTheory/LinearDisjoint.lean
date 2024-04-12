/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.LinearDisjoint
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!

# Linearly disjoint of subalgebras

This file contains basics about the linearly disjoint of subalgebras.

## Main definitions

- ...

## Main results

- ...

## Tags

linearly disjoint, linearly independent, tensor product

## TODO

- ...

-/

open scoped Classical TensorProduct

open FiniteDimensional

noncomputable section

universe u v w

namespace Subalgebra

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras of `S / R`,
then `A` and `B` are linearly disjoint, if they are linearly disjoint as submodules of `S`. -/
protected def LinearDisjoint : Prop := (toSubmodule A).LinearDisjoint (toSubmodule B)

variable {A B}

@[nontriviality]
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_subsingleton

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem LinearDisjoint.symm_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : B.LinearDisjoint A :=
  Submodule.LinearDisjoint.symm_of_commute H hc

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem linearDisjoint_symm_of_commute
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

namespace LinearDisjoint

variable (A B)

theorem of_bot_left : (⊥ : Subalgebra R S).LinearDisjoint B :=
  Submodule.LinearDisjoint.of_one_left _

theorem of_bot_right : A.LinearDisjoint ⊥ :=
  Submodule.LinearDisjoint.of_one_right _

-- skip of_linearDisjoint_finite_left ?? (not correct ??)

-- skip of_linearDisjoint_finite_right ?? (not correct ??)

-- skip of_linearDisjoint_finite ?? (not correct ??)

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, there is the natural map
`A ⊗[R] B →ₐ[R] S` induced by multiplication in `S`. -/
def mulMap := Algebra.TensorProduct.productMap A.val B.val

variable {A B}

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem linearDisjoint_symm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

@[simp]
theorem mulMap_tmul (a : A) (b : B) : mulMap A B (a ⊗ₜ[R] b) = a.1 * b.1 := rfl

variable (A B)

theorem mulMap_toLinearMap : (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (toSubmodule B) :=
  rfl

theorem mulMap_comm : mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R B A) := by
  ext <;> simp

theorem mulMap_range : (A.mulMap B).range = A ⊔ B := by
  simp_rw [mulMap, Algebra.TensorProduct.productMap_range, Subalgebra.range_val]

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, there is the natural map
`A ⊗[R] B →ₐ[R] A ⊔ B` induced by multiplication in `S`,
which is surjective (`Subalgebra.mulMap'_surjective`). -/
def mulMap' := (equivOfEq _ _ (mulMap_range A B)).toAlgHom.comp (mulMap A B).rangeRestrict

theorem mulMap'_surjective : Function.Surjective (mulMap' A B) := by
  simp_rw [mulMap', AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EquivLike.comp_surjective, AlgHom.rangeRestrict_surjective]

namespace LinearDisjoint

variable {A B}

variable (H : A.LinearDisjoint B)

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint, then there is the natural isomorphism
`A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`. -/
def mulMap := (AlgEquiv.ofInjective (A.mulMap B) H).trans (equivOfEq _ _ (mulMap_range A B))

@[simp]
theorem coe_mulMap_tmul (a : A) (b : B) : (H.mulMap (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl

theorem sup_free_of_free [Module.Free R A] [Module.Free R B] : Module.Free R ↥(A ⊔ B) :=
  Module.Free.of_equiv H.mulMap.toLinearEquiv

end LinearDisjoint

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (A B : Subalgebra R S)

section TODO

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

-- TODO: move to suitable file
/-- The ordered set of subalgebras of the opposite algebra is isomorphic to the
ordered set of subalgebras. -/
def _root_.Subalgebra.equivOpposite : Subalgebra R Aᵐᵒᵖ ≃o Subalgebra R A where
  toFun S := { MulOpposite.unop (Submodule.equivOpposite (toSubmodule S)) with
    mul_mem' := fun ha hb ↦ S.mul_mem hb ha
    algebraMap_mem' := S.algebraMap_mem }
  invFun S := { Submodule.equivOpposite.symm (MulOpposite.op (toSubmodule S)) with
    mul_mem' := fun ha hb ↦ S.mul_mem hb ha
    algebraMap_mem' := S.algebraMap_mem }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {_} {_} :=
    Submodule.comap_le_comap_iff_of_surjective (MulOpposite.opLinearEquiv R).surjective _ _

-- TODO: move to suitable file
/-- There is a natural linear isomorphism from a subalgebra `S` to
its `Subalgebra.equivOpposite`. -/
def _root_.Subalgebra.opLinearEquiv (S : Subalgebra R A) : S ≃ₗ[R] equivOpposite.symm S :=
  ((MulOpposite.opLinearEquiv R).symm.ofSubmodule' (toSubmodule S)).symm

-- TODO: move to suitable file
/-- There is a natural algebra isomorphism from a subalgebra `S` to
the opposite of its `Subalgebra.equivOpposite`. -/
def _root_.Subalgebra.opAlgEquiv (S : Subalgebra R A) : S ≃ₐ[R] (equivOpposite.symm S)ᵐᵒᵖ where
  __ := opLinearEquiv S ≪≫ₗ MulOpposite.opLinearEquiv _
  map_mul' _ _ := rfl
  commutes' _ := rfl

-- TODO: move to suitable file
/-- There is a natural algebra isomorphism from the opposite of a subalgebra `S` to
the its `Subalgebra.equivOpposite`. -/
def _root_.Subalgebra.opAlgEquiv' (S : Subalgebra R A) : Sᵐᵒᵖ ≃ₐ[R] equivOpposite.symm S where
  __ := (MulOpposite.opLinearEquiv _).symm ≪≫ₗ opLinearEquiv S
  map_mul' _ _ := rfl
  commutes' _ := rfl

end TODO

lemma mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι → A) :
    LinearMap.ker (Submodule.LinearDisjoint.mulLeftMap
      (M := toSubmodule A) (toSubmodule B) a) = ⊥ ↔
    LinearIndependent (equivOpposite.symm B) (MulOpposite.op ∘ A.val ∘ a) := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ toSubmodule B) := Finsupp.instAddCommGroup
  letI : AddCommGroup (ι →₀ equivOpposite.symm B) := Finsupp.instAddCommGroup
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ B) →ₗ[R] S :=
    Submodule.LinearDisjoint.mulLeftMap (M := toSubmodule A) (toSubmodule B) a
  let j : (ι →₀ B) →ₗ[R] S := (MulOpposite.opLinearEquiv _).symm.toLinearMap ∘ₗ
    (Finsupp.total ι Sᵐᵒᵖ (equivOpposite.symm B) (MulOpposite.op ∘ A.val ∘ a)).restrictScalars R ∘ₗ
    (Finsupp.mapRange.linearEquiv (opLinearEquiv B)).toLinearMap
  suffices i = j by
    change Function.Injective i ↔ _
    simp_rw [this, j, LinearMap.coe_comp,
      LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]
    rfl
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    Finsupp.mapRange.linearEquiv_toLinearMap, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv_symm, LinearMap.coe_restrictScalars,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.total_single,
    MulOpposite.unop_smul, MulOpposite.unop_op, i, j]
  exact Submodule.LinearDisjoint.mulLeftMap_apply_single _ _ _

variable {A B} in
theorem map_linearIndependent_left_op_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) :
    LinearIndependent (equivOpposite.symm B) (MulOpposite.op ∘ A.val ∘ a) := by
  haveI : Module.Flat R (toSubmodule B) := ‹_›
  have h := Submodule.LinearDisjoint.map_linearIndependent_left_of_flat H ha
  rwa [mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at h

theorem of_map_linearIndependent_left_op {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent (equivOpposite.symm B) (MulOpposite.op ∘ A.val ∘ a)) :
    A.LinearDisjoint B := by
  rw [← mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at H
  exact Submodule.LinearDisjoint.of_map_linearIndependent_left _ _ a H

lemma mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι → B) :
    LinearMap.ker (Submodule.LinearDisjoint.mulRightMap
      (toSubmodule A) (N := toSubmodule B) b) = ⊥ ↔
    LinearIndependent A (B.val ∘ b) := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ toSubmodule A) := Finsupp.instAddCommGroup
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ A) →ₗ[R] S :=
    Submodule.LinearDisjoint.mulRightMap (toSubmodule A) (N := toSubmodule B) b
  let j : (ι →₀ A) →ₗ[R] S := (Finsupp.total ι S A (B.val ∘ b)).restrictScalars R
  suffices i = j by change Function.Injective i ↔ Function.Injective j; rw [this]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    LinearMap.coe_restrictScalars, Finsupp.total_single, i, j]
  exact Submodule.LinearDisjoint.mulRightMap_apply_single _ _ _

variable {A B} in
theorem map_linearIndependent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A]
    {ι : Type*} {b : ι → B} (hb : LinearIndependent R b) :
    LinearIndependent A (B.val ∘ b) := by
  haveI : Module.Flat R (toSubmodule A) := ‹_›
  have h := Submodule.LinearDisjoint.map_linearIndependent_right_of_flat H hb
  rwa [mulRightMap_ker_eq_bot_iff_linearIndependent] at h

theorem of_map_linearIndependent_right {ι : Type*} (b : Basis ι R B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B := by
  rw [← mulRightMap_ker_eq_bot_iff_linearIndependent] at H
  exact Submodule.LinearDisjoint.of_map_linearIndependent_right _ _ b H

variable {A B} in
theorem map_linearIndependent_left_of_flat_of_commute (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : LinearIndependent B (A.val ∘ a) :=
  (H.symm_of_commute hc).map_linearIndependent_right_of_flat ha

theorem of_map_linearIndependent_left_of_commute {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) (hc : ∀ (a : A) (b : B), Commute a.1 b.1) :
    A.LinearDisjoint B :=
  (of_map_linearIndependent_right B A a H).symm_of_commute fun _ _ ↦ (hc _ _).symm

variable {A B} in
theorem map_linearIndependent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R A]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 := by
  haveI : Module.Flat R (toSubmodule A) := ‹_›
  exact Submodule.LinearDisjoint.map_linearIndependent_mul_of_flat_left H ha hb

variable {A B} in
theorem map_linearIndependent_mul_of_flat_right (H : A.LinearDisjoint B) [Module.Flat R B]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 := by
  haveI : Module.Flat R (toSubmodule B) := ‹_›
  exact Submodule.LinearDisjoint.map_linearIndependent_mul_of_flat_right H ha hb

variable {A B} in
theorem map_linearIndependent_mul_of_flat (H : A.LinearDisjoint B)
    (hf : Module.Flat R A ∨ Module.Flat R B)
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.map_linearIndependent_mul_of_flat H hf ha hb

theorem of_map_linearIndependent_mul {κ ι : Type*} (a : Basis κ R A) (b : Basis ι R B)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_map_linearIndependent_mul _ _ a b H

variable {A B}

variable (H : A.LinearDisjoint B)

theorem of_le_left_of_flat {A' : Subalgebra R S}
    (h : A' ≤ A) [Module.Flat R B] : A'.LinearDisjoint B := by
  haveI : Module.Flat R (toSubmodule B) := ‹_›
  exact Submodule.LinearDisjoint.of_le_left_of_flat H h

theorem of_le_right_of_flat {B' : Subalgebra R S}
    (h : B' ≤ B) [Module.Flat R A] : A.LinearDisjoint B' := by
  haveI : Module.Flat R (toSubmodule A) := ‹_›
  exact Submodule.LinearDisjoint.of_le_right_of_flat H h

theorem of_le_of_flat_right {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R B] [Module.Flat R A'] :
    A'.LinearDisjoint B' := (H.of_le_left_of_flat ha).of_le_right_of_flat hb

theorem of_le_of_flat_left {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R A] [Module.Flat R B'] :
    A'.LinearDisjoint B' := (H.of_le_right_of_flat hb).of_le_left_of_flat ha

theorem rank_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 := by
  nontriviality R
  refine le_antisymm (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat H hf hc) ?_
  have : 1 ≤ Module.rank R (⊥ : Subalgebra R S) := by
    let s : Set (⊥ : Subalgebra R S) := {1}
    have : LinearIndependent R fun x : s ↦ x.1 := by
      rw [LinearIndependent, LinearMap.ker_eq_bot]
      have : (Finsupp.total s (⊥ : Subalgebra R S) R fun x ↦ x.1) =
          Algebra.linearMap R (⊥ : Subalgebra R S) ∘ₗ
          (Finsupp.LinearEquiv.finsuppUnique R R s).toLinearMap := by
        ext x
        simp [show x = ⟨1, Set.mem_singleton 1⟩ from Subsingleton.elim _ _]
      simp_rw [this, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp]
      intro x y hxy
      exact hinj congr(val _ $(hxy))
    simpa only [Cardinal.mk_fintype, Fintype.card_ofSubsingleton,
      Nat.cast_one, s] using this.cardinal_le_rank'
  exact this.trans <| rank_le_of_submodule (toSubmodule (⊥ : Subalgebra R S)) (toSubmodule (A ⊓ B))
    (bot_le : (⊥ : Subalgebra R S) ≤ A ⊓ B)

theorem rank_inf_eq_one_of_commute_of_flat_left_of_inj [Module.Flat R A]
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inl ‹_›) hc hinj

theorem rank_inf_eq_one_of_commute_of_flat_right_of_inj [Module.Flat R B]
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inr ‹_›) hc hinj

theorem rank_eq_one_of_commute_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hc : ∀ (a b : A), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.rank_inf_eq_one_of_commute_of_flat_left_of_inj hc hinj

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

-- TODO: remove once #12025 is merged
instance _root_.Subalgebra.finite_bot {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E] :
    Module.Finite F (⊥ : Subalgebra F E) := Module.Finite.range (Algebra.linearMap F E)

-- TODO: remove once #12025 is merged
theorem _root_.Subalgebra.finite_sup {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    (E1 E2 : Subalgebra K L) [Module.Finite K E1] [Module.Finite K E2] :
    Module.Finite K ↥(E1 ⊔ E2) := by
  rw [← E1.range_val, ← E2.range_val, ← Algebra.TensorProduct.productMap_range]
  exact Module.Finite.range (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap

variable [CommRing R] [CommRing S] [Algebra R S]

variable (A B : Subalgebra R S)

variable {A B} in
theorem map_linearIndependent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) : LinearIndependent B (A.val ∘ a) :=
  H.map_linearIndependent_left_of_flat_of_commute ha fun _ _ ↦ mul_comm _ _

theorem of_map_linearIndependent_left {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) : A.LinearDisjoint B :=
  of_map_linearIndependent_left_of_commute A B a H fun _ _ ↦ mul_comm _ _

variable {A B}

variable (H : A.LinearDisjoint B)

theorem rank_inf_eq_one_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj hf (fun _ _ ↦ mul_comm _ _) hinj

theorem rank_inf_eq_one_of_flat_left_of_inj [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_left_of_inj (fun _ _ ↦ mul_comm _ _) hinj

theorem rank_inf_eq_one_of_flat_right_of_inj [Module.Flat R B]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_right_of_inj (fun _ _ ↦ mul_comm _ _) hinj

theorem rank_eq_one_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 :=
  H.rank_eq_one_of_commute_of_flat_of_self_of_inj (fun _ _ ↦ mul_comm _ _) hinj

-- TODO: move to suitable place
variable (A B) in
theorem _root_.Subalgebra.rank_sup_le_of_free [Module.Free R A] [Module.Free R B] :
    Module.rank R ↥(A ⊔ B) ≤ Module.rank R A * Module.rank R B := by
  nontriviality R
  rw [← rank_tensorProduct', ← mulMap_range]
  exact rank_range_le (A.mulMap B).toLinearMap

-- TODO: move to suitable place
variable (A B) in
theorem _root_.Subalgebra.finrank_sup_le_of_free [Module.Free R A] [Module.Free R B]
    [Module.Finite R A] [Module.Finite R B] :
    finrank R ↥(A ⊔ B) ≤ finrank R A * finrank R B := by
  nontriviality R using finrank
  rw [← finrank_tensorProduct, ← mulMap_range]
  exact (A.mulMap B).toLinearMap.finrank_range_le

theorem rank_sup_of_free [Module.Free R A] [Module.Free R B] :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank R B := by
  nontriviality R
  rw [← rank_tensorProduct', H.mulMap.toLinearEquiv.rank_eq]

theorem finrank_sup_of_free [Module.Free R A] [Module.Free R B] :
    finrank R ↥(A ⊔ B) = finrank R A * finrank R B := by
  simpa only [map_mul] using congr(Cardinal.toNat $(H.rank_sup_of_free))

/-- TODO: remove once #12076 is merged -/
axiom _root_.Module.Finite.injective_of_surjective_of_injective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] (i f : N →ₗ[R] M)
    (hi : Function.Injective i) (hf : Function.Surjective f) : Function.Injective f

/-- TODO: remove once #9626 is merged -/
axiom _root_.exists_linearIndependent_of_le_finrank
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ f : Fin n → M, LinearIndependent R f

theorem of_finrank_sup_of_free [Module.Free R A] [Module.Free R B]
    [Module.Finite R A] [Module.Finite R B]
    (H : finrank R ↥(A ⊔ B) = finrank R A * finrank R B) : A.LinearDisjoint B := by
  nontriviality R
  rw [← finrank_tensorProduct] at H
  obtain ⟨j, hj⟩ := exists_linearIndependent_of_le_finrank H.ge
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hj
  let j' := Finsupp.total _ ↥(A ⊔ B) R j ∘ₗ
    (LinearEquiv.ofFinrankEq (A ⊗[R] B) _ (by simp)).toLinearMap
  replace hj : Function.Injective j' := by simpa [j']
  have hf : Function.Surjective (mulMap' A B).toLinearMap := mulMap'_surjective A B
  haveI := Subalgebra.finite_sup A B
  exact Subtype.val_injective.comp (Module.Finite.injective_of_surjective_of_injective j' _ hj hf)

/-- If `A` and `B` are linearly disjoint, if `A` is free and `B` is flat,
then `[B[A] : B] = [A : R]`. See also `Subalgebra.adjoin_rank_le`. -/
theorem adjoin_rank_eq_rank_left [Module.Free R A] [Module.Flat R B]
    [Nontrivial R] [Nontrivial S] :
    Module.rank B (Algebra.adjoin B (A : Set S)) = Module.rank R A := by
  rw [← rank_toSubmodule, Module.Free.rank_eq_card_chooseBasisIndex R A,
    A.adjoin_eq_span_basis B (Module.Free.chooseBasis R A)]
  change Module.rank B (Submodule.span B (Set.range (A.val ∘ Module.Free.chooseBasis R A))) = _
  have := H.map_linearIndependent_left_of_flat (Module.Free.chooseBasis R A).linearIndependent
  rw [rank_span this, Cardinal.mk_range_eq _ this.injective]

/-- If `A` and `B` are linearly disjoint, if `B` is free and `A` is flat,
then `[A[B] : A] = [B : R]`. See also `Subalgebra.adjoin_rank_le`. -/
theorem adjoin_rank_eq_rank_right [Module.Free R B] [Module.Flat R A]
    [Nontrivial R] [Nontrivial S] :
    Module.rank A (Algebra.adjoin A (B : Set S)) = Module.rank R B :=
  H.symm.adjoin_rank_eq_rank_left

end LinearDisjoint

end CommRing

section FieldAndRing

namespace LinearDisjoint

variable [Field R] [Ring S] [Algebra R S]

variable {A B : Subalgebra R S} (H : A.LinearDisjoint B)

theorem inf_eq_bot_of_commute (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1) : A ⊓ B = ⊥ :=
  eq_bot_of_rank_le_one (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left H hc)

theorem eq_bot_of_commute_of_self (H : A.LinearDisjoint A)
    (hc : ∀ (a b : A), Commute a.1 b.1) : A = ⊥ := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.inf_eq_bot_of_commute hc

end LinearDisjoint

end FieldAndRing

section FieldAndCommRing

namespace LinearDisjoint

variable [Field R] [CommRing S] [Nontrivial S] [Algebra R S]

variable {A B : Subalgebra R S} (H : A.LinearDisjoint B)

theorem inf_eq_bot : A ⊓ B = ⊥ := H.inf_eq_bot_of_commute fun _ _ ↦ mul_comm _ _

theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  H.eq_bot_of_commute_of_self fun _ _ ↦ mul_comm _ _

end LinearDisjoint

end FieldAndCommRing

end Subalgebra

/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Data.Fin.Tuple.Reflection

/-!

# Linearly disjoint of submodules

This file contains basics about the linearly disjoint of submodules.

## Mathematical background

We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
Let `R` be a commutative ring, `S` be an `R`-algebra (not necessarily commutative).
Let `M` and `N` be `R`-submodules in `S` (`Submodule R S`).

- `M` and `N` are linearly disjoint (`Submodule.LinearDisjoint M N` or simply
  `M.LinearDisjoint N`), if the natural `R`-linear map `M ⊗[R] N →ₗ[R] S`
  (`Submodule.mulMap M N`) induced by the multiplication in `S` is injective.

The following is the first equivalent characterization of linearly disjointness:

- `Submodule.LinearDisjoint.map_linearIndependent_left_of_flat`:
  if `M` and `N` are linearly disjoint, if `N` is a flat `R`-module, then for any family of
  `R`-linearly independent elements `{ m_i }` of `M`, they are also `N`-linearly independent,
  in the sense that the `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }`
  to the sum of `m_i * n_i` (`Submodule.LinearDisjoint.mulLeftMap N m`) is injective.

- `Submodule.LinearDisjoint.of_map_linearIndependent_left`:
  conversely, if `{ m_i }` is an `R`-basis of `M`, which is also `N`-linearly independent,
  then `M` and `N` are linearly disjoint.

Dually, we have:

- `Submodule.LinearDisjoint.map_linearIndependent_right_of_flat`:
  if `M` and `N` are linearly disjoint, if `M` is a flat `R`-module, then for any family of
  `R`-linearly independent elements `{ n_i }` of `N`, they are also `M`-linearly independent,
  in the sense that the `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }`
  to the sum of `m_i * n_i` (`Submodule.LinearDisjoint.mulRightMap M n`) is injective.

- `Submodule.LinearDisjoint.of_map_linearIndependent_right`:
  conversely, if `{ n_i }` is an `R`-basis of `N`, which is also `M`-linearly independent,
  then `M` and `N` are linearly disjoint.

The following is the second equivalent characterization of linearly disjointness:

- `Submodule.LinearDisjoint.map_linearIndependent_mul_of_flat`:
  if `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then for any family of
  `R`-linearly independent elements `{ m_i }` of `M`, and any family of
  `R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` in `S` is
  also `R`-linearly independent.

- `Submodule.LinearDisjoint.of_map_linearIndependent_mul`:
  conversely, if `{ m_i }` is an `R`-basis of `M`, if `{ n_i }` is an `R`-basis of `N`,
  such that the family `{ m_i * n_j }` in `S` is `R`-linearly independent,
  then `M` and `N` are linearly disjoint.

## Other main results

- `Submodule.LinearDisjoint.symm_of_commute`, `Submodule.linearDisjoint_symm_of_commute`:
  linearly disjoint is symmetric under some commutative conditions.

- `Submodule.linearDisjoint_op`:
  linearly disjoint is preserved by taking multiplicative opposite.

- `Submodule.LinearDisjoint.of_le_left_of_flat`, `Submodule.LinearDisjoint.of_le_right_of_flat`,
  `Submodule.LinearDisjoint.of_le_of_flat_left`, `Submodule.LinearDisjoint.of_le_of_flat_right`:
  linearly disjoint is preserved by taking submodules under some flatness conditions.

- `Submodule.LinearDisjoint.of_linearDisjoint_finite_left`,
  `Submodule.LinearDisjoint.of_linearDisjoint_finite_right`,
  `Submodule.LinearDisjoint.of_linearDisjoint_finite`:
  conversely, if any finitely generated submodules of `M` and `N` are linearly disjoint,
  then `M` and `N` themselves are linearly disjoint.

- `Submodule.LinearDisjoint.of_bot_left`, `Submodule.LinearDisjoint.of_bot_right`:
  the zero module is linearly disjoint with any other submodules.

- `Submodule.LinearDisjoint.of_one_left`, `Submodule.LinearDisjoint.of_one_right`:
  the image of `R` in `S` is linearly disjoint with any other submodules.

- `Submodule.LinearDisjoint.of_left_le_one_of_flat`,
  `Submodule.LinearDisjoint.of_right_le_one_of_flat`:
  if a submodule is contained in the image of `R` in `S`, then it is linearly disjoint with
  any other submodules, under some flatness conditions.

- `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat`,
  `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`:
  if `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then any two commutative
  elements contained in the intersection of `M` and `N` are not `R`-linearly independent (namely,
  their span is not `R ^ 2`). In particular, if any two elements in the intersection of `M` and `N`
  are commutative, then the rank of the intersection of `M` and `N` is at most one.

- `Submodule.LinearDisjoint.rank_le_one_of_commute_of_flat_of_self`:
  if `M` and itself are linearly disjoint, if `M` is flat, if any two elements in `M`
  are commutative, then the rank of `M` is at most one.

The results with name containing "of_commute" also have corresponding specified versions
assuming `S` is commutative.

## Tags

linearly disjoint, linearly independent, tensor product

-/

open scoped Classical TensorProduct

noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (M N : Submodule R S)

section mulMap

/-- If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S`. -/
def mulMap := LinearMap.mul' R S ∘ₗ TensorProduct.mapIncl M N

@[simp]
theorem mulMap_tmul (m : M) (n : N) : mulMap M N (m ⊗ₜ[R] n) = m.1 * n.1 := rfl

theorem mulMap_op :
    mulMap (equivOpposite.symm (MulOpposite.op M)) (equivOpposite.symm (MulOpposite.op N)) =
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ mulMap N M ∘ₗ
    (TensorProduct.congr
      (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm M)
      (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm N) ≪≫ₗ
    TensorProduct.comm R M N).toLinearMap :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem mulMap_comm_of_commute (hc : ∀ (m : M) (n : N), Commute m.1 n.1) :
    mulMap N M = mulMap M N ∘ₗ TensorProduct.comm R N M := by
  refine TensorProduct.ext' fun n m ↦ ?_
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, mulMap_tmul]
  exact (hc m n).symm

theorem mulMap_comp_rTensor (M' : Submodule R S) (hM : M' ≤ M) :
    mulMap M N ∘ₗ (inclusion hM).rTensor N = mulMap M' N :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem mulMap_comp_lTensor (N' : Submodule R S) (hN : N' ≤ N) :
    mulMap M N ∘ₗ (inclusion hN).lTensor M = mulMap M N' :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem mulMap_comp_map_inclusion (M' N' : Submodule R S) (hM : M' ≤ M) (hN : N' ≤ N) :
    mulMap M N ∘ₗ TensorProduct.map (inclusion hM) (inclusion hN) = mulMap M' N' :=
  TensorProduct.ext' fun _ _ ↦ rfl

/-- If `N` is a submodule in an algebra `S` over `R`, there is the natural map
`i(R) ⊗[R] N →ₗ[R] N` induced by multiplication in `S`, here `i : R → S` is the structure map. -/
def lTensorOne' : (1 : Submodule R S) ⊗[R] N →ₗ[R] N := by
  refine (mulMap (1 : Submodule R S) N).codRestrict N ?_
  intro c
  induction c using TensorProduct.induction_on with
  | zero => rw [_root_.map_zero]; exact N.zero_mem
  | tmul r n =>
    rw [mulMap_tmul]
    obtain ⟨_, y, rfl⟩ := r
    convert N.smul_mem y n.2 using 1
    simp [Algebra.smul_def]
  | add x y hx hy => rw [_root_.map_add]; exact N.add_mem hx hy

theorem lTensorOne'_apply
    (y : R) {hy : algebraMap R S y ∈ (1 : Submodule R S)}
    (n : N) : N.lTensorOne' (⟨algebraMap R S y, hy⟩ ⊗ₜ[R] n) = y • n :=
  Subtype.val_injective <| by simp [lTensorOne', Algebra.smul_def]

/-- If `N` is a submodule in an algebra `S` over `R`, there is the natural isomorphism between
`i(R) ⊗[R] N` and `N` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `TensorProduct.lid` as `i(R)` is not necessarily isomorphic to `R`. -/
def lTensorOne : (1 : Submodule R S) ⊗[R] N ≃ₗ[R] N := by
  refine LinearEquiv.ofLinear N.lTensorOne'
    (TensorProduct.mk R (1 : Submodule R S) N ⟨1, one_le.1 (le_refl _)⟩) ?_ ?_
  · ext; simp [lTensorOne']
  · ext r n
    obtain ⟨_, y, rfl⟩ := r
    simp only [Algebra.linearMap_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
      Function.comp_apply, lTensorOne'_apply, map_smul, TensorProduct.mk_apply,
      LinearMap.id_coe, id_eq]
    rw [← TensorProduct.tmul_smul, ← TensorProduct.smul_tmul]
    congr 1
    exact Subtype.val_injective <| by simp [Algebra.smul_def]

theorem lTensorOne_apply
    (y : R) {hy : algebraMap R S y ∈ (1 : Submodule R S)}
    (n : N) : N.lTensorOne (⟨algebraMap R S y, hy⟩ ⊗ₜ[R] n) = y • n :=
  N.lTensorOne'_apply y n

theorem lTensorOne_symm_apply (n : N) :
    N.lTensorOne.symm n = ⟨1, one_le.1 (le_refl _)⟩ ⊗ₜ[R] n := rfl

/-- If `M` is a submodule in an algebra `S` over `R`, there is the natural map
`M ⊗[R] i(R) →ₗ[R] M` induced by multiplication in `S`, here `i : R → S` is the structure map. -/
def rTensorOne' : M ⊗[R] (1 : Submodule R S) →ₗ[R] M := by
  refine (mulMap M (1 : Submodule R S)).codRestrict M ?_
  intro c
  induction c using TensorProduct.induction_on with
  | zero => rw [_root_.map_zero]; exact M.zero_mem
  | tmul m r =>
    rw [mulMap_tmul]
    obtain ⟨_, y, rfl⟩ := r
    convert M.smul_mem y m.2 using 1
    simp [Algebra.smul_def, Algebra.commutes y m.1]
  | add x y hx hy => rw [_root_.map_add]; exact M.add_mem hx hy

theorem rTensorOne'_apply
    (y : R) {hy : algebraMap R S y ∈ (1 : Submodule R S)}
    (m : M) : M.rTensorOne' (m ⊗ₜ[R] ⟨algebraMap R S y, hy⟩) = y • m :=
  Subtype.val_injective <| by simp [rTensorOne', Algebra.smul_def, Algebra.commutes y m.1]

/-- If `M` is a submodule in an algebra `S` over `R`, there is the natural isomorphism between
`M ⊗[R] i(R)` and `M` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `TensorProduct.rid` as `i(R)` is not necessarily isomorphic to `R`. -/
def rTensorOne : M ⊗[R] (1 : Submodule R S) ≃ₗ[R] M := by
  refine LinearEquiv.ofLinear M.rTensorOne'
    ((TensorProduct.comm R _ _).toLinearMap ∘ₗ TensorProduct.mk R
      (1 : Submodule R S) M ⟨1, one_le.1 (le_refl _)⟩) ?_ ?_
  · ext; simp [rTensorOne']
  · ext m r
    obtain ⟨_, y, rfl⟩ := r
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, Algebra.linearMap_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, rTensorOne'_apply, map_smul, TensorProduct.mk_apply,
      TensorProduct.comm_tmul, LinearMap.id_coe, id_eq]
    rw [← TensorProduct.tmul_smul]
    congr 1
    exact Subtype.val_injective <| by simp [Algebra.smul_def]

theorem rTensorOne_apply
    (y : R) {hy : algebraMap R S y ∈ (1 : Submodule R S)}
    (m : M) : M.rTensorOne (m ⊗ₜ[R] ⟨algebraMap R S y, hy⟩) = y • m :=
  M.rTensorOne'_apply y m

theorem rTensorOne_symm_apply (m : M) :
    M.rTensorOne.symm m = m ⊗ₜ[R] ⟨1, one_le.1 (le_refl _)⟩ := rfl

namespace LinearDisjoint

variable {M} in
/-- If `m : ι → M` is a family of elements, then there is an `R`-linear map from `ι →₀ N` to
`S` which maps `{ n_i }` to the sum of `m_i * n_i`. -/
def mulLeftMap {ι : Type*} (m : ι → M) : (ι →₀ N) →ₗ[R] S :=
  mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.total ι M R m) ∘ₗ
    (TensorProduct.finsuppScalarLeft R N ι).symm.toLinearMap

variable {M N} in
@[simp]
theorem mulLeftMap_apply_single {ι : Type*} (m : ι → M) (i : ι) (n : N) :
    mulLeftMap N m (Finsupp.single i n) = (m i).1 * n.1 := by
  simp [mulLeftMap, TensorProduct.finsuppScalarLeft_symm_apply_single]

variable {M} in
theorem mulLeftMap_def' {ι : Type*} (m : ι → M) : mulLeftMap N m =
    Finsupp.lsum ℕ fun (i : ι) ↦ (LinearMap.mulLeft R (m i).1).comp N.subtype := by
  ext; simp

variable {M N} in
theorem mulLeftMap_apply {ι : Type*} (m : ι → M) (n : ι →₀ N) :
    mulLeftMap N m n = Finsupp.sum n fun (i : ι) (n : N) ↦ (m i).1 * n.1 :=
  congr($(mulLeftMap_def' N m) n)

variable {N} in
/-- If `n : ι → N` is a family of elements, then there is an `R`-linear map from `ι →₀ M` to
`S` which maps `{ m_i }` to the sum of `m_i * n_i`. -/
def mulRightMap {ι : Type*} (n : ι → N) : (ι →₀ M) →ₗ[R] S :=
  mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.total ι N R n) ∘ₗ
    (TensorProduct.finsuppScalarRight R M ι).symm.toLinearMap

variable {M N} in
@[simp]
theorem mulRightMap_apply_single {ι : Type*} (n : ι → N) (i : ι) (m : M) :
    mulRightMap M n (Finsupp.single i m) = m.1 * (n i).1 := by
  simp [mulRightMap, TensorProduct.finsuppScalarRight_symm_apply_single]

variable {N} in
theorem mulRightMap_def' {ι : Type*} (n : ι → N) : mulRightMap M n =
    Finsupp.lsum ℕ fun (i : ι) ↦ LinearMap.smulRight M.subtype (n i).1 := by
  ext; simp

variable {M N} in
theorem mulRightMap_apply {ι : Type*} (n : ι → N) (m : ι →₀ M) :
    mulRightMap M n m = Finsupp.sum m fun (i : ι) (m : M) ↦ m.1 * (n i).1 :=
  congr($(mulRightMap_def' M n) m)

end LinearDisjoint

end mulMap

/-- Two submodules `M` and `N` in an algebra `S` over `R` are linearly disjoint if the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S` is injective. -/
protected def LinearDisjoint : Prop := Function.Injective (mulMap M N)

variable {M N}

theorem LinearDisjoint.injective (H : M.LinearDisjoint N) : Function.Injective (mulMap M N) := H

@[nontriviality]
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : M.LinearDisjoint N := by
  haveI : Subsingleton S := Module.subsingleton R S
  exact Function.injective_of_subsingleton _

/-- Linearly disjoint is preserved by taking multiplicative opposite. -/
theorem linearDisjoint_op :
    M.LinearDisjoint N ↔ (equivOpposite.symm (MulOpposite.op N)).LinearDisjoint
      (equivOpposite.symm (MulOpposite.op M)) := by
  simp only [Submodule.LinearDisjoint, mulMap_op, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]

alias ⟨LinearDisjoint.op, LinearDisjoint.of_op⟩ := linearDisjoint_op

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem LinearDisjoint.symm_of_commute (H : M.LinearDisjoint N)
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : N.LinearDisjoint M := by
  rw [Submodule.LinearDisjoint, mulMap_comm_of_commute M N hc]
  exact ((TensorProduct.comm R N M).toEquiv.injective_comp _).2 H

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem linearDisjoint_symm_of_commute
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

-- TODO: remove once #11731 is merged
lemma _root_.TensorProduct.coe_congr_right_refl {R : Type*} [CommSemiring R] {M N P : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] (f : M ≃ₗ[R] P) :
    (TensorProduct.congr f (LinearEquiv.refl R N)).toLinearMap = LinearMap.rTensor N f :=
  rfl

-- TODO: remove once #11731 is merged
lemma _root_.TensorProduct.coe_congr_left_refl {R : Type*} [CommSemiring R] {M N Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R Q] (g : N ≃ₗ[R] Q) :
    (TensorProduct.congr (LinearEquiv.refl R M) g).toLinearMap = LinearMap.lTensor M g :=
  rfl

namespace LinearDisjoint

variable (M N)

theorem of_map_linearIndependent_left' {ι : Type*} (m : Basis ι R M)
    (H : Function.Injective (mulLeftMap N m)) : M.LinearDisjoint N := by
  simp_rw [mulLeftMap, ← Basis.coe_repr_symm,
    ← TensorProduct.coe_congr_right_refl, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

theorem of_map_linearIndependent_right' {ι : Type*} (n : Basis ι R N)
    (H : Function.Injective (mulRightMap M n)) : M.LinearDisjoint N := by
  simp_rw [mulRightMap, ← Basis.coe_repr_symm,
    ← TensorProduct.coe_congr_left_refl, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

theorem of_map_linearIndependent_mul' {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : Function.Injective (Finsupp.total (κ × ι) S R fun i ↦ m i.1 * n i.2)) :
    M.LinearDisjoint N := by
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := TensorProduct.congr m.repr n.repr
  let i := mulMap M N ∘ₗ (i0.trans i1.symm).toLinearMap
  have : i = Finsupp.total (κ × ι) S R fun i ↦ m i.1 * n i.2 := by
    ext x
    simp [i, i0, i1, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  simp_rw [← this, i, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

theorem of_bot_left : (⊥ : Submodule R S).LinearDisjoint N := Function.injective_of_subsingleton _

theorem of_bot_right : M.LinearDisjoint (⊥ : Submodule R S) := Function.injective_of_subsingleton _

theorem of_one_left :
    (1 : Submodule R S).LinearDisjoint N := by
  have : N.subtype ∘ₗ N.lTensorOne.toLinearMap =
      mulMap (1 : Submodule R S) N := by
    change N.subtype ∘ₗ N.lTensorOne' = _
    simp [lTensorOne']
  have h : Function.Injective (N.subtype ∘ₗ N.lTensorOne.toLinearMap) :=
    N.injective_subtype.comp N.lTensorOne.injective
  rwa [this] at h

theorem of_one_right :
    M.LinearDisjoint (1 : Submodule R S) := by
  have : M.subtype ∘ₗ M.rTensorOne.toLinearMap =
      mulMap M (1 : Submodule R S) := by
    change M.subtype ∘ₗ M.rTensorOne' = _
    simp [rTensorOne']
  have h : Function.Injective (M.subtype ∘ₗ M.rTensorOne.toLinearMap) :=
    M.injective_subtype.comp M.rTensorOne.injective
  rwa [this] at h

variable {M N} in
/-- TODO: remove once #11859 is merged -/
private axiom test6 (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ (M' N' : Submodule R S) (hM : M' ≤ M) (hN : N' ≤ N),
    Module.Finite R M' ∧ Module.Finite R N' ∧
    s ⊆ LinearMap.range (TensorProduct.map (inclusion hM) (inclusion hN))

-- TODO: remove once #11859 is merged
variable {M N} in
private theorem test6L (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ (M' : Submodule R S) (hM : M' ≤ M), Module.Finite R M' ∧
    s ⊆ LinearMap.range ((inclusion hM).rTensor N) := by
  obtain ⟨M', _, hM, _, hfin, _, h⟩ := test6 s hs
  refine ⟨M', hM, hfin, ?_⟩
  rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

-- TODO: remove once #11859 is merged
variable {M N} in
private theorem test6R (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ (N' : Submodule R S) (hN : N' ≤ N), Module.Finite R N' ∧
    s ⊆ LinearMap.range ((inclusion hN).lTensor M) := by
  obtain ⟨_, N', _, hN, _, hfin, h⟩ := test6 s hs
  refine ⟨N', hN, hfin, ?_⟩
  rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

theorem of_linearDisjoint_finite_left
    (H : ∀ M' : Submodule R S, M' ≤ M → [Module.Finite R M'] → M'.LinearDisjoint N) :
    M.LinearDisjoint N := fun x y hxy ↦ by
  obtain ⟨M', hM, _, h⟩ := test6L {x, y} (Set.toFinite _)
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact H M' hM (by simp [← mulMap_comp_rTensor _ _ _ hM, hx', hy', hxy])

theorem of_linearDisjoint_finite_right
    (H : ∀ N' : Submodule R S, N' ≤ N → [Module.Finite R N'] → M.LinearDisjoint N') :
    M.LinearDisjoint N := fun x y hxy ↦ by
  obtain ⟨N', hN, _, h⟩ := test6R {x, y} (Set.toFinite _)
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact H N' hN (by simp [← mulMap_comp_lTensor _ _ _ hN, hx', hy', hxy])

theorem of_linearDisjoint_finite
    (H : ∀ (M' N' : Submodule R S), M' ≤ M → N' ≤ N →
      [Module.Finite R M'] → [Module.Finite R N'] → M'.LinearDisjoint N') :
    M.LinearDisjoint N :=
  of_linearDisjoint_finite_left _ _ fun _ hM _ ↦
    of_linearDisjoint_finite_right _ _ fun _ hN _ ↦ H _ _ hM hN

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (M N : Submodule R S)

theorem mulMap_comm : mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap :=
  mulMap_comm_of_commute M N fun _ _ ↦ mul_comm _ _

variable {M N}

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem LinearDisjoint.symm (H : M.LinearDisjoint N) : N.LinearDisjoint M :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem linearDisjoint_symm : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (M N : Submodule R S)

variable {M N} in
theorem map_linearIndependent_left_of_flat (H : M.LinearDisjoint N) [Module.Flat R N]
    {ι : Type*} {m : ι → M} (hm : LinearIndependent R m) : LinearMap.ker (mulLeftMap N m) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  let f := mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.total ι M R m)
  refine ((TensorProduct.finsuppScalarLeft R N ι).symm.toEquiv.injective_comp f).2 ?_
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm
  exact H.injective.comp (Module.Flat.rTensor_preserves_injective_linearMap (M := N) _ hm)

theorem of_map_linearIndependent_left {ι : Type*} (m : Basis ι R M)
    (H : LinearMap.ker (mulLeftMap N m) = ⊥) : M.LinearDisjoint N := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ N) := Finsupp.instAddCommGroup
  exact of_map_linearIndependent_left' M N m (LinearMap.ker_eq_bot.1 H)

variable {M N} in
theorem map_linearIndependent_right_of_flat (H : M.LinearDisjoint N) [Module.Flat R M]
    {ι : Type*} {n : ι → N} (hn : LinearIndependent R n) : LinearMap.ker (mulRightMap M n) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  let f := mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.total ι N R n)
  refine ((TensorProduct.finsuppScalarRight R M ι).symm.toEquiv.injective_comp f).2 ?_
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hn
  exact H.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap (M := M) _ hn)

theorem of_map_linearIndependent_right {ι : Type*} (n : Basis ι R N)
    (H : LinearMap.ker (mulRightMap M n) = ⊥) : M.LinearDisjoint N := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ M) := Finsupp.instAddCommGroup
  exact of_map_linearIndependent_right' M N n (LinearMap.ker_eq_bot.1 H)

variable {M N} in
theorem map_linearIndependent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R M]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.rTensor (ι →₀ R) (Finsupp.total κ M R m)
  let i2 := LinearMap.lTensor M (Finsupp.total ι N R n)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.rTensor_preserves_injective_linearMap _ hm
  have h2 : Function.Injective i2 := Module.Flat.lTensor_preserves_injective_linearMap _ hn
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.total (κ × ι) S R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp [i, i0, i1, i2, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rwa [this] at h

variable {M N} in
theorem map_linearIndependent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat R N]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.lTensor (κ →₀ R) (Finsupp.total ι N R n)
  let i2 := LinearMap.rTensor N (Finsupp.total κ M R m)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.lTensor_preserves_injective_linearMap _ hn
  have h2 : Function.Injective i2 := Module.Flat.rTensor_preserves_injective_linearMap _ hm
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.total (κ × ι) S R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp [i, i0, i1, i2, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rwa [this] at h

variable {M N} in
theorem map_linearIndependent_mul_of_flat (H : M.LinearDisjoint N)
    (hf : Module.Flat R M ∨ Module.Flat R N)
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rcases hf with _ | _
  · exact H.map_linearIndependent_mul_of_flat_left hm hn
  · exact H.map_linearIndependent_mul_of_flat_right hm hn

theorem of_map_linearIndependent_mul {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1) : M.LinearDisjoint N := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at H
  exact of_map_linearIndependent_mul' M N m n H

variable {M N} in
theorem of_le_left_of_flat (H : M.LinearDisjoint N) {M' : Submodule R S}
    (h : M' ≤ M) [Module.Flat R N] : M'.LinearDisjoint N := by
  let i := mulMap M N ∘ₗ (inclusion h).rTensor N
  have hi : Function.Injective i := H.injective.comp <|
    Module.Flat.rTensor_preserves_injective_linearMap _ <| inclusion_injective h
  have : i = mulMap M' N := by ext; simp [i]
  rwa [this] at hi

variable {M N} in
theorem of_le_right_of_flat (H : M.LinearDisjoint N) {N' : Submodule R S}
    (h : N' ≤ N) [Module.Flat R M] : M.LinearDisjoint N' := by
  let i := mulMap M N ∘ₗ (inclusion h).lTensor M
  have hi : Function.Injective i := H.injective.comp <|
    Module.Flat.lTensor_preserves_injective_linearMap _ <| inclusion_injective h
  have : i = mulMap M N' := by ext; simp [i]
  rwa [this] at hi

variable {M N} in
theorem of_le_of_flat_right (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' ≤ M) (hn : N' ≤ N) [Module.Flat R N] [Module.Flat R M'] :
    M'.LinearDisjoint N' := (H.of_le_left_of_flat hm).of_le_right_of_flat hn

variable {M N} in
theorem of_le_of_flat_left (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' ≤ M) (hn : N' ≤ N) [Module.Flat R M] [Module.Flat R N'] :
    M'.LinearDisjoint N' := (H.of_le_right_of_flat hn).of_le_left_of_flat hm

theorem of_left_le_one_of_flat (h : M ≤ 1) [Module.Flat R N] :
    M.LinearDisjoint N := (of_one_left N).of_le_left_of_flat h

theorem of_right_le_one_of_flat (h : N ≤ 1) [Module.Flat R M] :
    M.LinearDisjoint N := (of_one_right M).of_le_right_of_flat h

section not_linearIndependent_pair

variable {M N}

variable (H : M.LinearDisjoint N)

section

variable [Nontrivial R]

theorem not_linearIndependent_pair_of_commute_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h ↦ by
  let n : Fin 2 → N := (inclusion inf_le_right) ∘ ![a, b]
  have hn : LinearIndependent R n := h.map' _
    (LinearMap.ker_eq_bot_of_injective (inclusion_injective _))
  -- need this instance otherwise it only has semigroup structure
  letI : AddCommGroup (Fin 2 →₀ M) := Finsupp.instAddCommGroup
  let m : Fin 2 →₀ M := .single 0 ⟨b.1, b.2.1⟩ - .single 1 ⟨a.1, a.2.1⟩
  have hm : mulRightMap M n m = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker, H.map_linearIndependent_right_of_flat hn, mem_bot] at hm
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero,
    false_or, m] at hm
  exact h.ne_zero 0 hm.2

theorem not_linearIndependent_pair_of_commute_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h ↦ by
  let m : Fin 2 → M := (inclusion inf_le_left) ∘ ![a, b]
  have hm : LinearIndependent R m := h.map' _
    (LinearMap.ker_eq_bot_of_injective (inclusion_injective _))
  -- need this instance otherwise it only has semigroup structure
  letI : AddCommGroup (Fin 2 →₀ N) := Finsupp.instAddCommGroup
  let n : Fin 2 →₀ N := .single 0 ⟨b.1, b.2.2⟩ - .single 1 ⟨a.1, a.2.2⟩
  have hn : mulLeftMap N m n = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker, H.map_linearIndependent_left_of_flat hm, mem_bot] at hn
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero,
    false_or, n] at hn
  exact h.ne_zero 0 hn.2

theorem not_linearIndependent_pair_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := by
  rcases hf with _ | _
  · exact H.not_linearIndependent_pair_of_commute_of_flat_left a b hc
  · exact H.not_linearIndependent_pair_of_commute_of_flat_right a b hc

theorem not_linearIndependent_pair_of_commute_of_flat' (hf : Module.Flat R M ∨ Module.Flat R N)
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) (hc : Commute a b) :
    ¬LinearIndependent R ![a, b] := by
  have h := H.not_linearIndependent_pair_of_commute_of_flat hf ⟨a, ha⟩ ⟨b, hb⟩ hc
  contrapose! h
  refine .of_comp (M ⊓ N).subtype ?_
  convert h
  exact (FinVec.map_eq _ _).symm

theorem not_linearIndependent_pair_of_commute_of_flat_left' [Module.Flat R M]
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) (hc : Commute a b) :
    ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat' (Or.inl ‹_›) ha hb hc

theorem not_linearIndependent_pair_of_commute_of_flat_right' [Module.Flat R N]
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) (hc : Commute a b) :
    ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat' (Or.inr ‹_›) ha hb hc

end

theorem rank_inf_le_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 := by
  nontriviality R
  refine rank_le fun s h ↦ ?_
  by_contra hs
  rw [not_le, ← Fintype.card_coe, Fintype.one_lt_card_iff_nontrivial] at hs
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  refine H.not_linearIndependent_pair_of_commute_of_flat hf a.1 b.1 (hc a.1 b.1) ?_
  have := h.comp ![a, b] fun i j hij ↦ by
    fin_cases i <;> fin_cases j
    · rfl
    · simp [hab] at hij
    · simp [hab.symm] at hij
    · rfl
  convert this
  ext i
  fin_cases i <;> simp

theorem rank_inf_le_one_of_commute_of_flat_left [Module.Flat R M]
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inl ‹_›) hc

theorem rank_inf_le_one_of_commute_of_flat_right [Module.Flat R N]
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inr ‹_›) hc

theorem rank_le_one_of_commute_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M]
    (hc : ∀ (m n : M), Commute m.1 n.1) : Module.rank R M ≤ 1 := by
  rw [← inf_of_le_left (le_refl M)] at hc ⊢
  exact H.rank_inf_le_one_of_commute_of_flat_left hc

end not_linearIndependent_pair

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable (M N : Submodule R S)

section not_linearIndependent_pair

variable {M N}

variable (H : M.LinearDisjoint N)

section

variable [Nontrivial R]

theorem not_linearIndependent_pair_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_left a b (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_right a b (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat hf a b (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat' (hf : Module.Flat R M ∨ Module.Flat R N)
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat' hf ha hb (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat_left' [Module.Flat R M]
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_left' ha hb (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat_right' [Module.Flat R N]
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_right' ha hb (mul_comm _ _)

end

theorem rank_inf_le_one_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) :
    Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat hf fun _ _ ↦ mul_comm _ _

theorem rank_inf_le_one_of_flat_left [Module.Flat R M] : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat_left fun _ _ ↦ mul_comm _ _

theorem rank_inf_le_one_of_flat_right [Module.Flat R N] : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat_right fun _ _ ↦ mul_comm _ _

theorem rank_le_one_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M] :
    Module.rank R M ≤ 1 :=
  H.rank_le_one_of_commute_of_flat_of_self fun _ _ ↦ mul_comm _ _

end not_linearIndependent_pair

end LinearDisjoint

end CommRing

end Submodule

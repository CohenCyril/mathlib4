/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Restrict
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Topology.ContinuousFunction.UniqueCFC
import Mathlib.Analysis.NormedSpace.Star.Matrix
import Mathlib.Algebra.Star.StarAlgHom

/-
This file defines an instance of the continuous functional calculus for Hermitian matrices over an
RCLike field 𝕜.

## Tags

spectral theorem, diagonalization theorem, continuous functional calculus
-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

open scoped BigOperators
namespace IsHermitian
section DecidableEq

variable [DecidableEq n]

variable {A : Matrix n n 𝕜} (hA : IsHermitian A)

/-To do:

1) Somehow make this natural map defined in terms of the diagonal into a *-alg hom,
so I have to learn how to specify all of this data.

2) Use the resulting * algebra hom as the φ in the instance of the CFC.

-/

theorem eigenvalue_mem_toEuclideanLin_spectrum_RCLike (i : n) :
    (RCLike.ofReal ∘ hA.eigenvalues) i ∈ spectrum 𝕜 (toEuclideanLin A) :=
  LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _ |>.mem_spectrum

theorem range_thm_RCLike : Set.range
    (fun (i : n) ↦ (RCLike.ofReal ∘ hA.eigenvalues) i) ⊆ (spectrum 𝕜 (toEuclideanLin A)) := by
    rw [Set.range_subset_iff]
    apply eigenvalue_mem_toEuclideanLin_spectrum_RCLike

noncomputable def AlgEquivEuclideanLinearEuclideanCLM : AlgEquiv (R := 𝕜)
    (A := (EuclideanSpace 𝕜 n) →ₗ[𝕜] (EuclideanSpace 𝕜 n))
    (B := (EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)):=
    {LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl}

theorem spec_toEuclideanLin_eq_spec : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A
    := AlgEquiv.spectrum_eq ((AlgEquiv.trans ((toEuclideanCLM : Matrix n n 𝕜 ≃⋆ₐ[𝕜]
    EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) : Matrix n n 𝕜 ≃ₐ[𝕜]
    EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)) AlgEquivEuclideanLinearEuclideanCLM.symm) _

theorem eigenvalue_mem_real : ∀ (i : n), (hA.eigenvalues) i ∈ spectrum ℝ A := by
    intro i
    apply spectrum.of_algebraMap_mem (S := 𝕜) (R := ℝ) (A := Matrix n n 𝕜)
    rw [←spec_toEuclideanLin_eq_spec]
    apply hA.eigenvalue_mem_toEuclideanLin_spectrum_RCLike i

noncomputable def φ : StarAlgHom ℝ C(spectrum ℝ A, ℝ) (Matrix n n 𝕜) where
  toFun := fun g => (eigenvectorUnitary hA : Matrix n n 𝕜) *
      diagonal (RCLike.ofReal ∘ g ∘
      (fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalue_mem_real i⟩))
      * star (eigenvectorUnitary hA : Matrix n n 𝕜)
  map_one' := by
      dsimp
      have h1 : diagonal 1 = (1 : Matrix n n 𝕜) := rfl
      simp only  [h1, algebraMap.coe_one, Function.const_one, mul_one,
                 Matrix.mem_unitaryGroup_iff.mp, SetLike.coe_mem]
  map_mul' := by
      dsimp
      intro f g
      have H : diagonal ((RCLike.ofReal ∘ (⇑f * ⇑g) ∘
      (fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalue_mem_real i⟩))) = diagonal ((RCLike.ofReal ∘ ⇑f ∘
      (fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalue_mem_real i⟩))) * (1 : Matrix n n 𝕜)
      * diagonal (RCLike.ofReal ∘ ⇑g ∘ (fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalue_mem_real i⟩)) := by
            simp only [mul_one, Matrix.diagonal_mul_diagonal']
            refine diagonal_eq_diagonal_iff.mpr ?_
            intro i
            simp only [Function.comp_apply, Pi.mul_apply, RCLike.ofReal_mul]
      rw [H, ←(hA.eigenvectorUnitary).2.1]
      simp only [mul_assoc]
  map_zero' := by
      dsimp
      simp only [algebraMap.coe_zero, Function.const_zero, diagonal_zero]
      --have h : diagonal 0 = (0 : Matrix n n 𝕜) := by
      --    refine (Matrix.ext ?_).symm
      --    intro i j
      --    simp only [zero_apply, Matrix.diagonal]
      --    refine (ite_self 0).symm
#exit
  map_add' := by sorry
  commutes' := by sorry
  map_star' := fun
    | .mk toFun continuous_toFun => sorry

instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus 𝕜 (IsHermitian : Matrix n n 𝕜 → Prop) where
exists_cfc_of_predicate

sorry

--theorem spec_EuclideanCLM_eq_spec : spectrum 𝕜 (toEuclideanCLM (𝕜:= 𝕜) A) = spectrum 𝕜 A :=
--    AlgEquiv.spectrum_eq _ A

--theorem spec_EuclideanCLM_eq_spec_toEuclideanLin : spectrum 𝕜 (toEuclideanCLM (𝕜:= 𝕜) A)
--    = spectrum 𝕜 (toEuclideanLin A) := AlgEquiv.spectrum_eq (LinearAlgEquiv) _

--#check Matrix.coe_toEuclideanCLM_eq_toEuclideanLin
--the above might be useful when refactoring all of this

--noncomputable def f1 : n → spectrum ℝ A := by
--apply Set.codRestrict (fun (i : n) ↦ hA.eigenvalues i)
--apply eigenvalue_mem_real

--noncomputable def f2 : n → spectrum ℝ A := Set.codRestrict (fun (i : n) ↦ hA.eigenvalues i) (spectrum ℝ A) (hA.eigenvalue_mem_real)

--noncomputable def f : n → spectrum ℝ A := by
--apply Set.codRestrict fun (i : n) ↦ (RCLike.ofReal ∘ hA.eigenvalues) i
--have H := spec_toEuclideanLin_eq_spec (𝕜 := 𝕜) (n := n)
--      ▸ eigenvalue_mem_toEuclideanLin_spectrum_RCLike hA
--intro i
--apply spectrum.of_algebraMap_mem 𝕜
--refine H i

--noncomputable def φ₀ : C(spectrum ℝ A, ℝ) →  Matrix n n 𝕜 :=
--  fun g => (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ g ∘ f hA)
--      * star (eigenvectorUnitary hA : Matrix n n 𝕜)

--noncomputable def φ1 : C(spectrum ℝ A, ℝ) →  Matrix n n 𝕜 :=
--fun g => (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ g ∘ Set.codRestrict (fun (i : n) ↦ hA.eigenvalues i) (spectrum ℝ A) (hA.eigenvalue_mem_real))
--      * star (eigenvectorUnitary hA : Matrix n n 𝕜)
--

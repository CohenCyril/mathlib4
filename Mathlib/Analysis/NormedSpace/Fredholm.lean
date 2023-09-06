import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.Complex.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex

open Cardinal
open Function

namespace LinearMap

variable {K U V W : Type 0} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def isFiniteRank (A : V →ₗ[K] W) : Prop :=
  rank A < ℵ₀

lemma sumFiniteRank (A B : V →ₗ[K] W) (hA : isFiniteRank A) (hB : isFiniteRank B):
    isFiniteRank (A + B) := by
    dsimp only [isFiniteRank]
    calc
      rank (A + B) ≤ rank A + rank B := by apply rank_add_le
                 _ < ℵ₀              := by apply add_lt_aleph0 <;> assumption

lemma rightCompFiniteRank (A : V →ₗ[K] W) (B : U →ₗ[K] V) (hB : isFiniteRank B) :
    isFiniteRank (A ∘ₗ B) := by
  dsimp only [isFiniteRank]
  calc
    rank (A ∘ₗ B) ≤ rank B := by apply rank_comp_le_right
                _ < ℵ₀     := by assumption

lemma leftCompFiniteRank (A : V →ₗ[K] W) (B : U →ₗ[K] V) (hA : isFiniteRank A):
    isFiniteRank (A ∘ₗ B) := by
  dsimp only [isFiniteRank]
  calc
    rank (A ∘ₗ B) ≤ rank A := by apply rank_comp_le_left
                _ < ℵ₀     := by assumption

lemma smulFiniteRank (c : K) (A : V →ₗ[K] W) (hA : isFiniteRank A) : isFiniteRank (c • A) := by
  suffices : isFiniteRank ((c • id) ∘ₗ A)
  · exact this -- "suffices + exact" cannot be changed to "change" (?!)
  apply rightCompFiniteRank
  assumption

theorem zeroFiniteRank : isFiniteRank (0 : V →ₗ[K] W) := by
  dsimp only [isFiniteRank]
  rw [rank_zero]
  exact aleph0_pos

def eqUpToFiniteRank (A B : V →ₗ[K] W) : Prop := isFiniteRank (A - B)
infix:50 " =ᶠ " => eqUpToFiniteRank

@[refl]
theorem eqUpToFiniteRank_refl (A : V →ₗ[K] W) :  A =ᶠ A := by
  dsimp only [eqUpToFiniteRank]
  rw [sub_self]
  exact zeroFiniteRank

@[symm]
theorem eqUpToFiniteRank_symm (A B : V →ₗ[K] W) (h: A =ᶠ B): B =ᶠ A := by
  dsimp only [eqUpToFiniteRank]
  have : B - A = (-1 : K) • (A - B) := by simp only [neg_smul, one_smul, neg_sub]
  rw [this]
  apply smulFiniteRank
  assumption

@[trans]
theorem eqUpToFiniteRank_trans (A B C : V →ₗ[K] W) (hAB : A =ᶠ B) (hBC : B =ᶠ C) : A =ᶠ C := by
  dsimp only [eqUpToFiniteRank]
  rw [← sub_add_sub_cancel]
  apply sumFiniteRank (A - B) (B - C) hAB hBC

-- This is not be necessary. I just cannot structure proofs properly.
lemma eqUpToFiniteRank_lift_eq (A B : V →ₗ[K] W) (h : A = B) : A =ᶠ B := by rw [h]

def isQuasiInv (A : V →ₗ[K] W) (B : W →ₗ[K] V) : Prop :=
  1 =ᶠ B ∘ₗ A ∧ 1 =ᶠ A ∘ₗ B

end LinearMap

variable {E F G : Type _}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (T : E →L[ℂ] F) (S : F →L[ℂ] G)

open FiniteDimensional

def isFredholm (A : E →L[ℂ] F) : Prop :=
  ∃ (B : F →L[ℂ] E), LinearMap.isQuasiInv (A : E →ₗ[ℂ] F) B

namespace isFredholm

-- TODO What assumptions are really needed here?
lemma iff_finiteDimensional_ker_coker :
    isFredholm T ↔
    FiniteDimensional ℂ (LinearMap.ker T) ∧ FiniteDimensional ℂ (F ⧸ LinearMap.range T) := by
  sorry

lemma isFredholm_equiv (A : E ≃L[ℂ] F) : isFredholm (A : E →L[ℂ] F) := by
  use A.symm
  constructor <;> {
    apply LinearMap.eqUpToFiniteRank_lift_eq
    rw [←ContinuousLinearMap.coe_comp]
    first | rw [ContinuousLinearEquiv.coe_symm_comp_coe]
          | rw [ContinuousLinearEquiv.coe_comp_coe_symm]
    rw [LinearMap.one_eq_id, ContinuousLinearMap.coe_id]
  }

  protected def compOld (hT : isFredholm T) (hS : isFredholm S) : isFredholm (S.comp T) := by
  obtain ⟨T', hTl, hTr⟩ := hT
  obtain ⟨S', hSl, hSr⟩ := hS
  use (T' ∘L S')
  constructor
  · sorry
  · sorry

-- TODO maybe get rid of fixed u
universe u

-- The preimage of a finite rank module has finite rank, given that the map has finite rank kernel
lemma comap_fin_dim (A B : Type u)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (R : A →ₗ[ℂ] B) (B' : Submodule ℂ B)
    (hR : FiniteDimensional ℂ (LinearMap.ker R))
    (hB' : FiniteDimensional ℂ B')
    : FiniteDimensional ℂ (Submodule.comap R B') := by
  let A' := Submodule.comap R B'
  let hA' : ∀ x : A, x ∈ A' → R x ∈ B' := by
      intro x a
      simp_all only [Submodule.mem_comap]
  let R' := R.restrict hA'
  set rKer := Module.rank ℂ (LinearMap.ker R')
  have hKer : rKer ≤ Module.rank ℂ (LinearMap.ker R) := by
    sorry
  have hSurj : Surjective R' := by
    sorry
  have hRank : Module.rank ℂ A' = Module.rank ℂ B' + rKer := rank_eq_of_surjective R' hSurj
  suffices : Module.rank ℂ A' ≤ (Module.rank ℂ B') + (Module.rank ℂ (LinearMap.ker R))
  · sorry
  calc Module.rank ℂ A' = Module.rank ℂ B' + rKer := by rw [hRank]
    _ ≤ Module.rank ℂ B' + (Module.rank ℂ (LinearMap.ker R))
      := add_le_add_left hKer (Module.rank ℂ B')

lemma map_fin_codim (A B : Type u)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (R : A →ₗ[ℂ] B) (A' : Submodule ℂ A)
    (hR : FiniteDimensional ℂ (B ⧸ (LinearMap.range R)) )
    (hA' : FiniteDimensional ℂ (A ⧸ A'))
    : FiniteDimensional ℂ (B ⧸ (Submodule.map R A')) := by
  let B' := Submodule.map R A'
  let hA' : ∀ x : A, x ∈ A' → R x ∈ B' := by
      aesop
  let R' := R.restrict hA'
  have hRank : Module.rank ℂ (B ⧸ B') + Module.rank ℂ B' = Module.rank ℂ B :=
    rank_quotient_add_rank (Submodule.map R A')
  suffices : True
  · sorry
  sorry

-- Stability under composition; proof via the iff_finiteDimensional_ker_coker definition
protected lemma comp (hT : isFredholm T) (hS : isFredholm S)
    : isFredholm (S.comp T) := by
  rw [iff_finiteDimensional_ker_coker]
  rw [iff_finiteDimensional_ker_coker] at hT
  rw [iff_finiteDimensional_ker_coker] at hS
  constructor
  · change FiniteDimensional ℂ (LinearMap.ker ((S : F →ₗ[ℂ] G).comp (T : E →ₗ[ℂ] F) ))
    rw [LinearMap.ker_comp]
    apply comap_fin_dim
    · exact hT.1
    · exact hS.1
  · change FiniteDimensional ℂ (G ⧸ LinearMap.range ((S : F →ₗ[ℂ] G).comp (T : E →ₗ[ℂ] F) ))
    rw [LinearMap.range_comp]
    apply map_fin_codim
    · exact hS.2
    · exact hT.2



noncomputable def index : ℤ :=
  (finrank ℂ (LinearMap.ker T) : ℤ) - (finrank ℂ (F ⧸ LinearMap.range T) : ℤ)

lemma index_comp (hT : isFredholm T) (hS : isFredholm S) :
    index (S.comp T) = index T + index S := by
  sorry

end isFredholm

variable (E)

def Fredholm : Submonoid (E →L[ℂ] E) :=
  { carrier := isFredholm,
    one_mem' := sorry,
    mul_mem' := sorry, }

instance : ContinuousMul (E →L[ℂ] E) := by
  constructor
  sorry

instance : ContinuousMul (Fredholm E) := ⟨by continuity⟩

/- TODO (not sure if how easy these are)
  * Index additive on direct sums
  * Relationship to compact operators
-/

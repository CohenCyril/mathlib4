import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.Algebra.Module.Zlattice.Covolume

open Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

namespace NumberField.mixedEmbedding.euclideanSpace

open NumberField NumberField.InfinitePlace MeasureTheory BigOperators Submodule

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E₂" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

/-- Docs. -/
local instance : Ring (EuclideanSpace ℝ { w : InfinitePlace K // IsReal w }) := Pi.ring

/-- Docs. -/
local instance : Ring (EuclideanSpace ℂ { w : InfinitePlace K // IsComplex w }) := Pi.ring

instance : Ring (E₂ K) := Prod.instRing

instance : MeasurableSpace (E₂ K) := borel _

instance : BorelSpace (E₂ K)  :=  ⟨rfl⟩

instance : T2Space (E₂ K) := Prod.t2Space

-- protected theorem norm_apply (x : E₂ K) :
--     ‖x‖ = Real.sqrt (∑ w, ‖x.1 w‖ ^ 2 + ∑ w, ‖x.2 w‖ ^ 2) := by
--   rw [WithLp.prod_norm_eq_add (by exact Nat.ofNat_pos), EuclideanSpace.norm_eq,
--     EuclideanSpace.norm_eq, ENNReal.toReal_ofNat, Real.rpow_two, Real.sq_sqrt (by positivity),
--     Real.rpow_two, Real.sq_sqrt (by positivity), Real.sqrt_eq_rpow]

-- protected theorem inner_apply (x y : E₂ K) :
--     ⟪x, y⟫_ℝ = ∑ w, (x.1 w) * (y.1 w) +
--       ∑ w, ((x.2 w).re * (y.2 w).re + (x.2 w).im * (y.2 w).im) := by
--   simp_rw [WithLp.prod_inner_apply, EuclideanSpace.inner_eq_star_dotProduct, real_inner_eq_re_inner,
--     EuclideanSpace.inner_eq_star_dotProduct, Matrix.dotProduct, Pi.star_apply, star_trivial,
--     RCLike.star_def, map_sum, RCLike.mul_re, RCLike.conj_re, RCLike.re_to_complex,
--     RCLike.conj_im, WithLp.equiv_pi_apply, neg_mul, sub_neg_eq_add, RCLike.im_to_complex]

/-- Docs. -/
protected def equiv : (E₂ K) ≃ (E K) := WithLp.equiv _ _

instance : Nontrivial (E₂ K) := (euclideanSpace.equiv K).nontrivial

/-- Docs. -/
protected def linearEquiv : (E₂ K) ≃ₗ[ℝ] (E K) := WithLp.linearEquiv _ _ _

/-- Docs. -/
protected def addEquiv : (E₂ K) ≃+ (E K) := (euclideanSpace.linearEquiv K).toAddEquiv

/-- Docs. -/
protected def stdOrthonormalBasis : OrthonormalBasis (index K) ℝ (E₂ K) := sorry

theorem stdOrthonormalBasis_equiv :
    (euclideanSpace.stdOrthonormalBasis K).toBasis.map (euclideanSpace.linearEquiv K) =
      mixedEmbedding.stdBasis K := sorry

theorem measurePreserving_euclideanEquiv : MeasurePreserving (euclideanSpace.equiv K) := by
  let e := (euclideanSpace.linearEquiv K).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  convert e.measurable.measurePreserving volume
  rw [← (OrthonormalBasis.addHaar_eq_volume (euclideanSpace.stdOrthonormalBasis K)),
    Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    Basis.map_addHaar, LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, stdOrthonormalBasis_equiv,
    eq_comm, Basis.addHaar_eq_iff, Basis.coe_parallelepiped, ← measure_congr
    (Zspan.fundamentalDomain_ae_parallelepiped (stdBasis K) volume),
    volume_fundamentalDomain_stdBasis K]

end NumberField.mixedEmbedding.euclideanSpace

open Filter NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Topology MeasureTheory
  NumberField.Units NumberField.mixedEmbedding.fundamentalCone Submodule Bornology
  NumberField.mixedEmbedding.euclideanSpace

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E₂" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

/-- Docs. -/
def Λ : AddSubgroup (E₂ K) :=
    (span ℤ (Set.range ((latticeBasis K).map (euclideanSpace.linearEquiv K).symm))).toAddSubgroup

instance : DiscreteTopology (Λ K) := Zspan.instDiscreteTopology _

instance : IsZlattice ℝ (Λ K) where
  span_top := by
    unfold Λ
    simp_rw [coe_toAddSubgroup, ← Zspan.map, map_coe, LinearEquiv.restrictScalars_apply,
      ← Submodule.map_span, Zspan.span_top, Submodule.map_top, LinearEquivClass.range]

/-- Docs. -/
abbrev X : Set (E₂ K) := (euclideanSpace.equiv K)⁻¹' (fundamentalCone K)

/-- Docs. -/
abbrev X₁ : Set (E₂ K) := {x ∈ X K | mixedEmbedding.norm (euclideanSpace.equiv K x) ≤ 1}

/-- Docs. -/
abbrev F₁ : Set (E₂ K) := {x ∈ X K | mixedEmbedding.norm (euclideanSpace.equiv K x) = 1}

theorem aux00 {x : E₂ K} (hx : x ∈ X₁ K) (hx' : x ≠ 0) :
    mixedEmbedding.norm (euclideanSpace.equiv K x) ≠ 0 := by
  obtain ⟨h, _⟩ := hx
  rw [X, fundamentalCone, Set.mem_preimage] at h
  have := h.resolve_right ?_
  exact this.2
  

theorem aux0 {x : E₂ K} (hx : x ∈ X₁ K) (hx' : x ≠ 0) :
    ∃ c : ℝ, 1 ≤ c ∧ c • x ∈ F₁ K := by
  refine ⟨(mixedEmbedding.norm (euclideanSpace.equiv K x))⁻¹, ?_, ?_⟩
  · refine one_le_inv_iff.mpr ⟨?_, ?_⟩
    · obtain ⟨hx₁, _⟩ := hx
      refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
      · exact mixedEmbedding.norm_nonneg _
      · exact Ne.symm hx₂

      sorry
    ·
      sorry
  ·
    sorry

theorem aux1 (h : IsBounded (F₁ K)) :
    IsBounded (X₁ K) := by
  rw [Metric.isBounded_iff_subset_ball 0]
  obtain ⟨r, hr₁, hr₂⟩ := h.subset_ball_lt 0 0
  refine ⟨r, ?_⟩
  rintro x hx
  by_cases hx' : x = 0
  · rw [hx']
    exact Metric.mem_ball_self hr₁
  · obtain ⟨c, hc₁, hc₂⟩ := aux0 K hx hx'
    have := hr₂ hc₂
    rw [mem_ball_zero_iff] at this ⊢
    rw [norm_smul, ← lt_div_iff'] at this
    refine lt_of_lt_of_le this ?_
    refine div_le_self ?_ ?_
    exact le_of_lt hr₁
    rw [Real.norm_eq_abs]
    exact le_trans hc₁ (le_abs_self _)
    rw [norm_pos_iff]
    refine ne_of_gt ?_
    exact lt_of_lt_of_le zero_lt_one hc₁


example :
    Tendsto (fun n : ℝ ↦
      Nat.card {I : Ideal (𝓞 K) // Submodule.IsPrincipal I ∧ Ideal.absNorm I = n} *
        torsionOrder K / n) atTop
          (𝓝 ((volume (X₁ K)).toReal / Zlattice.covolume (Λ K))) := by
  refine Tendsto.congr' ?_
    (Zlattice.covolume.tendsto_card_le_div' (Λ K) ?_ ?_ ?_ ?_)
  ·
    sorry
  · intro x r hx hr
    erw [Set.mem_preimage, _root_.map_smul (euclideanSpace.linearEquiv K)]
    refine smul_mem_of_mem ?_ r
    exact hx
  · intro x r hr
    rw [mixedEmbedding.norm_smul, abs_eq_self.mpr hr]
    erw [mixedEmbedding.finrank]
  · -- Not trivial at all
    sorry
  ·
    sorry

#lint

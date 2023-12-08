/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Integral curves of vector fields on a manifold

Let `M` be a manifold and `v : (x : M) → TangentSpace I x` be a vector field on `M`. An integral
curve of `v` is a function `γ : ℝ → M` such that the derivative of `γ` at `t` equals `v (γ t)`. The
integral curve may only be defined for all `t` within some subset of `ℝ`.

Assume `v` is continuously differentiable. The existence theorem for solutions to ODEs implies that
a unique local integral curve exists for any continuously differentiable vector field `v`. The
uniqueness theorem for solutions to ODEs implies that integral curves of `v` are unique. These are
the main results of this file.

## Main definition

Let `v : M → TM` be a vector field on `M`, and let `γ : ℝ → M`.
- **`IsIntegralCurve γ v`**: `γ t` is tangent to `v (γ t)` for all `t : ℝ`. That is, `γ` is a global
integral curve of `v`.
- **`IsIntegralCurveOn γ v s`**: `γ t` is tangent to `v (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
- **`IsIntegralCurveAt γ v t₀`**: `γ t` is tangent to `v (γ t)` for all `t` in some open interval
around `t₀`. That is, `γ` is a local integral curve of `v`.

For `IsIntegralCurveOn γ v s` and `IsIntegralCurveAt γ v t₀`, even though `γ` is defined for all
time, its value outside of the set `s` or a small interval around `t₀` is irrelevant and considered
junk.

## Implementation notes

For the existence and uniqueness theorems, we assume that the image of the integral curve lies in
the interior of the manifold. The case where the integral curve may lie on the boundary of the
manifold requires special treatment, and we leave it as a to-do.

The uniqueness theorem requires the manifold to be Hausdorff (T2), so that the set on which two
continuous functions agree is closed.

We state simpler versions of the theorem for manifolds without boundary as corollaries.

## To-do

- The case where the integral curve may venture to the boundary of the manifold. See Theorem 9.34,
  J. M. Lee. May require submanifolds.

## Tags

integral curve, vector field, local existence, uniqueness
-/

open scoped Manifold
scoped[Manifold] notation "𝓔(" I ", " x ")" => extChartAt I x
scoped[Manifold] notation "𝓔⁻¹(" I ", " x ")" => LocalEquiv.symm (𝓔(I, x))

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']
  {v : (x : M) → TangentSpace I x} {x₀ : M}
  (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀)
  {s : Set ℝ} {t₀ : ℝ}


/-- If `γ : ℝ → M`, `v : M → TM` is a vector field on `M`, and `s ∈ Set ℝ`,
  `IsIntegralCurveOn γ v s` means `γ t` is tangent to `v (γ t)` for all `t ∈ s`. The value of `γ`
  outside of `s` is irrelevant and considered junk.  -/
def IsIntegralCurveOn (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (s : Set ℝ) :=
  ∀ (t : ℝ), t ∈ s → HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

/-- If `v : M → TM` is a vector field on `M`, and `t₀ : ℝ`, `IsIntegralCurveAt γ v t₀` means
  `γ : ℝ → M` is a local integral curve of `v` in an open interval of `t₀`. That is, there exists
  `ε > 0` such that `γ t` is tangent to `v (γ t)` for all `t ∈ Ioo (t₀ - ε) (t₀ + ε)`. The value of
  `γ` outside of this interval is irrelevant and considered junk. -/
def IsIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t : ℝ) :=
  ∃ ε > (0 : ℝ), IsIntegralCurveOn γ v (Ioo (t - ε) (t + ε))

/-- If `v : M → TM` is a vector field on `M`, `IsIntegralCurve γ v` means `γ : ℝ → M` is a global
  integral curve of `v`. That is, `γ t` is tangent to `v (γ t)` for all `t : ℝ`. -/
def IsIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x) :=
  ∀ t : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

lemma IsIntegralCurve.isIntegralCurveOn {γ : ℝ → M} {v : (x : M) → TangentSpace I x}
    (h : IsIntegralCurve γ v) (s : Set ℝ) : IsIntegralCurveOn γ v s := fun t _ => h t

lemma isIntegralCurve_iff_isIntegralCurveOn {γ : ℝ → M} {v : (x : M) → TangentSpace I x} :
    IsIntegralCurve γ v ↔ IsIntegralCurveOn γ v univ :=
  ⟨fun h => h.isIntegralCurveOn _, fun h t => h t (mem_univ _)⟩

lemma IsIntegralCurve.isIntegralCurveAt {γ : ℝ → M} {v : (x : M) → TangentSpace I x}
    (h : IsIntegralCurve γ v) (t : ℝ) : IsIntegralCurveAt γ v t :=
  ⟨1, zero_lt_one, fun t _ => h t⟩

lemma isIntegralCurve_iff_isIntegralCurveAt {γ : ℝ → M} {v : (x : M) → TangentSpace I x} :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h => h.isIntegralCurveAt, fun h t => by
    obtain ⟨ε, hε, h⟩ := h t
    exact h t (Real.ball_eq_Ioo _ _ ▸ Metric.mem_ball_self hε)⟩

lemma IsIntegralCurveOn.mono {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (h : IsIntegralCurveOn γ v s) {s' : Set ℝ} (hs : s' ⊆ s) : IsIntegralCurveOn γ v s' :=
  fun t ht => h t (mem_of_mem_of_subset ht hs)

lemma IsIntegralCurveOn.isIntegralCurveAt {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (h : IsIntegralCurveOn γ v s) {t : ℝ} (hs : s ∈ nhds t) : IsIntegralCurveAt γ v t := by
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hmem⟩ := hs
  exact ⟨ε, hε, Real.ball_eq_Ioo _ _ ▸ h.mono hmem⟩

lemma IsIntegralCurveAt.isIntegralCurveOn {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) : IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨ε, hε, h⟩ := h t ht
  exact h t (Real.ball_eq_Ioo _ _ ▸ Metric.mem_ball_self hε)

/-! ### Translation lemmas -/

lemma IsIntegralCurveOn.comp_add {γ : ℝ → M} (hγ : IsIntegralCurveOn γ v s) (dt : ℝ) :
    IsIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } := by
  intros t ht
  rw [Function.comp_apply,
    ← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivAt.comp t (hγ (t + dt) ht)
  refine ⟨(continuous_add_right _).continuousAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  exact HasFDerivAt.add_const (hasFDerivAt_id _) _

lemma isIntegralCurveOn_comp_add {γ : ℝ → M} {dt : ℝ} : IsIntegralCurveOn γ v s ↔
    IsIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } := by
  refine ⟨fun hγ => hγ.comp_add _, fun hγ => ?_⟩
  have := hγ.comp_add (-dt)
  simp only [mem_setOf_eq, neg_add_cancel_right, setOf_mem_eq] at this
  convert this
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]

lemma IsIntegralCurveAt.comp_add {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert h.comp_add dt
  ext t'
  rw [sub_right_comm, sub_add_eq_add_sub, ← add_mem_Ioo_iff_left]
  rfl

lemma isIntegralCurveAt_comp_add {γ : ℝ → M} {dt : ℝ} : IsIntegralCurveAt γ v t₀ ↔
    IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  refine ⟨fun hγ => hγ.comp_add _, fun hγ ↦ ?_⟩
  have := hγ.comp_add (-dt)
  rw [sub_neg_eq_add, sub_add_cancel] at this
  convert this
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]

lemma IsIntegralCurve.comp_add {γ : ℝ → M} (hγ : IsIntegralCurve γ v) (dt : ℝ) :
    IsIntegralCurve (γ ∘ (· + dt)) v := by
  rw [isIntegralCurve_iff_isIntegralCurveOn] at *
  exact hγ.comp_add _

lemma isIntegralCurve_comp_add {γ : ℝ → M} {dt : ℝ} : IsIntegralCurve γ v ↔
    IsIntegralCurve (γ ∘ (· + dt)) v := by
  refine ⟨fun hγ => hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]

/-! ### Scale lemmas -/

lemma IsIntegralCurveOn.comp_mul {γ : ℝ → M} (hγ : IsIntegralCurveOn γ v s) (a : ℝ) :
    IsIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  intros t ht
  rw [Function.comp_apply, Pi.smul_apply, ← ContinuousLinearMap.smulRight_comp]
  refine HasMFDerivAt.comp t (hγ (t * a) ht) ⟨(continuous_mul_right _).continuousAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  exact HasFDerivAt.mul_const' (hasFDerivAt_id _) _

lemma isIntegralCurvOn_comp_mul_ne_zero {γ : ℝ → M} {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  refine ⟨fun hγ => hγ.comp_mul a, fun hγ ↦ ?_⟩
  have := hγ.comp_mul a⁻¹
  simp_rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul, mem_setOf_eq, mul_assoc,
    inv_mul_eq_div, div_self ha, mul_one, setOf_mem_eq] at this
  convert this
  ext t
  rw [Function.comp_apply, Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]

lemma IsIntegralCurveAt.comp_mul_ne_zero {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀) {a : ℝ}
    (ha : a ≠ 0) : IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, div_pos hε (abs_pos.mpr ha), ?_⟩
  convert h.comp_mul a
  ext t
  rw [Ioo, Ioo, mem_setOf_eq, mem_setOf_eq, mem_setOf_eq]
  by_cases ha' : 0 < a
  · rw [abs_eq_self.mpr (le_of_lt ha'), ← sub_div, ← add_div, div_lt_iff ha', lt_div_iff ha']
  · rw [abs_eq_neg_self.mpr (not_lt.mp ha'), div_neg, sub_neg_eq_add, ← sub_eq_add_neg, ← sub_div,
    ← add_div, div_lt_iff_of_neg (ha.lt_of_le (not_lt.mp ha')),
    lt_div_iff_of_neg (ha.lt_of_le (not_lt.mp ha')), and_comm]

lemma isIntegralCurveAt_comp_mul_ne_zero {γ : ℝ → M} {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  refine ⟨fun hγ => hγ.comp_mul_ne_zero ha, fun hγ ↦ ?_⟩
  have := hγ.comp_mul_ne_zero (inv_ne_zero ha)
  rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul, ← div_mul_eq_div_div_swap,
    inv_mul_eq_div, div_self ha, div_one, Function.comp.assoc] at this
  convert this
  ext t
  simp [inv_mul_eq_div, div_self ha]

lemma IsIntegralCurve.comp_mul {γ : ℝ → M} (hγ : IsIntegralCurve γ v) (a : ℝ) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [isIntegralCurve_iff_isIntegralCurveOn] at *
  exact hγ.comp_mul _

lemma isIntegralCurve_comp_mul_ne_zero {γ : ℝ → M} {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· * a)) (a • v) := by
  refine ⟨fun hγ => hγ.comp_mul _, fun hγ => ?_⟩
  have := hγ.comp_mul a⁻¹
  rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul] at this
  convert this
  ext t
  rw [Function.comp_apply, Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]

/-- If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
  is a global integral curve of `v`. -/
lemma isIntegralCurve_const (h : v x₀ = 0) : IsIntegralCurve (fun _ => x₀) v := by
  intro t
  rw [h, ← ContinuousLinearMap.zero_apply (R₁ := ℝ) (R₂ := ℝ) (1 : ℝ),
    ContinuousLinearMap.smulRight_one_one]
  exact hasMFDerivAt_const ..

lemma IsIntegralCurveOn.continuousAt {γ : ℝ → M} (hγ : IsIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousAt γ t₀ := (hγ t₀ ht).1

lemma IsIntegralCurveOn.continuousOn {γ : ℝ → M} (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := fun t ht => (hγ t ht).1.continuousWithinAt

lemma IsIntegralCurveAt.continuousAt {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ := by
  obtain ⟨ε, hε, hγ⟩ := hγ
  apply hγ.continuousAt
  rw [← Real.ball_eq_Ioo]
  exact Metric.mem_ball_self hε

lemma IsIntegralCurve.continuous {γ : ℝ → M} (hγ : IsIntegralCurve γ v) :
    Continuous γ := continuous_iff_continuousAt.mpr
      fun _ => (hγ.isIntegralCurveOn univ).continuousAt (mem_univ _)

variable (t₀)

/-- For any continuously differentiable vector field and any chosen non-boundary point `x₀` on the
  manifold, there exists an integral curve `γ : ℝ → M` such that `γ t₀ = x₀` and the tangent vector
  of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open interval around
  `t₀`.-/
theorem exists_isIntegralCurveAt_of_contMDiffAt (hx : I.IsInteriorPoint x₀) :
    ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ := by
  -- express the differentiability of the section `v` in the local charts
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  obtain ⟨f, hf1, ε1, hε1, hf2⟩ :=
    exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt t₀
      (hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)).snd
  rw [← Real.ball_eq_Ioo] at hf2
  -- use continuity of `f` to extract `ε2` so that for `t ∈ Real.ball t₀ ε2`,
  -- `f t ∈ interior (extChartAt I x₀).target`
  have hcont := (hf2 t₀ (Metric.mem_ball_self hε1)).continuousAt
  rw [continuousAt_def, hf1] at hcont
  have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ nhds t₀ :=
    hcont _ (isOpen_interior.mem_nhds (ModelWithCorners.isInteriorPoint_iff.mp hx))
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨ε2, hε2, hf3⟩ := hnhds
  simp_rw [subset_def, mem_preimage] at hf3
  -- prove that `γ := (extChartAt I x₀).symm ∘ f` is a desired integral curve
  refine ⟨(extChartAt I x₀).symm ∘ f,
    Eq.symm (by rw [Function.comp_apply, hf1, LocalEquiv.left_inv _ (mem_extChartAt_source ..)]),
    min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intros t ht
  -- collect useful terms in convenient forms
  rw [← Real.ball_eq_Ioo] at ht
  have hf3 := hf3 t <| mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_right ..))
  have h : HasDerivAt f
    ((fderivWithin ℝ ((extChartAt I x₀) ∘ (extChartAt I ((extChartAt I x₀).symm (f t))).symm)
        (range I) (extChartAt I ((extChartAt I x₀).symm (f t)) ((extChartAt I x₀).symm (f t))))
      (v ((extChartAt I x₀).symm (f t))))
    t := hf2 t <| mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_left ..))
  rw [← tangentCoordChange_def] at h
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source I ((extChartAt I x₀).symm (f t))
  -- express the derivative of the integral curve in the local chart
  refine ⟨ContinuousAt.comp (continuousAt_extChartAt_symm'' _ _ hf3') (h.continuousAt),
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  show HasDerivAt (((extChartAt I ((extChartAt I x₀).symm (f t))) ∘ (extChartAt I x₀).symm) ∘ f)
    (v ((extChartAt I x₀).symm (f t))) t
  -- express `v (γ t)` as `D⁻¹ D (v (γ t))`, where `D` is a change of coordinates, so we can use
  -- `HasFDerivAt.comp_hasDerivAt` on `h`
  rw [← tangentCoordChange_self (I := I) (x := (extChartAt I x₀).symm (f t))
      (z := (extChartAt I x₀).symm (f t)) (v := v ((extChartAt I x₀).symm (f t))) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  nth_rw 4 [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- For any continuously differentiable vector field defined on a manifold without boundary and any
  chosen starting point `x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the
  tangent vector of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open
  interval around `t₀`. -/
lemma exists_isIntegralCurveAt_of_contMDiffAt_boundaryless [I.Boundaryless] :
    ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ :=
  exists_isIntegralCurveAt_of_contMDiffAt hv t₀ I.isInteriorPoint

variable (I)

/-- Local integral curves are unique.

  If a continuously differentiable vector field `v` admits two local integral curves `γ γ' : ℝ → M`
  at `t₀` with `γ t₀ = γ' t₀`, then `γ` and `γ'` agree on some open interval around `t₀` -/
theorem isIntegralCurveAt_eqOn_of_contMDiffAt {γ γ' : ℝ → M} (ht : I.IsInteriorPoint (γ t₀))
    (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsIntegralCurveAt γ v t₀) (hγ' : IsIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    ∃ ε > 0, EqOn γ γ' (Ioo (t₀ - ε) (t₀ + ε)) := by
  -- extract set `s` on which `v` is Lipschitz
  set v' : E → E := fun x =>
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  obtain ⟨K, s, hs, hlip⟩ : ∃ K, ∃ s ∈ nhds _, LipschitzOnWith K v' s :=
    ContDiffAt.exists_lipschitzOnWith (hv.contDiffAt (range_mem_nhds_isInteriorPoint ht)).snd
  have hlip : ∀ t : ℝ, LipschitzOnWith K ((fun _ => v') t) ((fun _ => s) t) := fun _ => hlip
  -- extract `εs` so that `(extChartAt I (γ t₀)) (γ t) ∈ s` for all `t ∈ Ioo (t₀ - εs) (t₀ + εs)`
  have hcont : ContinuousAt ((extChartAt I (γ t₀)) ∘ γ) t₀ :=
    ContinuousAt.comp (continuousAt_extChartAt ..) hγ.continuousAt
  rw [continuousAt_def] at hcont
  have hnhds := hcont _ hs
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨εs, hεs, hmem⟩ := hnhds
  simp_rw [subset_def, mem_preimage] at hmem
  -- `εs'` for `γ'`
  have hcont' : ContinuousAt ((extChartAt I (γ' t₀)) ∘ γ') t₀ :=
    ContinuousAt.comp (continuousAt_extChartAt ..) hγ'.continuousAt
  rw [continuousAt_def] at hcont'
  have hnhds' := hcont' _ (h ▸ hs)
  rw [Metric.mem_nhds_iff] at hnhds'
  obtain ⟨εs', hεs', hmem'⟩ := hnhds'
  simp_rw [subset_def, mem_preimage] at hmem'
  -- extract `εe` so `γ t` stays within the interior of the chart around `γ t₀`
  have := continuousAt_def.mp hγ.continuousAt _ <| extChartAt_source_mem_nhds I (γ t₀)
  rw [Metric.mem_nhds_iff] at this
  obtain ⟨εe, hεe, hsrc⟩ := this
  simp_rw [subset_def, mem_preimage] at hsrc
  have := continuousAt_def.mp hγ'.continuousAt _ <| extChartAt_source_mem_nhds I (γ' t₀)
  rw [Metric.mem_nhds_iff] at this
  obtain ⟨εe', hεe', hsrc'⟩ := this
  simp_rw [subset_def, mem_preimage] at hsrc'
  -- extract `εγ` from local existence of integral curve
  obtain ⟨εγ, hεγ, hγ⟩ := hγ
  obtain ⟨εγ', hεγ', hγ'⟩ := hγ'
  let ε := min (min εe εe') <| min (min εs εs') (min εγ εγ')
  have hf : ContinuousOn ((extChartAt I (γ t₀)) ∘ γ) (Ioo (t₀ - ε) (t₀ + ε)) := by
    apply ContinuousOn.comp (continuousOn_extChartAt I (γ t₀))
    · apply hγ.continuousOn.mono
      rw [← Real.ball_eq_Ioo, ← Real.ball_eq_Ioo]
      apply Metric.ball_subset_ball
      simp
    · apply MapsTo.mono_left hsrc
      rw [← Real.ball_eq_Ioo]
      apply Metric.ball_subset_ball
      simp
  have hf' : ContinuousOn ((extChartAt I (γ' t₀)) ∘ γ') (Ioo (t₀ - ε) (t₀ + ε)) := by
    apply ContinuousOn.comp (continuousOn_extChartAt I (γ' t₀))
    · apply hγ'.continuousOn.mono
      rw [← Real.ball_eq_Ioo, ← Real.ball_eq_Ioo]
      apply Metric.ball_subset_ball
      simp
    · apply MapsTo.mono_left hsrc'
      rw [← Real.ball_eq_Ioo]
      apply Metric.ball_subset_ball
      simp
  have hε : 0 < ε := lt_min (lt_min hεe hεe') (lt_min (lt_min hεs hεs') (lt_min hεγ hεγ'))
  refine ⟨ε, hε, ?_⟩
  have heqon : EqOn ((extChartAt I (γ t₀)) ∘ γ) ((extChartAt I (γ' t₀)) ∘ γ')
    (Ioo (t₀ - ε) (t₀ + ε)) := by
    apply ODE_solution_unique_of_mem_set_Ioo hlip (t₀ := t₀) _ hf _ _ hf'
    · intros t ht
      have ht' : t ∈ Ioo (t₀ - εγ') (t₀ + εγ') := by
        apply mem_of_mem_of_subset ht
        rw [← Real.ball_eq_Ioo, ← Real.ball_eq_Ioo]
        apply Metric.ball_subset_ball
        simp
      have hrw : HasDerivAt ((extChartAt I (γ' t₀)) ∘ γ')
        (tangentCoordChange I (γ' t) (γ' t₀) (γ' t) (v (γ' t))) t := by
        -- turn `HasDerivAt` into comp of `HasMFDerivAt`
        rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
        -- finagle to use `HasMFDerivAt.comp` on `hasMFDerivAt_extChartAt` and `this`
        have := (hasMFDerivAt_extChartAt I (x := γ' t₀) (y := γ' t) (by
          rw [← extChartAt_source I]
          apply hsrc'
          apply mem_of_mem_of_subset ht
          rw [← Real.ball_eq_Ioo]
          apply Metric.ball_subset_ball
          simp
        )).comp t (hγ' t ht')
        have h2 : ContinuousLinearMap.comp
          (mfderiv I I (↑(chartAt H (γ' t₀))) (γ' t))
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v (γ' t))) =
          ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          ((tangentCoordChange I (γ' t) (γ' t₀) (γ' t)) (v (γ' t))) := by
          rw [ContinuousLinearMap.ext_iff]
          intro a
          rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.one_apply, ContinuousLinearMap.map_smul_of_tower,
            ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply]
          congr
          rw [tangentCoordChange_def, mfderiv]
          have hdiff : MDifferentiableAt I I (↑(chartAt H (γ' t₀))) (γ' t) := by
            apply mdifferentiableAt_atlas I (ChartedSpace.chart_mem_atlas _)
            rw [← extChartAt_source I]
            apply hsrc'
            apply mem_of_mem_of_subset ht
            rw [← Real.ball_eq_Ioo]
            apply Metric.ball_subset_ball
            simp
          simp only [hdiff, if_true]
          rfl
        rw [← h2]
        exact this
      have hsub : (fun x ↦ v') t ((↑(extChartAt I (γ' t₀)) ∘ γ') t) =
        (tangentCoordChange I (γ' t) (γ' t₀) (γ' t)) (v (γ' t)) := by
        dsimp only
        rw [h, Function.comp_apply, LocalEquiv.left_inv]
        apply hsrc'
        apply mem_of_mem_of_subset ht
        rw [← Real.ball_eq_Ioo]
        apply Metric.ball_subset_ball
        simp
      rw [hsub]
      exact hrw
    · intros t ht
      apply hmem'
      apply mem_of_mem_of_subset ht
      rw [← Real.ball_eq_Ioo]
      apply Metric.ball_subset_ball
      simp
    · simp [h]
    · rw [← Real.ball_eq_Ioo]
      exact Metric.mem_ball_self hε
    · intros t ht
      have ht' : t ∈ Ioo (t₀ - εγ) (t₀ + εγ) := by
        apply mem_of_mem_of_subset ht
        rw [← Real.ball_eq_Ioo, ← Real.ball_eq_Ioo]
        apply Metric.ball_subset_ball
        simp
      have hrw : HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
        (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) t := by
        -- turn `HasDerivAt` into comp of `HasMFDerivAt`
        rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
        -- finagle to use `HasMFDerivAt.comp` on `hasMFDerivAt_extChartAt` and `this`
        have := (hasMFDerivAt_extChartAt I (x := γ t₀) (y := γ t) (by
          rw [← extChartAt_source I]
          apply hsrc
          apply mem_of_mem_of_subset ht
          rw [← Real.ball_eq_Ioo]
          apply Metric.ball_subset_ball
          simp
        )).comp t (hγ t ht')
        have h2 : ContinuousLinearMap.comp
          (mfderiv I I (↑(chartAt H (γ t₀))) (γ t))
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v (γ t))) =
          ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          ((tangentCoordChange I (γ t) (γ t₀) (γ t)) (v (γ t))) := by
          rw [ContinuousLinearMap.ext_iff]
          intro a
          rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.one_apply, ContinuousLinearMap.map_smul_of_tower,
            ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply]
          congr
          rw [tangentCoordChange_def, mfderiv]
          have hdiff : MDifferentiableAt I I (↑(chartAt H (γ t₀))) (γ t) := by
            apply mdifferentiableAt_atlas I (ChartedSpace.chart_mem_atlas _)
            rw [← extChartAt_source I]
            apply hsrc
            apply mem_of_mem_of_subset ht
            rw [← Real.ball_eq_Ioo]
            apply Metric.ball_subset_ball
            simp
          simp only [hdiff, if_true]
          rfl
        rw [← h2]
        exact this
      have hsub : (fun _ ↦ v') t ((↑(extChartAt I (γ t₀)) ∘ γ) t) =
        (tangentCoordChange I (γ t) (γ t₀) (γ t)) (v (γ t)) := by
        dsimp only
        rw [Function.comp_apply, LocalEquiv.left_inv]
        apply hsrc
        apply mem_of_mem_of_subset ht
        rw [← Real.ball_eq_Ioo]
        apply Metric.ball_subset_ball
        simp
      rw [hsub]
      exact hrw
    · intros t ht
      apply hmem
      apply mem_of_mem_of_subset ht
      rw [← Real.ball_eq_Ioo]
      apply Metric.ball_subset_ball
      simp
  refine EqOn.trans ?_ (EqOn.trans (heqon.comp_left (g := (extChartAt I (γ t₀)).symm)) ?_)
  · intros t ht
    rw [Function.comp_apply, Function.comp_apply, LocalEquiv.left_inv]
    apply hsrc
    rw [← Real.ball_eq_Ioo] at ht
    apply mem_of_mem_of_subset ht (Metric.ball_subset_ball _)
    simp
  · intros t ht
    rw [Function.comp_apply, Function.comp_apply, h, LocalEquiv.left_inv]
    apply hsrc'
    rw [← Real.ball_eq_Ioo] at ht
    apply mem_of_mem_of_subset ht (Metric.ball_subset_ball _)
    simp

/-- Integral curves are unique on open intervals.

  If a continuously differentiable vector field `v` admits two integral curves `γ γ' : ℝ → M`
  on some open interval `Ioo a b`, and `γ t₀ = γ' t₀` for some `t ∈ Ioo a b`, then `γ` and `γ'`
  agree on `Ioo a b`. -/
theorem isIntegralCurveOn_Ioo_eqOn_of_contMDiff {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [T2Space M] {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M}
    {a b : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hip : ∀ t ∈ Ioo a b, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurveOn γ v (Ioo a b)) (hγ' : IsIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) := by
  /-
  strategy:
  * Lee P.213, just need to translate "S is closed in J" to type theory language
  -/
  set s := {t | γ t = γ' t} ∩ Ioo a b with hs
  have hsub : Ioo a b ⊆ s := by
    apply isPreconnected_Ioo.subset_of_closure_inter_subset
    · rw [isOpen_iff_mem_nhds]
      intro t₁ ht₁
      rw [mem_nhds_iff]
      have : ∃ ε > 0, EqOn γ γ' (Ioo (t₁ - ε) (t₁ + ε)) := by
        apply isIntegralCurveAt_eqOn_of_contMDiffAt (I := I)
        · apply hip
          exact ht₁.2
        · exact hv.contMDiffAt
        · apply hγ.isIntegralCurveAt
          exact Ioo_mem_nhds ht₁.2.1 ht₁.2.2
        · apply hγ'.isIntegralCurveAt
          exact Ioo_mem_nhds ht₁.2.1 ht₁.2.2
        · exact ht₁.1
      obtain ⟨ε, hε, heqon⟩ := this
      use Ioo (max a (t₁ - ε)) (min b (t₁ + ε))
      refine ⟨?_, isOpen_Ioo, ?_⟩
      · apply subset_inter
        · intros t ht
          apply @heqon t
          apply mem_of_mem_of_subset ht
          apply Ioo_subset_Ioo (by simp) (by simp)
        · apply Ioo_subset_Ioo (by simp) (by simp)
      · rw [mem_Ioo]
        constructor
        · apply max_lt ht₁.2.1
          simp [hε]
        · apply lt_min ht₁.2.2
          simp [hε]
    · use t₀
      rw [mem_inter_iff]
      use ht₀
      use h
    · -- is this really the most convenient way to pass to subtype topology?
      rw [hs, ← Subtype.image_preimage_val, ← Subtype.image_preimage_val,
        image_subset_image_iff Subtype.val_injective, preimage_setOf_eq]
      intros t ht
      rw [mem_preimage, ← closure_subtype] at ht
      revert ht t
      apply IsClosed.closure_subset
      apply isClosed_eq
      · rw [continuous_iff_continuousAt]
        rintro ⟨t, ht⟩
        apply ContinuousAt.comp _ continuousAt_subtype_val
        rw [Subtype.coe_mk]
        exact hγ.continuousAt ht
      · rw [continuous_iff_continuousAt]
        rintro ⟨t, ht⟩
        apply ContinuousAt.comp _ continuousAt_subtype_val
        rw [Subtype.coe_mk]
        exact hγ'.continuousAt ht
  intros t ht
  exact mem_setOf.mp ((subset_def ▸ hsub) t ht).1

/-- Global integral curves are unique. -/
theorem isIntegralCurve_eq_of_contMDiff {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [T2Space M] {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M}
    (hip : ∀ t, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurve γ v) (hγ' : IsIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' := by
  ext t
  have : ∃ T > 0, t ∈ Ioo (t₀ - T) (t₀ + T) := by
    refine ⟨2 * |t - t₀| + 1, add_pos_of_nonneg_of_pos (by simp) zero_lt_one, ?_⟩
    rw [mem_Ioo]
    by_cases ht : t - t₀ < 0
    · rw [abs_of_neg ht]
      constructor <;> linarith
    · rw [abs_of_nonneg (not_lt.mp ht)]
      constructor <;> linarith
  obtain ⟨T, hT, ht⟩ := this
  exact isIntegralCurveOn_Ioo_eqOn_of_contMDiff I t₀
    (Real.ball_eq_Ioo t₀ T ▸ Metric.mem_ball_self hT) (fun t _ => hip t) hv
    (IsIntegralCurveOn.mono (hγ.isIntegralCurveOn _) (subset_univ _))
    (IsIntegralCurveOn.mono (hγ'.isIntegralCurveOn _) (subset_univ _)) h ht

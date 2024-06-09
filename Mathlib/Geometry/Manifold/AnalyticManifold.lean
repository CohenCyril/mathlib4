/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Analytic manifolds (possibly with boundary or corners)

An analytic manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which changes of coordinates are analytic in the
interior and smooth everywhere (including at the boundary).  The definition mirrors
`SmoothManifoldWithCorners`, but using an `analyticGroupoid` in place of `contDiffGroupoid`.  All
analytic manifolds are smooth manifolds.

Completeness is required throughout, but this is nonessential: it is due to many of the lemmas about
`AnalyticWithinOn` requiring completeness for easy of proof.
-/

noncomputable section

open Set Filter Function

open scoped Manifold Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M]

/-!
## `analyticGroupoid`

`f ∈ PartialHomeomorph H H` is in `analyticGroupoid I` if `f` and `f.symm` are smooth everywhere,
analytic on the interior, and map the interior to itself.  This allows us to define
`AnalyticManifold` including in cases with boundary.
-/


section analyticGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M]

/-- Given a model with corners `(E, H)`, we define the groupoid of analytic transformations of `H`
as the maps that are analytic and map interior to interior when read in `E` through `I`. We also
explicitly define that they are `C^∞` on the whole domain, since we are only requiring
analyticity on the interior of the domain. -/
def analyticGroupoid : StructureGroupoid H :=
  (contDiffGroupoid ∞ I) ⊓ Pregroupoid.groupoid
    { property := fun f s => AnalyticOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
        (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)
      comp := fun {f g u v} hf hg _ _ _ => by
        simp only [] at hf hg ⊢
        have comp : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
        apply And.intro
        · simp only [comp, preimage_inter]
          refine hg.left.comp (hf.left.mono ?_) ?_
          · simp only [subset_inter_iff, inter_subset_right]
            rw [inter_assoc]
            simp
          · intro x hx
            apply And.intro
            · rw [mem_preimage, comp_apply, I.left_inv]
              exact hx.left.right
            · apply hf.right
              rw [mem_image]
              exact ⟨x, ⟨⟨hx.left.left, hx.right⟩, rfl⟩⟩
        · simp only [comp]
          rw [image_comp]
          intro x hx
          rw [mem_image] at hx
          rcases hx with ⟨x', hx'⟩
          refine hg.right ⟨x', And.intro ?_ hx'.right⟩
          apply And.intro
          · have hx'1 : x' ∈ ((v.preimage f).preimage (I.symm)).image (I ∘ f ∘ I.symm) := by
              refine image_subset (I ∘ f ∘ I.symm) ?_ hx'.left
              rw [preimage_inter]
              refine Subset.trans ?_ (u.preimage I.symm).inter_subset_right
              apply inter_subset_left
            rcases hx'1 with ⟨x'', hx''⟩
            rw [hx''.right.symm]
            simp only [comp_apply, mem_preimage, I.left_inv]
            exact hx''.left
          · rw [mem_image] at hx'
            rcases hx'.left with ⟨x'', hx''⟩
            exact hf.right ⟨x'', ⟨⟨hx''.left.left.left, hx''.left.right⟩, hx''.right⟩⟩
      id_mem := by
        apply And.intro
        · simp only [preimage_univ, univ_inter]
          exact AnalyticOn.congr isOpen_interior
            (f := (1 : E →L[𝕜] E)) (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
            (fun z hz => (I.right_inv (interior_subset hz)).symm)
        · intro x hx
          simp only [id_comp, comp_apply, preimage_univ, univ_inter, mem_image] at hx
          rcases hx with ⟨y, hy⟩
          rw [← hy.right, I.right_inv (interior_subset hy.left)]
          exact hy.left
      locality := fun {f u} _ h => by
        simp only [] at h
        simp only [AnalyticOn]
        apply And.intro
        · intro x hx
          rcases h (I.symm x) (mem_preimage.mp hx.left) with ⟨v, hv⟩
          exact hv.right.right.left x ⟨mem_preimage.mpr ⟨hx.left, hv.right.left⟩, hx.right⟩
        · apply mapsTo'.mp
          simp only [MapsTo]
          intro x hx
          rcases h (I.symm x) hx.left with ⟨v, hv⟩
          apply hv.right.right.right
          rw [mem_image]
          have hx' := And.intro hx (mem_preimage.mpr hv.right.left)
          rw [← mem_inter_iff, inter_comm, ← inter_assoc, ← preimage_inter, inter_comm v u] at hx'
          exact ⟨x, ⟨hx', rfl⟩⟩
      congr := fun {f g u} hu fg hf => by
        simp only [] at hf ⊢
        apply And.intro
        · refine AnalyticOn.congr (IsOpen.inter (hu.preimage I.continuous_symm) isOpen_interior)
            hf.left ?_
          intro z hz
          simp only [comp_apply]
          rw [fg (I.symm z) hz.left]
        · intro x hx
          apply hf.right
          rw [mem_image] at hx ⊢
          rcases hx with ⟨y, hy⟩
          refine ⟨y, ⟨hy.left, ?_⟩⟩
          rw [comp_apply, comp_apply, fg (I.symm y) hy.left.left] at hy
          exact hy.right }

/-- An identity partial homeomorphism belongs to the analytic groupoid. -/
theorem ofSet_mem_analyticGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ analyticGroupoid I := by
  rw [analyticGroupoid]
  refine And.intro (ofSet_mem_contDiffGroupoid ∞ I hs) ?_
  apply mem_groupoid_of_pregroupoid.mpr
  suffices h : AnalyticOn 𝕜 (I ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
      (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ I.symm) ⊆ interior (range I) by
    simp only [PartialHomeomorph.ofSet_apply, id_comp, PartialHomeomorph.ofSet_toPartialEquiv,
      PartialEquiv.ofSet_source, h, comp_apply, mem_range, image_subset_iff, true_and,
      PartialHomeomorph.ofSet_symm, PartialEquiv.ofSet_target, and_self]
    intro x hx
    refine mem_preimage.mpr ?_
    rw [← I.right_inv (interior_subset hx.right)] at hx
    exact hx.right
  apply And.intro
  · have : AnalyticOn 𝕜 (1 : E →L[𝕜] E) (univ : Set E) := (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
    exact (this.mono (subset_univ (s.preimage (I.symm) ∩ interior (range I)))).congr
      ((hs.preimage I.continuous_symm).inter isOpen_interior)
      fun z hz => (I.right_inv (interior_subset hz.right)).symm
  · intro x hx
    simp only [comp_apply, mem_image] at hx
    rcases hx with ⟨y, hy⟩
    rw [← hy.right, I.right_inv (interior_subset hy.left.right)]
    exact hy.left.right

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the analytic groupoid. -/
theorem symm_trans_mem_analyticGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ analyticGroupoid I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_analyticGroupoid I e.open_target) this

/-- The analytic groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (analyticGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      apply (analyticGroupoid I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_analyticGroupoid I hs)

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem mem_analyticGroupoid_of_boundaryless [CompleteSpace E] [I.Boundaryless]
    (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOn 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
    AnalyticOn 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  apply Iff.intro
  · intro he
    have := mem_groupoid_of_pregroupoid.mp he.right
    simp only [I.image_eq, I.range_eq_univ, interior_univ, subset_univ, and_true] at this ⊢
    exact this
  · intro he
    apply And.intro
    all_goals apply mem_groupoid_of_pregroupoid.mpr; simp only [I.image_eq, I.range_eq_univ,
      interior_univ, subset_univ, and_true, contDiffPregroupoid] at he ⊢
    · exact ⟨he.left.contDiffOn, he.right.contDiffOn⟩
    · exact he

end analyticGroupoid


section analyticGroupoid

/-- Given a model with corners `(E, H)`, we define the pregroupoid of analytic transformations of
`H` as the maps that are `AnalyticWithinOn` when read in `E` through `I`.  Using `AnalyticWithinOn`
rather than `AnalyticOn` gives us meaningful definitions at boundary points. -/
def analyticPregroupoid : Pregroupoid H where
  property f s := AnalyticWithinOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
  comp {f g u v} hf hg _ _ _ := by
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [this]
    apply hg.comp
    · exact hf.mono fun _ ⟨hx1, hx2⟩ ↦ ⟨hx1.1, hx2⟩
    · rintro x ⟨hx1, _⟩
      simp only [mfld_simps] at hx1 ⊢
      exact hx1.2
  id_mem := by
    apply AnalyticWithinOn.congr (analyticOn_id 𝕜).analyticWithinOn
    rintro x ⟨_, hx2⟩
    rcases mem_range.1 hx2 with ⟨y, hy⟩
    rw [← hy]
    simp only [mfld_simps]
  locality {f u} _ H := by
    apply analyticWithinOn_of_locally_analyticWithinOn
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩
    have : I.symm ⁻¹' (u ∩ v) ∩ range I = I.symm ⁻¹' u ∩ range I ∩ I.symm ⁻¹' v := by
      rw [preimage_inter, inter_assoc, inter_assoc]
      congr 1
      rw [inter_comm]
    rw [this] at hv
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  congr {f g u} _ fg hf := by
    apply hf.congr
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rw [fg _ hy1]

/-- Given a model with corners `(E, H)`, we define the groupoid of analytic transformations of
`H` as the maps that are `AnalyticWithinOn` when read in `E` through `I`.  Using `AnalyticWithinOn`
rather than `AnalyticOn` gives us meaningful definitions at boundary points. -/
def analyticGroupoid : StructureGroupoid H :=
  (analyticPregroupoid I).groupoid

/-- An identity partial homeomorphism belongs to the analytic groupoid. -/
theorem ofSet_mem_analyticGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ analyticGroupoid I := by
  rw [analyticGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : AnalyticWithinOn 𝕜 (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I) by
    simp [h, analyticPregroupoid]
  have hi : AnalyticWithinOn 𝕜 id (univ : Set E) := (analyticOn_id _).analyticWithinOn
  exact (hi.mono (subset_univ _)).congr (fun x hx ↦ (I.right_inv hx.2).symm)

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the analytic groupoid. -/
theorem symm_trans_mem_analyticGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ analyticGroupoid I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_analyticGroupoid I e.open_target) this

/-- The analytic groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (analyticGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      apply StructureGroupoid.le_iff.mpr
      rintro e ⟨s, hs, hes⟩
      apply (analyticGroupoid I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_analyticGroupoid I hs)

/-- `f ∈ analyticGroupoid` iff it and its inverse are analytic within `range I`. -/
lemma mem_analyticGroupoid {I : ModelWithCorners 𝕜 E H} {f : PartialHomeomorph H H} :
    f ∈ analyticGroupoid I ↔
      AnalyticWithinOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' f.source ∩ range I) ∧
      AnalyticWithinOn 𝕜 (I ∘ f.symm ∘ I.symm) (I.symm ⁻¹' f.target ∩ range I) := by
  rfl

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem mem_analyticGroupoid_of_boundaryless [CompleteSpace E] [I.Boundaryless]
    (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOn 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
      AnalyticOn 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  rw [mem_analyticGroupoid]
  simp only [I.range_eq_univ, inter_univ, I.image_eq]
  rw [IsOpen.analyticWithinOn_iff_analyticOn, IsOpen.analyticWithinOn_iff_analyticOn]
  · exact I.continuous_symm.isOpen_preimage _ e.open_target
  · exact I.continuous_symm.isOpen_preimage _ e.open_source

/-- `analyticGroupoid` is closed under products -/
theorem analyticGroupoid_prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] [TopologicalSpace B] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {f : PartialHomeomorph A A} {g : PartialHomeomorph B B}
    (fa : f ∈ analyticGroupoid I) (ga : g ∈ analyticGroupoid J) :
    f.prod g ∈ analyticGroupoid (I.prod J) := by
  have pe : range (I.prod J) = (range I).prod (range J) := I.range_prod
  simp only [mem_analyticGroupoid, Function.comp, image_subset_iff] at fa ga ⊢
  constructor
  · apply AnalyticWithinOn.prod
    · exact fa.1.comp (analyticOn_fst _).analyticWithinOn fun _ m ↦ ⟨m.1.1, (pe.subst m.2).1⟩
    · exact ga.1.comp (analyticOn_snd _).analyticWithinOn fun _ m ↦ ⟨m.1.2, (pe.subst m.2).2⟩
  · apply AnalyticWithinOn.prod
    · exact fa.2.comp (analyticOn_fst _).analyticWithinOn fun _ m ↦ ⟨m.1.1, (pe.subst m.2).1⟩
    · exact ga.2.comp (analyticOn_snd _).analyticWithinOn fun _ m ↦ ⟨m.1.2, (pe.subst m.2).2⟩

end analyticGroupoid

section AnalyticManifold

/-- An analytic manifold w.r.t. a model `I : ModelWithCorners 𝕜 E H` is a charted space over H
    s.t. all extended chart conversion maps are analytic. -/
class AnalyticManifold (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] extends HasGroupoid M (analyticGroupoid I) : Prop

/-- Normed spaces are analytic manifolds over themselves -/
instance AnalyticManifold.self : AnalyticManifold 𝓘(𝕜, E) E where

/-- `M × N` is a analytic manifold if `M` and `N` are -/
instance AnalyticManifold.prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] [TopologicalSpace B] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {M : Type} [TopologicalSpace M] [ChartedSpace A M] [m : AnalyticManifold I M]
    {N : Type} [TopologicalSpace N] [ChartedSpace B N] [n : AnalyticManifold J N] :
    AnalyticManifold (I.prod J) (M × N) where
  compatible := by
    intro f g ⟨f1, f2, hf1, hf2, fe⟩ ⟨g1, g2, hg1, hg2, ge⟩
    rw [← fe, ← ge, PartialHomeomorph.prod_symm, PartialHomeomorph.prod_trans]
    exact analyticGroupoid_prod (m.toHasGroupoid.compatible f2 g2)
      (n.toHasGroupoid.compatible hf2 hg2)

/-- Complex manifolds are smooth manifolds -/
instance AnalyticManifold.smoothManifoldWithCorners [ChartedSpace H M] [cm : AnalyticManifold I M] :
    SmoothManifoldWithCorners I M where
  compatible := by
    intro f g hf hg
    have m := cm.compatible hf hg
    exact ⟨m.1.contDiffOn, m.2.contDiffOn⟩

end AnalyticManifold

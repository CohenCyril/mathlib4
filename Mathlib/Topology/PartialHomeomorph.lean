/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.Sets.Opens

#align_import topology.local_homeomorph from "leanprover-community/mathlib"@"431589bce478b2229eba14b14a283250428217db"

/-!
# Partial homeomorphisms
# Partial homeomorphisms

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`PartialHomeomorph α β` is an extension of `PartialEquiv α β`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

* `Homeomorph.toPartialHomeomorph`: associating a partial homeomorphism to a homeomorphism, with
  `source = target = Set.univ`;
* `PartialHomeomorph.symm`: the inverse of a partial homeomorphism
* `PartialHomeomorph.trans`: the composition of two partial homeomorphisms
* `PartialHomeomorph.refl`: the identity partial homeomorphism
* `PartialHomeomorph.ofSet`: the identity on a set `s`
* `PartialHomeomorph.EqOnSource`: equivalence relation describing the "right" notion of equality
  for partial homeomorphisms

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/


open Function Set Filter Topology

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-- Partial homeomorphisms, defined on open subsets of the space -/
-- porting note: commented @[nolint has_nonempty_instance]
structure PartialHomeomorph (α : Type*) (β : Type*) [TopologicalSpace α]
  [TopologicalSpace β] extends PartialEquiv α β where
  open_source : IsOpen source
  open_target : IsOpen target
  continuousOn_toFun : ContinuousOn toFun source
  continuousOn_invFun : ContinuousOn invFun target
#align local_homeomorph PartialHomeomorph

namespace PartialHomeomorph

variable (e : PartialHomeomorph α β) (e' : PartialHomeomorph β γ)

/-- Coercion of a partial homeomorphisms to a function. We don't use `e.toFun` because it is
actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`.
While we may want to switch to this behavior later, doing it mid-port will break a lot of proofs. -/
@[coe] def toFun' : α → β := e.toFun

/-- Coercion of a `PartialHomeomorph` to function.
Note that a `PartialHomeomorph` is not `FunLike`. -/
instance : CoeFun (PartialHomeomorph α β) fun _ => α → β :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of a partial homeomorphism -/
@[symm]
protected def symm : PartialHomeomorph β α where
  toPartialEquiv := e.toPartialEquiv.symm
  open_source := e.open_target
  open_target := e.open_source
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun
#align local_homeomorph.symm PartialHomeomorph.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : PartialHomeomorph α β) : α → β := e
#align local_homeomorph.simps.apply PartialHomeomorph.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : PartialHomeomorph α β) : β → α := e.symm
#align local_homeomorph.simps.symm_apply PartialHomeomorph.Simps.symm_apply

initialize_simps_projections PartialHomeomorph (toFun → apply, invFun → symm_apply)

protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuousOn_toFun
#align local_homeomorph.continuous_on PartialHomeomorph.continuousOn

theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuousOn_invFun
#align local_homeomorph.continuous_on_symm PartialHomeomorph.continuousOn_symm

@[simp, mfld_simps]
theorem mk_coe (e : PartialEquiv α β) (a b c d) : (PartialHomeomorph.mk e a b c d : α → β) = e :=
  rfl
#align local_homeomorph.mk_coe PartialHomeomorph.mk_coe

@[simp, mfld_simps]
theorem mk_coe_symm (e : PartialEquiv α β) (a b c d) :
    ((PartialHomeomorph.mk e a b c d).symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.mk_coe_symm PartialHomeomorph.mk_coe_symm

theorem toPartialEquiv_injective :
    Injective (toPartialEquiv : PartialHomeomorph α β → PartialEquiv α β)
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl => rfl
#align local_homeomorph.to_local_equiv_injective PartialHomeomorph.toPartialEquiv_injective

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem toFun_eq_coe (e : PartialHomeomorph α β) : e.toFun = e :=
  rfl
#align local_homeomorph.to_fun_eq_coe PartialHomeomorph.toFun_eq_coe

@[simp, mfld_simps]
theorem invFun_eq_coe (e : PartialHomeomorph α β) : e.invFun = e.symm :=
  rfl
#align local_homeomorph.inv_fun_eq_coe PartialHomeomorph.invFun_eq_coe

@[simp, mfld_simps]
theorem coe_coe : (e.toPartialEquiv : α → β) = e :=
  rfl
#align local_homeomorph.coe_coe PartialHomeomorph.coe_coe

@[simp, mfld_simps]
theorem coe_coe_symm : (e.toPartialEquiv.symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.coe_coe_symm PartialHomeomorph.coe_coe_symm

@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h
#align local_homeomorph.map_source PartialHomeomorph.map_source

/-- Variant of `map_source`, stated for images of subsets of `source`. -/
lemma map_source'' : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h
#align local_homeomorph.map_target PartialHomeomorph.map_target

@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h
#align local_homeomorph.left_inv PartialHomeomorph.left_inv

@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
#align local_homeomorph.right_inv PartialHomeomorph.right_inv

theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toPartialEquiv.eq_symm_apply hx hy
#align local_homeomorph.eq_symm_apply PartialHomeomorph.eq_symm_apply

protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source
#align local_homeomorph.maps_to PartialHomeomorph.mapsTo

protected theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo
#align local_homeomorph.symm_maps_to PartialHomeomorph.symm_mapsTo

protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv
#align local_homeomorph.left_inv_on PartialHomeomorph.leftInvOn

protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv
#align local_homeomorph.right_inv_on PartialHomeomorph.rightInvOn

protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩
#align local_homeomorph.inv_on PartialHomeomorph.invOn

protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn
#align local_homeomorph.inj_on PartialHomeomorph.injOn

protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.symm_mapsTo
#align local_homeomorph.bij_on PartialHomeomorph.bijOn

protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn
#align local_homeomorph.surj_on PartialHomeomorph.surjOn

/-- Interpret a `Homeomorph` as a `PartialHomeomorph` by restricting it
to an open set `s` in the domain and to `t` in the codomain. -/
@[simps! (config := .asFn) apply symm_apply toPartialEquiv,
  simps! (config := .lemmasOnly) source target]
def _root_.Homeomorph.toPartialHomeomorphOfImageEq (e : α ≃ₜ β) (s : Set α) (hs : IsOpen s)
    (t : Set β) (h : e '' s = t) : PartialHomeomorph α β where
  toPartialEquiv := e.toPartialEquivOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn

/-- A homeomorphism induces a partial homeomorphism on the whole space -/
@[simps! (config := mfld_cfg)]
def _root_.Homeomorph.toPartialHomeomorph (e : α ≃ₜ β) : PartialHomeomorph α β :=
  e.toPartialHomeomorphOfImageEq univ isOpen_univ univ <| by rw [image_univ, e.surjective.range_eq]
#align homeomorph.to_local_homeomorph Homeomorph.toPartialHomeomorph

/-- Replace `toPartialEquiv` field to provide better definitional equalities. -/
def replaceEquiv (e : PartialHomeomorph α β) (e' : PartialEquiv α β) (h : e.toPartialEquiv = e') :
    PartialHomeomorph α β where
  toPartialEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun
#align local_homeomorph.replace_equiv PartialHomeomorph.replaceEquiv

theorem replaceEquiv_eq_self (e' : PartialEquiv α β)
    (h : e.toPartialEquiv = e') : e.replaceEquiv e' h = e := by
  cases e
  subst e'
  rfl
#align local_homeomorph.replace_equiv_eq_self PartialHomeomorph.replaceEquiv_eq_self

theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo
#align local_homeomorph.source_preimage_target PartialHomeomorph.source_preimage_target

@[deprecated toPartialEquiv_injective]
theorem eq_of_localEquiv_eq {e e' : PartialHomeomorph α β}
    (h : e.toPartialEquiv = e'.toPartialEquiv) : e = e' :=
  toPartialEquiv_injective h
#align local_homeomorph.eq_of_local_equiv_eq PartialHomeomorph.eq_of_localEquiv_eq

theorem eventually_left_inverse {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'
#align local_homeomorph.eventually_left_inverse PartialHomeomorph.eventually_left_inverse

theorem eventually_left_inverse' {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)
#align local_homeomorph.eventually_left_inverse' PartialHomeomorph.eventually_left_inverse'

theorem eventually_right_inverse {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'
#align local_homeomorph.eventually_right_inverse PartialHomeomorph.eventually_right_inverse

theorem eventually_right_inverse' {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)
#align local_homeomorph.eventually_right_inverse' PartialHomeomorph.eventually_right_inverse'

theorem eventually_ne_nhdsWithin {x} (hx : x ∈ e.source) :
    ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhdsWithin_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']
#align local_homeomorph.eventually_ne_nhds_within PartialHomeomorph.eventually_ne_nhdsWithin

theorem nhdsWithin_source_inter {x} (hx : x ∈ e.source) (s : Set α) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)
#align local_homeomorph.nhds_within_source_inter PartialHomeomorph.nhdsWithin_source_inter

theorem nhdsWithin_target_inter {x} (hx : x ∈ e.target) (s : Set β) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhdsWithin_source_inter hx s
#align local_homeomorph.nhds_within_target_inter PartialHomeomorph.nhdsWithin_target_inter

theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h
#align local_homeomorph.image_eq_target_inter_inv_preimage PartialHomeomorph.image_eq_target_inter_inv_preimage

theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s
#align local_homeomorph.image_source_inter_eq' PartialHomeomorph.image_source_inter_eq'

theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toPartialEquiv.image_source_inter_eq s
#align local_homeomorph.image_source_inter_eq PartialHomeomorph.image_source_inter_eq

theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
#align local_homeomorph.symm_image_eq_source_inter_preimage PartialHomeomorph.symm_image_eq_source_inter_preimage

theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
#align local_homeomorph.symm_image_target_inter_eq PartialHomeomorph.symm_image_target_inter_eq

theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s
#align local_homeomorph.source_inter_preimage_inv_preimage PartialHomeomorph.source_inter_preimage_inv_preimage

theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
#align local_homeomorph.target_inter_inv_preimage_preimage PartialHomeomorph.target_inter_inv_preimage_preimage

theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s
#align local_homeomorph.source_inter_preimage_target_inter PartialHomeomorph.source_inter_preimage_target_inter

theorem image_source_eq_target : e '' e.source = e.target :=
  e.toPartialEquiv.image_source_eq_target
#align local_homeomorph.image_source_eq_target PartialHomeomorph.image_source_eq_target

theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
#align local_homeomorph.symm_image_target_eq_source PartialHomeomorph.symm_image_target_eq_source

/-- Two partial homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `EqOnSource`. -/
@[ext]
protected theorem ext (e' : PartialHomeomorph α β) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialEquiv_injective (PartialEquiv.ext h hinv hs)
#align local_homeomorph.ext PartialHomeomorph.ext

protected theorem ext_iff {e e' : PartialHomeomorph α β} :
    e = e' ↔ (∀ x, e x = e' x) ∧ (∀ x, e.symm x = e'.symm x) ∧ e.source = e'.source :=
  ⟨by
    rintro rfl
    exact ⟨fun x => rfl, fun x => rfl, rfl⟩, fun h => e.ext e' h.1 h.2.1 h.2.2⟩
#align local_homeomorph.ext_iff PartialHomeomorph.ext_iff

@[simp, mfld_simps]
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl
#align local_homeomorph.symm_to_local_equiv PartialHomeomorph.symm_toPartialEquiv

-- The following lemmas are already simp via `PartialEquiv`
theorem symm_source : e.symm.source = e.target :=
  rfl
#align local_homeomorph.symm_source PartialHomeomorph.symm_source

theorem symm_target : e.symm.target = e.source :=
  rfl
#align local_homeomorph.symm_target PartialHomeomorph.symm_target

@[simp, mfld_simps] theorem symm_symm : e.symm.symm = e := rfl
#align local_homeomorph.symm_symm PartialHomeomorph.symm_symm

theorem symm_bijective : Function.Bijective
    (PartialHomeomorph.symm : PartialHomeomorph α β → PartialHomeomorph β α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- A partial homeomorphism is continuous at any point of its source -/
protected theorem continuousAt {x : α} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.continuousOn x h).continuousAt (e.open_source.mem_nhds h)
#align local_homeomorph.continuous_at PartialHomeomorph.continuousAt

/-- A partial homeomorphism inverse is continuous at any point of its target -/
theorem continuousAt_symm {x : β} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.continuousAt h
#align local_homeomorph.continuous_at_symm PartialHomeomorph.continuousAt_symm

theorem tendsto_symm {x} (hx : x ∈ e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)
#align local_homeomorph.tendsto_symm PartialHomeomorph.tendsto_symm

theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymm (e.continuousAt hx) <|
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)
#align local_homeomorph.map_nhds_eq PartialHomeomorph.map_nhds_eq

theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by rw [e.left_inv hx]
#align local_homeomorph.symm_map_nhds_eq PartialHomeomorph.symm_map_nhds_eq

theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set α} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs
#align local_homeomorph.image_mem_nhds PartialHomeomorph.image_mem_nhds

theorem map_nhdsWithin_eq {x} (hx : x ∈ e.source) (s : Set α) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.leftInvOn.mono <| inter_subset_left _ _).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
        (e.continuousAt hx).continuousWithinAt
#align local_homeomorph.map_nhds_within_eq PartialHomeomorph.map_nhdsWithin_eq

theorem map_nhdsWithin_preimage_eq {x} (hx : x ∈ e.source) (s : Set β) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhdsWithin_target_inter (e.map_source hx)]
#align local_homeomorph.map_nhds_within_preimage_eq PartialHomeomorph.map_nhdsWithin_preimage_eq

theorem eventually_nhds {x : α} (p : β → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map
#align local_homeomorph.eventually_nhds PartialHomeomorph.eventually_nhds

theorem eventually_nhds' {x : α} (p : α → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x := by
  rw [e.eventually_nhds _ hx]
  refine' eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => _)
  rw [hy]
#align local_homeomorph.eventually_nhds' PartialHomeomorph.eventually_nhds'

theorem eventually_nhdsWithin {x : α} (p : β → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) := by
  refine' Iff.trans _ eventually_map
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.nhdsWithin_target_inter (e.mapsTo hx)]
#align local_homeomorph.eventually_nhds_within PartialHomeomorph.eventually_nhdsWithin

theorem eventually_nhdsWithin' {x : α} (p : α → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x := by
  rw [e.eventually_nhdsWithin _ hx]
  refine eventually_congr <|
    (eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => ?_
  rw [hy]
#align local_homeomorph.eventually_nhds_within' PartialHomeomorph.eventually_nhdsWithin'

/-- This lemma is useful in the manifold library in the case that `e` is a chart. It states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a chart on `γ`).  -/
theorem preimage_eventuallyEq_target_inter_preimage_inter {e : PartialHomeomorph α β} {s : Set α}
    {t : Set γ} {x : α} {f : α → γ} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.source)
    (ht : t ∈ 𝓝 (f x)) :
    e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set β) := by
  rw [eventuallyEq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhdsWithin_iff_eventually.mp (hf.preimage_mem_nhdsWithin ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.mapsTo hy, true_and_iff, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]
#align local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter PartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter

theorem isOpen_inter_preimage {s : Set β} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.continuousOn.isOpen_inter_preimage e.open_source hs
#align local_homeomorph.preimage_open_of_open PartialHomeomorph.isOpen_inter_preimage

theorem isOpen_inter_preimage_symm {s : Set α} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target hs
#align local_homeomorph.preimage_open_of_open_symm PartialHomeomorph.isOpen_inter_preimage_symm

/-- A partial homeomorphism is an open map on its source:
  the image of an open subset of the source is open. -/
lemma isOpen_image_of_subset_source {s : Set α} (hs : IsOpen s) (hse : s ⊆ e.source) :
    IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact e.continuousOn_invFun.isOpen_inter_preimage e.open_target hs
#align local_homeomorph.image_open_of_open PartialHomeomorph.isOpen_image_of_subset_source

/-- The image of the restriction of an open set to the source is open. -/
theorem isOpen_image_source_inter {s : Set α} (hs : IsOpen s) :
    IsOpen (e '' (e.source ∩ s)) :=
  e.isOpen_image_of_subset_source (e.open_source.inter hs) (inter_subset_left _ _)
#align local_homeomorph.image_open_of_open' PartialHomeomorph.isOpen_image_source_inter

/-- The inverse of a partial homeomorphism `e` is an open map on `e.target`. -/
lemma isOpen_image_symm_of_subset_target {t : Set β} (ht : IsOpen t) (hte : t ⊆ e.target) :
    IsOpen (e.symm '' t) :=
  isOpen_image_of_subset_source e.symm ht (e.symm_source ▸ hte)

lemma isOpen_symm_image_iff_of_subset_target {t : Set β} (hs : t ⊆ e.target) :
    IsOpen (e.symm '' t) ↔ IsOpen t := by
  refine ⟨fun h ↦ ?_, fun h ↦ e.symm.isOpen_image_of_subset_source h hs⟩
  have hs' : e.symm '' t ⊆ e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.isOpen_image_of_subset_source h hs'

theorem isOpen_image_iff_of_subset_source {s : Set α} (hs : s ⊆ e.source) :
    IsOpen (e '' s) ↔ IsOpen s := by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target hs, e.symm_symm]

/-!
### `PartialHomeomorph.IsImage` relation

We say that `t : Set β` is an image of `s : Set α` under a partial homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `PartialEquiv.IsImage` for partial homeomorphisms.
In this section we transfer API about `PartialEquiv.IsImage` to partial homeomorphisms and
add a few `PartialHomeomorph`-specific lemmas like `PartialHomeomorph.IsImage.closure`.
-/

/-- We say that `t : Set β` is an image of `s : Set α` under a partial homeomorphism `e`
if any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_homeomorph.is_image PartialHomeomorph.IsImage

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

theorem toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t :=
  h
#align local_homeomorph.is_image.to_local_equiv PartialHomeomorph.IsImage.toPartialEquiv

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
#align local_homeomorph.is_image.apply_mem_iff PartialHomeomorph.IsImage.apply_mem_iff

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toPartialEquiv.symm
#align local_homeomorph.is_image.symm PartialHomeomorph.IsImage.symm

theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy
#align local_homeomorph.is_image.symm_apply_mem_iff PartialHomeomorph.IsImage.symm_apply_mem_iff

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align local_homeomorph.is_image.symm_iff PartialHomeomorph.IsImage.symm_iff

protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toPartialEquiv.mapsTo
#align local_homeomorph.is_image.maps_to PartialHomeomorph.IsImage.mapsTo

theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo
#align local_homeomorph.is_image.symm_maps_to PartialHomeomorph.IsImage.symm_mapsTo

theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toPartialEquiv.image_eq
#align local_homeomorph.is_image.image_eq PartialHomeomorph.IsImage.image_eq

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
#align local_homeomorph.is_image.symm_image_eq PartialHomeomorph.IsImage.symm_image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  PartialEquiv.IsImage.iff_preimage_eq
#align local_homeomorph.is_image.iff_preimage_eq PartialHomeomorph.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq
#align local_homeomorph.is_image.preimage_eq PartialHomeomorph.IsImage.preimage_eq
#align local_homeomorph.is_image.of_preimage_eq PartialHomeomorph.IsImage.of_preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq
#align local_homeomorph.is_image.iff_symm_preimage_eq PartialHomeomorph.IsImage.iff_symm_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq
#align local_homeomorph.is_image.symm_preimage_eq PartialHomeomorph.IsImage.symm_preimage_eq
#align local_homeomorph.is_image.of_symm_preimage_eq PartialHomeomorph.IsImage.of_symm_preimage_eq

theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']
#align local_homeomorph.is_image.iff_symm_preimage_eq' PartialHomeomorph.IsImage.iff_symm_preimage_eq'

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'
#align local_homeomorph.is_image.symm_preimage_eq' PartialHomeomorph.IsImage.symm_preimage_eq'
#align local_homeomorph.is_image.of_symm_preimage_eq' PartialHomeomorph.IsImage.of_symm_preimage_eq'

theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'
#align local_homeomorph.is_image.iff_preimage_eq' PartialHomeomorph.IsImage.iff_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'
#align local_homeomorph.is_image.preimage_eq' PartialHomeomorph.IsImage.preimage_eq'
#align local_homeomorph.is_image.of_preimage_eq' PartialHomeomorph.IsImage.of_preimage_eq'

theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  PartialEquiv.IsImage.of_image_eq h
#align local_homeomorph.is_image.of_image_eq PartialHomeomorph.IsImage.of_image_eq

theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  PartialEquiv.IsImage.of_symm_image_eq h
#align local_homeomorph.is_image.of_symm_image_eq PartialHomeomorph.IsImage.of_symm_image_eq

protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => (h hx).not
#align local_homeomorph.is_image.compl PartialHomeomorph.IsImage.compl

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => (h hx).and (h' hx)
#align local_homeomorph.is_image.inter PartialHomeomorph.IsImage.inter

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => (h hx).or (h' hx)
#align local_homeomorph.is_image.union PartialHomeomorph.IsImage.union

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
#align local_homeomorph.is_image.diff PartialHomeomorph.IsImage.diff

theorem leftInvOn_piecewise {e' : PartialHomeomorph α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toPartialEquiv.leftInvOn_piecewise h'
#align local_homeomorph.is_image.left_inv_on_piecewise PartialHomeomorph.IsImage.leftInvOn_piecewise

theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialHomeomorph α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq
#align local_homeomorph.is_image.inter_eq_of_inter_eq_of_eq_on PartialHomeomorph.IsImage.inter_eq_of_inter_eq_of_eqOn

theorem symm_eqOn_of_inter_eq_of_eqOn {e' : PartialHomeomorph α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq
#align local_homeomorph.is_image.symm_eq_on_of_inter_eq_of_eq_on PartialHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOn

theorem map_nhdsWithin_eq (h : e.IsImage s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhdsWithin_eq hx, h.image_eq, e.nhdsWithin_target_inter (e.map_source hx)]
#align local_homeomorph.is_image.map_nhds_within_eq PartialHomeomorph.IsImage.map_nhdsWithin_eq

protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhdsWithin_eq hx, map_neBot_iff]
#align local_homeomorph.is_image.closure PartialHomeomorph.IsImage.closure

protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl
#align local_homeomorph.is_image.interior PartialHomeomorph.IsImage.interior

protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diff h.interior
#align local_homeomorph.is_image.frontier PartialHomeomorph.IsImage.frontier

theorem isOpen_iff (h : e.IsImage s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.isOpen_inter_preimage hs, fun hs =>
    h.preimage_eq' ▸ e.isOpen_inter_preimage hs⟩
#align local_homeomorph.is_image.is_open_iff PartialHomeomorph.IsImage.isOpen_iff

/-- Restrict a `PartialHomeomorph` to a pair of corresponding open sets. -/
@[simps toPartialEquiv]
def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : PartialHomeomorph α β where
  toPartialEquiv := h.toPartialEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuousOn_toFun := e.continuousOn.mono (inter_subset_left _ _)
  continuousOn_invFun := e.symm.continuousOn.mono (inter_subset_left _ _)
#align local_homeomorph.is_image.restr PartialHomeomorph.IsImage.restr

end IsImage

theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toPartialEquiv.isImage_source_target
#align local_homeomorph.is_image_source_target PartialHomeomorph.isImage_source_target

theorem isImage_source_target_of_disjoint (e' : PartialHomeomorph α β)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht
#align local_homeomorph.is_image_source_target_of_disjoint PartialHomeomorph.isImage_source_target_of_disjoint

/-- Preimage of interior or interior of preimage coincide for partial homeomorphisms,
when restricted to the source. -/
theorem preimage_interior (s : Set β) :
    e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq
#align local_homeomorph.preimage_interior PartialHomeomorph.preimage_interior

theorem preimage_closure (s : Set β) : e.source ∩ e ⁻¹' closure s = e.source ∩ closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq
#align local_homeomorph.preimage_closure PartialHomeomorph.preimage_closure

theorem preimage_frontier (s : Set β) :
    e.source ∩ e ⁻¹' frontier s = e.source ∩ frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq
#align local_homeomorph.preimage_frontier PartialHomeomorph.preimage_frontier

/-- A `PartialEquiv` with continuous open forward map and open source is a `PartialHomeomorph`. -/
def ofContinuousOpenRestrict (e : PartialEquiv α β) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : PartialHomeomorph α β where
  toPartialEquiv := e
  open_source := hs
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.isOpen_range
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn
#align local_homeomorph.of_continuous_open_restrict PartialHomeomorph.ofContinuousOpenRestrict

/-- A `PartialEquiv` with continuous open forward map and open source is a `PartialHomeomorph`. -/
def ofContinuousOpen (e : PartialEquiv α β) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph α β :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs
#align local_homeomorph.of_continuous_open PartialHomeomorph.ofContinuousOpen

/-- Restricting a partial homeomorphism `e` to `e.source ∩ s` when `s` is open.
This is sometimes hard to use because of the openness assumption, but it has the advantage that
when it can be used then its `PartialEquiv` is defeq to `PartialEquiv.restr`. -/
protected def restrOpen (s : Set α) (hs : IsOpen s) : PartialHomeomorph α β :=
  (@IsImage.of_symm_preimage_eq α β _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)
#align local_homeomorph.restr_open PartialHomeomorph.restrOpen

@[simp, mfld_simps]
theorem restrOpen_toPartialEquiv (s : Set α) (hs : IsOpen s) :
    (e.restrOpen s hs).toPartialEquiv = e.toPartialEquiv.restr s :=
  rfl
#align local_homeomorph.restr_open_to_local_equiv PartialHomeomorph.restrOpen_toPartialEquiv

-- Already simp via `PartialEquiv`
theorem restrOpen_source (s : Set α) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source ∩ s :=
  rfl
#align local_homeomorph.restr_open_source PartialHomeomorph.restrOpen_source

/-- Restricting a partial homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since partial homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of partial equivalences -/
@[simps! (config := mfld_cfg) apply symm_apply, simps! (config := .lemmasOnly) source target]
protected def restr (s : Set α) : PartialHomeomorph α β :=
  e.restrOpen (interior s) isOpen_interior
#align local_homeomorph.restr PartialHomeomorph.restr

@[simp, mfld_simps]
theorem restr_toPartialEquiv (s : Set α) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr (interior s) :=
  rfl
#align local_homeomorph.restr_to_local_equiv PartialHomeomorph.restr_toPartialEquiv

theorem restr_source' (s : Set α) (hs : IsOpen s) : (e.restr s).source = e.source ∩ s := by
  rw [e.restr_source, hs.interior_eq]
#align local_homeomorph.restr_source' PartialHomeomorph.restr_source'

theorem restr_toPartialEquiv' (s : Set α) (hs : IsOpen s) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr s := by
  rw [e.restr_toPartialEquiv, hs.interior_eq]
#align local_homeomorph.restr_to_local_equiv' PartialHomeomorph.restr_toPartialEquiv'

theorem restr_eq_of_source_subset {e : PartialHomeomorph α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e :=
  toPartialEquiv_injective <| PartialEquiv.restr_eq_of_source_subset <|
    interior_maximal h e.open_source
#align local_homeomorph.restr_eq_of_source_subset PartialHomeomorph.restr_eq_of_source_subset

@[simp, mfld_simps]
theorem restr_univ {e : PartialHomeomorph α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)
#align local_homeomorph.restr_univ PartialHomeomorph.restr_univ

theorem restr_source_inter (s : Set α) : e.restr (e.source ∩ s) = e.restr s := by
  refine' PartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) _
  simp [e.open_source.interior_eq, ← inter_assoc]
#align local_homeomorph.restr_source_inter PartialHomeomorph.restr_source_inter

/-- The identity on the whole space as a partial homeomorphism. -/
@[simps! (config := mfld_cfg) apply, simps! (config := .lemmasOnly) source target]
protected def refl (α : Type*) [TopologicalSpace α] : PartialHomeomorph α α :=
  (Homeomorph.refl α).toPartialHomeomorph
#align local_homeomorph.refl PartialHomeomorph.refl

@[simp, mfld_simps]
theorem refl_localEquiv : (PartialHomeomorph.refl α).toPartialEquiv = PartialEquiv.refl α :=
  rfl
#align local_homeomorph.refl_local_equiv PartialHomeomorph.refl_localEquiv

@[simp, mfld_simps]
theorem refl_symm : (PartialHomeomorph.refl α).symm = PartialHomeomorph.refl α :=
  rfl
#align local_homeomorph.refl_symm PartialHomeomorph.refl_symm

section

variable {s : Set α} (hs : IsOpen s)

/-- The identity partial equivalence on a set `s` -/
@[simps! (config := mfld_cfg) apply, simps! (config := .lemmasOnly) source target]
def ofSet (s : Set α) (hs : IsOpen s) : PartialHomeomorph α α where
  toPartialEquiv := PartialEquiv.ofSet s
  open_source := hs
  open_target := hs
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn
#align local_homeomorph.of_set PartialHomeomorph.ofSet

@[simp, mfld_simps]
theorem ofSet_toPartialEquiv : (ofSet s hs).toPartialEquiv = PartialEquiv.ofSet s :=
  rfl
#align local_homeomorph.of_set_to_local_equiv PartialHomeomorph.ofSet_toPartialEquiv

@[simp, mfld_simps]
theorem ofSet_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl
#align local_homeomorph.of_set_symm PartialHomeomorph.ofSet_symm

@[simp, mfld_simps]
theorem ofSet_univ_eq_refl : ofSet univ isOpen_univ = PartialHomeomorph.refl α := by ext <;> simp
#align local_homeomorph.of_set_univ_eq_refl PartialHomeomorph.ofSet_univ_eq_refl

end

/-- Composition of two partial homeomorphisms when the target of the first and the source of
the second coincide. -/
@[simps! apply symm_apply toPartialEquiv, simps! (config := .lemmasOnly) source target]
protected def trans' (h : e.target = e'.source) : PartialHomeomorph α γ where
  toPartialEquiv := PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source := e.open_source
  open_target := e'.open_target
  continuousOn_toFun := e'.continuousOn.comp e.continuousOn <| h ▸ e.mapsTo
  continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm <| h.symm ▸ e'.symm_mapsTo
#align local_homeomorph.trans' PartialHomeomorph.trans'

/-- Composing two partial homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
@[trans]
protected def trans : PartialHomeomorph α γ :=
  PartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])
#align local_homeomorph.trans PartialHomeomorph.trans

@[simp, mfld_simps]
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  rfl
#align local_homeomorph.trans_to_local_equiv PartialHomeomorph.trans_toPartialEquiv

@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl
#align local_homeomorph.coe_trans PartialHomeomorph.coe_trans

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl
#align local_homeomorph.coe_trans_symm PartialHomeomorph.coe_trans_symm

theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl
#align local_homeomorph.trans_apply PartialHomeomorph.trans_apply

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl
#align local_homeomorph.trans_symm_eq_symm_trans_symm PartialHomeomorph.trans_symm_eq_symm_trans_symm

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv
#align local_homeomorph.trans_source PartialHomeomorph.trans_source

theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv
#align local_homeomorph.trans_source' PartialHomeomorph.trans_source'

theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv
#align local_homeomorph.trans_source'' PartialHomeomorph.trans_source''

theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv
#align local_homeomorph.image_trans_source PartialHomeomorph.image_trans_source

theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
#align local_homeomorph.trans_target PartialHomeomorph.trans_target

theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
#align local_homeomorph.trans_target' PartialHomeomorph.trans_target'

theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
#align local_homeomorph.trans_target'' PartialHomeomorph.trans_target''

theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
#align local_homeomorph.inv_image_trans_target PartialHomeomorph.inv_image_trans_target

theorem trans_assoc (e'' : PartialHomeomorph γ δ) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  toPartialEquiv_injective <| e.1.trans_assoc _ _
#align local_homeomorph.trans_assoc PartialHomeomorph.trans_assoc

@[simp, mfld_simps]
theorem trans_refl : e.trans (PartialHomeomorph.refl β) = e :=
  toPartialEquiv_injective e.1.trans_refl
#align local_homeomorph.trans_refl PartialHomeomorph.trans_refl

@[simp, mfld_simps]
theorem refl_trans : (PartialHomeomorph.refl α).trans e = e :=
  toPartialEquiv_injective e.1.refl_trans
#align local_homeomorph.refl_trans PartialHomeomorph.refl_trans

theorem trans_ofSet {s : Set β} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by
    rw [trans_source, restr_source, ofSet_source, ← preimage_interior, hs.interior_eq]
#align local_homeomorph.trans_of_set PartialHomeomorph.trans_ofSet

theorem trans_of_set' {s : Set β} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_ofSet, restr_source_inter]
#align local_homeomorph.trans_of_set' PartialHomeomorph.trans_of_set'

theorem ofSet_trans {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  PartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) <| by simp [hs.interior_eq, inter_comm]
#align local_homeomorph.of_set_trans PartialHomeomorph.ofSet_trans

theorem ofSet_trans' {s : Set α} (hs : IsOpen s) :
    (ofSet s hs).trans e = e.restr (e.source ∩ s) := by
  rw [ofSet_trans, restr_source_inter]
#align local_homeomorph.of_set_trans' PartialHomeomorph.ofSet_trans'

@[simp, mfld_simps]
theorem ofSet_trans_ofSet {s : Set α} (hs : IsOpen s) {s' : Set α} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') := by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]
#align local_homeomorph.of_set_trans_of_set PartialHomeomorph.ofSet_trans_ofSet

theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  toPartialEquiv_injective <|
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)
#align local_homeomorph.restr_trans PartialHomeomorph.restr_trans

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same partial equivalence. -/
def EqOnSource (e e' : PartialHomeomorph α β) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source
#align local_homeomorph.eq_on_source PartialHomeomorph.EqOnSource

theorem eqOnSource_iff (e e' : PartialHomeomorph α β) :
    EqOnSource e e' ↔ PartialEquiv.EqOnSource e.toPartialEquiv e'.toPartialEquiv :=
  Iff.rfl
#align local_homeomorph.eq_on_source_iff PartialHomeomorph.eqOnSource_iff

/-- `EqOnSource` is an equivalence relation. -/
instance eqOnSourceSetoid : Setoid (PartialHomeomorph α β) :=
  { PartialEquiv.eqOnSourceSetoid.comap toPartialEquiv with r := EqOnSource }

theorem eqOnSource_refl : e ≈ e := Setoid.refl _
#align local_homeomorph.eq_on_source_refl PartialHomeomorph.eqOnSource_refl

/-- If two partial homeomorphisms are equivalent, so are their inverses. -/
theorem EqOnSource.symm' {e e' : PartialHomeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
  PartialEquiv.EqOnSource.symm' h
#align local_homeomorph.eq_on_source.symm' PartialHomeomorph.EqOnSource.symm'

/-- Two equivalent partial homeomorphisms have the same source. -/
theorem EqOnSource.source_eq {e e' : PartialHomeomorph α β} (h : e ≈ e') : e.source = e'.source :=
  h.1
#align local_homeomorph.eq_on_source.source_eq PartialHomeomorph.EqOnSource.source_eq

/-- Two equivalent partial homeomorphisms have the same target. -/
theorem EqOnSource.target_eq {e e' : PartialHomeomorph α β} (h : e ≈ e') : e.target = e'.target :=
  h.symm'.1
#align local_homeomorph.eq_on_source.target_eq PartialHomeomorph.EqOnSource.target_eq

/-- Two equivalent partial homeomorphisms have coinciding `toFun` on the source -/
theorem EqOnSource.eqOn {e e' : PartialHomeomorph α β} (h : e ≈ e') : EqOn e e' e.source :=
  h.2
#align local_homeomorph.eq_on_source.eq_on PartialHomeomorph.EqOnSource.eqOn

/-- Two equivalent partial homeomorphisms have coinciding `invFun` on the target -/
theorem EqOnSource.symm_eqOn_target {e e' : PartialHomeomorph α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2
#align local_homeomorph.eq_on_source.symm_eq_on_target PartialHomeomorph.EqOnSource.symm_eqOn_target

/-- Composition of partial homeomorphisms respects equivalence. -/
theorem EqOnSource.trans' {e e' : PartialHomeomorph α β} {f f' : PartialHomeomorph β γ}
    (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  PartialEquiv.EqOnSource.trans' he hf
#align local_homeomorph.eq_on_source.trans' PartialHomeomorph.EqOnSource.trans'

/-- Restriction of partial homeomorphisms respects equivalence -/
theorem EqOnSource.restr {e e' : PartialHomeomorph α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s :=
  PartialEquiv.EqOnSource.restr he _
#align local_homeomorph.eq_on_source.restr PartialHomeomorph.EqOnSource.restr

/- Two equivalent partial homeomorphisms are equal when the source and target are `univ`. -/
theorem Set.EqOn.restr_eqOn_source {e e' : PartialHomeomorph α β}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source := by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine' (EqOn.trans _ h).trans _ <;> simp only [mfld_simps, eqOn_refl]
#align local_homeomorph.set.eq_on.restr_eq_on_source PartialHomeomorph.Set.EqOn.restr_eqOn_source

/-- Composition of a partial homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem self_trans_symm : e.trans e.symm ≈ PartialHomeomorph.ofSet e.source e.open_source :=
  PartialEquiv.self_trans_symm _
#align local_homeomorph.self_trans_symm PartialHomeomorph.self_trans_symm

theorem symm_trans_self : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
  e.symm.self_trans_symm
#align local_homeomorph.symm_trans_self PartialHomeomorph.symm_trans_self

theorem eq_of_eqOnSource_univ {e e' : PartialHomeomorph α β} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  toPartialEquiv_injective <| PartialEquiv.eq_of_eqOnSource_univ _ _ h s t
#align local_homeomorph.eq_of_eq_on_source_univ PartialHomeomorph.eq_of_eqOnSource_univ

section Prod

/-- The product of two partial homeomorphisms, as a partial homeomorphism on the product space. -/
@[simps! (config := mfld_cfg) toPartialEquiv apply,
  simps! (config := .lemmasOnly) source target symm_apply]
def prod (e : PartialHomeomorph α β) (e' : PartialHomeomorph γ δ) :
    PartialHomeomorph (α × γ) (β × δ) where
  open_source := e.open_source.prod e'.open_source
  open_target := e.open_target.prod e'.open_target
  continuousOn_toFun := e.continuousOn.prod_map e'.continuousOn
  continuousOn_invFun := e.continuousOn_symm.prod_map e'.continuousOn_symm
  toPartialEquiv := e.toPartialEquiv.prod e'.toPartialEquiv
#align local_homeomorph.prod PartialHomeomorph.prod

@[simp, mfld_simps]
theorem prod_symm (e : PartialHomeomorph α β) (e' : PartialHomeomorph γ δ) :
    (e.prod e').symm = e.symm.prod e'.symm :=
  rfl
#align local_homeomorph.prod_symm PartialHomeomorph.prod_symm

@[simp]
theorem refl_prod_refl {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] :
    (PartialHomeomorph.refl α).prod (PartialHomeomorph.refl β) = PartialHomeomorph.refl (α × β) :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ
#align local_homeomorph.refl_prod_refl PartialHomeomorph.refl_prod_refl

@[simp, mfld_simps]
theorem prod_trans {η : Type*} {ε : Type*} [TopologicalSpace η] [TopologicalSpace ε]
    (e : PartialHomeomorph α β) (f : PartialHomeomorph β γ) (e' : PartialHomeomorph δ η)
    (f' : PartialHomeomorph η ε) : (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
  toPartialEquiv_injective <| e.1.prod_trans ..
#align local_homeomorph.prod_trans PartialHomeomorph.prod_trans

theorem prod_eq_prod_of_nonempty {e₁ e₁' : PartialHomeomorph α β} {e₂ e₂' : PartialHomeomorph γ δ}
    (h : (e₁.prod e₂).source.Nonempty) : e₁.prod e₂ = e₁'.prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  haveI : Nonempty α := ⟨x⟩
  haveI : Nonempty β := ⟨e₁ x⟩
  haveI : Nonempty γ := ⟨y⟩
  haveI : Nonempty δ := ⟨e₂ y⟩
  simp_rw [PartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const,
    and_assoc, and_left_comm]
#align local_homeomorph.prod_eq_prod_of_nonempty PartialHomeomorph.prod_eq_prod_of_nonempty

theorem prod_eq_prod_of_nonempty' {e₁ e₁' : PartialHomeomorph α β} {e₂ e₂' : PartialHomeomorph γ δ}
    (h : (e₁'.prod e₂').source.Nonempty) : e₁.prod e₂ = e₁'.prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ e₂']
#align local_homeomorph.prod_eq_prod_of_nonempty' PartialHomeomorph.prod_eq_prod_of_nonempty'

end Prod

section Piecewise

/-- Combine two `PartialHomeomorph`s using `Set.piecewise`. The source of the new
`PartialHomeomorph` is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for
target.  The function sends `e.source ∩ s` to `e.target ∩ t` using `e` and
`e'.source \ s` to `e'.target \ t` using `e'`, and similarly for the inverse function.
To ensure the maps `toFun` and `invFun` are inverse of each other on the new `source` and `target`,
the definition assumes that the sets `s` and `t` are related both by `e.is_image` and `e'.is_image`.
To ensure that the new maps are continuous on `source`/`target`, it also assumes that `e.source` and
`e'.source` meet `frontier s` on the same set and `e x = e' x` on this intersection. -/
@[simps! (config := .asFn) toPartialEquiv apply]
def piecewise (e e' : PartialHomeomorph α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : PartialHomeomorph α β where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs Heq
  continuousOn_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq)
#align local_homeomorph.piecewise PartialHomeomorph.piecewise

@[simp]
theorem symm_piecewise (e e' : PartialHomeomorph α β) {s : Set α} {t : Set β}
    [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq) :=
  rfl
#align local_homeomorph.symm_piecewise PartialHomeomorph.symm_piecewise

/-- Combine two `PartialHomeomorph`s with disjoint sources and disjoint targets. We reuse
`PartialHomeomorph.piecewise` then override `toPartialEquiv` to `PartialEquiv.disjointUnion`.
This way we have better definitional equalities for `source` and `target`. -/
def disjointUnion (e e' : PartialHomeomorph α β) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : PartialHomeomorph α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eqOn_empty _ _)).replaceEquiv
    (e.toPartialEquiv.disjointUnion e'.toPartialEquiv Hs Ht)
    (PartialEquiv.disjointUnion_eq_piecewise _ _ _ _).symm
#align local_homeomorph.disjoint_union PartialHomeomorph.disjointUnion

/-- Combine a family of local homeomorphisms with disjoint sources/targets -/
@[simps! source target]
noncomputable def disjoint_iUnion {I : Type _} [Nonempty I]
    (h : I → PartialHomeomorph α β)
    (disj₁ : Pairwise (Disjoint on fun i : I => (h i).source))
    (disj₂ : Pairwise (Disjoint on fun i : I => (h i).target)) : PartialHomeomorph α β := by
  have opn_src : IsOpen (⋃ i, (h i).source) := isOpen_iUnion fun i => (h i).open_source
  have opn_tgt : IsOpen (⋃ i, (h i).target) := isOpen_iUnion fun i => (h i).open_target
  refine
    ⟨PartialEquiv.disjoint_iUnion (fun i => (h i).toPartialEquiv) disj₁ disj₂, opn_src, opn_tgt, ?_, ?_⟩
  · simp only [PartialEquiv.disjoint_iUnion, opn_src.continuousOn_iff, Set.mem_iUnion]
    rintro x ⟨i, hx⟩
    refine ((h i).continuousAt hx).congr
      (Filter.eventuallyEq_of_mem ((h i).open_source.mem_nhds hx) ?_)
    intro x' hx'
    simp [disj₁.disjoint_inv_iUnion_eq hx']
  · simp only [PartialEquiv.disjoint_iUnion, opn_tgt.continuousOn_iff, Set.mem_iUnion]
    rintro y ⟨i, hy⟩
    refine ((h i).symm.continuousAt hy).congr
      (Filter.eventuallyEq_of_mem ((h i).open_target.mem_nhds hy) ?_)
    intro y' hy'
    simp [disj₂.disjoint_inv_iUnion_eq hy']

theorem disjoint_iUnion_apply' {I : Type _} [Nonempty I]
    (h : I → PartialHomeomorph α β) (i : I) (disj₁ disj₂)
    (x : α) (hx : x ∈ (h i).source) : disjoint_iUnion h disj₁ disj₂ x = h i x :=
  PartialEquiv.disjoint_iUnion_apply' (fun i => (h i).toPartialEquiv) i disj₁ disj₂ x hx

theorem disjoint_iUnion_symm_apply' {I : Type _} [Nonempty I]
    (h : I → PartialHomeomorph α β) (i : I) (disj₁ disj₂)
    (y : β) (hy : y ∈ (h i).target) : (disjoint_iUnion h disj₁ disj₂).symm y = (h i).symm y :=
  PartialEquiv.disjoint_iUnion_symm_apply' (fun i => (h i).toPartialEquiv) i disj₁ disj₂ y hy

end Piecewise

section Pi

variable {ι : Type*} [Fintype ι] {Xi Yi : ι → Type*} [∀ i, TopologicalSpace (Xi i)]
  [∀ i, TopologicalSpace (Yi i)] (ei : ∀ i, PartialHomeomorph (Xi i) (Yi i))

/-- The product of a finite family of `PartialHomeomorph`s. -/
@[simps toPartialEquiv]
def pi : PartialHomeomorph (∀ i, Xi i) (∀ i, Yi i) where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuousOn_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
#align local_homeomorph.pi PartialHomeomorph.pi

end Pi

section Continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuousWithinAt_iff_continuousWithinAt_comp_right {f : β → γ} {s : Set β} {x : β}
    (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhdsWithin_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]
#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_right PartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_right

/-- Continuity at a point can be read under right composition with a partial homeomorphism, if the
point is in its target -/
theorem continuousAt_iff_continuousAt_comp_right {f : β → γ} {x : β} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuousWithinAt_univ, e.continuousWithinAt_iff_continuousWithinAt_comp_right h,
    preimage_univ, continuousWithinAt_univ]
#align local_homeomorph.continuous_at_iff_continuous_at_comp_right PartialHomeomorph.continuousAt_iff_continuousAt_comp_right

/-- A function is continuous on a set if and only if its composition with a partial homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_right {f : β → γ} {s : Set β} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) := by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, ball_image_iff]
  refine' forall₂_congr fun x hx => _
  rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))
#align local_homeomorph.continuous_on_iff_continuous_on_comp_right PartialHomeomorph.continuousOn_iff_continuousOn_comp_right

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
theorem continuousWithinAt_iff_continuousWithinAt_comp_left {f : γ → α} {s : Set γ} {x : γ}
    (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x := by
  refine' ⟨(e.continuousAt hx).comp_continuousWithinAt, fun fe_cont => _⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])
#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left PartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_left

/-- Continuity at a point can be read under left composition with a partial homeomorphism if a
neighborhood of the initial point is sent to the source of the partial homeomorphism-/
theorem continuousAt_iff_continuousAt_comp_left {f : γ → α} {x : γ} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x := by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ, ← continuousWithinAt_univ,
    e.continuousWithinAt_iff_continuousWithinAt_comp_left hx h']
#align local_homeomorph.continuous_at_iff_continuous_at_comp_left PartialHomeomorph.continuousAt_iff_continuousAt_comp_left

/-- A function is continuous on a set if and only if its composition with a partial homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_left {f : γ → α} {s : Set γ} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun _x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)
#align local_homeomorph.continuous_on_iff_continuous_on_comp_left PartialHomeomorph.continuousOn_iff_continuousOn_comp_left

/-- A function is continuous if and only if its composition with a partial homeomorphism
on the left is continuous and its image is contained in the source. -/
theorem continuous_iff_continuous_comp_left {f : γ → α} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) := by
  simp only [continuous_iff_continuousOn_univ]
  exact e.continuousOn_iff_continuousOn_comp_left (Eq.symm h).subset
#align local_homeomorph.continuous_iff_continuous_comp_left PartialHomeomorph.continuous_iff_continuous_comp_left

end Continuity

/-- The homeomorphism obtained by restricting a `PartialHomeomorph` to a subset of the source. -/
@[simps]
def homeomorphOfImageSubsetSource {s : Set α} {t : Set β} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  have h₁ : MapsTo e s t := mapsTo'.2 ht.subset
  have h₂ : t ⊆ e.target := ht ▸ e.image_source_eq_target ▸ image_subset e hs
  have h₃ : MapsTo e.symm t s := ht ▸ ball_image_iff.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
    right_inv := fun b => Subtype.eq <| e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).restrict_mapsTo h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).restrict_mapsTo h₃ }
#align local_homeomorph.homeomorph_of_image_subset_source PartialHomeomorph.homeomorphOfImageSubsetSource

/-- A partial homeomorphism defines a homeomorphism between its source and target. -/
@[simps!] -- porting note: new `simps`
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
#align local_homeomorph.to_homeomorph_source_target PartialHomeomorph.toHomeomorphSourceTarget

theorem secondCountableTopology_source [SecondCountableTopology β] :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology
#align local_homeomorph.second_countable_topology_source PartialHomeomorph.secondCountableTopology_source

theorem nhds_eq_comap_inf_principal {x} (hx : x ∈ e.source) :
    𝓝 x = comap e (𝓝 (e x)) ⊓ 𝓟 e.source := by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2, ← map_nhds_subtype_val, ← map_comap_setCoe_val,
    e.toHomeomorphSourceTarget.nhds_eq_comap, nhds_subtype_eq_comap]
  simp only [(· ∘ ·), toHomeomorphSourceTarget_apply_coe, comap_comap]

/-- If a partial homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps (config := mfld_cfg) apply symm_apply] -- porting note: todo: add a `PartialEquiv` version
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set α)) (h' : e.target = univ) :
    α ≃ₜ β where
  toFun := e
  invFun := e.symm
  left_inv x :=
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv x :=
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuous_iff_continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuous_iff_continuousOn_univ, h'] using e.continuousOn_symm
#align local_homeomorph.to_homeomorph_of_source_eq_univ_target_eq_univ PartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv

theorem openEmbedding_restrict : OpenEmbedding (e.source.restrict e) := by
  refine openEmbedding_of_continuous_injective_open (e.continuousOn.comp_continuous
    continuous_subtype_val Subtype.prop) e.injOn.injective fun V hV ↦ ?_
  rw [Set.restrict_eq, Set.image_comp]
  exact e.isOpen_image_of_subset_source (e.open_source.isOpenMap_subtype_val V hV)
    fun _ ⟨x, _, h⟩ ↦ h ▸ x.2

/-- A partial homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.
The converse is also true; see `OpenEmbedding.toPartialHomeomorph`. -/
theorem to_openEmbedding (h : e.source = Set.univ) : OpenEmbedding e :=
  e.openEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ α).symm.openEmbedding

#align local_homeomorph.to_open_embedding PartialHomeomorph.to_openEmbedding

end PartialHomeomorph

namespace Homeomorph

variable (e : α ≃ₜ β) (e' : β ≃ₜ γ)

/- Register as simp lemmas that the fields of a partial homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/
@[simp, mfld_simps]
theorem refl_toPartialHomeomorph :
    (Homeomorph.refl α).toPartialHomeomorph = PartialHomeomorph.refl α :=
  rfl
#align homeomorph.refl_to_local_homeomorph Homeomorph.refl_toPartialHomeomorph

@[simp, mfld_simps]
theorem symm_toPartialHomeomorph : e.symm.toPartialHomeomorph = e.toPartialHomeomorph.symm :=
  rfl
#align homeomorph.symm_to_local_homeomorph Homeomorph.symm_toPartialHomeomorph

@[simp, mfld_simps]
theorem trans_toPartialHomeomorph :
    (e.trans e').toPartialHomeomorph = e.toPartialHomeomorph.trans e'.toPartialHomeomorph :=
  PartialHomeomorph.toPartialEquiv_injective <| Equiv.trans_toPartialEquiv _ _
#align homeomorph.trans_to_local_homeomorph Homeomorph.trans_toPartialHomeomorph

/-- Precompose a partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! (config := .asFn)]
def transPartialHomeomorph (e : α ≃ₜ β) (f' : PartialHomeomorph β γ) : PartialHomeomorph α γ where
  toPartialEquiv := e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source := f'.open_source.preimage e.continuous
  open_target := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn
#align homeomorph.trans_local_homeomorph Homeomorph.transPartialHomeomorph

theorem transPartialHomeomorph_eq_trans (e : α ≃ₜ β) (f' : PartialHomeomorph β γ) :
    e.transPartialHomeomorph f' = e.toPartialHomeomorph.trans f' :=
  PartialHomeomorph.toPartialEquiv_injective <| Equiv.transPartialEquiv_eq_trans _ _
#align homeomorph.trans_local_homeomorph_eq_trans Homeomorph.transPartialHomeomorph_eq_trans

@[simp, mfld_simps]
theorem transPartialHomeomorph_trans (e : α ≃ₜ β) (f : PartialHomeomorph β γ)
    (f' : PartialHomeomorph γ δ) :
    (e.transPartialHomeomorph f).trans f' = e.transPartialHomeomorph (f.trans f') := by
  simp only [transPartialHomeomorph_eq_trans, PartialHomeomorph.trans_assoc]

@[simp, mfld_simps]
theorem trans_transPartialHomeomorph (e : α ≃ₜ β) (e' : β ≃ₜ γ) (f'' : PartialHomeomorph γ δ) :
    (e.trans e').transPartialHomeomorph f'' =
      e.transPartialHomeomorph (e'.transPartialHomeomorph f'') := by
  simp only [transPartialHomeomorph_eq_trans, PartialHomeomorph.trans_assoc,
    trans_toPartialHomeomorph]

end Homeomorph

namespace OpenEmbedding

variable (f : α → β) (h : OpenEmbedding f)

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a partial homeomorphism
whose source is all of `α`. The converse is also true; see `PartialHomeomorph.to_openEmbedding`. -/
@[simps! (config := mfld_cfg) apply source target]
noncomputable def toPartialHomeomorph [Nonempty α] : PartialHomeomorph α β :=
  PartialHomeomorph.ofContinuousOpen ((h.toEmbedding.inj.injOn univ).toPartialEquiv _ _)
    h.continuous.continuousOn h.isOpenMap isOpen_univ
#align open_embedding.to_local_homeomorph OpenEmbedding.toPartialHomeomorph

variable [Nonempty α]

lemma toPartialHomeomorph_left_inv {x : α} : (h.toPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.left_inv]
  exact Set.mem_univ _

lemma toPartialHomeomorph_right_inv {x : β} (hx : x ∈ Set.range f) :
    f ((h.toPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.right_inv]
  rwa [toPartialHomeomorph_target]

/-- An open embedding of `α` into `β` interpreted as a local homeomorphism on the set `s`.
  This is equivalent to `(toPartialHomeomorph e h).restrOpen s hs` but with better
  definitional equalities -/
@[simps! (config := mfld_cfg) apply source target]
noncomputable def toPartialHomeomorphOn [Nonempty α] (s : Set α) (hs : IsOpen s) :
    PartialHomeomorph α β :=
  PartialHomeomorph.ofContinuousOpen ((h.toEmbedding.inj.injOn s).toPartialEquiv _ _)
    h.continuous.continuousOn h.isOpenMap hs

@[simp] lemma toPartialHomeomorphOn_univ [Nonempty α] :
    toPartialHomeomorphOn f h univ isOpen_univ = toPartialHomeomorph f h := rfl

end OpenEmbedding

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (s : Opens α) [Nonempty s]

/-- The inclusion of an open subset `s` of a space `α` into `α` is a partial homeomorphism from the
subtype `s` to `α`. -/
noncomputable def partialHomeomorphSubtypeCoe : PartialHomeomorph s α :=
  OpenEmbedding.toPartialHomeomorph _ s.2.openEmbedding_subtype_val
#align topological_space.opens.local_homeomorph_subtype_coe TopologicalSpace.Opens.partialHomeomorphSubtypeCoe

@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_coe : (s.partialHomeomorphSubtypeCoe : s → α) = (↑) :=
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_coe TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_coe

@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_source : s.partialHomeomorphSubtypeCoe.source = Set.univ :=
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_source TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_source

@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_target : s.partialHomeomorphSubtypeCoe.target = s := by
  simp only [partialHomeomorphSubtypeCoe, Subtype.range_coe_subtype, mfld_simps]
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_target TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_target

end TopologicalSpace.Opens

namespace PartialHomeomorph

/-- Postcompose a partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! (config := .asFn)]
def transHomeomorph (e : PartialHomeomorph α β) (f' : β ≃ₜ γ) : PartialHomeomorph α γ where
  toPartialEquiv := e.toPartialEquiv.transEquiv f'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id
#align local_homeomorph.trans_homeomorph PartialHomeomorph.transHomeomorph

theorem transHomeomorph_eq_trans (e : PartialHomeomorph α β) (f' : β ≃ₜ γ) :
    e.transHomeomorph f' = e.trans f'.toPartialHomeomorph :=
  toPartialEquiv_injective <| PartialEquiv.transEquiv_eq_trans _ _
#align local_homeomorph.trans_equiv_eq_trans PartialHomeomorph.transHomeomorph_eq_trans

@[simp, mfld_simps]
theorem transHomeomorph_transHomeomorph (e : PartialHomeomorph α β) (f' : β ≃ₜ γ) (f'' : γ ≃ₜ δ) :
    (e.transHomeomorph f').transHomeomorph f'' = e.transHomeomorph (f'.trans f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toPartialHomeomorph]

@[simp, mfld_simps]
theorem trans_transHomeomorph (e : PartialHomeomorph α β) (e' : PartialHomeomorph β γ)
    (f'' : γ ≃ₜ δ) :
    (e.trans e').transHomeomorph f'' = e.trans (e'.transHomeomorph f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toPartialHomeomorph]

open TopologicalSpace

variable (e : PartialHomeomorph α β)

variable (s : Opens α) [Nonempty s]

/-- The restriction of a partial homeomorphism `e` to an open subset `s` of the domain type
produces a partial homeomorphism whose domain is the subtype `s`. -/
noncomputable def subtypeRestr : PartialHomeomorph s β :=
  s.partialHomeomorphSubtypeCoe.trans e
#align local_homeomorph.subtype_restr PartialHomeomorph.subtypeRestr

theorem subtypeRestr_def : e.subtypeRestr s = s.partialHomeomorphSubtypeCoe.trans e :=
  rfl
#align local_homeomorph.subtype_restr_def PartialHomeomorph.subtypeRestr_def

@[simp, mfld_simps]
theorem subtypeRestr_coe :
    ((e.subtypeRestr s : PartialHomeomorph s β) : s → β) = Set.restrict ↑s (e : α → β) :=
  rfl
#align local_homeomorph.subtype_restr_coe PartialHomeomorph.subtypeRestr_coe

@[simp, mfld_simps]
theorem subtypeRestr_source : (e.subtypeRestr s).source = (↑) ⁻¹' e.source := by
  simp only [subtypeRestr_def, mfld_simps]
#align local_homeomorph.subtype_restr_source PartialHomeomorph.subtypeRestr_source

variable {s}

theorem map_subtype_source {x : s} (hxe : (x : α) ∈ e.source): e x ∈ (e.subtypeRestr s).target := by
  refine' ⟨e.map_source hxe, _⟩
  rw [s.partialHomeomorphSubtypeCoe_target, mem_preimage, e.leftInvOn hxe]
  exact x.prop
#align local_homeomorph.map_subtype_source PartialHomeomorph.map_subtype_source

variable (s)

/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : PartialHomeomorph α β) :
    (f.subtypeRestr s).symm.trans (f'.subtypeRestr s) ≈
      (f.symm.trans f').restr (f.target ∩ f.symm ⁻¹' s) := by
  simp only [subtypeRestr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.isOpen_inter_preimage_symm s.2
  rw [← ofSet_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine' EqOnSource.trans' _ (eqOnSource_refl _)
  -- f' has been eliminated !!!
  have sets_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s :=
    by mfld_set_tac
  have openness₂ : IsOpen (s : Set α) := s.2
  rw [ofSet_trans', sets_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine' EqOnSource.trans' (eqOnSource_refl _) _
  -- f has been eliminated !!!
  refine' Setoid.trans (symm_trans_self s.partialHomeomorphSubtypeCoe) _
  simp only [mfld_simps, Setoid.refl]
#align local_homeomorph.subtype_restr_symm_trans_subtype_restr PartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr

theorem subtypeRestr_symm_eqOn (U : Opens α) [Nonempty U] :
    EqOn e.symm (Subtype.val ∘ (e.subtypeRestr U).symm) (e.subtypeRestr U).target := by
  intro y hy
  rw [eq_comm, eq_symm_apply _ _ hy.1]
  · change restrict _ e _ = _
    rw [← subtypeRestr_coe, (e.subtypeRestr U).right_inv hy]
  · have := map_target _ hy; rwa [subtypeRestr_source] at this

theorem subtypeRestr_symm_eqOn_of_le {U V : Opens α} [Nonempty U] [Nonempty V] (hUV : U ≤ V) :
    EqOn (e.subtypeRestr V).symm (Set.inclusion hUV ∘ (e.subtypeRestr U).symm)
      (e.subtypeRestr U).target := by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [PartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y ∈ V.partialHomeomorphSubtypeCoe.target := by
    rw [Opens.partialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine' V.partialHomeomorphSubtypeCoe.injOn _ trivial _
  · rw [← PartialHomeomorph.symm_target]
    apply PartialHomeomorph.map_source
    rw [PartialHomeomorph.symm_source]
    exact hyV
  · rw [V.partialHomeomorphSubtypeCoe.right_inv hyV]
    show _ = U.partialHomeomorphSubtypeCoe _
    rw [U.partialHomeomorphSubtypeCoe.right_inv hy.2]
#align local_homeomorph.subtype_restr_symm_eq_on_of_le PartialHomeomorph.subtypeRestr_symm_eqOn_of_le

section Discrete

theorem OpenEmbedding.prodMkRight [DiscreteTopology β] (b : β) :
    OpenEmbedding ((·, b) : α → α × β) where
  open_range := by convert isOpen_univ.prod (isOpen_discrete {b}); ext; simp
  toEmbedding := Function.LeftInverse.embedding (f := Prod.fst) (by simp [LeftInverse])
    continuous_fst (by continuity)


theorem OpenEmbedding.prodMkLeft [DiscreteTopology β] (b : β) :
    OpenEmbedding ((b, ·) : α → β × α) where
  open_range := by convert (isOpen_discrete {b}).prod isOpen_univ; ext; simp
  toEmbedding := Function.LeftInverse.embedding (f := Prod.snd) (by simp [LeftInverse])
    continuous_snd (by continuity)

end Discrete

end PartialHomeomorph

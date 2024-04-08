/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

-/

import Mathlib.Algebra.Module.LinearMap.Pointwise
import Mathlib.Data.Setoid.Partition
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Subgroup.Actions

/-! # Blocks

Given `SMul G X`, an action of a type `G` on a type `X`, we define

- the predicate `MulAction.IsBlock G B` states that `B : Set X` is a block,
which means that the sets `g • B`, for `g ∈ G`, are pairwise disjoint.
Under `Group G` and `MulAction G X`, this is equivalent to the classical
definition `MulAction.IsBlock.def_one`

- a bunch of lemmas that give example of “trivial” blocks : ⊥, ⊤, singletons, orbits…

The non-existence of nontrivial blocks is the definition of primitive actions.

-/

open scoped BigOperators Pointwise

namespace MulAction

section SMul

variable (G : Type _) {X : Type _} [SMul G X]

/-- A fixed block is a fully invariant subset -/
def IsFixedBlock (B : Set X) := ∀ g : G, g • B = B

/-- An invariant block is a set which is stable under `SMul.smul` -/
def IsInvariantBlock (B : Set X) := ∀ g : G, g • B ≤ B

/-- A trivial block is a subsingleton or ⊤ (it is not necessarily a block…) -/
def IsTrivialBlock (B : Set X) := B.Subsingleton ∨ B = ⊤

/-- A block is a set all of whose translates are pairwise disjoint -/
def IsBlock (B : Set X) := (Set.range fun g : G => g • B).PairwiseDisjoint id

variable {G}

/-- A set B is a block iff for all g, g',
the sets g • B and g' • B are either equal or disjoint -/
theorem IsBlock.def {B : Set X} :
    IsBlock G B ↔ ∀ g g' : G, g • B = g' • B ∨ Disjoint (g • B) (g' • B) := by
  constructor
  · intro hB g g'
    by_cases h : g • B = g' • B
    · refine' Or.intro_left _ h
    · apply Or.intro_right
      exact hB (Set.mem_range_self g) (Set.mem_range_self g') h
  · intro hB
    unfold IsBlock
    intro C hC C' hC'
    obtain ⟨g, rfl⟩ := hC
    obtain ⟨g', rfl⟩ := hC'
    intro hgg'
    cases hB g g' with
    | inl h => exfalso; exact hgg' h
    | inr h => exact h

/-- Alternate definition of a block -/
theorem IsBlock.mk_notempty {B : Set X} :
    IsBlock G B ↔ ∀ g g' : G, g • B ∩ g' • B ≠ ∅ → g • B = g' • B := by
  rw [IsBlock.def]
  apply forall_congr'; intro g
  apply forall_congr'; intro g'
  rw [Set.disjoint_iff_inter_eq_empty]
  exact or_iff_not_imp_right
#align mul_action.is_block.mk_notempty MulAction.IsBlock.mk_notempty

/-- A fixed block is a block -/
theorem IsFixedBlock.isBlock {B : Set X} (hfB : IsFixedBlock G B) :
    IsBlock G B := by
  rw [IsBlock.def]
  intro g g'
  apply Or.intro_left
  rw [hfB g, hfB g']

variable (X)

/-- The empty set is a block -/
theorem isBlock_bot : IsBlock G (⊥ : Set X) := by
  rw [IsBlock.def]
  intro g g'; apply Or.intro_left
  simp only [Set.bot_eq_empty, Set.smul_set_empty]

variable {X}

theorem isBlock_singleton (a : X) :
    IsBlock G ({a} : Set X) := by
  rw [IsBlock.def]
  intro g g'
  simp only [Set.smul_set_singleton, Set.singleton_eq_singleton_iff, Set.disjoint_singleton, Ne.def]
  apply em

/-- Subsingletons are (trivial) blocks -/
theorem isBlock_subsingleton {B : Set X} (hB : B.Subsingleton) :
    IsBlock G B := by
  cases Set.Subsingleton.eq_empty_or_singleton hB with
  | inl h => rw [h]; exact isBlock_bot X
  | inr h =>
    obtain ⟨a, ha⟩ := h
    rw [ha]
    exact isBlock_singleton a


end SMul

section Group

variable {G : Type _} [Group G] {X : Type _} [MulAction G X]

theorem IsTrivialBlock.smul {B : Set X} (g : G) (hB : IsTrivialBlock B) :
    IsTrivialBlock (g • B) := by
  cases hB with
  | inl hB =>
    left
    apply Set.Subsingleton.image hB
  | inr hB =>
    apply Or.intro_right
    rw [hB, eq_top_iff]
    intro x _
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact Set.mem_univ _

theorem IsTrivialBlock.smul_iff {B : Set X} (g : G) :
    IsTrivialBlock (g • B) ↔ IsTrivialBlock B := by
  constructor
  · intro hg
    convert hg.smul g⁻¹
    simp only [inv_smul_smul]
  exact IsTrivialBlock.smul g

theorem IsBlock.def_one {B : Set X} :
    IsBlock G B ↔ ∀ g : G, g • B = B ∨ Disjoint (g • B) B := by
  rw [IsBlock.def]
  constructor
  · intro hB g
    simpa only [one_smul] using hB g 1
  · intro hB g g'
    cases hB (g'⁻¹ * g) with
    | inl h =>
      apply Or.intro_left
      rw [← inv_inv g', eq_inv_smul_iff, smul_smul]
      exact h
    | inr h =>
      apply Or.intro_right
      rw [Set.disjoint_iff] at h ⊢
      rintro x ⟨hx, hx'⟩
      simp only [Set.mem_empty_iff_false]
      suffices g'⁻¹ • x ∈ (g'⁻¹ * g) • B ⊓ B by
        apply h this
      simp only [Set.inf_eq_inter, Set.mem_inter_iff,
        ← Set.mem_smul_set_iff_inv_smul_mem, ← smul_smul, smul_inv_smul]
      exact ⟨hx, hx'⟩

theorem IsBlock.mk_notempty_one {B : Set X} :
    IsBlock G B ↔ ∀ g : G, g • B ∩ B ≠ ∅ → g • B = B := by
  rw [IsBlock.def_one]
  apply forall_congr'
  intro g
  rw [Set.disjoint_iff_inter_eq_empty]
  exact or_iff_not_imp_right

theorem IsBlock.mk_mem {B : Set X} :
    IsBlock G B ↔
      ∀ (g : G) (a : X) (_ : a ∈ B) (_ : g • a ∈ B), g • B = B := by
  rw [IsBlock.mk_notempty_one]
  simp_rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def]
  simp_rw [Set.mem_inter_iff]
  simp_rw [exists_imp]
  simp_rw [and_imp]
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro H g a ha hga
    rw [← eq_inv_smul_iff]; apply symm
    apply H g⁻¹ a _ ha
    rw [inv_inv]
    exact hga
  · intro H g a ha hga
    rw [← eq_inv_smul_iff]
    apply symm
    exact H g⁻¹ a hga ha

theorem IsBlock.def_mem {B : Set X} (hB : IsBlock G B) {a : X} {g : G} :
    a ∈ B → g • a ∈ B → g • B = B :=
  IsBlock.mk_mem.mp hB g a

theorem IsBlock.mk_subset {B : Set X} :
    IsBlock G B ↔ ∀ {g : G} {b : X} (_ : b ∈ B) (_ : b ∈ g • B), g • B ≤ B := by
  constructor
  · intro hB g b hb hgb
    rw [Set.le_iff_subset, Set.set_smul_subset_iff,
      IsBlock.def_mem hB hb (Set.mem_smul_set_iff_inv_smul_mem.mp hgb)]
  · rw [IsBlock.mk_notempty_one]
    intro hB g hg
    rw [← Set.nonempty_iff_ne_empty] at hg
    obtain ⟨b : X, hb' : b ∈ g • B, hb : b ∈ B⟩ := Set.nonempty_def.mp hg
    apply le_antisymm
    · exact hB hb hb'
    suffices g⁻¹ • B ≤ B by
      rw [Set.le_iff_subset] at this ⊢
      rw [← inv_inv g, ← Set.set_smul_subset_iff]
      exact this
    exact hB (Set.mem_smul_set_iff_inv_smul_mem.mp hb')
      (Set.smul_mem_smul_set_iff.mpr hb)

/-- An invariant block is a block -/
theorem IsInvariantBlock.isBlock {B : Set X} (hfB : IsInvariantBlock G B) :
    IsBlock G B := by
  rw [IsBlock.def_one]
  intro g
  left
  apply le_antisymm
  exact hfB g
  · intro x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    apply hfB g⁻¹
    rw [Set.smul_mem_smul_set_iff]; exact hx

/-- An orbit is a block -/
theorem isBlock_of_orbit (a : X) : IsBlock G (orbit G a) := by
  apply IsFixedBlock.isBlock
  exact fun g ↦ smul_orbit g a

variable (X)

/-- The full set is a (trivial) block -/
theorem isBlock_top : IsBlock G (⊤ : Set X) := by
  apply IsFixedBlock.isBlock
  intro g
  simp only [Set.top_eq_univ, Set.smul_set_univ]

variable {X}

/-- Is B is a block for an action G, it is a block for the action of any subgroup of G -/
theorem IsBlock.subgroup {H : Subgroup G} {B : Set X} (hfB : IsBlock G B) :
    IsBlock H B := by
  rw [IsBlock.def_one]
  rintro ⟨g, _⟩
  simpa only using IsBlock.def_one.mp hfB g

-- TODO: Generalize to φ : H → G
theorem IsBlock.preimage {H Y : Type _} [Group H] [MulAction H Y]
    {φ : H →* G} (j : Y →ₑ[φ] X) {B : Set X} (hB : IsBlock G B) :
    IsBlock H (j ⁻¹' B) := by
  rw [IsBlock.def_one]
  intro g
  cases' IsBlock.def_one.mp hB (φ g) with heq hdis
  · left
    rw [← preimage_smul_setₛₗ Y X φ j (Group.isUnit g), heq]
  · right
    rw [← preimage_smul_setₛₗ Y X φ j (Group.isUnit g)]
    exact Disjoint.preimage _ hdis

theorem IsBlock_image {H Y : Type _} [Group H] [MulAction H Y]
    {φ : G →* H} (j : X →ₑ[φ] Y)
    (hφ : Function.Surjective φ) (hj : Function.Injective j)
    {B : Set X} (hB : IsBlock G B) :
    IsBlock H (j '' B) := by
  rw [IsBlock.def]
  intro h h'
  obtain ⟨g, rfl⟩ := hφ h
  obtain ⟨g', rfl⟩ := hφ h'
  simp only [← image_smul_setₛₗ X Y φ j]
  cases' IsBlock.def.mp hB g g' with h h
  · left; rw [h]
  · right; exact Set.disjoint_image_of_injective hj h

theorem SubMulAction.IsBlock {C : SubMulAction G X} {B : Set X} (hB : IsBlock G B) :
    IsBlock G (Subtype.val ⁻¹' B : Set C) := by
  exact @IsBlock_preimage G _ X _ G C _ _ (MonoidHom.id G) C.inclusion B hB
#align mul_action.sub_mul_action.is_block MulAction.SubMulAction.IsBlock

theorem SubMulAction.smul_coe_eq_coe_smul {C : SubMulAction G X} {B : Set C} {g : G} :
    g • (Subtype.val '' B : Set X) = Subtype.val '' (g • B) := by
  ext; constructor
  · intro hx; obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    use g • z
    constructor
    exact ⟨z, hz, rfl⟩
    rw [SubMulAction.val_smul_of_tower]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    rw [SubMulAction.val_smul_of_tower]
    use ↑z; constructor
    exact ⟨z, hz, rfl⟩; rfl
#align mul_action.sub_mul_action.smul_coe_eq_coe_smul MulAction.SubMulAction.smul_coe_eq_coe_smul

theorem SubMulAction.IsBlock_coe {C : SubMulAction G X} {B : Set C} :
    MulAction.IsBlock G B ↔ MulAction.IsBlock G (Subtype.val '' B : Set X) :=
  by
  simp only [IsBlock.def_one]
  apply forall_congr'
  intro g
  rw [SubMulAction.smul_coe_eq_coe_smul]
  apply or_congr (Set.image_eq_image Subtype.coe_injective).symm
  simp only [Set.disjoint_iff, Set.subset_empty_iff]
  rw [←
    Set.InjOn.image_inter (Set.injOn_of_injective Subtype.coe_injective _) (Set.subset_univ _)
      (Set.subset_univ _)]
  simp only [Set.image_eq_empty]
#align mul_action.sub_mul_action.is_block_coe MulAction.SubMulAction.IsBlock_coe

theorem IsBlock.of_top_iff (B : Set X) : IsBlock G B ↔ IsBlock (⊤ : Subgroup G) B :=
  by
  simp only [IsBlock.def_one]
  constructor
  intro h g; exact h g
  intro h g; exact h ⟨g, Subgroup.mem_top g⟩
#align mul_action.is_block.of_top_iff MulAction.IsBlock.of_top_iff

theorem orbit.equal_or_disjoint (a b : X) :
    orbit G a = orbit G b ∨ Disjoint (orbit G a) (orbit G b) :=
  by
  cases' em (Disjoint (orbit G a) (orbit G b)) with h h
  · apply Or.intro_right; exact h
  apply Or.intro_left
  rw [Set.not_disjoint_iff] at h
  obtain ⟨x, hxa, hxb⟩ := h
  rw [← orbit_eq_iff] at hxa hxb
  rw [← hxa, ← hxb]
#align mul_action.orbit.equal_or_disjoint MulAction.orbit.equal_or_disjoint

/-- The intersection of two blocks is a block -/
theorem IsBlock.inter {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂) :
    IsBlock G (B₁ ∩ B₂) := by
  rw [IsBlock.def_one]
  intro g
  rw [Set.smul_set_inter]
  cases' IsBlock.def_one.mp h₁ g with h₁ h₁
  -- em (disjoint (g • B₁) B₁) with h h,
  · cases' IsBlock.def_one.mp h₂ g with h₂ h₂
    · apply Or.intro_left; rw [h₁, h₂]
    apply Or.intro_right
    apply Disjoint.inter_left'; apply Disjoint.inter_right'
    exact h₂
  · apply Or.intro_right
    apply Disjoint.inter_left; apply Disjoint.inter_right
    exact h₁
#align mul_action.is_block.inter MulAction.IsBlock.inter

/-- An intersection of blocks is a block -/
theorem IsBlock.iInter {ι : Type _} {B : ι → Set X} (hB : ∀ i : ι, IsBlock G (B i)) :
    IsBlock G (⋂ i, B i) := by
  rw [IsBlock.def_one]
  cases' em (IsEmpty ι) with hι hι
  · -- ι = ∅, block = ⊤
    suffices (⋂ i : ι, B i) = Set.univ by
      rw [this]
      exact IsBlock.def_one.mp (top_IsBlock X)
    simp only [Set.top_eq_univ, Set.iInter_eq_univ]
    intro i; exfalso; apply hι.false; exact i
  intro g
  rw [Set.smul_set_iInter]
  cases' em (∃ i : ι, Disjoint (g • B i) (B i)) with h h
  · obtain ⟨j, hj⟩ := h
    apply Or.intro_right
    refine' Disjoint.mono _ _ hj
    apply Set.iInter_subset
    apply Set.iInter_subset
  simp only [not_exists] at h
  apply Or.intro_left
  have : ∀ i : ι, g • B i = B i := fun i => Or.resolve_right (IsBlock.def_one.mp (hB i) g) (h i)
  rw [Set.iInter_congr this]
#align mul_action.is_block.Inter MulAction.IsBlock.iInter

theorem IsBlock.of_subgroup_of_conjugate {B : Set X} {H : Subgroup G} (hB : IsBlock H B) (g : G) :
    IsBlock (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) H) (g • B) :=
  by
  rw [IsBlock.def_one]
  intro h'
  obtain ⟨h, hH, hh⟩ := Subgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hh
  suffices h' • g • B = g • h • B by
    simp only [this]
    cases' IsBlock.def_one.mp hB ⟨h, hH⟩ with heq hdis
    · left; congr
    · right
      exact Set.disjoint_image_of_injective (MulAction.injective g) hdis
  suffices (h' : G) • g • B = g • h • B by
    rw [← this]; rfl
  rw [← hh]
  rw [smul_smul (g * h * g⁻¹) g B]
  rw [smul_smul g h B]
  simp only [inv_mul_cancel_right]
#align mul_action.is_block.of_subgroup_of_conjugate MulAction.IsBlock.of_subgroup_of_conjugate

/-- A translate of a block is a block -/
theorem IsBlock_of_block {B : Set X} (g : G) (hB : IsBlock G B) : IsBlock G (g • B) := by
  rw [IsBlock.of_top_iff] at hB ⊢
  suffices Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) ⊤ = ⊤ by
    rw [← this]
    exact IsBlock.of_subgroup_of_conjugate hB g
  suffices ⊤ = Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj g)) ⊤ by
    rw [this]
    refine Subgroup.map_comap_eq_self_of_surjective ?_ _
    exact MulEquiv.surjective (MulAut.conj g)
  rw [Subgroup.comap_top]
#align mul_action.is_block_of_block MulAction.IsBlock_of_block

variable (G)

/-- A block_system of X is a partition of X into blocks -/
def IsBlockSystem (B : Set (Set X)) :=
  Setoid.IsPartition B ∧ ∀ b : Set X, b ∈ B → IsBlock G b
#align mul_action.is_block_system MulAction.IsBlockSystem

variable {G}

-- The following proof is absurdly complicated !
/-- Translates of a block form a `block_system` -/
theorem IsBlockSystem.of_block [hGX : MulAction.IsPretransitive G X] {B : Set X} (hB : IsBlock G B)
    (hBe : B.Nonempty) : IsBlockSystem G (Set.range fun g : G => g • B) :=
  by
  constructor
  constructor
  · simp only [Set.mem_range, not_exists]
    intro x hx; apply Set.Nonempty.ne_empty hBe
    rw [← Set.image_eq_empty]
    exact hx
  · intro a
    obtain ⟨b : X, hb : b ∈ B⟩ := hBe
    obtain ⟨g, hab⟩ := exists_smul_eq G b a
    have hg : a ∈ g • B := by
      change a ∈ (fun b => g • b) '' B
      rw [Set.mem_image]
      use b
    use g • B
    constructor
    · simp only [Set.mem_range, exists_apply_eq_apply, exists_unique_iff_exists, exists_true_left]
      exact hg
    · simp only [Set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index,
        forall_apply_eq_imp_iff']
      intro B' g' hg' ha
      rw [← hg']
      apply symm
      apply Or.resolve_right (IsBlock.def.mp hB g g')
      rw [Set.not_disjoint_iff]
      use a
      rw [hg']
      exact ⟨hg, ha⟩
  intro b; rintro ⟨g, hg : g • B = b⟩
  rw [← hg]; exact IsBlock_of_block g hB
#align mul_action.is_block_system.of_block MulAction.IsBlockSystem.of_block

/-- Orbits of an element form a partition -/
theorem IsPartition.of_orbits : Setoid.IsPartition (Set.range fun a : X => orbit G a) := by
  constructor
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact Set.Nonempty.ne_empty (MulAction.orbit_nonempty a) ha
  intro a; use orbit G a
  constructor
  · simp only [Set.mem_range_self, mem_orbit_self, exists_unique_iff_exists, exists_true_left]
  · simp only [Set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index,
      forall_apply_eq_imp_iff']
    rintro B b ⟨rfl⟩ ha
    apply symm
    rw [orbit_eq_iff]
    exact ha
#align mul_action.is_partition.of_orbits MulAction.IsPartition.of_orbits

section Normal

/-- An orbit of a normal subgroup is a block -/
theorem orbit.IsBlock_of_normal {N : Subgroup G} (nN : Subgroup.Normal N) (a : X) :
    IsBlock G (orbit N a) := by
  rw [IsBlock.def_one]
  intro g
  suffices g • orbit N a = orbit N (g • a) by rw [this]; apply orbit.equal_or_disjoint
  change ((fun x : X => g • x) '' Set.range fun k : N => k • a) = Set.range fun k : N => k • g • a
  simp only [Set.image_smul, Set.smul_set_range]
  ext
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    suffices g * k * g⁻¹ ∈ N by
      use ⟨g * k * g⁻¹, this⟩
      change (g * k * g⁻¹) • g • a = g • k • a
      rw [smul_smul, inv_mul_cancel_right, ← smul_smul]
    apply nN.conj_mem; exact hk
  · rintro ⟨⟨k, hk⟩, rfl⟩
    suffices g⁻¹ * k * g ∈ N by
      use ⟨g⁻¹ * k * g, this⟩
      change g • (g⁻¹ * k * g) • a = k • g • a
      simp only [← mul_assoc, ← smul_smul, smul_inv_smul, inv_inv]
    convert nN.conj_mem k hk g⁻¹
    rw [inv_inv]

/-- The orbits of a normal subgroup form a block system -/
theorem IsBlockSystem.of_normal {N : Subgroup G} (nN : Subgroup.Normal N) :
    IsBlockSystem G (Set.range fun a : X => orbit N a) := by
  constructor
  · apply IsPartition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact orbit.IsBlock_of_normal nN a
#align mul_action.is_block_system.of_normal MulAction.IsBlockSystem.of_normal

end Normal

section Stabilizer

/- For transitive actions, construction of the lattice equivalence
  `stabilizer_block_equiv` between
  - blocks of `mul_action G X` containing a point a ∈ X,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/
/-- The orbit of a under a subgroup containing the stabilizer of a
 is a block -/
theorem IsBlock_of_suborbit {H : Subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
    IsBlock G (MulAction.orbit H a) :=
  by
  rw [IsBlock.mk_subset]; intro g b
  rintro ⟨h, rfl⟩
  simp
  intro hb'
  suffices g ∈ H by
    rw [← Subgroup.coe_mk H g this, ← Subgroup.smul_def]
    apply smul_orbit_subset
  rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, ← MulAction.mul_smul] at hb'
  obtain ⟨k : ↥H, hk⟩ := hb'
  simp only at hk
  rw [MulAction.mul_smul, ← smul_eq_iff_eq_inv_smul, ← inv_inv (h : G), ← smul_eq_iff_eq_inv_smul, ←
    MulAction.mul_smul, Subgroup.smul_def, ← MulAction.mul_smul] at hk
  rw [← mem_stabilizer_iff] at hk
  let hk' := hH hk
  rw [Subgroup.mul_mem_cancel_right, Subgroup.mul_mem_cancel_left] at hk'
  exact hk'
  apply Subgroup.inv_mem; exact SetLike.coe_mem h
  exact SetLike.coe_mem k
#align mul_action.is_block_of_suborbit MulAction.IsBlock_of_suborbit

/-- If B is a block containing a , then the stabilizer of B contains the stabilizer of a -/
theorem stabilizer_of_block {B : Set X} (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    stabilizer G a ≤ stabilizer G B := by
  intro g hg
  rw [mem_stabilizer_iff] at hg ⊢
  cases' IsBlock.def_one.mp hB g with h h'
  exact h
  exfalso; rw [← Set.mem_empty_iff_false a]
  simp only [disjoint_iff, Set.inf_eq_inter, Set.bot_eq_empty] at h'
  rw [← h', Set.mem_inter_iff]
  constructor
  rw [← hg]; rw [Set.smul_mem_smul_set_iff]; exact ha
  exact ha
#align mul_action.stabilizer_of_block MulAction.stabilizer_of_block

/-- A block is the orbit of a under its stabilizer -/
theorem block_of_stabilizer_of_block [htGX : IsPretransitive G X] {B : Set X} (hB : IsBlock G B)
    {a : X} (ha : a ∈ B) : MulAction.orbit (stabilizer G B) a = B :=
  by
  ext x
  constructor
  · -- rw mul_action.mem_orbit_iff, intro h,
    rintro ⟨k, rfl⟩
    let z := mem_stabilizer_iff.mp (SetLike.coe_mem k)
    rw [← Subgroup.smul_def] at z
    let zk : k • a ∈ k • B := Set.smul_mem_smul_set_iff.mpr ha
    rw [z] at zk ; exact zk
  intro hx
  obtain ⟨k, rfl⟩ := exists_smul_eq G a x
  suffices k ∈ stabilizer G B by
    exact ⟨⟨k, this⟩, rfl⟩
  rw [mem_stabilizer_iff]
  exact IsBlock.def_mem hB ha hx

/--
A subgroup containing the stabilizer of a is the stabilizer of the orbit of a under that subgroup -/
theorem stabilizer_of_block_of_stabilizer {a : X} {H : Subgroup G} (hH : stabilizer G a ≤ H) :
    stabilizer G (orbit H a) = H := by
  ext g; constructor
  · intro hg; rw [mem_stabilizer_iff] at hg
    suffices g • a ∈ orbit H a by
      rw [mem_orbit_iff] at this
      obtain ⟨k, hk⟩ := this
      rw [← Subgroup.mul_mem_cancel_left H (SetLike.coe_mem k⁻¹)]
      rw [smul_eq_iff_eq_inv_smul] at hk
      apply hH
      rw [mem_stabilizer_iff]; rw [MulAction.mul_smul]
      rw [← Subgroup.smul_def]; exact hk.symm
    rw [← hg]
    simp only [Set.smul_mem_smul_set_iff, mem_orbit_self]
  intro hg
  rw [mem_stabilizer_iff]
  rw [← Subgroup.coe_mk H g hg, ← Subgroup.smul_def]
  apply smul_orbit
#align mul_action.stabilizer_of_block_of_stabilizer MulAction.stabilizer_of_block_of_stabilizer

variable (G)

/-- Order equivalence between blocks in X containing a point a
 and subgroups of G containing the stabilizer of a (Wielandt, th. 7.5)-/
def stabilizerBlockEquiv [htGX : IsPretransitive G X] (a : X) :
    { B : Set X // a ∈ B ∧ IsBlock G B } ≃o Set.Ici (stabilizer G a)
    where
  toFun := fun ⟨B, ha, hB⟩ => ⟨stabilizer G B, stabilizer_of_block hB ha⟩
  invFun := fun ⟨H, hH⟩ => ⟨MulAction.orbit H a, MulAction.mem_orbit_self a, IsBlock_of_suborbit hH⟩
  left_inv := fun ⟨B, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (block_of_stabilizer_of_block hB ha)
  right_inv := fun ⟨H, hH⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (stabilizer_of_block_of_stabilizer hH)
  map_rel_iff' := by
    rintro ⟨B, ha, hB⟩; rintro ⟨B', ha', hB'⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Set.le_eq_subset]
    constructor
    · intro hBB'
      rw [← block_of_stabilizer_of_block hB ha]
      rw [← block_of_stabilizer_of_block hB' ha']
      rintro x ⟨k, rfl⟩
      use ⟨k, ?_⟩
      rfl
      apply hBB'; exact SetLike.coe_mem k
    · intro hBB'
      intro g
      change g ∈ stabilizer G B → g ∈ stabilizer G B'
      simp only [mem_stabilizer_iff]
      intro hgB
      apply IsBlock.def_mem hB' ha'
      apply hBB'
      rw [← hgB]
      simp_rw [Set.smul_mem_smul_set_iff]; exact ha
#align mul_action.stabilizer_block_equiv MulAction.stabilizerBlockEquiv

end Stabilizer

end Group

end MulAction

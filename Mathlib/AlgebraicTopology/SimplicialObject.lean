/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.AugmentedSimplexCategory
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Opposites

#align_import algebraic_topology.simplicial_object from "leanprover-community/mathlib"@"5ed51dc37c6b891b79314ee11a50adc2b1df6fd6"

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `SimplexCategory`.
(Similarly a cosimplicial object is functor `SimplexCategory ⥤ C`.)

Use the notation `X _[n]` in the `Simplicial` locale to obtain the `n`-th term of a
(co)simplicial object `X`, where `n` is a natural number.

Define augmented simplicial objects via the comma category construction, and show that this is
equivalent to functors `AugmentedSimplexCategoryᵒᵖ ⥤ C`.

-/

set_option autoImplicit true


open Opposite

open CategoryTheory

open CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

-- porting note: removed @[nolint has_nonempty_instance]
/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `SimplexCategory` to `C`. -/
def SimplicialObject :=
  SimplexCategoryᵒᵖ ⥤ C
#align category_theory.simplicial_object CategoryTheory.SimplicialObject

@[simps!]
instance : Category (SimplicialObject C) := by
  dsimp only [SimplicialObject]
  infer_instance

namespace SimplicialObject

set_option quotPrecheck false in
/-- `X _[n]` denotes the `n`th-term of the simplicial object X -/
scoped[Simplicial]
  notation3:1000 X " _[" n "]" =>
    (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

open Simplicial

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance

instance [HasLimits C] : HasLimits (SimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance

instance [HasColimits C] : HasColimits (SimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : SimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SimplexCategoryᵒᵖ), f.app n = g.app n) : f = g :=
  NatTrans.ext _ _ (by ext; apply h)

variable (X : SimplicialObject C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.δ i).op
#align category_theory.simplicial_object.δ CategoryTheory.SimplicialObject.δ

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.σ i).op
#align category_theory.simplicial_object.σ CategoryTheory.SimplicialObject.σ

/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso (CategoryTheory.eqToIso (by congr))
#align category_theory.simplicial_object.eq_to_iso CategoryTheory.SimplicialObject.eqToIso

@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  ext
  simp [eqToIso]
#align category_theory.simplicial_object.eq_to_iso_refl CategoryTheory.SimplicialObject.eqToIso_refl

/-- The generic case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]
#align category_theory.simplicial_object.δ_comp_δ CategoryTheory.SimplicialObject.δ_comp_δ

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ j ≫ X.δ i =
      X.δ (Fin.castSucc i) ≫
        X.δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
#align category_theory.simplicial_object.δ_comp_δ' CategoryTheory.SimplicialObject.δ_comp_δ'
@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ j.succ ≫ X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
#align category_theory.simplicial_object.δ_comp_δ'' CategoryTheory.SimplicialObject.δ_comp_δ''

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ (Fin.castSucc i) ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]
#align category_theory.simplicial_object.δ_comp_δ_self CategoryTheory.SimplicialObject.δ_comp_δ_self

@[reassoc]
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  subst H
  rw [δ_comp_δ_self]
#align category_theory.simplicial_object.δ_comp_δ_self' CategoryTheory.SimplicialObject.δ_comp_δ_self'

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.σ j.succ ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]
#align category_theory.simplicial_object.δ_comp_σ_of_le CategoryTheory.SimplicialObject.δ_comp_σ_of_le

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ (Fin.castSucc i) = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]
#align category_theory.simplicial_object.δ_comp_σ_self CategoryTheory.SimplicialObject.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]
#align category_theory.simplicial_object.δ_comp_σ_self' CategoryTheory.SimplicialObject.δ_comp_σ_self'

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]
#align category_theory.simplicial_object.δ_comp_σ_succ CategoryTheory.SimplicialObject.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]
#align category_theory.simplicial_object.δ_comp_σ_succ' CategoryTheory.SimplicialObject.δ_comp_σ_succ'

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.σ (Fin.castSucc j) ≫ X.δ i.succ = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]
#align category_theory.simplicial_object.δ_comp_σ_of_gt CategoryTheory.SimplicialObject.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.σ j ≫ X.δ i =
      X.δ (i.pred fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) ≫
        X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
#align category_theory.simplicial_object.δ_comp_σ_of_gt' CategoryTheory.SimplicialObject.δ_comp_σ_of_gt'

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ j ≫ X.σ (Fin.castSucc i) = X.σ i ≫ X.σ j.succ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]
#align category_theory.simplicial_object.σ_comp_σ CategoryTheory.SimplicialObject.σ_comp_σ

open Simplicial

@[reassoc (attr := simp)]
theorem δ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (op [n]) = f.app (op [n + 1]) ≫ X'.δ i :=
  f.naturality _
#align category_theory.simplicial_object.δ_naturality CategoryTheory.SimplicialObject.δ_naturality

@[reassoc (attr := simp)]
theorem σ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (op [n + 1]) = f.app (op [n]) ≫ X'.σ i :=
  f.naturality _
#align category_theory.simplicial_object.σ_naturality CategoryTheory.SimplicialObject.σ_naturality

variable (C)

/-- Functor composition induces a functor on simplicial objects. -/
@[simps!]
def whiskering (D : Type*) [Category D] : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D :=
  whiskeringRight _ _ _
#align category_theory.simplicial_object.whiskering CategoryTheory.SimplicialObject.whiskering

-- porting note: removed @[nolint has_nonempty_instance]
/-- Truncated simplicial objects. -/
def Truncated (n : ℕ) :=
  (SimplexCategory.Truncated n)ᵒᵖ ⥤ C
#align category_theory.simplicial_object.truncated CategoryTheory.SimplicialObject.Truncated

instance : Category (Truncated C n) := by
  dsimp [Truncated]
  infer_instance

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C)

/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps!]
def whiskering {n} (D : Type*) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _
#align category_theory.simplicial_object.truncated.whiskering CategoryTheory.SimplicialObject.Truncated.whiskering

variable {C}

end Truncated

section Skeleton

/-- The skeleton functor from simplicial objects to truncated simplicial objects. -/
def sk (n : ℕ) : SimplicialObject C ⥤ SimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.inclusion.op
#align category_theory.simplicial_object.sk CategoryTheory.SimplicialObject.sk

end Skeleton

variable (C)

/-- The constant simplicial object is the constant functor. -/
abbrev const : C ⥤ SimplicialObject C :=
  CategoryTheory.Functor.const _
#align category_theory.simplicial_object.const CategoryTheory.SimplicialObject.const

-- porting note: removed @[nolint has_nonempty_instance]
/-- The category of augmented simplicial objects, defined as a comma category. -/
def Augmented :=
  Comma (𝟭 (SimplicialObject C)) (const C)
#align category_theory.simplicial_object.augmented CategoryTheory.SimplicialObject.Augmented

@[simps!]
instance : Category (Augmented C) := by
  dsimp only [Augmented]
  infer_instance

variable {C}

namespace Augmented

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!]
def drop : Augmented C ⥤ SimplicialObject C :=
  Comma.fst _ _
#align category_theory.simplicial_object.augmented.drop CategoryTheory.SimplicialObject.Augmented.drop

/-- The point of the augmentation. -/
@[simps!]
def point : Augmented C ⥤ C :=
  Comma.snd _ _
#align category_theory.simplicial_object.augmented.point CategoryTheory.SimplicialObject.Augmented.point

/-- The functor from augmented objects to arrows. -/
@[simps]
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := drop.obj X _[0]
      right := point.obj X
      hom := X.hom.app _ }
  map η :=
    { left := (drop.map η).app _
      right := point.map η
      w := by
        dsimp
        rw [← NatTrans.comp_app]
        erw [η.w]
        rfl }
#align category_theory.simplicial_object.augmented.to_arrow CategoryTheory.SimplicialObject.Augmented.toArrow

/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
theorem w₀ {X Y : Augmented C} (f : X ⟶ Y) :
    (Augmented.drop.map f).app (op (SimplexCategory.mk 0)) ≫ Y.hom.app (op (SimplexCategory.mk 0)) =
      X.hom.app (op (SimplexCategory.mk 0)) ≫ Augmented.point.map f :=
  by convert congr_app f.w (op (SimplexCategory.mk 0))
#align category_theory.simplicial_object.augmented.w₀ CategoryTheory.SimplicialObject.Augmented.w₀

variable (C)

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskeringObj (D : Type*) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := ((whiskering _ _).obj F).obj (drop.obj X)
      right := F.obj (point.obj X)
      hom := whiskerRight X.hom F ≫ (Functor.constComp _ _ _).hom }
  map η :=
    { left := whiskerRight η.left _
      right := F.map η.right
      w := by
        ext
        dsimp [whiskerRight]
        simp only [Category.comp_id, ← F.map_comp, ← NatTrans.comp_app]
        erw [η.w]
        rfl }
#align category_theory.simplicial_object.augmented.whiskering_obj CategoryTheory.SimplicialObject.Augmented.whiskeringObj

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := whiskerLeft _ η
          right := η.app _
          w := by
            ext n
            dsimp
            rw [Category.comp_id, Category.comp_id, η.naturality] } }
  map_comp := fun _ _ => by ext <;> rfl
#align category_theory.simplicial_object.augmented.whiskering CategoryTheory.SimplicialObject.Augmented.whiskering

variable {C}

end Augmented

/-- Augment a simplicial object with an object. -/
@[simps]
def augment (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀)
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : ([0] : SimplexCategory) ⟶ i),
      X.map g₁.op ≫ f = X.map g₂.op ≫ f) :
    SimplicialObject.Augmented C where
  left := X
  right := X₀
  hom :=
    { app := fun i => X.map (SimplexCategory.const i.unop 0).op ≫ f
      naturality := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }
#align category_theory.simplicial_object.augment CategoryTheory.SimplicialObject.augment

-- porting note: removed @[simp] as the linter complains
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀) (w) :
    (X.augment X₀ f w).hom.app (op [0]) = f := by
  dsimp
  rw [SimplexCategory.hom_zero_zero ([0].const 0), op_id, X.map_id, Category.id_comp]
#align category_theory.simplicial_object.augment_hom_zero CategoryTheory.SimplicialObject.augment_hom_zero


-- We now want to give an equivelent definition of augmented  simplicial objects using the
-- augmented simplex category.

namespace funcToAug
def obj' (X : AugmentedSimplexCategoryᵒᵖ ⥤ C) :
    SimplicialObject.Augmented C where
    left := (SimplexCategory.augment.op ⋙ X)
    right := (X.obj (op [0]ₐ))
    hom :=
    {
      app := fun d => X.map (AugmentedSimplexCategory.map_from_initial
       (SimplexCategory.augment.obj d.unop).len ).op
      naturality := by
        intro Z Y f
        dsimp only [Functor.id_obj, Functor.comp_obj, Functor.op_obj, Functor.const_obj_obj,
          Functor.comp_map, Functor.op_map, unop_op, Functor.const_obj_map]
        rw [← X.map_comp,← op_comp,Category.comp_id]
        congr
        apply IsInitial.hom_ext  (AugmentedSimplexCategory.zero_isInitial)
    }

lemma obj'_left (X : AugmentedSimplexCategoryᵒᵖ ⥤ C) :
    (funcToAug.obj' X).left =(SimplexCategory.augment.op ⋙ X) := by
      rfl

def map' {X  Y : AugmentedSimplexCategoryᵒᵖ ⥤ C} (f : X⟶ Y) :
    funcToAug.obj' X ⟶ funcToAug.obj' Y where
    left := whiskerLeft SimplexCategory.augment.op f
    right := f.app  (op [0]ₐ)
    w := by
       ext d
       rw [Functor.id_map,NatTrans.comp_app,NatTrans.comp_app]
       simp only [Functor.id_obj, Functor.const_obj_obj, whiskerLeft_app, Functor.op_obj,
         Functor.const_map_app,funcToAug.obj',Functor.id_obj, Functor.op_obj, Functor.comp_obj,
          NatTrans.naturality]
end funcToAug

def funcToAug : (AugmentedSimplexCategoryᵒᵖ ⥤ C)⥤ SimplicialObject.Augmented C  where
   obj := funcToAug.obj'
   map := funcToAug.map'



--We now define the inverse function
namespace augToFunc
namespace obj'
open AugmentedSimplexCategory

def obj' (X: SimplicialObject.Augmented C) (Y : AugmentedSimplexCategoryᵒᵖ  ):
    C := if Y.unop.len=0 then X.right else X.left.obj (op [Y.unop.len-1])

lemma obj'_neq_zero (X: SimplicialObject.Augmented C) {Y : AugmentedSimplexCategoryᵒᵖ}
    (hY: Y.unop.len ≠ 0): (𝟭 (SimplicialObject C)).obj X.left _[AugmentedSimplexCategory.len Y.unop - 1]
        = obj'.obj' X Y := (if_neg hY).symm

lemma obj'_eq_zero (X: SimplicialObject.Augmented C) {Y : AugmentedSimplexCategoryᵒᵖ}
    (hY: Y.unop.len = 0): obj'.obj' X Y=X.right:=if_pos hY

def map'' (X: SimplicialObject.Augmented C) (Y : AugmentedSimplexCategoryᵒᵖ  )
    : obj'.obj' X Y ⟶ X.right :=  by
    by_cases h: Y.unop.len=0
    · exact eqToHom (obj'.obj'_eq_zero X h)
    · exact (eqToHom (obj'.obj'_neq_zero X h).symm) ≫  X.hom.app (op [Y.unop.len-1])

def map' (X: SimplicialObject.Augmented C) {Y Z: AugmentedSimplexCategoryᵒᵖ}
    (f: Y ⟶ Z): obj'.obj' X Y ⟶ obj'.obj' X Z :=  by
    by_cases hZ : Z.unop.len =0
    · exact  (obj'.map'' X Y)≫ (eqToHom (obj'.obj'_eq_zero X hZ).symm)
    · exact (eqToHom (obj'.obj'_neq_zero X (strict_initial' f.unop hZ)).symm)
       ≫ X.left.map (unaugment.map f.unop hZ).op  ≫ (eqToHom (obj'.obj'_neq_zero X hZ))

end obj'
open AugmentedSimplexCategory
def obj' (X: SimplicialObject.Augmented C) :
  (AugmentedSimplexCategoryᵒᵖ ⥤ C) where
   obj := obj'.obj' X
   map := obj'.map' X
   map_id := by {
    simp only
    intro Y
    unfold obj'.map' obj'.map''
    by_cases hY: Y.unop.len=0
    ·  rw [dif_pos hY,dif_pos hY,eqToHom_trans,eqToHom_refl]
    ·  rw [dif_neg hY,unop_id,unaugment.map_id,show
       (𝟙 (SimplexCategory.mk (Y.unop.len - 1))).op = 𝟙 (op (SimplexCategory.mk (Y.unop.len - 1)))
       from rfl,X.left.map_id,←eqToHom_refl,←eqToHom_refl,←eqToHom_refl,eqToHom_trans,eqToHom_trans]
       all_goals rfl
   }
   map_comp := by {
    intro Y Z W f g
    unfold obj'.map' obj'.map''
    dsimp only
    by_cases hW : W.unop.len=0
    · rw [dif_pos hW,dif_pos hW]
      by_cases hZ : Z.unop.len=0
      · rw [dif_pos hZ,dif_pos hZ]
        simp only [Functor.id_obj, eqToHom_trans, Category.assoc]
      · have hx:= X.hom.naturality (unaugment.map f.unop hZ).op
        unfold unaugment.obj at hx
        rw [dif_neg hZ,dif_neg hZ,dif_neg (strict_initial' f.unop hZ),←Category.assoc,
        ←Category.assoc,← Category.assoc,Category.assoc _ (eqToHom _) (eqToHom _),eqToHom_trans,
        eqToHom_refl,Category.comp_id,Category.assoc (eqToHom _) (X.left.map _) _,show
        X.left.map (unaugment.map f.unop hZ).op = ((𝟭 (SimplicialObject C)).obj X.left).map
        (unaugment.map f.unop hZ).op from rfl, hx]
        simp only [Functor.id_obj, Category.assoc, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id]
    · rw [dif_neg hW,dif_neg hW,dif_neg (strict_initial' g.unop hW),unop_comp,unaugment.map_comp,
      op_comp,X.left.map_comp]
      simp only [Functor.id_obj, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
   }


lemma obj'_left  (X: Augmented C) :
SimplexCategory.augment.op ⋙ augToFunc.obj' X = X.left := by
  apply Functor.ext
  intro Y Z f
  rw [Functor.comp_map]
  unfold augToFunc.obj' obj'.map'
  dsimp
  rw [dif_neg (SimplexCategory.augment_len Z.unop)]
  simp
  congr
  exact SimplexCategory.augment_unaugment_map f.unop
  --obj
  intro Y
  rw [Functor.comp_obj]
  unfold augToFunc.obj' obj'.obj'
  dsimp
  rw [if_neg (SimplexCategory.augment_len Y.unop)]
  congr

def map'  {X1 X2: SimplicialObject.Augmented C}  (f :X1 ⟶ X2):
    augToFunc.obj' X1 ⟶ augToFunc.obj' X2 where
    app Y :=by
      by_cases  hY: Y.unop.len=0
      · exact eqToHom (obj'.obj'_eq_zero X1 hY) ≫ f.right ≫ eqToHom (obj'.obj'_eq_zero X2 hY).symm
      · exact eqToHom (obj'.obj'_neq_zero X1 hY).symm≫  f.left.app (op [Y.unop.len-1])
             ≫ eqToHom (obj'.obj'_neq_zero X2 hY)
    naturality := by {
      intro Y Z g
      dsimp
      unfold augToFunc.obj' obj'.map'
      dsimp
      by_cases hZ : Z.unop.len =0
      · unfold obj'.map''
        rw [dif_pos hZ,dif_pos hZ,dif_pos hZ]
        by_cases hY : Y.unop.len=0
        · rw [dif_pos hY,dif_pos hY,dif_pos hY]
          simp only [eqToHom_trans, eqToHom_trans_assoc, Category.assoc]
        · rw [dif_neg hY,dif_neg hY,dif_neg hY]
          simp only [Functor.id_obj, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
            Category.id_comp]
          rw [← Category.assoc,← Category.assoc, Category.assoc _ _ f.right]
          have h2 := congrFun (congrArg NatTrans.app f.w) (op [AugmentedSimplexCategory.len Y.unop - 1])
          rw [NatTrans.comp_app,NatTrans.comp_app,show ((const C).map f.right).app
            (op [AugmentedSimplexCategory.len Y.unop - 1]) = f.right from rfl] at h2
          rw [← h2]
          simp only [Functor.id_obj, Functor.const_obj_obj, Functor.id_map, Category.assoc]
      · rw [dif_neg hZ,dif_neg hZ,dif_neg hZ,dif_neg (strict_initial' g.unop hZ )]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc,← Category.assoc,← Category.assoc,← Category.assoc,
        Category.assoc _ _ (X2.left.map _),← f.left.naturality,Category.assoc,Category.assoc,
        Category.assoc,Category.assoc]
        congr
    }

end augToFunc

def augToFunc : SimplicialObject.Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)  where
   obj := augToFunc.obj'
   map := augToFunc.map'
   map_id := by {
    intro X
    apply NatTrans.ext
    funext Y
    unfold augToFunc.map'
    dsimp only [Functor.id_obj, instCategoryAugmented_id_right, instCategoryAugmented_id_left_app,
      NatTrans.id_app]
    split
    all_goals simp only [ Category.id_comp, eqToHom_trans, eqToHom_refl]
   }
   map_comp := by {
    intro X1 X2 X3 F G
    apply NatTrans.ext
    funext Y
    unfold augToFunc.map'
    dsimp
    by_cases hY: Y.unop.len=0
    · rw [dif_pos hY,dif_pos hY,dif_pos hY]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · rw [dif_neg hY,dif_neg hY,dif_neg hY]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
   }

namespace augFuncEquiv
namespace unitIso'
open AugmentedSimplexCategory in

lemma eq (X : AugmentedSimplexCategoryᵒᵖ ⥤ C) : (funcToAug ⋙ augToFunc ).obj X =X
  :=by
    rw [Functor.comp_obj]
    apply Functor.ext
    case h_obj =>
      intro Y
      unfold augToFunc augToFunc.obj' augToFunc.obj'.obj' funcToAug funcToAug.obj'
      by_cases hY :Y.unop.len=0
      · simp only [Functor.comp_obj, Functor.op_obj, unop_op,if_pos hY,congrArg X.obj]
        exact congrArg X.obj (congrArg op hY.symm)
      · nth_rewrite 2 [← (op_unop Y)]
        rw [← unaugment_augment_obj hY]
        exact if_neg hY
    case h_map =>
      intro Y Z f
      unfold augToFunc augToFunc.obj' augToFunc.obj'.map' augToFunc.obj'.map''
      by_cases hZ : Z.unop.len =0
      · dsimp
        rw [dif_pos hZ]
        by_cases hY : Y.unop.len =0
        · let hx:= congrArg X.map
            (congrArg Quiver.Hom.op (map_into_initial_eqToHom (len_zero_isInitial hY) f.unop))
          rw [eqToHom_op,eqToHom_map X,Quiver.Hom.op_unop] at hx
          simp only [dif_pos hY,eqToHom_trans, hx, op_unop]
        · unfold funcToAug funcToAug.obj'
          simp only [dif_neg hY,Functor.id_obj,Functor.op_obj, Functor.comp_obj, unop_op]
          rw [show map_from_initial (SimplexCategory.augment.obj [Y.unop.len-1]).len
           =(eqToHom (congrArg op (unaugment_augment_obj hY)) ≫f≫eqToHom (congrArg op hZ)).unop by
           apply IsInitial.hom_ext zero_isInitial,Quiver.Hom.op_unop,X.map_comp,X.map_comp,
           eqToHom_map X,eqToHom_map X,eqToHom_trans_assoc,Category.assoc,Category.assoc,
           eqToHom_trans]
      · nth_rewrite 2 [← (Quiver.Hom.op_unop f)]
        rw [← unaugment_augment_map f.unop hZ,op_comp, op_comp,X.map_comp,X.map_comp,eqToHom_op,
        eqToHom_op,eqToHom_map X,eqToHom_map X,Category.assoc,Category.assoc,eqToHom_trans,
        eqToHom_trans_assoc]
        exact dif_neg hZ


lemma nat' (X1 X2 : AugmentedSimplexCategoryᵒᵖ ⥤ C)  (F :X1⟶ X2):
(𝟭 (AugmentedSimplexCategoryᵒᵖ ⥤ C)).map F ≫ eqToHom (augFuncEquiv.unitIso'.eq X2).symm
= eqToHom (augFuncEquiv.unitIso'.eq X1).symm  ≫ (funcToAug ⋙ augToFunc).map F:= by
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
  apply NatTrans.ext
  funext d
  unfold funcToAug  augToFunc  augToFunc.map'
  simp
  by_cases hd: d.unop.len=0
  · rw [dif_pos hd]
    simp only [comp_eqToHom_iff,eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
    exact dcongr_arg F.app (unop_eq_iff_eq_op.mp hd)
  · rw [dif_neg hd]
    unfold funcToAug.map'
    simp only [Functor.id_obj, whiskerLeft_app, Functor.op_obj, unop_op, eqToHom_trans_assoc,
      comp_eqToHom_iff, Category.assoc, eqToHom_trans]
    refine  dcongr_arg F.app ?_
    change op d.unop =_
    apply congrArg
    exact (AugmentedSimplexCategory.unaugment_augment_obj hd).symm


end unitIso'
def unitIso' : 𝟭 (AugmentedSimplexCategoryᵒᵖ ⥤ C) ≅ funcToAug ⋙ augToFunc where
  hom := {
    app := by
      intro X
      exact eqToHom (augFuncEquiv.unitIso'.eq X).symm
    naturality := by
       intro X1 X2 F
       exact augFuncEquiv.unitIso'.nat' X1 X2 F
  }
  inv := {
    app := by
        intro X
        exact eqToHom (augFuncEquiv.unitIso'.eq X)
    naturality := by
      intro X1 X2 F
      symm
      rw [eqToHom_comp_iff,← Category.assoc,← comp_eqToHom_iff]
      exact augFuncEquiv.unitIso'.nat' X1 X2 F
  }

namespace counitIso'
lemma eq_left   (X : Augmented C) : ((augToFunc⋙ funcToAug ).obj X).left = X.left:= by
    unfold funcToAug
    dsimp only [Functor.comp_obj]
    rw [funcToAug.obj'_left]
    exact augToFunc.obj'_left X

lemma eq_right   (X : Augmented C) :((augToFunc⋙ funcToAug ).obj X).right = X.right :=rfl

def app' (X : Augmented C) : ((augToFunc⋙ funcToAug ).obj X) ≅ X:= by
    refine Comma.isoMk (CategoryTheory.eqToIso (augFuncEquiv.counitIso'.eq_left X))
     (CategoryTheory.eqToIso (augFuncEquiv.counitIso'.eq_right X)) (?_)
    apply NatTrans.ext
    funext d
    unfold funcToAug augToFunc  funcToAug.obj' augToFunc.obj' augToFunc.obj'.obj'
      augToFunc.obj'.map' augToFunc.obj'.map''
    simp only [Functor.id_obj, Functor.op_obj, Functor.comp_obj, unop_op, eqToHom_refl,
      Quiver.Hom.unop_op, Functor.const_obj_obj, eqToIso.hom, Functor.id_map,
      instCategorySimplicialObject_comp_app, Category.id_comp, Category.comp_id,
      CategoryTheory.eqToIso_refl, Iso.refl_hom, Functor.map_id]
    rw [dif_pos (by rfl),dif_neg (SimplexCategory.augment_len d.unop ),
    show (eqToHom (augFuncEquiv.counitIso'.eq_left X)).app d= eqToHom (by rfl) by apply eqToHom_app]
    exact Category.id_comp (X.hom.app d)

end counitIso'
def counitIso'   : augToFunc ⋙  funcToAug ≅ 𝟭 (Augmented C) where
  hom := {
    app := by
      intro X
      exact (augFuncEquiv.counitIso'.app' X).hom
    naturality := by
      intro X1 X2 F
      simp
      apply Comma.hom_ext
      · rw [Comma.comp_left,Comma.comp_left]
        unfold funcToAug funcToAug.map' augFuncEquiv.counitIso'.app' augToFunc augToFunc.map'
        apply NatTrans.ext
        funext d
        dsimp
        rw [dif_neg (SimplexCategory.augment_len d.unop)]
        simp
        rw [eqToHom_app,eqToHom_app]
        exact eqToHom_naturality F.left.app (by rfl)
      · rw [Comma.comp_right,Comma.comp_right]
        unfold funcToAug funcToAug.map' augFuncEquiv.counitIso'.app' augToFunc augToFunc.map'
        simp only [Functor.id_obj, unop_op, eqToHom_refl, Category.comp_id, Category.id_comp,
          Functor.comp_obj, CategoryTheory.eqToIso_refl, Comma.isoMk_hom_right, Iso.refl_hom]
        rw [dif_pos (by rfl),show 𝟙 (funcToAug.obj (augToFunc.obj' X1)).right≫F.right=F.right
         from Category.id_comp F.right]
        exact Category.comp_id F.right
  }
  inv := {
    app := by
      intro X
      exact (augFuncEquiv.counitIso'.app' X).inv
    naturality := by
        intro X1 X2 F
        simp
        apply Comma.hom_ext
        · rw [Comma.comp_left,Comma.comp_left]
          unfold funcToAug funcToAug.map' augFuncEquiv.counitIso'.app' augToFunc augToFunc.map'
          apply NatTrans.ext
          funext d
          simp only [Functor.id_obj, Functor.comp_obj, CategoryTheory.eqToIso_refl,
            Comma.isoMk_inv_left, eqToIso.inv, instCategorySimplicialObject_comp_app,
            whiskerLeft_app, Functor.op_obj, unop_op, eqToHom_refl, Category.comp_id,
            Category.id_comp]
          rw [dif_neg (SimplexCategory.augment_len d.unop),eqToHom_app,eqToHom_app]
          exact eqToHom_naturality F.left.app rfl
        · rw [Comma.comp_right,Comma.comp_right]
          unfold funcToAug funcToAug.map' augFuncEquiv.counitIso'.app' augToFunc augToFunc.map'
          simp only [Functor.id_obj, Functor.comp_obj, CategoryTheory.eqToIso_refl,
            Comma.isoMk_inv_right, Iso.refl_inv, unop_op, eqToHom_refl, Category.comp_id,
            Category.id_comp]
          rw [dif_pos (by rfl), show 𝟙 (funcToAug.obj (augToFunc.obj' X1)).right ≫ F.right =F.right
           from  Category.id_comp F.right]
          exact Category.comp_id F.right
  }

end augFuncEquiv

open augFuncEquiv in
def augFuncEquiv :(AugmentedSimplexCategoryᵒᵖ ⥤ C)  ≌ (Augmented C) where
   functor := funcToAug
   inverse := augToFunc
   unitIso := unitIso'
   counitIso := counitIso'
   functor_unitIso_comp := by
      intro X1
      unfold  unitIso' counitIso' counitIso'.app'  Comma.isoMk
      dsimp
      apply Comma.hom_ext
      · rw [eqToHom_map,Comma.comp_left,Comma.eqToHom_left,Comma.id_left,eqToHom_trans,eqToHom_refl]
      · rw [eqToHom_map,Comma.comp_right,Comma.eqToHom_right,eqToHom_refl,Category.comp_id
         ,Comma.id_right]







end SimplicialObject

-- porting note: removed @[nolint has_nonempty_instance]
/-- Cosimplicial objects. -/
def CosimplicialObject :=
  SimplexCategory ⥤ C
#align category_theory.cosimplicial_object CategoryTheory.CosimplicialObject

@[simps!]
instance : Category (CosimplicialObject C) := by
  dsimp only [CosimplicialObject]
  infer_instance

namespace CosimplicialObject

-- mathport name: cosimplicial_object.at
set_option quotPrecheck false in
/-- `X _[n]` denotes the `n`th-term of the cosimplicial object X -/
scoped[Simplicial]
  notation:1000 X " _[" n "]" =>
    (X : CategoryTheory.CosimplicialObject _).obj (SimplexCategory.mk n)

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance

instance [HasLimits C] : HasLimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance

instance [HasColimits C] : HasColimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : CosimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SimplexCategory), f.app n = g.app n) : f = g :=
  NatTrans.ext _ _ (by ext; apply h)

variable (X : CosimplicialObject C)

open Simplicial

/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.δ i)
#align category_theory.cosimplicial_object.δ CategoryTheory.CosimplicialObject.δ

/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.σ i)
#align category_theory.cosimplicial_object.σ CategoryTheory.CosimplicialObject.σ

/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso (CategoryTheory.eqToIso (by rw [h]))
#align category_theory.cosimplicial_object.eq_to_iso CategoryTheory.CosimplicialObject.eqToIso

@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  ext
  simp [eqToIso]
#align category_theory.cosimplicial_object.eq_to_iso_refl CategoryTheory.CosimplicialObject.eqToIso_refl

/-- The generic case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]
#align category_theory.cosimplicial_object.δ_comp_δ CategoryTheory.CosimplicialObject.δ_comp_δ

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ i ≫ X.δ j =
      X.δ (j.pred fun (hj : j = 0) => by simp only [hj, Fin.not_lt_zero] at H) ≫
        X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
#align category_theory.cosimplicial_object.δ_comp_δ' CategoryTheory.CosimplicialObject.δ_comp_δ'

@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ X.δ j.succ =
      X.δ j ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
#align category_theory.cosimplicial_object.δ_comp_δ'' CategoryTheory.CosimplicialObject.δ_comp_δ''

/-- The special case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ i ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]
#align category_theory.cosimplicial_object.δ_comp_δ_self CategoryTheory.CosimplicialObject.δ_comp_δ_self

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ := by
  subst H
  rw [δ_comp_δ_self]
#align category_theory.cosimplicial_object.δ_comp_δ_self' CategoryTheory.CosimplicialObject.δ_comp_δ_self'

/-- The second cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.δ (Fin.castSucc i) ≫ X.σ j.succ = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_le CategoryTheory.CosimplicialObject.δ_comp_σ_of_le

/-- The first part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.δ (Fin.castSucc i) ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]
#align category_theory.cosimplicial_object.δ_comp_σ_self CategoryTheory.CosimplicialObject.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]
#align category_theory.cosimplicial_object.δ_comp_σ_self' CategoryTheory.CosimplicialObject.δ_comp_σ_self'

/-- The second part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]
#align category_theory.cosimplicial_object.δ_comp_σ_succ CategoryTheory.CosimplicialObject.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]
#align category_theory.cosimplicial_object.δ_comp_σ_succ' CategoryTheory.CosimplicialObject.δ_comp_σ_succ'

/-- The fourth cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.δ i.succ ≫ X.σ (Fin.castSucc j) = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.δ i ≫ X.σ j =
      X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
        X.δ (i.pred <|
          fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt' CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt'

/-- The fifth cosimplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ (Fin.castSucc i) ≫ X.σ j = X.σ j.succ ≫ X.σ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]
#align category_theory.cosimplicial_object.σ_comp_σ CategoryTheory.CosimplicialObject.σ_comp_σ

@[reassoc (attr := simp)]
theorem δ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (SimplexCategory.mk (n + 1)) = f.app (SimplexCategory.mk n) ≫ X'.δ i :=
  f.naturality _
#align category_theory.cosimplicial_object.δ_naturality CategoryTheory.CosimplicialObject.δ_naturality

@[reassoc (attr := simp)]
theorem σ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (SimplexCategory.mk n) = f.app (SimplexCategory.mk (n + 1)) ≫ X'.σ i :=
  f.naturality _
#align category_theory.cosimplicial_object.σ_naturality CategoryTheory.CosimplicialObject.σ_naturality

variable (C)

/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps!]
def whiskering (D : Type*) [Category D] : (C ⥤ D) ⥤ CosimplicialObject C ⥤ CosimplicialObject D :=
  whiskeringRight _ _ _
#align category_theory.cosimplicial_object.whiskering CategoryTheory.CosimplicialObject.whiskering

-- porting note: removed @[nolint has_nonempty_instance]
/-- Truncated cosimplicial objects. -/
def Truncated (n : ℕ) :=
  SimplexCategory.Truncated n ⥤ C
#align category_theory.cosimplicial_object.truncated CategoryTheory.CosimplicialObject.Truncated

instance : Category (Truncated C n) := by
  dsimp [Truncated]
  infer_instance

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C)

/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps!]
def whiskering {n} (D : Type*) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _
#align category_theory.cosimplicial_object.truncated.whiskering CategoryTheory.CosimplicialObject.Truncated.whiskering

variable {C}

end Truncated

section Skeleton

/-- The skeleton functor from cosimplicial objects to truncated cosimplicial objects. -/
def sk (n : ℕ) : CosimplicialObject C ⥤ CosimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.inclusion
#align category_theory.cosimplicial_object.sk CategoryTheory.CosimplicialObject.sk

end Skeleton

variable (C)

/-- The constant cosimplicial object. -/
abbrev const : C ⥤ CosimplicialObject C :=
  CategoryTheory.Functor.const _
#align category_theory.cosimplicial_object.const CategoryTheory.CosimplicialObject.const

-- porting note: removed @[nolint has_nonempty_instance]
/-- Augmented cosimplicial objects. -/
def Augmented :=
  Comma (const C) (𝟭 (CosimplicialObject C))
#align category_theory.cosimplicial_object.augmented CategoryTheory.CosimplicialObject.Augmented

@[simps!]
instance : Category (Augmented C) := by
  dsimp only [Augmented]
  infer_instance

variable {C}

namespace Augmented

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!]
def drop : Augmented C ⥤ CosimplicialObject C :=
  Comma.snd _ _
#align category_theory.cosimplicial_object.augmented.drop CategoryTheory.CosimplicialObject.Augmented.drop

/-- The point of the augmentation. -/
@[simps!]
def point : Augmented C ⥤ C :=
  Comma.fst _ _
#align category_theory.cosimplicial_object.augmented.point CategoryTheory.CosimplicialObject.Augmented.point

/-- The functor from augmented objects to arrows. -/
@[simps!]
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := point.obj X
      right := drop.obj X _[0]
      hom := X.hom.app _ }
  map η :=
    { left := point.map η
      right := (drop.map η).app _
      w := by
        dsimp
        rw [← NatTrans.comp_app]
        erw [← η.w]
        rfl }
#align category_theory.cosimplicial_object.augmented.to_arrow CategoryTheory.CosimplicialObject.Augmented.toArrow

variable (C)

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
def whiskeringObj (D : Type*) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := F.obj (point.obj X)
      right := ((whiskering _ _).obj F).obj (drop.obj X)
      hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.hom F }
  map η :=
    { left := F.map η.left
      right := whiskerRight η.right _
      w := by
        ext
        dsimp
        rw [Category.id_comp, Category.id_comp, ← F.map_comp, ← F.map_comp, ← NatTrans.comp_app]
        erw [← η.w]
        rfl }
#align category_theory.cosimplicial_object.augmented.whiskering_obj CategoryTheory.CosimplicialObject.Augmented.whiskeringObj

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := η.app _
          right := whiskerLeft _ η
          w := by
            ext n
            dsimp
            rw [Category.id_comp, Category.id_comp, η.naturality] }
      naturality := fun _ _ f => by ext <;> dsimp <;> simp }
#align category_theory.cosimplicial_object.augmented.whiskering CategoryTheory.CosimplicialObject.Augmented.whiskering

variable {C}

end Augmented

open Simplicial

/-- Augment a cosimplicial object with an object. -/
@[simps]
def augment (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0])
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : ([0] : SimplexCategory) ⟶ i),
      f ≫ X.map g₁ = f ≫ X.map g₂) : CosimplicialObject.Augmented C where
  left := X₀
  right := X
  hom :=
    { app := fun i => f ≫ X.map (SimplexCategory.const i 0)
      naturality := by
        intro i j g
        dsimp
        simpa [← X.map_comp] using w _ _ _ }
#align category_theory.cosimplicial_object.augment CategoryTheory.CosimplicialObject.augment

-- porting note: removed @[simp] as the linter complains
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) (w) :
    (X.augment X₀ f w).hom.app [0] = f := by
  dsimp
  rw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, Category.comp_id]
#align category_theory.cosimplicial_object.augment_hom_zero CategoryTheory.CosimplicialObject.augment_hom_zero

end CosimplicialObject

/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps!]
def simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ :=
  Functor.leftOpRightOpEquiv _ _
#align category_theory.simplicial_cosimplicial_equiv CategoryTheory.simplicialCosimplicialEquiv

/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps!]
def cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ :=
  Functor.opUnopEquiv _ _
#align category_theory.cosimplicial_simplicial_equiv CategoryTheory.cosimplicialSimplicialEquiv

variable {C}

/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps!]
def SimplicialObject.Augmented.rightOp (X : SimplicialObject.Augmented C) :
    CosimplicialObject.Augmented Cᵒᵖ where
  left := Opposite.op X.right
  right := X.left.rightOp
  hom := NatTrans.rightOp X.hom
#align category_theory.simplicial_object.augmented.right_op CategoryTheory.SimplicialObject.Augmented.rightOp

/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps!]
def CosimplicialObject.Augmented.leftOp (X : CosimplicialObject.Augmented Cᵒᵖ) :
    SimplicialObject.Augmented C where
  left := X.right.leftOp
  right := X.left.unop
  hom := NatTrans.leftOp X.hom
#align category_theory.cosimplicial_object.augmented.left_op CategoryTheory.CosimplicialObject.Augmented.leftOp

/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps!]
def SimplicialObject.Augmented.rightOpLeftOpIso (X : SimplicialObject.Augmented C) :
    X.rightOp.leftOp ≅ X :=
  Comma.isoMk X.left.rightOpLeftOpIso (CategoryTheory.eqToIso <| by aesop_cat)
#align category_theory.simplicial_object.augmented.right_op_left_op_iso CategoryTheory.SimplicialObject.Augmented.rightOpLeftOpIso

/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps!]
def CosimplicialObject.Augmented.leftOpRightOpIso (X : CosimplicialObject.Augmented Cᵒᵖ) :
    X.leftOp.rightOp ≅ X :=
  Comma.isoMk (CategoryTheory.eqToIso <| by simp) X.right.leftOpRightOpIso
#align category_theory.cosimplicial_object.augmented.left_op_right_op_iso CategoryTheory.CosimplicialObject.Augmented.leftOpRightOpIso

variable (C)

/-- A functorial version of `SimplicialObject.Augmented.rightOp`. -/
@[simps]
def simplicialToCosimplicialAugmented :
    (SimplicialObject.Augmented C)ᵒᵖ ⥤ CosimplicialObject.Augmented Cᵒᵖ where
  obj X := X.unop.rightOp
  map f :=
    { left := f.unop.right.op
      right := NatTrans.rightOp f.unop.left
      w := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }
#align category_theory.simplicial_to_cosimplicial_augmented CategoryTheory.simplicialToCosimplicialAugmented

/-- A functorial version of `Cosimplicial_object.Augmented.leftOp`. -/
@[simps]
def cosimplicialToSimplicialAugmented :
    CosimplicialObject.Augmented Cᵒᵖ ⥤ (SimplicialObject.Augmented C)ᵒᵖ where
  obj X := Opposite.op X.leftOp
  map f :=
    Quiver.Hom.op <|
      { left := NatTrans.leftOp f.right
        right := f.left.unop
        w := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w (unop x)).symm }
#align category_theory.cosimplicial_to_simplicial_augmented CategoryTheory.cosimplicialToSimplicialAugmented

/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps! functor inverse]
def simplicialCosimplicialAugmentedEquiv :
    (SimplicialObject.Augmented C)ᵒᵖ ≌ CosimplicialObject.Augmented Cᵒᵖ :=
  Equivalence.mk (simplicialToCosimplicialAugmented _) (cosimplicialToSimplicialAugmented _)
    (NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun f => by
      dsimp
      rw [← f.op_unop]
      simp_rw [← op_comp]
      congr 1
      aesop_cat)
    (NatIso.ofComponents fun X => X.leftOpRightOpIso)
#align category_theory.simplicial_cosimplicial_augmented_equiv CategoryTheory.simplicialCosimplicialAugmentedEquiv

end CategoryTheory

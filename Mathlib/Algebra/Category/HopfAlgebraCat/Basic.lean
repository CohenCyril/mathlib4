/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.BialgebraCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The category of Hopf algebras

This file mimics `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-Hopf algebrass. -/
structure HopfAlgebraCat extends Bundled Ring.{v} where
  isHopfAlgebra : HopfAlgebra R α

attribute [instance] HopfAlgebraCat.isHopfAlgebra

variable {R}

namespace HopfAlgebraCat

open HopfAlgebra

instance : CoeSort (HopfAlgebraCat.{v} R) (Type v) :=
  ⟨(·.α)⟩

-- I guess I'm only making this because I wanted to extend `RingCat` but can't.
/-- The object in `RingCat` underlying an object in `HopfAlgebraCat R`. -/
def toRingCat (X : HopfAlgebraCat.{v} R) : RingCat := toBundled X

@[simp] theorem ringCat_of_toRingCat (X : HopfAlgebraCat.{v} R) :
    RingCat.of X.toRingCat = X.toRingCat :=
  rfl

variable (R)

/-- The object in the category of `R`-Hopf algebrass associated to an `R`-Hopf algebras. -/
@[simps]
def of (X : Type v) [Ring X] [HopfAlgebra R X] :
    HopfAlgebraCat R where
  isHopfAlgebra := (inferInstance : HopfAlgebra R X)

variable {R}

@[simp]
lemma of_comul {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
lemma of_counit {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : HopfAlgebraCat.{v} R) :=
  /-- The underlying isometry -/
  toBialgHom : V →ₐc[R] W

lemma Hom.toBialgHom_injective (V W : HopfAlgebraCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

instance category : Category (HopfAlgebraCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom f.toBialgHom⟩
  id_comp g := Hom.ext _ _ <| BialgHom.id_comp g.toBialgHom
  comp_id f := Hom.ext _ _ <| BialgHom.comp_id f.toBialgHom
  assoc f g h := Hom.ext _ _ <| BialgHom.comp_assoc h.toBialgHom g.toBialgHom f.toBialgHom

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.
@[ext]
lemma hom_ext {X Y : HopfAlgebraCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext _ _ h

/-- Typecheck a `BialgHom` as a morphism in `HopfAlgebraCat R`. -/
abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [HopfAlgebra R X] [HopfAlgebra R Y] (f : X →ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ⟨f⟩

@[simp] theorem toBialgHom_comp {X Y Z : HopfAlgebraCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl

@[simp] theorem toBialgHom_id {M : HopfAlgebraCat.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl

instance concreteCategory : ConcreteCategory.{v} (HopfAlgebraCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := @fun M N f => f.toBialgHom }
  forget_faithful :=
    { map_injective := @fun M N => DFunLike.coe_injective.comp <| Hom.toBialgHom_injective _ _ }

instance hasForgetToAlgebra : HasForget₂ (HopfAlgebraCat R) (BialgebraCat R) where
  forget₂ :=
    { obj := fun X => BialgebraCat.of R X
      map := fun {X Y} f => BialgebraCat.ofHom f.toBialgHom }

@[simp]
theorem forget₂_bialgebra_obj (X : HopfAlgebraCat R) :
    (forget₂ (HopfAlgebraCat R) (BialgebraCat R)).obj X = BialgebraCat.of R X :=
  rfl

@[simp]
theorem forget₂_bialgebra_map (X Y : HopfAlgebraCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgebraCat R) (BialgebraCat R)).map f = BialgebraCat.ofHom f.toBialgHom :=
  rfl

end HopfAlgebraCat

namespace BialgEquiv

open HopfAlgebraCat

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [HopfAlgebra R X] [HopfAlgebra R Y] [HopfAlgebra R Z]

/-- Build an isomorphism in the category `HopfAlgebraCat R` from a
`BialgEquiv`. -/
@[simps]
def toHopfAlgebraCatIso (e : X ≃ₐc[R] Y) : HopfAlgebraCat.of R X ≅ HopfAlgebraCat.of R Y where
  hom := ⟨e.toBialgHom⟩
  inv := ⟨e.symm.toBialgHom⟩
  hom_inv_id := Hom.ext _ _ <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext _ _ <| DFunLike.ext _ _ e.right_inv

@[simp] theorem toHopfAlgebraCatIso_refl : toIso (BialgEquiv.refl R X) = .refl _ :=
  rfl

@[simp] theorem toHopfAlgebraCatIso_symm (e : X ≃ₐc[R] Y) :
    toIso e.symm = (toIso e).symm :=
  rfl

@[simp] theorem toHopfAlgebraCatIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toIso (e.trans f) = toIso e ≪≫ toIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open HopfAlgebra

variable {X Y Z : HopfAlgebraCat.{v} R}

/-- Build a `BialgEquiv` from an isomorphism in the category
`HopfAlgebraCat R`. -/
def toHopfAlgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgebraCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgebraCat.Hom.toBialgHom i.4) x }

@[simp] theorem toHopfAlgEquiv_toBialgHom (i : X ≅ Y) :
    (i.toHopfAlgEquiv : X →ₐc[R] Y) = i.hom.1 := rfl

@[simp] theorem toHopfAlgEquiv_refl : toHopfAlgEquiv (.refl X) = .refl _ _ :=
  rfl

@[simp] theorem toHopfAlgEquiv_symm (e : X ≅ Y) :
    toHopfAlgEquiv e.symm = (toHopfAlgEquiv e).symm :=
  rfl

@[simp] theorem toHopfAlgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toHopfAlgEquiv (e ≪≫ f) = e.toHopfAlgEquiv.trans f.toHopfAlgEquiv :=
  rfl

end CategoryTheory.Iso

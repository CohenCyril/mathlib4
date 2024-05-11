/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# The category of coalgebras

This file mimics `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-coalgebras. -/
structure CoalgebraCat extends ModuleCat.{v} R where
  isCoalgebra : Coalgebra R carrier

attribute [instance] CoalgebraCat.isCoalgebra

variable {R}

namespace CoalgebraCat

open Coalgebra

instance : CoeSort (CoalgebraCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

@[simp] theorem moduleCat_of_toModuleCat (X : CoalgebraCat.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

variable (R)

/-- The object in the category of `R`-coalgebras associated to an `R`-coalgebra. -/
@[simps]
def of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] :
    CoalgebraCat R where
  isCoalgebra := (inferInstance : Coalgebra R X)

variable {R}

@[simp]
lemma of_comul {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
lemma of_counit {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `CoalgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : CoalgebraCat.{v} R) :=
  /-- The underlying `CoalgHom` -/
  toCoalgHom : V →ₗc[R] W

lemma Hom.toCoalgHom_injective (V W : CoalgebraCat.{v} R) :
    Function.Injective (Hom.toCoalgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

instance category : Category (CoalgebraCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨CoalgHom.id R M⟩
  comp f g := ⟨CoalgHom.comp g.toCoalgHom f.toCoalgHom⟩
  id_comp g := Hom.ext _ _ <| CoalgHom.id_comp g.toCoalgHom
  comp_id f := Hom.ext _ _ <| CoalgHom.comp_id f.toCoalgHom
  assoc f g h := Hom.ext _ _ <| CoalgHom.comp_assoc h.toCoalgHom g.toCoalgHom f.toCoalgHom

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.
@[ext]
lemma hom_ext {M N : CoalgebraCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom) :
    f = g :=
  Hom.ext _ _ h

/-- Typecheck a `CoalgHom` as a morphism in `CoalgebraCat R`. -/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [Coalgebra R X] [Coalgebra R Y] (f : X →ₗc[R] Y) :
    of R X ⟶ of R Y :=
  ⟨f⟩

@[simp] theorem toCoalgHom_comp {M N U : CoalgebraCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toCoalgHom = g.toCoalgHom.comp f.toCoalgHom :=
  rfl

@[simp] theorem toCoalgHom_id {M : CoalgebraCat.{v} R} :
    Hom.toCoalgHom (𝟙 M) = CoalgHom.id _ _ :=
  rfl

instance concreteCategory : ConcreteCategory.{v} (CoalgebraCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := @fun M N f => f.toCoalgHom }
  forget_faithful :=
    { map_injective := @fun M N => DFunLike.coe_injective.comp <| Hom.toCoalgHom_injective _ _ }

instance hasForgetToModule : HasForget₂ (CoalgebraCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => f.toCoalgHom.toLinearMap }

@[simp]
theorem forget₂_obj (X : CoalgebraCat R) :
    (forget₂ (CoalgebraCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
theorem forget₂_map (X Y : CoalgebraCat R) (f : X ⟶ Y) :
    (forget₂ (CoalgebraCat R) (ModuleCat R)).map f = (f.toCoalgHom : X →ₗ[R] Y) :=
  rfl

end CoalgebraCat

namespace CoalgEquiv

open CoalgebraCat

variable {X Y Z : Type v}
variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
variable [Coalgebra R X] [Coalgebra R Y] [Coalgebra R Z]

/-- Build an isomorphism in the category `CoalgebraCat R` from a
`CoalgEquiv`. -/
@[simps]
def toIso (e : X ≃ₗc[R] Y) : CoalgebraCat.of R X ≅ CoalgebraCat.of R Y where
  hom := ⟨e.toCoalgHom⟩
  inv := ⟨e.symm.toCoalgHom⟩
  hom_inv_id := Hom.ext _ _ <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext _ _ <| DFunLike.ext _ _ e.right_inv

@[simp] theorem toIso_refl : toIso (CoalgEquiv.refl R X) = .refl _ :=
  rfl

@[simp] theorem toIso_symm (e : X ≃ₗc[R] Y) : toIso e.symm = (toIso e).symm :=
  rfl

@[simp] theorem toIso_trans (e : X ≃ₗc[R] Y) (f : Y ≃ₗc[R] Z) :
    toIso (e.trans f) = toIso e ≪≫ toIso f :=
  rfl

end CoalgEquiv

namespace CategoryTheory.Iso

open Coalgebra

variable {X Y Z : CoalgebraCat.{v} R}

/-- Build a `CoalgEquiv` from an isomorphism in the category
`CoalgebraCat R`. -/
@[simps! toCoalgHom]
def toCoalgEquiv (i : X ≅ Y) : X ≃ₗc[R] Y :=
  { i.hom.toCoalgHom with
    invFun := i.inv.toCoalgHom
    left_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgebraCat.Hom.toCoalgHom i.3) x
    right_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgebraCat.Hom.toCoalgHom i.4) x }

@[simp] theorem toCoalgEquiv_refl : toCoalgEquiv (.refl X) = .refl _ _ :=
  rfl

@[simp] theorem toCoalgEquiv_symm (e : X ≅ Y) :
    toCoalgEquiv e.symm = (toCoalgEquiv e).symm :=
  rfl

@[simp] theorem toCoalgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toCoalgEquiv (e ≪≫ f) = e.toCoalgEquiv.trans f.toCoalgEquiv :=
  rfl

end CategoryTheory.Iso

/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic

/-!
# Morphisms of star rings

This file defines morphisms between (non-unital) rings `A` and `B` where both
`A` and `B` are equipped with a `star` operation. This morphisms, namely `NonUnitalStarRingHom` is
a direct extension of its non-`star`red counterpart with a field `map_star` which guarantees it
preserves the star operation.

As with `NonUnitalAlgHom`, the multiplications are not assumed to be associative or unital.

## Main definitions

  * `NonUnitalRingAlgHom`

## Implementation

This file is heavily inspired by `Mathlib.Algebra.Star.StarAlgHom`.

## Tags

non-unital, ring, morphism, star
-/

/-! ### Non-unital star ring homomorphisms -/

/-- A *non-unital ⋆-ring homomorphism* is a non-unital ring homomorphism between non-unital
non-associative semirings `A` and `B` equipped with a `star` operation, and this homomorphism is
also `star`-preserving. -/
structure NonUnitalStarRingHom (A B : Type*) [NonUnitalNonAssocSemiring A]
  [Star A] [NonUnitalNonAssocSemiring B]
  [Star B] extends A →ₙ+* B where
  /-- By definition, a non-unital ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

/-- `α →⋆ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " →⋆ₙ+* " => NonUnitalStarRingHom

/-- Reinterpret a non-unital star ring homomorphism as a non-unital ring homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc NonUnitalStarRingHom.toNonUnitalRingHom

/-- `NonUnitalStarRingHomClass F A B` states that `F` is a type of non-unital ⋆-ring homomorphisms.
You should also extend this typeclass when you extend `NonUnitalStarRingHom`. -/
class NonUnitalStarRingHomClass (F : Type*) (A B : outParam Type*)
     [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] extends StarHomClass F A B : Prop

namespace NonUnitalStarRingHom

section

variable {A B C : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Star C]

instance : FunLike (A →⋆ₙ+* B) A B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩,  _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

instance : NonUnitalRingHomClass (A →⋆ₙ+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

instance : NonUnitalStarRingHomClass (A →⋆ₙ+* B) A B
    where
  map_star f := f.map_star'

initialize_simps_projections NonUnitalStarRingHom (toFun → apply)

@[simp]
theorem coe_toNonUnitalRingHom (f : A →⋆ₙ+* B) : ⇑f.toNonUnitalRingHom = f :=
  rfl

/-- The composition of non-unital ⋆-ring homomorphisms, as a non-unital ⋆-ring homomorphism. -/
def comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : A →⋆ₙ+* C :=
  { f.toNonUnitalRingHom.comp g.toNonUnitalRingHom with
    map_star' := fun a => (calc
      (f ∘ g) (star a) = f ( g (star a)) := rfl
      _ = star (f (g a)) := by rw [map_star, map_star]
      _ = star ((f ∘ g) a) := rfl )}

end

end NonUnitalStarRingHom

/-! ### Star ring equivalences -/

/-- A *⋆-ring* equivalence is an equivalence preserving addition, multiplication, and the star
operation, which allows for considering both unital and non-unital equivalences with a single
structure. -/
structure StarRingEquiv (A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃+* B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

@[inherit_doc StarRingEquiv] infixr:25 " ≃⋆+* " => StarRingEquiv _

@[inherit_doc] notation:25 A " ≃⋆+* " B => StarRingEquiv A B

/-- Reinterpret a star ring equivalence as a `RingEquiv` by forgetting the interaction with the star
operation. -/
add_decl_doc StarRingEquiv.toRingEquiv

/-- `StarRingEquivClass F A B` asserts `F` is a type of bundled ⋆-ring equivalences between `A` and
`B`.
You should also extend this typeclass when you extend `StarRingEquiv`. -/
class StarRingEquivClass (F : Type*) (A B : outParam Type*)
  [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B] [EquivLike F A B]
  extends RingEquivClass F A B : Prop
  where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star : ∀ (f : F) (a : A), f (star a) = star (f a)

namespace StarRingEquiv

section Basic

variable {A B : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]

instance : EquivLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

instance : RingEquivClass (A ≃⋆+* B) A B
    where
  map_mul f := f.map_mul'
  map_add f := f.map_add'

instance : StarRingEquivClass (A ≃⋆+* B) A B
    where
  map_star := map_star'

end Basic

end StarRingEquiv

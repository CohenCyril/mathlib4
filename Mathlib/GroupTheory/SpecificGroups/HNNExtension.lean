/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.SpecificGroups.Coprod
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup
import Mathlib.GroupTheory.Complement

open Monoid Coprod Multiplicative Subgroup

local notation "C∞ " => Multiplicative ℤ

def HNNExtension.con (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Con (G ∗ C∞) :=
  conGen (fun x y => ∃ (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

def HNNExtension  (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Type _ :=
  (HNNExtension.con G A B φ).Quotient

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B} {H : Type*} [Group H]

instance : Group (HNNExtension G A B φ) := by
  delta HNNExtension; infer_instance

namespace HNNExtension

def of : G →* HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inl

def t : HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)

theorem t_mul_of (a : A) :
    t * (of (a : G) : HNNExtension G A B φ) = of (φ a : G) * t :=
  (Con.eq _).2 <| ConGen.Rel.of _ _ <| ⟨a, by simp⟩

theorem of_mul_t (b : B) :
    (of (b : G) : HNNExtension G A B φ) * t = t * of (φ.symm b : G) := by
  rw [t_mul_of]; simp

theorem equiv_eq_conj (a : A) :
    (of (φ a : G) : HNNExtension G A B φ) = t * of (a : G) * t⁻¹ := by
  rw [t_mul_of]; simp

theorem equiv_symm_eq_conj (b : B) :
    (of (φ.symm b : G) : HNNExtension G A B φ) = t⁻¹ * of (b : G) * t := by
  rw [mul_assoc, of_mul_t]; simp

theorem inv_t_mul_of (b : B) :
    t⁻¹ * (of (b : G) : HNNExtension G A B φ) = of (φ.symm b : G) * t⁻¹ := by
  rw [equiv_symm_eq_conj]; simp

theorem of_mul_inv_t (a : A) :
    (of (a : G) : HNNExtension G A B φ) * t⁻¹ = t⁻¹ * of (φ a : G) := by
  rw [equiv_eq_conj]; simp [mul_assoc]

def lift (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    HNNExtension G A B φ →* H :=
  Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

@[simp]
theorem lift_t (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    lift f x hx t = x := by
  delta HNNExtension; simp [lift, t]

@[simp]
theorem lift_of (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) (g : G) :
    lift f x hx (of g) = f g := by
  delta HNNExtension; simp [lift, of]

@[ext]
theorem hom_ext {f g : HNNExtension G A B φ →* H}
    (hg : f.comp of  = g.comp of) (ht : f t = g t) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.ext_hom _ _ hg (MonoidHom.ext_mint ht)

namespace NormalWord

@[reducible]
def BoolFamily (G : Type*) [Group G] : Bool → Type _
  | true => ULift C∞
  | false => G

instance (b : Bool) : Group (BoolFamily G b) := by
  cases b <;> dsimp [BoolFamily] <;> infer_instance

variable (G)

abbrev SumInt : Type _ := Sigma (BoolFamily G)

variable {G}

def SumInt.ofInt (n : ℤ) : SumInt G := ⟨true, ULift.up (ofAdd n)⟩

def SumInt.ofGroup (g : G) : SumInt G := ⟨false, g⟩

@[elab_as_elim]
def SumInt.casesOn {motive : SumInt G → Sort _} (n : SumInt G)
    (h₁ : ∀ n : ℤ, motive (SumInt.ofInt n))
    (h₂ : ∀ g : G, motive (SumInt.ofGroup g)) : motive n :=
  match n with
  | ⟨true, ULift.up n⟩ => h₁ n
  | ⟨false, g⟩ => h₂ g

@[simp]
theorem SumInt.casesOn_ofInt {motive : SumInt G → Sort _} (n : ℤ)
    (h₁ : ∀ n : ℤ, motive (SumInt.ofInt n))
    (h₂ : ∀ g : G, motive (SumInt.ofGroup g)) :
    SumInt.casesOn (SumInt.ofInt n) h₁ h₂ = h₁ n :=
  rfl

@[simp]
theorem SumInt.casesOn_ofGroup {motive : SumInt G → Sort _} (g : G)
    (h₁ : ∀ n : ℤ, motive (SumInt.ofInt n))
    (h₂ : ∀ g : G, motive (SumInt.ofGroup g)) :
    SumInt.casesOn (SumInt.ofGroup g) h₁ h₂ = h₂ g :=
  rfl

variable (G A B φ)

structure TransversalPair : Type _ :=
  /-- The transversal of the first subgroup -/
  ( setA : Set G )
  /-- The chosen element of the subgroup itself is the identity -/
  ( one_mem_A : 1 ∈ setA )
  /-- We have exactly one element of each coset of the subgroup -/
  ( compl_A : IsComplement A setA )
  /-- The transversal of the second subgroup -/
  ( setB : Set G )
  /-- The chosen element of the subgroup itself is the identity -/
  ( one_mem_B : 1 ∈ setB )
  /-- We have exactly one element of each coset of the subgroup -/
  ( compl_B : IsComplement B setB )

instance transversalPair_nonempty  : Nonempty (TransversalPair G A B) := by
  rcases exists_right_transversal (H := A) 1 with ⟨setA, compl_A, one_mem_A⟩
  rcases exists_right_transversal (H := B) 1 with ⟨setB, compl_B, one_mem_B⟩
  exact
    ⟨{ setA := setA, one_mem_A := one_mem_A, compl_A := compl_A,
       setB := setB, one_mem_B := one_mem_B, compl_B := compl_B }⟩

variable {G A B}

structure NormalWord (d : TransversalPair G A B) extends Monoid.CoprodI.Word (BoolFamily G) : Type _ :=
  ( left : ℤ )
  ( chain : toList.Chain' (fun a b : SumInt G => ∀ (t : ℤ) (g : G),
      a = SumInt.ofGroup g → b = SumInt.ofInt t →
      (0 < t → g ∈ d.setB) ∧ (t < 0 → g ∈ d.setA) ) )


end NormalWord

end HNNExtension

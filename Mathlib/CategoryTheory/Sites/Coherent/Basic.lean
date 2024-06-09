/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# The Coherent, Regular and Extensive Grothendieck Topologies

This file defines three related Grothendieck topologies on a category `C`.

The first one is called the *coherent* topology. For that to exist, the category `C` must satisfy a
condition called `Precoherent C`, which is essentially the minimal requirement for the coherent
coverage to exist. It means that finite effective epimorphic families can be "pulled back".
Given such a category, the coherent coverage is `coherentCoverage C` and the corresponding
Grothendieck topology is `coherentTopology C`. The covering sieves of this coverage are generated by
presieves consisting of finite effective epimorphic families.

The second one is called the *regular* topology and for that to exist, the category `C` must satisfy
a condition called `Preregular C`. This means that effective epimorphisms can be "pulled back".
The regular coverage is `regularCoverage C` and the corresponding Grothendieck topology is
`regularTopology C`. The covering sieves of this coverage are generated by presieves consisting of
a single effective epimorphism.

The third one is called the *extensive* coverage and for that to exist, the category `C` must
satisfy a condition called `FinitaryPreExtensive C`. This means `C` has finite coproducts and that
those are preserved by pullbacks. This condition is weaker than `FinitaryExtensive`, where in
addition finite coproducts are disjoint. The extensive coverage is `extensiveCoverage C` and the
corresponding Grothendieck topology is `extensiveTopology C`. The covering sieves of this coverage
are generated by presieves consisting finitely many arrows that together induce an isomorphism
from the coproduct to the target.

## References:
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1, Example 2.1.12.
- [nLab, *Coherent Coverage*](https://ncatlab.org/nlab/show/coherent+coverage)

-/

namespace CategoryTheory

open Limits

variable (C : Type*) [Category C]

/--
The condition `Precoherent C` is essentially the minimal condition required to define the
coherent coverage on `C`.
-/
class Precoherent : Prop where
  /--
  Given an effective epi family `π₁` over `B₁` and a morphism `f : B₂ ⟶ B₁`, there exists
  an effective epi family `π₂` over `B₂`, such that `π₂` factors through `π₁`.
  -/
  pullback {B₁ B₂ : C} (f : B₂ ⟶ B₁) :
    ∀ (α : Type) [Finite α] (X₁ : α → C) (π₁ : (a : α) → (X₁ a ⟶ B₁)),
      EffectiveEpiFamily X₁ π₁ →
    ∃ (β : Type) (_ : Finite β) (X₂ : β → C) (π₂ : (b : β) → (X₂ b ⟶ B₂)),
      EffectiveEpiFamily X₂ π₂ ∧
      ∃ (i : β → α) (ι : (b :  β) → (X₂ b ⟶ X₁ (i b))),
      ∀ (b : β), ι b ≫ π₁ _ = π₂ _ ≫ f

/--
The coherent coverage on a precoherent category `C`.
-/
def coherentCoverage [Precoherent C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Finite α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ EffectiveEpiFamily X π }
  pullback := by
    rintro B₁ B₂ f S ⟨α, _, X₁, π₁, rfl, hS⟩
    obtain ⟨β,_,X₂,π₂,h,i,ι,hh⟩ := Precoherent.pullback f α X₁ π₁ hS
    refine ⟨Presieve.ofArrows X₂ π₂, ⟨β, inferInstance, X₂, π₂, rfl, h⟩, ?_⟩
    rintro _ _ ⟨b⟩
    exact ⟨(X₁ (i b)), ι _, π₁ _, ⟨_⟩, hh _⟩

/--
The coherent Grothendieck topology on a precoherent category `C`.
-/
def coherentTopology [Precoherent C] : GrothendieckTopology C :=
  Coverage.toGrothendieck _ <| coherentCoverage C

/--
The condition `Preregular C` is property that effective epis can be "pulled back" along any
morphism. This is satisfied e.g. by categories that have pullbacks that preserve effective
epimorphisms (like `Profinite` and `CompHaus`), and categories where every object is projective
(like  `Stonean`).
-/
class Preregular : Prop where
  /--
  For `X`, `Y`, `Z`, `f`, `g` like in the diagram, where `g` is an effective epi, there exists
  an object `W`, an effective epi `h : W ⟶ X` and a morphism `i : W ⟶ Z` making the diagram
  commute.
  ```
  W --i-→ Z
  |       |
  h       g
  ↓       ↓
  X --f-→ Y
  ```
  -/
  exists_fac : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [EffectiveEpi g],
    (∃ (W : C) (h : W ⟶ X) (_ : EffectiveEpi h) (i : W ⟶ Z), i ≫ g = h ≫ f)

/--
The regular coverage on a regular category `C`.
-/
def regularCoverage [Preregular C] : Coverage C where
  covering B := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f }
  pullback := by
    intro X Y f S ⟨Z, π, hπ, h_epi⟩
    have := Preregular.exists_fac f π
    obtain ⟨W, h, _, i, this⟩ := this
    refine ⟨Presieve.singleton h, ⟨?_, ?_⟩⟩
    · exact ⟨W, h, by {rw [Presieve.ofArrows_pUnit h]}, inferInstance⟩
    · intro W g hg
      cases hg
      refine ⟨Z, i, π, ⟨?_, this⟩⟩
      cases hπ
      rw [Presieve.ofArrows_pUnit]
      exact Presieve.singleton.mk

/--
The regular Grothendieck topology on a preregular category `C`.
-/
def regularTopology [Preregular C] : GrothendieckTopology C :=
  Coverage.toGrothendieck _ <| regularCoverage C

/--
The extensive coverage on an extensive category `C`

TODO: use general colimit API instead of `IsIso (Sigma.desc π)`
-/
def extensiveCoverage [FinitaryPreExtensive C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Finite α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }
  pullback := by
    intro X Y f S ⟨α, hα, Z, π, hS, h_iso⟩
    let Z' : α → C := fun a ↦ pullback f (π a)
    let π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst
    refine ⟨@Presieve.ofArrows C _ _ α Z' π', ⟨?_, ?_⟩⟩
    · constructor
      exact ⟨hα, Z', π', ⟨by simp only, FinitaryPreExtensive.sigma_desc_iso (fun x => π x) f h_iso⟩⟩
    · intro W g hg
      rcases hg with ⟨a⟩
      refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
      rw [hS]
      exact Presieve.ofArrows.mk a

/--
The extensive Grothendieck topology on a finitary pre-extensive category `C`.
-/
def extensiveTopology [FinitaryPreExtensive C] : GrothendieckTopology C :=
  Coverage.toGrothendieck _ <| extensiveCoverage C

end CategoryTheory

/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Nat.PrimeFin

/-!

# The First Order Theory of Algebraically Closed Fields

This file defines the theory of algebraically closed fields of characteristic `p`, as well
as proving completeness of the theory and the Lefschetz Principle.

## Main definitions

* `FirstOrder.Language.Theory.ACF p` : the theory of algebraically closed fields of characteristic
`p` as a theory over the language of rings.
* `FirstOrder.Field.ACF_isComplete` : the theory of algebraically closed fields of characteristic
`p` is complete whenever `p` is prime or zero.
* `FirstOrder.Field.ACF0_realize_iff_infinite_ACF_prime_realize` : the Lefschetz principle.

## Implementation details

To apply a theorem about the model theory of algebraically closed fields to a specific
algebraically closed field `K` which does not have a `Language.ring.Structure` instance,
you must introduce the local instance `compatibleRingOfRing K`. Theorems whose statement requires
both a `Language.ring.Structure` instance and a `Field` instance will all be stated with the
assumption `Field K`, `CharP K p`, `IsAlgClosed K` and `CompatibleRing K` and there are instances
defined saying that these assumption imply `Theory.field.Model K` and `(Theory.ACF p).Model K`

## References
The first order theory of algebraically closed fields, along with the Lefschetz Principle and
the Ax-Grothendieck Theorem were first formalized in Lean 3 by Joseph Hua
[here](https://github.com/Jlh18/ModelTheoryInLean8) with the master's thesis
[here](https://github.com/Jlh18/ModelTheory8Report)

-/

variable {K : Type*}

namespace FirstOrder

namespace Field

open Ring FreeCommRing BigOperators Polynomial Language

/-- A generic monic polynomial of degree `n` as an element of the
free commutative ring in `n+1` variables, with a variable for each
of the `n` non-leading coefficients of the polynomial and one variable (`Fin.last n`)
for `X`.  -/
def genericMonicPoly (n : ℕ) : FreeCommRing (Fin (n + 1)) :=
  of (Fin.last _) ^ n + ∑ i : Fin n, of i.castSucc * of (Fin.last _) ^ (i : ℕ)

/-- Monic polynomials of degree `n` over `K` are equivalent to functions `Fin n → K`  -/
noncomputable def monicPolyEquivFin [CommRing K] [Nontrivial K] (n : ℕ) :
    { p : K[X] // p.Monic ∧ p.natDegree = n } ≃ (Fin n → K) :=
  { toFun := fun p i => p.1.coeff i
    invFun := fun v =>
      let p := Polynomial.ofFinsupp <|
        Finsupp.ofSupportFinite
          (fun i =>
            if h : i < n then v ⟨i, h⟩
            else if i = n then 1 else 0)
          (Set.Finite.subset (Set.finite_le_nat n) <| by
              intro i
              simp
              split_ifs <;> simp_all [le_iff_lt_or_eq])
      have hpn : p.natDegree = n := by
        refine le_antisymm ?_ ?_
        · refine natDegree_le_iff_coeff_eq_zero.2 ?_
          intro i hi
          simp [not_lt_of_gt hi, ne_of_gt hi, Finsupp.ofSupportFinite]
        · refine le_natDegree_of_ne_zero ?_
          simp [Finsupp.ofSupportFinite]
      have hpm : p.Monic := by
        rw [Monic.def, leadingCoeff, hpn]
        simp [Finsupp.ofSupportFinite]
      ⟨p, hpm, hpn⟩
    left_inv := by
      intro p
      ext i
      simp only [ne_eq, Finset.mem_range, dite_eq_ite, coeff_ofFinsupp,
        Finsupp.coe_mk, ite_eq_left_iff, not_lt, Finsupp.ofSupportFinite]
      intro hni
      cases lt_or_eq_of_le hni with
      | inr =>
        subst n
        have := p.2.1
        simp [Monic.def, leadingCoeff, p.2.2] at this
        simp [this]
      | inl h =>
        rw [eq_comm, if_neg (ne_of_gt h)]
        exact coeff_eq_zero_of_natDegree_lt (p.2.2.symm ▸ h)
    right_inv := fun _ => by simp [Finsupp.ofSupportFinite] }

theorem lift_genericMonicPoly [CommRing K] [Nontrivial K] {n : ℕ} (v : Fin (n+1) → K) :
    FreeCommRing.lift v (genericMonicPoly n) =
    ((monicPolyEquivFin n).symm (v ∘ Fin.castSucc)).1.eval (v (Fin.last _)) := by
  let p := (monicPolyEquivFin n).symm (v ∘ Fin.castSucc)
  simp only [genericMonicPoly, map_add, map_pow, lift_of, map_sum, map_mul,
    eval_eq_sum_range, p.2.2]
  simp [monicPolyEquivFin, Finset.sum_range_succ, add_comm, Finsupp.ofSupportFinite,
    Finset.sum_range, Fin.castSucc, Fin.castAdd, Fin.castLE]

/-- A sentence saying every monic polynomial of degree `n` has a root. -/
noncomputable def genericMonicPolyHasRoot (n : ℕ) : Language.ring.Sentence :=
  (∃' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

theorem realize_genericMonicPolyHasRoot [Field K] [CompatibleRing K] (n : ℕ) :
    K ⊨ genericMonicPolyHasRoot n ↔
      ∀ p : { p : K[X] // p.Monic ∧ p.natDegree = n }, ∃ x, p.1.eval x = 0 := by
  letI := Classical.decEq K
  rw [Equiv.forall_congr_left' (monicPolyEquivFin n)]
  simp [Sentence.Realize, genericMonicPolyHasRoot, lift_genericMonicPoly]

/-- The theory of algebraically closed fields of characteristic `p` as a theory over
the language of rings -/
def _root_.FirstOrder.Language.Theory.ACF (p : ℕ) : Theory Language.ring :=
  Theory.fieldOfChar p ∪ genericMonicPolyHasRoot '' {n | 0 < n}

instance [Language.ring.Structure K] (p : ℕ) [h : (Theory.ACF p).Model K] :
    (Theory.fieldOfChar p).Model K :=
  Theory.Model.mono h (Set.subset_union_left _ _)

instance [Field K] [CompatibleRing K] {p : ℕ} [CharP K p] [IsAlgClosed K] :
    (Theory.ACF p).Model K := by
  refine Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  simp only [Theory.model_iff, Set.mem_image, Set.mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  simp only [realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p (ne_of_gt
    (natDegree_pos_iff_degree_pos.1 hn0))

theorem modelField_of_modelACF (p : ℕ) (K : Type*) [Language.ring.Structure K]
    [h : (Theory.ACF p).Model K] : Theory.field.Model K :=
  Theory.Model.mono h (Set.subset_union_of_subset_left (Set.subset_union_left _ _) _)

/-- A model for the Theory of algebraically closed fields is a Field. After introducing
this as a local instance on a particular Type, you should usually also introduce
`modelField_of_modelACF p M`, `compatibleRingOfModelField` and `isAlgClosed_of_model_ACF` -/
@[reducible]
noncomputable def fieldOfModelACF (p : ℕ) (K : Type*)
    [Language.ring.Structure K]
    [h : (Theory.ACF p).Model K] : Field K := by
  haveI := modelField_of_modelACF p K
  exact fieldOfModelField K

theorem isAlgClosed_of_model_ACF (p : ℕ) (K : Type*)
    [Field K] [CompatibleRing K] [h : (Theory.ACF p).Model K] :
    IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h : K ⊨ genericMonicPolyHasRoot '' {n | 0 < n} :=
    Theory.Model.mono h (by simp [Theory.ACF])
  simp only [Theory.model_iff, Set.mem_image, Set.mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp] at h
  have := h _ p.natDegree (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hpi)) rfl
  rw [realize_genericMonicPolyHasRoot] at this
  exact this ⟨_, hpm, rfl⟩

/- Note this is caused by `AlgebraicClosure ℚ`. We don't need to increase heartbeats for
`AlgebraicClosure (ZMod p)` for some reason -/
set_option synthInstance.maxHeartbeats 50000 in
theorem ACF_isSatisfiable {p : ℕ} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsSatisfiable := by
  cases hp with
  | inl hp =>
    haveI : Fact p.Prime := ⟨hp⟩
    letI := compatibleRingOfRing (AlgebraicClosure (ZMod p))
    haveI : CharP (AlgebraicClosure (ZMod p)) p :=
      charP_of_injective_algebraMap
        (RingHom.injective (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) p
    exact ⟨⟨AlgebraicClosure (ZMod p)⟩⟩
  | inr hp =>
    subst hp
    letI := compatibleRingOfRing (AlgebraicClosure ℚ)
    haveI : CharP (AlgebraicClosure ℚ) 0 :=
      charP_of_injective_algebraMap
        (RingHom.injective (algebraMap ℚ (AlgebraicClosure ℚ))) 0
    exact ⟨⟨AlgebraicClosure ℚ⟩⟩

open Cardinal

theorem ACF_isComplete {p : ℕ} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsComplete := by
  apply Categorical.isComplete.{0, 0, 0} (Order.succ ℵ₀) _ _
    (Order.le_succ ℵ₀)
  · simp only [card_ring, lift_id']
    exact le_trans (le_of_lt (lt_aleph0_of_finite _)) (Order.le_succ _)
  · exact ACF_isSatisfiable hp
  · rintro ⟨M⟩
    letI := fieldOfModelACF p M
    haveI := modelField_of_modelACF p M
    letI := compatibleRingOfModelField M
    haveI := isAlgClosed_of_model_ACF p M
    infer_instance
  · rintro ⟨M⟩ ⟨N⟩ hM hN
    letI := fieldOfModelACF p M
    haveI := modelField_of_modelACF p M
    letI := compatibleRingOfModelField M
    haveI := isAlgClosed_of_model_ACF p M
    letI := fieldOfModelACF p N
    haveI := modelField_of_modelACF p N
    letI := compatibleRingOfModelField N
    haveI := isAlgClosed_of_model_ACF p N
    haveI := @charP_of_model_fieldOfChar
    constructor
    refine languageEquivEquivRingEquiv ?_
    apply Classical.choice
    refine IsAlgClosed.ringEquivOfCardinalEqOfCharEq p ?_ ?_
    · rw [hM]; exact Order.lt_succ _
    · rw [hM, hN]

theorem ACF0_realize_of_infinite_ACF_prime_realize (φ : Language.ring.Sentence)
    (hφ : Set.Infinite { p : Nat.Primes | (Theory.ACF p) ⊨ᵇ φ }) :
    Theory.ACF 0 ⊨ᵇ φ := by
  rw [← @not_not (_ ⊨ᵇ _), ← (ACF_isComplete (Or.inr rfl)).models_not_iff,
    Theory.models_iff_finset_models]
  push_neg
  intro T0 hT0
  have f : ∀ ψ ∈ Theory.ACF 0,
      { s : Finset Nat.Primes // ∀ q : Nat.Primes, (¬ (Theory.ACF q) ⊨ᵇ ψ) → q ∈ s } := by
    intro ψ hψ
    rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm, Set.mem_union, if_pos rfl,
      Set.mem_image] at hψ
    apply Classical.choice
    rcases hψ with h | ⟨p, hp, rfl⟩
    · refine ⟨⟨∅, ?_⟩⟩
      intro q hq
      exact (hq (Theory.models_sentence_of_mem
        (by rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm];
            exact Set.mem_union_left _ h))).elim
    · refine ⟨⟨{⟨p, hp⟩}, ?_⟩⟩
      intro q hq
      rw [Theory.models_sentence_iff, not_forall] at hq
      rcases hq with ⟨K, hK⟩
      letI := fieldOfModelACF q K
      haveI := modelField_of_modelACF q K
      letI := compatibleRingOfModelField K
      letI := isAlgClosed_of_model_ACF q K
      simp only [Sentence.Realize, eqZero, Formula.realize_not, Formula.realize_equal,
        realize_termOfFreeCommRing, map_natCast, ne_eq, realize_zero,
        not_not, ← CharP.charP_iff_prime_eq_zero hp] at hK
      haveI := @charP_of_model_fieldOfChar
      rw [Finset.mem_singleton]
      exact Subtype.eq <| CharP.eq K inferInstance inferInstance
  let s : Finset Nat.Primes := T0.attach.biUnion (fun φ => f φ.1 (hT0 φ.2))
  have hs : ∀ (p : Nat.Primes) ψ, ψ ∈ T0 → ¬ (Theory.ACF p) ⊨ᵇ ψ → p ∈ s := by
    intro p ψ hψ hpψ
    refine Finset.mem_biUnion.2 ?_
    refine ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, ?_⟩
    exact (f ψ (hT0 hψ)).2 p hpψ
  rcases hφ.exists_not_mem_finset s with ⟨p, hpφ, hps⟩
  have hpT0 : ∀ ψ ∈ T0, Theory.ACF p ⊨ᵇ ψ :=
    fun ψ hψ => not_not.1 (mt (hs p ψ hψ) hps)
  intro h
  have : Theory.ACF p ⊨ᵇ Formula.not φ := Theory.models_of_models_theory hpT0 h
  rw [(ACF_isComplete (Or.inl p.2)).models_not_iff] at this
  exact this hpφ

/-- The Lefschetz principle. A first order sentence is modeled by the theory
of algebraically closed fields of characteristic zero if and only if it is modeled by
the theory of algebraically closed fields of characteristic `p` for infinitely many `p`. -/
theorem ACF0_realize_iff_infinite_ACF_prime_realize {φ : Language.ring.Sentence} :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ } := by
  refine ⟨?_, ACF0_realize_of_infinite_ACF_prime_realize φ⟩
  rw [← not_imp_not, ← (ACF_isComplete (Or.inr rfl)).models_not_iff,
    Set.not_infinite]
  intro hs
  apply ACF0_realize_of_infinite_ACF_prime_realize
  apply Set.infinite_of_finite_compl
  convert hs using 1
  ext p
  simp [(ACF_isComplete (Or.inl p.2)).models_not_iff]

end Field

end FirstOrder

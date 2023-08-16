/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.Minpoly.Field

#align_import ring_theory.power_basis from "leanprover-community/mathlib"@"d1d69e99ed34c95266668af4e288fc1c598b9a7f"

/-!
# Power basis

This file defines a structure `PowerBasis R S`, giving a basis of the
`R`-algebra `S` as a finite list of powers `1, x, ..., x^n`.
For example, if `x` is algebraic over a ring/field, adjoining `x`
gives a `PowerBasis` structure generated by `x`.

## Definitions

* `PowerBasis R A`: a structure containing an `x` and an `n` such that
`1, x, ..., x^n` is a basis for the `R`-algebra `A` (viewed as an `R`-module).

* `finrank (hf : f ≠ 0) : FiniteDimensional.finrank K (AdjoinRoot f) = f.natDegree`,
  the dimension of `AdjoinRoot f` equals the degree of `f`

* `PowerBasis.lift (pb : PowerBasis R S)`: if `y : S'` satisfies the same
  equations as `pb.gen`, this is the map `S →ₐ[R] S'` sending `pb.gen` to `y`

* `PowerBasis.equiv`: if two power bases satisfy the same equations, they are
  equivalent as algebras

## Implementation notes

Throughout this file, `R`, `S`, `A`, `B` ... are `CommRing`s, and `K`, `L`, ... are `Field`s.
`S` is an `R`-algebra, `B` is an `A`-algebra, `L` is a `K`-algebra.

## Tags

power basis, powerbasis

-/


open Polynomial

open Polynomial

variable {R S T : Type*} [CommRing R] [Ring S] [Algebra R S]

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]

variable {K : Type*} [Field K]

/-- `pb : PowerBasis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)`
is a basis for the `R`-algebra `S` (viewed as `R`-module).

This is a structure, not a class, since the same algebra can have many power bases.
For the common case where `S` is defined by adjoining an integral element to `R`,
the canonical power basis is given by `{Algebra,IntermediateField}.adjoin.powerBasis`.
-/
-- @[nolint has_nonempty_instance] -- Porting note: doesn't exist
structure PowerBasis (R S : Type*) [CommRing R] [Ring S] [Algebra R S] where
  gen : S
  dim : ℕ
  basis : Basis (Fin dim) R S
  basis_eq_pow : ∀ (i), basis i = gen ^ (i : ℕ)
#align power_basis PowerBasis

-- this is usually not needed because of `basis_eq_pow` but can be needed in some cases;
-- in such circumstances, add it manually using `@[simps dim gen basis]`.
initialize_simps_projections PowerBasis (-basis)

namespace PowerBasis

@[simp]
theorem coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun i : Fin pb.dim => pb.gen ^ (i : ℕ) :=
  funext pb.basis_eq_pow
#align power_basis.coe_basis PowerBasis.coe_basis

/-- Cannot be an instance because `PowerBasis` cannot be a class. -/
theorem finiteDimensional [Algebra K S] (pb : PowerBasis K S) : FiniteDimensional K S :=
  FiniteDimensional.of_fintype_basis pb.basis
#align power_basis.finite_dimensional PowerBasis.finiteDimensional

theorem finrank [Algebra K S] (pb : PowerBasis K S) : FiniteDimensional.finrank K S = pb.dim := by
  rw [FiniteDimensional.finrank_eq_card_basis pb.basis, Fintype.card_fin]
#align power_basis.finrank PowerBasis.finrank

theorem mem_span_pow' {x y : S} {d : ℕ} :
    y ∈ Submodule.span R (Set.range fun i : Fin d => x ^ (i : ℕ)) ↔
      ∃ f : R[X], f.degree < d ∧ y = aeval x f := by
  have : (Set.range fun i : Fin d => x ^ (i : ℕ)) = (fun i : ℕ => x ^ i) '' ↑(Finset.range d) := by
    ext n
    simp_rw [Set.mem_range, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    exact ⟨fun ⟨⟨i, hi⟩, hy⟩ => ⟨i, hi, hy⟩, fun ⟨i, hi, hy⟩ => ⟨⟨i, hi⟩, hy⟩⟩
  simp only [this, Finsupp.mem_span_image_iff_total, degree_lt_iff_coeff_zero,
    exists_iff_exists_finsupp, coeff, aeval, eval₂RingHom', eval₂_eq_sum, Polynomial.sum, support,
    Finsupp.mem_supported', Finsupp.total, Finsupp.sum, Algebra.smul_def, eval₂_zero, exists_prop,
    LinearMap.id_coe, eval₂_one, id.def, not_lt, Finsupp.coe_lsumHom, LinearMap.coe_smulRight,
    Finset.mem_range, AlgHom.coe_mks, Finset.mem_coe]
  simp_rw [@eq_comm _ y]
  exact Iff.rfl
#align power_basis.mem_span_pow' PowerBasis.mem_span_pow'

theorem mem_span_pow {x y : S} {d : ℕ} (hd : d ≠ 0) :
    y ∈ Submodule.span R (Set.range fun i : Fin d => x ^ (i : ℕ)) ↔
      ∃ f : R[X], f.natDegree < d ∧ y = aeval x f := by
  rw [mem_span_pow']
  constructor <;>
    · rintro ⟨f, h, hy⟩
      refine' ⟨f, _, hy⟩
      by_cases hf : f = 0
      · simp only [hf, natDegree_zero, degree_zero] at h ⊢
        first | exact lt_of_le_of_ne (Nat.zero_le d) hd.symm | exact WithBot.bot_lt_coe d
      simp_all only [degree_eq_natDegree hf]
      · first | exact WithBot.coe_lt_coe.1 h | exact WithBot.coe_lt_coe.2 h
#align power_basis.mem_span_pow PowerBasis.mem_span_pow

theorem dim_ne_zero [Nontrivial S] (pb : PowerBasis R S) : pb.dim ≠ 0 := fun h =>
  not_nonempty_iff.mpr (h.symm ▸ Fin.isEmpty : IsEmpty (Fin pb.dim)) pb.basis.index_nonempty
#align power_basis.dim_ne_zero PowerBasis.dim_ne_zero

theorem dim_pos [Nontrivial S] (pb : PowerBasis R S) : 0 < pb.dim :=
  Nat.pos_of_ne_zero pb.dim_ne_zero
#align power_basis.dim_pos PowerBasis.dim_pos

theorem exists_eq_aeval [Nontrivial S] (pb : PowerBasis R S) (y : S) :
    ∃ f : R[X], f.natDegree < pb.dim ∧ y = aeval pb.gen f :=
  (mem_span_pow pb.dim_ne_zero).mp (by simpa using pb.basis.mem_span y)
#align power_basis.exists_eq_aeval PowerBasis.exists_eq_aeval

theorem exists_eq_aeval' (pb : PowerBasis R S) (y : S) : ∃ f : R[X], y = aeval pb.gen f := by
  nontriviality S
  obtain ⟨f, _, hf⟩ := exists_eq_aeval pb y
  exact ⟨f, hf⟩
#align power_basis.exists_eq_aeval' PowerBasis.exists_eq_aeval'

theorem algHom_ext {S' : Type*} [Semiring S'] [Algebra R S'] (pb : PowerBasis R S)
    ⦃f g : S →ₐ[R] S'⦄ (h : f pb.gen = g pb.gen) : f = g := by
  ext x
  obtain ⟨f, rfl⟩ := pb.exists_eq_aeval' x
  rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, h]
#align power_basis.alg_hom_ext PowerBasis.algHom_ext

section minpoly

open BigOperators

variable [Algebra A S]

/-- `pb.minpolyGen` is the minimal polynomial for `pb.gen`. -/
noncomputable def minpolyGen (pb : PowerBasis A S) : A[X] :=
  X ^ pb.dim - ∑ i : Fin pb.dim, C (pb.basis.repr (pb.gen ^ pb.dim) i) * X ^ (i : ℕ)
#align power_basis.minpoly_gen PowerBasis.minpolyGen

theorem aeval_minpolyGen (pb : PowerBasis A S) : aeval pb.gen (minpolyGen pb) = 0 := by
  simp_rw [minpolyGen, AlgHom.map_sub, AlgHom.map_sum, AlgHom.map_mul, AlgHom.map_pow, aeval_C, ←
    Algebra.smul_def, aeval_X]
  refine' sub_eq_zero.mpr ((pb.basis.total_repr (pb.gen ^ pb.dim)).symm.trans _)
  rw [Finsupp.total_apply, Finsupp.sum_fintype] <;>
    simp only [pb.coe_basis, zero_smul, eq_self_iff_true, imp_true_iff]
#align power_basis.aeval_minpoly_gen PowerBasis.aeval_minpolyGen

theorem minpolyGen_monic (pb : PowerBasis A S) : Monic (minpolyGen pb) := by
  nontriviality A
  apply (monic_X_pow _).sub_of_left _
  rw [degree_X_pow]
  exact degree_sum_fin_lt _
#align power_basis.minpoly_gen_monic PowerBasis.minpolyGen_monic

theorem dim_le_natDegree_of_root (pb : PowerBasis A S) {p : A[X]} (ne_zero : p ≠ 0)
    (root : aeval pb.gen p = 0) : pb.dim ≤ p.natDegree := by
  refine' le_of_not_lt fun hlt => ne_zero _
  rw [p.as_sum_range' _ hlt, Finset.sum_range]
  refine' Fintype.sum_eq_zero _ fun i => _
  simp_rw [aeval_eq_sum_range' hlt, Finset.sum_range, ← pb.basis_eq_pow] at root
  have := Fintype.linearIndependent_iff.1 pb.basis.linearIndependent _ root
  dsimp only at this
  rw [this, monomial_zero_right]
#align power_basis.dim_le_nat_degree_of_root PowerBasis.dim_le_natDegree_of_root

theorem dim_le_degree_of_root (h : PowerBasis A S) {p : A[X]} (ne_zero : p ≠ 0)
    (root : aeval h.gen p = 0) : ↑h.dim ≤ p.degree := by
  rw [degree_eq_natDegree ne_zero]
  exact WithBot.coe_le_coe.2 (h.dim_le_natDegree_of_root ne_zero root)
#align power_basis.dim_le_degree_of_root PowerBasis.dim_le_degree_of_root

theorem degree_minpolyGen [Nontrivial A] (pb : PowerBasis A S) :
    degree (minpolyGen pb) = pb.dim := by
  unfold minpolyGen
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  apply degree_sum_fin_lt
#align power_basis.degree_minpoly_gen PowerBasis.degree_minpolyGen

theorem natDegree_minpolyGen [Nontrivial A] (pb : PowerBasis A S) :
    natDegree (minpolyGen pb) = pb.dim :=
  natDegree_eq_of_degree_eq_some pb.degree_minpolyGen
#align power_basis.nat_degree_minpoly_gen PowerBasis.natDegree_minpolyGen

@[simp]
theorem minpolyGen_eq (pb : PowerBasis A S) : pb.minpolyGen = minpoly A pb.gen := by
  nontriviality A
  refine' minpoly.unique' A _ pb.minpolyGen_monic pb.aeval_minpolyGen fun q hq =>
    or_iff_not_imp_left.2 fun hn0 h0 => _
  exact (pb.dim_le_degree_of_root hn0 h0).not_lt (pb.degree_minpolyGen ▸ hq)
#align power_basis.minpoly_gen_eq PowerBasis.minpolyGen_eq

theorem isIntegral_gen (pb : PowerBasis A S) : IsIntegral A pb.gen :=
  ⟨minpolyGen pb, minpolyGen_monic pb, aeval_minpolyGen pb⟩
#align power_basis.is_integral_gen PowerBasis.isIntegral_gen

@[simp]
theorem degree_minpoly [Nontrivial A] (pb : PowerBasis A S) : degree (minpoly A pb.gen) = pb.dim :=
  by rw [← minpolyGen_eq, degree_minpolyGen]
#align power_basis.degree_minpoly PowerBasis.degree_minpoly

@[simp]
theorem natDegree_minpoly [Nontrivial A] (pb : PowerBasis A S) :
    (minpoly A pb.gen).natDegree = pb.dim := by rw [← minpolyGen_eq, natDegree_minpolyGen]
#align power_basis.nat_degree_minpoly PowerBasis.natDegree_minpoly

protected theorem leftMulMatrix (pb : PowerBasis A S) : Algebra.leftMulMatrix pb.basis pb.gen =
    @Matrix.of (Fin pb.dim) (Fin pb.dim) _ fun i j =>
      if ↑j + 1 = pb.dim then -pb.minpolyGen.coeff ↑i else if (i : ℕ) = j + 1 then 1 else 0 := by
  cases subsingleton_or_nontrivial A; · apply Subsingleton.elim
  rw [Algebra.leftMulMatrix_apply, ← LinearEquiv.eq_symm_apply, LinearMap.toMatrix_symm]
  refine' pb.basis.ext fun k => _
  simp_rw [Matrix.toLin_self, Matrix.of_apply, pb.basis_eq_pow]
  apply (pow_succ _ _).symm.trans
  split_ifs with h
  · simp_rw [h, neg_smul, Finset.sum_neg_distrib, eq_neg_iff_add_eq_zero]
    convert pb.aeval_minpolyGen
    rw [add_comm, aeval_eq_sum_range, Finset.sum_range_succ, ← leadingCoeff,
      pb.minpolyGen_monic.leadingCoeff, one_smul, natDegree_minpolyGen, Finset.sum_range]
  · rw [Fintype.sum_eq_single (⟨(k : ℕ) + 1, lt_of_le_of_ne k.2 h⟩ : Fin pb.dim), if_pos, one_smul]
    · rfl
    intro x hx
    rw [if_neg, zero_smul]
    apply mt Fin.ext hx
#align power_basis.left_mul_matrix PowerBasis.leftMulMatrix

end minpoly

section Equiv

variable [Algebra A S] {S' : Type*} [Ring S'] [Algebra A S']

theorem constr_pow_aeval (pb : PowerBasis A S) {y : S'} (hy : aeval y (minpoly A pb.gen) = 0)
    (f : A[X]) : pb.basis.constr A (fun i => y ^ (i : ℕ)) (aeval pb.gen f) = aeval y f := by
  cases subsingleton_or_nontrivial A
  · rw [(Subsingleton.elim _ _ : f = 0), aeval_zero, map_zero, aeval_zero]
  rw [← aeval_modByMonic_eq_self_of_root (minpoly.monic pb.isIntegral_gen) (minpoly.aeval _ _), ←
    @aeval_modByMonic_eq_self_of_root _ _ _ _ _ f _ (minpoly.monic pb.isIntegral_gen) y hy]
  by_cases hf : f %ₘ minpoly A pb.gen = 0
  · simp only [hf, AlgHom.map_zero, LinearMap.map_zero]
  have : (f %ₘ minpoly A pb.gen).natDegree < pb.dim := by
    rw [← pb.natDegree_minpoly]
    apply natDegree_lt_natDegree hf
    exact degree_modByMonic_lt _ (minpoly.monic pb.isIntegral_gen)
  rw [aeval_eq_sum_range' this, aeval_eq_sum_range' this, LinearMap.map_sum]
  refine' Finset.sum_congr rfl fun i (hi : i ∈ Finset.range pb.dim) => _
  rw [Finset.mem_range] at hi
  rw [LinearMap.map_smul]
  congr
  rw [← Fin.val_mk hi, ← pb.basis_eq_pow ⟨i, hi⟩, Basis.constr_basis]
#align power_basis.constr_pow_aeval PowerBasis.constr_pow_aeval

theorem constr_pow_gen (pb : PowerBasis A S) {y : S'} (hy : aeval y (minpoly A pb.gen) = 0) :
    pb.basis.constr A (fun i => y ^ (i : ℕ)) pb.gen = y := by
  convert pb.constr_pow_aeval hy X <;> rw [aeval_X]
#align power_basis.constr_pow_gen PowerBasis.constr_pow_gen

theorem constr_pow_algebraMap (pb : PowerBasis A S) {y : S'} (hy : aeval y (minpoly A pb.gen) = 0)
    (x : A) : pb.basis.constr A (fun i => y ^ (i : ℕ)) (algebraMap A S x) = algebraMap A S' x := by
  convert pb.constr_pow_aeval hy (C x) <;> rw [aeval_C]
#align power_basis.constr_pow_algebra_map PowerBasis.constr_pow_algebraMap

theorem constr_pow_mul (pb : PowerBasis A S) {y : S'} (hy : aeval y (minpoly A pb.gen) = 0)
    (x x' : S) : pb.basis.constr A (fun i => y ^ (i : ℕ)) (x * x') =
      pb.basis.constr A (fun i => y ^ (i : ℕ)) x * pb.basis.constr A (fun i => y ^ (i : ℕ)) x' := by
  obtain ⟨f, rfl⟩ := pb.exists_eq_aeval' x
  obtain ⟨g, rfl⟩ := pb.exists_eq_aeval' x'
  simp only [← aeval_mul, pb.constr_pow_aeval hy]
#align power_basis.constr_pow_mul PowerBasis.constr_pow_mul

/-- `pb.lift y hy` is the algebra map sending `pb.gen` to `y`,
where `hy` states the higher powers of `y` are the same as the higher powers of `pb.gen`.

See `PowerBasis.liftEquiv` for a bundled equiv sending `⟨y, hy⟩` to the algebra map.
-/
noncomputable def lift (pb : PowerBasis A S) (y : S') (hy : aeval y (minpoly A pb.gen) = 0) :
    S →ₐ[A] S' :=
  { pb.basis.constr A fun i => y ^ (i : ℕ) with
    map_one' := by convert pb.constr_pow_algebraMap hy 1 using 2 <;> rw [RingHom.map_one]
    map_zero' := by convert pb.constr_pow_algebraMap hy 0 using 2 <;> rw [RingHom.map_zero]
    map_mul' := pb.constr_pow_mul hy
    commutes' := pb.constr_pow_algebraMap hy }
#align power_basis.lift PowerBasis.lift

@[simp]
theorem lift_gen (pb : PowerBasis A S) (y : S') (hy : aeval y (minpoly A pb.gen) = 0) :
    pb.lift y hy pb.gen = y :=
  pb.constr_pow_gen hy
#align power_basis.lift_gen PowerBasis.lift_gen

@[simp]
theorem lift_aeval (pb : PowerBasis A S) (y : S') (hy : aeval y (minpoly A pb.gen) = 0) (f : A[X]) :
    pb.lift y hy (aeval pb.gen f) = aeval y f :=
  pb.constr_pow_aeval hy f
#align power_basis.lift_aeval PowerBasis.lift_aeval

/-- `pb.liftEquiv` states that roots of the minimal polynomial of `pb.gen` correspond to
maps sending `pb.gen` to that root.

This is the bundled equiv version of `PowerBasis.lift`.
If the codomain of the `AlgHom`s is an integral domain, then the roots form a multiset,
see `liftEquiv'` for the corresponding statement.
-/
@[simps]
noncomputable def liftEquiv (pb : PowerBasis A S) :
    (S →ₐ[A] S') ≃ { y : S' // aeval y (minpoly A pb.gen) = 0 } where
  toFun f := ⟨f pb.gen, by rw [aeval_algHom_apply, minpoly.aeval, f.map_zero]⟩
  invFun y := pb.lift y y.2
  left_inv f := pb.algHom_ext <| lift_gen _ _ _
  right_inv y := Subtype.ext <| lift_gen _ _ y.prop
#align power_basis.lift_equiv PowerBasis.liftEquiv

/-- `pb.liftEquiv'` states that elements of the root set of the minimal
polynomial of `pb.gen` correspond to maps sending `pb.gen` to that root. -/
@[simps! (config := { fullyApplied := false })]
noncomputable def liftEquiv' (pb : PowerBasis A S) :
    (S →ₐ[A] B) ≃ { y : B // y ∈ ((minpoly A pb.gen).map (algebraMap A B)).roots } :=
  pb.liftEquiv.trans ((Equiv.refl _).subtypeEquiv fun x => by
    rw [Equiv.refl_apply, mem_roots_iff_aeval_eq_zero]
    · simp
    · exact map_monic_ne_zero (minpoly.monic pb.isIntegral_gen))
#align power_basis.lift_equiv' PowerBasis.liftEquiv'

/-- There are finitely many algebra homomorphisms `S →ₐ[A] B` if `S` is of the form `A[x]`
and `B` is an integral domain. -/
noncomputable def AlgHom.fintype (pb : PowerBasis A S) : Fintype (S →ₐ[A] B) :=
  letI := Classical.decEq B
  Fintype.ofEquiv _ pb.liftEquiv'.symm
#align power_basis.alg_hom.fintype PowerBasis.AlgHom.fintype

/-- `pb.equivOfRoot pb' h₁ h₂` is an equivalence of algebras with the same power basis,
where "the same" means that `pb` is a root of `pb'`s minimal polynomial and vice versa.

See also `PowerBasis.equivOfMinpoly` which takes the hypothesis that the
minimal polynomials are identical.
-/
@[simps! (config := { isSimp := false }) apply]
noncomputable def equivOfRoot (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h₁ : aeval pb.gen (minpoly A pb'.gen) = 0) (h₂ : aeval pb'.gen (minpoly A pb.gen) = 0) :
    S ≃ₐ[A] S' :=
  AlgEquiv.ofAlgHom (pb.lift pb'.gen h₂) (pb'.lift pb.gen h₁)
    (by
      ext x
      obtain ⟨f, hf, rfl⟩ := pb'.exists_eq_aeval' x
      simp)
    (by
      ext x
      obtain ⟨f, hf, rfl⟩ := pb.exists_eq_aeval' x
      simp)
#align power_basis.equiv_of_root PowerBasis.equivOfRoot

@[simp]
theorem equivOfRoot_aeval (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h₁ : aeval pb.gen (minpoly A pb'.gen) = 0) (h₂ : aeval pb'.gen (minpoly A pb.gen) = 0)
    (f : A[X]) : pb.equivOfRoot pb' h₁ h₂ (aeval pb.gen f) = aeval pb'.gen f :=
  pb.lift_aeval _ h₂ _
#align power_basis.equiv_of_root_aeval PowerBasis.equivOfRoot_aeval

@[simp]
theorem equivOfRoot_gen (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h₁ : aeval pb.gen (minpoly A pb'.gen) = 0) (h₂ : aeval pb'.gen (minpoly A pb.gen) = 0) :
    pb.equivOfRoot pb' h₁ h₂ pb.gen = pb'.gen :=
  pb.lift_gen _ h₂
#align power_basis.equiv_of_root_gen PowerBasis.equivOfRoot_gen

@[simp]
theorem equivOfRoot_symm (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h₁ : aeval pb.gen (minpoly A pb'.gen) = 0) (h₂ : aeval pb'.gen (minpoly A pb.gen) = 0) :
    (pb.equivOfRoot pb' h₁ h₂).symm = pb'.equivOfRoot pb h₂ h₁ :=
  rfl
#align power_basis.equiv_of_root_symm PowerBasis.equivOfRoot_symm

/-- `pb.equivOfMinpoly pb' h` is an equivalence of algebras with the same power basis,
where "the same" means that they have identical minimal polynomials.

See also `PowerBasis.equivOfRoot` which takes the hypothesis that each generator is a root of the
other basis' minimal polynomial; `PowerBasis.equivOfRoot` is more general if `A` is not a field.
-/
@[simps! (config := { isSimp := false }) apply]
noncomputable def equivOfMinpoly (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h : minpoly A pb.gen = minpoly A pb'.gen) : S ≃ₐ[A] S' :=
  pb.equivOfRoot pb' (h ▸ minpoly.aeval _ _) (h.symm ▸ minpoly.aeval _ _)
#align power_basis.equiv_of_minpoly PowerBasis.equivOfMinpoly

@[simp]
theorem equivOfMinpoly_aeval (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h : minpoly A pb.gen = minpoly A pb'.gen) (f : A[X]) :
    pb.equivOfMinpoly pb' h (aeval pb.gen f) = aeval pb'.gen f :=
  pb.equivOfRoot_aeval pb' _ _ _
#align power_basis.equiv_of_minpoly_aeval PowerBasis.equivOfMinpoly_aeval

@[simp]
theorem equivOfMinpoly_gen (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h : minpoly A pb.gen = minpoly A pb'.gen) : pb.equivOfMinpoly pb' h pb.gen = pb'.gen :=
  pb.equivOfRoot_gen pb' _ _
#align power_basis.equiv_of_minpoly_gen PowerBasis.equivOfMinpoly_gen

@[simp]
theorem equivOfMinpoly_symm (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h : minpoly A pb.gen = minpoly A pb'.gen) :
    (pb.equivOfMinpoly pb' h).symm = pb'.equivOfMinpoly pb h.symm :=
  rfl
#align power_basis.equiv_of_minpoly_symm PowerBasis.equivOfMinpoly_symm

end Equiv

end PowerBasis

open PowerBasis

/-- Useful lemma to show `x` generates a power basis:
the powers of `x` less than the degree of `x`'s minimal polynomial are linearly independent. -/
theorem linearIndependent_pow [Algebra K S] (x : S) :
    LinearIndependent K fun i : Fin (minpoly K x).natDegree => x ^ (i : ℕ) := by
  by_cases IsIntegral K x; swap
  · rw [minpoly.eq_zero h, natDegree_zero]
    exact linearIndependent_empty_type
  refine' Fintype.linearIndependent_iff.2 fun g hg i => _
  simp only at hg
  simp_rw [Algebra.smul_def, ← aeval_monomial, ← map_sum] at hg
  apply (fun hn0 => (minpoly.degree_le_of_ne_zero K x (mt (fun h0 => ?_) hn0) hg).not_lt).mtr
  · simp_rw [← C_mul_X_pow_eq_monomial]
    exact (degree_eq_natDegree <| minpoly.ne_zero h).symm ▸ degree_sum_fin_lt _
  · apply_fun lcoeff K i at h0
    simp_rw [map_sum, lcoeff_apply, coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq'] at h0
    exact (if_pos <| Finset.mem_univ _).symm.trans h0
#align linear_independent_pow linearIndependent_pow

theorem IsIntegral.mem_span_pow [Nontrivial R] {x y : S} (hx : IsIntegral R x)
    (hy : ∃ f : R[X], y = aeval x f) :
    y ∈ Submodule.span R (Set.range fun i : Fin (minpoly R x).natDegree => x ^ (i : ℕ)) := by
  obtain ⟨f, rfl⟩ := hy
  apply mem_span_pow'.mpr _
  have := minpoly.monic hx
  refine' ⟨f %ₘ minpoly R x, (degree_modByMonic_lt _ this).trans_le degree_le_natDegree, _⟩
  conv_lhs => rw [← modByMonic_add_div f this]
  simp only [add_zero, MulZeroClass.zero_mul, minpoly.aeval, aeval_add, AlgHom.map_mul]
#align is_integral.mem_span_pow IsIntegral.mem_span_pow

namespace PowerBasis

section Map

variable {S' : Type*} [CommRing S'] [Algebra R S']

/-- `PowerBasis.map pb (e : S ≃ₐ[R] S')` is the power basis for `S'` generated by `e pb.gen`. -/
@[simps dim gen basis]
noncomputable def map (pb : PowerBasis R S) (e : S ≃ₐ[R] S') : PowerBasis R S' where
  dim := pb.dim
  basis := pb.basis.map e.toLinearEquiv
  gen := e pb.gen
  basis_eq_pow i := by rw [Basis.map_apply, pb.basis_eq_pow, e.toLinearEquiv_apply, e.map_pow]
#align power_basis.map PowerBasis.map

variable [Algebra A S] [Algebra A S']

-- @[simp] -- Porting note: simp can prove this
theorem minpolyGen_map (pb : PowerBasis A S) (e : S ≃ₐ[A] S') :
    (pb.map e).minpolyGen = pb.minpolyGen := by
  dsimp only [minpolyGen, map_dim]
  -- Turn `Fin (pb.map e).dim` into `Fin pb.dim`
  simp only [LinearEquiv.trans_apply, map_basis, Basis.map_repr, map_gen,
    AlgEquiv.toLinearEquiv_apply, e.toLinearEquiv_symm, AlgEquiv.map_pow,
    AlgEquiv.symm_apply_apply, sub_right_inj]
#align power_basis.minpoly_gen_map PowerBasis.minpolyGen_map

@[simp]
theorem equivOfRoot_map (pb : PowerBasis A S) (e : S ≃ₐ[A] S') (h₁ h₂) :
    pb.equivOfRoot (pb.map e) h₁ h₂ = e := by
  ext x
  obtain ⟨f, rfl⟩ := pb.exists_eq_aeval' x
  simp [aeval_algEquiv]
#align power_basis.equiv_of_root_map PowerBasis.equivOfRoot_map

@[simp]
theorem equivOfMinpoly_map (pb : PowerBasis A S) (e : S ≃ₐ[A] S')
    (h : minpoly A pb.gen = minpoly A (pb.map e).gen) : pb.equivOfMinpoly (pb.map e) h = e :=
  pb.equivOfRoot_map _ _ _
#align power_basis.equiv_of_minpoly_map PowerBasis.equivOfMinpoly_map

end Map

section Adjoin

open Algebra

theorem adjoin_gen_eq_top (B : PowerBasis R S) : adjoin R ({B.gen} : Set S) = ⊤ := by
  rw [← toSubmodule_eq_top, _root_.eq_top_iff, ← B.basis.span_eq, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  rw [B.basis_eq_pow i]
  exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
#align power_basis.adjoin_gen_eq_top PowerBasis.adjoin_gen_eq_top

theorem adjoin_eq_top_of_gen_mem_adjoin {B : PowerBasis R S} {x : S}
    (hx : B.gen ∈ adjoin R ({x} : Set S)) : adjoin R ({x} : Set S) = ⊤ := by
  rw [_root_.eq_top_iff, ← B.adjoin_gen_eq_top]
  refine' adjoin_le _
  simp [hx]
#align power_basis.adjoin_eq_top_of_gen_mem_adjoin PowerBasis.adjoin_eq_top_of_gen_mem_adjoin

end Adjoin

end PowerBasis

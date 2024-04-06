import Mathlib.NumberTheory.NumberField.Units

noncomputable section Ideal

open nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDomain R]

example {R : Type*} [CommRing R] [IsDomain R] :
    Quotient (MulAction.orbitRel Rˣ R) ≃ {I : Ideal R | Submodule.IsPrincipal I} := by
  have h_main : ∀ ⦃x : R⦄, ∀ ⦃y:R⦄,
      y ∈ MulAction.orbit Rˣ x ↔ Ideal.span {x} = Ideal.span {y} := fun x y ↦ by
    simp_rw [Ideal.span_singleton_eq_span_singleton, MulAction.orbit, Set.mem_range, Associated,
    mul_comm x _]
    rfl
  refine Equiv.ofBijective ?_ ⟨?_, fun ⟨I, hI⟩ ↦ ?_⟩
  · exact Quotient.lift (fun x ↦ ⟨Ideal.span {x}, ⟨x, rfl⟩⟩)
      fun _ _ h ↦ Subtype.mk_eq_mk.mpr (h_main.mp h).symm
  · rintro ⟨_⟩ ⟨_⟩ h
    exact Quotient.sound <| h_main.mpr ((Subtype.mk_eq_mk.mp h).symm)
  · obtain ⟨x, hx⟩ := hI
    exact ⟨⟦x⟧, Subtype.mk_eq_mk.mpr hx.symm⟩

end Ideal

variable {K : Type*} [Field K] [NumberField K]

open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem FiniteDimensional

open scoped BigOperators Classical

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

section Embedding  -- Move this to `Embeddings`

theorem NumberField.InfinitePlace.norm_embedding_eq_of_isReal {K : Type*} [Field K]
    {w : NumberField.InfinitePlace K} (hw : NumberField.InfinitePlace.IsReal w) (x : K) :
    ‖embedding_of_isReal hw x‖ = w x := by
  rw [← norm_embedding_eq, ← embedding_of_isReal_apply hw, Complex.norm_real]

end Embedding

noncomputable section Basic -- Move this to `CanonicalEmbedding.Basic`

namespace NumberField

def mixedEmbedding.norm : (E K) →*₀ ℝ where
  toFun := fun x ↦ (∏ w, ‖x.1 w‖) * ∏ w, ‖x.2 w‖ ^ 2
  map_one' := by simp only [Prod.fst_one, Pi.one_apply, norm_one, Finset.prod_const_one,
    Prod.snd_one, one_pow, mul_one]
  map_zero' := by
    simp_rw [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, norm_zero, zero_pow (two_ne_zero),
      mul_eq_zero, Finset.prod_const, pow_eq_zero_iff', true_and, Finset.card_univ]
    by_contra!
    have : finrank ℚ K = 0 := by
      rw [← card_add_two_mul_card_eq_rank, NrRealPlaces, NrComplexPlaces, this.1, this.2]
    exact ne_of_gt finrank_pos this
  map_mul' _ _ := by simp only [Prod.fst_mul, Pi.mul_apply, norm_mul, Real.norm_eq_abs,
      Finset.prod_mul_distrib, Prod.snd_mul, Complex.norm_eq_abs, mul_pow]; ring

theorem mixedEmbedding.norm_ne_zero {x : E K} :
    norm x ≠ 0 ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ w, x.2 w ≠ 0) := by
  simp_rw [norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_true_left, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]

theorem mixedEmbedding.norm_const (c : ℝ) :
    norm ((fun _ ↦ c, fun _ ↦ c) : (E K)) = |c| ^ finrank ℚ K := by
  simp_rw [norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Real.norm_eq_abs, Complex.norm_eq_abs,
    Complex.abs_ofReal, Finset.prod_const, ← pow_mul, ← card_add_two_mul_card_eq_rank,
    Finset.card_univ, pow_add]

theorem mixedEmbedding.norm_smul (c : ℝ) (x : E K) :
    norm (c • x) = |c| ^ finrank ℚ K * (norm x) := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (E K)) * x by rfl, map_mul, norm_const]

@[simp]
theorem mixedEmbedding.norm_eq_norm (x : K) :
    norm (mixedEmbedding K x) = |Algebra.norm ℚ x| := by
  simp_rw [← prod_eq_abs_norm, mixedEmbedding.norm, mixedEmbedding, RingHom.prod_apply,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Pi.ringHom_apply, norm_embedding_eq,
    norm_embedding_eq_of_isReal]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K ↦ IsReal w)]
  congr 1
  · exact Finset.prod_congr rfl (fun w _ ↦ by rw [mult, if_pos w.prop, pow_one])
  · refine (Fintype.prod_equiv (Equiv.subtypeEquivRight ?_) _ _ (fun w ↦ ?_)).symm
    · exact fun _ ↦ not_isReal_iff_isComplex
    · rw [Equiv.subtypeEquivRight_apply_coe, mult, if_neg w.prop]

theorem mixedEmbedding.norm_unit (u : (𝓞 K)ˣ) :
    norm (mixedEmbedding K u) = 1 := by
  rw [norm_eq_norm, show |(Algebra.norm ℚ) (u : K)| = 1
      by exact NumberField.isUnit_iff_norm.mp (Units.isUnit u), Rat.cast_one]

end NumberField

end Basic

noncomputable section UnitSMul

instance : SMul (𝓞 K)ˣ (E K) where
  smul := fun u x ↦ (mixedEmbedding K u) * x

instance : MulAction (𝓞 K)ˣ (E K) where
  one_smul := fun _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, Units.coe_mul, map_mul, mul_assoc]

theorem NumberField.mixedEmbedding.unitSMul_def (u : (𝓞 K)ˣ) (x : E K) :
    u • x = (mixedEmbedding K u) * x := rfl

end UnitSMul

namespace NumberField.mixedEmbedding

noncomputable section logMap

open NumberField.Units

def logMap (x : E K) : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun w ↦
    if hw : IsReal w.val then
      Real.log ‖x.1 ⟨w.val, hw⟩‖ - Real.log (norm x) * (finrank ℚ K : ℝ)⁻¹
    else
      2 * (Real.log ‖x.2 ⟨w.val, not_isReal_iff_isComplex.mp hw⟩‖ -
        Real.log (norm x) * (finrank ℚ K : ℝ)⁻¹)

theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K u := by
  ext
  simp_rw [logMap, norm_unit, Real.log_one, zero_mul, sub_zero, logEmbedding, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, mult, Nat.cast_ite, ite_mul, Nat.cast_one, one_mul, Nat.cast_ofNat,
    mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply, norm_embedding_eq,
    norm_embedding_eq_of_isReal]
  rfl

theorem logMap_zero : logMap (0 : E K) = 0 := by
  ext
  simp_rw [logMap, Prod.fst_zero, Prod.snd_zero, map_zero, Pi.zero_apply, norm_zero, Real.log_zero,
    zero_mul, sub_zero, mul_zero, dite_eq_ite, ite_self]

theorem logMap_torsion_unitSMul_eq (x : E K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap, unitSMul_def, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, map_mul,
    norm_eq_norm, mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply,
    show |(Algebra.norm ℚ) (ζ : K)| = 1 by exact NumberField.isUnit_iff_norm.mp (Units.isUnit ζ),
    Rat.cast_one, one_mul, norm_embedding_eq, norm_embedding_eq_of_isReal, (mem_torsion K).mp hζ,
    one_mul]

theorem logMap_mul {x y : E K} (hx : norm x ≠ 0) (hy : norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap]
  split_ifs with hw
  · rw [Prod.fst_mul, Pi.mul_apply, norm_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
    · ring
    · exact norm_ne_zero_iff.mpr <| (norm_ne_zero.mp hx).1 ⟨_, hw⟩
    · exact norm_ne_zero_iff.mpr <| (norm_ne_zero.mp hy).1 ⟨_, hw⟩
  · replace hw := not_isReal_iff_isComplex.mp hw
    rw [Prod.snd_mul, Pi.mul_apply, norm_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
    · ring
    · exact norm_ne_zero_iff.mpr <| (norm_ne_zero.mp hx).2 ⟨_, hw⟩
    · exact norm_ne_zero_iff.mpr <| (norm_ne_zero.mp hy).2 ⟨_, hw⟩

theorem logMap_unitSMul_eq (u : (𝓞 K)ˣ) {x : E K} (hx : norm x ≠ 0) :
    logMap (u • x) = logEmbedding K u + logMap x := by
  rw [unitSMul_def, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

theorem logMap_smul_eq_self {x : E K} {c : ℝ} (hx : norm x ≠ 0) (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (E K)) * x by rfl, logMap_mul _ hx, add_left_eq_self]
  ext
  have hr : (finrank ℚ K : ℝ) ≠ 0 :=  Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
  simp_rw [logMap, Pi.zero_apply, norm_const, Real.log_pow, mul_comm, inv_mul_cancel_left₀ hr,
    Real.norm_eq_abs, Complex.norm_eq_abs,  Complex.abs_ofReal, sub_self, mul_zero, dite_eq_ite,
    ite_self]
  rw [norm_const]
  exact pow_ne_zero _ (abs_ne_zero.mpr hc)

end logMap

open NumberField.Units

variable (K)

def fundamentalCone : Set (E K) := by
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  exact logMap⁻¹' (Zspan.fundamentalDomain B)

theorem fundamentalCone_zero_mem : 0 ∈ fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_preimage, Zspan.mem_fundamentalDomain, logMap_zero, map_zero,
    Finsupp.coe_zero, Pi.zero_apply, Set.left_mem_Ico, zero_lt_one, implies_true]

variable {K}

theorem fundamentalCone_smul_mem_of_mem {x : E K} (hx : norm x ≠ 0) (hx' : x ∈ fundamentalCone K)
    (c : ℝ) : c • x ∈ fundamentalCone K := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    exact  fundamentalCone_zero_mem K
  · rwa [fundamentalCone, Set.mem_preimage, logMap_smul_eq_self hx hc]

theorem fundamentalCone_exists_unitSMul_mem {x : E K} (hx : norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ Zspan.fundamentalDomain B
  · exact ⟨u, by rwa [fundamentalCone, Set.mem_preimage, logMap_unitSMul_eq u hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Basis.ofZlatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩

theorem fundamentalCone_torsion_unitSMul_mem_of_mem' {x : E K} (hx : norm x ≠ 0)
    (hx' : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  rwa [fundamentalCone, Set.mem_preimage, logMap_unitSMul_eq _ hx,
    logEmbedding_eq_zero_iff.mpr hζ, zero_add]

theorem fundamentalCone_torsion_unitSMul_mem_of_mem {x : E K}
    (hx' : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  rwa [fundamentalCone, Set.mem_preimage, logMap_torsion_unitSMul_eq _ hζ]

theorem fundamentalCone_unitSMul_mem_iff {x : E K} (hx : norm x ≠ 0) (hx' : x ∈ fundamentalCone K)
    (u : (𝓞 K)ˣ) : u • x ∈ fundamentalCone K ↔ u ∈ torsion K := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← logEmbedding_eq_zero_iff]
    let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
    refine (Subtype.mk_eq_mk (h := ?_) (h' := ?_)).mp <|
      ExistsUnique.unique (Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)) ?_ ?_
    · change logEmbedding K u ∈ (Submodule.span ℤ (Set.range B)).toAddSubgroup
      rw [Basis.ofZlatticeBasis_span ℝ (unitLattice K)]
      exact ⟨u, trivial, rfl⟩
    · exact zero_mem _
    · rwa [fundamentalCone, Set.mem_preimage, logMap_unitSMul_eq _ hx] at h
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
      rwa [fundamentalCone, Set.mem_preimage] at hx'
  · exact fundamentalCone_torsion_unitSMul_mem_of_mem hx' h

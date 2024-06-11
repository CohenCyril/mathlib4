/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Laura Capuano, Amos Turchet
-/
import Mathlib.Analysis.Matrix
import Mathlib.Data.Pi.Interval

/-!
# Siegel's Lemma, first version for ℤ

In this file we introduce and prove Siegel's Lemma in its most basic version. This is a fundamental
tool in diophantine approximation and transcendency and says that there exists a "small" integral
non-zero solution of a non-trivial underdetermined system of linear equations with integer
coefficients.

## Notation

 - `‖_‖ ` : Matrix.seminormedAddCommGroup is the sup norm, the maximum of the absolute values of
 the entries of the matrix
## References

See [M. Hindry and J. Silverman, Diophantine Geometry: an Introduction][hindrysilverman00] .
-/

/- We set ‖⬝‖ to be Matrix.seminormedAddCommGroup  -/
attribute [local instance] Matrix.seminormedAddCommGroup

namespace Matrix

/-- The norm of a matrix is the sup of the sup of the nnnorm of the entries -/
  lemma norm_eq_sup_sup_nnnorm (A : Matrix m n α) :
    ‖A‖ = Finset.sup Finset.univ fun i ↦ Finset.sup Finset.univ fun j ↦ ‖A i j‖₊ := by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def]

open Finset

/-- The norm of an integral matrix as the sup of the sup of the natAbs of the entries -/
def natNorm (A : Matrix m n ℤ) : ℕ := sup univ fun i ↦ sup univ fun j ↦ (A i j).natAbs

/-- The norm of an integral matrix is equal to the natNorm -/
lemma norm_eq_natNorm (A : Matrix m n ℤ) : ‖A‖ = natNorm A := by
  simp only [norm_eq_sup_sup_nnnorm, ← NNReal.coe_natCast, bot_eq_zero', CharP.cast_eq_zero,
    comp_sup_eq_sup_comp_of_is_total Nat.cast Nat.mono_cast, Function.comp_def, NNReal.coe_inj,
    natNorm]
  congr! with i j
  exact (NNReal.natCast_natAbs (A i j)).symm

/-- The natNorm of a non-zero integral matrix is at least 1-/
lemma one_le_natNorm_of_ne_zero (A : Matrix m n ℤ) (hA_ne_zero : A ≠ 0) : 1 ≤ natNorm A := by
  simp only [← norm_pos_iff', norm_eq_natNorm A, Nat.cast_pos] at hA_ne_zero
  linarith

end Matrix

open Finset Matrix

variable (m n a : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) (hn : m < n)
(hm : 0 < m)

--Some definitions and relative properties

local notation3 "e" => m / ((n : ℝ ) - m) --exponent
local notation3 "B" => Nat.floor (((n : ℝ) * ‖A‖) ^ e)
-- B' is the vector with all components = B
local notation3 "B'" => fun _ : Fin n => (B  : ℤ)
-- T is the box [0 B]^n
local notation3 "T" =>  Finset.Icc 0 B'


local notation3  "P" => fun i : Fin m => (∑ j : Fin n, B * posPart (A i j))
local notation3  "N" => fun i : Fin m =>  (∑ j : Fin n, B * (- negPart (A i j)))
   -- S is the box where the image of T goes
local notation3  "S" => Finset.Icc N P
section preparation

--In order to apply Pigeohole we need:  (1) ∀ v ∈  T, (A.mulVec v) ∈  S and (2) S.card < T.card

--(1)

private lemma image_T_subset_S : ∀ v ∈ T, (A.mulVec v) ∈ S := by
  intro v hv
  rw [Finset.mem_Icc] at hv
  rw [Finset.mem_Icc]
  have mulVec_def : A.mulVec v =
      fun i => Finset.sum Finset.univ fun (j : (Fin n)) => A i j * v j := by rfl
  rw [mulVec_def] --unfolds def of MulVec
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ --this gives 2 goals
  all_goals simp only [mul_neg]
  all_goals gcongr (∑ _ : Fin n, ?_) with j _ -- gets rid of sums
  all_goals rw [← mul_comm (v j)] -- moves A i j to the right of the products
  all_goals by_cases hsign : 0 ≤ A i j   --we have to distinguish cases: we have now 4 goals
  · rw [negPart_eq_zero.2 hsign]
    exact mul_nonneg (hv.1 j) hsign
  · rw [not_le] at hsign
    rw [negPart_eq_neg.2 (le_of_lt hsign)]
    simp only [mul_neg, neg_neg]
    exact mul_le_mul_of_nonpos_right (hv.2 j) (le_of_lt hsign)
  · rw [posPart_eq_self.2  hsign]
    exact mul_le_mul_of_nonneg_right (hv.2 j) hsign
  · rw [not_le] at hsign
    rw [posPart_eq_zero.2 (le_of_lt hsign)]
    exact mul_nonpos_of_nonneg_of_nonpos (hv.1 j) (le_of_lt hsign)

--Preparation for (2)

private lemma card_T_eq : (T).card = (B+1)^n := by
   rw [Pi.card_Icc 0 B']
   simp only [Pi.zero_apply, Int.card_Icc, sub_zero, Int.toNat_ofNat_add_one, prod_const, card_fin]

open Nat Real
variable  (hA : A ≠ 0 ) (ha : ‖A‖ = ↑a)

--S is not empty
private lemma N_le_P_add_one : ∀ j : Fin m, N j ≤ P j + 1 := by
  intro j
  calc N j ≤ 0 := by
              apply Finset.sum_nonpos
              intro i _
              simp only [mul_neg, Left.neg_nonpos_iff]
              exact mul_nonneg (cast_nonneg B) (negPart_nonneg (A j i))
        _ ≤ P j + 1 := by
              apply le_trans ?_ (Int.le_add_one (le_refl P j))
              apply Finset.sum_nonneg
              intro i _
              exact mul_nonneg (cast_nonneg B) (posPart_nonneg (A j i))

private lemma card_S_eq : (Finset.Icc N P).card = (∏ i : Fin m, (P i - N i + 1)):= by
   rw [Pi.card_Icc N P,Nat.cast_prod]
   congr
   ext j
   rw [Int.card_Icc_of_le (N j) (P j) (N_le_P_add_one m n A j)]
   ring

private lemma hcompexp : (e * (n - m)) = m := by
      apply div_mul_cancel₀
      apply sub_ne_zero_of_ne
      simp only [ne_eq, Nat.cast_inj]
      linarith only [hn]

variable (h_one_le_a : 1 ≤ a)

-- (2)

private lemma card_S_lt_card_T : (S).card < (T).card := by
      zify
      rw [card_T_eq, card_S_eq]
      calc
      ∏ i : Fin m, (P i - N i + 1) ≤ (n * a * B + 1) ^ m := by
            rw [← Fin.prod_const m ((n * a * B + 1) : ℤ)]
            apply Finset.prod_le_prod  --2 goals
            all_goals intro i _
            linarith only [N_le_P_add_one m n A i] --first goal done
            simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add, cast_succ, cast_mul,
              add_le_add_iff_right]
            rw [(mul_sum Finset.univ (fun i_1 => (A i i_1)⁺) ↑B).symm,
                (mul_sum Finset.univ (fun i_1 => (A i i_1)⁻) ↑B).symm, ← mul_add,
                mul_comm ((n : ℤ) * a) (B : ℤ)]
            apply mul_le_mul_of_nonneg_left _ (by simp only [cast_nonneg])
            rw [← Finset.sum_add_distrib]
            have h1 : n * (a : ℤ) = ∑ _ : Fin n, (a : ℤ) := by
                simp only [sum_const, card_fin, nsmul_eq_mul]
            rw [h1]
            gcongr with j _
            rw [posPart_add_negPart (A i j)]
            have h2 : |A i j| ≤ (a : ℝ) := by
                      rw [Int.cast_abs, ← Int.norm_eq_abs, ← ha]
                      exact norm_entry_le_entrywise_sup_norm A
            exact Int.cast_le.1 h2
         _  ≤ (n * a) ^ m * (B + 1) ^ m := by
            rw [← mul_pow (n * (a : ℤ)) ((B : ℤ) + 1) m]
            apply pow_le_pow_left (Int.ofNat_nonneg (n*a*B+1))
            rw [mul_add]
            simp only [cast_succ, cast_mul, mul_one, add_le_add_iff_left]
            exact_mod_cast one_le_mul (one_le_of_lt hn) h_one_le_a
         _ < (B + 1) ^ (n - m) * (B + 1) ^ m := by
            simp only [gt_iff_lt, Int.succ_ofNat_pos, pow_pos, mul_lt_mul_right]
            have h1 : ((n * a) ^ (m / ((n : ℝ) - m))) ^ ((n : ℝ) - m) <
                ((B + 1): ℝ) ^ ((n : ℝ) - m) := by
              apply Real.rpow_lt_rpow /- this creates 3 goals: 0 ≤ (↑n * ↑a) ^ (↑m / (↑n - ↑m)),
                                          (↑n * ↑a) ^ (↑m / (↑n - ↑m)) < ↑B + 1 and 0 < ↑n - ↑m -/
              · apply rpow_nonneg
                exact_mod_cast Nat.zero_le (n * a)
              · rw [← ha]
                exact lt_floor_add_one ((n * ‖A‖) ^ (m / ((n : ℝ ) - ↑m)))
              · rw [sub_pos, cast_lt]
                exact hn
            have h2 : ((n * a) ^ (m / ((n : ℝ) - m))) ^ ((n : ℝ) - m) =
                ((n : ℝ) * a) ^ (m : ℝ) := by
              rw [← rpow_mul (by exact_mod_cast Nat.zero_le (n * a)) (m / (n - m)) (n - m),
                hcompexp m n hn]
            rw [h2] at h1
            nth_rw 2 [← Nat.cast_sub (le_of_lt hn)] at h1
            rw [rpow_natCast ((↑B + 1)) (n - m), rpow_natCast ] at h1
            exact_mod_cast h1
         _  = ↑((B + 1) ^ n) := by
            rw [mul_comm,pow_mul_pow_sub]
            simp only [cast_pow, cast_add, cast_one]
            exact (le_of_lt hn)

--end (2)

end preparation

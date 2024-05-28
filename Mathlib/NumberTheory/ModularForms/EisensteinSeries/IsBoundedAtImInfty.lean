/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.

## Outline of argument

We need to bound the value of the Eisenstein series (acted on by `A : SL(2,ℤ)`)
at a given point `z` in the upper half plane. Since these are modular forms of level `Γ(N)`,
it suffices to prove this for `z ∈ verticalStrip N z.im`.

We can then, first observe that the slash action just changes our `a` to `(a ᵥ* A)` and
we then use our bounds for Eisenstein series in these vertical strips to get the result.
-/

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane Set Filter Function Complex Matrix
  SlashInvariantForm

open scoped Topology BigOperators Nat Classical MatrixGroups

namespace EisensteinSeries

lemma norm_eisSummand_Summable (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖ := by
  have hk' : (2 : ℝ) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : ℝ)).of_nonneg_of_le
    (fun _ => Complex.abs.nonneg _)
  intro b
  simp only [eisSummand, Fin.isValue, one_div, map_inv₀, map_zpow₀]
  rw [← inv_zpow, inv_zpow', ← Real.rpow_intCast, Int.cast_neg]
  have hk0 : 0 ≤ (k : ℝ) := by norm_cast; omega
  exact summand_bound z hk0 b

/-- The absolute value of the restricted sum is less than the full sum of the absolute values. -/
lemma abs_le_tsum_abs (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ):
    Complex.abs (eisensteinSeries a k z) ≤ ∑' (x : Fin 2 → ℤ), Complex.abs (eisSummand k x z) := by
  simp_rw [← Complex.norm_eq_abs, eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ((norm_eisSummand_Summable k hk z).subtype _))
    (tsum_subtype_le (fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖) _ (fun _ ↦ norm_nonneg _)
      (norm_eisSummand_Summable k hk z))

/-- Eisenstein seires are bounded at infinity. -/
theorem eisensteinSeries_IsBoundedAtImInfty {N : ℕ+} (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k)
    (A : SL(2, ℤ)) : IsBoundedAtImInfty ((eisensteinSeries_SIF a k).toFun ∣[k] A) := by
    simp_rw [UpperHalfPlane.bounded_mem, eisensteinSeries_SIF] at *
    refine ⟨∑'(x : Fin 2 → ℤ), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
    intro z hz
    obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z N.2)
    rw [eisensteinSeries_slash_apply, ← eisensteinSeries_SIF_apply,
      ← T_zpow_width_invariant N k n (eisensteinSeries_SIF (a ᵥ* A) k) z]
    let Z := (ModularGroup.T ^ ((N : ℤ) * n)) • z
    apply le_trans (abs_le_tsum_abs N (a ᵥ* A) k hk Z)
    apply tsum_le_tsum _ (norm_eisSummand_Summable k hk _)
    · have hk' : (2 : ℝ) < k := by norm_cast
      have := (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
      simp_rw [← Int.cast_neg, Real.rpow_intCast] at this
      exact this
    · intro x
      have hk0 : 0 ≤ (k : ℝ) := by norm_cast; omega
      have := summand_bound_of_mem_verticalStrip (z := Z) hk0 x (A := N) (B := 2) (two_pos)
        (verticalStrip_anti_right (N : ℕ) hz hn)
      simp_rw [eisSummand, Fin.isValue, one_div, norm_eq_abs, map_inv₀, map_zpow₀, ge_iff_le,
        ← inv_zpow, inv_zpow', ← Real.rpow_intCast, Int.cast_neg]
      exact this

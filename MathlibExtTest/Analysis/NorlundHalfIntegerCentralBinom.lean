/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.CentralBinomDigammaSeries

/-! # Checks of the central binomial series at `m = 1` and `m = 2` -/

open Finset MetaMathlibExt

private noncomputable def coeff (n : ℕ) : ℝ :=
  4 ^ n / (((n : ℝ) + 1) * ((n + 2).choose 2 : ℝ) * ((n + 2).centralBinom : ℝ))

private lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  unfold coeff
  positivity

private lemma coeff_step (n : ℕ) :
    coeff (n + 1) * (((n : ℝ) + 2) * (2 * (n : ℝ) + 5)) =
      coeff n * (2 * ((n : ℝ) + 1) ^ 2) := by
  have hc (j : ℕ) : ((j + 2).choose 2 : ℝ) = ((j : ℝ) + 2) * ((j : ℝ) + 1) / 2 := by
    have h : 2 * (j + 2).choose 2 = (j + 2) * (j + 1) := by
      simpa [Nat.descFactorial_succ, mul_comm] using (Nat.descFactorial_eq_factorial_mul_choose
        (j + 2) 2).symm
    have hr : 2 * ((j + 2).choose 2 : ℝ) = ((j : ℝ) + 2) * ((j : ℝ) + 1) := by exact_mod_cast h
    linarith only [hr]
  have hb : ((n + 1 + 2).centralBinom : ℝ) =
      2 * (2 * (n : ℝ) + 5) * ((n + 2).centralBinom : ℝ) / ((n : ℝ) + 3) := by
    apply (eq_div_iff (by positivity)).2
    have h := congrArg (fun j : ℕ ↦ (j : ℝ)) (Nat.succ_mul_centralBinom_succ (n + 2))
    rw [show n + 1 + 2 = n + 2 + 1 by omega]
    push_cast at h
    linear_combination h
  simp only [coeff, hc, hb, pow_succ, Nat.cast_succ]
  field_simp
  ring

-- Compute a finite prefix, then bound the tail by telescoping differences of `(n+1) * coeff n`.
-- This check does not invoke the new series identity or any of its proof lemmas.
example : (21 / 100 : ℝ) < ∑' n, coeff n ∧ (∑' n, coeff n) < 6 / 25 := by
  let b (n : ℕ) : ℝ := ((n : ℝ) + 1) * coeff n
  have hb (n : ℕ) : 0 ≤ b n := mul_nonneg (by positivity) (coeff_nonneg n)
  have hstep (n : ℕ) (hn : 2 ≤ n) : coeff n ≤ b n - b (n + 1) := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp only [b]
    push_cast
    refine le_of_mul_le_mul_right ?_ (show 0 < 2 * (n : ℝ) + 5 by positivity)
    nlinarith only [coeff_step n, mul_nonneg (coeff_nonneg n) (sub_nonneg.mpr hn')]
  have hbound (N : ℕ) : ∑ n ∈ range N, coeff (n + 4) ≤ b 4 := by
    calc
      _ ≤ ∑ n ∈ range N, (b (n + 4) - b (n + 1 + 4)) := by
        exact sum_le_sum fun n _ ↦ by simpa only [Nat.add_right_comm] using hstep (n + 4) (by omega)
      _ = b 4 - b (N + 4) := sum_range_sub' (fun n ↦ b (n + 4)) N
      _ ≤ b 4 := sub_le_self _ (hb _)
  have hs := summable_of_sum_range_le (fun n ↦ coeff_nonneg (n + 4)) hbound
  have htotal := (hasSum_nat_add_iff 4).1 hs.hasSum
  have hprefix : ∑ n ∈ range 4, coeff n = 23 / 105 := by
    norm_num [sum_range_succ, coeff, Nat.centralBinom, Nat.choose]
  have htail : b 4 < 2 / 100 := by
    norm_num [b, coeff, Nat.centralBinom, Nat.choose]
  constructor
  · have hle := htotal.summable.sum_le_tsum (range 4) (fun n _ ↦ coeff_nonneg n)
    rw [hprefix] at hle
    linarith
  · rw [htotal.tsum_eq, hprefix]
    linarith [hs.tsum_le_of_sum_range_le hbound]

-- Independently bound the proposed value with certified bounds for π, including the correction.
example :
    let value := (2 : ℝ) / 4 *
      (3 * (Real.pi ^ 2 / 6) - 4 * ∑ j ∈ range (2 - 1), 1 / (2 * (j : ℝ) + 1) ^ 2) /
      ((2 - 1 : ℕ).centralBinom : ℝ)
    (21 / 100 : ℝ) < value ∧ value < 6 / 25 := by
  change (21 / 100 : ℝ) < _ ∧ _ < 6 / 25
  norm_num [Nat.centralBinom, Nat.choose]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr Real.pi_gt_d2) (show 0 < Real.pi + 3.14 by positivity)]
  · nlinarith [mul_pos (sub_pos.mpr Real.pi_lt_d4) (show 0 < 3.1416 + Real.pi by positivity)]

-- The exact formula at `m = 2` is also available to callers of the public theorem.
example : ∑' n, coeff n = Real.pi ^ 2 / 8 - 1 := by
  unfold coeff
  rw [tsum_four_pow_div_succ_mul_choose_mul_centralBinom (m := 2) (by decide)]
  norm_num [Nat.centralBinom, Nat.choose]
  ring

-- At `m = 1`, the finite correction is empty and `Nat.centralBinom 0 = 1`.
example :
    ∑' n : ℕ, (4 : ℝ) ^ n / (((n : ℝ) + 1) ^ 2 * ((n + 1).centralBinom : ℝ)) =
      Real.pi ^ 2 / 8 := by
  have h := tsum_four_pow_div_succ_mul_choose_mul_centralBinom (m := 1) (by decide)
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, ← pow_two] at h
  rw [h]
  norm_num [Nat.centralBinom]
  ring

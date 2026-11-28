/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.TakagiDyadicMidpoint

/-! # Tests for the dyadic Takagi midpoint recurrence -/

open Finset MetaMathlibExt

-- On the sixteenth mesh, evaluate the first four terms of the coefficient series directly
-- and sum its constant-coefficient tail. This uses neither the recurrence nor the tent sum.
private theorem value_sixteenths (r : ℕ) :
    takagiNewdef r 3 = (∑ i ∈ range 4, (takagiEll r 3 (i + 1) : ℝ) / 2 ^ (i + 1)) +
      (∑ j ∈ range 4, (takagiBit r (3 - (j : ℤ)) : ℝ)) / 16 := by
  let f (i : ℕ) : ℝ := (takagiEll r 3 (i + 1) : ℝ) / 2 ^ (i + 1)
  let c : ℝ := (∑ j ∈ range 4, (takagiBit r (3 - (j : ℤ)) : ℝ)) / 16
  have hbit (i : ℕ) (hi : 4 ≤ i) : takagiBit r (3 - (i : ℤ)) = 0 :=
    takagiBit_neg _ _ (by omega)
  have hell (i : ℕ) : takagiEll r 3 (i + 4 + 1) =
      ∑ j ∈ range 4, takagiBit r (3 - (j : ℤ)) := by
    rw [takagiEll_succ, hbit _ (by omega), ite_eq_left rfl, add_comm i 4, sum_range_add]
    rw [sum_eq_zero (fun j _ ↦ hbit (4 + j) (by omega)), add_zero]
  have htail : HasSum (fun i ↦ f (i + 4)) c := by
    refine HasSum.congr_fun (hasSum_geometric_two' c) fun i ↦ ?_
    dsimp only [f, c]
    rw [hell, Nat.cast_sum, show i + 4 + 1 = 5 + i by omega, pow_add, div_div, div_div, ← mul_assoc]
    norm_num
  rw [takagiNewdef_eq]
  simpa only [add_comm c] using ((hasSum_nat_add_iff (f := f) 4).mp htail).tsum_eq

private noncomputable def midpointCorrection (r : ℕ) : ℝ :=
  takagiNewdef r 3 - (takagiNewdef (r - 1) 3 + takagiNewdef (r + 1) 3) / 2

-- Odd numerator, valuation one, valuation two, and the last interior point (whose next
-- neighbor is exactly 1). Compute the midpoint corrections from the series and the valuations.
example : midpointCorrection 1 = (1 - (padicValNat 2 1 : ℝ)) / 16 ∧
    midpointCorrection 2 = (1 - (padicValNat 2 2 : ℝ)) / 16 ∧
    midpointCorrection 4 = (1 - (padicValNat 2 4 : ℝ)) / 16 ∧
    midpointCorrection 15 = (1 - (padicValNat 2 15 : ℝ)) / 16 := by
  have h₁ : padicValNat 2 1 = 0 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  have h₂ : padicValNat 2 2 = 1 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  have h₄ : padicValNat 2 4 = 2 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  have h₁₅ : padicValNat 2 15 = 0 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  norm_num [midpointCorrection, h₁, h₂, h₄, h₁₅, value_sixteenths, sum_range_succ, takagiEll_succ,
    takagiBit_eq, Nat.testBit_eq_decide_div_mod_eq]

-- An API client can instantiate the public theorem at a point with a negative correction.
example : takagiNewdef 4 ((4 : ℤ) - 1) =
    (takagiNewdef (4 - 1) ((4 : ℤ) - 1) + takagiNewdef (4 + 1) ((4 : ℤ) - 1)) / 2 +
      (1 - (padicValNat 2 4 : ℝ)) / 2 ^ (4 : ℕ) :=
  takagi_dyadic_eq_midpoint_add 4 4 (by decide) (by decide)

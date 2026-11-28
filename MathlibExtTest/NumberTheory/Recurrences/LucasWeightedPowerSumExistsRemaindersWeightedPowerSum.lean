/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFib
import MathlibExt.NumberTheory.Recurrences.LucasWeightedPowerSumExistsRemaindersWeightedPowerSum

/-!
# Tests for weighted Lucas power-sum remainders

Concrete weighted Fibonacci sums exercise the linear case, the mixed-exponent case, and
the case where both exponents are at least two. The bounds on the explicit remainder are
also checked independently in two Fibonacci cases.
-/

namespace MathlibExtTest.NumberTheory.Recurrences
namespace LucasWeightedPowerSumExistsRemaindersWeightedPowerSum

open MetaMathlibExt

example :
    let α : ℝ := (1 + Real.sqrt 5) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < 16 * α ^ (-4 : ℝ) ∧ |R₂| < α ^ (-8 : ℝ) := by
  have hsol : ∑ j ∈ Finset.Icc (1 : ℕ) 4, (j : ℤ) * lucasU fibonacciLucasParams j ^ 1 =
      lucasU fibonacciLucasParams 8 ^ 1 := by decide
  obtain ⟨R₁, R₂, hR₁, hR₂, _⟩ := exists_remainders_weighted_power_sum
    fibonacciLucasParams (Or.inr rfl) (by decide) (by decide)
    (n := 8) (k := 4) (p := 1) (q := 1) (by decide) (by decide) (by decide) (by decide) hsol
  refine ⟨R₁, R₂, ?_, ?_⟩
  · convert hR₁ using 1
    norm_num [fibonacciLucasParams]
  · convert hR₂ using 1
    norm_num [fibonacciLucasParams]

example :
    let α : ℝ := (1 + Real.sqrt 5) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < 9 * α ^ (-3 : ℝ) ∧ |R₂| < 1 ∧
      (5 : ℝ) ^ ((1 : ℝ) / 2) * (3 * α - 4) / (α - 1) ^ 2 * α ^ 4 - α ^ 8 =
        5 * R₂ - 5 * R₁ - (5 : ℝ) ^ ((1 : ℝ) / 2) * α / (α - 1) ^ 2 := by
  have hsol : ∑ j ∈ Finset.Icc (1 : ℕ) 3, (j : ℤ) * lucasU fibonacciLucasParams j ^ 1 =
      lucasU fibonacciLucasParams 4 ^ 2 := by decide
  obtain ⟨R₁, R₂, hR₁, hR₂, hE⟩ := exists_remainders_weighted_power_sum
    fibonacciLucasParams (Or.inr rfl) (by decide) (by decide)
    (n := 4) (k := 3) (p := 1) (q := 2) (by decide) (by decide) (by decide) (by decide) hsol
  refine ⟨R₁, R₂, ?_, ?_, ?_⟩
  · convert hR₁ using 1
    norm_num [fibonacciLucasParams]
  · convert hR₂ using 1
    norm_num [fibonacciLucasParams]
  · convert hE using 1 <;> norm_num [fibonacciLucasParams]

example :
    let α : ℝ := (1 + Real.sqrt 5) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < 9 * α ^ (3 : ℝ) ∧ |R₂| < α ^ (4 : ℝ) := by
  have hsol : ∑ j ∈ Finset.Icc (1 : ℕ) 3, (j : ℤ) * lucasU fibonacciLucasParams j ^ 3 =
      lucasU fibonacciLucasParams 4 ^ 3 := by decide
  obtain ⟨R₁, R₂, hR₁, hR₂, _⟩ := exists_remainders_weighted_power_sum
    fibonacciLucasParams (Or.inr rfl) (by decide) (by decide)
    (n := 4) (k := 3) (p := 3) (q := 3) (by decide) (by decide) (by decide) (by decide) hsol
  refine ⟨R₁, R₂, ?_, ?_⟩
  · convert hR₁ using 1
    norm_num [fibonacciLucasParams]
  · convert hR₂ using 1
    norm_num [fibonacciLucasParams]

private theorem goldenRatio_eighth : Real.goldenRatio ^ (8 : ℕ) = 21 * Real.goldenRatio + 13 := by
  have h := Real.goldenRatio_mul_fib_succ_add_fib 7
  norm_num at h
  linarith only [h]

private theorem goldenRatio_bounds : (8 : ℝ) / 5 < Real.goldenRatio ∧
    Real.goldenRatio < 5 / 3 := by
  have hlo : (11 : ℝ) / 5 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 5 < (7 : ℝ) / 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  dsimp only [Real.goldenRatio]
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

-- Independent check for (n, k, p, q) = (8, 4, 1, 1): the sum equals F₈ = 21.
example : Real.sqrt 5 * |(lucasU fibonacciLucasParams 8 : ℝ) -
      Real.goldenRatio ^ (8 : ℕ) / Real.sqrt 5| < 144 * Real.goldenRatio ^ (-3 : ℝ) := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hU : lucasU fibonacciLucasParams 8 = 21 := by norm_num [lucasU_fibonacciLucasParams]
  have hφ : Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
    dsimp only [Real.goldenRatio]
    ring
  calc
    _ = |Real.sqrt 5 * ((lucasU fibonacciLucasParams 8 : ℝ) -
        Real.goldenRatio ^ (8 : ℕ) / Real.sqrt 5)| := by rw [abs_mul, abs_of_pos hs]
    _ = |21 * Real.goldenRatio - 34| := by
      rw [hU, goldenRatio_eighth]
      congr 1
      push_cast
      field_simp
      rw [hφ]
      ring
    _ < 1 := abs_lt.mpr ⟨by linarith only [goldenRatio_bounds.1],
      by linarith only [goldenRatio_bounds.2]⟩
    _ ≤ _ := by
      rw [Real.rpow_neg Real.goldenRatio_pos.le, Real.rpow_ofNat, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos Real.goldenRatio_pos _)).mpr
      have hp : Real.goldenRatio ^ (3 : ℕ) ≤ (2 : ℝ) ^ (3 : ℕ) :=
        pow_le_pow_left₀ Real.goldenRatio_pos.le Real.goldenRatio_lt_two.le _
      norm_num at hp ⊢
      linarith only [hp]

-- Independent check for (n, k, p, q) = (4, 3, 1, 2): the sum equals F₄² = 9.
example : 5 * |(lucasU fibonacciLucasParams 4 : ℝ) ^ (2 : ℕ) -
      Real.goldenRatio ^ (8 : ℕ) / 5| < 648 * Real.goldenRatio := by
  have hU : lucasU fibonacciLucasParams 4 = 3 := by norm_num [lucasU_fibonacciLucasParams]
  calc
    _ = |(5 : ℝ) * ((lucasU fibonacciLucasParams 4 : ℝ) ^ (2 : ℕ) -
        Real.goldenRatio ^ (8 : ℕ) / 5)| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    _ = |32 - 21 * Real.goldenRatio| := by
      rw [hU, goldenRatio_eighth]
      congr 1
      push_cast
      ring
    _ < 3 := abs_lt.mpr ⟨by linarith only [goldenRatio_bounds.2],
      by linarith only [goldenRatio_bounds.1]⟩
    _ ≤ _ := by linarith only [Real.one_lt_goldenRatio]

-- Client check: specialize the public theorem to the linear solution.
example : Real.sqrt 5 * |(lucasU fibonacciLucasParams 8 : ℝ) -
      Real.goldenRatio ^ (8 : ℕ) / Real.sqrt 5| < 144 * Real.goldenRatio ^ (-3 : ℝ) := by
  have hsol : ∑ j ∈ Finset.Icc (1 : ℕ) 4, (j : ℤ) * lucasU fibonacciLucasParams j ^ 1 =
      lucasU fibonacciLucasParams 8 ^ 1 := by decide
  have h := remainder_bound_of_neg fibonacciLucasParams (n := 8) (k := 4) (p := 1) (q := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsol
  have hp : fibonacciLucasParams.p = 1 := by decide
  have hq : fibonacciLucasParams.q = -1 := by decide
  dsimp only at h
  norm_num [hp, hq, Real.sqrt_eq_rpow, Real.goldenRatio] at h ⊢
  exact h

end LucasWeightedPowerSumExistsRemaindersWeightedPowerSum
end MathlibExtTest.NumberTheory.Recurrences

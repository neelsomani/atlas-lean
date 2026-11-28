/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.TwoAdicEulerDissection
import Mathlib.Tactic.NormNum

open MetaMathlibExt.QPochhammer

private theorem norm_zero_dyadic_lt_one (j : ℕ) : ‖(0 : ℂ) ^ 2 ^ j‖ < 1 := by
  rw [zero_pow (by positivity : 2 ^ j ≠ 0), norm_zero]
  exact zero_lt_one

-- Independently evaluate both sides at the center of the disk.
example :
    (∏' j : ℕ, (qPochhammerInf ((0 : ℂ) ^ 2 ^ j) (0 ^ 2 ^ (j + 1))
          (norm_zero_dyadic_lt_one (j + 1))
        / qPochhammerInf ((0 : ℂ) ^ 2 ^ (j + 1)) (0 ^ 2 ^ (j + 1))
          (norm_zero_dyadic_lt_one (j + 1))) ^ 2 ^ j) = 1 ∧
      qPochhammerInf 0 0 (by simp) = 1 := by
  have hz (j : ℕ) : (0 : ℂ) ^ 2 ^ j = 0 := zero_pow (by positivity)
  simp [hz]

-- These finite products retain only factors with q-exponent at most `bound`.
private def eulerPrefix (q : ℚ) (scale bound : ℕ) : ℚ :=
  ∏ k ∈ Finset.range (bound / scale), (1 - q ^ (scale * (k + 1)))

private def oddPrefix (q : ℚ) (scale bound : ℕ) : ℚ :=
  ∏ k ∈ Finset.range ((bound / scale + 1) / 2), (1 - q ^ (scale * (2 * k + 1)))

-- At q = 1/2 and cutoff 4 the first two quotient factors telescope, with a
-- residual fourth power from the even factors. Check the quotient factors as well
-- so an incorrect dyadic weight cannot pass the finite test.
example :
    oddPrefix (1 / 2) 1 4 / eulerPrefix (1 / 2) 2 4 = 28 / 45 ∧
      (oddPrefix (1 / 2) 2 4 / eulerPrefix (1 / 2) 4 4) ^ (2 : ℕ) = 16 / 25 ∧
      eulerPrefix (1 / 2) 1 4 / eulerPrefix (1 / 2) 4 4 ^ (4 : ℕ) =
        (28 / 45) * (16 / 25) := by
  norm_num [eulerPrefix, oddPrefix, Finset.prod_range_succ]

private theorem norm_half_lt_one : ‖(1 / 2 : ℂ)‖ < 1 := by
  norm_num [norm_div, Complex.norm_ofNat]

private theorem norm_half_dyadic_lt_one (j : ℕ) : ‖(1 / 2 : ℂ) ^ 2 ^ j‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) norm_half_lt_one (by positivity)

-- Exercise the public theorem at a nonzero argument in the open unit disk.
example :
    (∏' j : ℕ, (qPochhammerInf ((1 / 2 : ℂ) ^ 2 ^ j) ((1 / 2) ^ 2 ^ (j + 1))
          (norm_half_dyadic_lt_one (j + 1))
        / qPochhammerInf ((1 / 2 : ℂ) ^ 2 ^ (j + 1)) ((1 / 2) ^ 2 ^ (j + 1))
          (norm_half_dyadic_lt_one (j + 1))) ^ 2 ^ j) =
      qPochhammerInf (1 / 2) (1 / 2) norm_half_lt_one :=
  MetaMathlibExt.tprod_qPochhammer_twoAdic (1 / 2) norm_half_lt_one

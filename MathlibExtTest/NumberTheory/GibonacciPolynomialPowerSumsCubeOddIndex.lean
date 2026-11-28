/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GibonacciPolynomialPowerSumsCubeOddIndex

/-!
# Tests for cubic series at odd Fibonacci polynomial indices

At `x = 1`, evaluate the first two terms of each series from the polynomial recurrence and
compare with the corresponding total minus the uncanceled tail. The public theorem is
also exercised at `x = 1` for both series.
-/

namespace MathlibExtTest.NumberTheory.GibonacciPolynomialPowerSumsCubeOddIndex

open MetaMathlibExt Polynomial

local notation "F" => fun n : ℕ ↦ aeval (1 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)
local notation "L" => fun n : ℕ ↦ aeval (1 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

-- The centers are 3 and 5. The shift by one leaves the initial index 2 and tail index 6.
example : (4 * F 9 - 3 * F 3) / (F 3 ^ 2 - 1) ^ 3 +
    (4 * F 15 - 3 * F 5) / (F 5 ^ 2 - 1) ^ 3 = 5 - 5 / F 6 ^ 3 := by
  norm_num [generalizedFibonacciPolynomial_add_two]

-- For shift two, both initial indices (1 and 3) and both tail indices (5 and 7) matter.
example : (8 * L 9 + 3 * L 3) / (F 3 ^ 2 + 1) ^ 3 +
    (8 * L 15 + 3 * L 5) / (F 5 ^ 2 + 1) ^ 3 = 45 / 8 - 5 / F 5 ^ 3 - 5 / F 7 ^ 3 := by
  norm_num [generalizedFibonacciPolynomial_add_two, map_ofNat]

example : ∑' n : ℕ, (4 * F (6 * (n + 1) + 3) - 3 * F (2 * (n + 1) + 1)) /
    (F (2 * (n + 1) + 1) ^ 2 - 1) ^ 3 = 5 := by
  have h := (tsum_fibPoly_cube_odd_index (by norm_num : 0 < (1 : ℝ))).1
  norm_num at h ⊢
  exact h

example : ∑' n : ℕ, (8 * L (6 * (n + 1) + 3) + 3 * L (2 * (n + 1) + 1)) /
    (F (2 * (n + 1) + 1) ^ 2 + 1) ^ 3 = 45 / 8 := by
  have h := (tsum_fibPoly_cube_odd_index (by norm_num : 0 < (1 : ℝ))).2
  norm_num at h ⊢
  exact h

end MathlibExtTest.NumberTheory.GibonacciPolynomialPowerSumsCubeOddIndex

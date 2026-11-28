/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GibonacciPolynomialEvenPowerEvenIndex

/-!
# Tests for the Fibonacci polynomial even-power series at even indices

Compute the first two fourth-power summands at `x = 1` directly from the polynomial
recurrence for each parity of the shift, and compare them to the asserted total minus
its uncanceled tail. The client examples exercise both squared-denominator identities.
-/

namespace MathlibExtTest.NumberTheory.GibonacciPolynomialEvenPowerEvenIndex

open MetaMathlibExt Polynomial

local notation "F" => fun i : ℕ ↦ aeval (1 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 i)

-- Odd shift `k = 1`: the centers are 2 and 4, and the fourth-power numerator adds its terms.
example : (F 4 * F 8 + 4 * F 2 * F 4) / (F 2 ^ 2 + F 1 ^ 2) ^ 4 +
    (F 4 * F 16 + 4 * F 2 * F 8) / (F 4 ^ 2 + F 1 ^ 2) ^ 4 =
      5 * (1 / F 1 ^ 4 - 1 / F 5 ^ 4) := by
  norm_num [generalizedFibonacciPolynomial_add_two]

-- Even shift `k = 2`: the centers are 4 and 6, and the fourth-power numerator subtracts.
example : (F 8 * F 16 - 4 * F 4 * F 8) / (F 4 ^ 2 - F 2 ^ 2) ^ 4 +
    (F 8 * F 24 - 4 * F 4 * F 12) / (F 6 ^ 2 - F 2 ^ 2) ^ 4 =
      5 * (1 / F 2 ^ 4 + 1 / F 4 ^ 4 - 1 / F 6 ^ 4 - 1 / F 8 ^ 4) := by
  norm_num [generalizedFibonacciPolynomial_add_two]

example : ∑' n : ℕ, F (4 * (n + 1)) / (F (2 * (n + 1)) ^ 2 + 1) ^ 2 = 1 := by
  have h := tsum_fibPoly_even_pow_even_index (k := 1) (m := 1)
    (by norm_num : 0 < (1 : ℝ)) (by decide) (by decide)
  norm_num [Finset.sum_range_succ, generalizedFibonacciPolynomial_add_two] at h ⊢
  exact h

example : ∑' n : ℕ, 3 * F (4 * (n + 2)) / (F (2 * (n + 2)) ^ 2 - 1) ^ 2 = 10 / 9 := by
  have h := tsum_fibPoly_even_pow_even_index (k := 2) (m := 1)
    (by norm_num : 0 < (1 : ℝ)) (by decide) (by decide)
  have he : ¬ Odd (2 : ℕ) := by decide
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.sum_pair (by decide)] at h
  norm_num [he, Finset.sum_range_succ, generalizedFibonacciPolynomial_add_two] at h ⊢
  exact h

end MathlibExtTest.NumberTheory.GibonacciPolynomialEvenPowerEvenIndex

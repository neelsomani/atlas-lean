/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.DixonSummation
import MathlibExt.NumberTheory.Recurrences.LucasAlternatingTwoBinomialCatalanConvolution

/-! # Tests for the alternating two-binomial Catalan convolution -/

open Finset MetaMathlibExt

-- Check Dixon's identity directly with unequal parameters. The terms at `j = ±2` vanish.
example :
    (∑ j ∈ Icc (-2 : ℤ) 2, (-1 : ℚ) ^ j * invFact (2 + j) * invFact (2 - j) *
      invFact (1 + j) * invFact (1 - j) * invFact (1 + j) * invFact (1 - j)) = 1 / 6 ∧
      extFact 4 * invFact 3 * invFact 3 * invFact 2 * invFact 2 * invFact 1 * invFact 1 =
        1 / 6 := by
  constructor <;> decide +kernel

-- Compute the sum and the closed form independently, with odd `n` and Pell parameters.
example :
    (∑ k ∈ range (2 * 1 + 1), (-1 : ℤ) ^ k *
        ((2 * 1).choose k * (4 * 1).choose (2 * k) * catalan k * catalan (2 * 1 - k) : ℤ) *
        lucasU ⟨2, -1, by decide⟩ (2 * 1 - k) * lucasV ⟨2, -1, by decide⟩ k) = -16 ∧
      (-1 : ℤ) ^ (1 : ℕ) * ((3 * 1 + 1).choose 1 * catalan 1 * catalan (2 * 1) : ℤ) *
        lucasU ⟨2, -1, by decide⟩ (2 * 1) = -16 := by
  constructor <;>
    norm_num [sum_range_succ, catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose] <;>
    decide +kernel

-- Check the positive sign at even `n` with Fibonacci parameters, again without the new theorem.
example :
    (∑ k ∈ range (2 * 2 + 1), (-1 : ℤ) ^ k *
        ((2 * 2).choose k * (4 * 2).choose (2 * k) * catalan k * catalan (2 * 2 - k) : ℤ) *
        lucasU ⟨1, -1, by decide⟩ (2 * 2 - k) * lucasV ⟨1, -1, by decide⟩ k) = 1764 ∧
      (-1 : ℤ) ^ (2 : ℕ) * ((3 * 2 + 1).choose 2 * catalan 2 * catalan (2 * 2) : ℤ) *
        lucasU ⟨1, -1, by decide⟩ (2 * 2) = 1764 := by
  constructor <;>
    norm_num [sum_range_succ, catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose] <;>
    decide +kernel

-- The public theorem also evaluates the single summand at the endpoint `n = 0`.
example :
    ∑ k ∈ range (2 * 0 + 1), (-1 : ℤ) ^ k *
      ((2 * 0).choose k * (4 * 0).choose (2 * k) * catalan k * catalan (2 * 0 - k) : ℤ) *
      lucasU ⟨-2, -1, by decide⟩ (2 * 0 - k) * lucasV ⟨-2, -1, by decide⟩ k = 0 := by
  rw [lucasU_lucasV_sum_choose_sq_catalan_alternating]
  decide +kernel

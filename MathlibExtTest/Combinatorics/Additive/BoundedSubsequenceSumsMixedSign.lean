/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Fin.Tuple
import MathlibExt.Combinatorics.Additive.BoundedSubsequenceSumsMixedSign

open MetaMathlibExt

-- One negative term and two positive values, the first occurring twice. With α = β = 1, the
-- permitted lengths are one through three and the padding multiplicity is two.
private def capacities : Fin 4 → ℕ := Fin.append ![1] (Fin.cons 2 ![2, 1])

-- Putting the zero first instead of between the two blocks would give 7 rather than 6.
example : yangChenBound capacities 3 = 6 := by decide

-- Direct enumeration gives nine sums, strictly above the independently computed bound.
example :
    boundedSubsequenceSums 1 1 (repetitionSequence ![(-2 : ℤ)] ![1] +
      repetitionSequence ![3, 8] ![2, 1]) = {-2, 1, 3, 4, 6, 8, 9, 11, 14} := by decide

example : yangChenBound capacities 3 <
    (boundedSubsequenceSums 1 1 (repetitionSequence ![(-2 : ℤ)] ![1] +
      repetitionSequence ![3, 8] ![2, 1])).card := by decide

-- With consecutive values on either side of zero, enumeration attains the bound.
example :
    boundedSubsequenceSums 1 1 (repetitionSequence ![(-1 : ℤ)] ![1] +
      repetitionSequence ![1, 2] ![2, 1]) = {-1, 0, 1, 2, 3, 4} := by decide

example : ((boundedSubsequenceSums 1 1 (repetitionSequence ![(-1 : ℤ)] ![1] +
    repetitionSequence ![1, 2] ![2, 1])).card : ℤ) = yangChenBound capacities 3 := by decide

-- A client can apply the lower bound to the nonextremizing sequence without enumerating its sums.
example : yangChenBound capacities 3 ≤
    (boundedSubsequenceSums 1 1 (repetitionSequence ![(-2 : ℤ)] ![1] +
      repetitionSequence ![3, 8] ![2, 1])).card :=
  (card_boundedSubsequenceSums_ge_mixedSign (n := 1) (p := 2) (by decide) (by decide)
    ![1] ![2, 1] (by decide) (by decide) 4 (by decide) 1 1 (by decide) (by decide)).1
    ![-2] ![3, 8] (by rw [Fin.strictMono_iff_lt_succ]; decide) (by decide)
    (by rw [Fin.strictMono_iff_lt_succ]; decide) (by decide)

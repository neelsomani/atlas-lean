/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.IsSquare
meta import MathlibExt.NumberTheory.InitialRepetitionsC8Prime
import MathlibExt.NumberTheory.InitialRepetitionsC8Prime

/-! # Tests for the partition function `c₈'` with a possibly distinguished part -/

open MetaMathlibExt

-- The least allowed prime: 15 · 1 + 4 = 19 is 5 modulo 7, a nonsquare.
example (n : ℕ) : Even (initialRepetitionsC8Prime (7 * n + 1)) :=
  initialRepetitionsC8Prime_prime_mul_add_even 7 1 n (by decide) (by decide) (by decide)
    (by unfold IsSquare; decide)

-- With `n = 0` the theorem gives the parity of one value: 15 · 5 + 4 = 79 is 2 modulo 11.
example : Even (initialRepetitionsC8Prime 5) :=
  initialRepetitionsC8Prime_prime_mul_add_even 11 5 0 (by decide) (by decide) (by decide)
    (by unfold IsSquare; decide)

-- At residue 3 the value 15 · 3 + 4 = 49 vanishes modulo 7, so it counts as a square.
example : IsSquare ((15 * 3 + 4 : ℕ) : ZMod 7) := ⟨0, by decide⟩

-- Count independently of the parity theorem: {2} is counted twice, once with 2 distinguished.
#guard initialRepetitionsC8Prime 2 == 2

-- With a square discriminant the count can be odd. Only {2, 1}, with 2 distinguished, qualifies.
#guard initialRepetitionsC8Prime 3 == 1

-- The nonsquare criterion applies at N = 2, where 15 · 2 + 4 = 34.
example : Even (initialRepetitionsC8Prime 2) :=
  initialRepetitionsC8Prime_even_of_not_isSquare 2 (by norm_num)

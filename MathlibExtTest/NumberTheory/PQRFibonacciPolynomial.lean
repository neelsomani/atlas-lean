/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PQRFibonacciPolynomial

/-! # Tests for the (p,q)-r-Fibonacci recurrences -/

open MetaMathlibExt

-- At n = r the shifted polynomial has index zero.
example {R : Type*} [CommSemiring R] {r : ℕ} (hr : 1 ≤ r) (x y p q : R) (m : ℕ) :
    pqRFibonacci r x y p q m (r + 1) = p * x * pqRFibonacci r (p * x) (q * y) p q m r := by
  simpa only [Nat.sub_self, pqRFibonacci_zero, mul_zero, add_zero] using
    pqRFibonacci_succ_eq_left hr (Nat.le_refl r) x y p q m

-- Both recurrence terms contribute when p = 2 and q = 3.
example : pqRFibonacci 1 (1 : ℕ) 1 2 3 0 4 = 94 := by
  rw [pqRFibonacci_succ_eq_left (r := 1) (n := 3) (by decide) (by decide)]
  decide

-- At p = 0 only the top y-degree survives, and its exponent depends on m.
example : pqRFibonacci 1 (1 : ℕ) 1 0 2 2 5 = 32 := by
  rw [pqRFibonacci_succ_eq_left (r := 1) (n := 4) (by decide) (by decide)]
  decide

-- At n = r, the second summand is zero. Check both sides by evaluation.
example :
    pqRFibonacci 2 (1 : ℕ) 1 2 3 1 3 =
      2 * pqRFibonacci 2 2 2 2 3 1 2 + 3 * pqRFibonacci 2 3 9 2 3 1 0 := by
  decide

-- Distinct p and q and positive m make the two substitutions distinguishable.
example : pqRFibonacci 1 (1 : ℕ) 1 2 3 1 5 = 1561 ∧
    2 * pqRFibonacci 1 (2 : ℕ) 2 2 3 1 4 = 1264 ∧
    3 * pqRFibonacci 1 (3 : ℕ) 9 2 3 1 3 = 297 := by
  decide

-- The division-free recurrence also works at p = 0, with only the second summand surviving.
example : pqRFibonacci 1 (1 : ℕ) 1 0 2 2 5 = 2 * pqRFibonacci 1 2 8 0 2 2 3 := by
  decide

-- Apply the public recurrence at the nondegenerate inputs above.
example :
    pqRFibonacci 1 (1 : ℕ) 1 2 3 1 5 =
      2 * pqRFibonacci 1 2 2 2 3 1 4 + 3 * pqRFibonacci 1 3 9 2 3 1 3 :=
  pqRFibonacci_succ_eq_right (r := 1) (n := 4) (by decide) (by decide) 1 1 2 3 1

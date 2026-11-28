/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ComplementarySequencesPyramidal

/-!
# Tests for the non-pyramidal formula
-/

open MetaMathlibExt

private def pyramidal (k j : ℕ) : ℕ := j * (j + 1) * ((k - 2) * j + 5 - k) / 6

-- Compute the complement without using the cube-root formula. For k = 3 and n = 7,
-- the lower cutoff is exact. For k = 8, the cube root jumps at n = 8 as the complement skips 9.
example : nthNonValue (pyramidal 3) 7 = 9 ∧ nthNonValue (pyramidal 8) 7 = 8 ∧
    nthNonValue (pyramidal 8) 8 = 10 := by
  have hgap (d j : ℕ) (hj : 1 ≤ j) : pyramidal (d + 2) j + j ≤ pyramidal (d + 2) (j + 1) := by
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [pyramidal, Nat.add_sub_cancel]
    have hsub (t : ℕ) : d * (t + 1) + 5 - (d + 2) = d * t + 3 := by
      rw [Nat.mul_succ]
      omega
    rw [hsub i, hsub (i + 1)]
    have hdiff : (i + 1 + 1) * (i + 1 + 1 + 1) * (d * (i + 1) + 3) =
        (i + 1) * (i + 1 + 1) * (d * i + 3) + 6 * (i + 1) +
          (3 * (i + 1) * (i + 2) * d + 6) := by ring
    rw [hdiff]
    omega
  have h3 := nthNonValue_eq_one_step (pyramidal 3) (by decide) (hgap 1)
  have h8 := nthNonValue_eq_one_step (pyramidal 8) (by decide) (hgap 6)
  exact ⟨(h3 7 (by decide)).trans (by decide), (h8 7 (by decide)).trans (by decide),
    (h8 8 (by decide)).trans (by decide)⟩

-- Exercise the public formula at the same cutoffs; evaluate its arithmetic independently.
example : nthNonValue (pyramidal 3) 7 = 9 ∧ nthNonValue (pyramidal 8) 7 = 8 ∧
    nthNonValue (pyramidal 8) 8 = 10 :=
  ⟨(nthNonValue_pyramidal 3 (by decide) (by decide) 7 (by decide)).trans (by decide),
    (nthNonValue_pyramidal 8 (by decide) (by decide) 7 (by decide)).trans (by decide),
    (nthNonValue_pyramidal 8 (by decide) (by decide) 8 (by decide)).trans (by decide)⟩

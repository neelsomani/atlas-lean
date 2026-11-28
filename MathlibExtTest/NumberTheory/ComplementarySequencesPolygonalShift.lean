/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ComplementarySequencesPolygonalShift
import MathlibExt.NumberTheory.PolygonalNumber

/-!
# Tests for the shifted formula for non-polygonal numbers
-/

open MetaMathlibExt

-- The first two positive 11-gonal numbers are 1 and 11. Compute the non-values by finite counting.
example : nthNonValue (Nat.polygonalNumber 11) 1 = 2 ∧
    nthNonValue (Nat.polygonalNumber 11) 9 = 10 ∧ nthNonValue (Nat.polygonalNumber 11) 10 = 12 := by
  have hgap (j : ℕ) (_ : 1 ≤ j) :
      Nat.polygonalNumber 11 j + j ≤ Nat.polygonalNumber 11 (j + 1) := by
    have hstep : (j + 1).choose 2 = j.choose 2 + j := by
      simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' j 1
    simp only [Nat.polygonalNumber_eq, hstep, Nat.reduceSub, Nat.mul_add]
    omega
  have hcount := nthNonValue_eq_two_step (Nat.polygonalNumber 11) (by simp) hgap
  exact ⟨(hcount 1 (by decide)).trans (by decide), (hcount 9 (by decide)).trans (by decide),
    (hcount 10 (by decide)).trans (by decide)⟩

private noncomputable def shiftedCandidate (n : ℕ) (r : ℝ) : ℕ :=
  let s := ⌊Real.sqrt ((2 * n + r) / ((11 : ℝ) - 2))⌋₊
  if (11 - 2) * s * (s + 1) < 2 * n then n + s + 1 else n + s

-- Compute the formula itself independently: floor zero, an exact square, equality at the cutoff,
-- and a strict crossing at positive s with a nonintegral shift.
private theorem candidateValues : shiftedCandidate 1 (-1) = 2 ∧ shiftedCandidate 1 7 = 2 ∧
    shiftedCandidate 9 7 = 10 ∧ shiftedCandidate 10 (1 / 2) = 12 := by
  have hfloor (x : ℝ) (s : ℕ) (hlo : (s : ℝ) ^ 2 ≤ x) (hhi : x < ((s : ℝ) + 1) ^ 2) :
      ⌊Real.sqrt x⌋₊ = s :=
    (Nat.floor_eq_iff (Real.sqrt_nonneg _)).2
      ⟨Real.le_sqrt_of_sq_le hlo, (Real.sqrt_lt' (by positivity)).2 hhi⟩
  have hzero := hfloor ((2 * 1 + (-1)) / ((11 : ℝ) - 2)) 0 (by norm_num) (by norm_num)
  have hone := hfloor ((2 * 1 + 7) / ((11 : ℝ) - 2)) 1 (by norm_num) (by norm_num)
  have heq := hfloor ((2 * 9 + 7) / ((11 : ℝ) - 2)) 1 (by norm_num) (by norm_num)
  have hgt := hfloor ((2 * 10 + 1 / 2) / ((11 : ℝ) - 2)) 1 (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [shiftedCandidate, Nat.cast_one, Nat.cast_ofNat, hzero, hone, heq, hgt] <;> decide

-- A client uses the exported theorem at the exact cutoff and just after it.
example :
    let f (j : ℕ) := (11 - 2) * j * (j - 1) / 2 + j
    nthNonValue f 9 = 10 ∧ nthNonValue f 10 = 12 := by
  intro f
  exact ⟨(nthNonValue_polygonal_shift 11 (by decide) 7 (by norm_num) (by norm_num) 9
      (by decide)).trans candidateValues.2.2.1,
    (nthNonValue_polygonal_shift 11 (by decide) (1 / 2) (by norm_num) (by norm_num) 10
      (by decide)).trans candidateValues.2.2.2⟩

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelHalfPrimeResidueWalk
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

namespace MathlibExtTest.NumberTheory.GobelHalfPrimeResidueWalk

open MetaMathlibExt

-- The walk from 2 takes a negative step at index 1, then reaches 0 at index 3.
private theorem walk_two_at_two : gobelResidueWalk 5 2 2 = 1 := by
  have h₁ := gobelResidueWalk_one 5 2
  rw [gobelResidueWalk_succ_of_between 5 2 1 (by decide) (by rw [h₁]; decide), h₁]
  norm_num

-- The scaled term at n = 2 is 6, so its difference from the walk is nonzero
-- and has valuation exactly 1.
example : padicValRat 5 ((2 : ℚ) * gobelSequence 2 2 2 - gobelResidueWalk 5 2 2) = 1 := by
  rw [gobelSequence_two_two_small.1, walk_two_at_two]
  convert padicValRat.self (p := 5) (by decide) using 2
  norm_num

example : gobelResidueWalk 5 2 5 = 0 ∧ 0 ≤ padicValRat 5 (gobelSequence 2 2 5) := by
  have h₃ : gobelResidueWalk 5 2 3 = 0 := by
    rw [gobelResidueWalk_succ_of_between 5 2 2 (by decide) (by rw [walk_two_at_two]; decide),
      walk_two_at_two]
    norm_num
  have h₄ := gobelResidueWalk_succ_of_eq_zero 5 2 3 (by decide) h₃
  refine ⟨gobelResidueWalk_succ_of_eq_zero 5 2 4 (by decide) h₄, ?_⟩
  rw [gobelSequence_two_two_small.2.2.2]
  exact zero_le_padicValRat_of_nat 28

-- Starting at 4, the walk reaches 5 at index 2 and stays there.
private theorem walk_four_at_five : gobelResidueWalk 5 4 5 = 5 := by
  have h₁ := gobelResidueWalk_one 5 4
  have h₂ : gobelResidueWalk 5 4 2 = 5 := by
    rw [gobelResidueWalk_succ_of_between 5 4 1 (by decide) (by rw [h₁]; decide), h₁]
    norm_num
  have h₃ := gobelResidueWalk_succ_of_eq_prime 5 4 2 (by decide) h₂
  have h₄ := gobelResidueWalk_succ_of_eq_prime 5 4 3 (by decide) h₃
  exact gobelResidueWalk_succ_of_eq_prime 5 4 4 (by decide) h₄

-- The fifth term is a unit at 5, independently of the walk calculation.
example : gobelResidueWalk 5 4 5 = 5 ∧ padicValRat 5 (gobelSequence 2 4 5) = 0 := by
  refine ⟨walk_four_at_five, ?_⟩
  have h₁ := gobelSequence_one 2 4
  have h₂ : gobelSequence 2 4 2 = 10 := by
    have h := gobelSequence_succ 2 4 1 (by decide)
    rw [h₁] at h
    norm_num at h
    linarith only [h]
  have h₃ : gobelSequence 2 4 3 = 40 := by
    have h := gobelSequence_succ 2 4 2 (by decide)
    rw [h₂] at h
    norm_num at h
    linarith only [h]
  have h₄ : gobelSequence 2 4 4 = 430 := by
    have h := gobelSequence_succ 2 4 3 (by decide)
    rw [h₃] at h
    norm_num at h
    linarith only [h]
  have h₅ : gobelSequence 2 4 5 = 37324 := by
    have h := gobelSequence_succ 2 4 4 (by decide)
    rw [h₄] at h
    norm_num at h
    linarith only [h]
  rw [h₅, ← show ((37324 : ℕ) : ℚ) = 37324 by norm_num, padicValRat.of_nat,
    multiplicity_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ (37324 : ℕ)), Nat.cast_zero]

-- The initial difference is zero, rather than a nonzero multiple of 5.
example : (1 : ℚ) * gobelSequence 2 4 1 - gobelResidueWalk 5 4 1 = 0 := by
  rw [gobelSequence_one, gobelResidueWalk_one, one_mul, sub_self]

-- At 13 this walk instead ends strictly between the two absorbing endpoints.
example : gobelResidueWalk 13 4 13 = 4 := by
  have step (n x y : ℕ) (hn : 1 ≤ n) (hx : 0 < x ∧ x < 13)
      (hw : gobelResidueWalk 13 4 n = x)
      (hy : Int.toNat ((x : ℤ) + jacobiSym (n : ℤ) 13 * jacobiSym (x : ℤ) 13) = y) :
      gobelResidueWalk 13 4 (n + 1) = y := by
    rw [gobelResidueWalk_succ_of_between 13 4 n hn (by rwa [hw]), hw, hy]
  have h₁ := gobelResidueWalk_one 13 4
  have h₂ := step 1 4 5 (by decide) (by decide) h₁ (by norm_num)
  have h₃ := step 2 5 6 (by decide) (by decide) h₂ (by norm_num)
  have h₄ := step 3 6 5 (by decide) (by decide) h₃ (by norm_num)
  have h₅ := step 4 5 4 (by decide) (by decide) h₄ (by norm_num)
  have h₆ := step 5 4 3 (by decide) (by decide) h₅ (by norm_num)
  have h₇ := step 6 3 2 (by decide) (by decide) h₆ (by norm_num)
  have h₈ := step 7 2 3 (by decide) (by decide) h₇ (by norm_num)
  have h₉ := step 8 3 2 (by decide) (by decide) h₈ (by norm_num)
  have h₁₀ := step 9 2 1 (by decide) (by decide) h₉ (by norm_num)
  have h₁₁ := step 10 1 2 (by decide) (by decide) h₁₀ (by norm_num)
  have h₁₂ := step 11 2 3 (by decide) (by decide) h₁₁ (by norm_num)
  exact step 12 3 4 (by decide) (by decide) h₁₂ (by norm_num)

-- A client can obtain integrality from the upper endpoint without computing the rational term.
example : 0 ≤ padicValRat 5 (gobelSequence 2 4 5) :=
  (gobelSequence_half_pred_congruent_residue_walk 5 4 (by norm_num) ⟨2, rfl⟩ (by decide)).2.mpr
    (Or.inr walk_four_at_five)

end MathlibExtTest.NumberTheory.GobelHalfPrimeResidueWalk

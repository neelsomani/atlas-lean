/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OlympicGamesNumerationFloorGreedyTwoPell
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Tests for the greedy doubled-Pell floor identity

Independently check the greedy cutoffs, the shifted sum and the floor for small inputs with
nonzero digits at either parity, including a saturated even digit and the all-zero input.
-/

namespace MathlibExtTest.NumberTheory.OlympicGamesNumerationFloorGreedyTwoPell

open Finset MetaMathlibExt

private def weight (k : ℕ) : ℕ :=
  if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k

private def shifted (k : ℕ) : ℕ :=
  if k % 2 = 1 then pellNumber k else pellLucasSequence k

-- Compute both successor relations and both weight recurrences at specific indices.
example : pellLucasSequence 2 + pellNumber 2 = pellNumber 3 ∧
    pellLucasSequence 3 = pellNumber 3 + pellNumber 2 := by decide

example : weight 4 + weight 2 = 2 * weight 3 ∧ weight 5 + weight 3 = 4 * weight 4 := by decide

private theorem sqrt_two_bounds : (1414 : ℝ) / 1000 < Real.sqrt 2 ∧
    Real.sqrt 2 < (1415 : ℝ) / 1000 :=
  ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num),
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)⟩

private def Check (n : ℕ) (a : ℕ → ℕ) (t u : ℕ) : Prop :=
  (∀ m ≤ n + 1, ∑ k ∈ range m, a k * weight k < weight m) ∧
    (∑ k ∈ range (n + 1), a k * weight k) = t ∧
    (∑ k ∈ range (n + 1), a k * shifted (k + 1)) = u ∧
    ⌊(t : ℝ) * ((2 + Real.sqrt 2) / 2)⌋₊ = u

example : Check 0 (fun _ ↦ 0) 0 0 := by
  refine ⟨?_, by decide, by decide, by simp⟩
  intro m hm
  interval_cases m <;> decide

private def seven (k : ℕ) : ℕ := [1, 0, 2].getD k 0

example : Check 2 seven 7 11 := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · intro m hm
    interval_cases m <;> decide
  · rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> norm_num <;> linarith only [sqrt_two_bounds.1, sqrt_two_bounds.2]

-- Three copies of weight 3 fit below weight 10, but there is no room to add weight 1.
example : Check 2 (fun k ↦ [0, 0, 3].getD k 0) 9 15 ∧ 9 + weight 0 = weight 3 := by
  refine ⟨⟨?_, by decide, by decide, ?_⟩, by decide⟩
  · intro m hm
    interval_cases m <;> decide
  · rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> norm_num <;> linarith only [sqrt_two_bounds.1, sqrt_two_bounds.2]

-- Both positive odd digits contribute to the shifted sum.
example : Check 3 (fun k ↦ [0, 1, 0, 1].getD k 0) 12 20 := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · intro m hm
    interval_cases m <;> decide
  · rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> norm_num <;> linarith only [sqrt_two_bounds.1, sqrt_two_bounds.2]

-- Client example: the same sum is allowed with a leading zero.
example : ⌊(7 : ℝ) * ((2 + Real.sqrt 2) / 2)⌋₊ = 11 := by
  have h := floor_greedy_two_pell_halfCompanion_sum_mul weight shifted (fun _ ↦ rfl)
    (fun _ ↦ rfl) 3 seven (by intro m hm; interval_cases m <;> decide)
  have hw : (∑ k ∈ range 4, seven k * weight k) = 7 := by decide
  have ht : (∑ k ∈ range 4, seven k * shifted (k + 1)) = 11 := by decide
  simpa only [hw, ht, Nat.cast_ofNat] using h

end MathlibExtTest.NumberTheory.OlympicGamesNumerationFloorGreedyTwoPell

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Digraph.TournamentScoreSequence

/-!
# Tests for the support bounds on atomic tournaments

The regular tournament on five players and the transitive tournament on four players with
its extreme edge reversed test the odd and even bounds, respectively.
-/

open MathlibExt.GraphTheory.TournamentScoreSequenceWanted

-- Each player beats the next two players in cyclic order.
private def cyclicFive (i j : Fin 5) : Bool := decide (j = i + 1 ∨ j = i + 2)

-- Reverse the edge from 3 to 0 in the tournament where larger players beat smaller players.
private def reversedEndpoints (i j : Fin 4) : Bool :=
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then decide (i < j) else decide (j < i)

example : IsTournament cyclicFive ∧ ¬ IsReducible cyclicFive ∧
    circularTriadCount cyclicFive = 5 := by decide

example : 5 ≤ circularTriadCount cyclicFive + 2 ∧
    24 * (circularTriadCount cyclicFive : ℤ) = (5 : ℤ) ^ 3 - 5 := by decide

example : IsTournament reversedEndpoints ∧ ¬ IsReducible reversedEndpoints ∧
    circularTriadCount reversedEndpoints = 2 := by decide

example : 4 = circularTriadCount reversedEndpoints + 2 ∧
    24 * (circularTriadCount reversedEndpoints : ℤ) = (4 : ℤ) ^ 3 - 4 * 4 := by decide

example : 3 ≤ 1 + 2 ∧ ∃ j : ℕ, 0 < j ∧ j ≤ 3 ∧
    ((Odd j ∧ 24 * (1 : ℤ) ≤ (j : ℤ) ^ 3 - j) ∨
      (Even j ∧ 24 * (1 : ℤ) ≤ (j : ℤ) ^ 3 - 4 * j)) :=
  atomCount_ne_zero_bounds 1 3 le_rfl (by rw [atomCount_three_one]; decide)

#print axioms atomCount_ne_zero_bounds

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.ParkingFunctionLastEntry

/-! # Regression tests for the last-entry counts of peakless-tieless parking functions -/

namespace MetaMathlibExt

set_option quotPrecheck false in
local notation "NoTies" w:max => ∀ i j, j.val = i.val + 1 → w i ≠ w j

set_option quotPrecheck false in
local notation "NoPeaks" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w i < w j ∧ w k < w j)

private def ending (n : ℕ) (a : Fin (n + 1)) : Finset (Fin (n + 1) → Fin (n + 1)) :=
  (Finset.univ.filter (fun f => IsParkingFunction (n + 1) f ∧ (NoTies f) ∧ NoPeaks f)).filter
    (fun f => ∀ j : Fin (n + 1), j.val + 1 = n + 1 → (f j).val + 1 = a.val + 1)

-- Enumerate the parking and shape predicates without using the last-entry theorem.
example : (ending 0 0).card = 1 := by decide

set_option maxHeartbeats 2000000 in
example : List.ofFn (fun a : Fin 4 => (ending 3 a).card) = [1, 3, 5, 5] := by decide

-- At length four and final preference 2, both branches of the recurrence occur.
set_option maxHeartbeats 2000000 in
example : ((ending 3 1).filter (fun f => f 0 = 3)).card = 2 ∧
    ((ending 3 1).filter (fun f => f 0 ≠ 3)).card = 1 := by decide

-- The same last-entry slice can also be counted by using the public theorem.
example : ((ending 3 1).card : ℚ) = 3 :=
  (card_peakless_tieless_parkingFunction_last 4 2 (by decide) (by decide)).trans
    (by norm_num [Nat.choose])

end MetaMathlibExt

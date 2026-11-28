/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.InversionSequencePatternReductions
import Mathlib.Data.Fintype.Basic

open MetaMathlibExt

-- Decide containment by checking the six comparisons on each increasing index triple.
private def hasPattern {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ) : Bool :=
  (List.finRange n).any fun i => (List.finRange n).any fun j =>
    decide (i < j) && (List.finRange n).any fun k =>
      decide (j < k) && decide ((e i < e j ↔ p 0 < p 1) ∧ (e i < e k ↔ p 0 < p 2) ∧
        (e j < e i ↔ p 1 < p 0) ∧ (e j < e k ↔ p 1 < p 2) ∧
        (e k < e i ↔ p 2 < p 0) ∧ (e k < e j ↔ p 2 < p 1))

local instance {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ) : Decidable (InvSeqContainsPattern e p) :=
  decidable_of_iff (hasPattern e p = true) (by
    simp only [hasPattern, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
      decide_eq_true_eq, invSeqContainsPattern_iff_exists_indices, invSeqPatternSameOrder_iff]
    exact ⟨fun ⟨i, j, hij, k, hjk, h⟩ => ⟨i, j, k, hij, hjk, h⟩,
      fun ⟨i, j, k, hij, hjk, h⟩ => ⟨i, j, hij, k, hjk, h⟩⟩)

-- Pattern codes in this test are decimal, with the omitted leading digits interpreted as zero.
private def digits (p : ℕ) : Fin 3 → ℕ := ![p / 100, p / 10 % 10, p % 10]

-- These four finite choices enumerate all 120 inversion sequences of length five. Each check
-- uses the containment decision procedure above, independently of the reduction theorem.
private def reducesAtFive (C : List ℕ) (τ : ℕ) : Prop :=
  ∀ (a : Fin 2) (b : Fin 3) (c : Fin 4) (d : Fin 5),
    let e : Fin 5 → ℕ := ![0, (a : ℕ), (b : ℕ), (c : ℕ), (d : ℕ)]
    (∀ p ∈ C, ¬ InvSeqContainsPattern e (digits p)) → ¬ InvSeqContainsPattern e (digits τ)

private instance (C : List ℕ) (τ : ℕ) : Decidable (reducesAtFive C τ) := by
  unfold reducesAtFive
  infer_instance

example : reducesAtFive [1] 101 := by decide
example : reducesAtFive [1] 102 := by decide
example : reducesAtFive [1] 201 := by decide
example : reducesAtFive [11] 101 := by decide
example : reducesAtFive [11] 110 := by decide
example : reducesAtFive [12] 102 := by decide
example : reducesAtFive [12] 120 := by decide
example : reducesAtFive [21] 201 := by decide
example : reducesAtFive [21] 210 := by decide

example : reducesAtFive [0, 1] 100 := by decide
example : reducesAtFive [0, 11] 100 := by decide
example : reducesAtFive [0, 11] 201 := by decide
example : reducesAtFive [0, 11] 210 := by decide
example : reducesAtFive [0, 12] 201 := by decide
example : reducesAtFive [0, 12] 210 := by decide
example : reducesAtFive [0, 21] 100 := by decide

example : reducesAtFive [1, 10] 21 := by decide
example : reducesAtFive [1, 10] 100 := by decide
example : reducesAtFive [1, 10] 110 := by decide
example : reducesAtFive [1, 10] 120 := by decide
example : reducesAtFive [1, 10] 210 := by decide
example : reducesAtFive [1, 11] 21 := by decide
example : reducesAtFive [1, 12] 21 := by decide
example : reducesAtFive [1, 110] 210 := by decide
example : reducesAtFive [1, 120] 210 := by decide

example : reducesAtFive [10, 11] 100 := by decide
example : reducesAtFive [10, 12] 101 := by decide
example : reducesAtFive [10, 12] 201 := by decide
example : reducesAtFive [10, 21] 100 := by decide
example : reducesAtFive [10, 21] 101 := by decide
example : reducesAtFive [10, 21] 102 := by decide
example : reducesAtFive [10, 21] 110 := by decide
example : reducesAtFive [10, 21] 120 := by decide

example : reducesAtFive [1, 11, 12] 210 := by decide
example : reducesAtFive [1, 11, 100] 210 := by decide
example : reducesAtFive [1, 12, 100] 210 := by decide

-- Both exclusions in the {000, 012} → 210 row matter.
example : ¬ reducesAtFive [0] 210 := by decide
example : ¬ reducesAtFive [12] 210 := by decide

-- A client of the theorem with the nontrivial base set {001, 011, 100}.
example : ¬ InvSeqContainsPattern (![0, 1, 2, 0] : Fin 4 → ℕ) ![2, 1, 0] := by
  refine invSeq_reducible_pattern_sets
    ({![0, 0, 1], ![0, 1, 1], ![1, 0, 0]}, ![2, 1, 0]) (by simp) 4 _ (by decide) ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;> decide

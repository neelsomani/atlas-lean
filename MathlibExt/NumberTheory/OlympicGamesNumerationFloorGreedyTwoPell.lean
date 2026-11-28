/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import MathlibExt.NumberTheory.OlympicGamesNumerationExistsTwoPellHalfCompanionRepresentation
import MathlibExt.NumberTheory.PellSilverRatio
import Mathlib.Tactic.LinearCombination

/-!
# Floor of greedy doubled-Pell and half-companion Pell sums

For natural-number digits through place $n$ in the basis $R_k = 2P_k$ at odd places and
$R_k = H_k$ at even places, assume the sum below each place $m \le n+1$ is strictly less than
$R_m$. Multiplying the sum by $(2+\sqrt 2)/2$ and taking the floor shifts the digits to $P_{k+1}$
for even $k$ and $H_{k+1}$ for odd $k$. The prefix inequalities express the greedy choice in the
source and allow leading zero digits, including the all-zero sum.

The positive single-digit errors satisfy the same three-term recurrences as the place values.
The error estimate allows extra copies of the last digit's weight as long as they still fit
below the next place value. This extra margin is used when the next digit is maximal.

## References

* Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with
  Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, pp. 1–38, Theorem 4, Proposition 2, and
  Theorem 6 (2). The article omits the proof of part (2).
* The strengthened prefix estimate adapts `greedy_error_lt_one` in
  `MathlibExt.NumberTheory.GreedyOddFibonacciFloor`.
-/

namespace MetaMathlibExt

open Finset

local notation "q" => (Real.sqrt 2 - 1)

private noncomputable def shiftError (j : ℕ) : ℝ :=
  (if j % 2 = 1 then 1 else Real.sqrt 2 / 2) * q ^ j

private lemma mixed_digit_shift {R R' : ℕ → ℕ}
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    (hR' : ∀ k, R' k = if k % 2 = 1 then pellNumber k else pellLucasSequence k) (j : ℕ) :
    (R j : ℝ) * ((2 + Real.sqrt 2) / 2) = R' (j + 1) + shiftError j := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · have hp := congrArg (fun t : ℕ ↦ (t : ℝ)) (pellLucasSequence_pellNumber_succ (2 * k)).1
    have hh := congrArg (fun t : ℕ ↦ (t : ℝ)) (pellLucasSequence_pellNumber_succ (2 * k)).2
    push_cast at hp hh
    simp [hR, hR', shiftError, Nat.add_mod]
    linear_combination (pellNumber_odd_mul_one_add_sqrt_two k).2 / 2 + (hp + hh) / 2
  · have hh := congrArg (fun t : ℕ ↦ (t : ℝ)) (pellLucasSequence_pellNumber_succ (2 * k + 1)).2
    push_cast at hh
    simp [hR, hR', shiftError, Nat.add_mod, Nat.add_assoc]
    linear_combination (pellNumber_odd_mul_one_add_sqrt_two k).1 - hh

/-- **Floor of greedy sums of $2P_k$ and $H_k$ times $(2 + \sqrt 2)/2$.** Let $P_k$ be the Pell
numbers and $H_k$ the Pell–Lucas numbers ($H_0 = H_1 = 1$, $H_{k+2} = 2H_{k+1} + H_k$). Put
$R_k = 2P_k$ and $R'_k = P_k$ for odd $k$, and $R_k = R'_k = H_k$ for even $k$. Let $n$ be a
natural number and $a_0, a_1, \dots$ natural numbers such that $\sum_{k<m} a_k R_k < R_m$ for
every $m \le n + 1$, and let $t = \sum_{k=0}^{n} a_k R_k$. Then
$\lfloor t(2 + \sqrt 2)/2 \rfloor = \sum_{k=0}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of $t$ by the
$R_k$; $n$ need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 6 (2). -/
public theorem floor_greedy_two_pell_halfCompanion_sum_mul (R R' : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    (hR' : ∀ k, R' k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    (n : ℕ) (a : ℕ → ℕ) (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, a k * R k < R m) :
    ⌊((∑ k ∈ range (n + 1), a k * R k : ℕ) : ℝ) * ((2 + Real.sqrt 2) / 2)⌋₊ =
      ∑ k ∈ range (n + 1), a k * R' (k + 1) := by
  have hs₁ : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs₂ : Real.sqrt 2 < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hq : 0 < q := sub_pos.mpr hs₁
  have hpos (j : ℕ) : 0 < shiftError j := by
    unfold shiftError
    split <;> exact mul_pos (by positivity) (pow_pos hq _)
  have hdecr (j : ℕ) : shiftError (j + 1) < shiftError j := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · have h : q < Real.sqrt 2 / 2 := by linarith only [hs₂]
      simpa [shiftError, Nat.add_mod, pow_succ' q (2 * k)] using
        mul_lt_mul_of_pos_right h (pow_pos hq (2 * k))
    · have h : Real.sqrt 2 / 2 * q < 1 := by nlinarith only [hs₁, hsq]
      simpa [shiftError, Nat.add_mod, pow_succ' q (2 * k + 1), ← mul_assoc] using
        mul_lt_mul_of_pos_right h (pow_pos hq (2 * k + 1))
  have hstep (j : ℕ) : ∃ b : ℕ, R (j + 2) + R j = b * R (j + 1) ∧
      shiftError (j + 2) + shiftError j = (b : ℝ) * shiftError (j + 1) := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · refine ⟨2, (two_pell_halfCompanion_place_recurrence R hR k).1, ?_⟩
      simp [shiftError, Nat.add_mod, pow_add]
      linear_combination q ^ (2 * k) * (Real.sqrt 2 / 2 - 1) * hsq
    · refine ⟨4, ?_, ?_⟩
      · simpa only [Nat.add_assoc, Nat.reduceAdd] using
          (two_pell_halfCompanion_place_recurrence R hR k).2
      · simp [shiftError, Nat.add_mod, pow_add]
        linear_combination -q ^ (2 * k + 1) * hsq
  let S (j : ℕ) := ∑ k ∈ range j, a k * R k
  let E (j : ℕ) := ∑ k ∈ range j, (a k : ℝ) * shiftError k
  -- Count extra copies of the last weight that still fit below the cutoff.
  have hbound (j : ℕ) (hj : j ≤ n) (c : ℕ)
      (hc : S (j + 1) + c * R j < R (j + 1)) :
      E (j + 1) + ((c : ℝ) + 1) * shiftError j ≤ 1 + shiftError (j + 1) := by
    induction j generalizing c with
    | zero =>
      have hR₀ : R 0 = 1 := by rw [hR]; decide
      have hR₁ : R 1 = 2 := by rw [hR]; decide
      have hcap : a 0 + c ≤ 1 := by simpa [S, hR₀, hR₁, Nat.lt_succ_iff] using hc
      have hcast : (a 0 : ℝ) + (c : ℝ) ≤ 1 := by exact_mod_cast hcap
      have hmul := mul_le_mul_of_nonneg_right hcast (hpos 0).le
      have hbase : 2 * shiftError 0 = 1 + shiftError 1 := by
        norm_num [shiftError]
        ring
      change E 1 + ((c : ℝ) + 1) * shiftError 0 ≤ 1 + shiftError 1
      simp only [E, sum_range_one, add_mul, one_mul] at hmul ⊢
      linarith only [hmul, hbase]
    | succ j ih =>
      obtain ⟨b, hw, he⟩ := hstep j
      change S (j + 2) + c * R (j + 1) < R (j + 2) at hc
      change E (j + 2) + ((c : ℝ) + 1) * shiftError (j + 1) ≤ 1 + shiftError (j + 2)
      rw [show S (j + 2) = S (j + 1) + a (j + 1) * R (j + 1) from sum_range_succ ..,
        add_assoc, ← add_mul] at hc
      rw [show E (j + 2) = E (j + 1) + (a (j + 1) : ℝ) * shiftError (j + 1) from
        sum_range_succ .., add_assoc, ← add_mul, ← add_assoc (a (j + 1) : ℝ)]
      have hcap : a (j + 1) + c < b := by
        by_contra! h
        have hmul := Nat.mul_le_mul_right (R (j + 1)) h
        omega
      by_cases hsmall : a (j + 1) + c + 2 ≤ b
      · have hprev := ih (by omega) 0 (by simpa using ha (j + 1) (by omega))
        simp only [Nat.cast_zero, zero_add, one_mul] at hprev
        have hcast : (a (j + 1) : ℝ) + (c : ℝ) + 2 ≤ (b : ℝ) := by exact_mod_cast hsmall
        have hmul := mul_le_mul_of_nonneg_right hcast (hpos (j + 1)).le
        simp only [add_mul, one_mul] at hmul ⊢
        linarith only [hprev, hmul, he]
      · have hb : b = a (j + 1) + c + 1 := by omega
        have hfit : S (j + 1) + 1 * R j < R (j + 1) := by
          rw [hb, Nat.add_mul (a (j + 1) + c) 1, one_mul] at hw
          omega
        have hprev := ih (by omega) 1 hfit
        simp only [Nat.cast_one] at hprev
        have hcast : (b : ℝ) = (a (j + 1) : ℝ) + (c : ℝ) + 1 := by exact_mod_cast hb
        rw [← hcast]
        linarith only [hprev, he, hdecr j]
  have hlt : E (n + 1) < 1 := by
    have h := hbound n le_rfl 0 (by simpa [S] using ha (n + 1) le_rfl)
    simp only [Nat.cast_zero, zero_add, one_mul] at h
    linarith only [h, hdecr n]
  have hnonneg : 0 ≤ E (n + 1) := sum_nonneg fun j _ ↦
    mul_nonneg (Nat.cast_nonneg _) (hpos j).le
  have hsum : (S (n + 1) : ℝ) * ((2 + Real.sqrt 2) / 2) =
      ((∑ k ∈ range (n + 1), a k * R' (k + 1) : ℕ) : ℝ) + E (n + 1) := by
    simp only [S, E, Nat.cast_sum, Nat.cast_mul, sum_mul]
    simp_rw [mul_assoc, mixed_digit_shift hR hR', mul_add, sum_add_distrib]
  change ⌊(S (n + 1) : ℝ) * ((2 + Real.sqrt 2) / 2)⌋₊ = _
  rw [hsum, Nat.floor_eq_iff (by positivity)]
  exact ⟨le_add_of_nonneg_right hnonneg, add_lt_add_right hlt _⟩

end MetaMathlibExt

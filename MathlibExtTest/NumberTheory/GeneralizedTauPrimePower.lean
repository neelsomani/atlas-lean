/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.PentagonalExpand
import MathlibExt.NumberTheory.GeneralizedTauPrimePower

namespace MathlibExtTest.NumberTheory.GeneralizedTauPrimePower

open MetaMathlibExt PowerSeries

-- Only the indices -1, 0, 1 and 2 can contribute through degree six.
private theorem pentagonal_gap {i : ℕ} (hi : i < 7) (h₀ : i ≠ 0) (h₁ : i ≠ 1) (h₂ : i ≠ 2)
    (h₅ : i ≠ 5) : i ∉ Set.range pentagonal := by
  rintro ⟨t, rfl⟩
  have hl : -1 ≤ t := by
    by_contra! h
    have hle : pentagonal (-2) ≤ pentagonal t :=
      pentagonal_strictAntiOn.antitoneOn (show t ≤ 0 by omega) (by decide) (by omega)
    rw [show pentagonal (-2) = 7 by norm_num [pentagonal_def]] at hle
    omega
  have hu : t ≤ 2 := by
    by_contra! h
    have hle : pentagonal 3 ≤ pentagonal t :=
      pentagonal_strictMonoOn.monotoneOn (by decide) (show 0 ≤ t by omega) (by omega)
    rw [show pentagonal 3 = 12 by norm_num [pentagonal_def]] at hle
    omega
  interval_cases t <;> norm_num [pentagonal_def] at *

private theorem trunc_pentagonal : trunc 7 (pentagonalSeries ℤ) =
    (1 - Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 5 : Polynomial ℤ) := by
  have c₀ : coeff 0 (pentagonalSeries ℤ) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_pentagonalSeries_int]
  have c₁ : coeff 1 (pentagonalSeries ℤ) = -1 := by
    simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ 1
  have c₂ : coeff 2 (pentagonalSeries ℤ) = -1 := by
    simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ (-1)
  have c₅ : coeff 5 (pentagonalSeries ℤ) = 1 := by
    simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ 2
  have cz (i : ℕ) (hi : i < 7) (h₀ : i ≠ 0) (h₁ : i ≠ 1) (h₂ : i ≠ 2) (h₅ : i ≠ 5) :
      coeff i (pentagonalSeries ℤ) = 0 :=
    coeff_pentagonalSeries_eq_zero ℤ (pentagonal_gap hi h₀ h₁ h₂ h₅)
  ext m
  rw [coeff_trunc, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
  by_cases h : m < 7
  · interval_cases m <;> norm_num [c₀, c₁, c₂, c₅, cz]
  · have hm (i : ℕ) (hi : i < 7) : m ≠ i := by omega
    simp [h, hm 0 (by decide), (hm 1 (by decide)).symm, hm 2 (by decide), hm 5 (by decide)]

-- Compute tau over the integers by powering a low-degree polynomial, without Frobenius.
private theorem tau_low_degree (k m : ℕ) (hm : m < 7) :
    generalizedTau (k : ℤ) (m + 1) =
      ((1 - Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 5 : Polynomial ℤ) ^ k).coeff m := by
  rw [generalizedTau_natCast, coeff_succ_X_mul, ← coeff_coe_trunc_of_lt hm, ← trunc_trunc_pow,
    trunc_pentagonal, coeff_coe_trunc_of_lt hm, ← Polynomial.coe_pow, Polynomial.coeff_coe]

-- At p = 2, s = 2, n = 2, the degree is not divisible by 4.
example : generalizedTau 4 3 ≡
    ∑ t ∈ Finset.Icc (-2 : ℤ) 2, if 2 = 4 * pentagonal t then (t.negOnePow : ℤ) else 0
    [ZMOD 2] := by
  have h : generalizedTau 4 3 = 2 := by
    change generalizedTau ((4 : ℕ) : ℤ) (2 + 1) = 2
    rw [tau_low_degree 4 2 (by decide)]
    ring_nf
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  rw [h]
  simp only [Int.Icc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, pentagonal_def]
  decide

-- At p = 2, s = 1, n = 6, the quotient 3 is a gap between pentagonal degrees.
example : generalizedTau 2 7 ≡
    ∑ t ∈ Finset.Icc (-6 : ℤ) 6, if 6 = 2 * pentagonal t then (t.negOnePow : ℤ) else 0
    [ZMOD 2] := by
  have h : generalizedTau 2 7 = -2 := by
    change generalizedTau ((2 : ℕ) : ℤ) (6 + 1) = -2
    rw [tau_low_degree 2 6 (by decide)]
    ring_nf
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  rw [h]
  simp only [Int.Icc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, pentagonal_def]
  decide

-- At p = 3, s = 1, n = 3, the sole contributing index is 1, with sign -1, not +1.
example : generalizedTau 3 4 ≡
    ∑ t ∈ Finset.Icc (-3 : ℤ) 3, if 3 = 3 * pentagonal t then (t.negOnePow : ℤ) else 0
    [ZMOD 3] := by
  have h : generalizedTau 3 4 = 5 := by
    change generalizedTau ((3 : ℕ) : ℤ) (3 + 1) = 5
    rw [tau_low_degree 3 3 (by decide)]
    ring_nf
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  rw [h]
  simp only [Int.Icc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, pentagonal_def]
  decide

-- Independently check the public coefficient formula at j = 4 < n = 6, with index -1.
example : coeff 4 (expand 2 (by decide) (pentagonalSeries ℤ)) =
    ∑ t ∈ Finset.Icc (-6 : ℤ) 6, if 2 * pentagonal t = 4 then (t.negOnePow : ℤ) else 0 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, coeff_expand_mul]
  have h : coeff 2 (pentagonalSeries ℤ) = -1 := by
    simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ (-1)
  rw [h]
  simp only [Int.Icc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, pentagonal_def]
  decide

-- A client can apply the prime-power congruence directly at p = 2, s = 2, n = 4.
example : generalizedTau 4 5 ≡ -1 [ZMOD 2] := by
  refine (generalizedTau_prime_pow_succ_modEq 2 Nat.prime_two 2 (by decide) 4).trans ?_
  simp only [Int.Icc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, pentagonal_def]
  decide

end MathlibExtTest.NumberTheory.GeneralizedTauPrimePower

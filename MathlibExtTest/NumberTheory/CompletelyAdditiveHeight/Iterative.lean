/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CompletelyAdditiveHeight.Iterative
import MathlibExt.NumberTheory.CompletelyAdditiveHeightExistsHeightFunctionWithProfile
import MathlibExt.NumberTheory.CompletelyAdditiveHeightIsGreatestPrimeIndexHeightLevel
import Mathlib.Data.Nat.Log

namespace MetaMathlibExt

private noncomputable def testHeight (m : ℕ) : ℕ :=
  2 * additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) m

-- Independently exhibit a completely additive solution for `f i = 2 ^ (i - 1)` and `j = 2`.
example : IsCompletelyAdditiveNat testHeight ∧
    ∀ i, 1 ≤ i → testHeight (nthPrimeOne i) = testHeight (2 ^ (i - 1)) + 2 := by
  constructor
  · intro a b ha hb
    simp only [testHeight, isCompletelyAdditiveNat_additiveOfPrimeValues _ a b ha hb, Nat.mul_add]
  · intro i hi
    have hpow := (isGreatest_primeIndexHeight_level (i - 1)).1.2
    simp only [testHeight, additiveOfPrimeValues_prime _ (nthPrimeOne_prime i),
      count_nthPrimeOne i hi, hpow]
    omega

-- Compute the prime heights of any such solution directly from the values at powers of two.
example {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (hrec : ∀ i, 1 ≤ i → H (nthPrimeOne i) = H (2 ^ (i - 1)) + 2) :
    IsHeightFunction H ∧ {p : ℕ | p.Prime ∧ H p = 1} = ∅ ∧
      {p : ℕ | p.Prime ∧ H p = 2} = {2} := by
  have h₂ := hrec 1 le_rfl
  simp only [nthPrimeOne_one_two_three.1, Nat.sub_self, pow_zero, hH.map_one, zero_add] at h₂
  have hpow (k : ℕ) : H (2 ^ k) = 2 * k := by
    induction k with
    | zero => simp only [pow_zero, hH.map_one, mul_zero]
    | succ k ih =>
      rw [pow_succ, hH (2 ^ k) 2 (pow_pos (by decide) k) (by decide), ih, h₂]
      omega
  have hindex (i : ℕ) (hi : 1 ≤ i) : H (nthPrimeOne i) = 2 * i := by
    rw [hrec i hi, hpow]
    omega
  have hpEq (p : ℕ) (hp : p.Prime) : H p = 2 * (Nat.count Nat.Prime p + 1) := by
    simpa only [nthPrimeOne_count p hp] using hindex (Nat.count Nat.Prime p + 1) (Nat.succ_pos _)
  refine ⟨⟨hH, fun p hp => ?_, fun n _ => ?_⟩, ?_, ?_⟩
  · rw [hpEq p hp]
    omega
  · refine (Set.finite_singleton (nthPrimeOne (n / 2))).subset ?_
    rintro p ⟨hp, hpn⟩
    have := hpEq p hp
    have hidx : n / 2 = Nat.count Nat.Prime p + 1 := by omega
    exact Set.mem_singleton_iff.mpr (by rw [hidx, nthPrimeOne_count p hp])
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp, h⟩
    have := hpEq p hp
    omega
  · ext p
    constructor
    · rintro ⟨hp, h⟩
      have := hpEq p hp
      have hidx : Nat.count Nat.Prime p + 1 = 1 := by omega
      exact Set.mem_singleton_iff.mpr (by
        simpa only [hidx, nthPrimeOne_one_two_three.1] using (nthPrimeOne_count p hp).symm)
    · intro hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact ⟨Nat.prime_two, h₂⟩

-- A client obtains a height function with the specified recurrence from the public theorem.
example : ∃ H : ℕ → ℕ, IsHeightFunction H ∧
    ∀ i, 1 ≤ i → H (nthPrimeOne i) = H (2 ^ (i - 1)) + 2 := by
  have h := isHeightFunction_of_iterative (fun i => 2 ^ (i - 1)) (by decide) ?_ ?_ (j := 2) (by decide)
  · obtain ⟨H, hH, hrec⟩ := h.1
    exact ⟨H, h.2 H hH hrec, hrec⟩
  · intro i r hi hr hd
    have hp := nthPrimeOne_prime r
    have hr₂ := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
    have hEq : nthPrimeOne r = nthPrimeOne 1 := hr₂.trans nthPrimeOne_one_two_three.1.symm
    have hr₁ : r = 1 := by
      rw [← count_nthPrimeOne r hr, hEq, count_nthPrimeOne 1 le_rfl]
    have hi₁ : i ≠ 1 := by
      rintro rfl
      exact hp.not_dvd_one (by simpa only [Nat.sub_self, pow_zero] using hd)
    omega
  · intro t _
    refine (Set.finite_singleton (Nat.log 2 t + 1)).subset ?_
    rintro i ⟨hi, hfi⟩
    rw [Set.mem_singleton_iff, ← hfi, Nat.log_pow (by decide : 1 < (2 : ℕ)), Nat.sub_add_cancel hi]

end MetaMathlibExt

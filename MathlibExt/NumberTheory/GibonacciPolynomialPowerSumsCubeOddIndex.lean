/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.FibonacciPolynomialOddPowerSub
import MathlibExt.NumberTheory.GibonacciPolynomialPowerSums

/-!
# Cubic series at odd Fibonacci polynomial indices

For a real argument `x > 0`, two series centered at the odd Fibonacci indices `3, 5, …`
telescope. With shifts `1` and `2`, the cubic power-difference and Catalan identities turn
both summands into `x ^ 2 + 4` times a difference of reciprocal cubes. The shift `1` leaves
only the reciprocal cube at index `2`; the shift `2` leaves the ones at indices `1` and `3`.

## References

* Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
  The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Corollary 4.7 (p. 155),
  Theorem 1.7 and Lemmas 2.1, 2.4, 2.5 and 4.1.
* Thomas Koshy, *Sums Involving Gibonacci Polynomial Squares*, The Fibonacci Quarterly
  61 (2023), no. 2, 98–104, §1.1, Eq. (4), and §1.3, Lemmas 3–4, cited by Lin and Zhou
  for the Catalan identity and reciprocal-power telescoping.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1
local notation "F[" x ", " n "]" => aeval x (𝔣 n)
local notation "L[" x ", " n "]" => aeval x (𝔩 n)

/-- **Cubic-denominator series for odd-index Fibonacci polynomials.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and
$g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. For every real $x > 0$,
$$
\sum_{n \ge 1} \frac{(x^3 + 3x) f_{6n+3}(x) - 3x f_{2n+1}(x)}{(f_{2n+1}(x)^2 - 1)^3} =
\frac{x^2 + 4}{x^3}
$$
and
$$
\sum_{n \ge 1} \frac{x(x^4 + 4x^2 + 3) \ell_{6n+3}(x) + 3x \ell_{2n+1}(x)}
{(f_{2n+1}(x)^2 + x^2)^3} =
\frac{(x^2 + 4)\bigl((x^2 + 1)^3 + 1\bigr)}{(x^2 + 1)^3}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.7 (`fq-2024-linzhou02172024-cor-4.7`). -/
public theorem tsum_fibPoly_cube_odd_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔣 (6 * (n + 1) + 3)) -
          3 * x * aeval x (𝔣 (2 * (n + 1) + 1))) /
        (aeval x (𝔣 (2 * (n + 1) + 1)) ^ 2 - 1) ^ 3 =
      (x ^ 2 + 4) / x ^ 3 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔩 (6 * (n + 1) + 3)) +
          3 * x * aeval x (𝔩 (2 * (n + 1) + 1))) /
          (aeval x (𝔣 (2 * (n + 1) + 1)) ^ 2 + x ^ 2) ^ 3 =
        (x ^ 2 + 4) * ((x ^ 2 + 1) ^ 3 + 1) / (x ^ 2 + 1) ^ 3 := by
  have hf₂ : F[x, 2] = x := by simp
  have hf₃ : F[x, 3] = x ^ 2 + 1 := by simp; ring
  have hf₆ : F[x, 6] = x * (x ^ 4 + 4 * x ^ 2 + 3) := by simp; ring
  have hl₃ : L[x, 3] = x ^ 3 + 3 * x := by simp [map_ofNat]; ring
  -- Catalan with lower index 1 expresses each odd term as a sum of two squares.
  have hodd (n : ℕ) : 0 ≤ F[x, 2 * n + 1] := by
    have h := congrArg (aeval x) (gibonacciPoly_mul_sub_sq (k := n) (Nat.le_succ n)).1
    have hlo : n + 1 - n = 1 := by omega
    have hhi : n + 1 + n = 2 * n + 1 := by omega
    have he : Even (n + 1 + n + 1) := ⟨n + 1, by omega⟩
    simp only [map_sub, map_mul, map_pow, map_neg, map_one] at h
    rw [he.neg_one_pow, hlo, hhi, generalizedFibonacciPolynomial_one, map_one,
      mul_one, one_mul] at h
    linarith [sq_nonneg F[x, n], sq_nonneg F[x, n + 1]]
  -- The recurrence now bounds every positive even term below by `f₂(x) = x`.
  have hmono : Monotone (fun n : ℕ ↦ F[x, 2 * n + 2]) := by
    apply monotone_nat_of_le_succ
    intro n
    change F[x, 2 * n + 2] ≤ F[x, 2 * (n + 1) + 2]
    rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by omega,
      generalizedFibonacciPolynomial_add_two 0 1 X 1 (2 * n + 2), map_add, map_mul,
      aeval_X, map_mul, map_one, one_mul, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by omega]
    exact le_add_of_nonneg_left (mul_nonneg hx.le (hodd (n + 1)))
  have heven_ne (n : ℕ) : F[x, 2 * n + 2] ≠ 0 := by
    have h := hmono (Nat.zero_le n)
    change F[x, 2] ≤ F[x, 2 * n + 2] at h
    rw [hf₂] at h
    exact (hx.trans_le h).ne'
  constructor
  · calc
      _ = ∑' n : ℕ, (x ^ 2 + 4) *
          (1 / F[x, 2 * n + 2] ^ 3 - 1 / F[x, 2 * n + 2 + 2] ^ 3) := by
        apply tsum_congr
        intro n
        let m := 2 * (n + 1) + 1
        have hk : 1 ≤ m := by dsimp [m]; omega
        have hlo : m - 1 = 2 * n + 2 := by dsimp [m]; omega
        have hhi : m + 1 = 2 * n + 2 + 2 := by dsimp [m]; omega
        have hmul : m * 3 = 6 * (n + 1) + 3 := by dsimp [m]; omega
        have hm : Odd m := ⟨n + 1, rfl⟩
        have hs : Odd (m + 1 + 1) := ⟨n + 2, by dsimp [m]; omega⟩
        have hden := congrArg (aeval x) (gibonacciPoly_mul_sub_sq hk).1
        simp only [map_sub, map_mul, map_pow, map_neg, map_one] at hden
        rw [hs.neg_one_pow, hlo, hhi, generalizedFibonacciPolynomial_one, map_one,
          one_pow, mul_one] at hden
        have hprod : F[x, m] ^ 2 - 1 = F[x, 2 * n + 2] * F[x, 2 * n + 2 + 2] := by
          linear_combination -hden
        have hnum := congrArg (aeval x) ((fibPoly_pow_odd_sub hk 1).1 (by decide))
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add,
          map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat, aeval_X,
          hlo, hhi, hmul, Nat.choose_zero_right, Nat.choose_one_right, Nat.mul_zero,
          Nat.mul_one, hm.neg_one_pow, generalizedFibonacciPolynomial_one, hl₃] at hnum
        have hhi_ne : F[x, 2 * n + 2 + 2] ≠ 0 := by
          rw [show 2 * n + 2 + 2 = 2 * (n + 1) + 2 by omega]
          exact heven_ne (n + 1)
        change ((_ * F[x, 6 * (n + 1) + 3] - 3 * x * F[x, m]) / _) = _
        rw [hprod, div_sub_div _ _ (pow_ne_zero 3 (heven_ne n)) (pow_ne_zero 3 hhi_ne),
          ← mul_pow, one_mul, mul_one, ← mul_div_assoc]
        congr 1
        linear_combination -hnum
      _ = _ := by
        rw [tsum_mul_left, tsum_inv_pow_gibonacciPoly_succ_sub_odd hx (Or.inl rfl)
          (k := 1) (lam := 3) (by decide) (by decide)]
        simp [div_eq_mul_inv]
  · calc
      _ = ∑' n : ℕ, (x ^ 2 + 4) *
          (1 / F[x, 2 * n + 1] ^ 3 - 1 / F[x, 2 * n + 1 + 4] ^ 3) := by
        apply tsum_congr
        intro n
        let m := 2 * (n + 1) + 1
        have hk : 2 ≤ m := by dsimp [m]; omega
        have hlo : m - 2 = 2 * n + 1 := by dsimp [m]; omega
        have hhi : m + 2 = 2 * n + 1 + 4 := by dsimp [m]; omega
        have hmul : m * 3 = 6 * (n + 1) + 3 := by dsimp [m]; omega
        have hm : Even (m + 1) := ⟨n + 2, by dsimp [m]; omega⟩
        have hs : Even (m + 2 + 1) := ⟨n + 3, by dsimp [m]; omega⟩
        have hden := congrArg (aeval x) (gibonacciPoly_mul_sub_sq hk).1
        simp only [map_sub, map_mul, map_pow, map_neg, map_one] at hden
        rw [hs.neg_one_pow, hlo, hhi, hf₂, one_mul] at hden
        have hprod : F[x, m] ^ 2 + x ^ 2 = F[x, 2 * n + 1] * F[x, 2 * n + 1 + 4] := by
          linear_combination -hden
        have hnum := congrArg (aeval x) ((fibPoly_pow_odd_sub hk 1).2 (by decide))
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add,
          map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat, aeval_X,
          hlo, hhi, hmul, Nat.choose_zero_right, Nat.choose_one_right, Nat.mul_zero,
          Nat.mul_one, hm.neg_one_pow, hf₂, hf₆] at hnum
        have hbase : 0 < F[x, m] ^ 2 + x ^ 2 :=
          add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hx)
        obtain ⟨hlo_ne, hhi_ne⟩ := mul_ne_zero_iff.mp (hprod ▸ hbase.ne')
        change ((_ * L[x, 6 * (n + 1) + 3] + 3 * x * L[x, m]) / _) = _
        rw [hprod, div_sub_div _ _ (pow_ne_zero 3 hlo_ne) (pow_ne_zero 3 hhi_ne),
          ← mul_pow, one_mul, mul_one, ← mul_div_assoc]
        congr 1
        linear_combination -hnum
      _ = _ := by
        rw [tsum_mul_left, tsum_inv_pow_gibonacciPoly_succ_sub_even hx (Or.inl rfl)
          (k := 2) (lam := 3) (by decide) (by decide),
          show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.sum_pair (by decide)]
        norm_num only [Nat.reduceMul, Nat.reduceSub, generalizedFibonacciPolynomial_one,
          map_one, one_pow, div_one, hf₃]
        have h : (x ^ 2 + 1) ^ 3 ≠ 0 := by positivity
        rw [mul_div_assoc, add_div, div_self h]

end MetaMathlibExt

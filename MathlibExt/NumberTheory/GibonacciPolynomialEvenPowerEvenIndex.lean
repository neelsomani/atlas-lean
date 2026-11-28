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
import MathlibExt.NumberTheory.GibonacciPolynomialPowerSums
import MathlibExt.NumberTheory.GibonacciPolynomialPowerSumsFibPolyPowEvenSub
import MathlibExt.NumberTheory.Recurrences.GeneralizedFibonacciIdentities

/-!
# Series of even powers of Fibonacci polynomials at even indices

For real `x > 0` and positive natural numbers `k` and `m`, the Catalan identity and the
binomial expansion of the difference of two `2m`-th powers turn the summand at each even
center `2n` into a scaled difference of reciprocal powers. The lower center is `2L`,
where `L = (k + 1) / 2` for odd `k` and `L = k / 2 + 1` for even `k`. The first `k`
reciprocal powers at positive indices of the shift's parity survive telescoping.

## References

* Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
  The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Theorem 1.1 (pp. 148, 151–152),
  Lemmas 2.1–2.3 and 3.1, and the Binet formula in §2.
* Thomas Koshy, *Sums Involving Gibonacci Polynomial Squares*, The Fibonacci Quarterly
  61 (2023), no. 2, 98–104, §1.1, Eq. (4), and §1.3, Lemmas 1–2 (cited by Lin and Zhou
  for the Catalan and telescoping identities).
* Thomas Koshy, *Fibonacci and Lucas Numbers with Applications*, vol. 2,
  John Wiley & Sons, 2019, §31.1 (Binet formula, cited by Lin and Zhou in §2).
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔏[" k "]" => ite (Odd k) ((k + 1) / 2) (k / 2 + 1)
local notation "𝔰[" k ", " r "]" => ite (Odd k) (2 * r - 1) (2 * r)

/-- **Series of even powers of Fibonacci polynomials at even indices.** Let $f_i$ be the
Fibonacci polynomials, defined by $f_0 = 0$, $f_1 = 1$ and $f_{i+2} = x f_{i+1} + f_i$. Let
$x > 0$ be real and let $k$ and $m$ be positive integers. If $k$ is odd, put $L = (k + 1)/2$ and
$s_r = 2r - 1$; if $k$ is even, put $L = k/2 + 1$ and $s_r = 2r$. Then
$$
\sum_{n \ge L} \frac{\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(k+1)j} f_{2k(m-j)}(x)
f_{4n(m-j)}(x)}{\bigl(f_{2n}(x)^2 - (-1)^k f_k(x)^2\bigr)^{2m}} =
(x^2 + 4)^{m-1} \sum_{r=1}^{k} \frac{1}{f_{s_r}(x)^{2m}}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.1 (`fq-2024-linzhou02172024-thm-1.1`). -/
public theorem tsum_fibPoly_even_pow_even_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ ((k + 1) * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 (4 * (n + 𝔏[k]) * (m - j)))) /
        (aeval x (𝔣 (2 * (n + 𝔏[k]))) ^ 2 - (-1) ^ k * aeval x (𝔣 k) ^ 2) ^ (2 * m) =
      (x ^ 2 + 4) ^ (m - 1) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 𝔰[k, r]) ^ (2 * m) := by
  let F (i : ℕ) : ℝ := aeval x (𝔣 i)
  have hne (i : ℕ) (hi : 0 < i) : F i ≠ 0 := by
    let s := Real.sqrt (x ^ 2 + 4)
    let a := (x + s) / 2
    let b := (x - s) / 2
    have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
    -- The two Binet roots satisfy `a + b = x > 0` and `a - b = s > 0`.
    have hab : |b| < a := abs_lt.mpr ⟨by dsimp [a, b]; linarith, by dsimp [a, b]; linarith⟩
    have hpow : b ^ i < a ^ i := by
      apply (le_abs_self (b ^ i)).trans_lt
      rw [abs_pow]
      exact pow_lt_pow_left₀ hab (abs_nonneg _) hi.ne'
    have hbinet := generalizedFibonacci_binet x F (fun n ↦ by simp [F]) i
    change F i = (F 1 - F 0 * b) / s * a ^ i + (F 0 * a - F 1) / s * b ^ i at hbinet
    have hFi : F i = (a ^ i - b ^ i) / s := by
      rw [hbinet, show F 0 = 0 by simp [F], show F 1 = 1 by simp [F]]
      ring
    rw [hFi]
    exact (div_pos (sub_pos.mpr hpow) hs).ne'
  let d : ℕ := if Odd k then 1 else 2
  have hd : 0 < d := by dsimp [d]; split <;> decide
  have hstart : 2 * 𝔏[k] = k + d := by
    by_cases ho : Odd k
    · simp only [d, ite_eq_left ho]
      obtain ⟨t, ht⟩ := ho
      omega
    · simp only [d, ite_eq_right ho]
      obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp ho
      omega
  have hsign (i : ℕ) : (-1 : ℝ) ^ (2 * i + k + 1) = (-1) ^ (k + 1) := by
    rw [show 2 * i + k + 1 = 2 * i + (k + 1) by omega, pow_add,
      (even_two_mul i).neg_one_pow, one_mul]
  calc
    _ = ∑' n : ℕ, (x ^ 2 + 4) ^ (m - 1) * (1 / F (2 * n + d) ^ (2 * m) -
        1 / F (2 * n + d + 2 * k) ^ (2 * m)) := by
      apply tsum_congr
      intro n
      let i := n + 𝔏[k]
      have hlo : 2 * i - k = 2 * n + d := by dsimp [i]; omega
      have hhi : 2 * i + k = 2 * n + d + 2 * k := by dsimp [i]; omega
      have hki : k ≤ 2 * i := by dsimp [i]; omega
      have hden := congrArg (aeval x) (gibonacciPoly_mul_sub_sq hki).1
      simp only [map_sub, map_mul, map_pow, map_neg, map_one, hsign, pow_succ (-1 : ℝ)] at hden
      have hprod : F (2 * i) ^ 2 - (-1) ^ k * F k ^ 2 = F (2 * i - k) * F (2 * i + k) := by
        dsimp only [F]
        linear_combination -hden
      have hnum := congrArg (aeval x) (fibPoly_pow_even_sub hki m)
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat, map_sum,
        map_natCast, aeval_X, show 2 * (2 * i) = 4 * i by omega] at hnum
      simp_rw [pow_mul (-1 : ℝ) (2 * i + k + 1), hsign, ← pow_mul (-1 : ℝ) (k + 1)] at hnum
      change (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ ((k + 1) * j) *
        F (2 * k * (m - j)) * F (4 * i * (m - j))) / (F (2 * i) ^ 2 - (-1) ^ k * F k ^ 2) ^
          (2 * m) = _
      rw [← hnum, hprod, mul_pow, hlo, hhi,
        div_sub_div _ _ (pow_ne_zero _ (hne _ (by omega))) (pow_ne_zero _ (hne _ (by omega))),
        one_mul, mul_one, ← mul_div_assoc]
    _ = _ := by
      rw [tsum_mul_left]
      have hm' : 0 < 2 * m := by omega
      by_cases ho : Odd k
      · rw [show d = 1 by simp [d, ho], tsum_inv_pow_gibonacciPoly_sub_odd hx (Or.inl rfl) ho hm']
        simp only [ite_eq_left ho]
      · rw [show d = 2 by simp [d, ho],
          tsum_inv_pow_gibonacciPoly_sub_even hx (Or.inl rfl) (Nat.not_odd_iff_even.mp ho) hm']
        simp only [ite_eq_right ho]

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import MathlibExt.Combinatorics.DixonSummation
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition

/-!
# Alternating two-binomial Catalan convolution with Lucas sequences

For every integer $p$ and natural number $n$, the alternating convolution of
$U_{2n-k}(p,-1)V_k(p,-1)$ with weights $\binom{2n}{k}\binom{4n}{2k} C_k C_{2n-k}$
over $0\le k\le 2n$ is $(-1)^n\binom{3n+1}{n} C_n C_{2n} U_{2n}(p,-1)$,
where $C_k$ denotes the $k$-th Catalan number. Reflecting the sum and using Lucas addition
reduces it to a scalar convolution. After cancellation of factorials and the shift $j=k-n$,
that scalar sum is Dixon's inverse-factorial sum at parameters $(n,n,n+1)$.

## References

* John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
  Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64, Proposition 2.13.
* Wenchang Chu and Emrah Kılıç, *Binomial sums involving Catalan numbers*, Rocky Mountain Journal
  of Mathematics 51 (2021), no. 4, 1221–1225, Theorem 3 (the scalar identity cited in
  Proposition 2.13).
* Abdelmalek Abdesselam, *An algebraic independence result related to a conjecture of Dixmier on
  binary form invariants*, Research in the Mathematical Sciences 6 (2019), Article 26,
  Proposition 5 (Dixon's summation). The proof uses `dixon_kernel_sum` from
  `MathlibExt.Combinatorics.DixonSummation`.
* Vladimir V. Kruchinin and Maria Y. Perminova, *Identities and Hadamard Product of the Generalized
  Fibonacci, Lucas, Catalan, and Harmonic Numbers*, Journal of Integer Sequences 28 (2025),
  Article 25.8.8, 1–17, Proposition 1 (Lucas addition).
* The reflection argument follows `lucasU_lucasV_sum_choose_cube_alternating` in
  `MathlibExt.NumberTheory.Recurrences.LucasDixonBinomialSum` and uses `two_mul_lucasU_add` from
  `MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition`.
-/

namespace MetaMathlibExt

open Finset
open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted (two_mul_lucasU_add)

private theorem sum_signed_two_binomial_catalan (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), (-1 : ℚ) ^ k *
        ((2 * n).choose k * (4 * n).choose (2 * k) * catalan k * catalan (2 * n - k) : ℚ) =
      (-1) ^ n * ((3 * n + 1).choose n * catalan n * catalan (2 * n) : ℚ) := by
  let f (j : ℤ) : ℚ := (-1 : ℚ) ^ j * invFact ((n : ℤ) + j) * invFact ((n : ℤ) - j) *
    invFact ((n : ℤ) + j) * invFact ((n : ℤ) - j) *
    invFact ((n : ℤ) + 1 + j) * invFact ((n : ℤ) + 1 - j)
  let c : ℚ := (-1 : ℚ) ^ n * (2 * n).factorial * (4 * n).factorial
  have hd := dixon_kernel_sum (n : ℤ) n ((n : ℤ) + 1)
    (by positivity) (by positivity) (by positivity)
  change (∑ j ∈ Icc (-(n : ℤ)) (n : ℤ), f j) = _ at hd
  rw [Int.Icc_eq_finset_map, sum_map,
    show ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 by omega] at hd
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply] at hd
  calc
    _ = ∑ k ∈ range (2 * n + 1), c * f (-(n : ℤ) + (k : ℤ)) := by
      refine sum_congr rfl fun k hk => ?_
      have hkn := mem_range_succ_iff.mp hk
      have hsign : (-1 : ℚ) ^ n * (-1 : ℚ) ^ (-(n : ℤ) + (k : ℤ)) = (-1 : ℚ) ^ k := by
        rw [← zpow_natCast (-1 : ℚ) n, ← zpow_add₀ (by norm_num),
          show (n : ℤ) + (-(n : ℤ) + (k : ℤ)) = (k : ℤ) by omega, zpow_natCast]
      simp only [f, c,
        show (n : ℤ) + (-(n : ℤ) + (k : ℤ)) = (k : ℤ) by omega,
        show (n : ℤ) - (-(n : ℤ) + (k : ℤ)) = ↑(2 * n - k : ℕ) by omega,
        show (n : ℤ) + 1 + (-(n : ℤ) + (k : ℤ)) = ↑(k + 1 : ℕ) by omega,
        show (n : ℤ) + 1 - (-(n : ℤ) + (k : ℤ)) = ↑(2 * n - k + 1 : ℕ) by omega,
        invFact_natCast, catalan_eq_centralBinom_div]
      rw [Nat.cast_div_charZero (Nat.succ_dvd_centralBinom k),
        Nat.cast_div_charZero (Nat.succ_dvd_centralBinom (2 * n - k))]
      simp only [Nat.centralBinom]
      rw [Nat.cast_choose ℚ hkn, Nat.cast_choose ℚ (show 2 * k ≤ 4 * n by omega),
        Nat.cast_choose ℚ (show k ≤ 2 * k by omega),
        Nat.cast_choose ℚ (show 2 * n - k ≤ 2 * (2 * n - k) by omega),
        show 4 * n - 2 * k = 2 * (2 * n - k) by omega,
        show 2 * k - k = k by omega,
        show 2 * (2 * n - k) - (2 * n - k) = 2 * n - k by omega,
        Nat.factorial_succ k, Nat.factorial_succ (2 * n - k), ← hsign]
      push_cast
      field_simp
    _ = _ := by
      rw [← mul_sum, hd,
        show (n : ℤ) + n + ((n : ℤ) + 1) = ↑(3 * n + 1 : ℕ) by omega,
        show (n : ℤ) + ((n : ℤ) + 1) = ↑(2 * n + 1 : ℕ) by omega,
        show (n : ℤ) + n = ↑(2 * n : ℕ) by omega,
        show (n : ℤ) + 1 = ↑(n + 1 : ℕ) by omega]
      simp only [c, extFact_natCast, invFact_natCast, catalan_eq_centralBinom_div]
      rw [Nat.cast_div_charZero (Nat.succ_dvd_centralBinom n),
        Nat.cast_div_charZero (Nat.succ_dvd_centralBinom (2 * n))]
      simp only [Nat.centralBinom]
      rw [Nat.cast_choose ℚ (show n ≤ 3 * n + 1 by omega),
        Nat.cast_choose ℚ (show n ≤ 2 * n by omega),
        Nat.cast_choose ℚ (show 2 * n ≤ 2 * (2 * n) by omega),
        show 3 * n + 1 - n = 2 * n + 1 by omega,
        show 2 * n - n = n by omega, show 2 * (2 * n) - 2 * n = 2 * n by omega,
        show 2 * (2 * n) = 4 * n by omega,
        Nat.factorial_succ n, Nat.factorial_succ (2 * n)]
      push_cast
      field_simp

set_option backward.proofsInPublic true in
/-- **Alternating two-binomial Catalan convolution of U and V.** Let $p$ be an integer and let $U$
and $V$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so that $U_0 = 0$, $U_1 = 1$, $V_0 = 2$,
$V_1 = p$, and both satisfy $X_{j+2} = p X_{j+1} + X_j$. Writing $C_j$ for the $j$-th Catalan
number, for every natural number $n$
$$\sum_{k=0}^{2n} (-1)^k \binom{2n}{k} \binom{4n}{2k} C_k C_{2n-k} U_{2n-k} V_k =
(-1)^n \binom{3n+1}{n} C_n C_{2n} U_{2n}.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023,
Proposition 2.13. -/
public theorem lucasU_lucasV_sum_choose_sq_catalan_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        (-1) ^ k *
            ((2 * n).choose k * (4 * n).choose (2 * k) * catalan k * catalan (2 * n - k) : ℤ) *
          lucasU ⟨p, -1, by decide⟩ (2 * n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (-1) ^ n * ((3 * n + 1).choose n * catalan n * catalan (2 * n) : ℤ) *
        lucasU ⟨p, -1, by decide⟩ (2 * n) := by
  let P : LucasSequenceParams := ⟨p, -1, by decide⟩
  let a (k : ℕ) : ℤ := (-1) ^ k *
    ((2 * n).choose k * (4 * n).choose (2 * k) * catalan k * catalan (2 * n - k) : ℤ)
  have hrefl :
      ∑ k ∈ range (2 * n + 1), a k * lucasV P (2 * n - k) * lucasU P k =
        ∑ k ∈ range (2 * n + 1), a k * lucasU P (2 * n - k) * lucasV P k := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hkn := mem_range_succ_iff.mp hk
    have hsign : (-1 : ℤ) ^ (2 * n - k) = (-1) ^ k := by
      rw [neg_one_pow_eq_pow_mod_two (2 * n - k), neg_one_pow_eq_pow_mod_two k,
        show (2 * n - k) % 2 = k % 2 by omega]
    simp only [a, Nat.add_sub_cancel, Nat.sub_sub_self hkn, Nat.choose_symm hkn,
      show 2 * (2 * n - k) = 4 * n - 2 * k by omega,
      Nat.choose_symm (show 2 * k ≤ 4 * n by omega), hsign]
    ac_rfl
  have hscalar : ∑ k ∈ range (2 * n + 1), a k =
      (-1 : ℤ) ^ n * ((3 * n + 1).choose n * catalan n * catalan (2 * n) : ℤ) := by
    dsimp only [a]
    exact_mod_cast sum_signed_two_binomial_catalan n
  change (∑ k ∈ range (2 * n + 1), a k * lucasU P (2 * n - k) * lucasV P k) = _
  apply mul_left_cancel₀ (two_ne_zero (α := ℤ))
  calc
    2 * (∑ k ∈ range (2 * n + 1), a k * lucasU P (2 * n - k) * lucasV P k) =
        ∑ k ∈ range (2 * n + 1), a k *
          (lucasU P (2 * n - k) * lucasV P k + lucasV P (2 * n - k) * lucasU P k) := by
      rw [two_mul]
      simp only [mul_add, ← mul_assoc, sum_add_distrib, hrefl]
    _ = ∑ k ∈ range (2 * n + 1), a k * (2 * lucasU P (2 * n)) := by
      refine sum_congr rfl fun k hk => ?_
      rw [← two_mul_lucasU_add, Nat.sub_add_cancel (mem_range_succ_iff.mp hk)]
    _ = _ := by
      rw [← sum_mul, hscalar]
      ac_rfl

end MetaMathlibExt

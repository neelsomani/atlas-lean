/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ComplementarySequences
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.Linarith

/-!
# Formula for the non-pyramidal numbers

For $3 \le k \le 8$ and $n \ge 1$, the integer cube root of $\lfloor 6n/(k-2) \rfloor$
locates the $n$-th positive integer outside the $k$-gonal pyramidal numbers
$j(j+1)((k-2)j-(k-5))/6$, $j \ge 1$. The upper cutoff in the three-case formula cannot be
reached in this range of $k$, so the two-case formula suffices.

## References

* Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95,
  pp. 1–26, Section 2.2.4, Theorem 9, Equation (6) (p. 11), and the remark after
  Corollary 4 (p. 12). The proof uses `nthNonValue_pyramidal_two_case_le_eight` from
  `MathlibExt.NumberTheory.ComplementarySequences` for the remark's two-case formula.
-/

namespace MetaMathlibExt

/-- **Formula for the non-pyramidal numbers.** Let $3 \le k \le 8$, and for $j \ge 1$ let
$P(k, j) = j (j + 1) ((k - 2) j - (k - 5))/6$ be the $k$-gonal pyramidal numbers. For every
integer $n \ge 1$, put $s = \lfloor \sqrt[3]{6n/(k - 2)} \rfloor$. Then the $n$-th positive
integer that is not of the form $P(k, j)$ with $j \ge 1$ equals $n + s + 1$ if
$6n \ge s^3 (k - 2) + 3 s^2 (k - 1) + s (2k - 1) + 6$; otherwise it equals $n + s - 1$ if
$6n \le s (s - 1) (s (k - 2) + k + 1)$, and $n + s$ if not.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 9, Equation (6). -/
public theorem nthNonValue_pyramidal (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) (n : ℕ)
    (hn : 1 ≤ n) :
    let s := Nat.nthRoot 3 (6 * n / (k - 2))
    nthNonValue (fun j => j * (j + 1) * ((k - 2) * j + 5 - k) / 6) n =
      if s ^ 3 * (k - 2) + 3 * s ^ 2 * (k - 1) + s * (2 * k - 1) + 6 ≤ 6 * n then n + s + 1
      else if 6 * n ≤ s * (s - 1) * (s * (k - 2) + k + 1) then n + s - 1
      else n + s := by
  intro s
  have hd : 0 < k - 2 := by omega
  have hd' : k - 2 ≤ 6 := by omega
  have hcube : 6 * n < (s + 1) ^ 3 * (k - 2) :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_pow_nthRoot_add_one (by decide) _)
  have hs : 1 ≤ s := by
    apply (Nat.le_nthRoot_iff (by decide)).mpr
    apply (Nat.le_div_iff_mul_le hd).mpr
    simpa using (show k - 2 ≤ 6 * n by omega)
  -- The cutoff minus the scaled next cube is 3s(s - 1) + (8 - k)(s + 1).
  have hcut : (s + 1) ^ 3 * (k - 2) ≤
      s ^ 3 * (k - 2) + 3 * s ^ 2 * (k - 1) + s * (2 * k - 1) + 6 := by
    rw [show k - 1 = (k - 2) + 1 by omega, show 2 * k - 1 = 2 * (k - 2) + 3 by omega]
    nlinarith only [Nat.mul_le_mul_left s hs, Nat.mul_le_mul_left (s + 1) hd']
  rw [ite_eq_right (hcube.trans_le hcut).not_ge]
  exact nthNonValue_pyramidal_two_case_le_eight k hk hk' n hn

end MetaMathlibExt

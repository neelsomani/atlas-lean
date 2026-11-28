/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PadicValNat
public import MathlibExt.Analysis.SpecialFunctions.TakagiFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The midpoint recurrence for dyadic Takagi values

For natural numbers `k` and `r` with `1 ≤ r` and `r < 2 ^ k`, the midpoint correction on the
mesh of denominator `2 ^ k` is `(1 - padicValNat 2 r) / 2 ^ k`. The coefficient of each term
in the Takagi series counts disagreements with earlier digits. Grouping the series by the earlier
digit gives a finite sum of triangular waves, whose second differences are supported at their
troughs and peaks.

## References

* Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences
  27 (2024), Article 24.2.7, pp. 1–14, Definition 3 and Theorems 24 and 25. The argument here
  uses the digit series directly instead of the paper's reduction to D-node counts.
* T. Takagi, *A simple example of the continuous function without derivative*, Phys.-Math.
  Soc. Japan 1 (1903), pp. 176–177 (the digit-series definition cited by Monroe).
-/

namespace MetaMathlibExt

open Finset

private def bitCost (a : ℕ) (x : ℝ) : ℝ := if a = 0 then x else 1 - x

private def tent (r p : ℕ) : ℕ := min (r % (2 * 2 ^ p)) (2 * 2 ^ p - r % (2 * 2 ^ p))

private theorem takagiBit_nat (r p : ℕ) : takagiBit r p = r / 2 ^ p % 2 := by
  rw [takagiBit_eq, ite_eq_left (Int.natCast_nonneg p), Int.toNat_natCast, ← Nat.toNat_testBit]
  cases r.testBit p <;> rfl

-- The coefficient is the row sum of the disagreements; no pair of positions past the
-- binary point's finite expansion contributes.
private theorem ell_eq_sum_bitCost (r k i : ℕ) :
    (takagiEll r ((k : ℤ) - 1) (i + 1) : ℝ) =
      ∑ j ∈ range k, if j < i then
        bitCost (takagiBit r ((k : ℤ) - 1 - j)) (takagiBit r ((k : ℤ) - 1 - i)) else 0 := by
  let a (j : ℕ) := takagiBit r ((k : ℤ) - 1 - j)
  have hzero (j : ℕ) (hj : k ≤ j) : a j = 0 := takagiBit_neg _ _ (by omega)
  have hbit (j : ℕ) : a j ≤ 1 := by
    dsimp only [a]
    rw [takagiBit_eq]
    split_ifs <;> decide
  let f (j : ℕ) := if j < i then bitCost (a j) (a i) else 0
  change _ = ∑ j ∈ range k, f j
  have htrim : (∑ j ∈ range k, f j) = ∑ j ∈ range i, f j := by
    rcases le_total i k with hik | hki
    · symm
      exact sum_subset (range_mono hik) fun j _ hj ↦ ite_eq_right (fun h ↦ hj (mem_range.mpr h))
    · refine sum_subset (range_mono hki) fun j hj hj' ↦ ?_
      have hk : k ≤ j := Nat.le_of_not_gt fun h ↦ hj' (mem_range.mpr h)
      have hi := mem_range.mp hj
      simp [f, hi, bitCost, hzero j hk, hzero i (hk.trans hi.le)]
  rw [htrim, takagiEll_succ]
  change (↑(if a i = 0 then ∑ j ∈ range i, a j else i - ∑ j ∈ range i, a j) : ℝ) = _
  trans ∑ j ∈ range i, bitCost (a j) (a i)
  · have hsum : (∑ j ∈ range i, a j) ≤ i := calc
      _ ≤ ∑ _j ∈ range i, 1 := sum_le_sum fun j _ ↦ hbit j
      _ = i := by simp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hbit i) with h | h
    · rw [h, ite_eq_left rfl, Nat.cast_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hbit j) with hj | hj <;> simp [hj, bitCost]
    · rw [h, ite_eq_right one_ne_zero, Nat.cast_sub hsum, Nat.cast_sum]
      calc
        _ = ∑ j ∈ range i, (1 - (a j : ℝ)) := by simp [sum_sub_distrib]
        _ = _ := by
          refine sum_congr rfl fun j _ ↦ ?_
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hbit j) with hj | hj <;> simp [hj, bitCost]
  · exact sum_congr rfl fun j hj ↦ (ite_eq_left (mem_range.mp hj)).symm

-- Sum one column against its fixed earlier bit. The residue at the next modulus extends
-- the binary fraction by one place; the all-zero tail still contributes for an earlier one.
private theorem hasSum_bitCost (r a p : ℕ) :
    HasSum (fun t : ℕ ↦ bitCost a (takagiBit r ((p : ℤ) - 1 - t)) / 2 ^ (t + 1))
      (bitCost a ((r % 2 ^ p : ℕ) / (2 : ℝ) ^ p)) := by
  induction p with
  | zero =>
    have h (t : ℕ) : takagiBit r ((0 : ℤ) - 1 - t) = 0 := takagiBit_neg _ _ (by omega)
    simpa only [Nat.cast_zero, h, pow_zero, Nat.mod_one, zero_div, pow_succ', div_div]
      using hasSum_geometric_two' (bitCost a 0)
  | succ p ih =>
    have ht (t : ℕ) : (p : ℤ) - (↑(t + 1) : ℤ) = (p : ℤ) - 1 - t := by omega
    have hhead : ((p + 1 : ℕ) : ℤ) - 1 = p := by omega
    have hdecomp : ((r % 2 ^ (p + 1) : ℕ) : ℝ) / 2 ^ (p + 1) =
        (((r % 2 ^ p : ℕ) : ℝ) / 2 ^ p + (takagiBit r p : ℝ)) / 2 := by
      rw [pow_succ (2 : ℕ), Nat.mod_mul, takagiBit_nat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, pow_succ, add_div, add_div, div_div]
      congr 1
      field_simp
    rw [← hasSum_nat_add_iff' 1, hdecomp]
    simp only [sum_range_one, Nat.cast_zero, sub_zero, hhead, zero_add, pow_one, ht]
    convert ih.div_const 2 using 1
    · funext t
      rw [div_div, pow_succ]
    · by_cases h : a = 0 <;> simp [bitCost, h] <;> ring

private theorem bitCost_residue (r p : ℕ) :
    bitCost (takagiBit r p) ((r % 2 ^ p : ℕ) / (2 : ℝ) ^ p) = (tent r p : ℝ) / 2 ^ p := by
  have hlt := Nat.mod_lt r (Nat.two_pow_pos p)
  have hdecomp : r % (2 * 2 ^ p) = r % 2 ^ p + 2 ^ p * (r / 2 ^ p % 2) := by
    rw [mul_comm, Nat.mod_mul]
  rw [bitCost, takagiBit_nat, tent, hdecomp]
  rcases Nat.mod_two_eq_zero_or_one (r / 2 ^ p) with h | h
  · simp only [h, ite_true, mul_zero, add_zero, min_eq_left (by omega :
      r % 2 ^ p ≤ 2 * 2 ^ p - r % 2 ^ p)]
  · simp only [h, ite_eq_right one_ne_zero, mul_one,
      min_eq_right (by omega : 2 * 2 ^ p - (r % 2 ^ p + 2 ^ p) ≤ r % 2 ^ p + 2 ^ p)]
    rw [show 2 * 2 ^ p - (r % 2 ^ p + 2 ^ p) = 2 ^ p - r % 2 ^ p by omega,
      Nat.cast_sub hlt.le, Nat.cast_pow, Nat.cast_ofNat, sub_div, div_self (by positivity)]

private theorem hasSum_column (r k j : ℕ) (hj : j < k) :
    HasSum (fun i : ℕ ↦ (if j < i then
        bitCost (takagiBit r ((k : ℤ) - 1 - j)) (takagiBit r ((k : ℤ) - 1 - i)) else 0) /
          2 ^ (i + 1))
      ((tent r (k - 1 - j) : ℝ) / 2 ^ k) := by
  let p := k - 1 - j
  have hp : (k : ℤ) - 1 - j = (p : ℤ) := by dsimp [p]; omega
  have hs (i : ℕ) : (k : ℤ) - 1 - (↑(i + (j + 1)) : ℤ) = (p : ℤ) - 1 - i := by omega
  have hpow (i : ℕ) : i + (j + 1) + 1 = (i + 1) + (j + 1) := by omega
  have hprefix : (∑ i ∈ range (j + 1), (if j < i then
      bitCost (takagiBit r ((k : ℤ) - 1 - j)) (takagiBit r ((k : ℤ) - 1 - i)) else 0) /
        (2 : ℝ) ^ (i + 1)) = 0 := by
    refine sum_eq_zero fun i hi ↦ ?_
    rw [ite_eq_right (by have := mem_range.mp hi; omega), zero_div]
  rw [← hasSum_nat_add_iff' (j + 1), hprefix, sub_zero]
  have h := (hasSum_bitCost r (takagiBit r p) p).div_const ((2 : ℝ) ^ (j + 1))
  rw [bitCost_residue, div_div, ← pow_add, show p + (j + 1) = k by dsimp [p]; omega] at h
  have hjlt (i : ℕ) : j < i + (j + 1) := by omega
  simpa only [hjlt, ite_true, hp, hs, hpow, pow_add, ← div_div] using h

private theorem takagiNewdef_eq_tent_sum (r k : ℕ) :
    takagiNewdef r ((k : ℤ) - 1) = (∑ p ∈ range k, (tent r p : ℝ)) / 2 ^ k := by
  rw [takagiNewdef_eq]
  have h := hasSum_sum fun j (hj : j ∈ range k) ↦ hasSum_column r k j (mem_range.mp hj)
  simp_rw [ell_eq_sum_bitCost, div_eq_mul_inv, sum_mul]
  simp only [div_eq_mul_inv] at h
  rw [h.tsum_eq, sum_range_reflect (fun p ↦ (tent r p : ℝ) * (2 ^ k)⁻¹)]

-- At a multiple of the period the wave has a trough; halfway between two multiples it
-- has a peak. At all other mesh points its two unit steps have the same slope.
private theorem tent_secondDiff (r p : ℕ) (hr0 : 1 ≤ r) :
    2 * (tent r p : ℝ) - tent (r - 1) p - tent (r + 1) p =
      (if r % (2 * 2 ^ p) = 2 ^ p then 2 else 0) -
        (if r % (2 * 2 ^ p) = 0 then 2 else 0) := by
  let m : ℕ := 2 ^ p
  have hm : 0 < m := Nat.two_pow_pos p
  have hmod (n : ℕ) : n % (2 * m) + 1 =
      (n + 1) % (2 * m) + (if n % (2 * m) + 1 < 2 * m then 0 else 2 * m) := by
    simpa only [Nat.mod_eq_of_lt (show 1 < 2 * m by omega)] using
      (Nat.mod_add_mod_eq (a := n) (b := 1) (c := 2 * m))
  have hprev := hmod (r - 1)
  rw [Nat.sub_add_cancel hr0] at hprev
  have hnext := hmod r
  have hleft := Nat.mod_lt (r - 1) (show 0 < 2 * m by omega)
  have hcenter := Nat.mod_lt r (show 0 < 2 * m by omega)
  have hright := Nat.mod_lt (r + 1) (show 0 < 2 * m by omega)
  change 2 * (tent r p : ℝ) - tent (r - 1) p - tent (r + 1) p =
    (if r % (2 * m) = m then 2 else 0) - (if r % (2 * m) = 0 then 2 else 0)
  have hanat : 2 * tent r p + (if r % (2 * m) = 0 then 2 else 0) =
      tent (r - 1) p + tent (r + 1) p + (if r % (2 * m) = m then 2 else 0) := by
    simp only [tent, ← show m = 2 ^ p from rfl, min_def]
    split_ifs at hprev hnext ⊢ <;> omega
  by_cases hzero : r % (2 * m) = 0 <;> by_cases hmid : r % (2 * m) = m <;>
    simp only [hzero, hmid, ite_true, ite_false] at hanat ⊢ <;>
    have hreal := congrArg (fun n : ℕ ↦ (n : ℝ)) hanat <;>
    push_cast at hreal <;> linear_combination hreal

/-- **Midpoint recurrence for the Takagi function at dyadic rationals.** Let $k$ and $r$ be
natural numbers with $1 \le r < 2^k$. For a natural number $m$, write $\tau(m / 2^k)$ for the
Takagi value of the dyadic presentation $m / 2^k$, and let $\rho_1$ be the $2$-adic valuation of
$r$, the position (counted from $0$) of the lowest nonzero binary digit of $r$. Then
$\tau(r / 2^k) = (\tau((r - 1) / 2^k) + \tau((r + 1) / 2^k))/2 + (1 - \rho_1)/2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 24 (`jis-2024-24.2.7-thm-24`). -/
public theorem takagi_dyadic_eq_midpoint_add (k r : ℕ) (hr0 : 1 ≤ r) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
      (takagiNewdef (r - 1) ((k : ℤ) - 1) + takagiNewdef (r + 1) ((k : ℤ) - 1)) / 2 +
        (1 - (padicValNat 2 r : ℝ)) / 2 ^ k := by
  let v := padicValNat 2 r
  have hdvd (j : ℕ) : 2 ^ j ∣ r ↔ j ≤ v := by
    rw [show v = multiplicity 2 r from Nat.padicValNat_def]
    exact Nat.pow_dvd_iff_le_multiplicity (by decide) (by omega)
  have hv : v < k := by
    by_contra! h
    exact (not_lt_of_ge (Nat.le_of_dvd hr0 ((hdvd k).2 h))) hr
  let d (p : ℕ) : ℝ := 2 * (tent r p : ℝ) - tent (r - 1) p - tent (r + 1) p
  have hzero (p : ℕ) : r % (2 * 2 ^ p) = 0 ↔ p < v := by
    rw [← pow_succ', ← Nat.dvd_iff_mod_eq_zero, hdvd]
    omega
  have hmid (p : ℕ) : r % (2 * 2 ^ p) = 2 ^ p ↔ p = v := by
    have hpos := Nat.two_pow_pos p
    have hdecomp : r % (2 * 2 ^ p) = r % 2 ^ p + 2 ^ p * (r / 2 ^ p % 2) := by
      rw [mul_comm, Nat.mod_mul]
    have hsmall : r % 2 ^ p = 0 ↔ p ≤ v := (Nat.dvd_iff_mod_eq_zero).symm.trans (hdvd p)
    have hlt := Nat.mod_lt r hpos
    rcases Nat.mod_two_eq_zero_or_one (r / 2 ^ p) with h | h
    · simp only [h, mul_zero, add_zero] at hdecomp
      have hne : p ≠ v := by
        intro hp
        have h0 := hsmall.mpr hp.le
        exact (hzero p).mp (hdecomp.trans h0) |>.ne hp
      simp [hdecomp, hlt.ne, hne]
    · simp only [h, mul_one] at hdecomp
      have hnv : ¬p < v := fun hp ↦ by have := (hzero p).mpr hp; omega
      rw [hdecomp]
      omega
  have hd (p : ℕ) : d p = (if p = v then 2 else 0) - (if p < v then 2 else 0) := by
    simp only [d, tent_secondDiff r p hr0, hzero p, hmid p]
  have hlo : (∑ p ∈ range v, d p) = -2 * (v : ℝ) := by
    calc
      _ = ∑ _p ∈ range v, (-2 : ℝ) := by
        refine sum_congr rfl fun p hp ↦ ?_
        have h := mem_range.mp hp
        simp [hd, h, h.ne]
      _ = _ := by simp [mul_comm]
  have hhi : (∑ p ∈ range (k - (v + 1)), d (v + 1 + p)) = 0 := by
    refine sum_eq_zero fun p _ ↦ ?_
    rw [hd, ite_eq_right (by omega : v + 1 + p ≠ v),
      ite_eq_right (by omega : ¬v + 1 + p < v), sub_zero]
  have hsum : (∑ p ∈ range k, d p) = 2 * (1 - (v : ℝ)) := by
    rw [← Nat.add_sub_of_le (show v + 1 ≤ k by omega), sum_range_add, sum_range_succ,
      hlo, hhi, hd v]
    simp
    ring
  have hscaled :
      2 * (∑ p ∈ range k, (tent r p : ℝ)) - (∑ p ∈ range k, (tent (r - 1) p : ℝ)) -
        (∑ p ∈ range k, (tent (r + 1) p : ℝ)) = 2 * (1 - (v : ℝ)) := by
    simpa only [d, sum_sub_distrib, ← mul_sum] using hsum
  simp_rw [takagiNewdef_eq_tent_sum]
  field_simp
  dsimp only [v] at hscaled
  linear_combination hscaled

end MetaMathlibExt

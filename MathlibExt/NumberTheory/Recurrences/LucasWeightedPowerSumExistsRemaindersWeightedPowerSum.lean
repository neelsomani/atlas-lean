/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.LucasBinomialSum
public import MathlibExt.NumberTheory.Recurrences.LucasCompanionSquare
public import MathlibExt.NumberTheory.Recurrences.LucasRatioLowerBound
public import MathlibExt.NumberTheory.Recurrences.LucasRootPower
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula
import MathlibExt.NumberTheory.Recurrences.LucasWeightedPowerSumAlphaBounds

/-!
# Remainders for weighted Lucas power sums

For positive integers $x,n,p,q$ and an integer $k \ge 3$ satisfying
$\sum_{j=1}^k j U_j(x,y)^p = U_n(x,y)^q$, this module bounds the remainders in the
Binet expansion when $y \in \{1,-1\}$ and $D = x^2 - 4y > 0$.
When $y=-1$, it also bounds the explicit remainder for $U_n^q$ by comparing the weighted sum
with a geometric sum of powers of the dominant root. This uses the weak exponent comparison
$4/q \le p+3$, which includes $p=q=1$.

## References

* Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
  Equation $\sum_{j=1}^k j F_j^p = F_n^q$ to a Family of Lucas Sequences*, The Fibonacci Quarterly
  62 (2024), no. 3, pp. 241–257, Proposition 4.1 and Lemma 4.2. The estimates for the index and the
  weighted sum in Lemma 4.2 follow here from the dominant-root bounds of Lemma 2.2, via
  `lucasU_lucasV_alpha_bounds`.
* Krisztián Gueth, Florian Luca and László Szalay, *On a Diophantine equation involving powers of
  Fibonacci numbers*, Proceedings of the Japan Academy, Series A, Mathematical Sciences 96
  (2020), no. 4, pp. 33–37, Section 2 (the Fibonacci argument cited in Section 4 above).
-/

namespace MetaMathlibExt

private theorem ag_identity (x : ℝ) (k : ℕ) :
    (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * x ^ j) * (x - 1) ^ 2 =
      (k * x - (k + 1)) * x ^ (k + 1) + x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    push_cast
    simp only [pow_succ]
    ring

private theorem power_error (a b x s : ℝ) (t : ℕ)
    (hx : 0 < x) (hx2 : 2 < x ^ 2) (hs : 2 ≤ s) (hs2 : 5 ≤ s ^ 2)
    (ha : |a| ≤ 3 / 4 * x) (hb : b = x / s)
    (hab : |a - b| * x = 1 / s) (ht : 2 ≤ t) :
    |a ^ t - b ^ t| < x ^ (t - 2) / 2 := by
  have hspos : 0 < s := by linarith
  have hbabs : |b| = x / s := by rw [hb, abs_of_pos (div_pos hx hspos)]
  have hbase : |a ^ 2 - b ^ 2| < 1 / 2 := by
    have hsum : |a + b| ≤ 2 * (x / s) + |a - b| := by
      calc
        |a + b| = |(a - b) + (b + b)| := by congr 1; ring
        _ ≤ |a - b| + |b + b| := abs_add_le _ _
        _ = 2 * (x / s) + |a - b| := by
          rw [abs_of_pos (by rw [hb]; positivity : 0 < b + b), hb]
          ring
    have hprod : |a ^ 2 - b ^ 2| ≤ |a - b| * (2 * (x / s) + |a - b|) := by
      calc
        |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by rw [← abs_mul]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    have he : |a - b| = 1 / (s * x) := by
      apply (eq_div_iff (ne_of_gt (mul_pos hspos hx))).2
      calc
        |a - b| * (s * x) = s * (|a - b| * x) := by ring
        _ = 1 := by rw [hab]; field_simp
    rw [he] at hprod
    have hh : 1 / (s * x) * (2 * (x / s) + 1 / (s * x)) < 1 / 2 := by
      have heq : 1 / (s * x) * (2 * (x / s) + 1 / (s * x)) =
          (2 * x ^ 2 + 1) / (s ^ 2 * x ^ 2) := by field_simp
      rw [heq]
      apply (div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [mul_le_mul_of_nonneg_right hs2 (sq_nonneg x)]
    exact hprod.trans_lt hh
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' ht
  induction r with
  | zero => simpa using hbase
  | succ r ih =>
    have hr : (1 : ℝ) / s ^ (r + 3) ≤ 1 / 8 := by
      apply one_div_le_one_div_of_le (by norm_num)
      calc
        (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs _
        _ ≤ s ^ (r + 3) := pow_le_pow_right₀ (by linarith) (by omega)
    have he : |a - b| = 1 / (s * x) := by
      apply (eq_div_iff (ne_of_gt (mul_pos hspos hx))).2
      calc
        |a - b| * (s * x) = s * (|a - b| * x) := by ring
        _ = 1 := by rw [hab]; field_simp
    have hbterm : |b| ^ (r + 2) * |a - b| ≤ x ^ (r + 1) / 8 := by
      rw [hbabs, he, div_pow]
      have heq : x ^ (r + 2) / s ^ (r + 2) * (1 / (s * x)) =
          x ^ (r + 1) * (1 / s ^ (r + 3)) := by
        field_simp
        simp only [pow_succ]
        ring
      rw [heq]
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hr (pow_nonneg hx.le _)
    have haterm : |a| * |a ^ (r + 2) - b ^ (r + 2)| <
        3 / 8 * x ^ (r + 1) := by
      calc
        _ ≤ (3 / 4 * x) * |a ^ (r + 2) - b ^ (r + 2)| :=
          mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        _ < (3 / 4 * x) * (x ^ r / 2) :=
          mul_lt_mul_of_pos_left (by simpa using ih) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    calc
      |a ^ (r + 1 + 2) - b ^ (r + 1 + 2)| =
          |a * (a ^ (r + 2) - b ^ (r + 2)) + b ^ (r + 2) * (a - b)| := by
        congr 1
        rw [show r + 1 + 2 = (r + 2) + 1 by omega]
        simp only [pow_succ]
        ring
      _ ≤ |a * (a ^ (r + 2) - b ^ (r + 2))| + |b ^ (r + 2) * (a - b)| := abs_add_le _ _
      _ = |a| * |a ^ (r + 2) - b ^ (r + 2)| + |b| ^ (r + 2) * |a - b| := by
        rw [abs_mul, abs_mul, abs_pow]
      _ < 3 / 8 * x ^ (r + 1) + x ^ (r + 1) / 8 := add_lt_add_of_lt_of_le haterm hbterm
      _ = x ^ (r + 1 + 2 - 2) / 2 := by simp; ring

private theorem weighted_negative_root (β : ℝ) (k : ℕ) (hk : 3 ≤ k)
    (hlow : -2 / 3 ≤ β) (hneg : β ≤ 0) :
    |∑ j ∈ Finset.Icc 1 k, (j : ℝ) * β ^ j| ≤ 2 / 3 := by
  let S := ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * β ^ j
  have hid := ag_identity β k
  change S * (β - 1) ^ 2 = _ at hid
  let r := -β
  have hr0 : 0 ≤ r := neg_nonneg.mpr hneg
  have hr : r ≤ 2 / 3 := by dsimp [r]; linarith
  have hf (l : ℕ) (hl : 3 ≤ l) :
      (l * r + (l + 1)) * r ^ (l + 1) ≤ (3 * r + 4) * r ^ 4 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hl
    induction i with
    | zero => norm_num
    | succ i ih =>
      have hstep : ((i + 4 : ℕ) * r + (i + 4 + 1)) * r ≤
          (i + 3 : ℕ) * r + (i + 3 + 1) := by
        push_cast
        have hr2 : r ^ 2 ≤ 4 / 9 := by nlinarith
        have hh := mul_nonneg (by positivity : 0 ≤ (i : ℝ) + 4) (sub_nonneg.mpr hr2)
        nlinarith
      calc
        _ = (((i + 4 : ℕ) * r + (i + 4 + 1)) * r) * r ^ (i + 3 + 1) := by
          rw [show i + 1 + 3 + 1 = (i + 3 + 1) + 1 by omega, pow_succ]
          push_cast
          ring
        _ ≤ ((i + 3 : ℕ) * r + (i + 3 + 1)) * r ^ (i + 3 + 1) :=
          mul_le_mul_of_nonneg_right hstep (pow_nonneg hr0 _)
        _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_ofNat] using ih (by omega)
  have htail := hf k hk
  have hr3 : r ^ 3 ≤ (2 / 3 : ℝ) ^ 3 := pow_le_pow_left₀ hr0 hr _
  have hr4 : r ^ 4 ≤ 8 / 27 * r := by nlinarith [mul_le_mul_of_nonneg_right hr3 hr0]
  have hpoly : (3 * r + 4) * r ^ 4 + r ≤ 2 / 3 * (1 + r) ^ 2 := by
    have h₀ : (3 * r + 4) * r ^ 4 ≤ 6 * r ^ 4 := by
      nlinarith [pow_nonneg hr0 4]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 / 3 - r) (by linarith : 0 ≤ 3 / 2 - r)]
  have hab : |S| * (β - 1) ^ 2 ≤
      (k * r + (k + 1)) * r ^ (k + 1) + r := by
    calc
      _ = |S * (β - 1) ^ 2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg (β - 1))]
      _ = |(k * β - (k + 1)) * β ^ (k + 1) + β| := by rw [hid]
      _ ≤ |(k * β - (k + 1)) * β ^ (k + 1)| + |β| := abs_add_le _ _
      _ = _ := by
        rw [abs_mul, abs_pow, abs_of_nonpos hneg,
          abs_of_nonpos (by
            nlinarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hneg] :
            k * β - (k + 1) ≤ 0)]
        dsimp [r]
        ring
  have heq : (β - 1) ^ 2 = (1 + r) ^ 2 := by dsimp [r]; ring
  rw [heq] at hab
  nlinarith [sq_pos_of_pos (by positivity : 0 < 1 + r)]

private theorem weighted_small_root (β : ℝ) (k : ℕ) (hk : 3 ≤ k)
    (hβ : (0 ≤ β ∧ β < 1 ∧ β ≤ (1 - β) ^ 2) ∨ (-2 / 3 ≤ β ∧ β ≤ 0)) :
    |∑ j ∈ Finset.Icc 1 k, (j : ℝ) * β ^ j| < 1 := by
  let S := ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * β ^ j
  have hid := ag_identity β k
  change S * (β - 1) ^ 2 = _ at hid
  rcases hβ with ⟨hpos, hlt, hsq⟩ | ⟨hlow, hneg⟩
  · have hn : 0 ≤ S :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hpos _)
    rw [abs_of_nonneg hn]
    have htail : (k * β - (k + 1)) * β ^ (k + 1) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        nlinarith
      · exact pow_nonneg hpos _
    by_cases hzero : β = 0
    · subst β
      simp only [zero_sub, neg_sq, one_pow, mul_one, mul_zero,
        zero_pow (by omega : k + 1 ≠ 0), zero_add] at hid
      linarith
    · have htail' : (k * β - (k + 1)) * β ^ (k + 1) < 0 := by
        apply mul_neg_of_neg_of_pos
        · nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        · exact pow_pos (lt_of_le_of_ne hpos (Ne.symm hzero)) _
      have hdpos : 0 < (β - 1) ^ 2 := sq_pos_of_ne_zero (by linarith)
      nlinarith
  · exact (weighted_negative_root β k hk hlow hneg).trans_lt (by norm_num)

private theorem root_data (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) :
    let s : ℝ := Real.sqrt (P.p ^ 2 - 4 * P.q)
    let α : ℝ := (P.p + s) / 2
    let β : ℝ := (P.p - s) / 2
    2 < s ∧ 5 ≤ s ^ 2 ∧ 3 / 2 < α ∧ 2 < α ^ 2 ∧
    α + β = P.p ∧ α * β = P.q ∧ α - β = s ∧ |β| * α = 1 ∧
    ((0 ≤ β ∧ β < 1 ∧ β ≤ (1 - β) ^ 2) ∨ (-2 / 3 ≤ β ∧ β ≤ 0)) := by
  dsimp
  let s : ℝ := Real.sqrt (P.p ^ 2 - 4 * P.q)
  let α : ℝ := (P.p + s) / 2
  let β : ℝ := (P.p - s) / 2
  change 2 < s ∧ 5 ≤ s ^ 2 ∧ 3 / 2 < α ∧ 2 < α ^ 2 ∧
    α + β = P.p ∧ α * β = P.q ∧ α - β = s ∧ |β| * α = 1 ∧ _
  have hx1 : (1 : ℝ) ≤ P.p := by exact_mod_cast (show 1 ≤ P.p by omega)
  have hd5 : (5 : ℝ) ≤ P.p ^ 2 - 4 * P.q := by
    have hh : 5 ≤ P.p ^ 2 - 4 * P.q := by
      rcases hy with h | h
      · rw [h] at hD ⊢
        have hx3 : 3 ≤ P.p := by nlinarith
        nlinarith
      · rw [h]
        nlinarith
    exact_mod_cast hh
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = P.p ^ 2 - 4 * P.q := Real.sq_sqrt (by linarith)
  have hs : 2 < s := by nlinarith
  have hα : 3 / 2 < α := by dsimp [α]; linarith
  have hα0 : 0 < α := by linarith
  have hα2 : 2 < α ^ 2 := by nlinarith
  have hsum : α + β = P.p := by dsimp [α, β]; ring
  have hprod : α * β = P.q := by dsimp [α, β]; nlinarith
  have hdiff : α - β = s := by dsimp [α, β]; ring
  refine ⟨hs, by linarith, hα, hα2, hsum, hprod, hdiff, ?_, ?_⟩
  · rcases hy with h | h
    · have hq : (P.q : ℝ) = 1 := by exact_mod_cast h
      have hβ : 0 < β := by nlinarith
      rw [abs_of_pos hβ]
      nlinarith
    · have hq : (P.q : ℝ) = -1 := by exact_mod_cast h
      have hβ : β < 0 := by nlinarith
      rw [abs_of_neg hβ]
      nlinarith
  · rcases hy with h | h
    · have hq : (P.q : ℝ) = 1 := by exact_mod_cast h
      have hx3 : (3 : ℝ) ≤ P.p := by
        have hh : 3 ≤ P.p := by rw [h] at hD; nlinarith
        exact_mod_cast hh
      have hβ : 0 ≤ β := by nlinarith
      refine Or.inl ⟨hβ, by nlinarith, ?_⟩
      have hh : β ^ 2 - P.p * β + 1 = 0 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hx3) hβ]
    · have hq : (P.q : ℝ) = -1 := by exact_mod_cast h
      have hβ : β ≤ 0 := by nlinarith
      refine Or.inr ⟨?_, hβ⟩
      nlinarith

private theorem binet_error_bound (α β s u : ℝ) (m t : ℕ) (hm : 0 < m) (ht : 2 ≤ t)
    (hα : 3 / 2 < α) (hs : 2 < s) (hs2 : 5 ≤ s ^ 2) (hprod : |β| * α = 1)
    (hu : u = (α ^ m - β ^ m) / s) :
    |u ^ t - α ^ (m * t) / s ^ t| < α ^ (m * (t - 2)) / 2 := by
  have hα0 : 0 < α := by linarith
  have hα1 : 1 ≤ α := by linarith
  let x := α ^ m
  have hx : 0 < x := pow_pos hα0 _
  have hxα : α ≤ x := by
    simpa only [pow_one] using pow_le_pow_right₀ hα1 hm
  have hx2 : 2 < x ^ 2 := by nlinarith
  have hv : |β ^ m| * x = 1 := by
    dsimp [x]
    rw [abs_pow, ← mul_pow, hprod, one_pow]
  have hvsmall : |β ^ m| ≤ x / 2 := by nlinarith [abs_nonneg (β ^ m)]
  have huabs : |u| ≤ 3 / 4 * x := by
    rw [hu, abs_div, abs_of_pos (by linarith : 0 < s)]
    apply (div_le_iff₀ (by linarith : 0 < s)).2
    have hh : |α ^ m - β ^ m| ≤ x + |β ^ m| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_pos (pow_pos hα0 m), x] using
        abs_sub_le (α ^ m) 0 (β ^ m)
    have hh₂ := mul_nonneg (by positivity : 0 ≤ 3 / 4 * x) (by linarith : 0 ≤ s - 2)
    nlinarith
  have hab : |u - x / s| * x = 1 / s := by
    rw [hu]
    change |(x - β ^ m) / s - x / s| * x = 1 / s
    rw [← sub_div, sub_sub_cancel_left, abs_div, abs_neg, abs_of_pos (by linarith : 0 < s)]
    rw [div_mul_eq_mul_div, hv]
  have hh := power_error u (x / s) x s t hx hx2 hs.le hs2 huabs rfl hab ht
  simpa only [x, div_pow, ← pow_mul] using hh

private theorem real_root_pow (P : LucasSequenceParams) (β : ℝ)
    (hβ : β ^ 2 - P.p * β + P.q = 0) (n : ℕ) (hn : 0 < n) :
    β ^ n = β * lucasU P n - P.q * lucasU P (n - 1) := by
  have hc : (β : ℂ) ^ 2 - P.p * (β : ℂ) + P.q = 0 := by exact_mod_cast hβ
  have hh := lucasU_root_pow P hc hn
  exact_mod_cast hh

private theorem linear_solution_index (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) (hD : 0 < P.p ^ 2 - 4 * P.q)
    (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j = lucasU P n) : 3 ≤ n := by
  have hpos (m : ℕ) : 0 ≤ lucasU P m := by
    rcases root_data P hy hx hD with ⟨hs, hs2, hα, hα2, hsum, hprod, hdiff, hab, hβ⟩
    let s : ℝ := Real.sqrt (P.p ^ 2 - 4 * P.q)
    let α : ℝ := (P.p + s) / 2
    let β : ℝ := (P.p - s) / 2
    have hα0 : 0 < α := by dsimp [α, s]; linarith
    have hβabs : |β| ≤ α := by
      have hα1 : 1 ≤ α := by dsimp [α, s]; linarith
      change |β| * α = 1 at hab
      nlinarith [abs_nonneg β]
    have hh : β ^ m ≤ α ^ m := by
      exact (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hβabs _)
    have hbin := ((lucas_binet_formulas_of_field P α β hsum hprod).1
      (by change α - β = s at hdiff; linarith) m).1
    have hnon : (0 : ℝ) ≤ lucasU P m := by
      rw [hbin, hdiff]
      exact div_nonneg (sub_nonneg.mpr hh) (by linarith)
    exact_mod_cast hnon
  have hsum : 3 * lucasU P 3 ≤ lucasU P n := by
    rw [← hsol]
    exact Finset.single_le_sum (fun j _ => mul_nonneg (Int.natCast_nonneg _) (hpos j))
      (by simp; omega)
  have hu3 : lucasU P 3 = P.p ^ 2 - P.q := by simp [lucasU]; ring
  rw [hu3] at hsum
  by_contra h
  have hh : n = 1 ∨ n = 2 := by omega
  rcases hh with rfl | rfl <;> simp only [lucasU, mul_one, mul_zero, sub_zero] at hsum
  · rcases hy with hy | hy <;> rw [hy] at hsum hD <;> nlinarith
  · rcases hy with hy | hy <;> rw [hy] at hsum hD <;> nlinarith

private theorem linear_solution_cancels (P : LucasSequenceParams) (α β s : ℝ)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) (hD : 0 < P.p ^ 2 - 4 * P.q)
    (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j = lucasU P n)
    (hsum : α + β = P.p) (hprod : α * β = P.q) (hdiff : α - β = s)
    (hs : 2 < s)
    (hβ : (0 ≤ β ∧ β < 1 ∧ β ≤ (1 - β) ^ 2) ∨ (-2 / 3 ≤ β ∧ β ≤ 0)) :
    (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * α ^ j) - α ^ n = 0 := by
  let S := ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * β ^ j
  let z : ℤ := -P.q * ((∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P (j - 1)) - lucasU P (n - 1))
  have hroot : β ^ 2 - P.p * β + P.q = 0 := by rw [← hsum, ← hprod]; ring
  have he : S - β ^ n = (z : ℝ) := by
    dsimp [S, z]
    rw [real_root_pow P β hroot n hn]
    have hh : (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * β ^ j) =
        β * (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (lucasU P j : ℝ)) -
        P.q * (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (lucasU P (j - 1) : ℝ)) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [real_root_pow P β hroot j (Finset.mem_Icc.mp hj).1]
      ring
    rw [hh]
    have hsol' : (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (lucasU P j : ℝ)) = lucasU P n := by
      exact_mod_cast hsol
    rw [hsol']
    push_cast
    ring
  have hz : |(z : ℝ)| < 1 := by
    rw [← he]
    rcases hβ with ⟨hβ0, hβ1, hβsq⟩ | ⟨hβlow, hβ0⟩
    · have hS0 : 0 ≤ S :=
        Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hβ0 _)
      have hS1 : S < 1 := (le_abs_self S).trans_lt
        (weighted_small_root β k hk (Or.inl ⟨hβ0, hβ1, hβsq⟩))
      have hpow0 := pow_nonneg hβ0 n
      have hpow1 : β ^ n < 1 := pow_lt_one₀ hβ0 hβ1 (by omega)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · have hS := weighted_negative_root β k hk hβlow hβ0
      have hβabs : |β| ≤ 2 / 3 := by rw [abs_of_nonpos hβ0]; linarith
      have hn3 := linear_solution_index P hy hx hD n k hn hk hsol
      have hpow : |β ^ n| ≤ (2 / 3 : ℝ) ^ 3 := by
        rw [abs_pow]
        exact (pow_le_pow_left₀ (abs_nonneg _) hβabs _).trans
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn3)
      have htriangle : |S - β ^ n| ≤ |S| + |β ^ n| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le S 0 (β ^ n)
      exact htriangle.trans_lt (by dsimp [S] at *; norm_num at hpow ⊢; linarith)
  have hz0 : z = 0 := by
    have hh := abs_lt.mp hz
    have hlo : (-1 : ℤ) < z := by exact_mod_cast hh.1
    have hhi : z < (1 : ℤ) := by exact_mod_cast hh.2
    omega
  have hbin (m : ℕ) : α ^ m - β ^ m = s * (lucasU P m : ℝ) := by
    have hh := ((lucas_binet_formulas_of_field P α β hsum hprod).1 (by linarith) m).1
    rw [hdiff] at hh
    exact (div_eq_iff (by linarith : s ≠ 0)).1 hh.symm |>.trans (by ring)
  have hsol' : (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (lucasU P j : ℝ)) = lucasU P n := by
    exact_mod_cast hsol
  have hsum' : (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * α ^ j) - S = s * lucasU P n := by
    dsimp [S]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, hbin]
    rw [show (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (s * lucasU P j)) =
      s * (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * lucasU P j) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring]
    rw [hsol']
  rw [hz0, Int.cast_zero] at he
  linarith [hbin n]

private theorem weighted_error_bound (P : LucasSequenceParams) (α β s : ℝ) (k p : ℕ)
    (hk : 3 ≤ k) (hp : 2 ≤ p) (hα : 3 / 2 < α) (hs : 2 < s) (hs2 : 5 ≤ s ^ 2)
    (hab : |β| * α = 1)
    (hu : ∀ m : ℕ, (lucasU P m : ℝ) = (α ^ m - β ^ m) / s) :
    |∑ j ∈ Finset.Icc 1 k, (j : ℝ) * ((lucasU P j : ℝ) ^ p - α ^ (j * p) / s ^ p)| <
      (k : ℝ) ^ 2 * α ^ (k * (p - 2)) := by
  have hα0 : 0 < α := by linarith
  have hα1 : 1 ≤ α := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hB : 0 < α ^ (k * (p - 2)) := pow_pos hα0 _
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 k, |(j : ℝ) * ((lucasU P j : ℝ) ^ p - α ^ (j * p) / s ^ p)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ < ∑ _j ∈ Finset.Icc 1 k, (k : ℝ) * α ^ (k * (p - 2)) := by
      apply Finset.sum_lt_sum_of_nonempty (by exact ⟨1, by simp; omega⟩)
      intro j hj
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hjk := (Finset.mem_Icc.mp hj).2
      have he := binet_error_bound α β s (lucasU P j) j p hj1 hp hα hs hs2 hab (hu j)
      have hpow : α ^ (j * (p - 2)) ≤ α ^ (k * (p - 2)) :=
        pow_le_pow_right₀ hα1 (Nat.mul_le_mul_right _ hjk)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      calc
        _ < (j : ℝ) * (α ^ (j * (p - 2)) / 2) := mul_lt_mul_of_pos_left he hj0
        _ ≤ (k : ℝ) * (α ^ (k * (p - 2)) / 2) :=
          mul_le_mul (by exact_mod_cast hjk) (div_le_div_of_nonneg_right hpow (by norm_num))
            (by positivity) (Nat.cast_nonneg k)
        _ < _ := by nlinarith
    _ = _ := by simp [Finset.sum_const]; ring

private theorem power_remainder_bound (P : LucasSequenceParams) (α β s : ℝ) (n q : ℕ)
    (hn : 0 < n) (hq : 0 < q) (hα : 3 / 2 < α) (hs : 2 < s) (hs2 : 5 ≤ s ^ 2)
    (hab : |β| * α = 1) (hu : (lucasU P n : ℝ) = (α ^ n - β ^ n) / s) :
    |(lucasU P n : ℝ) ^ q - α ^ (n * q) / s ^ q| <
      α ^ ((n : ℝ) * ((q : ℝ) - 2)) := by
  have hα0 : 0 < α := by linarith
  have hs0 : 0 < s := by linarith
  by_cases hq1 : q = 1
  · subst q
    simp only [pow_one, Nat.mul_one, Nat.cast_one]
    rw [show (n : ℝ) * (1 - 2) = -(n : ℝ) by ring,
      Real.rpow_neg hα0.le, Real.rpow_natCast, hu, ← sub_div, sub_sub_cancel_left,
      abs_div, abs_neg, abs_of_pos hs0]
    have habn : |β ^ n| * α ^ n = 1 := by rw [abs_pow, ← mul_pow, hab, one_pow]
    apply (div_lt_iff₀ hs0).2
    have hx := pow_pos hα0 n
    apply (mul_lt_mul_iff_left₀ hx).1
    rw [habn]
    field_simp
    linarith
  · have hq2 : 2 ≤ q := by omega
    rw [show (n : ℝ) * ((q : ℝ) - 2) = (n * (q - 2) : ℕ) by
      rw [Nat.cast_mul, Nat.cast_sub hq2]; norm_num, Real.rpow_natCast]
    have hh := binet_error_bound α β s (lucasU P n) n q hn hq2 hα hs hs2 hab hu
    exact lt_trans hh (by linarith [pow_pos hα0 (n * (q - 2))])

private theorem exists_auxiliary_remainders (P : LucasSequenceParams) (α β s : ℝ)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) (hD : 0 < P.p ^ 2 - 4 * P.q)
    (n k p q : ℕ) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q)
    (hα : 3 / 2 < α) (hs : 2 < s) (hs2 : 5 ≤ s ^ 2)
    (hsum : α + β = P.p) (hprod : α * β = P.q) (hdiff : α - β = s)
    (hab : |β| * α = 1)
    (hβ : (0 ≤ β ∧ β < 1 ∧ β ≤ (1 - β) ^ 2) ∨ (-2 / 3 ≤ β ∧ β ≤ 0)) :
    ∃ R₁ R₂ : ℝ,
      |R₁| < (k : ℝ) ^ 2 * α ^ ((k : ℝ) * ((p : ℝ) - 2)) ∧
      |R₂| < α ^ ((n : ℝ) * ((q : ℝ) - 2)) ∧
      R₂ - R₁ = (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * α ^ (j * p)) / s ^ p -
        α ^ (q * n) / s ^ q := by
  have hα0 : 0 < α := by linarith
  have hs0 : 0 < s := by linarith
  have hu (m : ℕ) : (lucasU P m : ℝ) = (α ^ m - β ^ m) / s := by
    have hh := ((lucas_binet_formulas_of_field P α β hsum hprod).1 (by linarith) m).1
    simpa only [hdiff] using hh
  let E₁ := ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * ((lucasU P j : ℝ) ^ p - α ^ (j * p) / s ^ p)
  let E₂ := (lucasU P n : ℝ) ^ q - α ^ (n * q) / s ^ q
  have he : E₂ - E₁ = (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * α ^ (j * p)) / s ^ p -
      α ^ (q * n) / s ^ q := by
    have hsol' : (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (lucasU P j : ℝ) ^ p) = (lucasU P n : ℝ) ^ q := by
      exact_mod_cast hsol
    dsimp [E₁, E₂]
    simp_rw [mul_sub, Finset.sum_sub_distrib, div_eq_mul_inv, ← mul_assoc]
    rw [← Finset.sum_mul]
    rw [hsol', Nat.mul_comm n q]
    ring
  have hB₁ : 0 < (k : ℝ) ^ 2 * α ^ ((k : ℝ) * ((p : ℝ) - 2)) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    exact mul_pos (sq_pos_of_pos hk0) (Real.rpow_pos_of_pos hα0 _)
  by_cases hp1 : p = 1
  · subst p
    by_cases hq1 : q = 1
    · subst q
      have hlinear : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j = lucasU P n := by
        simpa only [pow_one] using hsol
      have hc := linear_solution_cancels P α β s hy hx hD n k hn hk hlinear hsum hprod hdiff hs hβ
      refine ⟨0, 0, by simpa using hB₁,
        by simpa using Real.rpow_pos_of_pos hα0 ((n : ℝ) * ((1 : ℝ) - 2)), ?_⟩
      simp only [pow_one, Nat.mul_one, Nat.one_mul, zero_sub]
      rw [← sub_div, hc, zero_div]
      simp
    · have hq2 : 2 ≤ q := by omega
      have hB₂ : 1 ≤ α ^ ((n : ℝ) * ((q : ℝ) - 2)) := by
        apply Real.one_le_rpow (by linarith)
        have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
      have he₂ : |E₂| < α ^ ((n : ℝ) * ((q : ℝ) - 2)) / 2 := by
        have hh := binet_error_bound α β s (lucasU P n) n q hn hq2 hα hs hs2 hab (hu n)
        simpa only [E₂, ← Real.rpow_natCast α (n * (q - 2)), Nat.cast_mul,
          Nat.cast_sub hq2, Nat.cast_ofNat] using hh
      have he₁ : |E₁| < 1 / 2 := by
        have heq : E₁ = -(∑ j ∈ Finset.Icc 1 k, (j : ℝ) * β ^ j) / s := by
          dsimp [E₁]
          simp only [pow_one, Nat.mul_one]
          simp_rw [hu, ← sub_div, sub_sub_cancel_left, div_eq_mul_inv, ← mul_assoc, mul_neg]
          rw [← Finset.sum_mul, ← Finset.sum_neg_distrib]
        rw [heq, abs_div, abs_neg, abs_of_pos hs0]
        apply (div_lt_iff₀ hs0).2
        have hh := weighted_small_root β k hk hβ
        linarith
      refine ⟨0, E₂ - E₁, by simpa using hB₁, ?_, by simpa using he⟩
      calc
        |E₂ - E₁| ≤ |E₂| + |E₁| := by
          simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le E₂ 0 E₁
        _ < α ^ ((n : ℝ) * ((q : ℝ) - 2)) / 2 + 1 / 2 := add_lt_add he₂ he₁
        _ ≤ _ := by linarith
  · have hp2 : 2 ≤ p := by omega
    refine ⟨E₁, E₂, ?_, power_remainder_bound P α β s n q hn hq hα hs hs2 hab (hu n), he⟩
    have hh := weighted_error_bound P α β s k p hk hp2 hα hs hs2 hab hu
    simpa only [E₁, ← Real.rpow_natCast α (k * (p - 2)), Nat.cast_mul,
      Nat.cast_sub hp2, Nat.cast_ofNat] using hh

private theorem equation_of_diff (R₁ R₂ S A B C E α : ℝ) (k p q n : ℕ)
    (hdiff : R₂ - R₁ = S / C - α ^ (q * n) / B)
    (hag : S * E = (k * α ^ p - (k + 1)) * α ^ (p * (k + 1)) + α ^ p)
    (hsplit : A = B / C) (hEne : E ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) :
    A * (k * α ^ p - (k + 1)) / E * α ^ (p * (k + 1)) - α ^ (q * n) =
      B * R₂ - B * R₁ - A * α ^ p / E := by
  have hb : B * (R₂ - R₁) = A * S - α ^ (q * n) := by
    rw [hdiff, hsplit]
    field_simp
  have hS : S = ((k * α ^ p - (k + 1)) * α ^ (p * (k + 1)) + α ^ p) / E :=
    (eq_div_iff hEne).2 hag
  calc
    _ = A * S - A * α ^ p / E - α ^ (q * n) := by rw [hS]; ring
    _ = _ := by nlinarith only [hb]

@[expose] public section

/-- **Remainder form of the weighted power-sum equation for Lucas sequences.** Let $x$ be a
positive integer, let $y \in \{1, -1\}$, and let $(U_n)$ be the Lucas sequence with parameters
$(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$. Suppose
$D = x^2 - 4y > 0$ and put $\alpha = (x + \sqrt{D})/2$. Let $n, p, q$ be positive integers and
$k \geq 3$ an integer with
$$
\sum_{j=1}^{k} j \, U_j^p = U_n^q.
$$
Then there are real numbers $R_1, R_2$ with $|R_1| < k^2 \alpha^{k(p-2)}$,
$|R_2| < \alpha^{n(q-2)}$ and
$$
\frac{D^{(q-p)/2} (k\alpha^p - (k+1))}{(\alpha^p - 1)^2} \alpha^{p(k+1)} - \alpha^{qn} =
D^{q/2} R_2 - D^{q/2} R_1 - \frac{D^{(q-p)/2} \alpha^p}{(\alpha^p - 1)^2}.
$$

The remainders $R_1, R_2$ are only asserted to exist; the source defines them explicitly in its
proof.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Proposition 4.1 (`fq-2024-earplynch07182024-prop-4.1`). -/
public theorem exists_remainders_weighted_power_sum (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) {n k p q : ℕ}
    (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < (k : ℝ) ^ 2 * α ^ ((k : ℝ) * ((p : ℝ) - 2)) ∧
      |R₂| < α ^ ((n : ℝ) * ((q : ℝ) - 2)) ∧
      D ^ (((q : ℝ) - p) / 2) * (k * α ^ p - (k + 1)) / (α ^ p - 1) ^ 2 * α ^ (p * (k + 1)) -
          α ^ (q * n) =
        D ^ ((q : ℝ) / 2) * R₂ - D ^ ((q : ℝ) / 2) * R₁ -
          D ^ (((q : ℝ) - p) / 2) * α ^ p / (α ^ p - 1) ^ 2 := by
  let D : ℝ := P.p ^ 2 - 4 * P.q
  let s := Real.sqrt D
  let α : ℝ := (P.p + s) / 2
  let β : ℝ := (P.p - s) / 2
  change ∃ R₁ R₂ : ℝ, |R₁| < (k : ℝ) ^ 2 * α ^ ((k : ℝ) * ((p : ℝ) - 2)) ∧
    |R₂| < α ^ ((n : ℝ) * ((q : ℝ) - 2)) ∧
    D ^ (((q : ℝ) - p) / 2) * (k * α ^ p - (k + 1)) / (α ^ p - 1) ^ 2 * α ^ (p * (k + 1)) -
      α ^ (q * n) = D ^ ((q : ℝ) / 2) * R₂ - D ^ ((q : ℝ) / 2) * R₁ -
      D ^ (((q : ℝ) - p) / 2) * α ^ p / (α ^ p - 1) ^ 2
  have hD0 : 0 < D := by dsimp [D]; exact_mod_cast hD
  have hr := root_data P hy hx hD
  change 2 < s ∧ 5 ≤ s ^ 2 ∧ 3 / 2 < α ∧ 2 < α ^ 2 ∧ α + β = P.p ∧
    α * β = P.q ∧ α - β = s ∧ |β| * α = 1 ∧ _ at hr
  rcases hr with ⟨hs, hs2, hα, hα2, hsum, hprod, hdiff, hab, hβ⟩
  obtain ⟨R₁, R₂, hR₁, hR₂, hd⟩ := exists_auxiliary_remainders P α β s hy hx hD n k p q
    hn hp hq hk hsol hα hs hs2 hsum hprod hdiff hab hβ
  refine ⟨R₁, R₂, hR₁, hR₂, ?_⟩
  have hsp (t : ℕ) : s ^ t = D ^ ((t : ℝ) / 2) := by
    rw [Real.rpow_div_two_eq_sqrt (t : ℝ) hD0.le, Real.rpow_natCast]
  have hsplit : D ^ (((q : ℝ) - p) / 2) = s ^ q / s ^ p := by
    rw [show ((q : ℝ) - p) / 2 = (q : ℝ) / 2 - (p : ℝ) / 2 by ring,
      Real.rpow_sub hD0, hsp, hsp]
  have hα0 : 0 < α := by linarith
  have hαp : 1 < α ^ p := by
    have hh : α ^ 1 ≤ α ^ p := pow_le_pow_right₀ (by linarith) hp
    simp only [pow_one] at hh
    linarith
  have hE : (α ^ p - 1) ^ 2 ≠ 0 := pow_ne_zero _ (by linarith)
  have hag : (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * α ^ (j * p)) * (α ^ p - 1) ^ 2 =
      (k * α ^ p - (k + 1)) * α ^ (p * (k + 1)) + α ^ p := by
    have hh := ag_identity (α ^ p) k
    simpa only [← pow_mul, Nat.mul_comm p] using hh
  have hh := equation_of_diff R₁ R₂ _ _ _ _ _ α k p q n hd hag hsplit hE
    (pow_ne_zero _ (by linarith : s ≠ 0)) (pow_ne_zero _ (by linarith : s ≠ 0))
  simpa only [hsp] using hh

/-- **Remainder bound for weighted Lucas power sums when $y = -1$.** Let $x$ be a positive
integer, let $(U_m)$ be the Lucas sequence with parameters $(x, -1)$, given by $U_0 = 0$,
$U_1 = 1$ and $U_{m+2} = x U_{m+1} + U_m$, and let $D = x^2 + 4$ and $\alpha = (x + \sqrt{D})/2$.
If positive integers $n$, $p$, $q$ and an integer $k \ge 3$ satisfy
$\sum_{j=1}^k j U_j^p = U_n^q$, then the remainder $R_2 = U_n^q - \alpha^{nq}/D^{q/2}$ satisfies
$D^{q/2} |R_2| < k (D + 1/x)^{q+1} \alpha^{kp - 2k/q + 1}$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 4.2 (`fq-2024-earplynch07182024-lem-4.2`). -/
public theorem remainder_bound_of_neg (P : LucasSequenceParams) (hyP : P.q = -1)
    (hx : 0 < P.p) {n k p q : ℕ} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    D ^ ((q : ℝ) / 2) * |(lucasU P n : ℝ) ^ q - α ^ (n * q) / D ^ ((q : ℝ) / 2)| <
      k * (D + 1 / P.p) ^ (q + 1) * α ^ ((k : ℝ) * p - 2 * k / q + 1) := by
  let x : ℝ := P.p
  let D : ℝ := P.p ^ 2 - 4 * P.q
  let s := Real.sqrt D
  let α : ℝ := (x + s) / 2
  let β : ℝ := (x - s) / 2
  let U (j : ℕ) : ℝ := lucasU P j
  change D ^ ((q : ℝ) / 2) * |U n ^ q - α ^ (n * q) / D ^ ((q : ℝ) / 2)| <
    k * (D + 1 / x) ^ (q + 1) * α ^ ((k : ℝ) * p - 2 * k / q + 1)
  have hx' : 1 ≤ P.p := by omega
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast hx'
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hD : 0 < P.p ^ 2 - 4 * P.q := by rw [hyP]; nlinarith [sq_nonneg P.p]
  have hD0 : 0 < D := by dsimp only [D]; exact_mod_cast hD
  obtain ⟨hs, hs2, hα, _, hsum, hprod, hdiff, hab, _⟩ := root_data P (Or.inr hyP) hx hD
  change α + β = x at hsum
  change α * β = (P.q : ℝ) at hprod
  change α - β = s at hdiff
  change |β| * α = 1 at hab
  have hα1 : 1 < α := by change 3 / 2 < α at hα; linarith
  have hα0 : 0 < α := zero_lt_one.trans hα1
  change 2 < s at hs
  have hs0 : 0 < s := by linarith
  have hBinet : U n = (α ^ n - β ^ n) / s := by
    have hne : α ≠ β := sub_ne_zero.mp (hdiff.symm ▸ hs0.ne')
    simpa only [hdiff] using ((lucas_binet_formulas_of_field P α β hsum hprod).1 hne n).1
  have hrem := power_remainder_bound P α β s n q hn hq hα hs hs2 hab hBinet
  rw [Real.rpow_div_two_eq_sqrt (q : ℝ) hD0.le, Real.rpow_natCast]
  change s ^ q * |U n ^ q - α ^ (n * q) / s ^ q| < _
  have hterms (j : ℕ) (hj : 2 ≤ j) : x * α ^ (j - 2) ≤ U j ∧ U j ≤ α ^ (j - 1) := by
    have hy : |P.q + 1| ≤ P.p := by rw [hyP, neg_add_cancel, abs_zero]; exact hx.le
    have hb := lucasU_lucasV_alpha_bounds P hx' hy hD hj
    exact ⟨hb.1, hb.2.1 (by rw [hyP]; decide)⟩
  have hUone : U 1 = 1 := by
    have h : lucasU P 1 = 1 := by simpa using lucasU_eq_sum_choose P (r := 1) (by decide)
    dsimp only [U]
    exact_mod_cast h
  have hU (j : ℕ) (hj : 1 ≤ j) : 1 ≤ U j ∧ U j ≤ α ^ (j - 1) := by
    by_cases h : j = 1
    · subst j
      simp only [hUone, Nat.sub_self, pow_zero, le_refl, and_self]
    · obtain ⟨hl, hu⟩ := hterms j (by omega)
      exact ⟨(one_le_mul_of_one_le_of_one_le hx1 (one_le_pow₀ hα1.le)).trans hl, hu⟩
  have hsol' : ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * U j ^ p = U n ^ q := by
    dsimp only [U]
    exact_mod_cast hsol
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlast : α ^ (k - 2) < U n ^ q := calc
    _ ≤ x * α ^ (k - 2) := le_mul_of_one_le_left (by positivity) hx1
    _ ≤ U k := (hterms k (by omega)).1
    _ ≤ U k ^ p := by simpa only [pow_one] using pow_le_pow_right₀ (hU k (by omega)).1 hp
    _ < (k : ℝ) * U k ^ p := lt_mul_of_one_lt_left (by positivity [(hU k (by omega)).1]) hk1
    _ ≤ U n ^ q := by
      rw [← hsol']
      refine Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) * U j ^ p)
        (fun j hj => mul_nonneg (Nat.cast_nonneg _) ?_)
        (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      exact pow_nonneg (zero_le_one.trans (hU j (Finset.mem_Icc.mp hj).1).1) _
  have hn2 : 2 ≤ n := by
    by_contra! hn2
    have h : n = 1 := by omega
    rw [h, hUone, one_pow] at hlast
    exact (not_lt_of_ge (one_le_pow₀ hα1.le)) hlast
  have hindex : k - 2 < (n - 1) * q := by
    apply (pow_lt_pow_iff_right₀ hα1).mp
    rw [pow_mul]
    exact hlast.trans_le (pow_le_pow_left₀ (by positivity [(hU n (by omega)).1]) (hterms n hn2).2 q)
  -- Dominate each weight by k and sum the resulting geometric progression.
  let a := α ^ p
  have ha : 3 / 2 < a := hα.trans_le (by simpa only [pow_one] using pow_le_pow_right₀ hα1.le hp)
  have ha0 : 0 < a := by linarith
  have hgeom : (∑ j ∈ Finset.Icc 1 k, a ^ (j - 1)) < 3 * a ^ (k - 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    simp only [Nat.add_sub_cancel_left]
    apply (mul_lt_mul_iff_of_pos_right (show 0 < a - 1 by linarith)).mp
    have hapow : a ^ k = a ^ (k - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [geom_sum_mul, hapow]
    nlinarith only [mul_lt_mul_of_pos_left (show a < 3 * (a - 1) by linarith)
      (pow_pos ha0 (k - 1))]
  have hweighted : U n ^ q < 3 * k * α ^ ((k - 1) * p) := calc
    _ = ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * U j ^ p := hsol'.symm
    _ ≤ ∑ j ∈ Finset.Icc 1 k, (k : ℝ) * a ^ (j - 1) := by
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
      obtain ⟨hl, hu⟩ := hU j hj1
      have hpow : U j ^ p ≤ a ^ (j - 1) := by
        simpa only [a, ← pow_mul, Nat.mul_comm p] using pow_le_pow_left₀ (zero_le_one.trans hl) hu p
      exact mul_le_mul (by exact_mod_cast hjk) hpow (by positivity [hl]) (Nat.cast_nonneg k)
    _ = k * ∑ j ∈ Finset.Icc 1 k, a ^ (j - 1) := (Finset.mul_sum _ _ _).symm
    _ < k * (3 * a ^ (k - 1)) := mul_lt_mul_of_pos_left hgeom (zero_lt_one.trans hk1)
    _ = 3 * k * α ^ ((k - 1) * p) := by
      dsimp only [a]
      rw [← pow_mul, Nat.mul_comm p]
      ring
  have hgrowth : x ^ q * α ^ ((n - 2) * q) < 3 * k * α ^ ((k - 1) * p) := by
    rw [pow_mul, ← mul_pow]
    exact (pow_le_pow_left₀ (by positivity) (hterms n hn2).1 q).trans_lt hweighted
  -- Use α² - β² = sx and sβ² < 1 to bound the coefficient.
  have hsquare : s ^ 2 = D := Real.sq_sqrt hD0.le
  have hbase : s * α ^ 2 / x < D + 1 / x := by
    have hβ : |β| < 1 := by
      apply (mul_lt_mul_iff_of_pos_right hα0).mp
      simpa only [hab, one_mul] using hα1
    have hroot : α ^ 2 = x * α + 1 := by
      have hneg : (P.q : ℝ) = -1 := by exact_mod_cast hyP
      rw [hneg] at hprod
      rw [← hsum]
      nlinarith only [hprod]
    have hslt : s < α ^ 2 := by
      rw [← hdiff, hroot]
      linarith only [neg_le_abs β, hβ, mul_le_mul_of_nonneg_right hx1 hα0.le]
    have habsq : β ^ 2 * α ^ 2 = 1 := by
      have h : (|β| * α) ^ 2 = (1 : ℝ) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hab
      simpa only [mul_pow, sq_abs, one_pow] using h
    have hβterm : s * β ^ 2 < 1 := calc
      _ < α ^ 2 * β ^ 2 := mul_lt_mul_of_pos_right hslt (sq_pos_of_ne_zero (by
        intro h; simp [h] at hab))
      _ = 1 := (mul_comm _ _).trans habsq
    apply (div_lt_iff₀ hx0).mpr
    calc
      s * α ^ 2 = (s ^ 2) * x + s * β ^ 2 := by rw [← hsum, ← hdiff]; ring
      _ < D * x + 1 := by linarith only [congrArg (· * x) hsquare, hβterm]
      _ = (D + 1 / x) * x := by rw [add_mul, one_div, inv_mul_cancel₀ hx0.ne']
  have hthree : 3 ≤ D + 1 / x := by
    have hs2' : 5 ≤ s ^ 2 := hs2
    have hinv : 0 ≤ 1 / x := by positivity
    linarith only [hsquare, hs2', hinv]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hcut : (k : ℝ) - 2 < ((n : ℝ) - 1) * q := by
    have h : (((k - 2 : ℕ) : ℝ)) < (((n - 1) * q : ℕ) : ℝ) := by exact_mod_cast hindex
    simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ k),
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_ofNat, Nat.cast_one] using h
  have hexp : (((k - 1) * p : ℕ) : ℝ) + (-2 * (n : ℝ)) ≤ (k : ℝ) * p - 2 * k / q + 1 := by
    have hdiv := (div_lt_iff₀ hq0).mpr hcut
    rw [sub_div] at hdiv
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have h2 : 2 / (q : ℝ) ≤ 2 := (div_le_iff₀ hq0).mpr (by linarith only [hq1])
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    rw [mul_div_assoc]
    linarith only [hdiv, hp1, h2]
  calc
    _ < s ^ q * α ^ ((n : ℝ) * ((q : ℝ) - 2)) := mul_lt_mul_of_pos_left hrem (pow_pos hs0 q)
    _ = (s * α ^ 2 / x) ^ q * (x ^ q * α ^ ((n - 2) * q)) * α ^ (-2 * (n : ℝ)) := by
      have he : (n : ℝ) * ((q : ℝ) - 2) = ((2 * q : ℕ) : ℝ) +
          ((((n - 2) * q : ℕ) : ℝ) + (-2 * (n : ℝ))) := by
        push_cast [Nat.cast_sub hn2]
        ring
      rw [he, Real.rpow_add hα0, Real.rpow_add hα0, Real.rpow_natCast, Real.rpow_natCast,
        div_pow (s * α ^ 2) x q, mul_pow s (α ^ 2) q, ← pow_mul α 2 q]
      field_simp
    _ ≤ (D + 1 / x) ^ q * (3 * k * α ^ ((k - 1) * p)) * α ^ (-2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (pow_le_pow_left₀ (by positivity) hbase.le _) hgrowth.le
          (by positivity) (by positivity)) (Real.rpow_nonneg hα0.le _)
    _ = k * (D + 1 / x) ^ q * 3 * α ^ ((((k - 1) * p : ℕ) : ℝ) + (-2 * (n : ℝ))) := by
      rw [Real.rpow_add hα0, Real.rpow_natCast]
      ring
    _ ≤ k * (D + 1 / x) ^ (q + 1) * α ^ ((k : ℝ) * p - 2 * k / q + 1) := by
      rw [pow_succ, ← mul_assoc (k : ℝ)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hthree (by positivity))
        (Real.rpow_le_rpow_of_exponent_le hα1.le hexp) (by positivity) (by positivity)

end
end MetaMathlibExt

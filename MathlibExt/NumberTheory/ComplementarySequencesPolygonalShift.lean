/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ComplementarySequences
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.ComplementarySequencesInterleaveNear
import MathlibExt.NumberTheory.PolygonalNumber

/-!
# Shifted formula for non-polygonal numbers

For $k \ge 3$, $n \ge 1$, and a real shift $-1 \le r \le k - 4$, the floor of
$\sqrt{(2n+r)/(k-2)}$ locates the gap containing the $n$-th positive integer outside the
$k$-gonal numbers $(k-2)j(j-1)/2+j$ for $j \ge 1$. A strict cutoff test distinguishes the two
possible offsets from $n$.

## References

* Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95,
  pp. 1–26, Section 2.2.1, Theorem 5, Equation (4) (p. 9). The proof here uses the binomial
  cutoffs and Wu's Corollary 1 (p. 7), via `nthNonValue_eq_interleave_of_sub_lt` in
  `MathlibExt.NumberTheory.ComplementarySequencesInterleaveNear`.
* J. Lambek and L. Moser, *Inverse and Complementary Sequences of Natural Numbers*, American
  Mathematical Monthly 61 (1954), no. 7, pp. 454–458, for the counting method in Wu's Section 2.1.
-/

namespace MetaMathlibExt

/-- **Shifted formula for the non-polygonal numbers.** Let $k \ge 3$, let $r$ be a real number
with $-1 \le r \le k - 4$, and for $j \ge 1$ let $T(k, j) = (k - 2) j (j - 1)/2 + j$ be the
$k$-gonal numbers. For every integer $n \ge 1$, put $s = \lfloor \sqrt{(2n + r)/(k - 2)} \rfloor$.
Then the $n$-th positive integer that is not of the form $T(k, j)$ with $j \ge 1$ equals
$n + s + 1$ if $(k - 2) s (s + 1) < 2n$, and $n + s$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 5, Equation (4). -/
public theorem nthNonValue_polygonal_shift (k : ℕ) (hk : 3 ≤ k) (r : ℝ) (hr : -1 ≤ r)
    (hr' : r ≤ (k : ℝ) - 4) (n : ℕ) (hn : 1 ≤ n) :
    let s := ⌊Real.sqrt ((2 * n + r) / ((k : ℝ) - 2))⌋₊
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      if (k - 2) * s * (s + 1) < 2 * n then n + s + 1 else n + s := by
  let a := k - 2
  let g (j : ℕ) := a * j.choose 2
  let f := Nat.polygonalNumber k
  let x (m : ℕ) : ℝ := (2 * m + r) / a
  let s (m : ℕ) := ⌊Real.sqrt (x m)⌋₊
  let h (m : ℕ) := if g (s m + 1) < m then s m + 1 else s m
  have ha : 1 ≤ a := by omega
  have haPos : (0 : ℝ) < a := by exact_mod_cast ha
  have haCast : (a : ℝ) = (k : ℝ) - 2 := by
    simp only [a, Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_ofNat]
  have hrHi : r ≤ (a : ℝ) - 2 := by rw [haCast]; linarith only [hr']
  have hf (j : ℕ) : f j = g j + j := Nat.polygonalNumber_eq k j
  have hseq : (fun j : ℕ => (k - 2) * j * (j - 1) / 2 + j) = f := by
    funext j
    rw [hf]
    change a * j * (j - 1) / 2 + j = a * j.choose 2 + j
    rw [Nat.choose_two_right, mul_assoc a,
      Nat.mul_div_assoc _ (even_iff_two_dvd.mp (Nat.even_mul_pred_self j))]
  have hbracket (m : ℕ) (hm : 1 ≤ m) : 1 ≤ h m ∧ g (h m) < m ∧ m ≤ g (h m + 1) := by
    let t := s m
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hx : 0 ≤ x m := div_nonneg (by linarith only [hmR, hr]) haPos.le
    have hsLo : (t : ℝ) ≤ Real.sqrt (x m) := Nat.floor_le (Real.sqrt_nonneg _)
    have hsHi : Real.sqrt (x m) < (t : ℝ) + 1 := Nat.lt_floor_add_one _
    have hsqLo : (t : ℝ) ^ 2 * a ≤ 2 * m + r :=
      (le_div_iff₀ haPos).mp ((Real.le_sqrt (Nat.cast_nonneg t) hx).mp hsLo)
    have hsqHi : (2 * m + r : ℝ) < ((t : ℝ) + 1) ^ 2 * a :=
      (div_lt_iff₀ haPos).mp (Real.lt_sq_of_sqrt_lt hsHi)
    have hlo : g t < m := by
      by_cases ht : t = 0
      · simpa [ht, g] using (show 0 < m from hm)
      · have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
        exact_mod_cast (show ((a * t.choose 2 : ℕ) : ℝ) < m by
          rw [Nat.cast_mul, Nat.cast_choose_two ℝ]
          nlinarith only [hsqLo, hrHi, mul_nonneg haPos.le (sub_nonneg.mpr htR)])
    have hhi : m ≤ g (t + 1 + 1) := by
      -- The upper square bound puts 2m less than one above the doubled cutoff.
      have hprod : (0 : ℝ) ≤ a * ((t : ℝ) + 1) := by positivity
      have hdbl : 2 * m < 2 * g (t + 1 + 1) + 1 := by
        exact_mod_cast (show (2 * m : ℝ) < 2 * (g (t + 1 + 1) : ℝ) + 1 by
          simp only [g, Nat.cast_mul, Nat.cast_choose_two ℝ, Nat.cast_add, Nat.cast_one]
          nlinarith only [hsqHi, hr, hprod])
      omega
    simp only [h, show s m = t from rfl]
    split_ifs with hlt
    · exact ⟨Nat.succ_pos t, hlt, hhi⟩
    · have ht : t ≠ 0 := by
        intro he
        exact hlt (by simpa [he, g] using (show 0 < m from hm))
      exact ⟨Nat.pos_of_ne_zero ht, hlo, Nat.le_of_not_gt hlt⟩
  have hstep (j : ℕ) : g (j + 1) = g j + a * j := by
    simp only [g, Nat.choose_succ_succ j 1, Nat.choose_one_right, Nat.mul_add, add_comm]
  have hmul (j : ℕ) : j ≤ a * j := by simpa using Nat.mul_le_mul_right j ha
  have hgap (j : ℕ) (_ : 1 ≤ j) : f j + j ≤ f (j + 1) := by
    rw [hf, hf, hstep]
    have := hmul j
    omega
  -- At f(j) there are g(j) missing values, so g(j) + 1 is the next cutoff.
  let α (j : ℕ) : ℝ := (g j + 1 : ℕ)
  have hα (j : ℕ) (hj : 2 ≤ j) : (f (j - 1) : ℝ) ≤ α j ∧ α j ≤ f j := by
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [α, Nat.cast_le, Nat.add_sub_cancel, hf, hstep]
    have := hmul i
    omega
  have hh (m : ℕ) (hm : 1 ≤ m) : 1 ≤ h m ∧ α (h m) ≤ m ∧ (m : ℝ) < α (h m + 1) := by
    obtain ⟨hp, hlo, hhi⟩ := hbracket m hm
    exact ⟨hp, Nat.cast_le.mpr (Nat.succ_le_of_lt hlo), Nat.cast_lt.mpr (Nat.lt_succ_of_le hhi)⟩
  have hclose (j : ℕ) (_ : 1 ≤ j) : (f j : ℝ) - α j < j := by
    simp only [α, hf, Nat.cast_add, Nat.cast_one]
    linarith
  have hnext : n + h n < f (h n + 1) := by
    rw [hf]
    exact Nat.lt_succ_of_le (Nat.add_le_add_right (hbracket n hn).2.2 _)
  have htest : a * s n * (s n + 1) < 2 * n ↔ g (s n + 1) < n := by
    rw [← Nat.cast_lt (α := ℝ), ← Nat.cast_lt (α := ℝ) (m := g (s n + 1))]
    simp only [g, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_choose_two ℝ]
    constructor <;> intro hc <;> nlinarith only [hc]
  rw [hseq, ← haCast,
    nthNonValue_eq_interleave_of_sub_lt f (by simp [f]) hgap α hα h hh hclose n hn,
    ite_eq_right hnext.not_ge]
  change n + h n = if a * s n * (s n + 1) < 2 * n then n + s n + 1 else n + s n
  by_cases hc : g (s n + 1) < n <;> simp [h, htest, hc, Nat.add_assoc]

end MetaMathlibExt

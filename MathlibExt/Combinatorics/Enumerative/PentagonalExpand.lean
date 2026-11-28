/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Coefficients of the expanded pentagonal series

For a nonzero dilation factor `p` and degrees `j ≤ n`, the coefficient at degree `j` is the
signed sum over pentagonal indices in `[-n, n]` whose dilated degree is `j`.

## References

* Leonhard Euler, *Evolutio producti infiniti $(1-x)(1-x^2)(1-x^3)(1-x^4)(1-x^5)(1-x^6)$
  etc. in seriem simplicem*, Acta Academiae Scientiarum Imperialis Petropolitanae,
  vol. 1780, part I (1783), pp. 47–55; the pentagonal number theorem.
* `coeff_expand_pentagonalSeries` and its interval bound were extracted from
  `MathlibExt.NumberTheory.RamanujanTauModNineteen`.
-/

namespace PowerSeries

private theorem mem_Icc_of_pentagonal_le {r : ℤ} {n : ℕ} (h : pentagonal r ≤ n) :
    r ∈ Finset.Icc (-(n : ℤ)) n := by
  have h₂ := two_mul_natCast_pentagonal r
  have h' : (pentagonal r : ℤ) ≤ n := by exact_mod_cast h
  rw [Finset.mem_Icc]
  constructor <;> nlinarith

/-- **Coefficients of Euler's pentagonal series after dilation.** For `j ≤ n` and `p ≠ 0`, the
coefficient of `X ^ j` in `∑_r (-1)^r X^(p P(r))`, the expansion of Euler's pentagonal series
by `p`, is a finite sum over `r ∈ [-n, n]`. -/
public theorem coeff_expand_pentagonalSeries (p : ℕ) (hp : p ≠ 0) {j n : ℕ} (hj : j ≤ n) :
    coeff j (expand p hp (pentagonalSeries ℤ)) =
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, if p * pentagonal r = j then (r.negOnePow : ℤ) else 0 := by
  rw [coeff_expand]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
    simp_rw [Nat.mul_left_cancel_iff (Nat.pos_of_ne_zero hp)]
    by_cases hm : m ∈ Set.range pentagonal
    · obtain ⟨r₀, rfl⟩ := hm
      have hle : pentagonal r₀ ≤ n :=
        (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hp)).trans hj
      rw [coeff_pentagonalSeries_pentagonal, Int.cast_id]
      simp_rw [pentagonal_inj]
      rw [Finset.sum_ite_eq', ite_eq_left (mem_Icc_of_pentagonal_le hle)]
    · rw [coeff_pentagonalSeries_eq_zero ℤ hm]
      exact (Finset.sum_eq_zero fun r _ => ite_eq_right fun h => hm ⟨r, h⟩).symm
  · exact (Finset.sum_eq_zero fun r _ => ite_eq_right fun h => hdvd ⟨_, h.symm⟩).symm

end PowerSeries

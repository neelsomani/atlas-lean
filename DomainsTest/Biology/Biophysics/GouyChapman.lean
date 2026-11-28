/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.Biophysics.GouyChapman
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Checks for the negative-charge Gouy–Chapman branch

With `e = ε = k_B = T = 1`, `C₀ = 1/2`, and `σ = -3/2`, the reduced charge is `-3/2` and the
charge ratio is `-4/3`. The two radicals in the branch formulas are rational in this example,
so the printed and corrected formulas can be compared by exact arithmetic.
-/

open Set WantedExt.Biology.Biophysics.GouyChapmanWanted

local notation "h₀" => reducedCharge 1 1 1 1 (1 / 2) (-3 / 2)
local notation "a₀" => chargeRatio 1 1 1 1 (1 / 2) (-3 / 2)

/-- **Independent check at a negative charge.** The printed expression exceeds `1`; the
corrected expression agrees with the reduced-charge formula and belongs to `(-1, 0)`. -/
example : 1 < -a₀ + Real.sqrt (1 + a₀ ^ 2) ∧
    h₀ / (2 + Real.sqrt (4 + h₀ ^ 2)) = -a₀ - Real.sqrt (1 + a₀ ^ 2) ∧
    -a₀ - Real.sqrt (1 + a₀ ^ 2) ∈ Ioo (-1) 0 := by
  have hh : h₀ = -3 / 2 := by
    rw [reducedCharge_eq_div_sqrt 1 1 1 1 (1 / 2) (-3 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have ha : a₀ = -4 / 3 := by
    have hha := reducedCharge_mul_chargeRatio 1 1 1 1 (1 / 2) (-3 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hh] at hha
    calc
      a₀ = 2 / (-3 / 2) := (eq_div_iff_mul_eq (by norm_num)).2 ((mul_comm _ _).trans hha)
      _ = -4 / 3 := by norm_num
  rw [hh, ha]
  norm_num [mem_Ioo]

/-- **Client check.** Apply the public theorem to locate the corrected branch at this charge. -/
example : -a₀ - Real.sqrt (1 + a₀ ^ 2) ∈ Ioo (-1) 0 :=
  (g_eq_corrected_of_neg 1 1 1 1 (1 / 2) (-3 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.2

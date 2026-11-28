/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The negative-charge Gouy–Chapman branch

For a `1:1` electrolyte with `e, ε, k_B, T, C₀ > 0` and surface charge density `σ < 0`, use the
SI Bjerrum length `ℓ_B = e² / (4π ε k_B T)` and Debye length `λ_D = √(ε k_B T / (2 e² C₀))`.
Writing `h = 4π ℓ_B σ λ_D / e` and `a = e / (2π ℓ_B σ λ_D)`, the expression `-a + √(1 + a²)`
printed in the source exceeds `1`. The corrected branch equals `h / (2 + √(4 + h²))` and lies
in `(-1, 0)`. This is a sign and normalization calculation, not a proof of the differential
equation for the potential.

## References

* Andrei Tokmakoff, *Concepts in Biophysical Chemistry*, Chemistry LibreTexts (2021),
  §6.7, “Ion Distributions Near a Charged Interface,” subsection “Gouy–Chapman Model.”
  The model and printed expression for `g` come from this section; the signed correction is
  derived here.
-/

namespace WantedExt.Biology.Biophysics.GouyChapmanWanted

open Set

@[expose] public section

/-- The **Bjerrum length** `ℓ_B = e² / (4π ε k_B T)` (supplied SI convention). -/
noncomputable def bjerrum (e ε kB T : ℝ) : ℝ :=
  e ^ 2 / (4 * Real.pi * ε * kB * T)

/-- The **Debye length** `λ_D = √(ε k_B T / (2 e² C₀))` of a `1:1` electrolyte. -/
noncomputable def debye (e ε kB T C₀ : ℝ) : ℝ :=
  Real.sqrt (ε * kB * T / (2 * e ^ 2 * C₀))

/-- The reduced surface charge `h = 4π ℓ_B σ λ_D / e`. -/
noncomputable def reducedCharge (e ε kB T C₀ σ : ℝ) : ℝ :=
  4 * Real.pi * bjerrum e ε kB T * σ * debye e ε kB T C₀ / e

/-- `a = x₀ / λ_D` with `x₀ = e / (2π ℓ_B σ)`. -/
noncomputable def chargeRatio (e ε kB T C₀ σ : ℝ) : ℝ :=
  e / (2 * Real.pi * bjerrum e ε kB T * σ) / debye e ε kB T C₀

end

/-- **Reduced charge in SI parameters.** For positive `e`, `ε`, `kB`, `T` and `C₀`, substitution
of the Bjerrum and Debye lengths gives `h = σ / √(2 ε kB T C₀)`, independent of `e`. -/
public theorem reducedCharge_eq_div_sqrt (e ε kB T C₀ σ : ℝ) (he : 0 < e) (hε : 0 < ε)
    (hkB : 0 < kB) (hT : 0 < T) (hC : 0 < C₀) :
    reducedCharge e ε kB T C₀ σ = σ / Real.sqrt (2 * (ε * kB * T) * C₀) := by
  have hroot : 0 < Real.sqrt (2 * (ε * kB * T) * C₀) := by positivity
  have hDebye : debye e ε kB T C₀ = ε * kB * T / (e * Real.sqrt (2 * (ε * kB * T) * C₀)) := by
    unfold debye
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    rw [div_pow, mul_pow e, Real.sq_sqrt (by positivity)]
    field_simp
  rw [reducedCharge, hDebye, bjerrum]
  field_simp

/-- **Reciprocity of reduced charge and charge ratio.** For positive `e`, `ε`, `kB`, `T` and `C₀`
and nonzero `σ`, the reduced charge `h` and the signed ratio `a = x₀ / λ_D` satisfy `h * a = 2`. -/
public theorem reducedCharge_mul_chargeRatio (e ε kB T C₀ σ : ℝ) (he : 0 < e) (hε : 0 < ε)
    (hkB : 0 < kB) (hT : 0 < T) (hC : 0 < C₀) (hσ : σ ≠ 0) :
    reducedCharge e ε kB T C₀ σ * chargeRatio e ε kB T C₀ σ = 2 := by
  have hB : 0 < bjerrum e ε kB T := by unfold bjerrum; positivity
  have hD : 0 < debye e ε kB T C₀ := by unfold debye; positivity
  unfold reducedCharge chargeRatio
  field_simp
  ring

/-- **The corrected branch for negative charge** (Tokmakoff, Section 6.7, corrected): for
`e, ε, k_B, T, C₀ > 0` and `σ < 0`, with `h` and `a = x₀ / λ_D < 0` as above, the printed value
`-a + √(1 + a²)` exceeds `1`, while `h / (2 + √(4 + h²)) = -a - √(1 + a²)`, which lies in
`(-1, 0)`.

Source: Tokmakoff, Section 6.7. -/
public theorem g_eq_corrected_of_neg (e ε kB T C₀ σ : ℝ) (he : 0 < e) (hε : 0 < ε)
    (hkB : 0 < kB) (hT : 0 < T) (hC : 0 < C₀) (hσ : σ < 0) :
    1 < -chargeRatio e ε kB T C₀ σ + Real.sqrt (1 + chargeRatio e ε kB T C₀ σ ^ 2) ∧
      reducedCharge e ε kB T C₀ σ / (2 + Real.sqrt (4 + reducedCharge e ε kB T C₀ σ ^ 2)) =
        -chargeRatio e ε kB T C₀ σ - Real.sqrt (1 + chargeRatio e ε kB T C₀ σ ^ 2) ∧
      -chargeRatio e ε kB T C₀ σ - Real.sqrt (1 + chargeRatio e ε kB T C₀ σ ^ 2) ∈ Ioo (-1) 0 := by
  set h := reducedCharge e ε kB T C₀ σ
  set a := chargeRatio e ε kB T C₀ σ
  have hha : h * a = 2 := reducedCharge_mul_chargeRatio e ε kB T C₀ σ he hε hkB hT hC hσ.ne
  have hh : h < 0 := by
    rw [show h = σ / Real.sqrt (2 * (ε * kB * T) * C₀) from
      reducedCharge_eq_div_sqrt e ε kB T C₀ σ he hε hkB hT hC]
    exact div_neg_of_neg_of_pos hσ (by positivity)
  have ha : a < 0 := neg_of_mul_pos_right (hha.symm ▸ (by norm_num : (0 : ℝ) < 2)) hh.le
  have h_eq : h = 2 / a := (eq_div_iff ha.ne).2 hha
  set s := Real.sqrt (1 + a ^ 2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hs_one : 1 ≤ s := Real.one_le_sqrt.2 (by linarith [sq_nonneg a])
  have ha_lt : -a < s := Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hs_lt : s < 1 - a := (Real.sqrt_lt' (by linarith)).2 (by nlinarith)
  have hs_eq : Real.sqrt (4 + h ^ 2) = -(2 * s / a) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (neg_nonneg.mpr
      (div_nonpos_of_nonneg_of_nonpos (by positivity) ha.le))).2
    rw [h_eq, neg_sq, div_pow, div_pow, mul_pow, hs_sq]
    field_simp [ha.ne]
    ring
  refine ⟨by linarith, ?_, ⟨by linarith, by linarith⟩⟩
  apply (div_eq_iff (by positivity)).2
  rw [hs_eq, h_eq]
  field_simp [ha.ne]
  nlinarith [hs_sq]

end WantedExt.Biology.Biophysics.GouyChapmanWanted

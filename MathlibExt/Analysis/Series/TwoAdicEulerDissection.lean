/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Two-adic dissection of the Euler function

For complex $q$ with $|q| < 1$, splitting the Euler product at $q^{2^j}$ into odd and even
exponents turns the factor in the dissection into the ratio of two consecutive powered Euler
products. To justify cancellation in the unconditional product, we count each Euler factor at
$q^{2^j}$ with multiplicity $2^j$. The norms of the deviations of these repeated factors from
one have a summable polynomial-geometric majorant. The resulting product converges to a nonzero
limit, so the product of the successive ratios cancels in the group of complex units.

## References

* Christophe Vignat and Michael Milgram, *Curious Multisection Identities by Index Factorization*,
  Journal of Integer Sequences 27 (2024), Article 24.5.5, pp. 1–37, Proposition 19, equation (149).
-/

namespace MetaMathlibExt

open QPochhammer

private theorem exists_hasProd_dyadicEuler_pow (q : ℂ) (hq : ‖q‖ < 1)
    (hbase : ∀ j : ℕ, ‖q ^ 2 ^ j‖ < 1) :
    ∃ L : ℂ, L ≠ 0 ∧ HasProd (fun j : ℕ =>
      qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ j) (hbase j) ^ 2 ^ j) L := by
  let I := Σ j : ℕ, Fin (2 ^ j) × ℕ
  let f (p : I) : ℂ := -(q ^ 2 ^ p.1 * (q ^ 2 ^ p.1) ^ p.2.2)
  let r := ‖q‖
  let g (p : I) : ℝ := r ^ (2 ^ p.1) * r ^ p.2.2
  have hr : 0 ≤ r := norm_nonneg q
  have hg₀ (p : I) : 0 ≤ g p := mul_nonneg (pow_nonneg hr _) (pow_nonneg hr _)
  have hgeom := summable_geometric_of_lt_one hr hq
  have hrow (j : ℕ) : Summable (fun p : Fin (2 ^ j) × ℕ => g ⟨j, p⟩) :=
    (summable_prod_of_nonneg fun p => hg₀ ⟨j, p⟩).2
      ⟨fun _ => hgeom.mul_left (r ^ (2 ^ j : ℕ)), (hasSum_fintype _).summable⟩
  have hweighted : Summable fun j : ℕ => ((2 ^ j : ℕ) : ℝ) * r ^ (2 ^ j) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (show ‖r‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hr])
    have hs : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by simpa only [pow_one] using h
    exact hs.comp_injective (Nat.pow_right_injective (a := 2) (by decide))
  have hg : Summable g := by
    refine (summable_sigma_of_nonneg hg₀).2 ⟨hrow, ?_⟩
    refine (hweighted.mul_right (∑' k : ℕ, r ^ k)).congr fun j => ?_
    rw [(hrow j).tsum_prod]
    simp only [g, tsum_mul_left, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have hf : Summable fun p : I => ‖f p‖ := hg.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => by
    simp only [f, g, norm_neg, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg hr _) ?_ _) (pow_nonneg hr _)
    exact pow_le_pow_of_le_one hr hq.le (Nat.one_le_iff_ne_zero.mpr (by positivity)) |>.trans_eq
      (pow_one _)
  have hne (p : I) : 1 + f p ≠ 0 := by
    simp only [f, ← sub_eq_add_neg, ← pow_succ', sub_ne_zero]
    intro h
    have hn : ‖(q ^ 2 ^ p.1) ^ (p.2.2 + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (hbase p.1) (Nat.succ_ne_zero _)
    rw [← h, norm_one] at hn
    exact (lt_irrefl 1) hn
  let F (p : I) : ℂ := 1 + f p
  have hm : Multipliable F := multipliable_one_add_of_summable hf
  let L : ℂ := ∏' p : I, F p
  have hL : L ≠ 0 := tprod_one_add_ne_zero_of_summable (f := f) hne hf
  have hfiber (j : ℕ) : HasProd (fun p : Fin (2 ^ j) × ℕ => F ⟨j, p⟩)
      (qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ j) (hbase j) ^ 2 ^ j) := by
    have hfj : Summable (fun p : Fin (2 ^ j) × ℕ => ‖f ⟨j, p⟩‖) :=
      ((summable_sigma_of_nonneg fun p : I => norm_nonneg (f p)).mp hf).1 j
    have hj : Multipliable (fun p : Fin (2 ^ j) × ℕ => F ⟨j, p⟩) :=
      multipliable_one_add_of_summable (f := fun p => f ⟨j, p⟩) hfj
    have hinner (i : Fin (2 ^ j)) : HasProd (fun k : ℕ => F ⟨j, (i, k)⟩)
        (qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ j) (hbase j)) := by
      simpa only [F, f, ← sub_eq_add_neg] using
        hasProd_qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ j) (hbase j)
    have hval : (∏' p : Fin (2 ^ j) × ℕ, F ⟨j, p⟩) =
        qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ j) (hbase j) ^ 2 ^ j := by
      rw [hj.tprod_prod' (fun i => (hinner i).multipliable)]
      simp only [fun i => (hinner i).tprod_eq, tprod_fintype, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    exact hval ▸ hj.hasProd
  exact ⟨L, hL, HasProd.sigma (f := F) hm.hasProd hfiber⟩

/-- **2-adic dissection of the Euler function.** For every complex number $q$ with $|q| < 1$,
with the infinite q-Pochhammer symbol $(a; r)_\infty = \prod_{k \ge 0} (1 - a r^k)$, the
unconditional infinite product over $j \ge 0$ satisfies
$$\prod_{j \ge 0} \left( \frac{(q^{2^j}; q^{2^{j+1}})_\infty}
{(q^{2^{j+1}}; q^{2^{j+1}})_\infty} \right)^{2^j} = (q; q)_\infty.$$

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, first display (`jis-2024-24.5.5-prop-19`). -/
public theorem tprod_qPochhammer_twoAdic (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, (QPochhammer.qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
        / QPochhammer.qPochhammerInf (q ^ 2 ^ (j + 1)) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))) ^ 2 ^ j
      = QPochhammer.qPochhammerInf q q hq := by
  let w (j : ℕ) := q ^ (2 ^ j : ℕ)
  have hw (j : ℕ) : ‖w j‖ < 1 := by
    rw [show w j = q ^ (2 ^ j : ℕ) from rfl, norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by positivity)
  let E (j : ℕ) := qPochhammerInf (w j) (w j) (hw j)
  let A (j : ℕ) := qPochhammerInf (w j) (w (j + 1)) (hw (j + 1))
  let B (j : ℕ) := E j ^ (2 ^ j : ℕ)
  have hsq (j : ℕ) : w j ^ 2 = w (j + 1) := by
    change (q ^ (2 ^ j : ℕ)) ^ (2 : ℕ) = q ^ (2 ^ (j + 1) : ℕ)
    rw [← pow_mul, pow_succ]
  have hsplit (j : ℕ) : E j = A j * E (j + 1) := by
    have ha : HasProd (fun k : ℕ => 1 - w j * (w j) ^ (2 * k)) (A j) := by
      simpa only [pow_mul, hsq] using hasProd_qPochhammerInf (w j) (w (j + 1)) (hw (j + 1))
    have he : HasProd (fun k : ℕ => 1 - w j * (w j) ^ (2 * k + 1)) (E (j + 1)) := by
      refine (hasProd_qPochhammerInf (w (j + 1)) (w (j + 1)) (hw (j + 1))).congr_fun fun k => ?_
      rw [pow_succ', pow_mul, ← hsq, pow_two, mul_assoc]
    exact (hasProd_qPochhammerInf (w j) (w j) (hw j)).unique (ha.even_mul_odd he)
  obtain ⟨L, hL, hB⟩ : ∃ L : ℂ, L ≠ 0 ∧ HasProd B L := exists_hasProd_dyadicEuler_pow q hq hw
  have hB₀ (j : ℕ) : B j ≠ 0 := fun hj =>
    hL (hB.unique (hasProd_zero_of_exists_eq_zero ⟨j, hj⟩))
  have hE₀ (j : ℕ) : E j ≠ 0 := by
    intro hj
    exact hB₀ j (by simp only [B, hj, zero_pow (by positivity : 2 ^ j ≠ 0)])
  let U (j : ℕ) := Units.mk0 (B j) (hB₀ j)
  have hU : Multipliable U := ⟨Units.mk0 L hL,
    (Units.isEmbedding_val₀.isInducing.hasProd_iff (g := Units.coeHom ℂ) U _).mp hB⟩
  have hshift := (multipliable_nat_add_iff 1).2 hU
  have hquot := hU.hasProd.div hshift.hasProd
  rw [hU.tprod_eq_zero_mul, mul_div_cancel_right] at hquot
  change (∏' j : ℕ, (A j / E (j + 1)) ^ (2 ^ j : ℕ)) = _
  calc
    _ = (↑(U 0) : ℂ) := by
      refine ((hquot.map (Units.coeHom ℂ) Units.continuous_val).congr_fun fun j => ?_).tprod_eq
      change (A j / E (j + 1)) ^ (2 ^ j : ℕ) =
        E j ^ (2 ^ j : ℕ) / E (j + 1) ^ (2 ^ (j + 1) : ℕ)
      have hratio : A j / E (j + 1) = E j / E (j + 1) ^ (2 : ℕ) := by
        rw [hsplit j, pow_two, mul_div_mul_right _ _ (hE₀ (j + 1))]
      rw [hratio, div_pow, ← pow_mul, pow_succ (2 : ℕ) j, Nat.mul_comm 2]
    _ = _ := by simp [U, B, E, w]

end MetaMathlibExt

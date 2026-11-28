/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelNonIntegrality
public import MathlibExt.NumberTheory.GobelSequence
import Mathlib.NumberTheory.Padics.RingHoms
import MathlibExt.NumberTheory.GobelNonIntegralityDiagonalIsZigzagBelowGobelResidueWalkOfOdd

/-!
# The half-exponent Göbel residue walk

For an odd prime $p$ and a natural number $l \le p-1$, set $k=(p-1)/2$. For
$1 \le n \le p$, the scaled Göbel term $n g_{k,l}(n)$ and the residue walk from $l$
have the same residue modulo $p$. In particular, $g_{k,l}(p)$ is $p$-integral
exactly when the walk ends at $0$ or $p$.

## References

* Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*,
  Journal of Integer Sequences **29** (2026), Article 26.3.8, pp. 1–25, Definition 5 and Lemma 6.
-/

namespace MetaMathlibExt

-- The two endpoints represent zero. At an interior point, Euler's criterion
-- turns the power of the quotient into the product of the two signs.
private theorem residueWalk_step {p l n : ℕ} [Fact p.Prime] (hpodd : Odd p) (hn : 1 ≤ n)
    (hnp : n < p) (hw : gobelResidueWalk p l n ≤ p) {r : ZMod p}
    (hr : (n : ZMod p) * r = (gobelResidueWalk p l n : ZMod p)) :
    (gobelResidueWalk p l (n + 1) : ZMod p) =
      (gobelResidueWalk p l n : ZMod p) + r ^ ((p - 1) / 2) := by
  have hp : p.Prime := Fact.out
  have hn0 : (n : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff n p).not.mpr (Nat.not_dvd_of_pos_of_lt hn hnp)
  have hdiv : r = (gobelResidueWalk p l n : ZMod p) / n :=
    (eq_div_iff hn0).2 ((mul_comm _ _).trans hr)
  have hpos : 0 < (p - 1) / 2 := by
    have := hp.two_le
    obtain ⟨a, ha⟩ := hpodd
    omega
  by_cases hzero : gobelResidueWalk p l n = 0
  · rw [gobelResidueWalk_succ_of_eq_zero p l n hn hzero, hdiv, hzero]
    simp [hpos.ne']
  by_cases hprime : gobelResidueWalk p l n = p
  · rw [gobelResidueWalk_succ_of_eq_prime p l n hn hprime, hdiv, hprime]
    simp [hpos.ne']
  have hwpos : 0 < gobelResidueWalk p l n := Nat.pos_of_ne_zero hzero
  have hwlt : gobelResidueWalk p l n < p := lt_of_le_of_ne hw hprime
  have hncop : (n : ℤ).gcd p = 1 := (Nat.coprime_of_lt_prime (by omega) hnp hp).symm
  have hwcop : (gobelResidueWalk p l n : ℤ).gcd p = 1 :=
    (Nat.coprime_of_lt_prime hzero hwlt hp).symm
  have hk : (p - 1) / 2 = p / 2 := by
    obtain ⟨a, ha⟩ := hpodd
    omega
  have hpow (a : ℕ) : (a : ZMod p) ^ ((p - 1) / 2) = (jacobiSym (a : ℤ) p : ZMod p) := by
    simpa only [hk, jacobiSym.legendreSym.to_jacobiSym, Int.cast_natCast] using
      (legendreSym.eq_pow (p := p) (a : ℤ)).symm
  have hsignInv : (jacobiSym (n : ℤ) p : ZMod p)⁻¹ = (jacobiSym (n : ℤ) p : ZMod p) := by
    rcases jacobiSym.eq_one_or_neg_one hncop with h | h <;> simp [h]
  have hpower : r ^ ((p - 1) / 2) =
      (jacobiSym (n : ℤ) p * jacobiSym (gobelResidueWalk p l n : ℤ) p : ℤ) := by
    rw [hdiv, div_pow, hpow, hpow, div_eq_mul_inv, hsignInv, Int.cast_mul, mul_comm]
  rw [gobelResidueWalk_succ_of_between p l n hn ⟨hwpos, hwlt⟩, hpower]
  have hnonneg :
      0 ≤ (gobelResidueWalk p l n : ℤ) + jacobiSym (n : ℤ) p *
        jacobiSym (gobelResidueWalk p l n : ℤ) p := by
    rcases jacobiSym.eq_one_or_neg_one hncop with h₁ | h₁ <;>
      rcases jacobiSym.eq_one_or_neg_one hwcop with h₂ | h₂ <;>
      simp only [h₁, h₂, one_mul, mul_one, neg_mul, neg_neg] <;> omega
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg, Int.cast_add, Int.cast_natCast]

-- Identify the kernel of reduction on p-adic integers that come from rationals.
private theorem reduction_eq_zero_iff {p : ℕ} [Fact p.Prime] {q : ℚ} {a : ℤ_[p]}
    (ha : (a : ℚ_[p]) = (q : ℚ_[p])) :
    PadicInt.toZMod a = 0 ↔ q = 0 ∨ 1 ≤ padicValRat p q := by
  by_cases hq : q = 0
  · have ha0 : a = 0 := PadicInt.ext (by simpa [hq] using ha)
    simp [ha0, hq]
  · have ha0 : a ≠ 0 := by
      intro h
      exact hq (Rat.cast_eq_zero.mp (ha.symm.trans (by simp [h])))
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, or_iff_right hq]
    have hval : a.valuation = (padicValRat p q).toNat := by
      rw [PadicInt.valuation, ha, Padic.valuation_ratCast]
    rw [← pow_one (p : ℤ_[p]), PadicInt.mem_span_pow_iff_le_valuation a ha0, hval]
    omega

/-- **Index-scaled Göbel terms with $k = (p-1)/2$ are congruent to the residue walk.** Let $p$
be an odd prime and $l \le p - 1$ a natural number. Write $k = (p-1)/2$, let $g_{k,l}$ be the
$(k,l)$-Göbel sequence, and let $\tilde g_l$ be the residue walk of $p$ starting at $l$. Then
(a) for every $1 \le n \le p$, the rational number $n\,g_{k,l}(n) - \tilde g_l(n)$ is either $0$
or has $p$-adic valuation at least $1$, that is,
$n\,g_{k,l}(n) \equiv \tilde g_l(n) \pmod{p}$ in $\mathbb{Z}_{(p)}$; and (b) $g_{k,l}(p)$ lies in
the localization $\mathbb{Z}_{(p)}$, that is, has nonnegative $p$-adic valuation, if and only if
$\tilde g_l(p) = 0$ or $\tilde g_l(p) = p$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 6. -/
public theorem gobelSequence_half_pred_congruent_residue_walk
    (p l : ℕ) (hp : p.Prime) (hpodd : Odd p) (hl : l ≤ p - 1) :
    (∀ n, 1 ≤ n → n ≤ p →
      let d : ℚ := (n : ℚ) * gobelSequence ((p - 1) / 2) l n - gobelResidueWalk p l n
      d = 0 ∨ 1 ≤ padicValRat p d) ∧
    (0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p) ↔
      gobelResidueWalk p l p = 0 ∨ gobelResidueWalk p l p = p) := by
  have : Fact p.Prime := ⟨hp⟩
  let k := (p - 1) / 2
  let g := gobelSequence k l
  let w := gobelResidueWalk p l
  have hk : 1 ≤ k := by
    dsimp [k]
    have := hp.two_le
    obtain ⟨a, ha⟩ := hpodd
    omega
  have hw (n : ℕ) : w n ≤ p := gobelResidueWalk_le p l (by omega) n
  -- Track an integral lift of each scaled term and its residue.
  have hscale (n : ℕ) (hn : 1 ≤ n) (hnp : n ≤ p) :
      ∃ a : ℤ_[p], (a : ℚ_[p]) = (((n : ℚ) * g n : ℚ) : ℚ_[p]) ∧
        PadicInt.toZMod a = (w n : ZMod p) := by
    induction n, hn using Nat.le_induction with
    | base =>
      refine ⟨(l : ℤ_[p]), ?_, ?_⟩
      · simp [g, gobelSequence_one]
      · simp [w, gobelResidueWalk_one]
    | succ n hn ih =>
      have hnlt : n < p := hnp
      obtain ⟨a, ha, hres⟩ := ih hnlt.le
      have hnNorm : ‖(n : ℚ_[p])‖ = 1 :=
        Padic.norm_natCast_eq_one_iff.mpr (Nat.coprime_of_lt_prime (by omega) hnlt hp)
      have hgNorm : ‖(g n : ℚ_[p])‖ ≤ 1 := by
        have h := PadicInt.norm_le_one a
        rwa [← PadicInt.norm_coe, ha, Rat.cast_mul, Rat.cast_natCast, norm_mul, hnNorm,
          one_mul] at h
      let b : ℤ_[p] := Padic.lift (g n : ℚ_[p]) hgNorm
      have hmul : (n : ℤ_[p]) * b = a := by
        apply PadicInt.ext
        simp [b, ha]
      have hr : (n : ZMod p) * PadicInt.toZMod b = (w n : ZMod p) := by
        rw [← map_natCast PadicInt.toZMod, ← map_mul, hmul, hres]
      have hres' := residueWalk_step hpodd hn hnlt (hw n) hr
      have hrec : ((n + 1 : ℕ) : ℚ) * g (n + 1) = (n : ℚ) * g n + g n ^ k := by
        change ((n + 1 : ℕ) : ℚ) * gobelSequence k l (n + 1) = _
        rw [Nat.cast_add, Nat.cast_one, gobelSequence_succ k l n hn]
        simp only [g, mul_add, mul_comm (gobelSequence k l n) (n : ℚ), ← pow_succ',
          Nat.sub_add_cancel hk]
      refine ⟨a + b ^ k, ?_, ?_⟩
      · rw [PadicInt.coe_add, PadicInt.coe_pow, ha, PadicInt.coe_lift, ← Rat.cast_pow,
          ← Rat.cast_add, ← hrec]
      · rw [map_add, map_pow, hres, hres']
  constructor
  · intro n hn hnp
    obtain ⟨a, ha, hres⟩ := hscale n hn hnp
    exact (reduction_eq_zero_iff (q := (n : ℚ) * g n - w n) (a := a - (w n : ℤ_[p]))
      (by simp [ha])).mp (by simp [hres])
  · obtain ⟨a, ha, hres⟩ := hscale p hp.pos le_rfl
    have hzero : PadicInt.toZMod a = 0 ↔ w p = 0 ∨ w p = p := by
      rw [hres, ZMod.natCast_eq_zero_iff]
      constructor
      · intro hdvd
        rcases (hw p).eq_or_lt with heq | hlt
        · exact Or.inr heq
        · exact Or.inl (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
      · rintro (hz | hz) <;> simp [hz]
    rw [← hzero, reduction_eq_zero_iff ha]
    change 0 ≤ padicValRat p (g p) ↔ (p : ℚ) * g p = 0 ∨ 1 ≤ padicValRat p ((p : ℚ) * g p)
    by_cases hgp : g p = 0
    · simp [hgp, padicValRat.zero]
    · have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      rw [or_iff_right (mul_ne_zero hp0 hgp), padicValRat.mul hp0 hgp, padicValRat.self hp.one_lt]
      omega

end MetaMathlibExt

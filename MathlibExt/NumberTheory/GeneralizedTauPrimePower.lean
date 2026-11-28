/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.GeneralizedTau
import Mathlib.Algebra.Field.ZMod
import MathlibExt.Combinatorics.Enumerative.PentagonalExpand

/-!
# Generalized tau at a prime power

For a prime `p`, a positive natural number `s` and a natural number `n`, the residue of
`τ_(p^s)(n + 1)` modulo `p` is the Euler pentagonal coefficient with its degree dilated by
`p ^ s`. Iterated Frobenius gives the dilation before the shift by one in the tau index.

## References

* S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
  Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
  Article A39, pp. 1–30, Theorem 15 (pp. 19–20, equation (28)).
* Leonhard Euler, *Evolutio producti infiniti $(1-x)(1-x^2)(1-x^3)(1-x^4)(1-x^5)(1-x^6)$
  etc. in seriem simplicem*, Acta Academiae Scientiarum Imperialis Petropolitanae,
  vol. 1780, part I (1783), pp. 47–55; the pentagonal number theorem used in Theorem 15.
* The Frobenius step follows `generalizedTau_prime_sq_add_one_succ_modEq` in
  `MathlibExt.NumberTheory.GeneralizedTauPrimeSquare`; the coefficient formula is the one
  extracted from `MathlibExt.NumberTheory.RamanujanTauModNineteen`.
-/

namespace MetaMathlibExt

open PowerSeries

/-- **Generalized tau at a prime power modulo the prime.** Let $p$ be a prime, let $s \ge 1$ and
$n \ge 0$ be natural numbers, and for an integer $t$ let $P(t) = t(3t - 1)/2$ be the generalized
pentagonal number. Then $\tau_{p^s}(n + 1)$ is congruent modulo $p$ to the sum of $(-1)^t$ over
the integers $t$ with $-n \le t \le n$ and $n = p^s P(t)$.

Since $P$ is injective, this sum has at most one term: $\tau_{p^s}(n + 1) \equiv (-1)^t \pmod{p}$
if $n = p^s P(t)$, and $\tau_{p^s}(n + 1) \equiv 0 \pmod{p}$ if $n$ is not of this form.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Theorem 15 (`integers-2024-A39-thm-15`). -/
public theorem generalizedTau_prime_pow_succ_modEq (p : ℕ) (hp : p.Prime) (s : ℕ)
    (hs : 0 < s) (n : ℕ) :
    generalizedTau ((p ^ s : ℕ) : ℤ) (n + 1) ≡
      ∑ t ∈ Finset.Icc (-(n : ℤ)) n,
          if n = p ^ s * pentagonal t then (t.negOnePow : ℤ) else 0 [ZMOD p] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have : Fact p.Prime := ⟨hp⟩
  rw [generalizedTau_natCast, coeff_succ_X_mul, ← ZMod.intCast_eq_intCast_iff]
  change Int.castRingHom (ZMod p) _ = _
  simp_rw [eq_comm (a := n)]
  rw [← coeff_expand_pentagonalSeries _ (pow_ne_zero _ hp.ne_zero) le_rfl]
  change Int.castRingHom (ZMod p) _ = Int.castRingHom (ZMod p) _
  rw [← coeff_map, ← coeff_map, map_pow, map_expand,
    ← map_iterateFrobenius_expand p hp.ne_zero _ (k + 1),
    RingHom.ext_zmod (iterateFrobenius (ZMod p) p (k + 1)) (RingHom.id _), map_id, id_eq]

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CompletelyAdditiveHeight
import MathlibExt.NumberTheory.CompletelyAdditiveHeightExistsHeightFunctionWithProfile
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Set.Finite.Lattice

/-!
# Iteratively defined height functions

Let `f 1 = 1`, let `j ≥ 1`, and suppose every prime divisor of `f i` for `i ≥ 1` has
one-based index less than `i`. If every positive value of `f` has a finite fiber on the
positive indices, the recurrence `H (nthPrimeOne i) = H (f i) + j` for `i ≥ 1` has a
completely additive solution on positive integers, and every such solution is a height
function. The divisor condition excludes zero values on positive indices, and including
the single index zero cannot affect finiteness of any fiber.

We define the prime values by well-founded recursion on the index. For finiteness we
induct on the height bound: a prime at the next bound comes from a fiber over a lower
sublevel, and a composite is the product of two members of the lower sublevel.

## References

* Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds, and
  Inverse Growth*, INTEGERS 26 (2026), Article A116, pp. 1–45, Theorem 2 (pp. 11–12).
-/

namespace MetaMathlibExt

open scoped Pointwise

private noncomputable def iterativePrimeHeight (f : ℕ → ℕ) (j i : ℕ) : ℕ :=
  additiveOfPrimeValues (fun p =>
    if h : Nat.count Nat.Prime p + 1 < i then
      iterativePrimeHeight f j (Nat.count Nat.Prime p + 1)
    else 0) (f i) + j
termination_by i

private theorem additiveOfPrimeValues_congr_of_dvd {v w : ℕ → ℕ} {m : ℕ} (hm : 0 < m)
    (h : ∀ p, p.Prime → p ∣ m → v p = w p) :
    additiveOfPrimeValues v m = additiveOfPrimeValues w m := by
  induction m using induction_on_primes with
  | zero => omega
  | one => simp only [additiveOfPrimeValues_one]
  | prime_mul p a hp ih =>
    have ha : 0 < a := Nat.pos_of_mul_pos_left hm
    rw [isCompletelyAdditiveNat_additiveOfPrimeValues v p a hp.pos ha,
      isCompletelyAdditiveNat_additiveOfPrimeValues w p a hp.pos ha,
      additiveOfPrimeValues_prime v hp, additiveOfPrimeValues_prime w hp,
      h p hp (dvd_mul_right p a), ih ha (fun q hq hqa => h q hq (dvd_mul_of_dvd_right hqa p))]

/-- **Iteratively defined height functions.** Write $p_i$ for the $i$-th prime, so $p_1 = 2$. Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) = 1$; suppose that for all integers $i, r \ge 1$, if
$p_r$ divides $f(i)$ then $r < i$ (this forces $f(i) \ge 1$ for $i \ge 1$); and suppose that for
every $t \ge 1$ only finitely many $i \ge 1$ have $f(i) = t$. Let $j \ge 1$. Then there is a
function $H : \mathbb{N} \to \mathbb{N}$ that is completely additive on the positive integers and
satisfies $H(p_i) = H(f(i)) + j$ for every $i \ge 1$, and every such $H$ is a height function.

The case $i = 1$ gives $H(2) = j$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 2 (`integers-2026-A116-thm-2`). -/
public theorem isHeightFunction_of_iterative (f : ℕ → ℕ) (hf1 : f 1 = 1)
    (hdiv : ∀ i r, 1 ≤ i → 1 ≤ r → nthPrimeOne r ∣ f i → r < i)
    (hfin : ∀ t, 1 ≤ t → {i : ℕ | 1 ≤ i ∧ f i = t}.Finite) {j : ℕ} (hj : 1 ≤ j) :
    (∃ H : ℕ → ℕ, IsCompletelyAdditiveNat H ∧ ∀ i, 1 ≤ i → H (nthPrimeOne i) = H (f i) + j) ∧
      ∀ H : ℕ → ℕ, IsCompletelyAdditiveNat H → (∀ i, 1 ≤ i → H (nthPrimeOne i) = H (f i) + j) →
        IsHeightFunction H := by
  have hfpos (i : ℕ) (hi : 1 ≤ i) : 0 < f i := by
    obtain rfl | _ := eq_or_lt_of_le hi
    · rw [hf1]
      exact Nat.zero_lt_one
    · refine Nat.pos_of_ne_zero fun h0 => (Nat.lt_irrefl i) (hdiv i i hi hi ?_)
      rw [h0]
      exact dvd_zero _
  constructor
  · refine ⟨additiveOfPrimeValues (fun p => iterativePrimeHeight f j (Nat.count Nat.Prime p + 1)),
      isCompletelyAdditiveNat_additiveOfPrimeValues _, fun i hi => ?_⟩
    rw [additiveOfPrimeValues_prime _ (nthPrimeOne_prime i), count_nthPrimeOne i hi]
    conv_lhs => rw [iterativePrimeHeight]
    congr 1
    refine additiveOfPrimeValues_congr_of_dvd (hfpos i hi) fun p hp hdvd => ?_
    have hlt := hdiv i (Nat.count Nat.Prime p + 1) hi (Nat.succ_pos _) (by
      rwa [nthPrimeOne_count p hp])
    rw [dite_eq_left hlt]
  · intro H hH hrec
    have hIndex (p : ℕ) (hp : p.Prime) : H p = H (f (Nat.count Nat.Prime p + 1)) + j := by
      simpa only [nthPrimeOne_count p hp] using hrec (Nat.count Nat.Prime p + 1) (Nat.succ_pos _)
    have hpPos (p : ℕ) (hp : p.Prime) : 1 ≤ H p := by
      rw [hIndex p hp]
      omega
    have hmPos (m : ℕ) (hm : 0 < m) (hne : m ≠ 1) : 1 ≤ H m := by
      obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd hne
      rw [hH p k hp.pos (Nat.pos_of_mul_pos_left hm)]
      exact (hpPos p hp).trans (Nat.le_add_right _ _)
    let level (n : ℕ) : Set ℕ := {m | 0 < m ∧ H m ≤ n}
    have hlevels (n : ℕ) : (level n).Finite := by
      induction n with
      | zero =>
        refine (Set.finite_singleton 1).subset ?_
        rintro m ⟨hm, hmn⟩
        by_contra h
        have := hmPos m hm (fun heq => h (Set.mem_singleton_iff.mpr heq))
        omega
      | succ n ih =>
        let indices := ⋃ t ∈ level n, {i : ℕ | 1 ≤ i ∧ f i = t}
        have hindices : indices.Finite := ih.biUnion fun t ht => hfin t ht.1
        refine ((Set.finite_singleton 1).union ((hindices.image nthPrimeOne).union
          (ih.mul ih))).subset ?_
        rintro m ⟨hm, hmn⟩
        by_cases h₁ : m = 1
        · exact Or.inl (Set.mem_singleton_iff.mpr h₁)
        by_cases hprime : m.Prime
        · let i := Nat.count Nat.Prime m + 1
          have hi : 1 ≤ i := Nat.succ_pos _
          have hfi : H (f i) ≤ n := by
            have h := hIndex m hprime
            change H m = H (f i) + j at h
            omega
          exact Or.inr (Or.inl ⟨i, Set.mem_biUnion ⟨hfpos i hi, hfi⟩ ⟨hi, rfl⟩,
            nthPrimeOne_count m hprime⟩)
        · obtain ⟨p, hp, a, rfl⟩ := Nat.exists_prime_and_dvd h₁
          have ha : 0 < a := Nat.pos_of_mul_pos_left hm
          have ha₁ : a ≠ 1 := by
            rintro rfl
            exact hprime (by simpa only [mul_one] using hp)
          have hpH := hpPos p hp
          have haH := hmPos a ha ha₁
          rw [hH p a hp.pos ha] at hmn
          have hp' : p ∈ level n := ⟨hp.pos, by omega⟩
          have ha' : a ∈ level n := ⟨ha, by omega⟩
          exact Or.inr (Or.inr (Set.mul_mem_mul hp' ha'))
    exact ⟨hH, hpPos, fun n _ => (hlevels n).subset fun _ hp => ⟨hp.1.pos, hp.2.le⟩⟩

end MetaMathlibExt

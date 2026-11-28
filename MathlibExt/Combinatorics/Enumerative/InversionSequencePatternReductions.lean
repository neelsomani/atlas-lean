/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.InversionSequencePatternSets
import Mathlib.Order.Interval.Finset.Fin

/-!
# Reductions of length-three pattern sets in inversion sequences

For each of the 36 listed pairs `(C, τ)` and every `n`, an inversion sequence `e : Fin n → ℕ`
with `e i ≤ i` that avoids every pattern in `C` also avoids `τ`. Thus adding `τ` to `C` does not
change the set of inversion sequences that avoid it. This includes the empty sequence, which has
no triple of indices. The proofs replace a witness for `τ` with one for an element of `C`, or rule
it out by bounding the number or size of possible entries.

## References

* Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024),
  Article A76, pp. 1–112, Theorem 2 (p. 3).
* David Callan and Toufik Mansour, *Inversion Sequences Avoiding Quadruple Length-3 Patterns*,
  INTEGERS 23 (2023), Article A78, pp. 1–64, Theorems 2–4 (pp. 3–4). Their proof for `001` and
  `101` uses the initial segment of distinct entries; we use it across the reductions for `001`.
-/

namespace MetaMathlibExt

namespace InversionSequencePatternReductions

-- Below any value that occurs in a 001-avoider, the initial entries must equal their indices.
private theorem initial_value {n : ℕ} {e : Fin n → ℕ} (he : ∀ i, e i ≤ i)
    (h001 : ¬ InvSeqContainsPattern e ![0, 0, 1]) {i : Fin n} (r : ℕ) (hr : r < e i) :
    ∃ a : Fin n, (a : ℕ) = r ∧ a < i ∧ e a = r := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    have hri : r < (i : ℕ) := hr.trans_le (he i)
    let a : Fin n := ⟨r, hri.trans i.isLt⟩
    refine ⟨a, rfl, hri, ?_⟩
    have ha : e a ≤ r := he a
    by_contra hne
    have hlt : e a < r := lt_of_le_of_ne ha hne
    obtain ⟨b, hb, _, hba⟩ := ih (e a) hlt (hlt.trans hr)
    have hb' : b < a := by
      change (b : ℕ) < r
      omega
    apply h001 ((invSeqContainsPattern_iff_exists_indices e _).2 ⟨b, a, i, hb', hri, ?_⟩)
    simp [invSeqPatternSameOrder_iff, hba]
    omega

-- With no 000 or 011, the entries at positive indices are distinct. Counting the indices
-- from 1 to e i - 1 together with j and k would give too many values strictly below e i.
private theorem not_two_smaller_of_avoid000_011 {n : ℕ} {e : Fin n → ℕ}
    (he : ∀ i, e i ≤ i) (h000 : ¬ InvSeqContainsPattern e ![0, 0, 0])
    (h011 : ¬ InvSeqContainsPattern e ![0, 1, 1]) {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hji : e j < e i) (hki : e k < e i) : False := by
  have hi := he i
  let z : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let bound : Fin n := ⟨e i, hi.trans_lt i.isLt⟩
  let interval := Finset.Ico one bound
  have hbound : bound ≤ i := hi
  have hnmem {a : Fin n} (ha : i < a) : a ∉ interval := fun h =>
    (not_lt_of_ge (hbound.trans ha.le)) (Finset.mem_Ico.mp h).2
  have hkn := hnmem (hij.trans hjk)
  have hjn : j ∉ insert k interval := by
    simpa [hjk.ne] using hnmem hij
  let indices := insert j (insert k interval)
  have hcard : indices.card = e i - 1 + 1 + 1 := by
    change (insert j (insert k interval)).card = _
    rw [Finset.card_insert_of_notMem hjn, Finset.card_insert_of_notMem hkn, Fin.card_Ico]
  have hz : e z = 0 := Nat.eq_zero_of_le_zero (he z)
  have hsmall (a : Fin n) (ha : a ∈ indices) : z < a ∧ e a < e i := by
    simp only [indices, Finset.mem_insert] at ha
    rcases ha with rfl | rfl | ha
    · have hzi : z < i := show 0 < (i : ℕ) by omega
      exact ⟨hzi.trans hij, hji⟩
    · have hzi : z < i := show 0 < (i : ℕ) by omega
      exact ⟨hzi.trans (hij.trans hjk), hki⟩
    · have ⟨hal, hau⟩ := Finset.mem_Ico.mp ha
      exact ⟨(show z < one from Nat.zero_lt_one).trans_le hal, (he a).trans_lt hau⟩
  have hne {a b : Fin n} (ha : a ∈ indices) (hab : a < b) (heq : e a = e b) : False := by
    have hza := (hsmall a ha).1
    by_cases h : e b = 0
    · apply h000 ((invSeqContainsPattern_iff_exists_indices e _).2 ⟨z, a, b, hza, hab, ?_⟩)
      simp [invSeqPatternSameOrder_iff, hz, heq, h]
    · apply h011 ((invSeqContainsPattern_iff_exists_indices e _).2 ⟨z, a, b, hza, hab, ?_⟩)
      simp [invSeqPatternSameOrder_iff, hz, heq, Nat.pos_of_ne_zero h]
  have hle := Finset.card_le_card_of_injOn (t := Finset.range (e i)) e
    (fun a ha => Finset.mem_range.mpr (hsmall a ha).2)
    (fun a ha b hb hab => by
      rcases lt_trichotomy a b with h | h | h
      · exact (hne ha h hab).elim
      · exact h
      · exact (hne hb h hab.symm).elim)
  rw [hcard, Finset.card_range] at hle
  omega

-- Avoiding 012 makes the positive entries nonincreasing. A value greater than 2 would force
-- the first three entries to be zero; a value of 2 already forces the first two to be zero.
private theorem not_two_distinct_smaller_of_avoid000_012 {n : ℕ} {e : Fin n → ℕ}
    (he : ∀ i, e i ≤ i) (h000 : ¬ InvSeqContainsPattern e ![0, 0, 0])
    (h012 : ¬ InvSeqContainsPattern e ![0, 1, 2]) {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hji : e j < e i) (hki : e k < e i) (hne : e j ≠ e k) : False := by
  let z : Fin n := ⟨0, by omega⟩
  have hz : e z = 0 := Nat.eq_zero_of_le_zero (he z)
  have hi := he i
  have hzero {a : Fin n} (ha : (a : ℕ) < e i) : e a = 0 := by
    have ha' := he a
    by_contra! h
    have hza : z < a := show 0 < (a : ℕ) by omega
    have hai : a < i := ha.trans_le hi
    apply h012 ((invSeqContainsPattern_iff_exists_indices e _).2 ⟨z, a, i, hza, hai, ?_⟩)
    simp [invSeqPatternSameOrder_iff, hz]
    omega
  have hi2 : 2 ≤ e i := by omega
  let one : Fin n := ⟨1, by omega⟩
  have h1 : e one = 0 := hzero (show 1 < e i by omega)
  have hle : e i ≤ 2 := by
    by_contra! h
    let two : Fin n := ⟨2, by omega⟩
    have h2 : e two = 0 := hzero h
    apply h000 ((invSeqContainsPattern_iff_exists_indices e _).2
      ⟨z, one, two, Nat.zero_lt_one, Nat.lt_succ_self 1, ?_⟩)
    simp [invSeqPatternSameOrder_iff, hz, h1, h2]
  have no_late_zero {a : Fin n} (hia : i < a) (ha : e a = 0) : False := by
    have h1a : one < a := show 1 < (a : ℕ) by omega
    apply h000 ((invSeqContainsPattern_iff_exists_indices e _).2
      ⟨z, one, a, Nat.zero_lt_one, h1a, ?_⟩)
    simp [invSeqPatternSameOrder_iff, hz, h1, ha]
  exact (show e j = 0 ∨ e k = 0 by omega).elim (no_late_zero hij) (no_late_zero (hij.trans hjk))

private theorem monotone_of_avoid010_021 {n : ℕ} {e : Fin n → ℕ} (he : ∀ i, e i ≤ i)
    (h010 : ¬ InvSeqContainsPattern e ![0, 1, 0])
    (h021 : ¬ InvSeqContainsPattern e ![0, 2, 1]) : Monotone e := by
  apply monotone_iff_forall_lt.mpr
  intro i j hij
  by_contra! h
  let z : Fin n := ⟨0, by omega⟩
  have hz : e z = 0 := Nat.eq_zero_of_le_zero (he z)
  have hzi : z < i := (Nat.zero_lt_of_lt h).trans_le (he i)
  by_cases hzero : e j = 0
  · apply h010 ((invSeqContainsPattern_iff_exists_indices e _).2 ⟨z, i, j, hzi, hij, ?_⟩)
    simp [invSeqPatternSameOrder_iff, hz, hzero] at h ⊢
    omega
  · apply h021 ((invSeqContainsPattern_iff_exists_indices e _).2 ⟨z, i, j, hzi, hij, ?_⟩)
    simp [invSeqPatternSameOrder_iff, hz]
    omega

end InversionSequencePatternReductions

open InversionSequencePatternReductions in
/-- **Reducible sets of length-3 patterns for inversion sequences.** An inversion sequence of
length $n$ is a sequence $e_0 e_1 \cdots e_{n-1}$ of natural numbers with $e_i \le i$ for all $i$;
write a length-3 pattern as a digit string ($101$ is the pattern $(1, 0, 1)$). For each pair
$(C, \tau)$ listed below and every $n$, every inversion sequence of length $n$ that avoids every
pattern in $C$ also avoids $\tau$, so $C \cup \{\tau\}$ and $C$ are avoided by the same inversion
sequences. The pairs are: $C = \{001\}$ with $\tau \in \{101, 102, 201\}$;
$C = \{011\}$ with $\tau \in \{101, 110\}$; $C = \{012\}$ with $\tau \in \{102, 120\}$;
$C = \{021\}$ with $\tau \in \{201, 210\}$; $C = \{000, 001\}$ with $\tau = 100$;
$C = \{000, 011\}$ with $\tau \in \{100, 201, 210\}$;
$C = \{000, 012\}$ with $\tau \in \{201, 210\}$; $C = \{000, 021\}$ with $\tau = 100$;
$C = \{001, 010\}$ with $\tau \in \{021, 100, 110, 120, 210\}$;
$C = \{001, 011\}$ with $\tau = 021$; $C = \{001, 012\}$ with $\tau = 021$;
$C = \{001, 110\}$ with $\tau = 210$; $C = \{001, 120\}$ with $\tau = 210$;
$C = \{010, 011\}$ with $\tau = 100$; $C = \{010, 012\}$ with $\tau \in \{101, 201\}$;
$C = \{010, 021\}$ with $\tau \in \{100, 101, 102, 110, 120\}$;
$C = \{001, 011, 012\}$ with $\tau = 210$; $C = \{001, 011, 100\}$ with $\tau = 210$; and
$C = \{001, 012, 100\}$ with $\tau = 210$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 2 (`integers-2024-A76-thm-2`). -/
public theorem invSeq_reducible_pattern_sets :
    ∀ Cτ ∈ ([(({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 2, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 2, 1]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 0, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![1, 1, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![1, 2, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 1, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 1, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 0, 1], ![0, 1, 1], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 1], ![1, 0, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 2], ![1, 0, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0])]
      : List (Set (Fin 3 → ℕ) × (Fin 3 → ℕ))),
      ∀ (n : ℕ) (e : Fin n → ℕ), (∀ i, e i ≤ i) → (∀ p ∈ Cτ.1, ¬ InvSeqContainsPattern e p) →
        ¬ InvSeqContainsPattern e Cτ.2 := by
  intro Cτ hrow n e he havoid hcontains
  obtain ⟨i, j, k, hij, hjk, hs⟩ := (invSeqContainsPattern_iff_exists_indices e _).mp hcontains
  let z : Fin n := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
  have hz : e z = 0 := Nat.eq_zero_of_le_zero (he z)
  have zero_lt_of_pos {a : Fin n} (ha : 0 < e a) : z < a := ha.trans_le (he a)
  have ht (p : Fin 3 → ℕ) (hp : p ∈ Cτ.1) {a b c : Fin n} (hab : a < b) (hbc : b < c) :
      ¬ InvSeqPatternSameOrder (e a) (e b) (e c) p := fun h =>
    havoid p hp ((invSeqContainsPattern_iff_exists_indices e p).mpr ⟨a, b, c, hab, hbc, h⟩)
  have earlier (hp : ![0, 0, 1] ∈ Cτ.1) {b : Fin n} {r : ℕ} (hr : r < e b) :=
    initial_value he (havoid _ hp) r hr
  have low_middle (hp : ![0, 0, 1] ∈ Cτ.1) (hji : e j < e i) (hjk' : e j < e k) : False := by
    obtain ⟨a, -, hai, ha⟩ := earlier hp hji
    apply ht _ hp (hai.trans hij) hjk
    simp [invSeqPatternSameOrder_iff, ha, hjk', hjk'.le]
  -- A 021 under 001-avoidance has another copy of the last value between its first two indices.
  have middle_copy (hp : ![0, 0, 1] ∈ Cτ.1) (hik : e i < e k) (hkj : e k < e j) :
      ∃ b : Fin n, i < b ∧ b < j ∧ e b = e k := by
    obtain ⟨a, hval, -, ha⟩ := earlier hp (hik.trans hkj)
    have hi := he i
    have hia : (i : ℕ) ≤ a := by
      by_contra! h
      apply ht _ hp (show a < i from h) hij
      have hlt := hik.trans hkj
      simp [invSeqPatternSameOrder_iff, ha, hlt, hlt.le]
    obtain ⟨b, hb, hbj, hbe⟩ := earlier hp hkj
    exact ⟨b, show (i : ℕ) < b by omega, hbj, hbe⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [invSeqPatternSameOrder_iff] at hs
  -- 001 excludes 101, 102 and 201: in each the middle value is the least.
  · exact low_middle (by simp) (by omega) (by omega)
  · exact low_middle (by simp) (by omega) (by omega)
  · exact low_middle (by simp) (by omega) (by omega)
  -- In the single-pattern reductions not using 001, prepend the initial zero.
  · apply ht ![0, 1, 1] (by simp) (zero_lt_of_pos (a := i) (by omega)) (hij.trans hjk)
    simp [invSeqPatternSameOrder_iff, hz]; omega
  · apply ht ![0, 1, 1] (by simp) (zero_lt_of_pos (a := i) (by omega)) hij
    simp [invSeqPatternSameOrder_iff, hz]; omega
  · apply ht ![0, 1, 2] (by simp) (zero_lt_of_pos (a := i) (by omega)) (hij.trans hjk)
    simp [invSeqPatternSameOrder_iff, hz]; omega
  · apply ht ![0, 1, 2] (by simp) (zero_lt_of_pos (a := i) (by omega)) hij
    simp [invSeqPatternSameOrder_iff, hz]; omega
  · apply ht ![0, 2, 1] (by simp) (zero_lt_of_pos (a := i) (by omega)) (hij.trans hjk)
    simp [invSeqPatternSameOrder_iff, hz]; omega
  · apply ht ![0, 2, 1] (by simp) (zero_lt_of_pos (a := i) (by omega)) hij
    simp [invSeqPatternSameOrder_iff, hz]; omega
  -- 000, with 001, 011, 012 or 021 as appropriate.
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e j < e i by omega)
    apply ht ![0, 0, 0] (by simp) (hai.trans hij) hjk
    simp [invSeqPatternSameOrder_iff, ha]; omega
  · by_cases h : e j = 0
    · apply ht ![0, 0, 0] (by simp) (zero_lt_of_pos (a := i) (by omega) |>.trans hij) hjk
      simp [invSeqPatternSameOrder_iff, hz, h]; omega
    · apply ht ![0, 1, 1] (by simp) (zero_lt_of_pos (a := j) (by omega)) hjk
      simp [invSeqPatternSameOrder_iff, hz]; omega
  · exact not_two_smaller_of_avoid000_011 he (havoid _ (by simp)) (havoid _ (by simp))
      hij hjk (by omega) (by omega)
  · exact not_two_smaller_of_avoid000_011 he (havoid _ (by simp)) (havoid _ (by simp))
      hij hjk (by omega) (by omega)
  · exact not_two_distinct_smaller_of_avoid000_012 he (havoid _ (by simp)) (havoid _ (by simp))
      hij hjk (by omega) (by omega) (by omega)
  · exact not_two_distinct_smaller_of_avoid000_012 he (havoid _ (by simp)) (havoid _ (by simp))
      hij hjk (by omega) (by omega) (by omega)
  · have hzi := zero_lt_of_pos (a := i) (by omega)
    by_cases h : e j = 0
    · apply ht ![0, 0, 0] (by simp) (hzi.trans hij) hjk
      simp [invSeqPatternSameOrder_iff, hz, h]; omega
    · apply ht ![0, 2, 1] (by simp) hzi hij
      simp [invSeqPatternSameOrder_iff, hz]; omega
  -- With 001 and 010, a repeated smaller value on either side of a larger one is impossible.
  · obtain ⟨a, -, haj, ha⟩ := earlier (by simp) (show e k < e j by omega)
    apply ht ![0, 1, 0] (by simp) haj hjk
    simp [invSeqPatternSameOrder_iff, ha]; omega
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e j < e i by omega)
    apply ht ![0, 1, 0] (by simp) hai hij
    simp [invSeqPatternSameOrder_iff, ha]; omega
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e k < e i by omega)
    apply ht ![0, 1, 0] (by simp) hai (hij.trans hjk)
    simp [invSeqPatternSameOrder_iff, ha]; omega
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e k < e i by omega)
    apply ht ![0, 1, 0] (by simp) hai (hij.trans hjk)
    simp [invSeqPatternSameOrder_iff, ha]; omega
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e k < e i by omega)
    apply ht ![0, 1, 0] (by simp) hai (hij.trans hjk)
    simp [invSeqPatternSameOrder_iff, ha]; omega
  · obtain ⟨b, hib, hbj, hb⟩ := middle_copy (by simp) (by omega) (by omega)
    apply ht ![0, 1, 1] (by simp) hib (hbj.trans hjk)
    simp [invSeqPatternSameOrder_iff, hb]; omega
  · obtain ⟨b, hib, hbj, hb⟩ := middle_copy (by simp) (by omega) (by omega)
    apply ht ![0, 1, 2] (by simp) hib hbj
    simp [invSeqPatternSameOrder_iff, hb]; omega
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e j < e i by omega)
    apply ht ![1, 1, 0] (by simp) (hai.trans hij) hjk
    simp [invSeqPatternSameOrder_iff, ha]; omega
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e j < e i by omega)
    apply ht ![1, 2, 0] (by simp) hai (hij.trans hjk)
    simp [invSeqPatternSameOrder_iff, ha]; omega
  -- When the middle value is zero, 010 is present; otherwise prepend zero to the last pair.
  · by_cases h : e j = 0
    · apply ht ![0, 1, 0] (by simp) (zero_lt_of_pos (a := i) (by omega)) hij
      simp [invSeqPatternSameOrder_iff, hz, h]; omega
    · apply ht ![0, 1, 1] (by simp) (zero_lt_of_pos (a := j) (by omega)) hjk
      simp [invSeqPatternSameOrder_iff, hz]; omega
  · by_cases h : e j = 0
    · apply ht ![0, 1, 0] (by simp) (zero_lt_of_pos (a := i) (by omega)) hij
      simp [invSeqPatternSameOrder_iff, hz, h]; omega
    · apply ht ![0, 1, 2] (by simp) (zero_lt_of_pos (a := j) (by omega)) hjk
      simp [invSeqPatternSameOrder_iff, hz]; omega
  · by_cases h : e j = 0
    · apply ht ![0, 1, 0] (by simp) (zero_lt_of_pos (a := i) (by omega)) hij
      simp [invSeqPatternSameOrder_iff, hz, h]; omega
    · apply ht ![0, 1, 2] (by simp) (zero_lt_of_pos (a := j) (by omega)) hjk
      simp [invSeqPatternSameOrder_iff, hz]; omega
  -- Every added pattern in these five rows has a descent.
  · have hm := monotone_of_avoid010_021 he (havoid _ (by simp)) (havoid _ (by simp))
    exact (not_lt_of_ge (hm hij.le)) (by omega)
  · have hm := monotone_of_avoid010_021 he (havoid _ (by simp)) (havoid _ (by simp))
    exact (not_lt_of_ge (hm hij.le)) (by omega)
  · have hm := monotone_of_avoid010_021 he (havoid _ (by simp)) (havoid _ (by simp))
    exact (not_lt_of_ge (hm hij.le)) (by omega)
  · have hm := monotone_of_avoid010_021 he (havoid _ (by simp)) (havoid _ (by simp))
    exact (not_lt_of_ge (hm hjk.le)) (by omega)
  · have hm := monotone_of_avoid010_021 he (havoid _ (by simp)) (havoid _ (by simp))
    exact (not_lt_of_ge (hm hjk.le)) (by omega)
  -- The smaller positive entry of a 210 has an earlier copy, yielding 011 or 012.
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e j < e i by omega)
    apply ht ![0, 1, 1] (by simp) (zero_lt_of_pos (a := a) (by omega)) (hai.trans hij)
    simp [invSeqPatternSameOrder_iff, hz, ha]; omega
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e j < e i by omega)
    apply ht ![0, 1, 1] (by simp) (zero_lt_of_pos (a := a) (by omega)) (hai.trans hij)
    simp [invSeqPatternSameOrder_iff, hz, ha]; omega
  · obtain ⟨a, -, hai, ha⟩ := earlier (by simp) (show e j < e i by omega)
    apply ht ![0, 1, 2] (by simp) (zero_lt_of_pos (a := a) (by omega)) hai
    simp [invSeqPatternSameOrder_iff, hz, ha]; omega

end MetaMathlibExt

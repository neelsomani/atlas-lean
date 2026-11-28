/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

/-!
# Peakless-tieless parking functions by last entry

For `1 ≤ i ≤ n`, the number of length-`n` parking functions with no peaks or ties and
last preference `i` is the corresponding Catalan-triangle entry. To shorten a word of length
at least two, delete its first entry if it is the largest allowed preference, and otherwise
delete its last entry. The two inverse operations give the Catalan-triangle row recurrence.

## References

* Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
  Alex Moon, John O. Museus, and Eric Redmon, *On Some Discrete Statistics of Parking Functions*,
  Journal of Integer Sequences 27 (2024), Article 24.8.6, pp. 1–34, Corollary 32 and equation (12).
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
/-- `w` has no ties. -/
local notation "NoTies" w:max => ∀ i j, j.val = i.val + 1 → w i ≠ w j

set_option quotPrecheck false in
/-- `w` has no peaks. -/
local notation "NoPeaks" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w i < w j ∧ w k < w j)

set_option quotPrecheck false in
/-- The peakless-tieless parking functions `PTPF_n`. -/
local notation "ptpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ (NoTies f) ∧ NoPeaks f)
    Finset.univ

namespace ParkingFunctionLastEntry

open Finset

variable {n : ℕ}

-- If the right endpoint of a subinterval exceeds the last entry of the word, its left
-- endpoint must be even larger: otherwise an interval maximum would be an interior peak.
private lemma lt_left_of_last_lt {f : Fin (n + 1) → Fin (n + 1)}
    (ht : NoTies f) (hp : NoPeaks f) {i j : Fin (n + 1)} (hij : i < j)
    (hj : f (Fin.last n) < f j) : f j < f i := by
  by_contra! hi
  let s := Ioc i (Fin.last n)
  have hjs : j ∈ s := mem_Ioc.mpr ⟨hij, Fin.le_last j⟩
  obtain ⟨p, hps, hmax⟩ := exists_max_image s f ⟨j, hjs⟩
  have hip := (mem_Ioc.mp hps).1
  have hlast := hj.trans_le (hmax j hjs)
  have hpn : p.val < n := by
    have hne : p ≠ Fin.last n := fun he => by simp [he] at hlast
    exact (Fin.lt_def.mp ((Fin.le_last p).lt_of_ne hne))
  let l : Fin (n + 1) := ⟨p.val - 1, by have := p.isLt; omega⟩
  let r : Fin (n + 1) := ⟨p.val + 1, by omega⟩
  have hl : p.val = l.val + 1 := by simp only [l, Fin.lt_def] at hip ⊢; omega
  have hrl : r ∈ s := mem_Ioc.mpr ⟨by simpa only [r, Fin.lt_def] using Nat.lt_succ_of_lt hip,
    Fin.le_last r⟩
  have hll : f l ≤ f p := by
    by_cases he : l = i
    · exact he ▸ hi.trans (hmax j hjs)
    · apply hmax
      refine mem_Ioc.mpr ⟨?_, Fin.le_last l⟩
      have hv : l.val ≠ i.val := fun h => he (Fin.ext h)
      simp only [Fin.lt_def] at hip ⊢
      omega
  exact hp l p r hl rfl ⟨hll.lt_of_ne (ht l p hl), (hmax r hrl).lt_of_ne (ht p r rfl).symm⟩

-- The lower-tail bound at the penultimate preference leaves room for at most one top entry.
private lemma top_unique {f : Fin (n + 2) → Fin (n + 2)} (hf : IsParkingFunction (n + 2) f)
    {i j : Fin (n + 2)} (hi : f i = Fin.last (n + 1)) (hj : f j = Fin.last (n + 1)) : i = j := by
  let k := (Fin.last n).castSucc
  have h : n + 1 ≤ (univ.filter fun i => f i ≤ k).card :=
    (isParkingFunction_iff_card_filter_le _ _).mp hf k
  have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin (n + 2))))
    (fun i => f i ≤ k)
  simp only [not_le, card_univ, Fintype.card_fin] at hc
  have hb : (univ.filter fun p => k < f p).card ≤ 1 := by omega
  apply card_le_one_iff.mp hb
  · simp [hi, k, Fin.lt_def]
  · simp [hj, k, Fin.lt_def]

private lemma last_ascent {f : Fin (n + 2) → Fin (n + 2)} (ht : NoTies f) (hp : NoPeaks f)
    (hfirst : f 0 ≠ Fin.last (n + 1)) : f (Fin.last n).castSucc < f (Fin.last (n + 1)) := by
  let penult := (Fin.last n).castSucc
  let last := Fin.last (n + 1)
  rcases lt_or_gt_of_ne (ht penult last rfl) with ha | hd
  · exact ha
  have hlast (p : Fin (n + 2)) (hpl : p < last) : f last < f p := by
    by_cases he : p = penult
    · simpa only [he] using hd
    have hpp : p < penult := by
      have hn : p.val ≠ penult.val := fun h => he (Fin.ext h)
      simp only [Fin.lt_def, penult, last, Fin.val_castSucc, Fin.val_last] at hpl hn ⊢
      omega
    exact hd.trans (lt_left_of_last_lt ht hp hpp hd)
  have hanti : StrictAnti f := by
    intro i j hij
    rcases (Fin.le_last j).lt_or_eq with hj | rfl
    · exact lt_left_of_last_lt ht hp hij (hlast j hj)
    · exact hlast i hij
  obtain ⟨j, hj⟩ := Finite.surjective_of_injective hanti.injective last
  have hle := hanti.antitone (Fin.zero_le j)
  rw [hj] at hle
  exact (hfirst (le_antisymm (Fin.le_last _) hle)).elim

private abbrev prependTop (f : Fin (n + 1) → Fin (n + 1)) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cons (Fin.last (n + 1)) (Fin.castSucc ∘ f)

private abbrev appendEntry (f : Fin (n + 1) → Fin (n + 1)) (a : Fin (n + 2)) :
    Fin (n + 2) → Fin (n + 2) :=
  Fin.snoc (Fin.castSucc ∘ f) a

private lemma prependTop_mem_iff {f : Fin (n + 1) → Fin (n + 1)} :
    prependTop f ∈ ptpfSet (n + 2) ↔ f ∈ ptpfSet (n + 1) := by
  simp only [mem_filter, mem_univ, true_and, isParkingFunction_iff_card_filter_le]
  have hcount (k : Fin (n + 1)) :
      (univ.filter fun i => prependTop f i ≤ k.castSucc).card =
        (univ.filter fun i => f i ≤ k).card := by
    rw [Fin.card_filter_univ_succ']
    have hk : ¬ Fin.last (n + 1) ≤ k.castSucc := (Fin.castSucc_lt_last k).not_ge
    simp only [prependTop, Fin.cons_zero, Fin.cons_succ, Function.comp_apply,
      Fin.castSucc_le_castSucc_iff, ite_eq_right hk, zero_add]
  constructor
  · rintro ⟨hpark, ht, hp⟩
    refine ⟨fun k => ?_, fun i j hij => ?_, fun i j k hij hjk h => ?_⟩
    · simpa only [hcount, Fin.val_castSucc] using hpark k.castSucc
    · intro h
      exact ht i.succ j.succ (by simpa using congrArg Nat.succ hij) (by simp [prependTop, h])
    · exact hp i.succ j.succ k.succ (by simpa using congrArg Nat.succ hij)
        (by simpa using congrArg Nat.succ hjk) (by simpa [prependTop] using h)
  · rintro ⟨hpark, ht, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k
      refine Fin.lastCases ?_ (fun t => ?_) k
      · simp [Fin.le_last]
      · simpa only [hcount, Fin.val_castSucc] using hpark t
    · intro i j hij
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (show j ≠ 0 from by
        intro h; simp [h] at hij)
      revert hij
      refine Fin.cases (fun _ => ?_) (fun t hij => ?_) i
      · simpa only [prependTop, Fin.cons_zero, Fin.cons_succ, Function.comp_apply] using
          (Fin.castSucc_lt_last (f j)).ne'
      · exact fun h => ht t j (by simp only [Fin.val_succ] at hij; omega)
          (by simpa [prependTop] using h)
    · intro i j k hij hjk h
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (show j ≠ 0 from by
        intro he; simp [he] at hij)
      obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr (show k ≠ 0 from by
        intro he; simp [he] at hjk)
      revert hij h
      refine Fin.cases (fun _ h => ?_) (fun t hij h => ?_) i
      · exact (not_lt_of_ge (Fin.le_last _)) h.1
      · have htj : j.val = t.val + 1 := by simp only [Fin.val_succ] at hij; omega
        have hjk' : k.val = j.val + 1 := by simp only [Fin.val_succ] at hjk; omega
        exact hp t j k htj hjk' (by simpa [prependTop] using h)

private lemma appendEntry_mem_iff {f : Fin (n + 1) → Fin (n + 1)} {a : Fin (n + 2)}
    (ha : (f (Fin.last n)).castSucc < a) :
    appendEntry f a ∈ ptpfSet (n + 2) ↔ f ∈ ptpfSet (n + 1) := by
  let g := appendEntry f a
  change g ∈ ptpfSet (n + 2) ↔ _
  simp only [mem_filter, mem_univ, true_and, isParkingFunction_iff_card_filter_le]
  have hcount (k : Fin (n + 1)) :
      (univ.filter fun i => g i ≤ k.castSucc).card =
        (univ.filter fun i => f i ≤ k).card + if a ≤ k.castSucc then 1 else 0 := by
    conv_lhs => rw [Fin.univ_castSuccEmb (n + 1), filter_cons, apply_ite Finset.card,
      card_cons, filter_map, card_map]
    simp only [g, appendEntry, Fin.snoc_last, Function.comp_apply, Fin.castSuccEmb_apply,
      Fin.snoc_castSucc, Fin.castSucc_le_castSucc_iff]
    split <;> simp
  constructor
  · rintro ⟨hpark, ht, hp⟩
    refine ⟨?_, fun i j hij => ?_, fun i j k hij hjk h => ?_⟩
    · intro k
      by_cases hk : a ≤ k.castSucc
      · -- Above this threshold, the entries of the shorter word are distinct.
        have hanti : StrictAntiOn f (↑(univ.filter fun i => k < f i) : Set (Fin (n + 1))) := by
          intro i _ j hj hij
          have hkj : k < f j := (mem_filter.mp (mem_coe.mp hj)).2
          have hj' : g (Fin.last (n + 1)) < g j.castSucc := by
            simpa only [g, appendEntry, Fin.snoc_last, Fin.snoc_castSucc, Function.comp_apply]
              using hk.trans_lt (Fin.castSucc_lt_castSucc_iff.mpr hkj)
          simpa [g, appendEntry] using
            lt_left_of_last_lt ht hp (Fin.castSucc_lt_castSucc_iff.mpr hij) hj'
        have habove : (univ.filter (fun i => k < f i)).card ≤ (Ioi k).card :=
          card_le_card_of_injOn f (fun _ hi => mem_coe.mpr (mem_Ioi.mpr (mem_filter.mp
            (mem_coe.mp hi)).2)) hanti.injOn
        have hpartition := card_filter_add_card_filter_not (s := (univ : Finset (Fin (n + 1))))
          (fun i => f i ≤ k)
        simp only [not_le, card_univ, Fintype.card_fin] at hpartition
        rw [Fin.card_Ioi] at habove
        omega
      · simpa only [hcount, ite_eq_right hk, Nat.add_zero, Fin.val_castSucc] using hpark k.castSucc
    · intro h
      exact ht i.castSucc j.castSucc hij (by simp [g, appendEntry, h])
    · exact hp i.castSucc j.castSucc k.castSucc hij hjk (by simpa [g, appendEntry] using h)
  · rintro ⟨hpark, ht, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k
      refine Fin.lastCases ?_ (fun t => ?_) k
      · simp [Fin.le_last]
      · rw [hcount, Fin.val_castSucc]
        exact (hpark t).trans (Nat.le_add_right _ _)
    · intro i j hij
      revert hij
      refine Fin.lastCases (fun hij => ?_) (fun j hij => ?_) j
      · have he : i = (Fin.last n).castSucc := Fin.ext (by simp at hij ⊢; omega)
        simpa [he, g, appendEntry] using ha.ne
      · revert hij
        refine Fin.lastCases (fun hij => ?_) (fun i hij => ?_) i
        · simp at hij
          omega
        · simpa [g, appendEntry] using ht i j hij
    · intro i j k hij hjk h
      revert hjk h
      refine Fin.lastCases (fun hjk h => ?_) (fun k hjk h => ?_) k
      · have he : j = (Fin.last n).castSucc := Fin.ext (by simp at hjk ⊢; omega)
        exact ha.not_gt (by simpa [he, g, appendEntry] using h.2)
      · revert hij hjk h
        refine Fin.lastCases (fun _ hjk _ => ?_) (fun j hij hjk h => ?_) j
        · simp at hjk
          omega
        · revert hij h
          refine Fin.lastCases (fun hij _ => ?_) (fun i hij h => ?_) i
          · simp at hij
            omega
          · exact hp i j k hij hjk (by simpa [g, appendEntry] using h)

private def ending (n k : ℕ) : Finset (Fin (n + 1) → Fin (n + 1)) :=
  (ptpfSet (n + 1)).filter fun f => (f (Fin.last n)).val = k

private lemma card_ending_succ (a : Fin (n + 2)) :
    (ending (n + 1) a.val).card = ∑ k ∈ range (a.val + 1), (ending n k).card := by
  let s := (ptpfSet (n + 1)).filter fun f => (f (Fin.last n)).castSucc ≤ a
  have hs : s.card = ∑ k ∈ range (a.val + 1), (ending n k).card := by
    rw [card_eq_sum_card_fiberwise (s := s) (f := fun f => (f (Fin.last n)).val)
      (t := range (a.val + 1)) (fun f hf => mem_coe.mpr (mem_range.mpr
        (Nat.lt_succ_of_le (mem_filter.mp (mem_coe.mp hf)).2)))]
    apply sum_congr rfl
    intro k hk
    congr 1
    ext f
    simp only [s, ending, mem_filter, Fin.le_iff_val_le_val, Fin.val_castSucc]
    refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
    rw [h.2]
    exact Nat.le_of_lt_succ (mem_range.mp hk)
  rw [← hs]
  symm
  let grow (f : Fin (n + 1) → Fin (n + 1)) :=
    if (f (Fin.last n)).castSucc = a then prependTop f else appendEntry f a
  refine card_bij (fun f _ => grow f) ?_ ?_ ?_
  · intro f hf
    obtain ⟨hf, hfa⟩ := mem_filter.mp hf
    by_cases h : (f (Fin.last n)).castSucc = a
    · refine mem_filter.mpr ⟨?_, ?_⟩
      · simpa only [grow, ite_eq_left h] using prependTop_mem_iff.mpr hf
      · simp [grow, ← h, prependTop]
    · refine mem_filter.mpr ⟨?_, by simp [grow, h, appendEntry]⟩
      simpa only [grow, ite_eq_right h] using (appendEntry_mem_iff (hfa.lt_of_ne h)).mpr hf
  · intro f hf g hg he
    by_cases h : (f (Fin.last n)).castSucc = a <;>
      by_cases h' : (g (Fin.last n)).castSucc = a
    · funext i
      have hi := congrFun he i.succ
      simpa [grow, h, h', prependTop] using hi
    · have hzero : Fin.last (n + 1) = (g 0).castSucc := by
        simpa [grow, h, h', prependTop, appendEntry] using congrFun he 0
      exact ((Fin.castSucc_lt_last _).ne hzero.symm).elim
    · have hzero : (f 0).castSucc = Fin.last (n + 1) := by
        simpa [grow, h, h', prependTop, appendEntry] using congrFun he 0
      exact ((Fin.castSucc_lt_last _).ne hzero).elim
    · funext i
      have hi := congrFun he i.castSucc
      simpa [grow, h, h', appendEntry] using hi
  · intro g hg
    obtain ⟨hgood, hlast⟩ := mem_filter.mp hg
    have hlast : g (Fin.last (n + 1)) = a := Fin.ext hlast
    obtain ⟨hpark, ht, hp⟩ := by simpa only [mem_filter, mem_univ, true_and] using hgood
    by_cases hfirst : g 0 = Fin.last (n + 1)
    · have hb (i : Fin (n + 1)) : (g i.succ).val < n + 1 := by
        have hn : g i.succ ≠ Fin.last (n + 1) := fun he =>
          Fin.succ_ne_zero i (top_unique hpark he hfirst)
        exact (Fin.le_last _).lt_of_ne hn
      let f (i : Fin (n + 1)) : Fin (n + 1) := ⟨(g i.succ).val, hb i⟩
      have he : prependTop f = g := by
        funext i
        refine Fin.cases hfirst.symm (fun j => ?_) i
        simp [prependTop, f]
      have hf : (f (Fin.last n)).castSucc = a := by
        simpa [prependTop, ← Fin.succ_last] using (congrFun he (Fin.last (n + 1))).trans hlast
      exact ⟨f, mem_filter.mpr ⟨prependTop_mem_iff.mp (he.symm ▸ hgood), hf.le⟩,
        by simpa only [grow, ite_eq_left hf] using he⟩
    · have hb (i : Fin (n + 1)) : (g i.castSucc).val < n + 1 := by
        apply (Fin.le_last _).lt_of_ne
        intro he
        by_cases h : a = Fin.last (n + 1)
        · have hi := top_unique hpark he (hlast.trans h)
          exact Fin.castSucc_ne_last i hi
        · have h0 : (0 : Fin (n + 2)) < i.castSucc := by
            apply (Fin.zero_le _).lt_of_ne
            intro hz
            exact hfirst (hz ▸ he)
          have ha : g (Fin.last (n + 1)) < g i.castSucc := by
            rw [hlast, he]
            exact (Fin.le_last _).lt_of_ne h
          exact (not_lt_of_ge (Fin.le_last (g 0))) (he ▸ lt_left_of_last_lt ht hp h0 ha)
      let f (i : Fin (n + 1)) : Fin (n + 1) := ⟨(g i.castSucc).val, hb i⟩
      have he : appendEntry f a = g := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [appendEntry, Fin.snoc_last] using hlast.symm
        · simp [appendEntry, f]
      have hf : (f (Fin.last n)).castSucc < a := by
        have ha := last_ascent ht hp hfirst
        rwa [← he, appendEntry, Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply] at ha
      exact ⟨f, mem_filter.mpr ⟨(appendEntry_mem_iff hf).mp (he.symm ▸ hgood), hf.le⟩,
        by simpa only [grow, ite_eq_right hf.ne] using he⟩

private def ballot (n k : ℕ) : ℚ := ((n + k).choose n : ℚ) - (n + k).choose (n + 1)

private lemma sum_ballot (n k : ℕ) : ∑ j ∈ range (k + 1), ballot n j = ballot (n + 1) k := by
  have h₁ : (∑ j ∈ range (k + 1), (n + j).choose n) = (n + 1 + k).choose (n + 1) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.sum_range_add_choose k n
  have h₂ : (∑ j ∈ range (k + 1), (n + j).choose (n + 1)) = (n + 1 + k).choose (n + 2) := by
    cases k with
    | zero => simp
    | succ k =>
      rw [sum_range_succ']
      simp only [Nat.choose_succ_self, add_zero]
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.sum_range_add_choose k (n + 1)
  simp only [ballot, sum_sub_distrib, ← Nat.cast_sum, h₁, h₂]

private lemma card_ending_eq_ballot (n k : ℕ) (hk : k ≤ n) :
    ((ending n k).card : ℚ) = ballot n k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    have hc : (ending 0 0).card = 1 := by decide
    simp [hc, ballot]
  | succ n ih =>
    rw [card_ending_succ (⟨k, by omega⟩ : Fin (n + 2)), Nat.cast_sum, ← sum_ballot]
    apply sum_congr rfl
    intro j hj
    by_cases hjn : j ≤ n
    · exact ih j hjn
    have he : j = n + 1 := by have := mem_range.mp hj; omega
    subst j
    have hempty : ending n (n + 1) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro f _ hf
      exact (f (Fin.last n)).isLt.ne hf
    have hsymm : (n + (n + 1)).choose (n + 1) = (n + (n + 1)).choose n :=
      Nat.choose_symm_add.symm
    simp [hempty, ballot, hsymm]

private lemma ballot_eq (n k : ℕ) (hk : k ≤ n) :
    ballot n k = ((n + k).choose k : ℚ) * ((n + 1 - k : ℕ) : ℚ) / (n + 1) := by
  have hsymm : (n + k).choose n = (n + k).choose k := Nat.choose_symm_add
  have hchoose := Nat.choose_succ_right_eq (n + k) n
  have hchoose' : ((n + k).choose (n + 1) : ℚ) * (n + 1) = ((n + k).choose n : ℚ) * k := by
    exact_mod_cast (by simpa only [Nat.add_sub_cancel_left] using hchoose :
      (n + k).choose (n + 1) * (n + 1) = (n + k).choose n * k)
  rw [ballot, ← hsymm, eq_div_iff (by positivity), sub_mul, hchoose',
    Nat.cast_sub (by omega)]
  push_cast
  ring

end ParkingFunctionLastEntry

/-- **Peakless-tieless parking functions by last entry.** Write a parking function $f$ of length
$n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1 \in \{1, \dots, n\}$. It is
peakless-tieless if there is no $j$ with $a_{j-1} < a_j > a_{j+1}$ (a peak) and no $j$ with
$a_j = a_{j+1}$ (a tie). For natural numbers $i$ and $n$ with $1 \le i \le n$, the number of
peakless-tieless parking functions of length $n$ with last entry $a_n = i$ is
$$\binom{n+i-2}{i-1} \cdot \frac{n-i+1}{n}.$$

This is the Catalan-triangle entry $T(n-1, i-1)$ of OEIS A009766.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 32
(`jis-2024-24.8.6-cor-32`). -/
public theorem card_peakless_tieless_parkingFunction_last (n i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    ((((ptpfSet n).filter (fun f => ∀ j : Fin n, j.val + 1 = n → (f j : ℕ) + 1 = i)).card :
      ℕ) : ℚ) = ((n + i - 2).choose (i - 1) : ℚ) * ((n - i + 1 : ℕ) : ℚ) / n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have he : (ptpfSet (m + 1)).filter
      (fun f => ∀ j : Fin (m + 1), j.val + 1 = m + 1 → (f j : ℕ) + 1 = k + 1) =
        ParkingFunctionLastEntry.ending m k := by
    ext f
    simp only [ParkingFunctionLastEntry.ending, Finset.mem_filter]
    refine and_congr_right fun _ => ⟨fun h => Nat.succ.inj (h (Fin.last m) rfl), ?_⟩
    intro h j hj
    have hj' : j = Fin.last m := Fin.ext (Nat.succ.inj hj)
    simp only [hj', h]
  rw [he, ParkingFunctionLastEntry.card_ending_eq_ballot m k (by omega),
    ParkingFunctionLastEntry.ballot_eq m k (by omega)]
  rw [show m + 1 + (k + 1) - 2 = m + k by omega,
    show k + 1 - 1 = k by omega, show m + 1 - (k + 1) + 1 = m + 1 - k by omega, Nat.cast_add,
    Nat.cast_one]

end MetaMathlibExt

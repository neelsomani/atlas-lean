/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibExt.Combinatorics.Words.DumontThomasNumeration

namespace MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

private def letterMap : Bool → List Bool
  | false => [true, false]
  | true => [false, false]

private def path : ℕ → List Bool × Bool
  | 0 => ([], true)
  | _ + 1 => ([true], false)

private theorem letterMap_isSubstitution : IsSubstitution letterMap := by
  refine IsSubstitution.of_nonempty_images (a := false) (fun a => by cases a <;> decide)
    (Filter.tendsto_atTop_atTop.mpr ?_)
  intro n
  refine ⟨n, fun k hk => ?_⟩
  have hlen (a : Bool) : (letterMap a).length = 2 := by cases a <;> rfl
  simpa [morphIterate_length_of_uniform hlen] using hk.trans (Nat.lt_two_pow_self (n := k)).le

end MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

namespace MetaMathlibExt.substitutionAutomaton_admissibleSequence.Tests

open morphIterate_getElem_eq_substitutionAutomaton_tail

private theorem path_isLetterAdmissible : IsLetterAdmissibleSequence letterMap false path 1 := by
  refine IsLetterAdmissibleSequence.of_top_prefix
    (IsAdmissibleSequence.of_prefixes (fun i hi => ?_)) ⟨[], rfl⟩
  obtain rfl : i = 0 := by omega
  exact ⟨[false], rfl⟩

-- The first digit skips a block of length two. Reversing the digits selects a different letter.
example : (morphIterate letterMap 2 [false])[2]? =
    substitutionAutomaton letterMap false [1, 0] := by
  exact morphIterate_getElem_eq_substitutionAutomaton_tail
    letterMap letterMap_isSubstitution 2 (by decide) false path path_isLetterAdmissible

-- A single pair can have an empty word. Its digit still makes a transition.
example : substitutionAutomaton letterMap false [0] = some true := by
  have hadm : IsLetterAdmissibleSequence letterMap false path 0 :=
    IsLetterAdmissibleSequence.of_top_prefix (isAdmissibleSequence_zero _ _) ⟨[false], rfl⟩
  exact substitutionAutomaton_admissibleSequence
    letterMap letterMap_isSubstitution 1 (by decide) false path hadm 0 (by decide)

-- The first digit reaches the intermediate letter, and the next digit changes it.
example : substitutionAutomaton letterMap false [1] = some false ∧
    substitutionAutomaton letterMap false [1, 0] = some true := by
  have h := substitutionAutomaton_admissibleSequence
    letterMap letterMap_isSubstitution 2 (by decide) false path path_isLetterAdmissible
  exact ⟨h 1 (by decide), h 0 (by decide)⟩

end MetaMathlibExt.substitutionAutomaton_admissibleSequence.Tests

namespace MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

-- At depth zero the terminal word is unchanged and the only summand is `|m₀|`.
example : (∑ j ∈ Finset.range (0 + 1), (morphIterate letterMap j [true]).length) <
    (morphIterate letterMap 0 [true, false]).length :=
  admissibleSequence_weightedLength_lt letterMap letterMap_isSubstitution
    (fun _ => ([true], false)) 0 (isAdmissibleSequence_zero _ _)

-- Two transitions: `m₁a₁` is a full image, while `m₀a₀` is a proper prefix.
example : (∑ j ∈ Finset.range (2 + 1), (morphIterate letterMap j (path j).1).length) <
    (morphIterate letterMap 2 [true, false]).length := by
  apply admissibleSequence_weightedLength_lt letterMap letterMap_isSubstitution path 2
  refine IsAdmissibleSequence.of_prefixes (fun i hi => ?_)
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · exact ⟨[false], rfl⟩
  · exact ⟨[], rfl⟩

example : substitutionAutomaton letterMap false [1, 0] = some true ∧
    substitutionAutomaton letterMap false [0, 1] = some false ∧
    substitutionAutomaton letterMap false [1, 2] = none := by
  decide

end MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

namespace MetaMathlibExt.letterAdmissibleSequence_eq_of_weightedLength_eq.Tests

open morphIterate_getElem_eq_substitutionAutomaton_tail

private def onePair : ℕ → List Bool × Bool
  | 0 => ([true], false)
  | _ + 1 => ([], false)

private def onePair' : ℕ → List Bool × Bool := fun _ => ([true], false)

-- At depth zero the prefix is nonempty and the two tails need not agree.
example : onePair 0 = onePair' 0 ∧ onePair 1 ≠ onePair' 1 := by
  have hs : IsLetterAdmissibleSequence letterMap false onePair 0 :=
    IsLetterAdmissibleSequence.of_top_prefix (isAdmissibleSequence_zero _ _) ⟨[], rfl⟩
  have hs' : IsLetterAdmissibleSequence letterMap false onePair' 0 :=
    IsLetterAdmissibleSequence.of_top_prefix (isAdmissibleSequence_zero _ _) ⟨[], rfl⟩
  have hw : (∑ j ∈ Finset.range (0 + 1), (morphIterate letterMap j (onePair j).1).length) = 1 ∧
      (∑ j ∈ Finset.range (0 + 1), (morphIterate letterMap j (onePair' j).1).length) = 1 := by
    decide
  exact ⟨letterAdmissibleSequence_eq_of_weightedLength_eq letterMap letterMap_isSubstitution 0
    false onePair onePair' hs hs' (hw.1.trans hw.2.symm) 0 (by decide), by decide⟩

private def pathWithTail (i : ℕ) : List Bool × Bool :=
  if i ≤ 1 then path i else ([], false)

-- At depth one the top word has length one but contributes two to the weight.
-- The top letter is false; the lower letter is true. The second tail is different.
example : path 0 = pathWithTail 0 ∧ path 1 = pathWithTail 1 ∧ path 2 ≠ pathWithTail 2 := by
  have hs : IsLetterAdmissibleSequence letterMap false path 1 := by
    refine IsLetterAdmissibleSequence.of_top_prefix
      (IsAdmissibleSequence.of_prefixes (fun i hi => ?_)) ⟨[], rfl⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[false], rfl⟩
  have hs' : IsLetterAdmissibleSequence letterMap false pathWithTail 1 := by
    refine IsLetterAdmissibleSequence.of_top_prefix
      (IsAdmissibleSequence.of_prefixes (fun i hi => ?_)) ⟨[], rfl⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[false], rfl⟩
  have hw : (∑ j ∈ Finset.range (1 + 1), (morphIterate letterMap j (path j).1).length) = 2 ∧
      (∑ j ∈ Finset.range (1 + 1), (morphIterate letterMap j (pathWithTail j).1).length) = 2 := by
    decide
  have h := letterAdmissibleSequence_eq_of_weightedLength_eq (η := letterMap)
    (hη := letterMap_isSubstitution) (k := 1) (b := false) (s := path) (s' := pathWithTail)
    (hs := hs) (hs' := hs') (hsum := hw.1.trans hw.2.symm)
  exact ⟨h 0 (by decide), h 1 (by decide), by decide⟩

end MetaMathlibExt.letterAdmissibleSequence_eq_of_weightedLength_eq.Tests

namespace MetaMathlibExt.seedAutomaton_neutral_padding.Tests

private def double : Unit → List Unit := fun _ => [(), ()]

private theorem unitPoint : IsPeriodicPointWithGrowingSeed double (fun _ => ()) 1 := by
  have hgrow : Filter.Tendsto (fun k => (morphIterate double k [()]).length)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun n => ⟨n, fun k hk => ?_⟩
    have hlen (a : Unit) : (double a).length = 2 := rfl
    simpa [morphIterate_length_of_uniform hlen] using hk.trans (Nat.lt_two_pow_self (n := k)).le
  have hper : IsTwoSidedPeriodicPoint double (fun _ => ()) 1 :=
    IsTwoSidedPeriodicPoint.of_prefix_suffix le_rfl (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ _ _ => Subsingleton.elim _ _)
  refine IsPeriodicPointWithGrowingSeed.of_least_period
    (IsSubstitution.of_nonempty_images (fun _ => List.cons_ne_nil _ _) hgrow)
    hper ?_ hgrow hgrow
  intro q hq
  exact hq.one_le

-- Insert two padding blocks after either sign, keeping the nonempty suffix.
example : seedAutomaton double () () [0, 0, 0, 1] = some () ∧
    seedAutomaton double () () [1, 1, 1, 0] = some () := by
  have hzero := (seedAutomaton_neutral_padding (η := double) (u := fun _ => ())
    (p := 1) (hu := unitPoint) (v := [1]) (i := 2)).1 (by decide)
  have hone := (seedAutomaton_neutral_padding double (fun _ => ()) 1 unitPoint [0] 2).2
    (by decide)
  exact ⟨hzero.trans rfl, hone.trans rfl⟩

private def fibonacci (a : Fin 2) : List (Fin 2) := if a = 0 then [0, 1] else [0]

-- From the negative Fibonacci seed, two copies of `01` return to the seed; `10` is rejected.
example : lastLetterDigits fibonacci 2 1 = [0, 1] ∧
    seedAutomaton fibonacci 1 0 (1 :: ((List.replicate 2 (lastLetterDigits fibonacci 2 1)).flatten
      ++ [0])) = some 0 ∧
    seedAutomaton fibonacci 1 0 [1, 1, 0, 0] = none := by
  decide

end MetaMathlibExt.seedAutomaton_neutral_padding.Tests

namespace MetaMathlibExt.tail_injective_and_strictMono.Tests

open morphIterate_getElem_eq_substitutionAutomaton_tail
open substitutionAutomaton_admissibleSequence.Tests (path_isLetterAdmissible)

private def smallerTop : ℕ → List Bool × Bool
  | 0 => ([false], false)
  | _ + 1 => ([], true)

private def largerBottom : ℕ → List Bool × Bool := fun _ => ([true], false)

-- The top digit decides even though the bottom digits compare the other way.
example : ([0, 1] : List ℕ) < [1, 0] := by
  have hs : IsLetterAdmissibleSequence letterMap false smallerTop 1 := by
    refine IsLetterAdmissibleSequence.of_top_prefix
      (IsAdmissibleSequence.of_prefixes (fun i hi => ?_)) ⟨[false], rfl⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[], rfl⟩
  exact (tail_injective_and_strictMono letterMap letterMap_isSubstitution 2 (by decide)
    false smallerTop path hs path_isLetterAdmissible).2.mp (by decide)

-- With a shared top digit, the bottom digit breaks the tie: [1, 0] < [1, 1].
example : (∑ j ∈ Finset.range 2, (morphIterate letterMap j (path j).1).length) <
    ∑ j ∈ Finset.range 2, (morphIterate letterMap j (largerBottom j).1).length := by
  have hs : IsLetterAdmissibleSequence letterMap false largerBottom 1 :=
    IsLetterAdmissibleSequence.of_top_prefix
      (IsAdmissibleSequence.of_prefixes (fun _ _ => ⟨[], rfl⟩)) ⟨[], rfl⟩
  exact (tail_injective_and_strictMono letterMap letterMap_isSubstitution 2 (by decide)
    false path largerBottom path_isLetterAdmissible hs).2.mpr (by decide)

-- At depth one, equality of the retained digit determines the weight, not the unused pairs.
example : (∑ j ∈ Finset.range 1, (morphIterate letterMap j (path j).1).length) =
    ∑ j ∈ Finset.range 1, (morphIterate letterMap j (path 0).1).length := by
  have hs : IsLetterAdmissibleSequence letterMap false path 0 :=
    IsLetterAdmissibleSequence.of_top_prefix (isAdmissibleSequence_zero _ _) ⟨[false], rfl⟩
  have hs' : IsLetterAdmissibleSequence letterMap false (fun _ => path 0) 0 :=
    IsLetterAdmissibleSequence.of_top_prefix (isAdmissibleSequence_zero _ _) ⟨[false], rfl⟩
  exact (tail_injective_and_strictMono letterMap letterMap_isSubstitution 1 (by decide)
    false path (fun _ => path 0) hs hs').1.mpr rfl

end MetaMathlibExt.tail_injective_and_strictMono.Tests

namespace MetaMathlibExt.dumontThomasRep_quotient_remainder_pos.Tests

private def ternary (a : Bool) : List Bool := [a, !a, a]

private def alternating (i : ℤ) : Bool := decide (i % 2 = 1)

private def onePath (_ : ℕ) : List Bool × Bool := ([false], true)

private def fivePath : ℕ → List Bool × Bool
  | 0 => ([true, false], true)
  | _ + 1 => ([false], true)

private theorem onePath_admissible :
    IsLetterAdmissibleSequence ternary (alternating 0) onePath 0 :=
  IsLetterAdmissibleSequence.of_top_prefix (isAdmissibleSequence_zero _ _) ⟨[false], rfl⟩

private theorem one_rep : IsDumontThomasRep ternary alternating 1 1 [0, 1] :=
  IsDumontThomasRep.of_pos (p := 1) (N := 1) (k := 1) (s := onePath)
    (by decide) (dvd_refl _) onePath_admissible (by decide) (by decide)

-- Odd-length images preserve the alternating word on both sides of the origin. For N = 5,
-- the first digit skips a block of three; the last skips two letters in the image of `true`.
example : IsDumontThomasRep ternary alternating 1 5 [0, 1, 2] := by
  have hs : IsLetterAdmissibleSequence ternary (alternating 0) fivePath 1 := by
    refine IsLetterAdmissibleSequence.of_top_prefix
      (IsAdmissibleSequence.of_prefixes (fun i hi => ?_)) ⟨[false], rfl⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[], rfl⟩
  exact IsDumontThomasRep.of_pos (p := 1) (N := 5) (k := 2) (s := fivePath)
    (by decide) (by decide) hs (by decide) (by decide)

-- Independent positive-quotient check: the weighted positions are q = 1 and r = 2;
-- the quotient seed is `true`, not the original seed `false`.
example : (∑ j ∈ Finset.range (2 - 1), (morphIterate ternary j (fivePath (j + 1)).1).length) = 1 ∧
    (∑ j ∈ Finset.range 1, (morphIterate ternary j (fivePath j).1).length) = 2 ∧
    (morphIterate ternary 1 [alternating 1])[2]? = some (alternating 5) ∧
    IsDumontThomasRep ternary alternating 1 1 [0, 1] ∧
    IsLetterAdmissibleSequence ternary (alternating 1) fivePath 0 :=
  ⟨by decide, by decide, by decide, one_rep,
    IsLetterAdmissibleSequence.of_top_prefix (isAdmissibleSequence_zero _ _) ⟨[], rfl⟩⟩

-- Independent zero-quotient check: there are no retained digits and r = 1.
example : (∑ j ∈ Finset.range (1 - 1), (morphIterate ternary j (onePath (j + 1)).1).length) = 0 ∧
    (∑ j ∈ Finset.range 1, (morphIterate ternary j (onePath j).1).length) = 1 ∧
    (morphIterate ternary 1 [alternating 0])[1]? = some (alternating 1) ∧
    IsDumontThomasRep ternary alternating 1 0 [0] ∧
    IsLetterAdmissibleSequence ternary (alternating 0) onePath 0 :=
  ⟨by decide, by decide, by decide, isDumontThomasRep_zero _ _ _, onePath_admissible⟩

-- Compute the empty word and zero iterate independently of their public rewrite rules.
example : morphExtend ternary [] = [] ∧ morphIterate ternary 0 [true, false] = [true, false] :=
  by decide

-- Compute the singleton extension and both sides of iterate composition independently.
example : morphExtend ternary [true] = [true, false, true] ∧
    morphIterate ternary 2 [true] = [true, false, true, false, true, false, true, false, true] ∧
    morphIterate ternary 1 (morphIterate ternary 1 [true]) =
      [true, false, true, false, true, false, true, false, true] := by decide

open seedAutomaton_neutral_padding.Tests (double unitPoint)

-- Apply the public theorem on an actual period-one point, with a zero quotient.
example : IsDumontThomasRep double (fun _ => ()) 1 0 [0] := by
  let s : ℕ → List Unit × Unit := fun _ => ([()], ())
  have hs : IsLetterAdmissibleSequence double () s 0 :=
    IsLetterAdmissibleSequence.of_top_prefix (isAdmissibleSequence_zero _ _) ⟨[], rfl⟩
  exact (dumontThomasRep_quotient_remainder_pos (η := double) (u := fun _ => ())
    (p := 1) (hu := unitPoint) (N := 1) (k := 1) (s := s) (hN := by decide)
    (hk := dvd_refl _) (hs := hs) (htop := by decide) (hpre := by decide)).2.1

-- One application flips the phase of the alternating word; two restore it.
private def flipped (a : Bool) : List Bool := [!a, a, !a]

private def segment (z : ℤ) (n : ℕ) : List Bool :=
  (List.range n).map fun j : ℕ => alternating (z + (j : ℤ))

private theorem segment_add (z : ℤ) (m n : ℕ) :
    segment z (m + n) = segment z m ++ segment (z + (m : ℤ)) n := by
  simp only [segment, List.range_add, List.map_append, List.map_map, Function.comp_def,
    Nat.cast_add, add_assoc]

private theorem alternating_succ (z : ℤ) : alternating (z + 1) = !(alternating z) := by
  by_cases h : z % 2 = 1
  · have h' : (z + 1) % 2 ≠ 1 := by omega
    simp [alternating, h, h']
  · have h' : (z + 1) % 2 = 1 := by omega
    simp [alternating, h, h']

private theorem flipped_extend_segment (z : ℤ) (n : ℕ) :
    morphExtend flipped (segment z n) = segment (z + 1) (3 * n) := by
  induction n with
  | zero => simp [segment, morphExtend_nil]
  | succ n ih =>
    rw [segment_add z n 1, Nat.mul_succ, segment_add (z + 1) (3 * n) 3,
      morphExtend_append, ih]
    congr 1
    have hphase : alternating (z + 1 + (↑(3 * n) : ℤ)) = !(alternating (z + (n : ℤ))) := by
      rw [← alternating_succ]
      have hmod : (z + 1 + (↑(3 * n) : ℤ)) % 2 = (z + (n : ℤ) + 1) % 2 := by
        push_cast
        omega
      simp only [alternating, hmod]
    have htriple (x : ℤ) : segment x 3 = [alternating x, !alternating x, alternating x] := by
      have htwo : x + 2 = (x + 1) + 1 := by omega
      simp only [segment, show List.range 3 = [0, 1, 2] by decide, List.map_cons, List.map_nil,
        Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero, htwo, alternating_succ, Bool.not_not]
    rw [show segment (z + (n : ℤ)) 1 = [alternating (z + (n : ℤ))] by
      simp [segment, List.range_one], morphExtend_singleton, htriple, hphase]
    simp only [flipped, Bool.not_not]

private theorem flipped_second_iterate_segment (z : ℤ) (n : ℕ) :
    morphIterate flipped 2 (segment z n) = segment z (9 * n) := by
  rw [morphIterate_succ flipped 1, morphIterate_succ flipped 0, morphIterate_zero,
    flipped_extend_segment, flipped_extend_segment, show 3 * (3 * n) = 9 * n by omega]
  apply List.map_congr_left
  intro j _
  have hmod : (z + 1 + 1 + (j : ℤ)) % 2 = (z + (j : ℤ)) % 2 := by omega
  simp only [alternating, hmod]

private theorem flipped_grows (a : Bool) :
    Filter.Tendsto (fun k => (morphIterate flipped k [a]).length) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun n => ⟨n, fun k hk => ?_⟩
  have hpow : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) _
  simpa [morphIterate_length_of_uniform (k := 3) (f := flipped) (fun _ => rfl)] using
    hk.trans ((Nat.lt_two_pow_self (n := k)).le.trans hpow)

private theorem flipped_period_two : IsPeriodicPointWithGrowingSeed flipped alternating 2 := by
  have hsub : IsSubstitution flipped :=
    IsSubstitution.of_nonempty_images (fun _ => List.cons_ne_nil _ _) (flipped_grows false)
  have hper : IsTwoSidedPeriodicPoint flipped alternating 2 := by
    refine IsTwoSidedPeriodicPoint.of_prefix_suffix (by decide) ?_ ?_
    · intro n i hi
      have hw := flipped_second_iterate_segment 0 n
      simp only [segment, zero_add] at hw
      simp only [hw, List.getElem_map, List.getElem_range]
    · intro n i hi
      have hleft : ((List.range n).reverse.map fun j : ℕ => alternating (-1 - (j : ℤ))) =
          segment (-(n : ℤ)) n := by
        apply List.ext_getElem
        · simp [segment]
        · intro j _ hj
          have hj' : j < n := by simpa [segment] using hj
          simp only [segment, List.getElem_map, List.getElem_reverse, List.length_range,
            List.getElem_range]
          congr 1
          omega
      have hw := (congrArg (morphIterate flipped 2) hleft).trans
        (flipped_second_iterate_segment (-(n : ℤ)) n)
      have hlen := congrArg List.length hw
      simp only [segment, List.length_map, List.length_range] at hlen
      have hi' : i < 9 * n := hlen ▸ hi
      simp only [hw, segment, List.length_map, List.length_range, List.getElem_map,
        List.getElem_range]
      have hmod : (-(n : ℤ) + (↑(9 * n - 1 - i) : ℤ)) % 2 = (-1 - (i : ℤ)) % 2 := by
        omega
      simp only [alternating, hmod]
  refine IsPeriodicPointWithGrowingSeed.of_least_period hsub hper ?_
    (flipped_grows _) (flipped_grows _)
  intro q hq
  by_contra! h
  obtain rfl : q = 1 := by have := hq.one_le; omega
  -- At period one, the digit 0 would have to return to the seed, but it flips it.
  have hp : IsPeriodicPointWithGrowingSeed flipped alternating 1 :=
    IsPeriodicPointWithGrowingSeed.of_least_period hsub hq (fun _ hq' => hq'.one_le)
      (flipped_grows _) (flipped_grows _)
  have hpad := (seedAutomaton_neutral_padding flipped alternating 1 hp [] 1).1 (by decide)
  exact (by decide : seedAutomaton flipped (alternating (-1)) (alternating 0) [0, 0] ≠
    seedAutomaton flipped (alternating (-1)) (alternating 0) [0]) hpad

private def fourteenPath : ℕ → List Bool × Bool
  | 0 => ([false, true], false)
  | 1 | 2 => ([false], true)
  | _ + 3 => ([], true)

private theorem fourteen_admissible :
    IsLetterAdmissibleSequence flipped (alternating 0) fourteenPath 3 := by
  refine IsLetterAdmissibleSequence.of_top_prefix (IsAdmissibleSequence.of_prefixes ?_) (by decide)
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide

private def periodTwoQuotient : ℕ :=
  ∑ j ∈ Finset.range (4 - 2), (morphIterate flipped j (fourteenPath (j + 2)).1).length

private def periodTwoRemainder : ℕ :=
  ∑ j ∈ Finset.range 2, (morphIterate flipped j (fourteenPath j).1).length

private def retainedDigits : List ℕ :=
  0 :: (List.range (4 - 2)).reverse.map fun j => (fourteenPath (j + 2)).1.length

private theorem periodTwo_values :
    periodTwoQuotient = 1 ∧ periodTwoRemainder = 5 ∧ retainedDigits = [0, 0, 1] := by decide

-- Independently check the representation and both prefix links. At index 5 the first iterate
-- is out of bounds, and the second iterate from u₁ = true selects false.
example : (morphIterate flipped 1 [alternating 1])[5]? = none ∧
    (morphIterate flipped 2 [alternating 1])[5]? = some false ∧
    IsDumontThomasRep flipped alternating 2 1 [0, 0, 1] ∧
    IsLetterAdmissibleSequence flipped (alternating 1) fourteenPath 1 := by
  let s := fun j => fourteenPath (j + 2)
  have hs : IsLetterAdmissibleSequence flipped (alternating 0) s 1 := by
    refine IsLetterAdmissibleSequence.of_top_prefix (IsAdmissibleSequence.of_prefixes ?_) (by decide)
    intro i hi
    obtain rfl : i = 0 := by omega
    decide
  refine ⟨by decide, by decide, IsDumontThomasRep.of_pos (p := 2) (N := 1) (k := 2) (s := s)
    (by decide) (dvd_refl _) hs (by decide) (by decide), ?_⟩
  refine IsLetterAdmissibleSequence.of_top_prefix (IsAdmissibleSequence.of_prefixes ?_) (by decide)
  intro i hi
  obtain rfl : i = 0 := by omega
  decide

-- The public theorem must return the same three conclusions on this positive quotient.
example : (morphIterate flipped 2 [alternating 1])[5]? = some false ∧
    IsDumontThomasRep flipped alternating 2 1 [0, 0, 1] ∧
    IsLetterAdmissibleSequence flipped (alternating 1) fourteenPath 1 := by
  have h := dumontThomasRep_quotient_remainder_pos (η := flipped) (u := alternating)
    (p := 2) (hu := flipped_period_two) (N := 14) (k := 4) (s := fourteenPath)
    (hN := by decide) (hk := by decide) (hs := fourteen_admissible) (htop := by decide)
    (hpre := by decide)
  change (morphIterate flipped 2 [alternating (periodTwoQuotient : ℤ)])[periodTwoRemainder]? =
      some (alternating 14) ∧
    IsDumontThomasRep flipped alternating 2 periodTwoQuotient retainedDigits ∧
    IsLetterAdmissibleSequence flipped (alternating (periodTwoQuotient : ℤ)) fourteenPath 1 at h
  rw [periodTwo_values.1, periodTwo_values.2.1, periodTwo_values.2.2] at h
  simpa only [Nat.cast_one, show alternating 14 = false by decide] using h

end MetaMathlibExt.dumontThomasRep_quotient_remainder_pos.Tests

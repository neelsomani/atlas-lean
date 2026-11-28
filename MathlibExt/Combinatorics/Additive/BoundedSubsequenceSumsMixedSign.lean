/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Fin.Tuple
public import MathlibExt.Combinatorics.Additive.BoundedSubsequenceSums
public import MathlibExt.Combinatorics.Additive.YangChen

/-!
# Sharp lower bound for bounded subsequence sums of mixed-sign integers

For a sequence of length `h` with no zero terms, `1 ≤ n ≤ p` distinct negative and positive terms,
respectively, and positive multiplicities, assume `1 ≤ α` and `α + β + 1 ≤ h` for `α, β : ℕ`.
Pad the subsequence sums of lengths `α` through `h - β` by inserting zero between the two blocks.
The resulting fixed-length sumset satisfies the Yang–Chen bound. Equality follows by translating
a Yang–Chen extremizer so that the term at the inserted index is zero, and then removing it.

## References

* Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*,
  INTEGERS 24 (2024), Article A116, pp. 1–35, Lemmas 3–4 and Theorems 2 and 15.
* Quan-Hui Yang and Yong-Gao Chen, *On the cardinality of general $h$-fold sumsets*,
  European Journal of Combinatorics 47 (2015), pp. 103–114, Section 2 (sharp lower bound).
* The normalization of the extremizer follows `card_boundedSubsequenceSums_ge_of_pos` in
  `MathlibExt.Combinatorics.Additive.BoundedSubsequenceSumsPositive`.
-/

namespace MetaMathlibExt

private theorem strictMono_append {m n : ℕ} {a : Fin m → ℤ} {b : Fin n → ℤ}
    (ha : StrictMono a) (hb : StrictMono b) (hab : ∀ i j, a i < b j) :
    StrictMono (Fin.append a b) := by
  intro i j
  refine Fin.addCases (fun i => Fin.addCases (fun j hij => ?_) (fun j _ => ?_) j)
    (fun i => Fin.addCases (fun j hij => ?_) (fun j hij => ?_) j) i
  · simpa only [Fin.append_left] using ha (show i < j from hij)
  · simpa only [Fin.append_left, Fin.append_right] using hab i j
  · exact ((Fin.castAdd_lt n j).not_ge (Nat.le_add_right m i.val |>.trans hij.le)).elim
  · simpa only [Fin.append_right] using hb ((Fin.natAdd_lt_natAdd_iff m).mp hij)

-- Move the initial entry to the boundary between the two blocks.
private def moveFirstToBoundary (n p : ℕ) : Equiv.Perm (Fin (n + p + 1)) :=
  (finSuccEquiv (n + p)).trans
    (finSuccEquiv' (n := n + p) (Fin.natAdd n (0 : Fin (p + 1)))).symm

private theorem cons_append_eq_comp {A : Type*} {n p : ℕ} (a : A)
    (c : Fin n → A) (d : Fin p → A) :
    Fin.cons a (Fin.append c d) = Fin.append c (Fin.cons a d) ∘ moveFirstToBoundary n p := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [moveFirstToBoundary]
  · simp only [Function.comp_apply, moveFirstToBoundary, Equiv.trans_apply, finSuccEquiv_succ,
      Fin.cons_succ]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [finSuccEquiv'_symm_some_below (show (Fin.castAdd p j).castSucc <
        Fin.natAdd n (0 : Fin (p + 1)) from by simpa only [Fin.lt_def, Fin.val_castSucc,
          Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, Nat.add_zero] using j.isLt)]
      simp only [Fin.castSucc_castAdd, Fin.append_left]
    · rw [finSuccEquiv'_symm_some_above (show Fin.natAdd n (0 : Fin (p + 1)) ≤
        (Fin.natAdd n j).castSucc from Nat.le_add_right n j.val)]
      simp only [Fin.succ_natAdd, Fin.append_right, Fin.cons_succ]

/-- **Lower bound for bounded subsequence sums of a mixed-sign sequence.** Let $1 \le n \le p$, let
$t_0, \dots, t_{n-1}$ and $t_{n+1}, \dots, t_{n+p}$ be positive integers, let $h$ be their sum,
and let $\alpha, \beta$ be natural numbers with $1 \le \alpha$ and $\alpha + \beta \le h - 1$.
Put $\bar r = (t_0, \dots, t_{n-1}, h - \alpha - \beta, t_{n+1}, \dots, t_{n+p})$. For integers
$c_0 < \dots < c_{n-1} < 0 < d_1 < \dots < d_p$, let $\mathcal{A}$ be the sequence in which
$c_i$ occurs $t_i$ times and $d_j$ occurs $t_{n+j}$ times. Then
$|\Sigma^{\beta}_{\alpha}(\mathcal{A})| \ge L(\bar r, h - \beta)$ for all such $c$ and $d$, and
equality holds for some such $c$ and $d$. Here $\Sigma^{\beta}_{\alpha}(\mathcal{A})$ is the set
of sums of subsequences of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$ terms, and
$L$ is the Yang–Chen bound.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 15 (`integers-2024-A116-thm-15`). -/
public theorem card_boundedSubsequenceSums_ge_mixedSign {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (tn : Fin n → ℕ) (tp : Fin p → ℕ) (htn : ∀ i, 0 < tn i)
    (htp : ∀ j, 0 < tp j) (h : ℕ) (hh : h = ∑ i, tn i + ∑ j, tp j) (α β : ℕ) (hα : 1 ≤ α)
    (hαβ : α + β + 1 ≤ h) :
    (∀ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c → (∀ i, c i < 0) → StrictMono d →
      (∀ j, 0 < d j) →
      yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β) ≤
        (boundedSubsequenceSums α β (repetitionSequence c tn + repetitionSequence d tp)).card) ∧
    ∃ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c ∧ (∀ i, c i < 0) ∧ StrictMono d ∧
      (∀ j, 0 < d j) ∧
      ((boundedSubsequenceSums α β (repetitionSequence c tn + repetitionSequence d tp)).card :
          ℤ) = yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β) := by
  -- The proof does not need the source's restriction on the sizes of the two blocks.
  have _ := hn
  have _ := hnp
  let r := Fin.append tn (Fin.cons (h - α - β) tp)
  have hpad : 0 < h - α - β := by omega
  have hr : ∀ i, 0 < r i := by
    rw [Fin.forall_fin_add (m := n) (n := p + 1)]
    simpa only [r, Fin.append_left, Fin.append_right, Fin.forall_fin_succ,
      Fin.cons_zero, Fin.cons_succ] using And.intro htn (And.intro hpad htp)
  have hcap : h - β ≤ ∑ i, r i := by
    simp only [r, Fin.sum_univ_add, Fin.sum_univ_succ, Fin.append_left, Fin.append_right,
      Fin.cons_zero, Fin.cons_succ]
    omega
  have hrewrite (c : Fin n → ℤ) (d : Fin p → ℤ) (hc : StrictMono c) (hcneg : ∀ i, c i < 0)
      (hd : StrictMono d) (hdpos : ∀ j, 0 < d j) :
      boundedSubsequenceSums α β (repetitionSequence c tn + repetitionSequence d tp) =
        generalizedHFoldSumset (Fin.append c (Fin.cons 0 d)) r (h - β) := by
    have hmono := strictMono_append hc hd fun i j => (hcneg i).trans (hdpos j)
    have hnonzero (i : Fin (n + p)) : Fin.append c d i ≠ 0 := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using (hcneg j).ne
      · simpa only [Fin.append_right] using (hdpos j).ne'
    have ht (i : Fin (n + p)) : 0 < Fin.append tn tp i := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using htn j
      · simpa only [Fin.append_right] using htp j
    have hsum : h = ∑ i, Fin.append tn tp i := by
      simpa only [Fin.sum_univ_add, Fin.append_left, Fin.append_right] using hh
    rw [← repetitionSequence_append,
      boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_not_mem _ hmono.injective hnonzero
        _ ht h hsum α β hα hαβ,
      cons_append_eq_comp, cons_append_eq_comp, generalizedHFoldSumset_comp_perm]
  obtain ⟨hlower, a, ha, heq⟩ :=
    yangChen_card_generalizedHFoldSumset_ge r hr (h - β) (by omega) hcap
  constructor
  · intro c d hc hcneg hd hdpos
    rw [hrewrite c d hc hcneg hd hdpos]
    exact hlower _ (strictMono_append hc (Fin.strictMono_cons.2 ⟨hdpos, hd⟩)
      fun i j => Fin.cases (hcneg i) (fun j => (hcneg i).trans (hdpos j)) j)
  · let z := Fin.natAdd n (0 : Fin (p + 1))
    let c (i : Fin n) := a (i.castAdd (p + 1)) - a z
    let d (j : Fin p) := a (Fin.natAdd n j.succ) - a z
    have hc : StrictMono c := fun _ _ hij => sub_lt_sub_right (ha (Fin.strictMono_castAdd _ hij)) _
    have hd : StrictMono d := fun _ _ hij =>
      sub_lt_sub_right (ha (Fin.strictMono_natAdd _ (Fin.succ_lt_succ_iff.mpr hij))) _
    have hcneg (i : Fin n) : c i < 0 := sub_neg.mpr (ha (show i.castAdd (p + 1) < z by
      simpa only [z, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
        using i.isLt))
    have hdpos (j : Fin p) : 0 < d j :=
      sub_pos.mpr (ha (Fin.strictMono_natAdd _ (Fin.succ_pos j)))
    have hshift : Fin.append c (Fin.cons 0 d) = fun i => a i - a z := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [c]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [z]
        · simp [d]
    refine ⟨c, d, hc, hcneg, hd, hdpos, ?_⟩
    rw [hrewrite c d hc hcneg hd hdpos, hshift, card_generalizedHFoldSumset_sub_const]
    exact heq

end MetaMathlibExt

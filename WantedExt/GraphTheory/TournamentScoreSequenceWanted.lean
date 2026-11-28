/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting tournaments with a specified number of circular triads

Statements from Ian R. Harris and Ryan P. A. McShane,
"Counting Tournaments with a Specified Number of
Circular Triads", *Journal of Integer Sequences* 27
(2024), Article 24.8.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html>).

A tournament on `Fin n` is encoded by `T i j = true`
for "`i` beats `j`", with `score T i` the outdegree of
`i`. A circular triad is a 3-subset in which every
vertex has outdegree exactly `1` (a directed 3-cycle,
as opposed to a transitive triple with outdegrees
`2, 1, 0`), and reducibility is the existence of a
nonempty proper subset losing all its games against
the complement. Landau's theorem, the reducibility
criterion, and the circular-triad count were verified
exhaustively/randomly for small `n` against these
definitions.

Propositions 2 and 3 are the sum and product rules for
exponential generating functions of labeled structures
whose counts depend only on the number of players.
`atomCount n d` is the paper's `N(n, d)` (non-trivial
atoms, i.e. irreducible tournaments on `n ≥ 2` players,
with `d` circular triads) and `tournamentCount n d` its
`g_d(n)`; Theorems 8 and 10 are stated with these.

The tournament definitions and Theorems 1, 4, 5 and 6
are proved in
`MathlibExt.Combinatorics.Digraph.TournamentScoreSequence`.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Digraph.TournamentScoreSequence
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.GraphTheory.TournamentScoreSequenceWanted

/-- The atomic generator `A_d(x) = ∑_n N(n, d) xⁿ / n!`.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Section 3. -/
noncomputable def atomicGenerator (d : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (atomCount n d : ℚ) / n.factorial

/-- **Proposition 2**: if `c_n = a_n + b_n` counts the
structures on `n` labeled players split into two disjoint
cases, then the exponential generating functions satisfy
`C(x) = A(x) + B(x)`.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Proposition 2
(`jis-2024-24.8.7-prop-2`). -/
theorem_wanted egf_add (a b c : ℕ → ℕ)
    (hc : ∀ n, c n = a n + b n) :
    PowerSeries.mk (fun n => (c n : ℚ) / n.factorial) =
      PowerSeries.mk (fun n => (a n : ℚ) / n.factorial) +
        PowerSeries.mk (fun n => (b n : ℚ) / n.factorial)

/-- **Proposition 3**: if `a_k` and `b_k` count the
`α`- and `β`-structures on `k` labeled players and `c_n`
counts the ways to split `{1, …, n}` into sets `S₁`, `S₂`
and place an `α`-structure on `S₁` and a `β`-structure on
`S₂` (so `c_n = ∑_{S₁ ⊆ [n]} a_{|S₁|} b_{n - |S₁|}`), then
`C(x) = A(x) B(x)` for the exponential generating
functions.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Proposition 3
(`jis-2024-24.8.7-prop-3`). -/
theorem_wanted egf_mul (a b c : ℕ → ℕ)
    (hc : ∀ n, c n = ∑ S ∈ (Finset.range n).powerset,
      a S.card * b (n - S.card)) :
    PowerSeries.mk (fun n => (c n : ℚ) / n.factorial) =
      PowerSeries.mk (fun n => (a n : ℚ) / n.factorial) *
        PowerSeries.mk (fun n => (b n : ℚ) / n.factorial)

/-- **Theorem 10**: the exponential generating function
`G_d(x) = ∑_n g_d(n) xⁿ / n!` of tournaments with `d`
circular triads is
`∑_{r ∈ P_d} r!/(r₁! ⋯ r_d!) (1 - x)^{-(1+r)}
  ∏_{i=1}^d A_i(x)^{r_i}`, the sum over partitions of `d`
with multiplicities `r_i` and size `r`. Stated for every
`d` (at `d = 0` both sides are `1/(1 - x)`), with the
`n = 0` coefficient `g_d(0)` included.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Theorem 10
(`jis-2024-24.8.7-thm-10`). -/
theorem_wanted tournament_egf (d : ℕ) :
    PowerSeries.mk (fun n => (tournamentCount n d : ℚ) / n.factorial) =
      ∑ p : Nat.Partition d,
        ((p.parts.card.factorial : ℚ) /
            ∏ i ∈ p.parts.toFinset, ((p.parts.count i).factorial : ℚ)) •
          ((1 - PowerSeries.X)⁻¹ ^ (1 + p.parts.card) *
            (p.parts.map atomicGenerator).prod)

end MathlibExt.GraphTheory.TournamentScoreSequenceWanted

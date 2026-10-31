/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CliqueColoring
public import Complexity.Logics.Propositional.Resolution.Interpolation
public import Complexity.Computability.Circuit.Monotone.Clique.Asymptotic

/-!
# Resolution lower bounds for clique–colouring formulas

The clique–colouring formula `Clique_{n,k}(p, q) ∧ Color_{n,r}(p, z)`
(`Cslib.Logic.PL.CNF.cliqueColoring`) says that a graph on `n` vertices, given by the shared edge
variables `p`, has a `k`-clique and is `r`-colourable [Krajíček, Section 7][Krajicek1997]. Its
interpolants are exactly the Boolean functions of the edges separating the graphs with a `k`-clique
from the `r`-colourable graphs (`Cslib.Logic.PL.CNF.isInterpolant_clique_coloring_iff`), so for
`r < k` it is unsatisfiable (`Cslib.Logic.PL.CNF.not_satisfiable_cliqueColoring`).

The edge variables occur only positively in the clique formula, so monotone feasible interpolation
turns a resolution refutation with `s` lines into a monotone circuit with at most `2 s` gates
separating the two classes of graphs
(`Cslib.Logic.PL.CNF.exists_separates_of_refutableInSize_cliqueColoring`). For `r = k - 1`,
Razborov's method of approximations bounds such circuits from below, since it reads them only on
complete graphs on `k`-sets and complete `(k - 1)`-partite graphs
(`Cslib.Circuits.Monotone.lt_size_of_separates`), and every edge is essential to them
(`Cslib.Circuits.Clique.Separates.essentialAt`). So half of each monotone bound bounds the
resolution refutations of the clique–colouring formula from below: with explicit parameters
(`Cslib.Logic.PL.CNF.lt_two_mul_of_refutableInSize_cliqueColoring`), more than `64 ^ w / 2`
lines for `w ≥ 16`, `4 w² ≤ k - 1` and `64 w⁶ k ≤ n`
(`Cslib.Logic.PL.CNF.sixtyFour_pow_lt_two_mul_of_refutableInSize_cliqueColoring`), at least
`(n.choose 2 - 1) / 2` lines for `2 ≤ k ≤ n`
(`Cslib.Logic.PL.CNF.edgeCount_le_one_add_two_mul_of_refutableInSize_cliqueColoring`), and more
than `2 ^ (2 ⌊√k⌋) / 2` lines for `2 ≤ k` and `k⁴ ≤ n`
(`Cslib.Logic.PL.CNF.two_pow_two_mul_sqrt_lt_two_mul_of_refutableInSize_cliqueColoring`). Taking
`k = ⌊√⌊√n⌋⌋` for `n ≥ 16` gives refutations of more than `2 ^ (2 m) / 2` lines with `m = ⌊√k⌋`,
of order `n^{1/8}` (`Cslib.Logic.PL.CNF.two_pow_lt_two_mul_of_refutableInSize_cliqueColoring_sqrt`).

This is the argument of [Krajíček, Corollary 7.3(1)][Krajicek1997], which combines his Theorem 6.1
with the Alon–Boppana bound (his Theorem 7.2) for `k = ⌈√n⌉ + 1` and obtains `2 ^ Ω(n^{1/4})`
lines. The Razborov bound used here needs `k⁴ ≤ n`, and so gives the weaker `2 ^ Ω(n^{1/8})`.

## Main definitions

* `Cslib.Logic.PL.CNF.cliqueColoring`: the clique–colouring formula.

## Main results

* `Cslib.Logic.PL.CNF.isInterpolant_clique_coloring_iff`: the interpolants of the clique and
  colouring formulas are the functions separating the graphs with a `k`-clique from the
  `r`-colourable graphs.
* `Cslib.Logic.PL.CNF.not_satisfiable_cliqueColoring`: the formula is unsatisfiable for `r < k`.
* `Cslib.Logic.PL.CNF.exists_separates_of_refutableInSize_cliqueColoring`: monotone interpolation
  for the clique–colouring formula.
* `Cslib.Logic.PL.CNF.lt_two_mul_of_refutableInSize_cliqueColoring`,
  `Cslib.Logic.PL.CNF.sixtyFour_pow_lt_two_mul_of_refutableInSize_cliqueColoring`,
  `Cslib.Logic.PL.CNF.edgeCount_le_one_add_two_mul_of_refutableInSize_cliqueColoring`,
  `Cslib.Logic.PL.CNF.two_pow_two_mul_sqrt_lt_two_mul_of_refutableInSize_cliqueColoring`,
  `Cslib.Logic.PL.CNF.two_pow_lt_two_mul_of_refutableInSize_cliqueColoring_sqrt`: **resolution
  lower bounds** for the clique–colouring formula.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]; Section 7, Theorem 7.2 and Corollary 7.3 are numbered as
  in the author's preprint.
* [P. Pudlák, *Lower bounds for resolution and cutting plane proofs and monotone
  computations*][Pudlak1997]
* [A. A. Razborov, *Lower bounds on the monotone complexity of some Boolean
  functions*][Razborov1985]
-/

public section

namespace Cslib.Logic.PL

open Cslib.Circuits Cslib.Circuits.Clique

variable {n k r : ℕ}

/-- **The clique–colouring formula** `Clique_{n,k}(p, q) ∧ Color_{n,r}(p, z)`
[Krajíček, Section 7][Krajicek1997]: the graph on `n` vertices given by the shared edge variables
has a `k`-clique and is `r`-colourable. -/
noncomputable abbrev CNF.cliqueColoring (n k r : ℕ) :
    CNF (Fin (edgeCount n) ⊕ (Fin k × Fin n ⊕ Fin n × Fin r)) :=
  (CNF.clique n k).appendShared (CNF.coloring n r)

/-- **The interpolants of the clique and colouring formulas** are exactly the Boolean functions of
the edges separating the graphs with a `k`-clique from the `r`-colourable graphs. -/
theorem CNF.isInterpolant_clique_coloring_iff {f : BooleanFunction (edgeCount n)} :
    (CNF.clique n k).IsInterpolant (CNF.coloring n r) f ↔ Separates k r f := by
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨q, hq⟩ := (CNF.exists_eval_clique_iff x).2 hx
      exact hA x q hq
    · obtain ⟨z, hz⟩ := (CNF.exists_eval_coloring_iff x).2 hx
      exact hB x z hz
  · rintro ⟨hA, hB⟩
    exact ⟨fun x q hq => hA x ((CNF.exists_eval_clique_iff x).1 ⟨q, hq⟩),
      fun x z hz => hB x ((CNF.exists_eval_coloring_iff x).1 ⟨z, hz⟩)⟩

/-- For `r < k`, the clique–colouring formula is unsatisfiable: `k`-clique is an interpolant. -/
theorem CNF.not_satisfiable_cliqueColoring (hr : r < k) :
    ¬ (CNF.cliqueColoring n k r).Satisfiable :=
  (CNF.isInterpolant_clique_coloring_iff.2 (separates_clique hr)).not_satisfiable

/-- **Monotone interpolation for the clique–colouring formula.** A resolution refutation of the
clique–colouring formula with at most `s` lines gives a monotone circuit with at most `2 s` gates
separating the graphs with a `k`-clique from the `r`-colourable graphs. -/
theorem CNF.exists_separates_of_refutableInSize_cliqueColoring {s : ℕ}
    (h : (CNF.cliqueColoring n k r).RefutableInSize s) :
    ∃ C : Circuit Monotone.signature (edgeCount n) 1, C.size ≤ 2 * s ∧
      Separates k r fun x => C.eval Monotone.interpretation x 0 := by
  obtain ⟨C, hsize, hC⟩ := h.exists_monotone_interpolant_of_positive
    fun _ hd _ _ hl => CNF.eq_true_of_mem_clique hd hl
  exact ⟨C, hsize, CNF.isInterpolant_clique_coloring_iff.1 hC⟩

open Cslib.Circuits.Monotone in
/-- **Resolution lower bound for the clique–colouring formula**, with explicit parameters
[Krajíček, Corollary 7.3][Krajicek1997]. If `t` is below both error budgets of the approximators
with `p ≥ 2` petals and width `w ≥ 2`, with `w + 1 ≤ k` and `2 w ^ 2 ≤ k - 1`, then every
resolution refutation of `Clique_{n,k} ∧ Color_{n,k-1}` has more than `t / 2` lines. -/
theorem CNF.lt_two_mul_of_refutableInSize_cliqueColoring {p w t s : ℕ} (hp : 2 ≤ p)
    (hw : 2 ≤ w) (hk : w + 1 ≤ k) (hr : 2 * w ^ 2 ≤ k - 1)
    (hpos : Positive.errorCap n k p w * t < n.choose k)
    (hneg : 2 * negativeGateCap n (k - 1) p w * t < (k - 1) ^ n)
    (h : (CNF.cliqueColoring n k (k - 1)).RefutableInSize s) : t < 2 * s := by
  obtain ⟨C, hsize, hC⟩ := CNF.exists_separates_of_refutableInSize_cliqueColoring h
  exact (lt_size_of_separates hp hw hk hr hpos hneg hC).trans_le hsize

/-- **Resolution lower bound for the clique–colouring formula.** For every width `w ≥ 16` with
`4 w ^ 2 ≤ k - 1` and `64 w ^ 6 k ≤ n`, every resolution refutation of
`Clique_{n,k} ∧ Color_{n,k-1}` has more than `64 ^ w / 2` lines. -/
theorem CNF.sixtyFour_pow_lt_two_mul_of_refutableInSize_cliqueColoring {w s : ℕ} (hw : 16 ≤ w)
    (hk : 4 * w ^ 2 ≤ k - 1) (hn : 64 * w ^ 6 * k ≤ n)
    (h : (CNF.cliqueColoring n k (k - 1)).RefutableInSize s) : 64 ^ w < 2 * s := by
  obtain ⟨C, hsize, hC⟩ := CNF.exists_separates_of_refutableInSize_cliqueColoring h
  exact (Monotone.pow_lt_size_of_separates hw hk hn hC).trans_le hsize

/-- **Resolution lower bound for the clique–colouring formula, small cliques.** For `2 ≤ k ≤ n`,
every resolution refutation of `Clique_{n,k} ∧ Color_{n,k-1}` has at least `(n.choose 2 - 1) / 2`
lines: every edge is essential to the interpolant. -/
theorem CNF.edgeCount_le_one_add_two_mul_of_refutableInSize_cliqueColoring {s : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) (h : (CNF.cliqueColoring n k (k - 1)).RefutableInSize s) :
    edgeCount n ≤ 1 + 2 * s := by
  obtain ⟨C, hsize, hC⟩ := CNF.exists_separates_of_refutableInSize_cliqueColoring h
  exact (Monotone.edgeCount_le_succ_size_of_separates hk hkn hC).trans (by omega)

/-- **Resolution lower bound for the clique–colouring formula.** For `2 ≤ k` with `k ^ 4 ≤ n`,
every resolution refutation of `Clique_{n,k} ∧ Color_{n,k-1}` has more than `2 ^ (2 ⌊√k⌋) / 2`
lines. -/
theorem CNF.two_pow_two_mul_sqrt_lt_two_mul_of_refutableInSize_cliqueColoring {s : ℕ}
    (hk : 2 ≤ k) (hn : k ^ 4 ≤ n) (h : (CNF.cliqueColoring n k (k - 1)).RefutableInSize s) :
    2 ^ (2 * Nat.sqrt k) < 2 * s := by
  obtain ⟨C, hsize, hC⟩ := CNF.exists_separates_of_refutableInSize_cliqueColoring h
  exact (Monotone.two_pow_two_mul_sqrt_lt_size_of_separates hk hn hC).trans_le hsize

/-- **An exponential resolution lower bound for clique–colouring formulas.** For `n ≥ 16` and
`k = ⌊√⌊√n⌋⌋`, so that `2 ≤ k` and `k ^ 4 ≤ n`, every resolution refutation of
`Clique_{n,k} ∧ Color_{n,k-1}` has more than `2 ^ (2 m) / 2` lines, where `m = ⌊√k⌋` is of order
`n^{1/8}`. -/
theorem CNF.two_pow_lt_two_mul_of_refutableInSize_cliqueColoring_sqrt {s : ℕ}
    (hn : 16 ≤ n)
    (h : (CNF.cliqueColoring n n.sqrt.sqrt (n.sqrt.sqrt - 1)).RefutableInSize s) :
    2 ^ (2 * n.sqrt.sqrt.sqrt) < 2 * s := by
  refine CNF.two_pow_two_mul_sqrt_lt_two_mul_of_refutableInSize_cliqueColoring ?_ ?_ h
  · exact Nat.le_sqrt.2 (Nat.le_sqrt.2 (by omega))
  · calc n.sqrt.sqrt ^ 4 = (n.sqrt.sqrt ^ 2) ^ 2 := by ring
      _ ≤ n.sqrt ^ 2 := Nat.pow_le_pow_left (Nat.sqrt_le' _) 2
      _ ≤ n := Nat.sqrt_le' n

end Cslib.Logic.PL

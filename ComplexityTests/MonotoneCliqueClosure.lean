/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.CliqueColoring

/-!
# Tests: the Alon–Boppana bound for monotone clique separators

The two singletons `{0}` and `{1}` form an implication-minimal family for `3`: no three of them
have pairwise intersections inside `∅`. So the Alon–Boppana family bound `(3 - 1) ^ 1 = 2` is
attained. For `2` they imply `∅`, and indeed the bound `(2 - 1) ^ 1 = 1` excludes them.

The `2 ^ l` separator bound applies at `l = 16`, `k = 513` and `n = 2 ^ 21`, where `n < k ^ 4`,
outside the range of the Razborov bound. It applies to an actual circuit computing `513`-clique,
and to resolution refutations with `600`-cliques and `512` colours. At `n = 2 ^ 40` and
`k = 2 ^ 20 + 1 = ⌊√n⌋ + 1` the clique–colouring formula is refutable, and every refutation has
more than `2 ^ 512 / 2` lines.
-/

namespace ComplexityTests.MonotoneCliqueClosure

open Cslib Cslib.Circuits Cslib.Circuits.Clique Cslib.Logic.PL

/-- Two singletons form an implication-minimal family for `3`. -/
example : IsImplicationMinimal 3 ({{0}, {1}} : Finset (Finset (Fin 2))) := by
  unfold IsImplicationMinimal ImpliedBy
  decide

/-- The family bound is attained: `2 = (3 - 1) ^ 1` sets of one element. -/
example : ({{0}, {1}} : Finset (Finset (Fin 2))).card = (3 - 1) ^ 1 := by decide

/-- For `2` implying sets, the two singletons imply their intersection `∅`, so they are not
implication-minimal. -/
example : ¬IsImplicationMinimal 2 ({{0}, {1}} : Finset (Finset (Fin 2))) := by
  unfold IsImplicationMinimal ImpliedBy
  decide

/-- An implication-minimal family for `2` has at most one member. -/
example {F : Finset (Finset (Fin 5))} (hF : IsImplicationMinimal 2 F) : F.card ≤ 1 := by
  simpa using card_le_pow_of_isImplicationMinimal le_rfl (k := 5) (fun W _ => W.card_le_univ.trans
    (by simp)) hF

/-- `n = 2 ^ 21` is below `513 ^ 4`, the vertex count the Razborov bound needs. -/
example : 2 ^ 21 < 513 ^ 4 := by norm_num

/-- **The `2 ^ l` bound instantiated** at `l = 16`, `k = 513` and `n = 2 ^ 21`, on an actual
monotone circuit computing `513`-clique. -/
example : ∃ C : Circuit Monotone.signature (edgeCount (2 ^ 21)) 1,
    C.Computes Monotone.interpretation (single (clique (2 ^ 21) 513)) ∧ 2 ^ 16 < C.size := by
  obtain ⟨C, hC⟩ := Monotone.exists_computes_clique (2 ^ 21) 513
  refine ⟨C, hC, Monotone.two_pow_lt_size_of_computes_clique (by norm_num) (by norm_num) ?_ hC⟩
  rw [Nat.log_pow (by norm_num)]
  norm_num

/-- **Fewer colours than `k - 1`**: on `2 ^ 21` vertices, every resolution refutation of
`Clique_{n,600} ∧ Color_{n,512}` has more than `2 ^ 16 / 2` lines. -/
example {s : ℕ} (h : (CNF.cliqueColoring (2 ^ 21) 600 512).RefutableInSize s) :
    2 ^ 16 < 2 * s := by
  refine CNF.two_pow_lt_two_mul_of_refutableInSize_cliqueColoring (by norm_num) (by norm_num)
    (by norm_num) ?_ h
  rw [Nat.log_pow (by norm_num)]
  norm_num

/-- `⌊√(2 ^ 40)⌋ = 2 ^ 20`. -/
private theorem sqrt_two_pow_forty : (2 ^ 40 : ℕ).sqrt = 2 ^ 20 := by
  rw [show (2 : ℕ) ^ 40 = (2 ^ 20) ^ 2 by norm_num]
  exact Nat.sqrt_eq' _

/-- `⌊√(2 ^ 20)⌋ = 2 ^ 10`. -/
private theorem sqrt_two_pow_twenty : (2 ^ 20 : ℕ).sqrt = 2 ^ 10 := by
  rw [show (2 : ℕ) ^ 20 = (2 ^ 10) ^ 2 by norm_num]
  exact Nat.sqrt_eq' _

/-- **The `n^{1/4}` resolution bound instantiated** at `n = 2 ^ 40` and `k = ⌊√n⌋ + 1`: the
clique–colouring formula is refutable, and every refutation has more than `2 ^ 512 / 2` lines. -/
example : (∃ s, (CNF.cliqueColoring (2 ^ 40) (2 ^ 20 + 1) (2 ^ 20)).RefutableInSize s) ∧
    ∀ s, (CNF.cliqueColoring (2 ^ 40) (2 ^ 20 + 1) (2 ^ 20)).RefutableInSize s →
      2 ^ 512 < 2 * s := by
  refine ⟨CNF.exists_refutableInSize_iff_not_satisfiable.2
    (CNF.not_satisfiable_cliqueColoring (by norm_num)), fun s h => ?_⟩
  have := CNF.two_pow_lt_two_mul_of_refutableInSize_cliqueColoring_of_sqrt_lt (n := 2 ^ 40)
    (k := 2 ^ 20 + 1) le_rfl (by rw [sqrt_two_pow_forty]; norm_num)
    (by rw [sqrt_two_pow_forty]; norm_num) h
  rwa [sqrt_two_pow_forty, sqrt_two_pow_twenty, show (2 ^ 10 / 2 : ℕ) = 512 by norm_num] at this

end ComplexityTests.MonotoneCliqueClosure

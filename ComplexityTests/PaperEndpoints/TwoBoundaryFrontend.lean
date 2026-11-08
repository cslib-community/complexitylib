/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend
public import Complexity.Logics.Propositional.CNF.VCOne
meta import Complexity.Computability.PolyTime.CNF.TwoBoundaryFrontend
meta import Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend

/-! # Actual arbitrary DNF constructor, counts, exact budgets and resource clients

Exhaustive counting is a small test oracle only. Production certificates instantiate the proved
sharp native counter. A tautological DNF demonstrates why a generic VC-one conversion is invalid.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM
open TwoBoundary.BinaryFrontend

set_option linter.hashCommand false

/-- Small test oracle; this is not a production counter. -/
@[expose] def dnfTestCounter (p : ℕ × CNF ℕ) : ℕ :=
  let (n, q) := p
  (List.range (2 ^ n)).countP fun x => q.eval (Nat.testBit x)

/-- info: (1, 0, 1, 1) -/
#guard_msgs in
#eval (execute dnfTestCounter (compile (0, [], [])),
  execute dnfTestCounter (compile (0, [], [[]])),
  execute dnfTestCounter (compile (0, [], [[[]]])),
  execute dnfTestCounter (compile (0, [], [[[]], [[]], [[]]])))

/- Arbitrary two-literal terms, overlapping conditions, and no VC-one promise. -/
/-- info: (5, 2, 2, 2) -/
#guard_msgs in
#eval (execute dnfTestCounter (compile
    (3, [], [[[(0, true), (1, true)], [(2, false)]]])),
  execute dnfTestCounter (compile
    (3, [], [[[(0, true), (1, true)], [(2, false)]], [[(1, false)]]])),
  execute dnfTestCounter (compile
    (2, [], [[[(0, true), (0, true)], [(1, true), (1, false)]]])),
  execute dnfTestCounter (compile (2, [], [[[(0, true)], [(0, true)]]])))

/- A wide side clause is retained, and unused declared bits retain their multiplicity. -/
/-- info: (6, 0, 1, 2) -/
#guard_msgs in
#eval (execute dnfTestCounter (compile (3, [[(0, true), (1, true)]], [])),
  execute dnfTestCounter (compile (3, [[]], [[[]]])),
  (queries (compile (3, [], []))).length,
  (queries (compile (3, [], [[[]]]))).length)

/- Actual construction on a wide declaration writes constant-size clauses, not the cube. -/
/-- info: [(256, 0), (256, 1)] -/
#guard_msgs in
#eval (queries (compile (256, [], [[[]]]))).map fun (N, q) => (N, q.length)

/-- An arbitrary DNF can admit the full two-bit cube, which is not VC-one. -/
example : (∀ σ : Fin 2 → Bool, DNF.eval σ ([[]] : DNF (Fin 2)) = true) ∧
    ¬VCOne.DimensionOne (Finset.univ : Finset (Fin 2 → Bool)) := by
  constructor
  · intro σ; rfl
  · intro h
    have hc := VCOne.card_le (Finset.univ : Finset (Fin 2 → Bool)) h
    norm_num at hc

example : ComputableInPolyTime compile encInput encOutput := compile_polytime

open Classical in
/-- Original-count theorem applies to repeated literals/terms and arbitrary overlapping formulas. -/
example {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n))) :
    value (compile (ofFinite B P)) =
      Fintype.card {σ : Fin n → Bool // B.eval σ = true ∧ ∀ p ∈ P, DNF.eval σ p = true} :=
  compile_count B P

/-- The actual source clause budget is independent of term widths after fixing their bound. -/
example {n b d : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (hb : ∀ c ∈ B, c.length ≤ b) (hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d)
    (N : ℕ) (q : CNF ℕ) (hq : (N, q) ∈ queries (compile (ofFinite B P))) :
    N = (if P.isEmpty then n else n + P.length - 1) ∧
      q.length ≤ B.length + 2 * (P.map List.length).sum ∧
      ∀ c ∈ q, c.length ≤ max b (d + 2) ∧ ∀ l ∈ c, l.1 < N :=
  compile_budget B P hb hp N q hq

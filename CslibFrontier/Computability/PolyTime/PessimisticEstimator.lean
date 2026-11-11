/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Capabilities
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Foundations.Combinatorics.PessimisticEstimator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops

/-!
# Polynomial-time transfer for greedy pessimistic-estimator derandomization

`PolyTimeGreedyInput` packages an input-parameterized instance of
`Cslib.PessimisticEstimator.greedy` (round list, initial state, binary branch transition, and
pessimistic estimator / conditional expectation) and proves plain multi-tape polynomial-time
computability (`Turing.MultiTapeTM.ComputableInPolyTime`) whenever:
1. `rounds`, `init`, `branch`, `estimate`, and the order comparison `(· ≤ ·)` on `M` are
   `ComputableInPolyTime`; and
2. taking either branch on any round `r ∈ rounds x` grows the encoded state by at most a
   polynomially bounded additive budget `growth x`.

`run_polyTime_spec` and `run_polyTime_spec_of_add_le` pair this plain complexity certificate with
the invariant and deterministic objective bound `estimate x (run x) ≤ estimate x (init x)` from
`Cslib.PessimisticEstimator.greedy_spec`.

## Main definitions

* `Cslib.Computability.PolyTimeGreedyInput`: input-parameterized greedy / pessimistic-estimator
  specification.
* `Cslib.Computability.PolyTimeGreedyInput.encBranchInput`: tuple encoding for branch transitions.
* `Cslib.Computability.PolyTimeGreedyInput.run`: execute `Cslib.PessimisticEstimator.greedy` on an
  input `x`.

## Main results

* `Cslib.Computability.PolyTimeGreedyInput.computableInPolyTime_run`: plain polynomial-time
  transfer for general order encodings `encM`.
* `Cslib.Computability.PolyTimeGreedyInput.computableInPolyTime_run_nat`: specialization to binary
  natural-number estimators (`encNat`).
* `Cslib.Computability.PolyTimeGreedyInput.run_polyTime_spec`,
  `Cslib.Computability.PolyTimeGreedyInput.run_polyTime_spec_of_add_le`: combined polynomial-time
  and pessimistic-estimator correctness specifications.
-/

public section

namespace Cslib.Computability

open Cslib.PessimisticEstimator Turing.MultiTapeTM ComputableInPolyTime

/-- Input-parameterized greedy binary-choice derandomization bundle. -/
structure PolyTimeGreedyInput (I R S M : Type) [LE M] [DecidableRel (α := M) (· ≤ ·)] where
  /-- Ordered list of decision rounds extracted from input `x`. -/
  rounds : I → List R
  /-- Initial state constructed from input `x`. -/
  init : I → S
  /-- Branch transition for input `x`, round `r`, choice `b`, and state `s`. -/
  branch : I → R → Bool → S → S
  /-- Pessimistic-estimator / conditional-expectation value on state `s` under input `x`. -/
  estimate : I → S → M

namespace PolyTimeGreedyInput

/-- Tuple encoding `(((I × S) × R) × Bool)` for input-parameterized greedy branch transitions. -/
abbrev encBranchInput {I R S : Type}
    (encI : I ↪ List Bool) (encS : S ↪ List Bool) (encR : R ↪ List Bool) :
    (((I × S) × R) × Bool) ↪ List Bool :=
  encPair (encPair (encPair encI encS) encR) encBool

section Execution

variable {I R S M : Type} [LE M] [DecidableRel (α := M) (· ≤ ·)]
  (G : PolyTimeGreedyInput I R S M)

/-- Run `Cslib.PessimisticEstimator.greedy` on input `x`. -/
@[expose] def run (x : I) : S :=
  greedy (G.branch x) (G.estimate x) (G.rounds x) (G.init x)

private theorem run_eq_foldl (x : I) :
    G.run x =
      (G.rounds x).foldl
        (fun s r =>
          if G.estimate x (G.branch x r true s) ≤ G.estimate x (G.branch x r false s) then
            G.branch x r true s
          else
            G.branch x r false s)
        (G.init x) :=
  rfl

/-- Plain `ComputableInPolyTime` transfer for `G.run` when `rounds`, `init`, `branch`, `estimate`,
and `(· ≤ ·)` are polynomial-time and each round increases `(encS s).length` by at most a
polynomially bounded `growth x`. -/
theorem computableInPolyTime_run
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encL : List R ↪ List Bool}
    [ListEncoding encR encL] [SizedListEncoding encR encL]
    {encS : S ↪ List Bool} {encM : M ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encL)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encBranchInput encI encS encR) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encM)
    (hle : ComputableInPolyTime (fun (m₁, m₂) => decide (m₁ ≤ m₂))
      (encPair encM encM) encBool)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r b, r ∈ G.rounds x →
      (encS (G.branch x r b s)).length ≤ (encS s).length + growth x) :
    ComputableInPolyTime G.run encI encS := by
  let encStep := encPair (encPair encI encS) encR
  have hid : ComputableInPolyTime id encStep encStep := id'
  have hx : ComputableInPolyTime (fun ((input, _state), _round) => input) encStep encI :=
    (fst (encPair encI encS) encR).fst'
  have hbr (b : Bool) : ComputableInPolyTime
      (fun ((input, state), round) => G.branch input round b state) encStep encS :=
    hbranch.comp (hid.prod (const b))
  have hest (b : Bool) : ComputableInPolyTime
      (fun ((input, state), round) =>
        G.estimate input (G.branch input round b state)) encStep encM :=
    hestimate.comp (hx.prod (hbr b))
  have hcmp : ComputableInPolyTime
      (fun ((input, state), round) =>
        decide (G.estimate input (G.branch input round true state) ≤
          G.estimate input (G.branch input round false state)))
      encStep encBool :=
    hle.comp ((hest true).prod (hest false))
  have hstep : ComputableInPolyTime
      (fun ((input, state), round) =>
        if G.estimate input (G.branch input round true state) ≤
            G.estimate input (G.branch input round false state) then
          G.branch input round true state
        else
          G.branch input round false state)
      encStep encS := by
    simpa only [decide_eq_true_eq] using ite hcmp (hbr true) (hbr false)
  refine foldlWithInput_of_bounded_growth hinit ⟨hrounds, hstep, inferInstance, inferInstance⟩
    ⟨hpoly, fun x s r hr => ?_⟩
  dsimp only [greedyStep]
  split_ifs
  · exact hgrowth x s r true hr
  · exact hgrowth x s r false hr

end Execution

section NatSpecialization

variable {I R S : Type} (G : PolyTimeGreedyInput I R S ℕ)

/-- Specialization of `computableInPolyTime_run` to `ℕ`-valued estimators encoded in binary
(`encNat`). -/
theorem computableInPolyTime_run_nat
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encL : List R ↪ List Bool}
    [ListEncoding encR encL] [SizedListEncoding encR encL]
    {encS : S ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encL)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encBranchInput encI encS encR) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encNat)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r b, r ∈ G.rounds x →
      (encS (G.branch x r b s)).length ≤ (encS s).length + growth x) :
    ComputableInPolyTime G.run encI encS :=
  G.computableInPolyTime_run hrounds hinit hbranch hestimate
    (binary_le' (fst encNat encNat) (snd encNat encNat)) hpoly hgrowth

end NatSpecialization

section CombinedSpec

variable {I R S M : Type} [LinearOrder M] (G : PolyTimeGreedyInput I R S M)

/-- Pairs the plain `ComputableInPolyTime` certificate for `G.run` with the terminal invariant and
deterministic bound `G.estimate x (G.run x) ≤ G.estimate x (G.init x)`. -/
theorem run_polyTime_spec
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encL : List R ↪ List Bool}
    [ListEncoding encR encL] [SizedListEncoding encR encL]
    {encS : S ↪ List Bool} {encM : M ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encL)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encBranchInput encI encS encR) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encM)
    (hle : ComputableInPolyTime (fun (m₁, m₂) => decide (m₁ ≤ m₂))
      (encPair encM encM) encBool)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r b, r ∈ G.rounds x →
      (encS (G.branch x r b s)).length ≤ (encS s).length + growth x)
    (Inv : I → List R → S → Prop)
    (hinv_init : ∀ x, Inv x (G.rounds x) (G.init x))
    (hinv_branch : ∀ x r rs s b, Inv x (r :: rs) s → Inv x rs (G.branch x r b s))
    (hmin : ∀ x r rs s, Inv x (r :: rs) s →
      min (G.estimate x (G.branch x r true s)) (G.estimate x (G.branch x r false s)) ≤
        G.estimate x s) :
    ComputableInPolyTime G.run encI encS ∧
      ∀ x, Inv x [] (G.run x) ∧ G.estimate x (G.run x) ≤ G.estimate x (G.init x) :=
  ⟨G.computableInPolyTime_run hrounds hinit hbranch hestimate hle hpoly hgrowth, fun x =>
    greedy_spec (G.branch x) (G.estimate x) (Inv x) (hinv_branch x) (hmin x)
      (G.rounds x) (G.init x) (hinv_init x)⟩

/-- Averaging form of `run_polyTime_spec` when the two branch estimates sum to at most twice the
current estimate. -/
theorem run_polyTime_spec_of_add_le [AddCommMonoid M] [IsOrderedCancelAddMonoid M]
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encL : List R ↪ List Bool}
    [ListEncoding encR encL] [SizedListEncoding encR encL]
    {encS : S ↪ List Bool} {encM : M ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encL)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encBranchInput encI encS encR) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encM)
    (hle : ComputableInPolyTime (fun (m₁, m₂) => decide (m₁ ≤ m₂))
      (encPair encM encM) encBool)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r b, r ∈ G.rounds x →
      (encS (G.branch x r b s)).length ≤ (encS s).length + growth x)
    (Inv : I → List R → S → Prop)
    (hinv_init : ∀ x, Inv x (G.rounds x) (G.init x))
    (hinv_branch : ∀ x r rs s b, Inv x (r :: rs) s → Inv x rs (G.branch x r b s))
    (havg : ∀ x r rs s, Inv x (r :: rs) s →
      G.estimate x (G.branch x r true s) + G.estimate x (G.branch x r false s) ≤
        G.estimate x s + G.estimate x s) :
    ComputableInPolyTime G.run encI encS ∧
      ∀ x, Inv x [] (G.run x) ∧ G.estimate x (G.run x) ≤ G.estimate x (G.init x) :=
  G.run_polyTime_spec hrounds hinit hbranch hestimate hle hpoly hgrowth Inv hinv_init hinv_branch
    fun x r rs s h => min_le_of_add_le_two_nsmul ((havg x r rs s h).trans_eq (two_nsmul _).symm)

end CombinedSpec

end PolyTimeGreedyInput

end Cslib.Computability

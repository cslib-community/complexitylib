/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Program
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Tactic.SuppCases

/-!
# A native adaptive pointer walk controlling three qubits

The controller retains one classical address bit. Each round requests the next address from a
classical service, reads at most one reply bit, and executes two NOT gates around one coherent
query. The NOT target is the address wire for a true reply and the response wire for a false
reply. Both branches therefore have the same separate operation costs. Empty replies select
false; later reply bits are never read. Discarded gate and query replies are never read either.

The device uses wire 0 for phase memory, wire 1 for the selected address, and wire 2 for the
oracle response. The oracle signature is two input bits and one response bit. Preparation
produces `|+⟩|0⟩|−⟩`; a final Hadamard and measurement read the phase memory. Quantum correctness
is a property of the device handler, separate from the native certificate proved here.

The controller is an existing `WordOracleComp`, and its single native certificate covers every
number of adaptive rounds and every stateful word oracle. No density matrix occurs in its
classically encoded state. This is original formalization infrastructure.

## Main definitions

* `Cslib.Quantum.PointerWalk.round`: one adaptive service and coherent-query round.
* `Cslib.Quantum.PointerWalk.walk`: the existing bounded iteration of that round.
* `Cslib.Quantum.PointerWalk.program`: preparation, the adaptive loop and terminal readout.

## Main results

* `Cslib.Quantum.PointerWalk.isOraclePPTOn_walk`: a single native certificate for the loop.
* `Cslib.Quantum.PointerWalk.isOraclePPT_program`: the complete parameterized controller.
* `Cslib.Quantum.PointerWalk.isCostBounded_program`: separate operation costs from arbitrary
  nonnegative weights on the four operation tags.
* `Cslib.Quantum.PointerWalk.transcript_cost_program`: every supported run has exactly those
  costs, independently of replies and the underlying stateful oracle.
-/

public section

namespace Cslib.Quantum.PointerWalk

open Cslib.Probability Turing.MultiTapeTM DeviceProgram

/-- The quantum device channels and one classical pointer-service channel. -/
abbrev Operation := DeviceOperation ⊕ Unit

/-- Select the classical address, query, then restore it. For a false address the two NOT gates
act on the response wire instead, giving the same operation count. -/
@[expose] def phase (address : Bool) : WordOracleComp Operation Bool := do
  let target := if address then 1 else 2
  gate (false, false, target, [])
  command (.inl .query) []
  gate (false, false, target, [])
  return address

/-- The classical service's reply selects the address used by the quantum query and by the next
service request. -/
@[expose] def round (address : Bool) : WordOracleComp Operation Bool := do
  let next ← requestBit (.inr ()) [address]
  phase next

/-- Execute the adaptive round `count` times, beginning at address false. -/
@[expose] def walk (count : ℕ) : WordOracleComp Operation Bool :=
  OracleComp.iterate count round false

/-- Prepare phase memory and the negative response eigenstate from the all-zero register. -/
@[expose] def prepare : WordOracleComp Operation Unit := do
  gate (false, false, 2, [])
  gate (false, true, 2, [])
  gate (false, true, 0, [])

/-- A single native controller, parameterized by the number of adaptive rounds. The auxiliary
classical word is unused; the device keeps all three qubits throughout the run. -/
@[expose] def program (count : ℕ) (_input : List Bool) : WordOracleComp Operation Bool := do
  prepare
  let _ ← walk count
  gate (false, true, 0, [])
  requestBit (.inl .measure) (encUnary 0)

/-- The phase subroutine's native machine branches only on its one-bit classical address. -/
theorem isOraclePPTOn_phase : IsOraclePPTOn encBool encBool phase := by
  apply IsOraclePPTOn.finite_cases' (branch := fun address _ => phase address)
    ComputableInPolyTime.id'
  intro address
  unfold phase
  exact (isOraclePPTOn_gate encBool _).bind
    ((isOraclePPTOn_command encUnit _ _).bind
      ((isOraclePPTOn_gate encUnit _).bind
        (ComputableInPolyTime.const address).isOraclePPTOn))

/-- The loop body reads one bounded service reply and makes its next query depend on it. -/
theorem isOraclePPTOn_round : IsOraclePPTOn encBool encBool round :=
  (isOraclePPTOn_requestBit encBool (.inr ()) (by fun_prop)).bind isOraclePPTOn_phase

/-- One native machine generates the entire adaptive loop. The encoded classical loop state has
length exactly one under every possible word reply, so its growth allowance is zero. -/
theorem isOraclePPTOn_walk : IsOraclePPTOn encUnary encBool walk := by
  refine IsOraclePPTOn.iterate_of_bounded_growth' (growth := 0)
    ComputableInPolyTime.id' (.const false) isOraclePPTOn_round ?_
  intro address next _
  simp only [encBool_apply, List.length_singleton, Nat.add_zero, le_refl]

private theorem isOraclePPTOn_prepare {α : Type} (input : α ↪ List Bool) :
    IsOraclePPTOn input encUnit (fun _ => prepare) :=
  (isOraclePPTOn_gate input _).bind
    ((isOraclePPTOn_gate encUnit _).bind (isOraclePPTOn_gate encUnit _))

/-- A native certificate for preparation, all adaptive rounds and terminal measurement. It
quantifies over arbitrary stateful word oracles, not only the intended quantum handler. -/
theorem isOraclePPT_program : IsOraclePPT encBool program := by
  apply IsOraclePPTOn.isOraclePPT
  unfold program
  apply (isOraclePPTOn_prepare (encPair encUnary encBits)).bind_with
  apply (isOraclePPTOn_walk.preprocess' (by fun_prop)).bind
  exact (isOraclePPTOn_gate encBool _).bind
    (isOraclePPTOn_requestBit encUnit (.inl .measure) (.const (encUnary 0)))

/-- Every address branch makes two elementary calls and one coherent query. -/
theorem isCostBounded_phase (cost : Operation → ℕ) (address : Bool) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun request => cost request.1))
      (phase address) (2 * cost (.inl .gate) + cost (.inl .query)) := by
  exact ((isCostBounded_command cost (.inl .gate) _).bind fun _ =>
    (isCostBounded_command cost (.inl .query) _).bind fun _ =>
      (isCostBounded_command cost (.inl .gate) _).bind fun _ =>
        OracleComp.IsCostBounded.pure address 0).mono (by omega)

/-- Each round has an independent classical-service call in addition to its quantum costs. -/
theorem isCostBounded_round (cost : Operation → ℕ) (address : Bool) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun request => cost request.1))
      (round address)
      (2 * cost (.inl .gate) + cost (.inl .query) + cost (.inr ())) :=
  ((isCostBounded_requestBit cost (.inr ()) _).bind
    (isCostBounded_phase cost)).mono (by omega)

/-- The weighted costs grow linearly with the number of adaptive rounds. -/
theorem isCostBounded_walk (cost : Operation → ℕ) (count : ℕ) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun request => cost request.1))
      (walk count)
      (count * (2 * cost (.inl .gate) + cost (.inl .query) + cost (.inr ()))) := by
  induction count with
  | zero =>
    rw [walk, OracleComp.iterate_zero, Nat.zero_mul]
    exact .pure false 0
  | succ count ih =>
    rw [walk, OracleComp.iterate_succ]
    simpa only [walk, Nat.succ_mul] using ih.bind (isCostBounded_round cost)

/-- Indicator weights recover the separate bounds: `2 * count + 4` elementary gates, `count`
coherent queries, `count` classical service calls and one measurement. -/
theorem isCostBounded_program (cost : Operation → ℕ) (count : ℕ) (input : List Bool) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun request => cost request.1))
      (program count input)
      ((2 * count + 4) * cost (.inl .gate) + count * cost (.inl .query) +
        count * cost (.inr ()) + cost (.inl .measure)) := by
  have hprepare :
      OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun request => cost request.1))
        prepare (3 * cost (.inl .gate)) :=
    ((isCostBounded_command cost (.inl .gate) _).bind fun _ =>
      (isCostBounded_command cost (.inl .gate) _).bind fun _ =>
        isCostBounded_command cost (.inl .gate) _).mono (by omega)
  exact (hprepare.bind fun _ => (isCostBounded_walk cost count).bind fun _ =>
    (isCostBounded_command cost (.inl .gate) _).bind fun _ =>
      isCostBounded_requestBit cost (.inl .measure) _).mono (by ring_nf; exact le_rfl)

private theorem transcript_cost_phase {State : Type} (cost : Operation → ℕ)
    (oracle : Operation × List Bool → StateT State PMF (List Bool))
    (address : Bool) {state final : State} {result : Bool}
    {before after : OracleComp.Transcript (fun _ : Operation × List Bool => List Bool)}
    (h : (result, final, after) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle) (phase address)
        (state, before)).support) :
    (after.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum =
      (before.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum +
        2 * cost (.inl .gate) + cost (.inl .query) := by
  supp_cases h [phase, gate, command, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    ProbOracleComp.runWith_pure, OracleComp.withTranscript]
  simp only [Prod.map_snd, id_eq, List.map_cons, List.sum_cons]
  omega

private theorem transcript_cost_round {State : Type} (cost : Operation → ℕ)
    (oracle : Operation × List Bool → StateT State PMF (List Bool))
    (address : Bool) {state final : State} {result : Bool}
    {before after : OracleComp.Transcript (fun _ : Operation × List Bool => List Bool)}
    (h : (result, final, after) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle) (round address)
        (state, before)).support) :
    (after.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum =
      (before.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum +
        (2 * cost (.inl .gate) + cost (.inl .query) + cost (.inr ())) := by
  rw [round, ProbOracleComp.runWith_bind] at h
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨⟨next, middle, seen⟩, hnext, hphase⟩ := h
  have hcost := transcript_cost_phase cost oracle next hphase
  supp_cases hnext [requestBit, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_query, OracleComp.withTranscript]
  simp only [List.map_cons, List.sum_cons] at hcost
  dsimp only [Prod.map, id] at hcost ⊢
  omega

private theorem transcript_cost_walk {State : Type} (cost : Operation → ℕ)
    (oracle : Operation × List Bool → StateT State PMF (List Bool)) (count : ℕ)
    {state final : State} {result : Bool}
    {before after : OracleComp.Transcript (fun _ : Operation × List Bool => List Bool)}
    (h : (result, final, after) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle) (walk count)
        (state, before)).support) :
    (after.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum =
      (before.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum +
        count * (2 * cost (.inl .gate) + cost (.inl .query) + cost (.inr ())) := by
  induction count generalizing state final result before after with
  | zero =>
    supp_cases h [walk, OracleComp.iterate_zero, ProbOracleComp.runWith_pure]
    simp only [Nat.zero_mul, Nat.add_zero]
  | succ count ih =>
    rw [walk, OracleComp.iterate_succ, ProbOracleComp.runWith_bind] at h
    rw [PMF.mem_support_bind_iff] at h
    obtain ⟨⟨next, middle, seen⟩, hwalk, hround⟩ := h
    have hfirst := ih hwalk
    have hlast := transcript_cost_round cost oracle next hround
    rw [Nat.succ_mul]
    omega

private theorem transcript_cost_prepare {State : Type} (cost : Operation → ℕ)
    (oracle : Operation × List Bool → StateT State PMF (List Bool))
    {state final : State} {result : Unit}
    {before after : OracleComp.Transcript (fun _ : Operation × List Bool => List Bool)}
    (h : (result, final, after) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle) prepare
        (state, before)).support) :
    (after.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum =
      (before.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum +
        3 * cost (.inl .gate) := by
  supp_cases h [prepare, gate, command, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    ProbOracleComp.runWith_pure, OracleComp.withTranscript]
  simp only [Prod.map_snd, id_eq, List.map_cons, List.sum_cons]
  omega

/-- Every supported execution has exactly the separate operation costs. Indicator weights count
each channel independently; this is stronger than existence of an execution attaining a bound. -/
theorem transcript_cost_program {State : Type} (cost : Operation → ℕ)
    (oracle : Operation × List Bool → StateT State PMF (List Bool))
    (count : ℕ) (input : List Bool) {state final : State} {result : Bool}
    {transcript : OracleComp.Transcript (fun _ : Operation × List Bool => List Bool)}
    (h : (result, final, transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle) (program count input)
        (state, [])).support) :
    (transcript.map fun ⟨⟨operation, _⟩, _⟩ => cost operation).sum =
      (2 * count + 4) * cost (.inl .gate) + count * cost (.inl .query) +
        count * cost (.inr ()) + cost (.inl .measure) := by
  rw [program, ProbOracleComp.runWith_bind] at h
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨⟨_, first, prepared⟩, hprepare, h⟩ := h
  rw [ProbOracleComp.runWith_bind] at h
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨⟨_, second, walked⟩, hwalk, h⟩ := h
  have hfirst := transcript_cost_prepare cost oracle hprepare
  have hsecond := transcript_cost_walk cost oracle count hwalk
  supp_cases h [gate, command, requestBit, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, OracleComp.withTranscript]
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at hfirst
  simp only [Prod.map_snd, id_eq, List.map_cons, List.sum_cons]
  rw [hsecond, hfirst]
  ring

end Cslib.Quantum.PointerWalk

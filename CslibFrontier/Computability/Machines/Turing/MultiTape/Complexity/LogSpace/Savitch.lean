/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.RadixRounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Foundations.Data.BitString.ShortWords
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.Counter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Tactic.Space
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Savitch's theorem for general space bounds

A nondeterministic machine whose computation paths on an input of length `n` visit at most `S`
work cells is simulated by a deterministic machine within space `O((S + log₂ n + 1) ^ 2)`: this is
Savitch's theorem [Savitch1970]. No constructibility of `S` is assumed; as in Sipser's proof of
Theorem 8.5 [Sipser2013], the machine tries growing bounds. The simulation runs Savitch's midpoint
recursion with an explicit stack (`Cslib.Reachability.Savitch.step`) on the compact configuration
graph of the machine (`Turing.MultiTapeNTM.ConfigurationGraph`), whose vertices omit the input. A
vertex of the graph of radix `B` is stored as a word of `W = O(log B)` bits, so the stack of at
most `W` frames has `O(W ^ 2)` bits. The input is never copied: the simulation is a query machine
(`Turing.QueryMachine`), which reads one input bit per step, and the edge test at the bottom of the
recursion needs exactly one input bit, at the input head of its source vertex.

The space bound `S` is not computed. The machine counts the input in binary and then tries the
radices `roundRadix State n j = 4 ^ j * startRadix State n` of
`Turing.MultiTapeNTM.ConfigurationGraph.roundRadix` in turn, the radices of Immerman's inductive
counting for nondeterministic space; Sipser's proof of Theorem 8.5 likewise tries the space bounds
`1, 2, 3, …` and checks whether the machine uses more. In round `j`, a first recursion asks
whether an overflowing vertex, one with a step leaving the radix, is reachable from the start
vertex; if it is, the machine moves on to round `j + 1`. Otherwise every reachable view fits the
radix, and a second recursion on the same graph asks whether an accepting halted vertex is
reachable, which decides acceptance. A machine
within space `S` has no reachable overflow from round `4 * S + 1` on
(`Turing.MultiTapeNTM.ConfigurationGraph.fits_roundRadix_of_runsInSpace`), so every round has
vertices of `O(S + log₂ n + 1)` bits. To have a single target, the graph on words gains a sink, the
word of `W` ones: every target vertex steps to it
(`Turing.MultiTapeNTM.SquareSavitch.sinkReach_eq_true_iff`).

The sublinear form of Savitch's theorem is the extension stated in the final paragraph of
Section 8.4 of Sipser's third edition, just before Section 8.5 (p. 351): "We can extend Savitch's
theorem to hold for sublinear space bounds down to f(n) ≥ log n." Sipser's Theorem 8.5 itself
assumes `f(n) ≥ n`, and Arora and Barak's Theorem 4.14 assumes a space-constructible bound
`S(n) ≥ log n`. In the extension, the machine has a read-only input tape, and the configurations of
the machine on the input `w` record the state, the work tapes and the head positions but not `w`.
Here these are the vertices of the compact configuration graph, and the query machine reads the one
input bit an edge test needs. The sources state the theorem for languages decided by
nondeterministic machines whose branches all halt; the statement here also covers machines that
only recognize the problem (branches may run forever), arbitrary per-instance bounds without
constructibility, and arbitrary instances under an encoding into `List Bool`.

## Main definitions

* `Turing.MultiTapeNTM.SquareSavitch.wordEdge`: the edges of the graph on words, given the round
  mode and the input bit at the source.
* `Turing.MultiTapeNTM.SquareSavitch.sinkReach`: the recursion from the start vertex to the sink.
* `Turing.MultiTapeNTM.SquareSavitch.machine`: the deterministic query machine.
* `Turing.MultiTapeNTM.SquareSavitch.Runtime`: named runtime fields with generated encodings and
  certificates.

## Main results

* `Turing.MultiTapeNTM.SquareSavitch.sinkReach_true_iff`,
  `Turing.MultiTapeNTM.SquareSavitch.sinkReach_false_iff`: the recursion decides reachable overflow,
  and without it acceptance.
* `Turing.MultiTapeNTM.exists_decidableInTimeAndSpace_sq`: **Savitch's theorem**: a problem
  recognized by a nondeterministic machine within space `S` is decided by a deterministic machine
  within space `O((S + log₂ n + 1) ^ 2)`.
* `Turing.MultiTapeNTM.SquareSavitch.exists_halted`,
  `Turing.MultiTapeNTM.SquareSavitch.length_encRuntime_le`: the machine halts, and its states have
  `O((S + log₂ n + 1) ^ 2)` bits.

## References

* [W. J. Savitch, *Relationships between nondeterministic and deterministic tape
  complexities*][Savitch1970]; journal text not inspected (paywalled), so no theorem number or
  page is cited.
* [M. Sipser, *Introduction to the Theory of Computation*, 3rd edition, Theorem 8.5 and its proof,
  and Section 8.4, final paragraph (p. 351)][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.14][AroraBarak09]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
-/

@[expose] public section

namespace Turing.MultiTapeNTM.SquareSavitch

open MultiTapeTM ConfigurationGraph Cslib.Reachability Cslib.Reachability.Savitch
open Cslib.BitString (lowBits length_lowBits lsbValue_replicate_true)

/-! ### The graph on words -/

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)

/-- The targets of a round, given the input bit `symbol` at the vertex: the overflowing vertices
in overflow mode, and the accepting halted vertices otherwise. -/
noncomputable def target (overflowMode : Bool) (B n : ℕ) (symbol : Option Bool) (u : ℕ) : Bool :=
  if overflowMode then overflow ntm B n u symbol else bad (k := k) (State := State) B n u

/-- **The edges of the graph on words**, given the round mode and the input bit `symbol` at the
source: the edges of the compact configuration graph between the values of the words, and an edge
from every target vertex to the sink, the word of ones. -/
noncomputable def wordEdge (overflowMode : Bool) (B n : ℕ) (symbol : Option Bool)
    (u v : List Bool) : Bool :=
  edgeWithSymbol ntm B n (ofBits u) (ofBits v) symbol ||
    (target ntm overflowMode B n symbol (ofBits u) && v.all id)

/-- The edges of the graph on words, with the round mode, the radix, the input length and the
input bit as one parameter. -/
noncomputable def paramEdge (p : Bool × ℕ × ℕ × Option Bool) : List Bool → List Bool → Bool :=
  wordEdge ntm p.1 p.2.1 p.2.2.1 p.2.2.2

/-- The edges of the graph on words on the input `w`: the input bit is read at the input head of
the source. -/
noncomputable def inputEdge (overflowMode : Bool) (B : ℕ) (w : List Bool) (u v : List Bool) :
    Bool :=
  wordEdge ntm overflowMode B w.length w[queryIndex (k := k) B (ofBits u)]? u v

/-- The target test on an actual input, reading the bit at `queryIndex`. -/
def Target (overflowMode : Bool) (B : ℕ) (w : List Bool) (u : ℕ) : Prop :=
  target ntm overflowMode B w.length w[queryIndex (k := k) B u]? u = true

/-- **The recursion of a round**: Savitch's midpoint recursion at depth `W = vertexWidth k B` on
the graph on words of width `W`, from the start vertex to the sink. -/
noncomputable def sinkReach (overflowMode : Bool) (B : ℕ) (w : List Bool) : Bool :=
  reach (inputEdge ntm overflowMode B w) (vertexWidth k B) (vertexWidth k B)
    (lowBits (vertexWidth k B) (startID ntm B)) (List.replicate (vertexWidth k B) true)

/-- Some overflowing vertex is reachable in the graph of radix `B`. -/
def OverflowReachable (B : ℕ) (w : List Bool) : Prop :=
  ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧ Overflow ntm B w u

/-! ### Reachability of the sink -/

section Graph

variable {ntm} {B : ℕ} {w : List Bool}

/-- No vertex is the sink. -/
theorem vertexBound_le_ofBits_sink (B : ℕ) :
    vertexBound (k := k) B ≤ ofBits (List.replicate (vertexWidth k B) true) := by
  have h := lsbValue_replicate_true (vertexWidth k B)
  have := vertexBound_lt_two_pow_vertexWidth k B
  rw [ofBits_eq_lsbValue]
  omega

/-- Every target is a vertex of the graph. -/
theorem lt_vertexBound_of_target {overflowMode : Bool} {n u : ℕ} {symbol : Option Bool}
    (h : target ntm overflowMode B n symbol u = true) : u < vertexBound (k := k) B := by
  cases overflowMode
  · simp only [target, Bool.false_eq_true, ↓reduceIte, bad, Bool.and_eq_true] at h
    exact lt_vertexBound_of_valid h.1.1
  · simp only [target, ↓reduceIte, overflow, Bool.and_eq_true] at h
    exact lt_vertexBound_of_valid h.1

/-- **The sink is reachable exactly when a target is.** Along the graph on words of width
`W = vertexWidth k B`, from the start vertex to the word of `W` ones. -/
theorem reflTransGen_sink_iff {overflowMode : Bool}
    (hstart : startID ntm B < vertexBound (k := k) B) :
    Relation.ReflTransGen (fun a b => a.length = vertexWidth k B ∧ b.length = vertexWidth k B ∧
        inputEdge ntm overflowMode B w a b = true)
      (lowBits (vertexWidth k B) (startID ntm B)) (List.replicate (vertexWidth k B) true) ↔
      ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
        Target ntm overflowMode B w u := by
  have hW := vertexBound_lt_two_pow_vertexWidth k B
  have hsink := vertexBound_le_ofBits_sink (k := k) B
  set W := vertexWidth k B
  have hsrc : ofBits (lowBits W (startID ntm B)) = startID ntm B :=
    ofBits_lowBits (hstart.trans hW)
  constructor
  · intro h
    have key : ∀ x, Relation.ReflTransGen (fun a b => a.length = W ∧ b.length = W ∧
          inputEdge ntm overflowMode B w a b = true) (lowBits W (startID ntm B)) x →
        (∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
          Target ntm overflowMode B w u) ∨
        (Relation.ReflTransGen (Edge ntm B w) (startID ntm B) (ofBits x) ∧
          x ≠ List.replicate W true) := by
      intro x hx
      induction hx with
      | refl =>
        refine .inr ⟨by rw [hsrc], fun h => ?_⟩
        have := congrArg ofBits h
        omega
      | @tail x y _ hxy ih =>
        obtain ⟨-, -, he⟩ := hxy
        rcases ih with ih | ⟨hr, -⟩
        · exact .inl ih
        simp only [inputEdge, wordEdge, Bool.or_eq_true, Bool.and_eq_true] at he
        rcases he with he | ⟨hb, -⟩
        · refine .inr ⟨hr.tail he, fun h => ?_⟩
          have := (lt_vertexBound_of_edgeWithSymbol he).2
          rw [h] at this
          omega
        · exact .inl ⟨_, hr, hb⟩
    rcases key _ h with h | ⟨-, h⟩
    · exact h
    · exact absurd rfl h
  · rintro ⟨u, hu, hb⟩
    have key : ∀ x, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) x →
        Relation.ReflTransGen (fun a b => a.length = W ∧ b.length = W ∧
          inputEdge ntm overflowMode B w a b = true) (lowBits W (startID ntm B)) (lowBits W x) ∧
        x < vertexBound (k := k) B := by
      intro x hx
      induction hx with
      | refl => exact ⟨.refl, hstart⟩
      | @tail a b _ hab ih =>
        have hlt := lt_vertexBound_of_edgeWithSymbol hab
        refine ⟨ih.1.tail ⟨length_lowBits _ _, length_lowBits _ _, ?_⟩, hlt.2⟩
        simp only [inputEdge, wordEdge, ofBits_lowBits (hlt.1.trans hW),
          ofBits_lowBits (hlt.2.trans hW)]
        rw [show edgeWithSymbol ntm B w.length a b w[queryIndex (k := k) B a]? = true from hab,
          Bool.true_or]
    have hu' : u < vertexBound (k := k) B := lt_vertexBound_of_target hb
    have hb' : target ntm overflowMode B w.length w[queryIndex (k := k) B u]? u = true := hb
    refine (key u hu).1.tail ⟨length_lowBits _ _, List.length_replicate, ?_⟩
    simp only [inputEdge, wordEdge, ofBits_lowBits (hu'.trans hW), hb', Bool.true_and,
      Bool.or_eq_true]
    exact .inr (by simp)

/-- **The recursion of a round decides whether a target is reachable**, for every radix above the
finite tags. -/
theorem sinkReach_eq_true_iff {overflowMode : Bool} (hB : Fintype.card (Option State) + 1 < B) :
    sinkReach ntm overflowMode B w = true ↔
      ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
        Target ntm overflowMode B w u := by
  have hstart := startID_lt (ntm := ntm) (k := k) hB
  have hsrc : (lowBits (vertexWidth k B) (startID ntm B)).length = vertexWidth k B :=
    length_lowBits _ _
  have hcard : {x | Relation.ReflTransGen (fun a b => a.length = vertexWidth k B ∧
      b.length = vertexWidth k B ∧ inputEdge ntm overflowMode B w a b = true)
      (lowBits (vertexWidth k B) (startID ntm B)) x}.encard ≤ 2 ^ vertexWidth k B + 1 := by
    refine (Set.encard_le_encard fun x hx => ?_).trans
      ((Cslib.BitString.encard_setOf_length_eq _).le.trans le_self_add)
    induction hx with
    | refl => exact hsrc
    | tail _ hstep _ => exact hstep.2.1
  rw [sinkReach, reach_iff hsrc List.length_replicate,
    ← Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le hcard,
    reflTransGen_sink_iff hstart]

/-- **The overflow round decides reachable overflow.** -/
theorem sinkReach_true_iff (hB : Fintype.card (Option State) + 1 < B) :
    sinkReach ntm true B w = true ↔ OverflowReachable ntm B w :=
  sinkReach_eq_true_iff hB

/-- **Without reachable overflow, the acceptance round decides acceptance.** -/
theorem sinkReach_false_iff (hB : Fintype.card (Option State) + 1 < B)
    (hno : ¬ OverflowReachable ntm B w) :
    sinkReach ntm false B w = true ↔ ntm.Accepts w := by
  rw [accepts_iff_reachable_bad
    (fits_of_not_overflow (fits_init hB) fun u hu ho => hno ⟨u, hu, ho⟩),
    sinkReach_eq_true_iff hB]
  rfl

/-- **The late rounds have no reachable overflow**: for a machine within space `S`, from round
`4 * S + 1` on. -/
theorem not_overflowReachable_of_runsInSpace {S j : ℕ} (hs : ntm.RunsInSpace w S)
    (hj : 4 * S + 1 ≤ j) : ¬ OverflowReachable ntm (roundRadix State w.length j) w :=
  fun ⟨u, hu, ho⟩ => not_overflow_of_fits
    (fun _ hv => fits_roundRadix_of_runsInSpace hs hj hv) u hu ho

end Graph

/-! ### The query machine -/

/-- The encoding of the parameter of the edge test: the round mode, the radix and the input length
in binary, and the input bit read last. -/
abbrev encParam : Bool × ℕ × ℕ × Option Bool ↪ List Bool :=
  encPair encBool (encPair encNat (encPair encNat (encOption encBool)))

/-- Edge-test parameters, with the input bit read last. -/
structure EdgeParams where
  /-- Whether the round searches for overflow, rather than for acceptance. -/
  overflowMode : Bool
  /-- Radix used to encode the simulated machine registers. -/
  radix : ℕ
  /-- Length of the original read-only input. -/
  inputLength : ℕ
  /-- Input bit just read, or `none` beyond the input. -/
  symbol : Option Bool

/-- The parameters and unary vertex width share one frame. -/
structure RoundSetup where
  /-- Parameters shared by all edge tests in this round. -/
  params : EdgeParams
  /-- Bit width of vertices, stored in unary. -/
  width : ℕ

/-- A round of midpoint recursion. -/
structure SimulationRound where
  /-- Edge-test parameters and vertex width. -/
  setup : RoundSetup
  /-- Current continuation stack and recursion register. -/
  recursion : Savitch.State

/-- The input counter, startup flag, and current simulation round. -/
structure Runtime where
  /-- Number of input bits counted; the input length after startup. -/
  counter : ℕ
  /-- Whether input counting has finished and recursion has started. -/
  started : Bool
  /-- Current midpoint-recursion round. -/
  round : SimulationRound

/-- Round mode, binary radix and input length followed by the optional input bit, in field
order. -/
enc_structure encEdgeParams : EdgeParams where
  overflowMode : encBool, radix : encNat, inputLength : encNat, symbol : (encOption encBool)
/-- Framed edge parameters followed by the unary vertex width. -/
enc_structure encRoundSetup : RoundSetup where params : encEdgeParams, width : encUnary
/-- Framed round setup followed by the encoded recursion state. -/
enc_structure encSimulationRound : SimulationRound where setup : encRoundSetup, recursion : encState
/-- Binary counter, startup bit and simulation round, in field order. -/
enc_structure encRuntime : Runtime where
  counter : encNat, started : encBool, round : encSimulationRound

/-- Enter the named runtime representation at the generic Savitch round boundary. -/
def SimulationRound.ofRound (q : ((Bool × ℕ × ℕ × Option Bool) × ℕ) × Savitch.State) :
    SimulationRound := ⟨⟨⟨q.1.1.1, q.1.1.2.1, q.1.1.2.2.1, q.1.1.2.2.2⟩, q.1.2⟩, q.2⟩

/-- The first state of a round of the given mode and radix, on inputs of length `n`: the call at
depth `W` from the start vertex to the sink. The start vertex is written as the binary digits of
its value plus `2 ^ W`, without the last one (`Turing.MultiTapeTM.bits_add_two_pow`). -/
noncomputable def initRound (overflowMode : Bool) (B n : ℕ) :
    ((Bool × ℕ × ℕ × Option Bool) × ℕ) × Savitch.State :=
  (((overflowMode, B, n, none), vertexWidth k B),
    ⟨[], .call (vertexWidth k B) (startID ntm B + 2 ^ vertexWidth k B).bits.dropLast
      (List.replicate (vertexWidth k B) true)⟩)

/-- The round held while the input is counted. -/
def idle : ((Bool × ℕ × ℕ × Option Bool) × ℕ) × Savitch.State :=
  (((false, 0, 0, none), 0), ⟨[], .ret false⟩)

/-- The source of the pending call, if any. -/
def callSource (st : Savitch.State) : List Bool := (st.reg.toPair.1.getD (0, [], [])).2.1

/-- The recursion has returned its value. -/
def returned (st : Savitch.State) : Bool := st.stack.isEmpty && !st.reg.toPair.1.isSome

/-- The round has returned, and it is an overflow round: the next round starts. -/
def restarts (s : Runtime) : Bool := s.round.setup.params.overflowMode && returned s.round.recursion

variable (k) in
/-- The input bit to read: the next input position while counting, then the input head of the
source of the pending call. -/
noncomputable def query (s : Runtime) : ℕ :=
  if s.started then
    queryIndex (k := k) s.round.setup.params.radix (ofBits (callSource s.round.recursion))
  else s.counter

/-- A step of the machine, given the input bit read: count the input until its end, then start the
overflow round of the first radix. An overflow round that returns `true` starts the overflow round
of the next radix; one that returns `false` starts the acceptance round of the same radix. Other
steps run the recursion, with the bit read as the input bit of the edge test. -/
noncomputable def next (p : Runtime × Option Bool) : Runtime :=
  if p.1.started then
    if restarts p.1 then
      ⟨p.1.counter, true, .ofRound (initRound ntm p.1.round.recursion.reg.toPair.2
        (if p.1.round.recursion.reg.toPair.2 then 4 * p.1.round.setup.params.radix
          else p.1.round.setup.params.radix) p.1.counter)⟩
    else
      ⟨p.1.counter, true, .ofRound (roundStep (paramEdge ntm)
        (((p.1.round.setup.params.overflowMode, p.1.round.setup.params.radix,
          p.1.round.setup.params.inputLength, p.2), p.1.round.setup.width),
          p.1.round.recursion))⟩
  else if p.2.isSome then ⟨p.1.counter + 1, false, p.1.round⟩
  else ⟨p.1.counter, true, .ofRound (initRound ntm true (startRadix State p.1.counter) p.1.counter)⟩

/-- The machine halts once an acceptance round has returned. -/
def halted (s : Runtime) : Bool :=
  s.started && !s.round.setup.params.overflowMode && returned s.round.recursion

/-- The answer: the value returned by the recursion. -/
def finish (s : Runtime) : List Bool := [s.round.recursion.reg.toPair.2]

/-- **The deterministic simulation**, as a query machine: count the input, then run Savitch's
recursion on the graphs on words of growing radix, reading the input bit of each edge test. -/
noncomputable def machine : QueryMachine Runtime where
  init := ⟨0, false, .ofRound idle⟩
  query := query k
  next := next ntm
  emit _ := []
  halted := halted
  finish := finish

/-! ### The runs of the machine -/

section Run

variable {ntm} (w : List Bool)

/-- The step of the recursion only uses the edge test at a call at level `0`. -/
theorem step_congr {e₁ e₂ : List Bool → List Bool → Bool} {W : ℕ} {st : Savitch.State}
    (h : ∀ u v, st.reg = .call 0 u v → e₁ u v = e₂ u v) :
    Savitch.step e₁ W st = Savitch.step e₂ W st := by
  obtain ⟨stack, (⟨_ | i, u, v⟩ | b)⟩ := st
  · simp only [Savitch.step, h u v rfl]
  · rfl
  · cases stack <;> cases b <;> rfl

/-- The machine emits nothing before its final answer. -/
theorem output_eq (t : ℕ) : (machine ntm).output w t = finish ((machine ntm).run w t) := by
  rw [QueryMachine.output]
  conv_rhs => rw [← List.nil_append (finish _)]
  congr 1
  simp only [List.flatten_eq_nil_iff, List.mem_map]
  rintro _ ⟨i, -, rfl⟩
  split <;> rfl

/-- While counting, the machine holds the number of input bits read. -/
theorem run_of_le {t : ℕ} (ht : t ≤ w.length) :
    (machine ntm).run w t = ⟨t, false, .ofRound idle⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.run_succ, ih (by omega)]
    have hread : (machine ntm).read w ⟨t, false, .ofRound idle⟩ = some w[t] := by
      simp [QueryMachine.read, machine, query,
        List.getElem?_eq_getElem (show t < w.length by omega)]
    rw [QueryMachine.step, hread]
    simp [machine, halted, next]

/-- At the end of the input, the machine starts the overflow round of the first radix. -/
theorem run_length_succ :
    (machine ntm).run w (w.length + 1) =
      ⟨w.length, true, .ofRound (initRound ntm true (startRadix State w.length) w.length)⟩ := by
  rw [QueryMachine.run_succ, run_of_le w le_rfl]
  have hread : (machine ntm).read w ⟨w.length, false, .ofRound idle⟩ = none := by
    simp [QueryMachine.read, machine, query]
  rw [QueryMachine.step, hread]
  simp [machine, halted, next]

/-- The value of a returned recursion is the value of its register. -/
theorem returned_eq_true_iff {st : Savitch.State} :
    returned st = true ↔ ∃ b, st = ⟨[], .ret b⟩ := by
  obtain ⟨stack, (⟨i, u, v⟩ | b)⟩ := st
  · simp [returned, Reg.toPair]
  · cases stack <;> simp [returned, Reg.toPair]

/-- **A step of a round that has not returned** runs the recursion, with the input bit at the
source of the pending call. -/
theorem step_round {mode : Bool} {B : ℕ} {symbol : Option Bool} {st : Savitch.State}
    (h : returned st = false) :
    (machine ntm).step w ⟨w.length, true, .ofRound (((mode, B, w.length, symbol),
        vertexWidth k B), st)⟩ =
      ⟨w.length, true, .ofRound (((mode, B, w.length,
        w[queryIndex (k := k) B (ofBits (callSource st))]?), vertexWidth k B),
        Savitch.step (inputEdge ntm mode B w) (vertexWidth k B) st)⟩ := by
  have hh : halted (⟨w.length, true, .ofRound (((mode, B, w.length, symbol),
      vertexWidth k B), st)⟩ : Runtime) = false := by
    simp [halted, SimulationRound.ofRound, h]
  have hr : restarts (⟨w.length, true, .ofRound (((mode, B, w.length, symbol),
      vertexWidth k B), st)⟩ : Runtime) = false := by
    simp [restarts, SimulationRound.ofRound, h]
  simp only [QueryMachine.step, machine, hh, Bool.false_eq_true, ↓reduceIte, next, hr,
    QueryMachine.read, query]
  have hstep : Savitch.step (wordEdge ntm mode B w.length
      w[queryIndex (k := k) B (ofBits (callSource st))]?) (vertexWidth k B) st =
      Savitch.step (inputEdge ntm mode B w) (vertexWidth k B) st :=
    step_congr fun u v hreg => by simp [inputEdge, callSource, hreg, Reg.toPair]
  simp only [roundStep, paramEdge, SimulationRound.ofRound, hstep]

/-- **A returned overflow round starts the next round**: the overflow round of the next radix if
it returned `true`, and the acceptance round of the same radix otherwise. -/
theorem step_restart {B : ℕ} {symbol : Option Bool} {b : Bool} :
    (machine ntm).step w ⟨w.length, true, .ofRound (((true, B, w.length, symbol),
        vertexWidth k B), ⟨[], .ret b⟩)⟩ =
      ⟨w.length, true, .ofRound (initRound ntm b (if b then 4 * B else B) w.length)⟩ :=
  rfl

/-- A returned acceptance round has halted. -/
theorem halted_round {B : ℕ} {symbol : Option Bool} {b : Bool} :
    halted ⟨w.length, true, .ofRound (((false, B, w.length, symbol), vertexWidth k B),
      ⟨[], .ret b⟩)⟩ = true := rfl

/-- The first state of a round, once the start vertex is known to have a word. -/
theorem initRound_snd {mode : Bool} {B : ℕ} (hB : Fintype.card (Option State) + 1 < B) :
    (initRound ntm mode B w.length).2 = ⟨[], .call (vertexWidth k B)
      (lowBits (vertexWidth k B) (startID ntm B)) (List.replicate (vertexWidth k B) true)⟩ := by
  rw [initRound, dropLast_bits_add_two_pow
    ((startID_lt hB).trans (vertexBound_lt_two_pow_vertexWidth k B))]

/-- **A returned round holds the value of its recursion.** -/
theorem ret_eq_sinkReach {mode : Bool} {B : ℕ} (hB : Fintype.card (Option State) + 1 < B) {i : ℕ}
    {b : Bool} (h : (Savitch.step (inputEdge ntm mode B w) (vertexWidth k B))^[i]
      (initRound ntm mode B w.length).2 = ⟨[], .ret b⟩) :
    b = sinkReach ntm mode B w := by
  rw [initRound_snd w hB] at h
  obtain ⟨T, -, hT⟩ := exists_iterate_step_call (edge := inputEdge ntm mode B w)
    (w := vertexWidth k B) (vertexWidth k B) (lowBits (vertexWidth k B) (startID ntm B))
    (List.replicate (vertexWidth k B) true) []
  rcases le_total i T with hiT | hTi
  · rw [← Nat.sub_add_cancel hiT, Function.iterate_add_apply, h,
      Function.iterate_fixed rfl] at hT
    cases hT
    rfl
  · rw [← Nat.sub_add_cancel hTi, Function.iterate_add_apply, hT,
      Function.iterate_fixed rfl] at h
    cases h
    rfl

/-- **A round runs to its return**: from the first state of a round, the machine runs the
recursion until it returns the value `sinkReach`. -/
theorem exists_run_returned {mode : Bool} {B t₀ : ℕ} (hB : Fintype.card (Option State) + 1 < B)
    (h₀ : (machine ntm).run w t₀ =
      ⟨w.length, true, .ofRound (initRound ntm mode B w.length)⟩) :
    ∃ t symbol, (machine ntm).run w t = ⟨w.length, true, .ofRound (((mode, B, w.length, symbol),
      vertexWidth k B), ⟨[], .ret (sinkReach ntm mode B w)⟩)⟩ := by
  have hex : ∃ i, returned ((Savitch.step (inputEdge ntm mode B w) (vertexWidth k B))^[i]
      (initRound ntm mode B w.length).2) = true := by
    obtain ⟨T, -, hT⟩ := exists_iterate_step_call (edge := inputEdge ntm mode B w)
      (w := vertexWidth k B) (vertexWidth k B) (lowBits (vertexWidth k B) (startID ntm B))
      (List.replicate (vertexWidth k B) true) []
    exact ⟨T, by rw [initRound_snd w hB, hT]; rfl⟩
  have hrun : ∀ i ≤ Nat.find hex, ∃ symbol, (machine ntm).run w (t₀ + i) =
      ⟨w.length, true, .ofRound (((mode, B, w.length, symbol), vertexWidth k B),
        (Savitch.step (inputEdge ntm mode B w) (vertexWidth k B))^[i]
          (initRound ntm mode B w.length).2)⟩ := by
    intro i hi
    induction i with
    | zero => exact ⟨none, h₀⟩
    | succ i ih =>
      obtain ⟨symbol, hs⟩ := ih (by omega)
      have hr : returned ((Savitch.step (inputEdge ntm mode B w) (vertexWidth k B))^[i]
          (initRound ntm mode B w.length).2) = false := by
        simpa using Nat.find_min hex (show i < Nat.find hex by omega)
      rw [← Nat.add_assoc, QueryMachine.run_succ, hs, step_round w hr,
        Function.iterate_succ_apply']
      exact ⟨_, rfl⟩
  obtain ⟨symbol, hs⟩ := hrun _ le_rfl
  obtain ⟨b, hb⟩ := returned_eq_true_iff.mp (Nat.find_spec hex)
  refine ⟨t₀ + Nat.find hex, symbol, ?_⟩
  rw [hs, hb, ← ret_eq_sinkReach w hB hb]

/-- **The states of a run**: counting the input, or a round of radix `roundRadix State n j`,
after overflow rounds that found overflow at every earlier radix. An acceptance round has no
reachable overflow at its radix. -/
def RunState (s : Runtime) : Prop :=
  (∃ t ≤ w.length, s = ⟨t, false, .ofRound idle⟩) ∨
    ∃ (mode : Bool) (j i : ℕ) (symbol : Option Bool),
      (∀ j' < j, OverflowReachable ntm (roundRadix State w.length j') w) ∧
      (mode = false → ¬ OverflowReachable ntm (roundRadix State w.length j) w) ∧
      s = ⟨w.length, true, .ofRound (((mode, roundRadix State w.length j, w.length, symbol),
        vertexWidth k (roundRadix State w.length j)),
        (Savitch.step (inputEdge ntm mode (roundRadix State w.length j) w)
          (vertexWidth k (roundRadix State w.length j)))^[i]
          (initRound ntm mode (roundRadix State w.length j) w.length).2)⟩

/-- The machine keeps the states of a run. -/
theorem runState_step {s : Runtime} (h : RunState (ntm := ntm) w s) :
    RunState (ntm := ntm) w ((machine ntm).step w s) := by
  rcases h with ⟨t, ht, rfl⟩ | ⟨mode, j, i, symbol, hlt, hmode, rfl⟩
  · rcases ht.lt_or_eq with ht | rfl
    · refine .inl ⟨t + 1, ht, ?_⟩
      rw [← run_of_le (ntm := ntm) w ht.le, ← QueryMachine.run_succ, run_of_le w ht]
    · refine .inr ⟨true, 0, 0, none, fun _ h => absurd h (Nat.not_lt_zero _), by simp, ?_⟩
      rw [← run_of_le (ntm := ntm) w le_rfl, ← QueryMachine.run_succ, run_length_succ,
        roundRadix_zero]
      rfl
  · have hB := card_lt_roundRadix (State := State) w.length j
    cases hr : returned ((Savitch.step (inputEdge ntm mode (roundRadix State w.length j) w)
        (vertexWidth k (roundRadix State w.length j)))^[i]
        (initRound ntm mode (roundRadix State w.length j) w.length).2) with
    | false =>
      rw [step_round w hr, ← Function.iterate_succ_apply'
        (Savitch.step (inputEdge ntm mode (roundRadix State w.length j) w)
          (vertexWidth k (roundRadix State w.length j)))]
      exact .inr ⟨mode, j, i + 1, _, hlt, hmode, rfl⟩
    | true =>
      obtain ⟨b, hb⟩ := returned_eq_true_iff.mp hr
      have hbv := ret_eq_sinkReach w hB hb
      rw [hb]
      cases mode with
      | false =>
        refine .inr ⟨false, j, i, symbol, hlt, hmode, ?_⟩
        rw [hb]
        simp only [QueryMachine.step, machine, halted_round, ↓reduceIte]
      | true =>
        rw [step_restart]
        cases b with
        | true =>
          have ho := (sinkReach_true_iff hB).mp hbv.symm
          refine .inr ⟨true, j + 1, 0, none, fun j' hj' => ?_, by simp, ?_⟩
          · rcases (Nat.lt_succ_iff.mp hj').lt_or_eq with hj' | rfl
            · exact hlt j' hj'
            · exact ho
          · rw [roundRadix_succ]
            rfl
        | false =>
          have hno : ¬ OverflowReachable ntm (roundRadix State w.length j) w := fun ho =>
            Bool.false_ne_true (hbv.trans ((sinkReach_true_iff hB).mpr ho))
          exact .inr ⟨false, j, 0, none, hlt, fun _ => hno, rfl⟩

/-- Every state of the run is a state of a run. -/
theorem runState_run (t : ℕ) : RunState (ntm := ntm) w ((machine ntm).run w t) := by
  induction t with
  | zero => exact .inl ⟨0, Nat.zero_le _, rfl⟩
  | succ t ih => rw [QueryMachine.run_succ]; exact runState_step w ih

/-- **A halted machine has decided acceptance.** -/
theorem answer_iff_of_halted {s : Runtime} (h : RunState (ntm := ntm) w s)
    (hh : halted s = true) : s.round.recursion.reg.toPair.2 = true ↔ ntm.Accepts w := by
  rcases h with ⟨t, -, rfl⟩ | ⟨mode, j, i, symbol, -, hmode, rfl⟩
  · simp [halted] at hh
  · have hB := card_lt_roundRadix (State := State) w.length j
    cases mode with
    | true => simp [halted, SimulationRound.ofRound] at hh
    | false =>
      have hr : returned ((Savitch.step (inputEdge ntm false (roundRadix State w.length j) w)
          (vertexWidth k (roundRadix State w.length j)))^[i]
          (initRound ntm false (roundRadix State w.length j) w.length).2) = true := by
        simpa [halted, SimulationRound.ofRound] using hh
      obtain ⟨b, hb⟩ := returned_eq_true_iff.mp hr
      simp only [SimulationRound.ofRound, hb, Reg.toPair]
      rw [ret_eq_sinkReach w hB hb]
      exact sinkReach_false_iff hB (hmode rfl)

/-- A returned overflow round leads to a halted machine or to the overflow round of the next
radix, after reachable overflow. -/
theorem halted_or_next_round {j t₀ : ℕ}
    (h₀ : (machine ntm).run w t₀ = ⟨w.length, true, .ofRound
      (initRound ntm true (roundRadix State w.length j) w.length)⟩) :
    (∃ t, halted ((machine ntm).run w t) = true) ∨
      (OverflowReachable ntm (roundRadix State w.length j) w ∧ ∃ t₁,
        (machine ntm).run w t₁ = ⟨w.length, true, .ofRound
          (initRound ntm true (roundRadix State w.length (j + 1)) w.length)⟩) := by
  have hB := card_lt_roundRadix (State := State) w.length j
  obtain ⟨t, symbol, ht⟩ := exists_run_returned w hB h₀
  have hnext := (QueryMachine.run_succ _ w t).trans (by rw [ht, step_restart])
  cases hb : sinkReach ntm true (roundRadix State w.length j) w with
  | false =>
    rw [hb] at hnext
    obtain ⟨t', symbol', ht'⟩ := exists_run_returned w hB hnext
    exact .inl ⟨t', by rw [ht']; exact halted_round w⟩
  | true =>
    rw [hb] at hnext
    refine .inr ⟨(sinkReach_true_iff hB).mp hb, t + 1, ?_⟩
    rw [hnext, roundRadix_succ]
    rfl

/-- **The machine halts** on the inputs of a machine within some space bound. -/
theorem exists_halted {S : ℕ} (hs : ntm.RunsInSpace w S) :
    ∃ t, halted ((machine ntm).run w t) = true := by
  suffices key : ∀ m j t₀, 4 * S + 1 ≤ j + m →
      (machine ntm).run w t₀ = ⟨w.length, true, .ofRound
        (initRound ntm true (roundRadix State w.length j) w.length)⟩ →
      ∃ t, halted ((machine ntm).run w t) = true from
    key (4 * S + 1) 0 (w.length + 1) (by omega) (by rw [run_length_succ, roundRadix_zero])
  intro m
  induction m with
  | zero =>
    intro j t₀ hj h₀
    rcases halted_or_next_round w h₀ with h | ⟨ho, -⟩
    · exact h
    · exact absurd ho (not_overflowReachable_of_runsInSpace hs (by omega))
  | succ m ih =>
    intro j t₀ hj h₀
    rcases halted_or_next_round w h₀ with h | ⟨-, t₁, h₁⟩
    · exact h
    · exact ih (j + 1) t₁ (by omega) h₁

end Run

/-! ### The size of the states -/

section Size

variable {ntm} {w : List Bool}

/-- A run within space `S` stays below round `4 * S + 1`. -/
theorem le_of_overflowReachable {S j : ℕ} (hs : ntm.RunsInSpace w S)
    (hlt : ∀ j' < j, OverflowReachable ntm (roundRadix State w.length j') w) : j ≤ 4 * S + 1 := by
  by_contra h
  exact not_overflowReachable_of_runsInSpace hs le_rfl (hlt _ (by omega))

/-- The states of the recursion satisfy the invariant of a run at depth `W`. -/
theorem invariant_iterate_initRound {mode : Bool} {B : ℕ}
    (hB : Fintype.card (Option State) + 1 < B) (i : ℕ) :
    Invariant (vertexWidth k B) (vertexWidth k B)
      ((Savitch.step (inputEdge ntm mode B w) (vertexWidth k B))^[i]
        (initRound ntm mode B w.length).2) := by
  refine invariant_iterate _ ?_ i
  rw [initRound_snd w hB]
  refine ⟨trivial, fun i u v h => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
  exact ⟨by simp, length_lowBits _ _, List.length_replicate⟩

/-- The runtime's framing cost, separated from the encoded recursion state. -/
theorem length_encRuntime (s : Runtime) :
    (encRuntime s).length = 2 * (encNat s.counter).length +
      8 * (encNat s.round.setup.params.radix).length +
      8 * (encNat s.round.setup.params.inputLength).length +
      4 * (encOption encBool s.round.setup.params.symbol).length +
      2 * s.round.setup.width + 27 + (encState s.round.recursion).length := by
  enc_len [encRuntime_apply, encSimulationRound_apply, encRoundSetup_apply, encEdgeParams_apply,
    encRuntimeFields, encSimulationRoundFields, encRoundSetupFields, encEdgeParamsFields]

variable (k State) in
/-- The constant factor of the width of the vertices in the rounds of a run. -/
noncomputable def widthConst : ℕ :=
  Fintype.card (Register k) * (Fintype.card (Option State) + 8) + 1

variable (k State) in
/-- The constant of the bound on the states of the machine. -/
noncomputable def sizeConst : ℕ :=
  (encState (⟨[], .ret false⟩ : Savitch.State)).length + 47 +
    8 * (Fintype.card (Option State) + 9) + 2 * widthConst k State +
    24 * (widthConst k State + 1) * (widthConst k State + widthConst k State + 1)

/-- **The states of a run have `O((S + log₂ n + 1) ^ 2)` bits**, for a machine within space
`S`. -/
theorem length_encRuntime_le {S : ℕ} (hs : ntm.RunsInSpace w S) {s : Runtime}
    (h : RunState (ntm := ntm) w s) :
    (encRuntime s).length ≤ sizeConst k State * (S + Nat.log2 w.length + 1) ^ 2 := by
  have hL1 : 1 ≤ S + Nat.log2 w.length + 1 := by omega
  have hLL : S + Nat.log2 w.length + 1 ≤ (S + Nat.log2 w.length + 1) ^ 2 :=
    Nat.le_self_pow two_ne_zero _
  rcases h with ⟨t, ht, rfl⟩ | ⟨mode, j, i, symbol, hlt, -, rfl⟩
  · have h₁ := length_encNat_le_log2 ht
    have h₀ : (encNat 0).length = 0 := by simp
    have hnone : (encOption encBool none).length ≤ 2 := by simp
    have hE : (encState (⟨[], .ret false⟩ : Savitch.State)).length + 47 ≤ sizeConst k State := by
      unfold sizeConst
      omega
    rw [length_encRuntime]
    simp only [SimulationRound.ofRound, idle]
    calc _ ≤ ((encState (⟨[], .ret false⟩ : Savitch.State)).length + 47) *
          (S + Nat.log2 w.length + 1) := by
          nlinarith [Nat.mul_le_mul_left (encState (⟨[], .ret false⟩ : Savitch.State)).length hL1]
      _ ≤ sizeConst k State * (S + Nat.log2 w.length + 1) ^ 2 := Nat.mul_le_mul hE hLL
  · have hB := card_lt_roundRadix (State := State) w.length j
    have hj := le_of_overflowReachable hs hlt
    have hinv := invariant_iterate_initRound (ntm := ntm) (w := w) (mode := mode) hB i
    have hn := length_encNat_le_log2 (le_refl w.length)
    have hBl : (encNat (roundRadix State w.length j)).length ≤
        2 * j + Nat.log2 w.length + Fintype.card (Option State) + 5 := by
      rw [length_encNat_eq_size, Nat.size_le]
      exact (roundRadix_le_two_pow (State := State) w.length j).trans_lt
        (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hW := vertexWidth_roundRadix_le k State w.length j
    have hsym : (encOption encBool symbol).length ≤ 2 := by cases symbol <;> simp
    rw [length_encRuntime]
    simp only [SimulationRound.ofRound]
    unfold sizeConst
    have hW' : vertexWidth k (roundRadix State w.length j) ≤
        widthConst k State * (S + Nat.log2 w.length + 1) := by
      unfold widthConst
      generalize Fintype.card (Register k) = R at *
      generalize Fintype.card (Option State) = q at *
      have : 2 * j + Nat.log2 w.length + q + 4 ≤ (q + 8) * (S + Nat.log2 w.length + 1) := by
        nlinarith
      nlinarith
    have hBl' : (encNat (roundRadix State w.length j)).length ≤
        (Fintype.card (Option State) + 9) * (S + Nat.log2 w.length + 1) := by
      generalize Fintype.card (Option State) = q at *
      nlinarith
    have hst := length_encState_le_of_bounds hinv hW' hW' hL1
    have hn' : (encNat w.length).length ≤ S + Nat.log2 w.length + 1 := by omega
    generalize (encState (⟨[], .ret false⟩ : Savitch.State)).length = E at *
    generalize widthConst k State = Wc at *
    generalize vertexWidth k (roundRadix State w.length j) = W at *
    generalize (encNat (roundRadix State w.length j)).length = Bl at *
    generalize (encNat w.length).length = nl at *
    generalize (encOption encBool symbol).length = sl at *
    generalize Fintype.card (Option State) = q at *
    generalize S + Nat.log2 w.length + 1 = L at *
    generalize (encState _).length = E' at *
    have hlin : 2 * nl + 8 * Bl + 8 * nl + 4 * sl + 2 * W + 27 ≤
        (E + 47 + 8 * (q + 9) + 2 * Wc) * L ^ 2 := by
      have : (E + 47 + 8 * (q + 9) + 2 * Wc) * L ≤ (E + 47 + 8 * (q + 9) + 2 * Wc) * L ^ 2 :=
        Nat.mul_le_mul_left _ hLL
      nlinarith [Nat.zero_le (E * L)]
    nlinarith

end Size

/-! ### The parts of the machine in linear space -/

section Parts

open ComputableInSpace

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

/-- The fields of a state of the recursion, as pairs. -/
theorem stateFields_inSpace :
    ComputableInSpace (fun st : Savitch.State => (st.stack, st.reg.toPair)) encState
      (encPair (encList encFrame) (encPair (encOption encCall) encBool))
      fun st => (encState st).length :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

/-- The stack, within a budget. -/
theorem budget_stack {st : α → Savitch.State} (h : ComputableInSpace st enc encState S) :
    ComputableInSpace (fun a => (st a).stack) enc (encList encFrame) S :=
  (budget_comp_linear stateFields_inSpace h).fst'

/-- The register as a pair, within a budget. -/
theorem budget_reg {st : α → Savitch.State} (h : ComputableInSpace st enc encState S) :
    ComputableInSpace (fun a => (st a).reg.toPair) enc (encPair (encOption encCall) encBool) S :=
  (budget_comp_linear stateFields_inSpace h).snd'

/-- The value of the source of the pending call, within a budget. -/
theorem budget_callSource {st : α → Savitch.State} (h : ComputableInSpace st enc encState S) :
    ComputableInSpace (fun a => ofBits (callSource (st a))) enc encNat S := by
  exact budget_comp_linear (of_inO ComputableInO.bitsToNat)
    (budget_optionGetD (0, [], []) (budget_reg h).fst').snd'.fst'

/-- Whether the recursion has returned, within a budget. -/
theorem budget_returned {st : α → Savitch.State} (h : ComputableInSpace st enc encState S) :
    ComputableInSpace (fun a => returned (st a)) enc encBool S :=
  (budget_finite (fun p : Bool × Bool => p.1 && !p.2)
    (budget_prod (budget_isEmpty (budget_stack h))
      (budget_optionIsSome (budget_reg h).fst'))).of_enc_eq fun _ => rfl

attribute [local fun_prop] budget_stack budget_reg budget_callSource budget_returned
  queryIndex_budget

/-- The input position to read, in space linear in the state. -/
theorem query_inSpace :
    ComputableInSpace (query k) encRuntime encNat fun s => (encRuntime s).length := by
  space [query]

/-- The halting test, in space linear in the state. -/
theorem halted_inSpace :
    ComputableInSpace halted encRuntime encBool fun s => (encRuntime s).length := by
  exact (budget_finite (fun p : Bool × Bool × Bool => p.1 && !p.2.1 && p.2.2)
    (show ComputableInSpace
      (fun s : Runtime => (s.started, s.round.setup.params.overflowMode,
        returned s.round.recursion)) encRuntime
      (encPair encBool (encPair encBool encBool)) (fun s => (encRuntime s).length)
      from by space)).of_enc_eq fun _ => rfl

/-- The restart test, in space linear in the state. -/
theorem restarts_inSpace :
    ComputableInSpace restarts encRuntime encBool fun s => (encRuntime s).length := by
  exact (budget_finite (fun p : Bool × Bool => p.1 && p.2)
    (show ComputableInSpace
      (fun s : Runtime => (s.round.setup.params.overflowMode, returned s.round.recursion))
      encRuntime (encPair encBool encBool) (fun s => (encRuntime s).length)
      from by space)).of_enc_eq fun _ => rfl

/-- The answer, in space linear in the state. -/
theorem finish_inSpace :
    ComputableInSpace finish encRuntime encBits fun s => (encRuntime s).length := by
  exact (show ComputableInSpace (fun s : Runtime => s.round.recursion.reg.toPair.2)
    encRuntime encBool (fun s => (encRuntime s).length) from by space).of_enc_eq fun _ => rfl

/-- The edge test of the graph on words, in linear space. -/
theorem paramEdge_inSpace : ComputableInSpace
    (fun q : (Bool × ℕ × ℕ × Option Bool) × List Bool × List Bool =>
      paramEdge ntm q.1 q.2.1 q.2.2)
    (encPair encParam (encPair encBits encBits)) encBool
    fun q => (encPair encParam (encPair encBits encBits) q).length := by
  have hp := fst encParam (encPair encBits encBits)
  have huv := snd encParam (encPair encBits encBits)
  have hmode := hp.fst'
  have hrest := hp.snd'
  have hB := hrest.fst'
  have hrest' := hrest.snd'
  have hn := hrest'.fst'
  have hsym := hrest'.snd'
  have hu := huv.fst'
  have hv := huv.snd'
  have hvalU := budget_comp_linear (of_inO ComputableInO.bitsToNat) hu
  have hvalV := budget_comp_linear (of_inO ComputableInO.bitsToNat) hv
  have hin : (fun q : (Bool × ℕ × ℕ × Option Bool) × List Bool × List Bool =>
      (encPair encParam (encPair encBits encBits) q).length) ≼ _ := .refl _
  have he := edgeWithSymbol_budget ntm hB hn hvalU hvalV hsym hin
  have ho := overflow_budget ntm hB hn hvalU hsym hin
  have hb := bad_budget (k := k) (State := State) hB hn hvalU hin
  have hall := budget_comp_linear
    (of_inO (.of_linear (.of_transducer (encIn := encBits) (encMid := encBool)
      (f := fun l : List Bool => l.all id) Savitch.allT fun l => by
        rw [Savitch.allT_run]; rfl))) hv
  exact (budget_finite
    (fun p : Bool × Bool × Bool × Bool × Bool => p.1 || ((if p.2.1 then p.2.2.1 else p.2.2.2.1) &&
      p.2.2.2.2))
    (budget_prod he (budget_prod hmode (budget_prod ho (budget_prod hb hall))))).of_enc_eq
    fun _ => rfl

/-- A round of the recursion on the graph on words, in space linear in the round. -/
theorem roundStep_inSpace : ComputableInSpace (roundStep (paramEdge ntm)) (encRound encParam)
    (encRound encParam) fun q => (encRound encParam q).length := by
  obtain ⟨Te, hedge⟩ := (paramEdge_inSpace ntm).exists_inO
  refine (of_inO (computableInO_roundStep hedge)).weaken (.of_le_linear 3 0 fun q => ?_)
  rcases h : q.2.reg with ⟨i, u, v⟩ | b
  · have hreg := length_encReg_call i u v
    have hst := length_encState q.2
    rw [h, hreg] at hst
    simp only [Reg.edgeCost, encRound, length_encPair, encBits_apply] at hst ⊢
    omega
  · simp only [Reg.edgeCost]
    omega

/-- The first state of a round, from the mode, the radix and the input length, within a
budget. -/
theorem initRound_budget {mode : α → Bool} {B n : α → ℕ}
    (hmode : ComputableInSpace mode enc encBool S) (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S) (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => initRound ntm (mode a) (B a) (n a)) enc (encRound encParam) S := by
  have hN := vertexBound_budget (k := k) hB hin
  have hW₀ := budget_comp_linear natSizeUnary hN
  have hW : ComputableInSpace (fun a => vertexWidth k (B a)) enc encUnary S :=
    hW₀.of_enc_eq fun _ => rfl
  have hstart := startID_budget ntm hB hin
  have hpow₀ : ComputableInSpace (fun W : ℕ => 2 ^ W) encUnary encNat
      fun W => (encUnary W).length := by
    simpa only [encUnary_apply, List.length_replicate] using
      of_inO (ComputableInDegree.two_pow_length encUnary).inO_one
  have hpow := budget_comp_linear hpow₀ hW
  have hbits : ComputableInSpace
      (fun a => (startID ntm (B a) + 2 ^ vertexWidth k (B a)).bits) enc encBits S :=
    (budget_natAdd hstart hpow).of_enc_eq fun _ => rfl
  have hsrc := budget_comp_linear (of_inO ComputableInDegree.bitsDropLast.inO_one) hbits
  have hsink : ComputableInSpace (fun a => List.replicate (vertexWidth k (B a)) true) enc
      encBits S := hW.of_enc_eq fun _ => rfl
  have hcall := budget_optionSome (budget_prod hW (budget_prod hsrc hsink))
  have hstate : ComputableInSpace (fun a => (initRound ntm (mode a) (B a) (n a)).2) enc encState
      S :=
    (budget_prod (budget_const (encB := encList encFrame) [] hin)
      (budget_prod hcall (budget_const (encB := encBool) false hin))).of_enc_eq fun _ => rfl
  exact (budget_prod (budget_prod (budget_prod hmode (budget_prod hB (budget_prod hn
    (budget_const (encB := encOption encBool) none hin)))) hW) hstate).of_enc_eq fun _ => rfl

/-- The first radix, within a budget. -/
theorem startRadix_budget {n : α → ℕ} (hn : ComputableInSpace n enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => startRadix State (n a)) enc encNat S :=
  budget_natMul (budget_natAdd hn (budget_const 2 hin)) (budget_const _ hin)

attribute [local fun_prop] initRound_budget startRadix_budget

/-- A step of the machine, in space linear in the state and the bit read. -/
theorem next_inSpace : ComputableInSpace (next ntm)
    (encPair encRuntime (encOption encBool)) encRuntime
    fun p => (encPair encRuntime (encOption encBool) p).length := by
  have hstep := roundStep_inSpace ntm
  have hrestart := restarts_inSpace
  have hconvert : ComputableInSpace SimulationRound.ofRound (encRound encParam)
      encSimulationRound (fun q => (encRound encParam q).length) :=
    of_inO (ComputableInO.of_eq fun _ => rfl)
  space [next]

end Parts

end Turing.MultiTapeNTM.SquareSavitch

namespace Turing.MultiTapeNTM

open MultiTapeTM ConfigurationGraph SquareSavitch

/-- **Savitch's theorem** [Savitch1970], for general space bounds. No constructibility is assumed:
the machine tries growing bounds, as in Sipser's proof of Theorem 8.5 [Sipser2013]. A
problem recognized by a nondeterministic machine whose computation paths on `enc a` visit at most
`S a` work cells, and whose branches need not halt, is decided by a deterministic machine within
space `O((S a + log₂ |enc a| + 1) ^ 2)`: Savitch's midpoint recursion on the compact configuration
graphs of the machine of growing radix (`Turing.MultiTapeNTM.SquareSavitch.machine`). -/
theorem exists_decidableInTimeAndSpace_sq {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {k : ℕ} {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State} {S : α → ℕ}
    (hA : ntm.RecognizesInSpace enc A S) :
    ∃ t c, DecidableInTimeAndSpace A enc t
      fun a => c * (S a + Nat.log2 (enc a).length + 1) ^ 2 := by
  classical
  let : Fintype State := Fintype.ofFinite State
  have hex (a : α) : ∃ t, (machine ntm).halted ((machine ntm).run (enc a) t) = true :=
    exists_halted (enc a) (hA a).1
  have hhalt (a : α) := Nat.find_spec (hex a)
  have hpre (a : α) : ∀ t < Nat.find (hex a),
      (machine ntm).halted ((machine ntm).run (enc a) t) = false := fun t ht => by
    simpa using Nat.find_min (hex a) ht
  have hf (a : α) :
      encBool (decide (a ∈ A)) = (machine ntm).output (enc a) (Nat.find (hex a)) := by
    rw [output_eq, encBool_apply, finish]
    congr 1
    rw [Bool.eq_iff_iff, answer_iff_of_halted (enc a) (runState_run (enc a) _) (hhalt a),
      decide_eq_true_iff]
    exact (hA a).2
  obtain ⟨t, c, h⟩ := (machine ntm).computableInSpace query_inSpace (next_inSpace ntm)
    (ComputableInSpace.const []) halted_inSpace finish_inSpace (fun a => Nat.find (hex a))
    hhalt hpre hf (fun a => (S a + Nat.log2 (enc a).length + 1) ^ 2)
    (fun a => (show Nat.log2 (enc a).length + 1 ≤ S a + Nat.log2 (enc a).length + 1 by omega).trans
      (Nat.le_self_pow two_ne_zero _))
    ⟨sizeConst k State, fun a t _ => length_encRuntime_le (hA a).1 (runState_run (enc a) t)⟩
  exact ⟨t, c, decidableInTimeAndSpace_iff.mpr ⟨_, h, fun a => by simp⟩⟩

end Turing.MultiTapeNTM

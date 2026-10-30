/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Complexity.Foundations.Data.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Foundations.Data.BitString.ShortWords
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.BitString.Counter
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/-!
# Savitch's theorem in space `log² n`

A nondeterministic machine whose computation paths on inputs of length `n` visit at most
`c * (log₂ n + 1)` work cells is simulated by a deterministic machine within space
`O((log₂ n + 1) ^ 2)` [Savitch1970]. The simulation runs Savitch's midpoint recursion with an
explicit stack (`Cslib.Reachability.Savitch.step`) on the compact configuration graph of the
machine (`Turing.MultiTapeNTM.ConfigurationGraph`), whose vertices are numbers below
`(n + 2) ^ O(1)` that omit the input. A vertex is stored as a word of `W = O(log n)` bits, so the
stack of at most `W` frames has `O(W ^ 2)` bits. The input is never copied: the simulation is a
query machine (`Turing.QueryMachine`), which reads one input bit per step, and the edge test at
the bottom of the recursion needs exactly one input bit, at the input head of its source vertex.

The machine first counts the input in binary, then fixes the radix `(n + 2) ^ D` of the graph
and the width `W` of its vertices. To have a single target, the graph on words gains a sink, the
word of `W` ones: every accepting halted vertex steps to it. The recursion at depth `W` then
decides whether the sink is reachable from the start vertex, that is, whether the machine accepts
(`Turing.MultiTapeNTM.LogSquareSavitch.reach_eq_true_iff`).

The sublinear form of Savitch's theorem is the extension stated in the final paragraph of
Section 8.4 of Sipser's third edition, just before Section 8.5 (p. 351): "We can extend Savitch's
theorem to hold for sublinear space bounds down to f(n) ≥ log n." Sipser's Theorem 8.5 itself
assumes `f(n) ≥ n`. In the extension, the machine has a read-only input tape, and the
configurations of the machine on the input `w` record the state, the work tapes and the head
positions but not `w`. Here these are the vertices of the compact configuration graph, which omit
the input, and the query machine reads the one input bit an edge test needs. The source states
the theorem for every `f(n) ≥ log n` and for languages decided by nondeterministic machines whose
branches all halt; this file proves only the case `f(n) = c * (log₂ n + 1)`, but for machines that
only recognize the problem (branches may run forever), on arbitrary instances under an encoding
into `List Bool`.

## Main definitions

* `Turing.MultiTapeNTM.LogSquareSavitch.wordEdge`: the edges of the graph on words, given the
  input bit at the source.
* `Turing.MultiTapeNTM.LogSquareSavitch.machine`: the deterministic query machine.

## Main results

* `Turing.MultiTapeNTM.LogSquareSavitch.reach_eq_true_iff`: the recursion decides acceptance.
* `Turing.MultiTapeNTM.exists_decidableInTimeAndSpace_log_sq`: **Savitch's theorem in space
  `log² n`**: a problem recognized by a nondeterministic machine in space `c * (log₂ n + 1)` is
  decided by a deterministic machine in space `O((log₂ n + 1) ^ 2)`.
* `Turing.MultiTapeNTM.LogSquareSavitch.exists_run_add`,
  `Turing.MultiTapeNTM.LogSquareSavitch.length_encRuntime_run_le`: the machine runs the recursion,
  and its states have `O((log₂ n + 1) ^ 2)` bits.

## References

* [W. J. Savitch, *Relationships between nondeterministic and deterministic tape
  complexities*][Savitch1970]
* [M. Sipser, *Introduction to the Theory of Computation*, 3rd edition, Section 8.4, final
  paragraph (p. 351)][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeNTM.LogSquareSavitch

open MultiTapeTM ConfigurationGraph Cslib.Reachability Cslib.Reachability.Savitch
open Cslib.BitString (lowBits length_lowBits lsbValue_lowBits lsbValue_eq_foldr_bit
  lsbValue_replicate_true)

/-! ### The graph on words -/

/-- The value of the `W` low-order digits of `x < 2 ^ W` is `x`. -/
private theorem ofBits_lowBits {W x : ℕ} (hx : x < 2 ^ W) :
    ofBits (lowBits W x) = x :=
  (lsbValue_eq_foldr_bit _).symm.trans (lsbValue_lowBits hx)

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)

variable (k) in
/-- The width of the words for the vertices of the graph of radix `B`. -/
noncomputable def width (B : ℕ) : ℕ := (vertexBound (k := k) B).size

/-- **The edges of the graph on words**, given the input bit `symbol` at the source: the edges of
the compact configuration graph between the values of the words, and an edge from every accepting
halted vertex to the sink, the word of ones. -/
noncomputable def wordEdge (B n : ℕ) (symbol : Option Bool) (u v : List Bool) : Bool :=
  edgeWithSymbol ntm B n (ofBits u) (ofBits v) symbol ||
    (bad (k := k) (State := State) B n (ofBits u) && v.all id)

/-- The edges of the graph on words, with the radix, the input length and the input bit as one
parameter. -/
noncomputable def paramEdge (p : ℕ × ℕ × Option Bool) : List Bool → List Bool → Bool :=
  wordEdge ntm p.1 p.2.1 p.2.2

/-- The edges of the graph on words on the input `w`: the input bit is read at the input head of
the source. -/
noncomputable def inputEdge (B : ℕ) (w : List Bool) (u v : List Bool) : Bool :=
  wordEdge ntm B w.length w[queryIndex (k := k) B (ofBits u)]? u v

/-! ### Reachability of the sink -/

section Graph

variable {ntm} {B : ℕ} {w : List Bool}

variable (k) in
/-- Every vertex of the graph of radix `B` has a word of width `width k B`. -/
theorem vertexBound_lt_two_pow_width (B : ℕ) : vertexBound (k := k) B < 2 ^ width k B :=
  Nat.lt_size_self _

/-- No vertex is the sink. -/
theorem vertexBound_le_ofBits_sink (B : ℕ) :
    vertexBound (k := k) B ≤ ofBits (List.replicate (width k B) true) := by
  have h := lsbValue_replicate_true (width k B)
  rw [lsbValue_eq_foldr_bit] at h
  have := vertexBound_lt_two_pow_width k B
  change _ ≤ (List.replicate _ true).foldr Nat.bit 0
  omega

/-- **The sink is reachable exactly when an accepting halted vertex is.** Along the graph on words
of width `W = width k B`, from the start vertex to the word of `W` ones. -/
theorem reflTransGen_sink_iff (hstart : startID ntm B < vertexBound (k := k) B) :
    Relation.ReflTransGen (fun a b => a.length = width k B ∧ b.length = width k B ∧
        inputEdge ntm B w a b = true)
      (lowBits (width k B) (startID ntm B)) (List.replicate (width k B) true) ↔
      ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
        bad (k := k) (State := State) B w.length u = true := by
  have hW := vertexBound_lt_two_pow_width k B
  have hsink := vertexBound_le_ofBits_sink (k := k) B
  set W := width k B
  have hsrc : ofBits (lowBits W (startID ntm B)) = startID ntm B :=
    ofBits_lowBits (hstart.trans hW)
  constructor
  · intro h
    have key : ∀ x, Relation.ReflTransGen (fun a b => a.length = W ∧ b.length = W ∧
          inputEdge ntm B w a b = true) (lowBits W (startID ntm B)) x →
        (∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
          bad (k := k) (State := State) B w.length u = true) ∨
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
          inputEdge ntm B w a b = true) (lowBits W (startID ntm B)) (lowBits W x) ∧
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
    have hu' : u < vertexBound (k := k) B := by
      simp only [bad, Bool.and_eq_true] at hb
      exact lt_vertexBound_of_valid hb.1.1
    refine (key u hu).1.tail ⟨length_lowBits _ _, List.length_replicate, ?_⟩
    simp only [inputEdge, wordEdge, ofBits_lowBits (hu'.trans hW), hb, Bool.true_and,
      Bool.or_eq_true]
    exact .inr (by simp)

/-- **The recursion decides acceptance.** For a machine whose computation paths on `w` visit at
most `c * (log₂ |w| + 1)` work cells, Savitch's midpoint recursion at depth `W` on the graph on
words of width `W`, from the start vertex to the sink, decides whether the machine accepts `w`. -/
theorem reach_eq_true_iff {c : ℕ} (hs : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1))) :
    reach (inputEdge ntm (radix (radixExponent State c) w.length) w)
        (width k (radix (radixExponent State c) w.length))
        (width k (radix (radixExponent State c) w.length))
        (lowBits (width k (radix (radixExponent State c) w.length))
          (startID ntm (radix (radixExponent State c) w.length)))
        (List.replicate (width k (radix (radixExponent State c) w.length)) true) = true ↔
      ntm.Accepts w := by
  set B := radix (radixExponent State c) w.length
  set W := width k B
  have hstart : startID ntm B < vertexBound (k := k) B := by
    rw [← vertexID_init ntm B w]
    exact vertexID_lt (fits_of_runsInSpace c hs .refl)
  have hsrc : (lowBits W (startID ntm B)).length = W := length_lowBits _ _
  have hcard : {x | Relation.ReflTransGen (fun a b => a.length = W ∧ b.length = W ∧
      inputEdge ntm B w a b = true) (lowBits W (startID ntm B)) x}.encard ≤ 2 ^ W + 1 := by
    refine (Set.encard_le_encard fun x hx => ?_).trans
      ((Cslib.BitString.encard_setOf_length_eq _).le.trans le_self_add)
    induction hx with
    | refl => exact hsrc
    | tail _ hstep _ => exact hstep.2.1
  rw [reach_iff hsrc List.length_replicate,
    ← Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le hcard,
    reflTransGen_sink_iff hstart, accepts_iff_reachable_bad_of_runsInSpace c hs]

end Graph

/-! ### The query machine -/

/-- The encoding of the parameter of the edge test: the radix and the input length in binary, and
the input bit read last. -/
abbrev encParam : ℕ × ℕ × Option Bool ↪ List Bool :=
  encPair encNat (encPair encNat (encOption encBool))

/-- The states of the machine: the input counter, which becomes the input length; whether the
recursion has started; and a round of the recursion, with its parameter and width. -/
abbrev Runtime := ℕ × Bool × ((ℕ × ℕ × Option Bool) × ℕ) × Savitch.State

/-- The encoding of the states of the machine. -/
abbrev encRuntime : Runtime ↪ List Bool := encPair encNat (encPair encBool (encRound encParam))

/-- The first round of the recursion on inputs of length `n`, for the radix `(n + 2) ^ D`: the
call at depth `W` from the start vertex to the sink. The start vertex is written as the binary
digits of its value plus `2 ^ W`, without the last one (`Turing.MultiTapeTM.bits_add_two_pow`). -/
noncomputable def initRound (D n : ℕ) : ((ℕ × ℕ × Option Bool) × ℕ) × Savitch.State :=
  (((radix D n, n, none), width k (radix D n)),
    ⟨[], .call (width k (radix D n))
      (startID ntm (radix D n) + 2 ^ width k (radix D n)).bits.dropLast
      (List.replicate (width k (radix D n)) true)⟩)

/-- The round held while the input is counted. -/
def idle : ((ℕ × ℕ × Option Bool) × ℕ) × Savitch.State := (((0, 0, none), 0), ⟨[], .ret false⟩)

/-- The source of the pending call, if any. -/
def callSource (st : Savitch.State) : List Bool := (st.reg.toPair.1.getD (0, [], [])).2.1

variable (k) in
/-- The input bit to read: the next input position while counting, then the input head of the
source of the pending call. -/
noncomputable def query (s : Runtime) : ℕ :=
  if s.2.1 then queryIndex (k := k) s.2.2.1.1.1 (ofBits (callSource s.2.2.2)) else s.1

/-- A step of the machine, given the input bit read: count the input until its end, then start
the recursion, then run its rounds with the bit read as the input bit of the edge test. -/
noncomputable def next (D : ℕ) (p : Runtime × Option Bool) : Runtime :=
  if p.1.2.1 then
    (p.1.1, true, roundStep (paramEdge ntm)
      (((p.1.2.2.1.1.1, p.1.2.2.1.1.2.1, p.2), p.1.2.2.1.2), p.1.2.2.2))
  else if p.2.isSome then (p.1.1 + 1, false, p.1.2.2)
  else (p.1.1, true, initRound ntm D p.1.1)

/-- The machine halts once the recursion has returned. -/
def halted (s : Runtime) : Bool :=
  s.2.1 && s.2.2.2.stack.isEmpty && !s.2.2.2.reg.toPair.1.isSome

/-- The answer: the value returned by the recursion. -/
def finish (s : Runtime) : List Bool := [s.2.2.2.reg.toPair.2]

/-- **The deterministic simulation**, as a query machine: count the input, then run Savitch's
recursion on the graph on words of the radix `(n + 2) ^ D`, reading the input bit of each edge
test. -/
noncomputable def machine (D : ℕ) : QueryMachine Runtime where
  init := (0, false, idle)
  query := query k
  next := next ntm D
  emit _ := []
  halted := halted
  finish := finish

/-! ### The runs of the machine -/

section Run

variable {ntm} {D : ℕ} (w : List Bool)

/-- The step of the recursion only uses the edge test at a call at level `0`. -/
theorem step_congr {e₁ e₂ : List Bool → List Bool → Bool} {W : ℕ} {st : Savitch.State}
    (h : ∀ u v, st.reg = .call 0 u v → e₁ u v = e₂ u v) :
    Savitch.step e₁ W st = Savitch.step e₂ W st := by
  obtain ⟨stack, (⟨_ | i, u, v⟩ | b)⟩ := st
  · simp only [Savitch.step, h u v rfl]
  · rfl
  · cases stack <;> cases b <;> rfl

/-- The machine emits nothing before its final answer. -/
theorem output_eq (t : ℕ) : (machine ntm D).output w t = finish ((machine ntm D).run w t) := by
  rw [QueryMachine.output]
  conv_rhs => rw [← List.nil_append (finish _)]
  congr 1
  simp only [List.flatten_eq_nil_iff, List.mem_map]
  rintro _ ⟨i, -, rfl⟩
  split <;> rfl

/-- While counting, the machine holds the number of input bits read. -/
theorem run_of_le {t : ℕ} (ht : t ≤ w.length) : (machine ntm D).run w t = (t, false, idle) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.run_succ, ih (by omega)]
    have hread : (machine ntm D).read w (t, false, idle) = some w[t] := by
      simp [QueryMachine.read, machine, query,
        List.getElem?_eq_getElem (show t < w.length by omega)]
    rw [QueryMachine.step, hread]
    simp [machine, halted, next]

/-- At the end of the input, the machine starts the recursion. -/
theorem run_length_succ :
    (machine ntm D).run w (w.length + 1) = (w.length, true, initRound ntm D w.length) := by
  rw [QueryMachine.run_succ, run_of_le w le_rfl]
  have hread : (machine ntm D).read w (w.length, false, idle) = none := by
    simp [QueryMachine.read, machine, query]
  rw [QueryMachine.step, hread]
  simp [machine, halted, next]

/-- **The machine runs the recursion** on the graph on words of the input, with the input bit of
each edge test read at the source of its call. -/
theorem exists_run_add (j : ℕ) : ∃ symbol, (machine ntm D).run w (w.length + 1 + j) =
    (w.length, true, (((radix D w.length, w.length, symbol), width k (radix D w.length)),
      (Savitch.step (inputEdge ntm (radix D w.length) w) (width k (radix D w.length)))^[j]
        (initRound ntm D w.length).2)) := by
  induction j with
  | zero => exact ⟨none, run_length_succ w⟩
  | succ j ih =>
    obtain ⟨symbol, ih⟩ := ih
    set st := (Savitch.step (inputEdge ntm (radix D w.length) w) (width k (radix D w.length)))^[j]
      (initRound ntm D w.length).2
    rw [← Nat.add_assoc, QueryMachine.run_succ, ih, Function.iterate_succ_apply']
    by_cases hh : halted (w.length, true, (((radix D w.length, w.length, symbol),
        width k (radix D w.length)), st)) = true
    · refine ⟨symbol, ?_⟩
      have hst : ∃ b, st = ⟨[], .ret b⟩ := by
        obtain ⟨stack, (⟨i, u, v⟩ | b)⟩ := st
        · simp [halted, Reg.toPair] at hh
        · simp only [halted, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff,
            Bool.not_eq_eq_eq_not, Bool.not_true] at hh
          exact ⟨b, by rw [hh.1]⟩
      obtain ⟨b, hb⟩ := hst
      have hfix : Savitch.step (inputEdge ntm (radix D w.length) w) (width k (radix D w.length))
          st = st := by
        rw [hb]; rfl
      rw [hfix, QueryMachine.step]
      simp only [show (machine ntm D).halted _ = true from hh, ↓reduceIte]
    · refine ⟨w[queryIndex (k := k) (radix D w.length) (ofBits (callSource st))]?, ?_⟩
      simp only [Bool.not_eq_true] at hh
      simp only [QueryMachine.step, machine, hh, Bool.false_eq_true, ↓reduceIte,
        QueryMachine.read, query, next, roundStep, paramEdge]
      congr 3
      refine step_congr fun u v hreg => ?_
      simp [inputEdge, callSource, hreg, Reg.toPair]

end Run

/-! ### Halting and the size of the states -/

section Halting

variable {ntm} {D : ℕ} {w : List Bool}

/-- The first round, once the start vertex is known to have a word. -/
theorem initRound_snd (hstart : startID ntm (radix D w.length) < 2 ^ width k (radix D w.length)) :
    (initRound ntm D w.length).2 = ⟨[], .call (width k (radix D w.length))
      (lowBits (width k (radix D w.length)) (startID ntm (radix D w.length)))
      (List.replicate (width k (radix D w.length)) true)⟩ := by
  rw [initRound, dropLast_bits_add_two_pow hstart]

/-- **The machine halts with the value of the recursion.** -/
theorem exists_halted (hstart : startID ntm (radix D w.length) < 2 ^ width k (radix D w.length)) :
    ∃ t, halted ((machine ntm D).run w t) = true ∧
      finish ((machine ntm D).run w t) =
        [reach (inputEdge ntm (radix D w.length) w) (width k (radix D w.length))
          (width k (radix D w.length))
          (lowBits (width k (radix D w.length)) (startID ntm (radix D w.length)))
          (List.replicate (width k (radix D w.length)) true)] := by
  obtain ⟨T, -, hT⟩ := exists_iterate_step_call (edge := inputEdge ntm (radix D w.length) w)
    (w := width k (radix D w.length)) (width k (radix D w.length))
    (lowBits (width k (radix D w.length)) (startID ntm (radix D w.length)))
    (List.replicate (width k (radix D w.length)) true) []
  obtain ⟨symbol, h⟩ := exists_run_add (ntm := ntm) (D := D) w T
  refine ⟨w.length + 1 + T, ?_⟩
  rw [h, initRound_snd hstart, hT]
  exact ⟨rfl, rfl⟩

/-- The states of the recursion satisfy the invariant of a run at depth `W`. -/
theorem invariant_iterate_initRound
    (hstart : startID ntm (radix D w.length) < 2 ^ width k (radix D w.length)) (j : ℕ) :
    Invariant (width k (radix D w.length)) (width k (radix D w.length))
      ((Savitch.step (inputEdge ntm (radix D w.length) w) (width k (radix D w.length)))^[j]
        (initRound ntm D w.length).2) := by
  refine invariant_iterate _ ?_ j
  rw [initRound_snd hstart]
  refine ⟨trivial, fun i u v h => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
  exact ⟨by simp, length_lowBits _ _, List.length_replicate⟩

/-- The binary length of the radix `(n + 2) ^ D`. -/
theorem length_encNat_radix_le (D n : ℕ) :
    (encNat (radix D n)).length ≤ (D + 1) * (Nat.log2 n + 2) := by
  refine (length_encNat_le_of_le_pow (N := n + 1) (d := D) (le_of_eq (by simp [radix]))).trans ?_
  have : Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_add_one_le 2 n
  exact Nat.mul_le_mul_left _ (by omega)

/-- The width of the words for the radix `(n + 2) ^ D`. -/
theorem width_radix_le (D n : ℕ) :
    width k (radix D n) ≤ (D * Fintype.card (Register k) + 1) * (Nat.log2 n + 2) := by
  rw [width, ← length_encNat_eq_size, vertexBound_eq_pow]
  refine (length_encNat_le_of_le_pow (N := n + 1) le_rfl).trans ?_
  have : Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_add_one_le 2 n
  exact Nat.mul_le_mul_left _ (by omega)

variable (k) in
/-- The constant of the bound on the states of the machine. -/
noncomputable def sizeConst (D : ℕ) : ℕ :=
  40 + (encRound encParam idle).length + 16 * (D + 1) + 4 * (D * Fintype.card (Register k) + 1) +
    24 * (2 * (D * Fintype.card (Register k) + 1) + 1) *
      (4 * (D * Fintype.card (Register k) + 1) + 1)

/-- **The states of the machine have `O((log₂ n + 1) ^ 2)` bits.** -/
theorem length_encRuntime_run_le
    (hstart : startID ntm (radix D w.length) < 2 ^ width k (radix D w.length)) (t : ℕ) :
    (encRuntime ((machine ntm D).run w t)).length ≤
      sizeConst k D * (Nat.log2 w.length + 1) ^ 2 := by
  rw [sizeConst]
  generalize hI : (encRound encParam idle).length = I
  rcases le_or_gt t w.length with ht | ht
  · rw [run_of_le w ht]
    have h₁ := length_encNat_le_log2 ht
    rw [encRuntime, length_encPair, length_encPair, encBool_apply, List.length_singleton, hI]
    generalize Nat.log2 w.length = L at *
    generalize D * Fintype.card (Register k) = R
    have hLL : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by omega) _
    calc 2 * (encNat t).length + 1 + (2 * 1 + 1 + I) ≤ (40 + I) * (L + 1) := by nlinarith
      _ ≤ (40 + I) * (L + 1) ^ 2 := Nat.mul_le_mul_left _ hLL
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · obtain ⟨j, rfl⟩ : ∃ j, t = w.length + 1 + j := ⟨t - (w.length + 1), by omega⟩
    obtain ⟨symbol, h⟩ := exists_run_add (ntm := ntm) (D := D) w j
    rw [h]
    have hinv := length_encState_le (invariant_iterate_initRound hstart j)
    have hn := length_encNat_le_log2 (le_refl w.length)
    have hB := length_encNat_radix_le D w.length
    have hW := width_radix_le (k := k) D w.length
    have hsym : (encOption encBool symbol).length ≤ 2 := by cases symbol <;> simp
    simp only [encRuntime, encRound, encParam, length_encPair, encBool_apply, encUnary_apply,
      List.length_singleton, List.length_replicate]
    generalize Nat.log2 w.length = L at *
    generalize D * Fintype.card (Register k) = R at *
    generalize width k (radix D w.length) = W at *
    generalize (encState _).length = E at *
    generalize (encNat (radix D w.length)).length = Bl at *
    generalize (encNat w.length).length = nl at *
    generalize (encOption encBool symbol).length = sl at *
    have hLL : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have hW' : W ≤ 2 * (R + 1) * (L + 1) := by nlinarith
    have hB' : Bl ≤ 2 * (D + 1) * (L + 1) := by nlinarith
    have hst : E ≤ 24 * (2 * (R + 1) + 1) * (4 * (R + 1) + 1) * (L + 1) ^ 2 := by
      refine hinv.trans ?_
      have h₁ : W + 1 ≤ (2 * (R + 1) + 1) * (L + 1) := by nlinarith
      have h₂ : W + W + 1 ≤ (4 * (R + 1) + 1) * (L + 1) := by nlinarith
      have := Nat.mul_le_mul h₁ h₂
      nlinarith
    have hlin : 2 * nl + 1 + (2 * 1 + 1 + (2 * (2 * (2 * Bl + 1 + (2 * nl + 1 + sl)) + 1 + W) + 1))
        ≤ (40 + 16 * (D + 1) + 4 * (R + 1)) * (L + 1) ^ 2 := by
      have : (40 + 16 * (D + 1) + 4 * (R + 1)) * (L + 1) ≤
          (40 + 16 * (D + 1) + 4 * (R + 1)) * (L + 1) ^ 2 := Nat.mul_le_mul_left _ hLL
      nlinarith
    nlinarith

end Halting

/-! ### The parts of the machine in linear space -/

section Parts

open ComputableInSpace

/-- A function computed by a finite transducer is computable in linear space. -/
theorem transducer_inSpace {Q : Type} [Finite Q] (τ : Transducer Bool Q) {α β : Type}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (h : ∀ a, encOut (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableInSpace f encIn encOut fun a => (encIn a).length :=
  of_inO (ComputableInO.of_linear (ComputableInLinearTimeAndSpace.of_transducer τ h))

/-- Whether an option holds a value, in linear space. -/
theorem isSome_inSpace {β : Type} (e : β ↪ List Bool) :
    ComputableInSpace (fun o : Option β => o.isSome) (encOption e) encBool
      fun o => (encOption e o).length :=
  of_inO (ComputableInDegree.isSome e).inO_one

/-- The binary length of a number, in unary, in linear space. -/
theorem size_inSpace : ComputableInSpace Nat.size encNat encUnary fun x => (encNat x).length :=
  ((of_inO ComputableInO.lengthUnary).of_encIn_eq Nat.bits fun _ => rfl).of_enc_eq fun x => by
    rw [Nat.size_eq_bits_len]

/-- The value of a word, in linear space. -/
theorem ofBits_inSpace : ComputableInSpace ofBits encBits encNat fun l => (encBits l).length :=
  of_inO ComputableInO.bitsToNat

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
  (budget_comp_lin (fst _ _) (.refl _) (budget_comp_linear stateFields_inSpace h)).of_enc_eq
    fun _ => rfl

/-- The register as a pair, within a budget. -/
theorem budget_reg {st : α → Savitch.State} (h : ComputableInSpace st enc encState S) :
    ComputableInSpace (fun a => (st a).reg.toPair) enc (encPair (encOption encCall) encBool) S :=
  (budget_comp_lin (snd _ _) (.refl _) (budget_comp_linear stateFields_inSpace h)).of_enc_eq
    fun _ => rfl

/-- The value of the source of the pending call, within a budget. -/
theorem budget_callSource {st : α → Savitch.State} (h : ComputableInSpace st enc encState S) :
    ComputableInSpace (fun a => ofBits (callSource (st a))) enc encNat S := by
  have hreg := budget_reg h
  have hopt := budget_comp_lin (fst _ _) (.refl _) hreg
  have hcall := budget_comp_linear
    (of_inO
      (ComputableInDegree.optionGetD encCall ((0, [], []) : ℕ × List Bool × List Bool)).inO_one)
    hopt
  have hu := budget_comp_lin (fst _ _) (.refl _) (budget_comp_lin (snd _ _) (.refl _) hcall)
  exact (budget_comp_linear ofBits_inSpace hu).of_enc_eq fun _ => rfl

/-- The projections of a state of the machine, within a budget. -/
theorem budget_runtime {s : α → Runtime} (h : ComputableInSpace s enc encRuntime S) :
    ComputableInSpace (fun a => (s a).1) enc encNat S ∧
    ComputableInSpace (fun a => (s a).2.1) enc encBool S ∧
    ComputableInSpace (fun a => (s a).2.2) enc (encRound encParam) S ∧
    ComputableInSpace (fun a => (s a).2.2.1.1.1) enc encNat S ∧
    ComputableInSpace (fun a => (s a).2.2.1.1.2.1) enc encNat S ∧
    ComputableInSpace (fun a => (s a).2.2.1.2) enc encUnary S ∧
    ComputableInSpace (fun a => (s a).2.2.2) enc encState S := by
  have hrest := budget_comp_lin (snd _ _) (.refl _) h
  have hround := budget_comp_lin (snd _ _) (.refl _) hrest
  have hpw := budget_comp_lin (fst _ _) (.refl _) hround
  have hparam := budget_comp_lin (fst _ _) (.refl _) hpw
  exact ⟨budget_comp_lin (fst _ _) (.refl _) h, budget_comp_lin (fst _ _) (.refl _) hrest, hround,
    budget_comp_lin (fst _ _) (.refl _) hparam,
    budget_comp_lin (fst _ _) (.refl _) (budget_comp_lin (snd _ _) (.refl _) hparam),
    budget_comp_lin (snd _ _) (.refl _) hpw, budget_comp_lin (snd _ _) (.refl _) hround⟩

/-- The input position to read, in space linear in the state. -/
theorem query_inSpace :
    ComputableInSpace (query k) encRuntime encNat fun s => (encRuntime s).length := by
  obtain ⟨hk, hstarted, -, hB, -, -, hst⟩ := budget_runtime (ComputableInSpace.of_inO
    (ComputableInO.of_eq (encIn := encRuntime) (encMid := encRuntime) (f := id) fun _ => rfl))
  exact (budget_ite hstarted (queryIndex_budget (k := k) hB (budget_callSource hst)) hk).of_enc_eq
    fun _ => rfl

/-- The halting test, in space linear in the state. -/
theorem halted_inSpace :
    ComputableInSpace halted encRuntime encBool fun s => (encRuntime s).length := by
  obtain ⟨-, hstarted, -, -, -, -, hst⟩ := budget_runtime (ComputableInSpace.of_inO
    (ComputableInO.of_eq (encIn := encRuntime) (encMid := encRuntime) (f := id) fun _ => rfl))
  have hempty := budget_isEmpty (budget_stack hst)
  have hsome := budget_comp_linear (isSome_inSpace encCall)
    (budget_comp_lin (fst _ _) (.refl _) (budget_reg hst))
  exact (budget_finite (fun p : Bool × Bool × Bool => p.1 && p.2.1 && !p.2.2)
    (budget_prod hstarted (budget_prod hempty hsome))).of_enc_eq fun _ => rfl

/-- The answer, in space linear in the state. -/
theorem finish_inSpace :
    ComputableInSpace finish encRuntime encBits fun s => (encRuntime s).length := by
  obtain ⟨-, -, -, -, -, -, hst⟩ := budget_runtime (ComputableInSpace.of_inO
    (ComputableInO.of_eq (encIn := encRuntime) (encMid := encRuntime) (f := id) fun _ => rfl))
  exact (budget_comp_lin (snd _ _) (.refl _) (budget_reg hst)).of_enc_eq fun _ => rfl

/-- The edge test of the graph on words, in linear space. -/
theorem paramEdge_inSpace : ComputableInSpace
    (fun q : (ℕ × ℕ × Option Bool) × List Bool × List Bool => paramEdge ntm q.1 q.2.1 q.2.2)
    (encPair encParam (encPair encBits encBits)) encBool
    fun q => (encPair encParam (encPair encBits encBits) q).length := by
  have hp := fst encParam (encPair encBits encBits)
  have huv := snd encParam (encPair encBits encBits)
  have hB := budget_comp_lin (fst _ _) (.refl _) hp
  have hrest := budget_comp_lin (snd _ _) (.refl _) hp
  have hn := budget_comp_lin (fst _ _) (.refl _) hrest
  have hsym := budget_comp_lin (snd _ _) (.refl _) hrest
  have hu := budget_comp_lin (fst _ _) (.refl _) huv
  have hv := budget_comp_lin (snd _ _) (.refl _) huv
  have hvalU := budget_comp_linear ofBits_inSpace hu
  have hvalV := budget_comp_linear ofBits_inSpace hv
  have hin : (fun q : (ℕ × ℕ × Option Bool) × List Bool × List Bool =>
      (encPair encParam (encPair encBits encBits) q).length) ≼ _ := .refl _
  have he := edgeWithSymbol_budget ntm hB hn hvalU hvalV hsym hin
  have hb := bad_budget (k := k) (State := State) hB hn hvalU hin
  have hall := budget_comp_linear (transducer_inSpace (encIn := encBits) (encOut := encBool)
    (f := fun l : List Bool => l.all id) Savitch.allT fun l => by rw [Savitch.allT_run]; rfl) hv
  exact (budget_finite (fun p : Bool × Bool × Bool => p.1 || (p.2.1 && p.2.2))
    (budget_prod he (budget_prod hb hall))).of_enc_eq fun _ => rfl

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

/-- The first round, from the input length, in linear space. -/
theorem initRound_inSpace (D : ℕ) : ComputableInSpace (initRound ntm D) encNat (encRound encParam)
    fun n => (encNat n).length := by
  have hn : ComputableInSpace (fun n : ℕ => n) encNat encNat fun n => (encNat n).length :=
    of_inO (ComputableInO.of_eq fun _ => rfl)
  have hin : (fun n : ℕ => (encNat n).length) ≼ fun n => (encNat n).length := .refl _
  have hB : ComputableInSpace (fun n => radix D n) encNat encNat fun n => (encNat n).length :=
    (budget_natPow (budget_natAdd hn (budget_const 2 hin)) hin D).of_enc_eq fun _ => rfl
  have hN := vertexBound_budget (k := k) hB hin
  have hW₀ := budget_comp_linear size_inSpace hN
  have hW : ComputableInSpace (fun n => width k (radix D n)) encNat encUnary
      fun n => (encNat n).length := hW₀.of_enc_eq fun _ => rfl
  have hstart := startID_budget ntm hB hin
  have hpow₀ : ComputableInSpace (fun W : ℕ => 2 ^ W) encUnary encNat
      fun W => (encUnary W).length := by
    simpa only [encUnary_apply, List.length_replicate] using
      of_inO (ComputableInDegree.two_pow_length encUnary).inO_one
  have hpow := budget_comp_linear hpow₀ hW
  have hbits : ComputableInSpace
      (fun n => (startID ntm (radix D n) + 2 ^ width k (radix D n)).bits) encNat encBits
      fun n => (encNat n).length :=
    (budget_natAdd hstart hpow).of_enc_eq fun _ => rfl
  have hsrc := budget_comp_linear (of_inO ComputableInDegree.bitsDropLast.inO_one) hbits
  have hsink : ComputableInSpace (fun n => List.replicate (width k (radix D n)) true) encNat
      encBits fun n => (encNat n).length := hW.of_enc_eq fun _ => rfl
  have hcall := budget_comp_linear
    (of_inO (ComputableInDegree.optionSome (enc₁ := encCall) (enc := encOption encCall)).inO_one)
    (budget_prod hW (budget_prod hsrc hsink))
  have hstate : ComputableInSpace (fun n => (initRound ntm D n).2) encNat encState
      fun n => (encNat n).length :=
    (budget_prod (budget_const (encB := encList encFrame) [] hin)
      (budget_prod hcall (budget_const (encB := encBool) false hin))).of_enc_eq fun _ => rfl
  exact (budget_prod (budget_prod (budget_prod hB (budget_prod hn
    (budget_const (encB := encOption encBool) none hin))) hW) hstate).of_enc_eq fun _ => rfl

/-- A step of the machine, in space linear in the state and the bit read. -/
theorem next_inSpace (D : ℕ) : ComputableInSpace (next ntm D)
    (encPair encRuntime (encOption encBool)) encRuntime
    fun p => (encPair encRuntime (encOption encBool) p).length := by
  have hin : (fun p : Runtime × Option Bool => (encPair encRuntime (encOption encBool) p).length)
      ≼ _ := .refl _
  have hs := fst encRuntime (encOption encBool)
  have hsym := snd encRuntime (encOption encBool)
  obtain ⟨hk, hstarted, hround, hB, hn, hW, hst⟩ := budget_runtime hs
  have hq := budget_prod (budget_prod (budget_prod hB (budget_prod hn hsym)) hW) hst
  have hA := budget_prod hk (budget_prod (budget_const (encB := encBool) true hin)
    (budget_comp_linear (roundStep_inSpace ntm) hq))
  have hC := budget_prod (budget_natSucc hk) (budget_prod
    (budget_const (encB := encBool) false hin) hround)
  have hI := budget_prod hk (budget_prod (budget_const (encB := encBool) true hin)
    (budget_comp_linear (initRound_inSpace ntm D) hk))
  have hsome := budget_comp_linear (isSome_inSpace encBool) hsym
  exact (budget_ite hstarted hA (budget_ite hsome hC hI)).of_enc_eq fun _ => rfl

end Parts

end Turing.MultiTapeNTM.LogSquareSavitch

namespace Turing.MultiTapeNTM

open MultiTapeTM ConfigurationGraph LogSquareSavitch

/-- **Savitch's theorem in space `log² n`** [Savitch1970]. A problem recognized by a
nondeterministic machine whose computation paths on `enc a` visit at most
`c * (log₂ |enc a| + 1)` work cells, and whose branches need not halt, is decided by a
deterministic machine within space `O((log₂ |enc a| + 1) ^ 2)`: Savitch's midpoint recursion on
the compact configuration graph of the machine
(`Turing.MultiTapeNTM.LogSquareSavitch.machine`). -/
theorem exists_decidableInTimeAndSpace_log_sq {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {k : ℕ} {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State} {c : ℕ}
    (hA : ntm.RecognizesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)) :
    ∃ t c', DecidableInTimeAndSpace A enc t fun a => c' * (Nat.log2 (enc a).length + 1) ^ 2 := by
  classical
  let : Fintype State := Fintype.ofFinite State
  set D := radixExponent State c
  have hstart (a : α) :
      startID ntm (radix D (enc a).length) < 2 ^ width k (radix D (enc a).length) := by
    rw [← vertexID_init ntm _ (enc a)]
    exact (vertexID_lt (fits_of_runsInSpace c (hA a).1 .refl)).trans
      (vertexBound_lt_two_pow_width k _)
  have hex (a : α) : ∃ t, (machine ntm D).halted ((machine ntm D).run (enc a) t) = true :=
    let ⟨t, h, _⟩ := exists_halted (hstart a)
    ⟨t, h⟩
  have hhalt (a : α) := Nat.find_spec (hex a)
  have hpre (a : α) : ∀ t < Nat.find (hex a),
      (machine ntm D).halted ((machine ntm D).run (enc a) t) = false := fun t ht => by
    simpa using Nat.find_min (hex a) ht
  have hf (a : α) :
      encBool (decide (a ∈ A)) = (machine ntm D).output (enc a) (Nat.find (hex a)) := by
    obtain ⟨t, ht, hfin⟩ := exists_halted (hstart a)
    rw [output_eq, ← (machine ntm D).run_eq_of_le (enc a) (hhalt a) (Nat.find_min' (hex a) ht),
      hfin, encBool_apply]
    congr 1
    rw [Bool.eq_iff_iff, reach_eq_true_iff (hA a).1, decide_eq_true_iff]
    exact (hA a).2
  obtain ⟨t, c', h⟩ := (machine ntm D).computableInSpace query_inSpace (next_inSpace ntm D)
    (ComputableInSpace.const []) halted_inSpace finish_inSpace (fun a => Nat.find (hex a))
    hhalt hpre hf (fun a => (Nat.log2 (enc a).length + 1) ^ 2)
    (fun a => Nat.le_self_pow two_ne_zero _)
    ⟨sizeConst k D, fun a t _ => length_encRuntime_run_le (hstart a) t⟩
  exact ⟨t, c', decidableInTimeAndSpace_iff.mpr ⟨_, h, fun a => by simp⟩⟩

end Turing.MultiTapeNTM

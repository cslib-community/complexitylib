/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Deterministic
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Finite.List

/-!
# Simulating a clocked oracle machine with a computed oracle

The run of a fair-coin oracle machine with every coin fixed to `false`, against a deterministic
answer function, is the iteration of one instruction on finite storage
(`Turing.MultiTapePTM.answerStep`, `Turing.MultiTapePTM.interpret_run_pure_false`): a local
instruction updates the tapes, and a query installs the answer to the pending request.

Against an oracle that answers a request `w` with the bit `g w`, an instruction costs polynomial
time in the encoded configuration plus one evaluation of `g` on the pending request
(`Turing.MultiTapePTM.answerStep_inO`). Along a clocked run the configuration grows by a bounded
amount per instruction and every request is no longer than the clock
(`Turing.MultiTapePTM.spaceBound_answerStep`, `Turing.MultiTapePTM.length_pendingRequest_le`).
Iterating the instruction with a binary counter
(`Turing.MultiTapeTM.ComputableInO.iterate`) therefore simulates a run of polynomial clock
within polynomial space whenever `g` is computable within polynomial space
(`Turing.MultiTapePTM.exists_computableTidilyInO_run`). The time is not bounded by a polynomial:
it charges, for every instruction, the largest time of `g` on a word no longer than the clock
(`Turing.MultiTapeTM.wordMax`). When `g` is polynomial-time, both the instruction and the clocked
run are polynomial-time (`Turing.MultiTapePTM.computableTidilyInPolyTime_answerStep`,
`Turing.MultiTapePTM.computableInPolyTime_run`).

## Main definitions

* `Turing.MultiTapePTM.answerStep`: one instruction against an answer function.
* `Turing.MultiTapePTM.pendingQuery`, `Turing.MultiTapePTM.pendingRequest`: the query about to be
  submitted and its request word.
* `Turing.MultiTapeTM.wordMax`: the largest value of a function on the words up to a length.

## Main results

* `Turing.MultiTapePTM.interpret_run_pure_false`: a coin-fixed run is an iteration of
  `answerStep`.
* `Turing.MultiTapePTM.answerStep_inO`: the bounds of an instruction.
* `Turing.MultiTapePTM.exists_computableInO_run`: the plain charged-time/workspace frontend,
  retaining the independent bounds and exact clocked run.
* `Turing.MultiTapePTM.exists_computableTidilyInO_run`: a clocked run against an oracle computed
  within polynomial space is computable within polynomial space.
* `Turing.MultiTapePTM.computableTidilyInPolyTime_answerStep`: an instruction against a
  polynomial-time oracle is polynomial-time.
* `Turing.MultiTapePTM.computableInPolyTime_run`: a clocked run against a polynomial-time
  oracle is polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4
  (oracle Turing machines) and Theorem 3.7.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The largest value of `f` on the words of length at most `N`. -/
noncomputable def wordMax (f : List Bool → ℕ) (N : ℕ) : ℕ := sSup (f '' {w | w.length ≤ N})

theorem le_wordMax (f : List Bool → ℕ) {N : ℕ} {w : List Bool} (hw : w.length ≤ N) :
    f w ≤ wordMax f N :=
  le_csSup ((List.finite_length_le Bool N).image f).bddAbove ⟨w, hw, rfl⟩

end Turing.MultiTapeTM

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
  (machine : MultiTapePTM k Bool Control Operation)

/-! ### One instruction against an answer function -/

/-- One instruction of the run with every coin `false`, the reply to a query given by `answer`. A
halted configuration is unchanged. -/
def answerStep (answer : Operation × List Bool → List Bool)
    (cfg : FiniteConfig k Bool Control Operation) : FiniteConfig k Bool Control Operation :=
  match cfg.tapes.state with
  | none => cfg
  | some control =>
    match machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols
        false with
    | .step action symbol move => cfg.step action symbol move
    | .query op next => cfg.receive op next (answer (op, (cfg.channels op).1))

omit [DecidableEq Operation] in
/-- Interpreting a bounded loop against an answer function iterates the interpreted body. -/
theorem _root_.Cslib.OracleComp.interpret_id_iterate {State Query : Type}
    {spec : OracleSpec.{0, 0} Query} (answer : (q : Query) → spec q) (n : ℕ)
    (step : State → OracleComp spec State) (s : State) :
    OracleComp.interpret (m := Id) answer (OracleComp.iterate n step s) =
      (fun s => OracleComp.interpret (m := Id) answer (step s))^[n] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [OracleComp.iterate_succ, OracleComp.interpret_bind, Function.iterate_succ_apply', ← ih]
    rfl

/-- The interpreted native instruction, with every coin `false`, is `answerStep`. -/
private theorem interpret_finiteStep (answer : Operation × List Bool → List Bool)
    (cfg : FiniteConfig k Bool Control Operation) :
    OracleComp.interpret (m := Id) answer (MultiTapeMachine.finiteStep machine
      (fun choices => choices <$> (pure false : OracleComp _ Bool))
      (fun op word => OracleComp.query (op, word)) cfg) = machine.answerStep answer cfg := by
  unfold MultiTapeMachine.finiteStep answerStep
  cases cfg.tapes.state with
  | none => rfl
  | some control =>
    simp only [map_pure, pure_bind]
    cases machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols
      false <;> rfl

/-- **A coin-fixed run is an iteration of `answerStep`** on finite storage, against every answer
function. -/
theorem interpret_run_pure_false (answer : Operation × List Bool → List Bool) (fuel : ℕ)
    (input : List Bool) :
    OracleComp.interpret (m := Id) answer (machine.run (pure false)
        (fun op word => OracleComp.query (op, word)) fuel input) =
      ((machine.answerStep answer)^[fuel]
        (FiniteConfig.init machine.initial input)).tapes.output := by
  change OracleComp.interpret (m := Id) answer (MultiTapeMachine.run machine
    (fun choices => choices <$> (pure false : OracleComp _ Bool))
    (fun op word => OracleComp.query (op, word)) fuel input) = _
  rw [← finiteRunFrom_init, finiteRunFrom, OracleComp.interpret_map,
    OracleComp.interpret_id_iterate]
  simp only [interpret_finiteStep]
  rfl

/-! ### The parts of an instruction -/

/-- The query about to be submitted: its channel and the next control state, if the machine has
not halted and its next instruction, with coin `false`, is a query. -/
def pendingQuery (cfg : FiniteConfig k Bool Control Operation) : Option (Operation × Control) :=
  match cfg.tapes.state.map fun control => machine.tr control cfg.tapes.inputSymbol
      cfg.tapes.workTapeSymbols cfg.answerSymbols false with
  | some (.query op next) => some (op, next)
  | _ => none

/-- The request word of the pending query, or the empty word. -/
def pendingRequest (cfg : FiniteConfig k Bool Control Operation) : List Bool :=
  match machine.pendingQuery cfg with
  | some (op, _) => (cfg.channels op).1
  | none => []

/-- The next instruction if it is local; otherwise the configuration is unchanged. -/
def localStep (cfg : FiniteConfig k Bool Control Operation) :
    FiniteConfig k Bool Control Operation :=
  match cfg.tapes.state.map fun control => machine.tr control cfg.tapes.inputSymbol
      cfg.tapes.workTapeSymbols cfg.answerSymbols false with
  | some (.step action symbol move) => cfg.step action symbol move
  | _ => cfg

/-- Install a one-bit reply to the pending query. -/
def receiveBit (p : FiniteConfig k Bool Control Operation × Bool) :
    FiniteConfig k Bool Control Operation :=
  match machine.pendingQuery p.1 with
  | some (op, next) => p.1.receive op next [p.2]
  | none => p.1

/-- Against an oracle answering one bit, an instruction either installs the bit for the pending
request or is local. -/
theorem answerStep_bit (g : List Bool → Bool) (cfg : FiniteConfig k Bool Control Operation) :
    machine.answerStep (fun q => [g q.2]) cfg =
      if (machine.pendingQuery cfg).isSome then
        machine.receiveBit (cfg, g (machine.pendingRequest cfg))
      else machine.localStep cfg := by
  unfold answerStep receiveBit pendingRequest localStep pendingQuery
  cases cfg.tapes.state with
  | none => rfl
  | some control =>
    simp only [Option.map_some]
    cases machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols
      false <;> rfl

/-- The observations selecting the next instruction. -/
private def observe (cfg : FiniteConfig k Bool Control Operation) :
    Option Control × Option Bool × (Fin k → Option Bool) × (Operation → Option Bool) :=
  (cfg.tapes.state, cfg.tapes.inputSymbol, cfg.tapes.workTapeSymbols, cfg.answerSymbols)

variable [Finite Control] [Fintype Operation]

omit [DecidableEq Operation] in
private theorem observe_pt : ComputableTidilyInPolyTime
    (observe (k := k) (Control := Control) (Operation := Operation)) encFiniteConfig
    (encPair (encFinite (Option Control)) (encPair (encFinEnum (Option Bool))
      (encPair (encFinEnum (Fin k → Option Bool)) (encFinite (Operation → Option Bool))))) := by
  unfold observe
  fun_prop

omit [DecidableEq Operation] in
private theorem instruction_pt : ComputableTidilyInPolyTime
    (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.state.map fun control =>
      machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols false)
    encFiniteConfig (encFinite (Option (MultiTapeMachine.Action k Bool Control Operation))) :=
  ((ComputableTidilyInPolyTime.of_finite fun obs : Option Control × Option Bool ×
      (Fin k → Option Bool) × (Operation → Option Bool) => obs.1.map fun control =>
        machine.tr control obs.2.1 obs.2.2.1 obs.2.2.2 false).comp observe_pt).of_enc_eq
    fun _ => rfl

omit [DecidableEq Operation] in
theorem pendingQuery_pt : ComputableTidilyInPolyTime machine.pendingQuery encFiniteConfig
    (encFinite (Option (Operation × Control))) :=
  ((ComputableTidilyInPolyTime.of_finite fun i : Option (MultiTapeMachine.Action k Bool Control
      Operation) => match i with
    | some (.query op next) => some (op, next)
    | _ => none).comp machine.instruction_pt).of_enc_eq fun _ => rfl

omit [DecidableEq Operation] in
theorem localStep_pt : ComputableTidilyInPolyTime machine.localStep encFiniteConfig
    encFiniteConfig := by
  refine ComputableTidilyInPolyTime.finite_cases
    (tag := fun cfg : FiniteConfig k Bool Control Operation => (cfg.tapes.state.map fun control =>
      machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols false :
        Option (MultiTapeMachine.Action k Bool Control Operation)))
    (branch := fun i cfg => match i with
      | some (.step action symbol move) => cfg.step action symbol move
      | _ => cfg) machine.instruction_pt ?_
  rintro (_ | ⟨_, _, _⟩ | _)
  · exact ComputableTidilyInPolyTime.id'
  · fun_prop
  · exact ComputableTidilyInPolyTime.id'

omit [DecidableEq Operation] in
theorem pendingRequest_pt : ComputableTidilyInPolyTime machine.pendingRequest encFiniteConfig
    encBits := by
  refine ComputableTidilyInPolyTime.finite_cases (tag := machine.pendingQuery)
    (branch := fun q cfg => match q with
      | some (op, _) => (cfg.channels op).1
      | none => []) machine.pendingQuery_pt ?_
  rintro (_ | ⟨op, _⟩)
  · exact ComputableTidilyInPolyTime.const _
  · fun_prop

theorem receiveBit_pt : ComputableTidilyInPolyTime machine.receiveBit
    (encPair encFiniteConfig encBool) encFiniteConfig := by
  refine ComputableTidilyInPolyTime.finite_cases
    (tag := fun p : FiniteConfig k Bool Control Operation × Bool => machine.pendingQuery p.1)
    (branch := fun q (p : FiniteConfig k Bool Control Operation × Bool) => match q with
      | some (op, next) => p.1.receive op next [p.2]
      | none => p.1)
    (machine.pendingQuery_pt.comp (ComputableTidilyInPolyTime.fst encFiniteConfig encBool)) ?_
  rintro (_ | ⟨op, next⟩)
  · exact ComputableTidilyInPolyTime.fst _ _
  · have hbit : ComputableTidilyInPolyTime (fun p : FiniteConfig k Bool Control Operation × Bool =>
        [p.2]) (encPair encFiniteConfig encBool) encBits :=
      (ComputableTidilyInPolyTime.snd encFiniteConfig encBool).of_enc_eq fun p =>
        (encBool_apply p.2).symm
    exact ComputableTidilyInPolyTime.finiteConfig_receive
      (ComputableTidilyInPolyTime.fst encFiniteConfig encBool) hbit op next

/-! ### Bounds -/

/-- **The bounds of an instruction.** Against an oracle answering `[g w]` to a request `w`, an
instruction takes polynomial time and space in the encoded configuration, plus the time and space
of `g` on the pending request. -/
theorem answerStep_inO {g : List Bool → Bool} {Tg Sg : List Bool → ℕ}
    (hg : ComputableTidilyInO g encBits encBool Tg Sg) :
    ∃ e, ComputableTidilyInO (machine.answerStep fun q => [g q.2]) encFiniteConfig
      encFiniteConfig
      (fun cfg => ((encFiniteConfig cfg).length + 1) ^ e + Tg (machine.pendingRequest cfg))
      (fun cfg => ((encFiniteConfig cfg).length + 1) ^ e + Sg (machine.pendingRequest cfg)) := by
  have hcond : ComputableTidilyInPolyTime (fun cfg => (machine.pendingQuery cfg).isSome)
      encFiniteConfig encBool :=
    (ComputableTidilyInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt
  have hid : ComputableTidilyInPolyTime (fun cfg : FiniteConfig k Bool Control Operation => cfg)
      encFiniteConfig encFiniteConfig := ComputableTidilyInPolyTime.id'
  obtain ⟨dc, _, hc⟩ := hcond.exists_degree
  obtain ⟨dr, _, hr⟩ := machine.pendingRequest_pt.exists_degree
  obtain ⟨dv, _, hv⟩ := machine.receiveBit_pt.exists_degree
  obtain ⟨dl, _, hl⟩ := machine.localStep_pt.exists_degree
  obtain ⟨di, _, hi⟩ := hid.exists_degree
  have h := hc.inO.ite (hv.inO.comp (hi.inO.prod (hg.comp hr.inO))) hl.inO
  refine ⟨dc + dr + dv + dl + di, (h.mono (4 ^ dv + 5) (fun cfg => ?_) fun cfg => ?_).of_enc_eq
    fun cfg => by rw [answerStep_bit]; rfl⟩
  all_goals
    simp only [Function.comp_apply, length_encPair, encBool_apply, List.length_singleton]
    generalize (encFiniteConfig cfg).length = L
    have hL : 1 ≤ L + 1 := by omega
    have hpow (d : ℕ) (hd : d ≤ dc + dr + dv + dl + di) :
        (L + 1) ^ d ≤ (L + 1) ^ (dc + dr + dv + dl + di) := Nat.pow_le_pow_right hL hd
    have h2 : (2 * L + 1 + 1 + 1) ^ dv ≤ 4 ^ dv * (L + 1) ^ dv := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by omega) dv
    have h4 : 1 ≤ 4 ^ dv := Nat.one_le_pow _ _ (by omega)
    have hc' := hpow dc (by omega)
    have hr' := hpow dr (by omega)
    have hv' := hpow dv (by omega)
    have hl' := hpow dl (by omega)
    have hi' := hpow di (by omega)
    generalize (L + 1) ^ (dc + dr + dv + dl + di) = M at *
    split_ifs <;> nlinarith

omit [Finite Control] [Fintype Operation] in
/-- An instruction against a one-bit oracle grows the storage by a bounded amount. -/
theorem spaceBound_answerStep (g : List Bool → Bool) {inputSize steps : ℕ}
    {cfg : FiniteConfig k Bool Control Operation}
    (h : FiniteConfig.SpaceBound inputSize steps 1 cfg) :
    FiniteConfig.SpaceBound inputSize (steps + 1) 1
      (machine.answerStep (fun q => [g q.2]) cfg) := by
  unfold answerStep
  split
  · exact h.mono le_rfl (Nat.le_succ _) le_rfl
  · split
    · exact h.step _ _ _
    · exact h.receive _ _ _ (by simp)

omit [DecidableEq Operation] [Finite Control] [Fintype Operation] in
/-- A pending request after `steps` instructions has at most `steps` symbols. -/
theorem length_pendingRequest_le {inputSize steps answerSize : ℕ}
    {cfg : FiniteConfig k Bool Control Operation}
    (h : FiniteConfig.SpaceBound inputSize steps answerSize cfg) :
    (machine.pendingRequest cfg).length ≤ steps := by
  unfold pendingRequest
  split
  · exact h.query _
  · exact Nat.zero_le _

omit [Fintype Operation] in
/-- **A clocked run against an oracle computed within polynomial space is computable within
polynomial space.** Against the oracle answering `[g w]` to a request `w`, where `g` is tidily
computable with space polynomial in the length of `w`, the run with every coin fixed to `false`
under the clock `c * (n + 1) ^ d` is tidily computable from its input, within space polynomial in
the length of the encoded input. -/
theorem exists_computableTidilyInO_run [Finite Operation] {α : Type} {input : α ↪ List Bool}
    {g : List Bool → Bool} {Tg Sg : List Bool → ℕ}
    (hg : ComputableTidilyInO g encBits encBool Tg Sg) (hSg : PolyBounded List.length Sg)
    (c d : ℕ) :
    ∃ T S, PolyBounded (fun a => (input a).length) S ∧
      ComputableTidilyInO (fun a => OracleComp.interpret (m := Id) (fun q => [g q.2])
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (c * ((input a).length + 1) ^ d) (input a))) input encBits T S := by
  classical
  let _ := Fintype.ofFinite Operation
  let _ : Inhabited (FiniteConfig k Bool Control Operation) :=
    ⟨FiniteConfig.init machine.initial []⟩
  obtain ⟨e, hstep⟩ := machine.answerStep_inO hg
  obtain ⟨cg, dg, hSg⟩ := hSg.exists_le
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  -- the clock in binary, the initial storage and the output
  have hn : ComputableTidilyInPolyTime (fun a => c * ((input a).length + 1) ^ d) input encNat := by
    have hlen : ComputableTidilyInPolyTime (fun a => (input a).length) input encUnary := by
      fun_prop
    exact (ComputableTidilyInPolyTime.unary_to_binary.comp
      ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
        hlen)).of_enc_eq fun a => by simp
  obtain ⟨dn, _, hn⟩ := hn.exists_degree
  have hinit : ComputableTidilyInPolyTime
      (fun a => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial (input a))
      input encFiniteConfig :=
    ComputableTidilyInPolyTime.finiteConfig_init (by fun_prop) _
  obtain ⟨di, _, hinit⟩ := hinit.exists_degree
  have hout : ComputableTidilyInPolyTime
      (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output) encFiniteConfig
      encBits := by fun_prop
  obtain ⟨do', _, hout⟩ := hout.exists_degree
  -- the storage of the iterates
  set n : α → ℕ := fun a => c * ((input a).length + 1) ^ d with hn_def
  set step := machine.answerStep fun q => [g q.2] with hstep_def
  have hspace (a : α) (i : ℕ) : FiniteConfig.SpaceBound (input a).length i 1
      (step^[i] (FiniteConfig.init machine.initial (input a))) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact machine.spaceBound_answerStep g ih
  set B : α → ℕ := fun a => cf * ((input a).length + n a + 1 + 1) with hB
  have hlen (a : α) {i : ℕ} (hi : i ≤ n a) :
      (encFiniteConfig (step^[i] (FiniteConfig.init machine.initial (input a)))).length ≤ B a :=
    (hcf _ _ _ _ (hspace a i)).trans (Nat.mul_le_mul_left cf (by omega))
  have hreq (a : α) {i : ℕ} (hi : i ≤ n a) :
      (machine.pendingRequest (step^[i] (FiniteConfig.init machine.initial (input a)))).length ≤
        n a :=
    (machine.length_pendingRequest_le (hspace a i)).trans hi
  -- the iteration, with every request answered within the space of `g` on a short word
  have hit := (ComputableInO.iterate hn.inO.computableInO hinit.inO.computableInO
    hstep.computableInO
    (R := fun a => (B a + 1) ^ e + wordMax Tg (n a))
    (Q := fun a => (B a + 1) ^ e + cg * (n a + 1) ^ dg) (B := B)
    (fun a i hi => Nat.add_le_add (Nat.pow_le_pow_left (by have := hlen a hi; omega) e)
      (le_wordMax Tg (hreq a hi)))
    (fun a i hi => Nat.add_le_add (Nat.pow_le_pow_left (by have := hlen a hi; omega) e)
      ((hSg _).trans (Nat.mul_le_mul_left cg (Nat.pow_le_pow_left (by
        have := hreq a hi; omega) dg))))
    (fun a i hi => hlen a hi)).tidy
  have h := (hout.inO.comp hit).mono_le (T' := fun a => _ + (B a + 1) ^ do')
    (S' := fun a => ((input a).length + 1) ^ dn + ((input a).length + 1) ^ di +
      ((B a + 1) ^ e + cg * (n a + 1) ^ dg) + B a + (n a + 1) + (B a + 1) ^ do')
    (fun a => Nat.add_le_add_left (Nat.pow_le_pow_left (by
      have := hlen a (le_refl (n a)); omega) do') _)
    (fun a => by
      have h₁ := hlen a (le_refl (n a))
      have h₂ : (encNat (n a)).length ≤ n a + 1 := by
        rw [encNat_apply, Nat.size_eq_bits_len]
        exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_succ _)
      have h₃ := Nat.pow_le_pow_left (Nat.add_le_add_right h₁ 1) do'
      omega)
  refine ⟨_, _, ?_, h.of_enc_eq (g := fun a => OracleComp.interpret (m := Id)
    (fun q => [g q.2]) (machine.run (pure false) (fun op word => OracleComp.query (op, word))
      (c * ((input a).length + 1) ^ d) (input a))) fun a => by
    rw [interpret_run_pure_false]; rfl⟩
  exact PolyBounded.mono (PolyBounded.of_polynomiallyBounded (fun a => (input a).length)
    (bound := fun L => (L + 1) ^ dn + (L + 1) ^ di +
      ((cf * (L + c * (L + 1) ^ d + 1 + 1) + 1) ^ e + cg * (c * (L + 1) ^ d + 1) ^ dg) +
      cf * (L + c * (L + 1) ^ d + 1 + 1) + (c * (L + 1) ^ d + 1) +
      (cf * (L + c * (L + 1) ^ d + 1 + 1) + 1) ^ do') (by fun_prop)) fun a => le_rfl


omit [Fintype Operation] in
/-- A clocked coin-false run against a plain oracle decider is computable within polynomial
space. Both oracle and run certificates charge encoded output in workspace. The independent
time and workspace bounds are exactly those of the tidy simulation; only the realizing-machine
presentation changes. No polynomial time bound on the oracle is assumed. -/
theorem exists_computableInO_run [Finite Operation] {α : Type} {input : α ↪ List Bool}
    {g : List Bool → Bool} {Tg Sg : List Bool → ℕ}
    (hg : ComputableInO g encBits encBool Tg Sg) (hSg : PolyBounded List.length Sg)
    (c d : ℕ) :
    ∃ T S, PolyBounded (fun a => (input a).length) S ∧
      ComputableInO (fun a => OracleComp.interpret (m := Id) (fun q => [g q.2])
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (c * ((input a).length + 1) ^ d) (input a))) input encBits T S := by
  obtain ⟨T, S, hS, hrun⟩ := machine.exists_computableTidilyInO_run hg.tidy hSg c d
  exact ⟨T, S, hS, .of_tidy hrun⟩

/-- **An instruction against a polynomial-time oracle is polynomial-time.** Against an oracle
answering `[g w]` to a request `w`, with `g` polynomial-time, an instruction is polynomial-time in
the encoded configuration: it either installs `g` of the pending request or is local. -/
theorem computableTidilyInPolyTime_answerStep {g : List Bool → Bool}
    (hg : ComputableTidilyInPolyTime g encBits encBool) :
    ComputableTidilyInPolyTime (machine.answerStep fun q => [g q.2]) encFiniteConfig
      encFiniteConfig := by
  have h : ComputableTidilyInPolyTime (fun cfg => if (machine.pendingQuery cfg).isSome then
      machine.receiveBit (cfg, g (machine.pendingRequest cfg)) else machine.localStep cfg)
      encFiniteConfig encFiniteConfig :=
    ComputableTidilyInPolyTime.cond
      ((ComputableTidilyInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt)
      (machine.receiveBit_pt.comp
        (ComputableTidilyInPolyTime.id'.prod (hg.comp machine.pendingRequest_pt)))
      machine.localStep_pt
  exact h.of_enc_eq fun cfg => by rw [answerStep_bit]

omit [Fintype Operation] in
/-- **A clocked run against a polynomial-time oracle is polynomial-time.** Against the oracle
answering `[g w]` to a request `w`, where `g` is polynomial-time, the run with every coin fixed to
`false` under the clock `c * (n + 1) ^ d` is polynomial-time in the encoded input. -/
theorem computableInPolyTime_run [Finite Operation] {α : Type} {input : α ↪ List Bool}
    {g : List Bool → Bool} (hg : ComputableInPolyTime g encBits encBool) (c d : ℕ) :
    ComputableInPolyTime (fun a => OracleComp.interpret (m := Id) (fun q => [g q.2])
      (machine.run (pure false) (fun op word => OracleComp.query (op, word))
        (c * ((input a).length + 1) ^ d) (input a))) input encBits := by
  replace hg := hg.tidy
  refine .of_tidy ?_
  classical
  let _ := Fintype.ofFinite Operation
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  have hcount : ComputableTidilyInPolyTime (fun a => c * ((input a).length + 1) ^ d) input
      encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableTidilyInPolyTime.encoding_length input)).of_enc_eq fun a => by simp
  have hinit : ComputableTidilyInPolyTime
      (fun a => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial (input a))
      input encFiniteConfig :=
    ComputableTidilyInPolyTime.finiteConfig_init (by fun_prop) _
  have hspace (a : α) (i : ℕ) : FiniteConfig.SpaceBound (input a).length i 1
      ((machine.answerStep fun q => [g q.2])^[i]
        (FiniteConfig.init machine.initial (input a))) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact machine.spaceBound_answerStep g ih
  have hbound : PolyBounded (fun a => (input a).length)
      (fun a => cf * ((input a).length + c * ((input a).length + 1) ^ d + 1 + 1)) :=
    PolyBounded.mono (PolyBounded.of_polynomiallyBounded (fun a => (input a).length)
      (bound := fun L => cf * (L + c * (L + 1) ^ d + 1 + 1)) (by fun_prop)) fun _ => le_rfl
  have hit := ComputableTidilyInPolyTime.iterate hcount hinit
    (machine.computableTidilyInPolyTime_answerStep hg) hbound fun a i hi =>
      (hcf _ _ _ _ (hspace a i)).trans (Nat.mul_le_mul_left cf (by omega))
  have hout : ComputableTidilyInPolyTime
      (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output) encFiniteConfig
      encBits := by fun_prop
  exact (hout.comp hit).of_enc_eq fun a => by rw [interpret_run_pure_false]; rfl

end Turing.MultiTapePTM

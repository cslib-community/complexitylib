/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.PrefixLocality
public import Complexity.Computability.Probabilistic.Oracle.Composition
public import Complexity.Computability.Probabilistic.PPT.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
import Complexity.Probability.PMF.Map

/-!
# Probabilistic polynomial-time programs clocked in a designated primary input

In auxiliary-input cryptography (such as Goldreich's definition of auxiliary-input zero knowledge),
a probabilistic machine receives a primary input `a : α` together with an arbitrary, potentially
unbounded auxiliary input word `z : List Bool` on its input tape `encPair input encBits (a, z) =
frame (input a) ++ z`, while its polynomial step bound `c * ((input a).length + 1) ^ d` is a
function of the primary input length `(input a).length` alone.

`IsPPTWithAux` and `IsOraclePPTWithAux` capture this machine contract for closed and oracle
probabilistic programs. Because `frame (input a)` is self-delimiting (`unframe (frame (input a) ++
z) = input a`), a machine can recover the primary input length from the combined input tape without
scanning `z`. Generalizing `IsTidyOraclePPTOn.runOracle` to any polynomial-time computable clock
therefore shows that every `IsOraclePPTWithAux` (resp. `IsPPTWithAux`) program is automatically a
standard `IsOraclePPTOn` (resp. `IsPPTOn`) program on `encPair input encBits`. Moreover, by the
input-tape prefix-locality theorem (`runOracle_append_take` / `runClosed_append_take`), a run of
`T = c * ((input a).length + 1) ^ d` steps on `frame (input a) ++ z` depends only on `z.take T`.

## Main definitions

* `Cslib.Probability.IsPPTWithAux`: closed uniform strict PPT clocked in the primary input.
* `Cslib.Probability.IsOraclePPTWithAux`: oracle uniform strict PPT clocked in the primary input.

## Main results

* `Cslib.Probability.IsOraclePPTOn.runOracle_of_clock`: any finite-control oracle machine run
  under a polynomial-time computable clock `clock : List Bool → ℕ` is `IsOraclePPTOn`.
* `Cslib.Probability.IsPPTWithAux.of_machine`,
  `Cslib.Probability.IsOraclePPTWithAux.of_machine`: explicit finite-control machine constructors.
* `Cslib.Probability.IsOraclePPTWithAux.isOraclePPTOn`,
  `Cslib.Probability.IsPPTWithAux.isPPTOn`: prefix-clocked programs are standard `IsOraclePPTOn`
  and `IsPPTOn` programs on `encPair input encBits`.
* `Cslib.Probability.computableInPolyTime_take_aux`,
  `Cslib.Probability.IsPPTOn.take_aux`,
  `Cslib.Probability.IsOraclePPTOn.take_aux`: truncating the auxiliary input to length
  `c * ((input a).length + 1) ^ d` preserves `IsPPTOn` and `IsOraclePPTOn`.
* `Cslib.Probability.IsOraclePPTOn.isOraclePPTWithAux_take`,
  `Cslib.Probability.IsPPTOn.isPPTWithAux_take`: truncating the auxiliary input of an
  `IsOraclePPTOn` or `IsPPTOn` program to `c * ((input a).length + 1) ^ d` upgrades it to
  `IsOraclePPTWithAux` or `IsPPTWithAux` clocked in `a` alone.
* `Cslib.Probability.IsPPTWithAux.length_le`,
  `Cslib.Probability.IsOraclePPTWithAux.length_le`: supported encoded outputs are bounded by a
  polynomial in the primary input length `(input a).length`, uniformly over all `z`.
* `Cslib.Probability.IsOraclePPTWithAux.exists_run_interpret_take`,
  `Cslib.Probability.IsPPTWithAux.exists_eval_take`: a prefix-clocked program on `(a, z)` has the
  exact same semantics as on `(a, z.take m)` for every `m ≥ c * ((input a).length + 1) ^ d`.
* `Cslib.Probability.IsPPTWithAux.preprocess`,
  `Cslib.Probability.IsOraclePPTWithAux.preprocess`: polynomial-time primary-input preprocessing
  for `IsPPTWithAux` and `IsOraclePPTWithAux`.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM

variable {Operation α β : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {output : β ↪ List Bool}

private theorem runOracle_of_clock_tidy {k : ℕ} {Control : Type}
    [Finite Operation] [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Operation)
    {clock : List Bool → ℕ} (hclock : ComputableInPolyTime clock encBits encUnary) :
    IsTidyOraclePPTOn encBits encBits
      (fun word : List Bool => machine.runOracle (clock word) word) := by
  let _ := Fintype.ofFinite Operation
  obtain ⟨cf, hconfigurationSize⟩ :=
    length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  have hclockPoly : PolyBounded (fun word => (encBits word).length) clock := by
    simpa only [encUnary_apply, List.length_replicate] using hclock.polyBounded_length
  have hstart : ComputableInPolyTime
      (fun word => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial word)
      encBits encFiniteConfig := by fun_prop
  let step (word : List Bool) (cfg : FiniteConfig k Bool Control Operation) :
      WordOracleComp Operation (FiniteConfig k Bool Control Operation) :=
    machine.finiteStep (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op query => List.take (clock word) <$> ProbOracleComp.query (op, query)) cfg
  have hstep : IsTidyOraclePPTOn (encPair encBits encFiniteConfig) encFiniteConfig
      (fun pair => step pair.1 pair.2) :=
    (IsTidyOraclePPTOn.finiteStep machine).preprocess
      (prepare := fun pair : List Bool × FiniteConfig k Bool Control Operation =>
        (clock pair.1, pair.2)) (by fun_prop)
  have hloop := (IsTidyOraclePPTOn.iterateWith_spec hclock hstart hstep
    (fun word i cfg => FiniteConfig.SpaceBound word.length i (clock word) cfg)
    (fun word => FiniteConfig.spaceBound_init _ _ _)
    (by
      intro word i cfg _ hcfg next hnext
      cases hstate : cfg.tapes.state with
      | none =>
        simp only [step, MultiTapeMachine.finiteStep, hstate] at hnext
        exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸
          hcfg.mono le_rfl (Nat.le_succ i) le_rfl
      | some control =>
        simp only [step, MultiTapeMachine.finiteStep, hstate] at hnext
        obtain ⟨action, _, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
        cases action with
        | step action symbol move =>
          exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸ hcfg.step action symbol move
        | query channel control =>
          obtain ⟨answer, hanswer, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
          obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hanswer
          exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸
            hcfg.receive channel control _ (List.length_take_le _ _))
    (size := fun word => cf * (word.length + clock word + clock word + 1))
    ((PolyBounded.const cf).mul
      (((PolyBounded.self.add hclockPoly).add hclockPoly).add (.const 1)))
    (fun word i cfg hi hcfg => (hconfigurationSize _ _ _ cfg hcfg).trans
      (Nat.mul_le_mul_left cf (by lia)))).1
  refine (hloop.map (by fun_prop : ComputableInPolyTime
    (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output)
    encFiniteConfig encBits)).congr fun word State oracle s => ?_
  rw [← finiteRunFrom_take_runOracle]
  rfl

/-- Every clocked run of a finite-control oracle machine under a polynomial-time computable clock
`clock : List Bool → ℕ` is `IsOraclePPTOn`. -/
theorem IsOraclePPTOn.runOracle_of_clock {k : ℕ} {Control : Type}
    [Finite Operation] [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Operation)
    {clock : List Bool → ℕ} (hclock : ComputableInPolyTime clock encBits encUnary) :
    IsOraclePPTOn encBits encBits
      (fun word : List Bool => machine.runOracle (clock word) word) :=
  (runOracle_of_clock_tidy machine hclock).isOraclePPTOn

/-- **Closed uniform strict PPT clocked in the primary input.** One finite fair-coin machine runs
on the pair encoding `encPair input encBits (a, z) = frame (input a) ++ z`, clocked by a polynomial
`c * ((input a).length + 1) ^ d` in the primary input length `(input a).length` alone. -/
def IsPPTWithAux {α β : Type} (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → List Bool → ProbComp β) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : Turing.MultiTapePTM k Bool State)
    (c d : ℕ), ∀ a z, (ProbComp.eval (program a z)).map output =
      ProbComp.eval (machine.runClosed (c * ((input a).length + 1) ^ d)
        (encPair input encBits (a, z)))

/-- **Oracle uniform strict PPT clocked in the primary input.** One finite oracle fair-coin machine
runs on `encPair input encBits (a, z) = frame (input a) ++ z`, clocked by a polynomial
`c * ((input a).length + 1) ^ d` in `(input a).length` alone, preserving the full joint output and
external oracle state for every stateful handler. -/
def IsOraclePPTWithAux {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → List Bool → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a z (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (output <$> program a z)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (machine.runOracle (c * ((input a).length + 1) ^ d)
            (encPair input encBits (a, z)))).run s

/-- A fixed finite-control closed machine and polynomial clock in the primary input supply an
`IsPPTWithAux` certificate directly. -/
theorem IsPPTWithAux.of_machine {k : ℕ} {State : Type} [Finite State]
    (machine : Turing.MultiTapePTM k Bool State) (c d : ℕ) :
    IsPPTWithAux input encBits
      (fun a z =>
        machine.runClosed (c * ((input a).length + 1) ^ d) (encPair input encBits (a, z))) := by
  refine ⟨k, State, inferInstance, machine, c, d, fun a z => ?_⟩
  simp only [encBits, Function.Embedding.coe_refl, PMF.map_id]

/-- Distributional equality preserves `IsPPTWithAux`. -/
theorem IsPPTWithAux.congr {program program' : α → List Bool → ProbComp β}
    (h : IsPPTWithAux input output program)
    (heq : ∀ a z, ProbComp.eval (program a z) = ProbComp.eval (program' a z)) :
    IsPPTWithAux input output program' := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  exact ⟨k, State, hfinite, machine, c, d, fun a z =>
    (congrArg (PMF.map output) (heq a z)).symm.trans (h a z)⟩

/-- A fixed finite-control oracle machine and polynomial clock in the primary input supply an
`IsOraclePPTWithAux` certificate directly. -/
theorem IsOraclePPTWithAux.of_machine [Finite Operation] {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ) :
    IsOraclePPTWithAux input encBits
      (fun a z =>
        machine.runOracle (c * ((input a).length + 1) ^ d) (encPair input encBits (a, z))) := by
  refine ⟨inferInstance, k, Control, inferInstance, machine, c, d, fun a z State oracle s => ?_⟩
  simp only [encBits, Function.Embedding.coe_refl, id_map]

/-- Equality of the complete stateful semantics preserves `IsOraclePPTWithAux`. -/
theorem IsOraclePPTWithAux.congr {program program' : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program)
    (heq : ∀ a z (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program a z)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program' a z)).run s) :
    IsOraclePPTWithAux input output program' := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, c, d, fun a z State oracle s => ?_⟩
  simpa only [OracleComp.interpret_map, StateT.run_map, heq] using h a z State oracle s

/-- Every `IsOraclePPTWithAux` program is a standard `IsOraclePPTOn` program on
`encPair input encBits`: the machine recovers `(input a).length` by unframing the self-delimiting
first component `frame (input a)` without reading `z`. -/
theorem IsOraclePPTWithAux.isOraclePPTOn {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program) :
    IsOraclePPTOn (encPair input encBits) output (fun (a, z) => program a z) := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  let clock (word : List Bool) : ℕ := c * ((unframe word).length + 1) ^ d
  have hclock : ComputableInPolyTime clock encBits encUnary := by
    dsimp only [clock]
    fun_prop
  have htidy : IsTidyOraclePPTOn (encPair input encBits) encBits
      (fun (a, z) => output <$> program a z) := by
    refine ((runOracle_of_clock_tidy machine hclock).preprocess
      (ComputableInPolyTime.of_eq (encOut := encBits)
        (f := encPair input encBits) fun _ => rfl)).congr fun (a, z) State oracle s => ?_
    have hunframe : clock (encPair input encBits (a, z)) = c * ((input a).length + 1) ^ d := by
      simp [clock, encPair_apply, unframe_frame_append]
    rw [hunframe, ← h a z State oracle s]
  exact IsOraclePPTOn.iff_encoded.mpr htidy.isOraclePPTOn

/-- Closed `IsPPTWithAux` programs lift to `IsOraclePPTWithAux` with no external operations. -/
theorem IsPPTWithAux.isOraclePPTWithAux {program : α → List Bool → ProbComp β}
    [Finite Operation] (h : IsPPTWithAux input output program) :
    IsOraclePPTWithAux (Operation := Operation) input output
      (fun a z => ProbOracleComp.sample (program a z)) := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  refine ⟨inferInstance, k, State, hfinite, MultiTapePTM.ofClosed machine, c, d,
    fun a z OracleState oracle s => ?_⟩
  change ProbOracleComp.runWith oracle _ s = ProbOracleComp.runWith oracle _ s
  rw [MultiTapePTM.run_interpret_runOracle_ofClosed, ← h a z, ← ProbOracleComp.sample_map,
    ProbOracleComp.runWith_sample, ProbComp.eval_map]

/-- Every `IsPPTWithAux` program is a standard `IsPPTOn` program on `encPair input encBits`. -/
theorem IsPPTWithAux.isPPTOn {program : α → List Bool → ProbComp β}
    (h : IsPPTWithAux input output program) :
    IsPPTOn (encPair input encBits) output (fun (a, z) => program a z) :=
  (h.isOraclePPTWithAux (Operation := Empty)).isOraclePPTOn.isPPTOn

/-- Truncating the auxiliary input word `z` to a polynomial in the primary input length
`(input a).length` is computable in plain polynomial time on `encPair input encBits`. -/
theorem computableInPolyTime_take_aux (input : α ↪ List Bool) (c d : ℕ) :
    ComputableInPolyTime
      (fun p : α × List Bool => (p.1, p.2.take (c * ((input p.1).length + 1) ^ d)))
      (encPair input encBits) (encPair input encBits) := by
  have hlen : ComputableInPolyTime (fun p : α × List Bool => (input p.1).length)
      (encPair input encBits) encUnary :=
    (ComputableInPolyTime.encoding_length input).comp (.fst input encBits)
  fun_prop

/-- Truncating the auxiliary input of a standard `IsPPTOn` program to a polynomial in the primary
input length preserves `IsPPTOn`. -/
theorem IsPPTOn.take_aux {program : α → List Bool → ProbComp β}
    (h : IsPPTOn (encPair input encBits) output (fun (a, z) => program a z)) (c d : ℕ) :
    IsPPTOn (encPair input encBits) output
      (fun (a, z) => program a (z.take (c * ((input a).length + 1) ^ d))) :=
  h.preprocess (computableInPolyTime_take_aux input c d)

/-- Truncating the auxiliary input of a standard `IsOraclePPTOn` program to a polynomial in the
primary input length preserves `IsOraclePPTOn`. -/
theorem IsOraclePPTOn.take_aux {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTOn (encPair input encBits) output (fun (a, z) => program a z)) (c d : ℕ) :
    IsOraclePPTOn (encPair input encBits) output
      (fun (a, z) => program a (z.take (c * ((input a).length + 1) ^ d))) :=
  h.preprocess' (computableInPolyTime_take_aux input c d)

/-! ### Upgrading prefix-truncated `IsOraclePPTOn` / `IsPPTOn` programs to
`IsOraclePPTWithAux` / `IsPPTWithAux` -/

private theorem RunsWords.of_runFrom {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    {x : List Bool} {ws₀ ws₁ : Fin k → List Bool} {out₀ emitted : List Bool} {time : ℕ}
    (hrun : tm.runFrom (wordsCfg x (some tm.q₀) ws₀ out₀) time =
      wordsCfg x none ws₁ (out₀ ++ emitted)) :
    (ofDeterministic tm : MultiTapePTM k Bool State Operation).RunsWords
      x ws₀ out₀ time (pure emitted) (fun _ => ws₁) id := by
  intro OracleState oracle s cfg htapes hbuf
  have htapes' : cfg.tapes = wordsCfg x (some tm.q₀) ws₀ out₀ := htapes
  dsimp only
  rw [run_interpret_runOracleConfigFrom_ofDeterministic, htapes', hrun]
  simp only [ProbOracleComp.runWith_pure, PMF.pure_map, id_eq, PMF.support_pure,
    Set.mem_singleton_iff, forall_eq, true_and]
  exact hbuf

private def unframePrefixCore : MultiTapeTM 0 Bool Bool :=
  ofTr false fun state inp _ =>
    match state, inp with
    | false, some true => ⟨1, Fin.elim0, none, some true⟩
    | true, some b => ⟨1, Fin.elim0, some b, some false⟩
    | _, _ => ⟨0, Fin.elim0, none, none⟩

private noncomputable def unframePrefixTM : MultiTapeTM 0 Bool (Bool ⊕ RewindState) :=
  unframePrefixCore.seq (rewindInput Bool)

private def unframePrefixCfg (x : List Bool) (state : Option Bool) (idx : ℕ)
    (hidx : idx ≤ x.length) (out : List Bool) : Cfg 0 Bool Bool x where
  state := state
  inputPos := ⟨idx + 1, by lia⟩
  workTapes := Fin.elim0
  workTapePos := Fin.elim0
  output := out

private theorem runFrom_unframePrefixCore (x : List Bool) (rem : List Bool) :
    ∀ (pre suf : List Bool) (h : x = pre ++ frame rem ++ suf) (out : List Bool),
      unframePrefixCore.runFrom
        (unframePrefixCfg x (some false) pre.length (by subst h; simp) out)
        (2 * rem.length + 1) =
      unframePrefixCfg x none (pre.length + 2 * rem.length)
        (by subst h; simp [length_frame]; lia) (out ++ rem) := by
  induction rem with
  | nil =>
    intro pre suf h out
    have hlt : pre.length < x.length := by subst h; simp
    have hget : x[pre.length]'hlt = false := by subst h; simp
    let c₀ := unframePrefixCfg x (some false) pre.length hlt.le out
    have hstate : c₀.state = some false := rfl
    have hsym : c₀.inputSymbol = some false := by
      rw [inputSymbolInner pre.length (by simp [c₀, unframePrefixCfg]; lia) hlt]
      exact congrArg some hget
    change unframePrefixCore.runFrom c₀ 1 = _
    rw [runFrom_one, step_of_state hstate]
    refine Cfg.ext_zero_tapes ?_ ?_ ?_
    · simp only [unframePrefixCore, tr_ofTr, hsym, Action.apply_state, unframePrefixCfg]
    · simp only [unframePrefixCore, tr_ofTr, hsym, Action.apply_inputPos, moveInputPos_zero]
      simp [c₀, unframePrefixCfg]
    · simp only [unframePrefixCore, tr_ofTr, hsym, Action.apply_output, Option.toList_none]
      simp [c₀, unframePrefixCfg]
  | cons b rem ih =>
    intro pre suf h out
    have hlt₁ : pre.length < x.length := by subst h; simp
    have hget₁ : x[pre.length]'hlt₁ = true := by subst h; simp
    let c₀ := unframePrefixCfg x (some false) pre.length hlt₁.le out
    have hstate₁ : c₀.state = some false := rfl
    have hsym₁ : c₀.inputSymbol = some true := by
      rw [inputSymbolInner pre.length (by simp [c₀, unframePrefixCfg]; lia) hlt₁]
      exact congrArg some hget₁
    have hlt₂ : pre.length + 1 < x.length := by subst h; simp
    have hget₂ : x[pre.length + 1]'hlt₂ = b := by subst h; simp [List.getElem_append_right]
    let c₁ := unframePrefixCfg x (some true) (pre.length + 1) hlt₂.le out
    have hstate₂ : c₁.state = some true := rfl
    have hsym₂ : c₁.inputSymbol = some b := by
      rw [inputSymbolInner (pre.length + 1) (by simp [c₁, unframePrefixCfg]; lia) hlt₂]
      exact congrArg some hget₂
    have hstep₁ : unframePrefixCore.step c₀ = c₁ := by
      rw [step_of_state hstate₁]
      refine Cfg.ext_zero_tapes
        (by simp only [unframePrefixCore, tr_ofTr, hsym₁, Action.apply_state, c₁,
          unframePrefixCfg]) ?_
        (by simp only [unframePrefixCore, tr_ofTr, hsym₁, Action.apply_output, Option.toList_none]
            simp [c₀, c₁, unframePrefixCfg])
      apply Fin.ext
      simp only [unframePrefixCore, tr_ofTr, hsym₁, Action.apply_inputPos]
      change (moveInputPos _ .pos).val = pre.length + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp [c₀, unframePrefixCfg]; lia)]
      simp [c₀, unframePrefixCfg]
    have hlen₃ : (pre ++ [true, b]).length ≤ x.length := by
      have hlen := congrArg List.length h
      simp only [List.length_append, frame_cons, List.length_cons, List.length_nil] at hlen ⊢
      lia
    let c₂ := unframePrefixCfg x (some false) (pre ++ [true, b]).length hlen₃ (out ++ [b])
    have hstep₂ : unframePrefixCore.step c₁ = c₂ := by
      rw [step_of_state hstate₂]
      refine Cfg.ext_zero_tapes
        (by simp only [unframePrefixCore, tr_ofTr, hsym₂, Action.apply_state, c₂,
          unframePrefixCfg]) ?_
        (by simp only [unframePrefixCore, tr_ofTr, hsym₂, Action.apply_output, Option.toList_some]
            simp [c₁, c₂, unframePrefixCfg])
      apply Fin.ext
      simp only [unframePrefixCore, tr_ofTr, hsym₂, Action.apply_inputPos]
      change (moveInputPos _ .pos).val = (pre ++ [true, b]).length + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp [c₁, unframePrefixCfg]; lia)]
      simp [c₁, unframePrefixCfg]
    have hsplit : x = (pre ++ [true, b]) ++ frame rem ++ suf := by
      rw [h]
      simp [frame_cons, List.append_assoc]
    have h2 : unframePrefixCore.runFrom c₀ 2 = c₂ := by
      rw [MultiTapeTM.runFrom_succ, runFrom_one, hstep₁, hstep₂]
    have htot : 2 * (b :: rem).length + 1 = 2 + (2 * rem.length + 1) := by simp; lia
    have hrun : unframePrefixCore.runFrom c₀ (2 * (b :: rem).length + 1) =
        unframePrefixCore.runFrom c₂ (2 * rem.length + 1) := by
      rw [htot, MultiTapeTM.runFrom_add, h2]
    rw [show unframePrefixCfg x (some false) pre.length _ out = c₀ from rfl,
      hrun, ih (pre ++ [true, b]) suf hsplit (out ++ [b])]
    refine Cfg.ext_zero_tapes rfl ?_ (by simp [unframePrefixCfg, List.append_assoc])
    apply Fin.ext
    simp only [unframePrefixCfg, List.length_append, List.length_cons, List.length_nil]
    lia

private theorem computesTidily_unframePrefixTM (u z : List Bool) :
    (ofDeterministic unframePrefixTM :
      MultiTapePTM 0 Bool (Bool ⊕ RewindState) Operation).ComputesTidily
      (frame u ++ z) (4 * u.length + 3) (pure u) := by
  intro out₀
  apply RunsWords.of_runFrom
  have hcore := runFrom_unframePrefixCore (frame u ++ z) u [] z (by simp) out₀
  have hinit : wordsCfg (frame u ++ z) (some unframePrefixCore.q₀) (fun _ => []) out₀ =
      unframePrefixCfg (frame u ++ z) (some false) ([] : List Bool).length (by simp) out₀ :=
    Cfg.ext_zero_tapes rfl rfl rfl
  have hlen : ([] : List Bool).length + 2 * u.length ≤ (frame u ++ z).length := by
    simp only [List.length_nil, List.length_append, length_frame]
    lia
  have hcore' : unframePrefixCore.runFrom
      (wordsCfg (frame u ++ z) (some unframePrefixCore.q₀) (fun _ => []) out₀)
      (2 * u.length + 1) =
      unframePrefixCfg (frame u ++ z) none (([] : List Bool).length + 2 * u.length)
        hlen (out₀ ++ u) := by
    rw [hinit]
    exact hcore
  have hrew :
      (rewindInput Bool).runFrom
        ((unframePrefixCfg (frame u ++ z) none (([] : List Bool).length + 2 * u.length)
          hlen (out₀ ++ u)).withState (some (rewindInput Bool).q₀))
        (2 * u.length + 2) =
      wordsCfg (frame u ++ z) none (fun _ => []) (out₀ ++ u) := by
    have htime : 2 * u.length + 2 =
        (⟨(([] : List Bool).length + 2 * u.length) + 1, by lia⟩ :
          Fin ((frame u ++ z).length + 2)).val - 1 + 2 := by simp
    rw [htime]
    exact (runFrom_rewindInput _ Fin.elim0 Fin.elim0 (out₀ ++ u)).trans
      (Cfg.ext_zero_tapes rfl rfl rfl)
  have hseq := runFrom_seq hcore' rfl hrew rfl
  have htot : 4 * u.length + 3 = (2 * u.length + 1) + (2 * u.length + 2) := by lia
  rw [htot]
  exact (congrArg (fun c => unframePrefixTM.runFrom c _)
    (Cfg.ext_zero_tapes rfl rfl rfl)).trans (hseq.trans (Cfg.ext_zero_tapes rfl rfl rfl))

private def takeFromWorkCore : MultiTapeTM 1 Bool Unit :=
  ofTr () fun _ inp work =>
    match work 0 with
    | some _ =>
      match inp with
      | some b => ⟨1, fun _ => (none, 1), some b, some ()⟩
      | none => ⟨0, fun _ => (none, 1), none, some ()⟩
    | none => ⟨0, fun _ => (none, 0), none, none⟩

private noncomputable def takeFromWorkTM :
    MultiTapeTM 1 Bool ((Unit ⊕ RewindWorkState) ⊕ RewindState) :=
  (takeFromWorkCore.seq (rewindWork Bool)).seq ((rewindInput Bool).extendTapes (noTapes 1))

private def takeFromWorkCfg (x : List Bool) (K : ℕ) (state : Option Unit) (idx : ℕ)
    (hidx : idx ≤ x.length) (pos : ℕ) (out : List Bool) : Cfg 1 Bool Unit x where
  state := state
  inputPos := ⟨idx + 1, by lia⟩
  workTapes := fun _ => tapeOfList (List.replicate K true)
  workTapePos := fun _ => (pos : ℤ)
  output := out

private theorem runFrom_takeFromWorkCore (x : List Bool) (K : ℕ) (rem : ℕ) :
    ∀ (pos : ℕ) (_hpos : pos + rem = K) (idx : ℕ) (hidx : idx ≤ x.length) (out : List Bool),
      takeFromWorkCore.runFrom (takeFromWorkCfg x K (some ()) idx hidx pos out) (rem + 1) =
        takeFromWorkCfg x K none (min (idx + rem) x.length) (Nat.min_le_right _ _)
          (pos + rem) (out ++ (x.drop idx).take rem) := by
  induction rem with
  | zero =>
    intro pos hpos idx hidx out
    have hposK : pos = K := by lia
    subst hposK
    let c₀ := takeFromWorkCfg x pos (some ()) idx hidx pos out
    have hstate : c₀.state = some () := rfl
    have hwork : c₀.workTapeSymbols 0 = none := by
      simp [c₀, takeFromWorkCfg, Cfg.workTapeSymbols, tapeOfList]
    change takeFromWorkCore.runFrom c₀ 1 = _
    rw [runFrom_one, step_of_state hstate]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp only [takeFromWorkCore, tr_ofTr, hwork, Action.apply_state, takeFromWorkCfg]
    · simp only [takeFromWorkCore, tr_ofTr, hwork, Action.apply_inputPos, moveInputPos_zero]
      simp [c₀, takeFromWorkCfg, Nat.min_eq_left hidx]
    · funext j
      simp only [takeFromWorkCore, tr_ofTr, hwork, Action.apply_workTapes]
      rfl
    · funext j
      simp only [takeFromWorkCore, tr_ofTr, hwork, Action.apply_workTapePos, SignType.coe_zero,
        add_zero]
      simp [c₀, takeFromWorkCfg]
    · simp only [takeFromWorkCore, tr_ofTr, hwork, Action.apply_output, Option.toList_none]
      simp [c₀, takeFromWorkCfg]
  | succ rem ih =>
    intro pos hpos idx hidx out
    have hltK : pos < K := by lia
    let c₀ := takeFromWorkCfg x K (some ()) idx hidx pos out
    have hstate : c₀.state = some () := rfl
    have hwork : c₀.workTapeSymbols 0 = some true := by
      simp [c₀, takeFromWorkCfg, Cfg.workTapeSymbols, tapeOfList, hltK]
    by_cases hlt : idx < x.length
    · have hsym : c₀.inputSymbol = some (x[idx]'hlt) := by
        rw [inputSymbolInner idx (by simp [c₀, takeFromWorkCfg]; lia) hlt]
      let c₁ := takeFromWorkCfg x K (some ()) (idx + 1) hlt (pos + 1) (out ++ [x[idx]'hlt])
      have hstep : takeFromWorkCore.step c₀ = c₁ := by
        rw [step_of_state hstate]
        refine Cfg.ext ?_ ?_ ?_ ?_ ?_
        · simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_state, c₁,
            takeFromWorkCfg]
        · apply Fin.ext
          simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_inputPos]
          change (moveInputPos _ .pos).val = idx + 1 + 1
          rw [moveInputPos_pos_of_ne_right _ (by simp [c₀, takeFromWorkCfg]; lia)]
          simp [c₀, takeFromWorkCfg]
        · funext j
          simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_workTapes]
          rfl
        · funext j
          simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_workTapePos]
          simp [c₀, c₁, takeFromWorkCfg, Nat.cast_add]
        · simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_output,
            Option.toList_some]
          simp [c₀, c₁, takeFromWorkCfg]
      have hrun : takeFromWorkCore.runFrom c₀ (rem + 1 + 1) =
          takeFromWorkCore.runFrom c₁ (rem + 1) := by
        rw [show rem + 1 + 1 = 1 + (rem + 1) by lia, MultiTapeTM.runFrom_add, runFrom_one, hstep]
      rw [show takeFromWorkCfg x K (some ()) idx hidx pos out = c₀ from rfl,
        hrun, ih (pos + 1) (by lia) (idx + 1) hlt (out ++ [x[idx]'hlt])]
      have hdrop : x[idx]'hlt :: (x.drop (idx + 1)).take rem = (x.drop idx).take (rem + 1) := by
        rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
      refine Cfg.ext rfl ?_ rfl ?_ (by simp [takeFromWorkCfg, List.append_assoc, hdrop])
      · apply Fin.ext
        simp only [takeFromWorkCfg]
        lia
      · funext j
        simp only [takeFromWorkCfg]
        lia
    · have hidx_eq : idx = x.length := by lia
      subst hidx_eq
      have hsym : c₀.inputSymbol = none :=
        inputSymbol_eq_none_of_boundary (Or.inr (by simp [c₀, takeFromWorkCfg]))
      let c₁ := takeFromWorkCfg x K (some ()) x.length le_rfl (pos + 1) out
      have hstep : takeFromWorkCore.step c₀ = c₁ := by
        rw [step_of_state hstate]
        refine Cfg.ext ?_ ?_ ?_ ?_ ?_
        · simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_state, c₁,
            takeFromWorkCfg]
        · simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_inputPos,
            moveInputPos_zero]
          rfl
        · funext j
          simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_workTapes]
          rfl
        · funext j
          simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_workTapePos]
          simp [c₀, c₁, takeFromWorkCfg, Nat.cast_add]
        · simp only [takeFromWorkCore, tr_ofTr, hwork, hsym, Action.apply_output,
            Option.toList_none]
          simp [c₀, c₁, takeFromWorkCfg]
      have hrun : takeFromWorkCore.runFrom c₀ (rem + 1 + 1) =
          takeFromWorkCore.runFrom c₁ (rem + 1) := by
        rw [show rem + 1 + 1 = 1 + (rem + 1) by lia, MultiTapeTM.runFrom_add, runFrom_one, hstep]
      rw [show takeFromWorkCfg x K (some ()) x.length hidx pos out = c₀ from rfl,
        hrun, ih (pos + 1) (by lia) x.length le_rfl out]
      refine Cfg.ext rfl ?_ rfl ?_ (by simp [takeFromWorkCfg])
      · apply Fin.ext
        simp only [takeFromWorkCfg]
        lia
      · funext j
        simp only [takeFromWorkCfg]
        lia

private theorem runFrom_takeFromWorkTM (x : List Bool) (K : ℕ) (out₀ : List Bool) :
    takeFromWorkTM.runFrom
      (wordsCfg x (some takeFromWorkTM.q₀) (fun _ => List.replicate K true) out₀) (3 * K + 5) =
      wordsCfg x none (fun _ => List.replicate K true) (out₀ ++ x.take K) := by
  have hcore := runFrom_takeFromWorkCore x K K 0 (by lia) 0 (Nat.zero_le _) out₀
  simp only [Nat.zero_add, List.drop_zero] at hcore
  have hinit : wordsCfg x (some takeFromWorkCore.q₀) (fun _ => List.replicate K true) out₀ =
      takeFromWorkCfg x K (some ()) 0 (Nat.zero_le _) 0 out₀ :=
    Cfg.ext rfl rfl rfl rfl rfl
  have hcore' : takeFromWorkCore.runFrom
      (wordsCfg x (some takeFromWorkCore.q₀) (fun _ => List.replicate K true) out₀) (K + 1) =
      takeFromWorkCfg x K none (min K x.length) (Nat.min_le_right _ _) K (out₀ ++ x.take K) := by
    rw [hinit]
    exact hcore
  let mid₁ := takeFromWorkCfg x K none (min K x.length) (Nat.min_le_right _ _) K (out₀ ++ x.take K)
  let mid₂ : Cfg 1 Bool RewindWorkState x :=
    ⟨none, ⟨min K x.length + 1, by lia⟩, fun _ => tapeOfList (List.replicate K true),
      fun _ => 0, out₀ ++ x.take K⟩
  have hrewW :
      (rewindWork Bool).runFrom (mid₁.withState (some (rewindWork Bool).q₀)) (K + 2) = mid₂ := by
    let w := List.replicate K true
    have hlen : w.length = K := by simp [w]
    change (rewindWork Bool).runFrom
      ⟨some (rewindWork Bool).q₀, ⟨min K x.length + 1, by lia⟩, fun _ => tapeOfList w,
        fun _ => (K : ℤ), out₀ ++ x.take K⟩ (K + 2) =
      ⟨none, ⟨min K x.length + 1, by lia⟩, fun _ => tapeOfList w, fun _ => 0, out₀ ++ x.take K⟩
    rw [← hlen]
    exact runFrom_rewindWork_none _ _ _ rfl le_rfl
  have hseq₁ := runFrom_seq hcore' rfl hrewW rfl
  let rewI : MultiTapeTM 1 Bool RewindState := (rewindInput Bool).extendTapes (noTapes 1)
  have hrewI_early :
      rewI.runFrom ((Sequential.rightCfg (State₀ := Unit) mid₂).withState (some rewI.q₀))
        (min K x.length + 2) =
      wordsCfg x none (fun _ => List.replicate K true) (out₀ ++ x.take K) := by
    dsimp only [rewI]
    rw [runFrom_noTapes]
    have hno : noTapesCfg ((Sequential.rightCfg (State₀ := Unit) mid₂).withState
        (some rewI.q₀)) =
        ⟨some (rewindInput Bool).q₀, ⟨min K x.length + 1, by lia⟩,
          Fin.elim0, Fin.elim0, out₀ ++ x.take K⟩ :=
      Cfg.ext_zero_tapes rfl rfl rfl
    have htime : min K x.length + 2 =
        (⟨min K x.length + 1, by lia⟩ : Fin (x.length + 2)).val - 1 + 2 := by simp
    rw [hno, htime, runFrom_rewindInput]
    exact Cfg.ext rfl rfl rfl rfl rfl
  have hrewI :
      rewI.runFrom ((Sequential.rightCfg (State₀ := Unit) mid₂).withState (some rewI.q₀)) (K + 2) =
      wordsCfg x none (fun _ => List.replicate K true) (out₀ ++ x.take K) := by
    rw [runFrom_eq_of_halt rewI _ (by lia : min K x.length + 2 ≤ K + 2)
      (by rw [hrewI_early]; rfl), hrewI_early]
  have hseq₂ := runFrom_seq hseq₁ rfl hrewI rfl
  have htot : 3 * K + 5 = ((K + 1) + (K + 2)) + (K + 2) := by lia
  rw [htot]
  exact (congrArg (fun c => takeFromWorkTM.runFrom c _)
    (Cfg.ext rfl rfl rfl rfl rfl)).trans (hseq₂.trans (Cfg.ext rfl rfl rfl rfl rfl))

private noncomputable def takePrefixPTM {k : ℕ} {State : Type}
    (budget : MultiTapePTM k Bool State Operation) :
    MultiTapePTM (k + 1) Bool
      ((State ⊕ RewindWorkState) ⊕
        (((Unit ⊕ RewindWorkState) ⊕ RewindState) ⊕ Unit ⊕ RewindWorkState)) Operation :=
  budget.outputToWord.seq
    (((ofDeterministic takeFromWorkTM).extendTapes (tapeEmb (Fin.last k))).seq
      (ofDeterministic ((clearWork Bool).extendTapes (tapeEmb (Fin.last k)))))

private theorem computesTidily_takePrefixPTM {k : ℕ} {State : Type}
    {budget : MultiTapePTM k Bool State Operation} {x : List Bool} {t K : ℕ}
    (hbudget : budget.ComputesTidily x t (pure (List.replicate K true))) :
    (takePrefixPTM budget).ComputesTidily x (t + 7 * K + 10) (pure (x.take K)) := by
  dsimp only [takePrefixPTM]
  rw [computesTidily_iff_nil_output]
  let w := List.replicate K true
  let ws : Fin (k + 1) → List Bool := Function.update (fun _ => []) (Fin.last k) w
  have hp₁ : budget.outputToWord.RunsWords x (fun _ => []) [] (t + (K + 2)) (pure w)
      (fun w' => Function.update (fun _ => []) (Fin.last k) w') (fun _ => []) := by
    refine hbudget.outputToWord_of_le (l := K) ?_ []
    intro OracleState oracle s w' s' hw'
    simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hw'
    rcases Prod.mk.inj hw' with ⟨rfl, rfl⟩
    simp
  have hinj₁ : Function.Injective
      (fun w' : List Bool => (Function.update (fun _ : Fin (k + 1) => []) (Fin.last k) w',
        ([] : List Bool))) := by
    intro w₁ w₂ heq
    have hfun := congrFun (congrArg Prod.fst heq) (Fin.last k)
    simpa only [Function.update_self] using hfun
  have hp₂ : ((ofDeterministic takeFromWorkTM : MultiTapePTM 1 Bool _ Operation).extendTapes
      (tapeEmb (Fin.last k))).RunsWords x ws [] (3 * K + 5) (pure (x.take K))
      (fun _ => ws) id := by
    have h1 : (ofDeterministic takeFromWorkTM : MultiTapePTM 1 Bool _ Operation).RunsWords
        x (fun j => ws (tapeEmb (Fin.last k) j)) [] (3 * K + 5) (pure (x.take K))
        (fun _ _ => w) id := by
      have hsel : (fun j : Fin 1 => ws (tapeEmb (Fin.last k) j)) = fun _ => w := by
        funext j
        simp [ws, tapeEmb_apply]
      rw [hsel]
      exact RunsWords.of_runFrom (runFrom_takeFromWorkTM x K [])
    have hext := h1.extendTapes (tapeEmb (Fin.last k))
    have hupd : (fun (_ : List Bool) (l : Fin (k + 1)) =>
        (MultiTapeTM.partialInv (tapeEmb (Fin.last k)) l).elim (ws l) (fun _ => w)) =
        fun _ => ws := by
      funext _ l
      rcases hl : MultiTapeTM.partialInv (tapeEmb (Fin.last k)) l with _ | j
      · rfl
      · have hj := MultiTapeTM.partialInv_eq_some (tapeEmb (Fin.last k)) hl
        simp only [tapeEmb_apply] at hj
        subst hj
        simp [ws]
    simpa only [hupd] using hext
  have hinj₂ : Function.Injective (fun y : List Bool => (ws, id y)) :=
    fun _ _ heq => congrArg Prod.snd heq
  have hp₃ : ∀ y (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s₀ s₁ : OracleState),
      (y, s₁) ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (pure (x.take K))).run s₀).support →
      (ofDeterministic (Oracle := Operation)
        ((clearWork Bool).extendTapes (tapeEmb (Fin.last k)))).RunsWords
        x ws ([] ++ id y) (3 * (K + 1)) (pure ())
        (fun _ _ => []) (fun _ => []) := by
    intro y _ _ _ _ _
    have hlen : w.length = K := by simp [w]
    rw [← hlen]
    exact RunsWords.of_transformsTapes (Operation := Operation) (out₀ := [] ++ id y)
      (transformsTapes_clearWork_only (Fin.last k) w) rfl (fun _ _ hQ => hQ)
  have hp₂₃ : ∀ w' (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w', s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (pure w)).run s).support →
      (((ofDeterministic takeFromWorkTM : MultiTapePTM 1 Bool _ Operation).extendTapes
        (tapeEmb (Fin.last k))).seq
        (ofDeterministic (Oracle := Operation)
          ((clearWork Bool).extendTapes (tapeEmb (Fin.last k))))).RunsWords
        x (Function.update (fun _ => []) (Fin.last k) w') ([] ++ []) ((3 * K + 5) + 3 * (K + 1))
        (pure (x.take K)) (fun _ _ => []) id := by
    intro w' OracleState oracle s s' hw'
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff] at hw'
    rcases Prod.mk.inj hw' with ⟨rfl, rfl⟩
    have hseq := hp₂.seq_pure_right hinj₂ hp₃
    have happend : (fun a : List Bool => id a ++ []) = id := by
      funext a
      exact List.append_nil a
    simpa only [List.nil_append, happend] using hseq
  have hseq := (hp₁.seq_bind hinj₁ hp₂₃).of_map Prod.snd (fun _ _ => []) id
  have hbind :
      (Prod.snd <$> ((pure w : WordOracleComp Operation (List Bool)) >>=
        fun a => (fun b => (a, b)) <$> pure (x.take K))) =
      pure (x.take K) := by simp
  rw [hbind] at hseq
  have htot : t + 7 * K + 10 = (t + (K + 2)) + ((3 * K + 5) + 3 * (K + 1)) := by lia
  rw [htot]
  simpa only [List.nil_append] using hseq

/-- **Upgrading prefix-truncated `IsOraclePPTOn` to `IsOraclePPTWithAux`.**
If `program` is a standard `IsOraclePPTOn` program on `encPair input encBits`, then truncating its
auxiliary input word `z` to a polynomial `c * ((input a).length + 1) ^ d` in the primary input
length `(input a).length` yields an `IsOraclePPTWithAux` program clocked in `a` alone. -/
theorem IsOraclePPTOn.isOraclePPTWithAux_take
    {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTOn (encPair input encBits) output (fun (a, z) => program a z)) (c d : ℕ) :
    IsOraclePPTWithAux input output
      (fun a z => program a (z.take (c * ((input a).length + 1) ^ d))) := by
  have hops := h.1
  let limitFn (u : List Bool) : ℕ := 2 * u.length + 1 + c * (u.length + 1) ^ d
  have hlimit : ComputableInPolyTime limitFn encBits encUnary := by
    dsimp only [limitFn]
    fun_prop
  obtain ⟨_, kL, ControlL, hfiniteL, tmLimit, cL, dL, htmLimit⟩ :=
    IsTidyOraclePPTOn.of_computableInPolyTime (Operation := Operation) hlimit
  obtain ⟨_, kP, ControlP, hfiniteP, tmProg, cP, dP, htmProg⟩ := h.isTidyOraclePPTOn
  let tmUnframe : MultiTapePTM 0 Bool (Bool ⊕ RewindState) Operation :=
    ofDeterministic unframePrefixTM
  let tmBudget := tmLimit.tidyComp tmUnframe true
  let tmTrunc := takePrefixPTM tmBudget
  let tmFull := tmProg.tidyComp tmTrunc true
  let tUnframe (n : ℕ) : ℕ := 4 * n + 3
  let tLimit (n : ℕ) : ℕ := cL * (n + 1) ^ dL
  let tBudget (n : ℕ) : ℕ := tUnframe n + tLimit n + 4 * n + 9
  let K (n : ℕ) : ℕ := 2 * n + 1 + c * (n + 1) ^ d
  let tTrunc (n : ℕ) : ℕ := tBudget n + 7 * K n + 10
  let tProg (n : ℕ) : ℕ := cP * (K n + 1) ^ dP
  let tFull (n : ℕ) : ℕ := tTrunc n + tProg n + 4 * K n + 9
  have hpoly : Cslib.PolynomiallyBounded tFull := by
    dsimp only [tFull, tTrunc, tProg, tBudget, tUnframe, tLimit, K]
    fun_prop
  obtain ⟨cF, dF, hleF⟩ :=
    (PolyBounded.of_polynomiallyBounded (fun a : α => (input a).length) hpoly).exists_le
  refine ⟨hops, _, _, inferInstance, tmFull, cF, dF, fun a z State oracle s => ?_⟩
  let u := input a
  let n := u.length
  let x := encPair input encBits (a, z)
  have hx : x = frame u ++ z := rfl
  have hunframe : tmUnframe.ComputesTidily x (tUnframe n) (pure u) :=
    computesTidily_unframePrefixTM u z
  have hbudget : tmBudget.ComputesTidily x (tBudget n) (pure (List.replicate (K n) true)) := by
    have hcomp := hunframe.comp_of_le (prog₂ := fun w => pure (encUnary (limitFn w)))
      (t₂ := tLimit n) (l := n) true
      (fun OracleState oracle s w s' hw => by
        simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hw
        rcases Prod.mk.inj hw with ⟨rfl, rfl⟩
        exact le_rfl)
      (fun w OracleState oracle s s' hw => by
        simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hw
        rcases Prod.mk.inj hw with ⟨rfl, rfl⟩
        simpa only [map_pure, encBits_apply, tLimit, n] using htmLimit u)
    simpa only [pure_bind, encUnary_apply, limitFn, K, n] using hcomp
  have htrunc : tmTrunc.ComputesTidily x (tTrunc n)
      (pure (encPair input encBits (a, z.take (c * (n + 1) ^ d)))) := by
    have htake : x.take (K n) = encPair input encBits (a, z.take (c * (n + 1) ^ d)) := by
      have hlen_frame : (frame u).length = 2 * n + 1 := length_frame u
      change (frame u ++ z).take (2 * n + 1 + c * (n + 1) ^ d) = frame u ++ z.take (c * (n + 1) ^ d)
      rw [← hlen_frame, List.take_append]
      simp
    simpa only [htake] using computesTidily_takePrefixPTM hbudget
  let wTrunc := encPair input encBits (a, z.take (c * (n + 1) ^ d))
  have hwTrunc_len : wTrunc.length ≤ K n := by
    simp only [wTrunc, encPair_apply, encBits_apply, List.length_append, length_frame, K, n]
    have := List.length_take_le (c * (u.length + 1) ^ d) z
    lia
  have hfull : tmFull.ComputesTidily x (cF * (n + 1) ^ dF)
      (output <$> program a (z.take (c * (n + 1) ^ d))) := by
    have hcomp := htrunc.comp_of_le
      (prog₂ := fun _ => output <$> program a (z.take (c * (n + 1) ^ d)))
      (t₂ := tProg n) (l := K n) true
      (fun OracleState oracle s w s' hw => by
        simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hw
        rcases Prod.mk.inj hw with ⟨rfl, rfl⟩
        exact hwTrunc_len)
      (fun w OracleState oracle s s' hw => by
        simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hw
        rcases Prod.mk.inj hw with ⟨rfl, rfl⟩
        refine (htmProg (a, z.take (c * (n + 1) ^ d))).mono ?_
        exact Nat.mul_le_mul_left cP (Nat.pow_le_pow_left (Nat.add_le_add_right hwTrunc_len 1) dP))
    rw [pure_bind] at hcomp
    exact hcomp.mono (hleF a)
  exact (hfull.runOracle oracle s).symm

/-- **Upgrading prefix-truncated `IsPPTOn` to `IsPPTWithAux`.**
If `program` is a standard `IsPPTOn` program on `encPair input encBits`, then truncating its
auxiliary input word `z` to a polynomial `c * ((input a).length + 1) ^ d` in `(input a).length`
yields an `IsPPTWithAux` program clocked in `a` alone. -/
theorem IsPPTOn.isPPTWithAux_take {program : α → List Bool → ProbComp β}
    (h : IsPPTOn (encPair input encBits) output (fun (a, z) => program a z)) (c d : ℕ) :
    IsPPTWithAux input output
      (fun a z => program a (z.take (c * ((input a).length + 1) ^ d))) := by
  have horacle :
      IsOraclePPTWithAux (Operation := Empty) input output
        (fun a z => ProbOracleComp.sample (program a (z.take (c * ((input a).length + 1) ^ d)))) :=
    IsOraclePPTOn.isOraclePPTWithAux_take
      (program := fun a z => ProbOracleComp.sample (program a z))
      (h.isOraclePPTOn (Operation := Empty)) c d
  obtain ⟨_, k, Control, hfinite, machine, c', d', hmachine⟩ := horacle
  refine ⟨k, Control, hfinite, machine, c', d', fun a z => ?_⟩
  have hrun := congrArg (PMF.map Prod.fst) (hmachine a z Unit (fun q => q.1.elim) ())
  rw [← ProbOracleComp.sample_map, ProbOracleComp.run_interpret_sample,
    runOracle_eq_sample_runClosed, ProbOracleComp.run_interpret_sample,
    PMF.map_comp, PMF.map_comp, ProbComp.eval_map] at hrun
  have hid : (Prod.fst ∘ fun word : List Bool => (word, ())) = id := rfl
  rwa [hid, PMF.map_id, PMF.map_id] at hrun

/-- Every supported encoded output of an `IsPPTWithAux` program has length bounded by a polynomial
in the primary input length `(input a).length`, uniformly over all auxiliary inputs `z`. -/
theorem IsPPTWithAux.length_le {program : α → List Bool → ProbComp β}
    (h : IsPPTWithAux input output program) :
    ∃ c d : ℕ, ∀ (a : α) (z : List Bool) (result : β),
      result ∈ (ProbComp.eval (program a z)).support →
      (output result).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a z result hresult => ?_⟩
  have hmap := (PMF.mem_support_map_iff output (ProbComp.eval (program a z))
    (output result)).mpr ⟨result, hresult, rfl⟩
  rw [h a z] at hmap
  exact machine.length_output_eval_runClosed_le _ _ _ hmap

/-- Every supported encoded output of an `IsOraclePPTWithAux` program has length bounded by a
polynomial in `(input a).length`, uniformly over all auxiliary inputs `z` and all oracle replies. -/
theorem IsOraclePPTWithAux.length_le {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program) :
    ∃ c d : ℕ, ∀ (a : α) (z : List Bool) (State : Type)
      (oracle : Operation × List Bool → StateT State PMF (List Bool)) (s s' : State) (result : β),
      (result, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program a z)).run s).support →
      (output result).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨_, k, Control, _, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a z State oracle s s' result hresult => ?_⟩
  have hmap : (output result, s') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (output <$> program a z)).run s).support := by
    rw [OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, s'), hresult, rfl⟩
  rw [h a z State oracle s] at hmap
  exact machine.length_output_runOracle_le oracle _ _ _ s s' hmap

/-- **Prefix truncation for `IsPPTWithAux`.** A closed program clocked in `a` produces the exact
same output distribution on `(a, z.take m)` as on `(a, z)` whenever `m` is at least its polynomial
clock `c * ((input a).length + 1) ^ d`. -/
theorem IsPPTWithAux.exists_eval_take {program : α → List Bool → ProbComp β}
    (h : IsPPTWithAux input output program) :
    ∃ c d : ℕ, ∀ (a : α) (z : List Bool) {m : ℕ},
      c * ((input a).length + 1) ^ d ≤ m →
      ProbComp.eval (program a (z.take m)) = ProbComp.eval (program a z) := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a z {m} hm => PMF.map_injective output.injective ?_⟩
  rw [h a (z.take m), h a z]
  simp only [encPair_apply, encBits, Function.Embedding.coe_refl, id]
  rw [machine.runClosed_append_take_of_le hm]

/-- **Prefix truncation for `IsOraclePPTWithAux`.** An oracle program clocked in `a` produces the
exact same joint distribution of `(result, finalState)` on `(a, z.take m)` as on `(a, z)` under
every stateful oracle handler whenever `m ≥ c * ((input a).length + 1) ^ d`. -/
theorem IsOraclePPTWithAux.exists_run_interpret_take
    {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program) :
    ∃ c d : ℕ, ∀ (a : α) (z : List Bool) {m : ℕ},
      c * ((input a).length + 1) ^ d ≤ m →
      ∀ (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) (s : State),
        (OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
            (program a (z.take m))).run s =
        (OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
            (program a z)).run s := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a z {m} hm State oracle s => ?_⟩
  have hinj : Function.Injective (fun p : β × State => (output p.1, p.2)) := by
    intro ⟨b₁, s₁⟩ ⟨b₂, s₂⟩ heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (output.injective heq.1) heq.2
  apply PMF.map_injective hinj
  have h₁ := h a (z.take m) State oracle s
  have h₂ := h a z State oracle s
  simp only [OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at h₁ h₂
  rw [h₁, h₂]
  simp only [encPair_apply, encBits, Function.Embedding.coe_refl, id]
  rw [machine.runOracle_append_take_of_le hm]

/-- Polynomial-time deterministic preprocessing of the primary input preserves `IsPPTWithAux`. -/
theorem IsPPTWithAux.preprocess {γ : Type} {middle : β ↪ List Bool} {out : γ ↪ List Bool}
    {program : β → List Bool → ProbComp γ} {prepare : α → β}
    (h : IsPPTWithAux middle out program)
    (hprepare : ComputableInPolyTime prepare input middle) :
    IsPPTWithAux input out (fun a z => program (prepare a) z) := by
  obtain ⟨c, d, htake⟩ := h.exists_eval_take
  have hbound : ComputableInPolyTime
      (fun a : α => c * ((middle (prepare a)).length + 1) ^ d) input encUnary := by
    fun_prop
  obtain ⟨C, D, hle⟩ := hbound.tidy.polyBounded.exists_le
  have hppt : IsPPTOn (encPair input encBits) out (fun (a, z) => program (prepare a) z) :=
    h.isPPTOn.preprocess (prepare := fun (a, z) => (prepare a, z)) (by fun_prop)
  exact (hppt.isPPTWithAux_take C D).congr fun a z => htake (prepare a) z (hle a)

/-- Polynomial-time deterministic preprocessing of the primary input preserves
`IsOraclePPTWithAux`. -/
theorem IsOraclePPTWithAux.preprocess {γ : Type} {middle : β ↪ List Bool} {out : γ ↪ List Bool}
    {program : β → List Bool → WordOracleComp Operation γ} {prepare : α → β}
    (h : IsOraclePPTWithAux middle out program)
    (hprepare : ComputableInPolyTime prepare input middle) :
    IsOraclePPTWithAux input out (fun a z => program (prepare a) z) := by
  obtain ⟨c, d, htake⟩ := h.exists_run_interpret_take
  have hbound : ComputableInPolyTime
      (fun a : α => c * ((middle (prepare a)).length + 1) ^ d) input encUnary := by
    fun_prop
  obtain ⟨C, D, hle⟩ := hbound.tidy.polyBounded.exists_le
  have hppt : IsOraclePPTOn (encPair input encBits) out (fun (a, z) => program (prepare a) z) :=
    h.isOraclePPTOn.preprocess' (prepare := fun (a, z) => (prepare a, z)) (by fun_prop)
  exact (hppt.isOraclePPTWithAux_take C D).congr fun a z State oracle s =>
    htake (prepare a) z (hle a) State oracle s

end Cslib.Probability

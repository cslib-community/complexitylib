/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
import Complexity.Probability.PMF.Bind

/-!
# Fair-bit and bounded-prefix oracle query machines

`coinMachine` emits a single fair bit in one step. `queryTakePTM op` realizes the primitive
bounded-prefix oracle call on an encoded pair `encPair encBits encUnary (q, limit)`: it unframes `q`
into channel `op`'s query buffer, submits the query once, copies at most `limit` reply bits while
scanning the unary limit, and rewinds the input head.

## Main definitions

* `Turing.MultiTapePTM.coinMachine`: one-step fair-bit emitter.
* `Turing.MultiTapePTM.queryTakePTM`: tidy machine for `List.take limit <$> query (op, q)`.

## Main results

* `Turing.MultiTapePTM.computesTidily_coinMachine`: tidy specification of `coinMachine`.
* `Turing.MultiTapePTM.computesTidily_queryTakePTM`: tidy specification of `queryTakePTM`.

## References

Adapts the probabilistic oracle machines of the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the tidy-machine conventions of
crei:crei/tidy-universal @7f7c0696.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeMachine.Sequential MultiTapeTM

variable {Operation OracleState : Type} [DecidableEq Operation]

/-! ### Fair-bit machine -/

/-- One-state machine that emits a single fair bit and halts without moving any head. -/
def coinMachine : MultiTapePTM 0 Bool Unit Operation where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    (fun _ => none) (fun _ => 0)

/-- `coinMachine` tidily computes `encBool <$> sample (uniform Bool)` in `1` step. -/
theorem computesTidily_coinMachine (x : List Bool) :
    (coinMachine (Operation := Operation)).ComputesTidily x 1
      (encBool <$> ProbOracleComp.sample (ProbComp.uniform Bool)) := by
  intro out₀ OracleState oracle s cfg htapes hbuf
  have hs : cfg.tapes.state = some () := by rw [htapes]; rfl
  dsimp only [runOracleConfigFrom, runConfigFrom]
  simp only [MultiTapeMachine.runConfigFrom, hs, coinMachine, bind_map_left,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_map,
    StateT.run_bind, StateT.run_pure, StateT.run_map, run_interpret_sample_uniform_bool,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.monad_map_eq_map, PMF.bind_map, PMF.map_bind, PMF.pure_map, PMF.map_comp,
    Function.comp_def]
  constructor
  · change (PMF.uniformOfFintype Bool).map _ = (PMF.uniformOfFintype Bool).map _
    refine congrArg (fun f => (PMF.uniformOfFintype Bool).map f) (funext fun bit => ?_)
    refine Prod.ext ?_ rfl
    rw [Config.step, htapes]
    exact Cfg.ext_zero_tapes rfl rfl (by simp [Turing.Action.apply, wordsCfg])
  · rintro ⟨finalCfg, finalState⟩ hfinal op
    obtain ⟨bit, _, heq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    rw [PMF.mem_support_pure_iff] at heq
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    simp [Config.step, hbuf op]

/-! ### Bounded-prefix query machine -/

/-- Control states of `queryTakeCore`: read frame marker, read framed query bit, submit query,
and copy reply bits while scanning the unary limit. -/
inductive QueryTakeState where
  | marker
  | bit
  | submit
  | copyReply
  deriving DecidableEq

instance : Finite QueryTakeState :=
  Finite.of_injective
    (fun
      | .marker => (0 : Fin 4)
      | .bit => 1
      | .submit => 2
      | .copyReply => 3)
    (fun a b h => by cases a <;> cases b <;> simp_all)

/-- Unframe the query word from the input into channel `op`, submit the query, and copy at most
`limit` reply bits while scanning the unary suffix. -/
def queryTakeCore (op : Operation) : MultiTapePTM 0 Bool QueryTakeState Operation where
  initial := .marker
  tr state symbol _ answer _ := match state with
    | .marker => match symbol with
      | some true => .step
        { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .bit }
        (fun _ => none) (fun _ => 0)
      | some false => .step
        { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .submit }
        (fun _ => none) (fun _ => 0)
      | none => .step
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
        (fun _ => none) (fun _ => 0)
    | .bit => match symbol with
      | some b => .step
        { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .marker }
        (Function.update (fun _ => none) op (some b)) (fun _ => 0)
      | none => .step
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
        (fun _ => none) (fun _ => 0)
    | .submit => .query op .copyReply
    | .copyReply => match symbol with
      | some _ => .step
        { inputTape := 1, workTapes := Fin.elim0, output := answer op, state := some .copyReply }
        (fun _ => none) (Function.update (fun _ => 0) op 1)
      | none => .step
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
        (fun _ => none) (fun _ => 0)

/-- Run `queryTakeCore op` and then rewind the input head to position `1`. -/
noncomputable def queryTakePTM (op : Operation) :
    MultiTapePTM 0 Bool (QueryTakeState ⊕ RewindState) Operation :=
  (queryTakeCore op).seq (ofDeterministic (rewindInput Bool))

namespace QueryTakeCore

variable (op : Operation)

/-- Configuration of `queryTakeCore` at 0-based input index `idx ≤ x.length`. -/
def config (x : List Bool) (state : Option QueryTakeState) (idx : ℕ) (hidx : idx ≤ x.length)
    (out : List Bool) (ch : Operation → Channel Bool) :
    Config 0 Bool QueryTakeState Operation x where
  tapes :=
    { state := state
      inputPos := ⟨idx + 1, by lia⟩
      workTapes := Fin.elim0
      workTapePos := Fin.elim0
      output := out }
  channels := ch

omit [DecidableEq Operation] in
private theorem head_toList_append_tail_take (l : List Bool) (r : ℕ) :
    l.head?.toList ++ l.tail.take r = l.take (r + 1) := by
  cases l <;> simp

omit [DecidableEq Operation] in
private theorem getElem?_toList_append_drop_take (answer : List Bool) (pos r : ℕ) :
    (answer[pos]?).toList ++ (answer.drop (pos + 1)).take r =
      (answer.drop pos).take (r + 1) := by
  have hhead : answer[pos]? = (answer.drop pos).head? := by simp
  have htail : answer.drop (pos + 1) = (answer.drop pos).tail := by simp
  rw [hhead, htail, head_toList_append_tail_take]

/-- Scanning `List.replicate remLimit true` in state `.copyReply` appends `(answer.drop pos).take
remLimit` to `out` and halts at the right boundary in `remLimit + 1` steps. -/
theorem run_copyReply (x : List Bool)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (remLimit : ℕ) :
    ∀ (pre : List Bool) (h : x = pre ++ List.replicate remLimit true)
      (pos : ℕ) (answer out : List Bool) (ch : Operation → Channel Bool)
      (_hch : ch op = ⟨[], answer, (pos : ℤ)⟩) (s : OracleState),
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((queryTakeCore op).runOracleConfigFrom (remLimit + 1)
          (config x (some .copyReply) pre.length (by subst h; simp) out ch))).run s =
        PMF.pure
          (config x none x.length le_rfl (out ++ (answer.drop pos).take remLimit)
            (Function.update ch op ⟨[], answer, (pos + remLimit : ℤ)⟩), s) := by
  induction remLimit with
  | zero =>
    intro pre h pos answer out ch hch s
    have hlen : pre.length = x.length := by subst h; simp
    have hsym := inputSymbol_eq_none_of_boundary
      (cfg := (config x (some .copyReply) pre.length (by lia) out ch).tapes)
      (Or.inr (by simp [config, hlen]))
    rw [run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle 0
      (config x (some .copyReply) pre.length (by lia) out ch) s rfl
      (fun _ => by rw [hsym]; rfl)]
    dsimp only [runOracleConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure]
    congr 1
    refine Prod.ext (Config.ext ?_ ?_) rfl
    · exact Cfg.ext_zero_tapes rfl
        (by simp [Config.step, config, Turing.Action.apply, hlen])
        (by simp [Config.step, config, Turing.Action.apply])
    · funext other
      by_cases heq : other = op
      · subst other
        simp [Config.step, config, hch]
      · simp [Config.step, config, heq]
  | succ remLimit ih =>
    intro pre h pos answer out ch hch s
    have hlt : pre.length < x.length := by subst h; simp
    have hget : x[pre.length]'hlt = true := by
      cases h
      simp
    have hsym : (config x (some .copyReply) pre.length hlt.le out ch).tapes.inputSymbol =
        some true := by
      rw [inputSymbolInner pre.length (by simp [config]; lia) hlt]
      exact congrArg some hget
    have hans : (config x (some .copyReply) pre.length hlt.le out ch).answerSymbols op =
        answer[pos]? := by
      simp [Config.answerSymbols, config, hch, Channel.answerSymbol]
    let ch' := Function.update ch op ⟨[], answer, ((pos + 1 : ℕ) : ℤ)⟩
    have hstep :
        (config x (some .copyReply) pre.length hlt.le out ch).step
          { inputTape := 1, workTapes := Fin.elim0, output := answer[pos]?,
            state := some .copyReply }
          (fun _ => none) (Function.update (fun _ => 0) op 1) =
        config x (some .copyReply) (pre ++ [true]).length
          (by subst h; simp) (out ++ (answer[pos]?).toList) ch' := by
      refine Config.ext ?_ ?_
      · refine Cfg.ext_zero_tapes rfl ?_ (by simp [Config.step, config, Turing.Action.apply])
        apply Fin.ext
        change (moveInputPos _ .pos).val = (pre ++ [true]).length + 1
        rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
        simp [config]
      · funext other
        by_cases heq : other = op
        · subst other
          simp [Config.step, config, ch', hch, Nat.cast_add]
        · simp [Config.step, config, ch', heq]
    have hsplit : pre ++ List.replicate (remLimit + 1) true =
        (pre ++ [true]) ++ List.replicate remLimit true := by
      rw [List.replicate_succ, ← List.singleton_append, List.append_assoc]
    rw [run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle (remLimit + 1)
      (config x (some .copyReply) pre.length hlt.le out ch) s rfl
      (fun _ => by rw [hsym]; rfl),
      hans, hstep,
      ih (pre ++ [true]) (h.trans hsplit) (pos + 1) answer
        (out ++ (answer[pos]?).toList) ch' (by simp [ch']) s]
    congr 1
    refine Prod.ext (Config.ext ?_ ?_) rfl
    · refine Cfg.ext_zero_tapes rfl rfl ?_
      simp [config, List.append_assoc, getElem?_toList_append_drop_take]
    · funext other
      by_cases heq : other = op
      · subst other
        simp only [config, List.append_assoc, Nat.cast_add, Nat.cast_one, Function.update_idem,
          Function.update_self, Channel.mk.injEq, true_and, ch']
        lia
      · simp [config, ch', heq]

/-- Scanning `frame rem` in state `.marker` appends `rem` to channel `op`'s query buffer and
submits the accumulated query in `2 * rem.length + 2` steps, entering `.copyReply`. -/
theorem run_frame (x : List Bool)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (rem : List Bool) :
    ∀ (pre suf : List Bool) (h : x = pre ++ frame rem ++ suf)
      (out : List Bool) (ch : Operation → Channel Bool) (s : OracleState),
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((queryTakeCore op).runOracleConfigFrom (2 * rem.length + 2)
          (config x (some .marker) pre.length (by subst h; simp) out ch))).run s =
        (oracle (op, (ch op).queryBuffer ++ rem) s).map
          (fun (answer, s') =>
            (config x (some .copyReply) (pre.length + (frame rem).length)
              (by subst h; simp) out (Function.update ch op ⟨[], answer, 0⟩), s')) := by
  induction rem with
  | nil =>
    intro pre suf h out ch s
    have hlt : pre.length < x.length := by subst h; simp
    have hget : x[pre.length]'hlt = false := by
      cases h
      simp
    have hsym : (config x (some .marker) pre.length hlt.le out ch).tapes.inputSymbol =
        some false := by
      rw [inputSymbolInner pre.length (by simp [config]; lia) hlt]
      exact congrArg some hget
    have hstep₁ :
        (config x (some .marker) pre.length hlt.le out ch).step
          { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .submit }
          (fun _ => none) (fun _ => 0) =
        config x (some .submit) (pre.length + 1) (by subst h; simp) out ch := by
      refine Config.ext ?_ (funext fun _ => by simp [Config.step, config])
      refine Cfg.ext_zero_tapes rfl ?_ (by simp [Config.step, config, Turing.Action.apply])
      apply Fin.ext
      change (moveInputPos _ .pos).val = pre.length + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
      rfl
    change (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((queryTakeCore op).runOracleConfigFrom (0 + 1 + 1)
          (config x (some .marker) pre.length hlt.le out ch))).run s = _
    rw [run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle (0 + 1)
      (config x (some .marker) pre.length hlt.le out ch) s rfl
      (fun _ => by rw [hsym]; rfl),
      hstep₁,
      run_interpret_runOracleConfigFrom_succ_query (queryTakeCore op) oracle 0
        (config x (some .submit) (pre.length + 1) (by subst h; simp) out ch) s rfl
        (fun _ => rfl)]
    dsimp only [runOracleConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      List.append_nil]
    rfl
  | cons b rem ih =>
    intro pre suf h out ch s
    have hlt₁ : pre.length < x.length := by subst h; simp
    have hget₁ : x[pre.length]'hlt₁ = true := by
      cases h
      simp
    have hsym₁ : (config x (some .marker) pre.length hlt₁.le out ch).tapes.inputSymbol =
        some true := by
      rw [inputSymbolInner pre.length (by simp [config]; lia) hlt₁]
      exact congrArg some hget₁
    have hlt₂ : pre.length + 1 < x.length := by subst h; simp
    have hget₂ : x[pre.length + 1]'hlt₂ = b := by
      cases h
      simp [List.getElem_append_right]
    have hsym₂ : (config x (some .bit) (pre.length + 1) hlt₂.le out ch).tapes.inputSymbol =
        some b := by
      rw [inputSymbolInner (pre.length + 1) (by simp [config]; lia) hlt₂]
      exact congrArg some hget₂
    let ch' := Function.update ch op
      { ch op with queryBuffer := (ch op).queryBuffer ++ [b] }
    have hstep₁ :
        (config x (some .marker) pre.length hlt₁.le out ch).step
          { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .bit }
          (fun _ => none) (fun _ => 0) =
        config x (some .bit) (pre.length + 1) hlt₂.le out ch := by
      refine Config.ext ?_ (funext fun _ => by simp [Config.step, config])
      refine Cfg.ext_zero_tapes rfl ?_ (by simp [Config.step, config, Turing.Action.apply])
      apply Fin.ext
      change (moveInputPos _ .pos).val = pre.length + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
      rfl
    have hstep₂ :
        (config x (some .bit) (pre.length + 1) hlt₂.le out ch).step
          { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .marker }
          (Function.update (fun _ => none) op (some b)) (fun _ => 0) =
        config x (some .marker) (pre ++ [true, b]).length
          (by subst h; simp) out ch' := by
      refine Config.ext ?_ ?_
      · refine Cfg.ext_zero_tapes rfl ?_ (by simp [Config.step, config, Turing.Action.apply])
        apply Fin.ext
        change (moveInputPos _ .pos).val = (pre ++ [true, b]).length + 1
        rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
        simp [config]
      · funext other
        by_cases heq : other = op
        · subst other
          simp [Config.step, config, ch']
        · simp [Config.step, config, ch', heq]
    have h2 : 2 * (b :: rem).length + 2 = (2 * rem.length + 2) + 1 + 1 := by simp; lia
    have hsplit : pre ++ frame (b :: rem) ++ suf = (pre ++ [true, b]) ++ frame rem ++ suf := by
      simp [frame_cons, List.append_assoc]
    rw [h2,
      run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle
        ((2 * rem.length + 2) + 1)
        (config x (some .marker) pre.length hlt₁.le out ch) s rfl
        (fun _ => by rw [hsym₁]; rfl),
      hstep₁,
      run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle
        (2 * rem.length + 2)
        (config x (some .bit) (pre.length + 1) hlt₂.le out ch) s rfl
        (fun _ => by rw [hsym₂]; rfl),
      hstep₂,
      ih (pre ++ [true, b]) suf (h.trans hsplit) out ch' s]
    congr 1
    · funext p
      refine Prod.ext (Config.ext ?_ ?_) rfl
      · refine Cfg.ext_zero_tapes rfl ?_ rfl
        apply Fin.ext
        simp only [config, List.length_append, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, length_frame, frame_cons, Nat.add_right_cancel_iff]
        lia
      · funext other
        by_cases heq : other = op
        · subst other
          simp [config, ch']
        · simp [config, ch', heq]
    · simp [ch', List.append_assoc]

end QueryTakeCore

/-- `queryTakePTM op` tidily computes `List.take limit <$> query (op, q)` on
`encPair encBits encUnary (q, limit)` in `4 * q.length + 2 * limit + 6` steps. -/
theorem computesTidily_queryTakePTM (op : Operation) (q : List Bool) (limit : ℕ) :
    (queryTakePTM op).ComputesTidily (encPair encBits encUnary (q, limit))
      (4 * q.length + 2 * limit + 6)
      (List.take limit <$> ProbOracleComp.query (op, q)) := by
  let x := encPair encBits encUnary (q, limit)
  have hx : x = frame q ++ List.replicate limit true := by
    simp [x, encPair_apply, encBits_apply, encUnary_apply]
  have hxlen : x.length = 2 * q.length + 1 + limit := by simp [hx]
  let t₁ := 2 * q.length + 2
  let t₂ := limit + 1
  let tCore := t₁ + t₂
  let tRew := 2 * q.length + limit + 3
  intro out₀ OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config 0 Bool QueryTakeState Operation x :=
    QueryTakeCore.config x (some .marker) 0 (Nat.zero_le _) out₀ cfg.channels
  have hcfg : cfg = Sequential.left (ofDeterministic (rewindInput Bool)) cfg₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    exact Cfg.ext_zero_tapes rfl rfl rfl
  -- Combine `run_frame` and `run_copyReply` for `queryTakeCore op`
  have hcore :
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((queryTakeCore op).runOracleConfigFrom tCore cfg₀)).run s =
      (oracle (op, q) s).map
        (fun (answer, s') =>
          (QueryTakeCore.config x none x.length le_rfl (out₀ ++ answer.take limit)
            (Function.update cfg.channels op ⟨[], answer, (limit : ℤ)⟩), s')) := by
    dsimp only [tCore, runOracleConfigFrom, runConfigFrom]
    rw [MultiTapeMachine.runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind]
    have hframe := QueryTakeCore.run_frame op x oracle q [] (List.replicate limit true)
      (by simp [hx]) out₀ cfg.channels s
    dsimp only [runOracleConfigFrom, runConfigFrom] at hframe
    simp only [List.length_nil, Nat.zero_add, hbuf op, List.nil_append] at hframe
    rw [hframe, PMF.bind_map]
    refine (PMF.bind_congr_on_support _ _ _ ?_).trans rfl
    rintro ⟨answer, s₁⟩ _
    dsimp only [Function.comp_def, t₂]
    have hcopy := QueryTakeCore.run_copyReply op x oracle limit (frame q) hx 0 answer out₀
      (Function.update cfg.channels op ⟨[], answer, 0⟩) (by simp) s₁
    dsimp only [runOracleConfigFrom, runConfigFrom] at hcopy
    simpa only [List.drop_zero, Nat.cast_zero, zero_add, Function.update_idem] using hcopy
  have hhalt₁ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((queryTakeCore op).runOracleConfigFrom tCore cfg₀)).run s).support,
      result.1.tapes.state = none := by
    intro result hresult
    rw [hcore] at hresult
    obtain ⟨⟨answer, s₁⟩, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    rfl
  have hrew (answer : List Bool) :
      (rewindInput Bool).runFrom
        (Sequential.start (ofDeterministic (rewindInput Bool) :
          MultiTapePTM 0 Bool RewindState Operation)
          (QueryTakeCore.config x none x.length le_rfl (out₀ ++ answer.take limit)
            (Function.update cfg.channels op ⟨[], answer, (limit : ℤ)⟩))).tapes tRew =
        wordsCfg x none (fun _ => []) (out₀ ++ answer.take limit) := by
    have htime : tRew = (⟨x.length + 1, by lia⟩ : Fin (x.length + 2)).val - 1 + 2 := by
      dsimp only [tRew]
      lia
    rw [htime]
    exact (runFrom_rewindInput ⟨x.length + 1, by lia⟩ Fin.elim0 Fin.elim0
      (out₀ ++ answer.take limit)).trans (Cfg.ext_zero_tapes rfl rfl rfl)
  have hhalt₂ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((queryTakeCore op).runOracleConfigFrom tCore cfg₀)).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((ofDeterministic (rewindInput Bool)).runOracleConfigFrom tRew
          (Sequential.start (ofDeterministic (rewindInput Bool)) result.1))).run result.2).support,
        final.1.tapes.state = none := by
    rintro result hresult ⟨finalCfg, finalState⟩ hfinal
    rw [hcore] at hresult
    obtain ⟨⟨answer, s₁⟩, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hrew answer,
      PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    rfl
  have htotal : 4 * q.length + 2 * limit + 6 = tCore + tRew := by
    dsimp only [tCore, t₁, t₂, tRew]
    lia
  dsimp only [queryTakePTM]
  rw [htotal, hcfg,
    run_interpret_runOracleConfigFrom_seq (queryTakeCore op) (ofDeterministic (rewindInput Bool))
      oracle cfg₀ tCore tRew s hhalt₁ hhalt₂,
    hcore]
  constructor
  · simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
      run_interpret_runOracleConfigFrom_ofDeterministic, hrew, PMF.pure_map,
      OracleComp.interpret_map, ProbOracleComp.interpret_query, StateT.run_map,
      PMF.monad_map_eq_map, Sequential.right, Cfg.mapState, wordsCfg_state, Option.map_none,
      id_eq]
    rfl
  · rintro ⟨finalCfg, finalState⟩ hfinal other
    rw [PMF.bind_map] at hfinal
    obtain ⟨⟨answer, s₁⟩, _, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    dsimp only [Function.comp_def] at hfinal
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hrew answer, PMF.pure_map,
      PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    by_cases heq : other = op
    · subst other
      simp [Sequential.right, Sequential.start, QueryTakeCore.config]
    · simp [Sequential.right, Sequential.start, QueryTakeCore.config, heq, hbuf other]

end Turing.MultiTapePTM

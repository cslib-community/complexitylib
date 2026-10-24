/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.Nondeterministic

/-! Nondeterministic acceptance and time bounds on concrete stuck and fair-coin machines,
guess-and-verify deciders for verifier `NP`, and verifiers checking encoded accepting
computations, including empty instances and padded certificates. Only the nondeterministic
verifier API is imported. -/

namespace ComplexityTests.NondeterministicVerifiers

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### A stuck machine: time bounds do not force halting -/

/-- A machine with no transitions; its initial configuration is stuck. -/
private def stuck : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ _ := False

/-- Every computation path of `stuck` consists of its initial configuration. -/
private theorem time_stuck {input : List Bool} (p : stuck.ComputationPath input) : p.time = 0 := by
  by_contra h
  have hpos : 0 < p.length := Nat.pos_of_ne_zero h
  have hstep : stuck.Step (p.toRunPath (Fin.castSucc ⟨0, hpos⟩))
      (p.toRunPath (Fin.succ ⟨0, hpos⟩)) := p.step ⟨0, hpos⟩
  have hhead : p.toRunPath (Fin.castSucc ⟨0, hpos⟩) = stuck.initCfg input := p.head_eq
  rw [hhead] at hstep
  simp [MultiTapeNTM.Step, stuck] at hstep

/-- The time bound holds vacuously although no branch halts. -/
private theorem runsInTime_stuck (input : List Bool) : stuck.RunsInTime input 1 :=
  fun p hp => absurd (time_stuck p) (by omega)

/-- A stuck branch does not accept. -/
private theorem not_accepts_stuck (input : List Bool) : ¬stuck.Accepts input := by
  rw [MultiTapeNTM.accepts_iff_exists_time_eq (runsInTime_stuck input)]
  rintro ⟨p, hp, -⟩
  simp [time_stuck p] at hp

example : stuck.DecidesInTime encBits ∅ fun _ => 1 :=
  fun a => ⟨runsInTime_stuck a, by simpa using not_accepts_stuck a⟩

example : ¬(stuck.initCfg [] : Cfg 0 Bool Unit []).Halted := by simp [stuck]

/-! ### A fair coin as a nondeterministic machine -/

/-- Emit one fair bit and halt. -/
private def coin : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

/-- The configuration after one coin: halted, with the coin as output. -/
private def coinFinal (bit : Bool) (input : List Bool) : Cfg 0 Bool Unit input :=
  ⟨none, 1, fun _ _ => none, fun _ => 0, [bit]⟩

/-- One step with a given coin halts with that bit as output. -/
private theorem stepCoins_coin (bit : Bool) (input : List Bool) :
    coin.stepCoins [bit] (coin.toNTM.initCfg input) = coinFinal bit input := by
  simp only [MultiTapePTM.stepCoins, List.foldl_cons, List.foldl_nil]
  rw [MultiTapeTM.step_of_state rfl]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeMachine.toTM, MultiTapeMachine.Action.emptyOracleEquiv, MultiTapePTM.withCoin,
      coin, Action.apply, MultiTapePTM.toNTM, coinFinal]

/-- For each bit, a computation path of one step halts with that bit as output. -/
private theorem exists_path_coin (bit : Bool) (input : List Bool) :
    ∃ p : coin.toNTM.ComputationPath input, p.time = 1 ∧ p.last.Halted ∧ p.last.output = [bit] := by
  obtain ⟨p, hhead, hlen, hlast⟩ :=
    (coin.exists_runPath_toNTM_iff (c := coin.toNTM.initCfg input) (n := 1)).mpr
      ⟨[bit], rfl, rfl⟩
  have hfinal : (⟨p, hhead⟩ : coin.toNTM.ComputationPath input).last = coinFinal bit input :=
    hlast.trans (stepCoins_coin bit input)
  exact ⟨⟨p, hhead⟩, hlen, by rw [hfinal]; rfl, by rw [hfinal]; rfl⟩

/-- Both branches halt after one step. -/
private theorem runsInTime_coin (input : List Bool) : coin.toNTM.RunsInTime input 1 := by
  intro p hp
  have hlt : 1 < p.length + 1 := Nat.lt_succ_of_le hp
  have hstep : coin.toNTM.Step (p.toRunPath (Fin.castSucc ⟨0, hp⟩))
      (p.toRunPath (Fin.succ ⟨0, hp⟩)) := p.step ⟨0, hp⟩
  have hhead : p.toRunPath (Fin.castSucc ⟨0, hp⟩) = coin.toNTM.initCfg input := p.head_eq
  rw [hhead] at hstep
  obtain ⟨bit, hbit⟩ := (coin.step_toNTM_iff).mp hstep
  have hone : p.toRunPath ⟨1, hlt⟩ = coinFinal bit input :=
    hbit.symm.trans (stepCoins_coin bit input)
  have hhalt : (p.toRunPath ⟨1, hlt⟩).Halted := by rw [hone]; rfl
  exact (MultiTapeNTM.RunPath.last_eq_of_halted p.toRunPath _ hhalt) ▸ hhalt

example (input : List Bool) : coin.toNTM.Accepts input :=
  let ⟨p, _, hhalt, hout⟩ := exists_path_coin true input
  ⟨p, hhalt, hout⟩

/-- A rejecting branch exists beside the accepting one. -/
example (input : List Bool) :
    ∃ p : coin.toNTM.ComputationPath input, p.last.Halted ∧ p.last.output = [false] :=
  let ⟨p, _, hhalt, hout⟩ := exists_path_coin false input
  ⟨p, hhalt, hout⟩

/-- Halted self-loops: the accepting path also has exactly three steps. -/
example : ∃ p : coin.toNTM.ComputationPath [], p.time = 3 ∧ p.last.output = [true] :=
  (MultiTapeNTM.accepts_iff_exists_time_eq ((runsInTime_coin []).mono (by omega))).mp
    (let ⟨p, _, hhalt, hout⟩ := exists_path_coin true []; ⟨p, hhalt, hout⟩)

/-- The fair coin is never stuck, so its paths within the bound extend to halted ones. -/
example (input : List Bool) (p : coin.toNTM.ComputationPath input) (hp : p.time ≤ 1) :
    ∃ (q : coin.toNTM.ComputationPath input) (_ : q.time = 1), q.last.Halted ∧
      ∀ i (hi : i < p.length + 1), q.toRunPath ⟨i, by
        unfold MultiTapeNTM.ComputationPath.time MultiTapeNTM.RunPath.time at *; omega⟩ =
        p.toRunPath ⟨i, hi⟩ :=
  MultiTapeNTM.ComputationPath.exists_halted_extension (coin.exists_step_toNTM)
    (runsInTime_coin input) p hp

/-! ### A looping machine violates every time bound -/

/-- Stay in its only state forever. -/
private def loop : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }

private theorem state_runFrom_loop (input : List Bool) (t : ℕ) :
    (loop.runFrom (loop.initCfg input) t).state = some () := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
      MultiTapeTM.step_of_state ih]
    simp [loop, Action.apply]

example (input : List Bool) (t : ℕ) : ¬loop.toMultiTapeNTM.RunsInTime input t := by
  intro h
  have hhalt := h (MultiTapeNTM.ComputationPath.ofDeterministic loop input t) le_rfl
  rw [MultiTapeTM.computationPath_last_eq_runFrom] at hhalt
  have htime : (MultiTapeNTM.ComputationPath.ofDeterministic loop input t).time = t := rfl
  rw [htime, Cfg.Halted, state_runFrom_loop] at hhalt
  exact Option.some_ne_none _ hhalt

/-! ### A stuck branch beside an accepting one -/

/-- Halt with output `[true]`. -/
private def acceptAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

/-- Move to the state `true`, which has no transitions. -/
private def stuckAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := some true }

/-- From its initial state `false`, either accept or move to the stuck state `true`. -/
private def fork : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ action := q = false ∧ (action = acceptAction ∨ action = stuckAction)

/-- The stuck branch does not prevent acceptance. -/
example (input : List Bool) : fork.Accepts input := by
  have hstep : fork.Step (fork.initCfg input) (acceptAction.apply (fork.initCfg input)) :=
    ⟨acceptAction, ⟨rfl, .inl rfl⟩, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (fork.initCfg input) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- After one step the stuck branch is still running, so one step is not a time bound. -/
example (input : List Bool) : ¬fork.RunsInTime input 1 := by
  have hstep : fork.Step (fork.initCfg input) (stuckAction.apply (fork.initCfg input)) :=
    ⟨stuckAction, ⟨rfl, .inr rfl⟩, rfl⟩
  intro h
  have := h ⟨(RelSeries.singleton _ _).cons (fork.initCfg input) hstep, rfl⟩
    (by simp [MultiTapeNTM.ComputationPath.time, MultiTapeNTM.RunPath.time])
  simp [Cfg.Halted, stuckAction] at this

/-- Two steps bound every branch: the stuck branch has no second step. -/
private theorem runsInTime_fork (input : List Bool) : fork.RunsInTime input 2 := by
  intro p hp
  have hlen : 1 < p.length := hp
  have h₀ : fork.Step (p.toRunPath (Fin.castSucc ⟨0, by omega⟩))
      (p.toRunPath (Fin.succ ⟨0, by omega⟩)) := p.step ⟨0, by omega⟩
  have h₁ : fork.Step (p.toRunPath (Fin.castSucc ⟨1, hlen⟩))
      (p.toRunPath (Fin.succ ⟨1, hlen⟩)) := p.step ⟨1, hlen⟩
  have hhead : p.toRunPath (Fin.castSucc ⟨0, by omega⟩) = fork.initCfg input := p.head_eq
  have hone : p.toRunPath (Fin.succ ⟨0, by omega⟩) = p.toRunPath (Fin.castSucc ⟨1, hlen⟩) :=
    congrArg p.toRunPath (Fin.ext rfl)
  rw [hhead] at h₀
  rw [← hone] at h₁
  obtain ⟨action, ⟨-, haction⟩, hnext⟩ := h₀
  rcases haction with rfl | rfl
  · have hhalt : (p.toRunPath (Fin.succ ⟨0, by omega⟩)).Halted := by rw [hnext]; rfl
    exact (MultiTapeNTM.RunPath.last_eq_of_halted p.toRunPath _ hhalt) ▸ hhalt
  · rw [hnext] at h₁
    simp [MultiTapeNTM.Step, fork, stuckAction] at h₁

/-! ### Acceptance requires exactly the output `[true]` -/

/-- Emit `true` twice, then halt. -/
private def twice : MultiTapeTM 0 Bool (Fin 2) :=
  MultiTapeTM.ofTr 0 fun q _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some true,
      state := if q = 0 then some 1 else none }

private theorem runFrom_twice (input : List Bool) :
    twice.runFrom (twice.initCfg input) 2 =
      ⟨none, 1, fun _ _ => none, fun _ => 0, [true, true]⟩ := by
  change twice.step (twice.step (twice.initCfg input)) = _
  rw [MultiTapeTM.step_of_state (cfg := twice.initCfg input) (q := 0) rfl,
    MultiTapeTM.step_of_state (q := 1) (by simp [twice, Action.apply])]
  apply Cfg.ext_zero_tapes <;> simp [twice, Action.apply]

/-- Every branch halts after two steps, with output `[true, true]`. -/
private theorem runsInTime_twice (input : List Bool) :
    twice.toMultiTapeNTM.RunsInTime input 2 :=
  MultiTapeTM.runsInTime_of_halted (by rw [runFrom_twice])

/-- Halting after emitting `[true, true]` does not accept. -/
example (input : List Bool) : ¬twice.toMultiTapeNTM.Accepts input := by
  rw [MultiTapeNTM.accepts_iff_exists_time_eq (runsInTime_twice input)]
  rintro ⟨p, hp, hout⟩
  have hlast := MultiTapeTM.computationPath_last_eq_runFrom p
  rw [show p.time = 2 from hp, runFrom_twice] at hlast
  simp [hlast] at hout

/-! ### Guess and verify -/

/-- The verifier reading the first certificate bit. -/
private theorem polyTime_headD :
    ComputableTidilyInPolyTime (fun x : List Bool × List Bool => x.2.headD false)
      (encPair encBits encBits) encBool :=
  (ComputableTidilyInPolyTime.headD (encA := encBool) false).comp
    (ComputableTidilyInPolyTime.snd encBits encBits)

/-- With one-bit certificates, the decider accepts the empty instance only through the branch
guessing `[true]`. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State),
    machine.toNTM.Accepts [] := by
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, -⟩ :=
    IsVerifier.exists_decidesInTime (enc := encBits) (p := 1) (A := Set.univ)
      (.of_tidy polyTime_headD)
      fun _ => ⟨fun _ => ⟨[true], by simp, rfl⟩, fun _ => trivial⟩
  exact ⟨k, State, hfinite, machine, ((hdecides []).2).mp trivial⟩

/-- With empty certificates, the same verifier rejects: the decider guesses exactly
`p (enc a).length` bits, so it cannot reach the accepting certificate `[true]`. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State),
    ¬machine.toNTM.Accepts [] := by
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, -⟩ :=
    IsVerifier.exists_decidesInTime (enc := encBits) (p := 0) (A := ∅) (.of_tidy polyTime_headD)
      fun _ => by simp
  exact ⟨k, State, hfinite, machine, fun h => ((hdecides []).2).mpr h⟩

/-- The guessing decider of the trivial verifier accepts the empty instance. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State),
    machine.toNTM.Accepts [] := by
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, -⟩ :=
    IsVerifier.exists_decidesInTime (enc := encBits) (p := 0) (A := Set.univ)
      (.of_tidy (ComputableTidilyInPolyTime.const true)) fun _ => by simp
  exact ⟨k, State, hfinite, machine, ((hdecides []).2).mp trivial⟩

/-- The guessing decider of the rejecting verifier rejects the empty instance, although every
branch halts within the explicit polynomial bound. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State)
    (t : ℕ), ¬machine.toNTM.Accepts [] ∧ machine.toNTM.RunsInTime [] t ∧
      ∀ input (cfg : Cfg k Bool State input), ∃ cfg', machine.toNTM.Step cfg cfg' := by
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, htotal⟩ :=
    IsVerifier.exists_decidesInTime (enc := encBits) (p := 0) (A := ∅)
      (.of_tidy (ComputableTidilyInPolyTime.const false)) fun _ => by simp
  exact ⟨k, State, hfinite, machine, _, fun h => ((hdecides []).2).mpr h, (hdecides []).1,
    htotal⟩

/-- A verifier reading only its instance, under a pair encoding. -/
example : MultiTapeNTM.DecidableInPolyTime {a : Bool × ℕ | a.1 = true}
    (encPair encBool encNat) := by
  refine decidableInPolyTime_of_mem_NP ⟨0, fun x => x.1.1, ?_, fun a => by simp⟩
  exact (ComputableInPolyTime.fst encBool encNat).comp
    (ComputableInPolyTime.fst (encPair encBool encNat) encBits)

/-! ### Checking encoded accepting computations -/

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- A fixed machine's checker is inferred under any encoding of instances. -/
example {k : ℕ} {State α : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)
    (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (ntm.checkChoices enc) (encPair enc encBits) encBool := by
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Checker inference composes with ordinary projections and a runtime guard. -/
example {k : ℕ} {State α : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)
    (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime
      (fun x : (α × List Bool) × Bool => if x.2 then ntm.checkChoices enc x.1 else false)
      (encPair (encPair enc encBits) encBool) encBool := by
  fun_prop

/-- The fair coin decides the universal problem within one step: some branch emits `[true]`. -/
private theorem decides_coin : coin.toNTM.DecidesInTime encBits Set.univ fun _ => 1 :=
  fun a => ⟨runsInTime_coin a, by
    simp only [Set.mem_univ, true_iff]
    obtain ⟨p, -, hhalt, hout⟩ := exists_path_coin true a
    exact ⟨p, hhalt, hout⟩⟩

/-- The universal problem has accepting certificates at the exact sufficient-length threshold. -/
example : ∃ w : List Bool, w.length = Nat.card (Action 0 Bool Unit) ∧
    coin.toNTM.checkChoices encBits ([], w) = true :=
  (decides_coin.mem_iff_exists_checkChoices (a := []) (by simp)).mp (Set.mem_univ _)

/-- Certificates can be padded beyond the threshold, including on the empty instance. -/
example (extra : ℕ) : ∃ w : List Bool, w.length = Nat.card (Action 0 Bool Unit) + extra ∧
    coin.toNTM.checkChoices encBits ([], w) = true :=
  (decides_coin.mem_iff_exists_checkChoices (a := []) (by simp)).mp (Set.mem_univ _)

example : (Set.univ : Set (List Bool)) ∈ NP encBits :=
  mem_NP_of_decidableInPolyTime ⟨_, .const 1, 0, Unit, inferInstance, coin.toNTM, decides_coin⟩

/-- The stuck machine yields the empty problem: its stuck branch rejects. -/
example : (∅ : Set (List Bool)) ∈ NP encBits :=
  mem_NP_of_decidableInPolyTime ⟨_, .const 1, 0, Unit, inferInstance, stuck,
    fun a => ⟨runsInTime_stuck a, by simpa using not_accepts_stuck a⟩⟩

/-- No certificate encodes an accepting computation of the stuck machine: choosing beyond its
(absent) permitted actions rejects. -/
example (w : List Bool) : stuck.checkChoices encBits ([], w) = false := by
  rw [MultiTapeNTM.checkChoices, decide_eq_false_iff_not]
  exact fun h => not_accepts_stuck [] (MultiTapeNTM.accepts_of_runClosedCoins_choiceTable h)

/-- The accepting computation of the fair coin, padded arbitrarily, is accepted. -/
example (padding : List Bool) : ∃ coins : List Bool,
    coins.length ≤ Nat.card (Action 0 Bool Unit) ∧
      coin.toNTM.checkChoices encBits ([], coins ++ padding) = true := by
  obtain ⟨p, hp, hhalt, hout⟩ := exists_path_coin true []
  obtain ⟨coins, hlen, hcoins⟩ := MultiTapeNTM.exists_runClosedCoins_choiceTable p hhalt hout
  refine ⟨coins, by simpa [hp] using hlen, ?_⟩
  simp [MultiTapeNTM.checkChoices, hcoins]

/-- The explicit certificate length: one step of the fair coin needs at most `Nat.card` coins. -/
example : IsVerifier encBits
    (Polynomial.C (Nat.card (Action 0 Bool Unit) * 1) * (Polynomial.X + 1) ^ 0)
    (coin.toNTM.checkChoices encBits) Set.univ :=
  (decides_coin.mono fun _ => by simp).isVerifier

/-- A stuck branch beside an accepting one: the fork's problem is still in `NP`. -/
private theorem decides_fork : fork.DecidesInTime encBits Set.univ fun _ => 2 := by
  intro input
  refine ⟨runsInTime_fork _, ?_⟩
  · simp only [Set.mem_univ, true_iff]
    have hstep : fork.Step (fork.initCfg (encBits input))
        (acceptAction.apply (fork.initCfg (encBits input))) :=
      ⟨acceptAction, ⟨rfl, .inl rfl⟩, rfl⟩
    refine ⟨⟨(RelSeries.singleton _ _).cons (fork.initCfg (encBits input)) hstep, rfl⟩, ?_, ?_⟩ <;>
      simp [acceptAction]

example : (Set.univ : Set (List Bool)) ∈ NP encBits :=
  mem_NP_of_decidableInPolyTime ⟨_, .const 2, 0, Bool, inferInstance, fork, decides_fork⟩

/-- Emit `true`, then run forever. -/
private def emitLoop : MultiTapeTM 0 Bool Bool :=
  MultiTapeTM.ofTr false fun q _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := if q then none else some true,
      state := some true }

private theorem isSome_state_runFrom_emitLoop (input : List Bool) (t : ℕ) :
    (emitLoop.runFrom (emitLoop.initCfg input) t).state.isSome := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp ih
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
      MultiTapeTM.step_of_state hq]
    simp [emitLoop, Action.apply]

/-- After one step, `emitLoop` has emitted `[true]` and is still running. -/
example : (emitLoop.runFrom (emitLoop.initCfg []) 1).output = [true] ∧
    (emitLoop.runFrom (emitLoop.initCfg []) 1).state = some true := by
  change (emitLoop.step (emitLoop.initCfg [])).output = _ ∧ (emitLoop.step _).state = _
  rw [MultiTapeTM.step_of_state (q := false) rfl]
  simp [emitLoop, Action.apply]

/-- A running prefix `[true]` is not acceptance: no certificate is accepted for `emitLoop`. -/
example (input w : List Bool) :
    emitLoop.toMultiTapeNTM.choiceTable.runClosedCoins w input ≠ [true] := by
  intro h
  obtain ⟨p, hhalt, -⟩ := MultiTapeNTM.accepts_of_runClosedCoins_choiceTable h
  have hlast := MultiTapeTM.computationPath_last_eq_runFrom p
  have hsome := isSome_state_runFrom_emitLoop input p.time
  rw [← hlast, show p.last.state = none from hhalt] at hsome
  exact absurd hsome (by simp)

/-- The encoded rejecting branch of the fair coin is rejected, although the coin accepts. -/
example : ∃ coins : List Bool, coin.toNTM.checkChoices encBits ([], coins) = false := by
  obtain ⟨p, -, hhalt, hout⟩ := exists_path_coin false []
  obtain ⟨coins, -, hcoins⟩ := MultiTapeNTM.ChoiceTable.exists_coins_runPath p.toRunPath
  have hsim : MultiTapeNTM.ChoiceTable.simCfg p.last = MultiTapeNTM.ChoiceTable.haltCfg p.last := by
    simp only [MultiTapeNTM.ChoiceTable.simCfg, show p.last.state = none from hhalt]
  refine ⟨coins, ?_⟩
  rw [MultiTapeNTM.checkChoices, decide_eq_false_iff_not]
  change ¬coin.toNTM.choiceTable.runClosedCoins coins [] = [true]
  rw [MultiTapePTM.runClosedCoins, MultiTapePTM.tapes_runClosedConfigFromCoins,
    ← MultiTapePTM.initCfg_toNTM, MultiTapeNTM.ChoiceTable.initCfg_choiceTable, ← p.head_eq,
    hcoins, hsim]
  simp [MultiTapeNTM.ChoiceTable.haltCfg, hout]

/-- Halting with `[true, true]` is rejected under every certificate. -/
example (w : List Bool) : twice.toMultiTapeNTM.checkChoices encBits ([], w) = false := by
  rw [MultiTapeNTM.checkChoices, decide_eq_false_iff_not]
  change ¬twice.toMultiTapeNTM.choiceTable.runClosedCoins w [] = [true]
  intro h
  have hacc := MultiTapeNTM.accepts_of_runClosedCoins_choiceTable h
  rw [MultiTapeNTM.accepts_iff_exists_time_eq (runsInTime_twice [])] at hacc
  obtain ⟨p, hp, hout⟩ := hacc
  have hlast := MultiTapeTM.computationPath_last_eq_runFrom p
  rw [show p.time = 2 from hp, runFrom_twice] at hlast
  simp [hlast] at hout

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeNTM.DecidesInTime.mem_iff_exists_checkChoices' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.DecidesInTime.mem_iff_exists_checkChoices

/--
info: 'Turing.MultiTapePTM.exists_runPath_toNTM_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.exists_runPath_toNTM_iff

/--
info: 'Turing.MultiTapePTM.mem_support_runClosedConfigFrom_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.mem_support_runClosedConfigFrom_iff

/--
info: 'Turing.MultiTapePTM.runsInTime_toNTM' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.runsInTime_toNTM

/--
info: 'Turing.MultiTapeNTM.accepts_iff_exists_time_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.accepts_iff_exists_time_eq

/--
info: 'Turing.MultiTapeNTM.ComputationPath.exists_halted_extension' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.ComputationPath.exists_halted_extension

/--
info: 'Cslib.Complexity.IsVerifier.exists_decidesInTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IsVerifier.exists_decidesInTime

/--
info: 'Cslib.Complexity.decidableInPolyTime_of_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.decidableInPolyTime_of_mem_NP

/--
info: 'Cslib.Complexity.mem_NP_iff_decidableInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_iff_decidableInPolyTime

/--
info: 'Cslib.Complexity.mem_NP_of_decidableInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_of_decidableInPolyTime

/--
info: 'Turing.MultiTapeNTM.DecidesInTime.isVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.DecidesInTime.isVerifier

/--
info: 'Turing.MultiTapeNTM.computableInPolyTime_checkChoices' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.computableInPolyTime_checkChoices

/--
info: 'Turing.MultiTapeNTM.accepts_of_runClosedCoins_choiceTable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.accepts_of_runClosedCoins_choiceTable

/--
info: 'Turing.MultiTapeNTM.exists_runClosedCoins_choiceTable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.exists_runClosedCoins_choiceTable

end ComplexityTests.NondeterministicVerifiers

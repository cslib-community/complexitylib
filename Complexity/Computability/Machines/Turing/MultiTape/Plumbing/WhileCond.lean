/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput

/-!
# Repeating a machine while a condition holds

`whileCond c tm` reads the symbols under its heads and halts unless the condition `c` holds of them;
otherwise it runs `tm` and repeats. Unlike `Turing.MultiTapeTM.repeatUntilBlank`, the rounds may
leave the input head anywhere (`Turing.MultiTapeTM.TransformsTapesAt`), so the loop can drive a
two-way input head.

## Main definitions

* `Turing.MultiTapeTM.whileCond`: the loop.

## Main results

* `Turing.MultiTapeTM.transformsTapesAt_whileCond`: a loop invariant preserved by every round
  gives a specification of `whileCond c tm`, with the times of the rounds adding up.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- From `check`, the machine halts unless `c` holds of the symbols under the input head and the
work-tape heads, and otherwise starts `tm`, moving no head. Each round of `tm` returns to
`check`. -/
public noncomputable def whileCond (c : Option Symbol → (Fin k → Option Symbol) → Bool)
    (tm : MultiTapeTM k Symbol State) : MultiTapeTM k Symbol (RepeatUntilBlankState State) :=
  ofTr .check fun q inp work =>
    match q with
    | .run q =>
      let a := tm.tr q inp work
      { a with state := some (a.state.elim .check .run) }
    | .check =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := if c inp work then some (.run tm.q₀) else none }

/-- The condition `c` on the configuration with the input head at `p` and the words `ws` on the
work tapes, read at the start of each word. -/
@[expose] public def condAt (c : Option Symbol → (Fin k → Option Symbol) → Bool)
    (input : List Symbol) (p : Fin (input.length + 2)) (ws : Fin k → List Symbol) : Bool :=
  c (inputSymbolAt input p) fun j => (ws j).head?

namespace WhileCond

variable {c : Option Symbol → (Fin k → Option Symbol) → Bool} {tm : MultiTapeTM k Symbol State}

/-- A configuration of `tm` as one of `whileCond c tm`: a live state `q` becomes `run q` and the
halted state becomes `check`. -/
def runCfg (cfg : Cfg k Symbol State input) : Cfg k Symbol (RepeatUntilBlankState State) input :=
  cfg.mapState (fun st => some (st.elim .check .run))

lemma step_runCfg (cfg : Cfg k Symbol State input) (h : ¬ cfg.Halted) :
    (whileCond c tm).step (runCfg cfg) = runCfg (tm.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (runCfg cfg).state = some (RepeatUntilBlankState.run q) := by
    simp [runCfg, Cfg.mapState, hq]
  rw [step_of_state hstate, step_of_state hq]
  simp only [whileCond, tr_ofTr]
  rfl

lemma runFrom_runCfg {cfg : Cfg k Symbol State input} {u n : ℕ} (hhalt : tm.HaltsAt cfg u)
    (hn : n ≤ u) :
    (whileCond c tm).runFrom (runCfg cfg) n = runCfg (tm.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ, runFrom_succ, ih (by lia), step_runCfg _ (hhalt.not_halted (by lia))]

/-- From `check`, the machine halts unless the condition holds, and otherwise starts `tm`. -/
lemma step_check (p : Fin (input.length + 2)) (ws : Fin k → List Symbol) (out : List Symbol) :
    (whileCond c tm).step (wordsCfgAt input p (some .check) ws out) =
      wordsCfgAt input p (if condAt c input p ws then some (.run tm.q₀) else none) ws out := by
  have hsym : (wordsCfgAt (State := RepeatUntilBlankState State) input p (some .check) ws
      out).workTapeSymbols = fun j => (ws j).head? := by
    funext j
    simp [Cfg.workTapeSymbols, wordsCfgAt, tapeOfList_zero]
  rw [step_of_state rfl, inputSymbol_eq_inputSymbolAt, hsym]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> (try simp [whileCond, condAt, Action.apply,
    moveInputPos_zero]) <;> rfl

/-- One round: from `check` with the condition holding, the loop runs `tm` once and is back in
`check`, after at most `τ + 1` steps and with its heads within `[-σ, σ]`. -/
lemma exists_runFrom_round {d : Cfg k Symbol (RepeatUntilBlankState State) input} {t : ℕ}
    {p p' : Fin (input.length + 2)} {w w' : Fin k → List Symbol} {out out' : List Symbol}
    {τ σ : ℕ} (hd : ConfinedRun (whileCond c tm) d (wordsCfgAt input p (some .check) w out) t σ)
    (hc : condAt c input p w)
    (hrun : tm.runFrom (wordsCfgAt input p (some tm.q₀) w out) τ = wordsCfgAt input p' none w' out')
    (hsp : (MultiTapeNTM.RunPath.ofDeterministic tm (wordsCfgAt input p (some tm.q₀) w out)
      τ).space ≤ σ) :
    ∃ u ≤ τ, ConfinedRun (whileCond c tm) d (wordsCfgAt input p' (some .check) w' out')
      (t + (u + 1)) σ := by
  obtain ⟨u, hu, hhalt⟩ := exists_haltsAt (show (tm.runFrom _ τ).Halted by rw [hrun]; rfl)
  have hstart : (whileCond c tm).step (wordsCfgAt input p (some .check) w out) =
      runCfg (wordsCfgAt input p (some tm.q₀) w out) := by
    rw [step_check, hc]
    rfl
  have hround : (whileCond c tm).runFrom (wordsCfgAt input p (some .check) w out) (u + 1) =
      wordsCfgAt input p' (some .check) w' out' := by
    rw [Nat.add_comm, runFrom_add, runFrom_one, hstart, runFrom_runCfg hhalt le_rfl,
      ← hhalt.runFrom_eq hu, hrun]
    rfl
  refine ⟨u, hu, by rw [runFrom_add, hd.reaches, hround], fun l => ?_⟩
  rw [visitedByTapeHead_add, hd.reaches]
  refine Finset.union_subset (hd.confined l) (visitedByTapeHead_subset _ fun m hm => ?_)
  rcases m with _ | m
  · simp [runFrom]
  · rw [Nat.add_comm, runFrom_add, runFrom_one, hstart]
    obtain hlt | rfl := (Nat.lt_succ_iff.mp hm).lt_or_eq
    · rw [runFrom_runCfg hhalt hlt.le]
      exact visitedByTapeHead_subset_Icc _ rfl ((space_mono tm _ hu).trans hsp)
        (MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mpr ⟨m, by lia, rfl⟩)
    · rw [runFrom_runCfg hhalt le_rfl, ← hhalt.runFrom_eq hu, hrun]
      simp [runCfg]

end WhileCond

open WhileCond in
/-- Let `P n` be a loop invariant after `n` rounds, on the input position, the words on the tapes
and the word emitted so far. If each round `n < rounds` starts with the condition holding and takes
`P n` to `P (n + 1)` within `t n` steps and `s` cells, and `P rounds` implies that the condition
fails and that `R` holds, then `whileCond c tm` takes `P 0` to `R`. -/
public theorem transformsTapesAt_whileCond {c : Option Symbol → (Fin k → Option Symbol) → Bool}
    {tm : MultiTapeTM k Symbol State}
    {P : ℕ → (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {R : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol →
      Prop} {rounds : ℕ} {t : ℕ → ℕ} {s : ℕ}
    (hround : ∀ n < rounds, ∀ emitted, TransformsTapesAt tm
      (fun input p ws => P n input p ws emitted)
      (fun input _ _ p' ws' e => P (n + 1) input p' ws' (emitted ++ e)) (t n) s)
    (hmore : ∀ n < rounds, ∀ input p ws emitted, P n input p ws emitted → condAt c input p ws)
    (hend : ∀ input p ws emitted, P rounds input p ws emitted →
      condAt c input p ws = false ∧ R input p ws emitted) :
    TransformsTapesAt (whileCond c tm) (fun input p ws => P 0 input p ws [])
      (fun input _ _ p' ws' emitted => R input p' ws' emitted)
      (∑ n ∈ Finset.range rounds, (t n + 1) + 1) (2 * k * s + k) := by
  intro input p ws out hP0
  rw [show (whileCond c tm).q₀ = .check from rfl]
  set start := wordsCfgAt (State := RepeatUntilBlankState State) input p (some .check) ws out
    with hstart
  -- after `n ≤ rounds` rounds the loop is back in `check` with `P n` holding
  have hrec : ∀ n ≤ rounds, ∃ m ≤ ∑ j ∈ Finset.range n, (t j + 1),
      ∃ (pn : Fin (input.length + 2)) (wsn : Fin k → List Symbol) (acc : List Symbol),
      ConfinedRun (whileCond c tm) start (wordsCfgAt input pn (some .check) wsn (out ++ acc)) m s ∧
        P n input pn wsn acc := by
    intro n hn
    induction n with
    | zero =>
      exact ⟨0, by simp, p, ws, [], ⟨by simp [runFrom, hstart], fun l => by
        simp [MultiTapeNTM.RunPath.visitedByTapeHead, MultiTapeNTM.RunPath.ofDeterministic,
          hstart, Finset.subset_iff]⟩, hP0⟩
    | succ n ih =>
      obtain ⟨m, hm, pn, wsn, acc, hc, hPn⟩ := ih (by lia)
      obtain ⟨pn', wsn', e, hrunTm, hQ, hsp⟩ := hround n (by lia) acc input pn wsn (out ++ acc) hPn
      obtain ⟨u, hu, hc'⟩ :=
        exists_runFrom_round hc (hmore n (by lia) input pn wsn acc hPn) hrunTm hsp
      rw [List.append_assoc] at hc'
      exact ⟨m + (u + 1), by rw [Finset.sum_range_succ]; lia, pn', wsn', acc ++ e, hc', hQ⟩
  obtain ⟨m, hm, pLast, wsLast, acc, hc, hPlast⟩ := hrec rounds le_rfl
  obtain ⟨hstop, hR⟩ := hend input pLast wsLast acc hPlast
  have hfinal : (whileCond c tm).runFrom start (m + 1) =
      wordsCfgAt input pLast none wsLast (out ++ acc) := by
    rw [runFrom_succ, hc.reaches, step_check, hstop]
    rfl
  have hhalt : ((whileCond c tm).runFrom start (m + 1)).Halted := by rw [hfinal]; rfl
  refine ⟨pLast, wsLast, acc, ?_, hR, ?_⟩
  · rw [runFrom_eq_of_halt _ _ (by lia) hhalt, hfinal]
  · rw [space_eq_of_halt _ (by lia) hhalt]
    refine space_le_of_visited_subset_Icc _ _ fun l => ?_
    rw [visitedByTapeHead_add, hc.reaches]
    refine Finset.union_subset (hc.confined l) (visitedByTapeHead_subset _ fun j hj => ?_)
    rcases j with _ | j
    · simp [runFrom]
    · rw [runFrom_eq_of_halt (τ := 1) _ _ (by lia) (by rw [runFrom_one, step_check, hstop]; rfl),
        runFrom_one, step_check, hstop]
      simp

end Turing.MultiTapeTM

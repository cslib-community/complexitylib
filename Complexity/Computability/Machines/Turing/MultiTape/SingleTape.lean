/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Complexity.Computability.Machines.Turing.SingleTape.PostTuringMachine
public import Complexity.Foundations.Data.BiTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ReadInput
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Simulation of `SingleTapeTM` by `MultiTapeTM`

This file simulates any single-tape Turing machine (`Cslib.Turing.SingleTapeTM Symbol`) on a
1-work-tape multi-tape Turing machine (`Turing.MultiTapeTM 1 Symbol ...`) in three sequential
phases:

1. `copyInputToWork`: copy the read-only input `x` onto work tape `0` and rewind work tape `0` to
   cell `0` in `2 * x.length + 4` steps (reusing `InputReader.appendOne`).
2. `runOnWork`: execute the single-tape transitions of `tm` directly on work tape `0`. By
   `BiTape.Represents.step`, `n` steps of `tm` correspond to `n` steps of `runOnWork tm`.
3. `emitWork`: starting from the final head position on work tape `0`, walk right and emit each
   non-blank symbol to the output tape until the first blank cell, taking `y.length + 1` steps when
   the final tape represents `BiTape.mk₁ y`.

## Main definitions

* `Turing.MultiTapeTM.copyInputToWork`: copy the input tape to work tape `0` and rewind to `0`.
* `Turing.MultiTapeTM.runOnWork`: run a `SingleTapeTM` on work tape `0`.
* `Turing.MultiTapeTM.emitWork`: emit the word on work tape `0` to the output tape until blank.
* `Turing.MultiTapeTM.ofSingleTapeTM`: the composed 3-phase `MultiTapeTM 1 Symbol` simulating a
  `SingleTapeTM Symbol`.

## Main results

* `Turing.MultiTapeTM.computesInTimeAndSpace_ofTM0`: simulation of Mathlib TM0 machines in
  linear time and space overhead.
* `Turing.MultiTapeTM.computesInTimeAndSpace_ofSingleTapeTM`: if `tm.OutputsWithinTime x y t`, then
  `ofSingleTapeTM tm` computes `y` from `x` in `2 * x.length + 4 + (t + (y.length + 1))` steps
  (and in `3 * x.length + 2 * t + 6` steps).
* `Turing.MultiTapeTM.computes_ofSingleTapeTM`: if `tm.Outputs x y`, then
  `(ofSingleTapeTM tm).Computes x y`.
* `Cslib.Turing.SingleTapeTM.TimeComputable.computableInTimeAndSpace`: transfers
  `SingleTapeTM.TimeComputable` to `MultiTapeTM.ComputableInTimeAndSpace`.
* `Cslib.Turing.SingleTapeTM.PolyTimeComputable.computableInPolyTime`: transfers
  `SingleTapeTM.PolyTimeComputable` to `MultiTapeTM.ComputableInPolyTime`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

open Cslib Cslib.Turing Relation

namespace Turing.MultiTapeTM

variable {Symbol : Type}

/-! ## Phase 1: Copy input to work tape `0` and rewind -/

/-- The `InputReader` that copies every input symbol verbatim. -/
def copyReader (Symbol : Type*) : InputReader Symbol Unit where
  q₀ := ()
  step _ a := (some (), some a)

@[simp] lemma copyReader_q₀ (Symbol : Type*) : (copyReader Symbol).q₀ = () := rfl

@[simp] lemma copyReader_read (Symbol : Type*) (w : List Symbol) :
    (copyReader Symbol).read () w = (w, w.length) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [InputReader.read_cons_of_some (copyReader Symbol) w (q' := ()) rfl, ih]
    rfl

/-- State type of `copyInputToWork`. -/
abbrev CopyInputState := Unit ⊕ Unit ⊕ RewindWorkState

/-- Phase 1 machine: copies the input tape onto work tape `0` and rewinds work tape `0` to cell `0`.
-/
noncomputable def copyInputToWork (Symbol : Type*) : MultiTapeTM 1 Symbol CopyInputState :=
  appendRead (copyReader Symbol) 0

theorem runFrom_copyInputToWork (x : List Symbol) :
    ∃ p' : Fin (x.length + 2),
      (copyInputToWork Symbol).runFrom ((copyInputToWork Symbol).initCfg x) (2 * x.length + 4) =
        ⟨none, p', fun _ => tapeOfList x, fun _ => 0, []⟩ := by
  have hinit : (copyInputToWork Symbol).initCfg x =
      wordsCfgAt x 1 (some (copyInputToWork Symbol).q₀) (fun _ => []) [] := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    simp [MultiTapeNTM.initCfg, Cfg.init, wordsCfgAt]
  have hval : ((1 : Fin (x.length + 2)) : ℕ) = 1 :=
    (Fin.val_one' _).trans (Nat.mod_eq_of_lt (by omega))
  have hp₀ : ((1 : Fin (x.length + 2)) : ℕ) ≠ 0 := by omega
  have happ := transformsTapesAt_appendRead (copyReader Symbol) (0 : Fin 1) x 1 hp₀ []
    x 1 (fun _ => []) [] ⟨rfl, rfl, rfl⟩
  rcases happ with ⟨p', ws', e, hrun, ⟨-, hws', he⟩, -⟩
  refine ⟨p', ?_⟩
  rw [hinit]
  have htime : ([] : List Symbol).length + 1 +
      ((((copyReader Symbol).read (copyReader Symbol).q₀
          (x.drop (((1 : Fin (x.length + 2)) : ℕ) - 1))).2 + 1) +
        (([] ++ ((copyReader Symbol).read (copyReader Symbol).q₀
          (x.drop (((1 : Fin (x.length + 2)) : ℕ) - 1))).1).length + 2)) =
      2 * x.length + 4 := by
    rw [hval]
    simp only [copyReader_q₀, Nat.sub_self, List.drop_zero, copyReader_read, List.length_nil,
      List.nil_append]
    omega
  rw [← htime]
  change (appendRead (copyReader Symbol) 0).runFrom
      (wordsCfgAt x 1 (some (appendRead (copyReader Symbol) 0).q₀) (fun _ => []) []) _ = _
  rw [hrun, hws', he]
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  rw [Fin.fin_one_eq_zero i, hval]
  simp [wordsCfgAt]

/-- `BiTape.mk₁ xs` represents `tapeOfList xs` with head at `0`. -/
theorem represents_tapeOfList (xs : List Symbol) :
    (BiTape.mk₁ xs).Represents (tapeOfList xs) 0 := by
  intro position
  cases position <;> simp [BiTape.read_mk₁, tapeOfList]

/-! ## Phase 2: Run `SingleTapeTM` transitions on work tape `0` -/

/-- Convert an optional `Turing.Dir` to a `SignType` head movement. -/
def dirToSign : Option _root_.Turing.Dir → SignType
  | none => .zero
  | some .left => .neg
  | some .right => .pos

lemma biTape_step_dirToSign (t : BiTape Symbol) (wr : Option Symbol)
    (dir : Option _root_.Turing.Dir) :
    t.step (some wr, dirToSign dir) = (t.write wr).optionMove dir := by
  cases dir with
  | none => rfl
  | some d => cases d <;> rfl

section RunOnWork

variable [Inhabited Symbol] [Fintype Symbol]

/-- Phase 2 machine: executes the transitions of `tm : SingleTapeTM Symbol` on work tape `0`,
leaving the input head and output tape untouched. -/
def runOnWork (tm : SingleTapeTM Symbol) : MultiTapeTM 1 Symbol tm.State :=
  ofTr tm.q₀ fun q _ work =>
    let res := tm.tr q (work 0)
    { inputTape := .zero
      workTapes := fun _ => (some res.1.symbol, dirToSign res.1.movement)
      output := none
      state := res.2 }

/-- Simulation relation between a `SingleTapeTM` configuration and a 1-work-tape `MultiTapeTM`
configuration. -/
structure SimRel (tm : SingleTapeTM Symbol) {input : List Symbol}
    (scfg : tm.Cfg) (mcfg : Cfg 1 Symbol tm.State input) : Prop where
  state : mcfg.state = scfg.state
  work : scfg.BiTape.Represents (mcfg.workTapes 0) (mcfg.workTapePos 0)

theorem SimRel.step {tm : SingleTapeTM Symbol} {input : List Symbol}
    {scfg scfg' : tm.Cfg} {mcfg : Cfg 1 Symbol tm.State input}
    (hsim : SimRel tm scfg mcfg) (hstep : tm.TransitionRelation scfg scfg') :
    SimRel tm scfg' ((runOnWork tm).step mcfg) ∧
      ((runOnWork tm).step mcfg).output = mcfg.output := by
  rcases scfg with ⟨_ | q, t⟩
  · cases hstep
  · have hq : mcfg.state = some q := hsim.state
    have hhead : mcfg.workTapeSymbols 0 = t.head := (hsim.work.head).symm
    obtain ⟨rfl⟩ :
        ({ state := (tm.tr q t.head).2
           BiTape := (t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement } :
          tm.Cfg) = scfg' := Option.some.inj hstep
    rw [step_of_state hq]
    simp only [runOnWork, tr_ofTr, hhead]
    refine ⟨⟨rfl, ?_⟩, by simp [Action.apply]⟩
    have hrep := hsim.work.step (some (tm.tr q t.head).1.symbol,
      dirToSign (tm.tr q t.head).1.movement)
    rw [biTape_step_dirToSign] at hrep
    exact hrep

theorem SimRel.runFrom_of_relatesInSteps {tm : SingleTapeTM Symbol} {input : List Symbol}
    {scfg₁ scfg₂ : tm.Cfg} {mcfg₁ : Cfg 1 Symbol tm.State input} {n : ℕ}
    (hsim : SimRel tm scfg₁ mcfg₁)
    (hrel : RelatesInSteps tm.TransitionRelation scfg₁ scfg₂ n) :
    SimRel tm scfg₂ ((runOnWork tm).runFrom mcfg₁ n) ∧
      ((runOnWork tm).runFrom mcfg₁ n).output = mcfg₁.output := by
  induction hrel with
  | refl => exact ⟨hsim, rfl⟩
  | tail t' t'' m _ hstep ih =>
    rcases ih with ⟨hsim', hout'⟩
    rcases hsim'.step hstep with ⟨hsim'', hout''⟩
    rw [runFrom_succ]
    exact ⟨hsim'', hout''.trans hout'⟩

theorem runFrom_runOnWork_of_outputsWithinTime (tm : SingleTapeTM Symbol)
    {input x y : List Symbol} {t : ℕ} {mcfg : Cfg 1 Symbol tm.State input}
    (hstate : mcfg.state = some tm.q₀)
    (hwork : (BiTape.mk₁ x).Represents (mcfg.workTapes 0) (mcfg.workTapePos 0))
    (hout : tm.OutputsWithinTime x y t) :
    ((runOnWork tm).runFrom mcfg t).state = none ∧
      (BiTape.mk₁ y).Represents (((runOnWork tm).runFrom mcfg t).workTapes 0)
        (((runOnWork tm).runFrom mcfg t).workTapePos 0) ∧
      ((runOnWork tm).runFrom mcfg t).output = mcfg.output := by
  rcases hout with ⟨n, hnt, hrel⟩
  have hsim₀ : SimRel tm (tm.initCfg x) mcfg := ⟨hstate, hwork⟩
  rcases hsim₀.runFrom_of_relatesInSteps hrel with ⟨hsim_n, hout_n⟩
  have hhalt_n : ((runOnWork tm).runFrom mcfg n).state = none := hsim_n.state
  have heq := runFrom_eq_of_halt (runOnWork tm) mcfg hnt hhalt_n
  rw [heq]
  exact ⟨hhalt_n, hsim_n.work, hout_n⟩

end RunOnWork

/-! ## Phase 3: Emit work tape `0` until blank -/

/-- Phase 3 machine: walks right along work tape `0`, emitting each symbol to the output tape, and
halts on the first blank cell. -/
def emitWork (Symbol : Type*) : MultiTapeTM 1 Symbol Unit :=
  ofTr () fun _ _ work =>
    match work 0 with
    | some a => ⟨0, fun _ => (none, 1), some a, some ()⟩
    | none => ⟨0, fun _ => (none, 0), none, none⟩

namespace EmitWork

variable {input : List Symbol} {inpos : Fin (input.length + 2)}

lemma runFrom_walk {y : List Symbol} {contents : ℤ → Option Symbol} {head : ℤ}
    (hrep : (BiTape.mk₁ y).Represents contents head) (out : List Symbol)
    (n : ℕ) (hn : n ≤ y.length) :
    (emitWork Symbol).runFrom ⟨some (), inpos, fun _ => contents, fun _ => head, out⟩ n =
      ⟨some (), inpos, fun _ => contents, fun _ => head + n, out ++ y.take n⟩ := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    have hlt : n < y.length := by omega
    have hsym : contents (head + n) = some (y[n]'hlt) := by
      have hread := (hrep n).symm
      rw [BiTape.read_mk₁] at hread
      simpa [List.getElem?_eq_getElem hlt] using hread
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_of_state rfl]
    simp only [emitWork, tr_ofTr, Cfg.workTapeSymbols, hsym]
    refine Cfg.ext rfl (by simp [Action.apply, moveInputPos_zero]) rfl ?_ ?_
    · funext _
      simp only [Action.apply_workTapePos, SignType.coe_one, Nat.cast_add, Nat.cast_one]
      omega
    · rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [Action.apply]

end EmitWork

open EmitWork in
theorem runFrom_emitWork {input y : List Symbol} (mcfg : Cfg 1 Symbol Unit input)
    (hstate : mcfg.state = some ())
    (hrep : (BiTape.mk₁ y).Represents (mcfg.workTapes 0) (mcfg.workTapePos 0)) :
    ((emitWork Symbol).runFrom mcfg (y.length + 1)).state = none ∧
      ((emitWork Symbol).runFrom mcfg (y.length + 1)).output = mcfg.output ++ y := by
  have hmcfg : mcfg = ⟨some (), mcfg.inputPos, fun _ => mcfg.workTapes 0,
      fun _ => mcfg.workTapePos 0, mcfg.output⟩ := by
    refine Cfg.ext hstate rfl ?_ ?_ rfl <;> funext i <;> rw [Fin.fin_one_eq_zero i]
  have hwalk := runFrom_walk (inpos := mcfg.inputPos) hrep mcfg.output y.length le_rfl
  have hblank : mcfg.workTapes 0 (mcfg.workTapePos 0 + y.length) = none := by
    have hread := (hrep y.length).symm
    rw [BiTape.read_mk₁] at hread
    simpa using hread
  have htotal : (emitWork Symbol).runFrom
      ⟨some (), mcfg.inputPos, fun _ => mcfg.workTapes 0, fun _ => mcfg.workTapePos 0, mcfg.output⟩
      (y.length + 1) =
    ⟨none, mcfg.inputPos, fun _ => mcfg.workTapes 0, fun _ => mcfg.workTapePos 0 + y.length,
      mcfg.output ++ y⟩ := by
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, hwalk, step_of_state rfl]
    simp only [emitWork, tr_ofTr, Cfg.workTapeSymbols, hblank]
    refine Cfg.ext rfl (by simp [Action.apply, moveInputPos_zero]) rfl ?_ ?_
    · funext _
      simp [Action.apply]
    · simp [Action.apply]
  rw [← hmcfg] at htotal
  rw [htotal]
  exact ⟨rfl, rfl⟩

/-! ## Composed 3-phase `SingleTapeTM` simulator -/

section Simulator

variable [Inhabited Symbol] [Fintype Symbol]

/-- State type of `ofSingleTapeTM tm`. -/
abbrev OfSingleTapeState (tm : SingleTapeTM Symbol) :=
  CopyInputState ⊕ tm.State ⊕ Unit

/-- Simulate a `SingleTapeTM Symbol` on a 1-work-tape `MultiTapeTM`:
copy input to work tape `0`, run `tm` on work tape `0`, and emit work tape `0` to output. -/
noncomputable def ofSingleTapeTM (tm : SingleTapeTM Symbol) :
    MultiTapeTM 1 Symbol (OfSingleTapeState tm) :=
  (copyInputToWork Symbol).seq ((runOnWork tm).seq (emitWork Symbol))

open Sequential in
theorem runFrom_ofSingleTapeTM_of_outputsWithinTime (tm : SingleTapeTM Symbol)
    {x y : List Symbol} {t : ℕ} (h : tm.OutputsWithinTime x y t) :
    let T := 2 * x.length + 4 + (t + (y.length + 1))
    ((ofSingleTapeTM tm).runFrom ((ofSingleTapeTM tm).initCfg x) T).Halted ∧
      ((ofSingleTapeTM tm).runFrom ((ofSingleTapeTM tm).initCfg x) T).output = y := by
  intro T
  rcases runFrom_copyInputToWork x with ⟨p', hcopy⟩
  let mid₁ : Cfg 1 Symbol CopyInputState x :=
    ⟨none, p', fun _ => tapeOfList x, fun _ => 0, []⟩
  have hmid₁_halt : mid₁.Halted := rfl
  let start₂ : Cfg 1 Symbol tm.State x := mid₁.withState (some (runOnWork tm).q₀)
  have hrun₂ := runFrom_runOnWork_of_outputsWithinTime tm (mcfg := start₂) rfl
    (represents_tapeOfList x) h
  rcases hrun₂ with ⟨hstate₂, hrep₂, hout₂⟩
  let mid₂ := (runOnWork tm).runFrom start₂ t
  have hmid₂_halt : mid₂.Halted := hstate₂
  let start₃ : Cfg 1 Symbol Unit x := mid₂.withState (some (emitWork Symbol).q₀)
  have hrun₃ := runFrom_emitWork (y := y) start₃ rfl hrep₂
  rcases hrun₃ with ⟨hstate₃, hout₃⟩
  let fin₃ := (emitWork Symbol).runFrom start₃ (y.length + 1)
  have hfin₃_halt : fin₃.Halted := hstate₃
  have hseq₂₃ : ((runOnWork tm).seq (emitWork Symbol)).runFrom
      (leftCfg (emitWork Symbol) start₂) (t + (y.length + 1)) = rightCfg fin₃ :=
    runFrom_seq (tm₀ := runOnWork tm) (tm₁ := emitWork Symbol) rfl hmid₂_halt rfl hfin₃_halt
  have hstart₂_eq : mid₁.withState (some ((runOnWork tm).seq (emitWork Symbol)).q₀) =
      leftCfg (emitWork Symbol) start₂ := rfl
  rw [← hstart₂_eq] at hseq₂₃
  have hright_halt : (rightCfg (State₀ := tm.State) fin₃).Halted := by
    simp [Cfg.Halted, rightCfg, hfin₃_halt]
  have hinit_eq : (ofSingleTapeTM tm).initCfg x =
      leftCfg ((runOnWork tm).seq (emitWork Symbol)) ((copyInputToWork Symbol).initCfg x) := rfl
  have hseq₁₂₃ : (ofSingleTapeTM tm).runFrom ((ofSingleTapeTM tm).initCfg x) T =
      rightCfg (rightCfg fin₃) := by
    rw [hinit_eq]
    exact runFrom_seq (tm₀ := copyInputToWork Symbol)
      (tm₁ := (runOnWork tm).seq (emitWork Symbol)) hcopy hmid₁_halt hseq₂₃ hright_halt
  rw [hseq₁₂₃]
  refine ⟨by simp [Cfg.Halted, rightCfg, hfin₃_halt], ?_⟩
  change ((emitWork Symbol).runFrom start₃ (y.length + 1)).output = y
  rw [hout₃]
  change ((runOnWork tm).runFrom start₂ t).output ++ y = y
  rw [hout₂]
  rfl

/-- If `tm.OutputsWithinTime x y t`, then `ofSingleTapeTM tm` computes `y` from `x` in
`2 * x.length + 4 + (t + (y.length + 1))` steps. -/
theorem computesInTimeAndSpace_ofSingleTapeTM (tm : SingleTapeTM Symbol)
    {x y : List Symbol} {t : ℕ} (h : tm.OutputsWithinTime x y t) :
    let T := 2 * x.length + 4 + (t + (y.length + 1))
    (ofSingleTapeTM tm).ComputesInTimeAndSpace x y T (T + 1) := by
  intro T
  rcases runFrom_ofSingleTapeTM_of_outputsWithinTime tm h with ⟨hhalt, hout⟩
  have h1 : (ofSingleTapeTM tm).ComputesInTimeAndSpace x y T (1 * T + 1) :=
    ⟨⟨T, hhalt, hout⟩, runsInTime_of_halted hhalt,
      runsInSpace_of_halted hhalt
        ((MultiTapeNTM.RunPath.space_le_mul_time_add_one (.ofDeterministic _ _ T)).trans_eq
          (Nat.mul_add_one _ _))⟩
  exact ⟨h1.1, h1.2.1, h1.2.2.mono (by omega)⟩

/-- Input-only time bound for `ofSingleTapeTM tm`: since `y.length ≤ max 1 x.length + t`,
`3 * x.length + 2 * t + 6` steps always suffice. -/
theorem computesInTimeAndSpace_ofSingleTapeTM_of_input (tm : SingleTapeTM Symbol)
    {x y : List Symbol} {t : ℕ} (h : tm.OutputsWithinTime x y t) :
    let T := 3 * x.length + 2 * t + 6
    (ofSingleTapeTM tm).ComputesInTimeAndSpace x y T (T + 1) := by
  intro T
  have hlen : y.length ≤ max 1 x.length + t :=
    SingleTapeTM.output_length_le_input_length_add_time tm x y t h
  have hT : 2 * x.length + 4 + (t + (y.length + 1)) ≤ T := by omega
  have hbase := computesInTimeAndSpace_ofSingleTapeTM tm h
  exact ⟨hbase.1, hbase.2.1.mono hT, hbase.2.2.mono (by omega)⟩

/-- If `tm.Outputs x y`, then `(ofSingleTapeTM tm).Computes x y`. -/
theorem computes_ofSingleTapeTM (tm : SingleTapeTM Symbol) {x y : List Symbol}
    (h : tm.Outputs x y) :
    (ofSingleTapeTM tm).Computes x y := by
  rcases h.relatesInSteps with ⟨t, ht⟩
  exact (computesInTimeAndSpace_ofSingleTapeTM tm ⟨t, le_rfl, ht⟩).1

/-- Any Mathlib `TM0.Machine` supported on `S` is simulated on a 1-work-tape `MultiTapeTM` in
`2 * x.length + 4 + ((t + 1) + (y.length + 1))` steps. -/
theorem computesInTimeAndSpace_ofTM0 {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : _root_.Turing.TM0.Machine (Option Symbol) Λ) (S : Finset Λ)
    (hs : _root_.Turing.TM0.Supports M S) {x y : List Symbol} {t : ℕ} {q_f : Λ}
    (hreach : RelatesWithinSteps (fun a b => b ∈ _root_.Turing.TM0.step M a)
      (_root_.Turing.TM0.init (x.map some)) ⟨q_f, BiTape.equivTape (BiTape.mk₁ y)⟩ t)
    (hhalt : _root_.Turing.TM0.step M ⟨q_f, BiTape.equivTape (BiTape.mk₁ y)⟩ = none) :
    let T := 2 * x.length + 4 + ((t + 1) + (y.length + 1))
    (ofSingleTapeTM (SingleTapeTM.ofTM0 M S hs)).ComputesInTimeAndSpace x y T (T + 1) :=
  computesInTimeAndSpace_ofSingleTapeTM (SingleTapeTM.ofTM0 M S hs)
    ((SingleTapeTM.outputsWithinTime_ofTM0_iff M S hs x y t).mpr ⟨q_f, hreach, hhalt⟩)

/-- Any Mathlib `TM0.Machine` supported on `S` is simulated on a 1-work-tape `MultiTapeTM`. -/
theorem computes_ofTM0 {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : _root_.Turing.TM0.Machine (Option Symbol) Λ) (S : Finset Λ)
    (hs : _root_.Turing.TM0.Supports M S) {x y : List Symbol} {q_f : Λ}
    (h : (⟨q_f, BiTape.equivTape (BiTape.mk₁ y)⟩ : _root_.Turing.TM0.Cfg (Option Symbol) Λ) ∈
      StateTransition.eval (_root_.Turing.TM0.step M) (_root_.Turing.TM0.init (x.map some))) :
    (ofSingleTapeTM (SingleTapeTM.ofTM0 M S hs)).Computes x y :=
  computes_ofSingleTapeTM (SingleTapeTM.ofTM0 M S hs)
    ((SingleTapeTM.outputs_ofTM0_iff M S hs x y).mpr ⟨q_f, h⟩)

end Simulator

end Turing.MultiTapeTM

namespace Cslib.Turing.SingleTapeTM

open _root_.Turing _root_.Turing.MultiTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A `SingleTapeTM.TimeComputable` function is computed by `ofSingleTapeTM hf.tm` in
`3 * n + 2 * hf.timeBound n + 6` steps. -/
theorem TimeComputable.computesFunInTimeAndSpace {α β : Type*} {f : List Symbol → List Symbol}
    (hf : TimeComputable f) (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (g : α → β)
    (hfg : ∀ a, f (encIn a) = encOut (g a)) :
    (ofSingleTapeTM hf.tm).ComputesFunInTimeAndSpace encIn encOut g
      (fun a => 3 * (encIn a).length + 2 * hf.timeBound (encIn a).length + 6)
      (fun a => 3 * (encIn a).length + 2 * hf.timeBound (encIn a).length + 7) := by
  intro a
  have h := hf.outputsFunInTime (encIn a)
  rw [hfg a] at h
  exact computesInTimeAndSpace_ofSingleTapeTM_of_input hf.tm h

/-- A `SingleTapeTM.TimeComputable` function over `Bool` gives
`MultiTapeTM.ComputableInTimeAndSpace`. -/
theorem TimeComputable.computableInTimeAndSpace {α β : Type*} {f : List Bool → List Bool}
    (hf : TimeComputable f) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (g : α → β)
    (hfg : ∀ a, f (encIn a) = encOut (g a)) :
    ComputableInTimeAndSpace g encIn encOut
      (fun a => 3 * (encIn a).length + 2 * hf.timeBound (encIn a).length + 6)
      (fun a => 3 * (encIn a).length + 2 * hf.timeBound (encIn a).length + 7) :=
  ⟨1, OfSingleTapeState hf.tm, inferInstance, ofSingleTapeTM hf.tm,
    hf.computesFunInTimeAndSpace encIn encOut g hfg⟩

/-- A `SingleTapeTM.PolyTimeComputable` function over `Bool` is computable in polynomial time on a
multi-tape Turing machine (`MultiTapeTM.ComputableInPolyTime`). -/
theorem PolyTimeComputable.computableInPolyTime {α β : Type*} {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (g : α → β)
    (hfg : ∀ a, f (encIn a) = encOut (g a)) :
    ComputableInPolyTime g encIn encOut := by
  refine ⟨fun n => 3 * n + 2 * hf.poly.eval n + 6,
    fun n => 3 * n + 2 * hf.poly.eval n + 7, by fun_prop, by fun_prop, ?_⟩
  refine (hf.toTimeComputable.computableInTimeAndSpace encIn encOut g hfg).mono ?_ ?_
  · intro a
    have hb := hf.bounds (encIn a).length
    dsimp only
    omega
  · intro a
    have hb := hf.bounds (encIn a).length
    dsimp only
    omega

/-- Special case of `PolyTimeComputable.computableInPolyTime` for `f : List Bool → List Bool`
under the identity encoding. -/
theorem PolyTimeComputable.computableInPolyTime_id {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) :
    ComputableInPolyTime f (Function.Embedding.refl _) (Function.Embedding.refl _) :=
  hf.computableInPolyTime (Function.Embedding.refl _) (Function.Embedding.refl _) f
    (fun _ => rfl)

end Cslib.Turing.SingleTapeTM

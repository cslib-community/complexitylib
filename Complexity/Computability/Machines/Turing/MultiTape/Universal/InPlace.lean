/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122; `try` steps
-- that the unused-tactic linter flags are dropped

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Translate
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Space
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# The universal machine, reading its input in place

The universal function (`Turing.MultiTapeTM.Universal.universal`) is computed by a multi-pass fold
over its input, one pass per step of the simulation. The state of the fold holds the description,
the configuration and the number of steps left, but never the input `x` of the simulated machine:
a pass reads the symbol under the simulated input head by counting down the symbols of `x` on the
input tape. A finite-state translator (`Turing.MultiTapeTM.Universal.inTr`) turns the encoded
input into events, one per unary digit and one per end of a symbol of `x`, so that the fold is
a plain function on events.

## Main definitions

* `Turing.MultiTapeTM.Universal.inTr`: the events of the encoded input.
* `Turing.MultiTapeTM.Universal.scan`: the countdown to the symbol under the input head.
* `Turing.MultiTapeTM.Universal.stateSpace`: a bound on the states of the fold.

## Main results

* `Turing.MultiTapeTM.Universal.events_eIn`: the events of the encoded input.
* `Turing.MultiTapeTM.Universal.inputSymbol_scan`: the countdown finds the symbol under the input
  head.
* `Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_universal_inPlace`: the universal
  function is tidily computable in space linear in `stateSpace`.
* `Turing.MultiTapeTM.Universal.stateSpace_desc`: on descriptions of machines, `stateSpace` is
  linear in the description times the space of the machine, plus logarithms of the length of the
  input and of the number of steps, plus the largest symbol of the input.
-/

namespace Turing.MultiTapeTM

/-- The bits of `w`, each after a marker `true`: `frame w` is `doubled w` followed by `false`. -/
@[expose] public def doubled (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

@[simp] public lemma doubled_nil : doubled [] = [] := rfl

@[simp] public lemma doubled_cons (b : Bool) (w : List Bool) :
    doubled (b :: w) = true :: b :: doubled w := rfl

@[simp] public lemma doubled_append (u v : List Bool) : doubled (u ++ v) = doubled u ++ doubled v :=
  by simp [doubled]

public lemma frame_eq_doubled (w : List Bool) : frame w = doubled w ++ [false] := rfl

/-- Doubles its input. -/
def doubledT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [true, b])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

lemma doubledT_run (w : List Bool) : doubledT.run () w = doubled w := by
  induction w with
  | nil => rfl
  | cons b w ih => exact congrArg (true :: b :: ·) ih

/-- A function computed by a transducer is computed in the space of its output. -/
public theorem ComputableTidilyInO.of_transducer {Q : Type} [Finite Q] (τ : Transducer Bool Q)
    {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (hf : ∀ a, encOut (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableTidilyInO f encIn encOut (fun a => (encIn a).length)
      fun a => (encOut (f a)).length :=
  .of_bounds (τ.computableTidilyInTimeAndSpace hf) 8 (fun a => by omega)
    (fun _ => Nat.zero_le _) (fun a => by omega)

namespace Universal

/-! ### The events of the input -/

/-- The states of the translator: in the framed description, at a marker or a bit; in the framed
input `x`, at a marker or a bit of the outer frame, before an inner marker or digit; after the
input, in the number of steps. -/
public inductive InState
  | descMarker | descBit | marker | bit | digitMarker | digit | steps
deriving DecidableEq

public instance : Finite InState :=
  Finite.of_surjective (fun n : Fin 7 => [InState.descMarker, .descBit, .marker, .bit,
    .digitMarker, .digit, .steps][n]) fun q => by
      cases q
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩]

/-- The translator of the encoded input into events: `true` for each unary digit of a symbol of
`x` and `false` at the end of each symbol. -/
@[expose] public def inTr : Translator InState Bool where
  q₀ := .descMarker
  step
    | .descMarker, true => (.descBit, none)
    | .descMarker, false => (.marker, none)
    | .descBit, _ => (.descMarker, none)
    | .marker, true => (.bit, none)
    | .marker, false => (.steps, none)
    | .bit, true => (.digitMarker, some true)
    | .bit, false => (.marker, some false)
    | .digitMarker, true => (.digit, none)
    | .digitMarker, false => (.steps, none)
    | .digit, _ => (.marker, none)
    | .steps, _ => (.steps, none)

@[simp] lemma inTr_step_descBit (b : Bool) : inTr.step .descBit b = (.descMarker, none) := rfl
@[simp] lemma inTr_step_marker_true : inTr.step .marker true = (.bit, none) := rfl
@[simp] lemma inTr_step_marker_false : inTr.step .marker false = (.steps, none) := rfl
@[simp] lemma inTr_step_bit_true : inTr.step .bit true = (.digitMarker, some true) := rfl
@[simp] lemma inTr_step_bit_false : inTr.step .bit false = (.marker, some false) := rfl
@[simp] lemma inTr_step_digitMarker : inTr.step .digitMarker true = (.digit, none) := rfl
@[simp] lemma inTr_step_digit (b : Bool) : inTr.step .digit b = (.marker, none) := rfl
@[simp] lemma inTr_step_steps (b : Bool) : inTr.step .steps b = (.steps, none) := rfl

/-- The events of a symbol: its unary digits, then the end. -/
@[expose] public def tok (n : ℕ) : List Bool := List.replicate n true ++ [false]

lemma run_frame (w v : List Bool) : inTr.run .descMarker (frame w ++ v) = inTr.run .marker v := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> exact ih

lemma run_steps (v : List Bool) : inTr.run .steps v = (.steps, []) := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [Translator.run, ih]

lemma run_symbol (n : ℕ) (v : List Bool) :
    inTr.run .marker (doubled (frame (List.replicate n true)) ++ v) =
      ((inTr.run .marker v).1, tok n ++ (inTr.run .marker v).2) := by
  induction n with
  | zero => simp [Translator.run, tok]
  | succ n ih =>
    rw [List.replicate_succ, frame_cons, doubled_cons, doubled_cons]
    simp only [List.cons_append, Translator.run, inTr_step_marker_true, inTr_step_bit_true,
      inTr_step_digitMarker, inTr_step_digit, ih, tok, List.replicate_succ]
    simp

/-- **The events of the encoded input** are the events of the symbols of `x`. -/
public theorem events_eIn (d : Desc) (x : List ℕ) (t : ℕ) :
    inTr.events (eIn (d, x, t)) = (x.map tok).flatten := by
  have hx : ∀ v, inTr.run .marker (doubled (encList encUnary x) ++ v) =
      ((inTr.run .marker v).1, (x.map tok).flatten ++ (inTr.run .marker v).2) := by
    intro v
    induction x with
    | nil => simp
    | cons n x ih =>
      rw [encList_cons, doubled_append, List.append_assoc, encUnary_apply, run_symbol, ih]
      simp
  rw [Translator.events, show eIn (d, x, t) = frame (eDesc d) ++ (frame (encList encUnary x) ++
    encNat t) from rfl, show inTr.q₀ = .descMarker from rfl, run_frame, frame_eq_doubled,
    List.append_assoc, hx, List.singleton_append]
  simp [Translator.run, run_steps]

/-! ### The countdown -/

/-- A round of the countdown: a digit counts towards the symbol read while the countdown is at
`1`, and the end of a symbol counts down. -/
@[expose] public def scan (p : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  if b then (p.1, if p.1 = 1 then p.2 + 1 else p.2) else (p.1 - 1, p.2)

lemma foldl_scan_replicate (k cur j : ℕ) :
    (List.replicate j true).foldl scan (k, cur) = (k, if k = 1 then cur + j else cur) := by
  induction j generalizing cur with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldl_cons]
    simp only [scan, ↓reduceIte, ih]
    split_ifs <;> simp
    omega

public lemma scan_tok (k cur n : ℕ) :
    (tok n).foldl scan (k, cur) = (k - 1, if k = 1 then cur + n else cur) := by
  simp [tok, List.foldl_append, foldl_scan_replicate, scan]

lemma scan_zero (l : List Bool) (cur : ℕ) : l.foldl scan (0, cur) = (0, cur) := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [scan, ih]

/-- The countdown from `k ≥ 1` ends at `0` exactly when `k ≤ x.length`, having read `x[k - 1]`. -/
lemma scan_all (x : List ℕ) (k cur : ℕ) (hk : 1 ≤ k) :
    ((x.map tok).flatten).foldl scan (k, cur) =
      (k - x.length, cur + (x.drop (k - 1)).head?.getD 0) := by
  induction x generalizing k cur with
  | nil => simp
  | cons n x ih =>
    simp only [List.map_cons, List.flatten_cons, List.foldl_append, scan_tok]
    rcases Nat.lt_or_ge 1 (k - 1) with h | h
    · rw [ih _ _ (by omega)]
      simp only [show k ≠ 1 by omega, ↓reduceIte, List.length_cons]
      rw [show k - 1 - 1 = k - 2 by omega, show k - 1 = (k - 2) + 1 by omega, List.drop_succ_cons]
      congr 1
      omega
    · rcases Nat.eq_or_lt_of_le h with h | h
      · obtain rfl : k = 2 := by omega
        rw [ih _ _ le_rfl]
        simp
      · obtain rfl : k = 1 := by omega
        simp [scan_zero]

/-- **The countdown finds the symbol under the input head.** -/
public theorem inputSymbol_scan (x : List ℕ) (p : ℕ) :
    inputSymbol x p = if p = 0 ∨ ((x.map tok).flatten.foldl scan (p, 0)).1 ≠ 0 then none
      else some ((x.map tok).flatten.foldl scan (p, 0)).2 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [inputSymbol]
  rw [scan_all x p 0 hp]
  simp only [inputSymbol, hp.ne', false_or, ne_eq, ↓reduceIte, Nat.zero_add]
  rcases Nat.lt_or_ge (p - 1) x.length with h | h
  · simp [Nat.sub_eq_zero_iff_le.mpr (by omega : p ≤ x.length), List.head?_drop, h]
  · simp [List.drop_of_length_le h, show p - x.length ≠ 0 by omega]

/-! ### The fold -/

/-- The state of the fold: the description and the configuration, then the number of steps left,
the countdown and the symbol read so far. -/
public abbrev St := (Desc × SCfg) × (ℕ × ℕ × ℕ)

/-- The encoding of states of the fold, with the number of steps left and the countdown in
binary. -/
public abbrev eSt : St ↪ List Bool :=
  encPair (encPair eDesc eCfg) (encPair encNat (encPair encNat encUnary))

/-- The initial state: the initial configuration, all steps left, and the countdown at the input
head. -/
@[expose] public def foldInit (i : Desc × List ℕ × ℕ) : St := ((i.1, init i.1), (i.2.2, 1, 0))

/-- A round: one event of the countdown. -/
@[expose] public def foldNext (p : St × Bool) : St := (p.1.1, (p.1.2.1, scan p.1.2.2 p.2))

/-- The symbol under the input head, at the end of a pass. -/
@[expose] public def symAt (s : St) : Option ℕ :=
  if s.1.2.inputPos = 0 ∨ s.2.2.1 ≠ 0 then none else some s.2.2.2

/-- The step at the end of a pass, if any steps are left, and the symbol it emits. -/
@[expose] public def stepAt (s : St) : SCfg × Option ℕ :=
  if s.2.1 = 0 then (s.1.2, none) else stepWith s.1.1 s.1.2 (symAt s)

/-- The end of a pass: the step, and the countdown reset to the new input head. -/
@[expose] public def foldEnd (s : St) : St :=
  ((s.1.1, (stepAt s).1), (s.2.1 - 1, (stepAt s).1.inputPos, 0))

/-- The emitted symbol, as its part of the encoded output. -/
@[expose] public def foldEmit (s : St) : List Bool :=
  (stepAt s).2.elim [] fun n => doubled (frame (encUnary n))

/-- Whether another pass follows. -/
@[expose] public def foldCont (s : St) : Bool := s.2.1 ≠ 0

/-- Whether the simulated machine has halted. -/
@[expose] public def foldFinish (s : St) : Bool := s.1.2.state.isNone

/-- The end of the encoded output: the end of the frame of the output, then whether the machine
has halted. -/
@[expose] public def eHalted : Bool ↪ List Bool :=
  ⟨fun b => [false, b], fun _ _ h => by simpa using h⟩

/-- The events of the input `x`. -/
@[expose] public def events (x : List ℕ) : List Bool := (x.map tok).flatten

lemma streamState_foldNext (s : St) (l : List Bool) (j : ℕ) :
    streamState s foldNext l j = (s.1, (s.2.1, (l.take j).foldl scan s.2.2)) :=
  List.foldl_hom (fun a => (s.1, (s.2.1, a))) (fun _ _ => rfl)

public lemma run_succ' (d : Desc) (x : List ℕ) (j : ℕ) :
    run d x (j + 1) = (step d x (run d x j)).1 := by
  simp only [run, Function.iterate_succ_apply', stepOut]

/-- The end of pass `i`, after the countdown over the input. -/
lemma stepAt_scan (d : Desc) (x : List ℕ) (c : SCfg) (r : ℕ) :
    stepAt ((d, c), (r, (events x).foldl scan (c.inputPos, 0))) =
      if r = 0 then (c, none) else step d x c := by
  rw [stepAt, step_eq_stepWith, inputSymbol_scan]
  rfl

/-- **The passes** follow the steps of the simulation, as long as steps are left. -/
public theorem passState_fold (d : Desc) (x : List ℕ) (t i : ℕ) :
    passState (foldInit (d, x, t)) foldNext foldEnd (events x) i =
      ((d, run d x (min i t)), (t - i, (run d x (min i t)).inputPos, 0)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [passState, ih, streamState_foldNext, List.take_length, foldEnd]
    simp only
    rw [stepAt_scan]
    split_ifs with h
    · rw [show min (i + 1) t = min i t by omega]
      simp only [Prod.mk.injEq, true_and, and_true]
      omega
    · rw [show min (i + 1) t = min i t + 1 by omega, run_succ']
      simp only [Prod.mk.injEq, true_and, and_true]
      omega

/-- What pass `i` emits. -/
lemma foldEmit_pass (d : Desc) (x : List ℕ) (t i : ℕ) :
    foldEmit (streamState (passState (foldInit (d, x, t)) foldNext foldEnd (events x) i) foldNext
      (events x) (events x).length) =
      if i < t then (step d x (run d x i)).2.elim [] fun n => doubled (frame (encUnary n))
      else [] := by
  rw [passState_fold, streamState_foldNext, List.take_length, foldEmit]
  simp only
  rw [stepAt_scan]
  by_cases h : i < t
  · have h' : ¬t - i = 0 := by omega
    simp only [h, h', ↓reduceIte, show min i t = i by omega]
  · have h' : t - i = 0 := by omega
    simp only [h, h', ↓reduceIte]
    rfl

public lemma simulate_eq (d : Desc) (x : List ℕ) (t : ℕ) : simulate d x t =
    (((List.range t).map fun i => (step d x (run d x i)).2.toList).flatten,
      (run d x t).state.isNone) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [simulate, Prod.mk.injEq] at ih ⊢
    rw [Function.iterate_succ_apply', run_succ', List.range_succ, List.map_append,
      List.flatten_append]
    exact ⟨by rw [← ih.1]; simp [stepOut, run], by rw [stepOut]; rfl⟩

/-- The encoded output: the symbols emitted by the passes, then whether the machine has halted. -/
public theorem eOut_universal (d : Desc) (x : List ℕ) (t : ℕ) :
    eOut (universal (d, x, t)) = ((List.range (t - 1 + 1)).map fun i =>
      encBits (foldEmit (streamState (passState (foldInit (d, x, t)) foldNext foldEnd (events x) i)
        foldNext (events x) (events x).length))).flatten ++
      eHalted (foldFinish (passState (foldInit (d, x, t)) foldNext foldEnd (events x)
        (t - 1 + 1))) := by
  have hout (out : List ℕ) (b : Bool) : eOut (out, b) =
      (out.map fun n => doubled (frame (encUnary n))).flatten ++ eHalted b := by
    rw [show eOut (out, b) = frame (encList encUnary out) ++ [b] from rfl, frame_eq_doubled,
      List.append_assoc]
    congr 1
    induction out with
    | nil => rfl
    | cons n out ih => rw [encList_cons, doubled_append, ih]; rfl
  rw [universal, simulate_eq, hout, foldFinish, passState_fold, show min (t - 1 + 1) t = t by omega]
  congr 1
  simp only [encBits_apply, foldEmit_pass, List.map_flatten, List.map_map, List.flatten_flatten]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rfl
  rw [show t - 1 + 1 = t by omega]
  refine congrArg List.flatten (List.map_congr_left fun i hi => ?_)
  simp only [Function.comp_apply, List.mem_range.mp hi, ↓reduceIte]
  cases (step d x (run d x i)).2 <;> simp

/-! ### The parts of the fold, within bounds in the length of the state -/

open ComputableTidilyInO

/-- A round of the countdown. -/
public lemma foldNext_inO : ComputableTidilyInO foldNext (encPair eSt encBool) eSt
    (fun p => ((encPair eSt encBool p).length + 1) ^ 2)
    fun p => (encPair eSt encBool p).length + 1 := by
  have hs := fst eSt encBool
  have hb := snd eSt encBool
  have hdc := hs.fst'
  have hn := hs.snd'
  have hr := hn.fst'
  have hk := hn.snd'.fst'
  have hcur := hn.snd'.snd'
  have hk1 := (ComputableInO.eq encNat).tidy.comp (hk.prod (const (encMid := encNat) 1))
  have hsucc := (of_linear (.of_cons_true (f := (· + 1)) (encIn := encUnary) (encOut := encUnary)
    fun n => rfl)).comp_linear hcur
  have hkpred := ComputableInO.natPred.tidy.comp hk
  have hdigit := hdc.prod (hr.prod (hk.prod (hk1.ite hsucc hcur)))
  have hend := hdc.prod (hr.prod (hkpred.prod hcur))
  refine ((hb.ite hdigit hend).of_enc_eq (g := foldNext) fun p => ?_).mono 100 (fun p => ?_)
    fun p => ?_
  · obtain ⟨⟨dc, r, k, cur⟩, b⟩ := p
    cases b <;> simp [foldNext, scan]
  all_goals
    have hk : (encNat p.1.2.2.1).length ≤ (encPair eSt encBool p).length := by
      simp only [length_encPair]
      omega
    have h1 : (encNat 1).length = 1 := rfl
    have h2 : (encPair encNat encNat (p.1.2.2.1, 1)).length ≤
        2 * (encPair eSt encBool p).length + 2 := by
      simp only [length_encPair, h1]
      omega
    dsimp only [Function.comp_apply]
    try simp only [h1]
    split_ifs <;> nlinarith

/-- The context of the step at the end of a pass is no longer than the state. -/
lemma length_ctx_le (s : St) : (eWCtx (s.1, symAt s)).length ≤ (eSt s).length + 1 := by
  have : (eSym (symAt s)).length ≤ s.2.2.2 + 1 := by
    unfold symAt
    split_ifs <;> simp
  simp only [length_encPair, encUnary_apply, List.length_replicate] at this ⊢
  omega

lemma wTime_le (s : St) : wTime (s.1, symAt s) ≤ 9 * ((eSt s).length + 1) ^ 3 := by
  have hc := length_ctx_le s
  have ht := length_le_length_encList eTape s.1.2.workTapes
  have hd := length_le_length_encList (encPair eKey eAct) s.1.1.table
  have hl : s.1.2.workTapes.length + s.1.1.table.length + 1 ≤ (eSt s).length + 1 := by
    simp only [length_encPair, eCfg_apply, eDesc_apply] at ht hd ⊢
    omega
  have hdesc : (eDesc s.1.1).length ≤ (eSt s).length := by
    simp only [length_encPair]
    omega
  have hpos : (encNat s.1.2.inputPos).length ≤ (eSt s).length := by
    simp only [length_encPair, eCfg_apply]
    omega
  have hproduct : (s.1.2.workTapes.length + s.1.1.table.length + 1) *
      ((eDesc s.1.1).length + 1) * ((eWCtx (s.1, symAt s)).length + 1) ≤
        ((eSt s).length + 1) * ((eSt s).length + 1) * ((eSt s).length + 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul hl (by omega)) (by omega)
  have hdigits := Nat.pow_le_pow_left (Nat.succ_le_succ hpos) 2
  unfold wTime
  dsimp only at hproduct hdigits ⊢
  nlinarith [Nat.le_self_pow (show 2 ≠ 0 by decide) ((eSt s).length + 1)]

/-- The step at the end of a pass. -/
public lemma stepAt_inO : ComputableTidilyInO stepAt eSt (encPair eCfg eSym)
    (fun s => ((eSt s).length + 1) ^ 3) fun s => (eSt s).length + 1 := by
  have hdc := fst (encPair eDesc eCfg) (encPair encNat (encPair encNat encUnary))
  have hn := snd (encPair eDesc eCfg) (encPair encNat (encPair encNat encUnary))
  have hc := hdc.snd'
  have hpos := (hc.of_enc_eq (encOut := eCfgFields)
    (g := fun s : St => (s.1.2.state, s.1.2.inputPos, s.1.2.workTapes)) fun _ => rfl).snd'.fst'
  have hr := hn.fst'
  have hk := hn.snd'.fst'
  have hcur := hn.snd'.snd'
  have hor := (ComputableTidilyInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun b : Bool × Bool => b.1 || !b.2).inO_one.comp_linear
      ((ComputableInO.natIsZero.tidy.comp_linear hpos).prod
        (ComputableInO.natIsZero.tidy.comp_linear hk))
  have hsym : ComputableTidilyInO symAt eSt eSym _ _ :=
    (hor.ite (const none) ((ComputableTidilyInDegree.optionSome (enc₁ := encUnary)
      (enc := eSym)).inO_one.comp_linear hcur)).of_enc_eq fun s => by
        simp only [symAt, Function.comp_apply]
        split_ifs <;> simp_all
  have hstep := stepWith_inO.comp (hdc.prod hsym)
  have hidle := hc.prod (const (encMid := eSym) none)
  refine (((ComputableInO.natIsZero.tidy.comp_linear hr).ite hidle hstep).of_enc_eq (g := stepAt)
    fun s => ?_).mono 100 (fun s => ?_) fun s => ?_
  · simp only [stepAt, Function.comp_apply]
    split_ifs <;> simp_all
  all_goals
    have := wTime_le s
    have := length_ctx_le s
    dsimp only [eSt] at *
    generalize ((encPair (encPair eDesc eCfg) (encPair encNat (encPair encNat encUnary))) s).length
      = L at *
    have hL : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    split_ifs <;> linarith

/-- A uniform bound on the parts at the end of a pass. -/
lemma le_cube {L a : ℕ} (h : a ≤ 6 * (L + 1)) : a ≤ 6 * ((L + 1) ^ 3 + 1) := by
  have : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

/-- The end of a pass. -/
public lemma foldEnd_inO : ComputableTidilyInO foldEnd eSt eSt
    (fun s => ((eSt s).length + 1) ^ 3) fun s => (eSt s).length + 1 := by
  have hdc := fst (encPair eDesc eCfg) (encPair encNat (encPair encNat encUnary))
  have hn := snd (encPair eDesc eCfg) (encPair encNat (encPair encNat encUnary))
  have hc := stepAt_inO.fst'
  have hpos := (hc.of_enc_eq (encOut := eCfgFields)
    (g := fun s : St => ((stepAt s).1.state, (stepAt s).1.inputPos, (stepAt s).1.workTapes))
    fun _ => rfl).snd'.fst'
  have hr := ComputableInO.natPred.tidy.comp hn.fst'
  refine (((hdc.fst'.prod hc).prod (hr.prod (hpos.prod (const (encMid := encUnary) 0)))).of_enc_eq
    (g := foldEnd) fun s => rfl).mono 100 (fun s => ?_) fun s => ?_
  all_goals
    have hr : (encNat s.2.1).length ≤ (eSt s).length := by simp only [length_encPair]; omega
    have h₁ : ((encNat s.2.1).length + 1) ^ 2 ≤ ((eSt s).length + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have h₂ : ((eSt s).length + 1) ^ 2 ≤ ((eSt s).length + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hL : (eSt s).length + 1 ≤ ((eSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    nlinarith

/-- What a pass emits. -/
public lemma foldEmit_inO : ComputableTidilyInO foldEmit eSt encBits
    (fun s => ((eSt s).length + 1) ^ 3) fun s => (eSt s).length + 1 := by
  have ho := stepAt_inO.snd'
  have hsome := (ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear ho
  have hn := (ComputableTidilyInDegree.getD (enc₁ := encUnary) (enc := eSym) 0).inO_one.comp_linear
    ho
  have hdbl : ComputableTidilyInO (fun n => doubled (frame (encUnary n))) encUnary encBits
      (fun n => (encUnary n).length) fun n => (encUnary n).length :=
    (of_linear (doubledT.computableTidilyInLinearTimeAndSpace (f := doubled) (encIn := encBits)
      (encOut := encBits) fun w => (doubledT_run w).symm)).comp_linear
      (of_linear (.of_frame (f := fun n => frame (encUnary n)) fun _ => rfl))
  refine ((hsome.ite (hdbl.comp_linear hn) (const (encMid := encBits) [])).of_enc_eq
    (g := foldEmit) fun s => ?_).mono 100 (fun s => ?_) fun s => ?_
  · simp only [foldEmit, Function.comp_apply]
    cases (stepAt s).2 <;> rfl
  all_goals
    have hL : (eSt s).length + 1 ≤ ((eSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    simp only [Function.comp_apply]
    split_ifs <;> nlinarith

/-- Whether another pass follows. -/
public lemma foldCont_inO : ComputableTidilyInO foldCont eSt encBool
    (fun s => ((eSt s).length + 1) ^ 3) fun s => (eSt s).length + 1 := by
  have hr := (snd (encPair eDesc eCfg) (encPair encNat (encPair encNat encUnary))).fst'
  refine (((ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool)
    fun b : Bool => !b).inO_one.comp_linear (ComputableInO.natIsZero.tidy.comp_linear hr)).of_enc_eq
    (g := foldCont) fun s => by simp [foldCont]).mono 1 (fun s => ?_) fun s => ?_ <;>
  · have hL : (eSt s).length + 1 ≤ ((eSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have : (encNat s.2.1).length ≤ (eSt s).length := by simp only [length_encPair]; omega
    dsimp only [eSt] at *
    omega

/-- Whether the simulated machine has halted. -/
public lemma foldFinish_inO : ComputableTidilyInO foldFinish eSt eHalted
    (fun s => ((eSt s).length + 1) ^ 3) fun s => (eSt s).length + 1 := by
  have hc := (fst (encPair eDesc eCfg) (encPair encNat (encPair encNat encUnary))).snd'
  refine (((ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := eHalted)
    fun b : Bool => !b).inO_one.comp_linear
      ((ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear
        (state_inO.comp_linear hc))).of_enc_eq (g := foldFinish) fun s => by
        simp only [foldFinish, Function.comp_apply]
        cases s.1.2.state <;> rfl).mono 1 (fun s => ?_) fun s => ?_ <;>
  · have hL : (eSt s).length + 1 ≤ ((eSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    dsimp only [eSt] at *
    omega

/-! ### The initial state, without the input -/

/-- The states of the extracting transducer: in the framed description, at a marker or a bit; in
the framed input, at a marker or a bit; in the number of steps. -/
public inductive ExState
  | descMarker | descBit | marker | bit | steps

public instance : Finite ExState :=
  Finite.of_surjective (fun n : Fin 5 => [ExState.descMarker, .descBit, .marker, .bit,
    .steps][n]) fun q => by
      cases q
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

/-- Copies the framed description, drops the framed input and copies the number of steps. -/
@[simps q₀ step final]
def extractT : Transducer Bool ExState where
  q₀ := .descMarker
  step
    | .descMarker, true => (.descBit, [true])
    | .descMarker, false => (.marker, [false])
    | .descBit, b => (.descMarker, [b])
    | .marker, true => (.bit, [])
    | .marker, false => (.steps, [])
    | .bit, _ => (.marker, [])
    | .steps, b => (.steps, [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

lemma extractT_run (d : Desc) (x : List ℕ) (t : ℕ) :
    extractT.run extractT.q₀ (eIn (d, x, t)) = encPair eDesc encNat (d, t) := by
  have h₁ (w v : List Bool) :
      extractT.run .descMarker (frame w ++ v) = frame w ++ extractT.run .marker v := by
    induction w with
    | nil => rfl
    | cons b w ih => cases b <;> simp [ih]
  have h₂ (w v : List Bool) : extractT.run .marker (frame w ++ v) = extractT.run .steps v := by
    induction w with
    | nil => rfl
    | cons b w ih => cases b <;> simp [ih]
  have h₃ (w : List Bool) : extractT.run .steps w = w := by
    induction w with
    | nil => rfl
    | cons b w ih => simp [ih]
  simp only [eIn, encPair_apply, extractT_q₀, h₁, h₂, h₃]

/-- The initial state, in the space of the description and the number of steps. -/
public lemma foldInit_inO : ComputableTidilyInO foldInit eIn eSt
    (fun i => (eIn i).length + ((encPair eDesc encNat (i.1, i.2.2)).length + 1) ^ 2)
    fun i => (encPair eDesc encNat (i.1, i.2.2)).length + 1 := by
  have hext := ComputableTidilyInO.of_transducer extractT (f := fun i : Desc × List ℕ × ℕ =>
    (i.1, i.2.2)) (encIn := eIn) (encOut := encPair eDesc encNat)
    fun i => (extractT_run i.1 i.2.1 i.2.2).symm
  have hd := fst eDesc encNat
  have ht := snd eDesc encNat
  have hg := (hd.prod (init_inO.comp hd)).prod
    (ht.prod ((const (encMid := encNat) 1).prod (const (encMid := encUnary) 0)))
  refine ((hg.comp hext).of_enc_eq (g := foldInit) fun i => rfl).mono 10 (fun i => ?_)
    fun i => ?_
  all_goals
    have : (eDesc i.1).length ≤ (encPair eDesc encNat (i.1, i.2.2)).length := by
      simp only [length_encPair]; omega
    dsimp only
    nlinarith

/-! ### The size of the state -/

/-- Along the events of a symbol, the countdown does not go up and the symbol read grows by at
most the symbol. -/
lemma scan_take_tok (n k cur j : ℕ) :
    (((tok n).take j).foldl scan (k, cur)).1 ≤ k ∧
      (((tok n).take j).foldl scan (k, cur)).2 ≤ cur + n ∧
      ((((tok n).take j).foldl scan (k, cur)).2 = cur ∨ k = 1) := by
  rcases Nat.lt_or_ge n j with h | h
  · rw [List.take_of_length_le (by simp [tok]; omega), scan_tok]
    split_ifs <;> simp_all
  · rw [tok, List.take_append_of_le_length (by simpa using h), List.take_replicate,
      Nat.min_eq_left h, foldl_scan_replicate]
    split_ifs <;> simp_all

/-- **Along the events of the input**, the countdown does not go up and the symbol read stays
within the largest symbol. -/
lemma scan_take (x : List ℕ) (k cur j : ℕ) :
    (((events x).take j).foldl scan (k, cur)).1 ≤ k ∧
      (((events x).take j).foldl scan (k, cur)).2 ≤ cur + x.foldr max 0 := by
  induction x generalizing k cur j with
  | nil => simp [events]
  | cons n x ih =>
    rw [events, List.map_cons, List.flatten_cons, ← events, List.take_append, List.foldl_append]
    obtain ⟨h₁, h₂, h₃⟩ := scan_take_tok n k cur j
    set p := ((tok n).take j).foldl scan (k, cur)
    obtain ⟨h₄, h₅⟩ := ih p.1 p.2 (j - (tok n).length)
    simp only [Prod.mk.eta] at h₄ h₅
    refine ⟨h₄.trans h₁, ?_⟩
    rcases h₃ with h₃ | rfl
    · simp only [List.foldr_cons] at h₅ ⊢
      omega
    · rcases Nat.lt_or_ge j (tok n).length with hj | hj
      · rw [Nat.sub_eq_zero_of_le hj.le]
        simp only [List.take_zero, List.foldl_nil, List.foldr_cons]
        omega
      · have hp : p = (0, cur + n) := by
          simp only [p, List.take_of_length_le hj, scan_tok, ↓reduceIte]
        rw [hp, scan_zero]
        simp only [List.foldr_cons]
        omega

public lemma simSpace_mono (d : Desc) (x : List ℕ) {j j' : ℕ} (h : j ≤ j') :
    simSpace d x j ≤ simSpace d x j' :=
  Finset.sum_le_sum fun _ _ => Finset.card_le_card (Finset.image_subset_image (by
    intro a ha
    simp only [Finset.mem_range] at ha ⊢
    omega))

/-- A bound on the configurations of the simulation within `t` steps, from
`Turing.MultiTapeTM.Universal.length_eCfg_le_space`. -/
@[expose] public def cfgSpace (d : Desc) (x : List ℕ) (t : ℕ) : ℕ :=
  2 * descLen d + 3 + 2 * (encNat (x.length + 1)).length + 1 +
    3 * (2 * descLen d + 5) * 2 * simSpace d x t + d.tapes

/-- A bound on the states of the fold: the description, a configuration, the number of steps and
the position of the input head in binary, and the largest symbol of the input. -/
@[expose] public def stateSpace (d : Desc) (x : List ℕ) (t : ℕ) : ℕ :=
  2 * (2 * descLen d + 1 + cfgSpace d x t) + 1 + (2 * (encNat t).length + 1 +
    (2 * (encNat (x.length + 1)).length + 1 + x.foldr max 0))

/-- **The size of the states** of the fold. -/
public lemma length_eSt_le (d : Desc) (x : List ℕ) (t i j : ℕ) :
    (eSt (streamState (passState (foldInit (d, x, t)) foldNext foldEnd (events x) i) foldNext
      (events x) j)).length ≤ stateSpace d x t := by
  rw [passState_fold, streamState_foldNext]
  have hc := (length_eCfg_le_space d x (min i t)).trans (show _ ≤ cfgSpace d x t by
    have := simSpace_mono d x (show min i t ≤ t by omega)
    unfold cfgSpace
    gcongr)
  have hpos := (inv_iterate d x (min i t)).1.inputPos
  obtain ⟨hk, hcur⟩ := scan_take x (run d x (min i t)).inputPos 0 j
  have hr := ComputableTidilyInO.length_encNat_mono (show t - i ≤ t by omega)
  have hk' := ComputableTidilyInO.length_encNat_mono (hk.trans hpos)
  simp only [length_encPair, encUnary_apply, List.length_replicate, stateSpace, descLen] at *
  omega

/-! ### The universal machine -/

/-- The states of the translator, by number. -/
def InState.toFin : InState → Fin 7
  | .descMarker => 0 | .descBit => 1 | .marker => 2 | .bit => 3 | .digitMarker => 4 | .digit => 5
  | .steps => 6

/-- An encoding of the states of the translator. -/
def encInState : InState ↪ List Bool :=
  ⟨fun q => encUnary q.toFin, fun a b h => by
    cases a <;> cases b <;> simp_all [InState.toFin]⟩

/-- The time of the universal machine, simplified. -/
lemma final_time (c N t L P E : ℕ) (hP : P ≤ L) (hE : E ≤ L) :
    c * (N + (P + 1) ^ 2 + (E + 1) ^ 3 + (t - 1 + 1) * (N + (N + 1) * (9 * (L + 1) ^ 3 + L + 1)))
      ≤ 20 * c * ((t + 1) * (N + 1) ^ 2 * (L + 1) ^ 3) := by
  have hA : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h₁ : (P + 1) ^ 2 ≤ (L + 1) ^ 3 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h₂ : (E + 1) ^ 3 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h₃ : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h₄ : t - 1 + 1 ≤ t + 1 := by omega
  rw [Nat.mul_assoc 20, Nat.mul_left_comm 20 c]
  refine Nat.mul_le_mul_left c ?_
  set Y := (L + 1) ^ 3
  set Z := (N + 1) ^ 2 * Y
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hz₁ : (N + 1) * Y ≤ Z := Nat.mul_le_mul_right _ hN
  have hz₂ : N + 1 ≤ (N + 1) * Y := Nat.le_mul_of_pos_right _ hA
  have hz₃ : Y ≤ (N + 1) * Y := Nat.le_mul_of_pos_left _ (by omega)
  have hz₄ : Z ≤ (t + 1) * Z := Nat.le_mul_of_pos_left _ (by omega)
  have h₅ : N + (N + 1) * (9 * Y + L + 1) ≤ 11 * Z := by
    have := Nat.mul_le_mul_left (N + 1) (show 9 * Y + L + 1 ≤ 10 * Y by omega)
    rw [show (N + 1) * (10 * Y) = 10 * ((N + 1) * Y) by ring] at this
    omega
  calc _ ≤ N + Y + Y + (t + 1) * (11 * Z) := by gcongr
    _ = N + Y + Y + 11 * ((t + 1) * Z) := by ring
    _ ≤ 20 * ((t + 1) * Z) := by omega
    _ = 20 * ((t + 1) * (N + 1) ^ 2 * Y) := by ring

/-- The space of the universal machine, simplified. -/
lemma final_space (c L P E : ℕ) (hP : P ≤ L) (hE : E ≤ L) :
    c * (P + 1 + (E + 1) + 9 * (L + 1) + L + 1) ≤ 12 * c * (L + 1) := by
  rw [Nat.mul_assoc 12, Nat.mul_left_comm 12 c]
  exact Nat.mul_le_mul_left c (by omega)

lemma length_eSt_le' (d : Desc) (x : List ℕ) (t i j : ℕ) :
    (eSt (streamState (passState (foldInit (d, x, t)) foldNext foldEnd (inTr.events (eIn (d, x, t)))
      i) foldNext (inTr.events (eIn (d, x, t))) j)).length ≤ stateSpace d x t := by
  rw [events_eIn]
  exact length_eSt_le d x t i j

/-- **The universal machine, reading its input in place.** The universal function is tidily
computable in space linear in a bound on the states of the simulation (`stateSpace`): the
description, a configuration, the number of steps and the position of the input head in binary,
and the largest symbol of the input. It never copies the input. Each step reads the whole
input. -/
public theorem computableTidilyInTimeAndSpace_universal_inPlace : ∃ c,
    ComputableTidilyInTimeAndSpace universal eIn eOut
      (fun i => c * ((i.2.2 + 1) * ((eIn i).length + 1) ^ 2 * (stateSpace i.1 i.2.1 i.2.2 + 1) ^ 3))
      (fun i => c * (stateSpace i.1 i.2.1 i.2.2 + 1)) := by
  refine Exists.elim (ComputableTidilyInTimeAndSpace.multiPassFold_translate inTr
    (encQ := encInState)
    foldInit_inO foldNext_inO foldEmit_inO foldEnd_inO foldCont_inO foldFinish_inO
    (passes := fun i => i.2.2 - 1) (g := universal) (encOut := eOut) ?_ ?_
    (tMax := fun i => 9 * (stateSpace i.1 i.2.1 i.2.2 + 1) ^ 3)
    (sMax := fun i => 9 * (stateSpace i.1 i.2.1 i.2.2 + 1))
    (lMax := fun i => stateSpace i.1 i.2.1 i.2.2) ?_ ?_ ?_ ?_ ?_ ?_) fun c h => ?_
  case refine_1 =>
    rintro ⟨d, x, t⟩ i hi
    rw [events_eIn]
    change foldCont (passState (foldInit (d, x, t)) foldNext foldEnd (events x) (i + 1)) = _
    rw [passState_fold]
    simp only [foldCont, decide_eq_decide]
    omega
  case refine_2 =>
    rintro ⟨d, x, t⟩
    rw [events_eIn]
    exact eOut_universal d x t
  case refine_3 =>
    rintro ⟨d, x, t⟩ i - j -
    have := length_eSt_le' d x t i j
    rw [length_encPair, encBool_apply, List.length_singleton]
    generalize (eSt _).length = a at this ⊢
    have h₁ := Nat.pow_le_pow_left (show 2 * a + 1 + 1 + 1 ≤ 3 * (stateSpace d x t + 1) by omega) 2
    have h₂ : (stateSpace d x t + 1) ^ 2 ≤ (stateSpace d x t + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  case refine_4 =>
    rintro ⟨d, x, t⟩ i - j -
    have := length_eSt_le' d x t i j
    rw [length_encPair, encBool_apply, List.length_singleton]
    dsimp only
    omega
  case refine_5 =>
    rintro ⟨d, x, t⟩ i -
    have h₁ := length_eSt_le' d x t i (inTr.events (eIn (d, x, t))).length
    have h₂ : (eSt (passState (foldInit (d, x, t)) foldNext foldEnd (inTr.events (eIn (d, x, t)))
      (i + 1))).length ≤ _ := length_eSt_le' d x t (i + 1) 0
    have h₃ := Nat.pow_le_pow_left (Nat.add_le_add_right h₁ 1) 3
    have h₄ := Nat.pow_le_pow_left (Nat.add_le_add_right h₂ 1) 3
    refine (Nat.add_le_add (Nat.add_le_add h₃ h₃) h₄).trans ?_
    generalize (stateSpace d x t + 1) ^ 3 = Y
    omega
  case refine_6 =>
    rintro ⟨d, x, t⟩ i -
    have h₁ := length_eSt_le' d x t i (inTr.events (eIn (d, x, t))).length
    have h₂ : (eSt (passState (foldInit (d, x, t)) foldNext foldEnd (inTr.events (eIn (d, x, t)))
      (i + 1))).length ≤ _ := length_eSt_le' d x t (i + 1) 0
    refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right h₁ 1)
      (Nat.add_le_add_right h₁ 1)) (Nat.add_le_add_right h₂ 1)).trans ?_
    dsimp only
    omega
  case refine_7 =>
    rintro ⟨d, x, t⟩ i - j -
    exact length_eSt_le' d x t i j
  case refine_8 =>
    rintro ⟨d, x, t⟩
    dsimp only
    exact length_eSt_le' d x t (t - 1 + 1) 0
  refine ⟨20 * c, h.mono (fun i => ?_) fun i => ?_⟩ <;> obtain ⟨d, x, t⟩ := i <;> dsimp only
  · exact final_time c _ t _ _ _ (by simp only [length_encPair, stateSpace, descLen]; omega)
      (length_eSt_le' d x t (t - 1 + 1) 0)
  · exact (final_space c _ _ _ (by simp only [length_encPair, stateSpace, descLen]; omega)
      (length_eSt_le' d x t (t - 1 + 1) 0)).trans (Nat.mul_le_mul_right _ (by omega))

/-- The bound on the states, in the description, the cells visited by the simulation, the
lengths of the input and the number of steps in binary, and the largest symbol of the input. -/
public lemma stateSpace_le (d : Desc) (x : List ℕ) (t : ℕ) :
    stateSpace d x t ≤ 60 * (descLen d + 1) * (simSpace d x t + 1) +
      6 * (encNat (x.length + 1)).length + 2 * (encNat t).length + x.foldr max 0 := by
  have : d.tapes ≤ descLen d := by
    simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]
    omega
  simp only [stateSpace, cfgSpace]
  nlinarith

/-- **The space of the universal machine** on the description of a machine: linear in the
description times the space of the machine, plus the logarithms of the length of the input and of
the number of steps, plus the largest symbol of the input. -/
public theorem stateSpace_desc {k : ℕ} {Symbol S : Type} [Fintype S] [Fintype Symbol]
    (eS : S ↪ ℕ) (eY : Symbol ↪ ℕ) (tm : MultiTapeTM k Symbol S) (x : List Symbol) (t : ℕ) :
    stateSpace (desc eS eY tm) (x.map eY) t ≤
      60 * (descLen (desc eS eY tm) + 1) *
          ((MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg x) t).space + 1) +
        6 * (encNat (x.length + 1)).length + 2 * (encNat t).length + (x.map eY).foldr max 0 := by
  simpa [simSpace_desc] using stateSpace_le (desc eS eY tm) (x.map eY) t

end Universal

end Turing.MultiTapeTM

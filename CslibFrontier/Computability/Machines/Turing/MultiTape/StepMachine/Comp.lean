/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.StepMachine.Basic

/-!
# Composing step machines

`g.comp f` runs `g` on the output of `f` without ever writing that output down. It keeps the state
of `g` and the position of its head on the output of `f`. Whenever `g` needs the symbol under its
head, `g.comp f` runs `f` from the start on its own input, counting down the bits that `f` emits to
the one under the head of `g`, and then makes a step of `g` and rewinds its input head to restart
`f`.

## Main definitions

* `Turing.StepMachine.comp`: the composition.

## Main results

* `Turing.StepMachine.simulates_comp`: `g.comp f` simulates `g` on the output of `f`, with
  `compPeriod` steps per step of `g`.
* `Turing.StepMachine.exists_haltsAt_comp`: `g.comp f` halts within `ug * compPeriod` steps, with
  the output of `g` on the output of `f`.
* `Turing.StepMachine.Computes.comp`: `g.comp f` computes `g` after `f`.
-/

@[expose] public section

namespace Turing.StepMachine

variable {σf σg Out : Type*}

/-- The phases of `g.comp f`: running `f`, or rewinding the input head, before or after the first
move to the left. -/
inductive CompPhase
  | run | rewindStart | rewind
deriving DecidableEq

/-- A countdown over the bits emitted by `f` to the bit under the head of `g`. -/
structure Countdown where
  /-- The number of bits still to come, up to the one sought. -/
  k : ℕ
  /-- The bit found. -/
  found : Bool
  /-- The number of bits emitted so far. -/
  len : ℕ

namespace Countdown

/-- The countdown to the bit at the position `p`, before any bit is emitted. -/
def start (p : ℕ) : Countdown := ⟨p, false, 0⟩

@[simp] lemma len_start (p : ℕ) : (start p).len = 0 := rfl

/-- One more emitted bit: the countdown goes down, and at `1` the bit is found. -/
def push (c : Countdown) (b : Bool) : Countdown :=
  ⟨c.k - 1, if c.k = 1 then b else c.found, c.len + 1⟩

/-- The symbol at the position `p`, once all bits are emitted: a blank before the first bit and
after the last one. -/
def symbol (p : ℕ) (c : Countdown) : Option Bool :=
  if p = 0 ∨ c.k ≠ 0 then none else some c.found

end Countdown

/-- The state of `g.comp f`: the state of `g` with the position of its head on the output of `f`,
the phase, the state of `f`, and the countdown. -/
structure CompState (σf σg : Type*) where
  /-- The state of `g` and the position of its head on the output of `f`. -/
  g : σg × ℕ
  /-- The phase. -/
  phase : CompPhase
  /-- The state of `f`. -/
  f : σf
  /-- The countdown to the bit under the head of `g`. -/
  cd : Countdown

/-- The head of `g` after the move `d` from `p` on an output of length `n`: as `moveInputPos`, it
stays on the blanks at `0` and `n + 1`. -/
def moveOn (n p : ℕ) : SignType → ℕ
  | 0 => p
  | -1 => p - 1
  | 1 => if p = n + 1 then p else p + 1

/-- The step of `g.comp f` on the symbol `a` under the input head. -/
def compStep (f : StepMachine σf Bool Bool) (g : StepMachine σg Bool Out) (s : CompState σf σg)
    (a : Option Bool) : CompState σf σg × SignType × List Out :=
  match s.phase with
  | .run =>
    if f.halt s.f then
      -- `f` has halted: the countdown has found the symbol under the head of `g`
      let r := g.step s.g.1 (s.cd.symbol s.g.2)
      let p := moveOn s.cd.len s.g.2 r.2.1
      (⟨(r.1, p), .rewindStart, f.init, .start p⟩, 0, r.2.2)
    else
      let r := f.step s.f a
      ({ s with f := r.1, cd := r.2.2.foldl .push s.cd }, r.2.1, [])
  | .rewindStart => ({ s with phase := .rewind }, -1, [])
  | .rewind => if a.isNone then ({ s with phase := .run }, 1, []) else (s, -1, [])

/-- **The composition**: `g` run on the output of `f`, which is never written down. -/
def comp (g : StepMachine σg Bool Out) (f : StepMachine σf Bool Bool) :
    StepMachine (CompState σf σg) Bool Out where
  init := ⟨(g.init, 1), .run, f.init, .start 1⟩
  halt s := decide (s.phase = .run) && g.halt s.g.1
  step := compStep f g

/-! ### The head of `g` and the countdown -/

lemma val_moveInputPos {n p : ℕ} (hp : p < n + 2) (d : SignType) :
    (moveInputPos (⟨p, hp⟩ : Fin (n + 2)) d).val = moveOn n p d := by
  rcases d with _ | _ | _
  · simp [moveOn, moveInputPos_zero]
  · simp [moveOn, SignType.neg_eq_neg_one]
  · simp only [moveOn, SignType.pos_eq_one, MultiTapeTM.val_moveInputPos_pos]
    split_ifs <;> omega

namespace Countdown

lemma foldl_push_zero (w : List Bool) (fd : Bool) (len : ℕ) :
    w.foldl push ⟨0, fd, len⟩ = ⟨0, fd, len + w.length⟩ := by
  induction w generalizing len with
  | nil => rfl
  | cons b w ih => simp [push, ih]; omega

lemma foldl_push (w : List Bool) {k : ℕ} (fd : Bool) (len : ℕ) (hk : 1 ≤ k) :
    w.foldl push ⟨k, fd, len⟩ =
      ⟨k - w.length, if k ≤ w.length then w.getD (k - 1) false else fd, len + w.length⟩ := by
  induction w generalizing k fd len with
  | nil => simp; omega
  | cons b w ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hk'
    · simp [push, foldl_push_zero]
      omega
    · rw [List.foldl_cons, push, ih (k := k - 1) _ _ (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      simp only [show j + 2 ≠ 1 by omega, ↓reduceIte, List.length_cons, mk.injEq]
      refine ⟨by omega, ?_, by omega⟩
      split_ifs <;> first | omega | simp

lemma k_foldl (w : List Bool) (c : Countdown) : (w.foldl push c).k = c.k - w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih => rw [List.foldl_cons, ih]; simp [push]; omega

lemma len_foldl (w : List Bool) (c : Countdown) : (w.foldl push c).len = c.len + w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih => rw [List.foldl_cons, ih]; simp [push]; omega

/-- **The countdown finds the bit under the head of `g`.** -/
lemma symbol_foldl (y : List Bool) (p : ℕ) (hp : p < y.length + 2) :
    (y.foldl push (start p)).symbol p = MultiTapeTM.inputSymbolAt y ⟨p, hp⟩ := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp [symbol, MultiTapeTM.inputSymbolAt]
  rw [start, foldl_push y false 0 hp0]
  simp only [symbol, MultiTapeTM.inputSymbolAt, hp0.ne', ↓reduceIte, false_or]
  rcases Nat.lt_or_ge (p - 1) y.length with h | h
  · simp [show p ≤ y.length by omega, show p - y.length = 0 by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h]
  · simp [show p - y.length ≠ 0 by omega,
      List.getElem?_eq_none (show y.length ≤ p - 1 by omega)]

end Countdown

/-! ### The run of the composition -/

section Run

variable (f : StepMachine σf Bool Bool) (g : StepMachine σg Bool Out) (x : List Bool)

/-- **Rewinding**: from the position `r` on the input in the rewinding phase, the input head
reaches the first cell after `r + 1` steps, and the phase is back to running `f`. -/
lemma rewind_iterate (s : CompState σf σg) (out : List Out) (r : ℕ) (hr : r ≤ x.length) :
    (g.comp f).stepCfg^[r + 1]
        (⟨{ s with phase := .rewind }, ⟨r, by omega⟩, out⟩ : Cfg (CompState σf σg) Out x) =
      ⟨{ s with phase := .run }, 1, out⟩ := by
  induction r with
  | zero =>
    simp [stepCfg, stepAt, comp, compStep, MultiTapeTM.inputSymbolAt, moveInputPos, SignType.cast]
  | succ r ih =>
    rw [Function.iterate_succ_apply]
    convert ih (by omega) using 2
    have hsym : (MultiTapeTM.inputSymbolAt x ⟨r + 1, by omega⟩).isNone = false := by
      simp [MultiTapeTM.inputSymbolAt, List.getElem?_eq_getElem (show r < x.length by omega)]
    simp only [stepCfg, stepAt, comp, compStep, hsym]
    simp [moveInputPos, SignType.cast, show r < x.length + 2 by omega]

/-- While rewinding, the input head moves to the left and nothing else changes. -/
lemma rewind_iterate_le (s : CompState σf σg) (out : List Out) {j r : ℕ} (hj : j ≤ r)
    (hr : r ≤ x.length) :
    (g.comp f).stepCfg^[j]
        (⟨{ s with phase := .rewind }, ⟨r, by omega⟩, out⟩ : Cfg (CompState σf σg) Out x) =
      ⟨{ s with phase := .rewind }, ⟨r - j, by omega⟩, out⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hsym : (MultiTapeTM.inputSymbolAt x ⟨r - j, by omega⟩).isNone = false := by
      simp [MultiTapeTM.inputSymbolAt, show r - j ≠ 0 by omega,
        List.getElem?_eq_getElem (show r - j - 1 < x.length by omega)]
    simp only [stepCfg, stepAt, comp, compStep, hsym, reduceCtorEq, decide_false, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, List.append_nil, Cfg.mk.injEq, true_and, and_true]
    refine Fin.ext ?_
    rw [val_moveInputPos]
    simp only [moveOn]
    omega

/-- The time of the rewind from the position `p`. -/
def rewindTime (p : ℕ) : ℕ := p - 1 + 2

/-- **The rewind** from the position `p`: after `rewindTime p` steps the input head is on the
first cell and the phase is back to running `f`. -/
lemma stepCfg_rewindStart (s : CompState σf σg) (out : List Out) (p : Fin (x.length + 2)) :
    (g.comp f).stepCfg
        (⟨{ s with phase := .rewindStart }, p, out⟩ : Cfg (CompState σf σg) Out x) =
      ⟨{ s with phase := .rewind }, ⟨p.val - 1, by omega⟩, out⟩ := by
  simp only [stepCfg, stepAt, comp, compStep]
  refine congrArg₂ _ rfl (congrArg₂ _ (Fin.ext ?_) (by simp))
  rw [show p = ⟨p.val, p.isLt⟩ from rfl, val_moveInputPos]
  rfl

lemma rewindStart_iterate (s : CompState σf σg) (out : List Out) (p : Fin (x.length + 2)) :
    (g.comp f).stepCfg^[rewindTime p]
        (⟨{ s with phase := .rewindStart }, p, out⟩ : Cfg (CompState σf σg) Out x) =
      ⟨{ s with phase := .run }, 1, out⟩ := by
  rw [rewindTime, show p.val - 1 + 2 = (p.val - 1 + 1) + 1 by omega, Function.iterate_succ_apply,
    stepCfg_rewindStart]
  exact rewind_iterate f g x s out _ (by omega)

/-- During the rewind, only the phase changes. -/
lemma rewindStart_iterate_le (s : CompState σf σg) (out : List Out) (p : Fin (x.length + 2))
    {j : ℕ} (hj : j ≤ rewindTime p) : ∃ ph, ((g.comp f).stepCfg^[j]
      (⟨{ s with phase := .rewindStart }, p, out⟩ : Cfg (CompState σf σg) Out x)).state =
        { s with phase := ph } := by
  rcases j with _ | j
  · exact ⟨_, rfl⟩
  rw [Function.iterate_succ_apply, stepCfg_rewindStart]
  rcases Nat.lt_or_ge j (p.val - 1 + 1) with h | h
  · exact ⟨_, by rw [rewind_iterate_le f g x s out (by omega) (by omega)]⟩
  · obtain rfl : j = p.val - 1 + 1 := by simp only [rewindTime] at hj; omega
    exact ⟨_, by rw [rewind_iterate f g x s out _ (by omega)]⟩

/-- **Running `f`**: from the start of a round, the composition follows the run of `f` on the
input, counting down its output to the position `pg` of the head of `g`. -/
lemma run_f_iterate {uf : ℕ} (hf : f.HaltsAt x uf) (sg : σg) (hsg : g.halt sg = false) (pg : ℕ)
    (out : List Out) {r : ℕ} (hr : r ≤ uf) :
    (g.comp f).stepCfg^[r]
        (⟨⟨(sg, pg), .run, f.init, .start pg⟩, 1, out⟩ : Cfg (CompState σf σg) Out x) =
      ⟨⟨(sg, pg), .run, (f.run x r).state, (f.run x r).out.foldl .push (.start pg)⟩,
        (f.run x r).pos, out⟩ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hfh : f.halt (f.run x r).state = false := by simpa using hf.2 r (by omega)
    rw [Function.iterate_succ_apply', ih (by omega), f.run_succ_of_not_halt hfh]
    simp [stepCfg, stepAt, comp, compStep, hsg, hfh]

/-- The configuration of `g.comp f` at the start of the round for the configuration `c` of `g`:
the input head on the first cell, ready to run `f`. -/
def roundCfg {y : List Bool} (c : Cfg σg Out y) : Cfg (CompState σf σg) Out x :=
  ⟨⟨(c.state, c.pos.val), .run, f.init, .start c.pos.val⟩, 1, c.out⟩

/-- **A round**: after running `f` to its halt, the composition makes the step of `g` on the bit
under its head and starts rewinding. -/
lemma round_g {uf : ℕ} (hf : f.HaltsAt x uf) (c : Cfg σg Out (f.run x uf).out)
    (hc : g.halt c.state = false) :
    (g.comp f).stepCfg^[uf + 1] (roundCfg f x c) =
      ⟨⟨((g.stepCfg c).state, (g.stepCfg c).pos.val), .rewindStart, f.init,
        .start (g.stepCfg c).pos.val⟩, (f.run x uf).pos, (g.stepCfg c).out⟩ := by
  rw [Function.iterate_succ_apply', roundCfg, run_f_iterate f g x hf _ hc _ _ le_rfl]
  have hfh : f.halt (f.run x uf).state = true := hf.1
  have hsym := Countdown.symbol_foldl (f.run x uf).out c.pos.val c.pos.isLt
  have hmv := fun d => (val_moveInputPos (n := (f.run x uf).out.length) c.pos.isLt d).symm
  simp only [Fin.eta] at hsym hmv
  simp [stepCfg, stepAt, comp, compStep, hc, hfh, hsym, Countdown.len_foldl, hmv]

/-- The length of a round: running `f`, the step of `g` and the rewind. -/
def compPeriod (uf : ℕ) : ℕ := uf + 1 + rewindTime (f.run x uf).pos.val

/-- The composition starts at the start of the first round. -/
lemma run_zero_comp {y : List Bool} : (g.comp f).run x 0 = roundCfg f x (g.initCfg y) := by
  simp [roundCfg, initCfg, comp, run]

/-- **The composition simulates `g` on the output of `f`**, a step of `g` per round. -/
theorem simulates_comp {uf : ℕ} (hf : f.HaltsAt x uf) :
    (g.comp f).Simulates x (g.stepCfg (input := (f.run x uf).out)) (fun c => g.halt c.state)
      Cfg.out (fun c C => C = roundCfg f x c) (compPeriod f x uf) where
  step c _ hC hc := by
    rw [hC, compPeriod, Nat.add_comm (uf + 1), Function.iterate_add_apply, round_g f g x hf c hc]
    exact rewindStart_iterate f g x ⟨_, .run, f.init, _⟩ _ _
  halt_eq := by rintro c _ rfl; simp [roundCfg, comp]
  out_eq := by rintro c _ rfl; rfl

/-- `s` is made of states along the runs of `f` on `x` up to `uf` and of `g` on the output of `f`
up to `ug`, with its countdown within the output of `f`. -/
structure CompState.Along (f : StepMachine σf Bool Bool) (g : StepMachine σg Bool Out)
    (x : List Bool) (uf ug : ℕ) (s : CompState σf σg) : Prop where
  exists_g : ∃ q ≤ ug, s.g = ((g.run (f.run x uf).out q).state, (g.run (f.run x uf).out q).pos.val)
  exists_f : ∃ r ≤ uf, s.f = (f.run x r).state
  k_le : s.cd.k ≤ (f.run x uf).out.length + 1
  len_le : s.cd.len ≤ (f.run x uf).out.length

/-- **The states along the run** of `g.comp f` are made of states along the runs of `f` and `g`. -/
theorem along_run_comp {uf ug : ℕ} (hf : f.HaltsAt x uf) (hg : g.HaltsAt (f.run x uf).out ug)
    {i : ℕ} (hi : i ≤ ug * compPeriod f x uf) :
    ((g.comp f).run x i).state.Along f g x uf ug := by
  set y := (f.run x uf).out with hy
  obtain ⟨q, j, hj, hqu, hround, hrun⟩ := (simulates_comp f g x hf).exists_round
    (run_zero_comp f g x) (u := ug) (fun i hi => Bool.eq_false_iff.mpr (hg.2 i hi))
    (by simp [compPeriod]) hi
  simp only [Nat.zero_add] at hround hrun
  rw [hrun, show (g.comp f).run x (q * compPeriod f x uf) = roundCfg f x (g.run y q) from hround]
  have hpos (q : ℕ) : (g.run y q).pos.val ≤ y.length + 1 := Nat.lt_succ_iff.mp (g.run y q).pos.isLt
  rcases Nat.eq_zero_or_pos j with rfl | hj₀
  · exact ⟨⟨q, by omega, rfl⟩, ⟨0, Nat.zero_le _, rfl⟩, hpos q, Nat.zero_le _⟩
  have hq : q < ug := hqu.resolve_right (by omega)
  have hgq : g.halt (g.run y q).state = false := Bool.eq_false_iff.mpr (hg.2 q hq)
  rcases Nat.lt_or_ge uf j with hjf | hjf
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + (uf + 1) := ⟨j - (uf + 1), by omega⟩
    rw [Function.iterate_add_apply, round_g f g x hf _ hgq]
    obtain ⟨ph, hph⟩ := rewindStart_iterate_le f g x
      ⟨((g.stepCfg (g.run y q)).state, (g.stepCfg (g.run y q)).pos.val), .run, f.init,
        .start (g.stepCfg (g.run y q)).pos.val⟩ (g.stepCfg (g.run y q)).out (f.run x uf).pos
      (j := j') (by simp only [compPeriod] at hj; omega)
    rw [hph, ← run_succ]
    exact ⟨⟨q + 1, hq, rfl⟩, ⟨0, Nat.zero_le _, rfl⟩, hpos (q + 1), Nat.zero_le _⟩
  · rw [roundCfg, run_f_iterate f g x hf _ hgq _ _ hjf]
    have hlen := (f.out_run_prefix (input := x) hjf).length_le
    refine ⟨⟨q, hq.le, rfl⟩, ⟨j, hjf, rfl⟩, ?_, ?_⟩
    · simp only [Countdown.k_foldl, Countdown.start, ← hy]
      have := hpos q
      omega
    · simp only [Countdown.len_foldl, Countdown.start, ← hy] at hlen ⊢
      omega

/-- **Composition**: when `f` halts after `uf` steps and `g` on its output after `ug` steps,
`g.comp f` halts within `ug` rounds, with the output of `g`. -/
theorem exists_haltsAt_comp {uf ug : ℕ} (hf : f.HaltsAt x uf)
    (hg : g.HaltsAt (f.run x uf).out ug) :
    ∃ t ≤ ug * compPeriod f x uf, (g.comp f).HaltsAt x t ∧
      ((g.comp f).run x t).out = (g.run (f.run x uf).out ug).out :=
  by
  have h := (simulates_comp f g x hf).exists_haltsAt (run_zero_comp f g x) (u := ug)
    (fun i hi => Bool.eq_false_iff.mpr (hg.2 i hi)) hg.1
  rw [Nat.zero_add] at h
  exact h

/-- **Composition**: `g.comp f` computes `g` after `f`. -/
theorem Computes.comp {y : List Bool} {z : List Out} (hf : f.Computes x y) (hg : g.Computes y z) :
    (g.comp f).Computes x z := by
  obtain ⟨uf, hf, rfl⟩ := hf
  obtain ⟨ug, hg, rfl⟩ := hg
  obtain ⟨t, -, ht⟩ := exists_haltsAt_comp f g x hf hg
  exact ⟨t, ht⟩

end Run

end Turing.StepMachine

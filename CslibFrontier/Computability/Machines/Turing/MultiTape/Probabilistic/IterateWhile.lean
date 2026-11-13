/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Iterating a probabilistic oracle machine while its result is non-empty

`tm.iterateWhile mark` applies the tidy probabilistic oracle machine `tm` to its input, then to
the result, and so on, until `tm` produces the empty word, and then outputs the last word before
the empty one. The machine keeps the current word on one work tape and the next word on another.
A round copies the next word to the current tape and computes the new next word from it with `tm`.
Rounds are repeated by `Turing.MultiTapePTM.repeatUntilBlank` until the next word is empty.
The tape layout helpers are module-private, as in the deterministic construction.

Each round makes exactly the oracle calls of `tm` on the current word, with the external oracle
state left by the previous round. The final round's program returns the empty word, and the loop
then halts; no further round is executed.

## Main definitions

* `Turing.MultiTapePTM.iterateWhileRound`: one round of the iteration.
* `Turing.MultiTapePTM.iterateWhile`: the iterating machine.

## Main results

* `Turing.MultiTapePTM.ComputesTidily.iterateWhile`: if `tm` tidily computes `step w` from every
  word `w` reached in the first `r` rounds and the empty word in round `r`, then
  `tm.iterateWhile mark` tidily computes `OracleComp.iterate r step`, preserving the joint law of
  the result and the external oracle state.
* `Turing.MultiTapePTM.RunsInSpace.iterateWhile`: the same supplied closed machine uses
  workspace independent of the number of rounds, with an explicit terminal-round certificate.

## References

Adapts `Combinators/IterateWhile` (vendored crei:crei/tidy-universal @7f7c0696), by Christian
Reitwiessner, and cslib's `Plumbing/RepeatUntilBlank` to probabilistic oracle machines.
-/

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeTM

variable {k : ℕ} {State Operation : Type} {x : List Bool} [DecidableEq Operation]

namespace IterateWhile

/-! ### The tapes -/

section Tapes

variable (k)

/-- The tape holding the current word: the input tape of `Turing.MultiTapePTM.onWords`. -/
abbrev curTape : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 0

/-- The tape holding the next word: the output tape of `Turing.MultiTapePTM.onWords`. -/
abbrev nextTape : Fin (k + 1 + 2) := (Fin.last k).castAdd 2

/-- The flag tape of `Turing.MultiTapePTM.onWords`. -/
abbrev flagTape : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 1

/-- The tapes of `Turing.MultiTapeTM.copyWord`: from the next tape to the current tape, flagged on
the flag tape. -/
def copyEmb : Fin (0 + 1 + 2) ↪ Fin (k + 1 + 2) :=
  ⟨![curTape k, nextTape k, flagTape k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at h ⊢ <;> omega⟩

/-- The tapes of `Turing.MultiTapeTM.emitWord`: the current tape, flagged on the flag tape. -/
def emitEmb : Fin (0 + 2) ↪ Fin (k + 1 + 2) :=
  ⟨![curTape k, flagTape k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at h ⊢⟩

end Tapes

/-- `copyEmb` writes to the current tape. -/
@[simp] theorem copyEmb_zero : copyEmb k 0 = curTape k := rfl
/-- `copyEmb` reads the next tape. -/
@[simp] theorem copyEmb_one : copyEmb k 1 = nextTape k := rfl
/-- `copyEmb` flags on the flag tape. -/
@[simp] theorem copyEmb_two : copyEmb k 2 = flagTape k := rfl
/-- `emitEmb` reads the current tape. -/
@[simp] theorem emitEmb_zero : emitEmb k 0 = curTape k := rfl
/-- `emitEmb` flags on the flag tape. -/
@[simp] theorem emitEmb_one : emitEmb k 1 = flagTape k := rfl

/-- The current and next tapes differ. -/
theorem curTape_ne_nextTape : curTape k ≠ nextTape k := Fin.ne_of_val_ne (by simp)

/-- The flag and next tapes differ. -/
theorem flagTape_ne_nextTape : flagTape k ≠ nextTape k :=
  Fin.ne_of_val_ne (by simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]; omega)

/-- The flag and current tapes differ. -/
theorem flagTape_ne_curTape : flagTape k ≠ curTape k := Fin.ne_of_val_ne (by simp)

/-- The words between two phases: `vc` on the current tape, `vn` on the next tape, all other
tapes blank. -/
def words (vc vn : List Bool) : Fin (k + 1 + 2) → List Bool :=
  Function.update (Function.update (fun _ => []) (curTape k) vc) (nextTape k) vn

/-- The current tape holds the current word. -/
@[simp]
theorem words_cur (vc vn : List Bool) : words (k := k) vc vn (curTape k) = vc := by
  simp [words, curTape_ne_nextTape]

/-- The next tape holds the next word. -/
@[simp]
theorem words_next (vc vn : List Bool) : words (k := k) vc vn (nextTape k) = vn := by
  simp [words]

/-- The flag tape is blank. -/
@[simp]
theorem words_flag (vc vn : List Bool) : words (k := k) vc vn (flagTape k) = [] := by
  simp [words, flagTape_ne_nextTape, flagTape_ne_curTape]

/-- Replacing the current word. -/
theorem update_words_cur (vc vn v : List Bool) :
    Function.update (words (k := k) vc vn) (curTape k) v = words v vn := by
  rw [words, Function.update_comm curTape_ne_nextTape.symm, Function.update_idem, ← words]

/-- Replacing the next word. -/
theorem update_words_next (vc vn v : List Bool) :
    Function.update (words (k := k) vc vn) (nextTape k) v = words vc v := by
  rw [words, Function.update_idem, ← words]

/-- Without a next word, only the current tape is non-blank. -/
theorem words_nil_next (v : List Bool) :
    words (k := k) v [] = Function.update (fun _ => []) (curTape k) v :=
  Function.update_eq_self_iff.mpr (by simp [curTape_ne_nextTape.symm])

/-- Without a current word, only the next tape is non-blank. -/
theorem words_nil_cur (v : List Bool) :
    words (k := k) [] v = Function.update (fun _ => []) (nextTape k) v := by
  rw [words, Function.update_eq_self]

/-- Without words, every tape is blank. -/
theorem words_nil_nil : words (k := k) [] [] = fun _ => [] := by
  rw [words_nil_next, Function.update_eq_self]

/-- The words on the current and next tapes determine the tapes. -/
theorem words_injective : Function.Injective (fun p : List Bool × List Bool =>
    words (k := k) p.1 p.2) := by
  rintro ⟨vc, vn⟩ ⟨vc', vn'⟩ h
  have hcur := congrFun h (curTape k)
  have hnext := congrFun h (nextTape k)
  simp only [words_cur, words_next] at hcur hnext
  rw [hcur, hnext]

/-! ### The deterministic phases -/

/-- The states of `Turing.MultiTapePTM.IterateWhile.prepareRound`. -/
public abbrev PrepareState : Type :=
  (Unit ⊕ RewindWorkState) ⊕
    (MarkWorkState ⊕ ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕ MarkWorkState) ⊕
      (Unit ⊕ RewindWorkState)

/-- The states of `Turing.MultiTapePTM.IterateWhile.finish`. -/
public abbrev FinishState : Type :=
  (MarkWorkState ⊕ (Unit ⊕ RewindState) ⊕ MarkWorkState) ⊕ (Unit ⊕ RewindWorkState)

/-- The states of `Turing.MultiTapePTM.iterateWhileRound`. -/
public abbrev RoundState (State : Type) : Type :=
  PrepareState ⊕ (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState)

/-- The states of `Turing.MultiTapePTM.iterateWhile`. -/
public abbrev MachineState (State : Type) : Type :=
  ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕
    ((RoundState State ⊕ Unit) ⊕ FinishState)

variable (k) in
/-- Prepare a round: clear the current tape, copy the next word to it and clear the next tape,
using `mark` to flag the left end of words. -/
noncomputable def prepareRound (mark : Bool) : MultiTapeTM (k + 1 + 2) Bool PrepareState :=
  ((clearWork Bool).extendTapes (tapeEmb (curTape k))).seq
    ((copyWord (copyEmb k) mark).seq ((clearWork Bool).extendTapes (tapeEmb (nextTape k))))

variable (k) in
/-- Finish the iteration: output the current word and clear its tape. -/
noncomputable def finish (mark : Bool) : MultiTapeTM (k + 1 + 2) Bool FinishState :=
  (emitWord (emitEmb k) mark).seq ((clearWork Bool).extendTapes (tapeEmb (curTape k)))

/-- Preparing a round moves the next word `v` to the current tape, replacing `vp`. -/
theorem transformsTapes_prepareRound (mark : Bool) (vp v : List Bool) :
    TransformsTapes (prepareRound k mark) (fun _ ws => ws = words vp v)
      (fun _ _ ws' e => ws' = words v [] ∧ e = [])
      (3 * vp.length + 6 * v.length + 16) (vp.length + 5 * v.length + 3 * (k + 1 + 2) + 17) := by
  have hcur := (transformsTapes_clearWork_tapeEmb (curTape k) vp).imp
    (P' := fun _ ws => ws = words vp v) (Q' := fun _ _ ws' e => ws' = words [] v ∧ e = [])
    (fun _ _ h => by rw [h, words_cur])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_cur], he⟩) le_rfl le_rfl
  have hcopy := (transformsTapes_copyWord (copyEmb k) mark v).imp
    (P' := fun _ ws => ws = words [] v) (Q' := fun _ _ ws' e => ws' = words v v ∧ e = [])
    (fun _ _ h => by subst h; simp)
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, copyEmb_zero, update_words_cur], he⟩) le_rfl le_rfl
  have hnext := (transformsTapes_clearWork_tapeEmb (nextTape k) v).imp
    (P' := fun _ ws => ws = words v v) (Q' := fun _ _ ws' e => ws' = words v [] ∧ e = [])
    (fun _ _ h => by rw [h, words_next])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_next], he⟩) le_rfl le_rfl
  exact (hcur.seq_eq (hcopy.seq_eq hnext)).imp (fun _ _ h => h)
    (fun _ _ _ _ _ ⟨h', he⟩ => ⟨h', by simp [he]⟩) (by omega) (by omega)

/-- Finishing outputs the current word `v` and leaves every tape blank. -/
theorem transformsTapes_finish (mark : Bool) (v : List Bool) :
    TransformsTapes (finish k mark) (fun _ ws => ws = words v [])
      (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = v)
      (5 * v.length + 11) (3 * v.length + 2 * (k + 1 + 2) + 11) := by
  have hemit := (transformsTapes_emitWord (emitEmb k) mark v).imp
    (P' := fun _ ws => ws = words v []) (Q' := fun _ _ ws' e => ws' = words v [] ∧ e = v)
    (fun _ _ h => by subst h; simp) (fun _ _ _ _ h ⟨h', he⟩ => ⟨h'.trans h, he⟩) le_rfl le_rfl
  have hclear := (transformsTapes_clearWork_tapeEmb (curTape k) v).imp
    (P' := fun _ ws => ws = words v []) (Q' := fun _ _ ws' e => ws' = (fun _ => []) ∧ e = [])
    (fun _ _ h => by rw [h, words_cur])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_cur, words_nil_nil], he⟩) le_rfl le_rfl
  exact (hemit.seq_eq hclear).imp (fun _ _ h => h)
    (fun _ _ _ _ _ ⟨h', he⟩ => ⟨h', by simp [he]⟩) (by omega) (by omega)

end IterateWhile

open IterateWhile

/-! ### The machine -/

/-- One round: move the next word to the current tape, then apply `tm` from the current tape to
the next tape, using `mark` to flag the left end of words. -/
public noncomputable def iterateWhileRound (tm : MultiTapePTM k Bool State Operation)
    (mark : Bool) :
    MultiTapePTM (k + 1 + 2) Bool (RoundState State) Operation :=
  (ofDeterministic (prepareRound k mark)).seq (tm.onWords mark)

/-- `tm`, applied repeatedly while its result is non-empty, using `mark` to flag the left end of
words: load the input to the next tape, repeat rounds until the next tape is empty, then output
the current word and clear its tape. -/
public noncomputable def iterateWhile (tm : MultiTapePTM k Bool State Operation) (mark : Bool) :
    MultiTapePTM (k + 1 + 2) Bool (MachineState State) Operation :=
  (ofDeterministic (loadWord Bool (nextTape k))).seq
    ((repeatUntilBlank (nextTape k) (tm.iterateWhileRound mark)).seq
      (ofDeterministic (finish k mark)))

/-- A round moves `v` to the current tape and replaces it on the next tape by the result of
`tm` on `v`, making exactly the oracle calls of `tm`. -/
theorem RunsWords.iterateWhileRound {tm : MultiTapePTM k Bool State Operation} (mark : Bool)
    {vp v : List Bool} {t l : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : tm.ComputesTidily v t program)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w' : List Bool) (s' : OracleState),
      (w', s') ∈ (ProbOracleComp.runWith oracle program
          s).support → w'.length ≤ l) (out₀ : List Bool) :
    (tm.iterateWhileRound mark).RunsWords x (words vp v) out₀
      (3 * vp.length + 6 * v.length + 16 + (t + l + 6)) program (fun v' => words v v')
      (fun _ => []) := by
  have h₁ := RunsWords.of_transformsTapes (Operation := Operation) (x := x) (out₀ := out₀)
    (transformsTapes_prepareRound (k := k) mark vp v) rfl (ws' := words v []) (emitted := [])
    (fun _ _ hQ => hQ)
  have h₂ : (tm.onWords mark).RunsWords x (words v []) (out₀ ++ []) (t + l + 6) program
      (fun v' => words v v') (fun _ => []) := by
    rw [words_nil_next]
    exact h.onWords_of_le mark hl (out₀ ++ [])
  exact h₁.seq_pure_left h₂

namespace IterateWhile

private def liftedStep
    (step : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool))
    (p : List Bool × List Bool) :
    ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool × List Bool) :=
  (fun v' => (p.2, v')) <$> step p.2

private def liftedLast (p : List Bool × List Bool) :
    ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool × List Bool) :=
  pure (p.2, [])

private def liftedInvariant (invariant : ℕ → List Bool → Prop) (L n : ℕ)
    (p : List Bool × List Bool) : Prop := invariant n p.2 ∧ p.1.length ≤ L

omit [DecidableEq Operation] in
private theorem lifted_preserve {r L : ℕ}
    {step : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop)
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w) s).support →
          invariant (n + 1) w' ∧ w' ≠ [])
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    ∀ n < r, ∀ p, liftedInvariant invariant L n p →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (p' : List Bool × List Bool),
        (p', st') ∈ (ProbOracleComp.runWith oracle (liftedStep step p) st).support →
          liftedInvariant invariant L (n + 1) p' ∧ p'.2 ≠ [] := by
  intro n hn p hp _ oracle st st' p' hp'
  simp only [liftedStep, ProbOracleComp.runWith_map, PMF.mem_support_map_iff] at hp'
  obtain ⟨⟨w', st''⟩, hw', heq⟩ := hp'
  rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
  obtain ⟨hinv, hne⟩ := hpreserve n hn p.2 hp.1 _ oracle st st'' w' hw'
  exact ⟨⟨hinv, hlength n hn.le p.2 hp.1⟩, hne⟩

omit [DecidableEq Operation] in
private theorem lifted_final_support {r L : ℕ} {w₀ : List Bool}
    {step : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop) (hbase : invariant 0 w₀)
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w) s).support →
          invariant (n + 1) w' ∧ w' ≠ [])
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState) (p : List Bool × List Bool),
      (p, s') ∈ (ProbOracleComp.runWith oracle
        (OracleComp.iterate r (liftedStep step) ([], w₀) >>= liftedLast) s).support →
        p.2 = [] ∧ p.1.length ≤ L := by
  intro _ oracle s s' p hp
  rw [ProbOracleComp.runWith_bind] at hp
  obtain ⟨⟨mid, s₁⟩, hmid, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  simp only [liftedLast, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hp
  obtain ⟨rfl, -⟩ := hp
  have hmidInv := OracleComp.iterate_invariant (liftedInvariant invariant L)
    (⟨hbase, Nat.zero_le L⟩ : liftedInvariant invariant L 0 ([], w₀))
    (fun n p hn hp p' hp' => by
      obtain ⟨_, oracle', st, st', hp'⟩ := ProbOracleComp.mem_support_iff_exists.mp hp'
      exact (lifted_preserve invariant hpreserve hlength n hn p hp _ oracle' st st' p' hp').1)
    mid (ProbOracleComp.mem_support_of_mem oracle hmid)
  exact ⟨rfl, hlength r le_rfl mid.2 hmidInv.1⟩

private theorem runsWords_liftedRound {tm : MultiTapePTM k Bool State Operation} (mark : Bool)
    {p : List Bool × List Bool} {t L : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : tm.ComputesTidily p.2 t program)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w' : List Bool) (s' : OracleState),
      (w', s') ∈ (ProbOracleComp.runWith oracle program s).support → w'.length ≤ L)
    (hp : p.1.length ≤ L) (hv : p.2.length ≤ L) (out : List Bool) :
    (tm.iterateWhileRound mark).RunsWords x (words p.1 p.2) out (t + 10 * L + 22)
      ((fun v' => (p.2, v')) <$> program) (fun q => words q.1 q.2) (fun _ => []) := by
  have hround := (RunsWords.iterateWhileRound (x := x) mark (vp := p.1) h hl out).of_map
    (fun v' => (p.2, v')) (fun q => words q.1 q.2) (fun _ => [])
  exact hround.mono (by omega)

private theorem runsWords_liftedLast {tm : MultiTapePTM k Bool State Operation} (mark : Bool)
    {p : List Bool × List Bool} {t L : ℕ}
    (h : tm.ComputesTidily p.2 t (pure []))
    (hp : p.1.length ≤ L) (hv : p.2.length ≤ L) (out : List Bool) :
    (tm.iterateWhileRound mark).RunsWords x (words p.1 p.2) out (t + 10 * L + 22)
      (liftedLast p) (fun q => words q.1 q.2) (fun _ => []) := by
  have hround := runsWords_liftedRound (x := x) mark h
    (fun _ _ _ w' _ hw' => by
      simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hw'
      simp [hw'.1]) hp hv out
  simpa only [map_pure, liftedLast] using hround

omit [DecidableEq Operation] in
private theorem liftedLast_stops (p : List Bool × List Bool)
    (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (st st' : OracleState) (p' : List Bool × List Bool)
    (hp' : (p', st') ∈ (ProbOracleComp.runWith oracle (liftedLast p) st).support) :
    words (k := k) p'.1 p'.2 (nextTape k) = [] := by
  simp only [liftedLast, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hp'
  rw [hp'.1]
  exact words_next _ _

end IterateWhile

/-- If `tm` tidily computes `step w` within `t` steps from every word `w` reached after `n < r`
rounds, and the empty word from every word reached after `r` rounds, all these words having length
at most `L`, then `tm.iterateWhile mark` tidily computes `OracleComp.iterate r step`. Each round
makes exactly the oracle calls of `tm` on its word, with the external oracle state left by the
previous round, and no round follows the one producing the empty word. -/
public theorem ComputesTidily.iterateWhile {tm : MultiTapePTM k Bool State Operation} (mark : Bool)
    {r t L : ℕ} {w₀ : List Bool}
    {step : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop) (hbase : invariant 0 w₀)
    (hround : ∀ n < r, ∀ w, invariant n w → tm.ComputesTidily w t (step w))
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w)
            s).support → invariant (n + 1) w' ∧ w' ≠ [])
    (hlast : ∀ w, invariant r w → tm.ComputesTidily w t (pure []))
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    (tm.iterateWhile mark).ComputesTidily w₀ ((r + 1) * (t + 10 * L + 23) + 8 * L + 17)
      (OracleComp.iterate r step w₀) := by
  have hloop (out : List Bool) := RunsWords.repeatUntilBlank (nextTape k)
    (body := tm.iterateWhileRound mark) (x := w₀) (out₀ := out) (words_injective (k := k))
    (step := liftedStep step) (last := liftedLast) (t := t + 10 * L + 22)
    (rounds := r) (s₀ := ([], w₀)) (liftedInvariant invariant L) ⟨hbase, by simp⟩
    (fun n hn p hp => runsWords_liftedRound mark (hround n hn p.2 hp.1)
      (fun _ oracle st w' st' hw' =>
        hlength (n + 1) hn w' (hpreserve n hn p.2 hp.1 _ oracle st st' w' hw').1)
      hp.2 (hlength n hn.le p.2 hp.1) out)
    (fun p hp => runsWords_liftedLast mark (hlast p.2 hp.1)
      hp.2 (hlength r le_rfl p.2 hp.1) out)
    (by simpa only [words_next] using lifted_preserve invariant hpreserve hlength)
    (fun p _ => liftedLast_stops (k := k) p)
  have hinner (out : List Bool) := (hloop out).seq_pure_right
    (second := ofDeterministic (finish k mark)) (t₂ := 5 * L + 11)
    (ws₂ := fun _ _ => []) (emit₂ := fun p => p.1)
    (fun _ _ h => words_injective (congrArg Prod.fst h))
    (fun p _ oracle s s' hp => by
      obtain ⟨hnil, hlen⟩ :=
        lifted_final_support invariant hbase hpreserve hlength _ oracle s s' p hp
      exact (RunsWords.of_transformsTapes (transformsTapes_finish (k := k) mark p.1)
        (congrArg (words p.1) hnil) (ws' := fun _ => []) (emitted := p.1) (fun _ _ hQ => hQ)).mono
        (by omega))
  have hload (out : List Bool) := RunsWords.of_transformsTapes (Operation := Operation) (x := w₀)
    (out₀ := out)
    (transformsTapes_loadWord (nextTape k) w₀) ⟨rfl, rfl⟩ (ws' := words (k := k) [] w₀)
    (emitted := []) (fun _ _ h => ⟨h.1.trans (words_nil_cur w₀).symm, h.2⟩)
  intro out₀
  have hall := ((hload out₀).seq_pure_left (hinner (out₀ ++ []))).of_map Prod.fst
    (fun _ _ => []) id
  have hprogram : Prod.fst <$> (OracleComp.iterate r (liftedStep step) ([], w₀) >>= liftedLast) =
      OracleComp.iterate r step w₀ := by
    calc
      _ = Prod.snd <$> OracleComp.iterate r (liftedStep step) ([], w₀) := by
        simp only [map_bind, liftedLast, map_pure, bind_pure_comp]
      _ = _ :=
        (OracleComp.iterate_map r (liftedStep step) step Prod.snd
          (fun p => by simp only [liftedStep, Functor.map_map, id_map']) ([], w₀)).symm
  rw [hprogram] at hall
  have := hlength 0 (Nat.zero_le _) w₀ hbase
  refine hall.mono ?_
  rw [show (r + 1) * (t + 10 * L + 22 + 1) = (r + 1) * (t + 10 * L + 23) by ring]
  omega

/-- A supplied closed machine satisfying the normal and terminal round certificates uses
workspace independent of the round count. The terminal `hlast` premise has the same per-round
time bound as every normal step. -/
public theorem RunsInSpace.iterateWhile {tm : MultiTapePTM k Bool State Empty} (mark : Bool)
    {r t L : ℕ} {w₀ : List Bool}
    {step : List Bool → ProbOracleComp (fun _ : Empty × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop) (hbase : invariant 0 w₀)
    (hround : ∀ n < r, ∀ w, invariant n w → tm.ComputesTidily w t (step w))
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w)
            s).support → invariant (n + 1) w' ∧ w' ≠ [])
    (hlast : ∀ w, invariant r w → tm.ComputesTidily w t (pure []))
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    (tm.iterateWhile mark).toNTM.RunsInSpace w₀
      ((k + 1 + 2) * (2 * (t + 10 * L + 22) + 1)) := by
  have hbound := runsInSpace_toNTM_seq_repeatUntilBlank
    (first := ofDeterministic (loadWord Bool (nextTape k)))
    (body := tm.iterateWhileRound mark) (lastM := ofDeterministic (finish (k := k) mark))
    (t₁ := 3 * L + 6) (t := t + 10 * L + 22) (t₂ := 5 * L + 11) (rounds := r) (s₀ := ([], w₀))
    (ws := fun q => words q.1 q.2)
    (step := liftedStep step) (last := liftedLast)
    (hfirst := (RunsWords.of_transformsTapes (Operation := Empty) (x := w₀) (out₀ := [])
        (ws₀ := fun _ => []) (transformsTapes_loadWord (nextTape k) w₀) ⟨rfl, rfl⟩
        (ws' := words (k := k) [] w₀) (emitted := [])
        (fun _ _ h => ⟨h.1.trans (words_nil_cur w₀).symm, h.2⟩)).mono (time' := 3 * L + 6)
      (by have := hlength 0 (by omega) w₀ hbase; omega))
    (nextTape k) words_injective (liftedInvariant invariant L) ⟨hbase, Nat.zero_le L⟩
    (fun n hn p hp => runsWords_liftedRound mark (hround n hn p.2 hp.1)
      (fun _ oracle st w' st' hw' =>
        hlength (n + 1) hn w' (hpreserve n hn p.2 hp.1 _ oracle st st' w' hw').1)
      hp.2 (hlength n hn.le p.2 hp.1) [])
    (fun p hp => runsWords_liftedLast mark (hlast p.2 hp.1)
      hp.2 (hlength r le_rfl p.2 hp.1) [])
    (by simpa only [words_next] using lifted_preserve invariant hpreserve hlength)
    (fun p _ => liftedLast_stops (k := k) p)
    (fun _ oracle s s' p hp => by
      obtain ⟨hnil, hlen⟩ :=
        lifted_final_support invariant hbase hpreserve hlength _ oracle s s' p hp
      exact (RunsWords.of_transformsTapes (Operation := Empty)
        (transformsTapes_finish (k := k) mark p.1)
        (hP := congrArg (words p.1) hnil) (hQ := fun _ _ h => h)
        (ws' := fun _ => []) (emitted := p.1)).mono (time' := 5 * L + 11) (by omega))
  exact hbound.mono (by
    have : max (3 * L + 6) (max (t + 10 * L + 22) (5 * L + 11)) = t + 10 * L + 22 := by omega
    rw [this])

end Turing.MultiTapePTM

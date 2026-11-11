/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (graded realization frontend regression tests)

public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
public import CslibFrontierTests.WordRAMRealizationLoop

/-!
# Local-work propagation through `realize`

Opaque method certificates retain their supplied work functions through argument wiring,
staging, sequencing and selected branches. Query-free loops retain their iteration charges,
including when their bodies are captured computations or other query-free loops. Native halving
and its framing/zero-width witnesses are exercised in `WordRAMRealizationWhile`.
-/

public section

namespace CslibFrontierTests.WordRAMRealizeGraded

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.Tests (identityBody)

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := WordEncoding.encode
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode
private abbrev countedWords : (Unit × ℕ) × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode
private abbrev tripleWords : (ℕ × ℕ) × ℕ ↪ (Fin 3 → ℕ) := WordEncoding.encode

-- Static wiring retains the actual word- and memory-dependent grade of an opaque method.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (work : ℕ → Memory.State → ℕ) (hm : Realizes .exact m word word P work) :
    Realizes .exact (fun d : ℕ × ℕ => m d.2) pairWords word
      (fun w d s => P w d.2 s) (fun d s => work d.2 s) := by
  realize
  exact h

-- Argument staging does not absorb a method's unbounded grade into a fixed exchange factor.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (work : ℕ → Memory.State → ℕ) (hm : Realizes .exact m word word P work) :
    Realizes .exact (fun n : ℕ => m (n + 1)) word word
      (fun w n s => Fits w (n + 1) ∧ P w (n + 1) s)
      (fun n s => work (n + 1) s) := by
  realize
  · exact h.1
  · exact h.2

-- The continuation's variable grade is evaluated at the first call's reply and reached memory.
example (first : ℕ → Memory.Prog ℕ) (next : ℕ × ℕ → Memory.Prog ℕ)
    (firstWork : ℕ → Memory.State → ℕ) (nextWork : ℕ × ℕ → Memory.State → ℕ)
    (hFirst : Realizes .exact first word word (fun _ _ _ => True) firstWork)
    (hNext : Realizes .exact next pairWords word (fun _ _ _ => True) nextWork) :
    Realizes .exact (fun n : ℕ => do
      let a ← first n
      next (n, a)) word word (fun _ _ _ => True)
      (fun n s => firstWork n s +
        nextWork (n, (Memory.spec 0).clientResult s (first n))
          ((Memory.spec 0).clientState s (first n))) := by
  realize

-- A concrete write changes the memory consulted by the following opaque method's grade.
example (m : ℕ → Memory.Prog ℕ)
    (hm : Realizes .exact m word word (fun _ _ _ => True) (fun n s => n + s.mem 0)) :
    Realizes .exact (fun d : ℕ × ℕ => do
      Memory.write 0 d.2
      m d.1) pairWords word (fun _ _ _ => True) (fun d _ => d.1 + d.2) := by
  realize

-- Only the selected method contributes work; the larger alternate grade is not charged eagerly.
example (m : ℕ → Memory.Prog ℕ) (work : ℕ → Memory.State → ℕ)
    (hm : Realizes .exact m word word (fun _ _ _ => True) work) :
    Realizes .exact (fun d : ℕ × ℕ => if d.1 < d.2 then m d.1 else m d.2)
      pairWords word (fun _ _ _ => True)
      (fun d s => if d.1 < d.2 then work d.1 s else work d.2 s) := by
  realize

-- Both the source choice and its selected work may use whole-condition classical decidability.
example (m : ℕ → Memory.Prog ℕ) (work : ℕ → Memory.State → ℕ)
    (hm : Realizes .exact m word word (fun _ _ _ => True) work) :
    Realizes .exact
      (fun d : ℕ × ℕ => @ite (Memory.Prog ℕ) (d.1 < d.2)
        (Classical.propDecidable _) (m d.1) (m d.2))
      pairWords word (fun _ _ _ => True)
      (fun d s => @ite ℕ (d.1 < d.2) (Classical.propDecidable _)
        (work d.1 s) (work d.2 s)) := by
  realize

-- Staging a computed operand preserves whole-condition decidability even for zero-work choices.
example : Realizes .exact
    (fun d : ℕ × ℕ => @ite (Memory.Prog ℕ) (d.1 + 1 < d.2)
      (Classical.propDecidable _) (pure d.1) (pure d.2)) pairWords word
    (fun w d _ => Fits w (d.1 + 1)) (fun _ _ => 0) := by
  realize
  exact h

-- The same staged comparison retains the selected opaque grade and its source decidability.
example (m : ℕ → Memory.Prog ℕ) (work : ℕ → Memory.State → ℕ)
    (hm : Realizes .exact m word word (fun _ _ _ => True) work) :
    Realizes .exact
      (fun d : ℕ × ℕ => @ite (Memory.Prog ℕ) (d.1 + 1 < d.2)
        (Classical.propDecidable _) (m d.1) (m d.2)) pairWords word
      (fun w d _ => Fits w (d.1 + 1))
      (fun d s => @ite ℕ (d.1 + 1 < d.2) (Classical.propDecidable _)
        (work d.1 s) (work d.2 s)) := by
  realize
  · exact h
  · split_ifs <;> exact le_rfl

-- Normalizing a non-strict guard transports the selected nonzero grade to the source budget.
example (m : ℕ → Memory.Prog ℕ) (work : ℕ → Memory.State → ℕ)
    (hm : Realizes .exact m word word (fun _ _ _ => True) (fun n s => work n s + 1)) :
    Realizes .exact (fun d : ℕ × ℕ => if d.1 ≤ d.2 then m d.1 else m d.2)
      pairWords word (fun _ _ _ => True)
      (fun d s => if d.1 ≤ d.2 then work d.1 s + 1 else work d.2 s + 1) := by
  realize
  split_ifs <;> first | exact le_rfl | omega

-- A query-free counted loop pays one control unit for every iteration, including identity work.
example : Realizes .exact
    (fun d : (Unit × ℕ) × ℕ => iterate identityBody d.1.1 d.2 d.1.2)
    countedWords word (fun _ _ _ => True)
    (fun d s => iterationWork identityBody (fun _ _ => 0) d.1.1 d.2 d.1.2 s) := by
  realize

-- The pointwise work obligation can be discharged by the source grading's actual arithmetic.
/-- A counted identity loop has one control-work unit per iteration and no memory charge. -/
theorem counted_bound_realizes : Realizes .exact
    (fun d : (Unit × ℕ) × ℕ => iterate identityBody d.1.1 d.2 d.1.2)
    (WordEncoding.encode (α := (Unit × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
    (fun _ _ _ => True) (fun d _ => d.2) := by
  realize
  exact (iterationWork_zero identityBody d.1.1 d.2 d.1.2 s).le

-- The safe entry domain may justify a caller's requested budget; it is not a global inequality.
-- Both fuel and budget are encoded words, while zero is the unchanged initial accumulator.
example : Realizes .exact
    (fun d : ℕ × ℕ => iterate identityBody () d.1 0) pairWords word
    (fun _ d _ => d.1 ≤ d.2) (fun d _ => d.2) := by
  realize
  rw [iterationWork_zero]
  exact h

private def nestedBody (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate identityBody () d.1 d.2

-- A nested counted loop retains the inner grade as the outer body's variable work.
example : Realizes .exact
    (fun d : ℕ × ℕ => iterate nestedBody d.1 d.2 0) pairWords word
    (fun _ _ _ => True)
    (fun d s => iterationWork nestedBody
      (fun d s => iterationWork identityBody (fun _ _ => 0) () d.1 d.2 s) d.1 d.2 0 s) := by
  realize
  apply le_of_eq
  apply iterationWork_congr
  · intro a
    rfl
  · intro a t
    rfl

-- Captured live words remain available in a query-free loop whose explicit environment is Unit.
example : Realizes .exact
    (fun d : ℕ × ℕ => iterate (fun _ : Unit × ℕ => pure d.1) () d.2 d.1)
    pairWords word (fun _ _ _ => True)
    (fun d s => iterationWork (fun _ : Unit × ℕ => pure d.1)
      (fun _ _ => 0) () d.2 d.1 s) := by
  realize

-- A captured call retains nonzero work depending on its capture, accumulator and reached memory.
example (step : (ℕ × ℕ) × ℕ → Memory.Prog ℕ)
    (hStep : Realizes .exact step tripleWords word (fun _ _ _ => True)
      (fun d s => d.1.1 + d.2 + s.mem d.1.2 + 1)) :
    Realizes .exact
      (fun d : (ℕ × ℕ) × ℕ => iterate
        (fun a : Unit × ℕ => step ((d.1.1, d.1.2), a.2)) () d.2 0)
      tripleWords word (fun _ _ _ => True)
      (fun d s => iterationWork
        (fun a : Unit × ℕ => step ((d.1.1, d.1.2), a.2))
        (fun a s => d.1.1 + a.2 + s.mem d.1.2 + 1) () d.2 0 s) := by
  realize

-- Bounded captured calls retain their domain and grade at the original fixed environment.
example (step : (ℕ × ℕ) × ℕ → Memory.Prog ℕ)
    (P : ℕ → (ℕ × ℕ) × ℕ → Memory.State → Prop)
    (work : (ℕ × ℕ) × ℕ → Memory.State → ℕ)
    (hStep : RealizesBounded .exact step tripleWords word P work) :
    RealizesBounded .exact
      (fun d : (ℕ × ℕ) × ℕ => iterate
        (fun a : Unit × ℕ => step ((d.1.1, d.1.2), a.2)) () d.2 0)
      tripleWords word
      (fun w d s => iterationSafe
        (fun a : Unit × ℕ => step ((d.1.1, d.1.2), a.2))
        (fun w a s => P w ((d.1.1, d.1.2), a.2) s) w () d.2 0 s)
      (fun d s => iterationWork
        (fun a : Unit × ℕ => step ((d.1.1, d.1.2), a.2))
        (fun a s => work ((d.1.1, d.1.2), a.2) s) () d.2 0 s) := by
  realize
  exact h

-- Opaque body grades may depend on every reached accumulator and the changed whole memory.
example (step : ℕ × ℕ → Memory.Prog ℕ) (work : ℕ × ℕ → Memory.State → ℕ)
    (hStep : Realizes .exact step pairWords word (fun _ _ _ => True) work) :
    Realizes .exact
      (fun d : (ℕ × ℕ) × ℕ => iterate step d.1.1 d.2 d.1.2)
      tripleWords word (fun _ _ _ => True)
      (fun d s => iterationWork step work d.1.1 d.2 d.1.2 s) := by
  realize
  apply le_of_eq
  apply iterationWork_congr
  · intro a
    rfl
  · intro a t
    rfl

-- Bounded branch/iterate/bind composition retains the selected loop and following call's grade.
example (m : ℕ → Memory.Prog ℕ) (work : ℕ → Memory.State → ℕ)
    (hm : RealizesBounded .exact m word word (fun _ _ _ => True) work) :
    RealizesBounded .exact (fun d : ℕ × ℕ => if d.1 < d.2 then do
      let a ← iterate identityBody () d.1 d.2
      m a
    else m d.1) pairWords word (fun _ _ _ => True)
      (fun d s => if d.1 < d.2 then
        iterationWork identityBody (fun _ _ => 0) () d.1 d.2 s +
          work ((Memory.spec 0).clientResult s (iterate identityBody () d.1 d.2))
            ((Memory.spec 0).clientState s (iterate identityBody () d.1 d.2))
        else work d.1 s) := by
  realize

private def decrement (d : Unit × ℕ) : Memory.Prog ℕ := pure (d.2 - 1)
private def positive (_ : Unit) (n : ℕ) : Prop := 0 < n
private instance (u : Unit) (n : ℕ) : Decidable (positive u n) :=
  inferInstanceAs (Decidable (0 < n))

-- Query-free early exit retains actual executed iteration work, rather than the ghost cutoff.
example : Realizes .exact
    (fun n : ℕ => boundedWhile positive decrement () (n + 5) n) word word
    (fun _ _ _ => True)
    (fun n s => whileWork positive decrement (fun _ _ => 0) () (n + 5) n s) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun n _ => n)
    (fun n _ _ hn hg => by change 0 < n at hg; omega)
    (fun n t _ hg _ => ⟨?_, trivial, ?_⟩) trivial (by omega) hv
  · change 1 ≤ n
    change 0 < n at hg
    omega
  · change n - 1 < n
    change 0 < n at hg
    omega

example : Realizes .standard
    (fun n : ℕ => boundedWhile positive decrement () (n + 5) n) word word
    (fun _ _ _ => True)
    (fun n s => whileWork positive decrement (fun _ _ => 0) () (n + 5) n s) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun n _ => Fits w n) (fun n _ => n)
    (fun n _ _ hn hg => by change 0 < n at hg; omega)
    (fun n t hi hg _ => ⟨?_, ?_, ?_⟩) (hwords 0) (by omega) hv
  · exact hi.of_le (by change 0 < n at hg; omega)
  · exact hi.of_le (Nat.sub_le n 1)
  · change n - 1 < n
    change 0 < n at hg
    omega

example : RealizesBounded .exact
    (fun n : ℕ => boundedWhile positive decrement () (n + 5) n) word word
    (fun _ _ _ => True)
    (fun n s => whileWork positive decrement (fun _ _ => 0) () (n + 5) n s) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun n _ => n)
    (fun n _ _ hn hg => by change 0 < n at hg; omega)
    (fun n t _ hg _ => ⟨?_, trivial, ?_⟩) trivial (by omega) hv
  · change 1 ≤ n
    change 0 < n at hg
    omega
  · change n - 1 < n
    change 0 < n at hg
    omega

-- A local certificate's variable grade cannot disappear merely because the function is opaque.
example (m : ℕ → Memory.Prog ℕ)
    (_hm : Realizes .exact m word word (fun _ _ _ => True) (fun n _ => n)) : True := by
  fail_if_success
    have _ : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
  trivial

-- Its positive counterpart ensures that the rejection is a budget failure, not call matching.
example (m : ℕ → Memory.Prog ℕ)
    (hm : Realizes .exact m word word (fun _ _ _ => True) (fun n _ => n)) :
    Realizes .exact m word word (fun _ _ _ => True) (fun n _ => n) := by
  realize

-- The counted loop's safety is trivial; a zero target grade fails only on unpaid loop control.
example : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun d : (Unit × ℕ) × ℕ => iterate identityBody d.1.1 d.2 d.1.2)
        countedWords word (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
  trivial

end CslibFrontierTests.WordRAMRealizeGraded

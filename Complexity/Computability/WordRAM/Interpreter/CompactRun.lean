/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Interpreter.Compact
import all Complexity.Computability.WordRAM.Interpreter.Compact
import all Complexity.Computability.WordRAM.Interpreter.Run
import all Complexity.Computability.GenericRAM.Simulation.Run
import all Complexity.Computability.GenericRAM.Simulation.Turing

/-!
# Runtime bit execution with actual compaction after every instruction

The approved uniform interpreter is composed with a real default-deleting filter
at initialization and after each executed round. An exact commuting refinement
identifies every resulting prefix with the normalized original native prefix.
Faults/returns still absorb rounds. The resource certificate includes compaction
and all copied state and uses simultaneous prefix maxima, not historical writes.

Scan time and the general interpreter's polynomial workspace overhead persist;
compact state size alone is not a sharp source bit-space theorem.
-/

public section
namespace Cslib.WordRAM.Interpreter
open Cslib.GenericRAM Turing.MultiTapeTM NativeCertificate

/-- Normalize every continuing state of the loop without changing the runtime program. -/
def compactLoop {r : ℕ} (x : Loop r) : Loop r := (x.1, compactResult x.2)

/-- One actual compacting round; this executes filtering, not just a semantic projection. -/
def compactRound {r : ℕ} (x : Loop r) : Loop r := compactLoop (round x)

/-- Normalization respects absorbing fault/return and every real instruction. -/
theorem stepResult_compact {r : ℕ} (w : ℕ)
    (p : GenericRAM.Program Basis.standard.genericModel r)
    (out : FiniteState.Result Basis.standard.genericModel r) :
    compactResult (FiniteState.stepResult w p (compactResult out)) =
      compactResult (FiniteState.stepResult w p out) := by
  cases out with
  | none => rfl
  | some v =>
    cases v with
    | inl s => exact step_compact w p s
    | inr v => rfl

/-- Compaction before a round gives exactly the same normalized result and binding order. -/
theorem compactRound_compactLoop {r : ℕ} (x : Loop r) :
    compactRound (compactLoop x) = compactLoop (round x) := by
  exact congrArg (fun out => (x.1, out)) (stepResult_compact x.1.1 x.1.2.toGeneric x.2)

/-- Every actual compacting prefix is the normalized original prefix, with no trace premise. -/
theorem iterate_compactRound {r : ℕ} (x : Loop r) (n : ℕ) :
    compactRound^[n] (compactLoop x) = compactLoop (round^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, compactRound_compactLoop,
      Function.iterate_succ_apply']

/-- One machine normalizes a complete runtime-program loop state. -/
noncomputable def compactLoopCertificate {r : ℕ} : NativeCertificate
    (compactLoop (r := r)) (loopEncoding r) (loopEncoding r) := by
  let hid : NativeCertificate (id : Loop r → Loop r) (loopEncoding r) (loopEncoding r) :=
    linear (ComputableInO.of_eq fun _ => rfl)
  exact prod (fst hid) (compactResultCertificate.comp (snd hid))

/-- The actual round machine includes the real interpreter and default deletion. -/
noncomputable def compactRoundCertificate {r : ℕ} : NativeCertificate
    (compactRound (r := r)) (loopEncoding r) (loopEncoding r) :=
  compactLoopCertificate.comp roundCertificate

/-- Initialize the loop and really filter its original sparse input, including zero inputs. -/
noncomputable def compactInitialCertificate {r : ℕ} : NativeCertificate
    (fun x : RunInput r => compactLoop (initial x)) (runInputEncoding r) (loopEncoding r) := by
  let hid : NativeCertificate (id : RunInput r → RunInput r)
      (runInputEncoding r) (runInputEncoding r) := linear (ComputableInO.of_eq fun _ => rfl)
  exact compactLoopCertificate.comp
    (prod (fst (snd hid)) (NativeCertificate.some (NativeCertificate.inl (snd (snd hid)) encNat)))

/-- One uniform machine executes the compacting loop, with binary countdown and full prefix
resource charges. In particular zero writes cannot accumulate unrepresented historical bindings. -/
noncomputable def compactClockedCertificate {r : ℕ} : NativeCertificate
    (fun x : RunInput r => compactRound^[x.1] (compactLoop (initial x)))
    (runInputEncoding r) (loopEncoding r) := by
  let hid : NativeCertificate (id : RunInput r → RunInput r)
      (runInputEncoding r) (runInputEncoding r) := linear (ComputableInO.of_eq fun _ => rfl)
  exact iterate (fst hid) compactInitialCertificate compactRoundCertificate

/-- Exact native-prefix refinement of the compacting machine, for every binary clock. -/
theorem compact_run {r : ℕ} (x : RunInput r) :
    (compactRound^[x.1] (compactLoop (initial x))).2 =
      compactResult (FiniteState.run x.2.1.1 x.2.1.2.toGeneric x.1 x.2.2) := by
  rw [iterate_compactRound, initial, iterate_round, ← FiniteState.run_eq_iterate_stepResult]
  rfl

/-- One actual uniform machine returns the compacted native finite outcome. -/
noncomputable def compactRunCertificate {r : ℕ} : NativeCertificate
    (fun x : RunInput r =>
      compactResult (FiniteState.run x.2.1.1 x.2.1.2.toGeneric x.1 x.2.2))
    (runInputEncoding r) (FiniteState.resultEncoding Basis.standard.encoding) :=
  congr (snd compactClockedCertificate) compact_run

/-- Complete normalized loop-state maximum, taken over every executed prefix. -/
noncomputable def compactTrajectoryLength {r : ℕ} (x : RunInput r) : ℕ :=
  maxStateLength (loopEncoding r) compactRound x.1 (compactLoop (initial x))

/-- The compacting implementation's time charges the whole scan at every round, plus binary
control and preparation. No missing efficient-simulator bound is assumed. -/
theorem compactClocked_time {r : ℕ} (x : RunInput r) :
    compactClockedCertificate.time x = (runInputEncoding r x).length +
      compactInitialCertificate.time x + (x.1 + 1) *
        (maxRoundTime compactRoundCertificate x.1 (compactLoop (initial x)) +
          compactTrajectoryLength x + ((encNat x.1).length + 1) ^ 2) := by
  dsimp only [compactClockedCertificate, NativeCertificate.iterate, NativeCertificate.fst,
    NativeCertificate.linear, NativeCertificate.post, compactTrajectoryLength]

/-- Simultaneous workspace uses a maximum over compacted prefixes, never the sum of all
allocated historical cells. The round workspace itself remains explicitly charged. -/
theorem compactClocked_space {r : ℕ} (x : RunInput r) :
    compactClockedCertificate.space x = (runInputEncoding r x).length +
      compactInitialCertificate.space x +
        maxRoundSpace compactRoundCertificate x.1 (compactLoop (initial x)) +
          compactTrajectoryLength x + (encNat x.1).length := by
  dsimp only [compactClockedCertificate, NativeCertificate.iterate, NativeCertificate.fst,
    NativeCertificate.linear, NativeCertificate.post, compactTrajectoryLength]

end Cslib.WordRAM.Interpreter

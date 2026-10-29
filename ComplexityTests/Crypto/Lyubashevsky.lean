/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.SIS.Basic
import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF

/-!
# Tests for SIS, box rejection sampling and Lyubashevsky identification

Short integer solutions and the SIS experiment, the exact box rejection-sampling law, and a
run of Lyubashevsky's protocol over `ZMod 7` with `n = 1`, `m = 2`, `k = 1`, `γ = 2`, `β = 1` and
witness entries bounded by `η = 1`. The block checks honest answers and an abort, runs the
extractor on two conversations with a common commitment, and evaluates the simulator's law.
-/

namespace ComplexityTests.Crypto.Lyubashevsky

open Cslib Cslib.Crypto Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Protocols
  SigmaProtocol Turing.MultiTapeTM
open scoped ENNReal

/-! ### Short integer solutions -/

/-- `(1, 1, -1)` is a short solution for the row `(1, 2, 3)` modulo `7`. -/
example : SIS.IsSolution !![(1 : ZMod 7), 2, 3] 1 ![1, 1, -1] := by decide

/-- The zero vector is never a solution, and the bound is enforced. -/
example : ¬SIS.IsSolution !![(1 : ZMod 7), 2, 3] 1 0 := by decide
example : ¬SIS.IsSolution !![(1 : ZMod 7), 2, 3] 1 ![2, -1, 0] := by decide
example : SIS.IsSolution !![(1 : ZMod 7), 2, 3] 2 ![2, -1, 0] := by decide

/-- Three-bit residues `1` and `7` modulo `8` decode to `1` and `-1`. -/
example : SIS.decode 2 3 [true, false, false, true, true, true] = ![1, -1] := by decide

/-- With no rows, the unit vector is always a solution, so a constant program breaks SIS: the
hypothesis is not vacuous. -/
example : ¬SIS (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => 1) := fun h => by
  have hwin (security : ℕ) : SIS.game (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ _ => pure [true]) security = PMF.pure true := by
    have hsol (A : Matrix (Fin 0) (Fin 1) (ZMod (2 ^ 1))) :
        SIS.IsSolution A 1 (SIS.decode 1 1 [true]) := by
      refine ⟨by decide, by decide, ?_⟩
      funext i
      exact i.elim0
    simp only [SIS.game, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.pure_bind, hsol, decide_true, PMF.bind_const]
  refine not_negligible_const one_ne_zero ?_
  simpa only [hwin, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one] using
    h (fun _ _ => pure [true]) (ComputableInPolyTime.const [true]).isPPTOn

/-! ### Lyubashevsky's protocol

The statement is `A = (1, 2)` and `T = A S = (6)` for the witness `S = (1, -1)ᵀ`. With the
commitment randomness `y = (0, 1)` the commitment is `w = A y = 2`. The challenge `0` gets the
answer `y = (0, 1)` and the challenge `1` gets `y + S = (1, 0)`; both lie in the inner box
`[-1, 1]²`. -/

/-- The public matrix. -/
abbrev A : Matrix (Fin 1) (Fin 2) (ZMod 7) := !![1, 2]

/-- The witness. -/
abbrev S : Matrix (Fin 2) (Fin 1) ℤ := !![1; -1]

/-- The image `T = A S`. -/
abbrev T : Matrix (Fin 1) (Fin 1) (ZMod 7) := !![6]

/-- The protocol with `γ = 2` and `β = 1`. -/
noncomputable abbrev P := lyubashevsky 1 2 1 7 2 1

example : lyubashevskyRelation 1 S (A, T) := by decide

/-- The honest prover's answers to both challenges, for the randomness `(0, 1)`. -/
example : P.respond S (A, T) ![0, 1] ![false] = some ![0, 1] := by decide
example : P.respond S (A, T) ![0, 1] ![true] = some ![1, 0] := by decide

/-- For the randomness `(1, 0)` the challenge `1` would give `(2, -1)`, so the prover aborts. -/
example : P.respond S (A, T) ![1, 0] ![true] = none := by decide

/-- The commitment `2` for the randomness `(0, 1)` is a possible honest commitment. -/
example : ((![2] : Fin 1 → ZMod 7), (![0, 1] : Fin 2 → ℤ)) ∈ (P.commit S (A, T)).support :=
  (PMF.mem_support_map_iff _ _ _).mpr
    ⟨![0, 1], (mem_support_uniformOfFinset_iff _ _).mpr (by decide), by decide⟩

example : P.Accepts (A, T) ![2] ![false] (some ![0, 1]) := by decide
example : P.Accepts (A, T) ![2] ![true] (some ![1, 0]) := by decide
example : ¬P.Accepts (A, T) ![2] ![true] (some ![0, 1]) := by decide
example : ¬P.Accepts (A, T) ![2] ![true] none := by decide

/-- The extractor returns `(-1, 1, 1)`, and `[A | T] (-1, 1, 1) = -1 + 2 + 6 = 0` modulo `7`. -/
example : lyubashevskyExtract 1 2 1 7 (A, T) ![2] ![false] (some ![0, 1]) ![true]
    (some ![1, 0]) = Sum.elim ![-1, 1] ![1] := by
  decide

example : SIS.IsSolution (Matrix.fromCols A T) 2
    (lyubashevskyExtract 1 2 1 7 (A, T) ![2] ![false] (some ![0, 1]) ![true] (some ![1, 0])) :=
  lyubashevsky_specialSoundness (γ := 2) (β := 1) _ _ _ _ _ _ (by decide) (by decide) (by decide)

/-- At the challenge `1`, the prover aborts with probability `1 - (3 / 5) ^ 2 = 16 / 25`. -/
example : P.acceptedTranscript S (A, T) ![true] none = 1 - (3 / 5) ^ 2 := by
  rw [lyubashevsky_acceptedTranscript_none (η := 1) (by norm_num) (by norm_num) (by decide)]
  norm_num

/-- The simulator and the honest prover publish `(w, z) = (2, (1, 0))` at the challenge `1` with
probability `1 / 25`: the answer `(1, 0)` comes from one of the `25` points of `[-2, 2]²`. -/
theorem simulate_apply :
    lyubashevskySimulate 1 2 1 7 2 1 (A, T) ![true] (some (![2], ![1, 0])) = 25⁻¹ := by
  rw [lyubashevskySimulate, PMF.map_apply, tsum_eq_single (some ![1, 0])]
  · rw [ite_eq_left (by decide), boxReject, shiftReject_apply_some (fun _ hz => by
      rw [sub_zero]
      exact intBox_mono (by norm_num) hz), card_intBox, ite_eq_left (by decide)]
    norm_num
  · rintro (_ | z) hz
    · simp
    · rw [ite_eq_right]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, not_and]
      exact fun _ h => hz (congrArg some h.symm)

example : P.acceptedTranscript S (A, T) ![true] (some (![2], ![1, 0])) = 25⁻¹ := by
  have h := (lyubashevsky_nonAbortSpecialHVZK (n := 1) (m := 2) (k := 1) (q := 7) (γ := 2)
    (β := 1) (η := 1) (by norm_num) (by norm_num)).acceptedTranscript_eq S (A, T) (by decide)
    ![true]
  rw [← h]
  exact simulate_apply

end ComplexityTests.Crypto.Lyubashevsky

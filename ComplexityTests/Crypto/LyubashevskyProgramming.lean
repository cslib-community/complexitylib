/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Programming
public import ComplexityTests.Crypto.LyubashevskyRandomOracle

@[expose] public section

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.OracleComp
open Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol ROMSignature
open scoped ENNReal

open LyubashevskyViewTests LyubashevskyRandomOracleTests

namespace LyubashevskyProgrammingTests

noncomputable def program (point : Query) : StateT Cache PMF Digest := fun cache =>
  (PMF.uniformOfFintype Digest).map fun c => (c, (point, c) :: cache)

private theorem program_run (q : Query) (cache : Cache) :
    (program q).run cache =
      (PMF.uniformOfFintype Digest).map (fun c => (c, (q, c) :: cache)) := rfl

private theorem oracle_run (q : Query) (cache : Cache) :
    (oracle Digest q).run cache = memoize (fun _ => PMF.uniformOfFintype Digest) q cache := rfl

/-- Neither handler performs any query when the actual signer is given zero attempts. -/
example (cache : Cache) :
    ((iid (protocol.commit 0 key) 0).bind fun coins =>
      (interpret (oracle Digest) (fiatShamirAbortSign protocol (0, key) () 0 coins)).run
        cache) =
    ((iid (protocol.commit 0 key) 0).bind fun coins =>
      (interpret program (fiatShamirAbortSign protocol (0, key) () 0 coins)).run cache) := by
  simp [iid, fiatShamirAbortSign]

/-- At an empty cache, one actual sampled signing attempt has exactly the same full law. -/
example :
    ((iid (protocol.commit 0 key) 1).bind fun coins =>
      (interpret (oracle Digest)
        (fiatShamirAbortSign protocol (0, key) () 1 coins)).run []) =
    ((iid (protocol.commit 0 key) 1).bind fun coins =>
      (interpret program (fiatShamirAbortSign protocol (0, key) () 1 coins)).run []) := by
  simp [fiatShamirAbortSign, oracle_run, memoize, program_run, PMF.map,
    Function.comp_def]

/-- Programming retains the commitment even when this supported attempt aborts. -/
example :
    (interpret program
      (fiatShamirAbortSign protocol (0, key) () 1 (fun _ => badCoins))).run [] =
    (PMF.uniformOfFintype Digest).map fun c => (none, [(((), 1), c)]) := by
  simp [fiatShamirAbortSign, program_run, PMF.map, respond_bad, badCoins,
    Function.comp_def]

/-- A repeated point is still read after first success: memoization retains one digest. -/
theorem read_repeated_success :
    (interpret (oracle Digest)
      (fiatShamirAbortSign protocol (0, key) () 2 (fun _ => (0, (0 : Fin 2 → ℤ))))).run [] =
    (PMF.uniformOfFintype Digest).map fun c => (some (0, 0), [(((), 0), c)]) := by
  simp [fiatShamirAbortSign, oracle_run, memoize, PMF.map, respond_good,
    Fin.tail, Function.comp_def]

/-- Programming samples again and retains both entries after the first success. The newer
entry can disagree with the earlier digest, which is exactly the collision being charged. -/
theorem program_repeated_success :
    (interpret program
      (fiatShamirAbortSign protocol (0, key) () 2
        (fun _ => (0, (0 : Fin 2 → ℤ))))).run [] = do
      let c₀ ← PMF.uniformOfFintype Digest
      let c₁ ← PMF.uniformOfFintype Digest
      return (some (0, 0), [(((), 0), c₁), (((), 0), c₀)]) := by
  simp [fiatShamirAbortSign, program_run, PMF.map, respond_good,
    Fin.tail, Function.comp_def]

/-- The collision path is supported by the real mask sampler, not an impossible coin tape. -/
example : (fun _ : Fin 2 => (0, (0 : Fin 2 → ℤ))) ∈ (iid (protocol.commit 0 key) 2).support := by
  apply (mem_support_iid_iff _ _).mpr
  intro i
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨0, (mem_support_uniformOfFinset_iff _ _).mpr (zero_mem_intBox 3), ?_⟩
  simp [protocol, lyubashevsky]

/-- Distinct programmed digests after success occur with positive probability. -/
example : 0 < ((interpret program
    (fiatShamirAbortSign protocol (0, key) () 2 (fun _ => (0, (0 : Fin 2 → ℤ))))).run [])
      (some (0, 0), [(((), 0), fun _ => true), (((), 0), fun _ => false)]) := by
  rw [program_repeated_success]
  apply (PMF.apply_pos_iff _ _).mpr
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff]
  exact ⟨fun _ => false, by simp,
    fun _ => true, by simp, rfl⟩

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

abbrev Mat := Matrix (Fin 1) (Fin 8) (ZMod 17)

/-- This client uses the canonical scheme's actual coin law and signing program. -/
noncomputable def signingRun (answer : Query → StateT Cache PMF Digest) := do
  let A ← PMF.uniformOfFintype Mat
  let coins ← (lyubashevskyROMSignature Unit 1 8 1 17 1 3 1 2).signCoins (0, (A, 0)) ()
  let out ← (interpret answer
    ((lyubashevskyROMSignature Unit 1 8 1 17 1 3 1 2).sign (0, (A, 0)) () coins)).run []
  return (A, out)

/-- The actual averaged two-attempt laws have a nontrivial bound, including full caches. -/
example : CloseTo (signingRun (oracle Digest)) (signingRun program) (1 / 10) := by
  have h := (closeTo_lyubashevskySign_program 1 8 1 17 3 1 2 0 (by decide)
    (fun _ => PMF.pure ()) (fun _ => 0) (fun _ _ => 0) (fun _ => ()) (fun _ => [])
    (by intro A h hh; simp)).map (fun out => (out.1, out.2.2))
  have he : (∑ j ∈ Finset.range 2, ((0 + j : ℕ) / (17 : ℝ≥0∞) ^ 1 +
      ENNReal.ofReal (Real.sqrt ((17 : ℝ) ^ 1 / ((2 * 3 + 1 : ℕ) : ℝ) ^ 8) / 2))) ≤
      1 / 10 := by
    have hs : Real.sqrt ((17 : ℝ) / 7 ^ 8) / 2 ≤ 1 / 1000 := by
      have ht : Real.sqrt ((17 : ℝ) / 7 ^ 8) ≤ 1 / 500 :=
        Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      linarith
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.cast_ofNat, pow_one, Nat.reduceMul, Nat.reduceAdd]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    have hz : 0 ≤ Real.sqrt ((17 : ℝ) / 7 ^ 8) / 2 := by positivity
    norm_num only [Nat.reducePow] at hs hz
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_ofReal hz,
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_zero, ENNReal.toReal_ofNat,
      zero_div, zero_add]
    linarith
  have h' := h.mono he
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
    PMF.map_bind, PMF.pure_map] at h'
  unfold signingRun program
  simpa only [lyubashevskyROMSignature, fiatShamirAbort, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind] using h'

end LyubashevskyProgrammingTests

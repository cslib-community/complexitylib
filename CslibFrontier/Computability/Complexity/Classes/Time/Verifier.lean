/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.Time.SampleVerify
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayVerdict
import CslibFrontier.Probability.BitString

/-!
# Nondeterministic time through verifiers, with explicit bounds

This module characterizes `Cslib.Complexity.NTIME enc t` by deterministic verifiers, keeping the
time bound up to constant factors. The polynomial characterization of `NP`
(`Cslib.Complexity.mem_NP_iff_decidableInPolyTime`) loses the degree in both directions. The
two directions here keep it.

* **Guess and verify** (`Cslib.Complexity.setOf_exists_mem_NTIME`). Suppose a verifier `V` is
  computable within time `T (a, w)` on encoded pairs, and a certificate length `ℓ a` is
  computable in unary within time `Tℓ a`. Then the problem
  `{a | ∃ w, w.length = ℓ a ∧ V (a, w) = true}` lies in `NTIME enc t` whenever
  `(enc a).length + Tℓ a + T (a, w)` is within `O(t (enc a).length)` on certificates of that
  length. The certificate length may depend on the instance, not only on its encoded length.
  The machine is the nondeterministic reading of the sample-and-verify machine
  (`Cslib.Complexity.exists_machine_sampleVerify`), a closed fair-coin composition that writes
  `frame (enc a)` followed by `ℓ` ones, replaces the ones by fair coins with the fixed sampler
  `Turing.MultiTapePTM.pairSampler`, and runs the verifier. Its computation paths are exactly the
  coin replays, so it accepts exactly when some certificate is accepted, and every branch halts
  within the clock.
* **Verifiers from nondeterministic time** (`Cslib.Complexity.exists_verifier_of_mem_NTIME`).
  A problem in `NTIME enc t` has a verifier that is computable in linear time on encoded pairs:
  check that the certificate, read as coins of the choice table
  (`Turing.MultiTapeNTM.checkChoices`), replays an accepting computation. Every certificate
  length of at least `c * t (enc a).length + c` works, for a constant `c`.

These are explicit-time forms of the guess-and-verify characterization of nondeterministic
polynomial time [Arora and Barak][AroraBarak09]: the choices of an accepting computation are a
certificate, and a certificate can be guessed and then checked.

## Main results

* `Cslib.Complexity.setOf_exists_mem_NTIME`: guess and verify within explicit time.
* `Cslib.Complexity.exists_verifier_of_mem_NTIME`: a linear-time verifier for a problem in
  `NTIME`, with certificates of every sufficient length.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Guess and verify, within explicit time.** If a verifier `V` is computable within time
`T (a, w)` on encoded pairs, and the certificate length `ℓ a` is computable in unary within time
`Tℓ a`, then the problem of instances with an accepted certificate of that length is in
`NTIME enc t`, provided `(enc a).length + Tℓ a + T (a, w) ≤ C * t (enc a).length + C` for every
certificate `w` of that length. -/
theorem setOf_exists_mem_NTIME {V : α × List Bool → Bool} {ℓ : α → ℕ} {t : ℕ → ℕ}
    {Tℓ Sℓ : α → ℕ} {T S : α × List Bool → ℕ} {C : ℕ}
    (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ)
    (hV : ComputableInO V (encPair enc encBits) encBool T S)
    (ht : ∀ a w, w.length = ℓ a → (enc a).length + Tℓ a + T (a, w) ≤ C * t (enc a).length + C) :
    {a | ∃ w : List Bool, w.length = ℓ a ∧ V (a, w) = true} ∈ NTIME enc t := by
  obtain ⟨c₁, c₂, k, State, hfinite, machine, hmachine⟩ := exists_machine_sampleVerify hℓ hV ht
  refine ⟨c₁, c₂, k, State, hfinite, machine.toNTM, fun a => ?_⟩
  -- the nondeterministic reading accepts exactly when some sampled string is accepted
  have htime : machine.toNTM.RunsInTime (enc a) (c₁ * t (enc a).length + c₂) :=
    machine.runsInTime_toNTM (hmachine a).1
  refine ⟨htime, ?_⟩
  rw [MultiTapeNTM.accepts_iff_exists_time_eq htime,
    machine.exists_computationPath_toNTM_iff (P := fun cfg => cfg.output = [true])]
  set T := c₁ * t (enc a).length + c₂
  have hiff : (∃ final ∈ (ProbComp.eval (machine.runClosedConfigFrom T
      (machine.initialConfig (enc a)))).support, final.tapes.output = [true]) ↔
      [true] ∈ (ProbComp.eval (machine.runClosed T (enc a))).support := by
    rw [MultiTapePTM.runClosed_eq_map, ProbComp.eval_map, PMF.mem_support_map_iff]
  rw [hiff, (hmachine a).2, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨w, hw, hVw⟩
    exact ⟨w, BitString.mem_support_uniformList_iff.mpr hw, by rw [hVw]⟩
  · rintro ⟨w, hw, hVw⟩
    exact ⟨w, BitString.mem_support_uniformList_iff.mp hw, by simpa using hVw⟩

/-- **A linear-time verifier for nondeterministic time.** A problem in `NTIME enc t` has a
verifier computable in linear time on encoded pairs. For a constant `c`, every certificate length
`L ≥ c * t (enc a).length + c` works: `a ∈ A` exactly when some certificate of length `L` is
accepted. The verifier checks that the certificate, read as coins of the choice table, replays an
accepting computation. -/
theorem exists_verifier_of_mem_NTIME {A : Set α} {t : ℕ → ℕ} (hA : A ∈ NTIME enc t) :
    ∃ (V : α × List Bool → Bool) (c : ℕ),
      ComputableInO V (encPair enc encBits) encBool (fun p => (encPair enc encBits p).length)
        (fun p => (encPair enc encBits p).length) ∧
      ∀ a L, c * t (enc a).length + c ≤ L →
        (a ∈ A ↔ ∃ w : List Bool, w.length = L ∧ V (a, w) = true) := by
  obtain ⟨c₁, c₂, k, State, hfinite, ntm, hdec⟩ := hA
  set M := Nat.card (Turing.Action k Bool State)
  refine ⟨ntm.checkChoices enc, M * (c₁ + c₂), ?_, fun a L hL =>
    hdec.mem_iff_exists_checkChoices ?_⟩
  · -- replay the certificate with the choice table, then compare the output with `[true]`
    exact MultiTapePTM.computableInO_decide_runClosedCoins ntm.choiceTable
  · have hmul : M * (c₁ * t (enc a).length + c₂) ≤
        M * (c₁ + c₂) * t (enc a).length + M * (c₁ + c₂) := by
      rw [Nat.mul_assoc, ← Nat.mul_add]
      exact Nat.mul_le_mul_left M (by nlinarith)
    exact hmul.trans hL

end Cslib.Complexity

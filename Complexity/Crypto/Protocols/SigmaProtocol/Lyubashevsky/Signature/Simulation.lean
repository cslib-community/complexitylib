/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game.CloseTo.RandomOracle
public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Commitment
public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.RandomOracle

/-!
# One-attempt simulation through a visible oracle continuation

The counterfactual continuation on an abort starts from the original cache and sees neither
fresh mask nor hidden challenge. Its transcript is sampled before the independent mask in the
cache-hit bound. The comparison observes only outputs, not the different private caches.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF OracleComp ROMSignature Interactive
open scoped _root_.Matrix ENNReal

private theorem counterfactual_hit_le {Ω M α : Type} [DecidableEq M]
    (n m k q γ β R : ℕ) [Fact q.Prime] (hγ : 2 * γ < q)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (next : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α)
    (hnext : ∀ A h, h ∈ (H A).support → IsQueryBounded (next A h) R) :
    (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
      let trace ← (interpret (withTranscript (oracle (BitString k))) (next A h)).run (cache h, [])
      return ((trace.2.2.map
          fun entry : (Σ _ : M × (Fin n → ZMod q), BitString k) => (entry.1, entry.2)).lookup
            (msg h, coin.1)).isSome) true ≤
    R / (q : ℝ≥0∞) ^ n +
      ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2) := by
  classical
  let history := fun A => do
    let h ← H A
    let trace ← (interpret (withTranscript (oracle (BitString k))) (next A h)).run (cache h, [])
    return (h, trace)
  have hlength : ∀ A v, v ∈ (history A).support →
      (v.2.2.2.map
        fun entry : (Σ _ : M × (Fin n → ZMod q), BitString k) => (entry.1, entry.2)).length ≤ R := by
    intro A v hv
    simp only [history, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hv
    obtain ⟨h, hh, trace, ht, rfl⟩ := hv
    simpa only [List.length_map] using
      (hnext A h hh).length_transcript_le (oracle (BitString k)) ht
  have hb := lyubashevsky_commit_lookup_le n m k q γ β R hγ history
    (fun v => S v.1) (fun A v => T A v.1) (fun v => msg v.1)
    (fun v => v.2.2.2.map
      fun entry : (Σ _ : M × (Fin n → ZMod q), BitString k) => (entry.1, entry.2)) hlength
  have horder :
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
        let trace ← (interpret (withTranscript (oracle (BitString k))) (next A h)).run (cache h, [])
        return ((trace.2.2.map
          fun entry : (Σ _ : M × (Fin n → ZMod q), BitString k) => (entry.1, entry.2)).lookup
            (msg h, coin.1)).isSome) =
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let trace ← (interpret (withTranscript (oracle (BitString k))) (next A h)).run (cache h, [])
        let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
        return ((trace.2.2.map
          fun entry : (Σ _ : M × (Fin n → ZMod q), BitString k) => (entry.1, entry.2)).lookup
            (msg h, coin.1)).isSome) := by
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    congr 1
    funext A
    congr 1
    funext h
    exact PMF.bind_comm _ _ _
  rw [horder]
  simpa only [history, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind] using hb

end Cslib.Crypto.Protocols.SigmaProtocol

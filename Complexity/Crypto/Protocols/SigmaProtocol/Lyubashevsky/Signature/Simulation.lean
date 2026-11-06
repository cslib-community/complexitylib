/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game.CloseTo
public import Complexity.Crypto.Game.CloseTo.RandomOracle
public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Commitment
public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.RandomOracle
import Complexity.Probability.PMF.Bind

/-!
# One-attempt simulation through a visible oracle continuation

The counterfactual continuation on an abort starts from the original cache and sees neither
fresh mask nor hidden challenge. Its transcript is sampled before the independent mask in the
cache-hit bound. The comparison observes only outputs, not the different private caches.

The programmed signing experiment `lyubashevskySignVisibleProg` is the one-attempt programmed
hybrid: it draws a fresh challenge and prepends `(message, commitment) ↦ challenge` to the random
oracle cache even on an abort and even if that key was already present. The actual memoizing
`Sign → Prog` transport from honest signing that reuses cached challenges remains a separate
obligation.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySimCache`: updated cache after a simulated
  signing attempt, adding an entry on acceptance and leaving the cache unchanged on abort.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignVisibleProg`: one-attempt programmed signing
  hybrid with attempted-query cache programming and a visible oracle continuation.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignVisibleSim`: simulated signing experiment
  with accepted-transcript caching and a visible oracle continuation.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignFullProg`: full execution of the programmed
  signing hybrid retaining the final cache.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignFullSim`: full execution of the simulated
  signing experiment retaining the final cache.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.closeTo_lyubashevskySign_simulate`: one-attempt simulation
  bridge bounding the statistical distance between the programmed signing hybrid and simulated
  signing with accepted-transcript caching under any bounded visible continuation.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignVisibleProg_eq_sim_of_pure`: exact visible
  output agreement when the continuation makes zero oracle queries.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignVisibleProg_eq_map_full`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignVisibleSim_eq_map_full`: visible experiments
  are the first projections of full executions.

## References

* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF OracleComp ROMSignature Interactive RandomOracle Crypto.Game
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
  let entryToPair : (Σ _ : M × (Fin n → ZMod q), BitString k) →
      (M × (Fin n → ZMod q)) × BitString k :=
    fun entry => (entry.1, entry.2)
  let history := fun A => do
    let h ← H A
    let trace ← (interpret (withTranscript (oracle (BitString k))) (next A h)).run (cache h, [])
    return (h, trace)
  have hlength : ∀ A v, v ∈ (history A).support →
      (v.2.2.2.map entryToPair).length ≤ R := by
    intro A v hv
    simp only [history, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hv
    obtain ⟨h, hh, trace, ht, rfl⟩ := hv
    simpa only [List.length_map] using
      (hnext A h hh).length_transcript_le (oracle (BitString k)) ht
  have hb := lyubashevsky_commit_lookup_le n m k q γ β R hγ history
    (fun v => S v.1) (fun A v => T A v.1) (fun v => msg v.1)
    (fun v => v.2.2.2.map entryToPair) hlength
  have horder :
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
        let trace ← (interpret (withTranscript (oracle (BitString k))) (next A h)).run (cache h, [])
        return ((trace.2.2.map entryToPair).lookup (msg h, coin.1)).isSome) =
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let trace ← (interpret (withTranscript (oracle (BitString k))) (next A h)).run (cache h, [])
        let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
        return ((trace.2.2.map entryToPair).lookup (msg h, coin.1)).isSome) := by
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    congr 1
    funext A
    congr 1
    funext h
    exact PMF.bind_comm _ _ _
  rw [horder]
  simpa only [history, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind] using hb

/-- Update the random oracle cache after a simulated signing attempt. On an accepted transcript
`(t, z)`, the commitment-challenge pair `((msg, t), c)` is prepended to the cache; on an abort,
the cache is left unchanged. -/
@[expose] def lyubashevskySimCache {M T Z C : Type} (msg : M) (c : C) (cache : List ((M × T) × C)) :
    Option (T × Z) → List ((M × T) × C)
  | some (t, _) => ((msg, t), c) :: cache
  | none => cache

@[simp] theorem lyubashevskySimCache_none {M T Z C : Type} (msg : M) (c : C)
    (cache : List ((M × T) × C)) :
    lyubashevskySimCache msg c cache (none : Option (T × Z)) = cache := rfl

@[simp] theorem lyubashevskySimCache_some {M T Z C : Type} (msg : M) (c : C)
    (cache : List ((M × T) × C)) (t : T) (z : Z) :
    lyubashevskySimCache msg c cache (some (t, z)) = ((msg, t), c) :: cache := rfl

theorem lyubashevskySimCache_eq_nil_iff {M T Z C : Type} (msg : M) (c : C)
    (cache : List ((M × T) × C)) (view : Option (T × Z)) :
    lyubashevskySimCache msg c cache view = [] ↔ cache = [] ∧ view = none := by
  cases view <;> simp [lyubashevskySimCache]

private theorem hybrid_eq_simulate {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β : ℕ) [Fact q.Prime] (hβ : β ≤ γ) (hη : k * η ≤ β)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (hvalid : ∀ A h, h ∈ (H A).support → lyubashevskyRelation η (S h) (A, T A h))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
      let c ← PMF.uniformOfFintype (BitString k)
      let sig := ((lyubashevsky n m k q γ β).respond (S h) (A, T A h) coin.2 c).map
        fun z => (coin.1, z)
      let out ← (interpret (oracle (BitString k)) (cont A h sig)).run
        (lyubashevskySimCache (msg h) c (cache h) sig)
      return (A, h, out.1)) =
    (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let c ← PMF.uniformOfFintype (BitString k)
      let view ← lyubashevskySimulate n m k q γ β (A, T A h) c
      let out ← (interpret (oracle (BitString k)) (cont A h view)).run
        (lyubashevskySimCache (msg h) c (cache h) view)
      return (A, h, out.1)) := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  congr 1
  funext A
  refine PMF.bind_congr_on_support (H A) _ _ fun h hh => ?_
  rw [PMF.bind_comm]
  congr 1
  funext c
  have heq := (lyubashevsky_nonAbortSpecialHVZK (n := n) (m := m) (k := k) (q := q)
    (γ := γ) (β := β) hβ hη).acceptedTranscript_eq (S h) (A, T A h) (hvalid A h hh) c
  rw [heq]
  simp only [acceptedTranscript, transcript, PMF.bind_map, Function.comp_def]

private theorem outerMeasure_entry_le_lookup_isSome {M α : Type} [DecidableEq M]
    {n k q : ℕ}
    (μ : PMF (α × List ((M × (Fin n → ZMod q)) × BitString k) ×
      List (Σ _ : M × (Fin n → ZMod q), BitString k)))
    (target : M × (Fin n → ZMod q)) :
    μ.toOuterMeasure
      {out : α × List ((M × (Fin n → ZMod q)) × BitString k) ×
        List (Σ _ : M × (Fin n → ZMod q), BitString k) | ∃ entry ∈ out.2.2, entry.1 = target} ≤
      (μ.map fun (trace : α × List ((M × (Fin n → ZMod q)) × BitString k) ×
        List (Σ _ : M × (Fin n → ZMod q), BitString k)) =>
        ((trace.2.2.map
          (fun entry : Σ _ : M × (Fin n → ZMod q), BitString k => (entry.1, entry.2))).lookup
            target).isSome) true := by
  have hsub :
      {out : α × List ((M × (Fin n → ZMod q)) × BitString k) ×
        List (Σ _ : M × (Fin n → ZMod q), BitString k) | ∃ entry ∈ out.2.2, entry.1 = target} ⊆
      (fun trace : α × List ((M × (Fin n → ZMod q)) × BitString k) ×
        List (Σ _ : M × (Fin n → ZMod q), BitString k) =>
        ((trace.2.2.map
          (fun entry : Σ _ : M × (Fin n → ZMod q), BitString k => (entry.1, entry.2))).lookup
            target).isSome) ⁻¹' {true} := by
    intro out hout
    obtain ⟨entry, hentry, heq⟩ := hout
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [List.lookup_isSome_iff]
    refine ⟨(entry.1, entry.2), List.mem_map.mpr ⟨entry, hentry, rfl⟩, ?_⟩
    change (target == entry.1) = true
    rw [heq, beq_self_eq_true]
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  exact μ.toOuterMeasure.mono hsub

/-- The one-attempt programmed signing hybrid with attempted-query cache programming
and a visible oracle continuation. Note: this programs the cache by prepending `(msg, t) ↦ c`
even on an abort; the transport from honest memoizing signing (`Sign → Prog`) is a separate
obligation. -/
noncomputable def lyubashevskySignVisibleProg {Ω M α : Type} [DecidableEq M]
    (n m k q γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω × α) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
  let h ← H A
  let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
  let c ← PMF.uniformOfFintype (BitString k)
  let sig := ((lyubashevsky n m k q γ β).respond (S h) (A, T A h) coin.2 c).map
    fun z => (coin.1, z)
  let out ← (interpret (oracle (BitString k)) (cont A h sig)).run
    (((msg h, coin.1), c) :: cache h)
  return (A, h, out.1)

/-- The simulated signing experiment with accepted-transcript caching
and a visible oracle continuation. -/
noncomputable def lyubashevskySignVisibleSim {Ω M α : Type} [DecidableEq M]
    (n m k q γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω × α) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
  let h ← H A
  let c ← PMF.uniformOfFintype (BitString k)
  let view ← lyubashevskySimulate n m k q γ β (A, T A h) c
  let out ← (interpret (oracle (BitString k)) (cont A h view)).run
    (lyubashevskySimCache (msg h) c (cache h) view)
  return (A, h, out.1)

/-- Full execution of the programmed signing hybrid, returning public matrix `A`, secret context
`h`, optional signature `sig`, and final random oracle cache. -/
@[expose] noncomputable def lyubashevskySignFullProg {Ω M : Type}
    (n m k q γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k)) :
    PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) ×
      List ((M × (Fin n → ZMod q)) × BitString k)) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
  let h ← H A
  let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
  let c ← PMF.uniformOfFintype (BitString k)
  let sig := ((lyubashevsky n m k q γ β).respond (S h) (A, T A h) coin.2 c).map
    fun z => (coin.1, z)
  return (A, h, sig, ((msg h, coin.1), c) :: cache h)

/-- Full execution of the simulated signing experiment, returning public matrix `A`, secret
context `h`, simulated transcript `view`, and updated random oracle cache. -/
@[expose] noncomputable def lyubashevskySignFullSim {Ω M : Type}
    (n m k q γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k)) :
    PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) ×
      List ((M × (Fin n → ZMod q)) × BitString k)) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
  let h ← H A
  let c ← PMF.uniformOfFintype (BitString k)
  let view ← lyubashevskySimulate n m k q γ β (A, T A h) c
  return (A, h, view, lyubashevskySimCache (msg h) c (cache h) view)

theorem lyubashevskySignVisibleProg_eq_pure {Ω M α : Type} [DecidableEq M]
    (n m k q : ℕ) [NeZero q] (γ β : ℕ)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (f : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Option ((Fin n → ZMod q) × (Fin m → ℤ)) → α) :
    lyubashevskySignVisibleProg n m k q γ β H S T msg cache (fun A h sig => pure (f A h sig)) =
    do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
      let c ← PMF.uniformOfFintype (BitString k)
      let sig := ((lyubashevsky n m k q γ β).respond (S h) (A, T A h) coin.2 c).map
        fun z => (coin.1, z)
      return (A, h, f A h sig) := by
  simp only [lyubashevskySignVisibleProg, interpret_pure, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]

theorem lyubashevskySignVisibleSim_eq_pure {Ω M α : Type} [DecidableEq M]
    (n m k q : ℕ) [NeZero q] (γ β : ℕ)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (f : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Option ((Fin n → ZMod q) × (Fin m → ℤ)) → α) :
    lyubashevskySignVisibleSim n m k q γ β H T msg cache (fun A h sig => pure (f A h sig)) =
    do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let c ← PMF.uniformOfFintype (BitString k)
      let view ← lyubashevskySimulate n m k q γ β (A, T A h) c
      return (A, h, f A h view) := by
  simp only [lyubashevskySignVisibleSim, interpret_pure, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]

@[simp] theorem lyubashevskySignVisibleProg_eq_map_full {Ω M : Type} [DecidableEq M]
    (n m k q γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k)) :
    lyubashevskySignVisibleProg n m k q γ β H S T msg cache (fun _ _ sig => pure sig) =
      (lyubashevskySignFullProg n m k q γ β H S T msg cache).map
        fun (A, h, sig, _) => (A, h, sig) := by
  simp only [lyubashevskySignVisibleProg_eq_pure, lyubashevskySignFullProg, PMF.map,
    Function.comp_def, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]

@[simp] theorem lyubashevskySignVisibleSim_eq_map_full {Ω M : Type} [DecidableEq M]
    (n m k q γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k)) :
    lyubashevskySignVisibleSim n m k q γ β H T msg cache (fun _ _ view => pure view) =
      (lyubashevskySignFullSim n m k q γ β H T msg cache).map
        fun (A, h, view, _) => (A, h, view) := by
  simp only [lyubashevskySignVisibleSim_eq_pure, lyubashevskySignFullSim, PMF.map,
    Function.comp_def, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]

/-- When the continuation makes zero oracle queries, the visible output of the programmed
signing hybrid and that of the simulated transcript are identically distributed. -/
public theorem lyubashevskySignVisibleProg_eq_sim_of_pure {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β : ℕ) [Fact q.Prime] (hβ : β ≤ γ) (hη : k * η ≤ β)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (hvalid : ∀ A h, h ∈ (H A).support → lyubashevskyRelation η (S h) (A, T A h))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (f : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) → α) :
    lyubashevskySignVisibleProg n m k q γ β H S T msg cache (fun A h sig => pure (f A h sig)) =
      lyubashevskySignVisibleSim n m k q γ β H T msg cache (fun A h sig => pure (f A h sig)) := by
  rw [lyubashevskySignVisibleProg_eq_pure, lyubashevskySignVisibleSim_eq_pure]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  congr 1
  funext A
  refine PMF.bind_congr_on_support (H A) _ _ fun h hh => ?_
  rw [PMF.bind_comm]
  congr 1
  funext c
  have heq := (lyubashevsky_nonAbortSpecialHVZK (n := n) (m := m) (k := k) (q := q)
    (γ := γ) (β := β) hβ hη).acceptedTranscript_eq (S h) (A, T A h) (hvalid A h hh) c
  rw [heq]
  simp only [acceptedTranscript, transcript, PMF.bind_map, Function.comp_def]

/-- One-attempt signing simulation through a visible oracle continuation:
the visible output of the one-attempt programmed signing hybrid
and of the simulated transcript differ by at most the unconditioned commitment collision bound. -/
public theorem closeTo_lyubashevskySign_simulate {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β R : ℕ) [Fact q.Prime] (hγ : 2 * γ < q) (hβ : β ≤ γ) (hη : k * η ≤ β)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (hvalid : ∀ A h, h ∈ (H A).support → lyubashevskyRelation η (S h) (A, T A h))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α)
    (hcont : ∀ A h sig, h ∈ (H A).support → IsQueryBounded (cont A h sig) R) :
    CloseTo
      (lyubashevskySignVisibleProg n m k q γ β H S T msg cache cont)
      (lyubashevskySignVisibleSim n m k q γ β H T msg cache cont)
      (R / (q : ℝ≥0∞) ^ n +
        ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2)) := by
  classical
  have hsim := hybrid_eq_simulate (n := n) (m := m) (k := k) (q := q) (η := η) (γ := γ) (β := β)
    hβ hη H S T hvalid msg cache cont
  let src : PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      ((Fin n → ZMod q) × (Fin m → ℤ)) × BitString k) := do
    let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
    let h ← H A
    let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
    let c ← PMF.uniformOfFintype (BitString k)
    return (A, h, coin, c)
  let f : Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      ((Fin n → ZMod q) × (Fin m → ℤ)) × BitString k →
      PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω × α) := fun a =>
    let sig := ((lyubashevsky n m k q γ β).respond (S a.2.1) (a.1, T a.1 a.2.1)
      a.2.2.1.2 a.2.2.2).map fun z => (a.2.2.1.1, z)
    ((interpret (oracle (BitString k)) (cont a.1 a.2.1 sig)).run
      (((msg a.2.1, a.2.2.1.1), a.2.2.2) :: cache a.2.1)).map
        fun out => (a.1, a.2.1, out.1)
  let g : Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      ((Fin n → ZMod q) × (Fin m → ℤ)) × BitString k →
      PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω × α) := fun a =>
    let sig := ((lyubashevsky n m k q γ β).respond (S a.2.1) (a.1, T a.1 a.2.1)
      a.2.2.1.2 a.2.2.2).map fun z => (a.2.2.1.1, z)
    ((interpret (oracle (BitString k)) (cont a.1 a.2.1 sig)).run
      (lyubashevskySimCache (msg a.2.1) a.2.2.2 (cache a.2.1) sig)).map
        fun out => (a.1, a.2.1, out.1)
  let entryToPair : (Σ _ : M × (Fin n → ZMod q), BitString k) →
      (M × (Fin n → ZMod q)) × BitString k :=
    fun entry => (entry.1, entry.2)
  let err : Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      ((Fin n → ZMod q) × (Fin m → ℤ)) × BitString k → PMF Bool := fun a =>
    (((interpret (withTranscript (oracle (BitString k)))
      (cont a.1 a.2.1 none)).run (cache a.2.1, [])).map
        fun trace => ((trace.2.2.map entryToPair).lookup
          (msg a.2.1, a.2.2.1.1)).isSome)
  have hc : CloseTo (src.bind f) (src.bind g) ((src.bind err) true) := by
    apply closeTo_bind_of_le
    intro a ha test
    cases hsig : (lyubashevsky n m k q γ β).respond (S a.2.1) (a.1, T a.1 a.2.1)
      a.2.2.1.2 a.2.2.2 with
    | some z =>
      have heq : f a = g a := by
        dsimp only [f, g]
        simp only [hsig, Option.map_some, lyubashevskySimCache_some]
      rw [heq]
      exact ⟨le_add_right le_rfl, le_add_right le_rfl⟩
    | none =>
      have hclose : CloseTo (f a) (g a) (err a true) := by
        dsimp only [f, g]
        simp only [hsig, Option.map_none, lyubashevskySimCache_none]
        have hmemo := closeTo_run_interpret_memoize_cons
          (fun _ : M × (Fin n → ZMod q) => PMF.uniformOfFintype (BitString k))
          (msg a.2.1, a.2.2.1.1) a.2.2.2 (cont a.1 a.2.1 none) (cache a.2.1)
        have hpost := hmemo.map (fun out1 => (a.1, a.2.1, out1))
        simp only [PMF.map_comp, Function.comp_def] at hpost
        refine hpost.mono ?_
        exact outerMeasure_entry_le_lookup_isSome _ _
      constructor
      · simpa only [PMF.toOuterMeasure_apply_singleton] using (hclose.map test) {true}
      · simpa only [PMF.toOuterMeasure_apply_singleton] using (hclose.map test).symm {true}
  have hbound : (src.bind err) true ≤
      R / (q : ℝ≥0∞) ^ n +
        ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2) := by
    have hsrc : (src.bind err) =
        (do
          let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
          let h ← H A
          let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
          let trace ← (interpret (withTranscript (oracle (BitString k)))
            (cont A h none)).run (cache h, [])
          return ((trace.2.2.map entryToPair).lookup (msg h, coin.1)).isSome) := by
      simp only [src, err, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.map]
      congr 1
      funext A
      congr 1
      funext h
      congr 1
      funext coin
      rw [PMF.bind_const]; rfl
    rw [hsrc]
    exact counterfactual_hit_le n m k q γ β R hγ H S T msg cache
      (fun A h => cont A h none) (fun A h hh => hcont A h none hh)
  have hprog : lyubashevskySignVisibleProg n m k q γ β H S T msg cache cont = src.bind f := by
    simp only [lyubashevskySignVisibleProg, src, f, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]
  have hhyb :
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
        let c ← PMF.uniformOfFintype (BitString k)
        let sig := ((lyubashevsky n m k q γ β).respond (S h) (A, T A h) coin.2 c).map
          fun z => (coin.1, z)
        let out ← (interpret (oracle (BitString k)) (cont A h sig)).run
          (lyubashevskySimCache (msg h) c (cache h) sig)
        return (A, h, out.1)) = src.bind g := by
    simp only [src, g, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]
  have htrans : lyubashevskySignVisibleSim n m k q γ β H T msg cache cont = src.bind g :=
    hsim.symm.trans hhyb
  exact hprog.symm ▸ htrans.symm ▸ (hc.mono hbound)

/-- Simulating all `K` signing attempts without the secret key.
Each attempt samples a uniform challenge and runs `lyubashevskySimulate`.
On the first non-abort transcript, it prepends that accepted transcript to the cache and halts.
If all `K` attempts abort, it returns `none` with the unmodified cache. -/
noncomputable def lyubashevskySimAttempts {M : Type} (n m k q γ β : ℕ) [NeZero q]
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (T : Matrix (Fin n) (Fin k) (ZMod q)) (msg : M) :
    (K : ℕ) → List ((M × (Fin n → ZMod q)) × BitString k) →
    PMF (Option ((Fin n → ZMod q) × (Fin m → ℤ)) × List ((M × (Fin n → ZMod q)) × BitString k))
  | 0, cache => pure (none, cache)
  | K + 1, cache => do
      let c ← PMF.uniformOfFintype (BitString k)
      let view ← lyubashevskySimulate n m k q γ β (A, T) c
      match view with
      | some sig => pure (some sig, ((msg, sig.1), c) :: cache)
      | none => lyubashevskySimAttempts n m k q γ β A T msg K cache

/-- The all-`K` programmed signing hybrid under a query-bounded visible continuation.
It executes `K` signing attempts with fresh uniform challenges programmed into the random oracle,
prepending each attempted hash point even on abort, and returns the first success (or `none`).
The continuation `cont` receives the optional signature and runs with the resulting cache. -/
noncomputable def lyubashevskySignAttemptsVisibleProg {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β K : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω × α) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
  let h ← H A
  let out ← (iid ((lyubashevsky n m k q γ β).commit (S h) (A, T A h)) K).bind fun coins =>
    (interpret (m := StateT (List ((M × (Fin n → ZMod q)) × BitString k)) PMF)
      (fun point curCache => (PMF.uniformOfFintype (BitString k)).map
        fun c => (c, (point, c) :: curCache))
      (fiatShamirAbortSign (lyubashevsky n m k q γ β) (lyubashevskyKeyGen n m k q η)
        (S h, (A, T A h)) (msg h) K coins)).run (cache h)
  let res ← (interpret (oracle (BitString k)) (cont A h out.1)).run out.2
  return (A, h, res.1)

/-- The all-`K` simulated signing algorithm under a query-bounded visible continuation.
It simulates up to `K` attempts using `lyubashevskySimulate`, caching only accepted transcripts.
The continuation `cont` receives the optional simulated signature and runs with the resulting
cache. -/
noncomputable def lyubashevskySignAttemptsVisibleSim {Ω M α : Type} [DecidableEq M]
    (n m k q γ β K : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω × α) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
  let h ← H A
  let out ← lyubashevskySimAttempts n m k q γ β A (T A h) (msg h) K (cache h)
  let res ← (interpret (oracle (BitString k)) (cont A h out.1)).run out.2
  return (A, h, res.1)

/-- With zero attempts, the programmed hybrid and simulation are identically distributed. -/
theorem lyubashevskySignAttemptsVisibleProg_zero_eq_sim {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    lyubashevskySignAttemptsVisibleProg n m k q η γ β 0 H S T msg cache cont =
    lyubashevskySignAttemptsVisibleSim n m k q γ β 0 H T msg cache cont := by
  dsimp only [lyubashevskySignAttemptsVisibleProg, lyubashevskySignAttemptsVisibleSim]
  simp only [iid, fiatShamirAbortSign, run_interpret_pure,
    lyubashevskySimAttempts, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
    PMF.pure_bind]

/-- Simulating one attempt agrees with the single-attempt visible simulator. -/
theorem lyubashevskySignAttemptsVisibleSim_one_eq {Ω M α : Type} [DecidableEq M]
    (n m k q γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    lyubashevskySignAttemptsVisibleSim n m k q γ β 1 H T msg cache cont =
    lyubashevskySignVisibleSim n m k q γ β H T msg cache cont := by
  dsimp only [lyubashevskySignAttemptsVisibleSim, lyubashevskySignVisibleSim]
  congr 1
  funext A
  congr 1
  funext h
  dsimp only [lyubashevskySimAttempts]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind]
  congr 1
  funext c
  congr 1
  funext view
  rcases view with _ | ⟨u, z⟩
  · simp only [PMF.pure_bind, lyubashevskySimCache_none]
  · simp only [PMF.pure_bind, lyubashevskySimCache_some]

/-- The one-attempt programmed hybrid agrees with the single-attempt programmed signer. -/
theorem lyubashevskySignAttemptsVisibleProg_one_eq {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    lyubashevskySignAttemptsVisibleProg n m k q η γ β 1 H S T msg cache cont =
    lyubashevskySignVisibleProg n m k q γ β H S T msg cache cont := by
  dsimp only [lyubashevskySignAttemptsVisibleProg, lyubashevskySignVisibleProg]
  congr 1
  funext A
  congr 1
  funext h
  rw [show (1 : ℕ) = 0 + 1 from rfl, fiatShamirAbortSign_run_succ]
  simp only [iid, fiatShamirAbortSign, interpret_pure, StateT.run_pure,
    PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.pure_bind,
    PMF.map, Function.comp_def, PMF.bind_bind]
  simp only [fiatShamir, Function.Embedding.refl_apply, interpret_map, interpret_query,
    StateT.run_map, PMF.monad_map_eq_map, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def]
  simp only [StateT.run, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext coin
  congr 1
  funext c
  cases (lyubashevsky n m k q γ β).respond (S h) (A, T A h) coin.2 c <;> rfl

theorem lyubashevskySignAttemptsVisibleProg_eq_pure {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β K : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (f : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Option ((Fin n → ZMod q) × (Fin m → ℤ)) → α) :
    lyubashevskySignAttemptsVisibleProg n m k q η γ β K H S T msg cache
        (fun A h sig => pure (f A h sig)) =
      do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let out ← (iid ((lyubashevsky n m k q γ β).commit (S h) (A, T A h)) K).bind fun coins =>
          (interpret (m := StateT (List ((M × (Fin n → ZMod q)) × BitString k)) PMF)
            (fun point curCache => (PMF.uniformOfFintype (BitString k)).map
              fun c => (c, (point, c) :: curCache))
            (fiatShamirAbortSign (lyubashevsky n m k q γ β) (lyubashevskyKeyGen n m k q η)
              (S h, (A, T A h)) (msg h) K coins)).run (cache h)
        return (A, h, f A h out.1) := by
  simp only [lyubashevskySignAttemptsVisibleProg, interpret_pure, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]

theorem lyubashevskySignAttemptsVisibleSim_eq_pure {Ω M α : Type} [DecidableEq M]
    (n m k q γ β K : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (f : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Option ((Fin n → ZMod q) × (Fin m → ℤ)) → α) :
    lyubashevskySignAttemptsVisibleSim n m k q γ β K H T msg cache
        (fun A h sig => pure (f A h sig)) =
      do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let out ← lyubashevskySimAttempts n m k q γ β A (T A h) (msg h) K (cache h)
        return (A, h, f A h out.1) := by
  simp only [lyubashevskySignAttemptsVisibleSim, interpret_pure, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]

/-- For one attempt, the all-attempt simulation bridge recovers the single-attempt bridge. -/
public theorem closeTo_lyubashevskySignAttempts_simulate_one
    {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β R : ℕ) [Fact q.Prime] (hγ : 2 * γ < q) (hβ : β ≤ γ) (hη : k * η ≤ β)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (hvalid : ∀ A h, h ∈ (H A).support → lyubashevskyRelation η (S h) (A, T A h))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α)
    (hcont : ∀ A h sig, h ∈ (H A).support → IsQueryBounded (cont A h sig) R) :
    CloseTo
      (lyubashevskySignAttemptsVisibleProg n m k q η γ β 1 H S T msg cache cont)
      (lyubashevskySignAttemptsVisibleSim n m k q γ β 1 H T msg cache cont)
      (R / (q : ℝ≥0∞) ^ n +
        ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2)) := by
  rw [lyubashevskySignAttemptsVisibleProg_one_eq, lyubashevskySignAttemptsVisibleSim_one_eq]
  exact closeTo_lyubashevskySign_simulate n m k q η γ β R hγ hβ hη H S T hvalid msg cache
    cont hcont

/-- For zero attempts, the simulation distance is zero. -/
public theorem closeTo_lyubashevskySignAttempts_simulate_zero
    {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α) :
    CloseTo
      (lyubashevskySignAttemptsVisibleProg n m k q η γ β 0 H S T msg cache cont)
      (lyubashevskySignAttemptsVisibleSim n m k q γ β 0 H T msg cache cont) 0 := by
  rw [lyubashevskySignAttemptsVisibleProg_zero_eq_sim]
  exact CloseTo.refl _

/-- All-`K` signing simulation through a visible oracle continuation for `K ≤ 1`:
the visible outputs of the all-`K` programmed signing hybrid
and of the simulated transcript differ by at most the sum of commitment collision bounds. -/
public theorem closeTo_lyubashevskySignAttempts_simulate_le_one {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β K R : ℕ) [Fact q.Prime] (hγ : 2 * γ < q) (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hK : K ≤ 1)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (hvalid : ∀ A h, h ∈ (H A).support → lyubashevskyRelation η (S h) (A, T A h))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (cont : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) →
      OracleComp (fun _ : M × (Fin n → ZMod q) => BitString k) α)
    (hcont : ∀ A h sig, h ∈ (H A).support → IsQueryBounded (cont A h sig) R) :
    CloseTo
      (lyubashevskySignAttemptsVisibleProg n m k q η γ β K H S T msg cache cont)
      (lyubashevskySignAttemptsVisibleSim n m k q γ β K H T msg cache cont)
      (∑ j ∈ Finset.range K, ((R + K - 1 - j : ℝ≥0∞) / (q : ℝ≥0∞) ^ n +
        ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2))) := by
  cases K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [lyubashevskySignAttemptsVisibleProg_zero_eq_sim]
    exact CloseTo.refl _
  | succ K =>
    cases K with
    | zero =>
      rw [show (0 + 1 : ℕ) = 1 from rfl]
      simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, tsub_zero]
      rw [ENNReal.add_sub_cancel_right (by norm_num)]
      exact closeTo_lyubashevskySignAttempts_simulate_one n m k q η γ β R hγ hβ hη
        H S T hvalid msg cache cont hcont
    | succ K =>
      omega

/-- When the continuation makes zero oracle queries, the all-`K` programmed
signing hybrid and the all-`K` simulated signing algorithm agree in distribution for `K = 0`. -/
public theorem lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_zero
    {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β : ℕ) [NeZero q]
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (f : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) → α) :
    lyubashevskySignAttemptsVisibleProg n m k q η γ β 0 H S T msg cache
        (fun A h sig => pure (f A h sig)) =
      lyubashevskySignAttemptsVisibleSim n m k q γ β 0 H T msg cache
        (fun A h sig => pure (f A h sig)) :=
  lyubashevskySignAttemptsVisibleProg_zero_eq_sim n m k q η γ β H S T msg cache _

/-- When the continuation makes zero oracle queries, the all-`K` programmed
signing hybrid and the all-`K` simulated signing algorithm agree in distribution for `K = 1`. -/
public theorem lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_one {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β : ℕ) [Fact q.Prime] (hβ : β ≤ γ) (hη : k * η ≤ β)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (hvalid : ∀ A h, h ∈ (H A).support → lyubashevskyRelation η (S h) (A, T A h))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (f : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) → α) :
    lyubashevskySignAttemptsVisibleProg n m k q η γ β 1 H S T msg cache
        (fun A h sig => pure (f A h sig)) =
      lyubashevskySignAttemptsVisibleSim n m k q γ β 1 H T msg cache
        (fun A h sig => pure (f A h sig)) := by
  rw [lyubashevskySignAttemptsVisibleProg_one_eq, lyubashevskySignAttemptsVisibleSim_one_eq]
  exact lyubashevskySignVisibleProg_eq_sim_of_pure n m k q η γ β hβ hη H S T hvalid msg cache f

/-- When the continuation makes zero oracle queries, the all-`K` programmed
signing hybrid and the all-`K` simulated signing algorithm agree in distribution for `K ≤ 1`. -/
public theorem lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_le_one
    {Ω M α : Type} [DecidableEq M]
    (n m k q η γ β K : ℕ) [Fact q.Prime] (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hK : K ≤ 1)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (hvalid : ∀ A h, h ∈ (H A).support → lyubashevskyRelation η (S h) (A, T A h))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (f : Matrix (Fin n) (Fin m) (ZMod q) → Ω →
      Option ((Fin n → ZMod q) × (Fin m → ℤ)) → α) :
    lyubashevskySignAttemptsVisibleProg n m k q η γ β K H S T msg cache
        (fun A h sig => pure (f A h sig)) =
      lyubashevskySignAttemptsVisibleSim n m k q γ β K H T msg cache
        (fun A h sig => pure (f A h sig)) := by
  cases K with
  | zero =>
    exact lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_zero n m k q η γ β H S T msg cache f
  | succ K =>
    cases K with
    | zero =>
      exact lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_one n m k q η γ β hβ hη H S T
        hvalid msg cache f
    | succ K =>
      omega

end Cslib.Crypto.Protocols.SigmaProtocol

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
import Complexity.Probability.PMF.Bind

/-!
# One-attempt simulation through a visible oracle continuation

The counterfactual continuation on an abort starts from the original cache and sees neither
fresh mask nor hidden challenge. Its transcript is sampled before the independent mask in the
cache-hit bound. The comparison observes only outputs, not the different private caches.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignVisibleProg`: real one-attempt signing
  experiment with attempted-query cache programming and a visible oracle continuation.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignVisibleSim`: simulated signing experiment
  with accepted-transcript caching and a visible oracle continuation.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.closeTo_lyubashevskySign_simulate`: one-attempt
  simulation bridge bounding the statistical distance between real signing with attempted-query
  caching and simulated signing with accepted-transcript caching under any bounded visible
  continuation.

## References

* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF OracleComp ROMSignature Interactive RandomOracle
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
        (match sig with
         | some (t, _) => ((msg h, t), c) :: cache h
         | none => cache h)
      return (A, h, out.1)) =
    (do
      let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
      let h ← H A
      let c ← PMF.uniformOfFintype (BitString k)
      let view ← lyubashevskySimulate n m k q γ β (A, T A h) c
      let out ← (interpret (oracle (BitString k)) (cont A h view)).run
        (match view with
         | some (t, _) => ((msg h, t), c) :: cache h
         | none => cache h)
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

/-- The real one-attempt signing experiment with attempted-query cache programming
and a visible oracle continuation. -/
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
    (match view with
     | some (t, _) => ((msg h, t), c) :: cache h
     | none => cache h)
  return (A, h, out.1)

/-- One-attempt signing simulation through a visible oracle continuation:
the visible output of the actual one-attempt programmed signing attempt
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
      (match sig with
       | some (t, _) => ((msg a.2.1, t), a.2.2.2) :: cache a.2.1
       | none => cache a.2.1)).map
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
    apply RandomOracle.closeTo_bind_of_le
    intro a ha test
    cases hsig : (lyubashevsky n m k q γ β).respond (S a.2.1) (a.1, T a.1 a.2.1)
      a.2.2.1.2 a.2.2.2 with
    | some z =>
      have heq : f a = g a := by
        dsimp only [f, g]
        simp only [hsig, Option.map_some]
      rw [heq]
      exact ⟨le_add_right le_rfl, le_add_right le_rfl⟩
    | none =>
      have hclose : CloseTo (f a) (g a) (err a true) := by
        dsimp only [f, g]
        simp only [hsig, Option.map_none]
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
          (match sig with
           | some (t, _) => ((msg h, t), c) :: cache h
           | none => cache h)
        return (A, h, out.1)) = src.bind g := by
    simp only [src, g, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]
  have htrans : lyubashevskySignVisibleSim n m k q γ β H T msg cache cont = src.bind g :=
    hsim.symm.trans hhyb
  exact hprog.symm ▸ htrans.symm ▸ (hc.mono hbound)

end Cslib.Crypto.Protocols.SigmaProtocol

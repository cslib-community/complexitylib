/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.RandomOracle
public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Commitment
public import Complexity.Crypto.Game.CloseTo.UntilBad

/-!
# Programming every bounded signing attempt

This is the read-to-program hop for the actual all-attempt box signer. Programming retains
aborted entries and the effects of later attempts after the first success. The matrix is uniform,
and histories are sampled before each fresh mask without conditioning on collision survival.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF OracleComp ROMSignature Interactive
open scoped _root_.Matrix ENNReal

private theorem closeTo_attempt_program {Ω M : Type} [DecidableEq M]
    (n m k q η γ β Q : ℕ) [Fact q.Prime] (hγ : 2 * γ < q)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (hcache : ∀ A h, h ∈ (H A).support → (cache h).length ≤ Q) :
    CloseTo
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
        let out ← (interpret (oracle (BitString k))
          ((fiatShamir (lyubashevsky n m k q γ β) (lyubashevskyKeyGen n m k q η)).sign
            (S h, (A, T A h)) (msg h) coin)).run (cache h)
        return (A, h, out))
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
        let c ← PMF.uniformOfFintype (BitString k)
        return (A, h, ((coin.1,
          (lyubashevsky n m k q γ β).respond (S h) (A, T A h) coin.2 c),
          ((msg h, coin.1), c) :: cache h)))
      (Q / (q : ℝ≥0∞) ^ n +
        ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2)) := by
  classical
  let src : PMF (Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      ((Fin n → ZMod q) × (Fin m → ℤ))) := do
    let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
    let h ← H A
    let coin ← (lyubashevsky n m k q γ β).commit (S h) (A, T A h)
    return (A, h, coin)
  let hit := fun a : Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      ((Fin n → ZMod q) × (Fin m → ℤ)) =>
    ((cache a.2.1).lookup (msg a.2.1, a.2.2.1)).isSome
  let real := fun a : Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      ((Fin n → ZMod q) × (Fin m → ℤ)) =>
    ((interpret (oracle (BitString k))
      ((fiatShamir (lyubashevsky n m k q γ β) (lyubashevskyKeyGen n m k q η)).sign
        (S a.2.1, (a.1, T a.1 a.2.1)) (msg a.2.1) a.2.2)).run (cache a.2.1)).map
        (fun out => (a.1, a.2.1, out))
  let programmed := fun a : Matrix (Fin n) (Fin m) (ZMod q) × Ω ×
      ((Fin n → ZMod q) × (Fin m → ℤ)) =>
    (PMF.uniformOfFintype (BitString k)).map fun c =>
      (a.1, a.2.1, ((a.2.2.1,
        (lyubashevsky n m k q γ β).respond (S a.2.1) (a.1, T a.1 a.2.1) a.2.2.2 c),
        ((msg a.2.1, a.2.2.1), c) :: cache a.2.1))
  have hc := CloseTo.bind_of_eq_on src real programmed {a | hit a} (by
    intro a _ hgood
    have hlookup : (cache a.2.1).lookup (msg a.2.1, a.2.2.1) = none := by
      cases hq : (cache a.2.1).lookup (msg a.2.1, a.2.2.1) with
      | none => rfl
      | some c => exact False.elim (hgood (by
          simp only [Set.mem_ofPred_eq, hit, hq, Option.isSome_some]))
    dsimp only [real, programmed]
    simp only [fiatShamir, interpret_map, interpret_query, StateT.run_map,
      PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
    change ((oracle (BitString k) (msg a.2.1, a.2.2.1) (cache a.2.1)).map _) = _
    rw [oracle, memoize_of_none _ _ _ hlookup]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
    rfl)
  have hb := lyubashevsky_commit_lookup_le n m k q γ β Q hγ H S T msg cache hcache
  have hevent : src.toOuterMeasure {a | hit a} = (src.map hit) true := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  have hbound : src.toOuterMeasure {a | hit a} ≤
      Q / (q : ℝ≥0∞) ^ n +
        ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2) := by
    rw [hevent]
    simpa only [src, hit, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map] using hb
  simpa only [src, real, programmed, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def] using hc.mono hbound

/-- Replacing all `K` memoized challenge reads by fresh programming changes the joint signature
and full cache law by the finite sum of prior-cache collision bounds. Every attempt executes,
including after the first success, and every programmed entry is retained even on abort. -/
theorem closeTo_lyubashevskySign_program {Ω M : Type} [DecidableEq M]
    (n m k q η γ β K Q : ℕ) [Fact q.Prime] (hγ : 2 * γ < q)
    (H : Matrix (Fin n) (Fin m) (ZMod q) → PMF Ω)
    (S : Ω → Matrix (Fin m) (Fin k) ℤ)
    (T : Matrix (Fin n) (Fin m) (ZMod q) → Ω → Matrix (Fin n) (Fin k) (ZMod q))
    (msg : Ω → M) (cache : Ω → List ((M × (Fin n → ZMod q)) × BitString k))
    (hcache : ∀ A h, h ∈ (H A).support → (cache h).length ≤ Q) :
    CloseTo
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let out ← (iid ((lyubashevsky n m k q γ β).commit (S h) (A, T A h)) K).bind fun coins =>
          (interpret (oracle (BitString k))
            (fiatShamirAbortSign (lyubashevsky n m k q γ β) (lyubashevskyKeyGen n m k q η)
              (S h, (A, T A h)) (msg h) K coins)).run (cache h)
        return (A, h, out))
      (do
        let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
        let h ← H A
        let out ← (iid ((lyubashevsky n m k q γ β).commit (S h) (A, T A h)) K).bind fun coins =>
          (interpret (m := StateT (List ((M × (Fin n → ZMod q)) × BitString k)) PMF)
            (fun point curCache => (PMF.uniformOfFintype (BitString k)).map
            (fun c => (c, (point, c) :: curCache)))
            (fiatShamirAbortSign (lyubashevsky n m k q γ β) (lyubashevskyKeyGen n m k q η)
              (S h, (A, T A h)) (msg h) K coins)).run (cache h)
        return (A, h, out))
      (∑ j ∈ Finset.range K, ((Q + j : ℕ) / (q : ℝ≥0∞) ^ n +
        ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ n / ((2 * γ + 1 : ℕ) : ℝ) ^ m) / 2))) := by
  classical
  induction K generalizing Ω Q with
  | zero =>
    simp only [iid, fiatShamirAbortSign, run_interpret_pure, StateT.run_pure,
      PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.pure_bind, Finset.range_zero,
      Finset.sum_empty]
    exact CloseTo.refl _
  | succ K ih =>
    trace_state

end Cslib.Crypto.Protocols.SigmaProtocol

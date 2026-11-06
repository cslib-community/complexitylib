/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.RandomOracle
public import ComplexityTests.Crypto.LyubashevskyView

@[expose] public section

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.OracleComp
open Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol ROMSignature
open LyubashevskyViewTests

namespace LyubashevskyRandomOracleTests

abbrev Query := Unit × (Fin 1 → ZMod 17)
abbrev Digest := BitString 1
abbrev Cache := List (Query × Digest)

noncomputable abbrev protocol := lyubashevsky 1 2 1 17 3 1

noncomputable def keyGen := PMF.pure ((0 : Matrix (Fin 2) (Fin 1) ℤ), key)

def badCoins : (Fin 1 → ZMod 17) × (Fin 2 → ℤ) := (1, ![1, 3])

theorem respond_bad (c : Digest) : protocol.respond 0 key ![1, 3] c = none := by
  simp only [protocol, lyubashevsky, Matrix.zero_mulVec, add_zero]
  norm_num [mem_intBox, Fin.forall_fin_two]

theorem respond_good (c : Digest) : protocol.respond 0 key (0 : Fin 2 → ℤ) c = some 0 := by
  simp [protocol, lyubashevsky]

/-- The abort fixture is an actual possible commitment and mask, with nonzero public matrix. -/
theorem bad_coins_mem : badCoins ∈ (protocol.commit 0 key).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨![1, 3], (mem_support_uniformOfFinset_iff _ _).mpr ?_, ?_⟩
  · rw [mem_intBox]
    intro i
    fin_cases i <;> norm_num
  · apply Prod.ext
    · funext i
      norm_num [key, A, badCoins, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rfl

private theorem oracle_run (q : Query) (cache : Cache) :
    (oracle Digest q).run cache = memoize (fun _ => PMF.uniformOfFintype Digest) q cache := rfl

/-- An aborted new hash query is still sampled and stored in the actual final cache. -/
theorem abort_new_query :
    (interpret (oracle Digest)
      (fiatShamirAbortSign protocol keyGen (0, key) () 1 (fun _ => badCoins))).run [] =
    (PMF.uniformOfFintype Digest).map fun c => (none, [(((), 1), c)]) := by
  simp [fiatShamirAbortSign, fiatShamir, oracle_run, memoize, PMF.map, respond_bad, badCoins,
    Function.comp_def]

/-- Repeating that aborted point reuses its first digest: two calls leave only one cache entry. -/
theorem repeated_abort_query :
    (interpret (oracle Digest)
      (fiatShamirAbortSign protocol keyGen (0, key) () 2 (fun _ => badCoins))).run [] =
    (PMF.uniformOfFintype Digest).map fun c => (none, [(((), 1), c)]) := by
  simp [fiatShamirAbortSign, fiatShamir, oracle_run, memoize, PMF.map, respond_bad, badCoins,
    Fin.tail, Function.comp_def]

/-- A later external query reads exactly the digest stored by the aborted attempt. -/
example : (do
    let signed ← (interpret (oracle Digest)
      (fiatShamirAbortSign protocol keyGen (0, key) () 1 (fun _ => badCoins))).run []
    let answer ← (oracle Digest ((), 1)).run signed.2
    return (signed, answer)) =
    (PMF.uniformOfFintype Digest).map fun c =>
      ((none, [(((), 1), c)]), (c, [(((), 1), c)])) := by
  rw [abort_new_query]
  simp [oracle_run, memoize, PMF.map, Function.comp_def]

/-- The actual sampled signer has positive probability of this retained aborted cache entry. -/
example :
    0 < (((lyubashevskyROMSignature Unit 1 2 1 17 1 3 1 1).signCoins (0, key) ()).bind
      fun coins => (interpret (oracle Digest)
        ((lyubashevskyROMSignature Unit 1 2 1 17 1 3 1 1).sign (0, key) () coins)).run [])
      (none, [(((), 1), fun _ => false)]) := by
  apply (PMF.apply_pos_iff _ _).mpr
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨fun _ => badCoins, ?_, ?_⟩
  · exact (mem_support_iid_iff _ _).mpr fun _ => bad_coins_mem
  · change (none, [(((), 1), fun _ => false)]) ∈
      ((interpret (oracle Digest)
        (fiatShamirAbortSign protocol keyGen (0, key) () 1 (fun _ => badCoins))).run []).support
    rw [abort_new_query]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨fun _ => false, by simp, rfl⟩

/-- A success does not stop later hash effects. Both different points are retained, and the
returned signature is the earlier success even though the later attempt aborts. -/
theorem success_then_abort :
    (interpret (oracle Digest)
      (fiatShamirAbortSign protocol keyGen (0, key) () 2
        ![(0, (0 : Fin 2 → ℤ)), badCoins])).run [] = do
        let c₀ ← PMF.uniformOfFintype Digest
        let c₁ ← PMF.uniformOfFintype Digest
        return (some (0, 0), [(((), 1), c₁), (((), 0), c₀)]) := by
  simp [fiatShamirAbortSign, fiatShamir, oracle_run, memoize, PMF.map, respond_good,
    badCoins, List.lookup_cons, Function.comp_def,
    show (((), (1 : Fin 1 → ZMod 17)) == ((), 0)) = false by decide]

/-- Both masks in the success-then-abort execution can actually be sampled honestly. -/
example : ![(0, (0 : Fin 2 → ℤ)), badCoins] ∈ (iid (protocol.commit 0 key) 2).support := by
  apply (mem_support_iid_iff (protocol.commit 0 key) _).mpr
  intro i
  fin_cases i
  · apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨0, (mem_support_uniformOfFinset_iff _ _).mpr (zero_mem_intBox 3), ?_⟩
    simp [protocol, lyubashevsky]
  · exact bad_coins_mem

/-- Optional aborts are explicitly rejected, so this is not a total-correctness assertion. -/
example : (lyubashevskyROMSignature Unit 1 2 1 17 1 3 1 2).verify key () none =
    (pure false : OracleComp (fun _ : Query => Digest) Bool) := rfl

/-- Zero attempts abort without changing the cache, but the requested message is logged. -/
example (cache : Cache) (log : List Unit) :
    handler (lyubashevskyROMSignature Unit 1 2 1 17 1 3 1 0) (0, key) (.inl ())
      (cache, log) = PMF.pure (none, (cache, () :: log)) := by
  simp [handler, lyubashevskyROMSignature, fiatShamirAbort, iid, fiatShamirAbortSign]

/-- Distinct valid witnesses of this nonzero public matrix give the same full adaptive view. -/
example {α : Type}
    (program : OracleComp (ForgerSpec Unit Query
      (Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) Digest) α)
    (cache : Cache) (log : List Unit) :
    (interpret (handler (lyubashevskyROMSignature Unit 1 2 1 17 1 3 1 3)
      (0, key)) program).run (cache, log) =
    (interpret (handler (lyubashevskyROMSignature Unit 1 2 1 17 1 3 1 3)
      (secret, key)) program).run (cache, log) :=
  lyubashevskyROMSignature_forger_run_eq (by decide) (by decide) zero_valid secret_valid
    program (cache, log)

end LyubashevskyRandomOracleTests

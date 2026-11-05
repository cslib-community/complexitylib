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

noncomputable def keyGen := PMF.pure ((0 : Matrix (Fin 2) (Fin 1) ℤ), key)

def badCoins : (Fin 1 → ZMod 17) × (Fin 2 → ℤ) := (1, ![1, 3])

theorem respond_bad (c : Digest) : P.respond 0 key badCoins.2 c = none := by
  norm_num [P, lyubashevsky, badCoins, mem_intBox, Fin.forall_fin_two]

theorem respond_good (c : Digest) : P.respond 0 key (0 : Fin 2 → ℤ) c = some 0 := by
  simp [P, lyubashevsky, zero_mem_intBox]

/-- The abort fixture is an actual possible commitment and mask, with nonzero public matrix. -/
example : badCoins ∈ (P.commit 0 key).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨![1, 3], (mem_support_uniformOfFinset_iff _ _).mpr ?_, ?_⟩
  · rw [mem_intBox]
    intro i
    fin_cases i <;> norm_num
  · apply Prod.ext
    · funext i
      norm_num [key, A, badCoins, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rfl

/-- An aborted new hash query is still sampled and stored in the actual final cache. -/
theorem abort_new_query :
    (interpret (oracle Digest)
      (fiatShamirAbortSign P keyGen (0, key) () 1 (fun _ => badCoins))).run [] =
    (PMF.uniformOfFintype Digest).map fun c => (none, [(((), 1), c)]) := by
  simp [fiatShamirAbortSign, fiatShamir, interpret_bind, interpret_map, interpret_query,
    StateT.run_bind, StateT.run_map, oracle, memoize, PMF.map, respond_bad, badCoins]

/-- Repeating that aborted point reuses its first digest: two calls leave only one cache entry. -/
theorem repeated_abort_query :
    (interpret (oracle Digest)
      (fiatShamirAbortSign P keyGen (0, key) () 2 (fun _ => badCoins))).run [] =
    (PMF.uniformOfFintype Digest).map fun c => (none, [(((), 1), c)]) := by
  simp [fiatShamirAbortSign, fiatShamir, interpret_bind, interpret_map, interpret_query,
    StateT.run_bind, StateT.run_map, oracle, memoize, PMF.map, respond_bad, badCoins]

/-- A success does not stop later hash effects. Both different points are retained, and the
returned signature is the earlier success even though the later attempt aborts. -/
theorem success_then_abort :
    (interpret (oracle Digest)
      (fiatShamirAbortSign P keyGen (0, key) () 2 ![(0, 0), badCoins])).run [] = do
        let c₀ ← PMF.uniformOfFintype Digest
        let c₁ ← PMF.uniformOfFintype Digest
        return (some (0, 0), [(((), 1), c₁), (((), 0), c₀)]) := by
  simp [fiatShamirAbortSign, fiatShamir, interpret_bind, interpret_map, interpret_query,
    StateT.run_bind, StateT.run_map, oracle, memoize, PMF.map, respond_bad, respond_good,
    badCoins]

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

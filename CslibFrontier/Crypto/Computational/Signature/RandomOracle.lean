/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Signature.Bridge
public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind

/-!
# Signature schemes as random-oracle signature schemes

A signature scheme that never queries a random oracle is a random-oracle signature scheme
(`ROMSignature.Scheme`, [BonehShoup2023], Section 13.2.1) with no oracle points: `Query` is
`Empty`. `Signature.Scheme.toROM` is this view; its signing coins are the signature itself.

Its random-oracle forgery experiment `ROMSignature.worldGame`, against the forger
`Signature.Forger.toROM A`, is the forgery experiment of the scheme against `A`, for every freshness
condition (`Signature.Scheme.worldGame_toROM`). The random-oracle experiment keeps the signed pairs
newest first and the forgery experiment oldest first. In particular, the random-oracle EUF-CMA and
SUF-CMA experiments of `S.toROM` are `S.eufCmaExperiment` and `S.sufCmaExperiment`.

Through `SignatureScheme.toScheme`, the word-level EUF-CMA games are random-oracle experiments
too, and honest signatures of `n`-bit messages verify in `(S.toScheme n).toROM`.

## Main definitions

* `Cslib.Crypto.Signature.Scheme.toROM`: a signature scheme as a random-oracle signature scheme
  with no oracle points.
* `Cslib.Crypto.Signature.Forger.toROM`: a forger as a random-oracle forger that makes no hash
  calls.

## Main results

* `Cslib.Crypto.Signature.Scheme.correctOn_toROM`, `Cslib.Crypto.Signature.Scheme.correct_toROM`:
  correctness of `S.toROM` on admissible and on all messages.
* `Cslib.Crypto.Signature.Scheme.worldGame_toROM`: the random-oracle experiment of `S.toROM` is
  the forgery experiment of `S`.
* `Cslib.Crypto.Signature.Scheme.worldGame_toROM_eufCma`,
  `Cslib.Crypto.Signature.Scheme.worldGame_toROM_sufCma`: the EUF-CMA and SUF-CMA instances.
* `Cslib.Crypto.SignatureScheme.eufCmaGame_eq_worldGame_toROM`,
  `Cslib.Crypto.WordSignatureScheme.eufCmaGame_eq_worldGame_toROM`,
  `Cslib.Crypto.SignatureScheme.correctOn_toROM`, `Cslib.Crypto.WordSignatureScheme.correct_toROM`:
  the word-level instances.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 13.1 and 13.2.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability OracleComp Protocols

namespace Signature

variable {PK SK M Sig : Type}

/-- The scheme `S` as a random-oracle signature scheme with no oracle points: the signing coins are
the signature drawn by `S.sign`, and signing and verification make no oracle calls. -/
noncomputable def Scheme.toROM (S : Scheme PK SK M Sig) :
    ROMSignature.Scheme PK SK M Sig Empty Unit where
  keyGen := ProbComp.eval S.keyGen
  SignCoins := Sig
  signCoins sk m := ProbComp.eval (S.sign sk m)
  sign _ _ σ := pure σ
  verify pk m σ := pure (S.verify pk m σ)

@[simp] theorem Scheme.toROM_keyGen (S : Scheme PK SK M Sig) :
    S.toROM.keyGen = ProbComp.eval S.keyGen := rfl

@[simp] theorem Scheme.toROM_verify (S : Scheme PK SK M Sig) (pk : PK) (m : M) (σ : Sig) :
    S.toROM.verify pk m σ = pure (S.verify pk m σ) := rfl

/-- The forger `A` as a random-oracle forger: each signing query `m` becomes the signing call
`.inl m`, and private sampling is unchanged. It makes no hash calls. -/
def Forger.toROM (A : Forger PK M Sig) (pk : PK) :
    ProbOracleComp (ROMSignature.ForgerSpec M Empty Sig Unit) (M × Sig) :=
  interpret
    (sumHandler
      (fun k => ProbOracleComp.sample (spec := ROMSignature.ForgerSpec M Empty Sig Unit)
        (ProbComp.unifFin k))
      (fun m => ProbOracleComp.query (spec := ROMSignature.ForgerSpec M Empty Sig Unit) (.inl m)))
    (A pk)

namespace Scheme

/-- `S.toROM` is correct on the messages satisfying `adm` when every honest signature on such a
message verifies under `S`. -/
theorem correctOn_toROM {S : Scheme PK SK M Sig} {adm : M → Prop}
    (h : ∀ keys ∈ (ProbComp.eval S.keyGen).support, ∀ m, adm m →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 m)).support, S.verify keys.1 m σ = true) :
    S.toROM.CorrectOn adm := by
  dsimp only [ROMSignature.Scheme.CorrectOn, toROM]
  intro keys hkeys m hm σ hσ cache signed hsigned verified hverified
  simp only [interpret_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
    PMF.mem_support_pure_iff] at hsigned hverified
  subst hsigned hverified
  exact h keys hkeys m hm σ hσ

/-- A correct scheme is a correct random-oracle scheme. -/
theorem correct_toROM {S : Scheme PK SK M Sig} (h : S.Correct) : S.toROM.Correct :=
  (ROMSignature.Scheme.correctOn_true_iff _).mp
    (correctOn_toROM fun keys hkeys m _ σ hσ => h keys hkeys m σ hσ)

variable [Inhabited Sig]

/-- Running `A.toROM` with signing-pair logging against the signer of `S.toROM` at `sk`, and
reversing the log, is running `A` against the logging signer of `S`. The oracle cache stays
empty. -/
private theorem runWith_runLoggedForger_toROM (S : Scheme PK SK M Sig) (A : Forger PK M Sig)
    (pk : PK) (sk : SK) :
    (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl S.toROM sk)
      (ROMSignature.runLoggedForger (A.toROM pk)) []).map
        (fun ((msig, pairs), _) => (msig, pairs.reverse)) =
      ProbComp.eval ((A pk).runLogWith (Signer.ofSign S.sign sk)) := by
  rw [ProbOracleComp.runLogWith, ProbOracleComp.eval_runState]
  unfold ROMSignature.runLoggedForger Forger.toROM
  have hcomp :
      interpret
        (sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample
            (spec := ROMSignature.ForgerSpec M Empty Sig Unit) (ProbComp.unifFin k)))
          ROMSignature.logSigning)
        (interpret
          (sumHandler
            (fun k => ProbOracleComp.sample (spec := ROMSignature.ForgerSpec M Empty Sig Unit)
              (ProbComp.unifFin k))
            (fun m => ProbOracleComp.query (spec := ROMSignature.ForgerSpec M Empty Sig Unit)
              (.inl m)))
          (A pk)) =
      interpret
        (sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample
            (spec := ROMSignature.ForgerSpec M Empty Sig Unit) (ProbComp.unifFin k)))
          (fun m => ROMSignature.logSigning (.inl m)))
        (A pk) := by
    rw [interpret_interpret]
    congr 1 with q : 1
    cases q with
    | inl k =>
      simp [sumHandler, ProbOracleComp.sample, ProbComp.unifFin, interpret_query]
    | inr m =>
      simp [sumHandler, ProbOracleComp.query, interpret_query]
  rw [hcomp, ProbOracleComp.runWith_run_interpret, PMF.map_comp]
  exact ProbOracleComp.runWith_map_state _
    (fun m log => ProbComp.eval (ProbOracleComp.logOracle (Signer.ofSign S.sign sk) m log))
    (fun (state : List (M × Sig) × List (Empty × Unit)) => state.1.reverse)
    (fun m ⟨pairs, cache⟩ => by
      simp only [ROMSignature.forgerWorldImpl, toROM, StateT.run, interpret_pure,
        PMF.monad_bind_eq_bind, ROMSignature.logSigning, bind_pure_comp,
        ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, sumHandler, PMF.map_bind,
        PMF.map_comp, Function.comp_def]
      have hpure : ∀ σ : Sig, (pure σ : StateT (List (Empty × Unit)) PMF Sig) cache =
          PMF.pure (σ, cache) := fun _ => rfl
      simp only [Prod.map_fst, List.reverse_cons, hpure, PMF.pure_map, ProbOracleComp.logOracle,
        Signer.ofSign_apply, ProbComp.eval_map]
      rfl)
    (A pk) ([], [])

/-- **The random-oracle experiment of `S.toROM` is the forgery experiment of `S`**: for every
freshness condition `fresh`, the random-oracle experiment that accepts a verified candidate fresh
for the signed pairs (newest first) has the distribution of `forgeExperiment` with `fresh`. -/
theorem worldGame_toROM (S : Scheme PK SK M Sig) (fresh : M → Sig → List (M × Sig) → Bool)
    (A : Forger PK M Sig) :
    ROMSignature.worldGame S.toROM A.toROM
        (fun verified (m, σ) pairs => verified && fresh m σ pairs.reverse) =
      ProbComp.eval
        (forgeExperiment S.keyGen (.ofSign S.sign) (fun pk _ => S.verify pk) fresh A) := by
  unfold ROMSignature.worldGame forgeExperiment
  simp only [toROM_keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ _ => ?_
  dsimp only
  rw [ROMSignature.eval_world_worldRealize, ← runWith_runLoggedForger_toROM, PMF.bind_map]
  simp only [toROM_verify, interpret_pure, StateT.run_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind]
  rfl

/-- The random-oracle EUF-CMA experiment of `S.toROM` is `S.eufCmaExperiment`. -/
theorem worldGame_toROM_eufCma [DecidableEq M] (S : Scheme PK SK M Sig) (A : Forger PK M Sig) :
    ROMSignature.worldGame S.toROM A.toROM
        (fun verified ⟨m, _⟩ pairs => verified && !(pairs.map Prod.fst).contains m) =
      ProbComp.eval (S.eufCmaExperiment A) := by
  refine Eq.trans ?_ (S.worldGame_toROM freshMessage A)
  congr 1
  funext verified msig pairs
  have hmem : ∀ x, x ∈ pairs.reverse.map Prod.fst ↔ x ∈ pairs.map Prod.fst := by
    simp [List.mem_map]
  simp only [freshMessage, hmem, List.contains_eq_mem, decide_not]

/-- The random-oracle SUF-CMA experiment of `S.toROM` is `S.sufCmaExperiment`. -/
theorem worldGame_toROM_sufCma [DecidableEq M] [DecidableEq Sig] (S : Scheme PK SK M Sig)
    (A : Forger PK M Sig) :
    ROMSignature.worldGame S.toROM A.toROM
        (fun verified msig pairs => verified && !pairs.contains msig) =
      ProbComp.eval (S.sufCmaExperiment A) := by
  refine Eq.trans ?_ (S.worldGame_toROM freshPair A)
  congr 1
  funext verified msig pairs
  simp [freshPair]

end Scheme

end Signature

/-- At each parameter `n`, the word-level EUF-CMA game is the random-oracle EUF-CMA experiment of
`(S.toScheme n).toROM`. -/
theorem SignatureScheme.eufCmaGame_eq_worldGame_toROM (S : SignatureScheme) (adversary : Forger)
    (n : ℕ) :
    ProbComp.eval (S.eufCmaGame adversary n) =
      ROMSignature.worldGame (S.toScheme n).toROM (adversary.toTyped n).toROM
        (fun verified (⟨m, _⟩ : List Bool × List Bool) pairs =>
          verified && !(pairs.map Prod.fst).contains m) := by
  rw [S.eufCmaGame_eq_eufCmaExperiment, ← Signature.Scheme.worldGame_toROM_eufCma]
  congr 1
  funext verified msig pairs
  simp only [List.contains_eq_mem]
  congr

/-- At each parameter `n`, honest signatures of `n`-bit messages verify in
`(S.toScheme n).toROM`. -/
theorem SignatureScheme.correctOn_toROM (S : SignatureScheme) (n : ℕ) :
    (S.toScheme n).toROM.CorrectOn (fun m => m.length = n) :=
  Signature.Scheme.correctOn_toROM fun keys hkeys m hm σ hσ => by
    simpa [hm] using S.verify_sign n keys hkeys m hm σ hσ

/-- At each parameter `n`, the unrestricted word-level EUF-CMA game is the random-oracle EUF-CMA
experiment of `(S.toScheme n).toROM`. -/
theorem WordSignatureScheme.eufCmaGame_eq_worldGame_toROM (S : WordSignatureScheme)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame adversary n) =
      ROMSignature.worldGame (S.toScheme n).toROM (adversary.toTyped n).toROM
        (fun verified (⟨m, _⟩ : List Bool × List Bool) pairs =>
          verified && !(pairs.map Prod.fst).contains m) := by
  rw [S.eufCmaGame_eq_eufCmaExperiment, ← Signature.Scheme.worldGame_toROM_eufCma]
  congr 1
  funext verified msig pairs
  simp only [List.contains_eq_mem]
  congr

/-- At each parameter `n`, `(S.toScheme n).toROM` is correct on every message. -/
theorem WordSignatureScheme.correct_toROM (S : WordSignatureScheme) (n : ℕ) :
    (S.toScheme n).toROM.Correct :=
  Signature.Scheme.correct_toROM fun keys hkeys m σ hσ =>
    S.verify_sign n keys.1 keys.2 hkeys m σ hσ

end Cslib.Crypto

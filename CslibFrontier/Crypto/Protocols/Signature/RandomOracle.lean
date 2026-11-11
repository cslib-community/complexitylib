/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Basic
public import CslibFrontier.Foundations.Control.Monad.Memoize
public import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Languages.Probabilistic.Sum
public import Cslib.Probability.PMF
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind

/-!
# Signatures in the random-oracle model

A signature scheme in the random-oracle model ([BonehShoup2023], Section 13.2.1) signs and
verifies with oracle access to a function `H : Query → Digest`, which the security experiment
draws uniformly at random. Signing draws its coins and then runs an `OracleComp` program against
`H`; verification is a deterministic `OracleComp` program. The oracle is sampled lazily: each new
point gets a uniform answer, remembered in an association list (`oracle`), so the query and digest
types need not be finite beyond the digests.

The existential-unforgeability experiment (`eufCmaGame`, [BonehShoup2023], Attack Game 13.1 in
its random-oracle version) gives a forger the public key and oracle access to the signer and to
`H`; the forger wins with a valid signature on a message it never asked to have signed. A
`Forger` has explicit coins, drawn first, and is otherwise a deterministic `OracleComp` program;
this is the form in which a forger can be rerun on the same coins, as forking needs. Its signing
and hash calls are counted separately (`Forger.CallBounded`), as security bounds depend on them
differently.

The shared interactive execution core (`world`, `logSigning`, `runLoggedForger`, `liftVerify`,
`liftOracleForger`, `worldRealize`, `worldGame`) realizes the forger's signing/hash interface and
the verifier's hash interface inside a single `Cslib.Interactive.World` whose state is the shared
random-oracle cache `List (Query × Digest)`, with local signing-pair logging `List (M × Sig)`.
Projecting the pair log recovers `handler` (`runWith_world_runLoggedForger_liftOracleForger`), and
specializing the post-verification acceptance predicate yields:

* `eufCmaGame` and its final-message admissibility generalization `eufCmaFinalMsgGame` (which gates
  only the final forged message `msg` by `admissible msg` and `FreshOutputsOnFinalMessage`,
  leaving signing queries unrestricted and allowing internal random-oracle collisions);
* key-only existential unforgeability `ufCma0Game`; and
* strong (fresh-pair) unforgeability `sufCmaGame` and its key-only companion `sufCma0Game`.

This interface also connects directly to `Cslib.Crypto.SignatureScheme` and
`Cslib.Crypto.WordSignatureScheme` (in `CslibFrontier.Crypto.Computational.Signature.RandomOracle`)
by
specializing `Query := Empty` and `Digest := Unit` and gating final-message admissibility by
`msg.length == n`.

## Main definitions

* `Cslib.Crypto.Protocols.ROMSignature.ForgerSpec`: the disjoint sum of signing and hash calls.
* `Cslib.Crypto.Protocols.ROMSignature.Scheme`: key generation, signing and verification.
* `Cslib.Crypto.Protocols.ROMSignature.Forger`: a forger with explicit coins.
* `Cslib.Crypto.Protocols.ROMSignature.signingCost`,
  `Cslib.Crypto.Protocols.ROMSignature.hashCost`,
  `Cslib.Crypto.Protocols.ROMSignature.Forger.CallBounded`: separate signing and hash call budgets.
* `Cslib.Crypto.Protocols.ROMSignature.FreshOutputs`,
  `Cslib.Crypto.Protocols.ROMSignature.FreshOutputsOnFinalMessage`: full transcript message
  distinctness and final-message freshness (`msg ∉ queried`).
* `Cslib.Crypto.Protocols.ROMSignature.oracle`,
  `Cslib.Crypto.Protocols.ROMSignature.handler`: the lazily sampled uniform random oracle and
  joint signing/hash handler.
* `Cslib.Crypto.Protocols.ROMSignature.forgerWorldImpl`,
  `Cslib.Crypto.Protocols.ROMSignature.world`,
  `Cslib.Crypto.Protocols.ROMSignature.logSigning`,
  `Cslib.Crypto.Protocols.ROMSignature.runLoggedForger`,
  `Cslib.Crypto.Protocols.ROMSignature.liftVerify`,
  `Cslib.Crypto.Protocols.ROMSignature.liftOracleForger`,
  `Cslib.Crypto.Protocols.ROMSignature.worldRealize`,
  `Cslib.Crypto.Protocols.ROMSignature.worldGame`: shared `Cslib.Interactive.World` execution core.
* `Cslib.Crypto.Protocols.ROMSignature.eufCmaGame`,
  `Cslib.Crypto.Protocols.ROMSignature.eufCmaFinalMsgGame`,
  `Cslib.Crypto.Protocols.ROMSignature.ufCma0Game`,
  `Cslib.Crypto.Protocols.ROMSignature.sufCmaGame`,
  `Cslib.Crypto.Protocols.ROMSignature.sufCma0Game`: adaptive and key-only signature security games.
* `Cslib.Crypto.Protocols.ROMSignature.Scheme.Correct`,
  `Cslib.Crypto.Protocols.ROMSignature.Scheme.CorrectOn`: all-message and admissible-message
  completeness predicates.

## Main results

* `Cslib.Crypto.Protocols.ROMSignature.Forger.CallBounded.isQueryBounded`: separate signing and
  hash bounds imply a total query bound.
* `Cslib.Crypto.Protocols.ROMSignature.FreshOutputs.freshOutputsOnFinalMessage`,
  `Cslib.Crypto.Protocols.ROMSignature.decide_freshOutputsOnFinalMessage`: full output freshness
  implies final-message freshness, decided by `!queried.contains msg`.
* `Cslib.Crypto.Protocols.ROMSignature.lookup_of_mem_support_oracle`,
  `Cslib.Crypto.Protocols.ROMSignature.length_le_of_mem_support_oracle`: post-call cache lookup and
  one-step cache-growth bounds for `oracle`.
* `Cslib.Crypto.Protocols.ROMSignature.runWith_world_liftProver`,
  `Cslib.Crypto.Protocols.ROMSignature.runWith_world_liftVerify`,
  `Cslib.Crypto.Protocols.ROMSignature.runWith_world_runLoggedForger_liftOracleForger`,
  `Cslib.Crypto.Protocols.ROMSignature.eval_world_worldRealize`,
  `Cslib.Crypto.Protocols.ROMSignature.eval_world_worldRealize_liftOracleForger`: exact execution
  equivalences for the `Interactive.World` core.
* `Cslib.Crypto.Protocols.ROMSignature.eufCmaFinalMsgGame_eq_worldGame`,
  `Cslib.Crypto.Protocols.ROMSignature.eufCmaGame_eq_worldGame`,
  `Cslib.Crypto.Protocols.ROMSignature.eufCmaFinalMsgGame_true`,
  `Cslib.Crypto.Protocols.ROMSignature.eufCmaFinalMsgGame_apply_true_le`,
  `Cslib.Crypto.Protocols.ROMSignature.sufCma0Game_eq_ufCma0Game`: shared-world characterizations of
  the signature games.
* `Cslib.Crypto.Protocols.ROMSignature.Scheme.Correct.correctOn`,
  `Cslib.Crypto.Protocols.ROMSignature.Scheme.correctOn_true_iff`: relationship between
  `Scheme.Correct` and `Scheme.CorrectOn`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 13.1 and 13.2.1.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.ROMSignature

open Probability OracleComp

/-- The calls of a forger: a signing call names a message and returns a signature, and a hash call
names a point and returns its digest. -/
abbrev ForgerSpec (M Query Sig Digest : Type) : OracleSpec (M ⊕ Query) :=
  (fun _ : M => Sig) ⊕ₒ (fun _ : Query => Digest)

/-- A signature scheme in the random-oracle model, with public keys `PK`, secret keys `SK`,
messages `M`, signatures `Sig`, and oracle `H : Query → Digest`. Signing first draws coins. -/
structure Scheme (PK SK M Sig Query Digest : Type) where
  /-- Draw a public key and a secret key. -/
  keyGen : PMF (PK × SK)
  /-- The signer's coins. -/
  SignCoins : Type
  /-- Draw the signer's coins for a message. -/
  signCoins : SK → M → PMF SignCoins
  /-- Sign, querying the oracle. -/
  sign : SK → M → SignCoins → OracleComp (fun _ : Query => Digest) Sig
  /-- Verify, querying the oracle. -/
  verify : PK → M → Sig → OracleComp (fun _ : Query => Digest) Bool

/-- A forger with explicit coins: it draws its coins, then, given the public key, calls the signer
and the oracle and outputs a message and a signature. -/
structure Forger (PK M Sig Query Digest : Type) where
  /-- The forger's coins. -/
  Coins : Type
  /-- Draw the forger's coins. -/
  coins : PMF Coins
  /-- Forge, calling the signer and the oracle. -/
  forge : PK → Coins → OracleComp (ForgerSpec M Query Sig Digest) (M × Sig)

variable {PK SK M Sig Query Digest : Type}

/-- A forger's call costs one when it is a signing call. -/
def signingCost : M ⊕ Query → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- A forger's call costs one when it is a hash call. -/
def hashCost : M ⊕ Query → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- The forger makes at most `signs` signing calls and at most `hashes` hash calls on every path,
for every public key and every choice of its coins. -/
def Forger.CallBounded (A : Forger PK M Sig Query Digest) (signs hashes : ℕ) : Prop :=
  ∀ pk coins, IsCostBounded signingCost (A.forge pk coins) signs ∧
    IsCostBounded hashCost (A.forge pk coins) hashes

/-- A forger making at most `signs` signing and `hashes` hash calls makes at most
`signs + hashes` calls. -/
theorem Forger.CallBounded.isQueryBounded {A : Forger PK M Sig Query Digest} {signs hashes : ℕ}
    (h : A.CallBounded signs hashes) (pk : PK) (coins : A.Coins) :
    IsQueryBounded (A.forge pk coins) (signs + hashes) :=
  ((h pk coins).1.add (h pk coins).2).of_le fun q => by cases q <;> simp [signingCost, hashCost]

/-- Every message in the signing query log and final candidate forgery is distinct. -/
def FreshOutputs (queried : List M) (msg : M) : Prop :=
  (msg :: queried).Nodup

instance [DecidableEq M] (queried : List M) (msg : M) :
    Decidable (FreshOutputs queried msg) :=
  inferInstanceAs (Decidable (msg :: queried).Nodup)

/-- The final forged message `msg` was never queried to the signing oracle (`msg ∉ queried`),
allowing earlier signing queries or internal random-oracle queries to repeat. -/
def FreshOutputsOnFinalMessage (queried : List M) (msg : M) : Prop :=
  msg ∉ queried

instance [DecidableEq M] (queried : List M) (msg : M) :
    Decidable (FreshOutputsOnFinalMessage queried msg) :=
  inferInstanceAs (Decidable (msg ∉ queried))

/-- Distinctness of all outputs (`FreshOutputs`) implies freshness of the final forged message
(`FreshOutputsOnFinalMessage`). -/
theorem FreshOutputs.freshOutputsOnFinalMessage {queried : List M} {msg : M}
    (h : FreshOutputs queried msg) : FreshOutputsOnFinalMessage queried msg :=
  (List.nodup_cons.mp h).1

@[simp]
theorem decide_freshOutputsOnFinalMessage [DecidableEq M] (queried : List M) (msg : M) :
    decide (FreshOutputsOnFinalMessage queried msg) = !queried.contains msg := by
  by_cases h : msg ∈ queried <;> simp [FreshOutputsOnFinalMessage, List.contains_eq_mem, h]

variable [DecidableEq Query] [Fintype Digest] [Nonempty Digest]

variable (Digest) in
/-- The random oracle: a uniform digest for each new point, remembered thereafter. -/
noncomputable def oracle (q : Query) : StateT (List (Query × Digest)) PMF Digest :=
  memoize (fun _ => PMF.uniformOfFintype Digest) q

/-- A table entry produced by a call of `oracle` is found at its queried point. -/
theorem lookup_of_mem_support_oracle {q : Query} {cache : List (Query × Digest)}
    {result : Digest × List (Query × Digest)} (h : result ∈ (oracle Digest q cache).support) :
    result.2.lookup q = some result.1 := by
  cases hlookup : cache.lookup q <;>
    simp only [oracle, memoize, hlookup, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
      PMF.mem_support_pure_iff, PMF.mem_support_bind_iff] at h
  · obtain ⟨_, _, rfl⟩ := h
    exact List.lookup_cons_self
  · subst h
    exact hlookup

/-- A call of `oracle` adds at most one entry to the cache. -/
theorem length_le_of_mem_support_oracle {q : Query} {cache : List (Query × Digest)}
    {result : Digest × List (Query × Digest)} (h : result ∈ (oracle Digest q cache).support) :
    result.2.length ≤ cache.length + 1 := by
  cases hlookup : cache.lookup q <;>
    simp only [oracle, memoize, hlookup, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
      PMF.mem_support_pure_iff, PMF.mem_support_bind_iff] at h
  · obtain ⟨_, _, rfl⟩ := h
    exact le_rfl
  · subst h
    exact Nat.le_succ _

/-- Answer a forger's calls: sign with the secret key, recording the message, or query the
oracle. Signing and the forger share the oracle. -/
noncomputable def handler (scheme : Scheme PK SK M Sig Query Digest) (sk : SK) :
    (q : M ⊕ Query) → StateT (List (Query × Digest) × List M) PMF (ForgerSpec M Query Sig Digest q)
  | .inl m => fun state => do
    let coins ← scheme.signCoins sk m
    let signed ← (interpret (oracle Digest) (scheme.sign sk m coins)).run state.1
    return (signed.1, (signed.2, m :: state.2))
  | .inr x => fun state => do
    let answer ← oracle Digest x state.1
    return (answer.1, (answer.2, state.2))

/-! ### Shared `Interactive.World` execution core -/

/-- Implementation of the forger's signing and hash calls against the shared random-oracle cache
`List (Query × Digest)` without recording a signing log. -/
noncomputable def forgerWorldImpl (scheme : Scheme PK SK M Sig Query Digest) (sk : SK) :
    (q : M ⊕ Query) → StateT (List (Query × Digest)) PMF (ForgerSpec M Query Sig Digest q) :=
  sumHandler
    (fun m cache => do
      let coins ← scheme.signCoins sk m
      (interpret (oracle Digest) (scheme.sign sk m coins)).run cache)
    (oracle Digest)

/-- The interactive oracle world of a random-oracle signature experiment under secret key `sk`:
the forger's signing and hash calls (`ForgerSpec M Query Sig Digest`) and the verifier's hash calls
(`fun _ : Query => Digest`) share the same lazily sampled random-oracle cache
`List (Query × Digest)`. -/
@[reducible]
noncomputable def world (scheme : Scheme PK SK M Sig Query Digest) (sk : SK) :
    Interactive.World (ForgerSpec M Query Sig Digest) (fun _ : Query => Digest) where
  State := List (Query × Digest)
  init := []
  impl := sumHandler (forgerWorldImpl scheme sk) (oracle Digest)

/-- Forger call handler that forwards signing and hash queries to the external `ForgerSpec`
oracle while logging each `(message, signature)` pair returned by the signing oracle. -/
def logSigning :
    (q : M ⊕ Query) →
      StateT (List (M × Sig)) (ProbOracleComp (ForgerSpec M Query Sig Digest))
        (ForgerSpec M Query Sig Digest q)
  | .inl m, pairs => do
    let sig ← ProbOracleComp.query (spec := ForgerSpec M Query Sig Digest) (.inl m)
    return (sig, (m, sig) :: pairs)
  | .inr x, pairs => do
    let d ← ProbOracleComp.query (spec := ForgerSpec M Query Sig Digest) (.inr x)
    return (d, pairs)

/-- Run an adaptive `ProbOracleComp` forger while recording the list of `(message, signature)`
pairs returned by the signing oracle. -/
def runLoggedForger
    (forger : ProbOracleComp (ForgerSpec M Query Sig Digest) (M × Sig)) :
    ProbOracleComp (ForgerSpec M Query Sig Digest) ((M × Sig) × List (M × Sig)) :=
  (interpret
    (sumHandler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) logSigning)
    forger).run []

/-- Lift a verifier `OracleComp` over the hash oracle into the joint prover/verifier oracle
interface of `world`. -/
def liftVerify {α : Type} (prog : OracleComp (fun _ : Query => Digest) α) :
    ProbOracleComp (ForgerSpec M Query Sig Digest ⊕ₒ (fun _ : Query => Digest)) α :=
  interpret (fun x =>
    ProbOracleComp.query
      (spec := ForgerSpec M Query Sig Digest ⊕ₒ (fun _ : Query => Digest)) (.inr x)) prog

/-- Embed a deterministic `OracleComp` forger program into `ProbOracleComp`. -/
def liftOracleForger {α : Type}
    (prog : OracleComp (ForgerSpec M Query Sig Digest) α) :
    ProbOracleComp (ForgerSpec M Query Sig Digest) α :=
  interpret (fun q => ProbOracleComp.query (spec := ForgerSpec M Query Sig Digest) q) prog

/-- Shared interactive execution core in `world scheme sk`: run a `ProbOracleComp` forger with
signing-pair logging, then run `scheme.verify pk` on the candidate forgery in the same
random-oracle world, and judge the outcome with `accept verified msig pairs`. -/
def worldRealize (scheme : Scheme PK SK M Sig Query Digest) (pk : PK)
    (forger : ProbOracleComp (ForgerSpec M Query Sig Digest) (M × Sig))
    (accept : Bool → M × Sig → List (M × Sig) → Bool) :
    ProbOracleComp (ForgerSpec M Query Sig Digest ⊕ₒ (fun _ : Query => Digest)) Bool := do
  let out ← Interactive.liftProver (oV := fun _ : Query => Digest) (runLoggedForger forger)
  let msig := out.1
  let pairs := out.2
  let verified ← liftVerify (scheme.verify pk msig.1 msig.2)
  return accept verified msig pairs

/-- Evaluate a signature security game through `Interactive.World.eval` on `world scheme sk`:
draw `(pk, sk) ← scheme.keyGen`, run `worldRealize scheme pk (forger pk) accept` in
`world scheme sk`, and return the acceptance distribution. -/
noncomputable def worldGame (scheme : Scheme PK SK M Sig Query Digest)
    (forger : PK → ProbOracleComp (ForgerSpec M Query Sig Digest) (M × Sig))
    (accept : Bool → M × Sig → List (M × Sig) → Bool) : PMF Bool := do
  let keys ← scheme.keyGen
  Interactive.World.eval (world scheme keys.2)
    (worldRealize scheme keys.1 (forger keys.1) accept)

/-- Running a lifted prover computation in `world scheme sk` reduces to running it against
`forgerWorldImpl scheme sk`. -/
theorem runWith_world_liftProver (scheme : Scheme PK SK M Sig Query Digest) (sk : SK) {α : Type}
    (prog : ProbOracleComp (ForgerSpec M Query Sig Digest) α)
    (cache : List (Query × Digest)) :
    ProbOracleComp.runWith (world scheme sk).impl
      (Interactive.liftProver (oV := fun _ : Query => Digest) prog) cache =
    ProbOracleComp.runWith (forgerWorldImpl scheme sk) prog cache := by
  simp only [Interactive.liftProver, ← ProbOracleComp.sample_unifFin,
    ProbOracleComp.runWith_interpret_sumHandler]
  congr 1 with q s : 2
  simp [sumHandler]

/-- Running a lifted verifier computation in `world scheme sk` reduces to interpreting it against
`oracle Digest`. -/
theorem runWith_world_liftVerify (scheme : Scheme PK SK M Sig Query Digest) (sk : SK) {α : Type}
    (prog : OracleComp (fun _ : Query => Digest) α)
    (cache : List (Query × Digest)) :
    ProbOracleComp.runWith (world scheme sk).impl (liftVerify (M := M) (Sig := Sig) prog) cache =
    (interpret (oracle Digest) prog).run cache := by
  rw [liftVerify, ProbOracleComp.runWith_interpret, OracleComp.runWith]
  congr 2 with x s : 2
  simp [world, sumHandler]

/-- Running `runLoggedForger (liftOracleForger prog)` against `forgerWorldImpl scheme sk` and
projecting the logged `(message, signature)` pairs to their first components reproduces
`handler scheme sk`. -/
theorem runWith_world_runLoggedForger_liftOracleForger
    (scheme : Scheme PK SK M Sig Query Digest) (sk : SK)
    (prog : OracleComp (ForgerSpec M Query Sig Digest) (M × Sig))
    (cache : List (Query × Digest)) :
    (ProbOracleComp.runWith (forgerWorldImpl scheme sk)
      (runLoggedForger (liftOracleForger prog)) cache).map
        (fun ⟨⟨msig, pairs⟩, cache'⟩ => (msig, (cache', pairs.map Prod.fst))) =
    (interpret (handler scheme sk) prog).run (cache, []) := by
  rw [runLoggedForger, ProbOracleComp.runWith_run_interpret, PMF.map_comp, liftOracleForger,
    ProbOracleComp.runWith_interpret]
  refine OracleComp.run_interpret_map_state (oracle' := handler scheme sk)
    (represent := fun (state : List (M × Sig) × List (Query × Digest)) =>
      (state.2, state.1.map Prod.fst)) (step := fun q ⟨pairs, curCache⟩ => ?_) (program := prog)
    (s := ([], cache))
  rw [ProbOracleComp.runWith_query]
  cases q <;> simp [logSigning, handler, forgerWorldImpl, sumHandler, StateT.run, PMF.map,
    Function.comp_def]

/-- Evaluating `worldRealize` on any `ProbOracleComp` forger in `world scheme sk` matches running
`runLoggedForger forger` against `forgerWorldImpl scheme sk` and then running `scheme.verify` on
the resulting cache. -/
theorem eval_world_worldRealize
    (scheme : Scheme PK SK M Sig Query Digest) (pk : PK) (sk : SK)
    (forger : ProbOracleComp (ForgerSpec M Query Sig Digest) (M × Sig))
    (accept : Bool → M × Sig → List (M × Sig) → Bool) :
    (world scheme sk).eval (worldRealize scheme pk forger accept) = (do
      let out ←
        ProbOracleComp.runWith (forgerWorldImpl scheme sk) (runLoggedForger forger) []
      let msig := out.1.1
      let pairs := out.1.2
      let cache := out.2
      let verified ← (interpret (oracle Digest) (scheme.verify pk msig.1 msig.2)).run cache
      return accept verified.1 msig pairs) := by
  unfold Interactive.World.eval worldRealize
  rw [ProbOracleComp.runWith_bind, runWith_world_liftProver, PMF.map_bind]
  refine PMF.bind_congr_on_support _ _ _ fun out _ => ?_
  rw [ProbOracleComp.runWith_bind, runWith_world_liftVerify, PMF.map_bind]
  refine PMF.bind_congr_on_support _ _ _ fun verified _ => ?_
  rw [ProbOracleComp.runWith_pure, PMF.pure_map]
  rfl

/-- Evaluating `worldRealize` on a lifted deterministic `OracleComp` forger in `world scheme sk`
matches running `logSigning` + `forgerWorldImpl` and then `scheme.verify` on the resulting cache. -/
theorem eval_world_worldRealize_liftOracleForger
    (scheme : Scheme PK SK M Sig Query Digest) (pk : PK) (sk : SK)
    (prog : OracleComp (ForgerSpec M Query Sig Digest) (M × Sig))
    (accept : Bool → M × Sig → List (M × Sig) → Bool) :
    (world scheme sk).eval (worldRealize scheme pk (liftOracleForger prog) accept) = (do
      let out ←
        ProbOracleComp.runWith (forgerWorldImpl scheme sk)
          (runLoggedForger (liftOracleForger prog)) []
      let msig := out.1.1
      let pairs := out.1.2
      let cache := out.2
      let verified ← (interpret (oracle Digest) (scheme.verify pk msig.1 msig.2)).run cache
      return accept verified.1 msig pairs) :=
  eval_world_worldRealize scheme pk sk (liftOracleForger prog) accept

/-! ### Security games (`eufCmaGame`, `eufCmaFinalMsgGame`, `ufCma0Game`, `sufCmaGame`) -/

/-- The random-oracle EUF-CMA experiment ([BonehShoup2023], Attack Game 13.1): the forger wins with
a valid signature, under the same oracle, on a message it never had signed. -/
noncomputable def eufCmaGame [DecidableEq M] (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) : PMF Bool := do
  let keys ← scheme.keyGen
  let s ← forger.coins
  let forged ← (interpret (handler scheme keys.2) (forger.forge keys.1 s)).run ([], [])
  let msig := forged.1
  let state := forged.2
  let verified ← (interpret (oracle Digest) (scheme.verify keys.1 msig.1 msig.2)).run
    state.1
  return (verified.1 && !(state.2.contains msig.1))

/-- The random-oracle EUF-CMA experiment with final-message admissibility guard `admissible`:
signing queries are answered on arbitrary messages `m : M`, and the forger wins when its final
candidate `(msg, sig)` satisfies `admissible msg`, verifies under the shared random oracle, and
satisfies `FreshOutputsOnFinalMessage` (`!queried.contains msg`). -/
noncomputable def eufCmaFinalMsgGame [DecidableEq M] (admissible : M → Bool)
    (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) : PMF Bool := do
  let keys ← scheme.keyGen
  let s ← forger.coins
  let forged ← (interpret (handler scheme keys.2) (forger.forge keys.1 s)).run ([], [])
  let msig := forged.1
  let state := forged.2
  let verified ← (interpret (oracle Digest) (scheme.verify keys.1 msig.1 msig.2)).run
    state.1
  return (admissible msig.1 && verified.1 && !(state.2.contains msig.1))

/-- Unconditional (all-message admissible) `eufCmaFinalMsgGame` is identical to `eufCmaGame`. -/
@[simp]
theorem eufCmaFinalMsgGame_true [DecidableEq M]
    (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) :
    eufCmaFinalMsgGame (fun _ => true) scheme forger = eufCmaGame scheme forger := by
  simp only [eufCmaFinalMsgGame, eufCmaGame, Bool.true_and]

/-- `eufCmaFinalMsgGame` is equivalent to evaluating `worldRealize` in `world scheme sk` for each
sampled key pair and forger coin tape. -/
theorem eufCmaFinalMsgGame_eq_worldGame [DecidableEq M] (admissible : M → Bool)
    (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) :
    eufCmaFinalMsgGame admissible scheme forger = (do
      let keys ← scheme.keyGen
      let s ← forger.coins
      Interactive.World.eval (world scheme keys.2)
        (worldRealize scheme keys.1 (liftOracleForger (forger.forge keys.1 s))
          (fun verified ⟨msg, _⟩ pairs =>
            admissible msg && verified && !(pairs.map Prod.fst).contains msg))) := by
  unfold eufCmaFinalMsgGame
  refine PMF.bind_congr_on_support _ _ _ fun keys _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun s _ => ?_
  rw [eval_world_worldRealize_liftOracleForger,
    ← runWith_world_runLoggedForger_liftOracleForger]
  simp only [PMF.monad_bind_eq_bind, PMF.bind_map]
  rfl

/-- `eufCmaGame` is equivalent to evaluating `worldRealize` in `world scheme sk` with the
unrestricted final-message freshness predicate `!(pairs.map Prod.fst).contains msg`. -/
theorem eufCmaGame_eq_worldGame [DecidableEq M]
    (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) :
    eufCmaGame scheme forger = (do
      let keys ← scheme.keyGen
      let s ← forger.coins
      Interactive.World.eval (world scheme keys.2)
        (worldRealize scheme keys.1 (liftOracleForger (forger.forge keys.1 s))
          (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg))) := by
  rw [← eufCmaFinalMsgGame_true, eufCmaFinalMsgGame_eq_worldGame]
  simp only [Bool.true_and]

/-- Restricting final-message admissibility can only decrease the forger's winning probability. -/
theorem eufCmaFinalMsgGame_apply_true_le [DecidableEq M] (admissible : M → Bool)
    (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) :
    (eufCmaFinalMsgGame admissible scheme forger) true ≤
      (eufCmaGame scheme forger) true := by
  unfold eufCmaFinalMsgGame eufCmaGame
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_apply]
  refine tsum_le_tsum fun keys => mul_le_mul_right ?_ _
  refine tsum_le_tsum fun s => mul_le_mul_right ?_ _
  refine tsum_le_tsum fun forged => mul_le_mul_right ?_ _
  refine tsum_le_tsum fun verified => mul_le_mul_right ?_ _
  rw [PMF.pure_apply, PMF.pure_apply]
  split_ifs <;> simp_all

/-- Key-only existential unforgeability (`ufCma0Game`): the forger wins when its candidate
forgery verifies and it made zero signing queries (`pairs.isEmpty`). -/
noncomputable def ufCma0Game (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) : PMF Bool := do
  let keys ← scheme.keyGen
  let s ← forger.coins
  Interactive.World.eval (world scheme keys.2)
    (worldRealize scheme keys.1 (liftOracleForger (forger.forge keys.1 s))
      (fun verified _ pairs => verified && pairs.isEmpty))

/-- Strong (fresh-pair) existential unforgeability under chosen-message attack (`sufCmaGame`):
the forger wins when its candidate `(msg, sig)` verifies and `(msg, sig)` was never returned by the
signing oracle (`!pairs.contains (msg, sig)`). -/
noncomputable def sufCmaGame [DecidableEq M] [DecidableEq Sig]
    (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) : PMF Bool := do
  let keys ← scheme.keyGen
  let s ← forger.coins
  Interactive.World.eval (world scheme keys.2)
    (worldRealize scheme keys.1 (liftOracleForger (forger.forge keys.1 s))
      (fun verified msig pairs => verified && !pairs.contains msig))

/-- Key-only strong existential unforgeability (`sufCma0Game`): the forger wins when its candidate
`(msg, sig)` verifies, `(msg, sig)` was never returned by the signing oracle, and the signing log
is empty (`pairs.isEmpty`). -/
noncomputable def sufCma0Game [DecidableEq M] [DecidableEq Sig]
    (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) : PMF Bool := do
  let keys ← scheme.keyGen
  let s ← forger.coins
  Interactive.World.eval (world scheme keys.2)
    (worldRealize scheme keys.1 (liftOracleForger (forger.forge keys.1 s))
      (fun verified msig pairs => verified && !pairs.contains msig && pairs.isEmpty))

/-- Key-only strong unforgeability `sufCma0Game` coincides with `ufCma0Game` because an empty
signing log contains no pairs. -/
@[simp]
theorem sufCma0Game_eq_ufCma0Game [DecidableEq M] [DecidableEq Sig]
    (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) :
    sufCma0Game scheme forger = ufCma0Game scheme forger := by
  have haccept :
      (fun (verified : Bool) (msig : M × Sig) (pairs : List (M × Sig)) =>
        verified && !pairs.contains msig && pairs.isEmpty) =
      (fun verified _ pairs => verified && pairs.isEmpty) := by
    funext verified msig pairs
    cases pairs <;> simp
  simp only [sufCma0Game, ufCma0Game, haccept]

/-! ### Completeness (`Scheme.Correct` and `Scheme.CorrectOn`) -/

/-- A scheme is correct when every honest signature verifies under the same oracle, from every
state of the oracle. -/
def Scheme.Correct (scheme : Scheme PK SK M Sig Query Digest) : Prop :=
  ∀ keys ∈ scheme.keyGen.support, ∀ m coins, coins ∈ (scheme.signCoins keys.2 m).support →
    ∀ cache, ∀ signed ∈ ((interpret (oracle Digest) (scheme.sign keys.2 m coins)).run
      cache).support, ∀ verified ∈ ((interpret (oracle Digest)
        (scheme.verify keys.1 m signed.1)).run signed.2).support, verified.1 = true

/-- A scheme is correct on messages satisfying `admissible` when every honest signature on an
admissible message verifies under the same oracle, from every state of the oracle. -/
def Scheme.CorrectOn (scheme : Scheme PK SK M Sig Query Digest) (admissible : M → Prop) : Prop :=
  ∀ keys ∈ scheme.keyGen.support, ∀ m, admissible m →
    ∀ coins, coins ∈ (scheme.signCoins keys.2 m).support →
    ∀ cache, ∀ signed ∈ ((interpret (oracle Digest) (scheme.sign keys.2 m coins)).run
      cache).support, ∀ verified ∈ ((interpret (oracle Digest)
        (scheme.verify keys.1 m signed.1)).run signed.2).support, verified.1 = true

/-- All-message correctness implies correctness on any admissible message predicate. -/
theorem Scheme.Correct.correctOn {scheme : Scheme PK SK M Sig Query Digest}
    (h : scheme.Correct) (admissible : M → Prop) :
    scheme.CorrectOn admissible :=
  fun keys hkeys m _ coins hcoins cache signed hsigned verified hverified =>
    h keys hkeys m coins hcoins cache signed hsigned verified hverified

/-- Correctness on `fun _ => True` is equivalent to unrestricted `Scheme.Correct`. -/
@[simp]
theorem Scheme.correctOn_true_iff (scheme : Scheme PK SK M Sig Query Digest) :
    scheme.CorrectOn (fun _ => True) ↔ scheme.Correct :=
  ⟨fun h keys hkeys m coins hcoins => h keys hkeys m trivial coins hcoins,
    fun h => h.correctOn (fun _ => True)⟩

end Cslib.Crypto.Protocols.ROMSignature

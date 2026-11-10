/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Identification
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrSignature
public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
public import CslibFrontier.Languages.Probabilistic.Forking
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform

/-!
# Fiat–Shamir non-interactive zero-knowledge proofs of knowledge in the random-oracle model

The Fiat–Shamir transformation ([FiatShamir1986]; [BonehShoup2023], Sections 20.3.3–20.3.5)
compiles a public-coin Sigma protocol `P : SigmaProtocol X Y T C Z` for a relation
`R : X → Y → Prop` into a non-interactive proof system in the random-oracle model: given a
witness-statement pair `(x, y)` and commitment coins `(t, st) ← P.commit x y`, the prover queries a
hash oracle `H : Y × T → C` on the pair `(y, t)` to obtain the challenge `c` and outputs
`(t, P.respond x y st c)` (`fiatShamirNIZKProve`); the verifier queries `H` at `(y, t)` and checks
`P.verify y t c z` (`fiatShamirNIZKVerify`). Binding *both* the statement `y` and the commitment `t`
in the hash query is essential when statements can be chosen adaptively after querying `H`: hashing
`t` alone fails soundness on protocols such as Schnorr's where a cheating prover can solve the
verification equation for `y` after seeing `H(t)`.

This module establishes the random-oracle security properties of Fiat–Shamir NIZK proofs as exact
probability laws over `OracleComp`:

1. **Completeness** (`fiatShamirNIZK_complete`, `fiatShamirNIZK_verify_of_prove`; [BonehShoup2023],
   Section 20.3.3): for every `(x, y)` with `R x y` and every initial random-oracle cache `cache`,
   running honest commitment sampling, `fiatShamirNIZKProve`, and `fiatShamirNIZKVerify` against the
   lazy uniform random oracle `ROMSignature.oracle C` accepts with probability `1`
   (`= PMF.pure true`).
2. **Adaptive multi-theorem zero knowledge in the programmable ROM** ([BonehShoup2023], Section
   20.3.5, Attack Game 20.3, Figure 20.2, and Theorem 20.3 / Equation (20.9)): an adaptive
   distinguisher queries `.inl (x, y)` for a proof (validated by an explicit Boolean relation
   checker `valid : X → Y → Bool` with `∀ x y, valid x y = true → R x y`, returning `none`
   identically in both experiments when `valid x y = false`) and `.inr (y, t)` for the random
   oracle. Under `P.SpecialHVZK R simulate` and `δ`-unpredictable commitments
   (`P.UnpredictableCommitments R δ`, Definition 19.7), replacing honest proving by the
   witness-free programmable-ROM simulator `nizkSimProve simulate` changes the acceptance
   probability of any distinguisher making at most `Qp` prove calls and `Qro` hash calls by at most
   `Qp * (Qp + Qro) * δ` (`abs_sub_fiatShamirNIZKRealGame_simGame_le`,
   `advantage_fiatShamirNIZKRealGame_simGame_le`). Concrete adaptation: whereas Figure 20.2 in
   [BonehShoup2023] outputs `fail` when a sampled commitment point `(y, t)` is already programmed in
   the random-oracle table, `nizkSimProve` overwrites `(y, t)` at the head of the association-list
   cache; the `IdenticalUntilBad` / `toOuterMeasure_bad_le` collision hop directly justifies this
   overwrite simulator.
3. **ROM proof of knowledge and derived simulation-extractability**:
   * *Plain ROM proof of knowledge* (`fiatShamirNIZKExtract`,
     `succProbability_fiatShamirNIZKPokGame_le`; [BonehShoup2023], Section 20.3.4, proved via the
     general forking inequality of [BellareNeven2006], Lemma 1): for an explicit-coin cheating
     prover making at most `Qro` hash calls on statement `y`, the acceptance probability `ε`
     satisfies `ε ≤ (Qro + 1) / |C| + √((Qro + 1) * ε')`, where `ε'` is the probability that
     rewinding outputs `some w` with `R w y`.
   * *Derived adaptive multi-theorem simulation-extractability* (`fiatShamirNIZKSimExtractWith`,
     `fiatShamirNIZKSimExtract`, `succProbability_fiatShamirNIZKRealExtGame_le`,
     `succProbability_fiatShamirNIZKSimExtGame_le`): derived here by combining our Attack Game 20.3
     zero-knowledge simulation hop, `SimCoinSource` presampling across forks, and
     [BellareNeven2006], Lemma 1 (rather than stated as a standalone theorem in [BonehShoup2023]).
     When an explicit-coin adversary also makes up to `Qp` adaptive prove calls and outputs
     `(y*, (t*, z*))` whose statement-commitment pair `(y*, t*)` was never returned by the prove
     oracle (which in particular holds whenever `y*` is a fresh statement), the witness-free
     rewinding extractor recovers `some (y*, w*)` with `R w* y*` with probability `ε'` satisfying
     `ε ≤ Qp * (Qp + Qro) * δ + (Qro + 1) / |C| + √((Qro + 1) * ε')` against real proofs (and
     `ε ≤ (Qro + 1) / |C| + √((Qro + 1) * ε')` against simulated proofs).

Specializations are provided for `SigmaProtocol.linear` and `SigmaProtocol.schnorr`, using an
explicit statement-independent simulator coin source (`linearSimCoinSource`) so that `linear` and
`schnorr` simulation-extractability require no finiteness assumption on the statement or group
carrier types.

All results are exact finite probability laws in the `OracleComp` random-oracle model; encoded
machine-level `IsPPT` efficiency bridges for multi-query rewinding reductions are separate.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.NIZKHashSpec`: statement-bound random-oracle query
  specification `(Y × T) → C`.
* `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKProve`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKVerify`: Fiat–Shamir non-interactive prover
  and verifier programs.
* `Cslib.Crypto.Protocols.SigmaProtocol.UnpredictableCommitments`: `δ`-unpredictable commitments
  on a relation.
* `Cslib.Crypto.Protocols.SigmaProtocol.NIZKDistinguisherSpec`,
  `Cslib.Crypto.Protocols.SigmaProtocol.NIZKCallBounded`: two-channel prove/hash oracle interface
  and separate call budgets.
* `Cslib.Crypto.Protocols.SigmaProtocol.nizkSimProve`,
  `Cslib.Crypto.Protocols.SigmaProtocol.nizkRealHandler`,
  `Cslib.Crypto.Protocols.SigmaProtocol.nizkSimHandler`,
  `Cslib.Crypto.Protocols.SigmaProtocol.nizkRealExtHandler`,
  `Cslib.Crypto.Protocols.SigmaProtocol.nizkSimExtHandler`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKRealGame`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKSimGame`: adaptive multi-theorem real and
  programmable-ROM simulated handlers and experiments.
* `Cslib.Crypto.Protocols.SigmaProtocol.NIZKProver`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKPokGame`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKExtract`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKExtractGame`: plain ROM proof-of-knowledge
  experiment and rewinding witness extractor.
* `Cslib.Crypto.Protocols.SigmaProtocol.SimCoinSource`,
  `Cslib.Crypto.Protocols.SigmaProtocol.SimCoinSource.ofFintype`,
  `Cslib.Crypto.Protocols.SigmaProtocol.linearSimCoinSource`: explicit coin sources for replaying
  adaptive multi-statement simulation across forks.
* `Cslib.Crypto.Protocols.SigmaProtocol.NIZKSimProver`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKRealExtGameOn`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKRealExtGame`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKSimExtGameOn`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKSimExtGame`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKSimExtractWith`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKSimExtract`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKSimExtractGame`: adaptive
  simulation-extractability experiments and witness-free rewinding extractors.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZK_verify_of_prove`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZK_complete`: perfect completeness in the lazy
  random-oracle model.
* `Cslib.Crypto.Protocols.SigmaProtocol.nizkRealHandler_inl_of_false`,
  `Cslib.Crypto.Protocols.SigmaProtocol.nizkSimHandler_inl_of_false`,
  `Cslib.Crypto.Protocols.SigmaProtocol.nizkSimHandler_inl_congr`: invalid queries return `none`
  identically and simulation ignores witness values beyond `valid x y`.
* `Cslib.Crypto.Protocols.SigmaProtocol.abs_sub_fiatShamirNIZKRealGame_simGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.advantage_fiatShamirNIZKRealGame_simGame_le`: adaptive
  multi-theorem NIZK zero-knowledge bound `Qp * (Qp + Qro) * δ`.
* `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKPokGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKPokKeyGen_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKPokGame_le_of_false`: plain
  ROM proof-of-knowledge, one-way key-generator reduction, and soundness on false statements.
* `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKSimExtGameOn_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKSimExtGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKRealExtGameOn_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKRealExtGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKFreshStmtGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKRealExtGameOn_le_of_false`:
  adaptive simulation-extractability and simulation-soundness bounds.
* `Cslib.Crypto.Protocols.SigmaProtocol.linear_unpredictableCommitments_of_injective`,
  `Cslib.Crypto.Protocols.SigmaProtocol.linear_advantage_fiatShamirNIZKRealGame_simGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.linear_succProbability_fiatShamirNIZKPokGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.linear_succProbability_fiatShamirNIZKRealExtGame_le`:
  specializations to `SigmaProtocol.linear`.
* `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_unpredictableCommitments`,
  `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_fiatShamirNIZK_complete`,
  `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_advantage_fiatShamirNIZKRealGame_simGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_succProbability_fiatShamirNIZKPokGame_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_succProbability_fiatShamirNIZKRealExtGame_le`:
  specializations to `SigmaProtocol.schnorr`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 19.6.1, 19.7, and 20.3.3–20.3.5 (Attack Game 20.3,
  Figure 20.2, and Theorem 20.3).
* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
* [A. Fiat, A. Shamir, *How to Prove Yourself: Practical Solutions to Identification and Signature
  Problems*][FiatShamir1986].
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability OracleComp ROMSignature
open scoped ENNReal NNReal

variable {X Y T C Z : Type}

/-! ### Non-interactive prover, verifier, and completeness -/

/-- Random-oracle query specification for Fiat–Shamir NIZK proofs
([BonehShoup2023], Section 20.3.3): every challenge query binds both the statement `y : Y` and the
commitment `t : T` and returns a challenge in `C`. -/
abbrev NIZKHashSpec (Y T C : Type) : OracleSpec (Y × T) :=
  fun _ : Y × T => C

/-- Fiat–Shamir non-interactive prover ([BonehShoup2023], Section 20.3.3): given witness `x`,
statement `y`, and commitment coins `(t, st)` sampled from `P.commit x y`, query the random oracle
at `(y, t)` for the challenge `c` and output `(t, P.respond x y st c)`. -/
@[expose] def fiatShamirNIZKProve (P : SigmaProtocol X Y T C Z) (x : X) (y : Y)
    (coins : T × P.State) : OracleComp (NIZKHashSpec Y T C) (T × Z) :=
  (fun c => (coins.1, P.respond x y coins.2 c)) <$>
    OracleComp.query (spec := NIZKHashSpec Y T C) (y, coins.1)

/-- Fiat–Shamir non-interactive verifier ([BonehShoup2023], Section 20.3.3): query the random
oracle at `(y, prf.1)` for the challenge `c` and check `P.verify y prf.1 c prf.2`. -/
@[expose] def fiatShamirNIZKVerify (P : SigmaProtocol X Y T C Z) (y : Y) (prf : T × Z) :
    OracleComp (NIZKHashSpec Y T C) Bool :=
  (fun c => P.verify y prf.1 c prf.2) <$>
    OracleComp.query (spec := NIZKHashSpec Y T C) (y, prf.1)

/-- Support-level completeness of Fiat–Shamir NIZK proofs: for any `(x, y)` in `R`, any supported
commitment coins, and any initial random-oracle cache, every proof produced by
`fiatShamirNIZKProve` is accepted by `fiatShamirNIZKVerify` under the updated cache. -/
theorem fiatShamirNIZK_verify_of_prove [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop} (hP : P.Complete R)
    {x : X} {y : Y} (hxy : R x y) {coins : T × P.State} (hcoins : coins ∈ (P.commit x y).support)
    (cache : List ((Y × T) × C))
    {proved : (T × Z) × List ((Y × T) × C)}
    (hproved :
      proved ∈ ((interpret (oracle C) (fiatShamirNIZKProve P x y coins)).run cache).support)
    {verified : Bool × List ((Y × T) × C)}
    (hverified :
      verified ∈
        ((interpret (oracle C) (fiatShamirNIZKVerify P y proved.1)).run proved.2).support) :
    verified.1 = true := by
  simp only [fiatShamirNIZKProve, fiatShamirNIZKVerify, interpret_map, interpret_query,
    StateT.run_map, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hproved hverified
  obtain ⟨r, hr, rfl⟩ := hproved
  obtain ⟨r', hr', rfl⟩ := hverified
  have hlookup := lookup_of_mem_support_oracle hr
  change r' ∈ (oracle C (y, coins.1) r.2).support at hr'
  rw [oracle, memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure,
    PMF.mem_support_pure_iff] at hr'
  subst hr'
  exact hP.accepts_of_mem_support_commit hxy hcoins r.1

/-- **Perfect completeness** of Fiat–Shamir NIZK proofs in the lazy random-oracle model
([BonehShoup2023], Section 20.3.3): for any `(x, y)` satisfying `R x y` and any initial cache
`cache`, sampling commitment coins, proving, and verifying in sequence against `oracle C` accepts
with probability `1`. -/
theorem fiatShamirNIZK_complete [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop} (hP : P.Complete R)
    {x : X} {y : Y} (hxy : R x y) (cache : List ((Y × T) × C)) :
    (do
      let coins ← P.commit x y
      let (prf, cache') ← (interpret (oracle C) (fiatShamirNIZKProve P x y coins)).run cache
      let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache'
      return acc) = PMF.pure true := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine (Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true)
    fun coins hcoins => ?_).trans (PMF.bind_const _ _)
  refine (Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true)
    fun proved hproved => ?_).trans (PMF.bind_const _ _)
  refine (Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true)
    fun verified hverified => ?_).trans (PMF.bind_const _ _)
  exact congrArg PMF.pure (fiatShamirNIZK_verify_of_prove hP hxy hcoins cache hproved hverified)

/-! ### Unpredictable commitments and adaptive multi-theorem zero knowledge -/

/-- Commitments of `P` are `δ`-unpredictable on `R` ([BonehShoup2023], Definition 19.7): for every
witness-statement pair `(x, y)` in `R`, no commitment value occurs with probability greater than
`δ`. -/
@[expose] def UnpredictableCommitments (P : SigmaProtocol X Y T C Z) (R : X → Y → Prop)
    (δ : ℝ≥0) : Prop :=
  ∀ x y, R x y → ∀ t, (P.commit x y).map Prod.fst t ≤ (δ : ℝ≥0∞)

/-- Monotonicity of `UnpredictableCommitments` in both the relation and the collision bound. -/
theorem UnpredictableCommitments.mono {P : SigmaProtocol X Y T C Z} {R R' : X → Y → Prop}
    {δ δ' : ℝ≥0} (h : P.UnpredictableCommitments R δ) (hR : ∀ x y, R' x y → R x y)
    (hδ : δ ≤ δ') : P.UnpredictableCommitments R' δ' :=
  fun x y hxy t => (h x y (hR x y hxy) t).trans (ENNReal.coe_le_coe.mpr hδ)

/-- Two-channel oracle specification for adaptive multi-theorem Fiat–Shamir NIZK experiments
([BonehShoup2023], Section 20.3.5, Attack Game 20.3): `.inl (x, y)` requests a proof for candidate
witness-statement pair `(x, y)` (returning `Option (T × Z)`) and `.inr (y, t)` queries the random
oracle at `(y, t)` (returning `C`). -/
abbrev NIZKDistinguisherSpec (X Y T C Z : Type) : OracleSpec ((X × Y) ⊕ (Y × T)) :=
  (fun _ : X × Y => Option (T × Z)) ⊕ₒ NIZKHashSpec Y T C

/-- Separate prove-query (`Qp`) and hash-query (`Qro`) budgets for an `OracleComp` over
`NIZKDistinguisherSpec`. -/
@[expose] def NIZKCallBounded {α : Type}
    (program : OracleComp (NIZKDistinguisherSpec X Y T C Z) α) (Qp Qro : ℕ) : Prop :=
  IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program Qp ∧
    IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program Qro

/-- A program making at most `Qp` prove calls and `Qro` hash calls makes at most `Qp + Qro` calls
in total. -/
theorem NIZKCallBounded.isQueryBounded {α : Type}
    {program : OracleComp (NIZKDistinguisherSpec X Y T C Z) α} {Qp Qro : ℕ}
    (h : NIZKCallBounded program Qp Qro) : IsQueryBounded program (Qp + Qro) :=
  (h.1.add h.2).of_le fun q => by cases q <;> simp

/-- Witness-free programmable-ROM proof simulation on statement `y` ([BonehShoup2023], Section
20.3.5, adapted from Figure 20.2): sample a uniform challenge `c ← C`, sample
`(t, z) ← simulate y c`, program `(y, t) ↦ c` at the front of the random-oracle cache (overwriting
any existing binding rather than returning `fail`), and return `(t, z)`. -/
@[expose] noncomputable def nizkSimProve [Fintype C] [Nonempty C]
    (simulate : Y → C → PMF (T × Z)) (y : Y) :
    StateT (List ((Y × T) × C)) PMF (T × Z) := fun cache => do
  let c ← PMF.uniformOfFintype C
  let (t, z) ← simulate y c
  return ((t, z), ((y, t), c) :: cache)

/-- Real multi-theorem NIZK oracle handler ([BonehShoup2023], Attack Game 20.3): invalid witness
candidates (`valid x y = false`) return `none` without touching the random-oracle cache; valid
pairs sample honest commitment coins and run `fiatShamirNIZKProve` against `oracle C`. -/
@[expose] noncomputable def nizkRealHandler [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) :
    (q : (X × Y) ⊕ (Y × T)) →
      StateT (List ((Y × T) × C)) PMF (NIZKDistinguisherSpec X Y T C Z q)
  | .inl (x, y) => fun cache =>
    if valid x y then do
      let coins ← P.commit x y
      let (prf, cache') ← (interpret (oracle C) (fiatShamirNIZKProve P x y coins)).run cache
      return (some prf, cache')
    else
      PMF.pure (none, cache)
  | .inr yt => oracle C yt

/-- Programmable-ROM simulated multi-theorem NIZK oracle handler ([BonehShoup2023], Attack Game
20.3, using the overwrite adaptation of Figure 20.2): invalid witness candidates
(`valid x y = false`) return `none` identically without touching the cache; valid pairs run the
witness-free simulator `nizkSimProve simulate y`. -/
@[expose] noncomputable def nizkSimHandler [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (simulate : Y → C → PMF (T × Z)) (valid : X → Y → Bool) :
    (q : (X × Y) ⊕ (Y × T)) →
      StateT (List ((Y × T) × C)) PMF (NIZKDistinguisherSpec X Y T C Z q)
  | .inl (x, y) => fun cache =>
    if valid x y then do
      let (prf, cache') ← nizkSimProve simulate y cache
      return (some prf, cache')
    else
      PMF.pure (none, cache)
  | .inr yt => oracle C yt

/-- Invalid prove queries return `none` without modifying the cache in `nizkRealHandler`. -/
@[simp] theorem nizkRealHandler_inl_of_false [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) {valid : X → Y → Bool} {x : X} {y : Y}
    (h : valid x y = false) (cache : List ((Y × T) × C)) :
    nizkRealHandler P valid (.inl (x, y)) cache = PMF.pure (none, cache) := by
  simp only [nizkRealHandler, h, Bool.false_eq_true, ↓reduceIte]

/-- Invalid prove queries return `none` without modifying the cache in `nizkSimHandler`. -/
@[simp] theorem nizkSimHandler_inl_of_false [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (simulate : Y → C → PMF (T × Z)) {valid : X → Y → Bool} {x : X} {y : Y}
    (h : valid x y = false) (cache : List ((Y × T) × C)) :
    nizkSimHandler simulate valid (.inl (x, y)) cache = PMF.pure (none, cache) := by
  simp only [nizkSimHandler, h, Bool.false_eq_true, ↓reduceIte]

/-- Witness-invariance of `nizkSimHandler`: two witness candidates `x₁, x₂` with the same validity
bit `valid x₁ y = valid x₂ y` induce identical simulated prove transitions. -/
theorem nizkSimHandler_inl_congr [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    (simulate : Y → C → PMF (T × Z)) {valid : X → Y → Bool} {x₁ x₂ : X} {y : Y}
    (h : valid x₁ y = valid x₂ y) (cache : List ((Y × T) × C)) :
    nizkSimHandler simulate valid (.inl (x₁, y)) cache =
      nizkSimHandler simulate valid (.inl (x₂, y)) cache := by
  simp only [nizkSimHandler, h]

/-- Real adaptive multi-theorem NIZK experiment ([BonehShoup2023], Attack Game 20.3, Experiment
0). -/
@[expose] noncomputable def fiatShamirNIZKRealGame [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool)
    (D : OracleComp (NIZKDistinguisherSpec X Y T C Z) Bool) : Game := do
  let (b, _) ← (interpret (nizkRealHandler P valid) D).run []
  return b

/-- Simulated adaptive multi-theorem NIZK experiment in the programmable random-oracle model
([BonehShoup2023], Attack Game 20.3, Experiment 1, with the overwrite simulator `nizkSimProve`). -/
@[expose] noncomputable def fiatShamirNIZKSimGame [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (simulate : Y → C → PMF (T × Z)) (valid : X → Y → Bool)
    (D : OracleComp (NIZKDistinguisherSpec X Y T C Z) Bool) : Game := do
  let (b, _) ← (interpret (nizkSimHandler simulate valid) D).run []
  return b

/-! ### Shared game-hop handlers (logging proved `(y, t)` pairs and collision flag) -/

/-- State of the logged adaptive experiment: the random-oracle cache paired with the list of
statement-commitment pairs `(y, t)` returned by valid prove queries. -/
private abbrev ExtGameState (Y T C : Type) := List ((Y × T) × C) × List (Y × T)

/-- Logged real prove/hash handler, recording `(y, t)` on each valid prove query. -/
@[expose] noncomputable def nizkRealExtHandler [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) :
    (q : (X × Y) ⊕ (Y × T)) →
      StateT (List ((Y × T) × C) × List (Y × T)) PMF (NIZKDistinguisherSpec X Y T C Z q)
  | .inl (x, y) => fun (cache, proved) =>
    if valid x y then do
      let coins ← P.commit x y
      let (prf, cache') ← (interpret (oracle C) (fiatShamirNIZKProve P x y coins)).run cache
      return (some prf, (cache', (y, prf.1) :: proved))
    else
      PMF.pure (none, (cache, proved))
  | .inr yt => fun (cache, proved) =>
    (oracle C yt cache).map fun (c, cache') => (c, (cache', proved))

/-- Logged programmable-ROM simulated prove/hash handler, recording `(y, t)` on each valid prove
query. -/
@[expose] noncomputable def nizkSimExtHandler [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (simulate : Y → C → PMF (T × Z)) (valid : X → Y → Bool) :
    (q : (X × Y) ⊕ (Y × T)) →
      StateT (List ((Y × T) × C) × List (Y × T)) PMF (NIZKDistinguisherSpec X Y T C Z q)
  | .inl (x, y) => fun (cache, proved) =>
    if valid x y then do
      let (prf, cache') ← nizkSimProve simulate y cache
      return (some prf, (cache', (y, prf.1) :: proved))
    else
      PMF.pure (none, (cache, proved))
  | .inr yt => fun (cache, proved) =>
    (oracle C yt cache).map fun (c, cache') => (c, (cache', proved))

/-- Flagged real handler raising `bad` when a valid prove commitment hits an existing cache
entry. -/
private noncomputable def realFlaggedHandler [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) :
    (q : (X × Y) ⊕ (Y × T)) →
      StateT (ExtGameState Y T C × Bool) PMF (NIZKDistinguisherSpec X Y T C Z q)
  | .inl (x, y) => fun st =>
    if valid x y then
      (P.commit x y).bind fun ts =>
        (oracle C (y, ts.1) st.1.1).map fun r =>
          (some (ts.1, P.respond x y ts.2 r.1),
            ((r.2, (y, ts.1) :: st.1.2), st.2 || (st.1.1.lookup (y, ts.1)).isSome))
    else
      PMF.pure (none, st)
  | .inr yt => fun st =>
    (oracle C yt st.1.1).map fun r => (r.1, ((r.2, st.1.2), st.2))

/-- Flagged programming handler setting `(y, t) ↦ c` to a fresh uniform challenge on valid prove
queries, raising the same `bad` flag on cache collisions. -/
private noncomputable def programFlaggedHandler [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) :
    (q : (X × Y) ⊕ (Y × T)) →
      StateT (ExtGameState Y T C × Bool) PMF (NIZKDistinguisherSpec X Y T C Z q)
  | .inl (x, y) => fun st =>
    if valid x y then
      (P.commit x y).bind fun ts =>
        (PMF.uniformOfFintype C).map fun c =>
          (some (ts.1, P.respond x y ts.2 c),
            ((((y, ts.1), c) :: st.1.1, (y, ts.1) :: st.1.2),
              st.2 || (st.1.1.lookup (y, ts.1)).isSome))
    else
      PMF.pure (none, st)
  | .inr yt => fun st =>
    (oracle C yt st.1.1).map fun r => (r.1, ((r.2, st.1.2), st.2))

/-- Projecting away the proved-pair log from `nizkRealExtHandler` recovers `nizkRealHandler`. -/
private theorem nizkRealExtHandler_map_cache [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool)
    (q : (X × Y) ⊕ (Y × T)) (st : ExtGameState Y T C) :
    (nizkRealExtHandler P valid q st).map (fun (a, s') => (a, s'.1)) =
      nizkRealHandler P valid q st.1 := by
  obtain ⟨cache, proved⟩ := st
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · simp only [nizkRealExtHandler, nizkRealHandler, hv, ↓reduceIte, PMF.monad_bind_eq_bind,
        PMF.monad_pure_eq_pure, PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun coins => ?_)
      refine congrArg (PMF.bind _) (funext fun (prf, cache') => ?_)
      simp only [PMF.pure_map]
    · simp only [Bool.not_eq_true] at hv
      simp only [nizkRealExtHandler, nizkRealHandler, hv, Bool.false_eq_true, ↓reduceIte,
        PMF.pure_map]
  | inr yt =>
    simp only [nizkRealExtHandler, nizkRealHandler, PMF.map_comp]
    exact PMF.map_id _

/-- Projecting away the proved-pair log from `nizkSimExtHandler` recovers `nizkSimHandler`. -/
private theorem nizkSimExtHandler_map_cache [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (simulate : Y → C → PMF (T × Z)) (valid : X → Y → Bool)
    (q : (X × Y) ⊕ (Y × T)) (st : ExtGameState Y T C) :
    (nizkSimExtHandler simulate valid q st).map (fun (a, s') => (a, s'.1)) =
      nizkSimHandler simulate valid q st.1 := by
  obtain ⟨cache, proved⟩ := st
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · simp only [nizkSimExtHandler, nizkSimHandler, hv, ↓reduceIte, PMF.monad_bind_eq_bind,
        PMF.monad_pure_eq_pure, PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun (prf, cache') => ?_)
      simp only [PMF.pure_map]
    · simp only [Bool.not_eq_true] at hv
      simp only [nizkSimExtHandler, nizkSimHandler, hv, Bool.false_eq_true, ↓reduceIte,
        PMF.pure_map]
  | inr yt =>
    simp only [nizkSimExtHandler, nizkSimHandler, PMF.map_comp]
    exact PMF.map_id _

/-- Forgetting the collision flag on `realFlaggedHandler` yields `nizkRealExtHandler`. -/
private theorem realFlaggedHandler_map [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool)
    (q : (X × Y) ⊕ (Y × T)) (st : ExtGameState Y T C × Bool) :
    (realFlaggedHandler P valid q st).map (fun x => (x.1, x.2.1)) =
      nizkRealExtHandler P valid q st.1 := by
  obtain ⟨⟨cache, proved⟩, flag⟩ := st
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · simp only [realFlaggedHandler, nizkRealExtHandler, fiatShamirNIZKProve, hv, ↓reduceIte,
        interpret_map, interpret_query, StateT.run_map, PMF.monad_bind_eq_bind,
        PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind, PMF.map_comp, PMF.bind_map,
        Function.comp_def]
      exact congrArg (PMF.bind _) (funext fun ts => (PMF.bind_pure_comp _ _).symm)
    · simp only [Bool.not_eq_true] at hv
      simp only [realFlaggedHandler, nizkRealExtHandler, hv, Bool.false_eq_true, ↓reduceIte,
        PMF.pure_map]
  | inr yt =>
    simp only [realFlaggedHandler, nizkRealExtHandler, PMF.map_comp, Function.comp_def]

/-- Under `SpecialHVZK` and `hvalid`, forgetting the collision flag on `programFlaggedHandler`
yields `nizkSimExtHandler`. -/
private theorem programFlaggedHandler_map [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)}
    {valid : X → Y → Bool} (hvalid : ∀ x y, valid x y = true → R x y)
    (hHVZK : P.SpecialHVZK R simulate)
    (q : (X × Y) ⊕ (Y × T)) (st : ExtGameState Y T C × Bool) :
    (programFlaggedHandler P valid q st).map (fun x => (x.1, x.2.1)) =
      nizkSimExtHandler simulate valid q st.1 := by
  obtain ⟨⟨cache, proved⟩, flag⟩ := st
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · simp only [programFlaggedHandler, nizkSimExtHandler, nizkSimProve, hv, ↓reduceIte,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map_comp, PMF.bind_bind,
        PMF.pure_bind, Function.comp_def]
      have htr := hHVZK.transcript_eq x y (hvalid x y hv)
      conv_rhs =>
        enter [2, c]
        rw [htr c, SigmaProtocol.transcript, PMF.bind_map]
      rw [PMF.bind_comm]
      exact congrArg (PMF.bind _) (funext fun ts => (PMF.bind_pure_comp _ _).symm)
    · simp only [Bool.not_eq_true] at hv
      simp only [programFlaggedHandler, nizkSimExtHandler, hv, Bool.false_eq_true, ↓reduceIte,
        PMF.pure_map]
  | inr yt =>
    simp only [programFlaggedHandler, nizkSimExtHandler, PMF.map_comp, Function.comp_def]

/-- `realFlaggedHandler` and `programFlaggedHandler` are identical until the collision flag is
raised. -/
private theorem identicalUntilBad_flaggedHandlers [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) :
    IdenticalUntilBad (realFlaggedHandler P valid) (programFlaggedHandler P valid)
      fun st => st.2 = true where
  agree q st _ a st' hst' := by
    cases q with
    | inr yt => rfl
    | inl xy =>
      obtain ⟨x, y⟩ := xy
      by_cases hv : valid x y = true
      · simp only [realFlaggedHandler, programFlaggedHandler, hv, ↓reduceIte, PMF.bind_apply]
        refine tsum_congr fun ts => congrArg (_ * ·) ?_
        cases hlookup : st.1.1.lookup (y, ts.1) with
        | some c =>
          refine ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).trans
            ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).symm <;>
          · obtain ⟨r, -, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
            exact hst' (by rw [← (Prod.mk.inj hr).2]; simp)
        | none =>
          rw [oracle, memoize_of_none _ _ _ hlookup]
          simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
          exact DFunLike.congr_fun (PMF.bind_pure_comp _ _) _
      · simp only [Bool.not_eq_true] at hv
        simp only [realFlaggedHandler, programFlaggedHandler, hv, Bool.false_eq_true, ↓reduceIte]
  absorb_first q st hst out hout := by
    cases q with
    | inl xy =>
      obtain ⟨x, y⟩ := xy
      by_cases hv : valid x y = true
      · simp only [realFlaggedHandler, hv, ↓reduceIte] at hout
        obtain ⟨ts, -, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
        obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
        simp [hst]
      · simp only [Bool.not_eq_true] at hv
        simp only [realFlaggedHandler, hv, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_pure_iff] at hout
        subst hout
        exact hst
    | inr yt =>
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      exact hst
  absorb_second q st hst out hout := by
    cases q with
    | inl xy =>
      obtain ⟨x, y⟩ := xy
      by_cases hv : valid x y = true
      · simp only [programFlaggedHandler, hv, ↓reduceIte] at hout
        obtain ⟨ts, -, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
        obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
        simp [hst]
      · simp only [Bool.not_eq_true] at hv
        simp only [programFlaggedHandler, hv, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_pure_iff] at hout
        subst hout
        exact hst
    | inr yt =>
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      exact hst

/-- Union bound for a commitment hitting an existing cache entry at `(y, ·)`. -/
private theorem toOuterMeasure_lookup_commit_le [DecidableEq Y] [DecidableEq T]
    (P : SigmaProtocol X Y T C Z) {x : X} {y : Y} {δ : ℝ≥0∞}
    (hcommit : ∀ t, (P.commit x y).map Prod.fst t ≤ δ) (cache : List ((Y × T) × C)) :
    (P.commit x y).toOuterMeasure {ts | (cache.lookup (y, ts.1)).isSome} ≤
      cache.length * δ := by
  induction cache with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨⟨y', t'⟩, c⟩ := e
    calc (P.commit x y).toOuterMeasure
          {ts | ((((y', t'), c) :: rest).lookup (y, ts.1)).isSome}
        ≤ (P.commit x y).toOuterMeasure
          ({ts | ts.1 = t'} ∪ {ts | (rest.lookup (y, ts.1)).isSome}) := by
          refine (P.commit x y).toOuterMeasure.mono fun ts hts => ?_
          have hts : ((((y', t'), c) :: rest).lookup (y, ts.1)).isSome = true := hts
          rw [List.lookup_cons] at hts
          by_cases h : (y, ts.1) = (y', t')
          · exact Or.inl (Prod.ext_iff.mp h).2
          · rw [beq_false_of_ne h] at hts
            exact Or.inr hts
      _ ≤ (P.commit x y).toOuterMeasure {ts | ts.1 = t'} +
          (P.commit x y).toOuterMeasure {ts | (rest.lookup (y, ts.1)).isSome} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ δ + rest.length * δ := by
          refine add_le_add ?_ ih
          rw [show {ts : T × P.State | ts.1 = t'} = Prod.fst ⁻¹' {t'} from rfl,
            ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
          exact hcommit t'
      _ = (((y', t'), c) :: rest).length * δ := by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Under `UnpredictableCommitments R δ` and `hvalid`, a program with budgets `(Qp, Qro)` raises
the collision flag of `realFlaggedHandler` with probability at most `Qp * (Qp + Qro) * δ`. -/
private theorem toOuterMeasure_flag_le_nizk [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop} {valid : X → Y → Bool}
    {δ : ℝ≥0} (hvalid : ∀ x y, valid x y = true → R x y)
    (hUnpred : P.UnpredictableCommitments R δ) {α : Type}
    {program : OracleComp (NIZKDistinguisherSpec X Y T C Z) α} {Qp Qro : ℕ}
    (hcall : NIZKCallBounded program Qp Qro) :
    ((interpret (realFlaggedHandler P valid) program).run (([], []), false)).toOuterMeasure
      {x | x.2.2 = true} ≤ (Qp * (Qp + Qro) : ℕ) * (δ : ℝ≥0∞) := by
  have h := toOuterMeasure_bad_le (handler := realFlaggedHandler P valid)
    (bad := fun st => st.2 = true)
    (Sum.elim (fun _ => 1) (fun _ => 0))
    (fun st => st.1.1.length * (δ : ℝ≥0∞)) (δ : ℝ≥0∞) ?_ ?_
    hcall.isQueryBounded hcall.1 (s := (([], []), false)) (by simp)
  · calc _ ≤ (Qp : ℝ≥0∞) * (0 + (Qp + Qro : ℕ) * (δ : ℝ≥0∞)) := by simpa using h
      _ = (Qp * (Qp + Qro) : ℕ) * (δ : ℝ≥0∞) := by push_cast; ring
  · intro q st hst
    cases q with
    | inl xy =>
      obtain ⟨x, y⟩ := xy
      rw [Sum.elim_inl, Nat.cast_one, one_mul]
      by_cases hv : valid x y = true
      · simp only [realFlaggedHandler, hv, ↓reduceIte, PMF.toOuterMeasure_bind_apply]
        calc ∑' ts, (P.commit x y) ts *
              ((oracle C (y, ts.1) st.1.1).map fun r =>
                (some (ts.1, P.respond x y ts.2 r.1),
                  ((r.2, (y, ts.1) :: st.1.2),
                    st.2 || (st.1.1.lookup (y, ts.1)).isSome))).toOuterMeasure
                {out | out.2.2 = true}
            ≤ ∑' ts, (P.commit x y) ts *
                {ts : T × P.State | (st.1.1.lookup (y, ts.1)).isSome}.indicator 1 ts := by
              refine tsum_le_tsum fun ts => mul_le_mul_of_nonneg_left ?_ zero_le
              by_cases hts : (st.1.1.lookup (y, ts.1)).isSome
              · rw [Set.indicator_of_mem
                  (show ts ∈ {ts : T × P.State | (st.1.1.lookup (y, ts.1)).isSome} from hts),
                  Pi.one_apply]
                exact Probability.PMF.toOuterMeasure_le_one _ _
              · rw [Set.indicator_of_notMem
                  (show ts ∉ {ts : T × P.State | (st.1.1.lookup (y, ts.1)).isSome} from hts)]
                refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_)
                refine Set.disjoint_left.mpr fun out hout hbad => ?_
                obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
                simp_all
          _ = (P.commit x y).toOuterMeasure {ts | (st.1.1.lookup (y, ts.1)).isSome} := by
              rw [PMF.toOuterMeasure_apply]
              refine tsum_congr fun ts => ?_
              by_cases hts : (st.1.1.lookup (y, ts.1)).isSome
              · rw [Set.indicator_of_mem
                  (show ts ∈ {ts : T × P.State | (st.1.1.lookup (y, ts.1)).isSome} from hts),
                  Set.indicator_of_mem
                  (show ts ∈ {ts : T × P.State | (st.1.1.lookup (y, ts.1)).isSome} from hts),
                  Pi.one_apply, mul_one]
              · rw [Set.indicator_of_notMem
                  (show ts ∉ {ts : T × P.State | (st.1.1.lookup (y, ts.1)).isSome} from hts),
                  Set.indicator_of_notMem
                  (show ts ∉ {ts : T × P.State | (st.1.1.lookup (y, ts.1)).isSome} from hts),
                  mul_zero]
          _ ≤ st.1.1.length * (δ : ℝ≥0∞) :=
              toOuterMeasure_lookup_commit_le P (hUnpred x y (hvalid x y hv)) st.1.1
      · simp only [Bool.not_eq_true] at hv
        simp only [realFlaggedHandler, hv, Bool.false_eq_true, ↓reduceIte,
          PMF.toOuterMeasure_pure_apply]
        split_ifs with hbad
        · exact absurd hbad hst
        · exact zero_le
    | inr yt =>
      refine le_of_eq_of_le ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_) zero_le
      refine Set.disjoint_left.mpr fun out hout hbad => hst ?_
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      exact hbad
  · intro q st _ out hout _
    have hlen : out.2.1.1.length ≤ st.1.1.length + 1 := by
      cases q with
      | inl xy =>
        obtain ⟨x, y⟩ := xy
        by_cases hv : valid x y = true
        · simp only [realFlaggedHandler, hv, ↓reduceIte] at hout
          obtain ⟨ts, -, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
          obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
          exact length_le_of_mem_support_oracle hr
        · simp only [Bool.not_eq_true] at hv
          simp only [realFlaggedHandler, hv, Bool.false_eq_true, ↓reduceIte,
            PMF.mem_support_pure_iff] at hout
          subst hout
          exact Nat.le_succ _
      | inr yt =>
        obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
        exact length_le_of_mem_support_oracle hr
    calc (out.2.1.1.length : ℝ≥0∞) * (δ : ℝ≥0∞)
        ≤ ((st.1.1.length + 1 : ℕ) : ℝ≥0∞) * (δ : ℝ≥0∞) := by gcongr
      _ = st.1.1.length * (δ : ℝ≥0∞) + (δ : ℝ≥0∞) := by
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- Two-sided difference bound between continuing from `nizkRealExtHandler` and continuing from
`nizkSimExtHandler`. -/
private theorem abs_sub_extHandlers_bind_le [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)}
    {valid : X → Y → Bool} {δ : ℝ≥0}
    (hvalid : ∀ x y, valid x y = true → R x y)
    (hHVZK : P.SpecialHVZK R simulate)
    (hUnpred : P.UnpredictableCommitments R δ) {α β : Type}
    {program : OracleComp (NIZKDistinguisherSpec X Y T C Z) α} {Qp Qro : ℕ}
    (hcall : NIZKCallBounded program Qp Qro) (next : α × ExtGameState Y T C → PMF β) (b : β) :
    |(((interpret (nizkRealExtHandler P valid) program).run ([], [])).bind next b).toReal -
        (((interpret (nizkSimExtHandler simulate valid) program).run ([], [])).bind
          next b).toReal| ≤
      Qp * (Qp + Qro) * δ := by
  have hreal := run_interpret_map_state (realFlaggedHandler P valid)
    (nizkRealExtHandler P valid) Prod.fst (realFlaggedHandler_map P valid) program
    (([], []), false)
  have hsim := run_interpret_map_state (programFlaggedHandler P valid)
    (nizkSimExtHandler simulate valid) Prod.fst (programFlaggedHandler_map hvalid hHVZK) program
    (([], []), false)
  rw [← hreal, ← hsim, PMF.bind_map, PMF.bind_map]
  have hdiff := (identicalUntilBad_flaggedHandlers P valid).abs_sub_le program (([], []), false)
    (next ∘ fun (a, s) => (a, s.1)) b
  have hflag := toOuterMeasure_flag_le_nizk hvalid hUnpred hcall
  have htop : ((Qp * (Qp + Qro) : ℕ) : ℝ≥0∞) * (δ : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top
  refine hdiff.trans ((ENNReal.toReal_mono htop hflag).trans_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal]
  push_cast
  ring

/-- One-sided `ℝ≥0∞` bound between continuing from `nizkRealExtHandler` and continuing from
`nizkSimExtHandler`. -/
private theorem extHandlers_bind_apply_le [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)}
    {valid : X → Y → Bool} {δ : ℝ≥0}
    (hvalid : ∀ x y, valid x y = true → R x y)
    (hHVZK : P.SpecialHVZK R simulate)
    (hUnpred : P.UnpredictableCommitments R δ) {α β : Type}
    {program : OracleComp (NIZKDistinguisherSpec X Y T C Z) α} {Qp Qro : ℕ}
    (hcall : NIZKCallBounded program Qp Qro) (next : α × ExtGameState Y T C → PMF β) (b : β) :
    ((interpret (nizkRealExtHandler P valid) program).run ([], [])).bind next b ≤
      ((interpret (nizkSimExtHandler simulate valid) program).run ([], [])).bind next b +
        (Qp * (Qp + Qro) : ℕ) * (δ : ℝ≥0∞) := by
  have hreal := run_interpret_map_state (realFlaggedHandler P valid)
    (nizkRealExtHandler P valid) Prod.fst (realFlaggedHandler_map P valid) program
    (([], []), false)
  have hsim := run_interpret_map_state (programFlaggedHandler P valid)
    (nizkSimExtHandler simulate valid) Prod.fst (programFlaggedHandler_map hvalid hHVZK) program
    (([], []), false)
  rw [← hreal, ← hsim, PMF.bind_map, PMF.bind_map]
  exact ((identicalUntilBad_flaggedHandlers P valid).bind_apply_le program (([], []), false)
    (next ∘ fun (a, s) => (a, s.1)) b).trans
      (add_le_add le_rfl (toOuterMeasure_flag_le_nizk hvalid hUnpred hcall))

/-- **Adaptive multi-theorem zero knowledge** of Fiat–Shamir NIZK proofs in the programmable
random-oracle model ([BonehShoup2023], Section 20.3.5, Theorem 20.3 / Equation (20.9), adapted via
`IdenticalUntilBad` to the overwrite simulator `nizkSimProve`): under `SpecialHVZK` and
`δ`-unpredictable commitments, any adaptive distinguisher making at most `Qp` prove calls and `Qro`
direct hash calls distinguishes `fiatShamirNIZKRealGame` from `fiatShamirNIZKSimGame` with
acceptance-probability difference at most `Qp * (Qp + Qro) * δ`. -/
theorem abs_sub_fiatShamirNIZKRealGame_simGame_le [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop}
    {simulate : Y → C → PMF (T × Z)} {valid : X → Y → Bool} {δ : ℝ≥0}
    (hvalid : ∀ x y, valid x y = true → R x y)
    (hHVZK : P.SpecialHVZK R simulate)
    (hUnpred : P.UnpredictableCommitments R δ)
    {D : OracleComp (NIZKDistinguisherSpec X Y T C Z) Bool} {Qp Qro : ℕ}
    (hD : NIZKCallBounded D Qp Qro) :
    |((fiatShamirNIZKRealGame P valid D) true).toReal -
        ((fiatShamirNIZKSimGame simulate valid D) true).toReal| ≤
      Qp * (Qp + Qro) * δ := by
  have hreal := run_interpret_map_state (nizkRealExtHandler P valid) (nizkRealHandler P valid)
    Prod.fst (nizkRealExtHandler_map_cache P valid) D ([], [])
  have hsim := run_interpret_map_state (nizkSimExtHandler simulate valid)
    (nizkSimHandler simulate valid) Prod.fst (nizkSimExtHandler_map_cache simulate valid) D ([], [])
  have hrealEq : fiatShamirNIZKRealGame P valid D =
      ((interpret (nizkRealExtHandler P valid) D).run ([], [])).bind
        (fun (b, _) => PMF.pure b) := by
    simp only [fiatShamirNIZKRealGame, ← hreal, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_map, Function.comp_def]
  have hsimEq : fiatShamirNIZKSimGame simulate valid D =
      ((interpret (nizkSimExtHandler simulate valid) D).run ([], [])).bind
        (fun (b, _) => PMF.pure b) := by
    simp only [fiatShamirNIZKSimGame, ← hsim, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_map, Function.comp_def]
  rw [hrealEq, hsimEq]
  exact abs_sub_extHandlers_bind_le hvalid hHVZK hUnpred hD (fun (b, _) => PMF.pure b) true

/-- `Game.advantage` form of **adaptive multi-theorem Fiat–Shamir NIZK zero knowledge**
([BonehShoup2023], Section 20.3.5, Theorem 20.3 / Equation (20.9)). -/
theorem advantage_fiatShamirNIZKRealGame_simGame_le [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop}
    {simulate : Y → C → PMF (T × Z)} {valid : X → Y → Bool} {δ : ℝ≥0}
    (hvalid : ∀ x y, valid x y = true → R x y)
    (hHVZK : P.SpecialHVZK R simulate)
    (hUnpred : P.UnpredictableCommitments R δ)
    {D : OracleComp (NIZKDistinguisherSpec X Y T C Z) Bool} {Qp Qro : ℕ}
    (hD : NIZKCallBounded D Qp Qro) :
    Game.advantage (fiatShamirNIZKRealGame P valid D)
      (fiatShamirNIZKSimGame simulate valid D) ≤
      Qp * (Qp + Qro) * δ := by
  rw [← NNReal.coe_le_coe, Game.coe_advantage]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, NNReal.coe_mul,
    NNReal.coe_add, NNReal.coe_natCast] using
    abs_sub_fiatShamirNIZKRealGame_simGame_le hvalid hHVZK hUnpred hD

/-! ### Rewinding core for ROM proof of knowledge and simulation-extractability -/

namespace FiatShamirNIZK

/-- Named components of a candidate proof verdict in the forking reduction. -/
private structure ForkOutcome (Y T C Z : Type) where
  /-- Whether the candidate proof won the experiment. -/
  won : Bool
  /-- Target statement `y*` of the candidate proof. -/
  stmt : Y
  /-- Commitment `t*` of the candidate proof. -/
  commitment : T
  /-- Challenge `c` assigned to `(stmt, commitment)`. -/
  challenge : C
  /-- Response `z*` of the candidate proof. -/
  response : Z

/-- State of the rewinding reduction during an adversary run: the random-oracle table with optional
external query indices, the `(y, t)` pairs returned by valid prove calls, the external query count,
and the presampled simulator coins. -/
private structure ReductionState (Y T C S : Type) where
  /-- Association list of `(y, t)` points with `(challenge, externalQueryIndex?)`. -/
  table : List ((Y × T) × C × Option ℕ)
  /-- Statement-commitment pairs `(y, t)` produced by valid prove queries. -/
  proved : List (Y × T)
  /-- Number of external random-oracle queries issued so far. -/
  count : ℕ
  /-- Remaining presampled simulator coins. -/
  samples : List S

/-- Reduction handler answering prove calls deterministically from presampled simulator coins and
hash calls from the recorded table or the external hash oracle. -/
private def reductionHandler [DecidableEq Y] [DecidableEq T] {S : Type}
    (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) :
    (q : (X × Y) ⊕ (Y × T)) →
      StateT (ReductionState Y T C S) (OracleComp (NIZKHashSpec Y T C))
        (NIZKDistinguisherSpec X Y T C Z q)
  | .inl (x, y) => fun st =>
    if hv : valid x y = true then
      let (t, c, z) := simEval (st.samples.headD fallback) x y hv
      pure (some (t, z),
        ⟨((y, t), c, none) :: st.table, (y, t) :: st.proved, st.count, st.samples.tail⟩)
    else
      pure (none, ⟨st.table, st.proved, st.count, st.samples.tail⟩)
  | .inr yt => fun st =>
    match st.table.lookup yt with
    | some entry => pure (entry.1, ⟨st.table, st.proved, st.count, st.samples.tail⟩)
    | none =>
      (fun c => (c, ⟨(yt, c, some st.count) :: st.table, st.proved, st.count + 1,
        st.samples.tail⟩)) <$> OracleComp.query (spec := NIZKHashSpec Y T C) yt

/-- Verdict on a candidate output `(y, (t, z))` at challenge `c` and optional query position. -/
private def verdict [DecidableEq Y] [DecidableEq T] (P : SigmaProtocol X Y T C Z)
    (admissible : Y → Bool) {S : Type}
    (cand : (Y × (T × Z)) × ReductionState Y T C S) (c : C) (position : Option ℕ) :
    Option ℕ × ForkOutcome Y T C Z :=
  let ((y, t, z), state) := cand
  let win := admissible y && P.verify y t c z && !state.proved.contains (y, t)
  (if win then position else none, ⟨win, y, t, c, z⟩)

/-- Final verification step in the forking program, querying `(y, t)` if absent from `table`. -/
private def finish [DecidableEq Y] [DecidableEq T] (P : SigmaProtocol X Y T C Z)
    (admissible : Y → Bool) {S : Type}
    (cand : (Y × (T × Z)) × ReductionState Y T C S) :
    OracleComp (NIZKHashSpec Y T C) (Option ℕ × ForkOutcome Y T C Z) :=
  let ((y, t, _), state) := cand
  match state.table.lookup (y, t) with
  | some entry => pure (verdict P admissible cand entry.1 entry.2)
  | none =>
    (fun c => verdict P admissible cand c (some state.count)) <$>
      OracleComp.query (spec := NIZKHashSpec Y T C) (y, t)

/-- Presampled online handler corresponding to one `S` draw per query. -/
private noncomputable def presampledHandler [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] {S : Type} (valid : X → Y → Bool)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) (sample : S) :
    (q : (X × Y) ⊕ (Y × T)) →
      StateT (ExtGameState Y T C) PMF (NIZKDistinguisherSpec X Y T C Z q)
  | .inl (x, y) => fun (cache, proved) =>
    if hv : valid x y = true then
      let (t, c, z) := simEval sample x y hv
      PMF.pure (some (t, z), (((y, t), c) :: cache, (y, t) :: proved))
    else
      PMF.pure (none, (cache, proved))
  | .inr yt => fun (cache, proved) =>
    (oracle C yt cache).map fun (c, cache') => (c, (cache', proved))

/-- Game-view projection of `ReductionState`. -/
private def represent {S : Type} (st : ReductionState Y T C S) : ExtGameState Y T C × List S :=
  ((st.table.map fun e => (e.1, e.2.1), st.proved), st.samples)

private theorem run_interpret_countingUniform_pure [Fintype C] [Nonempty C] {β : Type}
    (b : β) (n : ℕ) :
    (interpret countingUniform (pure b : OracleComp (NIZKHashSpec Y T C) β)).run n =
      PMF.pure (b, n) := rfl

private theorem run_countingUniform [Fintype C] [Nonempty C] (yt : Y × T) (n : ℕ) :
    (countingUniform (H := C) yt).run n = (PMF.uniformOfFintype C).map (·, n + 1) := rfl

private theorem run_reductionHandler_inl_pos [DecidableEq Y] [DecidableEq T] {S : Type}
    {valid : X → Y → Bool} (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z)
    {x : X} {y : Y} (hv : valid x y = true) (st : ReductionState Y T C S) :
    (reductionHandler valid fallback simEval (.inl (x, y))).run st =
      let (t, c, z) := simEval (st.samples.headD fallback) x y hv
      pure (some (t, z),
        ⟨((y, t), c, none) :: st.table, (y, t) :: st.proved, st.count, st.samples.tail⟩) := by
  simp only [reductionHandler, StateT.run, hv, ↓reduceDIte]

private theorem run_reductionHandler_inl_neg [DecidableEq Y] [DecidableEq T] {S : Type}
    {valid : X → Y → Bool} (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z)
    {x : X} {y : Y} (hv : ¬valid x y = true) (st : ReductionState Y T C S) :
    (reductionHandler valid fallback simEval (.inl (x, y))).run st =
      pure (none, ⟨st.table, st.proved, st.count, st.samples.tail⟩) := by
  simp only [reductionHandler, StateT.run, hv, Bool.false_eq_true, ↓reduceDIte]

private theorem run_reductionHandler_inr_some [DecidableEq Y] [DecidableEq T] {S : Type}
    (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z)
    {yt : Y × T} {st : ReductionState Y T C S} {e : C × Option ℕ}
    (h : st.table.lookup yt = some e) :
    (reductionHandler valid fallback simEval (.inr yt)).run st =
      pure (e.1, ⟨st.table, st.proved, st.count, st.samples.tail⟩) := by
  simp only [reductionHandler, StateT.run, h]

private theorem run_reductionHandler_inr_none [DecidableEq Y] [DecidableEq T] {S : Type}
    (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z)
    {yt : Y × T} {st : ReductionState Y T C S} (h : st.table.lookup yt = none) :
    (reductionHandler valid fallback simEval (.inr yt)).run st =
      (fun c => (c, ⟨(yt, c, some st.count) :: st.table, st.proved, st.count + 1,
        st.samples.tail⟩)) <$> OracleComp.query (spec := NIZKHashSpec Y T C) yt := by
  simp only [reductionHandler, StateT.run, h]

/-- Single-call simulation identity between `reductionHandler` (under `countingUniform`) and
`withSampleList fallback (presampledHandler valid simEval)`. -/
private theorem combined_step [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C] {S : Type}
    (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z)
    (q : (X × Y) ⊕ (Y × T)) (s : ReductionState Y T C S × ℕ) :
    ((fun result => (result.1.1, result.1.2, result.2)) <$>
      (interpret countingUniform
        ((reductionHandler valid fallback simEval q).run s.1)).run s.2).map
        (fun x => (x.1, represent x.2.1)) =
      withSampleList fallback (presampledHandler valid simEval) q (represent s.1) := by
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · rw [run_reductionHandler_inl_pos fallback simEval hv, run_interpret_countingUniform_pure]
      simp only [PMF.monad_map_eq_map, PMF.pure_map, withSampleList, presampledHandler, hv,
        ↓reduceDIte, represent]
      rfl
    · rw [run_reductionHandler_inl_neg fallback simEval hv, run_interpret_countingUniform_pure]
      simp only [PMF.monad_map_eq_map, PMF.pure_map, withSampleList, presampledHandler, hv,
        Bool.false_eq_true, ↓reduceDIte, represent]
  | inr yt =>
    cases h : s.1.table.lookup yt with
    | some e =>
      have hcache : (represent s.1).1.1.lookup yt = some e.1 := by
        rw [represent, List.lookup_map_snd, h]
        rfl
      rw [run_reductionHandler_inr_some valid fallback simEval h]
      simp only [run_interpret_countingUniform_pure, PMF.monad_map_eq_map, PMF.pure_map,
        withSampleList, presampledHandler]
      rw [oracle, memoize_of_some _ _ _ _ hcache]
      simp only [PMF.monad_pure_eq_pure, PMF.pure_map]
      rfl
    | none =>
      have hcache : (represent s.1).1.1.lookup yt = none := by
        rw [represent, List.lookup_map_snd, h]
        rfl
      rw [run_reductionHandler_inr_none valid fallback simEval h]
      simp only [interpret_map, interpret_query, StateT.run_map, PMF.monad_map_eq_map,
        withSampleList, presampledHandler]
      rw [oracle, memoize_of_none _ _ _ hcache]
      simp only [run_countingUniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
      rfl

/-- Game-side final check corresponding to `finish`. -/
private noncomputable def finishExtGame [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    (P : SigmaProtocol X Y T C Z) (admissible : Y → Bool)
    (cand : (Y × (T × Z)) × ExtGameState Y T C) : PMF Bool :=
  let ((y, t, z), (cache, proved)) := cand
  (oracle C (y, t) cache).map fun (c, _) =>
    admissible y && P.verify y t c z && !proved.contains (y, t)

/-- `finish` under `countingUniform` has the exact winning distribution of `finishExtGame`. -/
private theorem map_run_finish [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    (P : SigmaProtocol X Y T C Z) (admissible : Y → Bool) {S : Type}
    (cand : Y × (T × Z)) (st : ReductionState Y T C S) (n : ℕ) :
    ((interpret countingUniform (finish P admissible (cand, st))).run n).map
        (fun run => run.1.2.won) =
      finishExtGame P admissible (cand, (represent st).1) := by
  obtain ⟨y, t, z⟩ := cand
  cases h : st.table.lookup (y, t) with
  | some e =>
    have hcache : (represent st).1.1.lookup (y, t) = some e.1 := by
      rw [represent, List.lookup_map_snd, h]
      rfl
    simp only [finish, h, run_interpret_countingUniform_pure, PMF.pure_map, finishExtGame, verdict]
    rw [oracle, memoize_of_some _ _ _ _ hcache]
    simp only [PMF.monad_pure_eq_pure, PMF.pure_map]
    rfl
  | none =>
    have hcache : (represent st).1.1.lookup (y, t) = none := by
      rw [represent, List.lookup_map_snd, h]
      rfl
    simp only [finish, h, interpret_map, interpret_query, StateT.run_map, PMF.monad_map_eq_map,
      finishExtGame, verdict]
    rw [oracle, memoize_of_none _ _ _ hcache]
    simp only [run_countingUniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
    rfl

/-- Complete forking program for an `OracleComp` over `NIZKDistinguisherSpec` given presampled
simulator coins. -/
private def forkingProg [DecidableEq Y] [DecidableEq T] {S : Type}
    (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) (admissible : Y → Bool)
    (prog : OracleComp (NIZKDistinguisherSpec X Y T C Z) (Y × (T × Z)))
    (samples : List S) :
    OracleComp (NIZKHashSpec Y T C) (Option ℕ × ForkOutcome Y T C Z) :=
  (interpret (reductionHandler valid fallback simEval) prog).run ⟨[], [], 0, samples⟩ >>=
    finish P admissible

/-- Running `forkingProg` against `countingUniform` has the exact winning law of running `prog`
against `withSampleList` followed by `finishExtGame`. -/
private theorem map_run_forkingProg [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {S : Type} (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) (admissible : Y → Bool)
    (prog : OracleComp (NIZKDistinguisherSpec X Y T C Z) (Y × (T × Z))) (samples : List S) :
    ((interpret countingUniform
        (forkingProg P valid fallback simEval admissible prog samples)).run 0).map
        (fun run => run.1.2.won) =
      ((interpret (withSampleList fallback (presampledHandler valid simEval)) prog).run
        (([], []), samples)).bind fun x => finishExtGame P admissible (x.1, x.2.1) := by
  have hsim := run_interpret_map_state _
    (withSampleList fallback (presampledHandler valid simEval))
    (fun s => represent s.1) (combined_step valid fallback simEval)
    prog (⟨[], [], 0, samples⟩, 0)
  rw [show represent (⟨[], [], 0, samples⟩ : ReductionState Y T C S) = (([], []), samples)
    from rfl] at hsim
  rw [forkingProg, interpret_bind, StateT.run_bind, run_interpret_run_interpret, ← hsim]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.map_bind, PMF.bind_map,
    Function.comp_def]
  exact congrArg (PMF.bind _) (funext fun r => map_run_finish P admissible r.1 r.2.1 r.2.2)

/-- Table-consistency invariant of `reductionHandler` on a fixed answer list. -/
private def Consistent (defaultC : C) (answers : List C) {S : Type}
    (st : ReductionState Y T C S) (queries : List (Y × T)) : Prop :=
  st.count = queries.length ∧
    (∀ yt c i, (yt, c, some i) ∈ st.table →
      queries[i]? = some yt ∧ answers.getD i defaultC = c) ∧
    ∀ yt c, (yt, c, none) ∈ st.table → yt ∈ st.proved

private theorem consistent_step [DecidableEq Y] [DecidableEq T] (defaultC : C) (answers : List C)
    {S : Type} (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z)
    (q : (X × Y) ⊕ (Y × T)) (st : ReductionState Y T C S) (queries : List (Y × T))
    (h : Consistent defaultC answers st queries) :
    Consistent defaultC answers
      (runWithAnswers defaultC
        ((reductionHandler valid fallback simEval q).run st) (answers.drop queries.length)).1.2
      (queries ++ (runWithAnswers defaultC
        ((reductionHandler valid fallback simEval q).run st) (answers.drop queries.length)).2) := by
  obtain ⟨hcount, hpos, hproved⟩ := h
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · rw [run_reductionHandler_inl_pos fallback simEval hv, runWithAnswers_pure, List.append_nil]
      refine ⟨hcount, fun yt c i hmem => ?_, fun yt c hmem => ?_⟩
      · simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hmem
        exact hpos yt c i hmem
      · simp only [List.mem_cons, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, -, -⟩ | hmem
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hproved yt c hmem)
    · rw [run_reductionHandler_inl_neg fallback simEval hv, runWithAnswers_pure, List.append_nil]
      exact ⟨hcount, hpos, hproved⟩
  | inr yt =>
    cases hl : st.table.lookup yt with
    | some e =>
      rw [run_reductionHandler_inr_some valid fallback simEval hl, runWithAnswers_pure,
        List.append_nil]
      exact ⟨hcount, hpos, hproved⟩
    | none =>
      rw [run_reductionHandler_inr_none valid fallback simEval hl, runWithAnswers_map_query]
      refine ⟨by simp [hcount], fun yt' c i hmem => ?_, fun yt' c hmem => ?_⟩
      · simp only [List.mem_cons, Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
        · rw [hcount, List.getElem?_concat_length, List.getD_eq_getElem?_getD,
            List.headD_eq_head?_getD, List.head?_drop]
          exact ⟨rfl, rfl⟩
        · obtain ⟨hq, hc⟩ := hpos yt' c i hmem
          have hi : i < queries.length := (List.getElem?_eq_some_iff.mp hq).1
          exact ⟨by rw [List.getElem?_append_left hi, hq], hc⟩
      · simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hmem
        exact hproved yt' c hmem

/-- Deterministic run characterization of `forkingProg` on fixed hash answers: every winning run
names an external query index, and every named index `j` queried `(o.stmt, o.commitment)`,
received challenge `answers.getD j defaultC = o.challenge`, and satisfied `admissible o.stmt` and
`P.verify o.stmt o.commitment o.challenge o.response = true`. -/
private theorem runWithAnswers_forkingProg [DecidableEq Y] [DecidableEq T] (defaultC : C)
    {S : Type} (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) (admissible : Y → Bool)
    (prog : OracleComp (NIZKDistinguisherSpec X Y T C Z) (Y × (T × Z)))
    (samples : List S) (answers : List C)
    {out : (Option ℕ × ForkOutcome Y T C Z) × List (Y × T)}
    (hout :
      runWithAnswers defaultC
        (forkingProg P valid fallback simEval admissible prog samples) answers = out) :
    (out.1.2.won = true → out.1.1.isSome) ∧
      ∀ j, out.1.1 = some j →
        out.2[j]? = some (out.1.2.stmt, out.1.2.commitment) ∧
        answers.getD j defaultC = out.1.2.challenge ∧
        admissible out.1.2.stmt = true ∧
        P.verify out.1.2.stmt out.1.2.commitment out.1.2.challenge out.1.2.response = true := by
  have hinv := runWithAnswers_run_interpret_invariant defaultC
    (reductionHandler valid fallback simEval) answers (Consistent defaultC answers)
    (consistent_step defaultC answers valid fallback simEval) prog
    ⟨[], [], 0, samples⟩ [] ⟨rfl, by simp, by simp⟩
  simp only [List.length_nil, List.drop_zero, List.nil_append] at hinv
  rw [forkingProg, runWithAnswers_bind] at hout
  subst hout
  generalize runWithAnswers defaultC
    ((interpret (reductionHandler valid fallback simEval) prog).run ⟨[], [], 0, samples⟩) answers =
      r at hinv ⊢
  obtain ⟨⟨⟨y, t, z⟩, st⟩, queries⟩ := r
  obtain ⟨hcount, hpos, hproved⟩ := hinv
  cases hl : st.table.lookup (y, t) with
  | some e =>
    simp only [finish, hl, runWithAnswers_pure, List.append_nil]
    obtain ⟨l₁, l₂, htable, -⟩ := List.lookup_eq_some_iff.mp hl
    have hmem : ((y, t), e.1, e.2) ∈ st.table := by
      rw [htable]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨c, position⟩ := e
    cases position with
    | none =>
      have hyt : (y, t) ∈ st.proved := hproved (y, t) c hmem
      simp [verdict, hyt]
    | some i =>
      obtain ⟨hq, hc⟩ := hpos (y, t) c i hmem
      refine ⟨fun hwin => ?_, fun j hj => ?_⟩
      · simp only [verdict] at hwin ⊢
        simpa using hwin
      · simp only [verdict] at hj ⊢
        split_ifs at hj with hwin
        · cases hj
          simp only [Bool.and_eq_true] at hwin
          exact ⟨hq, hc, hwin.1.1, hwin.1.2⟩
  | none =>
    simp only [finish, hl, runWithAnswers_map_query]
    refine ⟨fun hwin => ?_, fun j hj => ?_⟩
    · simp only [verdict] at hwin ⊢
      simpa using hwin
    · simp only [verdict] at hj ⊢
      split_ifs at hj with hwin
      · cases hj
        simp only [Bool.and_eq_true] at hwin
        refine ⟨by rw [hcount, List.getElem?_concat_length], ?_, hwin.1.1, hwin.1.2⟩
        rw [hcount, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

/-- `forkingProg` makes at most `Qro + 1` external hash calls when `prog` makes at most `Qro` hash
calls. -/
private theorem isQueryBounded_forkingProg [DecidableEq Y] [DecidableEq T] {S : Type}
    (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) (admissible : Y → Bool)
    {prog : OracleComp (NIZKDistinguisherSpec X Y T C Z) (Y × (T × Z))} {Qro : ℕ}
    (hQro : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) prog Qro)
    (samples : List S) :
    IsQueryBounded (forkingProg P valid fallback simEval admissible prog samples) (Qro + 1) := by
  have hhandler (q : (X × Y) ⊕ (Y × T)) (st : ReductionState Y T C S) :
      IsQueryBounded ((reductionHandler valid fallback simEval q).run st)
        (Sum.elim (fun _ => 0) (fun _ => 1) q) := by
    cases q with
    | inl xy =>
      obtain ⟨x, y⟩ := xy
      by_cases hv : valid x y = true
      · rw [run_reductionHandler_inl_pos fallback simEval hv]
        exact .pure _ _
      · rw [run_reductionHandler_inl_neg fallback simEval hv]
        exact .pure _ _
    | inr yt =>
      cases hl : st.table.lookup yt with
      | some e =>
        rw [run_reductionHandler_inr_some valid fallback simEval hl]
        exact .pure _ _
      | none =>
        rw [run_reductionHandler_inr_none valid fallback simEval hl]
        exact .liftBind _ _ 0 fun _ => .pure _ 0
  refine (hQro.run_interpret hhandler ⟨[], [], 0, samples⟩).bind fun cand => ?_
  obtain ⟨⟨y, t, z⟩, st⟩ := cand
  cases hl : st.table.lookup (y, t) with
  | some e =>
    simp only [finish, hl]
    exact .pure _ _
  | none =>
    simp only [finish, hl]
    exact .liftBind _ _ 0 fun _ => .pure _ 0

/-- Under `countingUniform`, `forkingProg` wins at most as often as it validly names a query below
`Qro + 1`. -/
private theorem map_run_le_validIndex [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {S : Type} (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) (admissible : Y → Bool)
    {prog : OracleComp (NIZKDistinguisherSpec X Y T C Z) (Y × (T × Z))} {Qro : ℕ}
    (hQro : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) prog Qro)
    (samples : List S) :
    ((interpret countingUniform
        (forkingProg P valid fallback simEval admissible prog samples)).run 0).map
        (fun run => run.1.2.won) true ≤
      ((interpret countingUniform
        (forkingProg P valid fallback simEval admissible prog samples)).run 0).bind
        (fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true := by
  have hbound := isQueryBounded_forkingProg P valid fallback simEval admissible hQro samples
  let defC := Classical.arbitrary C
  rw [run_interpret_countingUniform_eq defC _ hbound]
  simp only [← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun h _ => ?_
  obtain ⟨hwin, hnamed⟩ :=
    runWithAnswers_forkingProg defC P valid fallback simEval admissible prog samples (List.ofFn h)
      rfl
  set run :=
    runWithAnswers defC (forkingProg P valid fallback simEval admissible prog samples) (List.ofFn h)
  by_cases hw : run.1.2.won = true
  · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hwin hw)
    have hlt : j < run.2.length := (List.getElem?_eq_some_iff.mp (hnamed j hj).1).1
    have hle : run.2.length ≤ Qro + 1 := hbound.length_runWithAnswers_le defC (List.ofFn h)
    have hvalid : (validIndex (Qro + 1) (0 + run.2.length) run.1.1).isSome = true := by
      rw [hj, zero_add]
      simp only [validIndex, Option.bind_some]
      split_ifs with hc
      · rfl
      · exact absurd ⟨by omega, hlt⟩ hc
    rw [hw, hvalid]
  · rw [Bool.eq_false_iff.mpr hw]
    simp

end FiatShamirNIZK

/-! ### Plain ROM proof of knowledge -/

/-- An explicit-coin cheating prover in the plain random-oracle model: it draws private coins
`coins` and, given statement `y`, queries `NIZKHashSpec Y T C` to output a candidate proof
`(t, z)`. -/
structure NIZKProver (Y T C Z : Type) where
  /-- The cheating prover's private coin type. -/
  Coins : Type
  /-- Distribution on the cheating prover's private coins. -/
  coins : PMF Coins
  /-- Deterministic oracle program producing `(t, z)` for statement `y`. -/
  prove : Y → Coins → OracleComp (NIZKHashSpec Y T C) (T × Z)

/-- Plain random-oracle proof-of-knowledge experiment on statement `y`: draw `s ← A.coins`, run
`A.prove y s` against `oracle C` from an empty cache, and verify the returned proof under the
shared cache. -/
@[expose] noncomputable def fiatShamirNIZKPokGame [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (A : NIZKProver Y T C Z) (y : Y) : Game := do
  let s ← A.coins
  let (prf, cache) ← (interpret (oracle C) (A.prove y s)).run []
  let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache
  return acc

/-- Lift a plain `NIZKHashSpec` prover run on statement `y` into `NIZKDistinguisherSpec` with an
empty prove-query domain. -/
private def liftPlainProve (y : Y) (prog : OracleComp (NIZKHashSpec Y T C) (T × Z)) :
    OracleComp (NIZKDistinguisherSpec Empty Y T C Z) (Y × (T × Z)) :=
  (fun prf => (y, prf)) <$>
    interpret (fun yt =>
      OracleComp.query (spec := NIZKDistinguisherSpec Empty Y T C Z) (.inr yt)) prog

private theorem isCostBounded_liftPlainProve {y : Y}
    {prog : OracleComp (NIZKHashSpec Y T C) (T × Z)} {Qro : ℕ} (hQro : IsQueryBounded prog Qro) :
    IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1))
      (liftPlainProve (T := T) (C := C) (Z := Z) y prog) Qro := by
  rw [liftPlainProve, isCostBounded_map_iff]
  refine hQro.interpret fun yt => ?_
  exact .liftBind (Sum.inr yt : (Empty × Y) ⊕ (Y × T)) _ 0 fun _ => .pure _ 0

/-- Plain ROM forking program for `A` on statement `y`. -/
private def plainForkingProg [DecidableEq Y] [DecidableEq T] (P : SigmaProtocol X Y T C Z)
    (A : NIZKProver Y T C Z) (y : Y) (s : A.Coins) :
    OracleComp (NIZKHashSpec Y T C) (Option ℕ × FiatShamirNIZK.ForkOutcome Y T C Z) :=
  let P' : SigmaProtocol Empty Y T C Z :=
    ⟨Unit, fun e => e.elim, fun e => e.elim, P.verify⟩
  FiatShamirNIZK.forkingProg P' (fun e _ => e.elim) () (fun _ e => e.elim)
    (fun y' => decide (y' = y)) (liftPlainProve y (A.prove y s)) []

/-- **Plain ROM knowledge extractor** ([BonehShoup2023], Section 20.3.4; rewinding via
[BellareNeven2006], Lemma 1): fork `A` across its at most `Qro + 1` hash queries on statement `y`
and apply `extract` to the two accepting transcripts when the fork succeeds. -/
noncomputable def fiatShamirNIZKExtract [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] [DecidableEq C] {W : Type}
    (P : SigmaProtocol X Y T C Z) (extract : Y → T → C → Z → C → Z → W)
    (A : NIZKProver Y T C Z) (Qro : ℕ) (y : Y) : PMF (Option W) :=
  (Forking.fork A.coins
    (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (plainForkingProg P A y))).map fun res =>
      match res with
      | none => none
      | some (_, (out, _), (out', _)) =>
        some (extract y out.2.commitment out.2.challenge out.2.response
          out'.2.challenge out'.2.response)

/-- Game testing whether an `Option W` extractor distribution outputs `some w` satisfying
`R w y`. -/
@[expose] noncomputable def fiatShamirNIZKExtractGame {W : Type} (R : W → Y → Prop)
    [∀ w y, Decidable (R w y)] (ext : PMF (Option W)) (y : Y) : Game := do
  let res ← ext
  return match res with
    | none => false
    | some w => decide (R w y)

private theorem pokGame_eq_plainForkingProg [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (A : NIZKProver Y T C Z) (y : Y) :
    fiatShamirNIZKPokGame P A y = A.coins.bind fun s =>
      ((interpret countingUniform (plainForkingProg P A y s)).run 0).map
        fun run => run.1.2.won := by
  let P' : SigmaProtocol Empty Y T C Z :=
    ⟨Unit, fun e => e.elim, fun e => e.elim, P.verify⟩
  simp only [fiatShamirNIZKPokGame, plainForkingProg, FiatShamirNIZK.map_run_forkingProg,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine congrArg A.coins.bind (funext fun s => ?_)
  have hstep :
      ∀ (yt : Y × T) (cache : List ((Y × T) × C)),
        (oracle C yt cache).map
          (fun (c, cache') => (c, ((cache', ([] : List (Y × T))), ([] : List Unit)))) =
        withSampleList ()
          (FiatShamirNIZK.presampledHandler (T := T) (C := C) (Z := Z)
            (fun (e : Empty) _ => e.elim) (fun _ e => e.elim))
          (.inr yt) ((cache, []), []) := by
    intro yt cache
    simp only [withSampleList, FiatShamirNIZK.presampledHandler, List.tail_nil,
      PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  have hsim := run_interpret_map_state (oracle C)
    (fun yt st =>
      withSampleList ()
        (FiatShamirNIZK.presampledHandler (T := T) (C := C) (Z := Z)
          (fun (e : Empty) _ => e.elim) (fun _ e => e.elim))
        (.inr yt) st)
    (fun cache => ((cache, ([] : List (Y × T))), ([] : List Unit)))
    hstep (A.prove y s) []
  rw [liftPlainProve, run_interpret_map, interpret_interpret]
  simp only [PMF.monad_map_eq_map, PMF.bind_map, interpret_query]
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def, FiatShamirNIZK.finishExtGame,
    fiatShamirNIZKVerify, interpret_map, interpret_query, StateT.run_map, PMF.monad_map_eq_map]
  refine congrArg (PMF.bind _) (funext fun (prf, cache) => ?_)
  simp only [Prod.map_apply, id_eq, decide_true, Bool.true_and, List.contains_nil, Bool.not_false,
    Bool.and_true]
  exact PMF.bind_pure_comp _ _

private theorem fork_plain_le_extractGame [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    [DecidableEq C] {W : Type} {P : SigmaProtocol X Y T C Z} {R : W → Y → Prop}
    [∀ w y, Decidable (R w y)] {extract : Y → T → C → Z → C → Z → W}
    {y : Y}
    (hsound : ∀ t c z c' z', c ≠ c' → P.Accepts y t c z → P.Accepts y t c' z' →
      R (extract y t c z c' z') y)
    (A : NIZKProver Y T C Z) (Qro : ℕ) :
    (Forking.fork A.coins
        (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (plainForkingProg P A y))).map
          Option.isSome true ≤
      fiatShamirNIZKExtractGame R (fiatShamirNIZKExtract P extract A Qro y) y true := by
  simp only [fiatShamirNIZKExtractGame, fiatShamirNIZKExtract, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun result hresult => ?_
  rcases result with _ | ⟨j, out, out'⟩
  · simp
  · obtain ⟨s, -, h, h', -, hne, hout, hout', hj, hj', -, query, hq, hq'⟩ :=
      mem_support_fork hresult
    let defC := Classical.arbitrary C
    obtain ⟨-, hnamed⟩ := FiatShamirNIZK.runWithAnswers_forkingProg defC _
      (fun (e : Empty) _ => e.elim) () (fun _ e => e.elim) (fun y' => decide (y' = y))
      (liftPlainProve y (A.prove y s)) [] (List.ofFn h) hout.symm
    obtain ⟨-, hnamed'⟩ := FiatShamirNIZK.runWithAnswers_forkingProg defC _
      (fun (e : Empty) _ => e.elim) () (fun _ e => e.elim) (fun y' => decide (y' = y))
      (liftPlainProve y (A.prove y s)) [] (List.ofFn h') hout'.symm
    obtain ⟨hp, hc, hy, hv⟩ := hnamed j hj
    obtain ⟨hp', hc', -, hv'⟩ := hnamed' j hj'
    rw [List.getD_ofFn] at hc hc'
    have hpoint : (out.1.2.stmt, out.1.2.commitment) = (out'.1.2.stmt, out'.1.2.commitment) :=
      Option.some.inj (hp.symm.trans (hq.trans (hq'.symm.trans hp')))
    have hstmt : out.1.2.stmt = y := of_decide_eq_true hy
    have ht : out.1.2.commitment = out'.1.2.commitment := (Prod.mk.inj hpoint).2
    have hstmt' : out'.1.2.stmt = y := (Prod.mk.inj hpoint).1.symm.trans hstmt
    have hacc : P.Accepts y out.1.2.commitment out.1.2.challenge out.1.2.response := by
      simpa only [SigmaProtocol.Accepts, hstmt] using hv
    have hacc' : P.Accepts y out.1.2.commitment out'.1.2.challenge out'.1.2.response := by
      simpa only [SigmaProtocol.Accepts, hstmt', ← ht] using hv'
    have hR := hsound out.1.2.commitment out.1.2.challenge out.1.2.response
      out'.1.2.challenge out'.1.2.response (by rw [← hc, ← hc']; exact hne) hacc hacc'
    obtain ⟨⟨_, o⟩, _⟩ := out
    obtain ⟨⟨_, o'⟩, _⟩ := out'
    simp [hR]

/-- **Plain ROM proof of knowledge** for Fiat–Shamir NIZK proofs ([BonehShoup2023], Section 20.3.4,
proved via the general forking inequality of [BellareNeven2006], Lemma 1): if `P` is special sound
at `y` with extractor `extract` and `A` makes at most `Qro` hash calls on `y`, then `A`'s
acceptance probability `ε` satisfies `ε ≤ (Qro + 1) / |C| + √((Qro + 1) * ε')`, where `ε'` is the
probability that `fiatShamirNIZKExtract P extract A Qro y` outputs `some w` with `R w y`. -/
theorem succProbability_fiatShamirNIZKPokGame_le [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] [DecidableEq C] {W : Type} {P : SigmaProtocol X Y T C Z} {R : W → Y → Prop}
    [∀ w y, Decidable (R w y)] {extract : Y → T → C → Z → C → Z → W}
    (hsound : P.SpecialSoundness R extract)
    (A : NIZKProver Y T C Z) {Qro : ℕ} (y : Y)
    (hQro : ∀ s, IsQueryBounded (A.prove y s) Qro) :
    (Game.succProbability (fiatShamirNIZKPokGame P A y) : ℝ) ≤
      (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKExtractGame R (fiatShamirNIZKExtract P extract A Qro y) y)) := by
  have hB : fiatShamirNIZKPokGame P A y true ≤
      A.coins.bind (fun s => ((interpret countingUniform (plainForkingProg P A y s)).run 0).bind
        fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true := by
    rw [pokGame_eq_plainForkingProg]
    exact Probability.PMF.bind_apply_mono_on_support _ _ fun s _ =>
      FiatShamirNIZK.map_run_le_validIndex _ _ () _ _
        (isCostBounded_liftPlainProve (hQro s)) []
  have hC := le_add_sqrt_fork A.coins (plainForkingProg P A y) (Classical.arbitrary C)
    (fun s => FiatShamirNIZK.isQueryBounded_forkingProg _ _ () _ _
      (isCostBounded_liftPlainProve (hQro s)) [])
  have hD := fork_plain_le_extractGame (hsound y) A Qro
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] at hC
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  calc (fiatShamirNIZKPokGame P A y true).toReal
      ≤ (A.coins.bind (fun s =>
          ((interpret countingUniform (plainForkingProg P A y s)).run 0).bind
            fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true).toReal :=
        ENNReal.toReal_mono (PMF.apply_ne_top _ _) hB
    _ ≤ (Qro + 1 : ℕ) / Fintype.card C +
          √((Qro + 1 : ℕ) * ((Forking.fork A.coins
            (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (plainForkingProg P A y))).map
              Option.isSome true).toReal) := hC
    _ ≤ _ := by
        push_cast
        have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hD) (by positivity : (0 : ℝ) ≤ Qro + 1))
        linarith

/-- **Plain ROM proof of knowledge against a key generator** (`oneWayGame` form): averaging over
`(x, y) ← keyGen`, a cheating prover making at most `Qro` hash calls yields a `oneWayGame`
adversary via `fiatShamirNIZKExtract`. -/
theorem succProbability_fiatShamirNIZKPokKeyGen_le [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] [DecidableEq C] [Nonempty X] {P : SigmaProtocol X Y T C Z}
    {keyGen : PMF (X × Y)} {R : X → Y → Prop} [∀ x y, Decidable (R x y)]
    {extract : Y → T → C → Z → C → Z → X}
    (hsound : P.SpecialSoundOn keyGen R extract)
    (A : NIZKProver Y T C Z) {Qro : ℕ}
    (hQro : ∀ y s, IsQueryBounded (A.prove y s) Qro) :
    (Game.succProbability (keyGen.bind fun (_, y) => fiatShamirNIZKPokGame P A y) : ℝ) ≤
      (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (oneWayGame keyGen R fun y =>
            (fiatShamirNIZKExtract P extract A Qro y).map
              (fun w => w.getD (Classical.arbitrary X)))) := by
  set first : PMF ((X × Y) × A.Coins) :=
    keyGen.bind fun key => A.coins.map fun s => (key, s)
  let prog : (X × Y) × A.Coins →
      OracleComp (NIZKHashSpec Y T C) (Option ℕ × FiatShamirNIZK.ForkOutcome Y T C Z) :=
    fun (key, s) => plainForkingProg P A key.2 s
  have hB : (keyGen.bind fun (_, y) => fiatShamirNIZKPokGame P A y) true ≤
      first.bind (fun ks => ((interpret countingUniform (prog ks)).run 0).bind
        fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true := by
    simp only [first, prog, pokGame_eq_plainForkingProg, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun key _ => ?_
    exact Probability.PMF.bind_apply_mono_on_support _ _ fun s _ =>
      FiatShamirNIZK.map_run_le_validIndex _ _ () _ _
        (isCostBounded_liftPlainProve (hQro key.2 s)) []
  have hC := le_add_sqrt_fork first prog (Classical.arbitrary C)
    (fun (key, s) => FiatShamirNIZK.isQueryBounded_forkingProg _ _ () _ _
      (isCostBounded_liftPlainProve (hQro key.2 s)) [])
  have hD : (Forking.fork first
      (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) prog)).map Option.isSome true ≤
      oneWayGame keyGen R (fun y =>
        (fiatShamirNIZKExtract P extract A Qro y).map
          (fun w => w.getD (Classical.arbitrary X))) true := by
    have hfork : Forking.fork first (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) prog) =
        keyGen.bind fun key =>
          Forking.fork A.coins
            (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (plainForkingProg P A key.2)) := by
      simp only [first, prog, Forking.fork, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.bind_map, Function.comp_def]
      rfl
    rw [hfork, PMF.map_bind]
    simp only [oneWayGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
      Function.comp_def]
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun key hkey => ?_
    refine (fork_plain_le_extractGame (hsound key hkey) A Qro).trans ?_
    simp only [fiatShamirNIZKExtractGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun res _ => ?_
    cases res <;> simp
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] at hC
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  calc ((keyGen.bind fun (_, y) => fiatShamirNIZKPokGame P A y) true).toReal
      ≤ (first.bind (fun ks => ((interpret countingUniform (prog ks)).run 0).bind
          fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true).toReal :=
        ENNReal.toReal_mono (PMF.apply_ne_top _ _) hB
    _ ≤ (Qro + 1 : ℕ) / Fintype.card C +
          √((Qro + 1 : ℕ) * ((Forking.fork first
            (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) prog)).map
              Option.isSome true).toReal) := hC
    _ ≤ _ := by
        push_cast
        have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hD) (by positivity : (0 : ℝ) ≤ Qro + 1))
        linarith

/-- **ROM soundness on false statements**: if `y` has no witness in `R`, any cheating prover making
at most `Qro` hash calls convinces `fiatShamirNIZKVerify` with probability at most
`(Qro + 1) / |C|`. -/
theorem succProbability_fiatShamirNIZKPokGame_le_of_false [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] {W : Type} {P : SigmaProtocol X Y T C Z}
    {R : W → Y → Prop} {extract : Y → T → C → Z → C → Z → W}
    (hsound : P.SpecialSoundness R extract) {y : Y} (hfalse : ∀ w, ¬ R w y)
    (A : NIZKProver Y T C Z) {Qro : ℕ} (hQro : ∀ s, IsQueryBounded (A.prove y s) Qro) :
    (Game.succProbability (fiatShamirNIZKPokGame P A y) : ℝ) ≤
      (Qro + 1) / Fintype.card C := by
  classical
  have h := succProbability_fiatShamirNIZKPokGame_le hsound A y hQro
  have hzero :
      (Game.succProbability
        (fiatShamirNIZKExtractGame R (fiatShamirNIZKExtract P extract A Qro y) y) : ℝ) = 0 := by
    have heq :
        fiatShamirNIZKExtractGame R (fiatShamirNIZKExtract P extract A Qro y) y =
          PMF.pure false := by
      simp only [fiatShamirNIZKExtractGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      refine (Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure false)
        fun res _ => ?_).trans (PMF.bind_const _ _)
      cases res with
      | none => rfl
      | some w => simp [hfalse w]
    simp [heq, Game.succProbability]
  rw [hzero, mul_zero, Real.sqrt_zero, add_zero] at h
  exact h

/-! ### Simulation-extractability (adaptive multi-theorem proof of knowledge) -/

/-- An explicit coin source realizing one step of `simulateConversation simulate`: drawing
`r ← coins` and evaluating `eval r y` reproduces `(t, c, z) ← simulateConversation simulate y` at
every statement `y`. -/
structure SimCoinSource (Y T C Z : Type) [Fintype C] [Nonempty C]
    (simulate : Y → C → PMF (T × Z)) where
  /-- Coin space for one simulated transcript across statements. -/
  Coins : Type
  /-- Distribution on simulator coins. -/
  coins : PMF Coins
  /-- Deterministic evaluation of `(t, c, z)` at statement `y`. -/
  eval : Coins → Y → T × C × Z
  /-- Marginal law at each statement `y` equals `simulateConversation simulate y`. -/
  map_eval : ∀ y, coins.map (fun r => eval r y) = simulateConversation simulate y

/-- Canonical `SimCoinSource` for any simulator over finite statement, commitment, and response
types via `PMF.pi`. -/
@[expose] noncomputable def SimCoinSource.ofFintype [Fintype Y] [Finite T] [Finite Z]
    [Fintype C] [Nonempty C] (simulate : Y → C → PMF (T × Z)) :
    SimCoinSource Y T C Z simulate where
  Coins := Y → T × C × Z
  coins := PMF.pi (fun y => simulateConversation simulate y)
  eval f y := f y
  map_eval y := PMF.pi_map_eval _ y

/-- Explicit-coin adaptive multi-theorem cheating prover: it draws private coins `coins`, queries
both the prove oracle `.inl (x, y)` and the hash oracle `.inr (y, t)`, and outputs a target
statement `y*` paired with a candidate proof `(t*, z*)`. -/
structure NIZKSimProver (X Y T C Z : Type) where
  /-- The adversary's private coin type. -/
  Coins : Type
  /-- Distribution on the adversary's private coins. -/
  coins : PMF Coins
  /-- Adaptive oracle program outputting `(y*, (t*, z*))`. -/
  prove : Coins → OracleComp (NIZKDistinguisherSpec X Y T C Z) (Y × (T × Z))

/-- `A` makes at most `Qp` prove calls and `Qro` hash calls on every coin sample. -/
@[expose] def NIZKSimProver.CallBounded (A : NIZKSimProver X Y T C Z) (Qp Qro : ℕ) : Prop :=
  ∀ s, NIZKCallBounded (A.prove s) Qp Qro

/-- Real adaptive multi-theorem proof-of-knowledge experiment with final-statement guard
`admissible`: `A` interacts with the real prove and hash oracles and wins when its output
`(y*, (t*, z*))` satisfies `admissible y*`, passes `fiatShamirNIZKVerify`, and has a fresh
statement-commitment pair `(y*, t*)` not returned by any valid prove query. -/
@[expose] noncomputable def fiatShamirNIZKRealExtGameOn [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] (admissible : Y → Bool) (P : SigmaProtocol X Y T C Z)
    (valid : X → Y → Bool) (A : NIZKSimProver X Y T C Z) : Game := do
  let s ← A.coins
  let ((y, prf), (cache, proved)) ←
    (interpret (nizkRealExtHandler P valid) (A.prove s)).run ([], [])
  let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache
  return (admissible y && acc && !proved.contains (y, prf.1))

/-- Unrestricted real adaptive multi-theorem proof-of-knowledge experiment (`admissible = true`). -/
@[expose] noncomputable def fiatShamirNIZKRealExtGame [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool)
    (A : NIZKSimProver X Y T C Z) : Game :=
  fiatShamirNIZKRealExtGameOn (fun _ => true) P valid A

/-- Simulated adaptive multi-theorem proof-of-knowledge experiment with final-statement guard
`admissible`: `A` interacts with the programmable-ROM simulated prove oracle and shared hash oracle,
winning under the same fresh-`(y*, t*)` acceptance condition. -/
@[expose] noncomputable def fiatShamirNIZKSimExtGameOn [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] (admissible : Y → Bool) (P : SigmaProtocol X Y T C Z)
    (simulate : Y → C → PMF (T × Z)) (valid : X → Y → Bool)
    (A : NIZKSimProver X Y T C Z) : Game := do
  let s ← A.coins
  let ((y, prf), (cache, proved)) ←
    (interpret (nizkSimExtHandler simulate valid) (A.prove s)).run ([], [])
  let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache
  return (admissible y && acc && !proved.contains (y, prf.1))

/-- Unrestricted simulated adaptive multi-theorem proof-of-knowledge experiment
(`admissible = true`). -/
@[expose] noncomputable def fiatShamirNIZKSimExtGame [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] (P : SigmaProtocol X Y T C Z)
    (simulate : Y → C → PMF (T × Z)) (valid : X → Y → Bool)
    (A : NIZKSimProver X Y T C Z) : Game :=
  fiatShamirNIZKSimExtGameOn (fun _ => true) P simulate valid A

/-- Forking program for simulation-extractability using `src : SimCoinSource`. -/
private noncomputable def simForkingProg [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {simulate : Y → C → PMF (T × Z)} (P : SigmaProtocol X Y T C Z)
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool) (admissible : Y → Bool)
    (A : NIZKSimProver X Y T C Z) (s : A.Coins × List src.Coins) :
    OracleComp (NIZKHashSpec Y T C) (Option ℕ × FiatShamirNIZK.ForkOutcome Y T C Z) :=
  FiatShamirNIZK.forkingProg P valid src.coins.support_nonempty.some
    (fun r _ y _ => src.eval r y) admissible (A.prove s.1) s.2

/-- Joint coin distribution `(s, samples)` for `simForkingProg`. -/
private noncomputable def simForkCoins [Fintype C] [Nonempty C]
    {simulate : Y → C → PMF (T × Z)} (src : SimCoinSource Y T C Z simulate)
    (A : NIZKSimProver X Y T C Z) (Q : ℕ) : PMF (A.Coins × List src.Coins) := do
  let s ← A.coins
  let samples ← (PMF.iid src.coins Q).map List.ofFn
  return (s, samples)

/-- **Witness-free simulation-extractability rewinding extractor** parameterized by an explicit
`SimCoinSource` (derived adaptive multi-theorem reduction combining `SimCoinSource` presampling with
[BellareNeven2006], Lemma 1). -/
noncomputable def fiatShamirNIZKSimExtractWith [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] [DecidableEq C] {W : Type}
    {simulate : Y → C → PMF (T × Z)} (P : SigmaProtocol X Y T C Z)
    (src : SimCoinSource Y T C Z simulate) (extract : Y → T → C → Z → C → Z → W)
    (valid : X → Y → Bool) (admissible : Y → Bool)
    (A : NIZKSimProver X Y T C Z) (Qp Qro : ℕ) : PMF (Option (Y × W)) :=
  (Forking.fork (simForkCoins src A (Qp + Qro))
    (forkingAlgorithm (Classical.arbitrary C) (Qro + 1)
      (simForkingProg P src valid admissible A))).map fun res =>
        match res with
        | none => none
        | some (_, (out, _), (out', _)) =>
          some (out.2.stmt,
            extract out.2.stmt out.2.commitment out.2.challenge out.2.response
              out'.2.challenge out'.2.response)

/-- **Witness-free simulation-extractability rewinding extractor** over finite statement and
transcript spaces (`admissible = true`), answering prove queries with `simulate` and rewinding hash
queries via `Forking.fork`. -/
noncomputable def fiatShamirNIZKSimExtract [DecidableEq Y] [DecidableEq T]
    [Fintype Y] [Finite T] [Finite Z] [Fintype C] [Nonempty C] [DecidableEq C] {W : Type}
    (P : SigmaProtocol X Y T C Z) (simulate : Y → C → PMF (T × Z))
    (extract : Y → T → C → Z → C → Z → W) (valid : X → Y → Bool)
    (A : NIZKSimProver X Y T C Z) (Qp Qro : ℕ) : PMF (Option (Y × W)) :=
  fiatShamirNIZKSimExtractWith P (SimCoinSource.ofFintype simulate) extract valid (fun _ => true)
    A Qp Qro

/-- Game testing whether a simulation-extractability extractor outputs `some (y*, w*)` satisfying
both `admissible y*` and `R w* y*`. -/
@[expose] noncomputable def fiatShamirNIZKSimExtractGame {W : Type} (R : W → Y → Prop)
    [∀ w y, Decidable (R w y)] (admissible : Y → Bool)
    (ext : PMF (Option (Y × W))) : Game := do
  let res ← ext
  return match res with
    | none => false
    | some (y, w) => admissible y && decide (R w y)

private theorem presampledHandler_bind_eq_nizkSimExtHandler [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] {simulate : Y → C → PMF (T × Z)}
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool)
    (q : (X × Y) ⊕ (Y × T)) (st : ExtGameState Y T C) :
    src.coins.bind (fun r =>
      FiatShamirNIZK.presampledHandler valid (fun r _ y _ => src.eval r y) r q st) =
      nizkSimExtHandler simulate valid q st := by
  obtain ⟨cache, proved⟩ := st
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · simp only [FiatShamirNIZK.presampledHandler, nizkSimExtHandler, nizkSimProve, hv,
        ↓reduceDIte, ↓reduceIte, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
        PMF.pure_bind]
      have hmap := congrArg
        (fun μ : PMF (T × C × Z) =>
          μ.bind fun (t, c, z) => PMF.pure (some (t, z), (((y, t), c) :: cache, (y, t) :: proved)))
        (src.map_eval y)
      simpa only [simulateConversation, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] using hmap
    · simp only [Bool.not_eq_true] at hv
      simp only [FiatShamirNIZK.presampledHandler, hv, Bool.false_eq_true, ↓reduceDIte,
        nizkSimExtHandler, ↓reduceIte, PMF.bind_const]
  | inr yt =>
    simp only [FiatShamirNIZK.presampledHandler, nizkSimExtHandler, PMF.bind_const]

private theorem simExtGameOn_eq_simForkingProg [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] {simulate : Y → C → PMF (T × Z)} (P : SigmaProtocol X Y T C Z)
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool) (admissible : Y → Bool)
    {A : NIZKSimProver X Y T C Z} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    fiatShamirNIZKSimExtGameOn admissible P simulate valid A =
      (simForkCoins src A (Qp + Qro)).bind fun s =>
        ((interpret countingUniform (simForkingProg P src valid admissible A s)).run 0).map
          fun run => run.1.2.won := by
  simp only [fiatShamirNIZKSimExtGameOn, simForkCoins, simForkingProg,
    FiatShamirNIZK.map_run_forkingProg, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  refine congrArg A.coins.bind (funext fun s => ?_)
  have hpre := (hA s).isQueryBounded.run_interpret_presample src.coins
    src.coins.support_nonempty.some
    (FiatShamirNIZK.presampledHandler valid (fun r _ y _ => src.eval r y)) ([], [])
  have hstep :
      (fun q state =>
        src.coins.bind fun value =>
          FiatShamirNIZK.presampledHandler valid (fun r _ y _ => src.eval r y) value q state) =
      nizkSimExtHandler simulate valid :=
    funext fun q => funext fun state =>
      presampledHandler_bind_eq_nizkSimExtHandler src valid q state
  rw [hstep] at hpre
  have hfin :
      ((interpret (nizkSimExtHandler simulate valid) (A.prove s)).run ([], [])).bind
        (fun ((y, prf), (cache, proved)) =>
          ((interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache).bind
            fun (acc, _) => PMF.pure (admissible y && acc && !proved.contains (y, prf.1))) =
      ((interpret (nizkSimExtHandler simulate valid) (A.prove s)).run ([], [])).bind
        (FiatShamirNIZK.finishExtGame P admissible) := by
    refine congrArg (PMF.bind _) (funext fun ((y, prf), (cache, proved)) => ?_)
    simp only [FiatShamirNIZK.finishExtGame, fiatShamirNIZKVerify, interpret_map, interpret_query,
      StateT.run_map, PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
    exact (PMF.bind_pure_comp _ _).symm
  rw [hfin, ← hpre, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun samples => ?_)
  rw [PMF.bind_map]
  rfl

private theorem fork_sim_le_simExtractGame [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] [DecidableEq C] {W : Type} {P : SigmaProtocol X Y T C Z} {R : W → Y → Prop}
    [∀ w y, Decidable (R w y)] {simulate : Y → C → PMF (T × Z)}
    {extract : Y → T → C → Z → C → Z → W}
    (hsound : P.SpecialSoundness R extract)
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool) (admissible : Y → Bool)
    (A : NIZKSimProver X Y T C Z) (Qp Qro : ℕ) :
    (Forking.fork (simForkCoins src A (Qp + Qro))
        (forkingAlgorithm (Classical.arbitrary C) (Qro + 1)
          (simForkingProg P src valid admissible A))).map Option.isSome true ≤
      fiatShamirNIZKSimExtractGame R admissible
        (fiatShamirNIZKSimExtractWith P src extract valid admissible A Qp Qro) true := by
  simp only [fiatShamirNIZKSimExtractGame, fiatShamirNIZKSimExtractWith, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun result hresult => ?_
  rcases result with _ | ⟨j, out, out'⟩
  · simp
  · obtain ⟨s, -, h, h', -, hne, hout, hout', hj, hj', -, query, hq, hq'⟩ :=
      mem_support_fork hresult
    let defC := Classical.arbitrary C
    obtain ⟨-, hnamed⟩ := FiatShamirNIZK.runWithAnswers_forkingProg defC P valid
      src.coins.support_nonempty.some (fun r _ y _ => src.eval r y) admissible
      (A.prove s.1) s.2 (List.ofFn h) hout.symm
    obtain ⟨-, hnamed'⟩ := FiatShamirNIZK.runWithAnswers_forkingProg defC P valid
      src.coins.support_nonempty.some (fun r _ y _ => src.eval r y) admissible
      (A.prove s.1) s.2 (List.ofFn h') hout'.symm
    obtain ⟨hp, hc, hadm, hv⟩ := hnamed j hj
    obtain ⟨hp', hc', -, hv'⟩ := hnamed' j hj'
    rw [List.getD_ofFn] at hc hc'
    have hpoint : (out.1.2.stmt, out.1.2.commitment) = (out'.1.2.stmt, out'.1.2.commitment) :=
      Option.some.inj (hp.symm.trans (hq.trans (hq'.symm.trans hp')))
    have hacc' :
        P.Accepts out.1.2.stmt out.1.2.commitment out'.1.2.challenge out'.1.2.response := by
      simpa only [SigmaProtocol.Accepts, (Prod.mk.inj hpoint).1, (Prod.mk.inj hpoint).2] using hv'
    have hR := hsound out.1.2.stmt out.1.2.commitment out.1.2.challenge out.1.2.response
      out'.1.2.challenge out'.1.2.response (by rw [← hc, ← hc']; exact hne) hv hacc'
    obtain ⟨⟨_, o⟩, _⟩ := out
    obtain ⟨⟨_, o'⟩, _⟩ := out'
    simp [hadm, hR]

/-- **Derived simulation-extractability against simulated proofs** (general `SimCoinSource` and
`admissible` form, via `SimCoinSource` presampling and [BellareNeven2006], Lemma 1): without
needing commitment unpredictability or `SpecialHVZK`, an adaptive adversary making at most `Qp`
prove calls and `Qro` hash calls wins `fiatShamirNIZKSimExtGameOn` with probability at most
`(Qro + 1) / |C| + √((Qro + 1) * ε')`. -/
theorem succProbability_fiatShamirNIZKSimExtGameOn_le [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] [DecidableEq C] {W : Type} {P : SigmaProtocol X Y T C Z}
    {R : W → Y → Prop} [∀ w y, Decidable (R w y)]
    {simulate : Y → C → PMF (T × Z)} {extract : Y → T → C → Z → C → Z → W}
    (hsound : P.SpecialSoundness R extract)
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool) (admissible : Y → Bool)
    {A : NIZKSimProver X Y T C Z} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    (Game.succProbability (fiatShamirNIZKSimExtGameOn admissible P simulate valid A) : ℝ) ≤
      (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKSimExtractGame R admissible
            (fiatShamirNIZKSimExtractWith P src extract valid admissible A Qp Qro))) := by
  set first := simForkCoins src A (Qp + Qro)
  have hB : fiatShamirNIZKSimExtGameOn admissible P simulate valid A true ≤
      first.bind (fun s =>
        ((interpret countingUniform (simForkingProg P src valid admissible A s)).run 0).bind
          fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true := by
    rw [simExtGameOn_eq_simForkingProg P src valid admissible hA]
    exact Probability.PMF.bind_apply_mono_on_support _ _ fun s _ =>
      FiatShamirNIZK.map_run_le_validIndex P valid src.coins.support_nonempty.some
        (fun r _ y _ => src.eval r y) admissible (hA s.1).2 s.2
  have hC := le_add_sqrt_fork first (simForkingProg P src valid admissible A)
    (Classical.arbitrary C)
    (fun s => FiatShamirNIZK.isQueryBounded_forkingProg P valid src.coins.support_nonempty.some
      (fun r _ y _ => src.eval r y) admissible (hA s.1).2 s.2)
  have hD := fork_sim_le_simExtractGame hsound src valid admissible A Qp Qro
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] at hC
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  calc (fiatShamirNIZKSimExtGameOn admissible P simulate valid A true).toReal
      ≤ (first.bind (fun s =>
          ((interpret countingUniform (simForkingProg P src valid admissible A s)).run 0).bind
            fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true).toReal :=
        ENNReal.toReal_mono (PMF.apply_ne_top _ _) hB
    _ ≤ (Qro + 1 : ℕ) / Fintype.card C +
          √((Qro + 1 : ℕ) * ((Forking.fork first
            (forkingAlgorithm (Classical.arbitrary C) (Qro + 1)
              (simForkingProg P src valid admissible A))).map Option.isSome true).toReal) := hC
    _ ≤ _ := by
        push_cast
        have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hD) (by positivity : (0 : ℝ) ≤ Qro + 1))
        linarith

/-- **Simulation-extractability against simulated proofs** over finite statement and transcript
types. -/
theorem succProbability_fiatShamirNIZKSimExtGame_le [DecidableEq Y] [DecidableEq T]
    [Fintype Y] [Finite T] [Finite Z] [Fintype C] [Nonempty C] [DecidableEq C] {W : Type}
    {P : SigmaProtocol X Y T C Z} {R : W → Y → Prop} [∀ w y, Decidable (R w y)]
    {simulate : Y → C → PMF (T × Z)} {extract : Y → T → C → Z → C → Z → W}
    (hsound : P.SpecialSoundness R extract) (valid : X → Y → Bool)
    {A : NIZKSimProver X Y T C Z} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    (Game.succProbability (fiatShamirNIZKSimExtGame P simulate valid A) : ℝ) ≤
      (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKSimExtractGame R (fun _ => true)
            (fiatShamirNIZKSimExtract P simulate extract valid A Qp Qro))) :=
  succProbability_fiatShamirNIZKSimExtGameOn_le hsound (SimCoinSource.ofFintype simulate)
    valid (fun _ => true) hA

/-- **Derived adaptive multi-theorem proof of knowledge (simulation-extractability) against real
proofs** (general `SimCoinSource` and `admissible` form, combining the Attack Game 20.3 / Theorem
20.3 zero-knowledge hop with `SimCoinSource` presampling and [BellareNeven2006], Lemma 1): under
`SpecialSoundness`, `SpecialHVZK`, and `UnpredictableCommitments R_honest δ`, an adversary making
at most `Qp` prove calls and `Qro` hash calls wins `fiatShamirNIZKRealExtGameOn` with probability
at most `Qp * (Qp + Qro) * δ + (Qro + 1) / |C| + √((Qro + 1) * ε')`. -/
theorem succProbability_fiatShamirNIZKRealExtGameOn_le [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] [DecidableEq C] {W : Type} {P : SigmaProtocol X Y T C Z}
    {R_honest : X → Y → Prop} {R : W → Y → Prop} [∀ w y, Decidable (R w y)]
    {simulate : Y → C → PMF (T × Z)} {extract : Y → T → C → Z → C → Z → W}
    {valid : X → Y → Bool} {δ : ℝ≥0}
    (hvalid : ∀ x y, valid x y = true → R_honest x y)
    (hsound : P.SpecialSoundness R extract)
    (hHVZK : P.SpecialHVZK R_honest simulate)
    (hUnpred : P.UnpredictableCommitments R_honest δ)
    (src : SimCoinSource Y T C Z simulate) (admissible : Y → Bool)
    {A : NIZKSimProver X Y T C Z} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    (Game.succProbability (fiatShamirNIZKRealExtGameOn admissible P valid A) : ℝ) ≤
      Qp * (Qp + Qro) * δ + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKSimExtractGame R admissible
            (fiatShamirNIZKSimExtractWith P src extract valid admissible A Qp Qro))) := by
  let post : (Y × (T × Z)) × ExtGameState Y T C → PMF Bool :=
    fun ((y, prf), (cache, proved)) =>
      ((interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache).bind
        fun (acc, _) => PMF.pure (admissible y && acc && !proved.contains (y, prf.1))
  have hhop : fiatShamirNIZKRealExtGameOn admissible P valid A true ≤
      fiatShamirNIZKSimExtGameOn admissible P simulate valid A true +
        (Qp * (Qp + Qro) : ℕ) * (δ : ℝ≥0∞) := by
    simp only [fiatShamirNIZKRealExtGameOn, fiatShamirNIZKSimExtGameOn, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure]
    rw [PMF.bind_apply, PMF.bind_apply]
    calc ∑' s, A.coins s * _ ≤
          ∑' s, A.coins s * (_ + (Qp * (Qp + Qro) : ℕ) * (δ : ℝ≥0∞)) :=
          tsum_le_tsum fun s => mul_le_mul_of_nonneg_left
            (extHandlers_bind_apply_le hvalid hHVZK hUnpred (hA s) post true) zero_le
      _ = _ := by
          rw [tsum_congr fun s => mul_add _ _ _, tsum_add, ENNReal.tsum_mul_right,
            PMF.tsum_coe, one_mul]
  have hsim := succProbability_fiatShamirNIZKSimExtGameOn_le hsound src valid admissible hA
  have htop : ((Qp * (Qp + Qro) : ℕ) : ℝ≥0∞) * (δ : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top
  have hrealLe : (Game.succProbability (fiatShamirNIZKRealExtGameOn admissible P valid A) : ℝ) ≤
      (Game.succProbability (fiatShamirNIZKSimExtGameOn admissible P simulate valid A) : ℝ) +
        Qp * (Qp + Qro) * δ := by
    simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
    have hle := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, htop⟩) hhop
    rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) htop, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.coe_toReal] at hle
    push_cast at hle
    linarith
  linarith

/-- **Derived adaptive multi-theorem simulation-extractability** of Fiat–Shamir NIZK proofs in the
random-oracle model (combining the Attack Game 20.3 / Theorem 20.3 zero-knowledge hop with
[BellareNeven2006], Lemma 1). -/
theorem succProbability_fiatShamirNIZKRealExtGame_le [DecidableEq Y] [DecidableEq T]
    [Fintype Y] [Finite T] [Finite Z] [Fintype C] [Nonempty C] [DecidableEq C] {W : Type}
    {P : SigmaProtocol X Y T C Z} {R_honest : X → Y → Prop} {R : W → Y → Prop}
    [∀ w y, Decidable (R w y)] {simulate : Y → C → PMF (T × Z)}
    {extract : Y → T → C → Z → C → Z → W} {valid : X → Y → Bool} {δ : ℝ≥0}
    (hvalid : ∀ x y, valid x y = true → R_honest x y)
    (hsound : P.SpecialSoundness R extract)
    (hHVZK : P.SpecialHVZK R_honest simulate)
    (hUnpred : P.UnpredictableCommitments R_honest δ)
    {A : NIZKSimProver X Y T C Z} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    (Game.succProbability (fiatShamirNIZKRealExtGame P valid A) : ℝ) ≤
      Qp * (Qp + Qro) * δ + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKSimExtractGame R (fun _ => true)
            (fiatShamirNIZKSimExtract P simulate extract valid A Qp Qro))) :=
  succProbability_fiatShamirNIZKRealExtGameOn_le hvalid hsound hHVZK hUnpred
    (SimCoinSource.ofFintype simulate) (fun _ => true) hA

/-- Fresh-statement corollary: outputting an accepted proof on a statement `y*` never queried on an
accepted prove call (`!(proved.map Prod.fst).contains y*`) implies `(y*, t*) ∉ proved`, so the same
simulation-extractability bound applies. -/
theorem succProbability_fiatShamirNIZKFreshStmtGame_le [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] [DecidableEq C] {W : Type} {P : SigmaProtocol X Y T C Z}
    {R_honest : X → Y → Prop} {R : W → Y → Prop} [∀ w y, Decidable (R w y)]
    {simulate : Y → C → PMF (T × Z)} {extract : Y → T → C → Z → C → Z → W}
    {valid : X → Y → Bool} {δ : ℝ≥0}
    (hvalid : ∀ x y, valid x y = true → R_honest x y)
    (hsound : P.SpecialSoundness R extract)
    (hHVZK : P.SpecialHVZK R_honest simulate)
    (hUnpred : P.UnpredictableCommitments R_honest δ)
    (src : SimCoinSource Y T C Z simulate) (admissible : Y → Bool)
    {A : NIZKSimProver X Y T C Z} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    (Game.succProbability (do
      let s ← A.coins
      let ((y, prf), (cache, proved)) ←
        (interpret (nizkRealExtHandler P valid) (A.prove s)).run ([], [])
      let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache
      return (admissible y && acc && !(proved.map Prod.fst).contains y)) : ℝ) ≤
      Qp * (Qp + Qro) * δ + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKSimExtractGame R admissible
            (fiatShamirNIZKSimExtractWith P src extract valid admissible A Qp Qro))) := by
  have hmono :
      (do
        let s ← A.coins
        let ((y, prf), (cache, proved)) ←
          (interpret (nizkRealExtHandler P valid) (A.prove s)).run ([], [])
        let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache
        return (admissible y && acc && !(proved.map Prod.fst).contains y) : PMF Bool) true ≤
      fiatShamirNIZKRealExtGameOn admissible P valid A true := by
    simp only [fiatShamirNIZKRealExtGameOn, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun s _ => ?_
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun ((y, prf), (cache, proved)) _ => ?_
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun (acc, _) _ => ?_
    by_cases hmem : (y, prf.1) ∈ proved
    · have hy : y ∈ proved.map Prod.fst := List.mem_map_of_mem hmem
      simp [hy]
    · by_cases hacc : admissible y = true ∧ acc = true
      · refine (PMF.coe_le_one _ _).trans_eq ?_
        simp [hacc.1, hacc.2, hmem]
      · cases hadm : admissible y <;> cases ha : acc
        · simp
        · simp
        · simp
        · exact absurd ⟨hadm, ha⟩ hacc
  have hle :
      (Game.succProbability (do
        let s ← A.coins
        let ((y, prf), (cache, proved)) ←
          (interpret (nizkRealExtHandler P valid) (A.prove s)).run ([], [])
        let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache
        return (admissible y && acc && !(proved.map Prod.fst).contains y)) : ℝ) ≤
      Game.succProbability (fiatShamirNIZKRealExtGameOn admissible P valid A) := by
    simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ _) hmono
  exact hle.trans
    (succProbability_fiatShamirNIZKRealExtGameOn_le hvalid hsound hHVZK hUnpred src admissible hA)

/-- **Adaptive simulation-soundness** on false statements: if every statement accepted by
`admissible` lacks a witness in `R`, then even after `Qp` adaptive prove queries on valid
statements, `A` produces an accepted proof on an `admissible` false statement with probability at
most `Qp * (Qp + Qro) * δ + (Qro + 1) / |C|`. -/
theorem succProbability_fiatShamirNIZKRealExtGameOn_le_of_false [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] {W : Type} {P : SigmaProtocol X Y T C Z}
    {R_honest : X → Y → Prop} {R : W → Y → Prop}
    {simulate : Y → C → PMF (T × Z)} {extract : Y → T → C → Z → C → Z → W}
    {valid : X → Y → Bool} {δ : ℝ≥0}
    (hvalid : ∀ x y, valid x y = true → R_honest x y)
    (hsound : P.SpecialSoundness R extract)
    (hHVZK : P.SpecialHVZK R_honest simulate)
    (hUnpred : P.UnpredictableCommitments R_honest δ)
    (src : SimCoinSource Y T C Z simulate) {admissible : Y → Bool}
    (hfalse : ∀ y, admissible y = true → ∀ w, ¬ R w y)
    {A : NIZKSimProver X Y T C Z} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    (Game.succProbability (fiatShamirNIZKRealExtGameOn admissible P valid A) : ℝ) ≤
      Qp * (Qp + Qro) * δ + (Qro + 1) / Fintype.card C := by
  classical
  have h := succProbability_fiatShamirNIZKRealExtGameOn_le hvalid hsound hHVZK hUnpred src
    admissible hA
  have hzero :
      (Game.succProbability
        (fiatShamirNIZKSimExtractGame R admissible
          (fiatShamirNIZKSimExtractWith P src extract valid admissible A Qp Qro)) : ℝ) = 0 := by
    have heq :
        fiatShamirNIZKSimExtractGame R admissible
          (fiatShamirNIZKSimExtractWith P src extract valid admissible A Qp Qro) =
        PMF.pure false := by
      simp only [fiatShamirNIZKSimExtractGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      refine (Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure false)
        fun res _ => ?_).trans (PMF.bind_const _ _)
      rcases res with _ | ⟨y, w⟩
      · rfl
      · by_cases hadm : admissible y = true
        · simp [hadm, hfalse y hadm w]
        · simp [Bool.eq_false_iff.mpr hadm]
    simp [heq, Game.succProbability]
  rw [hzero, mul_zero, Real.sqrt_zero, add_zero] at h
  exact h

/-! ### Specializations to `SigmaProtocol.linear` and `SigmaProtocol.schnorr` -/

section Linear

variable {q : ℕ} {M N Y C : Type} [AddCommGroup M] [Module (ZMod q) M] [Fintype M]
  [AddCommGroup N] [Module (ZMod q) N] [DecidableEq N]

/-- When `ψ y` is injective on every statement `y` having a witness `x` with `ψ y x = u y`, the
commitments `ψ y r` of `linear ψ u ι` are `(Fintype.card M)⁻¹`-unpredictable. -/
theorem linear_unpredictableCommitments_of_injective (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N)
    (ι : C ↪ ZMod q) (hinj : ∀ x y, ψ y x = u y → Function.Injective (ψ y)) :
    (linear ψ u ι).UnpredictableCommitments (fun x y => ψ y x = u y) (Fintype.card M : ℝ≥0)⁻¹ := by
  classical
  intro x y hxy t
  have hcard : (Fintype.card M : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmap : ((linear ψ u ι).commit x y).map Prod.fst =
      (PMF.uniformOfFintype M).map (ψ y) := by
    simp only [linear, PMF.map_comp]
    rfl
  rw [ENNReal.coe_inv hcard, ENNReal.coe_natCast, hmap, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply, Probability.PMF.toOuterMeasure_uniformOfFintype]
  calc ((Finset.univ.filter (· ∈ (ψ y) ⁻¹' {t})).card : ℝ≥0∞) * (Fintype.card M : ℝ≥0∞)⁻¹
      ≤ 1 * (Fintype.card M : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast Finset.card_le_one.mpr fun a ha b hb =>
          hinj x y hxy (by simp_all)
    _ = (Fintype.card M : ℝ≥0∞)⁻¹ := one_mul _

/-- Statement-independent `SimCoinSource` for `linearSimulate ψ u ι`: a single uniform draw from
`C × M` determines `(ψ y z - ι c • u y, c, z)` at every statement `y`, requiring no finiteness on
`Y` or `N`. -/
@[expose] noncomputable def linearSimCoinSource [Fintype C] [Nonempty C]
    (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q) :
    SimCoinSource Y N C M (linearSimulate ψ u ι) where
  Coins := C × M
  coins := PMF.uniformOfFintype (C × M)
  eval cz y := (ψ y cz.2 - ι cz.1 • u y, cz.1, cz.2)
  map_eval y := by
    rw [← Probability.PMF.uniformOfFintype_prod]
    simp only [simulateConversation, linearSimulate, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
    rfl

/-- Adaptive multi-theorem NIZK zero-knowledge bound for `SigmaProtocol.linear`. -/
theorem linear_advantage_fiatShamirNIZKRealGame_simGame_le [DecidableEq Y] [Fintype C]
    [Nonempty C] (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q)
    (hinj : ∀ x y, ψ y x = u y → Function.Injective (ψ y))
    {D : OracleComp (NIZKDistinguisherSpec M Y N C M) Bool} {Qp Qro : ℕ}
    (hD : NIZKCallBounded D Qp Qro) :
    (Game.advantage
      (fiatShamirNIZKRealGame (linear ψ u ι) (fun x y => decide (ψ y x = u y)) D)
      (fiatShamirNIZKSimGame (linearSimulate ψ u ι) (fun x y => decide (ψ y x = u y)) D) : ℝ) ≤
      Qp * (Qp + Qro) / Fintype.card M := by
  have h := NNReal.coe_le_coe.mpr
    (advantage_fiatShamirNIZKRealGame_simGame_le
      (fun x y h => of_decide_eq_true h)
      (linear_specialHVZK ψ u ι)
      (linear_unpredictableCommitments_of_injective ψ u ι hinj) hD)
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast,
    div_eq_mul_inv] using h

/-- Plain ROM proof-of-knowledge bound for `SigmaProtocol.linear` when `q` is prime. -/
theorem linear_succProbability_fiatShamirNIZKPokGame_le [Fact q.Prime] [DecidableEq Y]
    [Fintype C] [Nonempty C] [DecidableEq C]
    (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q)
    (A : NIZKProver Y N C M) {Qro : ℕ} (y : Y)
    (hQro : ∀ s, IsQueryBounded (A.prove y s) Qro) :
    (Game.succProbability (fiatShamirNIZKPokGame (linear ψ u ι) A y) : ℝ) ≤
      (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKExtractGame (fun x y => ψ y x = u y)
            (fiatShamirNIZKExtract (linear ψ u ι) (linearExtract ι) A Qro y) y)) :=
  succProbability_fiatShamirNIZKPokGame_le (linear_specialSoundness ψ u ι) A y hQro

/-- Adaptive multi-theorem simulation-extractability bound for `SigmaProtocol.linear` when `q` is
prime (requiring no finiteness on `Y` or `N`). -/
theorem linear_succProbability_fiatShamirNIZKRealExtGame_le [Fact q.Prime] [DecidableEq Y]
    [Fintype C] [Nonempty C] [DecidableEq C]
    (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q)
    (hinj : ∀ x y, ψ y x = u y → Function.Injective (ψ y))
    (admissible : Y → Bool)
    {A : NIZKSimProver M Y N C M} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    (Game.succProbability
      (fiatShamirNIZKRealExtGameOn admissible (linear ψ u ι)
        (fun x y => decide (ψ y x = u y)) A) : ℝ) ≤
      Qp * (Qp + Qro) / Fintype.card M + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKSimExtractGame (fun x y => ψ y x = u y) admissible
            (fiatShamirNIZKSimExtractWith (linear ψ u ι) (linearSimCoinSource ψ u ι)
              (linearExtract ι) (fun x y => decide (ψ y x = u y)) admissible A Qp Qro))) := by
  have h := succProbability_fiatShamirNIZKRealExtGameOn_le
    (fun x y hv => of_decide_eq_true hv)
    (linear_specialSoundness ψ u ι)
    (linear_specialHVZK ψ u ι)
    (linear_unpredictableCommitments_of_injective ψ u ι hinj)
    (linearSimCoinSource ψ u ι) admissible hA
  simpa only [NNReal.coe_inv, NNReal.coe_natCast, div_eq_mul_inv] using h

end Linear

section Schnorr

variable {q : ℕ} [Fact q.Prime] {G C : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]
  {ι : C ↪ ZMod q} {g : G}

/-- Commitments of `schnorr ι g` are `(q : ℝ≥0)⁻¹`-unpredictable whenever `g ≠ 0`
(reusing `schnorr_commit_map_fst_le`). -/
theorem schnorr_unpredictableCommitments (hg : g ≠ 0) :
    (schnorr ι g).UnpredictableCommitments (fun α u => α • g = u) (q : ℝ≥0)⁻¹ := by
  have hq : (q : ℝ≥0) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  intro x y _ t
  rw [ENNReal.coe_inv hq, ENNReal.coe_natCast]
  exact schnorr_commit_map_fst_le (ι := ι) hg x y t

/-- Perfect completeness of Schnorr Fiat–Shamir NIZK proofs in the lazy random-oracle model. -/
theorem schnorr_fiatShamirNIZK_complete [Fintype C] [Nonempty C]
    {α : ZMod q} {u : G} (hαu : α • g = u) (cache : List ((G × G) × C)) :
    (do
      let coins ← (schnorr ι g).commit α u
      let (prf, cache') ← (interpret (oracle C) (fiatShamirNIZKProve (schnorr ι g) α u coins)).run
        cache
      let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify (schnorr ι g) u prf)).run cache'
      return acc) = PMF.pure true :=
  fiatShamirNIZK_complete schnorr_complete hαu cache

/-- Adaptive multi-theorem NIZK zero-knowledge bound `Qp * (Qp + Qro) / q` for Schnorr Fiat–Shamir
NIZK proofs when `g ≠ 0`. -/
theorem schnorr_advantage_fiatShamirNIZKRealGame_simGame_le [Fintype C] [Nonempty C]
    (hg : g ≠ 0)
    {D : OracleComp (NIZKDistinguisherSpec (ZMod q) G G C (ZMod q)) Bool} {Qp Qro : ℕ}
    (hD : NIZKCallBounded D Qp Qro) :
    (Game.advantage
      (fiatShamirNIZKRealGame (schnorr ι g) (fun α u => decide (α • g = u)) D)
      (fiatShamirNIZKSimGame
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι)
        (fun α u => decide (α • g = u)) D) : ℝ) ≤
      Qp * (Qp + Qro) / q := by
  have h := NNReal.coe_le_coe.mpr
    (advantage_fiatShamirNIZKRealGame_simGame_le
      (fun α u hv => of_decide_eq_true hv)
      schnorr_specialHVZK
      (schnorr_unpredictableCommitments (ι := ι) hg) hD)
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast,
    div_eq_mul_inv] using h

/-- Plain ROM proof-of-knowledge bound for Schnorr Fiat–Shamir NIZK proofs. -/
theorem schnorr_succProbability_fiatShamirNIZKPokGame_le [Fintype C] [Nonempty C] [DecidableEq C]
    (A : NIZKProver G G C (ZMod q)) {Qro : ℕ} (u : G)
    (hQro : ∀ s, IsQueryBounded (A.prove u s) Qro) :
    (Game.succProbability (fiatShamirNIZKPokGame (schnorr ι g) A u) : ℝ) ≤
      (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKExtractGame (fun α u => α • g = u)
            (fiatShamirNIZKExtract (schnorr ι g) (linearExtract ι) A Qro u) u)) :=
  succProbability_fiatShamirNIZKPokGame_le schnorr_specialSoundness A u hQro

/-- Adaptive multi-theorem simulation-extractability bound
`Qp * (Qp + Qro) / q + (Qro + 1) / |C| + √((Qro + 1) * ε')` for Schnorr Fiat–Shamir NIZK proofs
when `g ≠ 0` (requiring no finiteness assumption on `G`). -/
theorem schnorr_succProbability_fiatShamirNIZKRealExtGame_le [Fintype C] [Nonempty C]
    [DecidableEq C] (hg : g ≠ 0) (admissible : G → Bool)
    {A : NIZKSimProver (ZMod q) G G C (ZMod q)} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    (Game.succProbability
      (fiatShamirNIZKRealExtGameOn admissible (schnorr ι g)
        (fun α u => decide (α • g = u)) A) : ℝ) ≤
      Qp * (Qp + Qro) / q + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKSimExtractGame (fun α u => α • g = u) admissible
            (fiatShamirNIZKSimExtractWith (schnorr ι g)
              (linearSimCoinSource (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι)
              (linearExtract ι) (fun α u => decide (α • g = u)) admissible A Qp Qro))) := by
  have h := succProbability_fiatShamirNIZKRealExtGameOn_le
    (fun α u hv => of_decide_eq_true hv)
    schnorr_specialSoundness
    schnorr_specialHVZK
    (schnorr_unpredictableCommitments (ι := ι) hg)
    (linearSimCoinSource (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι)
    admissible hA
  simpa only [NNReal.coe_inv, NNReal.coe_natCast, div_eq_mul_inv] using h

end Schnorr

end Cslib.Crypto.Protocols.SigmaProtocol

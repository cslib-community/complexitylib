/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.ForkingReduction
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Identification
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrSignature
public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
public import CslibFrontier.Languages.Probabilistic.Forking
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Union

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
  `Cslib.Crypto.Protocols.SigmaProtocol.fiatShamirNIZKFreshStmtGameOn`,
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
  `Cslib.Crypto.Protocols.SigmaProtocol.succProbability_fiatShamirNIZKFreshStmtGameOn_le`,
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
      StateT (ExtGameState Y T C × Bool) PMF (NIZKDistinguisherSpec X Y T C Z q) :=
  RandomOracle.flaggedOverwriteProgramHandler (Reply := fun _ : X × Y => Option (T × Z))
    (PMF.uniformOfFintype C) (fun xy => valid xy.1 xy.2)
    (fun _ _ proved => PMF.pure (none, proved)) (fun xy => P.commit xy.1 xy.2)
    (fun xy ts => (xy.2, ts.1))
    (fun xy ts c proved => (some (ts.1, P.respond xy.1 xy.2 ts.2 c), (xy.2, ts.1) :: proved))

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

private theorem realFlaggedHandler_eq_flaggedLazyProgramHandler [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) :
    realFlaggedHandler P valid =
      RandomOracle.flaggedLazyProgramHandler (Reply := fun _ : X × Y => Option (T × Z))
        (PMF.uniformOfFintype C) (fun xy => valid xy.1 xy.2)
        (fun _ _ proved => PMF.pure (none, proved)) (fun xy => P.commit xy.1 xy.2)
        (fun xy ts => (xy.2, ts.1))
        (fun xy ts c proved =>
          (some (ts.1, P.respond xy.1 xy.2 ts.2 c), (xy.2, ts.1) :: proved)) := by
  funext q ⟨⟨cache, proved⟩, b⟩
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    rw [RandomOracle.flaggedLazyProgramHandler_apply_inl]
    by_cases hv : valid x y = true
    · simp only [realFlaggedHandler, hv, ↓reduceIte, ↓reduceDIte, oracle]
    · simp only [realFlaggedHandler, hv, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, PMF.pure_map]
  | inr yt =>
    rw [RandomOracle.flaggedLazyProgramHandler_apply_inr]
    rfl

private theorem nizkRealExtHandler_eq_lazyProgramHandler [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) :
    nizkRealExtHandler P valid =
      RandomOracle.lazyProgramHandler (Reply := fun _ : X × Y => Option (T × Z))
        (PMF.uniformOfFintype C) (fun xy => valid xy.1 xy.2)
        (fun _ _ proved => PMF.pure (none, proved)) (fun xy => P.commit xy.1 xy.2)
        (fun xy ts => (xy.2, ts.1))
        (fun xy ts c proved =>
          (some (ts.1, P.respond xy.1 xy.2 ts.2 c), (xy.2, ts.1) :: proved)) := by
  funext q ⟨cache, proved⟩
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · simp only [pmf_norm, nizkRealExtHandler, fiatShamirNIZKProve,
        RandomOracle.lazyProgramHandler, hv, ↓reduceIte, ↓reduceDIte, interpret_map,
        interpret_query, StateT.run_map, oracle]
      rfl
    · simp only [nizkRealExtHandler, RandomOracle.lazyProgramHandler, hv, Bool.false_eq_true,
        ↓reduceIte, ↓reduceDIte, PMF.pure_map]
  | inr yt =>
    rfl

private theorem nizkSimExtHandler_eq_overwriteProgramHandler [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop}
    {simulate : Y → C → PMF (T × Z)} {valid : X → Y → Bool}
    (hvalid : ∀ x y, valid x y = true → R x y) (hHVZK : P.SpecialHVZK R simulate) :
    nizkSimExtHandler simulate valid =
      RandomOracle.overwriteProgramHandler (Reply := fun _ : X × Y => Option (T × Z))
        (PMF.uniformOfFintype C) (fun xy => valid xy.1 xy.2)
        (fun _ _ proved => PMF.pure (none, proved)) (fun xy => P.commit xy.1 xy.2)
        (fun xy ts => (xy.2, ts.1))
        (fun xy ts c proved =>
          (some (ts.1, P.respond xy.1 xy.2 ts.2 c), (xy.2, ts.1) :: proved)) := by
  funext q ⟨cache, proved⟩
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · simp only [pmf_norm, nizkSimExtHandler, nizkSimProve, RandomOracle.overwriteProgramHandler,
        hv, ↓reduceIte, ↓reduceDIte]
      have htr := hHVZK.transcript_eq x y (hvalid x y hv)
      conv_lhs =>
        enter [2, c]
        rw [htr c, SigmaProtocol.transcript, PMF.bind_map]
      rw [PMF.bind_comm]
      rfl
    · simp only [nizkSimExtHandler, RandomOracle.overwriteProgramHandler, hv, Bool.false_eq_true,
        ↓reduceIte, ↓reduceDIte, PMF.pure_map]
  | inr yt =>
    rfl

/-- `realFlaggedHandler` and `programFlaggedHandler` are identical until the collision flag is
raised. -/
private theorem identicalUntilBad_flaggedHandlers [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] (P : SigmaProtocol X Y T C Z) (valid : X → Y → Bool) :
    IdenticalUntilBad (realFlaggedHandler P valid) (programFlaggedHandler P valid)
      fun st => st.2 = true := by
  rw [realFlaggedHandler_eq_flaggedLazyProgramHandler, programFlaggedHandler]
  exact RandomOracle.identicalUntilBad_flaggedProgramHandlers _ _ _ _ _ _

/-- Union bound for a commitment hitting an existing cache entry at `(y, ·)`. -/
private theorem toOuterMeasure_lookup_commit_le [DecidableEq Y] [DecidableEq T]
    (P : SigmaProtocol X Y T C Z) {x : X} {y : Y} {δ : ℝ≥0∞}
    (hcommit : ∀ t, (P.commit x y).map Prod.fst t ≤ δ) (cache : List ((Y × T) × C)) :
    (P.commit x y).toOuterMeasure {ts | (cache.lookup (y, ts.1)).isSome} ≤
      cache.length * δ := by
  refine Probability.PMF.toOuterMeasure_lookup_isSome_le _ _ (fun k => ?_) cache
  calc (P.commit x y).toOuterMeasure {ts | (y, ts.1) = k}
      ≤ (P.commit x y).toOuterMeasure (Prod.fst ⁻¹' {k.2}) :=
        (P.commit x y).toOuterMeasure.mono fun ts (hts : (y, ts.1) = k) =>
          (congrArg Prod.snd hts : ts.1 = k.2)
    _ ≤ δ := by
        rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
        exact hcommit k.2

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
      · simp only [realFlaggedHandler, hv, ↓reduceIte]
        refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
          {ts : T × P.State | (st.1.1.lookup (y, ts.1)).isSome} _ 0
          fun ts _ hts => le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
            (Set.disjoint_left.mpr fun out hout hbad => ?_))).trans ?_
        · obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
          simp_all
        · rw [add_zero]
          exact toOuterMeasure_lookup_commit_le P (hUnpred x y (hvalid x y hv)) st.1.1
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
  have hreal : ((interpret (realFlaggedHandler P valid) program).run (([], []), false)).map
      (Prod.map id Prod.fst) =
      (interpret (nizkRealExtHandler P valid) program).run ([], []) := by
    rw [realFlaggedHandler_eq_flaggedLazyProgramHandler, nizkRealExtHandler_eq_lazyProgramHandler]
    exact RandomOracle.run_flaggedLazyProgramHandler_map_fst _ _ _ _ _ _ _ _ false
  have hsim : ((interpret (programFlaggedHandler P valid) program).run (([], []), false)).map
      (Prod.map id Prod.fst) =
      (interpret (nizkSimExtHandler simulate valid) program).run ([], []) := by
    rw [programFlaggedHandler, nizkSimExtHandler_eq_overwriteProgramHandler hvalid hHVZK]
    exact RandomOracle.run_flaggedOverwriteProgramHandler_map_fst _ _ _ _ _ _ _ _ false
  rw [← hreal, ← hsim, PMF.bind_map, PMF.bind_map]
  have hdiff := (identicalUntilBad_flaggedHandlers P valid).abs_sub_le program (([], []), false)
    (next ∘ Prod.map id Prod.fst) b
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
  have hreal : ((interpret (realFlaggedHandler P valid) program).run (([], []), false)).map
      (Prod.map id Prod.fst) =
      (interpret (nizkRealExtHandler P valid) program).run ([], []) := by
    rw [realFlaggedHandler_eq_flaggedLazyProgramHandler, nizkRealExtHandler_eq_lazyProgramHandler]
    exact RandomOracle.run_flaggedLazyProgramHandler_map_fst _ _ _ _ _ _ _ _ false
  have hsim : ((interpret (programFlaggedHandler P valid) program).run (([], []), false)).map
      (Prod.map id Prod.fst) =
      (interpret (nizkSimExtHandler simulate valid) program).run ([], []) := by
    rw [programFlaggedHandler, nizkSimExtHandler_eq_overwriteProgramHandler hvalid hHVZK]
    exact RandomOracle.run_flaggedOverwriteProgramHandler_map_fst _ _ _ _ _ _ _ _ false
  rw [← hreal, ← hsim, PMF.bind_map, PMF.bind_map]
  exact ((identicalUntilBad_flaggedHandlers P valid).bind_apply_le program (([], []), false)
    (next ∘ Prod.map id Prod.fst) b).trans
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
    simp only [pmf_norm, fiatShamirNIZKRealGame, ← hreal]
  have hsimEq : fiatShamirNIZKSimGame simulate valid D =
      ((interpret (nizkSimExtHandler simulate valid) D).run ([], [])).bind
        (fun (b, _) => PMF.pure b) := by
    simp only [pmf_norm, fiatShamirNIZKSimGame, ← hsim]
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

/-! ### The forking reduction for proofs of knowledge -/

namespace FiatShamirNIZK

/-- The final check on a candidate proof `(y, (t, z))`: its point is `(y, t)`, and it wins when
`admissible y`, `(t, c, z)` is accepting for `y`, and `(y, t)` was not returned by a valid prove
call. -/
private def check [DecidableEq Y] [DecidableEq T] (P : SigmaProtocol X Y T C Z)
    (admissible : Y → Bool) : ForkingReduction.Check Y T C Z (Y × T) (Y × T) where
  point y t := (y, t)
  accepts y t c z := admissible y && P.verify y t c z
  fresh y t proved := !proved.contains (y, t)

/-- Proving without a witness, from one presampled value per call: a valid prove call on `(x, y)`
evaluates `simEval` to a transcript `(t, c, z)`, returns `(t, z)`, programs the oracle at `(y, t)`
with `c` and logs `(y, t)`; an invalid call returns `none`. -/
private def signer {S : Type} (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) :
    ForkingReduction.Signer (X × Y) (Option (T × Z)) (Y × T) C (Y × T) S where
  fallback := fallback
  step s q :=
    if hv : valid q.1 q.2 = true then
      let v := simEval s q.1 q.2 hv
      (some (v.1, v.2.2), some ((q.2, v.1), v.2.1, (q.2, v.1)))
    else (none, none)

/-- A candidate at a point programmed by a valid prove call is not fresh once that call's pair is
logged. -/
private theorem rejectsProgrammed [DecidableEq Y] [DecidableEq T] {S W : Type}
    (P : SigmaProtocol W Y T C Z) (valid : X → Y → Bool) (fallback : S)
    (simEval : S → ∀ x y, valid x y = true → T × C × Z) (admissible : Y → Bool) :
    ForkingReduction.RejectsProgrammed (signer valid fallback simEval) (check P admissible) := by
  intro s q x c l hr y t log hpt hl
  simp only [signer] at hr
  split_ifs at hr with hv
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, -, rfl⟩ := hr
  simp only [check] at hpt ⊢
  rw [hpt]
  simp [hl]

/-- The signer of the plain proof-of-knowledge experiment, which has no prove calls. -/
private abbrev plainSigner : ForkingReduction.Signer (Empty × Y) (Option (T × Z)) (Y × T) C (Y × T)
    Unit :=
  signer (fun e _ => e.elim) () (fun _ e => e.elim)

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
    IsCostBounded hashCost (liftPlainProve (T := T) (C := C) (Z := Z) y prog) Qro := by
  rw [liftPlainProve, isCostBounded_map_iff]
  refine hQro.interpret fun yt => ?_
  exact .liftBind (Sum.inr yt : (Empty × Y) ⊕ (Y × T)) _ 0 fun _ => .pure _ 0

/-- Plain ROM forking program for `A` on statement `y`. -/
private def plainForkingProg [DecidableEq Y] [DecidableEq T] (P : SigmaProtocol X Y T C Z)
    (A : NIZKProver Y T C Z) (y : Y) (s : A.Coins) :
    OracleComp (NIZKHashSpec Y T C) (Option ℕ × ForkingReduction.Outcome Y T C Z) :=
  ForkingReduction.program FiatShamirNIZK.plainSigner
    (FiatShamirNIZK.check P fun y' => decide (y' = y)) (liftPlainProve y (A.prove y s)) []

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
        fun ((_, outcome), _) => outcome.won := by
  simp only [fiatShamirNIZKPokGame, plainForkingProg, ForkingReduction.map_run_program,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine congrArg A.coins.bind (funext fun s => ?_)
  have hstep :
      ∀ (yt : Y × T) (cache : List ((Y × T) × C)),
        (oracle C yt cache).map
          (fun (c, cache') => (c, ((cache', ([] : List (Y × T))), ([] : List Unit)))) =
        withSampleList ()
          (ForkingReduction.gameHandler (FiatShamirNIZK.plainSigner (Z := Z)))
          (.inr yt) ((cache, []), []) := by
    intro yt cache
    simp only [pmf_norm, withSampleList, ForkingReduction.gameHandler, List.tail_nil]
  have hsim := run_interpret_map_state (oracle C)
    (fun yt st =>
      withSampleList () (ForkingReduction.gameHandler (FiatShamirNIZK.plainSigner (Z := Z)))
        (.inr yt) st)
    (fun cache => ((cache, ([] : List (Y × T))), ([] : List Unit)))
    hstep (A.prove y s) []
  rw [liftPlainProve, run_interpret_map, interpret_interpret]
  simp only [PMF.monad_map_eq_map, PMF.bind_map, interpret_query]
  rw [← hsim]
  simp only [pmf_norm, ForkingReduction.finishGame, FiatShamirNIZK.check, fiatShamirNIZKVerify,
    interpret_map, interpret_query, StateT.run_map]
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
  simp only [pmf_norm, fiatShamirNIZKExtractGame, fiatShamirNIZKExtract]
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun result hresult => ?_
  rcases result with _ | ⟨j, ⟨⟨_, o⟩, _⟩, ⟨⟨_, o'⟩, _⟩⟩
  · simp
  · obtain ⟨s, -, hpt, hne, hv, hv'⟩ := ForkingReduction.exists_of_mem_support_fork
      (first := A.coins) FiatShamirNIZK.plainSigner
      (fun _ => FiatShamirNIZK.check P fun y' => decide (y' = y))
      (fun _ => FiatShamirNIZK.rejectsProgrammed _ _ _ _ _)
      (fun s => liftPlainProve y (A.prove y s)) (fun _ => []) hresult
    simp only [FiatShamirNIZK.check, Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq]
      at hpt hv hv'
    obtain ⟨hy, ht⟩ := hpt
    have hacc : P.Accepts y o.commitment o.challenge o.response := by
      simpa only [SigmaProtocol.Accepts, hv.1] using hv.2
    have hacc' : P.Accepts y o.commitment o'.challenge o'.response := by
      simpa only [SigmaProtocol.Accepts, hv'.1, ht] using hv'.2
    have hR := hsound _ _ _ _ _ hne hacc hacc'
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
  have h := ForkingReduction.toReal_le_add_sqrt_fork_of_le (p := fiatShamirNIZKPokGame P A y true)
    A.coins FiatShamirNIZK.plainSigner (fun _ => FiatShamirNIZK.check P fun y' => decide (y' = y))
    (fun _ => FiatShamirNIZK.rejectsProgrammed _ _ _ _ _)
    (fun s => liftPlainProve y (A.prove y s)) (fun _ => [])
    (fun s => isCostBounded_liftPlainProve (hQro s)) ENNReal.zero_ne_top
    (by rw [pokGame_eq_plainForkingProg, add_zero]; rfl)
    (fork_plain_le_extractGame (hsound y) A Qro) (PMF.apply_ne_top _ _)
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  push_cast at h ⊢
  linarith [ENNReal.toReal_zero]

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
  have hp : (keyGen.bind fun (_, y) => fiatShamirNIZKPokGame P A y) true ≤
      first.bind (fun ks =>
        ((interpret countingUniform (plainForkingProg P A ks.1.2 ks.2)).run 0).map
          fun ((_, outcome), _) => outcome.won) true + 0 := by
    rw [add_zero]
    simp only [pmf_norm, first, pokGame_eq_plainForkingProg]
    exact le_rfl
  have hD : (Forking.fork first (forkingAlgorithm (Classical.arbitrary C) (Qro + 1)
      fun ks => plainForkingProg P A ks.1.2 ks.2)).map Option.isSome true ≤
      oneWayGame keyGen R (fun y =>
        (fiatShamirNIZKExtract P extract A Qro y).map
          (fun w => w.getD (Classical.arbitrary X))) true := by
    have hfork : Forking.fork first (forkingAlgorithm (Classical.arbitrary C) (Qro + 1)
        fun ks => plainForkingProg P A ks.1.2 ks.2) =
        keyGen.bind fun key =>
          Forking.fork A.coins
            (forkingAlgorithm (Classical.arbitrary C) (Qro + 1) (plainForkingProg P A key.2)) := by
      simp only [pmf_norm, first, Forking.fork]
      rfl
    rw [hfork, PMF.map_bind]
    simp only [pmf_norm, oneWayGame]
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun key hkey => ?_
    refine (fork_plain_le_extractGame (hsound key hkey) A Qro).trans ?_
    simp only [fiatShamirNIZKExtractGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun res _ => ?_
    cases res <;> simp
  have h := ForkingReduction.toReal_le_add_sqrt_fork_of_le first FiatShamirNIZK.plainSigner
    (fun ks => FiatShamirNIZK.check P fun y' => decide (y' = ks.1.2))
    (fun _ => FiatShamirNIZK.rejectsProgrammed _ _ _ _ _)
    (fun ks => liftPlainProve ks.1.2 (A.prove ks.1.2 ks.2)) (fun _ => [])
    (fun ks => isCostBounded_liftPlainProve (hQro ks.1.2 ks.2)) ENNReal.zero_ne_top hp hD
    (PMF.apply_ne_top _ _)
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  push_cast at h ⊢
  linarith [ENNReal.toReal_zero]

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

/-- Real fresh-statement experiment with final-statement guard `admissible`: as
`fiatShamirNIZKRealExtGameOn`, but the output statement `y*` itself must not have been answered by a
valid prove call. -/
@[expose] noncomputable def fiatShamirNIZKFreshStmtGameOn [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] (admissible : Y → Bool) (P : SigmaProtocol X Y T C Z)
    (valid : X → Y → Bool) (A : NIZKSimProver X Y T C Z) : Game := do
  let s ← A.coins
  let ((y, prf), (cache, proved)) ←
    (interpret (nizkRealExtHandler P valid) (A.prove s)).run ([], [])
  let (acc, _) ← (interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache
  return (admissible y && acc && !(proved.map Prod.fst).contains y)

/-- The signer of the simulation-extractability reduction: a valid prove call on `(x, y)` reads
the transcript `src.eval r y` from presampled coins `r`. -/
private noncomputable abbrev simSigner [Fintype C] [Nonempty C] {simulate : Y → C → PMF (T × Z)}
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool) :
    ForkingReduction.Signer (X × Y) (Option (T × Z)) (Y × T) C (Y × T) src.Coins :=
  FiatShamirNIZK.signer valid src.coins.support_nonempty.some fun r _ y _ => src.eval r y

/-- Forking program for simulation-extractability using `src : SimCoinSource`. -/
private noncomputable def simForkingProg [DecidableEq Y] [DecidableEq T] [Fintype C] [Nonempty C]
    {simulate : Y → C → PMF (T × Z)} (P : SigmaProtocol X Y T C Z)
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool) (admissible : Y → Bool)
    (A : NIZKSimProver X Y T C Z) (s : A.Coins × List src.Coins) :
    OracleComp (NIZKHashSpec Y T C) (Option ℕ × ForkingReduction.Outcome Y T C Z) :=
  ForkingReduction.program (simSigner src valid) (FiatShamirNIZK.check P admissible)
    (A.prove s.1) s.2

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
          some (out.2.message,
            extract out.2.message out.2.commitment out.2.challenge out.2.response
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

private theorem gameHandler_bind_eq_nizkSimExtHandler [DecidableEq Y] [DecidableEq T]
    [Fintype C] [Nonempty C] {simulate : Y → C → PMF (T × Z)}
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool)
    (q : (X × Y) ⊕ (Y × T)) (st : ExtGameState Y T C) :
    src.coins.bind (fun r => ForkingReduction.gameHandler (simSigner src valid) r q st) =
      nizkSimExtHandler simulate valid q st := by
  obtain ⟨cache, proved⟩ := st
  cases q with
  | inl xy =>
    obtain ⟨x, y⟩ := xy
    by_cases hv : valid x y = true
    · simp only [pmf_norm, ForkingReduction.gameHandler, FiatShamirNIZK.signer, nizkSimExtHandler,
        nizkSimProve, hv, ↓reduceDIte, ↓reduceIte, ForkingReduction.recordGame]
      have hmap := congrArg
        (fun μ : PMF (T × C × Z) =>
          μ.bind fun v => PMF.pure (some (v.1, v.2.2), (((y, v.1), v.2.1) :: cache,
            (y, v.1) :: proved)))
        (src.map_eval y)
      simpa only [pmf_norm, simulateConversation] using hmap
    · simp only [Bool.not_eq_true] at hv
      simp only [ForkingReduction.gameHandler, FiatShamirNIZK.signer, hv, Bool.false_eq_true,
        ↓reduceDIte, nizkSimExtHandler, ↓reduceIte, ForkingReduction.recordGame, PMF.bind_const]
  | inr yt =>
    simp only [ForkingReduction.gameHandler, nizkSimExtHandler, PMF.bind_const]

private theorem simExtGameOn_eq_simForkingProg [DecidableEq Y] [DecidableEq T] [Fintype C]
    [Nonempty C] {simulate : Y → C → PMF (T × Z)} (P : SigmaProtocol X Y T C Z)
    (src : SimCoinSource Y T C Z simulate) (valid : X → Y → Bool) (admissible : Y → Bool)
    {A : NIZKSimProver X Y T C Z} {Qp Qro : ℕ} (hA : A.CallBounded Qp Qro) :
    fiatShamirNIZKSimExtGameOn admissible P simulate valid A =
      (simForkCoins src A (Qp + Qro)).bind fun s =>
        ((interpret countingUniform (simForkingProg P src valid admissible A s)).run 0).map
          fun ((_, outcome), _) => outcome.won := by
  simp only [fiatShamirNIZKSimExtGameOn, simForkCoins, simForkingProg,
    ForkingReduction.map_run_program, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  refine congrArg A.coins.bind (funext fun s => ?_)
  have hpre := (hA s).isQueryBounded.run_interpret_presample src.coins
    (simSigner src valid).fallback (ForkingReduction.gameHandler (simSigner src valid)) ([], [])
  have hstep :
      (fun q state =>
        src.coins.bind fun value =>
          ForkingReduction.gameHandler (simSigner src valid) value q state) =
      nizkSimExtHandler simulate valid :=
    funext fun q => funext fun state => gameHandler_bind_eq_nizkSimExtHandler src valid q state
  rw [hstep] at hpre
  have hfin :
      ((interpret (nizkSimExtHandler simulate valid) (A.prove s)).run ([], [])).bind
        (fun ((y, prf), (cache, proved)) =>
          ((interpret (oracle C) (fiatShamirNIZKVerify P y prf)).run cache).bind
            fun (acc, _) => PMF.pure (admissible y && acc && !proved.contains (y, prf.1))) =
      ((interpret (nizkSimExtHandler simulate valid) (A.prove s)).run ([], [])).bind
        (ForkingReduction.finishGame (FiatShamirNIZK.check P admissible)) := by
    refine congrArg (PMF.bind _) (funext fun ((y, prf), (cache, proved)) => ?_)
    simp only [ForkingReduction.finishGame, FiatShamirNIZK.check, fiatShamirNIZKVerify,
      interpret_map, interpret_query, StateT.run_map, PMF.monad_map_eq_map, PMF.bind_map,
      Function.comp_def]
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
  simp only [pmf_norm, fiatShamirNIZKSimExtractGame, fiatShamirNIZKSimExtractWith]
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun result hresult => ?_
  rcases result with _ | ⟨j, ⟨⟨_, o⟩, _⟩, ⟨⟨_, o'⟩, _⟩⟩
  · simp
  · obtain ⟨s, -, hpt, hne, hv, hv'⟩ := ForkingReduction.exists_of_mem_support_fork
      (first := simForkCoins src A (Qp + Qro)) (simSigner src valid)
      (fun _ => FiatShamirNIZK.check P admissible)
      (fun _ => FiatShamirNIZK.rejectsProgrammed _ _ _ _ _)
      (fun s => A.prove s.1) (fun s => s.2) hresult
    simp only [FiatShamirNIZK.check, Prod.mk.injEq, Bool.and_eq_true] at hpt hv hv'
    obtain ⟨hy, ht⟩ := hpt
    have hacc' :
        P.Accepts o.message o.commitment o'.challenge o'.response := by
      simpa only [SigmaProtocol.Accepts, hy, ht] using hv'.2
    have hR := hsound _ _ _ _ _ _ hne hv.2 hacc'
    have hadm := hv.1
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
  have h := ForkingReduction.toReal_le_add_sqrt_fork_of_le
    (p := fiatShamirNIZKSimExtGameOn admissible P simulate valid A true)
    (simForkCoins src A (Qp + Qro)) (simSigner src valid)
    (fun _ => FiatShamirNIZK.check P admissible)
    (fun _ => FiatShamirNIZK.rejectsProgrammed _ _ _ _ _) (fun s => A.prove s.1) (fun s => s.2)
    (fun s => (hA s.1).2.of_le fun q => by cases q <;> rfl) ENNReal.zero_ne_top
    (by rw [simExtGameOn_eq_simForkingProg P src valid admissible hA, add_zero]; rfl)
    (fork_sim_le_simExtractGame hsound src valid admissible A Qp Qro) (PMF.apply_ne_top _ _)
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  push_cast at h ⊢
  linarith [ENNReal.toReal_zero]

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
    exact Probability.PMF.bind_apply_le_add_const_on_support _ _ fun s _ =>
      extHandlers_bind_apply_le hvalid hHVZK hUnpred (hA s) post true
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
theorem succProbability_fiatShamirNIZKFreshStmtGameOn_le [DecidableEq Y] [DecidableEq T]
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
    (Game.succProbability (fiatShamirNIZKFreshStmtGameOn admissible P valid A) : ℝ) ≤
      Qp * (Qp + Qro) * δ + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability
          (fiatShamirNIZKSimExtractGame R admissible
            (fiatShamirNIZKSimExtractWith P src extract valid admissible A Qp Qro))) := by
  have hmono : fiatShamirNIZKFreshStmtGameOn admissible P valid A true ≤
      fiatShamirNIZKRealExtGameOn admissible P valid A true := by
    simp only [fiatShamirNIZKFreshStmtGameOn, fiatShamirNIZKRealExtGameOn, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure]
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
  refine le_trans ?_
    (succProbability_fiatShamirNIZKRealExtGameOn_le hvalid hsound hHVZK hUnpred src admissible hA)
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  exact ENNReal.toReal_mono (PMF.apply_ne_top _ _) hmono

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
    simp only [pmf_norm, simulateConversation, linearSimulate]
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

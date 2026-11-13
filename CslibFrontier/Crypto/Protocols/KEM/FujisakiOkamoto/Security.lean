/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.KEM
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto
public import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.RandomOracle.Represented
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Tactic.PMFSwap

/-!
# ROM IND-CCA Games, Eager/Lazy Equivalence, and CPA Reduction for HHK17 `FO-notbot`

This module formalizes the Random Oracle Model (ROM) IND-CCA security experiments, eager/lazy
equivalence, keyless oracle simulator, and IND-CPA reduction hit-probability bounds for the
domain-separated implicit-rejection Fujisaki–Okamoto transform `FO-notbot` (`Scheme.keyGenNotBot`,
`Scheme.encapsNotBot`, `Scheme.decapsNotBot`) from
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto`
([HofheinzHoevelmannsKiltz2017], IACR ePrint 2017/604 full version dated 2 November 2021, §2.1,
§2.1 Def. 2.2 / Fig. 4, §3.1 Fig. 5, and §3.2.2 Fig. 12).

## Source map and model notes

Section and figure locators follow `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto` and refer to
the full version of [HofheinzHoevelmannsKiltz2017] served by IACR ePrint 2017/604, dated
**2 November 2021**:

* **§2.1** and **§2.1, Definition 2.2 / Figure 4**: `ExplicitCoinPKE` and its single-stage
  fixed-message distinguishing experiment `ExplicitCoinPKE.indCpaGame` /
  `ExplicitCoinPKE.indCpaAdvantage` (using caller-supplied messages `m₀, m₁ : M` and
  probability-difference `Game.advantage` rather than Def. 2.2 / Fig. 4's two-stage
  key-dependent-message guessing experiment).
* **§3.1, Figure 5**: derandomization and mandatory re-encryption check `T[PKE, G]` (`encT`,
  `decT`).
* **§3.2.2, Figure 12**: implicit-rejection KEM `FO-notbot = U-notbot ∘ T` (`ImplicitSK`,
  `Scheme.keyGenNotBot`, `Scheme.encapsNotBot`, `Scheme.decapsNotBot`), with the deliberate
  domain-separated random oracle `H : Bool × M × CT → K` (`false` for valid key derivations
  `H(false, m, c)` and `true` for implicit-rejection fallback queries `H(true, fallback, c)`) and
  arbitrary `Scheme` samplers `sampleCoins`, `sampleMsg`, `sampleKey`.

In addition to the `ExplicitCoinPKE` and `Scheme` modeling choices documented in
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto`, this module makes two ROM-specific modeling
choices:

* **Deterministic oracle adversaries (`ROAdversary`)**: adversaries are deterministic oracle
  programs `KEM.Challenge PK CT K → OracleComp (ROResp R K) Bool` with no private-coin channel;
  randomized oracle adversaries reduce to these by fixing coins (see `ProbOracleComp.coinLaw` /
  `fixCoins`).
* **Standard KEM IND-CCA experiment (`Scheme.roIndCcaGame`, `Scheme.eagerIndCcaGame`, not
  separately located in the source map above)**: the real-or-random key experiment draws the
  random challenge key via `kRand ← S.sampleKey` (rather than a uniform draw on `K`), leaves
  decapsulation queries unbounded and uncounted in `ROQueryBounds`, and requires
  `[Fintype M] [Finite R] [Fintype CT] [Finite K]` on `eagerIndCcaGame` to sample the eager
  random-oracle tables `Scheme.coinTable` and `Scheme.keyTable`.

On top of those definitions, this module formalizes:

1. **Executable lazy and eager ROM IND-CCA games for `FO-notbot`** (`Scheme.roIndCcaGame`,
   `Scheme.indCcaRomAdvantage`, `Scheme.eagerIndCcaGame`) over the oracle interface
   `ROQuery M CT` (`G`, `H`, and punctured decapsulation rejecting `c = cStar` with `none`),
   together with exact eager/lazy equivalence (`Scheme.eval_roIndCcaGame_eq_eagerIndCcaGame`,
   `Scheme.indCcaRomAdvantage_eq_eager`). Both games are instances of one ROM IND-CCA experiment
   `Scheme.romIndCcaExperiment`, parameterized by the key generator and the decapsulation oracle
   (written as a program against the random oracles), whose eager/lazy equivalence
   `Scheme.eval_romIndCcaExperiment_eq_eager` follows from the generic represented-cache law
   `RandomOracle.eval_run_interpret_eq_complete_bind`. The `@[simp]` bridges
   `Scheme.romIndCcaExperiment_notBot` and `Scheme.eagerRomIndCcaExperiment_notBot` identify the
   `FO-notbot` instance with `roIndCcaGame` and `eagerIndCcaGame`; the `FO^⊥` instance is in
   `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot`.
2. **Keyless ROM simulator and IND-CPA reduction** (`Scheme.simHandler`,
   `Scheme.romCpaReduction`, `Scheme.simHitProb`). Neither is a verbatim construction from
   [HofheinzHoevelmannsKiltz2017]; both are adapted to domain-separated `FO-notbot`. `simHandler` is
   adapted from the `G`/`H` simulations in two proofs of the full version: the proof of the §3.1
   theorem for `T` (IND-CPA security of the PKE implies OW-PCVA security of `T[PKE, G]`), which
   answers `G` lazily, and the proof of the §3.2.2 IND-CCA theorem for `U-notbot`, which answers
   decapsulation queries and the matching `H` queries from a ciphertext-indexed table. Here
   `simHandler` answers `H(false, m, c)` via a lazy table `H_q(c)` whenever the §3.1 Fig. 5
   re-encryption check `Enc(pk, m; G(m)) = c` holds, and answers punctured decapsulation queries
   `c ≠ cStar` from `H_q(c)` without using `sk` (its consistency with `roHandler` /
   `eagerIndCcaGame` is proved in the `NotBot` modules). `romCpaReduction` is modelled on the
   IND-CPA adversary in the proof of the §3.1 theorem for `T`, with two differences: the challenge
   messages `m₀, m₁ : M` are explicit parameters rather than sampled uniformly inside the reduction,
   and the wrapped adversary is an `FO-notbot` IND-CCA adversary rather than an OW-PCVA adversary
   against `T[PKE, G]`. It runs `A` against `simHandler` on an `ExplicitCoinPKE.indCpaGame`
   challenge `(pk, cStar)` and outputs whether `m₁` was recorded in `gCache`. We prove that the
   reduction's IND-CPA advantage unfolds to the difference of simulator hit probabilities
   (`Scheme.indCpaAdvantage_romCpaReduction`), the query-budget row bound
   `Scheme.sum_simHitProb_le`, and the OW-to-CPA averaging bound
   `Scheme.avg_simHitProb_le_indCpaAdvantage_romCpaReduction`. The IND-CCA bound for `FO-notbot`
   relating `indCcaRomAdvantage` to these terms is `Scheme.indCcaRomAdvantage_le` in
   `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot`.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.ROQuery`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.ROResp`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.ROAdversary`: query/response family and deterministic
  oracle adversary for the ROM IND-CCA experiment with random oracles `G`, `H` and decapsulation
  oracle.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.ROQuery.dispatch`: the oracle interface in any monad.
  Every lazy, eager and simulated handler of the FO games and proof hybrids is this dispatcher
  applied to its own `G`, `H` and decapsulation implementations.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.ROQueryBounds`: query-count bounds `(qG, qH)` on
  `G` and `H` expressed via `Cslib.OracleComp.IsCostBounded`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.ROCache`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.roHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.roIndCcaGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaRomAdvantage`:
  lazy-cached executable ROM IND-CCA game and advantage for `FO-notbot`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerIndCcaGame`: eager random-oracle
  IND-CCA game defined directly from `Scheme.keyGenNotBot`, `Scheme.encapsNotBot`, and
  `Scheme.decapsNotBot`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.ROSpec`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.romProgram`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.romIndCcaExperiment`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerRomIndCcaExperiment`: the random-oracle
  signature `G ⊕ₒ H`, the IND-CCA oracle interface as a program against it, and the lazy and
  eager ROM IND-CCA experiments for any key generator and decapsulation program.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.notBotDecaps`: the `FO-notbot` decapsulation
  program, the instance of `romIndCcaExperiment` that gives `roIndCcaGame`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.SimState`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.romCpaReduction`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simHitProb`: keyless ROM simulator,
  IND-CPA reduction, and simulator `G`-query hit probability.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eval_romIndCcaExperiment_eq_eager`: the lazy
  ROM IND-CCA experiment has the same output distribution as its eager form, for every key
  generator and decapsulation program.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.romIndCcaExperiment_notBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerRomIndCcaExperiment_notBot`: the
  `FO-notbot` instance of the experiment is `roIndCcaGame`, and its eager form is
  `eagerIndCcaGame`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eval_roIndCcaGame_eq_eagerIndCcaGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaRomAdvantage_eq_eager`:
  the lazy executable game `roIndCcaGame` has the same output distribution and advantage as
  `eagerIndCcaGame`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCpaAdvantage_romCpaReduction`:
  the IND-CPA advantage of `romCpaReduction` unfolds to the absolute difference of simulator
  `G`-query hit probabilities `simHitProb`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.sum_simHitProb_le`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.avg_simHitProb_le_indCpaAdvantage_romCpaReduction`:
  query-count row bound `∑_{m₁} simHitProb m₀ m₁ ≤ qG + qH` and OW-to-CPA averaging bound
  relating `|M|⁻¹ ∑_m simHitProb m m` to `indCpaAdvantage m₀ m₁ (romCpaReduction A m₀ m₁)`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

/-! ### Section 1: ROM Queries, Executable IND-CCA Game, Simulator, and CPA Reduction -/

/-- Oracle query sum type for the ROM IND-CCA game of `FO-notbot`: random oracle `G : M → R`,
random oracle `H : Bool × M × CT → K` (domain-separated by a Boolean tag `false` for
key derivation `H(false, m, c)` and `true` for implicit-rejection fallback `H(true, s, c)`),
and the decapsulation oracle `Decaps : CT → Option K`. -/
inductive ROQuery (M CT : Type) where
  /-- Query the coin-derivation random oracle `G : M → R`. -/
  | G (m : M)
  /-- Query the key-derivation random oracle `H : Bool × M × CT → K`. -/
  | H (x : Bool × M × CT)
  /-- Query the decapsulation oracle `Decaps : CT → Option K`. -/
  | decaps (c : CT)

/-- Response type family for `ROQuery M CT`. -/
abbrev ROResp (R K : Type) : ROQuery M CT → Type
  | .G _ => R
  | .H _ => K
  | .decaps _ => Option K

/-- The oracle interface of the FO IND-CCA games, in any monad: `G` and `H` queries go to the
given random-oracle implementations, decapsulation of the challenge `cStar` is refused with
`none`, and any other ciphertext is answered by `decaps`. Every lazy, eager and simulated handler
of the games and proof hybrids is this dispatcher applied to its own `G`, `H` and `decaps`. -/
@[simp] def ROQuery.dispatch [DecidableEq CT] {m : Type → Type} [Monad m] (G : M → m R)
    (H : Bool × M × CT → m K) (decaps : CT → m (Option K)) (cStar : CT) :
    (q : ROQuery M CT) → m (ROResp R K q)
  | .G msg => G msg
  | .H x => H x
  | .decaps c => if c = cStar then pure none else decaps c

/-- A deterministic IND-CCA oracle adversary in the Random Oracle Model receives the challenge
`⟨pk, c*, k*⟩` and interacts with `G`, `H`, and the decapsulation oracle before outputting a
Boolean guess. Randomized oracle adversaries reduce to these by fixing coins (see
`ProbOracleComp.coinLaw`). -/
abbrev ROAdversary (PK M R CT K : Type) : Type :=
  KEM.Challenge PK CT K → OracleComp (ROResp (M := M) (CT := CT) R K) Bool

/-- Query cost counting calls to `G`. -/
@[simp] def ROQuery.gCost : ROQuery M CT → ℕ
  | .G _ => 1
  | .H _ => 0
  | .decaps _ => 0

/-- Query cost counting calls to `H`. -/
@[simp] def ROQuery.hCost : ROQuery M CT → ℕ
  | .G _ => 0
  | .H _ => 1
  | .decaps _ => 0

/-- Query cost counting combined calls to `G` and `H`. -/
@[simp] def ROQuery.ghCost : ROQuery M CT → ℕ
  | .G _ => 1
  | .H _ => 1
  | .decaps _ => 0

/-- Query cost counting calls to the decapsulation oracle. -/
@[simp] def ROQuery.dCost : ROQuery M CT → ℕ
  | .G _ => 0
  | .H _ => 0
  | .decaps _ => 1

/-- An `ROAdversary` satisfies query bounds `(qG, qH)` if on every challenge `ch` its execution
makes at most `qG` queries to `G` and at most `qH` queries to `H`. -/
def ROQueryBounds (A : ROAdversary PK M R CT K) (qG qH : ℕ) : Prop :=
  ∀ ch : KEM.Challenge PK CT K,
    OracleComp.IsCostBounded ROQuery.gCost (A ch) qG ∧
    OracleComp.IsCostBounded ROQuery.hCost (A ch) qH

/-- Bounds `(qG, qH)` on `G` and `H` queries bound their combined count by `qG + qH`. -/
theorem ROQueryBounds.ghCost {A : ROAdversary PK M R CT K} {qG qH : ℕ} (hq : ROQueryBounds A qG qH)
    (ch : KEM.Challenge PK CT K) : OracleComp.IsCostBounded ROQuery.ghCost (A ch) (qG + qH) := by
  convert OracleComp.IsCostBounded.add (hq ch).1 (hq ch).2 using 1
  funext q; cases q <;> rfl

/-- An `ROAdversary` satisfies full query bounds `(qG, qH, qD)` if on every challenge `ch` its
execution makes at most `qG` queries to `G`, `qH` queries to `H`, and `qD` queries to `decaps`. -/
def ROFullQueryBounds (A : ROAdversary PK M R CT K) (qG qH qD : ℕ) : Prop :=
  ROQueryBounds A qG qH ∧
  ∀ ch : KEM.Challenge PK CT K, OracleComp.IsCostBounded ROQuery.dCost (A ch) qD

/-- Association-list caches for the lazy random oracles `G : M → R` and
`H : Bool × M × CT → K` in the executable ROM IND-CCA game. -/
structure ROCache (M R CT K : Type) where
  /-- Cached query-response pairs for `G : M → R`. -/
  gCache : List (M × R) := []
  /-- Cached query-response pairs for `H : Bool × M × CT → K`. -/
  hCache : List ((Bool × M × CT) × K) := []

/-- Association-list caches for the keyless ROM simulator `Scheme.simHandler`, extending
`ROCache` (`gCache` for
`G : M → R` and `hCache` for unprogrammed queries to `H : Bool × M × CT → K`) with `hqCache` for
the ciphertext-indexed key table `H_q : CT → K`. -/
structure SimState (M R CT K : Type) extends ROCache M R CT K where
  /-- Cached query-response pairs for the ciphertext-key table `H_q : CT → K`. -/
  hqCache : List (CT × K) := []

section LazyOracles

variable [DecidableEq M] [DecidableEq CT]

/-- Lazy evaluation of `G : M → R` inside `ROCache` via `memoize`. -/
def roHashG (sampleCoins : ProbComp R) (m : M) : StateT (ROCache M R CT K) ProbComp R :=
  RandomOracle.zoomStateT ROCache.gCache (fun st c => { st with gCache := c })
    (memoize (fun _ => sampleCoins) m)

/-- Lazy evaluation of `H : Bool × M × CT → K` inside `ROCache` via `memoize`. -/
def roHashH (sampleKey : ProbComp K) (x : Bool × M × CT) :
      StateT (ROCache M R CT K) ProbComp K :=
  RandomOracle.zoomStateT ROCache.hCache (fun st c => { st with hCache := c })
    (memoize (fun _ => sampleKey) x)

/-- Lazy evaluation of `G : M → R` on the inherited `gCache` of `SimState` via `memoize`. -/
def simHashG (sampleCoins : ProbComp R) (m : M) : StateT (SimState M R CT K) ProbComp R :=
  RandomOracle.zoomStateT (fun st => st.gCache) (fun st c => { st with gCache := c })
    (memoize (fun _ => sampleCoins) m)

/-- Lazy evaluation of unprogrammed `H : Bool × M × CT → K` queries on the inherited `hCache` of
`SimState` via `memoize`. -/
def simHashHRaw (sampleKey : ProbComp K) (x : Bool × M × CT) :
    StateT (SimState M R CT K) ProbComp K :=
  RandomOracle.zoomStateT (fun st => st.hCache) (fun st c => { st with hCache := c })
    (memoize (fun _ => sampleKey) x)

/-- Lazy evaluation of the ciphertext-key table `H_q : CT → K` inside `SimState` via
`memoize`. -/
def simHashHq (sampleKey : ProbComp K) (c : CT) : StateT (SimState M R CT K) ProbComp K :=
  RandomOracle.zoomStateT SimState.hqCache (fun st c' => { st with hqCache := c' })
    (memoize (fun _ => sampleKey) c)

/-- Filtered decapsulation branch of the lazy `SimState` handlers: answer `some (Hq c)` when the
filter `d` accepts `c` on the current `G` cache, and `none` otherwise. -/
def filterDecaps (Hq : CT → StateT (SimState M R CT K) ProbComp K)
    (d : List (M × R) → CT → Bool) (c : CT) : StateT (SimState M R CT K) ProbComp (Option K) :=
  fun st =>
    cond (d st.gCache c)
      ((do
        let k ← Hq c
        return some k) st)
      ((return none : StateT (SimState M R CT K) ProbComp (Option K)) st)

end LazyOracles

/-- The random oracles `G : M → R` and `H : Bool × M × CT → K` as one interface. -/
abbrev ROSpec (M R CT K : Type) := (fun _ : M => R) ⊕ₒ (fun _ : Bool × M × CT => K)

/-- Each query of a ROM IND-CCA game as a program over the random oracles: `G` and `H` are
forwarded, decapsulation of `cStar` is refused, and any other ciphertext runs `decaps`. -/
def romProgram [DecidableEq CT] (decaps : CT → OracleComp (ROSpec M R CT K) (Option K))
    (cStar : CT) :
    (q : ROQuery M CT) → OracleComp (ROSpec M R CT K) (ROResp R K q) :=
  ROQuery.dispatch (fun m => OracleComp.query (spec := ROSpec M R CT K) (Sum.inl m))
    (fun x => OracleComp.query (spec := ROSpec M R CT K) (Sum.inr x)) decaps cStar

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- Stateful oracle handler for the real ROM IND-CCA game of `FO-notbot`. Queries to the
challenge ciphertext `cStar` are rejected with `none`; other decapsulation queries run the scheme's
decapsulation `decapsNotBotM` against the lazy random oracles `G` and `H`. -/
def roHandler (S : Scheme PK SK M R CT K) (dk : ImplicitSK PK SK M) (cStar : CT)
    (q : ROQuery M CT) : StateT (ROCache M R CT K) ProbComp (ROResp R K q) :=
  ROQuery.dispatch (roHashG S.pke.sampleCoins) (roHashH S.sampleKey)
    (fun c => some <$> S.decapsNotBotM (roHashG S.pke.sampleCoins) (roHashH S.sampleKey) dk c)
    cStar q

/-- The executable ROM IND-CCA security game for `FO-notbot` with bit `b : Bool` (standard KEM
IND-CCA experiment, not separately located in the source map above). When `b = false`, the
adversary receives the real encapsulated key `kReal = H(false, m*, c*)`; when `b = true`, it
receives an independent key `kRand ← S.sampleKey`. Decapsulation queries are punctured at `cStar`
and otherwise unbounded. -/
def roIndCcaGame (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (b : Bool) : ProbComp Bool := do
  let (pk, dk) ← S.keyGenNotBot
  let mStar ← S.sampleMsg
  let rStar ← S.pke.sampleCoins
  let cStar := S.pke.encDet pk mStar rStar
  let kReal ← S.sampleKey
  let kRand ← S.sampleKey
  let kStar := if b then kRand else kReal
  let st₀ : ROCache M R CT K :=
    { gCache := [(mStar, rStar)], hCache := [((false, mStar, cStar), kReal)] }
  let (guess, _) ←
    (OracleComp.interpret (S.roHandler dk cStar) (A ⟨pk, cStar, kStar⟩)).run st₀
  return guess

/-- The ROM IND-CCA advantage of an adversary `A` against `FO-notbot`. -/
noncomputable def indCcaRomAdvantage (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) : ℝ≥0 :=
  Game.advantage
    (ProbComp.eval (S.roIndCcaGame A false))
    (ProbComp.eval (S.roIndCcaGame A true))

omit [DecidableEq M] [DecidableEq CT] in
/-- The eager random oracle `G : M → R`: an independent coin `S.pke.sampleCoins` at every
message. -/
noncomputable def coinTable [Fintype M] [Finite R] (S : Scheme PK SK M R CT K) : PMF (M → R) :=
  pi fun _ => ProbComp.eval S.pke.sampleCoins

omit [DecidableEq M] [DecidableEq CT] in
/-- An eager random oracle `X → K` into the key space: an independent key `S.sampleKey` at every
point. The FO games draw `H ← S.keyTable (Bool × M × CT)` and their ciphertext-indexed key tables
`S.keyTable CT` from it. -/
noncomputable def keyTable [Finite K] (S : Scheme PK SK M R CT K) (X : Type) [Fintype X] :
    PMF (X → K) :=
  pi fun _ => ProbComp.eval S.sampleKey

/-- Stateless handler for `S.eagerIndCcaGame`: `G` and `H` are complete functions and
decapsulation queries for `c ≠ cStar` evaluate `S.decapsNotBot G H dk c`. -/
noncomputable def eagerHandler (S : Scheme PK SK M R CT K) (G : M → R) (H : Bool × M × CT → K)
    (dk : ImplicitSK PK SK M) (cStar : CT) (q : ROQuery M CT) : PMF (ROResp R K q) :=
  ROQuery.dispatch (PMF.pure ∘ G) (PMF.pure ∘ H)
    (fun c => PMF.pure (some (S.decapsNotBot G H dk c))) cStar q

/-- The eager random-oracle IND-CCA game for `FO-notbot` (standard KEM IND-CCA experiment, not
separately located in the source map above), defined directly from `S.keyGenNotBot`,
`S.encapsNotBot`, and `S.decapsNotBot` over eager random oracles `G ← S.coinTable` and
`H ← S.keyTable (Bool × M × CT)` and `kRand ← S.sampleKey`. -/
noncomputable def eagerIndCcaGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, dk) ← ProbComp.eval S.keyGenNotBot
  let G ← S.coinTable
  let H ← S.keyTable (Bool × M × CT)
  let (cStar, kReal) ← ProbComp.eval (S.encapsNotBot G H pk)
  let kRand ← ProbComp.eval S.sampleKey
  let kStar := if b then kRand else kReal
  OracleComp.interpret (S.eagerHandler G H dk cStar) (A ⟨pk, cStar, kStar⟩)

/-- Simulated `H` oracle of `simHandler`: on key-derivation queries `(false, m, c)`, checks whether
`S.pke.encDet pk m (G(m)) = c` and if so returns `H_q(c)`. This is designed so that decapsulation
queries can be answered from `H_q(c)` without the secret key `sk`; its consistency with the real
game is proved in the `NotBot` modules. The `H_q` table is adapted from the proof of the §3.2.2
IND-CCA theorem for `U-notbot` in [HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version
dated 2 November 2021), with that proof's plaintext check replaced by the re-encryption check of `T`
and with `H` domain-separated. -/
def simHashH (S : Scheme PK SK M R CT K) (pk : PK)
    (x : Bool × M × CT) : StateT (SimState M R CT K) ProbComp K :=
  match x with
  | (false, m, c) => do
    let r ← simHashG S.pke.sampleCoins m
    if S.pke.encDet pk m r = c then
      simHashHq S.sampleKey c
    else
      simHashHRaw S.sampleKey (false, m, c)
  | (true, m, c) =>
    simHashHRaw S.sampleKey (true, m, c)

/-- Common `ROQuery` dispatcher for lazy `SimState` handlers parameterized by an `H` handler `hH`
and a decapsulation filter `d : List (M × R) → CT → Bool`. -/
def simFilterDispatch (S : Scheme PK SK M R CT K)
    (hH : Bool × M × CT → StateT (SimState M R CT K) ProbComp K)
    (d : List (M × R) → CT → Bool) (cStar : CT) (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  ROQuery.dispatch (simHashG S.pke.sampleCoins) hH (filterDecaps (simHashHq S.sampleKey) d) cStar q

/-- Keyless ROM simulator parameterized by a decapsulation acceptance filter
`d : List (M × R) → CT → Bool` on the cached `G`-queries `gCache`. On `c ≠ cStar`, decapsulation
returns `some (H_q(c))` when `d st.gCache c = true` and `none` otherwise. Taking
`d = fun _ _ => true` recovers `simHandler` for `FO-notbot`, while filtering by whether `c` is a
cached re-encryption gives the simulator for `FO^⊥`. -/
def simFilterHandler (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (pk : PK) (cStar : CT) (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  S.simFilterDispatch (S.simHashH pk) d cStar q

/-- Stateful oracle handler for a keyless ROM simulator of the domain-separated `FO-notbot` IND-CCA
game, designed to answer decapsulation queries for `c ≠ cStar` directly from `H_q(c)` without using
`sk` (consistency with the real game is proved in the `NotBot` modules). It is not a verbatim
construction from [HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
2 November 2021): it is adapted from the lazy `G` simulation in the proof of the §3.1 theorem for
`T` (IND-CPA implies OW-PCVA) and the `H`/decapsulation simulation in the proof of the §3.2.2
IND-CCA theorem for `U-notbot`, combined for `FO-notbot` with domain-separated `H`. -/
def simHandler (S : Scheme PK SK M R CT K) (pk : PK) (cStar : CT) (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  S.simFilterHandler (fun _ _ => true) pk cStar q

/-- IND-CPA adversary built from a ROM IND-CCA adversary `A` and decapsulation filter `d`:
given an IND-CPA challenge `pk` and `cStar`, samples a challenge key `kStar ← S.sampleKey`, runs
`A ⟨pk, cStar, kStar⟩` against `S.simFilterHandler (d pk) pk cStar`, and outputs whether `m1` was
queried to `G`. -/
def romFilterCpaReduction (S : Scheme PK SK M R CT K) (d : PK → List (M × R) → CT → Bool)
    (A : ROAdversary PK M R CT K) (_m0 m1 : M) : PK → CT → ProbComp Bool :=
  fun pk cStar => do
    let kStar ← S.sampleKey
    let (_, st) ←
      (OracleComp.interpret (S.simFilterHandler (d pk) pk cStar) (A ⟨pk, cStar, kStar⟩)).run {}
    return (st.gCache.lookup m1).isSome

/-- IND-CPA adversary built from a ROM IND-CCA adversary `A` against domain-separated `FO-notbot`:
given an IND-CPA challenge `pk` and `cStar`, samples a challenge key `kStar ← S.sampleKey`, runs
`A ⟨pk, cStar, kStar⟩` against `S.simHandler pk cStar`, and outputs whether `m1` was
queried to `G`.

It is modelled on the IND-CPA adversary in the proof of the §3.1 theorem for `T` in
[HofheinzHoevelmannsKiltz2017] (IND-CPA security of the PKE implies OW-PCVA security of
`T[PKE, G]`; IACR ePrint 2017/604, full version dated 2 November 2021), with two adaptations:
the challenge messages `m0, m1 : M` are explicit parameters rather than sampled uniformly inside
the reduction (the average over `M` is taken separately, in
`avg_simHitProb_le_indCpaAdvantage_romCpaReduction`), and the wrapped adversary is an `FO-notbot`
IND-CCA adversary rather than an OW-PCVA adversary against `T[PKE, G]`. The first message `_m0`
is unused in the body; it is kept as an explicit parameter so that
`S.pke.indCpaAdvantage m₀ m₁ (S.romCpaReduction A m₀ m₁)` names both challenge messages. -/
def romCpaReduction (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (m0 m1 : M) : PK → CT → ProbComp Bool :=
  S.romFilterCpaReduction (fun _ _ _ => true) A m0 m1

/-! ### Section 2: One ROM IND-CCA Experiment and Eager/Lazy Equivalence

The ROM IND-CCA games of `FO-notbot` and `FO^⊥` differ only in their key generation and in the
decapsulation they run against the random oracles `G` and `H`. `romIndCcaExperiment` takes both as
parameters, with decapsulation a program over the joined interface `ROSpec` of `G` and `H`.
`roIndCcaGame` and `eagerIndCcaGame` are its `FO-notbot` instances
(`romIndCcaExperiment_notBot`, `eagerRomIndCcaExperiment_notBot`), and
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot` gives the `FO^⊥` instances. Every query
of the experiment is the oracle program `romProgram`, so
`RandomOracle.eval_run_interpret_eq_complete_bind` replaces both caches by complete tables in one
step, and `RandomOracle.bind_complete_sum` splits the completed table into `G` and `H`
(`eval_romIndCcaExperiment_eq_eager`). -/

/-- The lazy handler of a ROM IND-CCA game: `romProgram` against the lazy oracles `roHashG` and
`roHashH`. -/
abbrev romHandler (S : Scheme PK SK M R CT K)
    (decaps : CT → OracleComp (ROSpec M R CT K) (Option K)) (cStar : CT) (q : ROQuery M CT) :
    StateT (ROCache M R CT K) ProbComp (ROResp R K q) :=
  OracleComp.interpret (OracleComp.sumHandler (roHashG S.pke.sampleCoins) (roHashH S.sampleKey))
    (romProgram decaps cStar q)

omit [DecidableEq M] in
/-- The eager handler of a ROM IND-CCA game: `romProgram` against complete tables `G` and `H`. -/
noncomputable abbrev romEagerHandler (G : M → R) (H : Bool × M × CT → K)
    (decaps : CT → OracleComp (ROSpec M R CT K) (Option K)) (cStar : CT) (q : ROQuery M CT) :
    PMF (ROResp R K q) :=
  OracleComp.interpret (OracleComp.sumHandler (fun m => PMF.pure (G m)) (fun x => PMF.pure (H x)))
    (romProgram decaps cStar q)

/-- **The ROM IND-CCA experiment** of an FO-style KEM with key generation `keyGen` and
decapsulation `decaps pk dk`, a program over the random oracles, for challenge bit `b`. The
challenge encrypts `m* ← sampleMsg` under coins `r* ← sampleCoins`, which are programmed as
`G(m*)`; the real key `kReal ← sampleKey` is programmed as `H(false, m*, c*)`. The adversary
receives `kReal` when `b = false` and an independent `kRand ← sampleKey` when `b = true`, and
interacts with the lazy oracles through `romHandler`. -/
def romIndCcaExperiment {DK : Type} (S : Scheme PK SK M R CT K) (keyGen : ProbComp (PK × DK))
    (decaps : PK → DK → CT → OracleComp (ROSpec M R CT K) (Option K))
    (A : ROAdversary PK M R CT K) (b : Bool) : ProbComp Bool := do
  let (pk, dk) ← keyGen
  let mStar ← S.sampleMsg
  let rStar ← S.pke.sampleCoins
  let cStar := S.pke.encDet pk mStar rStar
  let kReal ← S.sampleKey
  let kRand ← S.sampleKey
  let kStar := if b then kRand else kReal
  let st₀ : ROCache M R CT K :=
    { gCache := [(mStar, rStar)], hCache := [((false, mStar, cStar), kReal)] }
  let (guess, _) ←
    (OracleComp.interpret (S.romHandler (decaps pk dk) cStar) (A ⟨pk, cStar, kStar⟩)).run st₀
  return guess

/-- The eager ROM IND-CCA experiment: `romIndCcaExperiment` with eager random oracles
`G ← S.coinTable` and `H ← S.keyTable (Bool × M × CT)` and the challenge `S.encapsBot G H pk`. -/
noncomputable def eagerRomIndCcaExperiment [Fintype M] [Finite R] [Fintype CT] [Finite K]
    {DK : Type} (S : Scheme PK SK M R CT K) (keyGen : ProbComp (PK × DK))
    (decaps : PK → DK → CT → OracleComp (ROSpec M R CT K) (Option K))
    (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, dk) ← ProbComp.eval keyGen
  let G ← S.coinTable
  let H ← S.keyTable (Bool × M × CT)
  let (cStar, kReal) ← ProbComp.eval (S.encapsBot G H pk)
  let kRand ← ProbComp.eval S.sampleKey
  let kStar := if b then kRand else kReal
  OracleComp.interpret (romEagerHandler G H (decaps pk dk) cStar) (A ⟨pk, cStar, kStar⟩)

omit [DecidableEq M] in
/-- A dispatcher whose random oracles are the calls of `oracle` and whose decapsulation interprets
`decaps` against `oracle` is `oracle` interpreting `romProgram`. -/
theorem dispatch_eq_interpret_romProgram {n : Type → Type} [Monad n] [LawfulMonad n]
    (oracle : (q : M ⊕ (Bool × M × CT)) → n (ROSpec M R CT K q))
    (decaps : CT → OracleComp (ROSpec M R CT K) (Option K)) (cStar : CT) (q : ROQuery M CT) :
    ROQuery.dispatch (fun m => oracle (.inl m)) (fun x => oracle (.inr x))
        (fun c => OracleComp.interpret oracle (decaps c)) cStar q =
      OracleComp.interpret oracle (romProgram decaps cStar q) := by
  cases q with
  | G m => exact (OracleComp.interpret_query _ _).symm
  | H x => exact (OracleComp.interpret_query _ _).symm
  | decaps c => by_cases hc : c = cStar <;> simp [romProgram, hc]

omit [DecidableEq M] in
/-- Interpreting `decapsNotBotM` against oracle calls runs it against the interpreted calls. -/
theorem interpret_decapsNotBotM {ι : Type} {spec : OracleSpec ι} {n : Type → Type}
    [Monad n] [LawfulMonad n] (oracle : (q : ι) → n (spec q)) (S : Scheme PK SK M R CT K)
    (G : M → OracleComp spec R) (H : Bool × M × CT → OracleComp spec K)
    (dk : ImplicitSK PK SK M) (c : CT) :
    OracleComp.interpret oracle (S.decapsNotBotM G H dk c) =
      S.decapsNotBotM (fun m => OracleComp.interpret oracle (G m))
        (fun x => OracleComp.interpret oracle (H x)) dk c := by
  rw [decapsNotBotM_eq, decapsNotBotM_eq]
  cases S.pke.dec dk.sk c with
  | none => rfl
  | some m' =>
    simp only [OracleComp.interpret_bind]
    congr 1 with r'
    split_ifs <;> rfl

omit [DecidableEq M] in
/-- Interpreting `decapsBotM` against oracle calls runs it against the interpreted calls. -/
theorem interpret_decapsBotM {ι : Type} {spec : OracleSpec ι} {n : Type → Type}
    [Monad n] [LawfulMonad n] (oracle : (q : ι) → n (spec q)) (S : Scheme PK SK M R CT K)
    (G : M → OracleComp spec R) (H : Bool × M × CT → OracleComp spec K) (pk : PK) (sk : SK)
    (c : CT) :
    OracleComp.interpret oracle (S.decapsBotM G H pk sk c) =
      S.decapsBotM (fun m => OracleComp.interpret oracle (G m))
        (fun x => OracleComp.interpret oracle (H x)) pk sk c := by
  rw [decapsBotM_eq, decapsBotM_eq]
  cases S.pke.dec sk c with
  | none => simp
  | some m' =>
    simp only [OracleComp.interpret_bind]
    congr 1 with r'
    split_ifs <;> simp

/-- The joined cache represented by the two list caches of an `ROCache`. -/
private abbrev roTables (st : ROCache M R CT K) : RandomOracle.Cache (ROSpec M R CT K) :=
  RandomOracle.Cache.sum (RandomOracle.ofList st.gCache) (RandomOracle.ofList st.hCache)

/-- Each lazy oracle call, read on the joined cache, is a lazy call of the joined oracle. -/
private theorem eval_roHash_map_roTables (S : Scheme PK SK M R CT K)
    (q : M ⊕ (Bool × M × CT)) (st : ROCache M R CT K) :
    (ProbComp.eval (OracleComp.sumHandler (roHashG S.pke.sampleCoins) (roHashH S.sampleKey) q
        st)).map (fun z => (z.1, roTables z.2)) =
      RandomOracle.answer (OracleComp.sumHandler (fun _ => ProbComp.eval S.pke.sampleCoins)
        (fun _ => ProbComp.eval S.sampleKey)) q (roTables st) := by
  rcases q with m | x
  · rw [roTables, RandomOracle.answer_sum_inl]
    exact RandomOracle.eval_zoom_memoize_map ROCache.gCache (fun st c => { st with gCache := c })
      S.pke.sampleCoins m st (fun r => r) roTables
      (fun c => RandomOracle.Cache.sum c (RandomOracle.ofList st.hCache)) (fun _ => rfl)
  · rw [roTables, RandomOracle.answer_sum_inr]
    exact RandomOracle.eval_zoom_memoize_map ROCache.hCache (fun st c => { st with hCache := c })
      S.sampleKey x st (fun k => k) roTables
      (fun c => RandomOracle.Cache.sum (RandomOracle.ofList st.gCache) c) (fun _ => rfl)

/-- Running a program under `romHandler` has the law of completing both caches into tables `G` and
`H` and running it under `romEagerHandler`. -/
private theorem eval_run_romHandler_eq_eager [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (decaps : CT → OracleComp (ROSpec M R CT K) (Option K))
    (cStar : CT) {α : Type} (prog : OracleComp (ROResp (M := M) (CT := CT) R K) α)
    (st : ROCache M R CT K) :
    (ProbComp.eval ((OracleComp.interpret (S.romHandler decaps cStar) prog).run st)).map
        Prod.fst =
      (RandomOracle.complete (fun _ => ProbComp.eval S.pke.sampleCoins)
          (RandomOracle.ofList st.gCache)).bind fun G =>
        (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey)
            (RandomOracle.ofList st.hCache)).bind fun H =>
          OracleComp.interpret (romEagerHandler G H decaps cStar) prog := by
  simp only [← OracleComp.interpret_interpret]
  rw [RandomOracle.eval_run_interpret_eq_complete_bind
      (OracleComp.sumHandler (fun _ => ProbComp.eval S.pke.sampleCoins)
        (fun _ => ProbComp.eval S.sampleKey))
      (OracleComp.sumHandler (roHashG S.pke.sampleCoins) (roHashH S.sampleKey)) roTables
      S.eval_roHash_map_roTables,
    ← RandomOracle.bind_complete_sum]
  congr 1 with T : 1
  congr 1 with q : 1
  rcases q with m | x <;> rfl

/-- **Eager/lazy equivalence for the ROM IND-CCA experiment**: for every key generation and
decapsulation program, the lazy experiment has the output distribution of the eager one. -/
theorem eval_romIndCcaExperiment_eq_eager [Fintype M] [Finite R] [Fintype CT] [Finite K]
    {DK : Type} (S : Scheme PK SK M R CT K) (keyGen : ProbComp (PK × DK))
    (decaps : PK → DK → CT → OracleComp (ROSpec M R CT K) (Option K))
    (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp.eval (S.romIndCcaExperiment keyGen decaps A b) =
      S.eagerRomIndCcaExperiment keyGen decaps A b := by
  let dG : M → PMF R := fun _ => ProbComp.eval S.pke.sampleCoins
  let dH : Bool × M × CT → PMF K := fun _ => ProbComp.eval S.sampleKey
  dsimp only [romIndCcaExperiment]
  simp only [eagerRomIndCcaExperiment, coinTable, keyTable, encapsBot, encT,
    Probability.PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind]
  congr 1; funext ⟨pk, dk⟩
  have hstep (mStar : M) (rStar : R) (kReal kRand : K) :
      (ProbComp.eval ((OracleComp.interpret
        (S.romHandler (decaps pk dk) (S.pke.encDet pk mStar rStar))
        (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else kReal⟩)).run
        { gCache := [(mStar, rStar)],
          hCache := [((false, mStar, S.pke.encDet pk mStar rStar), kReal)] })).bind
          (fun x => PMF.pure x.fst) =
      (pi (Function.update dG mStar (PMF.pure rStar))).bind fun G =>
        (pi (Function.update dH (false, mStar, S.pke.encDet pk mStar rStar)
            (PMF.pure kReal))).bind fun H =>
          OracleComp.interpret
            (romEagerHandler G H (decaps pk dk) (S.pke.encDet pk mStar rStar))
            (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else kReal⟩) := by
    change (ProbComp.eval _).map Prod.fst = _
    rw [eval_run_romHandler_eq_eager, RandomOracle.complete_ofList_singleton,
      RandomOracle.complete_ofList_singleton]
  simp only [hstep]
  pmf_hoist (ProbComp.eval S.sampleMsg)
  congr 1 with mStar : 1
  rw [← bind_pi_update dG mStar fun rStar G =>
    (pi dH).bind fun H => (ProbComp.eval S.sampleKey).bind fun kRand =>
      OracleComp.interpret (romEagerHandler G H (decaps pk dk) (S.pke.encDet pk mStar rStar))
        (A ⟨pk, S.pke.encDet pk mStar rStar,
          if b then kRand else H (false, mStar, S.pke.encDet pk mStar rStar)⟩)]
  congr 1 with rStar : 1
  pmf_hoist (pi (Function.update dG mStar (PMF.pure rStar)))
  congr 1 with G : 1
  rw [← bind_pi_update dH (false, mStar, S.pke.encDet pk mStar rStar) fun kReal H =>
    (ProbComp.eval S.sampleKey).bind fun kRand =>
      OracleComp.interpret (romEagerHandler G H (decaps pk dk) (S.pke.encDet pk mStar rStar))
        (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else kReal⟩)]
  congr 1 with kReal : 1
  exact PMF.bind_comm _ _ _

/-! #### The `FO-notbot` instance -/

omit [DecidableEq M] in
/-- `FO-notbot` decapsulation `decapsNotBotM` as a program over the random oracles. -/
def notBotDecaps (S : Scheme PK SK M R CT K) (dk : ImplicitSK PK SK M) (c : CT) :
    OracleComp (ROSpec M R CT K) (Option K) :=
  some <$> S.decapsNotBotM (fun m => OracleComp.query (spec := ROSpec M R CT K) (Sum.inl m))
    (fun x => OracleComp.query (spec := ROSpec M R CT K) (Sum.inr x)) dk c

/-- `roHandler` is the lazy handler of `romProgram` with `FO-notbot` decapsulation. -/
theorem roHandler_eq_romHandler (S : Scheme PK SK M R CT K) (dk : ImplicitSK PK SK M)
    (cStar : CT) : S.roHandler dk cStar = S.romHandler (S.notBotDecaps dk) cStar := by
  funext q
  refine Eq.trans ?_ (dispatch_eq_interpret_romProgram _ _ cStar q)
  simp only [roHandler, notBotDecaps, OracleComp.interpret_map, interpret_decapsNotBotM,
    OracleComp.interpret_query]

omit [DecidableEq M] in
/-- `eagerHandler` is the eager handler of `romProgram` with `FO-notbot` decapsulation. -/
theorem eagerHandler_eq_romEagerHandler (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (cStar : CT) :
    S.eagerHandler G H dk cStar = romEagerHandler G H (S.notBotDecaps dk) cStar := by
  have hd (c : CT) : PMF.pure (some (S.decapsNotBot G H dk c)) = OracleComp.interpret
      (OracleComp.sumHandler (fun m => PMF.pure (G m)) (fun x => PMF.pure (H x)))
      (S.notBotDecaps dk c) := by
    simp only [notBotDecaps, OracleComp.interpret_map, interpret_decapsNotBotM,
      OracleComp.interpret_query]
    change _ = some <$> S.decapsNotBotM (m := PMF) (pure ∘ G) (pure ∘ H) dk c
    rw [decapsNotBotM_pure, map_pure]
    rfl
  funext q
  refine Eq.trans ?_ (dispatch_eq_interpret_romProgram _ _ cStar q)
  simp only [eagerHandler, hd]
  rfl

/-- `roIndCcaGame` is the ROM IND-CCA experiment of `FO-notbot`. -/
@[simp] theorem romIndCcaExperiment_notBot (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (b : Bool) :
    S.romIndCcaExperiment S.keyGenNotBot (fun _ dk => S.notBotDecaps dk) A b =
      S.roIndCcaGame A b := by
  simp only [romIndCcaExperiment, roIndCcaGame, roHandler_eq_romHandler]

omit [DecidableEq M] in
/-- `eagerIndCcaGame` is the eager ROM IND-CCA experiment of `FO-notbot`. -/
@[simp] theorem eagerRomIndCcaExperiment_notBot [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    S.eagerRomIndCcaExperiment S.keyGenNotBot (fun _ dk => S.notBotDecaps dk) A b =
      S.eagerIndCcaGame A b := by
  simp only [eagerRomIndCcaExperiment, eagerIndCcaGame, encapsNotBot,
    eagerHandler_eq_romEagerHandler]

/-- **Eager/lazy equivalence for the `FO-notbot` ROM IND-CCA game**: evaluating the executable
lazy-cached game `S.roIndCcaGame A b` yields the exact same output distribution as the eager
random-oracle game `S.eagerIndCcaGame A b`. -/
theorem eval_roIndCcaGame_eq_eagerIndCcaGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp.eval (S.roIndCcaGame A b) = S.eagerIndCcaGame A b := by
  rw [← romIndCcaExperiment_notBot, ← eagerRomIndCcaExperiment_notBot]
  exact S.eval_romIndCcaExperiment_eq_eager _ _ A b

/-- The ROM IND-CCA advantage of `A` against `FO-notbot` equals the distinguishing advantage
between `S.eagerIndCcaGame A false` and `S.eagerIndCcaGame A true`. -/
theorem indCcaRomAdvantage_eq_eager [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) :
    S.indCcaRomAdvantage A =
      Game.advantage (S.eagerIndCcaGame A false) (S.eagerIndCcaGame A true) := by
  simp [indCcaRomAdvantage, eval_roIndCcaGame_eq_eagerIndCcaGame]

/-! ### Section 3: Simulator Hit Probability and IND-CPA Averaging for `romCpaReduction` -/

omit [DecidableEq CT] in
/-- A supported transition of `simHashG` adds at most one entry to `gCache`. -/
theorem simHashG_gCache_length_le (sampleCoins : ProbComp R) (m : M)
    (st : SimState M R CT K) (z : R × SimState M R CT K)
    (hz : z ∈ (ProbComp.eval (simHashG sampleCoins m st)).support) :
    z.snd.gCache.length ≤ st.gCache.length + 1 := by
  rw [simHashG, RandomOracle.eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨r, c'⟩, hc', rfl⟩ := hz
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc' with ⟨-, hnext⟩ | ⟨-, -, hnext⟩ <;>
    · dsimp only at hnext; simp [hnext]

/-- A supported transition of `simHashHRaw` preserves `gCache`. -/
theorem simHashHRaw_gCache_eq (sampleKey : ProbComp K) (x : Bool × M × CT)
    (st : SimState M R CT K) (z : K × SimState M R CT K)
    (hz : z ∈ (ProbComp.eval (simHashHRaw sampleKey x st)).support) :
    z.snd.gCache = st.gCache := by
  rw [simHashHRaw, RandomOracle.eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨_, _⟩, -, rfl⟩ := hz
  rfl

omit [DecidableEq M] in
/-- A supported transition of `simHashHq` preserves `gCache`. -/
theorem simHashHq_gCache_eq (sampleKey : ProbComp K) (c : CT)
    (st : SimState M R CT K) (z : K × SimState M R CT K)
    (hz : z ∈ (ProbComp.eval (simHashHq sampleKey c st)).support) :
    z.snd.gCache = st.gCache := by
  rw [simHashHq, RandomOracle.eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨_, _⟩, -, rfl⟩ := hz
  rfl

/-- Each query `q` to `S.simFilterHandler d pk cStar` increases `gCache.length` by at most
`ROQuery.ghCost q`. -/
theorem simFilterHandler_gCache_length_le (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (pk : PK) (cStar : CT)
    (q : ROQuery M CT) (st : SimState M R CT K) (res : ROResp R K q) (st' : SimState M R CT K)
    (hmem : (res, st') ∈ (ProbComp.eval (S.simFilterHandler d pk cStar q st)).support) :
    st'.gCache.length ≤ st.gCache.length + q.ghCost := by
  cases q with
  | G m =>
    simpa only [simFilterHandler, simFilterDispatch, ROQuery.ghCost, ROQuery.dispatch,
      filterDecaps] using
      simHashG_gCache_length_le S.pke.sampleCoins m st (res, st') hmem
  | H x =>
    rcases x with ⟨isFb, m, c⟩
    cases isFb
    · dsimp only [simFilterHandler, simFilterDispatch, simHashH, ROQuery.ghCost, ROQuery.dispatch,
        filterDecaps] at hmem ⊢
      change (res, st') ∈ (ProbComp.eval (simHashG S.pke.sampleCoins m st >>= fun z =>
        (if S.pke.encDet pk m z.fst = c then
          simHashHq S.sampleKey c
        else
          simHashHRaw S.sampleKey (false, m, c)) z.snd)).support at hmem
      rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
      obtain ⟨z, hz, hmem₂⟩ := hmem
      have hz_le := simHashG_gCache_length_le S.pke.sampleCoins m st z hz
      by_cases henc : S.pke.encDet pk m z.fst = c
      · simp only [henc, ↓reduceIte] at hmem₂
        rw [simHashHq_gCache_eq S.sampleKey c z.snd (res, st') hmem₂]
        exact hz_le
      · simp only [henc, ↓reduceIte] at hmem₂
        rw [simHashHRaw_gCache_eq S.sampleKey (false, m, c) z.snd (res, st') hmem₂]
        exact hz_le
    · dsimp only [simFilterHandler, simFilterDispatch, simHashH, ROQuery.ghCost, ROQuery.dispatch,
        filterDecaps] at hmem ⊢
      rw [simHashHRaw_gCache_eq S.sampleKey (true, m, c) st (res, st') hmem]
      exact Nat.le_add_right _ 1
  | decaps c =>
    dsimp only [simFilterHandler, simFilterDispatch, ROQuery.ghCost, ROQuery.dispatch,
      filterDecaps] at hmem ⊢
    by_cases hc : c = cStar
    · simp only [hc, ↓reduceIte] at hmem
      change (res, st') ∈ (ProbComp.eval (pure (none, st))).support at hmem
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨-, rfl⟩
      simp
    · simp only [hc, ↓reduceIte] at hmem
      cases hd : d st.gCache c
      · simp only [hd, filterDecaps, Bool.cond_false] at hmem
        change (res, st') ∈ (ProbComp.eval (pure (none, st))).support at hmem
        simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨-, rfl⟩
        simp
      · simp only [hd, filterDecaps, Bool.cond_true] at hmem
        change (res, st') ∈ (ProbComp.eval (simHashHq S.sampleKey c st >>= fun a =>
          pure (some a.fst, a.snd))).support at hmem
        rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
        obtain ⟨z, hz, hmem₂⟩ := hmem
        simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem₂
        rcases hmem₂ with ⟨-, rfl⟩
        rw [simHashHq_gCache_eq S.sampleKey c st z hz, Nat.add_zero]

/-- Each query `q` to `S.simHandler pk cStar` increases `gCache.length` by at most
`ROQuery.ghCost q`. -/
theorem simHandler_gCache_length_le (S : Scheme PK SK M R CT K) (pk : PK) (cStar : CT)
    (q : ROQuery M CT) (st : SimState M R CT K) (res : ROResp R K q) (st' : SimState M R CT K)
    (hmem : (res, st') ∈ (ProbComp.eval (S.simHandler pk cStar q st)).support) :
    st'.gCache.length ≤ st.gCache.length + q.ghCost :=
  S.simFilterHandler_gCache_length_le (fun _ _ => true) pk cStar q st res st' hmem

omit [DecidableEq M] in
/-- If each row of an `|M| × |M|` matrix sums to at most `Q` and `2 ≤ |M|`, some off-diagonal pair
`(m₀, m₁)` bounds the diagonal average by `|p m₀ m₁ - p m₁ m₁| + Q / |M|`. -/
private theorem avg_pair_abs [Fintype M] (hM : 2 ≤ Fintype.card M)
    (p : M → M → ℝ) (Q : ℝ) (hrow : ∀ a, ∑ b : M, p a b ≤ Q) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (∑ m : M, p m m) / (Fintype.card M : ℝ) ≤
        |p m₀ m₁ - p m₁ m₁| + Q / (Fintype.card M : ℝ) := by
  classical
  set N := Fintype.card M with hN
  set T := ∑ m : M, p m m with hT
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hne : (Finset.univ : Finset M).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff]; omega
  have ⟨a₀, _⟩ := hne
  have herase₀ : (Finset.univ.erase a₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ a₀), Finset.card_univ]; omega
  obtain ⟨b₀, hb₀⟩ := herase₀
  have hab₀ : a₀ ≠ b₀ := (Finset.ne_of_mem_erase hb₀).symm
  by_contra hcon
  push Not at hcon
  have h0lt : 0 < (T - Q) / (N : ℝ) := by
    have h₀ := hcon a₀ b₀ hab₀
    have habs : 0 ≤ |p a₀ b₀ - p b₀ b₀| := abs_nonneg _
    linarith [div_sub_div_same T Q (N : ℝ)]
  have hentry : ∀ a b : M, p b b - p a b < (T - Q) / (N : ℝ) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simpa only [sub_self] using h0lt
    · have h1 := hcon a b hab
      have h2 : p b b - p a b ≤ |p a b - p b b| := by
        rw [abs_sub_comm]; exact le_abs_self _
      linarith [div_sub_div_same T Q (N : ℝ)]
  have hlt : ∑ a : M, ∑ b : M, (p b b - p a b) < ∑ _a : M, ∑ _b : M, ((T - Q) / (N : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty hne fun a _ =>
      Finset.sum_lt_sum_of_nonempty hne fun b _ => hentry a b
  have hR : (∑ _a : M, ∑ _b : M, ((T - Q) / (N : ℝ))) = (N : ℝ) * (T - Q) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
    field_simp
  have hL : (∑ a : M, ∑ b : M, (p b b - p a b)) = (N : ℝ) * T - ∑ a : M, ∑ b : M, p a b := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, ← hT]
  have hrows : (∑ a : M, ∑ b : M, p a b) ≤ (N : ℝ) * Q := by
    calc (∑ a : M, ∑ b : M, p a b) ≤ ∑ _a : M, Q := Finset.sum_le_sum fun a _ => hrow a
      _ = (N : ℝ) * Q := by simp [← hN]
  rw [hL, hR] at hlt
  linarith

/-- Probability that `S.romFilterCpaReduction d A m₀ m₁` records `m₁` in `gCache` when challenged
on an encryption of `m₀` in `S.pke.indCpaGame`. -/
noncomputable def simFilterHitProb (S : Scheme PK SK M R CT K)
    (d : PK → List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K) (m₀ m₁ : M) : ℝ :=
  ((ProbComp.eval (S.pke.indCpaGame m₀ m₁ false (S.romFilterCpaReduction d A m₀ m₁))) true).toReal

/-- Probability that `S.romCpaReduction A m₀ m₁` records `m₁` in `gCache` when challenged on an
encryption of `m₀` in `S.pke.indCpaGame`. -/
noncomputable def simHitProb (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (m₀ m₁ : M) : ℝ :=
  ((ProbComp.eval (S.pke.indCpaGame m₀ m₁ false (S.romCpaReduction A m₀ m₁))) true).toReal

/-- The fixed-message IND-CPA advantage of `S.romFilterCpaReduction d A m₀ m₁` on `(m₀, m₁)`
unfolds to the absolute difference between the simulator `G`-query hit probabilities on `m₁`
under challenge encryptions of `m₀` and `m₁`. -/
theorem indCpaAdvantage_romFilterCpaReduction (S : Scheme PK SK M R CT K)
    (d : PK → List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K) (m₀ m₁ : M) :
    (S.pke.indCpaAdvantage m₀ m₁ (S.romFilterCpaReduction d A m₀ m₁) : ℝ) =
      |S.simFilterHitProb d A m₀ m₁ - S.simFilterHitProb d A m₁ m₁| := by
  have htrue : S.pke.indCpaGame m₀ m₁ true (S.romFilterCpaReduction d A m₀ m₁) =
      S.pke.indCpaGame m₁ m₁ false (S.romFilterCpaReduction d A m₁ m₁) := rfl
  simp only [ExplicitCoinPKE.indCpaAdvantage, Game.coe_advantage,
    Game.coe_succProbability, simFilterHitProb, htrue]

/-- The fixed-message IND-CPA advantage of `S.romCpaReduction A m₀ m₁` on `(m₀, m₁)` unfolds to
the absolute difference between the simulator `G`-query hit probabilities on `m₁` under challenge
encryptions of `m₀` and `m₁`. -/
theorem indCpaAdvantage_romCpaReduction (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (m₀ m₁ : M) :
    (S.pke.indCpaAdvantage m₀ m₁ (S.romCpaReduction A m₀ m₁) : ℝ) =
      |S.simHitProb A m₀ m₁ - S.simHitProb A m₁ m₁| :=
  S.indCpaAdvantage_romFilterCpaReduction (fun _ _ _ => true) A m₀ m₁

/-- **Query-count row bound on filtered simulator hit probabilities**: for any adversary `A`
satisfying `ROQueryBounds A qG qH`, any decapsulation filter `d`, and any challenge message `m₀`,
the sum over all target messages `m₁ : M` of `S.simFilterHitProb d A m₀ m₁` is at most `qG + qH`. -/
theorem sum_simFilterHitProb_le [Fintype M] (S : Scheme PK SK M R CT K)
    (d : PK → List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K)
    {qG qH : ℕ} (hq : ROQueryBounds A qG qH) (m₀ : M) :
    ∑ m₁ : M, S.simFilterHitProb d A m₀ m₁ ≤ (qG : ℝ) + (qH : ℝ) := by
  let runDist : PMF (Bool × SimState M R CT K) :=
    (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
    (ProbComp.eval S.sampleKey).bind fun kStar =>
      let cStar := S.pke.encDet keys.fst m₀ rStar
      (OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
        (fun q st => ProbComp.eval (S.simFilterHandler (d keys.fst) keys.fst cStar q st))
        (A ⟨keys.fst, cStar, kStar⟩)).run {}
  have heq (m₁ : M) :
      ProbComp.eval (S.pke.indCpaGame m₀ m₁ false (S.romFilterCpaReduction d A m₀ m₁)) =
        runDist.map fun p => (p.snd.gCache.lookup m₁).isSome := by
    simp only [ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt, romFilterCpaReduction,
      Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      OracleComp.map_run_interpret ProbComp.isMonadHom_eval, runDist, PMF.map, PMF.bind_bind,
      PMF.pure_bind, Function.comp_def]
  have hcard : ∀ x ∈ runDist.support,
      (Finset.univ.filter fun m => (x.snd.gCache.lookup m).isSome = true).card ≤ qG + qH := by
    intro x hx
    simp only [runDist, PMF.mem_support_bind_iff] at hx
    obtain ⟨keys, -, rStar, -, kStar, -, hrun⟩ := hx
    set pk := keys.fst
    set cStar := S.pke.encDet pk m₀ rStar
    have hlen := (hq.ghCost ⟨pk, cStar, kStar⟩).measure_le
      (fun q st => ProbComp.eval (S.simFilterHandler (d pk) pk cStar q st))
      (fun st : SimState M R CT K => st.gCache.length)
      (S.simFilterHandler_gCache_length_le (d pk) pk cStar)
      hrun
    exact (RandomOracle.card_filter_lookup_isSome_le x.snd.gCache).trans (by simpa using hlen)
  calc ∑ m₁ : M, S.simFilterHitProb d A m₀ m₁
      = ∑ m₁ : M, ((runDist.map fun p => (p.snd.gCache.lookup m₁).isSome) true).toReal := by
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [simFilterHitProb, heq m₁]
    _ ≤ ((qG + qH : ℕ) : ℝ) := sum_toReal_indicator_le runDist _ (qG + qH) hcard
    _ = (qG : ℝ) + (qH : ℝ) := Nat.cast_add qG qH

/-- **Query-count row bound on simulator hit probabilities**: for any adversary `A` satisfying
`ROQueryBounds A qG qH` and any challenge message `m₀`, the sum over all target messages `m₁ : M`
of `S.simHitProb A m₀ m₁` is at most `qG + qH`. -/
theorem sum_simHitProb_le [Fintype M] (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) {qG qH : ℕ} (hq : ROQueryBounds A qG qH) (m₀ : M) :
    ∑ m₁ : M, S.simHitProb A m₀ m₁ ≤ (qG : ℝ) + (qH : ℝ) :=
  S.sum_simFilterHitProb_le (fun _ _ _ => true) A hq m₀

/-- **OW-to-CPA averaging bound for `romFilterCpaReduction`**: when `2 ≤ Fintype.card M` and `A`
satisfies `ROQueryBounds A qG qH`, there exist distinct messages `m₀ ≠ m₁` such that the average
diagonal simulator hit probability `|M|⁻¹ ∑_m S.simFilterHitProb d A m m` is bounded by
`S.pke.indCpaAdvantage m₀ m₁ (S.romFilterCpaReduction d A m₀ m₁) + (qG + qH) / |M|`. -/
theorem avg_simFilterHitProb_le_indCpaAdvantage_romFilterCpaReduction [Fintype M]
    (S : Scheme PK SK M R CT K) (d : PK → List (M × R) → CT → Bool)
    (A : ROAdversary PK M R CT K) {qG qH : ℕ} (hM : 2 ≤ Fintype.card M)
    (hq : ROQueryBounds A qG qH) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (∑ m : M, S.simFilterHitProb d A m m) / (Fintype.card M : ℝ) ≤
        (S.pke.indCpaAdvantage m₀ m₁ (S.romFilterCpaReduction d A m₀ m₁) : ℝ) +
          ((qG : ℝ) + (qH : ℝ)) / (Fintype.card M : ℝ) := by
  obtain ⟨m₀, m₁, hne, hpair⟩ :=
    avg_pair_abs hM (S.simFilterHitProb d A) ((qG : ℝ) + (qH : ℝ))
      (S.sum_simFilterHitProb_le d A hq)
  refine ⟨m₀, m₁, hne, ?_⟩
  rwa [S.indCpaAdvantage_romFilterCpaReduction d A m₀ m₁]

/-- **OW-to-CPA averaging bound for `romCpaReduction`**: when `2 ≤ Fintype.card M` and `A`
satisfies `ROQueryBounds A qG qH`, there exist distinct messages `m₀ ≠ m₁` such that the average
diagonal simulator hit probability `|M|⁻¹ ∑_m S.simHitProb A m m` is bounded by
`S.pke.indCpaAdvantage m₀ m₁ (S.romCpaReduction A m₀ m₁) + (qG + qH) / |M|`. -/
theorem avg_simHitProb_le_indCpaAdvantage_romCpaReduction [Fintype M]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    {qG qH : ℕ} (hM : 2 ≤ Fintype.card M) (hq : ROQueryBounds A qG qH) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (∑ m : M, S.simHitProb A m m) / (Fintype.card M : ℝ) ≤
        (S.pke.indCpaAdvantage m₀ m₁ (S.romCpaReduction A m₀ m₁) : ℝ) +
          ((qG : ℝ) + (qH : ℝ)) / (Fintype.card M : ℝ) :=
  S.avg_simFilterHitProb_le_indCpaAdvantage_romFilterCpaReduction (fun _ _ _ => true) A hM hq

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto

/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.KEM.FujisakiOkamoto
public import Complexity.Languages.Probabilistic.RandomOracle
import Complexity.Languages.Probabilistic.Simulation

/-!
# ROM IND-CCA Games, Eager/Lazy Equivalence, and CPA Reduction for HHK17 `FO-notbot`

This module formalizes the Random Oracle Model (ROM) IND-CCA security experiments, eager/lazy
equivalence, keyless oracle simulator, and IND-CPA reduction hit-probability bounds for the
domain-separated implicit-rejection Fujisaki–Okamoto transform `FO-notbot` (`Scheme.keyGenNotBot`,
`Scheme.encapsNotBot`, `Scheme.decapsNotBot`) from `Complexity.Crypto.Protocols.KEM.FujisakiOkamoto`
([HofheinzHoevelmannsKiltz2017], IACR ePrint 2017/604 full version dated 2 November 2021, §2.1,
§2.1 Def. 2.2 / Fig. 4, §3.1 Fig. 5, and §3.2.2 Fig. 12).

## Source map and model notes

Section and figure locators follow `Complexity.Crypto.Protocols.KEM.FujisakiOkamoto` and refer to
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

On top of those definitions, this module formalizes:

1. **Executable lazy and eager ROM IND-CCA games for `FO-notbot`** (`Scheme.roIndCcaGame`,
   `Scheme.indCcaRomAdvantage`, `Scheme.eagerIndCcaGame`) over the oracle interface
   `ROQuery M CT` (`G`, `H`, and punctured decapsulation rejecting `c = cStar` with `none`),
   together with exact eager/lazy equivalence (`Scheme.eval_roIndCcaGame_eq_h1`,
   `Scheme.eval_roIndCcaGame_eq_eagerIndCcaGame`, `Scheme.indCcaRomAdvantage_eq_eager`).
2. **Keyless ROM simulator and IND-CPA reduction** (`Scheme.simHandler`,
   `Scheme.romCpaReduction`, `Scheme.simHitProb`): `simHandler` answers `H(false, m, c)` via a
   lazy ciphertext-indexed table `H_q(c)` whenever the §3.1 Fig. 5 re-encryption check
   `Enc(pk, m; G(m)) = c` holds and answers punctured decapsulation queries `c ≠ cStar` from
   `H_q(c)` without using `sk`; `romCpaReduction` runs `A` against `simHandler` on an
   `ExplicitCoinPKE.indCpaGame` challenge `(pk, cStar)` and outputs whether `m₁` was recorded in
   `gCache`. We prove the exact IND-CPA advantage identity
   `Scheme.indCpaAdvantage_romCpaReduction`, the query-budget row bound
   `Scheme.sum_simHitProb_le`, and the OW-to-CPA averaging bound
   `Scheme.avg_simHitProb_le_indCpaAdvantage_romCpaReduction`. Multi-hop game transitions from
   `eagerIndCcaGame` to `simHitProb` via fallback-seed decoupling and `δ`-correctness bad-event
   bounds are deferred to follow-up modules.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.ROQuery`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.ROResp`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.ROAdversary`: query/response family and oracle
  adversary for the ROM IND-CCA experiment with random oracles `G`, `H` and decapsulation oracle.
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
* `Cslib.Crypto.Protocols.FujisakiOkamoto.SimState`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.romCpaReduction`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simHitProb`: keyless ROM simulator,
  IND-CPA reduction, and simulator `G`-query hit probability.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eval_roIndCcaGame_eq_eagerIndCcaGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaRomAdvantage_eq_eager`:
  the lazy executable game `roIndCcaGame` has the same output distribution and advantage as
  `eagerIndCcaGame`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCpaAdvantage_romCpaReduction`:
  characterizes the IND-CPA advantage of `romCpaReduction` in terms of the simulator's
  `G`-query hit probability `simHitProb`.
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

/-- An IND-CCA adversary in the Random Oracle Model receives `(pk, c*, k*)` and interacts
with `G`, `H`, and the decapsulation oracle before outputting a Boolean guess. -/
abbrev ROAdversary (PK M R CT K : Type) : Type :=
  PK × CT × K → OracleComp (ROResp (M := M) (CT := CT) R K) Bool

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

/-- An `ROAdversary` satisfies query bounds `(qG, qH)` if for every challenge input `inp`,
its execution makes at most `qG` queries to `G` and at most `qH` queries to `H`. -/
def ROQueryBounds (A : ROAdversary PK M R CT K) (qG qH : ℕ) : Prop :=
  ∀ inp : PK × CT × K,
    OracleComp.IsCostBounded ROQuery.gCost (A inp) qG ∧
    OracleComp.IsCostBounded ROQuery.hCost (A inp) qH

/-- Lift a stateful computation on a component cache `C` into a composite state `S`. -/
def zoomStateT {S C α : Type} {m : Type → Type} [Monad m]
    (get : S → C) (set : S → C → S) (act : StateT C m α) : StateT S m α := fun s => do
  let (a, c') ← act (get s)
  return (a, set s c')

/-- Association-list caches for the lazy random oracles `G : M → R` and
`H : Bool × M × CT → K` in the executable ROM IND-CCA game. -/
structure ROCache (M R CT K : Type) where
  /-- Cached query-response pairs for `G : M → R`. -/
  gCache : List (M × R) := []
  /-- Cached query-response pairs for `H : Bool × M × CT → K`. -/
  hCache : List ((Bool × M × CT) × K) := []

/-- Association-list caches for the HHK17 ROM simulator: `gCache` for `G : M → R`,
`hCache` for unprogrammed queries to `H : Bool × M × CT → K`, and `hqCache` for the
ciphertext-indexed key table `H_q : CT → K`. -/
structure SimState (M R CT K : Type) where
  /-- Cached query-response pairs for `G : M → R`. -/
  gCache : List (M × R) := []
  /-- Cached query-response pairs for unprogrammed `H : Bool × M × CT → K` queries. -/
  hCache : List ((Bool × M × CT) × K) := []
  /-- Cached query-response pairs for the ciphertext-key table `H_q : CT → K`. -/
  hqCache : List (CT × K) := []

section LazyOracles

variable [DecidableEq M] [DecidableEq CT]

/-- Lazy evaluation of `G : M → R` inside `ROCache` via `memoize`. -/
def roHashG (sampleCoins : ProbComp R) (m : M) : StateT (ROCache M R CT K) ProbComp R :=
  zoomStateT ROCache.gCache (fun st c => { st with gCache := c })
    (memoize (fun _ => sampleCoins) m)

/-- Lazy evaluation of `H : Bool × M × CT → K` inside `ROCache` via `memoize`. -/
def roHashH (sampleKey : ProbComp K) (x : Bool × M × CT) :
    StateT (ROCache M R CT K) ProbComp K :=
  zoomStateT ROCache.hCache (fun st c => { st with hCache := c })
    (memoize (fun _ => sampleKey) x)

/-- Lazy evaluation of `G : M → R` inside `SimState` via `memoize`. -/
def simHashG (sampleCoins : ProbComp R) (m : M) : StateT (SimState M R CT K) ProbComp R :=
  zoomStateT SimState.gCache (fun st c => { st with gCache := c })
    (memoize (fun _ => sampleCoins) m)

/-- Lazy evaluation of unprogrammed `H : Bool × M × CT → K` queries inside `SimState` via
`memoize`. -/
def simHashHRaw (sampleKey : ProbComp K) (x : Bool × M × CT) :
    StateT (SimState M R CT K) ProbComp K :=
  zoomStateT SimState.hCache (fun st c => { st with hCache := c })
    (memoize (fun _ => sampleKey) x)

/-- Lazy evaluation of the ciphertext-key table `H_q : CT → K` inside `SimState` via
`memoize`. -/
def simHashHq (sampleKey : ProbComp K) (c : CT) : StateT (SimState M R CT K) ProbComp K :=
  zoomStateT SimState.hqCache (fun st c' => { st with hqCache := c' })
    (memoize (fun _ => sampleKey) c)

end LazyOracles

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- Stateful oracle handler for the real ROM IND-CCA game of `FO-notbot`. Queries to the
challenge ciphertext `cStar` are rejected with `none`; other decapsulation queries
re-encrypt under the lazy random oracle `G` and derive the key via the lazy random oracle
`H`, falling back to `H(true, dk.fallback, c)` on implicit rejection. -/
def roHandler (S : Scheme PK SK M R CT K) (dk : ImplicitSK PK SK M) (cStar : CT)
    (q : ROQuery M CT) : StateT (ROCache M R CT K) ProbComp (ROResp R K q) :=
  match q with
  | .G m => roHashG S.pke.sampleCoins m
  | .H x => roHashH S.sampleKey x
  | .decaps c =>
    if c = cStar then
      return none
    else
      match S.pke.dec dk.sk c with
      | none => do
        let k ← roHashH S.sampleKey (true, dk.fallback, c)
        return some k
      | some m' => do
        let r' ← roHashG S.pke.sampleCoins m'
        if S.pke.encDet dk.pk m' r' = c then do
          let k ← roHashH S.sampleKey (false, m', c)
          return some k
        else do
          let k ← roHashH S.sampleKey (true, dk.fallback, c)
          return some k

/-- The executable ROM IND-CCA security game for `FO-notbot` with bit `b : Bool`.
When `b = false`, the adversary receives the real encapsulated key `kReal = H(false, m*, c*)`;
when `b = true`, it receives an independent uniform key `kRand`. -/
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
    (OracleComp.interpret (S.roHandler dk cStar) (A (pk, cStar, kStar))).run st₀
  return guess

/-- The ROM IND-CCA advantage of an adversary `A` against `FO-notbot`. -/
noncomputable def indCcaRomAdvantage (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) : ℝ≥0 :=
  Game.advantage
    (ProbComp.eval (S.roIndCcaGame A false))
    (ProbComp.eval (S.roIndCcaGame A true))

/-- The eager random-oracle IND-CCA game for `FO-notbot`, defined directly from
`S.keyGenNotBot`, `S.encapsNotBot`, and `S.decapsNotBot` over eagerly sampled
random functions `G : M → R` and `H : Bool × M × CT → K`. -/
noncomputable def eagerIndCcaGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, dk) ← ProbComp.eval S.keyGenNotBot
  let G ← pi (α := fun _ : M => R) (fun _ => ProbComp.eval S.pke.sampleCoins)
  let H ← pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let (cStar, kReal) ← ProbComp.eval (S.encapsNotBot G H pk)
  let kRand ← ProbComp.eval S.sampleKey
  let kStar := if b then kRand else kReal
  OracleComp.interpret (fun (q : ROQuery M CT) => match q with
    | .G m => PMF.pure (G m)
    | .H x => PMF.pure (H x)
    | .decaps c => PMF.pure (if c = cStar then none else some (S.decapsNotBot G H dk c)))
    (A (pk, cStar, kStar))

/-- Simulated `H` oracle: on key-derivation queries `(false, m, c)`, checks whether
`S.pke.encDet pk m (G(m)) = c` and if so returns `H_q(c)` so that decapsulation queries can
be answered consistently without the secret key `sk`. -/
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

/-- Stateful oracle handler for the HHK17 ROM simulator. Decapsulation queries for
`c ≠ cStar` are answered directly from `H_q(c)` without using `sk`. -/
def simHandler (S : Scheme PK SK M R CT K) (pk : PK) (cStar : CT) (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  match q with
  | .G m => simHashG S.pke.sampleCoins m
  | .H x => S.simHashH pk x
  | .decaps c =>
    if c = cStar then
      return none
    else do
      let k ← simHashHq S.sampleKey c
      return some k

/-- The HHK17 IND-CPA reduction `B_{m0, m1}` from a ROM IND-CCA adversary `A`: given an
IND-CPA challenge `pk` and `cStar`, samples a challenge key `kStar ← S.sampleKey`, runs
`A(pk, cStar, kStar)` against `S.simHandler pk cStar`, and outputs whether `m1` was
queried to `G`. -/
def romCpaReduction (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (_m0 m1 : M) : PK → CT → ProbComp Bool :=
  fun pk cStar => do
    let kStar ← S.sampleKey
    let (_, st) ←
      (OracleComp.interpret (S.simHandler pk cStar) (A (pk, cStar, kStar))).run {}
    return (st.gCache.lookup m1).isSome

/-! ### Section 2: Connecting `memoize` to `RandomOracle.answer` and Eager/Lazy Equivalence -/

/-- Mapping an association-list cache by `RandomOracle.ofList` turns `memoize` into
`RandomOracle.answer`. -/
theorem memoize_map_ofList {Q V : Type} [DecidableEq Q] (d : Q → PMF V) (q : Q)
    (cache : List (Q × V)) :
    (memoize d q cache).map (fun (v, c') => (v, RandomOracle.ofList c')) =
      RandomOracle.answer d q (RandomOracle.ofList cache) := by
  cases h : cache.lookup q with
  | none =>
    rw [memoize_of_none _ _ _ h, RandomOracle.answer_of_none d (RandomOracle.ofList cache) q h]
    change ((d q).map (fun v => (v, (q, v) :: cache))).map _ = _
    simp only [PMF.map_comp, Function.comp_def, RandomOracle.ofList_cons]
  | some v =>
    rw [memoize_of_some _ _ _ _ h, RandomOracle.answer_of_some d (RandomOracle.ofList cache) q v h]
    exact PMF.pure_map _ _

/-- Evaluating `zoomStateT get set (memoize (fun _ => dist) q)` commutes with `ProbComp.eval`. -/
theorem eval_zoomStateT_memoize {S₀ Q V : Type} [DecidableEq Q]
    (get : S₀ → List (Q × V)) (set : S₀ → List (Q × V) → S₀)
    (dist : ProbComp V) (q : Q) (s : S₀) :
    ProbComp.eval (zoomStateT get set (memoize (fun _ => dist) q) s) =
      (memoize (fun _ => ProbComp.eval dist) q (get s)).map
        (fun (v, c') => (v, set s c')) := by
  simp [zoomStateT, ProbComp.eval_memoize, PMF.map]

/-- Sampling one coordinate `v ← p i` and completing the remaining coordinates via
`pi (Function.update p i (PMF.pure v))` equals sampling `G ← pi p` and reading `(G i, G)`. -/
theorem bind_pi_update {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Finite (α i)]
    {β : Type*} (p : ∀ i, PMF (α i)) (i : ι) (F : α i → (∀ j, α j) → PMF β) :
    (p i).bind (fun v => (pi (Function.update p i (PMF.pure v))).bind (F v)) =
      (pi p).bind (fun G => F (G i) G) := by
  have h := congrArg (fun q : PMF (α i × ∀ j, α j) => q.bind (fun x => F x.fst x.snd))
    (pi_bind_update_pair p i)
  simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def] using h

/-- Evaluating an `OracleComp` interpreted into `StateT σ ProbComp` commutes with `ProbComp.eval`
on the state transformer. -/
theorem eval_run_interpret {ι σ α : Type} {spec : ι → Type}
    (h : (q : ι) → StateT σ ProbComp (spec q)) (prog : OracleComp spec α) (s : σ) :
    ProbComp.eval ((OracleComp.interpret h prog).run s) =
      (OracleComp.interpret (m := StateT σ PMF) (fun q s' => ProbComp.eval (h q s')) prog).run s :=
  OracleComp.map_run_interpret ProbComp.isMonadHom_eval h prog s

/-- Hybrid 1 handler: `G : M → R` is a complete table while `H : Bool × M × CT → K` is answered
lazily via `RandomOracle.answer`. Decapsulation uses `decT S.pke G dk.pk dk.sk c`. -/
noncomputable def h1Handler (S : Scheme PK SK M R CT K)
    (G : M → R) (dk : ImplicitSK PK SK M) (cStar : CT)
    (q : ROQuery M CT) :
    StateT (RandomOracle.Cache (fun _ : Bool × M × CT => K)) PMF (ROResp R K q) := fun tH =>
  match q with
  | .G m => PMF.pure (G m, tH)
  | .H x => RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) x tH
  | .decaps c =>
    if c = cStar then
      PMF.pure (none, tH)
    else
      match decT S.pke G dk.pk dk.sk c with
      | some m' =>
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (false, m', c) tH).map
          (fun (k, tH') => (some k, tH'))
      | none =>
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (true, dk.fallback, c) tH).map
          (fun (k, tH') => (some k, tH'))

/-- Intermediate handler answering `G` and `H` via `RandomOracle.answer` on a pair of
`RandomOracle.Cache` tables `(tG, tH)`. -/
noncomputable def roAnswerHandler (S : Scheme PK SK M R CT K)
    (dk : ImplicitSK PK SK M) (cStar : CT) (q : ROQuery M CT) :
    StateT (RandomOracle.Cache (fun _ : M => R) ×
      RandomOracle.Cache (fun _ : Bool × M × CT => K)) PMF (ROResp R K q) := fun (tG, tH) =>
  match q with
  | .G m =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m tG).map
      (fun (r, tG') => (r, (tG', tH)))
  | .H x =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) x tH).map
      (fun (k, tH') => (k, (tG, tH')))
  | .decaps c =>
    if c = cStar then
      PMF.pure (none, (tG, tH))
    else
      match S.pke.dec dk.sk c with
      | none =>
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (true, dk.fallback, c) tH).map
          (fun (k, tH') => (some k, (tG, tH')))
      | some m' =>
        (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m' tG).bind fun (r', tG') =>
          if S.pke.encDet dk.pk m' r' = c then
            (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (false, m', c) tH).map
              (fun (k, tH') => (some k, (tG', tH')))
          else
            (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (true, dk.fallback, c) tH).map
              (fun (k, tH') => (some k, (tG', tH')))

/-- Evaluating `(do let k ← roHashH sampleKey x; return some k) st` and mapping `ROCache` via
`RandomOracle.ofList`. -/
theorem eval_roHashH_some_map_ofList (sampleKey : ProbComp K) (x : Bool × M × CT)
    (st : ROCache M R CT K) :
    (ProbComp.eval ((do let k ← roHashH sampleKey x; return some k) st)).map
      (fun (res, st') =>
        (res, (RandomOracle.ofList st'.gCache, RandomOracle.ofList st'.hCache))) =
    (RandomOracle.answer (fun _ => ProbComp.eval sampleKey) x
      (RandomOracle.ofList st.hCache)).map
      (fun (k, tH') => (some k, (RandomOracle.ofList st.gCache, tH'))) := by
  dsimp only [roHashH]
  change (ProbComp.eval (zoomStateT ROCache.hCache (fun st c => { st with hCache := c })
    (memoize (fun _ => sampleKey) x) st >>= fun a => pure (some a.fst, a.snd))).map _ = _
  simp only [ProbComp.eval_bind, eval_zoomStateT_memoize, ProbComp.eval_pure,
    PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def]
  have h := congrArg (PMF.map (fun (k, tH') => (some k, (RandomOracle.ofList st.gCache, tH'))))
    (memoize_map_ofList (fun _ => ProbComp.eval sampleKey) x st.hCache)
  simpa only [PMF.map_comp, Function.comp_def, PMF.map, PMF.bind_bind, PMF.pure_bind] using h

/-- Mapping `ROCache` via `RandomOracle.ofList` turns `S.roHandler` into `S.roAnswerHandler`. -/
theorem roHandler_map_ofList (S : Scheme PK SK M R CT K) (dk : ImplicitSK PK SK M) (cStar : CT)
    (q : ROQuery M CT) (st : ROCache M R CT K) :
    (ProbComp.eval (S.roHandler dk cStar q st)).map
      (fun (res, st') =>
        (res, (RandomOracle.ofList st'.gCache, RandomOracle.ofList st'.hCache))) =
    S.roAnswerHandler dk cStar q
      (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache) := by
  let dG : M → PMF R := fun _ => ProbComp.eval S.pke.sampleCoins
  let dH : Bool × M × CT → PMF K := fun _ => ProbComp.eval S.sampleKey
  cases q with
  | G m =>
    dsimp only [roHandler, roHashG, roAnswerHandler]
    rw [eval_zoomStateT_memoize]
    have h := congrArg (PMF.map (fun (r, tG') => (r, (tG', RandomOracle.ofList st.hCache))))
      (memoize_map_ofList dG m st.gCache)
    simpa only [PMF.map_comp, Function.comp_def, dG] using h
  | H x =>
    dsimp only [roHandler, roHashH, roAnswerHandler]
    rw [eval_zoomStateT_memoize]
    have h := congrArg (PMF.map (fun (k, tH') => (k, (RandomOracle.ofList st.gCache, tH'))))
      (memoize_map_ofList dH x st.hCache)
    simpa only [PMF.map_comp, Function.comp_def, dH] using h
  | decaps c =>
    dsimp only [roHandler, roAnswerHandler]
    by_cases hc : c = cStar
    · simp only [hc, ↓reduceIte]
      exact PMF.pure_map _ _
    · simp only [hc, ↓reduceIte]
      cases hdec : S.pke.dec dk.sk c with
      | none => exact eval_roHashH_some_map_ofList S.sampleKey (true, dk.fallback, c) st
      | some m' =>
        change (ProbComp.eval (roHashG S.pke.sampleCoins m' st >>= fun a =>
            (if S.pke.encDet dk.pk m' a.fst = c then do
              let k ← roHashH S.sampleKey (false, m', c)
              return some k
            else do
              let k ← roHashH S.sampleKey (true, dk.fallback, c)
              return some k) a.snd)).map _ = _
        dsimp only [roHashG]
        simp only [ProbComp.eval_bind, eval_zoomStateT_memoize, PMF.map_bind, PMF.bind_map,
          Function.comp_def]
        rw [← memoize_map_ofList dG m' st.gCache, PMF.bind_map]
        congr 1; funext ⟨r', gC'⟩
        dsimp only [Function.comp_def]
        by_cases henc : S.pke.encDet dk.pk m' r' = c <;>
          simp only [henc, ↓reduceIte] <;>
          exact eval_roHashH_some_map_ofList S.sampleKey _ { st with gCache := gC' }

/-- Single-step simulation from `S.roAnswerHandler` to `S.h1Handler` via
`RandomOracle.answer_complete`. -/
theorem roAnswerHandler_sim_h1 [Fintype M] [Finite R]
    (S : Scheme PK SK M R CT K) (dk : ImplicitSK PK SK M) (cStar : CT)
    (q : ROQuery M CT)
    (st : RandomOracle.Cache (fun _ : M => R) × RandomOracle.Cache (fun _ : Bool × M × CT => K)) :
    (do
      let (res, st') ← S.roAnswerHandler dk cStar q st
      let G ← RandomOracle.complete (fun _ : M => ProbComp.eval S.pke.sampleCoins) st'.fst
      PMF.pure (res, (G, st'.snd))) =
    (do
      let G ← RandomOracle.complete (fun _ : M => ProbComp.eval S.pke.sampleCoins) st.fst
      let (res, tH') ← S.h1Handler G dk cStar q st.snd
      PMF.pure (res, (G, tH'))) := by
  rcases st with ⟨tG, tH⟩
  let dG : M → PMF R := fun _ => ProbComp.eval S.pke.sampleCoins
  let dH : Bool × M × CT → PMF K := fun _ => ProbComp.eval S.sampleKey
  simp only [Probability.PMF.monad_bind_eq_bind]
  cases q with
  | G m =>
    dsimp only [roAnswerHandler, h1Handler]
    have hc := congrArg (PMF.map (fun (r, G) => (r, (G, tH))))
      (RandomOracle.answer_complete dG tG m)
    simpa only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
      Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.map, dG] using hc
  | H x =>
    dsimp only [roAnswerHandler, h1Handler]
    rw [PMF.bind_map, PMF.bind_comm]
    rfl
  | decaps c =>
    dsimp only [roAnswerHandler, h1Handler]
    by_cases hc : c = cStar
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      cases hdec : S.pke.dec dk.sk c with
      | none =>
        simp only [decT, hdec, Function.comp_def, PMF.map, PMF.bind_bind, PMF.pure_bind]
        exact PMF.bind_comm _ _ _
      | some m' =>
        simp only [decT, encT, hdec, PMF.bind_bind]
        have hcomm :
            (RandomOracle.answer dG m' tG).bind (fun (r', tG') =>
              (if S.pke.encDet dk.pk m' r' = c then
                (RandomOracle.answer dH (false, m', c) tH).map
                  (fun (k, tH') => (some k, (tG', tH')))
              else
                (RandomOracle.answer dH (true, dk.fallback, c) tH).map
                  (fun (k, tH') => (some k, (tG', tH')))).bind
              fun (res, st') => (RandomOracle.complete dG st'.fst).bind
                fun G => PMF.pure (res, (G, st'.snd))) =
            ((RandomOracle.answer dG m' tG).bind (fun (r', tG') =>
              (RandomOracle.complete dG tG').map (fun G => (r', G)))).bind (fun (r', G) =>
              if S.pke.encDet dk.pk m' r' = c then
                (RandomOracle.answer dH (false, m', c) tH).bind
                  fun (k, tH') => PMF.pure (some k, (G, tH'))
              else
                (RandomOracle.answer dH (true, dk.fallback, c) tH).bind
                  fun (k, tH') => PMF.pure (some k, (G, tH'))) := by
          simp only [PMF.bind_bind]
          congr 1; funext ⟨r', tG'⟩
          by_cases henc : S.pke.encDet dk.pk m' r' = c <;>
            simp only [henc, ↓reduceIte, PMF.bind_map, Function.comp_def]
          · exact PMF.bind_comm _ _ _
          · exact PMF.bind_comm _ _ _
        rw [hcomm]
        have hG := RandomOracle.answer_complete dG tG m'
        simp only [Probability.PMF.monad_bind_eq_bind] at hG
        rw [hG, PMF.bind_map]
        congr 1; funext G
        dsimp only [Function.comp_def]
        by_cases henc : S.pke.encDet dk.pk m' (G m') = c <;>
          simp [henc, dH, PMF.map]

/-- Completing a singleton cache `[(q₀, v₀)]` equals
`pi (Function.update d q₀ (PMF.pure v₀))`. -/
theorem complete_ofList_singleton {Q V : Type} [Fintype Q] [DecidableEq Q] [Finite V]
    (d : Q → PMF V) (q₀ : Q) (v₀ : V) :
    RandomOracle.complete d (RandomOracle.ofList [(q₀, v₀)]) =
      pi (Function.update d q₀ (PMF.pure v₀)) := by
  unfold RandomOracle.complete
  congr 1; funext q
  simp only [RandomOracle.ofList, List.lookup_cons, List.lookup_nil, Function.update_apply]
  by_cases h : q = q₀
  · simp [h]
  · rw [beq_eq_false_iff_ne.mpr h]
    simp [h]

/-- Marginalizing `OracleComp.run_interpret_simulation` to the output value discards the simulated
final state. -/
theorem run_interpret_simulation_fst {ι State State' α : Type} {spec : ι → Type}
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q))
    (relate : State → PMF State')
    (step : ∀ q s, (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (oracle' q))
    (program : OracleComp spec α) (s : State) :
    ((OracleComp.interpret oracle program).run s).map Prod.fst =
      (relate s).bind (fun t => ((OracleComp.interpret oracle' program).run t).map Prod.fst) := by
  have h := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_simulation oracle oracle' relate step program s)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  change (((OracleComp.interpret oracle program).run s).bind fun a =>
      (relate a.snd).map (Function.const _ a.fst)) = _ at h
  simp only [PMF.map_const] at h
  exact h

/-- Running `A` under `S.roHandler` from `st` has the same output distribution as completing
`st.gCache` via `RandomOracle.complete` and running `A` under `S.h1Handler`. -/
theorem eval_run_roHandler_eq_h1 [Fintype M] [Finite R]
    (S : Scheme PK SK M R CT K) (dk : ImplicitSK PK SK M) (cStar : CT)
    (prog : OracleComp (ROResp (M := M) (CT := CT) R K) Bool) (st : ROCache M R CT K) :
    (ProbComp.eval ((OracleComp.interpret (S.roHandler dk cStar) prog).run st)).map Prod.fst =
      (RandomOracle.complete (fun _ : M => ProbComp.eval S.pke.sampleCoins)
        (RandomOracle.ofList st.gCache)).bind (fun G =>
          ((OracleComp.interpret (S.h1Handler G dk cStar) prog).run
            (RandomOracle.ofList st.hCache)).map Prod.fst) := by
  rw [eval_run_interpret]
  have hmap := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_map_state
      (fun q s => ProbComp.eval (S.roHandler dk cStar q s))
      (S.roAnswerHandler dk cStar)
      (fun s => (RandomOracle.ofList s.gCache, RandomOracle.ofList s.hCache))
      (fun q s => S.roHandler_map_ofList dk cStar q s) prog st)
  simp only [PMF.map_comp, Function.comp_def] at hmap
  rw [hmap]
  let sim : (RandomOracle.Cache (fun _ : M => R) ×
      RandomOracle.Cache (fun _ : Bool × M × CT => K)) →
      PMF ((M → R) × RandomOracle.Cache (fun _ : Bool × M × CT => K)) :=
    fun (tG, tH) => (RandomOracle.complete (fun _ : M => ProbComp.eval S.pke.sampleCoins) tG).map
      (fun G => (G, tH))
  let h₂ : (q : ROQuery M CT) →
      StateT ((M → R) × RandomOracle.Cache (fun _ : Bool × M × CT => K)) PMF (ROResp R K q) :=
    fun q (G, tH) => (S.h1Handler G dk cStar q tH).map (fun (res, tH') => (res, (G, tH')))
  have hsim := run_interpret_simulation_fst
    (S.roAnswerHandler dk cStar) h₂ sim
    (fun q s => by
      simpa only [sim, h₂, Probability.PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind,
        Function.comp_def, PMF.map, PMF.bind_bind, PMF.pure_bind] using
        S.roAnswerHandler_sim_h1 dk cStar q s)
    prog (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache)
  simp only [sim, PMF.bind_map, Function.comp_def] at hsim
  rw [hsim]
  congr 1; funext G
  have hproj := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_map_state
      (S.h1Handler G dk cStar) h₂ (fun tH => (G, tH))
      (fun q tH => rfl) prog (RandomOracle.ofList st.hCache))
  simpa only [PMF.map_comp, Function.comp_def] using hproj.symm

/-- Evaluating `S.roIndCcaGame A b` equals sampling `G` eagerly from `pi` and running `A`
against `S.h1Handler`. -/
theorem eval_roIndCcaGame_eq_h1 [Fintype M] [Finite R]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp.eval (S.roIndCcaGame A b) =
      (ProbComp.eval S.keyGenNotBot).bind (fun (pk, dk) =>
      (ProbComp.eval S.sampleMsg).bind (fun mStar =>
      (pi (α := fun _ : M => R) (fun _ => ProbComp.eval S.pke.sampleCoins)).bind (fun G =>
      let cStar := S.pke.encDet pk mStar (G mStar)
      (ProbComp.eval S.sampleKey).bind (fun kReal =>
      (ProbComp.eval S.sampleKey).bind (fun kRand =>
      let kStar := if b then kRand else kReal
      let tH₀ := RandomOracle.ofList [((false, mStar, cStar), kReal)]
      ((OracleComp.interpret (S.h1Handler G dk cStar) (A (pk, cStar, kStar))).run tH₀).map
        Prod.fst))))) := by
  dsimp only [roIndCcaGame]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  congr 1; funext ⟨pk, dk⟩
  congr 1; funext mStar
  let dG : M → PMF R := fun _ => ProbComp.eval S.pke.sampleCoins
  have hinner : ∀ rStar : R,
      (ProbComp.eval S.sampleKey).bind (fun kReal =>
      (ProbComp.eval S.sampleKey).bind (fun kRand =>
      (ProbComp.eval ((OracleComp.interpret (S.roHandler dk (S.pke.encDet pk mStar rStar))
        (A (pk, S.pke.encDet pk mStar rStar, if b then kRand else kReal))).run
        { gCache := [(mStar, rStar)],
          hCache := [((false, mStar, S.pke.encDet pk mStar rStar), kReal)] })).bind
        fun x => PMF.pure x.fst)) =
      (pi (Function.update dG mStar (PMF.pure rStar))).bind (fun G =>
      let cStar := S.pke.encDet pk mStar rStar
      (ProbComp.eval S.sampleKey).bind (fun kReal =>
      (ProbComp.eval S.sampleKey).bind (fun kRand =>
      let kStar := if b then kRand else kReal
      let tH₀ := RandomOracle.ofList [((false, mStar, cStar), kReal)]
      ((OracleComp.interpret (S.h1Handler G dk cStar) (A (pk, cStar, kStar))).run tH₀).map
        Prod.fst))) := by
    intro rStar
    have hstep : ∀ kReal kRand : K,
        (ProbComp.eval ((OracleComp.interpret (S.roHandler dk (S.pke.encDet pk mStar rStar))
          (A (pk, S.pke.encDet pk mStar rStar, if b then kRand else kReal))).run
          { gCache := [(mStar, rStar)],
            hCache := [((false, mStar, S.pke.encDet pk mStar rStar), kReal)] })).bind
            (fun x => PMF.pure x.fst) =
        (pi (Function.update dG mStar (PMF.pure rStar))).bind (fun G =>
          ((OracleComp.interpret (S.h1Handler G dk (S.pke.encDet pk mStar rStar))
            (A (pk, S.pke.encDet pk mStar rStar, if b then kRand else kReal))).run
            (RandomOracle.ofList [((false, mStar, S.pke.encDet pk mStar rStar), kReal)])).map
              Prod.fst) := by
      intro kReal kRand
      change (ProbComp.eval _).map Prod.fst = _
      rw [eval_run_roHandler_eq_h1, complete_ofList_singleton]
    simp only [hstep]
    symm
    rw [PMF.bind_comm]
    congr 1; funext kReal
    exact PMF.bind_comm _ _ _
  simp only [hinner]
  exact bind_pi_update dG mStar _

/-- Stateless handler for `S.eagerIndCcaGame`: `G` and `H` are complete functions and
decapsulation queries for `c ≠ cStar` evaluate `S.decapsNotBot G H dk c`. -/
noncomputable def eagerHandler (S : Scheme PK SK M R CT K) (G : M → R) (H : Bool × M × CT → K)
    (dk : ImplicitSK PK SK M) (cStar : CT) (q : ROQuery M CT) : PMF (ROResp R K q) :=
  match q with
  | .G m => PMF.pure (G m)
  | .H x => PMF.pure (H x)
  | .decaps c => PMF.pure (if c = cStar then none else some (S.decapsNotBot G H dk c))

/-- Single-step simulation from `S.h1Handler` to `S.eagerHandler` via
`RandomOracle.answer_complete`. -/
theorem h1Handler_sim_eager [Fintype M] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (G : M → R) (dk : ImplicitSK PK SK M) (cStar : CT)
    (q : ROQuery M CT) (tH : RandomOracle.Cache (fun _ : Bool × M × CT => K)) :
    (do
      let (res, tH') ← S.h1Handler G dk cStar q tH
      let H ← RandomOracle.complete (fun _ : Bool × M × CT => ProbComp.eval S.sampleKey) tH'
      PMF.pure (res, H)) =
    (do
      let H ← RandomOracle.complete (fun _ : Bool × M × CT => ProbComp.eval S.sampleKey) tH
      let res ← S.eagerHandler G H dk cStar q
      PMF.pure (res, H)) := by
  let dH : Bool × M × CT → PMF K := fun _ => ProbComp.eval S.sampleKey
  simp only [Probability.PMF.monad_bind_eq_bind]
  cases q with
  | G m =>
    simp [h1Handler, eagerHandler]
  | H x =>
    dsimp only [h1Handler, eagerHandler]
    simpa only [Probability.PMF.monad_bind_eq_bind, PMF.pure_bind, PMF.map, Function.comp_def, dH]
      using RandomOracle.answer_complete dH tH x
  | decaps c =>
    dsimp only [h1Handler, eagerHandler, decapsNotBot]
    by_cases hc : c = cStar
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      cases hdec : decT S.pke G dk.pk dk.sk c with
      | none =>
        have hH := congrArg (PMF.map (fun (k, H) => (some k, H)))
          (RandomOracle.answer_complete dH tH (true, dk.fallback, c))
        simpa only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
          Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.map, dH] using hH
      | some m' =>
        have hH := congrArg (PMF.map (fun (k, H) => (some k, H)))
          (RandomOracle.answer_complete dH tH (false, m', c))
        simpa only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
          Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.map, dH] using hH

/-- Running `prog` under `S.h1Handler G dk cStar` from `tH` has the same output distribution as
completing `tH` via `RandomOracle.complete` and interpreting `prog` under `S.eagerHandler`. -/
theorem eval_run_h1Handler_eq_eager [Fintype M] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (G : M → R) (dk : ImplicitSK PK SK M) (cStar : CT)
    (prog : OracleComp (ROResp (M := M) (CT := CT) R K) Bool)
    (tH : RandomOracle.Cache (fun _ : Bool × M × CT => K)) :
    ((OracleComp.interpret (S.h1Handler G dk cStar) prog).run tH).map Prod.fst =
      (RandomOracle.complete (fun _ : Bool × M × CT => ProbComp.eval S.sampleKey) tH).bind (fun H =>
        OracleComp.interpret (S.eagerHandler G H dk cStar) prog) := by
  let h₂ : (q : ROQuery M CT) → StateT (Bool × M × CT → K) PMF (ROResp R K q) :=
    fun q H => (S.eagerHandler G H dk cStar q).map (fun res => (res, H))
  have hsim := run_interpret_simulation_fst
    (S.h1Handler G dk cStar) h₂
    (RandomOracle.complete (fun _ : Bool × M × CT => ProbComp.eval S.sampleKey))
    (fun q s => by
      simpa only [h₂, Probability.PMF.monad_bind_eq_bind, PMF.map, Function.comp_def] using
        S.h1Handler_sim_eager G dk cStar q s)
    prog tH
  rw [hsim]
  congr 1; funext H
  have hro := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_readOnly (fun q H' => S.eagerHandler G H' dk cStar q) prog H)
  change ((OracleComp.interpret h₂ prog).run H).map Prod.fst =
    ((OracleComp.interpret (fun q => S.eagerHandler G H dk cStar q) prog).map
      (fun a => (a, H))).map Prod.fst at hro
  rw [PMF.map_comp] at hro
  exact hro.trans (PMF.map_id _)

/-- **Eager/lazy equivalence for the `FO-notbot` ROM IND-CCA game**: evaluating the executable
lazy-cached game `S.roIndCcaGame A b` yields the exact same output distribution as the eager
random-oracle game `S.eagerIndCcaGame A b`. -/
theorem eval_roIndCcaGame_eq_eagerIndCcaGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp.eval (S.roIndCcaGame A b) = S.eagerIndCcaGame A b := by
  rw [eval_roIndCcaGame_eq_h1]
  simp only [eagerIndCcaGame, encapsNotBot, encapsBot, encT, Probability.PMF.monad_bind_eq_bind,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1; funext ⟨pk, dk⟩
  let dG : M → PMF R := fun _ => ProbComp.eval S.pke.sampleCoins
  let dH : Bool × M × CT → PMF K := fun _ => ProbComp.eval S.sampleKey
  have hH_step : ∀ (mStar : M) (G : M → R),
      let cStar := S.pke.encDet pk mStar (G mStar)
      (ProbComp.eval S.sampleKey).bind (fun kReal =>
      (ProbComp.eval S.sampleKey).bind (fun kRand =>
      let kStar := if b then kRand else kReal
      let tH₀ := RandomOracle.ofList [((false, mStar, cStar), kReal)]
      ((OracleComp.interpret (S.h1Handler G dk cStar) (A (pk, cStar, kStar))).run tH₀).map
        Prod.fst)) =
      (pi dH).bind (fun H =>
      (ProbComp.eval S.sampleKey).bind (fun kRand =>
      let cStar := S.pke.encDet pk mStar (G mStar)
      let kReal := H (false, mStar, cStar)
      let kStar := if b then kRand else kReal
      OracleComp.interpret (S.eagerHandler G H dk cStar) (A (pk, cStar, kStar)))) := by
    intro mStar G
    dsimp only
    set cStar := S.pke.encDet pk mStar (G mStar)
    have hinner : ∀ kReal : K,
        (ProbComp.eval S.sampleKey).bind (fun kRand =>
          ((OracleComp.interpret (S.h1Handler G dk cStar)
            (A (pk, cStar, if b then kRand else kReal))).run
            (RandomOracle.ofList [((false, mStar, cStar), kReal)])).map Prod.fst) =
        (pi (Function.update dH (false, mStar, cStar) (PMF.pure kReal))).bind (fun H =>
          (ProbComp.eval S.sampleKey).bind (fun kRand =>
            OracleComp.interpret (S.eagerHandler G H dk cStar)
              (A (pk, cStar, if b then kRand else kReal)))) := by
      intro kReal
      have hstep : ∀ kRand : K,
          ((OracleComp.interpret (S.h1Handler G dk cStar)
            (A (pk, cStar, if b then kRand else kReal))).run
            (RandomOracle.ofList [((false, mStar, cStar), kReal)])).map Prod.fst =
          (pi (Function.update dH (false, mStar, cStar) (PMF.pure kReal))).bind (fun H =>
            OracleComp.interpret (S.eagerHandler G H dk cStar)
              (A (pk, cStar, if b then kRand else kReal))) := by
        intro kRand
        rw [eval_run_h1Handler_eq_eager, complete_ofList_singleton]
      simp only [hstep]
      exact PMF.bind_comm _ _ _
    simp only [hinner]
    exact bind_pi_update dH (false, mStar, cStar) _
  simp only [hH_step]
  rw [PMF.bind_comm (ProbComp.eval S.sampleMsg)]
  congr 1; funext G
  rw [PMF.bind_comm (ProbComp.eval S.sampleMsg)]
  congr 1

/-- The ROM IND-CCA advantage of `A` against `FO-notbot` equals the distinguishing advantage
between `S.eagerIndCcaGame A false` and `S.eagerIndCcaGame A true`. -/
theorem indCcaRomAdvantage_eq_eager [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) :
    S.indCcaRomAdvantage A =
      Game.advantage (S.eagerIndCcaGame A false) (S.eagerIndCcaGame A true) := by
  simp [indCcaRomAdvantage, eval_roIndCcaGame_eq_eagerIndCcaGame]

/-! ### Section 3: Simulator Hit Probability and IND-CPA Averaging for `romCpaReduction` -/

/-- If each oracle call `q` increases a state measure `size : σ → ℕ` by at most `cost q` on every
supported transition, then any `cost`-bounded execution increases `size` by at most `n`. -/
theorem measure_le_of_isCostBounded {ι σ α : Type} {spec : ι → Type}
    (cost : ι → ℕ) (oracle : (q : ι) → StateT σ PMF (spec q)) (size : σ → ℕ)
    (hstep : ∀ q s res s', (res, s') ∈ (oracle q s).support → size s' ≤ size s + cost q)
    {prog : OracleComp spec α} {n : ℕ} (hcost : OracleComp.IsCostBounded cost prog n)
    (s : σ) (res : α) (s' : σ)
    (hmem : (res, s') ∈ ((OracleComp.interpret oracle prog).run s).support) :
    size s' ≤ size s + n := by
  induction hcost generalizing s with
  | pure a n =>
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, rfl⟩
    omega
  | liftBind q cont n _ ih =>
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨ans, s₁⟩, hans, hcont⟩ := hmem
    have h₁ := hstep q s ans s₁ hans
    have h₂ := ih ans s₁ hcont
    omega

/-- The number of keys `q : Q` present in an association list `cache` is at most `cache.length`. -/
theorem card_filter_lookup_isSome_le_length {Q V : Type} [Fintype Q] [DecidableEq Q]
    (cache : List (Q × V)) :
    (Finset.univ.filter fun q : Q => (cache.lookup q).isSome = true).card ≤ cache.length := by
  calc (Finset.univ.filter fun q : Q => (cache.lookup q).isSome = true).card
      ≤ (cache.map Prod.fst).toFinset.card := by
        apply Finset.card_le_card
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists] at hq
        obtain ⟨v, hv⟩ := hq
        obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hv
        have hmem : (q, v) ∈ cache := by simp [hlist]
        exact List.mem_toFinset.mpr (List.mem_map_of_mem hmem)
    _ ≤ (cache.map Prod.fst).length := List.toFinset_card_le _
    _ = cache.length := List.length_map Prod.fst

omit [DecidableEq CT] in
/-- A supported transition of `simHashG` adds at most one entry to `gCache`. -/
theorem simHashG_gCache_length_le (sampleCoins : ProbComp R) (m : M)
    (st : SimState M R CT K) (z : R × SimState M R CT K)
    (hz : z ∈ (ProbComp.eval (simHashG sampleCoins m st)).support) :
    z.snd.gCache.length ≤ st.gCache.length + 1 := by
  rw [simHashG, eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨r, c'⟩, hc', rfl⟩ := hz
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc' with ⟨-, hnext⟩ | ⟨-, -, hnext⟩ <;>
    · dsimp only at hnext; simp [hnext]

/-- A supported transition of `simHashHRaw` preserves `gCache`. -/
theorem simHashHRaw_gCache_eq (sampleKey : ProbComp K) (x : Bool × M × CT)
    (st : SimState M R CT K) (z : K × SimState M R CT K)
    (hz : z ∈ (ProbComp.eval (simHashHRaw sampleKey x st)).support) :
    z.snd.gCache = st.gCache := by
  rw [simHashHRaw, eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨_, _⟩, -, rfl⟩ := hz
  rfl

omit [DecidableEq M] in
/-- A supported transition of `simHashHq` preserves `gCache`. -/
theorem simHashHq_gCache_eq (sampleKey : ProbComp K) (c : CT)
    (st : SimState M R CT K) (z : K × SimState M R CT K)
    (hz : z ∈ (ProbComp.eval (simHashHq sampleKey c st)).support) :
    z.snd.gCache = st.gCache := by
  rw [simHashHq, eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨_, _⟩, -, rfl⟩ := hz
  rfl

/-- Each query `q` to `S.simHandler pk cStar` increases `gCache.length` by at most
`ROQuery.ghCost q`. -/
theorem simHandler_gCache_length_le (S : Scheme PK SK M R CT K) (pk : PK) (cStar : CT)
    (q : ROQuery M CT) (st : SimState M R CT K) (res : ROResp R K q) (st' : SimState M R CT K)
    (hmem : (res, st') ∈ (ProbComp.eval (S.simHandler pk cStar q st)).support) :
    st'.gCache.length ≤ st.gCache.length + q.ghCost := by
  cases q with
  | G m =>
    simpa only [simHandler, ROQuery.ghCost] using
      simHashG_gCache_length_le S.pke.sampleCoins m st (res, st') hmem
  | H x =>
    rcases x with ⟨isFb, m, c⟩
    cases isFb
    · dsimp only [simHandler, simHashH, ROQuery.ghCost] at hmem ⊢
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
    · dsimp only [simHandler, simHashH, ROQuery.ghCost] at hmem ⊢
      rw [simHashHRaw_gCache_eq S.sampleKey (true, m, c) st (res, st') hmem]
      exact Nat.le_add_right _ 1
  | decaps c =>
    dsimp only [simHandler, ROQuery.ghCost] at hmem ⊢
    by_cases hc : c = cStar
    · simp only [hc, ↓reduceIte] at hmem
      change (res, st') ∈ (ProbComp.eval (pure (none, st))).support at hmem
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨-, rfl⟩
      simp
    · simp only [hc, ↓reduceIte] at hmem
      change (res, st') ∈ (ProbComp.eval (simHashHq S.sampleKey c st >>= fun a =>
        pure (some a.fst, a.snd))).support at hmem
      rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
      obtain ⟨z, hz, hmem₂⟩ := hmem
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem₂
      rcases hmem₂ with ⟨-, rfl⟩
      rw [simHashHq_gCache_eq S.sampleKey c st z hz, Nat.add_zero]

omit [DecidableEq M] in
/-- If each outcome in the support of `p : PMF α` satisfies `pred x m = true` for at most `Q`
indices `m : M`, then the sum over `m : M` of `Pr_{x ← p}[pred x m = true]` is at most `Q`. -/
theorem sum_toReal_indicator_le {α : Type} [Fintype M] (p : PMF α)
    (pred : α → M → Bool) (Q : ℕ)
    (hcard : ∀ x ∈ p.support, (Finset.univ.filter fun m => pred x m = true).card ≤ Q) :
    (∑ m : M, ((p.map fun x => pred x m) true).toReal) ≤ (Q : ℝ) := by
  have hterm (m : M) :
      ((p.map fun x => pred x m) true).toReal =
        ∑' x : α, (p x).toReal * if pred x m = true then 1 else 0 := by
    simp only [PMF.map, Function.comp_def, Probability.PMF.bind_apply_toReal_tsum]
    refine tsum_congr fun x => ?_
    cases pred x m <;> simp
  simp_rw [hterm]
  have hsumm (m : M) :
      Summable (fun x : α => (p x).toReal * if pred x m = true then (1 : ℝ) else 0) := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) (Probability.PMF.summable_toReal p)
    · positivity
    · by_cases hx : pred x m = true <;> simp [hx, ENNReal.toReal_nonneg]
  rw [← Summable.tsum_finsetSum (fun m _ => hsumm m)]
  calc ∑' x : α, ∑ m : M, ((p x).toReal * if pred x m = true then (1 : ℝ) else 0)
      ≤ ∑' x : α, (p x).toReal * (Q : ℝ) := by
        refine Summable.tsum_le_tsum (fun x => ?_)
          (summable_sum fun m _ => hsumm m) ((Probability.PMF.summable_toReal p).mul_right (Q : ℝ))
        rw [← Finset.mul_sum]
        by_cases hx : x ∈ p.support
        · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          rw [Finset.sum_boole]
          exact_mod_cast hcard x hx
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hx, ENNReal.toReal_zero, zero_mul, zero_mul]
    _ = (Q : ℝ) := by
        rw [tsum_mul_right, Probability.PMF.tsum_toReal, one_mul]

omit [DecidableEq M] in
/-- If each row of an `|M| × |M|` matrix sums to at most `Q` and `2 ≤ |M|`, some off-diagonal pair
`(m₀, m₁)` bounds the diagonal average by `|p m₀ m₁ - p m₁ m₁| + Q / |M|`. -/
theorem avg_pair_abs [Fintype M] (hM : 2 ≤ Fintype.card M)
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

/-- Probability that `S.romCpaReduction A m₀ m₁` records `m₁` in `gCache` when challenged on an
encryption of `m₀` in `S.pke.indCpaGame`. -/
noncomputable def simHitProb (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (m₀ m₁ : M) : ℝ :=
  ((ProbComp.eval (S.pke.indCpaGame m₀ m₁ false (S.romCpaReduction A m₀ m₁))) true).toReal

/-- **IND-CPA advantage characterization for `romCpaReduction`**: the fixed-message IND-CPA
advantage of `S.romCpaReduction A m₀ m₁` on `(m₀, m₁)` equals the absolute difference between
the simulator `G`-query hit probabilities on `m₁` under challenge encryptions of `m₀` and `m₁`. -/
theorem indCpaAdvantage_romCpaReduction (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (m₀ m₁ : M) :
    (S.pke.indCpaAdvantage m₀ m₁ (S.romCpaReduction A m₀ m₁) : ℝ) =
      |S.simHitProb A m₀ m₁ - S.simHitProb A m₁ m₁| := by
  have htrue : S.pke.indCpaGame m₀ m₁ true (S.romCpaReduction A m₀ m₁) =
      S.pke.indCpaGame m₁ m₁ false (S.romCpaReduction A m₁ m₁) := rfl
  simp only [ExplicitCoinPKE.indCpaAdvantage, Game.coe_advantage,
    Game.coe_succProbability, simHitProb, htrue]

/-- **Query-count row bound on simulator hit probabilities**: for any adversary `A` satisfying
`ROQueryBounds A qG qH` and any challenge message `m₀`, the sum over all target messages `m₁ : M`
of `S.simHitProb A m₀ m₁` is at most `qG + qH`. -/
theorem sum_simHitProb_le [Fintype M] (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) {qG qH : ℕ} (hq : ROQueryBounds A qG qH) (m₀ : M) :
    ∑ m₁ : M, S.simHitProb A m₀ m₁ ≤ (qG : ℝ) + (qH : ℝ) := by
  let runDist : PMF (Bool × SimState M R CT K) :=
    (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
    (ProbComp.eval S.sampleKey).bind fun kStar =>
      let cStar := S.pke.encDet keys.fst m₀ rStar
      (OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
        (fun q st => ProbComp.eval (S.simHandler keys.fst cStar q st))
        (A (keys.fst, cStar, kStar))).run {}
  have heq (m₁ : M) :
      ProbComp.eval (S.pke.indCpaGame m₀ m₁ false (S.romCpaReduction A m₀ m₁)) =
        runDist.map fun p => (p.snd.gCache.lookup m₁).isSome := by
    simp only [ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt, romCpaReduction,
      Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      eval_run_interpret, runDist, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  have hcard : ∀ x ∈ runDist.support,
      (Finset.univ.filter fun m => (x.snd.gCache.lookup m).isSome = true).card ≤ qG + qH := by
    intro x hx
    simp only [runDist, PMF.mem_support_bind_iff] at hx
    obtain ⟨keys, -, rStar, -, kStar, -, hrun⟩ := hx
    set pk := keys.fst
    set cStar := S.pke.encDet pk m₀ rStar
    have hcost : OracleComp.IsCostBounded ROQuery.ghCost (A (pk, cStar, kStar)) (qG + qH) := by
      have ⟨hG, hH⟩ := hq (pk, cStar, kStar)
      convert OracleComp.IsCostBounded.add hG hH using 1
      funext q; cases q <;> rfl
    have hlen := measure_le_of_isCostBounded ROQuery.ghCost
      (fun q st => ProbComp.eval (S.simHandler pk cStar q st))
      (fun st : SimState M R CT K => st.gCache.length)
      (S.simHandler_gCache_length_le pk cStar)
      hcost {} x.fst x.snd hrun
    exact (card_filter_lookup_isSome_le_length x.snd.gCache).trans (by simpa using hlen)
  calc ∑ m₁ : M, S.simHitProb A m₀ m₁
      = ∑ m₁ : M, ((runDist.map fun p => (p.snd.gCache.lookup m₁).isSome) true).toReal := by
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [simHitProb, heq m₁]
    _ ≤ ((qG + qH : ℕ) : ℝ) := sum_toReal_indicator_le runDist _ (qG + qH) hcard
    _ = (qG : ℝ) + (qH : ℝ) := Nat.cast_add qG qH

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
          ((qG : ℝ) + (qH : ℝ)) / (Fintype.card M : ℝ) := by
  obtain ⟨m₀, m₁, hne, hpair⟩ :=
    avg_pair_abs hM (S.simHitProb A) ((qG : ℝ) + (qH : ℝ)) (S.sum_simHitProb_le A hq)
  refine ⟨m₀, m₁, hne, ?_⟩
  rwa [S.indCpaAdvantage_romCpaReduction A m₀ m₁]

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto

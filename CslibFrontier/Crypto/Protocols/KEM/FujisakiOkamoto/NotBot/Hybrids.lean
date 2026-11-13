/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security

/-!
# Hybrid games for the ROM IND-CCA security of `FO-notbot`

This module fixes the intermediate games of the IND-CCA proof for the domain-separated
implicit-rejection transform `FO-notbot = U-notbot ∘ T` of [HofheinzHoevelmannsKiltz2017]
(IACR ePrint 2017/604, full version dated 2 November 2021, §3.1 and §3.2.2). The proof follows
the structure of the paper's proofs of the §3.1 theorem for `T` (OW-PCA case, with the
correctness hop that replaces `G` by good coins) and the §3.2.2 IND-CCA theorem for `U-notbot`,
composed directly rather than through an OW-PCA interface.

Starting from the eager game `Scheme.eagerIndCcaGame` of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security`, the hybrids are:

1. `Scheme.eagerFbGame`: decapsulation of invalid ciphertexts uses an independent table
   `Hfb : CT → K` instead of `H(true, s, ·)` for the secret seed `s`.
2. `Scheme.eagerCoupledGame`: the oracles are computed from independent tables
   `G`, `Hq : CT → K` and `Hraw : Bool × M × CT → K`; a key-derivation query `H(false, m, c)` reads
   `Hq c` exactly when `c = Enc(pk, m; G(m))` and `Dec(sk, c) = some m`
   (`Scheme.coupledH`), and every decapsulation query `c ≠ c*` reads `Hq c`.
3. `Scheme.coupledGame`: the lazy-sampling realization of `eagerCoupledGame` on `SimState`.
4. `Scheme.simGame`: the keyless simulator `Scheme.simHandler`, which drops the decryption test
   `Dec(sk, c) = some m` from `coupledH`. The two lazy games agree until a sampled coin `G(m)` is a
   decryption failure for `m`.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerFbHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerFbGame`: eager game with decoupled
  implicit-rejection keys.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.coupledH`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerCoupledHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerCoupledGame`: eager coupled game.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.coupledHashH`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.coupledHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.coupledGame`: lazy coupled game.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simGame`: lazy keyless simulator game with the
  challenge coin `G(m*)` programmed.

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

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-! ### Decoupled implicit rejection -/

/-- Stateless oracle of `eagerFbGame`: as `eagerHandler`, except that a decapsulation query
`c ≠ cStar` that `decT` rejects is answered by an independent table `Hfb c` rather than by
`H(true, dk.fallback, c)`. -/
noncomputable def eagerFbHandler (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (Hfb : CT → K) (dk : ImplicitSK PK SK M) (cStar : CT)
    (q : ROQuery M CT) : PMF (ROResp R K q) :=
  ROQuery.dispatch (PMF.pure ∘ G) (PMF.pure ∘ H)
    (fun c =>
      PMF.pure
        (some
          (match decT S.pke G dk.pk dk.sk c with
          | some m' => H (false, m', c)
          | none => Hfb c)))
    cStar q

/-- The eager IND-CCA game of `FO-notbot` with implicit-rejection keys drawn from an independent
table `Hfb : CT → K` instead of `H(true, s, ·)`. -/
noncomputable def eagerFbGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, dk) ← ProbComp.eval S.keyGenNotBot
  let G ← pi (α := fun _ : M => R) (fun _ => ProbComp.eval S.pke.sampleCoins)
  let H ← pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let Hfb ← pi (α := fun _ : CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let (cStar, kReal) ← ProbComp.eval (S.encapsNotBot G H pk)
  let kRand ← ProbComp.eval S.sampleKey
  OracleComp.interpret (S.eagerFbHandler G H Hfb dk cStar)
    (A ⟨pk, cStar, if b then kRand else kReal⟩)

/-! ### Eager coupled game -/

/-- Coupled key-derivation oracle: `H(false, m, c)` reads the ciphertext table `Hq c` when
`c = Enc(pk, m; G(m))` and `Dec(sk, c) = some m`, and the raw table `Hraw` otherwise. -/
def coupledH (S : Scheme PK SK M R CT K) (G : M → R) (Hq : CT → K) (Hraw : Bool × M × CT → K)
    (pk : PK) (sk : SK) : Bool × M × CT → K
  | (false, m, c) =>
    if S.pke.encDet pk m (G m) = c ∧ S.pke.dec sk c = some m then Hq c else Hraw (false, m, c)
  | (true, m, c) => Hraw (true, m, c)

/-- Stateless oracle of `eagerCoupledGame`: `G` reads `G`, `H` reads `coupledH`, and every
decapsulation query `c ≠ cStar` reads `Hq c`. -/
noncomputable def eagerCoupledHandler (S : Scheme PK SK M R CT K) (G : M → R) (Hq : CT → K)
    (Hraw : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT) (q : ROQuery M CT) :
    PMF (ROResp R K q) :=
  ROQuery.dispatch (PMF.pure ∘ G) (PMF.pure ∘ S.coupledH G Hq Hraw pk sk)
    (fun c => PMF.pure (some (Hq c))) cStar q

/-- The eager coupled game: independent tables `G`, `Hq`, `Hraw`, challenge
`c* = Enc(pk, m*; G(m*))` with real key `coupledH (false, m*, c*)`. -/
noncomputable def eagerCoupledGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, sk) ← ProbComp.eval S.pke.keyGen
  let G ← pi (α := fun _ : M => R) (fun _ => ProbComp.eval S.pke.sampleCoins)
  let Hq ← pi (α := fun _ : CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let Hraw ← pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let mStar ← ProbComp.eval S.sampleMsg
  let cStar := encT S.pke G pk mStar
  let kRand ← ProbComp.eval S.sampleKey
  let kReal := S.coupledH G Hq Hraw pk sk (false, mStar, cStar)
  OracleComp.interpret (S.eagerCoupledHandler G Hq Hraw pk sk cStar)
    (A ⟨pk, cStar, if b then kRand else kReal⟩)

/-! ### Lazy coupled and simulator games -/

/-- Lazy realization of `coupledH` on `SimState`: `G` on `gCache`, `Hq` on `hqCache` and `Hraw`
on `hCache`. It differs from `simHashH` only in the decryption test `Dec(sk, c) = some m`. -/
def coupledHashH (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (x : Bool × M × CT) : StateT (SimState M R CT K) ProbComp K :=
  match x with
  | (false, m, c) => do
    let r ← simHashG S.pke.sampleCoins m
    if S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m then
      simHashHq S.sampleKey c
    else
      simHashHRaw S.sampleKey (false, m, c)
  | (true, m, c) =>
    simHashHRaw S.sampleKey (true, m, c)

omit [DecidableEq M] in
/-- The filtered decapsulation branch shared by `simFilterHandler` and `coupledFilterHandler`
leaves `gCache` unchanged. -/
theorem gCache_eq_of_mem_support_filterDecaps (sampleKey : ProbComp K)
    (d : List (M × R) → CT → Bool) (cStar c : CT)
    (st : SimState M R CT K) (x : Option K × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval ((if c = cStar then return none else
      filterDecaps (simHashHq sampleKey) d c : StateT (SimState M R CT K) ProbComp (Option K))
        st)).support) :
    x.2.gCache = st.gCache := by
  by_cases hc : c = cStar
  · simp only [hc, ↓reduceIte] at hx
    change x ∈ (ProbComp.eval (pure (none, st))).support at hx
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx
    rw [hx]
  · simp only [hc, ↓reduceIte] at hx
    cases hd : d st.gCache c
    · simp only [filterDecaps, hd, Bool.cond_false] at hx
      change x ∈ (ProbComp.eval (pure (none, st))).support at hx
      rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx
      rw [hx]
    · simp only [filterDecaps, hd, Bool.cond_true] at hx
      change x ∈ (ProbComp.eval (simHashHq sampleKey c st >>= fun a =>
        pure (some a.fst, a.snd))).support at hx
      rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hx
      obtain ⟨z, hz, hx⟩ := hx
      rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx
      rw [hx]
      exact simHashHq_gCache_eq _ _ _ _ hz

omit [DecidableEq M] in
/-- The decapsulation branch shared by `simHandler` and `coupledHandler` leaves `gCache`
unchanged. -/
theorem gCache_eq_of_mem_support_decaps (sampleKey : ProbComp K) (cStar c : CT)
    (st : SimState M R CT K) (x : Option K × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval ((if c = cStar then return none else do
      let k ← simHashHq sampleKey c
      return some k : StateT (SimState M R CT K) ProbComp (Option K)) st)).support) :
    x.2.gCache = st.gCache :=
  gCache_eq_of_mem_support_filterDecaps sampleKey (fun _ _ => true) cStar c st x hx

/-- Lazy coupled handler parameterized by a decapsulation filter `d : List (M × R) → CT → Bool`;
it differs from `simFilterHandler` only in using `coupledHashH` for `H`. -/
def coupledFilterHandler (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (pk : PK) (sk : SK) (cStar : CT)
    (q : ROQuery M CT) : StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  S.simFilterDispatch (S.coupledHashH pk sk) d cStar q

/-- Lazy realization of `eagerCoupledHandler` on `SimState`; it differs from `simHandler` only
in using `coupledHashH` for `H`. -/
def coupledHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT)
    (q : ROQuery M CT) : StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  S.coupledFilterHandler (fun _ _ => true) pk sk cStar q

/-- Lazy coupled game parameterized by a decapsulation filter
`d : PK → SK → List (M × R) → CT → Bool`. -/
def coupledFilterGame (S : Scheme PK SK M R CT K) (d : PK → SK → List (M × R) → CT → Bool)
    (A : ROAdversary PK M R CT K) (b : Bool) : ProbComp Bool := do
  let (pk, sk) ← S.pke.keyGen
  let mStar ← S.sampleMsg
  let rStar ← S.pke.sampleCoins
  let cStar := S.pke.encDet pk mStar rStar
  let (kReal, st₀) ← (S.coupledHashH pk sk (false, mStar, cStar)).run
    { gCache := [(mStar, rStar)] }
  let kRand ← S.sampleKey
  let (guess, _) ← (OracleComp.interpret (S.coupledFilterHandler (d pk sk) pk sk cStar)
    (A ⟨pk, cStar, if b then kRand else kReal⟩)).run st₀
  return guess

/-- The lazy coupled game: `G(m*)` is programmed to fresh challenge coins `r*` and the real key
is the answer of `coupledHashH` to `(false, m*, c*)`. -/
def coupledGame (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp Bool :=
  S.coupledFilterGame (fun _ _ _ _ => true) A b

/-- Lazy keyless simulator game parameterized by a decapsulation filter
`d : PK → List (M × R) → CT → Bool`. -/
def simFilterGame (S : Scheme PK SK M R CT K) (d : PK → List (M × R) → CT → Bool)
    (A : ROAdversary PK M R CT K) (b : Bool) : ProbComp Bool := do
  let (pk, _) ← S.pke.keyGen
  let mStar ← S.sampleMsg
  let rStar ← S.pke.sampleCoins
  let cStar := S.pke.encDet pk mStar rStar
  let (kReal, st₀) ← (S.simHashH pk (false, mStar, cStar)).run
    { gCache := [(mStar, rStar)] }
  let kRand ← S.sampleKey
  let (guess, _) ← (OracleComp.interpret (S.simFilterHandler (d pk) pk cStar)
    (A ⟨pk, cStar, if b then kRand else kReal⟩)).run st₀
  return guess

/-- The lazy keyless simulator game: as `coupledGame` with `simHashH` and `simHandler`, which do
not use the secret key. -/
def simGame (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp Bool :=
  S.simFilterGame (fun _ _ _ => true) A b

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto

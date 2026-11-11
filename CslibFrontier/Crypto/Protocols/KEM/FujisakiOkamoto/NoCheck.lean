/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security

/-!
# The re-encryption check of `FO-notbot` is load-bearing

`FO-notbot` decapsulates `c` to `H(false, m', c)` only if `m' = Dec(sk, c)` passes the
re-encryption check `Enc(pk, m'; G(m')) = c` of `T` ([HofheinzHoevelmannsKiltz2017], IACR ePrint
2017/604, full version dated 2 November 2021, §3.1 Fig. 5 and §3.2.2 Fig. 12). This module shows
that the check cannot be dropped.

For any explicit-coin PKE `P` with messages `Fin n → Bool`, `leakyPKE P` appends a tag
`Option (Fin n)` to ciphertexts. Honest ciphertexts carry `none` and decrypt as in `P`, while
`Dec(sk, (c, some i))` returns the constant message with value `m i`, where `m = Dec(sk, c)`. The
encryption algorithm, and hence the IND-CPA experiment, is unchanged
(`leakyPKE_indCpaAdvantage`), and so are `δ`-correctness and `γ`-spreadness
(`leakyPKE_deltaCorrect`, `leakyPKE_gammaSpread`). With the check, `Scheme.indCcaRomAdvantage_le`
therefore applies to `leakyPKE P` with the hypotheses of `P`: a tagged ciphertext `(c, some i)` is
never an encryption of anything, so decapsulation rejects it.

Without the check (`Scheme.decapsNoCheck`, `Scheme.eagerNoCheckGame`), the adversary `leakAdv`
recovers the challenge message bit by bit: it compares the decapsulation of `(c*, some i)` with
`H(false, 1, (c*, some i))`, where `1` is the all-`true` message, and then recomputes
`H(false, m*, c*)`. For a perfectly correct `P` and uniform keys its advantage is at least
`1 - (n + 1) / |K|` (`advantage_eagerNoCheckGame_leakAdv`), using `n` decapsulation queries and
`n + 1` queries to `H`.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.leakyPKE`: the bit-leaking variant of a PKE.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsNoCheck`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerNoCheckGame`: `FO-notbot` decapsulation
  without the re-encryption check, and its eager ROM IND-CCA game.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.leakAdv`: the bit-recovery adversary.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.leakyPKE_indCpaAdvantage`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.leakyPKE_deltaCorrect`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.leakyPKE_gammaSpread`: `leakyPKE P` has the IND-CPA
  advantages, correctness and spreadness of `P`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.advantage_eagerNoCheckGame_leakAdv`: without the
  re-encryption check, `leakAdv` breaks IND-CCA security of `FO-notbot` over `leakyPKE P`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

/-! ### The bit-leaking PKE -/

section Leaky

variable {n : ℕ}

/-- The bit-leaking variant of `P`: ciphertexts carry a tag `Option (Fin n)`; honest encryptions
carry `none`, and `Dec(sk, (c, some i))` is the constant message with value `m i` for
`m = Dec(sk, c)`. -/
@[expose] def leakyPKE (P : ExplicitCoinPKE PK SK (Fin n → Bool) R CT) :
    ExplicitCoinPKE PK SK (Fin n → Bool) R (CT × Option (Fin n)) where
  keyGen := P.keyGen
  sampleCoins := P.sampleCoins
  encDet pk m r := (P.encDet pk m r, none)
  dec sk c :=
    match c.2 with
    | none => P.dec sk c.1
    | some i => (P.dec sk c.1).map fun m _ => m i

/-- `leakyPKE P` has the IND-CPA advantages of `P`: an adversary against `leakyPKE P` is an
adversary against `P` that appends the tag `none`. -/
theorem leakyPKE_indCpaAdvantage (P : ExplicitCoinPKE PK SK (Fin n → Bool) R CT)
    (m₀ m₁ : Fin n → Bool) (A : PK → CT × Option (Fin n) → ProbComp Bool) :
    (leakyPKE P).indCpaAdvantage m₀ m₁ A =
      P.indCpaAdvantage m₀ m₁ fun pk c => A pk (c, none) := by
  simp [ExplicitCoinPKE.indCpaAdvantage, ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt,
    leakyPKE]

/-- `leakyPKE P` is `δ`-correct whenever `P` is. -/
theorem leakyPKE_deltaCorrect (P : ExplicitCoinPKE PK SK (Fin n → Bool) R CT) {δ : ℝ}
    (h : P.DeltaCorrect δ) : (leakyPKE P).DeltaCorrect δ :=
  h

/-- `leakyPKE P` is `γ`-spread whenever `P` is. -/
theorem leakyPKE_gammaSpread (P : ExplicitCoinPKE PK SK (Fin n → Bool) R CT) {γ : ℝ}
    (h : P.GammaSpread γ) : (leakyPKE P).GammaSpread γ := by
  intro pk sk hkeys m c
  refine le_trans (ENNReal.toReal_mono ?_ ?_) (h pk sk hkeys m c.1)
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_le_one _ _)
  · refine (ProbComp.eval P.sampleCoins).toOuterMeasure.mono fun r hr => ?_
    simp only [leakyPKE, Set.mem_ofPred_eq] at hr ⊢
    rw [← hr]

end Leaky

/-! ### Decapsulation without the re-encryption check -/

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- `FO-notbot` decapsulation without the re-encryption check: `H(false, m', c)` whenever
`Dec(sk, c) = some m'`, and the implicit-rejection key `H(true, s, c)` otherwise. -/
def decapsNoCheck (S : Scheme PK SK M R CT K) (H : Bool × M × CT → K)
    (dk : ImplicitSK PK SK M) (c : CT) : K :=
  match S.pke.dec dk.sk c with
  | some m' => H (false, m', c)
  | none => H (true, dk.fallback, c)

/-- The eager ROM IND-CCA game of `FO-notbot` with decapsulation `decapsNoCheck`; otherwise as
`eagerIndCcaGame`. -/
noncomputable def eagerNoCheckGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, dk) ← ProbComp.eval S.keyGenNotBot
  let G ← pi (α := fun _ : M => R) (fun _ => ProbComp.eval S.pke.sampleCoins)
  let H ← pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let (cStar, kReal) ← ProbComp.eval (S.encapsNotBot G H pk)
  let kRand ← ProbComp.eval S.sampleKey
  OracleComp.interpret (fun (q : ROQuery M CT) => match q with
    | .G m => PMF.pure (G m)
    | .H x => PMF.pure (H x)
    | .decaps c => PMF.pure (if c = cStar then none else some (S.decapsNoCheck H dk c)))
    (A (pk, cStar, if b then kRand else kReal))

end Scheme

/-! ### The bit-recovery adversary -/

section Attack

variable {n : ℕ}

/-- Query, for each index `i` in `is`, the decapsulation of `(c, some i)` and the key
`H(false, 1, (c, some i))`, and record whether they agree. -/
def leakBits [DecidableEq K] (c : CT) :
    List (Fin n) → OracleComp (ROResp (M := Fin n → Bool) (CT := CT × Option (Fin n)) R K)
      (List (Fin n × Bool))
  | [] => pure []
  | i :: is => do
    let d ← OracleComp.query (ROQuery.decaps (c, some i))
    let h ← OracleComp.query (ROQuery.H (false, fun _ => true, (c, some i)))
    let rest ← leakBits c is
    return (i, decide (d = some h)) :: rest

/-- The bit-recovery adversary: it reads off a candidate message `m̂` bit by bit with
`leakBits`, then outputs whether `H(false, m̂, c*)` equals the challenge key. -/
def leakAdv [DecidableEq K] : ROAdversary PK (Fin n → Bool) R (CT × Option (Fin n)) K :=
  fun (_, cStar, kStar) => do
    let bits ← leakBits (R := R) (K := K) cStar.1 (List.finRange n)
    let k ← OracleComp.query (ROQuery.H (false, fun i => (bits.lookup i).getD false, cStar))
    return decide (k = kStar)

end Attack

end Cslib.Crypto.Protocols.FujisakiOkamoto

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Product

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
(`leakyPKE_deltaCorrect`, `leakyPKE_gammaSpread`). With the re-encryption check in place, a tagged
ciphertext `(c, some i)` is never an encryption of any message (`encT_leakyPKE`), so `decT`
rejects it and `Scheme.decapsNotBot` outputs the fallback key `H(true, dk.fallback, (c, some i))`
(`decapsNotBot_leakyPKE_some`).

Without the check (`Scheme.decapsNoCheck`, `Scheme.eagerNoCheckGame`), the adversary `leakAdv`
recovers the challenge message bit by bit: it compares the decapsulation of `(c*, some i)` with
`H(false, 1, (c*, some i))`, where `1` is the all-`true` message, and then recomputes
`H(false, m*, c*)`. For a perfectly correct `P` and uniform keys its advantage is at least
`1 - (n + 1) / |K|` (`advantage_eagerNoCheckGame_leakAdv`), using `n` decapsulation queries and
`n + 1` queries to `H` (`roQueryBounds_leakAdv`). The eager oracles are deterministic, so the
adversary's run is a function of `H` (`interpret_leakAdv`): bit `i` of the guess `leakGuess` is
wrong only if `m* i = false` and `H` collides on the two constant messages at `(c*, some i)`.
A union bound over these `n` collisions shows that `leakAdv` rejects the real key with
probability at most `n / |K|`; it accepts the random key, which is independent of the guess, with
probability `1 / |K|`.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.leakyPKE`: the bit-leaking variant of a PKE.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsNoCheck`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerNoCheckOracle`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerNoCheckGame`: `FO-notbot` decapsulation
  without the re-encryption check, its eager oracles, and its eager ROM IND-CCA game.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.leakAdv`: the bit-recovery adversary, and
  `Cslib.Crypto.Protocols.FujisakiOkamoto.leakGuess`: the message it reads off.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.leakyPKE_indCpaAdvantage`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.leakyPKE_deltaCorrect`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.leakyPKE_gammaSpread`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.decapsNotBot_leakyPKE_some`: `leakyPKE P` preserves the
  IND-CPA advantages, correctness, and spreadness of `P`, and `Scheme.decapsNotBot` rejects tagged
  ciphertexts `(c, some i)` via the re-encryption check.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.advantage_eagerNoCheckGame_leakAdv`: without the
  re-encryption check, `leakAdv` breaks IND-CCA security of `FO-notbot` over `leakyPKE P`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.roQueryBounds_leakAdv`: `leakAdv` makes no `G` queries
  and `n + 1` queries to `H`.

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

/-- Honest encryptions of `leakyPKE P` carry the tag `none`. -/
@[simp] theorem encT_leakyPKE (P : ExplicitCoinPKE PK SK (Fin n → Bool) R CT)
    (G : (Fin n → Bool) → R) (pk : PK) (m : Fin n → Bool) :
    encT (leakyPKE P) G pk m = (P.encDet pk m (G m), none) :=
  rfl

/-- If `c` decrypts to `m` under `P`, then `(c, some i)` decrypts under `leakyPKE P` to the
constant message with value `m i`. -/
theorem leakyPKE_dec_some {P : ExplicitCoinPKE PK SK (Fin n → Bool) R CT} {sk : SK} {c : CT}
    {m : Fin n → Bool} (h : P.dec sk c = some m) (i : Fin n) :
    (leakyPKE P).dec sk (c, some i) = some fun _ => m i := by
  simp [leakyPKE, h]

/-- With the re-encryption check of `T`, `Scheme.decapsNotBot` over `leakyPKE P` rejects every
tagged ciphertext `(c, some i)` and returns the fallback key `H(true, dk.fallback, (c, some i))`. -/
theorem decapsNotBot_leakyPKE_some [DecidableEq CT]
    (P : ExplicitCoinPKE PK SK (Fin n → Bool) R CT)
    (sampleMsg : ProbComp (Fin n → Bool)) (sampleKey : ProbComp K)
    (G : (Fin n → Bool) → R)
    (H : Bool × (Fin n → Bool) × (CT × Option (Fin n)) → K)
    (dk : ImplicitSK PK SK (Fin n → Bool)) (c : CT) (i : Fin n) :
    (⟨leakyPKE P, sampleMsg, sampleKey⟩ :
      Scheme PK SK (Fin n → Bool) R (CT × Option (Fin n)) K).decapsNotBot G H dk (c, some i) =
      H (true, dk.fallback, (c, some i)) :=
  Scheme.decapsNotBot_of_reencrypt_ne _ G H dk (c, some i) fun _ _ henc => by
    simpa [encT_leakyPKE] using congrArg Prod.snd henc

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

omit [DecidableEq M] [DecidableEq CT] in
/-- Without the check, a ciphertext that decrypts to `m'` decapsulates to `H(false, m', c)`. -/
theorem decapsNoCheck_of_dec_eq_some (S : Scheme PK SK M R CT K) (H : Bool × M × CT → K)
    (dk : ImplicitSK PK SK M) {c : CT} {m' : M} (h : S.pke.dec dk.sk c = some m') :
    S.decapsNoCheck H dk c = H (false, m', c) := by
  simp [decapsNoCheck, h]

/-- The eager oracles of `eagerNoCheckGame` for fixed random functions `G` and `H`, secret key
`dk` and challenge ciphertext `cStar`: decapsulation queries use `decapsNoCheck` and reject
`cStar`. -/
noncomputable def eagerNoCheckOracle (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (cStar : CT) (q : ROQuery M CT) :
    PMF (ROResp R K q) :=
  ROQuery.dispatch (PMF.pure ∘ G) (PMF.pure ∘ H) (fun c => PMF.pure (some (S.decapsNoCheck H dk c)))
    cStar q

/-- The eager ROM IND-CCA game of `FO-notbot` with decapsulation `decapsNoCheck`; otherwise as
`eagerIndCcaGame`. -/
noncomputable def eagerNoCheckGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, dk) ← ProbComp.eval S.keyGenNotBot
  let G ← S.coinTable
  let H ← S.keyTable (Bool × M × CT)
  let (cStar, kReal) ← ProbComp.eval (S.encapsNotBot G H pk)
  let kRand ← ProbComp.eval S.sampleKey
  OracleComp.interpret (S.eagerNoCheckOracle G H dk cStar)
    (A ⟨pk, cStar, if b then kRand else kReal⟩)

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
  fun ch => do
    let bits ← leakBits (R := R) (K := K) ch.ct.1 (List.finRange n)
    let k ← OracleComp.query (ROQuery.H (false, fun i => (bits.lookup i).getD false, ch.ct))
    return decide (k = ch.key)

variable [DecidableEq K]

/-- `leakBits` costs `k` per index when each `H` query costs `k` and decapsulation queries are
free. -/
theorem isCostBounded_leakBits (cost : ROQuery (Fin n → Bool) (CT × Option (Fin n)) → ℕ)
    (k : ℕ) (hd : ∀ x, cost (.decaps x) = 0) (hH : ∀ x, cost (.H x) = k) (c : CT) :
    ∀ l : List (Fin n),
      OracleComp.IsCostBounded cost (leakBits (R := R) (K := K) c l) (l.length * k)
  | [] => .pure _ _
  | i :: l => by
    refine ((OracleComp.IsCostBounded.query _).bind fun _ =>
      (OracleComp.IsCostBounded.query _).bind fun _ =>
        (isCostBounded_leakBits cost k hd hH c l).bind fun _ => .pure _ 0).mono ?_
    simp only [hd, hH, List.length_cons, Nat.succ_mul]
    omega

/-- `leakAdv` makes no `G` queries and `n + 1` queries to `H`. -/
theorem roQueryBounds_leakAdv :
    ROQueryBounds (leakAdv (PK := PK) (R := R) (CT := CT) (K := K) (n := n)) 0 (n + 1) := by
  have h (cost : ROQuery (Fin n → Bool) (CT × Option (Fin n)) → ℕ) (k : ℕ)
      (hd : ∀ x, cost (.decaps x) = 0) (hH : ∀ x, cost (.H x) = k)
      (ch : KEM.Challenge PK (CT × Option (Fin n)) K) :
      OracleComp.IsCostBounded cost (leakAdv (R := R) ch) (n * k + k) := by
    dsimp only [leakAdv]
    refine OracleComp.IsCostBounded.bind ?_ fun bits => ?_
    · simpa using
        isCostBounded_leakBits (R := R) (K := K) cost k hd hH ch.ct.1 (List.finRange n)
    · exact ((OracleComp.IsCostBounded.query _).bind fun _ => .pure _ 0).mono (by simp [hH])
  intro ch
  exact ⟨by simpa using h ROQuery.gCost 0 (fun _ => rfl) (fun _ => rfl) ch,
    by simpa using h ROQuery.hCost 1 (fun _ => rfl) (fun _ => rfl) ch⟩

/-- The candidate message that `leakAdv` reads off for the challenge `(c, none)` when `c`
decrypts to `m`: bit `i` is read as `true` iff `H(false, m i, (c, some i))` agrees with
`H(false, 1, (c, some i))`, writing `m i` and `1` for constant messages. -/
def leakGuess (H : Bool × (Fin n → Bool) × (CT × Option (Fin n)) → K)
    (m : Fin n → Bool) (c : CT) (i : Fin n) : Bool :=
  decide (H (false, fun _ => m i, (c, some i)) = H (false, fun _ => true, (c, some i)))

variable [DecidableEq CT]

/-- With eager oracles, `leakBits` deterministically returns the bits of `leakGuess`. -/
theorem interpret_leakBits (S : Scheme PK SK (Fin n → Bool) R (CT × Option (Fin n)) K)
    (G : (Fin n → Bool) → R) (H : Bool × (Fin n → Bool) × (CT × Option (Fin n)) → K)
    (dk : ImplicitSK PK SK (Fin n → Bool)) (c : CT) (m : Fin n → Bool)
    (hdec : ∀ i, S.pke.dec dk.sk (c, some i) = some fun _ => m i) :
    ∀ l : List (Fin n), OracleComp.interpret (S.eagerNoCheckOracle G H dk (c, none))
      (leakBits (R := R) c l) = PMF.pure (l.map fun i => (i, leakGuess H m c i))
  | [] => by simp [leakBits]
  | i :: l => by
    simp [leakBits, interpret_leakBits S G H dk c m hdec l, Scheme.eagerNoCheckOracle,
      Scheme.decapsNoCheck_of_dec_eq_some S H dk (hdec i), leakGuess]

/-- With eager oracles, `leakAdv` deterministically compares `H(false, m̂, c*)` with the
challenge key, where `m̂` is `leakGuess`. -/
theorem interpret_leakAdv (S : Scheme PK SK (Fin n → Bool) R (CT × Option (Fin n)) K)
    (G : (Fin n → Bool) → R) (H : Bool × (Fin n → Bool) × (CT × Option (Fin n)) → K)
    (dk : ImplicitSK PK SK (Fin n → Bool)) (c : CT) (m : Fin n → Bool)
    (hdec : ∀ i, S.pke.dec dk.sk (c, some i) = some fun _ => m i) (pk : PK) (k : K) :
    OracleComp.interpret (S.eagerNoCheckOracle G H dk (c, none)) (leakAdv ⟨pk, (c, none), k⟩) =
      PMF.pure (decide (H (false, leakGuess H m c, (c, none)) = k)) := by
  have hguess : (fun i => ((List.finRange n).map fun i => (i, leakGuess H m c i)).lookup i
      |>.getD false) = leakGuess H m c :=
    funext fun i => by rw [List.lookup_graph _ (List.mem_finRange i)]; rfl
  simp [leakAdv, interpret_leakBits S G H dk c m hdec, Scheme.eagerNoCheckOracle, hguess]

/-- Two distinct coordinates of a uniform random function collide with probability
`1 / |γ|`. -/
private theorem pi_toOuterMeasure_eq {ι γ : Type} [Fintype ι] [Fintype γ] [Nonempty γ]
    {a b : ι} (hab : a ≠ b) :
    (pi (α := fun _ : ι => γ) fun _ => uniformOfFintype γ).toOuterMeasure {H | H a = H b} =
      (Fintype.card γ : ℝ≥0∞)⁻¹ := by
  classical
  have hset : {H : ι → γ | H a = H b} = (fun H => decide (H a = H b)) ⁻¹' {true} := by
    ext; simp
  have hupd := bind_pi_update (fun _ : ι => uniformOfFintype γ) b
    (fun w H => PMF.pure (decide (H a = w)))
  rw [hset, ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton, PMF.map,
    Function.comp_def, ← hupd]
  refine bind_apply_of_forall _ fun w => ?_
  have h := pi_map_eval (Function.update (fun _ : ι => uniformOfFintype γ) b (PMF.pure w)) a
  rw [Function.update_of_ne hab] at h
  generalize hμ : pi (Function.update (fun _ : ι => uniformOfFintype γ) b (PMF.pure w)) = μ at h ⊢
  rw [← uniformOfFintype_apply w, ← bind_pure_decide_eq_apply_true' _ w, ← h, PMF.bind_map]
  rfl

/-- Union bound: some pair among `|J|` pairs of distinct coordinates of a uniform random
function collides with probability at most `|J| / |γ|`. -/
private theorem pi_toOuterMeasure_exists_le {ι γ J : Type} [Fintype ι] [Fintype γ] [Nonempty γ]
    [Fintype J] {a b : J → ι} (hab : ∀ j, a j ≠ b j) :
    (pi (α := fun _ : ι => γ) fun _ => uniformOfFintype γ).toOuterMeasure
        {H | ∃ j, H (a j) = H (b j)} ≤ Fintype.card J * (Fintype.card γ : ℝ≥0∞)⁻¹ := by
  have hset : {H : ι → γ | ∃ j, H (a j) = H (b j)} =
      ⋃ j ∈ (Finset.univ : Finset J), {H | H (a j) = H (b j)} := by
    ext; simp
  rw [hset]
  refine (MeasureTheory.measure_biUnion_finset_le _ _).trans_eq ?_
  simp [pi_toOuterMeasure_eq (hab _)]

/-- A game failing with probability at most `n / K` and another succeeding with probability at
most `1 / K` have advantage at least `1 - (n + 1) / K`. -/
private theorem le_advantage_of_apply_le {g₀ g₁ : Game} {n k : ℕ} (hk : k ≠ 0)
    (h₀ : g₀ false ≤ n * (k : ℝ≥0∞)⁻¹) (h₁ : g₁ true ≤ (k : ℝ≥0∞)⁻¹) :
    1 - ((n : ℝ) + 1) / k ≤ (Game.advantage g₀ g₁ : ℝ) := by
  have hk' : (k : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by exact_mod_cast hk)
  have hr₀ := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hk') h₀
  have hr₁ := ENNReal.toReal_mono hk' h₁
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    at hr₀
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at hr₁
  have hsum := toReal_true_add_toReal_false g₀
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
  refine le_trans ?_ (le_abs_self _)
  rw [add_div, div_eq_mul_inv, div_eq_mul_inv, one_mul]
  linarith

/-- Without the re-encryption check, `leakAdv` distinguishes the real challenge key of
`FO-notbot` over `leakyPKE P` from a random one with advantage at least `1 - (n + 1) / |K|`, for
a perfectly correct `P` and uniform keys. -/
theorem advantage_eagerNoCheckGame_leakAdv [Finite R] [Fintype CT] [Fintype K] [Nonempty K]
    (P : ExplicitCoinPKE PK SK (Fin n → Bool) R CT) (sampleMsg : ProbComp (Fin n → Bool))
    (sampleKey : ProbComp K) (hkey : ProbComp.eval sampleKey = uniformOfFintype K)
    (hcorr : ∀ pk sk, (pk, sk) ∈ (ProbComp.eval P.keyGen).support → ∀ m,
      ∀ r ∈ (ProbComp.eval P.sampleCoins).support, P.dec sk (P.encDet pk m r) = some m) :
    1 - ((n : ℝ) + 1) / Fintype.card K ≤
      (Game.advantage
        ((⟨leakyPKE P, sampleMsg, sampleKey⟩ :
          Scheme PK SK (Fin n → Bool) R (CT × Option (Fin n)) K).eagerNoCheckGame leakAdv false)
        ((⟨leakyPKE P, sampleMsg, sampleKey⟩ : Scheme _ _ _ _ _ _).eagerNoCheckGame leakAdv true) :
        ℝ) := by
  have h1 : (⟨leakyPKE P, sampleMsg, sampleKey⟩ :
      Scheme PK SK (Fin n → Bool) R (CT × Option (Fin n)) K).eagerNoCheckGame leakAdv true true ≤
        (Fintype.card K : ℝ≥0∞)⁻¹ := by
    simp only [Scheme.eagerNoCheckGame, Scheme.keyGenNotBot, Scheme.encapsNotBot,
      Scheme.encapsBot, ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
      PMF.bind_bind, PMF.pure_bind]
    refine bind_apply_le_on_support _ fun ⟨pk, sk⟩ hk => ?_
    refine bind_apply_le_on_support _ fun s _ => ?_
    refine bind_apply_le_on_support _ fun G hG => ?_
    refine bind_apply_le_on_support _ fun H _ => ?_
    refine bind_apply_le_on_support _ fun m _ => ?_
    have hdec := leakyPKE_dec_some (hcorr pk sk hk m (G m) ((mem_support_pi_iff _ _).1 hG m))
    simp only [encT_leakyPKE, ite_true,
      interpret_leakAdv ⟨leakyPKE P, sampleMsg, sampleKey⟩ G H ⟨sk, pk, s⟩ _ m hdec]
    rw [hkey, bind_pure_decide_eq_apply_true, uniformOfFintype_apply]
  have h0 : (⟨leakyPKE P, sampleMsg, sampleKey⟩ :
      Scheme PK SK (Fin n → Bool) R (CT × Option (Fin n)) K).eagerNoCheckGame leakAdv false false ≤
        n * (Fintype.card K : ℝ≥0∞)⁻¹ := by
    simp only [Scheme.eagerNoCheckGame, Scheme.keyTable, Scheme.keyGenNotBot, Scheme.encapsNotBot,
      Scheme.encapsBot, ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
      PMF.bind_bind, PMF.pure_bind]
    refine bind_apply_le_on_support _ fun ⟨pk, sk⟩ hk => ?_
    refine bind_apply_le_on_support _ fun s _ => ?_
    refine bind_apply_le_on_support _ fun G hG => ?_
    rw [PMF.bind_comm]
    refine bind_apply_le_on_support _ fun m _ => ?_
    have hdec := leakyPKE_dec_some (hcorr pk sk hk m (G m) ((mem_support_pi_iff _ _).1 hG m))
    simp only [encT_leakyPKE, Bool.false_eq_true, ite_false,
      interpret_leakAdv ⟨leakyPKE P, sampleMsg, sampleKey⟩ _ _ ⟨sk, pk, s⟩ _ m hdec, PMF.bind_const]
    rw [hkey]
    change (PMF.map _ _) false ≤ _
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    set c := P.encDet pk m (G m)
    have hab (i : Fin n) : ((false, fun _ => false, (c, some i)) : Bool × (Fin n → Bool) × _) ≠
        (false, fun _ => true, (c, some i)) := by
      simpa using fun h => Bool.false_ne_true (congrFun h i)
    refine (MeasureTheory.measure_mono ?_).trans
      ((pi_toOuterMeasure_exists_le hab).trans_eq (by simp))
    intro H hH
    simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_false_iff_not] at hH
    by_contra hne
    simp only [Set.mem_ofPred_eq, not_exists] at hne
    refine hH (congrArg (fun m' => H (false, m', (c, none))) (funext fun i => ?_))
    cases hm : m i <;> simp [leakGuess, hm, hne i]
  exact le_advantage_of_apply_le Fintype.card_ne_zero h0 h1

end Attack

end Cslib.Crypto.Protocols.FujisakiOkamoto

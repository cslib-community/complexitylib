/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.IndexedSignature
public import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# Doubling the capacity of an indexed signature scheme

Two independent instances of an indexed signature scheme `S` of capacity at least `1` combine into
an indexed signature scheme `S.double hcap` of constant capacity `2`: key generation samples two
independent key pairs `(k₀, k₁)` from `S.keyGen n`, index `0` signs and verifies at index `0` under
`k₀`, index `1` signs and verifies at index `0` under `k₁`, and verification rejects every index
`u ≥ 2`.

This is the `q = 2` case of the `q`-key construction in [BonehShoup2023], Section 14.6.1,
construction `(14.4)` (generalized from one-time signatures to any indexed scheme with
`1 ≤ S.capacity n`, with randomized signing and arbitrary-length messages as in
`IndexedSignatureScheme`). By the plug-and-pray reduction ([BonehShoup2023], Section 14.6.1,
referring to Exercise 13.2), `doubleForger` plants its challenge verification key at a uniform slot
`b ∈ {false, true}`, generates the other key pair locally, forwards queries at slot `b.toNat` to its
indexed signing oracle at index `0`, and answers queries at the unplanted slot locally. Every valid
forgery against `S.double hcap` lands on `u = 0` or `u = 1` and hits the planted slot with
probability `1 / 2`, losing at most a factor of `2` (`succProbability_indexedEufCmaGame_double_le`,
`IndexedSignatureScheme.IndexedEUFCMA.double`).

In particular, doubling upgrades any capacity-`1` indexed signature scheme to the `2 ≤ capacity n`
hypothesis of `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay`.

## Main definitions

* `Cslib.Crypto.IndexedSignatureScheme.doubleKeyDecoder`: pair decoder for bundled public and secret
  keys.
* `Cslib.Crypto.IndexedSignatureScheme.doubleKeyGen`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleSign`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleVerify`,
  `Cslib.Crypto.IndexedSignatureScheme.double`: capacity-`2` doubling combinator.
* `Cslib.Crypto.IndexedSignatureScheme.doublePlantPk`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleHandler`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleForgerAt`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleForger`: plug-and-pray reduction to `S`.

## Main results

* `Cslib.Crypto.IndexedSignatureScheme.succProbability_indexedEufCmaGame_double_le`: forging
  probability against `S.double hcap` is at most `2` times that of `doubleForger` against `S`.
* `Cslib.Crypto.IndexedSignatureScheme.isOraclePPT_doubleForger`: `doubleForger` is uniformly strict
  oracle PPT.
* `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.double`: `IndexedEUFCMA` is preserved by
  `S.double hcap`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.1 (construction `(14.4)` at `q = 2`) and Exercise 13.2.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace IndexedSignatureScheme

/-! ### The capacity-`2` doubled scheme -/

/-- Total decoder for paired public or secret keys `encPair encBits encBits (k₀, k₁)`. -/
@[expose]
def doubleKeyDecoder : Decoder (encPair encBits encBits) :=
  Decoder.bits.pair Decoder.bits

/-- Sample two independent key pairs `(k₀, k₁)` from `S.keyGen n` and bundle their public and secret
halves with `encPair encBits encBits`. -/
@[expose]
def doubleKeyGen (S : IndexedSignatureScheme) (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let k₀ ← S.keyGen n
  let k₁ ← S.keyGen n
  return (encPair encBits encBits (k₀.1, k₁.1), encPair encBits encBits (k₀.2, k₁.2))

/-- Sign `msg` at index `u ∈ {0, 1}` using index `0` of the `u`-th secret key, returning `[]` when
`u ≥ 2`. -/
@[expose]
def doubleSign (S : IndexedSignatureScheme) (sk : List Bool) (u : ℕ) (msg : List Bool) :
    ProbComp (List Bool) :=
  let sks := doubleKeyDecoder.decode sk
  if u = 0 then
    S.sign sks.1 0 msg
  else if u = 1 then
    S.sign sks.2 0 msg
  else
    pure []

/-- Verify `(u, msg, sig)` under bundled public keys `(pk₀, pk₁)`: accept only at `u = 0` under
`pk₀` or at `u = 1` under `pk₁`, always at inner index `0`. -/
@[expose]
def doubleVerify (S : IndexedSignatureScheme) (pk : List Bool) (u : ℕ) (msg sig : List Bool) :
    Bool :=
  let pks := doubleKeyDecoder.decode pk
  (u == 0 && S.verify pks.1 0 msg sig) || (u == 1 && S.verify pks.2 0 msg sig)

/-- **Capacity-`2` doubling combinator** ([BonehShoup2023], Section 14.6.1, construction `(14.4)` at
`q = 2`): combine two independent instances of `S` (with `∀ n, 1 ≤ S.capacity n`) into an
`IndexedSignatureScheme` of capacity `2`. -/
@[expose]
def double (S : IndexedSignatureScheme) (hcap : ∀ n, 1 ≤ S.capacity n) :
    IndexedSignatureScheme where
  capacity := fun _ => 2
  keyGen := S.doubleKeyGen
  sign := S.doubleSign
  verify := S.doubleVerify
  capacity_polyTime := ComputableInPolyTime.const 2
  keyGen_ppt := by
    let EKg := encPair (encPair encUnary (encPair encBits encBits)) (encPair encBits encBits)
    have hp := ComputableTidilyInPolyTime.id' (encIn := EKg)
    have hret := (hp.fst'.snd'.fst'.prod hp.snd'.fst').encoded.prod
      (hp.fst'.snd'.snd'.prod hp.snd'.snd').encoded
    exact S.keyGen_ppt.bind_with
      ((S.keyGen_ppt.preprocess (ComputableInPolyTime.fst _ _)).bind_with hret.isPPTOn)
  sign_ppt := by
    let ESign := encPair encBits (encPair encUnary encBits)
    have hp := ComputableTidilyInPolyTime.id' (encIn := ESign)
    have hdec := doubleKeyDecoder.computableInPolyTime.tidy.comp hp.fst'
    have hu := hp.snd'.fst'
    have hmsg := hp.snd'.snd'
    have heq : (fun p : List Bool × ℕ × List Bool => S.doubleSign p.1 p.2.1 p.2.2) =
        fun p =>
          if (p.2.1 == 0) = true then S.sign (doubleKeyDecoder.decode p.1).1 0 p.2.2
          else if (p.2.1 == 1) = true then S.sign (doubleKeyDecoder.decode p.1).2 0 p.2.2
          else pure [] := by
      funext p; simp only [doubleSign, beq_iff_eq]
    rw [heq]
    have h0msg := (ComputableTidilyInPolyTime.const (encMid := encUnary) 0).prod hmsg
    exact IsPPTOn.ite (ComputableTidilyInPolyTime.unary_beq hu (.const 0))
      (S.sign_ppt.preprocess (.of_tidy (hdec.fst'.prod h0msg)))
      (IsPPTOn.ite (ComputableTidilyInPolyTime.unary_beq hu (.const 1))
        (S.sign_ppt.preprocess (.of_tidy (hdec.snd'.prod h0msg)))
        (ComputableInPolyTime.const []).isPPTOn)
  verify_polyTime := by
    let EVer := encPair encBits (encPair encUnary (encPair encBits encBits))
    have hp := ComputableTidilyInPolyTime.id' (encIn := EVer)
    have hdec := doubleKeyDecoder.computableInPolyTime.tidy.comp hp.fst'
    have hu := hp.snd'.fst'
    have hms := hp.snd'.snd'
    have hv := S.verify_polyTime.tidy
    have h0 := (ComputableTidilyInPolyTime.unary_beq hu (.const 0)).bool_and'
      (hv.comp (hdec.fst'.prod ((ComputableTidilyInPolyTime.const 0).prod hms)))
    have h1 := (ComputableTidilyInPolyTime.unary_beq hu (.const 1)).bool_and'
      (hv.comp (hdec.snd'.prod ((ComputableTidilyInPolyTime.const 0).prod hms)))
    exact .of_tidy (ComputableTidilyInPolyTime.bool_or.comp (h0.prod h1))
  verify_sign := by
    intro n keys hkeys u hu msg sig hsig
    simp only [doubleKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hkeys
    obtain ⟨k₀, hk₀, k₁, hk₁, rfl⟩ := hkeys
    have h0 : 0 < S.capacity n := hcap n
    by_cases hu0 : u = 0
    · subst hu0
      simp only [doubleSign, ↓reduceIte, doubleKeyDecoder.decode_enc] at hsig
      simp only [doubleVerify, doubleKeyDecoder.decode_enc, beq_self_eq_true, Bool.true_and,
        S.verify_sign n k₀ hk₀ 0 h0 msg sig hsig, Bool.true_or]
    · have hu1 : u = 1 := by omega
      subst hu1
      simp only [doubleSign, Nat.one_ne_zero, ↓reduceIte, doubleKeyDecoder.decode_enc] at hsig
      simp only [doubleVerify, doubleKeyDecoder.decode_enc, beq_self_eq_true, Bool.true_and,
        S.verify_sign n k₁ hk₁ 0 h0 msg sig hsig, Bool.or_true]

@[simp]
theorem capacity_double (S : IndexedSignatureScheme) (hcap : ∀ n, 1 ≤ S.capacity n) (n : ℕ) :
    (S.double hcap).capacity n = 2 := rfl

/-! ### Plug-and-pray reduction -/

/-- Bundle a challenge verification key `vk` at slot `b.toNat` (`false ↦ 0`, `true ↦ 1`) with a
locally generated public key `otherPk` at the complementary slot. -/
@[expose]
def doublePlantPk (b : Bool) (vk otherPk : List Bool) : List Bool :=
  if b then encPair encBits encBits (otherPk, vk)
  else encPair encBits encBits (vk, otherPk)

/-- Stateful signing handler for `doubleForger`: maintains the outer query log `signed` of pairs
`(u, msg)` with `u < 2`. When a fresh index `u < 2` is queried:
* if `u = b.toNat`, forward `(0, msg)` to the external `S`-signing oracle and truncate the reply to
  `bound n msg.length` bits;
* otherwise, sign `(0, msg)` locally under `otherSk`. -/
def doubleHandler (S : IndexedSignatureScheme) (b : Bool) (otherSk : List Bool)
    (bound : ℕ → ℕ → ℕ) (n : ℕ) (request : Unit × List Bool)
    (signed : List (ℕ × List Bool)) :
    WordOracleComp Unit (List Bool × List (ℕ × List Bool)) :=
  let r := requestDecoder.decode request.2
  if r.1 < 2 ∧ r.1 ∉ signed.map Prod.fst then
    if r.1 = b.toNat then
      (fun sig => (sig, r :: signed)) <$>
        (List.take (bound n r.2.length) <$>
          ProbOracleComp.query ((), encPair encUnary encBits (0, r.2)))
    else
      (fun sig => (sig, r :: signed)) <$>
        ProbOracleComp.sample (S.sign otherSk 0 r.2)
  else
    pure ([], signed)

/-- Fixed-slot reduction from `(S.double hcap)` to `S` at slot `b : Bool`. -/
def doubleForgerAt (S : IndexedSignatureScheme) (bound : ℕ → ℕ → ℕ) (adversary : IndexedForger)
    (b : Bool) (n : ℕ) (vk : List Bool) : WordOracleComp Unit (ℕ × List Bool × List Bool) := do
  let other ← ProbOracleComp.sample (S.keyGen n)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (S.doubleHandler b other.2 bound n))
    (adversary n (doublePlantPk b vk other.1))).run []
  let (_, msg, sig) := out.1
  return (0, msg, sig)

/-- Plug-and-pray reduction ([BonehShoup2023], Section 14.6.1, Exercise 13.2): sample a fair slot
`b ← ProbComp.uniform Bool` and run `doubleForgerAt`. -/
noncomputable def doubleForger (S : IndexedSignatureScheme) (bound : ℕ → ℕ → ℕ)
    (adversary : IndexedForger) : IndexedForger := fun n vk => do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  S.doubleForgerAt bound adversary b n vk

/-! ### Exact simulation at each slot -/

/-- Joint handler pairing `doubleHandler`'s outer log with `S.indexedSigningOracle`'s inner log. -/
private noncomputable def doubleJointOracle (S : IndexedSignatureScheme) (b : Bool)
    (challengeSk otherSk : List Bool) (bound : ℕ → ℕ → ℕ) (n : ℕ) (q : Unit × List Bool)
    (state : List (ℕ × List Bool) × List (ℕ × List Bool)) :
    PMF (List Bool × List (ℕ × List Bool) × List (ℕ × List Bool)) :=
  (ProbOracleComp.runWith (fun q' s' => ProbComp.eval (S.indexedSigningOracle n challengeSk q' s'))
      (S.doubleHandler b otherSk bound n q state.1) state.2).map
      (fun r => (r.1.1, r.1.2, r.2))

/-- Invariant relating the outer log `signed` and the inner `S`-oracle log `ext`: `0` has been used
in `ext` iff `b.toNat` has been used in `signed`, and any `(0, m)` in `ext` came from
`(b.toNat, m)` in `signed`. -/
private def doubleLogInv (b : Bool)
    (state : List (ℕ × List Bool) × List (ℕ × List Bool)) : Prop :=
  (0 ∈ state.2.map Prod.fst ↔ b.toNat ∈ state.1.map Prod.fst) ∧
    ∀ m, (0, m) ∈ state.2 → (b.toNat, m) ∈ state.1

private theorem doubleJointOracle_planted {S : IndexedSignatureScheme} {b : Bool}
    {challengeSk otherSk : List Bool} {bound : ℕ → ℕ → ℕ} {n : ℕ} (hcap : 1 ≤ S.capacity n)
    {w : List Bool} {signed ext : List (ℕ × List Bool)}
    (hinv : doubleLogInv b (signed, ext))
    (hfresh : (requestDecoder.decode w).1 < 2 ∧ (requestDecoder.decode w).1 ∉ signed.map Prod.fst)
    (hslot : (requestDecoder.decode w).1 = b.toNat) :
    doubleJointOracle S b challengeSk otherSk bound n ((), w) (signed, ext) =
      (ProbComp.eval (S.sign challengeSk 0 (requestDecoder.decode w).2)).bind fun σ =>
        PMF.pure (List.take (bound n (requestDecoder.decode w).2.length) σ,
          requestDecoder.decode w :: signed, (0, (requestDecoder.decode w).2) :: ext) := by
  have hpos : 0 < S.capacity n := hcap
  have hnot0 : 0 ∉ ext.map Prod.fst := fun h0 => hfresh.2 (hslot ▸ hinv.1.mp h0)
  simp only [doubleJointOracle, doubleHandler, hfresh.1, hfresh.2, not_false_eq_true, and_self,
    ↓reduceIte]
  simp only [hslot, ↓reduceIte, indexedSigningOracle, requestDecoder.decode_enc, hpos, hnot0,
    not_false_eq_true, and_self, runWith_norm, pmf_norm]

private theorem doubleJointOracle_unplanted {S : IndexedSignatureScheme} {b : Bool}
    {challengeSk otherSk : List Bool} {bound : ℕ → ℕ → ℕ} {n : ℕ}
    {w : List Bool} {signed ext : List (ℕ × List Bool)}
    (hfresh : (requestDecoder.decode w).1 < 2 ∧ (requestDecoder.decode w).1 ∉ signed.map Prod.fst)
    (hslot : (requestDecoder.decode w).1 ≠ b.toNat) :
    doubleJointOracle S b challengeSk otherSk bound n ((), w) (signed, ext) =
      (ProbComp.eval (S.sign otherSk 0 (requestDecoder.decode w).2)).bind fun σ =>
        PMF.pure (σ, requestDecoder.decode w :: signed, ext) := by
  simp only [doubleJointOracle, doubleHandler, hfresh.1, hfresh.2, not_false_eq_true, and_self,
    ↓reduceIte, hslot, runWith_norm, pmf_norm]
  rfl

private theorem doubleJointOracle_refused {S : IndexedSignatureScheme} {b : Bool}
    {challengeSk otherSk : List Bool} {bound : ℕ → ℕ → ℕ} {n : ℕ}
    {w : List Bool} {signed ext : List (ℕ × List Bool)}
    (href : ¬ ((requestDecoder.decode w).1 < 2 ∧
      (requestDecoder.decode w).1 ∉ signed.map Prod.fst)) :
    doubleJointOracle S b challengeSk otherSk bound n ((), w) (signed, ext) =
      PMF.pure ([], signed, ext) := by
  simp only [doubleJointOracle, doubleHandler, href, ↓reduceIte, runWith_norm, pmf_norm]

private theorem doubleLogInv_preserve {S : IndexedSignatureScheme} {b : Bool}
    {challengeSk otherSk : List Bool} {bound : ℕ → ℕ → ℕ} {n : ℕ} (hcap : 1 ≤ S.capacity n)
    (q : Unit × List Bool) (state : List (ℕ × List Bool) × List (ℕ × List Bool))
    (hinv : doubleLogInv b state) (reply : List Bool)
    (next : List (ℕ × List Bool) × List (ℕ × List Bool))
    (hmem : (reply, next) ∈
      (doubleJointOracle S b challengeSk otherSk bound n q state).support) :
    doubleLogInv b next := by
  rcases q with ⟨⟨⟩, w⟩
  rcases state with ⟨signed, ext⟩
  by_cases hfresh :
      (requestDecoder.decode w).1 < 2 ∧ (requestDecoder.decode w).1 ∉ signed.map Prod.fst
  · by_cases hslot : (requestDecoder.decode w).1 = b.toNat
    · rw [doubleJointOracle_planted hcap hinv hfresh hslot] at hmem
      simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      obtain ⟨σ, -, -, rfl, rfl⟩ := hmem
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons, true_or, hslot.symm]
      · intro m hm
        rcases List.mem_cons.mp hm with heq | hm
        · rcases Prod.mk.inj heq with ⟨-, rfl⟩
          exact List.mem_cons.mpr (Or.inl (Prod.ext hslot.symm rfl))
        · exact List.mem_cons_of_mem _ (hinv.2 m hm)
    · rw [doubleJointOracle_unplanted hfresh hslot] at hmem
      simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      obtain ⟨σ, -, -, rfl, rfl⟩ := hmem
      have hne : b.toNat ≠ (requestDecoder.decode w).1 := Ne.symm hslot
      refine ⟨?_, ?_⟩
      · simpa only [doubleLogInv, List.map_cons, List.mem_cons, hne, false_or] using hinv.1
      · intro m hm
        exact List.mem_cons_of_mem _ (hinv.2 m hm)
  · rw [doubleJointOracle_refused hfresh] at hmem
    simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact hinv

/-- Projecting the joint run onto `(output, signed)` recovers `(S.double hcap).indexedSigningOracle`
on the bundled secret key `(sk₀, sk₁)` corresponding to slot `b`. -/
private theorem map_run_doubleJointOracle {S : IndexedSignatureScheme}
    (hcap : ∀ n, 1 ≤ S.capacity n) (b : Bool) {challengeSk otherSk : List Bool}
    {bound : ℕ → ℕ → ℕ} {n : ℕ}
    (hbound : ∀ msg, ∀ σ ∈ (ProbComp.eval (S.sign challengeSk 0 msg)).support,
      σ.length ≤ bound n msg.length)
    {α : Type} (program : WordOracleComp Unit α) :
    let bundledSk := if b then encPair encBits encBits (otherSk, challengeSk)
      else encPair encBits encBits (challengeSk, otherSk)
    ((ProbOracleComp.runWith (doubleJointOracle S b challengeSk otherSk bound n) program
        ([], [])).map (fun r => (r.1, r.2.1)) =
      ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          ((S.double hcap).indexedSigningOracle n bundledSk))
        program).run [])) ∧
    ∀ r ∈ (ProbOracleComp.runWith (doubleJointOracle S b challengeSk otherSk bound n) program
        ([], [])).support,
      doubleLogInv b r.2 := by
  intro bundledSk
  have hinvAll : ∀ r ∈ (ProbOracleComp.runWith (doubleJointOracle S b challengeSk otherSk bound n)
      program ([], [])).support,
      doubleLogInv b r.2 := by
    intro r hr
    exact ProbOracleComp.runWith_invariant
      (oracle := doubleJointOracle S b challengeSk otherSk bound n)
      (invariant := doubleLogInv b)
      (fun q st hst a next hmem => doubleLogInv_preserve (hcap n) q st hst a next hmem)
      program ([], []) ⟨by simp, by simp⟩ r.1 r.2 hr
  refine ⟨?_, hinvAll⟩
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  refine ProbOracleComp.runWith_map_state_of_invariant _ _
    Prod.fst (doubleLogInv b)
    (fun q st hst a next hmem => doubleLogInv_preserve (hcap n) q st hst a next hmem)
    ?_ program ([], []) ⟨by simp, by simp⟩
  rintro ⟨⟨⟩, w⟩ ⟨signed, ext⟩ hinv
  by_cases hfresh :
      (requestDecoder.decode w).1 < 2 ∧ (requestDecoder.decode w).1 ∉ signed.map Prod.fst
  · by_cases hslot : (requestDecoder.decode w).1 = b.toNat
    · rw [doubleJointOracle_planted (hcap n) hinv hfresh hslot]
      have hdouble :
          (S.double hcap).sign bundledSk (requestDecoder.decode w).1 (requestDecoder.decode w).2 =
            S.sign challengeSk 0 (requestDecoder.decode w).2 := by
        cases b
        · have h0 : (requestDecoder.decode w).1 = 0 := hslot
          simp only [bundledSk, Bool.false_eq_true, ↓reduceIte, double, doubleSign,
            doubleKeyDecoder.decode_enc, h0]
        · have h1 : (requestDecoder.decode w).1 = 1 := hslot
          simp only [bundledSk, ↓reduceIte, double, doubleSign, doubleKeyDecoder.decode_enc, h1,
            Nat.one_ne_zero]
      simp only [indexedSigningOracle, capacity_double, hfresh.1, hfresh.2, not_false_eq_true,
        and_self, ↓reduceIte, hdouble, pmf_norm]
      refine PMF.bind_congr_on_support _ _ _ fun σ hσ => ?_
      rw [List.take_of_length_le (hbound _ σ hσ)]
    · rw [doubleJointOracle_unplanted hfresh hslot]
      have hdouble :
          (S.double hcap).sign bundledSk (requestDecoder.decode w).1 (requestDecoder.decode w).2 =
            S.sign otherSk 0 (requestDecoder.decode w).2 := by
        cases b
        · have hne0 : (requestDecoder.decode w).1 ≠ 0 := hslot
          have h1 : (requestDecoder.decode w).1 = 1 := by
            have := hfresh.1
            omega
          simp only [bundledSk, Bool.false_eq_true, ↓reduceIte, double, doubleSign,
            doubleKeyDecoder.decode_enc, h1, Nat.one_ne_zero]
        · have hne1 : (requestDecoder.decode w).1 ≠ 1 := hslot
          have h0 : (requestDecoder.decode w).1 = 0 := by
            have := hfresh.1
            omega
          simp only [bundledSk, ↓reduceIte, double, doubleSign, doubleKeyDecoder.decode_enc, h0]
      simp only [indexedSigningOracle, capacity_double, hfresh.1, hfresh.2, not_false_eq_true,
        and_self, ↓reduceIte, hdouble, pmf_norm]
  · rw [doubleJointOracle_refused hfresh]
    simp only [indexedSigningOracle, capacity_double, hfresh, ↓reduceIte, pmf_norm]

private theorem eval_indexedEufCmaGame_doubleForgerAt (S : IndexedSignatureScheme)
    (bound : ℕ → ℕ → ℕ) (adversary : IndexedForger) (b : Bool) (n : ℕ) :
    ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary b) n) =
      (ProbComp.eval (S.keyGen n)).bind fun challenge =>
        (ProbComp.eval (S.keyGen n)).bind fun other =>
          (ProbOracleComp.runWith (doubleJointOracle S b challenge.2 other.2 bound n)
              (adversary n (doublePlantPk b challenge.1 other.1)) ([], [])).map fun r =>
              !r.2.2.contains (0, r.1.2.1) && S.verify challenge.1 0 r.1.2.1 r.1.2.2 := by
  simp only [indexedEufCmaGame, doubleForgerAt, runWith_norm, pmf_norm]
  rfl

/-- **Plug-and-pray bound for `S.double hcap`** ([BonehShoup2023], Section 14.6.1, Exercise 13.2):
for every indexed forger `adversary` and every security parameter `n`, when `bound n L` covers the
length of every supported `S`-signature at index `0` on an `L`-bit message, the forging probability
against `S.double hcap` is at most `2` times the forging probability of `S.doubleForger` against
`S`. -/
theorem succProbability_indexedEufCmaGame_double_le {S : IndexedSignatureScheme}
    (hcap : ∀ n, 1 ≤ S.capacity n) {bound : ℕ → ℕ → ℕ} {n : ℕ}
    (hbound : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg,
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 0 msg)).support, σ.length ≤ bound n msg.length)
    (adversary : IndexedForger) :
    Game.succProbability (ProbComp.eval ((S.double hcap).indexedEufCmaGame adversary n)) ≤
      2 * Game.succProbability
        (ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n)) := by
  have hsplit :
      ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n) =
        (ProbComp.eval (ProbComp.uniform Bool)).bind fun b =>
          ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary b) n) := by
    simp only [indexedEufCmaGame, doubleForger, runWith_norm, pmf_norm]
    exact PMF.bind_comm _ _ _
  have htwo :
      (2 : ℝ≥0∞) * (ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n)) true =
        (ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary false) n)) true +
          (ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary true) n)) true := by
    rw [hsplit, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    have hunif : ∀ b : Bool, (ProbComp.eval (ProbComp.uniform Bool)) b = (2 : ℝ≥0∞)⁻¹ := by
      intro b
      simp [ProbComp.eval_uniform, PMF.uniformOfFintype_apply]
    rw [hunif false, hunif true, ← mul_add, ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, add_comm]
  let slotEvent (b : Bool) (k₀ k₁ : List Bool × List Bool) : PMF Bool :=
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        ((S.double hcap).indexedSigningOracle n (encPair encBits encBits (k₀.2, k₁.2))))
      (adversary n (encPair encBits encBits (k₀.1, k₁.1)))).run [])).map fun out =>
        !out.2.contains (out.1.1, out.1.2.1) && (out.1.1 == b.toNat) &&
          S.verify (if b then k₁.1 else k₀.1) 0 out.1.2.1 out.1.2.2
  have hslot_step {vk : List Bool}
      {r : (ℕ × List Bool × List Bool) × List (ℕ × List Bool) × List (ℕ × List Bool)}
      (b : Bool) (hinv : doubleLogInv b r.2) :
      PMF.pure (!r.2.1.contains (r.1.1, r.1.2.1) && (r.1.1 == b.toNat) &&
        S.verify vk 0 r.1.2.1 r.1.2.2) true ≤
      PMF.pure (!r.2.2.contains (0, r.1.2.1) && S.verify vk 0 r.1.2.1 r.1.2.2) true := by
    cases hwin : !r.2.1.contains (r.1.1, r.1.2.1) && (r.1.1 == b.toNat) &&
        S.verify vk 0 r.1.2.1 r.1.2.2
    · simp
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq,
        ← Bool.not_eq_true, List.contains_iff_mem] at hwin
      obtain ⟨⟨hfresh, hu⟩, hv⟩ := hwin
      have hwin' : (!r.2.2.contains (0, r.1.2.1) && S.verify vk 0 r.1.2.1 r.1.2.2) = true := by
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          ← Bool.not_eq_true, List.contains_iff_mem]
        exact ⟨fun hmem => hfresh (hu ▸ hinv.2 _ hmem), hv⟩
      rw [hwin']
  have hslot0 :
      ((ProbComp.eval (S.keyGen n)).bind fun k₀ =>
        (ProbComp.eval (S.keyGen n)).bind fun k₁ => slotEvent false k₀ k₁) true ≤
      (ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary false) n)) true := by
    rw [eval_indexedEufCmaGame_doubleForgerAt]
    apply PMF.bind_apply_mono_on_support; intro k₀ hk₀
    apply PMF.bind_apply_mono_on_support; intro k₁ _
    obtain ⟨heq, hinv⟩ := map_run_doubleJointOracle hcap false (otherSk := k₁.2) (hbound k₀ hk₀)
      (adversary n (encPair encBits encBits (k₀.1, k₁.1)))
    dsimp only [slotEvent, doublePlantPk]
    simp only [Bool.false_eq_true, ↓reduceIte] at heq ⊢
    rw [← heq, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    apply PMF.bind_apply_mono_on_support; intro r hr
    exact hslot_step false (hinv r hr)
  have hslot1 :
      ((ProbComp.eval (S.keyGen n)).bind fun k₀ =>
        (ProbComp.eval (S.keyGen n)).bind fun k₁ => slotEvent true k₀ k₁) true ≤
      (ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary true) n)) true := by
    rw [eval_indexedEufCmaGame_doubleForgerAt]
    conv_rhs => rw [PMF.bind_comm]
    apply PMF.bind_apply_mono_on_support; intro k₀ _
    apply PMF.bind_apply_mono_on_support; intro k₁ hk₁
    obtain ⟨heq, hinv⟩ := map_run_doubleJointOracle hcap true (otherSk := k₀.2) (hbound k₁ hk₁)
      (adversary n (encPair encBits encBits (k₀.1, k₁.1)))
    dsimp only [slotEvent, doublePlantPk]
    simp only [↓reduceIte] at heq ⊢
    rw [← heq, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    apply PMF.bind_apply_mono_on_support; intro r hr
    exact hslot_step true (hinv r hr)
  have hgame :
      (ProbComp.eval ((S.double hcap).indexedEufCmaGame adversary n)) true ≤
        ((ProbComp.eval (S.keyGen n)).bind fun k₀ =>
          (ProbComp.eval (S.keyGen n)).bind fun k₁ => slotEvent false k₀ k₁) true +
        ((ProbComp.eval (S.keyGen n)).bind fun k₀ =>
          (ProbComp.eval (S.keyGen n)).bind fun k₁ => slotEvent true k₀ k₁) true := by
    simp only [indexedEufCmaGame, double, doubleKeyGen, pmf_norm]
    rw [PMF.bind_apply, PMF.bind_apply, PMF.bind_apply, ← tsum_add]
    refine tsum_le_tsum fun k₀ => ?_
    rw [← mul_add, PMF.bind_apply, PMF.bind_apply, PMF.bind_apply, ← tsum_add]
    refine mul_le_mul_right (tsum_le_tsum fun k₁ => ?_) _
    rw [← mul_add]
    refine mul_le_mul_right ?_ _
    dsimp only [slotEvent]
    rw [show (fun x : (ℕ × List Bool × List Bool) × List (ℕ × List Bool) =>
        PMF.pure (!x.2.contains (x.1.1, x.1.2.1) &&
          S.doubleVerify (encPair encBits encBits (k₀.1, k₁.1)) x.1.1 x.1.2.1 x.1.2.2)) =
      fun x => PMF.pure (!x.2.contains (x.1.1, x.1.2.1) &&
        ((x.1.1 == 0 && S.verify k₀.1 0 x.1.2.1 x.1.2.2) ||
          (x.1.1 == 1 && S.verify k₁.1 0 x.1.2.1 x.1.2.2))) by
      funext x
      simp only [doubleVerify, doubleKeyDecoder.decode_enc]]
    rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp, PMF.bind_apply, PMF.bind_apply, PMF.bind_apply,
      ← tsum_add]
    refine tsum_le_tsum fun out => ?_
    rw [← mul_add]
    refine mul_le_mul_right ?_ _
    dsimp only [Function.comp_def]
    cases hfresh : !out.2.contains (out.1.1, out.1.2.1)
    · simp
    · by_cases hu0 : out.1.1 = 0
      · cases hv0 : S.verify k₀.1 0 out.1.2.1 out.1.2.2 <;> simp [hu0, hv0]
      · by_cases hu1 : out.1.1 = 1
        · cases hv1 : S.verify k₁.1 0 out.1.2.1 out.1.2.2 <;> simp [hu1, hv1]
        · have hb0 : (out.1.1 == 0) = false := beq_false_of_ne hu0
          have hb1 : (out.1.1 == 1) = false := beq_false_of_ne hu1
          simp [hb0, hb1]
  have htotal :
      (ProbComp.eval ((S.double hcap).indexedEufCmaGame adversary n)) true ≤
        (2 : ℝ≥0∞) *
          (ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n)) true := by
    rw [htwo]
    exact hgame.trans (add_le_add hslot0 hslot1)
  have hne : (2 : ℝ≥0∞) *
      (ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n)) true ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (PMF.apply_ne_top _ _)
  unfold Game.succProbability
  simpa only [ENNReal.toNNReal_mul, ENNReal.toNNReal_ofNat] using
    ENNReal.toNNReal_mono hne htotal

/-! ### Strict oracle-PPT efficiency of `doubleForger` -/

private abbrev DoubleCaller := (ℕ × Bool) × (List Bool × List Bool)

private noncomputable def encDoubleCaller : DoubleCaller ↪ List Bool :=
  encPair (encPair encUnary encBool) (encPair encBits encBits)

private abbrev DoubleHandlerIn :=
  DoubleCaller × ((Unit × List Bool) × List (ℕ × List Bool))

private noncomputable def encDoubleHandlerIn : DoubleHandlerIn ↪ List Bool :=
  encPair encDoubleCaller
    (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encUnary encBits)))

private theorem isOraclePPTOn_doubleHandler (S : IndexedSignatureScheme) {bound : ℕ → ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary) :
    IsOraclePPTOn encDoubleHandlerIn
      (encPair encBits (encList (encPair encUnary encBits)))
      (fun pair : DoubleHandlerIn =>
        S.doubleHandler pair.1.1.2 pair.1.2.2 bound pair.1.1.1 pair.2.1 pair.2.2) := by
  have hp := ComputableTidilyInPolyTime.id' (encIn := encDoubleHandlerIn)
  have hn := hp.fst'.fst'.fst'
  have hbFlag := hp.fst'.fst'.snd'
  have hotherSk := hp.fst'.snd'.snd'
  have hsigned := hp.snd'.snd'
  have hr := requestDecoder.computableInPolyTime.tidy.comp hp.snd'.fst'.snd'
  have hr1 := hr.fst'
  have hr2 := hr.snd'
  have hfreshDec : ComputableInPolyTime
      (fun pair : DoubleHandlerIn =>
        decide ((requestDecoder.decode pair.2.1.2).1 < 2 ∧
          (requestDecoder.decode pair.2.1.2).1 ∉ pair.2.2.map Prod.fst))
      encDoubleHandlerIn encBool := by
    have hused := ComputableTidilyInPolyTime.anyWithInput
      (test := fun (pair : DoubleHandlerIn) (e : ℕ × List Bool) =>
        (requestDecoder.decode pair.2.1.2).1 == e.1) hsigned
      (ComputableTidilyInPolyTime.unary_beq
        (hr1.comp (ComputableTidilyInPolyTime.fst encDoubleHandlerIn (encPair encUnary encBits)))
        (ComputableTidilyInPolyTime.snd encDoubleHandlerIn (encPair encUnary encBits)).fst')
    have hlt2 := hr1.unary_lt' (.const 2)
    have heq : (fun pair : DoubleHandlerIn =>
        decide ((requestDecoder.decode pair.2.1.2).1 < 2 ∧
          (requestDecoder.decode pair.2.1.2).1 ∉ pair.2.2.map Prod.fst)) =
      fun pair =>
        decide ((requestDecoder.decode pair.2.1.2).1 < 2) &&
          !(pair.2.2.any fun e => (requestDecoder.decode pair.2.1.2).1 == e.1) := by
      funext pair; rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
        List.mem_map, not_exists, not_and, beq_iff_eq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun e he h => h2 e he h.symm⟩,
        fun ⟨h1, h2⟩ => ⟨h1, fun e he h => h2 e he h.symm⟩⟩
    rw [heq]
    exact .of_tidy (hlt2.bool_and' (ComputableTidilyInPolyTime.bool_not.comp hused))
  have hslotDec : ComputableInPolyTime
      (fun pair : DoubleHandlerIn =>
        decide ((requestDecoder.decode pair.2.1.2).1 = pair.1.1.2.toNat))
      encDoubleHandlerIn encBool := by
    have htarget : ComputableTidilyInPolyTime (fun pair : DoubleHandlerIn => pair.1.1.2.toNat)
        encDoubleHandlerIn encUnary := by
      have heq : (fun pair : DoubleHandlerIn => pair.1.1.2.toNat) =
          fun pair => if pair.1.1.2 then 1 else 0 := by
        funext pair; cases pair.1.1.2 <;> rfl
      rw [heq]
      exact ComputableTidilyInPolyTime.ite' hbFlag (.const 1) (.const 0)
    have heq : (fun pair : DoubleHandlerIn =>
        decide ((requestDecoder.decode pair.2.1.2).1 = pair.1.1.2.toNat)) =
      fun pair => (requestDecoder.decode pair.2.1.2).1 == pair.1.1.2.toNat := by
      funext pair; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, beq_iff_eq]
    rw [heq]
    exact .of_tidy (ComputableTidilyInPolyTime.unary_beq hr1 htarget)
  have hb := hboundPoly.tidy.comp (hn.prod (ComputableTidilyInPolyTime.length_bits.comp hr2))
  have hq := ComputableTidilyInPolyTime.id' (encIn := encPair encDoubleHandlerIn encBits)
  have hconsLog : ComputableInPolyTime
      (fun p : DoubleHandlerIn × List Bool =>
        (p.2, requestDecoder.decode p.1.2.1.2 :: p.1.2.2))
      (encPair encDoubleHandlerIn encBits)
      (encPair encBits (encList (encPair encUnary encBits))) :=
    .of_tidy (hq.snd'.prod ((hr.comp hq.fst').cons' (hsigned.comp hq.fst')))
  change IsOraclePPTOn encDoubleHandlerIn (encPair encBits (encList (encPair encUnary encBits)))
    (fun pair =>
      if (requestDecoder.decode pair.2.1.2).1 < 2 ∧
          (requestDecoder.decode pair.2.1.2).1 ∉ pair.2.2.map Prod.fst then
        if (requestDecoder.decode pair.2.1.2).1 = pair.1.1.2.toNat then
          (fun sig => (sig, requestDecoder.decode pair.2.1.2 :: pair.2.2)) <$>
            (List.take (bound pair.1.1.1 (requestDecoder.decode pair.2.1.2).2.length) <$>
              ProbOracleComp.query
                ((), encPair encUnary encBits (0, (requestDecoder.decode pair.2.1.2).2)))
        else
          (fun sig => (sig, requestDecoder.decode pair.2.1.2 :: pair.2.2)) <$>
            ProbOracleComp.sample (S.sign pair.1.2.2 0 (requestDecoder.decode pair.2.1.2).2)
      else pure ([], pair.2.2))
  refine IsOraclePPTOn.ite' hfreshDec (IsOraclePPTOn.ite' hslotDec ?_ ?_)
    (((ComputableInPolyTime.const []).prod (.of_tidy hsigned)).isOraclePPTOn)
  · have hqword := ((ComputableTidilyInPolyTime.const (encMid := encUnary) 0).prod hr2).encoded
    exact (IsOraclePPTOn.query_take' () (.of_tidy hqword) (.of_tidy hb)).map_with' hconsLog
  · have hsignLocal := (S.sign_ppt.preprocess
      (.of_tidy (hotherSk.prod ((ComputableTidilyInPolyTime.const 0).prod hr2)))).map_with
      (f := fun pair sig => (sig, requestDecoder.decode pair.2.1.2 :: pair.2.2)) hconsLog
    simpa only [ProbOracleComp.sample_map, Function.comp_apply] using
      hsignLocal.isOraclePPTOn (Operation := Unit)

/-- `S.doubleForger bound adversary` is uniformly strict oracle PPT for every strict oracle-PPT
`adversary` and every plain polynomial-time bound `bound`. -/
theorem isOraclePPT_doubleForger (S : IndexedSignatureScheme) {bound : ℕ → ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary)
    {adversary : IndexedForger}
    (hadversary : IsOraclePPT (encPair encUnary (encPair encBits encBits)) adversary) :
    IsOraclePPT (encPair encUnary (encPair encBits encBits))
      (S.doubleForger bound adversary) := by
  obtain ⟨cs, ds, hlens⟩ := S.sign_ppt.length_le
  have hdec := requestDecoder.computableInPolyTime.tidy
  let resources (caller : DoubleCaller) (w : List Bool) : ℕ :=
    bound caller.1.1 (requestDecoder.decode w).2.length +
      cs * (2 * caller.2.2.length + w.length + 4) ^ ds + 2 * w.length + 12
  have hresources : ComputableInPolyTime
      (fun pair : DoubleCaller × List Bool => resources pair.1 pair.2)
      (encPair encDoubleCaller encBits) encUnary := by
    have hp := ComputableTidilyInPolyTime.id' (encIn := encPair encDoubleCaller encBits)
    have hn := hp.fst'.fst'.fst'
    have hotherSk := hp.fst'.snd'.snd'
    have hw := hp.snd'
    have hr2Len := ComputableTidilyInPolyTime.length_bits.comp (hdec.comp hw).snd'
    have hb := hboundPoly.tidy.comp (hn.prod hr2Len)
    have hskLen := ComputableTidilyInPolyTime.length_bits.comp hotherSk
    have hwLen := ComputableTidilyInPolyTime.length_bits.comp hw
    have h2sk := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hskLen)
    have hbase := ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.unary_add.comp (h2sk.prod hwLen)).prod (.const 4))
    have hpow := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const cs).prod
        ((ComputableTidilyInPolyTime.unary_pow ds).comp hbase))
    have h2w := ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const 2).prod hwLen)).prod (.const 12))
    exact .of_tidy (ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.unary_add.comp (hb.prod hpow)).prod h2w))
  have hprepare : ComputableInPolyTime
      (fun caller : DoubleCaller => (caller.1.1, caller.2.1))
      encDoubleCaller (encPair encUnary encBits) := by
    have hp := ComputableTidilyInPolyTime.id' (encIn := encDoubleCaller)
    exact .of_tidy (hp.fst'.fst'.prod hp.snd'.fst')
  have hrun : IsOraclePPTOn encDoubleCaller
      (encPair (encPair encUnary (encPair encBits encBits))
        (encList (encPair encUnary encBits)))
      (fun caller : DoubleCaller =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (S.doubleHandler caller.1.2 caller.2.2 bound caller.1.1))
          (adversary caller.1.1 caller.2.1)).run []) := by
    refine hadversary.run_interpret_preprocess_open'
      (prepare := fun caller : DoubleCaller => (caller.1.1, caller.2.1))
      (initial := fun _ => ([] : List (ℕ × List Bool)))
      (resources := resources)
      hprepare (isOraclePPTOn_doubleHandler S hboundPoly)
      (ComputableInPolyTime.const []) (fun _ _ => True) (fun _ => trivial) hresources ?_
    intro caller request signed _ result hresult
    have hmsg : (requestDecoder.decode request.2).2.length ≤ request.2.length :=
      length_dropFrame_le request.2
    unfold doubleHandler at hresult; dsimp only at hresult
    split_ifs at hresult with hfresh hslot
    · obtain ⟨sig, hsig, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hsig
      have htake := List.length_take_le
        (bound caller.1.1 (requestDecoder.decode request.2).2.length) raw
      have hu2 : (requestDecoder.decode request.2).1 < 2 := hfresh.1
      refine ⟨trivial, by dsimp only [resources]; omega, ?_⟩
      simp only [encList_cons, List.length_append, length_frame, length_encPair, encUnary_apply,
        encBits_apply, List.length_replicate, resources]; omega
    · obtain ⟨sig, hsig, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      have hsigMem : sig ∈ (ProbComp.eval
          (S.sign caller.2.2 0 (requestDecoder.decode request.2).2)).support :=
        (ProbOracleComp.support_sample _).subset hsig
      have hsigLen := hlens (caller.2.2, 0, (requestDecoder.decode request.2).2) sig hsigMem
      simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hsigLen
      have hpow :
          cs * (2 * caller.2.2.length + 1 + (2 * 0 + 1 +
            (requestDecoder.decode request.2).2.length) + 1) ^ ds ≤
          cs * (2 * caller.2.2.length + request.2.length + 4) ^ ds :=
        Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by omega) ds)
      have hu2 : (requestDecoder.decode request.2).1 < 2 := hfresh.1
      refine ⟨trivial, by dsimp only [resources]; omega, ?_⟩
      simp only [encList_cons, List.length_append, length_frame, length_encPair, encUnary_apply,
        encBits_apply, List.length_replicate, resources]; omega
    · obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, by simp, by dsimp only [resources]; omega⟩
  have hpost : ComputableInPolyTime
      (fun pair : DoubleCaller ×
          ((ℕ × List Bool × List Bool) × List (ℕ × List Bool)) =>
        (0, pair.2.1.2.1, pair.2.1.2.2))
      (encPair encDoubleCaller
        (encPair (encPair encUnary (encPair encBits encBits))
          (encList (encPair encUnary encBits))))
      (encPair encUnary (encPair encBits encBits)) := by
    have hout := (ComputableInPolyTime.snd encDoubleCaller
      (encPair (encPair encUnary (encPair encBits encBits))
        (encList (encPair encUnary encBits)))).fst'
    exact (ComputableInPolyTime.const 0).prod hout.snd'
  have hstep3 : IsOraclePPTOn encDoubleCaller (encPair encUnary (encPair encBits encBits))
      (fun caller : DoubleCaller => do
        let out ← (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (S.doubleHandler caller.1.2 caller.2.2 bound caller.1.1))
          (adversary caller.1.1 caller.2.1)).run []
        return (0, out.1.2.1, out.1.2.2)) :=
    hrun.bind_with
      (second := fun (_ : DoubleCaller) out =>
        (pure (0, out.1.2.1, out.1.2.2) : WordOracleComp Unit (ℕ × List Bool × List Bool)))
      (hpost.isOraclePPTOn (Operation := Unit))
  have hstep2 : IsOraclePPTOn (encPair (encPair encUnary encBits) encBool)
      (encPair encUnary (encPair encBits encBits))
      (fun p : (ℕ × List Bool) × Bool => S.doubleForgerAt bound adversary p.2 p.1.1 p.1.2) := by
    let encP := encPair (encPair (encPair encUnary encBits) encBool) (encPair encBits encBits)
    have hp := ComputableTidilyInPolyTime.id' (encIn := encP)
    have hb := hp.fst'.snd'
    have hvk := hp.fst'.fst'.snd'
    have hopk := hp.snd'.fst'
    have hplant := hb.ite' (hopk.prod hvk).encoded (hvk.prod hopk).encoded
    have hotherClosed : IsPPTOn (encPair (encPair encUnary encBits) encBool)
        encDoubleCaller
        (fun p : (ℕ × List Bool) × Bool =>
          (fun other => ((p.1.1, p.2), (doublePlantPk p.2 p.1.2 other.1, other.2))) <$>
            S.keyGen p.1.1) :=
      (S.keyGen_ppt.preprocess
        (ComputableInPolyTime.fst (encPair encUnary encBits) encBool).fst').map_with
        (.of_tidy ((hp.fst'.fst'.fst'.prod hb).prod (hplant.prod hp.snd'.snd')))
    have hother : IsOraclePPTOn (Operation := Unit) (encPair (encPair encUnary encBits) encBool)
        encDoubleCaller
        (fun p : (ℕ × List Bool) × Bool =>
          (fun other => ((p.1.1, p.2), (doublePlantPk p.2 p.1.2 other.1, other.2))) <$>
            ProbOracleComp.sample (S.keyGen p.1.1)) := by
      simpa only [ProbOracleComp.sample_map] using hotherClosed.isOraclePPTOn (Operation := Unit)
    refine (hother.bind hstep3).congr fun p State oracle st => ?_
    simp only [doubleForgerAt, StateT.run, bind_map_left]
  exact ((isPPTOn_uniform_bool (encPair encUnary encBits)).isOraclePPTOn
    (Operation := Unit)).bind_with hstep2

/-! ### Security preservation -/

/-- **Doubling preserves `IndexedEUFCMA`** ([BonehShoup2023], Section 14.6.1, construction `(14.4)`
at `q = 2`): if `S` is indexed EUF-CMA secure with `∀ n, 1 ≤ S.capacity n`, then `S.double hcap`
is indexed EUF-CMA secure of capacity `2`. -/
theorem IndexedEUFCMA.double {S : IndexedSignatureScheme} (hS : S.IndexedEUFCMA)
    (hcap : ∀ n, 1 ≤ S.capacity n) :
    (S.double hcap).IndexedEUFCMA := by
  obtain ⟨ck, dk, hlenk⟩ := S.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := S.sign_ppt.length_le
  obtain ⟨bound, hboundPoly, hbound⟩ : ∃ bound : ℕ → ℕ → ℕ,
      ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2) (encPair encUnary encUnary) encUnary ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg,
        ∀ σ ∈ (ProbComp.eval (S.sign keys.2 0 msg)).support, σ.length ≤ bound n msg.length := by
    have hp := ComputableTidilyInPolyTime.id' (encIn := encPair encUnary encUnary)
    have hn1 := ComputableTidilyInPolyTime.unary_add.comp (hp.fst'.prod (.const 1))
    have hck := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const ck).prod
        ((ComputableTidilyInPolyTime.unary_pow dk).comp hn1))
    have h2ck := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hck)
    have hbase := ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.unary_add.comp (h2ck.prod hp.snd')).prod (.const 3))
    refine ⟨fun n L => cs * (2 * (ck * (n + 1) ^ dk) + L + 3) ^ ds,
      .of_tidy (ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const cs).prod
          ((ComputableTidilyInPolyTime.unary_pow ds).comp hbase))),
      fun n keys hkeys msg σ hσ => ?_⟩
    have hkeyLen := hlenk n keys hkeys
    simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at hkeyLen
    have hσLen := hlens (keys.2, 0, msg) σ hσ
    simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hσLen
    refine hσLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left ?_ ds))
    omega
  apply IndexedEUFCMA.of_negligible
  intro adversary hadversary
  have hneg := hS.negligible (S.doubleForger bound adversary)
    (isOraclePPT_doubleForger S hboundPoly hadversary)
  refine negligible_of_le (hneg.const_mul 2) fun n => ?_
  simpa only [Pi.mul_apply] using
    succProbability_indexedEufCmaGame_double_le hcap (hbound n) adversary

end IndexedSignatureScheme

end Cslib.Crypto

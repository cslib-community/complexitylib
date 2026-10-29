/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.NaorReingold
public import Complexity.Crypto.Computational.DiffieHellman.Order
public import Complexity.Crypto.Computational.ElGamal.KDF
public import Complexity.Crypto.Computational.PseudorandomFunction.RandomOracle
import Complexity.Computability.Probabilistic.LinearHash
import Complexity.Computability.Probabilistic.Memoize
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Crypto.Game.Hybrid
import Complexity.Crypto.Game.Statistical
import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Languages.Probabilistic.Presample
import Complexity.Languages.Probabilistic.RandomOracle.Probabilistic
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.StatisticalDistance.Product
import Complexity.Tactic.PPT

/-!
# Computational security of the Naor–Reingold PRF from DDH

This module completes the efficient lazy-sampling Decisional Diffie–Hellman (`DDH`) reduction and
the universal-hash bit-string pseudorandom-function bridge for the Naor–Reingold PRF over a
`PrimeOrderGroupFamily` ([BonehShoup2023], Section 10.11, Exercises 10.4, 10.8, 10.11, pp. 424–426,
and Section 4.11, Exercise 4.18, p. 172; [NaorReingold2004], Section 4.1, Construction 4.1,
Theorem 4.1, Lemma 4.2, Construction 4.2, Theorem 4.3, and Remark 4.2):

1. **Inverse-order bound from `DDH`:** `DDH.negligible_expected_inv_order`, imported from
   `Complexity.Crypto.Computational.DiffieHellman.Order`, makes the setup-averaged inverse group
   order negligible; it bounds the hashed-PRF error terms below.
2. **Word-level adaptive group-PRF games and lazy-sampling `IsOraclePPT` DDH reduction:**
   `naorReingoldFrontierOracle` memoizes `ddhFixedUWordRerandomize` only on the `k`-bit prefixes
   queried by an `OracleDistinguisher` and evaluates the remaining suffix via
   `naorReingoldWordSuffix`. Choosing `k ← sampleDyadicIndex (inLen n)` yields the uniform strict
   PPT DDH distinguisher `naorReingoldToDDHDistinguisher`, proving both quantitative single-
   distinguisher bounds and asymptotic security (`DDH.negligible_naorReingoldWordGame`,
   `DDH.negligible_naorReingoldProbGame`) under `F.DDH setup` alone.
3. **Universal-hash bit-string Naor–Reingold PRF (paraphrase of [NaorReingold2004], Section 4.1,
   Construction 4.2, Theorem 4.3, and Remark 4.2, using Lemma 4.2):** composing
   `naorReingoldWordEval` with `linearHashKDF` under a public universal-hash seed (`F.withSeed` and
   `F.seededSetup`) maps group outputs into uniform `outLen n`-bit strings; a multi-query Leftover
   Hash Lemma bound via `PMF.dist_bind_pair_pi_le_sum` yields adaptive bit-string PRF security
   (`DDH.negligible_naorReingoldHashedGame`, `DDH.negligible_naorReingoldHashedProbGame`, and
   `DDH.negligible_naorReingoldHashedGame_const`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.sampleNaorReingoldExp`: executable modular exponent sampler
  with statistical slack `n + (F.encDesc d).length`.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldWordRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldProbRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldWordIdealGame`: setup-parameterized word-level
  adaptive Naor–Reingold group-PRF experiments.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldFrontierOracle`: memoized prefix DDH
  rerandomization followed by `naorReingoldWordSuffix`.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldToDDHDistinguisher`: single-challenge uniform
  strict PPT DDH distinguisher constructed from an adaptive PRF distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedWordEval`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedProbRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedGroupIdealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedIdealGame`: universal-hash bit-string
  Naor–Reingold evaluation and setup-parameterized PRF experiments.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_naorReingoldToDDHDistinguisher`: uniform strict PPT
  certificate for `naorReingoldToDDHDistinguisher` from any `IsOraclePPT` distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingoldWordGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingoldProbRealGame_wordRealGame_le`:
  quantitative single-distinguisher DDH reduction and modular-sampling bounds for the group-PRF.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldWordGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldProbGame`: asymptotic adaptive
  security of the Naor–Reingold group-PRF under `F.DDH setup`.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_naorReingoldHashedWordEval`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingoldHashedIdeal_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldHashedGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldHashedProbGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldHashedGame_const`: polynomial-time
  evaluation, multi-query Leftover Hash Lemma bound, and asymptotic bit-string PRF security.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.11 (Exercise 4.18, p. 172) and Section 10.11
  (Exercises 10.4, 10.8, and 10.11, pp. 424–426).
* [M. Naor, O. Reingold, *Number-Theoretic Constructions of Efficient Pseudo-Random
  Functions*][NaorReingold2004], Section 4.1 (Construction 4.1, Theorem 4.1, Lemma 4.2,
  Construction 4.2, Theorem 4.3, and Remark 4.2).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Probability.PMF Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

variable (F : PrimeOrderGroupFamily)

private instance carrier_finite (F : PrimeOrderGroupFamily) (d : F.Desc) : Finite (F.Carrier d) :=
  Finite.of_surjective _ (F.smul_generator_surjective d)

/-! ### Word-level Naor–Reingold group-PRF games and prefix hybrids -/

/-- Sample a nearly-uniform modular exponent modulo `F.order d` via `F.sampleExp` with
`n + (F.encDesc d).length` statistical slack bits so that the statistical error
`1 / 2 ^ (n + |encDesc d|)` offsets polynomial query counts depending on `|encDesc d|`
(original). -/
noncomputable def sampleNaorReingoldExp (n : ℕ) (d : F.Desc) : ProbComp ℕ :=
  F.sampleExp (n + (F.encDesc d).length) d

/-- Every value supported by `sampleNaorReingoldExp` is strictly less than `F.order d`. -/
theorem lt_order_of_mem_support_sampleNaorReingoldExp {n : ℕ} {d : F.Desc} {v : ℕ}
    (hv : v ∈ (ProbComp.eval (F.sampleNaorReingoldExp n d)).support) :
    v < F.order d := by
  simp only [sampleNaorReingoldExp, sampleExp, ProbComp.eval_sampleModNat,
    PMF.mem_support_map_iff] at hv
  obtain ⟨x, _, rfl⟩ := hv
  exact Nat.mod_lt _ (F.prime_order d).pos

/-- Projected to `ZMod (F.order d)`, `sampleNaorReingoldExp n d` has law
`F.sampleModZModLaw (n + (F.encDesc d).length) d`. -/
theorem map_natCast_eval_sampleNaorReingoldExp (n : ℕ) (d : F.Desc) :
    (ProbComp.eval (F.sampleNaorReingoldExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)) =
      F.sampleModZModLaw (n + (F.encDesc d).length) d := by
  simp only [sampleNaorReingoldExp, sampleExp, sampleModZModLaw]
  have hlen : (n + (F.encDesc d).length) + (encNat (F.order d)).length =
      (F.order d).size + (n + (F.encDesc d).length) := by
    rw [encNat_apply, ← Nat.size_eq_bits_len, Nat.add_comm]
  rw [hlen]

/-- `sampleNaorReingoldExp` is uniform strict PPT in `(n, d)`. -/
@[fun_prop]
theorem isPPTOn_sampleNaorReingoldExp {α : Type} {input : α ↪ List Bool}
    {param : α → ℕ} {desc : α → F.Desc}
    (hparam : ComputableInPolyTime param input encUnary)
    (hdesc : ComputableInPolyTime desc input F.encDesc) :
    IsPPTOn input encNat (fun a => F.sampleNaorReingoldExp (param a) (desc a)) := by
  have hdlen : ComputableInPolyTime (fun a => (F.encDesc (desc a)).length) input encUnary :=
    (ComputableInPolyTime.encoding_length F.encDesc).comp hdesc
  have hadd : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  exact F.isPPTOn_sampleExp (hadd.comp (hparam.prod hdlen)) hdesc

/-- Deterministic word-level oracle wrapper encoding `fn : BitString m → F.Carrier d` on valid
`m`-bit queries and returning `[]` on malformed queries. -/
@[expose] def naorReingoldWordOracle (d : F.Desc) {m : ℕ} (fn : BitString m → F.Carrier d)
    (query : List Bool) : List Bool :=
  if query.length = m then F.encode d (fn (BitString.ofList m query)) else []

/-- Run a randomized word-level oracle program against `naorReingoldWordOracle d fn`. -/
private noncomputable def naorReingoldWordRun (F : PrimeOrderGroupFamily) (d : F.Desc) {m : ℕ}
    (prog : WordOracleComp Unit Bool) (fn : BitString m → F.Carrier d) : PMF Bool :=
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifOracle fun request =>
      PMF.pure (F.naorReingoldWordOracle d fn request.2))
    prog

/-- Setup-parameterized real Naor–Reingold group-PRF game with exact uniform `ZMod (F.order d)`
exponents ([BonehShoup2023], Exercise 10.4, p. 424; [NaorReingold2004], Construction 4.1 &
Theorem 4.1). -/
@[expose] noncomputable def naorReingoldWordRealGame (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let α₀ ← PMF.uniformOfFintype (ZMod (F.order d))
  let α ← PMF.uniformOfFintype (Fin (inLen n) → ZMod (F.order d))
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifOracle fun request =>
      PMF.pure (F.naorReingoldWordOracle d (F.naorReingoldEval d α₀ α) request.2))
    (adversary n (F.encDesc d))

/-- Setup-parameterized executable Naor–Reingold group-PRF real game sampling modular exponents via
`sampleNaorReingoldExp` (original). -/
@[expose] noncomputable def naorReingoldProbRealGame (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  ProbComp.eval (do
    let α₀ ← F.sampleNaorReingoldExp n d
    let αs ← OracleComp.replicate (inLen n) (F.sampleNaorReingoldExp n d)
    OracleComp.interpret
      (ProbOracleComp.handler ProbComp.unifFin fun request =>
        pure (if request.2.length = inLen n then
          F.naorReingoldWordEval d α₀ αs request.2 else []))
      (adversary n (F.encDesc d)))

/-- Setup-parameterized ideal random group-function game against `OracleDistinguisher`
([BonehShoup2023], Exercise 10.4, p. 424; [NaorReingold2004], Theorem 4.1). -/
@[expose] noncomputable def naorReingoldWordIdealGame (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let B ← PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order d))
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifOracle fun request =>
      PMF.pure (F.naorReingoldWordOracle d (fun x => B x • F.generator d) request.2))
    (adversary n (F.encDesc d))

private noncomputable def naorReingoldWordHybridAt (F : PrimeOrderGroupFamily) (d : F.Desc)
    (m k : ℕ) (prog : WordOracleComp Unit Bool) : Game := do
  let B ← PMF.uniformOfFintype (BitString k → ZMod (F.order d))
  let α ← PMF.uniformOfFintype (Fin m → ZMod (F.order d))
  naorReingoldWordRun F d prog (F.naorReingoldHybridEval d k B α)

private theorem naorReingoldWordHybridAt_zero (F : PrimeOrderGroupFamily) (d : F.Desc) (m : ℕ)
    (prog : WordOracleComp Unit Bool) :
    naorReingoldWordHybridAt F d m 0 prog =
      (do
        let α₀ ← PMF.uniformOfFintype (ZMod (F.order d))
        let α ← PMF.uniformOfFintype (Fin m → ZMod (F.order d))
        naorReingoldWordRun F d prog (F.naorReingoldEval d α₀ α)) := by
  let e : ZMod (F.order d) ≃ (BitString 0 → ZMod (F.order d)) :=
    (Equiv.funUnique (BitString 0) (ZMod (F.order d))).symm
  simp only [naorReingoldWordHybridAt, PMF.monad_bind_eq_bind]
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
  congr 1; funext α₀
  dsimp only [Function.comp_apply]
  congr 1; funext α
  refine congrArg (naorReingoldWordRun F d prog) (funext fun x => ?_)
  simp [naorReingoldHybridEval, naorReingoldEval, e]

private theorem naorReingoldWordHybridAt_self (F : PrimeOrderGroupFamily) (d : F.Desc) (m : ℕ)
    (prog : WordOracleComp Unit Bool) :
    naorReingoldWordHybridAt F d m m prog =
      (do
        let B ← PMF.uniformOfFintype (BitString m → ZMod (F.order d))
        naorReingoldWordRun F d prog (fun x => B x • F.generator d)) := by
  simp only [naorReingoldWordHybridAt, PMF.monad_bind_eq_bind]
  congr 1; funext B
  have hfn (α : Fin m → ZMod (F.order d)) :
      F.naorReingoldHybridEval d m B α = fun x => B x • F.generator d := by
    funext x
    simp [naorReingoldHybridEval]
  simp_rw [hfn, PMF.bind_const]

private def shiftFinAtEquiv {m : ℕ} {α : Type*} [AddGroup α] (i : Fin m) (δ : α) :
    (Fin m → α) ≃ (Fin m → α) where
  toFun f := Function.update f i (f i + δ)
  invFun f := Function.update f i (f i - δ)
  left_inv f := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  right_inv f := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]

private theorem uniformOfFintype_bind_update_fin {m : ℕ} {α β : Type*}
    [AddGroup α] [Fintype α] [Nonempty α] (i : Fin m) (g : (Fin m → α) → PMF β) :
    ((PMF.uniformOfFintype α).bind fun a =>
      (PMF.uniformOfFintype (Fin m → α)).bind fun f =>
        g (Function.update f i a)) =
    (PMF.uniformOfFintype (Fin m → α)).bind g := by
  rw [PMF.bind_comm]
  have h1 (f : Fin m → α) :
      ((PMF.uniformOfFintype α).bind fun a => g (Function.update f i a)) =
      ((PMF.uniformOfFintype α).bind fun δ => g (shiftFinAtEquiv i δ f)) := by
    change (PMF.uniformOfFintype α).bind (fun a => g (Function.update f i a)) =
      (PMF.uniformOfFintype α).bind
        ((fun a => g (Function.update f i a)) ∘ Equiv.addLeft (f i))
    rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]
  simp_rw [h1]
  rw [PMF.bind_comm]
  have h2 (δ : α) :
      ((PMF.uniformOfFintype (Fin m → α)).bind fun f => g (shiftFinAtEquiv i δ f)) =
      (PMF.uniformOfFintype (Fin m → α)).bind g := by
    change (PMF.uniformOfFintype (Fin m → α)).bind (g ∘ shiftFinAtEquiv i δ) = _
    rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]
  simp_rw [h2, PMF.bind_const]

private def wordPrefixTableEquiv (α : Type*) (k : ℕ) :
    (BitString k → α × α) ≃ (BitString (k + 1) → α) :=
  ((Equiv.piCongrRight fun _ : BitString k =>
      { toFun := fun (p : α × α) (b : Bool) => if b then p.2 else p.1
        invFun := fun f => (f false, f true)
        left_inv := fun _ => by simp
        right_inv := fun f => by funext b; cases b <;> rfl }).trans
    (Equiv.curry (BitString k) Bool α).symm).trans
    (Equiv.arrowCongr
      ((Fin.snocEquiv fun _ : Fin (k + 1) => Bool).symm.trans (Equiv.prodComm _ _)).symm
      (Equiv.refl α))

private noncomputable def naorReingoldWordLevelTest (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) (_u : F.Carrier d)
    (T : BitString k → F.Carrier d × F.Carrier d) : PMF Bool := do
  let suffix ← PMF.uniformOfFintype (Fin (m - (k + 1)) → ZMod (F.order d))
  let α : Fin m → ZMod (F.order d) := fun i =>
    if h : k + 1 ≤ i.val then suffix ⟨i.val - (k + 1), by omega⟩ else 1
  naorReingoldWordRun F d prog (F.naorReingoldTableEval d k hk T α)

private theorem naorReingoldSuffixExp_extend_suffix (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m k : ℕ} (α : Fin m → ZMod (F.order d)) (x : BitString m) :
    F.naorReingoldSuffixExp d (k + 1)
      (fun i : Fin m =>
        if h : k + 1 ≤ i.val then α ⟨k + 1 + (i.val - (k + 1)), by omega⟩ else 1) x =
      F.naorReingoldSuffixExp d (k + 1) α x := by
  unfold naorReingoldSuffixExp
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : k + 1 ≤ i.val
  · have heq : (⟨k + 1 + (i.val - (k + 1)), by omega⟩ : Fin m) = i := by
      ext
      dsimp
      omega
    dsimp only
    simp only [hi, ↓reduceDIte, true_and]
    rw [heq]
  · simp [hi]

private theorem naorReingoldWordLevelTest_eq_uniform_full (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) (u : F.Carrier d) :
    naorReingoldWordLevelTest F d k hk prog u =
      fun T => (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
        naorReingoldWordRun F d prog (F.naorReingoldTableEval d k hk T α) := by
  funext T
  let splitEquiv : (Fin m → ZMod (F.order d)) ≃
      ((Fin (m - (k + 1)) → ZMod (F.order d)) × (Fin (k + 1) → ZMod (F.order d))) :=
    ((Equiv.arrowCongr
      ((finSumFinEquiv (m := k + 1) (n := m - (k + 1))).trans
        (Fin.castOrderIso (Nat.add_sub_of_le hk)).toEquiv).symm
      (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)).trans (Equiv.prodComm _ _)
  have hproj :
      (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).map
        (fun α : Fin m → ZMod (F.order d) =>
          fun j : Fin (m - (k + 1)) => α ⟨k + 1 + j.val, by omega⟩) =
      PMF.uniformOfFintype (Fin (m - (k + 1)) → ZMod (F.order d)) := by
    have hcomp :
        (fun α : Fin m → ZMod (F.order d) =>
          fun j : Fin (m - (k + 1)) => α ⟨k + 1 + j.val, by omega⟩) =
        Prod.fst ∘ splitEquiv := by
      funext α j
      rfl
    rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_prod_map_fst]
  simp only [naorReingoldWordLevelTest, PMF.monad_bind_eq_bind]
  rw [← hproj, PMF.bind_map]
  congr 1; funext α
  dsimp only [Function.comp_apply]
  refine congrArg (naorReingoldWordRun F d prog) (funext fun x => ?_)
  simp only [naorReingoldTableEval, naorReingoldSuffixExp_extend_suffix F d α x]

private theorem multiDDHRealTupleLaw_naorReingoldWordLevelTest (F : PrimeOrderGroupFamily)
    (d : F.Desc) {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α_k =>
      (F.multiDDHRealTupleLaw d (BitString k) α_k).bind
        (naorReingoldWordLevelTest F d k hk prog (α_k • F.generator d))) =
      naorReingoldWordHybridAt F d m k prog := by
  simp_rw [naorReingoldWordLevelTest_eq_uniform_full F d k hk prog]
  simp only [multiDDHRealTupleLaw, naorReingoldWordHybridAt, PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))
    (PMF.uniformOfFintype (BitString k → ZMod (F.order d)))]
  congr 1; funext B
  have hfn (α_k : ZMod (F.order d)) (α : Fin m → ZMod (F.order d)) :
      F.naorReingoldTableEval d k hk
        (fun i => (B i • F.generator d, (α_k * B i) • F.generator d)) α =
      F.naorReingoldHybridEval d k B (Function.update α ⟨k, hk⟩ α_k) := by
    funext x
    rw [naorReingoldTableEval, naorReingoldHybridEval,
      F.naorReingoldSuffixExp_eq_mul_succ d hk (Function.update α ⟨k, hk⟩ α_k) x,
      F.naorReingoldSuffixExp_succ_update d hk α α_k x]
    simp only [Function.update_self]
    rcases Bool.eq_false_or_eq_true (x ⟨k, hk⟩) with hxk | hxk
    · simp only [hxk, ↓reduceIte, smul_smul]
      exact congrArg (· • F.generator d) (by ring)
    · simp [hxk, smul_smul, mul_comm]
  simp_rw [hfn]
  exact uniformOfFintype_bind_update_fin ⟨k, hk⟩
    (fun α => naorReingoldWordRun F d prog (F.naorReingoldHybridEval d k B α))

private theorem multiDDHIdealTupleLaw_naorReingoldWordLevelTest (F : PrimeOrderGroupFamily)
    (d : F.Desc) {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α_k =>
      (F.multiDDHIdealTupleLaw d (BitString k)).bind
        (naorReingoldWordLevelTest F d k hk prog (α_k • F.generator d))) =
      naorReingoldWordHybridAt F d m (k + 1) prog := by
  simp_rw [naorReingoldWordLevelTest_eq_uniform_full F d k hk prog]
  rw [PMF.bind_const]
  simp only [multiDDHIdealTupleLaw, naorReingoldWordHybridAt, PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def]
  rw [← PMF.uniformOfFintype_map_equiv (wordPrefixTableEquiv (ZMod (F.order d)) k), PMF.bind_map]
  congr 1; funext B
  dsimp only [Function.comp_apply]
  congr 1; funext α
  refine congrArg (naorReingoldWordRun F d prog) (funext fun x => ?_)
  rw [naorReingoldTableEval, naorReingoldHybridEval]
  have hpref :
      wordPrefixTableEquiv (ZMod (F.order d)) k B (BitString.zeroExtend (d' := k + 1) x) =
        if x ⟨k, hk⟩ then (B (BitString.zeroExtend (d' := k) x)).2
        else (B (BitString.zeroExtend (d' := k) x)).1 := by
    change (if BitString.zeroExtend (d' := k + 1) x (Fin.last k) then
        (B (Fin.init (BitString.zeroExtend (d' := k + 1) x))).2
      else (B (Fin.init (BitString.zeroExtend (d' := k + 1) x))).1) = _
    rw [BitString.init_zeroExtend_succ, BitString.last_zeroExtend_succ hk]
  rw [hpref]
  rcases Bool.eq_false_or_eq_true (x ⟨k, hk⟩) with hxk | hxk <;>
    simp [hxk, smul_smul, mul_comm]

/-! ### Lazy-sampling frontier oracle and `IsOraclePPT` DDH distinguisher -/

/-- Association-list cache mapping queried `k`-bit prefixes to encoded group-element pairs. -/
abbrev NaorReingoldCache := List (List Bool × (List Bool × List Bool))

/-- Encoding of `NaorReingoldCache`. -/
def naorReingoldCacheEncoding : NaorReingoldCache ↪ List Bool :=
  encList (encPair encBits (encPair encBits encBits))

/-- Executable rerandomized pair sampler for `naorReingoldFrontierOracle`: draw two exponents via
`sampleNaorReingoldExp` and apply `ddhFixedUWordRerandomize`. -/
noncomputable def sampleNaorReingoldPair (n : ℕ) (d : F.Desc) (u v w : List Bool) :
    ProbComp (List Bool × List Bool) := do
  let σ ← F.sampleNaorReingoldExp n d
  let τ ← F.sampleNaorReingoldExp n d
  return F.ddhFixedUWordRerandomize d u v w σ τ

/-- Stateful level-`k` frontier oracle for Naor–Reingold ([BonehShoup2023], Exercises 10.4(b) &
4.18(b); [NaorReingold2004], Theorem 4.1): on a valid `m`-bit query, memoize a freshly
rerandomized DDH pair on `query.take k`, select the `query[k]` child, and evaluate the remaining
suffix with `naorReingoldWordSuffix`. Malformed queries return `[]` without modifying the cache. -/
noncomputable def naorReingoldFrontierOracle (n m k : ℕ) (d : F.Desc) (u v w : List Bool)
    (αs : List ℕ) (query : List Bool) : StateT NaorReingoldCache ProbComp (List Bool) :=
  fun cache =>
    if query.length = m then do
      let (vw, cache') ← memoize (fun _ : List Bool => F.sampleNaorReingoldPair n d u v w)
        (query.take k) cache
      let child := if query.getD k false then vw.2 else vw.1
      return (F.naorReingoldWordSuffix d child αs (query.drop (k + 1)), cache')
    else pure ([], cache)

private noncomputable def naorReingoldDescToDDHDistinguisher (F : PrimeOrderGroupFamily)
    (inLen : ℕ → ℕ) (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let m := inLen n
  let k ← ProbComp.sampleDyadicIndex m
  if k < m then do
    let αs ← OracleComp.replicate (m - (k + 1)) (F.sampleNaorReingoldExp n input.1)
    Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifFin r))
        (fun request => F.naorReingoldFrontierOracle n m k input.1
          input.2.1 input.2.2.1 input.2.2.2 αs request.2))
      (adv n input.1)).run []
  else pure false

/-- Single-challenge uniform strict PPT DDH distinguisher constructed from an adaptive PRF
distinguisher `adversary`: sample a hybrid level `k ← sampleDyadicIndex (inLen n)`, draw suffix
exponents `αs`, and run `adversary` against `naorReingoldFrontierOracle` from an empty cache
([BonehShoup2023], Exercises 10.4(b) & 10.11; [NaorReingold2004], Theorem 4.1). -/
noncomputable def naorReingoldToDDHDistinguisher (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let m := inLen n
  let k ← ProbComp.sampleDyadicIndex m
  if k < m then do
    let αs ← OracleComp.replicate (m - (k + 1)) (F.sampleNaorReingoldExp n input.1)
    Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifFin r))
        (fun request => F.naorReingoldFrontierOracle n m k input.1
          input.2.1 input.2.2.1 input.2.2.2 αs request.2))
      (adversary n (F.encDesc input.1))).run []
  else pure false

private theorem isPPTOn_sampleNaorReingoldPair (F : PrimeOrderGroupFamily)
    {α : Type} {input : α ↪ List Bool}
    {param : α → ℕ} {desc : α → F.Desc} {u v w : α → List Bool}
    (hparam : ComputableInPolyTime param input encUnary)
    (hdesc : ComputableInPolyTime desc input F.encDesc)
    (hu : ComputableInPolyTime u input encBits)
    (hv : ComputableInPolyTime v input encBits)
    (hw : ComputableInPolyTime w input encBits) :
    IsPPTOn input (encPair encBits encBits)
      (fun a => F.sampleNaorReingoldPair (param a) (desc a) (u a) (v a) (w a)) := by
  have hsample := F.isPPTOn_sampleNaorReingoldExp hparam hdesc
  have hrerand := F.computableInPolyTime_ddhFixedUWordRerandomize
  unfold sampleNaorReingoldPair
  refine hsample.bind_with ?_
  refine (hsample.preprocess (prepare := Prod.fst) (by fun_prop)).bind_with ?_
  refine ComputableInPolyTime.isPPTOn ?_
  exact hrerand.comp
    ((hdesc.comp (by fun_prop)).prod
      ((hu.comp (by fun_prop)).prod
        ((hv.comp (by fun_prop)).prod
          ((hw.comp (by fun_prop)).prod
            ((by fun_prop : ComputableInPolyTime
                (fun p : (α × ℕ) × ℕ => p.1.2)
                (encPair (encPair input encNat) encNat) encNat).prod
              (by fun_prop))))))

attribute [local fun_prop] isPPTOn_sampleNaorReingoldPair

private theorem isPPTOn_naorReingoldFrontierOracle (F : PrimeOrderGroupFamily)
    {α : Type} {input : α ↪ List Bool}
    {param m k : α → ℕ} {desc : α → F.Desc} {u v w : α → List Bool}
    {αs : α → List ℕ} {query : α → List Bool} {cache : α → NaorReingoldCache}
    (hparam : ComputableInPolyTime param input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hk : ComputableInPolyTime k input encUnary)
    (hdesc : ComputableInPolyTime desc input F.encDesc)
    (hu : ComputableInPolyTime u input encBits)
    (hv : ComputableInPolyTime v input encBits)
    (hw : ComputableInPolyTime w input encBits)
    (hαs : ComputableInPolyTime αs input (encList encNat))
    (hquery : ComputableInPolyTime query input encBits)
    (hcache : ComputableInPolyTime cache input naorReingoldCacheEncoding) :
    IsPPTOn input (encPair encBits naorReingoldCacheEncoding)
      (fun a => F.naorReingoldFrontierOracle (param a) (m a) (k a) (desc a)
        (u a) (v a) (w a) (αs a) (query a) (cache a)) := by
  have hpair := isPPTOn_sampleNaorReingoldPair F hparam hdesc hu hv hw
  have htake : ComputableInPolyTime (fun a => (query a).take (k a)) input encBits := by
    have hq_t := hquery.tidy
    have hk_t := hk.tidy
    exact .of_tidy (by fun_prop)
  have hmemo : IsPPTOn input (encPair (encPair encBits encBits) naorReingoldCacheEncoding)
      (fun a => memoize (fun _ : List Bool =>
        F.sampleNaorReingoldPair (param a) (desc a) (u a) (v a) (w a))
        ((query a).take (k a)) (cache a)) := by
    unfold naorReingoldCacheEncoding
    exact IsPPTOn.memoize hpair htake hcache
  have hpost : ComputableInPolyTime
      (fun p : α × (List Bool × List Bool) × NaorReingoldCache =>
        let child := if (query p.1).getD (k p.1) false then p.2.1.2 else p.2.1.1
        (F.naorReingoldWordSuffix (desc p.1) child (αs p.1) ((query p.1).drop (k p.1 + 1)), p.2.2))
      (encPair input (encPair (encPair encBits encBits) naorReingoldCacheEncoding))
      (encPair encBits naorReingoldCacheEncoding) := by
    let EP := encPair input (encPair (encPair encBits encBits) naorReingoldCacheEncoding)
    have hp1 : ComputableInPolyTime (fun p : α × (List Bool × List Bool) × NaorReingoldCache => p.1)
        EP input := by fun_prop
    have hq_t := (hquery.comp hp1).tidy
    have hk_t := (hk.comp hp1).tidy
    have hk1_t : ComputableTidilyInPolyTime
        (fun p : α × (List Bool × List Bool) × NaorReingoldCache => k p.1 + 1) EP encUnary := by
      polytime
    have hv1 : ComputableTidilyInPolyTime
        (fun p : α × (List Bool × List Bool) × NaorReingoldCache => p.2.1.1) EP encBits := by
      fun_prop
    have hv2 : ComputableTidilyInPolyTime
        (fun p : α × (List Bool × List Bool) × NaorReingoldCache => p.2.1.2) EP encBits := by
      fun_prop
    have hbit : ComputableTidilyInPolyTime
        (fun p : α × (List Bool × List Bool) × NaorReingoldCache =>
          (query p.1).getD (k p.1) false) EP encBool :=
      (ComputableTidilyInPolyTime.bitsGetD false).comp (hq_t.prod hk_t)
    have hchild : ComputableInPolyTime
        (fun p : α × (List Bool × List Bool) × NaorReingoldCache =>
          if (query p.1).getD (k p.1) false then p.2.1.2 else p.2.1.1) EP encBits :=
      .of_tidy (hbit.ite' hv2 hv1)
    have hdrop : ComputableInPolyTime
        (fun p : α × (List Bool × List Bool) × NaorReingoldCache =>
          (query p.1).drop (k p.1 + 1)) EP encBits :=
      .of_tidy (ComputableTidilyInPolyTime.bitsDropWithInput hq_t hk1_t)
    have hsuf := F.computableInPolyTime_naorReingoldWordSuffix.comp
      ((hdesc.comp hp1).prod (hchild.prod ((hαs.comp hp1).prod hdrop)))
    have hc2 : ComputableInPolyTime
        (fun p : α × (List Bool × List Bool) × NaorReingoldCache => p.2.2)
        EP naorReingoldCacheEncoding := by fun_prop
    exact hsuf.prod hc2
  have hbranch : ComputableTidilyInPolyTime
      (fun a => decide ((query a).length = m a)) input encBool := by
    have hq_t := hquery.tidy
    have hm_t := hm.tidy
    polytime
  have hnil : IsPPTOn input (encPair encBits naorReingoldCacheEncoding)
      (fun a => pure ([], cache a)) := by
    refine ComputableInPolyTime.isPPTOn ?_
    exact (ComputableInPolyTime.const ([] : List Bool)).prod hcache
  have hvalid : IsPPTOn input (encPair encBits naorReingoldCacheEncoding)
      (fun a => do
        let (vw, cache') ← memoize (fun _ : List Bool =>
          F.sampleNaorReingoldPair (param a) (desc a) (u a) (v a) (w a))
          ((query a).take (k a)) (cache a)
        return (F.naorReingoldWordSuffix (desc a)
          (if (query a).getD (k a) false then vw.2 else vw.1)
          (αs a) ((query a).drop (k a + 1)), cache')) :=
    hmemo.bind_with (ComputableInPolyTime.isPPTOn hpost)
  unfold naorReingoldFrontierOracle
  refine (IsPPTOn.ite hbranch hvalid hnil).congr fun a => ?_
  by_cases h : (query a).length = m a <;> simp [h]

private abbrev DDHInput (F : PrimeOrderGroupFamily) :=
  ℕ × F.Desc × List Bool × List Bool × List Bool

private abbrev DDHLevelInput (F : PrimeOrderGroupFamily) := DDHInput F × ℕ

private abbrev DDHCaller (F : PrimeOrderGroupFamily) := DDHLevelInput F × List ℕ

private def ddhInputEncoding (F : PrimeOrderGroupFamily) : DDHInput F ↪ List Bool :=
  encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))

private def ddhLevelInputEncoding (F : PrimeOrderGroupFamily) : DDHLevelInput F ↪ List Bool :=
  encPair (ddhInputEncoding F) encUnary

private def ddhCallerEncoding (F : PrimeOrderGroupFamily) : DDHCaller F ↪ List Bool :=
  encPair (ddhLevelInputEncoding F) (encList encNat)

private theorem isPPTOn_naorReingoldDescToDDHDistinguisher (F : PrimeOrderGroupFamily)
    {inLen : ℕ → ℕ} (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adv : ℕ → F.Desc → WordOracleComp Unit Bool}
    (hadv : IsOraclePPTOn (encPair encUnary F.encDesc) encBool (fun p => adv p.1 p.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => naorReingoldDescToDDHDistinguisher F inLen adv input.1 input.2) := by
  change IsPPTOn (ddhInputEncoding F) encBool
    (fun input => naorReingoldDescToDDHDistinguisher F inLen adv input.1 input.2)
  obtain ⟨cO, eO, hO⟩ := F.computableInPolyTime_order.tidy.polyBounded_length.exists_le
  obtain ⟨cR, eR, hR⟩ :=
    F.computableInPolyTime_ddhFixedUWordRerandomize.tidy.polyBounded_length.exists_le
  obtain ⟨cS, eS, hS⟩ :=
    F.computableInPolyTime_naorReingoldWordSuffix.tidy.polyBounded_length.exists_le
  let pairBound : DDHCaller F → ℕ := fun caller =>
    let L := (ddhCallerEncoding F caller).length
    cR * (16 * L + 16 * (cO * (L + 1) ^ eO) + 16) ^ eR
  have hpair_support :
      ∀ (caller : DDHCaller F) (vw : List Bool × List Bool),
        vw ∈ (ProbComp.eval (F.sampleNaorReingoldPair caller.1.1.1 caller.1.1.2.1
          caller.1.1.2.2.1 caller.1.1.2.2.2.1 caller.1.1.2.2.2.2)).support →
        (encPair encBits encBits vw).length ≤ pairBound caller := by
    intro caller vw hvw
    simp only [sampleNaorReingoldPair, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hvw
    obtain ⟨σ, hσ, τ, hτ, rfl⟩ := hvw
    let d := caller.1.1.2.1
    have hσ_lt : σ < F.order d := F.lt_order_of_mem_support_sampleNaorReingoldExp hσ
    have hτ_lt : τ < F.order d := F.lt_order_of_mem_support_sampleNaorReingoldExp hτ
    have hσ_len : (encNat σ).length ≤ (encNat (F.order d)).length := by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le_size hσ_lt.le
    have hτ_len : (encNat τ).length ≤ (encNat (F.order d)).length := by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le_size hτ_lt.le
    have hord_len :
        (encNat (F.order d)).length ≤ cO * ((ddhCallerEncoding F caller).length + 1) ^ eO := by
      refine (hO d).trans ?_
      have hd_le : (F.encDesc d).length ≤ (ddhCallerEncoding F caller).length := by
        simp only [ddhCallerEncoding, ddhLevelInputEncoding, ddhInputEncoding, length_encPair]
        lia
      exact Nat.mul_le_mul_left cO (Nat.pow_le_pow_left (by lia) eO)
    have hinput_le :
        (encPair F.encDesc
          (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat))))
          (d, caller.1.1.2.2.1, caller.1.1.2.2.2.1, caller.1.1.2.2.2.2, σ, τ)).length + 1 ≤
        16 * (ddhCallerEncoding F caller).length +
          16 * (cO * ((ddhCallerEncoding F caller).length + 1) ^ eO) + 16 := by
      have hcaller :
          2 * (F.encDesc d).length + 2 * caller.1.1.2.2.1.length +
            2 * caller.1.1.2.2.2.1.length + 2 * caller.1.1.2.2.2.2.length ≤
          (ddhCallerEncoding F caller).length := by
        simp only [ddhCallerEncoding, ddhLevelInputEncoding, ddhInputEncoding, length_encPair,
          encBits_apply]
        lia
      simp only [length_encPair, encBits_apply]
      lia
    exact (hR (d, caller.1.1.2.2.1, caller.1.1.2.2.2.1, caller.1.1.2.2.2.2, σ, τ)).trans
      (Nat.mul_le_mul_left cR (Nat.pow_le_pow_left hinput_le eR))
  let resources : DDHCaller F → List Bool → ℕ := fun caller query =>
    let B := pairBound caller
    let L := (ddhCallerEncoding F caller).length
    (4 * query.length + 2 * B + 3) + cS * (8 * L + 8 * B + 8 * query.length + 16) ^ eS
  have hresources : ComputableTidilyInPolyTime
      (fun pair : DDHCaller F × List Bool => resources pair.1 pair.2)
      (encPair (ddhCallerEncoding F) encBits) encUnary := by
    have hL : ComputableTidilyInPolyTime
        (fun pair : DDHCaller F × List Bool => (ddhCallerEncoding F pair.1).length)
        (encPair (ddhCallerEncoding F) encBits) encUnary := by
      have henc := (ComputableTidilyInPolyTime.encode (ddhCallerEncoding F)).comp
        (ComputableTidilyInPolyTime.fst (ddhCallerEncoding F) encBits)
      fun_prop
    have hQ : ComputableTidilyInPolyTime
        (fun pair : DDHCaller F × List Bool => pair.2.length)
        (encPair (ddhCallerEncoding F) encBits) encUnary := by fun_prop
    have hpolyB : ComputableTidilyInPolyTime
        (fun L : ℕ => cR * (16 * L + 16 * (cO * (L + 1) ^ eO) + 16) ^ eR)
        encUnary encUnary := by
      have hpO : ComputableTidilyInPolyTime (fun L : ℕ => (L + 1) ^ eO) encUnary encUnary :=
        (ComputableTidilyInPolyTime.unary_pow eO).comp (by fun_prop)
      have hbaseR : ComputableTidilyInPolyTime
          (fun L : ℕ => 16 * L + 16 * (cO * (L + 1) ^ eO) + 16) encUnary encUnary := by
        fun_prop
      have hpR : ComputableTidilyInPolyTime
          (fun L : ℕ => (16 * L + 16 * (cO * (L + 1) ^ eO) + 16) ^ eR) encUnary encUnary :=
        (ComputableTidilyInPolyTime.unary_pow eR).comp hbaseR
      fun_prop
    have hpolyRes : ComputableTidilyInPolyTime
        (fun lq : ℕ × ℕ =>
          let B := cR * (16 * lq.1 + 16 * (cO * (lq.1 + 1) ^ eO) + 16) ^ eR
          (4 * lq.2 + 2 * B + 3) + cS * (8 * lq.1 + 8 * B + 8 * lq.2 + 16) ^ eS)
        (encPair encUnary encUnary) encUnary := by
      have hB1 : ComputableTidilyInPolyTime
          (fun lq : ℕ × ℕ => cR * (16 * lq.1 + 16 * (cO * (lq.1 + 1) ^ eO) + 16) ^ eR)
          (encPair encUnary encUnary) encUnary := hpolyB.comp (by fun_prop)
      have hbaseS : ComputableTidilyInPolyTime
          (fun lq : ℕ × ℕ =>
            8 * lq.1 + 8 * (cR * (16 * lq.1 + 16 * (cO * (lq.1 + 1) ^ eO) + 16) ^ eR) +
              8 * lq.2 + 16)
          (encPair encUnary encUnary) encUnary := by fun_prop
      have hpS : ComputableTidilyInPolyTime
          (fun lq : ℕ × ℕ =>
            (8 * lq.1 + 8 * (cR * (16 * lq.1 + 16 * (cO * (lq.1 + 1) ^ eO) + 16) ^ eR) +
              8 * lq.2 + 16) ^ eS)
          (encPair encUnary encUnary) encUnary :=
        (ComputableTidilyInPolyTime.unary_pow eS).comp hbaseS
      dsimp only
      fun_prop
    exact hpolyRes.comp (hL.prod hQ)
  have hprepare : ComputableTidilyInPolyTime
      (fun caller : DDHCaller F => (caller.1.1.1, caller.1.1.2.1))
      (ddhCallerEncoding F) (encPair encUnary F.encDesc) := by
    unfold ddhCallerEncoding ddhLevelInputEncoding ddhInputEncoding
    fun_prop
  have hhandler : IsPPTOn
      (encPair (ddhCallerEncoding F)
        (encPair (encPair (encFinEnum Unit) encBits) naorReingoldCacheEncoding))
      (encPair encBits naorReingoldCacheEncoding)
      (fun pair => F.naorReingoldFrontierOracle pair.1.1.1.1 (inLen pair.1.1.1.1) pair.1.1.2
        pair.1.1.1.2.1 pair.1.1.1.2.2.1 pair.1.1.1.2.2.2.1 pair.1.1.1.2.2.2.2
        pair.1.2 pair.2.1.2 pair.2.2) := by
    unfold ddhCallerEncoding ddhLevelInputEncoding ddhInputEncoding
    refine isPPTOn_naorReingoldFrontierOracle F
      (by fun_prop) (hinLen.comp (by fun_prop)) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hrun : IsPPTOn (ddhCallerEncoding F) (encPair encBool naorReingoldCacheEncoding)
      (fun caller : DDHCaller F => (OracleComp.interpret
        (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifFin r))
          (fun request => F.naorReingoldFrontierOracle caller.1.1.1 (inLen caller.1.1.1)
            caller.1.2 caller.1.1.2.1 caller.1.1.2.2.1 caller.1.1.2.2.2.1 caller.1.1.2.2.2.2
            caller.2 request.2))
        (adv caller.1.1.1 caller.1.1.2.1)).run []) := by
    refine hadv.run_interpret_preprocess
      (prepare := fun caller : DDHCaller F => (caller.1.1.1, caller.1.1.2.1))
      (resources := resources)
      hprepare hhandler (by fun_prop)
      (fun caller cache => ∀ entry ∈ cache, (encPair encBits encBits entry.2).length ≤
        pairBound caller)
      (by simp) hresources ?_
    intro caller request cache hcache result hresult
    by_cases hq : request.2.length = inLen caller.1.1.1
    · simp only [naorReingoldFrontierOracle, hq, ↓reduceIte, ProbComp.eval_bind,
        PMF.mem_support_bind_iff] at hresult
      obtain ⟨⟨vw, cache'⟩, hvw, hres⟩ := hresult
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hres
      subst result
      rw [ProbComp.eval_memoize] at hvw
      obtain ⟨hvw_len, hcache', hgrowth⟩ := memoize_call_size_le encBits (encPair encBits encBits)
        (fun _ : List Bool => ProbComp.eval (F.sampleNaorReingoldPair caller.1.1.1
          caller.1.1.2.1 caller.1.1.2.2.1 caller.1.1.2.2.2.1 caller.1.1.2.2.2.2))
        (request.2.take caller.1.2) cache (pairBound caller) hcache
        (fun value hval => hpair_support caller value hval) (vw, cache') hvw
      have hchild_le :
          (if request.2.getD caller.1.2 false then vw.2 else vw.1).length ≤ pairBound caller := by
        simp only [length_encPair, encBits_apply] at hvw_len
        split_ifs <;> lia
      have hsuf_le :
          (F.naorReingoldWordSuffix caller.1.1.2.1
            (if request.2.getD caller.1.2 false then vw.2 else vw.1)
            caller.2 (request.2.drop (caller.1.2 + 1))).length ≤
          cS * (8 * (ddhCallerEncoding F caller).length + 8 * pairBound caller +
            8 * request.2.length + 16) ^ eS := by
        have hS' := hS
          (caller.1.1.2.1, (if request.2.getD caller.1.2 false then vw.2 else vw.1),
            caller.2, request.2.drop (caller.1.2 + 1))
        simp only [encBits_apply] at hS'
        refine hS'.trans (Nat.mul_le_mul_left cS (Nat.pow_le_pow_left ?_ eS))
        have hcaller_le :
            2 * (F.encDesc caller.1.1.2.1).length + 8 * (encList encNat caller.2).length ≤
            8 * (ddhCallerEncoding F caller).length := by
          simp only [ddhCallerEncoding, ddhLevelInputEncoding, ddhInputEncoding, length_encPair]
          lia
        have hdrop_le : (request.2.drop (caller.1.2 + 1)).length ≤ request.2.length := by simp
        simp only [encBits_apply, length_encPair]
        lia
      have hgrowth' :
          (naorReingoldCacheEncoding cache').length ≤
            (naorReingoldCacheEncoding cache).length +
              (4 * request.2.length + 2 * pairBound caller + 3) := by
        change (naorReingoldCacheEncoding cache').length ≤
          (naorReingoldCacheEncoding cache).length +
            4 * (request.2.take caller.1.2).length + 2 * pairBound caller + 3 at hgrowth
        have htake_le : (request.2.take caller.1.2).length ≤ request.2.length := by simp
        lia
      refine ⟨hcache', ?_, ?_⟩
      · dsimp only [resources]
        lia
      · dsimp only [resources]
        lia
    · simp only [naorReingoldFrontierOracle, hq, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨hcache, by simp, by lia⟩
  have hrun_fst : IsPPTOn (ddhCallerEncoding F) encBool
      (fun caller : DDHCaller F => Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifFin r))
          (fun request => F.naorReingoldFrontierOracle caller.1.1.1 (inLen caller.1.1.1)
            caller.1.2 caller.1.1.2.1 caller.1.1.2.2.1 caller.1.1.2.2.2.1 caller.1.1.2.2.2.2
            caller.2 request.2))
        (adv caller.1.1.1 caller.1.1.2.1)).run []) :=
    hrun.map (ComputableInPolyTime.fst _ _)
  have hrep : IsPPTOn (ddhLevelInputEncoding F) (encList encNat)
      (fun p : DDHLevelInput F =>
        OracleComp.replicate (inLen p.1.1 - (p.2 + 1))
          (F.sampleNaorReingoldExp p.1.1 p.1.2.1)) := by
    unfold ddhLevelInputEncoding ddhInputEncoding
    refine (F.isPPTOn_sampleNaorReingoldExp (by fun_prop) (by fun_prop)).replicate ?_
    have hm_t := (hinLen.comp (by fun_prop : ComputableInPolyTime
      (fun p : DDHLevelInput F => p.1.1)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encUnary) encUnary)).tidy
    have hk_t : ComputableTidilyInPolyTime (fun p : DDHLevelInput F => p.2)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encUnary) encUnary := by fun_prop
    exact .of_tidy (by polytime)
  have hvalidK : IsPPTOn (ddhLevelInputEncoding F) encBool
      (fun p : DDHLevelInput F => do
        let αs ← OracleComp.replicate (inLen p.1.1 - (p.2 + 1))
          (F.sampleNaorReingoldExp p.1.1 p.1.2.1)
        Prod.fst <$> (OracleComp.interpret
          (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifFin r))
            (fun request => F.naorReingoldFrontierOracle p.1.1 (inLen p.1.1) p.2 p.1.2.1
              p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 αs request.2))
          (adv p.1.1 p.1.2.1)).run []) :=
    hrep.bind_with hrun_fst
  have hdyadic : IsPPTOn (ddhInputEncoding F) encUnary
      (fun inp : DDHInput F => ProbComp.sampleDyadicIndex (inLen inp.1)) := by
    unfold ddhInputEncoding
    exact isPPTOn_sampleDyadicIndex (hinLen.comp (by fun_prop))
  have hguard : ComputableTidilyInPolyTime
      (fun p : DDHLevelInput F => decide (p.2 < inLen p.1.1))
      (ddhLevelInputEncoding F) encBool := by
    unfold ddhLevelInputEncoding ddhInputEncoding
    have hm_t := (hinLen.comp (by fun_prop : ComputableInPolyTime
      (fun p : DDHLevelInput F => p.1.1)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encUnary) encUnary)).tidy
    have hk_t : ComputableTidilyInPolyTime (fun p : DDHLevelInput F => p.2)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encUnary) encUnary := by fun_prop
    exact ComputableTidilyInPolyTime.unary_lt.comp (hk_t.prod hm_t)
  have hbody : IsPPTOn (ddhLevelInputEncoding F) encBool
      (fun p : DDHLevelInput F =>
        if p.2 < inLen p.1.1 then
          do
            let αs ← OracleComp.replicate (inLen p.1.1 - (p.2 + 1))
              (F.sampleNaorReingoldExp p.1.1 p.1.2.1)
            Prod.fst <$> (OracleComp.interpret
              (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifFin r))
                (fun request => F.naorReingoldFrontierOracle p.1.1 (inLen p.1.1) p.2 p.1.2.1
                  p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 αs request.2))
              (adv p.1.1 p.1.2.1)).run []
        else pure false) := by
    refine (IsPPTOn.ite hguard hvalidK
      (ComputableInPolyTime.isPPTOn (ComputableInPolyTime.const false))).congr fun p => ?_
    by_cases h : p.2 < inLen p.1.1
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
  exact hdyadic.bind_with hbody

/-- **`naorReingoldToDDHDistinguisher` is uniform strict PPT** whenever `inLen` is computable in
polynomial time in unary and `adversary` satisfies `IsOraclePPT encBool` ([BonehShoup2023],
Exercise 10.4(b); [NaorReingold2004], Theorem 4.1). -/
theorem isPPTOn_naorReingoldToDDHDistinguisher {inLen : ℕ → ℕ}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.naorReingoldToDDHDistinguisher inLen adversary input.1 input.2) := by
  have henc : ComputableTidilyInPolyTime
      (fun p : ℕ × F.Desc => (p.1, F.encDesc p.2))
      (encPair encUnary F.encDesc) (encPair encUnary encBits) :=
    (ComputableTidilyInPolyTime.fst encUnary F.encDesc).prod
      (ComputableTidilyInPolyTime.encoded (ComputableTidilyInPolyTime.snd encUnary F.encDesc))
  have hadv : IsOraclePPTOn (encPair encUnary F.encDesc) encBool
      (fun p => adversary p.1 (F.encDesc p.2)) :=
    hadversary.on.preprocess henc
  rw [← ddhInputEncoding]
  exact isPPTOn_naorReingoldDescToDDHDistinguisher F
    (adv := fun n d => adversary n (F.encDesc d)) hinLen hadv

/-! ### Quantitative and asymptotic DDH security of the Naor–Reingold group-PRF -/

private theorem eval_sampleNaorReingoldExp_eq_map_val (F : PrimeOrderGroupFamily) (n : ℕ)
    (d : F.Desc) :
    ProbComp.eval (F.sampleNaorReingoldExp n d) =
      (F.sampleModZModLaw (n + (F.encDesc d).length) d).map ZMod.val := by
  rw [← F.map_natCast_eval_sampleNaorReingoldExp n d, PMF.map_comp]
  symm
  refine (map_congr_on_support _ _ id fun x hx => ?_).trans (PMF.map_id _)
  dsimp only [Function.comp_apply, id_eq]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (F.lt_order_of_mem_support_sampleNaorReingoldExp hx)]

private theorem eval_replicate_sampleNaorReingoldExp_eq_iid (F : PrimeOrderGroupFamily)
    (n count : ℕ) (d : F.Desc) :
    ProbComp.eval (OracleComp.replicate count (F.sampleNaorReingoldExp n d)) =
      (PMF.iid (F.sampleModZModLaw (n + (F.encDesc d).length) d) count).map
        (fun s => List.ofFn fun j => (s j).val) := by
  rw [ProbComp.eval_replicate_iid, eval_sampleNaorReingoldExp_eq_map_val, PMF.iid_map, PMF.map_comp]
  rfl

private theorem iid_two_map {α β : Type*} (μ : PMF α) (f : α → α → β) :
    (PMF.iid μ 2).map (fun p => f (p 0) (p 1)) =
      μ.bind fun a => μ.map (fun b => f a b) := by
  simp only [PMF.iid, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map,
    Fin.cons_zero, Fin.cons_one]
  rfl

private theorem eval_sampleNaorReingoldPair_eq_iid (F : PrimeOrderGroupFamily) (n : ℕ)
    (d : F.Desc) (u v w : List Bool) :
    ProbComp.eval (F.sampleNaorReingoldPair n d u v w) =
      (PMF.iid (F.sampleModZModLaw (n + (F.encDesc d).length) d) 2).map
        (fun p => F.ddhFixedUWordRerandomize d u v w (p 0).val (p 1).val) := by
  symm
  refine (iid_two_map (F.sampleModZModLaw (n + (F.encDesc d).length) d)
    (fun a b => F.ddhFixedUWordRerandomize d u v w a.val b.val)).trans ?_
  simp only [sampleNaorReingoldPair, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleNaorReingoldExp_eq_map_val F n d, PMF.bind_map, Function.comp_def]
  rfl

private theorem pi_uniformOfFintype {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [Nonempty α] :
    PMF.pi (fun _ : ι => PMF.uniformOfFintype α) = PMF.uniformOfFintype (ι → α) := by
  ext f
  simp only [PMF.pi_apply, PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- The `k`-fold independent product of `PMF.uniformOfFintype α` is
`PMF.uniformOfFintype (Fin k → α)`. -/
theorem iid_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α] (k : ℕ) :
    PMF.iid (PMF.uniformOfFintype α) k = PMF.uniformOfFintype (Fin k → α) := by
  rw [PMF.iid_eq_pi, pi_uniformOfFintype]

private theorem pi_ddhFixedURerandomizeLaw_eq_multi (F : PrimeOrderGroupFamily) (d : F.Desc)
    (ι : Type*) [Fintype ι] [DecidableEq ι] (u₀ v₀ w₀ : F.Carrier d) :
    PMF.pi (fun _ : ι => F.ddhFixedURerandomizeLaw d u₀ v₀ w₀) =
      F.multiDDHRerandomizeLaw d ι u₀ v₀ w₀ := by
  have hcoord :
      F.ddhFixedURerandomizeLaw d u₀ v₀ w₀ =
        (PMF.uniformOfFintype (ZMod (F.order d) × ZMod (F.order d))).map
          (fun p => F.ddhFixedURerandomize d u₀ v₀ w₀ p.1 p.2) := by
    rw [← PMF.uniformOfFintype_prod, PMF.map_bind]
    simp only [ddhFixedURerandomizeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_comp, Function.comp_def]
    rfl
  simp_rw [hcoord]
  rw [PMF.pi_map, pi_uniformOfFintype, multiDDHRerandomizeLaw]

private noncomputable def frontierLevelWithExpLaw (F : PrimeOrderGroupFamily) (d : F.Desc)
    (m k : ℕ) (prog : WordOracleComp Unit Bool) (u v w : List Bool)
    (expLaw : PMF (ZMod (F.order d))) : PMF Bool := do
  let suffix ← PMF.iid expLaw (m - (k + 1))
  let αs := List.ofFn fun j => (suffix j).val
  let pairLaw := (PMF.iid expLaw 2).map fun p =>
    F.ddhFixedUWordRerandomize d u v w (p 0).val (p 1).val
  ((OracleComp.interpret
    (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
      fun request cache =>
        if request.2.length = m then do
          let (vw, cache') ← memoize (fun _ : List Bool => pairLaw) (request.2.take k) cache
          let child := if request.2.getD k false then vw.2 else vw.1
          pure (F.naorReingoldWordSuffix d child αs (request.2.drop (k + 1)), cache')
        else pure ([], cache))
    prog).run []).map Prod.fst

private theorem eval_frontierLevel_eq_withExpLaw (F : PrimeOrderGroupFamily) (n m k : ℕ)
    (d : F.Desc) (prog : WordOracleComp Unit Bool) (u v w : List Bool) :
    ProbComp.eval (do
      let αs ← OracleComp.replicate (m - (k + 1)) (F.sampleNaorReingoldExp n d)
      Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifFin r))
          (fun request => F.naorReingoldFrontierOracle n m k d u v w αs request.2))
        prog).run []) =
      frontierLevelWithExpLaw F d m k prog u v w
        (F.sampleModZModLaw (n + (F.encDesc d).length) d) := by
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbOracleComp.eval_run_interpret,
    eval_replicate_sampleNaorReingoldExp_eq_iid F n (m - (k + 1)) d, frontierLevelWithExpLaw,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
  congr 1; funext suffix
  refine congrArg (PMF.map Prod.fst)
    (congrArg (fun h => StateT.run (OracleComp.interpret h prog) []) ?_)
  funext q
  cases q with
  | inl r => rfl
  | inr request =>
    funext cache
    dsimp only [ProbOracleComp.handler, naorReingoldFrontierOracle]
    by_cases hq : request.2.length = m
    · simp only [hq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_memoize,
        eval_sampleNaorReingoldPair_eq_iid F n d u v w]
      rfl
    · simp [hq]

private noncomputable def frontierStep (F : PrimeOrderGroupFamily) (d : F.Desc) (m k : ℕ)
    (αs : List ℕ) (fresh : List Bool × List Bool) (request : Unit × List Bool) :
    StateT NaorReingoldCache PMF (List Bool) :=
  fun cache =>
    if request.2.length = m then
      match cache.lookup (request.2.take k) with
      | some vw =>
          PMF.pure (F.naorReingoldWordSuffix d
            (if request.2.getD k false then vw.2 else vw.1) αs (request.2.drop (k + 1)), cache)
      | none =>
          PMF.pure (F.naorReingoldWordSuffix d
            (if request.2.getD k false then fresh.2 else fresh.1) αs (request.2.drop (k + 1)),
            (request.2.take k, fresh) :: cache)
    else PMF.pure ([], cache)

private theorem frontierStep_bind_eq (F : PrimeOrderGroupFamily) (d : F.Desc) (m k : ℕ)
    (αs : List ℕ) (source : PMF (List Bool × List Bool)) (request : Unit × List Bool)
    (cache : NaorReingoldCache) :
    (source.bind fun fresh => frontierStep F d m k αs fresh request cache) =
      (if request.2.length = m then do
        let (vw, cache') ← memoize (fun _ : List Bool => source) (request.2.take k) cache
        let child := if request.2.getD k false then vw.2 else vw.1
        pure (F.naorReingoldWordSuffix d child αs (request.2.drop (k + 1)), cache')
      else pure ([], cache)) := by
  unfold frontierStep memoize
  by_cases hq : request.2.length = m
  · cases cache.lookup (request.2.take k) with
    | some vw =>
      simp [hq, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_const]
    | none =>
      simp [hq, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  · simp [hq, PMF.monad_pure_eq_pure, PMF.bind_const]

private theorem dist_frontierLevelWithExpLaw_le (F : PrimeOrderGroupFamily) (d : F.Desc)
    (m k Q : ℕ) {prog : WordOracleComp Unit Bool} (hQ : prog.IsQueryBounded Q)
    (u v w : List Bool) (μ₁ μ₂ : PMF (ZMod (F.order d))) :
    dist (frontierLevelWithExpLaw F d m k prog u v w μ₁)
      (frontierLevelWithExpLaw F d m k prog u v w μ₂) ≤
      (m + 2 * Q : ℝ) * dist μ₁ μ₂ := by
  let r := m - (k + 1)
  let detKernel : (Fin r → ZMod (F.order d)) × (Fin Q → Fin 2 → ZMod (F.order d)) → PMF Bool :=
    fun st =>
      let αs := List.ofFn fun j => (st.1 j).val
      let values := List.ofFn fun i =>
        F.ddhFixedUWordRerandomize d u v w (st.2 i 0).val (st.2 i 1).val
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun t => StateT.lift (ProbComp.unifOracle t))
          (OracleComp.withSampleList ([], []) (frontierStep F d m k αs)))
        prog).run ([], values)).map fun res => res.1)
  have hlaw (μ : PMF (ZMod (F.order d))) :
      frontierLevelWithExpLaw F d m k prog u v w μ =
        ((PMF.iid μ r).bind fun s => (PMF.iid (PMF.iid μ 2) Q).map (s, ·)).bind detKernel := by
    simp only [frontierLevelWithExpLaw, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]
    congr 1; funext s
    set αs := List.ofFn fun j => (s j).val
    set pairLaw := (PMF.iid μ 2).map fun p =>
      F.ddhFixedUWordRerandomize d u v w (p 0).val (p 1).val
    have hpre := congrArg (PMF.map Prod.fst)
      (hQ.run_interpret_presample pairLaw ([], []) (frontierStep F d m k αs) [])
    trans (((OracleComp.interpret
      (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
        fun request cache => pairLaw.bind fun fresh => frontierStep F d m k αs fresh request cache)
      prog).run []).map Prod.fst)
    · refine congrArg (PMF.map Prod.fst)
        (congrArg (fun h => StateT.run (OracleComp.interpret h prog) []) ?_)
      funext q
      cases q with
      | inl _ => rfl
      | inr request =>
        funext cache
        exact (frontierStep_bind_eq F d m k αs pairLaw request cache).symm
    · rw [← hpre, PMF.map_bind, PMF.iid_map, PMF.map_comp, PMF.bind_map]
      congr 1; funext tbl
      simp only [Function.comp_def, PMF.map_comp, detKernel]
      rfl
  rw [hlaw μ₁, hlaw μ₂]
  have hdist_r : dist (PMF.iid μ₁ r) (PMF.iid μ₂ r) ≤ r * dist μ₁ μ₂ :=
    PMF.dist_iid_le μ₁ μ₂ r
  have hdist_q : dist (PMF.iid (PMF.iid μ₁ 2) Q) (PMF.iid (PMF.iid μ₂ 2) Q) ≤
      (2 * Q : ℝ) * dist μ₁ μ₂ := by
    calc dist (PMF.iid (PMF.iid μ₁ 2) Q) (PMF.iid (PMF.iid μ₂ 2) Q)
        ≤ Q * dist (PMF.iid μ₁ 2) (PMF.iid μ₂ 2) := PMF.dist_iid_le _ _ Q
      _ ≤ Q * (2 * dist μ₁ μ₂) :=
          mul_le_mul_of_nonneg_left (PMF.dist_iid_le μ₁ μ₂ 2) (Nat.cast_nonneg Q)
      _ = (2 * Q : ℝ) * dist μ₁ μ₂ := by ring
  have hswap (a : PMF (Fin r → ZMod (F.order d)))
      (b : PMF (Fin Q → Fin 2 → ZMod (F.order d))) :
      (a.bind fun s => b.map (s, ·)) = (b.bind fun t => a.map (·, t)) := by
    simp only [PMF.map, Function.comp_def]
    exact PMF.bind_comm a b fun s t => PMF.pure (s, t)
  have hj1 :
      dist ((PMF.iid μ₁ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·))
        ((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·)) ≤
        r * dist μ₁ μ₂ :=
    (dist_bind_le _ _ _).trans hdist_r
  have hj2 :
      dist ((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·))
        ((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₂ 2) Q).map (s, ·)) ≤
        (2 * Q : ℝ) * dist μ₁ μ₂ := by
    rw [hswap (PMF.iid μ₂ r) (PMF.iid (PMF.iid μ₁ 2) Q),
      hswap (PMF.iid μ₂ r) (PMF.iid (PMF.iid μ₂ 2) Q)]
    exact (dist_bind_le _ _ _).trans hdist_q
  have hr_le : (r : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m (k + 1)
  have hnonneg : 0 ≤ dist μ₁ μ₂ := dist_nonneg
  calc dist (((PMF.iid μ₁ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·)).bind detKernel)
        (((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₂ 2) Q).map (s, ·)).bind detKernel)
      ≤ dist ((PMF.iid μ₁ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·))
          ((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₂ 2) Q).map (s, ·)) :=
        dist_bind_le _ _ _
    _ ≤ dist ((PMF.iid μ₁ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·))
          ((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·)) +
        dist ((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·))
          ((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₂ 2) Q).map (s, ·)) :=
        dist_triangle _ _ _
    _ ≤ r * dist μ₁ μ₂ + (2 * Q : ℝ) * dist μ₁ μ₂ := add_le_add hj1 hj2
    _ = (r + 2 * Q : ℝ) * dist μ₁ μ₂ := by ring
    _ ≤ (m + 2 * Q : ℝ) * dist μ₁ μ₂ := by nlinarith

private theorem ofFn_zeroExtend_ofList {m k : ℕ} (hk : k ≤ m) {xs : List Bool}
    (hxs : xs.length = m) :
    List.ofFn (BitString.zeroExtend (d' := k) (BitString.ofList m xs)) = xs.take k := by
  refine List.ext_getElem (by simp [hxs, Nat.min_eq_left hk]) fun i h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₁
  simp only [List.getElem_ofFn, BitString.zeroExtend, show i < m by omega, ↓reduceDIte,
    BitString.ofList, List.getElem_take]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem naorReingoldWordSuffix_eq_tableEval (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m : ℕ} (k : ℕ) (hk : k < m) (T : BitString k → F.Carrier d × F.Carrier d)
    (suffix : Fin (m - (k + 1)) → ZMod (F.order d)) {xs : List Bool} (hxs : xs.length = m) :
    let x := BitString.ofList m xs
    let pref := BitString.zeroExtend (d' := k) x
    let child := if xs.getD k false then F.encode d (T pref).2 else F.encode d (T pref).1
    let α : Fin m → ZMod (F.order d) := fun i =>
      if h : k + 1 ≤ i.val then suffix ⟨i.val - (k + 1), by omega⟩ else 1
    F.naorReingoldWordSuffix d child (List.ofFn fun j => (suffix j).val) (xs.drop (k + 1)) =
      F.encode d (F.naorReingoldTableEval d k hk T α x) := by
  dsimp only
  let x := BitString.ofList m xs
  let pref := BitString.zeroExtend (d' := k) x
  let base : F.Carrier d := if x ⟨k, hk⟩ then (T pref).2 else (T pref).1
  have hchild :
      (if xs.getD k false then F.encode d (T pref).2 else F.encode d (T pref).1) =
        F.encode d base := by
    have hbit : xs.getD k false = x ⟨k, hk⟩ := rfl
    rw [hbit]
    dsimp only [base]
    split_ifs <;> rfl
  rw [hchild, naorReingoldWordSuffix, F.smul_encode, naorReingoldTableEval]
  refine congrArg (F.encode d) (congrArg (· • base) ?_)
  rw [naorReingoldProdNat_cast, Nat.cast_one, one_mul]
  have hzip :
      ((List.ofFn fun j : Fin (m - (k + 1)) => (suffix j).val).zip (xs.drop (k + 1))) =
        List.ofFn fun j : Fin (m - (k + 1)) => ((suffix j).val, x ⟨k + 1 + j.val, by omega⟩) := by
    refine List.ext_getElem (by simp [hxs]) fun j h₁ h₂ => ?_
    simp only [List.length_ofFn] at h₂
    simp only [List.getElem_zip, List.getElem_ofFn, List.getElem_drop, Prod.mk.injEq, true_and]
    dsimp only [x, BitString.ofList]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hzip, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_def, ZMod.natCast_zmod_val]
  let e : Fin (k + 1) ⊕ Fin (m - (k + 1)) ≃ Fin m :=
    (finSumFinEquiv (m := k + 1) (n := m - (k + 1))).trans
      (Fin.castOrderIso (Nat.add_sub_of_le hk)).toEquiv
  rw [naorReingoldSuffixExp, ← Equiv.prod_comp e]
  rw [Fintype.prod_sum_type]
  have hleft :
      (∏ i : Fin (k + 1),
        if k + 1 ≤ (e (Sum.inl i)).val ∧ x (e (Sum.inl i)) then
          (if h : k + 1 ≤ (e (Sum.inl i)).val then
            suffix ⟨(e (Sum.inl i)).val - (k + 1), by omega⟩ else 1)
        else 1) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hlt : (e (Sum.inl i)).val < k + 1 := by
      change i.val < k + 1
      exact i.isLt
    simp [Nat.not_le.mpr hlt]
  rw [hleft, one_mul]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hval : (e (Sum.inr j)).val = k + 1 + j.val := rfl
  have hle : k + 1 ≤ (e (Sum.inr j)).val := by omega
  have he_eq : e (Sum.inr j) = ⟨k + 1 + j.val, by omega⟩ := by ext; exact hval
  simp only [he_eq, Nat.le_add_right, true_and, ↓reduceDIte]
  have hj_eq : (⟨k + 1 + j.val - (k + 1), by omega⟩ : Fin (m - (k + 1))) = j := by
    ext; dsimp; omega
  rw [hj_eq]

private theorem frontierLevelWithExpLaw_uniform_eq_multi (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) (u₀ v₀ w₀ : F.Carrier d) :
    frontierLevelWithExpLaw F d m k prog (F.encode d u₀) (F.encode d v₀) (F.encode d w₀)
      (PMF.uniformOfFintype (ZMod (F.order d))) =
      (F.multiDDHRerandomizeLaw d (BitString k) u₀ v₀ w₀).bind
        (naorReingoldWordLevelTest F d k hk prog u₀) := by
  have hpairLaw :
      ((PMF.iid (PMF.uniformOfFintype (ZMod (F.order d))) 2).map fun p =>
        F.ddhFixedUWordRerandomize d (F.encode d u₀) (F.encode d v₀) (F.encode d w₀)
          (p 0).val (p 1).val) =
      (F.ddhFixedURerandomizeLaw d u₀ v₀ w₀).map (Prod.map (F.encode d) (F.encode d)) := by
    refine (iid_two_map (PMF.uniformOfFintype (ZMod (F.order d)))
      (fun a b => F.ddhFixedUWordRerandomize d (F.encode d u₀) (F.encode d v₀) (F.encode d w₀)
        a.val b.val)).trans ?_
    simp only [ddhFixedURerandomizeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map, Function.comp_def, Prod.map, PMF.bind_bind, PMF.pure_bind,
      F.ddhFixedUWordRerandomize_encode, ZMod.natCast_zmod_val]
  unfold frontierLevelWithExpLaw naorReingoldWordLevelTest
  rw [hpairLaw]
  simp only [iid_uniformOfFintype, PMF.monad_bind_eq_bind]
  symm
  rw [PMF.bind_comm]
  congr 1; funext suffix
  let αs := List.ofFn fun j => (suffix j).val
  let keyMap : BitString k ↪ List Bool := ⟨List.ofFn, List.ofFn_injective⟩
  let valMap : F.Carrier d × F.Carrier d → List Bool × List Bool :=
    Prod.map (F.encode d) (F.encode d)
  let distK : BitString k → PMF (F.Carrier d × F.Carrier d) :=
    fun _ => F.ddhFixedURerandomizeLaw d u₀ v₀ w₀
  let sample' : List Bool → PMF (List Bool × List Bool) :=
    fun _ => (F.ddhFixedURerandomizeLaw d u₀ v₀ w₀).map valMap
  let prefixProg : ProbOracleComp (fun _ : BitString k => List Bool × List Bool) Bool :=
    OracleComp.interpret
      (ProbOracleComp.handler (fun r => ProbOracleComp.sample (ProbComp.unifFin r))
        fun request =>
          if request.2.length = m then
            (fun vw : List Bool × List Bool =>
              F.naorReingoldWordSuffix d
                (if request.2.getD k false then vw.2 else vw.1) αs (request.2.drop (k + 1))) <$>
              ProbOracleComp.query (BitString.zeroExtend (d' := k) (BitString.ofList m request.2))
          else pure [])
      prog
  have hmemo := RandomOracle.interpret_prob_eq_memoize_map keyMap valMap distK sample'
    (fun _ => rfl) prefixProg
  simp only [PMF.monad_bind_eq_bind] at hmemo
  rw [pi_ddhFixedURerandomizeLaw_eq_multi F d (BitString k) u₀ v₀ w₀] at hmemo
  have hlhs :
      ((F.multiDDHRerandomizeLaw d (BitString k) u₀ v₀ w₀).bind fun T =>
        naorReingoldWordRun F d prog
          (F.naorReingoldTableEval d k hk T
            (fun i => if h : k + 1 ≤ i.val then suffix ⟨i.val - (k + 1), by omega⟩ else 1))) =
      ((F.multiDDHRerandomizeLaw d (BitString k) u₀ v₀ w₀).bind fun T =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle
            (fun key => PMF.pure (valMap (T key))))
          prefixProg) := by
    congr 1; funext T
    dsimp only [naorReingoldWordRun, prefixProg]
    rw [OracleComp.interpret_interpret]
    congr 1; funext q
    cases q with
    | inl r =>
      simp [ProbOracleComp.handler, ProbOracleComp.sample, ProbComp.unifFin]
    | inr request =>
      dsimp only [ProbOracleComp.handler, Function.comp_apply]
      by_cases hq : request.2.length = m
      · simp only [hq, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
          PMF.monad_map_eq_map, PMF.pure_map, naorReingoldWordOracle, valMap]
        exact congrArg PMF.pure
          (naorReingoldWordSuffix_eq_tableEval F d k hk T suffix hq).symm
      · simp [hq, naorReingoldWordOracle, PMF.monad_pure_eq_pure]
  have hrhs :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
          (fun key => memoize sample' (keyMap key)))
        prefixProg).run []).map Prod.fst =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
          fun request cache =>
            if request.2.length = m then do
              let (vw, cache') ← memoize sample' (request.2.take k) cache
              let child := if request.2.getD k false then vw.2 else vw.1
              pure (F.naorReingoldWordSuffix d child αs (request.2.drop (k + 1)), cache')
            else pure ([], cache))
        prog).run []).map Prod.fst := by
    refine congrArg (PMF.map Prod.fst) ?_
    dsimp only [prefixProg]
    change (OracleComp.interpret (m := StateT NaorReingoldCache PMF) _
      (OracleComp.interpret _ prog)) [] = _
    rw [OracleComp.interpret_interpret]
    refine congrFun (congrArg (fun h => OracleComp.interpret h prog) ?_) []
    funext q
    cases q with
    | inl r =>
      funext cache
      simp [ProbOracleComp.handler, ProbOracleComp.sample, ProbComp.unifFin, StateT.lift]
    | inr request =>
      funext cache
      dsimp only [ProbOracleComp.handler, Function.comp_apply]
      by_cases hq : request.2.length = m
      · simp only [hq, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
          keyMap, Function.Embedding.coeFn_mk,
          ofFn_zeroExtend_ofList hk.le hq]
        rfl
      · simp only [hq, ↓reduceIte, OracleComp.interpret_pure]
        rfl
  exact hlhs.trans (hmemo.trans hrhs)

private noncomputable def naorReingoldDescRealGame (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α₀ ← PMF.uniformOfFintype (ZMod (F.order d))
  let α ← PMF.uniformOfFintype (Fin (inLen n) → ZMod (F.order d))
  naorReingoldWordRun F d (adv n d) (F.naorReingoldEval d α₀ α)

private noncomputable def naorReingoldDescIdealGame (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ) : Game := do
  let d ← setup n
  let B ← PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order d))
  naorReingoldWordRun F d (adv n d) (fun x => B x • F.generator d)

private theorem eval_naorReingoldDescToDDHDistinguisher (F : PrimeOrderGroupFamily)
    (inLen : ℕ → ℕ) (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ)
    (d : F.Desc) (u v w : List Bool) :
    ProbComp.eval (naorReingoldDescToDDHDistinguisher F inLen adv n (d, u, v, w)) =
      (PMF.uniformOfFintype (Fin (dyadicSize (inLen n)))).bind fun i =>
        if i.val < inLen n then
          frontierLevelWithExpLaw F d (inLen n) i.val (adv n d) u v w
            (F.sampleModZModLaw (n + (F.encDesc d).length) d)
        else PMF.pure false := by
  unfold naorReingoldDescToDDHDistinguisher
  rw [ProbComp.eval_bind, ProbComp.eval_sampleDyadicIndex, PMF.bind_map]
  congr 1; funext i
  dsimp only [Function.comp_apply]
  by_cases hk : i.val < inLen n
  · simp only [hk, ↓reduceIte]
    exact eval_frontierLevel_eq_withExpLaw F n (inLen n) i.val d (adv n d) u v w
  · simp [hk]

private theorem advantage_exactDDHIdeal_le (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (m : ℕ) (adv : F.Desc → WordOracleComp Unit Bool) (n : ℕ) :
    Game.advantage
      ((setup n).bind fun d =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
              (PMF.uniformOfFintype (Fin (dyadicSize m))).bind fun i =>
                if i.val < m then
                  frontierLevelWithExpLaw F d m i.val (adv d)
                    (F.encode d (α • F.generator d))
                    (F.encode d (β • F.generator d))
                    (F.encode d (γ • F.generator d))
                    (PMF.uniformOfFintype (ZMod (F.order d)))
                else PMF.pure false)
      ((PMF.uniformOfFintype (Fin (dyadicSize m))).bind fun i =>
        if i.val < m then (setup n).bind fun d => naorReingoldWordHybridAt F d m (i.val + 1) (adv d)
        else PMF.pure false) ≤
      (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal := by
  let cap := dyadicSize m
  have hrhs_comm :
      ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
        if i.val < m then (setup n).bind fun d => naorReingoldWordHybridAt F d m (i.val + 1) (adv d)
        else PMF.pure false) =
      ((setup n).bind fun d =>
        (PMF.uniformOfFintype (Fin cap)).bind fun i =>
          if i.val < m then naorReingoldWordHybridAt F d m (i.val + 1) (adv d)
          else PMF.pure false) := by
    have hite (i : Fin cap) :
        (if i.val < m then
          (setup n).bind fun d => naorReingoldWordHybridAt F d m (i.val + 1) (adv d)
        else PMF.pure false) =
        ((setup n).bind fun d =>
          if i.val < m then naorReingoldWordHybridAt F d m (i.val + 1) (adv d)
          else PMF.pure false) := by
      by_cases hk : i.val < m <;> simp [hk, PMF.bind_const]
    simp_rw [hite]
    exact PMF.bind_comm _ _ _
  rw [hrhs_comm]
  let errPMF : F.Desc → Game := fun d =>
    (PMF.uniformOfFintype (ZMod (F.order d))).bind fun x => PMF.pure (decide (x = 0))
  have herr_true (d : F.Desc) : errPMF d true = (F.order d : ℝ≥0∞)⁻¹ := by
    dsimp only [errPMF]
    rw [PMF.bind_apply, tsum_fintype]
    simp [PMF.uniformOfFintype_apply, PMF.pure_apply, ZMod.card, eq_comm (a := true)]
  have herr_succ :
      Game.succProbability ((setup n).bind errPMF) =
        (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal := by
    unfold Game.succProbability
    rw [PMF.bind_apply]
    simp_rw [herr_true]
  rw [← herr_succ]
  refine Game.advantage_bind_le_succProbability_bind (setup n) _ _ errPMF fun d => ?_
  let g1 :=
    (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
          (PMF.uniformOfFintype (Fin cap)).bind fun i =>
            if i.val < m then
              frontierLevelWithExpLaw F d m i.val (adv d)
                (F.encode d (α • F.generator d))
                (F.encode d (β • F.generator d))
                (F.encode d (γ • F.generator d))
                (PMF.uniformOfFintype (ZMod (F.order d)))
            else PMF.pure false
  let g2 :=
    (PMF.uniformOfFintype (Fin cap)).bind fun i =>
      if i.val < m then naorReingoldWordHybridAt F d m (i.val + 1) (adv d)
      else PMF.pure false
  have hadv_d : Game.advantage g1 g2 ≤ (F.order d : ℝ≥0)⁻¹ := by
    have hg1_comm :
        g1 =
          (PMF.uniformOfFintype (Fin cap)).bind fun i =>
            if hk : i.val < m then
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
                (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
                  (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                    (F.multiDDHRerandomizeLaw d (BitString i.val)
                      (α • F.generator d) (β • F.generator d) (γ • F.generator d)).bind
                      (naorReingoldWordLevelTest F d i.val hk (adv d) (α • F.generator d))
            else PMF.pure false := by
      dsimp only [g1]
      have hc3 (α β : ZMod (F.order d)) :
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
            (PMF.uniformOfFintype (Fin cap)).bind fun i =>
              if i.val < m then
                frontierLevelWithExpLaw F d m i.val (adv d)
                  (F.encode d (α • F.generator d))
                  (F.encode d (β • F.generator d))
                  (F.encode d (γ • F.generator d))
                  (PMF.uniformOfFintype (ZMod (F.order d)))
              else PMF.pure false) =
          ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
              if i.val < m then
                frontierLevelWithExpLaw F d m i.val (adv d)
                  (F.encode d (α • F.generator d))
                  (F.encode d (β • F.generator d))
                  (F.encode d (γ • F.generator d))
                  (PMF.uniformOfFintype (ZMod (F.order d)))
              else PMF.pure false) := PMF.bind_comm _ _ _
      simp_rw [hc3]
      have hc2 (α : ZMod (F.order d)) :
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
            (PMF.uniformOfFintype (Fin cap)).bind fun i =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                if i.val < m then
                  frontierLevelWithExpLaw F d m i.val (adv d)
                    (F.encode d (α • F.generator d))
                    (F.encode d (β • F.generator d))
                    (F.encode d (γ • F.generator d))
                    (PMF.uniformOfFintype (ZMod (F.order d)))
                else PMF.pure false) =
          ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                if i.val < m then
                  frontierLevelWithExpLaw F d m i.val (adv d)
                    (F.encode d (α • F.generator d))
                    (F.encode d (β • F.generator d))
                    (F.encode d (γ • F.generator d))
                    (PMF.uniformOfFintype (ZMod (F.order d)))
                else PMF.pure false) := PMF.bind_comm _ _ _
      simp_rw [hc2]
      rw [PMF.bind_comm]
      congr 1; funext i
      by_cases hk : i.val < m
      · simp only [hk, ↓reduceIte, ↓reduceDIte]
        congr 1; funext α; congr 1; funext β; congr 1; funext γ
        exact frontierLevelWithExpLaw_uniform_eq_multi F d i.val hk (adv d) _ _ _
      · simp [hk, PMF.bind_const]
    rw [hg1_comm]
    refine Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (Fin cap)) _ _ fun i => ?_
    by_cases hk : i.val < m
    · simp only [hk, ↓reduceDIte, ↓reduceIte,
        ← multiDDHIdealTupleLaw_naorReingoldWordLevelTest F d i.val hk (adv d)]
      refine Game.advantage_bind_le_nnreal _ _ _ fun α => ?_
      rw [← PMF.bind_const (PMF.uniformOfFintype (ZMod (F.order d)))
        ((F.multiDDHIdealTupleLaw d (BitString i.val)).bind
          (naorReingoldWordLevelTest F d i.val hk (adv d) (α • F.generator d)))]
      refine Game.advantage_bind_le_nnreal _ _ _ fun β => ?_
      simpa only [ZMod.card] using
        Game.advantage_bind_uniformOfFintype_of_ne_le (α * β)
          (fun γ => (F.multiDDHRerandomizeLaw d (BitString i.val)
            (α • F.generator d) (β • F.generator d) (γ • F.generator d)).bind
            (naorReingoldWordLevelTest F d i.val hk (adv d) (α • F.generator d)))
          ((F.multiDDHIdealTupleLaw d (BitString i.val)).bind
            (naorReingoldWordLevelTest F d i.val hk (adv d) (α • F.generator d)))
          (fun γ hγ => by rw [F.multiDDHRerandomizeLaw_ideal d (BitString i.val) hγ])
    · simp [hk]
  have hadv_real :
      |(g1 true).toReal - (g2 true).toReal| ≤ (F.order d : ℝ)⁻¹ := by
    have h := NNReal.coe_le_coe.mpr hadv_d
    simpa only [Game.coe_advantage, Game.coe_succProbability, Real.dist_eq, NNReal.coe_inv,
      NNReal.coe_natCast] using h
  have h1_real : (g1 true).toReal ≤ (g2 true).toReal + (F.order d : ℝ)⁻¹ := by
    linarith [(abs_le.mp hadv_real).2]
  have h2_real : (g2 true).toReal ≤ (g1 true).toReal + (F.order d : ℝ)⁻¹ := by
    linarith [(abs_le.mp hadv_real).1]
  have hinv_eq : (errPMF d true).toReal = (F.order d : ℝ)⁻¹ := by
    rw [herr_true, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have h1_enn : g1 true ≤ g2 true + errPMF d true := by
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top g1 true),
      ← ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr
        ⟨PMF.apply_ne_top g2 true, PMF.apply_ne_top (errPMF d) true⟩),
      ENNReal.toReal_add (PMF.apply_ne_top g2 true) (PMF.apply_ne_top (errPMF d) true),
      hinv_eq]
    exact ENNReal.ofReal_le_ofReal h1_real
  have h2_enn : g2 true ≤ g1 true + errPMF d true := by
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top g2 true),
      ← ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr
        ⟨PMF.apply_ne_top g1 true, PMF.apply_ne_top (errPMF d) true⟩),
      ENNReal.toReal_add (PMF.apply_ne_top g1 true) (PMF.apply_ne_top (errPMF d) true),
      hinv_eq]
    exact ENNReal.ofReal_le_ofReal h2_real
  exact ⟨h1_enn, h2_enn⟩

private theorem advantage_naorReingoldDescGame_le (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ)
    (Q : F.Desc → ℕ) {ε : ℝ≥0}
    (hQ : ∀ d ∈ (setup n).support, (adv n d).IsQueryBounded (Q d))
    (hε : ∀ d ∈ (setup n).support,
      ((inLen n + 2 * Q d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + (F.encDesc d).length) ≤ ε) :
    Game.advantage
      (naorReingoldDescRealGame F setup inLen adv n)
      (naorReingoldDescIdealGame F setup inLen adv n) ≤
      (dyadicSize (inLen n) : ℝ≥0) *
        (Game.advantage
          (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
          (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) +
          2 * ε +
          (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal) := by
  let m := inLen n
  let cap := dyadicSize m
  let H : ℕ → Game := fun k => (setup n).bind fun d => naorReingoldWordHybridAt F d m k (adv n d)
  have hH0 : H 0 = naorReingoldDescRealGame F setup inLen adv n := by
    simp only [H, naorReingoldDescRealGame, PMF.monad_bind_eq_bind]
    congr 1; funext d
    exact naorReingoldWordHybridAt_zero F d m (adv n d)
  have hHm : H m = naorReingoldDescIdealGame F setup inLen adv n := by
    simp only [H, naorReingoldDescIdealGame, PMF.monad_bind_eq_bind]
    congr 1; funext d
    exact naorReingoldWordHybridAt_self F d m (adv n d)
  rw [← hH0, ← hHm, Game.advantage_hybrid_average H m cap (lt_dyadicSize m).le]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  let exactDDHReal : Game :=
    (setup n).bind fun d =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (Fin cap)).bind fun i =>
            if i.val < m then
              frontierLevelWithExpLaw F d m i.val (adv n d)
                (F.encode d (α • F.generator d))
                (F.encode d (β • F.generator d))
                (F.encode d ((α * β) • F.generator d))
                (PMF.uniformOfFintype (ZMod (F.order d)))
            else PMF.pure false
  let exactDDHIdeal : Game :=
    (setup n).bind fun d =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
            (PMF.uniformOfFintype (Fin cap)).bind fun i =>
              if i.val < m then
                frontierLevelWithExpLaw F d m i.val (adv n d)
                  (F.encode d (α • F.generator d))
                  (F.encode d (β • F.generator d))
                  (F.encode d (γ • F.generator d))
                  (PMF.uniformOfFintype (ZMod (F.order d)))
              else PMF.pure false
  have hEqReal :
      ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
        if i.val < m then H i.val else PMF.pure false) = exactDDHReal := by
    have hite (i : Fin cap) :
        (if i.val < m then H i.val else PMF.pure false) =
        ((setup n).bind fun d =>
          if i.val < m then naorReingoldWordHybridAt F d m i.val (adv n d)
          else PMF.pure false) := by
      by_cases hk : i.val < m <;> simp [H, hk, PMF.bind_const]
    simp_rw [hite]
    rw [PMF.bind_comm]
    dsimp only [exactDDHReal]
    congr 1; funext d
    symm
    have hcomm (α : ZMod (F.order d)) :
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (Fin cap)).bind fun i =>
            if i.val < m then
              frontierLevelWithExpLaw F d m i.val (adv n d)
                (F.encode d (α • F.generator d))
                (F.encode d (β • F.generator d))
                (F.encode d ((α * β) • F.generator d))
                (PMF.uniformOfFintype (ZMod (F.order d)))
            else PMF.pure false) =
        ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
            if i.val < m then
              frontierLevelWithExpLaw F d m i.val (adv n d)
                (F.encode d (α • F.generator d))
                (F.encode d (β • F.generator d))
                (F.encode d ((α * β) • F.generator d))
                (PMF.uniformOfFintype (ZMod (F.order d)))
            else PMF.pure false) := PMF.bind_comm _ _ _
    simp_rw [hcomm]
    rw [PMF.bind_comm]
    congr 1; funext i
    by_cases hk : i.val < m
    · simp only [hk, ↓reduceIte]
      simp_rw [frontierLevelWithExpLaw_uniform_eq_multi F d i.val hk (adv n d),
        F.multiDDHRerandomizeLaw_real d (BitString i.val), PMF.bind_const]
      exact multiDDHRealTupleLaw_naorReingoldWordLevelTest F d i.val hk (adv n d)
    · simp [hk, PMF.bind_const]
  have hDDHReal_eq :
      F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n =
        (setup n).bind fun d =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
              (PMF.uniformOfFintype (Fin cap)).bind fun i =>
                if i.val < m then
                  frontierLevelWithExpLaw F d m i.val (adv n d)
                    (F.encode d (α • F.generator d))
                    (F.encode d (β • F.generator d))
                    (F.encode d ((α * β) • F.generator d))
                    (F.sampleModZModLaw (n + (F.encDesc d).length) d)
                else PMF.pure false := by
    simp only [ddhRealGame, PMF.monad_bind_eq_bind,
      eval_naorReingoldDescToDDHDistinguisher F inLen adv n]
    rfl
  have hDDHIdeal_eq :
      F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n =
        (setup n).bind fun d =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                (PMF.uniformOfFintype (Fin cap)).bind fun i =>
                  if i.val < m then
                    frontierLevelWithExpLaw F d m i.val (adv n d)
                      (F.encode d (α • F.generator d))
                      (F.encode d (β • F.generator d))
                      (F.encode d (γ • F.generator d))
                      (F.sampleModZModLaw (n + (F.encDesc d).length) d)
                  else PMF.pure false := by
    simp only [ddhIdealGame, PMF.monad_bind_eq_bind,
      eval_naorReingoldDescToDDHDistinguisher F inLen adv n]
    rfl
  have hstep_err :
      ∀ d ∈ (setup n).support, ∀ u v w : List Bool, ∀ i : Fin cap,
        Game.advantage
          (if i.val < m then
            frontierLevelWithExpLaw F d m i.val (adv n d) u v w
              (PMF.uniformOfFintype (ZMod (F.order d)))
          else PMF.pure false)
          (if i.val < m then
            frontierLevelWithExpLaw F d m i.val (adv n d) u v w
              (F.sampleModZModLaw (n + (F.encDesc d).length) d)
          else PMF.pure false) ≤ ε := by
    intro d hd u v w i
    by_cases hk : i.val < m
    · simp only [hk, ↓reduceIte]
      refine le_trans ?_ (hε d hd)
      rw [Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
      have h1 := dist_frontierLevelWithExpLaw_le F d m i.val (Q d) (hQ d hd) u v w
        (PMF.uniformOfFintype (ZMod (F.order d)))
        (F.sampleModZModLaw (n + (F.encDesc d).length) d)
      have h2 := F.dist_sampleModZModLaw_le (n + (F.encDesc d).length) d
      calc dist
            (frontierLevelWithExpLaw F d m i.val (adv n d) u v w
              (PMF.uniformOfFintype (ZMod (F.order d))))
            (frontierLevelWithExpLaw F d m i.val (adv n d) u v w
              (F.sampleModZModLaw (n + (F.encDesc d).length) d))
          ≤ (m + 2 * Q d : ℝ) *
              dist (PMF.uniformOfFintype (ZMod (F.order d)))
                (F.sampleModZModLaw (n + (F.encDesc d).length) d) := h1
        _ ≤ (m + 2 * Q d : ℝ) * (1 / 2 ^ (n + (F.encDesc d).length)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ((((m + 2 * Q d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + (F.encDesc d).length) : ℝ≥0) : ℝ) := by
            push_cast
            ring
    · simp [hk]
  have hAdvRealApprox :
      Game.advantage exactDDHReal
        (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) ≤ ε := by
    rw [hDDHReal_eq]
    refine Game.advantage_bind_le_of_support (setup n) _ _ fun d hd => ?_
    refine Game.advantage_bind_le_nnreal _ _ _ fun α => ?_
    refine Game.advantage_bind_le_nnreal _ _ _ fun β => ?_
    exact Game.advantage_bind_le_nnreal _ _ _ fun i => hstep_err d hd _ _ _ i
  have hAdvIdealApprox :
      Game.advantage
        (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
        exactDDHIdeal ≤ ε := by
    rw [Game.advantage_comm, hDDHIdeal_eq]
    refine Game.advantage_bind_le_of_support (setup n) _ _ fun d hd => ?_
    refine Game.advantage_bind_le_nnreal _ _ _ fun α => ?_
    refine Game.advantage_bind_le_nnreal _ _ _ fun β => ?_
    refine Game.advantage_bind_le_nnreal _ _ _ fun γ => ?_
    exact Game.advantage_bind_le_nnreal _ _ _ fun i => hstep_err d hd _ _ _ i
  have hAdvTail :
      Game.advantage exactDDHIdeal
        ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
          if i.val < m then H (i.val + 1) else PMF.pure false) ≤
        (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal :=
    advantage_exactDDHIdeal_le F setup m (adv n) n
  rw [hEqReal]
  have ht1 := Game.advantage_triangle exactDDHReal
    (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
    ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
      if i.val < m then H (i.val + 1) else PMF.pure false)
  have ht2 := Game.advantage_triangle
    (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
    (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
    ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
      if i.val < m then H (i.val + 1) else PMF.pure false)
  have ht3 := Game.advantage_triangle
    (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
    exactDDHIdeal
    ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
      if i.val < m then H (i.val + 1) else PMF.pure false)
  calc Game.advantage exactDDHReal
        ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
          if i.val < m then H (i.val + 1) else PMF.pure false)
      ≤ Game.advantage exactDDHReal
          (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) +
        (Game.advantage
          (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
          (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) +
        (Game.advantage
          (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
          exactDDHIdeal +
        Game.advantage exactDDHIdeal
          ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
            if i.val < m then H (i.val + 1) else PMF.pure false))) :=
        ht1.trans (add_le_add le_rfl (ht2.trans (add_le_add le_rfl ht3)))
    _ ≤ ε +
        (Game.advantage
          (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
          (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) +
        (ε + (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal)) :=
        add_le_add hAdvRealApprox (add_le_add le_rfl (add_le_add hAdvIdealApprox hAdvTail))
    _ = Game.advantage
          (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
          (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) +
        2 * ε +
        (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal := by ring

/-- **Quantitative single-distinguisher DDH security bound for the Naor–Reingold group-PRF**
([BonehShoup2023], Exercises 10.4 & 10.11; [NaorReingold2004], Theorem 4.1): if `adversary` makes at
most `Q d` queries on `d ∈ (setup n).support` with modular-sampling slack bounded by `ε`, then its
PRF distinguishing advantage is at most `dyadicSize (inLen n)` times the single-challenge DDH
advantage of `naorReingoldToDDHDistinguisher` plus `2 * ε` plus the setup-averaged inverse group
order. -/
theorem advantage_naorReingoldWordGame_le (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) (Q : F.Desc → ℕ) {ε : ℝ≥0}
    (hQ : ∀ d ∈ (setup n).support, (adversary n (F.encDesc d)).IsQueryBounded (Q d))
    (hε : ∀ d ∈ (setup n).support,
      ((inLen n + 2 * Q d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + (F.encDesc d).length) ≤ ε) :
    Game.advantage
      (F.naorReingoldWordRealGame setup inLen adversary n)
      (F.naorReingoldWordIdealGame setup inLen adversary n) ≤
      (dyadicSize (inLen n) : ℝ≥0) *
        (Game.advantage
          (F.ddhRealGame setup (F.naorReingoldToDDHDistinguisher inLen adversary) n)
          (F.ddhIdealGame setup (F.naorReingoldToDDHDistinguisher inLen adversary) n) +
          2 * ε +
          (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal) :=
  advantage_naorReingoldDescGame_le F setup inLen (fun n d => adversary n (F.encDesc d)) n Q hQ hε

/-- **Modular-sampling distance between `naorReingoldProbRealGame` and `naorReingoldWordRealGame`**:
replacing `(inLen n + 1)` calls to `sampleNaorReingoldExp` by exact uniform `ZMod (F.order d)`
exponents changes the output distribution by at most `(inLen n + 1) / 2 ^ n`. -/
theorem advantage_naorReingoldProbRealGame_wordRealGame_le (setup : ℕ → PMF F.Desc)
    (inLen : ℕ → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    Game.advantage
      (F.naorReingoldProbRealGame setup inLen adversary n)
      (F.naorReingoldWordRealGame setup inLen adversary n) ≤
      ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  let m := inLen n
  simp only [naorReingoldProbRealGame, naorReingoldWordRealGame, PMF.monad_bind_eq_bind]
  refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  let detRun : (ZMod (F.order d) × (Fin m → ZMod (F.order d))) → PMF Bool := fun p =>
    OracleComp.interpret
      (ProbOracleComp.handler ProbComp.unifOracle fun request =>
        PMF.pure (F.naorReingoldWordOracle d (F.naorReingoldEval d p.1 p.2) request.2))
      (adversary n (F.encDesc d))
  have hprob :
      ProbComp.eval (do
        let α₀ ← F.sampleNaorReingoldExp n d
        let αs ← OracleComp.replicate m (F.sampleNaorReingoldExp n d)
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifFin fun request =>
            pure (if request.2.length = m then
              F.naorReingoldWordEval d α₀ αs request.2 else []))
          (adversary n (F.encDesc d))) =
      ((F.sampleModZModLaw (n + (F.encDesc d).length) d).bind fun α₀ =>
        (PMF.iid (F.sampleModZModLaw (n + (F.encDesc d).length) d) m).map (α₀, ·)).bind
        detRun := by
    simp only [ProbComp.eval_bind, ProbOracleComp.eval_interpret, ProbComp.eval_pure,
      eval_sampleNaorReingoldExp_eq_map_val F n d,
      eval_replicate_sampleNaorReingoldExp_eq_iid F n m d,
      PMF.bind_bind, PMF.bind_map, Function.comp_def]
    congr 1; funext α₀; congr 1; funext α
    dsimp only [detRun]
    congr 1; funext q
    cases q with
    | inl r => rfl
    | inr request =>
      dsimp only [ProbOracleComp.handler]
      by_cases hq : request.2.length = m
      · simp only [hq, ↓reduceIte, naorReingoldWordOracle]
        have hxs : List.ofFn (BitString.ofList m request.2) = request.2 :=
          BitString.ofFn_ofList hq
        have heval := F.naorReingoldWordEval_eq_encode d α₀.val (fun i => (α i).val)
          (BitString.ofList m request.2)
        simp only [ZMod.natCast_zmod_val, hxs] at heval
        exact congrArg PMF.pure heval
      · simp [hq, naorReingoldWordOracle]
  have hword :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₀ =>
        (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
          detRun (α₀, α)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₀ =>
        (PMF.iid (PMF.uniformOfFintype (ZMod (F.order d))) m).map (α₀, ·)).bind detRun := by
    rw [iid_uniformOfFintype]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  change Game.advantage _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₀ =>
      (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
        detRun (α₀, α)) ≤ _
  rw [hprob, hword, Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
  let μ := F.sampleModZModLaw (n + (F.encDesc d).length) d
  let ν := PMF.uniformOfFintype (ZMod (F.order d))
  have hswap (a : PMF (ZMod (F.order d))) (b : PMF (Fin m → ZMod (F.order d))) :
      (a.bind fun x => b.map (x, ·)) = (b.bind fun y => a.map (·, y)) := by
    simp only [PMF.map, Function.comp_def]
    exact PMF.bind_comm a b fun x y => PMF.pure (x, y)
  have hd_step : dist μ ν ≤ 1 / 2 ^ n := by
    rw [dist_comm]
    refine (F.dist_sampleModZModLaw_le (n + (F.encDesc d).length) d).trans ?_
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + (F.encDesc d).length) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n _)
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hj1 :
      dist (μ.bind fun x => (PMF.iid μ m).map (x, ·))
        (ν.bind fun x => (PMF.iid μ m).map (x, ·)) ≤ dist μ ν :=
    dist_bind_le _ _ _
  have hj2 :
      dist (ν.bind fun x => (PMF.iid μ m).map (x, ·))
        (ν.bind fun x => (PMF.iid ν m).map (x, ·)) ≤ m * dist μ ν := by
    rw [hswap ν (PMF.iid μ m), hswap ν (PMF.iid ν m)]
    exact (dist_bind_le _ _ _).trans (PMF.dist_iid_le μ ν m)
  calc dist ((μ.bind fun x => (PMF.iid μ m).map (x, ·)).bind detRun)
        ((ν.bind fun x => (PMF.iid ν m).map (x, ·)).bind detRun)
      ≤ dist (μ.bind fun x => (PMF.iid μ m).map (x, ·))
          (ν.bind fun x => (PMF.iid ν m).map (x, ·)) := dist_bind_le _ _ _
    _ ≤ dist (μ.bind fun x => (PMF.iid μ m).map (x, ·))
          (ν.bind fun x => (PMF.iid μ m).map (x, ·)) +
        dist (ν.bind fun x => (PMF.iid μ m).map (x, ·))
          (ν.bind fun x => (PMF.iid ν m).map (x, ·)) := dist_triangle _ _ _
    _ ≤ dist μ ν + m * dist μ ν := add_le_add hj1 hj2
    _ = (m + 1 : ℝ) * dist μ ν := by ring
    _ ≤ (m + 1 : ℝ) * (1 / 2 ^ n) := mul_le_mul_of_nonneg_left hd_step (by positivity)
    _ = ((((m + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by push_cast; ring

private theorem exists_pow_le_const_mul_two_pow (e : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ L : ℕ, (L + 1) ^ e ≤ C * 2 ^ L := by
  have hpoly : PolynomiallyBounded (fun L : ℕ => (L + 1) ^ e) := by fun_prop
  have hneg : Negligible fun L => ((L + 1) ^ e : ℝ≥0) * ((2 : ℝ≥0)⁻¹) ^ L := by
    have h1 := (negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)).polynomiallyBounded_mul
      hpoly
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h1
  have htend := (negligible_iff_coe.mp hneg 0).eventually_le_const (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp htend
  refine ⟨(L₀ + 1) ^ e + 1, by positivity, fun L => ?_⟩
  by_cases hL : L₀ ≤ L
  · have h := hL₀ L hL
    simp only [pow_zero, one_mul, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_inv, NNReal.coe_ofNat, inv_pow] at h
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    have hreal : ((L + 1 : ℕ) : ℝ) ^ e ≤ (2 : ℝ) ^ L := by
      have h' := mul_le_mul_of_nonneg_right h h2pos.le
      rw [mul_assoc, inv_mul_cancel₀ h2pos.ne', mul_one, one_mul] at h'
      simpa only [Nat.cast_add, Nat.cast_one] using h'
    have hnat : (L + 1) ^ e ≤ 2 ^ L := by exact_mod_cast hreal
    exact hnat.trans (Nat.le_mul_of_pos_left _ (by positivity))
  · have hp1 : (L + 1) ^ e ≤ (L₀ + 1) ^ e + 1 :=
      (Nat.pow_le_pow_left (by omega) e).trans (Nat.le_succ _)
    exact hp1.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos L))

private theorem DDH.negligible_naorReingoldDescGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adv : ℕ → F.Desc → WordOracleComp Unit Bool}
    (hadv : IsOraclePPTOn (encPair encUnary F.encDesc) encBool (fun p => adv p.1 p.2)) :
    Negligible fun n =>
      Game.advantage
        (naorReingoldDescRealGame F setup inLen adv n)
        (naorReingoldDescIdealGame F setup inLen adv n) := by
  obtain ⟨cQ, eQ, hQb⟩ := hadv.query_bounds
  obtain ⟨C, _, hC⟩ := exists_pow_le_const_mul_two_pow eQ
  let Q : ℕ → F.Desc → ℕ := fun n d =>
    cQ * ((encPair encUnary F.encDesc (n, d)).length + 1) ^ eQ
  let ε : ℕ → ℝ≥0 := fun n =>
    ((inLen n + 2 * cQ * C * (2 * n + 6) ^ eQ : ℕ) : ℝ≥0) * ((2 : ℝ≥0)⁻¹) ^ n
  have hQ_supp (n : ℕ) (d : F.Desc) (_ : d ∈ (setup n).support) :
      (adv n d).IsQueryBounded (Q n d) :=
    (hQb (n, d)).1
  have hε_supp (n : ℕ) (d : F.Desc) (_ : d ∈ (setup n).support) :
      ((inLen n + 2 * Q n d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + (F.encDesc d).length) ≤ ε n := by
    let L := (F.encDesc d).length
    have hlen : (encPair encUnary F.encDesc (n, d)).length + 1 ≤ (2 * n + 6) * (L + 1) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      dsimp only [L]
      nlinarith
    have hQd_le : Q n d ≤ cQ * C * (2 * n + 6) ^ eQ * 2 ^ L := by
      calc Q n d
          ≤ cQ * ((2 * n + 6) * (L + 1)) ^ eQ :=
            Nat.mul_le_mul_left cQ (Nat.pow_le_pow_left hlen eQ)
        _ = cQ * ((2 * n + 6) ^ eQ * (L + 1) ^ eQ) := by rw [Nat.mul_pow]
        _ ≤ cQ * ((2 * n + 6) ^ eQ * (C * 2 ^ L)) :=
            Nat.mul_le_mul_left cQ (Nat.mul_le_mul_left _ (hC L))
        _ = cQ * C * (2 * n + 6) ^ eQ * 2 ^ L := by ring
    have hnum_le : inLen n + 2 * Q n d ≤ (inLen n + 2 * cQ * C * (2 * n + 6) ^ eQ) * 2 ^ L := by
      have h1 : inLen n ≤ inLen n * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
      nlinarith
    have hcast :
        (((inLen n + 2 * Q n d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + L)) ≤
          (((inLen n + 2 * cQ * C * (2 * n + 6) ^ eQ : ℕ) * (2 : ℝ≥0) ^ L) /
            ((2 : ℝ≥0) ^ n * (2 : ℝ≥0) ^ L)) := by
      rw [pow_add]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact_mod_cast hnum_le
    have h2L : ((2 : ℝ≥0) ^ L) ≠ 0 := by positivity
    refine hcast.trans_eq ?_
    rw [mul_div_mul_right _ _ h2L, div_eq_mul_inv, ← inv_pow]
  have hinLen_poly : PolynomiallyBounded inLen := hinLen.tidy.polynomiallyBounded
  have hcap_poly : PolynomiallyBounded (fun n => dyadicSize (inLen n)) :=
    dyadicSize_polynomiallyBounded.comp hinLen_poly
  have hnum_poly : PolynomiallyBounded
      (fun n => inLen n + 2 * cQ * C * (2 * n + 6) ^ eQ) := by
    fun_prop
  have hε_neg : Negligible ε :=
    (negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)).polynomiallyBounded_mul hnum_poly
  have hddh_neg : Negligible fun n =>
      Game.advantage
        (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
        (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) :=
    hDDH _ (isPPTOn_naorReingoldDescToDDHDistinguisher F hinLen hadv)
  have hinv_neg := hDDH.negligible_expected_inv_order
  have hsum_neg : Negligible fun n =>
      Game.advantage
        (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
        (F.ddhIdealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) +
        2 * ε n +
        (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal :=
    (hddh_neg.add (hε_neg.const_mul 2)).add hinv_neg
  have htot_neg := hsum_neg.polynomiallyBounded_mul hcap_poly
  refine negligible_of_le htot_neg fun n => ?_
  simpa only [mul_comm (dyadicSize (inLen n) : ℝ≥0)] using
    advantage_naorReingoldDescGame_le F setup inLen adv n (Q n) (hQ_supp n) (hε_supp n)

/-- **Asymptotic DDH security of the Naor–Reingold group-PRF (`naorReingoldWordRealGame`)**
([BonehShoup2023], Exercise 10.4; [NaorReingold2004], Theorem 4.1): if `F.DDH setup` holds and
`inLen` is computable in polynomial time in unary, no `IsOraclePPT` adversary can distinguish
`naorReingoldWordRealGame` from `naorReingoldWordIdealGame` with non-negligible advantage. -/
theorem DDH.negligible_naorReingoldWordGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldWordRealGame setup inLen adversary n)
        (F.naorReingoldWordIdealGame setup inLen adversary n) := by
  have henc : ComputableTidilyInPolyTime
      (fun p : ℕ × F.Desc => (p.1, F.encDesc p.2))
      (encPair encUnary F.encDesc) (encPair encUnary encBits) :=
    (ComputableTidilyInPolyTime.fst encUnary F.encDesc).prod
      (ComputableTidilyInPolyTime.encoded (ComputableTidilyInPolyTime.snd encUnary F.encDesc))
  have hadv : IsOraclePPTOn (encPair encUnary F.encDesc) encBool
      (fun p => adversary p.1 (F.encDesc p.2)) :=
    hadversary.on.preprocess henc
  exact hDDH.negligible_naorReingoldDescGame hinLen hadv

/-- **Asymptotic DDH security of the executable Naor–Reingold group-PRF
(`naorReingoldProbRealGame`)** ([BonehShoup2023], Exercise 10.4; [NaorReingold2004], Theorem 4.1):
if `F.DDH setup` holds and `inLen` is computable in polynomial time in unary, no `IsOraclePPT`
adversary can distinguish `naorReingoldProbRealGame` from `naorReingoldWordIdealGame` with
non-negligible advantage. -/
theorem DDH.negligible_naorReingoldProbGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldProbRealGame setup inLen adversary n)
        (F.naorReingoldWordIdealGame setup inLen adversary n) := by
  have hinLen_poly : PolynomiallyBounded inLen := hinLen.tidy.polynomiallyBounded
  have hprob_neg : Negligible fun n => ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    have hp : PolynomiallyBounded (fun n => inLen n + 1) := by fun_prop
    have h1 := (negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)).polynomiallyBounded_mul
      hp
    refine negligible_of_le h1 fun n => ?_
    rw [div_eq_mul_inv, ← inv_pow]
  refine negligible_of_le
    (hprob_neg.add (hDDH.negligible_naorReingoldWordGame hinLen hadversary)) fun n => ?_
  exact (Game.advantage_triangle _ (F.naorReingoldWordRealGame setup inLen adversary n) _).trans
    (add_le_add (F.advantage_naorReingoldProbRealGame_wordRealGame_le setup inLen adversary n)
      le_rfl)

/-! ### Universal-hash bit-string Naor–Reingold PRF -/

/-- Word-level universal-hash Naor–Reingold evaluation (paraphrase of [NaorReingold2004],
Section 4.1, Construction 4.2): evaluate `naorReingoldWordEval` and hash the resulting encoded
group element into `{0, 1}^{outLen}` with `linearHashKDF`. -/
@[expose] def naorReingoldHashedWordEval (outLen : ℕ) (bound : F.Desc → ℕ) (d : F.Desc)
    (seed : List Bool) (α₀ : ℕ) (αs : List ℕ) (xs : List Bool) : List Bool :=
  F.linearHashKDF (fun _ => outLen) bound ((d, seed), F.naorReingoldWordEval d α₀ αs xs)

/-- `naorReingoldHashedWordEval` always outputs `outLen` bits. -/
@[simp] theorem length_naorReingoldHashedWordEval (outLen : ℕ) (bound : F.Desc → ℕ)
    (d : F.Desc) (seed : List Bool) (α₀ : ℕ) (αs : List ℕ) (xs : List Bool) :
    (F.naorReingoldHashedWordEval outLen bound d seed α₀ αs xs).length = outLen := by
  simp [naorReingoldHashedWordEval]

/-- `naorReingoldHashedWordEval` is computable in polynomial time when `outLen` is given in unary
and `bound` is computable in polynomial time in unary from `d`. -/
theorem computableInPolyTime_naorReingoldHashedWordEval {bound : F.Desc → ℕ}
    (hbound : ComputableInPolyTime bound F.encDesc encUnary) :
    ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × ℕ × List ℕ × List Bool =>
        F.naorReingoldHashedWordEval input.1 bound input.2.1 input.2.2.1 input.2.2.2.1
          input.2.2.2.2.1 input.2.2.2.2.2)
      (encPair encUnary
        (encPair F.encDesc
          (encPair encBits (encPair encNat (encPair (encList encNat) encBits)))))
      encBits := by
  let EIn := encPair encUnary
    (encPair F.encDesc (encPair encBits (encPair encNat (encPair (encList encNat) encBits))))
  have hout : ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × ℕ × List ℕ × List Bool => input.1)
      EIn encUnary := by fun_prop
  have hd : ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × ℕ × List ℕ × List Bool => input.2.1)
      EIn F.encDesc := by fun_prop
  have hseed : ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × ℕ × List ℕ × List Bool => input.2.2.1)
      EIn encBits := by fun_prop
  have hnr : ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × ℕ × List ℕ × List Bool =>
        F.naorReingoldWordEval input.2.1 input.2.2.2.1 input.2.2.2.2.1 input.2.2.2.2.2)
      EIn encBits :=
    F.computableInPolyTime_naorReingoldWordEval.comp
      (hd.prod ((by fun_prop : ComputableInPolyTime _ EIn encNat).prod
        ((by fun_prop : ComputableInPolyTime _ EIn (encList encNat)).prod
          (by fun_prop : ComputableInPolyTime _ EIn encBits))))
  have hpad : ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × ℕ × List ℕ × List Bool =>
        Cslib.BitString.padWord (bound input.2.1)
          (F.naorReingoldWordEval input.2.1 input.2.2.2.1 input.2.2.2.2.1 input.2.2.2.2.2))
      EIn encBits := by
    have hb := (hbound.comp hd).tidy
    have hnr_t := hnr.tidy
    exact .of_tidy (ComputableTidilyInPolyTime.bitsPadWord hb hnr_t)
  simpa only [naorReingoldHashedWordEval, linearHashKDF] using
    Cslib.BitString.LinearHash.computableInPolyTime_wordHash hout hseed hpad

/-- Setup-parameterized real universal-hash Naor–Reingold bit-string PRF game with exact uniform
`ZMod (F.order d)` exponents and public hash seed `(d, seed)` encoded via `F.withSeed.encDesc`
(paraphrase of [NaorReingold2004], Section 4.1, Construction 4.2, Theorem 4.3, and Remark 4.2). -/
@[expose] noncomputable def naorReingoldHashedRealGame (setup : ℕ → PMF F.Desc)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    Game := do
  let ds ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n
  let α₀ ← PMF.uniformOfFintype (ZMod (F.order ds.1))
  let α ← PMF.uniformOfFintype (Fin (inLen n) → ZMod (F.order ds.1))
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifOracle fun request =>
      PMF.pure (if request.2.length = inLen n then
        F.linearHashKDF (fun _ => outLen n) bound
          (ds, F.encode ds.1 (F.naorReingoldEval ds.1 α₀ α
            (BitString.ofList (inLen n) request.2)))
      else []))
    (adversary n (F.withSeed.encDesc ds))

/-- Setup-parameterized executable real universal-hash Naor–Reingold bit-string PRF game sampling
exponents via `sampleNaorReingoldExp` (original). -/
@[expose] noncomputable def naorReingoldHashedProbRealGame (setup : ℕ → PMF F.Desc)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) : Game := do
  let ds ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n
  ProbComp.eval (do
    let α₀ ← F.sampleNaorReingoldExp n ds.1
    let αs ← OracleComp.replicate (inLen n) (F.sampleNaorReingoldExp n ds.1)
    OracleComp.interpret
      (ProbOracleComp.handler ProbComp.unifFin fun request =>
        pure (if request.2.length = inLen n then
          F.naorReingoldHashedWordEval (outLen n) bound ds.1 ds.2 α₀ αs request.2
        else []))
      (adversary n (F.withSeed.encDesc ds)))

/-- Setup-parameterized ideal bit-string random-function game for universal-hash Naor–Reingold:
sample `(d, seed) ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n`, draw an independent
uniform random function `f : BitString (inLen n) → BitString (outLen n)`, and pass
`F.withSeed.encDesc (d, seed)` to `adversary` (paraphrase of [NaorReingold2004], Section 4.1,
Theorem 4.3 and Remark 4.2). -/
@[expose] noncomputable def naorReingoldHashedIdealGame (setup : ℕ → PMF F.Desc)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    Game := do
  let ds ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n
  let f ← PMF.uniformOfFintype (BitString (inLen n) → BitString (outLen n))
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifOracle fun request =>
      PMF.pure (if request.2.length = inLen n then
        List.ofFn (f (BitString.ofList (inLen n) request.2))
      else []))
    (adversary n (F.withSeed.encDesc ds))

/-- Intermediate hybrid game for universal-hash Naor–Reingold: sample `(d, seed)` via `seededSetup`,
draw an independent uniform random group-valued table `B : BitString (inLen n) → ZMod (F.order d)`,
and hash each queried group element `B x • g` with `linearHashKDF` (paraphrase of
[NaorReingold2004], Section 4.1, Theorem 4.3 and Remark 4.2, using Lemma 4.2). -/
@[expose] noncomputable def naorReingoldHashedGroupIdealGame (setup : ℕ → PMF F.Desc)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) : Game := do
  let ds ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n
  let B ← PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order ds.1))
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifOracle fun request =>
      PMF.pure (if request.2.length = inLen n then
        F.linearHashKDF (fun _ => outLen n) bound
          (ds, F.encode ds.1 (B (BitString.ofList (inLen n) request.2) • F.generator ds.1))
      else []))
    (adversary n (F.withSeed.encDesc ds))

private theorem run_eager_bitStringTable_eq_presample {m ℓ Q : ℕ}
    {prog : WordOracleComp Unit Bool} (hQ : prog.IsQueryBounded Q)
    (outLaw : PMF (BitString ℓ)) :
    ((PMF.pi (fun _ : BitString m => outLaw)).bind fun f =>
      OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = m then
            List.ofFn (f (BitString.ofList m request.2))
          else []))
        prog) =
    (PMF.pi (fun _ : Fin Q => outLaw)).bind fun tbl =>
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
          (OracleComp.withSampleList []
            (fun (fresh : List Bool) (request : Unit × List Bool)
                (cache : List (List Bool × List Bool)) =>
              if request.2.length = m then
                match cache.lookup request.2 with
                | some v => PMF.pure (v, cache)
                | none => PMF.pure (fresh, (request.2, fresh) :: cache)
              else PMF.pure ([], cache))))
        prog).run ([], List.ofFn fun i => List.ofFn (tbl i))).map fun res => res.1) := by
  let keyMap : BitString m ↪ List Bool := ⟨List.ofFn, List.ofFn_injective⟩
  let valMap : BitString ℓ → List Bool := List.ofFn
  let sample' : List Bool → PMF (List Bool) := fun _ => outLaw.map valMap
  let innerProg : ProbOracleComp (fun _ : BitString m => List Bool) Bool :=
    OracleComp.interpret
      (ProbOracleComp.handler (fun r => ProbOracleComp.sample (ProbComp.unifFin r))
        fun request =>
          if request.2.length = m then
            ProbOracleComp.query (BitString.ofList m request.2)
          else pure [])
      prog
  have hmemo := RandomOracle.interpret_prob_eq_memoize_map keyMap valMap
    (fun _ => outLaw) sample' (fun _ => rfl) innerProg
  simp only [PMF.monad_bind_eq_bind] at hmemo
  have hlhs :
      ((PMF.pi (fun _ : BitString m => outLaw)).bind fun f =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle fun request =>
            PMF.pure (if request.2.length = m then
              List.ofFn (f (BitString.ofList m request.2))
            else []))
          prog) =
      ((PMF.pi (fun _ : BitString m => outLaw)).bind fun f =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle fun key => PMF.pure (valMap (f key)))
          innerProg) := by
    congr 1; funext f
    dsimp only [innerProg]
    rw [OracleComp.interpret_interpret]
    congr 1; funext q
    cases q with
    | inl r => simp [ProbOracleComp.handler, ProbOracleComp.sample, ProbComp.unifFin]
    | inr request =>
      dsimp only [ProbOracleComp.handler, Function.comp_apply]
      by_cases hq : request.2.length = m <;>
        simp [hq, ProbOracleComp.interpret_query, valMap, PMF.monad_pure_eq_pure]
  have hrhs :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
          (fun key => memoize sample' (keyMap key)))
        innerProg).run []).map Prod.fst =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
          fun (request : Unit × List Bool) (cache : List (List Bool × List Bool)) =>
            (outLaw.map valMap).bind fun fresh =>
              if request.2.length = m then
                match cache.lookup request.2 with
                | some v => PMF.pure (v, cache)
                | none => PMF.pure (fresh, (request.2, fresh) :: cache)
              else PMF.pure ([], cache))
        prog).run []).map Prod.fst := by
    refine congrArg (PMF.map Prod.fst) ?_
    dsimp only [innerProg]
    change (OracleComp.interpret (m := StateT (List (List Bool × List Bool)) PMF) _
      (OracleComp.interpret _ prog)) [] = _
    rw [OracleComp.interpret_interpret]
    refine congrFun (congrArg (fun h => OracleComp.interpret h prog) ?_) []
    funext q
    cases q with
    | inl r =>
      funext cache
      simp [ProbOracleComp.handler, ProbOracleComp.sample, ProbComp.unifFin, StateT.lift]
    | inr request =>
      funext cache
      dsimp only [ProbOracleComp.handler, Function.comp_apply]
      by_cases hq : request.2.length = m
      · simp only [hq, ↓reduceIte, ProbOracleComp.interpret_query, keyMap,
          Function.Embedding.coeFn_mk, BitString.ofFn_ofList hq, memoize, sample']
        cases cache.lookup request.2 with
        | some v =>
          simp only [PMF.monad_pure_eq_pure, PMF.bind_const]
        | none =>
          simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      · simp only [hq, ↓reduceIte, PMF.bind_const]
        rfl
  have hpre := congrArg (PMF.map Prod.fst)
    (hQ.run_interpret_presample (outLaw.map valMap) []
      (fun (fresh : List Bool) (request : Unit × List Bool)
          (cache : List (List Bool × List Bool)) =>
        if request.2.length = m then
          match cache.lookup request.2 with
          | some v => PMF.pure (v, cache)
          | none => PMF.pure (fresh, (request.2, fresh) :: cache)
        else PMF.pure ([], cache)) [])
  rw [hlhs, hmemo, hrhs, ← hpre, PMF.map_bind, PMF.iid_map, PMF.iid_eq_pi, PMF.map_comp,
    PMF.bind_map]
  congr 1; funext tbl
  simp only [Function.comp_def, PMF.map_comp, valMap]

private theorem advantage_naorReingoldHashedIdeal_at_le (F : PrimeOrderGroupFamily)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher)
    (n Q : ℕ) (d : F.Desc)
    (hbound : ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hQ : ∀ seed : BitString (outLen n * (2 * bound d + 1)),
      (adversary n (F.withSeed.encDesc (d, List.ofFn seed))).IsQueryBounded Q) :
    Game.advantage
      ((Cslib.BitString.uniformList (F.linearHashSeedLen outLen bound n d)).bind fun seed =>
        (PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order d))).bind fun B =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = inLen n then
                F.linearHashKDF (fun _ => outLen n) bound
                  ((d, seed), F.encode d
                    (B (BitString.ofList (inLen n) request.2) • F.generator d))
              else []))
            (adversary n (F.withSeed.encDesc (d, seed))))
      ((Cslib.BitString.uniformList (F.linearHashSeedLen outLen bound n d)).bind fun seed =>
        (PMF.uniformOfFintype (BitString (inLen n) → BitString (outLen n))).bind fun f =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = inLen n then
                List.ofFn (f (BitString.ofList (inLen n) request.2))
              else []))
            (adversary n (F.withSeed.encDesc (d, seed)))) ≤
      (Q : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (F.order d : ℝ≥0)) / 2) := by
  let m := inLen n
  let ℓ := outLen n
  let W := 2 * bound d + 1
  let source : PMF (BitString W) :=
    (PMF.uniformOfFintype (ZMod (F.order d))).map (F.paddedGeneratorMultiple bound d)
  let hashSeed : BitString (ℓ * W) → BitString W → BitString ℓ := fun seed =>
    Cslib.BitString.LinearHash.hash (Cslib.BitString.blocksEquiv (m := ℓ) (k := W) seed)
  let detKernel : BitString (ℓ * W) × (Fin Q → BitString ℓ) → PMF Bool := fun pair =>
    (((OracleComp.interpret
      (ProbOracleComp.handler (fun r => StateT.lift (ProbComp.unifOracle r))
        (OracleComp.withSampleList []
          (fun (fresh : List Bool) (request : Unit × List Bool)
              (cache : List (List Bool × List Bool)) =>
            if request.2.length = m then
              match cache.lookup request.2 with
              | some v => PMF.pure (v, cache)
              | none => PMF.pure (fresh, (request.2, fresh) :: cache)
            else PMF.pure ([], cache))))
      (adversary n (F.withSeed.encDesc (d, List.ofFn pair.1)))).run
        ([], List.ofFn fun i => List.ofFn (pair.2 i))).map fun res => res.1)
  have hreal :
      ((Cslib.BitString.uniformList (F.linearHashSeedLen outLen bound n d)).bind fun seed =>
        (PMF.uniformOfFintype (BitString m → ZMod (F.order d))).bind fun B =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = m then
                F.linearHashKDF (fun _ => ℓ) bound
                  ((d, seed), F.encode d (B (BitString.ofList m request.2) • F.generator d))
              else []))
            (adversary n (F.withSeed.encDesc (d, seed)))) =
      ((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
        (PMF.pi (fun _ : Fin Q => source.map (hashSeed seed))).map (seed, ·)).bind detKernel := by
    simp only [linearHashSeedLen, Cslib.BitString.uniformList, PMF.bind_map, PMF.bind_bind,
      Function.comp_def]
    congr 1; funext seed
    have htable :
        ((PMF.uniformOfFintype (BitString m → ZMod (F.order d))).bind fun B =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = m then
                F.linearHashKDF (fun _ => ℓ) bound
                  ((d, List.ofFn seed),
                    F.encode d (B (BitString.ofList m request.2) • F.generator d))
              else []))
            (adversary n (F.withSeed.encDesc (d, List.ofFn seed)))) =
        ((PMF.pi (fun _ : BitString m => source.map (hashSeed seed))).bind fun f =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = m then
                List.ofFn (f (BitString.ofList m request.2))
              else []))
            (adversary n (F.withSeed.encDesc (d, List.ofFn seed)))) := by
      have hpi :
          PMF.pi (fun _ : BitString m => source.map (hashSeed seed)) =
            (PMF.uniformOfFintype (BitString m → ZMod (F.order d))).map
              (fun B x => hashSeed seed (F.paddedGeneratorMultiple bound d (B x))) := by
        dsimp only [source]
        simp_rw [PMF.map_comp]
        rw [PMF.pi_map, pi_uniformOfFintype]
        rfl
      rw [hpi, PMF.bind_map]
      congr 1; funext B
      dsimp only [Function.comp_apply]
      congr 1; funext q
      cases q with
      | inl r => rfl
      | inr request =>
        dsimp only [ProbOracleComp.handler]
        by_cases hq : request.2.length = m
        · simp only [hq, ↓reduceIte]
          have hpad := F.ofFn_paddedGeneratorMultiple hbound (B (BitString.ofList m request.2))
          have hhash :
              F.linearHashKDF (fun _ => ℓ) bound
                ((d, List.ofFn seed),
                  F.encode d (B (BitString.ofList m request.2) • F.generator d)) =
              List.ofFn (hashSeed seed
                (F.paddedGeneratorMultiple bound d (B (BitString.ofList m request.2)))) := by
            simp only [linearHashKDF, ← hpad, Cslib.BitString.LinearHash.wordHash_eq_ofFn,
              Cslib.BitString.ofList_ofFn, Cslib.BitString.blocksEquiv_apply, hashSeed]
          rw [hhash]
        · simp [hq]
    rw [htable, run_eager_bitStringTable_eq_presample (hQ seed) (source.map (hashSeed seed))]
  have hideal :
      ((Cslib.BitString.uniformList (F.linearHashSeedLen outLen bound n d)).bind fun seed =>
        (PMF.uniformOfFintype (BitString m → BitString ℓ)).bind fun f =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = m then
                List.ofFn (f (BitString.ofList m request.2))
              else []))
            (adversary n (F.withSeed.encDesc (d, seed)))) =
      ((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
        (PMF.pi (fun _ : Fin Q => PMF.uniformOfFintype (BitString ℓ))).map (seed, ·)).bind
        detKernel := by
    simp only [linearHashSeedLen, Cslib.BitString.uniformList, PMF.bind_map, PMF.bind_bind,
      Function.comp_def]
    congr 1; funext seed
    rw [← pi_uniformOfFintype (ι := BitString m) (α := BitString ℓ),
      run_eager_bitStringTable_eq_presample (hQ seed) (PMF.uniformOfFintype (BitString ℓ))]
  change Game.advantage
    ((Cslib.BitString.uniformList (F.linearHashSeedLen outLen bound n d)).bind fun seed =>
      (PMF.uniformOfFintype (BitString m → ZMod (F.order d))).bind fun B => _)
    ((Cslib.BitString.uniformList (F.linearHashSeedLen outLen bound n d)).bind fun seed =>
      (PMF.uniformOfFintype (BitString m → BitString ℓ)).bind fun f => _) ≤ _
  rw [hreal, hideal, Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
  have hlhl :
      dist
        ((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
          (source.map (hashSeed seed)).map (seed, ·))
        ((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
          (PMF.uniformOfFintype (BitString ℓ)).map (seed, ·)) ≤
        Real.sqrt (Fintype.card (BitString ℓ) * collisionProbability source) / 2 := by
    simpa only [seededHash, PMF.map_comp, Function.comp_def] using
      (Cslib.BitString.LinearHash.isTwoUniversal_flat W ℓ).leftover_hash source
  have hcoll : collisionProbability source = (F.order d : ℝ)⁻¹ := by
    simp only [source,
      collisionProbability_map_of_injective _ _ (F.paddedGeneratorMultiple_injective hbound),
      collisionProbability_uniform, ZMod.card]
  calc dist
        (((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
          (PMF.pi (fun _ : Fin Q => source.map (hashSeed seed))).map (seed, ·)).bind detKernel)
        (((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
          (PMF.pi (fun _ : Fin Q => PMF.uniformOfFintype (BitString ℓ))).map (seed, ·)).bind
          detKernel)
      ≤ dist
          ((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
            (PMF.pi (fun _ : Fin Q => source.map (hashSeed seed))).map (seed, ·))
          ((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
            (PMF.pi (fun _ : Fin Q => PMF.uniformOfFintype (BitString ℓ))).map (seed, ·)) :=
        dist_bind_le _ _ _
    _ ≤ ∑ _i : Fin Q,
          dist
            ((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
              (source.map (hashSeed seed)).map (seed, ·))
            ((PMF.uniformOfFintype (BitString (ℓ * W))).bind fun seed =>
              (PMF.uniformOfFintype (BitString ℓ)).map (seed, ·)) :=
        PMF.dist_bind_pair_pi_le_sum _ _ _
    _ ≤ ∑ _i : Fin Q, (Real.sqrt (Fintype.card (BitString ℓ) * collisionProbability source) / 2) :=
        Finset.sum_le_sum fun _ _ => hlhl
    _ = (Q : ℝ) * (Real.sqrt ((2 : ℝ) ^ ℓ * (F.order d : ℝ)⁻¹) / 2) := by
        simp [BitString, hcoll]
    _ = ↑((Q : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ ℓ / (F.order d : ℝ≥0)) / 2)) := by
        push_cast
        rw [← div_eq_mul_inv]

/-- **Multi-query Leftover Hash Lemma bound for hashed Naor–Reingold** (paraphrase of
[NaorReingold2004], Section 4.1, Lemma 4.2; [BonehShoup2023], Section 8.10.4, Theorem 8.11, p. 334):
if `adversary` makes at most `Q` queries on `(setup n).support` and `qMin ≤ F.order d`, then
replacing hashed random group elements by a uniform random function `BitString (inLen n) →
BitString (outLen n)` changes the output distribution by at most
`Q * (√(2 ^ (outLen n) / qMin) / 2)`. -/
theorem advantage_naorReingoldHashedIdeal_le (setup : ℕ → PMF F.Desc) (inLen outLen : ℕ → ℕ)
    (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n Q qMin : ℕ)
    (hq0 : 0 < qMin)
    (hbound : ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq : ∀ d ∈ (setup n).support, qMin ≤ F.order d)
    (hQ : ∀ d ∈ (setup n).support,
      ∀ seed : BitString (outLen n * (2 * bound d + 1)),
        (adversary n (F.withSeed.encDesc (d, List.ofFn seed))).IsQueryBounded Q) :
    Game.advantage
      (F.naorReingoldHashedGroupIdealGame setup inLen outLen bound adversary n)
      (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) ≤
      (Q : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (qMin : ℝ≥0)) / 2) := by
  simp only [naorReingoldHashedGroupIdealGame, naorReingoldHashedIdealGame, seededSetup,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  refine Game.advantage_bind_le_of_support (setup n) _ _ fun d hd => ?_
  refine (advantage_naorReingoldHashedIdeal_at_le F inLen outLen bound adversary n Q d
    (hbound d hd) (hQ d hd)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine div_le_div_of_nonneg_right (NNReal.sqrt_le_sqrt.mpr ?_) (by norm_num)
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hq0)
    (by exact_mod_cast hq d hd)

private noncomputable def hashedAdvGroup (F : PrimeOrderGroupFamily) (inLen outLen : ℕ → ℕ)
    (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n : ℕ)
    (ds : F.withSeed.Desc) : WordOracleComp Unit Bool :=
  Prod.fst <$> (OracleComp.interpret
    (ProbOracleComp.handler
      (fun r => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin r)))
      fun (request : Unit × List Bool) (_ : Unit) =>
        if request.2.length = inLen n then
          (fun raw => (F.linearHashKDF (fun _ => outLen n) bound (ds, raw), ())) <$>
            (List.take (bound ds.1) <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                ((), request.2))
        else pure ([], ()))
    (adversary n (F.withSeed.encDesc ds))).run ()

private theorem isOraclePPTOn_hashedAdvGroup (F : PrimeOrderGroupFamily) {inLen outLen : ℕ → ℕ}
    {bound : F.Desc → ℕ}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPTOn (encPair encUnary F.withSeed.encDesc) encBool
      (fun p => hashedAdvGroup F inLen outLen bound adversary p.1 p.2) := by
  let ECaller := encPair encUnary F.withSeed.encDesc
  let EHandler := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hprep : ComputableTidilyInPolyTime
      (fun p : ℕ × F.withSeed.Desc => (p.1, F.withSeed.encDesc p.2))
      ECaller (encPair encUnary encBits) :=
    (ComputableTidilyInPolyTime.fst encUnary F.withSeed.encDesc).prod
      (ComputableTidilyInPolyTime.encoded
        (ComputableTidilyInPolyTime.snd encUnary F.withSeed.encDesc))
  have hguard : ComputableTidilyInPolyTime
      (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit =>
        pair.2.1.2.length == inLen pair.1.1)
      EHandler encBool := by
    have hqlen : ComputableTidilyInPolyTime
        (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit => pair.2.1.2.length)
        EHandler encUnary := by
      dsimp only [EHandler]
      fun_prop
    have hm : ComputableTidilyInPolyTime
        (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit => inLen pair.1.1)
        EHandler encUnary :=
      hinLen.tidy.comp (by dsimp only [EHandler, ECaller]; fun_prop)
    exact ComputableTidilyInPolyTime.unary_beq hqlen hm
  have htake : IsOraclePPTOn EHandler encBits
      (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit =>
        List.take (bound pair.1.2.1) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), pair.2.1.2)) :=
    IsOraclePPTOn.query_take ()
      (request := fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit => pair.2.1.2)
      (limit := fun pair => bound pair.1.2.1)
      (by dsimp only [EHandler]; fun_prop)
      (hbound.tidy.comp (by dsimp only [EHandler, ECaller, withSeed]; fun_prop))
  have hhash_post : ComputableTidilyInPolyTime
      (fun pair : ((ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit) × List Bool =>
        (F.linearHashKDF (fun _ => outLen pair.1.1.1) bound (pair.1.1.2, pair.2), ()))
      (encPair EHandler encBits) (encPair encBits (encFinEnum Unit)) := by
    have hout_t : ComputableInPolyTime
        (fun pair : ((ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit) × List Bool =>
          outLen pair.1.1.1)
        (encPair EHandler encBits) encUnary :=
      houtLen.comp (by dsimp only [EHandler, ECaller]; fun_prop)
    have hseed_t : ComputableInPolyTime
        (fun pair : ((ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit) × List Bool =>
          pair.1.1.2.2)
        (encPair EHandler encBits) encBits := by
      dsimp only [EHandler, ECaller, withSeed]; fun_prop
    have hpad_t : ComputableInPolyTime
        (fun pair : ((ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit) × List Bool =>
          Cslib.BitString.padWord (bound pair.1.1.2.1) pair.2)
        (encPair EHandler encBits) encBits := by
      have hb := (hbound.comp
        (by dsimp only [EHandler, ECaller, withSeed]; fun_prop :
          ComputableInPolyTime
            (fun pair : ((ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit) × List Bool =>
              pair.1.1.2.1)
            (encPair EHandler encBits) F.encDesc)).tidy
      have hr : ComputableTidilyInPolyTime
          (fun pair : ((ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit) × List Bool => pair.2)
          (encPair EHandler encBits) encBits := by fun_prop
      exact .of_tidy (ComputableTidilyInPolyTime.bitsPadWord hb hr)
    have hkdf := (Cslib.BitString.LinearHash.computableInPolyTime_wordHash
      hout_t hseed_t hpad_t).tidy
    exact hkdf.prod (ComputableTidilyInPolyTime.const ())
  have hvalid : IsOraclePPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit =>
        (fun raw => (F.linearHashKDF (fun _ => outLen pair.1.1) bound (pair.1.2, raw), ())) <$>
          (List.take (bound pair.1.2.1) <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
              ((), pair.2.1.2))) :=
    htake.map_with hhash_post
  have hinvalid : IsOraclePPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun _ => (pure ([], ()) : WordOracleComp Unit (List Bool × Unit))) := by
    simpa only [ProbOracleComp.sample_pure] using
      (ComputableInPolyTime.const ([], ())).isPPTOn.isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) × Unit =>
        if pair.2.1.2.length = inLen pair.1.1 then
          (fun raw => (F.linearHashKDF (fun _ => outLen pair.1.1) bound (pair.1.2, raw), ())) <$>
            (List.take (bound pair.1.2.1) <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                ((), pair.2.1.2))
        else pure ([], ())) := by
    refine (IsOraclePPTOn.cond hguard hvalid hinvalid).congr fun pair State oracle s => ?_
    by_cases h : pair.2.1.2.length = inLen pair.1.1 <;> simp [h]
  have hres : ComputableTidilyInPolyTime
      (fun pair : (ℕ × F.withSeed.Desc) × List Bool => outLen pair.1.1 + 1)
      (encPair ECaller encBits) encUnary := by
    have ho := houtLen.tidy.comp (by dsimp only [ECaller]; fun_prop :
      ComputableTidilyInPolyTime
        (fun pair : (ℕ × F.withSeed.Desc) × List Bool => pair.1.1)
        (encPair ECaller encBits) encUnary)
    have hsucc : ComputableTidilyInPolyTime (fun n => n + 1) encUnary encUnary := by fun_prop
    exact hsucc.comp ho
  have hsub := hadversary.on.run_interpret_preprocess_open (State := Unit)
    (operationEncoding := encFinEnum Unit) (stateEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × F.withSeed.Desc) (request : Unit × List Bool) (_ : Unit) =>
      if request.2.length = inLen p.1 then
        (fun raw => (F.linearHashKDF (fun _ => outLen p.1) bound (p.2, raw), ())) <$>
          (List.take (bound p.2.1) <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
              ((), request.2))
      else pure ([], ()))
    (prepare := fun p : ℕ × F.withSeed.Desc => (p.1, F.withSeed.encDesc p.2))
    (initial := fun _ => ())
    (resources := fun p _ => outLen p.1 + 1)
    hprep hhandler (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) hres
    (fun a request _ _ result hresult => by
      by_cases hq : request.2.length = inLen a.1
      · simp only [hq, ↓reduceIte] at hresult
        obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
        exact ⟨trivial, by simp, Nat.le_add_right _ _⟩
      · simp only [hq, ↓reduceIte] at hresult
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
        exact ⟨trivial, by simp, Nat.le_add_right _ _⟩)
  exact hsub.map (ComputableTidilyInPolyTime.fst encBool (encFinEnum Unit))

private theorem naorReingoldWordRun_hashedAdvGroup (F : PrimeOrderGroupFamily)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) (ds : F.withSeed.Desc)
    (hbound : ∀ x : F.Carrier ds.1, (F.encode ds.1 x).length ≤ bound ds.1)
    (fn : BitString (inLen n) → F.Carrier ds.1) :
    naorReingoldWordRun F.withSeed ds (hashedAdvGroup F inLen outLen bound adversary n ds) fn =
      OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = inLen n then
            F.linearHashKDF (fun _ => outLen n) bound
              (ds, F.encode ds.1 (fn (BitString.ofList (inLen n) request.2)))
          else []))
        (adversary n (F.withSeed.encDesc ds)) := by
  dsimp only [naorReingoldWordRun, hashedAdvGroup]
  rw [OracleComp.interpret_map, PMF.monad_map_eq_map]
  have hH :
      (ProbOracleComp.handler
        (fun r => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin r)))
        fun (request : Unit × List Bool) (_ : Unit) =>
          if request.2.length = inLen n then
            (fun raw => (F.linearHashKDF (fun _ => outLen n) bound (ds, raw), ())) <$>
              (List.take (bound ds.1) <$>
                ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                  ((), request.2))
          else pure ([], ())) =
      fun q => StateT.lift (m := ProbOracleComp (fun _ : Unit × List Bool => List Bool))
        (match q with
        | .inl r => ProbOracleComp.sample (ProbComp.unifFin r)
        | .inr request =>
            if request.2.length = inLen n then
              (fun raw => F.linearHashKDF (fun _ => outLen n) bound (ds, raw)) <$>
                (List.take (bound ds.1) <$>
                  ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                    ((), request.2))
            else pure []) := by
    funext q
    cases q with
    | inl r => rfl
    | inr request =>
      funext u
      by_cases hq : request.2.length = inLen n <;>
        simp [ProbOracleComp.handler, hq, StateT.lift, Functor.map_map]
  rw [hH, OracleComp.run_interpret_lift, OracleComp.interpret_map, PMF.monad_map_eq_map,
    PMF.map_comp, show Prod.fst ∘ (fun a : Bool => (a, ())) = id from rfl, PMF.map_id,
    OracleComp.interpret_interpret]
  congr 1; funext q
  cases q with
  | inl r =>
    simp [ProbOracleComp.handler, ProbOracleComp.sample, ProbComp.unifFin]
  | inr request =>
    dsimp only [ProbOracleComp.handler, Function.comp_apply]
    by_cases hq : request.2.length = inLen n
    · simp only [hq, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        PMF.monad_map_eq_map, PMF.pure_map, naorReingoldWordOracle,
        List.take_of_length_le (hbound _)]
    · simp [hq, PMF.monad_pure_eq_pure]

/-- **Asymptotic DDH security of the universal-hash Naor–Reingold bit-string PRF** (paraphrase of
[NaorReingold2004], Section 4.1, Construction 4.2, Theorem 4.3, and Remark 4.2): under
`F.DDH setup`, when group descriptions on `(setup n).support` have polynomially bounded bit-length,
`bound` bounds encoded group elements, and `2 ^ (outLen n) / qMin n` is negligible, no `IsOraclePPT`
adversary can distinguish `naorReingoldHashedRealGame` from `naorReingoldHashedIdealGame`. -/
theorem DDH.negligible_naorReingoldHashedGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen outLen : ℕ → ℕ} {bound : F.Desc → ℕ}
    {descBound qMin : ℕ → ℕ}
    (hDDH : F.DDH setup)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hdesc_poly : PolynomiallyBounded descBound)
    (hdesc : ∀ n, ∀ d ∈ (setup n).support, (F.encDesc d).length ≤ descBound n)
    (hbound : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq0 : ∀ n, 0 < qMin n)
    (hq : ∀ n, ∀ d ∈ (setup n).support, qMin n ≤ F.order d)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) := by
  have hDDH_seed : F.withSeed.DDH (F.seededSetup setup (F.linearHashSeedLen outLen bound)) :=
    hDDH.withSeed (F.computableInPolyTime_linearHashSeedLen houtLen hbound_poly)
  have hstep1_neg := hDDH_seed.negligible_naorReingoldDescGame hinLen
    (isOraclePPTOn_hashedAdvGroup F hinLen houtLen hbound_poly hadversary)
  have hstep1_eq (n : ℕ) :
      Game.advantage
        (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n)
        (naorReingoldHashedGroupIdealGame F setup inLen outLen bound adversary n) =
      Game.advantage
        (naorReingoldDescRealGame F.withSeed
          (F.seededSetup setup (F.linearHashSeedLen outLen bound)) inLen
          (hashedAdvGroup F inLen outLen bound adversary) n)
        (naorReingoldDescIdealGame F.withSeed
          (F.seededSetup setup (F.linearHashSeedLen outLen bound)) inLen
          (hashedAdvGroup F inLen outLen bound adversary) n) := by
    have hreal_eq :
        F.naorReingoldHashedRealGame setup inLen outLen bound adversary n =
        naorReingoldDescRealGame F.withSeed
          (F.seededSetup setup (F.linearHashSeedLen outLen bound)) inLen
          (hashedAdvGroup F inLen outLen bound adversary) n := by
      simp only [naorReingoldHashedRealGame, naorReingoldDescRealGame, PMF.monad_bind_eq_bind]
      refine bind_congr_on_support _ _ _ fun ds hds => ?_
      simp only [seededSetup, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hds
      obtain ⟨d, hd, _, _, rfl⟩ := hds
      congr 1; funext α₀; congr 1; funext α
      exact (naorReingoldWordRun_hashedAdvGroup F inLen outLen bound adversary n (d, _)
        (hbound n d hd) (F.naorReingoldEval d α₀ α)).symm
    have hideal_eq :
        naorReingoldHashedGroupIdealGame F setup inLen outLen bound adversary n =
        naorReingoldDescIdealGame F.withSeed
          (F.seededSetup setup (F.linearHashSeedLen outLen bound)) inLen
          (hashedAdvGroup F inLen outLen bound adversary) n := by
      simp only [naorReingoldHashedGroupIdealGame, naorReingoldDescIdealGame,
        PMF.monad_bind_eq_bind]
      refine bind_congr_on_support _ _ _ fun ds hds => ?_
      simp only [seededSetup, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hds
      obtain ⟨d, hd, _, _, rfl⟩ := hds
      congr 1; funext B
      exact (naorReingoldWordRun_hashedAdvGroup F inLen outLen bound adversary n (d, _)
        (hbound n d hd) (fun x => B x • F.generator d)).symm
    rw [hreal_eq, hideal_eq]
  obtain ⟨cA, eA, hQb⟩ := hadversary.query_bounds
  obtain ⟨cB, eB, hBb⟩ := hbound_poly.tidy.polyBounded_length.exists_le
  have hout_poly : PolynomiallyBounded outLen := houtLen.tidy.polynomiallyBounded
  let Q : ℕ → ℕ := fun n =>
    cA * (n + (2 * descBound n + 2 + outLen n * (2 * (cB * (descBound n + 1) ^ eB) + 1)) + 2) ^ eA
  have hQ_poly : PolynomiallyBounded Q := by
    dsimp only [Q]
    fun_prop
  have hQ_supp (n : ℕ) (d : F.Desc) (hd : d ∈ (setup n).support)
      (seed : BitString (outLen n * (2 * bound d + 1))) :
      (adversary n (F.withSeed.encDesc (d, List.ofFn seed))).IsQueryBounded (Q n) := by
    have hbd : bound d ≤ cB * (descBound n + 1) ^ eB := by
      have h1 := hBb d
      simp only [encUnary_apply, List.length_replicate] at h1
      exact h1.trans (Nat.mul_le_mul_left cB (Nat.pow_le_pow_left
        (Nat.add_le_add_right (hdesc n d hd) 1) eB))
    have hlen :
        (F.withSeed.encDesc (d, List.ofFn seed)).length ≤
          2 * descBound n + 2 + outLen n * (2 * (cB * (descBound n + 1) ^ eB) + 1) := by
      simp only [length_encPair, encBits_apply, List.length_ofFn]
      have hd_len := hdesc n d hd
      have hmul : outLen n * (2 * bound d + 1) ≤
          outLen n * (2 * (cB * (descBound n + 1) ^ eB) + 1) :=
        Nat.mul_le_mul_left (outLen n) (by lia)
      lia
    exact (hQb n (F.withSeed.encDesc (d, List.ofFn seed))).1.mono
      (Nat.mul_le_mul_left cA (Nat.pow_le_pow_left (by lia) eA))
  have hstep2_neg : Negligible fun n =>
      (Q n : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0)) / 2) := by
    have hsqrt : Negligible fun n =>
        NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0)) / 2 := by
      have h1 : Negligible fun n =>
          (2⁻¹ : ℝ≥0) * NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0)) :=
        (Negligible.sqrt hneg).const_mul (2⁻¹ : ℝ≥0)
      simpa only [div_eq_inv_mul] using h1
    exact hsqrt.polynomiallyBounded_mul hQ_poly
  refine negligible_of_le (hstep1_neg.add hstep2_neg) fun n => ?_
  calc Game.advantage
        (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n)
      ≤ Game.advantage
          (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n)
          (naorReingoldHashedGroupIdealGame F setup inLen outLen bound adversary n) +
        Game.advantage
          (naorReingoldHashedGroupIdealGame F setup inLen outLen bound adversary n)
          (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) :=
        Game.advantage_triangle _ _ _
    _ ≤ Game.advantage
          (naorReingoldDescRealGame F.withSeed
            (F.seededSetup setup (F.linearHashSeedLen outLen bound)) inLen
            (hashedAdvGroup F inLen outLen bound adversary) n)
          (naorReingoldDescIdealGame F.withSeed
            (F.seededSetup setup (F.linearHashSeedLen outLen bound)) inLen
            (hashedAdvGroup F inLen outLen bound adversary) n) +
        (Q n : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0)) / 2) := by
        rw [← hstep1_eq n]
        exact add_le_add le_rfl
          (F.advantage_naorReingoldHashedIdeal_le setup inLen outLen bound adversary n (Q n)
            (qMin n) (hq0 n) (hbound n) (hq n) (hQ_supp n))

/-- **Asymptotic DDH security of the executable universal-hash Naor–Reingold bit-string PRF
(`naorReingoldHashedProbRealGame`)** (paraphrase of [NaorReingold2004], Section 4.1,
Construction 4.2, Theorem 4.3, and Remark 4.2). -/
theorem DDH.negligible_naorReingoldHashedProbGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen outLen : ℕ → ℕ} {bound : F.Desc → ℕ}
    {descBound qMin : ℕ → ℕ}
    (hDDH : F.DDH setup)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hdesc_poly : PolynomiallyBounded descBound)
    (hdesc : ∀ n, ∀ d ∈ (setup n).support, (F.encDesc d).length ≤ descBound n)
    (hbound : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq0 : ∀ n, 0 < qMin n)
    (hq : ∀ n, ∀ d ∈ (setup n).support, qMin n ≤ F.order d)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedProbRealGame setup inLen outLen bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) := by
  have hinLen_poly : PolynomiallyBounded inLen := hinLen.tidy.polynomiallyBounded
  have hprob_neg : Negligible fun n => ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    have hp : PolynomiallyBounded (fun n => inLen n + 1) := by fun_prop
    have h1 := (negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)).polynomiallyBounded_mul
      hp
    refine negligible_of_le h1 fun n => ?_
    rw [div_eq_mul_inv, ← inv_pow]
  have hprob_le (n : ℕ) :
      Game.advantage
        (F.naorReingoldHashedProbRealGame setup inLen outLen bound adversary n)
        (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n) ≤
        ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    simp only [naorReingoldHashedProbRealGame, naorReingoldHashedRealGame, PMF.monad_bind_eq_bind]
    refine Game.advantage_bind_le_nnreal _ _ _ fun ds => ?_
    let m := inLen n
    let d := ds.1
    let detRun : (ZMod (F.order d) × (Fin m → ZMod (F.order d))) → PMF Bool := fun p =>
      OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = m then
            F.linearHashKDF (fun _ => outLen n) bound
              (ds, F.encode d (F.naorReingoldEval d p.1 p.2 (BitString.ofList m request.2)))
          else []))
        (adversary n (F.withSeed.encDesc ds))
    have hp_eq :
        ProbComp.eval (do
          let α₀ ← F.sampleNaorReingoldExp n d
          let αs ← OracleComp.replicate m (F.sampleNaorReingoldExp n d)
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifFin fun request =>
              pure (if request.2.length = m then
                F.naorReingoldHashedWordEval (outLen n) bound d ds.2 α₀ αs request.2
              else []))
            (adversary n (F.withSeed.encDesc ds))) =
        ((F.sampleModZModLaw (n + (F.encDesc d).length) d).bind fun α₀ =>
          (PMF.iid (F.sampleModZModLaw (n + (F.encDesc d).length) d) m).map (α₀, ·)).bind
          detRun := by
      simp only [ProbComp.eval_bind, ProbOracleComp.eval_interpret, ProbComp.eval_pure,
        eval_sampleNaorReingoldExp_eq_map_val F n d,
        eval_replicate_sampleNaorReingoldExp_eq_iid F n m d,
        PMF.bind_bind, PMF.bind_map, Function.comp_def]
      congr 1; funext α₀; congr 1; funext α
      dsimp only [detRun]
      congr 1; funext q
      cases q with
      | inl r => rfl
      | inr request =>
        dsimp only [ProbOracleComp.handler]
        by_cases hq : request.2.length = m
        · simp only [hq, ↓reduceIte, naorReingoldHashedWordEval]
          have hxs : List.ofFn (BitString.ofList m request.2) = request.2 :=
            BitString.ofFn_ofList hq
          have heval := F.naorReingoldWordEval_eq_encode d α₀.val (fun i => (α i).val)
            (BitString.ofList m request.2)
          simp only [ZMod.natCast_zmod_val, hxs] at heval
          rw [heval]
        · simp [hq]
    have hw_eq :
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₀ =>
          (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
            detRun (α₀, α)) =
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₀ =>
          (PMF.iid (PMF.uniformOfFintype (ZMod (F.order d))) m).map (α₀, ·)).bind detRun := by
      rw [iid_uniformOfFintype]
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    change Game.advantage _
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₀ =>
        (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
          detRun (α₀, α)) ≤ _
    rw [hp_eq, hw_eq, Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
    let μ := F.sampleModZModLaw (n + (F.encDesc d).length) d
    let ν := PMF.uniformOfFintype (ZMod (F.order d))
    have hswap (a : PMF (ZMod (F.order d))) (b : PMF (Fin m → ZMod (F.order d))) :
        (a.bind fun x => b.map (x, ·)) = (b.bind fun y => a.map (·, y)) := by
      simp only [PMF.map, Function.comp_def]
      exact PMF.bind_comm a b fun x y => PMF.pure (x, y)
    have hd_step : dist μ ν ≤ 1 / 2 ^ n := by
      rw [dist_comm]
      refine (F.dist_sampleModZModLaw_le (n + (F.encDesc d).length) d).trans ?_
      have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + (F.encDesc d).length) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n _)
      exact one_div_le_one_div_of_le (by positivity) hpow
    have hj1 :
        dist (μ.bind fun x => (PMF.iid μ m).map (x, ·))
          (ν.bind fun x => (PMF.iid μ m).map (x, ·)) ≤ dist μ ν :=
      dist_bind_le _ _ _
    have hj2 :
        dist (ν.bind fun x => (PMF.iid μ m).map (x, ·))
          (ν.bind fun x => (PMF.iid ν m).map (x, ·)) ≤ m * dist μ ν := by
      rw [hswap ν (PMF.iid μ m), hswap ν (PMF.iid ν m)]
      exact (dist_bind_le _ _ _).trans (PMF.dist_iid_le μ ν m)
    calc dist ((μ.bind fun x => (PMF.iid μ m).map (x, ·)).bind detRun)
          ((ν.bind fun x => (PMF.iid ν m).map (x, ·)).bind detRun)
        ≤ dist (μ.bind fun x => (PMF.iid μ m).map (x, ·))
            (ν.bind fun x => (PMF.iid ν m).map (x, ·)) := dist_bind_le _ _ _
      _ ≤ dist (μ.bind fun x => (PMF.iid μ m).map (x, ·))
            (ν.bind fun x => (PMF.iid μ m).map (x, ·)) +
          dist (ν.bind fun x => (PMF.iid μ m).map (x, ·))
            (ν.bind fun x => (PMF.iid ν m).map (x, ·)) := dist_triangle _ _ _
      _ ≤ dist μ ν + m * dist μ ν := add_le_add hj1 hj2
      _ = (m + 1 : ℝ) * dist μ ν := by ring
      _ ≤ (m + 1 : ℝ) * (1 / 2 ^ n) := mul_le_mul_of_nonneg_left hd_step (by positivity)
      _ = ((((m + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by push_cast; ring
  refine negligible_of_le
    (hprob_neg.add
      (hDDH.negligible_naorReingoldHashedGame hinLen houtLen hbound_poly hdesc_poly hdesc hbound
        hq0 hq hneg hadversary)) fun n => ?_
  exact (Game.advantage_triangle _
    (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n) _).trans
    (add_le_add (hprob_le n) le_rfl)

/-- **Constant-output-length hashed Naor–Reingold security under `F.DDH setup` alone**
(original, combining `DDH.negligible_expected_inv_order` with Theorem 4.3, Remark 4.2, and Lemma 4.2
of [NaorReingold2004]): for any constant output length `c : ℕ` (including `c = 1`), `F.DDH setup`
automatically supplies the inverse-order decay needed by the Leftover Hash Lemma, requiring no
external `qMin` hypothesis. -/
theorem DDH.negligible_naorReingoldHashedGame_const {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen : ℕ → ℕ} {bound : F.Desc → ℕ} {descBound : ℕ → ℕ}
    (c : ℕ) (hDDH : F.DDH setup)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hdesc_poly : PolynomiallyBounded descBound)
    (hdesc : ∀ n, ∀ d ∈ (setup n).support, (F.encDesc d).length ≤ descBound n)
    (hbound : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedRealGame setup inLen (fun _ => c) bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen (fun _ => c) bound adversary n) := by
  have houtLen : ComputableInPolyTime (fun _ : ℕ => c) encUnary encUnary := by fun_prop
  have hDDH_seed : F.withSeed.DDH
      (F.seededSetup setup (F.linearHashSeedLen (fun _ => c) bound)) :=
    hDDH.withSeed (F.computableInPolyTime_linearHashSeedLen houtLen hbound_poly)
  have hstep1_neg := hDDH_seed.negligible_naorReingoldDescGame hinLen
    (isOraclePPTOn_hashedAdvGroup F hinLen houtLen hbound_poly hadversary)
  have hstep1_eq (n : ℕ) :
      Game.advantage
        (F.naorReingoldHashedRealGame setup inLen (fun _ => c) bound adversary n)
        (naorReingoldHashedGroupIdealGame F setup inLen (fun _ => c) bound adversary n) =
      Game.advantage
        (naorReingoldDescRealGame F.withSeed
          (F.seededSetup setup (F.linearHashSeedLen (fun _ => c) bound)) inLen
          (hashedAdvGroup F inLen (fun _ => c) bound adversary) n)
        (naorReingoldDescIdealGame F.withSeed
          (F.seededSetup setup (F.linearHashSeedLen (fun _ => c) bound)) inLen
          (hashedAdvGroup F inLen (fun _ => c) bound adversary) n) := by
    have hreal_eq :
        F.naorReingoldHashedRealGame setup inLen (fun _ => c) bound adversary n =
        naorReingoldDescRealGame F.withSeed
          (F.seededSetup setup (F.linearHashSeedLen (fun _ => c) bound)) inLen
          (hashedAdvGroup F inLen (fun _ => c) bound adversary) n := by
      simp only [naorReingoldHashedRealGame, naorReingoldDescRealGame, PMF.monad_bind_eq_bind]
      refine bind_congr_on_support _ _ _ fun ds hds => ?_
      simp only [seededSetup, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hds
      obtain ⟨d, hd, _, _, rfl⟩ := hds
      congr 1; funext α₀; congr 1; funext α
      exact (naorReingoldWordRun_hashedAdvGroup F inLen (fun _ => c) bound adversary n (d, _)
        (hbound n d hd) (F.naorReingoldEval d α₀ α)).symm
    have hideal_eq :
        naorReingoldHashedGroupIdealGame F setup inLen (fun _ => c) bound adversary n =
        naorReingoldDescIdealGame F.withSeed
          (F.seededSetup setup (F.linearHashSeedLen (fun _ => c) bound)) inLen
          (hashedAdvGroup F inLen (fun _ => c) bound adversary) n := by
      simp only [naorReingoldHashedGroupIdealGame, naorReingoldDescIdealGame,
        PMF.monad_bind_eq_bind]
      refine bind_congr_on_support _ _ _ fun ds hds => ?_
      simp only [seededSetup, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hds
      obtain ⟨d, hd, _, _, rfl⟩ := hds
      congr 1; funext B
      exact (naorReingoldWordRun_hashedAdvGroup F inLen (fun _ => c) bound adversary n (d, _)
        (hbound n d hd) (fun x => B x • F.generator d)).symm
    rw [hreal_eq, hideal_eq]
  obtain ⟨cA, eA, hQb⟩ := hadversary.query_bounds
  obtain ⟨cB, eB, hBb⟩ := hbound_poly.tidy.polyBounded_length.exists_le
  let Q : ℕ → ℕ := fun n =>
    cA * (n + (2 * descBound n + 2 + c * (2 * (cB * (descBound n + 1) ^ eB) + 1)) + 2) ^ eA
  have hQ_poly : PolynomiallyBounded Q := by
    dsimp only [Q]
    fun_prop
  have hQ_supp (n : ℕ) (d : F.Desc) (hd : d ∈ (setup n).support)
      (seed : BitString (c * (2 * bound d + 1))) :
      (adversary n (F.withSeed.encDesc (d, List.ofFn seed))).IsQueryBounded (Q n) := by
    have hbd : bound d ≤ cB * (descBound n + 1) ^ eB := by
      have h1 := hBb d
      simp only [encUnary_apply, List.length_replicate] at h1
      exact h1.trans (Nat.mul_le_mul_left cB (Nat.pow_le_pow_left
        (Nat.add_le_add_right (hdesc n d hd) 1) eB))
    have hlen :
        (F.withSeed.encDesc (d, List.ofFn seed)).length ≤
          2 * descBound n + 2 + c * (2 * (cB * (descBound n + 1) ^ eB) + 1) := by
      simp only [length_encPair, encBits_apply, List.length_ofFn]
      have hd_len := hdesc n d hd
      have hmul : c * (2 * bound d + 1) ≤ c * (2 * (cB * (descBound n + 1) ^ eB) + 1) :=
        Nat.mul_le_mul_left c (by lia)
      lia
    exact (hQb n (F.withSeed.encDesc (d, List.ofFn seed))).1.mono
      (Nat.mul_le_mul_left cA (Nat.pow_le_pow_left (by lia) eA))
  let ε : ℕ → ℝ≥0 := fun n => (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal
  have hε_neg : Negligible ε := hDDH.negligible_expected_inv_order
  let lhlBound : ℕ → ℝ≥0 := fun n =>
    (Q n : ℝ≥0) * (2 : ℝ≥0) ^ c * NNReal.sqrt (NNReal.sqrt (ε n)) + NNReal.sqrt (ε n)
  have hlhl_neg : Negligible lhlBound := by
    have h1 : Negligible fun n => (2 : ℝ≥0) ^ c * NNReal.sqrt (NNReal.sqrt (ε n)) :=
      (hε_neg.sqrt.sqrt).const_mul ((2 : ℝ≥0) ^ c)
    have h2 : Negligible fun n =>
        (Q n : ℝ≥0) * ((2 : ℝ≥0) ^ c * NNReal.sqrt (NNReal.sqrt (ε n))) :=
      h1.polynomiallyBounded_mul hQ_poly
    have h2' : Negligible fun n =>
        (Q n : ℝ≥0) * (2 : ℝ≥0) ^ c * NNReal.sqrt (NNReal.sqrt (ε n)) := by
      simpa only [mul_assoc] using h2
    exact h2'.add hε_neg.sqrt
  have hstep2_le (n : ℕ) :
      Game.advantage
        (naorReingoldHashedGroupIdealGame F setup inLen (fun _ => c) bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen (fun _ => c) bound adversary n) ≤
        lhlBound n := by
    have hexp_top : (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
      calc (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹)
          ≤ ∑' d, setup n d * 1 := by
            refine ENNReal.tsum_le_tsum fun d => mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact ENNReal.inv_le_one.mpr (by exact_mod_cast (F.prime_order d).pos)
        _ = 1 := by simp [(setup n).tsum_coe]
    have hε_pos : 0 < ε n := by
      obtain ⟨d₀, hd₀⟩ := (setup n).support_nonempty
      have hd₀_ne : setup n d₀ ≠ 0 := (PMF.mem_support_iff _ _).mp hd₀
      have hord_ne : (F.order d₀ : ℝ≥0∞)⁻¹ ≠ 0 :=
        ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (F.order d₀))
      have hterm_pos : 0 < setup n d₀ * (F.order d₀ : ℝ≥0∞)⁻¹ :=
        ENNReal.mul_pos hd₀_ne hord_ne
      exact ENNReal.toNNReal_pos
        (ne_of_gt (lt_of_lt_of_le hterm_pos
          (ENNReal.le_tsum (f := fun d => setup n d * (F.order d : ℝ≥0∞)⁻¹) d₀)))
        hexp_top
    let τ : ℝ≥0 := NNReal.sqrt (ε n)
    have hτ_pos : 0 < τ := NNReal.sqrt_pos.mpr hε_pos
    simp only [naorReingoldHashedGroupIdealGame, naorReingoldHashedIdealGame, seededSetup,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
    let g1 : F.Desc → Game := fun d =>
      (Cslib.BitString.uniformList (F.linearHashSeedLen (fun _ => c) bound n d)).bind fun seed =>
        (PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order d))).bind fun B =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = inLen n then
                F.linearHashKDF (fun _ => c) bound
                  ((d, seed), F.encode d
                    (B (BitString.ofList (inLen n) request.2) • F.generator d))
              else []))
            (adversary n (F.withSeed.encDesc (d, seed)))
    let g2 : F.Desc → Game := fun d =>
      (Cslib.BitString.uniformList (F.linearHashSeedLen (fun _ => c) bound n d)).bind fun seed =>
        (PMF.uniformOfFintype (BitString (inLen n) → BitString c)).bind fun f =>
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = inLen n then
                List.ofFn (f (BitString.ofList (inLen n) request.2))
              else []))
            (adversary n (F.withSeed.encDesc (d, seed)))
    let errTerm : F.Desc → ℝ≥0∞ := fun d =>
      ((Q n : ℝ≥0) * (2 : ℝ≥0) ^ c * NNReal.sqrt τ : ℝ≥0) +
        (F.order d : ℝ≥0∞)⁻¹ * ((τ⁻¹ : ℝ≥0) : ℝ≥0∞)
    have hpoint (d : F.Desc) (hd : d ∈ (setup n).support) :
        ((Game.advantage (g1 d) (g2 d) : ℝ≥0) : ℝ≥0∞) ≤ errTerm d := by
      by_cases hsmall : (F.order d : ℝ≥0)⁻¹ ≤ τ
      · have hadv := advantage_naorReingoldHashedIdeal_at_le F inLen (fun _ => c) bound
          adversary n (Q n) d (hbound n d hd) (hQ_supp n d hd)
        have hle1 : Game.advantage (g1 d) (g2 d) ≤
            (Q n : ℝ≥0) * (2 : ℝ≥0) ^ c * NNReal.sqrt τ := by
          refine hadv.trans ?_
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hsq : NNReal.sqrt ((2 : ℝ≥0) ^ c / (F.order d : ℝ≥0)) / 2 ≤
              NNReal.sqrt ((2 : ℝ≥0) ^ c * τ) := by
            refine (div_le_self (by positivity) (by norm_num)).trans (NNReal.sqrt_le_sqrt.mpr ?_)
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left hsmall (by positivity)
          refine hsq.trans ?_
          rw [NNReal.sqrt_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc NNReal.sqrt ((2 : ℝ≥0) ^ c)
              ≤ NNReal.sqrt (((2 : ℝ≥0) ^ c) ^ 2) := by
                refine NNReal.sqrt_le_sqrt.mpr ?_
                rw [sq]
                exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
            _ = (2 : ℝ≥0) ^ c := NNReal.sqrt_sq _
        exact (ENNReal.coe_le_coe.mpr hle1).trans le_self_add
      · push Not at hsmall
        have hadv1 : Game.advantage (g1 d) (g2 d) ≤ 1 := by
          rw [Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist, NNReal.coe_one]
          exact dist_le_one _ _
        have h1_le : (1 : ℝ≥0) ≤ (F.order d : ℝ≥0)⁻¹ * τ⁻¹ :=
          (le_mul_inv_iff₀ hτ_pos).mpr (by simpa only [one_mul] using hsmall.le)
        have henn : ((Game.advantage (g1 d) (g2 d) : ℝ≥0) : ℝ≥0∞) ≤
            (F.order d : ℝ≥0∞)⁻¹ * ((τ⁻¹ : ℝ≥0) : ℝ≥0∞) := by
          calc ((Game.advantage (g1 d) (g2 d) : ℝ≥0) : ℝ≥0∞)
              ≤ ((1 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hadv1
            _ ≤ (((F.order d : ℝ≥0)⁻¹ * τ⁻¹ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h1_le
            _ = (F.order d : ℝ≥0∞)⁻¹ * ((τ⁻¹ : ℝ≥0) : ℝ≥0∞) := by
                rw [ENNReal.coe_mul, ENNReal.coe_inv (by exact_mod_cast (F.prime_order d).ne_zero),
                  ENNReal.coe_natCast]
        exact henn.trans le_add_self
    have hsum_err :
        (∑' d, setup n d * errTerm d) = ((lhlBound n : ℝ≥0) : ℝ≥0∞) := by
      dsimp only [errTerm, lhlBound]
      simp_rw [mul_add, ENNReal.tsum_add, ← mul_assoc]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, (setup n).tsum_coe, one_mul,
        ENNReal.coe_add]
      congr 1
      have hexp_eq : (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹) = ((ε n : ℝ≥0) : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal hexp_top).symm
      rw [hexp_eq, ← ENNReal.coe_mul]
      refine congrArg ENNReal.ofNNReal ?_
      have hsq : τ * τ = ε n := NNReal.mul_self_sqrt (ε n)
      calc ε n * τ⁻¹ = (τ * τ) * τ⁻¹ := by rw [hsq]
        _ = τ * (τ * τ⁻¹) := by ring
        _ = τ := by rw [mul_inv_cancel₀ hτ_pos.ne', mul_one]
    have hle_apply (f g : F.Desc → Game)
        (hfg : ∀ d ∈ (setup n).support,
          f d true ≤ g d true + ((Game.advantage (g1 d) (g2 d) : ℝ≥0) : ℝ≥0∞)) :
        ((setup n).bind f) true ≤ ((setup n).bind g) true + ((lhlBound n : ℝ≥0) : ℝ≥0∞) := by
      rw [← hsum_err, PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun d => ?_
      by_cases hd : d ∈ (setup n).support
      · rw [← mul_add]
        exact mul_le_mul_of_nonneg_left ((hfg d hd).trans (add_le_add le_rfl (hpoint d hd)))
          (by positivity)
      · have hz : setup n d = 0 := by simpa [PMF.mem_support_iff] using hd
        simp [hz]
    have hfg1 (d : F.Desc) (_ : d ∈ (setup n).support) :
        g1 d true ≤ g2 d true + ((Game.advantage (g1 d) (g2 d) : ℝ≥0) : ℝ≥0∞) := by
      have hadv : (g1 d true).toReal ≤ (g2 d true).toReal + (Game.advantage (g1 d) (g2 d) : ℝ) := by
        have h := le_abs_self ((g1 d true).toReal - (g2 d true).toReal)
        have hc : |(g1 d true).toReal - (g2 d true).toReal| =
            (Game.advantage (g1 d) (g2 d) : ℝ) := by
          simp only [Game.coe_advantage, Game.coe_succProbability]
        linarith
      rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top (g1 d) true),
        ← ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top (g2 d) true, by simp⟩),
        ENNReal.toReal_add (PMF.apply_ne_top (g2 d) true) (by simp), ENNReal.coe_toReal]
      exact ENNReal.ofReal_le_ofReal hadv
    have hfg2 (d : F.Desc) (_ : d ∈ (setup n).support) :
        g2 d true ≤ g1 d true + ((Game.advantage (g1 d) (g2 d) : ℝ≥0) : ℝ≥0∞) := by
      have hadv : (g2 d true).toReal ≤ (g1 d true).toReal + (Game.advantage (g1 d) (g2 d) : ℝ) := by
        have h := neg_le_abs ((g1 d true).toReal - (g2 d true).toReal)
        have hc : |(g1 d true).toReal - (g2 d true).toReal| =
            (Game.advantage (g1 d) (g2 d) : ℝ) := by
          simp only [Game.coe_advantage, Game.coe_succProbability]
        linarith
      rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top (g2 d) true),
        ← ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top (g1 d) true, by simp⟩),
        ENNReal.toReal_add (PMF.apply_ne_top (g1 d) true) (by simp), ENNReal.coe_toReal]
      exact ENNReal.ofReal_le_ofReal hadv
    have hadv_fin := Game.advantage_le_of_apply_le (by simp : ((lhlBound n : ℝ≥0) : ℝ≥0∞) ≠ ⊤)
      (hle_apply g1 g2 hfg1) (hle_apply g2 g1 hfg2)
    rw [ENNReal.coe_toReal] at hadv_fin
    exact NNReal.coe_le_coe.mp hadv_fin
  refine negligible_of_le (hstep1_neg.add hlhl_neg) fun n => ?_
  calc Game.advantage
        (F.naorReingoldHashedRealGame setup inLen (fun _ => c) bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen (fun _ => c) bound adversary n)
      ≤ Game.advantage
          (F.naorReingoldHashedRealGame setup inLen (fun _ => c) bound adversary n)
          (naorReingoldHashedGroupIdealGame F setup inLen (fun _ => c) bound adversary n) +
        Game.advantage
          (naorReingoldHashedGroupIdealGame F setup inLen (fun _ => c) bound adversary n)
          (F.naorReingoldHashedIdealGame setup inLen (fun _ => c) bound adversary n) :=
        Game.advantage_triangle _ _ _
    _ ≤ Game.advantage
          (naorReingoldDescRealGame F.withSeed
            (F.seededSetup setup (F.linearHashSeedLen (fun _ => c) bound)) inLen
            (hashedAdvGroup F inLen (fun _ => c) bound adversary) n)
          (naorReingoldDescIdealGame F.withSeed
            (F.seededSetup setup (F.linearHashSeedLen (fun _ => c) bound)) inLen
            (hashedAdvGroup F inLen (fun _ => c) bound adversary) n) +
        lhlBound n := by
        rw [← hstep1_eq n]
        exact add_le_add le_rfl (hstep2_le n)

end Cslib.Crypto.PrimeOrderGroupFamily

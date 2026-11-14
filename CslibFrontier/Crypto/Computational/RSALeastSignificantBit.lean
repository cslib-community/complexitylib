/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Data.Nat.Size

/-!
# The least significant bit of RSA

The RSA least-significant-bit experiment and the hard-core assumption it defines, together with
the exact inversion of RSA from a perfect least-significant-bit predictor.

For odd `N` and `k ≥ 1`, the parity of `2 ^ k * x % N` is the parity of `⌊2 ^ k * x / N⌋`
(`two_pow_mul_mod_mod_two`), and `2 ^ k * x % N` is the RSA preimage of `2 ^ (k * e) * y % N`
when `y = x ^ e % N`. So the parities answered on the `m` public queries `2 ^ (k * e) * y % N`,
`k = 1, …, m`, are the most-significant-first binary digits (`BitString.binaryValue`) of
`⌊2 ^ m * x / N⌋` (`binaryValue_testBit_two_pow_mul_mod`), which determines `x` once
`N ≤ 2 ^ m` (`lsbRecover`). The inverter `lsbInverter` runs a predictor on these queries and
recovers `x` exactly whenever the predictor is always correct on the modulus (`eval_lsbInverter`).

## Main definitions

* `Cslib.Crypto.RSAPredictor`, `Cslib.Crypto.RSAPredictor.IsPPT`, `Cslib.Crypto.rsaLSBGame`,
  `Cslib.Crypto.RSAHardCoreLSB`: the least-significant-bit prediction experiment and the
  assumption that every PPT predictor has negligible bias.
* `Cslib.Crypto.lsbQueries`, `Cslib.Crypto.lsbRecover`: the doubling queries, and the final
  rounding of the most-significant-first value of the answered parities.
* `Cslib.Crypto.lsbInverter`: the inverter that queries a predictor on the `N.size` doubling
  queries.

## Main results

* `Cslib.Crypto.rsaHardCoreLSB_iff_encoded`: `RSAHardCoreLSB` is the word-level assumption.
* `Cslib.Crypto.two_pow_mul_mod_mod_two`: parity of a doubled residue modulo an odd modulus.
* `Cslib.Crypto.lsbRecover_lsbQueries`: a correct parity oracle determines the RSA preimage.
* `Cslib.Crypto.eval_lsbInverter`, `Cslib.Crypto.succProbability_rsaInversionGame_lsbInverter`:
  a perfect predictor inverts RSA with certainty.
* `Cslib.Crypto.computableInPolyTime_lsbQueries`, `Cslib.Crypto.computableInPolyTime_lsbRecover`,
  `Cslib.Crypto.isPPT_lsbInverter`: uniform polynomial-time and strict-PPT efficiency
  certificates for the query generator, recovery arithmetic, and doubling inverter.
* `Cslib.Crypto.RSAOneWay.not_frequently_alwaysCorrect_lsbPredictor`: under `RSAOneWay` on
  eventually odd moduli, no strict-PPT predictor is always correct on infinitely many parameters.

## Implementation notes

`rsaLSBGame` runs `Cslib.Crypto.predictionExperiment` on `x` drawn uniformly from `Fin N`, as
`rsaInversionGame` does, rather than from `(ZMod N)ˣ`. An `RSAPredictor` receives the public key
and a challenge residue; `RSAPredictor.IsPPT` reads `encRSAInput`, like `RSAInverter.IsPPT`, and
writes a bit. Since the output is a bit, `rsaHardCoreLSB_iff_encoded` shows that `RSAHardCoreLSB` is
the assumption over word-level predictors reading the same layout on keys with `0 < N`
(`IsPPTOn.exists_bool_extension`).

[KatzLindell2020], Theorem 12.31, states that the least significant bit is hard-core
for RSA whenever RSA is hard. Its proof must handle predictors that are only noticeably better than
a fair guess; that reconstruction is not formalized here, so `RSAHardCoreLSB` is a separate
assumption, and `RSAOneWay.not_frequently_alwaysCorrect_lsbPredictor` establishes only the
noiseless consequence (`isPPT_lsbInverter` plus `succProbability_rsaInversionGame_lsbInverter`) for
predictors that are always correct on every residue modulo `N`.
`HardCore` in `CslibFrontier.Crypto.Computational.HardCore` covers unkeyed functions on uniform bit
strings, so it cannot express a predicate of a uniform residue under generated RSA keys;
`rsaLSBGame` is a separate keyed game that reuses `Game.guessingAdvantage`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 12.5.3, pp. 443–445 (Theorem 12.31 and the noiseless doubling inversion).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-! ### The prediction experiment -/

/-- A least-significant-bit predictor for RSA: given the security parameter, a public key
`(N, e)` and a residue modulo `N`, it outputs a bit. `RSAPredictor.IsPPT` states its efficiency
on encodings. -/
abbrev RSAPredictor : Type :=
  ℕ → (pk : RSAPublicKey) → Fin pk.N → ProbComp Bool

/-- An RSA predictor is PPT when one uniform strict PPT machine reads `encRSAInput` and writes the
predicted bit. -/
@[expose] def RSAPredictor.IsPPT (predictor : RSAPredictor) : Prop :=
  IsPPTOn encRSAInput encBool fun x => predictor x.secParam x.publicKey x.challenge

/-- The RSA least-significant-bit experiment: sample `desc ← gen n` and run
`Cslib.Crypto.predictionExperiment` on a uniform residue `x` modulo `N`. The predictor receives
`(pk, x ^ e % N)` and wins when it returns the least significant bit `x.testBit 0` of `x`. -/
@[expose] noncomputable def rsaLSBGame (gen : RSAGen) (predictor : RSAPredictor) (n : ℕ) :
    Game := do
  let desc ← gen n
  ProbComp.eval (predictionExperiment (ProbComp.uniform (Fin desc.modulus)) desc.publicKey.eval
    (fun x => (x : ℕ).testBit 0) (predictor n desc.publicKey))

/-- The least significant bit is hard-core for RSA relative to `gen`: every PPT predictor guesses
the least significant bit of a uniform residue from its RSA image with negligible bias from one
half. -/
@[expose] def RSAHardCoreLSB (gen : RSAGen) : Prop :=
  ∀ predictor : RSAPredictor, predictor.IsPPT →
    Negligible fun n => Game.guessingAdvantage (rsaLSBGame gen predictor n)

/-- `rsaLSBGame` written out: the predictor sees the RSA image of a uniform residue `x`. -/
theorem rsaLSBGame_eq (gen : RSAGen) (predictor : RSAPredictor) (n : ℕ) :
    rsaLSBGame gen predictor n = (do
      let desc ← gen n
      let x ← PMF.uniformOfFintype (Fin desc.modulus)
      let guess ← ProbComp.eval (predictor n desc.publicKey (desc.publicKey.eval x))
      return guess == (x : ℕ).testBit 0) := by
  simp only [rsaLSBGame, predictionExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  rfl

/-- **`RSAHardCoreLSB` is the word-level assumption.** Quantifying over predictors that read
`(1ⁿ, (N, e), y)` with binary numbers on keys with `0 < N`, each with one uniform strict PPT
machine, gives the same assumption as quantifying over typed predictors. A typed predictor's machine
reads exactly that layout; conversely, a typed predictor extends to all words by rerunning its
machine (`IsPPTOn.exists_bool_extension`), since its output is a single bit. -/
theorem rsaHardCoreLSB_iff_encoded (gen : RSAGen) :
    RSAHardCoreLSB gen ↔ ∀ W : ℕ → {pk : RSAPublicKey // 0 < pk.N} × ℕ → ProbComp Bool,
      IsPPTOn (encPair encUnary (encPair
          ((Function.Embedding.subtype fun pk : RSAPublicKey => 0 < pk.N).trans encRSAPublicKey)
          encNat)) encBool (fun x => W x.1 x.2) →
      Negligible fun n => Game.guessingAdvantage (do
        let desc ← gen n
        let x ← PMF.uniformOfFintype (Fin desc.modulus)
        let guess ← ProbComp.eval
          (W n (⟨desc.publicKey, desc.modulus_pos⟩, rsaEval desc.modulus desc.e x))
        return guess == (x : ℕ).testBit 0) := by
  constructor
  · intro h W hW
    have := h (fun n pk y => W n (⟨pk, y.pos⟩, y)) (hW.preprocess (prepare := fun x : RSAInput =>
      (x.secParam, (⟨x.publicKey, x.challenge.pos⟩ : {pk : RSAPublicKey // 0 < pk.N}),
        (x.challenge : ℕ))) (.of_eq (encIn := encRSAInput) fun _ => rfl))
    simpa only [rsaLSBGame_eq, RSAPublicKey.val_eval] using this
  · intro h P hP
    obtain ⟨E, hEppt, hE⟩ := hP.exists_bool_extension
    set E' := encPair encUnary (encPair
      ((Function.Embedding.subtype fun pk : RSAPublicKey => 0 < pk.N).trans encRSAPublicKey)
      encNat)
    have hold := h (fun n t => E (E' (n, t)))
      (hEppt.preprocess ComputableInPolyTime.id'.encoding_comp)
    have hrun (n : ℕ) (desc : RSADesc) (x : Fin desc.modulus) :
        ProbComp.eval
            (E (E' (n, ⟨desc.publicKey, desc.modulus_pos⟩, rsaEval desc.modulus desc.e x))) =
          ProbComp.eval (P n desc.publicKey (desc.publicKey.eval x)) :=
      hE ⟨n, desc.publicKey, desc.publicKey.eval x⟩
    simpa only [rsaLSBGame_eq, hrun] using hold

/-! ### Doubling and parity -/

/-- For odd `N` and `k ≠ 0`, the residue `2 ^ k * x % N` has the parity of the quotient
`⌊2 ^ k * x / N⌋`. -/
theorem two_pow_mul_mod_mod_two {N : ℕ} (hN : Odd N) {k : ℕ} (hk : k ≠ 0) (x : ℕ) :
    2 ^ k * x % N % 2 = 2 ^ k * x / N % 2 := by
  obtain ⟨t, rfl⟩ := hN
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hdiv := Nat.div_add_mod (2 ^ (j + 1) * x) (2 * t + 1)
  generalize 2 ^ (j + 1) * x / (2 * t + 1) = q at hdiv ⊢
  generalize 2 ^ (j + 1) * x % (2 * t + 1) = r at hdiv ⊢
  rw [show 2 ^ (j + 1) * x = 2 * (2 ^ j * x) by ring,
    show (2 * t + 1) * q = 2 * (t * q) + q by ring] at hdiv
  omega

/-- The doubling query `2 ^ (k * e) * y % N` is the RSA image of `2 ^ k * x % N` when
`y = x ^ e % N`. -/
theorem two_pow_mul_rsaEval (N e k x : ℕ) :
    2 ^ (k * e) * rsaEval N e x % N = rsaEval N e (2 ^ k * x % N) := by
  unfold rsaEval
  rw [← Nat.pow_mod, mul_pow, ← pow_mul, Nat.mul_mod_mod]

/-- The public doubling queries `2 ^ (k * e) * y % N` for `k = 1, …, m`. -/
@[expose] def lsbQueries (N e y m : ℕ) : List ℕ :=
  (List.range m).map fun k => 2 ^ ((k + 1) * e) * y % N

/-- Recover `x` from the most-significant-first digits `bits` of `q = ⌊2 ^ m * x / N⌋` as
`⌈q * N / 2 ^ m⌉`. -/
@[expose] def lsbRecover (N m : ℕ) (bits : List Bool) : ℕ :=
  (BitString.binaryValue bits * N + 2 ^ m - 1) / 2 ^ m

private theorem toNat_decide_mod_two (v : ℕ) : (decide (v % 2 = 1)).toNat = v % 2 := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

/-- The parities of the doubled residues are the binary digits of `⌊2 ^ m * x / N⌋`. -/
theorem binaryValue_testBit_two_pow_mul_mod {N x : ℕ} (hN : Odd N) (hx : x < N) (m : ℕ) :
    BitString.binaryValue ((List.range m).map fun k => (2 ^ (k + 1) * x % N).testBit 0) =
      2 ^ m * x / N := by
  induction m with
  | zero => simp [BitString.binaryValue, Nat.div_eq_of_lt hx]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, BitString.binaryValue_snoc, ih]
    simp only [Nat.testBit_zero, toNat_decide_mod_two,
      two_pow_mul_mod_mod_two hN (k := m + 1) (by omega)]
    have hhalf : 2 ^ (m + 1) * x / N / 2 = 2 ^ m * x / N := by
      rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm (2 ^ m) 2, mul_assoc, mul_comm N 2,
        Nat.mul_div_mul_left _ _ two_pos]
    have := Nat.div_add_mod (2 ^ (m + 1) * x / N) 2
    omega

/-- Rounding `⌊2 ^ m * x / N⌋ * N / 2 ^ m` up recovers `x` once `N ≤ 2 ^ m`. -/
theorem lsbRecover_eq {N x m : ℕ} (hx : x < N) (hm : N ≤ 2 ^ m) (bits : List Bool)
    (hbits : BitString.binaryValue bits = 2 ^ m * x / N) : lsbRecover N m bits = x := by
  have hN : 0 < N := by omega
  have hP : 0 < 2 ^ m := Nat.two_pow_pos m
  unfold lsbRecover
  rw [hbits]
  have hlo := Nat.div_mul_le_self (2 ^ m * x) N
  have hhi := Nat.lt_div_mul_add (a := 2 ^ m * x) hN
  apply Nat.div_eq_of_lt_le
  · rw [mul_comm x]
    omega
  · rw [add_mul, one_mul, mul_comm x]
    omega

/-- A parity oracle that is correct on all RSA images modulo an odd `N` determines the preimage
from the `m` doubling queries, once `N ≤ 2 ^ m`. -/
theorem lsbRecover_lsbQueries {N e x m : ℕ} (hN : Odd N) (hx : x < N) (hm : N ≤ 2 ^ m)
    (oracle : ℕ → Bool) (horacle : ∀ z < N, oracle (rsaEval N e z) = z.testBit 0) :
    lsbRecover N m ((lsbQueries N e (rsaEval N e x) m).map oracle) = x := by
  apply lsbRecover_eq hx hm
  rw [← binaryValue_testBit_two_pow_mul_mod hN hx m, lsbQueries, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  rw [two_pow_mul_rsaEval, horacle _ (Nat.mod_lt _ (by omega))]

/-! ### The inverter -/

/-- The inverter built from a least-significant-bit predictor `P`: on `(pk, y)` with
`pk = (N, e)`, run `P` on the `N.size` doubling queries and round the value of the answers. -/
@[expose] noncomputable def lsbInverter (P : RSAPredictor) : RSAInverter := fun n pk y => do
  let bits ← (lsbQueries pk.N pk.e y pk.N.size).mapM
    fun query => P n pk ⟨query % pk.N, Nat.mod_lt _ y.pos⟩
  return ⟨lsbRecover pk.N pk.N.size bits % pk.N, Nat.mod_lt _ y.pos⟩

private theorem eval_mapM_of_pure {α β : Type} (f : α → ProbComp β) (g : α → β) :
    ∀ list : List α, (∀ a ∈ list, ProbComp.eval (f a) = PMF.pure (g a)) →
      ProbComp.eval (list.mapM f) = PMF.pure (list.map g)
  | [], _ => by simp
  | a :: list, h => by
    rw [List.mapM_cons]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, h a List.mem_cons_self, PMF.pure_bind,
      eval_mapM_of_pure f g list fun b hb => h b (List.mem_cons_of_mem a hb), List.map_cons]

/-- If `P` predicts the least significant bit correctly with certainty on every RSA image modulo
an odd `N`, then `lsbInverter P` returns the preimage of every `y = x ^ e % N` with certainty. -/
theorem eval_lsbInverter {P : RSAPredictor} {n : ℕ} {pk : RSAPublicKey} (hN : Odd pk.N)
    (hP : ∀ z : Fin pk.N, ProbComp.eval (P n pk (pk.eval z)) = PMF.pure ((z : ℕ).testBit 0))
    (x : Fin pk.N) : ProbComp.eval (lsbInverter P n pk (pk.eval x)) = PMF.pure x := by
  classical
  have hpos : 0 < pk.N := x.pos
  let oracle : ℕ → Bool := fun query =>
    if h : ∃ z : Fin pk.N, rsaEval pk.N pk.e z = query then (Classical.choose h).val.testBit 0
    else false
  have hcorrect : ∀ z < pk.N, oracle (rsaEval pk.N pk.e z) = z.testBit 0 := by
    intro z hz
    have hex : ∃ z' : Fin pk.N, rsaEval pk.N pk.e z' = rsaEval pk.N pk.e z := ⟨⟨z, hz⟩, rfl⟩
    have heq : pk.eval (Classical.choose hex) = pk.eval ⟨z, hz⟩ :=
      Fin.ext (Classical.choose_spec hex)
    have h1 := congrArg PMF.support (hP (Classical.choose hex))
    rw [heq, hP ⟨z, hz⟩, PMF.support_pure, PMF.support_pure,
      Set.singleton_eq_singleton_iff] at h1
    simp only [oracle, dite_eq_left_of_eq_true (eq_true hex)]
    exact h1.symm
  have hqueries : ∀ query ∈ lsbQueries pk.N pk.e (pk.eval x) pk.N.size,
      ProbComp.eval (P n pk ⟨query % pk.N, Nat.mod_lt _ (pk.eval x).pos⟩) =
        PMF.pure (oracle query) := by
    intro query hq
    simp only [lsbQueries, List.mem_map, List.mem_range] at hq
    obtain ⟨k, -, rfl⟩ := hq
    have hpoint : (⟨2 ^ ((k + 1) * pk.e) * (pk.eval x : ℕ) % pk.N % pk.N,
        Nat.mod_lt _ (pk.eval x).pos⟩ : Fin pk.N) =
        pk.eval ⟨2 ^ (k + 1) * x % pk.N, Nat.mod_lt _ hpos⟩ := by
      ext
      simp only [RSAPublicKey.val_eval, two_pow_mul_rsaEval]
      exact Nat.mod_mod _ _
    rw [hpoint, hP, RSAPublicKey.val_eval, two_pow_mul_rsaEval,
      hcorrect _ (Nat.mod_lt _ hpos)]
  simp only [lsbInverter, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_mapM_of_pure _ oracle _ hqueries, PMF.pure_bind]
  congr 1
  ext
  simp only [RSAPublicKey.val_eval]
  rw [lsbRecover_lsbQueries hN x.isLt (Nat.lt_size_self pk.N).le oracle hcorrect,
    Nat.mod_eq_of_lt x.isLt]

/-- A predictor that is always correct on the odd moduli produced by `gen n` yields an inverter
that wins the RSA inversion experiment with probability one. -/
theorem succProbability_rsaInversionGame_lsbInverter {gen : RSAGen} {P : RSAPredictor} {n : ℕ}
    (hodd : ∀ desc ∈ (gen n).support, Odd desc.modulus)
    (hP : ∀ desc ∈ (gen n).support, ∀ z : Fin desc.modulus,
      ProbComp.eval (P n desc.publicKey (desc.publicKey.eval z)) = PMF.pure ((z : ℕ).testBit 0)) :
    Game.succProbability (rsaInversionGame gen (lsbInverter P) n) = 1 := by
  have hgame : rsaInversionGame gen (lsbInverter P) n = PMF.pure true := by
    rw [rsaInversionGame_eq, ← PMF.bind_const (gen n) (PMF.pure true)]
    refine PMF.bind_congr_on_support _ _ _ fun desc hdesc => ?_
    rw [← PMF.bind_const (PMF.uniformOfFintype (Fin desc.modulus)) (PMF.pure true)]
    refine PMF.bind_congr_on_support _ _ _ fun x _ => ?_
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    rw [eval_lsbInverter (pk := desc.publicKey) (hodd desc hdesc) (hP desc hdesc) x,
      PMF.pure_bind, decide_eq_true rfl]
  rw [hgame]
  simp [Game.succProbability]

/-! ### Efficiency certificates and noiseless impossibility -/

/-- Generating the `m` doubling queries `2 ^ ((k + 1) * e) * y % N` is computable in polynomial
time when `N`, `e`, and `y` are binary, `m` is unary, and `0 < N`. -/
theorem computableInPolyTime_lsbQueries {α : Type} {enc : α ↪ List Bool} {N e y m : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (he : ComputableInPolyTime e enc encNat)
    (hy : ComputableInPolyTime y enc encNat) (hm : ComputableInPolyTime m enc encUnary)
    (hpos : ∀ a, 0 < N a) :
    ComputableInPolyTime (fun a => lsbQueries (N a) (e a) (y a) (m a)) enc (encList encNat) := by
  have hrange : ComputableInPolyTime (fun a => List.range (m a)) enc (encList encUnary) :=
    ComputableInPolyTime.range.comp hm
  have hpow : ComputableInPolyTime
      (fun p : α × ℕ => 2 ^ ((p.2 + 1) * e p.1) % N p.1)
      (encPair enc encUnary) encNat := by
    have hk : ComputableInPolyTime (fun p : α × ℕ => p.2) (encPair enc encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary)
    have hexp : ComputableInPolyTime (fun p : α × ℕ => (p.2 + 1) * e p.1)
        (encPair enc encUnary) encNat :=
      ComputableInPolyTime.binary_mul'
        (ComputableInPolyTime.binary_add' hk (ComputableInPolyTime.const 1))
        (he.comp (ComputableInPolyTime.fst enc encUnary))
    exact ComputableInPolyTime.binary_powMod (ComputableInPolyTime.const 2) hexp
      (hN.comp (ComputableInPolyTime.fst enc encUnary)) (fun p => hpos p.1)
  have hstep : ComputableInPolyTime
      (fun p : α × ℕ => 2 ^ ((p.2 + 1) * e p.1) * y p.1 % N p.1)
      (encPair enc encUnary) encNat := by
    have hmul : ComputableInPolyTime
        (fun p : α × ℕ => (2 ^ ((p.2 + 1) * e p.1) % N p.1) * y p.1 % N p.1)
        (encPair enc encUnary) encNat :=
      ComputableInPolyTime.binary_mod'
        (ComputableInPolyTime.binary_mul' hpow
          (hy.comp (ComputableInPolyTime.fst enc encUnary)))
        (hN.comp (ComputableInPolyTime.fst enc encUnary))
    simpa only [Nat.mod_mul_mod] using hmul
  exact ComputableInPolyTime.mapWithInput hrange hstep

/-- Computing `lsbRecover N m bits = (BitString.binaryValue bits * N + 2 ^ m - 1) / 2 ^ m` is
computable in polynomial time when `N` is binary and `m` is unary. -/
theorem computableInPolyTime_lsbRecover {α : Type} {enc : α ↪ List Bool}
    {N m : α → ℕ} {bits : α → List Bool}
    (hN : ComputableInPolyTime N enc encNat) (hm : ComputableInPolyTime m enc encUnary)
    (hbits : ComputableInPolyTime bits enc (encList encBool)) :
    ComputableInPolyTime (fun a => lsbRecover (N a) (m a) (bits a)) enc encNat := by
  have hval : ComputableInPolyTime (fun a => BitString.binaryValue (bits a)) enc encNat :=
    ComputableInPolyTime.bitsBinaryValue.comp (ComputableInPolyTime.listToBits.comp hbits)
  have hpow : ComputableInPolyTime (fun a => 2 ^ m a) enc encNat :=
    ComputableInPolyTime.binary_two_pow.comp hm
  have hnum : ComputableInPolyTime (fun a => BitString.binaryValue (bits a) * N a + 2 ^ m a - 1)
      enc encNat :=
    ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' hval hN) hpow)
      (ComputableInPolyTime.const 1)
  exact ComputableInPolyTime.binary_div' hnum hpow

/-- `lsbInverter P` runs in uniform strict polynomial time whenever the predictor `P` is PPT. -/
theorem isPPT_lsbInverter {P : RSAPredictor} (hP : P.IsPPT) : (lsbInverter P).IsPPT := by
  have hqueries : ComputableInPolyTime
      (fun x : RSAInput => lsbQueries x.publicKey.N x.publicKey.e x.challenge x.publicKey.N.size)
      encRSAInput (encList encNat) :=
    computableInPolyTime_lsbQueries (by fun_prop) (by fun_prop)
      (RSAInput.computableInPolyTime_challenge_val (by fun_prop))
      (ComputableInPolyTime.binary_size.comp (by fun_prop))
      (fun x => x.challenge.pos)
  have hprepare : ComputableInPolyTime
      (fun p : RSAInput × ℕ =>
        ({ secParam := p.1.secParam, publicKey := p.1.publicKey,
           challenge := ⟨p.2 % p.1.publicKey.N, Nat.mod_lt _ p.1.challenge.pos⟩ } : RSAInput))
      (encPair encRSAInput encNat) encRSAInput := by
    have hraw : ComputableInPolyTime
        (fun p : RSAInput × ℕ =>
          (p.1.secParam, p.1.publicKey, p.2 % p.1.publicKey.N))
        (encPair encRSAInput encNat) (encPair encUnary (encPair encRSAPublicKey encNat)) :=
      (ComputableInPolyTime.prod (by fun_prop)
        (ComputableInPolyTime.prod (by fun_prop)
          (ComputableInPolyTime.binary_mod' (by fun_prop) (by fun_prop))))
    exact hraw.of_enc_eq fun _ => rfl
  have hqueryPPT : IsPPTOn (encPair encRSAInput encNat) encBool
      (fun p : RSAInput × ℕ =>
        P p.1.secParam p.1.publicKey ⟨p.2 % p.1.publicKey.N, Nat.mod_lt _ p.1.challenge.pos⟩) :=
    hP.preprocess hprepare
  have hmapM : IsPPTOn encRSAInput (encList encBool)
      (fun x : RSAInput =>
        (lsbQueries x.publicKey.N x.publicKey.e x.challenge x.publicKey.N.size).mapM
          fun query => P x.secParam x.publicKey
            ⟨query % x.publicKey.N, Nat.mod_lt _ x.challenge.pos⟩) :=
    IsPPTOn.mapMWith hqueryPPT hqueries
  have hpost : ComputableInPolyTime
      (fun p : RSAInput × List Bool =>
        lsbRecover p.1.publicKey.N p.1.publicKey.N.size p.2 % p.1.publicKey.N)
      (encPair encRSAInput (encList encBool)) encNat :=
    ComputableInPolyTime.binary_mod'
      (computableInPolyTime_lsbRecover (by fun_prop)
        (ComputableInPolyTime.binary_size.comp (by fun_prop)) (by fun_prop))
      (by fun_prop)
  refine (hmapM.map_with (f := fun x bits =>
      lsbRecover x.publicKey.N x.publicKey.N.size bits % x.publicKey.N)
    hpost).congr fun x => ?_
  simp only [lsbInverter, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.map_bind, PMF.pure_map]
  rfl

/-- Under `RSAOneWay gen` and eventually odd moduli, no uniform strict-PPT predictor can predict
`x.testBit 0` with certainty on every residue modulo `N` for infinitely many security parameters
(the noiseless corollary of `isPPT_lsbInverter` and
`succProbability_rsaInversionGame_lsbInverter`). -/
theorem RSAOneWay.not_frequently_alwaysCorrect_lsbPredictor {gen : RSAGen}
    (hRSA : RSAOneWay gen)
    (hodd : ∀ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support, Odd desc.modulus)
    {P : RSAPredictor} (hP : P.IsPPT) :
    ¬ ∃ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support, ∀ z : Fin desc.modulus,
      ProbComp.eval (P n desc.publicKey (desc.publicKey.eval z)) =
        PMF.pure ((z : ℕ).testBit 0) := by
  intro hfreq
  have hneg := hRSA (lsbInverter P) (isPPT_lsbInverter hP)
  obtain ⟨m, hm⟩ := (negligible_iff _).mp hneg 0 1 zero_lt_one
  obtain ⟨n, hnm, hodd_n, hcorr_n⟩ :=
    Filter.frequently_atTop.mp (hodd.and_frequently hfreq) m
  have h1 := succProbability_rsaInversionGame_lsbInverter hodd_n hcorr_n
  have hlt := hm n hnm
  simp only [pow_zero, one_mul, h1] at hlt
  exact lt_irrefl _ hlt

end Cslib.Crypto

/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import CslibFrontier.Foundations.Data.BitString.List.Binary
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

* `Cslib.Crypto.rsaLSBGame`, `Cslib.Crypto.RSAHardCoreLSB`: the least-significant-bit prediction
  experiment and the assumption that every uniform PPT predictor has negligible bias.
* `Cslib.Crypto.lsbQueries`, `Cslib.Crypto.lsbRecover`: the doubling queries, and the final
  rounding of the most-significant-first value of the answered parities.
* `Cslib.Crypto.lsbInverter`: the inverter that queries a predictor on the `N.size` doubling
  queries.

## Main results

* `Cslib.Crypto.two_pow_mul_mod_mod_two`: parity of a doubled residue modulo an odd modulus.
* `Cslib.Crypto.lsbRecover_lsbQueries`: a correct parity oracle determines the RSA preimage.
* `Cslib.Crypto.eval_lsbInverter`, `Cslib.Crypto.succProbability_rsaInversionGame_lsbInverter`:
  a perfect predictor inverts RSA with certainty.

## Implementation notes

As in `rsaInversionGame`, `rsaLSBGame` samples `x` uniformly from `Fin N` rather than from
`(ZMod N)ˣ`. [KatzLindell2020], Theorem 12.31, states that the least significant bit is hard-core
for RSA whenever RSA is hard. Its proof must handle predictors that are only noticeably better than
a fair guess; that reconstruction is not formalized here, so `RSAHardCoreLSB` is a separate
assumption, and the inversion from a perfect predictor (by repeated doubling) is only the
noiseless special case. A strict PPT certificate for `lsbInverter` is also not proved here.
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

/-- The RSA least-significant-bit experiment: sample `desc ← gen n` and a uniform `x ← Fin N`,
pass `(pk, x ^ e % N)` to the predictor and test whether it returns the least significant bit
`x.testBit 0` of `x`. -/
@[expose] noncomputable def rsaLSBGame (gen : RSAGen) (A : ℕ → RSAPublicKey × ℕ → ProbComp Bool)
    (n : ℕ) : Game := do
  let desc ← gen n
  have : NeZero desc.modulus := ⟨Nat.ne_of_gt desc.modulus_pos⟩
  let x ← PMF.uniformOfFintype (Fin desc.modulus)
  let guess ← ProbComp.eval (A n (desc.publicKey, rsaEval desc.modulus desc.e x.1))
  return guess == x.1.testBit 0

/-- The least significant bit is hard-core for RSA relative to `gen`: every uniform strict PPT
predictor receiving `(1^n, ((N, e), y))` guesses the least significant bit of the preimage with
negligible bias from one half. -/
@[expose] def RSAHardCoreLSB (gen : RSAGen) : Prop :=
  ∀ A : ℕ → RSAPublicKey × ℕ → ProbComp Bool,
    IsPPTOn (encPair encUnary (encPair encRSAPublicKey encNat)) encBool
      (fun input => A input.1 input.2) →
    Negligible (fun n => Game.guessingAdvantage (rsaLSBGame gen A n))

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

/-- The inverter built from a least-significant-bit predictor `A`: on `(pk, y)` with `pk = (N, e)`,
run `A` on the `N.size` doubling queries and round the value of the answers. -/
@[expose] noncomputable def lsbInverter (A : ℕ → RSAPublicKey × ℕ → ProbComp Bool) (n : ℕ)
    (input : RSAPublicKey × ℕ) : ProbComp ℕ := do
  let bits ← (lsbQueries input.1.N input.1.e input.2 input.1.N.size).mapM
    fun query => A n (input.1, query)
  return lsbRecover input.1.N input.1.N.size bits

private theorem eval_mapM_of_pure {α β : Type} (f : α → ProbComp β) (g : α → β) :
    ∀ list : List α, (∀ a ∈ list, ProbComp.eval (f a) = PMF.pure (g a)) →
      ProbComp.eval (list.mapM f) = PMF.pure (list.map g)
  | [], _ => by simp
  | a :: list, h => by
    rw [List.mapM_cons]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, h a List.mem_cons_self, PMF.pure_bind,
      eval_mapM_of_pure f g list fun b hb => h b (List.mem_cons_of_mem a hb), List.map_cons]

/-- If `A` predicts the least significant bit correctly with certainty on every RSA image modulo
an odd `N`, then `lsbInverter A` returns the preimage of every `y = x ^ e % N` with certainty. -/
theorem eval_lsbInverter {A : ℕ → RSAPublicKey × ℕ → ProbComp Bool} {n : ℕ}
    {pk : RSAPublicKey} (hN : Odd pk.N)
    (hA : ∀ z < pk.N, ProbComp.eval (A n (pk, rsaEval pk.N pk.e z)) = PMF.pure (z.testBit 0))
    {x : ℕ} (hx : x < pk.N) :
    ProbComp.eval (lsbInverter A n (pk, rsaEval pk.N pk.e x)) = PMF.pure x := by
  classical
  let oracle : ℕ → Bool := fun query =>
    if h : ∃ z < pk.N, rsaEval pk.N pk.e z = query then (Classical.choose h).testBit 0 else false
  have hcorrect : ∀ z < pk.N, oracle (rsaEval pk.N pk.e z) = z.testBit 0 := by
    intro z hz
    have hex : ∃ z' < pk.N, rsaEval pk.N pk.e z' = rsaEval pk.N pk.e z := ⟨z, hz, rfl⟩
    obtain ⟨hlt, heq⟩ := Classical.choose_spec hex
    have h1 := congrArg PMF.support (hA _ hlt)
    rw [heq, hA z hz, PMF.support_pure, PMF.support_pure,
      Set.singleton_eq_singleton_iff] at h1
    simp only [oracle, dite_eq_left_of_eq_true (eq_true hex)]
    exact h1.symm
  have hqueries : ∀ query ∈ lsbQueries pk.N pk.e (rsaEval pk.N pk.e x) pk.N.size,
      ProbComp.eval (A n (pk, query)) = PMF.pure (oracle query) := by
    intro query hq
    simp only [lsbQueries, List.mem_map, List.mem_range] at hq
    obtain ⟨k, -, rfl⟩ := hq
    rw [two_pow_mul_rsaEval, hA _ (Nat.mod_lt _ (by grind)),
      hcorrect _ (Nat.mod_lt _ (by grind))]
  simp only [lsbInverter, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_mapM_of_pure _ oracle _ hqueries, PMF.pure_bind]
  exact congrArg PMF.pure (lsbRecover_lsbQueries hN hx (Nat.lt_size_self pk.N).le oracle hcorrect)

/-- A predictor that is always correct on the odd moduli produced by `gen n` yields an inverter
that wins the RSA inversion experiment with probability one. -/
theorem succProbability_rsaInversionGame_lsbInverter {gen : RSAGen}
    {A : ℕ → RSAPublicKey × ℕ → ProbComp Bool} {n : ℕ}
    (hodd : ∀ desc ∈ (gen n).support, Odd desc.modulus)
    (hA : ∀ desc ∈ (gen n).support, ∀ z < desc.modulus,
      ProbComp.eval (A n (desc.publicKey, rsaEval desc.modulus desc.e z)) =
        PMF.pure (z.testBit 0)) :
    Game.succProbability (rsaInversionGame gen (lsbInverter A) n) = 1 := by
  have hgame : rsaInversionGame gen (lsbInverter A) n = PMF.pure true := by
    unfold rsaInversionGame
    rw [← PMF.bind_const (gen n) (PMF.pure true)]
    apply PMF.bind_congr_on_support
    intro desc hdesc
    have : NeZero desc.modulus := ⟨Nat.ne_of_gt desc.modulus_pos⟩
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    rw [← PMF.bind_const (PMF.uniformOfFintype (Fin desc.modulus)) (PMF.pure true)]
    refine PMF.bind_congr_on_support _ _ _ fun x _ => ?_
    change (ProbComp.eval (lsbInverter A n
      (desc.publicKey, rsaEval desc.publicKey.N desc.publicKey.e x))).bind _ = _
    rw [eval_lsbInverter (pk := desc.publicKey) (hodd desc hdesc) (hA desc hdesc) x.2,
      PMF.pure_bind, decide_eq_true rfl]
  rw [hgame]
  simp [Game.succProbability]

end Cslib.Crypto

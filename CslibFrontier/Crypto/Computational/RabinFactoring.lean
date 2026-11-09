/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Computational.QuadraticResiduosity
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.BitString
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Tactic.PPT
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Equivalence of Rabin inversion and integer factoring for Blum moduli

The Rabin squaring function `x ↦ x ^ 2 % N` over Blum moduli `N = p * q` (`p ≠ q` primes with
`p ≡ q ≡ 3 [MOD 4]`), the integer factoring assumption `FactoringHard`, the Rabin one-wayness
assumption `RabinOneWay`, and the polynomial-time equivalence `RabinOneWay gen ↔ FactoringHard gen`.

## Main definitions

* `Cslib.Crypto.BlumDesc`, `Cslib.Crypto.BlumGen`: Blum modulus parameters and generators.
* `Cslib.Crypto.rabinEval`: Rabin squaring `x ^ 2 % N`.
* `Cslib.Crypto.factoringGame`, `Cslib.Crypto.FactoringHard`: the integer factoring experiment
  and assumption.
* `Cslib.Crypto.rabinInversionGame`, `Cslib.Crypto.RabinOneWay`: the Rabin modular square-root
  experiment and assumption.
* `Cslib.Crypto.rabinToFactor`, `Cslib.Crypto.factorToRabin`: explicit PPT reductions between
  Rabin inversion and factoring.

## Main results

* `Cslib.Crypto.rabinOneWay_of_factoringHard`: if factoring is hard for `gen`, then Rabin
  squaring is one-way for `gen`.
* `Cslib.Crypto.factoringHard_of_rabinOneWay`: if Rabin squaring is one-way for `gen`, then
  factoring is hard for `gen`.
* `Cslib.Crypto.rabinOneWay_iff_factoringHard`: `RabinOneWay gen ↔ FactoringHard gen`.

## Implementation notes

To execute natively inside `ProbComp` without an exact uniform sampler over `(ZMod N)ˣ` or
modular rejection-sampling error, `rabinInversionGame` and `rabinToFactor` use an original
dyadic all-residue sampling variant: they draw a uniform `2 * N.bits.length`-bit word `r`
(`x = ofBits r < 2^(2 * bits(N))` with `N^2 ≤ 2^(2 * bits(N))`) and evaluate
`rabinEval N x = x^2 % N`. In `rabinToFactor`, if `1 < gcd(x, N) < N` the reduction factors
`N` immediately; otherwise it queries the Rabin inverter `A` on `(N, x^2 % N)` and returns
`(gcd(x + x', N), N / gcd(x + x', N))`. Partitioning `Fin (2^L)` into nontrivial-gcd draws,
multiples of `N`, and 4-to-1 unit fibers (where at least `2k` of the at most `4(k + 1)`
preimages in `Fin (2^L)` fall in the two mixed-sign CRT classes, equal to `x'` modulo one prime
and `-x'` modulo the other, for `k = 2^L / N ≥ N ≥ 21`) yields the concrete factor-`3` reduction
bound `succProbability_rabinInversionGame_le`:
`Game.succProbability (rabinInversionGame gen A n) ≤`
`3 * Game.succProbability (factoringGame gen (rabinToFactor A) n)`.
Both `FactoringHard` and `RabinOneWay` are parameterized by an arbitrary generator family
`gen : BlumGen := ℕ → PMF BlumDesc` (without bundling efficient Blum-modulus sampling or
bit-length bounds in `n`) and quantify over uniform native strict-PPT algorithms (`IsPPTOn`)
charging the full binary-encoded inputs and sampled/callback outputs uniformly before `n`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 9.2.3, Definition 9.45 (The Factoring Assumption) and Sections 15.5.1–15.5.2,
  Lemma 15.35, Theorem 15.36, Proposition 15.37, and Theorem 15.38 (Computing Modular Square
  Roots; A Trapdoor Permutation Based on Factoring).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Validity predicate for Blum modulus parameters `(p, q)`. -/
def BlumDescValid (raw : ℕ × ℕ) : Prop :=
  IsBlumModulus raw.1 raw.2

/-- Blum modulus parameters `(p, q)` with `p, q` distinct primes and `p ≡ q ≡ 3 [MOD 4]`. -/
abbrev BlumDesc := { raw : ℕ × ℕ // BlumDescValid raw }

namespace BlumDesc

/-- First Blum prime factor. -/
abbrev p (desc : BlumDesc) : ℕ := desc.1.1

/-- Second Blum prime factor. -/
abbrev q (desc : BlumDesc) : ℕ := desc.1.2

/-- The Blum modulus `N = p * q`. -/
abbrev modulus (desc : BlumDesc) : ℕ := desc.p * desc.q

/-- Primality of `p`. -/
theorem hp (desc : BlumDesc) : desc.p.Prime := desc.2.1.1

/-- Primality of `q`. -/
theorem hq (desc : BlumDesc) : desc.q.Prime := desc.2.2.1.1

/-- Distinctness of `p` and `q`. -/
theorem hpq (desc : BlumDesc) : desc.p ≠ desc.q := desc.2.2.2

/-- `p ≡ 3 [MOD 4]`. -/
theorem hp3 (desc : BlumDesc) : desc.p % 4 = 3 := desc.2.1.2

/-- `q ≡ 3 [MOD 4]`. -/
theorem hq3 (desc : BlumDesc) : desc.q % 4 = 3 := desc.2.2.1.2

/-- The Blum modulus is positive. -/
theorem modulus_pos (desc : BlumDesc) : 0 < desc.modulus :=
  Nat.mul_pos desc.hp.pos desc.hq.pos

/-- Every Blum prime is at least `3`. -/
theorem three_le_p (desc : BlumDesc) : 3 ≤ desc.p := by
  have hp2 := desc.hp.two_le
  have hp3 := desc.hp3
  omega

/-- Every Blum prime is at least `3`. -/
theorem three_le_q (desc : BlumDesc) : 3 ≤ desc.q := by
  have hq2 := desc.hq.two_le
  have hq3 := desc.hq3
  omega

/-- Every Blum modulus is at least `21`. -/
theorem twentyOne_le_modulus (desc : BlumDesc) : 21 ≤ desc.modulus := by
  have hp3 := desc.three_le_p
  have hq3 := desc.three_le_q
  have hpq := desc.hpq
  have hp_mod := desc.hp3
  have hq_mod := desc.hq3
  by_cases hp : desc.p = 3
  · have hq7 : 7 ≤ desc.q := by omega
    nlinarith
  · have hp7 : 7 ≤ desc.p := by omega
    nlinarith

end BlumDesc

/-- A Blum modulus generator indexed by the security parameter `n`. -/
abbrev BlumGen := ℕ → PMF BlumDesc

/-- Rabin squaring function: `x ^ 2 % N`. -/
def rabinEval (N x : ℕ) : ℕ := x ^ 2 % N

/-- Rabin squaring `(N, x) ↦ x ^ 2 % N` is computable in polynomial time whenever `N` and `x` are
computable in polynomial time and `0 < N a`. -/
theorem computableInPolyTime_rabinEval {α : Type} {enc : α ↪ List Bool} {N x : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hx : ComputableInPolyTime x enc encNat)
    (hpos : ∀ a, 0 < N a) :
    ComputableInPolyTime (fun a => rabinEval (N a) (x a)) enc encNat :=
  ComputableInPolyTime.binary_powMod hx (by fun_prop) hN hpos

/-- The integer factoring experiment: sample `desc ← gen n`, run `A n N`, and accept when `A`
returns a nontrivial factorization `1 < a`, `1 < b`, `a * b = N`. -/
noncomputable def factoringGame (gen : BlumGen) (A : ℕ → ℕ → ProbComp (ℕ × ℕ))
    (n : ℕ) : Game := do
  let desc ← gen n
  let ab ← ProbComp.eval (A n desc.modulus)
  return decide (1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus)

/-- The integer factoring assumption for `gen`: every uniform PPT factoring algorithm succeeds with
negligible probability. -/
def FactoringHard (gen : BlumGen) : Prop :=
  ∀ A : ℕ → ℕ → ProbComp (ℕ × ℕ),
    IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => A input.1 input.2) →
    Negligible (fun n => Game.succProbability (factoringGame gen A n))

/-- The Rabin inversion experiment: sample `desc ← gen n` and a uniform bitstring `r` of length
`2 * N.bits.length`, set `y = (ofBits r) ^ 2 % N`, and accept when `A n (N, y)` outputs `x'` with
`x' ^ 2 % N = y`. -/
noncomputable def rabinInversionGame (gen : BlumGen) (A : ℕ → ℕ × ℕ → ProbComp ℕ)
    (n : ℕ) : Game := do
  let desc ← gen n
  let r ← ProbComp.eval (BitString.sampleList (2 * desc.modulus.bits.length))
  let y := rabinEval desc.modulus (ofBits r)
  let x' ← ProbComp.eval (A n (desc.modulus, y))
  return decide (x' ^ 2 % desc.modulus = y)

/-- The Rabin one-wayness assumption for `gen`: every uniform PPT inverter has negligible
probability of finding a modular square root of `x ^ 2 % N`. -/
def RabinOneWay (gen : BlumGen) : Prop :=
  ∀ A : ℕ → ℕ × ℕ → ProbComp ℕ,
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encNat
      (fun input => A input.1 input.2) →
    Negligible (fun n => Game.succProbability (rabinInversionGame gen A n))

/-- Split `N` at `g = Nat.gcd u N`, returning `(g, N / g)`. -/
def rabinFactorPair (u N : ℕ) : ℕ × ℕ :=
  let g := Nat.gcd u N
  (g, N / g)

/-- Explicit PPT reduction from factoring to Rabin inversion: sample `x` uniformly, check
`gcd x N`, and otherwise query the Rabin inverter `A` on `(N, x^2 mod N)` to recover
`gcd (x + x') N`. -/
noncomputable def rabinToFactor (A : ℕ → ℕ × ℕ → ProbComp ℕ) (n N : ℕ) : ProbComp (ℕ × ℕ) := do
  let r ← BitString.sampleList (2 * N.bits.length)
  let x := ofBits r
  let g0 := Nat.gcd x N
  if 1 < g0 ∧ g0 < N then
    return rabinFactorPair x N
  else
    let y := rabinEval N x
    let x' ← A n (N, y)
    return rabinFactorPair (x + x') N

/-- Helper step for Chinese Remainder Theorem recombination in `crtSqrt`. -/
def crtStep (sp sq inv a' : ℕ) : ℕ :=
  (sp + a' - sq % a') * inv % a'

/-- Recombine square roots modulo Blum primes `a` and `b` via Fermat's little theorem CRT. -/
def crtSqrt (y a b : ℕ) : ℕ :=
  let a' := if a = 0 then 1 else a
  let b' := if b = 0 then 1 else b
  let sp := y ^ ((a + 1) / 4) % a'
  let sq := y ^ ((b + 1) / 4) % b'
  let inv := b ^ (a - 2) % a'
  sq + b * crtStep sp sq inv a'

/-- Explicit PPT reduction from Rabin inversion to factoring: given `(n, (N, y))`, run the
factoring algorithm `F n N`; if it returns `(a, b)` with `1 < a`, `1 < b`, `a * b = N`, extract
square roots modulo `a` and `b` via `y ^ ((p + 1) / 4) % p` and combine them via Fermat's little
theorem CRT. -/
def factorToRabin (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n : ℕ) (Ny : ℕ × ℕ) : ProbComp ℕ := do
  let N := Ny.1
  let y := Ny.2
  let ab ← F n N
  if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = N then
    return crtSqrt y ab.1 ab.2
  else
    return 0

private theorem blum_pow_add_one_div_four_sq {p y : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (hsq : ∃ x : ℕ, x ^ 2 ≡ y [MOD p]) :
    (y ^ ((p + 1) / 4) % p) ^ 2 ≡ y [MOD p] := by
  rcases hsq with ⟨x, hx⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff] at hx ⊢
  push_cast at hx ⊢
  rw [ZMod.natCast_mod, Nat.cast_pow, ← hx]
  by_cases hx0 : (x : ZMod p) = 0
  · have hpos : 0 < (p + 1) / 4 := by omega
    rw [hx0, zero_pow (by norm_num), zero_pow (Nat.ne_of_gt hpos), zero_pow (by norm_num)]
  · have h4 : 4 * ((p + 1) / 4) = p + 1 := by omega
    calc
      (((x : ZMod p) ^ 2) ^ ((p + 1) / 4)) ^ 2
          = (x : ZMod p) ^ (4 * ((p + 1) / 4)) := by ring
      _ = (x : ZMod p) ^ (p + 1) := by rw [h4]
      _ = (x : ZMod p) ^ (p - 1) * (x : ZMod p) ^ 2 := by
        have hp1 : 1 ≤ p := hp.one_lt.le
        rw [← pow_add, show p - 1 + 2 = p + 1 by omega]
      _ = 1 * (x : ZMod p) ^ 2 := by rw [ZMod.pow_card_sub_one_eq_one hx0]
      _ = (x : ZMod p) ^ 2 := one_mul _

private theorem crt_combine_sq_modEq {a b y : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (ha3 : a % 4 = 3) (hb3 : b % 4 = 3) (hsq : ∃ x : ℕ, x ^ 2 ≡ y [MOD a * b]) :
    let sp := y ^ ((a + 1) / 4) % a
    let sq := y ^ ((b + 1) / 4) % b
    let inv := b ^ (a - 2) % a
    let u := (sp + a - sq % a) * inv % a
    (sq + b * u) ^ 2 ≡ y [MOD a * b] := by
  intro sp sq inv u
  have hcop : Nat.Coprime a b := (Nat.coprime_primes ha hb).mpr hab
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  rcases hsq with ⟨x, hx⟩
  have hsq_a : ∃ z : ℕ, z ^ 2 ≡ y [MOD a] := ⟨x, hx.of_dvd (dvd_mul_right a b)⟩
  have hsq_b : ∃ z : ℕ, z ^ 2 ≡ y [MOD b] := ⟨x, hx.of_dvd (dvd_mul_left b a)⟩
  have hsp : sp ^ 2 ≡ y [MOD a] := blum_pow_add_one_div_four_sq ha ha3 hsq_a
  have hsq' : sq ^ 2 ≡ y [MOD b] := blum_pow_add_one_div_four_sq hb hb3 hsq_b
  have hmod_b : sq + b * u ≡ sq [MOD b] := by
    rw [Nat.ModEq, Nat.add_mul_mod_self_left]
  have hmod_a : sq + b * u ≡ sp [MOD a] := by
    have : Fact a.Prime := ⟨ha⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    have hsq_le : sq % a ≤ a := Nat.le_of_lt (Nat.mod_lt sq ha.pos)
    have hle : sq % a ≤ sp + a := by omega
    dsimp only [u, inv]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_sub hle,
      Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_mod, ZMod.natCast_mod,
      ZMod.natCast_mod, Nat.cast_pow, Nat.cast_pow]
    have hb0 : (b : ZMod a) ≠ 0 := by
      intro h0
      exact hab.symm ((hb.dvd_iff_eq ha.ne_one).mp ((ZMod.natCast_eq_zero_iff b a).mp h0))
    have ha2 : 2 ≤ a := ha.two_le
    calc
      (sq : ZMod a) + (b : ZMod a) *
          (((y : ZMod a) ^ ((a + 1) / 4) - (sq : ZMod a)) * (b : ZMod a) ^ (a - 2))
          = (sq : ZMod a) +
              ((y : ZMod a) ^ ((a + 1) / 4) - (sq : ZMod a)) *
                ((b : ZMod a) ^ (a - 2) * (b : ZMod a) ^ 1) := by ring
      _ = (sq : ZMod a) +
            ((y : ZMod a) ^ ((a + 1) / 4) - (sq : ZMod a)) * (b : ZMod a) ^ (a - 1) := by
          rw [← pow_add, show a - 2 + 1 = a - 1 by omega]
      _ = (sq : ZMod a) + ((y : ZMod a) ^ ((a + 1) / 4) - (sq : ZMod a)) * 1 := by
          rw [ZMod.pow_card_sub_one_eq_one hb0]
      _ = (y : ZMod a) ^ ((a + 1) / 4) := by ring
  exact ⟨(hmod_a.pow 2).trans hsp, (hmod_b.pow 2).trans hsq'⟩

private theorem computableInPolyTime_crtStep {α : Type} {enc : α ↪ List Bool}
    {sp sq inv a' : α → ℕ}
    (hsp : ComputableInPolyTime sp enc encNat)
    (hsq : ComputableInPolyTime sq enc encNat)
    (hinv : ComputableInPolyTime inv enc encNat)
    (ha' : ComputableInPolyTime a' enc encNat) :
    ComputableInPolyTime (fun x => crtStep (sp x) (sq x) (inv x) (a' x)) enc encNat := by
  unfold crtStep
  fun_prop

private theorem computableInPolyTime_crtSqrt {α : Type} {enc : α ↪ List Bool}
    {y a b : α → ℕ}
    (hy : ComputableInPolyTime y enc encNat)
    (ha : ComputableInPolyTime a enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun x => crtSqrt (y x) (a x) (b x)) enc encNat := by
  unfold crtSqrt
  have ha_pos : ∀ x, 0 < (if a x = 0 then 1 else a x) := fun x => by
    split_ifs <;> omega
  have hb_pos : ∀ x, 0 < (if b x = 0 then 1 else b x) := fun x => by
    split_ifs <;> omega
  have ha' : ComputableInPolyTime (fun x => if a x = 0 then 1 else a x) enc encNat := by fun_prop
  have hb' : ComputableInPolyTime (fun x => if b x = 0 then 1 else b x) enc encNat := by fun_prop
  have hsp : ComputableInPolyTime
      (fun x => y x ^ ((a x + 1) / 4) % (if a x = 0 then 1 else a x)) enc encNat :=
    ComputableInPolyTime.binary_powMod hy (by fun_prop) ha' ha_pos
  have hsq : ComputableInPolyTime
      (fun x => y x ^ ((b x + 1) / 4) % (if b x = 0 then 1 else b x)) enc encNat :=
    ComputableInPolyTime.binary_powMod hy (by fun_prop) hb' hb_pos
  have hinv : ComputableInPolyTime
      (fun x => b x ^ (a x - 2) % (if a x = 0 then 1 else a x)) enc encNat :=
    ComputableInPolyTime.binary_powMod hb (by fun_prop) ha' ha_pos
  have hstep := computableInPolyTime_crtStep hsp hsq hinv ha'
  dsimp only
  fun_prop

private theorem computableInPolyTime_rabinFactorPair {α : Type} {enc : α ↪ List Bool}
    {u N : α → ℕ}
    (hu : ComputableInPolyTime u enc encNat)
    (hN : ComputableInPolyTime N enc encNat) :
    ComputableInPolyTime (fun x => rabinFactorPair (u x) (N x)) enc (encPair encNat encNat) := by
  unfold rabinFactorPair
  have hg := ComputableInPolyTime.binary_gcd' hu hN
  fun_prop

/-- `factorToRabin F` is uniform PPT whenever `F` is uniform PPT. -/
theorem isPPTOn_factorToRabin {F : ℕ → ℕ → ProbComp (ℕ × ℕ)}
    (hF : IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => F input.1 input.2)) :
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encNat
      (fun input => factorToRabin F input.1 input.2) := by
  unfold factorToRabin
  have hcrt := @computableInPolyTime_crtSqrt
  refine IsPPTOn.bind_with
    (IsPPTOn.preprocess hF (prepare := fun input : ℕ × (ℕ × ℕ) => (input.1, input.2.1))
      (by fun_prop)) ?_
  ppt

/-- `rabinToFactor A` is uniform PPT whenever `A` is uniform PPT. -/
theorem isPPTOn_rabinToFactor {A : ℕ → ℕ × ℕ → ProbComp ℕ}
    (hA : IsPPTOn (encPair encUnary (encPair encNat encNat)) encNat
      (fun input => A input.1 input.2)) :
    IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => rabinToFactor A input.1 input.2) := by
  unfold rabinToFactor rabinEval
  have hpair := @computableInPolyTime_rabinFactorPair
  have hlen : ComputableInPolyTime (fun input : ℕ × ℕ => 2 * input.2.bits.length)
      (encPair encUnary encNat) encUnary := by fun_prop
  refine IsPPTOn.bind_with hlen.sampleList ?_
  have hcond : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List Bool =>
        decide (1 < Nat.gcd (ofBits x.2) x.1.2 ∧ Nat.gcd (ofBits x.2) x.1.2 < x.1.2))
      (encPair (encPair encUnary encNat) encBits) encBool := by
    fun_prop
  have hyes : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List Bool => rabinFactorPair (ofBits x.2) x.1.2)
      (encPair (encPair encUnary encNat) encBits) (encPair encNat encNat) :=
    hpair (by fun_prop) (by fun_prop)
  have hno_branch : IsPPTOn (encPair (encPair encUnary encNat) encBits) (encPair encNat encNat)
      (fun x : (ℕ × ℕ) × List Bool => do
        let x' ← A x.1.1 (x.1.2, (ofBits x.2) ^ 2 % x.1.2)
        pure (rabinFactorPair (ofBits x.2 + x') x.1.2)) := by
    refine IsPPTOn.bind_with
      (IsPPTOn.preprocess hA
        (prepare := fun x : (ℕ × ℕ) × List Bool =>
          (x.1.1, (x.1.2, (ofBits x.2) ^ 2 % x.1.2)))
        (by fun_prop)) ?_
    have hno : ComputableInPolyTime
        (fun x : ((ℕ × ℕ) × List Bool) × ℕ => rabinFactorPair (ofBits x.1.2 + x.2) x.1.1.2)
        (encPair (encPair (encPair encUnary encNat) encBits) encNat) (encPair encNat encNat) :=
      hpair (by fun_prop) (by fun_prop)
    exact hno.isPPTOn
  exact (IsPPTOn.cond' hcond hyes.isPPTOn hno_branch).congr
    (fun _ => by simp only [decide_eq_true_eq])

private theorem mul_eq_blum_cases {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 1 < a) (hb : 1 < b) (hab : a * b = p * q) :
    (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  have hdvd : a ∣ p * q := ⟨b, hab.symm⟩
  by_cases hpa : p ∣ a
  · rcases hpa with ⟨k, rfl⟩
    have hkb : k * b = q := by
      have : p * (k * b) = p * q := by rw [← mul_assoc]; exact hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    rcases (Nat.dvd_prime hq).mp ⟨b, hkb.symm⟩ with rfl | hk
    · left; exact ⟨mul_one p, by simpa using hkb⟩
    · rw [hk] at hkb
      have hb1 : b = 1 := Nat.eq_of_mul_eq_mul_left hq.pos (by simpa using hkb)
      omega
  · have haq : a ∣ q := (hp.coprime_iff_not_dvd.mpr hpa).symm.dvd_of_dvd_mul_left hdvd
    rcases (Nat.dvd_prime hq).mp haq with rfl | rfl
    · exact absurd ha (by omega)
    · right
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hq.pos (by rw [hab, mul_comm])⟩

/-- On a nontrivial factorization `a * b = N` of a Blum modulus, `crtSqrt` returns a square root of
every Rabin image `x ^ 2 % N`. -/
private theorem crtSqrt_sq_mod_eq {desc : BlumDesc} {a b x : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hab : a * b = desc.modulus) :
    crtSqrt (rabinEval desc.modulus x) a b ^ 2 % desc.modulus = rabinEval desc.modulus x := by
  set y := rabinEval desc.modulus x
  have hy_lt : y < desc.modulus := Nat.mod_lt _ desc.modulus_pos
  have hy_mod : x ^ 2 ≡ y [MOD a * b] := by
    rw [hab]
    exact (Nat.mod_modEq (x ^ 2) desc.modulus).symm
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hcrt_eq : crtSqrt y a b =
      y ^ ((b + 1) / 4) % b + b * ((y ^ ((a + 1) / 4) % a + a - (y ^ ((b + 1) / 4) % b) % a) *
        (b ^ (a - 2) % a) % a) := by
    simp only [crtSqrt, crtStep, ha0, hb0, ↓reduceIte]
  rw [hcrt_eq]
  rcases mul_eq_blum_cases desc.hp desc.hq ha hb hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hmod := crt_combine_sq_modEq desc.hp desc.hq desc.hpq desc.hp3 desc.hq3 ⟨x, hy_mod⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt hy_lt] at hmod
    exact hmod
  · have hmod := crt_combine_sq_modEq desc.hq desc.hp desc.hpq.symm desc.hq3 desc.hp3 ⟨x, hy_mod⟩
    rw [Nat.ModEq, mul_comm desc.q desc.p, Nat.mod_eq_of_lt hy_lt] at hmod
    exact hmod

/-- Success probability of `factoringGame gen F n` is at most that of
`rabinInversionGame gen (factorToRabin F) n`. -/
theorem succProbability_factoringGame_le (gen : BlumGen)
    (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n : ℕ) :
    Game.succProbability (factoringGame gen F n) ≤
      Game.succProbability (rabinInversionGame gen (factorToRabin F) n) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [factoringGame, rabinInversionGame, Bind.bind, Pure.pure, PMF.bind_apply,
    PMF.pure_apply, eq_comm (a := true), decide_eq_true_eq]
  refine tsum_le_tsum fun desc => mul_le_mul_of_nonneg_left ?_ zero_le
  -- The factoring success does not depend on the Rabin challenge `r`.
  calc _ = ∑' r, ProbComp.eval (BitString.sampleList (2 * desc.modulus.bits.length)) r *
        ∑' ab : ℕ × ℕ, ProbComp.eval (F n desc.modulus) ab *
          if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus then 1 else 0 := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := by
      refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
      -- On a nontrivial factorization, `factorToRabin` returns a square root.
      simp only [factorToRabin, ProbComp.eval_bind, PMF.tsum_bind_mul]
      refine tsum_le_tsum fun ab => mul_le_mul_of_nonneg_left ?_ zero_le
      split_ifs with h
      · simp only [ProbComp.eval_pure, PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
        rw [ite_eq_left (crtSqrt_sq_mod_eq h.1 h.2.1 h.2.2)]
      · exact zero_le

/-- If Rabin squaring is one-way for `gen`, then factoring is hard for `gen`. -/
theorem factoringHard_of_rabinOneWay {gen : BlumGen} (h : RabinOneWay gen) :
    FactoringHard gen := fun F hF =>
  negligible_of_le (h _ (isPPTOn_factorToRabin hF)) (succProbability_factoringGame_le gen F)

private theorem ofBits_ofFn_equivFin_symm (L : ℕ) (x : Fin (2 ^ L)) :
    ofBits (List.ofFn ((BitString.equivFin L).symm x)) = x.1 := by
  rw [ofBits, ← BitString.lsbValue_eq_foldr_bit, BitString.lsbValue_ofFn, Equiv.apply_symm_apply]

private theorem tsum_uniformList_mul (L : ℕ) (g : List Bool → ℝ≥0∞) :
    (∑' r : List Bool, BitString.uniformList L r * g r) =
      (2 ^ L : ℝ≥0∞)⁻¹ * ∑ x : Fin (2 ^ L), g (List.ofFn ((BitString.equivFin L).symm x)) := by
  simp only [BitString.uniformList, PMF.map_apply, PMF.uniformOfFintype_apply,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hcomm : (∑' r : List Bool,
      (∑' f : Fin L → Bool, if r = List.ofFn f then ((2 ^ L : ℕ) : ℝ≥0∞)⁻¹ else 0) * g r) =
      ∑' f : Fin L → Bool, ((2 ^ L : ℕ) : ℝ≥0∞)⁻¹ * g (List.ofFn f) := by
    simp_rw [← ENNReal.tsum_mul_right]
    rw [tsum_comm]
    refine tsum_congr fun f => ?_
    rw [tsum_eq_single (List.ofFn f) (fun r hr => by simp [hr])]
    simp
  rw [hcomm, tsum_fintype, ← Finset.mul_sum]
  congr 1
  · simp
  exact Fintype.sum_equiv (BitString.equivFin L)
    (fun f => g (List.ofFn f))
    (fun x => g (List.ofFn ((BitString.equivFin L).symm x)))
    (fun f => by simp)

private theorem le_two_pow_two_mul_bits_length_div (N : ℕ) (hN : 0 < N) :
    N ≤ 2 ^ (2 * N.bits.length) / N := by
  have hlt : N < 2 ^ N.bits.length := Nat.size_eq_bits_len N ▸ Nat.lt_size_self N
  have hsq : N * N ≤ 2 ^ (2 * N.bits.length) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul hlt.le hlt.le
  exact (Nat.le_div_iff_mul_le hN).mpr hsq

/-! ### Counting Rabin preimages -/

/-- The Rabin factor pair of `u` is a nontrivial factorization of `N` exactly when `gcd u N` is a
nontrivial factor of `N`. -/
private theorem rabinFactorPair_good_iff {u N : ℕ} :
    (1 < (rabinFactorPair u N).1 ∧ 1 < (rabinFactorPair u N).2 ∧
        (rabinFactorPair u N).1 * (rabinFactorPair u N).2 = N) ↔
      1 < Nat.gcd u N ∧ Nat.gcd u N < N := by
  have hmul : Nat.gcd u N * (N / Nat.gcd u N) = N := Nat.mul_div_cancel' (Nat.gcd_dvd_right u N)
  simp only [rabinFactorPair, hmul, and_true]
  refine and_congr_right fun h1 => ⟨fun h2 => ?_, fun h2 => ?_⟩
  · calc Nat.gcd u N = Nat.gcd u N * 1 := (mul_one _).symm
      _ < Nat.gcd u N * (N / Nat.gcd u N) := Nat.mul_lt_mul_of_pos_left h2 (by omega)
      _ = N := hmul
  · by_contra hle
    have : Nat.gcd u N * (N / Nat.gcd u N) ≤ Nat.gcd u N * 1 := Nat.mul_le_mul_left _ (by omega)
    omega

/-- A divisor `d` of `N` with `1 < d` that divides `u`, when `N` itself does not divide `u`,
forces `gcd u N` to be a nontrivial factor of `N`. -/
private theorem one_lt_gcd_lt_of_dvd {u N d : ℕ} (hN : 0 < N) (hd : 1 < d) (hdN : d ∣ N)
    (hdu : d ∣ u) (hNu : ¬ N ∣ u) : 1 < Nat.gcd u N ∧ Nat.gcd u N < N := by
  refine ⟨lt_of_lt_of_le hd (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right u hN)
    (Nat.dvd_gcd hdu hdN)), lt_of_le_of_ne (Nat.le_of_dvd hN (Nat.gcd_dvd_right u N)) ?_⟩
  intro h
  exact hNu (h ▸ Nat.gcd_dvd_left u N)

/-- Modulo a prime, two square roots of `x' ^ 2` that agree on whether they are `≡ x'` are
congruent. -/
private theorem modEq_of_sq_modEq_of_decide_eq {p a b x' : ℕ} (hp : p.Prime)
    (ha : a ^ 2 ≡ x' ^ 2 [MOD p]) (hb : b ^ 2 ≡ x' ^ 2 [MOD p])
    (hab : a ≡ x' [MOD p] ↔ b ≡ x' [MOD p]) : a ≡ b [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  simp only [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow] at ha hb hab ⊢
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with ha | ha <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb with hb | hb
  · rw [ha, hb]
  · rw [ha, hab.mp ha]
  · rw [hab.mpr hb, hb]
  · rw [ha, hb]

/-- Numbers with congruent squares are coprime to the modulus together. -/
private theorem coprime_of_sq_modEq {N a b : ℕ} (h : a ^ 2 ≡ b ^ 2 [MOD N]) (hb : Nat.Coprime b N) :
    Nat.Coprime a N := by
  rw [← Nat.coprime_pow_left_iff two_pos] at hb ⊢
  exact h.gcd_eq.trans hb

/-- An odd prime that does not divide `x'` does not divide `u + x'` when `u ≡ x'`. -/
private theorem not_dvd_add_of_modEq {p u x' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpx : ¬ p ∣ x')
    (hu : u ≡ x' [MOD p]) : ¬ p ∣ u + x' := by
  intro h
  have h2x : p ∣ 2 * x' := (((hu.add_right x').dvd_iff dvd_rfl).mp h).trans (by rw [two_mul])
  rcases (Nat.Prime.dvd_mul hp).mp h2x with h2 | h2
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · exact hpx h2

/-- A residue modulo `p * q` that is `≡ x'` modulo `p` and `≡ -x'` modulo `q`. -/
private theorem exists_crt_root {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (x' : ℕ) :
    ∃ r < p * q, r ≡ x' [MOD p] ∧ q ∣ r + x' := by
  let c := Nat.chineseRemainder ((Nat.coprime_primes hp hq).mpr hpq) x' ((q - 1) * x')
  refine ⟨c, Nat.chineseRemainder_lt_mul _ _ _ hp.ne_zero hq.ne_zero, c.2.1, ?_⟩
  have hq1 : (q - 1) * x' + x' = q * x' := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left x' hq.pos)]
  refine (Nat.modEq_zero_iff_dvd).mp ?_
  calc (c : ℕ) + x' ≡ (q - 1) * x' + x' [MOD q] := c.2.2.add_right x'
    _ = q * x' := hq1
    _ ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right q x')

/-- Each residue class modulo `N` contains at least `2 ^ L / N` numbers below `2 ^ L`. -/
private theorem le_card_residueClass {N L r : ℕ} (hr : r < N) :
    2 ^ L / N ≤ (Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = r)).card := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) hr
  let θ : Fin (2 ^ L / N) → Fin (2 ^ L) := fun m => ⟨m.1 * N + r, by
    have h1 : (m.1 + 1) * N ≤ 2 ^ L / N * N := Nat.mul_le_mul_right N m.2
    have h2 : 2 ^ L / N * N ≤ 2 ^ L := Nat.div_mul_le_self _ _
    rw [Nat.add_mul, one_mul] at h1
    omega⟩
  have hmem : ∀ m ∈ (Finset.univ : Finset (Fin (2 ^ L / N))),
      θ m ∈ Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = r) := fun m _ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, θ, Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt hr]
  have hinj : Set.InjOn θ (Finset.univ : Finset (Fin (2 ^ L / N))) := fun m₁ _ m₂ _ h => by
    have h' : m₁.1 * N + r = m₂.1 * N + r := congrArg Fin.val h
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hN (Nat.add_right_cancel h'))
  simpa using Finset.card_le_card_of_injOn θ hmem hinj

/-- At most `4 * (2 ^ L / (p * q) + 1)` numbers below `2 ^ L` square to `x' ^ 2` modulo
`p * q`: such an `x` is determined by its quotient by `p * q` and by whether it is `≡ x'`
modulo `p` and modulo `q`. -/
private theorem card_sq_modEq_le {p q L x' : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 ^ 2 ≡ x' ^ 2 [MOD p * q])).card ≤
      4 * (2 ^ L / (p * q) + 1) := by
  let ψ : Fin (2 ^ L) → (Bool × Bool) × Fin (2 ^ L / (p * q) + 1) := fun x =>
    ((decide (x.1 ≡ x' [MOD p]), decide (x.1 ≡ x' [MOD q])),
      ⟨x.1 / (p * q), Nat.lt_succ_of_le (Nat.div_le_div_right x.2.le)⟩)
  have hinj : Set.InjOn ψ (Finset.univ.filter (fun x : Fin (2 ^ L) =>
      x.1 ^ 2 ≡ x' ^ 2 [MOD p * q])) := by
    intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx₁ hx₂
    simp only [ψ, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide] at heq
    obtain ⟨⟨hbp, hbq⟩, hdiv⟩ := heq
    have hmodp := modEq_of_sq_modEq_of_decide_eq hp
      (hx₁.of_dvd (dvd_mul_right p q)) (hx₂.of_dvd (dvd_mul_right p q)) hbp
    have hmodq := modEq_of_sq_modEq_of_decide_eq hq
      (hx₁.of_dvd (dvd_mul_left q p)) (hx₂.of_dvd (dvd_mul_left q p)) hbq
    have hmod : x₁.1 % (p * q) = x₂.1 % (p * q) :=
      (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes hp hq).mpr hpq)).mp ⟨hmodp, hmodq⟩
    ext
    rw [← Nat.div_add_mod x₁.1 (p * q), ← Nat.div_add_mod x₂.1 (p * q), hdiv, hmod]
  have hcard := Finset.card_le_card_of_injOn ψ (fun _ _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using hcard

/-- If `x ≡ x' [MOD p]` and `q ∣ x + x'` for distinct odd primes `p, q` with `p ∤ x'`, then
`x` is a square root of `x' ^ 2` modulo `p * q` and `gcd (x + x') (p * q)` is the nontrivial
factor `q`. -/
private theorem sq_modEq_and_gcd_of_crt {p q x x' : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hpx : ¬ p ∣ x') (hxp : x ≡ x' [MOD p]) (hxq : q ∣ x + x') :
    x ^ 2 ≡ x' ^ 2 [MOD p * q] ∧
      1 < Nat.gcd (x + x') (p * q) ∧ Nat.gcd (x + x') (p * q) < p * q := by
  refine ⟨(Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes hp hq).mpr hpq)).mp
    ⟨hxp.pow 2, ?_⟩, one_lt_gcd_lt_of_dvd (Nat.mul_pos hp.pos hq.pos) hq.one_lt
      (dvd_mul_left q p) hxq fun hN => not_dvd_add_of_modEq hp hp2 hpx hxp
        ((dvd_mul_right p q).trans hN)⟩
  have hneg : (x : ZMod q) = -x' :=
    eq_neg_of_add_eq_zero_left (by exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr hxq)
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_pow, hneg, neg_sq]

/-- At most `2 ^ L / N + 1` numbers below `2 ^ L` lie in a given residue class modulo `N`. -/
private theorem card_residueClass_le {N L r : ℕ} :
    (Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = r)).card ≤ 2 ^ L / N + 1 := by
  let θ : Fin (2 ^ L) → Fin (2 ^ L / N + 1) := fun x =>
    ⟨x.1 / N, Nat.lt_succ_of_le (Nat.div_le_div_right x.2.le)⟩
  have hinj : Set.InjOn θ (Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = r)) := by
    intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx₁ hx₂
    have hdiv : x₁.1 / N = x₂.1 / N := congrArg Fin.val heq
    ext
    rw [← Nat.div_add_mod x₁.1 N, ← Nat.div_add_mod x₂.1 N, hdiv, hx₁, hx₂]
  simpa using Finset.card_le_card_of_injOn θ (fun _ _ => Finset.mem_univ _) hinj

/-- If `x % N = d` for a divisor `d` of `N`, then `gcd x N = d`. -/
private theorem gcd_eq_of_mod_eq {x N d : ℕ} (hd : d ∣ N) (hx : x % N = d) : Nat.gcd x N = d := by
  rw [Nat.gcd_comm, Nat.gcd_rec, hx, Nat.gcd_comm, Nat.gcd_eq_right hd]

/-- For distinct primes `p, q` and `k = 2 ^ L / (p * q) ≥ 1`, at most twice as many numbers below
`2 ^ L` share a factor with `p * q` as have a nontrivial gcd with it: the multiples of `p * q`
number at most `k + 1`, while the classes of `p` and `q` modulo `p * q` contribute at least `2 * k`
numbers with nontrivial gcd. -/
private theorem card_not_coprime_le {p q L : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hk : 1 ≤ 2 ^ L / (p * q)) :
    (Finset.univ.filter (fun x : Fin (2 ^ L) => ¬Nat.gcd x.1 (p * q) = 1)).card ≤
      2 * (Finset.univ.filter (fun x : Fin (2 ^ L) =>
        1 < Nat.gcd x.1 (p * q) ∧ Nat.gcd x.1 (p * q) < p * q)).card := by
  set N := p * q
  set nt := Finset.univ.filter (fun x : Fin (2 ^ L) => 1 < Nat.gcd x.1 N ∧ Nat.gcd x.1 N < N)
  have hN : 0 < N := Nat.mul_pos hp.pos hq.pos
  -- A number sharing a factor with `N` is a multiple of `N` or has a nontrivial gcd.
  have hsplit : Finset.univ.filter (fun x : Fin (2 ^ L) => ¬Nat.gcd x.1 N = 1) ⊆
      Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = 0) ∪ nt := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, nt] at hx ⊢
    have h1 := Nat.gcd_pos_of_pos_right x.1 hN
    have h2 := Nat.le_of_dvd hN (Nat.gcd_dvd_right x.1 N)
    rcases h2.lt_or_eq with h2 | h2
    · exact Or.inr ⟨by omega, h2⟩
    · exact Or.inl (Nat.mod_eq_zero_of_dvd (h2 ▸ Nat.gcd_dvd_left x.1 N))
  -- The classes of the proper divisors `p` and `q` modulo `N` lie in `nt`.
  have hclass : ∀ d, 1 < d → d < N → d ∣ N →
      Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = d) ⊆ nt := by
    intro d hd1 hdN hd x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, nt] at hx ⊢
    rw [gcd_eq_of_mod_eq hd hx]
    exact ⟨hd1, hdN⟩
  have hpN : p < N := lt_mul_of_one_lt_right hp.pos hq.one_lt
  have hqN : q < N := lt_mul_of_one_lt_left hq.pos hp.one_lt
  have hdisj : Disjoint (Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = p))
      (Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = q)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact hpq (h1.symm.trans h2)
  have hnt := Finset.card_le_card (Finset.union_subset
    (hclass p hp.one_lt hpN (dvd_mul_right p q)) (hclass q hq.one_lt hqN (dvd_mul_left q p)))
  rw [Finset.card_union_of_disjoint hdisj] at hnt
  have hlp := le_card_residueClass (L := L) hpN
  have hlq := le_card_residueClass (L := L) hqN
  have h0 := card_residueClass_le (N := N) (L := L) (r := 0)
  have hsub := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  omega

/-- For distinct odd primes `p, q` with `2 ≤ 2 ^ L / (p * q)` and any `x'`, at least a third of
the units `x < 2 ^ L` with `x ^ 2 ≡ x' ^ 2 [MOD p * q]` split `p * q` through
`gcd (x + x') (p * q)`. There are at most `4 * (k + 1)` such units for `k = 2 ^ L / (p * q)`,
and the two mixed classes, `≡ x'` modulo one prime and `≡ -x'` modulo the other, contribute at
least `2 * k` splitting ones. -/
private theorem rabin_fiber_card_le {p q L x' : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hk : 2 ≤ 2 ^ L / (p * q)) :
    ((Finset.univ.filter (fun x : Fin (2 ^ L) => Nat.gcd x.1 (p * q) = 1)).filter
        (fun x => x' ^ 2 % (p * q) = x.1 ^ 2 % (p * q))).card ≤
      3 * (((Finset.univ.filter (fun x : Fin (2 ^ L) => Nat.gcd x.1 (p * q) = 1)).filter
        (fun x => x' ^ 2 % (p * q) = x.1 ^ 2 % (p * q))).filter
          (fun x => 1 < Nat.gcd (x.1 + x') (p * q) ∧ Nat.gcd (x.1 + x') (p * q) < p * q)).card := by
  set N := p * q
  set S := (Finset.univ.filter (fun x : Fin (2 ^ L) => Nat.gcd x.1 N = 1)).filter
    (fun x => x' ^ 2 % N = x.1 ^ 2 % N)
  rcases S.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · simp [hempty]
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx₀
  -- `x'` is a unit since it has the same square as the unit `x₀`.
  have hx' : Nat.Coprime x' N := coprime_of_sq_modEq hx₀.2 hx₀.1
  have hpx : ¬p ∣ x' :=
    hp.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_left (dvd_mul_right p q) hx'.symm)
  have hqx : ¬q ∣ x' :=
    hq.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_left (dvd_mul_left q p) hx'.symm)
  -- Upper bound: the fibre has at most `4 * (k + 1)` elements.
  have hupper : S.card ≤ 4 * (2 ^ L / N + 1) :=
    (Finset.card_le_card fun x hx => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.2.symm).trans (card_sq_modEq_le (x' := x') hp hq hpq)
  -- Lower bound: each mixed CRT class lies in the splitting part of the fibre.
  have hclass : ∀ {a b : ℕ}, a.Prime → b.Prime → a ≠ b → a ≠ 2 → ¬a ∣ x' → a * b = N →
      ∀ r, r ≡ x' [MOD a] → b ∣ r + x' →
        Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = r) ⊆
          S.filter (fun x => 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N) := by
    intro a b ha hb hab ha2 hax habN r hra hrb x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hxr : x.1 ≡ r [MOD a * b] := by
      rw [habN, Nat.ModEq, ← hx, Nat.mod_mod]
    have hxa : x.1 ≡ x' [MOD a] := (hxr.of_dvd (dvd_mul_right a b)).trans hra
    have hxb : b ∣ x.1 + x' :=
      ((hxr.of_dvd (dvd_mul_left b a)).add_right x').dvd_iff dvd_rfl |>.mpr hrb
    obtain ⟨hsq, hgcd⟩ := habN ▸ sq_modEq_and_gcd_of_crt ha hb hab ha2 hax hxa hxb
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨coprime_of_sq_modEq hsq hx', hsq.symm⟩, hgcd⟩
  obtain ⟨r₁, hr₁N, hr₁p, hr₁q⟩ := exists_crt_root hp hq hpq x'
  obtain ⟨r₂, hr₂N, hr₂q, hr₂p⟩ := exists_crt_root hq hp hpq.symm x'
  rw [mul_comm q p] at hr₂N
  have hdisj : Disjoint (Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = r₁))
      (Finset.univ.filter (fun x : Fin (2 ^ L) => x.1 % N = r₂)) := by
    rw [Finset.disjoint_filter]
    rintro x - h1 h2
    exact not_dvd_add_of_modEq hp hp2 hpx hr₁p (h1.symm.trans h2 ▸ hr₂p)
  have hlower := Finset.card_le_card (Finset.union_subset
    (hclass hp hq hpq hp2 hpx rfl r₁ hr₁p hr₁q)
    (hclass hq hp hpq.symm hq2 hqx (mul_comm q p) r₂ hr₂q hr₂p))
  rw [Finset.card_union_of_disjoint hdisj] at hlower
  have h₁ := le_card_residueClass (N := N) (L := L) hr₁N
  have h₂ := le_card_residueClass (N := N) (L := L) hr₂N
  omega

/-- The counting core of the Rabin-to-factoring reduction, for an arbitrary inverter
distribution `P`: summed over the `2 ^ L` draws `x`, the probability that `P` inverts
`x ^ 2 % N` is at most three times the probability that the reduction splits `N`, either through
`gcd x N` directly or through `gcd (x + x') N` for the inverter's answer `x'`. -/
private theorem sum_rabin_success_le {p q N L : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hN : p * q = N) (hk : 2 ≤ 2 ^ L / N) (P : ℕ → PMF ℕ) :
    ∑ x : Fin (2 ^ L), ∑' x', P (rabinEval N x.1) x' *
        (if x' ^ 2 % N = rabinEval N x.1 then 1 else 0) ≤
      3 * ∑ x : Fin (2 ^ L),
        if 1 < Nat.gcd x.1 N ∧ Nat.gcd x.1 N < N then 1
        else ∑' x', P (rabinEval N x.1) x' *
          (if 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N then 1 else 0) := by
  subst hN
  set N := p * q
  set U := Finset.univ.filter (fun x : Fin (2 ^ L) => Nat.gcd x.1 N = 1)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Fin (2 ^ L) => Nat.gcd x.1 N = 1),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Fin (2 ^ L) => Nat.gcd x.1 N = 1),
    mul_add]
  refine add_le_add ?_ ?_
  · -- Units: compare fibre by fibre over the inverter's answer `x'`.
    rw [Finset.sum_ite_of_false fun x hx => by
      have := (Finset.mem_filter.mp hx).2
      omega]
    rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable),
      ← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable), ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun x' => ?_
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    set S := U.filter (fun x => x' ^ 2 % N = rabinEval N x.1)
    set T := S.filter (fun x => 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N)
    have hP : ∀ x ∈ S, P (rabinEval N x.1) x' = P (x' ^ 2 % N) x' := fun x hx => by
      rw [(Finset.mem_filter.mp hx).2]
    calc ∑ x ∈ S, P (rabinEval N x.1) x'
        ≤ S.card • P (x' ^ 2 % N) x' := Finset.sum_le_card_nsmul _ _ _ fun x hx => (hP x hx).le
      _ ≤ (3 * T.card) • P (x' ^ 2 % N) x' :=
          nsmul_le_nsmul_left zero_le (rabin_fiber_card_le hp hq hpq hp2 hq2 hk)
      _ = 3 * (T.card • P (x' ^ 2 % N) x') := by
          simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
      _ ≤ 3 * ∑ x ∈ T, P (rabinEval N x.1) x' := by
          gcongr
          exact Finset.card_nsmul_le_sum _ _ _ fun x hx => (hP x (Finset.filter_subset _ _ hx)).ge
      _ ≤ 3 * ∑ x ∈ U.filter (fun x => 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N),
            P (rabinEval N x.1) x' := by
          gcongr
          exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
  · -- Non-units: each success probability is at most `1`, and at most twice as many draws
    -- share a factor with `N` as split it outright.
    calc ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ L) => ¬Nat.gcd x.1 N = 1),
          ∑' x', P (rabinEval N x.1) x' * (if x' ^ 2 % N = rabinEval N x.1 then 1 else 0)
        ≤ ∑ _x ∈ Finset.univ.filter (fun x : Fin (2 ^ L) => ¬Nat.gcd x.1 N = 1), (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun x _ => ?_
          calc _ ≤ ∑' x', P (rabinEval N x.1) x' :=
                tsum_le_tsum fun x' => mul_le_of_le_one_right zero_le (by split_ifs <;> simp)
            _ = 1 := PMF.tsum_coe _
      _ ≤ 3 * ∑ _x ∈ Finset.univ.filter (fun x : Fin (2 ^ L) =>
            1 < Nat.gcd x.1 N ∧ Nat.gcd x.1 N < N), (1 : ℝ≥0∞) := by
          simp only [Finset.sum_const, nsmul_one]
          exact_mod_cast (card_not_coprime_le hp hq hpq (le_trans (by norm_num) hk)).trans
            (Nat.mul_le_mul_right _ (by norm_num))
      _ ≤ _ := by
          gcongr
          refine (Finset.sum_congr rfl fun x hx =>
            (ite_eq_left (Finset.mem_filter.mp hx).2).symm).trans_le
              (Finset.sum_le_sum_of_subset fun x hx => ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          omega

/-- Success probability of `rabinInversionGame gen A n` is at most `3` times that of
`factoringGame gen (rabinToFactor A) n`. -/
theorem succProbability_rabinInversionGame_le (gen : BlumGen)
    (A : ℕ → ℕ × ℕ → ProbComp ℕ) (n : ℕ) :
    Game.succProbability (rabinInversionGame gen A n) ≤
      3 * Game.succProbability (factoringGame gen (rabinToFactor A) n) := by
  rw [Game.succProbability, Game.succProbability, ← ENNReal.toNNReal_ofNat 3,
    ← ENNReal.toNNReal_mul]
  refine ENNReal.toNNReal_mono (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)) ?_
  simp only [rabinInversionGame, factoringGame, Bind.bind, Pure.pure, PMF.bind_apply,
    PMF.pure_apply, BitString.eval_sampleList, eq_comm (a := true), decide_eq_true_eq]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun desc => ?_
  rw [mul_left_comm (3 : ℝ≥0∞)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have hp2 : desc.p ≠ 2 := by
    have := desc.three_le_p
    omega
  have hq2 : desc.q ≠ 2 := by
    have := desc.three_le_q
    omega
  have hk : 2 ≤ 2 ^ (2 * desc.modulus.bits.length) / desc.modulus := by
    have := le_two_pow_two_mul_bits_length_div desc.modulus desc.modulus_pos
    have := desc.twentyOne_le_modulus
    omega
  -- Average both experiments over the `2 ^ L` uniform draws `x`.
  simp only [rabinToFactor, ProbComp.eval_bind, BitString.eval_sampleList, PMF.tsum_bind_mul,
    tsum_uniformList_mul, ofBits_ofFn_equivFin_symm]
  rw [mul_left_comm (3 : ℝ≥0∞)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  refine (sum_rabin_success_le desc.hp desc.hq desc.hpq hp2 hq2 rfl hk
    fun y => ProbComp.eval (A n (desc.modulus, y))).trans_eq ?_
  -- Match the reduction's two branches with the counting bound.
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · simp only [ProbComp.eval_pure, PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
    rw [ite_eq_left (rabinFactorPair_good_iff.mpr h)]
  · rw [ProbComp.eval_bind, PMF.tsum_bind_mul]
    refine tsum_congr fun x' => ?_
    simp only [ProbComp.eval_pure, PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq,
      rabinFactorPair_good_iff]

/-- If factoring is hard for `gen`, then Rabin squaring is one-way for `gen`. -/
theorem rabinOneWay_of_factoringHard {gen : BlumGen} (h : FactoringHard gen) :
    RabinOneWay gen := fun A hA =>
  negligible_of_le ((h _ (isPPTOn_rabinToFactor hA)).const_mul 3)
    (succProbability_rabinInversionGame_le gen A)

/-- Equivalence of Rabin one-wayness and integer factoring hardness for Blum modulus generators. -/
theorem rabinOneWay_iff_factoringHard (gen : BlumGen) :
    RabinOneWay gen ↔ FactoringHard gen :=
  ⟨factoringHard_of_rabinOneWay, rabinOneWay_of_factoringHard⟩

end Cslib.Crypto

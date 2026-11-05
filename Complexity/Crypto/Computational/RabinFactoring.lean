/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Computational.QuadraticResiduosity
public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.BitString
public import Cslib.Foundations.Data.BitString
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PPT
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

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 13.4.2 (Theorem 13.12).
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

/-- Explicit PPT reduction from factoring to Rabin inversion: given `(n, N)`, sample a random
`r` of length `2 * N.bits.length`, check `gcd(x, N)` first, and otherwise invoke the Rabin
inverter `A` on `(N, x ^ 2 % N)` and take `gcd(x + x', N)`. -/
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

private theorem computableInPolyTime_add_mul {α : Type} {enc : α ↪ List Bool}
    {x y z : α → ℕ}
    (hx : ComputableInPolyTime x enc encNat)
    (hy : ComputableInPolyTime y enc encNat)
    (hz : ComputableInPolyTime z enc encNat) :
    ComputableInPolyTime (fun a => x a + y a * z a) enc encNat := by
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
  exact computableInPolyTime_add_mul hsq hb hstep

private theorem computableInPolyTime_gcd {α : Type} {enc : α ↪ List Bool}
    {u v : α → ℕ}
    (hu : ComputableInPolyTime u enc encNat)
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => Nat.gcd (u x) (v x)) enc encNat :=
  ComputableInPolyTime.binary_gcd.comp' (hu.pair hv)

private theorem computableInPolyTime_rabinFactorPair {α : Type} {enc : α ↪ List Bool}
    {u N : α → ℕ}
    (hu : ComputableInPolyTime u enc encNat)
    (hN : ComputableInPolyTime N enc encNat) :
    ComputableInPolyTime (fun x => rabinFactorPair (u x) (N x)) enc (encPair encNat encNat) := by
  unfold rabinFactorPair
  have hg := computableInPolyTime_gcd hu hN
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
  have hgcd := @computableInPolyTime_gcd
  have hpair := @computableInPolyTime_rabinFactorPair
  have hlen : ComputableInPolyTime (fun input : ℕ × ℕ => 2 * input.2.bits.length)
      (encPair encUnary encNat) encUnary := by fun_prop
  refine IsPPTOn.bind_with hlen.sampleList ?_
  have hcond : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List Bool =>
        decide (1 < Nat.gcd (ofBits x.2) x.1.2 ∧ Nat.gcd (ofBits x.2) x.1.2 < x.1.2))
      (encPair (encPair encUnary encNat) encBits) encBool := by
    have hg : ComputableInPolyTime
        (fun x : (ℕ × ℕ) × List Bool => Nat.gcd (ofBits x.2) x.1.2)
        (encPair (encPair encUnary encNat) encBits) encNat :=
      hgcd (by fun_prop) (by fun_prop)
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

private theorem crtSqrt_sq_mod_eq {desc : BlumDesc} {a b x : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hab : a * b = desc.modulus) :
    let y := rabinEval desc.modulus x
    (crtSqrt y a b) ^ 2 % desc.modulus = y := by
  intro y
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
  rw [← NNReal.coe_le_coe]
  refine ENNReal.toReal_mono (PMF.apply_ne_top (rabinInversionGame gen (factorToRabin F) n) true) ?_
  simp only [factoringGame, rabinInversionGame, factorToRabin,
    Bind.bind, Pure.pure, PMF.bind_apply, PMF.pure_apply,
    eq_comm (a := true), decide_eq_true_eq]
  refine tsum_le_tsum fun desc => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  have hsample : (∑' r : List Bool,
      (ProbComp.eval (BitString.sampleList (2 * desc.modulus.bits.length))) r) = 1 :=
    PMF.tsum_coe _
  calc
    (∑' ab : ℕ × ℕ, (ProbComp.eval (F n desc.modulus)) ab *
        if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus then 1 else 0)
        = (∑' ab : ℕ × ℕ, (ProbComp.eval (F n desc.modulus)) ab *
            ((if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus then 1 else 0) *
              (∑' r : List Bool,
                (ProbComp.eval (BitString.sampleList (2 * desc.modulus.bits.length))) r))) := by
          rw [hsample]
          refine tsum_congr fun ab => ?_
          ring
    _ = (∑' r : List Bool,
          (ProbComp.eval (BitString.sampleList (2 * desc.modulus.bits.length))) r *
            (∑' ab : ℕ × ℕ, (ProbComp.eval (F n desc.modulus)) ab *
              if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus then 1 else 0)) := by
          trans (∑' ab : ℕ × ℕ, ∑' r : List Bool,
              (ProbComp.eval (BitString.sampleList (2 * desc.modulus.bits.length))) r *
                ((ProbComp.eval (F n desc.modulus)) ab *
                  if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus then 1 else 0))
          · refine tsum_congr fun ab => ?_
            simp_rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun r => ?_
            ring
          · rw [tsum_comm]
            refine tsum_congr fun r => ?_
            rw [← ENNReal.tsum_mul_left]
    _ ≤ (∑' r : List Bool,
          (ProbComp.eval (BitString.sampleList (2 * desc.modulus.bits.length))) r *
            (∑' x' : ℕ, (∑' ab : ℕ × ℕ, (ProbComp.eval (F n desc.modulus)) ab *
              (if x' = (if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus
                  then crtSqrt (rabinEval desc.modulus (ofBits r)) ab.1 ab.2 else 0)
                then 1 else 0)) *
              if x' ^ 2 % desc.modulus = rabinEval desc.modulus (ofBits r)
                then 1 else 0)) := by
          refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ (by simp)
          have hswap : (∑' x' : ℕ, (∑' ab : ℕ × ℕ, (ProbComp.eval (F n desc.modulus)) ab *
              (if x' = (if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus
                  then crtSqrt (rabinEval desc.modulus (ofBits r)) ab.1 ab.2 else 0)
                then 1 else 0)) *
              if x' ^ 2 % desc.modulus = rabinEval desc.modulus (ofBits r)
                then 1 else 0) =
              ∑' ab : ℕ × ℕ, (ProbComp.eval (F n desc.modulus)) ab *
                ∑' x' : ℕ,
                  (if x' = (if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus
                      then crtSqrt (rabinEval desc.modulus (ofBits r)) ab.1 ab.2 else 0)
                    then 1 else 0) *
                  if x' ^ 2 % desc.modulus = rabinEval desc.modulus (ofBits r)
                    then 1 else 0 := by
            simp_rw [← ENNReal.tsum_mul_right]
            rw [tsum_comm]
            refine tsum_congr fun ab => ?_
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun x' => ?_
            ring
          rw [hswap]
          refine tsum_le_tsum fun ab => mul_le_mul_of_nonneg_left ?_ (by simp)
          by_cases hgood : 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus
          · have hcrt : crtSqrt (rabinEval desc.modulus (ofBits r)) ab.1 ab.2 ^ 2 % desc.modulus =
                rabinEval desc.modulus (ofBits r) :=
              crtSqrt_sq_mod_eq hgood.1 hgood.2.1 hgood.2.2
            simp only [hgood]
            rw [tsum_eq_single (crtSqrt (rabinEval desc.modulus (ofBits r)) ab.1 ab.2)
              (fun x' hx' => by simp [hx'])]
            simp [hcrt]
          · simp [hgood]
    _ = _ := by
          refine tsum_congr fun r => ?_
          congr 1
          refine tsum_congr fun x' => ?_
          change _ = (ProbComp.eval ((F n desc.modulus) >>= fun ab =>
            if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus then
              pure (crtSqrt (rabinEval desc.modulus (ofBits r)) ab.1 ab.2)
            else pure 0)) x' * _
          rw [ProbComp.eval_bind, PMF.bind_apply]
          simp_rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun ab => ?_
          split_ifs <;> simp_all [ProbComp.eval_pure, PMF.pure_apply]

/-- If Rabin squaring is one-way for `gen`, then factoring is hard for `gen`. -/
theorem factoringHard_of_rabinOneWay {gen : BlumGen} (h : RabinOneWay gen) :
    FactoringHard gen := by
  intro F hF d
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h (factorToRabin F) (isPPTOn_factorToRabin hF) d)
    (fun _ => by simp)
    (fun n => mul_le_mul_of_nonneg_left (succProbability_factoringGame_le gen F n) (by simp))

private theorem ofBits_lt_two_pow : ∀ l : List Bool, ofBits l < 2 ^ l.length
  | [] => by unfold ofBits; simp
  | b :: bs => by
    have ih := ofBits_lt_two_pow bs
    unfold ofBits at ih ⊢
    simp only [List.foldr_cons, List.length_cons, pow_succ']
    cases b <;> simp [Nat.bit_val] <;> omega

private theorem ofBits_ofFn_testBit (L : ℕ) :
    ∀ x : ℕ, x < 2 ^ L → ofBits (List.ofFn (fun i : Fin L => x.testBit i)) = x := by
  induction L with
  | zero =>
    intro x hx
    simp only [pow_zero] at hx
    obtain rfl : x = 0 := by omega
    unfold ofBits
    rfl
  | succ L ih =>
    intro x hx
    rw [List.ofFn_succ]
    unfold ofBits
    rw [List.foldr_cons]
    have hx2 : x / 2 < 2 ^ L := by
      rw [pow_succ'] at hx
      omega
    have hdiv : (fun i : Fin L => x.testBit i.succ) = (fun i : Fin L => (x / 2).testBit i) := by
      ext i
      simp [Nat.testBit_succ]
    have ih' := ih (x / 2) hx2
    unfold ofBits at ih'
    rw [hdiv, ih', Nat.bit_val, Fin.val_zero, Nat.testBit_zero]
    cases hmod : x % 2 == 1 <;> simp_all <;> omega

private theorem ofFn_testBit_ofBits (L : ℕ) :
    ∀ f : Fin L → Bool, (fun i : Fin L => (ofBits (List.ofFn f)).testBit i) = f := by
  induction L with
  | zero =>
    intro f
    ext i
    exact Fin.elim0 i
  | succ L ih =>
    intro f
    ext i
    refine Fin.cases ?_ ?_ i
    · rw [List.ofFn_succ]
      unfold ofBits
      rw [List.foldr_cons, Nat.bit_val]
      simp only [Fin.val_zero, Nat.testBit_zero]
      cases f 0 <;> simp
    · intro j
      rw [List.ofFn_succ]
      unfold ofBits
      rw [List.foldr_cons, Nat.bit_val]
      simp only [Fin.val_succ, Nat.testBit_succ]
      have hdiv : ((f 0).toNat +
          2 * List.foldr Nat.bit 0 (List.ofFn fun k : Fin L => f k.succ)) / 2 =
          List.foldr Nat.bit 0 (List.ofFn fun k : Fin L => f k.succ) := by
        (cases f 0 <;> simp); omega
      rw [add_comm (2 * List.foldr Nat.bit 0 (List.ofFn fun k : Fin L => f k.succ)) (f 0).toNat,
        hdiv]
      have ih' := congrFun (ih (fun k => f k.succ)) j
      unfold ofBits at ih'
      exact ih'

private def finTwoPowEquiv (L : ℕ) : (Fin L → Bool) ≃ Fin (2 ^ L) where
  toFun f := ⟨ofBits (List.ofFn f), by simpa using ofBits_lt_two_pow (List.ofFn f)⟩
  invFun x := fun i => x.1.testBit i
  left_inv f := ofFn_testBit_ofBits L f
  right_inv x := Fin.ext (ofBits_ofFn_testBit L x.1 x.2)

private theorem tsum_uniformList_mul (L : ℕ) (g : List Bool → ℝ≥0∞) :
    (∑' r : List Bool, BitString.uniformList L r * g r) =
      (2 ^ L : ℝ≥0∞)⁻¹ * ∑ x : Fin (2 ^ L), g (List.ofFn (fun i : Fin L => x.1.testBit i)) := by
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
  exact Fintype.sum_equiv (finTwoPowEquiv L)
    (fun f => g (List.ofFn f))
    (fun x => g (List.ofFn fun i : Fin L => x.1.testBit i))
    (fun f => by
      simp only [finTwoPowEquiv, Equiv.coe_fn_mk]
      congr 2
      exact (ofFn_testBit_ofBits L f).symm)

private theorem lt_two_pow_bits_length : ∀ n : ℕ, n < 2 ^ n.bits.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hbit : Nat.bit (decide (n % 2 = 1)) (n / 2) = n := by
        cases h : decide (n % 2 = 1) <;> simp [Nat.bit_val] at h ⊢ <;> omega
      have hn' : n / 2 = 0 → decide (n % 2 = 1) = true := by
        intro h0
        simp
        omega
      have hlen : n.bits.length = (n / 2).bits.length + 1 := by
        conv_lhs => rw [← hbit]
        rw [Nat.bits_append_bit (n / 2) (decide (n % 2 = 1)) hn', List.length_cons]
      rw [hlen, pow_succ']
      have hdiv : n / 2 < 2 ^ (n / 2).bits.length :=
        ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega))
      omega

private theorem le_two_pow_two_mul_bits_length_div (N : ℕ) (hN : 0 < N) :
    N ≤ 2 ^ (2 * N.bits.length) / N := by
  have hlt : N < 2 ^ N.bits.length := lt_two_pow_bits_length N
  have hsq : N * N ≤ 2 ^ (2 * N.bits.length) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul hlt.le hlt.le
  exact (Nat.le_div_iff_mul_le hN).mpr hsq

private theorem rabinFactorPair_good {u N : ℕ} (h1 : 1 < Nat.gcd u N) (h2 : Nat.gcd u N < N) :
    let ab := rabinFactorPair u N
    1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = N := by
  dsimp only [rabinFactorPair]
  have hdvd : Nat.gcd u N ∣ N := Nat.gcd_dvd_right u N
  have hmul : Nat.gcd u N * (N / Nat.gcd u N) = N := Nat.mul_div_cancel' hdvd
  have hdiv1 : 1 < N / Nat.gcd u N := by
    by_contra hle
    have hle' : N / Nat.gcd u N ≤ 1 := by omega
    have : Nat.gcd u N * (N / Nat.gcd u N) ≤ Nat.gcd u N * 1 :=
      Nat.mul_le_mul_left _ hle'
    omega
  exact ⟨h1, hdiv1, hmul⟩

private theorem gcd_prime_mul_eq_left {p q u : ℕ} (_hp : p.Prime) (hq : q.Prime) (_hpq : p ≠ q)
    (hpu : p ∣ u) (hqu : ¬ q ∣ u) :
    Nat.gcd u (p * q) = p := by
  have hdvd : Nat.gcd u (p * q) ∣ p * q := Nat.gcd_dvd_right u (p * q)
  have hpg : p ∣ Nat.gcd u (p * q) := Nat.dvd_gcd hpu (dvd_mul_right p q)
  by_cases hqg : q ∣ Nat.gcd u (p * q)
  · exact absurd (hqg.trans (Nat.gcd_dvd_left u (p * q))) hqu
  · have hcop : Nat.Coprime (Nat.gcd u (p * q)) q := (hq.coprime_iff_not_dvd.mpr hqg).symm
    have hgp : Nat.gcd u (p * q) ∣ p := hcop.dvd_of_dvd_mul_right hdvd
    exact Nat.dvd_antisymm hgp hpg

private theorem gcd_prime_mul_eq_right {p q u : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpu : ¬ p ∣ u) (hqu : q ∣ u) :
    Nat.gcd u (p * q) = q := by
  rw [mul_comm p q]
  exact gcd_prime_mul_eq_left hq hp hpq.symm hqu hpu

private theorem crt_pair_modEq {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    let N := p * q
    let r := ((a % p) * (q ^ (p - 2) % p) % p * q + (b % q) * (p ^ (q - 2) % q) % q * p) % N
    r < N ∧ r ≡ a [MOD p] ∧ r ≡ b [MOD q] := by
  intro N r
  have hN : 0 < N := Nat.mul_pos hp.pos hq.pos
  refine ⟨Nat.mod_lt _ hN, ?_, ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    have hmodp : r % p = ((a % p) * (q ^ (p - 2) % p) % p * q +
        (b % q) * (p ^ (q - 2) % q) % q * p) % p :=
      Nat.mod_mod_of_dvd _ (dvd_mul_right p q)
    rw [← ZMod.natCast_mod, hmodp]
    simp only [Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.add_mul_mod_self_right, ZMod.natCast_mod,
      Nat.cast_mul, Nat.cast_pow]
    have hq0 : (q : ZMod p) ≠ 0 := by
      intro h0
      exact hpq.symm ((hq.dvd_iff_eq hp.ne_one).mp ((ZMod.natCast_eq_zero_iff q p).mp h0))
    have hp2 : 2 ≤ p := hp.two_le
    calc
      (a : ZMod p) * (q : ZMod p) ^ (p - 2) * (q : ZMod p)
          = (a : ZMod p) * ((q : ZMod p) ^ (p - 2) * (q : ZMod p) ^ 1) := by ring
      _ = (a : ZMod p) * (q : ZMod p) ^ (p - 1) := by
              rw [← pow_add, show p - 2 + 1 = p - 1 by omega]
      _ = (a : ZMod p) * 1 := by rw [ZMod.pow_card_sub_one_eq_one hq0]
      _ = (a : ZMod p) := mul_one _
  · have : Fact q.Prime := ⟨hq⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    have hmodq : r % q = ((a % p) * (q ^ (p - 2) % p) % p * q +
        (b % q) * (p ^ (q - 2) % q) % q * p) % q :=
      Nat.mod_mod_of_dvd _ (dvd_mul_left q p)
    rw [← ZMod.natCast_mod, hmodq]
    simp only [Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_add_mod_self_right, ZMod.natCast_mod,
      Nat.cast_mul, Nat.cast_pow]
    have hp0 : (p : ZMod q) ≠ 0 := by
      intro h0
      exact hpq ((hp.dvd_iff_eq hq.ne_one).mp ((ZMod.natCast_eq_zero_iff p q).mp h0))
    have hq2 : 2 ≤ q := hq.two_le
    calc
      (b : ZMod q) * (p : ZMod q) ^ (q - 2) * (p : ZMod q)
          = (b : ZMod q) * ((p : ZMod q) ^ (q - 2) * (p : ZMod q) ^ 1) := by ring
      _ = (b : ZMod q) * (p : ZMod q) ^ (q - 1) := by
              rw [← pow_add, show q - 2 + 1 = q - 1 by omega]
      _ = (b : ZMod q) * 1 := by rw [ZMod.pow_card_sub_one_eq_one hp0]
      _ = (b : ZMod q) := mul_one _

private theorem blum_rabin_fiber_card_le {desc : BlumDesc} {L y x' : ℕ}
    (hL : desc.modulus ≤ 2 ^ L / desc.modulus)
    (hy : x' ^ 2 % desc.modulus = y) :
    let S_y : Finset (Fin (2 ^ L)) :=
      Finset.univ.filter (fun x => Nat.gcd x.1 desc.modulus = 1 ∧ x.1 ^ 2 % desc.modulus = y)
    S_y.card ≤ 3 * (S_y.filter (fun x =>
      1 < Nat.gcd (x.1 + x') desc.modulus ∧
        Nat.gcd (x.1 + x') desc.modulus < desc.modulus)).card := by
  intro S_y
  rcases S_y.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · rw [hempty]
    simp
  have hS : ∀ x ∈ S_y, Nat.gcd x.1 desc.modulus = 1 ∧ x.1 ^ 2 % desc.modulus = y := fun x hx =>
    (Finset.mem_filter.mp hx).2
  set N := desc.modulus
  set p := desc.p
  set q := desc.q
  set k := 2 ^ L / N
  have hk21 : 21 ≤ k := le_trans desc.twentyOne_le_modulus hL
  have hNpos : 0 < N := desc.modulus_pos
  have hp : p.Prime := desc.hp
  have hq : q.Prime := desc.hq
  have hpq : p ≠ q := desc.hpq
  have hp3 : p % 4 = 3 := desc.hp3
  have hq3 : q % 4 = 3 := desc.hq3
  have hcop_pq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  -- Upper bound: `S_y.card ≤ 4 * (k + 1)`
  have hupper : S_y.card ≤ 4 * (k + 1) := by
    let ψ : Fin (2 ^ L) → (Bool × Bool) × Fin (k + 1) := fun x =>
      ((decide (x.1 % p = x' % p), decide (x.1 % q = x' % q)),
        ⟨x.1 / N, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt x.2))⟩)
    have hinj : Set.InjOn ψ S_y := by
      intro x₁ hx₁ x₂ hx₂ heq
      have hdiv : x₁.1 / N = x₂.1 / N := congrArg (fun z => z.2.1) heq
      have hbp : decide (x₁.1 % p = x' % p) = decide (x₂.1 % p = x' % p) :=
        congrArg (fun z => z.1.1) heq
      have hbq : decide (x₁.1 % q = x' % q) = decide (x₂.1 % q = x' % q) :=
        congrArg (fun z => z.1.2) heq
      have hsq1 : x₁.1 ^ 2 ≡ x' ^ 2 [MOD N] := by
        rw [Nat.ModEq, (hS x₁ hx₁).2, hy]
      have hsq2 : x₂.1 ^ 2 ≡ x' ^ 2 [MOD N] := by
        rw [Nat.ModEq, (hS x₂ hx₂).2, hy]
      have hmodp : x₁.1 ≡ x₂.1 [MOD p] := by
        have : Fact p.Prime := ⟨hp⟩
        rw [← ZMod.natCast_eq_natCast_iff]
        have hs1 : (x₁.1 : ZMod p) ^ 2 = (x' : ZMod p) ^ 2 := by
          have := hsq1.of_dvd (dvd_mul_right p q)
          rw [← ZMod.natCast_eq_natCast_iff] at this
          simpa using this
        have hs2 : (x₂.1 : ZMod p) ^ 2 = (x' : ZMod p) ^ 2 := by
          have := hsq2.of_dvd (dvd_mul_right p q)
          rw [← ZMod.natCast_eq_natCast_iff] at this
          simpa using this
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs1 with h1 | h1 <;>
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs2 with h2 | h2
        · rw [h1, h2]
        · have e1 : x₁.1 % p = x' % p := by
            rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]; exact h1
          have e2 : x₂.1 % p = x' % p := by
            rw [e1] at hbp
            simpa using hbp.symm
          have e2' : (x₂.1 : ZMod p) = (x' : ZMod p) := by
            rw [ZMod.natCast_eq_natCast_iff]; exact e2
          rw [h1, e2']
        · have e2 : x₂.1 % p = x' % p := by
            rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]; exact h2
          have e1 : x₁.1 % p = x' % p := by
            rw [e2] at hbp
            simpa using hbp
          have e1' : (x₁.1 : ZMod p) = (x' : ZMod p) := by
            rw [ZMod.natCast_eq_natCast_iff]; exact e1
          rw [e1', h2]
        · rw [h1, h2]
      have hmodq : x₁.1 ≡ x₂.1 [MOD q] := by
        have : Fact q.Prime := ⟨hq⟩
        rw [← ZMod.natCast_eq_natCast_iff]
        have hs1 : (x₁.1 : ZMod q) ^ 2 = (x' : ZMod q) ^ 2 := by
          have := hsq1.of_dvd (dvd_mul_left q p)
          rw [← ZMod.natCast_eq_natCast_iff] at this
          simpa using this
        have hs2 : (x₂.1 : ZMod q) ^ 2 = (x' : ZMod q) ^ 2 := by
          have := hsq2.of_dvd (dvd_mul_left q p)
          rw [← ZMod.natCast_eq_natCast_iff] at this
          simpa using this
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs1 with h1 | h1 <;>
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs2 with h2 | h2
        · rw [h1, h2]
        · have e1 : x₁.1 % q = x' % q := by
            rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]; exact h1
          have e2 : x₂.1 % q = x' % q := by
            rw [e1] at hbq
            simpa using hbq.symm
          have e2' : (x₂.1 : ZMod q) = (x' : ZMod q) := by
            rw [ZMod.natCast_eq_natCast_iff]; exact e2
          rw [h1, e2']
        · have e2 : x₂.1 % q = x' % q := by
            rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]; exact h2
          have e1 : x₁.1 % q = x' % q := by
            rw [e2] at hbq
            simpa using hbq
          have e1' : (x₁.1 : ZMod q) = (x' : ZMod q) := by
            rw [ZMod.natCast_eq_natCast_iff]; exact e1
          rw [e1', h2]
        · rw [h1, h2]
      have hmodN : x₁.1 % N = x₂.1 % N :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop_pq).mp ⟨hmodp, hmodq⟩
      ext
      rw [← Nat.div_add_mod x₁.1 N, ← Nat.div_add_mod x₂.1 N, hdiv, hmodN]
    have hcard := Finset.card_le_card_of_injOn ψ (fun _ _ => Finset.mem_univ _) hinj
    simpa [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using hcard
  -- Lower bound: `2 * k ≤ (S_y.filter ...).card`
  have hpx' : ¬ p ∣ x' := by
    intro hdiv
    have hd1 : p ∣ x' ^ 2 := dvd_pow hdiv (by norm_num)
    have hd2 : p ∣ x' ^ 2 % N := (Nat.dvd_mod_iff (dvd_mul_right p q)).mpr hd1
    rw [hy, ← (hS x₀ hx₀).2] at hd2
    have hd3 : p ∣ x₀.1 ^ 2 := (Nat.dvd_mod_iff (dvd_mul_right p q)).mp hd2
    have hd4 : p ∣ x₀.1 := hp.dvd_of_dvd_pow hd3
    have hgcd : p ∣ Nat.gcd x₀.1 N := Nat.dvd_gcd hd4 (dvd_mul_right p q)
    rw [(hS x₀ hx₀).1] at hgcd
    exact hp.ne_one (Nat.dvd_one.mp hgcd)
  have hqx' : ¬ q ∣ x' := by
    intro hdiv
    have hd1 : q ∣ x' ^ 2 := dvd_pow hdiv (by norm_num)
    have hd2 : q ∣ x' ^ 2 % N := (Nat.dvd_mod_iff (dvd_mul_left q p)).mpr hd1
    rw [hy, ← (hS x₀ hx₀).2] at hd2
    have hd3 : q ∣ x₀.1 ^ 2 := (Nat.dvd_mod_iff (dvd_mul_left q p)).mp hd2
    have hd4 : q ∣ x₀.1 := hq.dvd_of_dvd_pow hd3
    have hgcd : q ∣ Nat.gcd x₀.1 N := Nat.dvd_gcd hd4 (dvd_mul_left q p)
    rw [(hS x₀ hx₀).1] at hgcd
    exact hq.ne_one (Nat.dvd_one.mp hgcd)
  set r₁ := ((x' % p) * (q ^ (p - 2) % p) % p * q +
    ((q - x' % q) % q) * (p ^ (q - 2) % q) % q * p) % N
  set r₂ := (((p - x' % p) % p) * (q ^ (p - 2) % p) % p * q +
    (x' % q) * (p ^ (q - 2) % q) % q * p) % N
  have hr₁ := crt_pair_modEq hp hq hpq (a := x') (b := q - x' % q)
  have hr₂ := crt_pair_modEq hp hq hpq (a := p - x' % p) (b := x')
  have hr_ne : r₁ ≠ r₂ := by
    intro heq
    have : Fact p.Prime := ⟨hp⟩
    have h1p : (r₁ : ZMod p) = (x' : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr₁.2.1
    have h2p : (r₂ : ZMod p) = ((p - x' % p : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr₂.2.1
    rw [heq, h2p] at h1p
    have hle : x' % p ≤ p := Nat.le_of_lt (Nat.mod_lt x' hp.pos)
    rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, ZMod.natCast_mod] at h1p
    have h2x : (2 : ZMod p) * (x' : ZMod p) = 0 := by
      calc
        (2 : ZMod p) * (x' : ZMod p) = (x' : ZMod p) + (x' : ZMod p) := by ring
        _ = -(x' : ZMod p) + (x' : ZMod p) := by conv_lhs => lhs; rw [← h1p]
        _ = 0 := neg_add_cancel _
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
      have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
      omega
    have hx0' : (x' : ZMod p) = 0 := (mul_eq_zero.mp h2x).resolve_left h20
    exact hpx' ((ZMod.natCast_eq_zero_iff x' p).mp hx0')
  have hlower : 2 * k ≤ (S_y.filter (fun x =>
      1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N)).card := by
    have hr1_lt_N : r₁ < N := Nat.mod_lt _ hNpos
    have hr2_lt_N : r₂ < N := Nat.mod_lt _ hNpos
    let θ : Bool × Fin k → Fin (2 ^ L) := fun bm =>
      ⟨bm.2.1 * N + (if bm.1 then r₁ else r₂), by
        have hm1 : bm.2.1 + 1 ≤ k := bm.2.2
        have h1 : bm.2.1 * N + N ≤ k * N := by
          calc
            bm.2.1 * N + N = (bm.2.1 + 1) * N := by ring
            _ ≤ k * N := Nat.mul_le_mul_right N hm1
        have h2 : k * N ≤ 2 ^ L := Nat.div_mul_le_self (2 ^ L) N
        have hrlt : (if bm.1 then r₁ else r₂) < N := by
          cases bm.1 <;> simp [hr1_lt_N, hr2_lt_N]
        omega⟩
    have hmem : ∀ bm ∈ (Finset.univ : Finset (Bool × Fin k)),
        θ bm ∈ S_y.filter (fun x => 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N) := by
      intro ⟨b, m⟩ _
      rw [Finset.mem_filter, Finset.mem_filter]
      set r := if b then r₁ else r₂
      have hr_mod : r ^ 2 ≡ x' ^ 2 [MOD N] := by
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop_pq]
        cases b
        · refine ⟨?_, ?_⟩
          · have : Fact p.Prime := ⟨hp⟩
            rw [← ZMod.natCast_eq_natCast_iff]
            have h2p : (r₂ : ZMod p) = ((p - x' % p : ℕ) : ZMod p) :=
              (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr₂.2.1
            have hle : x' % p ≤ p := Nat.le_of_lt (Nat.mod_lt x' hp.pos)
            have hr_eq : r = r₂ := rfl
            rw [hr_eq, Nat.cast_pow, Nat.cast_pow, h2p, Nat.cast_sub hle, ZMod.natCast_self,
              zero_sub, ZMod.natCast_mod, neg_sq]
          · exact hr₂.2.2.pow 2
        · refine ⟨hr₁.2.1.pow 2, ?_⟩
          · have : Fact q.Prime := ⟨hq⟩
            rw [← ZMod.natCast_eq_natCast_iff]
            have h1q : (r₁ : ZMod q) = ((q - x' % q : ℕ) : ZMod q) :=
              (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr₁.2.2
            have hle : x' % q ≤ q := Nat.le_of_lt (Nat.mod_lt x' hq.pos)
            have hr_eq : r = r₁ := rfl
            rw [hr_eq, Nat.cast_pow, Nat.cast_pow, h1q, Nat.cast_sub hle, ZMod.natCast_self,
              zero_sub, ZMod.natCast_mod, neg_sq]
      have hsq_eq : (m.1 * N + r) ^ 2 % N = y := by
        rw [← hy, ← Nat.ModEq]
        have hadd : m.1 * N + r ≡ r [MOD N] := by
          rw [Nat.ModEq, add_comm, Nat.add_mul_mod_self_right]
        exact (hadd.pow 2).trans hr_mod
      have hgcd1 : Nat.gcd (m.1 * N + r) N = 1 := by
        have hr_lt : r < N := by dsimp only [r]; cases b <;> simp [hr1_lt_N, hr2_lt_N]
        have hgcd_eq : Nat.gcd (m.1 * N + r) N = Nat.gcd N r := by
          rw [Nat.gcd_comm, Nat.gcd_rec N (m.1 * N + r), add_comm, Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt hr_lt, Nat.gcd_comm]
        rw [hgcd_eq]
        by_contra hne
        have hdvd : Nat.gcd N r ∣ p * q := Nat.gcd_dvd_left N r
        have hgt1 : 1 < Nat.gcd N r :=
          Nat.lt_of_le_of_ne (Nat.gcd_pos_of_pos_left r hNpos) (Ne.symm hne)
        have hpr_or : p ∣ Nat.gcd N r ∨ q ∣ Nat.gcd N r := by
          by_cases hp_div : p ∣ Nat.gcd N r
          · exact Or.inl hp_div
          · have hcop_p : Nat.Coprime (Nat.gcd N r) p := (hp.coprime_iff_not_dvd.mpr hp_div).symm
            have hq_div : q ∣ Nat.gcd N r := by
              have hd := hcop_p.dvd_of_dvd_mul_left hdvd
              rcases (Nat.dvd_prime hq).mp hd with h1 | hq'
              · exact absurd h1 (by omega)
              · exact hq' ▸ dvd_rfl
            exact Or.inr hq_div
        rcases hpr_or with hp_div | hq_div
        · have hpr : p ∣ r := hp_div.trans (Nat.gcd_dvd_right N r)
          have hpx2 : p ∣ x' ^ 2 := by
            have hmod := hr_mod.of_dvd (dvd_mul_right p q)
            rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd (dvd_pow hpr (by norm_num))] at hmod
            exact Nat.dvd_of_mod_eq_zero hmod.symm
          exact hpx' (hp.dvd_of_dvd_pow hpx2)
        · have hqr : q ∣ r := hq_div.trans (Nat.gcd_dvd_right N r)
          have hqx2 : q ∣ x' ^ 2 := by
            have hmod := hr_mod.of_dvd (dvd_mul_left q p)
            rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd (dvd_pow hqr (by norm_num))] at hmod
            exact Nat.dvd_of_mod_eq_zero hmod.symm
          exact hqx' (hq.dvd_of_dvd_pow hqx2)
      refine ⟨⟨Finset.mem_univ _, hgcd1, hsq_eq⟩, ?_⟩
      cases b
      · -- `b = false`, `r = r₂`: `gcd (m * N + r₂ + x') N = p`
        have hpu : p ∣ m.1 * N + r₂ + x' := by
          have : Fact p.Prime := ⟨hp⟩
          rw [← ZMod.natCast_eq_zero_iff]
          have h2p : (r₂ : ZMod p) = ((p - x' % p : ℕ) : ZMod p) :=
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr₂.2.1
          have hle : x' % p ≤ p := Nat.le_of_lt (Nat.mod_lt x' hp.pos)
          have hNp : (N : ZMod p) = 0 := by simp [N]
          push_cast
          rw [h2p, Nat.cast_sub hle, ZMod.natCast_self, zero_sub, ZMod.natCast_mod,
            hNp, mul_zero, zero_add, neg_add_cancel]
        have hqu : ¬ q ∣ m.1 * N + r₂ + x' := by
          intro hdiv
          have : Fact q.Prime := ⟨hq⟩
          rw [← ZMod.natCast_eq_zero_iff] at hdiv
          have h2q : (r₂ : ZMod q) = (x' : ZMod q) :=
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr₂.2.2
          have hNq : (N : ZMod q) = 0 := by simp [N]
          push_cast at hdiv
          rw [h2q, hNq, mul_zero, zero_add] at hdiv
          have h2x : (2 : ZMod q) * (x' : ZMod q) = 0 := by
            calc
              (2 : ZMod q) * (x' : ZMod q) = (x' : ZMod q) + (x' : ZMod q) := by ring
              _ = 0 := hdiv
          have h20 : (2 : ZMod q) ≠ 0 := by
            intro h0
            have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h0
            have hle2 : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
            have hq2 := hq.two_le
            omega
          exact hqx' ((ZMod.natCast_eq_zero_iff x' q).mp ((mul_eq_zero.mp h2x).resolve_left h20))
        have hgcd_eq : Nat.gcd (m.1 * N + r₂ + x') N = p :=
          gcd_prime_mul_eq_left hp hq hpq hpu hqu
        change 1 < (m.1 * N + r₂ + x').gcd N ∧ (m.1 * N + r₂ + x').gcd N < N
        rw [hgcd_eq]
        exact ⟨desc.hp.one_lt, lt_mul_of_one_lt_right desc.hp.pos desc.hq.one_lt⟩
      · -- `b = true`, `r = r₁`: `gcd (m * N + r₁ + x') N = q`
        have hqu : q ∣ m.1 * N + r₁ + x' := by
          have : Fact q.Prime := ⟨hq⟩
          rw [← ZMod.natCast_eq_zero_iff]
          have h1q : (r₁ : ZMod q) = ((q - x' % q : ℕ) : ZMod q) :=
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr₁.2.2
          have hle : x' % q ≤ q := Nat.le_of_lt (Nat.mod_lt x' hq.pos)
          have hNq : (N : ZMod q) = 0 := by simp [N]
          push_cast
          rw [h1q, Nat.cast_sub hle, ZMod.natCast_self, zero_sub, ZMod.natCast_mod,
            hNq, mul_zero, zero_add, neg_add_cancel]
        have hpu : ¬ p ∣ m.1 * N + r₁ + x' := by
          intro hdiv
          have : Fact p.Prime := ⟨hp⟩
          rw [← ZMod.natCast_eq_zero_iff] at hdiv
          have h1p : (r₁ : ZMod p) = (x' : ZMod p) :=
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr₁.2.1
          have hNp : (N : ZMod p) = 0 := by simp [N]
          push_cast at hdiv
          rw [h1p, hNp, mul_zero, zero_add] at hdiv
          have h2x : (2 : ZMod p) * (x' : ZMod p) = 0 := by
            calc
              (2 : ZMod p) * (x' : ZMod p) = (x' : ZMod p) + (x' : ZMod p) := by ring
              _ = 0 := hdiv
          have h20 : (2 : ZMod p) ≠ 0 := by
            intro h0
            have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
            have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
            have hp2 := hp.two_le
            omega
          exact hpx' ((ZMod.natCast_eq_zero_iff x' p).mp ((mul_eq_zero.mp h2x).resolve_left h20))
        have hgcd_eq : Nat.gcd (m.1 * N + r₁ + x') N = q :=
          gcd_prime_mul_eq_right hp hq hpq hpu hqu
        change 1 < (m.1 * N + r₁ + x').gcd N ∧ (m.1 * N + r₁ + x').gcd N < N
        rw [hgcd_eq]
        exact ⟨desc.hq.one_lt, lt_mul_of_one_lt_left desc.hq.pos desc.hp.one_lt⟩
    have hinj : Set.InjOn θ (Finset.univ : Finset (Bool × Fin k)) := by
      intro ⟨b₁, m₁⟩ _ ⟨b₂, m₂⟩ _ heq
      have hval : m₁.1 * N + (if b₁ then r₁ else r₂) = m₂.1 * N + (if b₂ then r₁ else r₂) :=
        congrArg Fin.val heq
      have hr1_lt : (if b₁ then r₁ else r₂) < N := by cases b₁ <;> simp [hr1_lt_N, hr2_lt_N]
      have hr2_lt : (if b₂ then r₁ else r₂) < N := by cases b₂ <;> simp [hr1_lt_N, hr2_lt_N]
      have hdiv1 : (m₁.1 * N + (if b₁ then r₁ else r₂)) / N = m₁.1 := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hr1_lt,
          Nat.zero_add]
      have hdiv2 : (m₂.1 * N + (if b₂ then r₁ else r₂)) / N = m₂.1 := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hr2_lt,
          Nat.zero_add]
      have hm_eq : m₁.1 = m₂.1 := by rw [← hdiv1, ← hdiv2, hval]
      have hr_eq : (if b₁ then r₁ else r₂) = (if b₂ then r₁ else r₂) := by
        rw [hm_eq] at hval
        omega
      have hb_eq : b₁ = b₂ := by
        cases b₁ <;> cases b₂ <;> simp_all [hr_ne.symm]
      subst hb_eq
      ext <;> simp [hm_eq]
    have hcard := Finset.card_le_card_of_injOn θ hmem hinj
    simpa [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using hcard
  omega

/-- Success probability of `rabinInversionGame gen A n` is at most `3` times that of
`factoringGame gen (rabinToFactor A) n`. -/
theorem succProbability_rabinInversionGame_le (gen : BlumGen)
    (A : ℕ → ℕ × ℕ → ProbComp ℕ) (n : ℕ) :
    Game.succProbability (rabinInversionGame gen A n) ≤
      3 * Game.succProbability (factoringGame gen (rabinToFactor A) n) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_ofNat]
  have htop : (factoringGame gen (rabinToFactor A) n) true ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have h1 : ((rabinInversionGame gen A n) true).toNNReal.toReal =
      ((rabinInversionGame gen A n) true).toReal := rfl
  have h2 : ((factoringGame gen (rabinToFactor A) n) true).toNNReal.toReal =
      ((factoringGame gen (rabinToFactor A) n) true).toReal := rfl
  simp only [Game.succProbability]
  rw [h1, h2, ← ENNReal.toReal_ofNat 3, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) htop) ?_
  simp only [rabinInversionGame, factoringGame, rabinToFactor,
    ProbComp.eval_bind, BitString.eval_sampleList]
  simp only [Bind.bind, Pure.pure, PMF.bind_apply, PMF.pure_apply]
  simp_rw [eq_comm (a := true), decide_eq_true_eq]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun desc => ?_
  set N := desc.modulus
  set p := desc.p
  set q := desc.q
  set L := 2 * N.bits.length
  have hNpos : 0 < N := desc.modulus_pos
  have hL : N ≤ 2 ^ L / N := le_two_pow_two_mul_bits_length_div N hNpos
  let pdesc : ℝ≥0∞ := gen n desc
  change _ ≤ (3 : ℝ≥0∞) * (pdesc * _)
  rw [← mul_assoc, mul_comm (3 : ℝ≥0∞) pdesc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  simp only [tsum_uniformList_mul]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  let inv2L : ℝ≥0∞ := (2 ^ L : ℝ≥0∞)⁻¹
  change _ ≤ (3 : ℝ≥0∞) * (inv2L * _)
  rw [← mul_assoc, mul_comm (3 : ℝ≥0∞) inv2L, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  simp_rw [ofBits_ofFn_testBit L _ (Fin.isLt _)]
  -- Partition `Finset.univ` into `S_nontriv`, `S_zero`, `S_unit`
  let S_nontriv : Finset (Fin (2 ^ L)) :=
    Finset.univ.filter (fun x => 1 < Nat.gcd x.1 N ∧ Nat.gcd x.1 N < N)
  let S_zero : Finset (Fin (2 ^ L)) :=
    Finset.univ.filter (fun x => Nat.gcd x.1 N = N)
  let S_unit : Finset (Fin (2 ^ L)) :=
    Finset.univ.filter (fun x => Nat.gcd x.1 N = 1)
  have hN1 : 1 < N := one_lt_mul desc.hp.one_lt.le desc.hq.one_lt
  have hdisj_nz : Disjoint S_nontriv S_zero := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    omega
  have hdisj_nzu : Disjoint (S_nontriv ∪ S_zero) S_unit := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [S_nontriv, S_zero, S_unit, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and] at h1 h2
    omega
  have huniv : (Finset.univ : Finset (Fin (2 ^ L))) = (S_nontriv ∪ S_zero) ∪ S_unit := by
    ext x
    simp only [S_nontriv, S_zero, S_unit, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, true_iff]
    have h1 : 1 ≤ Nat.gcd x.1 N := Nat.gcd_pos_of_pos_right x.1 hNpos
    have h2 : Nat.gcd x.1 N ≤ N := Nat.le_of_dvd hNpos (Nat.gcd_dvd_right x.1 N)
    rcases eq_or_lt_of_le h1 with h1' | h1'
    · exact Or.inr h1'.symm
    · rcases eq_or_lt_of_le h2 with h2' | h2'
      · exact Or.inl (Or.inr h2')
      · exact Or.inl (Or.inl ⟨h1', h2'⟩)
  have htsum_finset : ∀ (s : Finset (Fin (2 ^ L))) (f : Fin (2 ^ L) → ℕ × ℕ → ℝ≥0∞),
      (∑' a, ∑ x ∈ s, f x a) = ∑ x ∈ s, ∑' a, f x a := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => simp [Finset.sum_insert hx, tsum_add, ih]
  simp_rw [huniv, Finset.sum_union hdisj_nzu, Finset.sum_union hdisj_nz,
    add_mul, tsum_add, mul_add]
  refine add_le_add ?_ ?_
  · -- Bound on `S_nontriv ∪ S_zero`
    have hlhs_le_one : ∀ x : Fin (2 ^ L),
        (∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
          if x' ^ 2 % N = rabinEval N x.1 then 1 else 0) ≤ 1 := by
      intro x
      calc
        (∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
            if x' ^ 2 % N = rabinEval N x.1 then 1 else 0)
            ≤ ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' * 1 := by
              refine tsum_le_tsum fun x' =>
                mul_le_mul_of_nonneg_left ?_ (by simp : (0 : ℝ≥0∞) ≤ _)
              split_ifs <;> simp
        _ = 1 := by simp [PMF.tsum_coe]
    have hlhs_nz : (∑ x ∈ S_nontriv, ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
          if x' ^ 2 % N = rabinEval N x.1 then 1 else 0) +
        (∑ x ∈ S_zero, ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
          if x' ^ 2 % N = rabinEval N x.1 then 1 else 0) ≤
        (S_nontriv.card : ℝ≥0∞) + (S_zero.card : ℝ≥0∞) := by
      refine add_le_add ?_ ?_
      · calc
          _ ≤ ∑ _x ∈ S_nontriv, (1 : ℝ≥0∞) := Finset.sum_le_sum fun x _ => hlhs_le_one x
          _ = S_nontriv.card := by simp
      · calc
          _ ≤ ∑ _x ∈ S_zero, (1 : ℝ≥0∞) := Finset.sum_le_sum fun x _ => hlhs_le_one x
          _ = S_zero.card := by simp
    have hcard_zn : S_zero.card ≤ S_nontriv.card := by
      have hq_lt : q < 2 ^ L := by
        have h1 : N ≤ 2 ^ L := le_trans hL (Nat.div_le_self _ _)
        have h2 : q < N := lt_mul_of_one_lt_left desc.hq.pos desc.hp.one_lt
        omega
      let φ : Fin (2 ^ L) → Fin (2 ^ L) := fun x =>
        if h : x.1 + p < 2 ^ L then ⟨x.1 + p, h⟩ else ⟨q, hq_lt⟩
      have hmem : ∀ x ∈ S_zero, φ x ∈ S_nontriv := by
        intro x hx
        simp only [S_zero, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hdvdN : N ∣ x.1 := Nat.gcd_eq_right_iff_dvd.mp hx
        simp only [S_nontriv, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hlt : x.1 + p < 2 ^ L
        · simp only [φ, hlt, ↓reduceDIte]
          have hpx : p ∣ x.1 := (dvd_mul_right p q).trans hdvdN
          have hqx : q ∣ x.1 := (dvd_mul_left q p).trans hdvdN
          have hpu : p ∣ x.1 + p := dvd_add hpx dvd_rfl
          have hqu : ¬ q ∣ x.1 + p := by
            intro hdiv
            have hqp : q ∣ p := (Nat.dvd_add_right hqx).mp hdiv
            rcases (Nat.dvd_prime desc.hp).mp hqp with hq1 | hqp'
            · exact desc.hq.ne_one hq1
            · exact desc.hpq hqp'.symm
          have hgcd : Nat.gcd (x.1 + p) N = p :=
            gcd_prime_mul_eq_left desc.hp desc.hq desc.hpq hpu hqu
          rw [hgcd]
          have hp3 := desc.three_le_p
          have hq3 := desc.three_le_q
          exact ⟨by omega, lt_mul_of_one_lt_right desc.hp.pos (by omega)⟩
        · simp only [φ, hlt, ↓reduceDIte]
          have hpu : ¬ p ∣ q := by
            intro hdiv
            rcases (Nat.dvd_prime desc.hq).mp hdiv with hp1 | hpq'
            · exact desc.hp.ne_one hp1
            · exact desc.hpq hpq'
          have hgcd : Nat.gcd q N = q :=
            gcd_prime_mul_eq_right desc.hp desc.hq desc.hpq hpu dvd_rfl
          rw [hgcd]
          have hp3 := desc.three_le_p
          have hq3 := desc.three_le_q
          exact ⟨by omega, lt_mul_of_one_lt_left desc.hq.pos (by omega)⟩
      have hinj : Set.InjOn φ S_zero := by
        intro x₁ hx₁ x₂ hx₂ heq
        simp only [S_zero, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        have hdvd1 : N ∣ x₁.1 := Nat.gcd_eq_right_iff_dvd.mp hx₁
        have hdvd2 : N ∣ x₂.1 := Nat.gcd_eq_right_iff_dvd.mp hx₂
        by_cases h1 : x₁.1 + p < 2 ^ L <;> by_cases h2 : x₂.1 + p < 2 ^ L
        · simp only [φ, h1, h2, ↓reduceDIte, Fin.mk.injEq] at heq
          ext; omega
        · simp only [φ, h1, h2, ↓reduceDIte, Fin.mk.injEq] at heq
          have hqx1 : q ∣ x₁.1 := (dvd_mul_left q p).trans hdvd1
          have hqp : q ∣ p := by
            have : x₁.1 + p = q := heq
            exact (Nat.dvd_add_right hqx1).mp (this ▸ dvd_rfl)
          rcases (Nat.dvd_prime desc.hp).mp hqp with hq1 | hqp'
          · exact absurd hq1 desc.hq.ne_one
          · exact absurd hqp'.symm desc.hpq
        · simp only [φ, h1, h2, ↓reduceDIte, Fin.mk.injEq] at heq
          have hqx2 : q ∣ x₂.1 := (dvd_mul_left q p).trans hdvd2
          have hqp : q ∣ p := by
            have : q = x₂.1 + p := heq
            exact (Nat.dvd_add_right hqx2).mp (this ▸ dvd_rfl)
          rcases (Nat.dvd_prime desc.hp).mp hqp with hq1 | hqp'
          · exact absurd hq1 desc.hq.ne_one
          · exact absurd hqp'.symm desc.hpq
        · rcases hdvd1 with ⟨m₁, hm₁⟩
          rcases hdvd2 with ⟨m₂, hm₂⟩
          have hpN : p < N := lt_mul_of_one_lt_right desc.hp.pos (by have := desc.three_le_q; omega)
          have hm_eq : m₁ = m₂ := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have : m₁ + 1 ≤ m₂ := hlt
              have : N * m₁ + N ≤ N * m₂ := by nlinarith
              omega
            · have : m₂ + 1 ≤ m₁ := hgt
              have : N * m₂ + N ≤ N * m₁ := by nlinarith
              omega
          ext
          rw [hm₁, hm₂, hm_eq]
      exact Finset.card_le_card_of_injOn φ hmem hinj
    have hrhs_n : (S_nontriv.card : ℝ≥0∞) ≤
        ∑ x ∈ S_nontriv, ∑' ab : ℕ × ℕ,
          (ProbComp.eval (if 1 < Nat.gcd x.1 N ∧ Nat.gcd x.1 N < N then
            pure (rabinFactorPair x.1 N)
          else do
            let x' ← A n (N, rabinEval N x.1)
            pure (rabinFactorPair (x.1 + x') N))) ab *
          if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = N then 1 else 0 := by
      have h1 : (S_nontriv.card : ℝ≥0∞) = ∑ _x ∈ S_nontriv, (1 : ℝ≥0∞) := by simp
      rw [h1]
      refine Finset.sum_le_sum fun x hx => ?_
      simp only [S_nontriv, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [hx.1, hx.2, and_self, ↓reduceIte, ProbComp.eval_pure, PMF.pure_apply]
      rw [tsum_eq_single (rabinFactorPair x.1 N) (fun ab hab => by simp [hab])]
      have hgood := rabinFactorPair_good hx.1 hx.2
      simp [hgood]
    simp_rw [Finset.sum_mul, htsum_finset]
    calc
      (∑ x ∈ S_nontriv, _) + (∑ x ∈ S_zero, _)
          ≤ (S_nontriv.card : ℝ≥0∞) + (S_zero.card : ℝ≥0∞) := hlhs_nz
      _ ≤ (S_nontriv.card : ℝ≥0∞) + (S_nontriv.card : ℝ≥0∞) := by
          exact add_le_add_right (Nat.cast_le.mpr hcard_zn) _
      _ ≤ 3 * (S_nontriv.card : ℝ≥0∞) := by
          have htwo : (S_nontriv.card : ℝ≥0∞) + (S_nontriv.card : ℝ≥0∞) =
              2 * (S_nontriv.card : ℝ≥0∞) := by
            ring
          rw [htwo]
          exact mul_le_mul_of_nonneg_right (by norm_num) (by simp)
      _ ≤ 3 * (∑ x ∈ S_nontriv, _) := mul_le_mul_of_nonneg_left hrhs_n (by simp)
      _ ≤ 3 * (∑ x ∈ S_nontriv, _) + 3 * (∑ x ∈ S_zero, _) := le_self_add
  · -- Bound on `S_unit`
    have hrhs_unit : (∑ x ∈ S_unit, ∑' ab : ℕ × ℕ,
        (ProbComp.eval (if 1 < Nat.gcd x.1 N ∧ Nat.gcd x.1 N < N then
          PFunctor.FreeM.pure (rabinFactorPair x.1 N)
        else
          PFunctor.FreeM.bind (A n (N, rabinEval N x.1)) fun x' =>
            PFunctor.FreeM.pure (rabinFactorPair (x.1 + x') N))) ab *
        if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = N then 1 else 0) =
        ∑ x ∈ S_unit, ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
          if 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N then 1 else 0 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [S_unit, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hnot : ¬ (1 < Nat.gcd x.1 N ∧ Nat.gcd x.1 N < N) := by omega
      simp only [hnot, ↓reduceIte]
      change (∑' ab : ℕ × ℕ, (ProbComp.eval ((A n (N, rabinEval N x.1)) >>= fun x' =>
        pure (rabinFactorPair (x.1 + x') N))) ab *
        if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = N then 1 else 0) = _
      rw [ProbComp.eval_bind]
      simp only [ProbComp.eval_pure, PMF.bind_apply, PMF.pure_apply]
      simp_rw [← ENNReal.tsum_mul_right]
      rw [tsum_comm]
      refine tsum_congr fun x' => ?_
      have hpull : (∑' a : ℕ × ℕ,
          ((ProbComp.eval (A n (N, rabinEval N x.1))) x' *
            @ite ℝ≥0∞ (a = rabinFactorPair (x.1 + x') N) (Classical.propDecidable _) 1 0) *
          if 1 < a.1 ∧ 1 < a.2 ∧ a.1 * a.2 = N then 1 else 0) =
          (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
          ∑' a : ℕ × ℕ,
            (@ite ℝ≥0∞ (a = rabinFactorPair (x.1 + x') N) (Classical.propDecidable _) 1 0) *
            if 1 < a.1 ∧ 1 < a.2 ∧ a.1 * a.2 = N then 1 else 0 := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun a => ?_
        ring
      refine hpull.trans ?_
      rw [tsum_eq_single (rabinFactorPair (x.1 + x') N) (fun ab hab => by simp [hab])]
      simp only [↓reduceIte, one_mul]
      by_cases hgood : 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N
      · have hp := rabinFactorPair_good hgood.1 hgood.2
        simp [hgood, hp]
      · have hnot' : ¬ (1 < (rabinFactorPair (x.1 + x') N).1 ∧
            1 < (rabinFactorPair (x.1 + x') N).2 ∧
            (rabinFactorPair (x.1 + x') N).1 * (rabinFactorPair (x.1 + x') N).2 = N) := by
          intro ⟨h1, h2, h3⟩
          dsimp only [rabinFactorPair] at h1 h2 h3
          have hlt : Nat.gcd (x.1 + x') N < N := by
            by_contra hge
            have heq : Nat.gcd (x.1 + x') N = N :=
              le_antisymm (Nat.le_of_dvd hNpos (Nat.gcd_dvd_right _ _)) (by omega)
            rw [heq, Nat.div_self hNpos] at h2
            omega
          exact hgood ⟨h1, hlt⟩
        simp [hgood, hnot']
    simp_rw [Finset.sum_mul, htsum_finset]
    trans (3 : ℝ≥0∞) * ∑ x ∈ S_unit, ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
        if 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N then 1 else 0
    · -- Group `S_unit` by `y : Fin N`
      have hfib_lhs : (∑ x ∈ S_unit, ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
          if x' ^ 2 % N = rabinEval N x.1 then 1 else 0) =
          ∑ y : Fin N, ∑ x ∈ S_unit.filter
              (fun x => (⟨rabinEval N x.1, Nat.mod_lt _ hNpos⟩ : Fin N) = y),
            ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
              if x' ^ 2 % N = rabinEval N x.1 then 1 else 0 := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (g := fun x : Fin (2 ^ L) => (⟨rabinEval N x.1, Nat.mod_lt _ hNpos⟩ : Fin N))
          (fun _ _ => Finset.mem_univ _)]
      have hfib_rhs : (∑ x ∈ S_unit, ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
          if 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N then 1 else 0) =
          ∑ y : Fin N, ∑ x ∈ S_unit.filter
              (fun x => (⟨rabinEval N x.1, Nat.mod_lt _ hNpos⟩ : Fin N) = y),
            ∑' x' : ℕ, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
              if 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N then 1 else 0 := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (g := fun x : Fin (2 ^ L) => (⟨rabinEval N x.1, Nat.mod_lt _ hNpos⟩ : Fin N))
          (fun _ _ => Finset.mem_univ _)]
      rw [hfib_lhs, hfib_rhs, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      set S_y := S_unit.filter (fun x => (⟨rabinEval N x.1, Nat.mod_lt _ hNpos⟩ : Fin N) = y)
      have hS_y_eq : S_y = Finset.univ.filter (fun x : Fin (2 ^ L) =>
          Nat.gcd x.1 N = 1 ∧ x.1 ^ 2 % N = y.1) := by
        ext x
        simp only [S_y, S_unit, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff,
          rabinEval]
      have htsum_nat : ∀ (s : Finset (Fin (2 ^ L))) (f : Fin (2 ^ L) → ℕ → ℝ≥0∞),
          (∑' a, ∑ x ∈ s, f x a) = ∑ x ∈ s, ∑' a, f x a := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | insert x s hx ih => simp [Finset.sum_insert hx, tsum_add, ih]
      rw [← htsum_nat, ← htsum_nat, ← ENNReal.tsum_mul_left]
      refine tsum_le_tsum fun x' => ?_
      by_cases hy : x' ^ 2 % N = y.1
      · have hlhs_y : (∑ x ∈ S_y, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
            if x' ^ 2 % N = rabinEval N x.1 then 1 else 0) =
            (ProbComp.eval (A n (N, y.1))) x' * (S_y.card : ℝ≥0∞) := by
          have hcongr : (∑ x ∈ S_y, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
              if x' ^ 2 % N = rabinEval N x.1 then 1 else 0) =
              ∑ _x ∈ S_y, (ProbComp.eval (A n (N, y.1))) x' := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hxy : rabinEval N x.1 = y.1 := congrArg Fin.val (Finset.mem_filter.mp hx).2
            rw [hxy, hy]
            simp
          rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_comm]
        have hrhs_y : (3 : ℝ≥0∞) * (∑ x ∈ S_y, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
            if 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N then 1 else 0) =
            (ProbComp.eval (A n (N, y.1))) x' *
              ((3 * (S_y.filter (fun x => 1 < Nat.gcd (x.1 + x') N ∧
                Nat.gcd (x.1 + x') N < N)).card : ℕ) : ℝ≥0∞) := by
          have hcongr : (∑ x ∈ S_y, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
              if 1 < Nat.gcd (x.1 + x') N ∧ Nat.gcd (x.1 + x') N < N then 1 else 0) =
              (ProbComp.eval (A n (N, y.1))) x' *
                ((S_y.filter (fun x => 1 < Nat.gcd (x.1 + x') N ∧
                  Nat.gcd (x.1 + x') N < N)).card : ℝ≥0∞) := by
            have hmul_ite : ∀ (a : ℝ≥0∞) (P : Prop) [Decidable P],
                a * (if P then 1 else 0) = if P then a else 0 := fun a P _ => by
              split_ifs <;> simp
            simp_rw [hmul_ite, ← Finset.sum_filter]
            have hcongr' : (∑ x ∈ S_y.filter (fun x => 1 < Nat.gcd (x.1 + x') N ∧
                Nat.gcd (x.1 + x') N < N),
                (ProbComp.eval (A n (N, rabinEval N x.1))) x') =
                ∑ _x ∈ S_y.filter (fun x => 1 < Nat.gcd (x.1 + x') N ∧
                  Nat.gcd (x.1 + x') N < N),
                  (ProbComp.eval (A n (N, y.1))) x' := by
              refine Finset.sum_congr rfl fun x hx => ?_
              have hx1 := (Finset.mem_filter.mp hx).1
              have hxy : rabinEval N x.1 = y.1 := congrArg Fin.val (Finset.mem_filter.mp hx1).2
              rw [hxy]
            rw [hcongr', Finset.sum_const, nsmul_eq_mul, mul_comm]
          rw [hcongr, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [hlhs_y, hrhs_y]
        refine mul_le_mul_of_nonneg_left ?_ (by simp)
        rw [hS_y_eq]
        exact Nat.cast_le.mpr (blum_rabin_fiber_card_le hL hy)
      · have hlhs_zero : (∑ x ∈ S_y, (ProbComp.eval (A n (N, rabinEval N x.1))) x' *
            if x' ^ 2 % N = rabinEval N x.1 then 1 else 0) = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxy : rabinEval N x.1 = y.1 := congrArg Fin.val (Finset.mem_filter.mp hx).2
          rw [hxy]
          simp [hy]
        rw [hlhs_zero]
        simp
    · exact le_of_eq (congrArg (fun z => (3 : ℝ≥0∞) * z) hrhs_unit.symm)

/-- If factoring is hard for `gen`, then Rabin squaring is one-way for `gen`. -/
theorem rabinOneWay_of_factoringHard {gen : BlumGen} (h : FactoringHard gen) :
    RabinOneWay gen := by
  intro A hA d
  have hle : ∀ n, Game.succProbability (rabinInversionGame gen A n) ≤
      3 * Game.succProbability (factoringGame gen (rabinToFactor A) n) :=
    succProbability_rabinInversionGame_le gen A
  have h3 : Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ≥0) ^ d * (3 * Game.succProbability (factoringGame gen (rabinToFactor A) n)))
      Filter.atTop (nhds 0) := by
    have hmul : (fun n : ℕ => (n : ℝ≥0) ^ d *
        (3 * Game.succProbability (factoringGame gen (rabinToFactor A) n))) =
        fun n : ℕ =>
          3 * ((n : ℝ≥0) ^ d * Game.succProbability (factoringGame gen (rabinToFactor A) n)) := by
      ext n
      exact congrArg NNReal.toReal (mul_left_comm ((n : ℝ≥0) ^ d) 3 _)
    rw [hmul]
    simpa using (h (rabinToFactor A) (isPPTOn_rabinToFactor hA) d).const_mul 3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ≥0)) Filter.atTop (nhds 0)) h3
    (by intro n; simp)
    (by intro n; exact mul_le_mul_of_nonneg_left (hle n) (by simp))

/-- Equivalence of Rabin one-wayness and integer factoring hardness for Blum modulus generators. -/
theorem rabinOneWay_iff_factoringHard (gen : BlumGen) :
    RabinOneWay gen ↔ FactoringHard gen :=
  ⟨factoringHard_of_rabinOneWay, rabinOneWay_of_factoringHard⟩

end Cslib.Crypto

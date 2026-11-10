/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Paillier
import CslibFrontier.Crypto.Game.FourHop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.UnitSampling
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformSubset
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.Uniform

/-!
# Paillier encryption is IND-CPA secure under DCR

[KatzLindell2020], Theorem 15.13: if the decisional composite residuosity problem is hard relative
to the modulus generator, Paillier encryption is CPA-secure. We prove this for
`Paillier.keyGen` and `Paillier.encrypt` with the strict-PPT game `Encryption.INDCPAOn`.

For a chosen-message adversary `A` and a challenge bit `b`, the distinguisher
`dcrDistinguisher A b` on input `(N, y)` runs `A` on the public key `N` and, for an admissible
pair, answers with `(1 + N) ^ m_b * y mod N ^ 2`, as in the book's proof. The proof has four
hops:

1. The real IND-CPA experiment for bit `b` is within `5 / 2 ^ n` of the DCR real game of
   `dcrDistinguisher A b`. In the DCR real game `y = s ^ N` for `s` uniform in
   `(ZMod (N ^ 2))ˣ`, and `s ^ N` depends only on `s mod N`; reduction modulo `N` pushes the
   uniform law on `(ZMod (N ^ 2))ˣ` to the uniform law on `(ZMod N)ˣ`. The encryption
   randomness is `unitOrOne N r` for `r` from `ProbComp.sampleModNat`, which is within
   `N / 2 ^ (n + |N|) + (N - φ(N)) / N` of uniform on the units.
2. The DCR real and ideal games of `dcrDistinguisher A b` differ by its DCR advantage.
3. The DCR ideal games for `b = false` and `b = true` are equal: multiplying a uniform unit by
   the unit `(1 + N) ^ m` gives a uniform unit, whatever `m` is.
4. Hops 1 and 2 again, for the other bit.

The book's encryption samples `r` uniformly from `ℤ*_N`. Our encryption samples from
`ProbComp.sampleModNat` and replaces a non-unit by `1`; the extra statistical distance
`(N - φ(N)) / N ≤ 1 / p + 1 / q` is negligible only when the primes grow with `n`. This is the
hypothesis `hsize` of `DCR.indcpaOn_paillier`: every modulus the generator outputs at parameter
`n` has primes of at least `n` bits, as in the book's `GenModulus`.

## Main results

* `Cslib.Crypto.Paillier.isPPTOn_dcrDistinguisher`: the reduction distinguishers are uniform
  strict PPT.
* `Cslib.Crypto.Paillier.DCR.indcpaOn_paillier`: DCR implies IND-CPA security of Paillier
  encryption ([KatzLindell2020], Theorem 15.13, with the hypothesis `hsize`).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Chapter 15,
  Theorem 15.13.
-/

@[expose] public section

namespace Cslib.Crypto.Paillier

open Probability Turing.MultiTapeTM BalancedModulus Encryption
open scoped ENNReal NNReal Cslib.Probability.PMF

/-- Admissible challenge pairs: both messages are below the modulus `N` of the public key. -/
def validMessages (_n : ℕ) (pk : List Bool) (m₀ m₁ : ℕ) : Bool :=
  decide (m₀ < ofBits pk ∧ m₁ < ofBits pk)

/-- The DCR distinguisher built from a chosen-message adversary and a challenge bit: on `(N, y)`,
it runs the adversary on the public key `N` and answers its challenge with
`(1 + N) ^ m * y mod N ^ 2` ([KatzLindell2020], proof of Theorem 15.13). -/
noncomputable def dcrDistinguisher (adversary : AdversaryOf ℕ) (bit : Bool) (n : ℕ)
    (input : ℕ × ℕ) : ProbComp Bool := do
  let choice ← adversary.choose n (encNat input.1)
  if validMessages n (encNat input.1) (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let m := if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice
    adversary.guess n (ChoiceOut.state choice)
      (encNat (powMod (input.1 ^ 2) (1 + input.1) m * input.2 % input.1 ^ 2))
  else
    return false

/-- The reduction distinguishers are uniform strict PPT. -/
theorem isPPTOn_dcrDistinguisher {adversary : AdversaryOf ℕ} (hA : adversary.IsPPT encNat)
    (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
      (fun input => dcrDistinguisher adversary bit input.1 input.2) := by
  let EIn := encPair encUnary (encPair encNat encNat)
  let EChoice := encPair (encPair encNat encNat) encBits
  have hin2 := ComputableInPolyTime.snd encUnary (encPair encNat encNat)
  have hN_in := (ComputableInPolyTime.fst encNat encNat).comp hin2
  have hp1 := ComputableInPolyTime.fst EIn EChoice
  have hp2 := ComputableInPolyTime.snd EIn EChoice
  have hn := (ComputableInPolyTime.fst encUnary (encPair encNat encNat)).comp hp1
  have hN := hN_in.comp hp1
  have hy := ((ComputableInPolyTime.snd encNat encNat).comp hin2).comp hp1
  have hmsgs := (ComputableInPolyTime.fst (encPair encNat encNat) encBits).comp hp2
  have hst := (ComputableInPolyTime.snd (encPair encNat encNat) encBits).comp hp2
  have hm0 := (ComputableInPolyTime.fst encNat encNat).comp hmsgs
  have hm1 := (ComputableInPolyTime.snd encNat encNat).comp hmsgs
  have hm : ComputableInPolyTime
      (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) × List Bool => if bit then p.2.1.2 else p.2.1.1)
      (encPair EIn EChoice) encNat := by
    cases bit
    · exact hm0
    · exact hm1
  have hN2 := computableInPolyTime_sq hN
  have hpow := computableInPolyTime_powMod hN2
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.binary_add'
      (ComputableTidilyInPolyTime.const 1) hN.tidy)) hm
  have hct := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.binary_mod'
    (ComputableTidilyInPolyTime.binary_mul' hpow.tidy hy.tidy) hN2.tidy)
  have hvalidStep : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) × List Bool =>
        validMessages p.1.1 (encNat p.1.2.1) p.2.1.1 p.2.1.2) (encPair EIn EChoice) encBool := by
    simpa only [validMessages, ofBits_encNat, Function.comp_def] using
      ComputableTidilyInPolyTime.decide_and
        (ComputableTidilyInPolyTime.binary_lt' hm0.tidy hN.tidy)
        (ComputableTidilyInPolyTime.binary_lt' hm1.tidy hN.tidy)
  have hguessStep := hA.guess.preprocess
    (prepare := fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) × List Bool =>
      (p.1.1, p.2.2, encNat (powMod (p.1.2.1 ^ 2) (1 + p.1.2.1)
        (if bit then p.2.1.2 else p.2.1.1) * p.1.2.2 % p.1.2.1 ^ 2)))
    (hn.prod (hst.prod hct.encoding_comp))
  unfold dcrDistinguisher
  refine (hA.choose.on.preprocess
    (prepare := fun input : ℕ × ℕ × ℕ => (input.1, encNat input.2.1))
    ((ComputableInPolyTime.fst encUnary (encPair encNat encNat)).prod
      hN_in.encoding_comp)).bind_with ?_
  exact IsPPTOn.cond hvalidStep hguessStep (ComputableTidilyInPolyTime.const false).isPPTOn

/-! ### Algebra of the reduction -/

private theorem eq_of_natCast_eq_of_lt {M a b : ℕ} (ha : a < M) (hb : b < M)
    (h : (a : ZMod M) = (b : ZMod M)) : a = b := by
  rw [← ZMod.val_cast_of_lt ha, ← ZMod.val_cast_of_lt hb, h]

/-- Multiplying the challenge `y = r` by `(1 + N) ^ m` is multiplication by a unit. -/
private theorem powMod_mul_val_eq (N : ℕ) [NeZero N] (m : ℕ) (r : (ZMod (N ^ 2))ˣ) :
    powMod (N ^ 2) (1 + N) m * (r : ZMod (N ^ 2)).val % N ^ 2 =
      ((oneAddUnit N ^ m * r : (ZMod (N ^ 2))ˣ) : ZMod (N ^ 2)).val := by
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 (NeZero.ne N)
  have h : ((powMod (N ^ 2) (1 + N) m * (r : ZMod (N ^ 2)).val % N ^ 2 : ℕ) : ZMod (N ^ 2)) =
      ((oneAddUnit N ^ m * r : (ZMod (N ^ 2))ˣ) : ZMod (N ^ 2)) := by
    simp only [powMod_of_ne_zero hN2, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, ZMod.natCast_zmod_val, Units.val_mul, Units.val_pow_eq_pow_val,
      coe_oneAddUnit]
  rw [← h, ZMod.val_natCast, Nat.mod_mod]

/-- With `y = s ^ N`, the distinguisher's challenge is the Paillier ciphertext of `m` with
randomness `s mod N`. -/
private theorem powMod_mul_val_pow_eq_ciphertext (N : ℕ) [NeZero N] (m : ℕ)
    (s : (ZMod (N ^ 2))ˣ) :
    powMod (N ^ 2) (1 + N) m * ((s ^ N : (ZMod (N ^ 2))ˣ) : ZMod (N ^ 2)).val % N ^ 2 =
      ciphertext N m (unitOrOne N
        ((ZMod.unitsMap (dvd_pow_self N two_ne_zero) s : ZMod N)).val) := by
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 (NeZero.ne N)
  have hcop : Nat.gcd ((ZMod.unitsMap (dvd_pow_self N two_ne_zero) s : ZMod N)).val N = 1 :=
    ZMod.val_coe_unit_coprime _
  simp only [unitOrOne, hcop, ↓reduceIte]
  refine eq_of_natCast_eq_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hN2)) ?_ ?_
  · unfold ciphertext
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero hN2)
  · rw [natCast_ciphertext (NeZero.ne N), ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast,
      ← ZMod.natCast_pow_self_mod, ZMod.natCast_zmod_val]
    simp only [powMod_of_ne_zero hN2, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, ZMod.natCast_zmod_val, Units.val_pow_eq_pow_val]

/-! ### Distributions -/

/-- Reduction modulo `N` sends the uniform unit modulo `N ^ 2` to the uniform unit modulo `N`. -/
private theorem uniformOfFintype_map_unitsMap (N : ℕ) [NeZero N] :
    (PMF.uniformOfFintype (ZMod (N ^ 2))ˣ).map (ZMod.unitsMap (dvd_pow_self N two_ne_zero)) =
      PMF.uniformOfFintype (ZMod N)ˣ := by
  rw [← Probability.PMF.uniformOfFintype_map_equiv
      (Additive.toMul : Additive (ZMod (N ^ 2))ˣ ≃ (ZMod (N ^ 2))ˣ), PMF.map_comp,
    ← Probability.PMF.uniformOfFintype_map_equiv
      (Additive.toMul : Additive (ZMod N)ˣ ≃ (ZMod N)ˣ),
    ← Probability.PMF.uniformOfFintype_map_addHom
      (MonoidHom.toAdditive (ZMod.unitsMap (dvd_pow_self N two_ne_zero)))
      (ZMod.unitsMap_surjective _), PMF.map_comp]
  rfl

/-! ### The hops -/

/-- Ingredient of the proof of [KatzLindell2020], Theorem 15.13: once the adversary has chosen
its messages, encrypting `m` is within `5 / 2 ^ n` of answering with `(1 + N) ^ m * s ^ N` for a
uniform unit `s`, for a modulus with `n`-bit primes. -/
private theorem advantage_encrypt_dcrReal_le (d : Desc) (n : ℕ)
    (hsize : n ≤ d.p.size ∧ n ≤ d.q.size) (adversary : AdversaryOf ℕ) (state : List Bool)
    (m : ℕ) :
    Game.advantage
      ((ProbComp.eval (ProbComp.sampleModNat (n + (encNat d.modulus).length) d.modulus)).bind
        fun r => ProbComp.eval (adversary.guess n state
          (encNat (ciphertext d.modulus m (unitOrOne d.modulus r)))))
      ((PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ).bind fun s =>
        ProbComp.eval (adversary.guess n state
          (encNat (powMod (d.modulus ^ 2) (1 + d.modulus) m *
            ((s ^ d.modulus : (ZMod (d.modulus ^ 2))ˣ) : ZMod (d.modulus ^ 2)).val %
              d.modulus ^ 2)))) ≤
      5 / 2 ^ n := by
  let K : ℕ → Game := fun x => ProbComp.eval (adversary.guess n state
    (encNat (ciphertext d.modulus m (unitOrOne d.modulus x))))
  have hreal : ((PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ).bind fun s =>
        ProbComp.eval (adversary.guess n state
          (encNat (powMod (d.modulus ^ 2) (1 + d.modulus) m *
            ((s ^ d.modulus : (ZMod (d.modulus ^ 2))ˣ) : ZMod (d.modulus ^ 2)).val %
              d.modulus ^ 2)))) =
      (PMF.uniformOfFintype (ZMod d.modulus)ˣ).bind fun u => K (u : ZMod d.modulus).val := by
    rw [← uniformOfFintype_map_unitsMap d.modulus, PMF.bind_map]
    refine congrArg _ (funext fun s => ?_)
    simp only [Function.comp_apply, K]
    rw [powMod_mul_val_pow_eq_ciphertext]
  rw [hreal]
  exact Game.advantage_sampleModNat_units_le d.2.prime_fst d.2.prime_snd d.2.fst_ne_snd
    hsize.1 hsize.2 K

/-- Ingredient of the proof of [KatzLindell2020], Theorem 15.13 (the case `y = r ^ N`): the
IND-CPA experiment for challenge bit `b` is within `5 / 2 ^ n` of the DCR real game of
`dcrDistinguisher adversary b`, for generators whose primes have at least `n` bits. -/
private theorem advantage_gameOn_dcrRealGame_le {gen : ℕ → ProbComp Desc}
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (adversary : AdversaryOf ℕ) (bit : Bool) (n : ℕ) :
    Game.advantage (ProbComp.eval (gameOn validMessages (keyGen gen) encrypt adversary bit n))
      (dcrRealGame (fun n => ProbComp.eval (gen n)) (dcrDistinguisher adversary bit) n) ≤
      5 / 2 ^ n := by
  simp only [gameOn, keyGen, encrypt, dcrRealGame, dcrDistinguisher, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.bind_bind,
    PMF.pure_bind, apply_ite ProbComp.eval, ofBits_encNat, ChoiceOut.msg₀, ChoiceOut.msg₁,
    ChoiceOut.msgs]
  refine Game.advantage_bind_le_of_support _ _ _ fun d hd => ?_
  rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ)]
  refine Game.advantage_bind_le_nnreal _ _ _ fun choice => ?_
  by_cases hv : validMessages n (encNat d.modulus) choice.1.1 choice.1.2 = true
  · simp only [hv, ↓reduceIte]
    exact advantage_encrypt_dcrReal_le d n (hsize n d hd) adversary choice.2 _
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, PMF.bind_const, Game.advantage_self, zero_le]

/-- Ingredient of the proof of [KatzLindell2020], Theorem 15.13 (the case `y` uniform): the DCR
ideal games of the two reduction distinguishers are equal. -/
private theorem dcrIdealGame_dcrDistinguisher_false_eq_true (setup : ℕ → PMF Desc)
    (adversary : AdversaryOf ℕ) (n : ℕ) :
    dcrIdealGame setup (dcrDistinguisher adversary false) n =
      dcrIdealGame setup (dcrDistinguisher adversary true) n := by
  simp only [dcrIdealGame, dcrDistinguisher, ProbComp.eval_bind, PMF.monad_bind_eq_bind,
    apply_ite ProbComp.eval, ProbComp.eval_pure, Bool.false_eq_true,
    ↓reduceIte]
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ)]
  refine congrArg (PMF.bind _) (funext fun choice => ?_)
  have key (m : ℕ) : ((PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ).bind fun r =>
        ProbComp.eval (adversary.guess n choice.2
          (encNat (powMod (d.modulus ^ 2) (1 + d.modulus) m * (r : ZMod (d.modulus ^ 2)).val %
            d.modulus ^ 2)))) =
      (PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ).bind fun u =>
        ProbComp.eval (adversary.guess n choice.2 (encNat (u : ZMod (d.modulus ^ 2)).val)) := by
    simp only [powMod_mul_val_eq]
    conv_rhs => rw [← Probability.PMF.uniformOfFintype_map_equiv
      (Equiv.mulLeft (oneAddUnit d.modulus ^ m))]
    rw [PMF.bind_map]
    rfl
  by_cases hv : validMessages n (encNat d.modulus) choice.1.1 choice.1.2 = true
  · simp only [hv, ↓reduceIte]
    rw [key, key]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]

/-- **Paillier encryption is IND-CPA secure under DCR** ([KatzLindell2020], Theorem 15.13): if
the decisional composite residuosity problem is hard relative to the generator's law, then
`(keyGen gen, encrypt)` satisfies `Encryption.INDCPAOn validMessages encNat`. The hypothesis
`hsize` (primes of at least `n` bits) makes the statistical distance between our encryption
randomness and a uniform unit of `ZMod N` negligible; the book's encryption samples a uniform
unit directly and needs no such hypothesis. -/
theorem DCR.indcpaOn_paillier {gen : ℕ → ProbComp Desc}
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hDCR : DCR fun n => ProbComp.eval (gen n)) :
    INDCPAOn validMessages encNat (keyGen gen) encrypt := by
  intro adversary hA
  have hD (bit : Bool) := hDCR (dcrDistinguisher adversary bit) (isPPTOn_dcrDistinguisher hA bit)
  have hmid : Negligible fun n => Game.advantage
      (dcrRealGame (fun n => ProbComp.eval (gen n)) (dcrDistinguisher adversary false) n)
      (dcrRealGame (fun n => ProbComp.eval (gen n)) (dcrDistinguisher adversary true) n) := by
    refine negligible_of_le ((hD false).add (hD true)) fun n => ?_
    dsimp only [Pi.add_apply]
    refine (Game.advantage_triangle _
      (dcrIdealGame (fun n => ProbComp.eval (gen n)) (dcrDistinguisher adversary false) n)
      _).trans (add_le_add le_rfl ?_)
    rw [dcrIdealGame_dcrDistinguisher_false_eq_true]
    exact (Game.advantage_comm _ _).le
  have h5 : Negligible fun n => (5 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 5
  refine negligible_of_le ((h5.add hmid).add h5) fun n => ?_
  dsimp only [Pi.add_apply]
  exact Game.advantage_four_hop_le (advantage_gameOn_dcrRealGame_le hsize adversary false n)
    (advantage_gameOn_dcrRealGame_le hsize adversary true n)

end Cslib.Crypto.Paillier

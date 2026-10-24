/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Circuit.Boolean.HardnessAmplification
public import Complexity.Computability.Languages.Slice
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Circuit.Boolean.Substitution
import Complexity.Computability.Complexity.Classes.BPP.Derandomization.Generator
import Complexity.Foundations.Data.Nat.PolynomialBound.Log
import Complexity.Tactic.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Derandomizing BPP from average-case hardness

**Hardness versus randomness** [NisanWigderson1994]: if some problem in `E`, decidable in time
`2 ^ O(n)`, is average-case hard for circuits of size `2 ^ (n / c)`, then `BPP = P`
[Arora and Barak, Chapter 20][AroraBarak09]. Here the hardness is
`Cslib.Circuits.Boolean.IsAverageCaseHard` for nonuniform De Morgan circuits, with the non-strict
bound produced by Yao's XOR lemma, and the conclusion is uniform: every problem in `BPP enc` is in
`P enc`, for every encoding `enc` of instances (`BPP_subset_P_of_isAverageCaseHard`), so
`P enc = BPP enc` (`P_eq_BPP_of_isAverageCaseHard`). A hardness `2 ^ (ε n)` for a real `ε > 0`
gives the hypothesis for every natural `c ≥ 1 / ε`, by
`Cslib.Circuits.Boolean.IsAverageCaseHard.mono`.

The deterministic algorithm is `Cslib.Complexity.nwDecider`. On an instance of length `N` it sets
`t = t₀ + e (⌊log₂ N⌋ + 1)` for constants `t₀` and `e`, and runs the verifier on the output of the
Nisan–Wigderson generator for all `2 ^ ℓ` seeds of `ℓ = (2 ^ (8 c + 1) + 1) t` bits, taking the
majority. The generator uses the greedy design (`Cslib.Crypto.PRG.NisanWigderson.Design.greedy`)
with blocks of `n = 4 c t` positions sharing at most `t - 1` of them, and the hard function on `n`
bits, evaluated in time `2 ^ O(n)`. Both `2 ^ ℓ` and `2 ^ O(n)` are polynomial in `N`, so the
algorithm runs in polynomial time (`Cslib.Complexity.computableInPolyTime_nwDecider`).

For correctness, the verifier with the instance fixed is a circuit of polynomial size in its
random string (`Cslib.Circuits.Boolean.PPoly.exists_of_polyTime`), and `t` is chosen so that
`2 ^ t` is at least eight times the size of this circuit and the number `m` of random bits. The
greedy design then has at least `m` blocks (`Cslib.Crypto.PRG.NisanWigderson.le_length_greedyMasks`)
and the hardness `2 ^ (n / c) = 2 ^ (4 t)` exceeds the size of the reconstructed circuits and `6 m`.
By `Cslib.Crypto.PRG.NisanWigderson.abs_card_div_sub_card_div_lt`, the fraction of seeds on which
the verifier accepts is within `1 / 6` of the fraction of random strings on which it accepts, which
is at least `2 / 3` on members and at most `1 / 3` on other instances.

## Main results

* `Cslib.Complexity.BPP_subset_P_of_isAverageCaseHard`: if a problem in `E` has slices
  average-case hard for size `2 ^ (n / c)` for all large `n`, then `BPP enc ⊆ P enc`.
* `Cslib.Complexity.P_eq_BPP_of_isAverageCaseHard`: under the same hypothesis, `P enc = BPP enc`.

The worst-case to average-case amplification, giving the same conclusion from a problem in `E`
outside `SIZE (2 ^ (ε n))` [ImpagliazzoWigderson1997], and the endpoint of Babai, Fortnow, Nisan
and Wigderson from `EXP ⊄ P/poly` [BabaiFortnowNisanWigderson1993] are not formalized here.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 20
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG.NisanWigderson Turing.MultiTapeTM
  Finset Filter

/-! ### Hardwiring a prefix -/

/-- The substitution feeding a function of `u.length + P` variables with `u ++ r`, from the
variables `r`. -/
private def prefixWiring (u : List Bool) (P : ℕ) (j : Fin (u.length + P)) : Fin P ⊕ Bool :=
  if h : (j : ℕ) < u.length then .inr u[j] else .inl ⟨j - u.length, by omega⟩

private theorem ofFn_substitute_prefixWiring (u : List Bool) {P : ℕ} (r : Fin P → Bool) :
    List.ofFn (substitute (prefixWiring u P) r) = u ++ List.ofFn r := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₁
  rw [List.getElem_ofFn]
  by_cases hj : j < u.length
  · rw [List.getElem_append_left hj]
    simp [substitute, prefixWiring, hj]
  · rw [List.getElem_append_right (by omega)]
    simp [substitute, prefixWiring, hj]

/-- A circuit for `L` on words of length `u.length + P` gives a circuit of at most two more gates
for a function `f` testing `u ++ r ∈ L`, as a function of `r`. -/
private theorem complexity_le_of_append (L : Language Bool) (u : List Bool) {P : ℕ}
    {f : BooleanFunction P} (hf : ∀ r, f r = true ↔ u ++ List.ofFn r ∈ L) :
    complexity interpretation (single f) ≤
      complexity interpretation (single (L.slice (u.length + P))) + 2 := by
  have h : f = fun r => L.slice (u.length + P) (substitute (prefixWiring u P) r) := by
    funext r
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, ofFn_substitute_prefixWiring, hf]
  rw [h]
  exact complexity_substitute_le _ _

/-! ### Counting votes -/

/-- The strict majority of the votes over all seeds of `ℓ` bits compares the number of seeds voting
`true` with half of `2 ^ ℓ`. -/
private theorem listStrictMajority_map_enumList (ℓ : ℕ) (vote : List Bool → Bool) :
    BitString.listStrictMajority ((BitString.enumList ℓ).map vote) =
      decide (2 ^ ℓ / 2 < #{z : Fin ℓ → Bool | vote (List.ofFn z) = true}) := by
  rw [BitString.enumList, List.map_map, BitString.listStrictMajority_map _ (BitString.nodup_enum ℓ),
    BitString.strictMajorityOn]
  have huniv : (BitString.enum ℓ).toFinset = univ := by ext; simp
  simp only [huniv, card_univ, BitString.card, Function.comp_apply]

/-! ### The main theorem -/

/-- **Hardness versus randomness: average-case hardness in `E` derandomizes `BPP`**
[NisanWigderson1994], [Arora and Barak, Chapter 20][AroraBarak09]. Let `L` be a problem on words
in `E`, decidable in time `O(2 ^ (k n))` for some `k`, and let `c > 0`. If for all large `n` the
slice of `L` at `n` is average-case hard for size `2 ^ (n / c)`, that is, every Boolean function of
De Morgan circuit complexity at most `2 ^ (n / c)` agrees with it on at most a
`1 / 2 + 2 ^ (-(n / c))` fraction of the words of length `n`, then every problem in `BPP enc` is
in `P enc`, for every encoding `enc` of instances.

The hardness is nonuniform and non-strict (`Cslib.Circuits.Boolean.IsAverageCaseHard`); the
conclusion is uniform, with the deterministic decider `Cslib.Complexity.nwDecider`. -/
theorem BPP_subset_P_of_isAverageCaseHard {L : Language Bool} {c : ℕ}
    (hL : (L : Set (List Bool)) ∈ E encBits) (hc : 0 < c)
    (hard : ∀ᶠ n in atTop, IsAverageCaseHard (L.slice n) (2 ^ (n / c)))
    {α : Type} (enc : α ↪ List Bool) : BPP enc ⊆ P enc := by
  rintro A ⟨p, V, hV, hdec⟩
  obtain ⟨k, hL⟩ := mem_E_iff.1 hL
  obtain ⟨g, hgL, hg⟩ := exists_computableInO_of_mem_DTIME hL
  have hslice (n : ℕ) : (fun y : Fin n → Bool => g (List.ofFn y)) = L.slice n := by
    funext y
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, ← hgL]
    rfl
  obtain ⟨L', hL', hVL'⟩ := PPoly.exists_of_polyTime hV
  -- the size of the verifier as a circuit in its random string, and the budget `B`
  set Tc : ℕ → ℕ := fun N =>
    complexity interpretation (single (L'.slice (2 * N + 1 + p.eval N))) with hTc
  have hTcpoly : PolynomiallyBounded Tc :=
    (mem_PPoly.1 hL').comp (g := fun N => 2 * N + 1 + p.eval N) (by fun_prop)
  set B : ℕ → ℕ := fun N => p.eval N + Tc N + 5 with hB
  have hBpoly : PolynomiallyBounded B := by
    simp only [hB]
    fun_prop
  obtain ⟨e, he⟩ := hBpoly.exists_clog_le_mul_log
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hard
  -- the parameters
  set t : ℕ → ℕ := fun N => n₀ + 3 + e * (Nat.log 2 N + 1) with ht
  set b := 2 ^ (8 * c + 1) with hb
  set seed : α → ℕ := fun x => (b + 1) * t (enc x).length with hseed
  set block : α → ℕ := fun x => c * (4 * t (enc x).length) with hblock
  set overlap : α → ℕ := fun x => t (enc x).length - 1 with hoverlap
  set out : α → ℕ := fun x => p.eval (enc x).length with hout
  refine ⟨nwDecider V g seed block overlap out, .of_tidy ?_, fun x => ?_⟩
  · -- polynomial time
    have hlog : ComputableTidilyInPolyTime (fun x => t (enc x).length) enc encUnary := by
      simp only [ht]
      fun_prop
    have hbudget (d : ℕ) : PolyBounded (fun x => (enc x).length) fun x =>
        2 ^ (d * t (enc x).length) := by
      refine PolyBounded.of_polynomiallyBounded (fun x => (enc x).length)
        (bound := fun N => 2 ^ (d * (n₀ + 3)) * 2 ^ (d * e * (Nat.log 2 N + 1)))
        ((PolynomiallyBounded.const _).mul (polynomiallyBounded_two_pow_mul_log _)) |>.mono
        fun x => le_of_eq ?_
      rw [← pow_add, ht]
      ring_nf
    have hseedO : ComputableTidilyInPolyTime seed enc encUnary := by
      simp only [hseed]
      fun_prop
    have hblockO : ComputableTidilyInPolyTime block enc encUnary := by
      simp only [hblock]
      fun_prop
    have hoverlapO : ComputableTidilyInPolyTime overlap enc encUnary := by
      simp only [hoverlap]
      fun_prop
    have houtO : ComputableTidilyInPolyTime out enc encUnary := by
      simp only [hout]
      fun_prop
    refine (computableInPolyTime_nwDecider hV
      (fun _ _ h => Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left k h)) hg (.of_tidy hseedO)
      (.of_tidy hblockO) (.of_tidy hoverlapO) (.of_tidy houtO)
      (hbudget (b + 1)) ((hbudget (k * (c * 4))).mono fun x => le_of_eq ?_)).tidy
    · simp only [hblock]
      ring_nf
  · -- correctness on the instance `x`
    set N := (enc x).length with hN
    set τ := t N with hτ
    set m := p.eval N with hm
    have hτ3 : n₀ + 3 ≤ τ := by simp only [hτ, ht]; omega
    -- `2 ^ τ` is at least eight times the budget
    have hBτ : 8 * B N ≤ 2 ^ τ := by
      have h₁ : B N ≤ 2 ^ (e * (Nat.log 2 N + 1)) :=
        (Nat.le_pow_clog one_lt_two _).trans (Nat.pow_le_pow_right two_pos (he N))
      have h₂ : 8 ≤ 2 ^ (n₀ + 3) := by
        rw [pow_add]
        exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      calc 8 * B N ≤ 2 ^ (n₀ + 3) * 2 ^ (e * (Nat.log 2 N + 1)) := Nat.mul_le_mul h₂ h₁
        _ = 2 ^ τ := by rw [← pow_add]
    have hBN : B N = m + Tc N + 5 := rfl
    set P := 2 ^ τ with hP
    have hP8 : 8 ≤ P := (Nat.pow_le_pow_right two_pos (by omega : 3 ≤ τ)).trans_eq' rfl
    -- the greedy design has at least `m` blocks
    have hc4 : c * 4 ≤ b + 1 := by
      have h₁ : c < 2 ^ c := Nat.lt_two_pow_self
      have h₂ : 2 ^ c * 4 ≤ b := by
        rw [hb, show 2 ^ c * 4 = 2 ^ (c + 2) by rw [pow_add]; rfl]
        exact Nat.pow_le_pow_right two_pos (by omega)
      omega
    have hlen : m ≤ (greedyMasks ((b + 1) * τ) (c * (4 * τ)) (τ - 1)).length := by
      refine le_length_greedyMasks (by omega) (by nlinarith) (by nlinarith) ?_
      calc 4 ^ (c * (4 * τ)) * m ≤ 4 ^ (c * (4 * τ)) * P := Nat.mul_le_mul_left _ (by omega)
        _ = b ^ τ := by
          rw [hb, hP, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, ← pow_add]
          ring_nf
    set D := Design.greedy ((b + 1) * τ) (c * (4 * τ)) (τ - 1) m hlen
    -- the hardness of the slice
    have hhard : IsAverageCaseHard (L.slice (c * (4 * τ))) (2 ^ (4 * τ)) := by
      have h := hn₀ (c * (4 * τ)) (by nlinarith)
      rwa [Nat.mul_div_cancel_left _ hc] at h
    -- the verifier with the instance fixed, as a test of its random string
    set test : BooleanFunction m := fun r => V (x, List.ofFn r) with htest_def
    have htest : complexity interpretation (single test) ≤ Tc N + 2 := by
      have h := complexity_le_of_append L' (frame (enc x)) (f := test) fun r => by
        rw [htest_def, hVL', encPair_apply, encBits_apply]
      rwa [length_frame] at h
    -- the generator fools the test
    have hY : 2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1 ≤ P ^ 2 := by
      have hQ : 2 ^ (τ - 1) * 2 = P := by
        rw [hP, ← pow_succ, Nat.sub_add_cancel (by omega)]
      have h₁ : τ - 1 < 2 ^ (τ - 1) := Nat.lt_two_pow_self
      have h₂ : 1 ≤ 2 ^ (τ - 1) := Nat.one_le_two_pow
      rw [← hQ]
      nlinarith
    have hs : Tc N + 2 + 1 + m * (2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1) + 1 ≤ 2 ^ (4 * τ) := by
      have h₁ : m * (2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1) ≤ m * P ^ 2 := Nat.mul_le_mul_left _ hY
      have h₂ : 8 * (m * P ^ 2) ≤ P ^ 3 :=
        calc 8 * (m * P ^ 2) = 8 * m * P ^ 2 := by ring
          _ ≤ P * P ^ 2 := Nat.mul_le_mul_right _ (by omega)
          _ = P ^ 3 := by ring
      have h₃ : 8 * P ^ 3 ≤ P ^ 4 := by
        rw [pow_succ P 3, mul_comm (P ^ 3)]
        exact Nat.mul_le_mul_right _ hP8
      have h₄ : P ≤ P ^ 4 := Nat.le_self_pow (by norm_num) P
      rw [mul_comm 4 τ, pow_mul, ← hP]
      omega
    have hεs : (m : ℝ) < 1 / 6 * ((2 ^ (4 * τ) : ℕ) : ℝ) := by
      have h₄ : P ≤ P ^ 4 := Nat.le_self_pow (by norm_num) P
      have h : 6 * m < 2 ^ (4 * τ) := by
        rw [mul_comm 4 τ, pow_mul, ← hP]
        omega
      have h' : (6 * m : ℝ) < ((2 ^ (4 * τ) : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    have hNW := abs_card_div_sub_card_div_lt D hhard hs hεs test htest
    -- the decider counts the seeds on which the test accepts the output of the generator
    have hmaj : nwDecider V g seed block overlap out x = decide (2 ^ ((b + 1) * τ) / 2 <
        #{z | test (generator D (L.slice (c * (4 * τ))) z) = true}) := by
      rw [nwDecider, listStrictMajority_map_enumList]
      congr 3
      refine filter_congr fun z _ => ?_
      rw [← hslice]
      change V (x, listGenerator g (c * (4 * τ)) ((greedyMasks ((b + 1) * τ) (c * (4 * τ))
        (τ - 1)).take m) (List.ofFn z)) = true ↔ _
      rw [listGenerator_take_greedyMasks hlen]
    rw [hmaj, decide_eq_true_iff]
    -- compare with the counts of the verifier
    set Z := #{z | test (generator D (L.slice (c * (4 * τ))) z) = true} with hZ
    set R := #{r | test r = true} with hR
    have hRF : #{r : Fin m → Bool | test r = false} = 2 ^ m - R := by
      have h := card_filter_add_card_filter_not (s := univ) (fun r : Fin m → Bool => test r = true)
      simp only [Bool.not_eq_true, card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin] at h
      have h' : R + #{r : Fin m → Bool | test r = false} = 2 ^ m := by convert h
      omega
    have h2ℓ : (0 : ℝ) < 2 ^ ((b + 1) * τ) := by positivity
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    rw [abs_sub_lt_iff] at hNW
    constructor
    · intro hxA
      have h := (hdec x).1 hxA
      have hR' : (2 : ℝ) * 2 ^ m ≤ 3 * R := by exact_mod_cast h
      have hZ' : (2 : ℝ) ^ ((b + 1) * τ) < 2 * Z := by
        have : (R : ℝ) / 2 ^ m - (Z : ℝ) / 2 ^ ((b + 1) * τ) < 1 / 6 := hNW.2
        rw [div_sub_div _ _ h2m.ne' h2ℓ.ne', div_lt_iff₀ (by positivity)] at this
        nlinarith
      have hZ'' : 2 ^ ((b + 1) * τ) < 2 * Z := by exact_mod_cast hZ'
      exact (Nat.div_lt_iff_lt_mul two_pos).2 (by omega)
    · intro hlt
      by_contra hxA
      have h := (hdec x).2 hxA
      have hRF' : 2 * 2 ^ m ≤ 3 * (2 ^ m - R) := hRF ▸ h
      have hRm : R ≤ 2 ^ m := (card_filter_le _ _).trans (by simp)
      have hR' : (3 : ℝ) * R ≤ 2 ^ m := by
        have : 3 * R ≤ 2 ^ m := by omega
        exact_mod_cast this
      have hZ' : (2 : ℝ) * Z < 2 ^ ((b + 1) * τ) := by
        have : (Z : ℝ) / 2 ^ ((b + 1) * τ) - (R : ℝ) / 2 ^ m < 1 / 6 := hNW.1
        rw [div_sub_div _ _ h2ℓ.ne' h2m.ne', div_lt_iff₀ (by positivity)] at this
        nlinarith
      have hZ'' : 2 * Z < 2 ^ ((b + 1) * τ) := by exact_mod_cast hZ'
      have := (Nat.div_lt_iff_lt_mul two_pos).1 hlt
      omega

/-- **Hardness versus randomness: `P = BPP` from average-case hardness in `E`**
[NisanWigderson1994], [Arora and Barak, Chapter 20][AroraBarak09]. If some problem in `E` has
slices that are average-case hard for size `2 ^ (n / c)` for all large `n`, for some `c > 0`, then
`P enc = BPP enc` for every encoding `enc` of instances. -/
theorem P_eq_BPP_of_isAverageCaseHard {L : Language Bool} {c : ℕ}
    (hL : (L : Set (List Bool)) ∈ E encBits) (hc : 0 < c)
    (hard : ∀ᶠ n in atTop, IsAverageCaseHard (L.slice n) (2 ^ (n / c)))
    {α : Type} (enc : α ↪ List Bool) : P enc = BPP enc :=
  P_subset_BPP.antisymm (BPP_subset_P_of_isAverageCaseHard hL hc hard enc)

end Cslib.Complexity

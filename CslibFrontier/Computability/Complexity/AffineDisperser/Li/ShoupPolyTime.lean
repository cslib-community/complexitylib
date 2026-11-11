/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.Berlekamp
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.ShoupIrreducible
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Complexity.AffineDisperser.PolyTime

/-!
# Polynomial-Time Certificates for Shoup's Irreducible Polynomial Construction

This module certifies `Turing.MultiTapeTM.ComputableInPolyTime` for the arithmetic, polynomial,
Berlekamp factoring, and Shoup construction algorithms in
`CslibFrontier.Computability.Complexity.AffineDisperser.Li.Berlekamp` and
`CslibFrontier.Computability.Complexity.AffineDisperser.Li.ShoupIrreducible`.

## Main results

* `Cslib.AffineDisperser.Li.computableInPolyTime_primeDeg`: `primeDeg` is computable in
  polynomial time on unary inputs.
* `Cslib.AffineDisperser.Li.computableInPolyTime_shoupIrreducibleBits`: `shoupIrreducibleBits` is
  computable in polynomial time from unary `q` to bit-list coefficients.

## References

* [V. Shoup, *New algorithms for finding irreducible polynomials over finite fields*][Shoup1990]
-/

public section

namespace Cslib.AffineDisperser.Li

open Turing.MultiTapeTM

attribute [local irreducible] ComputableInPolyTime ComputableTidilyInPolyTime

/-! ### Unary parameter selection (`fifthRoot`, `primeThresholdBound`, `primeDeg`) -/

private theorem tidy_fifthRoot :
    ComputableTidilyInPolyTime fifthRoot encUnary encUnary := by
  unfold fifthRoot
  have h5 : ComputableTidilyInPolyTime (fun k : ℕ => (k + 1) ^ 5) encUnary encUnary := by
    have heq : (fun k : ℕ => (k + 1) ^ 5) =
        fun k : ℕ => (k + 1) * (k + 1) * (k + 1) * (k + 1) * (k + 1) := by
      funext k; ring
    rw [heq]
    fun_prop
  refine ComputableTidilyInPolyTime.countPWithInput (encA := encUnary)
    ComputableTidilyInPolyTime.range ?_
  exact ComputableTidilyInPolyTime.unary_le'
    (h5.comp (ComputableTidilyInPolyTime.snd encUnary encUnary))
    (ComputableTidilyInPolyTime.fst encUnary encUnary)

/-- `fifthRoot` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_fifthRoot :
    ComputableInPolyTime fifthRoot encUnary encUnary :=
  .of_tidy tidy_fifthRoot

private theorem tidy_primeThresholdBound :
    ComputableTidilyInPolyTime primeThresholdBound encUnary encUnary := by
  unfold primeThresholdBound
  have := tidy_fifthRoot
  fun_prop

/-- `primeThresholdBound` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_primeThresholdBound :
    ComputableInPolyTime primeThresholdBound encUnary encUnary :=
  .of_tidy tidy_primeThresholdBound

private theorem tidy_primeDeg :
    ComputableTidilyInPolyTime primeDeg encUnary encUnary := by
  have hl : ComputableTidilyInPolyTime
      (fun N : ℕ =>
        (List.range (primeThresholdBound N)).map fun i => primeThresholdBound N + 1 + i)
      encUnary (encList encUnary) := by
    refine ComputableTidilyInPolyTime.mapWithInput
      (ComputableTidilyInPolyTime.range.comp tidy_primeThresholdBound) ?_
    have := tidy_primeThresholdBound
    fun_prop
  have hprimePlain : ComputableInPolyTime (fun b : ℕ => decide b.Prime) encUnary encBool := by
    fun_prop
  have hprime : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide p.2.Prime)
      (encPair encUnary encUnary) encBool :=
    hprimePlain.tidy.comp (ComputableTidilyInPolyTime.snd encUnary encUnary)
  have hf : ComputableTidilyInPolyTime
      (fun N : ℕ =>
        ((List.range (primeThresholdBound N)).map fun i => primeThresholdBound N + 1 + i).find?
          fun b => decide b.Prime)
      encUnary (encOption encUnary) :=
    ComputableTidilyInPolyTime.findWithInput hl hprime
  refine ComputableTidilyInPolyTime.optionGetDWithInput hf ?_
  have := tidy_primeThresholdBound
  fun_prop

/-- `primeDeg` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_primeDeg :
    ComputableInPolyTime primeDeg encUnary encUnary :=
  .of_tidy tidy_primeDeg

private def ordSomeAdd1 (_ x : ℕ) : ℕ := x + 1

private theorem tidy_ordTwoMod :
    ComputableTidilyInPolyTime ordTwoMod encUnary encUnary := by
  have hu2b : ComputableTidilyInPolyTime (fun n : ℕ => n) encUnary encNat := by fun_prop
  have htwoPow : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => 2 ^ (p.2 + 1))
      (encPair encUnary encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp
      (by fun_prop : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.2 + 1)
        (encPair encUnary encUnary) encUnary)
  have hmod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => 2 ^ (p.2 + 1) % p.1)
      (encPair encUnary encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_mod' htwoPow
      (hu2b.comp (ComputableTidilyInPolyTime.fst encUnary encUnary))
  have hpred := hmod.beq (.const 1)
  have hf : ComputableTidilyInPolyTime
      (fun q : ℕ => (List.range (q - 1)).find? fun i => 2 ^ (i + 1) % q == 1)
      encUnary (encOption encUnary) :=
    ComputableTidilyInPolyTime.findWithInput (test := fun q i => 2 ^ (i + 1) % q == 1)
      (ComputableTidilyInPolyTime.range.comp (by fun_prop :
        ComputableTidilyInPolyTime (fun q : ℕ => q - 1) encUnary encUnary))
      hpred
  have hsome : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => ordSomeAdd1 p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    unfold ordSomeAdd1
    fun_prop
  have helim := ComputableTidilyInPolyTime.optionElimWithInput hf
    (ComputableTidilyInPolyTime.const 0) hsome
  convert helim using 1
  funext q
  unfold ordTwoMod ordSomeAdd1
  cases (List.find? (fun i => 2 ^ (i + 1) % q == 1) (List.range (q - 1))) <;> rfl

/-- `ordTwoMod` is computable in polynomial time on unary naturals. -/
theorem computableInPolyTime_ordTwoMod :
    ComputableInPolyTime ordTwoMod encUnary encUnary :=
  .of_tidy tidy_ordTwoMod

private theorem tidy_qAdicValTwoPowSubOne :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => qAdicValTwoPowSubOne p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  have hu2b : ComputableTidilyInPolyTime (fun n : ℕ => n) encUnary encNat := by fun_prop
  have htwoPow : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => 2 ^ p.1.2)
      (encPair (encPair encUnary encUnary) encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp
      (by fun_prop : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2)
        (encPair (encPair encUnary encUnary) encUnary) encUnary)
  have hpow : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => p.1.1 ^ (p.2 + 1))
      (encPair (encPair encUnary encUnary) encUnary) encNat := by
    have hbase : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1)
        (encPair (encPair encUnary encUnary) encUnary) encNat := by fun_prop
    have hexp : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2 + 1)
        (encPair (encPair encUnary encUnary) encUnary) encUnary := by fun_prop
    exact ComputableTidilyInPolyTime.binary_pow' hbase hexp
  have hmod : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => 2 ^ p.1.2 % p.1.1 ^ (p.2 + 1))
      (encPair (encPair encUnary encUnary) encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_mod' htwoPow hpow
  have hpred : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => decide ((2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1) = true))
      (encPair (encPair encUnary encUnary) encUnary) encBool := by
    have hbeq := hmod.beq (.const 1)
    have heq : (fun p : (ℕ × ℕ) × ℕ =>
          decide ((2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1) = true)) =
        fun p => 2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1 := by
      funext p
      cases h : (2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1) <;> simp_all
    rw [heq]
    exact hbeq
  exact ComputableTidilyInPolyTime.countPWithInput (encA := encUnary)
    (ComputableTidilyInPolyTime.range.comp (ComputableTidilyInPolyTime.fst encUnary encUnary))
    hpred

/-- `qAdicValTwoPowSubOne` is computable in polynomial time on unary naturals. -/
theorem computableInPolyTime_qAdicValTwoPowSubOne :
    ComputableInPolyTime (fun p : ℕ × ℕ => qAdicValTwoPowSubOne p.1 p.2)
      (encPair encUnary encUnary) encUnary :=
  .of_tidy tidy_qAdicValTwoPowSubOne

/-! ### Binary polynomial arithmetic (`polyTrim`, `polyAdd`, `polyMul`, `polyDivMod`, `polyGcd`) -/

private def trimStep (st : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  (st.1 + 1, if b then st.1 + 1 else st.2)

private theorem foldl_trimStep_fst (p : List Bool) (i a : ℕ) :
    (p.foldl trimStep (i, a)).1 = i + p.length := by
  induction p generalizing i a with
  | nil => simp
  | cons b p ih =>
    simp only [List.foldl_cons, trimStep, List.length_cons, ih]
    omega

private theorem foldl_trimStep_le (p : List Bool) (i a : ℕ) (ha : a ≤ i) :
    (p.foldl trimStep (i, a)).2 ≤ i + p.length := by
  induction p generalizing i a with
  | nil => simpa using ha
  | cons b p ih =>
    rw [List.foldl_cons, List.length_cons]
    dsimp only [trimStep]
    have hnext : (if b = true then i + 1 else a) ≤ i + 1 := by
      cases b
      · exact Nat.le_succ_of_le ha
      · exact le_rfl
    have := ih (i + 1) _ hnext
    omega

private theorem polyTrim_append_false (p : List Bool) : polyTrim (p ++ [false]) = polyTrim p := by
  simp [polyTrim, List.foldr_append]

private theorem polyTrim_eq_take (p : List Bool) :
    polyTrim p = p.take (p.foldl trimStep (0, 0)).2 := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p b ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, trimStep, foldl_trimStep_fst,
      Nat.zero_add]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, polyTrim_append_false, ih]
      have hle := foldl_trimStep_le p 0 0 (le_refl 0)
      rw [Nat.zero_add] at hle
      exact (List.take_append_of_le_length hle).symm
    · simp only [↓reduceIte, polyTrim_append_true]
      have hlen : p.length + 1 = (p ++ [true]).length := by simp
      rw [hlen, List.take_length]

private theorem length_encUnary_le_iff {a b : ℕ} (h : a ≤ b) :
    (encUnary a).length ≤ (encUnary b).length := by
  simp only [encUnary]
  change (List.replicate a true).length ≤ (List.replicate b true).length
  simpa using h

private theorem length_encPair_mono {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    {a₁ a₂ : α} {b₁ b₂ : β} (ha : (encA a₁).length ≤ (encA a₂).length)
    (hb : (encB b₁).length ≤ (encB b₂).length) :
    (encPair encA encB (a₁, b₁)).length ≤ (encPair encA encB (a₂, b₂)).length := by
  rw [length_encPair, length_encPair]
  dsimp only
  omega

private theorem tidy_polyTrim : ComputableTidilyInPolyTime polyTrim encBits encBits := by
  have hstepPlain : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × Bool => trimStep p.1 p.2)
      (encPair (encPair encUnary encUnary) encBool) (encPair encUnary encUnary) := by
    unfold trimStep
    have hfst : ComputableInPolyTime (fun p : (ℕ × ℕ) × Bool => p.1.1 + 1)
        (encPair (encPair encUnary encUnary) encBool) encUnary := by fun_prop
    have hsnd : ComputableInPolyTime
        (fun p : (ℕ × ℕ) × Bool => if p.2 then p.1.1 + 1 else p.1.2)
        (encPair (encPair encUnary encUnary) encBool) encUnary :=
      ComputableInPolyTime.ite'
        (ComputableInPolyTime.snd (encPair encUnary encUnary) encBool)
        (by fun_prop) (by fun_prop)
    exact ComputableInPolyTime.pair hfst hsnd
  have hlenPair : ComputableTidilyInPolyTime (fun p : List Bool => (p.length, p.length))
      encBits (encPair encUnary encUnary) := by
    have hlen : ComputableTidilyInPolyTime List.length encBits encUnary :=
      ComputableTidilyInPolyTime.length_bits
    exact hlen.prod hlen
  have hfold : ComputableTidilyInPolyTime
      (fun p : List Bool => p.foldl trimStep (0, 0))
      encBits (encPair encUnary encUnary) := by
    refine ComputableTidilyInPolyTime.foldl' (encA := encBool) (encL := encBits)
      (encB := encPair encUnary encUnary)
      ComputableTidilyInPolyTime.id'
      (ComputableTidilyInPolyTime.const (0, 0))
      hstepPlain.tidy
      (B := fun p : List Bool => (encPair encUnary encUnary (p.length, p.length)).length)
      hlenPair.polyBounded_length ?_
    intro p i hi
    have hle1 : ((p.take i).foldl trimStep (0, 0)).1 ≤ p.length := by
      rw [foldl_trimStep_fst, Nat.zero_add, List.length_take]
      exact Nat.min_le_right _ _
    have hle2 : ((p.take i).foldl trimStep (0, 0)).2 ≤ p.length := by
      have := foldl_trimStep_le (p.take i) 0 0 (le_refl 0)
      rw [Nat.zero_add, List.length_take] at this
      exact this.trans (Nat.min_le_right _ _)
    exact length_encPair_mono encUnary encUnary
      (length_encUnary_le_iff hle1) (length_encUnary_le_iff hle2)
  have htake : ComputableTidilyInPolyTime
      (fun p : List Bool => p.take (p.foldl trimStep (0, 0)).2)
      encBits encBits :=
    ComputableTidilyInPolyTime.bitsTakeWithInput
      ComputableTidilyInPolyTime.id'
      (ComputableTidilyInPolyTime.snd encUnary encUnary |>.comp hfold)
  convert htake using 1
  funext p
  exact polyTrim_eq_take p

/-- `polyTrim` is computable in polynomial time on bit lists. -/
theorem computableInPolyTime_polyTrim : ComputableInPolyTime polyTrim encBits encBits :=
  .of_tidy tidy_polyTrim

private theorem tidy_polyAdd :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => polyAdd p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hmax : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => max p.1.length p.2.length)
      (encPair encBits encBits) encUnary :=
    ComputableTidilyInPolyTime.unary_max.comp
      ((ComputableTidilyInPolyTime.length_bits.comp
        (ComputableTidilyInPolyTime.fst encBits encBits)).prod
        (ComputableTidilyInPolyTime.length_bits.comp
          (ComputableTidilyInPolyTime.snd encBits encBits)))
  have hbit : ComputableTidilyInPolyTime
      (fun x : (List Bool × List Bool) × ℕ =>
        x.1.1.getD x.2 false ^^ x.1.2.getD x.2 false)
      (encPair (encPair encBits encBits) encUnary) encBool := by
    have h1 := ComputableTidilyInPolyTime.bitsGetDWithInput
      ((ComputableTidilyInPolyTime.fst encBits encBits).comp
        (ComputableTidilyInPolyTime.fst (encPair encBits encBits) encUnary))
      (ComputableTidilyInPolyTime.snd (encPair encBits encBits) encUnary)
      false
    have h2 := ComputableTidilyInPolyTime.bitsGetDWithInput
      ((ComputableTidilyInPolyTime.snd encBits encBits).comp
        (ComputableTidilyInPolyTime.fst (encPair encBits encBits) encUnary))
      (ComputableTidilyInPolyTime.snd (encPair encBits encBits) encUnary)
      false
    exact (ComputableTidilyInPolyTime.of_finite (fun b : Bool × Bool => b.1 ^^ b.2)
      (encA := encPair encBool encBool) (encB := encBool)).comp (h1.prod h2)
  have hmap : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool =>
        (List.range (max p.1.length p.2.length)).map fun i =>
          p.1.getD i false ^^ p.2.getD i false)
      (encPair encBits encBits) (encList encBool) :=
    ComputableTidilyInPolyTime.mapWithInput
      (ComputableTidilyInPolyTime.range.comp hmax) hbit
  exact tidy_polyTrim.comp (ComputableTidilyInPolyTime.listToBits.comp hmap)

/-- `polyAdd` is computable in polynomial time. -/
theorem computableInPolyTime_polyAdd :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyAdd p.1 p.2)
      (encPair encBits encBits) encBits :=
  .of_tidy tidy_polyAdd

private theorem polyBounded_encBool_const :
    ∀ b : Bool, (encBool b).length ≤ max (encBool false).length (encBool true).length := by
  intro b
  cases b
  · exact le_max_left _ _
  · exact le_max_right _ _

private theorem tidy_polyMul :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => polyMul p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hcond : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => p.1.isEmpty || p.2.isEmpty)
      (encPair encBits encBits) encBool :=
    (ComputableTidilyInPolyTime.of_finite (fun b : Bool × Bool => b.1 || b.2)
      (encA := encPair encBool encBool) (encB := encBool)).comp
      ((ComputableTidilyInPolyTime.bitsIsEmpty.comp
        (ComputableTidilyInPolyTime.fst encBits encBits)).prod
        (ComputableTidilyInPolyTime.bitsIsEmpty.comp
          (ComputableTidilyInPolyTime.snd encBits encBits)))
  have hsum : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => p.1.length + p.2.length)
      (encPair encBits encBits) encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.length_bits.comp
        (ComputableTidilyInPolyTime.fst encBits encBits)).prod
        (ComputableTidilyInPolyTime.length_bits.comp
          (ComputableTidilyInPolyTime.snd encBits encBits)))
  have hcoeffStep : ComputableTidilyInPolyTime
      (fun x : (((List Bool × List Bool) × ℕ) × Bool) × ℕ =>
        x.1.2 ^^ (x.1.1.1.1.getD x.2 false && x.1.1.1.2.getD (x.1.1.2 - x.2) false))
      (encPair (encPair (encPair (encPair encBits encBits) encUnary) encBool) encUnary)
      encBool := by
    have hfront := ComputableTidilyInPolyTime.fst
      (encPair (encPair (encPair encBits encBits) encUnary) encBool) encUnary
    have hpar := (ComputableTidilyInPolyTime.fst
      (encPair (encPair encBits encBits) encUnary) encBool).comp hfront
    have hacc := (ComputableTidilyInPolyTime.snd
      (encPair (encPair encBits encBits) encUnary) encBool).comp hfront
    have hi := ComputableTidilyInPolyTime.snd
      (encPair (encPair (encPair encBits encBits) encUnary) encBool) encUnary
    have hp := (ComputableTidilyInPolyTime.fst (encPair encBits encBits) encUnary).comp hpar
    have hk := (ComputableTidilyInPolyTime.snd (encPair encBits encBits) encUnary).comp hpar
    have hp1 := (ComputableTidilyInPolyTime.fst encBits encBits).comp hp
    have hp2 := (ComputableTidilyInPolyTime.snd encBits encBits).comp hp
    have hb1 := ComputableTidilyInPolyTime.bitsGetDWithInput hp1 hi false
    have hsub := ComputableTidilyInPolyTime.unary_sub.comp (hk.prod hi)
    have hb2 := ComputableTidilyInPolyTime.bitsGetDWithInput hp2 hsub false
    exact (ComputableTidilyInPolyTime.of_finite
      (fun b : Bool × Bool × Bool => b.1 ^^ (b.2.1 && b.2.2))
      (encA := encPair encBool (encPair encBool encBool)) (encB := encBool)).comp
      (hacc.prod (hb1.prod hb2))
  have hcoeff : ComputableTidilyInPolyTime
      (fun x : (List Bool × List Bool) × ℕ =>
        (List.range (x.2 + 1)).foldl
          (fun acc i => acc ^^ (x.1.1.getD i false && x.1.2.getD (x.2 - i) false)) false)
      (encPair (encPair encBits encBits) encUnary) encBool := by
    refine ComputableTidilyInPolyTime.foldlWith (encA := encUnary)
      (encL := encList encUnary) (encB := encBool)
      (par := id)
      (list := fun x : (List Bool × List Bool) × ℕ => List.range (x.2 + 1))
      (step := fun (x : (List Bool × List Bool) × ℕ) (acc : Bool) (i : ℕ) =>
        acc ^^ (x.1.1.getD i false && x.1.2.getD (x.2 - i) false))
      ComputableTidilyInPolyTime.id'
      (ComputableTidilyInPolyTime.range.comp (by fun_prop :
        ComputableTidilyInPolyTime (fun x : (List Bool × List Bool) × ℕ => x.2 + 1)
          (encPair (encPair encBits encBits) encUnary) encUnary))
      (ComputableTidilyInPolyTime.const false)
      hcoeffStep
      (B := fun _ => max (encBool false).length (encBool true).length)
      (PolyBounded.const _) ?_
    intro _ _ _
    exact polyBounded_encBool_const _
  have hmap : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool =>
        (List.range (p.1.length + p.2.length)).map fun k =>
          (List.range (k + 1)).foldl
            (fun acc i => acc ^^ (p.1.getD i false && p.2.getD (k - i) false)) false)
      (encPair encBits encBits) (encList encBool) :=
    ComputableTidilyInPolyTime.mapWithInput
      (ComputableTidilyInPolyTime.range.comp hsum) hcoeff
  have hres := tidy_polyTrim.comp (ComputableTidilyInPolyTime.listToBits.comp hmap)
  have hplain := ComputableInPolyTime.ite' hcond.computableInPolyTime
    (ComputableInPolyTime.const ([] : List Bool)) hres.computableInPolyTime
  convert hplain.tidy using 1
  funext p
  rfl

/-- `polyMul` is computable in polynomial time. -/
theorem computableInPolyTime_polyMul :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyMul p.1 p.2)
      (encPair encBits encBits) encBits :=
  .of_tidy tidy_polyMul

private theorem length_polyDivModStep_le (bt q r : List Bool) {n : ℕ}
    (hq : q.length ≤ n) (hr : r.length ≤ n) :
    (polyDivModStep bt (q, r)).1.length ≤ n ∧ (polyDivModStep bt (q, r)).2.length ≤ n := by
  unfold polyDivModStep
  dsimp only
  set r' := polyTrim r
  have hr' : r'.length ≤ n := (length_polyTrim_le r).trans hr
  split_ifs with h
  · exact ⟨(length_polyTrim_le q).trans hq, hr'⟩
  · have hbt_pos : 1 ≤ bt.length := by
      cases bt with
      | nil => simp at h
      | cons _ _ => simp
    have hr_ge : bt.length ≤ r'.length := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h
      exact h.1
    set d := r'.length - bt.length
    have hd1 : (List.replicate d false ++ [true]).length ≤ n := by
      simp only [List.length_append, List.length_replicate, List.length_singleton]
      omega
    have hdb : (List.replicate d false ++ bt).length ≤ n := by
      simp only [List.length_append, List.length_replicate]
      omega
    exact ⟨(length_polyAdd_le _ _).trans (max_le hq hd1),
      (length_polyAdd_le _ _).trans (max_le hr' hdb)⟩

private theorem tidy_replicateFalse :
    ComputableTidilyInPolyTime (fun d : ℕ => List.replicate d false) encUnary encBits := by
  have hmap : ComputableTidilyInPolyTime
      (fun d : ℕ => (List.range d).map fun _ => false)
      encUnary (encList encBool) :=
    ComputableTidilyInPolyTime.mapWithInput ComputableTidilyInPolyTime.range
      (ComputableTidilyInPolyTime.const false)
  have hres := ComputableTidilyInPolyTime.listToBits.comp hmap
  convert hres using 1
  funext d
  simp [List.map_const']

private theorem tidy_polyDivModStep :
    ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool × List Bool => polyDivModStep p.1 p.2)
      (encPair encBits (encPair encBits encBits)) (encPair encBits encBits) := by
  have hbt := ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hst := ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have hq := (ComputableTidilyInPolyTime.fst encBits encBits).comp hst
  have hr := tidy_polyTrim.comp ((ComputableTidilyInPolyTime.snd encBits encBits).comp hst)
  have hlenR := ComputableTidilyInPolyTime.length_bits.comp hr
  have hlenBt := ComputableTidilyInPolyTime.length_bits.comp hbt
  have hcond : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        decide ((polyTrim p.2.2).length < p.1.length) || p.1.isEmpty)
      (encPair encBits (encPair encBits encBits)) encBool :=
    (ComputableTidilyInPolyTime.of_finite (fun b : Bool × Bool => b.1 || b.2)
      (encA := encPair encBool encBool) (encB := encBool)).comp
      ((ComputableTidilyInPolyTime.unary_lt' hlenR hlenBt).prod
        (ComputableTidilyInPolyTime.bitsIsEmpty.comp hbt))
  have hbase : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool × List Bool => (polyTrim p.2.1, polyTrim p.2.2))
      (encPair encBits (encPair encBits encBits)) (encPair encBits encBits) :=
    (tidy_polyTrim.comp hq).prod hr
  have hd : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        (polyTrim p.2.2).length - p.1.length)
      (encPair encBits (encPair encBits encBits)) encUnary :=
    ComputableTidilyInPolyTime.unary_sub.comp (hlenR.prod hlenBt)
  have hrep : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        List.replicate ((polyTrim p.2.2).length - p.1.length) false)
      (encPair encBits (encPair encBits encBits)) encBits :=
    tidy_replicateFalse.comp hd
  have hstep1 : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        polyAdd p.2.1 (List.replicate ((polyTrim p.2.2).length - p.1.length) false ++ [true]))
      (encPair encBits (encPair encBits encBits)) encBits :=
    tidy_polyAdd.comp (hq.prod
      (ComputableTidilyInPolyTime.bitsAppend hrep (.const [true])))
  have hstep2 : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        polyAdd (polyTrim p.2.2)
          (List.replicate ((polyTrim p.2.2).length - p.1.length) false ++ p.1))
      (encPair encBits (encPair encBits encBits)) encBits :=
    tidy_polyAdd.comp (hr.prod
      (ComputableTidilyInPolyTime.bitsAppend hrep hbt))
  have hplain := ComputableInPolyTime.ite' hcond.computableInPolyTime
    hbase.computableInPolyTime (hstep1.prod hstep2).computableInPolyTime
  exact hplain.tidy

private theorem tidy_polyDivMod :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => polyDivMod p.1 p.2)
      (encPair encBits encBits) (encPair encBits encBits) := by
  have hpar : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => polyTrim p.2)
      (encPair encBits encBits) encBits :=
    tidy_polyTrim.comp (ComputableTidilyInPolyTime.snd encBits encBits)
  have hcnt : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => p.1.length)
      (encPair encBits encBits) encUnary :=
    ComputableTidilyInPolyTime.length_bits.comp (ComputableTidilyInPolyTime.fst encBits encBits)
  have hinit : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => (([] : List Bool), polyTrim p.1))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (ComputableTidilyInPolyTime.const ([] : List Bool)).prod
      (tidy_polyTrim.comp (ComputableTidilyInPolyTime.fst encBits encBits))
  have hbound : PolyBounded (fun p : List Bool × List Bool => (encPair encBits encBits p).length)
      (fun p : List Bool × List Bool => 3 * p.1.length + 1) :=
    ((PolyBounded.const 3).mul
      (ComputableTidilyInPolyTime.polyBounded hcnt)).add (PolyBounded.const 1)
  exact (ComputableTidilyInPolyTime.iterateWith_spec
    (invariant := fun p _ st => st.1.length ≤ p.1.length ∧ st.2.length ≤ p.1.length)
    hpar hcnt hinit tidy_polyDivModStep
    (fun p => ⟨by simp, length_polyTrim_le p.1⟩)
    (fun p _ _ _ hst => length_polyDivModStep_le _ _ _ hst.1 hst.2)
    hbound fun p _ st _ hst => by
      rw [length_encPair]
      simp only [encBits_apply]
      omega).1

private theorem tidy_polyMod :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => polyMod p.1 p.2)
      (encPair encBits encBits) encBits :=
  (ComputableTidilyInPolyTime.snd encBits encBits).comp tidy_polyDivMod

/-- `polyMod` is computable in polynomial time. -/
theorem computableInPolyTime_polyMod :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyMod p.1 p.2)
      (encPair encBits encBits) encBits :=
  .of_tidy tidy_polyMod

private theorem tidy_polyGcdStep :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => polyGcdStep p)
      (encPair encBits encBits) (encPair encBits encBits) := by
  have hcond := ComputableTidilyInPolyTime.bitsIsEmpty.comp
    (ComputableTidilyInPolyTime.snd encBits encBits)
  have hres : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => (p.2, polyMod p.1 p.2))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (ComputableTidilyInPolyTime.snd encBits encBits).prod tidy_polyMod
  exact (ComputableInPolyTime.ite' hcond.computableInPolyTime
    ComputableInPolyTime.id' hres.computableInPolyTime).tidy

private theorem length_polyGcdStep_le (a b : List Bool) {n : ℕ}
    (ha : a.length ≤ n) (hb : b.length ≤ n) :
    (polyGcdStep (a, b)).1.length ≤ n ∧ (polyGcdStep (a, b)).2.length ≤ n := by
  unfold polyGcdStep
  dsimp only
  split_ifs
  · exact ⟨ha, hb⟩
  · exact ⟨hb, (polyDivMod_iterate_bounds a (polyTrim b) a.length).2.1.trans ha⟩

private theorem tidy_polyGcd :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => polyGcd p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hpar : ComputableTidilyInPolyTime (fun _ : List Bool × List Bool => true)
      (encPair encBits encBits) encBool := .const true
  have hcnt : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => p.1.length + p.2.length + 1)
      (encPair encBits encBits) encUnary := by
    have h1 := ComputableTidilyInPolyTime.length_bits.comp
      (ComputableTidilyInPolyTime.fst encBits encBits)
    have h2 := ComputableTidilyInPolyTime.length_bits.comp
      (ComputableTidilyInPolyTime.snd encBits encBits)
    fun_prop
  have hinit : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => (polyTrim p.1, polyTrim p.2))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (tidy_polyTrim.comp (ComputableTidilyInPolyTime.fst encBits encBits)).prod
      (tidy_polyTrim.comp (ComputableTidilyInPolyTime.snd encBits encBits))
  have hstep : ComputableTidilyInPolyTime
      (fun x : Bool × List Bool × List Bool => polyGcdStep x.2)
      (encPair encBool (encPair encBits encBits)) (encPair encBits encBits) :=
    tidy_polyGcdStep.comp (ComputableTidilyInPolyTime.snd encBool (encPair encBits encBits))
  have hmax : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => max p.1.length p.2.length)
      (encPair encBits encBits) encUnary :=
    ComputableTidilyInPolyTime.unary_max.comp
      ((ComputableTidilyInPolyTime.length_bits.comp
        (ComputableTidilyInPolyTime.fst encBits encBits)).prod
        (ComputableTidilyInPolyTime.length_bits.comp
          (ComputableTidilyInPolyTime.snd encBits encBits)))
  have hbound : PolyBounded (fun p : List Bool × List Bool => (encPair encBits encBits p).length)
      (fun p : List Bool × List Bool => 3 * max p.1.length p.2.length + 1) :=
    ((PolyBounded.const 3).mul
      (ComputableTidilyInPolyTime.polyBounded hmax)).add (PolyBounded.const 1)
  have hiter : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool =>
        (polyGcdStep)^[p.1.length + p.2.length + 1] (polyTrim p.1, polyTrim p.2))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (ComputableTidilyInPolyTime.iterateWith_spec
      (step := fun (_ : Bool) x => polyGcdStep x)
      (invariant := fun p _ st =>
        st.1.length ≤ max p.1.length p.2.length ∧ st.2.length ≤ max p.1.length p.2.length)
      hpar hcnt hinit hstep
      (fun p => ⟨(length_polyTrim_le p.1).trans (le_max_left _ _),
        (length_polyTrim_le p.2).trans (le_max_right _ _)⟩)
      (fun p _ _ _ hst => length_polyGcdStep_le _ _ hst.1 hst.2)
      hbound fun p _ st _ hst => by
        rw [length_encPair]
        simp only [encBits_apply]
        omega).1
  exact (ComputableTidilyInPolyTime.fst encBits encBits).comp hiter

/-- `polyGcd` is computable in polynomial time. -/
theorem computableInPolyTime_polyGcd :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyGcd p.1 p.2)
      (encPair encBits encBits) encBits :=
  .of_tidy tidy_polyGcd

private theorem tidy_bitsFoldBool (op : Bool → Bool → Bool) (init : Bool) :
    ComputableTidilyInPolyTime (fun w : List Bool => w.foldl op init) encBits encBool :=
  ComputableTidilyInPolyTime.foldl' (encA := encBool) (encL := encBits) (encB := encBool)
    ComputableTidilyInPolyTime.id'
    (ComputableTidilyInPolyTime.const init)
    (ComputableTidilyInPolyTime.of_finite (fun b : Bool × Bool => op b.1 b.2)
      (encA := encPair encBool encBool) (encB := encBool))
    (B := fun _ => max (encBool false).length (encBool true).length)
    (PolyBounded.const _) (fun _ _ _ => polyBounded_encBool_const _)

private theorem tidy_bitsAnyId :
    ComputableTidilyInPolyTime (fun w : List Bool => w.any id) encBits encBool := by
  have heq : (fun w : List Bool => w.any id) = fun w => w.foldl or false := by
    funext w
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w b ih => simp [List.any_append, ih]
  rw [heq]
  exact tidy_bitsFoldBool or false

private theorem tidy_polyComposePow :
    ComputableTidilyInPolyTime (fun p : ℕ × List Bool => polyComposePow p.1 p.2)
      (encPair encUnary encBits) encBits := by
  have hq0 : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => decide (p.1 = 0))
      (encPair encUnary encBits) encBool := by
    have hle := ComputableTidilyInPolyTime.unary_le'
      (ComputableTidilyInPolyTime.fst encUnary encBits) (.const 0)
    convert hle using 1
    funext p
    simp
  have hsum : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => polyTrim [p.2.foldl xor false])
      (encPair encUnary encBits) encBits := by
    have hfold := tidy_bitsFoldBool xor false
    have hsing : ComputableTidilyInPolyTime (fun b : Bool => [b]) encBool encBits :=
      ComputableTidilyInPolyTime.of_finite (fun b : Bool => [b])
    exact tidy_polyTrim.comp
      (hsing.comp (hfold.comp (ComputableTidilyInPolyTime.snd encUnary encBits)))
  have hlen : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => p.1 * p.2.length)
      (encPair encUnary encBits) encUnary :=
    ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.fst encUnary encBits).prod
        (ComputableTidilyInPolyTime.length_bits.comp
          (ComputableTidilyInPolyTime.snd encUnary encBits)))
  have hcoeff : ComputableTidilyInPolyTime
      (fun x : (ℕ × List Bool) × ℕ =>
        if x.2 % x.1.1 == 0 then x.1.2.getD (x.2 / x.1.1) false else false)
      (encPair (encPair encUnary encBits) encUnary) encBool := by
    have hxq := (ComputableTidilyInPolyTime.fst encUnary encBits).comp
      (ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encUnary)
    have hxp := (ComputableTidilyInPolyTime.snd encUnary encBits).comp
      (ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encUnary)
    have hxj := ComputableTidilyInPolyTime.snd (encPair encUnary encBits) encUnary
    have hdm := ComputableTidilyInPolyTime.unary_divMod.comp (hxj.prod hxq)
    have hmod0 : ComputableTidilyInPolyTime
        (fun x : (ℕ × List Bool) × ℕ => x.2 % x.1.1 == 0)
        (encPair (encPair encUnary encBits) encUnary) encBool :=
      ((ComputableTidilyInPolyTime.snd encUnary encUnary).comp hdm).beq (.const 0)
    have hdiv := (ComputableTidilyInPolyTime.fst encUnary encUnary).comp hdm
    have hget := ComputableTidilyInPolyTime.bitsGetDWithInput hxp hdiv false
    exact (ComputableInPolyTime.ite' hmod0.computableInPolyTime
      hget.computableInPolyTime (ComputableInPolyTime.const false)).tidy
  have hmap : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool =>
        (List.range (p.1 * p.2.length)).map fun j =>
          if j % p.1 == 0 then p.2.getD (j / p.1) false else false)
      (encPair encUnary encBits) (encList encBool) :=
    ComputableTidilyInPolyTime.mapWithInput
      (f := fun p j => if j % p.1 == 0 then p.2.getD (j / p.1) false else false)
      (ComputableTidilyInPolyTime.range.comp hlen) hcoeff
  have hnz := tidy_polyTrim.comp (ComputableTidilyInPolyTime.listToBits.comp hmap)
  have hplain := ComputableInPolyTime.ite' hq0.computableInPolyTime
    hsum.computableInPolyTime hnz.computableInPolyTime
  convert hplain.tidy using 1
  funext p
  unfold polyComposePow
  simp

/-- `polyComposePow` is computable in polynomial time. -/
theorem computableInPolyTime_polyComposePow :
    ComputableInPolyTime (fun p : ℕ × List Bool => polyComposePow p.1 p.2)
      (encPair encUnary encBits) encBits :=
  .of_tidy tidy_polyComposePow

/-! ### Gaussian elimination and Berlekamp factoring -/

private theorem tidy_dotBool :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => dotBool p.1 p.2)
      (encPair encBits encBits) encBool :=
  (tidy_bitsFoldBool xor false).comp (ComputableTidilyInPolyTime.bitsZipWith and)

private def kernelDot (p : List (List Bool) × List Bool) (v : List Bool) : Bool :=
  dotBool p.2 v

private def kernelRowStep (par : List (List Bool) × List Bool) (v : List Bool) : List Bool :=
  if dotBool par.2 v then
    List.zipWith xor v (par.1.getD ((par.1.map (dotBool par.2)).idxOf true) [])
  else v

private theorem tidy_kernelStepBits :
    ComputableTidilyInPolyTime
      (fun p : List (List Bool) × List Bool => kernelStepBits p.2 p.1)
      (encPair (encList encBits) encBits) (encList encBits) := by
  have hN := ComputableTidilyInPolyTime.fst (encList encBits) encBits
  have ha := ComputableTidilyInPolyTime.snd (encList encBits) encBits
  have hdotEl : ComputableTidilyInPolyTime
      (fun x : (List (List Bool) × List Bool) × List Bool => kernelDot x.1 x.2)
      (encPair (encPair (encList encBits) encBits) encBits) encBool :=
    tidy_dotBool.comp ((ha.comp (ComputableTidilyInPolyTime.fst (encPair (encList encBits) encBits)
      encBits)).prod (ComputableTidilyInPolyTime.snd (encPair (encList encBits) encBits) encBits))
  have hvals : ComputableTidilyInPolyTime
      (fun p : List (List Bool) × List Bool => p.1.map (dotBool p.2))
      (encPair (encList encBits) encBits) (encList encBool) :=
    ComputableTidilyInPolyTime.mapWithInput (f := kernelDot) hN hdotEl
  have hpIdx : ComputableTidilyInPolyTime
      (fun p : List (List Bool) × List Bool => (p.1.map (dotBool p.2)).idxOf true)
      (encPair (encList encBits) encBits) encUnary :=
    ComputableTidilyInPolyTime.idxOfWithInput (encA := encBool) hvals (.const true)
  have hlenNPlain : ComputableInPolyTime (fun l : List (List Bool) => l.length)
      (encList encBits) encUnary := by fun_prop
  have hlenN : ComputableTidilyInPolyTime
      (fun p : List (List Bool) × List Bool => p.1.length)
      (encPair (encList encBits) encBits) encUnary :=
    hlenNPlain.tidy.comp hN
  have hcond := ComputableTidilyInPolyTime.unary_lt' hpIdx hlenN
  have hpiv : ComputableTidilyInPolyTime
      (fun p : List (List Bool) × List Bool => p.1.getD ((p.1.map (dotBool p.2)).idxOf true) [])
      (encPair (encList encBits) encBits) encBits := by
    have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
        (encPair (encList encBits) encUnary) encBits := by fun_prop
    exact hget.tidy.comp (hN.prod hpIdx)
  have hrowStep : ComputableTidilyInPolyTime
      (fun x : (List (List Bool) × List Bool) × List Bool => kernelRowStep x.1 x.2)
      (encPair (encPair (encList encBits) encBits) encBits) encBits := by
    have hxpar := ComputableTidilyInPolyTime.fst (encPair (encList encBits) encBits) encBits
    have hxv := ComputableTidilyInPolyTime.snd (encPair (encList encBits) encBits) encBits
    have hxa := ha.comp hxpar
    have hdot := tidy_dotBool.comp (hxa.prod hxv)
    have hxpiv := hpiv.comp hxpar
    have hxor := (ComputableTidilyInPolyTime.bitsZipWith xor).comp (hxv.prod hxpiv)
    exact (ComputableInPolyTime.ite' hdot.computableInPolyTime
      hxor.computableInPolyTime hxv.computableInPolyTime).tidy
  have hmapped := ComputableTidilyInPolyTime.mapWithInput (f := kernelRowStep) hN hrowStep
  convert (ComputableInPolyTime.ite' hcond.computableInPolyTime
    hmapped.computableInPolyTime hN.computableInPolyTime).tidy using 1
  funext p
  unfold kernelStepBits kernelRowStep
  simp only [decide_eq_true_eq]

private theorem tidy_kernelBasisBits :
    ComputableTidilyInPolyTime
      (fun p : ℕ × List (List Bool) => kernelBasisBits p.1 p.2)
      (encPair encUnary (encList encBits)) (encList encBits) := by
  have hboundFn : ComputableTidilyInPolyTime
      (fun p : ℕ × List (List Bool) => p.1 * (2 * p.1 + 1))
      (encPair encUnary (encList encBits)) encUnary := by
    have := ComputableTidilyInPolyTime.fst encUnary (encList encBits)
    fun_prop
  refine ComputableTidilyInPolyTime.foldlWith (encA := encBits) (encL := encList encBits)
    (encB := encList encBits)
    (par := fun _ => true)
    (list := fun p : ℕ × List (List Bool) => p.2)
    (step := fun _ N a => kernelStepBits a N)
    (.const true)
    (ComputableTidilyInPolyTime.snd encUnary (encList encBits))
    (ComputableTidilyInPolyTime.bitsSingles.comp
      (ComputableTidilyInPolyTime.fst encUnary (encList encBits)))
    (tidy_kernelStepBits.comp
      (((ComputableTidilyInPolyTime.snd encBool (encList encBits)).comp
        (ComputableTidilyInPolyTime.fst (encPair encBool (encList encBits)) encBits)).prod
        (ComputableTidilyInPolyTime.snd (encPair encBool (encList encBits)) encBits)))
    (B := fun p : ℕ × List (List Bool) => p.1 * (2 * p.1 + 1))
    (ComputableTidilyInPolyTime.polyBounded hboundFn) ?_
  intro p i hi
  obtain ⟨hlen, hrows⟩ := length_kernelBasisBits p.1 (p.2.take i)
  unfold kernelBasisBits at hlen hrows
  refine (length_encList_le encBits _ (b := p.1)
    (fun v hv => by simp [encBits_apply, hrows v hv])).trans ?_
  rw [hlen]

private theorem tidy_kernelVecBits :
    ComputableTidilyInPolyTime
      (fun p : ℕ × List (List Bool) => kernelVecBits p.1 p.2)
      (encPair encUnary (encList encBits)) encBits := by
  have hany : ComputableTidilyInPolyTime
      (fun x : (ℕ × List (List Bool)) × List Bool => x.2.any id)
      (encPair (encPair encUnary (encList encBits)) encBits) encBool :=
    tidy_bitsAnyId.comp
      (ComputableTidilyInPolyTime.snd (encPair encUnary (encList encBits)) encBits)
  have hfind := ComputableTidilyInPolyTime.findWithInput
    (test := fun (_ : ℕ × List (List Bool)) (v : List Bool) => v.any id)
    tidy_kernelBasisBits hany
  exact ComputableTidilyInPolyTime.optionGetDWithInput hfind
    (tidy_replicateFalse.comp (ComputableTidilyInPolyTime.fst encUnary (encList encBits)))

/-- `kernelVecBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_kernelVecBits :
    ComputableInPolyTime
      (fun p : ℕ × List (List Bool) => kernelVecBits p.1 p.2)
      (encPair encUnary (encList encBits)) encBits :=
  .of_tidy tidy_kernelVecBits

private def berlekampCell (x : List Bool × ℕ) (k : ℕ) : Bool :=
  ((powerTable x.1).getD (2 * (k + 1)) []).getD x.2 false ^^ decide ((x.2 == k + 1) = true)

private def berlekampRow (g : List Bool) (i : ℕ) : List Bool :=
  (List.range ((g.length - 1) - 1)).map (berlekampCell (g, i))

private theorem tidy_berlekampMatrix :
    ComputableTidilyInPolyTime berlekampMatrix encBits (encList encBits) := by
  have htab : ComputableTidilyInPolyTime powerTable encBits (encList encBits) := by
    have hp : ComputableInPolyTime powerTable encBits (encList encBits) := by fun_prop
    exact hp.tidy
  have hd : ComputableTidilyInPolyTime (fun g : List Bool => g.length - 1) encBits encUnary :=
    ComputableTidilyInPolyTime.unary_sub.comp
      (ComputableTidilyInPolyTime.length_bits.prod (.const 1))
  have hcell : ComputableTidilyInPolyTime
      (fun x : (List Bool × ℕ) × ℕ => berlekampCell x.1 x.2)
      (encPair (encPair encBits encUnary) encUnary) encBool := by
    unfold berlekampCell
    have hxg := (ComputableTidilyInPolyTime.fst encBits encUnary).comp
      (ComputableTidilyInPolyTime.fst (encPair encBits encUnary) encUnary)
    have hxi := (ComputableTidilyInPolyTime.snd encBits encUnary).comp
      (ComputableTidilyInPolyTime.fst (encPair encBits encUnary) encUnary)
    have hxk := ComputableTidilyInPolyTime.snd (encPair encBits encUnary) encUnary
    have htabx := htab.comp hxg
    have hj : ComputableTidilyInPolyTime
        (fun x : (List Bool × ℕ) × ℕ => x.2 + 1)
        (encPair (encPair encBits encUnary) encUnary) encUnary :=
      ComputableTidilyInPolyTime.unary_add.comp (hxk.prod (.const 1))
    have h2j : ComputableTidilyInPolyTime
        (fun x : (List Bool × ℕ) × ℕ => 2 * (x.2 + 1))
        (encPair (encPair encBits encUnary) encUnary) encUnary :=
      ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const 2).prod hj)
    have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
        (encPair (encList encBits) encUnary) encBits := by fun_prop
    have hrow := hget.tidy.comp (htabx.prod h2j)
    have hbit := ComputableTidilyInPolyTime.bitsGetDWithInput hrow hxi false
    have hdiag : ComputableTidilyInPolyTime
        (fun x : (List Bool × ℕ) × ℕ => decide ((x.1.2 == x.2 + 1) = true))
        (encPair (encPair encBits encUnary) encUnary) encBool := by
      convert hxi.beq hj using 1
      funext x
      rw [Bool.eq_iff_iff]
      simp
    exact (ComputableTidilyInPolyTime.of_finite (fun b : Bool × Bool => b.1 ^^ b.2)
      (encA := encPair encBool encBool) (encB := encBool)).comp (hbit.prod hdiag)
  have hrow : ComputableTidilyInPolyTime
      (fun x : List Bool × ℕ => berlekampRow x.1 x.2)
      (encPair encBits encUnary) encBits := by
    have hdr := ComputableTidilyInPolyTime.range.comp
      (ComputableTidilyInPolyTime.unary_sub.comp
        ((hd.comp (ComputableTidilyInPolyTime.fst encBits encUnary)).prod (.const 1)))
    exact ComputableTidilyInPolyTime.listToBits.comp
      (ComputableTidilyInPolyTime.mapWithInput (f := berlekampCell) hdr hcell)
  have hres := ComputableTidilyInPolyTime.mapWithInput (f := berlekampRow)
    (ComputableTidilyInPolyTime.range.comp hd) hrow
  convert hres using 1
  funext g
  unfold berlekampMatrix berlekampRow berlekampCell
  rfl

private theorem tidy_berlekampStep :
    ComputableTidilyInPolyTime berlekampStep encBits encBits := by
  have hgt := tidy_polyTrim
  have hlen := ComputableTidilyInPolyTime.length_bits.comp hgt
  have hle2 := ComputableTidilyInPolyTime.unary_le' hlen (.const 2)
  have hd2 : ComputableTidilyInPolyTime (fun g : List Bool => (polyTrim g).length - 2)
      encBits encUnary :=
    ComputableTidilyInPolyTime.unary_sub.comp (hlen.prod (.const 2))
  have hvec : ComputableTidilyInPolyTime
      (fun g : List Bool => kernelVecBits ((polyTrim g).length - 2) (berlekampMatrix (polyTrim g)))
      encBits encBits :=
    tidy_kernelVecBits.comp (hd2.prod (tidy_berlekampMatrix.comp hgt))
  have hany : ComputableTidilyInPolyTime
      (fun g : List Bool =>
        (kernelVecBits ((polyTrim g).length - 2) (berlekampMatrix (polyTrim g))).any id)
      encBits encBool :=
    tidy_bitsAnyId.comp hvec
  have hgcd := tidy_polyGcd.comp
    (hgt.prod (ComputableTidilyInPolyTime.bitsCons (.const false) hvec))
  have hinner := (ComputableInPolyTime.ite' hany.computableInPolyTime
    hgcd.computableInPolyTime hgt.computableInPolyTime).tidy
  convert (ComputableInPolyTime.ite' hle2.computableInPolyTime
    hgt.computableInPolyTime hinner.computableInPolyTime).tidy using 1
  funext g
  unfold berlekampStep
  simp only [Function.comp_def, decide_eq_true_eq]

private theorem length_berlekampStep_le (g : List Bool) :
    (berlekampStep g).length ≤ g.length := by
  unfold berlekampStep
  dsimp only
  set gt := polyTrim g
  have hgt : gt.length ≤ g.length := length_polyTrim_le g
  split_ifs with h1 h2
  · exact hgt
  · have hv : (kernelVecBits (gt.length - 2) (berlekampMatrix gt)).length = gt.length - 2 :=
      length_kernelVecBits _ _
    let w := false :: kernelVecBits (gt.length - 2) (berlekampMatrix gt)
    have hgcd : (polyGcd gt w).length ≤ max gt.length w.length :=
      (polyGcd_iterate_bounds gt w (gt.length + w.length + 1)).1
    simp only [w, List.length_cons, hv] at hgcd
    omega
  · exact hgt

private theorem tidy_berlekampIrreducibleFactor :
    ComputableTidilyInPolyTime berlekampIrreducibleFactor encBits encBits := by
  have hpar : ComputableTidilyInPolyTime (fun _ : List Bool => true) encBits encBool := .const true
  have hcnt := ComputableTidilyInPolyTime.length_bits
  have hinit := tidy_polyTrim
  have hstep : ComputableTidilyInPolyTime
      (fun x : Bool × List Bool => berlekampStep x.2)
      (encPair encBool encBits) encBits :=
    tidy_berlekampStep.comp (ComputableTidilyInPolyTime.snd encBool encBits)
  exact (ComputableTidilyInPolyTime.iterateWith_spec
    (step := fun (_ : Bool) f => berlekampStep f)
    (invariant := fun g _ f => f.length ≤ g.length)
    hpar hcnt hinit hstep
    (fun g => length_polyTrim_le g)
    (fun g _ f _ hf => (length_berlekampStep_le f).trans hf)
    PolyBounded.self fun _ _ _ _ hf => by
      simpa only [encBits_apply] using hf).1

private theorem getD_length_le_encList_bits (L : List (List Bool)) (i : ℕ) :
    (L.getD i []).length ≤ (encList encBits L).length := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[i]? with
  | none => simp
  | some v =>
    simp only [Option.getD_some]
    simpa only [encBits_apply] using length_le_encList_of_mem encBits (List.mem_of_getElem? h)

private theorem length_polyMod_lt {u f : List Bool} (hf : (polyTrim f).isEmpty = false) :
    (polyMod u f).length < (polyTrim f).length := by
  have hbt_ne : polyTrim f ≠ [] := by
    intro hnil
    rw [hnil] at hf
    simp at hf
  have hf0 : polyOfBits f ≠ 0 := polyOfBits_ne_zero_iff_polyTrim.mpr hbt_ne
  exact (polyOfBits_polyDivMod_spec (a := u) hf0).2.1

private theorem length_polyMul_le' (a b : List Bool) :
    (polyMul a b).length ≤ a.length + b.length := by
  unfold polyMul
  split_ifs
  · simp
  · exact (length_polyTrim_le _).trans (by simp)

private theorem tidy_replicateTrue :
    ComputableTidilyInPolyTime (fun d : ℕ => List.replicate d true) encUnary encBits := by
  have hmap : ComputableTidilyInPolyTime
      (fun d : ℕ => (List.range d).map fun _ => true)
      encUnary (encList encBool) :=
    ComputableTidilyInPolyTime.mapWithInput ComputableTidilyInPolyTime.range
      (ComputableTidilyInPolyTime.const true)
  have hres := ComputableTidilyInPolyTime.listToBits.comp hmap
  convert hres using 1
  funext d
  simp [List.map_const']

private theorem tidy_primeGeThree :
    ComputableTidilyInPolyTime (fun q : ℕ => decide (q.Prime ∧ 3 ≤ q)) encUnary encBool := by
  have hprimePlain : ComputableInPolyTime (fun q : ℕ => decide q.Prime) encUnary encBool := by
    fun_prop
  have hge3 := ComputableTidilyInPolyTime.unary_le' (.const 3) ComputableTidilyInPolyTime.id'
  have hand := (ComputableTidilyInPolyTime.of_finite (fun b : Bool × Bool => b.1 && b.2)
    (encA := encPair encBool encBool) (encB := encBool)).comp (hprimePlain.tidy.prod hge3)
  convert hand using 1
  funext q
  simp

private theorem tidy_shoupCyclicFactorBounded :
    ComputableTidilyInPolyTime
      (fun q : ℕ =>
        (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[
          if q.Prime ∧ 3 ≤ q then qAdicValTwoPowSubOne q (ordTwoMod q) - 1 else 0]
          (berlekampIrreducibleFactor (List.replicate q true)))
      encUnary encBits := by
  have hcond := tidy_primeGeThree
  have hk := tidy_qAdicValTwoPowSubOne.comp
    (ComputableTidilyInPolyTime.id'.prod tidy_ordTwoMod)
  have hcntTrue := ComputableTidilyInPolyTime.unary_sub.comp (hk.prod (.const 1))
  have hcnt : ComputableTidilyInPolyTime
      (fun q : ℕ => if q.Prime ∧ 3 ≤ q then qAdicValTwoPowSubOne q (ordTwoMod q) - 1 else 0)
      encUnary encUnary := by
    have hite := (ComputableInPolyTime.ite' hcond.computableInPolyTime
      hcntTrue.computableInPolyTime (ComputableInPolyTime.const (0 : ℕ))).tidy
    convert hite using 1
    funext q
    by_cases h : q.Prime ∧ 3 ≤ q <;> simp [h]
  have hinit : ComputableTidilyInPolyTime
      (fun q : ℕ => berlekampIrreducibleFactor (List.replicate q true)) encUnary encBits :=
    tidy_berlekampIrreducibleFactor.comp tidy_replicateTrue
  have hstep : ComputableTidilyInPolyTime
      (fun x : ℕ × List Bool => berlekampIrreducibleFactor (polyComposePow x.1 x.2))
      (encPair encUnary encBits) encBits :=
    tidy_berlekampIrreducibleFactor.comp tidy_polyComposePow
  have hbound : PolyBounded (fun q : ℕ => (encUnary q).length) (fun q : ℕ => q) :=
    ComputableTidilyInPolyTime.polyBounded ComputableTidilyInPolyTime.id'
  refine (ComputableTidilyInPolyTime.iterateWith_spec
    (invariant := fun q k g =>
      g = (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[k]
        (berlekampIrreducibleFactor (List.replicate q true)))
    ComputableTidilyInPolyTime.id' hcnt hinit hstep
    (fun _ => rfl)
    (fun q k g _ hg => by rw [hg, Function.iterate_succ_apply'])
    hbound ?_).1
  intro q k g hk hg
  simp only [encBits_apply]
  rw [hg]
  by_cases h : q.Prime ∧ 3 ≤ q
  · rw [ite_eq_left_iff.mpr (fun hnot => absurd h hnot)] at hk
    exact length_shoupCyclicFactor_iterate_le h.1 h.2 hk
  · rw [ite_eq_right_iff.mpr (fun hpos => absurd hpos h)] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [Function.iterate_zero_apply]
    unfold berlekampIrreducibleFactor
    have hinv : ∀ s, ((berlekampStep)^[s] (polyTrim (List.replicate q true))).length ≤ q := by
      intro s
      induction s with
      | zero => exact (length_polyTrim_le _).trans (by simp)
      | succ s ih => rw [Function.iterate_succ_apply']; exact (length_berlekampStep_le _).trans ih
    simpa only [List.length_replicate] using hinv q

private theorem tidy_shoupLAdd :
    ComputableTidilyInPolyTime
      (fun p : ℕ × List (List Bool) × List (List Bool) => shoupLAdd p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair (encList encBits) (encList encBits))) (encList encBits) := by
  have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
      (encPair (encList encBits) encUnary) encBits := by fun_prop
  have hcell : ComputableTidilyInPolyTime
      (fun x : (ℕ × List (List Bool) × List (List Bool)) × ℕ =>
        polyAdd (x.1.2.1.getD x.2 []) (x.1.2.2.getD x.2 []))
      (encPair (encPair encUnary (encPair (encList encBits) (encList encBits))) encUnary)
      encBits := by
    have hxpar := ComputableTidilyInPolyTime.fst
      (encPair encUnary (encPair (encList encBits) (encList encBits))) encUnary
    have hxi := ComputableTidilyInPolyTime.snd
      (encPair encUnary (encPair (encList encBits) (encList encBits))) encUnary
    have hxs := (ComputableTidilyInPolyTime.snd encUnary
      (encPair (encList encBits) (encList encBits))).comp hxpar
    have hxa := (ComputableTidilyInPolyTime.fst (encList encBits) (encList encBits)).comp hxs
    have hxb := (ComputableTidilyInPolyTime.snd (encList encBits) (encList encBits)).comp hxs
    exact tidy_polyAdd.comp ((hget.tidy.comp (hxa.prod hxi)).prod (hget.tidy.comp (hxb.prod hxi)))
  have hres := ComputableTidilyInPolyTime.mapWithInput
    (f := fun p i => polyAdd (p.2.1.getD i []) (p.2.2.getD i []))
    (ComputableTidilyInPolyTime.range.comp
      (ComputableTidilyInPolyTime.fst encUnary (encPair (encList encBits) (encList encBits))))
    hcell
  exact hres

private def shoupLMulSum (a b : List (List Bool)) (cnt off1 off2 : ℕ) : List Bool :=
  (List.range cnt).foldl
    (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) []))) []

private theorem length_foldl_shoupLMulSum_le (a b : List (List Bool)) (off1 off2 : ℕ)
    (L : List ℕ) :
    (L.foldl (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) [])))
      []).length ≤ (encList encBits a).length + (encList encBits b).length := by
  have hstep_gen : ∀ acc : List Bool,
      acc.length ≤ (encList encBits a).length + (encList encBits b).length →
      (L.foldl (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) [])))
        acc).length ≤ (encList encBits a).length + (encList encBits b).length := by
    intro acc hacc
    induction L generalizing acc with
    | nil => exact hacc
    | cons t L ih =>
      rw [List.foldl_cons]
      apply ih
      refine (length_polyAdd_le _ _).trans (max_le hacc ?_)
      refine (length_polyMul_le' _ _).trans ?_
      exact Nat.add_le_add (getD_length_le_encList_bits a _) (getD_length_le_encList_bits b _)
  exact hstep_gen [] (by simp)

private theorem tidy_shoupLMulSum :
    ComputableTidilyInPolyTime
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) =>
        shoupLMulSum p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary (encPair encUnary encUnary)))
      encBits := by
  have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
      (encPair (encList encBits) encUnary) encBits := by fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun x : (((List (List Bool) × List (List Bool)) × (ℕ × ℕ)) × List Bool) × ℕ =>
        polyAdd x.1.2
          (polyMul (x.1.1.1.1.getD (x.1.1.2.1 + x.2) [])
            (x.1.1.1.2.getD (x.1.1.2.2 - x.2) [])))
      (encPair (encPair (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary encUnary)) encBits) encUnary)
      encBits := by
    have hfront := ComputableTidilyInPolyTime.fst
      (encPair (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary))
        encBits) encUnary
    have hpar := (ComputableTidilyInPolyTime.fst
      (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary))
      encBits).comp hfront
    have hacc := (ComputableTidilyInPolyTime.snd
      (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary))
      encBits).comp hfront
    have ht := ComputableTidilyInPolyTime.snd
      (encPair (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary))
        encBits) encUnary
    have hab := (ComputableTidilyInPolyTime.fst
      (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary)).comp hpar
    have hoffs := (ComputableTidilyInPolyTime.snd
      (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary)).comp hpar
    have ha := (ComputableTidilyInPolyTime.fst (encList encBits) (encList encBits)).comp hab
    have hb := (ComputableTidilyInPolyTime.snd (encList encBits) (encList encBits)).comp hab
    have ho1 := (ComputableTidilyInPolyTime.fst encUnary encUnary).comp hoffs
    have ho2 := (ComputableTidilyInPolyTime.snd encUnary encUnary).comp hoffs
    have hidx1 := ComputableTidilyInPolyTime.unary_add.comp (ho1.prod ht)
    have hidx2 := ComputableTidilyInPolyTime.unary_sub.comp (ho2.prod ht)
    have haGet := hget.tidy.comp (ha.prod hidx1)
    have hbGet := hget.tidy.comp (hb.prod hidx2)
    exact tidy_polyAdd.comp (hacc.prod (tidy_polyMul.comp (haGet.prod hbGet)))
  have hparFn : ComputableTidilyInPolyTime
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) => (p.1, p.2.2))
      (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary (encPair encUnary encUnary)))
      (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary)) :=
    (ComputableTidilyInPolyTime.fst (encPair (encList encBits) (encList encBits))
      (encPair encUnary (encPair encUnary encUnary))).prod
      ((ComputableTidilyInPolyTime.snd encUnary (encPair encUnary encUnary)).comp
        (ComputableTidilyInPolyTime.snd (encPair (encList encBits) (encList encBits))
          (encPair encUnary (encPair encUnary encUnary))))
  have hlistFn : ComputableTidilyInPolyTime
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) => List.range p.2.1)
      (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary (encPair encUnary encUnary)))
      (encList encUnary) :=
    ComputableTidilyInPolyTime.range.comp
      ((ComputableTidilyInPolyTime.fst encUnary (encPair encUnary encUnary)).comp
        (ComputableTidilyInPolyTime.snd (encPair (encList encBits) (encList encBits))
          (encPair encUnary (encPair encUnary encUnary))))
  have hbound : PolyBounded
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) =>
        (encPair (encPair (encList encBits) (encList encBits))
          (encPair encUnary (encPair encUnary encUnary)) p).length)
      (fun p => (encList encBits p.1.1).length + (encList encBits p.1.2).length) := by
    have hab := ComputableTidilyInPolyTime.fst (encPair (encList encBits) (encList encBits))
      (encPair encUnary (encPair encUnary encUnary))
    have ha := ComputableTidilyInPolyTime.length_bits.comp
      ((ComputableTidilyInPolyTime.encode (encList encBits)).comp
        ((ComputableTidilyInPolyTime.fst (encList encBits) (encList encBits)).comp hab))
    have hb := ComputableTidilyInPolyTime.length_bits.comp
      ((ComputableTidilyInPolyTime.encode (encList encBits)).comp
        ((ComputableTidilyInPolyTime.snd (encList encBits) (encList encBits)).comp hab))
    exact ComputableTidilyInPolyTime.polyBounded
      (ComputableTidilyInPolyTime.unary_add.comp (ha.prod hb))
  exact ComputableTidilyInPolyTime.foldlWith
    (encA := encUnary) (encL := encList encUnary) (encB := encBits)
    (par := fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) => (p.1, p.2.2))
    (list := fun p => List.range p.2.1)
    (step := fun par acc t =>
      polyAdd acc (polyMul (par.1.1.getD (par.2.1 + t) []) (par.1.2.getD (par.2.2 - t) [])))
    hparFn hlistFn (.const ([] : List Bool)) hstep hbound fun p i _ => by
      simpa only [encBits_apply] using length_foldl_shoupLMulSum_le p.1.1 p.1.2 p.2.2.1 p.2.2.2
        ((List.range p.2.1).take i)

private def shoupLMulCell
    (p : (ℕ × List Bool) × (List (List Bool) × List (List Bool))) (k : ℕ) : List Bool :=
  let low := shoupLMulSum p.2.1 p.2.2 (k + 1) 0 k
  let high := shoupLMulSum p.2.1 p.2.2 (p.1.1 - 1 - k) (k + 1) (p.1.1 - 1)
  polyMod (polyAdd low (false :: high)) p.1.2

private theorem tidy_shoupLMul :
    ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × (List (List Bool) × List (List Bool)) =>
        shoupLMul p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits)))
      (encList encBits) := by
  let encCtx := encPair
    (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))) encUnary
  have hcell : ComputableTidilyInPolyTime
      (fun x : ((ℕ × List Bool) × (List (List Bool) × List (List Bool))) × ℕ =>
        shoupLMulCell x.1 x.2)
      encCtx encBits := by
    have hxpar := ComputableTidilyInPolyTime.fst
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))) encUnary
    have hxk := ComputableTidilyInPolyTime.snd
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))) encUnary
    have hqf := (ComputableTidilyInPolyTime.fst (encPair encUnary encBits)
      (encPair (encList encBits) (encList encBits))).comp hxpar
    have hab := (ComputableTidilyInPolyTime.snd (encPair encUnary encBits)
      (encPair (encList encBits) (encList encBits))).comp hxpar
    have hq := (ComputableTidilyInPolyTime.fst encUnary encBits).comp hqf
    have hf := (ComputableTidilyInPolyTime.snd encUnary encBits).comp hqf
    have h1 : ComputableTidilyInPolyTime
        (fun _ : ((ℕ × List Bool) × (List (List Bool) × List (List Bool))) × ℕ => (1 : ℕ))
        encCtx encUnary :=
      ComputableTidilyInPolyTime.const (1 : ℕ)
    have h0 : ComputableTidilyInPolyTime
        (fun _ : ((ℕ × List Bool) × (List (List Bool) × List (List Bool))) × ℕ => (0 : ℕ))
        encCtx encUnary :=
      ComputableTidilyInPolyTime.const (0 : ℕ)
    have hk1 := ComputableTidilyInPolyTime.unary_add.comp (hxk.prod h1)
    have hq1 := ComputableTidilyInPolyTime.unary_sub.comp (hq.prod h1)
    have hcntH := ComputableTidilyInPolyTime.unary_sub.comp (hq1.prod hxk)
    have hlow := tidy_shoupLMulSum.comp (hab.prod (hk1.prod (h0.prod hxk)))
    have hhigh := tidy_shoupLMulSum.comp (hab.prod (hcntH.prod (hk1.prod hq1)))
    have hsum := tidy_polyAdd.comp
      (hlow.prod (ComputableTidilyInPolyTime.bitsCons (.const false) hhigh))
    exact tidy_polyMod.comp (hsum.prod hf)
  have hres := ComputableTidilyInPolyTime.mapWithInput (f := shoupLMulCell)
    (ComputableTidilyInPolyTime.range.comp
      ((ComputableTidilyInPolyTime.fst encUnary encBits).comp
        (ComputableTidilyInPolyTime.fst (encPair encUnary encBits)
          (encPair (encList encBits) (encList encBits)))))
    hcell
  convert hres using 1
  funext p
  unfold shoupLMul
  refine congrArg (fun fn => List.map fn (List.range p.1.1)) ?_
  funext k
  dsimp only [shoupLMulCell, shoupLMulSum]
  have hidx : ∀ t, p.1.1 + k - (k + 1 + t) = p.1.1 - 1 - t := fun t => by omega
  simp [hidx]

private theorem length_shoupLMul (q : ℕ) (f : List Bool) (a b : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    (shoupLMul q f a b).length = q ∧ ∀ v ∈ shoupLMul q f a b, v.length ≤ f.length := by
  unfold shoupLMul
  refine ⟨by simp, fun v hv => ?_⟩
  rw [List.mem_map] at hv
  rcases hv with ⟨k, _, rfl⟩
  exact (length_polyMod_lt hf).le.trans (length_polyTrim_le f)

private def shoupFrobStep (p : ℕ × List Bool) (x : List (List Bool)) : List (List Bool) :=
  shoupLMul p.1 p.2 x x

private def shoupLFrobQBounded (q : ℕ) (f : List Bool) (a : List (List Bool)) :
    List (List Bool) :=
  (shoupFrobStep (q, f))^[if (polyTrim f).isEmpty then 0 else q] a

private theorem shoupLFrobQBounded_eq {q : ℕ} {f : List Bool} (a : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    shoupLFrobQBounded q f a = shoupLFrobQ q f a := by
  unfold shoupLFrobQBounded shoupLFrobQ shoupFrobStep
  simp [hf]

section ShoupFrobSection
attribute [local irreducible] shoupLMul shoupFrobStep polyTrim

private theorem tidy_shoupLFrobQBounded :
    ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => shoupLFrobQBounded p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBits) (encList encBits)) (encList encBits) := by
  have hpar := ComputableTidilyInPolyTime.fst (encPair encUnary encBits) (encList encBits)
  have ha := ComputableTidilyInPolyTime.snd (encPair encUnary encBits) (encList encBits)
  have hq := (ComputableTidilyInPolyTime.fst encUnary encBits).comp hpar
  have hf := (ComputableTidilyInPolyTime.snd encUnary encBits).comp hpar
  have hcond := ComputableTidilyInPolyTime.bitsIsEmpty.comp (tidy_polyTrim.comp hf)
  have hcnt : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => if (polyTrim p.1.2).isEmpty then 0 else p.1.1)
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary :=
    (ComputableInPolyTime.ite' hcond.computableInPolyTime
      (ComputableInPolyTime.const (0 : ℕ)) hq.computableInPolyTime).tidy
  have hstep := tidy_shoupLMul.comp ((ComputableTidilyInPolyTime.fst (encPair encUnary encBits)
    (encList encBits)).prod ((ComputableTidilyInPolyTime.snd (encPair encUnary encBits)
      (encList encBits)).prod (ComputableTidilyInPolyTime.snd (encPair encUnary encBits)
        (encList encBits))))
  have hstep' : ComputableTidilyInPolyTime
      (fun x : (ℕ × List Bool) × List (List Bool) => shoupFrobStep x.1 x.2)
      (encPair (encPair encUnary encBits) (encList encBits)) (encList encBits) := by
    convert hstep using 1
    funext x
    unfold shoupFrobStep
    rfl
  have haLenPlain : ComputableInPolyTime (fun l : List (List Bool) => l.length)
      (encList encBits) encUnary := by fun_prop
  have haLen := haLenPlain.tidy.comp ha
  have haBits := ComputableTidilyInPolyTime.length_bits.comp
    ((ComputableTidilyInPolyTime.encode (encList encBits)).comp ha)
  have hfLen := ComputableTidilyInPolyTime.length_bits.comp hf
  have hsizeFn : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        (p.1.1 + p.2.length) * (2 * (p.1.2.length + (encList encBits p.2).length) + 1))
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary := by
    have hq' := hq
    have ha' := haLen
    have hf' := hfLen
    have hab' := haBits
    have hsum1 := ComputableTidilyInPolyTime.unary_add.comp (hq'.prod ha')
    have hsum2 := ComputableTidilyInPolyTime.unary_add.comp (hf'.prod hab')
    have hmul2 := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hsum2)
    have hadd1 := ComputableTidilyInPolyTime.unary_add.comp
      (hmul2.prod (ComputableTidilyInPolyTime.const 1))
    exact ComputableTidilyInPolyTime.unary_mul.comp (hsum1.prod hadd1)
  have hiter := (ComputableTidilyInPolyTime.iterateWith_spec
    (step := shoupFrobStep)
    (invariant := fun p _ x =>
      x.length ≤ p.1.1 + p.2.length ∧
        ∀ v ∈ x, v.length ≤ p.1.2.length + (encList encBits p.2).length)
    hpar hcnt ha hstep'
    (fun p => ⟨Nat.le_add_left _ _, fun v hv => by
      simpa only [encBits_apply] using
        (length_le_encList_of_mem encBits hv).trans (Nat.le_add_left _ _)⟩)
    (fun p k x hk _ => by
      have hf_ne : (polyTrim p.1.2).isEmpty = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        rw [ite_eq_left_iff.mpr (fun hnot => absurd h hnot)] at hk
        omega
      unfold shoupFrobStep
      obtain ⟨hl, hrows⟩ := length_shoupLMul p.1.1 p.1.2 x x hf_ne
      exact ⟨by omega, fun v hv => (hrows v hv).trans (Nat.le_add_right _ _)⟩)
    (ComputableTidilyInPolyTime.polyBounded hsizeFn) fun p _ x _ hx => by
      refine (length_encList_le encBits x (b := p.1.2.length + (encList encBits p.2).length)
        (fun v hv => by simp [encBits_apply, hx.2 v hv])).trans ?_
      exact Nat.mul_le_mul_right _ hx.1).1
  exact hiter

end ShoupFrobSection

private theorem foldl_range_const_eq {α : Type*} (step : α → α) (init : α) (n : ℕ) :
    (List.range n).foldl (fun x _ => step x) init = step^[n] init := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Function.iterate_succ_apply']

private def shoupBetaInitYCell (_ q_i : ℕ) : List Bool :=
  if (q_i == 1) = true then [true] else []

private def shoupBetaStep (p : ℕ × List Bool) (st : List (List Bool) × List (List Bool)) :
    List (List Bool) × List (List Bool) :=
  (shoupLAdd p.1 st.1 st.2, shoupLFrobQBounded p.1 p.2 st.2)

private def shoupBetaBounded (q : ℕ) (f : List Bool) : List (List Bool) :=
  ((shoupBetaStep (q, f))^[if (polyTrim f).isEmpty then 0 else f.length - 1]
    (List.replicate q [], (List.range q).map (shoupBetaInitYCell q))).1

private theorem shoupBetaBounded_eq {q : ℕ} {f : List Bool} (hf : (polyTrim f).isEmpty = false) :
    shoupBetaBounded q f = shoupBeta q f := by
  unfold shoupBetaBounded shoupBeta shoupBetaStep
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [← foldl_range_const_eq]
  congr 1
  refine congrArg (fun g => List.foldl g _ (List.range (f.length - 1))) ?_
  funext st _
  rw [shoupLFrobQBounded_eq _ hf]

section ShoupBetaSection
attribute [local irreducible] shoupLAdd shoupLFrobQBounded shoupBetaStep polyTrim

private theorem tidy_shoupBetaBounded :
    ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => shoupBetaBounded p.1 p.2)
      (encPair encUnary encBits) (encList encBits) := by
  have hq := ComputableTidilyInPolyTime.fst encUnary encBits
  have hf := ComputableTidilyInPolyTime.snd encUnary encBits
  have hfne := ComputableTidilyInPolyTime.bitsIsEmpty.comp (tidy_polyTrim.comp hf)
  have hcntTrue := ComputableTidilyInPolyTime.unary_sub.comp
    ((ComputableTidilyInPolyTime.length_bits.comp hf).prod (.const 1))
  have hcnt : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => if (polyTrim p.2).isEmpty then 0 else p.2.length - 1)
      (encPair encUnary encBits) encUnary :=
    (ComputableInPolyTime.ite' hfne.computableInPolyTime
      (ComputableInPolyTime.const (0 : ℕ)) hcntTrue.computableInPolyTime).tidy
  have hinitY : ComputableTidilyInPolyTime
      (fun q : ℕ => (List.range q).map (shoupBetaInitYCell q))
      encUnary (encList encBits) := by
    have hbit : ComputableTidilyInPolyTime
        (fun x : ℕ × ℕ => shoupBetaInitYCell x.1 x.2)
        (encPair encUnary encUnary) encBits := by
      have hi := ComputableTidilyInPolyTime.snd encUnary encUnary
      have hcond : ComputableTidilyInPolyTime (fun x : ℕ × ℕ => x.2 == 1)
          (encPair encUnary encUnary) encBool :=
        hi.beq (.const 1)
      exact (ComputableInPolyTime.ite' hcond.computableInPolyTime
        (ComputableInPolyTime.const [true]) (ComputableInPolyTime.const ([] : List Bool))).tidy
    exact ComputableTidilyInPolyTime.mapWithInput (f := shoupBetaInitYCell)
      ComputableTidilyInPolyTime.range hbit
  have hinit1 : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => List.replicate p.1 ([] : List Bool))
      (encPair encUnary encBits) (encList encBits) := by
    let repEmpty : ℕ → ℕ → List Bool := fun _ _ => []
    have hconst : ComputableTidilyInPolyTime (fun x : ℕ × ℕ => repEmpty x.1 x.2)
        (encPair encUnary encUnary) encBits :=
      ComputableTidilyInPolyTime.const ([] : List Bool)
    have hmap := ComputableTidilyInPolyTime.mapWithInput (f := repEmpty)
      ComputableTidilyInPolyTime.range hconst
    have hres := hmap.comp hq
    have hrep : ∀ n m : ℕ,
        List.replicate n ([] : List Bool) = (List.range n).map (repEmpty m) := by
      intro n m
      induction n with
      | zero => rfl
      | succ k ih =>
        rw [List.replicate_succ', List.range_succ, List.map_append]
        exact congrArg (· ++ [[]]) ih
    convert hres using 1
    funext p
    simp only [Function.comp_def]
    exact hrep p.1 p.1
  have hinit := hinit1.prod (hinitY.comp hq)
  have hstep : ComputableTidilyInPolyTime
      (fun x : (ℕ × List Bool) × (List (List Bool) × List (List Bool)) =>
        shoupBetaStep x.1 x.2)
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits)))
      (encPair (encList encBits) (encList encBits)) := by
    have hxpar := ComputableTidilyInPolyTime.fst (encPair encUnary encBits)
      (encPair (encList encBits) (encList encBits))
    have hxst := ComputableTidilyInPolyTime.snd (encPair encUnary encBits)
      (encPair (encList encBits) (encList encBits))
    have hxq := (ComputableTidilyInPolyTime.fst encUnary encBits).comp hxpar
    have hx2 := (ComputableTidilyInPolyTime.snd (encList encBits) (encList encBits)).comp hxst
    have hpair := (tidy_shoupLAdd.comp (hxq.prod hxst)).prod
      (tidy_shoupLFrobQBounded.comp (hxpar.prod hx2))
    convert hpair using 1
    funext x
    unfold shoupBetaStep
    rfl
  have hboundFn : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => 3 * (p.1 * (2 * (p.2.length + 1) + 1)) + 1)
      (encPair encUnary encBits) encUnary := by
    have hq' := hq
    have hf1 := ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.length_bits.comp hf).prod (.const 1))
    have h2f := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hf1)
    have h2f1 := ComputableTidilyInPolyTime.unary_add.comp (h2f.prod (.const 1))
    have hqmul := ComputableTidilyInPolyTime.unary_mul.comp (hq'.prod h2f1)
    have h3q := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 3).prod hqmul)
    exact ComputableTidilyInPolyTime.unary_add.comp (h3q.prod (.const 1))
  have hgetD_le : ∀ (L : List (List Bool)) (m : ℕ),
      (∀ v ∈ L, v.length ≤ m) → ∀ i, (L.getD i []).length ≤ m := by
    intro L m hL i
    rw [List.getD_eq_getElem?_getD]
    cases hopt : L[i]? with
    | none => simp
    | some u => simp only [Option.getD_some]; exact hL u (List.mem_of_getElem? hopt)
  have hiter := (ComputableTidilyInPolyTime.iterateWith_spec
    (invariant := fun p _ st =>
      st.1.length ≤ p.1 ∧ st.2.length ≤ p.1 ∧
        (∀ v ∈ st.1, v.length ≤ p.2.length + 1) ∧ ∀ v ∈ st.2, v.length ≤ p.2.length + 1)
    ComputableTidilyInPolyTime.id' hcnt hinit hstep
    (fun p => by
      refine ⟨by simp, by simp, fun v hv => ?_, fun v hv => ?_⟩
      · simp only [List.mem_replicate] at hv
        rw [hv.2]
        simp
      · dsimp only [Function.comp_def] at hv
        rw [List.mem_map] at hv
        rcases hv with ⟨i, _, rfl⟩
        unfold shoupBetaInitYCell
        split_ifs <;> simp)
    (fun p k st hk hinv => by
      have hf_ne : (polyTrim p.2).isEmpty = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        rw [ite_eq_left_iff.mpr (fun hnot => absurd h hnot)] at hk
        omega
      have h1 : (shoupLAdd p.1 st.1 st.2).length ≤ p.1 := by
        simp [shoupLAdd]
      have h1_rows : ∀ v ∈ shoupLAdd p.1 st.1 st.2, v.length ≤ p.2.length + 1 := by
        intro v hv
        unfold shoupLAdd at hv
        rw [List.mem_map] at hv
        rcases hv with ⟨i, _, rfl⟩
        exact (length_polyAdd_le _ _).trans
          (max_le (hgetD_le _ _ hinv.2.2.1 i) (hgetD_le _ _ hinv.2.2.2 i))
      have hfrob : shoupLFrobQBounded p.1 p.2 st.2 = shoupLFrobQ p.1 p.2 st.2 :=
        shoupLFrobQBounded_eq _ hf_ne
      have h2 : (shoupLFrobQBounded p.1 p.2 st.2).length ≤ p.1 ∧
          ∀ v ∈ shoupLFrobQBounded p.1 p.2 st.2, v.length ≤ p.2.length + 1 := by
        rw [hfrob]
        unfold shoupLFrobQ
        cases hq0 : p.1 with
        | zero =>
          rw [Function.iterate_zero_apply]
          exact ⟨by omega, hinv.2.2.2⟩
        | succ q' =>
          rw [Function.iterate_succ_apply']
          obtain ⟨hl, hrows⟩ := length_shoupLMul (q' + 1) p.2 _ _ hf_ne
          exact ⟨hl.le, fun v hv => (hrows v hv).trans (Nat.le_succ _)⟩
      unfold shoupBetaStep
      exact ⟨h1, h2.1, h1_rows, h2.2⟩)
    (ComputableTidilyInPolyTime.polyBounded hboundFn)
    (fun p _ st _ hinv => by
      rw [length_encPair]
      have hl1 := length_encList_le encBits st.1 (b := p.2.length + 1)
        (fun v hv => by simp [encBits_apply, hinv.2.2.1 v hv])
      have hl2 := length_encList_le encBits st.2 (b := p.2.length + 1)
        (fun v hv => by simp [encBits_apply, hinv.2.2.2 v hv])
      have hm1 := hl1.trans (Nat.mul_le_mul_right _ hinv.1)
      have hm2 := hl2.trans (Nat.mul_le_mul_right _ hinv.2.1)
      omega)).1
  exact (ComputableTidilyInPolyTime.fst (encList encBits) (encList encBits)).comp hiter

end ShoupBetaSection

private def shoupPowersOneCell (_ q_i : ℕ) : List Bool :=
  if (q_i == 0) = true then [true] else []

private def shoupPowersStep (p : (ℕ × List Bool) × List (List Bool))
    (st : List (List (List Bool)) × List (List Bool)) :
    List (List (List Bool)) × List (List Bool) :=
  (st.1 ++ [st.2], shoupLMul p.1.1 p.1.2 st.2 p.2)

private def shoupPowersBounded (q : ℕ) (f : List Bool) (β : List (List Bool)) :
    List (List (List Bool)) :=
  ((shoupPowersStep ((q, f), β))^[if (polyTrim f).isEmpty then 0 else q + 1]
    ([], (List.range q).map (shoupPowersOneCell q))).1

private theorem shoupPowersBounded_eq {q : ℕ} {f : List Bool} (β : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    shoupPowersBounded q f β = shoupPowers q f β := by
  unfold shoupPowersBounded shoupPowers shoupPowersStep
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [← foldl_range_const_eq]
  rfl

section ShoupPowersSection
attribute [local irreducible] shoupLMul shoupPowersStep polyTrim

private theorem tidy_shoupPowersBounded :
    ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => shoupPowersBounded p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBits) (encList encBits))
      (encList (encList encBits)) := by
  have hpar := ComputableTidilyInPolyTime.fst (encPair encUnary encBits) (encList encBits)
  have hβ := ComputableTidilyInPolyTime.snd (encPair encUnary encBits) (encList encBits)
  have hq := (ComputableTidilyInPolyTime.fst encUnary encBits).comp hpar
  have hf := (ComputableTidilyInPolyTime.snd encUnary encBits).comp hpar
  have hfne := ComputableTidilyInPolyTime.bitsIsEmpty.comp (tidy_polyTrim.comp hf)
  have hq1 := ComputableTidilyInPolyTime.unary_add.comp (hq.prod (.const 1))
  have hcnt : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        if (polyTrim p.1.2).isEmpty then 0 else p.1.1 + 1)
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary :=
    (ComputableInPolyTime.ite' hfne.computableInPolyTime
      (ComputableInPolyTime.const (0 : ℕ)) hq1.computableInPolyTime).tidy
  have hinitOne : ComputableTidilyInPolyTime
      (fun q : ℕ => (List.range q).map (shoupPowersOneCell q))
      encUnary (encList encBits) := by
    have hbit : ComputableTidilyInPolyTime
        (fun x : ℕ × ℕ => shoupPowersOneCell x.1 x.2)
        (encPair encUnary encUnary) encBits := by
      have hi := ComputableTidilyInPolyTime.snd encUnary encUnary
      have hcond : ComputableTidilyInPolyTime (fun x : ℕ × ℕ => x.2 == 0)
          (encPair encUnary encUnary) encBool :=
        hi.beq (.const 0)
      exact (ComputableInPolyTime.ite' hcond.computableInPolyTime
        (ComputableInPolyTime.const [true]) (ComputableInPolyTime.const ([] : List Bool))).tidy
    exact ComputableTidilyInPolyTime.mapWithInput (f := shoupPowersOneCell)
      ComputableTidilyInPolyTime.range hbit
  let encIn := encPair (encPair encUnary encBits) (encList encBits)
  have hnil : ComputableTidilyInPolyTime
      (fun _ : (ℕ × List Bool) × List (List Bool) => ([] : List (List (List Bool))))
      encIn (encList (encList encBits)) :=
    ComputableTidilyInPolyTime.const ([] : List (List (List Bool)))
  have hinit : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        (([] : List (List (List Bool))), (List.range p.1.1).map (shoupPowersOneCell p.1.1)))
      encIn (encPair (encList (encList encBits)) (encList encBits)) :=
    hnil.prod (hinitOne.comp hq)
  have hsnoc : ComputableTidilyInPolyTime
      (fun p : List (List (List Bool)) × List (List Bool) => p.1 ++ [p.2])
      (encPair (encList (encList encBits)) (encList encBits)) (encList (encList encBits)) :=
    (ComputableTidilyInDegree.snoc (encList encBits)).computableTidilyInPolyTime
  have hstep : ComputableTidilyInPolyTime
      (fun x : ((ℕ × List Bool) × List (List Bool)) ×
          (List (List (List Bool)) × List (List Bool)) =>
        shoupPowersStep x.1 x.2)
      (encPair encIn (encPair (encList (encList encBits)) (encList encBits)))
      (encPair (encList (encList encBits)) (encList encBits)) := by
    have hxInput := ComputableTidilyInPolyTime.fst
      encIn (encPair (encList (encList encBits)) (encList encBits))
    have hxst := ComputableTidilyInPolyTime.snd
      encIn (encPair (encList (encList encBits)) (encList encBits))
    have hxqf := (ComputableTidilyInPolyTime.fst (encPair encUnary encBits) (encList encBits)).comp
      hxInput
    have hxβ := (ComputableTidilyInPolyTime.snd (encPair encUnary encBits) (encList encBits)).comp
      hxInput
    have hxcur :=
      (ComputableTidilyInPolyTime.snd (encList (encList encBits)) (encList encBits)).comp hxst
    have hpair := (hsnoc.comp hxst).prod (tidy_shoupLMul.comp (hxqf.prod (hxcur.prod hxβ)))
    convert hpair using 1
    funext x
    unfold shoupPowersStep
    rfl
  have hboundFn : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        let rowB := p.1.1 * (2 * (p.1.2.length + 1) + 1)
        2 * ((p.1.1 + 1) * (2 * rowB + 1)) + 1 + rowB)
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary := by
    have hq' := hq
    have hq1' := hq1
    have hf1 := ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.length_bits.comp hf).prod (.const 1))
    have h2f := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hf1)
    have h2f1 := ComputableTidilyInPolyTime.unary_add.comp (h2f.prod (.const 1))
    have hrowB := ComputableTidilyInPolyTime.unary_mul.comp (hq'.prod h2f1)
    have h2r := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hrowB)
    have h2r1 := ComputableTidilyInPolyTime.unary_add.comp (h2r.prod (.const 1))
    have houter := ComputableTidilyInPolyTime.unary_mul.comp (hq1'.prod h2r1)
    have h2out := ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod houter)
    have h2out1 := ComputableTidilyInPolyTime.unary_add.comp (h2out.prod (.const 1))
    exact ComputableTidilyInPolyTime.unary_add.comp (h2out1.prod hrowB)
  have hiter := ComputableTidilyInPolyTime.iterateWith_spec
    (invariant := fun p k st =>
      st.1.length = k ∧ st.2.length ≤ p.1.1 ∧
        (∀ u ∈ st.1, u.length ≤ p.1.1 ∧ ∀ v ∈ u, v.length ≤ p.1.2.length + 1) ∧
        ∀ v ∈ st.2, v.length ≤ p.1.2.length + 1)
    ComputableTidilyInPolyTime.id' hcnt hinit hstep
    (fun p => by
      refine ⟨by simp, by simp, by simp, fun v hv => ?_⟩
      rw [List.mem_map] at hv
      rcases hv with ⟨i, _, rfl⟩
      unfold shoupPowersOneCell
      split_ifs <;> simp)
    (fun p k st hk hinv => by
      have hf_ne : (polyTrim p.1.2).isEmpty = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        rw [ite_eq_left_iff.mpr (fun hnot => absurd h hnot)] at hk
        omega
      unfold shoupPowersStep
      obtain ⟨hl, hrows⟩ := length_shoupLMul p.1.1 p.1.2 st.2 p.2 hf_ne
      refine ⟨by simp [hinv.1], hl.le, fun u hu => ?_,
        fun v hv => (hrows v hv).trans (Nat.le_succ _)⟩
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hinv.2.2.1 u hu
      · exact ⟨hinv.2.1, hinv.2.2.2⟩)
    (ComputableTidilyInPolyTime.polyBounded hboundFn)
    (fun p k st hk hinv => by
      have hk_le : k ≤ p.1.1 + 1 := by
        split_ifs at hk <;> omega
      have hk_len : st.1.length ≤ p.1.1 + 1 := hinv.1.symm ▸ hk_le
      have hel_bound : ∀ u ∈ st.1,
          (encList encBits u).length ≤ p.1.1 * (2 * (p.1.2.length + 1) + 1) := by
        intro u hu
        have hu' := hinv.2.2.1 u hu
        exact (length_encList_le encBits u (b := p.1.2.length + 1)
          (fun v hv => by simp [encBits_apply, hu'.2 v hv])).trans
          (Nat.mul_le_mul_right _ hu'.1)
      have hl1 := (length_encList_le (encList encBits) st.1
        (b := p.1.1 * (2 * (p.1.2.length + 1) + 1)) hel_bound).trans
        (Nat.mul_le_mul_right _ hk_len)
      have hl2 := (length_encList_le encBits st.2 (b := p.1.2.length + 1)
        (fun v hv => by simp [encBits_apply, hinv.2.2.2 v hv])).trans
        (Nat.mul_le_mul_right _ hinv.2.1)
      rw [length_encPair]
      dsimp only
      omega)
  exact (ComputableTidilyInPolyTime.fst (encList (encList encBits)) (encList encBits)).comp hiter.1

end ShoupPowersSection

private def shoupMinPolyRow
    (p : (ℕ × ℕ) × List (List (List Bool))) (idx : ℕ) : List Bool :=
  let i := idx / p.1.2
  let j := idx % p.1.2
  p.2.map fun v => (v.getD i []).getD j false

private def shoupMinPolyBit (x : ((ℕ × ℕ) × List (List (List Bool))) × ℕ) (v : List (List Bool)) :
    Bool :=
  (v.getD (x.2 / x.1.1.2) []).getD (x.2 % x.1.1.2) false

private theorem tidy_shoupMinPolyMatrix :
    ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × List (List (List Bool)) => shoupMinPolyMatrix p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) (encList (encList encBits)))
      (encList encBits) := by
  have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
      (encPair (encList encBits) encUnary) encBits := by fun_prop
  have hbit : ComputableTidilyInPolyTime
      (fun y : (((ℕ × ℕ) × List (List (List Bool))) × ℕ) × List (List Bool) =>
        shoupMinPolyBit y.1 y.2)
      (encPair (encPair (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
        (encList encBits))
      encBool := by
    have hyx := ComputableTidilyInPolyTime.fst
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
      (encList encBits)
    have hyv := ComputableTidilyInPolyTime.snd
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
      (encList encBits)
    have hyp := (ComputableTidilyInPolyTime.fst (encPair encUnary encUnary)
      (encList (encList encBits))).comp
      ((ComputableTidilyInPolyTime.fst (encPair (encPair encUnary encUnary)
        (encList (encList encBits))) encUnary).comp hyx)
    have hym := (ComputableTidilyInPolyTime.snd encUnary encUnary).comp hyp
    have hyidx := (ComputableTidilyInPolyTime.snd
      (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary).comp hyx
    have hdm := ComputableTidilyInPolyTime.unary_divMod.comp (hyidx.prod hym)
    have hi := (ComputableTidilyInPolyTime.fst encUnary encUnary).comp hdm
    have hj := (ComputableTidilyInPolyTime.snd encUnary encUnary).comp hdm
    exact ComputableTidilyInPolyTime.bitsGetDWithInput (hget.tidy.comp (hyv.prod hi)) hj false
  have hrow : ComputableTidilyInPolyTime
      (fun x : ((ℕ × ℕ) × List (List (List Bool))) × ℕ => shoupMinPolyRow x.1 x.2)
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
      encBits := by
    have hpows := (ComputableTidilyInPolyTime.snd (encPair encUnary encUnary)
      (encList (encList encBits))).comp
      (ComputableTidilyInPolyTime.fst
        (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
    have hmap := ComputableTidilyInPolyTime.mapWithInput (f := shoupMinPolyBit) hpows hbit
    exact ComputableTidilyInPolyTime.listToBits.comp hmap
  have hlen : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × List (List (List Bool)) => p.1.1 * p.1.2)
      (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary := by
    have hqm := ComputableTidilyInPolyTime.fst (encPair encUnary encUnary)
      (encList (encList encBits))
    exact ComputableTidilyInPolyTime.unary_mul.comp
      (((ComputableTidilyInPolyTime.fst encUnary encUnary).comp hqm).prod
        ((ComputableTidilyInPolyTime.snd encUnary encUnary).comp hqm))
  have hres := ComputableTidilyInPolyTime.mapWithInput (f := shoupMinPolyRow)
    (ComputableTidilyInPolyTime.range.comp hlen) hrow
  convert hres using 1
  funext p
  unfold shoupMinPolyMatrix shoupMinPolyRow
  rfl

section ShoupIrreducibleSection
attribute [local irreducible] shoupCyclicFactor shoupBetaBounded shoupPowersBounded
  shoupMinPolyMatrix kernelVecBits ordTwoMod qAdicValTwoPowSubOne

private theorem tidy_shoupIrreducibleBits :
    ComputableTidilyInPolyTime shoupIrreducibleBits encUnary encBits := by
  have hcond := tidy_primeGeThree
  have hm := tidy_ordTwoMod
  have hf := tidy_shoupCyclicFactorBounded
  have hβ := tidy_shoupBetaBounded.comp (ComputableTidilyInPolyTime.id'.prod hf)
  have hpows := tidy_shoupPowersBounded.comp ((ComputableTidilyInPolyTime.id'.prod hf).prod hβ)
  have hmat := tidy_shoupMinPolyMatrix.comp ((ComputableTidilyInPolyTime.id'.prod hm).prod hpows)
  have hq1 := ComputableTidilyInPolyTime.unary_add.comp
    (ComputableTidilyInPolyTime.id'.prod (.const 1))
  have hvec := tidy_kernelVecBits.comp (hq1.prod hmat)
  have hite := (ComputableInPolyTime.ite' hcond.computableInPolyTime
    hvec.computableInPolyTime (ComputableInPolyTime.const ([] : List Bool))).tidy
  convert hite using 1
  funext q
  unfold shoupIrreducibleBits
  by_cases h : q.Prime ∧ 3 ≤ q
  · simp only [h, and_self, decide_true, ↓reduceIte, Function.comp_def]
    have hf_eq :
        (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[
          qAdicValTwoPowSubOne q (ordTwoMod q) - 1]
          (berlekampIrreducibleFactor (List.replicate q true)) =
        shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q)) := by
      unfold shoupCyclicFactor
      rfl
    have hspec := shoupCyclicFactor_spec h.1 h.2
    have hlen : (shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q))).length =
        ordTwoMod q + 1 := hspec.2.2.2.2
    have htrim : polyTrim (shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q))) =
        shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q)) := hspec.1
    have hne : (polyTrim (shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q)))).isEmpty =
        false := by
      rw [htrim, List.isEmpty_eq_false_iff]
      intro hnil
      rw [hnil, List.length_nil] at hlen
      omega
    rw [hf_eq, shoupBetaBounded_eq hne, shoupPowersBounded_eq _ hne]
  · simp [h]

end ShoupIrreducibleSection

/-- `shoupIrreducibleBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_shoupIrreducibleBits :
    ComputableInPolyTime shoupIrreducibleBits encUnary encBits :=
  .of_tidy tidy_shoupIrreducibleBits

end Cslib.AffineDisperser.Li

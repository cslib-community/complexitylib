/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Foundations.Data.BitString.List.Operations
public import Complexity.Crypto.Primitives.PRG.NisanWigderson.Derandomization
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Computing the Nisan–Wigderson generator

The derandomization of `BPP` with the Nisan–Wigderson generator is uniform: a deterministic
machine runs the verifier on the output of the generator for every seed and takes the majority
[NisanWigderson1994], [Arora and Barak, Chapter 20][AroraBarak09]. This file certifies that
computation in polynomial time, `Turing.MultiTapeTM.ComputableInPolyTime`.

Polynomial time is measured in the length of the instance, while the seeds have logarithmic
length `ℓ`, the hard function is evaluated on words of logarithmic length `n`, and the hard function
is only computable in time `T n`, exponential in `n`. The certificates therefore take polynomial
bounds on `2 ^ ℓ` and on `T n` as functions of the instance:

* a problem in `Cslib.Complexity.DTIME encBits t` has a Boolean decider computable within
  time and space `O(t n)` (`Cslib.Complexity.exists_computableInO_of_mem_DTIME`);
* such a decider, applied to words cut to a computed length `n`, runs in polynomial time when
  `T n` is polynomially bounded
  (`Turing.MultiTapeTM.ComputableInO.computableInPolyTime_take`);
* the greedy design of `Cslib.Crypto.PRG.NisanWigderson.greedyMasks` is a loop over the `2 ^ ℓ`
  masks of length `ℓ` that keeps at most one more mask per step
  (`Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_greedyMasks`);
* the generator on lists `Cslib.Crypto.PRG.NisanWigderson.listGenerator` reads each block with
  `Cslib.Crypto.PRG.NisanWigderson.restrictMask` and evaluates the hard function
  (`Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_listGenerator`).

The decider `Cslib.Complexity.nwDecider` combines them: it runs a verifier on the output of the
generator for each of the `2 ^ ℓ` seeds and takes the strict majority of the answers
(`Cslib.Complexity.computableInPolyTime_nwDecider`). Its correctness is the subject of
`Cslib.Complexity.BPP_subset_P_of_isAverageCaseHard`.

## Main definitions

* `Cslib.Complexity.nwDecider`: the majority of a verifier over the outputs of the
  Nisan–Wigderson generator on all seeds.

## Main results

* `Cslib.Complexity.exists_computableInO_of_mem_DTIME`: deterministic time classes have
  deciders within the same time and space bound, up to constant factors.
* `Turing.MultiTapeTM.ComputableInO.computableInPolyTime_take`: evaluation of a
  function computable in time `T n` on words of polynomially bounded `T n`.
* `Turing.MultiTapeTM.ComputableInPolyTime.bitsEnumList_of_polyBounded`: enumeration of the
  words of a computed length `ℓ` when `2 ^ ℓ` is polynomially bounded.
* `Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_greedyMasks`,
  `Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_listGenerator`: the greedy design
  and the generator in polynomial time, when `2 ^ ℓ` and `T n` are polynomially bounded.
* `Cslib.Complexity.computableInPolyTime_nwDecider`: the majority over all seeds in
  polynomial time.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 20
-/

@[expose] public section

open Turing Turing.MultiTapeTM

namespace Cslib.Complexity

/-- **Deterministic time classes have deciders within time and space `O(t n)`.** A problem
decided within time `O(t n)`, by a machine with any space bound, has a Boolean decider computable
within time and space `O(t n)`: time bounds space up to a linear factor. -/
theorem exists_computableInO_of_mem_DTIME {A : Set (List Bool)} {t : ℕ → ℕ}
    (h : A ∈ DTIME encBits t) :
    ∃ g : List Bool → Bool, (∀ y, y ∈ A ↔ g y = true) ∧
      ComputableInO g encBits encBool (fun y => t y.length) fun y => t y.length := by
  obtain ⟨c₁, c₂, s, hA⟩ := h
  obtain ⟨g, hg, hgA⟩ := decidableInTimeAndSpace_iff.mp hA
  obtain ⟨c, hg⟩ := hg.exists_space_linear
  set K := c * (c₁ + c₂) + (c₁ + c₂) + c + 1
  refine ⟨g, hgA, ComputableInO.of_bounds hg K (fun y => ?_) (fun y => ?_) fun y => ?_⟩
  · simp only [encBits_apply]
    dsimp only [K]
    ring_nf
    omega
  · simp only [encBits_apply]
    dsimp only [K]
    ring_nf
    omega
  · simp only [encBool_apply, List.length_singleton]
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

end Cslib.Complexity

namespace Turing.MultiTapeTM

/-- **Evaluation on short words.** Let `g` be computable within time and space `O(T n)` on words
of length `n`, for a monotone `T`. Then cutting a word to a computed length `cut x` and applying
`g` is polynomial-time in the pair of `x` and the word, provided `T (cut x)` is polynomially
bounded in the length of `x`. -/
theorem ComputableInO.computableInPolyTime_take {γ : Type} {encIn : γ ↪ List Bool}
    {g : List Bool → Bool} {T : ℕ → ℕ} (hT : Monotone T)
    (hg : ComputableInO g encBits encBool (fun y => T y.length) fun y => T y.length)
    {cut : γ → ℕ} (hcut : ComputableInPolyTime cut encIn encUnary)
    (hbound : PolyBounded (fun x => (encIn x).length) fun x => T (cut x)) :
    ComputableInPolyTime (fun p : γ × List Bool => g (p.2.take (cut p.1)))
      (encPair encIn encBits) encBool := by
  have htake : ComputableInPolyTime (fun p : γ × List Bool => p.2.take (cut p.1))
      (encPair encIn encBits) encBits := by
    have := hcut.comp (ComputableInPolyTime.fst encIn encBits)
    fun_prop
  obtain ⟨T₁, S₁, hT₁, hS₁, h₁⟩ := htake.exists_computableInO
  have hfst : PolyBounded (fun p : γ × List Bool => (encPair encIn encBits p).length)
      fun p => T (cut p.1) :=
    hbound.comp (PolyBounded.self.mono fun p => by simp [length_frame]; omega)
  have hTcut : PolyBounded (fun p : γ × List Bool => (encPair encIn encBits p).length)
      fun p => T (p.2.take (cut p.1)).length :=
    hfst.mono fun p => hT (List.length_take_le _ _)
  exact (hg.comp h₁).computableInPolyTime (hT₁.add hTcut) (hS₁.add hTcut)

namespace ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- Enumerate the words of a computed length `count x` when `2 ^ count x` is polynomially
bounded. -/
theorem bitsEnumList_of_polyBounded {count : γ → ℕ}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hbudget : PolyBounded (fun x => (encIn x).length) fun x => 2 ^ count x) :
    ComputableInPolyTime (fun x => Cslib.BitString.enumList (count x)) encIn
      (encList encBits) := by
  obtain ⟨c, d, h⟩ := hbudget.exists_le
  refine bitsEnumList hcount
    (size := fun n => 3 * (c * (n + 1) ^ d) ^ 2) (by fun_prop) fun x => ?_
  have h₁ : 2 * count x + 1 ≤ 3 * 2 ^ count x := by
    have := Nat.lt_two_pow_self (n := count x)
    omega
  calc 2 ^ count x * (2 * count x + 1) ≤ 2 ^ count x * (3 * 2 ^ count x) :=
        Nat.mul_le_mul_left _ h₁
    _ = 3 * (2 ^ count x) ^ 2 := by ring
    _ ≤ 3 * (c * ((encIn x).length + 1) ^ d) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (h x) 2)

end ComputableInPolyTime

end Turing.MultiTapeTM

namespace Cslib.Crypto.PRG.NisanWigderson

open Turing.MultiTapeTM.ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- Counting the common ones of two masks is polynomial-time. -/
private theorem computableInPolyTime_overlapCount :
    ComputableInPolyTime (fun p : List Bool × List Bool => overlapCount p.1 p.2)
      (encPair encBits encBits) encUnary := by
  unfold overlapCount
  fun_prop

/-- Reading the bits of a word at the ones of a mask is polynomial-time. -/
private theorem computableInPolyTime_restrictMask :
    ComputableInPolyTime (fun p : List Bool × List Bool => restrictMask p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold restrictMask
  fun_prop

private theorem greedyStep_eq (n a : ℕ) (kept : List (List Bool)) (w : List Bool) :
    greedyStep n a kept w =
      if (decide (w.count true = n) && kept.all fun v => decide (overlapCount w v ≤ a)) then
        kept ++ [w] else kept := by
  simp [greedyStep, Bool.and_eq_true, List.all_eq_true]

private theorem computableInPolyTime_greedyStep : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × List (List Bool)) × List Bool => greedyStep p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encUnary encUnary) (encList encBits)) encBits)
    (encList encBits) := by
  simp only [greedyStep_eq]
  have := computableInPolyTime_overlapCount
  fun_prop

/-- **The greedy design in polynomial time.** With computed seed length `seed x`, block size
`block x` and overlap bound `overlap x`, the greedy design is polynomial-time in `x` when
`2 ^ seed x` is polynomially bounded: the loop runs over `2 ^ seed x` masks and keeps at most as
many. -/
theorem computableInPolyTime_greedyMasks {seed block overlap : γ → ℕ}
    (hseed : ComputableInPolyTime seed encIn encUnary)
    (hblock : ComputableInPolyTime block encIn encUnary)
    (hoverlap : ComputableInPolyTime overlap encIn encUnary)
    (hbudget : PolyBounded (fun x => (encIn x).length) fun x => 2 ^ seed x) :
    ComputableInPolyTime (fun x => greedyMasks (seed x) (block x) (overlap x)) encIn
      (encList encBits) := by
  unfold greedyMasks
  refine foldlWith_of_bounded_growth (encA := encBits) (par := fun x => (block x, overlap x))
    (step := fun p kept w => greedyStep p.1 p.2 kept w) (growth := fun x => 2 * seed x + 1)
    (hblock.prod hoverlap)
    (ComputableInPolyTime.bitsEnumList_of_polyBounded hseed hbudget) (.const [])
    computableInPolyTime_greedyStep
    ((hseed.polyBounded.mul (.const 2)).add (.const 1) |>.mono fun x => by simp [Nat.mul_comm])
    fun x kept w hw => ?_
  have hw : w.length = seed x := Cslib.BitString.mem_enumList.1 hw
  simp only [greedyStep]
  split
  · simp [length_encList, hw]
  · exact Nat.le_add_right _ _

/-- **The generator on lists in polynomial time.** Let `g` be computable within time and space
`O(T n)` on words of length `n`, for a monotone `T`. With computed block size `block x`,
masks `masks x` and seed `seed x`, the generator on lists is polynomial-time in `x` when
`T (block x)` is polynomially bounded. -/
theorem computableInPolyTime_listGenerator {g : List Bool → Bool} {T : ℕ → ℕ}
    (hT : Monotone T)
    (hg : ComputableInO g encBits encBool (fun y => T y.length) fun y => T y.length)
    {block : γ → ℕ} {masks : γ → List (List Bool)} {seed : γ → List Bool}
    (hblock : ComputableInPolyTime block encIn encUnary)
    (hmasks : ComputableInPolyTime masks encIn (encList encBits))
    (hseed : ComputableInPolyTime seed encIn encBits)
    (hbudget : PolyBounded (fun x => (encIn x).length) fun x => T (block x)) :
    ComputableInPolyTime (fun x => listGenerator g (block x) (masks x) (seed x)) encIn
      encBits := by
  have heval := ComputableInO.computableInPolyTime_take hT hg
    (hblock.comp (.fst encIn encBits)) (hbudget.comp (PolyBounded.self.mono fun p => by
      simp [length_frame]; omega))
  have hread : ComputableInPolyTime (fun p : γ × List Bool => restrictMask p.2 (seed p.1))
      (encPair encIn encBits) encBits :=
    computableInPolyTime_restrictMask.comp
      ((ComputableInPolyTime.snd encIn encBits).prod (hseed.comp (.fst encIn encBits)))
  have hf : ComputableInPolyTime
      (fun p : γ × List Bool => g ((restrictMask p.2 (seed p.1)).take (block p.1)))
      (encPair encIn encBits) encBool :=
    heval.comp ((ComputableInPolyTime.id' (encIn := encPair encIn encBits)).prod hread)
  exact ComputableInPolyTime.mapToBitsWithInput hmasks hf

end Cslib.Crypto.PRG.NisanWigderson

namespace Cslib.Complexity

open Cslib.Crypto.PRG.NisanWigderson Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-- The decider obtained from a verifier `V` and the Nisan–Wigderson generator of a function `g`
on words: on an instance `x`, it runs `V` on `x` and the output of the generator on each of the
`2 ^ seed x` seeds of `seed x` bits, with the first `out x` masks of the greedy design with blocks
of `block x` positions sharing at most `overlap x` of them, and returns the strict majority of the
answers. -/
def nwDecider (V : α × List Bool → Bool) (g : List Bool → Bool) (seed block overlap out : α → ℕ)
    (x : α) : Bool :=
  BitString.listStrictMajority ((BitString.enumList (seed x)).map fun z =>
    V (x, listGenerator g (block x) ((greedyMasks (seed x) (block x) (overlap x)).take (out x)) z))

/-- **The Nisan–Wigderson decider in polynomial time.** Let `V` be polynomial-time and let `g` be
computable within time and space `O(T n)` on words of length `n`, for a monotone `T`. With
polynomial-time unary parameters, `nwDecider` is polynomial-time when `2 ^ seed x` and
`T (block x)` are polynomially bounded in the length of the instance. -/
theorem computableInPolyTime_nwDecider {V : α × List Bool → Bool} {g : List Bool → Bool}
    {T : ℕ → ℕ} {seed block overlap out : α → ℕ}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (hT : Monotone T)
    (hg : ComputableInO g encBits encBool (fun y => T y.length) fun y => T y.length)
    (hseed : ComputableInPolyTime seed enc encUnary)
    (hblock : ComputableInPolyTime block enc encUnary)
    (hoverlap : ComputableInPolyTime overlap enc encUnary)
    (hout : ComputableInPolyTime out enc encUnary)
    (hseedBudget : PolyBounded (fun x => (enc x).length) fun x => 2 ^ seed x)
    (hblockBudget : PolyBounded (fun x => (enc x).length) fun x => T (block x)) :
    ComputableInPolyTime (nwDecider V g seed block overlap out) enc encBool := by
  have hfst : ∀ {u : α → ℕ}, PolyBounded (fun x => (enc x).length) u →
      PolyBounded (fun p : α × List Bool => (encPair enc encBits p).length) fun p => u p.1 :=
    fun hu => hu.comp (PolyBounded.self.mono fun p => by simp [length_frame]; omega)
  have hmasks : ComputableInPolyTime
      (fun p : α × List Bool => (greedyMasks (seed p.1) (block p.1) (overlap p.1)).take (out p.1))
      (encPair enc encBits) (encList encBits) := by
    have := computableInPolyTime_greedyMasks (hseed.comp (.fst enc encBits))
      (hblock.comp (.fst enc encBits)) (hoverlap.comp (.fst enc encBits)) (hfst hseedBudget)
    fun_prop
  have hgen := computableInPolyTime_listGenerator hT hg (hblock.comp (.fst enc encBits))
    hmasks (.snd enc encBits) (hfst hblockBudget)
  have hvote : ComputableInPolyTime (fun p : α × List Bool => V (p.1,
      listGenerator g (block p.1) ((greedyMasks (seed p.1) (block p.1) (overlap p.1)).take
        (out p.1)) p.2)) (encPair enc encBits) encBool :=
    hV.comp ((fst enc encBits).prod hgen)
  exact bitsStrictMajorityWithInput (mapToBitsWithInput
    (f := fun x z => V (x, listGenerator g (block x)
      ((greedyMasks (seed x) (block x) (overlap x)).take (out x)) z))
    (bitsEnumList_of_polyBounded hseed hseedBudget) hvote)

end Cslib.Complexity

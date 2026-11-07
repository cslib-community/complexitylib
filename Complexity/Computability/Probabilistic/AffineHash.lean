/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.LinearHash
public import Complexity.Probability.BitString.AffineHash.ThreeWise
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Probabilistic.Sampling

/-!
# Plain polynomial-time Boolean affine hashing and prefix-collision conditioning

This module certifies `Cslib.BitString.LinearHash.wordAffineHash` and
`Cslib.BitString.LinearHash.wordAdjustAffineSeed` directly in the plain `ComputableInPolyTime`
calculus, together with uniform strict-PPT sampling of prefix-colliding affine seeds.

## Main results

* `Cslib.BitString.LinearHash.computableInPolyTime_wordAffineHash`: plain polynomial-time
  certificate for `wordAffineHash`.
* `Cslib.BitString.LinearHash.computableInPolyTime_wordAdjustAffineSeed`: plain polynomial-time
  certificate for `wordAdjustAffineSeed`.
* `Cslib.BitString.LinearHash.isPPTOn_sampleAdjustedAffineSeed`: uniform strict-PPT sampler
  drawing a fresh `(k * n + k)`-bit affine seed and projecting it onto prefix collisions of `y` and
  `y₀`.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 4.2, Theorem 4.5, pp. 21–25][HHRVW2020]
-/

public section

namespace Cslib.BitString.LinearHash

open Cslib.Probability Turing.MultiTapeTM

private theorem computableInPolyTime_pairBits {α : Type} {encode : α ↪ List Bool}
    {u v : α → List Bool}
    (hu : ComputableInPolyTime u encode encBits)
    (hv : ComputableInPolyTime v encode encBits) :
    ComputableInPolyTime (fun a => [u a, v a]) encode (encList encBits) := by
  simpa only [Function.comp_def, List.nil_append, List.cons_append] using
    (ComputableInPolyTime.snoc encBits).comp
      (((ComputableInPolyTime.snoc encBits).comp
        ((ComputableInPolyTime.const []).prod hu)).prod hv)

/-- Evaluate `wordAffineHash` in plain polynomial time, with output dimension supplied in unary. -/
@[fun_prop]
theorem computableInPolyTime_wordAffineHash {α : Type} {encode : α ↪ List Bool}
    {count : α → ℕ} {seed input : α → List Bool}
    (hcount : ComputableInPolyTime count encode encUnary)
    (hseed : ComputableInPolyTime seed encode encBits)
    (hinput : ComputableInPolyTime input encode encBits) :
    ComputableInPolyTime (fun a => wordAffineHash (count a) (seed a) (input a))
      encode encBits := by
  have hmatLen : ComputableInPolyTime (fun a => count a * (input a).length) encode encUnary :=
    ComputableInPolyTime.unary_mul.comp
      (hcount.prod (ComputableInPolyTime.length_bits_comp hinput))
  have hmat := ComputableInPolyTime.bitsTakeWithInput hseed hmatLen
  have hshift := ComputableInPolyTime.bitsDropWithInput hseed hmatLen
  have hlin := computableInPolyTime_wordHash hcount hmat hinput
  exact ComputableInPolyTime.bitsXorWithInput hcount
    (computableInPolyTime_pairBits hlin hshift)

/-- Project an affine seed onto the prefix-collision subgroup in plain polynomial time, with
dimensions `k`, `n`, and `r` supplied in unary. -/
@[fun_prop]
theorem computableInPolyTime_wordAdjustAffineSeed {α : Type} {encode : α ↪ List Bool}
    {k n r : α → ℕ} {y y₀ seed : α → List Bool}
    (hk : ComputableInPolyTime k encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hr : ComputableInPolyTime r encode encUnary)
    (hy : ComputableInPolyTime y encode encBits)
    (hy₀ : ComputableInPolyTime y₀ encode encBits)
    (hseed : ComputableInPolyTime seed encode encBits) :
    ComputableInPolyTime
      (fun a => wordAdjustAffineSeed (k a) (n a) (r a) (y a) (y₀ a) (seed a))
      encode encBits := by
  have hdiff : ComputableInPolyTime (fun a => listXor (n a) [y a, y₀ a]) encode encBits :=
    ComputableInPolyTime.bitsXorWithInput hn (computableInPolyTime_pairBits hy hy₀)
  have hidx : ComputableInPolyTime (fun a => (listXor (n a) [y a, y₀ a]).idxOf true)
      encode encUnary :=
    ComputableInPolyTime.idxOfWithInput
      (ComputableInPolyTime.bitsToList.comp hdiff) (ComputableInPolyTime.const true)
  have hmask : ComputableInPolyTime
      (fun a => listSingle (n a) ((listXor (n a) [y a, y₀ a]).idxOf true)) encode encBits :=
    ComputableInPolyTime.bitsSingle.comp (hn.prod hidx)
  have hkn : ComputableInPolyTime (fun a => k a * n a) encode encUnary :=
    ComputableInPolyTime.unary_mul.comp (hk.prod hn)
  have hmatBits := ComputableInPolyTime.bitsTakeWithInput hseed hkn
  have hshiftBits := ComputableInPolyTime.bitsDropWithInput hseed hkn
  have hshift := ComputableInPolyTime.bitsRowWithInput hk (ComputableInPolyTime.const 0) hshiftBits
  have hfst := ComputableInPolyTime.fst encode encUnary
  have hsnd := ComputableInPolyTime.snd encode encUnary
  have hrow : ComputableInPolyTime
      (fun p : α × ℕ => listRow (n p.1) p.2 ((seed p.1).take (k p.1 * n p.1)))
      (encPair encode encUnary) encBits :=
    ComputableInPolyTime.bitsRowWithInput (hn.comp hfst) hsnd (hmatBits.comp hfst)
  have hdot : ComputableInPolyTime
      (fun p : α × ℕ =>
        ((listRow (n p.1) p.2 ((seed p.1).take (k p.1 * n p.1))).zipWith Bool.and
          (listXor (n p.1) [y p.1, y₀ p.1])).foldl Bool.xor false)
      (encPair encode encUnary) encBool :=
    ComputableInPolyTime.bitsFoldlWithInput Bool.xor
      (ComputableInPolyTime.bitsZipWithInput Bool.and hrow (hdiff.comp hfst))
      (ComputableInPolyTime.const false)
  have hlt : ComputableInPolyTime (fun p : α × ℕ => decide (p.2 < r p.1))
      (encPair encode encUnary) encBool :=
    ComputableInPolyTime.unary_lt.comp (hsnd.prod (hr.comp hfst))
  have hcond : ComputableInPolyTime
      (fun p : α × ℕ =>
        decide (p.2 < r p.1) &&
          ((listRow (n p.1) p.2 ((seed p.1).take (k p.1 * n p.1))).zipWith Bool.and
            (listXor (n p.1) [y p.1, y₀ p.1])).foldl Bool.xor false)
      (encPair encode encUnary) encBool :=
    ComputableInPolyTime.bool_and.comp (hlt.prod hdot)
  have hadjRow : ComputableInPolyTime
      (fun p : α × ℕ =>
        listXor (n p.1)
          [listRow (n p.1) p.2 ((seed p.1).take (k p.1 * n p.1)),
           listSingle (n p.1) ((listXor (n p.1) [y p.1, y₀ p.1]).idxOf true)])
      (encPair encode encUnary) encBits :=
    ComputableInPolyTime.bitsXorWithInput (hn.comp hfst)
      (computableInPolyTime_pairBits hrow (hmask.comp hfst))
  have hstep := hcond.ite hadjRow hrow
  have hrows := ComputableInPolyTime.mapWithInput
    (f := fun a i =>
      let diff := listXor (n a) [y a, y₀ a]
      let mask := listSingle (n a) (diff.idxOf true)
      let row := listRow (n a) i ((seed a).take (k a * n a))
      let dot := (row.zipWith Bool.and diff).foldl Bool.xor false
      if decide (i < r a) && dot then listXor (n a) [row, mask] else row)
    (ComputableInPolyTime.range.comp hk) hstep
  exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsFlatten hrows) hshift

/-- Sample a fresh `(k * n + k)`-bit affine seed and project it onto the prefix-collision subgroup
of `y` and `y₀` in uniform strict polynomial time. -/
theorem isPPTOn_sampleAdjustedAffineSeed {α : Type} {encode : α ↪ List Bool}
    {k n r : α → ℕ} {y y₀ : α → List Bool}
    (hk : ComputableInPolyTime k encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hr : ComputableInPolyTime r encode encUnary)
    (hy : ComputableInPolyTime y encode encBits)
    (hy₀ : ComputableInPolyTime y₀ encode encBits) :
    IsPPTOn encode encBits (fun a => do
      let rawSeed ← sampleList (k a * n a + k a)
      return wordAdjustAffineSeed (k a) (n a) (r a) (y a) (y₀ a) rawSeed) := by
  have hseedLen : ComputableInPolyTime (fun a => k a * n a + k a) encode encUnary :=
    ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.unary_mul.comp (hk.prod hn)).prod hk)
  have hfst := ComputableInPolyTime.fst encode encBits
  have hsnd := ComputableInPolyTime.snd encode encBits
  have hcallback := computableInPolyTime_wordAdjustAffineSeed
    (hk.comp hfst) (hn.comp hfst) (hr.comp hfst) (hy.comp hfst) (hy₀.comp hfst) hsnd
  simpa only [bind_pure_comp, Function.comp_def] using IsPPTOn.of_seeded hseedLen hcallback

end Cslib.BitString.LinearHash

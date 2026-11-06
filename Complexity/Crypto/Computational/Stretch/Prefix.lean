/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Stretch
import Complexity.Probability.PMF.Map

/-!
# Prefixes of the emitted PRG stream

`forwardIterate` appends a reversed final seed after its emitted bits. Under the global one-bit
expansion promise, taking exactly the number of rounds discards that seed. These emitted prefixes
have exact length and agree across different stopping times. The complete `forwardIterate` output
is not claimed to be prefix-consistent.

## Main results

* `PRGStretch.length_take_forwardIterate`: exactly one emitted bit per round.
* `PRGStretch.take_forwardIterate_prefix`: increasing the round count preserves emitted prefixes.
* `PRGStretch.polyTime_take_forwardIterate`: native computation on a seed and unary round count.
* `PRGStretch.indistinguishable_take_forwardIterate`: any native polynomial-length emitted prefix
  is computationally indistinguishable from a uniform word of that length.

## References

These are consequences of the existing stretch construction and security theorem. The emitted
prefix is the pad used by the stream-cipher construction in [BonehShoup2023], Section 3.2,
Theorem 3.1, printed pp. 48–51. This module supplies the prefix prerequisite, not a cipher-security
theorem or a message-domain extension.
-/

@[expose] public section

namespace Cslib.Crypto.PRGStretch

open Probability BitString Turing.MultiTapeTM

/-- Taking the emitted portion discards the final seed, including at zero seed width or rounds. -/
theorem length_take_forwardIterate {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    ((forwardIterate generator count seed).take count).length = count := by
  rw [List.length_take, length_forwardIterate_of_forall hlen]
  exact Nat.min_eq_left (by omega)

private theorem length_emitted {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    (((List.range count).map fun i => emitBit generator (seedAt generator seed i)).flatten).length =
      count := by
  have hbit (s : List Bool) : (emitBit generator s).length = 1 :=
    length_emitBit_of_eq (fun t ht => by rw [hlen, ht]) rfl
  simp [List.length_flatten, List.map_map, Function.comp_def, hbit]

/-- Only the emitted prefix is consistent across stopping times; the final seed is excluded. -/
theorem take_forwardIterate_prefix {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool)
    {count total : ℕ} (hle : count ≤ total) :
    (forwardIterate generator total seed).take count =
      (forwardIterate generator count seed).take count := by
  rw [forwardIterate_eq, forwardIterate_eq,
    List.take_left' (length_emitted hlen seed count)]
  rw [show total = count + (total - count) by omega, List.range_add,
    List.map_append, List.flatten_append, List.append_assoc]
  exact List.take_left' (length_emitted hlen seed count)

/-- The number of rounds is supplied in unary independently of the seed width. -/
@[fun_prop]
theorem polyTime_take_forwardIterate {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = s.length + 1) :
    ComputableInPolyTime
      (fun p : List Bool × ℕ => (forwardIterate generator p.2 p.1).take p.2)
      (encPair encBits encUnary) encBits := by
  have hi : ComputableInPolyTime
      (fun p : List Bool × ℕ => iterate generator p.1.length p.2 p.1)
      (encPair encBits encUnary) encBits :=
    polyTime_iterate (hgenerator.comp (ComputableInPolyTime.snd _ _))
      (by fun_prop) (by fun_prop) (by fun_prop)
  have heq (seed : List Bool) (count : ℕ) :
      forwardIterate generator count seed = (iterate generator seed.length count seed).reverse := by
    rw [← reverse_forwardIterate_eq_iterate_of_forall hlen, List.reverse_reverse]
  simp_rw [heq]
  fun_prop

/-- Polynomially many emitted bits are pseudorandom at the original seed/security parameter.
The length schedule is uniform and may be zero; no new generator-security notion is used. -/
theorem indistinguishable_take_forwardIterate {generator : List Bool → List Bool}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1)) {count : ℕ → ℕ}
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    ComputationallyIndistinguishable
      (fun n => (uniformList n).map
        (fun seed => (forwardIterate generator (count n) seed).take (count n)))
      (fun n => uniformList (count n)) := by
  have h := (indistinguishable hgenerator hcount).map
    (f := fun n word => word.reverse.take (count n)) (by fun_prop)
  convert h using 1
  · funext n
    simp only [generatorEnsemble, PMF.map_comp, Function.comp_def]
    apply PMF.map_congr_on_support
    intro seed hseed
    have hs := length_of_mem_support_uniformList hseed
    simp only [stretch, hs]
    have heq := reverse_forwardIterate_eq_iterate_of_forall hgenerator.length_eq seed (count n)
    rw [hs] at heq
    rw [← heq, List.reverse_reverse]
  · funext n
    symm
    change (uniformList (n + count n)).map ((List.take (count n)) ∘ List.reverse) = _
    rw [← PMF.map_comp,
      uniformList_map_of_bijective List.reverse List.reverse_involutive.bijective
        (fun _ => List.length_reverse), uniformList_take (by omega)]

end Cslib.Crypto.PRGStretch

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Sampling
import Mathlib.Data.Finset.Sort

/-!
# The queries of the Nisan–Wigderson reconstruction

With its random choices fixed, the guess of the Nisan–Wigderson reconstruction
(`Cslib.Crypto.PRG.NisanWigderson.trialGuess`) reads the hard function `f` only through the
output bits at the positions before `t.pos`. With the seed bits outside the `t.pos`-th block
fixed, output bit `j` is `f` at the bits of the seed in the `j`-th block. Only the at most `a`
of these bits that lie in the `t.pos`-th block vary with the input, so output bit `j` takes the
values of `f` at at most `2 ^ a` points. These are the *queries* of the trial
(`Cslib.Crypto.PRG.NisanWigderson.trialPoints`): at most `m 2 ^ a` points
(`Cslib.Crypto.PRG.NisanWigderson.length_trialPoints_le`), determined by the trial and the design
alone, at which `f` determines the whole guess
(`Cslib.Crypto.PRG.NisanWigderson.trialGuess_congr`). A learner with membership queries can
therefore run the reconstruction by querying these points; this is step 4 of the reconstruction
algorithm of [Carmosino, Impagliazzo, Kabanets and Kolokolova, Section
2.4][CarmosinoImpagliazzoKabanetsKolokolova2016].

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.trialPoints`: the queries of a trial.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.length_trialPoints_le`: a trial makes at most `m 2 ^ a`
  queries.
* `Cslib.Crypto.PRG.NisanWigderson.restrict_extend_mem_trialPoints`: the inputs of the earlier
  output bits are queries.
* `Cslib.Crypto.PRG.NisanWigderson.trialGuess_congr`: the guess of a trial depends only on the
  values of `f` at its queries.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
-/

public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Finset

variable {ℓ n a m : ℕ}

/-- The *queries* of the trial `t`: for each position `j` before `t.pos` and each assignment to
the input bits in `D.overlap t.pos j`, the input `D.restrict j (D.extend t.pos x t.seed)` of output
bit `j`, where `x` carries the assignment on the overlap and `false` elsewhere. An assignment is
listed as the set of overlap positions where it is `true`, a sublist of the sorted overlap. -/
def trialPoints (D : Design ℓ n a m) (t : Trial ℓ m) : List (Fin n → Bool) :=
  (List.finRange t.pos).flatMap fun j =>
    ((D.overlap t.pos (Fin.castLE t.pos.isLt.le j)).sort (· ≤ ·)).sublists.map fun s =>
      D.restrict (Fin.castLE t.pos.isLt.le j) (D.extend t.pos (fun k => decide (k ∈ s)) t.seed)

variable (D : Design ℓ n a m)

/-- **Query count.** A trial makes at most `m 2 ^ a` queries: at most `2 ^ a` for each of the at
most `m` earlier positions. -/
theorem length_trialPoints_le (t : Trial ℓ m) : (trialPoints D t).length ≤ m * 2 ^ a := by
  rw [trialPoints, List.length_flatMap]
  calc ((List.finRange t.pos).map fun j => _).sum
      ≤ ((List.finRange t.pos).map fun _ => (2 ^ a : ℕ)).sum := by
        refine List.sum_le_sum fun j _ => ?_
        simp only [List.length_map, List.length_sublists, length_sort]
        exact Nat.pow_le_pow_right two_pos <| D.card_overlap_le <|
          Fin.ne_of_gt (show Fin.castLE t.pos.isLt.le j < t.pos from j.isLt)
    _ = (t.pos : ℕ) * 2 ^ a := by simp
    _ ≤ m * 2 ^ a := Nat.mul_le_mul_right _ t.pos.isLt.le

/-- **The earlier output bits read only queries.** For every input `x` and every position `j`
before `t.pos`, the input of output bit `j` on the seed `D.extend t.pos x t.seed` is a query of
the trial `t`. -/
theorem restrict_extend_mem_trialPoints (t : Trial ℓ m) (j : Fin t.pos) (x : Fin n → Bool) :
    D.restrict (Fin.castLE t.pos.isLt.le j) (D.extend t.pos x t.seed) ∈ trialPoints D t := by
  set O := D.overlap t.pos (Fin.castLE t.pos.isLt.le j)
  simp only [trialPoints, List.mem_flatMap, List.mem_finRange, List.mem_map, List.mem_sublists,
    true_and]
  refine ⟨j, (O.sort (· ≤ ·)).filter fun k => x k, List.filter_sublist, ?_⟩
  refine D.dependsOn_restrict_extend t.pos _ t.seed fun k hk => ?_
  have hk' : k ∈ O.sort (· ≤ ·) := (mem_sort _).2 hk
  simp [List.mem_filter, hk']

/-- **The guess reads `f` only at the queries.** Two hard functions that agree at the queries of
the trial `t` give the same guess. -/
theorem trialGuess_congr {f f' : (Fin n → Bool) → Bool} {test : (Fin m → Bool) → Bool}
    {t : Trial ℓ m} (h : ∀ x ∈ trialPoints D t, f x = f' x) :
    trialGuess D f test t = trialGuess D f' test t := by
  funext x
  simp only [trialGuess]
  congr 1
  funext j
  simp only [Fin.take_apply, generator_apply]
  exact h _ (restrict_extend_mem_trialPoints D t j x)

end Cslib.Crypto.PRG.NisanWigderson

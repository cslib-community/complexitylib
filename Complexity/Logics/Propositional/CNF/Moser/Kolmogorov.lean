/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Moser.Compression
public import Complexity.Computability.Kolmogorov.Incompressibility

/-!
# Moser's algorithm and Kolmogorov complexity

Fortnow's exposition of Moser's argument [Fortnow2009] is phrased with Kolmogorov complexity: a
random tape cannot be compressed, but a tape on which the algorithm runs for long can be described
by the final assignment and the execution log, which is shorter. This file states the argument for
an explicit description method (`Cslib.Kolmogorov.DescriptionMethod`).

For a CNF formula `φ` on `n` variables and parameters `k` and `L`,
`Cslib.Logic.PL.Moser.descriptionMethod` reads a program as an assignment (its first `n` bits)
followed by an execution log. It replays the log to find the number `t` of resamplings and outputs
the first `n + t k` bits of the tape recovered by `Cslib.Logic.PL.Moser.decode`. If `φ` is an exact
`k`-CNF in which every clause shares a variable with fewer than `2 ^ L` other clauses, every tape
word `y` of length `n + t k` on which a run uses up its budget of `t` resamplings has complexity at
most `n + m + t (L + 2)` (`Cslib.Logic.PL.Moser.ecomplexity_le_of_exhausts`), where `m` is the
number of clauses. Taking `L = k - 3`: if the clauses have degree below `2 ^ (k - 3)` and `y` has
complexity at least `|y| - c`, a run on `y` with a budget `t > m + c` stops with a satisfying
assignment (`Cslib.Logic.PL.Moser.not_exhausts_of_length_sub_le_ecomplexity`,
`Cslib.Logic.PL.Moser.eval_final_of_length_sub_le_ecomplexity`). Since some string of every length
is incompressible (`Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_le_ecomplexity`), for every
`t > m` the run on some tape word of length `n + t k` succeeds
(`Cslib.Logic.PL.Moser.exists_eval_final_of_degree_lt`). This is Fortnow's argument, with the
encoding of `Complexity.Logics.Propositional.CNF.Moser.Compression`.

The complexity here is relative to a description method that depends on `φ`, `k` and `L`. Fortnow
takes a tape that is Kolmogorov random relative to the formula and the parameters, that is, for a
universal machine given them as auxiliary input. Transferring the bound to the conditional
complexity `Cslib.Kolmogorov.condPlain` up to an additive constant independent of `φ` requires
implementing the decoder as a multi-tape Turing machine that receives `φ`, which is not done here.

## Main definitions

* `Cslib.Logic.PL.Moser.description`: the description of a tape by a run.
* `Cslib.Logic.PL.Moser.descriptionMethod`: the description method of the decoder.

## Main results

* `Cslib.Logic.PL.Moser.decodeWord_description`, `Cslib.Logic.PL.Moser.descriptionMethod_produces`:
  the decoder outputs the tape word.
* `Cslib.Logic.PL.Moser.ecomplexity_le_of_exhausts`: tapes using up the budget are compressible.
* `Cslib.Logic.PL.Moser.not_exhausts_of_length_sub_le_ecomplexity`,
  `Cslib.Logic.PL.Moser.eval_final_of_length_sub_le_ecomplexity`: on a nearly incompressible tape
  the algorithm stops with a satisfying assignment.
* `Cslib.Logic.PL.Moser.exists_eval_final_of_degree_lt`: Fortnow's argument.

## References

* [L. Fortnow, *A Kolmogorov Complexity Proof of the Lovász Local Lemma*][Fortnow2009]
* [R. A. Moser, *A constructive proof of the Lovász Local Lemma*][Moser2009]
-/

public section

namespace Cslib.Logic.PL.Moser

open Cslib.Kolmogorov

variable {n : ℕ} (φ : CNF (Fin n))

/-- The tape word decoded from a program: the program is an assignment (its first `n` bits)
followed by an execution log. Replaying the log gives the number `t` of resamplings, and the output
is the first `n + t k` bits of the recovered tape. -/
def decodeWord (k L : ℕ) (p : List Bool) : List Bool :=
  List.ofFn fun i : Fin (n + (replay φ L ⟨[], 0, []⟩ (p.drop n)).trace.length * k) =>
    decode φ k L (fun v : Fin n => p.getD v false) (p.drop n) i

/-- **The decoder as a description method**: programs are decoded by `decodeWord`. -/
def descriptionMethod (k L : ℕ) : DescriptionMethod (List Bool) where
  run p := Computation.pure (decodeWord φ k L p)

/-- The description of the tape `x` by a run with a budget of `t` resamplings: the final
assignment followed by the execution log. -/
@[expose] def description (k t L : ℕ) (x : ℕ → Bool) : List Bool :=
  List.ofFn (final φ k t x).assignment ++ log φ k t L x (fuel φ t)

variable {φ}

/-- A description has at most `n + m + t (L + 2)` bits. -/
theorem length_description_le (k t L : ℕ) (x : ℕ → Bool) :
    (description φ k t L x).length ≤ n + φ.length + t * (L + 2) := by
  rw [description, List.length_append, List.length_ofFn, Nat.add_assoc]
  exact Nat.add_le_add_left (length_log_le k t L x _) n

/-- A program describes exactly the word it decodes to. -/
theorem descriptionMethod_produces_iff {k L : ℕ} {p y : List Bool} :
    (descriptionMethod φ k L).Produces p y ↔ decodeWord φ k L p = y := by
  rw [eq_comm]
  exact Computation.mem_pure_iff _ _

/-- **Decoding.** If every clause shares a variable with fewer than `2 ^ L` other clauses, the
description of a tape word `y` by a run that uses up its budget of `t` resamplings, with the tape
`y` padded by `false`, decodes to `y`. -/
theorem decodeWord_description {k L : ℕ} (hφ : φ.IsExactDistinct k)
    (hL : ∀ c : Fin φ.length, degree φ c < 2 ^ L) {t : ℕ} {y : List Bool}
    (hy : y.length = n + t * k) (hex : Exhausts φ k t fun i => y.getD i false) :
    decodeWord φ k L (description φ k t L fun i => y.getD i false) = y := by
  set x : ℕ → Bool := fun i => y.getD i false
  have hdrop : (description φ k t L x).drop n = log φ k t L x (fuel φ t) := by
    rw [description, List.drop_left' (List.length_ofFn)]
  have hassign : (fun v : Fin n => (description φ k t L x).getD v false) =
      (final φ k t x).assignment := by
    funext v
    rw [description, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp),
      List.getElem?_ofFn]
    simp
  have htrace : (replay φ L ⟨[], 0, []⟩ (log φ k t L x (fuel φ t))).trace.length = t := by
    have h := replay_log hL k t x (fuel φ t) []
    rw [List.append_nil, replay_nil] at h
    rw [h]
    exact length_trace_final_eq hex
  refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
  · rw [hy, decodeWord, List.length_ofFn, hdrop, htrace]
  · have hi : i < n + (run φ k t x (fuel φ t)).trace.length * k := by
      change i < n + (final φ k t x).trace.length * k
      rw [length_trace_final_eq hex, ← hy]
      exact h₂
    simp only [decodeWord, List.getElem_ofFn, hassign, hdrop, Fin.val_cast]
    refine Eq.trans (decode_run hφ hL t x (fuel φ t) i hi) ?_
    simp only [x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

/-- The description of a tape word by a run that uses up its budget describes it. -/
theorem descriptionMethod_produces {k L : ℕ} (hφ : φ.IsExactDistinct k)
    (hL : ∀ c : Fin φ.length, degree φ c < 2 ^ L) {t : ℕ} {y : List Bool}
    (hy : y.length = n + t * k) (hex : Exhausts φ k t fun i => y.getD i false) :
    (descriptionMethod φ k L).Produces (description φ k t L fun i => y.getD i false) y :=
  descriptionMethod_produces_iff.2 (decodeWord_description hφ hL hy hex)

/-- **Tapes using up the budget are compressible.** If every clause of an exact `k`-CNF shares a
variable with fewer than `2 ^ L` other clauses, a tape word `y` of length `n + t k` on which the run
uses up its budget of `t` resamplings has complexity at most `n + m + t (L + 2)` relative to the
decoder. -/
theorem ecomplexity_le_of_exhausts {k L : ℕ} (hφ : φ.IsExactDistinct k)
    (hL : ∀ c : Fin φ.length, degree φ c < 2 ^ L) {t : ℕ} {y : List Bool}
    (hy : y.length = n + t * k) (hex : Exhausts φ k t fun i => y.getD i false) :
    (descriptionMethod φ k L).ecomplexity y ≤ (n + φ.length + t * (L + 2) : ℕ) :=
  ((descriptionMethod φ k L).ecomplexity_le_length (descriptionMethod_produces hφ hL hy hex)).trans
    (Nat.cast_le.2 (length_description_le k t L _))

/-- **Nearly incompressible tapes do not use up the budget** [Fortnow2009]. If every clause of an
exact `k`-CNF shares a variable with fewer than `2 ^ (k - 3)` other clauses and a tape word `y` has
complexity at least `|y| - c` relative to the decoder, a run on `y` with a budget of `t > m + c`
resamplings does not use it up. -/
theorem not_exhausts_of_length_sub_le_ecomplexity {k : ℕ} (hk : 3 ≤ k)
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) {t c : ℕ}
    (ht : φ.length + c < t) {y : List Bool} (hy : y.length = n + t * k)
    (hc : (y.length - c : ℕ) ≤ (descriptionMethod φ k (k - 3)).ecomplexity y) :
    ¬Exhausts φ k t fun i => y.getD i false := by
  intro hex
  have h := Nat.cast_le.1 (hc.trans (ecomplexity_le_of_exhausts hφ hdeg hy hex))
  have hk' : t * (k - 3 + 2) + t = t * k := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  omega

/-- **On a nearly incompressible tape the algorithm succeeds** [Fortnow2009]. If every clause of an
exact `k`-CNF shares a variable with fewer than `2 ^ (k - 3)` other clauses and a tape word `y` of
length `n + t k` has complexity at least `|y| - c` relative to the decoder, with `t > m + c`, the
run on `y` ends with a satisfying assignment. -/
theorem eval_final_of_length_sub_le_ecomplexity {k : ℕ} (hk : 3 ≤ k)
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) {t c : ℕ}
    (ht : φ.length + c < t) {y : List Bool} (hy : y.length = n + t * k)
    (hc : (y.length - c : ℕ) ≤ (descriptionMethod φ k (k - 3)).ecomplexity y) :
    φ.eval (final φ k t fun i => y.getD i false).assignment = true :=
  eval_final_of_not_exhausts (hφ.ne_nil (by omega))
    (not_exhausts_of_length_sub_le_ecomplexity hk hφ hdeg ht hy hc)

/-- **Fortnow's argument** [Fortnow2009]: if every clause of an exact `k`-CNF shares a variable with
fewer than `2 ^ (k - 3)` other clauses and `t > m`, the run on an incompressible tape word of length
`n + t k` ends with a satisfying assignment. -/
theorem exists_eval_final_of_degree_lt {k : ℕ} (hk : 3 ≤ k) (hφ : φ.IsExactDistinct k)
    (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) {t : ℕ} (ht : φ.length < t) :
    ∃ y : List Bool, y.length = n + t * k ∧
      φ.eval (final φ k t fun i => y.getD i false).assignment = true :=
  let ⟨y, hy, hc⟩ := (descriptionMethod φ k (k - 3)).exists_length_eq_le_ecomplexity (n + t * k)
  ⟨y, hy, eval_final_of_length_sub_le_ecomplexity (c := 0) hk hφ hdeg ht hy (by rwa [hy])⟩

end Cslib.Logic.PL.Moser

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.AcceptCount
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Verifiers reading a prefix of their random string

To show that a class defined by verifiers is closed under a polynomial-time reduction `f`, one runs
the verifier `V` of the target problem on the reduced instance `f a`. On that instance `V` reads
`q(|f a|)` random or certificate bits, while the strings given for an instance `a` must have a
length fixed by `|a|`. The new verifier therefore reads strings of a polynomial length
`P(|a|) ≥ q(|f a|)` and passes their prefix of length `q(|f a|)` to `V`
(`Cslib.Complexity.exists_truncated_verifier`). The verifier's output type is arbitrary.

Every prefix extends to the same number of longer strings, so counting through a prefix multiplies
the number of accepted strings by a power of two
(`Cslib.Complexity.acceptCount_eq_two_pow_mul_of_take`), and a bound on the fraction of strings with
a property survives (`Cslib.BitString.mul_two_pow_le_mul_card_filter_take`).

## Main results

* `Cslib.Complexity.exists_truncated_verifier`: a polynomial-time verifier that runs `V` on the
  reduced instance and a prefix of a polynomially long string.
* `Cslib.Complexity.acceptCount_eq_two_pow_mul_of_take`: accepted strings counted through a prefix.
* `Cslib.BitString.mul_two_pow_le_mul_card_filter_take`: a fraction bound carried through a
  prefix.
-/

public section

namespace Cslib.BitString

open Finset

/-- **Fraction bounds through a prefix.** If at least a `c / d` fraction of the strings of length
`k` satisfy `g`, then at least a `c / d` fraction of the strings of length `K ≥ k` have a prefix of
length `k` satisfying `g`. -/
theorem mul_two_pow_le_mul_card_filter_take {k K : ℕ} (hk : k ≤ K) (g : List Bool → Prop)
    [DecidablePred g] {c d : ℕ} (h : c * 2 ^ k ≤ d * #{r : Fin k → Bool | g (List.ofFn r)}) :
    c * 2 ^ K ≤ d * #{r : Fin K → Bool | g ((List.ofFn r).take k)} := by
  rw [card_filter_take hk g, ← pow_sub_mul_pow 2 hk, mul_left_comm c, mul_left_comm d]
  exact Nat.mul_le_mul_left _ h

end Cslib.BitString

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}

/-- **Running a verifier on a prefix.** For a polynomial-time map `f` and a polynomial-time
verifier `V` reading `q(|f a|)` bits on `f a`, some polynomial `P` bounds `q(|f a|)` by `P(|a|)`,
and running `V` on `f a` and the prefix of length `q(|f a|)` of a string is computable in
polynomial time. -/
theorem exists_truncated_verifier {encC : γ ↪ List Bool} {f : α → β}
    (hf : ComputableInPolyTime f enc encB) (q : Polynomial ℕ) {V : β × List Bool → γ}
    (hV : ComputableInPolyTime V (encPair encB encBits) encC) :
    ∃ (P : Polynomial ℕ) (V' : α × List Bool → γ),
      ComputableInPolyTime V' (encPair enc encBits) encC ∧
      (∀ a, q.eval (encB (f a)).length ≤ P.eval (enc a).length) ∧
      ∀ a w, V' (a, w) = V (f a, w.take (q.eval (encB (f a)).length)) := by
  have hq : ComputableInPolyTime (fun a => q.eval (encB (f a)).length) enc encUnary :=
    (ComputableInPolyTime.unary_eval q).comp ((ComputableInPolyTime.encoding_length encB).comp hf)
  obtain ⟨P, hP⟩ := hq.polyBounded.exists_polynomial
  exact ⟨P, fun x => V (f x.1, x.2.take (q.eval (encB (f x.1)).length)),
    hV.comp ((hf.comp (.fst enc encBits)).prod
      (.bitsTakeWithInput (.snd enc encBits) (hq.comp (.fst enc encBits)))),
    hP, fun _ _ => rfl⟩

/-- **Counting through a prefix.** If `V'` runs `V` on the first `k` bits, it accepts `2 ^ (K - k)`
times as many strings of length `K ≥ k` as `V` accepts strings of length `k`. -/
theorem acceptCount_eq_two_pow_mul_of_take {V : β × List Bool → Bool}
    {V' : α × List Bool → Bool} {a : α} {b : β} {k K : ℕ} (hk : k ≤ K)
    (hV : ∀ w, V' (a, w) = V (b, w.take k)) :
    acceptCount V' a K = 2 ^ (K - k) * acceptCount V b k := by
  simp only [acceptCount, hV]
  exact BitString.card_filter_take hk fun w => V (b, w) = true

end Cslib.Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.DirectProduct.Decode
public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import CslibFrontier.Foundations.Data.BitString.Block
import CslibFrontier.Computability.Circuit.Boolean.Combinators

/-!
# Circuit size of the direct-product decoder

The direct-product decoder `dpDecode` of
[Impagliazzo, Jaiswal, Kabanets and Wigderson][ImpagliazzoJaiswalKabanetsWigderson2010] (preprint
of 2009-10-19, Algorithm 2; Carmosino, Impagliazzo, Kabanets and Kolokolova cite the decoder as
their Theorem 4.1) has small De Morgan circuits relative to the circuit it decodes. Fix a seed
`(P, b₀, v)` and take `U = BitString n`, `V = Bool`. A tuple of `k` blocks is read from a flat
input of `k * n` bits with `Cslib.BitString.block`, as `glAmp` reads its first `k * n` bits. If
each output of `C'` costs at most `c` gates on the flat input, then the decoder costs at most
`m (#P + 1) (c + 4) + 3 m + 1` gates (`complexity_dpDecode_le`).

Each trial reads `#P + 1` outputs of `C'` on the tuple with `x` at the free position and constants
elsewhere, at two extra gates each for the constants. Its acceptance test compares the `#P`
outputs on `P` with the constants `C' b₀` (one gate each, plus the conjunction), and a multiplexer
selects the first accepted trial (four gates per trial). The default answer costs one gate. Each
step is a combinator of `CslibFrontier.Computability.Circuit.Boolean.Combinators`. The circuit
recomputes `C'` for each trial and each position read; it shares nothing between trials.

The constants `c₀ = 4`, `c₁ = 3` and the trailing `1` are ours. The bound is on size only; depth
is not certified. IJKW state the decoder as an oracle algorithm, and CIKK bound its circuit size by
a polynomial; the explicit affine form here is a library formulation.

## Main results

* `complexity_dpDecode_le`: the decoder's size.

## References

* [ImpagliazzoJaiswalKabanetsWigderson2010]
* [CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.Circuits.Boolean.DirectProduct

open Finset

variable {n : ℕ}

/-- **Circuit size of the direct-product decoder** (IJKW, preprint of 2009-10-19, Algorithm 2;
CIKK, Theorem 4.1). Read tuples of `k` blocks of `n` bits from flat inputs with
`Cslib.BitString.block`. If every output of `C'` costs at most `c` gates on the flat input, the
decoder with a fixed seed `(P, b₀, v)` of `m` trials costs at most `m (#P + 1) (c + 4) + 3 m + 1`
gates. The circuit recomputes `C'` for every read and shares nothing between trials. The constants
`4`, `3` and the trailing `1` (the default answer) are ours. This bounds size only; depth is not
certified. -/
theorem complexity_dpDecode_le {k : ℕ} (C' : (Fin k → BitString n) → Fin k → Bool) (dflt : Bool)
    (P : Finset (Fin k)) (b₀ : Fin k → BitString n) {m : ℕ} (v : Fin m → Trial (BitString n) k)
    {c : ℕ}
    (hC' : ∀ j, complexity interpretation
      (single fun y : BitString (k * n) => C' (BitString.block y) j) ≤ c) :
    complexity interpretation (single (dpDecode C' dflt P b₀ v)) ≤
      m * (#P + 1) * (c + 4) + 3 * m + 1 := by
  -- every output of `C'` on a trial tuple costs `c + 2`
  have hread : ∀ (t : Trial (BitString n) k) (j : Fin k),
      complexity interpretation (single fun x => C' (trialTuple P b₀ x t) j) ≤ c + 2 := by
    intro t j
    simp only [trialTuple_eq]
    exact (complexity_single_block_le (fun y => C' y j) _ t.1).trans
      (Nat.add_le_add_right (hC' j) _)
  -- the acceptance test of a trial
  have hacc : ∀ t : Trial (BitString n) k,
      complexity interpretation (single fun x => accepts C' P b₀ x t) ≤ #P * (c + 4) + 1 := by
    intro t
    by_cases ht : t.1 ∈ P
    · have heq : (fun x => accepts C' P b₀ x t) = fun _ => false := by
        funext x
        simp [accepts_eq, ht]
      rw [heq]
      exact (Synthesis.const (s := inputs n) false).complexity_le.trans (by omega)
    · have heq : (fun x => accepts C' P b₀ x t) =
          fun x => decide (∀ i ∈ P, decide (C' (trialTuple P b₀ x t) i = C' b₀ i) = true) := by
        funext x
        simp only [accepts_eq, ht, not_false_eq_true, true_and, decide_eq_true_eq]
      rw [heq]
      refine (complexity_decide_forall_mem_le (c := c + 3) P
        (fun i x => decide (C' (trialTuple P b₀ x t) i = C' b₀ i)) fun i _ => ?_).trans
        (le_of_eq (by ring))
      cases hb : C' b₀ i
      · simpa using (complexity_not_le fun x => C' (trialTuple P b₀ x t) i).trans
          (Nat.add_le_add_right (hread t i) 1)
      · simpa using (hread t i).trans (by omega)
  induction m with
  | zero =>
    have heq : dpDecode C' dflt P b₀ v = fun _ => dflt := funext fun x => dpDecode_zero ..
    rw [heq]
    simpa using (Synthesis.const (s := inputs n) dflt).complexity_le
  | succ m ih =>
    obtain ⟨t, w, rfl⟩ : ∃ t w, v = (Fin.cons t w : Fin (m + 1) → Trial (BitString n) k) :=
      ⟨v 0, Fin.tail v, (Fin.cons_self_tail v).symm⟩
    have heq : dpDecode C' dflt P b₀ (Fin.cons t w : Fin (m + 1) → Trial (BitString n) k) =
        fun x => if accepts C' P b₀ x t then C' (trialTuple P b₀ x t) t.1
          else dpDecode C' dflt P b₀ w x := funext fun x => dpDecode_cons ..
    rw [heq]
    refine (complexity_ite_le _ _ _).trans ((Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (hacc t) (hread t t.1)) (ih w)) 4).trans (le_of_eq ?_))
    ring

end Cslib.Circuits.Boolean.DirectProduct

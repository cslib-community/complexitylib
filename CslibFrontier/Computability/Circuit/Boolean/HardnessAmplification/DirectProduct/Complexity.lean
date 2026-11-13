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

The trial induction is stated once, with abstract costs for the reads and the comparisons
(`complexity_dpDecode_le_of`). A learner that decodes a hypothesis computed from the answers `w` to
its queries needs `C' w` to read `w` as well. Then `C' w b₀` is no longer a constant, and each
comparison recomputes both sides: the decoder costs at most `m (#P + 1) (2 c + 10) + 1` gates as a
function of `w` and `x` (`complexity_dpDecode_answers_le`), with constants that are again ours.

## Main results

* `complexity_dpDecode_le_of`: the decoder's size from the costs of its reads and comparisons.
* `complexity_dpDecode_le`: the decoder's size.
* `complexity_dpDecode_answers_le`: the decoder's size when `C'` also reads answer bits.

## References

* [ImpagliazzoJaiswalKabanetsWigderson2010]
* [CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.Circuits.Boolean.DirectProduct

open Finset

variable {n : ℕ}

/-- **The decoder's size from the cost of its reads.** Let the decoder use a family of circuits
`C' u` and read its input through `X`. If each output of `C' u` on a trial tuple with `X u` at the
free position costs at most `cr` gates as a function of `u`, and each comparison of an output on `P`
with the corresponding output on `b₀` costs at most `ce`, the decoder with `m` trials costs at most
`m (#P (ce + 1) + cr + 5) + 1` gates. This is the induction behind `complexity_dpDecode_le` and
`complexity_dpDecode_answers_le`. -/
theorem complexity_dpDecode_le_of {N k : ℕ}
    (C' : BitString N → (Fin k → BitString n) → Fin k → Bool) (X : BitString N → BitString n)
    (dflt : Bool) (P : Finset (Fin k)) (b₀ : Fin k → BitString n)
    {m : ℕ} (v : Fin m → Trial (BitString n) k) {cr ce : ℕ}
    (hread : ∀ t j, complexity interpretation
      (single fun u => C' u (trialTuple P b₀ (X u) t) j) ≤ cr)
    (hcmp : ∀ t, ∀ i ∈ P, complexity interpretation
      (single fun u => decide (C' u (trialTuple P b₀ (X u) t) i = C' u b₀ i)) ≤ ce) :
    complexity interpretation (single fun u => dpDecode (C' u) dflt P b₀ v (X u)) ≤
      m * (#P * (ce + 1) + cr + 5) + 1 := by
  -- the acceptance test of a trial
  have hacc : ∀ t : Trial (BitString n) k,
      complexity interpretation (single fun u => accepts (C' u) P b₀ (X u) t) ≤
        #P * (ce + 1) + 1 := by
    intro t
    by_cases ht : t.1 ∈ P
    · have heq : (fun u => accepts (C' u) P b₀ (X u) t) = fun _ => false := by
        funext u
        simp [accepts_eq, ht]
      rw [heq]
      exact (Synthesis.const (s := inputs N) false).complexity_le.trans (by omega)
    · have heq : (fun u => accepts (C' u) P b₀ (X u) t) = fun u =>
          decide (∀ i ∈ P, decide (C' u (trialTuple P b₀ (X u) t) i = C' u b₀ i) = true) := by
        funext u
        simp only [accepts_eq, ht, not_false_eq_true, true_and, decide_eq_true_eq]
      rw [heq]
      exact complexity_decide_forall_mem_le P _ (hcmp t)
  induction m with
  | zero =>
    have heq : (fun u => dpDecode (C' u) dflt P b₀ v (X u)) = fun _ => dflt :=
      funext fun u => dpDecode_zero ..
    rw [heq]
    simpa using (Synthesis.const (s := inputs N) dflt).complexity_le
  | succ m ih =>
    obtain ⟨t, w, rfl⟩ : ∃ t w, v = (Fin.cons t w : Fin (m + 1) → Trial (BitString n) k) :=
      ⟨v 0, Fin.tail v, (Fin.cons_self_tail v).symm⟩
    have heq : (fun u => dpDecode (C' u) dflt P b₀
          (Fin.cons t w : Fin (m + 1) → Trial (BitString n) k) (X u)) =
        fun u => if accepts (C' u) P b₀ (X u) t then C' u (trialTuple P b₀ (X u) t) t.1
          else dpDecode (C' u) dflt P b₀ w (X u) := funext fun u => dpDecode_cons ..
    rw [heq]
    refine (complexity_ite_le _ _ _).trans ((Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (hacc t) (hread t t.1)) (ih w)) 4).trans (le_of_eq ?_))
    ring

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
  -- comparing with the constant `C' b₀ i` costs at most one more gate
  have hcmp : ∀ (t : Trial (BitString n) k), ∀ i ∈ P, complexity interpretation
      (single fun x => decide (C' (trialTuple P b₀ x t) i = C' b₀ i)) ≤ c + 3 := by
    intro t i _
    cases hb : C' b₀ i
    · simpa using (complexity_not_le fun x => C' (trialTuple P b₀ x t) i).trans
        (Nat.add_le_add_right (hread t i) 1)
    · simpa using (hread t i).trans (by omega)
  refine (complexity_dpDecode_le_of (fun _ => C') id dflt P b₀ v hread hcmp).trans_eq ?_
  ring

/-- Reading the answer bits `w` and a tuple of blocks fed by `ρ` from `x`, a function of `w` and
the flat tuple costs at most two more gates. -/
private theorem complexity_answers_substitute_le {q k : ℕ}
    (G : BitString q → (Fin k → BitString n) → Bool) (ρ : Fin (k * n) → Fin n ⊕ Bool) :
    complexity interpretation (single fun wx : BitString (q + n) =>
      G (fun i => wx (Fin.castAdd n i))
        (BitString.block (substitute ρ fun i => wx (Fin.natAdd q i)))) ≤
      complexity interpretation (single fun wy : BitString (q + k * n) =>
        G (fun i => wy (Fin.castAdd (k * n) i)) (BitString.block fun i => wy (Fin.natAdd q i))) +
        2 := by
  let σ : Fin (q + k * n) → Fin (q + n) ⊕ Bool :=
    Fin.append (fun i => .inl (Fin.castAdd n i)) fun p => (ρ p).map (Fin.natAdd q) id
  have h := complexity_substitute_le σ fun wy : BitString (q + k * n) =>
    G (fun i => wy (Fin.castAdd (k * n) i)) (BitString.block fun i => wy (Fin.natAdd q i))
  refine le_of_eq_of_le ?_ h
  congr 2
  funext wx
  congr 2
  · funext i
    simp [σ, substitute]
  · funext p
    simp only [σ, substitute, Fin.append_right]
    cases ρ p <;> rfl

/-- **The decoder with answers as inputs.** Let `C' w` depend on `q` answer bits `w`, and let
every output of `C'` cost at most `c` gates as a function of `w` and the flat tuple. Then the
decoder with a fixed seed `(P, b₀, v)` of `m` trials, as a function of `w` and its input `x`, costs
at most `m (#P + 1) (2 c + 10) + 1` gates. Unlike `complexity_dpDecode_le`, the outputs `C' w b₀`
are not constants: each comparison recomputes both sides. The constants are ours. -/
theorem complexity_dpDecode_answers_le {q k : ℕ}
    (C' : BitString q → (Fin k → BitString n) → Fin k → Bool) (dflt : Bool) (P : Finset (Fin k))
    (b₀ : Fin k → BitString n) {m : ℕ} (v : Fin m → Trial (BitString n) k) {c : ℕ}
    (hC' : ∀ j, complexity interpretation (single fun wy : BitString (q + k * n) =>
      C' (fun i => wy (Fin.castAdd (k * n) i)) (BitString.block fun i => wy (Fin.natAdd q i)) j) ≤
        c) :
    complexity interpretation (single fun wx : BitString (q + n) =>
      dpDecode (C' fun i => wx (Fin.castAdd n i)) dflt P b₀ v fun i => wx (Fin.natAdd q i)) ≤
      m * (#P + 1) * (2 * c + 10) + 1 := by
  -- every output of `C'` on a trial tuple costs `c + 2`
  have hread : ∀ (t : Trial (BitString n) k) (j : Fin k),
      complexity interpretation (single fun wx : BitString (q + n) =>
        C' (fun i => wx (Fin.castAdd n i))
          (trialTuple P b₀ (fun i => wx (Fin.natAdd q i)) t) j) ≤ c + 2 := by
    intro t j
    simp only [trialTuple_eq]
    have h := complexity_answers_substitute_le (fun w y => C' w y j)
      (blockInputs (P.piecewise b₀ t.2) t.1)
    simp only [block_substitute_blockInputs] at h
    exact h.trans (Nat.add_le_add_right (hC' j) _)
  -- so does every output of `C'` on `b₀`
  have hfix : ∀ j : Fin k, complexity interpretation (single fun wx : BitString (q + n) =>
      C' (fun i => wx (Fin.castAdd n i)) b₀ j) ≤ c + 2 := by
    intro j
    have h := complexity_answers_substitute_le (fun w y => C' w y j)
      (fun p => .inr (BitString.blocksEquiv.symm b₀ p))
    have e (x : BitString n) : substitute (fun p => .inr (BitString.blocksEquiv.symm b₀ p)) x =
        BitString.blocksEquiv.symm b₀ := rfl
    simp only [e, BitString.block_blocksEquiv_symm] at h
    exact h.trans (Nat.add_le_add_right (hC' j) _)
  -- a comparison of two outputs is a negated exclusive or
  have hcmp : ∀ (t : Trial (BitString n) k), ∀ i ∈ P, complexity interpretation
      (single fun wx : BitString (q + n) =>
        decide (C' (fun i => wx (Fin.castAdd n i))
          (trialTuple P b₀ (fun i => wx (Fin.natAdd q i)) t) i =
            C' (fun i => wx (Fin.castAdd n i)) b₀ i)) ≤ 2 * c + 9 := by
    intro t i _
    have e : ∀ a b : Bool, decide (a = b) = !(a ^^ b) := by decide
    simp only [e]
    refine (complexity_not_le _).trans (le_trans (Nat.add_le_add_right
      ((complexity_xor_le _ _).trans (Nat.add_le_add_right
        (Nat.add_le_add (hread t i) (hfix i)) 4)) 1) ?_)
    omega
  refine (complexity_dpDecode_le_of (fun wx => C' fun i => wx (Fin.castAdd n i))
    (fun wx i => wx (Fin.natAdd q i)) dflt P b₀ v hread hcmp).trans ?_
  have hP : #P * (2 * c + 9 + 1) + (c + 2) + 5 ≤ (#P + 1) * (2 * c + 10) := by
    rw [show 2 * c + 9 + 1 = 2 * c + 10 by omega, add_one_mul]
    omega
  rw [mul_assoc]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left m hP) 1

end Cslib.Circuits.Boolean.DirectProduct

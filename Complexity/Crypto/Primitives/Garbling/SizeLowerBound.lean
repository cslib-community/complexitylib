/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Probability.Entropy.Continuity
public import Cslib.Foundations.Data.BitString
import Complexity.Probability.Entropy.Fano

/-!
# Entropy lower bounds on the size of garbled material

Garbled material must encode whatever the evaluator can recover from it but a simulator's view
hides. This module proves that one-world entropy argument for an observation `C`, a hidden value
`X : α` (for example the output-wire label selected by the input labels in `C`) and garbled
material `G` of `m` bits. Suppose that, in a simulated view at statistical distance at most `ε`
from the real one, `X` keeps `t` bits of entropy given `C`. Suppose also that, in the real view,
a decoder recovers `X` from `(C, G)` except with probability `δ`. Then
`t - ε log₂ |α| - (1 + ε) h₂(ε / (1 + ε)) - h₂(δ) - δ log₂ (|α| - 1) ≤ m`.

The argument combines three steps. Continuity of conditional entropy moves the bound `t` to the
real view (`Cslib.Probability.PMF.sub_le_conditionalEntropy_of_dist_le`). The chain rule gives
`H(X | C) ≤ H(G | C) + H(X | C, G)`, and Fano's inequality bounds the last term
(`Cslib.Probability.PMF.conditionalEntropy_map_le_binEntropy_add_mul_logb`). Finally, `m` bits
carry at most `m` bits of entropy.

Januzelli, Rosulek and Roy prove information-theoretic lower bounds on the size of garbled gates
[JanuzelliRosulekRoy2025]. Their tight `1.5λ`, `2λ` and `λ` bounds for classes of AND and XOR gates
combine entropy terms from several real and simulated worlds through gate-specific Shannon-type
inequalities. Those inequalities, and the single-gate random-oracle model they are stated in, are
not formalized here; this module provides only the generic one-world argument.

## Main results

* `Cslib.Crypto.Garbling.sub_le_bitLength_of_recover`: the size lower bound above.

## References

* [J. Januzelli, M. Rosulek, L. Roy, *Lower Bounds for Garbled Circuits from Shannon-Type
  Information Inequalities*][JanuzelliRosulekRoy2025]
-/

public section

namespace Cslib.Crypto.Garbling

open Cslib.Probability.PMF

variable {C α : Type*}

/-- `m` bits are `2^m` values. -/
private theorem logb_card_bitString (m : ℕ) : Real.logb 2 (Fintype.card (BitString m)) = m := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- `H(X | C) ≤ H(G | C) + H(X | C, G)` for random variables on a common space. -/
private theorem conditionalEntropy_le_add {Ω G : Type*} [Finite C] [Finite α] [Finite G]
    (ν : PMF Ω) (c : Ω → C) (x : Ω → α) (g : Ω → G) :
    conditionalEntropy (ν.map fun ω => (c ω, x ω)) ≤
      conditionalEntropy (ν.map fun ω => (c ω, g ω)) +
        conditionalEntropy (ν.map fun ω => ((c ω, g ω), x ω)) := by
  have h1 := entropy_map_le (ν.map fun ω => ((c ω, g ω), x ω)) fun t => (t.1.1, t.2)
  simp only [conditionalEntropy, PMF.map_comp] at h1 ⊢
  have e1 : ((fun t : (C × G) × α => (t.1.1, t.2)) ∘ fun ω => ((c ω, g ω), x ω)) =
      fun ω => (c ω, x ω) := rfl
  have e2 : (Prod.fst ∘ fun ω => (c ω, x ω)) = c := rfl
  have e3 : (Prod.fst ∘ fun ω => (c ω, g ω)) = c := rfl
  have e4 : (Prod.fst ∘ fun ω => ((c ω, g ω), x ω)) = fun ω => (c ω, g ω) := rfl
  rw [e1] at h1
  rw [e2, e3, e4]
  linarith

/-- **Size lower bound for garbled material.** Let `real` be the real joint law of an observation
`C`, a hidden value `X : α` and garbled material `G` of `m` bits, and let `ideal` be a simulated
law of `(C, X)` at statistical distance at most `ε` from the real one, in which `X` keeps at least
`t` bits of entropy given `C`. If `decode` recovers `X` from `(C, G)` except with probability `δ`
in the real view, then
`t - ε log₂ |α| - (1 + ε) h₂(ε / (1 + ε)) - h₂(δ) - δ log₂ (|α| - 1) ≤ m`. -/
theorem sub_le_bitLength_of_recover [Fintype C] [Fintype α] {m : ℕ}
    (real : PMF (C × α × BitString m)) (ideal : PMF (C × α)) (decode : C × BitString m → α)
    {ε t : ℝ} (hdist : dist (real.map fun w => (w.1, w.2.1)) ideal ≤ ε)
    (ht : t ≤ conditionalEntropy ideal) :
    t - ε * Real.logb 2 (Fintype.card α) - condEntropyModulus ε -
        (Real.binEntropy (real.toOuterMeasure {w | decode (w.1, w.2.2) ≠ w.2.1}).toReal /
            Real.log 2 +
          (real.toOuterMeasure {w | decode (w.1, w.2.2) ≠ w.2.1}).toReal *
            Real.logb 2 (Fintype.card α - 1)) ≤ m := by
  have htransfer := sub_le_conditionalEntropy_of_dist_le hdist ht
  have hchain := conditionalEntropy_le_add real Prod.fst (fun w => w.2.1) (fun w => w.2.2)
  have hfano := conditionalEntropy_map_le_binEntropy_add_mul_logb real (fun w => w.2.1)
    (fun w => (w.1, w.2.2)) decode
  have hsize := conditionalEntropy_le_log_card (real.map fun w => (w.1, w.2.2))
  rw [logb_card_bitString] at hsize
  linarith

end Cslib.Crypto.Garbling

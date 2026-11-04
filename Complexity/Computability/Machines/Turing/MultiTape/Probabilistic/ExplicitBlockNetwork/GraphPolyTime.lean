/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Graph
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# The graph of an explicit block-counting network in polynomial time

The ports of the vertices of the explicit block-counting networks, on numbers
(`Turing.MultiTapePTM.explicitPortsNum`), are computable in polynomial time from the number of
intervals and the number of bits of a letter in unary and the schedule number in binary. Every
step is arithmetic on numbers polynomial in the input, except the digits of the schedule number,
which are read in binary.

## Main results

* `Turing.MultiTapePTM.computableInPolyTime_digitCount`,
  `Turing.MultiTapePTM.computableInPolyTime_firstAfterNum`,
  `Turing.MultiTapePTM.computableInPolyTime_edgeTargetNum`: digit counts, next appearances and
  edge targets.
* `Turing.MultiTapePTM.computableInPolyTime_explicitSrcNum`,
  `Turing.MultiTapePTM.computableInPolyTime_explicitTgtNum`: the endpoints of the explicit
  edges.
* `Turing.MultiTapePTM.computableInPolyTime_explicitPortsNum`: the ports of a vertex, as a list of
  binary numbers.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeTM ComputableInPolyTime

variable {k : ℕ} {α : Type} {input : α ↪ List Bool}

/-- The digit of a binary number at a unary position in base `3`, compared with a unary digit. -/
private theorem digit_eq {σ pos δ : α → ℕ} (hσ : ComputableInPolyTime σ input encNat)
    (hpos : ComputableInPolyTime pos input encUnary)
    (hδ : ComputableInPolyTime δ input encUnary) :
    ComputableInPolyTime (fun a => decide (σ a / 3 ^ pos a % 3 = δ a)) input encBool := by
  have hpow : ComputableInPolyTime (fun a => 3 ^ pos a) input encNat :=
    binary_pow' (const 3) hpos
  have hdigit : ComputableInPolyTime (fun a => σ a / 3 ^ pos a % 3) input encNat :=
    binary_mod.comp ((binary_div.comp (hσ.prod hpow)).prod (const 3))
  exact decide_eq' hdigit (unary_to_binary.comp hδ)

/-- **Digit counts are polynomial-time.** -/
theorem computableInPolyTime_digitCount {σ c δ i : α → ℕ}
    (hσ : ComputableInPolyTime σ input encNat) (hc : ComputableInPolyTime c input encUnary)
    (hδ : ComputableInPolyTime δ input encUnary) (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => digitCount k (σ a) (c a) (δ a) (i a)) input encUnary := by
  unfold digitCount
  refine countPWithInput (range.comp hi) ?_
  have hpos : ComputableInPolyTime (fun p : α × ℕ => c p.1 + (k + 1) * p.2)
      (encPair input encUnary) encUnary :=
    unary_add' (hc.comp (fst _ _)) (unary_mul' (const _) (snd _ _))
  exact digit_eq (hσ.comp (fst _ _)) hpos (hδ.comp (fst _ _))

/-- Windows on numbers are polynomial-time. -/
theorem computableInPolyTime_inWindowNum {σ c i δ i' : α → ℕ}
    (hσ : ComputableInPolyTime σ input encNat) (hc : ComputableInPolyTime c input encUnary)
    (hi : ComputableInPolyTime i input encUnary) (hδ : ComputableInPolyTime δ input encUnary)
    (hi' : ComputableInPolyTime i' input encUnary) :
    ComputableInPolyTime (fun a => inWindowNum k (σ a) (c a) (i a) (δ a) (i' a)) input
      encBool := by
  have h2 := fun {j : α → ℕ} (hj : ComputableInPolyTime j input encUnary) =>
    computableInPolyTime_digitCount (k := k) hσ hc (const 2) hj
  have h0 := fun {j : α → ℕ} (hj : ComputableInPolyTime j input encUnary) =>
    computableInPolyTime_digitCount (k := k) hσ hc (const 0) hj
  unfold inWindowNum
  exact decide_and
    (unary_le' (unary_add' (unary_add' (h2 hi') (h0 hi)) (const 1))
      (unary_add' (unary_add' (unary_add' (h0 hi') (h2 hi)) hδ) (const 1)))
    (unary_le' (unary_add' (unary_add' (h0 hi') (h2 hi)) hδ)
      (unary_add' (unary_add' (h2 hi') (h0 hi)) (const 2)))

/-- **Next appearances are polynomial-time**: a search over the intervals. -/
theorem computableInPolyTime_firstAfterNum {q σ c i δ : α → ℕ}
    (hq : ComputableInPolyTime q input encUnary) (hσ : ComputableInPolyTime σ input encNat)
    (hc : ComputableInPolyTime c input encUnary) (hi : ComputableInPolyTime i input encUnary)
    (hδ : ComputableInPolyTime δ input encUnary) :
    ComputableInPolyTime (fun a => firstAfterNum k (q a) (σ a) (c a) (i a) (δ a)) input
      (encOption encUnary) := by
  unfold firstAfterNum
  refine findWithInput (range.comp hq) (bool_and' (unary_lt' (hi.comp (fst _ _)) (snd _ _)) ?_)
  exact computableInPolyTime_inWindowNum (hσ.comp (fst _ _)) (hc.comp (fst _ _))
    (hi.comp (fst _ _)) (hδ.comp (fst _ _)) (snd _ _)

/-- **Edge targets are polynomial-time.** -/
theorem computableInPolyTime_edgeTargetNum {q σ n : α → ℕ}
    (hq : ComputableInPolyTime q input encUnary) (hσ : ComputableInPolyTime σ input encNat)
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a => edgeTargetNum k (q a) (σ a) (n a)) input encUnary := by
  have hr : ComputableInPolyTime (fun a => n a - q a) input encUnary := unary_sub' hn hq
  have hk3 : ComputableInPolyTime (fun _ : α => k * 3) input encUnary := const _
  have hsink : ComputableInPolyTime (fun a => q a + n a) input encUnary := unary_add' hq hn
  unfold edgeTargetNum
  refine ite_decide (unary_lt' hn hq)
    (ite_decide (unary_lt' (unary_add' hn (const 1)) hq) (unary_add' hn (const 1)) hsink) ?_
  refine optionGetDWithInput (computableInPolyTime_firstAfterNum hq hσ ?_ ?_ ?_) hsink
  · exact unary_add' (unary_div.comp ((unary_mod.comp (hr.prod hk3)).prod (const 3))) (const 1)
  · exact unary_div.comp (hr.prod hk3)
  · exact unary_mod.comp (hr.prod (const 3))

/-- **The sources of the explicit edges are polynomial-time.** -/
theorem computableInPolyTime_explicitSrcNum {q m σ j : α → ℕ}
    (hq : ComputableInPolyTime q input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hσ : ComputableInPolyTime σ input encNat) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => explicitSrcNum k (q a) (m a) (σ a) (j a)) input encUnary := by
  have hcard : ComputableInPolyTime (fun a => q a * (3 * k + 1) * m a) input encUnary :=
    unary_mul' (unary_mul' hq (const _)) hm
  unfold explicitSrcNum blockSrcNum
  refine ite_decide (unary_lt' hj hcard) ?_ ?_
  · have hn : ComputableInPolyTime (fun a => j a / m a) input encUnary :=
      unary_div.comp (hj.prod hm)
    exact ite_decide (unary_lt' hn hq) hn (unary_div.comp ((unary_sub' hn hq).prod (const _)))
  · exact computableInPolyTime_edgeTargetNum hq hσ (unary_div.comp ((unary_sub' hj hcard).prod hm))

/-- **The targets of the explicit edges are polynomial-time.** -/
theorem computableInPolyTime_explicitTgtNum {q m j : α → ℕ}
    (hq : ComputableInPolyTime q input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => explicitTgtNum k (q a) (m a) (j a)) input encUnary := by
  have hcard : ComputableInPolyTime (fun a => q a * (3 * k + 1) * m a) input encUnary :=
    unary_mul' (unary_mul' hq (const _)) hm
  unfold explicitTgtNum
  exact unary_add' (unary_mul' hq (const _))
    (ite_decide (unary_lt' hj hcard) hj (unary_sub' hj hcard))

/-- **The ports of a vertex are polynomial-time**, as a list of binary numbers. -/
theorem computableInPolyTime_explicitPortsNum {q m σ v : α → ℕ}
    (hq : ComputableInPolyTime q input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hσ : ComputableInPolyTime σ input encNat) (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun a => explicitPortsNum k (q a) (m a) (σ a) (v a)) input
      (encList encNat) := by
  have hM : ComputableInPolyTime (fun a => 2 * (q a * (3 * k + 1) * m a)) input encUnary :=
    unary_mul' (const 2) (unary_mul' (unary_mul' hq (const _)) hm)
  have hfilter : ComputableInPolyTime (fun a => explicitPortsNum k (q a) (m a) (σ a) (v a)) input
      (encList encUnary) := by
    unfold explicitPortsNum
    refine filterWithInput (range.comp hM) (decide_or ?_ ?_)
    · exact decide_eq' (computableInPolyTime_explicitSrcNum (hq.comp (fst _ _)) (hm.comp (fst _ _))
        (hσ.comp (fst _ _)) (snd _ _)) (hv.comp (fst _ _))
    · exact decide_eq' (computableInPolyTime_explicitTgtNum (hq.comp (fst _ _)) (hm.comp (fst _ _))
        (snd _ _)) (hv.comp (fst _ _))
  simpa only [Function.comp_def, List.map_id'] using (map unary_to_binary).comp hfilter

end Turing.MultiTapePTM

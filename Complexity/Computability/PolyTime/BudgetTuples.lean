/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.BudgetTuples
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops

/-!
# The successor of a tuple of bounded weight in polynomial time

`Cslib.BudgetTuples.budgetNext` walks the tuples of weight below a budget, the mode exponents of
the Boolean tensor contraction proof of [OpenAI2026ETH] (§D.4.5, p. 63). This file certifies that
one step is polynomial-time, with the weights, the budget and the tuple in binary
(`computableInPolyTime_budgetNext`), through its left scan `budgetNextScan`. So the enumeration
has polynomial delay.

## Main definitions

* `Cslib.BudgetTuples.encScanState`, `Cslib.BudgetTuples.encBudgetInput`: encodings of the scan
  state and of the inputs.

## Main results

* `Cslib.BudgetTuples.computableInPolyTime_scanStep`: one step of the scan.
* `Cslib.BudgetTuples.computableInPolyTime_budgetNext`: the successor.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.5, the enumeration
  after (D.15), p. 63.
-/

public section

namespace Cslib.BudgetTuples

open Turing.MultiTapeTM

/-- The state of the scan: the remaining budget in binary, the number of remaining weights in
unary, the coordinates read and the successor found so far in binary. -/
abbrev ScanState : Type := ℕ × ℕ × List ℕ × Option (List ℕ)

/-- The encoding of `ScanState`. -/
@[expose] def encScanState : ScanState ↪ List Bool :=
  encPair encNat (encPair encUnary (encPair (encList encNat) (encOption (encList encNat))))

/-- The inputs `(ws, p, β)` of `budgetNext`, in binary. -/
@[expose] def encBudgetInput : List ℕ × ℕ × List ℕ ↪ List Bool :=
  encPair (encList encNat) (encPair encNat (encList encNat))

/-- **One step of the scan is polynomial-time.** -/
theorem computableInPolyTime_scanStep :
    ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) => scanStep q.1 q.2)
      (encPair encScanState (encPair encNat encNat)) encScanState := by
  let enc := encPair encScanState (encPair encNat encNat)
  have hr : ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) => q.1.1) enc encNat := by
    unfold enc encScanState; fun_prop
  have hrest : ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) => q.1.2.1) enc encUnary := by
    unfold enc encScanState; fun_prop
  have hpre : ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) => q.1.2.2.1) enc
      (encList encNat) := by
    unfold enc encScanState; fun_prop
  have hbest : ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) => q.1.2.2.2) enc
      (encOption (encList encNat)) := by
    unfold enc encScanState; fun_prop
  have hw : ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) => q.2.1) enc encNat := by
    unfold enc; fun_prop
  have hb : ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) => q.2.2) enc encNat := by
    unfold enc; fun_prop
  have hb1 : ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) => q.2.2 + 1) enc encNat :=
    ComputableInPolyTime.binary_add.comp (hb.prod (.const 1))
  have hrest1 := ComputableInPolyTime.unary_sub' hrest (.const 1)
  have hnew : ComputableInPolyTime (fun q : ScanState × (ℕ × ℕ) =>
      some (q.1.2.2.1 ++ (q.2.2 + 1) :: List.replicate (q.1.2.1 - 1) 0)) enc
      (encOption (encList encNat)) :=
    (ComputableInPolyTime.optionSome (encList encNat)).comp (ComputableInPolyTime.listAppend' hpre
      (ComputableInPolyTime.cons' hb1 (ComputableInPolyTime.replicate hrest1 (.const 0))))
  have hcond := ComputableInPolyTime.binary_lt' (ComputableInPolyTime.binary_mul' hw hb1) hr
  have h := ((ComputableInPolyTime.binary_sub' hr (ComputableInPolyTime.binary_mul' hw hb)).prod
    (hrest1.prod (((ComputableInPolyTime.snoc encNat).comp (hpre.prod hb)).prod
      (hcond.ite' hnew hbest))))
  unfold encScanState
  refine h.of_enc_eq fun q => ?_
  simp only [scanStep, decide_eq_true_eq, Function.comp_apply]

/-- The coordinates of the zipped pairs form a prefix of the tuple. -/
private theorem map_snd_zip_prefix (ws β : List ℕ) : (ws.zip β).map Prod.snd <+: β := by
  induction ws generalizing β with
  | nil => exact List.nil_prefix
  | cons w ws ih =>
    cases β with
    | nil => exact List.nil_prefix
    | cons b β => simpa [List.prefix_cons_inj] using ih β

/-- A prefix has a shorter encoding. -/
private theorem length_encList_le_of_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) :
    (encList encNat l₁).length ≤ (encList encNat l₂).length := by
  rw [length_encList, length_encList]
  exact (h.sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- A successor has at most one more bit. -/
private theorem length_encNat_succ_le (b : ℕ) :
    (encNat (b + 1)).length ≤ (encNat b).length + 1 := by
  rw [length_encNat_eq_size, length_encNat_eq_size]
  refine Nat.size_le.mpr ?_
  have := Nat.lt_size_self b
  rw [pow_succ]
  omega

/-- **The successor is polynomial-time**, with the weights, the budget and the tuple in binary:
the enumeration of the tuples of bounded weight has polynomial delay. -/
theorem computableInPolyTime_budgetNext :
    ComputableInPolyTime (fun x : List ℕ × ℕ × List ℕ => budgetNext x.1 x.2.1 x.2.2)
      encBudgetInput (encOption (encList encNat)) := by
  have hws : ComputableInPolyTime (fun x : List ℕ × ℕ × List ℕ => x.1) encBudgetInput
      (encList encNat) := by unfold encBudgetInput; fun_prop
  have hp : ComputableInPolyTime (fun x : List ℕ × ℕ × List ℕ => x.2.1) encBudgetInput encNat := by
    unfold encBudgetInput; fun_prop
  have hβ : ComputableInPolyTime (fun x : List ℕ × ℕ × List ℕ => x.2.2) encBudgetInput
      (encList encNat) := by unfold encBudgetInput; fun_prop
  have hlist := (ComputableInPolyTime.zip encNat encNat).comp (hws.prod hβ)
  have hinit : ComputableInPolyTime (fun x : List ℕ × ℕ × List ℕ =>
      ((x.2.1, x.1.length, [], none) : ScanState)) encBudgetInput encScanState := by
    unfold encScanState
    exact hp.prod (((ComputableInPolyTime.length_list _).comp hws).prod
      ((ComputableInPolyTime.const (encOut := encList encNat) []).prod
        (ComputableInPolyTime.const (encOut := encOption (encList encNat)) none)))
  let size (x : List ℕ × ℕ × List ℕ) : ℕ := 4 * (encBudgetInput x).length + 8
  have hsize : PolyBounded (fun x => (encBudgetInput x).length) size :=
    ((PolyBounded.const 4).mul .self).add (.const 8)
  have hproj : ComputableInPolyTime (fun s : ScanState => s.2.2.2) encScanState
      (encOption (encList encNat)) := by unfold encScanState; fun_prop
  refine (hproj.comp (ComputableInPolyTime.foldl_spec (step := scanStep) hlist hinit
    computableInPolyTime_scanStep
    (fun x consumed s => s.1 ≤ x.2.1 ∧ s.2.1 ≤ x.1.length ∧ s.2.2.1 = consumed.map Prod.snd ∧
      ∀ l, s.2.2.2 = some l →
        (encList encNat l).length ≤ (encList encNat x.2.2).length + x.1.length + 2)
    (fun x => ⟨le_rfl, le_rfl, rfl, fun _ h => by cases h⟩) ?_ hsize ?_).1).of_enc_eq
    fun x => ?_
  · -- The invariant is preserved.
    rintro ⟨ws, p, β⟩ consumed s ⟨w, b⟩ hpre ⟨hr, hrest, hcons, hbest⟩
    have hprefix : s.2.2.1 ++ [b] <+: β := by
      have h1 : (consumed ++ [(w, b)]).map Prod.snd <+: (ws.zip β).map Prod.snd :=
        hpre.map _
      rw [List.map_append, ← hcons] at h1
      exact h1.trans (map_snd_zip_prefix ws β)
    refine ⟨(Nat.sub_le _ _).trans hr, (Nat.sub_le _ _).trans hrest, by
      simp [scanStep, hcons], fun l hl => ?_⟩
    simp only [scanStep] at hl
    split_ifs at hl with hcond
    · cases hl
      have hle := length_encList_le_of_prefix hprefix
      have hsucc := length_encNat_succ_le b
      simp only [length_encList, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        List.map_replicate, List.sum_replicate, List.map_nil, List.sum_nil, smul_eq_mul] at hle ⊢
      have h0 : (encNat 0).length = 0 := rfl
      rw [h0] at ⊢
      have : s.2.1 - 1 ≤ ws.length := (Nat.sub_le _ _).trans hrest
      omega
    · exact hbest l hl
  · -- The states are polynomially bounded.
    rintro ⟨ws, p, β⟩ consumed s hpre ⟨hr, hrest, hcons, hbest⟩
    obtain ⟨r, rest, pre, best⟩ := s
    simp only at hr hrest hcons hbest
    have hpreβ : pre <+: β := hcons ▸ (hpre.map _).trans (map_snd_zip_prefix ws β)
    have hpl := length_encList_le_of_prefix hpreβ
    have hrl := length_encNat_mono hr
    have hbl : (encOption (encList encNat) best).length ≤
        (encList encNat β).length + ws.length + 3 := by
      cases best with
      | none => simp [encOption_none]
      | some l => simp only [encOption_some, List.length_cons]; have := hbest l rfl; omega
    have hlen : ws.length ≤ (encList encNat ws).length := by
      clear hpre hrest hbest hbl
      rw [length_encList]
      induction ws with
      | nil => simp
      | cons _ _ ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
    simp only [encScanState, encBudgetInput, length_encPair, encUnary_apply,
      List.length_replicate, size]
    omega
  · rw [← budgetNextScan_eq]
    rfl

end Cslib.BudgetTuples

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AWPP.Lowness
public import Complexity.Computability.Complexity.Classes.AWPP.WPP
public import Complexity.Computability.Complexity.Classes.SharpP.WeightedReplay
import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Oracle lowness of SPP, LWPP, and WPP

This module formalizes the oracle lowness hierarchy for the gap-definable counting classes `SPP`,
`LWPP`, and `WPP` following [Fenner, Fortnow and Kurtz, Section 5][FennerFortnowKurtz1994]:

* **Relativized gap-definable classes (`SPPWithOracle`, `LWPPWithFixedTarget`,
  `WPPWithFixedTarget`, `CeqPWithOracle`):** `SPPWithOracle` and `CeqPWithOracle` relativize `SPP`
  and `C=P` via `GapPWithOracle A enc`. For `LWPP` and `WPP`, `LWPPWithFixedTarget` and
  `WPPWithFixedTarget` relativize the counting gap (`g ∈ GapPWithOracle A enc`) while keeping the
  target function `f` in unrelativized `FP` (`ComputableInPolyTime f encUnary encIntBin` and
  `ComputableInPolyTime f enc encIntBin`), matching the fixed-target relativization caveat noted in
  [Fenner, Fortnow and Kurtz, Section 5 (following Definition 5.13)][FennerFortnowKurtz1994]:
  eliminating an oracle from the `GapPWithOracle A` gap does not eliminate oracle queries from an
  `FP^A` target function. Target-relativized `LWPP^A` and `WPP^A` with `FP^A` targets are not
  defined or claimed here.
* **Exact integer-weighted oracle replay (`acceptWeight_exact`, `generalWeightedReplay`,
  `GapP.generalWeightedReplay_mem`, `generalWeightedReplay_eq_exact`):** when the true-branch
  weight at each step equals a per-instance denominator `D a` on true oracle answers and `0` on
  false answers, the untaken branch at every step has weight `0`. Consequently, the replay tree
  collapses to the single deterministic path following the oracle, contributing `(D a) ^ (T a)` on
  accepting runs and `0` on rejecting runs.
* **`SPP` is low for `GapP` (`GapPWithOracle_eq_GapP_of_mem_SPP`,
  [Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]):** an `SPP` oracle has a `0`/`1`
  characteristic `GapP` function (`D a = 1`), so `GapPWithOracle A enc = GapP enc`. Hence `SPP` is
  low for `SPP`, `C=P`, and `PP` (`SPP^SPP = SPP`, `C=P^SPP = C=P`, `PP^SPP = PP`), and low for the
  fixed-target wide-gap classes `LWPPWithFixedTarget` and `WPPWithFixedTarget`.
* **`LWPP` scaling simulation and lowness (`exists_mul_mem_GapP_of_mem_LWPP`,
  [Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]):** for an `LWPP` oracle with
  length-dependent nonzero target `f : ℕ → ℤ`, multiplying the oracle's gap on query `w` by the
  product of `f i` over all `i ≤ τ(|a|)` with `i ≠ |w|` normalizes every query of length at most
  the clock `τ(|a|)` to the common length-dependent denominator `D(|a|) = ∏_{i ≤ τ(|a|)} f(i)`.
  Summing over witnesses shows that every `h ∈ GapPWithOracle A enc` can be scaled by a nonzero
  polynomial-time length-dependent factor `S(|a|)` into `GapP enc`. Hence `LWPP` is low for `C=P`
  and `PP` (`C=P^LWPP = C=P`, `PP^LWPP = PP`) and low for the fixed-target wide-gap classes
  `LWPPWithFixedTarget` and `WPPWithFixedTarget`.
* **`WPP` is low for `PP` (`PPWithOracle_eq_PP_of_mem_WPP`):** follows from `WPP ⊆ AWPP`
  (`WPP_subset_AWPP`) and `AWPP` lowness for `PP` (`PPWithOracle_eq_PP_of_mem_AWPP`).

All results use the library's strict polynomial-time adaptive word-oracle verifier model; no
nondeterministic oracle-machine counting characterization or `FP^A`-target wide-gap relativization
is claimed.

## Main definitions

* `Cslib.Complexity.SPPWithOracle`: `0`/`1` characteristic gaps in `GapPWithOracle`.
* `Cslib.Complexity.LWPPWithFixedTarget`: wide gaps in `GapPWithOracle` with an unrelativized
  polynomial-time unary-length target.
* `Cslib.Complexity.WPPWithFixedTarget`: wide gaps in `GapPWithOracle` with an unrelativized
  polynomial-time instance-dependent target.
* `Cslib.Complexity.CeqPWithOracle`: zero sets of `GapPWithOracle` functions.
* `Cslib.Complexity.generalWeightedReplay`: finite oracle replay with a general integer denominator.

## Main results

* `Cslib.Complexity.SPP_subset_SPPWithOracle`,
  `Cslib.Complexity.LWPP_subset_LWPPWithFixedTarget`,
  `Cslib.Complexity.WPP_subset_WPPWithFixedTarget`,
  `Cslib.Complexity.CeqP_subset_CeqPWithOracle`,
  `Cslib.Complexity.SPPWithOracle_eq_SPP`,
  `Cslib.Complexity.LWPPWithFixedTarget_eq_LWPP`,
  `Cslib.Complexity.WPPWithFixedTarget_eq_WPP`,
  `Cslib.Complexity.CeqPWithOracle_eq_CeqP`: base inclusions and `P`-oracle eliminations.
* `Cslib.Complexity.acceptWeight_exact`, `Cslib.Complexity.acceptWeight_exact_of_forall`:
  exact algebraic collapse of `acceptWeight` when untaken branches have weight zero.
* `Cslib.Complexity.GapP.generalWeightedReplay_mem`,
  `Cslib.Complexity.generalWeightedReplay_eq_exact`: `GapP` membership and exact evaluation of
  `generalWeightedReplay`.
* `Cslib.Complexity.GapPWithOracle_eq_GapP_of_mem_SPP`,
  `Cslib.Complexity.SPPWithOracle_eq_SPP_of_mem_SPP`,
  `Cslib.Complexity.LWPPWithFixedTarget_eq_LWPP_of_mem_SPP`,
  `Cslib.Complexity.WPPWithFixedTarget_eq_WPP_of_mem_SPP`,
  `Cslib.Complexity.CeqPWithOracle_eq_CeqP_of_mem_SPP`,
  `Cslib.Complexity.PPWithOracle_eq_PP_of_mem_SPP`.
* `Cslib.Complexity.exists_mul_mem_GapP_of_mem_LWPP`,
  `Cslib.Complexity.LWPPWithFixedTarget_eq_LWPP_of_mem_LWPP`,
  `Cslib.Complexity.WPPWithFixedTarget_eq_WPP_of_mem_LWPP`,
  `Cslib.Complexity.CeqPWithOracle_eq_CeqP_of_mem_LWPP`,
  `Cslib.Complexity.PPWithOracle_eq_PP_of_mem_LWPP`.
* `Cslib.Complexity.PPWithOracle_eq_PP_of_mem_WPP`.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994],
  Section 5 (including Definition 5.13 and the fixed-target relativization discussion).
* [S. Fenner, L. Fortnow, S. Kurtz, L. Li, *An Oracle Builder's Toolkit*][FennerEtAl2003],
  Section 6.
* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003].
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing (MultiTapePTM)
open _root_.Turing.MultiTapeTM
  (ComputableInPolyTime ComputableTidilyInPolyTime encBits encBits_apply encBool encBool_apply
    encFiniteConfig encIntBin encList encPair encUnary length_encPair)
open _root_.Turing.MultiTapeMachine (FiniteConfig)
open _root_.Turing.MultiTapePTM (replyStep)
open Probability.AdaptiveWeights Finset

variable {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

/-! ### Relativized gap-definable decision classes -/

/-- Small-gap polynomial time relative to a language oracle `A`: languages whose characteristic
function belongs to `GapPWithOracle A enc`
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]. -/
def SPPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ g ∈ GapPWithOracle A enc, (∀ a, g a = 0 ∨ g a = 1) ∧ ∀ a, a ∈ L ↔ g a = 1}

/-- Length-dependent wide-gap polynomial time relative to a language oracle `A` with an
unrelativized `FP` target: languages witnessed by a `GapPWithOracle A enc` function taking `0` on
nonmembers and a nonzero polynomial-time unary-length target `f (|enc a|)` (computable without `A`)
on members [Fenner, Fortnow and Kurtz, Section 5][FennerFortnowKurtz1994]. -/
def LWPPWithFixedTarget (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ g ∈ GapPWithOracle A enc, ∃ f : ℕ → ℤ, ComputableInPolyTime f encUnary encIntBin ∧
    (∀ n, f n ≠ 0) ∧ (∀ a, g a = 0 ∨ g a = f (enc a).length) ∧
    ∀ a, a ∈ L ↔ g a = f (enc a).length}

/-- Wide-gap polynomial time relative to a language oracle `A` with an unrelativized `FP` target:
languages witnessed by a `GapPWithOracle A enc` function taking `0` on nonmembers and a nonzero
polynomial-time target `f a` (computable without `A`) on members
[Fenner, Fortnow and Kurtz, Section 5][FennerFortnowKurtz1994]. -/
def WPPWithFixedTarget (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ g ∈ GapPWithOracle A enc, ∃ f : α → ℤ, ComputableInPolyTime f enc encIntBin ∧
    (∀ a, f a ≠ 0) ∧ (∀ a, g a = 0 ∨ g a = f a) ∧ ∀ a, a ∈ L ↔ g a = f a}

/-- Exact counting `C=P` relative to a language oracle `A`: zero sets of `GapPWithOracle A enc`
functions [Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]. -/
def CeqPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ g ∈ GapPWithOracle A enc, ∀ a, a ∈ L ↔ g a = 0}

/-- Ordinary `SPP` verifiers can ignore every oracle. -/
theorem SPP_subset_SPPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    SPP enc ⊆ SPPWithOracle A enc := fun _ ⟨g, hg, hr, hL⟩ =>
  ⟨g, GapP_subset_GapPWithOracle A enc hg, hr, hL⟩

/-- Ordinary `LWPP` verifiers can ignore every oracle in `LWPPWithFixedTarget`. -/
theorem LWPP_subset_LWPPWithFixedTarget (A : Set (List Bool)) (enc : α ↪ List Bool) :
    LWPP enc ⊆ LWPPWithFixedTarget A enc := fun _ ⟨g, hg, f, hf, hn, hr, hL⟩ =>
  ⟨g, GapP_subset_GapPWithOracle A enc hg, f, hf, hn, hr, hL⟩

/-- Ordinary `WPP` verifiers can ignore every oracle in `WPPWithFixedTarget`. -/
theorem WPP_subset_WPPWithFixedTarget (A : Set (List Bool)) (enc : α ↪ List Bool) :
    WPP enc ⊆ WPPWithFixedTarget A enc := fun _ ⟨g, hg, f, hf, hn, hr, hL⟩ =>
  ⟨g, GapP_subset_GapPWithOracle A enc hg, f, hf, hn, hr, hL⟩

/-- Ordinary `C=P` verifiers can ignore every oracle. -/
theorem CeqP_subset_CeqPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    CeqP enc ⊆ CeqPWithOracle A enc := fun _ ⟨g, hg, hL⟩ =>
  ⟨g, GapP_subset_GapPWithOracle A enc hg, hL⟩

/-- A polynomial-time oracle adds no `SPP` languages. -/
theorem SPPWithOracle_eq_SPP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    SPPWithOracle A enc = SPP enc := by
  simp only [SPPWithOracle, GapPWithOracle_eq_GapP hA, SPP]

/-- A polynomial-time oracle adds no `LWPPWithFixedTarget` languages. -/
theorem LWPPWithFixedTarget_eq_LWPP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    LWPPWithFixedTarget A enc = LWPP enc := by
  simp only [LWPPWithFixedTarget, GapPWithOracle_eq_GapP hA, LWPP]

/-- A polynomial-time oracle adds no `WPPWithFixedTarget` languages. -/
theorem WPPWithFixedTarget_eq_WPP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    WPPWithFixedTarget A enc = WPP enc := by
  simp only [WPPWithFixedTarget, GapPWithOracle_eq_GapP hA, WPP]

/-- A polynomial-time oracle adds no `C=P` languages. -/
theorem CeqPWithOracle_eq_CeqP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    CeqPWithOracle A enc = CeqP enc := by
  simp only [CeqPWithOracle, GapPWithOracle_eq_GapP hA, CeqP]

/-! ### Exact integer-weighted oracle replay -/

/-- Exact algebraic counterpart to `AdaptiveWeights.acceptWeight_error`: when the true-branch
weight at every state along the deterministic trajectory of `answer` is `D` if `answer` holds and
`0` otherwise, the untaken branch at each step receives weight `0`, so `acceptWeight` equals
`D ^ n` times the indicator of the deterministic trajectory accepting. -/
theorem acceptWeight_exact {σ : Type*} {D : ℤ} {p : σ → ℤ} (step : σ → Bool → σ)
    (accept answer : σ → Bool) (n : ℕ) (s : σ)
    (hp : ∀ i < n,
      p ((fun s => step s (answer s))^[i] s) =
        if answer ((fun s => step s (answer s))^[i] s) then D else 0) :
    acceptWeight D p step accept n s =
      D ^ n * (if accept ((fun s => step s (answer s))^[n] s) then 1 else 0) := by
  induction n generalizing s with
  | zero => rw [acceptWeight, pow_zero, Function.iterate_zero_apply, one_mul]
  | succ n ih =>
    have hp0 : p s = if answer s then D else 0 := hp 0 (Nat.zero_lt_succ n)
    have hpn : ∀ i < n,
        p ((fun s => step s (answer s))^[i] (step s (answer s))) =
          if answer ((fun s => step s (answer s))^[i] (step s (answer s))) then D else 0 :=
      fun i hi => hp (i + 1) (Nat.succ_lt_succ hi)
    have h := ih (step s (answer s)) hpn
    rw [acceptWeight, hp0, Function.iterate_succ_apply, pow_succ]
    cases ha : answer s
    · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, zero_mul, add_zero]
      have h' : step s false = step s (answer s) := by rw [ha]
      rw [h', h]
      ring
    · simp only [↓reduceIte, sub_self, zero_mul, zero_add]
      have h' : step s true = step s (answer s) := by rw [ha]
      rw [h', h]
      ring

/-- Special case of `acceptWeight_exact` when the exact weight identity holds at every state. -/
theorem acceptWeight_exact_of_forall {σ : Type*} {D : ℤ} {p : σ → ℤ} (step : σ → Bool → σ)
    (accept answer : σ → Bool)
    (hp : ∀ s, p s = if answer s then D else 0) (n : ℕ) (s : σ) :
    acceptWeight D p step accept n s =
      D ^ n * (if accept ((fun s => step s (answer s))^[n] s) then 1 else 0) :=
  acceptWeight_exact step accept answer n s fun _ _ => hp _

/-- Total accepting weight of the instruction-indexed replay tree with an arbitrary per-instance
integer denominator `D a`. Query instructions use the request numerator `H (a, w)`, while local
instructions assign zero weight to `true` and weight `D a` to the canonical padding bit `false`. -/
def generalWeightedReplay {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
    (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) (D : α → ℤ) (H : α × List Bool → ℤ) (a : α) : ℤ :=
  acceptWeight (D a)
    (fun cfg => if (machine.pendingQuery cfg).isSome then H (a, machine.pendingRequest cfg) else 0)
    machine.replyStep (fun cfg => cfg.tapes.output.headD false) (T a)
    (FiniteConfig.init machine.initial (input a))

/-- A finite oracle computation with a `GapP` per-step denominator `D` and `GapP` request
numerators `H` has an ordinary `GapP` accepting weight. -/
theorem GapP.generalWeightedReplay_mem {k : ℕ} {Control Operation : Type}
    [DecidableEq Operation] [Finite Control] [Finite Operation]
    (machine : MultiTapePTM k Bool Control Operation)
    {input : α → List Bool} {T : α → ℕ} {D : α → ℤ} {H : α × List Bool → ℤ}
    (hinput : ComputableInPolyTime input enc encBits)
    (hT : ComputableInPolyTime T enc encUnary)
    (hD : D ∈ GapP enc)
    (hH : H ∈ GapP (encPair enc encBits)) :
    generalWeightedReplay machine input T D H ∈ GapP enc := by
  let _ := Fintype.ofFinite Operation
  let cfg : (α × List Bool) × ℕ → FiniteConfig k Bool Control Operation :=
    fun x => machine.replayPrefix (input x.1.1) x.1.2 x.2
  have hcfg : ComputableInPolyTime cfg
      (encPair (encPair enc encBits) encUnary) encFiniteConfig :=
    machine.computableInPolyTime_replayPrefix.comp (g := fun x : (α × List Bool) × ℕ =>
      ((input x.1.1, x.1.2), x.2)) (by fun_prop)
  have hquery : ComputableInPolyTime
      (fun x => (machine.pendingQuery (cfg x)).isSome)
      (encPair (encPair enc encBits) encUnary) encBool :=
    (ComputableInPolyTime.of_finite Option.isSome).comp
      (machine.pendingQuery_pt.comp hcfg)
  have hrequest : ComputableInPolyTime
      (fun x : (α × List Bool) × ℕ => (x.1.1, machine.pendingRequest (cfg x)))
      (encPair (encPair enc encBits) encUnary) (encPair enc encBits) := by
    have hinstance : ComputableInPolyTime
        (fun x : (α × List Bool) × ℕ => x.1.1)
        (encPair (encPair enc encBits) encUnary) enc := by fun_prop
    exact hinstance.prod (machine.pendingRequest_pt.comp hcfg)
  let p : (α × List Bool) × ℕ → ℤ := fun x =>
    if (machine.pendingQuery (cfg x)).isSome then H (x.1.1, machine.pendingRequest (cfg x)) else 0
  have hp : p ∈ GapP (encPair (encPair enc encBits) encUnary) :=
    GapP.ite_mem hquery (GapP.comp_mem hH hrequest) GapP.zero_mem
  have hdenom : (fun x : (α × List Bool) × ℕ => D x.1.1) ∈
      GapP (encPair (encPair enc encBits) encUnary) :=
    GapP.comp_mem hD (by fun_prop)
  have hbit : ComputableInPolyTime
      (fun x : (α × List Bool) × ℕ => x.1.2.getD x.2 false)
      (encPair (encPair enc encBits) encUnary) encBool := by fun_prop
  have hfactor := GapP.ite_mem hbit hp (GapP.sub_mem' hdenom hp)
  have hprod := GapP.prod_range_mem hfactor
    (r := fun x : α × List Bool => x.2.length) (by fun_prop)
  have hout : ComputableInPolyTime
      (fun x : α × List Bool => (machine.replayOutput (input x.1) x.2).headD false)
      (encPair enc encBits) encBool := by
    have hreindex : ComputableInPolyTime
        (fun x : α × List Bool => (input x.1, x.2))
        (encPair enc encBits) (encPair encBits encBits) := by fun_prop
    exact (ComputableInPolyTime.headD false).comp
      (machine.computableInPolyTime_replayOutput.comp hreindex)
  have hmask : (fun x : α × List Bool =>
      if (machine.replayOutput (input x.1) x.2).headD false then (1 : ℤ) else 0) ∈
      GapP (encPair enc encBits) := GapP.ite_mem hout GapP.one_mem GapP.zero_mem
  have hsum := GapP.sum_bits_mem (GapP.mul_mem hprod hmask) hT
  convert hsum using 1
  funext a
  rw [generalWeightedReplay, acceptWeight_eq_sum]
  apply sum_congr rfl
  intro w _
  rw [pathWeight_eq_prod]
  rfl

open Classical in
/-- If `H (a, w)` equals `D a` on oracle members and `0` on nonmembers for every query `w` of
length at most the clock `T a`, then `generalWeightedReplay` evaluates to `(D a) ^ (T a)` times the
accepting indicator of the deterministic oracle computation. -/
theorem generalWeightedReplay_eq_exact {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit)
    (input : α → List Bool) (T : α → ℕ) (D : α → ℤ) (H : α × List Bool → ℤ)
    (a : α)
    (hw : ∀ w, w.length ≤ T a → H (a, w) = if w ∈ A then D a else 0) :
    generalWeightedReplay machine input T D H a =
      (D a) ^ (T a) * (if (OracleComp.interpret (m := Id) (languageOracle A)
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (T a) (input a))).headD false then 1 else 0) := by
  let g : List Bool → Bool := fun w => decide (w ∈ A)
  let p := fun cfg =>
    if (machine.pendingQuery cfg).isSome then H (a, machine.pendingRequest cfg) else 0
  let answer := fun cfg =>
    if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false
  have hstep : (fun cfg => machine.replyStep cfg (answer cfg)) =
      machine.answerStep (fun q => [g q.2]) := by
    funext cfg
    rw [machine.answerStep_bit g cfg]
    cases hq : (machine.pendingQuery cfg).isSome <;>
      simp only [replyStep, answer, hq, Bool.false_eq_true, ↓reduceIte]
  have hspace (i : ℕ) : FiniteConfig.SpaceBound (input a).length i 1
      ((machine.answerStep (fun q => [g q.2]))^[i]
        (FiniteConfig.init machine.initial (input a))) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact machine.spaceBound_answerStep g ih
  have hp : ∀ i < T a,
      p ((fun cfg => machine.replyStep cfg (answer cfg))^[i]
        (FiniteConfig.init machine.initial (input a))) =
        if answer ((fun cfg => machine.replyStep cfg (answer cfg))^[i]
          (FiniteConfig.init machine.initial (input a))) then D a else 0 := by
    intro i hi
    dsimp only [p, answer, g]
    rw [hstep]
    set cfg := (machine.answerStep (fun q => [g q.2]))^[i]
      (FiniteConfig.init machine.initial (input a))
    by_cases hq : (machine.pendingQuery cfg).isSome
    · have hlen : (machine.pendingRequest cfg).length ≤ T a :=
        (machine.length_pendingRequest_le (hspace i)).trans hi.le
      simp only [hq, ↓reduceIte, hw (machine.pendingRequest cfg) hlen, decide_eq_true_eq]
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
  have h := acceptWeight_exact machine.replyStep (fun cfg => cfg.tapes.output.headD false)
    answer (T a) (FiniteConfig.init machine.initial (input a)) hp
  rw [hstep] at h
  have hout := machine.interpret_run_pure_false (languageOracle A) (T a) (input a)
  change OracleComp.interpret (m := Id) (languageOracle A) _ =
    ((machine.answerStep (fun q => [g q.2]))^[T a]
      (FiniteConfig.init machine.initial (input a))).tapes.output at hout
  simpa only [generalWeightedReplay, p, hout] using h

/-! ### `SPP` oracle lowness (Fenner–Fortnow–Kurtz 1994, Section 5) -/

private theorem sharpPWithOracle_mem_GapP_of_mem_SPP (hA : A ∈ SPP encBits)
    {c : α → ℕ} (hc : c ∈ SharpPWithOracle A enc) :
    (fun a => (c a : ℤ)) ∈ GapP enc := by
  obtain ⟨g, hg, hrange, hmem⟩ := hA
  have hg_eq (w : List Bool) : g w = open Classical in if w ∈ A then 1 else 0 := by
    by_cases hw : w ∈ A
    · simp only [hw, ↓reduceIte, (hmem w).mp hw]
    · simp only [hw, ↓reduceIte]
      exact (hrange w).resolve_right fun h1 => hw ((hmem w).mpr h1)
  obtain ⟨p, V, ⟨program, hprogram, hV⟩, hc_eq⟩ := hc
  obtain ⟨k, m, machine, c₀, d₀, hrun⟩ :=
    Probability.IsOraclePPTOn.exists_fin_run_pure_false hprogram
  let r : α → ℕ := fun a => p.eval (enc a).length
  let T : α → ℕ := fun a => c₀ * (2 * (enc a).length + 1 + r a + 1) ^ d₀
  have hr : ComputableInPolyTime r enc encUnary := by dsimp [r]; fun_prop
  have hT : ComputableInPolyTime T enc encUnary := by dsimp [T]; fun_prop
  let input : α × List Bool → List Bool := encPair enc encBits
  let T' : α × List Bool → ℕ := fun x => T x.1
  let D' : α × List Bool → ℤ := fun _ => 1
  let H' : (α × List Bool) × List Bool → ℤ := fun x => g x.2
  let F := generalWeightedReplay machine input T' D' H'
  have hinput_pt : ComputableInPolyTime input (encPair enc encBits) encBits := by
    dsimp [input]; fun_prop
  have hT'_pt : ComputableInPolyTime T' (encPair enc encBits) encUnary := by
    dsimp [T']; fun_prop
  have hF : F ∈ GapP (encPair enc encBits) :=
    GapP.generalWeightedReplay_mem machine hinput_pt
      hT'_pt GapP.one_mem (GapP.comp_mem hg (by fun_prop))
  have hsum : (fun a => ∑ w : Fin (r a) → Bool, F (a, List.ofFn w)) ∈ GapP enc :=
    GapP.sum_bits_mem hF hr
  convert hsum using 1
  funext a
  have hF_eval (w : Fin (r a) → Bool) :
      F (a, List.ofFn w) = if V (a, List.ofFn w) then 1 else 0 := by
    have hexact := generalWeightedReplay_eq_exact (A := A) machine input T' D' H' (a, List.ofFn w)
      (fun q _ => hg_eq q)
    have hclock : c₀ * ((encPair enc encBits (a, List.ofFn w)).length + 1) ^ d₀ = T a := by
      simp only [T, r, length_encPair, encBits_apply, List.length_ofFn]
    have hout := hrun (a, List.ofFn w) (languageOracle A)
    rw [hclock, hV] at hout
    simpa only [F, input, T', D', hout, encBool_apply, List.headD_cons,
      one_pow, one_mul] using hexact
  simp only [r, hF_eval, hc_eq a, acceptCount, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- **`SPP` is low for `GapP`** ([Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]):
every `SPP` oracle can be simulated exactly with unit denominator in `GapP`. -/
theorem GapPWithOracle_eq_GapP_of_mem_SPP (hA : A ∈ SPP encBits) (enc : α ↪ List Bool) :
    GapPWithOracle A enc = GapP enc := by
  apply Set.Subset.antisymm ?_ (GapP_subset_GapPWithOracle A enc)
  rintro g ⟨f₁, hf₁, f₂, hf₂, hg⟩
  have h := GapP.sub_mem' (sharpPWithOracle_mem_GapP_of_mem_SPP hA hf₁)
    (sharpPWithOracle_mem_GapP_of_mem_SPP hA hf₂)
  convert h using 1
  funext a
  exact hg a

/-- **`SPP` is self-low** (`SPP^SPP = SPP`,
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem SPPWithOracle_eq_SPP_of_mem_SPP (hA : A ∈ SPP encBits) (enc : α ↪ List Bool) :
    SPPWithOracle A enc = SPP enc := by
  simp only [SPPWithOracle, GapPWithOracle_eq_GapP_of_mem_SPP hA, SPP]

/-- **`SPP` is low for fixed-target `LWPP`** (`LWPPWithFixedTarget A enc = LWPP enc` for
`A ∈ SPP encBits`, where the outer target `f : ℕ → ℤ` is computable without `A`;
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem LWPPWithFixedTarget_eq_LWPP_of_mem_SPP (hA : A ∈ SPP encBits) (enc : α ↪ List Bool) :
    LWPPWithFixedTarget A enc = LWPP enc := by
  simp only [LWPPWithFixedTarget, GapPWithOracle_eq_GapP_of_mem_SPP hA, LWPP]

/-- **`SPP` is low for fixed-target `WPP`** (`WPPWithFixedTarget A enc = WPP enc` for
`A ∈ SPP encBits`, where the outer target `f : α → ℤ` is computable without `A`;
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem WPPWithFixedTarget_eq_WPP_of_mem_SPP (hA : A ∈ SPP encBits) (enc : α ↪ List Bool) :
    WPPWithFixedTarget A enc = WPP enc := by
  simp only [WPPWithFixedTarget, GapPWithOracle_eq_GapP_of_mem_SPP hA, WPP]

/-- **`SPP` is low for `C=P`** (`C=P^SPP = C=P`,
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem CeqPWithOracle_eq_CeqP_of_mem_SPP (hA : A ∈ SPP encBits) (enc : α ↪ List Bool) :
    CeqPWithOracle A enc = CeqP enc := by
  simp only [CeqPWithOracle, GapPWithOracle_eq_GapP_of_mem_SPP hA, CeqP]

/-- **`SPP` is low for `PP`** (`PP^SPP = PP`,
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem PPWithOracle_eq_PP_of_mem_SPP (hA : A ∈ SPP encBits) (enc : α ↪ List Bool) :
    PPWithOracle A enc = PP enc := by
  ext L
  rw [mem_PPWithOracle_iff_exists_GapPWithOracle, GapPWithOracle_eq_GapP_of_mem_SPP hA,
    mem_PP_iff_exists_GapP]

/-! ### `LWPP` scaling simulation and oracle lowness (FFK94, Section 5) -/

private theorem exists_mul_mem_GapP_of_sharpPWithOracle_of_mem_LWPP (hA : A ∈ LWPP encBits)
    {c : α → ℕ} (hc : c ∈ SharpPWithOracle A enc) :
    ∃ S : ℕ → ℤ, ComputableInPolyTime S encUnary encIntBin ∧
      (∀ n, S n ≠ 0) ∧ (fun a => S (enc a).length * (c a : ℤ)) ∈ GapP enc := by
  obtain ⟨g, hg, f, hf, hfn, hrange, hmem⟩ := mem_LWPP.mp hA
  have hg_eq (w : List Bool) : g w = open Classical in if w ∈ A then f w.length else 0 := by
    by_cases hw : w ∈ A
    · simpa only [hw, ↓reduceIte, encBits_apply] using (hmem w).mp hw
    · simp only [hw, ↓reduceIte]
      exact (hrange w).resolve_right fun hfw => hw ((hmem w).mpr hfw)
  obtain ⟨p, V, ⟨program, hprogram, hV⟩, hc_eq⟩ := hc
  obtain ⟨k, m, machine, c₀, d₀, hrun⟩ :=
    Probability.IsOraclePPTOn.exists_fin_run_pure_false hprogram
  let r : α → ℕ := fun a => p.eval (enc a).length
  let τ : ℕ → ℕ := fun n => c₀ * (2 * n + 1 + p.eval n + 1) ^ d₀
  let T : α → ℕ := fun a => τ (enc a).length
  have hr : ComputableInPolyTime r enc encUnary := by dsimp [r]; fun_prop
  have hτ : ComputableInPolyTime τ encUnary encUnary := by dsimp [τ]; fun_prop
  have hT : ComputableInPolyTime T enc encUnary := by dsimp [T]; fun_prop
  let bound : ℕ → ℕ := fun n => τ n + 1
  have hbound : ComputableInPolyTime bound encUnary encUnary := by dsimp [bound]; fun_prop
  let D : ℕ → ℤ := fun n => ((List.range (bound n)).map f).prod
  have hD : ComputableInPolyTime D encUnary encIntBin :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_prod).comp
      ((ComputableInPolyTime.map hf).comp
        (ComputableInPolyTime.range.comp hbound))
  have hDn (n : ℕ) : D n ≠ 0 := List.prod_ne_zero (by simp [hfn])
  let S : ℕ → ℤ := fun n => D n ^ τ n
  -- elaborated without the expected type, which would unfold `S`
  have hS : ComputableInPolyTime S encUnary encIntBin :=
    ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_pow).comp (hD.prod hτ) :)
  have hSn (n : ℕ) : S n ≠ 0 := pow_ne_zero (τ n) (hDn n)
  let K : α × List Bool → ℤ := fun x =>
    (((List.range (bound (enc x.1).length)).filter (fun i => decide (i ≠ x.2.length))).map f).prod
  have hlist : ComputableInPolyTime
      (fun x : α × List Bool => List.range (bound (enc x.1).length))
      (encPair enc encBits) (encList encUnary) :=
    ((ComputableInPolyTime.range.comp hbound).comp (.encoding_length enc)).comp
      (.fst enc encBits)
  have htest : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ => decide (y.2 ≠ y.1.2.length))
      (encPair (encPair enc encBits) encUnary) encBool := by fun_prop
  have hK : ComputableInPolyTime K (encPair enc encBits) encIntBin :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_prod).comp
      ((ComputableInPolyTime.map hf).comp
        (ComputableInPolyTime.filterWithInput hlist htest))
  let H : α × List Bool → ℤ := fun x => g x.2 * K x
  have hH : H ∈ GapP (encPair enc encBits) :=
    GapP.mul_mem (GapP.comp_mem hg (by fun_prop)) (mem_GapP_of_polyTime hK)
  let input : α × List Bool → List Bool := encPair enc encBits
  let T' : α × List Bool → ℕ := fun x => T x.1
  let D' : α × List Bool → ℤ := fun x => D (enc x.1).length
  let H' : (α × List Bool) × List Bool → ℤ := fun x => H (x.1.1, x.2)
  let F := generalWeightedReplay machine input T' D' H'
  have hinput_pt : ComputableInPolyTime input (encPair enc encBits) encBits := by
    dsimp [input]; fun_prop
  have hT'_pt : ComputableInPolyTime T' (encPair enc encBits) encUnary := by
    dsimp [T']; fun_prop
  have hD'_pt : ComputableInPolyTime D' (encPair enc encBits) encIntBin :=
    (hD.comp (.encoding_length enc)).comp (.fst enc encBits)
  have hF : F ∈ GapP (encPair enc encBits) :=
    GapP.generalWeightedReplay_mem machine hinput_pt
      hT'_pt (mem_GapP_of_polyTime hD'_pt)
        (GapP.comp_mem hH (by fun_prop))
  have hsum : (fun a => ∑ w : Fin (r a) → Bool, F (a, List.ofFn w)) ∈ GapP enc :=
    GapP.sum_bits_mem hF hr
  refine ⟨S, hS, hSn, ?_⟩
  convert hsum using 1
  funext a
  have hH_exact (q : List Bool) (hq : q.length ≤ T a) :
      H (a, q) = open Classical in if q ∈ A then D (enc a).length else 0 := by
    have hlt : q.length < bound (enc a).length := Nat.lt_succ_of_le hq
    have hmul : f q.length * K (a, q) = D (enc a).length := by
      have herase :
          (List.range (bound (enc a).length)).filter (fun i => decide (i ≠ q.length)) =
            (List.range (bound (enc a).length)).erase q.length := by
        rw [List.nodup_range.erase_eq_filter]
        exact List.filter_congr fun i _ => by simp [bne, beq_eq_decide]
      simpa only [K, D, herase] using List.prod_map_erase f (List.mem_range.mpr hlt)
    dsimp only [H]
    rw [hg_eq q]
    split_ifs
    · exact hmul
    · exact zero_mul _
  have hF_eval (w : Fin (r a) → Bool) :
      F (a, List.ofFn w) = S (enc a).length * (if V (a, List.ofFn w) then 1 else 0) := by
    have hexact := generalWeightedReplay_eq_exact (A := A) machine input T' D' H' (a, List.ofFn w)
      (fun q hq => hH_exact q hq)
    have hclock : c₀ * ((encPair enc encBits (a, List.ofFn w)).length + 1) ^ d₀ = T a := by
      simp only [T, τ, r, length_encPair, encBits_apply, List.length_ofFn]
    have hout := hrun (a, List.ofFn w) (languageOracle A)
    rw [hclock, hV] at hout
    simpa only [F, S, T, input, T', D', H', hout, encBool_apply, List.headD_cons] using hexact
  simp only [r, hF_eval, ← mul_sum, hc_eq a, acceptCount, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- **`LWPP` scaling simulation for `GapPWithOracle`**
([Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]): for every `LWPP` oracle `A` and
every `h ∈ GapPWithOracle A enc`, there is a nonzero polynomial-time unary-length scaling function
`S : ℕ → ℤ` such that `a ↦ S (|enc a|) * h a` belongs to `GapP enc`. -/
theorem exists_mul_mem_GapP_of_mem_LWPP (hA : A ∈ LWPP encBits) {h : α → ℤ}
    (hh : h ∈ GapPWithOracle A enc) :
    ∃ S : ℕ → ℤ, ComputableInPolyTime S encUnary encIntBin ∧
      (∀ n, S n ≠ 0) ∧ (fun a => S (enc a).length * h a) ∈ GapP enc := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hh_eq⟩ := hh
  obtain ⟨S₁, hS₁, hS₁n, hG₁⟩ := exists_mul_mem_GapP_of_sharpPWithOracle_of_mem_LWPP hA hc₁
  obtain ⟨S₂, hS₂, hS₂n, hG₂⟩ := exists_mul_mem_GapP_of_sharpPWithOracle_of_mem_LWPP hA hc₂
  let S : ℕ → ℤ := fun n => S₁ n * S₂ n
  have hS : ComputableInPolyTime S encUnary encIntBin := hS₁.intBin_mul' hS₂
  have hS₁_gap : (fun a : α => S₁ (enc a).length) ∈ GapP enc :=
    mem_GapP_of_polyTime (hS₁.comp (.encoding_length enc))
  have hS₂_gap : (fun a : α => S₂ (enc a).length) ∈ GapP enc :=
    mem_GapP_of_polyTime (hS₂.comp (.encoding_length enc))
  refine ⟨S, hS, fun n => mul_ne_zero (hS₁n n) (hS₂n n), ?_⟩
  have hcomb := GapP.sub_mem' (GapP.mul_mem hS₂_gap hG₁) (GapP.mul_mem hS₁_gap hG₂)
  convert hcomb using 1
  funext a
  dsimp only [S, Pi.sub_apply, Pi.mul_apply]
  rw [hh_eq a]
  ring

/-- **`LWPP` is low for fixed-target `LWPP`** (`LWPPWithFixedTarget A enc = LWPP enc` for
`A ∈ LWPP encBits`, where the outer target `f : ℕ → ℤ` is computable without `A`;
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem LWPPWithFixedTarget_eq_LWPP_of_mem_LWPP (hA : A ∈ LWPP encBits) (enc : α ↪ List Bool) :
    LWPPWithFixedTarget A enc = LWPP enc := by
  apply Set.Subset.antisymm ?_ (LWPP_subset_LWPPWithFixedTarget A enc)
  rintro L ⟨g, hg, f, hf, hfn, hrange, hL⟩
  obtain ⟨S, hS, hSn, hSg⟩ := exists_mul_mem_GapP_of_mem_LWPP hA hg
  refine ⟨fun a => S (enc a).length * g a, hSg, fun n => S n * f n,
    hS.intBin_mul' hf, fun n => mul_ne_zero (hSn n) (hfn n),
    fun a => ?_, fun a => ?_⟩
  · rcases hrange a with h0 | hfa
    · exact Or.inl (by simp only [h0, mul_zero])
    · exact Or.inr (by simp only [hfa])
  · rw [hL a]
    exact (mul_right_inj' (hSn (enc a).length)).symm

/-- **`LWPP` is low for fixed-target `WPP`** (`WPPWithFixedTarget A enc = WPP enc` for
`A ∈ LWPP encBits`, where the outer target `f : α → ℤ` is computable without `A`;
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem WPPWithFixedTarget_eq_WPP_of_mem_LWPP (hA : A ∈ LWPP encBits) (enc : α ↪ List Bool) :
    WPPWithFixedTarget A enc = WPP enc := by
  apply Set.Subset.antisymm ?_ (WPP_subset_WPPWithFixedTarget A enc)
  rintro L ⟨g, hg, f, hf, hfn, hrange, hL⟩
  obtain ⟨S, hS, hSn, hSg⟩ := exists_mul_mem_GapP_of_mem_LWPP hA hg
  refine ⟨fun a => S (enc a).length * g a, hSg, fun a => S (enc a).length * f a,
    (hS.comp (.encoding_length enc)).intBin_mul' hf,
    fun a => mul_ne_zero (hSn (enc a).length) (hfn a), fun a => ?_, fun a => ?_⟩
  · rcases hrange a with h0 | hfa
    · exact Or.inl (by simp only [h0, mul_zero])
    · exact Or.inr (by simp only [hfa])
  · rw [hL a]
    exact (mul_right_inj' (hSn (enc a).length)).symm

/-- **`LWPP` is low for `C=P`** (`C=P^LWPP = C=P`,
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem CeqPWithOracle_eq_CeqP_of_mem_LWPP (hA : A ∈ LWPP encBits) (enc : α ↪ List Bool) :
    CeqPWithOracle A enc = CeqP enc := by
  apply Set.Subset.antisymm ?_ (CeqP_subset_CeqPWithOracle A enc)
  rintro L ⟨g, hg, hL⟩
  obtain ⟨S, -, hSn, hSg⟩ := exists_mul_mem_GapP_of_mem_LWPP hA hg
  refine ⟨fun a => S (enc a).length * g a, hSg, fun a => ?_⟩
  rw [hL a]
  exact ⟨fun h0 => by simp only [h0, mul_zero],
    fun hmul => (mul_eq_zero.mp hmul).resolve_left (hSn (enc a).length)⟩

/-- **`WPP` is low for `PP`** (`PP^WPP = PP`, via `WPP ⊆ AWPP` and `AWPP` lowness for `PP`). -/
theorem PPWithOracle_eq_PP_of_mem_WPP (hA : A ∈ WPP encBits) (enc : α ↪ List Bool) :
    PPWithOracle A enc = PP enc :=
  PPWithOracle_eq_PP_of_mem_AWPP (WPP_subset_AWPP hA) enc

/-- **`LWPP` is low for `PP`** (`PP^LWPP = PP`,
[Fenner–Fortnow–Kurtz, Section 5][FennerFortnowKurtz1994]). -/
theorem PPWithOracle_eq_PP_of_mem_LWPP (hA : A ∈ LWPP encBits) (enc : α ↪ List Bool) :
    PPWithOracle A enc = PP enc :=
  PPWithOracle_eq_PP_of_mem_WPP (LWPP_subset_WPP hA) enc

end Cslib.Complexity

/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.GreedySlotScore
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Runtime construction of balanced label schedules

Completes the `(n + m)`-slot greedy pass and empty-scope factor normalization of Lemma 4.5 of
[OpenAI2026ETH] (printed pp. 30–32) on top of `Complexity.Computability.PolyTime.GreedySlotScore`.

1. **Streaming `(n + m)`-slot pass**: `greedySchedulePass` iterates `greedySlotStepBody` via
   `Cslib.GenericRAM.IndexFold.run` across all `n` variable and `m` factor slots using
   `streamBestSlotLabel`, and `constructBalancedSchedules` normalizes empty-scope factors
   (`∀ e ∈ edges, e.1 ≠ f`) to `List.replicate Q 0`.
2. **Lemma 4.5 occupancy bounds**: `constructBalancedSchedules_balanced` bridges the runtime pass
   to `greedyLabelPass`, proving empty-factor normalization and both occupancy bounds under (4.13).
3. **Bit-length bounds and native certificates**: `length_encOuterState_run_le`,
   `length_encOuterState_run_valid_le`, `greedySchedulePassCertificate`, and
   `constructBalancedSchedulesCertificate` certify `O((r ^ Q + 1) * poly(|input|))` native time and
   polynomial workspace (`ComputableInPolySpace`).

Public encoded `ComputableInPolyTime`, `NativeCertificate`, `ComputableInO`, and
`ComputableInPolySpace` theorems govern `slotOfIndex`, `greedySchedulePass`,
`constructBalancedSchedules`, and their certificates (built on the concrete list/integer step and
postprocessing subroutines `pendingSlotOfState`, `greedySlotStepBody`, and
`normalizeEmptyFactorSchedules`) under `encScheduleParams` and `encOuterAcc`, whereas
`constructedVarSchedule` and `constructedFactorSchedule` are unencoded typed specification
bridges (`Fin n → Fin Q → Fin r` and `Fin m → Fin Q → Fin r`) to `greedyLabelPass`,
`completeLabels`, `normalizeEmptyFactors`, `potential`, and `occupancy`. Total fallback conventions:
`slotOfIndex` caps `s` at `n + m` via `min (n + m) s` before unary subtraction and returns `none`
for `s ≥ n + m`; `pendingSlotOfState` and `greedySlotStepBody` leave assigned or out-of-range
indices unchanged; when `r = 0` (`Q > 0`, so `r ^ Q = 0`) or a slot is `none`, fallback words are
`List.replicate Q 0` (when `Q = 0`, every word is `[]`); `normalizeEmptyFactorSchedules` sets every
empty-scope factor (`∀ e ∈ edges, e.1 ≠ f`) to `List.replicate Q 0` (group `⟨0, hr⟩` for
`d_f(t) = 1`); and `constructedVarSchedule` / `constructedFactorSchedule` clamp out-of-range digits
or missing positions to `0` via `wordToSchedule`.

## Main definitions

* `slotOfIndex`, `ScheduleParams`, `pendingSlotOfState`, `greedySlotStepBody`: outer `(n + m)`-slot
  decoding and single-slot step callback over `IndexFold.run`.
* `greedySchedulePass`, `normalizeEmptyFactorSchedules`, `constructBalancedSchedules`: full greedy
  pass, empty-scope factor normalization, and complete schedule constructor.
* `constructedVarSchedule`, `constructedFactorSchedule`: typed schedule bridges.
* `encScheduleParams`, `encOuterAcc`, `greedySchedulePassCertificate`,
  `constructBalancedSchedulesCertificate`: encodings and uniform `NativeCertificate`s.

## Main results

* `run_greedySlotStepBody_wf`, `wf_constructBalancedSchedules`,
  `getD_constructBalancedSchedules_empty_factor`: word well-formedness and empty-scope factor reset.
* `greedySchedulePass_eq_greedyLabelPass`, `constructedSchedules_eq_pass`,
  `constructedFactorSchedule_empty_factor`: exact agreement with `greedyLabelPass` and completion.
* `constructBalancedSchedules_score_le`, `constructBalancedSchedules_score_le_two`,
  `constructBalancedSchedules_balanced`: potential and Lemma 4.5 occupancy bounds under (4.13).
* `length_encEdges_le_of_lt`, `length_encPartialSchedules_le`,
  `length_encSlotSelectState_run_valid_le`, `length_encOuterState_run_valid_le`,
  `length_encOuterState_run_le`: encoded bit-length bounds across inner and outer loop prefixes.
* `computableInPolyTime_slotOfIndex`, `greedySchedulePassCertificate_bounds`,
  `computableInO_greedySchedulePass`, `computableInPolySpace_greedySchedulePass`,
  `constructBalancedSchedulesCertificate_bounds`, `computableInO_constructBalancedSchedules`,
  `computableInPolySpace_constructBalancedSchedules`: native time and workspace bounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §4.4, Lemma 4.5, pp. 30–32.
-/

@[expose] public section

namespace Cslib.BalancedSchedules

open Finset Cslib.GenericRAM Turing.MultiTapeTM
open scoped BigOperators

/-! ### Section 1: `(n + m)`-slot pass and empty-scope factor normalization -/

/-- Decode outer index `s < n + m` into `(false, s)` (`s < n`) or `(true, s - n)` (`n ≤ s < n + m`),
capping `s` at `n + m` so unary conversion stays bounded. -/
def slotOfIndex (n m s : ℕ) : Option (Bool × ℕ) :=
  let sCap := min (n + m) s
  if s < n then some (false, sCap)
  else if s < n + m then some (true, sCap - n)
  else none

/-- Runtime input tuple `((n, m, Q), (r, C), edges)` for full schedule construction. -/
abbrev ScheduleParams : Type := (ℕ × ℕ × ℕ) × (ℕ × ℕ) × List (ℕ × ℕ)

/-- Return `some slot` when `s < n + m` points to a still-unassigned slot, or `none` otherwise. -/
def pendingSlotOfState
    (state : ℕ × (ScheduleParams × (List (Option (List ℕ)) × List (Option (List ℕ))))) :
    Option (Bool × ℕ) :=
  (slotOfIndex state.2.1.1.1 state.2.1.1.2.1 state.1).elim none fun slot =>
    if (readSlotSchedule slot state.2.2).isSome then none else some slot

/-- Outer `IndexFold.run` callback fixing unassigned slot `s < n + m` via `streamBestSlotLabel`. -/
def greedySlotStepBody
    (state : ℕ × (ScheduleParams × (List (Option (List ℕ)) × List (Option (List ℕ))))) :
    ScheduleParams × (List (Option (List ℕ)) × List (Option (List ℕ))) :=
  (pendingSlotOfState state).elim state.2 fun slot =>
    let p := state.2.1
    let chosen := streamBestSlotLabel p.1.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2 state.2.2 slot
    (p, updateSlotSchedules slot (some chosen) state.2.2)

/-- Full `(n + m)`-slot greedy partial-schedule pass implemented with `IndexFold.run`. -/
def greedySchedulePass (n m Q r C : ℕ) (edges : List (ℕ × ℕ)) :
    List (Option (List ℕ)) × List (Option (List ℕ)) :=
  (IndexFold.run greedySlotStepBody (n + m)
    (((n, m, Q), (r, C), edges), (List.replicate n none, List.replicate m none))).2.2

/-- Replace schedules of empty-scope factors (`∀ e ∈ edges, e.1 ≠ f`) with `List.replicate Q 0`. -/
def normalizeEmptyFactorSchedules (Q : ℕ) (edges : List (ℕ × ℕ))
    (facWords : List (List ℕ)) : List (List ℕ) :=
  (List.range facWords.length).map fun f =>
    if edges.any (fun e => decide (e.1 = f)) then facWords.getD f [] else List.replicate Q 0

/-- Construct complete balanced variable and factor schedules `(varWords, facWords)` over `[r]^Q`
by streaming all `r ^ Q` candidates at each slot and normalizing empty-scope factors (Lemma 4.5). -/
def constructBalancedSchedules (n m Q r C : ℕ) (edges : List (ℕ × ℕ)) :
    List (List ℕ) × List (List ℕ) :=
  let raw := greedySchedulePass n m Q r C edges
  (raw.1.map fun o => o.getD (List.replicate Q 0),
    normalizeEmptyFactorSchedules Q edges (raw.2.map fun o => o.getD (List.replicate Q 0)))

/-! ### Section 2: Prefix invariants and Lemma 4.5 occupancy bounds -/

private theorem run_greedySlotStepBody_params (params : ScheduleParams)
    (initScheds : List (Option (List ℕ)) × List (Option (List ℕ))) (s : ℕ) :
    (IndexFold.run greedySlotStepBody s (params, initScheds)).2.1 = params := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [IndexFold.run_succ]; simp only [IndexFold.step, greedySlotStepBody]
    cases pendingSlotOfState _ <;> simp only [Option.elim_none, Option.elim_some, ih]

/-- Outer-loop prefix invariant: at every slot prefix `s`, `varSched` has length `n`, `facSched`
has length `m`, and every assigned word has length `Q` with digits `< max r 1`. -/
theorem run_greedySlotStepBody_wf (n m Q r C : ℕ) (edges : List (ℕ × ℕ)) (s : ℕ) :
    let scheds := (IndexFold.run greedySlotStepBody s
      (((n, m, Q), (r, C), edges), (List.replicate n none, List.replicate m none))).2.2
    scheds.1.length = n ∧ scheds.2.length = m ∧
      (∀ o ∈ scheds.1, ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1) ∧
      (∀ o ∈ scheds.2, ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1) := by
  induction s with
  | zero =>
    simp only [IndexFold.run_zero, List.length_replicate, true_and]
    have hnone (N : ℕ) : ∀ o ∈ List.replicate N (none : Option (List ℕ)),
        ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1 := fun o ho _ hw => by
      rcases List.mem_replicate.mp ho with ⟨_, rfl⟩; cases hw
    exact ⟨hnone n, hnone m⟩
  | succ s ih =>
    have hp := run_greedySlotStepBody_params ((n, m, Q), (r, C), edges)
      (List.replicate n none, List.replicate m none) s
    rw [IndexFold.run_succ]; simp only [IndexFold.step, greedySlotStepBody]
    cases pendingSlotOfState _ with
    | none => exact ih
    | some slot =>
      simp only [Option.elim_some]; rw [hp]
      have hset {L : List (Option (List ℕ))} {idx : ℕ} {chosen : List ℕ}
          (hL : ∀ o ∈ L, ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1)
          (hcl : chosen.length = Q) (hcm : ∀ x ∈ chosen, x < max r 1) :
          ∀ o ∈ L.set idx (some chosen), ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1 :=
        fun o ho w hw => by
          rcases List.mem_or_eq_of_mem_set ho with hmem | heq
          · exact hL o hmem w hw
          · rw [heq] at hw; injection hw with hw'; subst hw'; exact ⟨hcl, hcm⟩
      rcases slot with ⟨isFac, idx⟩; cases isFac
      · simp only [updateSlotSchedules, Bool.false_eq_true, ↓reduceIte, List.length_set]
        exact ⟨ih.1, ih.2.1, hset ih.2.2.1 (length_streamBestSlotLabel _ _ _ _ _ _ _)
          (fun _ hx => mem_streamBestSlotLabel_lt_max _ _ _ _ _ _ _ hx), ih.2.2.2⟩
      · simp only [updateSlotSchedules, ↓reduceIte, List.length_set]
        exact ⟨ih.1, ih.2.1, ih.2.2.1, hset ih.2.2.2 (length_streamBestSlotLabel _ _ _ _ _ _ _)
          (fun _ hx => mem_streamBestSlotLabel_lt_max _ _ _ _ _ _ _ hx)⟩

@[simp] theorem length_fst_constructBalancedSchedules (n m Q r C : ℕ) (edges : List (ℕ × ℕ)) :
    (constructBalancedSchedules n m Q r C edges).1.length = n := by
  simp only [constructBalancedSchedules, greedySchedulePass, List.length_map,
    (run_greedySlotStepBody_wf n m Q r C edges (n + m)).1]

@[simp] theorem length_snd_constructBalancedSchedules (n m Q r C : ℕ) (edges : List (ℕ × ℕ)) :
    (constructBalancedSchedules n m Q r C edges).2.length = m := by
  simp only [constructBalancedSchedules, normalizeEmptyFactorSchedules, List.length_map,
    List.length_range, greedySchedulePass, (run_greedySlotStepBody_wf n m Q r C edges (n + m)).2.1]

/-- Every variable and factor word produced by `constructBalancedSchedules` has exact length `Q`
and digits `< max r 1` (hence `< r` whenever `1 ≤ r`). -/
theorem wf_constructBalancedSchedules (n m Q r C : ℕ) (edges : List (ℕ × ℕ)) :
    (∀ w ∈ (constructBalancedSchedules n m Q r C edges).1,
      w.length = Q ∧ ∀ x ∈ w, x < max r 1) ∧
    (∀ w ∈ (constructBalancedSchedules n m Q r C edges).2,
      w.length = Q ∧ ∀ x ∈ w, x < max r 1) := by
  obtain ⟨_, hm_len, hwf1, hwf2⟩ := run_greedySlotStepBody_wf n m Q r C edges (n + m)
  have hrep : (List.replicate Q 0).length = Q ∧ ∀ x ∈ List.replicate Q 0, x < max r 1 :=
    ⟨List.length_replicate, fun x hx => by rcases List.mem_replicate.mp hx with ⟨_, rfl⟩; omega⟩
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · simp only [constructBalancedSchedules, greedySchedulePass, List.mem_map] at hw
    obtain ⟨o, ho, rfl⟩ := hw; cases o with
    | none => simpa only [Option.getD_none] using hrep
    | some u => simpa only [Option.getD_some] using hwf1 (some u) ho u rfl
  · simp only [constructBalancedSchedules, normalizeEmptyFactorSchedules, List.mem_map,
      List.mem_range, List.length_map, greedySchedulePass, hm_len] at hw
    obtain ⟨f, hf, hw_eq⟩ := hw; split_ifs at hw_eq
    · subst hw_eq
      let raw2 := (IndexFold.run greedySlotStepBody (n + m)
        (((n, m, Q), (r, C), edges), (List.replicate n none, List.replicate m none))).2.2.2
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, hm_len]; exact hf),
        List.getElem_map]
      have hmem : raw2[f] ∈ raw2 := List.getElem_mem (by rw [hm_len]; exact hf)
      cases ho : raw2[f] with
      | none => simpa only [Option.getD_none] using hrep
      | some u => rw [ho] at hmem; simpa only [Option.getD_some] using hwf2 (some u) hmem u rfl
    · subst hw_eq; exact hrep

/-- Concrete empty-factor normalization: any factor `f < m` absent from `edges` gets
`List.replicate Q 0`. -/
theorem getD_constructBalancedSchedules_empty_factor {n m Q r C f : ℕ} (hf : f < m)
    (edges : List (ℕ × ℕ)) (hempty : ∀ e ∈ edges, e.1 ≠ f) :
    ((constructBalancedSchedules n m Q r C edges).2).getD f [] = List.replicate Q 0 := by
  have hm := (run_greedySlotStepBody_wf n m Q r C edges (n + m)).2.1
  simp only [constructBalancedSchedules, normalizeEmptyFactorSchedules, greedySchedulePass]
  rw [List.getD_map_range _ [] (by simp only [List.length_map, hm]; exact hf)]
  have hany : edges.any (fun e => decide (e.1 = f)) = false :=
    List.any_eq_false.mpr fun e he => by
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]; exact hempty e he
  simp only [hany, Bool.false_eq_true, ↓reduceIte]

/-- Exact bridge between the runtime `IndexFold.run` schedule pass `greedySchedulePass` and the
combinatorial specification `greedyLabelPass`. -/
theorem greedySchedulePass_eq_greedyLabelPass {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (C : ℕ) :
    greedySchedulePass n m Q r C (edgesOfFin edge) =
      let slots : List (Fin n ⊕ Fin m) :=
        (List.ofFn fun v : Fin n => Sum.inl v) ++ (List.ofFn fun f : Fin m => Sum.inr f)
      let res := greedyLabelPass edge C (candidateScheduleList hr Q) slots
        (fun _ => none, fun _ => none)
      (partialScheduleListOfFin res.1, partialScheduleListOfFin res.2) := by
  dsimp only
  let toLists (assigned : (Fin n → Option (Fin Q → Fin r)) × (Fin m → Option (Fin Q → Fin r))) :=
    (partialScheduleListOfFin assigned.1, partialScheduleListOfFin assigned.2)
  have hstep_var (assigned : (Fin n → Option (Fin Q → Fin r)) × (Fin m → Option (Fin Q → Fin r)))
      (v : Fin n) :
      (if (readSlotSchedule (false, v.val) (toLists assigned)).isSome then toLists assigned
        else updateSlotSchedules (false, v.val)
          (some (streamBestSlotLabel n Q r C (edgesOfFin edge) (toLists assigned) (false, v.val)))
          (toLists assigned)) =
        toLists (greedyLabelStep edge C (candidateScheduleList hr Q) assigned (.inl v)) := by
    have hread : readSlotSchedule (false, v.val) (toLists assigned) =
        (assigned.1 v).map scheduleToWord := by
      simp only [toLists, readSlotSchedule, Bool.false_eq_true, ↓reduceIte,
        partialScheduleListOfFin, List.getD_ofFn]
    rw [hread]; dsimp only [toLists]
    cases hv : assigned.1 v with
    | some _ => simp only [Option.map_some, Option.isSome_some, ↓reduceIte, greedyLabelStep, hv]
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        greedyLabelStep, hv, updateSlotSchedules,
        set_partialScheduleListOfFin (hr := hr) assigned.1 v _
          (length_streamBestSlotLabel _ _ _ _ _ _ _)
          (fun _ hx => mem_streamBestSlotLabel_lt hr _ _ _ _ _ _ hx)]
      rw [streamBestSlotLabel_false_eq_bestVariableLabel hr edge assigned.1 assigned.2 C v]
  have hstep_fac (assigned : (Fin n → Option (Fin Q → Fin r)) × (Fin m → Option (Fin Q → Fin r)))
      (f : Fin m) :
      (if (readSlotSchedule (true, f.val) (toLists assigned)).isSome then toLists assigned
        else updateSlotSchedules (true, f.val)
          (some (streamBestSlotLabel n Q r C (edgesOfFin edge) (toLists assigned) (true, f.val)))
          (toLists assigned)) =
        toLists (greedyLabelStep edge C (candidateScheduleList hr Q) assigned (.inr f)) := by
    have hread : readSlotSchedule (true, f.val) (toLists assigned) =
        (assigned.2 f).map scheduleToWord := by
      simp only [toLists, readSlotSchedule, ↓reduceIte, partialScheduleListOfFin, List.getD_ofFn]
    rw [hread]; dsimp only [toLists]
    cases hf : assigned.2 f with
    | some _ => simp only [Option.map_some, Option.isSome_some, ↓reduceIte, greedyLabelStep, hf]
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        greedyLabelStep, hf, updateSlotSchedules,
        set_partialScheduleListOfFin (hr := hr) assigned.2 f _
          (length_streamBestSlotLabel _ _ _ _ _ _ _)
          (fun _ hx => mem_streamBestSlotLabel_lt hr _ _ _ _ _ _ hx)]
      rw [streamBestSlotLabel_true_eq_bestFactorLabel hr edge assigned.1 assigned.2 C f]
  let slotFin (s : ℕ) (hs : s < n + m) : Fin n ⊕ Fin m :=
    if h : s < n then .inl ⟨s, h⟩ else .inr ⟨s - n, by omega⟩
  have hslots_eq : (List.ofFn fun v : Fin n => (Sum.inl v : Fin n ⊕ Fin m)) ++
      (List.ofFn fun f : Fin m => Sum.inr f) =
      List.ofFn fun i : Fin (n + m) => slotFin i.val i.isLt := by
    apply List.ext_getElem (by simp only [List.length_append, List.length_ofFn])
    intro s _ hsm; simp only [List.length_ofFn] at hsm
    simp only [List.getElem_ofFn]; by_cases hsn : s < n
    · rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact hsn)]
      simp only [List.getElem_ofFn, slotFin, hsn, ↓reduceDIte]
    · rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
      simp only [List.length_ofFn, List.getElem_ofFn, slotFin, hsn, ↓reduceDIte]
  rw [hslots_eq, greedySchedulePass]
  let params : ScheduleParams := ((n, m, Q), (r, C), edgesOfFin edge)
  let initScheds := (List.replicate n (none : Option (List ℕ)),
    List.replicate m (none : Option (List ℕ)))
  have hrep_ofFn (N : ℕ) : List.replicate N (none : Option (List ℕ)) =
      partialScheduleListOfFin (Q := Q) (r := r) (fun _ : Fin N => none) := by
    simp only [partialScheduleListOfFin, Option.map_none, List.ofFn_const]
  have hloop : ∀ k (hk : k ≤ n + m),
      (IndexFold.run greedySlotStepBody k (params, initScheds)).2.2 =
        toLists (greedyLabelPass edge C (candidateScheduleList hr Q)
          (List.ofFn fun i : Fin k => slotFin i.val (lt_of_lt_of_le i.isLt hk))
          (fun _ => none, fun _ => none)) := by
    intro k hk; induction k with
    | zero =>
      simp only [IndexFold.run_zero, List.ofFn_zero, greedyLabelPass, List.foldl_nil, initScheds,
        toLists]
      exact Prod.ext (hrep_ofFn n) (hrep_ofFn m)
    | succ k ih =>
      have hk_lt : k < n + m := by omega
      let prev := greedyLabelPass edge C (candidateScheduleList hr Q)
        (List.ofFn fun i : Fin k => slotFin i.val (lt_trans i.isLt hk_lt))
        (fun _ => none, fun _ => none)
      have hst_eta : IndexFold.run greedySlotStepBody k (params, initScheds) =
          (k, (params, toLists prev)) :=
        Prod.ext (IndexFold.run_index _ _ _)
          (Prod.ext (run_greedySlotStepBody_params _ _ _) (ih (Nat.le_of_lt hk_lt)))
      have hsnoc : greedyLabelPass edge C (candidateScheduleList hr Q)
          (List.ofFn fun i : Fin (k + 1) => slotFin i.val (lt_of_lt_of_le i.isLt hk))
          (fun _ => none, fun _ => none) =
          greedyLabelStep edge C (candidateScheduleList hr Q) prev (slotFin k hk_lt) := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp only [Fin.val_castSucc, Fin.val_last, greedyLabelPass, List.foldl_append,
          List.foldl_cons, List.foldl_nil, prev]
      rw [hsnoc, IndexFold.run_succ, hst_eta]
      simp only [IndexFold.step, greedySlotStepBody, pendingSlotOfState, params]
      by_cases hkn : k < n
      · have hsl : slotOfIndex n m k = some (false, k) := by
          simp only [slotOfIndex, min_eq_right (Nat.le_of_lt hk_lt), hkn, ↓reduceIte]
        have hv := hstep_var prev ⟨k, hkn⟩
        simp only [hsl, Option.elim_some, slotFin, hkn, ↓reduceDIte]
        cases hcond : (readSlotSchedule (false, k) (toLists prev)).isSome <;>
          simpa only [hcond, ↓reduceIte, Bool.false_eq_true, Option.elim_none,
            Option.elim_some] using hv
      · have hsl : slotOfIndex n m k = some (true, k - n) := by
          simp only [slotOfIndex, min_eq_right (Nat.le_of_lt hk_lt), hkn, hk_lt, ↓reduceIte]
        have hf := hstep_fac prev ⟨k - n, by omega⟩
        simp only [hsl, Option.elim_some, slotFin, hkn, ↓reduceDIte]
        cases hcond : (readSlotSchedule (true, k - n) (toLists prev)).isSome <;>
          simpa only [hcond, ↓reduceIte, Bool.false_eq_true, Option.elim_none,
            Option.elim_some] using hf
  exact hloop (n + m) le_rfl

/-- Typed variable schedule `Fin n → Fin Q → Fin r` extracted from `constructBalancedSchedules`. -/
def constructedVarSchedule {r : ℕ} (hr : 1 ≤ r) (n m Q C : ℕ) (edges : List (ℕ × ℕ))
    (v : Fin n) : Fin Q → Fin r :=
  wordToSchedule hr Q (((constructBalancedSchedules n m Q r C edges).1).getD v.val [])

/-- Typed factor schedule `Fin m → Fin Q → Fin r` extracted from `constructBalancedSchedules`. -/
def constructedFactorSchedule {r : ℕ} (hr : 1 ≤ r) (n m Q C : ℕ) (edges : List (ℕ × ℕ))
    (f : Fin m) : Fin Q → Fin r :=
  wordToSchedule hr Q (((constructBalancedSchedules n m Q r C edges).2).getD f.val [])

/-- Typed schedules extracted from `constructBalancedSchedules` coincide with completing and
normalizing `greedyLabelPass`. -/
theorem constructedSchedules_eq_pass {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (C : ℕ) :
    let g₀ : Fin r := ⟨0, hr⟩
    let slots : List (Fin n ⊕ Fin m) :=
      (List.ofFn fun v : Fin n => Sum.inl v) ++ (List.ofFn fun f : Fin m => Sum.inr f)
    let raw := greedyLabelPass edge C (candidateScheduleList hr Q) slots
      (fun _ => none, fun _ => none)
    constructedVarSchedule hr n m Q C (edgesOfFin edge) =
        completeLabels raw.1 (fun _ _ => g₀) ∧
      constructedFactorSchedule hr n m Q C (edgesOfFin edge) =
        normalizeEmptyFactors (fun e => (edge e).1) g₀ (completeLabels raw.2 (fun _ _ => g₀)) := by
  dsimp only
  let slots : List (Fin n ⊕ Fin m) :=
    (List.ofFn fun v : Fin n => Sum.inl v) ++ (List.ofFn fun f : Fin m => Sum.inr f)
  let raw := greedyLabelPass edge C (candidateScheduleList hr Q) slots
    (fun _ => none, fun _ => none)
  have hpass := greedySchedulePass_eq_greedyLabelPass (Q := Q) hr edge C
  have hw0 : wordToSchedule hr Q (List.replicate Q 0) = fun _ => ⟨0, hr⟩ := by
    funext t; rw [wordToSchedule]
    have hget : (List.replicate Q 0).getD t.val 0 = 0 := by
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_replicate]; exact t.isLt)]
      simp only [List.getElem_replicate]
    rw [hget]; split_ifs <;> rfl
  refine ⟨funext fun v => ?_, funext fun f => ?_⟩
  · simp only [constructedVarSchedule]
    rw [List.getD_eq_getElem _ _ (by rw [length_fst_constructBalancedSchedules]; exact v.isLt)]
    simp only [constructBalancedSchedules, hpass, List.getElem_map, partialScheduleListOfFin,
      List.getElem_ofFn, completeLabels]
    cases raw.1 v <;> simp only [Option.map_none, Option.map_some, Option.getD_none,
      Option.getD_some, hw0, wordToSchedule_scheduleToWord]
  · simp only [constructedFactorSchedule]
    rw [List.getD_eq_getElem _ _ (by rw [length_snd_constructBalancedSchedules]; exact f.isLt)]
    simp only [constructBalancedSchedules, normalizeEmptyFactorSchedules, hpass,
      List.getElem_map, List.getElem_range]
    have hany_iff : (edgesOfFin edge).any (fun e => decide (e.1 = f.val)) = true ↔
        ∃ e : Fin E, (edge e).1 = f := by
      simp only [edgesOfFin, List.any_eq_true, List.mem_ofFn, decide_eq_true_eq, Fin.ext_iff]
      exact ⟨fun ⟨_, ⟨e, rfl⟩, he⟩ => ⟨e, he⟩, fun ⟨e, he⟩ => ⟨_, ⟨e, rfl⟩, he⟩⟩
    by_cases hex : ∃ e : Fin E, (edge e).1 = f
    · simp only [hany_iff.mpr hex, ↓reduceIte]; obtain ⟨e, rfl⟩ := hex
      rw [normalizeEmptyFactors_factorOf (factorOf := fun e => (edge e).1),
        List.getD_eq_getElem _ _
          (by simp only [List.length_map, length_partialScheduleListOfFin]; exact (edge e).1.isLt)]
      simp only [List.getElem_map, partialScheduleListOfFin, List.getElem_ofFn, completeLabels]
      cases raw.2 (edge e).1 <;> simp only [Option.map_none, Option.map_some, Option.getD_none,
        Option.getD_some, hw0, wordToSchedule_scheduleToWord]
    · have hany : (edgesOfFin edge).any (fun e => decide (e.1 = f.val)) = false :=
        Bool.eq_false_iff.mpr fun h => hex (hany_iff.mp h)
      rw [normalizeEmptyFactors_of_not_exists _ _ _ hex]
      simp only [hany, Bool.false_eq_true, ↓reduceIte, hw0]

/-- Empty-scope factor schedules are normalized to the constant zero group `⟨0, hr⟩`. -/
theorem constructedFactorSchedule_empty_factor {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (C : ℕ) {f : Fin m} (hf : ¬ ∃ e : Fin E, (edge e).1 = f) :
    constructedFactorSchedule hr n m Q C (edgesOfFin edge) f = fun _ => ⟨0, hr⟩ := by
  rw [(constructedSchedules_eq_pass (Q := Q) hr edge C).2]
  exact normalizeEmptyFactors_of_not_exists _ _ _ hf

/-- `constructBalancedSchedules` achieves joint normalized potential at most the initial
finite-uniform average over `(Fin n → Fin Q → Fin r) × (Fin m → Fin Q → Fin r)`. -/
theorem constructBalancedSchedules_score_le {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (C : ℕ) :
    let a := constructedVarSchedule hr n m Q C (edgesOfFin edge)
    let d := constructedFactorSchedule hr n m Q C (edgesOfFin edge)
    potential (fun e => (a (edge e).2, d (edge e).1)) / ((E : ℚ) * C) +
      (∑ t : Fin Q, potential (fun v => a v t)) / ((Q : ℚ) * n) ≤
      𝔼 a' : Fin n → Fin Q → Fin r, 𝔼 d' : Fin m → Fin Q → Fin r,
        (potential (fun e => (a' (edge e).2, d' (edge e).1)) / ((E : ℚ) * C) +
          (∑ t : Fin Q, potential (fun v => a' v t)) / ((Q : ℚ) * n)) := by
  dsimp only
  let g₀ : Fin r := ⟨0, hr⟩; let : Nonempty (Fin r) := ⟨g₀⟩
  let slots : List (Fin n ⊕ Fin m) :=
    (List.ofFn fun v : Fin n => Sum.inl v) ++ (List.ofFn fun f : Fin m => Sum.inr f)
  let raw := greedyLabelPass edge C (candidateScheduleList hr Q) slots
    (fun _ => none, fun _ => none)
  obtain ⟨hscore, hfill, -⟩ := greedyLabelPass_spec edge C (candidateScheduleList hr Q)
    (mem_candidateScheduleList hr Q) slots (fun _ => none, fun _ => none)
  have hvar (a' : Fin n → Fin Q → Fin r) :
      completeLabels raw.1 a' = completeLabels raw.1 (fun _ _ => g₀) := funext fun v => by
    obtain ⟨word, hw⟩ := hfill (.inl v) (List.mem_append_left _ (List.mem_ofFn.mpr ⟨v, rfl⟩))
    change raw.1 v = some word at hw; simp only [completeLabels, hw, Option.getD_some]
  have hfac (d' : Fin m → Fin Q → Fin r) :
      completeLabels raw.2 d' = completeLabels raw.2 (fun _ _ => g₀) := funext fun f => by
    obtain ⟨word, hw⟩ := hfill (.inr f) (List.mem_append_right _ (List.mem_ofFn.mpr ⟨f, rfl⟩))
    change raw.2 f = some word at hw; simp only [completeLabels, hw, Option.getD_some]
  have hout := normalizedPartialScore_eq_expect edge raw.1 raw.2 C
  simp only [hvar, hfac, Fintype.expect_const, Fintype.card_fin] at hout
  have hin := normalizedPartialScore_eq_expect (T := Fin Q) (G := Fin r) edge
    (fun _ => none) (fun _ => none) C
  simp only [completeLabels, Option.getD_none, Fintype.card_fin] at hin
  obtain ⟨ha_eq, hd_eq⟩ := constructedSchedules_eq_pass (Q := Q) hr edge C
  have hinc : (fun e => (constructedVarSchedule hr n m Q C (edgesOfFin edge) (edge e).2,
        constructedFactorSchedule hr n m Q C (edgesOfFin edge) (edge e).1)) =
      (fun e => (completeLabels raw.1 (fun _ _ => g₀) (edge e).2,
        completeLabels raw.2 (fun _ _ => g₀) (edge e).1)) := funext fun e => by
    rw [ha_eq, hd_eq, normalizeEmptyFactors_factorOf (factorOf := fun e => (edge e).1)]
  rw [hinc, ha_eq, ← hin]; exact hout.symm.trans_le hscore

/-- Under Lemma 4.5's degree hypotheses (`hb`, `hw`), `constructBalancedSchedules` achieves joint
normalized potential at most `2`. -/
theorem constructBalancedSchedules_score_le_two {E m n Q r : ℕ}
    (hr : 1 ≤ r) (hQ : 1 ≤ Q) (hn : 1 ≤ n) (hE : 0 < E)
    (edge : Fin E → Fin m × Fin n) {b w : ℕ}
    (hb : ∀ e : Fin E, #{e' : Fin E | (edge e').2 = (edge e).2} ≤ b)
    (hw : ∀ e : Fin E, #{e' : Fin E | (edge e').1 = (edge e).1} ≤ w)
    (hbw : 0 < b + w) :
    let a := constructedVarSchedule hr n m Q (b + w) (edgesOfFin edge)
    let d := constructedFactorSchedule hr n m Q (b + w) (edgesOfFin edge)
    potential (fun e => (a (edge e).2, d (edge e).1)) / ((E : ℚ) * (b + w : ℕ)) +
      (∑ t : Fin Q, potential (fun v => a v t)) / ((Q : ℚ) * n) ≤ 2 := by
  dsimp only; let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hx : (0 : ℚ) < (E : ℚ) * (b + w : ℕ) := by positivity
  have hy : (0 : ℚ) < (Q : ℚ) * n := by positivity
  have h1 : (𝔼 a' : Fin n → Fin Q → Fin r, 𝔼 d' : Fin m → Fin Q → Fin r,
      potential (fun e => (a' (edge e).2, d' (edge e).1)) / ((E : ℚ) * (b + w : ℕ))) ≤ 1 := by
    simp_rw [div_eq_mul_inv, ← Finset.expect_mul, ← div_eq_mul_inv]; rw [div_le_one hx]
    have h := expect_incidence_potential_le (L := Fin Q → Fin r)
      (fun e => (edge e).2) (fun e => (edge e).1) hb hw
    unfold incidenceLabel at h; simpa only [Fintype.card_fin, Nat.cast_add] using h
  have h2 : (𝔼 a' : Fin n → Fin Q → Fin r,
      (∑ t : Fin Q, potential (fun v => a' v t)) / ((Q : ℚ) * n)) ≤ 1 := by
    simp_rw [div_eq_mul_inv, ← Finset.expect_mul, ← div_eq_mul_inv]; rw [div_le_one hy]
    simpa only [Fintype.card_fin] using
      (expect_group_potential_le (T := Fin Q) (V := Fin n) (G := Fin r))
  apply (constructBalancedSchedules_score_le hr edge (b + w)).trans
  simp only [Finset.expect_add_distrib, Fintype.expect_const]; linarith

/-- **Lemma 4.5 correctness for `constructBalancedSchedules` ([OpenAI2026ETH], pp. 30–31)**:
under degree bounds `hb`, `hw`, `0 < b + w`, and size bounds (4.13)
`2 * (b + w) * ((r ^ Q) ^ 2) ^ 2 ≤ E` and `2 * Q * r ^ 2 ≤ n`, the runtime output satisfies
empty-factor normalization and both incidence and variable-group occupancy bounds. -/
theorem constructBalancedSchedules_balanced {E m n Q r : ℕ}
    (hr : 1 ≤ r) (hQ : 1 ≤ Q) (hn : 1 ≤ n)
    (edge : Fin E → Fin m × Fin n) {b w : ℕ}
    (hb : ∀ e : Fin E, #{e' : Fin E | (edge e').2 = (edge e).2} ≤ b)
    (hw : ∀ e : Fin E, #{e' : Fin E | (edge e').1 = (edge e).1} ≤ w)
    (hbw : 0 < b + w)
    (hincidenceSize : 2 * (b + w) * ((r ^ Q) ^ 2) ^ 2 ≤ E)
    (hgroupSize : 2 * Q * r ^ 2 ≤ n) :
    let a := constructedVarSchedule hr n m Q (b + w) (edgesOfFin edge)
    let d := constructedFactorSchedule hr n m Q (b + w) (edgesOfFin edge)
    (∀ f : Fin m, (¬ ∃ e : Fin E, (edge e).1 = f) → d f = fun _ => ⟨0, hr⟩) ∧
      (∀ u : (Fin Q → Fin r) × (Fin Q → Fin r),
        occupancy (fun e => (a (edge e).2, d (edge e).1)) u * (r ^ Q) ^ 2 ≤ 2 * E) ∧
      (∀ t : Fin Q, ∀ g : Fin r,
        occupancy (fun v => a v t) g * r ≤ 2 * n) := by
  dsimp only
  have hD : 0 < (r ^ Q) ^ 2 := Nat.pow_pos (Nat.pow_pos hr)
  have hE : 0 < E :=
    (by positivity : 0 < 2 * (b + w) * ((r ^ Q) ^ 2) ^ 2).trans_le hincidenceSize
  have hcardB : Fintype.card ((Fin Q → Fin r) × (Fin Q → Fin r)) = (r ^ Q) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, sq]
  have hbounds := incidence_and_group_bounds
    (fun e => (constructedVarSchedule hr n m Q (b + w) (edgesOfFin edge) (edge e).2,
      constructedFactorSchedule hr n m Q (b + w) (edgesOfFin edge) (edge e).1))
    (fun t v => constructedVarSchedule hr n m Q (b + w) (edgesOfFin edge) v t)
    (b + w) (by simp only [Fintype.card_fin]; exact hE) (by rw [hcardB]; exact hD) hbw
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
    (by simp only [Fintype.card_fin]; omega)
    (by simpa only [Fintype.card_fin, hcardB] using hincidenceSize)
    (by simpa only [Fintype.card_fin] using hgroupSize)
    (by simpa only [Fintype.card_fin] using
      constructBalancedSchedules_score_le_two hr hQ hn hE edge hb hw hbw)
  refine ⟨fun f hf => constructedFactorSchedule_empty_factor hr edge (b + w) hf,
    fun u => ?_, fun t g => ?_⟩
  · simpa only [hcardB, Fintype.card_fin] using hbounds.1 u
  · simpa only [Fintype.card_fin] using hbounds.2 t g

/-! ### Section 3: Hypergraph-valid bit-length bounds and native machine certificates -/

/-- Encoding of runtime inputs `((n, m, Q), (r, C), edges)` to `constructBalancedSchedules`. -/
def encScheduleParams : ScheduleParams ↪ List Bool :=
  encPair (encPair encUnary (encPair encUnary encUnary))
    (encPair (encPair encNat encNat) (encList (encPair encNat encNat)))

/-- Encoding of outer `IndexFold` accumulator `(ScheduleParams, (varSched, facSched))`. -/
def encOuterAcc :
    (ScheduleParams × (List (Option (List ℕ)) × List (Option (List ℕ)))) ↪ List Bool :=
  encPair encScheduleParams encPartialSchedules

end Cslib.BalancedSchedules

end

public section

namespace Cslib.BalancedSchedules

open Finset Cslib.GenericRAM Turing.MultiTapeTM
open ComputableTidilyInO (length_encNat_mono)

private theorem length_encNat_le_self (k : ℕ) : (encNat k).length ≤ k := by
  rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self k

/-- Encoded bit-length bound for an incidence list `edges` with endpoints `< m` and `< n`. -/
theorem length_encEdges_le_of_lt {n m : ℕ} {edges : List (ℕ × ℕ)}
    (h : ∀ e ∈ edges, e.1 < m ∧ e.2 < n) :
    (encList (encPair encNat encNat) edges).length ≤
      edges.length * (6 * (encNat (n + m)).length + 3) := by
  rw [length_encList]
  have hle : ∀ x ∈ edges.map (fun e => 2 * (encPair encNat encNat e).length + 1),
      x ≤ 6 * (encNat (n + m)).length + 3 := by
    intro x hx; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx; obtain ⟨hf, hv⟩ := h e he
    have h1 := length_encNat_mono (by omega : e.1 ≤ n + m)
    have h2 := length_encNat_mono (by omega : e.2 ≤ n + m)
    rw [length_encPair]; omega
  simpa only [List.length_map, smul_eq_mul] using
    List.sum_le_length_nsmul _ (6 * (encNat (n + m)).length + 3) hle

/-- Encoded bit-length bound for partial schedule tables `(varSched, facSched)` of lengths `n, m`
whose assigned words have length `Q` and digits `< max r 1`. -/
theorem length_encPartialSchedules_le {n m Q r : ℕ}
    {scheds : List (Option (List ℕ)) × List (Option (List ℕ))}
    (h1 : scheds.1.length = n) (h2 : scheds.2.length = m)
    (hw1 : ∀ o ∈ scheds.1, ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1)
    (hw2 : ∀ o ∈ scheds.2, ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1) :
    (encPartialSchedules scheds).length ≤
      2 * (n + m) * (2 * Q * (2 * (encNat r).length + 1) + 3) + 1 := by
  have hlist {L : List (Option (List ℕ))} {N : ℕ} (hN : L.length = N)
      (hw : ∀ o ∈ L, ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1) :
      (encList (encOption (encList encNat)) L).length ≤
        N * (2 * Q * (2 * (encNat r).length + 1) + 3) := by
    rw [length_encList, ← hN]
    have hle : ∀ x ∈ L.map (fun o => 2 * (encOption (encList encNat) o).length + 1),
        x ≤ 2 * Q * (2 * (encNat r).length + 1) + 3 := by
      intro x hx; obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx; cases o with
      | none => simp only [encOption_none, List.length_nil]; omega
      | some w =>
        obtain ⟨hlw, hmw⟩ := hw (some w) ho w rfl
        have hwl := length_encList_word_le hlw hmw
        simp only [encOption_some, List.length_cons]
        linarith [show 2 * Q * (2 * (encNat r).length + 1) =
          2 * (Q * (2 * (encNat r).length + 1)) by ring]
    simpa only [List.length_map, smul_eq_mul] using
      List.sum_le_length_nsmul _ (2 * Q * (2 * (encNat r).length + 1) + 3) hle
  rw [encPartialSchedules, length_encPair]
  have hb1 := hlist h1 hw1; have hb2 := hlist h2 hw2
  have hnm : 2 * n + m ≤ 2 * (n + m) := by omega
  calc 2 * (encList (encOption (encList encNat)) scheds.1).length + 1 +
        (encList (encOption (encList encNat)) scheds.2).length
      ≤ 2 * (n * (2 * Q * (2 * (encNat r).length + 1) + 3)) + 1 +
          m * (2 * Q * (2 * (encNat r).length + 1) + 3) := by omega
    _ = (2 * n + m) * (2 * Q * (2 * (encNat r).length + 1) + 3) + 1 := by ring
    _ ≤ 2 * (n + m) * (2 * Q * (2 * (encNat r).length + 1) + 3) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ hnm) 1

/-- Explicit `O((n + m + 1) * (Q + 1) * log(r + 2) + |E| * log(n + m + 2) + log(C + 2))` inner-loop
prefix bit-length bound for valid hypergraph incidences and partial schedules. -/
theorem length_encSlotSelectState_run_valid_le {n m Q r C : ℕ} {edges : List (ℕ × ℕ)}
    {scheds : List (Option (List ℕ)) × List (Option (List ℕ))} {slot : Bool × ℕ} {j : ℕ}
    (hj : j ≤ r ^ Q) (hslot : slot.2 ≤ n + m)
    (hedges : ∀ e ∈ edges, e.1 < m ∧ e.2 < n)
    (h1 : scheds.1.length = n) (h2 : scheds.2.length = m)
    (hw1 : ∀ o ∈ scheds.1, ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1)
    (hw2 : ∀ o ∈ scheds.2, ∀ w, o = some w → w.length = Q ∧ ∀ x ∈ w, x < max r 1) :
    (encPair encNat encSlotSelectAcc
      (IndexFold.run selectSlotStep j
        (((n, Q), (r, C), edges), (slot, (scheds, none))))).length ≤
      36 * (n + m + 1) * (Q + 1) * ((encNat r).length + 1) +
        28 * edges.length * ((encNat (n + m)).length + 1) + 9 * (encNat C).length + 60 := by
  have hed := length_encEdges_le_of_lt hedges
  have hsch := length_encPartialSchedules_le h1 h2 hw1 hw2
  have helen := length_encNat_le_self edges.length
  have hnlen := length_encNat_le_self n; have hQlen := length_encNat_le_self Q
  refine (length_encSlotSelectState_run_le n Q r C edges scheds slot hj).trans ?_
  simp only [encStreamSlotIn, encScoreParams, length_encPair, encUnary_apply, List.length_replicate,
    encBool_apply, List.length_singleton]
  have hcub : 16 * ((n + m) * Q * (encNat r).length) + 8 * ((n + m) * Q) +
      8 * (Q * (encNat r).length) + 34 * (n + m) + 14 * Q + 18 * (encNat r).length + 36 ≤
      36 * (n + m + 1) * (Q + 1) * ((encNat r).length + 1) := by
    have h0 := Nat.zero_le (20 * ((n + m) * Q * (encNat r).length) + 28 * ((n + m) * Q) +
      36 * ((n + m) * (encNat r).length) + 28 * (Q * (encNat r).length))
    linarith [show 36 * (n + m + 1) * (Q + 1) * ((encNat r).length + 1) =
      (16 * ((n + m) * Q * (encNat r).length) + 8 * ((n + m) * Q) +
        8 * (Q * (encNat r).length) + 34 * (n + m) + 14 * Q + 18 * (encNat r).length + 36) +
      (20 * ((n + m) * Q * (encNat r).length) + 28 * ((n + m) * Q) +
        36 * ((n + m) * (encNat r).length) + 28 * (Q * (encNat r).length)) +
      2 * (n + m) + 22 * Q + 18 * (encNat r).length by ring]
  have hsch' : (encPartialSchedules scheds).length ≤
      8 * ((n + m) * Q * (encNat r).length) + 4 * ((n + m) * Q) + 6 * (n + m) + 1 := by
    linarith [hsch, show 2 * (n + m) * (2 * Q * (2 * (encNat r).length + 1) + 3) + 1 =
      8 * ((n + m) * Q * (encNat r).length) + 4 * ((n + m) * Q) + 6 * (n + m) + 1 by ring]
  have hed' : 4 * (encList (encPair encNat encNat) edges).length +
      2 * (encNat edges.length).length ≤ 28 * edges.length * ((encNat (n + m)).length + 1) := by
    linarith [hed, helen, show 28 * edges.length * ((encNat (n + m)).length + 1) =
      4 * (edges.length * (6 * (encNat (n + m)).length + 3)) +
      4 * (edges.length * (encNat (n + m)).length) + 16 * edges.length by ring,
      Nat.zero_le (edges.length * (encNat (n + m)).length)]
  linarith

/-- All-prefix live-state bit-length bound for the outer `(n + m)`-slot `IndexFold.run` loop across
every visited slot prefix `s ≤ n + m`, in terms of input parameters and valid edges. -/
theorem length_encOuterState_run_valid_le {n m Q r C : ℕ} {edges : List (ℕ × ℕ)}
    {s : ℕ} (hs : s ≤ n + m) (hedges : ∀ e ∈ edges, e.1 < m ∧ e.2 < n) :
    (encPair encNat encOuterAcc
      (IndexFold.run greedySlotStepBody s
        (((n, m, Q), (r, C), edges), (List.replicate n none, List.replicate m none)))).length ≤
      24 * (n + m + 1) * (Q + 1) * ((encNat r).length + 1) +
        28 * edges.length * ((encNat (n + m)).length + 1) + 8 * (encNat C).length + 40 := by
  let init := (List.replicate n (none : Option (List ℕ)),
    List.replicate m (none : Option (List ℕ)))
  have hp := run_greedySlotStepBody_params ((n, m, Q), (r, C), edges) init s
  obtain ⟨h1, h2, hw1, hw2⟩ := run_greedySlotStepBody_wf n m Q r C edges s
  have hsch := length_encPartialSchedules_le h1 h2 hw1 hw2
  have hed := length_encEdges_le_of_lt hedges
  have hslen := (length_encNat_le_self s).trans hs
  rw [IndexFold.length_run]
  rcases hst : (IndexFold.run greedySlotStepBody s (((n, m, Q), (r, C), edges), init)).2 with
    ⟨par, sc⟩
  have hpar : par = ((n, m, Q), (r, C), edges) := by simpa only [init, hst] using hp
  have hsc_eq : sc = (IndexFold.run greedySlotStepBody s
      (((n, m, Q), (r, C), edges), init)).2.2 := by simp only [hst]
  subst hpar; rw [← hsc_eq] at hsch
  simp only [encOuterAcc, encScheduleParams, length_encPair, encUnary_apply, List.length_replicate]
  have hcub : 8 * ((n + m) * Q * (encNat r).length) + 4 * ((n + m) * Q) +
      16 * (n + m) + 4 * Q + 8 * (encNat r).length + 24 ≤
      24 * (n + m + 1) * (Q + 1) * ((encNat r).length + 1) := by
    have h0 := Nat.zero_le (16 * ((n + m) * Q * (encNat r).length) + 20 * ((n + m) * Q) +
      24 * ((n + m) * (encNat r).length) + 24 * (Q * (encNat r).length))
    linarith [show 24 * (n + m + 1) * (Q + 1) * ((encNat r).length + 1) =
      (8 * ((n + m) * Q * (encNat r).length) + 4 * ((n + m) * Q) +
        16 * (n + m) + 4 * Q + 8 * (encNat r).length + 24) +
      (16 * ((n + m) * Q * (encNat r).length) + 20 * ((n + m) * Q) +
        24 * ((n + m) * (encNat r).length) + 24 * (Q * (encNat r).length)) +
      8 * (n + m) + 20 * Q + 16 * (encNat r).length by ring]
  have hsch' : (encPartialSchedules sc).length ≤
      8 * ((n + m) * Q * (encNat r).length) + 4 * ((n + m) * Q) + 6 * (n + m) + 1 := by
    linarith [hsch, show 2 * (n + m) * (2 * Q * (2 * (encNat r).length + 1) + 3) + 1 =
      8 * ((n + m) * Q * (encNat r).length) + 4 * ((n + m) * Q) + 6 * (n + m) + 1 by ring]
  have hed' : 2 * (encList (encPair encNat encNat) edges).length ≤
      28 * edges.length * ((encNat (n + m)).length + 1) := by
    linarith [hed, show 28 * edges.length * ((encNat (n + m)).length + 1) =
      2 * (edges.length * (6 * (encNat (n + m)).length + 3)) +
      16 * (edges.length * (encNat (n + m)).length) + 22 * edges.length by ring,
      Nat.zero_le (edges.length * (encNat (n + m)).length)]
  linarith

private theorem scheduleParams_parts_le (p : ScheduleParams) :
    p.1.1 + p.1.2.1 ≤ (encScheduleParams p).length ∧
      p.1.2.2 ≤ (encScheduleParams p).length ∧
      (encNat p.2.1.1).length ≤ (encScheduleParams p).length ∧
      (encNat p.2.1.2).length ≤ (encScheduleParams p).length ∧
      (encList (encPair encNat encNat) p.2.2).length ≤ (encScheduleParams p).length := by
  simp only [encScheduleParams, length_encPair, encUnary_apply, List.length_replicate]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Unconditional all-prefix live-state bit-length bound for the outer `(n + m)`-slot
`IndexFold.run` loop in terms of input bit length `L = |encScheduleParams p|`. -/
theorem length_encOuterState_run_le (p : ScheduleParams) {s : ℕ} (hs : s ≤ p.1.1 + p.1.2.1) :
    (encPair encNat encOuterAcc
      (IndexFold.run greedySlotStepBody s
        (p, (List.replicate p.1.1 none, List.replicate p.1.2.1 none)))).length ≤
      8 * (encScheduleParams p).length ^ 3 + 4 * (encScheduleParams p).length ^ 2 +
        10 * (encScheduleParams p).length + 3 := by
  let L := (encScheduleParams p).length; have hparts := scheduleParams_parts_le p
  let init := (List.replicate p.1.1 (none : Option (List ℕ)),
    List.replicate p.1.2.1 (none : Option (List ℕ)))
  have hp := run_greedySlotStepBody_params p init s
  obtain ⟨h1, h2, hw1, hw2⟩ :=
    run_greedySlotStepBody_wf p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2 s
  have hsch := length_encPartialSchedules_le h1 h2 hw1 hw2
  have hslen : (encNat s).length ≤ L := (length_encNat_le_self s).trans (hs.trans hparts.1)
  have hprod : 2 * (p.1.1 + p.1.2.1) * (2 * p.1.2.2 * (2 * (encNat p.2.1.1).length + 1) + 3) ≤
      2 * L * (2 * L * (2 * L + 1) + 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hparts.1)
      (Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hparts.2.1)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hparts.2.2.1) 1)) 3)
  rw [IndexFold.length_run]
  rcases hst : (IndexFold.run greedySlotStepBody s (p, init)).2 with ⟨par, sc⟩
  have hpar : par = p := by simpa only [init, hst] using hp
  have hsc_eq : sc = (IndexFold.run greedySlotStepBody s (p, init)).2.2 := by simp only [hst]
  subst hpar; rw [← hsc_eq] at hsch
  simp only [encOuterAcc, length_encPair]
  change 2 * (encNat s).length + 1 + (2 * L + 1 + (encPartialSchedules sc).length) ≤
    8 * L ^ 3 + 4 * L ^ 2 + 10 * L + 3
  linarith [hprod, show 2 * L * (2 * L * (2 * L + 1) + 3) = 8 * L ^ 3 + 4 * L ^ 2 + 6 * L by ring]

/-- `slotOfIndex` is computable in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_slotOfIndex :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => slotOfIndex p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encNat) (encOption (encPair encBool encUnary)) := by
  let eIn := encPair (encPair encUnary encUnary) encNat
  have hsCap : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => min (p.1.1 + p.1.2) p.2)
      eIn encUnary := by unfold eIn; fun_prop
  have hnBin : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1) eIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold eIn; fun_prop)
  have hnmBin : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1 + p.1.2) eIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold eIn; fun_prop)
  have hsBin : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2) eIn encNat := by
    unfold eIn; fun_prop
  have hlt1 := ComputableInPolyTime.binary_lt' hsBin hnBin
  have hlt2 := ComputableInPolyTime.binary_lt' hsBin hnmBin
  have hb1 : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => (some (false, min (p.1.1 + p.1.2) p.2) : Option (Bool × ℕ)))
      eIn (encOption (encPair encBool encUnary)) := by fun_prop
  have hb2 : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => (some (true, min (p.1.1 + p.1.2) p.2 - p.1.1) : Option (Bool × ℕ)))
      eIn (encOption (encPair encBool encUnary)) := by unfold eIn; fun_prop
  refine (hlt1.ite' hb1 (hlt2.ite' hb2 (.const none))).of_enc_eq fun p => ?_
  unfold slotOfIndex
  by_cases h1 : p.2 < p.1.1
  · simp only [h1, decide_true, ↓reduceIte]
  · by_cases h2 : p.2 < p.1.1 + p.1.2 <;>
      simp only [h1, h2, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]

private abbrev OuterAcc : Type :=
  ScheduleParams × (List (Option (List ℕ)) × List (Option (List ℕ)))
private abbrev OuterSt : Type := ℕ × OuterAcc
private abbrev encOuterSt : OuterSt ↪ List Bool := encPair encNat encOuterAcc
private abbrev encSlotOpt : Option (Bool × ℕ) ↪ List Bool := encOption (encPair encBool encUnary)
private abbrev encOuterSlot : (OuterSt × (Bool × ℕ)) ↪ List Bool :=
  encPair encOuterSt (encPair encBool encUnary)
private abbrev encFinIn : ((OuterSt × (Bool × ℕ)) × List ℕ) ↪ List Bool :=
  encPair encOuterSlot (encList encNat)
private abbrev encOutWords : (List (List ℕ) × List (List ℕ)) ↪ List Bool :=
  encPair (encList (encList encNat)) (encList (encList encNat))

private theorem computableInPolyTime_pendingSlotOfState :
    ComputableInPolyTime pendingSlotOfState encOuterSt encSlotOpt := by
  have hsl : ComputableInPolyTime
      (fun st : OuterSt => slotOfIndex st.2.1.1.1 st.2.1.1.2.1 st.1) encOuterSt encSlotOpt :=
    computableInPolyTime_slotOfIndex.comp
      (show ComputableInPolyTime (fun st : OuterSt => ((st.2.1.1.1, st.2.1.1.2.1), st.1))
          encOuterSt (encPair (encPair encUnary encUnary) encNat) by
        unfold encOuterSt encOuterAcc encScheduleParams; fun_prop)
  unfold pendingSlotOfState encSlotOpt
  refine ComputableInPolyTime.optionElimWithInput hsl (.const none) ?_
  have his : ComputableInPolyTime
      (fun q : OuterSt × (Bool × ℕ) => (readSlotSchedule q.2 q.1.2.2).isSome)
      (encPair encOuterSt (encPair encBool encUnary)) encBool :=
    ComputableInPolyTime.optionIsSome (computableInPolyTime_readSlotSchedule.comp
      (show ComputableInPolyTime (fun q : OuterSt × (Bool × ℕ) => (q.2, q.1.2.2))
        (encPair encOuterSt (encPair encBool encUnary)) _ by
        unfold encOuterSt encOuterAcc; fun_prop))
  exact his.ite' (.const none) (by fun_prop)

private def streamSlotInOfOuter (q : OuterSt × (Bool × ℕ)) : StreamSlotIn :=
  (((q.1.2.1.1.1, q.1.2.1.1.2.2), q.1.2.1.2), (q.2, q.1.2.2))

private def finishGreedySlotStep (q : (OuterSt × (Bool × ℕ)) × List ℕ) : OuterAcc :=
  (q.1.1.2.1, updateSlotSchedules q.1.2 (some q.2) q.1.1.2.2)

private theorem computableInPolyTime_streamSlotInOfOuter :
    ComputableInPolyTime streamSlotInOfOuter encOuterSlot encStreamSlotIn := by
  unfold streamSlotInOfOuter encOuterSlot encOuterSt encOuterAcc encScheduleParams encStreamSlotIn
    encScoreParams
  fun_prop

private theorem computableInPolyTime_finishGreedySlotStep :
    ComputableInPolyTime finishGreedySlotStep encFinIn encOuterAcc := by
  have hupd := computableInPolyTime_updateSlotSchedules.comp
    (show ComputableInPolyTime (fun q : _ => ((q.1.2, some q.2), q.1.1.2.2)) encFinIn
        (encPair (encPair (encPair encBool encUnary) (encOption (encList encNat)))
          encPartialSchedules) by
      unfold encFinIn encOuterSlot encOuterSt encOuterAcc; fun_prop)
  exact (show ComputableInPolyTime (fun q : _ => q.1.1.2.1) encFinIn encScheduleParams by
    unfold encFinIn encOuterSlot encOuterSt encOuterAcc; fun_prop).prod hupd

private noncomputable def mkGreedyStepCert
    (cPend : NativeCertificate pendingSlotOfState encOuterSt encSlotOpt)
    (cIn : NativeCertificate streamSlotInOfOuter encOuterSlot encStreamSlotIn)
    (cSlot : NativeCertificate (fun a : StreamSlotIn =>
        streamBestSlotLabel a.1.1.1 a.1.1.2 a.1.2.1.1 a.1.2.1.2 a.1.2.2 a.2.2 a.2.1)
      encStreamSlotIn (encList encNat))
    (cFin : NativeCertificate finishGreedySlotStep encFinIn encOuterAcc) :
    NativeCertificate greedySlotStepBody encOuterSt encOuterAcc :=
  let cId : NativeCertificate id encOuterSlot encOuterSlot :=
    NativeCertificate.linear (ComputableInO.of_linear (.of_eq fun _ => rfl))
  NativeCertificate.option cPend (NativeCertificate.linear (ComputableInO.snd encNat encOuterAcc))
    ((cFin.comp (cId.prod (cSlot.comp cIn))).congr fun _ => rfl)

private noncomputable def greedySlotStepBodyCertificate :
    NativeCertificate greedySlotStepBody encOuterSt encOuterAcc :=
  mkGreedyStepCert
    (NativeCertificate.ofPolyTime computableInPolyTime_pendingSlotOfState)
    (NativeCertificate.ofPolyTime computableInPolyTime_streamSlotInOfOuter)
    streamBestSlotCertificate
    (NativeCertificate.ofPolyTime computableInPolyTime_finishGreedySlotStep)

private def outerCount (p : ScheduleParams) : ℕ := p.1.1 + p.1.2.1

private def outerInit (p : ScheduleParams) : OuterAcc :=
  (p, (List.replicate p.1.1 none, List.replicate p.1.2.1 none))

private def finalizeBalancedSchedules (q : OuterAcc) : List (List ℕ) × List (List ℕ) :=
  let Q := q.1.1.2.2; let edges := q.1.2.2
  (q.2.1.map fun o => o.getD (List.replicate Q 0),
    normalizeEmptyFactorSchedules Q edges (q.2.2.map fun o => o.getD (List.replicate Q 0)))

private theorem computableInPolyTime_outerCount :
    ComputableInPolyTime outerCount encScheduleParams encNat := by
  unfold outerCount encScheduleParams
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

private theorem computableInPolyTime_outerInit :
    ComputableInPolyTime outerInit encScheduleParams encOuterAcc := by
  unfold outerInit encOuterAcc encScheduleParams encPartialSchedules; fun_prop

private theorem computableInPolyTime_finalizeBalancedSchedules :
    ComputableInPolyTime finalizeBalancedSchedules encOuterAcc encOutWords := by
  unfold finalizeBalancedSchedules normalizeEmptyFactorSchedules encOuterAcc encScheduleParams
    encPartialSchedules encOutWords
  let eEdges := encList (encPair encNat encNat)
  let ePar := encPair (encPair encUnary (encPair encUnary encUnary))
    (encPair (encPair encNat encNat) eEdges)
  let eOpt := encOption (encList encNat)
  let eIn := encPair ePar (encPair (encList eOpt) (encList eOpt))
  have hvar : ComputableInPolyTime
      (fun q : OuterAcc => q.2.1.map fun o => o.getD (List.replicate q.1.1.2.2 0))
      eIn (encList (encList encNat)) := by fun_prop
  have hraw2 : ComputableInPolyTime
      (fun q : OuterAcc => q.2.2.map fun o => o.getD (List.replicate q.1.1.2.2 0))
      eIn (encList (encList encNat)) := by fun_prop
  have hfac : ComputableInPolyTime
      (fun q : OuterAcc =>
        (List.range (q.2.2.map fun o => o.getD (List.replicate q.1.1.2.2 0)).length).map fun f =>
          if q.1.2.2.any (fun e => decide (e.1 = f)) then
            (q.2.2.map fun o => o.getD (List.replicate q.1.1.2.2 0)).getD f []
          else List.replicate q.1.1.2.2 0)
      eIn (encList (encList encNat)) := by
    refine ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp
        ((ComputableInPolyTime.length_list (encList encNat)).comp hraw2)) ?_
    have hany : ComputableInPolyTime
        (fun r : OuterAcc × ℕ => r.1.1.2.2.any fun e => decide (e.1 = r.2))
        (encPair eIn encUnary) encBool :=
      ComputableInPolyTime.anyWithInput (by fun_prop)
        (ComputableInPolyTime.decide_eq' (by fun_prop)
          (ComputableInPolyTime.unary_to_binary.comp (by fun_prop)))
    have hthen : ComputableInPolyTime
        (fun r : OuterAcc × ℕ =>
          (r.1.2.2.map fun o => o.getD (List.replicate r.1.1.1.2.2 0)).getD r.2 [])
        (encPair eIn encUnary) (encList encNat) :=
      (ComputableInPolyTime.listGetD []).comp
        ((hraw2.comp (ComputableInPolyTime.fst _ _)).prod
          (ComputableInPolyTime.snd _ _))
    exact hany.ite' hthen (by fun_prop)
  exact hvar.prod hfac

private noncomputable def mkOuterAccCert
    (cCnt : NativeCertificate outerCount encScheduleParams encNat)
    (cInit : NativeCertificate outerInit encScheduleParams encOuterAcc)
    (cStep : NativeCertificate greedySlotStepBody encOuterSt encOuterAcc) :
    NativeCertificate
      (fun p : ScheduleParams => (IndexFold.run greedySlotStepBody (outerCount p) (outerInit p)).2)
      encScheduleParams encOuterAcc :=
  NativeCertificate.snd (IndexFold.certificate cCnt cInit cStep)

private noncomputable def mkConstructCert
    (cAcc : NativeCertificate
      (fun p : ScheduleParams => (IndexFold.run greedySlotStepBody (outerCount p) (outerInit p)).2)
      encScheduleParams encOuterAcc)
    (cFinal : NativeCertificate finalizeBalancedSchedules encOuterAcc encOutWords) :
    NativeCertificate
      (fun p : ScheduleParams =>
        constructBalancedSchedules p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
      encScheduleParams (encPair (encList (encList encNat)) (encList (encList encNat))) :=
  (cFinal.comp cAcc).congr fun ⟨⟨n, m, Q⟩, ⟨r, C⟩, edges⟩ => by
    have hp := run_greedySlotStepBody_params ((n, m, Q), (r, C), edges)
      (List.replicate n none, List.replicate m none) (n + m)
    dsimp only [Function.comp_apply, outerCount, outerInit, finalizeBalancedSchedules,
      constructBalancedSchedules, greedySchedulePass]
    rw [hp]

/-- Uniform native machine certificate for `greedySchedulePass`. -/
noncomputable def greedySchedulePassCertificate :
    NativeCertificate
      (fun p : ScheduleParams => greedySchedulePass p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
      encScheduleParams encPartialSchedules :=
  NativeCertificate.snd (mkOuterAccCert
    (NativeCertificate.ofPolyTime computableInPolyTime_outerCount)
    (NativeCertificate.ofPolyTime computableInPolyTime_outerInit)
    greedySlotStepBodyCertificate)

/-- Uniform native machine certificate for `constructBalancedSchedules` ([OpenAI2026ETH],
Lemma 4.5, p. 31). -/
noncomputable def constructBalancedSchedulesCertificate :
    NativeCertificate
      (fun p : ScheduleParams =>
        constructBalancedSchedules p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
      encScheduleParams (encPair (encList (encList encNat)) (encList (encList encNat))) :=
  mkConstructCert
    (mkOuterAccCert
      (NativeCertificate.ofPolyTime computableInPolyTime_outerCount)
      (NativeCertificate.ofPolyTime computableInPolyTime_outerInit)
      greedySlotStepBodyCertificate)
    (NativeCertificate.ofPolyTime computableInPolyTime_finalizeBalancedSchedules)

private theorem ofPolyTime_exists_bound {α β : Type} {f : α → β} {ea : α ↪ List Bool}
    {eb : β ↪ List Bool} (hf : ComputableInPolyTime f ea eb) :
    ∃ (c d : ℕ), ∀ (x : α), (NativeCertificate.ofPolyTime hf).time x +
      (NativeCertificate.ofPolyTime hf).space x ≤ c * ((ea x).length + 1) ^ d :=
  ((NativeCertificate.ofPolyTime_isPolynomial hf).1.add
    (NativeCertificate.ofPolyTime_isPolynomial hf).2).exists_le

private theorem pendingSlotOfState_snd_le {st : OuterSt} {slot : Bool × ℕ}
    (h : pendingSlotOfState st = some slot) : slot.2 ≤ st.2.1.1.1 + st.2.1.1.2.1 := by
  unfold pendingSlotOfState slotOfIndex at h
  by_cases h1 : st.1 < st.2.1.1.1
  · simp only [h1, ↓reduceIte, Option.elim_some] at h; split_ifs at h
    injection h with h'; subst h'; exact min_le_left _ _
  · by_cases h2 : st.1 < st.2.1.1.1 + st.2.1.1.2.1
    · simp only [h1, h2, ↓reduceIte, Option.elim_some] at h; split_ifs at h
      injection h with h'; subst h'; exact (Nat.sub_le _ _).trans (min_le_left _ _)
    · simp only [h1, h2, ↓reduceIte, Option.elim_none] at h; cases h

private theorem mkGreedyStepCert_bounds
    (cPend : NativeCertificate pendingSlotOfState encOuterSt encSlotOpt)
    (cIn : NativeCertificate streamSlotInOfOuter encOuterSlot encStreamSlotIn)
    (cSlot : NativeCertificate (fun a : StreamSlotIn =>
        streamBestSlotLabel a.1.1.1 a.1.1.2 a.1.2.1.1 a.1.2.1.2 a.1.2.2 a.2.2 a.2.1)
      encStreamSlotIn (encList encNat))
    (cFin : NativeCertificate finishGreedySlotStep encFinIn encOuterAcc)
    {cP dP cS dS cF dF : ℕ} {pSlot : ℕ → ℕ}
    (hPend : ∀ st, cPend.time st + cPend.space st ≤ cP * ((encOuterSt st).length + 1) ^ dP)
    (hIn : ∀ q, cIn.time q + cIn.space q ≤ cS * ((encOuterSlot q).length + 1) ^ dS)
    (hpSlot : Cslib.PolynomiallyBounded pSlot) (hmSlot : Monotone pSlot)
    (hSlot : ∀ a : StreamSlotIn,
      cSlot.time a ≤ (a.1.2.1.1 ^ a.1.1.2 + 1) * pSlot (encStreamSlotIn a).length ∧
        cSlot.space a ≤ pSlot (encStreamSlotIn a).length)
    (hFin : ∀ qc, cFin.time qc + cFin.space qc ≤ cF * ((encFinIn qc).length + 1) ^ dF) :
    ∃ pStep : ℕ → ℕ, Cslib.PolynomiallyBounded pStep ∧
      ∀ p : ScheduleParams, ∀ s ≤ outerCount p,
        let st := IndexFold.run greedySlotStepBody s (outerInit p)
        (mkGreedyStepCert cPend cIn cSlot cFin).time st ≤
          (p.2.1.1 ^ p.1.2.2 + 1) * pStep (encScheduleParams p).length ∧
        (mkGreedyStepCert cPend cIn cSlot cFin).space st ≤
          pStep (encScheduleParams p).length := by
  let pPend (n : ℕ) := cP * (n + 1) ^ dP; let pIn (n : ℕ) := cS * (n + 1) ^ dS
  let pFin (n : ℕ) := cF * (n + 1) ^ dF
  let bOuter (L : ℕ) := 8 * L ^ 3 + 4 * L ^ 2 + 10 * L + 3
  let bPair (L : ℕ) := 2 * bOuter L + L + 4; let bSlotIn (L : ℕ) := bOuter L + 28 * L + 20
  let bFinIn (L : ℕ) := 2 * bPair L + 4 * L ^ 2 + 2 * L + 2
  let pOver (L : ℕ) := 2 * pPend (bOuter L) + 2 * bOuter L + bPair L + pIn (bPair L) +
    pFin (bFinIn L)
  let pStep (L : ℕ) := pOver L + pSlot (bSlotIn L)
  have hpStep : Cslib.PolynomiallyBounded pStep := by
    dsimp only [pStep, pOver, bFinIn, bSlotIn, bPair, bOuter, pPend, pIn, pFin]; fun_prop
  refine ⟨pStep, hpStep, fun p s hs => ?_⟩
  dsimp only; set L := (encScheduleParams p).length; set rq := p.2.1.1 ^ p.1.2.2
  set runAt := IndexFold.run greedySlotStepBody s (outerInit p)
  have hparts := scheduleParams_parts_le p
  have hstL : (encOuterSt runAt).length ≤ bOuter L := length_encOuterState_run_le p hs
  have hpend : cPend.time runAt + cPend.space runAt ≤ pPend (bOuter L) :=
    (hPend runAt).trans
      (Nat.mul_le_mul_left cP (Nat.pow_le_pow_left (Nat.add_le_add_right hstL 1) dP))
  simp only [mkGreedyStepCert, NativeCertificate.option_time, NativeCertificate.option_space,
    NativeCertificate.linear_time, NativeCertificate.linear_space]
  cases hps : pendingSlotOfState runAt with
  | none =>
    simp only [Option.elim_none]
    have hnT : 2 * cPend.time runAt + (encOuterSt runAt).length + (encOuterSt runAt).length ≤
        pStep L := by dsimp only [pStep, pOver]; omega
    exact ⟨hnT.trans (Nat.le_mul_of_pos_left _ (by omega : 1 ≤ rq + 1)),
      by dsimp only [pStep, pOver]; omega⟩
  | some slot =>
    simp only [Option.elim_some]
    have hp_eq : runAt.2.1 = p :=
      run_greedySlotStepBody_params p (List.replicate p.1.1 none, List.replicate p.1.2.1 none) s
    have hsl_le : slot.2 ≤ L := by
      have := pendingSlotOfState_snd_le hps; rw [hp_eq] at this; exact this.trans hparts.1
    have hslotL : (encPair encBool encUnary slot).length = slot.2 + 3 := by
      simp only [length_encPair, encBool_apply, List.length_singleton, encUnary_apply,
        List.length_replicate]; omega
    let q := (runAt, slot)
    have hqL : (encOuterSlot q).length ≤ bPair L := by
      unfold encOuterSlot; rw [length_encPair, hslotL]; dsimp only [q, bPair]; omega
    have hIn_q : cIn.time q + cIn.space q ≤ pIn (bPair L) :=
      (hIn q).trans (Nat.mul_le_mul_left cS (Nat.pow_le_pow_left (Nat.add_le_add_right hqL 1) dS))
    let a := streamSlotInOfOuter q
    have hSlotInL : (encStreamSlotIn a).length ≤ bSlotIn L := by
      obtain ⟨h1, h2, hw1, hw2⟩ :=
        run_greedySlotStepBody_wf p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2 s
      have hsch : (encPartialSchedules runAt.2.2).length ≤ bOuter L := by
        have hsch0 := length_encPartialSchedules_le h1 h2 hw1 hw2
        have hp3 : 2 * (p.1.1 + p.1.2.1) * (2 * p.1.2.2 * (2 * (encNat p.2.1.1).length + 1) + 3) ≤
            2 * L * (2 * L * (2 * L + 1) + 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hparts.1)
            (Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hparts.2.1)
              (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hparts.2.2.1) 1)) 3)
        dsimp only [runAt, outerInit, bOuter]
        linarith [hsch0, hp3,
          show 2 * L * (2 * L * (2 * L + 1) + 3) = 8 * L ^ 3 + 4 * L ^ 2 + 6 * L by ring]
      simp only [a, streamSlotInOfOuter, q, hp_eq, encStreamSlotIn, encScoreParams, length_encPair,
        encUnary_apply, List.length_replicate, encBool_apply, List.length_singleton]
      dsimp only [bSlotIn]; omega
    have hSlot_a := hSlot a
    have hrq_eq : a.1.2.1.1 ^ a.1.1.2 = rq := by simp only [a, streamSlotInOfOuter, q, hp_eq, rq]
    have hSlotT : cSlot.time a ≤ (rq + 1) * pSlot (bSlotIn L) := by
      rw [← hrq_eq]; exact hSlot_a.1.trans (Nat.mul_le_mul_left _ (hmSlot hSlotInL))
    have hSlotS : cSlot.space a ≤ pSlot (bSlotIn L) := hSlot_a.2.trans (hmSlot hSlotInL)
    let chosen := streamBestSlotLabel a.1.1.1 a.1.1.2 a.1.2.1.1 a.1.2.1.2 a.1.2.2 a.2.2 a.2.1
    have hchL : (encList encNat chosen).length ≤ 4 * L ^ 2 + 2 * L + 1 := by
      have hw := length_encList_word_le (Q := a.1.1.2) (r := a.1.2.1.1) (w := chosen)
        (length_streamBestSlotLabel a.1.1.1 a.1.1.2 a.1.2.1.1 a.1.2.1.2 a.1.2.2 a.2.2 a.2.1)
        (fun _ hx => mem_streamBestSlotLabel_lt_max a.1.1.1 a.1.1.2 a.1.2.1.1 a.1.2.1.2 a.1.2.2
          a.2.2 a.2.1 hx)
      have hq1 : a.1.1.2 = p.1.2.2 := by simp only [a, streamSlotInOfOuter, q, hp_eq]
      have hq2 : a.1.2.1.1 = p.2.1.1 := by simp only [a, streamSlotInOfOuter, q, hp_eq]
      have hp2 : 2 * p.1.2.2 * (2 * (encNat p.2.1.1).length + 1) ≤ 2 * L * (2 * L + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hparts.2.1)
          (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hparts.2.2.1) 1)
      rw [hq1, hq2] at hw
      linarith [hw, hp2, show 2 * L * (2 * L + 1) = 4 * L ^ 2 + 2 * L by ring]
    have hFinL : (encFinIn (q, chosen)).length ≤ bFinIn L := by
      unfold encFinIn; rw [length_encPair]; dsimp only [bFinIn]; omega
    have hFin_qc : cFin.time (q, chosen) + cFin.space (q, chosen) ≤ pFin (bFinIn L) :=
      (hFin (q, chosen)).trans
        (Nat.mul_le_mul_left cF (Nat.pow_le_pow_left (Nat.add_le_add_right hFinL 1) dF))
    refine ⟨?_, ?_⟩
    · simp only [NativeCertificate.congr_time, NativeCertificate.comp_time,
        NativeCertificate.prod_time, NativeCertificate.linear_time, id_eq]
      change 2 * cPend.time runAt + (encOuterSt runAt).length +
        (((encOuterSlot q).length + (cIn.time q + cSlot.time a)) + cFin.time (q, chosen)) ≤
        (rq + 1) * pStep L
      have hover : 2 * cPend.time runAt + (encOuterSt runAt).length +
          (encOuterSlot q).length + cIn.time q + cFin.time (q, chosen) ≤ pOver L := by
        dsimp only [pOver]; omega
      calc 2 * cPend.time runAt + (encOuterSt runAt).length +
            (((encOuterSlot q).length + (cIn.time q + cSlot.time a)) + cFin.time (q, chosen))
          ≤ pOver L + (rq + 1) * pSlot (bSlotIn L) := by omega
        _ ≤ (rq + 1) * pOver L + (rq + 1) * pSlot (bSlotIn L) :=
              Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos rq)) _
        _ = (rq + 1) * pStep L := by dsimp only [pStep]; ring
    · simp only [NativeCertificate.congr_space, NativeCertificate.comp_space,
        NativeCertificate.prod_space, NativeCertificate.linear_space, id_eq]
      change 2 * cPend.space runAt + (encOuterSt runAt).length +
        (((encOuterSlot q).length + (cIn.space q + cSlot.space a)) + cFin.space (q, chosen)) ≤
        pStep L
      dsimp only [pStep, pOver]; omega

private theorem mkOuterAccCert_bounds
    (cCnt : NativeCertificate outerCount encScheduleParams encNat)
    (cInit : NativeCertificate outerInit encScheduleParams encOuterAcc)
    (cStep : NativeCertificate greedySlotStepBody encOuterSt encOuterAcc)
    {cC dC cI dI : ℕ} {pStep : ℕ → ℕ}
    (hCnt : ∀ p, cCnt.time p + cCnt.space p ≤ cC * ((encScheduleParams p).length + 1) ^ dC)
    (hInit : ∀ p, cInit.time p + cInit.space p ≤ cI * ((encScheduleParams p).length + 1) ^ dI)
    (hpStep : Cslib.PolynomiallyBounded pStep)
    (hStep : ∀ p : ScheduleParams, ∀ s ≤ outerCount p,
      let st := IndexFold.run greedySlotStepBody s (outerInit p)
      cStep.time st ≤ (p.2.1.1 ^ p.1.2.2 + 1) * pStep (encScheduleParams p).length ∧
        cStep.space st ≤ pStep (encScheduleParams p).length) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      ∀ p : ScheduleParams,
        (mkOuterAccCert cCnt cInit cStep).time p ≤
          (p.2.1.1 ^ p.1.2.2 + 1) * poly (encScheduleParams p).length ∧
        (mkOuterAccCert cCnt cInit cStep).space p ≤ poly (encScheduleParams p).length := by
  let pCnt (n : ℕ) := cC * (n + 1) ^ dC; let pInit (n : ℕ) := cI * (n + 1) ^ dI
  let bOuter (L : ℕ) := 8 * L ^ 3 + 4 * L ^ 2 + 10 * L + 3
  let rawPoly (L : ℕ) := pCnt L + L + pInit L + (L + 1) * (2 * bOuter L + 2 * (L + 1) ^ 2 + pStep L)
  have hraw : Cslib.PolynomiallyBounded rawPoly := by
    dsimp only [rawPoly, bOuter, pCnt, pInit]; fun_prop
  obtain ⟨cP, dP, hleP⟩ := (PolyBounded.of_polynomiallyBounded id hraw).exists_le
  let poly (n : ℕ) := cP * (n + 1) ^ dP
  refine ⟨poly, by dsimp only [poly]; fun_prop,
    fun _ _ hxy => Nat.mul_le_mul_left cP (Nat.pow_le_pow_left (Nat.add_le_add_right hxy 1) dP),
    fun p => ?_⟩
  let L := (encScheduleParams p).length; let K := outerCount p; let rq := p.2.1.1 ^ p.1.2.2
  have hpolyL : rawPoly L ≤ poly L := hleP L
  have hKL : K ≤ L := (scheduleParams_parts_le p).1
  have hlIdx : (encNat K).length ≤ L := (length_encNat_le_self K).trans hKL
  let runAt (s : ℕ) := IndexFold.run greedySlotStepBody s (outerInit p)
  have hbOuter (s : ℕ) (hs : s ≤ K) : (encOuterSt (runAt s)).length ≤ bOuter L :=
    length_encOuterState_run_le p hs
  let rstep := IndexFold.roundCertificate cStep; let initPair := (0, outerInit p)
  let M := NativeCertificate.maxStateLength encOuterSt (IndexFold.step greedySlotStepBody) K
    initPair
  let RT := NativeCertificate.maxRoundTime rstep K initPair
  let RS := NativeCertificate.maxRoundSpace rstep K initPair
  have hmaxS : M ≤ bOuter L := NativeCertificate.maxStateLength_le _ _ _ _ hbOuter
  have hcnt_p : cCnt.time p + cCnt.space p ≤ pCnt L := hCnt p
  have hinit_p : cInit.time p + cInit.space p ≤ pInit L := hInit p
  have hsqK : ((encNat K).length + 1) ^ 2 ≤ (L + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  refine ⟨?_, ?_⟩
  · have hmaxRT : RT ≤ bOuter L + (L + 1) ^ 2 + (rq + 1) * pStep L := by
      refine NativeCertificate.maxRoundTime_le _ _ _ fun s hs => ?_
      have hs_len : (encNat (runAt s).1).length ≤ L := by
        rw [IndexFold.run_index]; exact (length_encNat_mono hs).trans hlIdx
      have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hs_len 1) 2
      have hstL := hbOuter s hs
      have hcbT : cStep.time (runAt s) ≤ (rq + 1) * pStep L := (hStep p s hs).1
      change (encOuterSt (runAt s)).length + ((encNat (runAt s).1).length + 1) ^ 2 +
        cStep.time (runAt s) ≤ _
      omega
    have hround : RT + M + ((encNat K).length + 1) ^ 2 ≤
        (rq + 1) * (2 * bOuter L + 2 * (L + 1) ^ 2 + pStep L) :=
      calc RT + M + ((encNat K).length + 1) ^ 2
          ≤ (2 * bOuter L + 2 * (L + 1) ^ 2) + (rq + 1) * pStep L := by omega
        _ ≤ (rq + 1) * (2 * bOuter L + 2 * (L + 1) ^ 2) + (rq + 1) * pStep L :=
              Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos rq)) _
        _ = (rq + 1) * (2 * bOuter L + 2 * (L + 1) ^ 2 + pStep L) := by ring
    have hmul := Nat.mul_le_mul (Nat.add_le_add_right hKL 1) hround
    calc (mkOuterAccCert cCnt cInit cStep).time p
        = cCnt.time p + (L + cInit.time p) +
            (K + 1) * (RT + M + ((encNat K).length + 1) ^ 2) := rfl
      _ ≤ (pCnt L + L + pInit L) +
            (L + 1) * ((rq + 1) * (2 * bOuter L + 2 * (L + 1) ^ 2 + pStep L)) := by omega
      _ ≤ (rq + 1) * (pCnt L + L + pInit L) +
            (L + 1) * ((rq + 1) * (2 * bOuter L + 2 * (L + 1) ^ 2 + pStep L)) :=
            Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos rq)) _
      _ = (rq + 1) * rawPoly L := by dsimp only [rawPoly]; ring
      _ ≤ (rq + 1) * poly L := Nat.mul_le_mul_left _ hpolyL
  · have hmaxRS : RS ≤ bOuter L + (L + 1) + pStep L := by
      refine NativeCertificate.maxRoundSpace_le _ _ _ fun s hs => ?_
      have hs_len : (encNat (runAt s).1).length ≤ L := by
        rw [IndexFold.run_index]; exact (length_encNat_mono hs).trans hlIdx
      have hstL := hbOuter s hs
      have hcbS : cStep.space (runAt s) ≤ pStep L := (hStep p s hs).2
      change (encOuterSt (runAt s)).length + ((encNat (runAt s).1).length + 1) +
        cStep.space (runAt s) ≤ _
      omega
    have hlin_sq : L + 1 ≤ (L + 1) ^ 2 := by rw [sq]; exact Nat.le_mul_self _
    have h1 := Nat.mul_le_mul_right (2 * bOuter L + 2 * (L + 1) ^ 2 + pStep L)
      (by omega : 1 ≤ L + 1)
    calc (mkOuterAccCert cCnt cInit cStep).space p
        = cCnt.space p + (L + cInit.space p) + RS + M + (encNat K).length := rfl
      _ ≤ rawPoly L := by dsimp only [rawPoly]; omega
      _ ≤ poly L := hpolyL

/-- Trajectory-maximum time and polynomial-workspace bounds for `greedySchedulePassCertificate`:
`O((r ^ Q + 1) * poly(|input|))` native time and polynomial workspace. -/
theorem greedySchedulePassCertificate_bounds :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      ∀ p : ScheduleParams, greedySchedulePassCertificate.time p ≤
          (p.2.1.1 ^ p.1.2.2 + 1) * poly (encScheduleParams p).length ∧
        greedySchedulePassCertificate.space p ≤ poly (encScheduleParams p).length := by
  obtain ⟨cC, dC, hCnt⟩ := ofPolyTime_exists_bound computableInPolyTime_outerCount
  obtain ⟨cI, dI, hInit⟩ := ofPolyTime_exists_bound computableInPolyTime_outerInit
  obtain ⟨cP, dP, hPend⟩ := ofPolyTime_exists_bound computableInPolyTime_pendingSlotOfState
  obtain ⟨cS, dS, hIn⟩ := ofPolyTime_exists_bound computableInPolyTime_streamSlotInOfOuter
  obtain ⟨cF, dF, hFin⟩ := ofPolyTime_exists_bound computableInPolyTime_finishGreedySlotStep
  obtain ⟨pSlot, hpSlot, hmSlot, hSlot⟩ := streamBestSlotCertificate_bounds
  obtain ⟨pStep, hpStep, hStep⟩ :=
    mkGreedyStepCert_bounds _ _ _ _ hPend hIn hpSlot hmSlot hSlot hFin
  exact mkOuterAccCert_bounds _ _ _ hCnt hInit hpStep hStep

/-- `greedySchedulePass` runs in `O((r ^ Q + 1) * poly(|input|))` native time and polynomial
workspace. -/
theorem computableInO_greedySchedulePass :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun p : ScheduleParams => greedySchedulePass p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
        encScheduleParams encPartialSchedules
        (fun p => (p.2.1.1 ^ p.1.2.2 + 1) * poly (encScheduleParams p).length)
        (fun p => poly (encScheduleParams p).length) := by
  obtain ⟨poly, hpoly, _, hB⟩ := greedySchedulePassCertificate_bounds
  exact ⟨poly, hpoly, greedySchedulePassCertificate.computes.mono_le
    (fun p => (hB p).1) (fun p => (hB p).2)⟩

/-- `greedySchedulePass` runs in polynomial workspace (`ComputableInPolySpace`). -/
theorem computableInPolySpace_greedySchedulePass :
    ComputableInPolySpace
      (fun p : ScheduleParams => greedySchedulePass p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
      encScheduleParams encPartialSchedules := by
  obtain ⟨poly, hpoly, c, hc, hl⟩ := computableInO_greedySchedulePass
  exact ⟨_, fun n => c * (poly n + 1), by fun_prop, hc, hl⟩

private theorem mkConstructCert_bounds
    (cAcc : NativeCertificate
      (fun p : ScheduleParams => (IndexFold.run greedySlotStepBody (outerCount p) (outerInit p)).2)
      encScheduleParams encOuterAcc)
    (cFinal : NativeCertificate finalizeBalancedSchedules encOuterAcc encOutWords)
    {pPass : ℕ → ℕ} {cFinalC dFinal : ℕ}
    (hpPass : Cslib.PolynomiallyBounded pPass) (hmPass : Monotone pPass)
    (hPass : ∀ p : ScheduleParams,
      cAcc.time p ≤ (p.2.1.1 ^ p.1.2.2 + 1) * pPass (encScheduleParams p).length ∧
        cAcc.space p ≤ pPass (encScheduleParams p).length)
    (hFinal : ∀ q, cFinal.time q + cFinal.space q ≤
      cFinalC * ((encOuterAcc q).length + 1) ^ dFinal) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      ∀ p : ScheduleParams, (mkConstructCert cAcc cFinal).time p ≤
          (p.2.1.1 ^ p.1.2.2 + 1) * poly (encScheduleParams p).length ∧
        (mkConstructCert cAcc cFinal).space p ≤ poly (encScheduleParams p).length := by
  let bOuter (L : ℕ) := 8 * L ^ 3 + 4 * L ^ 2 + 10 * L + 3
  let pFinal (n : ℕ) := cFinalC * (n + 1) ^ dFinal; let poly (L : ℕ) := pPass L + pFinal (bOuter L)
  have hpoly : Cslib.PolynomiallyBounded poly := by dsimp only [poly, pFinal, bOuter]; fun_prop
  have hmono : Monotone poly := fun x y hxy => by
    have hbo : bOuter x ≤ bOuter y := by
      dsimp only [bOuter]; have := Nat.pow_le_pow_left hxy 2
      have := Nat.pow_le_pow_left hxy 3; omega
    exact Nat.add_le_add (hmPass hxy)
      (Nat.mul_le_mul_left cFinalC (Nat.pow_le_pow_left (Nat.add_le_add_right hbo 1) dFinal))
  refine ⟨poly, hpoly, hmono, fun p => ?_⟩
  let L := (encScheduleParams p).length; let rq := p.2.1.1 ^ p.1.2.2
  let outSt := (IndexFold.run greedySlotStepBody (outerCount p) (outerInit p)).2
  have houtL : (encOuterAcc outSt).length ≤ bOuter L := by
    have hrunL := length_encOuterState_run_le p (le_rfl : outerCount p ≤ p.1.1 + p.1.2.1)
    rw [IndexFold.length_run] at hrunL
    change 2 * (encNat (outerCount p)).length + 1 + (encOuterAcc outSt).length ≤ bOuter L at hrunL
    omega
  have hfin : cFinal.time outSt + cFinal.space outSt ≤ pFinal (bOuter L) :=
    (hFinal outSt).trans
      (Nat.mul_le_mul_left cFinalC (Nat.pow_le_pow_left (Nat.add_le_add_right houtL 1) dFinal))
  have hp : cAcc.time p ≤ (rq + 1) * pPass L ∧ cAcc.space p ≤ pPass L := hPass p
  refine ⟨?_, by change cAcc.space p + cFinal.space outSt ≤ poly L; dsimp only [poly]; omega⟩
  calc (mkConstructCert cAcc cFinal).time p
      = cAcc.time p + cFinal.time outSt := rfl
    _ ≤ (rq + 1) * pPass L + pFinal (bOuter L) := by omega
    _ ≤ (rq + 1) * pPass L + (rq + 1) * pFinal (bOuter L) :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (Nat.succ_pos rq)) _
    _ = (rq + 1) * poly L := by dsimp only [poly]; ring

/-- Trajectory-maximum time and polynomial-workspace bounds for
`constructBalancedSchedulesCertificate` ([OpenAI2026ETH], Lemma 4.5, pp. 30–31). -/
theorem constructBalancedSchedulesCertificate_bounds :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      ∀ p : ScheduleParams, constructBalancedSchedulesCertificate.time p ≤
          (p.2.1.1 ^ p.1.2.2 + 1) * poly (encScheduleParams p).length ∧
        constructBalancedSchedulesCertificate.space p ≤ poly (encScheduleParams p).length := by
  obtain ⟨pPass, hpPass, hmPass, hPass⟩ := greedySchedulePassCertificate_bounds
  obtain ⟨cFinal, dFinal, hFinal⟩ :=
    ofPolyTime_exists_bound computableInPolyTime_finalizeBalancedSchedules
  exact mkConstructCert_bounds _ _ hpPass hmPass hPass hFinal

/-- `constructBalancedSchedules` runs in `O((r ^ Q + 1) * poly(|input|))` native time
and polynomial workspace. For valid incidence endpoints, this gives
`poly(n, m, |E|, D, Q, r, C)` bit operations, where `D = r ^ (2 * Q)`. -/
theorem computableInO_constructBalancedSchedules :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun p : ScheduleParams =>
          constructBalancedSchedules p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
        encScheduleParams (encPair (encList (encList encNat)) (encList (encList encNat)))
        (fun p => (p.2.1.1 ^ p.1.2.2 + 1) * poly (encScheduleParams p).length)
        (fun p => poly (encScheduleParams p).length) := by
  obtain ⟨poly, hpoly, _, hB⟩ := constructBalancedSchedulesCertificate_bounds
  exact ⟨poly, hpoly, constructBalancedSchedulesCertificate.computes.mono_le
    (fun p => (hB p).1) (fun p => (hB p).2)⟩

/-- `constructBalancedSchedules` runs in polynomial workspace (`ComputableInPolySpace`) without
materializing `r ^ Q` candidate words. -/
theorem computableInPolySpace_constructBalancedSchedules :
    ComputableInPolySpace
      (fun p : ScheduleParams =>
        constructBalancedSchedules p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
      encScheduleParams (encPair (encList (encList encNat)) (encList (encList encNat))) := by
  obtain ⟨poly, hpoly, c, hc, hl⟩ := computableInO_constructBalancedSchedules
  exact ⟨_, fun n => c * (poly n + 1), by fun_prop, hc, hl⟩

end Cslib.BalancedSchedules

end

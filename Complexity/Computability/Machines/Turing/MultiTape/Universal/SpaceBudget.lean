/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.InPlace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# The universal machine within a space budget

`Turing.MultiTapeTM.Universal.budgetedUniversal (d, x, t, b)` runs the machine described by `d` on
`x` for `t` steps, as the universal function does, but within the *budget* `b`: a step whose
configuration of the simulation is encoded by more than `b` bits is not taken, and the simulation
stays at the last configuration within the budget (`Turing.MultiTapeTM.Universal.budgetStep`). It
returns the first two symbols of the output and whether the machine has halted: enough to tell
whether the output is a single given symbol, without storing an output that may be as long as the
run.

It is computed by the in-place run of the universal machine
(`Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_universal_inPlace`): the same
multi-pass fold over the input, one pass per step, reading the symbol under the simulated input
head by counting down the symbols of `x`, with the budget and the first two symbols of the output
added to its state, and a budget test at the end of each pass. So it is tidily computable within
space linear in `Turing.MultiTapeTM.Universal.budgetSpace`: the description, the budget, the
number of steps and the length of `x` in binary, and the largest symbol of `x`
(`Turing.MultiTapeTM.Universal.computableTidilyInO_budgetedUniversal`), never the length of `x`
itself or the space the described machine would use beyond the budget.

Within the budget it agrees with the universal function
(`Turing.MultiTapeTM.Universal.budgetedUniversal_eq_of_le`), and on the description of a machine
it returns the first two symbols of the output of the machine whenever the bound
`Turing.MultiTapeTM.Universal.cfgSpace` on the configurations of the simulation, linear in the
cells the machine visits, is within the budget
(`Turing.MultiTapeTM.Universal.budgetedUniversal_desc`).

## Main definitions

* `Turing.MultiTapeTM.Universal.budgetStep`: a step of the simulation within a budget.
* `Turing.MultiTapeTM.Universal.budgetedUniversal`: the universal function within a space budget.
* `Turing.MultiTapeTM.Universal.budgetSpace`: the bound on the states of its fold.

## Main results

* `Turing.MultiTapeTM.Universal.budgetStep_iterate`: the run within the budget is the run of the
  simulation up to some step.
* `Turing.MultiTapeTM.Universal.budgetedUniversal_eq_of_le`,
  `Turing.MultiTapeTM.Universal.budgetedUniversal_desc`: within the budget, the universal function.
* `Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_budgetedUniversal`,
  `Turing.MultiTapeTM.Universal.computableTidilyInO_budgetedUniversal`: it is tidily computable in
  space linear in `budgetSpace`.
* `Turing.MultiTapeTM.Universal.budgetSpace_le`: `budgetSpace` is linear in the description, the
  budget and the lengths of the number of steps and of the length of the input in binary, plus
  the largest symbol of the input.

## Implementation notes

The fold reuses the parts of the in-place fold (`Turing.MultiTapeTM.Universal.foldNext`,
`Turing.MultiTapeTM.Universal.stepAt`, `Turing.MultiTapeTM.Universal.foldEnd`) on the state of the
in-place fold, and its proof of computability adapts that of
`Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_universal_inPlace`, by Christian
Reitwiessner. The events of the input, the extraction of the parts the initial state reads, the
bounds on the countdown and the simplified time bound restate private lemmas and the extracting
transducer of the module
`Complexity.Computability.Machines.Turing.MultiTape.Universal.InPlace` for the
encoding `Turing.MultiTapeTM.Universal.eInS`, whose input ends in a budget.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 9.3][Sipser2013]: the
  simulation within a space budget in the proof of the space hierarchy theorem.
-/

namespace Turing.MultiTapeTM.Universal

/-! ### Simulating within a budget -/

/-- A step of the simulation within the budget `b`, keeping the first two symbols of the output:
the step of the machine described by `d` on `x`, unless the configuration it reaches is encoded by
more than `b` bits, in which case the configuration and the output stay. -/
@[expose] public def budgetStep (d : Desc) (x : List ℕ) (b : ℕ) (p : SCfg × List ℕ) :
    SCfg × List ℕ :=
  if (eCfg (step d x p.1).1).length ≤ b then
    ((step d x p.1).1, (p.2 ++ (step d x p.1).2.toList).take 2)
  else p

/-- **The universal function within a space budget.** The machine described by `i.1` runs on the
input `i.2.1` for `i.2.2.1` steps within the budget `i.2.2.2` (`budgetStep`); the result is the
first two symbols of its output and whether it has halted. -/
@[expose] public def budgetedUniversal (i : Desc × List ℕ × ℕ × ℕ) : List ℕ × Bool :=
  (((budgetStep i.1 i.2.1 i.2.2.2)^[i.2.2.1] (init i.1, [])).2,
    ((budgetStep i.1 i.2.1 i.2.2.2)^[i.2.2.1] (init i.1, [])).1.state.isNone)

/-- The encoding of inputs of `budgetedUniversal`: the number of steps in binary, the budget in
unary. -/
public abbrev eInS : Desc × List ℕ × ℕ × ℕ ↪ List Bool :=
  encPair eDesc (encPair (encList encUnary) (encPair encNat encUnary))

variable (d : Desc) (x : List ℕ) (b : ℕ)

lemma take_two_append_take_two (o e : List ℕ) : (o.take 2 ++ e).take 2 = (o ++ e).take 2 := by
  simp only [List.take_append, List.take_take, List.length_take]
  congr 2
  omega

lemma stepOut_iterate_succ (j : ℕ) :
    (stepOut d x)^[j + 1] (init d, []) =
      (run d x (j + 1), ((stepOut d x)^[j] (init d, [])).2 ++
        (step d x (run d x j)).2.toList) := by
  rw [Function.iterate_succ_apply', run_succ']
  rfl

/-- **The run within the budget** is the run of the simulation up to some step, with the first two
symbols of its output; past the start, that configuration is within the budget. -/
public theorem budgetStep_iterate (i : ℕ) : ∃ j ≤ i,
    (budgetStep d x b)^[i] (init d, []) = (run d x j, ((stepOut d x)^[j] (init d, [])).2.take 2) ∧
      (j = 0 ∨ (eCfg (run d x j)).length ≤ b) := by
  induction i with
  | zero => exact ⟨0, le_rfl, rfl, Or.inl rfl⟩
  | succ i ih =>
    obtain ⟨j, hj, heq, hb⟩ := ih
    rw [Function.iterate_succ_apply', heq, budgetStep]
    dsimp only
    split_ifs with h
    · refine ⟨j + 1, by omega, ?_, Or.inr (by rwa [run_succ'])⟩
      rw [stepOut_iterate_succ, take_two_append_take_two, run_succ']
    · exact ⟨j, by omega, rfl, hb⟩

/-- The run within the budget keeps at most two symbols of the output. -/
private lemma length_budgetStep_iterate_le (i : ℕ) :
    ((budgetStep d x b)^[i] (init d, [])).2.length ≤ 2 := by
  obtain ⟨j, -, heq, -⟩ := budgetStep_iterate d x b i
  rw [heq, List.length_take]
  exact min_le_left _ _

/-- The symbols of the output kept by the run within the budget are numbers of the description. -/
private lemma le_of_mem_budgetStep_iterate (i : ℕ) {o : ℕ}
    (ho : o ∈ ((budgetStep d x b)^[i] (init d, [])).2) : o ≤ descLen d := by
  obtain ⟨j, -, heq, -⟩ := budgetStep_iterate d x b i
  rw [heq] at ho
  exact (inv_iterate d x j).2.2 o (List.mem_of_mem_take ho)

/-- **Within the budget**, the run is the run of the simulation, with the first two symbols of its
output. -/
private theorem budgetStep_iterate_of_le {t : ℕ}
    (hb : ∀ j < t, (eCfg (run d x (j + 1))).length ≤ b) :
    (budgetStep d x b)^[t] (init d, []) = (run d x t, (simulate d x t).1.take 2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih fun j hj => hb j (by omega), budgetStep]
    dsimp only
    split_ifs with h
    · simp only [simulate]
      rw [stepOut_iterate_succ, ← run_succ', take_two_append_take_two]
    · exact absurd (by rw [← run_succ']; exact hb t (by omega)) h

/-- **Within the budget, the universal function**: if every configuration of the simulation within
`t` steps is encoded within `b` bits, `budgetedUniversal` returns the first two symbols of the
output of the universal function and whether the machine has halted. -/
public theorem budgetedUniversal_eq_of_le {t : ℕ}
    (hb : ∀ j < t, (eCfg (run d x (j + 1))).length ≤ b) :
    budgetedUniversal (d, x, t, b) = ((universal (d, x, t)).1.take 2, (universal (d, x, t)).2) := by
  simp only [budgetedUniversal, budgetStep_iterate_of_le d x b hb, universal]
  rfl

/-- **On the description of a machine**, within a budget that holds the configurations of the
simulation (`Turing.MultiTapeTM.Universal.cfgSpace`, linear in the space of the machine), the
budgeted universal function returns the first two symbols of the numbered output of the machine
and whether it has halted. -/
public theorem budgetedUniversal_desc {k : ℕ} {Symbol S : Type} [Fintype S] [Fintype Symbol]
    (eS : S ↪ ℕ) (eY : Symbol ↪ ℕ) (tm : MultiTapeTM k Symbol S) (x : List Symbol) (t b : ℕ)
    (hb : cfgSpace (desc eS eY tm) (x.map eY) t ≤ b) :
    budgetedUniversal (desc eS eY tm, x.map eY, t, b) =
      (((tm.runFrom (tm.initCfg x) t).output.map eY).take 2,
        (tm.runFrom (tm.initCfg x) t).state.isNone) := by
  rw [budgetedUniversal_eq_of_le _ _ _ fun j hj => ?_, universal_desc]
  refine (length_eCfg_le_space _ _ (j + 1)).trans (le_trans ?_ hb)
  have := simSpace_mono (desc eS eY tm) (x.map eY) (show j + 1 ≤ t by omega)
  unfold cfgSpace
  gcongr

/-! ### The fold within a budget -/

/-- The states of the fold within a budget: the state of the in-place fold
(`Turing.MultiTapeTM.Universal.St`), the budget and the first two symbols of the output so far. -/
public abbrev SSt := St × ℕ × List ℕ

/-- The encoding of the states of the fold within a budget, with the budget in unary. -/
private abbrev eSSt : SSt ↪ List Bool := encPair eSt (encPair encUnary (encList encUnary))

/-- The initial state: the initial state of the in-place fold, the budget and no output. -/
private def foldInitS (i : Desc × List ℕ × ℕ × ℕ) : SSt :=
  (foldInit (i.1, i.2.1, i.2.2.1), i.2.2.2, [])

/-- A round: one event of the countdown, as in the in-place fold. -/
private def foldNextS (p : SSt × Bool) : SSt := (foldNext (p.1.1, p.2), p.1.2)

/-- The end of a pass within the budget: the step of the in-place fold if the configuration it
reaches is encoded within the budget, keeping the first two symbols of the output; otherwise the
configuration stays, one step less is left and the countdown is reset to the input head. -/
private def foldEndS (s : SSt) : SSt :=
  if (eCfg (stepAt s.1).1).length ≤ s.2.1 then
    (foldEnd s.1, s.2.1, (s.2.2 ++ (stepAt s.1).2.toList).take 2)
  else (((s.1.1.1, s.1.1.2), (s.1.2.1 - 1, s.1.1.2.inputPos, 0)), s.2)

/-- Whether another pass follows. -/
private def foldContS (s : SSt) : Bool := foldCont s.1

/-- The result: the first two symbols of the output, and whether the machine has halted. -/
private def foldFinishS (s : SSt) : List ℕ × Bool := (s.2.2, s.1.1.2.state.isNone)

lemma streamState_foldNextS (s : SSt) (l : List Bool) (j : ℕ) :
    streamState s foldNextS l j = ((s.1.1, (s.1.2.1, (l.take j).foldl scan s.1.2.2)), s.2) :=
  List.foldl_hom (fun a => ((s.1.1, (s.1.2.1, a)), s.2)) (fun _ _ => rfl)

-- restated from the module `Universal.InPlace`, where it is private
lemma stepAt_scan' (c : SCfg) (r : ℕ) :
    stepAt ((d, c), (r, (events x).foldl scan (c.inputPos, 0))) =
      if r = 0 then (c, none) else step d x c := by
  rw [stepAt, step_eq_stepWith, inputSymbol_scan]
  rfl

/-- **The passes within the budget** follow the run within the budget, as long as steps are
left. -/
private theorem passState_foldS (t i : ℕ) :
    passState (foldInitS (d, x, t, b)) foldNextS foldEndS (events x) i =
      (((d, ((budgetStep d x b)^[min i t] (init d, [])).1),
        (t - i, ((budgetStep d x b)^[min i t] (init d, [])).1.inputPos, 0)), b,
        ((budgetStep d x b)^[min i t] (init d, [])).2) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [passState, ih, streamState_foldNextS, List.take_length]
    dsimp only
    have hP := length_budgetStep_iterate_le d x b (min i t)
    rcases Nat.lt_or_ge i t with h | h
    · rw [show min (i + 1) t = min i t + 1 by omega, Function.iterate_succ_apply']
      generalize (budgetStep d x b)^[min i t] (init d, []) = P at hP ⊢
      rw [foldEndS, stepAt_scan', budgetStep]
      simp only [show t - i ≠ 0 by omega, ↓reduceIte, foldEnd, stepAt_scan']
      split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega
    · rw [show min (i + 1) t = min i t by omega]
      generalize (budgetStep d x b)^[min i t] (init d, []) = P at hP ⊢
      rw [foldEndS, stepAt_scan']
      simp only [show t - i = 0 by omega, ↓reduceIte, foldEnd, stepAt_scan', Option.toList_none,
        List.append_nil, List.take_of_length_le hP]
      split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega

/-! ### The events of the input, and the parts of the input the initial state reads

The lemmas of this section restate private lemmas of the module
`Complexity.Computability.Machines.Turing.MultiTape.Universal.InPlace` for the encoding
`Turing.MultiTapeTM.Universal.eInS`, whose input ends in a budget. -/

lemma inTr_run_frame (w v : List Bool) :
    inTr.run .descMarker (frame w ++ v) = inTr.run .marker v := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> exact ih

lemma inTr_run_steps (v : List Bool) : inTr.run .steps v = (.steps, []) := by
  induction v with
  | nil => rfl
  | cons b v ih => exact congrArg (fun p : InState × List Bool => (p.1, p.2)) ih

lemma inTr_run_symbol (n : ℕ) (v : List Bool) :
    inTr.run .marker (doubled (frame (List.replicate n true)) ++ v) =
      ((inTr.run .marker v).1, tok n ++ (inTr.run .marker v).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, frame_cons, doubled_cons, doubled_cons]
    change ((inTr.run .marker (doubled (frame (List.replicate n true)) ++ v)).1,
      true :: (inTr.run .marker (doubled (frame (List.replicate n true)) ++ v)).2) = _
    rw [ih]
    simp [tok, List.replicate_succ]

/-- The events of the encoded input of `budgetedUniversal` are the events of the symbols of `x`. -/
private theorem events_eInS (t : ℕ) : inTr.events (eInS (d, x, t, b)) = events x := by
  have hx : ∀ v, inTr.run .marker (doubled (encList encUnary x) ++ v) =
      ((inTr.run .marker v).1, events x ++ (inTr.run .marker v).2) := by
    intro v
    induction x with
    | nil => simp [events]
    | cons n x ih =>
      rw [encList_cons, doubled_append, List.append_assoc, encUnary_apply, inTr_run_symbol, ih]
      simp [events]
  rw [Translator.events, show eInS (d, x, t, b) = frame (eDesc d) ++ (frame (encList encUnary x) ++
    encPair encNat encUnary (t, b)) from rfl, show inTr.q₀ = .descMarker from rfl, inTr_run_frame,
    frame_eq_doubled, List.append_assoc, hx, List.singleton_append]
  change events x ++ (inTr.run .steps (encPair encNat encUnary (t, b))).2 = events x
  rw [inTr_run_steps, List.append_nil]

/-- Copies the framed description, drops the framed input and copies the rest: a copy of the
private transducer `extractT` of the module
`Complexity.Computability.Machines.Turing.MultiTape.Universal.InPlace`. -/
def extractS : Transducer Bool ExState where
  q₀ := .descMarker
  step
    | .descMarker, true => (.descBit, [true])
    | .descMarker, false => (.marker, [false])
    | .descBit, b => (.descMarker, [b])
    | .marker, true => (.bit, [])
    | .marker, false => (.steps, [])
    | .bit, _ => (.marker, [])
    | .steps, b => (.steps, [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

lemma extractS_run (t : ℕ) :
    extractS.run extractS.q₀ (eInS (d, x, t, b)) =
      encPair eDesc (encPair encNat encUnary) (d, t, b) := by
  have h₁ (w v : List Bool) :
      extractS.run .descMarker (frame w ++ v) = frame w ++ extractS.run .marker v := by
    induction w with
    | nil => rfl
    | cons b w ih => exact congrArg (fun l => true :: b :: l) ih
  have h₂ (w v : List Bool) : extractS.run .marker (frame w ++ v) = extractS.run .steps v := by
    induction w with
    | nil => rfl
    | cons b w ih => exact ih
  have h₃ (w : List Bool) : extractS.run .steps w = w := by
    induction w with
    | nil => rfl
    | cons b w ih => exact congrArg (b :: ·) ih
  simp only [eInS, encPair_apply, show extractS.q₀ = .descMarker from rfl, h₁, h₂, h₃]

/-! ### The size of the states -/

-- restated from the module `Universal.InPlace`, where it is private
lemma foldl_scan_replicate' (k cur j : ℕ) :
    (List.replicate j true).foldl scan (k, cur) = (k, if k = 1 then cur + j else cur) := by
  induction j generalizing cur with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldl_cons]
    simp only [scan, ↓reduceIte, ih]
    split_ifs <;> simp
    omega

-- restated from the module `Universal.InPlace`, where it is private
lemma scan_zero' (l : List Bool) (cur : ℕ) : l.foldl scan (0, cur) = (0, cur) := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [scan, ih]

-- restated from the module `Universal.InPlace`, where it is private
lemma scan_take_tok' (n k cur j : ℕ) :
    (((tok n).take j).foldl scan (k, cur)).1 ≤ k ∧
      (((tok n).take j).foldl scan (k, cur)).2 ≤ cur + n ∧
      ((((tok n).take j).foldl scan (k, cur)).2 = cur ∨ k = 1) := by
  rcases Nat.lt_or_ge n j with h | h
  · rw [List.take_of_length_le (by simp [tok]; omega), scan_tok]
    split_ifs <;> simp_all
  · rw [tok, List.take_append_of_le_length (by simpa using h), List.take_replicate,
      Nat.min_eq_left h, foldl_scan_replicate']
    split_ifs <;> simp_all

-- restated from the module `Universal.InPlace`, where it is private
/-- Along the events of the input, the countdown does not go up and the symbol read stays within
the largest symbol. -/
lemma scan_take' (x : List ℕ) (k cur j : ℕ) :
    (((events x).take j).foldl scan (k, cur)).1 ≤ k ∧
      (((events x).take j).foldl scan (k, cur)).2 ≤ cur + x.foldr max 0 := by
  induction x generalizing k cur j with
  | nil => simp [events]
  | cons n x ih =>
    rw [events, List.map_cons, List.flatten_cons, ← events, List.take_append, List.foldl_append]
    obtain ⟨h₁, h₂, h₃⟩ := scan_take_tok' n k cur j
    set p := ((tok n).take j).foldl scan (k, cur)
    obtain ⟨h₄, h₅⟩ := ih p.1 p.2 (j - (tok n).length)
    simp only [Prod.mk.eta] at h₄ h₅
    refine ⟨h₄.trans h₁, ?_⟩
    rcases h₃ with h₃ | rfl
    · simp only [List.foldr_cons] at h₅ ⊢
      omega
    · rcases Nat.lt_or_ge j (tok n).length with hj | hj
      · rw [Nat.sub_eq_zero_of_le hj.le]
        simp only [List.take_zero, List.foldl_nil, List.foldr_cons]
        omega
      · have hp : p = (0, cur + n) := by
          simp only [p, List.take_of_length_le hj, scan_tok, ↓reduceIte]
        rw [hp, scan_zero']
        simp only [List.foldr_cons]
        omega

/-- A bound on the states of the fold within the budget `b`: the description, a configuration
within the budget or the initial one, the number of steps and the position of the input head in
binary, the largest symbol of the input, the budget in unary and two symbols of the output. -/
@[expose] public def budgetSpace (i : Desc × List ℕ × ℕ × ℕ) : ℕ :=
  2 * (2 * (2 * descLen i.1 + 1 + max i.2.2.2 (eCfg (init i.1)).length) + 1 +
    (2 * (encNat i.2.2.1).length + 1 + (2 * (encNat (i.2.1.length + 1)).length + 1 +
      i.2.1.foldr max 0))) + 1 + (2 * i.2.2.2 + 1 + 2 * (2 * descLen i.1 + 1))

/-- **The size of the states** of the fold within the budget. -/
private lemma length_eSSt_le (t i j : ℕ) :
    (eSSt (streamState (passState (foldInitS (d, x, t, b)) foldNextS foldEndS (events x) i)
      foldNextS (events x) j)).length ≤ budgetSpace (d, x, t, b) := by
  rw [passState_foldS, streamState_foldNextS]
  obtain ⟨j', -, heq, hb'⟩ := budgetStep_iterate d x b (min i t)
  rw [heq]
  dsimp only
  have hout := List.length_take_le 2 ((stepOut d x)^[j'] (init d, [])).2
  have hval (o : ℕ) (ho : o ∈ ((stepOut d x)^[j'] (init d, [])).2.take 2) : o ≤ descLen d :=
    (inv_iterate d x j').2.2 o (List.mem_of_mem_take ho)
  have hc : (eCfg (run d x j')).length ≤ max b (eCfg (init d)).length := by
    rcases hb' with rfl | hb'
    · exact le_max_right _ _
    · exact hb'.trans (le_max_left _ _)
  have hpos : (run d x j').inputPos ≤ x.length + 1 := (inv_iterate d x j').1.inputPos
  obtain ⟨hk, hcur⟩ := scan_take' x (run d x j').inputPos 0 j
  have hr := ComputableTidilyInO.length_encNat_mono (show t - i ≤ t by omega)
  have hk' := ComputableTidilyInO.length_encNat_mono (hk.trans hpos)
  have ho := length_encList_le encUnary (((stepOut d x)^[j'] (init d, [])).2.take 2)
    (b := descLen d) fun o ho => by rw [encUnary_apply, List.length_replicate]; exact hval o ho
  have ho' := Nat.mul_le_mul_right (2 * descLen d + 1) hout
  simp only [length_encPair, encUnary_apply, List.length_replicate, budgetSpace, descLen] at *
  omega

/-! ### The parts of the fold, within bounds in the length of the state -/

open ComputableTidilyInO

/-- The first two elements of a list, in linear time and space. -/
lemma take_two_deg : ComputableTidilyInDegree (fun l : List ℕ => l.take 2) (encList encUnary)
    (encList encUnary) 1 1 := by
  have hsingle : ComputableTidilyInDegree (fun n : ℕ => [n]) encUnary (encList encUnary) 1 1 :=
    .of_linear (.of_frame fun n => by rw [encList_cons, encList_nil, List.append_nil])
  have hhead := ComputableTidilyInDegree.headD (enc₁ := encUnary) (enc := encList encUnary) 0
  have hempty := ComputableTidilyInDegree.isEmpty (enc₁ := encUnary) (enc := encList encUnary)
  have htail := ComputableTidilyInDegree.tail (enc₁ := encUnary) (enc := encList encUnary)
  have hone : ComputableTidilyInDegree (fun l : List ℕ => if l.isEmpty then [] else [l.headD 0])
      (encList encUnary) (encList encUnary) 1 1 :=
    (hempty.ite ((ComputableTidilyInDegree.const (encMid := encList encUnary) []).restrict _)
      ((hsingle.comp hhead).restrict _)).mono
  have hcons := (ComputableTidilyInDegree.cons encUnary).comp (hhead.prod (hone.comp htail))
  refine ((hempty.ite ((ComputableTidilyInDegree.const (encMid := encList encUnary) []).restrict _)
    (hcons.restrict _)).of_enc_eq fun l => ?_).mono
  rcases l with _ | ⟨a, _ | ⟨c, l⟩⟩ <;> rfl

/-- The first two symbols of a list followed by an optional symbol, in linear time and space. -/
lemma keepTwo_deg : ComputableTidilyInDegree
    (fun p : List ℕ × Option ℕ => (p.1 ++ p.2.toList).take 2)
    (encPair (encList encUnary) eSym) (encList encUnary) 1 1 := by
  have hsingle : ComputableTidilyInDegree (fun n : ℕ => [n]) encUnary (encList encUnary) 1 1 :=
    .of_linear (.of_frame fun n => by rw [encList_cons, encList_nil, List.append_nil])
  have htoList : ComputableTidilyInDegree (fun e : Option ℕ => e.toList) eSym
      (encList encUnary) 1 1 := by
    refine (((ComputableTidilyInDegree.isSome encUnary).ite
      ((hsingle.comp (ComputableTidilyInDegree.getD (enc₁ := encUnary) (enc := eSym) 0)).restrict
        _) ((ComputableTidilyInDegree.const (encMid := encList encUnary) []).restrict _)).of_enc_eq
      fun e => ?_).mono
    cases e <;> rfl
  have happ := (ComputableTidilyInDegree.listAppend encUnary).comp
    ((ComputableTidilyInDegree.fst (encList encUnary) eSym).prod
      (htoList.comp (ComputableTidilyInDegree.snd (encList encUnary) eSym)))
  exact (take_two_deg.comp happ).mono

/-- The initial state, in the space of the description, the number of steps and the budget. -/
private lemma foldInitS_inO : ComputableTidilyInO foldInitS eInS eSSt
    (fun i => (eInS i).length +
      ((encPair eDesc (encPair encNat encUnary) (i.1, i.2.2)).length + 1) ^ 2)
    fun i => (encPair eDesc (encPair encNat encUnary) (i.1, i.2.2)).length + 1 := by
  have hext := ComputableTidilyInO.of_transducer extractS (f := fun i : Desc × List ℕ × ℕ × ℕ =>
    (i.1, i.2.2)) (encIn := eInS) (encOut := encPair eDesc (encPair encNat encUnary))
    fun i => (extractS_run i.1 i.2.1 i.2.2.2 i.2.2.1).symm
  have hd := fst eDesc (encPair encNat encUnary)
  have hr := snd eDesc (encPair encNat encUnary)
  have hg := ((hd.prod (init_inO.comp hd)).prod
    (hr.fst'.prod ((const (encMid := encNat) 1).prod (const (encMid := encUnary) 0)))).prod
    (hr.snd'.prod (const (encMid := encList encUnary) []))
  refine ((hg.comp hext).of_enc_eq (g := foldInitS) fun i => rfl).mono 20 (fun i => ?_)
    fun i => ?_
  all_goals
    have : (eDesc i.1).length ≤ (encPair eDesc (encPair encNat encUnary) (i.1, i.2.2)).length := by
      simp only [length_encPair]; omega
    dsimp only [Function.comp_apply]
    nlinarith

/-- A round of the countdown. -/
private lemma foldNextS_inO : ComputableTidilyInO foldNextS (encPair eSSt encBool) eSSt
    (fun p => ((encPair eSSt encBool p).length + 1) ^ 2)
    fun p => (encPair eSSt encBool p).length + 1 := by
  have h₁ := fst eSSt encBool
  have hn := foldNext_inO.comp (h₁.fst'.prod (snd eSSt encBool))
  refine ((hn.prod h₁.snd').of_enc_eq (g := foldNextS) fun p => rfl).mono 20 (fun p => ?_)
    fun p => ?_
  all_goals
    have : (encPair eSt encBool (p.1.1, p.2)).length ≤ (encPair eSSt encBool p).length := by
      simp only [length_encPair]; omega
    nlinarith

/-- Whether another pass follows. -/
private lemma foldContS_inO : ComputableTidilyInO foldContS eSSt encBool
    (fun s => ((eSSt s).length + 1) ^ 3) fun s => (eSSt s).length + 1 := by
  have h := foldCont_inO.comp (fst eSt (encPair encUnary (encList encUnary)))
  refine (h.of_enc_eq (g := foldContS) fun s => rfl).mono 2 (fun s => ?_) fun s => ?_
  all_goals
    have : (eSt s.1).length ≤ (eSSt s).length := by simp only [length_encPair]; omega
    have : ((eSt s.1).length + 1) ^ 3 ≤ ((eSSt s).length + 1) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have : (eSSt s).length + 1 ≤ ((eSSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    dsimp only [eSSt] at *
    omega

/-- The result: the first two symbols of the output, and whether the machine has halted. -/
private lemma foldFinishS_inO : ComputableTidilyInO foldFinishS eSSt eOut
    (fun s => ((eSSt s).length + 1) ^ 3) fun s => (eSSt s).length + 1 := by
  have h₁ := fst eSt (encPair encUnary (encList encUnary))
  have h₂ := snd eSt (encPair encUnary (encList encUnary))
  have hst := state_inO.comp_linear h₁.fst'.snd'
  have hnone := (ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool)
    fun b : Bool => !b).inO_one.comp_linear
      ((ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear hst)
  refine ((h₂.snd'.prod hnone).of_enc_eq (g := foldFinishS) fun s => ?_).mono 2 (fun s => ?_)
    fun s => ?_
  · simp only [foldFinishS, Function.comp_apply]
    cases s.1.1.2.state <;> rfl
  all_goals
    have : (eSSt s).length + 1 ≤ ((eSSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    dsimp only [eSSt] at *
    omega

lemma length_eSSt (s : SSt) : (eSSt s).length =
    2 * (eSt s.1).length + 1 + (2 * s.2.1 + 1 + (encList encUnary s.2.2).length) := by
  rw [length_encPair (enc₁ := eSt) (enc₂ := encPair encUnary (encList encUnary)),
    length_encPair (enc₁ := encUnary) (enc₂ := encList encUnary), encUnary_apply,
    List.length_replicate]

/-- The budget test: whether the configuration the step reaches is encoded within the budget. -/
lemma budgetTest_inO : ComputableTidilyInO
    (fun s : SSt => decide ((eCfg (stepAt s.1).1).length ≤ s.2.1))
    eSSt encBool (fun s => ((eSSt s).length + 1) ^ 3) fun s => (eSSt s).length + 1 := by
  have h₁ := fst eSt (encPair encUnary (encList encUnary))
  have hbud := (snd eSt (encPair encUnary (encList encUnary))).fst'
  have hword := (stepAt_inO.comp h₁).fst'.of_enc_eq (encOut := encBits)
    (g := fun s : SSt => eCfg (stepAt s.1).1) fun _ => rfl
  obtain ⟨cS, hcS⟩ := stepAt_inO.length_le
  refine ((ComputableInO.unaryLe.tidy.comp ((ComputableInO.lengthUnary.tidy.comp
    hword).prod hbud)).of_enc_eq fun s => rfl).mono (3 * (4 * cS + 5) ^ 2 + 3) (fun s => ?_)
    fun s => ?_
  all_goals
    dsimp only [Function.comp_apply, encBits_apply]
    have e₁ := length_eSSt s
    have e₂ : ((encPair eSt (encPair encUnary (encList encUnary))) s).length =
      (eSSt s).length := rfl
    have e₃ := length_encPair (enc₁ := encUnary) (enc₂ := encUnary)
      ((eCfg (stepAt s.1).1).length, s.2.1)
    have h₄ := hcS s.1
    rw [length_encPair (enc₁ := eCfg) (enc₂ := eSym)] at h₄
    simp only [encUnary_apply, List.length_replicate] at e₃
    rw [e₂, e₃]
    generalize (eSSt s).length = L at *
    generalize (eCfg (stepAt s.1).1).length = w at *
    generalize (eSt s.1).length = A at *
    have h₅ : cS * (A + 1 + 1) ≤ cS * (2 * (L + 1)) := Nat.mul_le_mul_left _ (by omega)
    have hw : 2 * w + 1 + s.2.1 + 1 ≤ (4 * cS + 5) * (L + 1) := by nlinarith
    have hX : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have hA : (A + 1) ^ 3 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hQ : (4 * cS + 5) * (L + 1) ≤ (4 * cS + 5) ^ 2 * (L + 1) ^ 3 :=
      Nat.mul_le_mul (Nat.le_self_pow (by norm_num) _) hX
    have hS : (2 * w + 1 + s.2.1 + 1) ^ 2 ≤ (4 * cS + 5) ^ 2 * (L + 1) ^ 3 :=
      calc (2 * w + 1 + s.2.1 + 1) ^ 2 ≤ ((4 * cS + 5) * (L + 1)) ^ 2 := Nat.pow_le_pow_left hw 2
        _ = (4 * cS + 5) ^ 2 * (L + 1) ^ 2 := mul_pow ..
        _ ≤ (4 * cS + 5) ^ 2 * (L + 1) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hQ1 : L + 1 ≤ (4 * cS + 5) ^ 2 * (L + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
    have hQ2 : (4 * cS + 5) * (L + 1) ≤ (4 * cS + 5) ^ 2 * (L + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
    generalize (4 * cS + 5) ^ 2 = Q at *
    generalize (L + 1) ^ 3 = Y at *
  · have e : (3 * Q + 3) * (Y + 1) = 3 * (Q * Y) + 3 * Q + 3 * Y + 3 := by ring
    omega
  · have e : (3 * Q + 3) * (L + 1 + 1) = 3 * (Q * (L + 1)) + 3 * Q + 3 * (L + 1) + 3 := by ring
    omega

/-- The end of a pass within the budget: the step of the in-place fold, the budget test on the
length of the configuration it reaches, and either branch. -/
private lemma foldEndS_inO : ComputableTidilyInO foldEndS eSSt eSSt
    (fun s => ((eSSt s).length + 1) ^ 3) fun s => (eSSt s).length + 1 := by
  have h₁ := fst eSt (encPair encUnary (encList encUnary))
  have h₂ := snd eSt (encPair encUnary (encList encUnary))
  have e₂ (s : SSt) : ((encPair eSt (encPair encUnary (encList encUnary))) s).length =
      (eSSt s).length := rfl
  -- the step taken
  have hkeep := keepTwo_deg.inO_one.comp_linear (h₂.snd'.prod (stepAt_inO.comp h₁).snd')
  have htaken : ComputableTidilyInO (fun s : SSt =>
      (foldEnd s.1, s.2.1, (s.2.2 ++ (stepAt s.1).2.toList).take 2)) eSSt eSSt
      (fun s => ((eSSt s).length + 1) ^ 3) fun s => (eSSt s).length + 1 := by
    refine ((foldEnd_inO.comp h₁).prod (h₂.fst'.prod hkeep)).mono 8 (fun s => ?_) fun s => ?_
    all_goals
      have e₁ := length_eSSt s
      rw [e₂]
      generalize (eSSt s).length = L at *
      generalize (eSt s.1).length = A at *
      have hX : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      have hA : (A + 1) ^ 3 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      generalize (L + 1) ^ 3 = Y at *
      omega
  -- the configuration stays
  have hpos := (h₁.fst'.snd'.of_enc_eq (encOut := eCfgFields)
    (g := fun s : SSt => (s.1.1.2.state, s.1.1.2.inputPos, s.1.1.2.workTapes))
    fun _ => rfl).snd'.fst'
  have hstay : ComputableTidilyInO (fun s : SSt =>
      (((s.1.1.1, s.1.1.2), (s.1.2.1 - 1, s.1.1.2.inputPos, 0)), s.2)) eSSt eSSt
      (fun s => ((eSSt s).length + 1) ^ 3) fun s => (eSSt s).length + 1 := by
    refine ((h₁.fst'.prod ((ComputableInO.natPred.tidy.comp h₁.snd'.fst').prod
      (hpos.prod (const (encMid := encUnary) 0)))).prod h₂).mono 8 (fun s => ?_) fun s => ?_
    all_goals
      have e₁ := length_eSSt s
      have e₃ := length_encPair (enc₁ := encPair eDesc eCfg)
        (enc₂ := encPair encNat (encPair encNat encUnary)) s.1
      have e₄ := length_encPair (enc₁ := encNat) (enc₂ := encPair encNat encUnary) s.1.2
      rw [e₂]
      have hr : (encNat s.1.2.1).length + 1 ≤ (eSSt s).length + 1 := by
        change (eSt s.1).length = _ at e₃
        omega
      have hsq := Nat.pow_le_pow_left hr 2
      have hX : (eSSt s).length + 1 ≤ ((eSSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      have hX2 : ((eSSt s).length + 1) ^ 2 ≤ ((eSSt s).length + 1) ^ 3 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      generalize (eSSt s).length = L at *
      generalize (L + 1) ^ 3 = Y at *
      omega
  refine ((budgetTest_inO.ite htaken hstay).of_enc_eq (g := foldEndS) fun s => ?_).mono 2
    (fun s => ?_) fun s => ?_
  · simp only [foldEndS, decide_eq_true_eq]
  all_goals
    have : (eSSt s).length + 1 ≤ ((eSSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    split_ifs <;> omega

/-! ### The universal machine within a space budget -/

lemma length_eSSt_le' (t i j : ℕ) :
    (eSSt (streamState (passState (foldInitS (d, x, t, b)) foldNextS foldEndS
      (inTr.events (eInS (d, x, t, b))) i) foldNextS (inTr.events (eInS (d, x, t, b))) j)).length ≤
      budgetSpace (d, x, t, b) := by
  rw [events_eInS]
  exact length_eSSt_le d x b t i j

-- restated from the module `Universal.InPlace`, where it is private
/-- The time of the universal machine within a budget, simplified. -/
lemma final_time' (c N t L P E : ℕ) (hP : P ≤ L) (hE : E ≤ L) :
    c * (N + (P + 1) ^ 2 + (E + 1) ^ 3 + (t - 1 + 1) * (N + (N + 1) * (9 * (L + 1) ^ 3 + L + 1)))
      ≤ 20 * c * ((t + 1) * (N + 1) ^ 2 * (L + 1) ^ 3) := by
  have hA : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h₁ : (P + 1) ^ 2 ≤ (L + 1) ^ 3 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h₂ : (E + 1) ^ 3 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h₃ : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h₄ : t - 1 + 1 ≤ t + 1 := by omega
  rw [Nat.mul_assoc 20, Nat.mul_left_comm 20 c]
  refine Nat.mul_le_mul_left c ?_
  set Y := (L + 1) ^ 3
  set Z := (N + 1) ^ 2 * Y
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hz₁ : (N + 1) * Y ≤ Z := Nat.mul_le_mul_right _ hN
  have hz₂ : N + 1 ≤ (N + 1) * Y := Nat.le_mul_of_pos_right _ hA
  have hz₃ : Y ≤ (N + 1) * Y := Nat.le_mul_of_pos_left _ (by omega)
  have hz₄ : Z ≤ (t + 1) * Z := Nat.le_mul_of_pos_left _ (by omega)
  have h₅ : N + (N + 1) * (9 * Y + L + 1) ≤ 11 * Z := by
    have := Nat.mul_le_mul_left (N + 1) (show 9 * Y + L + 1 ≤ 10 * Y by omega)
    rw [show (N + 1) * (10 * Y) = 10 * ((N + 1) * Y) by ring] at this
    omega
  calc _ ≤ N + Y + Y + (t + 1) * (11 * Z) := by gcongr
    _ = N + Y + Y + 11 * ((t + 1) * Z) := by ring
    _ ≤ 20 * ((t + 1) * Z) := by omega
    _ = 20 * ((t + 1) * (N + 1) ^ 2 * Y) := by ring

local instance : FinEnum InState :=
  FinEnum.ofList [.descMarker, .descBit, .marker, .bit, .digitMarker, .digit, .steps]
    fun q => by cases q <;> decide

/-- **The universal machine within a space budget.** The budgeted universal function is tidily
computable within space linear in the bound `budgetSpace` on the states of its fold, by the
multi-pass fold of the in-place universal machine with the budget test at the end of each pass.
Each of the `t` passes reads the whole input. -/
public theorem computableTidilyInTimeAndSpace_budgetedUniversal : ∃ c,
    ComputableTidilyInTimeAndSpace budgetedUniversal eInS eOut
      (fun i => c * ((i.2.2.1 + 1) * ((eInS i).length + 1) ^ 2 * (budgetSpace i + 1) ^ 3))
      (fun i => c * (budgetSpace i + 1)) := by
  refine Exists.elim (ComputableTidilyInTimeAndSpace.multiPassFold_translate inTr
    (encQ := encFinEnum InState) foldInitS_inO foldNextS_inO
    (const (encIn := eSSt) (encMid := encBits) ([] : List Bool)) foldEndS_inO foldContS_inO
    foldFinishS_inO (passes := fun i => i.2.2.1 - 1) (g := budgetedUniversal) (encOut := eOut) ?_ ?_
    (tMax := fun i => 9 * (budgetSpace i + 1) ^ 3)
    (sMax := fun i => 9 * (budgetSpace i + 1))
    (lMax := fun i => budgetSpace i) ?_ ?_ ?_ ?_ ?_ ?_) fun c h => ?_
  case refine_1 =>
    rintro ⟨d, x, t, b⟩ i hi
    rw [events_eInS, passState_foldS]
    simp only [foldContS, foldCont, decide_eq_decide]
    omega
  case refine_2 =>
    rintro ⟨d, x, t, b⟩
    rw [events_eInS, passState_foldS, show min (t - 1 + 1) t = t by omega]
    simp only [encBits_apply, List.map_const', List.flatten_replicate_nil, List.nil_append,
      foldFinishS, budgetedUniversal]
  case refine_3 =>
    rintro ⟨d, x, t, b⟩ i - j -
    have := length_eSSt_le' d x b t i j
    rw [length_encPair, encBool_apply, List.length_singleton]
    generalize (eSSt _).length = a at this ⊢
    have h₁ := Nat.pow_le_pow_left
      (show 2 * a + 1 + 1 + 1 ≤ 3 * (budgetSpace (d, x, t, b) + 1) by omega) 2
    have h₂ : (budgetSpace (d, x, t, b) + 1) ^ 2 ≤ (budgetSpace (d, x, t, b) + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  case refine_4 =>
    rintro ⟨d, x, t, b⟩ i - j -
    have := length_eSSt_le' d x b t i j
    rw [length_encPair, encBool_apply, List.length_singleton]
    dsimp only
    omega
  case refine_5 =>
    rintro ⟨d, x, t, b⟩ i -
    have h₁ := length_eSSt_le' d x b t i (inTr.events (eInS (d, x, t, b))).length
    have h₂ := length_eSSt_le' d x b t (i + 1) 0
    rw [streamState_zero] at h₂
    have h₃ := Nat.pow_le_pow_left (Nat.add_le_add_right h₁ 1) 3
    have h₄ := Nat.pow_le_pow_left (Nat.add_le_add_right h₂ 1) 3
    have h₅ : budgetSpace (d, x, t, b) + 1 ≤ (budgetSpace (d, x, t, b) + 1) ^ 3 :=
      Nat.le_self_pow (by norm_num) _
    refine (Nat.add_le_add (Nat.add_le_add h₁ h₃) h₄).trans ?_
    omega
  case refine_6 =>
    rintro ⟨d, x, t, b⟩ i -
    have h₁ := length_eSSt_le' d x b t i (inTr.events (eInS (d, x, t, b))).length
    have h₂ := length_eSSt_le' d x b t (i + 1) 0
    rw [streamState_zero] at h₂
    omega
  case refine_7 =>
    rintro ⟨d, x, t, b⟩ i - j -
    exact length_eSSt_le' d x b t i j
  case refine_8 =>
    rintro ⟨d, x, t, b⟩
    have h := length_eSSt_le' d x b t (t - 1 + 1) 0
    rw [streamState_zero] at h
    dsimp only
    exact h
  refine ⟨20 * c, h.mono (fun i => ?_) fun i => ?_⟩ <;> obtain ⟨d, x, t, b⟩ := i <;> dsimp only
  · have hP : (encPair eDesc (encPair encNat encUnary) (d, t, b)).length ≤
        budgetSpace (d, x, t, b) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, budgetSpace, descLen]
      omega
    have hE := length_eSSt_le' d x b t (t - 1 + 1) 0
    rw [streamState_zero] at hE
    exact final_time' c _ t _ _ _ hP hE
  · have hP : (encPair eDesc (encPair encNat encUnary) (d, t, b)).length ≤
        budgetSpace (d, x, t, b) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, budgetSpace, descLen]
      omega
    have := length_eSSt_le' d x b t (t - 1 + 1) 0
    simp only [streamState_zero] at this
    generalize budgetSpace (d, x, t, b) = B at *
    nlinarith

/-- The initial configuration is encoded within `11 * descLen d + 6` bits: the initial state, the
input head at `1` and blank work tapes. -/
private lemma length_eCfg_init_le : (eCfg (init d)).length ≤ 11 * descLen d + 6 := by
  have hq : d.q₀ ≤ descLen d := by
    simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]; omega
  have hk : d.tapes ≤ descLen d := by
    simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]; omega
  have ht := length_encList_le eTape (List.replicate d.tapes ⟨0, [], []⟩) (b := 4) fun t ht => by
    rw [List.eq_of_mem_replicate ht]
    rfl
  rw [List.length_replicate] at ht
  simp only [init, eCfg_apply, length_encPair, eSym, encOption_some, List.length_cons,
    encUnary_apply, List.length_replicate]
  have : (encNat 1).length = 1 := rfl
  omega

/-- **The space of the universal machine within a budget**: `budgetSpace` is linear in the
description, the budget and the lengths of the number of steps and of the length of the input in
binary, plus the largest symbol of the input. -/
public theorem budgetSpace_le (t : ℕ) :
    budgetSpace (d, x, t, b) ≤ 60 * (descLen d + 1) + 6 * b + 4 * (encNat t).length +
      4 * (encNat (x.length + 1)).length + 2 * x.foldr max 0 := by
  have := length_eCfg_init_le d
  simp only [budgetSpace]
  omega

/-- The encoded result of the universal function within a budget is within `budgetSpace`. -/
public lemma length_eOut_budgetedUniversal_le (t : ℕ) :
    (eOut (budgetedUniversal (d, x, t, b))).length ≤ budgetSpace (d, x, t, b) := by
  have hout := length_budgetStep_iterate_le d x b t
  have ho := length_encList_le encUnary ((budgetStep d x b)^[t] (init d, [])).2
    (b := descLen d) fun o ho => by
      rw [encUnary_apply, List.length_replicate]
      exact le_of_mem_budgetStep_iterate d x b t ho
  have := Nat.mul_le_mul_right (2 * descLen d + 1) hout
  simp only [budgetedUniversal, length_encPair, encBool_apply, List.length_singleton, budgetSpace]
  omega

/-- **The universal machine within a space budget**, up to constants: within time
`O((t + 1) * (n + 1) ^ 2 * (budgetSpace + 1) ^ 3)` on an encoded input of length `n` and space
`O(budgetSpace)` (`Turing.MultiTapeTM.Universal.budgetSpace_le`). -/
public theorem computableTidilyInO_budgetedUniversal :
    ComputableTidilyInO budgetedUniversal eInS eOut
      (fun i => (i.2.2.1 + 1) * ((eInS i).length + 1) ^ 2 * (budgetSpace i + 1) ^ 3)
      budgetSpace := by
  obtain ⟨c, h⟩ := computableTidilyInTimeAndSpace_budgetedUniversal
  refine .of_bounds h (c + 1) (fun i => ?_) (fun i => ?_) fun i => ?_
  · exact Nat.mul_le_mul (Nat.le_succ c) (Nat.le_succ _)
  · exact Nat.mul_le_mul (Nat.le_succ c) le_rfl
  · obtain ⟨d, x, t, b⟩ := i
    have := length_eOut_budgetedUniversal_le d x b t
    nlinarith

end Turing.MultiTapeTM.Universal

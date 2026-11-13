/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.Clocked
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite

/-!
# Local paired ports for fair-coin compact and clocked configuration graphs

For a probabilistic multi-tape Turing machine `machine : MultiTapePTM k Bool State`, each compact
configuration ID `u` has at most two outgoing fair-coin branches (`coin = false` and `coin = true`).
When the two branches target distinct vertices they occupy outgoing ports `0` and `1` with
multiplicity `1` each; when they coincide they merge onto outgoing port `0` with multiplicity `2`.

Conversely, for any target configuration ID `v`, every valid predecessor `u` arises either from the
absorbing self-loop on a halted state or by inverting one entry of the finite transition table along
with a binary input-boundary choice and a three-valued pre-step output code. Enumerating this
machine-fixed list of `inPortBound machine` predecessor recipes, querying each candidate's single
input symbol, filtering by positive `coinCountWithSymbol`, and sorting strictly deduplicates the
incoming predecessors and makes outgoing and incoming port lookups exact mutual inverses.

Lifting along `a ↦ (a / N, a % N)` yields explicit natural-number port and count functions
`clockedOutPort`, `clockedInPort`, and `clockedOutCount` on clocked configuration IDs, together
with native linear-workspace `ComputableInSpace` certificates on pre-queried input symbols. The
standalone `QueryMachine` logspace certificates on `(w, a, p)` are proved in the companion module
`FairCoin.PairedPorts.LogSpace`.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.stepTargetWithSymbol`: unique compact target of a
  deterministic machine step.
* `Turing.MultiTapePTM.ConfigurationGraph.coinOutTargetsWithSymbol`: sorted duplicate-free outgoing
  targets (length `≤ 2`) of a fair-coin step.
* `Turing.MultiTapePTM.ConfigurationGraph.PredRecipe`,
  `Turing.MultiTapePTM.ConfigurationGraph.predRecipes`,
  `Turing.MultiTapePTM.ConfigurationGraph.inPortBound`: finite predecessor recipes and constant
  in-degree bound.
* `Turing.MultiTapePTM.ConfigurationGraph.coinInSourcesWithSymbols`,
  `Turing.MultiTapePTM.ConfigurationGraph.coinInSources`: sorted duplicate-free incoming sources.
* `Turing.MultiTapePTM.ConfigurationGraph.clockedOutPort`,
  `Turing.MultiTapePTM.ConfigurationGraph.clockedInPort`,
  `Turing.MultiTapePTM.ConfigurationGraph.clockedOutCount`: clocked natural-number port and
  multiplicity functions.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.stepTargetWithSymbol_eq_some_iff`: exact equivalence with
  `edgeWithSymbol`.
* `Turing.MultiTapePTM.ConfigurationGraph.exists_predRecipe_of_coinCountWithSymbol_pos`:
  completeness of `predRecipes`.
* `Turing.MultiTapePTM.ConfigurationGraph.clockedOutPort_eq_some_iff`: mutual port inversion on
  clocked natural-number IDs.
* `Turing.MultiTapePTM.ConfigurationGraph.clockedOutCountWithSymbol_budget`,
  `Turing.MultiTapePTM.ConfigurationGraph.clockedOutPortWithSymbols_budget`,
  `Turing.MultiTapePTM.ConfigurationGraph.clockedInPortWithSymbols_budget`: native linear-space
  certificates on pre-queried symbols.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 2, Lemma 2.1.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open Cslib.Turing MultiTapeTM ComputableInSpace

section RadixAndListHelpers

variable {k : ℕ}

/-- Combine two optional natural targets into a strictly sorted duplicate-free list of length at
most `2`. -/
private def pairSortedTargets : Option ℕ → Option ℕ → List ℕ
  | none, none => []
  | some v₀, none => [v₀]
  | none, some v₁ => [v₁]
  | some v₀, some v₁ =>
    if v₀ < v₁ then [v₀, v₁]
    else if v₁ < v₀ then [v₁, v₀]
    else [v₀]

private theorem mem_pairSortedTargets (a b : Option ℕ) (v : ℕ) :
    v ∈ pairSortedTargets a b ↔ a = some v ∨ b = some v := by
  rcases a with _ | v₀ <;> rcases b with _ | v₁
  · simp [pairSortedTargets]
  · simp [pairSortedTargets, eq_comm]
  · simp [pairSortedTargets, eq_comm]
  · dsimp only [pairSortedTargets]
    split_ifs with h₁ h₂
    · simp [eq_comm]
    · simp [eq_comm, or_comm]
    · have heq : v₀ = v₁ := by omega
      subst heq
      simp [eq_comm]

private theorem nodup_pairSortedTargets (a b : Option ℕ) : (pairSortedTargets a b).Nodup := by
  rcases a with _ | v₀ <;> rcases b with _ | v₁
  · simp [pairSortedTargets]
  · simp [pairSortedTargets]
  · simp [pairSortedTargets]
  · dsimp only [pairSortedTargets]
    split_ifs with h₁ h₂
    · simp [Nat.ne_of_lt h₁]
    · simp [Nat.ne_of_lt h₂]
    · simp

private theorem length_pairSortedTargets_le (a b : Option ℕ) :
    (pairSortedTargets a b).length ≤ 2 := by
  rcases a with _ | v₀ <;> rcases b with _ | v₁ <;> dsimp only [pairSortedTargets]
  · simp
  · simp
  · simp
  · split_ifs <;> simp

/-- Insert `x` into a strictly increasing `List ℕ`, discarding duplicates. -/
private def insertSortedNat (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: insertSortedNat x ys

private theorem mem_insertSortedNat (x : ℕ) (l : List ℕ) (z : ℕ) :
    z ∈ insertSortedNat x l ↔ z = x ∨ z ∈ l := by
  induction l with
  | nil => simp [insertSortedNat]
  | cons y ys ih =>
    dsimp only [insertSortedNat]
    split_ifs with hlt heq
    · simp
    · subst heq
      simp only [List.mem_cons]
      tauto
    · simp only [List.mem_cons, ih]
      tauto

private theorem length_insertSortedNat_le (x : ℕ) (l : List ℕ) :
    (insertSortedNat x l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [insertSortedNat]
  | cons y ys ih =>
    dsimp only [insertSortedNat]
    split_ifs
    · simp
    · simp
    · simp only [List.length_cons]
      omega

private theorem pairwise_lt_insertSortedNat (x : ℕ) {l : List ℕ} (hl : l.Pairwise (· < ·)) :
    (insertSortedNat x l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertSortedNat]
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨hy, hys⟩ := hl
    dsimp only [insertSortedNat]
    split_ifs with hlt heq
    · rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr ⟨hy, hys⟩⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hlt
      · exact lt_trans hlt (hy z hz')
    · exact List.pairwise_cons.mpr ⟨hy, hys⟩
    · have hyx : y < x := by omega
      rw [List.pairwise_cons]
      refine ⟨?_, ih hys⟩
      intro z hz
      rcases (mem_insertSortedNat x ys z).mp hz with rfl | hz'
      · exact hyx
      · exact hy z hz'

/-- Fuel-unrolled version of `insertSortedNat` for fixed-length lists in `ComputableInSpace`. -/
private def insertSortedFuel : ℕ → ℕ → List ℕ → List ℕ
  | 0, x, _ => [x]
  | fuel + 1, x, l =>
    if l.isEmpty then [x]
    else
      let y := l.headD 0
      let ys := l.tail
      if x < y then x :: l
      else if x = y then l
      else y :: insertSortedFuel fuel x ys

private theorem insertSortedFuel_eq :
    ∀ (fuel x : ℕ) (l : List ℕ), l.length ≤ fuel → insertSortedFuel fuel x l = insertSortedNat x l
  | 0, x, l, hl => by
    cases l with
    | nil => rfl
    | cons _ _ => simp at hl
  | fuel + 1, x, [], _ => rfl
  | fuel + 1, x, y :: ys, hl => by
    have hys : ys.length ≤ fuel := by simpa using hl
    dsimp only [insertSortedFuel, insertSortedNat]
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.headD_cons, List.tail_cons, insertSortedFuel_eq fuel x ys hys]

/-- Fuel-unrolled optional indexing `l[q]?` for fixed-length lists in `ComputableInSpace`. -/
private def getElemOptFuel : ℕ → List ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, l, q =>
    if l.isEmpty then none
    else if q = 0 then some (l.headD 0)
    else getElemOptFuel fuel l.tail (q - 1)

private theorem getElemOptFuel_eq :
    ∀ (fuel : ℕ) (l : List ℕ) (q : ℕ), l.length ≤ fuel → getElemOptFuel fuel l q = l[q]?
  | 0, l, q, hl => by
    cases l with
    | nil => simp [getElemOptFuel]
    | cons _ _ => simp at hl
  | fuel + 1, [], q, _ => by simp [getElemOptFuel]
  | fuel + 1, y :: ys, 0, _ => by simp [getElemOptFuel]
  | fuel + 1, y :: ys, q + 1, hl => by
    have hys : ys.length ≤ fuel := by simpa using hl
    simp only [getElemOptFuel, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      Nat.add_one_ne_zero, List.tail_cons, Nat.add_sub_cancel, List.getElem?_cons_succ]
    exact getElemOptFuel_eq fuel ys q hys

/-- Fuel-unrolled `l.idxOf u` for fixed-length lists in `ComputableInSpace`. -/
private def idxOfFuel : ℕ → List ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, l, u =>
    if l.isEmpty then 0
    else if l.headD 0 = u then 0
    else idxOfFuel fuel l.tail u + 1

private theorem idxOfFuel_eq :
    ∀ (fuel : ℕ) (l : List ℕ) (u : ℕ), l.length ≤ fuel → idxOfFuel fuel l u = l.idxOf u
  | 0, l, u, hl => by
    cases l with
    | nil => simp [idxOfFuel]
    | cons _ _ => simp at hl
  | fuel + 1, [], u, _ => by simp [idxOfFuel]
  | fuel + 1, y :: ys, u, hl => by
    have hys : ys.length ≤ fuel := by simpa using hl
    simp only [idxOfFuel, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.headD_cons, List.tail_cons, List.idxOf_cons]
    by_cases hyu : y = u
    · simp [hyu]
    · have hbeq : (y == u) = false := beq_false_of_ne hyu
      simp [hyu, hbeq, idxOfFuel_eq fuel ys u hys]

section FuelBudgets

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

private theorem insertSortedFuel_budget (fuel : ℕ) {x : α → ℕ} {l : α → List ℕ}
    (hx : ComputableInSpace x enc encNat S)
    (hl : ComputableInSpace l enc (encList encNat) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => insertSortedFuel fuel (x a) (l a)) enc (encList encNat) S := by
  induction fuel generalizing l with
  | zero =>
    exact budget_cons hx (budget_const [] hin)
  | succ fuel ih =>
    have hy := budget_headD 0 hl
    have hys := budget_tail hl
    have hrec := ih hys
    have hinner := budget_ite (budget_natLt hx hy) (budget_cons hx hl)
      (budget_ite (budget_natEq hx hy) hl (budget_cons hy hrec))
    simpa only [insertSortedFuel, decide_eq_true_eq] using
      budget_ite (budget_isEmpty hl) (budget_cons hx (budget_const [] hin)) hinner

private theorem getElemOptFuel_budget (fuel : ℕ) {l : α → List ℕ} {q : α → ℕ}
    (hl : ComputableInSpace l enc (encList encNat) S)
    (hq : ComputableInSpace q enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => getElemOptFuel fuel (l a) (q a)) enc (encOption encNat) S := by
  induction fuel generalizing l q with
  | zero =>
    exact budget_const none hin
  | succ fuel ih =>
    have hrec := ih (budget_tail hl) (budget_natPred hq)
    simpa only [getElemOptFuel, decide_eq_true_eq] using
      budget_ite (budget_isEmpty hl) (budget_const none hin)
        (budget_ite (budget_natIsZero hq) (budget_optionSome (budget_headD 0 hl)) hrec)

/-- Indexing an optional natural number out of a bounded-length list preserves a common space
budget. -/
private theorem getElem?_budget (fuel : ℕ) {l : α → List ℕ} {q : α → ℕ}
    (hlen : ∀ a, (l a).length ≤ fuel)
    (hl : ComputableInSpace l enc (encList encNat) S)
    (hq : ComputableInSpace q enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => (l a)[q a]?) enc (encOption encNat) S :=
  (getElemOptFuel_budget fuel hl hq hin).of_enc_eq fun a => by
    rw [getElemOptFuel_eq fuel (l a) (q a) (hlen a)]

/-- Indexing an optional natural number out of a bounded-length list and defaulting `none` to `0`
preserves a common space budget. -/
theorem getElem?_getD_zero_budget (fuel : ℕ) {l : α → List ℕ} {q : α → ℕ}
    (hlen : ∀ a, (l a).length ≤ fuel)
    (hl : ComputableInSpace l enc (encList encNat) S)
    (hq : ComputableInSpace q enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => ((l a)[q a]?).getD 0) enc encNat S :=
  budget_optionGetD 0 (getElem?_budget fuel hlen hl hq hin)

private theorem idxOfFuel_budget (fuel : ℕ) {l : α → List ℕ} {u : α → ℕ}
    (hl : ComputableInSpace l enc (encList encNat) S)
    (hu : ComputableInSpace u enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => idxOfFuel fuel (l a) (u a)) enc encNat S := by
  induction fuel generalizing l with
  | zero =>
    exact budget_const 0 hin
  | succ fuel ih =>
    have hrec := ih (budget_tail hl)
    simpa only [idxOfFuel, decide_eq_true_eq] using
      budget_ite (budget_isEmpty hl) (budget_const 0 hin)
        (budget_ite (budget_natEq (budget_headD 0 hl) hu) (budget_const 0 hin)
          (budget_natSucc hrec))

/-- The index of a natural number in a bounded-length list preserves a common space budget. -/
private theorem idxOf_budget (fuel : ℕ) {l : α → List ℕ} {u : α → ℕ}
    (hlen : ∀ a, (l a).length ≤ fuel)
    (hl : ComputableInSpace l enc (encList encNat) S)
    (hu : ComputableInSpace u enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => (l a).idxOf (u a)) enc encNat S :=
  (idxOfFuel_budget fuel hl hu hin).of_enc_eq fun a => by
    rw [idxOfFuel_eq fuel (l a) (u a) (hlen a)]

private theorem pairSortedTargets_budget {a b : α → Option ℕ}
    (ha : ComputableInSpace a enc (encOption encNat) S)
    (hb : ComputableInSpace b enc (encOption encNat) S)
    (hin : (fun x => (enc x).length) ≼ S) :
    ComputableInSpace (fun x => pairSortedTargets (a x) (b x)) enc (encList encNat) S := by
  have hva := budget_optionGetD 0 ha
  have hvb := budget_optionGetD 0 hb
  have hnil : ComputableInSpace (fun _ : α => ([] : List ℕ)) enc (encList encNat) S :=
    budget_const [] hin
  have hboth :=
    budget_ite (budget_natLt hva hvb) (budget_cons hva (budget_cons hvb hnil))
      (budget_ite (budget_natLt hvb hva) (budget_cons hvb (budget_cons hva hnil))
        (budget_cons hva hnil))
  refine (budget_ite (budget_optionIsSome ha)
    (budget_ite (budget_optionIsSome hb) hboth (budget_cons hva hnil))
    (budget_ite (budget_optionIsSome hb) (budget_cons hvb hnil) hnil)).of_enc_eq fun x => ?_
  rcases a x with _ | v₀ <;> rcases b x with _ | v₁ <;>
    simp [pairSortedTargets, decide_eq_true_eq]

end FuelBudgets

end RadixAndListHelpers

section DeterministicStepTarget

variable {k : ℕ} {State : Type} [Fintype State]

/-- Whether transition entry `t` matches `(n, r, symbol)`, fits below `B`, and packs to a valid ID.
-/
private noncomputable def stepEntryPred (B n : ℕ) (r : Register k → ℕ) (symbol : Option Bool)
    (t : Instruction k State) : Bool :=
  let (_, _, _, act) := t
  let nxt := nextRegisters n r act
  matchesEntry n r symbol t && fitsB B nxt &&
    valid (k := k) (State := State) B n (Cslib.Radix.pack B nxt)

/-- Scan a fixed list of instructions for the first valid non-overflowing step target. -/
private noncomputable def findStepTarget (B n : ℕ) (r : Register k → ℕ) (symbol : Option Bool) :
    List (Instruction k State) → Option ℕ
  | [] => none
  | t :: ts =>
    if stepEntryPred (State := State) B n r symbol t then
      let (_, _, _, act) := t
      some (Cslib.Radix.pack B (nextRegisters n r act))
    else
      findStepTarget B n r symbol ts

private theorem findStepTarget_eq_some_imp {B n v : ℕ} {r : Register k → ℕ}
    {symbol : Option Bool} :
    ∀ {l : List (Instruction k State)},
      findStepTarget (State := State) B n r symbol l = some v →
        ∃ t ∈ l, stepEntryPred (State := State) B n r symbol t = true ∧
          v = Cslib.Radix.pack B (nextRegisters n r t.2.2.2)
  | [], h => by simp [findStepTarget] at h
  | t :: ts, h => by
    dsimp only [findStepTarget] at h
    split_ifs at h with hp
    · rw [Option.some.injEq] at h
      exact ⟨t, List.mem_cons_self, hp, h.symm⟩
    · obtain ⟨t', hmem, hp', hv⟩ := findStepTarget_eq_some_imp h
      exact ⟨t', List.mem_cons_of_mem t hmem, hp', hv⟩

private theorem findStepTarget_ne_none_of_mem {B n : ℕ} {r : Register k → ℕ}
    {symbol : Option Bool} :
    ∀ {l : List (Instruction k State)} {t : Instruction k State},
      t ∈ l → stepEntryPred (State := State) B n r symbol t = true →
        ∃ v, findStepTarget (State := State) B n r symbol l = some v
  | [], _, hmem, _ => by simp at hmem
  | t₀ :: ts, t, hmem, hp => by
    dsimp only [findStepTarget]
    split_ifs with hp₀
    · exact ⟨_, rfl⟩
    · rcases List.mem_cons.mp hmem with rfl | hts
      · exact absurd hp hp₀
      · exact findStepTarget_ne_none_of_mem hts hp

/-- Compute the unique compact target ID (if any) of a deterministic machine step from `u` with
supplied input symbol `symbol`. -/
noncomputable def stepTargetWithSymbol (tm : MultiTapeTM k Bool State)
    (B n u : ℕ) (symbol : Option Bool) : Option ℕ :=
  let r := readRegisters (k := k) B u
  if valid (k := k) (State := State) B n u then
    if r .control = stateCode (none : Option State) then
      some u
    else
      findStepTarget (State := State) B n r symbol (instructions tm.toMultiTapeNTM)
  else
    none

private theorem edgeWithSymbol_of_stepTargetWithSymbol (tm : MultiTapeTM k Bool State)
    {B n u v : ℕ} {symbol : Option Bool}
    (h : stepTargetWithSymbol tm B n u symbol = some v) :
    edgeWithSymbol tm.toMultiTapeNTM B n u v symbol = true := by
  dsimp only [stepTargetWithSymbol] at h
  split_ifs at h with hvu hhalt
  · rw [Option.some.injEq] at h
    subst h
    simp only [edgeWithSymbol, hvu, Bool.true_and, hhalt, decide_true, Bool.true_or]
  · obtain ⟨t, hmem, hp, hv⟩ := findStepTarget_eq_some_imp h
    simp only [stepEntryPred, Bool.and_eq_true] at hp
    obtain ⟨⟨hm, hf⟩, hvv⟩ := hp
    rw [← hv] at hvv
    simp only [edgeWithSymbol, hvu, hvv, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨t, hmem, ⟨hm, hf⟩, hv⟩

/-- `stepTargetWithSymbol` returns `some v` iff `edgeWithSymbol` holds at `(u, v)`. -/
theorem stepTargetWithSymbol_eq_some_iff (tm : MultiTapeTM k Bool State)
    (B n u v : ℕ) (symbol : Option Bool) :
    stepTargetWithSymbol tm B n u symbol = some v ↔
      edgeWithSymbol tm.toMultiTapeNTM B n u v symbol = true := by
  constructor
  · exact edgeWithSymbol_of_stepTargetWithSymbol tm
  · intro he
    have he_orig := he
    simp only [edgeWithSymbol, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      List.any_eq_true] at he
    obtain ⟨⟨hvu, hvv⟩, hdisj⟩ := he
    rcases hdisj with ⟨hhalt, rfl⟩ | ⟨t, hmem, ⟨hm, hf⟩, rfl⟩
    · simp [stepTargetWithSymbol, hvu, hhalt]
    · have hnot_halt :
          readRegisters (k := k) B u .control ≠ stateCode (none : Option State) := by
        intro hctrl
        simp only [matchesEntry, Bool.and_eq_true, decide_eq_true_eq] at hm
        have hinj := stateCode_injective (hctrl.symm.trans hm.1.1)
        cases hinj
      have hp :
          stepEntryPred (State := State) B n (readRegisters (k := k) B u) symbol t = true := by
        simp [stepEntryPred, hm, hf, hvv]
      obtain ⟨v', hfind⟩ := findStepTarget_ne_none_of_mem hmem hp
      have hstep' : stepTargetWithSymbol tm B n u symbol = some v' := by
        simp [stepTargetWithSymbol, hvu, hnot_halt, hfind]
      have he' := edgeWithSymbol_of_stepTargetWithSymbol tm hstep'
      have hv_eq := edgeWithSymbol_target_unique tm he' he_orig
      exact hv_eq ▸ hstep'

section Budgets

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
  {B n u : α → ℕ} {symbol : α → Option Bool}

theorem stepTargetWithSymbol_budget (tm : MultiTapeTM k Bool State)
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => stepTargetWithSymbol tm (B a) (n a) (u a) (symbol a))
      enc (encOption encNat) S := by
  have hr := readRegisters_budget (k := k) hB hu
  have hfind : ∀ l : List (Instruction k State),
      ComputableInSpace
        (fun a => findStepTarget (State := State) (B a) (n a)
          (readRegisters (k := k) (B a) (u a)) (symbol a) l)
        enc (encOption encNat) S := by
    intro l
    induction l with
    | nil => exact budget_const none hin
    | cons t ts ih =>
      have hnxt := nextRegisters_budget hn hr hin t.2.2.2
      have hpack := pack_inSpace hB hnxt hin
      have hpred := budget_boolAnd
        (budget_boolAnd (matchesEntry_budget hn hr hs hin t) (fitsB_budget hB hnxt hin))
        (valid_budget (k := k) (State := State) hB hn hpack hin)
      exact (budget_ite hpred (budget_optionSome hpack) ih).of_enc_eq fun a => by
        dsimp only [findStepTarget, stepEntryPred]
        rfl
  simpa only [stepTargetWithSymbol, decide_eq_true_eq] using
    budget_ite (valid_budget (k := k) (State := State) hB hn hu hin)
      (budget_ite (budget_natEq (hr .control) (budget_const (stateCode (none : Option State)) hin))
        (budget_optionSome hu) (hfind (instructions tm.toMultiTapeNTM)))
      (budget_const none hin)

end Budgets

end DeterministicStepTarget

end Turing.MultiTapeNTM.ConfigurationGraph

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph Cslib.Turing MultiTapeTM ComputableInSpace

variable {k : ℕ} {State : Type} [Fintype State]

/-! ### Forward fair-coin outgoing targets -/

/-- Sorted duplicate-free list (of length at most `2`) of valid compact targets reachable in one
fair-coin step from `u` under input symbol `symbol`. -/
noncomputable def coinOutTargetsWithSymbol (machine : MultiTapePTM k Bool State)
    (B n u : ℕ) (symbol : Option Bool) : List ℕ :=
  pairSortedTargets
    (stepTargetWithSymbol (machine.withCoin false).toTM B n u symbol)
    (stepTargetWithSymbol (machine.withCoin true).toTM B n u symbol)

theorem nodup_coinOutTargetsWithSymbol (machine : MultiTapePTM k Bool State)
    (B n u : ℕ) (symbol : Option Bool) :
    (coinOutTargetsWithSymbol machine B n u symbol).Nodup :=
  nodup_pairSortedTargets _ _

theorem length_coinOutTargetsWithSymbol_le (machine : MultiTapePTM k Bool State)
    (B n u : ℕ) (symbol : Option Bool) :
    (coinOutTargetsWithSymbol machine B n u symbol).length ≤ 2 :=
  length_pairSortedTargets_le _ _

/-- When both coin branches target the same compact ID `v`, `coinOutTargetsWithSymbol` is `[v]`. -/
theorem coinOutTargetsWithSymbol_eq_singleton (machine : MultiTapePTM k Bool State)
    {B n u v : ℕ} {symbol : Option Bool}
    (hf : stepTargetWithSymbol (machine.withCoin false).toTM B n u symbol = some v)
    (ht : stepTargetWithSymbol (machine.withCoin true).toTM B n u symbol = some v) :
    coinOutTargetsWithSymbol machine B n u symbol = [v] := by
  simp [coinOutTargetsWithSymbol, pairSortedTargets, hf, ht]

/-- When the two coin branches target `v₀ < v₁`, `coinOutTargetsWithSymbol` is `[v₀, v₁]`. -/
theorem coinOutTargetsWithSymbol_eq_pair_of_lt (machine : MultiTapePTM k Bool State)
    {B n u v₀ v₁ : ℕ} {symbol : Option Bool}
    (hf : stepTargetWithSymbol (machine.withCoin false).toTM B n u symbol = some v₀)
    (ht : stepTargetWithSymbol (machine.withCoin true).toTM B n u symbol = some v₁)
    (hlt : v₀ < v₁) :
    coinOutTargetsWithSymbol machine B n u symbol = [v₀, v₁] := by
  simp [coinOutTargetsWithSymbol, pairSortedTargets, hf, ht, hlt]

/-- When the two coin branches target `v₀ > v₁`, `coinOutTargetsWithSymbol` is `[v₁, v₀]`. -/
theorem coinOutTargetsWithSymbol_eq_pair_of_gt (machine : MultiTapePTM k Bool State)
    {B n u v₀ v₁ : ℕ} {symbol : Option Bool}
    (hf : stepTargetWithSymbol (machine.withCoin false).toTM B n u symbol = some v₀)
    (ht : stepTargetWithSymbol (machine.withCoin true).toTM B n u symbol = some v₁)
    (hgt : v₁ < v₀) :
    coinOutTargetsWithSymbol machine B n u symbol = [v₁, v₀] := by
  have hnot : ¬ v₀ < v₁ := Nat.not_lt.mpr (Nat.le_of_lt hgt)
  simp [coinOutTargetsWithSymbol, pairSortedTargets, hf, ht, hnot, hgt]

/-- A vertex `v` lies in `coinOutTargetsWithSymbol` iff its fair-coin edge multiplicity is positive.
-/
theorem mem_coinOutTargetsWithSymbol_iff (machine : MultiTapePTM k Bool State)
    (B n u v : ℕ) (symbol : Option Bool) :
    v ∈ coinOutTargetsWithSymbol machine B n u symbol ↔
      0 < coinCountWithSymbol machine B n u v symbol := by
  rw [coinOutTargetsWithSymbol, mem_pairSortedTargets, stepTargetWithSymbol_eq_some_iff,
    stepTargetWithSymbol_eq_some_iff, coinCountWithSymbol]
  cases edgeWithSymbol (machine.withCoin false).toTM.toMultiTapeNTM B n u v symbol <;>
    cases edgeWithSymbol (machine.withCoin true).toTM.toMultiTapeNTM B n u v symbol <;>
    decide

theorem lt_vertexBound_of_mem_coinOutTargetsWithSymbol (machine : MultiTapePTM k Bool State)
    {B n u v : ℕ} {symbol : Option Bool}
    (hv : v ∈ coinOutTargetsWithSymbol machine B n u symbol) :
    u < vertexBound (k := k) B ∧ v < vertexBound (k := k) B := by
  have hpos := (mem_coinOutTargetsWithSymbol_iff machine B n u v symbol).mp hv
  constructor
  · by_contra hu
    rw [coinCountWithSymbol_eq_zero_of_source_ge machine (Nat.le_of_not_lt hu) symbol] at hpos
    omega
  · by_contra hv'
    rw [coinCountWithSymbol_eq_zero_of_target_ge machine (Nat.le_of_not_lt hv') symbol] at hpos
    omega

theorem coinOutTargetsWithSymbol_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {B n u : α → ℕ} {symbol : α → Option Bool} (machine : MultiTapePTM k Bool State)
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => coinOutTargetsWithSymbol machine (B a) (n a) (u a) (symbol a))
      enc (encList encNat) S :=
  pairSortedTargets_budget
    (stepTargetWithSymbol_budget (machine.withCoin false).toTM hB hn hu hs hin)
    (stepTargetWithSymbol_budget (machine.withCoin true).toTM hB hn hu hs hin) hin

/-! ### Backward predecessor recipes and incoming sources -/

/-- Machine-fixed recipe reconstructing one candidate predecessor compact ID from a target ID `v`:
either `v` itself (for halted absorbing self-loops) or an inverted transition-table step together
with a binary input-boundary flag and a three-valued pre-step output code. -/
inductive PredRecipe (k : ℕ) (State : Type)
  /-- Absorbing self-loop candidate returning `v` itself. -/
  | self
  /-- Inverted transition-table step with input-boundary flag and pre-step output code. -/
  | step (t : Instruction k State) (altInput : Bool) (prevOutput : Fin 3)

/-- Reconstruct candidate source registers from target registers `rv` for a transition recipe. -/
private noncomputable def predRegisters (rv : Register k → ℕ) (t : Instruction k State)
    (altInput : Bool) (prevOutput : Fin 3) : Register k → ℕ :=
  let (qSrc, _, workObs, act) := t
  fun reg => match reg with
    | .inputPos =>
      match act.inputTape with
      | .neg => if altInput then rv .inputPos else rv .inputPos + 1
      | .zero => rv .inputPos
      | .pos => if altInput then rv .inputPos else rv .inputPos - 1
    | .control => stateCode (some qSrc)
    | .output => prevOutput.val
    | .head i => symbolCode (workObs i)
    | .left i =>
      match (act.workTapes i).2 with
      | .neg => rv (.head i) + 3 * rv (.left i)
      | .zero => rv (.left i)
      | .pos => rv (.left i) / 3
    | .right i =>
      match (act.workTapes i).2 with
      | .neg => rv (.right i) / 3
      | .zero => rv (.right i)
      | .pos => rv (.head i) + 3 * rv (.right i)

/-- Evaluate a predecessor recipe at radix `B` on target compact ID `v`. -/
noncomputable def evalPredRecipe : PredRecipe k State → ℕ → ℕ → ℕ
  | .self, _, v => v
  | .step t altInput prevOutput, B, v =>
    Cslib.Radix.pack B (predRegisters (readRegisters (k := k) B v) t altInput prevOutput)

/-- Six transition recipes associated to a single transition-table entry `t`. -/
private def stepRecipesFor (t : Instruction k State) : List (PredRecipe k State) :=
  ([false, true] : List Bool).flatMap fun altInput =>
    ([0, 1, 2] : List (Fin 3)).map fun prevOutput =>
      PredRecipe.step t altInput prevOutput

omit [Fintype State] in
private theorem mem_stepRecipesFor (t : Instruction k State) (altInput : Bool)
    (prevOutput : Fin 3) :
    PredRecipe.step t altInput prevOutput ∈ stepRecipesFor t := by
  simp only [stepRecipesFor, List.mem_flatMap, List.mem_map]
  refine ⟨altInput, by cases altInput <;> simp, prevOutput, ?_, rfl⟩
  fin_cases prevOutput <;> simp

/-- Complete machine-fixed list of candidate predecessor recipes for `machine`. -/
noncomputable def predRecipes (machine : MultiTapePTM k Bool State) : List (PredRecipe k State) :=
  PredRecipe.self ::
    ((instructions (machine.withCoin false).toTM.toMultiTapeNTM ++
      instructions (machine.withCoin true).toTM.toMultiTapeNTM).flatMap stepRecipesFor)

/-- Constant incoming port bound of `machine` (`1 + 6 * |instructions₀ ++ instructions₁|`). -/
@[expose] noncomputable def inPortBound (machine : MultiTapePTM k Bool State) : ℕ :=
  (predRecipes machine).length

theorem inPortBound_pos (machine : MultiTapePTM k Bool State) : 0 < inPortBound machine := by
  simp [inPortBound, predRecipes]

private theorem predRegisters_eq_of_step {B n : ℕ} {r : Register k → ℕ} {symbol : Option Bool}
    {t : Instruction k State} (hB : 0 < B)
    (hin_lt : r .inputPos < n + 2) (hout_lt : r .output < 3)
    (hm : matchesEntry n r symbol t = true)
    (hf : fitsB B (nextRegisters n r t.2.2.2) = true) :
    ∃ (altInput : Bool) (prevOutput : Fin 3),
      predRegisters (readRegisters (k := k) B (Cslib.Radix.pack B (nextRegisters n r t.2.2.2)))
        t altInput prevOutput = r := by
  let (qSrc, inObs, workObs, act) := t
  have hfits : ∀ reg : Register k, nextRegisters n r act reg < B := by
    intro reg
    simp only [fitsB, List.all_eq_true, Finset.mem_toList, Finset.mem_univ,
      decide_eq_true_eq] at hf
    exact hf reg trivial
  have hrv : ∀ reg : Register k,
      readRegisters (k := k) B (Cslib.Radix.pack B (nextRegisters n r act)) reg =
        nextRegisters n r act reg :=
    fun reg => Cslib.Radix.component_pack hB hfits reg
  simp only [matchesEntry, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_ofFn, id_eq] at hm
  obtain ⟨⟨hctrl, _⟩, hheads⟩ := hm
  let prevOutput : Fin 3 := ⟨r .output, hout_lt⟩
  let altInput : Bool :=
    match act.inputTape with
    | .neg => decide (r .inputPos = 0)
    | .zero => false
    | .pos => decide (r .inputPos = n + 1)
  refine ⟨altInput, prevOutput, funext fun reg => ?_⟩
  cases reg with
  | inputPos =>
    dsimp only [predRegisters, altInput]
    rw [hrv .inputPos]
    cases hm_in : act.inputTape <;> simp only [nextRegisters, inputMove, hm_in]
    · rcases Nat.eq_zero_or_pos (r .inputPos) with h0 | hpos
      · simp [h0]
      · simp only [Nat.ne_of_gt hpos, decide_false, Bool.false_eq_true, ↓reduceIte]
        omega
    · by_cases hn1 : r .inputPos = n + 1
      · simp [hn1]
      · have hle : r .inputPos + 1 ≤ n + 1 := by omega
        simp [hn1, Nat.min_eq_left hle]
  | control =>
    dsimp only [predRegisters]
    exact hctrl.symm
  | output =>
    rfl
  | head i =>
    dsimp only [predRegisters]
    exact (of_decide_eq_true (hheads _ ⟨i, rfl⟩)).symm
  | left i =>
    have hhi : r (.head i) = symbolCode (workObs i) :=
      of_decide_eq_true (hheads _ ⟨i, rfl⟩)
    let hwrite := (act.workTapes i).1.elim (r (.head i)) symbolCode
    have hhwrite_lt : hwrite < 3 := by
      dsimp only [hwrite]
      rcases (act.workTapes i).1 with _ | b
      · rw [Option.elim_none, hhi]
        exact symbolCode_lt _
      · exact symbolCode_lt b
    dsimp only [predRegisters]
    rw [hrv (.head i), hrv (.left i)]
    cases hm_wt : (act.workTapes i).2 <;>
      simp only [nextRegisters, tapeStep, hm_wt]
    · exact Nat.mod_add_div (r (.left i)) 3
    · change (hwrite + 3 * r (.left i)) / 3 = r (.left i)
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 3), Nat.div_eq_of_lt hhwrite_lt, Nat.zero_add]
  | right i =>
    have hhi : r (.head i) = symbolCode (workObs i) :=
      of_decide_eq_true (hheads _ ⟨i, rfl⟩)
    let hwrite := (act.workTapes i).1.elim (r (.head i)) symbolCode
    have hhwrite_lt : hwrite < 3 := by
      dsimp only [hwrite]
      rcases (act.workTapes i).1 with _ | b
      · rw [Option.elim_none, hhi]
        exact symbolCode_lt _
      · exact symbolCode_lt b
    dsimp only [predRegisters]
    rw [hrv (.head i), hrv (.right i)]
    cases hm_wt : (act.workTapes i).2 <;>
      simp only [nextRegisters, tapeStep, hm_wt]
    · change (hwrite + 3 * r (.right i)) / 3 = r (.right i)
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 3), Nat.div_eq_of_lt hhwrite_lt, Nat.zero_add]
    · exact Nat.mod_add_div (r (.right i)) 3

private theorem exists_predRecipe_of_edgeWithSymbol {B n u v : ℕ} {symbol : Option Bool}
    {bit : Bool} (machine : MultiTapePTM k Bool State)
    (he : edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B n u v symbol = true) :
    ∃ rec ∈ predRecipes machine, evalPredRecipe rec B v = u := by
  simp only [edgeWithSymbol, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at he
  obtain ⟨⟨hvu, _⟩, hdisj⟩ := he
  rcases hdisj with ⟨_, rfl⟩ | ⟨t, hmem, ⟨hm, hf⟩, rfl⟩
  · exact ⟨.self, by simp [predRecipes], rfl⟩
  · simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hvu
    obtain ⟨⟨⟨⟨hu_lt, hin_lt⟩, _⟩, hout_lt⟩, _⟩ := hvu
    have hB : 0 < B := radix_pos_of_lt_vertexBound hu_lt
    obtain ⟨altInput, prevOutput, hpred⟩ := predRegisters_eq_of_step hB hin_lt hout_lt hm hf
    refine ⟨.step t altInput prevOutput, ?_, ?_⟩
    · simp only [predRecipes, List.mem_cons, List.mem_flatMap, List.mem_append]
      refine Or.inr ⟨t, ?_, mem_stepRecipesFor t altInput prevOutput⟩
      cases bit
      · exact Or.inl hmem
      · exact Or.inr hmem
    · dsimp only [evalPredRecipe]
      rw [hpred, pack_readRegisters_of_lt_vertexBound hu_lt]

/-- Completeness of `predRecipes`: every positive-multiplicity fair-coin edge `(u, v)` is recovered
by evaluating some recipe in `predRecipes machine` at `v`. -/
theorem exists_predRecipe_of_coinCountWithSymbol_pos (machine : MultiTapePTM k Bool State)
    {B n u v : ℕ} {symbol : Option Bool}
    (hpos : 0 < coinCountWithSymbol machine B n u v symbol) :
    ∃ rec ∈ predRecipes machine, evalPredRecipe rec B v = u := by
  unfold coinCountWithSymbol at hpos
  cases hf : edgeWithSymbol (machine.withCoin false).toTM.toMultiTapeNTM B n u v symbol
  · cases ht : edgeWithSymbol (machine.withCoin true).toTM.toMultiTapeNTM B n u v symbol
    · simp [hf, ht] at hpos
    · exact exists_predRecipe_of_edgeWithSymbol (bit := true) machine ht
  · exact exists_predRecipe_of_edgeWithSymbol (bit := false) machine hf

/-- Collect and sort valid predecessors from a list of recipes paired with their pre-queried input
symbols. -/
private noncomputable def collectInSources (machine : MultiTapePTM k Bool State) (B n v : ℕ) :
    List (PredRecipe k State) → List (Option Bool) → List ℕ
  | [], _ => []
  | _, [] => []
  | rec :: recs, sym :: syms =>
    let u := evalPredRecipe rec B v
    let rest := collectInSources machine B n v recs syms
    if 0 < coinCountWithSymbol machine B n u v sym then
      insertSortedNat u rest
    else
      rest

private theorem pairwise_lt_collectInSources (machine : MultiTapePTM k Bool State) (B n v : ℕ) :
    ∀ (recs : List (PredRecipe k State)) (syms : List (Option Bool)),
      (collectInSources machine B n v recs syms).Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | _ :: _, [] => List.Pairwise.nil
  | rec :: recs, sym :: syms => by
    dsimp only [collectInSources]
    have ih := pairwise_lt_collectInSources machine B n v recs syms
    split_ifs
    · exact pairwise_lt_insertSortedNat _ ih
    · exact ih

private theorem length_collectInSources_le (machine : MultiTapePTM k Bool State) (B n v : ℕ) :
    ∀ (recs : List (PredRecipe k State)) (syms : List (Option Bool)),
      (collectInSources machine B n v recs syms).length ≤ recs.length
  | [], _ => le_rfl
  | _ :: _, [] => Nat.zero_le _
  | rec :: recs, sym :: syms => by
    dsimp only [collectInSources]
    have ih := length_collectInSources_le machine B n v recs syms
    split_ifs
    · exact (length_insertSortedNat_le _ _).trans (Nat.succ_le_succ ih)
    · exact ih.trans (Nat.le_succ _)

private theorem mem_collectInSources_map_iff (machine : MultiTapePTM k Bool State)
    (B : ℕ) (w : List Bool) (v u : ℕ) :
    ∀ (recs : List (PredRecipe k State)),
      u ∈ collectInSources machine B w.length v recs
          (recs.map fun rec => w[queryIndex (k := k) B (evalPredRecipe rec B v)]?) ↔
        (∃ rec ∈ recs, evalPredRecipe rec B v = u) ∧
          0 < coinCountWithSymbol machine B w.length u v w[queryIndex (k := k) B u]?
  | [] => by simp [collectInSources]
  | rec :: recs => by
    simp only [List.map_cons, collectInSources]
    have ih := mem_collectInSources_map_iff machine B w v u recs
    split_ifs with hpos
    · rw [mem_insertSortedNat, ih]
      constructor
      · rintro (rfl | ⟨⟨rec', hmem, heq⟩, hpos'⟩)
        · exact ⟨⟨rec, List.mem_cons_self, rfl⟩, hpos⟩
        · exact ⟨⟨rec', List.mem_cons_of_mem rec hmem, heq⟩, hpos'⟩
      · rintro ⟨⟨rec', hmem, heq⟩, hpos'⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact Or.inl heq.symm
        · exact Or.inr ⟨⟨rec', hmem', heq⟩, hpos'⟩
    · rw [ih]
      constructor
      · rintro ⟨⟨rec', hmem, heq⟩, hpos'⟩
        exact ⟨⟨rec', List.mem_cons_of_mem rec hmem, heq⟩, hpos'⟩
      · rintro ⟨⟨rec', hmem, heq⟩, hpos'⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · subst heq
          exact absurd hpos' hpos
        · exact ⟨⟨rec', hmem', heq⟩, hpos'⟩

/-- Incoming sources of `v` computed from pre-queried input symbols aligned with `predRecipes`. -/
noncomputable def coinInSourcesWithSymbols (machine : MultiTapePTM k Bool State)
    (B n v : ℕ) (syms : List (Option Bool)) : List ℕ :=
  collectInSources machine B n v (predRecipes machine) syms

/-- Sorted duplicate-free list of all compact predecessors `u` with a positive-multiplicity
fair-coin transition to `v` on input word `w`. -/
@[expose] noncomputable def coinInSources (machine : MultiTapePTM k Bool State)
    (B : ℕ) (w : List Bool) (v : ℕ) : List ℕ :=
  coinInSourcesWithSymbols machine B w.length v
    ((predRecipes machine).map fun rec => w[queryIndex (k := k) B (evalPredRecipe rec B v)]?)

theorem nodup_coinInSourcesWithSymbols (machine : MultiTapePTM k Bool State)
    (B n v : ℕ) (syms : List (Option Bool)) :
    (coinInSourcesWithSymbols machine B n v syms).Nodup :=
  (pairwise_lt_collectInSources machine B n v (predRecipes machine) syms).imp ne_of_lt

theorem length_coinInSourcesWithSymbols_le (machine : MultiTapePTM k Bool State)
    (B n v : ℕ) (syms : List (Option Bool)) :
    (coinInSourcesWithSymbols machine B n v syms).length ≤ inPortBound machine :=
  length_collectInSources_le machine B n v (predRecipes machine) syms

theorem nodup_coinInSources (machine : MultiTapePTM k Bool State)
    (B : ℕ) (w : List Bool) (v : ℕ) :
    (coinInSources machine B w v).Nodup :=
  nodup_coinInSourcesWithSymbols machine B w.length v _

theorem length_coinInSources_le (machine : MultiTapePTM k Bool State)
    (B : ℕ) (w : List Bool) (v : ℕ) :
    (coinInSources machine B w v).length ≤ inPortBound machine :=
  length_coinInSourcesWithSymbols_le machine B w.length v _

/-- `u ∈ coinInSources machine B w v` iff `coinCountWithSymbol` at `(u, v)` is positive. -/
theorem mem_coinInSources_iff (machine : MultiTapePTM k Bool State)
    (B : ℕ) (w : List Bool) (u v : ℕ) :
    u ∈ coinInSources machine B w v ↔
      0 < coinCountWithSymbol machine B w.length u v w[queryIndex (k := k) B u]? := by
  rw [coinInSources, coinInSourcesWithSymbols, mem_collectInSources_map_iff]
  exact ⟨fun h => h.2, fun hpos =>
    ⟨exists_predRecipe_of_coinCountWithSymbol_pos machine hpos, hpos⟩⟩

/-- Exact adjacency symmetry between `coinOutTargetsWithSymbol` and `coinInSources`. -/
theorem mem_coinOutTargetsWithSymbol_iff_mem_coinInSources (machine : MultiTapePTM k Bool State)
    (B : ℕ) (w : List Bool) (u v : ℕ) :
    v ∈ coinOutTargetsWithSymbol machine B w.length u w[queryIndex (k := k) B u]? ↔
      u ∈ coinInSources machine B w v := by
  rw [mem_coinOutTargetsWithSymbol_iff, mem_coinInSources_iff]

/-! ### Clocked natural-number paired ports and multiplicities -/

/-- Pre-queried outgoing port lookup on clocked IDs. -/
@[expose] noncomputable def clockedOutPortWithSymbols (machine : MultiTapePTM k Bool State)
    (D d n a p : ℕ) (symOut : Option Bool) (inSyms : List (Option Bool)) : Option (ℕ × ℕ) :=
  let B := radix D n
  let N := vertexBound (k := k) B
  let T := polyClock d n
  if a < clockedVertexBound (k := k) D d n ∧ p < 2 ∧ a / N < T then
    let u := a % N
    match (coinOutTargetsWithSymbol machine B n u symOut)[p]? with
    | none => none
    | some v =>
      some ((a / N + 1) * N + v, (coinInSourcesWithSymbols machine B n v inSyms).idxOf u)
  else
    none

/-- Outgoing port lookup on clocked IDs `(a, p)` for input word `w`. -/
@[expose] noncomputable def clockedOutPort (machine : MultiTapePTM k Bool State)
    (D d : ℕ) (w : List Bool) (a p : ℕ) : Option (ℕ × ℕ) :=
  let n := w.length
  let B := radix D n
  let N := vertexBound (k := k) B
  let T := polyClock d n
  if a < clockedVertexBound (k := k) D d n ∧ p < 2 ∧ a / N < T then
    let u := a % N
    let symOut := w[queryIndex (k := k) B u]?
    match (coinOutTargetsWithSymbol machine B n u symOut)[p]? with
    | none => none
    | some v =>
      some ((a / N + 1) * N + v, (coinInSources machine B w v).idxOf u)
  else
    none

/-- Pre-queried incoming port lookup on clocked IDs. -/
@[expose] noncomputable def clockedInPortWithSymbols (machine : MultiTapePTM k Bool State)
    (D d n b q : ℕ) (inSyms : List (Option Bool)) (symPred : Option Bool) : Option (ℕ × ℕ) :=
  let B := radix D n
  let N := vertexBound (k := k) B
  if b < clockedVertexBound (k := k) D d n ∧ q < inPortBound machine ∧ 0 < b / N then
    let v := b % N
    match (coinInSourcesWithSymbols machine B n v inSyms)[q]? with
    | none => none
    | some u =>
      some ((b / N - 1) * N + u, (coinOutTargetsWithSymbol machine B n u symPred).idxOf v)
  else
    none

/-- Incoming port lookup on clocked IDs `(b, q)` for input word `w`. -/
@[expose] noncomputable def clockedInPort (machine : MultiTapePTM k Bool State)
    (D d : ℕ) (w : List Bool) (b q : ℕ) : Option (ℕ × ℕ) :=
  let n := w.length
  let B := radix D n
  let N := vertexBound (k := k) B
  if b < clockedVertexBound (k := k) D d n ∧ q < inPortBound machine ∧ 0 < b / N then
    let v := b % N
    match (coinInSources machine B w v)[q]? with
    | none => none
    | some u =>
      let symPred := w[queryIndex (k := k) B u]?
      some ((b / N - 1) * N + u, (coinOutTargetsWithSymbol machine B n u symPred).idxOf v)
  else
    none

/-- Pre-queried outgoing port multiplicity (`0`, `1`, or `2`) on clocked IDs. -/
@[expose] noncomputable def clockedOutCountWithSymbol (machine : MultiTapePTM k Bool State)
    (D d n a p : ℕ) (symOut : Option Bool) : ℕ :=
  let B := radix D n
  let N := vertexBound (k := k) B
  let T := polyClock d n
  if a < clockedVertexBound (k := k) D d n ∧ p < 2 ∧ a / N < T then
    let u := a % N
    match (coinOutTargetsWithSymbol machine B n u symOut)[p]? with
    | none => 0
    | some v => coinCountWithSymbol machine B n u v symOut
  else
    0

/-- Outgoing port multiplicity (`0`, `1`, or `2`) on clocked IDs `(a, p)` for input word `w`. -/
@[expose] noncomputable def clockedOutCount (machine : MultiTapePTM k Bool State)
    (D d : ℕ) (w : List Bool) (a p : ℕ) : ℕ :=
  let B := radix D w.length
  let N := vertexBound (k := k) B
  clockedOutCountWithSymbol machine D d w.length a p w[queryIndex (k := k) B (a % N)]?

theorem clockedOutCount_le_two (machine : MultiTapePTM k Bool State)
    (D d : ℕ) (w : List Bool) (a p : ℕ) :
    clockedOutCount machine D d w a p ≤ 2 := by
  dsimp only [clockedOutCount, clockedOutCountWithSymbol]
  split_ifs
  · cases (coinOutTargetsWithSymbol machine (radix D w.length) w.length
        (a % vertexBound (k := k) (radix D w.length))
        w[queryIndex (k := k) (radix D w.length)
          (a % vertexBound (k := k) (radix D w.length))]?)[p]? with
    | none => simp
    | some v => exact coinCountWithSymbol_le_two machine ..
  · omega

theorem clockedOutPort_eq_none_of_ge_bound (machine : MultiTapePTM k Bool State)
    {D d : ℕ} {w : List Bool} {a : ℕ} (ha : clockedVertexBound (k := k) D d w.length ≤ a)
    (p : ℕ) : clockedOutPort machine D d w a p = none := by
  dsimp only [clockedOutPort]
  rw [ite_eq_right]
  omega

theorem clockedOutPort_eq_none_of_port_ge (machine : MultiTapePTM k Bool State)
    {D d : ℕ} {w : List Bool} (a : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    clockedOutPort machine D d w a p = none := by
  dsimp only [clockedOutPort]
  rw [ite_eq_right]
  omega

theorem clockedInPort_eq_none_of_ge_bound (machine : MultiTapePTM k Bool State)
    {D d : ℕ} {w : List Bool} {b : ℕ} (hb : clockedVertexBound (k := k) D d w.length ≤ b)
    (q : ℕ) : clockedInPort machine D d w b q = none := by
  dsimp only [clockedInPort]
  rw [ite_eq_right]
  omega

theorem clockedInPort_eq_none_of_port_ge (machine : MultiTapePTM k Bool State)
    {D d : ℕ} {w : List Bool} (b : ℕ) {q : ℕ} (hq : inPortBound machine ≤ q) :
    clockedInPort machine D d w b q = none := by
  dsimp only [clockedInPort]
  rw [ite_eq_right]
  omega

theorem clockedOutCount_eq_zero_of_ge_bound (machine : MultiTapePTM k Bool State)
    {D d : ℕ} {w : List Bool} {a : ℕ} (ha : clockedVertexBound (k := k) D d w.length ≤ a)
    (p : ℕ) : clockedOutCount machine D d w a p = 0 := by
  dsimp only [clockedOutCount, clockedOutCountWithSymbol]
  rw [ite_eq_right]
  omega

theorem clockedOutCount_eq_zero_of_port_ge (machine : MultiTapePTM k Bool State)
    {D d : ℕ} {w : List Bool} (a : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    clockedOutCount machine D d w a p = 0 := by
  dsimp only [clockedOutCount, clockedOutCountWithSymbol]
  rw [ite_eq_right]
  omega

theorem clockedOutCount_eq_zero_of_outPort_eq_none (machine : MultiTapePTM k Bool State)
    {D d : ℕ} {w : List Bool} {a p : ℕ} (h : clockedOutPort machine D d w a p = none) :
    clockedOutCount machine D d w a p = 0 := by
  dsimp only [clockedOutPort] at h
  dsimp only [clockedOutCount, clockedOutCountWithSymbol]
  split_ifs at h ⊢ with hcond
  · cases hg : (coinOutTargetsWithSymbol machine (radix D w.length) w.length
        (a % vertexBound (k := k) (radix D w.length))
        w[queryIndex (k := k) (radix D w.length)
          (a % vertexBound (k := k) (radix D w.length))]?)[p]? with
    | none => rfl
    | some v => rw [hg] at h; cases h
  · rfl

theorem clockedOutCount_pos_of_outPort_eq_some (machine : MultiTapePTM k Bool State)
    {D d : ℕ} {w : List Bool} {a p b q : ℕ}
    (h : clockedOutPort machine D d w a p = some (b, q)) :
    0 < clockedOutCount machine D d w a p := by
  dsimp only [clockedOutPort] at h
  dsimp only [clockedOutCount, clockedOutCountWithSymbol]
  split_ifs at h ⊢
  cases hg : (coinOutTargetsWithSymbol machine (radix D w.length) w.length
      (a % vertexBound (k := k) (radix D w.length))
      w[queryIndex (k := k) (radix D w.length)
        (a % vertexBound (k := k) (radix D w.length))]?)[p]? with
  | none => rw [hg] at h; cases h
  | some v => exact (mem_coinOutTargetsWithSymbol_iff machine ..).mp (List.mem_of_getElem? hg)

theorem clockedOutCount_eq_clockedCoinCount_of_outPort_eq_some
    (machine : MultiTapePTM k Bool State) {D d : ℕ} {w : List Bool} {a p b q : ℕ}
    (h : clockedOutPort machine D d w a p = some (b, q)) :
    clockedOutCount machine D d w a p =
      clockedCoinCountWithSymbol machine (radix D w.length) w.length a b
        w[queryIndex (k := k) (radix D w.length)
          (a % vertexBound (k := k) (radix D w.length))]? := by
  let B := radix D w.length
  let N := vertexBound (k := k) B
  dsimp only [clockedOutPort] at h
  split_ifs at h with hcond
  cases hg : (coinOutTargetsWithSymbol machine B w.length (a % N)
      w[queryIndex (k := k) B (a % N)]?)[p]? with
  | none => rw [hg] at h; cases h
  | some v =>
    rw [hg, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hb_eq, -⟩ := h
    have hv_mem : v ∈ coinOutTargetsWithSymbol machine B w.length (a % N)
        w[queryIndex (k := k) B (a % N)]? := List.mem_of_getElem? hg
    have hv_lt : v < N :=
      (lt_vertexBound_of_mem_coinOutTargetsWithSymbol machine hv_mem).2
    obtain ⟨hb_div, hb_mod⟩ : b / N = a / N + 1 ∧ b % N = v :=
      (Nat.div_mod_unique (Nat.zero_lt_of_lt hv_lt)).2 ⟨by rw [← hb_eq]; ring, hv_lt⟩
    dsimp only [clockedOutCount, clockedOutCountWithSymbol, clockedCoinCountWithSymbol]
    rw [ite_eq_left hcond, hg, ite_eq_left hb_div.symm, hb_mod]

/-- Exact mutual port inversion on natural-number clocked IDs `a, p, b, q`. -/
theorem clockedOutPort_eq_some_iff (machine : MultiTapePTM k Bool State)
    (D d : ℕ) (w : List Bool) (a p b q : ℕ) :
    clockedOutPort machine D d w a p = some (b, q) ↔
      clockedInPort machine D d w b q = some (a, p) := by
  let n := w.length
  let B := radix D n
  let N := vertexBound (k := k) B
  let T := polyClock d n
  constructor
  · intro hout
    dsimp only [clockedOutPort] at hout
    split_ifs at hout with hcond
    obtain ⟨_, hp_lt, ha_div⟩ := hcond
    have ha_div' : a / N < T := ha_div
    cases hg : (coinOutTargetsWithSymbol machine B n (a % N)
        w[queryIndex (k := k) B (a % N)]?)[p]? with
    | none => rw [hg] at hout; cases hout
    | some v =>
      rw [hg, Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨hb_eq, hq_eq⟩ := hout
      have hv_mem : v ∈ coinOutTargetsWithSymbol machine B n (a % N)
          w[queryIndex (k := k) B (a % N)]? := List.mem_of_getElem? hg
      have hv_lt : v < N := (lt_vertexBound_of_mem_coinOutTargetsWithSymbol machine hv_mem).2
      have hN_pos : 0 < N := Nat.zero_lt_of_lt hv_lt
      have hu_mem : a % N ∈ coinInSources machine B w v :=
        (mem_coinOutTargetsWithSymbol_iff_mem_coinInSources machine B w (a % N) v).mp hv_mem
      have hq_len : (coinInSources machine B w v).idxOf (a % N) <
          (coinInSources machine B w v).length := List.idxOf_lt_length_of_mem hu_mem
      have hq_lt : q < inPortBound machine := by
        rw [← hq_eq]
        exact hq_len.trans_le (length_coinInSources_le machine B w v)
      obtain ⟨hb_div, hb_mod⟩ : b / N = a / N + 1 ∧ b % N = v :=
        (Nat.div_mod_unique hN_pos).2 ⟨by rw [← hb_eq]; ring, hv_lt⟩
      have hb_lt : b < clockedVertexBound (k := k) D d n :=
        (Nat.div_lt_iff_lt_mul (y := T + 1) hN_pos).1 (by omega)
      have hb_cond : b < clockedVertexBound (k := k) D d n ∧ q < inPortBound machine ∧
          0 < b / N := ⟨hb_lt, hq_lt, by rw [hb_div]; exact Nat.succ_pos _⟩
      obtain ⟨hp_len, hp_val⟩ := List.getElem?_eq_some_iff.mp hg
      dsimp only [clockedInPort]
      rw [ite_eq_left hb_cond, hb_mod, ← hq_eq, List.getElem?_eq_getElem hq_len,
        List.getElem_idxOf hq_len]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [hb_div, Nat.add_sub_cancel, Nat.mul_comm]
        exact Nat.div_add_mod a N
      · rw [← hp_val]
        exact (nodup_coinOutTargetsWithSymbol machine B n (a % N) _).idxOf_getElem p hp_len
  · intro hin
    dsimp only [clockedInPort] at hin
    split_ifs at hin with hcond
    obtain ⟨hb_lt, _, hb_pos⟩ := hcond
    have hb_pos' : 0 < b / N := hb_pos
    cases hg : (coinInSources machine B w (b % N))[q]? with
    | none => rw [hg] at hin; cases hin
    | some u =>
      rw [hg, Option.some.injEq, Prod.mk.injEq] at hin
      obtain ⟨ha_eq, hp_eq⟩ := hin
      have hu_mem : u ∈ coinInSources machine B w (b % N) := List.mem_of_getElem? hg
      have hv_mem : b % N ∈ coinOutTargetsWithSymbol machine B n u
          w[queryIndex (k := k) B u]? :=
        (mem_coinOutTargetsWithSymbol_iff_mem_coinInSources machine B w u (b % N)).mpr hu_mem
      have hu_lt : u < N := (lt_vertexBound_of_mem_coinOutTargetsWithSymbol machine hv_mem).1
      have hN_pos : 0 < N := Nat.zero_lt_of_lt hu_lt
      have hp_len : (coinOutTargetsWithSymbol machine B n u
          w[queryIndex (k := k) B u]?).idxOf (b % N) <
          (coinOutTargetsWithSymbol machine B n u w[queryIndex (k := k) B u]?).length :=
        List.idxOf_lt_length_of_mem hv_mem
      have hp_lt : p < 2 := by
        rw [← hp_eq]
        exact hp_len.trans_le (length_coinOutTargetsWithSymbol_le machine B n u _)
      have hb_lt' : b < (T + 1) * N := hb_lt
      have hb_div_lt : b / N < T + 1 :=
        (Nat.div_lt_iff_lt_mul hN_pos).mpr hb_lt'
      obtain ⟨ha_div, ha_mod⟩ : a / N = b / N - 1 ∧ a % N = u :=
        (Nat.div_mod_unique hN_pos).2 ⟨by rw [← ha_eq]; ring, hu_lt⟩
      have ha_div_lt : a / N < T := by omega
      have ha_lt : a < clockedVertexBound (k := k) D d n :=
        (Nat.div_lt_iff_lt_mul (y := T + 1) hN_pos).1 (by omega)
      have ha_cond : a < clockedVertexBound (k := k) D d n ∧ p < 2 ∧ a / N < T :=
        ⟨ha_lt, hp_lt, ha_div_lt⟩
      obtain ⟨hq_len, hq_val⟩ := List.getElem?_eq_some_iff.mp hg
      dsimp only [clockedOutPort]
      rw [ite_eq_left ha_cond, ha_mod, ← hp_eq, List.getElem?_eq_getElem hp_len,
        List.getElem_idxOf hp_len]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · have hsub : b / N - 1 + 1 = b / N := by omega
        rw [ha_div, hsub, Nat.mul_comm]
        exact Nat.div_add_mod b N
      · rw [← hq_val]
        exact (nodup_coinInSources machine B w (b % N)).idxOf_getElem q hq_len

/-! ### Space-budget certificates for pre-queried port and multiplicity evaluation -/

section PortBudgets

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

/-- Evaluate a fixed `PredRecipe` within any common space budget. -/
theorem evalPredRecipe_budget (rec : PredRecipe k State) {B v : α → ℕ}
    (hB : ComputableInSpace B enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => evalPredRecipe rec (B a) (v a)) enc encNat S := by
  cases rec with
  | self => exact hv
  | step t altInput prevOutput =>
    let (qSrc, _, workObs, act) := t
    have hrv := readRegisters_budget (k := k) hB hv
    have hthree : ComputableInSpace (fun _ : α => 3) enc encNat S := budget_const 3 hin
    refine pack_inSpace hB (fun reg => ?_) hin
    cases reg with
    | inputPos =>
      dsimp only [predRegisters]
      cases act.inputTape with
      | neg =>
        cases altInput
        · exact budget_natSucc (hrv .inputPos)
        · exact hrv .inputPos
      | zero => exact hrv .inputPos
      | pos =>
        cases altInput
        · exact budget_natPred (hrv .inputPos)
        · exact hrv .inputPos
    | control => exact budget_const (stateCode (some qSrc)) hin
    | output => exact budget_const prevOutput.val hin
    | head i => exact budget_const (symbolCode (workObs i)) hin
    | left i =>
      dsimp only [predRegisters]
      cases (act.workTapes i).2 with
      | neg => exact budget_natAdd (hrv (.head i)) (budget_natMul hthree (hrv (.left i)))
      | zero => exact hrv (.left i)
      | pos => exact budget_natDiv (hrv (.left i)) hthree
    | right i =>
      dsimp only [predRegisters]
      cases (act.workTapes i).2 with
      | neg => exact budget_natDiv (hrv (.right i)) hthree
      | zero => exact hrv (.right i)
      | pos => exact budget_natAdd (hrv (.head i)) (budget_natMul hthree (hrv (.right i)))

/-- Dispatch on `(predRecipes machine).getD (idx a) .self` and evaluate its predecessor ID in
linear space. -/
theorem evalPredRecipe_getD_inSpace (machine : MultiTapePTM k Bool State)
    {B v idx : α → ℕ}
    (hB : ComputableInSpace B enc encNat fun a => (enc a).length)
    (hv : ComputableInSpace v enc encNat fun a => (enc a).length)
    (hidx : ComputableInSpace idx enc encNat fun a => (enc a).length) :
    ComputableInSpace
      (fun a => evalPredRecipe ((predRecipes machine).getD (idx a) .self) (B a) (v a))
      enc encNat fun a => (enc a).length :=
  dispatch (predRecipes machine) .self
    (fun rec a => evalPredRecipe rec (B a) (v a))
    (fun rec => evalPredRecipe_budget rec hB hv (.refl _)) hidx

/-- Evaluate `coinInSourcesWithSymbols` within a common space budget when the `inPortBound machine`
queried input symbols are supplied by a family of functions `symAt i`. -/
theorem coinInSourcesWithSymbols_ofFn_budget (machine : MultiTapePTM k Bool State)
    {B n v : α → ℕ}
    (symAt : Fin (inPortBound machine) → α → Option Bool)
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hsym : ∀ i, ComputableInSpace (symAt i) enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace
      (fun a => coinInSourcesWithSymbols machine (B a) (n a) (v a)
        (List.ofFn fun i : Fin (inPortBound machine) => symAt i a))
      enc (encList encNat) S := by
  suffices hrec : ∀ (recs : List (PredRecipe k State))
      (f : Fin recs.length → α → Option Bool),
      (∀ i, ComputableInSpace (f i) enc (encOption encBool) S) →
      ComputableInSpace
        (fun a => collectInSources machine (B a) (n a) (v a) recs (List.ofFn fun i => f i a))
        enc (encList encNat) S by
    exact hrec (predRecipes machine) symAt hsym
  intro recs
  induction recs with
  | nil =>
    intro _ _
    exact budget_const [] hin
  | cons rec recs ih =>
    intro f hf
    have hu := evalPredRecipe_budget rec hB hv hin
    have hrest := ih (fun j => f j.succ) (fun j => hf j.succ)
    have hpos := budget_natLt (budget_const 0 hin)
      (coinCountWithSymbol_budget machine hB hn hu hv (hf 0) hin)
    have hins := insertSortedFuel_budget recs.length hu hrest hin
    refine (budget_ite hpos hins hrest).of_enc_eq fun a => ?_
    simp only [List.ofFn_succ, collectInSources, decide_eq_true_eq]
    congr 1
    split_ifs
    · exact (insertSortedFuel_eq recs.length _ _
        (length_collectInSources_le machine (B a) (n a) (v a) recs _)).symm
    · rfl

/-- Space budget for `clockedOutCountWithSymbol`. -/
theorem clockedOutCountWithSymbol_budget (machine : MultiTapePTM k Bool State)
    (D d : ℕ) {n a p : α → ℕ} {symOut : α → Option Bool}
    (hn : ComputableInSpace n enc encNat S)
    (ha : ComputableInSpace a enc encNat S)
    (hp : ComputableInSpace p enc encNat S)
    (hsym : ComputableInSpace symOut enc (encOption encBool) S)
    (hin : (fun x => (enc x).length) ≼ S) :
    ComputableInSpace
      (fun x => clockedOutCountWithSymbol machine D d (n x) (a x) (p x) (symOut x))
      enc encNat S := by
  have htwo : ComputableInSpace (fun _ : α => 2) enc encNat S := budget_const 2 hin
  have hB : ComputableInSpace (fun x => radix D (n x)) enc encNat S :=
    budget_natPow (budget_natAdd hn htwo) hin D
  have hN := vertexBound_budget (k := k) hB hin
  have hT := polyClock_budget d hn hin
  have hM := clockedVertexBound_budget (k := k) D d hn hin
  have hcond := budget_boolAnd (budget_natLt ha hM)
    (budget_boolAnd (budget_natLt hp htwo) (budget_natLt (budget_natDiv ha hN) hT))
  have hu := budget_natMod ha hN
  have houtList := coinOutTargetsWithSymbol_budget machine hB hn hu hsym hin
  have hvOpt := getElem?_budget 2 (fun _ => length_coinOutTargetsWithSymbol_le ..) houtList hp hin
  have hcnt := coinCountWithSymbol_budget machine hB hn hu (budget_optionGetD 0 hvOpt) hsym hin
  refine (budget_ite hcond (budget_ite (budget_optionIsSome hvOpt) hcnt (budget_const 0 hin))
    (budget_const 0 hin)).of_enc_eq fun x => ?_
  clear * -
  simp only [clockedOutCountWithSymbol, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> (try split) <;> simp_all

/-- Space budget for `clockedOutPortWithSymbols`. -/
theorem clockedOutPortWithSymbols_budget (machine : MultiTapePTM k Bool State)
    (D d : ℕ) {n a p : α → ℕ} {symOut : α → Option Bool}
    (inSymAt : Fin (inPortBound machine) → α → Option Bool)
    (hn : ComputableInSpace n enc encNat S)
    (ha : ComputableInSpace a enc encNat S)
    (hp : ComputableInSpace p enc encNat S)
    (hsymOut : ComputableInSpace symOut enc (encOption encBool) S)
    (hinSym : ∀ i, ComputableInSpace (inSymAt i) enc (encOption encBool) S)
    (hin : (fun x => (enc x).length) ≼ S) :
    ComputableInSpace
      (fun x => clockedOutPortWithSymbols machine D d (n x) (a x) (p x) (symOut x)
        (List.ofFn fun i => inSymAt i x))
      enc (encOption (encPair encNat encNat)) S := by
  have htwo : ComputableInSpace (fun _ : α => 2) enc encNat S := budget_const 2 hin
  have hB : ComputableInSpace (fun x => radix D (n x)) enc encNat S :=
    budget_natPow (budget_natAdd hn htwo) hin D
  have hN := vertexBound_budget (k := k) hB hin
  have hT := polyClock_budget d hn hin
  have hM := clockedVertexBound_budget (k := k) D d hn hin
  have hcond := budget_boolAnd (budget_natLt ha hM)
    (budget_boolAnd (budget_natLt hp htwo) (budget_natLt (budget_natDiv ha hN) hT))
  have hu := budget_natMod ha hN
  have houtList := coinOutTargetsWithSymbol_budget machine hB hn hu hsymOut hin
  have hvOpt := getElem?_budget 2 (fun _ => length_coinOutTargetsWithSymbol_le ..) houtList hp hin
  have hvVal := budget_optionGetD 0 hvOpt
  have hinList := coinInSourcesWithSymbols_ofFn_budget machine inSymAt hB hn hvVal hinSym hin
  have hqIdx := idxOf_budget (inPortBound machine) (fun _ => length_coinInSourcesWithSymbols_le ..)
    hinList hu hin
  have hbVal := budget_natAdd (budget_natMul (budget_natSucc (budget_natDiv ha hN)) hN) hvVal
  have hnone : ComputableInSpace (fun _ : α => (none : Option (ℕ × ℕ)))
      enc (encOption (encPair encNat encNat)) S := budget_const none hin
  refine (budget_ite hcond (budget_ite (budget_optionIsSome hvOpt)
    (budget_optionSome (budget_prod hbVal hqIdx)) hnone) hnone).of_enc_eq fun x => ?_
  clear * -
  simp only [clockedOutPortWithSymbols, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> (try split) <;> simp_all

/-- Space budget for `clockedInPortWithSymbols`. -/
theorem clockedInPortWithSymbols_budget (machine : MultiTapePTM k Bool State)
    (D d : ℕ) {n b q : α → ℕ}
    (inSymAt : Fin (inPortBound machine) → α → Option Bool)
    {symPred : α → Option Bool}
    (hn : ComputableInSpace n enc encNat S)
    (hb : ComputableInSpace b enc encNat S)
    (hq : ComputableInSpace q enc encNat S)
    (hinSym : ∀ i, ComputableInSpace (inSymAt i) enc (encOption encBool) S)
    (hsymPred : ComputableInSpace symPred enc (encOption encBool) S)
    (hin : (fun x => (enc x).length) ≼ S) :
    ComputableInSpace
      (fun x => clockedInPortWithSymbols machine D d (n x) (b x) (q x)
        (List.ofFn fun i => inSymAt i x) (symPred x))
      enc (encOption (encPair encNat encNat)) S := by
  have htwo : ComputableInSpace (fun _ : α => 2) enc encNat S := budget_const 2 hin
  have hB : ComputableInSpace (fun x => radix D (n x)) enc encNat S :=
    budget_natPow (budget_natAdd hn htwo) hin D
  have hN := vertexBound_budget (k := k) hB hin
  have hM := clockedVertexBound_budget (k := k) D d hn hin
  have hcond := budget_boolAnd (budget_natLt hb hM)
    (budget_boolAnd (budget_natLt hq (budget_const (inPortBound machine) hin))
      (budget_natLt (budget_const 0 hin) (budget_natDiv hb hN)))
  have hv := budget_natMod hb hN
  have hinList := coinInSourcesWithSymbols_ofFn_budget machine inSymAt hB hn hv hinSym hin
  have huOpt := getElem?_budget (inPortBound machine)
    (fun _ => length_coinInSourcesWithSymbols_le ..) hinList hq hin
  have huVal := budget_optionGetD 0 huOpt
  have houtList := coinOutTargetsWithSymbol_budget machine hB hn huVal hsymPred hin
  have hpIdx := idxOf_budget 2 (fun _ => length_coinOutTargetsWithSymbol_le ..) houtList hv hin
  have haVal := budget_natAdd (budget_natMul (budget_natPred (budget_natDiv hb hN)) hN) huVal
  have hnone : ComputableInSpace (fun _ : α => (none : Option (ℕ × ℕ)))
      enc (encOption (encPair encNat encNat)) S := budget_const none hin
  refine (budget_ite hcond (budget_ite (budget_optionIsSome huOpt)
    (budget_optionSome (budget_prod haVal hpIdx)) hnone) hnone).of_enc_eq fun x => ?_
  clear * -
  simp only [clockedInPortWithSymbols, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> (try split) <;> simp_all

end PortBudgets

end Turing.MultiTapePTM.ConfigurationGraph


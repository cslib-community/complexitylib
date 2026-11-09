/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Equivalence
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option

/-!
# Labelled branches of counting machines

`MultiTapeCTM` specializes the shared multi-tape machine to lists of transition occurrences.
An occurrence is identified by its list index: two equal actions in the list remain two choices.
Deterministic instructions have singleton lists. Configurations, actions and tape operations are
the existing `Turing` ones; no new machine storage or instruction model is introduced.

A branch records occurrence indices and stops at its first halted configuration. In contrast to
the upstream unlabelled step relation, halted configurations have no further labelled steps.
An empty list at a running configuration is stuck, not a rejecting halt.

## Main definitions

* `Turing.MultiTapeCTM`: the list-choice specialization of the common machine.
* `Turing.MultiTapeCTM.lts`: labelled transitions, using the existing `Cslib.LTS` interface.
* `Turing.MultiTapeCTM.runBranch`: replay a list of occurrence indices.
* `Turing.MultiTapeCTM.branches`: first-halting branches of bounded length.
* `Turing.MultiTapeCTM.HaltsWithin`: an all-branches time bound excluding stuck states.
* `Turing.MultiTapeCTM.Nonblocking`: no local view has an empty live transition list.
* `Turing.MultiTapeCTM.acceptCount`, `Turing.MultiTapeCTM.rejectCount`: terminal branch counts.

## Main results

* `Turing.MultiTapeCTM.mem_branches_iff`: the enumeration is exactly the bounded terminal traces.
* `Turing.MultiTapeCTM.HaltsWithin.branches_eq`: larger sufficient clocks preserve every branch.
* `Turing.MultiTapeCTM.exists_branchBound`: finite control and alphabet bound occurrence counts.

This is operational counting semantics, without a claimed polynomial-time verifier or a new
storage/instruction model. Canonical certificates are developed in `MultiTape.Counting.Certificate`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]

The shared machine calculus is adapted from the cslib `crypto` branch; its source and authors are
credited in `MultiTape.Machine` and `MultiTape.Machine.Equivalence`. The counting layer retains
the transition identities forgotten by the relation-based nondeterministic interface.
-/

@[expose] public section

namespace Turing

/-- A shared-core machine with a finite list of transition occurrences at each local view. -/
abbrev MultiTapeCTM (k : ℕ) (Symbol State : Type*) :=
  MultiTapeMachine k Symbol State Empty List

namespace MultiTapeCTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The live transition occurrences, in their specified order. A halted state has no choices. -/
def actions (machine : MultiTapeCTM k Symbol State) (cfg : Cfg k Symbol State input) :
    List (Turing.Action k Symbol State) :=
  match cfg.state with
  | none => []
  | some state =>
    (machine.tr state cfg.inputSymbol cfg.workTapeSymbols Empty.elim).map
      MultiTapeMachine.Action.emptyOracleEquiv

/-- Every running local view has a transition occurrence. This excludes stuck states even on
unreachable configurations; a native `HaltsWithin` hypothesis only needs the reachable ones. -/
def Nonblocking (machine : MultiTapeCTM k Symbol State) : Prop :=
  ∀ state symbol work, machine.tr state symbol work Empty.elim ≠ []

/-- A nonblocking transition table has an occurrence at every running configuration. -/
theorem Nonblocking.actions_ne_nil {machine : MultiTapeCTM k Symbol State}
    (h : machine.Nonblocking) (cfg : Cfg k Symbol State input) (hrun : cfg.state ≠ none) :
    machine.actions cfg ≠ [] := by
  cases hs : cfg.state with
  | none => exact (hrun hs).elim
  | some state => simpa [actions, hs] using h state cfg.inputSymbol cfg.workTapeSymbols

/-- Execute one occurrence. Invalid indices and attempts to step a halted configuration fail. -/
def step? (machine : MultiTapeCTM k Symbol State) (cfg : Cfg k Symbol State input) (index : ℕ) :
    Option (Cfg k Symbol State input) :=
  ((machine.actions cfg)[index]?).map (fun action => action.apply cfg)

/-- The native labelled transition system; labels identify occurrences, not their effects. -/
def lts (machine : MultiTapeCTM k Symbol State) (input : List Symbol) :
    Cslib.LTS (Cfg k Symbol State input) ℕ where
  Tr cfg index next := machine.step? cfg index = some next

/-- Replay actual transitions, with no implicit padding after halting. -/
def runBranch (machine : MultiTapeCTM k Symbol State) :
    Cfg k Symbol State input → List ℕ → Option (Cfg k Symbol State input)
  | cfg, [] => some cfg
  | cfg, index :: rest => do
      let next ← machine.step? cfg index
      machine.runBranch next rest

@[simp]
theorem runBranch_nil (machine : MultiTapeCTM k Symbol State) (cfg : Cfg k Symbol State input) :
    machine.runBranch cfg [] = some cfg := rfl

theorem runBranch_cons (machine : MultiTapeCTM k Symbol State) (cfg : Cfg k Symbol State input)
    (index : ℕ) (rest : List ℕ) :
    machine.runBranch cfg (index :: rest) =
      (machine.step? cfg index).bind (fun next => machine.runBranch next rest) := rfl

/-- Replay is exactly the existing LTS multistep relation, with the occurrence labels retained. -/
theorem runBranch_eq_some_iff (machine : MultiTapeCTM k Symbol State)
    (cfg final : Cfg k Symbol State input) (choices : List ℕ) :
    machine.runBranch cfg choices = some final ↔ (machine.lts input).MTr cfg choices final := by
  induction choices generalizing cfg with
  | nil => simp [runBranch, Cslib.LTS.MTr.nil_iff]
  | cons index rest ih =>
    simp only [runBranch_cons, Option.bind_eq_some_iff, Cslib.LTS.MTr.cons_iff, lts]
    exact exists_congr fun next => and_congr_right fun _ => ih next

theorem actions_of_halted (machine : MultiTapeCTM k Symbol State)
    {cfg : Cfg k Symbol State input} (h : cfg.Halted) : machine.actions cfg = [] := by
  simp [actions, h]

theorem step?_of_halted (machine : MultiTapeCTM k Symbol State)
    {cfg : Cfg k Symbol State input} (h : cfg.Halted) (index : ℕ) :
    machine.step? cfg index = none := by
  simp [step?, machine.actions_of_halted h]

/-- From a halted configuration, only the empty trace can be replayed. -/
theorem runBranch_of_halted (machine : MultiTapeCTM k Symbol State)
    {cfg : Cfg k Symbol State input} (h : cfg.Halted) (choices : List ℕ) :
    machine.runBranch cfg choices = if choices = [] then some cfg else none := by
  cases choices with
  | nil => simp
  | cons index rest => simp [runBranch_cons, machine.step?_of_halted h]

/-- Replaying concatenated traces is sequential replay; a premature halt cannot be crossed. -/
theorem runBranch_append (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (first second : List ℕ) :
    machine.runBranch cfg (first ++ second) =
      (machine.runBranch cfg first).bind (fun next => machine.runBranch next second) := by
  induction first generalizing cfg with
  | nil => rfl
  | cons index rest ih =>
    simp only [List.cons_append, runBranch_cons, ih, Option.bind_assoc]

/-- Enumerate first-halting traces of at most the supplied number of actual transitions. -/
def branches (machine : MultiTapeCTM k Symbol State) :
    ℕ → Cfg k Symbol State input → Finset (List ℕ)
  | fuel, cfg => match cfg.state with
    | none => {[]}
    | some _ => match fuel with
      | 0 => ∅
      | fuel + 1 =>
        Finset.univ.biUnion fun index : Fin (machine.actions cfg).length =>
          (machine.branches fuel ((machine.actions cfg)[index].apply cfg)).image
            (List.cons index.val)

theorem branches_of_halted (machine : MultiTapeCTM k Symbol State)
    {cfg : Cfg k Symbol State input} (h : cfg.Halted) (fuel : ℕ) :
    machine.branches fuel cfg = {[]} := by
  cases fuel <;> simp [branches, h]

/-- A labelled step is exactly an in-range list occurrence, even if other occurrences agree. -/
theorem step?_eq_some_iff (machine : MultiTapeCTM k Symbol State)
    (cfg final : Cfg k Symbol State input) (index : ℕ) :
    machine.step? cfg index = some final ↔
      ∃ h : index < (machine.actions cfg).length,
        (machine.actions cfg)[index].apply cfg = final := by
  simp only [step?, Option.map_eq_some_iff, List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨action, ⟨h, rfl⟩, heq⟩
    exact ⟨h, heq⟩
  · rintro ⟨h, heq⟩
    exact ⟨_, ⟨h, rfl⟩, heq⟩

@[simp]
theorem nil_mem_branches (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) :
    [] ∈ machine.branches fuel cfg ↔ cfg.Halted := by
  cases fuel <;> cases hs : cfg.state <;> simp [branches, hs, Cfg.Halted]

theorem cons_mem_branches (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel index : ℕ) (rest : List ℕ) :
    index :: rest ∈ machine.branches (fuel + 1) cfg ↔
      ∃ next, machine.step? cfg index = some next ∧ rest ∈ machine.branches fuel next := by
  cases hs : cfg.state with
  | none => simp [machine.branches_of_halted hs, machine.step?_of_halted hs]
  | some state =>
    simp [branches, hs, Finset.mem_biUnion, Finset.mem_image, step?_eq_some_iff,
      Fin.exists_iff]

/-- The finite enumeration is exactly the first-halting LTS traces within the given clock. -/
theorem mem_branches_iff (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) (choices : List ℕ) :
    choices ∈ machine.branches fuel cfg ↔ choices.length ≤ fuel ∧
      ∃ final, machine.runBranch cfg choices = some final ∧ final.Halted := by
  induction fuel generalizing cfg choices with
  | zero =>
    cases choices with
    | nil => simp
    | cons index rest => cases hs : cfg.state <;> simp [branches, hs]
  | succ fuel ih =>
    cases choices with
    | nil => simp
    | cons index rest =>
      simp only [cons_mem_branches, ih, List.length_cons, Nat.add_le_add_iff_right,
        runBranch_cons, Option.bind_eq_some_iff]
      aesop

/-- Every branch halts within this many actual transitions. Running configurations must have
at least one occurrence, so a stuck branch cannot make a time bound hold vacuously. -/
inductive HaltsWithin (machine : MultiTapeCTM k Symbol State) :
    ℕ → Cfg k Symbol State input → Prop
  | halt {fuel cfg} (halted : cfg.Halted) : HaltsWithin machine fuel cfg
  | step {fuel cfg} (nonempty : machine.actions cfg ≠ [])
      (next : ∀ index : Fin (machine.actions cfg).length,
        HaltsWithin machine fuel ((machine.actions cfg)[index].apply cfg)) :
      HaltsWithin machine (fuel + 1) cfg

/-- Enlarging a sufficient clock does not add transitions after a branch halts. -/
theorem HaltsWithin.mono {machine : MultiTapeCTM k Symbol State}
    {cfg : Cfg k Symbol State input} {fuel larger : ℕ}
    (h : machine.HaltsWithin fuel cfg) (hle : fuel ≤ larger) :
    machine.HaltsWithin larger cfg := by
  induction h generalizing larger with
  | halt halted => exact .halt halted
  | @step fuel cfg nonempty next ih =>
    obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [show fuel + 1 + rest = (fuel + rest) + 1 by lia]
    exact .step nonempty (fun index => ih index (Nat.le_add_right fuel rest))

/-- A successful replay cannot pass the all-branches halting bound. -/
theorem HaltsWithin.length_le {machine : MultiTapeCTM k Symbol State}
    {cfg final : Cfg k Symbol State input} {fuel : ℕ} (h : machine.HaltsWithin fuel cfg)
    {choices : List ℕ} (hrun : machine.runBranch cfg choices = some final) :
    choices.length ≤ fuel := by
  induction h generalizing choices final with
  | halt halted =>
    cases choices with
    | nil => simp
    | cons index rest => simp [runBranch_cons, machine.step?_of_halted halted] at hrun
  | @step fuel cfg nonempty next ih =>
    cases choices with
    | nil => simp
    | cons index rest =>
      obtain ⟨nextCfg, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hrun
      obtain ⟨hi, rfl⟩ := (machine.step?_eq_some_iff cfg nextCfg index).mp hstep
      simpa only [List.length_cons, Nat.add_le_add_iff_right] using ih ⟨index, hi⟩ hrest

/-- A sufficient clock can be increased without changing any terminal branch multiplicity. -/
theorem HaltsWithin.branches_eq {machine : MultiTapeCTM k Symbol State}
    {cfg : Cfg k Symbol State input} {fuel larger : ℕ}
    (h : machine.HaltsWithin fuel cfg) (hle : fuel ≤ larger) :
    machine.branches larger cfg = machine.branches fuel cfg := by
  ext choices
  simp only [mem_branches_iff]
  constructor
  · rintro ⟨_, final, hrun, hhalt⟩
    exact ⟨h.length_le hrun, final, hrun, hhalt⟩
  · rintro ⟨hlen, hrun⟩
    exact ⟨hlen.trans hle, hrun⟩

/-- The no-stuck condition guarantees at least one terminal branch. -/
theorem HaltsWithin.branches_nonempty {machine : MultiTapeCTM k Symbol State}
    {cfg : Cfg k Symbol State input} {fuel : ℕ} (h : machine.HaltsWithin fuel cfg) :
    (machine.branches fuel cfg).Nonempty := by
  induction h with
  | halt halted => simp [machine.branches_of_halted halted]
  | @step fuel cfg nonempty next ih =>
    have hlen : 0 < (machine.actions cfg).length := List.length_pos_iff.mpr nonempty
    obtain ⟨rest, hrest⟩ := ih ⟨0, hlen⟩
    refine ⟨0 :: rest, (machine.cons_mem_branches cfg fuel 0 rest).mpr ⟨_, ?_, hrest⟩⟩
    exact (machine.step?_eq_some_iff cfg _ 0).mpr ⟨hlen, rfl⟩

/-- Count terminal branches whose output satisfies a Boolean verdict. A failed replay is never
counted, even for the complementary verdict. -/
def branchCount (machine : MultiTapeCTM k Symbol State) (verdict : List Symbol → Bool)
    (fuel : ℕ) (cfg : Cfg k Symbol State input) : ℕ :=
  ((machine.branches fuel cfg).filter fun choices =>
    (machine.runBranch cfg choices).any (fun final => verdict final.output)).card

/-- Acceptance and rejection partition the terminal branches, without counting stuck states. -/
theorem branchCount_add_not (machine : MultiTapeCTM k Symbol State)
    (verdict : List Symbol → Bool) (fuel : ℕ) (cfg : Cfg k Symbol State input) :
    machine.branchCount verdict fuel cfg + machine.branchCount (fun out => !verdict out) fuel cfg =
      (machine.branches fuel cfg).card := by
  unfold branchCount
  have hfilter :
      (machine.branches fuel cfg).filter (fun choices =>
        (machine.runBranch cfg choices).any (fun final => !verdict final.output)) =
      (machine.branches fuel cfg).filter (fun choices =>
        ¬(machine.runBranch cfg choices).any (fun final => verdict final.output)) := by
    apply Finset.filter_congr
    intro choices hchoices
    obtain ⟨_, final, hrun, _⟩ := (machine.mem_branches_iff cfg fuel choices).mp hchoices
    simp [hrun]
  rw [hfilter]
  exact Finset.card_filter_add_card_filter_not _

/-- The accepting terminal count uses the standard one-bit `true` output convention. -/
def acceptCount (machine : MultiTapeCTM k Bool State)
    {input : List Bool} (fuel : ℕ) (cfg : Cfg k Bool State input) : ℕ :=
  machine.branchCount (· == [true]) fuel cfg

/-- Every terminal output other than the one-bit `true` word rejects. Invalid or stuck traces
are not rejecting branches. -/
def rejectCount (machine : MultiTapeCTM k Bool State)
    {input : List Bool} (fuel : ℕ) (cfg : Cfg k Bool State input) : ℕ :=
  machine.branchCount (fun out => !(out == [true])) fuel cfg

theorem acceptCount_add_rejectCount (machine : MultiTapeCTM k Bool State)
    {input : List Bool} (fuel : ℕ) (cfg : Cfg k Bool State input) :
    machine.acceptCount fuel cfg + machine.rejectCount fuel cfg =
      (machine.branches fuel cfg).card :=
  machine.branchCount_add_not _ _ _

theorem HaltsWithin.branchCount_eq {machine : MultiTapeCTM k Symbol State}
    {cfg : Cfg k Symbol State input} {fuel larger : ℕ}
    (h : machine.HaltsWithin fuel cfg) (hle : fuel ≤ larger) (verdict : List Symbol → Bool) :
    machine.branchCount verdict larger cfg = machine.branchCount verdict fuel cfg := by
  simp only [branchCount, h.branches_eq hle]

/-- Finite control and a fixed finite alphabet give one fixed bound on transition occurrences.
Repeated actions are counted separately; their multiplicity is not bounded by `Nat.card Action`.
-/
theorem exists_branchBound (machine : MultiTapeCTM k Symbol State)
    [Finite State] [Finite Symbol] :
    ∃ bound : ℕ, ∀ (input : List Symbol) (cfg : Cfg k Symbol State input),
      (machine.actions cfg).length ≤ bound := by
  classical
  let := Fintype.ofFinite State
  let := Fintype.ofFinite Symbol
  let size (view : State × Option Symbol × (Fin k → Option Symbol)) :=
    (machine.tr view.1 view.2.1 view.2.2 Empty.elim).length
  refine ⟨Finset.univ.sup size, fun input cfg => ?_⟩
  cases hs : cfg.state with
  | none => simp [actions, hs]
  | some state =>
    simpa only [actions, hs, List.length_map] using
      (Finset.le_sup (f := size) (Finset.mem_univ (state, cfg.inputSymbol, cfg.workTapeSymbols)))

end MultiTapeCTM

end Turing

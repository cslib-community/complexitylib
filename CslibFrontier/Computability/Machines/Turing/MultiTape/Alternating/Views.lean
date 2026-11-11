/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Reachability

/-!
# Alternating acceptance on views

A view (`Turing.FiniteCfg`) of a configuration keeps everything except the input and the output
(`Turing.MultiTapeNTM.ViewRep`), and the views a running view steps to
(`Turing.MultiTapeNTM.viewSucc`) are, for the nondeterministic machine of the table of an
alternating machine, the views after its two moves (`Turing.MultiTapeATM.mem_viewSucc_iff`).
Acceptance within `n` moves therefore transfers to views
(`Turing.MultiTapeATM.ViewAcceptsWithin`, `Turing.MultiTapeATM.viewAcceptsWithin_iff`), so a
machine accepts exactly when its initial view accepts within some number of moves
(`Turing.MultiTapeATM.accepts_iff_exists_viewAcceptsWithin`).

Acceptance (`Turing.MultiTapeATM.Accepts`) is the least fixed point of the labelling: it asks for
acceptance within some finite number of moves, so a configuration whose acceptance would rely on an
infinite branch does not accept, as for Chandra, Kozen and Stockmeyer
[Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]. On a list of views closed
under successors, the views accepting within `n` moves grow with `n` and can grow strictly for at
most as many steps as the list has entries; once they stop growing they never grow again. So a view
of the list that accepts within some number of moves accepts within as many moves as the list has
entries (`Turing.MultiTapeATM.viewAcceptsWithin_length`). This finite stabilization is what lets a
bounded number of rounds of marking compute the least fixed point exactly.

## Main definitions

* `Turing.MultiTapeATM.ViewAcceptsWithin`: acceptance of a view within a number of moves.

## Main results

* `Turing.MultiTapeATM.tr_toNTM_iff_action`: the transitions of the nondeterministic machine of
  the table are the actions of the two moves.
* `Turing.MultiTapeATM.mem_viewSucc_iff`: the successors of a running view are its views after the
  two moves.
* `Turing.MultiTapeATM.viewAcceptsWithin_iff`: views accept within `n` moves as the configurations
  they represent do.
* `Turing.MultiTapeATM.accepts_iff_exists_viewAcceptsWithin`: acceptance through views.
* `Turing.MultiTapeATM.viewAcceptsWithin_length`: on a closed list of views, acceptance within
  some number of moves is acceptance within as many moves as the list has entries.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

public section

open Cslib.Turing

namespace Turing.MultiTapeATM

variable {k : ℕ} {State : Type} (atm : MultiTapeATM k Bool State)

/-- The transitions of the nondeterministic machine of the table are the actions of the two
moves. -/
theorem tr_toNTM_iff_action {q : State} {symbol : Option Bool} {work : Fin k → Option Bool}
    {act : Turing.Action k Bool State} :
    atm.toPTM.toNTM.Tr q symbol work act ↔ ∃ b, act = atm.action q symbol work b := by
  simp only [MultiTapePTM.toNTM, MultiTapeMachine.toNTM, MultiTapePTM.branches, Set.mem_range,
    action]
  exact exists_congr fun b => by rw [Equiv.eq_symm_apply, eq_comm]

/-- **Acceptance of a view within `n` moves**, as for configurations
(`Turing.MultiTapeATM.AcceptsWithin`): within `0` moves a halted view with output `[true]`, and
within `n + 1` moves a halted view with output `[true]` or a running view one (existential state)
or all (universal state) of whose successors accept within `n` moves. -/
def ViewAcceptsWithin [Finite State] : ℕ → FiniteCfg k Bool State → Prop
  | 0, v => v.state = none ∧ v.output = [true]
  | n + 1, v => match v.state with
    | none => v.output = [true]
    | some q => if atm.universal q then ∀ w ∈ atm.toPTM.toNTM.viewSucc v, ViewAcceptsWithin n w
      else ∃ w ∈ atm.toPTM.toNTM.viewSucc v, ViewAcceptsWithin n w

variable [Finite State] {atm}

/-- **The successors of a running view are its views after the two moves.** -/
theorem mem_viewSucc_iff {v w : FiniteCfg k Bool State} {q : State} (hq : v.state = some q) :
    w ∈ atm.toPTM.toNTM.viewSucc v ↔
      ∃ b, w = (v.step (atm.action q v.inputSymbol v.workTapeSymbols b)).summarizeOutput := by
  simp only [MultiTapeNTM.viewSucc, hq, List.mem_map, MultiTapeNTM.mem_actions,
    tr_toNTM_iff_action]
  constructor
  · rintro ⟨act, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨b, rfl⟩, rfl⟩

/-- A running view has a successor. -/
theorem viewSucc_ne_nil {v : FiniteCfg k Bool State} {q : State} (hq : v.state = some q) :
    atm.toPTM.toNTM.viewSucc v ≠ [] :=
  List.ne_nil_of_mem ((mem_viewSucc_iff hq).mpr ⟨false, rfl⟩)

/-- Within `0` moves, only a halted view with output `[true]` accepts. -/
theorem viewAcceptsWithin_zero_iff {v : FiniteCfg k Bool State} :
    atm.ViewAcceptsWithin 0 v ↔ v.state = none ∧ v.output = [true] := Iff.rfl

/-- A halted view accepts exactly when its output is `[true]`. -/
theorem viewAcceptsWithin_of_halted {n : ℕ} {v : FiniteCfg k Bool State} (h : v.state = none) :
    atm.ViewAcceptsWithin n v ↔ v.output = [true] := by
  cases n with
  | zero => simp [ViewAcceptsWithin, h]
  | succ n => simp [ViewAcceptsWithin, h]

/-- A universal view accepts within `n + 1` moves when all its successors accept within `n`. -/
theorem viewAcceptsWithin_succ_of_universal {n : ℕ} {v : FiniteCfg k Bool State} {q : State}
    (h : v.state = some q) (hq : atm.universal q = true) :
    atm.ViewAcceptsWithin (n + 1) v ↔
      ∀ w ∈ atm.toPTM.toNTM.viewSucc v, atm.ViewAcceptsWithin n w := by
  simp [ViewAcceptsWithin, h, hq]

/-- An existential view accepts within `n + 1` moves when one of its successors accepts within
`n`. -/
theorem viewAcceptsWithin_succ_of_existential {n : ℕ} {v : FiniteCfg k Bool State} {q : State}
    (h : v.state = some q) (hq : atm.universal q = false) :
    atm.ViewAcceptsWithin (n + 1) v ↔
      ∃ w ∈ atm.toPTM.toNTM.viewSucc v, atm.ViewAcceptsWithin n w := by
  simp [ViewAcceptsWithin, h, hq]

/-- A running view does not accept within `0` moves. -/
theorem not_viewAcceptsWithin_zero {v : FiniteCfg k Bool State} {q : State}
    (h : v.state = some q) : ¬atm.ViewAcceptsWithin 0 v := by
  simp [ViewAcceptsWithin, h]

/-- **Views accept as the configurations they represent do.** -/
theorem viewAcceptsWithin_iff {input : List Bool} {n : ℕ} {v : FiniteCfg k Bool State}
    {c : Cfg k Bool State input} (h : MultiTapeNTM.ViewRep v c) :
    atm.ViewAcceptsWithin n v ↔ atm.AcceptsWithin n c := by
  induction n generalizing v c with
  | zero =>
    rw [viewAcceptsWithin_zero_iff, AcceptsWithin, h.state, h.output,
      MultiTapeNTM.outputClass_eq_true_iff]
  | succ n ih =>
    rcases hs : c.state with _ | q
    · rw [viewAcceptsWithin_of_halted (h.state.trans hs), atm.acceptsWithin_of_halted hs,
        h.output, MultiTapeNTM.outputClass_eq_true_iff]
    · have hv : v.state = some q := h.state.trans hs
      obtain ⟨hin, hwork⟩ := h.symbols
      have hrep (b : Bool) : MultiTapeNTM.ViewRep
          (v.step (atm.action q v.inputSymbol v.workTapeSymbols b)).summarizeOutput
          (atm.next b c) := by
        rw [atm.next_of_state hs, hin, hwork]
        exact h.step _
      cases hq : atm.universal q
      · rw [viewAcceptsWithin_succ_of_existential hv hq,
          atm.acceptsWithin_succ_of_existential hs hq]
        constructor
        · rintro ⟨w, hw, hacc⟩
          obtain ⟨b, rfl⟩ := (mem_viewSucc_iff hv).mp hw
          exact ⟨b, (ih (hrep b)).mp hacc⟩
        · rintro ⟨b, hacc⟩
          exact ⟨_, (mem_viewSucc_iff hv).mpr ⟨b, rfl⟩, (ih (hrep b)).mpr hacc⟩
      · rw [viewAcceptsWithin_succ_of_universal hv hq,
          atm.acceptsWithin_succ_of_universal hs hq]
        constructor
        · intro hall b
          exact (ih (hrep b)).mp (hall _ ((mem_viewSucc_iff hv).mpr ⟨b, rfl⟩))
        · intro hall w hw
          obtain ⟨b, rfl⟩ := (mem_viewSucc_iff hv).mp hw
          exact (ih (hrep b)).mpr (hall b)

/-- **Acceptance through views**: the machine accepts exactly when its initial view accepts
within some number of moves. -/
theorem accepts_iff_exists_viewAcceptsWithin {input : List Bool} :
    atm.Accepts input ↔
      ∃ n, atm.ViewAcceptsWithin n (atm.toPTM.toNTM.initView input) :=
  exists_congr fun _ => (viewAcceptsWithin_iff (MultiTapeNTM.viewRep_init input)).symm

/-- Acceptance within `n` moves is acceptance within more. -/
theorem ViewAcceptsWithin.mono {n n' : ℕ} {v : FiniteCfg k Bool State}
    (h : atm.ViewAcceptsWithin n v) (hn : n ≤ n') : atm.ViewAcceptsWithin n' v := by
  induction n generalizing n' v with
  | zero =>
    obtain ⟨hhalt, hout⟩ := h
    exact (viewAcceptsWithin_of_halted hhalt).mpr hout
  | succ n ih =>
    obtain ⟨n', rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    rcases hs : v.state with _ | q
    · exact (viewAcceptsWithin_of_halted hs).mpr ((viewAcceptsWithin_of_halted hs).mp h)
    · cases hq : atm.universal q
      · obtain ⟨w, hw, hacc⟩ := (viewAcceptsWithin_succ_of_existential hs hq).mp h
        exact (viewAcceptsWithin_succ_of_existential hs hq).mpr ⟨w, hw, ih hacc (by omega)⟩
      · have hall := (viewAcceptsWithin_succ_of_universal hs hq).mp h
        exact (viewAcceptsWithin_succ_of_universal hs hq).mpr fun w hw =>
          ih (hall w hw) (by omega)

/-- On a list of views closed under successors, acceptance within `n + 1` moves depends only on
acceptance within `n` moves on the list. -/
theorem viewAcceptsWithin_succ_congr {found : List (FiniteCfg k Bool State)}
    (hclosed : ∀ v ∈ found, ∀ w ∈ atm.toPTM.toNTM.viewSucc v, w ∈ found) {n m : ℕ}
    (h : ∀ w ∈ found, (atm.ViewAcceptsWithin n w ↔ atm.ViewAcceptsWithin m w))
    {v : FiniteCfg k Bool State} (hv : v ∈ found) :
    atm.ViewAcceptsWithin (n + 1) v ↔ atm.ViewAcceptsWithin (m + 1) v := by
  rcases hs : v.state with _ | q
  · rw [viewAcceptsWithin_of_halted hs, viewAcceptsWithin_of_halted hs]
  · cases hq : atm.universal q
    · rw [viewAcceptsWithin_succ_of_existential hs hq, viewAcceptsWithin_succ_of_existential hs hq]
      exact exists_congr fun w => and_congr_right fun hw => h w (hclosed v hv w hw)
    · rw [viewAcceptsWithin_succ_of_universal hs hq, viewAcceptsWithin_succ_of_universal hs hq]
      exact forall_congr' fun w => forall_congr' fun hw => h w (hclosed v hv w hw)

/-- **Stabilization.** On a list of views closed under successors, a view of the list accepting
within some number of moves accepts within as many moves as the list has entries. -/
theorem viewAcceptsWithin_length {found : List (FiniteCfg k Bool State)}
    (hclosed : ∀ v ∈ found, ∀ w ∈ atm.toPTM.toNTM.viewSucc v, w ∈ found)
    {v : FiniteCfg k Bool State} (hv : v ∈ found) {n : ℕ} (h : atm.ViewAcceptsWithin n v) :
    atm.ViewAcceptsWithin found.length v := by
  classical
  -- the views of the list accepting within `i` moves
  let S : ℕ → Finset (FiniteCfg k Bool State) := fun i =>
    found.toFinset.filter fun w => atm.ViewAcceptsWithin i w
  have hmono {i j : ℕ} (hij : i ≤ j) : S i ⊆ S j := fun w hw => by
    simp only [S, Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, hw.2.mono hij⟩
  -- once two consecutive sets agree, all later sets agree
  have hstable {i : ℕ} (heq : S i = S (i + 1)) (j : ℕ) : S (i + j) = S i := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hiff (w) (hw : w ∈ found) :
          atm.ViewAcceptsWithin (i + j) w ↔ atm.ViewAcceptsWithin i w := by
        have := congrArg (w ∈ ·) ih
        simpa [S, hw] using this
      have hiff' (w) (hw : w ∈ found) :
          atm.ViewAcceptsWithin (i + j + 1) w ↔ atm.ViewAcceptsWithin (i + 1) w :=
        viewAcceptsWithin_succ_congr hclosed hiff hw
      rw [heq]
      ext w
      simp only [S, Finset.mem_filter, List.mem_toFinset]
      exact and_congr_right fun hw => hiff' w hw
  -- the sets cannot grow strictly for more steps than the list has entries
  have hfix : ∃ i ≤ found.length, S i = S (i + 1) := by
    by_contra hne
    push Not at hne
    have hgrow (i : ℕ) (hi : i ≤ found.length + 1) : i ≤ (S i).card := by
      induction i with
      | zero => exact Nat.zero_le _
      | succ i ih =>
        have hss : S i ⊂ S (i + 1) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hmono (Nat.le_succ i), hne i (by omega)⟩
        have := Finset.card_lt_card hss
        have := ih (by omega)
        omega
    have h1 := hgrow (found.length + 1) le_rfl
    have h2 : (S (found.length + 1)).card ≤ found.toFinset.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h3 := List.toFinset_card_le found
    omega
  obtain ⟨i, hi, heq⟩ := hfix
  have hlen : S found.length = S i := by
    simpa only [Nat.add_sub_cancel' hi] using hstable heq (found.length - i)
  have hmem : v ∈ S (max n found.length) := by
    simp only [S, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hv, h.mono (le_max_left _ _)⟩
  have hmax : S (max n found.length) = S i := by
    simpa only [Nat.add_sub_cancel' (hi.trans (le_max_right n found.length))] using
      hstable heq (max n found.length - i)
  rw [hmax, ← hlen] at hmem
  simp only [S, Finset.mem_filter] at hmem
  exact hmem.2

end Turing.MultiTapeATM

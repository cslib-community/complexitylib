/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DeterministicPhase
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StateSimulation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameHeader

/-!
# Native word games with an alternating terminal continuation

The controller keeps the game header on one work tape. A blank header enters an actual
alternating terminal machine. Otherwise the indicated player writes a move into the second
cell and a deterministic native round updates the stored position. All other tapes, cursors,
and the existing output are retained at every handoff.

The two controller steps and each native round are charged by a decreasing potential; the
terminal continuation has its own all-branch time and acceptance certificate.
-/

public section

namespace Turing.MultiTapeATM.WordGameLeaf

/-- Finite control for dispatch, a chosen player, the round, and the terminal continuation. -/
inductive State (R L : Type) where
  | dispatch
  | choose (player : Bool)
  | round (state : R)
  | leaf (state : L)

instance {R L : Type} [Finite R] [Finite L] : Finite (State R L) :=
  Finite.of_injective (fun s : State R L => match s with
    | .dispatch => (Sum.inl none : Option Bool ⊕ R ⊕ L)
    | .choose player => .inl (some player)
    | .round state => .inr (.inl state)
    | .leaf state => .inr (.inr state)) (by
      rintro (_ | _ | _ | _) (_ | _ | _ | _) h <;> simp_all)

variable {k : ℕ} {R L : Type}

private def controlAction (control : Fin k) (write : Option (Option Bool)) (move : SignType)
    (state : State R L) : Turing.Action k Bool (State R L) where
  inputTape := 0
  workTapes := Function.update (fun _ => (none, 0)) control (write, move)
  output := none
  state := some state

private noncomputable def transition (round : MultiTapeTM k Bool R)
    (leaf : MultiTapeATM k Bool L) (control : Fin k) (bit : Bool) :
    State R L → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool (State R L)
  | .dispatch, _, work => match work control with
    | none => controlAction control none 0 (.leaf leaf.toPTM.initial)
    | some player => controlAction control none 1 (.choose player)
  | .choose _, _, _ => controlAction control (some (some bit)) (-1) (.round round.q₀)
  | .round state, input, work =>
    let action := round.tr state input work
    { action with state := some (action.state.elim .dispatch .round) }
  | .leaf state, input, work =>
    let action := leaf.action state input work bit
    { action with state := action.state.map .leaf }

private def universal (leaf : MultiTapeATM k Bool L) : State R L → Bool
  | .choose player => player
  | .leaf state => leaf.universal state
  | _ => false

/-- Run native rounds until a blank header transfers to the actual terminal machine. -/
noncomputable def machine (round : MultiTapeTM k Bool R) (leaf : MultiTapeATM k Bool L)
    (control : Fin k) : MultiTapeATM k Bool (State R L) :=
  ofTMs (fun bit => MultiTapeTM.ofTr .dispatch (transition round leaf control bit))
    (universal leaf)

/-- The native game starts by dispatching the stored control header. -/
theorem machine_initial (round : MultiTapeTM k Bool R) (leaf : MultiTapeATM k Bool L)
    (control : Fin k) : (machine round leaf control).toPTM.initial = .dispatch := by rfl

/-- Install only the control word and head, preserving all ambient storage and output. -/
@[expose] def config {S : Type} {input : List Bool} (control : Fin k) (state : Option S)
    (word : List Bool) (position : ℕ) (storage : Cfg k Bool Unit input) : Cfg k Bool S input :=
  ⟨state, storage.inputPos, Function.update storage.workTapes control (tapeOfList word),
    Function.update storage.workTapePos control (position : ℤ), storage.output⟩

variable {input : List Bool} (round : MultiTapeTM k Bool R) (leaf : MultiTapeATM k Bool L)
  (control : Fin k)

/-- A blank control word starts the terminal continuation in one native step. -/
theorem next_terminal (bit : Bool) (storage : Cfg k Bool Unit input) :
    (machine round leaf control).next bit (config control (some .dispatch) [] 0 storage) =
      (config control (some leaf.toPTM.initial) [] 0 storage).mapState (Option.map State.leaf) := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (config control (some (State.dispatch (R := R) (L := L))) [] 0
      storage).workTapeSymbols control = none := by
    simp [Cfg.workTapeSymbols, config]
  simp only [MultiTapeTM.tr_ofTr, transition, hread, controlAction]
  refine Cfg.ext rfl (by simp [config, moveInputPos_zero]) ?_ ?_
    (by simp [config, Cfg.mapState]) <;>
    funext i <;> by_cases hi : i = control <;> simp [config, Cfg.mapState, hi]

/-- Read the player and move to the chosen-move cell in one native step. -/
theorem next_dispatch (bit player : Bool) (storage : Cfg k Bool Unit input) :
    (machine round leaf control).next bit
        (config control (some .dispatch) [player, false] 0 storage) =
      config control (some (.choose player)) [player, false] 1 storage := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hread : (config control (some (State.dispatch (R := R) (L := L))) [player, false] 0
      storage).workTapeSymbols control = some player := by
    simp [Cfg.workTapeSymbols, config, tapeOfList_zero]
  simp only [MultiTapeTM.tr_ofTr, transition, hread, controlAction]
  refine Cfg.ext rfl (by simp [config, moveInputPos_zero]) ?_ ?_ (by simp [config]) <;>
    funext i <;> by_cases hi : i = control <;> simp [config, hi]

/-- Embed a running deterministic round; its halt returns to live dispatch. -/
@[expose] def liftRound (c : Cfg k Bool R input) : Cfg k Bool (State R L) input :=
  c.mapState fun state => some (state.elim .dispatch .round)

/-- Write the alternating choice and enter the round with the control head rewound. -/
theorem next_choose (bit player : Bool) (storage : Cfg k Bool Unit input) :
    (machine round leaf control).next bit
        (config control (some (.choose player)) [player, false] 1 storage) =
      liftRound (config control (some round.q₀) [player, bit] 0 storage) := by
  have hwrite : Function.update (tapeOfList [player, false]) 1 (some bit) =
      tapeOfList [player, bit] := by
    simpa using (tapeOfList_set [player, false] (i := 1) (by simp) bit).symm
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl]
  simp only [MultiTapeTM.tr_ofTr, transition, controlAction]
  refine Cfg.ext rfl (by simp [config, liftRound, Cfg.mapState, moveInputPos_zero]) ?_ ?_
    (by simp [config, liftRound, Cfg.mapState]) <;>
    funext i <;> by_cases hi : i = control <;>
      simp [config, liftRound, Cfg.mapState, hi, hwrite]

/-- Every live round transition is deterministic and preserves the complete storage snapshot. -/
theorem next_liftRound (bit : Bool) {c : Cfg k Bool R input} (h : c.state ≠ none) :
    (machine round leaf control).next bit (liftRound c) = liftRound (round.step c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (liftRound (L := L) c).state = some (State.round q) := by
    simp [liftRound, Cfg.mapState, hq]
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state hstate, MultiTapeTM.step_of_state hq]
  simp only [MultiTapeTM.tr_ofTr, transition]
  rfl

/-- The terminal machine is embedded step for step, including its alternating player. -/
noncomputable def leafSimulation : StateSimulation leaf (machine round leaf control) where
  stateMap := .leaf
  universal_eq _ := rfl
  next_eq c bit := by
    cases hs : c.state with
    | none =>
      rw [next_of_halted _ (by simp [Cfg.mapState, hs]), next_of_halted _ hs]
    | some q =>
      have hstate : (c.mapState (Option.map (State.leaf (R := R)))).state =
          some (State.leaf q) := by simp [Cfg.mapState, hs]
      rw [machine, next_ofTMs, MultiTapeTM.step_of_state hstate, next_of_state _ hs]
      simp only [MultiTapeTM.tr_ofTr, transition]
      rfl

/-- A certified native round gives its first live handoff within the same clock. -/
theorem exists_round_phase {c : Cfg k Bool R input} {t : ℕ}
    (ht : (round.runFrom c t).state = none) :
    ∃ τ ≤ t,
      (∀ j < τ, ∀ bit, (machine round leaf control).next bit
        (((machine round leaf control).next false)^[j] (liftRound c)) =
          ((machine round leaf control).next false)^[j + 1] (liftRound c)) ∧
      (∀ j ≤ τ, (((machine round leaf control).next false)^[j]
        (liftRound c)).state ≠ none) ∧
      ((machine round leaf control).next false)^[τ] (liftRound c) =
        liftRound (round.runFrom c t) :=
  exists_deterministic_phase (machine round leaf control) liftRound
    (fun bit c h => next_liftRound round leaf control bit h)
    (fun _ => by simp [liftRound]) ht

/-- Native round and terminal clocks paid by a decreasing potential give both all-branch
halting and the game value. The storage may retain arbitrarily long words on every other tape;
only the supplied physical runs, including the two controller steps, enter the clock. -/
theorem spec_of_potential {Position : Type} (player : Position → Option Bool)
    (next : Position → Bool → Position) (storage : Position → Cfg k Bool Unit input)
    (valid : Position → Prop) (value : Position → Prop) (potential : Position → ℕ)
    (hterminal : ∀ a, valid a → player a = none → ∃ t,
      leaf.HaltsWithin t (config control (some leaf.toPTM.initial) [] 0 (storage a)) ∧
      (leaf.AcceptsWithin t (config control (some leaf.toPTM.initial) [] 0 (storage a)) ↔
        value a) ∧ t + 1 ≤ potential a)
    (hround : ∀ a, valid a → ∀ p, player a = some p → ∀ bit, ∃ t,
      round.runFrom (config control (some round.q₀) [p, bit] 0 (storage a)) t =
        config control none (wordGameHeader (player (next a bit))) 0 (storage (next a bit)) ∧
      valid (next a bit) ∧ t + 2 + potential (next a bit) ≤ potential a)
    (hvalue : ∀ a, valid a → ∀ p, player a = some p →
      (value a ↔ if p then ∀ bit, value (next a bit) else ∃ bit, value (next a bit)))
    {a : Position} (ha : valid a) {n : ℕ} (hn : potential a ≤ n) :
    (machine round leaf control).HaltsWithin n
        (config control (some .dispatch) (wordGameHeader (player a)) 0 (storage a)) ∧
      ((machine round leaf control).AcceptsWithin n
        (config control (some .dispatch) (wordGameHeader (player a)) 0 (storage a)) ↔ value a) := by
  have h (N : ℕ) : ∀ a, potential a = N → valid a → ∀ n, potential a ≤ n →
      (machine round leaf control).HaltsWithin n
          (config control (some .dispatch) (wordGameHeader (player a)) 0 (storage a)) ∧
        ((machine round leaf control).AcceptsWithin n
          (config control (some .dispatch) (wordGameHeader (player a)) 0 (storage a)) ↔
            value a) := by
    induction N using Nat.strong_induction_on with
    | ind N ih =>
      intro a hN ha n hn
      cases hp : player a with
      | none =>
        obtain ⟨t, ht, hv, hcost⟩ := hterminal a ha hp
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have htm : t ≤ m := by omega
        simp only [wordGameHeader]
        constructor
        · rw [haltsWithin_succ]
          intro bit
          rw [next_terminal]
          exact ((leafSimulation round leaf control).haltsWithin_iff m
            (config control (some leaf.toPTM.initial) [] 0 (storage a))).mpr (ht.mono htm)
        · rw [acceptsWithin_succ_of_next_eq (next_terminal round leaf control · (storage a))]
          exact ((leafSimulation round leaf control).acceptsWithin_iff m
            (config control (some leaf.toPTM.initial) [] 0 (storage a))).trans
              (Iff.trans ⟨fun h => h.of_halted_stepCoins ht, fun h => h.mono htm⟩ hv)
      | some p =>
        have hcost := (hround a ha p hp false).choose_spec.2.2
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        have hbranch (bit : Bool) :
            (machine round leaf control).HaltsWithin m
                (liftRound (config control (some round.q₀) [p, bit] 0 (storage a))) ∧
              ((machine round leaf control).AcceptsWithin m
                (liftRound (config control (some round.q₀) [p, bit] 0 (storage a))) ↔
                  value (next a bit)) := by
          obtain ⟨t, hr, hvalid, hcost⟩ := hround a ha p hp bit
          obtain ⟨τ, hτ, hnext, hrun, hd⟩ := exists_round_phase round leaf control
            (by rw [hr]; rfl)
          rw [hr] at hd
          have hremaining : potential (next a bit) ≤ m - τ := by omega
          have hc := ih (potential (next a bit)) (by omega) (next a bit) rfl hvalid
            (m - τ) hremaining
          constructor
          · rw [haltsWithin_iff_of_phase hnext hrun hd]
            exact ⟨by omega, hc.1⟩
          · rw [acceptsWithin_iff_of_phase hnext hrun hd]
            exact Iff.trans (and_iff_right (by omega : τ ≤ m)) hc.2
        simp only [wordGameHeader]
        constructor
        · rw [show m + 2 = (m + 1) + 1 by omega, haltsWithin_succ]
          intro bit
          rw [next_dispatch, haltsWithin_succ]
          intro chosen
          rw [next_choose]
          exact (hbranch chosen).1
        · rw [show m + 2 = (m + 1) + 1 by omega,
            acceptsWithin_succ_of_next_eq (next_dispatch round leaf control · p (storage a))]
          cases p with
          | false =>
            rw [acceptsWithin_succ_of_existential _ rfl rfl]
            simp only [next_choose]
            exact (exists_congr fun bit => (hbranch bit).2).trans (hvalue a ha false hp).symm
          | true =>
            rw [acceptsWithin_succ_of_universal _ rfl rfl]
            simp only [next_choose]
            exact (forall_congr' fun bit => (hbranch bit).2).trans (hvalue a ha true hp).symm
  exact h (potential a) a rfl ha n hn

end Turing.MultiTapeATM.WordGameLeaf

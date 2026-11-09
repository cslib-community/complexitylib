/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (`Turing.windowList` and `Turing.mem_window_iff_abs_le` belong in
-- `ConfigBound.lean`, next to `Turing.window`)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
public import CslibFrontier.Computability.Machines.Turing.MultiTape.OutView
public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Std.Sat.CNF.Literal

/-!
# Boolean features of configurations

A configuration of a multi-tape machine over `Bool` is described by finitely-valued *features*:
the control state, the position of the input head, the position of each work head, the contents
of each work cell, and what has been written on the output (`Turing.OutView`). Three more
features say what a step depends on: the symbol under each work head, the symbol under the input
head, and the *situation* (`Turing.MultiTapeTM.Situation`) — the state together with all the
symbols read.

Each feature of the next configuration is a Boolean combination of features of the current one:
a halted configuration does not change, and otherwise exactly one situation holds, which
determines the action. The *step equations* (`holds_step_state_iff`, …) state this kind by kind.
For inputs of length `n` and work heads in the window `|z| ≤ T`, the *basic* features
(`Feature.basic`: state, input head, work heads and cells in the window, output view) come in
groups of which exactly one feature holds, and the step equation of each basic feature is a
disjunction of *terms*, conjunctions of basic features, their negations and situations
(`Feature.stepTerms`, `holds_step_iff_exists_stepTerms`). Reductions that describe runs by
Boolean variables, such as the Cook–Levin tableau, and circuits simulating machines are built on
these equations.

## Main definitions

* `Turing.MultiTapeTM.Situation`, `Turing.Cfg.situation`.
* `Turing.MultiTapeTM.Feature`, `Turing.MultiTapeTM.Feature.Holds`.
* `Turing.MultiTapeTM.Feature.groups`, `Turing.MultiTapeTM.Feature.basic`: the basic features.
* `Turing.MultiTapeTM.Feature.stepTerms`: the terms of the step equation of a basic feature.

## Main results

* `Turing.MultiTapeTM.Feature.holds_read_iff`, `holds_inRead_iff`, `holds_sit_iff`: the symbols
  read and the situation, from the basic features.
* `Turing.MultiTapeTM.Feature.holds_step_state_iff`, `holds_step_inPos_iff`,
  `holds_step_head_iff`, `holds_step_cell_iff`, `holds_step_out_iff`: the step equations.
* `Turing.MultiTapeTM.Feature.exists_holds_of_mem_groups`, `eq_of_holds_of_mem_groups`: exactly
  one basic feature of each group holds.
* `Turing.MultiTapeTM.Feature.holds_step_iff_exists_stepTerms`: the step equations as
  disjunctions of terms.
-/

@[expose] public section

namespace Turing

/-- A cell is in the window `-T, …, T` exactly when its absolute value is at most `T`. -/
theorem mem_window_iff_abs_le {T : ℕ} {z : ℤ} : z ∈ window T ↔ |z| ≤ T := by
  rw [mem_window, Int.abs_eq_natAbs]
  exact Nat.cast_le.symm

/-- The cells `-T, …, T` of the window, from left to right. -/
def windowList (T : ℕ) : List ℤ := (List.range (2 * T + 1)).map fun i : ℕ => (i : ℤ) - T

@[simp] theorem mem_windowList {T : ℕ} {z : ℤ} : z ∈ windowList T ↔ |z| ≤ T := by
  rw [windowList, List.mem_map, abs_le]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := List.mem_range.1 hi
    omega
  · intro h
    exact ⟨(z + T).toNat, List.mem_range.2 (by omega), by omega⟩

@[simp] theorem length_windowList (T : ℕ) : (windowList T).length = 2 * T + 1 := by
  simp [windowList]

theorem nodup_windowList (T : ℕ) : (windowList T).Nodup :=
  (List.nodup_range).map fun _ _ h => by simpa using h

@[simp] theorem toFinset_windowList (T : ℕ) : (windowList T).toFinset = window T := by
  ext z
  rw [List.mem_toFinset, mem_windowList, mem_window_iff_abs_le]

namespace MultiTapeTM

variable {k : ℕ} {State : Type}

/-- The situation of a step: the state, the symbol under the input head, and the symbols under the
work heads. The transition function maps a situation to an action. -/
abbrev Situation (k : ℕ) (State : Type) : Type := State × Option Bool × (Fin k → Option Bool)

/-- The action that `tm` takes in situation `y`. -/
noncomputable def actionOf (tm : MultiTapeTM k Bool State) (y : Situation k State) :
    Action k Bool State :=
  tm.tr y.1 y.2.1 y.2.2

/-- The features describing configurations of a machine over `Bool`. -/
inductive Feature (k : ℕ) (State : Type) where
  /-- The control state is `q` (`none` once halted). -/
  | state (q : Option State)
  /-- The input head is at position `j`. -/
  | inPos (j : ℕ)
  /-- The head of work tape `i` is at cell `z`. -/
  | head (i : Fin k) (z : ℤ)
  /-- Cell `z` of work tape `i` holds `s`. -/
  | cell (i : Fin k) (z : ℤ) (s : Option Bool)
  /-- The output written so far has view `o`. -/
  | out (o : OutView)
  /-- The head of work tape `i` reads `s`. -/
  | read (i : Fin k) (s : Option Bool)
  /-- The input head reads `s`. -/
  | inRead (s : Option Bool)
  /-- The configuration is running in situation `y`. -/
  | sit (y : Situation k State)
  deriving DecidableEq

end MultiTapeTM

/-- The situation of a configuration running in state `q`. -/
def Cfg.situation {k : ℕ} {State : Type} {input : List Bool} (cfg : Cfg k Bool State input)
    (q : State) : MultiTapeTM.Situation k State :=
  (q, cfg.inputSymbol, cfg.workTapeSymbols)

namespace MultiTapeTM

namespace Feature

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Whether a feature holds of a configuration. -/
def Holds (cfg : Cfg k Bool State input) : Feature k State → Prop
  | .state q => cfg.state = q
  | .inPos j => cfg.inputPos.val = j
  | .head i z => cfg.workTapePos i = z
  | .cell i z s => cfg.workTapes i z = s
  | .out o => OutView.ofList cfg.output = o
  | .read i s => cfg.workTapeSymbols i = s
  | .inRead s => cfg.inputSymbol = s
  | .sit y => cfg.state = some y.1 ∧ cfg.inputSymbol = y.2.1 ∧ cfg.workTapeSymbols = y.2.2

instance [DecidableEq State] (cfg : Cfg k Bool State input) :
    ∀ φ : Feature k State, Decidable (φ.Holds cfg)
  | .state _ | .inPos _ | .head _ _ | .cell _ _ _ | .out _ | .read _ _ | .inRead _ =>
    inferInstanceAs (Decidable (_ = _))
  | .sit _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable {cfg : Cfg k Bool State input} {i : Fin k}

@[simp] theorem holds_state {q : Option State} : (state q).Holds cfg ↔ cfg.state = q := Iff.rfl
@[simp] theorem holds_inPos {j : ℕ} :
    (inPos j : Feature k State).Holds cfg ↔ cfg.inputPos.val = j := Iff.rfl
@[simp] theorem holds_head {i : Fin k} {z : ℤ} :
    (head i z : Feature k State).Holds cfg ↔ cfg.workTapePos i = z := Iff.rfl
@[simp] theorem holds_cell {i : Fin k} {z : ℤ} {s : Option Bool} :
    (cell i z s : Feature k State).Holds cfg ↔ cfg.workTapes i z = s := Iff.rfl
@[simp] theorem holds_out {o : OutView} :
    (out o : Feature k State).Holds cfg ↔ OutView.ofList cfg.output = o := Iff.rfl
@[simp] theorem holds_read {i : Fin k} {s : Option Bool} :
    (read i s : Feature k State).Holds cfg ↔ cfg.workTapeSymbols i = s := Iff.rfl
@[simp] theorem holds_inRead {s : Option Bool} :
    (inRead s : Feature k State).Holds cfg ↔ cfg.inputSymbol = s := Iff.rfl

/-! ### The symbols read and the situation -/

/-- A work head reads the symbol in the cell it is on, for a head within the window. -/
theorem holds_read_iff {T : ℕ} (hb : |cfg.workTapePos i| ≤ T) (s : Option Bool) :
    (read i s).Holds cfg ↔ ∃ z ∈ window T, (head i z).Holds cfg ∧ (cell i z s).Holds cfg := by
  simp only [holds_read, holds_head, holds_cell, mem_window_iff_abs_le]
  exact ⟨fun h => ⟨_, hb, rfl, h⟩, fun ⟨_, _, hz, h⟩ => by rw [Cfg.workTapeSymbols, hz]; exact h⟩

/-- The input head reads the input symbol at its position. -/
theorem holds_inRead_iff (s : Option Bool) :
    (inRead s : Feature k State).Holds cfg ↔
      ∃ j ∈ Finset.range (input.length + 2), (inPos j).Holds cfg ∧ inputAt input j = s := by
  simp only [holds_inRead, holds_inPos, Finset.mem_range, Cfg.inputSymbol_eq_inputAt]
  exact ⟨fun h => ⟨_, cfg.inputPos.isLt, rfl, h⟩, fun ⟨_, _, hj, h⟩ => hj ▸ h⟩

/-- The situation holds when the state and the symbols read are those of the situation. -/
theorem holds_sit_iff (y : Situation k State) :
    (sit y).Holds cfg ↔ (state (some y.1)).Holds cfg ∧ (inRead y.2.1).Holds cfg ∧
      ∀ i, (read i (y.2.2 i)).Holds cfg := by
  simp only [Holds, funext_iff]

/-- In a configuration running in state `q`, exactly its own situation holds. -/
theorem holds_sit_iff_eq {q : State} (hq : cfg.state = some q) (y : Situation k State) :
    (sit y).Holds cfg ↔ y = cfg.situation q := by
  obtain ⟨q', s, r⟩ := y
  simp only [Holds, hq, Option.some.injEq, Cfg.situation, Prod.mk.injEq]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁.symm, h₂.symm, h₃.symm⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨h₁.symm, h₂.symm, h₃.symm⟩⟩

/-- In a halted configuration, no situation holds. -/
theorem not_holds_sit (h : cfg.state = none) (y : Situation k State) : ¬(sit y).Holds cfg := by
  simp [Holds, h]

/-! ### The step equations -/

section Step

variable (tm : MultiTapeTM k Bool State)

/-- A halted configuration does not change. -/
theorem holds_step_of_halted (h : cfg.state = none) (φ : Feature k State) :
    φ.Holds (tm.step cfg) ↔ φ.Holds cfg := by
  rw [MultiTapeTM.step_of_halt h]

theorem step_eq_apply {q : State} (hq : cfg.state = some q) :
    tm.step cfg = (tm.actionOf (cfg.situation q)).apply cfg :=
  MultiTapeTM.step_of_state hq

variable [Fintype State]

/-- The step equation for the state. -/
theorem holds_step_state_iff [DecidableEq State] (q' : Option State) :
    (state q').Holds (tm.step cfg) ↔
      ((state none).Holds cfg ∧ q' = none) ∨
        ∃ y ∈ (Finset.univ : Finset (Situation k State)).filter
          (fun y => (tm.actionOf y).state = q'), (sit y).Holds cfg := by
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq, eq_comm]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, holds_sit_iff_eq hq,
      exists_eq_right, holds_state, hq, reduceCtorEq, false_and, false_or, step_eq_apply tm hq,
      Action.apply_state]

/-- The step equation for the input head. The input head moves at most one cell, so it comes from
one of the positions `j - 1`, `j`, `j + 1`. -/
theorem holds_step_inPos_iff (j : ℕ) :
    (inPos j).Holds (tm.step cfg) ↔
      ((state none).Holds cfg ∧ (inPos j).Holds cfg) ∨
        ∃ y ∈ (Finset.univ ×ˢ {j - 1, j, j + 1} : Finset (Situation k State × ℕ)).filter
          (fun y => y.2 < input.length + 2 ∧
            moveInputPosNat input.length y.2 (tm.actionOf y.1).inputTape = j),
          (sit y.1).Holds cfg ∧ (inPos y.2).Holds cfg := by
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp only [holds_state, hq, reduceCtorEq, false_and, false_or, Finset.mem_filter,
      Finset.mem_product, Finset.mem_univ, true_and, holds_inPos,
      step_eq_apply tm hq, Action.apply_inputPos, val_moveInputPos_eq_moveInputPosNat]
    constructor
    · intro h
      have hlt := cfg.inputPos.isLt
      have := le_add_one_of_moveInputPosNat_eq hlt h
      refine ⟨(cfg.situation q, cfg.inputPos.val), ⟨?_, hlt, h⟩, (holds_sit_iff_eq hq _).2 rfl, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · rintro ⟨⟨y, j'⟩, ⟨-, -, hy⟩, hsit, rfl⟩
      obtain rfl := (holds_sit_iff_eq hq y).1 hsit
      exact hy

/-- The step equation for a work head within the window `|z| ≤ T`, for a head that was within
the window. -/
theorem holds_step_head_iff {T : ℕ} (hb : |cfg.workTapePos i| ≤ T) (z : ℤ) :
    (head i z).Holds (tm.step cfg) ↔
      ((state none).Holds cfg ∧ (head i z).Holds cfg) ∨
        ∃ y ∈ (Finset.univ : Finset (Situation k State)).filter
          (fun y => |z - (((tm.actionOf y).workTapes i).2 : ℤ)| ≤ T),
          (sit y).Holds cfg ∧ (head i (z - (((tm.actionOf y).workTapes i).2 : ℤ))).Holds cfg := by
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp only [holds_state, hq, reduceCtorEq, false_and, false_or, Finset.mem_filter,
      Finset.mem_univ, true_and, holds_head, step_eq_apply tm hq, Action.apply_workTapePos]
    constructor
    · rintro rfl
      refine ⟨cfg.situation q, ?_, (holds_sit_iff_eq hq _).2 rfl, ?_⟩ <;>
        rw [add_sub_cancel_right]
      exact hb
    · rintro ⟨y, -, hsit, hpos⟩
      obtain rfl := (holds_sit_iff_eq hq y).1 hsit
      rw [hpos, sub_add_cancel]

/-- The step equation for a work cell. -/
theorem holds_step_cell_iff (z : ℤ) (s : Option Bool) :
    (cell i z s).Holds (tm.step cfg) ↔
      ((cell i z s).Holds cfg ∧ ((state none).Holds cfg ∨ ¬(head i z).Holds cfg)) ∨
        ∃ y ∈ (Finset.univ ×ˢ Finset.univ :
            Finset (Situation k State × Option Bool)).filter
          (fun y => ((tm.actionOf y.1).workTapes i).1.getD y.2 = s),
          (sit y.1).Holds cfg ∧ (head i z).Holds cfg ∧ (cell i z y.2).Holds cfg := by
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp only [holds_state, hq, reduceCtorEq, false_or, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and, holds_head, holds_cell, step_eq_apply tm hq,
      Action.apply_workTapes_eq_ite]
    by_cases hz : z = cfg.workTapePos i
    · rw [ite_eq_left hz]
      constructor
      · intro h
        exact Or.inr ⟨(cfg.situation q, cfg.workTapes i z), by simpa [Cfg.situation,
          Cfg.workTapeSymbols, hz, actionOf] using h, (holds_sit_iff_eq hq _).2 rfl, hz.symm, rfl⟩
      · rintro (⟨-, h⟩ | ⟨⟨y, s'⟩, hy, hsit, -, rfl⟩)
        · exact absurd hz.symm h
        · obtain rfl := (holds_sit_iff_eq hq y).1 hsit
          simpa [Cfg.situation, Cfg.workTapeSymbols, hz, actionOf] using hy
    · rw [ite_eq_right hz]
      constructor
      · intro h
        exact Or.inl ⟨h, fun h' => hz h'.symm⟩
      · rintro (⟨h, -⟩ | ⟨y, -, -, hhead, -⟩)
        · exact h
        · exact absurd hhead.symm hz

/-- The step equation for the output. -/
theorem holds_step_out_iff (o : OutView) :
    (out o).Holds (tm.step cfg) ↔
      ((state none).Holds cfg ∧ (out o).Holds cfg) ∨
        ∃ y ∈ (Finset.univ ×ˢ Finset.univ : Finset (Situation k State × OutView)).filter
          (fun y => y.2.push (tm.actionOf y.1).output = o),
          (sit y.1).Holds cfg ∧ (out y.2).Holds cfg := by
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp only [holds_state, hq, reduceCtorEq, false_and, false_or, Finset.mem_filter,
      Finset.mem_product, Finset.mem_univ, true_and, holds_out, step_eq_apply tm hq,
      Action.apply_output, OutView.ofList_append_toList]
    constructor
    · intro h
      exact ⟨(cfg.situation q, OutView.ofList cfg.output), h, (holds_sit_iff_eq hq _).2 rfl, rfl⟩
    · rintro ⟨⟨y, o'⟩, hy, hsit, rfl⟩
      obtain rfl := (holds_sit_iff_eq hq y).1 hsit
      exact hy

end Step

/-! ### Basic features and step terms -/

section Terms

/-- The three symbols a cell can hold: blank, `false` and `true`. -/
def symbols : List (Option Bool) := [none, some false, some true]

@[simp] theorem mem_symbols (s : Option Bool) : s ∈ symbols := by
  rcases s with _ | (_ | _) <;> simp [symbols]

@[simp] theorem length_symbols : symbols.length = 3 := rfl

/-- A term: a conjunction of features, written `(φ, true)`, and of negated features, written
`(φ, false)`. -/
abbrev Term (k : ℕ) (State : Type) : Type := List (Std.Sat.Literal (Feature k State))

/-- A term holds of a configuration when each of its features holds or fails as it says. -/
def Term.Holds (cfg : Cfg k Bool State input) (c : Term k State) : Prop :=
  ∀ l ∈ c, (l.1.Holds cfg ↔ l.2 = true)

@[simp] theorem Term.holds_nil : Term.Holds cfg ([] : Term k State) := by
  simp [Term.Holds]

@[simp] theorem Term.holds_cons {φ : Feature k State} {b : Bool} {c : Term k State} :
    Term.Holds cfg ((φ, b) :: c) ↔ (φ.Holds cfg ↔ b = true) ∧ Term.Holds cfg c := by
  simp [Term.Holds]

variable [Fintype State]

/-- Every control state, `none` included, in a fixed order. -/
noncomputable def states : List (Option State) := (Finset.univ : Finset (Option State)).toList

@[simp] theorem mem_states (q : Option State) : q ∈ (states : List (Option State)) :=
  Finset.mem_toList.2 (Finset.mem_univ q)

@[simp] theorem length_states : (states : List (Option State)).length = Fintype.card State + 1 := by
  simp [states]

/-- Every situation, in a fixed order. -/
noncomputable def situations : List (Situation k State) :=
  (Finset.univ : Finset (Situation k State)).toList

@[simp] theorem mem_situations (y : Situation k State) : y ∈ (situations : List _) :=
  Finset.mem_toList.2 (Finset.mem_univ y)

@[simp] theorem length_situations :
    (situations : List (Situation k State)).length = Fintype.card (Situation k State) := by
  simp [situations]

/-- The *basic* features for inputs of length `n` within the window `|z| ≤ T`, in groups: the
states, the positions of the input head, the positions of each work head in the window, the
contents of each work cell in the window, and the views of the output. In a configuration on an
input of length `n` whose work heads are in the window, exactly one feature of each group holds
(`exists_holds_of_mem_groups`, `eq_of_holds_of_mem_groups`). The window `|z| ≤ T` contains every
cell that a head can reach within `T` steps. -/
noncomputable def groups (n T : ℕ) : List (List (Feature k State)) :=
  states.map state :: (List.range (n + 2)).map inPos ::
    ((List.finRange k).map fun i => (windowList T).map (head i)) ++
      ((List.finRange k ×ˢ windowList T).map fun p => symbols.map (cell p.1 p.2)) ++
        [OutView.all.map out]

/-- The basic features for inputs of length `n` within the window `|z| ≤ T`: the features of all
groups. -/
noncomputable def basic (n T : ℕ) : List (Feature k State) := (groups n T).flatten

variable {n T : ℕ}

theorem mem_groups {g : List (Feature k State)} :
    g ∈ groups n T ↔ g = states.map state ∨ g = (List.range (n + 2)).map inPos ∨
      (∃ i, g = (windowList T).map (head i)) ∨
        (∃ i, ∃ z : ℤ, |z| ≤ T ∧ g = symbols.map (cell i z)) ∨ g = OutView.all.map out := by
  simp only [groups, List.mem_cons, List.mem_append, List.mem_map, Prod.exists, List.mem_product,
    List.mem_finRange, mem_windowList, true_and, List.not_mem_nil, or_false]
  grind

/-- In a configuration whose work heads are in the window, some feature of each group holds. -/
theorem exists_holds_of_mem_groups (hn : input.length = n) (hb : ∀ i, |cfg.workTapePos i| ≤ T)
    {g : List (Feature k State)} (hg : g ∈ groups n T) : ∃ φ ∈ g, φ.Holds cfg := by
  rcases mem_groups.1 hg with rfl | rfl | ⟨i, rfl⟩ | ⟨i, z, -, rfl⟩ | rfl
  · exact ⟨state cfg.state, List.mem_map_of_mem (mem_states _), rfl⟩
  · exact ⟨inPos cfg.inputPos.val, List.mem_map_of_mem (List.mem_range.2 (hn ▸ cfg.inputPos.isLt)),
      rfl⟩
  · exact ⟨head i (cfg.workTapePos i), List.mem_map_of_mem (mem_windowList.2 (hb i)), rfl⟩
  · exact ⟨cell i z (cfg.workTapes i z), List.mem_map_of_mem (mem_symbols _), rfl⟩
  · exact ⟨out (OutView.ofList cfg.output), List.mem_map_of_mem (OutView.mem_all _), rfl⟩

/-- At most one feature of each group holds. -/
theorem eq_of_holds_of_mem_groups {g : List (Feature k State)} (hg : g ∈ groups n T)
    {φ ψ : Feature k State} (hφ : φ ∈ g) (hψ : ψ ∈ g) (h₁ : φ.Holds cfg) (h₂ : ψ.Holds cfg) :
    φ = ψ := by
  rcases mem_groups.1 hg with rfl | rfl | ⟨i, rfl⟩ | ⟨i, z, -, rfl⟩ | rfl <;>
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hφ
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hψ
    simp only [Holds] at h₁ h₂
    subst h₁ h₂
    rfl

theorem mem_basic_iff_exists_mem_groups {φ : Feature k State} :
    φ ∈ basic n T ↔ ∃ g ∈ groups n T, φ ∈ g :=
  List.mem_flatten

theorem mem_basic {φ : Feature k State} :
    φ ∈ basic n T ↔ (∃ q, φ = state q) ∨ (∃ j < n + 2, φ = inPos j) ∨
      (∃ i, ∃ z : ℤ, |z| ≤ T ∧ φ = head i z) ∨
        (∃ i, ∃ z : ℤ, ∃ s, |z| ≤ T ∧ φ = cell i z s) ∨ ∃ o, φ = out o := by
  rw [mem_basic_iff_exists_mem_groups]
  constructor
  · rintro ⟨g, hg, hφ⟩
    rcases mem_groups.1 hg with rfl | rfl | ⟨i, rfl⟩ | ⟨i, z, hz, rfl⟩ | rfl <;>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hφ
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl ⟨a, List.mem_range.1 ha, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, a, mem_windowList.1 ha, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, z, a, hz, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, rfl⟩)))
  · rintro (⟨q, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨i, z, hz, rfl⟩ | ⟨i, z, s, hz, rfl⟩ | ⟨o, rfl⟩)
    · exact ⟨_, mem_groups.2 (Or.inl rfl), List.mem_map_of_mem (mem_states q)⟩
    · exact ⟨_, mem_groups.2 (Or.inr (Or.inl rfl)), List.mem_map_of_mem (List.mem_range.2 hj)⟩
    · exact ⟨_, mem_groups.2 (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))),
        List.mem_map_of_mem (mem_windowList.2 hz)⟩
    · exact ⟨_, mem_groups.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, z, hz, rfl⟩)))),
        List.mem_map_of_mem (mem_symbols s)⟩
    · exact ⟨_, mem_groups.2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        List.mem_map_of_mem (OutView.mem_all o)⟩

theorem state_mem_basic (q : Option State) : state q ∈ (basic n T : List (Feature k State)) :=
  mem_basic.2 (Or.inl ⟨q, rfl⟩)

theorem inPos_mem_basic {j : ℕ} (hj : j < n + 2) :
    inPos j ∈ (basic n T : List (Feature k State)) :=
  mem_basic.2 (Or.inr (Or.inl ⟨j, hj, rfl⟩))

theorem head_mem_basic (i : Fin k) {z : ℤ} (hz : |z| ≤ T) :
    head i z ∈ (basic n T : List (Feature k State)) :=
  mem_basic.2 (Or.inr (Or.inr (Or.inl ⟨i, z, hz, rfl⟩)))

theorem cell_mem_basic (i : Fin k) {z : ℤ} (hz : |z| ≤ T) (s : Option Bool) :
    cell i z s ∈ (basic n T : List (Feature k State)) :=
  mem_basic.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, z, s, hz, rfl⟩))))

theorem out_mem_basic (o : OutView) : out o ∈ (basic n T : List (Feature k State)) :=
  mem_basic.2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨o, rfl⟩))))

/-- The number of basic features. -/
theorem length_basic (n T : ℕ) :
    (basic n T : List (Feature k State)).length =
      (Fintype.card State + 1) + (n + 2) + k * (2 * T + 1) + k * (2 * T + 1) * 3 + 4 := by
  simp only [basic, groups, List.length_flatten, List.map_cons, List.map_append, List.map_map,
    Function.comp_def, List.length_map, length_states, List.length_range, length_windowList,
    length_symbols, List.map_const', List.sum_cons, List.sum_append, List.sum_replicate,
    List.length_finRange, List.length_product, OutView.length_all, List.map_nil, List.sum_nil]
  ring

variable [DecidableEq State] (tm : MultiTapeTM k Bool State)

/-- The terms of the step equation of a basic feature, for inputs of length `n` and the window
`|z| ≤ T`: the feature holds after a step exactly when one of its terms holds before it
(`holds_step_iff_exists_stepTerms`). Every term is made of basic features, their negations, and
situations (`mem_basic_of_mem_stepTerms`). -/
noncomputable def stepTerms (tm : MultiTapeTM k Bool State) (n T : ℕ) :
    Feature k State → List (Term k State)
  | state q' =>
    (if q' = none then [[(state none, true)]] else []) ++
      (situations.filter fun y => (tm.actionOf y).state = q').map fun y => [(sit y, true)]
  | inPos j =>
    [(state none, true), (inPos j, true)] ::
      ((situations ×ˢ [j - 1, j, j + 1]).filter fun p =>
          p.2 < n + 2 ∧ moveInputPosNat n p.2 (tm.actionOf p.1).inputTape = j).map
        fun p => [(sit p.1, true), (inPos p.2, true)]
  | head i z =>
    [(state none, true), (head i z, true)] ::
      (situations.filter fun y => |z - (((tm.actionOf y).workTapes i).2 : ℤ)| ≤ T).map
        fun y => [(sit y, true), (head i (z - (((tm.actionOf y).workTapes i).2 : ℤ)), true)]
  | cell i z s =>
    [(cell i z s, true), (state none, true)] :: [(cell i z s, true), (head i z, false)] ::
      ((situations ×ˢ symbols).filter fun p =>
          ((tm.actionOf p.1).workTapes i).1.getD p.2 = s).map
        fun p => [(sit p.1, true), (head i z, true), (cell i z p.2, true)]
  | out o =>
    [(state none, true), (out o, true)] ::
      ((situations ×ˢ OutView.all).filter fun p => p.2.push (tm.actionOf p.1).output = o).map
        fun p => [(sit p.1, true), (out p.2, true)]
  | read _ _ | inRead _ | sit _ => []

/-- **The step equation.** Within the window, a basic feature holds after a step exactly when one
of its terms holds before it. -/
theorem holds_step_iff_exists_stepTerms (hn : input.length = n)
    (hb : ∀ i, |cfg.workTapePos i| ≤ T) {φ : Feature k State} (hφ : φ ∈ basic n T) :
    φ.Holds (tm.step cfg) ↔ ∃ c ∈ stepTerms tm n T φ, Term.Holds cfg c := by
  subst hn
  rcases mem_basic.1 hφ with ⟨q, rfl⟩ | ⟨j, -, rfl⟩ | ⟨i, z, -, rfl⟩ | ⟨i, z, s, -, rfl⟩ | ⟨o, rfl⟩
  · rw [holds_step_state_iff]
    cases q <;> simp [stepTerms, or_and_right, exists_or]
  · rw [holds_step_inPos_iff, stepTerms]
    simp only [List.mem_cons, exists_eq_or_imp, List.mem_map, exists_exists_and_eq_and]
    refine or_congr (by simp) ⟨fun ⟨⟨y, j'⟩, hy, h⟩ => ⟨(y, j'), ?_, ?_⟩,
      fun ⟨⟨y, j'⟩, hy, h⟩ => ⟨(y, j'), ?_, ?_⟩⟩ <;>
      simp_all [List.mem_filter, Finset.mem_filter]
  · rw [holds_step_head_iff tm (hb i)]
    simp [stepTerms, or_and_right, exists_or]
  · rw [holds_step_cell_iff]
    simp only [stepTerms, List.mem_cons, List.mem_map, List.mem_filter, exists_eq_or_imp,
      Term.holds_cons, Term.holds_nil, iff_true, Bool.false_eq_true, iff_false, and_true]
    simp [and_or_left, or_assoc, and_assoc]
  · rw [holds_step_out_iff]
    simp [stepTerms, or_and_right, exists_or]

/-- A feature has at most `4 |Situation| + 2` terms in its step equation. -/
theorem length_stepTerms_le (φ : Feature k State) :
    (stepTerms tm n T φ).length ≤ 4 * Fintype.card (Situation k State) + 2 := by
  have hf {α : Type} (l : List α) (p : α → Bool) : (l.filter p).length ≤ l.length :=
    List.length_filter_le p l
  cases φ with
  | state q =>
    have := hf situations fun y => decide ((tm.actionOf y).state = q)
    simp only [stepTerms, List.length_append, List.length_map, length_situations] at this ⊢
    split_ifs <;> simp only [List.length_singleton, List.length_nil] <;> omega
  | inPos j =>
    have := hf (situations ×ˢ [j - 1, j, j + 1]) fun p =>
      decide (p.2 < n + 2 ∧ moveInputPosNat n p.2 (tm.actionOf p.1).inputTape = j)
    simp only [List.length_product, length_situations, List.length_cons, List.length_nil] at this
    simp only [stepTerms, List.length_cons, List.length_map]
    omega
  | head i z =>
    have := hf situations fun y => decide (|z - (((tm.actionOf y).workTapes i).2 : ℤ)| ≤ T)
    simp only [length_situations] at this
    simp only [stepTerms, List.length_cons, List.length_map]
    omega
  | cell i z s =>
    have := hf (situations ×ˢ symbols) fun p =>
      decide (((tm.actionOf p.1).workTapes i).1.getD p.2 = s)
    simp only [List.length_product, length_situations, length_symbols] at this
    simp only [stepTerms, List.length_cons, List.length_map]
    omega
  | out o =>
    have := hf (situations ×ˢ OutView.all) fun p => decide (p.2.push (tm.actionOf p.1).output = o)
    simp only [List.length_product, length_situations, OutView.length_all] at this
    simp only [stepTerms, List.length_cons, List.length_map]
    omega
  | read | inRead | sit => simp [stepTerms]

/-- Every term of a step equation has at most three literals. -/
theorem length_le_three_of_mem_stepTerms {φ : Feature k State} {c : Term k State}
    (hc : c ∈ stepTerms tm n T φ) : c.length ≤ 3 := by
  cases φ <;>
    simp only [stepTerms, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil] at hc
  · rcases hc with hc | ⟨y, -, rfl⟩
    · split_ifs at hc
      · obtain rfl := List.mem_singleton.1 hc
        simp
      · simp at hc
    · simp
  · rcases hc with rfl | ⟨_, -, rfl⟩ <;> simp
  · rcases hc with rfl | ⟨_, -, rfl⟩ <;> simp
  · rcases hc with rfl | rfl | ⟨_, -, rfl⟩ <;> simp
  · rcases hc with rfl | ⟨_, -, rfl⟩ <;> simp

/-- The terms of a basic feature are made of basic features, their negations, and situations. -/
theorem mem_basic_of_mem_stepTerms {φ : Feature k State} (hφ : φ ∈ basic n T)
    {c : Term k State} (hc : c ∈ stepTerms tm n T φ) {l : Std.Sat.Literal (Feature k State)}
    (hl : l ∈ c) : l.1 ∈ basic n T ∨ ∃ y, l = (sit y, true) := by
  have hsit (y : Situation k State) :
      (sit y, true) = l → l.1 ∈ basic n T ∨ ∃ y, l = (sit y, true) :=
    fun h => Or.inr ⟨y, h.symm⟩
  rcases mem_basic.1 hφ with ⟨q, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨i, z, hz, rfl⟩ | ⟨i, z, s, hz, rfl⟩ |
    ⟨o, rfl⟩ <;>
    simp only [stepTerms, List.mem_append, List.mem_cons, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hc
  · rcases hc with hc | ⟨y, -, rfl⟩
    · split_ifs at hc
      · obtain rfl := List.mem_singleton.1 hc
        obtain rfl := List.mem_singleton.1 hl
        exact Or.inl (state_mem_basic _)
      · simp at hc
    · exact hsit y (List.mem_singleton.1 hl).symm
  · rcases hc with rfl | ⟨⟨y, j'⟩, ⟨-, hj', -⟩, rfl⟩ <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl <;> rcases hl with rfl | rfl
    exacts [Or.inl (state_mem_basic _), Or.inl (inPos_mem_basic hj), hsit y rfl,
      Or.inl (inPos_mem_basic hj')]
  · rcases hc with rfl | ⟨y, ⟨-, hy⟩, rfl⟩ <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl <;> rcases hl with rfl | rfl
    exacts [Or.inl (state_mem_basic _), Or.inl (head_mem_basic i hz), hsit y rfl,
      Or.inl (head_mem_basic i hy)]
  · rcases hc with rfl | rfl | ⟨⟨y, s'⟩, -, rfl⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      exacts [Or.inl (cell_mem_basic i hz s), Or.inl (state_mem_basic _)]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      exacts [Or.inl (cell_mem_basic i hz s), Or.inl (head_mem_basic i hz)]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl | rfl
      exacts [hsit y rfl, Or.inl (head_mem_basic i hz), Or.inl (cell_mem_basic i hz s')]
  · rcases hc with rfl | ⟨⟨y, o'⟩, -, rfl⟩ <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl <;> rcases hl with rfl | rfl
    exacts [Or.inl (state_mem_basic _), Or.inl (out_mem_basic _), hsit y rfl,
      Or.inl (out_mem_basic _)]

end Terms

end Feature

end MultiTapeTM

end Turing

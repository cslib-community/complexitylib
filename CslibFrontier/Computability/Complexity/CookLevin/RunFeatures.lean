/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Correctness
public import CslibFrontier.Computability.Complexity.CookLevin.Parsimonious
public import CslibFrontier.Computability.Machines.Turing.MultiTape.TrackedRun

/-!
# The features that hold along a run

`Cslib.Complexity.CookLevin.trueVars tm u w T` lists the tableau variables that the run of `tm` on
`u ++ w` makes true, read off the tracked run (`Turing.MultiTapeTM.trackedRun`): at every time
`t ≤ T`, the control, the positions of the input and work heads, the work cells in the window
`|z| ≤ T`, the view of the output, the symbols read and the situation; and the certificate bits of
`w` that are `true`. On every variable of the tableau, membership in this list is the assignment
`Cslib.Complexity.CookLevin.runAssignment` read off the run
(`Cslib.Complexity.CookLevin.decide_mem_trueVars_eq_runAssignment`). The list is built from the
run by constructors only, so a polynomial-time computation of it never decodes a variable.

## Main definitions

* `Cslib.Complexity.CookLevin.trueFeatures`: the features listed for tracked storage.
* `Cslib.Complexity.CookLevin.trueVars`: the variables listed for a run.

## Main results

* `Cslib.Complexity.CookLevin.mem_trueFeatures_iff`: on agreeing storage, a feature with its cell
  in the window is listed exactly when it holds.
* `Cslib.Complexity.CookLevin.decide_mem_trueVars_eq_runAssignment`: listed variables are the true
  ones, on the variables of the tableau.
* `Cslib.Complexity.CookLevin.eval_tableau_trueVars`: the listed variables satisfy the tableau of
  an accepting run.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
-/

public section

namespace Cslib.Complexity.CookLevin

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Feature Cslib.Logic.PL

variable {k : ℕ} {State : Type}

/-- The features with finitely many values that hold, given the control, the input symbol read,
the work symbols read and the view of the output: these four, and the situation of a running
configuration. -/
def finiteFeatures : Option State × Option Bool × (Fin k → Option Bool) × OutView →
    List (Feature k State)
  | (q, s, r, o) => state q :: inRead s :: out o ::
      ((List.finRange k).map fun i => read i (r i)) ++ q.elim [] fun q => [sit (q, s, r)]

/-- The features listed for tracked storage `c`, with work cells in the window `|z| ≤ T`. -/
@[expose]
noncomputable def trueFeatures (T : ℕ) (c : FiniteCfg k Bool State × (Fin k → ℤ)) :
    List (Feature k State) :=
  finiteFeatures (c.1.state, c.1.inputSymbol, c.1.workTapeSymbols, OutView.ofList c.1.output) ++
    inPos c.1.inputPos.val :: (List.finRange k).flatMap fun i =>
      head i (c.2 i) :: (windowList T).map fun z => cell i z ((c.1.workTapes i).read (z - c.2 i))

/-- A feature whose cell, if any, lies in the window `|z| ≤ T`. -/
def InWindow (T : ℕ) : Feature k State → Prop
  | cell _ z _ => |z| ≤ T
  | _ => True

/-- On storage agreeing with a native configuration, the listed features are read off the native
configuration. -/
theorem trueFeatures_eq {w : List Bool} {c : FiniteCfg k Bool State × (Fin k → ℤ)}
    {cfg : Cfg k Bool State w} (h : TrackedAgrees c cfg) (T : ℕ) :
    trueFeatures T c =
      finiteFeatures
          (cfg.state, cfg.inputSymbol, cfg.workTapeSymbols, OutView.ofList cfg.output) ++
        inPos cfg.inputPos.val :: (List.finRange k).flatMap fun i =>
          head i (cfg.workTapePos i) :: (windowList T).map fun z =>
            cell i z (cfg.workTapes i z) := by
  simp only [trueFeatures, h.read_sub]
  simp only [h.state, h.inputSymbol, h.workTapeSymbols, h.output, h.inputPos, h.workTapePos]

/-- **Listed features hold.** On storage agreeing with a native configuration, a feature with its
cell in the window is listed exactly when it holds. -/
theorem mem_trueFeatures_iff {w : List Bool} {c : FiniteCfg k Bool State × (Fin k → ℤ)}
    {cfg : Cfg k Bool State w} (h : TrackedAgrees c cfg) {T : ℕ} {φ : Feature k State}
    (hφ : InWindow T φ) : φ ∈ trueFeatures T c ↔ φ.Holds cfg := by
  have hmem : ∀ ψ : Feature k State,
      ψ ∈ cfg.state.elim [] (fun q => [sit (q, cfg.inputSymbol, cfg.workTapeSymbols)]) ↔
        ∃ q, cfg.state = some q ∧ ψ = sit (q, cfg.inputSymbol, cfg.workTapeSymbols) := by
    intro ψ
    cases cfg.state <;> simp
  rw [trueFeatures_eq h]
  cases φ with
  | state q => simp [finiteFeatures, hmem, eq_comm]
  | inPos j => simp [finiteFeatures, hmem, eq_comm]
  | head i z => simp [finiteFeatures, hmem, eq_comm]
  | cell i z s =>
    simp only [InWindow] at hφ
    simp [finiteFeatures, hmem, hφ, eq_comm]
  | out o => simp [finiteFeatures, hmem, eq_comm]
  | read i s => simp [finiteFeatures, hmem, Cfg.workTapeSymbols, eq_comm]
  | inRead s => simp [finiteFeatures, hmem, eq_comm]
  | sit y =>
    rcases y with ⟨q, s, r⟩
    change _ ↔ cfg.state = some q ∧ cfg.inputSymbol = s ∧ cfg.workTapeSymbols = r
    simp only [finiteFeatures, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
      hmem, reduceCtorEq, false_or, or_false, and_false, exists_false, sit.injEq,
      Prod.mk.injEq, List.mem_finRange]
    constructor
    · rintro ⟨q', hq, rfl, rfl, rfl⟩
      exact ⟨hq, rfl, rfl⟩
    · rintro ⟨hq, rfl, rfl⟩
      exact ⟨q, hq, rfl, rfl, rfl⟩

/-- A basic feature has its cell, if any, in the window. -/
theorem inWindow_of_mem_basic {n T : ℕ} {φ : Feature k State} [Fintype State]
    (hφ : φ ∈ basic n T) : InWindow T φ := by
  rcases mem_basic.1 hφ with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, hz, rfl⟩ | ⟨_, rfl⟩
  all_goals trivial

/-! ### The listed variables of a run -/

variable [Fintype State] [DecidableEq State]

/-- The variables listed for the run of `tm` on `u ++ w` up to time `T`: the features listed for
the tracked storage at each time `t ≤ T`, and the certificate bits of `w` that are `true`. -/
@[expose]
noncomputable def trueVars (tm : MultiTapeTM k Bool State) (u w : List Bool) (T : ℕ) :
    List (Var k State) :=
  ((List.range (T + 1)).flatMap fun t =>
      (trueFeatures T (trackedRun tm (u ++ w, t))).map (Var.holds t)) ++
    (List.range w.length).flatMap fun j => if w.getD j false then [Var.cert j] else []

/-- **The listed variables are the true ones** on every variable that the tableau mentions (see
`Cslib.Complexity.CookLevin.determined_of_mem_vars_tableau`). -/
theorem decide_mem_trueVars_eq_runAssignment {tm : MultiTapeTM k Bool State} {u w : List Bool}
    {T : ℕ} {v : Var k State} (hv : Determined (u.length + w.length) w.length T v) :
    decide (v ∈ trueVars tm u w T) = runAssignment tm u w v := by
  have hite : ∀ (v : Var k State) j,
      v ∈ (if w.getD j false then [Var.cert j] else []) ↔ w.getD j false = true ∧ v = .cert j := by
    intro v j
    split <;> simp_all
  have hholds : ∀ t ≤ T, ∀ φ : Feature k State, InWindow T φ →
      decide (Var.holds t φ ∈ trueVars tm u w T) = runAssignment tm u w (.holds t φ) := by
    intro t ht φ hφ
    have hiff := mem_trueFeatures_iff (trackedAgrees_trackedRun tm (u ++ w) t) hφ
    simp only [trueVars, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, hite,
      Var.holds.injEq, reduceCtorEq, and_false, exists_false, or_false, runAssignment]
    refine decide_eq_decide.2 ⟨?_, fun h => ⟨t, by omega, φ, hiff.2 h, rfl, rfl⟩⟩
    rintro ⟨t', -, φ', hφ', rfl, rfl⟩
    exact hiff.1 hφ'
  rcases hv with ⟨j, hj, rfl⟩ | ⟨t, ht, φ, hφ, rfl⟩ | ⟨t, ht, ⟨i, s, rfl⟩ | ⟨s, rfl⟩ | ⟨y, rfl⟩⟩
  · have hmem : Var.cert j ∈ trueVars tm u w T ↔ w.getD j false = true := by
      simp only [trueVars, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, hite,
        reduceCtorEq, and_false, exists_false, false_or, Var.cert.injEq]
      exact ⟨fun ⟨a, _, h, e⟩ => e ▸ h, fun h => ⟨j, hj, h, rfl⟩⟩
    simp only [hmem, Bool.decide_eq_true, runAssignment]
  · exact hholds t ht φ (inWindow_of_mem_basic hφ)
  · exact hholds t ht.le _ trivial
  · exact hholds t ht.le _ trivial
  · exact hholds t ht.le _ trivial

/-- **The listed variables satisfy the tableau** of an accepting run: membership in
`trueVars tm u w T` agrees with `runAssignment tm u w` on every variable of the tableau. -/
theorem eval_tableau_trueVars {tm : MultiTapeTM k Bool State} {u w : List Bool} {T : ℕ}
    (hhalt : (tm.runFrom (tm.initCfg (u ++ w)) T).state = none)
    (hout : (tm.runFrom (tm.initCfg (u ++ w)) T).output = [true]) :
    (tableau tm u w.length T).eval (fun v => decide (v ∈ trueVars tm u w T)) = true := by
  rw [CNF.eval_congr fun v hv =>
    decide_mem_trueVars_eq_runAssignment (determined_of_mem_vars_tableau hv)]
  exact eval_tableau_runAssignment rfl hhalt hout

end Cslib.Complexity.CookLevin

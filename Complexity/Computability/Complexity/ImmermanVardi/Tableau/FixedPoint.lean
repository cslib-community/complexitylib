/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.ImmermanVardi.Tableau.Correct
public import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# A least fixed point for the native deterministic computation tableau

One ternary relation stores `(feature tag, time, position)`. Its positive transformer adds
initial facts and consequences of the preceding row. The least fixed point is exactly the
native deterministic run, uniformly for every finite domain large enough to hold the input
endmarkers and the fixed finite collection of tags.

## Main definitions

* `tagIndex`: input-independent numerical feature tags.
* `initial`: the initial native row, independent of the input bits.
* `traceRow`: project a ternary relation to a named row.
* `traceStep`: the monotone tableau transformer.

## Main results

* `traceStep_lfp`: the least fixed point equals the native run tableau.
* `traceRow_lfp`: a named row of the fixed point agrees with the corresponding native run.
-/

@[expose] public section

namespace Cslib.Complexity.ImmermanVardi.Tableau

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature

variable {m B : ℕ} {State : Type} [Fintype State]

/-- A fixed numerical encoding of the finite set of feature names. -/
noncomputable def tagIndex (q : Tag m State) : ℕ := (Fintype.equivFin (Tag m State) q).val

/-- The tag encoding is injective. -/
theorem tagIndex_injective : Function.Injective (tagIndex (m := m) (State := State)) :=
  fun _ _ h => (Fintype.equivFin _).injective (Fin.ext h)

/-- Every feature tag fits in a domain at least as large as the set of names. -/
theorem tagIndex_lt (hB : Fintype.card (Tag m State) ≤ B) (q : Tag m State) :
    tagIndex q < B :=
  lt_of_lt_of_le (Fintype.equivFin (Tag m State) q).isLt hB

/-- The initial row of a native machine, with blank work tapes and input head at one. -/
def initial (tm : MultiTapeTM m Bool State) : Row m State B
  | .state q, _ => q = some tm.q₀
  | .out o, _ => o = .empty
  | .inPos, a => a.val = 1
  | .head _ _, a => a.val = 0
  | .cell _ _ s, _ => s = none

omit [Fintype State] in
/-- The explicit initial row agrees with the actual native initial configuration. -/
theorem initial_iff (tm : MultiTapeTM m Bool State) (input : List Bool)
    (q : Tag m State) (a : Fin B) :
    initial tm q a ↔ row (tm.initCfg input) q a := by
  cases q with
  | head i sign =>
    cases sign <;> simp [initial, row, Tag.feature, Feature.Holds, offset, eq_comm]
  | state q => simp [initial, row, Tag.feature, Feature.Holds, eq_comm]
  | out o => simp [initial, row, Tag.feature, Feature.Holds, eq_comm]
  | inPos => simp [initial, row, Tag.feature, Feature.Holds, eq_comm]
  | cell i sign s => simp [initial, row, Tag.feature, Feature.Holds, eq_comm]

/-- The row of a ternary relation at time `t`, using the fixed feature tags. -/
def traceRow (R : Set (Fin 3 → Fin B)) (t : Fin B) : Row m State B :=
  fun q a => ∃ z : Fin B, z.val = tagIndex q ∧ ![z, t, a] ∈ R

/-- The positive, time-indexed tableau transformer. -/
noncomputable def traceStep (tm : MultiTapeTM m Bool State) (input : List Bool) :
    Set (Fin 3 → Fin B) →o Set (Fin 3 → Fin B) where
  toFun R := {x | ∃ q : Tag m State, (x 0).val = tagIndex q ∧
    (((x 1).val = 0 ∧ initial tm q (x 2)) ∨
      ∃ t : Fin B, t.val + 1 = (x 1).val ∧ rowStep tm input (traceRow R t) q (x 2))}
  monotone' := by
    intro R S h x hx
    rcases hx with ⟨q, hq, hbase | ⟨t, ht, hstep⟩⟩
    · exact ⟨q, hq, Or.inl hbase⟩
    · refine ⟨q, hq, Or.inr ⟨t, ht, rowStep_mono tm input ?_ q (x 2) hstep⟩⟩
      intro q a ha
      rcases ha with ⟨z, hz, hr⟩
      exact ⟨z, hz, h hr⟩

/-- The canonical ternary relation of all rows of the bounded native run. -/
def runTable (tm : MultiTapeTM m Bool State) (input : List Bool) : Set (Fin 3 → Fin B) :=
  {x | ∃ q : Tag m State, (x 0).val = tagIndex q ∧
    row (tm.runFrom (tm.initCfg input) (x 1).val) q (x 2)}

/-- Projecting the canonical ternary table recovers exactly the desired native row. -/
theorem traceRow_runTable (tm : MultiTapeTM m Bool State) (input : List Bool)
    (hB : Fintype.card (Tag m State) ≤ B) (t : Fin B) (q : Tag m State) (a : Fin B) :
    traceRow (runTable tm input) t q a ↔
      row (tm.runFrom (tm.initCfg input) t.val) q a := by
  constructor
  · rintro ⟨z, hz, q', hq', hr⟩
    have hqq : q' = q := tagIndex_injective (hq'.symm.trans hz)
    simpa [hqq] using hr
  · intro hr
    exact ⟨⟨tagIndex q, tagIndex_lt hB q⟩, rfl, q, rfl, hr⟩

private theorem traceRow_runTable_eq (tm : MultiTapeTM m Bool State) (input : List Bool)
    (hB : Fintype.card (Tag m State) ≤ B) (t : Fin B) :
    traceRow (runTable tm input) t = row (tm.runFrom (tm.initCfg input) t.val) :=
  funext fun q => funext fun a => propext (traceRow_runTable tm input hB t q a)

/-- The exact native table is closed under all positive tableau rules. -/
theorem traceStep_runTable_le (tm : MultiTapeTM m Bool State) (input : List Bool)
    (hn : input.length + 1 < B) (hB : Fintype.card (Tag m State) ≤ B) :
    traceStep (B := B) tm input (runTable tm input) ⊆ runTable tm input := by
  rintro x ⟨q, hq, ⟨ht, hinit⟩ | ⟨t, ht, hstep⟩⟩
  · refine ⟨q, hq, ?_⟩
    simpa only [ht, runFrom, Function.iterate_zero_apply]
      using (initial_iff tm input q (x 2)).1 hinit
  · refine ⟨q, hq, ?_⟩
    rw [traceRow_runTable_eq tm input hB] at hstep
    have hb : ∀ i, |(tm.runFrom (tm.initCfg input) t.val).workTapePos i| + 1 < B := by
      intro i
      have := tm.abs_workTapePos_runFrom_le input t.val i
      have := (x 1).isLt
      omega
    have hs := (rowStep_row tm hn hb q (x 2)).1 hstep
    simpa only [← ht, runFrom_succ] using hs

/-- The least fixed point contains every native row. -/
theorem runTable_le_traceStep_lfp (tm : MultiTapeTM m Bool State) (input : List Bool)
    (hn : input.length + 1 < B) (hB : Fintype.card (Tag m State) ≤ B) :
    runTable tm input ⊆ (traceStep (B := B) tm input).lfp := by
  have hrow : ∀ n, ∀ (t : Fin B), t.val = n → ∀ q a,
      row (tm.runFrom (tm.initCfg input) n) q a →
        traceRow (traceStep tm input).lfp t q a := by
    intro n
    induction n with
    | zero =>
      intro t ht q a hr
      let z : Fin B := ⟨tagIndex q, tagIndex_lt hB q⟩
      refine ⟨z, rfl, ?_⟩
      rw [← (traceStep (B := B) tm input).map_lfp]
      exact ⟨q, rfl, Or.inl ⟨ht, (initial_iff tm input q a).2 hr⟩⟩
    | succ n ih =>
      intro t ht q a hr
      let p : Fin B := ⟨n, by have := t.isLt; omega⟩
      let z : Fin B := ⟨tagIndex q, tagIndex_lt hB q⟩
      refine ⟨z, rfl, ?_⟩
      rw [← (traceStep (B := B) tm input).map_lfp]
      refine ⟨q, rfl, Or.inr ⟨p, ht.symm, ?_⟩⟩
      have hb : ∀ i, |(tm.runFrom (tm.initCfg input) n).workTapePos i| + 1 < B := by
        intro i
        have := tm.abs_workTapePos_runFrom_le input n i
        have := t.isLt
        omega
      have hs : rowStep tm input (row (tm.runFrom (tm.initCfg input) n)) q a :=
        (rowStep_row tm hn hb q a).2 (by simpa only [runFrom_succ] using hr)
      exact rowStep_mono tm input (fun q a ha => ih p rfl q a ha) q a hs
  rintro x ⟨q, hq, hx⟩
  obtain ⟨z, hz, hr⟩ := hrow (x 1).val (x 1) rfl q (x 2) hx
  have hz' : z = x 0 := Fin.ext (hz.trans hq.symm)
  have hvec : ![z, x 1, x 2] = x := by
    ext i
    fin_cases i <;> simp [hz']
  rwa [hvec] at hr

/-- The native deterministic tableau is exactly a least fixed point of positive local rules. -/
theorem traceStep_lfp (tm : MultiTapeTM m Bool State) (input : List Bool)
    (hn : input.length + 1 < B) (hB : Fintype.card (Tag m State) ≤ B) :
    (traceStep (B := B) tm input).lfp = runTable tm input :=
  Set.Subset.antisymm
    ((traceStep tm input).lfp_le (traceStep_runTable_le tm input hn hB))
    (runTable_le_traceStep_lfp tm input hn hB)

/-- Each named row of the least fixed point is the corresponding native configuration. -/
theorem traceRow_lfp (tm : MultiTapeTM m Bool State) (input : List Bool)
    (hn : input.length + 1 < B) (hB : Fintype.card (Tag m State) ≤ B)
    (t : Fin B) (q : Tag m State) (a : Fin B) :
    traceRow (traceStep tm input).lfp t q a ↔
      row (tm.runFrom (tm.initCfg input) t.val) q a := by
  rw [traceStep_lfp tm input hn hB]
  exact traceRow_runTable tm input hB t q a

end Cslib.Complexity.ImmermanVardi.Tableau

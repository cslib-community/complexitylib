/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.Defs
public import CslibFrontier.Computability.DecisionTree.Cost

/-!
# Read-Only Embedding of Static Boolean Decision Trees into 1-Bit Cell-Probe Trees

This file embeds static Boolean query trees (`Cslib.DecisionTree (Fin S) α`) as read-only 1-bit
cell-probe trees (`Cslib.CellProbe.ProbeTree S 1 α`), identifying Boolean assignments
`Fin S → Bool` with 1-bit cell memories `Mem S 1` (`Fin S → Fin 2`).

## Main definitions

* `Cslib.CellProbe.memToBool`, `Cslib.CellProbe.boolToMem`: inverse bijections between `Mem S 1`
  and `Fin S → Bool`.
* `Cslib.CellProbe.ProbeTree.ofDecisionTree`: read-only 1-bit cell-probe embedding of
  `DecisionTree (Fin S) α`.

## Main results

* `Cslib.CellProbe.ProbeTree.run_ofDecisionTree`,
  `Cslib.CellProbe.ProbeTree.probes_ofDecisionTree`,
  `Cslib.CellProbe.ProbeTree.probedCells_ofDecisionTree`,
  `Cslib.CellProbe.ProbeTree.depth_ofDecisionTree`: exact agreement on return value, pathwise probe
  cost, distinct queried coordinates, and structural worst-case depth.
-/

public section

namespace Cslib.CellProbe

/-- View a 1-bit cell memory `Mem S 1` (`Fin S → Fin 2`) as a Boolean assignment `Fin S → Bool`
(`0 ↦ false`, `1 ↦ true`). -/
@[expose] def memToBool {S : ℕ} (m : Mem S 1) : Fin S → Bool :=
  fun i => (m i).1 == 1

/-- Encode a Boolean assignment `x : Fin S → Bool` as a 1-bit cell memory `Mem S 1`
(`false ↦ 0`, `true ↦ 1`). -/
@[expose] def boolToMem {S : ℕ} (x : Fin S → Bool) : Mem S 1 :=
  fun i => cond (x i) ⟨1, by decide⟩ ⟨0, by decide⟩

@[simp]
theorem memToBool_boolToMem {S : ℕ} (x : Fin S → Bool) :
    memToBool (boolToMem x) = x := by
  funext i
  cases hx : x i <;> simp [memToBool, boolToMem, hx]

@[simp]
theorem boolToMem_memToBool {S : ℕ} (m : Mem S 1) :
    boolToMem (memToBool m) = m := by
  funext i
  cases hmi : m i with
  | mk v hv =>
    have hv2 : v = 0 ∨ v = 1 := by omega
    rcases hv2 with rfl | rfl <;> simp [memToBool, boolToMem, hmi]

namespace ProbeTree

/-- Embed a static Boolean `DecisionTree (Fin S) α` as a read-only 1-bit `ProbeTree S 1 α`. -/
@[expose] def ofDecisionTree {S : ℕ} {α : Type} : DecisionTree (Fin S) α → ProbeTree S 1 α
  | .leaf a => pure a
  | .node i ifFalse ifTrue => do
      let v ← read i
      if v.1 == 1 then ofDecisionTree ifTrue else ofDecisionTree ifFalse

@[simp]
theorem run_ofDecisionTree {S : ℕ} {α : Type} (t : DecisionTree (Fin S) α) (m : Mem S 1) :
    (ofDecisionTree t).run m = (t.eval (memToBool m), m) := by
  induction t with
  | leaf a => rfl
  | node i ifFalse ifTrue ihF ihT =>
    change (if (m i).1 == 1 then ofDecisionTree ifTrue else ofDecisionTree ifFalse).run m =
      (cond (memToBool m i) (ifTrue.eval (memToBool m)) (ifFalse.eval (memToBool m)), m)
    cases hbit : memToBool m i <;> simp only [memToBool] at hbit <;> simp [hbit, ihF, ihT]

@[simp]
theorem probes_ofDecisionTree {S : ℕ} {α : Type} (t : DecisionTree (Fin S) α) (m : Mem S 1) :
    (ofDecisionTree t).probes m = t.cost (memToBool m) := by
  induction t with
  | leaf a => rfl
  | node i ifFalse ifTrue ihF ihT =>
    change 1 + (if (m i).1 == 1 then ofDecisionTree ifTrue
      else ofDecisionTree ifFalse).probes m =
      cond (memToBool m i) (ifTrue.cost (memToBool m)) (ifFalse.cost (memToBool m)) + 1
    cases hbit : memToBool m i <;> simp only [memToBool] at hbit <;>
      simp only [hbit, Bool.false_eq_true, ↓reduceIte, ihF, ihT, Bool.cond_false,
        Bool.cond_true] <;> omega

@[simp]
theorem probedCells_ofDecisionTree {S : ℕ} {α : Type} (t : DecisionTree (Fin S) α) (m : Mem S 1) :
    (ofDecisionTree t).probedCells m = t.queries (memToBool m) := by
  induction t with
  | leaf a => rfl
  | node i ifFalse ifTrue ihF ihT =>
    change insert i ((if (m i).1 == 1 then ofDecisionTree ifTrue
      else ofDecisionTree ifFalse).probedCells m) =
      insert i (cond (memToBool m i) (ifTrue.queries (memToBool m)) (ifFalse.queries (memToBool m)))
    cases hbit : memToBool m i <;> simp only [memToBool] at hbit <;> simp [hbit, ihF, ihT]

@[simp]
theorem depth_ofDecisionTree {S : ℕ} {α : Type} (t : DecisionTree (Fin S) α) :
    (ofDecisionTree t).depth = t.depth := by
  induction t with
  | leaf a => rfl
  | node i ifFalse ifTrue ihF ihT =>
    change (Finset.univ : Finset (Fin (2 ^ 1))).sup (fun v : Fin (2 ^ 1) =>
      (if v.1 == 1 then ofDecisionTree ifTrue else ofDecisionTree ifFalse).depth) + 1 =
      max ifFalse.depth ifTrue.depth + 1
    have huniv : (Finset.univ : Finset (Fin (2 ^ 1))) = {⟨0, by decide⟩, ⟨1, by decide⟩} := by
      ext ⟨v, hv⟩
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, true_iff]
      omega
    rw [huniv]
    simp only [Finset.sup_insert, Finset.sup_singleton]
    have h0 : ((⟨0, by decide⟩ : Fin (2 ^ 1)).1 == 1) = false := rfl
    have h1 : ((⟨1, by decide⟩ : Fin (2 ^ 1)).1 == 1) = true := rfl
    simp only [h0, Bool.false_eq_true, ↓reduceIte, h1, ihF, ihT, Nat.max_def]

end ProbeTree

end Cslib.CellProbe

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Spec
public import Complexity.DataStructure.StateTransition.Refinement

/-!
# Records of named cells over the memory oracle

A data structure with a fixed shape, such as a struct of arrays, stores its words in named cells:
`key v`, `par v`, a counter. `Record.spec ok w` is the interface to such a record. Its state gives
each cell of a type `ι` a value; an operation reads or writes one cell. The predicate `ok` says
which cells exist (for instance `v < n` for an array of length `n`), and admissibility asks that
an accessed cell exist and that a written value fit a `w`-bit word.

A data structure is then a program over its record (`Record.Prog`), and its proofs see named
cells rather than addresses. `Record.wp` is the weakest precondition of such a program under a
postcondition on its answer, its final record and its number of operations. It evaluates by
`simp` one operation at a time (`wp_read_bind`, `wp_write_bind`), composes (`wp_bind`), and
determines admissibility, answer, final state and cost of the run (`wp_iff`).

A `Record.Layout` places the cells in memory: an address for each cell, injective on the cells
that exist. `Record.refinement` implements the record over `Memory.spec w` by one memory operation
per record operation (`Record.amortized`). Address arithmetic, allocation and word-fit of addresses
are therefore proved once here, for every record.

## Main definitions

* `Record.Op`, `Record.step`, `Record.valid`, `Record.spec`: the record interface.
* `Record.Prog`, `Record.read`, `Record.write`: programs over a record.
* `Record.wp`: weakest precondition of a program, with the number of its operations.
* `Record.Layout`, `Record.Layout.abs`, `Record.Layout.Inv`: a placement in memory.
* `Record.refinement`: the record over the memory oracle.

## Main results

* `Record.wp_iff`: the weakest precondition is admissibility of the run together with the
  postcondition on its answer, final state and length.
* `Record.wp_bind`, `Record.wp_mono`: sequencing and consequence.
* `Record.amortized`: each record operation costs one memory unit.
-/

@[expose] public section

namespace Cslib.DataStructure.Record

open Cslib.WordRAM

variable {ι : Type}

/-- Operations on a record of cells indexed by `ι`. -/
inductive Op (ι : Type) where
  /-- Read a cell. -/
  | read (i : ι)
  /-- Write a value to a cell. -/
  | write (i : ι) (value : ℕ)

/-- A read returns the cell's value. -/
abbrev Op.Result : Op ι → Type
  | .read _ => ℕ
  | .write _ _ => Unit

variable [DecidableEq ι]

/-- The transition of each record operation. -/
def step (g : ι → ℕ) : (o : Op ι) → (ι → ℕ) × o.Result
  | .read i => (g, g i)
  | .write i v => (Function.update g i v, ())

/-- Admissibility: the accessed cell exists, and a written value fits a `w`-bit word. -/
def valid (ok : ι → Prop) (w : ℕ) (_ : ι → ℕ) : Op ι → Prop
  | .read i => ok i
  | .write i v => ok i ∧ Fits w v

/-- The record interface with cells `ok` at word size `w`. -/
abbrev spec (ok : ι → Prop) (w : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := ι → ℕ) (Op := Op ι) (Result := Op.Result) step (valid ok w)

/-- Programs over a record with cells indexed by `ι`. -/
abbrev Prog (ι : Type) (α : Type) : Type := PFunctor.FreeM ⟨Op ι, Op.Result⟩ α

/-- Read a cell. -/
abbrev read (i : ι) : Prog ι ℕ := PFunctor.FreeM.lift (P := ⟨Op ι, Op.Result⟩) (.read i)

/-- Write a value to a cell. -/
abbrev write (i : ι) (v : ℕ) : Prog ι Unit :=
  PFunctor.FreeM.lift (P := ⟨Op ι, Op.Result⟩) (.write i v)

/-! ## Weakest preconditions -/

variable {ok : ι → Prop} {w : ℕ} {α β : Type}

/-- The weakest precondition of `p` under `Q`: every operation of the run from `g` is admissible,
and `Q` holds of the answer, the final record and the number of operations. -/
def wp (ok : ι → Prop) (w : ℕ) : Prog ι α → (α → (ι → ℕ) → ℕ → Prop) → (ι → ℕ) → Prop
  | .pure a, Q, g => Q a g 0
  | .liftBind o k, Q, g =>
    valid ok w g o ∧ wp ok w (k (step g o).2) (fun a g' t => Q a g' (t + 1)) (step g o).1

@[simp] theorem wp_pure (a : α) (Q : α → (ι → ℕ) → ℕ → Prop) (g : ι → ℕ) :
    wp ok w (pure a : Prog ι α) Q g ↔ Q a g 0 := Iff.rfl

@[simp] theorem wp_read_bind (i : ι) (k : ℕ → Prog ι α) (Q : α → (ι → ℕ) → ℕ → Prop)
    (g : ι → ℕ) :
    wp ok w (read i >>= k) Q g ↔ ok i ∧ wp ok w (k (g i)) (fun a g' t => Q a g' (t + 1)) g :=
  Iff.rfl

@[simp] theorem wp_write_bind (i : ι) (v : ℕ) (k : Unit → Prog ι α)
    (Q : α → (ι → ℕ) → ℕ → Prop) (g : ι → ℕ) :
    wp ok w (write i v >>= k) Q g ↔
      (ok i ∧ Fits w v) ∧
        wp ok w (k ()) (fun a g' t => Q a g' (t + 1)) (Function.update g i v) :=
  Iff.rfl

@[simp] theorem wp_read (i : ι) (Q : ℕ → (ι → ℕ) → ℕ → Prop) (g : ι → ℕ) :
    wp ok w (read i) Q g ↔ ok i ∧ Q (g i) g 1 := Iff.rfl

@[simp] theorem wp_write (i : ι) (v : ℕ) (Q : Unit → (ι → ℕ) → ℕ → Prop) (g : ι → ℕ) :
    wp ok w (write i v) Q g ↔ (ok i ∧ Fits w v) ∧ Q () (Function.update g i v) 1 := Iff.rfl

/-- Consequence: a weaker postcondition. -/
theorem wp_mono {p : Prog ι α} {Q Q' : α → (ι → ℕ) → ℕ → Prop}
    (h : ∀ a g t, Q a g t → Q' a g t) {g : ι → ℕ} (hp : wp ok w p Q g) : wp ok w p Q' g := by
  induction p generalizing Q Q' g with
  | pure a => exact h _ _ _ hp
  | liftBind o k ih => exact ⟨hp.1, ih _ (fun a g' t => h a g' (t + 1)) hp.2⟩

/-- Sequencing: the cost of `p >>= k` is the cost of `p` plus the cost of `k`. -/
theorem wp_bind (p : Prog ι α) (k : α → Prog ι β) (Q : β → (ι → ℕ) → ℕ → Prop) (g : ι → ℕ) :
    wp ok w (p >>= k) Q g ↔
      wp ok w p (fun a g' t => wp ok w (k a) (fun b g'' t' => Q b g'' (t + t')) g') g := by
  induction p generalizing Q g with
  | pure a =>
    change wp ok w (k a) Q g ↔ wp ok w (k a) (fun b g'' t' => Q b g'' (0 + t')) g
    simp only [Nat.zero_add]
  | liftBind o f ih =>
    change valid ok w g o ∧ wp ok w (f (step g o).2 >>= k) _ _ ↔ valid ok w g o ∧ wp ok w _ _ _
    rw [ih]
    refine and_congr_right fun _ => Iff.of_eq ?_
    congr
    funext a g' t
    congr
    funext b g'' t'
    rw [Nat.add_right_comm]

/-- The weakest precondition holds exactly when the run is admissible and `Q` holds of its answer,
final record and number of operations. -/
theorem wp_iff (p : Prog ι α) (Q : α → (ι → ℕ) → ℕ → Prop) (g : ι → ℕ) :
    wp ok w p Q g ↔
      (spec ok w).ValidHistory g ((spec ok w).clientHistory g p) ∧
        Q ((spec ok w).clientResult g p) ((spec ok w).clientState g p)
          ((spec ok w).clientHistory g p).length := by
  induction p generalizing Q g with
  | pure a => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | liftBind o k ih =>
    simp only [wp, ih, StateTransitionSpec.clientHistory, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState, StateTransitionSpec.runClient_liftBind,
      StateTransitionSpec.validHistory_cons, List.length_cons, and_assoc]

/-! ## Placement in memory -/

/-- A placement of the record's cells in memory: an address for each cell, injective on the
cells that exist. -/
structure Layout (ok : ι → Prop) where
  /-- The address of each cell. -/
  addr : ι → ℕ
  /-- Distinct existing cells have distinct addresses. -/
  addr_injOn : ∀ i j, ok i → ok j → addr i = addr j → i = j

namespace Layout

variable (L : Layout ok)

/-- The record operations as memory operations at the cells' addresses. -/
def methods (w : ℕ) : Methods (spec ok w) (Memory.spec w)
  | .read i => Memory.read (L.addr i)
  | .write i v => Memory.write (L.addr i) v

variable [DecidablePred ok]

/-- The record stored in memory; cells that do not exist read as `0`. -/
def abs (m : Memory.State) (i : ι) : ℕ := if ok i then m.mem (L.addr i) else 0

/-- Every existing cell is allocated. -/
def Inv (m : Memory.State) : Prop := ∀ i, ok i → L.addr i < m.frontier

/-- Writing an existing cell writes its address. -/
theorem abs_write {m : Memory.State} {i : ι} (hi : ok i) (v : ℕ) :
    L.abs ⟨Function.update m.mem (L.addr i) v, m.frontier⟩ = Function.update (L.abs m) i v := by
  funext j
  by_cases hj : ok j
  · by_cases hji : j = i
    · subst hji
      simp [abs, hj]
    · have ha : L.addr j ≠ L.addr i := fun h => hji (L.addr_injOn j i hj hi h)
      simp [abs, hj, hji, Function.update_of_ne ha]
  · have hji : j ≠ i := fun h => hj (h ▸ hi)
    simp [abs, hj, hji]

end Layout

/-- The record over the memory oracle: each operation is the memory operation at the cell's
address. -/
def refinement [DecidablePred ok] (L : Layout ok) (w : ℕ) :
    Refinement (spec ok w) (Memory.spec w) :=
  Refinement.ofFn (L.methods w) L.Inv L.abs
    (by
      intro m o hm hv
      cases o with
      | read i => exact ⟨hm i hv, trivial⟩
      | write i v => exact ⟨⟨hm i hv.1, hv.2⟩, trivial⟩)
    (by
      intro m o hm hv
      cases o with
      | read i =>
        refine ⟨?_, hm⟩
        simp [Layout.methods, Layout.abs, StateTransitionSpec.clientState,
          StateTransitionSpec.clientResult, step, show ok i from hv]
      | write i v =>
        refine ⟨?_, hm⟩
        simp only [Layout.methods, StateTransitionSpec.clientState,
          StateTransitionSpec.clientResult, StateTransitionSpec.runClient_lift,
          StateTransitionSpec.stepFn, Memory.step_write, step]
        rw [L.abs_write hv.1])

/-- Each record operation costs one memory unit; no potential is needed. -/
theorem amortized [DecidablePred ok] (L : Layout ok) (w : ℕ) :
    (refinement L w).Amortized Memory.charge (fun _ _ => 1) fun _ => 0 := by
  apply Refinement.Amortized.ofFn
  intro m o _ _
  cases o <;> simp [refinement, Layout.methods, StateTransitionSpec.clientHistory]

end Cslib.DataStructure.Record

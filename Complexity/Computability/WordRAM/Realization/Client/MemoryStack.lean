/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Bind
public import Complexity.Computability.WordRAM.Realization.Branch
public import Complexity.Computability.WordRAM.Realization.Glue
public import Complexity.Computability.WordRAM.Realization.GlueVector
public import Complexity.Computability.WordRAM.Realization.Primitive
public import Complexity.DataStructure.Stack.Memory

/-!
# Native realizations of the memory-oracle stack

The certificates consume the existing `Stack.Memory` methods unchanged. Every field of the
runtime layout has a faithful word encoding, so the emitter is chosen before the layout's
allocation addresses and all operation arguments. Arithmetic, copies, binds and branches have
explicit local-work charges in addition to the actual memory history.

## Main definitions

* `layoutWords`, `pushWords`: faithful encodings of the complete layout and push arguments.

## Main results

* `realizes_size`, `realizes_push`, `realizes_pop`: uniform native realizations of the existing
  stack methods.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryStack

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) := (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

/-- All four layout fields are retained: count base/length, then items base/length. -/
def layoutWords : Stack.Memory.Layout ↪ (Fin 4 → ℕ) where
  toFun L := ![L.count.base, L.count.length, L.items.base, L.items.length]
  inj' := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ h
    have ha := congrFun h 0
    have hb := congrFun h 1
    have hc := congrFun h 2
    have hd := congrFun h 3
    change a = a' at ha
    change b = b' at hb
    change c = c' at hc
    change d = d' at hd
    cases ha; cases hb; cases hc; cases hd
    rfl

/-- Push arguments append the unshifted value to the complete runtime layout. -/
def pushWords : Stack.Memory.Layout × ℕ ↪ (Fin 5 → ℕ) :=
  (layoutWords.prodMap (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
    (Fin.appendEquiv 4 1).toEmbedding

private def append {δ α : Type} {k l : ℕ} (input : δ ↪ (Fin k → ℕ))
    (answer : α ↪ (Fin l → ℕ)) : δ × α ↪ (Fin (k + l) → ℕ) :=
  (input.prodMap answer).trans (Fin.appendEquiv k l).toEmbedding

private theorem addWords {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) (i j : Fin k) :
    Realizes .exact (fun d => pure (input d i + input d j)) input word
      (fun w d _ => Fits w (input d i + input d j)) (fun _ _ => 3) := by
  have ha : GlueComputes .exact (fun _ : Fin k → ℕ => True) (fun v => v i)
      (fun v => v i + v j) 1 := GlueComputes.proj i (fun _ _ => Nat.le_add_right _ _)
  have hb : GlueComputes .exact (fun _ : Fin k → ℕ => True) (fun v => v j)
      (fun v => v i + v j) 1 := GlueComputes.proj j (fun _ _ => Nat.le_add_left _ _)
  have h := Realizes.glue input (ha.bin_exact hb .add (fun _ _ => rfl) (fun _ _ => le_rfl))
  exact h.consequence (fun _ _ _ _ _ hf => ⟨trivial, hf⟩) (fun _ _ => le_rfl)

private theorem increment {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) (i : Fin k) :
    Realizes .exact (fun d => pure (input d i + 1)) input word
      (fun w d _ => Fits w (input d i + 1)) (fun _ _ => 3) := by
  have ha : GlueComputes .exact (fun _ : Fin k → ℕ => True) (fun v => v i)
      (fun v => v i + 1) 1 := GlueComputes.proj i (fun _ _ => Nat.le_add_right _ _)
  have hb : GlueComputes .exact (fun _ : Fin k → ℕ => True) (fun _ => 1)
      (fun v => v i + 1) 1 := GlueComputes.const 1 (fun _ _ => by omega)
  have h := Realizes.glue input (ha.bin_exact hb .add (fun _ _ => rfl) (fun _ _ => le_rfl))
  exact h.consequence (fun _ _ _ _ _ hf => ⟨trivial, hf⟩) (fun _ _ => le_rfl)

private theorem decrement {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) (i : Fin k) :
    Realizes .exact (fun d => pure (input d i - 1)) input word
      (fun w d _ => 1 ≤ input d i ∧ Fits w (input d i)) (fun _ _ => 3) := by
  have ha : GlueComputes .exact (fun v : Fin k → ℕ => 1 ≤ v i) (fun v => v i)
      (fun v => v i) 1 := GlueComputes.proj i (fun _ _ => le_rfl)
  have hb : GlueComputes .exact (fun v : Fin k → ℕ => 1 ≤ v i) (fun _ => 1)
      (fun v => v i) 1 := GlueComputes.const 1 (fun _ h => h)
  exact Realizes.glue input (ha.bin_exact hb .sub
    (fun v h => by simp [h]) (fun _ _ => Nat.sub_le _ _))

private theorem returnNone {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) :
    Realizes .exact (fun _ => pure none) input optionWords
      (fun _ _ _ => True) (fun _ _ => 4) := by
  have h := Realizes.glueVector (B := .exact) input optionWords (fun _ => none)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1)
    (fun _ i => by fin_cases i <;> rfl)
    (P := fun _ => True) (fun _ => GlueComputes.const 0 (fun _ _ => le_rfl))
  exact h.consequence (fun w _ _ _ _ _ => ⟨trivial, fun _ => fits_zero w⟩)
    (fun _ _ => by simp)

private theorem returnSome {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) (j : Fin k) :
    Realizes .exact (fun d => pure (some (input d j))) input optionWords
      (fun w d _ => Fits w 1 ∧ Fits w (input d j)) (fun _ _ => 4) := by
  let g : Fin 2 → (Fin k → ℕ) → ℕ := fun i v => if i = 0 then 1 else v j
  have hc (i : Fin 2) : GlueComputes .exact (fun _ : Fin k → ℕ => True) (g i) (g i) 1 := by
    fin_cases i
    · exact GlueComputes.const 1 (fun _ _ => le_rfl)
    · exact GlueComputes.proj j (fun _ _ => le_rfl)
  have h := Realizes.glueVector input optionWords (fun d => some (input d j)) g g
    (fun _ => 1) (fun _ i => by fin_cases i <;> rfl) hc
  apply h.consequence (hwork := fun _ _ => by simp)
  intro w d s _ _ ⟨h1, hv⟩
  refine ⟨trivial, fun i => ?_⟩
  fin_cases i
  · exact h1
  · exact hv

/-- Size uses the existing count query with no additional local computation. -/
theorem realizes_size :
    Realizes .exact Stack.Memory.size layoutWords
      (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.read layoutWords 0

/-- Push works uniformly for every runtime layout and value. The visible invariant and spare
capacity discharge the address and increment fit obligations. The two additions cost six local
instructions; four bind rules contribute four units of local control work. -/
theorem realizes_push :
    Realizes .exact (fun d : Stack.Memory.Layout × ℕ => Stack.Memory.push d.1 d.2)
      pushWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => d.1.Valid w d.1.items.length ∧ Stack.Memory.Inv d.1 s ∧
        s.mem d.1.count.base < d.1.items.length) (fun _ _ => 10) := by
  let e₁ := append pushWords word
  let e₂ := append e₁ word
  let e₃ := append e₂ word
  let e₄ := append e₃ unitWords
  have hread : Realizes .exact (fun d : Stack.Memory.Layout × ℕ => Memory.read d.1.count.base)
      pushWords word (fun _ _ _ => True) (fun _ _ => 0) := Realizes.read pushWords 0
  have haddr : Realizes .exact
      (fun d : (Stack.Memory.Layout × ℕ) × ℕ => pure (d.1.1.items.base + d.2))
      e₁ word (fun w d _ => Fits w (d.1.1.items.base + d.2)) (fun _ _ => 3) :=
    addWords e₁ 2 5
  have hnext : Realizes .exact
      (fun d : ((Stack.Memory.Layout × ℕ) × ℕ) × ℕ => pure (d.1.2 + 1))
      e₂ word (fun w d _ => Fits w (d.1.2 + 1)) (fun _ _ => 3) := increment e₂ 5
  have hwrite : Realizes .exact
      (fun d : (((Stack.Memory.Layout × ℕ) × ℕ) × ℕ) × ℕ =>
        Memory.write d.1.2 d.1.1.1.2)
      e₃ unitWords (fun _ _ _ => True) (fun _ _ => 0) := Realizes.write e₃ 6 4
  have hcount : Realizes .exact
      (fun d : ((((Stack.Memory.Layout × ℕ) × ℕ) × ℕ) × ℕ) × Unit =>
        Memory.write d.1.1.1.1.1.count.base d.1.2)
      e₄ unitWords (fun _ _ _ => True) (fun _ _ => 0) := Realizes.write e₄ 0 7
  have hwrites := (Realizes.bind hwrite hcount).consequence
    (safe' := fun _ _ _ => True) (work' := fun _ _ => 1)
    (fun _ _ _ _ _ _ => ⟨trivial, trivial⟩) (fun _ _ => le_rfl)
  have hinc := (Realizes.bind hnext hwrites).consequence
    (safe' := fun w d _ => Fits w (d.1.2 + 1)) (work' := fun _ _ => 5)
    (fun _ _ _ _ _ h => ⟨h, trivial⟩) (fun _ _ => le_rfl)
  have hcompute := (Realizes.bind haddr hinc).consequence
    (safe' := fun w d _ => Fits w (d.1.1.items.base + d.2) ∧ Fits w (d.2 + 1))
    (work' := fun _ _ => 9) (fun _ _ _ _ _ h => h) (fun _ _ => le_rfl)
  apply (Realizes.bind hread hcompute).consequence (hwork := fun _ _ => le_rfl)
  intro w d s _ hw ⟨hL, hInv, hcap⟩
  change True ∧ Fits w (d.1.items.base + s.mem d.1.count.base) ∧
    Fits w (s.mem d.1.count.base + 1)
  exact ⟨trivial, hw.fits_of_lt_frontier (hInv.item_lt hcap),
    hL.capacity_fits.of_le (by omega)⟩

/-- Pop returns a presence tag and unshifted payload. Its positive branch uses defined exact
subtraction and performs the existing memory reads/write. All copies and branch/bind overhead
are charged; the local-work allowance is 19 for either path, including the shorter empty path. -/
theorem realizes_pop :
    Realizes .exact Stack.Memory.pop layoutWords optionWords
      (fun w L s => L.Valid w L.items.length ∧ Stack.Memory.Inv L s) (fun _ _ => 19) := by
  let e₁ := append layoutWords word
  let e₂ := append e₁ word
  let e₃ := append e₂ word
  let e₄ := append e₃ word
  let e₅ := append e₄ word
  let e₆ := append e₅ unitWords
  have hread : Realizes .exact (fun L : Stack.Memory.Layout => Memory.read L.count.base)
      layoutWords word (fun _ _ _ => True) (fun _ _ => 0) := Realizes.read layoutWords 0
  have hzero : Realizes .exact (fun _ : Stack.Memory.Layout × ℕ => pure 0) e₁ word
      (fun _ _ _ => True) (fun _ _ => 1) := by
    have h := Realizes.glue e₁
      (GlueComputes.const (B := .exact) (P := fun _ => True) (bound := fun _ => 0)
        0 (fun _ _ => le_rfl))
    exact h.consequence (fun w _ _ _ _ _ => ⟨trivial, fits_zero w⟩) (fun _ _ => le_rfl)
  have hsub : Realizes .exact
      (fun d : (Stack.Memory.Layout × ℕ) × ℕ => pure (d.1.2 - 1)) e₂ word
      (fun w d _ => 1 ≤ d.1.2 ∧ Fits w d.1.2) (fun _ _ => 3) := decrement e₂ 4
  have haddr : Realizes .exact
      (fun d : ((Stack.Memory.Layout × ℕ) × ℕ) × ℕ => pure (d.1.1.1.items.base + d.2))
      e₃ word (fun w d _ => Fits w (d.1.1.1.items.base + d.2)) (fun _ _ => 3) :=
    addWords e₃ 2 6
  have hitem : Realizes .exact
      (fun d : (((Stack.Memory.Layout × ℕ) × ℕ) × ℕ) × ℕ => Memory.read d.2)
      e₄ word (fun _ _ _ => True) (fun _ _ => 0) := Realizes.read e₄ 7
  have hwrite : Realizes .exact
      (fun d : ((((Stack.Memory.Layout × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        Memory.write d.1.1.1.1.1.count.base d.1.1.2)
      e₅ unitWords (fun _ _ _ => True) (fun _ _ => 0) := Realizes.write e₅ 0 6
  have hsome : Realizes .exact
      (fun d : (((((Stack.Memory.Layout × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × Unit =>
        pure (some d.1.2)) e₆ optionWords
      (fun w d _ => Fits w 1 ∧ Fits w d.1.2) (fun _ _ => 4) := returnSome e₆ 8
  have hpos := (Realizes.bind hsub (Realizes.bind haddr
    (Realizes.bind hitem (Realizes.bind hwrite hsome)))).consequence
    (safe' := fun w d s => 1 ≤ d.1.2 ∧ Fits w d.1.2 ∧
      Fits w (d.1.1.items.base + (d.1.2 - 1)) ∧ Fits w 1 ∧
      Fits w (s.mem (d.1.1.items.base + (d.1.2 - 1))))
    (work' := fun _ _ => 14)
    (by
      intro w d s _ _ ⟨hpos, hn, ha, h1, hv⟩
      change (1 ≤ d.1.2 ∧ Fits w d.1.2) ∧
        Fits w (d.1.1.items.base + (d.1.2 - 1)) ∧ True ∧ True ∧
        Fits w 1 ∧ Fits w (s.mem (d.1.1.items.base + (d.1.2 - 1)))
      exact ⟨⟨hpos, hn⟩, ha, trivial, trivial, h1, hv⟩)
    (fun _ _ => le_rfl)
  have hbranch := Realizes.branch (.eq 4 5) (returnNone e₂) hpos
  apply (Realizes.bind hread (Realizes.bind hzero hbranch)).consequence
  · intro w L s hwords hw ⟨hL, hInv⟩
    have hn : Fits w (s.mem L.count.base) := hw.mem_fits _
    have h1 : Fits w 1 := hL.count_length ▸ hwords 1
    change True ∧ True ∧ (if s.mem L.count.base = 0 then True else
      1 ≤ s.mem L.count.base ∧ Fits w (s.mem L.count.base) ∧
      Fits w (L.items.base + (s.mem L.count.base - 1)) ∧ Fits w 1 ∧
      Fits w (s.mem (L.items.base + (s.mem L.count.base - 1))))
    refine ⟨trivial, trivial, ?_⟩
    split
    · trivial
    · have hle := hInv.count_le
      exact ⟨by omega, hn, hw.fits_of_lt_frontier (hInv.item_lt (by omega)), h1,
        hw.mem_fits _⟩
  · intro L s
    change 0 + (1 + ((if test (.eq 4 5) (e₂ ((L,
      (Memory.spec 0).clientResult s (Memory.read L.count.base)), 0)) then 4 else 14) + 2) + 1) +
      1 ≤ 19
    split <;> omega

/-- The push's explicit local work is dominated by its actual three-query memory charge. -/
theorem push_work_bound (L : Stack.Memory.Layout) (v : ℕ) (s : Memory.State) :
    10 ≤ 4 * memoryCost (Stack.Memory.push L v) s := by
  change 10 ≤ 4 * 3
  decide

/-- Even the empty pop has a memory query. This domination uses the actual method history,
after separately certifying all 19 units of local work, and is not a general query-only rule. -/
theorem pop_work_bound (L : Stack.Memory.Layout) (s : Memory.State) :
    19 ≤ 19 * memoryCost (Stack.Memory.pop L) s := by
  by_cases h : s.mem L.count.base = 0
  · simp [memoryCost, StateTransitionSpec.clientHistory, Stack.Memory.runClient_pop_of_eq_zero,
      h, StateTransitionSpec.totalCost, Memory.charge]
  · simp [memoryCost, StateTransitionSpec.clientHistory, Stack.Memory.runClient_pop_of_pos,
      h, StateTransitionSpec.totalCost, Memory.charge]

end Cslib.WordRAM.Realization.MemoryStack

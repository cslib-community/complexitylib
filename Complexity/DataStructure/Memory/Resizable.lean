/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Resizable.Basic
public import Complexity.DataStructure.Memory.Field
public import Complexity.DataStructure.StateTransition.Refinement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Log

/-!
# Word-granular resizable memory specification

Word-granular resizable memory specification (`Cslib.DataStructure.Memory.Resizable`) accompanying
the **Resizable Word RAM** (`Cslib.WordRAM.Resizable`), modeling the dynamically resizable `w`-bit
word memory of [LiLiangYuZhou2023Succincter], Section 2.1, [LiLiangYuZhou2024], Section 3.2, and
[KuszmaulLiangZhou2026], Section 5.1 (termed the "virtual memory (VM) model" in those papers, with
1-indexed addresses `[1..M]` mapped here to 0-indexed `[0, s.frontier)`).

A data structure operating over word-granular resizable memory owns a 0-indexed active prefix
`[0, s.frontier)` of `w`-bit words in `s : Memory.State`, where `s.frontier` is the current number
of allocated words. In addition to reading and writing allocated words (`a < s.frontier`), a client
may **grow** (`grow k`, `growDirty k`) or **shrink** (`shrink k`) the active prefix by whole words.

## Main definitions

* `Cslib.DataStructure.Memory.Resizable.Op`: `read`, `write`, `grow`, `growDirty`, and `shrink`.
* `Cslib.DataStructure.Memory.Resizable.demonicStep`,
  `Cslib.DataStructure.Memory.Resizable.demonicSpec`: relational demonic specification at word
  width `w`, allowing arbitrary `w`-bit initial words in `[s.frontier, s.frontier + k)` on `grow`
  and `growDirty` ([KuszmaulLiangZhou2026], Section 5.1, Footnote 10).
* `Cslib.DataStructure.Memory.Resizable.step`, `Cslib.DataStructure.Memory.Resizable.spec`:
  deterministic zero-initialized specification (`HasStepFn`) at word width `w`.
* `Cslib.DataStructure.Memory.Resizable.spec_refines_demonicSpec`: refinement certificate
  `Refinement (demonicSpec w) (spec w)`.
* `Cslib.DataStructure.Memory.Resizable.charge`,
  `Cslib.DataStructure.Memory.Resizable.spaceWords`,
  `Cslib.DataStructure.Memory.Resizable.spaceBits`,
  `Cslib.DataStructure.Memory.Resizable.UnchangedOutside`: operation cost, live word/bit space
  measures, and resize-aware frame condition.

## Main results

* `Cslib.DataStructure.Memory.Resizable.canonical_step`,
  `Cslib.DataStructure.Memory.Resizable.canonical_demonicStep`: admissible transitions preserve
  `WellFormed w` and `ZeroAbove`.
* `Cslib.DataStructure.Memory.Resizable.demonicStep_grow_of_demonicGrow`: machine-level
  `WordRAM.Resizable.DemonicGrow` transitions satisfy `demonicStep w`.
* `Cslib.DataStructure.Memory.Resizable.Block.realizes_of_unchangedOutside`: `UnchangedOutside`
  preserves `Block.Realizes` across resizes.

## References

* [LiLiangYuZhou2023Succincter] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  "Succincter"*, FOCS 2023, pp. 1715–1733 (`arXiv:2309.12950v1`, Section 2.1).
* [LiLiangYuZhou2024] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  Dictionary with Subconstant Wasted Bits per Key*, SODA 2024 (`arXiv:2310.20536v1`, Section 3.2,
  PDF pp. 9–11 / printed pp. 8–10).
* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–19 / printed pp. 15–18, and Footnote 10, PDF p. 18 / printed p. 17).
-/

@[expose] public section

namespace Cslib.DataStructure.Memory.Resizable

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open scoped BigOperators

/-! ## Empty state and zero-above invariant -/

/-- The empty memory state with all cells zeroed and `frontier = 0`. -/
def emptyState : State := ⟨fun _ => 0, 0⟩

/-- Every address at or above `s.frontier` holds `0`. -/
def ZeroAbove (s : State) : Prop :=
  ∀ a, s.frontier ≤ a → s.mem a = 0

@[simp] theorem emptyState_frontier : emptyState.frontier = 0 := rfl

@[simp] theorem emptyState_mem (a : ℕ) : emptyState.mem a = 0 := rfl

theorem wellFormed_emptyState (w : ℕ) : WellFormed w emptyState :=
  ⟨fits_zero w, fun _ => fits_zero w⟩

theorem zeroAbove_emptyState : ZeroAbove emptyState := fun _ _ => rfl

/-! ## Operations, deterministic `spec w`, and relational `demonicSpec w` -/

/-- Operations of a word-granular resizable memory ([LiLiangYuZhou2023Succincter], Section 2.1;
[KuszmaulLiangZhou2026], Section 5.1). -/
inductive Op where
  /-- Read the `w`-bit word at address `a < frontier`. -/
  | read (a : ℕ)
  /-- Write the `w`-bit word `v` at address `a < frontier`. -/
  | write (a v : ℕ)
  /-- Grow `[0, frontier)` by `k` zeroed words to `[0, frontier + k)`, returning old `frontier`. -/
  | grow (k : ℕ)
  /-- Grow `[0, frontier)` by `k` uninitialized words, returning old `frontier`. -/
  | growDirty (k : ℕ)
  /-- Shrink `[0, frontier)` by `k ≤ frontier` words, clearing `[frontier - k, frontier)`. -/
  | shrink (k : ℕ)
  deriving DecidableEq, Repr

/-- Result type of each resizable-memory operation. -/
abbrev Op.Result : Op → Type
  | .read _ => ℕ
  | .write _ _ => Unit
  | .grow _ => ℕ
  | .growDirty _ => ℕ
  | .shrink _ => Unit

/-- Deterministic zero-initialized transition function on `Memory.State`. -/
def step (s : State) : (o : Op) → State × o.Result
  | .read a => (s, s.mem a)
  | .write a v => (⟨Function.update s.mem a v, s.frontier⟩, ())
  | .grow k => (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier)
  | .growDirty k => (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier)
  | .shrink k => (⟨clear s.mem (s.frontier - k) k, s.frontier - k⟩, ())

/-- Admissibility precondition at word width `w`. -/
def valid (w : ℕ) (s : State) : Op → Prop
  | .read a => a < s.frontier
  | .write a v => a < s.frontier ∧ Fits w v
  | .grow k => Fits w (s.frontier + k)
  | .growDirty k => Fits w (s.frontier + k)
  | .shrink k => k ≤ s.frontier

instance (w : ℕ) (s : State) (o : Op) : Decidable (valid w s o) := by
  cases o <;> unfold valid <;> infer_instance

/-- Deterministic zero-initialized word-granular resizable memory specification
at word width `w`. -/
abbrev spec (w : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := State) (Op := Op) (Result := Op.Result) step (valid w)

/-- Admissibility of a concrete history on `Resizable.spec w` is decidable. -/
instance decidableValidHistory (w : ℕ) (s : State) (os : List Op) :
    Decidable ((spec w).ValidHistory s os) := by
  induction os generalizing s with
  | nil => exact isTrue trivial
  | cons o os ih =>
    exact decidable_of_iff (valid w s o ∧ (spec w).ValidHistory (step s o).1 os) Iff.rfl

/-- Demonic relational transition at word width `w`: `.grow k` and `.growDirty k` permit any
post-state `s'` preserving `s.mem` outside `[s.frontier, s.frontier + k)` and placing arbitrary
`w`-bit words in `[s.frontier, s.frontier + k)` ([KuszmaulLiangZhou2026], Section 5.1). -/
def demonicStep (w : ℕ) (s : State) : (o : Op) → State → o.Result → Prop
  | .read a, s', r => s' = s ∧ r = s.mem a
  | .write a v, s', _ => s' = ⟨Function.update s.mem a v, s.frontier⟩
  | .grow k, s', r =>
      s'.frontier = s.frontier + k ∧ r = s.frontier ∧
        (∀ a, a < s.frontier ∨ s.frontier + k ≤ a → s'.mem a = s.mem a) ∧
        (∀ a, s.frontier ≤ a → a < s.frontier + k → Fits w (s'.mem a))
  | .growDirty k, s', r =>
      s'.frontier = s.frontier + k ∧ r = s.frontier ∧
        (∀ a, a < s.frontier ∨ s.frontier + k ≤ a → s'.mem a = s.mem a) ∧
        (∀ a, s.frontier ≤ a → a < s.frontier + k → Fits w (s'.mem a))
  | .shrink k, s', _ => s' = ⟨clear s.mem (s.frontier - k) k, s.frontier - k⟩

/-- Demonic relational word-granular resizable memory specification at word width `w`. -/
def demonicSpec (w : ℕ) : StateTransitionSpec where
  State := State
  Op := Op
  Result := Op.Result
  step := demonicStep w
  valid := valid w

/-! ## Effectful program primitives -/

/-- A program over the word-granular resizable memory oracle. -/
abbrev Prog (α : Type) : Type := PFunctor.FreeM ⟨Op, Op.Result⟩ α

/-- Read the word at address `a`. -/
abbrev read (a : ℕ) : Prog ℕ := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.read a)

/-- Write `v` to address `a`. -/
abbrev write (a v : ℕ) : Prog Unit := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.write a v)

/-- Grow the active prefix by `k` zeroed words, returning the old `frontier`. -/
abbrev grow (k : ℕ) : Prog ℕ := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.grow k)

/-- Grow the active prefix by `k` uninitialized words, returning the old `frontier`. -/
abbrev growDirty (k : ℕ) : Prog ℕ := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.growDirty k)

/-- Shrink the active prefix by `k` words. -/
abbrev shrink (k : ℕ) : Prog Unit := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.shrink k)

/-- Allocate a single zeroed word at `frontier`. -/
abbrev allocWord : Prog ℕ := grow 1

/-- Allocate a single uninitialized word at `frontier`. -/
abbrev allocWordDirty : Prog ℕ := growDirty 1

/-- Release a single word from `frontier`. -/
abbrev releaseWord : Prog Unit := shrink 1

@[simp] theorem step_read (s : State) (a : ℕ) : step s (.read a) = (s, s.mem a) := rfl
@[simp] theorem step_write (s : State) (a v : ℕ) :
    step s (.write a v) = (⟨Function.update s.mem a v, s.frontier⟩, ()) := rfl
@[simp] theorem step_grow (s : State) (k : ℕ) :
    step s (.grow k) = (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier) := rfl
@[simp] theorem step_growDirty (s : State) (k : ℕ) :
    step s (.growDirty k) = (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier) := rfl
@[simp] theorem step_shrink (s : State) (k : ℕ) :
    step s (.shrink k) = (⟨clear s.mem (s.frontier - k) k, s.frontier - k⟩, ()) := rfl

@[simp] theorem valid_read (w : ℕ) (s : State) (a : ℕ) : valid w s (.read a) ↔ a < s.frontier :=
  Iff.rfl
@[simp] theorem valid_write (w : ℕ) (s : State) (a v : ℕ) :
    valid w s (.write a v) ↔ a < s.frontier ∧ Fits w v := Iff.rfl
@[simp] theorem valid_grow (w : ℕ) (s : State) (k : ℕ) :
    valid w s (.grow k) ↔ Fits w (s.frontier + k) := Iff.rfl
@[simp] theorem valid_growDirty (w : ℕ) (s : State) (k : ℕ) :
    valid w s (.growDirty k) ↔ Fits w (s.frontier + k) := Iff.rfl
@[simp] theorem valid_shrink (w : ℕ) (s : State) (k : ℕ) :
    valid w s (.shrink k) ↔ k ≤ s.frontier := Iff.rfl

/-! ## Well-formedness and canonical state preservation -/

/-- A resizable memory state is canonical at word width `w` when all words and the frontier fit in
`w` bits (`WellFormed w s`) and all unallocated addresses `a ≥ s.frontier` hold `0`
(`ZeroAbove s`). -/
def Canonical (w : ℕ) (s : State) : Prop :=
  WellFormed w s ∧ ZeroAbove s

theorem canonical_emptyState (w : ℕ) : Canonical w emptyState :=
  ⟨wellFormed_emptyState w, zeroAbove_emptyState⟩

/-- When `ZeroAbove s` holds, clearing `[s.frontier, s.frontier + k)` is a no-op. -/
theorem clear_frontier_eq_of_zeroAbove {s : State} (hs : ZeroAbove s) (k : ℕ) :
    clear s.mem s.frontier k = s.mem := by
  funext a
  by_cases ha : (Block.mk s.frontier k).Owns a
  · rw [clear_of_owns ha, hs a ha.1]
  · exact clear_of_not_owns ha

/-- Every valid operation preserves `WellFormed w`. -/
theorem wellFormed_step {w : ℕ} {s : State} {o : Op}
    (hs : WellFormed w s) (hv : valid w s o) :
    WellFormed w (step s o).1 := by
  cases o with
  | read _ => exact hs
  | write a v => exact hs.step (o := .write a v) hv
  | grow k | growDirty k => exact hs.step (o := .alloc k) hv
  | shrink k =>
    refine ⟨hs.frontier_fits.of_le (Nat.sub_le _ _), fun a => ?_⟩
    dsimp only [step]
    by_cases ha : (Block.mk (s.frontier - k) k).Owns a
    · rw [clear_of_owns ha]; exact fits_zero w
    · rw [clear_of_not_owns ha]; exact hs.mem_fits a

/-- Every valid operation preserves `ZeroAbove`. -/
theorem zeroAbove_step {w : ℕ} {s : State} {o : Op}
    (hs : ZeroAbove s) (hv : valid w s o) :
    ZeroAbove (step s o).1 := by
  cases o with
  | read _ => exact hs
  | write a v =>
    intro b hb
    dsimp only [step] at hb ⊢
    have hba : b ≠ a := by have : a < s.frontier := hv.1; omega
    rw [Function.update_of_ne hba]
    exact hs b hb
  | grow k | growDirty k =>
    intro b hb
    dsimp only [step] at hb ⊢
    by_cases hown : (Block.mk s.frontier k).Owns b
    · exact clear_of_owns hown
    · rw [clear_of_not_owns hown]; exact hs b (by omega)
  | shrink k =>
    intro b hb
    dsimp only [step] at hb ⊢
    have hle : k ≤ s.frontier := hv
    by_cases hlt : b < s.frontier
    · exact clear_of_owns (by simp only [Block.Owns]; omega)
    · rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]; exact hs b (by omega)

/-- Every valid operation preserves `Canonical w`. -/
theorem canonical_step {w : ℕ} {s : State} {o : Op}
    (hs : Canonical w s) (hv : valid w s o) :
    Canonical w (step s o).1 :=
  ⟨wellFormed_step hs.1 hv, zeroAbove_step hs.2 hv⟩

/-- Every valid transition of `demonicStep w` preserves `WellFormed w`. -/
theorem wellFormed_demonicStep {w : ℕ} {s s' : State} {o : Op} {r : o.Result}
    (hs : WellFormed w s) (hv : valid w s o) (hstep : demonicStep w s o s' r) :
    WellFormed w s' := by
  cases o with
  | read _ => rcases hstep with ⟨rfl, -⟩; exact hs
  | write a v => subst hstep; exact hs.step (o := .write a v) hv
  | grow k | growDirty k =>
    rcases hstep with ⟨hfront, -, hout, hin⟩
    refine ⟨hfront.symm ▸ hv, fun a => ?_⟩
    by_cases ha : s.frontier ≤ a ∧ a < s.frontier + k
    · exact hin a ha.1 ha.2
    · rw [hout a (by omega)]; exact hs.mem_fits a
  | shrink k => subst hstep; exact wellFormed_step (o := .shrink k) hs hv

/-- Every valid transition of `demonicStep w` preserves `ZeroAbove`. -/
theorem zeroAbove_demonicStep {w : ℕ} {s s' : State} {o : Op} {r : o.Result}
    (hs : ZeroAbove s) (hv : valid w s o) (hstep : demonicStep w s o s' r) :
    ZeroAbove s' := by
  cases o with
  | read _ => rcases hstep with ⟨rfl, -⟩; exact hs
  | write a v => subst hstep; exact zeroAbove_step (o := .write a v) hs hv
  | grow k | growDirty k =>
    rcases hstep with ⟨hfront, -, hout, -⟩
    intro a ha
    rw [hfront] at ha
    rw [hout a (Or.inr ha)]
    exact hs a (by omega)
  | shrink k => subst hstep; exact zeroAbove_step (o := .shrink k) hs hv

/-- Every valid transition of `demonicStep w` preserves `Canonical w`. -/
theorem canonical_demonicStep {w : ℕ} {s s' : State} {o : Op} {r : o.Result}
    (hs : Canonical w s) (hv : valid w s o) (hstep : demonicStep w s o s' r) :
    Canonical w s' :=
  ⟨wellFormed_demonicStep hs.1 hv hstep, zeroAbove_demonicStep hs.2 hv hstep⟩

/-! ## Refinement `spec_refines_demonicSpec` and lifting `Memory.Prog` -/

/-- Every deterministic `step` transition satisfies `demonicStep w`. -/
theorem demonicStep_of_step (w : ℕ) (s : State) (o : Op) :
    demonicStep w s o (step s o).1 (step s o).2 := by
  cases o with
  | read _ => exact ⟨rfl, rfl⟩
  | write _ _ | shrink _ => rfl
  | grow k | growDirty k =>
    refine ⟨rfl, rfl, fun a ha => clear_of_not_owns (by simp only [Block.Owns]; omega), ?_⟩
    intro a hlo hhi
    dsimp only [step]
    rw [clear_of_owns ⟨hlo, hhi⟩]
    exact fits_zero w

/-- Any machine-level `WordRAM.Resizable.DemonicGrow` transition from a `ZeroAbove` state satisfies
`demonicStep w s (.grow k)`. -/
theorem demonicStep_grow_of_demonicGrow {w k : ℕ} {s s' : State}
    (hs : ZeroAbove s) (hfront : s'.frontier = s.frontier + k)
    (hg : WordRAM.Resizable.DemonicGrow w s.frontier k s.mem s'.mem) :
    demonicStep w s (.grow k) s' s.frontier := by
  refine ⟨hfront, rfl, fun a ha => ?_, hg.2.1⟩
  rcases ha with hlt | hge
  · exact hg.1 a hlt
  · rw [hg.2.2 a hge, hs a (by omega)]

/-- The zero-initialized specification `spec w` refines `demonicSpec w` over the identity state
map: every client verified against `demonicSpec w` is valid and has its behavior included in
`demonicSpec w` when executed on `spec w`. -/
def spec_refines_demonicSpec (w : ℕ) : Refinement (demonicSpec w) (spec w) where
  methods o := .liftBind o fun a => .pure a
  inv _ := True
  abs s := s
  valid o _ hv :=
    StateTransitionSpec.DemonicValid.liftBind (D := spec w) o _ hv fun s' a _ =>
      StateTransitionSpec.DemonicValid.pure s' a
  correct {e} o {_ _ _} _ _ hrun := by
    cases hrun with
    | liftBind _ _ a _ hstep hrest =>
      cases hrest
      have hd := demonicStep_of_step w e o
      rw [← hstep] at hd
      exact ⟨hd, trivial⟩

/-- Lift a program written against grow-only `Memory.Prog` into `Resizable.Prog`. -/
def liftMemory {α : Type} : Memory.Prog α → Prog α
  | .pure a => .pure a
  | .liftBind (.read a) k => .liftBind (.read a) (fun r => liftMemory (k r))
  | .liftBind (.write a v) k => .liftBind (.write a v) (fun r => liftMemory (k r))
  | .liftBind (.alloc n) k => .liftBind (.grow n) (fun r => liftMemory (k r))
  | .liftBind (.allocDirty n) k => .liftBind (.growDirty n) (fun r => liftMemory (k r))

/-! ## Cost, live space measures, and resize-aware frame condition -/

/-- Operation cost measure (`charge`): `read`, `write`, and `growDirty` cost `1` unit; zeroed
`grow k` and `shrink k` cost `max k 1` units. -/
def charge (_ : State) : Op → ℕ
  | .read _ | .write _ _ | .growDirty _ => 1
  | .grow k | .shrink k => max k 1

@[simp] theorem charge_read (s : State) (a : ℕ) : charge s (.read a) = 1 := rfl
@[simp] theorem charge_write (s : State) (a v : ℕ) : charge s (.write a v) = 1 := rfl
@[simp] theorem charge_grow (s : State) (k : ℕ) : charge s (.grow k) = max k 1 := rfl
@[simp] theorem charge_growDirty (s : State) (k : ℕ) : charge s (.growDirty k) = 1 := rfl
@[simp] theorem charge_shrink (s : State) (k : ℕ) : charge s (.shrink k) = max k 1 := rfl

theorem one_le_charge (s : State) (o : Op) : 1 ≤ charge s o := by
  cases o <;> simp [charge]

/-- Current allocated space of `s` in `w`-bit words (`s.frontier`). -/
abbrev spaceWords (s : State) : ℕ := s.frontier

/-- Current allocated space of `s` in bits (`w * s.frontier`). -/
def spaceBits (w : ℕ) (s : State) : ℕ := w * s.frontier

/-- Total space in bits of `s.frontier` allocated words plus a spillover integer in `[0, K)`
([LiLiangYuZhou2023Succincter], Section 2.1; [KuszmaulLiangZhou2026], Section 5.1). -/
def spilloverSpaceBits (w K : ℕ) (s : State) : ℕ := w * s.frontier + Nat.clog 2 K

/-- Peak number of allocated words reached during execution of `p` from `s` on `spec`. -/
def peakWords {α : Type} (s : State) : Prog α → ℕ
  | .pure _ => s.frontier
  | .liftBind o k =>
      let res := step s o
      max s.frontier (peakWords res.1 (k res.2))

theorem frontier_le_peakWords {α : Type} (s : State) (p : Prog α) :
    s.frontier ≤ peakWords s p := by
  cases p <;> [exact le_rfl; exact le_max_left _ _]

theorem clientState_frontier_le_peakWords {α : Type} (w : ℕ) (s : State) (p : Prog α) :
    ((spec w).clientState s p).frontier ≤ peakWords s p := by
  induction p generalizing s with
  | pure _ => exact le_rfl
  | liftBind o k ih => exact (ih (step s o).2 (step s o).1).trans (le_max_right _ _)

/-- Word-level frame condition across resizes: every address `a < min s.frontier s'.frontier`
outside `W` retains its value (`s'.mem a = s.mem a`). -/
def UnchangedOutside (s s' : State) (W : Set ℕ) : Prop :=
  ∀ a < min s.frontier s'.frontier, a ∉ W → s'.mem a = s.mem a

theorem UnchangedOutside.refl (s : State) (W : Set ℕ) : UnchangedOutside s s W :=
  fun _ _ _ => rfl

theorem UnchangedOutside.mono {s s' : State} {W₁ W₂ : Set ℕ}
    (h : UnchangedOutside s s' W₁) (hsub : W₁ ⊆ W₂) : UnchangedOutside s s' W₂ :=
  fun a ha hnot => h a ha fun hw1 => hnot (hsub hw1)

theorem UnchangedOutside.step_read (s : State) (a : ℕ) :
    UnchangedOutside s (step s (.read a)).1 ∅ := fun _ _ _ => rfl

theorem UnchangedOutside.step_write (s : State) (a v : ℕ) :
    UnchangedOutside s (step s (.write a v)).1 {a} := fun _ _ hx => by
  dsimp only [step]
  exact Function.update_of_ne (Set.mem_singleton_iff.not.mp hx) v s.mem

theorem UnchangedOutside.step_grow (s : State) (k : ℕ) :
    UnchangedOutside s (step s (.grow k)).1 ∅ := fun a ha _ => by
  have hlt : a < s.frontier := lt_of_lt_of_le ha (min_le_left _ _)
  exact clear_of_not_owns (by simp only [Block.Owns]; omega)

theorem UnchangedOutside.step_growDirty (s : State) (k : ℕ) :
    UnchangedOutside s (step s (.growDirty k)).1 ∅ :=
  UnchangedOutside.step_grow s k

theorem UnchangedOutside.step_shrink (s : State) (k : ℕ) :
    UnchangedOutside s (step s (.shrink k)).1 ∅ := fun a ha _ => by
  have hlt : a < s.frontier - k := lt_of_lt_of_le ha (min_le_right _ _)
  exact clear_of_not_owns (by simp only [Block.Owns]; omega)

/-- If a block `b` lies below `min s.frontier s'.frontier` and is disjoint from `W`, then
`UnchangedOutside s s' W` preserves `b.Realizes`. -/
theorem Block.realizes_of_unchangedOutside (b : Block) {s s' : State} {W : Set ℕ}
    {vs : Fin b.length → ℕ} (hreal : b.Realizes s.mem vs)
    (hfit : b.base + b.length ≤ min s.frontier s'.frontier)
    (hframe : UnchangedOutside s s' W) (hdisj : ∀ a, b.Owns a → a ∉ W) :
    b.Realizes s'.mem vs := fun i => by
  dsimp only [Block.read]
  have hown : b.Owns (b.base + i.val) := ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt _⟩
  rw [hframe (b.base + i.val) (by omega) (hdisj _ hown)]
  exact hreal i

end Cslib.DataStructure.Memory.Resizable

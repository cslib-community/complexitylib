/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalTensor
public import Complexity.Computability.Circuit.Frontier.TensorNetwork
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sum

/-!
# Block-counting tensor networks

The block-counting identity, Lemma 2.2 of the note *Deterministic simulations of
nondeterministic and randomized time* (30 October 2026) formalized in issue #1833. Fix a closed
fair-coin table `machine` over `Bool`, an input, a block length `b > 0` and a movement schedule
`σ` of `q > 0` intervals (`Turing.MultiTapePTM.Schedule`). The tensor network
`Turing.MultiTapePTM.blockNetwork` counts the accepting choice strings of `q * b` bits whose run
has schedule `σ` (`Turing.MultiTapePTM.contraction_blockNetwork`), so summing over the schedules
gives the accepting count `A_M(x)` (`Turing.MultiTapePTM.sum_contraction_blockNetwork`). The proof
idea is original to that note, building on the blocking of Hopcroft, Paul and Valiant
[HopcroftPaulValiant1977] (compare [Williams2025], Lemma 2.1 and §3.2).

**The network.** The schedule fixes the block index of every head at the start of every interval
(`Turing.MultiTapePTM.scheduleBlock`), and hence the window of three blocks around each work head.

* There is one vertex for each interval `i`, and one *sink* vertex for each edge.
* Every edge leaves an interval (`Turing.MultiTapePTM.BlockEdge`): the edge `.inl i` carries the
  control record leaving interval `i`, and the edge `.inr (i, h, d)` the contents of block
  `scheduleBlock σ i h + d - 1` of work tape `h` leaving interval `i`. Its target is the next
  interval whose window contains that block, or the next interval for a control record; when
  there is none, it ends at its sink.
* The tensor of interval `i` is the interval tensor of
  `Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalTensor`: the number of
  bit strings `u ∈ {0,1}^b` taking the entering record and window to the leaving ones and moving
  every block as `σ i` prescribes. The entering record comes from the control edge of interval
  `i - 1`, or is the initial record for `i = 0`. The entering contents of a block come from the
  previous interval whose window contains it, or are blank when there is none.
* The sink of the last control edge accepts exactly the records whose output track is `accept`;
  every other sink is the constant `1`.

Edges carry letters of `Turing.MultiTapePTM.BlockLetter`, a control record or the contents of a
block. A letter of the wrong kind on an edge gives weight zero, because the interval leaving
it requires the right kind.

**The identity.** Expanding every interval tensor as a sum over its bit strings writes the
contraction as a sum over `q` strings of `b` bits, that is over choice strings of `q * b` bits.
For a fixed choice string, induction over the intervals shows that an assignment of letters with
nonzero weight is forced to be the true run's: the control records and the window contents of
the true run at the end of each interval, and the run is forced to follow `σ`. Between two
appearances of a block in windows, the block is untouched
(`Turing.MultiTapePTM.workTapes_intervalStart_eq_of_notMem_blockWindow`), and within an interval
the embedded window is matched to the true run (`Turing.MultiTapePTM.intervalStep_view_iff`).
Conversely the true run's letters have weight one exactly when the run has schedule `σ` and
accepts.

**Size.** The network has `q * (3 k + 1)` edges and `q * (3 k + 2)` vertices, no loops, maximum
degree at most `2 * (3 k + 1)`, and entries at most `2 ^ b`. Its letters have `O(b)` bits, so
binarizing (`Cslib.Circuits.Frontier.TensorNetwork.binarize`) and subdividing it gives a
bipartite Boolean network with `O(q b)` edges and degree `O(b)`, as in the note.

## Main definitions

* `Turing.MultiTapePTM.scheduleBlock`: block indices prescribed by a schedule.
* `Turing.MultiTapePTM.firstAfter`, `Turing.MultiTapePTM.lastBefore`: the next and the previous
  appearance of a block in windows.
* `Turing.MultiTapePTM.InWindow`, `Turing.MultiTapePTM.portBlock`, `Turing.MultiTapePTM.portOf`:
  windows and window entries under a schedule.
* `Turing.MultiTapePTM.BlockEdge`, `Turing.MultiTapePTM.BlockLetter`: edges and letters.
* `Turing.MultiTapePTM.inControl`, `Turing.MultiTapePTM.inWindow`,
  `Turing.MultiTapePTM.IntervalHolds`, `Turing.MultiTapePTM.edgeTarget`: the entering record and
  window of an interval, its condition, and the targets of edges.
* `Turing.MultiTapePTM.blockNetwork`: the block-counting network of a schedule.

## Main results

* `Turing.MultiTapePTM.blockIndex_intervalStart_eq_scheduleBlock`: a run following `σ` has the
  block indices of `σ`.
* `Turing.MultiTapePTM.contraction_blockNetwork`: the network of `σ` counts the accepting choice
  strings with schedule `σ`.
* `Turing.MultiTapePTM.sum_contraction_blockNetwork`: summed over the `3 ^ ((k + 1) * q)`
  schedules, the contractions give the accepting count.
* `Turing.MultiTapePTM.card_blockEdge`, `Turing.MultiTapePTM.card_blockVertex`,
  `Turing.MultiTapePTM.loopless_blockNetwork`, `Turing.MultiTapePTM.maxDegreeLE_blockNetwork`,
  `Turing.MultiTapePTM.tensor_blockNetwork_le`: size, degree and entry bounds.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.1 (p. 53)
-/

public section

namespace Turing.MultiTapePTM

open Cslib.Circuits.Frontier MultiTapeNTM.ChoiceTable

variable {k q : ℕ} {State : Type}

/-! ### Block indices prescribed by a schedule -/

/-- The block index of every head at the start of interval `i` under the schedule `σ`, when every
head starts in block `0`: the sum of the entries of `σ` for the intervals before `i`. -/
@[expose] def scheduleBlock (σ : Schedule k q) : ℕ → Option (Fin k) → ℤ
  | 0 => fun _ => 0
  | i + 1 => fun head => scheduleBlock σ i head + if hi : i < q then (σ ⟨i, hi⟩ head : ℤ) else 0

@[simp] theorem scheduleBlock_zero (σ : Schedule k q) : scheduleBlock σ 0 = fun _ => 0 := rfl

theorem scheduleBlock_succ (σ : Schedule k q) {i : ℕ} (hi : i < q) (head : Option (Fin k)) :
    scheduleBlock σ (i + 1) head = scheduleBlock σ i head + (σ ⟨i, hi⟩ head : ℤ) := by
  simp only [scheduleBlock, dite_eq_left hi]

/-- **A run following `σ` has the block indices of `σ`.** If the run replaying `coins` from the
start has schedule entries `σ j` for the intervals `j < i`, it starts interval `i` with the block
indices `scheduleBlock σ i`. -/
theorem blockIndex_intervalStart_eq_scheduleBlock (machine : MultiTapePTM k Bool State)
    {input : List Bool} (b : ℕ) [NeZero b] (coins : List Bool) (σ : Schedule k q) {i : ℕ}
    (hi : i ≤ q)
    (hσ : ∀ j : Fin q, j.val < i →
      machine.schedule b q coins (Cfg.init machine.initial input) j = σ j) :
    (machine.intervalStart b coins (Cfg.init machine.initial input) i).blockIndex b =
      scheduleBlock σ i := by
  induction i with
  | zero =>
    funext head
    rw [intervalStart_zero, Cfg.blockIndex, Cfg.headPos_init, Int.zero_ediv]
    rfl
  | succ i ih =>
    funext head
    have hiq : i < q := by omega
    have hstep := machine.coe_schedule (Nat.pos_of_neZero b) q coins
      (Cfg.init machine.initial input) ⟨i, hiq⟩ head
    rw [hσ ⟨i, hiq⟩ (by simp)] at hstep
    have hprev := congrFun (ih (by omega) fun j hj => hσ j (by omega)) head
    simp only [Cfg.blockIndex] at hprev ⊢
    rw [scheduleBlock_succ σ hiq]
    simp only at hstep
    omega

/-! ### Appearances of a block in windows -/

/-- The first index after `i` satisfying `p`, if any. -/
def firstAfter (p : Fin q → Prop) [DecidablePred p] (i : Fin q) : Option (Fin q) :=
  if h : (Finset.univ.filter fun i' => i < i' ∧ p i').Nonempty then
    some ((Finset.univ.filter fun i' => i < i' ∧ p i').min' h)
  else none

/-- The last index before `i` satisfying `p`, if any. -/
def lastBefore (p : Fin q → Prop) [DecidablePred p] (i : Fin q) : Option (Fin q) :=
  if h : (Finset.univ.filter fun i' => i' < i ∧ p i').Nonempty then
    some ((Finset.univ.filter fun i' => i' < i ∧ p i').max' h)
  else none

theorem firstAfter_eq_some_iff {p : Fin q → Prop} [DecidablePred p] {i i' : Fin q} :
    firstAfter p i = some i' ↔ i < i' ∧ p i' ∧ ∀ j, i < j → j < i' → ¬ p j := by
  unfold firstAfter
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl
      have hmem := Finset.mem_filter.mp (Finset.min'_mem _ h)
      refine ⟨hmem.2.1, hmem.2.2, fun j hj hjlt hpj => ?_⟩
      exact absurd (Finset.min'_le _ j (by simp [hj, hpj])) (not_le.mpr hjlt)
    · rintro ⟨hlt, hp, hmin⟩
      refine le_antisymm (Finset.min'_le _ _ (by simp [hlt, hp])) ?_
      have hmem := Finset.mem_filter.mp (Finset.min'_mem _ h)
      by_contra hcon
      exact hmin _ hmem.2.1 (not_le.mp hcon) hmem.2.2
  · simp only [false_iff]
    rintro ⟨hlt, hp, -⟩
    exact h ⟨i', by simp [hlt, hp]⟩

theorem lastBefore_eq_some_iff {p : Fin q → Prop} [DecidablePred p] {i i' : Fin q} :
    lastBefore p i = some i' ↔ i' < i ∧ p i' ∧ ∀ j, i' < j → j < i → ¬ p j := by
  unfold lastBefore
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl
      have hmem := Finset.mem_filter.mp (Finset.max'_mem _ h)
      refine ⟨hmem.2.1, hmem.2.2, fun j hj hjlt hpj => ?_⟩
      exact absurd (Finset.le_max' _ j (by simp [hjlt, hpj])) (not_le.mpr hj)
    · rintro ⟨hlt, hp, hmax⟩
      refine le_antisymm ?_ (Finset.le_max' _ _ (by simp [hlt, hp]))
      have hmem := Finset.mem_filter.mp (Finset.max'_mem _ h)
      by_contra hcon
      exact hmax _ (not_le.mp hcon) hmem.2.1 hmem.2.2
  · simp only [false_iff]
    rintro ⟨hlt, hp, -⟩
    exact h ⟨i', by simp [hlt, hp]⟩

theorem lastBefore_eq_none_iff {p : Fin q → Prop} [DecidablePred p] {i : Fin q} :
    lastBefore p i = none ↔ ∀ j, j < i → ¬ p j := by
  unfold lastBefore
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    obtain ⟨j, hj⟩ := h
    exact ⟨j, (Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2⟩
  · simp only [true_iff]
    intro j hj hp
    exact h ⟨j, by simp [hj, hp]⟩

theorem firstAfter_eq_none_iff {p : Fin q → Prop} [DecidablePred p] {i : Fin q} :
    firstAfter p i = none ↔ ∀ j, i < j → ¬ p j := by
  unfold firstAfter
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    obtain ⟨j, hj⟩ := h
    exact ⟨j, (Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2⟩
  · simp only [true_iff]
    intro j hj hp
    exact h ⟨j, by simp [hj, hp]⟩

/-- Consecutive appearances: the last appearance before `i` has `i` as its next appearance. -/
theorem firstAfter_of_lastBefore {p : Fin q → Prop} [DecidablePred p] {i i' : Fin q}
    (hi : p i) (h : lastBefore p i = some i') : firstAfter p i' = some i := by
  obtain ⟨hlt, -, hbetween⟩ := lastBefore_eq_some_iff.mp h
  exact firstAfter_eq_some_iff.mpr ⟨hlt, hi, hbetween⟩

theorem lastBefore_of_firstAfter {p : Fin q → Prop} [DecidablePred p] {i i' : Fin q}
    (hi' : p i') (h : firstAfter p i' = some i) : lastBefore p i = some i' := by
  obtain ⟨hlt, -, hbetween⟩ := firstAfter_eq_some_iff.mp h
  exact lastBefore_eq_some_iff.mpr ⟨hlt, hi', hbetween⟩

/-- Block `j` of work tape `h` lies in the window of interval `i` under `σ`. -/
abbrev InWindow (σ : Schedule k q) (h : Fin k) (j : ℤ) (i : Fin q) : Prop :=
  |scheduleBlock σ i (some h) - j| ≤ 1

/-- The block of the window entry `d` of work tape `h` in interval `i`. -/
@[expose] def portBlock (σ : Schedule k q) (i : Fin q) (h : Fin k) (d : Fin 3) : ℤ :=
  scheduleBlock σ i (some h) + d - 1

/-- The window entry of block `j` of work tape `h` in interval `i`. -/
@[expose] def portOf (σ : Schedule k q) (i : Fin q) (h : Fin k) (j : ℤ) : Fin 3 :=
  ⟨(j - scheduleBlock σ i (some h) + 1).toNat % 3, Nat.mod_lt _ (by norm_num)⟩

theorem portBlock_portOf {σ : Schedule k q} {i : Fin q} {h : Fin k} {j : ℤ}
    (hj : InWindow σ h j i) : portBlock σ i h (portOf σ i h j) = j := by
  simp only [InWindow, abs_le] at hj
  simp only [portBlock, portOf]
  omega

theorem inWindow_portBlock (σ : Schedule k q) (i : Fin q) (h : Fin k) (d : Fin 3) :
    InWindow σ h (portBlock σ i h d) i := by
  have := d.isLt
  simp only [InWindow, portBlock, abs_le]
  omega

/-! ### The network -/

/-- The edges of a block-counting network of `q` intervals: `.inl i` carries the control record
leaving interval `i`, and `.inr (i, h, d)` the contents of window entry `d` of work tape `h`
leaving interval `i`. -/
abbrev BlockEdge (k q : ℕ) := Fin q ⊕ (Fin q × Fin k × Fin 3)

/-- The letters on the edges: a control record or the contents of a block. -/
abbrev BlockLetter (k : ℕ) (State : Type) (b : ℕ) :=
  BlockControl k State b ⊕ (ZMod b → Option Bool)

variable {b : ℕ}

/-- The control record of a letter, or a default for block contents. -/
@[expose] def BlockLetter.control : BlockLetter k State b → BlockControl k State b
  | .inl c => c
  | .inr _ => (none, 0, .empty)

/-- The block contents of a letter, or blank for a control record. -/
@[expose] def BlockLetter.contents : BlockLetter k State b → ZMod b → Option Bool
  | .inl _ => fun _ => none
  | .inr w => w

/-- The weight of the last control record: one when its output track is `accept`. -/
@[expose] def acceptWeight : BlockLetter k State b → ℕ
  | .inl c => if c.2.2 = .accept then 1 else 0
  | .inr _ => 0

variable (machine : MultiTapePTM k Bool State) (input : List Bool) (b : ℕ) [NeZero b]
  (σ : Schedule k q)

/-- The control record entering interval `i`: the initial record for `i = 0`, and otherwise the
letter on the control edge leaving interval `i - 1`. -/
@[expose] def inControl (i : Fin q) (x : BlockEdge k q → BlockLetter k State b) :
    BlockControl k State b :=
  if hi : i.val = 0 then (some machine.initial, 0, .empty)
  else (x (.inl ⟨i - 1, by omega⟩)).control

variable {b} in
/-- The window contents entering interval `i`: each block is read from the edge leaving the
previous interval whose window contains it, and is blank if there is none. -/
@[expose] def inWindow (i : Fin q) (x : BlockEdge k q → BlockLetter k State b) :
    Fin k → Fin 3 → ZMod b → Option Bool := fun h d =>
  (lastBefore (InWindow σ h (portBlock σ i h d)) i).elim (fun _ => none) fun i' =>
    (x (.inr (i', h, portOf σ i' h (portBlock σ i h d)))).contents

/-- The edge condition at interval `i` for the bits `u`: an interval step from the entering
record and window to the letters on the edges leaving `i`, which must be of the right kinds,
moving the blocks as `σ i` prescribes. -/
@[expose] def IntervalHolds (i : Fin q) (x : BlockEdge k q → BlockLetter k State b)
    (u : Fin b → Bool) : Prop :=
  ∃ cOut wOut, machine.IntervalStep b input (scheduleBlock σ i) (σ i)
      (machine.inControl b i x) (inWindow σ i x) (List.ofFn u) cOut wOut ∧
    x (.inl i) = .inl cOut ∧ ∀ h d, x (.inr (i, h, d)) = .inr (wOut h d)

/-- The target of an edge: the interval reading it next, or its sink. -/
@[expose] def edgeTarget : BlockEdge k q → Fin q ⊕ BlockEdge k q
  | .inl i => if hi : i.val + 1 < q then .inl ⟨i + 1, hi⟩ else .inr (.inl i)
  | .inr (i, h, d) =>
    (firstAfter (InWindow σ h (portBlock σ i h d)) i).elim (.inr (.inr (i, h, d))) .inl

/-- The interval `i ≠ 0` reads the control edge of interval `i - 1`. -/
private theorem edgeTarget_inl_pred {i : Fin q} (hi : i.val ≠ 0) :
    edgeTarget σ (.inl ⟨i - 1, by omega⟩) = .inl i := by
  simp only [edgeTarget]
  rw [dite_eq_left (by omega)]
  congr 1
  ext
  simp only
  omega

/-- Interval `i` reads the block edges of the previous appearances of its window blocks. -/
private theorem edgeTarget_inWindow {i i' : Fin q} {h : Fin k} {d : Fin 3}
    (hi' : lastBefore (InWindow σ h (portBlock σ i h d)) i = some i') :
    edgeTarget σ (.inr (i', h, portOf σ i' h (portBlock σ i h d))) = .inl i := by
  have hin : InWindow σ h (portBlock σ i h d) i' := (lastBefore_eq_some_iff.mp hi').2.1
  simp only [edgeTarget, portBlock_portOf hin,
    firstAfter_of_lastBefore (inWindow_portBlock σ i h d) hi', Option.elim_some]

omit [NeZero b] in
/-- Interval `i` only reads the edges at it. -/
private theorem intervalHolds_congr {i : Fin q} {x y : BlockEdge k q → BlockLetter k State b}
    (hxy : ∀ e, Sum.inl i = edgeTarget σ e ∨ e.elim id Prod.fst = i → x e = y e)
    (u : Fin b → Bool) :
    machine.IntervalHolds input b σ i x u ↔ machine.IntervalHolds input b σ i y u := by
  have hcontrol : machine.inControl b i x = machine.inControl b i y := by
    unfold inControl
    split_ifs with hi
    · rfl
    · rw [hxy _ (Or.inl (edgeTarget_inl_pred σ hi).symm)]
  have hwindow : inWindow σ i x = inWindow σ i y := by
    funext h d
    unfold inWindow
    cases hlast : lastBefore (InWindow σ h (portBlock σ i h d)) i with
    | none => rfl
    | some i' =>
      simp only [Option.elim_some]
      rw [hxy _ (Or.inl (edgeTarget_inWindow σ hlast).symm)]
  have hctrl : x (.inl i) = y (.inl i) := hxy _ (Or.inr rfl)
  have hblock : ∀ h d, x (.inr (i, h, d)) = y (.inr (i, h, d)) := fun h d => hxy _ (Or.inr rfl)
  simp only [IntervalHolds, hcontrol, hwindow, hctrl, hblock]

open scoped Classical in
/-- **The block-counting network** of the schedule `σ`. It has a vertex for every interval
(`.inl i`) and a sink for every edge (`.inr e`). Every edge `e` leaves its interval and ends at
`edgeTarget σ e`. The tensor of interval `i` counts the bit strings `u ∈ {0,1}^b` for which
`IntervalHolds` holds; the sink of the last control edge requires the output track `accept`, and
every other sink is `1`. -/
noncomputable def blockNetwork :
    TensorNetwork ℕ (BlockLetter k State b) (Fin q ⊕ BlockEdge k q) (BlockEdge k q) where
  src e := .inl (e.elim id Prod.fst)
  tgt := edgeTarget σ
  tensor
    | .inl i, x => (Finset.univ.filter fun u => machine.IntervalHolds input b σ i x u).card
    | .inr (.inl i), x => if i.val + 1 = q then acceptWeight (x (.inl i)) else 1
    | .inr (.inr _), _ => 1
  tensor_congr := by
    rintro (i | (i | e)) x y h
    · simp only
      congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine machine.intervalHolds_congr input b σ (fun e he => h e ?_) u
      rcases he with he | he
      · exact Or.inr he.symm
      · exact Or.inl (congrArg Sum.inl he)
    · simp only
      split_ifs with hi
      · rw [h (.inl i) (Or.inr ?_)]
        simp only [edgeTarget]
        rw [dite_eq_right (by omega)]
      · rfl
    · rfl

/-! ### The counting identity -/

section Identity

variable {machine input b σ}

/-- The configuration of the run replaying `y` from the start at the start of interval `i`. -/
private noncomputable abbrev trueRun (machine : MultiTapePTM k Bool State) (input : List Bool)
    (b : ℕ) (y : Fin (q * b) → Bool) (i : ℕ) : Cfg k Bool State input :=
  machine.intervalStart b (List.ofFn y) (Cfg.init machine.initial input) i

/-- The interval bits of a choice string: `y` split into `q` strings of `b` bits. -/
private def intervalBits : (Fin (q * b) → Bool) ≃ (Fin q → Fin b → Bool) :=
  (finProdFinEquiv.arrowCongr (Equiv.refl Bool)).symm.trans (Equiv.curry _ _ _)

omit [NeZero b] in
private theorem intervalBits_apply (y : Fin (q * b) → Bool) (i : Fin q) :
    intervalBits y i = fun r => y (finProdFinEquiv (i, r)) := rfl

/-- The letters of the true run: the control records and window contents at the end of every
interval. -/
private noncomputable def trueLetters (machine : MultiTapePTM k Bool State) (input : List Bool)
    (σ : Schedule k q) (y : Fin (q * b) → Bool) : BlockEdge k q → BlockLetter k State b
  | .inl i => .inl ((trueRun machine input b y (i + 1)).blockControl b)
  | .inr (i, h, d) =>
    .inr ((trueRun machine input b y (i + 1)).windowContents b
      (scheduleBlock σ i) h d)

/-- `x` agrees with the true run on the edges leaving the intervals before `i`, and the run
follows `σ` there. -/
private def AgreesBefore (machine : MultiTapePTM k Bool State) (input : List Bool)
    (σ : Schedule k q) (y : Fin (q * b) → Bool) (x : BlockEdge k q → BlockLetter k State b)
    (i : ℕ) : Prop :=
  ∀ j : Fin q, j.val < i →
    machine.schedule b q (List.ofFn y) (Cfg.init machine.initial input) j = σ j ∧
      x (.inl j) = trueLetters machine input σ y (.inl j) ∧
      ∀ h d, x (.inr (j, h, d)) = trueLetters machine input σ y (.inr (j, h, d))

omit [NeZero b] in
/-- The control record of the start configuration. -/
private theorem blockControl_init (q₀ : State) :
    (Cfg.init q₀ input : Cfg k Bool State input).blockControl b = (some q₀, 0, .empty) := by
  have h : ∀ head, ((Cfg.init q₀ input : Cfg k Bool State input).headPos head : ZMod b) = 0 :=
    fun head => by rw [Cfg.headPos_init, Int.cast_zero]
  rw [Cfg.blockControl, funext h]
  rfl

/-- A work-tape cell of a block outside the window of a configuration is outside its three
blocks. -/
private theorem notMem_blockWindow {c : Cfg k Bool State input} {h : Fin k} {j : ℤ}
    (hj : ¬ |c.blockIndex b (some h) - j| ≤ 1) (r : ZMod b) :
    b * j + (r.val : ℤ) ∉ c.blockWindow b h := by
  have hb : (0 : ℤ) < b := by exact_mod_cast Nat.pos_of_neZero b
  have hr : (r.val : ℤ) < b := by exact_mod_cast ZMod.val_lt r
  have hr0 : (0 : ℤ) ≤ r.val := by positivity
  simp only [Cfg.blockIndex, Cfg.headPos_some, abs_le, not_and_or, not_le] at hj
  simp only [Cfg.blockWindow, Set.mem_Ico, not_and_or, not_le, not_lt]
  rcases hj with hj | hj
  · right
    nlinarith
  · left
    nlinarith

/-- **The entering view is the true one.** If `x` agrees with the true run before interval `i`,
then interval `i` reads the true control record and window contents, at the true block
indices. -/
private theorem inView_eq (y : Fin (q * b) → Bool) {x : BlockEdge k q → BlockLetter k State b}
    {i : Fin q} (hx : AgreesBefore machine input σ y x i) :
    scheduleBlock σ i = (trueRun machine input b y i).blockIndex b ∧
      machine.inControl b i x = (trueRun machine input b y i).blockControl b ∧
      inWindow σ i x = (trueRun machine input b y i).windowContents b
        (scheduleBlock σ i) := by
  have hindex : ∀ i' : ℕ, i' ≤ i →
      (trueRun machine input b y i').blockIndex b = scheduleBlock σ i' :=
    fun i' hi' => machine.blockIndex_intervalStart_eq_scheduleBlock b _ σ (by omega)
      fun j hj => (hx j (by omega)).1
  refine ⟨(hindex i le_rfl).symm, ?_, ?_⟩
  · -- The control record.
    unfold inControl
    split_ifs with hi
    · have : (i : ℕ) = 0 := hi
      rw [trueRun, this, intervalStart_zero, blockControl_init]
    · rw [(hx ⟨i - 1, by omega⟩ (by simp; omega)).2.1]
      simp only [trueLetters, BlockLetter.control]
      congr 3
      omega
  · -- The window contents: the last appearance before `i`, untouched since.
    funext h d r
    set j := portBlock σ i h d
    have huntouched : ∀ i₁ : ℕ, i₁ ≤ i → (∀ i'' : Fin q, i₁ ≤ i'' → i'' < i →
        ¬ InWindow σ h j i'') →
        (trueRun machine input b y i).workTapes h (b * j + r.val) =
          (trueRun machine input b y i₁).workTapes h (b * j + r.val) := by
      intro i₁ hi₁ hnot
      refine machine.workTapes_intervalStart_eq_of_notMem_blockWindow (Nat.pos_of_neZero b)
        _ _ hi₁ fun i'' hi'' hi''i => notMem_blockWindow ?_ r
      rw [hindex i'' hi''i.le]
      exact hnot ⟨i'', by omega⟩ hi'' hi''i
    change (inWindow σ i x h d) r = (trueRun machine input b y i).workTapes h (b * j + r.val)
    unfold inWindow
    cases hlast : lastBefore (InWindow σ h j) i with
    | none =>
      simp only [Option.elim_none]
      rw [huntouched 0 (Nat.zero_le _) fun i'' _ hi'' =>
        lastBefore_eq_none_iff.mp hlast i'' hi'', trueRun, intervalStart_zero]
      rfl
    | some i' =>
      obtain ⟨hlt, hin, hbetween⟩ := lastBefore_eq_some_iff.mp hlast
      simp only [Option.elim_some]
      rw [(hx i' hlt).2.2, huntouched (i' + 1) hlt fun i'' h₁ h₂ => hbetween i'' h₁ h₂]
      change (trueRun machine input b y (i' + 1)).workTapes h
          (b * portBlock σ i' h (portOf σ i' h j) + r.val) = _
      rw [portBlock_portOf hin]

/-- `SignType` casts to `ℤ` injectively. -/
private theorem signType_cast_inj {s t : SignType} (h : (s : ℤ) = t) : s = t := by
  cases s <;> cases t <;> first | rfl | (simp at h)

/-- **The condition at an interval, on the true view.** If interval `i` reads the true view, its
condition holds exactly when the letters it leaves are the true ones and the run follows
`σ i`. -/
private theorem intervalHolds_iff (y : Fin (q * b) → Bool)
    {x : BlockEdge k q → BlockLetter k State b} {i : Fin q}
    (hindex : scheduleBlock σ i = (trueRun machine input b y i).blockIndex b)
    (hcontrol : machine.inControl b i x =
      (trueRun machine input b y i).blockControl b)
    (hwindow : inWindow σ i x = (trueRun machine input b y i).windowContents b
      (scheduleBlock σ i)) :
    machine.IntervalHolds input b σ i x (fun r => y (finProdFinEquiv (i, r))) ↔
      machine.schedule b q (List.ofFn y) (Cfg.init machine.initial input) i = σ i ∧
        x (.inl i) = trueLetters machine input σ y (.inl i) ∧
        ∀ h d, x (.inr (i, h, d)) = trueLetters machine input σ y (.inr (i, h, d)) := by
  have hnext := machine.intervalStart_succ_ofFn y (Cfg.init machine.initial input) i
  rw [IntervalHolds, hcontrol, hwindow, hindex]
  simp only [machine.intervalStep_view_iff b _ (List.length_ofFn (f := _)).le]
  rw [← hnext]
  have hsched : machine.schedule b q (List.ofFn y) (Cfg.init machine.initial input) i = σ i ↔
      ∀ head, (trueRun machine input b y (i + 1)).blockIndex b head =
        (trueRun machine input b y i).blockIndex b head + σ i head := by
    rw [funext_iff]
    refine forall_congr' fun head => ?_
    have := machine.coe_schedule (Nat.pos_of_neZero b) q (List.ofFn y)
      (Cfg.init machine.initial input) i head
    simp only [Cfg.blockIndex, trueRun]
    constructor
    · intro h
      rw [← h]
      omega
    · intro h
      exact signType_cast_inj (by omega)
  simp only [trueLetters, ← hindex, hsched]
  constructor
  · rintro ⟨cOut, wOut, ⟨rfl, rfl, hmove⟩, hc, hw⟩
    exact ⟨hmove, hc, hw⟩
  · rintro ⟨hmove, hc, hw⟩
    exact ⟨_, _, ⟨rfl, rfl, hmove⟩, hc, hw⟩

/-- Satisfying the conditions of all intervals forces agreement with the true run. -/
private theorem agreesBefore_of_forall (y : Fin (q * b) → Bool)
    {x : BlockEdge k q → BlockLetter k State b}
    (hx : ∀ i : Fin q, machine.IntervalHolds input b σ i x (intervalBits y i)) :
    ∀ i ≤ q, AgreesBefore machine input σ y x i := by
  intro i hi
  induction i with
  | zero => exact fun j hj => absurd hj (Nat.not_lt_zero _)
  | succ i ih =>
    have hprev := ih (by omega)
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact hprev j hj
    · obtain ⟨hindex, hcontrol, hwindow⟩ := inView_eq y (i := j) (fun j' hj' => hprev j' (by omega))
      exact (intervalHolds_iff y hindex hcontrol hwindow).mp (hx j)

/-- The true letters satisfy all interval conditions exactly when the run follows `σ`. -/
private theorem forall_intervalHolds_trueLetters_iff (y : Fin (q * b) → Bool) :
    (∀ i : Fin q, machine.IntervalHolds input b σ i (trueLetters machine input σ y)
      (intervalBits y i)) ↔
      machine.schedule b q (List.ofFn y) (Cfg.init machine.initial input) = σ := by
  constructor
  · intro h
    funext j
    exact (agreesBefore_of_forall y h q le_rfl j j.isLt).1
  · intro hσ i
    have hagree : AgreesBefore machine input σ y (trueLetters machine input σ y) i :=
      fun j _ => ⟨congrFun hσ j, rfl, fun _ _ => rfl⟩
    obtain ⟨hindex, hcontrol, hwindow⟩ := inView_eq y hagree
    exact (intervalHolds_iff y hindex hcontrol hwindow).mpr ⟨congrFun hσ i, rfl, fun _ _ => rfl⟩

omit [NeZero b] in
/-- The run replaying `q * b` bits ends at the start of interval `q`. -/
private theorem runClosedCoins_eq (y : Fin (q * b) → Bool) :
    machine.runClosedCoins (List.ofFn y) input =
      (trueRun machine input b y q).output := by
  rw [runClosedCoins_eq_output_stepCoins, trueRun, intervalStart,
    List.take_of_length_le (by simp)]

omit [NeZero b] in
/-- Agreeing with the true run before every interval is being the true letters. -/
private theorem eq_trueLetters_of_agreesBefore (y : Fin (q * b) → Bool)
    {x : BlockEdge k q → BlockLetter k State b} (hx : AgreesBefore machine input σ y x q) :
    x = trueLetters machine input σ y := by
  funext e
  rcases e with j | ⟨j, h, d⟩
  · exact (hx j j.isLt).2.1
  · exact (hx j j.isLt).2.2 h d


end Identity

omit [NeZero b] in
/-- The sinks contribute the acceptance check of the last control edge. -/
private theorem prod_sinks (hq : 0 < q) (x : BlockEdge k q → BlockLetter k State b) :
    ∏ e : BlockEdge k q, (machine.blockNetwork input b σ).tensor (.inr e) x =
      acceptWeight (x (.inl ⟨q - 1, by omega⟩)) := by
  rw [Fintype.prod_sum_type]
  have hblock : ∏ e : Fin q × Fin k × Fin 3,
      (machine.blockNetwork input b σ).tensor (.inr (.inr e)) x = 1 :=
    Finset.prod_eq_one fun _ _ => rfl
  rw [hblock, mul_one]
  rw [Finset.prod_eq_single (⟨q - 1, by omega⟩ : Fin q)]
  · change (if q - 1 + 1 = q then _ else 1) = _
    rw [ite_eq_left (by omega)]
  · intro i _ hi
    change (if i.val + 1 = q then _ else 1) = 1
    rw [ite_eq_right fun h => hi (Fin.ext (by simp only; omega))]
  · exact fun h => absurd (Finset.mem_univ _) h

omit [NeZero b] in
open scoped Classical in
/-- The interval tensors expanded as a sum over the bits of all intervals. -/
private theorem prod_intervals (x : BlockEdge k q → BlockLetter k State b) :
    ∏ i : Fin q, (machine.blockNetwork input b σ).tensor (.inl i) x =
      ∑ u : Fin q → Fin b → Bool,
        if ∀ i, machine.IntervalHolds input b σ i x (u i) then 1 else 0 := by
  have hcard : ∀ i : Fin q, (machine.blockNetwork input b σ).tensor (.inl i) x =
      ∑ u : Fin b → Bool, if machine.IntervalHolds input b σ i x u then 1 else 0 := by
    intro i
    change (Finset.univ.filter fun u => machine.IntervalHolds input b σ i x u).card = _
    rw [Finset.card_filter]
  simp only [hcard]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Fintype.prod_boole]
  exact Finset.sum_congr rfl fun u _ => by congr

/-- **The block-counting identity for one schedule.** The contraction of the network of `σ` is the
number of choice strings of `q * b` bits on which the machine accepts and whose run has movement
schedule `σ`. -/
theorem contraction_blockNetwork [Fintype State] (hq : 0 < q) :
    (machine.blockNetwork input b σ).contraction =
      (Finset.univ.filter fun y : Fin (q * b) → Bool =>
        machine.runClosedCoins (List.ofFn y) input = [true] ∧
          machine.schedule b q (List.ofFn y) (Cfg.init machine.initial input) = σ).card := by
  classical
  rw [TensorNetwork.contraction]
  simp only [Fintype.prod_sum_type, machine.prod_sinks input b σ hq, prod_intervals,
    Finset.sum_mul]
  rw [Finset.sum_comm, ← (intervalBits (q := q) (b := b)).sum_comp, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (trueLetters machine input σ y)]
  · -- The true letters weigh one exactly when the run follows `σ` and accepts.
    have hlast : trueLetters machine input σ y (.inl ⟨q - 1, by omega⟩) =
        .inl ((trueRun machine input b y q).blockControl b) := by
      simp only [trueLetters, Nat.sub_add_cancel hq]
    by_cases hall : ∀ i : Fin q,
        machine.IntervalHolds input b σ i (trueLetters machine input σ y) (intervalBits y i)
    · have hσ' := (forall_intervalHolds_trueLetters_iff y).mp hall
      rw [ite_eq_left hall, one_mul, hlast, acceptWeight]
      refine if_congr ?_ rfl rfl
      rw [Cfg.blockControl, OutputTrack.ofWord_eq_accept_iff, runClosedCoins_eq, hσ']
      exact (and_iff_left rfl).symm
    · have hσ' := fun h => hall ((forall_intervalHolds_trueLetters_iff y).mpr h)
      rw [ite_eq_right hall, zero_mul]
      exact (ite_eq_right fun h => hσ' h.2).symm
  · -- Any other assignment violates some interval condition.
    intro x _ hx
    rw [ite_eq_right fun hall =>
      hx (eq_trueLetters_of_agreesBefore y (agreesBefore_of_forall y hall q le_rfl)), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **The block-counting identity** (the note's Lemma 2.2, equation (2)). Summed over the
movement schedules of `q > 0` intervals of `b` bits, the contractions of the block-counting
networks are the accepting count on `q * b` bits. -/
theorem sum_contraction_blockNetwork [Fintype State] (hq : 0 < q) :
    ∑ σ : Schedule k q, (machine.blockNetwork input b σ).contraction =
      machine.acceptCount input (q * b) := by
  rw [machine.acceptCount_eq_sum_card_schedule input b q]
  exact Finset.sum_congr rfl fun σ _ => machine.contraction_blockNetwork input b σ hq

/-! ### Size, degree and entries -/

/-- A block-counting network has `q * (3 * k + 1)` edges: one control edge and three block edges
per work tape for each interval. -/
theorem card_blockEdge : Fintype.card (BlockEdge k q) = q * (3 * k + 1) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- A block-counting network has `q * (3 * k + 2)` vertices: the intervals and the sinks. -/
theorem card_blockVertex : Fintype.card (Fin q ⊕ BlockEdge k q) = q * (3 * k + 2) := by
  rw [Fintype.card_sum, card_blockEdge, Fintype.card_fin]
  ring

omit [NeZero b] in
/-- Every entry of a block-counting network is at most `2 ^ b`: an interval tensor counts bit
strings of length `b`, and a sink is `0` or `1`. -/
theorem tensor_blockNetwork_le (v : Fin q ⊕ BlockEdge k q)
    (x : BlockEdge k q → BlockLetter k State b) :
    (machine.blockNetwork input b σ).tensor v x ≤ 2 ^ b := by
  classical
  have hone : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
  rcases v with i | i | e
  · change (Finset.univ.filter fun u => machine.IntervalHolds input b σ i x u).card ≤ 2 ^ b
    exact (Finset.card_filter_le _ _).trans (by simp)
  · change (if i.val + 1 = q then acceptWeight (x (.inl i)) else 1) ≤ 2 ^ b
    split_ifs
    · rcases x (.inl i) with c | w
      · simp only [acceptWeight]
        split_ifs <;> omega
      · exact Nat.zero_le _
    · exact hone
  · exact hone

omit [NeZero b] in
/-- The source of an edge is its interval. -/
theorem blockNetwork_src (e : BlockEdge k q) :
    (machine.blockNetwork input b σ).src e = .inl (e.elim id Prod.fst) := by
  unfold blockNetwork; rfl

omit [NeZero b] in
/-- The target of an edge is the interval reading it next, or its sink. -/
theorem blockNetwork_tgt (e : BlockEdge k q) :
    (machine.blockNetwork input b σ).tgt e = edgeTarget σ e := by
  unfold blockNetwork; rfl

open scoped Classical in
omit [NeZero b] in
/-- The tensor of an interval counts the bit strings satisfying its condition. -/
theorem blockNetwork_tensor_interval (i : Fin q) (x : BlockEdge k q → BlockLetter k State b) :
    (machine.blockNetwork input b σ).tensor (.inl i) x =
      (Finset.univ.filter fun u => machine.IntervalHolds input b σ i x u).card := by
  unfold blockNetwork; rfl

omit [NeZero b] in
/-- The sink of a control edge accepts the last control record, and is `1` otherwise. -/
theorem blockNetwork_tensor_controlSink (i : Fin q) (x : BlockEdge k q → BlockLetter k State b) :
    (machine.blockNetwork input b σ).tensor (.inr (.inl i)) x =
      if i.val + 1 = q then acceptWeight (x (.inl i)) else 1 := by
  unfold blockNetwork; rfl

omit [NeZero b] in
/-- The sink of a block edge is the constant `1`. -/
theorem blockNetwork_tensor_blockSink (e : Fin q × Fin k × Fin 3)
    (x : BlockEdge k q → BlockLetter k State b) :
    (machine.blockNetwork input b σ).tensor (.inr (.inr e)) x = 1 := by
  unfold blockNetwork; rfl

omit [NeZero b] in
/-- Every edge goes forward in time, from its interval to a later interval or to a sink. -/
private theorem edgeTarget_eq_inl {e : BlockEdge k q} {i : Fin q}
    (h : edgeTarget σ e = .inl i) : e.elim id Prod.fst < i := by
  rcases e with i' | ⟨i', hd, d⟩
  · simp only [edgeTarget] at h
    split_ifs at h with hi
    · cases h
      simp only [Sum.elim_inl, id_eq, Fin.lt_def]
      omega
  · simp only [edgeTarget] at h
    cases hf : firstAfter (InWindow σ hd (portBlock σ i' hd d)) i' with
    | none => simp [hf] at h
    | some i'' =>
      simp only [hf, Option.elim_some, Sum.inl.injEq] at h
      subst h
      exact (firstAfter_eq_some_iff.mp hf).1

omit [NeZero b] in
/-- A block-counting network has no loops. -/
theorem loopless_blockNetwork : (machine.blockNetwork input b σ).Loopless := by
  intro e he
  rw [blockNetwork_src, blockNetwork_tgt] at he
  exact (edgeTarget_eq_inl σ he.symm).ne rfl

omit [NeZero b] in
/-- The edges into interval `i` are its entering control edge and one block edge for each window
entry it reads. -/
private theorem injOn_inEdges (i : Fin q) :
    Set.InjOn (fun e : BlockEdge k q => e.elim (fun _ => (none : Option (Fin k × Fin 3)))
      fun p => some (p.2.1, portOf σ i p.2.1 (portBlock σ p.1 p.2.1 p.2.2)))
      {e | edgeTarget σ e = .inl i} := by
  rintro (i₁ | ⟨i₁, h₁, d₁⟩) he₁ (i₂ | ⟨i₂, h₂, d₂⟩) he₂ heq
  · -- Two control edges into `i` both leave `i - 1`.
    simp only [Set.mem_ofPred_eq, edgeTarget] at he₁ he₂
    split_ifs at he₁ he₂
    cases he₁
    simp only [Sum.inl.injEq, Fin.mk.injEq] at he₂
    congr 1
    exact Fin.ext (by omega)
  · simp at heq
  · simp at heq
  · simp only [Option.some.injEq, Prod.mk.injEq, Sum.elim_inr] at heq
    obtain ⟨rfl, hport⟩ := heq
    simp only [Set.mem_ofPred_eq, edgeTarget] at he₁ he₂
    -- Both are previous appearances of the same block, read at the same window entry of `i`.
    have hf : ∀ {i' : Fin q} {d' : Fin 3},
        (firstAfter (InWindow σ h₁ (portBlock σ i' h₁ d')) i').elim
          (Sum.inr (Sum.inr (i', h₁, d'))) Sum.inl = (Sum.inl i : Fin q ⊕ BlockEdge k q) →
        firstAfter (InWindow σ h₁ (portBlock σ i' h₁ d')) i' = some i := by
      intro i' d' h
      cases hc : firstAfter (InWindow σ h₁ (portBlock σ i' h₁ d')) i' with
      | none => simp [hc] at h
      | some i'' => simp only [hc, Option.elim_some, Sum.inl.injEq] at h; rw [h]
    have hf₁ := hf he₁
    have hf₂ := hf he₂
    have hw₁ := (firstAfter_eq_some_iff.mp hf₁).2.1
    have hw₂ := (firstAfter_eq_some_iff.mp hf₂).2.1
    have hj : portBlock σ i₁ h₁ d₁ = portBlock σ i₂ h₁ d₂ := by
      rw [← portBlock_portOf hw₁, ← portBlock_portOf hw₂, hport]
    have hl₁ := lastBefore_of_firstAfter (inWindow_portBlock σ i₁ h₁ d₁) hf₁
    have hl₂ := lastBefore_of_firstAfter (inWindow_portBlock σ i₂ h₁ d₂) hf₂
    rw [hj] at hl₁
    have hi : i₁ = i₂ := Option.some.inj (hl₁.symm.trans hl₂)
    subst hi
    have hd : d₁ = d₂ := by
      simp only [portBlock] at hj
      exact Fin.ext (by omega)
    rw [hd]

omit [NeZero b] in
/-- **The degree bound.** An interval has its `3 k + 1` leaving edges and at most `3 k + 1`
entering edges, and a sink has at most one edge. -/
theorem maxDegreeLE_blockNetwork :
    (machine.blockNetwork input b σ).MaxDegreeLE (2 * (3 * k + 1)) := by
  classical
  rintro (i | e)
  · have hsplit : (machine.blockNetwork input b σ).incidenceSet (.inl i) ⊆
        {e | e.elim id Prod.fst = i} ∪ {e | edgeTarget σ e = .inl i} := by
      rintro e (he | he)
      · left
        rw [blockNetwork_src] at he
        exact Sum.inl_injective he
      · right
        exact he
    have hout : {e : BlockEdge k q | e.elim id Prod.fst = i}.ncard ≤ 3 * k + 1 := by
      calc {e : BlockEdge k q | e.elim id Prod.fst = i}.ncard
          ≤ (Set.range (Sum.elim (fun _ : Unit => (Sum.inl i : BlockEdge k q))
              fun p : Fin k × Fin 3 => Sum.inr (i, p))).ncard := by
            refine Set.ncard_le_ncard ?_ (Set.toFinite _)
            rintro (i' | ⟨i', h, d⟩) he
            · simp only [Set.mem_ofPred_eq, Sum.elim_inl, id_eq] at he
              exact ⟨.inl (), by simp [he]⟩
            · simp only [Set.mem_ofPred_eq, Sum.elim_inr] at he
              exact ⟨.inr (h, d), by simp [he]⟩
        _ = Nat.card (Unit ⊕ Fin k × Fin 3) := Set.ncard_range_of_injective (by
            rintro (_ | p) (_ | p') h <;> simp_all)
        _ = 3 * k + 1 := by
            simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_unit,
              Fintype.card_prod, Fintype.card_fin]
            ring
    have hin : {e : BlockEdge k q | edgeTarget σ e = .inl i}.ncard ≤ 3 * k + 1 := by
      calc {e : BlockEdge k q | edgeTarget σ e = .inl i}.ncard
          ≤ (Set.univ : Set (Option (Fin k × Fin 3))).ncard :=
            Set.ncard_le_ncard_of_injOn _ (fun _ _ => Set.mem_univ _) (injOn_inEdges σ i)
              (Set.toFinite _)
        _ = 3 * k + 1 := by
            rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_option,
              Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
            ring
    calc _ ≤ ({e : BlockEdge k q | e.elim id Prod.fst = i} ∪
          {e | edgeTarget σ e = .inl i}).ncard := Set.ncard_le_ncard hsplit (Set.toFinite _)
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ 2 * (3 * k + 1) := by omega
  · have hsub : (machine.blockNetwork input b σ).incidenceSet (.inr e) ⊆ {e} := by
      rintro e' (he' | he')
      · rw [blockNetwork_src] at he'
        cases he'
      · rw [blockNetwork_tgt] at he'
        rcases e' with i' | ⟨i', h, d⟩
        · simp only [edgeTarget] at he'
          split_ifs at he'
          cases he'
          rfl
        · simp only [edgeTarget] at he'
          cases hc : firstAfter (InWindow σ h (portBlock σ i' h d)) i' with
          | none =>
            simp only [hc, Option.elim_none, Sum.inr.injEq] at he'
            rw [he']
            rfl
          | some i'' => simp [hc] at he'
    calc _ ≤ ({e} : Set (BlockEdge k q)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 1 := Set.ncard_singleton e
      _ ≤ 2 * (3 * k + 1) := by omega

end Turing.MultiTapePTM

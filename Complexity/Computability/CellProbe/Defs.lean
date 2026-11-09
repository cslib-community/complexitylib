/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Languages.Probabilistic.QueryCount
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Log

/-!
# Adaptive Cell-Probe Decision Trees and Deterministic Cell-Probe Schemes

The cell-probe model originates in Minsky and Papert [MinskyPapert1969] and was developed for
dynamic data structures by Fredman and for static data structures by Yao [Yao1981] (see
[Miltersen1999], §1.2, pp. 1–2; §1.5, p. 4; §2.1, pp. 4–5). In a time-invariant deterministic
`Scheme`, persistent state between operations consists solely of `S` cells of `w`-bit words
(`Mem S w := Fin S → Fin (2 ^ w)`, total space `S * w` bits, with no persistent registers across
operations). `IndexedScheme` is a **time-aware relaxation** whose `step` additionally receives the
global operation index `t : ℕ` (a free clock outside cell memory); because per-operation coin
fixing (`Randomized.Scheme.exists_det_indexedScheme_le_expectedSeqProbes`) returns an
`IndexedScheme` (only the coin-free-step variant returns a time-invariant `Scheme`), deterministic
lower bounds used with it must hold against step-indexed schemes.

Each operation is answered by an adaptive read/write decision tree
(`ProbeTree S w α := OracleComp (@ProbeOp.Result S w) α`) whose internal nodes either read a cell
`i : Fin S` (branching `2 ^ w` ways on its `w`-bit content) or overwrite a cell `i : Fin S` with a
`w`-bit value, while all local computation between probes is uncharged. Three conventions differ
slightly from Miltersen's presentation ([Miltersen1999], §1.2, pp. 1–2):
* **Separate read and write probes:** reads and writes each cost `1` probe, whereas a combined
  decision-assignment node in [Miltersen1999] reads and overwrites the same cell at cost `1`, so
  probe counts here are at most twice Miltersen's.
* **Arbitrary initial memory `init`:** `Scheme.init` and `IndexedScheme.init` allow any initial
  `Mem cells w` rather than requiring `zeroMem`. For deterministic schemes this adds no power, as
  each tree can XOR-relabel reads and writes against a fixed `init` at zero probe cost
  ([Miltersen1999], §1.3, p. 3).
* **Finite cell domain:** memory has `S` cells (`Fin S`) rather than an unbounded sequence
  `C_0, C_1, …`, with `padCells` embedding `S ≤ S'`.

For the read-only embedding of static Boolean `DecisionTree`s into `ProbeTree S 1 α`, see
`Complexity.Computability.CellProbe.DecisionTree`.

## Main definitions

* `Cslib.CellProbe.Mem`, `Cslib.CellProbe.zeroMem`, `Cslib.CellProbe.restrictMem`,
  `Cslib.CellProbe.padMem`: `S`-cell `w`-bit memory configurations, subset snapshots, and cell
  padding.
* `Cslib.CellProbe.ProbeOp`, `Cslib.CellProbe.ProbeOp.Result`, `Cslib.CellProbe.ProbeOp.cell`:
  elementary read/write cell probes and their reply types.
* `Cslib.CellProbe.ProbeTree`, `Cslib.CellProbe.ProbeTree.read`, `Cslib.CellProbe.ProbeTree.write`,
  `Cslib.CellProbe.ProbeTree.run`, `Cslib.CellProbe.ProbeTree.eval`,
  `Cslib.CellProbe.ProbeTree.nextMem`, `Cslib.CellProbe.ProbeTree.probes`,
  `Cslib.CellProbe.ProbeTree.probedCells`, `Cslib.CellProbe.ProbeTree.depth`,
  `Cslib.CellProbe.ProbeTree.padCells`: deterministic adaptive cell-probe trees, stateful execution,
  probe counts, probed-cell sets, worst-case depth, and cell padding.
* `Cslib.CellProbe.Scheme`, `Cslib.CellProbe.IndexedScheme`, `Cslib.CellProbe.Scheme.toIndexed`:
  time-invariant deterministic cell-probe schemes and their time-aware step-indexed relaxation over
  arbitrary operation signatures `(Op, Result)`.
* `Cslib.CellProbe.IndexedScheme.runInterval`, `Cslib.CellProbe.IndexedScheme.probesInterval`,
  `Cslib.CellProbe.IndexedScheme.probedCellsInterval`, `Cslib.CellProbe.IndexedScheme.runSeq`,
  `Cslib.CellProbe.IndexedScheme.seqProbes`, `Cslib.CellProbe.IndexedScheme.probedCellsSeq`,
  `Cslib.CellProbe.IndexedScheme.padCells`: multi-step interval and full-sequence execution, probe
  accounting, and cell padding on `IndexedScheme`.
* `Cslib.CellProbe.Scheme.runFrom`, `Cslib.CellProbe.Scheme.probesFrom`,
  `Cslib.CellProbe.Scheme.probedCellsFrom`, `Cslib.CellProbe.Scheme.runSeq`,
  `Cslib.CellProbe.Scheme.seqProbes`, `Cslib.CellProbe.Scheme.probedCellsSeq`,
  `Cslib.CellProbe.Scheme.padCells`: execution, probe accounting, and cell padding on `Scheme`.

## Main results

* `Cslib.CellProbe.ProbeTree.run_bind`, `Cslib.CellProbe.ProbeTree.probes_bind`,
  `Cslib.CellProbe.ProbeTree.probedCells_bind`: monadic composition laws for stateful runs, probe
  counts, and probed-cell sets.
* `Cslib.CellProbe.ProbeTree.card_probedCells_le_probes`,
  `Cslib.CellProbe.ProbeTree.probes_le_depth`: cardinality of distinct probed cells is bounded by
  pathwise probes, which is bounded by structural tree depth.
* `Cslib.CellProbe.ProbeTree.nextMem_eq_of_notMem_probedCells`,
  `Cslib.CellProbe.ProbeTree.run_eq_of_eq_on_probedCells`: frame and locality/replay — unprobed
  cells retain their initial values, and memories agreeing on `t.probedCells m₁` produce identical
  outputs, probe counts, probed-cell sets, and post-memory values on `t.probedCells m₁`.
* `Cslib.CellProbe.ProbeTree.card_le_pow_depth`,
  `Cslib.CellProbe.ProbeTree.clog_le_depth_of_injective`: standard `2 ^ w`-ary branching lower bound
  `K ≤ (2 ^ w) ^ t.depth` (`⌈log_{2^w} K⌉ ≤ t.depth`) for any tree distinguishing `K` memory states.
* `Cslib.CellProbe.IndexedScheme.nextMem_runInterval_eq_of_notMem_probedCellsInterval`,
  `Cslib.CellProbe.IndexedScheme.runInterval_eq_of_eq_on_probedCellsInterval`: multi-operation
  interval lifts of the frame and locality/replay theorems.

## References

* [M. Minsky, S. Papert, *Perceptrons: An Introduction to Computational Geometry*][MinskyPapert1969]
* [A. C.-C. Yao, *Should Tables Be Sorted?*][Yao1981]
* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
-/

public section

namespace Cslib.CellProbe

universe u

/-! ### Cell memory and subset snapshots -/

/-- Memory state of a cell-probe data structure with `S` cells of `w`-bit words (`S * w` bits
total, with no persistent registers between operations). -/
abbrev Mem (S w : ℕ) : Type := Fin S → Fin (2 ^ w)

/-- All-zero initial memory of `S` cells of `w`-bit words. -/
@[expose] def zeroMem (S w : ℕ) : Mem S w :=
  fun _ => ⟨0, Nat.two_pow_pos w⟩

/-- Cardinality of the `S`-cell `w`-bit memory state space `Mem S w`. -/
theorem card_mem (S w : ℕ) : Fintype.card (Mem S w) = (2 ^ w) ^ S := by
  simp [Mem]

/-- Subset snapshot of memory `m` restricted to a cell set `I : Finset (Fin S)`, defined via
`Finset.restrict`. -/
@[expose] def restrictMem {S w : ℕ} (m : Mem S w) (I : Finset (Fin S)) :
    (i : I) → Fin (2 ^ w) :=
  I.restrict m

@[simp]
theorem restrictMem_apply {S w : ℕ} (m : Mem S w) (I : Finset (Fin S)) (i : I) :
    restrictMem m I i = m i.1 :=
  rfl

/-- Two memories have equal snapshots on `I` iff they agree at every cell in `I`. -/
theorem restrictMem_eq_iff {S w : ℕ} {m₁ m₂ : Mem S w} {I : Finset (Fin S)} :
    restrictMem m₁ I = restrictMem m₂ I ↔ ∀ i ∈ I, m₁ i = m₂ i := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext ⟨i, hi⟩
    exact h i hi

/-- Pad an `S`-cell memory to `S'` cells (`S ≤ S'`) by filling cells `[S, S')` with `0`. -/
@[expose] def padMem {S S' w : ℕ} (_h : S ≤ S') (m : Mem S w) : Mem S' w :=
  fun i => if hi : i.1 < S then m ⟨i.1, hi⟩ else ⟨0, Nat.two_pow_pos w⟩

@[simp]
theorem padMem_castLE {S S' w : ℕ} (h : S ≤ S') (m : Mem S w) (i : Fin S) :
    padMem h m (Fin.castLE h i) = m i := by
  simp [padMem, i.isLt]

theorem padMem_of_ge {S S' w : ℕ} (h : S ≤ S') (m : Mem S w) {i : Fin S'} (hi : S ≤ i.1) :
    padMem h m i = ⟨0, Nat.two_pow_pos w⟩ := by
  have hnot : ¬ i.1 < S := Nat.not_lt.mpr hi
  simp [padMem, hnot]

@[simp]
theorem padMem_update {S S' w : ℕ} (h : S ≤ S') (m : Mem S w) (i : Fin S) (v : Fin (2 ^ w)) :
    Function.update (padMem h m) (Fin.castLE h i) v = padMem h (Function.update m i v) := by
  funext j
  by_cases hj : j = Fin.castLE h i
  · subst hj
    simp [padMem, i.isLt]
  · rw [Function.update_of_ne hj]
    by_cases hlt : j.1 < S
    · have hij : (⟨j.1, hlt⟩ : Fin S) ≠ i := by
        intro heq
        have hval : j.1 = i.1 := congrArg Fin.val heq
        exact hj (Fin.ext hval)
      simp [padMem, hlt, Function.update_of_ne hij]
    · simp [padMem, hlt]

/-! ### Elementary cell-probe operations -/

/-- Elementary cell-probe actions on `S` cells of `w`-bit words. -/
inductive ProbeOp (S w : ℕ) : Type where
  /-- Read the `w`-bit word currently stored in `cell`. -/
  | read (cell : Fin S)
  /-- Overwrite `cell` with `val` (`w`-bit word). -/
  | write (cell : Fin S) (val : Fin (2 ^ w))
  deriving DecidableEq, Repr

instance (S w : ℕ) : Fintype (ProbeOp S w) :=
  Fintype.ofEquiv (Fin S ⊕ (Fin S × Fin (2 ^ w)))
    { toFun := fun
        | .inl i => .read i
        | .inr (i, v) => .write i v
      invFun := fun
        | .read i => .inl i
        | .write i v => .inr (i, v)
      left_inv := fun s => by rcases s with i | ⟨i, v⟩ <;> rfl
      right_inv := fun q => by cases q <;> rfl }

/-- Response type of a single cell probe: `Fin (2 ^ w)` for a read, `PUnit` for a write. -/
abbrev ProbeOp.Result {S w : ℕ} : ProbeOp S w → Type
  | .read _ => Fin (2 ^ w)
  | .write _ _ => PUnit

instance {S w : ℕ} (q : ProbeOp S w) : Fintype (ProbeOp.Result q) := by
  cases q <;> dsimp [ProbeOp.Result] <;> infer_instance

instance {S w : ℕ} (q : ProbeOp S w) : DecidableEq (ProbeOp.Result q) := by
  cases q <;> dsimp [ProbeOp.Result] <;> infer_instance

instance {S w : ℕ} (q : ProbeOp S w) : Inhabited (ProbeOp.Result q) := by
  cases q with
  | read _ => exact ⟨⟨0, Nat.two_pow_pos w⟩⟩
  | write _ _ => exact ⟨PUnit.unit⟩

/-- Every cell-probe reply type has at most `2 ^ w` values. -/
theorem ProbeOp.card_result_le {S w : ℕ} (q : ProbeOp S w) :
    Fintype.card (ProbeOp.Result q) ≤ 2 ^ w := by
  cases q with
  | read _ => simp [ProbeOp.Result]
  | write _ _ =>
    simp only [ProbeOp.Result, Fintype.card_unit]
    exact Nat.two_pow_pos w

/-- Cell index accessed by a `ProbeOp`. -/
@[expose] def ProbeOp.cell {S w : ℕ} : ProbeOp S w → Fin S
  | .read i => i
  | .write i _ => i

@[simp]
theorem ProbeOp.cell_read {S w : ℕ} (i : Fin S) : (ProbeOp.read (w := w) i).cell = i :=
  rfl

@[simp]
theorem ProbeOp.cell_write {S w : ℕ} (i : Fin S) (v : Fin (2 ^ w)) :
    (ProbeOp.write i v).cell = i :=
  rfl

/-! ### Deterministic adaptive cell-probe trees -/

/-- Deterministic adaptive cell-probe decision tree returning `α : Type` on `S` cells of `w` bits.
Defined as `OracleComp (@ProbeOp.Result S w) α`
(`= (PFunctor.mk (ProbeOp S w) ProbeOp.Result).FreeM α`), inheriting `LawfulMonad`, `do`-notation,
and arbitrary uncharged computation in continuations. -/
abbrev ProbeTree (S w : ℕ) (α : Type) : Type :=
  OracleComp (@ProbeOp.Result S w) α

namespace ProbeTree

variable {S S' w : ℕ} {α β : Type}

/-- Read cell `i : Fin S` (`1` probe). -/
@[expose] def read (i : Fin S) : ProbeTree S w (Fin (2 ^ w)) :=
  OracleComp.query (ProbeOp.read (w := w) i)

/-- Write `v : Fin (2 ^ w)` to cell `i : Fin S` (`1` probe). -/
@[expose] def write (i : Fin S) (v : Fin (2 ^ w)) : ProbeTree S w PUnit :=
  OracleComp.query (ProbeOp.write i v)

/-- Execute a deterministic `ProbeTree` from memory `m`, returning `(result, nextMem)`. -/
@[expose] def run : ProbeTree S w α → Mem S w → α × Mem S w
  | .pure a, m => (a, m)
  | .liftBind (.read i) k, m => run (k (m i)) m
  | .liftBind (.write i v) k, m => run (k PUnit.unit) (Function.update m i v)

/-- Return value produced by executing `t` from memory `m`. -/
@[expose] def eval (t : ProbeTree S w α) (m : Mem S w) : α :=
  (t.run m).1

/-- Updated memory state after executing `t` from memory `m`. -/
@[expose] def nextMem (t : ProbeTree S w α) (m : Mem S w) : Mem S w :=
  (t.run m).2

/-- Pathwise number of cell probes (reads plus writes, each charged `1`) executed from `m`. -/
@[expose] def probes : ProbeTree S w α → Mem S w → ℕ
  | .pure _, _ => 0
  | .liftBind (.read i) k, m => 1 + probes (k (m i)) m
  | .liftBind (.write i v) k, m => 1 + probes (k PUnit.unit) (Function.update m i v)

/-- Set of distinct cell indices probed (read or written) along the path executed from `m`. -/
@[expose] def probedCells : ProbeTree S w α → Mem S w → Finset (Fin S)
  | .pure _, _ => ∅
  | .liftBind (.read i) k, m => insert i (probedCells (k (m i)) m)
  | .liftBind (.write i v) k, m =>
      insert i (probedCells (k PUnit.unit) (Function.update m i v))

/-- Worst-case structural depth of a `ProbeTree` across all cell replies. -/
@[expose] def depth : ProbeTree S w α → ℕ
  | .pure _ => 0
  | .liftBind (.read _) k => Finset.univ.sup (fun v => depth (k v)) + 1
  | .liftBind (.write _ _) k => depth (k PUnit.unit) + 1

/-! ### Compositional and structural lemmas for `ProbeTree` -/

@[simp]
theorem run_pure (a : α) (m : Mem S w) : run (pure a : ProbeTree S w α) m = (a, m) :=
  rfl

@[simp]
theorem run_read (i : Fin S) (m : Mem S w) : run (read i : ProbeTree S w _) m = (m i, m) :=
  rfl

@[simp]
theorem run_write (i : Fin S) (v : Fin (2 ^ w)) (m : Mem S w) :
    run (write i v) m = (PUnit.unit, Function.update m i v) :=
  rfl

@[simp]
theorem run_bind (t : ProbeTree S w α) (k : α → ProbeTree S w β) (m : Mem S w) :
    run (t >>= k) m = run (k (t.run m).1) (t.run m).2 := by
  induction t generalizing m with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | read i => exact ih (m i) m
    | write i v => exact ih PUnit.unit (Function.update m i v)

@[simp]
theorem run_map (f : α → β) (t : ProbeTree S w α) (m : Mem S w) :
    run (f <$> t) m = (f (t.run m).1, (t.run m).2) := by
  rw [← bind_pure_comp, run_bind]
  rfl

@[simp]
theorem eval_pure (a : α) (m : Mem S w) : (pure a : ProbeTree S w α).eval m = a :=
  rfl

@[simp]
theorem eval_read (i : Fin S) (m : Mem S w) : (read i : ProbeTree S w _).eval m = m i :=
  rfl

@[simp]
theorem eval_write (i : Fin S) (v : Fin (2 ^ w)) (m : Mem S w) :
    (write i v).eval m = PUnit.unit :=
  rfl

@[simp]
theorem eval_bind (t : ProbeTree S w α) (k : α → ProbeTree S w β) (m : Mem S w) :
    (t >>= k).eval m = (k (t.eval m)).eval (t.nextMem m) := by
  simp [eval, nextMem]

@[simp]
theorem nextMem_pure (a : α) (m : Mem S w) : (pure a : ProbeTree S w α).nextMem m = m :=
  rfl

@[simp]
theorem nextMem_read (i : Fin S) (m : Mem S w) : (read i : ProbeTree S w _).nextMem m = m :=
  rfl

@[simp]
theorem nextMem_write (i : Fin S) (v : Fin (2 ^ w)) (m : Mem S w) :
    (write i v).nextMem m = Function.update m i v :=
  rfl

@[simp]
theorem nextMem_bind (t : ProbeTree S w α) (k : α → ProbeTree S w β) (m : Mem S w) :
    (t >>= k).nextMem m = (k (t.eval m)).nextMem (t.nextMem m) := by
  simp [eval, nextMem]

@[simp]
theorem probes_pure (a : α) (m : Mem S w) : (pure a : ProbeTree S w α).probes m = 0 :=
  rfl

@[simp]
theorem probes_read (i : Fin S) (m : Mem S w) : (read i : ProbeTree S w _).probes m = 1 :=
  rfl

@[simp]
theorem probes_write (i : Fin S) (v : Fin (2 ^ w)) (m : Mem S w) :
    (write i v).probes m = 1 :=
  rfl

@[simp]
theorem probes_bind (t : ProbeTree S w α) (k : α → ProbeTree S w β) (m : Mem S w) :
    (t >>= k).probes m = t.probes m + (k (t.run m).1).probes (t.run m).2 := by
  induction t generalizing m with
  | pure a => simp
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change 1 + probes ((cont (m i)) >>= k) m = 1 + probes (cont (m i)) m + _
      rw [ih (m i) m, Nat.add_assoc]; rfl
    | write i v =>
      change 1 + probes ((cont PUnit.unit) >>= k) (Function.update m i v) =
        1 + probes (cont PUnit.unit) (Function.update m i v) + _
      rw [ih PUnit.unit (Function.update m i v), Nat.add_assoc]; rfl

@[simp]
theorem probes_map (f : α → β) (t : ProbeTree S w α) (m : Mem S w) :
    (f <$> t).probes m = t.probes m := by
  rw [← bind_pure_comp, probes_bind]
  simp

@[simp]
theorem probedCells_pure (a : α) (m : Mem S w) :
    (pure a : ProbeTree S w α).probedCells m = ∅ :=
  rfl

@[simp]
theorem probedCells_read (i : Fin S) (m : Mem S w) :
    (read i : ProbeTree S w _).probedCells m = {i} :=
  rfl

@[simp]
theorem probedCells_write (i : Fin S) (v : Fin (2 ^ w)) (m : Mem S w) :
    (write i v).probedCells m = {i} :=
  rfl

@[simp]
theorem probedCells_bind (t : ProbeTree S w α) (k : α → ProbeTree S w β) (m : Mem S w) :
    (t >>= k).probedCells m =
      t.probedCells m ∪ (k (t.run m).1).probedCells (t.run m).2 := by
  induction t generalizing m with
  | pure a => simp
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change insert i (probedCells ((cont (m i)) >>= k) m) =
        insert i (probedCells (cont (m i)) m) ∪ _
      rw [ih (m i) m, Finset.insert_union]; rfl
    | write i v =>
      change insert i (probedCells ((cont PUnit.unit) >>= k) (Function.update m i v)) =
        insert i (probedCells (cont PUnit.unit) (Function.update m i v)) ∪ _
      rw [ih PUnit.unit (Function.update m i v), Finset.insert_union]; rfl

@[simp]
theorem probedCells_map (f : α → β) (t : ProbeTree S w α) (m : Mem S w) :
    (f <$> t).probedCells m = t.probedCells m := by
  rw [← bind_pure_comp, probedCells_bind]
  simp

@[simp]
theorem depth_pure (a : α) : (pure a : ProbeTree S w α).depth = 0 :=
  rfl

@[simp]
theorem depth_read (i : Fin S) : (read i : ProbeTree S w _).depth = 1 := by
  change (Finset.univ : Finset (Fin (2 ^ w))).sup (fun _ => 0) + 1 = 1
  simp

@[simp]
theorem depth_write (i : Fin S) (v : Fin (2 ^ w)) : (write i v).depth = 1 :=
  rfl

@[simp]
theorem depth_map (f : α → β) (t : ProbeTree S w α) : (f <$> t).depth = t.depth := by
  induction t with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change Finset.univ.sup (fun v => depth (f <$> cont v)) + 1 =
        Finset.univ.sup (fun v => depth (cont v)) + 1
      simp only [ih]
    | write i v =>
      change depth (f <$> cont PUnit.unit) + 1 = depth (cont PUnit.unit) + 1
      rw [ih PUnit.unit]

theorem depth_bind_le (t : ProbeTree S w α) (k : α → ProbeTree S w β) {d : ℕ}
    (hk : ∀ a, (k a).depth ≤ d) :
    (t >>= k).depth ≤ t.depth + d := by
  induction t with
  | pure a => simpa using hk a
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change Finset.univ.sup (fun v => depth (cont v >>= k)) + 1 ≤
        (Finset.univ.sup (fun v => depth (cont v)) + 1) + d
      have hsup : Finset.univ.sup (fun v => depth (cont v >>= k)) ≤
          Finset.univ.sup (fun v => depth (cont v)) + d := by
        refine Finset.sup_le fun v _ => (ih v).trans ?_
        exact Nat.add_le_add_right
          (Finset.le_sup (f := fun u => depth (cont u)) (Finset.mem_univ v)) d
      omega
    | write i v =>
      change depth (cont PUnit.unit >>= k) + 1 ≤ (depth (cont PUnit.unit) + 1) + d
      have h := ih PUnit.unit
      omega

/-- The number of distinct probed cells along a path is at most the number of probes. -/
theorem card_probedCells_le_probes (t : ProbeTree S w α) (m : Mem S w) :
    (t.probedCells m).card ≤ t.probes m := by
  induction t generalizing m with
  | pure a => simp
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change (insert i (probedCells (cont (m i)) m)).card ≤ 1 + probes (cont (m i)) m
      have hcard := Finset.card_insert_le i (probedCells (cont (m i)) m)
      have hsub := ih (m i) m
      omega
    | write i v =>
      change (insert i (probedCells (cont PUnit.unit) (Function.update m i v))).card ≤
        1 + probes (cont PUnit.unit) (Function.update m i v)
      have hcard :=
        Finset.card_insert_le i (probedCells (cont PUnit.unit) (Function.update m i v))
      have hsub := ih PUnit.unit (Function.update m i v)
      omega

/-- Pathwise probe count from any memory is bounded by structural `depth`. -/
theorem probes_le_depth (t : ProbeTree S w α) (m : Mem S w) :
    t.probes m ≤ t.depth := by
  induction t generalizing m with
  | pure a => simp
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change 1 + probes (cont (m i)) m ≤ Finset.univ.sup (fun v => depth (cont v)) + 1
      have hsub : probes (cont (m i)) m ≤ Finset.univ.sup (fun v => depth (cont v)) :=
        (ih (m i) m).trans (Finset.le_sup (f := fun v => depth (cont v)) (Finset.mem_univ (m i)))
      omega
    | write i v =>
      change 1 + probes (cont PUnit.unit) (Function.update m i v) ≤ depth (cont PUnit.unit) + 1
      have hsub := ih PUnit.unit (Function.update m i v)
      omega

theorem card_probedCells_le_depth (t : ProbeTree S w α) (m : Mem S w) :
    (t.probedCells m).card ≤ t.depth :=
  (t.card_probedCells_le_probes m).trans (t.probes_le_depth m)

/-- Structural `depth` characterizes `OracleComp.IsQueryBounded` on `ProbeTree`. -/
theorem isQueryBounded_iff_depth_le (t : ProbeTree S w α) {n : ℕ} :
    t.IsQueryBounded n ↔ t.depth ≤ n := by
  induction t generalizing n with
  | pure a =>
    constructor
    · intro _; exact Nat.zero_le n
    · intro _; exact .pure a n
  | liftBind q cont ih =>
    change OracleComp.IsCostBounded (fun _ => 1) (PFunctor.FreeM.liftBind q cont) n ↔ _
    rw [OracleComp.IsCostBounded.liftBind_iff]
    cases q with
    | read i =>
      change (1 ≤ n ∧ ∀ v, OracleComp.IsQueryBounded (cont v) (n - 1)) ↔
        Finset.univ.sup (fun v => depth (cont v)) + 1 ≤ n
      simp only [ih]
      constructor
      · rintro ⟨hn, hcont⟩
        rw [← Nat.le_sub_iff_add_le hn]
        exact Finset.sup_le fun v _ => hcont v
      · intro hsup
        refine ⟨by omega, fun v => ?_⟩
        have hv : depth (cont v) ≤ Finset.univ.sup (fun v => depth (cont v)) :=
          Finset.le_sup (f := fun v => depth (cont v)) (Finset.mem_univ v)
        exact hv.trans (Nat.le_sub_of_add_le hsup)
    | write i v =>
      change (1 ≤ n ∧ ∀ u : PUnit, OracleComp.IsQueryBounded (cont u) (n - 1)) ↔
        depth (cont PUnit.unit) + 1 ≤ n
      simp only [ih]
      constructor
      · rintro ⟨hn, hcont⟩
        have hu := hcont PUnit.unit
        omega
      · intro hle
        exact ⟨by omega, fun u => by cases u; omega⟩

/-! ### Frame and locality / replay -/

/-- Any cell outside `t.probedCells m` retains its initial value in `(t.run m).2`. -/
theorem nextMem_eq_of_notMem_probedCells (t : ProbeTree S w α) (m : Mem S w) {i : Fin S}
    (hi : i ∉ t.probedCells m) :
    (t.run m).2 i = m i := by
  induction t generalizing m with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | read j =>
      change i ∉ insert j (probedCells (cont (m j)) m) at hi
      rw [Finset.mem_insert, not_or] at hi
      exact ih (m j) m hi.2
    | write j v =>
      change i ∉ insert j (probedCells (cont PUnit.unit) (Function.update m j v)) at hi
      rw [Finset.mem_insert, not_or] at hi
      change (run (cont PUnit.unit) (Function.update m j v)).2 i = m i
      rw [ih PUnit.unit (Function.update m j v) hi.2, Function.update_of_ne hi.1]

/-- **Locality and replay for deterministic `ProbeTree`s:** if `m₂` agrees with `m₁` on
`t.probedCells m₁`, then executing `t` from `m₂` produces the exact same return value, probe count,
probed-cell set, and post-memory contents on `t.probedCells m₁` (for cells outside
`t.probedCells m₁`, see `nextMem_eq_of_notMem_probedCells`). -/
theorem run_eq_of_eq_on_probedCells (t : ProbeTree S w α) {m₁ m₂ : Mem S w}
    (h : ∀ i ∈ t.probedCells m₁, m₂ i = m₁ i) :
    (t.run m₂).1 = (t.run m₁).1 ∧
      t.probes m₂ = t.probes m₁ ∧
      t.probedCells m₂ = t.probedCells m₁ ∧
      (∀ i ∈ t.probedCells m₁, (t.run m₂).2 i = (t.run m₁).2 i) := by
  induction t generalizing m₁ m₂ with
  | pure a =>
    simp
  | liftBind q cont ih =>
    cases q with
    | read j =>
      change ∀ i ∈ insert j (probedCells (cont (m₁ j)) m₁), m₂ i = m₁ i at h
      have hj : m₂ j = m₁ j := h j (Finset.mem_insert_self j _)
      have hsub : ∀ i ∈ probedCells (cont (m₁ j)) m₁, m₂ i = m₁ i :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      obtain ⟨hout, hpr, hcells, hmem_in⟩ := ih (m₁ j) hsub
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (run (cont (m₂ j)) m₂).1 = (run (cont (m₁ j)) m₁).1
        rw [hj, hout]
      · change 1 + probes (cont (m₂ j)) m₂ = 1 + probes (cont (m₁ j)) m₁
        rw [hj, hpr]
      · change insert j (probedCells (cont (m₂ j)) m₂) =
          insert j (probedCells (cont (m₁ j)) m₁)
        rw [hj, hcells]
      · intro i hi
        change (run (cont (m₂ j)) m₂).2 i = (run (cont (m₁ j)) m₁).2 i
        rw [hj]
        by_cases hisub : i ∈ probedCells (cont (m₁ j)) m₁
        · exact hmem_in i hisub
        · have hij : i = j := by
            rcases Finset.mem_insert.mp hi with rfl | hmem
            · rfl
            · exact absurd hmem hisub
          subst hij
          have hisub₂ : i ∉ probedCells (cont (m₁ i)) m₂ := by rwa [hcells]
          rw [nextMem_eq_of_notMem_probedCells (cont (m₁ i)) m₂ hisub₂,
            nextMem_eq_of_notMem_probedCells (cont (m₁ i)) m₁ hisub, hj]
    | write j v =>
      change ∀ i ∈ insert j (probedCells (cont PUnit.unit) (Function.update m₁ j v)),
        m₂ i = m₁ i at h
      set m₁' := Function.update m₁ j v
      set m₂' := Function.update m₂ j v
      have hsub : ∀ i ∈ probedCells (cont PUnit.unit) m₁', m₂' i = m₁' i := by
        intro i hi
        by_cases hij : i = j
        · subst hij; simp [m₁', m₂']
        · simp only [m₁', m₂', Function.update_of_ne hij]
          exact h i (Finset.mem_insert_of_mem hi)
      obtain ⟨hout, hpr, hcells, hmem_in⟩ := ih PUnit.unit hsub
      refine ⟨hout, ?_, ?_, ?_⟩
      · change 1 + probes (cont PUnit.unit) m₂' = 1 + probes (cont PUnit.unit) m₁'
        rw [hpr]
      · change insert j (probedCells (cont PUnit.unit) m₂') =
          insert j (probedCells (cont PUnit.unit) m₁')
        rw [hcells]
      · intro i hi
        change (run (cont PUnit.unit) m₂').2 i = (run (cont PUnit.unit) m₁').2 i
        by_cases hisub : i ∈ probedCells (cont PUnit.unit) m₁'
        · exact hmem_in i hisub
        · have hij : i = j := by
            rcases Finset.mem_insert.mp hi with rfl | hmem
            · rfl
            · exact absurd hmem hisub
          subst hij
          have hisub₂ : i ∉ probedCells (cont PUnit.unit) m₂' := by rwa [hcells]
          rw [nextMem_eq_of_notMem_probedCells (cont PUnit.unit) m₂' hisub₂,
            nextMem_eq_of_notMem_probedCells (cont PUnit.unit) m₁' hisub]
          simp [m₁', m₂']

/-! ### Information-theoretic counting lower bound -/

/-- **Standard `2 ^ w`-ary branching bound:** if `t : ProbeTree S w α` produces distinct return
values across `(enc x)` for all `x ∈ I`, then `I.card ≤ (2 ^ w) ^ t.depth`. -/
theorem card_le_pow_depth {ι : Type*} (t : ProbeTree S w α) (I : Finset ι) (enc : ι → Mem S w)
    (hinj : Set.InjOn (fun x => (t.run (enc x)).1) ↑I) :
    I.card ≤ (2 ^ w) ^ t.depth := by
  classical
  induction t generalizing I enc with
  | pure a =>
    have hcard : I.card ≤ 1 :=
      Finset.card_le_one.mpr fun x hx y hy => hinj hx hy rfl
    simpa only [depth, Nat.pow_zero] using hcard
  | liftBind q cont ih =>
    cases q with
    | read j =>
      change I.card ≤ (2 ^ w) ^ (Finset.univ.sup (fun v => depth (cont v)) + 1)
      set d := Finset.univ.sup fun v => depth (cont v)
      rw [Finset.card_eq_sum_card_fiberwise (f := fun x => enc x j) (t := Finset.univ)
        (fun x _ => Finset.mem_univ _)]
      calc
        (∑ v : Fin (2 ^ w), (I.filter fun x => enc x j = v).card)
          ≤ ∑ _v : Fin (2 ^ w), (2 ^ w) ^ d := by
            refine Finset.sum_le_sum fun v _ => ?_
            have hinj_v : Set.InjOn (fun x => (run (cont v) (enc x)).1)
                ↑(I.filter fun x => enc x j = v) := by
              intro x hx y hy heq
              have hx' := Finset.mem_filter.mp hx
              have hy' := Finset.mem_filter.mp hy
              refine hinj hx'.1 hy'.1 ?_
              change (run (cont (enc x j)) (enc x)).1 = (run (cont (enc y j)) (enc y)).1
              rw [hx'.2, hy'.2]
              exact heq
            exact (ih v _ enc hinj_v).trans
              (Nat.pow_le_pow_right (Nat.two_pow_pos w)
                (Finset.le_sup (f := fun u => depth (cont u)) (Finset.mem_univ v)))
        _ = (2 ^ w) * (2 ^ w) ^ d := by simp [Finset.sum_const]
        _ = (2 ^ w) ^ (d + 1) := by ring
    | write j v =>
      change I.card ≤ (2 ^ w) ^ (depth (cont PUnit.unit) + 1)
      have hinj' : Set.InjOn (fun x => (run (cont PUnit.unit) (Function.update (enc x) j v)).1)
          ↑I := hinj
      exact (ih PUnit.unit I (fun x => Function.update (enc x) j v) hinj').trans
        (Nat.pow_le_pow_right (Nat.two_pow_pos w) (Nat.le_succ _))

/-- Standard `2 ^ w`-ary branching bound: if `t : ProbeTree S w α` distinguishes every input of a
finite type `ι` via `enc : ι → Mem S w`, then `Fintype.card ι ≤ (2 ^ w) ^ t.depth`. -/
theorem card_le_pow_depth_of_injective {ι : Type*} [Fintype ι] (t : ProbeTree S w α)
    (enc : ι → Mem S w) (hinj : Function.Injective (fun x => (t.run (enc x)).1)) :
    Fintype.card ι ≤ (2 ^ w) ^ t.depth := by
  simpa only [Finset.card_univ] using
    t.card_le_pow_depth Finset.univ enc (hinj.injOn)

/-- Information-theoretic worst-case cell-probe lower bound `⌈log_{2^w} |ι|⌉ ≤ t.depth` whenever
`t` distinguishes all inputs of `ι` (for `w = 0`, `Nat.clog 1 _ = 0`). -/
theorem clog_le_depth_of_injective {ι : Type*} [Fintype ι] (t : ProbeTree S w α)
    (enc : ι → Mem S w) (hinj : Function.Injective (fun x => (t.run (enc x)).1)) :
    Nat.clog (2 ^ w) (Fintype.card ι) ≤ t.depth := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · exact (Nat.clog_le_iff_le_pow (Nat.one_lt_two_pow hw.ne')).mpr
      (t.card_le_pow_depth_of_injective enc hinj)

/-! ### Cell padding on `ProbeTree` -/

/-- Lift a `ProbeTree S w α` to `S'` cells (`S ≤ S'`) by embedding cell indices via `Fin.castLE`. -/
@[expose] def padCells (h : S ≤ S') : ProbeTree S w α → ProbeTree S' w α
  | .pure a => .pure a
  | .liftBind (.read i) k => .liftBind (.read (Fin.castLE h i)) fun v => padCells h (k v)
  | .liftBind (.write i v) k => .liftBind (.write (Fin.castLE h i) v) fun u => padCells h (k u)

@[simp]
theorem run_padCells (h : S ≤ S') (t : ProbeTree S w α) (m : Mem S w) :
    (t.padCells h).run (padMem h m) = ((t.run m).1, padMem h (t.run m).2) := by
  induction t generalizing m with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change run (padCells h (cont (padMem h m (Fin.castLE h i)))) (padMem h m) = _
      rw [padMem_castLE]
      exact ih (m i) m
    | write i v =>
      change run (padCells h (cont PUnit.unit))
        (Function.update (padMem h m) (Fin.castLE h i) v) = _
      rw [padMem_update]
      exact ih PUnit.unit (Function.update m i v)

@[simp]
theorem probes_padCells (h : S ≤ S') (t : ProbeTree S w α) (m : Mem S w) :
    (t.padCells h).probes (padMem h m) = t.probes m := by
  induction t generalizing m with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change 1 + probes (padCells h (cont (padMem h m (Fin.castLE h i)))) (padMem h m) = _
      rw [padMem_castLE, ih (m i) m]
      rfl
    | write i v =>
      change 1 + probes (padCells h (cont PUnit.unit))
        (Function.update (padMem h m) (Fin.castLE h i) v) = _
      rw [padMem_update, ih PUnit.unit (Function.update m i v)]
      rfl

@[simp]
theorem depth_padCells (h : S ≤ S') (t : ProbeTree S w α) :
    (t.padCells h).depth = t.depth := by
  induction t with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change Finset.univ.sup (fun v => depth (padCells h (cont v))) + 1 = _
      simp only [ih]
      rfl
    | write i v =>
      change depth (padCells h (cont PUnit.unit)) + 1 = _
      rw [ih PUnit.unit]
      rfl

end ProbeTree

/-! ### Deterministic cell-probe schemes and multi-step interval locality -/

/-- Time-invariant deterministic cell-probe scheme with `cells` cells of `w`-bit words.
Persistent state between operations consists solely of `Mem cells w`. -/
structure Scheme (Op : Type u) (Result : Op → Type) (cells w : ℕ) where
  /-- Initial cell memory (0 probes; persistent state lives in `cells` words). -/
  init : Mem cells w
  /-- Adaptive read/write cell-probe decision tree executed for each operation `o : Op`. -/
  step : (o : Op) → ProbeTree cells w (Result o)

/-- **Time-aware relaxation** of a deterministic cell-probe scheme: `step` receives the global
operation index `t : ℕ` (a free clock outside cell memory) in addition to `o : Op`. Fixing
per-operation private coins via the averaging (coin-fixing) argument, the easy direction of Yao's
principle [Yao1977], produces an `IndexedScheme`, so deterministic lower bounds paired with it must
hold against step-indexed schemes. -/
structure IndexedScheme (Op : Type u) (Result : Op → Type) (cells w : ℕ) where
  /-- Initial cell memory (0 probes). -/
  init : Mem cells w
  /-- Adaptive read/write cell-probe decision tree executed at step `t` on operation `o`. -/
  step : ℕ → (o : Op) → ProbeTree cells w (Result o)

/-- Embed any time-invariant `Scheme` as a step-indexed `IndexedScheme`. -/
@[expose] def Scheme.toIndexed {Op : Type u} {Result : Op → Type} {cells w : ℕ}
    (P : Scheme Op Result cells w) : IndexedScheme Op Result cells w where
  init := P.init
  step _ := P.step

namespace IndexedScheme

variable {Op : Type u} {Result : Op → Type} {cells cells' w : ℕ}

/-- Execute an operation slice `ops : List Op` starting at step index `t₀` and memory `m`,
returning `(transcript, postMem)`. -/
@[expose] def runInterval (D : IndexedScheme Op Result cells w) :
    ℕ → Mem cells w → List Op → List (Sigma Result) × Mem cells w
  | _, m, [] => ([], m)
  | t₀, m, o :: ops =>
      let res := (D.step t₀ o).run m
      let tail := D.runInterval (t₀ + 1) res.2 ops
      (⟨o, res.1⟩ :: tail.1, tail.2)

/-- Total number of cell probes incurred while executing `ops` from step index `t₀` and `m`. -/
@[expose] def probesInterval (D : IndexedScheme Op Result cells w) :
    ℕ → Mem cells w → List Op → ℕ
  | _, _, [] => 0
  | t₀, m, o :: ops =>
      (D.step t₀ o).probes m + D.probesInterval (t₀ + 1) ((D.step t₀ o).run m).2 ops

/-- Set of distinct cell indices probed during `ops` starting at step index `t₀` and memory `m`. -/
@[expose] def probedCellsInterval (D : IndexedScheme Op Result cells w) :
    ℕ → Mem cells w → List Op → Finset (Fin cells)
  | _, _, [] => ∅
  | t₀, m, o :: ops =>
      (D.step t₀ o).probedCells m ∪
        D.probedCellsInterval (t₀ + 1) ((D.step t₀ o).run m).2 ops

/-- Execute `ops` from step `0` and initial memory `D.init`, returning `(transcript, postMem)`. -/
@[expose] def runSeq (D : IndexedScheme Op Result cells w) (ops : List Op) :
    List (Sigma Result) × Mem cells w :=
  D.runInterval 0 D.init ops

/-- Total number of cell probes executed across `ops` starting from `D.init`. -/
@[expose] def seqProbes (D : IndexedScheme Op Result cells w) (ops : List Op) : ℕ :=
  D.probesInterval 0 D.init ops

/-- Set of distinct cells probed across `ops` starting from `D.init`. -/
@[expose] def probedCellsSeq (D : IndexedScheme Op Result cells w) (ops : List Op) :
    Finset (Fin cells) :=
  D.probedCellsInterval 0 D.init ops

@[simp]
theorem runInterval_nil (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w) :
    D.runInterval t₀ m [] = ([], m) :=
  rfl

@[simp]
theorem runInterval_cons (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (o : Op) (ops : List Op) :
    D.runInterval t₀ m (o :: ops) =
      (⟨o, ((D.step t₀ o).run m).1⟩ ::
        (D.runInterval (t₀ + 1) ((D.step t₀ o).run m).2 ops).1,
       (D.runInterval (t₀ + 1) ((D.step t₀ o).run m).2 ops).2) :=
  rfl

@[simp]
theorem probesInterval_nil (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w) :
    D.probesInterval t₀ m [] = 0 :=
  rfl

@[simp]
theorem probesInterval_cons (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (o : Op) (ops : List Op) :
    D.probesInterval t₀ m (o :: ops) =
      (D.step t₀ o).probes m + D.probesInterval (t₀ + 1) ((D.step t₀ o).run m).2 ops :=
  rfl

@[simp]
theorem probedCellsInterval_nil (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w) :
    D.probedCellsInterval t₀ m [] = ∅ :=
  rfl

@[simp]
theorem probedCellsInterval_cons (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (o : Op) (ops : List Op) :
    D.probedCellsInterval t₀ m (o :: ops) =
      (D.step t₀ o).probedCells m ∪
        D.probedCellsInterval (t₀ + 1) ((D.step t₀ o).run m).2 ops :=
  rfl

theorem runInterval_append (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (ops₁ ops₂ : List Op) :
    D.runInterval t₀ m (ops₁ ++ ops₂) =
      ((D.runInterval t₀ m ops₁).1 ++
        (D.runInterval (t₀ + ops₁.length) (D.runInterval t₀ m ops₁).2 ops₂).1,
       (D.runInterval (t₀ + ops₁.length) (D.runInterval t₀ m ops₁).2 ops₂).2) := by
  induction ops₁ generalizing t₀ m with
  | nil => simp
  | cons o rest ih =>
    simp only [List.cons_append, runInterval_cons, List.length_cons, ih]
    have hidx : t₀ + 1 + rest.length = t₀ + (rest.length + 1) := by omega
    rw [hidx]

theorem probesInterval_append (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (ops₁ ops₂ : List Op) :
    D.probesInterval t₀ m (ops₁ ++ ops₂) =
      D.probesInterval t₀ m ops₁ +
        D.probesInterval (t₀ + ops₁.length) (D.runInterval t₀ m ops₁).2 ops₂ := by
  induction ops₁ generalizing t₀ m with
  | nil => simp
  | cons o rest ih =>
    simp only [List.cons_append, probesInterval_cons, runInterval_cons, List.length_cons, ih]
    have hidx : t₀ + 1 + rest.length = t₀ + (rest.length + 1) := by omega
    rw [hidx, Nat.add_assoc]

theorem probedCellsInterval_append (D : IndexedScheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (ops₁ ops₂ : List Op) :
    D.probedCellsInterval t₀ m (ops₁ ++ ops₂) =
      D.probedCellsInterval t₀ m ops₁ ∪
        D.probedCellsInterval (t₀ + ops₁.length) (D.runInterval t₀ m ops₁).2 ops₂ := by
  induction ops₁ generalizing t₀ m with
  | nil => simp
  | cons o rest ih =>
    simp only [List.cons_append, probedCellsInterval_cons, runInterval_cons, List.length_cons, ih]
    have hidx : t₀ + 1 + rest.length = t₀ + (rest.length + 1) := by omega
    rw [hidx, Finset.union_assoc]

theorem card_probedCellsInterval_le_probesInterval (D : IndexedScheme Op Result cells w)
    (t₀ : ℕ) (m : Mem cells w) (ops : List Op) :
    (D.probedCellsInterval t₀ m ops).card ≤ D.probesInterval t₀ m ops := by
  induction ops generalizing t₀ m with
  | nil => simp
  | cons o rest ih =>
    simp only [probedCellsInterval_cons, probesInterval_cons]
    calc
      ((D.step t₀ o).probedCells m ∪
          D.probedCellsInterval (t₀ + 1) ((D.step t₀ o).run m).2 rest).card
        ≤ ((D.step t₀ o).probedCells m).card +
            (D.probedCellsInterval (t₀ + 1) ((D.step t₀ o).run m).2 rest).card :=
          Finset.card_union_le _ _
      _ ≤ (D.step t₀ o).probes m +
            D.probesInterval (t₀ + 1) ((D.step t₀ o).run m).2 rest :=
          Nat.add_le_add ((D.step t₀ o).card_probedCells_le_probes m) (ih _ _)

/-- Cells outside `D.probedCellsInterval t₀ m ops` are unchanged in `(D.runInterval t₀ m ops).2`. -/
theorem nextMem_runInterval_eq_of_notMem_probedCellsInterval (D : IndexedScheme Op Result cells w)
    (t₀ : ℕ) (m : Mem cells w) (ops : List Op) {i : Fin cells}
    (hi : i ∉ D.probedCellsInterval t₀ m ops) :
    (D.runInterval t₀ m ops).2 i = m i := by
  induction ops generalizing t₀ m with
  | nil => rfl
  | cons o rest ih =>
    simp only [probedCellsInterval_cons, Finset.mem_union, not_or] at hi
    simp only [runInterval_cons]
    rw [ih (t₀ + 1) ((D.step t₀ o).run m).2 hi.2,
      (D.step t₀ o).nextMem_eq_of_notMem_probedCells m hi.1]

/-- Cells outside `D.probedCellsSeq ops` retain `D.init` in `(D.runSeq ops).2`. -/
theorem nextMem_runSeq_eq_of_notMem_probedCellsSeq (D : IndexedScheme Op Result cells w)
    (ops : List Op) {i : Fin cells} (hi : i ∉ D.probedCellsSeq ops) :
    (D.runSeq ops).2 i = D.init i :=
  D.nextMem_runInterval_eq_of_notMem_probedCellsInterval 0 D.init ops hi

/-- **Multi-step interval locality and replay:** if `m₂` agrees with `m₁` on
`D.probedCellsInterval t₀ m₁ ops`, then simulating `ops` from `(t₀, m₂)` produces the exact same
transcript, probe count, probed-cell set, and post-memory contents on
`D.probedCellsInterval t₀ m₁ ops` (for cells outside `D.probedCellsInterval t₀ m₁ ops`, see
`nextMem_runInterval_eq_of_notMem_probedCellsInterval`). -/
theorem runInterval_eq_of_eq_on_probedCellsInterval (D : IndexedScheme Op Result cells w)
    (t₀ : ℕ) {m₁ m₂ : Mem cells w} (ops : List Op)
    (h : ∀ i ∈ D.probedCellsInterval t₀ m₁ ops, m₂ i = m₁ i) :
    (D.runInterval t₀ m₂ ops).1 = (D.runInterval t₀ m₁ ops).1 ∧
      D.probesInterval t₀ m₂ ops = D.probesInterval t₀ m₁ ops ∧
      D.probedCellsInterval t₀ m₂ ops = D.probedCellsInterval t₀ m₁ ops ∧
      (∀ i ∈ D.probedCellsInterval t₀ m₁ ops,
        (D.runInterval t₀ m₂ ops).2 i = (D.runInterval t₀ m₁ ops).2 i) := by
  induction ops generalizing t₀ m₁ m₂ with
  | nil => simp
  | cons o rest ih =>
    have hstep : ∀ i ∈ (D.step t₀ o).probedCells m₁, m₂ i = m₁ i :=
      fun i hi => h i (Finset.mem_union_left _ hi)
    obtain ⟨hout₁, hpr₁, hcells₁, hmem_in₁⟩ :=
      (D.step t₀ o).run_eq_of_eq_on_probedCells hstep
    have hrest : ∀ i ∈ D.probedCellsInterval (t₀ + 1) ((D.step t₀ o).run m₁).2 rest,
        ((D.step t₀ o).run m₂).2 i = ((D.step t₀ o).run m₁).2 i := by
      intro i hi
      by_cases hi₁ : i ∈ (D.step t₀ o).probedCells m₁
      · exact hmem_in₁ i hi₁
      · have hi₁' : i ∉ (D.step t₀ o).probedCells m₂ := by rwa [hcells₁]
        rw [(D.step t₀ o).nextMem_eq_of_notMem_probedCells m₂ hi₁',
          (D.step t₀ o).nextMem_eq_of_notMem_probedCells m₁ hi₁]
        exact h i (Finset.mem_union_right _ hi)
    obtain ⟨hout₂, hpr₂, hcells₂, hmem_in₂⟩ := ih (t₀ + 1) hrest
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [runInterval_cons, hout₁, hout₂]
    · simp only [probesInterval_cons, hpr₁, hpr₂]
    · simp only [probedCellsInterval_cons, hcells₁, hcells₂]
    · intro i hi
      simp only [runInterval_cons]
      by_cases hi₂ : i ∈ D.probedCellsInterval (t₀ + 1) ((D.step t₀ o).run m₁).2 rest
      · exact hmem_in₂ i hi₂
      · have hi₁ : i ∈ (D.step t₀ o).probedCells m₁ := by
          rcases Finset.mem_union.mp hi with h1 | h2
          · exact h1
          · exact absurd h2 hi₂
        have hi₂' : i ∉ D.probedCellsInterval (t₀ + 1) ((D.step t₀ o).run m₂).2 rest := by
          rwa [hcells₂]
        rw [D.nextMem_runInterval_eq_of_notMem_probedCellsInterval
              (t₀ + 1) ((D.step t₀ o).run m₂).2 rest hi₂',
            D.nextMem_runInterval_eq_of_notMem_probedCellsInterval
              (t₀ + 1) ((D.step t₀ o).run m₁).2 rest hi₂]
        exact hmem_in₁ i hi₁

/-- Pad an `IndexedScheme` from `cells` cells to `cells'` cells (`cells ≤ cells'`). -/
@[expose] def padCells (h : cells ≤ cells') (D : IndexedScheme Op Result cells w) :
    IndexedScheme Op Result cells' w where
  init := padMem h D.init
  step t o := (D.step t o).padCells h

@[simp]
theorem padCells_init (h : cells ≤ cells') (D : IndexedScheme Op Result cells w) :
    (D.padCells h).init = padMem h D.init :=
  rfl

@[simp]
theorem padCells_step (h : cells ≤ cells') (D : IndexedScheme Op Result cells w) (t : ℕ) (o : Op) :
    (D.padCells h).step t o = (D.step t o).padCells h :=
  rfl

theorem runInterval_padCells (h : cells ≤ cells') (D : IndexedScheme Op Result cells w)
    (t₀ : ℕ) (m : Mem cells w) (ops : List Op) :
    (D.padCells h).runInterval t₀ (padMem h m) ops =
      ((D.runInterval t₀ m ops).1, padMem h (D.runInterval t₀ m ops).2) := by
  induction ops generalizing t₀ m with
  | nil => rfl
  | cons o rest ih =>
    simp only [runInterval_cons, padCells_step, ProbeTree.run_padCells, ih]

theorem probesInterval_padCells (h : cells ≤ cells') (D : IndexedScheme Op Result cells w)
    (t₀ : ℕ) (m : Mem cells w) (ops : List Op) :
    (D.padCells h).probesInterval t₀ (padMem h m) ops = D.probesInterval t₀ m ops := by
  induction ops generalizing t₀ m with
  | nil => rfl
  | cons o rest ih =>
    simp only [probesInterval_cons, padCells_step, ProbeTree.probes_padCells,
      ProbeTree.run_padCells, ih]

@[simp]
theorem runSeq_padCells (h : cells ≤ cells') (D : IndexedScheme Op Result cells w)
    (ops : List Op) :
    (D.padCells h).runSeq ops = ((D.runSeq ops).1, padMem h (D.runSeq ops).2) :=
  D.runInterval_padCells h 0 D.init ops

@[simp]
theorem seqProbes_padCells (h : cells ≤ cells') (D : IndexedScheme Op Result cells w)
    (ops : List Op) :
    (D.padCells h).seqProbes ops = D.seqProbes ops :=
  D.probesInterval_padCells h 0 D.init ops

end IndexedScheme

namespace Scheme

variable {Op : Type u} {Result : Op → Type} {cells cells' w : ℕ}

/-- Execute `ops` from memory `m` under a time-invariant `Scheme`. -/
@[expose] def runFrom (P : Scheme Op Result cells w) (m : Mem cells w) (ops : List Op) :
    List (Sigma Result) × Mem cells w :=
  P.toIndexed.runInterval 0 m ops

/-- Total probes incurred while executing `ops` from memory `m` under `P`. -/
@[expose] def probesFrom (P : Scheme Op Result cells w) (m : Mem cells w) (ops : List Op) : ℕ :=
  P.toIndexed.probesInterval 0 m ops

/-- Distinct cells probed while executing `ops` from memory `m` under `P`. -/
@[expose] def probedCellsFrom (P : Scheme Op Result cells w) (m : Mem cells w) (ops : List Op) :
    Finset (Fin cells) :=
  P.toIndexed.probedCellsInterval 0 m ops

/-- Execute `ops` from initial memory `P.init`, returning `(transcript, postMem)`. -/
@[expose] def runSeq (P : Scheme Op Result cells w) (ops : List Op) :
    List (Sigma Result) × Mem cells w :=
  P.toIndexed.runSeq ops

/-- Total number of cell probes executed across `ops` starting from `P.init`. -/
@[expose] def seqProbes (P : Scheme Op Result cells w) (ops : List Op) : ℕ :=
  P.toIndexed.seqProbes ops

/-- Set of distinct cells probed across `ops` starting from `P.init`. -/
@[expose] def probedCellsSeq (P : Scheme Op Result cells w) (ops : List Op) :
    Finset (Fin cells) :=
  P.toIndexed.probedCellsSeq ops

/-- Pad a time-invariant `Scheme` from `cells` cells to `cells'` cells (`cells ≤ cells'`). -/
@[expose] def padCells (h : cells ≤ cells') (P : Scheme Op Result cells w) :
    Scheme Op Result cells' w where
  init := padMem h P.init
  step o := (P.step o).padCells h

@[simp]
theorem toIndexed_padCells (h : cells ≤ cells') (P : Scheme Op Result cells w) :
    (P.padCells h).toIndexed = P.toIndexed.padCells h :=
  rfl

@[simp]
theorem toIndexed_runSeq (P : Scheme Op Result cells w) (ops : List Op) :
    P.toIndexed.runSeq ops = P.runSeq ops :=
  rfl

@[simp]
theorem toIndexed_seqProbes (P : Scheme Op Result cells w) (ops : List Op) :
    P.toIndexed.seqProbes ops = P.seqProbes ops :=
  rfl

@[simp]
theorem toIndexed_step (P : Scheme Op Result cells w) (t : ℕ) (o : Op) :
    P.toIndexed.step t o = P.step o :=
  rfl

theorem toIndexed_runInterval_eq (P : Scheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (ops : List Op) :
    P.toIndexed.runInterval t₀ m ops = P.runFrom m ops := by
  have hgen : ∀ (t₁ t₂ : ℕ) (m : Mem cells w),
      P.toIndexed.runInterval t₁ m ops = P.toIndexed.runInterval t₂ m ops := by
    induction ops with
    | nil => intro _ _ _; rfl
    | cons o rest ih =>
      intro t₁ t₂ m
      simp only [IndexedScheme.runInterval_cons, toIndexed_step, ih (t₁ + 1) (t₂ + 1)]
  exact hgen t₀ 0 m

theorem toIndexed_probesInterval_eq (P : Scheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (ops : List Op) :
    P.toIndexed.probesInterval t₀ m ops = P.probesFrom m ops := by
  have hgen : ∀ (t₁ t₂ : ℕ) (m : Mem cells w),
      P.toIndexed.probesInterval t₁ m ops = P.toIndexed.probesInterval t₂ m ops := by
    induction ops with
    | nil => intro _ _ _; rfl
    | cons o rest ih =>
      intro t₁ t₂ m
      simp only [IndexedScheme.probesInterval_cons, toIndexed_step, ih (t₁ + 1) (t₂ + 1)]
  exact hgen t₀ 0 m

theorem toIndexed_probedCellsInterval_eq (P : Scheme Op Result cells w) (t₀ : ℕ) (m : Mem cells w)
    (ops : List Op) :
    P.toIndexed.probedCellsInterval t₀ m ops = P.probedCellsFrom m ops := by
  have hgen : ∀ (t₁ t₂ : ℕ) (m : Mem cells w),
      P.toIndexed.probedCellsInterval t₁ m ops = P.toIndexed.probedCellsInterval t₂ m ops := by
    induction ops with
    | nil => intro _ _ _; rfl
    | cons o rest ih =>
      intro t₁ t₂ m
      simp only [IndexedScheme.probedCellsInterval_cons, toIndexed_step, ih (t₁ + 1) (t₂ + 1)]
  exact hgen t₀ 0 m

@[simp]
theorem runFrom_nil (P : Scheme Op Result cells w) (m : Mem cells w) :
    P.runFrom m [] = ([], m) :=
  rfl

@[simp]
theorem runFrom_cons (P : Scheme Op Result cells w) (m : Mem cells w) (o : Op) (ops : List Op) :
    P.runFrom m (o :: ops) =
      (⟨o, ((P.step o).run m).1⟩ :: (P.runFrom ((P.step o).run m).2 ops).1,
       (P.runFrom ((P.step o).run m).2 ops).2) := by
  change P.toIndexed.runInterval 0 m (o :: ops) = _
  rw [IndexedScheme.runInterval_cons, toIndexed_step, toIndexed_runInterval_eq]

@[simp]
theorem probesFrom_nil (P : Scheme Op Result cells w) (m : Mem cells w) :
    P.probesFrom m [] = 0 :=
  rfl

@[simp]
theorem probesFrom_cons (P : Scheme Op Result cells w) (m : Mem cells w) (o : Op)
    (ops : List Op) :
    P.probesFrom m (o :: ops) =
      (P.step o).probes m + P.probesFrom ((P.step o).run m).2 ops := by
  change P.toIndexed.probesInterval 0 m (o :: ops) = _
  rw [IndexedScheme.probesInterval_cons, toIndexed_step, toIndexed_probesInterval_eq]

/-- Cells outside `P.probedCellsFrom m ops` are unchanged in `(P.runFrom m ops).2`. -/
theorem nextMem_runFrom_eq_of_notMem_probedCellsFrom (P : Scheme Op Result cells w)
    (m : Mem cells w) (ops : List Op) {i : Fin cells} (hi : i ∉ P.probedCellsFrom m ops) :
    (P.runFrom m ops).2 i = m i :=
  P.toIndexed.nextMem_runInterval_eq_of_notMem_probedCellsInterval 0 m ops hi

/-- Cells outside `P.probedCellsSeq ops` retain `P.init` in `(P.runSeq ops).2`. -/
theorem nextMem_runSeq_eq_of_notMem_probedCellsSeq (P : Scheme Op Result cells w)
    (ops : List Op) {i : Fin cells} (hi : i ∉ P.probedCellsSeq ops) :
    (P.runSeq ops).2 i = P.init i :=
  P.toIndexed.nextMem_runSeq_eq_of_notMem_probedCellsSeq ops hi

theorem runFrom_eq_of_eq_on_probedCellsFrom (P : Scheme Op Result cells w) {m₁ m₂ : Mem cells w}
    (ops : List Op) (h : ∀ i ∈ P.probedCellsFrom m₁ ops, m₂ i = m₁ i) :
    (P.runFrom m₂ ops).1 = (P.runFrom m₁ ops).1 ∧
      P.probesFrom m₂ ops = P.probesFrom m₁ ops ∧
      P.probedCellsFrom m₂ ops = P.probedCellsFrom m₁ ops ∧
      (∀ i ∈ P.probedCellsFrom m₁ ops, (P.runFrom m₂ ops).2 i = (P.runFrom m₁ ops).2 i) :=
  P.toIndexed.runInterval_eq_of_eq_on_probedCellsInterval 0 ops h

@[simp]
theorem runSeq_padCells (h : cells ≤ cells') (P : Scheme Op Result cells w) (ops : List Op) :
    (P.padCells h).runSeq ops = ((P.runSeq ops).1, padMem h (P.runSeq ops).2) :=
  P.toIndexed.runSeq_padCells h ops

@[simp]
theorem seqProbes_padCells (h : cells ≤ cells') (P : Scheme Op Result cells w) (ops : List Op) :
    (P.padCells h).seqProbes ops = P.seqProbes ops :=
  P.toIndexed.seqProbes_padCells h ops

end Scheme

end Cslib.CellProbe

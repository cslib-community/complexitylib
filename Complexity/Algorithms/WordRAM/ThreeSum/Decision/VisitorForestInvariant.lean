/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorLoop
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingEntries

/-!
# Live frontend forest state for the in-place Chan–He visitor

The outer proof state records completed root descriptors and the nodes already consumed.
Every untouched frontend array remains live. Allocation credit reserves a separate complete
recursion budget for each remaining root; no published packed-pointer table is retained.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)
open ChanHe.Traversal

/-- Restrict one root to its allocation allowance without moving any physical region. -/
@[expose] def rootArena {r : ℕ} (a : Arena) (x : Data (registerCount r)) : Arena :=
  { a with ceiling := x.regs (preprocessingRegisters r heap) +
    Math.work a.fuel * allocationSize a.n a.m a.N }

/-- A smaller root allocation allowance retains the admitted native kernel envelope. -/
theorem rootArena_ready {r w : ℕ} {a : Arena} {x : Data (registerCount r)}
    (hw : a.Ready w) (hh : (rootArena a x).ceiling ≤ a.ceiling) :
    (rootArena a x).Ready w := by
  refine ⟨hw.1, hw.2.1, ?_⟩
  apply GenericRAM.Signed.Fits.of_natAbs_le hw.2.2
  simp only [Int.natAbs_natCast]
  dsimp only [envelope, rootArena] at *
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)

/-- The caller's same value and address envelope covers every restricted root. -/
theorem rootArena_resources {r κ n : ℕ} {a : Arena} {x : Data (registerCount r)}
    (hh : (rootArena a x).ceiling ≤ a.ceiling)
    (h : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ) :
    (rootArena a x).ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * (rootArena a x).N < (n + 2) ^ envelopeExponent κ ∧
      60 * (rootArena a x).U + 40 ≤ (n + 2) ^ envelopeExponent κ :=
  ⟨hh.trans h.1, h.2⟩

/-- Proof state of the actual descriptor loop. -/
structure ForestCursor where
  /-- Number of actual root descriptors already consumed. -/
  index : ℕ
  /-- Exact ordered mathematical nodes already supplied to the native solver. -/
  nodes : List Node

/-- Exact pending mathematical preorder for the untouched frontend descriptors. -/
@[expose] def ForestCursor.remaining (s : ForestCursor) (a : Arena)
    (l : Frontend.Layout) (U : ℕ) (rs : List (ℕ × ℕ)) : List Node :=
  Math.output (Nat.primesLE a.m) a.Λ
    (((ChanHe.Preprocessing.entries l U rs).drop s.index).map Entry.task)

/-- Outer traversal credit plus charges for the actual nodes still awaiting the solver. -/
@[expose] def ForestCursor.credit (s : ForestCursor) (a : Arena)
    (l : Frontend.Layout) (U : ℕ) (rs : List (ℕ × ℕ)) (T : ℕ) : ℕ :=
  (l.count - s.index) * (rootTime a.fuel a.n a.m a.N + 17) +
    (s.remaining a l U rs).length * T

/-- Loading the next descriptor consumes precisely its recursion preorder before later roots. -/
theorem ForestCursor.remaining_step {a : Arena} {l : Frontend.Layout} {U : ℕ}
    {rs : List (ℕ × ℕ)} (s : ForestCursor) (nodes : List Node)
    (hi : s.index < l.count)
    (hf : a.fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel l.n) :
    s.remaining a l U rs =
      (ChanHe.Preprocessing.entry l U a.fuel rs s.index).task.output
        (Nat.primesLE a.m) a.Λ ++
      (ForestCursor.mk (s.index + 1) nodes).remaining a l U rs := by
  have hlen : s.index < (ChanHe.Preprocessing.entries l U rs).length := by
    simpa only [ChanHe.Preprocessing.entries, List.length_map, List.length_range] using hi
  have hdrop : (ChanHe.Preprocessing.entries l U rs).drop s.index =
      ChanHe.Preprocessing.entry l U a.fuel rs s.index ::
        (ChanHe.Preprocessing.entries l U rs).drop (s.index + 1) := by
    rw [List.drop_eq_getElem_cons hlen]
    simp only [ChanHe.Preprocessing.entries, List.getElem_map, List.getElem_range, hf]
  simp only [ForestCursor.remaining, hdrop, List.map_cons, Math.output, List.flatMap_cons]

/-- Exact outer charge for one root, including descriptor loading, increment and loop control. -/
theorem ForestCursor.credit_step {a : Arena} {l : Frontend.Layout} {U : ℕ}
    {rs : List (ℕ × ℕ)} (s : ForestCursor) (nodes : List Node) (T : ℕ)
    (hi : s.index < l.count)
    (hf : a.fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel l.n) :
    s.credit a l U rs T = rootTime a.fuel a.n a.m a.N + 17 +
      ((ChanHe.Preprocessing.entry l U a.fuel rs s.index).task.output
        (Nat.primesLE a.m) a.Λ).length * T +
      (ForestCursor.mk (s.index + 1) nodes).credit a l U rs T := by
  have hr : l.count - s.index = (l.count - (s.index + 1)) + 1 := by omega
  simp only [ForestCursor.credit, s.remaining_step nodes hi hf, List.length_append,
    hr, Nat.add_mul, Nat.one_mul]
  ring

/-- Actual descriptors, live memory and Boolean fold at the native outer loop header. -/
structure ForestCursor.Invariant {r : ℕ} (a : Arena) (w κ n : ℕ)
    (l : Frontend.Layout) (U : ℕ) (rs : List (ℕ × ℕ))
    (s : ForestCursor) (x : Data (registerCount r)) : Prop where
  /-- Every native word remains bounded, including used callee scratch. -/
  bounded : x.Bounded (w + 2)
  /-- Persistent traversal parameters survive every root. -/
  controls : a.Controls (x.comap (preprocessingRegisters r))
  /-- Actual frontend descriptors and compact arrays remain available. -/
  frontend : Frontend.Output l U rs x.mem
  /-- Actual native descriptor base. -/
  descriptors : x.regs (preprocessingRegisters r ChanHe.Preprocessing.descriptors) = l.descriptors
  /-- Actual native root count. -/
  roots : x.regs (preprocessingRegisters r ChanHe.Preprocessing.roots) = l.count
  /-- Actual next descriptor index. -/
  current : x.regs (preprocessingRegisters r ChanHe.Preprocessing.current) = s.index
  /-- Native shared recursion fuel. -/
  levels : x.regs (preprocessingRegisters r ChanHe.Preprocessing.levels) = a.fuel
  /-- Native descriptor stride. -/
  stride : x.regs (preprocessingRegisters r ChanHe.Preprocessing.stride) = 6
  /-- Native outer-loop increment constant. -/
  increment : x.regs (preprocessingRegisters r ChanHe.Preprocessing.one) = 1
  /-- All roots up to this index have been executed. -/
  index_le : s.index ≤ l.count
  /-- Actual prime bitmap remains live. -/
  bitmap : a.Bitmap x.mem
  /-- Heap remains above shared reservations. -/
  floor : a.floor ≤ x.regs (preprocessingRegisters r heap)
  /-- Every remaining root retains its own complete allocation allowance. -/
  heapBudget : x.regs (preprocessingRegisters r heap) + (l.count - s.index) *
    (Math.work a.fuel * allocationSize a.n a.m a.N) ≤ a.ceiling
  /-- Actual common packed length. -/
  packedLength : x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) = 4 * a.N
  /-- Computed caller value envelope. -/
  envelopeValue : x.regs (controllerRegisters r Decision.envelope) =
    (n + 2) ^ envelopeExponent κ
  /-- Native Boolean constant one. -/
  unit : x.regs (controllerRegisters r Decision.one) = 1
  /-- Accumulated result is a raw Boolean. -/
  boolean : x.regs (controllerRegisters r answer) ≤ 1
  /-- Every consumed node contributes exactly its Convolution verdict. -/
  verdict : x.regs (controllerRegisters r answer) = 1 ↔
    ∃ node ∈ s.nodes, Cslib.Algorithms.ThreeSum.Convolution (4 * a.N) (node.oneArray a.U)
  /-- Consumed prefix and untouched roots retain the entire finite forest preorder. -/
  exactOutput : s.nodes ++ s.remaining a l U rs = Math.output (Nat.primesLE a.m) a.Λ
    ((ChanHe.Preprocessing.entries l U rs).map Entry.task)
  /-- Original frontend/source cells survive for every later root. -/
  protectedMemory : ∀ p < a.stack, x.mem p = a.retained p

/-- A live outer header can afford the one complete root it is about to execute. -/
theorem ForestCursor.Invariant.root_budget {r w κ n U : ℕ} {a : Arena}
    {l : Frontend.Layout} {rs : List (ℕ × ℕ)} {s : ForestCursor}
    {x : Data (registerCount r)} (h : s.Invariant a w κ n l U rs x)
    (hc : (Cond.lt (preprocessingRegisters r ChanHe.Preprocessing.current)
      (preprocessingRegisters r ChanHe.Preprocessing.roots)).Holds x) :
    (rootArena a x).ceiling ≤ a.ceiling := by
  have hi : s.index < l.count := by
    simpa only [Cond.holds_lt, h.current, h.roots] using hc
  have hm : 1 ≤ l.count - s.index := by omega
  have hp := Nat.mul_le_mul_left (Math.work a.fuel * allocationSize a.n a.m a.N) hm
  rw [Nat.mul_one, Nat.mul_comm _ (l.count - s.index)] at hp
  have hb := h.heapBudget
  change x.regs (preprocessingRegisters r heap) + Math.work a.fuel *
    allocationSize a.n a.m a.N ≤ a.ceiling
  omega

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

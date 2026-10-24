/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Query.Program
public import Complexity.Algorithms.WordRAM.FusionTree.Preprocessing
public import Complexity.Algorithms.Lean.FusionTree.Routing

/-!
# Actual preprocessed-node calls from traversal

The large-width routine receives the parameters actually stored by `parameterWords`.
The small-width routine receives exactly two children, as forced by the branching rule.
Neither branch assumes a node oracle. Both frame the caller's persistent registers.

## Main results

* `QueryProgram.exec_node`: inclusive full-key rank, in at most 201000 instructions.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.QueryProgram

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree

/-- A node call may alter scratch registers but frames all persistent traversal data. -/
theorem Entry.frame {q p : ℕ} {x y : Data registers} (hx : Entry q p x)
    (hq : y.regs query = q) (hp : y.regs pointer = p)
    (hf : ∀ i : Fin registers, 31 ≤ i.val → i.val < 39 → y.regs i = x.regs i) :
    Entry q p y :=
  ⟨hq, hp, (hf active (by decide) (by decide)).trans hx.active_eq,
    (hf found (by decide) (by decide)).trans hx.found_eq,
    (hf value (by decide) (by decide)).trans hx.value_eq,
    (hf one (by decide) (by decide)).trans hx.one_eq,
    (hf zero (by decide) (by decide)).trans hx.zero_eq⟩

/-- Whole-tree representation projects to the exact chosen fusion-node witness. -/
private theorem node_rep {w m p : ℕ} {cs : List Tree} {mem : ℕ → ℕ}
    (he : ParameterEligible w cs) (hr : Rep (parameterWords w) (.node m cs) p mem) :
    NodeProgram.Rep
      (NodeParameters.choose he.2.1 he.2.2.2.1 he.2.2.2.2 he.2.2.1 he.1) p mem := by
  refine ⟨hr.node_header.2.1, ?_, ?_⟩
  · intro j
    rw [hr.node_header.2.2.2 j, parameterWords_node he]
  · intro i
    simpa only [headerWords, Nat.mul_comm, childMinima] using (hr.child i).1

/-- Both actual node implementations return full-key inclusive rank. All preprocessing
is derived from the real tree, with constant words and the entire arena fitting explicitly.
The instruction bound includes the whole selected node call, with no assumed oracle. -/
theorem exec_node {w q p m : ℕ} {cs : List Tree} {x : Data registers}
    (hx : Entry q p x) (ht : Lean.FusionTree.Tree.Valid (branching w) (.node m cs))
    (hs : (Lean.FusionTree.Tree.node m cs).keys.Pairwise (· < ·))
    (hk : ∀ k ∈ (Lean.FusionTree.Tree.node m cs).keys, Fits w k)
    (hr : Rep (parameterWords w) (.node m cs) p x.mem)
    (ha : ArenaFits w p (.node m cs)) (hq : Fits w q) :
    ∃ y, ExecWithin w (node w) x y 201000 ∧
      y.regs rank = upperRank (childMinima cs) q ∧
      y.mem = x.mem ∧ Entry q p y := by
  have hv := ht
  simp only [Lean.FusionTree.Tree.Valid] at hv
  by_cases hw : 9 ≤ Nat.log 2 w
  · have he := parameterEligible_of_valid hw ht hs hk
    let params := NodeParameters.choose he.2.1 he.2.2.2.1 he.2.2.2.2 he.2.2.1 he.1
    have haddr : Fits w (p + 18 + (cs.length - 1) * 2) :=
      ha.of_le (by simp only [span, headerWords]; omega)
    obtain ⟨y, hey, hy, hym, hyq, hyp⟩ := NodeProgram.exec params hv.1
      (childMinima_strictMono ht hs) (childMinima_fit ht hk) hv.2.1 hw x
      (node_rep he hr) hq haddr hx.query_eq hx.pointer_eq
    refine ⟨y, by simpa only [node, ite_eq_left hw] using hey, hy, hym,
      hx.frame hyq hyp ?_⟩
    obtain ⟨t, _, hexy⟩ := hey
    exact fun i hlo hhi => NodeProgram.caller_regs_eq hexy i hlo hhi
  · have hB : branching w = 2 := by simp [branching, hw]
    have hlen : cs.length = 2 := by omega
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    have haddr : Fits w (x.regs pointer + 20) := by
      rw [hx.pointer_eq]
      exact ha.of_le (by simp only [span, headerWords, List.length_cons, List.length_nil]; omega)
    obtain ⟨hexy, hym, hy⟩ := BinaryNodeProgram.exec x haddr
    let y := BinaryNodeProgram.result x
    have hfirst : x.mem (p + 18) = a.minimum := by
      simpa [headerWords] using (hr.child (0 : Fin 2)).1
    have hsecond : x.mem (p + 20) = b.minimum := by
      simpa [headerWords] using (hr.child (1 : Fin 2)).1
    have hsorted := childMinima_strictMono ht hs
    have hab : a.minimum < b.minimum := hsorted (show (0 : Fin 2) < 1 by decide)
    have hkeys : childMinima [a, b] = ![a.minimum, b.minimum] := by
      funext i
      fin_cases i <;> rfl
    refine ⟨y, by simpa only [node, ite_eq_right hw] using hexy.mono (by decide), ?_, hym, ?_⟩
    · rw [hy, hx.query_eq, hx.pointer_eq, hfirst, hsecond, BinaryNodeProgram.rank_eq hab, hkeys]
    · rcases hx with ⟨hxq, hxp, hxa, hxf, hxv, hxo, hxz⟩
      constructor <;>
        simp +decide [y, BinaryNodeProgram.result, BinaryNodeProgram.two,
          BinaryNodeProgram.offset, BinaryNodeProgram.address, BinaryNodeProgram.first,
          BinaryNodeProgram.second, BinaryNodeProgram.out, hxq, hxp, hxa, hxf, hxv, hxo, hxz]

end Cslib.Algorithms.WordRAM.FusionTree.QueryProgram

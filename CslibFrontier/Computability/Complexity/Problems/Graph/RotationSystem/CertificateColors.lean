/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCycles
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexParityWords
public import CslibFrontier.Foundations.GroupTheory.Perm.ListColorPath
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Dart colors on the actual bounded certificate words

The finite dart-index equivalence reads mathematical colors at raw table positions.
On an accepted table, its literal cycle word computes vertex parity and cutting it after
the marked dart gives the exact entry/exit color path, including the empty-tail case.
-/

public section

namespace Cslib.Complexity.Graph

namespace Dart

/-- Extend colors to raw dart indices by the existing finite index equivalence. Values
outside the actual dart interval are false; no numeric label determines an iteration bound. -/
@[expose] def colorAtIndex {G : Graph} (P : Dart G → Bool) (i : ℕ) : Bool :=
  (List.ofFn fun j => P ((indexEquiv G).symm j)).getD i false

/-- Actual indexed darts read exactly their original mathematical color. -/
theorem colorAtIndex_index {G : Graph} (P : Dart G → Bool) (d : Dart G) :
    colorAtIndex P d.index = P d := by
  exact (List.getD_ofFn (fun j => P ((indexEquiv G).symm j)) (indexEquiv G d) false).trans
    (congrArg P ((indexEquiv G).symm_apply_apply d))

end Dart

namespace RotationCertificate

/-- The actual bounded raw cycle word computes the selected vertex's incidence parity. -/
theorem vertexParity_eq_sum_cycleWord {G : Graph} {c : RotationCertificate}
    (hc : verifyRotation G c = true) (x : Fin G.edges.length → Bool) (d : Dart G) :
    G.vertexParity x d.vertex =
      ((cycleWord c d.index).map (Dart.colorAtIndex fun e => x e.1)).sum := by
  let r := decode G c hc
  let word := (List.range (Function.minimalPeriod r.rotate d)).map fun k => r.rotate^[k] d
  have hw : word.map Dart.index = cycleWord c d.index := by
    simp only [word, r, List.map_map, Function.comp_def, cycleWord_eq_map_range hc]
  have hn : word.Nodup := (hw ▸ nodup_cycleWord hc d).of_map
  have hf (e : Dart G) : e ∈ word ↔ e.vertex = d.vertex := by
    constructor
    · intro he
      apply (mem_cycleWord_iff hc d e).mp
      rw [← hw]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    · intro he
      have hm := (mem_cycleWord_iff hc d e).mpr he
      rw [← hw] at hm
      obtain ⟨f, hf, he⟩ := List.mem_map.mp hm
      have hfe : f = e := (Dart.indexEquiv G).injective (Fin.ext he)
      exact hfe ▸ hf
  have hmap : ((cycleWord c d.index).map (Dart.colorAtIndex fun e => x e.1)) =
      word.map (fun e => x e.1) := by
    rw [← hw]
    rw [List.map_map]
    exact List.map_congr_left fun e _ => Dart.colorAtIndex_index (fun e => x e.1) e
  exact (G.vertexParity_eq_sum_word x d.vertex word hn hf).trans
    (congrArg List.sum hmap).symm

/-- Clockwise corner colors satisfy the actual listed cycle's forward equations. -/
theorem formPerm_cycleWord_colors {G : Graph} {c : RotationCertificate}
    (hc : verifyRotation G c = true) (d : Dart G) (P : Dart G → Bool)
    (hP : ∀ e, P ((decode G c hc).rotate e) = P e.reverse)
    (i : ℕ) (hi : i ∈ cycleWord c d.index) :
    Dart.colorAtIndex P ((cycleWord c d.index).formPerm i) =
      Dart.colorAtIndex (fun e => P e.reverse) i := by
  obtain ⟨e, he, hv⟩ := (mem_cycleWord_iff_exists_dart hc d i).mp hi
  rw [← he, formPerm_cycleWord_apply hc d e hv, ← index_decode_rotate hc,
    Dart.colorAtIndex_index, Dart.colorAtIndex_index]
  exact hP e

/-- The complete literal cycle is a closed corner-color path, anchored at its actual
first dart. Singleton cycles are included. -/
theorem isChain_colors_cycleWord {G : Graph} {c : RotationCertificate}
    (hc : verifyRotation G c = true) (d : Dart G) (P : Dart G → Bool)
    (hP : ∀ e, P ((decode G c hc).rotate e) = P e.reverse) :
    List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
      ((P d, P d) :: (cycleWord c d.index).map
        (fun i => (Dart.colorAtIndex P i, Dart.colorAtIndex (fun e => P e.reverse) i)) ++
        [(P d, P d)]) := by
  have h := List.isChain_colorPairs_cycle_formPerm d.index (cycleWord c d.index).tail
    (nodup_cycleWord hc d) (Dart.colorAtIndex P)
    (Dart.colorAtIndex fun e => P e.reverse) (formPerm_cycleWord_colors hc d P hP)
  simpa only [cycleWord, List.tail_cons, Dart.colorAtIndex_index] using h

/-- Cut the literal computed cycle at its marker. Clockwise-compatible colors give a
path from the reverse marker color to the marker color through precisely the stored tail. -/
theorem isChain_colors_tail_cycleWord {G : Graph} {c : RotationCertificate}
    (hc : verifyRotation G c = true) (d : Dart G) (P : Dart G → Bool)
    (hP : ∀ e, P ((decode G c hc).rotate e) = P e.reverse) :
    List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
      ((P d.reverse, P d.reverse) ::
        (cycleWord c d.index).tail.map
          (fun i => (Dart.colorAtIndex P i, Dart.colorAtIndex (fun e => P e.reverse) i)) ++
        [(P d, P d)]) := by
  have h := List.isChain_colorPairs_cut_formPerm d.index (cycleWord c d.index).tail
    (nodup_cycleWord hc d) (Dart.colorAtIndex P)
    (Dart.colorAtIndex fun e => P e.reverse) (formPerm_cycleWord_colors hc d P hP)
  simpa only [Dart.colorAtIndex_index] using h

end RotationCertificate
end Cslib.Complexity.Graph

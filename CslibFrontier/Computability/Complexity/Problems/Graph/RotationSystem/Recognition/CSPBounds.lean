/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Moves
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Split
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Tactic.Linarith

/-!
# Original-input bounds for sparse rotation queries

All bounds use the existing framed CSP encoding, including relation records, binary variable
names and actual ordered scope lists. Nullary points are funded by constraint framing. No bound
on a source label's numerical value, or on declared relation arity, is used.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM Cslib.Logic.PL

/-- Actual scope occurrences plus constraint positions are bounded by the full CSP bit length. -/
theorem scopes_add_constraints_le {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool)
    (F : CSP Rel V) :
    (F.map fun c => c.2.length).sum + F.length ≤ (encCSP encRel encV F).length := by
  induction F with
  | nil => simp [encCSP]
  | cons c F ih =>
    have hs := length_le_length_encList encV c.2
    have he : (encCSP encRel encV (c :: F)).length =
        2 * (encConstraint encRel encV c).length + 1 + (encCSP encRel encV F).length := by
      simp only [encCSP, length_encList, List.map_cons, List.sum_cons]
    rw [he]
    simp only [encConstraint, length_encPair, List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Dense incidence vertices and listed occurrences are each bounded by original encoded size. -/
theorem incidence_sizes_le {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (F : CSP Rel V) :
    (CSP.incidenceGraph F).1.length ≤ (encCSP encRel encV F).length ∧
      (CSP.incidenceGraph F).2.length ≤ (encCSP encRel encV F).length := by
  have hb := scopes_add_constraints_le encRel encV F
  have hn : F.numVars ≤ F.vars.length := List.toFinset_card_le _
  have hv : F.vars.length = (F.map fun c => c.2.length).sum := by
    simp only [CSP.vars, List.length_flatMap]
  rw [hv] at hn
  rw [CSP.length_vertices_incidenceGraph, CSP.length_edges_incidenceGraph]
  omega

/-- Any one-hub split of an original bounded graph has at most `3(B+1)` subdivided vertices
and segments. The statement is all-raw and does not require a feasibility premise. -/
theorem frame_sizes_split_le {I : FixedRotationInput} {B : ℕ}
    (hn : I.graph.1.length ≤ B) (hm : I.graph.2.length ≤ B) (v : ℕ) (block : List ℕ) :
    (frame (split I v block)).vertexCount ≤ 3 * (B + 1) ∧
      (frame (split I v block)).segments.length ≤ 3 * (B + 1) := by
  simp only [frame, subdivisionSize, length_split_vertices, length_split_edges, length_subdivide]
  omega

/-- Explicit full framed-system bit bound for every valid query with the uniform segment and
vertex budgets. It includes equation pairs, binary labels, right-hand sides and outer framing. -/
theorem length_encoding_compile_le_of_sizes {I : FixedRotationInput} (hI : Valid I) {K : ℕ}
    (hn : (frame I).vertexCount ≤ 3 * K) (hm : (frame I).segments.length ≤ 3 * K) :
    (XORSAT.encoding (compile I)).length ≤
      9 * K ^ 2 * (32 * (Nat.log2 (9 * K ^ 2) + 1) + 21) := by
  have hF := boundedEndpoints_frame hI
  have hlabels : ∀ r ∈ compileFrame (frame I), ∀ d ∈ r.1,
      (encNat d).length ≤ Nat.log2 (9 * K ^ 2) + 1 := by
    intro r hr d hd
    obtain ⟨e, he, f, hf, _, _, rfl⟩ := mem_compileFrame.mp hr
    have hlt := label_lt_row hF he hf hd
    have hrectangle : (frame I).segments.length * (frame I).vertexCount ≤ 9 * K ^ 2 := by
      nlinarith [Nat.mul_le_mul hm hn]
    exact length_encNat_le_log2 (hlt.le.trans hrectangle)
  have hrows : (compileFrame (frame I)).length ≤ 9 * K ^ 2 :=
    (length_compileFrame_le _).trans (by nlinarith [Nat.pow_le_pow_left hm 2])
  have hbits : ∀ r ∈ compileFrame (frame I),
      (XORSAT.equationEncoding r).length ≤ 16 * (Nat.log2 (9 * K ^ 2) + 1) + 10 := by
    intro r hr
    have hh := framed_row_length_le (width_compileFrame hr) (hlabels r hr)
    omega
  have hb := length_encList_le XORSAT.equationEncoding (compileFrame (frame I)) hbits
  change (encList XORSAT.equationEncoding (compileFrame (frame I))).length ≤ _
  exact hb.trans (by nlinarith)

/-- A valid original CSP split query has the full memo bit bound with `K=B+1`. -/
theorem length_encoding_compile_split_ofCSP_le {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (F : CSP Rel V) (v : ℕ) (block : List ℕ)
    (h : Valid (split (ofCSP F) v block)) :
    (XORSAT.encoding (compile (split (ofCSP F) v block))).length ≤
      9 * ((encCSP encRel encV F).length + 1) ^ 2 *
        (32 * (Nat.log2 (9 * ((encCSP encRel encV F).length + 1) ^ 2) + 1) + 21) := by
  obtain ⟨hn, hm⟩ := incidence_sizes_le encRel encV F
  have hs := frame_sizes_split_le (I := ofCSP F) hn hm v block
  exact length_encoding_compile_le_of_sizes h hs.1 hs.2

/-- The temporary original-CSP frame, including reference order and frozen flags, has quadratic
full framed storage in the original binary input length. -/
theorem length_encFrame_split_ofCSP_le {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (F : CSP Rel V) (v : ℕ) (block : List ℕ)
    (h : Valid (split (ofCSP F) v block)) :
    (encFrame (frame (split (ofCSP F) v block))).length ≤
      400 * ((encCSP encRel encV F).length + 1) ^ 2 := by
  obtain ⟨hn, hm⟩ := incidence_sizes_le encRel encV F
  apply length_encFrame_le h (by omega)
  · rw [length_split_vertices]
    exact Nat.add_le_add_right hn 1
  · rw [length_split_edges]
    exact Nat.add_le_add_right hm 1

/-- Full framed XOR storage of the initial bare original-CSP query. -/
theorem length_encoding_compile_ofCSP_le {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (F : CSP Rel V) :
    (XORSAT.encoding (compile (ofCSP F))).length ≤
      9 * ((encCSP encRel encV F).length + 1) ^ 2 *
        (32 * (Nat.log2 (9 * ((encCSP encRel encV F).length + 1) ^ 2) + 1) + 21) := by
  obtain ⟨hn, hm⟩ := incidence_sizes_le encRel encV F
  apply length_encoding_compile_le_of_sizes (valid_ofCSP F)
  · change (CSP.incidenceGraph F).1.length + 2 * (CSP.incidenceGraph F).2.length ≤ _
    omega
  · simp only [frame, length_subdivide]
    change 3 * (CSP.incidenceGraph F).2.length ≤ _
    omega

end Cslib.Complexity.Graph.RotationRecognition

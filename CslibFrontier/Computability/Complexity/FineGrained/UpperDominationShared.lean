/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.UpperDominationSharedBounds
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Native shared-marker upper-domination counting

Instantiate the actual ordinary width-three counter in the refined queries of
[ChenJiangZhu2027], Appendix D.3 (PDF p.35). Both query storage, both binary answers and subtraction
are charged. The whole execution has polynomial workspace; closing its sharp-time estimate is
still a separate obligation.

## Main results

* `exists_count_polySpace`: actual original-set counter with global polynomial workspace.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers

open Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits.Frontier.IncidenceNetwork

private theorem valid_query {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool) :
    CNF.validDeclaredInput 3 (oldDeclaration (ofGraph G k) + n) (query (ofGraph G k) β) := by
  apply CNF.validDeclaredInput_eq_true_iff.mpr
  refine ⟨query_width _ _, ?_⟩
  intro v hv
  obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
  exact Finset.mem_range.mpr (query_indices G k hn β c hc (v, b) hl)

open Classical in
/-- One genuine width-three native counter counts original minimal dominating sets with the
varying signed threshold and polynomial workspace on every raw input. No counter, answer or
resource conclusion is supplied as advice. The closed sharp-time estimate is not asserted here. -/
theorem exists_count_polySpace :
    ∃ count : Input → ℕ, ComputableInPolySpace count encInput encNat ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (ofGraph G k) =
          Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} := by
  obtain ⟨β, N₀, Ncut, cs, D, hresource, hspec⟩ :=
    exists_countGeneralParity_sharp_certificate 3 (by decide)
  let counter := countGeneralParity 3 β N₀ Ncut
  have hs : PolyBounded (fun x => (TwoBoundary.BinaryFrontend.encCounter x).length) cs.space :=
    PolyBounded.of_forall_le D D fun x => (hresource x).2
  have hcounter := ComputableInPolySpace.of_inSpace hs (ComputableInSpace.of_inO cs.computes)
  obtain ⟨hf, ht⟩ := TwoBoundary.BinaryFrontend.selectors_polytime
  have hfirst := hcounter.comp (.of_polyTime hf)
  have hsecond := hcounter.comp (.of_polyTime ht)
  have htag := (ComputableInO.isLeft_deg
    (encPair encUnary VCOne.encSignedCNF)
    (encPair encUnary (encPair VCOne.encSignedCNF VCOne.encSignedCNF))).computableInPolyTime
  have hexec : ComputableInPolySpace (TwoBoundary.BinaryFrontend.execute counter)
      TwoBoundary.BinaryFrontend.encOutput encNat :=
    (ComputableInPolySpace.of_polyTime htag).ite hfirst
      ((ComputableInPolySpace.of_polyTime ComputableInPolyTime.binary_sub).comp
        (hfirst.prod hsecond))
  refine ⟨fun x => TwoBoundary.BinaryFrontend.execute counter (compile x),
    hexec.comp (.of_polyTime compile_polytime), ?_⟩
  intro n G _ k
  change TwoBoundary.BinaryFrontend.execute counter (compile (ofGraph G k)) = _
  rw [← compile_count G k]
  by_cases hn : n = 0
  · obtain ⟨B, P, he, hb, hp, hl, _⟩ := Unique.representation G k
    have hem : P = [] := List.length_eq_zero_iff.mp (by omega)
    subst P
    have hnraw : IndependentDomination.order (graph (ofGraph G k)) = 0 := hn
    rw [compile, ite_eq_left hnraw, he]
    exact TwoBoundary.BinaryFrontend.execute_correct (b := 3) (d := 0) hspec B [] hb (by simp)
  · have hn' : 1 ≤ n := by omega
    have hnraw : IndependentDomination.order (graph (ofGraph G k)) ≠ 0 := hn
    simp only [compile, hnraw, ↓reduceIte, TwoBoundary.BinaryFrontend.execute,
      Sum.isLeft_inr, Bool.false_eq_true, TwoBoundary.BinaryFrontend.first,
      TwoBoundary.BinaryFrontend.second, TwoBoundary.BinaryFrontend.value]
    dsimp only [counter]
    have hnval : IndependentDomination.order (graph (ofGraph G k)) = n := rfl
    rw [hspec, hspec]
    simp only [hnval, valid_query G k hn' false, valid_query G k hn' true, ↓reduceIte,
      WeightedRow.BinaryPlan.queryCount_eq_modelCountOn]

end Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers

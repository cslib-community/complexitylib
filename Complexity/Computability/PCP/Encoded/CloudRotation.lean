/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Cloud
public import Complexity.Foundations.Combinatorics.Expander.Reindex
import Mathlib.Data.List.GetD

/-!
# Executable rotation within a vertex cloud

Cloud rotation enumerates the incident half-edges, finds the current one, calls a uniformly
certified numerical rotation algorithm, and reads the resulting half-edge. It retains the
return edge label. The correctness theorem identifies it with the existing mathematical
cloud graph whenever the supplied rotation algorithm realizes its family on `Fin n`.

## Main definitions

* `Cslib.PCP.Encoded.Graph.cloudRotation`: the executable cloud rotation.
* `Cslib.PCP.Encoded.Graph.cloudFamily`: the mathematical family transported to the clouds.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_cloudRotation`: a uniform certificate charging the full
  graph, enumeration, search, rotation, and result lookup.
* `Cslib.PCP.Encoded.Graph.cloudRotation_eq`: exact agreement with the transported rotation,
  including its return label.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM

variable {C α D Input : Type} {input : Input ↪ List Bool}
  {enc : C ↪ List Bool} {labelEncoding : D ↪ List Bool}

/-- Rotate within the current endpoint's cloud using its ordered half-edge enumeration.
An out-of-range answer retains the input half-edge. -/
def cloudRotation (fallback : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (g : Graph C) (p : (ℕ × Bool) × D) : (ℕ × Bool) × D :=
  let members := g.cloud fallback (g.endpoint fallback p.1)
  let next := rotate (members.length, members.idxOf p.1, p.2)
  (members[next.1]?.getD p.1, next.2)

/-- The polynomial-time hypothesis on the numerical rotation is joint in the cloud size,
vertex and label. A separate machine for each size is insufficient. -/
@[fun_prop]
theorem isPolyTime_cloudRotation {graph : Input → Graph C}
    {halfEdge : Input → (ℕ × Bool) × D} {rotate : ℕ × (ℕ × D) → ℕ × D}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hhalfEdge : ComputableInPolyTime halfEdge input
      (encPair (encPair encUnary encBool) labelEncoding))
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (fallback : C) :
    ComputableInPolyTime
      (fun x => (graph x).cloudRotation fallback rotate (halfEdge x))
      input (encPair (encPair encUnary encBool) labelEncoding) := by
  have hhalf := hhalfEdge.fst'
  have hvertex := isPolyTime_endpoint hgraph hhalf fallback
  have hmembers := isPolyTime_cloud hgraph hvertex fallback
  have hlength := (ComputableInPolyTime.length_list (encPair encUnary encBool)).comp hmembers
  have hindex := (ComputableInPolyTime.idxOf (encPair encUnary encBool)).comp
    (hmembers.prod hhalf)
  have hnext := hrotate.comp (hlength.prod (hindex.prod hhalfEdge.snd'))
  have hdrop := (ComputableInPolyTime.dropUnary (encA := encPair encUnary encBool)).comp
    (hmembers.prod hnext.fst')
  have hget := (ComputableInPolyTime.head? (encPair encUnary encBool)).comp hdrop
  have hresult := (ComputableInPolyTime.optionGetD (encPair encUnary encBool)).comp
    (hget.prod hhalf)
  simpa only [cloudRotation, Function.comp_def, List.head?_drop] using hresult.prod hnext.snd'

/-- Transport a numbered graph family to the explicitly enumerated mathematical clouds. -/
def cloudFamily (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
    (family : (n : ℕ) → RotationMap (Fin n) D) (vertex : ℕ) :
    RotationMap ((g.toGraph eval).Cloud vertex) D :=
  (family (g.cloud fallback vertex).length).reindex (g.cloudEquiv eval fallback vertex)

/-- Exact agreement of the numerical program with the transported rotation on a cloud.
The equality includes the return edge label, not only the neighboring half-edge. -/
theorem cloudRotation_eq (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
    (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (vertex : ℕ) (p : (g.toGraph eval).Cloud vertex) (d : D) :
    g.cloudRotation fallback rotate ((p.val.1.val, p.val.2), d) =
      let next := (g.cloudFamily eval fallback family vertex).rot (p, d)
      ((next.1.val.1.val, next.1.val.2), next.2) := by
  unfold cloudRotation
  rw [g.endpoint_eq eval fallback, p.property]
  dsimp only
  rw [← g.cloudEquiv_symm_apply eval fallback vertex p, hrotate]
  simp only [cloudFamily, RotationMap.rot_reindex]
  rw [← List.getD_eq_getElem?_getD, List.getD_eq_get]
  rfl

end Cslib.PCP.Encoded.Graph

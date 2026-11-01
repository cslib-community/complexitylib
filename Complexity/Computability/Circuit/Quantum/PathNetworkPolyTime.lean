/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.PathNetwork
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ExplicitTablesPolyTime
public import Complexity.Computability.Circuit.Quantum.Uniform
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DirectContraction
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Complexity.Foundations.Data.List.FilterMap
import Complexity.Tactic.OptionMatch

/-!
# The network of a circuit in polynomial time

The network of a list of gate codes (`Cslib.Quantum.PathNetwork.network`) is computable in
polynomial time from the gate codes, the measured qubits, the input register and the Hadamard sign,
with its number of rows in binary and the network in the encoding of the contraction algorithm
(`ExplicitTensorNetwork.encExplicitNetwork`). Every port and last occurrence is a search or a map
over the occurrences of qubits, written in unary, and every table is a map over the first `2 ^ 6`
numbers, a constant list.

## Main results

* `Cslib.Quantum.PathNetwork.computableInPolyTime_network`: the network is polynomial-time.
-/

public section

namespace Cslib.Quantum.PathNetwork

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Circuits.Frontier ExplicitTensorNetwork

variable {α : Type} {inp : α ↪ List Bool}

/-! ### Reformulations for the polynomial-time combinators -/

/-- The qubits of a gate code, read by projections, as the pair combinators compute them. -/
private theorem qubits_eq_proj : qubits = fun g : GateCode => g.2.1 :: g.2.2 :=
  funext fun ⟨_, _, _⟩ => rfl

private theorem gatePorts_eq (gs : List GateCode) (c i : ℕ) :
    gatePorts gs c i =
      (List.range (qubits (gs.getD i default)).length).map
          (fun k => 2 * (c * (occurrences gs).length + base gs i + k)) ++
        ((qubits (gs.getD i default)).filter
            fun j => (lastOcc (occurrences gs) j (base gs i)).isSome).map
          fun j => 2 * (c * (occurrences gs).length +
            (lastOcc (occurrences gs) j (base gs i)).getD 0) + 1 := by
  rw [gatePorts, List.filterMap_eq_map_filter _ _ 0]
  congr 1
  simp only [inPort, Option.isSome_map]
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (List.mem_filter.mp hj).2
  rw [hw]
  rfl

private theorem scalarVertex_eq (S : List ℕ) (X : List Bool) (gs : List GateCode) :
    (scalarVertex S X gs : List ℕ × List ℕ) =
      ([], [if (S.all fun j => decide (j ∈ occurrences gs) || X.getD j false) then 1
        else 0]) := by
  simp only [scalarVertex, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]

/-- The encoding of networks is the encoding of their number of edges and vertices. -/
private theorem computableInPolyTime_equivProd_symm :
    ComputableInPolyTime (DescribedNetwork.equivProd (T := List ℕ)).symm
      (encPair encUnary (encList (encPair (encList encNat) (encList encNat))))
      ExplicitTensorNetwork.encExplicitNetwork :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-! ### Occurrences -/

section Data

variable {gs : α → List GateCode} (hgs : ComputableInPolyTime gs inp (encList encGateCode))
include hgs

theorem computableInPolyTime_qubits_getD {i : α → ℕ} (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => qubits ((gs a).getD (i a) default)) inp
      (encList encUnary) := by
  have hg := listGetDWithInput hgs hi default
  rw [qubits_eq_proj]
  exact cons' ((fst _ _).comp ((snd _ _).comp hg)) ((snd _ _).comp ((snd _ _).comp hg))

theorem computableInPolyTime_occurrences :
    ComputableInPolyTime (fun a => occurrences (gs a)) inp (encList encUnary) := by
  unfold occurrences
  rw [qubits_eq_proj]
  exact flatMapWithInput hgs (cons' ((fst _ _).comp ((snd _ _).comp (snd _ _)))
    ((snd _ _).comp ((snd _ _).comp (snd _ _))))

theorem computableInPolyTime_base {i : α → ℕ} (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => base (gs a) (i a)) inp encUnary :=
  (length_list _).comp (computableInPolyTime_occurrences
    ((ComputableInDegree.takeUnary encGateCode).computableInPolyTime.comp (hgs.prod hi)))

end Data

theorem computableInPolyTime_lastOcc {qs : α → List ℕ} {j p : α → ℕ}
    (hqs : ComputableInPolyTime qs inp (encList encUnary))
    (hj : ComputableInPolyTime j inp encUnary) (hp : ComputableInPolyTime p inp encUnary) :
    ComputableInPolyTime (fun a => lastOcc (qs a) (j a) (p a)) inp (encOption encUnary) := by
  unfold lastOcc
  exact findWithInput (listReverseWithInput (range.comp hp))
    (decide_eq' (listGetDWithInput (hqs.comp (fst _ _)) (snd _ _) 0) (hj.comp (fst _ _)))

/-! ### Vertices -/

section Vertices

variable {gs : α → List GateCode} (hgs : ComputableInPolyTime gs inp (encList encGateCode))
include hgs

/-- The ports of a gate vertex, in unary. -/
theorem computableInPolyTime_gatePorts {c i : α → ℕ} (hc : ComputableInPolyTime c inp encUnary)
    (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => gatePorts (gs a) (c a) (i a)) inp (encList encUnary) := by
  have hq := computableInPolyTime_qubits_getD hgs hi
  have hN := (length_list _).comp (computableInPolyTime_occurrences hgs)
  have hb := computableInPolyTime_base hgs hi
  simp only [gatePorts_eq]
  refine listAppend' (mapWithInput (range.comp ((length_list _).comp hq))
    (unary_mul' (const 2) (unary_add' (unary_add' (unary_mul' (hc.comp (fst _ _))
      (hN.comp (fst _ _))) (hb.comp (fst _ _))) (snd _ _)))) ?_
  have hl : ComputableInPolyTime (fun p : α × ℕ => lastOcc (occurrences (gs p.1)) p.2
      (base (gs p.1) (i p.1))) (encPair inp encUnary) (encOption encUnary) :=
    computableInPolyTime_lastOcc (computableInPolyTime_occurrences (hgs.comp (fst _ _)))
      (snd _ _) (hb.comp (fst _ _))
  exact mapWithInput (filterWithInput hq (optionIsSome hl))
    (unary_add' (unary_mul' (const 2) (unary_add' (unary_mul' (hc.comp (fst _ _))
      (hN.comp (fst _ _))) (optionGetDWithInput hl (const 0)))) (const 1))

/-- **Gate vertices are polynomial-time.** -/
theorem computableInPolyTime_gateVertex {neg : α → ℕ} {X : α → List Bool} {c i : α → ℕ}
    (hneg : ComputableInPolyTime neg inp encNat) (hX : ComputableInPolyTime X inp encBits)
    (hc : ComputableInPolyTime c inp encUnary) (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => gateVertex (neg a) (X a) (gs a) (c a) (i a)) inp
      (encPair (encList encNat) (encList encNat)) := by
  have hps := computableInPolyTime_gatePorts hgs hc hi
  have hq := computableInPolyTime_qubits_getD hgs hi
  have hg := listGetDWithInput hgs hi default
  have hN := (length_list _).comp (computableInPolyTime_occurrences hgs)
  have hb := computableInPolyTime_base hgs hi
  refine (ports_unary_to_binary hps).prod
    (computableInPolyTime_boundedTable 6 ((length_list _).comp hps) fun idx => ?_)
  -- the bits entering the qubits of the gate
  have hins : ComputableInPolyTime (fun a => (qubits ((gs a).getD (i a) default)).map
      (inBit (X a) (gs a) (c a) (i a) idx)) inp (encList encBool) := by
    unfold inBit inPort
    option_match_to_elim
    simp only [Option.elim_map]
    refine mapWithInput hq (optionElimWithInput
      (computableInPolyTime_lastOcc (computableInPolyTime_occurrences (hgs.comp (fst _ _)))
        (snd _ _) (hb.comp (fst _ _)))
      (bitsGetDWithInput (hX.comp (fst _ _)) (snd _ _) false)
      (binary_testBit (const idx) (idxOfWithInput (hps.comp ((fst _ _).comp (fst _ _)))
        (unary_add' (unary_mul' (const 2) (unary_add' (unary_mul'
          (hc.comp ((fst _ _).comp (fst _ _))) (hN.comp ((fst _ _).comp (fst _ _))))
          (snd _ _))) (const 1)))))
  -- the bits leaving them
  have houts : ComputableInPolyTime (fun a => (List.range (qubits ((gs a).getD (i a)
      default)).length).map idx.testBit) inp (encList encBool) :=
    mapWithInput (range.comp ((length_list _).comp hq)) (binary_testBit (const idx) (snd _ _))
  unfold gateEntry
  refine ite_decide (decide_eq' ((fst _ _).comp hg) (const true)) ?_ ?_
  · exact ite_decide (decide_eq' (bool_and' ((headD false).comp hins) ((headD false).comp houts))
      (const true)) hneg (const 1)
  · have htl := (tail (encA := encBool)).comp hins
    exact ite_decide (decide_eq' houts (cons' (bool_xor.comp (((headD false).comp hins).prod
      (allWithInput htl (snd _ _)))) htl)) (const 1) (const 0)

/-- **Glue vertices are polynomial-time.** -/
theorem computableInPolyTime_glueVertex {S : α → List ℕ}
    (hS : ComputableInPolyTime S inp (encList encUnary)) {w : α → ℕ}
    (hw : ComputableInPolyTime w inp encUnary) :
    ComputableInPolyTime (fun a => (glueVertex (S a) (gs a) (w a) : List ℕ × List ℕ)) inp
      (encPair (encList encNat) (encList encNat)) := by
  have hqs := computableInPolyTime_occurrences hgs
  have hN := (length_list _).comp hqs
  have hq := listGetDWithInput hqs hw 0
  unfold glueVertex
  refine ite_decide (decide_eq' (computableInPolyTime_lastOcc hqs hq hN) (optionSome _ |>.comp hw))
    ((ports_unary_to_binary (cons' (unary_add' (unary_mul' (const 2) hw) (const 1))
      (cons' (unary_add' (unary_mul' (const 2) (unary_add' hN hw)) (const 1)) (const [])))).prod
      (ite_decide (decide_mem hS hq) (const _) (const _))) (const _)

end Vertices

/-- **The scalar vertex is polynomial-time.** -/
theorem computableInPolyTime_scalarVertex {S : α → List ℕ} {X : α → List Bool}
    {gs : α → List GateCode} (hS : ComputableInPolyTime S inp (encList encUnary))
    (hX : ComputableInPolyTime X inp encBits)
    (hgs : ComputableInPolyTime gs inp (encList encGateCode)) :
    ComputableInPolyTime (fun a => (scalarVertex (S a) (X a) (gs a) : List ℕ × List ℕ)) inp
      (encPair (encList encNat) (encList encNat)) := by
  simp only [scalarVertex_eq]
  refine (const []).prod (cons' (ite_decide (decide_eq' (allWithInput hS (bool_or.comp
    ((decide_mem (computableInPolyTime_occurrences (hgs.comp (fst _ _))) (snd _ _)).prod
    (bitsGetDWithInput (hX.comp (fst _ _)) (snd _ _) false)))) (const true)) (const 1) (const 0))
    (const []))

/-- **The network of a circuit is polynomial-time** in the gate codes, the measured qubits, the
input register and the Hadamard sign, with its number of rows in binary. -/
theorem computableInPolyTime_network {neg : α → ℕ} {S : α → List ℕ} {X : α → List Bool}
    {gs : α → List GateCode} (hneg : ComputableInPolyTime neg inp encNat)
    (hS : ComputableInPolyTime S inp (encList encUnary)) (hX : ComputableInPolyTime X inp encBits)
    (hgs : ComputableInPolyTime gs inp (encList encGateCode)) :
    ComputableInPolyTime (fun a => network (neg a) (S a) (X a) (gs a)) inp
      (encPair encNat ExplicitTensorNetwork.encExplicitNetwork) := by
  have hL := (length_list _).comp hgs
  have hN := (length_list _).comp (computableInPolyTime_occurrences hgs)
  have hgate (c : ℕ) : ComputableInPolyTime (fun a => (List.range (gs a).length).map
      (gateVertex (neg a) (X a) (gs a) c)) inp
      (encList (encPair (encList encNat) (encList encNat))) :=
    mapWithInput (range.comp hL) (computableInPolyTime_gateVertex (hgs.comp (fst _ _))
      (hneg.comp (fst _ _)) (hX.comp (fst _ _)) (const c) (snd _ _))
  have hverts : ComputableInPolyTime (fun a =>
      (List.range (gs a).length).map (gateVertex (neg a) (X a) (gs a) 0) ++
        (List.range (gs a).length).map (gateVertex (neg a) (X a) (gs a) 1) ++
        (List.range (occurrences (gs a)).length).map (glueVertex (S a) (gs a)) ++
        [scalarVertex (S a) (X a) (gs a)] ++
      (List.range (2 * (occurrences (gs a)).length)).map fun w =>
        (([2 * w, 2 * w + 1], eqTable) : List ℕ × List ℕ)) inp
      (encList (encPair (encList encNat) (encList encNat))) :=
    listAppend' (listAppend' (listAppend' (listAppend' (hgate 0) (hgate 1))
      (mapWithInput (range.comp hN) (computableInPolyTime_glueVertex (hgs.comp (fst _ _))
        (hS.comp (fst _ _)) (snd _ _))))
      (cons' (computableInPolyTime_scalarVertex hS hX hgs) (const [])))
      (mapWithInput (range.comp (unary_mul' (const 2) hN))
        ((ports_unary_to_binary (cons' (unary_mul' (const 2) (snd _ _))
          (cons' (unary_add' (unary_mul' (const 2) (snd _ _)) (const 1)) (const [])))).prod
          (const _)))
  unfold network
  exact (unary_to_binary.comp (unary_add' (unary_add' (unary_mul' (const 2) hL) hN)
    (const 1))).prod (computableInPolyTime_equivProd_symm.comp
      ((unary_mul' (const 2) (unary_mul' (const 2) hN)).prod hverts))

end Cslib.Quantum.PathNetwork

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedContraction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# Rows-first bipartiteness in polynomial time

Rows-first bipartiteness of a described network at a number of rows
(`DescribedNetwork.IsRowsFirstBipartite`) is decidable in polynomial time, from the number of rows
in binary and the network as encoded by `DescribedNetwork.encDescribed`. The test checks that every
port names an edge and counts, for each edge, its ports among the first `r` vertices and among the
others. It is the rows-first part of the guards of the contraction machines, for explicit networks
and for entry procedures.

## Main results

* `Cslib.Circuits.Frontier.DescribedNetwork.rowsFirst_polyTime`: rows-first bipartiteness is
  decidable in polynomial time.
-/

public section

namespace Cslib.Circuits.Frontier.DescribedNetwork

open Turing.MultiTapeTM

variable {T : Type} {encT : T ↪ List Bool}

/-- Rows-first bipartiteness as a conjunction of list tests. -/
private def rowsTest (r : ℕ) (d : DescribedNetwork T) : Bool :=
  d.vertices.all (fun v => v.1.all fun i => decide (i < d.numEdges)) &&
    (List.range d.numEdges).all (fun i =>
      decide (((d.vertices.take r).flatMap Prod.fst).count i = 1) &&
        decide (((d.vertices.drop r).flatMap Prod.fst).count i = 1))

private theorem decide_eq_rowsTest (r : ℕ) (d : DescribedNetwork T) :
    decide (d.IsRowsFirstBipartite r) = rowsTest r d := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [rowsTest, IsRowsFirstBipartite, decide_eq_true_eq, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, List.count_flatMap, Function.comp_def]

/-- Taking or dropping `min |l| r` elements is taking or dropping `r`. -/
private theorem take_drop_min {α : Type} (l : List α) (r : ℕ) :
    l.take (min l.length r) = l.take r ∧ l.drop (min l.length r) = l.drop r := by
  rcases le_total l.length r with hle | hle
  · rw [min_eq_left hle, List.take_length, List.take_of_length_le hle, List.drop_length,
      List.drop_of_length_le hle]
    exact ⟨rfl, rfl⟩
  · rw [min_eq_right hle]
    exact ⟨rfl, rfl⟩

/-- **Rows-first bipartiteness is decidable in polynomial time**, from the number of rows and the
network. -/
theorem rowsFirst_polyTime :
    ComputableInPolyTime
      (fun ((r, d) : ℕ × DescribedNetwork T) => decide (d.IsRowsFirstBipartite r))
      (encPair encNat (encDescribed encT)) encBool := by
  have hr := ComputableInPolyTime.fst encNat (encDescribed encT)
  have hm : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T => G.2.numEdges)
      (encPair encNat (encDescribed encT)) encUnary :=
    numEdges_polyTime.comp (ComputableInPolyTime.snd _ _)
  have hvs : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T => G.2.vertices)
      (encPair encNat (encDescribed encT)) (encList (encPair (encList encNat) encT)) :=
    vertices_polyTime.comp (ComputableInPolyTime.snd _ _)
  -- Ports in range.
  have h1 : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T =>
      G.2.vertices.all (fun v => v.1.all fun i => decide (i < G.2.numEdges)))
      (encPair encNat (encDescribed encT)) encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    refine ComputableInPolyTime.allWithInput
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)) ?_
    exact ComputableInPolyTime.binary_lt.comp ((ComputableInPolyTime.snd _ _).prod
      (ComputableInPolyTime.unary_to_binary.comp (hm.comp ((ComputableInPolyTime.fst _ _).comp
        (ComputableInPolyTime.fst _ _)))))
  -- Each edge has one row port and one column port.
  have hlen := (ComputableInPolyTime.length_list _).comp hvs
  have hcap := ComputableInPolyTime.binary_min_unary' hlen hr
  have htake : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T =>
      G.2.vertices.take (min G.2.vertices.length G.1)) (encPair encNat (encDescribed encT))
      (encList (encPair (encList encNat) encT)) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hvs.tidy hcap.tidy)
  have hdrop : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T =>
      G.2.vertices.drop (min G.2.vertices.length G.1)) (encPair encNat (encDescribed encT))
      (encList (encPair (encList encNat) encT)) :=
    .of_tidy (ComputableTidilyInPolyTime.listDropWithInput hvs.tidy hcap.tidy)
  have hflat {l : ℕ × DescribedNetwork T → List (List ℕ × T)}
      (hl : ComputableInPolyTime l (encPair encNat (encDescribed encT))
        (encList (encPair (encList encNat) encT))) :
      ComputableInPolyTime (fun G => (l G).flatMap Prod.fst) (encPair encNat (encDescribed encT))
        (encList encNat) :=
    ComputableInPolyTime.flatMapWithInput (f := fun _ v => v.1) hl
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  have hcount {l : ℕ × DescribedNetwork T → List ℕ}
      (hl : ComputableInPolyTime l (encPair encNat (encDescribed encT)) (encList encNat)) :
      ComputableInPolyTime (fun p : (ℕ × DescribedNetwork T) × ℕ =>
        decide ((l p.1).count p.2 = 1))
        (encPair (encPair encNat (encDescribed encT)) encUnary) encBool := by
    have hc := ComputableInPolyTime.countPWithInput (test := fun p a => decide (a = p.2))
      (hl.comp (ComputableInPolyTime.fst (encPair encNat (encDescribed encT)) encUnary))
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.snd _ _).comp
          (ComputableInPolyTime.fst _ _))))
    refine (ComputableInPolyTime.decide_eq' hc (ComputableInPolyTime.const 1)).of_enc_eq
      fun p => ?_
    simp only [Function.comp_apply, List.count_eq_countP]
    congr 3
  have h2 : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T =>
      (List.range G.2.numEdges).all (fun i =>
        decide (((G.2.vertices.take (min G.2.vertices.length G.1)).flatMap Prod.fst).count i =
          1) &&
          decide (((G.2.vertices.drop (min G.2.vertices.length G.1)).flatMap Prod.fst).count i =
            1))) (encPair encNat (encDescribed encT)) encBool :=
    ComputableInPolyTime.allWithInput (ComputableInPolyTime.range.comp hm)
      (ComputableInPolyTime.bool_and.comp ((hcount (hflat htake)).prod (hcount (hflat hdrop))))
  refine (ComputableInPolyTime.bool_and.comp (h1.prod h2)).of_enc_eq fun ⟨r, d⟩ => ?_
  obtain ⟨ht, hdr⟩ := take_drop_min d.vertices r
  dsimp only
  rw [decide_eq_rowsTest, rowsTest]
  simp only [Function.comp_apply, ht, hdr]

end Cslib.Circuits.Frontier.DescribedNetwork

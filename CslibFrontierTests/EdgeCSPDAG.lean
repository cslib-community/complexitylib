/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Logics.Propositional.CSP.Edge.DAGPaths
import Mathlib.Tactic.FinCases

/-!
# Nonvacuous positional edge-CSP DAG examples

Two copies of one four-port relation ensure the actual exact-two-occurrence edge model.
Within each coordinate pair both `00` and `11` are feasible; cross-pair flips are infeasible.
The DAG revisits the *same original constraint position* at timestamps zero and one.
-/

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.DAG Cslib.BitString

namespace EdgeCSPDAGTest

private def pairedSem (_ : Unit) : List Bool → Bool
  | [a, b, c, d] => (a == b) && (c == d)
  | _ => false

private abbrev pairedInstance : CSP Unit (Fin 4) :=
  [⟨(), [0, 1, 2, 3]⟩, ⟨(), [0, 1, 2, 3]⟩]

private abbrev port (j : Fin 4) : Occurrence pairedInstance := ⟨0, j⟩

private abbrev a : Arc pairedInstance := ⟨port 0, 0, true⟩
private abbrev b : Arc pairedInstance := ⟨port 1, 0, false⟩
private abbrev c : Arc pairedInstance := ⟨port 2, 1, true⟩
private abbrev d : Arc pairedInstance := ⟨port 3, 1, false⟩

private def repeated : DAG pairedInstance := ⟨{0, 1, 2, 3}, {(0, 0), (0, 1)}, {a, b, c, d}⟩

private def zero : OccurrenceLabeling pairedInstance Bool := fun _ => false

private theorem paired_edge : EdgeInstance pairedInstance := by
  unfold EdgeInstance
  decide

private theorem zero_valid : ValidLabeling pairedSem zero := by
  unfold ValidLabeling
  decide

private theorem paired_even : EdgeInstance.EvenConstraints pairedSem pairedInstance := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }

private theorem repeated_dag : repeated.IsFDAG pairedSem zero := by
  refine ⟨zero_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Supported, repeated, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    decide
  · simp only [repeated, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    decide
  · simp [repeated, Occurrence.var]
  · refine ⟨by
      simp only [repeated, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
      decide, ⟨Sum.elim (fun v => 2 * ((v.val + 1) / 2))
      (fun c => 2 * c.2 + 1), ?_⟩⟩
    intro x y hxy
    rcases hxy with ⟨e, he, rfl, rfl⟩ | ⟨c, hc, d, hd, hcd, rfl, rfl⟩
    · simp only [repeated, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    · simp only [repeated, Finset.mem_insert, Finset.mem_singleton] at hc hd
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num at *
  · simp only [repeated, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    simp [Arc.copy, ValidLabeling, Fin.forall_fin_succ, localTuple, pairFlip,
      flipOn_apply, pairedInstance, zero, pairedSem, List.ofFn_succ]
  · simp only [repeated, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    simp [ValidLabeling, Fin.forall_fin_succ, localTuple, pairFlip,
      flipOn_apply, pairedInstance, zero, pairedSem, List.ofFn_succ]

example : (⟨∅, ∅, ∅⟩ : DAG pairedInstance).IsFDAG pairedSem zero := isFDAG_empty zero_valid

example : ValidLabeling pairedSem (pairFlip zero (port 0) (port 1)) := by
  unfold ValidLabeling
  decide

example : ¬ ValidLabeling pairedSem (pairFlip zero (port 0) (port 2)) := by
  unfold ValidLabeling
  decide

private theorem earliest : repeated.Earliest a.copy := by
  simp [Earliest, repeated, Arc.copy]

example : (repeated.removeRootCopy a.occurrence.var a.copy).IsFDAG pairedSem
    (pairFlip zero a.occurrence b.occurrence) :=
  repeated_dag.removeRootCopy paired_even (by decide) (by decide) rfl rfl rfl earliest

example : ValidLabeling pairedSem (pairFlip zero a.occurrence b.occurrence) ∧
    (repeated.removeRootCopy a.occurrence.var a.copy).IsFDAG pairedSem
      (pairFlip zero a.occurrence b.occurrence) ∧
    (repeated.removeRootCopy a.occurrence.var a.copy).arcs =
      (repeated.arcs.erase a).erase b :=
  repeated_dag.delete_earliest_pair paired_even (by decide) (by decide)
    rfl rfl rfl earliest (by decide) (by decide)

example : (repeated.reroot a b).IsFDAG pairedSem
    (pairFlip zero a.occurrence b.occurrence) :=
  repeated_dag.reroot_earliest paired_even (by decide) (by decide)
    rfl rfl rfl earliest (by decide) (by decide)

private def oneStep : Walk pairedInstance := ⟨0, [(port 0, port 1)]⟩
private def stamps (o : Occurrence pairedInstance) : ℕ := o.2.val / 2

private theorem oneStep_directed : DirectedPath repeated oneStep stamps := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact ⟨rfl, rfl, trivial⟩
    · decide
  · decide
  · intro s hs
    have he : s = (port 0, port 1) := List.mem_singleton.mp hs
    subst s
    decide
  · intro s hs
    have he : s = (port 0, port 1) := List.mem_singleton.mp hs
    subst s
    decide
  · intro s hs t ht _
    exact (List.mem_singleton.mp hs).trans (List.mem_singleton.mp ht).symm

example (n : ℕ) : ValidLabeling pairedSem ((oneStep.take n).flip zero) :=
  oneStep_directed.valid_take repeated_dag paired_even n

example : oneStep.IsFWalk pairedSem zero :=
  oneStep_directed.isFWalk repeated_dag paired_even (by trivial) (by decide)

-- Two one-edge directed paths meet at their common terminal copy.
private def meet : DAG pairedInstance := terminalPair a b.reverse

private theorem meet_dag : meet.IsFDAG pairedSem zero := by
  refine ⟨zero_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Supported, meet, terminalPair, Finset.forall_mem_insert,
      Finset.mem_singleton, forall_eq]
    decide
  · simp [meet, terminalPair, Arc.reverse]
  · simp [meet, terminalPair, Arc.reverse]
  · refine ⟨by simp [meet, terminalPair], ⟨Sum.elim (fun _ => 0) (fun _ => 1), ?_⟩⟩
    intro x y hxy
    rcases hxy with ⟨e, he, rfl, rfl⟩ | ⟨c, hc, d, hd, hcd, rfl, rfl⟩
    · rcases (show e = a ∨ e = b.reverse from by
        simpa [meet, terminalPair] using he) with rfl | rfl <;> decide
    · have hce : c = a.copy := Finset.mem_singleton.mp hc
      have hde : d = a.copy := Finset.mem_singleton.mp hd
      subst c; subst d
      exact (Nat.lt_irrefl _ hcd).elim
  · simp [meet, terminalPair, Arc.reverse, Arc.copy, ValidLabeling,
      Fin.forall_fin_succ, localTuple, pairFlip, flipOn_apply, zero, pairedSem,
      pairedInstance, List.ofFn_succ]
  · simp [meet, terminalPair, Arc.reverse]

example : ValidLabeling pairedSem (meet.flip zero) :=
  meet_dag.valid_flip_of_pairedCopies paired_even
    (pairedCopies_terminalPair rfl rfl (by decide))

-- A nonempty external f-walk uses the same original constraint as the surviving DAG.
private def small : DAG pairedInstance := repeated.restrict {0, 1} {(0, 0)}
private def external : Walk pairedInstance := ⟨2, [(port 2, port 3)]⟩

private theorem small_arcs : small.arcs = {a, b} := by decide

private theorem external_fwalk : external.IsFWalk pairedSem zero := by
  refine ⟨⟨?_, by trivial, ?_⟩, by decide⟩
  · constructor
    · exact ⟨rfl, rfl, trivial⟩
    · decide
  · change ValidLabeling pairedSem zero ∧
      ValidLabeling pairedSem (flipOn {port 2, port 3} zero)
    exact ⟨zero_valid, by unfold ValidLabeling; decide⟩

private theorem external_no_extension : ∀ n < external.steps.length, ∀ e ∈ small.arcs,
    ∀ o : Occurrence pairedInstance, o.var = (external.take n).finish →
      o.1 = e.occurrence.1 → ¬ ((external.take n).snoc o e.occurrence).IsFWalk pairedSem zero := by
  have hbad : ∀ e ∈ small.arcs, ∀ o : Occurrence pairedInstance,
      o.var = 2 → o.1 = e.occurrence.1 →
        ¬ ValidLabeling pairedSem (pairFlip zero o e.occurrence) := by
    rw [small_arcs]
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    unfold ValidLabeling
    decide
  intro n hn e he o ho hc hfw
  have hn0 : n = 0 := by change n < 1 at hn; omega
  subst n
  have hov : o.var = 2 := ho
  have hne : o ≠ e.occurrence := by
    intro hh
    exact hbad e he o hov hc (by rw [hh, pairFlip_self]; exact zero_valid)
  apply hbad e he o hov hc
  have hv := hfw.1.valid_flip
  rw [pairFlip_eq zero hne]
  simpa [Walk.flip, Walk.edges, Walk.snoc, Walk.take, Walk.edgesOf] using hv

example : small.IsFDAG pairedSem (external.flip zero) :=
  (repeated_dag.restrict {0, 1} {(0, 0)}).flip_walk_of_no_prefix_extension paired_even
    external_fwalk (by decide)
    (by simp [external, Walk.edges, Walk.edgesOf, restrict, repeated, Occurrence.var])
    external_no_extension

-- A repeated original incidence is rejected, regardless of its new orientation and timestamp.
private def reused : DAG pairedInstance :=
  {repeated with arcs := insert ⟨port 0, 2, false⟩ repeated.arcs}

example : ¬ reused.IsFDAG pairedSem zero := by
  intro h
  have he := h.unique a (by decide) ⟨port 0, 2, false⟩ (by decide) rfl
  have ht := congrArg Arc.time he
  norm_num at ht

-- Different original constraints cannot receive the same timestamp, even as isolated copies.
example : ¬ ({repeated with copies := insert (1, 0) repeated.copies}).IsFDAG
    pairedSem zero := by
  intro h
  have he := h.ordered.1 (0, 0) (by decide) (1, 0) (by decide) rfl
  have hi := congrArg (fun c => c.1.val) he
  norm_num at hi

private def paritySem (_ : Unit) (xs : List Bool) : Bool := xs.count true % 2 == 0

private theorem parity_even : EdgeInstance.EvenConstraints paritySem pairedInstance := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }

-- Even parity alone allows the forbidden cross-pair, violating condition 6.
example : ¬ repeated.IsFDAG paritySem zero := by
  intro h
  exact h.noShortcut a (by decide) c (by decide) rfl rfl (by decide)
    (by unfold ValidLabeling; decide)

private abbrev child : Arc pairedInstance := ⟨port 2, 0, false⟩
private def star : DAG pairedInstance := ⟨{0, 1, 2}, {(0, 0)}, {a, b, child}⟩

private theorem star_dag : star.IsFDAG paritySem zero := by
  refine ⟨by unfold ValidLabeling; decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Supported, star, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    decide
  · simp only [star, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    decide
  · simp [star, Occurrence.var]
  · refine ⟨by simp [star], ⟨Sum.elim (fun v => if v = 0 then 0 else 2) (fun _ => 1), ?_⟩⟩
    intro x y hxy
    rcases hxy with ⟨e, he, rfl, rfl⟩ | ⟨c, hc, d, hd, hcd, rfl, rfl⟩
    · rcases (show e = a ∨ e = b ∨ e = child from by
        simpa [star] using he) with rfl | rfl | rfl <;> decide
    · have hce : c = a.copy := Finset.mem_singleton.mp hc
      have hde : d = a.copy := Finset.mem_singleton.mp hd
      subst c; subst d
      exact (Nat.lt_irrefl _ hcd).elim
  · simp only [star, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq, Arc.copy]
    unfold ValidLabeling
    simp only [true_implies, false_implies, and_true, Bool.false_eq_true]
    decide
  · simp [star]

-- Lemma 37 retains an additional outgoing child, and its new two-port exchange is feasible.
example : (star.reroot a b).IsFDAG paritySem (pairFlip zero a.occurrence b.occurrence) :=
  star_dag.reroot_earliest parity_even (by decide) (by decide) rfl rfl rfl
    (by simp [Earliest, star, Arc.copy])
    (by simp [star, Occurrence.var]) (by simp [star])

example : child ∈ (star.reroot a b).arcs := by decide

example : localTuple (pairFlip (pairFlip zero (port 0) (port 1)) (port 1) (port 2)) 0 =
    [true, false, true, false] := by decide

-- Timestamp order must also respect directed variable transitions between copies.
private abbrev backwardsOut : Arc pairedInstance := ⟨port 1, 2, false⟩
private abbrev backwardsIn : Arc pairedInstance :=
  ⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, 1, true⟩
private def backwards : DAG pairedInstance :=
  ⟨{0, 1, 2, 3}, {(0, 2), (1, 1)}, {backwardsOut, backwardsIn}⟩

example : ¬ backwards.IsFDAG pairedSem zero := by
  intro h
  obtain ⟨rank, hr⟩ := h.ordered.2
  have hfirst : rank (.inr (0, 2)) < rank (.inl 1) :=
    hr _ _ (Or.inl ⟨backwardsOut, by decide, rfl, rfl⟩)
  have hsecond : rank (.inl 1) < rank (.inr (1, 1)) :=
    hr _ _ (Or.inl ⟨backwardsIn, by decide, rfl, rfl⟩)
  have htime : rank (.inr (1, 1)) < rank (.inr (0, 2)) :=
    hr _ _ (Or.inr ⟨(1, 1), by decide, (0, 2), by decide, by decide, rfl, rfl⟩)
  omega

private def oddSem (_ : Unit) : List Bool → Bool
  | [a, b, c, d] => (a != b) && (c == d)
  | _ => false

private def odd : OccurrenceLabeling pairedInstance Bool := fun o => o.2.val == 0

private theorem odd_even : EdgeInstance.EvenConstraints oddSem pairedInstance := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }

example : (localTuple odd 0).count true = 1 := by decide

example : (⟨∅, ∅, ∅⟩ : DAG pairedInstance).IsFDAG oddSem odd :=
  isFDAG_empty (by unfold ValidLabeling; decide)

private theorem repeated_odd : repeated.IsFDAG oddSem odd := by
  refine ⟨by unfold ValidLabeling; decide, repeated_dag.supported, repeated_dag.unique,
    repeated_dag.indegree, repeated_dag.ordered, ?_, ?_⟩
  · simp only [repeated, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    simp [Arc.copy, ValidLabeling, Fin.forall_fin_succ, localTuple, pairFlip,
      flipOn_apply, pairedInstance, odd, oddSem, List.ofFn_succ]
  · simp only [repeated, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    simp [ValidLabeling, Fin.forall_fin_succ, localTuple, pairFlip,
      flipOn_apply, pairedInstance, odd, oddSem, List.ofFn_succ]

example : (repeated.reroot a b).IsFDAG oddSem (pairFlip odd a.occurrence b.occurrence) :=
  repeated_odd.reroot_earliest odd_even (by decide) (by decide) rfl rfl rfl earliest
    (by decide) (by decide)

private def chainSem (cross : Bool) : List Bool → Bool
  | [a, b, c, d] => if cross then (a == d) && (b == c) else (a == b) && (c == d)
  | _ => false

private abbrev chainInstance : CSP Bool (Fin 4) :=
  [⟨false, [0, 1, 2, 3]⟩, ⟨true, [0, 1, 2, 3]⟩]
private abbrev cp (i : Fin 2) (j : Fin 4) : Occurrence chainInstance :=
  ⟨i, ⟨j.val, by fin_cases i <;> exact j.isLt⟩⟩
private abbrev c0 : Arc chainInstance := ⟨cp 0 0, 0, true⟩
private abbrev c1 : Arc chainInstance := ⟨cp 0 1, 0, false⟩
private abbrev c2 : Arc chainInstance := ⟨cp 1 1, 1, true⟩
private abbrev c3 : Arc chainInstance := ⟨cp 1 2, 1, false⟩
private abbrev c4 : Arc chainInstance := ⟨cp 0 2, 2, true⟩
private abbrev c5 : Arc chainInstance := ⟨cp 0 3, 2, false⟩
private def chain : DAG chainInstance :=
  ⟨{0, 1, 2, 3}, {(0, 0), (1, 1), (0, 2)}, {c0, c1, c2, c3, c4, c5}⟩
private def chainZero : OccurrenceLabeling chainInstance Bool := fun _ => false
private def chainWalk : Walk chainInstance :=
  ⟨0, [(cp 0 0, cp 0 1), (cp 1 1, cp 1 2), (cp 0 2, cp 0 3)]⟩
private def chainTime (o : Occurrence chainInstance) : ℕ :=
  if o.1.val = 1 then 1 else if o.2.val < 2 then 0 else 2

example : EdgeInstance chainInstance := by
  unfold EdgeInstance
  decide

private theorem chain_even : EdgeInstance.EvenConstraints chainSem chainInstance := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }

private theorem chain_dag : chain.IsFDAG chainSem chainZero := by
  refine ⟨by unfold ValidLabeling; decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Supported, chain, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    decide
  · simp only [chain, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    simp [cp]
  · simp [chain, Occurrence.var]
  · refine ⟨?_, ⟨Sum.elim (fun v => 2 * v.val) (fun c => 2 * c.2 + 1), ?_⟩⟩
    · simp [chain]
    · intro x y hxy
      rcases hxy with ⟨e, he, rfl, rfl⟩ | ⟨c, hc, d, hd, hcd, rfl, rfl⟩
      · rcases (show e = c0 ∨ e = c1 ∨ e = c2 ∨ e = c3 ∨ e = c4 ∨ e = c5 from by
          simpa [chain] using he) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · simp only [chain, Finset.mem_insert, Finset.mem_singleton] at hc hd
        rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> norm_num at *
  · simp [chain, Arc.copy, ValidLabeling, Fin.forall_fin_succ, localTuple,
      pairFlip, flipOn_apply, chainZero, chainSem, chainInstance, List.ofFn_succ]
  · simp [chain, ValidLabeling, Fin.forall_fin_succ, localTuple,
      pairFlip, flipOn_apply, chainZero, chainSem, chainInstance, List.ofFn_succ]

private theorem chain_directed : DirectedPath chain chainWalk chainTime := by
  refine ⟨?_, by decide, ?_, ?_, ?_⟩
  · refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, by decide⟩
  · intro s hs
    rcases (show s = (cp 0 0, cp 0 1) ∨ s = (cp 1 1, cp 1 2) ∨
        s = (cp 0 2, cp 0 3) from by simpa [chainWalk] using hs) with rfl | rfl | rfl <;> decide
  · intro s hs
    rcases (show s = (cp 0 0, cp 0 1) ∨ s = (cp 1 1, cp 1 2) ∨
        s = (cp 0 2, cp 0 3) from by simpa [chainWalk] using hs) with rfl | rfl | rfl <;> decide
  · simp [chainWalk, inArc, Arc.copy, chainTime]

-- This actual directed path visits original constraint 0 twice, at different timestamps.
example : chainWalk.IsFWalk chainSem chainZero :=
  chain_directed.isFWalk chain_dag chain_even
    (by simp [Walk.InternallyConsistent, chainWalk, Inconsistent, chainZero])
    (by decide)

example : ValidLabeling chainSem ((chainWalk.take 2).flip chainZero) :=
  chain_directed.valid_take chain_dag chain_even 2

example : localTuple (chainWalk.flip chainZero) 0 = [true, true, true, true] := by decide

end EdgeCSPDAGTest

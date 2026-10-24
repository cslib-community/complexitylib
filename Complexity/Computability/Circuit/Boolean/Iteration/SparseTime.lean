/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Iteration.CounterChart.Time

import Mathlib.Tactic.Linarith

/-!
# Sparse counter modifications with a live iteration count

Let `r` be the number of inputs where the permutation differs from the counter.
Encoding and decoding cost `O((n+1)*(r+1))` and are each performed once. The middle
stage costs `O((n+1)*(m+1))` for an `m`-bit time, giving additive dependence on edits
and time width.
The theorem constructs actual CSLib Boolean circuits from any permutation.
The initial state occupies the first `n` inputs; the last `m` are the nonnegative
iteration count in least-significant-bit-first order. Constants and selectors
are charged. The chart is chosen nonuniformly; no bound on its construction
runtime or on generating the output circuit is asserted.

## Main definitions

* The input consists of an initial state followed by a binary iteration count.

## Main results

* `sparse_counter_variable_time`: additive dependence on edits and time width.
* `sparse_counter_labels`: canonical coordinates at linear table cost.
* `sparse_coordinate_variable_time`: both coordinate conversions charged.

## References

* Adapted from lean/Proofs/SparseCounterTime.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

attribute [local instance] counterChartWordOrder



open Cslib.FunctionalGraph

variable {n R : ℕ}

/-- Given a `CounterIntervalChart` with `R` runs for an injective map `f : BitVec n → BitVec n`,
iterating `f` by an `m`-bit input time on an `n`-bit input state has a Boolean circuit of size at
most `1000 * (n + 3) * (R + m)`. -/
theorem CounterIntervalChart.variable_time {f : BitVec n → BitVec n}
    (chart : CounterIntervalChart f R) (hf : Function.Injective f) (m : ℕ) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      out.Computes Boolean.interpretation (fun z i =>
        (f^[(word (fun j => z (Fin.natAdd n j))).toNat]
          (word fun j => z (Fin.castAdd m j))).getLsbD i.val) ∧
      out.size ≤ 1000 * (n + 3) * (R + m) := by
  let x := fun z : BitString (n + m) => word fun i => z (Fin.castAdd m i)
  let bits := fun z : BitString (n + m) => fun j : Fin m => z (Fin.natAdd n j)
  let constants : Set (BitString (n + m) → Bool) := {fun _ => false, fun _ => true}
  let src := inputs (n + m) ∪ constants
  have hc (b : Bool) : (fun _ : BitString (n + m) => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation (inputs (n + m)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hx : wordWires x ⊆ src := by
    rintro _ ⟨i, rfl⟩
    simpa only [x, getLsbD_word] using
      (show (fun z : BitString (n + m) => z (Fin.castAdd m i)) ∈ src
      from Or.inl ⟨_, rfl⟩)
  let encoded := fun z => chart.encode (x z)
  have henc := chart.synthesis_encode src x hx hc
  let s1 := src ∪ wires encoded
  have hadv := synthesis_advanceCycleLabel s1 encoded bits (fun _ h => Or.inr h)
    (fun j => Or.inl (Or.inl ⟨_, rfl⟩)) (Or.inl (hc false))
  let advanced := fun z => advanceCycleLabel (encoded z) (bits z)
  let s2 := s1 ∪ wires advanced
  let rep := fun z => word (labelRepresentative (advanced z))
  let p := fun z => labelPhase (advanced z)
  have hrep : wordWires rep ⊆ s2 := by
    rintro _ ⟨i, rfl⟩
    simpa only [rep, getLsbD_word, labelRepresentative] using
      (show (fun z => advanced z (Fin.castAdd (chartWidth n + chartWidth n) i)) ∈ s2
        from Or.inr ⟨_, rfl⟩)
  have hp : wordWires p ⊆ s2 := by
    rintro _ ⟨i, rfl⟩
    simpa only [p, labelPhase, getLsbD_word] using
      (show (fun z => advanced z (Fin.natAdd n (Fin.natAdd (chartWidth n) i))) ∈ s2
        from Or.inr ⟨_, rfl⟩)
  have hdec := chart.synthesis_decode s2 rep p hrep hp (fun b => Or.inl (Or.inl (hc b)))
  obtain ⟨out, hout, hs⟩ := (hconst.trans (henc.trans (hadv.trans hdec))).exists_circuit_outputs
  refine ⟨out, ?_, ?_⟩
  · intro z
    rw [hout z]
    dsimp only [rep, p, advanced, encoded]
    rw [chart.encode_spec hf, advanceCycleLabel_spec]
    simp only [wordCycleLabel, labelRepresentative_labelBits, word_getLsbD, labelPhase_labelBits,
      chart.decode_spec hf]
    rfl
  · obtain ⟨j, _, _⟩ := chart.covers 0
    have hR : 1 ≤ R := by have := j.isLt; lia
    have hRk : n + 3 ≤ R * (n + 3) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (n + 3) hR
    nlinarith only [hs, hRk, show 2 ≤ n + 3 by lia,
      Nat.zero_le (R * (n + 3)), Nat.zero_le (m * (n + 3))]

/-- Every sparsely edited counter permutation has an additive live-time bound.
Both the time and initial state are inputs; no edit-list or chart certificate is
an input or hypothesis of the resulting Boolean circuit. -/
theorem sparse_counter_variable_time (f : Equiv.Perm (BitVec n)) (m : ℕ) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      out.Computes Boolean.interpretation (fun z i =>
        ((f : BitVec n → BitVec n)^[(word (fun j => z (Fin.natAdd n j))).toNat]
          (word fun j => z (Fin.castAdd m j))).getLsbD i.val) ∧
      out.size ≤ 1000 * (n + 3) * ((disagreement f (fun x => x + 1)).card + m + 1) := by
  obtain ⟨R, hR, ⟨chart⟩⟩ := exists_counterIntervalChart (f : BitVec n → BitVec n)
  obtain ⟨out, hout, hs⟩ := chart.variable_time f.injective m
  exact ⟨out, hout, hs.trans (Nat.mul_le_mul_left (1000 * (n + 3)) (by lia))⟩

/-- The same chart computes canonical cycle labels and phase in linear table cost. -/
theorem sparse_counter_labels (f : Equiv.Perm (BitVec n)) :
    ∃ out : Circuit Boolean.signature n (n + (chartWidth n + chartWidth n)),
      out.Computes Boolean.interpretation (fun x => wordCycleLabel f (word x)) ∧
      out.size ≤ 500 * (n + 3) * ((disagreement f (fun x => x + 1)).card + 1) := by
  obtain ⟨R, hR, ⟨chart⟩⟩ := exists_counterIntervalChart (f : BitVec n → BitVec n)
  let constants : Set (BitString n → Bool) := {fun _ => false, fun _ => true}
  let src := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : BitString n => b) ∈ src := by cases b <;> simp [src, constants]
  have hw : wordWires (fun x : BitString n => word x) ⊆ src := by
    rintro _ ⟨i, rfl⟩
    simpa only [getLsbD_word] using (show (fun x : BitString n => x i) ∈ src from Or.inl ⟨i, rfl⟩)
  have hconst : Synthesis Boolean.interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  obtain ⟨out, hout, hs⟩ :=
    (hconst.trans (chart.synthesis_encode src word hw hc)).exists_circuit_outputs
  refine ⟨out, fun x => (hout x).trans (chart.encode_spec f.injective _), ?_⟩
  have hb := Nat.mul_le_mul_right (220 * (n + 3)) hR
  nlinarith only [hs, hb, Nat.zero_le (n * (disagreement f (fun x => x + 1)).card),
    Nat.zero_le n, Nat.zero_le (disagreement f (fun x => x + 1)).card]

/-- Charged coordinate changes preserve the additive live-time bound. -/
theorem sparse_coordinate_variable_time (f g e : Equiv.Perm (BitVec n))
    (hcycle : ∀ x, e (g x) = e x + 1)
    (encode decode : Circuit Boolean.signature n n)
    (he : encode.Computes Boolean.interpretation (fun x i => (e (word x)).getLsbD i.val))
    (hd : decode.Computes Boolean.interpretation (fun x i => (e.symm (word x)).getLsbD i.val))
    (m : ℕ) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      out.Computes Boolean.interpretation (fun z i =>
        ((f : BitVec n → BitVec n)^[(word (fun j => z (Fin.natAdd n j))).toNat]
          (word fun j => z (Fin.castAdd m j))).getLsbD i.val) ∧
      out.size ≤ encode.size + decode.size +
        1000 * (n + 3) * ((disagreement f g).card + m + 1) := by
  have hcounter : e ∘ g ∘ e.symm = fun x => x + 1 := by
    funext x
    simp only [Function.comp_apply, hcycle, Equiv.apply_symm_apply]
  have hr := disagreement_conjugate_card (f : BitVec n → BitVec n)
    (g : BitVec n → BitVec n) e
  rw [hcounter] at hr
  let conjugate := e.permCongrHom f
  obtain ⟨middle, hm, hs⟩ := sparse_counter_variable_time conjugate m
  change middle.size ≤ 1000 * (n + 3) *
    ((disagreement (e ∘ f ∘ e.symm) (fun x => x + 1)).card + m + 1) at hs
  rw [hr] at hs
  let x := fun z : BitString (n + m) => fun i : Fin n => z (Fin.castAdd m i)
  let bits := fun z : BitString (n + m) => fun j : Fin m => z (Fin.natAdd n j)
  let encoded := fun z => encode.eval Boolean.interpretation (x z)
  have henc := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (n + m))
    encode (fun i z => x z i) (fun _ => ⟨_, rfl⟩)
  let s1 := inputs (n + m) ∪ wires encoded
  let args := fun z => Fin.append (encoded z) (bits z)
  have hargs (i : Fin (n + m)) : (fun z => args z i) ∈ s1 := by
    induction i using Fin.addCases with
    | left i =>
      apply Or.inr
      exact ⟨i, by simp only [args, Fin.append_left]⟩
    | right i =>
      apply Or.inl
      exact ⟨_, by simp only [args, Fin.append_right]; rfl⟩
  let mid := fun z => middle.eval Boolean.interpretation (args z)
  have hmid := Synthesis.circuit (I := Boolean.interpretation) (s := s1)
    middle (fun i z => args z i) hargs
  have hdec := Synthesis.circuit (I := Boolean.interpretation) (s := s1 ∪ wires mid)
    decode (fun i z => mid z i) (fun i => Or.inr ⟨i, rfl⟩)
  obtain ⟨out, hout, ho⟩ := (henc.trans (hmid.trans hdec)).exists_circuit_outputs
  have hconj : Function.Semiconj (e : BitVec n → BitVec n) f conjugate := by
    intro x
    simp only [conjugate, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  refine ⟨out, ?_, by lia⟩
  intro z
  rw [hout z]
  change decode.eval Boolean.interpretation (mid z) = _
  rw [hd (mid z)]
  dsimp only [mid]
  rw [hm (args z)]
  simp only [args, Fin.append_left, Fin.append_right, word_getLsbD]
  change (fun i : Fin n => (e.symm (conjugate^[(word (bits z)).toNat]
    (word (encode.eval Boolean.interpretation (x z))))).getLsbD i.val) = _
  rw [he (x z), word_getLsbD, ← hconj.iterate_right ((word (bits z)).toNat) (word (x z)),
    Equiv.symm_apply_apply]

end Cslib.Circuits.Boolean.Iteration

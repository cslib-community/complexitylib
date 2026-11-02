/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.RankDecoder
public import Complexity.Computability.GenericRAM.Native.ExpTimePolySpace.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision

/-!
# Native realization of the integer-rank decoder

The decoder retains its original input, its selected prefix, and a residual rank. Each round
queries one left-child mass, appends one bit, and possibly subtracts the mass from the rank.
The residual rank never increases. Polynomially many rounds therefore keep polynomial workspace
and the oracle's common exponential time factor in the original input.

The resource theorem does not require nonnegative-real probabilities, additivity of masses, or a
valid initial rank. Those are separate hypotheses of the distribution theorems in `RankDecoder`.

## Main definitions

* `Cslib.BitString.RankDecoder.State`: the retained input, prefix and residual rank.
* `Cslib.BitString.RankDecoder.nativeCertificate`: a native machine for the deterministic decoder.

## Main results

* `Cslib.BitString.RankDecoder.iterate_step_prefix`: the native loop agrees with `decode`.
* `Cslib.BitString.RankDecoder.nativeCertificate_expTimePolySpace`: polynomially many adaptive
  mass queries preserve their common exponential factor and polynomial workspace.
-/

public section

namespace Cslib.BitString.RankDecoder

open Turing.MultiTapeTM Cslib.GenericRAM

variable {α : Type}

/-- The original input is retained alongside the selected prefix and residual rank. -/
abbrev State (α : Type) := α × (List Bool × ℕ)

/-- The input retained throughout the decoder loop. -/
abbrev State.input (s : State α) : α := s.1

/-- The output prefix selected so far. -/
abbrev State.prefix (s : State α) : List Bool := s.2.1

/-- The residual integer rank within the selected subtree. -/
abbrev State.rank (s : State α) : ℕ := s.2.2

/-- A framed input, followed by the raw prefix and binary residual rank. -/
@[expose] def stateEncoding (enc : α ↪ List Bool) : State α ↪ List Bool :=
  encPair enc (encPair encBits encNat)

/-- One binary split, with an unchanged state once the requested output length is reached. -/
@[expose] def step (mass : α → List Bool → ℕ) (depth : α → ℕ) (s : State α) : State α :=
  let (a, pre, rank) := s
  if pre.length < depth a then
    let left := mass a (pre ++ [false])
    if rank < left then (a, pre ++ [false], rank)
    else (a, pre ++ [true], rank - left)
  else s

@[simp] theorem step_input (mass : α → List Bool → ℕ) (depth : α → ℕ) (s : State α) :
    (step mass depth s).input = s.input := by
  simp only [step]
  split_ifs <;> rfl

/-- A residual rank cannot increase, including when the initial rank is invalid. -/
theorem step_rank_le (mass : α → List Bool → ℕ) (depth : α → ℕ) (s : State α) :
    (step mass depth s).rank ≤ s.rank := by
  simp only [State.rank, step]
  split_ifs <;> simp only [Nat.sub_le, le_refl]

@[simp] theorem iterate_step_input (mass : α → List Bool → ℕ) (depth : α → ℕ)
    (n : ℕ) (s : State α) : ((step mass depth)^[n] s).input = s.input := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', step_input, ih]

/-- The prefix accumulated by the loop is the recursive decoder's output, appended to the
initial prefix. The depth condition guarantees that each requested split is active. -/
theorem iterate_step_prefix (mass : α → List Bool → ℕ) (depth : α → ℕ)
    (a : α) (pre : List Bool) (rank n : ℕ) (hn : pre.length + n ≤ depth a) :
    ((step mass depth)^[n] (a, pre, rank)).prefix = pre ++ decode (mass a) n pre rank := by
  induction n generalizing pre rank with
  | zero => simp [decode]
  | succ n ih =>
    have hactive : pre.length < depth a := by omega
    have hstep : step mass depth (a, pre, rank) =
        if rank < mass a (pre ++ [false]) then (a, pre ++ [false], rank)
        else (a, pre ++ [true], rank - mass a (pre ++ [false])) := by
      simp only [step, hactive, ite_true]
    rw [Function.iterate_succ_apply, hstep]
    simp only [decode]
    split_ifs
    · rw [ih (pre ++ [false]) rank (by
        simp only [List.length_append, List.length_singleton]
        omega)]
      simp only [List.append_assoc, List.singleton_append]
    · rw [ih (pre ++ [true]) (rank - mass a (pre ++ [false])) (by
        simp only [List.length_append, List.length_singleton]
        omega)]
      simp only [List.append_assoc, List.singleton_append]

private theorem state_length_step_le (enc : α ↪ List Bool) (mass : α → List Bool → ℕ)
    (depth : α → ℕ) (s : State α) :
    (stateEncoding enc (step mass depth s)).length ≤ (stateEncoding enc s).length + 2 := by
  rcases s with ⟨a, pre, rank⟩
  have hsub : (encNat (rank - mass a (pre ++ [false]))).length ≤ (encNat rank).length := by
    simpa [Nat.size_eq_bits_len] using
      Nat.size_le_size (Nat.sub_le rank (mass a (pre ++ [false])))
  simp only [step]
  split_ifs <;>
    simp only [stateEncoding, length_encPair, encBits_apply,
      List.length_append, List.length_singleton] <;> omega

private theorem state_length_iterate_le (enc : α ↪ List Bool) (mass : α → List Bool → ℕ)
    (depth : α → ℕ) (n : ℕ) (s : State α) :
    (stateEncoding enc ((step mass depth)^[n] s)).length ≤
      (stateEncoding enc s).length + 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hstep := state_length_step_le enc mass depth ((step mass depth)^[n] s)
    omega

private def finish (depth : α → ℕ) (p : State α × ℕ) : State α :=
  if p.1.2.1.length < depth p.1.1 then
    if p.1.2.2 < p.2 then (p.1.1, p.1.2.1 ++ [false], p.1.2.2)
    else (p.1.1, p.1.2.1 ++ [true], p.1.2.2 - p.2)
  else p.1

private theorem length_polyTime : ComputableInPolyTime List.length encBits encNat :=
  ComputableInO.lengthNat.computableInPolyTime
    (PolyBounded.of_forall_le 1 2 fun _ => by simp)
    (PolyBounded.of_forall_le 1 1 fun _ => by simp)

private theorem finish_polyTime {enc : α ↪ List Bool} {depth : α → ℕ}
    (hd : ComputableInPolyTime depth enc encNat) :
    ComputableInPolyTime (finish depth) (encPair (stateEncoding enc) encNat)
      (stateEncoding enc) := by
  open ComputableInPolyTime in
    have hstate := fst (stateEncoding enc) encNat
    have hinput := hstate.fst'
    have hprefix := hstate.snd'.fst'
    have hrank := hstate.snd'.snd'
    have hleft := snd (stateEncoding enc) encNat
    have hfalse := hinput.prod ((bitsAppend hprefix (const [false])).prod hrank)
    have htrue := hinput.prod ((bitsAppend hprefix (const [true])).prod
      (binary_sub.comp (hrank.prod hleft)))
    have hsplit := (binary_lt.comp (hrank.prod hleft)).ite hfalse htrue
    have hactive := binary_lt.comp ((length_polyTime.comp hprefix).prod (hd.comp hinput))
    refine (hactive.ite hsplit hstate).of_enc_eq fun p => ?_
    simp only [finish, stateEncoding, Function.comp_def, decide_eq_true_eq]

private theorem initial_polyTime {enc : α ↪ List Bool} {rank : α → ℕ}
    (hr : ComputableInPolyTime rank enc encNat) :
    ComputableInPolyTime (fun a => (a, ([] : List Bool), rank a)) enc (stateEncoding enc) :=
  ComputableInPolyTime.id'.prod ((ComputableInPolyTime.const []).prod hr)

private noncomputable def stepCertificate {enc : α ↪ List Bool}
    {mass : α → List Bool → ℕ} {depth : α → ℕ}
    (hd : ComputableInPolyTime depth enc encNat)
    (cm : NativeCertificate (fun s : State α => mass s.input (s.prefix ++ [false]))
      (stateEncoding enc) encNat) :
    NativeCertificate (step mass depth) (stateEncoding enc) (stateEncoding enc) :=
  ((NativeCertificate.ofPolyTime (finish_polyTime hd)).comp
    ((NativeCertificate.ofPolyTime ComputableInPolyTime.id').prod cm))

private theorem stepCertificate_expTimePolySpace {enc : α ↪ List Bool}
    {mass : α → List Bool → ℕ} {depth E : α → ℕ}
    (hd : ComputableInPolyTime depth enc encNat)
    (cm : NativeCertificate (fun s : State α => mass s.input (s.prefix ++ [false]))
      (stateEncoding enc) encNat)
    (hm : cm.ExpTimePolySpace (fun s => E s.input)) :
    (stepCertificate hd cm).ExpTimePolySpace (fun s => E s.input) := by
  have hp := (NativeCertificate.expTimePolySpace_ofPolyTime
    (ComputableInPolyTime.id' (encIn := stateEncoding enc)) (fun _ => 0)).prod hm
  have hf := hp.comp_ofPolyTime (finish_polyTime hd)
  simpa only [NativeCertificate.ExpTimePolySpace, stepCertificate, Nat.zero_add] using hf

/-- A native realization of the decoder, using one supplied left-child mass computation in each
of `depth a` rounds. The oracle receives the retained input, current prefix and residual rank. -/
noncomputable def nativeCertificate {enc : α ↪ List Bool}
    {mass : α → List Bool → ℕ} {depth rank : α → ℕ}
    (hd : ComputableInPolyTime depth enc encNat)
    (hr : ComputableInPolyTime rank enc encNat)
    (cm : NativeCertificate (fun s : State α => mass s.input (s.prefix ++ [false]))
      (stateEncoding enc) encNat) :
    NativeCertificate (fun a => decode (mass a) (depth a) [] (rank a)) enc encBits :=
  (((NativeCertificate.iterate (NativeCertificate.ofPolyTime hd)
    (NativeCertificate.ofPolyTime (initial_polyTime hr)) (stepCertificate hd cm)).snd).fst).congr
    fun a => by simpa only [List.nil_append] using
      iterate_step_prefix mass depth a [] (rank a) (depth a) (by simp)

/-- Polynomially many adaptive prefix queries preserve the oracle's exponential time factor in
the original input and polynomial workspace. The initial rank may be exponentially large: only
its polynomial-time binary production is required. No mass law or rank-validity premise is used. -/
theorem nativeCertificate_expTimePolySpace {enc : α ↪ List Bool}
    {mass : α → List Bool → ℕ} {depth rank E : α → ℕ}
    (hd : ComputableInPolyTime depth enc encNat)
    (hr : ComputableInPolyTime rank enc encNat)
    (cm : NativeCertificate (fun s : State α => mass s.input (s.prefix ++ [false]))
      (stateEncoding enc) encNat)
    (hdepth : PolyBounded (fun a => (enc a).length) depth)
    (hm : cm.ExpTimePolySpace (fun s => E s.input)) :
    (nativeCertificate hd hr cm).ExpTimePolySpace E := by
  obtain ⟨C, d, hround⟩ := stepCertificate_expTimePolySpace hd cm hm
  let B a := (stateEncoding enc (a, ([] : List Bool), rank a)).length + 2 * depth a
  have hB : PolyBounded (fun a => (enc a).length) B :=
    (initial_polyTime hr).polyBounded_length.add ((PolyBounded.const 2).mul hdepth)
  have hfactor : PolyBounded (fun a => (enc a).length) (fun a => C * (B a + 1) ^ d) :=
    (PolyBounded.const C).mul ((hB.add (.const 1)).pow d)
  have hstate (a : α) (j : ℕ) (hj : j ≤ depth a) :
      (stateEncoding enc ((step mass depth)^[j] (a, [], rank a))).length ≤ B a :=
    (state_length_iterate_le enc mass depth j (a, [], rank a)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hj) _)
  have hloop := NativeCertificate.ExpTimePolySpace.iterate_of_bounds
    (NativeCertificate.ofPolyTime hd) (NativeCertificate.ofPolyTime (initial_polyTime hr))
    (stepCertificate hd cm) (NativeCertificate.ofPolyTime_isPolynomial hd)
    (NativeCertificate.ofPolyTime_isPolynomial (initial_polyTime hr))
    hdepth hfactor hfactor hB
    (R := fun a => C * (B a + 1) ^ d) (Q := fun a => C * (B a + 1) ^ d)
    (E := E)
    (fun a j hj => by
      have h := (hround ((step mass depth)^[j] (a, [], rank a))).1
      simp only [iterate_step_input] at h
      calc _ ≤ C * 2 ^ E a *
            ((stateEncoding enc ((step mass depth)^[j] (a, [], rank a))).length + 1) ^ d := h
        _ ≤ C * 2 ^ E a * (B a + 1) ^ d :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a j hj) 1) d)
        _ = _ := by ring)
    (fun a j hj => (hround ((step mass depth)^[j] (a, [], rank a))).2.trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a j hj) 1) d)))
    hstate
  exact hloop

end Cslib.BitString.RankDecoder

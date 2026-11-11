/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.StreamingEmitWidth
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Containers
import all CslibFrontier.Computability.GenericRAM.Native.StreamingEmit
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Streaming numeric indices on binary counters

One fixed machine retains only the binary position, emits a key/counter pair,
then increments. The actual unconsumed list and emitted output never enter its
callback state. Bounds include the index bits, counters and materialized output.

## Main definitions

* `run`: restore numeric keys while preserving counter positions and multiplicity.
* `width`: maximum counter wire, final index wire and framing.

## Main results

* `run_ofFn`: exact numeric-key restoration on complete tables.
* `run_computable`: one native writer with linear record-count/per-width resources.
-/

public section
namespace Turing.MultiTapeTM.IndexNat
open Cslib.GenericRAM

/-- Zero-based numeric keys, preserving every counter and its position. -/
def run (rows : List ℕ) : List (ℕ × ℕ) := rows.zipIdx.map Prod.swap

private def next (i : ℕ) (_ : ℕ) : ℕ := i+1
private def emit (i n : ℕ) : List (ℕ × ℕ) := [(i, n)]

private theorem emitted (rows : List ℕ) (k : ℕ) :
    NativeCertificate.emitFold next emit k rows = (rows.zipIdx k).map Prod.swap := by
  induction rows generalizing k with
  | nil => rfl
  | cons n rows ih => simpa only [NativeCertificate.emitFold, emit, next, List.zipIdx_cons,
      List.map_cons, List.singleton_append, Prod.swap] using congrArg ((k, n) :: ·) (ih (k+1))

/-- Reconstruct the original numeric state order without a supplied indexing conclusion. -/
theorem run_ofFn {n : ℕ} (f : Fin n → ℕ) :
    run (List.ofFn f) = List.ofFn (fun i => (i.val, f i)) := by
  apply List.ext_getElem
  · simp [run]
  · intro i hi hj
    simp [run]

/-- Binary counter width plus the final binary index and one for empty lists. -/
def width (rows : List ℕ) : ℕ :=
  streamRecordLength encNat rows+(encNat rows.length).length+1

private def inputWidth (input : ℕ × List ℕ) : ℕ :=
  let (k, rows) := input
  streamRecordLength encNat rows+(encNat (k+rows.length)).length+1

private theorem state_bound (input : ℕ × List ℕ) (j : ℕ) (hj : j ≤ input.2.length) :
    (encNat (streamState input.1 (fun q => next q.1 q.2) input.2 j)).length ≤ inputWidth input := by
  have value : streamState input.1 (fun q => next q.1 q.2) input.2 j = input.1+j := by
    simp only [streamState, next, List.foldl_add_const, List.length_take, Nat.min_eq_left hj,
      Nat.one_mul]
  rw [value]
  have h := length_encNat_mono (Nat.add_le_add_left hj input.1)
  dsimp only [inputWidth]
  omega

private theorem emit_polyTime : ComputableInPolyTime (fun q : ℕ × ℕ => emit q.1 q.2)
    (encPair encNat encNat) encNatPairList := by
  exact .of_tidy (.of_linear (.of_frame (fun _ => by simp [emit])))

/-- Uniform numeric indexing with a linear record-count factor and a polynomial only in
counter/index width. Initialization, every prefix index, input and output are charged. -/
theorem run_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO run (encList encNat) encNatPairList
      (fun rows => (rows.length + 1) * P (width rows))
      (fun rows => (rows.length + 1) * P (width rows)) := by
  have hn : ComputableInPolyTime (fun q : ℕ × ℕ => next q.1 q.2)
      (encPair encNat encNat) encNat := by unfold next; fun_prop
  let V := fun b => 10*b+10
  have hv : Cslib.PolynomiallyBounded V := by dsimp only [V]; fun_prop
  have mv : Monotone V := by intro a b h; dsimp only [V]; omega
  have rowBound (input : ℕ × List ℕ) (n : ℕ) (hn : n ∈ input.2) :
      (encNat n).length ≤ inputWidth input := by
    have := le_listMax (f := fun n => (encNat n).length) hn
    change (encNat n).length ≤ streamRecordLength encNat input.2 at this
    dsimp only [inputWidth]
    omega
  have out (input : ℕ × List ℕ) :
      (encNatPairList (NativeCertificate.emitFold next emit input.1 input.2)).length ≤
        (input.2.length+1)*V (inputWidth input) := by
    rw [emitted]
    apply (length_encList_le (encPair encNat encNat) _ (b := 3*inputWidth input+1) ?_).trans
    · simp only [List.length_map, List.length_zipIdx]
      dsimp only [V]
      nlinarith
    · intro r hr
      obtain ⟨⟨value, index⟩, hi, rfl⟩ := List.mem_map.mp hr
      have bound := List.snd_lt_add_of_mem_zipIdx hi
      have hn := rowBound input value (List.fst_mem_of_mem_zipIdx hi)
      have hk := length_encNat_mono (by omega : index ≤ input.1+input.2.length)
      simp only [Prod.swap, length_encPair]
      dsimp only [inputWidth] at *
      omega
  obtain ⟨P, hp, mp, machine⟩ := NativeCertificate.emitFold_width encNat encNat
    (encPair encNat encNat) next emit hn emit_polyTime inputWidth V hv mv state_bound
    rowBound (fun input => by
      have state := state_bound input 0 (Nat.zero_le _)
      have rows := length_encList_le encNat input.2 (rowBound input)
      simp only [streamState, List.take_zero, List.foldl_nil] at state
      rw [length_encPair]
      dsimp only [V]
      nlinarith) out
  have prepare := (ComputableInO.const (encIn := encList encNat) (encMid := encNat) 0).prod
    (ComputableInO.id' (encMid := encList encNat))
  have actual := (machine.comp prepare).of_enc_eq (g := run) (encC := encNatPairList)
    (fun rows => by simp only [Function.comp_def, emitted, run])
  let Q := fun b => P b+10*b+10
  refine ⟨Q, by dsimp only [Q]; fun_prop, ?_, actual.mono_le (fun rows => ?_) (fun rows => ?_)⟩
  · intro a b hab
    have := mp hab
    dsimp only [Q]
    omega
  all_goals
    have wire := length_encList_le encNat rows
      (fun n hn => le_listMax (f := fun n => (encNat n).length) hn)
    change (encList encNat rows).length ≤ rows.length*(2*streamRecordLength encNat rows+1) at wire
    dsimp only [Q, inputWidth, width]
    simp only [Nat.zero_add]
    nlinarith

end Turing.MultiTapeTM.IndexNat

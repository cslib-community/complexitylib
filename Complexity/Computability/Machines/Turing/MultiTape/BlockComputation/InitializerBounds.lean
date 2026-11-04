/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitializerCorrect
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Space for streamed runtime initialization

Every allocation clock retains one metadata record, a prefix of the padded bank and the
growing assignment capacity. A uniform bound is linear in the number of field cells and
their binary width, including the capacity accumulated by repeated multiplication.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Initializer

open MultiTapeTM
open Cslib.TreeEval.Ary.Packed

/-- Metadata plus a constant number of bank-width allocations pays every initializer state. -/
@[expose] noncomputable def space (k : ℕ) (metadata : Metadata) : ℕ :=
  let (_, (_, _, alphabet, p)) := metadata
  16 * ((encMetadata metadata).length + 1) +
    16 * bankCells k metadata * ((encNat p).length + (encNat alphabet).length + 1)

/-- The power accumulator and allocated list fit the same bank-width budget at every prefix. -/
theorem prefixState_encoding_le (k : ℕ) (metadata : Metadata) (j : ℕ)
    (hj : j ≤ bankCells k metadata) :
    (encState (prefixState k metadata j)).length ≤ space k metadata := by
  rcases metadata with ⟨args, m, r, alphabet, p⟩
  dsimp only [bankCells] at hj
  have hcursor := length_encNat_le_self j
  have hlist := length_encList_le encNat (List.replicate j p)
    (b := (encNat p).length) (by
      intro value hvalue
      have he : value = p := List.eq_of_mem_replicate hvalue
      subst value
      exact le_rfl)
  simp only [List.length_replicate] at hlist
  have hbank := hlist.trans (Nat.mul_le_mul_right (2 * (encNat p).length + 1) hj)
  have hpower := Nat.size_pow_le alphabet (min j ((k * 3 + 1) * r))
  have hmul := Nat.mul_le_mul_right alphabet.size
    ((Nat.min_le_left j ((k * 3 + 1) * r)).trans hj)
  simp only [prefixState, encState, length_encPair, space, bankCells,
    length_encNat_eq_size]
  simp only [length_encNat_eq_size] at hcursor hbank
  nlinarith

/-- All actual physical allocation clocks obey one explicit state bound. -/
theorem length_runFrom_le (k : ℕ) (metadata : Metadata) (w : List Bool)
    (j : ℕ) (hj : j ≤ bankCells k metadata) :
    (encState ((machine k).runFrom w (metadata, 0, [], 1) j)).length ≤ space k metadata := by
  rw [runFrom_prefix k metadata w j hj]
  exact prefixState_encoding_le k metadata j hj

/-- In particular, the runtime-selected initialization has a bound through its final clock. -/
theorem length_runFrom_prepare_le (k s : ℕ) (args : Args) (w : List Bool)
    (j : ℕ) (hj : j ≤ bankCells k ((prepare k s args).1)) :
    (encState ((machine k).runFrom w (prepare k s args) j)).length ≤
      space k ((prepare k s args).1) :=
  length_runFrom_le k ((prepare k s args).1) w j hj

/-- Selected initialization uses linear value-width storage, apart from its retained metadata. -/
theorem space_prepare_le (k s N b σ q : ℕ) :
    let d := k * 3 + 1
    let B := Encoding.width k s b
    space k ((prepare k s (N, b, σ, q)).1) ≤
      16 * ((encMetadata ((prepare k s (N, b, σ, q)).1)).length + 1) +
        192 * (d + 1) * (2 * B + d.size) := by
  let d := k * 3 + 1
  let B := Encoding.width k s b
  have hd : 0 < d := by omega
  have hB : 0 < B := Encoding.width_pos k s b
  have ha := length_encNat_mono (alphabetSize_lt hd hB).le
  have hp : 1 ≤ (fieldModulus d B).size :=
    Nat.size_pos.mpr (fieldModulus_prime d B).pos
  rw [length_encNat_eq_size, length_encNat_eq_size] at ha
  have hregister := chunkCount_mul_fieldModulus_size_le hd hB
  have hcells : chunkCount d B *
      ((fieldModulus d B).size + (2 ^ chunkWidth d B).size + 1) ≤
      12 * (B + chunkWidth d B) := by
    calc
      _ ≤ chunkCount d B * (3 * (fieldModulus d B).size) :=
        Nat.mul_le_mul_left _ (by omega)
      _ ≤ 12 * (B + chunkWidth d B) := by nlinarith
  have hm := chunkWidth_le d B
  have hwidth : B + chunkWidth d B ≤ 2 * B + d.size := by omega
  have htotal := Nat.mul_le_mul_left (16 * (d + 1)) hcells
  have hfinal := Nat.mul_le_mul_left (192 * (d + 1)) hwidth
  simp only [space, prepare, parameters, bankCells, length_encNat_eq_size]
  dsimp only [d, B] at htotal hfinal
  nlinarith

end Turing.MultiTapePTM.BlockComputation.Initializer

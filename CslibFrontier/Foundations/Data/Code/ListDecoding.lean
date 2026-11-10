/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Hamming

/-!
# List decoding

A *list code* encodes messages of a type `α` as words `ι → β` over an alphabet `β`, and its list
decoder turns every received word `w` into `L` candidate messages. The code *list decodes up to
radius `ρ`* if the candidates for `w` include every message whose codeword differs from `w` on at
most a `ρ` fraction of the coordinates [Arora and Barak, Chapter 19][AroraBarak09]; binary codes
are those with `β = Bool`. A word that agrees with the codeword of `x` on a `1 / 2 + δ` fraction of
the coordinates thus determines `x` up to `L` possibilities when the code list decodes up to radius
`1 / 2 - δ` (`Cslib.ListCode.ListDecodes.mem_candidates_of_half_add_le`): `x` is one of the at
most `L` candidates (`Cslib.ListCode.card_candidates_le`), and it is named by an index of
`⌈log₂ L⌉` bits (`Cslib.ListCode.ListDecodes.exists_decodeBits_eq_some`). This is how the
Nisan–Wigderson reconstruction recovers a message from a predictor of its codeword.

## Main definitions

* `Cslib.ListCode`: an encoder of messages as words over an alphabet with a list decoder.
* `Cslib.ListCode.ListDecodes`: list decoding up to a relative radius.
* `Cslib.ListCode.candidates`: the candidates for a received word.
* `Cslib.ListCode.decodeBits`: the candidate named by a binary index.

## Main results

* `Cslib.ListCode.card_candidates_le`: there are at most `L` candidates.
* `Cslib.ListCode.listDecodes_of_surjective`: a decoder listing every message list decodes at
  every radius.
* `Cslib.ListCode.ListDecodes.exists_decode_eq`,
  `Cslib.ListCode.ListDecodes.exists_decode_eq_of_half_add_le`: a message whose codeword
  agrees with the received word on enough coordinates is a candidate.
* `Cslib.ListCode.ListDecodes.exists_decodeBits_eq_some`: it is named by an index of
  `Nat.clog 2 L` bits.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib

open Finset

/-- A *list code*: an encoder of messages of type `α` as words on the coordinates `ι` over the
alphabet `β`, with a list decoder returning `L` candidate messages for every received word. -/
structure ListCode (α ι β : Type*) (L : ℕ) where
  /-- The codeword of a message. -/
  encode : α → ι → β
  /-- The `k`-th candidate message for a received word. -/
  decode : (ι → β) → Fin L → α

namespace ListCode

variable {α ι β : Type*} {L : ℕ} (C : ListCode α ι β L)

/-- The code *list decodes up to radius `ρ`*: the candidates for a received word `w` include every
message whose codeword differs from `w` on at most a `ρ` fraction of the coordinates. -/
def ListDecodes [Fintype ι] [DecidableEq β] (ρ : ℝ) : Prop :=
  ∀ x w, (hammingDist (C.encode x) w : ℝ) ≤ ρ * Fintype.card ι → ∃ k, C.decode w k = x

/-- The candidates for the received word `w`, without repetitions. -/
def candidates [DecidableEq α] (w : ι → β) : Finset α :=
  univ.image (C.decode w)

/-- A message is a candidate for `w` exactly when the decoder returns it at some index. -/
@[simp]
theorem mem_candidates [DecidableEq α] {w : ι → β} {x : α} :
    x ∈ C.candidates w ↔ ∃ k, C.decode w k = x := by
  simp [candidates]

/-- **List size.** A received word has at most `L` candidates. -/
theorem card_candidates_le [DecidableEq α] (w : ι → β) : #(C.candidates w) ≤ L :=
  card_image_le.trans_eq (card_fin L)

/-- The candidate named by the binary index `b` of `Nat.clog 2 L` bits, read least significant bit
first: the `k`-th candidate for `w` if `b` spells a number `k < L`, and nothing otherwise. -/
def decodeBits (w : ι → β) (b : BitString (Nat.clog 2 L)) : Option α :=
  let k : Fin (2 ^ Nat.clog 2 L) := BitString.equivFin (Nat.clog 2 L) b
  if h : (k : ℕ) < L then some (C.decode w ⟨k, h⟩) else none

/-- **Short index.** Every candidate is named by an index of `Nat.clog 2 L` bits. -/
theorem exists_decodeBits_eq_some {w : ι → β} {x : α} (h : ∃ k, C.decode w k = x) :
    ∃ b : BitString (Nat.clog 2 L), C.decodeBits w b = some x := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨BitString.indexBits k, ?_⟩
  simp only [decodeBits, BitString.indexBits, Equiv.apply_symm_apply, Fin.val_castLE, k.isLt,
    ↓reduceDIte]

variable [Fintype ι] [DecidableEq β] {C}

/-- A decoder whose candidates enumerate all messages, whatever the received word, list decodes at
every radius: the list then has `L ≥ |α|` entries, so this only shows that list decoding is
satisfiable. -/
theorem listDecodes_of_surjective (h : ∀ w, Function.Surjective (C.decode w)) (ρ : ℝ) :
    C.ListDecodes ρ :=
  fun x w _ => h w x

/-- A list decoder up to radius `ρ` lists every message whose codeword agrees with the received
word on at least a `1 - ρ` fraction of the coordinates. -/
theorem ListDecodes.exists_decode_eq {ρ : ℝ} (hC : C.ListDecodes ρ) {x : α} {w : ι → β}
    (h : 1 - ρ ≤ (dens {i | C.encode x i = w i} : ℝ)) : ∃ k, C.decode w k = x := by
  refine hC x w ?_
  rw [hammingDist_eq_card_mul_one_sub_dens (𝕜 := ℝ), mul_comm]
  gcongr
  linarith

/-- A list decoder up to radius `1 / 2 - δ` lists every message whose codeword agrees with the
received word on at least a `1 / 2 + δ` fraction of the coordinates. -/
theorem ListDecodes.exists_decode_eq_of_half_add_le {δ : ℝ} (hC : C.ListDecodes (1 / 2 - δ))
    {x : α} {w : ι → β} (h : 1 / 2 + δ ≤ (dens {i | C.encode x i = w i} : ℝ)) :
    ∃ k, C.decode w k = x :=
  hC.exists_decode_eq (by linarith)

/-- A message whose codeword agrees with the received word on at least a `1 / 2 + δ` fraction of
the coordinates is among the candidates of a list decoder up to radius `1 / 2 - δ`. -/
theorem ListDecodes.mem_candidates_of_half_add_le [DecidableEq α] {δ : ℝ}
    (hC : C.ListDecodes (1 / 2 - δ)) {x : α} {w : ι → β}
    (h : 1 / 2 + δ ≤ (dens {i | C.encode x i = w i} : ℝ)) : x ∈ C.candidates w :=
  C.mem_candidates.mpr (hC.exists_decode_eq_of_half_add_le h)

/-- **Short index.** If a code list decodes up to radius `1 / 2 - δ`, a received word that agrees
with the codeword of `x` on at least a `1 / 2 + δ` fraction of the coordinates, together with an
index of `Nat.clog 2 L` bits, determines `x`. -/
theorem ListDecodes.exists_decodeBits_eq_some {δ : ℝ} (hC : C.ListDecodes (1 / 2 - δ)) {x : α}
    {w : ι → β} (h : 1 / 2 + δ ≤ (dens {i | C.encode x i = w i} : ℝ)) :
    ∃ b : BitString (Nat.clog 2 L), C.decodeBits w b = some x :=
  C.exists_decodeBits_eq_some (hC.exists_decode_eq_of_half_add_le h)

end ListCode

end Cslib

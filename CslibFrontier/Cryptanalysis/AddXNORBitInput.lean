/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeGlobalLayout
public import CslibFrontier.Computability.WordRAM.Turing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import all CslibFrontier.Cryptanalysis.AddXNORNativeGlobalLayout

/-!
# Encoded original operands and charged native input preparation

The input is four framed lists of binary natural words, in original chain order.
An actual multitape computation reverses the suffix and builds the finite sparse
initial memory used by the native dissection. Reversal and materialization are
charged polynomial bit computations, not semantic initialization assumptions.

This is a representation bridge toward the deterministic multitape convention
of [WangLvShenZhang2027], PDF p. 6. It does not establish the sorted-list resource
bounds of Lemma 8/Theorem 7, pp. 21–22, or generate the native scalar parameters
and program from an input header.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.BitInput

open Turing.MultiTapeTM Cslib.WordRAM Cslib.GenericRAM

/-- Original-order quarters, before any reversal or projection. -/
abbrev Words := (List ℕ × List ℕ) × (List ℕ × List ℕ)

/-- Explicit quarter boundaries, with the ordinary framed binary natural encoding. -/
abbrev encoding : Words ↪ List Bool :=
  encPair (encPair (encList encNat) (encList encNat))
    (encPair (encList encNat) (encList encNat))

/-- The representation of actual original full-width operands. -/
def words {m : ℕ} (as bs cs ds : List (BitVec m)) : Words :=
  ((as.map BitVec.toNat, bs.map BitVec.toNat),
    (cs.map BitVec.toNat, ds.map BitVec.toNat))

/-- The native calling convention reverses the entire second half of the chain. -/
def prepare (xs : Words) : List ℕ :=
  xs.1.1 ++ (xs.1.2 ++ (xs.2.2.reverse ++ xs.2.1.reverse))

/-- The computed operand list is exactly the reviewed native input, including inverse order. -/
theorem prepare_words {m : ℕ} (as bs cs ds : List (BitVec m)) :
    prepare (words as bs cs ds) = Native.Driver.quarterInput as bs cs ds := by
  simp [prepare, words, Native.Driver.quarterInput, List.map_reverse]

/-- Input framing charges every original word and all four quarter boundaries. -/
theorem encoding_length (xs : Words) :
    (encoding xs).length =
      4 * (encList encNat xs.1.1).length + 2 * (encList encNat xs.1.2).length +
        2 * (encList encNat xs.2.1).length + (encList encNat xs.2.2).length + 4 := by
  simp only [encoding, length_encPair]
  omega

/-- Physical input size in the original operand count and full state width, including
all framing. Small values may use fewer bits; zero operands are retained as list elements. -/
theorem encoding_words_le {m : ℕ} (as bs cs ds : List (BitVec m)) :
    (encoding (words as bs cs ds)).length ≤
      4 * (as.length + bs.length + cs.length + ds.length) * (2 * m + 1) + 4 := by
  have bound (xs : List (BitVec m)) :
      (encList encNat (xs.map BitVec.toNat)).length ≤ xs.length * (2 * m + 1) := by
    simpa only [List.length_map] using
      length_encList_le encNat (xs.map BitVec.toNat) (fun v hv => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
        exact length_encNat_le_of_lt_two_pow x.isLt)
  have ha := bound as
  have hb := bound bs
  have hc := bound cs
  have hd := bound ds
  rw [encoding_length]
  dsimp only [words]
  nlinarith

/-- Reversal and concatenation preserve the total framed operand length. -/
theorem prepare_length (xs : Words) :
    (encList encNat (prepare xs)).length =
      (encList encNat xs.1.1).length + (encList encNat xs.1.2).length +
        (encList encNat xs.2.1).length + (encList encNat xs.2.2).length := by
  simp [prepare, length_encList, List.map_reverse, List.sum_reverse]
  omega

/-- The input conversion is an actual uniform bit-machine computation on all word lists. -/
theorem prepare_polyTime :
    ComputableInPolyTime prepare encoding (encList encNat) := by
  unfold prepare
  fun_prop

/-- Charged input preparation, including all encoded intermediate data. -/
noncomputable def prepareCertificate : NativeCertificate prepare encoding (encList encNat) :=
  .ofPolyTime prepare_polyTime

/-- No efficiency or simulation premise is needed for the input preparation bound. -/
theorem prepareCertificate_isPolynomial : prepareCertificate.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial prepare_polyTime

/-- The actual finite initial state, with zero registers/default and a stored length header. -/
def initial (xs : Words) : FiniteState Basis.standard.genericModel 40 :=
  initState .standard 40 (prepare xs)

/-- Charged source-order conversion and sparse-memory materialization before program execution. -/
noncomputable def initialCertificate : NativeCertificate initial encoding
    (FiniteState.encoding Basis.standard.encoding) :=
  FiniteState.initConstCertificate Basis.standard.encoding
    (NativeCertificate.const 0) (NativeCertificate.const 0)
    ((NativeCertificate.ofPolyTime initMemory_polyTime).comp prepareCertificate)

/-- Input reversal, address enumeration, tuple framing and materialization are polynomial. -/
theorem initialCertificate_isPolynomial : initialCertificate.IsPolynomial :=
  FiniteState.initConstCertificate_isPolynomial _ _ _ _
    (NativeCertificate.const_isPolynomial 0) (NativeCertificate.const_isPolynomial 0)
    (NativeCertificate.comp_isPolynomial _ _
      (NativeCertificate.ofPolyTime_isPolynomial initMemory_polyTime)
      prepareCertificate_isPolynomial)

/-- Materialization stores every input cell, including zeros, and the length header. -/
theorem initial_entries (xs : Words) :
    (SparseMemory.entries (initial xs).memory).length = (prepare xs).length + 1 :=
  length_entries_initState _

/-- Materialized input and the reviewed native initial state have identical semantics. -/
theorem initial_denote {m : ℕ} (as bs cs ds : List (BitVec m)) :
    (initial (words as bs cs ds)).denote =
      (State.init (Native.Driver.quarterInput as bs cs ds)).toGeneric .standard := by
  rw [initial, prepare_words, denote_initState]

end Cslib.Cryptanalysis.AddXNOR.BitInput

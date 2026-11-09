/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Cryptanalysis.AddXNORProgramTemplate
import all CslibFrontier.Cryptanalysis.AddXNORBitInput
import all CslibFrontier.Cryptanalysis.AddXNORBitExecution
import all CslibFrontier.Cryptanalysis.AddXNORNativeGlobalLayout
import all CslibFrontier.Cryptanalysis.AddXNORNativeGlobalTime
import all CslibFrontier.Cryptanalysis.AddXNORNativeDissection
import all CslibFrontier.Cryptanalysis.AddXNORNativeClassCounts

/-!
# Uniform encoded executable, physical width, clock and original-input state

A concrete multitape computation reads the original input and constructs all
inputs to a clocked native simulation: the actual encoded program, its derived
physical width in unary, its finite instruction clock in binary, and initialized
sparse memory. Quarter lengths are computed from the operand arrays. Every stage
has a uniform polynomial bit-time/workspace certificate; in particular the clock
is not materialized in unary and powers of two use binary outputs.

The packet has the exact program/configuration/input semantics of the reviewed
original-input execution. A single bit-machine interpreter consuming its runtime
program is still a separate obligation. No such interpreter or sharp source
sorted-list resource bound is assumed here. See [WangLvShenZhang2027], PDF p. 6
and Lemma 8/Theorem 7, pp. 21–22.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.GeneratedRunInput

open Cslib.WordRAM Cslib.WordRAM.ProgramLiterals
open Cslib.GenericRAM (NativeCertificate FiniteState)
open Turing.MultiTapeTM Native.Driver ProgramTemplate ProgramGeneration

/-- Derived physical word/address capacity and binary instruction clock, including halt. -/
def configuration (h : Metadata) : ℕ × ℕ :=
  (globalWidth (h.1 0) (h.1 1) (h.1 2) (h.1 3) (h.1 4) (h.1 5),
    BitExecution.steps (h.1 1) (h.1 2) (h.1 3) (h.1 4) (h.1 5))

@[instance_reducible] private def templateOfNat {n : ℕ} : OfNat (Expr 6 2) n := ⟨.literal n⟩
@[instance_reducible] private def templateAdd : Add (Expr 6 2) := ⟨.add⟩
@[instance_reducible] private def templateMul : Mul (Expr 6 2) := ⟨.mul⟩
attribute [local instance] templateOfNat templateAdd templateMul

private def size (i : Fin 6) : Expr 6 2 := .unary (.parameter i)
private def power (i : Fin 6) : Expr 6 2 := .powTwo (.parameter i)
private def halfPower (i j : Fin 6) : Expr 6 2 := .powTwo (.add (.parameter i) (.parameter j))
private def q : Expr 6 2 := size 2 + size 3 + size 4 + size 5

private def capacityExpr : Expr 6 2 :=
  1000 * (1 + q + power 1 + power 2 + power 3 + power 4 + power 5 +
    power 0 + halfPower 2 3 + halfPower 4 5)

private def prepareExpr (N a b : Expr 6 2) : Expr 6 2 :=
  (((10 * a + 8) + (6 + (4 * N + a * (14 * N + 14) + 10))) +
    (1 + (((10 * b + 8) + (6 + (4 * N + b * (14 * N + 14) + 10))) + 1))) +
    (14 * N + 11)

private def clockExpr : Expr 6 2 :=
  (prepareExpr (power 1) (size 2 + size 3) (size 4 + size 5) +
    power 1 * (100 * (q + 1) * (power 1 + power 2 + power 3 + power 4 + power 5) + 18) +
    100 * (q + 1) * (halfPower 2 3 + halfPower 4 5) + 7) + (7 * q + 53) + 1

/-- Layout capacity computation uses binary powers with unary size exponents. -/
theorem layoutLimit_polyTime : ComputableInPolyTime
    (fun h : Metadata => layoutLimit (h.1 0) (h.1 1) (h.1 2) (h.1 3) (h.1 4) (h.1 5))
    (ProgramLiterals.encoding 6 2) encNat :=
  capacityExpr.polyTime

/-- The physical word width is actually computed in unary from its binary layout capacity. -/
theorem width_polyTime : ComputableInPolyTime
    (fun h : Metadata => (configuration h).1) (ProgramLiterals.encoding 6 2) encUnary := by
  change ComputableInPolyTime
    (fun h : Metadata => (layoutLimit (h.1 0) (h.1 1) (h.1 2) (h.1 3) (h.1 4) (h.1 5)).log2 + 1)
    _ _
  simp only [Nat.log2_eq_log_two]
  exact ComputableInPolyTime.unary_add.comp
    (((ComputableInPolyTime.binary_log_two).comp layoutLimit_polyTime).prod (.const 1))

/-- The exponential native clock is computed in binary with polynomial metadata bit cost. -/
theorem clock_polyTime : ComputableInPolyTime
    (fun h : Metadata => (configuration h).2) (ProgramLiterals.encoding 6 2) encNat :=
  clockExpr.polyTime

/-- All word-width and clock computation is uniform and charged. -/
noncomputable def configurationCertificate : NativeCertificate configuration
    (ProgramLiterals.encoding 6 2) (encPair encUnary encNat) :=
  .ofPolyTime (width_polyTime.prod clock_polyTime)

/-- The actual simulation packet: executable, physical width/clock and sparse initial state. -/
abbrev Packet := (Program .standard 40 × (ℕ × ℕ)) ×
  FiniteState Basis.standard.genericModel 40

/-- Every program field, clock digit, unary width and initial cell is present in this encoding. -/
noncomputable abbrev packetEncoding : Packet ↪ List Bool :=
  encPair (encPair (programEncoding 40) (encPair encUnary encNat))
    (Cslib.GenericRAM.FiniteState.encoding Basis.standard.encoding)

/-- Construct all runtime simulation inputs from original operand words and scalar input fields. -/
def packet (x : Source) : Packet :=
  ((sourceGenerate x, configuration (readMetadata (sourceMetadata x))), BitInput.initial x.2)

/-- One actual multitape machine materializes the complete packet; no executable, width,
clock, initialization or simulation certificate is a caller premise. -/
noncomputable def packetCertificate : NativeCertificate packet sourceEncoding packetEncoding :=
  NativeCertificate.prod
    (NativeCertificate.prod sourceGenerationCertificate
      (configurationCertificate.comp
        ((NativeCertificate.ofPolyTime readMetadata_polyTime).comp
          (NativeCertificate.ofPolyTime sourceMetadata_polyTime))))
    (BitInput.initialCertificate.comp (NativeCertificate.ofPolyTime (by fun_prop)))

/-- Uniform polynomial packet time and simultaneous workspace include all encoded outputs. -/
theorem packetCertificate_isPolynomial : packetCertificate.IsPolynomial := by
  exact NativeCertificate.prod_isPolynomial _ _
    (NativeCertificate.prod_isPolynomial _ _ sourceGenerationCertificate_isPolynomial
      (NativeCertificate.comp_isPolynomial _ _
        (NativeCertificate.ofPolyTime_isPolynomial (width_polyTime.prod clock_polyTime))
        (NativeCertificate.comp_isPolynomial _ _
          (NativeCertificate.ofPolyTime_isPolynomial readMetadata_polyTime)
          (NativeCertificate.ofPolyTime_isPolynomial sourceMetadata_polyTime))))
    (NativeCertificate.comp_isPolynomial _ _ BitInput.initialCertificate_isPolynomial
      (NativeCertificate.ofPolyTime_isPolynomial (by fun_prop)))

/-- The generated program, word/address width, binary clock and initialized memory are
exactly those of the original-input dissection, with all metadata computed from that input. -/
theorem packet_original {m : ℕ} (p : ℕ) (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    packet (originalSource p as bs cs ds s t) =
      ((BitExecution.program p as.length bs.length cs.length ds.length s t,
        (globalWidth m p as.length bs.length cs.length ds.length,
          BitExecution.steps p as.length bs.length cs.length ds.length)),
        initState .standard 40 (quarterInput as bs cs ds)) := by
  rw [packet, sourceGenerate_original, sourceMetadata_original, read_rawMetadata]
  simp only [configuration, metadata, Matrix.cons_val, originalSource,
    BitInput.initial, BitInput.prepare_words]

/-- Run the actual generated program on the actual prepared finite state and read its output.
This is the finite RAM evaluator, not a claimed runtime-program Turing-machine interpreter. -/
def run (x : Packet) : List Bool :=
  let final := (Cslib.GenericRAM.FiniteState.continuing
    (Cslib.GenericRAM.FiniteState.run x.1.2.1 x.1.1.parkHalts.toGeneric x.1.2.2 x.2)).getD
      (initState .standard 40 [])
  BitExecution.decodeWords (parkedOutput x.1.1.length final)

/-- Generated packet execution is the real simulator run already proved for original inputs. -/
theorem run_original {m : ℕ} (p : ℕ) (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    run (packet (originalSource p as bs cs ds s t)) =
      BitExecution.solveBits p as.length bs.length cs.length ds.length s t
        (BitInput.words as bs cs ds) := by
  rw [packet_original]
  simp only [run, BitExecution.solveBits, BitExecution.execute, Function.comp_apply]
  rw [BitInput.prepare_words]
  rfl

/-- Original inputs derive exhaustive misses or valid original witnesses after actual generated
code/configuration/state construction and the concrete simulated run, with no oracle premises. -/
theorem original_correct {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    ∃ out : Option (List Bool),
      run (packet (originalSource p as bs cs ds s t)) = encOption encBits out ∧
      (out = none ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (∀ ops, out = some ops → ops.length = totalLength as bs cs ds ∧
        eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = t) := by
  rw [run_original]
  exact BitExecution.original_bits_correct hp as bs cs ds s t

/-- The complete original input, including unary dimensions and binary endpoints, has an
explicit bit bound in source width, class depth and operand count. -/
theorem original_input_length {m : ℕ} (p : ℕ) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) :
    (sourceEncoding (originalSource p as bs cs ds s t)).length ≤
      14 * m + 4 * p + 4 * totalLength as bs cs ds * (2 * m + 1) + 13 := by
  have hs := length_encNat_le_of_lt_two_pow s.isLt
  have ht := length_encNat_le_of_lt_two_pow t.isLt
  have hw := BitInput.encoding_words_le as bs cs ds
  rw [BitInput.encoding_length] at hw
  simp only [sourceEncoding, originalSource, length_encPair, encUnary_apply,
    List.length_replicate]
  dsimp only [totalLength]
  nlinarith

/-- One polynomial bounds preparation time, simultaneous workspace and the whole serialized
packet in original-input bit length, with constants independent of the runtime metadata. -/
theorem packet_resources : ∃ C d : ℕ, ∀ x : Source,
    packetCertificate.time x ≤ C * ((sourceEncoding x).length + 1) ^ d ∧
    packetCertificate.space x ≤ C * ((sourceEncoding x).length + 1) ^ d ∧
    (packetEncoding (packet x)).length ≤ C * ((sourceEncoding x).length + 1) ^ d := by
  have hp := packetCertificate_isPolynomial
  have hl := (packetCertificate.polyTime hp).polyBounded_length
  obtain ⟨C, d, h⟩ := ((hp.1.add hp.2).add hl).exists_le
  exact ⟨C, d, fun x => by have := h x; omega⟩

/-- Source-parameter bit bounds for all preparation, code/width/clock generation and initial
state materialization. This charges preparation only, not the subsequent simulated search. -/
theorem original_packet_resources : ∃ C d : ℕ, ∀ (m p : ℕ)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m),
    let bound := C * (14 * m + 4 * p + 4 * totalLength as bs cs ds * (2 * m + 1) + 14) ^ d
    packetCertificate.time (originalSource p as bs cs ds s t) ≤ bound ∧
    packetCertificate.space (originalSource p as bs cs ds s t) ≤ bound ∧
    (packetEncoding (packet (originalSource p as bs cs ds s t))).length ≤ bound := by
  obtain ⟨C, d, h⟩ := packet_resources
  refine ⟨C, d, fun m p as bs cs ds s t => ?_⟩
  have hx := h (originalSource p as bs cs ds s t)
  have length := original_input_length p as bs cs ds s t
  have bound := Nat.mul_le_mul_left C (Nat.pow_le_pow_left
    (show (sourceEncoding (originalSource p as bs cs ds s t)).length + 1 ≤
      14 * m + 4 * p + 4 * totalLength as bs cs ds * (2 * m + 1) + 14 by omega) d)
  exact ⟨hx.1.trans bound, hx.2.1.trans bound, hx.2.2.trans bound⟩

end Cslib.Cryptanalysis.AddXNOR.GeneratedRunInput

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORProgramTemplate
public import CslibFrontier.Cryptanalysis.AddXNORBitExecution
public import CslibFrontier.Computability.WordRAM.ProgramLiterals.Encoding
import all CslibFrontier.Cryptanalysis.AddXNORProgramTemplate
import all CslibFrontier.Computability.WordRAM.ProgramLiterals
import all CslibFrontier.Computability.WordRAM.ProgramLiterals.Encoding
import all CslibFrontier.Computability.WordRAM.ProgramLiterals.Expressions
import all CslibFrontier.Cryptanalysis.AddXNORNativeOutputResources
import all CslibFrontier.Cryptanalysis.AddXNORBitExecution

/-!
# Actual uniform encoded native dissection program generation

One metadata-input multitape machine computes the full program encoding. It
computes the immediate values, fills a fixed native graph, and emits every
opcode, register, branch label and literal as framed binary fields. Concrete
decoding reconstructs the actual reviewed native executable for arbitrary
metadata; no executable or compiler correctness conclusion is supplied by a
caller. The generated executable's clocked run retains original-input witness
and exhaustive-miss correctness.

Generation is uniform and polynomial in mixed unary-size/binary-endpoint metadata.
This does not yet turn the fixed-program simulator family into one metadata-input
Turing interpreter, or establish the sharp source sorted-list resource bounds of
[WangLvShenZhang2027], PDF p. 6 and Lemma 8/Theorem 7, pp. 21–22.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.ProgramGeneration

open Cslib.WordRAM Cslib.WordRAM.ProgramLiterals
open Cslib.GenericRAM (NativeCertificate)
open Turing.MultiTapeTM Native.Driver ProgramTemplate

/-- Metadata is actual unary lengths/widths and binary endpoints, not an executable. -/
def metadata (m p a b c d s t : ℕ) : Metadata :=
  (![m, p, a, b, c, d], ![s, t])

/-- Executable external metadata format: six unary sizes, followed by two binary endpoints. -/
abbrev RawMetadata := List ℕ × List ℕ

/-- Explicit source-order metadata wire; no abstract finite-table ordering is exposed. -/
abbrev metadataEncoding : RawMetadata ↪ List Bool :=
  encPair (encList encUnary) (encList encNat)

/-- Concrete valid metadata records. Extra fields are not used by the total generator. -/
def rawMetadata (m p a b c d s t : ℕ) : RawMetadata := ([m, p, a, b, c, d], [s, t])

/-- Read the six size and two endpoint fields, defaulting missing entries to zero.
This total conversion is not a malformed-input recognizer. -/
def readMetadata (raw : RawMetadata) : Metadata :=
  (fun i => raw.1.getD i 0, fun i => raw.2.getD i 0)

/-- The concrete source-order fields supply exactly the native metadata parameters. -/
theorem read_rawMetadata (m p a b c d s t : ℕ) :
    readMetadata (rawMetadata m p a b c d s t) = metadata m p a b c d s t := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- Runtime metadata parsing is an actual polynomial-time bit computation, including framing. -/
theorem readMetadata_polyTime : ComputableInPolyTime readMetadata metadataEncoding
    (ProgramLiterals.encoding 6 2) := by
  have sizes (i : Fin 6) : ComputableInPolyTime
      (fun raw : RawMetadata => raw.1.getD i 0) metadataEncoding encUnary := by fun_prop
  have endpoints (i : Fin 2) : ComputableInPolyTime
      (fun raw : RawMetadata => raw.2.getD i 0) metadataEncoding encNat := by fun_prop
  exact (ComputableInPolyTime.pi sizes).prod (ComputableInPolyTime.pi endpoints)

/-- Original source data includes unary width/class parameters, binary endpoints and operands. -/
abbrev Source := ((ℕ × ℕ) × (ℕ × ℕ)) × BitInput.Words

/-- Explicit runtime source-input encoding, without executable or quarter-length advice. -/
abbrev sourceEncoding : Source ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) (encPair encNat encNat)) BitInput.encoding

/-- Quarter lengths are computed from actual original operand arrays, retaining zeros/duplicates. -/
def sourceMetadata (x : Source) : RawMetadata :=
  rawMetadata x.1.1.1 x.1.1.2 x.2.1.1.length x.2.1.2.length
    x.2.2.1.length x.2.2.2.length x.1.2.1 x.1.2.2

/-- Actual input-length calculation and metadata materialization have polynomial bit cost. -/
theorem sourceMetadata_polyTime : ComputableInPolyTime sourceMetadata sourceEncoding
    metadataEncoding := by
  have length {f : Source → List ℕ}
      (hf : ComputableInPolyTime f sourceEncoding (encList encNat)) :
      ComputableInPolyTime (fun x => (f x).length) sourceEncoding encUnary :=
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length encNat)).comp hf
  have ha := length (f := fun x => x.2.1.1) (by fun_prop)
  have hb := length (f := fun x => x.2.1.2) (by fun_prop)
  have hc := length (f := fun x => x.2.2.1) (by fun_prop)
  have hd := length (f := fun x => x.2.2.2) (by fun_prop)
  unfold sourceMetadata rawMetadata
  fun_prop

/-- The one fixed native instruction graph, with all scalar immediates zeroed. -/
def skeleton : Program .standard 40 :=
  ((nativeCode (metadata 0 0 0 0 0 0 0 0)).program Output.result).eraseLiterals

/-- Executable native program generation by actual expression evaluation and literal filling. -/
def generate (h : Metadata) : Program .standard 40 :=
  skeleton.fillLiterals (evaluate literalTemplate h)

/-- Every metadata input has the one fixed native instruction graph. -/
theorem erased_exact (h : Metadata) :
    ((nativeCode h).program Output.result).eraseLiterals = skeleton := by
  unfold skeleton
  rw [Code.eraseLiterals_program, Code.eraseLiterals_program]
  exact congrArg (fun c : Code .standard 40 => c.program Output.result)
    ((graph_exact h).trans (graph_exact (metadata 0 0 0 0 0 0 0 0)).symm)

/-- The computed program is exactly the original executable, for arbitrary input metadata. -/
theorem generate_exact (h : Metadata) :
    generate h = (nativeCode h).program Output.result := by
  rw [generate, ← erased_exact h, literals_exact, ← Code.literals_program]
  exact Program.fillLiterals_erase _

/-- The full executable has a fixed instruction count, including halt. -/
theorem generate_length (h : Metadata) : (generate h).length = 1109 := by
  rw [generate_exact]
  simp only [nativeCode, Code.program, List.length_append, Code.length_assemble,
    dissectionOutput_size, List.length_cons, List.length_nil]

/-- All 303 scalar constants are computed from the metadata, including repeated values. -/
theorem literalTemplate_length : literalTemplate.length = 303 := by decide +kernel

/-- Uniform multitape program generation on encoded metadata, with actual instruction fields. -/
theorem serialize_generate_polyTime :
    ComputableInPolyTime (fun h => serialize (generate h))
      (ProgramLiterals.encoding 6 2) (encList (encList encNat)) :=
  (serialize_fill_polyTime skeleton).comp (evaluate_polyTime literalTemplate)

/-- The real code-generation machine, with its charged time and simultaneous workspace profiles. -/
noncomputable def generationCertificate : NativeCertificate generate
    (ProgramLiterals.encoding 6 2) (programEncoding 40) :=
  let c := (NativeCertificate.ofPolyTime (serialize_fill_polyTime skeleton)).comp
    (evaluateCertificate literalTemplate)
  ⟨c.time, c.space, c.computes.of_enc_eq (fun _ => rfl)⟩

/-- Both generator profiles have polynomial bounds uniform over every metadata input. -/
theorem generationCertificate_isPolynomial : generationCertificate.IsPolynomial :=
  NativeCertificate.comp_isPolynomial _ _
    (NativeCertificate.ofPolyTime_isPolynomial (serialize_fill_polyTime skeleton))
    (evaluateCertificate_isPolynomial literalTemplate)

/-- One polynomial bounds generation time, simultaneous workspace and complete emitted code
size in the actual metadata bit length. Its constants do not vary with the metadata. -/
theorem generation_resources : ∃ C d : ℕ, ∀ h : Metadata,
    generationCertificate.time h ≤ C * ((ProgramLiterals.encoding 6 2 h).length + 1) ^ d ∧
    generationCertificate.space h ≤ C * ((ProgramLiterals.encoding 6 2 h).length + 1) ^ d ∧
    (programEncoding 40 (generate h)).length ≤
      C * ((ProgramLiterals.encoding 6 2 h).length + 1) ^ d := by
  have hp := generationCertificate_isPolynomial
  have hl := (generationCertificate.polyTime hp).polyBounded_length
  obtain ⟨C, d, h⟩ := ((hp.1.add hp.2).add hl).exists_le
  exact ⟨C, d, fun x => by have := h x; omega⟩

/-- The complete uniform generator on explicit executable source-order metadata records. -/
def rawGenerate : RawMetadata → Program .standard 40 := generate ∘ readMetadata

/-- Actual parsing and code materialization on the explicit metadata wire. -/
noncomputable def rawGenerationCertificate : NativeCertificate rawGenerate
    metadataEncoding (programEncoding 40) :=
  generationCertificate.comp (NativeCertificate.ofPolyTime readMetadata_polyTime)

/-- Polynomial generation time and simultaneous bit workspace are uniform in source metadata. -/
theorem rawGenerationCertificate_isPolynomial : rawGenerationCertificate.IsPolynomial :=
  NativeCertificate.comp_isPolynomial _ _ generationCertificate_isPolynomial
    (NativeCertificate.ofPolyTime_isPolynomial readMetadata_polyTime)

/-- The raw-wire generator reconstructs the same executable as direct scalar parameters. -/
theorem rawGenerate_exact (m p a b c d s t : ℕ) :
    rawGenerate (rawMetadata m p a b c d s t) =
      (nativeCode (metadata m p a b c d s t)).program Output.result := by
  rw [rawGenerate, Function.comp_apply, read_rawMetadata, generate_exact]

/-- Uniform source-input-to-executable generation, computing its own quarter lengths. -/
def sourceGenerate : Source → Program .standard 40 := rawGenerate ∘ sourceMetadata

/-- One actual finite multitape generator on the complete original source input. -/
noncomputable def sourceGenerationCertificate : NativeCertificate sourceGenerate
    sourceEncoding (programEncoding 40) :=
  rawGenerationCertificate.comp (NativeCertificate.ofPolyTime sourceMetadata_polyTime)

/-- Uniform time and simultaneous workspace bounds include reading the original operands. -/
theorem sourceGenerationCertificate_isPolynomial : sourceGenerationCertificate.IsPolynomial :=
  NativeCertificate.comp_isPolynomial _ _ rawGenerationCertificate_isPolynomial
    (NativeCertificate.ofPolyTime_isPolynomial sourceMetadata_polyTime)

/-- The generator emits 1,109 rows of at most five fields each, including all control metadata. -/
theorem generated_rows (h : Metadata) :
    (serialize (generate h)).length = 1109 ∧
      ∀ row ∈ serialize (generate h), row.length ≤ 5 := by
  refine ⟨?_, ?_⟩
  · simpa only [serialize, List.length_map] using generate_length h
  · intro row hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact record_length i

/-- Concrete binary-row decoding reconstructs the executable used by the original algorithm. -/
theorem decode_generate (h : Metadata) :
    deserialize 40 (serialize (generate h)) = some ((nativeCode h).program Output.result) := by
  rw [deserialize_serialize, generate_exact]

/-- Actual clocked execution of the generated executable, followed by actual output readback. -/
def execute (h : Metadata) (xs : BitInput.Words) : List Bool :=
  BitExecution.decodeWords ((generate h).clockedList
    (globalWidth (h.1 0) (h.1 1) (h.1 2) (h.1 3) (h.1 4) (h.1 5))
    (BitExecution.steps (h.1 1) (h.1 2) (h.1 3) (h.1 4) (h.1 5))
    (BitInput.prepare xs))

/-- Canonical binary endpoint fields recover the original full-width seed and target. -/
theorem nativeCode_metadata {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) :
    nativeCode (metadata m p a b c d s.toNat t.toNat) =
      dissectionOutput (compactSearchLayout m p a b c d)
        (compactCounterLayout m p a b c d) s t := by
  change dissectionOutput _ _ (BitVec.ofNat m s.toNat) (BitVec.ofNat m t.toNat) = _
  simp only [metadata, Matrix.cons_val, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Complete original-input source data, with no supplied quarter lengths or executable. -/
def originalSource {m : ℕ} (p : ℕ) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) : Source := (((m, p), (s.toNat, t.toNat)), BitInput.words as bs cs ds)

/-- Generated metadata uses actual operand lengths and the original binary endpoints. -/
theorem sourceMetadata_original {m : ℕ} (p : ℕ) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) :
    sourceMetadata (originalSource p as bs cs ds s t) =
      rawMetadata m p as.length bs.length cs.length ds.length s.toNat t.toNat := by
  simp only [sourceMetadata, originalSource, BitInput.words, List.length_map]

/-- The uniform original-input generator emits exactly the reviewed native executable. -/
theorem sourceGenerate_original {m : ℕ} (p : ℕ) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) :
    sourceGenerate (originalSource p as bs cs ds s t) =
      BitExecution.program p as.length bs.length cs.length ds.length s t := by
  rw [sourceGenerate, Function.comp_apply, sourceMetadata_original,
    rawGenerate_exact, nativeCode_metadata]
  rfl

/-- Generated-code execution agrees with the existing proved bit-execution pipeline. -/
theorem execute_original {m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    execute (metadata m p as.length bs.length cs.length ds.length s.toNat t.toNat)
      (BitInput.words as bs cs ds) =
    BitExecution.solveBits p as.length bs.length cs.length ds.length s t
      (BitInput.words as bs cs ds) := by
  rw [execute, generate_exact]
  rw [nativeCode_metadata]
  simp only [metadata, Matrix.cons_val, BitExecution.solveBits, BitExecution.execute,
    Function.comp_apply]
  change BitExecution.decodeWords
    ((BitExecution.program p as.length bs.length cs.length ds.length s t).clockedList
      (globalWidth m p as.length bs.length cs.length ds.length)
      (BitExecution.steps p as.length bs.length cs.length ds.length)
      (BitInput.prepare (BitInput.words as bs cs ds))) = _
  rfl

/-- No supplied executable, simulation, dictionary, query or witness conclusion is a premise:
original operands derive exhaustive misses or sound witnesses from the generated program. -/
theorem original_correct {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    ∃ out : Option (List Bool),
      execute (metadata m p as.length bs.length cs.length ds.length s.toNat t.toNat)
        (BitInput.words as bs cs ds) = encOption encBits out ∧
      (out = none ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (∀ ops, out = some ops → ops.length = totalLength as bs cs ds ∧
        eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = t) := by
  rw [execute_original]
  exact BitExecution.original_bits_correct hp as bs cs ds s t

end Cslib.Cryptanalysis.AddXNOR.ProgramGeneration

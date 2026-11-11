/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORBitInput
public import CslibFrontier.Cryptanalysis.AddXNORNativeOutputResources
public import CslibFrontier.Computability.WordRAM.Turing.ClockedListOutput
import all CslibFrontier.Cryptanalysis.AddXNOROutputCodec
import all CslibFrontier.Cryptanalysis.AddXNORBitInput
import all CslibFrontier.Cryptanalysis.AddXNORNativeGlobalLayout
import all CslibFrontier.Computability.WordRAM.Turing.ClockedListOutput

/-!
# Concrete encoded execution of the native dissection program

For arbitrary admitted parameters, a real finite multitape machine receives
original-order quarter words, computes the reversed native calling convention,
materializes the sparse initial memory, simulates the actual native program and
reads its represented output array. Original inputs prove exhaustive misses or
sound original-chain witnesses; no semantic query, dictionary, output or
simulation conclusion is a premise.

The program is fixed for each choice of widths, quarter lengths and endpoints.
The machine construction therefore supplies a parameterized family, not one
uniform header-to-program compiler. Bounds retain the concrete simulator's
control, checked arithmetic and sparse-memory costs. They do not preserve the
source sorted-list asymptotics in [WangLvShenZhang2027], PDF p. 6 and Lemma 8 /
Theorem 7, pp. 21–22. Native computed-balance live support remains distinct from
the simulator's stored bindings, which include zeros and may grow with time.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.BitExecution

open Turing.MultiTapeTM Cslib.WordRAM Cslib.GenericRAM Native.Driver

/-- The actual compiled native code, with scalar parameters fixed in its instructions. -/
def program {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) : Program .standard 40 :=
  (dissectionOutput (compactSearchLayout m p a b c d)
    (compactCounterLayout m p a b c d) s t).program Output.result

/-- A fixed graph including the final halt; scalar literals still vary with the parameters. -/
theorem program_length {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) :
    (program p a b c d s t).length = 1109 := by
  simp [program, Code.program, Code.length_assemble, dissectionOutput_size]

/-- A derived finite clock including native serialization and halt. -/
def steps (p a b c d : ℕ) : ℕ := globalTime p a b c d + outputTime a b c d + 1

/-- Actual clocked computation, including fault fallback on arbitrary malformed word inputs. -/
def execute {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) : BitInput.Words → List ℕ :=
  (program p a b c d s t).clockedList (globalWidth m p a b c d)
    (steps p a b c d) ∘ BitInput.prepare

/-- Concrete source-order bit computation. Both stages are constructed implementations;
there is no caller-supplied simulation, resource bound or initialization certificate. -/
noncomputable def executionCertificate {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) :
    NativeCertificate (execute p a b c d s t) BitInput.encoding (encList encNat) :=
  ((program p a b c d s t).clockedListCertificate (globalWidth m p a b c d)
    (steps p a b c d)).comp BitInput.prepareCertificate

/-- Every preparation, initialization, simulator dispatch/word/address operation and output
read is charged. The fixed-program implementation constants are not uniform in its literals. -/
theorem executionCertificate_time {m : ℕ} (p a b c d : ℕ) (s t : BitVec m)
    (xs : BitInput.Words) :
    (executionCertificate p a b c d s t).time xs =
      BitInput.prepareCertificate.time xs +
      (2 * (encList encNat (BitInput.prepare xs)).length +
        (Program.clockedInitialCertificate (r := 40)).time (BitInput.prepare xs) +
        FiniteState.runTime Basis.standard.encoding Basis.standard.nativePrimitives
          (program p a b c d s t).parkHalts.toGeneric
          (steps p a b c d, (globalWidth m p a b c d,
            BitInput.initial xs)) +
        (program p a b c d s t).clockedReaderCertificate.time
          ((program p a b c d s t).clockedState (globalWidth m p a b c d)
            (steps p a b c d) (BitInput.prepare xs))) := by
  exact congrArg (BitInput.prepareCertificate.time xs + ·)
    (Program.clockedListCertificate_time _ _ _ _)

/-- Charged simultaneous bit workspace, not native cell count or total allocation.
The concrete simulator/reader profiles include every prefix of their execution. -/
theorem executionCertificate_space {m : ℕ} (p a b c d : ℕ) (s t : BitVec m)
    (xs : BitInput.Words) :
    (executionCertificate p a b c d s t).space xs =
      BitInput.prepareCertificate.space xs +
      (2 * (encList encNat (BitInput.prepare xs)).length +
        (Program.clockedInitialCertificate (r := 40)).space (BitInput.prepare xs) +
        FiniteState.runSpace Basis.standard.encoding Basis.standard.nativePrimitives
          (program p a b c d s t).parkHalts.toGeneric
          (steps p a b c d, (globalWidth m p a b c d,
            BitInput.initial xs)) +
        (program p a b c d s t).clockedReaderCertificate.space
          ((program p a b c d s t).clockedState (globalWidth m p a b c d)
            (steps p a b c d) (BitInput.prepare xs))) := by
  exact congrArg (BitInput.prepareCertificate.space xs + ·)
    (Program.clockedListCertificate_space _ _ _ _)

/-- Parse the actual read-back word wire to optional-witness bits. On arbitrary malformed
words this is just the finite transducer's output, not a validity recognizer. -/
def decodeWords (ws : List ℕ) : List Bool :=
  OutputCodec.decoder.run OutputCodec.decoder.q₀ (encList encNat ws)

/-- The concrete six-state output parser charges linear bit time and no work tapes. -/
theorem decodeWords_inO : ComputableInO decodeWords (encList encNat) encBits
    (fun ws => (encList encNat ws).length) (fun ws => (encList encNat ws).length) := by
  have h : ComputableInTimeAndSpace decodeWords (encList encNat) encBits
      (fun ws => 2 * (encList encNat ws).length + 3) (fun _ => 0) :=
    ⟨0, _, inferInstance, OutputCodec.decoder.toTM, fun ws =>
      OutputCodec.decoder.computesInTimeAndSpace_toTM (encList encNat ws)⟩
  exact .of_bounds h 3 (fun _ => by omega) (fun _ => by omega)
    (fun ws => by have := h.length_le ws; omega)

/-- The whole bit computation, including charged native-memory extraction before decoding. -/
def solveBits {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) : BitInput.Words → List Bool :=
  decodeWords ∘ execute p a b c d s t

/-- One actual finite multitape implementation for every operand tuple, with metadata fixed.
Linear final decoding is absorbed by the producer's encoded-output charge; the exposed time
and simultaneous workspace profiles are those of `executionCertificate`, up to constants. -/
noncomputable def solveBitsCertificate {m : ℕ} (p a b c d : ℕ) (s t : BitVec m) :
    NativeCertificate (solveBits p a b c d s t) BitInput.encoding encBits :=
  NativeCertificate.post (executionCertificate p a b c d s t) decodeWords_inO

/-- Original inputs determine the encoded execution's exhaustive answer and valid witness.
All widths and quarter lengths are arbitrary; zero-length quarters and collisions are allowed. -/
theorem original_correct {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    ∃ out : Option (List Bool),
      execute p as.length bs.length cs.length ds.length s t (BitInput.words as bs cs ds) =
        OutputCodec.encode out ∧
      (out = none ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (∀ ops, out = some ops → ops.length = totalLength as bs cs ds ∧
        eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = t) := by
  obtain ⟨out, y, n, ts, hn, _, he, _, absent, sound, _⟩ :=
    original_output_resources hp as bs cs ds s t
  refine ⟨out, ?_, absent, sound⟩
  rw [execute, Function.comp_apply, BitInput.prepare_words]
  exact Program.clockedList_eq he (by dsimp only [steps]; omega)

/-- Source-order encoded operands yield an exhaustive miss or a sound original witness in
the ordinary optional-bit encoding. The implementing machine reads RAM output itself. -/
theorem original_bits_correct {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    ∃ out : Option (List Bool),
      solveBits p as.length bs.length cs.length ds.length s t (BitInput.words as bs cs ds) =
        encOption encBits out ∧
      (out = none ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (∀ ops, out = some ops → ops.length = totalLength as bs cs ds ∧
        eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = t) := by
  obtain ⟨out, he, absent, sound⟩ := original_correct hp as bs cs ds s t
  refine ⟨out, ?_, absent, sound⟩
  simpa only [solveBits, Function.comp_apply, he, decodeWords, OutputCodec.wire] using
    OutputCodec.decoder_run out

/-- At every simulated prefix the physical word bound and actual stored-entry growth give
an encoded-state bound. Native peak live support is deliberately not substituted for entries. -/
theorem original_encoding_bound {m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (j : ℕ) :
    let P := program p as.length bs.length cs.length ds.length s t
    let W := globalWidth m p as.length bs.length cs.length ds.length
    (FiniteState.resultEncoding Basis.standard.encoding
      (FiniteState.run W P.parkHalts.toGeneric j
        (BitInput.initial (BitInput.words as bs cs ds)))).length ≤
      stateBound 40 (labelBound P.parkHalts.toGeneric) W
        (totalLength as bs cs ds + 1 + j) := by
  have h := Program.clocked_encoding_bound
    (program p as.length bs.length cs.length ds.length s t)
    (quarterInput_fits (p := p) as bs cs ds) j
  simpa only [BitInput.initial, BitInput.prepare_words, quarterInput, List.length_map,
    List.length_append, List.length_reverse, totalLength, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

end Cslib.Cryptanalysis.AddXNOR.BitExecution

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Tactic.PolyTime

/-!
# A uniform serialized Lyubashevsky extractor

The extractor needs only runtime dimensions `m,k`, two bit challenges and two optional integer
responses. It computes the response difference followed by the signed reversed challenge
difference. Dimensions are unary resources; integer magnitudes are binary. Every input word has
a total interpretation: missing vector entries are zero, missing challenge bits are false, and
surplus coordinates are ignored. The optional-vector default is the zero vector.

The same word program handles all dimensions; no parameter-family claim is inferred from a
certificate for one fixed finite vector type. This is a deterministic operation certificate,
not a rewinding, knowledge-soundness or cryptographic security theorem.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.LyubashevskyExtractInput`: the fixed runtime input type.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyExtractList`: the native integer output.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyExtractWord`: the complete word program.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.computableInPolyTime_lyubashevskyExtractWord`: all parsing,
  arithmetic, framing and output costs in one uniform plain certificate.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyExtractWord_eq_extract`: exact agreement with
  the typed protocol extractor for all dimensions, statements and commitments.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Turing.MultiTapeTM

/-- Dimensions followed by two challenge/optional-response pairs. -/
abbrev LyubashevskyExtractInput :=
  (ℕ × ℕ) × ((List Bool × Option (List ℤ)) × (List Bool × Option (List ℤ)))

/-- Unary dimensions, raw challenges and framed optional lists of binary signed integers. -/
def encLyubashevskyExtractInput : LyubashevskyExtractInput ↪ List Bool :=
  encPair (encPair encUnary encUnary)
    (encPair (encPair encBits (encOption (encList encIntBin)))
      (encPair encBits (encOption (encList encIntBin))))

/-- Parse every input word with the existing framing conventions; malformed fields have total
zero/default interpretations. -/
def decodeLyubashevskyExtractInput (word : List Bool) : LyubashevskyExtractInput :=
  let dimensions := unframe word
  let rows := dropFrame word
  let response (w : List Bool) : Option (List ℤ) :=
    if w.isEmpty then none else some ((frames w.tail).map decodeIntBin)
  let row (w : List Bool) := (unframe w, response (dropFrame w))
  (((unframe dimensions).length, (dropFrame dimensions).length),
    (row (unframe rows), row (dropFrame rows)))

private theorem extractInput_decoder :
    ∃ D : Decoder encLyubashevskyExtractInput, D.decode = decodeLyubashevskyExtractInput := by
  let integer : Decoder encIntBin := {
    decode := decodeIntBin
    decode_enc := decodeIntBin_encIntBin
    computable := computableInPolyTime_decodeIntBin.exists_degree }
  let row := Decoder.pair Decoder.bits (Decoder.option (Decoder.list integer))
  let decoder := Decoder.pair (Decoder.pair Decoder.unary Decoder.unary) (Decoder.pair row row)
  exact ⟨decoder, rfl⟩

/-- Parsing inverts the complete canonical input encoding. -/
@[simp] theorem decodeLyubashevskyExtractInput_enc (input : LyubashevskyExtractInput) :
    decodeLyubashevskyExtractInput (encLyubashevskyExtractInput input) = input := by
  obtain ⟨decoder, hdecoder⟩ := extractInput_decoder
  rw [← hdecoder]
  exact decoder.decode_enc input

/-- The total input parser has a plain polynomial-time certificate, including malformed words. -/
@[fun_prop]
theorem computableInPolyTime_decodeLyubashevskyExtractInput :
    ComputableInPolyTime decodeLyubashevskyExtractInput encBits encLyubashevskyExtractInput := by
  obtain ⟨decoder, hdecoder⟩ := extractInput_decoder
  rw [← hdecoder]
  exact decoder.computableInPolyTime

/-- Compute `z-z′` first, then the SIGNED challenge difference `c′-c`. The unary dimensions
control both output segments; optional responses default to zero coordinatewise. -/
def lyubashevskyExtractList (input : LyubashevskyExtractInput) : List ℤ :=
  ((List.range input.1.1).map fun i =>
    (input.2.1.2.getD []).getD i 0 - (input.2.2.2.getD []).getD i 0) ++
  ((List.range input.1.2).map fun i =>
    (if input.2.2.1.getD i false then (1 : ℤ) else 0) -
      (if input.2.1.1.getD i false then (1 : ℤ) else 0))

/-- Extraction always writes the two declared segments, even on malformed-length inputs. -/
@[simp] theorem length_lyubashevskyExtractList (input : LyubashevskyExtractInput) :
    (lyubashevskyExtractList input).length = input.1.1 + input.1.2 := by
  simp [lyubashevskyExtractList]

/-- One native extractor handles runtime dimensions and all binary integer magnitudes. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskyExtractList :
    ComputableInPolyTime lyubashevskyExtractList encLyubashevskyExtractInput
      (encList encIntBin) := by
  apply ComputableInPolyTime.of_tidy
  unfold lyubashevskyExtractList encLyubashevskyExtractInput
  fun_prop

private theorem getD_optional_ofFn {m : ℕ} (z : Option (Fin m → ℤ)) (i : Fin m) :
    ((z.map List.ofFn).getD []).getD i.val 0 = (z.getD 0) i := by
  cases z <;> simp [List.getD_eq_getElem?_getD]

private theorem map_range_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) (g : Fin n → α)
    (h : ∀ i : Fin n, f i.val = g i) : (List.range n).map f = List.ofFn g := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  conv_rhs => rw [List.ofFn_eq_map]
  exact List.map_congr_left fun i _ => h i

/-- Canonical typed vectors give exactly the ordered response difference and signed reversed
challenge difference. This formula is independent of statement matrices and the modulus. -/
theorem lyubashevskyExtractList_ofFn {m k : ℕ} (c : Fin k → Bool) (z : Option (Fin m → ℤ))
    (c' : Fin k → Bool) (z' : Option (Fin m → ℤ)) :
    lyubashevskyExtractList ((m, k),
      ((List.ofFn c, z.map List.ofFn), (List.ofFn c', z'.map List.ofFn))) =
      List.ofFn (Fin.append (fun i => (z.getD 0) i - (z'.getD 0) i)
        (fun i => (if c' i then (1 : ℤ) else 0) - (if c i then (1 : ℤ) else 0))) := by
  rw [List.ofFn_fin_append]
  unfold lyubashevskyExtractList
  dsimp only [Prod.fst, Prod.snd]
  congr 1
  · apply map_range_eq_ofFn
    intro i
    rw [getD_optional_ofFn, getD_optional_ofFn]
  · apply map_range_eq_ofFn
    intro i
    simp [List.getD_eq_getElem?_getD]

/-- The complete serialized program: parse, extract, and frame every signed output coordinate. -/
def lyubashevskyExtractWord (word : List Bool) : List Bool :=
  encList encIntBin (lyubashevskyExtractList (decodeLyubashevskyExtractInput word))

/-- The complete extractor is one plain polynomial-time word function, not a separate machine
for each fixed dimension. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskyExtractWord :
    ComputableInPolyTime lyubashevskyExtractWord encBits encBits := by
  apply ComputableInPolyTime.of_tidy
  exact (ComputableTidilyInPolyTime.encode (encList encIntBin)).comp
    (computableInPolyTime_lyubashevskyExtractList.tidy.comp
      computableInPolyTime_decodeLyubashevskyExtractInput.tidy)

/-- The word program exactly implements the integer-list extractor on canonical encoded data. -/
@[simp] theorem lyubashevskyExtractWord_enc (input : LyubashevskyExtractInput) :
    lyubashevskyExtractWord (encLyubashevskyExtractInput input) =
      encList encIntBin (lyubashevskyExtractList input) := by
  simp [lyubashevskyExtractWord]

/-- Canonical vectors realize the actual typed extractor for every statement and commitment.
The ignored statement dimensions and modulus do not need to be supplied to the word program. -/
theorem lyubashevskyExtractList_eq_extract (n m k q : ℕ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (w : Fin n → ZMod q) (c : BitString k) (z : Option (Fin m → ℤ))
    (c' : BitString k) (z' : Option (Fin m → ℤ)) :
    lyubashevskyExtractList ((m, k),
      ((List.ofFn c, z.map List.ofFn), (List.ofFn c', z'.map List.ofFn))) =
      List.ofFn (fun i : Fin (m + k) =>
        lyubashevskyExtract n m k q y w c z c' z' (finSumFinEquiv.symm i)) := by
  rw [lyubashevskyExtractList_ofFn]
  congr 1
  funext i
  cases i using Fin.addCases <;> simp [lyubashevskyExtract, lyubashevskyChallenge]

/-- The complete word program agrees exactly with the named typed extractor, including absent
responses and zero dimensions, without assuming acceptance of either conversation. -/
theorem lyubashevskyExtractWord_eq_extract (n m k q : ℕ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (w : Fin n → ZMod q) (c : BitString k) (z : Option (Fin m → ℤ))
    (c' : BitString k) (z' : Option (Fin m → ℤ)) :
    lyubashevskyExtractWord (encLyubashevskyExtractInput ((m, k),
      ((List.ofFn c, z.map List.ofFn), (List.ofFn c', z'.map List.ofFn)))) =
      encList encIntBin (List.ofFn (fun i : Fin (m + k) =>
        lyubashevskyExtract n m k q y w c z c' z' (finSumFinEquiv.symm i))) := by
  rw [lyubashevskyExtractWord_enc, lyubashevskyExtractList_eq_extract n m k q y w]

end Cslib.Crypto.Protocols.SigmaProtocol

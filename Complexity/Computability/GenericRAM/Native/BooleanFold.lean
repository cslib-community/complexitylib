/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import Mathlib.Data.Nat.Size

/-!
# Streaming local Boolean assignments

The runtime dimension is unary and the current index is binary. The existing `lowBits` decoder
returns exactly that many bits, padding or truncating on arbitrary indices. Its certificate below
is derived from direct native list/bit primitives; no legacy polynomial-time bridge is used.
The assignment list in the correctness specification is not constructed by the streaming loop.

This is the local Boolean-vector component of the enumeration in [OpenAI2026ETH], Lemma 3.2 and
Proposition 3.4, pp. 22–26. It is not a mixed-radix or subset-pair enumerator, and gives no
polynomial-time bound for a whole loop with exponentially many rounds.
-/

@[expose] public section

namespace Cslib.GenericRAM.BooleanFold

open Turing.MultiTapeTM
open Cslib.BitString


/-- The fixed decoder reads its runtime width in unary and its runtime index in binary.
The actual machine has polynomial time and charged workspace in their complete pair encoding. -/
theorem decoder_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => lowBits p.1 p.2)
      (encPair encUnary encNat) encBits := by
  have hw := ComputableInPolyTime.fst encUnary encNat
  have hv := ComputableInPolyTime.snd encUnary encNat
  have hl := ComputableInPolyTime.range.comp hw
  have hf : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2.testBit p.2)
      (encPair (encPair encUnary encNat) encUnary) encBool :=
    ComputableInPolyTime.binary_testBit
      (hv.comp (ComputableInPolyTime.fst (encPair encUnary encNat) encUnary))
      (ComputableInPolyTime.snd (encPair encUnary encNat) encUnary)
  have hm := ComputableInPolyTime.mapWithInput (f := fun p i => p.2.testBit i)
    (encB := encBool) hl hf
  simpa only [lowBits, Function.comp_def] using ComputableInPolyTime.listToBits.comp hm

/-- Bounds selected from the direct fixed decoder machine; the machine is uniform in both
runtime width and index. This is not a separate finite machine for every width. -/
noncomputable def decoder :
    NativeCertificate (fun p : ℕ × ℕ => lowBits p.1 p.2)
      (encPair encUnary encNat) encBits :=
  NativeCertificate.ofPolyTime decoder_polyTime

/-- Both selected decoder resource bounds are polynomial in the full encoded input length. -/
theorem decoder_isPolynomial : decoder.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial decoder_polyTime

/-- Each valid binary index decodes to its word in the existing finite enumeration order. -/
theorem lowBits_eq_word (n : ℕ) (j : Fin (2 ^ n)) :
    lowBits n j = List.ofFn ((equivFin n).symm j) := by
  rw [lowBits_eq_ofFn]
  congr 1
  funext i
  exact (equivFin_symm_apply j i).symm

/-- The conceptual sequence of decoded indices is exactly the old materializing enumeration.
Only this specification uses the list of all indices. -/
theorem decoded_range_eq_enumList (n : ℕ) :
    (List.range (2 ^ n)).map (lowBits n) = enumList n := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range, enumList_eq_ofFn, List.getElem_ofFn]
  exact lowBits_eq_word n ⟨i, by simpa using hi⟩

/-- Distinct valid indices decode to distinct runtime words. -/
theorem decoder_injective (n : ℕ) :
    Function.Injective (fun j : Fin (2 ^ n) => lowBits n j) := by
  intro i j h
  apply (equivFin n).symm.injective
  exact List.ofFn_inj.mp (by simpa only [lowBits_eq_word] using h)

/-- Every runtime word of the declared length is decoded by exactly one valid index. -/
theorem decoder_coverage (n : ℕ) (word : List Bool) (hw : word.length = n) :
    ∃! j : Fin (2 ^ n), lowBits n j = word := by
  have hm : word ∈ enumList n := mem_enumList.mpr hw
  rw [← decoded_range_eq_enumList] at hm
  obtain ⟨j, hj, heq⟩ := List.mem_map.mp hm
  refine ⟨⟨j, List.mem_range.mp hj⟩, heq, ?_⟩
  intro k hk
  exact decoder_injective n (hk.trans heq.symm)

private theorem bits_power (n : ℕ) : (2 ^ n).bits = List.replicate n false ++ [true] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_comm, Nat.bit0_bits _ (by positivity), ih]
    rfl

private def clockTransducer : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [false])
  final _ := [true]
  length_step_le _ _ := by decide
  length_final_le _ := by decide

private theorem clockRun (n : ℕ) :
    clockTransducer.run () (List.replicate n true) = List.replicate n false ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false :: clockTransducer.run () (List.replicate n true) = _
    rw [ih]
    rfl

/-- Construct the exponential visit count in binary, in linear time in the unary dimension.
Only `n + 1` output bits are produced; no unary representation of `2 ^ n` is constructed. -/
def clock : NativeCertificate (fun n : ℕ => 2 ^ n) encUnary encNat where
  time n := (encUnary n).length
  space n := (encUnary n).length
  computes := by
    apply ComputableInO.of_linear
    apply ComputableInLinearTimeAndSpace.of_transducer clockTransducer
    intro n
    change (2 ^ n).bits = clockTransducer.run () (List.replicate n true)
    rw [bits_power, clockRun]

/-- The binary visit count has exactly one more bit than the dimension. -/
theorem length_clock (n : ℕ) : (encNat (2 ^ n)).length = n + 1 := by
  change (2 ^ n).bits.length = n + 1
  simp [bits_power]

variable {β : Type}

/-- Decode the current index, retain the runtime dimension and invoke the full captured body. -/
def visit (body : (ℕ × List Bool) × β → β) (p : ℕ × (ℕ × β)) : ℕ × β :=
  (p.2.1, body ((p.2.1, lowBits p.2.1 p.1), p.2.2))

/-- A prefix of the streaming assignment traversal, retaining width and captured accumulator. -/
def runPrefix (body : (ℕ × List Bool) × β → β) (n j : ℕ) (initial : β) : ℕ × (ℕ × β) :=
  IndexFold.run (visit body) j (n, initial)

/-- The whole traversal, including its completed index and retained dimension. -/
def run (body : (ℕ × List Bool) × β → β) (n : ℕ) (initial : β) : ℕ × (ℕ × β) :=
  runPrefix body n (2 ^ n) initial

/-- The dimension is preserved at every prefix, independent of the body. -/
@[simp] theorem prefix_width (body : (ℕ × List Bool) × β → β) (n j : ℕ) (initial : β) :
    (runPrefix body n j initial).2.1 = n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (IndexFold.run (visit body) (j + 1) (n, initial)).2.1 = n
    rw [IndexFold.run_succ]
    exact ih

/-- Every prefix visits the decoded words in increasing index order. -/
theorem prefix_accumulator (body : (ℕ × List Bool) × β → β) (n j : ℕ) (initial : β) :
    (runPrefix body n j initial).2.2 =
      (List.range j).foldl (fun acc i => body ((n, lowBits n i), acc)) initial := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (IndexFold.run (visit body) (j + 1) (n, initial)).2.2 = _
    rw [IndexFold.run_succ]
    change body (((runPrefix body n j initial).2.1,
      lowBits (runPrefix body n j initial).2.1 (runPrefix body n j initial).1),
      (runPrefix body n j initial).2.2) = _
    rw [prefix_width, show (runPrefix body n j initial).1 = j from IndexFold.run_index _ _ _, ih]
    simp [List.range_succ, List.foldl_append]

/-- The streaming traversal agrees with the existing enumeration, hence covers every runtime
word of length `n` exactly once in that enumeration's order. The right side is
specification-only. -/
theorem run_accumulator (body : (ℕ × List Bool) × β → β) (n : ℕ) (initial : β) :
    (run body n initial).2.2 =
      (enumList n).foldl (fun acc word => body ((n, word), acc)) initial := by
  rw [run, prefix_accumulator]
  have h := List.foldl_map (f := lowBits n) (g := fun acc word => body ((n, word), acc))
    (l := List.range (2 ^ n)) (init := initial)
  simpa only [decoded_range_eq_enumList] using h.symm

variable {encB : β ↪ List Bool}

/-- The full live state contains the binary index, retained unary width and accumulator.
No word list or exponential history contributes to this prefix bound. -/
theorem length_prefix_le (body : (ℕ × List Bool) × β → β) (n j B : ℕ) (initial : β)
    (hj : j ≤ 2 ^ n) (hB : (encB (runPrefix body n j initial).2.2).length ≤ B) :
    (encPair encNat (encPair encUnary encB) (runPrefix body n j initial)).length ≤
      4 * n + 4 + B := by
  simp only [length_encPair, prefix_width, encUnary_apply, List.length_replicate]
  have hi : (runPrefix body n j initial).1 = j := IndexFold.run_index _ _ _
  rw [hi]
  have hn : (encNat j).length ≤ (encNat (2 ^ n)).length := by
    simpa [Nat.size_eq_bits_len] using Nat.size_le_size hj
  rw [length_clock] at hn
  omega

/-- The decoded word itself always has the declared runtime dimension, even on arbitrary
indices. This bounds temporary callback input as well as the persistent state. -/
theorem length_callback_input (n j : ℕ) (acc : β) :
    (encPair (encPair encUnary encBits) encB ((n, lowBits n j), acc)).length =
      6 * n + 3 + (encB acc).length := by
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply, length_lowBits]
  omega

/-- Prepare the complete runtime width/word/captured-accumulator input for one callback. -/
theorem prepare_polyTime :
    ComputableInPolyTime (fun p : ℕ × (ℕ × β) =>
      ((p.2.1, lowBits p.2.1 p.1), p.2.2))
      (encPair encNat (encPair encUnary encB)) (encPair (encPair encUnary encBits) encB) := by
  have hs := ComputableInPolyTime.snd encNat (encPair encUnary encB)
  have hn := (ComputableInPolyTime.fst encUnary encB).comp hs
  have hi := ComputableInPolyTime.fst encNat (encPair encUnary encB)
  exact (hn.prod (decoder_polyTime.comp (hn.prod hi))).prod
    ((ComputableInPolyTime.snd encUnary encB).comp hs)

/-- Construct the actual native captured callback, retaining width outside the user body.
Only the supplied body's certificate is assumed; decoder/preparation efficiency is proved here. -/
noncomputable def visitCertificate {body : (ℕ × List Bool) × β → β}
    (cb : NativeCertificate body (encPair (encPair encUnary encBits) encB) encB) :
    NativeCertificate (visit body) (encPair encNat (encPair encUnary encB))
      (encPair encUnary encB) :=
  (NativeCertificate.linear ((ComputableInO.fst encUnary encB).comp_linear
    (ComputableInO.snd encNat (encPair encUnary encB)))).prod
    (cb.comp (NativeCertificate.ofPolyTime prepare_polyTime))

/-- A polynomial native body gives a polynomial native visit, in the COMPLETE encoded
index/width/captured-state input. This is a per-visit result, not a whole-loop bound. -/
theorem visitCertificate_isPolynomial {body : (ℕ × List Bool) × β → β}
    (cb : NativeCertificate body (encPair (encPair encUnary encBits) encB) encB)
    (hcb : cb.IsPolynomial) : (visitCertificate cb).IsPolynomial := by
  apply NativeCertificate.prod_isPolynomial
  · exact NativeCertificate.linear_isPolynomial _
  · exact NativeCertificate.comp_isPolynomial cb _ hcb
      (NativeCertificate.ofPolyTime_isPolynomial prepare_polyTime)

/-- A single native machine handles all runtime dimensions. Count construction, initialization,
decoding and captured callback costs are included. The inherited IndexFold bounds retain maximum
live-state/workspace and linear-in-visit-count time; no exponential whole-loop PT claim is made. -/
noncomputable def certificate {α : Type} {encIn : α ↪ List Bool}
    {dimension : α → ℕ} {initial : α → β} {body : (ℕ × List Bool) × β → β}
    (cn : NativeCertificate dimension encIn encUnary)
    (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body (encPair (encPair encUnary encBits) encB) encB) :
    NativeCertificate (fun a => run body (dimension a) (initial a))
      encIn (encPair encNat (encPair encUnary encB)) :=
  IndexFold.certificate (clock.comp cn) (cn.prod ci) (visitCertificate cb)

end Cslib.GenericRAM.BooleanFold

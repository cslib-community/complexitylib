/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Circuits as certificates

A verifier that guesses a circuit reads it from a certificate of a fixed length. This file fixes
such a format for De Morgan circuits with `n` inputs, one output and at most `s` gates, of length
`certLength n s`, monotone in the number of inputs (`certLength_mono_left`). Wire numbers are
below `w = n + s` and are written in unary in fields of `w`
bits (`unaryField`); an operation takes three bits (`Op.bits`). A certificate lists the number of
gates in a field of `s` bits, the output wire, and then `s` rows of `3 + 2 w` bits, the first of
which hold the gates (`certificate`).

Every bit string reads as a list of gates and an output wire (`readCertificate`): a field is read
as its number of ones, any three bits as an operation, and the arguments of a gate are cut to the
arity of its operation. Reading is polynomial-time
(`Cslib.Circuits.Boolean.computableInPolyTime_readCertificate`), and the certificate of a
circuit, followed by any bits, reads as its code (`readCertificate_certificate_append`). A string
that is not the certificate of a circuit may read as gates that read wires not yet computed; the
polynomial-time test `codeCheck` tells the codes of circuits apart (`codeCheck_eq_true_iff`).

## Main definitions

* `Cslib.Circuits.Boolean.Op.ofBits`, `Cslib.Circuits.Boolean.gateRow`,
  `Cslib.Circuits.Boolean.readRow`: 3-bit operation decoding and gate row encoding/decoding.
* `Cslib.Circuits.Boolean.certLength`: the length of certificates.
* `Cslib.Circuits.Boolean.certificate`: the certificate of a circuit code.
* `Cslib.Circuits.Boolean.readCertificate`: the gates and the output wire read from a certificate.
* `Cslib.Circuits.Boolean.codeCheck`: the test for codes of circuits.

## Main results

* `Cslib.Circuits.Boolean.certLength_mono_left`: certificate length is monotone in the input count.
* `Cslib.Circuits.Boolean.length_certificate`: certificates have length `certLength n s`.
* `Cslib.Circuits.Boolean.readCertificate_certificate_append`: a certificate reads as the code of
  its circuit.
* `Cslib.Circuits.Boolean.codeCheck_eq_true_iff`: `codeCheck` tests `Program.IsCodeFrom`.
* `Cslib.Circuits.Boolean.computableInPolyTime_readCertificate`,
  `Cslib.Circuits.Boolean.computableInPolyTime_codeCheck`: reading certificates and checking
  codes are polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-! ### Fields and rows -/

/-- The number `a` in a field of `width` bits: `a` ones, then zeros. -/
def unaryField (width a : ℕ) : List Bool :=
  List.replicate a true ++ List.replicate (width - a) false

/-- A unary field of width `width` for `a ≤ width` has length `width`. -/
@[simp] theorem length_unaryField (width a : ℕ) (h : a ≤ width) :
    (unaryField width a).length = width := by
  simp [unaryField, h]

/-- A unary field of width `width` for `a` contains `a` ones. -/
@[simp] theorem count_unaryField (width a : ℕ) : (unaryField width a).count true = a := by
  simp [unaryField, List.count_replicate]

/-- An operation in three bits. -/
def Op.bits : Op → List Bool
  | .const false => [false, false, false]
  | .const true => [true, false, false]
  | .not => [false, true, false]
  | .and => [true, true, false]
  | .or => [false, false, true]

/-- The 3-bit encoding `op.bits` has length `3`. -/
@[simp] theorem Op.length_bits (op : Op) : op.bits.length = 3 := by
  cases op with
  | const b => cases b <;> rfl
  | _ => rfl

/-- The operation read from any three bits. -/
def Op.ofBits : Bool × Bool × Bool → Op
  | (b, false, false) => .const b
  | (false, true, false) => .not
  | (true, true, false) => .and
  | (_, _, true) => .or

/-- Decoding the three bits of `op.bits` via `Op.ofBits` recovers `op`. -/
theorem Op.ofBits_bits (op : Op) :
    Op.ofBits (op.bits.getD 0 false, op.bits.getD 1 false, op.bits.getD 2 false) = op := by
  cases op with
  | const b => cases b <;> rfl
  | _ => rfl

/-- The row of a gate whose wire numbers are below `width`: its operation, then its first two
arguments in fields of `width` bits. -/
def gateRow (width : ℕ) (g : Op × List ℕ) : List Bool :=
  g.1.bits ++ unaryField width (g.2.getD 0 0) ++ unaryField width (g.2.getD 1 0)

/-- The gate read from a row of `3 + 2 * width` bits, with as many arguments as its operation
takes. -/
def readRow (width : ℕ) (row : List Bool) : Op × List ℕ :=
  (Op.ofBits (row.getD 0 false, row.getD 1 false, row.getD 2 false),
    [((row.drop 3).take width).count true, ((row.drop (3 + width)).take width).count true].take
      (signature.Arity (Op.ofBits (row.getD 0 false, row.getD 1 false, row.getD 2 false))))

private theorem length_gateRow {width : ℕ} {g : Op × List ℕ} (h : ∀ i ∈ g.2, i ≤ width) :
    (gateRow width g).length = 3 + 2 * width := by
  rw [gateRow, List.length_append, List.length_append, Op.length_bits,
    length_unaryField _ _ (List.getD_le_of_forall_le h 0),
    length_unaryField _ _ (List.getD_le_of_forall_le h 1)]
  omega

/-- A row reads as its gate, when the gate has the arity of its operation. -/
private theorem readRow_gateRow {width : ℕ} {g : Op × List ℕ}
    (harity : g.2.length = signature.Arity g.1)
    (h : ∀ i ∈ g.2, i ≤ width) : readRow width (gateRow width g) = g := by
  obtain ⟨op, args⟩ := g
  have h₀ := length_unaryField _ _ (List.getD_le_of_forall_le h 0)
  have h₁ := length_unaryField _ _ (List.getD_le_of_forall_le h 1)
  have hop : ∀ j < 3, (gateRow width (op, args)).getD j false = op.bits.getD j false := by
    intro j hj
    rw [gateRow, List.append_assoc, List.getD_append _ _ _ _ (by simpa using hj)]
  have hdrop₀ : ((gateRow width (op, args)).drop 3).take width =
      unaryField width (args.getD 0 0) := by
    rw [gateRow, List.append_assoc, List.drop_left' (Op.length_bits op),
      List.take_left' h₀]
  have hdrop₁ : ((gateRow width (op, args)).drop (3 + width)).take width =
      unaryField width (args.getD 1 0) := by
    rw [gateRow, List.append_assoc, ← List.drop_drop, List.drop_left' (Op.length_bits op),
      List.drop_left' h₀, List.take_of_length_le h₁.le]
  simp only [readRow, hop 0 (by omega), hop 1 (by omega), hop 2 (by omega), Op.ofBits_bits,
    hdrop₀, hdrop₁, count_unaryField]
  refine Prod.ext rfl ?_
  dsimp only at harity ⊢
  cases op with
  | const b => simp_all
  | not =>
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 harity
    rfl
  | and | or =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 harity
    rfl

/-! ### Certificates -/

/-- The length of the certificates of circuits with `n` inputs and at most `s` gates. -/
def certLength (n s : ℕ) : ℕ := s + (n + s) + s * (3 + 2 * (n + s))

/-- Certificate length is monotone in the number of inputs. -/
theorem certLength_mono_left {m n : ℕ} (h : m ≤ n) (s : ℕ) : certLength m s ≤ certLength n s := by
  unfold certLength
  gcongr

/-- The certificate of a circuit with `n` inputs and at most `s` gates, given by its gate list and
its output wire: the number of gates and the output wire in fields of `s` and `n + s` bits, the
rows of the gates, and rows of zeros up to `s` rows. -/
def certificate (n s : ℕ) (gates : List (Op × List ℕ)) (output : ℕ) : List Bool :=
  unaryField s gates.length ++ unaryField (n + s) output ++ gates.flatMap (gateRow (n + s)) ++
    List.replicate ((s - gates.length) * (3 + 2 * (n + s))) false

/-- The gates and the output wire read from a certificate for circuits with `n` inputs and at
most `s` gates. Every bit string reads as some gates and some wire. -/
def readCertificate (n s : ℕ) (w : List Bool) : List (Op × List ℕ) × ℕ :=
  ((BitString.listRows ((w.take s).count true) (3 + 2 * (n + s)) (w.drop (s + (n + s)))).map
    (readRow (n + s)), ((w.drop s).take (n + s)).count true)

/-- A certificate reads as at most `s` gates. -/
theorem length_readCertificate_le (n s : ℕ) (w : List Bool) :
    (readCertificate n s w).1.length ≤ s := by
  simpa [readCertificate] using (List.count_le_length ..).trans (List.length_take_le s w)

/-- The certificate of a circuit has length `certLength n s`. -/
theorem length_certificate {n s : ℕ} {gates : List (Op × List ℕ)} {output : ℕ}
    (hs : gates.length ≤ s) (houtput : output ≤ n + s)
    (hgates : ∀ g ∈ gates, ∀ i ∈ g.2, i ≤ n + s) :
    (certificate n s gates output).length = certLength n s := by
  have hrows : (gates.flatMap (gateRow (n + s))).length = gates.length * (3 + 2 * (n + s)) := by
    rw [List.length_flatMap, List.map_congr_left fun g hg => length_gateRow (hgates g hg),
      List.map_const', List.sum_replicate, smul_eq_mul]
  rw [certificate, List.length_append, List.length_append, List.length_append, hrows,
    length_unaryField _ _ hs, length_unaryField _ _ houtput, List.length_replicate, certLength,
    Nat.add_assoc _ (gates.length * _), ← Nat.add_mul, Nat.add_sub_cancel' hs]

/-- **A certificate reads as the code of its circuit**, whatever bits follow it. -/
theorem readCertificate_certificate_append {n s : ℕ} {gates : List (Op × List ℕ)} {output : ℕ}
    (hcode : Program.IsCodeFrom signature n 0 gates) (hs : gates.length ≤ s)
    (houtput : output ≤ n + s) (extra : List Bool) :
    readCertificate n s (certificate n s gates output ++ extra) = (gates, output) := by
  have hgate (j : ℕ) (hj : j < gates.length) :
      gates[j].2.length = signature.Arity gates[j].1 ∧ ∀ i ∈ gates[j].2, i ≤ n + s := by
    obtain ⟨h₁, h₂⟩ := hcode.getElem j hj
    exact ⟨h₁, fun i hi => by have := h₂ i hi; omega⟩
  have hgates : ∀ g ∈ gates, ∀ i ∈ g.2, i ≤ n + s := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact (hgate j hj).2
  have hk := length_unaryField _ _ hs
  have ho := length_unaryField _ _ houtput
  simp only [readCertificate, certificate, List.append_assoc]
  rw [List.take_left' hk, count_unaryField, ← List.drop_drop, List.drop_left' hk,
    List.take_left' ho, count_unaryField, List.drop_left' ho]
  refine Prod.ext ?_ rfl
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [BitString.listRows, List.getElem_map, List.getElem_range]
  rw [BitString.listRow_flatMap_append _ _ (fun g hg => length_gateRow (hgates g hg)) _ j h₂,
    readRow_gateRow (hgate j h₂).1 (hgate j h₂).2]

/-- **The certificate of a circuit** with at most `s` gates reads as its code. -/
theorem readCertificate_certificate_code_append {n s : ℕ} (c : Circuit signature n 1)
    (hs : c.size ≤ s) (extra : List Bool) :
    readCertificate n s (certificate n s c.code.1 (c.outputs 0).toNat ++ extra) =
      (c.code.1, (c.outputs 0).toNat) := by
  have hcode : Program.IsCodeFrom signature n 0 c.code.1 := by
    rw [← Program.isSome_ofCode_iff, Circuit.code, Program.ofCode_code]
    rfl
  exact readCertificate_certificate_append hcode (by rw [Circuit.length_code_fst]; exact hs)
    (by have := (c.outputs 0).toNat_lt; omega) extra

/-- The certificate of a circuit with at most `s` gates has length `certLength n s`. -/
theorem length_certificate_code {n s : ℕ} (c : Circuit signature n 1) (hs : c.size ≤ s) :
    (certificate n s c.code.1 (c.outputs 0).toNat).length = certLength n s := by
  have hcode : Program.IsCodeFrom signature n 0 c.code.1 := by
    rw [← Program.isSome_ofCode_iff, Circuit.code, Program.ofCode_code]
    rfl
  refine length_certificate (by rw [Circuit.length_code_fst]; exact hs)
    (by have := (c.outputs 0).toNat_lt; omega) ?_
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have := (hcode.getElem j hj).2 i hi
  have : j < c.size := by rwa [Circuit.length_code_fst] at hj
  omega

/-! ### Checking codes -/

/-- Whether a list of gates is the code of a program on `n` inputs (`Program.IsCodeFrom`), as a
Boolean test: every entry has the arity of its operation and reads only inputs and earlier
gates. -/
def codeCheck (n : ℕ) (gates : List (Op × List ℕ)) : Bool :=
  gates.zipIdx.all fun g => decide (g.1.2.length = signature.Arity g.1.1) && g.1.2.all (· < n + g.2)

private theorem all_zipIdx_eq_true_iff {n : ℕ} (k : ℕ) (gates : List (Op × List ℕ)) :
    ((gates.zipIdx k).all fun g =>
      decide (g.1.2.length = signature.Arity g.1.1) && g.1.2.all (· < n + g.2)) = true ↔
      Program.IsCodeFrom signature n k gates := by
  induction gates generalizing k with
  | nil => simp [Program.IsCodeFrom]
  | cons g gates ih =>
    rw [List.zipIdx_cons, List.all_cons, Bool.and_eq_true, ih, Program.isCodeFrom_cons]
    simp

/-- `codeCheck n gates` returns `true` iff `gates` is a valid program code on `n` inputs. -/
theorem codeCheck_eq_true_iff {n : ℕ} {gates : List (Op × List ℕ)} :
    codeCheck n gates = true ↔ Program.IsCodeFrom signature n 0 gates :=
  all_zipIdx_eq_true_iff 0 gates

/-! ### Reading certificates in polynomial time -/

open ComputableInPolyTime

/-- Reading a gate from a row is polynomial-time, for the field width in unary. -/
private theorem computableInPolyTime_readRow :
    ComputableInPolyTime (fun p : ℕ × List Bool => readRow p.1 p.2)
      (encPair encUnary encBits) encGate := by
  have hop : ComputableInPolyTime (fun p : ℕ × List Bool =>
      Op.ofBits (p.2.getD 0 false, p.2.getD 1 false, p.2.getD 2 false))
      (encPair encUnary encBits) encOp :=
    (of_finite (encIn := encPair encBool (encPair encBool encBool)) Op.ofBits).comp (by fun_prop)
  have hc₀ : ComputableInPolyTime (fun p : ℕ × List Bool =>
      ((p.2.drop 3).take p.1).count true) (encPair encUnary encBits) encNat :=
    unary_to_binary.comp (by fun_prop)
  have hc₁ : ComputableInPolyTime (fun p : ℕ × List Bool =>
      ((p.2.drop (3 + p.1)).take p.1).count true) (encPair encUnary encBits) encNat :=
    unary_to_binary.comp (by fun_prop)
  unfold readRow
  refine finite_cases (tagEncoding := encOp) (branch := fun op p => (op,
    [((p.2.drop 3).take p.1).count true, ((p.2.drop (3 + p.1)).take p.1).count true].take
      (signature.Arity op))) hop fun op => (const op).prod ?_
  cases op with
  | const b => exact const []
  | not => exact cons' hc₀ (const [])
  | and | or => exact cons' hc₀ (cons' hc₁ (const []))

/-- Checking that a list of gates is a code is polynomial-time, with the number of inputs in
unary. -/
@[fun_prop]
theorem computableInPolyTime_codeCheck {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {gates : γ → List (Op × List ℕ)} (hn : ComputableInPolyTime n encIn encUnary)
    (hgates : ComputableInPolyTime gates encIn (encList encGate)) :
    ComputableInPolyTime (fun a => codeCheck (n a) (gates a)) encIn encBool := by
  have harity : ComputableInPolyTime (fun op : Op => signature.Arity op) encOp encUnary :=
    of_finite _
  have hbound : ComputableInPolyTime (fun p : (γ × ((Op × List ℕ) × ℕ)) × ℕ =>
      decide (p.2 < n p.1.1 + p.1.2.2))
      (encPair (encPair encIn (encPair encGate encUnary)) encNat) encBool :=
    binary_lt' (snd _ _) (unary_to_binary.comp (by fun_prop))
  have hzip : ComputableInPolyTime (fun a => (gates a).zipIdx)
      encIn (encList (encPair encGate encUnary)) := by fun_prop
  unfold codeCheck
  exact allWithInput hzip (bool_and'
    (decide_eq' (by fun_prop) (harity.comp (by fun_prop))) (allWithInput (by fun_prop) hbound))

/-- **Reading certificates is polynomial-time**, for the number of inputs and the number of gates
in unary. -/
@[fun_prop]
theorem computableInPolyTime_readCertificate {γ : Type} {encIn : γ ↪ List Bool}
    {n s : γ → ℕ} {w : γ → List Bool} (hn : ComputableInPolyTime n encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun a => readCertificate (n a) (s a) (w a)) encIn
      (encPair (encList encGate) encNat) := by
  unfold readCertificate
  have hk : ComputableInPolyTime (fun a => ((w a).take (s a)).count true) encIn encUnary :=
    bitsCountWithInput (bitsTakeWithInput hw hs) (const true)
  have hwidth : ComputableInPolyTime (fun a => 3 + 2 * (n a + s a)) encIn encUnary := by
    fun_prop
  have hdrop : ComputableInPolyTime (fun a => (w a).drop (s a + (n a + s a))) encIn encBits :=
    bitsDropWithInput hw (by fun_prop)
  have hrows : ComputableInPolyTime (fun a => BitString.listRows (((w a).take (s a)).count
      true) (3 + 2 * (n a + s a)) ((w a).drop (s a + (n a + s a)))) encIn (encList encBits) :=
    bitsRowsWithInput hk hwidth hdrop
  have hout : ComputableInPolyTime (fun a => (((w a).drop (s a)).take (n a + s a)).count true)
      encIn encUnary :=
    bitsCountWithInput (bitsTakeWithInput (bitsDropWithInput hw hs) (by fun_prop)) (const true)
  have hpair : ComputableInPolyTime (fun p : γ × List Bool => (n p.1 + s p.1, p.2))
      (encPair encIn encBits) (encPair encUnary encBits) := by
    fun_prop
  exact (mapWithInput hrows (computableInPolyTime_readRow.comp hpair)).prod
    (unary_to_binary.comp hout)

end Cslib.Circuits.Boolean

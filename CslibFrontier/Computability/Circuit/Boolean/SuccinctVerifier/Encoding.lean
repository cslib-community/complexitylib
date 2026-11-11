/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SuccinctVerifier
public import CslibFrontier.Computability.Circuit.Boolean.Encoding.Certificate
public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi

/-!
# Succinct witness verification from bounded circuit certificates

`certificateCircuit D s w` constructs a circuit detecting a violated clause of the succinct
formula decoded by `D`, using the circuit described by the certificate `w` as its assignment.
The certificate format is the existing `Boolean.readCertificate`, with `r` inputs and at most
`s` gates. Malformed certificates produce the constant-true circuit: an unsatisfiability test
therefore rejects them. No promise on the guessed bit string is needed.

The uniform constructor is certified on the native multitape model by
`computableInPolyTime_certificateCircuit`. It takes polynomial-time computations of the unary
widths and gate budget and of the decoder code; it does not enumerate clauses or assignments.

The clause-index input width stays unchanged, and the output circuit has at most
`D.size + 3 * s + 17` gates. There exists a certificate of exactly `Boolean.certLength r s`
bits producing an unsatisfiable output exactly when a size-at-most-`s` circuit supplies a
satisfying assignment of `toCNF D`.

This is the bounded-certificate implementation of the violated-clause verification in
[Williams2010], the proof of Theorem 3.2. It does not by itself establish a time-hierarchy
contradiction or the easy-witness theorem.

## Main definitions

* `decodeCertificate`: parse a bounded certificate as a typed single-output circuit.
* `certificateCircuit`: a total violated-clause circuit constructor, rejecting malformed
  certificates through a satisfiable output.
* `badClauseCode`, `certificateCircuitCode`: the corresponding uniform operations on raw codes.

## Main results

* `size_certificateCircuit_le`: the decoder plus three witness copies and seventeen gates.
* `exists_not_mem_CircuitSAT_certificateCircuit_iff`: exact-length guessed certificates suffice
  exactly for formulas with a small satisfying witness circuit.
* `computableInPolyTime_certificateCircuit`: native polynomial-time construction for varying
  widths, decoder codes and certificate strings.

## References

* [R. Williams, *Improving Exhaustive Search Implies Superpolynomial Lower Bounds*][Williams2010],
  author's May 4, 2010 version, proof of Theorem 3.2.
-/

public section

namespace Cslib.Circuits.Boolean.SuccinctVerifier

open Cslib.Complexity

/-- Read the existing bounded circuit-certificate format, and reject invalid wire references. -/
@[expose] def decodeCertificate (r s : ℕ) (w : List Bool) :
    Option (Circuit signature r 1) :=
  let (gates, output) := readCertificate r s w
  Circuit.ofCode r 1 (gates, [output])

/-- Every successfully decoded certificate describes a circuit of at most the gate budget. -/
theorem size_le_of_decodeCertificate_eq_some {r s : ℕ} {w : List Bool}
    {W : Circuit signature r 1} (h : decodeCertificate r s w = some W) : W.size ≤ s := by
  have hc := Circuit.code_of_ofCode_eq_some h
  calc W.size = (readCertificate r s w).1.length := by
        rw [← Circuit.length_code_fst, hc]
        rfl
    _ ≤ s := length_readCertificate_le r s w

/-- A canonical certificate recovers its circuit, ignoring any trailing bits. -/
theorem decodeCertificate_certificate_append {r s : ℕ} (W : Circuit signature r 1)
    (hs : W.size ≤ s) (extra : List Bool) :
    decodeCertificate r s (certificate r s W.code.1 (W.outputs 0).toNat ++ extra) = some W := by
  rw [decodeCertificate, readCertificate_certificate_code_append W hs extra]
  dsimp only
  have hcode : (W.code.1, [(W.outputs 0).toNat]) = W.code := by
    simp [Circuit.code, List.ofFn_succ]
  rw [hcode, Circuit.ofCode_code]

/-- The violated-clause circuit of a certificate; invalid certificates produce constant true,
so they cannot pass an unsatisfiability test. -/
@[expose] def certificateCircuit {q r : ℕ} (D : Circuit signature q (3 * (r + 1)))
    (s : ℕ) (w : List Bool) : Circuit signature q 1 :=
  match decodeCertificate r s w with
  | some W => badClause D W
  | none => Circuit.oneGate (.const true) Fin.elim0

/-- A valid certificate produces its witness circuit's violated-clause circuit. -/
theorem certificateCircuit_of_decode_eq_some {q r s : ℕ}
    (D : Circuit signature q (3 * (r + 1))) {w : List Bool} {W : Circuit signature r 1}
    (h : decodeCertificate r s w = some W) : certificateCircuit D s w = badClause D W := by
  simp [certificateCircuit, h]

/-- A malformed certificate always produces a satisfiable circuit. -/
theorem mem_CircuitSAT_certificateCircuit_of_decode_eq_none {q r s : ℕ}
    (D : Circuit signature q (3 * (r + 1))) {w : List Bool}
    (h : decodeCertificate r s w = none) :
    (⟨q, certificateCircuit D s w⟩ : Σ n, Circuit signature n 1) ∈ CircuitSAT := by
  refine ⟨fun _ => false, ?_⟩
  simp [certificateCircuit, h, interpretation]

/-- Compiling any bit string costs the decoder plus three budgeted witness copies and seventeen
Boolean gates; malformed certificates cost only one gate. -/
theorem size_certificateCircuit_le {q r : ℕ} (D : Circuit signature q (3 * (r + 1)))
    (s : ℕ) (w : List Bool) : (certificateCircuit D s w).size ≤ D.size + 3 * s + 17 := by
  cases h : decodeCertificate r s w with
  | none => simp [certificateCircuit, h]
  | some W =>
    rw [certificateCircuit_of_decode_eq_some D h, size_badClause]
    have := size_le_of_decodeCertificate_eq_some h
    omega

/-- A compiled certificate is unsatisfiable exactly when it decodes to a witness circuit whose
truth table satisfies every decoded clause. -/
theorem not_mem_CircuitSAT_certificateCircuit_iff {q r : ℕ}
    (D : Circuit signature q (3 * (r + 1))) (s : ℕ) (w : List Bool) :
    (⟨q, certificateCircuit D s w⟩ : Σ n, Circuit signature n 1) ∉ CircuitSAT ↔
      ∃ W : Circuit signature r 1, decodeCertificate r s w = some W ∧
        (toCNF D).eval (fun y => W.eval interpretation y 0) = true := by
  cases h : decodeCertificate r s w with
  | none =>
    exact iff_of_false
      (fun hn => hn (mem_CircuitSAT_certificateCircuit_of_decode_eq_none D h))
      (by simp)
  | some W =>
    rw [certificateCircuit_of_decode_eq_some D h, not_mem_CircuitSAT_badClause_iff]
    simp

/-- Guessing exactly `certLength r s` bits and testing the compiled circuit for unsatisfiability
finds a witness precisely when the succinct formula has a satisfying circuit of at most `s`
gates. The certificate is a circuit description, not the exponential truth table. -/
theorem exists_not_mem_CircuitSAT_certificateCircuit_iff {q r : ℕ}
    (D : Circuit signature q (3 * (r + 1))) (s : ℕ) :
    (∃ w : List Bool, w.length = certLength r s ∧
      (⟨q, certificateCircuit D s w⟩ : Σ n, Circuit signature n 1) ∉ CircuitSAT) ↔
      ∃ W : Circuit signature r 1, W.size ≤ s ∧
        (toCNF D).eval (fun y => W.eval interpretation y 0) = true := by
  constructor
  · rintro ⟨w, _, hw⟩
    obtain ⟨W, hW, hsat⟩ := (not_mem_CircuitSAT_certificateCircuit_iff D s w).1 hw
    exact ⟨W, size_le_of_decodeCertificate_eq_some hW, hsat⟩
  · rintro ⟨W, hsize, hsat⟩
    refine ⟨certificate r s W.code.1 (W.outputs 0).toNat,
      length_certificate_code W hsize, ?_⟩
    apply (not_mem_CircuitSAT_certificateCircuit_iff D s _).2
    refine ⟨W, ?_, hsat⟩
    simpa using decodeCertificate_certificate_append W hsize []

/-! ### Uniform construction on circuit codes -/

/-- The code-level bad-clause constructor. It rewires the witness code three times after the
shared decoder, then appends the fixed seventeen-gate violation test. All wire indices use
the existing binary encoding of circuit codes. -/
@[expose] def badClauseCode (q r : ℕ) (decoder witness : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  compCode q
    (compCode (3 * (r + 1)) violationTest.toCircuit.code
      (appendCode (3 * (r + 1))
        (appendCodes (3 * (r + 1)) (List.ofFn fun j : Fin 3 =>
          compCode (3 * (r + 1)) witness
            ([], (List.range r).map fun i => j.val * (r + 1) + i)))
        ([], List.ofFn fun j : Fin 3 => j.val * (r + 1) + r))) decoder

/-- The raw construction agrees exactly with the typed bad-clause circuit. -/
theorem badClauseCode_code {q r : ℕ} (D : Circuit signature q (3 * (r + 1)))
    (W : Circuit signature r 1) : badClauseCode q r D.code W.code = (badClause D W).code := by
  have haddress (j : Fin 3) :
      ([], (List.range r).map fun i => j.val * (r + 1) + i) =
        (Circuit.wiring signature (addressWire r j)).code :=
    (Circuit.code_wiring_eq_map fun _ => rfl).symm
  have hsign : ([], List.ofFn fun j : Fin 3 => j.val * (r + 1) + r) =
      (Circuit.wiring signature (signWire r)).code := rfl
  simp only [badClauseCode, haddress, hsign, compCode_code, appendCodes_code, appendCode_code]
  rfl

/-- The existing certificate parser accepts exactly the codes whose gates and output wire
pass the existing circuit-code validity checks. -/
theorem isSome_decodeCertificate_iff (r s : ℕ) (w : List Bool) :
    (decodeCertificate r s w).isSome ↔
      codeCheck signature r (readCertificate r s w).1 = true ∧
        (readCertificate r s w).2 < r + (readCertificate r s w).1.length := by
  change (Circuit.ofCode r 1 ((readCertificate r s w).1,
    [(readCertificate r s w).2]) : Option (Circuit signature r 1)).isSome ↔ _
  rw [Circuit.isSome_ofCode_iff, codeCheck_eq_true_iff]
  simp

/-- The complete certificate-to-checker compiler on raw data, including the invalid-certificate
branch. The constant-true output uses the first gate wire, numbered by the input count `q`. -/
@[expose] def certificateCircuitCode (q r s : ℕ) (decoder : List (Op × List ℕ) × List ℕ)
    (w : List Bool) : List (Op × List ℕ) × List ℕ :=
  let (gates, output) := readCertificate r s w
  if codeCheck signature r gates && decide (output < r + gates.length) then
    badClauseCode q r decoder (gates, [output])
  else ([((.const true : Op), [])], [q])

/-- The total raw compiler is the code of the total typed compiler. -/
theorem certificateCircuitCode_code {q r : ℕ} (D : Circuit signature q (3 * (r + 1)))
    (s : ℕ) (w : List Bool) :
    certificateCircuitCode q r s D.code w = (certificateCircuit D s w).code := by
  cases h : decodeCertificate r s w with
  | none =>
    have hcheck : ¬(codeCheck signature r (readCertificate r s w).1 = true ∧
        (readCertificate r s w).2 < r + (readCertificate r s w).1.length) := by
      rw [← isSome_decodeCertificate_iff, h]
      simp
    simp only [certificateCircuitCode, Bool.and_eq_true, decide_eq_true_eq,
      ite_eq_right hcheck, certificateCircuit, h]
    rfl
  | some W =>
    have hcheck : codeCheck signature r (readCertificate r s w).1 = true ∧
        (readCertificate r s w).2 < r + (readCertificate r s w).1.length := by
      rw [← isSome_decodeCertificate_iff, h]
      simp
    have hcode : W.code = ((readCertificate r s w).1, [(readCertificate r s w).2]) :=
      Circuit.code_of_ofCode_eq_some h
    simp only [certificateCircuitCode, Bool.and_eq_true, decide_eq_true_eq, ite_eq_left hcheck]
    rw [← hcode, badClauseCode_code, certificateCircuit_of_decode_eq_some D h]

open Turing.MultiTapeTM ComputableInPolyTime

/-- The raw bad-clause constructor is polynomial-time, uniformly in both widths. The variable
address width is unary because the constructor writes that many input-wire references. -/
theorem computableInPolyTime_badClauseCode {α : Type} {enc : α ↪ List Bool}
    {q r : α → ℕ} {decoder witness : α → List (Op × List ℕ) × List ℕ}
    (hq : ComputableInPolyTime q enc encNat)
    (hr : ComputableInPolyTime r enc encUnary)
    (hdecoder : ComputableInPolyTime decoder enc encCode)
    (hwitness : ComputableInPolyTime witness enc encCode) :
    ComputableInPolyTime (fun a => badClauseCode (q a) (r a) (decoder a) (witness a))
      enc encCode := by
  have hrb := unary_to_binary.comp hr
  have hwidth : ComputableInPolyTime (fun a => 3 * (r a + 1)) enc encNat := by fun_prop
  have haddress (j : Fin 3) : ComputableInPolyTime
      (fun a => ([], (List.range (r a)).map fun i => j.val * (r a + 1) + i)) enc encCode := by
    refine (const []).prod (mapWithInput (range.comp hr) ?_)
    have hr' := hrb.comp (fst enc encUnary)
    have hi := unary_to_binary.comp (snd enc encUnary)
    fun_prop
  have hsign : ComputableInPolyTime
      (fun a => ([], List.ofFn fun j : Fin 3 => j.val * (r a + 1) + r a)) enc encCode := by
    refine (const []).prod (ofFn fun j => ?_)
    fun_prop
  exact computableInPolyTime_compCode hq
    (computableInPolyTime_compCode hwidth (const violationTest.toCircuit.code)
      (computableInPolyTime_appendCode hwidth
        (computableInPolyTime_appendCodes hwidth (ofFn fun j =>
          computableInPolyTime_compCode hwidth hwitness (haddress j))) hsign)) hdecoder

/-- The raw certificate compiler is polynomial-time in the decoder code, certificate, and the
unary widths and gate budget, including checking all malformed descriptions. -/
theorem computableInPolyTime_certificateCircuitCode {α : Type} {enc : α ↪ List Bool}
    {q r s : α → ℕ} {decoder : α → List (Op × List ℕ) × List ℕ} {w : α → List Bool}
    (hq : ComputableInPolyTime q enc encNat)
    (hr : ComputableInPolyTime r enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary)
    (hdecoder : ComputableInPolyTime decoder enc encCode)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime
      (fun a => certificateCircuitCode (q a) (r a) (s a) (decoder a) (w a)) enc encCode := by
  have hread := computableInPolyTime_readCertificate hr hs hw
  have hgate := hread.fst'
  have hout := hread.snd'
  have hrb := unary_to_binary.comp hr
  have hlen := (length_list_binary encGate).comp hgate
  have hcheck : ComputableInPolyTime (fun a => codeCheck signature (r a)
      (readCertificate (r a) (s a) (w a)).1 && decide
        ((readCertificate (r a) (s a) (w a)).2 <
          r a + (readCertificate (r a) (s a) (w a)).1.length)) enc encBool := by
    have hc := computableInPolyTime_codeCheck hr hgate
    fun_prop
  exact hcheck.ite
    (computableInPolyTime_badClauseCode hq hr hdecoder (hgate.prod (hout.cons' (const []))))
    ((const [((.const true : Op), [])]).prod (hq.cons' (const [])))

/-- **Uniform native construction of the checker.** Supply polynomial-time computations of the
input count, variable-address width, gate budget, decoder code and guessed certificate. The
output uses the standard `Boolean.encCircuit` encoding, with a unary input count and binary wire
indices. Neither the expanded CNF nor the witness truth table is constructed. -/
theorem computableInPolyTime_certificateCircuit {α : Type} {enc : α ↪ List Bool}
    {q r s : α → ℕ} {D : (a : α) → Circuit signature (q a) (3 * (r a + 1))}
    {w : α → List Bool}
    (hq : ComputableInPolyTime q enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary)
    (hD : ComputableInPolyTime (fun a => (D a).code) enc encCode)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime
      (fun a => (⟨q a, certificateCircuit (D a) (s a) (w a)⟩ : Σ n, Circuit signature n 1))
      enc (encCircuit 1) := by
  have hcode := computableInPolyTime_certificateCircuitCode
    (unary_to_binary.comp hq) hr hs hD hw
  exact (hq.prod hcode).of_enc_eq fun a => by
    rw [encCircuit_apply, certificateCircuitCode_code]

end Cslib.Circuits.Boolean.SuccinctVerifier

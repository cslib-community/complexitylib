module

import CslibFrontier.Computability.Circuit.Boolean.SuccinctVerifier.Encoding

-- Regression tests intentionally export no declarations.
set_option linter.privateModule false

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Cslib.Circuits.Boolean.SuccinctVerifier Turing.MultiTapeTM

namespace CslibFrontierTests.SuccinctVerifierEncoding

private def trueWitness : Circuit signature 0 1 :=
  Circuit.oneGate (.const true) Fin.elim0

private def falseWitness : Circuit signature 0 1 :=
  Circuit.oneGate (.const false) Fin.elim0

private def positiveClause : Circuit signature 0 (3 * (0 + 1)) :=
  Circuit.pi fun _ => trueWitness

private theorem certificate_trueWitness :
    certificate 0 1 trueWitness.code.1 (trueWitness.outputs 0).toNat =
      [true, false, true, false, false, false, false] := by decide

private theorem certificate_falseWitness :
    certificate 0 1 falseWitness.code.1 (falseWitness.outputs 0).toNat =
      [true, false, false, false, false, false, false] := by decide

-- The unique variable is required to be true; its seven-bit certificate is parsed exactly.
example : decodeCertificate 0 1 [true, false, true, false, false, false, false] =
    some trueWitness := by
  simpa only [List.append_nil, certificate_trueWitness] using
    decodeCertificate_certificate_append (s := 1) trueWitness (by decide) []

-- No zero-gate circuit exists at input width zero. In particular the empty guess is rejected.
example : decodeCertificate 0 0 [] = none := by rfl

example : (⟨0, certificateCircuit (r := 0) positiveClause 0 []⟩ : Σ n, Circuit signature n 1) ∈
    CircuitSAT :=
  mem_CircuitSAT_certificateCircuit_of_decode_eq_none (r := 0) positiveClause (by rfl)

-- A NOT gate referring to its own output is an invalid circuit, rather than an accepting guess.
example : decodeCertificate 0 1 [true, false, false, true, false, false, false] = none := by rfl

-- Zero gates are allowed when an actual input wire is available.
example : decodeCertificate 1 0 [false] = some (Circuit.wiring signature id) := by
  have hcert : certificate 1 0 (Circuit.wiring signature id : Circuit signature 1 1).code.1
      ((Circuit.wiring signature id : Circuit signature 1 1).outputs 0).toNat = [false] := by decide
  simpa only [List.append_nil, hcert] using decodeCertificate_certificate_append (s := 0)
    (Circuit.wiring signature id : Circuit signature 1 1) (by decide) []

-- A real satisfying witness is accepted by the compiled UNSAT test.
example : (⟨0, certificateCircuit (r := 0) positiveClause 1
    [true, false, true, false, false, false, false]⟩ : Σ n, Circuit signature n 1) ∉
    CircuitSAT := by
  rw [not_mem_CircuitSAT_certificateCircuit_iff]
  refine ⟨trueWitness, ?_, ?_⟩
  · simpa only [List.append_nil, certificate_trueWitness] using
      decodeCertificate_certificate_append (s := 1) trueWitness (by decide) []
  · decide

-- A well-formed but incorrect constant-false witness produces a violated clause.
example : (⟨0, certificateCircuit (r := 0) positiveClause 1
    [true, false, false, false, false, false, false]⟩ : Σ n, Circuit signature n 1) ∈
    CircuitSAT := by
  have hdecode : decodeCertificate 0 1 [true, false, false, false, false, false, false] =
      some falseWitness := by
    simpa only [List.append_nil, certificate_falseWitness] using
      decodeCertificate_certificate_append (s := 1) falseWitness (by decide) []
  rw [certificateCircuit_of_decode_eq_some positiveClause hdecode]
  refine ⟨fun _ => false, ?_⟩
  rw [eval_badClause]
  decide

-- The raw and typed constructors agree on invalid certificates too.
example : certificateCircuitCode 0 0 0 positiveClause.code [] =
    ([((.const true : Op), [])], [0]) := by decide

-- The native constructor is uniform in the guessed bits and does not expand the truth table.
example : ComputableInPolyTime
    (fun w : List Bool => (⟨0, certificateCircuit (r := 0) positiveClause 1 w⟩ :
      Σ n, Circuit signature n 1)) encBits (encCircuit 1) :=
  computableInPolyTime_certificateCircuit
    (ComputableInPolyTime.const 0) (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.const 1) (ComputableInPolyTime.const positiveClause.code)
    (by fun_prop)

end CslibFrontierTests.SuccinctVerifierEncoding

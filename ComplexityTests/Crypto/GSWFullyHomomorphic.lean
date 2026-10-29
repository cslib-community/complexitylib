/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.FullyHomomorphic

/-!
Clients of the concrete GSW endpoints. The base widths are computed at security parameter zero.
Under the stated assumptions, the leveled scheme for a constant depth family and the fixed-key
scheme both evaluate the actual compiled NAND circuit correctly on fresh encryptions. The
decision-LWE and circular-security premises remain hypotheses; nothing here instantiates them.
-/

namespace ComplexityTests.Crypto.GSWFullyHomomorphic

open Cslib Cslib.Crypto Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.Homomorphic
open Cslib.Crypto.Homomorphic.GSW Cslib.Crypto.Homomorphic.GSW.DepthParameters
open Cslib.Probability Turing.MultiTapeTM
open Parameters (dimension noise)

-- At security parameter zero the base secret holds one 65536-bit residue, and a ciphertext is a
-- square bit matrix with `2 * 65536` rows. The leveled widths add only an endpoint secret pair
-- and a tag, whatever the depth budget.
example : secretWidth 0 = 65536 ∧ ciphertextWidth 0 = 131072 ^ 2 ∧
    3 * secretWidth 0 + 1 = 196609 := by
  decide +kernel

/-- For any polynomial-time unary budget family and strict-PPT leveled adversary, the composed
decision-LWE distinguisher for the leveled GSW reduction is native strict PPT. -/
example {budget : ℕ → ℕ} (hbudget : ComputableInPolyTime budget encUnary encUnary)
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT) :
    IsPPT encBool
      (lweDistinguisher dimension samples width
        (Leveled.leveledAdversary scheme (fun k => 2 * budget k) secretWidth adversary)) :=
  GSW.isPPT_lweDistinguisher Parameters.computableInPolyTime_dimension
    computableInPolyTime_samples computableInPolyTime_width
    (isPPT_leveledAdversary hbudget hadversary)

/-- Under decision LWE alone, one leveled scheme evaluates the compiled NAND circuit, whose
depth is two, on all supported fresh encryptions. -/
example (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k))) :
    ∃ budget : ℕ → ℕ, ∀ k keys,
      keys ∈ (ProbComp.eval ((Leveled.scheme decryptionCircuits budget).keyGen k)).support →
      ∀ a b inputs, (Leveled.scheme decryptionCircuits budget).FreshInputs k keys.1 [a, b] inputs →
      ∀ c ∈ (ProbComp.eval
          ((Leveled.scheme decryptionCircuits budget).evaluate k keys.1 ⟨2, nandCircuit⟩
            inputs)).support,
        (Leveled.scheme decryptionCircuits budget).decrypt k keys.2 c = !(a && b) := by
  obtain ⟨-, -, -, -, -, -, -, hleveled⟩ := exists_leveled_of_decisionLWE hLWE
  obtain ⟨budget, -, -, -, hcorrect, hpermitted, -⟩ := hleveled _ (PolynomiallyBounded.const 2)
  refine ⟨budget, fun k keys hkeys a b inputs hinputs c hc => ?_⟩
  have h := hcorrect.decrypt_evaluate k keys hkeys ⟨2, nandCircuit⟩
    (hpermitted k _ (by decide +kernel)) [a, b] inputs rfl hinputs c hc
  rw [h, eval_nandCircuit]
  rfl

/-- The schemes for two different depth families share one decryption algorithm, computed by one
uniformly generated polynomial-size circuit family chosen before either depth, as in Gentry's
Definition 3. -/
example (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k))) :
    ∃ circuits : ∀ k, Circuit Boolean.signature
        ((3 * secretWidth k + 1) + (ciphertextWidth k + 1)) 1,
      ComputableInPolyTime
        (fun k => (⟨_, circuits k⟩ : Σ m, Circuit Boolean.signature m 1))
        encUnary (Boolean.encCircuit 1) ∧
      PolynomiallyBounded (fun k => (circuits k).size) ∧
      ∃ shallow deep : ℕ → ℕ, (∀ k, 2 ≤ shallow k ∧ k ≤ deep k) ∧
        (Leveled.scheme decryptionCircuits shallow).decrypt =
          (Leveled.scheme decryptionCircuits deep).decrypt ∧
        ∀ k sk c, sk.length = 3 * secretWidth k + 1 → c.length = ciphertextWidth k + 1 →
          (circuits k).eval Boolean.interpretation
              (BitString.ofList ((3 * secretWidth k + 1) + (ciphertextWidth k + 1)) (sk ++ c)) 0 =
            (Leveled.scheme decryptionCircuits deep).decrypt k sk c := by
  obtain ⟨circuits, hgen, hsize, hcircuits, -, -, -, hleveled⟩ :=
    exists_leveled_of_decisionLWE hLWE
  obtain ⟨shallow, -, hshallow, hdecShallow, -⟩ := hleveled _ (PolynomiallyBounded.const 2)
  obtain ⟨deep, -, hdeep, hdecDeep, -⟩ := hleveled _ PolynomiallyBounded.id
  refine ⟨circuits, hgen, hsize, shallow, deep, fun k => ⟨hshallow k, hdeep k⟩,
    hdecShallow.trans hdecDeep.symm, fun k sk c hsk hc => ?_⟩
  rw [hdecDeep]
  exact hcircuits k sk c hsk hc

/-- With the additional circular-security premise, the fixed-key scheme permits the NAND circuit
at every security parameter and evaluates it correctly, with no depth budget in key generation. -/
example (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k)))
    (hcircular : Encryption.CircularSecure scheme.keyGen scheme.encrypt) (k : ℕ)
    (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval ((FixedKey.scheme decryptionCircuits).keyGen k)).support)
    (a b : Bool) (inputs : List (List Bool))
    (hinputs : (FixedKey.scheme decryptionCircuits).FreshInputs k keys.1 [a, b] inputs)
    (c : List Bool) (hc : c ∈ (ProbComp.eval
      ((FixedKey.scheme decryptionCircuits).evaluate k keys.1 ⟨2, nandCircuit⟩ inputs)).support) :
    (FixedKey.scheme decryptionCircuits).decrypt k keys.2 c = !(a && b) ∧
      c.length = ciphertextWidth k := by
  obtain ⟨hcorrect, hpermitted, hwidth, -⟩ :=
    fullyHomomorphic_of_decisionLWE_of_circularSecure hLWE hcircular
  refine ⟨?_, hwidth.evaluate_length k keys hkeys _ (hpermitted k _) [a, b] inputs rfl hinputs c
    hc⟩
  rw [hcorrect.decrypt_evaluate k keys hkeys _ (hpermitted k _) [a, b] inputs rfl hinputs c hc,
    eval_nandCircuit]
  rfl

end ComplexityTests.Crypto.GSWFullyHomomorphic

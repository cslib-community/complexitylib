/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.Basic
public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Serialized.Correctness

/-!
# The decision-LWE distribution of generated GSW public keys

The public marginal of the actual key generator is exactly the decision-LWE law with independent
centered-binomial errors reduced modulo `2 ^ w`. The joint key generator still retains its secret;
the equality below exposes only the public marginal, as required by the security experiment.

## Main definitions

* `noiseLaw`: the precise modular error law supplied to the decision-LWE hypothesis.

## Main results

* `eval_errorVector_mod`: independently sampled integer errors give the independent modular law.
* `eval_keyGen_publicMatrix`: the actual generated public matrix has the stated decision-LWE law.
* `eval_keyGenSerialized_publicWord`: the serialized key generator exposes that exact word ensemble.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open ProbComp Probability

/-- Reduce the difference of two independent `η`-bit counts modulo the actual modulus. -/
noncomputable def noiseLaw (w η : ℕ) : PMF (ZMod (2 ^ w)) :=
  (ProbComp.eval (sampleCenteredBinomial η)).map (fun error : ℤ => (error : ZMod (2 ^ w)))

/-- Reducing independent integer errors preserves the complete independent modular error law. -/
theorem eval_errorVector_mod (m w η : ℕ) :
    (ProbComp.eval (OracleComp.replicateFin m (sampleCenteredBinomial η))).map
      (fun error i => (error i : ZMod (2 ^ w))) =
        PMF.pi (fun _ : Fin m => noiseLaw w η) := by
  rw [← ProbComp.eval_replicateFin_map_coords, ProbComp.eval_replicateFin]
  simp only [noiseLaw, ProbComp.eval_map]

/-- The generated public matrix is an exact decision-LWE sample. This equality neither reveals
the generated secret nor asserts that any parameter or error family is computationally hard. -/
theorem eval_keyGen_publicMatrix (n m w η : ℕ) :
    (ProbComp.eval (keyGen n m w η)).map Prod.fst =
      LWE.publicMatrixLaw n m w (noiseLaw w η) := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, eval_sampleKeyInputs,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    PMF.map_bind, PMF.pure_map, LWE.publicMatrixLaw]
  rw [← eval_errorVector_mod m w η]
  simp only [PMF.bind_map, Function.comp_def]
  rfl

/-- Encoding the actual public marginal gives the exact word ensemble in the hardness
hypothesis, with no secret or error coordinates appended to the adversary's input. -/
theorem eval_keyGen_publicWord (n m w η : ℕ → ℕ) (security : ℕ) :
    (ProbComp.eval (keyGen (n security) (m security) (w security) (η security))).map
      (fun keys => Matrix.toBinary keys.1) =
        LWE.realEnsemble n m w (fun k => noiseLaw (w k) (η k)) security := by
  rw [LWE.realEnsemble, ← eval_keyGen_publicMatrix, PMF.map_comp]
  rfl

/-- The actual serialized key generator has precisely the public marginal used by decision LWE.
The encoded secret is discarded before the distinguisher is called. -/
theorem eval_keyGenSerialized_publicWord (n m w η : ℕ → ℕ) (security : ℕ) :
    (ProbComp.eval
      (keyGenSerialized (n security) (m security) (w security) (η security))).map Prod.fst =
        LWE.realEnsemble n m w (fun k => noiseLaw (w k) (η k)) security := by
  rw [eval_keyGenSerialized, PMF.map_comp]
  exact eval_keyGen_publicWord n m w η security

end Cslib.Crypto.Homomorphic.GSW

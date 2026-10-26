/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Basic
public import Complexity.Foundations.Data.Matrix.Binary
public import Complexity.Probability.Product
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Decision LWE with power-of-two moduli

The real experiment draws a uniform secret `t`, a uniform matrix `B`, and independent errors
with a specified residue distribution. Its public sample is the row-major binary encoding of
`[B * t + e | B]`. The comparison experiment draws an entirely uniform matrix of the same shape.
Only the public matrix is exposed; the secret and the sampled errors are not part of the word
given to a distinguisher.

`DecisionLWE` is an explicit computational hardness hypothesis for these two ensembles, against
uniform classical strict polynomial-time programs. It makes no assertion of hardness for any
particular parameter or error family. In particular, using a bounded noise distribution does
not identify it with a discrete Gaussian or establish a worst-case lattice reduction.

## Main definitions

* `Cslib.Crypto.LWE.publicMatrix`: the deterministic LWE matrix `[B * t + e | B]`.
* `Cslib.Crypto.LWE.publicMatrixLaw`: independent decision-LWE samples with a shared uniform secret.
* `Cslib.Crypto.LWE.realEnsemble`, `Cslib.Crypto.LWE.uniformEnsemble`: the binary experiments.
* `Cslib.Crypto.DecisionLWE`: indistinguishability of those experiments for the specified families.

## Main results

* `Cslib.Crypto.LWE.length_of_mem_support_realEnsemble`: every real sample has the declared length.
* `Cslib.Crypto.LWE.length_of_mem_support_uniformEnsemble`: the comparison uses the same length.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 2][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped _root_.Matrix

namespace LWE

/-- The deterministic LWE public matrix `[B * t + error | B]`. -/
def publicMatrix {n m w : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (t : Fin n → ZMod (2 ^ w)) (error : Fin m → ZMod (2 ^ w)) :
    Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) :=
  fun i => Fin.cons ((B *ᵥ t) i + error i) (B i)

/-- Draw the public matrix `[B * t + e | B]`. The errors are independent of one another, of
the uniform matrix, and of the uniform secret shared by all rows. -/
noncomputable def publicMatrixLaw (n m w : ℕ) (noise : PMF (ZMod (2 ^ w))) :
    PMF (Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) := do
  let secret ← PMF.uniformOfFintype (Fin n → ZMod (2 ^ w))
  let publicPart ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
  let error ← PMF.pi (fun _ : Fin m => noise)
  return publicMatrix publicPart secret error

/-- Binary decision-LWE samples, using `w` bits per residue and a uniform secret. -/
noncomputable def realEnsemble (n m w : ℕ → ℕ)
    (noise : (security : ℕ) → PMF (ZMod (2 ^ w security))) (security : ℕ) : PMF (List Bool) :=
  (publicMatrixLaw (n security) (m security) (w security) (noise security)).map Matrix.toBinary

/-- Encode a uniform matrix with exactly the real experiment's dimensions and modulus. -/
noncomputable def uniformEnsemble (n m w : ℕ → ℕ) (security : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype
    (Matrix (Fin (m security)) (Fin (n security + 1)) (ZMod (2 ^ w security)))).map Matrix.toBinary

/-- The real public word contains exactly one fixed-width residue for each matrix entry. -/
theorem length_of_mem_support_realEnsemble {n m w : ℕ → ℕ}
    {noise : (security : ℕ) → PMF (ZMod (2 ^ w security))} {security : ℕ} {word : List Bool}
    (h : word ∈ (realEnsemble n m w noise security).support) :
    word.length = m security * (n security + 1) * w security := by
  obtain ⟨A, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact Matrix.length_toBinary A

/-- Uniform public words have the same complete serialized length as real public words. -/
theorem length_of_mem_support_uniformEnsemble {n m w : ℕ → ℕ} {security : ℕ} {word : List Bool}
    (h : word ∈ (uniformEnsemble n m w security).support) :
    word.length = m security * (n security + 1) * w security := by
  obtain ⟨A, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact Matrix.length_toBinary A

end LWE

/-- Decision-LWE hardness for the exact dimension, sample count, binary modulus width and error
families. The adversary receives the unary security parameter and only the encoded public matrix.
This is a hypothesis against uniform classical strict PPT distinguishers, not a theorem of
hardness or a claim about quantum adversaries. -/
def DecisionLWE (n m w : ℕ → ℕ)
    (noise : (security : ℕ) → PMF (ZMod (2 ^ w security))) : Prop :=
  ComputationallyIndistinguishable (LWE.realEnsemble n m w noise) (LWE.uniformEnsemble n m w)

end Cslib.Crypto

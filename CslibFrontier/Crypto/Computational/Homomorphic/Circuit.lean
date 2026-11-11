/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Gates
public import CslibFrontier.Computability.Circuit.Parallel

/-!
# NAND-augmented decryption circuits

Gentry's bootstrappability condition concerns actual circuits obtained by connecting a gate to
copies of the decryption circuit [Gentry2009], Definition 4. Here `augmentNand D` runs two copies
of `D` on disjoint input blocks and applies NAND to their outputs. NAND uses one AND gate and
one NOT gate in the De Morgan basis.

## Main definitions

* `Cslib.Crypto.Homomorphic.augmentNand`: NAND applied to two copies of a circuit.

## Main results

* `Cslib.Crypto.Homomorphic.eval_augmentNand`: the augmentation computes NAND of the two results.
* `Cslib.Crypto.Homomorphic.size_augmentNand`: the augmentation has exactly `2 * D.size + 2` gates.

## References

* [C. Gentry, *Fully Homomorphic Encryption Using Ideal Lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic

open Cslib.Circuits
open Boolean (nandCircuit eval_nandCircuit)

/-- Connect the outputs of two copies of `D`, on disjoint input blocks, to a NAND circuit. -/
def augmentNand {n : ℕ} (D : Circuit Boolean.signature n 1) :
    Circuit Boolean.signature (n + n) 1 :=
  nandCircuit.comp (D.parallel D)

/-- The NAND augmentation evaluates `D` on each input block and takes NAND of the results. -/
@[simp] theorem eval_augmentNand {n : ℕ} (D : Circuit Boolean.signature n 1)
    (x y : Fin n → Bool) (j : Fin 1) :
    (augmentNand D).eval Boolean.interpretation (Fin.append x y) j =
      !(D.eval Boolean.interpretation x 0 && D.eval Boolean.interpretation y 0) := by
  simp only [augmentNand, Circuit.eval_comp, eval_nandCircuit, Circuit.eval_parallel,
    Fin.append_comp_castAdd, Fin.append_comp_natAdd]
  rfl

/-- The two copies of `D` and the two NAND gates account for every gate of the augmentation. -/
@[simp] theorem size_augmentNand {n : ℕ} (D : Circuit Boolean.signature n 1) :
    (augmentNand D).size = 2 * D.size + 2 := by
  simp [augmentNand, two_mul]

end Cslib.Crypto.Homomorphic

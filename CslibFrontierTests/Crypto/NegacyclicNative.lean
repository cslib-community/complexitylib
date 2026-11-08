/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.Native
import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption

/-! Native negacyclic coefficients, total input edges, and the actual key-generation client. -/

namespace ComplexityTests.NegacyclicNative

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- The dimension is an input to one certificate, rather than a fixed finite specialization. -/
example : ComputableInPolyTime
    (fun x : (ℕ × ℕ) × List ℕ × List ℕ => negacyclicMulResidues x.1.1 x.1.2 x.2.1 x.2.2)
    (encPair (encPair encUnary encNat) (encPair (encList encNat) (encList encNat)))
    (encList encNat) := computableInPolyTime_negacyclicMulResidues

example : negacyclicMulResidues 0 6 [1, 2] [3] = [] := by decide

/-- In degree one the ring product is ordinary multiplication. Excess input is discarded. -/
example : negacyclicMulResidues 1 7 [2, 99] [3] = [6] := by decide

/-- The wrap sign is visible over a composite coefficient modulus: X² = -1. -/
example : negacyclicMulResidues 2 6 [0, 1] [0, 1] = [5, 0] := by decide

example : negacyclicMulResidues 2 1 [0, 1] [0, 1] = [0, 0] := by decide

/-- Modulus zero is total but has no claimed canonical modular interpretation. -/
example : negacyclicMulResidues 2 0 [0, 1] [0, 1] = [0, 0] := by decide

example : negacyclicMulResidues 1 0 [2] [3] = [6] := by decide

/-- Short lists are zero-padded; inputs need not already be residues. -/
example : negacyclicMulResidues 3 7 [9] [3, 4] = [6, 1, 0] := by decide

/-- Binary magnitudes do not control the number of loop iterations. -/
example : negacyclicMulResidues 1 (2 ^ 128 + 1) [2 ^ 64] [2 ^ 64] = [2 ^ 128] := by
  decide

/-- The generic bridge applies even to the zero ring. -/
example (a b : Fin 2 → ZMod 1) :
    negacyclicMulResidues 2 1 (List.ofFn fun i => (a i).val)
      (List.ofFn fun i => (b i).val) =
        List.ofFn fun i => (negacyclicMul a b i).val :=
  negacyclicMulResidues_ofFn (by decide) a b

/-- An actual rank-one key-generation contribution uses the same native multiplication.
This certifies its coefficient computation, without asserting a complete key codec. -/
example {n q : ℕ} (hq : 0 < q) (a s : Fin n → ZMod q) :
    negacyclicMulResidues n q (List.ofFn fun i => (a i).val)
      (List.ofFn fun i => (s i).val) =
        List.ofFn fun i => ((moduleLWEKeyGen ![![a]] ![s] 0).2 0 i).val := by
  simpa [moduleLWEKeyGen, moduleSISMap] using negacyclicMulResidues_ofFn hq a s

/-- The checked rank-one client has a nonzero wrapped product. -/
example : ((moduleLWEKeyGen ![![![0, 1]]] ![![0, 1]] 0 :
    ModuleLWEPublicKey 1 2 6).2 0 0).val = 5 := by decide

end ComplexityTests.NegacyclicNative

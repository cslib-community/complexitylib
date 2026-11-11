/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.DirectProduct.Complexity
import CslibFrontier.Computability.Circuit.Boolean.Combinators

/-! # Concrete instances of the decoder's circuit bound

The combinators are instantiated on input bits, and the decoder's bound on a `C'` that reads the
first bit of each block. Each output of that `C'` is an input of the flat tuple and costs no
gates, so the decoder costs at most `4 m (#P + 1) + 3 m + 1` gates. This file is a module, so it
uses the decoder's equations only through the exported lemmas, as a downstream module does.
-/

namespace CslibFrontierTests.IJKWDecodeComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.DirectProduct Finset

/-! ### Combinators -/

-- A multiplexer of three input bits costs at most four gates.
example : complexity interpretation
    (single fun x : BitString 3 => if x 0 then x 1 else x 2) ≤ 4 := by
  have h := complexity_ite_le (fun x : BitString 3 => x 0) (fun x => x 1) (fun x => x 2)
  have h0 : complexity interpretation (single fun x : BitString 3 => x 0) ≤ 0 := by simp
  have h1 : complexity interpretation (single fun x : BitString 3 => x 1) ≤ 0 := by simp
  have h2 : complexity interpretation (single fun x : BitString 3 => x 2) ≤ 0 := by simp
  exact h.trans (by omega)

-- The conjunction of all three input bits costs at most four gates.
example : complexity interpretation
    (single fun x : BitString 3 => decide (∀ i ∈ (univ : Finset (Fin 3)), x i = true)) ≤ 4 := by
  simpa using complexity_decide_forall_mem_le (univ : Finset (Fin 3)) (fun i x => x i) (c := 0)
    fun i _ => by simp

/-! ### The decoder -/

-- Reading the first bit of every block costs nothing on the flat tuple, so `c = 0`.
example {k : ℕ} (P : Finset (Fin k)) (b₀ : Fin k → BitString 1) {m : ℕ}
    (v : Fin m → Trial (BitString 1) k) :
    complexity interpretation (single (dpDecode (fun z j => z j 0) false P b₀ v)) ≤
      m * (#P + 1) * 4 + 3 * m + 1 := by
  simpa using complexity_dpDecode_le (fun z j => z j 0) false P b₀ v (c := 0) fun j => by simp

-- Two trials and one fixed position on pairs of one-bit blocks: at most `23` gates.
example (b₀ : Fin 2 → BitString 1) (v : Fin 2 → Trial (BitString 1) 2) :
    complexity interpretation (single (dpDecode (fun z j => z j 0) false {0} b₀ v)) ≤ 23 :=
  complexity_dpDecode_le (fun z j => z j 0) false {0} b₀ v (c := 0) fun j => by simp

end CslibFrontierTests.IJKWDecodeComplexity

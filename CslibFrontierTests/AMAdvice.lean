/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Advice
import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.GraphNonIsomorphism
import CslibFrontier.Computability.Complexity.Classes.IP.Games.GoldwasserSipser

/-! Concrete clients for `AM ⊆ NP/poly`: a problem in `BPP`, graph isomorphism and a problem in
`IP[2]`. -/

namespace CslibFrontierTests.AMAdvice

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- `AM ⊆ NP/poly` for any encoding. -/
example {α : Type} (enc : α ↪ List Bool) : AM enc ⊆ NPPoly enc := AM_subset_NPPoly

/-- `MA ⊆ NP/poly` for any encoding. -/
example {α : Type} (enc : α ↪ List Bool) : MA enc ⊆ NPPoly enc := MA_subset_NPPoly

private theorem head_mem_AM : {w : List Bool | w.headD false = true} ∈ AM encBits :=
  BPP_subset_AM (P_subset_BPP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)

/-- A problem in `AM`, here from `P ⊆ BPP ⊆ AM`, gets polynomial advice. -/
example : {w : List Bool | w.headD false = true} ∈ NPPoly encBits :=
  AM_subset_NPPoly head_mem_AM

/-- Graph isomorphism is in `coNP/poly`, through graph non-isomorphism in `AM`. -/
example : GraphIsomorphism ∈ coNPPoly (encPair encGraph encGraph) :=
  GraphNonIsomorphism.GraphIsomorphism_mem_coNPPoly

/-- Graph non-isomorphism itself is in `NP/poly`. -/
example : GraphNonIsomorphism ∈ NPPoly (encPair encGraph encGraph) :=
  AM_subset_NPPoly GraphNonIsomorphism.mem_AM

/-- A problem in `IP[2]`, through the Goldwasser–Sipser emulation and round collapse, is in
`NP/poly`. -/
example : {w : List Bool | w.headD false = true} ∈ NPPoly encBits :=
  IPGameClass_subset_NPPoly _ (AMk_subset_IPk 2 (by rw [AMk_two]; exact head_mem_AM))

/-- `IP[k] ⊆ NP/poly` for every constant `k`. -/
example {α : Type} (enc : α ↪ List Bool) (k : ℕ) : IPk enc k ⊆ NPPoly enc :=
  IPGameClass_subset_NPPoly _

end CslibFrontierTests.AMAdvice

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.PermutationIndependentSet
import Complexity.Computability.MCSP.PartialETH
import Complexity.Computability.MCSP.PartialNP

/-!
# Tests: Partial-Function MCSP (`MCSP*`) and Bipartite Permutation Independent Set

Tests for `PartialMCSP`, `PartialMCSP.BinaryGate`, the binary-gate fan-in and threshold-$n-1$
rigidity bridges, `NP` membership under unary and binary thresholds, the reduction from `MCSP`,
`BipartitePermutationIndependentSet` (directed and undirected LMS formulations), and the
Lokshtanov–Marx–Saurabh $2^{o(n \log n)}$ ETH lower bound.
-/

namespace ComplexityTests.PartialMCSP

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

variable {n m g : ℕ}

/-! ### Partial MCSP and binary-gate rigidity -/

example (c : Circuit signature n m) :
    c.inputSupport.card ≤ m + c.program.cost binaryCost :=
  c.card_inputSupport_le_cost_binaryCost

example (p : Program signature n g) :
    p.cost binaryCost = g ↔ ∀ k : Fin g, (p.lines k).op.IsBinary :=
  Program.cost_binaryCost_eq_iff_forall_isBinary

example (x : PartialMCSP.Instance) :
    x ∈ PartialMCSP ↔ ∃ c : Circuit signature x.arity 1,
      c.size ≤ x.threshold ∧
        ∀ y b, x.partialFunction y = some b → c.eval interpretation y 0 = b :=
  PartialMCSP.mem_iff_exists_circuit

example (x : PartialMCSP.Instance) :
    x ∈ PartialMCSP ↔ ∃ f : BooleanFunction x.arity,
      x.AgreesWith f ∧ complexity interpretation (single f) ≤ x.threshold :=
  PartialMCSP.mem_iff_exists_total_extension

example (x : PartialMCSP.Instance) (h : x ∈ PartialMCSP) :
    x ∈ PartialMCSP.BinaryGate :=
  PartialMCSP.mem_binaryGate_of_mem h

example (x : PartialMCSP.Instance)
    (hess : ∀ i : Fin x.arity, x.EssentialAt i) (ht : x.threshold + 1 < x.arity) :
    x ∉ PartialMCSP.BinaryGate :=
  PartialMCSP.not_mem_binaryGate_of_threshold_lt hess ht

example (x : PartialMCSP.Instance) {c : Circuit signature x.arity 1}
    (hess : ∀ i : Fin x.arity, x.EssentialAt i)
    (hc : x.AgreesWith fun y => c.eval interpretation y 0)
    (hsize : c.size ≤ x.threshold) (ht : x.threshold + 1 ≤ x.arity) :
    c.program.cost binaryCost = x.arity - 1 ∧ c.size = x.arity - 1 ∧
      ∀ k : Fin c.size, (c.program.lines k).op.IsBinary :=
  PartialMCSP.isBinary_of_mem_of_threshold_le hess hc hsize ht

example (x : PartialMCSP.Instance)
    (hess : ∀ i : Fin x.arity, x.EssentialAt i) (hpos : 1 ≤ x.arity)
    (ht : x.threshold = x.arity - 1) :
    x ∈ PartialMCSP ↔ ∃ c : Circuit signature x.arity 1,
      c.size = x.arity - 1 ∧
      (∀ k : Fin c.size, (c.program.lines k).op.IsBinary) ∧
      x.AgreesWith fun y => c.eval interpretation y 0 :=
  PartialMCSP.mem_iff_exists_all_isBinary_of_threshold_eq_arity_sub_one hess hpos ht

example (x : MCSP.Instance) :
    PartialMCSP.Instance.ofTotal x ∈ PartialMCSP ↔ x ∈ MCSP :=
  PartialMCSP.ofTotal_mem_iff x

example (x : PartialMCSP.Instance) :
    x.toSuccinct ∈ SuccinctMCSP ↔ x ∈ PartialMCSP :=
  PartialMCSP.toSuccinct_mem_iff x

/-- A partial truth table with all `*` (`none`) entries is computed by a 0-gate wire circuit for
`1 ≤ n`. -/
example : (⟨1, fun _ => none, 0⟩ : PartialMCSP.Instance) ∈ PartialMCSP := by
  rw [PartialMCSP.mem_iff_exists_circuit]
  exact ⟨⟨.empty, fun _ => Wire.input 0⟩, le_rfl,
    fun _ _ h => by simp [PartialMCSP.Instance.partialFunction] at h⟩

/-! ### NP membership and reduction from MCSP -/

example : PartialMCSP ∈ NP PartialMCSP.enc :=
  PartialMCSP.mem_NP

example : PartialMCSP ∈ NP PartialMCSP.encBinary :=
  PartialMCSP.mem_NP_encBinary

example : ComputableInPolyTime PartialMCSP.verifier
    (encPair PartialMCSP.enc encBits) encBool :=
  PartialMCSP.computableInPolyTime_verifier

example : ComputableInPolyTime PartialMCSP.verifier
    (encPair PartialMCSP.encBinary encBits) encBool :=
  PartialMCSP.computableInPolyTime_verifier_encBinary

example : PolyTimeReducible MCSP.encInstance PartialMCSP.encBinary MCSP PartialMCSP :=
  PartialMCSP.polyTimeReducible_MCSP_PartialMCSP_encBinary

/-! ### Bipartite Permutation Independent Set and the LMS ETH lower bound -/

example (G : BipartitePermutationGraph) :
    (∃ π₁ π₂ : Equiv.Perm (Fin G.1), G.Satisfies π₁ π₂) ↔
      ∃ π : Equiv.Perm (Fin (2 * G.1)), G.SatisfiesUndirected π :=
  G.exists_satisfies_iff_exists_satisfiesUndirected

/-- An edgeless $n \times n$ bipartite permutation graph is always satisfiable. -/
example (n : ℕ) : ((n, []) : BipartitePermutationGraph) ∈ BipartitePermutationIndependentSet :=
  ⟨1, 1, fun _ h => by simp at h⟩

/-- A self-loop on every pair $(0, j)$ for $n = 1$ makes the instance unsatisfiable. -/
example : ((1, [((0, 0), (0, 0))]) : BipartitePermutationGraph) ∉
    BipartitePermutationIndependentSet := by
  rintro ⟨π₁, π₂, h⟩
  exact h ((0, 0), (0, 0)) (by simp) (by decide) (by decide) (by decide) (by decide)
    (Subsingleton.elim (π₁ 0) 0) (Subsingleton.elim (π₂ 0) 0)

example (H : Graph) :
    H ∈ ThreeColoring ↔
      ∃ r < 2 ^ BipartitePermutationIndependentSet.searchBits H.1.length,
        BipartitePermutationIndependentSet.bpisOfColoring (H, r) ∈
          BipartitePermutationIndependentSet :=
  BipartitePermutationIndependentSet.mem_ThreeColoring_iff_exists_bpisOfColoring H

example : ComputableInPolyTime BipartitePermutationIndependentSet.bpisOfColoring
    (encPair encGraph encNat) encBipartitePermutationGraph :=
  BipartitePermutationIndependentSet.computableInPolyTime_bpisOfColoring

example : ComputableInPolyTime BipartitePermutationIndependentSet.bpisOfColoring
    (encPair encGraph encNat) encBipartitePermutationGraphBinary :=
  BipartitePermutationIndependentSet.computableInPolyTime_bpisOfColoring_binary

example
    (h : DecidableInSubexpTime BipartitePermutationIndependentSet
      encBipartitePermutationGraph fun G => G.1 * Nat.log 2 G.1) :
    DecidableInSubexpTime ThreeColoring encGraph fun H => H.1.length :=
  h.threeColoring_of_bipartitePermutationIndependentSet

example (heth : ETH) :
    ¬DecidableInSubexpTime BipartitePermutationIndependentSet
      encBipartitePermutationGraph fun G => G.1 * Nat.log 2 G.1 :=
  heth.not_decidableInSubexpTime_BipartitePermutationIndependentSet

example (heth : ETH) :
    ¬DecidableInSubexpTime BipartitePermutationIndependentSet
      encBipartitePermutationGraphBinary fun G => G.1 * Nat.log 2 G.1 :=
  heth.not_decidableInSubexpTime_BipartitePermutationIndependentSet_binary

example (heth : ETH) :
    ¬DecidableInSubexpTime BipartitePermutationIndependentSet
      encBipartitePermutationGraph fun G => G.1 * Nat.clog 2 G.1 :=
  heth.not_decidableInSubexpTime_BipartitePermutationIndependentSet_clog

example (heth : ETH) :
    ¬DecidableInSubexpTime BipartitePermutationIndependentSet
      encBipartitePermutationGraph fun G => 2 * G.1 * Nat.log 2 (2 * G.1) :=
  heth.not_decidableInSubexpTime_BipartitePermutationIndependentSet_two_mul

/-! ### Monotone read-once formulas, Ilango's reduction, and PartialMCSP ETH lower bounds -/

example (F : PosFormula n) :
    F.size + 1 = F.leafSize :=
  F.size_add_one

example (hn : 0 < n) (c : Circuit signature n 1)
    (hcost : c.program.cost binaryCost + 1 ≤ n)
    (hpos : ∀ i : Fin n, ∃ y₀ y₁ : BitString n, (∀ k, k ≠ i → y₀ k = y₁ k) ∧
      y₀ i = false ∧ y₁ i = true ∧
      c.eval interpretation y₀ 0 = false ∧ c.eval interpretation y₁ 0 = true) :
    ∃ F : PosFormula n,
      F.IsReadOnce ∧ F.leafSize = n ∧ F.size = n - 1 ∧ F.leafSupport = Finset.univ ∧
      ∀ x, F.eval x = c.eval interpretation x 0 :=
  c.exists_posFormula_of_cost_binaryCost_le hn hcost hpos

example (G : BipartitePermutationGraph) (hG : 0 < G.1)
    {f : BitString (6 * G.1) → Bool} (hf : (PartialMCSP.ilangoInstance G).AgreesWith f)
    (v : Fin (6 * G.1)) :
    ∃ w : BitString (6 * G.1),
      f (Function.update w v false) = false ∧ f (Function.update w v true) = true :=
  PartialMCSP.ilangoInstance_posEssential hG hf v

example {F : PosFormula (6 * n)} (hro : F.IsReadOnce) (hleaf : F.leafSize = 6 * n)
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (PartialMCSP.packXYZ PartialMCSP.zeros2n y z) =
        decide (∃ i, y i = true ∧ z i = true))
    (hC2 : ∀ y z : BitString (2 * n),
      F.eval (PartialMCSP.packXYZ PartialMCSP.ones2n y z) = decide (∃ i, z i = true))
    (hC3 : ∀ x y : BitString (2 * n),
      F.eval (PartialMCSP.packXYZ x y PartialMCSP.ones2n) =
        decide (∃ i, x i = true ∨ y i = true))
    (hC4 : ∀ x y : BitString (2 * n),
      F.eval (PartialMCSP.packXYZ x y PartialMCSP.zeros2n) = false) :
    ∃ π : Equiv.Perm (Fin (2 * n)), ∀ x y z : BitString (2 * n),
      F.eval (PartialMCSP.packXYZ x y z) =
        decide (∃ i : Fin (2 * n), (x (π i) || y i) && z i) :=
  PosFormula.exists_perm_of_agreesWith_ilango hro hleaf hC1 hC2 hC3 hC4

example (G : BipartitePermutationGraph) :
    G ∈ BipartitePermutationIndependentSet ↔
      PartialMCSP.ilangoReduction G ∈ PartialMCSP.MonotoneReadOnce :=
  PartialMCSP.mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem_monotoneReadOnce G

example (G : BipartitePermutationGraph) :
    G ∈ BipartitePermutationIndependentSet ↔
      PartialMCSP.ilangoReduction G ∈ PartialMCSP.BinaryGate :=
  PartialMCSP.mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem_binaryGate G

example (G : BipartitePermutationGraph) :
    G ∈ BipartitePermutationIndependentSet ↔
      PartialMCSP.ilangoReduction G ∈ PartialMCSP :=
  PartialMCSP.mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem G

example :
    ∃ C D : ℕ, ComputableInO PartialMCSP.ilangoReduction
      encBipartitePermutationGraph PartialMCSP.enc
      (fun G => 2 ^ (C * G.1) * ((encBipartitePermutationGraph G).length + 1) ^ D)
      (fun G => 2 ^ (C * G.1) * ((encBipartitePermutationGraph G).length + 1) ^ D) :=
  PartialMCSP.exists_computableInO_ilangoReduction

example :
    ∃ C D : ℕ, ComputableInO PartialMCSP.ilangoReduction
      encBipartitePermutationGraph PartialMCSP.encBinary
      (fun G => 2 ^ (C * G.1) * ((encBipartitePermutationGraph G).length + 1) ^ D)
      (fun G => 2 ^ (C * G.1) * ((encBipartitePermutationGraph G).length + 1) ^ D) :=
  PartialMCSP.exists_computableInO_ilangoReduction_encBinary

example (heth : ETH) :
    ¬DecidableInSubexpTime PartialMCSP PartialMCSP.enc
      fun I => I.arity * Nat.log 2 I.arity :=
  heth.not_decidableInSubexpTime_PartialMCSP

example (heth : ETH) :
    ¬DecidableInSubexpTime PartialMCSP PartialMCSP.encBinary
      fun I => I.arity * Nat.log 2 I.arity :=
  heth.not_decidableInSubexpTime_PartialMCSP_encBinary

example (heth : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.BinaryGate PartialMCSP.enc
      fun I => I.arity * Nat.log 2 I.arity :=
  heth.not_decidableInSubexpTime_PartialMCSP_binaryGate

example (heth : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.BinaryGate PartialMCSP.encBinary
      fun I => I.arity * Nat.log 2 I.arity :=
  heth.not_decidableInSubexpTime_PartialMCSP_binaryGate_encBinary

example (heth : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.MonotoneReadOnce PartialMCSP.enc
      fun I => I.arity * Nat.log 2 I.arity :=
  heth.not_decidableInSubexpTime_PartialMonotoneReadOnceMCSP

example (heth : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.MonotoneReadOnce PartialMCSP.encBinary
      fun I => I.arity * Nat.log 2 I.arity :=
  heth.not_decidableInSubexpTime_PartialMonotoneReadOnceMCSP_encBinary

example (heth : ETH) :
    ¬DecidableInSubexpTime PartialMCSP PartialMCSP.enc
      fun I => Nat.log 2 I.tableSize * Nat.log 2 (Nat.log 2 I.tableSize) :=
  heth.not_decidableInSubexpTime_PartialMCSP_tableSize

example (heth : ETH) :
    ¬DecidableInSubexpTime PartialMCSP PartialMCSP.encBinary
      fun I => Nat.log 2 I.tableSize * Nat.log 2 (Nat.log 2 I.tableSize) :=
  heth.not_decidableInSubexpTime_PartialMCSP_tableSize_encBinary

end ComplexityTests.PartialMCSP

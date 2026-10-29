/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module

public import Complexity.Init
public import Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Kernel-checked tests for `Cslib.Complexity.SparseCNFLeafCounter`

Concrete `decide` and end-to-end semantic/resource tests for `sparseCNFDeclaredCounter`,
`normalizeDeclaredLeaf`, `sparseCNFLeafCounter`, and their native machine certificates.
-/

@[expose] public section

namespace ComplexityTests.SparseCNFLeafCounter

open Cslib.BitString Cslib.Complexity Cslib.Complexity.InitialTestsSearch
open Cslib.Complexity.SparseCNFLeafCounter Cslib.GenericRAM
open Cslib.GenericRAM.ExhaustiveCountFallback Cslib.Logic.PL Cslib.Logic.PL.CNF
open Turing.MultiTapeTM

/-- Runtime parameter pair `(N, B)` encoded in unary. -/
abbrev encNB : ℕ × ℕ ↪ List Bool := encPair encUnary encUnary

private abbrev declExh (N₀ : ℕ) (x : (ℕ × ℕ) × CNF ℕ) : ℕ :=
  sparseCNFDeclaredCounter Prod.fst Prod.snd 3 N₀ countSystemExhaustive x

private abbrev leafExh (N₀ : ℕ) (x : (ℕ × ℕ) × CNF ℕ) : ℕ :=
  sparseCNFLeafCounter Prod.fst Prod.snd 3 N₀ countSystemExhaustive x

/-! ### 1. Degenerate, Unit-Clause, Unused-Variable, and Guard Boundary Cases -/

example :
    (declExh 2 ((0, 1), []) = 1 ∧ leafExh 2 ((0, 1), []) = 1) ∧
    (declExh 2 ((3, 1), []) = 8 ∧ leafExh 2 ((3, 1), []) = 1) ∧
    (declExh 4 ((1, 1), [[(0, true)]]) = 1 ∧ leafExh 4 ((1, 1), [[(0, true)]]) = 1) ∧
    (declExh 4 ((3, 1), [[(0, true)]]) = 4 ∧ leafExh 4 ((3, 1), [[(0, true)]]) = 1) ∧
    (declExh 2 ((0, 1), [[]]) = 0 ∧ leafExh 2 ((0, 1), [[]]) = 0) ∧
    (declExh 2 ((4, 1), [[(0, true)], []]) = 0 ∧
      leafExh 2 ((4, 1), [[(0, true)], []]) = 0) ∧
    declExh 2 ((5, 2), [[(0, true), (1, true), (2, true), (3, true)]]) = 0 ∧
    declExh 2 ((2, 2), [[(2, true)]]) = 0 ∧
    (declExh 2 ((2, 1), [[(0, true)], [(1, true)], [(0, false), (1, false)]]) = 0 ∧
      leafExh 2 ((2, 1), [[(0, true)], [(1, true)], [(0, false), (1, false)]]) = 0) ∧
    (declExh 2 ((2, 1), [[(0, true)], [(0, true)], [(0, true)]]) = 0 ∧
      leafExh 2 ((2, 1), [[(0, true)], [(0, true)], [(0, true)]]) = 0) ∧
    (declExh 3 ((2, 1), [[(0, true)], [(0, true)], [(0, true)]]) = 2 ∧
      leafExh 3 ((2, 1), [[(0, true)], [(0, true)], [(0, true)]]) = 1) := by
  decide

/-! ### 2. Multi-Clause Sparse `3`-CNF Across Fallback, Pipeline Primitives, and Fast Path -/

/-- Three-clause `3`-CNF `(x₀ ∨ ¬x₁ ∨ x₂) ∧ (¬x₀ ∨ x₂) ∧ (x₁ ∨ ¬x₂)` (`modelCount = 3`,
`modelCountOn (Finset.range 4) = 6`). -/
def psi3 : CNF ℕ :=
  [[(0, true), (1, false), (2, true)], [(0, false), (2, true)], [(1, true), (2, false)]]

example (x : (ℕ × ℕ) × CNF ℕ) :
    psi3.modelCount = 3 ∧
    psi3.modelCountOn (Finset.range 4) = 6 ∧
    declExh 5 ((4, 1), psi3) = 6 ∧
    leafExh 5 ((4, 1), psi3) = 3 ∧
    entersSparseFastPath 3 2 4 1 psi3 = true ∧
    ((initialTestsRows 3 1).length ≤ 12 ∧ ∀ r ∈ initialTestsRows 3 1, r.length = 3) ∧
    (let initRows := initialTestsRows 3 1
      let rows := greedyParityRows
        (fun r => compiledRowCounter 3 countSystemExhaustive ((4, psi3), r)) 1 3 1 initRows
      compiledRowCounter 3 countSystemExhaustive ((4, psi3), rows) = 6) ∧
    declExh 2 ((4, 1), psi3) = 6 ∧
    leafExh 2 ((4, 1), psi3) = 3 ∧
    (sparseCNFDeclaredCounter Prod.fst Prod.snd 3 2 (fun _ => 999) x ≤ 2 ^ x.1.1 ∧
      sparseCNFLeafCounter Prod.fst Prod.snd 3 2 (fun _ => 999) x ≤ 2 ^ x.2.numVars) := by
  have hw : ∀ c ∈ psi3, c.length ≤ 3 := by decide
  have hsub : psi3.vars.toFinset ⊆ Finset.range 4 := by decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_,
    sparseCNFDeclaredCounter_le_two_pow _ _ _ _ _ x,
    sparseCNFLeafCounter_le_two_pow_numVars _ _ _ _ _ x⟩
  · rw [declExh, sparseCNFDeclaredCounter_exhaustive_eq_modelCountOn (NOf := Prod.fst)
      (BOf := Prod.snd) (p := (4, 1)) hw hsub (Or.inl (by decide))]
    decide
  · rw [leafExh, sparseCNFLeafCounter_exhaustive_eq_modelCount (NOf := Prod.fst)
      (BOf := Prod.snd) (p := (4, 1)) hw hsub (Or.inl (by decide))]
    decide

/-! ### 3. Concrete Native Certificate & Split `ComputableInO` Instantiations -/

private def CheckSplitComputableInO (f : (ℕ × ℕ) × CNF ℕ → ℕ) : Prop :=
  ∃ poly qInit polySys : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
    Cslib.PolynomiallyBounded qInit ∧ Cslib.PolynomiallyBounded polySys ∧
    ∀ R, ValidPolyTimeBound encNB Prod.fst Prod.snd 3 16 countSystemExhaustiveCertificate
        polySys R →
      ComputableInO f (encPair encNB encCNF) encNat
        (sparseCNFTimeBound encNB Prod.fst Prod.snd 3 16 poly qInit R)
        (fun x => poly (encPair encNB encCNF x).length)

example :
    (CheckSplitComputableInO (declExh 16) ∧ CheckSplitComputableInO (leafExh 16)) ∧
    PolyBounded (fun x : (ℕ × ℕ) × CNF ℕ => (encPair encNB encCNF x).length)
      (sparseCNFLeafCertificate (encP := encNB) (NOf := Prod.fst) (BOf := Prod.snd) 3 16
        (by fun_prop) (by fun_prop) countSystemExhaustiveCertificate).space :=
  ⟨⟨computableInO_sparseCNFDeclaredCounter 3 16 (by fun_prop) (by fun_prop)
      countSystemExhaustiveCertificate polyBounded_countSystemExhaustive_space,
    computableInO_sparseCNFLeafCounter 3 16 (by fun_prop) (by fun_prop)
      countSystemExhaustiveCertificate polyBounded_countSystemExhaustive_space⟩,
   polyBounded_sparseCNFLeafCertificate_space 3 16 (by fun_prop) (by fun_prop)
     countSystemExhaustiveCertificate polyBounded_countSystemExhaustive_space⟩

end ComplexityTests.SparseCNFLeafCounter

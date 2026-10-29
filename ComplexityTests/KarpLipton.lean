/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.SelfReduction
import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Foundations.Data.BitString.Enumeration

/-!
# Tests for the SAT self-reduction and the Karp–Lipton theorem

The self-reduction on concrete formulas with a brute-force decision procedure, which satisfies the
hypothesis of `SAT.verifier_search`; and advice strings for a concrete family of circuits.
-/

namespace Cslib.Complexity.Tests.KarpLipton

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The self-reduction -/

/-- A brute-force decision procedure for `SAT`: try every certificate with one bit for each literal
occurrence. -/
def bruteSAT (ψ : CNF ℕ) : Bool :=
  (BitString.enumList ψ.vars.length).any fun w => SAT.verifier (ψ, w)

/-- The brute-force procedure decides `SAT`, so it meets the hypothesis of
`SAT.verifier_search` at every length. -/
theorem bruteSAT_iff (ψ : CNF ℕ) : bruteSAT ψ = true ↔ ψ ∈ SAT := by
  rw [bruteSAT, List.any_eq_true]
  constructor
  · rintro ⟨w, -, hw⟩
    exact ⟨_, hw⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨ψ.vars.map τ, BitString.mem_enumList.2 (by simp), ?_⟩
    refine (CNF.eval_congr fun v hv => ?_).trans hτ
    have hlt : ψ.vars.idxOf v < ψ.vars.length := List.idxOf_lt_length_iff.2 hv
    rw [SAT.assignment, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
      List.getElem_idxOf hlt]

/-- `(x₀ ∨ x₁) ∧ ¬x₀`, with literal occurrences `x₀, x₁, x₀`. -/
def φ₁ : CNF ℕ := [[(0, true), (1, true)], [(0, false)]]

/-- `x₀ ∧ ¬x₀`. -/
def φ₂ : CNF ℕ := [[(0, true)], [(0, false)]]

-- Self-reduction on `φ₁` (`x₀ ↦ false`, `x₁ ↦ true`), unsatisfiable `φ₂`, wrong oracle answers,
-- and `SAT.queryBound 1 = 39`.
example :
    SAT.selfReduce bruteSAT φ₁ = [(0, false), (1, true), (0, false)] ∧
    SAT.search bruteSAT φ₁ = [false, true, false] ∧
    SAT.verifier (φ₁, SAT.search bruteSAT φ₁) = true ∧
    SAT.verifier (φ₂, SAT.search bruteSAT φ₂) = false ∧
    SAT.search (fun _ => true) φ₁ = [true, true, true] ∧
    SAT.verifier (φ₁, SAT.search (fun _ => true) φ₁) = false ∧
    SAT.queryBound 1 = 39 :=
  ⟨by decide, by decide,
    SAT.verifier_search (fun ψ _ => bruteSAT_iff ψ) ⟨fun v => v == 1, by decide⟩,
    by decide, by decide, by decide, rfl⟩

/-! ### Advice strings -/

/-- A family of circuits for the first input bit, `false` on the empty input. -/
def firstBit : (m : ℕ) → Circuit signature m 1
  | 0 => ⟨Program.empty.gate ⟨Op.const false, ![]⟩, fun _ => Wire.gate 0⟩
  | _ + 1 => ⟨Program.empty.gate ⟨Op.or, ![Wire.input 0, Wire.input 0]⟩, fun _ => Wire.gate 0⟩

theorem size_firstBit (m : ℕ) : (firstBit m).size ≤ 1 := by
  cases m <;> rfl

-- Length and evaluation of `familyAdvice 3 1 firstBit` within and beyond the listed lengths.
example :
    (familyAdvice 3 1 firstBit).length = 4 * certLength 3 1 ∧
    evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [] = false ∧
    evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [true, false] = true ∧
    evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [false, true, true] = false ∧
    evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [true, false] =
      (firstBit 2).eval interpretation (fun i => [true, false][i]) 0 ∧
    evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [true, true, true, true] = true :=
  ⟨length_familyAdvice fun m _ => size_firstBit m,
    by decide, by decide, by decide,
    evalAdvice_familyAdvice (fun m _ => size_firstBit m) (by decide : [true, false].length ≤ 3),
    by decide⟩

/-! ### Nonuniform quantifier elimination and `PH ⊆ P/poly` -/

/-- The language of non-empty bit strings whose first bit is `true`, computed by the 1-gate family
`firstBit`. -/
def firstBitLanguage : Language Bool :=
  Language.ofSlices fun m x => (firstBit m).eval interpretation x 0

theorem firstBitLanguage_mem_PPoly : firstBitLanguage ∈ PPoly :=
  mem_PPoly_iff_exists_mem_SIZE.2 ⟨1, fun m =>
    (complexity_le_of_computes (firstBit m)
      (Circuit.computes_single_iff.2 fun _ =>
        by rw [firstBitLanguage, Language.slice_ofSlices])).trans
      (by simpa using (size_firstBit m).trans (Nat.le_add_left 1 m))⟩

-- Reversing a bit string reduces "last bit is true" to `firstBitLanguage` in polynomial time,
-- witnessing `PolyTimeReducible.mem_PPolyOn` on a concrete reduction without open hypotheses.
example : {x : List Bool | x.reverse ∈ firstBitLanguage} ∈ PPolyOn encBits := by
  have hred : PolyTimeReducible encBits encBits
      {x : List Bool | x.reverse ∈ firstBitLanguage} (firstBitLanguage : Set (List Bool)) :=
    ⟨List.reverse, ComputableInPolyTime.bitsReverse, fun _ => Iff.rfl⟩
  exact hred.mem_PPolyOn (mem_PPolyOn_encBits_iff.2 firstBitLanguage_mem_PPoly)


end Cslib.Complexity.Tests.KarpLipton

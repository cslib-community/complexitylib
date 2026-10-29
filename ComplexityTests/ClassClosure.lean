/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP.Collapse
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.Ladner
import Complexity.Computability.Complexity.Classes.P.Closure
import Complexity.Computability.Complexity.Classes.P.Complement
import Complexity.Computability.Complexity.Classes.PCP.ZeroRandomness
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.RP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Classes.Space.Closure
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.ExactThreeSAT

/-! Verifier combinators on concrete verifiers, closure properties of `#P`, `GapP`, `PP`, `RP`,
`coRP` and `ZPP` applied to concrete problems, and non-vacuity witnesses for the new conditions.
-/

namespace ComplexityTests.ClassClosure

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Verifier combinators -/

/-- Reading the first bit and ignoring two more: `1 * 2 ^ 2` accepted strings of length `3`. -/
example : acceptCount (andVerifier (fun _ : Unit => 1) (fun x => x.2.headD false) fun _ => true)
    () (1 + 2) = 4 := by
  rw [acceptCount_andVerifier_true]
  decide

/-- Two strings of length `2` start with `true`, one is all `false`: three choices in total. -/
example : acceptCount (selectVerifier (allFalseVerifier : Unit × List Bool → Bool)
    fun x => x.2.headD false) () (2 + 1) = 3 := by
  rw [acceptCount_selectVerifier, acceptCount_allFalseVerifier]
  decide

/-- With no bits, a verifier accepts the empty string or nothing. -/
example : acceptCount (fun x : Unit × List Bool => x.2.isEmpty) () 0 = 1 := by
  rw [acceptCount_zero]
  rfl

/-- Reading two bits and accepting when either is `true`: only `false, false` is rejected, so
three of the four strings are accepted. -/
example : acceptCount (orVerifier (fun _ : Unit => 1) (fun x => x.2.headD false)
    fun x => x.2.headD false) () (1 + 1) = 3 := by
  have h := acceptCount_orVerifier (fun _ : Unit => 1) (fun x => x.2.headD false)
    (fun x => x.2.headD false) () 1
  have h₁ : acceptCount (fun x : Unit × List Bool => !x.2.headD false) () 1 = 1 := by decide
  rw [h₁] at h
  omega

/-! ### `#P` and `GapP` -/

example :
    ((1 : List Bool → ℕ) + 1 ∈ SharpP encBits ∧
      (fun w : List Bool => 2 ^ Polynomial.X.eval (encBits w).length) *
        (fun w => 2 ^ Polynomial.X.eval (encBits w).length) ∈ SharpP encBits) ∧
    ((fun w : List Bool => 2 ^ Polynomial.X.eval (encBits w).length) ^ 3 ∈ SharpP encBits ∧
      ∑ i ∈ Finset.range 4, ((i : ℕ) : List Bool → ℕ) ∈ SharpP encBits) ∧
    -((3 : ℕ) : List Bool → ℤ) ∈ GapP encBits :=
  ⟨⟨SharpP.add_one_mem SharpP.one_mem,
    SharpP.mul_mem (SharpP.two_pow_mem _) (SharpP.two_pow_mem _)⟩,
   ⟨SharpP.pow_mem (SharpP.two_pow_mem _) 3,
    SharpP.sum_mem _ fun i _ => SharpP.natCast_mem i⟩,
   GapP.neg_mem (natCast_mem (GapP.subring encBits) 3)⟩

/-- The complementary count of the constant function `1`. -/
example : ∃ p : Polynomial ℕ,
    (fun w : List Bool => 2 ^ p.eval (encBits w).length - 1) ∈ SharpP encBits :=
  let ⟨p, _, h⟩ := SharpP.exists_two_pow_sub_mem (SharpP.one_mem (enc := encBits))
  ⟨p, h⟩

example : (fun _ : List Bool => (1 : ℤ)) * (fun _ => (1 : ℤ)) - (fun _ => (1 : ℤ)) ∈
    GapP encBits := by
  have h : (fun _ : List Bool => (1 : ℤ)) ∈ GapP encBits := by
    simpa using SharpP.natCast_mem_GapP (SharpP.one_mem (enc := encBits))
  exact GapP.sub_mem' (GapP.mul_mem h h) h

/-! ### `PP` -/

/-- The non-strict majority, `GapP`, and `#P` characterizations of `PP`, together with
`ThreeSAT` and `UNSAT` membership in `PP`. -/
example :
    (Set.univ ∈ PP encBits ∧
      (∃ g ∈ GapP encBits, ∀ w, w ∈ (Set.univ : Set (List Bool)) ↔ 0 < g w) ∧
      Set.univ ∈ PP encBits) ∧
    (ThreeSAT ∈ PP encCNF ∧ UNSAT ∈ PP encCNF) :=
  have huniv : (Set.univ : Set (List Bool)) ∈ PP encBits :=
    mem_PP_iff_decidesByNonstrictMajority.2 ⟨0, fun _ => true, .const true, fun _ => by simp⟩
  ⟨⟨huniv, mem_PP_iff_exists_GapP.1 huniv,
    mem_PP_iff_exists_SharpP.2 ⟨1, SharpP.one_mem, 0, fun _ => by simp⟩⟩,
   ⟨(CookLevin.SAT_npHard encCNF ThreeSAT ThreeSAT.mem_NP).mem_PP
      (NP_subset_PP CookLevin.SAT_npComplete.1),
    coNP_subset_PP CookLevin.UNSAT_coNPComplete.1⟩⟩

/-! ### `P`, `RP`, `coRP` and `ZPP` -/

/-- The words starting with `true`. -/
theorem headD_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

example :
    ({w : List Bool | w.headD false = true}ᶜ ∈ coNP encBits ∧
      {w : List Bool | w.headD false = true} \ {w | w.headD false = true}ᶜ ∈ P encBits) ∧
    ({w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ RP encBits ∧
      {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ ZPP encBits ∧
      {w : List Bool | w.headD false = true} ∈ ZPP encBits ∩ (NP encBits ∩ coNP encBits)) ∧
    ({w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ BPP encBits ∧
      {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ BPP encBits) ∧
    ({w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ PSPACE encBits ∧
      {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ PSPACE encBits) :=
  have hc := compl_mem_P headD_mem_P
  ⟨⟨P_subset_coNP hc, diff_mem_P headD_mem_P hc⟩,
   ⟨union_mem_RP (P_subset_RP headD_mem_P) (P_subset_RP hc),
    inter_mem_ZPP (P_subset_ZPP headD_mem_P) (P_subset_ZPP hc),
    ⟨P_subset_ZPP headD_mem_P, ZPP_subset_NP_inter_coNP (P_subset_ZPP headD_mem_P)⟩⟩,
   ⟨inter_mem_BPP (P_subset_BPP headD_mem_P) (P_subset_BPP hc),
    union_mem_BPP (P_subset_BPP headD_mem_P) (P_subset_BPP hc)⟩,
   ⟨inter_mem_PSPACE (P_subset_PSPACE headD_mem_P) (P_subset_PSPACE hc),
    union_mem_PSPACE (P_subset_PSPACE headD_mem_P) (P_subset_PSPACE hc)⟩⟩

/-! ### `SAT` and `P` -/

example :
    (ExactThreeSAT ∈ P encCNF ↔ SAT ∈ P encCNF) ∧
    (UNSAT ∈ P encCNF ↔ ThreeSAT ∈ P encCNF) ∧
    (SAT ∈ P encCNF → BPP encBits = P encBits) :=
  ⟨ExactThreeSAT_npComplete.mem_P_iff_mem_P CookLevin.SAT_npComplete,
   UNSAT_mem_P_iff_SAT_mem_P.trans ThreeSAT_mem_P_iff_SAT_mem_P.symm,
   fun h => BPP_eq_P_of_NP_subset_P fun e => (SAT_mem_P_iff.1 h e).symm.subset⟩

/-! ### `PCP` without randomness -/

example :
    {w : List Bool | w.headD false = true} ∈ PCP (fun _ => 0) (fun _ => 0) encBits ∧
    ∃ k : ℕ, SAT ∈ PCP (fun _ => 0) (fun n => (n + 1) ^ k) encCNF :=
  ⟨PCP_zero_zero.symm ▸ headD_mem_P,
   mem_NP_iff_exists_PCP_zero.1 CookLevin.SAT_npComplete.1⟩

example :
    (PCPVerifier.answers [true, false, true] (List.range [true, false, true].length)).count true =
      2 := by
  rw [PCPVerifier.answers_range_length]
  decide

/-! ### Exact 3SAT -/

example : ExactThreeSAT.padClause [(0, true)] = [(0, true), (0, true), (0, true)] := by decide

example : ExactThreeSAT.padClause [(0, true), (1, false)] = [(0, true), (1, false), (0, true)] := by
  decide

/-- A satisfiable formula with one clause of three literals, one of them repeated. -/
example : [[(0, true), (1, false), (0, true)]] ∈ ExactThreeSAT :=
  ⟨by decide, fun _ => true, by decide⟩

example : toExactThreeSAT [[(0, true)], [(1, false), (2, true)]] =
    [[(0, true), (0, true), (0, true)], [(1, false), (2, true), (1, false)]] := by
  decide

/-- The formula `x₀ ∧ ¬x₀` has no clause wider than three, so its padding is unsatisfiable too. -/
example : toExactThreeSAT [[(0, true)], [(0, false)]] ∉ ExactThreeSAT := by
  rw [mem_ExactThreeSAT_toExactThreeSAT_iff]
  rintro ⟨-, σ, h⟩
  cases hσ : σ 0 <;> simp [hσ] at h

end ComplexityTests.ClassClosure

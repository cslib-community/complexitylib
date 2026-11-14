/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.MINKTStar
public import CslibFrontier.Computability.MCSP.PartialHardness.Evaluator
import CslibFrontier.Computability.Complexity.Problems.CMMSA.Size
import CslibFrontier.Computability.Kolmogorov.MINKTStar.TruthTable
import CslibFrontier.Computability.MCSP.PartialHardness.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Tactic.EncLen

/-!
# The `MINKT*` generator for the CMMSA table

A Yes instance `I` of `GapCMMSA` has an assignment `S` of weight at most `θ` that satisfies every
formula. For every choice of the functions `f`, the partial truth table of
`PartialMCSP.FromCMMSA.toInstance I Δ k λ P f` is then consistent with a total table that is
printed from a short description: the **generator witness** (`GenWitness`). It holds the instance,
`λ` in unary, one term per formula whose variables lie in `S`, and the tables of the functions
`f v` for `v ∈ S` only. Its expansion (`GenWitness.generate`) prints, at the input numbered `x`, the
parity of the chosen term of the indexed formula, computed from those tables by H5b1's evaluator
(`PartialMCSP.FromCMMSA.termParityN`). At a defined entry every term has the entry's parity, so
the printed table is consistent with the pattern (`GenWitness.exists_consistent_generate`).

The tables of the set variables have total length at most `2 w(S) λ ≤ 2 θ λ`
(`PartialMCSP.FromCMMSA.sum_two_pow_varLength_le_two_mul_weight`), so the witness has encoded
length at most `(4 Δ + 3) |enc I| + 3 + (4 θ + 2) λ` (`GenWitness.sizeBound`). A later step bounds
`K^t` of the printed table by this length plus the size of a machine computing `generate` in
polynomial time; the threshold of the `MINKT*` instance is chosen from that.

## Main definitions

* `Cslib.Kolmogorov.MINKTStar.GenWitness`: the generator witness, with its encoding
  `GenWitness.enc`.
* `Cslib.Kolmogorov.MINKTStar.GenWitness.generate`: the printed table.
* `Cslib.Kolmogorov.MINKTStar.GenWitness.sizeBound`: the size bound
  `(4 Δ + 3) |enc I| + 3 + (4 θ + 2) λ`.

## Main results

* `Cslib.Kolmogorov.MINKTStar.GenWitness.exists_consistent_generate`: for a Yes instance and every
  `f`, some witness for `I` and `λ ≥ 1` prints a table consistent with the CMMSA table and has
  encoded length at most `sizeBound`.

## References

The generator and its analysis are the library's own. They give the yes case of the library's
proof of the `MINKT*` clause of [Hirahara2022, Theorem I.2], `MINKTStar.rpHard` in `Hardness.lean`.

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.Kolmogorov.MINKTStar

open Cslib.Complexity Cslib.PartialMCSP.FromCMMSA Turing.MultiTapeTM

/-- **The generator witness**: an instance, `λ`, a term choice per formula and tables of variable
functions. The honest witness of a Yes instance chooses, for each formula, a term whose variables
lie in the satisfying assignment `S`, and lists the table of `f v` at `v ∈ S` and `[]` elsewhere. -/
structure GenWitness where
  /-- The CMMSA instance. -/
  inst : CMMSAInstance
  /-- The parameter `λ` of the table. -/
  lam : ℕ
  /-- Entry `j` is the term printed for formula `j`. -/
  choice : List ℕ
  /-- Entry `v` is the table of `f v`, in the order of `BitString.equivFin`, or `[]`. -/
  tables : List (List Bool)

namespace GenWitness

/-- The witness encoding: the instance, then `λ` and the term choices in unary, then the tables. `λ`
is unary so that the printed table, of length `2 ^ inputLength`, is polynomial in the encoding. -/
enc_structure enc : GenWitness where
  inst : CMMSAInstance.encoding, lam : encUnary, choice : (encList encUnary),
  tables : (encList encBits)

variable (Δ k : ℕ)

/-- The printed bit at the input numbered `x`: the parity of the chosen term of the indexed
formula, computed from the witness tables. -/
@[expose] def genEntry (w : GenWitness) (x : ℕ) : Bool :=
  termParityN w.inst Δ k w.lam w.tables x (w.choice.getD (x % 2 ^ indexWidth w.inst) 0)

/-- **The printed table**: the bits at the inputs numbered `0, …, 2 ^ inputLength - 1`. -/
@[expose] def generate (w : GenWitness) : List Bool :=
  (List.range (2 ^ inputLength w.inst Δ k w.lam)).map (genEntry Δ k w)

/-- The printed table has the length `2 ^ inputLength` of the CMMSA table. -/
@[simp]
theorem length_generate (w : GenWitness) :
    (generate Δ k w).length = 2 ^ inputLength w.inst Δ k w.lam := by
  simp [generate]

/-- The printed table as a list of an indexed table. -/
theorem generate_eq_ofFn (w : GenWitness) :
    generate Δ k w = List.ofFn fun x : Fin (2 ^ inputLength w.inst Δ k w.lam) =>
      genEntry Δ k w x := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [generate]

/-- The size bound of the honest witness: `(4 Δ + 3) |enc I| + 3 + (4 θ + 2) λ`. -/
@[expose] def sizeBound (I : CMMSAInstance) (lam : ℕ) : ℕ :=
  (4 * Δ + 3) * (CMMSAInstance.encoding I).length + 3 + (4 * I.threshold + 2) * lam

/-! ### The honest witness -/

variable {Δ k} {I : CMMSAInstance} {lam : ℕ}

/-- The tables of the variables in `S`, and `[]` at the others. -/
private def setTables (f : VarFunctions I lam) (S : Finset ℕ) : List (List Bool) :=
  (List.range I.weights.length).map fun v => if v ∈ S then varTable f v else []

/-- The honest witness for the term choice `τ` and the assignment `S`. -/
private def ofSat (I : CMMSAInstance) (lam : ℕ) (τ : ℕ → ℕ) (f : VarFunctions I lam)
    (S : Finset ℕ) : GenWitness :=
  ⟨I, lam, (List.range I.formulas.length).map τ, setTables f S⟩

private theorem getD_setTables {f : VarFunctions I lam} {S : Finset ℕ} {v : ℕ} (hv : v ∈ S) :
    (setTables f S).getD v [] = varTable f v := by
  by_cases hvn : v < I.weights.length
  · simp [setTables, List.getD_eq_getElem?_getD, hvn, hv]
  · simp [setTables, varTable, List.getD_eq_getElem?_getD, hvn]

/-- **Consistency.** If `τ j` is a term of formula `j` whose variables lie in `S`, then the honest
witness prints a table consistent with the CMMSA table. -/
private theorem consistent_generate_ofSat (hwf : I.WellFormed Δ) {τ : ℕ → ℕ} {S : Finset ℕ}
    (hτ : ∀ j < I.formulas.length, τ j < (I.formulas.getD j []).length ∧
      ∀ q < (term I j (τ j)).length, var I j (τ j) q ∈ S)
    (f : VarFunctions I lam) :
    Consistent (List.ofFn fun x : Fin (2 ^ inputLength I Δ k lam) =>
        entry (Δ := Δ) (k := k) f ((BitString.equivFin _).symm x))
      (generate Δ k (ofSat I lam τ f S)) := by
  rw [generate_eq_ofFn]
  refine consistent_ofFn_iff.2 fun x b hx => ?_
  have hj : (x : ℕ) % 2 ^ indexWidth I < I.formulas.length := by
    simpa only [formulaIndex_equivFin_symm] using formulaIndex_lt_of_entry_eq_some hx
  obtain ⟨htj, hS⟩ := hτ _ hj
  have hτΔ := htj.trans_le (hwf.length_le (List.getD_mem [] hj))
  have hpar := termParityN_eq (f := f) (T := setTables f S) x ⟨_, hτΔ⟩ fun q hq =>
    IsVarTable.of_getD_eq (getD_setTables (hS q hq))
  have hentry := termParity_eq_of_entry_eq_some hx ⟨_, hτΔ⟩
    (by rw [formulaIndex_equivFin_symm]; exact htj)
  have hchoice : ((List.range I.formulas.length).map τ).getD ((x : ℕ) % 2 ^ indexWidth I) 0 =
      τ ((x : ℕ) % 2 ^ indexWidth I) := by
    simp [List.getD_eq_getElem?_getD, hj]
  simp only [genEntry, ofSat, hchoice]
  exact hpar.trans hentry

/-- **The size bound** of the honest witness, for an assignment `S` of weight at most `θ`. -/
private theorem length_enc_ofSat_le (hwf : I.WellFormed Δ) (hlam : 1 ≤ lam) {τ : ℕ → ℕ}
    {S : Finset ℕ} (hSn : S ⊆ Finset.range I.weights.length) (hw : I.weight S ≤ I.threshold)
    (hτ : ∀ j < I.formulas.length, τ j < (I.formulas.getD j []).length)
    (f : VarFunctions I lam) :
    (enc (ofSat I lam τ f S)).length ≤ sizeBound Δ I lam := by
  -- the term choices: each `τ j < Δ`, so each costs at most `2 Δ`
  have hchoice : (encList encUnary ((List.range I.formulas.length).map τ)).length ≤
      I.formulas.length * (2 * Δ) := by
    rw [length_encList, List.map_map]
    refine (List.sum_le_length_nsmul _ (2 * Δ) fun a ha => ?_).trans (by simp)
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
    have hj' := List.mem_range.1 hj
    have := (hτ j hj').trans_le (hwf.length_le (List.getD_mem [] hj'))
    enc_len [Function.comp_apply]
  -- the tables: `2 ∑_{v ∈ S} 2 ^ ℓ v + n ≤ 4 w(S) λ + n`
  have hsum : ∑ v ∈ Finset.range I.weights.length,
      (if v ∈ S then varTable f v else []).length = ∑ v ∈ S, 2 ^ varLength I lam v := by
    rw [← Finset.sum_subset hSn fun v _ hv => by simp [hv]]
    refine Finset.sum_congr rfl fun v hv => ?_
    simp [hv, varTable, Finset.mem_range.1 (hSn hv)]
  have htables : (encList encBits (setTables f S)).length ≤
      2 * (2 * I.weight S * lam) + I.weights.length := by
    have h := sum_two_pow_varLength_le_two_mul_weight hSn hwf hlam
    rw [length_encList, setTables, List.map_map, List.sum_map_range_eq_sum_range]
    simp only [Function.comp_apply, encBits_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    omega
  have hm := CMMSAInstance.length_formulas_le I
  have hn := CMMSAInstance.length_weights_le I
  have hΔm : I.formulas.length * Δ ≤ (CMMSAInstance.encoding I).length * Δ :=
    Nat.mul_le_mul_right _ hm
  have hwl : I.weight S * lam ≤ I.threshold * lam := Nat.mul_le_mul_right _ hw
  simp only [enc_apply, encFields, length_encPair, encUnary_apply, List.length_replicate, ofSat]
  unfold sizeBound
  nlinarith

/-- **The generator for a Yes instance.** If `I` is a Yes instance of `GapCMMSA Δ g σ`, then for
every `λ ≥ 1` and every choice of the functions `f`, some witness for `I` and `λ` prints a table
consistent with the CMMSA table and has encoded length at most `sizeBound Δ I λ`. -/
theorem exists_consistent_generate (Δ k : ℕ) {g σ : ℝ} (hI : I ∈ (GapCMMSA Δ g σ).yes)
    (hlam : 1 ≤ lam) (f : VarFunctions I lam) :
    ∃ w : GenWitness, w.inst = I ∧ w.lam = lam ∧
      Consistent (List.ofFn fun x : Fin (2 ^ inputLength I Δ k lam) =>
          entry (Δ := Δ) (k := k) f ((BitString.equivFin _).symm x))
        (generate Δ k w) ∧
      (enc w).length ≤ sizeBound Δ I lam := by
  obtain ⟨hwf, S, hSn, hw, hsat⟩ := mem_yes_GapCMMSA.1 hI
  obtain ⟨τ, hτ⟩ := exists_satTerm hwf.monotone hsat
  exact ⟨ofSat I lam τ f S, rfl, rfl, consistent_generate_ofSat hwf hτ f,
    length_enc_ofSat_le hwf hlam hSn hw (fun j hj => (hτ j hj).1) f⟩

end GenWitness

end Cslib.Kolmogorov.MINKTStar

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Basic
public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.Elimination
public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree.Counting
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# #3SAT reduces to the integer permanent (Goldreich, Proposition 6.21)

`cnfToPermanentTable φ` is the integer matrix of Goldreich's proof of Proposition 6.21
[Goldreich, Section 6.2.1][Goldreich2007Draft], [Valiant][Valiant1979]: one auxiliary vertex per
variable, Goldreich's eight-vertex clause gadget (Figure 6.3) per clause, and one cycle of
weight-`1` track edges per literal. Clauses with fewer than three literals are padded by
repeating their last literal; a formula with an empty clause or a clause of more than three
literals is sent to the `1 × 1` zero matrix. Then
`IntPermanent (cnfToPermanentTable φ) = 12 ^ m * SharpThreeSAT φ`, where `m` is the number of
clauses of `φ` (`intPermanent_cnfToPermanentTable`), every entry lies in `{-1, 0, 1, 2, 3}`
(`mem_entries_cnfToPermanentTable`), and the construction is polynomial-time under the formula
encoding `encCNF` and the dense table encoding `encIntTable`
(`computableInPolyTime_cnfToPermanentTable`). This is Goldreich's statement with `c = 12` and
`I = {-1, 0, 1, 2, 3}` (`goldreich_prop_6_21`). Dividing by `12 ^ m` gives a metric reduction
from `#3SAT` to the integer permanent (`metricReducible_sharpThreeSAT_intPermanent`).

The proof uses Goldreich's gadget, verified by evaluation of its minors, and an elimination of
the gadgets one clause at a time. It is not the XOR-gadget construction of the Arora–Barak draft
[Arora and Barak, Theorem 9.8][AroraBarak07], whose draft claims a factor `4 ^ (3 m)` and does not
verify its gadgets.

## Main definitions

* `Cslib.Complexity.cnfToPermanentTable`: the integer matrix of a formula.

## Main results

* `Cslib.Complexity.intPermanent_cnfToPermanentTable`: its permanent.
* `Cslib.Complexity.mem_entries_cnfToPermanentTable`: its entries lie in `{-1, 0, 1, 2, 3}`.
* `Cslib.Complexity.computableInPolyTime_cnfToPermanentTable`: it is polynomial-time.
* `Cslib.Complexity.goldreich_prop_6_21`: Goldreich's Proposition 6.21.
* `Cslib.Complexity.metricReducible_sharpThreeSAT_intPermanent`: `#3SAT` reduces to the integer
  permanent by a metric reduction.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM PermanentThreeSAT PermanentGadget

/-- The integer matrix of Goldreich's Proposition 6.21 for a formula, as a dense table; the
`1 × 1` zero matrix if a clause is empty or has more than three literals. -/
def cnfToPermanentTable (φ : CNF ℕ) : List (List ℤ) :=
  if WellFormed φ then
    (List.range (size φ)).map fun k => (List.range (size φ)).map fun l => matrixEntry φ k l
  else [[0]]

theorem wellFormed_iff_all (φ : CNF ℕ) :
    WellFormed φ ↔ (φ.all fun c => decide (1 ≤ c.length ∧ c.length ≤ 3)) = true := by
  simp [WellFormed]

/-- The permanent of a table listing the entries of a function on `range N`. -/
theorem intPermanent_range_map (N : ℕ) (f : ℕ → ℕ → ℤ) :
    IntPermanent ((List.range N).map fun k => (List.range N).map (f k)) =
      (Matrix.of fun i j : Fin N => f i j).permanent := by
  have hlen : ((List.range N).map fun k => (List.range N).map (f k)).length = N := by simp
  rw [IntPermanent, ← Matrix.permanent_submatrix_equiv_equiv (finCongr hlen.symm)
    (finCongr hlen.symm)]
  congr 1
  ext i j
  simp [tableMatrix_apply, List.getD_eq_getElem?_getD]

/-- The permanent of the table of a well-formed formula is that of its matrix. -/
theorem intPermanent_cnfToPermanentTable_of_wellFormed {φ : CNF ℕ} (hφ : WellFormed φ) :
    IntPermanent (cnfToPermanentTable φ) = (fullMatrix φ).permanent := by
  rw [cnfToPermanentTable, ite_eq_left hφ, intPermanent_range_map]
  rfl

/-- A formula with an empty clause has no satisfying assignment. -/
theorem modelCount_eq_zero_of_nil_mem {φ : CNF ℕ} (h : [] ∈ φ) : φ.modelCount = 0 := by
  rw [CNF.modelCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro τ _ hτ
  rw [CNF.eval_eq_true_iff] at hτ
  exact absurd (hτ [] h) (by simp)

/-- **The permanent of the matrix of a formula** is `12 ^ m` times its number of satisfying
assignments, `m` being the number of clauses. -/
theorem intPermanent_cnfToPermanentTable (φ : CNF ℕ) :
    IntPermanent (cnfToPermanentTable φ) = 12 ^ φ.length * SharpThreeSAT φ := by
  by_cases hφ : WellFormed φ
  · rw [intPermanent_cnfToPermanentTable_of_wellFormed hφ, permanent_fullMatrix hφ,
      SharpThreeSAT, SharpSAT]
    have : (φ.all fun c => decide (c.length ≤ 3)) = true := by
      simp only [List.all_eq_true, decide_eq_true_eq]
      exact fun c hc => (hφ c hc).2
    rw [ite_eq_left this]
  · have hzero : IntPermanent (cnfToPermanentTable φ) = 0 := by
      rw [cnfToPermanentTable, ite_eq_right hφ]
      simp [IntPermanent, Matrix.permanent, tableMatrix_apply]
    rw [hzero]
    unfold SharpThreeSAT
    split_ifs with hall
    · obtain ⟨c, hc, hbad⟩ : ∃ c ∈ φ, ¬(1 ≤ c.length ∧ c.length ≤ 3) := by
        simpa [WellFormed] using hφ
      have hc3 : c.length ≤ 3 := by
        simp only [List.all_eq_true, decide_eq_true_eq] at hall
        exact hall c hc
      have hnil : c = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [SharpSAT, modelCount_eq_zero_of_nil_mem (hnil ▸ hc)]
      simp
    · simp

/-- The gadget entries lie in `{-1, 0, 1, 2, 3}`. -/
theorem gadgetEntry_mem (a b : ℕ) : gadgetEntry a b ∈ ({-1, 0, 1, 2, 3} : Finset ℤ) := by
  unfold gadgetEntry
  have hrow : ∀ r ∈ gadgetRows, ∀ x ∈ r, x ∈ ({-1, 0, 1, 2, 3} : Finset ℤ) := by decide
  by_cases ha : a < gadgetRows.length
  · rw [List.getD_eq_getElem _ _ ha]
    by_cases hb : b < (gadgetRows[a]).length
    · rw [List.getD_eq_getElem _ _ hb]
      exact hrow _ (List.getElem_mem ha) _ (List.getElem_mem hb)
    · rw [List.getD_eq_default (gadgetRows[a]) 0 (by omega)]; decide
  · rw [List.getD_eq_default gadgetRows [] (by omega)]; simp

/-- The gadget entries from exit rows to entry columns lie in `{-1, 0}`. -/
theorem gadgetEntry_exit_entry : ∀ r < 3, ∀ c < 3,
    gadgetEntry (r + 3) c ∈ ({-1, 0} : Finset ℤ) := by
  decide

theorem gadgetPart_mem (φ : CNF ℕ) (k l : ℕ) :
    gadgetPart φ k l ∈ ({-1, 0, 1, 2, 3} : Finset ℤ) := by
  unfold gadgetPart
  split_ifs
  · exact gadgetEntry_mem _ _
  · decide

/-- **The entries of the matrix of a formula lie in `{-1, 0, 1, 2, 3}`.** -/
theorem matrixEntry_mem {φ : CNF ℕ} (hφ : WellFormed φ) {k : ℕ} (hk : k < size φ) (l : ℕ) :
    matrixEntry φ k l ∈ ({-1, 0, 1, 2, 3} : Finset ℤ) := by
  rcases trackEntry_zero_or_one hφ k l with h | h
  · rw [matrixEntry, h, add_zero]; exact gadgetPart_mem φ k l
  · have key : gadgetPart φ k l ∈ ({-1, 0} : Finset ℤ) := by
      by_cases hkn : k < numAux φ
      · unfold gadgetPart
        rw [ite_eq_right (by omega)]
        decide
      · unfold trackEntry at h
        rw [ite_eq_right hkn] at h
        split_ifs at h with hpos hl
        · change exitSucc φ (exitOcc φ k) = l at hl
          have ho := exitOcc_lt (φ := φ) (by omega) hk hpos.2
          rcases e : nextOcc φ (exitOcc φ k) with _ | o'
          · rw [exitSucc_eq_none e] at hl
            have := List.idxOf_lt_length_iff.2 (fst_litAt_mem_varList hφ ho)
            unfold gadgetPart
            rw [ite_eq_right (by unfold numAux at *; omega)]
            decide
          · rw [exitSucc_eq_some e] at hl
            subst hl
            unfold gadgetPart
            split_ifs with hs
            · have hr := gadgetEntry_exit_entry ((k - numAux φ) % 8 - 3) (by omega)
                ((entryIdx φ o' - numAux φ) % 8) (by unfold entryIdx; omega)
              rwa [show (k - numAux φ) % 8 - 3 + 3 = (k - numAux φ) % 8 by omega] at hr
            · decide
        all_goals exact absurd h (by decide)
    rw [matrixEntry, h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at key ⊢
    rcases key with e | e <;> rw [e] <;> decide

/-- **Every entry of the matrix of a formula lies in `{-1, 0, 1, 2, 3}`.** -/
theorem mem_entries_cnfToPermanentTable (φ : CNF ℕ) :
    ∀ row ∈ cnfToPermanentTable φ, ∀ x ∈ row, x ∈ ({-1, 0, 1, 2, 3} : Finset ℤ) := by
  intro row hrow x hx
  by_cases hφ : WellFormed φ
  · rw [cnfToPermanentTable, ite_eq_left hφ] at hrow
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hrow
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact matrixEntry_mem hφ (List.mem_range.1 hk) l
  · rw [cnfToPermanentTable, ite_eq_right hφ] at hrow
    simp only [List.mem_singleton] at hrow
    subst hrow
    simp only [List.mem_singleton] at hx
    subst hx
    decide

theorem computableInPolyTime_size : ComputableInPolyTime size encCNF encUnary := by
  have := computableInPolyTime_numAux
  unfold size encCNF
  fun_prop

theorem computableInPolyTime_wellFormed :
    ComputableInPolyTime (fun φ => decide (WellFormed φ)) encCNF encBool := by
  have h : (fun φ => decide (WellFormed φ)) =
      fun φ : CNF ℕ => φ.all fun c => decide (1 ≤ c.length ∧ c.length ≤ 3) := by
    funext φ
    exact Bool.eq_iff_iff.2 (by simpa using wellFormed_iff_all φ)
  rw [h]
  unfold encCNF
  fun_prop

/-- **The matrix of a formula is computable in polynomial time**, from the formula under
`encCNF` to the dense table under `encIntTable`. -/
theorem computableInPolyTime_cnfToPermanentTable :
    ComputableInPolyTime cnfToPermanentTable encCNF encIntTable := by
  have hentry := computableInPolyTime_matrixEntry
  have hsize := computableInPolyTime_size
  have hwf := computableInPolyTime_wellFormed
  have hrow : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ => (List.range (size p.1)).map fun l => matrixEntry p.1 p.2 l)
      (encPair encCNF encUnary) (encList encIntBin) := by
    fun_prop
  have htable : ComputableInPolyTime
      (fun φ : CNF ℕ => (List.range (size φ)).map fun k =>
        (List.range (size φ)).map fun l => matrixEntry φ k l) encCNF encIntTable := by
    fun_prop
  have h : cnfToPermanentTable = fun φ => if decide (WellFormed φ) then
      (List.range (size φ)).map (fun k => (List.range (size φ)).map fun l => matrixEntry φ k l)
      else [[0]] := by
    funext φ
    simp [cnfToPermanentTable]
  rw [h]
  fun_prop

/-- **Goldreich, Proposition 6.21.** There are an even integer `c > 0`, a finite set `I` of
integers and a polynomial-time map from formulas to integer matrices with entries in `I` whose
permanent is `c ^ m` times the number of satisfying assignments counted by `#3SAT`, `m` being the
number of clauses: `c = 12` and `I = {-1, 0, 1, 2, 3}`. -/
theorem goldreich_prop_6_21 :
    ∃ c : ℕ, Even c ∧ 0 < c ∧ ∃ I : Finset ℤ, ∃ r : CNF ℕ → List (List ℤ),
      ComputableInPolyTime r encCNF encIntTable ∧
      ∀ φ, (∀ row ∈ r φ, ∀ x ∈ row, x ∈ I) ∧ IntPermanent (r φ) = c ^ φ.length * SharpThreeSAT φ :=
  ⟨12, ⟨6, rfl⟩, by norm_num, {-1, 0, 1, 2, 3}, cnfToPermanentTable,
    computableInPolyTime_cnfToPermanentTable,
    fun φ => ⟨mem_entries_cnfToPermanentTable φ, by
      rw [intPermanent_cnfToPermanentTable]; push_cast; rfl⟩⟩

/-- **`#3SAT` reduces to the integer permanent by a metric reduction**: build the matrix of the
formula and divide its permanent by `12 ^ m`. -/
theorem metricReducible_sharpThreeSAT_intPermanent :
    MetricReducible encCNF encIntTable encNat encIntBin SharpThreeSAT IntPermanent := by
  refine ⟨cnfToPermanentTable, fun p => p.2.toNat / ((12 : ℤ) ^ p.1.length).toNat,
    computableInPolyTime_cnfToPermanentTable, ?_, fun φ => ?_⟩
  · unfold encCNF
    fun_prop
  · simp only [intPermanent_cnfToPermanentTable]
    rw [show (12 : ℤ) ^ φ.length = ((12 ^ φ.length : ℕ) : ℤ) by push_cast; rfl,
      Int.toNat_natCast, show ((12 ^ φ.length : ℕ) : ℤ) * (SharpThreeSAT φ : ℤ) =
        ((12 ^ φ.length * SharpThreeSAT φ : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast,
      Nat.mul_div_cancel_left _ (by positivity)]

end Cslib.Complexity

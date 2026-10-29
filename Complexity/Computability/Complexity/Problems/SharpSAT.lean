/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Problems.USAT
public import Complexity.Logics.Propositional.CNF.ModelCount
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Counting satisfying assignments: #SAT

`SharpSAT φ` is the number of satisfying assignments of a formula `φ` in conjunctive normal form
over variables numbered by `ℕ`: the assignments of the variables occurring in `φ` that satisfy it
(`Cslib.Logic.PL.CNF.modelCount`). Valiant showed that `#SAT` is complete for `#P` under
parsimonious reductions [Valiant][Valiant1979], [Arora and Barak, Section 17.3][AroraBarak09];
completeness is proved in `Complexity/Computability/Complexity/CookLevin/Counting.lean`.

`#SAT` belongs to `#P` (`Cslib.Complexity.SharpSAT.mem_SharpP`). The verifier of `SAT`
(`Cslib.Complexity.SAT.verifier`) reads the value of each variable at the position of its first
occurrence in `φ.vars` and ignores the other bits of the certificate, so it accepts each
satisfying assignment once for every setting of the ignored bits. The counting verifier
`Cslib.Complexity.SharpSAT.verifier` asks in addition that the ignored bits be `false`
(`Cslib.Complexity.SharpSAT.canonical`). It then accepts exactly one certificate of length
`|encCNF φ|` for each satisfying assignment (`Cslib.Complexity.SharpSAT.acceptCount_verifier`).

## Main definitions

* `Cslib.Complexity.SharpSAT`: the number of satisfying assignments.
* `Cslib.Complexity.SharpSAT.isFirst`: testing for the first occurrence of a variable.
* `Cslib.Complexity.SharpSAT.canonical`, `Cslib.Complexity.SharpSAT.verifier`: the canonical
  certificates and the counting verifier.

## Main results

* `Cslib.Complexity.SharpSAT.mem_SAT_iff`, `Cslib.Complexity.SharpSAT.mem_USAT_iff`: `SAT` and
  `USAT` through `#SAT`.
* `Cslib.Complexity.SharpSAT.acceptCount_verifier`: the verifier accepts one certificate for each
  satisfying assignment.
* `Cslib.Complexity.SharpSAT.computableInPolyTime_card_vars`: the number of occurring
  variables is computable in polynomial time in unary.
* `Cslib.Complexity.SharpSAT.computableInPolyTime_verifier`: the verifier is
  polynomial-time.
* `Cslib.Complexity.SharpSAT.mem_SharpP`: `#SAT` belongs to `#P`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- **#SAT**: the number of satisfying assignments of a formula over variables numbered by `ℕ`,
counting assignments of the variables occurring in the formula. -/
def SharpSAT (φ : CNF ℕ) : ℕ := φ.modelCount

namespace SharpSAT

/-- A formula is satisfiable exactly when it has a satisfying assignment. -/
theorem mem_SAT_iff {φ : CNF ℕ} : φ ∈ SAT ↔ 0 < SharpSAT φ :=
  CNF.modelCount_pos_iff.symm

/-- A formula is uniquely satisfiable exactly when it has one satisfying assignment. -/
theorem mem_USAT_iff {φ : CNF ℕ} : φ ∈ USAT ↔ SharpSAT φ = 1 :=
  CNF.modelCount_eq_one_iff.symm

/-! ### The counting verifier -/

/-- Position `i` of a certificate for `φ` is the first occurrence of a variable in `φ.vars`. -/
def isFirst (φ : CNF ℕ) (i : ℕ) : Bool :=
  decide (i < φ.vars.length) && φ.vars.idxOf (φ.vars.getD i 0) == i

/-- A certificate for `φ` is canonical when it is `false` at every position that is not the first
occurrence of a variable. -/
def canonical (φ : CNF ℕ) (w : List Bool) : Bool :=
  (List.range w.length).all fun i => !w.getD i false || isFirst φ i

/-- The verifier for `#SAT`: the certificate is canonical and describes a satisfying assignment,
read at the first occurrences of the variables. -/
def verifier (x : CNF ℕ × List Bool) : Bool := SAT.verifier x && canonical x.1 x.2

private theorem isFirst_idxOf {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) :
    isFirst φ (φ.vars.idxOf v) = true := by
  have hlt := List.idxOf_lt_length_iff.2 hv
  simp [isFirst, hlt]

private theorem getD_mem_of_isFirst {φ : CNF ℕ} {i : ℕ} (h : isFirst φ i = true) :
    φ.vars.getD i 0 ∈ φ.vars ∧ φ.vars.idxOf (φ.vars.getD i 0) = i := by
  simp only [isFirst, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨by rw [List.getD_eq_getElem _ _ h.1]; exact List.getElem_mem h.1, h.2⟩

theorem canonical_eq_true_iff {φ : CNF ℕ} {w : List Bool} :
    canonical φ w = true ↔ ∀ i < w.length, w.getD i false = true → isFirst φ i = true := by
  simp only [canonical, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  refine forall₂_congr fun i _ => ?_
  cases w.getD i false <;> simp

/-- **The counting verifier accepts one certificate for each satisfying assignment**: the
certificates of length `|encCNF φ|` it accepts are as many as the satisfying assignments of `φ`. -/
theorem acceptCount_verifier (φ : CNF ℕ) :
    acceptCount verifier φ (encCNF φ).length = SharpSAT φ := by
  have hlt {v : ℕ} (hv : v ∈ φ.vars) : φ.vars.idxOf v < (encCNF φ).length :=
    (List.idxOf_lt_length_iff.2 hv).trans_le (SAT.length_vars_le φ)
  symm
  refine CNF.modelCount_eq_card_filter
    (fun σ (i : Fin (encCNF φ).length) => isFirst φ i && σ (φ.vars.getD i 0))
    (fun w => verifier (φ, List.ofFn w) = true) (fun σ τ _ _ => ⟨fun h v hv => ?_,
      fun h => funext fun i => ?_⟩) fun w => ⟨fun hw => ?_, ?_⟩
  · have := congrFun h ⟨_, hlt hv⟩
    simp only [isFirst_idxOf hv, List.getD_idxOf hv 0, Bool.true_and] at this
    exact this
  · cases hi : isFirst φ i
    · rfl
    · simp only [Bool.true_and]
      exact h _ (getD_mem_of_isFirst hi).1
  · simp only [verifier, Bool.and_eq_true] at hw
    obtain ⟨hsat, hcan⟩ := hw
    refine ⟨SAT.assignment φ (List.ofFn w), hsat, funext fun i => ?_⟩
    cases hi : isFirst φ i
    · rw [Bool.false_and]
      cases hwi : w i
      · rfl
      · have := canonical_eq_true_iff.1 hcan i (by simp) (by rw [List.getD_ofFn, hwi])
        rw [hi] at this
        exact absurd this Bool.false_ne_true
    · rw [Bool.true_and, SAT.assignment, (getD_mem_of_isFirst hi).2, List.getD_ofFn]
  · rintro ⟨σ, hσ, rfl⟩
    simp only [verifier, Bool.and_eq_true]
    refine ⟨?_, canonical_eq_true_iff.2 fun i hi h => ?_⟩
    · change φ.eval (SAT.assignment φ _) = true
      refine (CNF.eval_congr fun v hv => ?_).trans hσ
      rw [SAT.assignment, List.getD_ofFn_of_lt _ (hlt hv) false]
      dsimp only
      rw [isFirst_idxOf hv, List.getD_idxOf hv 0, Bool.true_and]
    · rw [List.length_ofFn] at hi
      rw [List.getD_ofFn_of_lt _ hi false, Bool.and_eq_true] at h
      exact h.1

/-! ### Polynomial time -/

/-- Testing for a first occurrence is polynomial-time, with the position in unary. -/
@[fun_prop]
theorem computableInPolyTime_isFirst :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => isFirst p.1 p.2)
      (encPair encCNF encUnary) encBool := by
  fun_prop [isFirst]

/-- The number of distinct variables occurring in `φ` is computable in polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_card_vars :
    ComputableInPolyTime (fun φ : CNF ℕ => φ.vars.toFinset.card) encCNF encUnary :=
  (CNF.computableInPolyTime_numVars encNat)

/-- The counting verifier is polynomial-time, including on certificates of arbitrary length. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encCNF encBits) encBool := by
  fun_prop [verifier, canonical]

/-- **`#SAT` belongs to `#P`**, with certificates as long as the encoded formula. -/
theorem mem_SharpP : SharpSAT ∈ SharpP encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, fun φ => by
    rw [Polynomial.eval_X, acceptCount_verifier]⟩

end SharpSAT

end Cslib.Complexity

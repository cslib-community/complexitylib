/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Selective
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Complexity.Classes.NP.SelfReduction
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# NP-hard P-selective sets: Selman's theorem

If some `NP`-hard set is P-selective, then `P = NP` [Selman1979]; see also
[Hemaspaandra and Torenvliet][HemaspaandraTorenvliet2003]. P-selectivity transfers
down polynomial-time reductions, so `SAT` would be P-selective, and a selector for `SAT` decides
it through the self-reduction of `SAT`
(`Cslib.Complexity.SAT.verifier_search_of_step`): to fix the next variable `v` of a satisfiable
formula `χ`, ask the selector to choose between `χ ∧ v` and `χ ∧ ¬v`. One of the two is
satisfiable, so the chosen one is, and fixing `v` to the chosen value keeps the formula
satisfiable. After the last variable the fixed values satisfy the input formula when it is
satisfiable, which the verifier checks; the answers of the selector need not be correct
membership answers.

## Main results

* `Cslib.Complexity.SAT.mem_P_of_mem_PSel`: if `SAT` is P-selective, it is in `P`.
* `Cslib.Complexity.SAT.mem_PSel_iff_mem_P`: `SAT` is P-selective exactly when it is in `P`.
* `Cslib.Complexity.NPHard.P_eq_NP_of_mem_PSel`: **Selman's theorem**, a P-selective `NP`-hard
  set gives `P = NP` for every encoding.
* `Cslib.Complexity.NPComplete.mem_PSel_iff`: an `NP`-complete set is P-selective exactly when
  `P = NP`.

## References

* [A. L. Selman, *P-selective sets, tally languages, and the behavior of polynomial time
  reducibilities on NP*][Selman1979]
* [L. A. Hemaspaandra and L. Torenvliet, *Theory of Semi-Feasible
  Algorithms*][HemaspaandraTorenvliet2003]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SAT

/-- Negate the literals of the last clause of a formula. On `χ ∧ v` it gives `χ ∧ ¬v`
(`flipLast_append_unit`). -/
private def flipLast (ψ : CNF ℕ) : CNF ℕ :=
  (((ψ.reverse.headD []).map fun l => (l.1, !l.2)) :: ψ.reverse.tail).reverse

private theorem flipLast_append_unit (χ : CNF ℕ) (v : ℕ) (b : Bool) :
    flipLast (χ ++ [[(v, b)]]) = χ ++ [[(v, !b)]] := by
  simp [flipLast]

private theorem computableInPolyTime_flipLast : ComputableInPolyTime flipLast encCNF encCNF := by
  unfold flipLast encCNF
  fun_prop

/-- The query answers built from a selector `f`: on `χ ∧ v`, answer `true` exactly when `f`
picks `χ ∧ v` over `χ ∧ ¬v`. -/
private def selectorQuery (f : CNF ℕ → CNF ℕ → CNF ℕ) (ψ : CNF ℕ) : Bool :=
  decide (f ψ (flipLast ψ) = ψ)

/-- Fixing `v` to the value chosen by a selector for `SAT` keeps a satisfiable formula
satisfiable. -/
private theorem selectorQuery_step {f : CNF ℕ → CNF ℕ → CNF ℕ} (hf : IsSelector SAT f)
    {χ : CNF ℕ} (v : ℕ) (hχ : χ.Satisfiable) :
    (χ ++ [[(v, selectorQuery f (χ ++ [[(v, true)]]))]]).Satisfiable := by
  obtain ⟨σ, hσ⟩ := hχ
  have hone : χ ++ [[(v, true)]] ∈ SAT ∨ χ ++ [[(v, false)]] ∈ SAT := by
    cases hv : σ v
    · exact .inr ⟨σ, by simp [CNF.eval_append, hσ, hv]⟩
    · exact .inl ⟨σ, by simp [CNF.eval_append, hσ, hv]⟩
  have hmem := hf.mem hone
  rw [selectorQuery, flipLast_append_unit, Bool.not_true]
  by_cases h : f (χ ++ [[(v, true)]]) (χ ++ [[(v, false)]]) = χ ++ [[(v, true)]]
  · rw [decide_eq_true h]
    rw [h] at hmem
    exact hmem
  · rw [decide_eq_false h]
    rw [(hf.eq_or_eq _ _).resolve_left h] at hmem
    exact hmem

/-- **A P-selective `SAT` is in `P`**: run the self-reduction, letting the polynomial-time
selector choose between the two values of each variable, and check the values found with the
verifier. -/
theorem mem_P_of_mem_PSel (h : SAT ∈ PSel encCNF) : SAT ∈ P encCNF := by
  classical
  obtain ⟨f, hf, hsel⟩ := h
  have hD : ComputableInPolyTime (selectorQuery f) encCNF encBool := by
    unfold selectorQuery
    exact ComputableInPolyTime.decide_eq'
      (hf.comp (ComputableInPolyTime.id'.prod computableInPolyTime_flipLast))
      ComputableInPolyTime.id'
  refine ⟨fun φ => verifier (φ, search (selectorQuery f) φ), ?_, fun φ => ⟨fun hφ => ?_, ?_⟩⟩
  · exact computableInPolyTime_verifier.comp (ComputableInPolyTime.id'.prod
      (computableInPolyTime_search (D := fun _ => selectorQuery f) (hD.comp (.snd _ _))
        ComputableInPolyTime.id'))
  · exact verifier_search_of_step (fun _ _ _ v _ hsat => selectorQuery_step hsel v hsat) hφ
  · exact fun h => ⟨_, h⟩

/-- `SAT` is P-selective exactly when it is in `P`. -/
theorem mem_PSel_iff_mem_P : SAT ∈ PSel encCNF ↔ SAT ∈ P encCNF :=
  ⟨mem_P_of_mem_PSel, fun h => P_subset_PSel h⟩

end SAT

/-- **Selman's theorem.** If an `NP`-hard set is P-selective, then `P = NP`, for every encoding of
instances: `SAT` reduces to it, so `SAT` is P-selective and hence in `P` [Selman1979]. -/
theorem NPHard.P_eq_NP_of_mem_PSel {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hB : NPHard encB B) (h : B ∈ PSel encB) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P
    (SAT.mem_P_of_mem_PSel ((hB encCNF SAT SAT.mem_NP).mem_PSel h)) enc

/-- **An `NP`-complete set is P-selective exactly when `P = NP`**, for every encoding of
instances. -/
theorem NPComplete.mem_PSel_iff {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hB : NPComplete encB B) :
    B ∈ PSel encB ↔ ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc :=
  ⟨fun h _ enc => NPHard.P_eq_NP_of_mem_PSel hB.2 h enc,
    fun h => P_subset_PSel (h encB ▸ hB.1)⟩

end Cslib.Complexity

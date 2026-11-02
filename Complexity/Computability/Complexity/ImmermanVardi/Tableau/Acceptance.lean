/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.ImmermanVardi.Tableau.Definability
import Mathlib.Tactic.FinCases

/-!
# FO(LFP) sentences for native machine acceptance

One sentence expresses that a given deterministic native machine has halted with output
`[true]` by the maximum time in a finite ordered domain. The sentence is uniform in the
input structure and the domain size. Its input-symbol formulas are ordinary first-order
formulas, so no computational predicate is hidden in an added relation.

## Main results

* `exists_acceptance_sentence`: native bounded machine acceptance has a single checked
  FO(LFP) sentence, given the first-order interpretation of its input tape.
-/

public section

namespace Cslib.Complexity.ImmermanVardi.Tableau

open Turing Turing.MultiTapeTM
open FirstOrder Language
open Cslib.Logic.FO
open Cslib.Logic.FO.Operator

variable {L : Language} {ι : Type} {size : ι → ℕ}
  [∀ i, L.Structure (Fin (size i))] [∀ i, Fact (2 ≤ size i)]
  {m : ℕ} {State : Type} [Fintype State]

private def maximum (i : ι) : Fin (size i) :=
  ⟨size i - 1, Nat.sub_lt (by have := (Fact.out : 2 ≤ size i); omega) (by omega)⟩

private theorem trace_lfp_definable_terms (tm : MultiTapeTM m Bool State)
    (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    {α : Type} (args : Fin 3 → (Ordered.language L).Term α) :
    Operator.Definable (L := Ordered.language L) LFP.policy
      (fun i => Fin (size i)) (fun _ => LFP.interpretation) (fun _ => RelEnv.empty)
      (fun i v => (fun j => (args j).realize v) ∈ (traceStep tm (input i)).lfp) := by
  apply LFP.definable_lfp (fun i _ => traceStep tm (input i)) args
  exact traceStep_polarityDefinable tm input inputFormula hinput Sum.inr

private theorem row_at_maximum_definable (tm : MultiTapeTM m Bool State)
    (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    (hn : ∀ i, (input i).length + 1 < size i)
    (hB : ∀ i, Fintype.card (Tag m State) ≤ size i) (q : Tag m State) :
    Operator.Definable (L := Ordered.language L) LFP.policy
      (fun i => Fin (size i)) (fun _ => LFP.interpretation) (fun _ => RelEnv.empty)
      (fun i (_ : Empty → Fin (size i)) =>
        row (tm.runFrom (tm.initCfg (input i)) (size i - 1)) q (maximum (size := size) i)) := by
  have hf : Operator.Definable (L := Ordered.language L) LFP.policy
      (fun i => Fin (size i)) (fun _ => LFP.interpretation) (fun _ => RelEnv.empty)
      (fun i (_ : Empty → Fin (size i)) =>
        traceRow (traceStep tm (input i)).lfp (maximum (size := size) i) q
          (maximum (size := size) i)) := by
    apply Definable.ex
    apply Definable.conj
    · exact (Definable.ofFO (Ordered.natEq L (tagIndex q) (.var none))).congr
        fun _ _ => Ordered.realize_natEq _ _ _
    · apply (trace_lfp_definable_terms tm input inputFormula hinput
        ![.var none, Ordered.max L, Ordered.max L]).congr
      intro i v
      have hm : (Ordered.max L).realize v = maximum (size := size) i :=
        Fin.ext (Ordered.realize_max_val _)
      have htuple :
          (fun j => ((![.var none, Ordered.max L, Ordered.max L] :
            Fin 3 → (Ordered.language L).Term (Option Empty)) j).realize v) =
            ![v none, maximum (size := size) i, maximum (size := size) i] := by
        ext j
        fin_cases j <;> simp [hm]
      rw [htuple]
  exact hf.congr fun i _ => traceRow_lfp tm (input i) (hn i) (hB i)
    (maximum (size := size) i) q (maximum (size := size) i)

/-- A native deterministic machine's acceptance by the domain's final time is described by one
checked FO(LFP) sentence. All input symbols are interpreted by ordinary first-order formulas. -/
theorem exists_acceptance_sentence (tm : MultiTapeTM m Bool State)
    (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    (hn : ∀ i, (input i).length + 1 < size i)
    (hB : ∀ i, Fintype.card (Tag m State) ≤ size i) :
    ∃ φ : LFP.Formula (Ordered.language L) [] Empty, ∀ i,
      φ.Realize (M := Fin (size i)) RelEnv.empty (fun e => nomatch e) ↔
        (tm.runFrom (tm.initCfg (input i)) (size i - 1)).Halted ∧
          (tm.runFrom (tm.initCfg (input i)) (size i - 1)).output = [true] := by
  have hs := row_at_maximum_definable tm input inputFormula hinput hn hB (.state none)
  have ho := row_at_maximum_definable tm input inputFormula hinput hn hB (.out (.one true))
  obtain ⟨φ, hwf, hφ⟩ := hs.conj ho
  refine ⟨⟨φ, hwf⟩, fun i => ?_⟩
  exact (hφ i (fun e => nomatch e)).trans (by
    simp only [row, Tag.feature, Feature.Holds, OutView.ofList_eq_one_iff, Cfg.Halted])

end Cslib.Complexity.ImmermanVardi.Tableau

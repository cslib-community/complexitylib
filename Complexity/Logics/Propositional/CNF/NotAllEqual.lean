/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne

/-!
# Not-all-equal semantics

`CNF.evalNAE` requires a true and a false literal in every clause, using the existing signed
CNF representation. Empty and singleton clauses are false; the empty formula is true.

## Main definitions

* `CNF.evalNAE`, `CNF.NAESatisfiable`: not-all-equal evaluation and satisfiability.

## Main results

* `CNF.evalNAE_complement`: complementing all variables preserves evaluation.
* `CNF.naeSatisfiable_relabel`: injective variable renaming preserves satisfiability.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V W : Type*}

/-- Complementing every variable negates each literal's value. -/
@[simp]
theorem Literal.eval_complement (σ : V → Bool) (l : Literal V) :
    Literal.eval (fun v => !σ v) l = !Literal.eval σ l := by
  rcases l with ⟨v, b⟩
  cases b <;> cases σ v <;> rfl

/-- Each clause has both a true and a false literal. -/
def CNF.evalNAE (σ : V → Bool) (φ : CNF V) : Bool :=
  φ.eval σ && φ.eval (fun v => !σ v)

/-- Some assignment makes every clause not all equal. -/
def CNF.NAESatisfiable (φ : CNF V) : Prop := ∃ σ, φ.evalNAE σ = true

/-- Global complementation preserves not-all-equal evaluation. -/
@[simp]
theorem CNF.evalNAE_complement (σ : V → Bool) (φ : CNF V) :
    φ.evalNAE (fun v => !σ v) = φ.evalNAE σ := by
  simp [evalNAE, Bool.and_comm]

/-- Not-all-equal evaluation depends only on the occurring variables. -/
theorem CNF.evalNAE_congr {σ τ : V → Bool} {φ : CNF V}
    (h : ∀ v ∈ φ.vars, σ v = τ v) : φ.evalNAE σ = φ.evalNAE τ := by
  unfold evalNAE
  rw [eval_congr h, eval_congr (fun v hv => congrArg Bool.not (h v hv))]

/-- NAE satisfaction of a blockwise formula is satisfaction of every block. -/
theorem CNF.evalNAE_flatMap_eq_true_iff {ι : Type*} (σ : V → Bool) (l : List ι)
    (f : ι → CNF V) :
    CNF.evalNAE σ (l.flatMap f) = true ↔ ∀ i ∈ l, (f i).evalNAE σ = true := by
  simp only [evalNAE, Bool.and_eq_true, eval_flatMap_eq_true_iff]
  exact ⟨fun h i hi => ⟨h.1 i hi, h.2 i hi⟩,
    fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩⟩

/-- Relabelling evaluates the composite assignment. -/
@[simp]
theorem CNF.evalNAE_relabel (f : V → W) (σ : W → Bool) (φ : CNF V) :
    (φ.relabel f).evalNAE σ = φ.evalNAE (σ ∘ f) := by
  simp [evalNAE, Function.comp_def]

/-- Injective renaming preserves not-all-equal satisfiability. -/
theorem CNF.naeSatisfiable_relabel {f : V → W} (hf : Function.Injective f) (φ : CNF V) :
    (φ.relabel f).NAESatisfiable ↔ φ.NAESatisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ f, by simpa using hσ⟩
  · rintro ⟨σ, hσ⟩
    classical
    let τ : W → Bool := Function.extend f σ (fun _ => false)
    refine ⟨τ, ?_⟩
    simpa only [evalNAE_relabel, τ, Function.extend_comp hf] using hσ

/-- An exact-one triple is encoded by four not-all-equal triples and a true reference literal. -/
def Clause.oneNAEEncoding (t a b c : Literal V) : CNF V :=
  [[a, b, c], [a, b, t], [a, c, t], [b, c, t]]

/-- With a true reference literal, the four NAE clauses express exactly one true position. -/
theorem Clause.eval_oneNAEEncoding (σ : V → Bool) (t a b c : Literal V)
    (ht : Literal.eval σ t = true) :
    (oneNAEEncoding t a b c).evalNAE σ = Clause.evalOne σ [a, b, c] := by
  cases ha : Literal.eval σ a <;> cases hb : Literal.eval σ b <;>
    cases hc : Literal.eval σ c <;>
    simp [oneNAEEncoding, CNF.evalNAE, CNF.eval, Clause.eval, Clause.evalOne,
      ht, ha, hb, hc]

end Cslib.Logic.PL

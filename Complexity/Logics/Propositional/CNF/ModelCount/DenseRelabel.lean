/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
public import Complexity.Logics.Propositional.CNF.Compact.Relabel
public import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Dense variable numbering for CNF formulas

`CNF.denseRelabel φ` renames each variable of a CNF formula `φ` by its index in `φ.distinctVars`.
Unlike `CNF.compact` (which uses first positions in `φ.vars` and can leave gaps when variables
repeat), `CNF.denseRelabel φ` maps the occurring variables bijectively onto `0, …, φ.numVars - 1`
in order of first occurrence [OpenAI2026ETH, Section 2].

The renaming preserves clause lengths, clause count, `numVars`, `Satisfiable`, `modelCount`, and
gives `φ.denseRelabel.modelCountOn (Finset.range φ.numVars) = φ.modelCount`. It is computable in
polynomial time for any variable encoding, both into unary variable indices and into binary
natural-number indices (`encCNF`).

## Main definitions

* `Cslib.Logic.PL.CNF.denseRelabel`: rename variables by their positions in `distinctVars`.

## Main results

* `Cslib.Logic.PL.CNF.vars_denseRelabel_toFinset`,
  `Cslib.Logic.PL.CNF.numVars_denseRelabel`,
  `Cslib.Logic.PL.CNF.distinctVars_denseRelabel`: the occurring variables of `φ.denseRelabel` are
  `0, …, φ.numVars - 1` in order.
* `Cslib.Logic.PL.CNF.satisfiable_denseRelabel`,
  `Cslib.Logic.PL.CNF.modelCount_denseRelabel`,
  `Cslib.Logic.PL.CNF.modelCountOn_denseRelabel`: satisfiability and model counts are preserved.
* `Cslib.Logic.PL.CNF.computableInPolyTime_denseRelabel_unary`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_denseRelabel`,
  `Cslib.Complexity.SAT.computableInPolyTime_denseRelabel`: dense relabeling is computable in
  polynomial time.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {V : Type*} [DecidableEq V]

/-- Rename each variable of `φ` by its index in `φ.distinctVars`, producing dense variable indices
`0, …, φ.numVars - 1`. -/
def denseRelabel (φ : CNF V) : CNF ℕ :=
  φ.relabel φ.distinctVars.idxOf

/-- Dense relabeling preserves all clause lengths in order. -/
@[simp]
theorem map_length_denseRelabel (φ : CNF V) :
    φ.denseRelabel.map List.length = φ.map List.length := by
  simp [denseRelabel, CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]

/-- Dense relabeling preserves the number of clauses. -/
@[simp]
theorem length_denseRelabel (φ : CNF V) :
    φ.denseRelabel.length = φ.length := by
  simp [denseRelabel, CNF.relabel]

/-- Dense relabeling preserves any uniform upper bound on clause lengths. -/
theorem all_length_le_denseRelabel {k : ℕ} (φ : CNF V) :
    (∀ c ∈ φ.denseRelabel, c.length ≤ k) ↔ ∀ c ∈ φ, c.length ≤ k := by
  simp [denseRelabel, CNF.relabel]

/-- The occurring variables of `φ.denseRelabel` are `Finset.range φ.numVars`. -/
@[simp]
theorem vars_denseRelabel_toFinset (φ : CNF V) :
    φ.denseRelabel.vars.toFinset = Finset.range φ.numVars :=
  vars_dense_relabel φ

/-- Every variable occurring in `φ.denseRelabel` is strictly below `φ.numVars`. -/
theorem mem_vars_denseRelabel_lt (φ : CNF V) {v : ℕ} (hv : v ∈ φ.denseRelabel.vars) :
    v < φ.numVars := by
  have hv' : v ∈ φ.denseRelabel.vars.toFinset := List.mem_toFinset.mpr hv
  rwa [vars_denseRelabel_toFinset, Finset.mem_range] at hv'

/-- Dense relabeling preserves the number of distinct occurring variables. -/
@[simp]
theorem numVars_denseRelabel (φ : CNF V) :
    φ.denseRelabel.numVars = φ.numVars := by
  rw [numVars, vars_denseRelabel_toFinset, Finset.card_range]

private theorem map_idxOf_of_nodup {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) :
    l.map l.idxOf = List.range l.length := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact List.Nodup.idxOf_getElem hl i _

/-- The distinct variables of `φ.denseRelabel` in order of first occurrence are
`0, …, φ.numVars - 1`. -/
@[simp]
theorem distinctVars_denseRelabel (φ : CNF V) :
    φ.denseRelabel.distinctVars = List.range φ.numVars := by
  have hinj : Set.InjOn φ.distinctVars.idxOf {v | v ∈ φ.vars} :=
    fun _ ha _ _ h => (List.idxOf_inj (mem_distinctVars.mpr ha)).mp h
  rw [denseRelabel, distinctVars_relabel_of_injOn φ φ.distinctVars.idxOf hinj,
    map_idxOf_of_nodup φ.distinctVars φ.nodup_distinctVars, length_distinctVars]

/-- Reading original variable values at their `distinctVars` indices recovers the evaluation of
`φ`. -/
theorem eval_denseRelabel (φ : CNF V) (σ : V → Bool) :
    φ.denseRelabel.eval (fun i => φ.distinctVars[i]?.elim false σ) = φ.eval σ := by
  rw [denseRelabel, CNF.eval_relabel]
  apply CNF.eval_congr
  intro v hv
  have hv' : v ∈ φ.distinctVars := mem_distinctVars.mpr hv
  simp [List.getElem?_idxOf hv']

/-- Dense relabeling preserves satisfiability. -/
@[simp]
theorem satisfiable_denseRelabel (φ : CNF V) :
    φ.denseRelabel.Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ φ.distinctVars.idxOf, by simpa only [denseRelabel, CNF.eval_relabel] using hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨fun i => φ.distinctVars[i]?.elim false σ, (eval_denseRelabel φ σ).trans hσ⟩

/-- Dense relabeling preserves the occurring-variable model count. -/
@[simp]
theorem modelCount_denseRelabel (φ : CNF V) :
    φ.denseRelabel.modelCount = φ.modelCount :=
  modelCount_dense_relabel φ

/-- Dense relabeling preserves the declared-variable model count on `Finset.range φ.numVars`. -/
theorem modelCountOn_denseRelabel (φ : CNF V) :
    φ.denseRelabel.modelCountOn (Finset.range φ.numVars) = φ.modelCount :=
  modelCountOn_dense_relabel φ

section PolyTime

variable {W : Type} [DecidableEq W]

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Dense relabeling is polynomial-time into unary variable indices for any variable encoding. -/
@[fun_prop]
theorem computableInPolyTime_denseRelabel_unary (enc : W ↪ List Bool) :
    ComputableInPolyTime (CNF.denseRelabel (V := W))
      (encList (encList (encPair enc encBool)))
      (encList (encList (encPair encUnary encBool))) := by
  have hd : ComputableTidilyInPolyTime (CNF.distinctVars (V := W))
      (encList (encList (encPair enc encBool))) (encList enc) :=
    (CNF.computableInPolyTime_distinctVars enc).tidy
  refine .of_tidy ?_
  unfold CNF.denseRelabel CNF.relabel Clause.relabel Prod.map
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Dense relabeling is polynomial-time into binary natural-number variable indices (`encCNF`) for
any variable encoding. -/
@[fun_prop]
theorem computableInPolyTime_denseRelabel (enc : W ↪ List Bool) :
    ComputableInPolyTime (CNF.denseRelabel (V := W))
      (encList (encList (encPair enc encBool)))
      Cslib.Complexity.encCNF := by
  have h1 : ComputableTidilyInPolyTime (CNF.denseRelabel (V := W))
      (encList (encList (encPair enc encBool)))
      (encList (encList (encPair encUnary encBool))) :=
    (computableInPolyTime_denseRelabel_unary enc).tidy
  have h2 : ComputableTidilyInPolyTime (CNF.relabel (id : ℕ → ℕ))
      (encList (encList (encPair encUnary encBool)))
      (encList (encList (encPair encNat encBool))) :=
    (CNF.computableInPolyTime_relabel (encV := encUnary) (encW := encNat)
      (.of_tidy unary_to_binary)).tidy
  have heq : (CNF.denseRelabel (V := W)) = fun φ => (CNF.denseRelabel φ).relabel id := by
    funext φ
    exact (CNF.relabel_id _).symm
  rw [heq]
  exact .of_tidy (h2.comp h1)

end PolyTime

end Cslib.Logic.PL.CNF

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Dense variable relabeling on `CNF ℕ` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_denseRelabel :
    ComputableInPolyTime (CNF.denseRelabel (V := ℕ)) encCNF encCNF :=
  CNF.computableInPolyTime_denseRelabel encNat

end Cslib.Complexity.SAT

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne.Compile

/-!
# Exact block indexing for positive clause replacements

The positive compiler numbers auxiliaries by the position of their signed source clause.
When signed clauses are themselves emitted in blocks, local drawings use local clause indices.
Shifting those indices by the preceding signed block lengths gives exactly the original
compiler's formula, including its variable names and clause order.

## Main definitions

* `PositiveExactOne.shift`: translate the signed-clause index of positive auxiliaries.
* `PositiveExactOne.formulaFrom`: the positive compiler starting at a supplied clause index.
* `PositiveExactOne.compileBlocks`: compile signed blocks with their actual global offsets.

## Main results

* `PositiveExactOne.formula_flatten`: exact global formula as separately compiled blocks.
* `PositiveExactOneCompile.rawFormula_eq_blocks`: partition by original source clauses.

## References

These are original indexing identities for the two local compilers.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PositiveExactOne

variable {V : Type*}

/-- Add the signed-clause offset to new positive auxiliaries, fixing source variables. -/
def shift (offset : ℕ) : Variable V → Variable V
  | .inl v => .inl v
  | .inr ((i, j), k) => .inr ((offset + i, j), k)

/-- Compile a signed formula whose first clause has the given global index. -/
def formulaFrom (start : ℕ) (φ : CNF V) : CNF (Variable V) :=
  φ.zipIdx start |>.flatMap fun c => clauseClauses c.2 c.1

/-- Shifting preserves the source role of every terminal and shifts each private slot. -/
theorem positiveLiteral_shift (offset i j : ℕ) (l : Literal V) :
    ((shift offset) (positiveLiteral i j l).1, (positiveLiteral i j l).2) =
      positiveLiteral (offset + i) j l := by
  cases l with
  | mk v b => cases b <;> rfl

/-- A complement block is equivariant under shifting its signed-clause index. -/
theorem complementBlock_shift (offset i j : ℕ) (l : Literal V) :
    (complementBlock i j l).relabel (shift offset) = complementBlock (offset + i) j l := by
  cases l with
  | mk v b => cases b <;> rfl

/-- The entire local clause replacement shifts to its actual global clause index. -/
theorem clauseClauses_shift (offset i : ℕ) (c : Clause V) :
    (clauseClauses i c).relabel (shift offset) = clauseClauses (offset + i) c := by
  simp only [clauseClauses, CNF.relabel, List.map_append, List.map_cons, List.map_nil,
    Clause.relabel, List.map_map, List.map_flatMap]
  apply congrArg₂ (· ++ ·)
  · apply congrArg (fun d => [d])
    apply List.map_congr_left
    intro l _
    exact positiveLiteral_shift _ _ _ _
  · simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro l _
    exact complementBlock_shift _ _ _ _

/-- The indexed list at a shifted starting position is the original list with shifted indices. -/
private theorem zipIdx_start {A : Type*} (xs : List A) (start offset : ℕ) :
    xs.zipIdx (offset + start) = (xs.zipIdx start).map fun c => (c.1, offset + c.2) := by
  induction xs generalizing start with
  | nil => rfl
  | cons a xs ih => simp [List.zipIdx_cons, ih, Nat.add_assoc]

/-- Starting a compiler at a nonzero index renames just its fresh auxiliaries. -/
theorem formulaFrom_eq_relabel (start : ℕ) (φ : CNF V) :
    formulaFrom start φ = (formula φ).relabel (shift start) := by
  unfold formulaFrom formula
  rw [show φ.zipIdx start = (φ.zipIdx 0).map (fun c => (c.1, start + c.2)) from
    by simpa only [Nat.add_zero] using zipIdx_start φ 0 start]
  simp only [CNF.relabel, List.flatMap_def, List.map_flatten, List.map_map,
    Function.comp_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro c _
  exact (clauseClauses_shift _ _ _).symm

/-- Compiling a concatenation gives the second part its exact signed-clause offset. -/
theorem formulaFrom_append (start : ℕ) (φ ψ : CNF V) :
    formulaFrom start (φ ++ ψ) = formulaFrom start φ ++ formulaFrom (start + φ.length) ψ := by
  simp only [formulaFrom, List.zipIdx_append, List.flatMap_append]

/-- Compile consecutive signed blocks with their true cumulative signed-clause offsets. -/
def compileBlocks (start : ℕ) : List (CNF V) → CNF (Variable V)
  | [] => []
  | b :: bs => (formula b).relabel (shift start) ++ compileBlocks (start + b.length) bs

/-- Number of signed clauses before one block. -/
def blockOffset (bs : List (CNF V)) (i : ℕ) : ℕ :=
  ((bs.take i).map List.length).sum

/-- The recursive partition is also an indexed concatenation with explicit prefix offsets. -/
theorem compileBlocks_eq_flatMap (start : ℕ) (bs : List (CNF V)) :
    compileBlocks start bs = bs.zipIdx.flatMap fun b =>
      (formula b.1).relabel (shift (start + blockOffset bs b.2)) := by
  induction bs generalizing start with
  | nil => rfl
  | cons b bs ih =>
    simp only [compileBlocks, List.zipIdx_cons, List.flatMap_cons]
    rw [ih]
    have he : bs.zipIdx 1 = (bs.zipIdx 0).map (fun c => (c.1, 1 + c.2)) :=
      zipIdx_start bs 0 1
    rw [he, List.flatMap_map]
    congr 1
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro c _
    simp [blockOffset, Nat.add_assoc, Nat.one_add]

/-- The blockwise compiler is exactly the indexed compiler on the flattened signed input. -/
theorem formulaFrom_flatten (start : ℕ) (bs : List (CNF V)) :
    formulaFrom start bs.flatten = compileBlocks start bs := by
  induction bs generalizing start with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatten_cons, formulaFrom_append, formulaFrom_eq_relabel, ih]
    rfl

/-- Exact formula and fresh-variable names for the block partition at index zero. -/
theorem formula_flatten (bs : List (CNF V)) :
    formula bs.flatten = compileBlocks 0 bs :=
  formulaFrom_flatten 0 bs

end Cslib.Logic.PL.CNF.PositiveExactOne

namespace Cslib.Logic.PL.CNF.PositiveExactOneCompile

variable {V : Type*}

/-- The actual positive formula is the concatenation of locally compiled source-clause
profiles, with outer auxiliaries shifted by signed-block lengths. -/
theorem rawFormula_eq_blocks (φ : CNF V) :
    rawFormula φ = PositiveExactOne.compileBlocks 0
      (φ.zipIdx.map fun c => FromSAT.clause c.2 c.1) := by
  exact PositiveExactOne.formula_flatten _

/-- The actual signed-clause offset of the replacement of original clause `i`. -/
def signedOffset (φ : CNF V) (i : ℕ) : ℕ :=
  PositiveExactOne.blockOffset (φ.zipIdx.map fun c => FromSAT.clause c.2 c.1) i

/-- Exact original-clause partition, in source order, with actual global auxiliary names. -/
theorem rawFormula_eq_flatMap (φ : CNF V) :
    rawFormula φ = φ.zipIdx.flatMap fun c =>
      (PositiveExactOne.formula (FromSAT.clause c.2 c.1)).relabel
        (PositiveExactOne.shift (signedOffset φ c.2)) := by
  rw [rawFormula_eq_blocks, PositiveExactOne.compileBlocks_eq_flatMap]
  simp only [List.zipIdx_map, List.flatMap_map, Nat.zero_add, signedOffset]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  have map_index (f : Clause V × ℕ → CNF (Variable V)) :
      (φ.zipIdx.map f) = (φ.zipIdx.zipIdx.map fun c => f c.1) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map f) (List.zipIdx_map_fst 0 φ.zipIdx).symm
  rw [map_index]
  apply List.map_congr_left
  intro ⟨⟨c, i⟩, j⟩ hc
  have hi := List.mem_zipIdx_iff_getElem?.mp hc
  obtain ⟨h, he⟩ := List.getElem?_eq_some_iff.mp hi
  have hij : i = j := by simpa using (congrArg Prod.snd he).symm
  simp only [Prod.map_fst, Prod.map_snd, id_eq, hij]

end Cslib.Logic.PL.CNF.PositiveExactOneCompile

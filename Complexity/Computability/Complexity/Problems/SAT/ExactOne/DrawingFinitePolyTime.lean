/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.Drawing
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding
public import Complexity.Logics.Propositional.CNF.ExactOne.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Pi

/-!
# Polynomial-time finite dispatch in the positive exact-one drawing compiler

The local profiles and ordered port assignments range over fixed finite types. Native finite
case analysis certifies their variable, clause, and route tables under binary coordinates.
Dynamic clause/literal indices remain unary counters. Source-role classification is a lookup
in a fixed finite option table, avoiding recursion through the structured raw variable type.

## Main definitions

* `encLocalIncidence`: unary local clause/variable indices and binary-coordinate routes.
* `profileRole`, `profileRoleTable`: finite source-slot or internal-variable classification.

## Main results

* `computableInPolyTime_clauseProfile`, `computableInPolyTime_directionSide`.
* `computableInPolyTime_variablePositions`, `computableInPolyTime_incidenceRoutes`.
* `computableInPolyTime_profileRole`: polynomial lookup with an unbounded unary index.
* `computableInPolyTime_clausePorts_of_literalSide`: compose dynamic source exit computation
  with the fixed finite collar completion.

## References

These are original computational certificates for the fixed drawing tables.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne.DrawingFinitePolyTime

open Cslib.Logic.PL Orthogonal Turing.MultiTapeTM

attribute [local fun_prop] ComputableInPolyTime.tidy

/-- The existing literal encoding, with binary natural variable labels. -/
abbrev encClause : Clause ℕ ↪ List Bool := encList (encPair encNat encBool)

/-- Native encoding of an input formula and its supplied binary-coordinate drawing. -/
abbrev encInput : CNF ℕ × Graph.OrthogonalDrawing ↪ List Bool :=
  encPair encCNF Graph.encOrthogonalDrawing

/-- Unary local incidence indices and a binary-coordinate route. -/
abbrev encLocalIncidence : LocalIncidence ↪ List Bool :=
  encPair encUnary (encPair encUnary encRoute)

/-- Encodings of the two fixed finite dispatch tags. -/
noncomputable abbrev encProfilePorts : ClauseProfile × PortAssignment ↪ List Bool :=
  encPair (encFinite ClauseProfile) (encFinite PortAssignment)

/-- Structured logical variables retain the source's binary natural encoding. -/
abbrev encRawVariable : CNF.PositiveExactOneCompile.Variable ℕ ↪ List Bool :=
  CNF.PositiveExactOneCompile.encVariable encNat

/-- Inspect at most three list constructors to obtain the clause's bounded length tag. -/
def boundedClauseLength (c : Clause ℕ) : Fin 4 :=
  if c.isEmpty then 0 else if c.tail.isEmpty then 1 else if c.tail.tail.isEmpty then 2 else 3

/-- The bounded length tag is exactly the first three source positions' presence count. -/
theorem boundedClauseLength_eq (c : Clause ℕ) :
    boundedClauseLength c = ⟨min c.length 3, by omega⟩ := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
  all_goals (apply Fin.ext; simp [boundedClauseLength])

/-- Native computation of the bounded presence tag examines three list heads. -/
@[fun_prop]
theorem computableInPolyTime_boundedClauseLength :
    ComputableInPolyTime boundedClauseLength encClause (encFinite (Fin 4)) := by
  refine .of_tidy ?_
  unfold boundedClauseLength encClause
  fun_prop

/-- The finite tag consisting of the bounded length and first three polarities. -/
def clauseTag (c : Clause ℕ) : Fin 4 × Bool × Bool × Bool :=
  (boundedClauseLength c, (c.getD 0 (0, true)).2,
    (c.getD 1 (0, true)).2, (c.getD 2 (0, true)).2)

private def profileOfTag (t : Fin 4 × Bool × Bool × Bool) : ClauseProfile :=
  clauseProfile ([(0, t.2.1), (1, t.2.2.1), (2, t.2.2.2)].take t.1.val)

private theorem clauseProfile_eq_tag (c : Clause ℕ) :
    clauseProfile c = profileOfTag (clauseTag c) := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩ <;> rfl

/-- Selecting the actual polarity profile is native polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_clauseProfile :
    ComputableInPolyTime clauseProfile encClause (encFinite ClauseProfile) := by
  let tagEncoding := encPair (encFinite (Fin 4)) (encPair encBool (encPair encBool encBool))
  have hget (i : ℕ) : ComputableTidilyInPolyTime
      (fun c : Clause ℕ => (c.getD i (0, true)).2) encClause encBool := by
    have hg := (ComputableTidilyInPolyTime.listGetD
      (encA := encPair encNat encBool) (encL := encClause) (0, true)).comp
      ((ComputableTidilyInPolyTime.id' (encIn := encClause)).prod
        (ComputableTidilyInPolyTime.const i))
    exact (ComputableTidilyInPolyTime.snd encNat encBool).comp hg
  have htag : ComputableTidilyInPolyTime clauseTag encClause tagEncoding :=
    computableInPolyTime_boundedClauseLength.tidy.prod ((hget 0).prod ((hget 1).prod (hget 2)))
  have hfinite : ComputableTidilyInPolyTime profileOfTag tagEncoding (encFinite ClauseProfile) :=
    .of_finite _
  have he : clauseProfile = profileOfTag ∘ clauseTag := funext clauseProfile_eq_tag
  rw [he]
  exact .of_tidy (hfinite.comp htag)

/-- A cardinal-vector classifier uses only three binary-coordinate equality tests. -/
@[fun_prop]
theorem computableInPolyTime_directionSide :
    ComputableInPolyTime directionSide encPoint (encFinite (Fin 4)) := by
  refine .of_tidy ?_
  unfold directionSide
  fun_prop

/-- Completing a partial source exit assignment is a fixed finite function. -/
@[fun_prop]
theorem computableInPolyTime_choosePorts :
    ComputableInPolyTime
      (fun p : Fin 4 × Fin 4 × Fin 4 × Fin 4 => choosePorts p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encFinite (Fin 4)) (encPair (encFinite (Fin 4))
        (encPair (encFinite (Fin 4)) (encFinite (Fin 4))))) (encFinite PortAssignment) :=
  .of_tidy (.of_finite _)

/-- A fixed profile/port pair computes its placed local variable-position list. -/
@[fun_prop]
theorem computableInPolyTime_variablePositions :
    ComputableInPolyTime (fun p : ClauseProfile × PortAssignment =>
      (collaredPrefixGeometry (profilePrefixGeometry p.1) p.2).variablePositions)
      encProfilePorts encRoute := .of_tidy (.of_finite _)

/-- A fixed profile/port pair computes its placed local clause-position list. -/
@[fun_prop]
theorem computableInPolyTime_clausePositions :
    ComputableInPolyTime (fun p : ClauseProfile × PortAssignment =>
      (collaredPrefixGeometry (profilePrefixGeometry p.1) p.2).clausePositions)
      encProfilePorts encRoute := .of_tidy (.of_finite _)

/-- A fixed profile/port pair computes its actual local incidence routes and indices. -/
@[fun_prop]
theorem computableInPolyTime_incidenceRoutes :
    ComputableInPolyTime (fun p : ClauseProfile × PortAssignment =>
      (collaredPrefixGeometry (profilePrefixGeometry p.1) p.2).incidenceRoutes)
      encProfilePorts (encList encLocalIncidence) := .of_tidy (.of_finite _)

/-- The source-variable list of a profile is a fixed finite lookup. -/
@[fun_prop]
theorem computableInPolyTime_profileVariables :
    ComputableInPolyTime profileVariables (encFinite ClauseProfile) (encList encRawVariable) :=
  .of_tidy (.of_finite _)

/-- The exact logical formula of a profile is a fixed finite lookup. -/
@[fun_prop]
theorem computableInPolyTime_profileFormula :
    ComputableInPolyTime profileFormula (encFinite ClauseProfile)
      (encList (encList (encPair encRawVariable encBool))) := .of_tidy (.of_finite _)

/-- Classify a fixed profile variable, normalizing its source position to the three finite slots.
-/
def variableRole (v : CNF.PositiveExactOneCompile.Variable ℕ) : Option (Fin 3) :=
  match v with
  | .inl (.inl j) => some ⟨j % 3, Nat.mod_lt _ (by decide)⟩
  | _ => none

/-- Source slot or internal-variable role of an indexed profile variable. Invalid indices
follow the actual drawing compiler's default source slot zero. -/
def profileRole (p : ClauseProfile) (n : ℕ) : Option (Fin 3) :=
  variableRole ((profileVariables p).getD n (.inl (.inl 0)))

/-- A fixed finite table of source-slot roles for the variables of each profile. -/
def profileRoleTable (p : ClauseProfile) : List (Option (Fin 3)) :=
  (profileVariables p).map variableRole

/-- The native role lookup agrees with the actual raw-variable classifier. -/
theorem profileRole_eq_getD (p : ClauseProfile) (n : ℕ) :
    profileRole p n = (profileRoleTable p).getD n (some 0) := by
  unfold profileRole profileRoleTable
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (profileVariables p)[n]? <;> rfl

/-- Every source-placeholder name occurring in a fixed profile is one of its three slots. -/
theorem profileVariables_source_bound : ∀ p : ClauseProfile, ∀ v ∈ profileVariables p,
    (match v with | .inl (.inl j) => j < 3 | _ => True) := by
  have hall : ∀ p : ClauseProfile, (profileVariables p).all
      (fun v => match v with | .inl (.inl j) => decide (j < 3) | _ => true) = true := by
    decide +kernel
  intro p v hv
  have hh := List.all_eq_true.mp (hall p) v hv
  rcases v with (j | k) | k
  · exact of_decide_eq_true hh
  · trivial
  · trivial

private theorem profileVariable_getD_source_bound (p : ClauseProfile) (n : ℕ) :
    (match (profileVariables p).getD n (.inl (.inl 0)) with
      | .inl (.inl j) => j < 3 | _ => True) := by
  by_cases hn : n < (profileVariables p).length
  · rw [List.getD_eq_getElem _ _ hn]
    exact profileVariables_source_bound p _ (List.getElem_mem hn)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    change (0 : ℕ) < 3
    decide

/-- The finite role tag recovers the exact natural source index used by the drawing compiler.
-/
theorem profileRole_map_val (p : ClauseProfile) (n : ℕ) :
    (profileRole p n).map Fin.val =
      (match (profileVariables p).getD n (.inl (.inl 0)) with
        | .inl (.inl j) => some j | _ => none) := by
  have hb := profileVariable_getD_source_bound p n
  unfold profileRole variableRole
  generalize he : (profileVariables p).getD n (.inl (.inl 0)) = v at hb ⊢
  cases v with
  | inl v =>
    cases v with
    | inl j => simpa only [Option.map_some] using congrArg some (Nat.mod_eq_of_lt hb)
    | inr v => rfl
  | inr v => rfl

/-- The finite role table can be emitted in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_profileRoleTable :
    ComputableInPolyTime profileRoleTable (encFinite ClauseProfile)
      (encList (encFinite (Option (Fin 3)))) := .of_tidy (.of_finite _)

/-- A role table lookup accepts any unary index, with no promise that it lies in the table. -/
@[fun_prop]
theorem computableInPolyTime_profileRole :
    ComputableInPolyTime (fun p : ClauseProfile × ℕ => profileRole p.1 p.2)
      (encPair (encFinite ClauseProfile) encUnary) (encFinite (Option (Fin 3))) := by
  have ht := computableInPolyTime_profileRoleTable.tidy.comp
    (ComputableTidilyInPolyTime.fst (encFinite ClauseProfile) encUnary)
  have hg := (ComputableTidilyInPolyTime.listGetD
    (encA := encFinite (Option (Fin 3))) (encL := encList (encFinite (Option (Fin 3))))
    (some 0)).comp (ht.prod (ComputableTidilyInPolyTime.snd (encFinite ClauseProfile) encUnary))
  refine .of_tidy ?_
  simpa only [Function.comp_def, profileRole_eq_getD] using hg

/-- Native computation of the selected collar follows from the three native source exits.
The dynamic geometric computation is supplied by the caller, independently of finite dispatch.
-/
theorem computableInPolyTime_clausePorts_of_literalSide
    (hside : ∀ j : ℕ, ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => literalSide p.1.1 p.1.2 p.2 j)
      (encPair encInput encUnary) (encFinite (Fin 4))) :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => clausePorts p.1.1 p.1.2 p.2)
      (encPair encInput encUnary) (encFinite PortAssignment) := by
  have hc : ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => p.1.1.getD p.2 [])
      (encPair encInput encUnary) encClause := by
    unfold encInput encCNF encClause
    fun_prop
  have hn := computableInPolyTime_boundedClauseLength.tidy.comp hc
  have ht := hn.prod ((hside 0).tidy.prod ((hside 1).tidy.prod (hside 2).tidy))
  have h := computableInPolyTime_choosePorts.tidy.comp ht
  refine .of_tidy ?_
  simpa only [Function.comp_def, clausePorts, boundedClauseLength_eq] using h

end Cslib.Complexity.SAT.ExactOne.DrawingFinitePolyTime

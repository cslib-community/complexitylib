/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import Complexity.Computability.PolyTime.CSP.CyclicDifference.Size
import Mathlib.Data.Fin.VecNotation
import Lean.Util.CollectAxioms

/-!
# Complete cyclic-difference compiler regressions

Kernel computations execute the actual compiler. Supplied rotations include long white faces,
repeated arguments/records, disconnected components, nullaries, huge binary names and malformed
indices. Semantic clients apply the combined theorem to both satisfiable and unsatisfiable inputs.
-/

open Cslib Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table Cslib.BitString
open Cslib.Complexity Cslib.Complexity.CSP Cslib.Complexity.CSP.CyclicCompiler
open Graph.RotationCertificate Turing.MultiTapeTM

namespace CSPCyclicCompilerTests

private def fullArity (_ : Unit) : ℕ := 5
private def fullSem (_ : Unit) (_ : List Bool) : Bool := true
private theorem fullSelf (r : Unit) : IsSelfComplementary (booleanRelation fullArity fullSem r) :=
  fun _ => Iff.rfl
private theorem fullDifferenceDelta (n : ℕ) :
    IsEvenDeltaMatroid (cyclicDifferenceRelation (Set.univ : Set (Fin n → Bool))) := by
  have he : cyclicDifferenceRelation (Set.univ : Set (Fin n → Bool)) =
      {d : Fin n → Bool | parityOn Finset.univ d = false} := by
    ext d
    change (∃ x : Fin n → Bool, True ∧ cyclicDifference x = d) ↔
      parityOn Finset.univ d = false
    simpa only [true_and] using exists_cyclicDifference_eq_iff d
  rw [he]
  apply isEvenDeltaMatroid_parityOn_fiber
  exact ⟨fun _ => false, by
    rw [parityOn_eq_sum]
    change (∑ _ : Fin n, (0 : Bool)) = 0
    exact Finset.sum_const_zero⟩
private theorem fullDelta (r : Unit) :
    IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation fullArity fullSem r)) := by
  have he : booleanRelation fullArity fullSem r = Set.univ := by
    ext; simp [booleanRelation, fullSem]
  rw [he]
  exact fullDifferenceDelta _

private abbrev longInput : CSP Unit ℕ := [((), [2 ^ 250, 9, 2 ^ 100, 31, 0])]
private abbrev longCert : Graph.RotationCertificate := ⟨[0, 3, 2, 5, 4, 7, 6, 9, 8, 1]⟩
private abbrev longOutput := compile fullArity fullSem (longInput, longCert)

example : verifyRotationCertificate longInput longCert = true := by decide
example : (whiteScopes longInput longCert) = [[0, 1, 2, 3, 4]] := by decide
example : longOutput.map (fun c => c.2) =
    [[0, 1, 2, 3, 4], [0, 1, 5], [5, 2, 6], [6, 3, 4]] := by decide
example : longOutput.map (fun c => (c.1.arity, c.1.rows.length)) =
    [(5, 32), (3, 4), (3, 4), (3, 4)] := by decide
example : longOutput.vars.toFinset = Finset.range 7 := by decide
example : longOutput.vars.length = 14 := by decide
example : longOutput.eval Table.sem (fun _ => false) = true := by decide
example : EdgeInstance longOutput := by unfold EdgeInstance; decide
example : WellFormed Table.arity longOutput := by decide
example : EdgeInstance.EvenConstraints Table.sem longOutput :=
  (compile_correct fullArity fullSem fullSelf (fun r _ => fullDelta r)
    (longInput, longCert)).2.2.1
example : longOutput.Satisfiable Table.sem := by
  exact (compile_correct fullArity fullSem fullSelf (fun r _ => fullDelta r)
    (longInput, longCert)).2.2.2.mp ⟨by decide, by decide, fun _ => true, by decide⟩

-- No exponential white-face table: twelve ports use ten EVEN3 constraints and nine auxiliaries.
example : (parityChain 12 (List.range 12)).length = 10 := by decide
example : (parityChain 12 (List.range 12)).vars.toFinset = Finset.range 21 := by decide
example : (parityChain 12 (List.range 12)).all (fun c => decide (c.1.rows.length = 4)) = true := by
  decide
example : (parityChain 4 [0, 1, 2, 3]).eval Table.sem
    (fun n => decide (n = 0 ∨ n = 3 ∨ n = 4)) = true := by decide
example : ¬ ∃ σ : ℕ → Bool, (∀ v < 4, σ v = decide (v = 0)) ∧
    (parityChain 4 [0, 1, 2, 3]).eval Table.sem σ = true := by
  rintro ⟨σ, hs, he⟩
  have hp := parityChain_sound 4 [0, 1, 2, 3] σ he
  simp only [List.map_cons, List.map_nil, hs 0 (by decide), hs 1 (by decide),
    hs 2 (by decide), hs 3 (by decide)] at hp
  contradiction

-- Raw invalid guards execute the fixed nonempty even-delta-matroid rejection gadget.
example : compile fullArity fullSem ([((), [2 ^ 250])], ⟨[0, 1]⟩) = rejectEdge := by decide
example : compile fullArity fullSem (longInput, ⟨[0, 3, 2, 5, 4, 7, 6, 9, 8, 2 ^ 250]⟩) =
    rejectEdge := by decide
example : compile fullArity fullSem (longInput, ⟨[]⟩) = rejectEdge := by decide
example : EdgeInstance (compile fullArity fullSem ([], ⟨[2 ^ 250]⟩)) := by
  unfold EdgeInstance
  decide
example : ¬ (compile fullArity fullSem (longInput, ⟨[]⟩)).Satisfiable Table.sem := by
  rw [show compile fullArity fullSem (longInput, ⟨[]⟩) = rejectEdge by decide]
  exact not_satisfiable_rejectEdge

-- Both nullary truth values, empty body and empty alphabet are actual program cases.
example : compile (fun _ : Bool => 0) (fun b _ => b) ([(true, []), (true, [])], ⟨[]⟩) = [] := by
  decide
example : compile (fun _ : Bool => 0) (fun b _ => b) ([(true, []), (false, [])], ⟨[]⟩) =
    rejectEdge := by decide
example : compile (fun _ : Unit => 1) (fun _ _ => false) ([((), [2 ^ 100])], ⟨[0, 1]⟩) =
    rejectEdge := by decide
example : compile fullArity fullSem ([], ⟨[]⟩) = [] := by decide
example : compile (fun e : Empty => nomatch e) (fun e _ => nomatch e) ([], ⟨[]⟩) = [] := by
  decide

-- True nullaries interleaved with identical unary records preserve the supplied original indices.
private def mixedArity (b : Bool) : ℕ := if b then 0 else 1
private def mixedSem (_ : Bool) (_ : List Bool) : Bool := true
private theorem mixedSelf (b : Bool) :
    IsSelfComplementary (booleanRelation mixedArity mixedSem b) := fun _ => Iff.rfl
private theorem mixedDelta (b : Bool) :
    IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation mixedArity mixedSem b)) := by
  have he : booleanRelation mixedArity mixedSem b = Set.univ := by
    ext; simp [booleanRelation, mixedSem]
  rw [he]
  exact fullDifferenceDelta _

private abbrev mixedInput : CSP Bool ℕ :=
  [(true, []), (false, [2 ^ 100]), (true, []), (false, [2 ^ 100])]
private abbrev mixedCert : Graph.RotationCertificate := ⟨[2, 1, 0, 3]⟩
private abbrev mixedOutput := compile mixedArity mixedSem (mixedInput, mixedCert)
example : verifyRotationCertificate mixedInput mixedCert = true := by decide
example : mixedOutput.map Prod.snd = [[0], [1], [0, 1]] := by decide
example : EdgeInstance mixedOutput := by unfold EdgeInstance; decide
example : mixedOutput.eval Table.sem (fun _ => false) = true := by decide
example : EdgeInstance.EvenConstraints Table.sem mixedOutput :=
  (compile_correct mixedArity mixedSem mixedSelf (fun b _ => mixedDelta b)
    (mixedInput, mixedCert)).2.2.1
example : (compile (fun _ : Unit => 1) (fun _ _ => true)
    ([((), [7]), ((), [2 ^ 100])], ⟨[0, 1, 2, 3]⟩)).map Prod.snd =
      [[0], [1], [0], [1]] := by decide

-- Ternary NAE is a nontrivial self-complementary difference-even-delta-matroid language.
private def naeArity (_ : Unit) : ℕ := 3
private def naeSem (_ : Unit) (row : List Bool) : Bool := row.any id && !row.all id
private theorem naeSelf (r : Unit) : IsSelfComplementary (booleanRelation naeArity naeSem r) := by
  unfold IsSelfComplementary booleanRelation naeArity naeSem
  decide
private theorem naeDelta (r : Unit) :
    IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation naeArity naeSem r)) := by
  cases r
  rw [← booleanRelation_differenceTable]
  unfold booleanRelation
  constructor
  · constructor
    · exact ⟨![true, true, false], by decide⟩
    · decide
  · decide
private abbrev naeInput : CSP Unit ℕ := [((), [0, 1, 2])]
private abbrev naeCert : Graph.RotationCertificate := ⟨[0, 3, 2, 5, 4, 1]⟩
private abbrev naeRepeated : CSP Unit ℕ := [((), [7, 7, 7])]
private abbrev naeRepeatedCert : Graph.RotationCertificate := ⟨[4, 3, 0, 5, 2, 1]⟩
example : (compile naeArity naeSem (naeInput, naeCert)).eval Table.sem
    (fun n => decide (n ≠ 2)) = true := by decide
example : (compile naeArity naeSem (naeRepeated, naeRepeatedCert)).map Prod.snd =
    [[0, 1, 2], [0], [1], [2]] := by decide
example : EdgeInstance.EvenConstraints Table.sem (compile naeArity naeSem
    (naeRepeated, naeRepeatedCert)) :=
  (compile_correct naeArity naeSem naeSelf (fun r _ => naeDelta r)
    (naeRepeated, naeRepeatedCert)).2.2.1
example : ¬ (compile naeArity naeSem (naeRepeated, naeRepeatedCert)).Satisfiable Table.sem := by
  rw [satisfiable_compile_iff naeArity naeSem naeSelf]
  rintro ⟨_, _, σ, hσ⟩
  cases h : σ 7 <;> simp [naeRepeated, CSP.eval, Constraint.eval, naeSem, h] at hσ

-- The original cyclic order is checked: the mirrored certificate rejects even at genus zero.
example : compile naeArity naeSem (naeInput, ⟨[0, 5, 2, 1, 4, 3]⟩) = rejectEdge := by decide

-- A correctly ordered toroidal rotation fails the numerical input guard.
example : compile naeArity naeSem
    ([((), [0, 1, 2]), ((), [0, 1, 2])],
      ⟨[6, 3, 8, 5, 10, 1, 0, 9, 2, 11, 4, 7]⟩) = rejectEdge := by decide

-- A real native client under the original encodings, with no machine/runtime premise supplied.
example : ComputableInPolyTime (compile naeArity naeSem)
    (encCSPRotationCertificate encUnit encNat) (encCSP encTable encNat) :=
  (compile_spec encUnit naeArity naeSem naeSelf (fun r _ => naeDelta r)).1

-- Empty symbols are allowed by the static criterion and are rejected only when they occur.
private def nullaryArity (_ : Bool) : ℕ := 0
private def nullarySem (b : Bool) (_ : List Bool) : Bool := b
private theorem nullarySelf (b : Bool) :
    IsSelfComplementary (booleanRelation nullaryArity nullarySem b) := fun _ => Iff.rfl
private theorem nullaryDelta (b : Bool)
    (hne : (booleanRelation nullaryArity nullarySem b).Nonempty) :
    IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation nullaryArity nullarySem b)) := by
  cases b
  · obtain ⟨x, hx⟩ := hne
    contradiction
  · rw [← booleanRelation_differenceTable]
    unfold booleanRelation
    constructor
    · constructor
      · exact ⟨fun _ => false, by decide⟩
      · decide
    · decide
example : EdgeInstance.EvenConstraints Table.sem
    (compile nullaryArity nullarySem ([(false, [])], ⟨[]⟩)) :=
  (compile_correct nullaryArity nullarySem nullarySelf nullaryDelta ([(false, [])], ⟨[]⟩)).2.2.1
example : (compile nullaryArity nullarySem ([(true, [])], ⟨[]⟩)).Satisfiable Table.sem := by
  apply (compile_correct nullaryArity nullarySem nullarySelf nullaryDelta
    ([(true, [])], ⟨[]⟩)).2.2.2.mp
  exact ⟨by decide, by decide, fun _ => false, by decide⟩

end CSPCyclicCompilerTests


-- Audit all stored declarations of the new modules, plus the narrowly promoted helper modules.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : List Name := [
    `Complexity.Computability.PolyTime.CSP.CyclicDifference,
    `Complexity.Foundations.Data.BitString.ListParity,
    `Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Nullary,
    `Complexity.Logics.Propositional.CSP.Table.ParityChain,
    `Complexity.Logics.Propositional.CSP.Table.CyclicDifference,
    `Complexity.Logics.Propositional.CSP.Occurrence.Count,
    `Complexity.Computability.PolyTime.Graph.RotationSystem,
    `Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if roots.any (·.isPrefixOf moduleName) then
      for name in data.constNames do
        count := count + 1
        let axioms ← collectAxioms name
        let bad := axioms.filter fun ax => !allowed.contains ax
        unless bad.isEmpty do
          throwError "cyclic compiler axiom audit: {name} depends on {bad}"
  unless count > 0 do
    throwError "cyclic compiler axiom audit found no declarations"

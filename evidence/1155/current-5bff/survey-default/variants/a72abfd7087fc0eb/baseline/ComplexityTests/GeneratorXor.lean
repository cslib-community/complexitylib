/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Combined
import Complexity.Tactic.PPT

/-!
XOR combination with captured programs, arbitrary encodings and complete output distributions.
-/

namespace ComplexityTests.GeneratorXor

open Cslib Cslib.BitString Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

-- Width is independent of row lengths; absent bits contribute false.
example : listXor 4 [[true, false], [true, true, true], []] =
    [false, true, true, false] := by decide

example : listXor 3 [] = [false, false, false] := by decide

example : listXor 0 [[true], [false, true]] = [] := by decide

example : ComputableTidilyInPolyTime (fun p : ℕ × List (List Bool) =>
    listXor (p.1 + 1) (p.2.reverse ++ [[true]]))
    (encPair encUnary (encList encBits)) encBits := by fun_prop

-- The same collection program accepts rows represented as framed Boolean lists.
example : ComputableTidilyInPolyTime (fun p : ℕ × List (List Bool) =>
    listXor (p.1 + 1) (p.2.map fun row => row.reverse))
    (encPair encUnary (encList (encList encBool))) encBits := by polytime

private def candidate (index : ℕ) (seed : List Bool) : List Bool :=
  seed ++ [decide (index = 0)]

example : GeneratorXor.generate 2 2 3 candidate [true, false, false, true] =
    [true, true, true] := by decide

example : GeneratorXor.generate 2 2 3 candidate [] = [false, false, true] := by decide

example : GeneratorXor.generate 0 2 3 candidate [true, false] =
    [false, false, false] := by decide

example : GeneratorXor.generate 2 0 2 candidate [] = [true, false] := by decide

example : GeneratorXor.generate 2 2 0 candidate [true] = [] := by decide

example (generator : ℕ → ℕ → List Bool → List Bool)
    (hgenerator : ComputableTidilyInPolyTime (fun p => generator p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encBits) encBits) :
    ComputableTidilyInPolyTime (fun p : ℕ × List Bool =>
      GeneratorXor.generate (p.1 + 1) (p.1 + 2) (p.1 + 3) (generator p.1) p.2.reverse)
      (encPair encUnary encBits) encBits := by
  fail_if_success (clear hgenerator; polytime)
  polytime

-- Expanded ordinary collection code has the same certificate as the named combiner.
example : ComputableTidilyInPolyTime (fun p : ℕ × List Bool =>
    listXor (p.1 + 3) ((List.range (p.1 + 1)).map fun i =>
      listRow (p.1 + 2) i p.2 ++ [decide (i = 0)]))
    (encPair encUnary encBits) encBits := by fun_prop

example (generator : ℕ → ℕ → List Bool → List Bool)
    (adversary : ℕ → List Bool → ProbComp Bool)
    (hgenerator : ComputableTidilyInPolyTime (fun p => generator p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encBits) encBits)
    (hadversary : IsPPTOn (encPair encUnary encBits) encBool
      (fun p => adversary p.1 p.2)) :
    IsPPTOn (encPair encUnary encBits) encBool (fun p : ℕ × List Bool =>
      GeneratorXor.test (p.1 + 1) (p.1 + 2) (p.1 + 3) (generator p.1) p.1
        (adversary p.1) p.2.reverse) := by
  fail_if_success (clear hgenerator; ppt)
  fail_if_success (clear hadversary; ppt)
  ppt

-- Framed challenges and nested preparation still use the public certificate.
example (adversary : ℕ → List Bool → ProbComp Bool)
    (hadversary : IsPPTOn (encPair encUnary encBits) encBool
      (fun p => adversary p.1 p.2)) :
    IsPPTOn (encPair encUnary (encList encBool)) encBool (fun p : ℕ × List Bool =>
      GeneratorXor.test (p.1 + 1) 2 3 (fun i seed => seed ++ [decide (i = p.1)]) 0
        (adversary p.1) (p.2.reverse ++ [false])) := by ppt

-- The endpoint candidate's independent seed is replaced without changing the complete output law.
example : ((uniformList 2).map (candidate 1)).bind (fun challenge =>
    (uniformList 4).map (GeneratorXor.generate 2 2 3
      (fun i seed => if i = 1 then challenge else candidate i seed))) =
    (uniformList 4).map (GeneratorXor.generate 2 2 3 candidate) :=
  GeneratorXor.real_distribution 2 2 3 candidate ⟨1, by decide⟩

-- Uniformity places no efficiency or quality requirement on the other candidate.
example (other : List Bool → List Bool) :
    (uniformList 3).bind (fun challenge =>
      (uniformList 4).map (GeneratorXor.generate 2 2 3
        (fun i seed => if i = 0 then challenge else other seed))) = uniformList 3 :=
  GeneratorXor.ideal_distribution 2 2 3 (fun _ => other) ⟨0, by decide⟩

example (adversary : List Bool → ProbComp Bool) :
    Game.advantage
      (((uniformList 4).map (GeneratorXor.generate 2 2 3 candidate)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformList 3).bind (fun word => ProbComp.eval (adversary word))) =
    Game.advantage
      (((uniformList 2).map (candidate 1)).bind
        (fun word => ProbComp.eval (GeneratorXor.test 2 2 3 candidate 1 adversary word)))
      ((uniformList 3).bind
        (fun word => ProbComp.eval (GeneratorXor.test 2 2 3 candidate 1 adversary word))) :=
  GeneratorXor.advantage_eq 2 2 3 candidate ⟨1, by decide⟩ adversary

end ComplexityTests.GeneratorXor

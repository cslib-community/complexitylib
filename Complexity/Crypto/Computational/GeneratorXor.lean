/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Probability.BitString.List
public import Complexity.Languages.Probabilistic.BitString
public import Complexity.Crypto.Computational.Basic
import Complexity.Probability.Product
import Complexity.Probability.Uniform
import Complexity.Tactic.PPT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# XOR combination of independently seeded generators

Split a uniform tape into equal seed blocks, evaluate every indexed generator, and XOR their
outputs. A reduction simulates all but one candidate. Replacing that candidate's output by
uniform bits makes the combined output uniform, with no assumption on the other candidates.

## Main definitions

* `generate`: evaluate an indexed family on independent seed blocks and XOR its outputs.
* `test`: the randomized reduction that inserts one supplied candidate output.

## Main results

* `isPolyTime_generate`, `isPPTOn_test`: uniform certificates with captured programs.
* `real_distribution`, `ideal_distribution`: exact laws of the complete combined output.
* `advantage_eq`, `indistinguishable`: one secure indexed candidate secures the combination.

## References

This is the combination step in Thomas Holenstein, *Pseudorandom Generators from One-Way
Functions: A Simple Construction for Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1,
[Holenstein2006].

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.GeneratorXor

open Probability BitString Turing.MultiTapeTM

/-- Evaluate every candidate on its own seed block and XOR the outputs at the declared width. -/
def generate (count seedBits outputBits : ℕ) (generator : ℕ → List Bool → List Bool)
    (seed : List Bool) : List Bool :=
  listXor outputBits ((List.range count).map fun i => generator i (listRow seedBits i seed))

/-- The output width is fixed, including on short or malformed input tapes. -/
@[simp] theorem length_generate (count seedBits outputBits : ℕ)
    (generator : ℕ → List Bool → List Bool) (seed : List Bool) :
    (generate count seedBits outputBits generator seed).length = outputBits := by
  simp only [generate, length_listXor]

/-- Combining polynomially many uniformly efficient candidates uses ordinary collection code. -/
theorem isPolyTime_generate {α : Type} {input : α ↪ List Bool}
    {count seedBits outputBits : α → ℕ} {generator : α → ℕ → List Bool → List Bool}
    {seed : α → List Bool}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hseedBits : ComputableTidilyInPolyTime seedBits input encUnary)
    (houtputBits : ComputableTidilyInPolyTime outputBits input encUnary)
    (hgenerator : ComputableTidilyInPolyTime (fun pair => generator pair.1.1 pair.1.2 pair.2)
      (encPair (encPair input encUnary) encBits) encBits)
    (hseed : ComputableTidilyInPolyTime seed input encBits) :
    ComputableTidilyInPolyTime (fun a =>
      generate (count a) (seedBits a) (outputBits a) (generator a) (seed a)) input encBits := by
  unfold generate
  apply ComputableTidilyInPolyTime.bitsXorWithInput houtputBits
  apply ComputableTidilyInPolyTime.mapWithInput (encA := encUnary) (by fun_prop)
  exact hgenerator.comp (g := fun p : α × ℕ =>
    ((p.1, p.2), listRow (seedBits p.1) p.2 (seed p.1))) (by fun_prop)

attribute [program_certificate] isPolyTime_generate

/-- The executable combiner is the finite sum of its candidates' bitstring outputs. -/
theorem generate_eq_sum (count seedBits outputBits : ℕ) (generator : ℕ → List Bool → List Bool)
    (seed : List Bool) :
    generate count seedBits outputBits generator seed =
      List.ofFn (∑ i : Fin count,
        ofList outputBits
          (generator i.val (List.ofFn (block (ofList (count * seedBits) seed) i)))) := by
  have hrows : (List.range count).map (fun i => generator i (listRow seedBits i seed)) =
      List.ofFn (fun i : Fin count =>
        generator i.val (List.ofFn (block (ofList (count * seedBits) seed) i))) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      congrArg (generator i) (listRow_eq_ofFn seedBits ⟨i, by simpa using hi'⟩ seed)
  rw [generate, hrows, listXor_eq_ofFn_sum]

/-- Uniform seed blocks are independent; the combiner's law is a sum over their finite tuple. -/
theorem generate_distribution (count seedBits outputBits : ℕ)
    (generator : ℕ → List Bool → List Bool) :
    (uniformList (count * seedBits)).map (generate count seedBits outputBits generator) =
      (PMF.uniformOfFintype (Fin count → BitString seedBits)).map
        (fun seeds => List.ofFn (∑ i : Fin count,
          ofList outputBits (generator i.val (List.ofFn (seeds i))))) := by
  rw [← uniformList_blocks count seedBits, PMF.map_comp]
  congr 1
  funext seed
  exact generate_eq_sum ..

/-- A real challenge can replace the chosen candidate's output because its seed is independent
of every other seed block. The simulator may sample and discard the unused chosen block. -/
theorem real_distribution (count seedBits outputBits : ℕ) (generator : ℕ → List Bool → List Bool)
    (i : Fin count) :
    (do
      let challenge ← (uniformList seedBits).map (generator i.val)
      (uniformList (count * seedBits)).map (generate count seedBits outputBits
        (fun j seed => if j = i.val then challenge else generator j seed))) =
      (uniformList (count * seedBits)).map (generate count seedBits outputBits generator) := by
  simp_rw [generate_distribution]
  simp only [uniformList, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
  let evaluate := fun seeds : Fin count → BitString seedBits =>
    List.ofFn (∑ j : Fin count, ofList outputBits (generator j.val (List.ofFn (seeds j))))
  have h := congrArg (PMF.map evaluate)
    (PMF.uniformOfFintype_update (γ := BitString seedBits) i)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  refine Eq.trans ?_ h
  congr 1
  funext fresh
  congr 1
  funext seeds
  apply congrArg List.ofFn
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp
  · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [hji, hval]

/-- One uniform candidate masks the complete XOR, for every fixed choice of the other outputs. -/
theorem ideal_distribution (count seedBits outputBits : ℕ) (generator : ℕ → List Bool → List Bool)
    (i : Fin count) :
    (do
      let challenge ← uniformList outputBits
      (uniformList (count * seedBits)).map (generate count seedBits outputBits
        (fun j seed => if j = i.val then challenge else generator j seed))) =
      uniformList outputBits := by
  simp_rw [generate_distribution]
  simp only [uniformList, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
  simp only [PMF.map]
  rw [PMF.bind_comm]
  calc
    _ = (PMF.uniformOfFintype (Fin count → BitString seedBits)).bind
        (fun _ => (PMF.uniformOfFintype (BitString outputBits)).map List.ofFn) := by
      congr 1
      funext seeds
      have h := congrArg (PMF.map List.ofFn) (PMF.uniformOfFintype_map_sum_update
        (fun j : Fin count => ofList outputBits (generator j.val (List.ofFn (seeds j)))) i)
      simp only [PMF.map_comp, Function.comp_def] at h
      refine Eq.trans ?_ h
      congr 1
      funext challenge
      apply congrArg (PMF.pure ∘ List.ofFn)
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
        simp [hji, hval]
    _ = _ := PMF.bind_const _ _

/-- Simulate every other candidate and insert the supplied challenge at the chosen index. -/
noncomputable def test (count seedBits outputBits : ℕ) (generator : ℕ → List Bool → List Bool)
    (index : ℕ) (adversary : List Bool → ProbComp Bool) (challenge : List Bool) :
    ProbComp Bool := do
  let seed ← BitString.sampleList (count * seedBits)
  adversary (generate count seedBits outputBits
    (fun j coins => if j = index then challenge else generator j coins) seed)

/-- The reduction is a uniform program that captures its index and its distinguisher. -/
@[program_certificate]
theorem isPPTOn_test {α : Type} {input : α ↪ List Bool}
    {count seedBits outputBits index : α → ℕ} {generator : α → ℕ → List Bool → List Bool}
    {adversary : α → List Bool → ProbComp Bool} {challenge : α → List Bool}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hseedBits : ComputableTidilyInPolyTime seedBits input encUnary)
    (houtputBits : ComputableTidilyInPolyTime outputBits input encUnary)
    (hindex : ComputableTidilyInPolyTime index input encUnary)
    (hgenerator : ComputableTidilyInPolyTime (fun pair => generator pair.1.1 pair.1.2 pair.2)
      (encPair (encPair input encUnary) encBits) encBits)
    (hadversary : IsPPTOn (encPair input encBits) encBool
      (fun pair => adversary pair.1 pair.2))
    (hchallenge : ComputableTidilyInPolyTime challenge input encBits) :
    IsPPTOn input encBool (fun a =>
      test (count a) (seedBits a) (outputBits a) (generator a) (index a)
        (adversary a) (challenge a)) := by
  unfold test
  apply IsPPTOn.bind_with (left := encBits) (by fun_prop)
  apply hadversary.preprocess (prepare := fun p : α × List Bool =>
    (p.1, generate (count p.1) (seedBits p.1) (outputBits p.1)
      (fun j coins => if j = index p.1 then challenge p.1 else generator p.1 j coins) p.2))
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.prod (by fun_prop)
  apply isPolyTime_generate (by fun_prop) (by fun_prop) (by fun_prop) ?_ (by fun_prop)
  have hgen := hgenerator.comp
    (encIn := encPair (encPair (encPair input encBits) encUnary) encBits)
    (g := fun p : ((α × List Bool) × ℕ) × List Bool => ((p.1.1.1, p.1.2), p.2))
    (by fun_prop)
  exact ComputableTidilyInPolyTime.ite_decide (by fun_prop) (by fun_prop) hgen

/-- XOR combination loses no distinguishing advantage when reducing to a valid candidate. -/
theorem advantage_eq (count seedBits outputBits : ℕ) (generator : ℕ → List Bool → List Bool)
    (i : Fin count) (adversary : List Bool → ProbComp Bool) :
    Game.advantage
      (((uniformList (count * seedBits)).map (generate count seedBits outputBits generator)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformList outputBits).bind (fun word => ProbComp.eval (adversary word))) =
    Game.advantage
      (((uniformList seedBits).map (generator i.val)).bind
        (fun word => ProbComp.eval (test count seedBits outputBits generator i.val adversary word)))
      ((uniformList outputBits).bind
        (fun word =>
          ProbComp.eval (test count seedBits outputBits generator i.val adversary word))) := by
  conv_lhs => rw [← real_distribution count seedBits outputBits generator i,
    ← ideal_distribution count seedBits outputBits generator i]
  simp only [test, ProbComp.eval_bind, BitString.eval_sampleList, PMF.monad_bind_eq_bind,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- One secure choice in a uniformly efficient family makes the XOR computationally uniform.
The combiner evaluates the whole family; only the reduction receives the proof's chosen index. -/
theorem indistinguishable {generator : ℕ → ℕ → List Bool → List Bool}
    {count seedBits outputBits choose : ℕ → ℕ}
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary)
    (hseedBits : ComputableTidilyInPolyTime seedBits encUnary encUnary)
    (houtputBits : ComputableTidilyInPolyTime outputBits encUnary encUnary)
    (hgenerator : ComputableTidilyInPolyTime (fun input => generator input.1.1 input.1.2 input.2)
      (encPair (encPair encUnary encUnary) encBits) encBits)
    (hchoose : ∀ᶠ n in Filter.atTop, choose n < count n)
    (hsecure : ∀ adversary : ℕ → ℕ → List Bool → ProbComp Bool,
      IsPPTOn (encPair (encPair encUnary encUnary) encBits)
        encBool (fun input => adversary input.1.1 input.1.2 input.2) →
      Negligible (fun n => Game.advantage
        (((uniformList (seedBits n)).map (generator n (choose n))).bind
          (fun word => ProbComp.eval (adversary n (choose n) word)))
        ((uniformList (outputBits n)).bind
          (fun word => ProbComp.eval (adversary n (choose n) word))))) :
    ComputationallyIndistinguishable
      (fun n => (uniformList (count n * seedBits n)).map
        (generate (count n) (seedBits n) (outputBits n) (generator n)))
      (fun n => uniformList (outputBits n)) := by
  intro adversary hadversary
  let reduction := fun n index =>
    test (count n) (seedBits n) (outputBits n) (generator n) index (adversary n)
  have hreduce : IsPPTOn (encPair (encPair encUnary encUnary) encBits)
      encBool (fun input => reduction input.1.1 input.1.2 input.2) := by
    unfold reduction
    apply isPPTOn_test <;> first | polytime | ppt
  apply (hsecure reduction hreduce).congr'
  filter_upwards [hchoose] with n hn
  simpa only [distinguishingGame, PMF.monad_bind_eq_bind] using
    (advantage_eq (count n) (seedBits n) (outputBits n) (generator n) ⟨choose n, hn⟩
      (adversary n)).symm

end Cslib.Crypto.GeneratorXor

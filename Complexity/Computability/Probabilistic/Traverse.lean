/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Languages.Probabilistic.Traverse
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Tactic.PolyTime.Init
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Strict PPT list traversal

An ordinary `List.mapM` traversal of a strict PPT program is strict PPT on framed list
encodings. One polynomial coin budget, chosen from the complete encoded input list, bounds the
budget of every element. Independent blocks of one random tape realize all calls. The existing
deterministic list calculus charges the traversal, row extraction and complete output encoding.

## Main results

* `Cslib.Probability.IsPPTOn.mapM`: strict PPT is closed under list traversal.
* `Cslib.Probability.IsPPTOn.mapMWith`: the traversal may capture its complete input.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

private theorem eval_mapM_of_uniformList {α β : Type} (program : α → ProbComp β)
    (evaluate : α → List Bool → β) (width : ℕ) (list : List α)
    (hlaw : ∀ a ∈ list,
      ProbComp.eval (program a) = (BitString.uniformList width).map (evaluate a)) :
    ProbComp.eval (list.mapM program) =
      (BitString.uniformList (list.length * width)).map
        (fun tape => List.zipWith evaluate list (BitString.listRows list.length width tape)) := by
  induction list with
  | nil => simp [BitString.listRows, ProbComp.eval_pure]
  | cons a list ih =>
    simp only [List.mapM_cons, bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map]
    rw [hlaw a (List.mem_cons_self ..), ih (fun b hb => hlaw b (List.mem_cons_of_mem _ hb))]
    rw [show (a :: list).length * width = width + list.length * width by
      simp [Nat.add_mul, Nat.add_comm]]
    rw [BitString.uniformList_add, PMF.map_bind, PMF.bind_map]
    apply PMF.bind_congr_on_support
    intro front hfront
    have hlength := BitString.length_of_mem_support_uniformList hfront
    simp [PMF.map_comp, Function.comp_def, BitString.listRows_succ_append _ _ hlength]

private theorem zipWith_listRows_eq {α β : Type} (evaluate : α → List Bool → β)
    (list : List α) (width : ℕ) (tape : List Bool) :
    List.zipWith evaluate list (BitString.listRows list.length width tape) =
      list.zipIdx.map (fun p => evaluate p.1 (BitString.listRow width p.2 tape)) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [BitString.listRows]

/-- Traverse a framed input list with a strict PPT program. One machine and polynomial clock
work for all lists, including the empty list, and charge the complete encoded output list. -/
@[program_certificate]
theorem IsPPTOn.mapM {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → ProbComp β} (hprogram : IsPPTOn input output program) :
    IsPPTOn (encList input) (encList output) (fun list => list.mapM program) := by
  obtain ⟨c, d, evaluate, hevaluate, _, hlaw⟩ := hprogram.exists_total_seeded_evaluator
  let budget (list : List α) := c * ((encList input list).length + 1) ^ d
  have hencode : ComputableTidilyInPolyTime (encList input) (encList input) encBits :=
    .of_eq fun _ => rfl
  have hbudget : ComputableTidilyInPolyTime budget (encList input) encUnary := by
    dsimp only [budget]
    fun_prop
  have hcount : ComputableTidilyInPolyTime (List.length (α := α))
      (encList input) encUnary := by fun_prop
  have hrun : ComputableTidilyInPolyTime (fun p : List α × List Bool =>
      p.1.zipIdx.map (fun q => evaluate q.1 (BitString.listRow (budget p.1) q.2 p.2)))
      (encPair (encList input) encBits) (encList output) := by
    apply ComputableTidilyInPolyTime.mapWithInput
    · fun_prop
    · exact hevaluate.comp (show ComputableTidilyInPolyTime
        (fun p : (List α × List Bool) × (α × ℕ) =>
          (p.2.1, BitString.listRow (budget p.1.1) p.2.2 p.1.2))
        (encPair (encPair (encList input) encBits) (encPair input encUnary))
        (encPair input encBits) by fun_prop)
  have hcoins := (ComputableTidilyInPolyTime.unary_mul.comp (hcount.prod hbudget)).sampleList
  apply (hcoins.map_with (f := fun list tape => list.zipIdx.map
    (fun q => evaluate q.1 (BitString.listRow (budget list) q.2 tape))) (.of_tidy hrun)).congr
  intro list
  rw [ProbComp.eval_map, BitString.eval_sampleList]
  symm
  rw [eval_mapM_of_uniformList program evaluate (budget list) list]
  · simp only [zipWith_listRows_eq, Function.comp_def]
  · intro a ha
    apply hlaw
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by
      have := length_le_encList_of_mem input ha
      omega) d)

/-- A list traversal may use the complete original input in every call. Preparing the pairs
charges for repeated captured data as well as all elements of the computed list. -/
@[program_certificate]
theorem IsPPTOn.mapMWith {α β γ : Type} {input : α ↪ List Bool}
    {element : β ↪ List Bool} {output : γ ↪ List Bool} {list : α → List β}
    {program : α → β → ProbComp γ}
    (hprogram : IsPPTOn (encPair input element) output (fun p => program p.1 p.2))
    (hlist : ComputableTidilyInPolyTime list input (encList element)) :
    IsPPTOn input (encList output) (fun a => (list a).mapM (program a)) := by
  have hpairs : ComputableTidilyInPolyTime (fun a => (list a).map fun b => (a, b))
      input (encList (encPair input element)) := by fun_prop
  apply (hprogram.mapM.preprocess (ComputableInPolyTime.of_tidy hpairs)).congr
  intro a
  simp only [List.mapM_map, Function.comp_def]

end Cslib.Probability

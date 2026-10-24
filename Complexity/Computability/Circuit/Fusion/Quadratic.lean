/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Cyclic.Compiler
public import Complexity.Computability.Circuit.Iteration
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# Quadratic completeness of semifilter covers

A cover of length `t` yields an acyclic set circuit with exactly `t²` charged AND gates.
Unions and constants are free. The construction works on arbitrary carriers: at each point,
only the `t` pair coordinates can become true, so `t` synchronous rounds suffice.

Counting every gate instead, unions and constants included, the circuit over `n` supplied sets
has at most `4 (t + 1)² (n + t + 1)` gates: each round reads at most `n + t` seeds per argument
through a union tree.

## Main definitions

* `Cslib.Circuits.Fusion.PairClosureCompiler.stages`: synchronous pair propagation.
* `Cslib.Circuits.Fusion.PairCover.toCircuit`: an acyclic circuit realizing an unrestricted cover.

## Main results

* `Cslib.Circuits.Fusion.PairClosureCompiler.readState_stages`: `t` rounds recover the closure.
* `Cslib.Circuits.Fusion.PairCover.cost_toCircuit`: exactly `t²` AND gates.
* `Cslib.Circuits.Fusion.PairCover.size_toCircuit_le`: at most `4 (t + 1)² (n + t + 1)` gates.
* `Cslib.Circuits.Fusion.PairCover.eval_toCircuit`: evaluation gives the target.
* `Cslib.Circuits.Fusion.ecomplexityFrom_le_pairCoverComplexity_sq`: the minimum AND cost is at
  most the square of unrestricted cover complexity.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*, Theorem 24][CavalarOliveira2025]. This formalization uses the native monotone
  basis with free bottom and top constants, and includes empty inputs and trivial targets.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.PairClosureCompiler

universe u

variable {U : Type u} {n : ℕ}
variable (target : Set U) (input : Fin n → Set U)
  (pairs : List (Set ↥(targetᶜ) × Set ↥(targetᶜ)))

/-- Apply every listed intersection rule to the reconstructed state. -/
def step (state : Fin pairs.length → Set U) : Fin pairs.length → Set U :=
  fun j => readState target input pairs state (pairs.get j).1 ∩
    readState target input pairs state (pairs.get j).2

/-- Pair values after `k` synchronous rounds, starting with all pair values empty. -/
def stages : ℕ → Fin pairs.length → Set U
  | 0 => ⊥
  | k + 1 => step target input pairs (stages k)

/-- Reconstruction is monotone in the supplied pair values. -/
theorem readState_mono {s t : Fin pairs.length → Set U} (h : s ≤ t) :
    readState target input pairs s ≤ readState target input pairs t := by
  intro a point hp
  rcases hp with hu | hi | ⟨j, hj, hx⟩
  · exact Or.inl hu
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr ⟨j, hj, h j hx⟩)

/-- Pair propagation is monotone. -/
theorem step_mono : Monotone (step target input pairs) :=
  fun _ _ h _ => Set.inter_subset_inter (readState_mono target input pairs h _)
    (readState_mono target input pairs h _)

/-- Pair values only grow as rounds proceed. -/
theorem stages_mono : Monotone (stages target input pairs) := by
  apply monotone_nat_of_le_succ
  intro k
  induction k with
  | zero => exact bot_le
  | succ k ih => exact step_mono target input pairs ih

private theorem readState_congr_point {s t : Fin pairs.length → Set U} {point : U}
    (h : ∀ j, point ∈ s j ↔ point ∈ t j) (a : Set ↥(targetᶜ)) :
    point ∈ readState target input pairs s a ↔ point ∈ readState target input pairs t a := by
  change (_ ∨ _ ∨ ∃ j, _ ∧ point ∈ s j) ↔ (_ ∨ _ ∨ ∃ j, _ ∧ point ∈ t j)
  simp only [h]

private theorem finite_chain_stable {m : ℕ} (a : ℕ → Finset (Fin m)) (ha : Monotone a)
    (hstep : ∀ k, a k = a (k + 1) → a (k + 1) = a (k + 2)) : a m = a (m + 1) := by
  have hcard (k : ℕ) : (a k).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (a k))
  have hanti : Antitone (fun k => m - (a k).card) := by
    intro k l hkl
    exact Nat.sub_le_sub_left (Finset.card_le_card (ha hkl)) m
  have heq (k : ℕ) (h : m - (a k).card = m - (a (k + 1)).card) :
      a k = a (k + 1) := by
    apply Finset.eq_of_subset_of_card_le (ha (Nat.le_succ k))
    have := hcard k
    have := hcard (k + 1)
    lia
  obtain ⟨k, hk, hstable⟩ := Nat.stabilises_of_antitone hanti (fun k h => by
    rw [hstep k (heq k h)])
  apply heq m
  rw [hstable m (by lia), hstable (m + 1) (by lia)]

/-- Every point's pair state stabilizes within the number of listed pairs, independently of
how many points the carrier contains. -/
theorem stages_stable :
    stages target input pairs pairs.length = stages target input pairs (pairs.length + 1) := by
  classical
  funext j
  ext point
  let a (k : ℕ) : Finset (Fin pairs.length) :=
    Finset.univ.filter (fun i => point ∈ stages target input pairs k i)
  have ha : Monotone a := by
    intro k l hkl i hi
    simp only [a, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact stages_mono target input pairs hkl i hi
  have hstep (k : ℕ) (h : a k = a (k + 1)) : a (k + 1) = a (k + 2) := by
    have hpoint (i) : point ∈ stages target input pairs k i ↔
        point ∈ stages target input pairs (k + 1) i := by
      have := Finset.ext_iff.mp h i
      simpa only [a, Finset.mem_filter, Finset.mem_univ, true_and] using this
    ext i
    simp only [a, Finset.mem_filter, Finset.mem_univ, true_and, stages, step, Set.mem_inter_iff]
    exact and_congr (readState_congr_point target input pairs hpoint _)
      (readState_congr_point target input pairs hpoint _)
  have := Finset.ext_iff.mp (finite_chain_stable a ha hstep) j
  simpa only [a, Finset.mem_filter, Finset.mem_univ, true_and] using this

/-- All finite propagation stages are contained in the generated pair values. -/
private theorem stages_le_pairValues (k : ℕ) :
    stages target input pairs k ≤ pairValues target input pairs := by
  induction k with
  | zero => exact bot_le
  | succ k ih =>
    have h := step_mono target input pairs ih
    intro j
    have hj := h j
    change _ ⊆ readState target input pairs (pairValues target input pairs) _ ∩
      readState target input pairs (pairValues target input pairs) _ at hj
    simpa only [readState_pairValues, stages, pairValues] using hj

/-- After one round per pair, reconstruction is exactly the generated semifilter closure. -/
theorem readState_stages :
    readState target input pairs (stages target input pairs pairs.length) =
      pairClosure target input pairs := by
  apply le_antisymm
  · exact (readState_mono target input pairs (stages_le_pairValues target input pairs _)).trans_eq
      (readState_pairValues target input pairs)
  · apply pairClosure_le_readState
    intro j
    change stages target input pairs (pairs.length + 1) j ⊆ _
    rw [← stages_stable]

/-- Preserve the external inputs while performing one native circuit update. -/
noncomputable def roundCircuit : Circuit Monotone.signature
    (n + (pairs.length + 1)) (n + (pairs.length + 1)) :=
  (Circuit.wiring Monotone.signature (Fin.castAdd (pairs.length + 1))).append
    (updateCircuit target input pairs)

/-- The initial state has the supplied inputs and empty pair coordinates. -/
def initialCircuit : Circuit Monotone.signature n (n + (pairs.length + 1)) :=
  (Circuit.id Monotone.signature n).append
    (Circuit.pi (fun _ : Fin (pairs.length + 1) =>
      (Monotone.const false : Formula Monotone.signature n).toCircuit))

/-- Unroll the finite update program, retaining the input wires at every round. -/
noncomputable def stageCircuit (k : ℕ) :
    Circuit Monotone.signature n (n + (pairs.length + 1)) :=
  ((roundCircuit target input pairs).iterate k).comp (initialCircuit target pairs)

/-- Each propagation round charges one conjunction per listed pair. -/
private theorem cost_stageCircuit (k : ℕ) :
    (stageCircuit target input pairs k).program.cost Monotone.andCost = k * pairs.length := by
  rw [stageCircuit, Circuit.cost_program_comp, Circuit.cost_program_iterate,
    roundCircuit, Circuit.cost_program_append, Circuit.cost_program_wiring, cost_updateCircuit,
    initialCircuit, Circuit.cost_program_append, Circuit.id, Circuit.cost_program_wiring,
    Circuit.cost_program_pi]
  simp [Formula.cost_toCircuit, Monotone.const]

/-- The unrolled program carries the intended pair values; the extra output is a free read
from the preceding round and is ignored by all subsequent pair updates. -/
theorem eval_stageCircuit (k : ℕ) :
    ∃ output, (stageCircuit target input pairs k).eval (Monotone.setInterpretation U) input =
      Fin.append input (Fin.lastCases output (stages target input pairs k)) := by
  induction k with
  | zero =>
    refine ⟨∅, ?_⟩
    simp only [stageCircuit, Circuit.iterate, Circuit.eval_comp, Circuit.id,
      Circuit.eval_wiring, Function.comp_id,
      initialCircuit, Circuit.eval_append, Circuit.eval_pi, Formula.eval_toCircuit]
    congr 1
    funext j
    induction j using Fin.lastCases <;> simp [Monotone.const, stages]
  | succ k ih =>
    obtain ⟨output, houtput⟩ := ih
    refine ⟨readState target input pairs (stages target input pairs k) ∅, ?_⟩
    have hrestrict : Fin.lastCases output (stages target input pairs k) ∘ Fin.castSucc =
        stages target input pairs k := by
      funext j
      simp only [Function.comp_apply, Fin.lastCases_castSucc]
    simp only [stageCircuit, Circuit.iterate, Circuit.eval_comp] at houtput ⊢
    rw [houtput]
    simp only [roundCircuit, Circuit.eval_append, Circuit.eval_wiring,
      Fin.append_comp_castAdd, eval_updateCircuit, hrestrict, stages]
    rfl

/-- A union tree has one disjunction per argument and its seed constant. -/
theorem size_joinFormula {r : ℕ} (seed : Bool) (fs : List (Formula Monotone.signature r)) :
    (joinFormula seed fs).size = (fs.map (·.size)).sum + fs.length + 1 := by
  induction fs with
  | nil => simp [joinFormula, Monotone.const]
  | cons f fs ih =>
    simp only [joinFormula, Monotone.or, Formula.size_gate, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, ih, List.map_cons, List.sum_cons,
      List.length_cons]
    lia

private theorem size_ite_input_le {r : ℕ} (p : Prop) [Decidable p] (i : Fin r) :
    (if p then Formula.input i else Monotone.const false :
      Formula Monotone.signature r).size ≤ 1 := by
  split <;> simp [Monotone.const]

/-- Reading a closure coordinate uses at most two gates per input seed and pair value. -/
theorem size_readFormula_le (s : Set ↥(targetᶜ)) :
    (readFormula target input pairs s).size ≤ 2 * (n + pairs.length) + 1 := by
  classical
  rw [readFormula, size_joinFormula]
  set L := List.ofFn (fun i : Fin n =>
      if Subtype.val ⁻¹' input i ⊆ s then Formula.input (Fin.castAdd (pairs.length + 1) i)
      else Monotone.const false) ++
    List.ofFn (fun j : Fin pairs.length =>
      if (pairs.get j).1 ∩ (pairs.get j).2 ⊆ s then Formula.input (Fin.natAdd n j.castSucc)
      else Monotone.const false) with hL
  have hsum := List.sum_le_length_nsmul (L.map (·.size)) 1 fun x hx => by
    obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hx
    rcases List.mem_append.1 hF with h | h <;> obtain ⟨i, rfl⟩ := List.mem_ofFn.1 h <;>
      exact size_ite_input_le _ _
  have hlen : L.length = n + pairs.length := by simp [hL]
  simp only [List.length_map, smul_eq_mul, mul_one, hlen] at hsum
  rw [hlen]
  lia

/-- The update circuit has at most `(t + 1) (4 (n + t) + 3)` gates for `t` pairs. -/
theorem size_updateCircuit_le :
    (updateCircuit target input pairs).size ≤
      (pairs.length + 1) * (4 * (n + pairs.length) + 3) := by
  rw [updateCircuit, Circuit.size_pi]
  calc ∑ j, (updateFormula target input pairs j).toCircuit.size
      ≤ ∑ _j : Fin (pairs.length + 1), (4 * (n + pairs.length) + 3) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Formula.size_toCircuit]
        induction j using Fin.lastCases with
        | last =>
          rw [updateFormula, Fin.lastCases_last]
          exact (size_readFormula_le target input pairs ∅).trans (by lia)
        | cast j =>
          rw [updateFormula, Fin.lastCases_castSucc]
          have h₁ := size_readFormula_le target input pairs (pairs.get j).1
          have h₂ := size_readFormula_le target input pairs (pairs.get j).2
          simp only [Monotone.and, Formula.size_gate, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_fin_one]
          lia
    _ = (pairs.length + 1) * (4 * (n + pairs.length) + 3) := by simp

/-- Each propagation round charges the gates of one update circuit. -/
theorem size_stageCircuit (k : ℕ) :
    (stageCircuit target input pairs k).size =
      (pairs.length + 1) + k * (updateCircuit target input pairs).size := by
  simp [stageCircuit, roundCircuit, initialCircuit, Circuit.id, Formula.size_toCircuit,
    Monotone.const]

end Cslib.Circuits.Fusion.PairClosureCompiler

namespace Cslib.Circuits.Fusion

universe u

variable {U : Type u} {n : ℕ} {target : Set U} {input : Fin n → Set U}

/-- Compile an unrestricted pair cover to an ordinary acyclic set circuit, using one
propagation round per pair. Constants and binary unions are free. -/
noncomputable def PairCover.toCircuit (c : PairCover target input) :
    Circuit Monotone.signature n 1 :=
  (PairClosureCompiler.readFormula target input c.pairs ∅).toCircuit.comp
    (PairClosureCompiler.stageCircuit target input c.pairs c.pairs.length)

/-- The unrolled cover compiler uses exactly the square of the pair count in AND gates. -/
@[simp] theorem PairCover.cost_toCircuit (c : PairCover target input) :
    c.toCircuit.program.cost Monotone.andCost = c.pairs.length ^ 2 := by
  rw [PairCover.toCircuit, Circuit.cost_program_comp, Formula.cost_toCircuit,
    PairClosureCompiler.cost_readFormula, PairClosureCompiler.cost_stageCircuit,
    Nat.add_zero, pow_two]

/-- The acyclic circuit compiled from an unrestricted cover computes its target set. -/
@[simp] theorem PairCover.eval_toCircuit (c : PairCover target input) :
    c.toCircuit.eval (Monotone.setInterpretation U) input = fun _ => target := by
  obtain ⟨output, houtput⟩ := PairClosureCompiler.eval_stageCircuit target input c.pairs
    c.pairs.length
  have hrestrict : Fin.lastCases output
      (PairClosureCompiler.stages target input c.pairs c.pairs.length) ∘ Fin.castSucc =
        PairClosureCompiler.stages target input c.pairs c.pairs.length := by
    funext j
    simp only [Function.comp_apply, Fin.lastCases_castSucc]
  funext i
  rw [PairCover.toCircuit, Circuit.eval_comp, houtput, Formula.eval_toCircuit,
    PairClosureCompiler.eval_readFormula, hrestrict, PairClosureCompiler.readState_stages,
    c.pairClosure_empty]

/-- The compiled circuit of a `t`-pair cover over `n` inputs has at most `4 (t + 1)² (n + t + 1)`
gates in total, counting unions and constants. -/
theorem PairCover.size_toCircuit_le (c : PairCover target input) :
    c.toCircuit.size ≤ 4 * (c.pairs.length + 1) ^ 2 * (n + c.pairs.length + 1) := by
  have hr := PairClosureCompiler.size_readFormula_le target input c.pairs ∅
  have hu := PairClosureCompiler.size_updateCircuit_le target input c.pairs
  rw [PairCover.toCircuit, Circuit.size_comp, PairClosureCompiler.size_stageCircuit,
    Formula.size_toCircuit]
  have hk := Nat.mul_le_mul_left c.pairs.length hu
  nlinarith

/-- Every unrestricted pair cover yields a quadratic upper bound for native AND complexity. -/
private theorem PairCover.ecomplexityFrom_le_sq (c : PairCover target input) :
    ecomplexityFrom (Monotone.setInterpretation U) Monotone.andCost
      (fun _ : Unit => fun _ : Fin 1 => target) (fun _ => input) ≤
        (c.pairs.length : ℕ∞) ^ 2 := by
  have h := ecomplexityFrom_le_of_computesFrom (cost := Monotone.andCost)
    c.toCircuit (fun _ : Unit => c.eval_toCircuit)
  simpa only [PairCover.cost_toCircuit, Nat.cast_pow] using h

/-- **Quadratic completeness of Fusion**, in the native basis with free constants and unions.
No assumption on the carrier, target, or input-family size is needed with this convention. -/
theorem ecomplexityFrom_le_pairCoverComplexity_sq (target : Set U) (input : Fin n → Set U) :
    ecomplexityFrom (Monotone.setInterpretation U) Monotone.andCost
      (fun _ : Unit => fun _ : Fin 1 => target) (fun _ => input) ≤
        pairCoverComplexity target input ^ 2 := by
  by_cases htop : pairCoverComplexity target input = ⊤
  · simp [htop]
  have : Nonempty (PairCover target input) := ENat.iInf_natCast_ne_top.mp htop
  obtain ⟨c, hc⟩ := ENat.exists_eq_iInf (fun c : PairCover target input =>
    (c.pairs.length : ℕ∞))
  exact c.ecomplexityFrom_le_sq.trans_eq (congrArg (fun x => x ^ 2) hc)

end Cslib.Circuits.Fusion

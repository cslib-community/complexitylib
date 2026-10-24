/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.SourceComplexity
public import Complexity.Computability.Circuit.Pi
public import Complexity.Computability.Circuit.Parallel
import Complexity.Computability.Circuit.Simulation
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Independent copies of a circuit

Inputs and outputs are arranged in consecutive blocks. A family of circuits runs its members on
disjoint blocks and adds their gate counts and arbitrary weighted costs exactly. Replication is
the constant family: it preserves sharing between the outputs of each copy, and multiplies both
gate count and arbitrary weighted cost exactly.
Keeping a positive initial batch requires only input and output wiring. The resulting minimum
cost is monotone even at zero copies, where a separate empty circuit suffices.

## Main definitions

* `Cslib.Circuits.directProductInput`, `Cslib.Circuits.blockMap`,
  `Cslib.Circuits.directProduct`: input block selection and independent copies of multi-output and
  scalar functions.
* `Cslib.Circuits.Circuit.parallelFamily`: different circuits on consecutive disjoint blocks.
* `Cslib.Circuits.Circuit.replicate`: independent copies of a multi-output circuit, the
  constant family.
* `Cslib.Circuits.Circuit.replicateScalar`: the single-output specialization.
* `Cslib.Circuits.Circuit.takeDirectProductPrefix`: retain a positive initial batch.

## Main results

* `Cslib.Circuits.Circuit.eval_parallelFamily_apply`,
  `Cslib.Circuits.Circuit.cost_program_parallelFamily`: blockwise semantics and additive cost.
* `Cslib.Circuits.Circuit.eval_replicate`,
  `Cslib.Circuits.Circuit.cost_program_replicate`: exact replication semantics and cost.
* `Cslib.Circuits.ecomplexityFrom_directProduct_le`: the naive replication upper bound.
* `Cslib.Circuits.ecomplexityFrom_directProduct_mono`,
  `Cslib.Circuits.complexity_directProduct_mono`: monotonicity in the number of copies.
* `Cslib.Circuits.ecomplexityFrom_directProduct_comp_wiring_le`: blockwise input rewiring.

## References

* Adapted from MassProduction/DirectProduct.lean and MassProduction/InputSplit.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} {U : Type u} {n m k : ℕ}

/-- Select one consecutive block of inputs. -/
def directProductInput (x : Fin (k * n) → U) (j : Fin k) : Fin n → U :=
  fun i => x (finProdFinEquiv (j, i))

/-- Apply a multi-output function independently to each input block. -/
def blockMap (f : (Fin n → U) → Fin m → U) (k : ℕ) :
    (Fin (k * n) → U) → Fin (k * m) → U :=
  fun x i => f (directProductInput x (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

/-- Apply a scalar function independently to each input block. -/
def directProduct (f : (Fin n → U) → U) (k : ℕ) : (Fin (k * n) → U) → Fin k → U :=
  fun x j => f (directProductInput x j)

/-- Coordinate `(j, i)` of `blockMap f k x` is output `i` of `f` on input block `j`. -/
@[simp] theorem blockMap_apply (f : (Fin n → U) → Fin m → U)
    (x : Fin (k * n) → U) (j : Fin k) (i : Fin m) :
    blockMap f k x (finProdFinEquiv (j, i)) = f (directProductInput x j) i := by
  simp [blockMap]

namespace Circuit

/-- Circuits of a family run on consecutive disjoint input blocks, preserving sharing within
each member. Their outputs are arranged in the same block order. -/
def parallelFamily : {k : ℕ} → (Fin k → Circuit σ n m) → Circuit σ (k * n) (k * m)
  | 0, _ => Circuit.wiring σ (Fin.elim0 ∘ Fin.cast (Nat.zero_mul m))
  | k + 1, cs =>
    (Circuit.wiring σ (Fin.cast (Nat.succ_mul k m))).comp
      (((parallelFamily fun j => cs j.castSucc).parallel (cs (Fin.last k))).comp
        (Circuit.wiring σ (Fin.cast (Nat.succ_mul k n).symm)))

/-- Each output of each member reads exactly that member's input block. -/
theorem eval_parallelFamily_apply {k : ℕ} (cs : Fin k → Circuit σ n m) (I : Interpretation σ U)
    (x : Fin (k * n) → U) (j : Fin k) (i : Fin m) :
    (parallelFamily cs).eval I x (finProdFinEquiv (j, i)) =
      (cs j).eval I (directProductInput x j) i := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    simp only [parallelFamily, eval_comp, eval_wiring, eval_parallel, Function.comp_apply]
    by_cases hj : j.val < k
    · let j' : Fin k := ⟨j.val, hj⟩
      rw [show Fin.cast (Nat.succ_mul k m) (finProdFinEquiv (j, i)) =
        Fin.castAdd m (finProdFinEquiv (j', i)) by
          apply Fin.ext
          simp [finProdFinEquiv, j']]
      rw [Fin.append_left, ih, show j'.castSucc = j from Fin.ext rfl]
      congr 1
    · have hj' : j = Fin.last k := Fin.ext (by simp only [Fin.val_last]; lia)
      subst hj'
      rw [show Fin.cast (Nat.succ_mul k m) (finProdFinEquiv (Fin.last k, i)) =
        Fin.natAdd (k * m) i by
          apply Fin.ext
          simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]]
      rw [Fin.append_right]
      congr 1
      funext a
      apply congrArg x
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Running a family on disjoint blocks adds arbitrary weighted cost exactly. -/
theorem cost_program_parallelFamily {k : ℕ} (cs : Fin k → Circuit σ n m) (cost : σ.Op → ℕ) :
    (parallelFamily cs).program.cost cost = ∑ j, (cs j).program.cost cost := by
  induction k with
  | zero => simp only [parallelFamily, cost_program_wiring, Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ k ih =>
    simp only [parallelFamily, cost_program_comp, cost_program_parallel, cost_program_wiring,
      Nat.zero_add, Nat.add_zero, ih, Fin.sum_univ_castSucc]

/-- Running a family on disjoint blocks adds gate counts exactly. -/
@[simp] theorem size_parallelFamily {k : ℕ} (cs : Fin k → Circuit σ n m) :
    (parallelFamily cs).size = ∑ j, (cs j).size := by
  simpa only [Program.cost_const, one_mul] using cost_program_parallelFamily cs (fun _ => 1)

/-- Disjoint-input copies of a circuit, preserving sharing within each copy. -/
def replicate (c : Circuit σ n m) (k : ℕ) : Circuit σ (k * n) (k * m) :=
  parallelFamily fun _ : Fin k => c

/-- Each output of each copy reads exactly its own input block. -/
theorem eval_replicate_apply (c : Circuit σ n m) (k : ℕ) (I : Interpretation σ U)
    (x : Fin (k * n) → U) (j : Fin k) (i : Fin m) :
    (c.replicate k).eval I x (finProdFinEquiv (j, i)) =
      c.eval I (directProductInput x j) i :=
  eval_parallelFamily_apply _ I x j i

/-- Replication computes the blockwise application of the original circuit. -/
@[simp] theorem eval_replicate (c : Circuit σ n m) (k : ℕ) (I : Interpretation σ U)
    (x : Fin (k * n) → U) :
    (c.replicate k).eval I x = blockMap (c.eval I) k x := by
  funext i
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective i
  exact (c.eval_replicate_apply k I x j i).trans (blockMap_apply _ _ _ _).symm

/-- Replication multiplies arbitrary weighted cost exactly. -/
theorem cost_program_replicate (c : Circuit σ n m) (k : ℕ) (cost : σ.Op → ℕ) :
    (c.replicate k).program.cost cost = k * c.program.cost cost := by
  -- This induction avoids the `Classical.choice` dependency of the general family cost law.
  induction k with
  | zero => simp only [replicate, parallelFamily, cost_program_wiring, Nat.zero_mul]
  | succ k ih =>
    simp only [replicate, parallelFamily, cost_program_comp, cost_program_parallel,
      cost_program_wiring, Nat.zero_add, Nat.add_zero] at ih ⊢
    rw [ih, Nat.succ_mul]

/-- Replication multiplies the gate count exactly. -/
@[simp] theorem size_replicate (c : Circuit σ n m) (k : ℕ) :
    (c.replicate k).size = k * c.size := by
  simpa only [Program.cost_const, one_mul] using c.cost_program_replicate k (fun _ => 1)

/-- Single-output copies, with one output per input block. -/
def replicateScalar (c : Circuit σ n 1) (k : ℕ) : Circuit σ (k * n) k :=
  pi fun j => c.comp (Circuit.wiring σ fun i => finProdFinEquiv (j, i))

/-- Evaluating `c.replicateScalar k` computes `directProduct (fun y => c.eval I y 0) k`. -/
@[simp] theorem eval_replicateScalar (c : Circuit σ n 1) (k : ℕ) (I : Interpretation σ U)
    (x : Fin (k * n) → U) :
    (c.replicateScalar k).eval I x = directProduct (fun y => c.eval I y 0) k x := by
  simp only [replicateScalar, eval_pi, eval_comp, eval_wiring]
  rfl

/-- Scalar replication also preserves the exact weighted cost. -/
theorem cost_program_replicateScalar (c : Circuit σ n 1) (k : ℕ) (cost : σ.Op → ℕ) :
    (c.replicateScalar k).program.cost cost = k * c.program.cost cost := by
  simp only [replicateScalar, cost_program_pi, cost_program_comp, cost_program_wiring,
    Nat.zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Scalar replication multiplies the gate count by `k`. -/
@[simp] theorem size_replicateScalar (c : Circuit σ n 1) (k : ℕ) :
    (c.replicateScalar k).size = k * c.size := by
  simpa only [Program.cost_const, one_mul] using c.cost_program_replicateScalar k (fun _ => 1)

/-- A scalar computation gives a concrete circuit for every finite direct product. -/
theorem Computes.replicateScalar {c : Circuit σ n 1} {I : Interpretation σ U}
    {f : (Fin n → U) → U} (hc : c.Computes I (single f)) (k : ℕ) :
    (c.replicateScalar k).Computes I (directProduct f k) := fun x => by
  rw [eval_replicateScalar]
  funext j
  exact congrFun (hc (directProductInput x j)) 0

/-- Retain a positive initial batch by rewiring inputs and selecting outputs, without adding
or removing gates. Discarded input blocks read the first retained block. -/
def takeDirectProductPrefix {large : ℕ} (c : Circuit σ (large * n) large) (small : ℕ)
    (hsmall : 0 < small) (hle : small ≤ large) : Circuit σ (small * n) small :=
  (Circuit.wiring σ (Fin.castLE hle)).comp (c.comp (Circuit.wiring σ fun i =>
    let ji := finProdFinEquiv.symm i
    finProdFinEquiv ((if h : ji.1.val < small then ⟨ji.1.val, h⟩ else ⟨0, hsmall⟩), ji.2)))

/-- Retaining a positive initial batch keeps the exact weighted cost. -/
theorem cost_program_takeDirectProductPrefix {small large : ℕ}
    (c : Circuit σ (large * n) large) (hsmall : 0 < small) (hle : small ≤ large)
    (cost : σ.Op → ℕ) :
    (c.takeDirectProductPrefix small hsmall hle).program.cost cost = c.program.cost cost := by
  simp only [takeDirectProductPrefix, cost_program_comp, cost_program_wiring,
    Nat.zero_add, Nat.add_zero]

/-- Retaining an initial batch preserves direct-product semantics. -/
theorem Computes.takeDirectProductPrefix {small large : ℕ} {c : Circuit σ (large * n) large}
    {I : Interpretation σ U} {f : (Fin n → U) → U}
    (hc : c.Computes I (directProduct f large)) (hsmall : 0 < small) (hle : small ≤ large) :
    (c.takeDirectProductPrefix small hsmall hle).Computes I (directProduct f small) := by
  intro x
  simp only [Circuit.takeDirectProductPrefix, eval_comp, eval_wiring]
  rw [hc]
  funext j
  apply congrArg f
  funext i
  simp only [directProductInput, Function.comp_apply, Equiv.symm_apply_apply]
  simp

end Circuit

variable {I : Interpretation σ U} {cost : σ.Op → ℕ} {f : (Fin n → U) → U}

/-- Zero copies have zero weighted complexity, even for a function with no circuit. -/
@[simp] theorem ecomplexityFrom_directProduct_zero :
    ecomplexityFrom I cost (directProduct f 0) id = 0 := by
  apply nonpos_iff_eq_zero.mp
  exact ecomplexityFrom_le_of_computesFrom
    (Circuit.wiring σ (Fin.elim0 : Fin 0 → Fin (0 * n))) (fun _ => funext fun i => i.elim0)

/-- Independently replicating a scalar implementation gives the naive weighted upper bound.
The statement includes zero copies and functions of infinite complexity. -/
theorem ecomplexityFrom_directProduct_le (k : ℕ) :
    ecomplexityFrom I cost (directProduct f k) id ≤
      (k : ℕ∞) * ecomplexityFrom I cost (single f) id := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  by_cases h : ecomplexityFrom I cost (single f) id = ⊤
  · simp [h, hk.ne']
  obtain ⟨c, hc, hcost⟩ := exists_computesFrom_cost_eq_ecomplexityFrom
    (ecomplexityFrom_ne_top_iff.mp h)
  exact (ecomplexityFrom_le_of_computesFrom _ (Circuit.Computes.replicateScalar hc k)).trans_eq
    (by rw [Circuit.cost_program_replicateScalar, Nat.cast_mul, hcost])

/-- Minimum weighted direct-product complexity is monotone in the number of copies. -/
theorem ecomplexityFrom_directProduct_mono {small large : ℕ} (hle : small ≤ large) :
    ecomplexityFrom I cost (directProduct f small) id ≤
      ecomplexityFrom I cost (directProduct f large) id := by
  rcases small.eq_zero_or_pos with rfl | hsmall
  · simp
  refine le_ecomplexityFrom_iff.mpr fun c hc => ?_
  exact (ecomplexityFrom_le_of_computesFrom _
    (Circuit.Computes.takeDirectProductPrefix hc hsmall hle)).trans_eq
    (by rw [Circuit.cost_program_takeDirectProductPrefix])

/-- Applying the same input wiring independently in every block adds no weighted cost. -/
theorem ecomplexityFrom_directProduct_comp_wiring_le {p : ℕ} (select : Fin n → Fin p) (k : ℕ) :
    ecomplexityFrom I cost (directProduct (fun x => f (x ∘ select)) k) id ≤
      ecomplexityFrom I cost (directProduct f k) id := by
  refine le_ecomplexityFrom_iff.mpr fun c hc => ?_
  change c.Computes I (directProduct f k) at hc
  let wiring := Circuit.wiring σ fun i : Fin (k * n) =>
    finProdFinEquiv ((finProdFinEquiv.symm i).1, select (finProdFinEquiv.symm i).2)
  have h : (c.comp wiring).ComputesFrom I (directProduct (fun x => f (x ∘ select)) k) id := by
    intro x
    rw [Circuit.eval_comp, hc]
    funext j
    apply congrArg f
    funext i
    simp only [directProductInput, wiring, Circuit.eval_wiring, Function.comp_apply,
      Equiv.symm_apply_apply, id_eq]
  exact (ecomplexityFrom_le_of_computesFrom _ h).trans_eq
    (by rw [Circuit.cost_program_comp, Circuit.cost_program_wiring, Nat.zero_add])

/-- Minimum direct-product size is monotone in the number of copies, including zero copies. -/
theorem complexity_directProduct_mono [I.IsComplete] {small large : ℕ} (hle : small ≤ large) :
    complexity I (directProduct f small) ≤ complexity I (directProduct f large) := by
  rcases small.eq_zero_or_pos with rfl | hsmall
  · exact (complexity_le_of_computes (Circuit.wiring σ (Fin.elim0 : Fin 0 → Fin (0 * n)))
      fun _ => funext fun i => i.elim0).trans (by simp)
  obtain ⟨c, hc, hsize⟩ :=
    exists_computes_size_eq_complexity (I := I) (f := directProduct f large)
  refine (complexity_le_of_computes _ (hc.takeDirectProductPrefix hsmall hle)).trans_eq ?_
  simp [Circuit.takeDirectProductPrefix, hsize]

/-- One copy costs no more than a single-output implementation. -/
theorem complexity_directProduct_one_le [I.IsComplete] :
    complexity I (directProduct f 1) ≤ complexity I (single f) := by
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := I) (f := single f)
  refine (complexity_le_of_computes (c.comp (Circuit.wiring σ fun i => finProdFinEquiv (0, i)))
    fun x => ?_).trans_eq (by simp [hsize])
  rw [Circuit.eval_comp, hc]
  funext j
  rw [Subsingleton.elim j 0]
  rfl

end Cslib.Circuits

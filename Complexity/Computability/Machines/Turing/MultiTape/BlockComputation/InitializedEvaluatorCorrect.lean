/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluator
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitializerBounds
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteEvaluatorCorrect

/-!
# Initialized same-input evaluation of the encoded block tree

The fixed machine selects its packing parameters, allocates its actual padded bank one cell
per clock, and enters the concrete evaluator. Its final bank decodes to the existing encoded
tree's root. Every physical clock in both phases is covered by an explicit allowance. Outer
time and schedule search and the standard Turing-machine compilation remain separate tasks.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.InitializedEvaluator

open Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- The active branch preserves all physical evaluator clocks. -/
theorem runFrom_inr (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (state : ConcreteEvaluator.State k Q) (t : ℕ) :
    (machine M e).runFrom w (.inr state) t =
      .inr ((ConcreteEvaluator.machine M e).runFrom w state t) := by
  have hstep (q : ConcreteEvaluator.State k Q) :
      (machine M e).step w (.inr q) = .inr ((ConcreteEvaluator.machine M e).step w q) := by
    simp only [QueryMachine.step, QueryMachine.read, machine, Sum.elim_inr]
    by_cases h : (ConcreteEvaluator.machine M e).halted q = true <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte]
  induction t with
  | zero => rfl
  | succ t ih => rw [QueryMachine.runFrom_succ, ih, hstep, QueryMachine.runFrom_succ]

/-- Initialization is reproduced clock for clock through the last allocation. -/
theorem runFrom_initializer_prefix (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (args : Initializer.Args) (w : List Bool) (j : ℕ)
    (hj : j ≤ Initializer.bankCells k ((Initializer.prepare k s args).1)) :
    (machine M e).runFrom w (start k s args) j =
      .inl ((Initializer.machine k).runFrom w (Initializer.prepare k s args) j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hjlt : j < Initializer.bankCells k ((Initializer.prepare k s args).1) := by omega
    have hhalt : (Initializer.machine k).halted
        ((Initializer.machine k).runFrom w (Initializer.prepare k s args) j) = false := by
      change (Initializer.machine k).halted ((Initializer.machine k).runFrom w
        ((Initializer.prepare k s args).1, 0, [], 1) j) = false
      rw [Initializer.runFrom_prefix k ((Initializer.prepare k s args).1) w j hjlt.le]
      change decide (Initializer.bankCells k ((Initializer.prepare k s args).1) ≤ j) = false
      exact decide_eq_false (by omega)
    rw [QueryMachine.runFrom_succ, ih (by omega), QueryMachine.runFrom_succ]
    change (if (Initializer.machine k).halted
      ((Initializer.machine k).runFrom w (Initializer.prepare k s args) j) then _ else _) = _
    rw [hhalt]
    rw [QueryMachine.step, hhalt]
    rfl

/-- The clock after the final allocation enters the concrete evaluator on the completed bank. -/
theorem runFrom_entry (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (N b σ q : ℕ) (w : List Bool) :
    let cells := ((k * 3 + 1) + 1) * chunkCount (k * 3 + 1) (Encoding.width k s b)
    (machine M e).runFrom w (start k s (N, b, σ, q)) (cells + 1) =
      .inr (resume k ((Initializer.machine k).runFrom w
        (Initializer.prepare k s (N, b, σ, q)) cells)) := by
  dsimp only
  rw [QueryMachine.runFrom_succ, runFrom_initializer_prefix M e (N, b, σ, q) w
    (((k * 3 + 1) + 1) * chunkCount (k * 3 + 1) (Encoding.width k s b)) le_rfl]
  change (if (Initializer.machine k).halted
    ((Initializer.machine k).runFrom w (Initializer.prepare k s (N, b, σ, q))
      (((k * 3 + 1) + 1) * chunkCount (k * 3 + 1) (Encoding.width k s b))) then _ else _) = _
  simp only [Initializer.halted_prepare, ↓reduceIte]

/-- One metadata-only allowance covers initialization and every evaluator subroutine clock. -/
@[expose] noncomputable def allowance (k s : ℕ) (Q : Type) (N b σ q : ℕ) : ℕ :=
  let d := k * 3 + 1
  let B := Encoding.width k s b
  let m := chunkWidth d B
  let r := chunkCount d B
  let p := fieldModulus d B
  let limit := (2 ^ m) ^ (d * r)
  let ctx : ConcreteSupplier.Context := (N, b, σ, q, m, 2 ^ m, limit)
  Initializer.space k ((Initializer.prepare k s (N, b, σ, q)).1) +
    RawController.Query.queryStateBound (ConcreteSupplier.encContext ctx).length p d r q
      (ConcreteSupplier.replySpace k s Q N b σ q m (2 ^ m) limit p d r) + 2

/-- A phase handoff combines the actual initializer and evaluator storage bounds. -/
theorem length_runFrom_entry_le [Finite Q]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (args : Initializer.Args)
    (w : List Bool) (active : ConcreteEvaluator.State k Q) (T C : ℕ)
    (hentry : (machine M e).runFrom w (start k s args)
      (Initializer.bankCells k ((Initializer.prepare k s args).1) + 1) = .inr active)
    (hspace : ∀ u ≤ T,
      (ConcreteEvaluator.encState ((ConcreteEvaluator.machine M e).runFrom w active u)).length ≤ C)
    (t : ℕ) (ht : t ≤ Initializer.bankCells k ((Initializer.prepare k s args).1) + 1 + T) :
    (encState ((machine M e).runFrom w (start k s args) t)).length ≤
      Initializer.space k ((Initializer.prepare k s args).1) + C + 2 := by
  let cells := Initializer.bankCells k ((Initializer.prepare k s args).1)
  by_cases hinit : t ≤ cells
  · have hbound : (Initializer.encState ((Initializer.machine k).runFrom w
        (Initializer.prepare k s args) t)).length ≤
        Initializer.space k ((Initializer.prepare k s args).1) :=
      Initializer.length_runFrom_prepare_le k s args w t hinit
    rw [runFrom_initializer_prefix M e args w t hinit]
    change (Initializer.encState ((Initializer.machine k).runFrom w
      (Initializer.prepare k s args) t)).length + 1 ≤ _
    omega
  · have htge : cells + 1 ≤ t := by omega
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le htge
    have hu : u ≤ T := by change cells + 1 + u ≤ cells + 1 + T at ht; omega
    rw [QueryMachine.runFrom_add, hentry, runFrom_inr]
    have hbound := hspace u hu
    change (ConcreteEvaluator.encState
      ((ConcreteEvaluator.machine M e).runFrom w active u)).length + 1 ≤ _
    omega

/-- Native initialization followed by concrete evaluation returns the existing encoded tree's
root, with selected packing and field hypotheses discharged internally. -/
theorem exists_runFrom_decode_root [Finite Q] (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ q : ℕ) :
    let d := k * 3 + 1
    let B := Encoding.width k s b
    let m := chunkWidth d B
    let r := chunkCount d B
    let p := fieldModulus d B
    let ctx : ConcreteSupplier.Context := (w.length, b, σ, q, m, 2 ^ m, (2 ^ m) ^ (d * r))
    ∃ clock bank,
      (machine M e).runFrom w (start k s (w.length, b, σ, q)) clock =
        .inr (.inl (ctx, (p, d, r), bank, [], none)) ∧
      RawController.Output.decode ((B, m, p, r, 0), bank) =
        List.ofFn (encodedTree (MultiTapePTM.ofDeterministic M) w b
          (scheduleOfNat k q σ) e).eval ∧
      (machine M e).halted
        ((machine M e).runFrom w (start k s (w.length, b, σ, q)) clock) = true ∧
      ∀ t ≤ clock,
        (encState ((machine M e).runFrom w (start k s (w.length, b, σ, q)) t)).length ≤
          allowance k s Q w.length b σ q := by
  classical
  let d := k * 3 + 1
  let B := Encoding.width k s b
  let m := chunkWidth d B
  let r := chunkCount d B
  let p := fieldModulus d B
  let limit := (2 ^ m) ^ (d * r)
  let ctx : ConcreteSupplier.Context := (w.length, b, σ, q, m, 2 ^ m, limit)
  let cells := (d + 1) * r
  have hd : 0 < d := by dsimp only [d]; omega
  have hB : 0 < B := Encoding.width_pos k s b
  have hm : 0 < m := chunkWidth_pos hd hB
  have hb : Encoding.width k s b ≤ r * m := le_chunkCount_mul hd hB
  have hsp : 2 ^ m ≤ p := (alphabetSize_lt hd hB).le
  have hp : Fact p.Prime := ⟨fieldModulus_prime d B⟩
  have hcapacity : r ≤ ((2 ^ m) ^ (d * r)).size := by
    rw [← pow_mul, Nat.size_pow]
    have hmr : r ≤ m * (d * r) := by
      have := Nat.mul_le_mul_right r (Nat.mul_pos hm hd)
      nlinarith
    omega
  obtain ⟨T, bank, hrun, hdecode, hspace⟩ := ConcreteEvaluator.exists_runFrom_decode_root
    (q := q) M e w b σ hcapacity hb hm hsp (alphabetEmbedding hd hB) (fun _ => rfl)
    (gateDegree_lt d B) (0 : Cslib.TreeEval.Ary.State (ZMod p) d r) 0 rfl
  have hentry : (machine M e).runFrom w (start k s (w.length, b, σ, q)) (cells + 1) =
      .inr (.inl (ctx, (p, d, r), RawController.ofCfg
        (Iter.initialCfg (0 : Cslib.TreeEval.Ary.State (ZMod p) d r) 1 (0 : Fin (d + 1))))) := by
    rw [runFrom_entry]
    unfold resume
    rw [Initializer.result_runFrom_prepare]
  have hafter (u : ℕ) :
      (machine M e).runFrom w (start k s (w.length, b, σ, q)) ((cells + 1) + u) =
        .inr ((ConcreteEvaluator.machine M e).runFrom w
          (.inl (ctx, (p, d, r), RawController.ofCfg
            (Iter.initialCfg (0 : Cslib.TreeEval.Ary.State (ZMod p) d r) 1 0))) u) := by
    rw [QueryMachine.runFrom_add, hentry, runFrom_inr]
  refine ⟨cells + 1 + T, bank, ?_, hdecode, ?_, ?_⟩
  · rw [hafter, hrun]
  · rw [hafter, hrun]
    change !RawController.validBank p d r bank || (true && true) = true
    simp
  · exact length_runFrom_entry_le M e (w.length, b, σ, q) w
      (.inl (ctx, (p, d, r), RawController.ofCfg
        (Iter.initialCfg (0 : Cslib.TreeEval.Ary.State (ZMod p) d r) 1 0))) T
      (RawController.Query.queryStateBound (ConcreteSupplier.encContext ctx).length
        p d r q (ConcreteSupplier.replySpace k s Q w.length b σ q m (2 ^ m)
          limit p d r)) hentry hspace

end Turing.MultiTapePTM.BlockComputation.InitializedEvaluator

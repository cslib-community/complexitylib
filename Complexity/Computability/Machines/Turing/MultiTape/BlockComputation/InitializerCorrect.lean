/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Initializer
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerZero

/-!
# Exact native initialization of the raw evaluator

Each physical clock appends one modulus-padded zero cell. The assignment capacity is grown
only during the child-register portion of the bank. The completed state is exactly the
existing raw encoding of the typed evaluator's zero-bank initial configuration.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Initializer

open Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed

/-- Number of padded cells in the complete runtime bank. -/
@[expose] def bankCells (k : ℕ) (metadata : Metadata) : ℕ :=
  let (_, (_, r, _, _)) := metadata
  ((k * 3 + 1) + 1) * r

/-- The exact bank and capacity accumulated after a specified number of allocation clocks. -/
@[expose] def prefixState (k : ℕ) (metadata : Metadata) (j : ℕ) : State :=
  let (_, (_, r, alphabet, p)) := metadata
  (metadata, j, List.replicate j p, alphabet ^ min j ((k * 3 + 1) * r))

/-- Every prefix uses exactly one physical clock per allocated padded cell. -/
theorem runFrom_prefix (k : ℕ) (metadata : Metadata) (w : List Bool) (j : ℕ)
    (hj : j ≤ bankCells k metadata) :
    (machine k).runFrom w (metadata, 0, [], 1) j = prefixState k metadata j := by
  rcases metadata with ⟨args, m, r, alphabet, p⟩
  dsimp only [bankCells] at hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have hjtotal : j < ((k * 3 + 1) + 1) * r := by omega
    rw [QueryMachine.runFrom_succ, ih (by omega)]
    have hhalt : (machine k).halted (prefixState k (args, m, r, alphabet, p) j) = false := by
      change decide (((k * 3 + 1) + 1) * r ≤ j) = false
      exact decide_eq_false (by omega)
    rw [QueryMachine.step, hhalt]
    change step k (prefixState k (args, m, r, alphabet, p) j) =
      prefixState k (args, m, r, alphabet, p) (j + 1)
    simp only [step, prefixState, hjtotal, ↓reduceIte]
    by_cases hchild : j < (k * 3 + 1) * r
    · have hjle : j ≤ (k * 3 + 1) * r := hchild.le
      have hsuccle : j + 1 ≤ (k * 3 + 1) * r := by omega
      simp only [hchild, ↓reduceIte, Nat.min_eq_left hjle, Nat.min_eq_left hsuccle,
        pow_succ, List.replicate_succ']
    · have hle : (k * 3 + 1) * r ≤ j := by omega
      have hlesucc : (k * 3 + 1) * r ≤ j + 1 := by omega
      simp only [hchild, ↓reduceIte, Nat.min_eq_right hle, Nat.min_eq_right hlesucc,
        List.replicate_succ']

/-- The last allocation clock produces exactly the full bank and assignment capacity. -/
theorem runFrom_complete (k : ℕ) (args : Args) (m r alphabet p : ℕ) (w : List Bool) :
    (machine k).runFrom w ((args, m, r, alphabet, p), 0, [], 1)
      (((k * 3 + 1) + 1) * r) =
      ((args, m, r, alphabet, p), ((k * 3 + 1) + 1) * r,
        List.replicate (((k * 3 + 1) + 1) * r) p, alphabet ^ ((k * 3 + 1) * r)) := by
  rw [runFrom_prefix k (args, m, r, alphabet, p) w (((k * 3 + 1) + 1) * r) le_rfl]
  have hle : (k * 3 + 1) * r ≤ ((k * 3 + 1) + 1) * r :=
    Nat.mul_le_mul_right r (Nat.le_succ _)
  simp only [prefixState, Nat.min_eq_right hle]

/-- Completion is a true halt, including the empty-bank edge case. -/
theorem halted_complete (k : ℕ) (args : Args) (m r alphabet p : ℕ) (w : List Bool) :
    (machine k).halted ((machine k).runFrom w ((args, m, r, alphabet, p), 0, [], 1)
      (((k * 3 + 1) + 1) * r)) = true := by
  rw [runFrom_complete]
  change decide (((k * 3 + 1) + 1) * r ≤ ((k * 3 + 1) + 1) * r) = true
  exact decide_eq_true le_rfl

/-- Reading the completed generic allocation gives exactly the typed zero-bank initial call. -/
theorem result_runFrom_complete {p : ℕ} [Fact p.Prime]
    (k N b σ q m r alphabet : ℕ) (w : List Bool) :
    result k ((machine k).runFrom w (((N, b, σ, q), m, r, alphabet, p), 0, [], 1)
      (((k * 3 + 1) + 1) * r)) =
      ((N, b, σ, q, m, alphabet, alphabet ^ ((k * 3 + 1) * r)),
        (p, k * 3 + 1, r), RawController.ofCfg
          (Iter.initialCfg (0 : Cslib.TreeEval.Ary.State (ZMod p) (k * 3 + 1) r)
            1 (0 : Fin ((k * 3 + 1) + 1)))) := by
  rw [runFrom_complete, RawController.ofCfg_initial_zero]
  rfl

/-- Runtime selection and streamed initialization recover the existing evaluator's actual
selected-field initial configuration, with the complete assignment capacity retained. -/
theorem result_runFrom_prepare (k s N b σ q : ℕ) (w : List Bool) :
    let d := k * 3 + 1
    let B := Encoding.width k s b
    let m := chunkWidth d B
    let r := chunkCount d B
    let alphabet := 2 ^ m
    let p := fieldModulus d B
    result k ((machine k).runFrom w (prepare k s (N, b, σ, q)) ((d + 1) * r)) =
      ((N, b, σ, q, m, alphabet, alphabet ^ (d * r)), (p, d, r),
        RawController.ofCfg (Iter.initialCfg
          (0 : Cslib.TreeEval.Ary.State (ZMod p) d r) 1 (0 : Fin (d + 1)))) := by
  have : Fact (fieldModulus (k * 3 + 1) (Encoding.width k s b)).Prime :=
    ⟨fieldModulus_prime _ _⟩
  exact result_runFrom_complete k N b σ q _ _ _ w

/-- The selected initializer halts at the exact full-bank allocation clock. -/
theorem halted_prepare (k s N b σ q : ℕ) (w : List Bool) :
    (machine k).halted ((machine k).runFrom w (prepare k s (N, b, σ, q))
      (((k * 3 + 1) + 1) * chunkCount (k * 3 + 1) (Encoding.width k s b))) = true :=
  halted_complete k (N, b, σ, q) _ _ _ _ w

end Turing.MultiTapePTM.BlockComputation.Initializer

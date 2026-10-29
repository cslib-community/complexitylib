/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.CircuitCounting
import Complexity.Computability.Circuit.Boolean.Iteration.CounterBatch
import Complexity.Computability.Circuit.Boolean.Iteration.InPlace
import Complexity.Computability.Circuit.Boolean.Iteration.ModulusCounter
import Complexity.Computability.Circuit.Boolean.Iteration.Optimization
import Complexity.Computability.Circuit.Boolean.Iteration.Permutation
import Complexity.Computability.Circuit.Boolean.Iteration.PrimeCycles
import Complexity.Computability.Circuit.Boolean.Iteration.SequentialSquaring
import Complexity.Computability.Circuit.Boolean.Iteration.UniversalMap
import Complexity.Computability.Circuit.Boolean.Iteration.VisitScheduleCircuits

/-!
# Fixed-power circuit clients

Exercise the word circuits on a two-bit adder and table selection, the residue correction on a
concrete repeat, record collisions, and the fixed-power theorems on a bit-flip circuit, on
zero-width states, on an empty and a singleton invariant set, through an encoding of a type in
a higher universe, and for permutation inversion and periodicity.
-/

namespace ComplexityTests.Iteration

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration

/-! ### Words -/

-- A two-bit ripple-carry adder on the first two and last two inputs, from the shared carries.
example : ∃ c : Circuit signature 4 2,
    c.Computes interpretation (fun x i =>
      (word (fun j : Fin 2 => x ⟨j, by omega⟩) +
        word (fun j : Fin 2 => x ⟨j + 2, by omega⟩)).getLsbD i.val) ∧ c.size ≤ 25 :=
  (Synthesis.word_add (s := inputs 4) (fun x => word fun j : Fin 2 => x ⟨j, by omega⟩)
    (fun x => word fun j : Fin 2 => x ⟨j + 2, by omega⟩)
    (fun i => ⟨⟨i, by omega⟩, funext fun x =>
      (getLsbD_word (fun j : Fin 2 => x ⟨j, by omega⟩) i).symm⟩)
    (fun i => ⟨⟨i + 2, by omega⟩, funext fun x =>
      (getLsbD_word (fun j : Fin 2 => x ⟨j + 2, by omega⟩) i).symm⟩)).exists_circuit_outputs

-- Table selection is exact in range, all-false out of range, and never selects positions beyond
-- the index range.
example :
    selectBits (BitVec.ofNat 2 1) ![![true, false], ![false, true]] = ![false, true] ∧
    selectBits (BitVec.ofNat 2 3) ![![true, false], ![false, true]] = ![false, false] ∧
    selectBits (BitVec.ofNat 1 0) ![![true, false], ![false, false], ![false, true]] =
      ![true, false] := by
  decide

/-! ### Residues and records -/

-- An orbit repeating between times 2 and 5: time 10 is the time 4 in `[2, 5)`, and equal states
-- collide unless a record is padding or both are identical.
example :
    (repeatWordIndex 10 5 (BitVec.ofNat 3 2) (BitVec.ofNat 3 5)).toNat = 4 ∧
    Record.collision (Record.query (n := 1) (w := 2) ![true] 0)
      (Record.stored ![true] ![false]) = true ∧
    Record.collision (Record.query (n := 1) (w := 2) ![true] 0)
      (Record.query ![true] 0) = false ∧
    Record.collision (Record.pad (n := 1) (w := 2)) Record.pad = false := by
  decide

/-! ### Fixed powers -/

/-- The one-bit negation circuit. -/
private def flip : Circuit signature 1 1 :=
  ⟨.gate .empty ⟨.not, fun _ => .input 0⟩, fun _ => .gate 0⟩

private theorem eval_flip (x : BitString 1) : flip.eval interpretation x = fun _ => !x 0 := by
  funext i
  fin_cases i
  rfl

-- Every power of the flip has a circuit within the bound at `L = 1`.
example (T : ℕ) : ∃ out : Circuit signature 1 1,
    out.Computes interpretation (flip.eval interpretation)^[T] ∧
      out.size ≤ 40000 * powerBudget 1 1 2 1 := by
  simpa [flip] using fixed_power 1 flip T 1 one_pos (by decide)

-- Zero-width states: `L = 1 = 2 ^ 0` is the only parameter.
example (c : Circuit signature 0 0) (T : ℕ) : ∃ out : Circuit signature 0 0,
    out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 40000 * (c.size + 3) := by
  simpa [powerBudget] using fixed_power 0 c T 1 one_pos le_rfl

-- The empty invariant set needs no checkpoint storage.
example (c : Circuit signature 2 2) (T : ℕ) : ∃ out : Circuit signature 2 2,
    out.ComputesOn interpretation ↑(∅ : Finset (BitString 2)) (c.eval interpretation)^[T] ∧
      out.size ≤ 40000 * powerBudget 2 c.size 0 1 :=
  fixed_power_on 2 c ∅ T 1 (by simp) one_pos (by decide)

-- A singleton invariant set: a fixed point stores at most one checkpoint.
example (c : Circuit signature 2 2) (h : c.eval interpretation ![false, false] = ![false, false])
    (T : ℕ) : ∃ out : Circuit signature 2 2,
      out.ComputesOn interpretation ↑({![false, false]} : Finset (BitString 2))
        (c.eval interpretation)^[T] ∧ out.size ≤ 40000 * powerBudget 2 c.size 1 1 :=
  fixed_power_on 2 c {![false, false]} T 1 (by simpa using h) one_pos (by decide)

/-! ### Encodings, permutations and periodicity -/

-- States in a higher universe, encoded by one bit.
example (T : ℕ) : ∃ out : Circuit signature 1 1,
    (∀ x ∈ (Finset.univ : Finset (ULift.{1} Bool)),
      out.eval interpretation (fun _ => x.down) = fun _ => (id^[T] x).down) ∧
    out.size ≤ 40000 * powerBudget 1 0 2 1 := by
  simpa using fixed_power_encoded (n := 1) id Finset.univ
    (fun (x : ULift.{1} Bool) (_ : Fin 1) => x.down)
    (fun _ _ _ _ h => ULift.ext (congrFun h 0)) (Circuit.id signature 1)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl) T 1 one_pos (by decide)

/-- Negation as a permutation of one-bit states. -/
private def flipPerm : Equiv.Perm (BitString 1) where
  toFun x := fun _ => !x 0
  invFun x := fun _ => !x 0
  left_inv x := funext fun i => by fin_cases i; simp
  right_inv x := funext fun i => by fin_cases i; simp

-- The flip's inverse, through the factorial exponent.
example : ∃ out : Circuit signature 1 1,
    out.Computes interpretation flipPerm.symm ∧ out.size ≤ 40000 * powerBudget 1 1 2 1 := by
  simpa [flip] using permutation_inverse flip flipPerm (fun x => eval_flip x) 1 one_pos (by decide)

-- Every state is periodic for the flip.
example : ∃ out : Circuit signature 1 1,
    (∀ x, out.eval interpretation x 0 = true ↔
      x ∈ Function.periodicPts (flip.eval interpretation)) ∧
    out.size ≤ 40000 * powerBudget 1 1 2 1 + 7 := by
  simpa [flip] using periodicPts_circuit flip 1 one_pos (by decide)

-- The half-exponential closed form.
example (c : Circuit signature 3 3) (T : ℕ) : ∃ out : Circuit signature 3 3,
    out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 120000 * (c.size + 64) * 4 := by
  simpa using fixed_power_half_exponent c T

/-! ### Universal step map, in-place machines, and sequential squaring -/

-- Zero-gate (`G = 0`), exact (`G = 1`), and padded (`G = 3 > flip.size`) rounds of the universal
-- map simulate `Circuit.id` and `flip`.
example (x : BitString 1) :
    (Universal.step interpretation)^[0 + 1]
      (Universal.start (Universal.describe 0 (Circuit.id signature 1) .not) x) =
    Universal.start (Universal.describe 0 (Circuit.id signature 1) .not)
      ((Circuit.id signature 1).eval interpretation x) ∧
    (Universal.step interpretation)^[1 + 1]
      (Universal.start (Universal.describe 1 flip .not) x) =
    Universal.start (Universal.describe 1 flip .not) (flip.eval interpretation x) ∧
    (Universal.step interpretation)^[3 + 1]
      (Universal.start (Universal.describe 3 flip .not) x) =
    Universal.start (Universal.describe 3 flip .not) (flip.eval interpretation x) :=
  ⟨Universal.step_round interpretation (Circuit.id signature 1) .not le_rfl x,
   Universal.step_round interpretation flip .not le_rfl x,
   Universal.step_round interpretation flip .not (by decide) x⟩

-- Concrete instantiation of `Universal.universal_power_circuit` for `T = 1` on `flip`.
example : ∃ d : Circuit signature 1 1,
    d.Computes interpretation (flip.eval interpretation)^[1] ∧ d.size ≤ flip.size + 2 :=
  Universal.universal_power_circuit flip .not le_rfl (fun s => s.x) Sum.inl id (fun _ => rfl)
    (fun _ => rfl) 1 flip (fun x =>
      (congrArg Universal.Config.x
        (Universal.step_iterate interpretation flip .not le_rfl 1 x)).symm)

/-- A 1-head halting in-place machine on `Bool` tape with one absorbing state `Unit`. -/
private def idleMachine : InPlace.Machine Unit Bool 1 where
  δ q r _ _ := (q, r, fun _ => .stay)
  start := ()
  halting _ := True
  embed := id

private theorem idleMachine_absorbing : idleMachine.HaltingAbsorbing :=
  fun _ _ _ _ _ => rfl

example : (InPlace.reach idleMachine 2).card ≤ 8 := by
  simpa using InPlace.reach_card_le_configs idleMachine (n := 2)

example (z : InPlace.Config Unit Bool 2 1) :
    idleMachine.step^[Fintype.card (InPlace.Config Unit Bool 2 1)] z = z :=
  ((InPlace.iterate_card_halting idleMachine idleMachine_absorbing z).2 0 trivial)

private theorem injOn_config_one {h : ℕ} (M : InPlace.Machine Unit Bool h) :
    Set.InjOn (fun z : InPlace.Config Unit Bool 1 h => z.1) (InPlace.reach M 1) := by
  intro z₁ _ z₂ _ h1
  exact Prod.ext h1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

-- Concrete instantiation of `InPlace.inplace_halting` on `idleMachine`.
example : ∃ (out : Circuit signature 1 1) (final : BitString 1 → InPlace.Config Unit Bool 1 1),
    (∀ x, out.eval interpretation x = (final x).1 ∧
      (idleMachine.halting (final x).2.2 ↔
        ∃ t, idleMachine.halting (idleMachine.step^[t] (idleMachine.init x)).2.2) ∧
      ∀ t, idleMachine.halting (idleMachine.step^[t] (idleMachine.init x)).2.2 →
        final x = idleMachine.step^[t] (idleMachine.init x)) ∧
    (out.size : ℝ) ≤ (Circuit.id signature 1).size + 120000 * optimizedBudget 1 0 2 := by
  simpa using InPlace.inplace_halting idleMachine idleMachine_absorbing (fun z => z.1)
    (injOn_config_one idleMachine) (Circuit.id signature 1)
    (fun z _ => by rw [InPlace.Machine.step_of_halting idleMachine_absorbing z trivial]; rfl)
    (Circuit.id signature 1) (fun _ => rfl)

/-- A 2-head 1-cell machine where head 0 writes `false` and moves `.left`, while head 1 writes
`!r 1` and moves `.right`. On a 1-cell tape both moves clamp to `0`, and head 1's write wins. -/
private def collideMachine : InPlace.Machine Unit Bool 2 where
  δ q r _ _ := (q, ![false, !r 1], ![.left, .right])
  start := ()
  halting _ := False
  embed := id

private theorem collideMachine_step (z : InPlace.Config Unit Bool 1 2) :
    collideMachine.step z = (fun _ => !z.1 0, fun _ => 0, ()) := by
  refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  funext i
  fin_cases i
  have hp0 : z.2.1 0 = 0 := Subsingleton.elim _ _
  have hp1 : z.2.1 1 = 0 := Subsingleton.elim _ _
  simp [collideMachine, InPlace.Machine.step, InPlace.writeHeads, Fin.foldl_succ_last,
    Fin.foldl_zero, hp1]

private theorem collideMachine_round (x : BitString 1) :
    collideMachine.step^[1] (collideMachine.init x) =
      collideMachine.init (flip.eval interpretation x) := by
  rw [Function.iterate_one, collideMachine_step]
  simp [InPlace.Machine.init, collideMachine, eval_flip]

-- Concrete instantiation of `InPlace.inplace_configs_optimized` and `InPlace.round_bounds_of_hard`
-- on the 2-head colliding/clamping machine `collideMachine`.
example (T : ℕ) : ∃ out : Circuit signature 1 1,
    (∀ x, out.eval interpretation x = (collideMachine.step^[T] (collideMachine.init x)).1) ∧
    (out.size : ℝ) ≤ (Circuit.id signature 1).size + 120000 * optimizedBudget 1 flip.size 2 := by
  simpa using InPlace.inplace_configs_optimized collideMachine (fun z => z.1)
    (injOn_config_one collideMachine) flip
    (fun z _ => by rw [collideMachine_step, eval_flip])
    (Circuit.id signature 1) (fun _ => rfl) T

example (q : ℕ)
    (hhard : ∀ d : Circuit signature 1 1,
      d.Computes interpretation (flip.eval interpretation)^[1] → q < d.size) :
    (∀ out : Circuit signature 1 1,
      (∀ x, out.eval interpretation x = (collideMachine.step^[1 * 1] (collideMachine.init x)).1) →
      q < out.size) ∧
    ∀ T', ∃ out : Circuit signature 1 1,
      (∀ x, out.eval interpretation x = (collideMachine.step^[T'] (collideMachine.init x)).1) ∧
      (out.size : ℝ) ≤ (Circuit.id signature 1).size + 120000 * optimizedBudget 1 flip.size 2 := by
  simpa using InPlace.round_bounds_of_hard collideMachine 1 1 q one_pos (flip.eval interpretation)
    collideMachine_round (fun z => z.1) (injOn_config_one collideMachine) id (fun _ => rfl) hhard
    flip (fun z _ => by rw [collideMachine_step, eval_flip]) (Circuit.id signature 1) (fun _ => rfl)

-- Sequential squaring modulo `M = 1`, at `T = 0`, and on a non-unit residue modulo `M = 15`.
private theorem squarefree_15 : Squarefree (15 : ℕ) := by
  rintro (_ | _ | _ | _ | d) ⟨k, hk⟩
  · omega
  · exact isUnit_one
  · omega
  · omega
  · rcases k with _ | k
    · omega
    · nlinarith

-- `3 : ZMod 15` is a non-unit, yet satisfies `pow_carmichael_succ` and `iterate_square_reduced`
-- (including at `T = 0`, alongside `M = 1`).
example (T : ℕ) (x : ZMod 15) :
    (fun y : ZMod 1 => y ^ 2)^[T] (0 : ZMod 1) =
      (0 : ZMod 1) ^ SequentialSquaring.reducedExponent 1 T ∧
    ¬ IsUnit (3 : ZMod 15) ∧
    (3 : ZMod 15) ^ (SequentialSquaring.carmichael 15 + 1) = (3 : ZMod 15) ∧
    (fun y : ZMod 15 => y ^ 2)^[0] (3 : ZMod 15) =
      (3 : ZMod 15) ^ SequentialSquaring.reducedExponent 15 0 ∧
    (fun y : ZMod 15 => y ^ 2)^[T] x = x ^ SequentialSquaring.reducedExponent 15 T := by
  refine ⟨SequentialSquaring.iterate_square_reduced squarefree_one T 0, ?_,
    SequentialSquaring.pow_carmichael_succ squarefree_15 3,
    SequentialSquaring.iterate_square_reduced squarefree_15 0 3,
    SequentialSquaring.iterate_square_reduced squarefree_15 T x⟩
  rintro ⟨u, hu⟩
  have h := congrArg (fun z : ZMod 15 => (5 : ZMod 15) * z) hu
  have h0 : (5 : ZMod 15) * 3 = 0 := by decide
  have h5 : (5 : ZMod 15) ≠ 0 := by decide
  have hu0 : (5 : ZMod 15) * (u : ZMod 15) = 0 := h.trans h0
  exact h5 ((Units.mul_left_eq_zero u).mp hu0)

-- Non-squarefree boundary (`M = 4`): `x ^ (λ(4) + 1) = x` fails at the nilpotent residue `2`.
example :
    ¬ Squarefree (4 : ℕ) ∧
    (2 : ZMod 4) ^ (SequentialSquaring.carmichael 4 + 1) ≠ (2 : ZMod 4) := by
  refine ⟨fun h => ?_, ?_⟩
  · have h2 := Nat.isUnit_iff.mp (h 2 ⟨1, by ring⟩)
    omega
  · obtain ⟨k, hk⟩ : ∃ k, SequentialSquaring.carmichael 4 + 1 = k + 2 :=
      ⟨SequentialSquaring.carmichael 4 - 1, by
        have := SequentialSquaring.carmichael_pos 4
        omega⟩
    rw [hk, pow_add, show (2 : ZMod 4) ^ 2 = 0 by decide, mul_zero]
    decide

/-! ### Compressed-forest reachability, hitting time, and visit schedules -/

-- Nonvacuous forest tables for the one-bit negation circuit at `L = 1`.
example : Nonempty (ForestCircuitTables (flip.eval interpretation) 1) :=
  exists_forest_circuit_tables (flip.eval interpretation) 1 one_pos

-- Reachability circuit for `flip` at `L = 1`.
example : ∃ out : Circuit signature 2 1,
    (∀ z, out.eval interpretation z 0 = true ↔
      ∃ t, (flip.eval interpretation)^[t] (inputLeft z) = inputRight z) ∧
    out.size ≤ 4500000 * powerBudget 1 1 2 1 := by
  simpa [flip] using forest_reachability_circuit flip 1 one_pos (by decide)

-- Navigation circuit (reachability + first hitting time) for `flip` at `L = 1`.
example : ∃ out : Circuit signature 2 3,
    out.Computes interpretation (fun z =>
      navigationBits (flip.eval interpretation) (inputLeft z) (inputRight z)) ∧
    out.size ≤ navigationBudget 1 1 1 := by
  simpa [flip] using navigation_circuit flip 1 one_pos (by decide)

-- Minimal period circuit for `flip` at `L = 1`.
example : ∃ out : Circuit signature 1 2,
    (∀ x, (word (out.eval interpretation x)).toNat =
      Function.minimalPeriod (flip.eval interpretation) x) ∧
    out.size ≤ 110000 * powerBudget 1 1 2 1 := by
  simpa [flip] using minimal_period_circuit flip 1 one_pos (by decide)

-- Complete visit-schedule circuit for `flip` at `L = 1`.
example : ∃ out : Circuit signature 2 (visitScheduleWidth 1),
    (∀ z t, (flip.eval interpretation)^[t] (inputLeft z) = inputRight z ↔
      visitScheduleContains (out.eval interpretation z) t) ∧
    out.size ≤ 5000000 * powerBudget 1 1 2 1 := by
  simpa [flip] using visit_schedule_circuit flip 1 one_pos (by decide)

/-! ### Hard-power counting, modular counters and prime-cycle permutations -/

-- Linear-size circuit for the 2-bit modular-counter step, exponential lower bound and density of
-- hard powers for the 64-bit modular counter, and least common multiple bound below 5.
example :
    (∃ c : Circuit signature (2 + 2) (2 + 2),
      c.Computes interpretation (counterStep 2) ∧ c.size ≤ 50 * 2 + 20) ∧
    (∃ c : Circuit signature (64 + 64) (64 + 64),
      c.size ≤ 50 * (64 + 1) ∧ Function.Bijective (c.eval interpretation) ∧
      ∃ T < ModulusCounter.period 64,
        ∀ out : Circuit signature (64 + 64) (64 + 64),
          out.Computes interpretation (c.eval interpretation)^[T] →
            2 ^ 64 / (1024 * (64 + 1)) < out.size) ∧
    (easyCounterPowers 64 (lowerBudget 64)).card * 2 ^ (2 ^ (64 - 1)) ≤
      ModulusCounter.period 64 ∧
    lcmBelow 5 < 4 ^ 5 :=
  ⟨counterStep_circuit 2,
   counter_power_lower_bound 64 (by decide),
   almost_all_counter_powers_hard 64 (by decide),
   lcmBelow_lt_four_pow 5 (by decide)⟩

/-- Non-vacuous concrete `PrimeCycleData` instance from the hash-class construction. -/
noncomputable def samplePrimeCycleData : PrimeCycleData 1 3 :=
  PrimeCycleData.ofHash 1 1 (fun _ => 0) (fun _ => by decide)

example : Function.Bijective samplePrimeCycleData.step :=
  samplePrimeCycleData.step_bijective

-- Batched modular-counter power for r = 2 blocks of width 2 * 2 = 4, plus empty-batch (r = 0) and
-- zero-width (k = 0) boundary cases.
example (T k : ℕ) :
    (∃ out : Circuit signature (2 * (2 + 2)) (2 * (2 + 2)),
      out.Computes interpretation (counterBatchPower T) ∧
        out.size ≤ 40000 * (2 + 1) ^ 3 * (2 ^ 2 + 2)) ∧
    (∃ out : Circuit signature (0 * (k + k)) (0 * (k + k)),
      out.Computes interpretation (counterBatchPower (r := 0) (k := k) T) ∧
        out.size ≤ 40000 * (k + 1) ^ 3 * (2 ^ k + 0)) ∧
    (∃ out : Circuit signature (1 * (0 + 0)) (1 * (0 + 0)),
      out.Computes interpretation (counterBatchPower (r := 1) (k := 0) T) ∧
        out.size ≤ 40000 * (0 + 1) ^ 3 * (2 ^ 0 + 1)) :=
  ⟨batched_counter_power T 2 (by decide),
   batched_counter_power T 0 (Nat.zero_le _),
   batched_counter_power T 1 (by decide)⟩

/-- Two-block `2 * (2 + 2)`-bit state with active block 0 `(modulus = 3, residue = 2)` and
inactive zero-modulus block 1 `(modulus = 0, residue = 1)`. -/
def sampleTwoBlockState : BitString (2 * (2 + 2)) :=
  fun i =>
    if (finProdFinEquiv.symm i).1 = 0 then
      ModulusCounter.pack (3 : BitVec 2) (2 : BitVec 2) (finProdFinEquiv.symm i).2
    else
      ModulusCounter.pack (0 : BitVec 2) (1 : BitVec 2) (finProdFinEquiv.symm i).2

-- Block 0 advances from residue 2 by T = 2 modulo 3 to residue 1, while block 1 (modulus 0)
-- stays fixed at residue 1.
example :
    counterBlock (counterBatchPower (r := 2) (k := 2) 2 sampleTwoBlockState) 0 =
      ModulusCounter.pack (3 : BitVec 2) (1 : BitVec 2) ∧
    counterBlock (counterBatchPower (r := 2) (k := 2) 2 sampleTwoBlockState) 1 =
      ModulusCounter.pack (0 : BitVec 2) (1 : BitVec 2) := by
  constructor <;> funext b <;> revert b <;> decide

-- Concrete nonidentity proof for `ModulusCounter.power (k := 2) 1` and instantiation of the
-- `r ≤ c.size` bound (`counterBatch_size_ge_of_ne_id` and `counterBatch_lower_bounds`).
theorem power_one_two_ne_id : ModulusCounter.power (k := 2) 1 ≠ id := by
  intro h
  have hbit := congrFun (congrFun h (ModulusCounter.pack (2 : BitVec 2) (0 : BitVec 2)))
    (Fin.natAdd 2 ⟨0, by decide⟩)
  revert hbit
  decide

example (c : Circuit signature (2 * (2 + 2)) (2 * (2 + 2)))
    (hc : c.Computes interpretation (counterBatchPower (r := 2) (k := 2) 1)) :
    (∃ out : Circuit signature (2 + 2) (2 + 2),
      out.Computes interpretation (ModulusCounter.power 1) ∧ out.size ≤ c.size) ∧
    2 ≤ c.size := by
  obtain ⟨hsingle, _⟩ := counterBatch_lower_bounds 1 two_pos c hc
  exact ⟨hsingle, counterBatch_size_ge_of_ne_id 1 power_one_two_ne_id c hc⟩

-- The combined theorem also supplies its independent per-block lower-bound route.
example (c : Circuit signature (2 * (2 + 2)) (2 * (2 + 2)))
    (hc : c.Computes interpretation (counterBatchPower (r := 2) (k := 2) 1)) :
    2 ≤ c.size := by
  obtain ⟨_, hbatch⟩ := counterBatch_lower_bounds 1 two_pos c hc
  exact hbatch power_one_two_ne_id

-- Combined upper and lower bounds for batched hard counter powers at k = 64.
example :
    ∃ T < ModulusCounter.period 64, ∀ r, 0 < r → r ≤ 2 ^ (64 + 64) →
      (∃ out : Circuit signature (r * (64 + 64)) (r * (64 + 64)),
        out.Computes interpretation (counterBatchPower T) ∧
          out.size ≤ 40000 * (64 + 1) ^ 3 * (2 ^ 64 + r)) ∧
      ∀ c : Circuit signature (r * (64 + 64)) (r * (64 + 64)),
        c.Computes interpretation (counterBatchPower T) →
          lowerBudget 64 < c.size ∧ r ≤ c.size :=
  batched_hard_counter_power 64 (by decide)

end ComplexityTests.Iteration

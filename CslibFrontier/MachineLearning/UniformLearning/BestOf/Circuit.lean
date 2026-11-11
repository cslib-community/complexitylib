/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Circuit.Boolean.PopulationCount
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Circuit.Boolean.Tournament
import CslibFrontier.Computability.Circuit.Complexity

/-!
# Circuits for best-of-`k` selection

Best-of-`k` selection (`Cslib.MachineLearning.UniformLearning.QueryLearner.bestOf`) outputs the
hypothesis of a run with the most agreements with the target on `t` sample points, the first such
run on ties (`QueryLearner.selectBest`, `QueryLearner.agreeCount_le_selectBest`,
`QueryLearner.agreeCount_lt_selectBest`). This file computes that choice by a circuit.

For each of the `k` hypotheses, an exclusive or per sample point marks the disagreements with the
target, and a population count (`Cslib.Circuits.Boolean.populationCountCircuit`) numbers them. The
record of hypothesis `j` is that number followed by its value at the point to classify. A
tournament of keyed minimums (`Cslib.Circuits.Boolean.exists_complexity_tournament_le`) outputs
the first record with the fewest disagreements, which is the record of the first hypothesis with
the most agreements. The selection costs `t (A + B + 4) + 463 (t + 1) + C` gates per hypothesis
beyond `k - 1` keyed minimums of `8 (⌈log₂ (t + 1)⌉ + 1) + 5` gates, when the values of the
hypotheses at the sample points cost at most `A`, those of the target `B`, and those of the
hypotheses at the point to classify `C` (`QueryLearner.exists_complexity_select_le`).

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.exists_complexity_select_le`: a circuit
  outputs the value of the first hypothesis with the most agreements.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets and A. Kolokolova,
  *Learning Algorithms from Natural Proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016],
  Theorem 2.11, p. 10:9 (the confidence boosting step).
-/

public section

namespace Cslib.MachineLearning.UniformLearning.QueryLearner

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.BitString Finset

variable {k t : ℕ}

/-- **Selecting the first best of `k` hypotheses by a circuit.** Let `v j i` be the value of
hypothesis `j` at sample point `i`, `y i` the value of the target there, and `h j` the value of
hypothesis `j` at the point to classify, all functions of the inputs. Some function outputs, on
every input, the value `h s` of the first hypothesis `s` with the most agreements `v s i = y i`. It
costs at most `t (A + B + 4) + 463 (t + 1) + C` per hypothesis, for the exclusive ors and the
population count of its disagreements and for its value, and `k - 1` keyed minimums. -/
theorem exists_complexity_select_le [NeZero k] {N : ℕ} (v : Fin k → Fin t → BooleanFunction N)
    (y : Fin t → BooleanFunction N) (h : Fin k → BooleanFunction N) {A B C : ℕ}
    (hv : ∀ j i, complexity interpretation (single (v j i)) ≤ A)
    (hy : ∀ i, complexity interpretation (single (y i)) ≤ B)
    (hh : ∀ j, complexity interpretation (single (h j)) ≤ C) :
    ∃ g : BooleanFunction N,
      complexity interpretation (single g) ≤
        k * (t * (A + B + 4) + 463 * (t + 1) + C) +
          (k - 1) * (8 * (Nat.clog 2 (t + 1) + 1) + 5) ∧
      ∀ z s, (∀ j, #{i | v j i z = y i z} ≤ #{i | v s i z = y i z}) →
        (∀ j < s, #{i | v j i z = y i z} < #{i | v s i z = y i z}) → g z = h s z := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := NeZero.ne k; omega⟩
  -- The record of hypothesis `j`: the number of its disagreements, then its value.
  let r : Fin (m + 1) → BitString N → BitString (Nat.clog 2 (t + 1) + 1 + 1) := fun j z =>
    Fin.append ((populationCountCircuit t).eval interpretation fun i => v j i z ^^ y i z)
      (single (h j) z)
  obtain ⟨G, hG, hsel⟩ := exists_complexity_tournament_le (k := Nat.clog 2 (t + 1) + 1) (p := 1) r
  refine ⟨fun z => G z (Fin.natAdd _ 0), ?_, fun z s hle hlt => ?_⟩
  · have hr : ∀ j, complexity interpretation (r j) ≤ t * (A + B + 4) + 463 * (t + 1) + C := by
      intro j
      refine (complexity_append_le _ _).trans (Nat.add_le_add ?_ (hh j))
      refine (complexity_comp_le (fun z i => v j i z ^^ y i z)
        ((populationCountCircuit t).eval interpretation)).trans (Nat.add_le_add ?_
          ((complexity_le_of_computes _ fun _ => rfl).trans (size_populationCountCircuit_le t)))
      refine (complexity_pi_le fun i z => v j i z ^^ y i z).trans ?_
      refine (Finset.sum_le_sum fun i _ => (complexity_xor_le _ _).trans
        (Nat.add_le_add_right (Nat.add_le_add (hv j i) (hy i)) 4)).trans ?_
      simp
    have hwire := complexity_comp_le (I := interpretation) G
      (fun u : BitString (Nat.clog 2 (t + 1) + 1 + 1) => u ∘ fun _ : Fin 1 => Fin.natAdd _ 0)
    rw [complexity_wiring, add_zero] at hwire
    calc complexity interpretation (single fun z => G z (Fin.natAdd _ 0))
        ≤ complexity interpretation G := hwire
      _ ≤ ∑ j, complexity interpretation (r j) + m * (8 * (Nat.clog 2 (t + 1) + 1) + 3 * 1 + 2) :=
        hG
      _ ≤ ∑ _j : Fin (m + 1), (t * (A + B + 4) + 463 * (t + 1) + C) +
          m * (8 * (Nat.clog 2 (t + 1) + 1) + 3 * 1 + 2) :=
        Nat.add_le_add_right (Finset.sum_le_sum fun j _ => hr j) _
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.add_sub_cancel]
  · -- The disagreements and the agreements of hypothesis `j` add up to `t`.
    have hcount : ∀ j, weight (fun i => v j i z ^^ y i z) + #{i | v j i z = y i z} = t := by
      intro j
      have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin t)))
        (fun i => v j i z = y i z)
      rw [card_univ, Fintype.card_fin] at hsplit
      have hw : weight (fun i => v j i z ^^ y i z) = #{i | ¬v j i z = y i z} := by
        exact congrArg Finset.card (Finset.filter_congr fun i _ => by
          change (v j i z ^^ y i z) = true ↔ _
          cases v j i z <;> cases y i z <;> decide)
      omega
    have hkey : ∀ j, (equivFin (Nat.clog 2 (t + 1) + 1) (recordKey (r j z)) : ℕ) =
        weight (fun i => v j i z ^^ y i z) := fun j => by
      simp only [r, recordKey, fstBits_append]
      exact val_eval_populationCountCircuit t _
    have hrs : G z = r s z := hsel z s
      (fun j => by
        rw [Fin.le_iff_val_le_val, hkey, hkey]
        have := hcount s; have := hcount j; have := hle j
        omega)
      (fun j hj => by
        rw [Fin.lt_def, hkey, hkey]
        have := hcount s; have := hcount j; have := hlt j hj
        omega)
    simp only [hrs, r, Fin.append_right, single_apply]

end Cslib.MachineLearning.UniformLearning.QueryLearner

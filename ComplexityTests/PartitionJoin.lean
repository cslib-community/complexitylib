/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

import Complexity.Computability.Communication.PartitionJoin

/-! Tests for the join matrix of the partition lattice and the communication bound for joining
partitions: the Möbius values `c(b)` for small `b`; `μ(x, ⊤)` through Mathlib's incidence algebra,
with the locally finite order of a finite type, at the one-block and the discrete partition of three
points; entries of the join matrix that are `1` and `0`; full rank over `ℚ` and over `ℝ`, with the
`Fintype` instance from `Fintype.ofFinite`, also for the empty type; the count `B_4 ≥ 4`; and the
resulting bound of two bits for joining partitions of four points. -/

namespace ComplexityTests.PartitionJoin

open Cslib Cslib.SetPartition Cslib.Communication

-- $c(b) = (-1)^{b-1} (b-1)!$ for the first few $b$.
example : derivCoeff 1 = 1 := derivCoeff_one
example : derivCoeff 2 = -1 := by simp [derivCoeff_succ]
example : derivCoeff 3 = 2 := by simp [derivCoeff_succ, Nat.factorial]
example : derivCoeff 4 = -6 := by simp [derivCoeff_succ, Nat.factorial]

-- Sums and ranks over the partitions use the `Fintype` instance from `Finite`.
noncomputable local instance (n : ℕ) : Fintype (Setoid (Fin n)) := Fintype.ofFinite _

section Mu

open Classical in
noncomputable local instance : LocallyFiniteOrder (Setoid (Fin 3)) :=
  Fintype.toLocallyFiniteOrder

open Classical in
-- Mathlib's Möbius function, with the locally finite order of a finite order, at the top.
example (x : Setoid (Fin 3)) : IncidenceAlgebra.mu ℤ x ⊤ = derivCoeff (blocks x) :=
  mu_top x

open Classical in
-- $\mu(\top, \top) = c(1) = 1$.
example : IncidenceAlgebra.mu ℤ (⊤ : Setoid (Fin 3)) ⊤ = 1 := by
  rw [mu_top, blocks_eq_one_iff.mpr rfl, derivCoeff_one]

open Classical in
-- $\mu(\bot, \top) = c(3) = 2$ on three points.
example : IncidenceAlgebra.mu ℤ (⊥ : Setoid (Fin 3)) ⊤ = 2 := by
  rw [mu_top, blocks_bot, Nat.card_fin]
  simp [derivCoeff_succ, Nat.factorial]

end Mu

-- The join matrix has a `1` where the join is the one-block partition, and a `0` where both
-- partitions are discrete on two points.
example : joinMatrix ℚ (Fin 2) ⊤ ⊥ = 1 := by simp
example : joinMatrix ℚ (Fin 2) ⊥ ⊥ = 0 := by
  have h : (⊥ : Setoid (Fin 2)) ≠ ⊤ := fun h => by
    have : (⊤ : Setoid (Fin 2)) 0 1 := trivial
    rw [← h, Setoid.bot_def] at this
    exact absurd this (by decide)
  simp [h]

-- The join matrix is nonsingular, over `ℚ` and over `ℝ`, and also for the empty type.
example : (joinMatrix ℚ (Fin 3)).rank = Nat.card (Setoid (Fin 3)) := rank_joinMatrix
example : (joinMatrix ℝ (Fin 3)).rank = Nat.card (Setoid (Fin 3)) := rank_joinMatrix
example : (joinMatrix ℚ (Fin 0)).rank = 1 := by
  rw [rank_joinMatrix, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun _ _ => Setoid.ext fun a => a.elim0⟩, ⟨⊥⟩⟩

-- There are at least $2^2 = 4$ partitions of four points (in fact $15$).
example : 4 ≤ Nat.card (Setoid (Fin 4)) := by
  simpa using pow_le_card_setoid (N := 4) (j := 2) (by norm_num)

open Classical in
-- So joining partitions of four points needs two bits.
example : (2 : ℕ∞) ≤ Protocol.ecomplexity
    (fun P Q : Setoid (Fin 4) => fun b => decide (P ⊔ Q = ⊤) = b) Set.univ Set.univ := by
  refine le_trans ?_ (clog_card_le_ecomplexity_join (α := Fin 4))
  have : 4 ≤ Nat.card (Setoid (Fin 4)) := by
    simpa using pow_le_card_setoid (N := 4) (j := 2) (by norm_num)
  have h := Nat.clog_mono_right 2 this
  rw [show 4 = 2 ^ 2 from rfl, Nat.clog_pow 2 2 (by norm_num)] at h
  exact_mod_cast h

end ComplexityTests.PartitionJoin

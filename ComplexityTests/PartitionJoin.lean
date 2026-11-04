/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

import Complexity.Computability.Communication.PartitionJoin

/-! Tests for the join matrix of the partition lattice and the communication bound for joining
partitions: the Möbius values `c(b)` for small `b`, `μ(x, ⊤)` through Mathlib's incidence algebra
with the locally finite order of a finite type, entries of the join matrix that are `1` and `0`,
the count `B_4 ≥ 4`, and the resulting bound of two bits for joining partitions of
four points. -/

namespace ComplexityTests.PartitionJoin

open Cslib Cslib.SetPartition Cslib.Communication

-- `c(b) = (-1)^(b-1) (b-1)!` for the first few `b`.
example : derivCoeff 1 = 1 := derivCoeff_one
example : derivCoeff 2 = -1 := by simp [derivCoeff_succ]
example : derivCoeff 3 = 2 := by simp [derivCoeff_succ, Nat.factorial]
example : derivCoeff 4 = -6 := by simp [derivCoeff_succ, Nat.factorial]

-- The Möbius function of Mathlib's incidence algebra, with the locally finite order that every
-- finite order carries, takes these values at the top.
section Mu

open Classical in
noncomputable local instance : LocallyFiniteOrder (Setoid (Fin 3)) :=
  Fintype.toLocallyFiniteOrder

open Classical in
example (x : Setoid (Fin 3)) : IncidenceAlgebra.mu ℤ x ⊤ = derivCoeff (blocks x) :=
  mu_top x

end Mu

-- On the one-block partition, `μ(⊤, ⊤) = c(1) = 1`.
example : blocks (⊤ : Setoid (Fin 3)) = 1 := blocks_eq_one_iff.mpr rfl

-- The join matrix has a `1` where the join is the one-block partition, and a `0` where both
-- partitions are discrete on two points.
example : joinMatrix (Fin 2) ⊤ ⊥ = 1 := by simp
example : joinMatrix (Fin 2) ⊥ ⊥ = 0 := by
  have h : (⊥ : Setoid (Fin 2)) ≠ ⊤ := fun h => by
    have : (⊤ : Setoid (Fin 2)) 0 1 := trivial
    rw [← h, Setoid.bot_def] at this
    exact absurd this (by decide)
  simp [h]

-- The join matrix is nonsingular.
example : (joinMatrix (Fin 3)).rank = Fintype.card (Setoid (Fin 3)) := rank_joinMatrix

-- There are at least `2 ^ 2 = 4` partitions of four points (in fact `15`).
example : 4 ≤ Fintype.card (Setoid (Fin 4)) := by
  simpa using pow_le_card_setoid (N := 4) (j := 2) (by norm_num)

-- So joining partitions of four points needs two bits.
open Classical in
example : (2 : ℕ∞) ≤ Protocol.ecomplexity
    (fun P Q : Setoid (Fin 4) => fun b => decide (P ⊔ Q = ⊤) = b) Set.univ Set.univ := by
  classical
  refine le_trans ?_ (clog_card_le_ecomplexity_join (α := Fin 4))
  have : 4 ≤ Fintype.card (Setoid (Fin 4)) := by
    simpa using pow_le_card_setoid (N := 4) (j := 2) (by norm_num)
  have h := Nat.clog_mono_right 2 this
  rw [show 4 = 2 ^ 2 from rfl, Nat.clog_pow 2 2 (by norm_num)] at h
  exact_mod_cast h

end ComplexityTests.PartitionJoin

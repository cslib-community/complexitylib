/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Monotone.BipartiteMatching

/-!
# Bipartite perfect matching

Small instances of the bipartite perfect matching function, the graphs of the Raz–Wigderson
reduction on concrete sizes (Alice's has a perfect matching and Bob's has none, so the game
instances are genuine), and a concrete consequence of the linear depth bound: monotone formulas
for bipartite perfect matching on `2 ^ 20 + 2 ^ 20` vertices have depth at least `126`.
-/

namespace ComplexityTests.BipartiteMatching

open Cslib Cslib.Circuits Cslib.Circuits.BipartiteMatching Cslib.Communication

/-! ### The function -/

-- The complete bipartite graph `K_{3,3}` has a perfect matching, the empty graph has none,
-- `bipartitePerfectMatching 4` is monotone, and Hall's theorem characterizes `K_{2,2}` graphs.
example :
    bipartitePerfectMatching 3 (fun _ => true) = true ∧
      bipartitePerfectMatching 3 (fun _ => false) = false ∧
      Monotone (bipartitePerfectMatching 4) ∧
      ¬HasPerfectMatching (fun _ : Fin 2 × Fin 2 => false) ∧
      HasPerfectMatching (fun e : Fin 2 × Fin 2 => decide (e ≠ (0, 0))) := by
  refine ⟨bipartitePerfectMatching_eq_true_iff.mpr ⟨Equiv.refl _, fun _ => rfl⟩, ?_,
    monotone_bipartitePerfectMatching, ?_,
    (hasPerfectMatching_iff_forall_card_le _).2 (by decide)⟩
  · rw [Bool.eq_false_iff]
    rintro h
    obtain ⟨σ, hσ⟩ := bipartitePerfectMatching_eq_true_iff.mp h
    exact Bool.false_ne_true (hσ 0)
  · rw [hasPerfectMatching_iff_forall_card_le]
    intro h
    simpa using h {0}

/-! ### The graphs of the reduction -/

-- Alice's graph has a perfect matching, Bob's graph has none, and the matching edges at `b₀` and
-- `b₂` are missing from Bob's graph when `x = y = {1, 2}` and `i₀ = 0`.
example :
    HasPerfectMatching (RazWigderson.aliceGraph (e := 1) (![true, false, true] : BitString 3)) ∧
      ¬HasPerfectMatching (RazWigderson.bobGraph (e := 1) (1 : Fin 3) ![false, true, true]) ∧
      RazWigderson.aliceGraph (e := 0) (![false, true, true] : BitString 3)
        (.inl (.inl 2), RazWigderson.aliceMatching ![false, true, true] (.inl (.inl 2))) = true ∧
      RazWigderson.bobGraph (e := 0) (0 : Fin 3) ![false, true, true]
        (.inl (.inl 2), RazWigderson.aliceMatching ![false, true, true] (.inl (.inl 2))) =
          false :=
  ⟨RazWigderson.hasPerfectMatching_aliceGraph _,
    RazWigderson.not_hasPerfectMatching_bobGraph _ _,
    by decide⟩

/-! ### Lower bounds -/

-- Public-coin communication reduction from disjointness, finiteness of monotone formula depth,
-- and the concrete depth lower bound `126 ≤ eformulaDepth (bipartitePerfectMatching (2 ^ 20))`.
example :
    PublicCoin.ecomplexityFun (1 / 2 ^ 1) (disjointness : BitString 1 → BitString 1 → Bool) ≤
      1 * (Protocol.ecomplexity ExceedsAt {x | bipartitePerfectMatching 2 x = true}
        {y | bipartitePerfectMatching 2 y = false} + 1) ∧
    Monotone.eformulaDepth (bipartitePerfectMatching (2 ^ 20)) ≠ ⊤ ∧
    (126 : ℕ∞) ≤ Monotone.eformulaDepth (bipartitePerfectMatching (2 ^ 20)) := by
  refine ⟨ecomplexityFun_disjointness_le_mul_ecomplexity_bipartitePerfectMatching (by norm_num)
    (by norm_num) (by norm_num),
    Monotone.eformulaDepth_ne_top_iff.2 monotone_bipartitePerfectMatching, ?_⟩
  have h := Monotone.le_mul_eformulaDepth_bipartitePerfectMatching_add (2 ^ 20)
  cases hd : Monotone.eformulaDepth (bipartitePerfectMatching (2 ^ 20)) using ENat.recTopCoe with
  | top => exact le_top
  | coe d =>
    rw [hd] at h
    have : 2 ^ 20 ≤ 2 ^ 13 * d + 2 ^ 14 := by exact_mod_cast h
    exact_mod_cast (show 126 ≤ d by omega)

end ComplexityTests.BipartiteMatching

/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.LabelingEvents
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.LabelingEstimate
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.TournamentCyclic

/-!
# Superquadratic sensitivity separation: labeling

A counting argument proves that good edge labelings exist. If `0 < r`, `120 ≤ k * k` and
`k ^ 16 < r ^ 104`, the bad labelings for sixteen vertices are fewer than all `r ^ (k * k)`
labelings, and any labeling avoiding them is good. Specializing to `k = 2 * M ^ 2 + 1` gives a good
labeling of the regular cyclic tournament with `Nat.ceil (Real.sqrt M)` labels for every `M ≥ 3`.

## Main results

* `regular_goodLabeling_exists`: the regular cyclic tournament has a good labeling with
  `Nat.ceil (Real.sqrt M)` labels for `3 ≤ M`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Labeling.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

namespace Tournament
variable {k r : ℕ} (T : Tournament k)

/-- If `A ∉ T.badLabelings n r`, then for every injective `v : Fin n → Fin k` and every
`m : Fin k → Fin r` there is an edge `v i → v j` of `T` with `A (v i, v j) ≠ m (v j)`. -/
private theorem labeled_edge_of_not_bad {n : ℕ} (A : (Fin k × Fin k) → Fin r)
    (hA : A ∉ T.badLabelings n r) (v : Fin n → Fin k)
    (hv : Function.Injective v) (m : Fin k → Fin r) :
    ∃ i j : Fin n, T.Adj (v i) (v j) ∧ A (v i, v j) ≠ m (v j) := by
  by_contra hn
  have hc : ∀ i j, T.Adj (v i) (v j) → A (v i, v j) = m (v j) := fun i j ha =>
    not_not.mp fun h => hn ⟨i, j, ha, h⟩
  have hevent := (T.mem_labelingEvent_iff hv).mpr hc
  exact hA (T.labelingEvent_subset_bad hevent)

/-- If `0 < r`, `120 ≤ k * k` and `k ^ 16 < r ^ 104`, then `T` admits a good labeling with `r`
labels. -/
private theorem goodLabeling_exists_of_power_bound (hr : 0 < r) (hN : 120 ≤ k * k)
    (hkr : k ^ 16 < r ^ 104) : Nonempty (GoodLabeling T r) := by
  have htotal : k ^ 16 * r ^ 16 * r ^ (k * k-120) < r ^ (k * k) := by
    calc
      k ^ 16 * r ^ 16 * r ^ (k * k-120) < r ^ 104 * r ^ 16 * r ^ (k * k-120) :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right hkr (pow_pos hr 16)) (pow_pos hr _)
      _ = r ^ (104 + 16 + (k * k-120)) := by rw [pow_add, pow_add]
      _ = r ^ (k * k) := congrArg (fun e : ℕ => r ^ e) (by omega)
  have hc : (T.badLabelings 16 r).card <
      (Finset.univ : Finset ((Fin k × Fin k) → Fin r)).card := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
      using (T.card_badLabelings_le (r := r) (n := 16)).trans_lt htotal
  obtain ⟨A,_,hA⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨⟨fun i j => A (i,j), ?_⟩⟩
  intro I hI m
  let e : Fin 16 ≃ I := (Finset.equivFinOfCardEq hI).symm
  let v : Fin 16 → Fin k := fun i => (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  obtain ⟨i, j, ha, hne⟩ := T.labeled_edge_of_not_bad A hA v hv m
  exact ⟨v i, (e i).property, v j, (e j).property, ha, hne⟩

end Tournament

/-- If `3 ≤ M` and `M ≤ r ^ 2`, then every tournament on `2 * M ^ 2 + 1` vertices admits a good
labeling with `r` labels. -/
private theorem goodLabeling_exists {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r ^ 2)
    (T : Tournament (2 * M ^ 2 + 1)) : Nonempty (GoodLabeling T r) := by
  have hr : 0 < r := (Nat.pow_pos_iff.mp
    (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
  exact T.goodLabeling_exists_of_power_bound hr (labeling_space_large hM)
    (labeling_power_bound hM hMr)

/-- For `3 ≤ M`, the regular cyclic tournament on `2 * M ^ 2 + 1` vertices admits a good labeling
with `Nat.ceil (Real.sqrt M)` labels. -/
theorem regular_goodLabeling_exists {M : ℕ} (hM : 3 ≤ M) :
    Nonempty (GoodLabeling (regularCyclicTournament M).toTournament
      (Nat.ceil (Real.sqrt M))) :=
  goodLabeling_exists hM (le_ceil_sqrt_sq M) _

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Correctness

/-!
# Deterministic edges throughout the compact configuration box

The guarded compact graph of a deterministic machine has at most one successor at every ID,
including invalid and unreachable IDs. This does not require a decoder or a represented-view
hypothesis. It follows directly from the fixed transition table and injective observation codes.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_target_unique`: target uniqueness for
  the compact graph of a deterministic machine.
* `Turing.MultiTapeNTM.ConfigurationGraph.sum_edgeWithSymbol_le_one`: each indicator row has
  total mass at most one, including rows truncated by the radix bound.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]

private theorem matchesEntry_observations {n : ℕ} {r : Register k → ℕ}
    {symbol : Option Bool} {a b : Instruction k State}
    (ha : matchesEntry n r symbol a = true) (hb : matchesEntry n r symbol b = true) :
    a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 := by
  simp only [matchesEntry, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_ofFn, id_eq] at ha hb
  refine ⟨Option.some.inj (stateCode_injective (ha.1.1.symm.trans hb.1.1)),
    ha.1.2.symm.trans hb.1.2, funext fun i => ?_⟩
  exact symbolCode_injective
    ((of_decide_eq_true (ha.2 _ ⟨i, rfl⟩)).symm.trans (of_decide_eq_true (hb.2 _ ⟨i, rfl⟩)))

/-- The compact graph of a deterministic machine has at most one target for each source and
supplied input symbol. The statement includes all IDs, with no validity or reachability premise. -/
theorem edgeWithSymbol_target_unique (tm : MultiTapeTM k Bool State)
    {B n u v z : ℕ} {symbol : Option Bool}
    (hv : edgeWithSymbol tm.toMultiTapeNTM B n u v symbol = true)
    (hz : edgeWithSymbol tm.toMultiTapeNTM B n u z symbol = true) : v = z := by
  simp only [edgeWithSymbol, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at hv hz
  rcases hv.2 with hv | ⟨a, ha, ⟨⟨hma, _⟩, hv⟩⟩
  · rcases hz.2 with hz | ⟨b, _, ⟨⟨hmb, _⟩, _⟩⟩
    · exact hv.2.trans hz.2.symm
    · simp only [matchesEntry, Bool.and_eq_true, decide_eq_true_eq] at hmb
      have h := stateCode_injective (hv.1.symm.trans hmb.1.1)
      cases h
  · rcases hz.2 with hz | ⟨b, hb, ⟨⟨hmb, _⟩, hz⟩⟩
    · simp only [matchesEntry, Bool.and_eq_true, decide_eq_true_eq] at hma
      have h := stateCode_injective (hz.1.symm.trans hma.1.1)
      cases h
    · obtain ⟨hq, hi, hw⟩ := matchesEntry_observations hma hmb
      have hta := MultiTapeTM.tr_iff.mp ((mem_instructions tm.toMultiTapeNTM a).mp ha)
      have htb := MultiTapeTM.tr_iff.mp ((mem_instructions tm.toMultiTapeNTM b).mp hb)
      rw [hq, hi, hw] at hta
      have haction := hta.symm.trans htb
      rw [haction] at hv
      exact hv.trans hz.symm

/-- Summing a deterministic edge indicator over the entire compact box gives at most one.
Invalid IDs and radix-overflowing transitions may give a row of zeros. -/
theorem sum_edgeWithSymbol_le_one (tm : MultiTapeTM k Bool State)
    (B n u : ℕ) (symbol : Option Bool) :
    ∑ v : Fin (vertexBound (k := k) B),
      (edgeWithSymbol tm.toMultiTapeNTM B n u v symbol).toNat ≤ 1 := by
  classical
  by_cases h : ∃ v : Fin (vertexBound (k := k) B),
      edgeWithSymbol tm.toMultiTapeNTM B n u v symbol = true
  · obtain ⟨v, hv⟩ := h
    rw [Finset.sum_eq_single v]
    · simp [hv]
    · intro z _ hz
      have he : edgeWithSymbol tm.toMultiTapeNTM B n u z symbol = false := by
        apply Bool.eq_false_iff.mpr
        intro he
        exact hz (Fin.ext (edgeWithSymbol_target_unique tm he hv))
      simp [he]
    · simp
  · have he (v : Fin (vertexBound (k := k) B)) :
        edgeWithSymbol tm.toMultiTapeNTM B n u v symbol = false :=
      Bool.eq_false_iff.mpr fun hv => h ⟨v, hv⟩
    simp [he]

end Turing.MultiTapeNTM.ConfigurationGraph

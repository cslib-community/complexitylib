/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Footprint
public import Complexity.Computability.WordRAM.ListOutput

/-!
# Output-size lower bounds for native word-RAM runs

Every changed memory cell costs a store instruction. The statements count changed cells rather
than output length alone: returning the initialized input is free apart from the halt. In
particular, materializing a nonzero dense `n × n` matrix in initially zero memory costs at least
`n²` continuing instructions, and returning a freshly materialized nonzero list costs its length
plus the halt. These are instruction-count bounds in the existing native memory-output model.

## Main results

* `Runs.card_changed_le`: a finite family of changed cells is bounded by the step count.
* `Runs.block_lowerBound`: every changed cell of an output block must be written.
* `ExecutesList.replicate_lowerBound`: a nonzero dense list returned from zero input requires
  at least its length plus one instructions, including the final halt.
* `ExecutesList.denseMatrix_lowerBound`: the square-output specialization.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-- Each distinct cell whose value changes requires its own store instruction. -/
theorem Runs.card_changed_le {w n : ℕ} {p : Program B r} {s t : State r}
    (h : Runs w p s t n) (S : Finset ℕ)
    (hchange : ∀ a ∈ S, t.data.mem a ≠ s.data.mem a) : S.card ≤ n := by
  obtain ⟨_, W, _, hW, hm, _⟩ := h.exists_footprints
  apply (Finset.card_le_card ?_).trans hW
  intro a ha
  by_contra hnot
  exact hchange a ha (hm a hnot)

/-- A dense output block costs at least one store per changed entry. -/
theorem Runs.block_lowerBound {w n : ℕ} {p : Program B r} {s t : State r}
    (h : Runs w p s t n) (b : Block)
    (hchange : ∀ i : Fin b.length, t.data.mem (b.base + i) ≠ s.data.mem (b.base + i)) :
    b.length ≤ n := by
  rw [← b.card_footprint]
  apply h.card_changed_le
  intro a ha
  obtain ⟨hlo, hhi⟩ := Block.mem_footprint.mp ha
  have he : b.base + (a - b.base) = a := by omega
  simpa only [he] using hchange ⟨a - b.base, by omega⟩

/-- Every positive-address cell of a zero-word input starts at zero, regardless of input length. -/
theorem Data.init_replicate_zero_mem {r m a : ℕ} (ha : 0 < a) :
    (Data.init (List.replicate m 0) : Data r).mem a = 0 := by
  simp only [Data.init, Nat.ne_of_gt ha, ↓reduceIte, List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split <;> rfl

/-- Returning a nonzero constant list from a zero-word input must materialize every entry.
The output pointer is unrestricted; its entries all lie at positive addresses, so none can
reuse the input-length header. The output-length header may require an additional store. -/
theorem ExecutesList.replicate_lowerBound {w m k n v : ℕ} {p : Program B r}
    (h : ExecutesList w p (.init (List.replicate m 0)) (List.replicate k v) n)
    (hv : v ≠ 0) : k + 1 ≤ n := by
  obtain ⟨t, steps, base, hr, _, hout, rfl⟩ := h
  have hl := (outputList_eq_iff.mp hout).2
  have hb : k ≤ steps := hr.block_lowerBound ⟨base + 1, k⟩ (by
    intro i
    have he := hl ⟨i.val, by simpa only [List.length_replicate] using i.isLt⟩
    change t.data.mem (base + 1 + i.val) = (List.replicate k v)[i.val] at he
    simp only [List.getElem_replicate] at he
    simpa only [he, State.init,
      Data.init_replicate_zero_mem (by omega : 0 < base + 1 + i.val)] using hv)
  omega

/-- Materializing the row-major all-one `n × n` matrix from initialized zero data has the
quadratic output-size barrier, even if the machine chooses its own output address. -/
theorem ExecutesList.denseMatrix_lowerBound {w m n steps : ℕ} {p : Program B r}
    (h : ExecutesList w p (.init (List.replicate m 0))
      (List.replicate (n * n) 1) steps) : n * n + 1 ≤ steps :=
  h.replicate_lowerBound (by decide)

end Cslib.WordRAM

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Reduction.TruthTable
import Mathlib.Data.List.Forall2

/-!
# Composing truth-table reductions

The composite of a truth-table reduction `(r, q, d)` from `L` to `B` and `(r', q', d')` from `B`
to `C` reserves, for each first-stage query `q (a, i)`, a block of `M a ≥ r' (q (a, i))`
consecutive positions starting at `i * M a` for its second-stage queries. It evaluates `d'` on
each block of answers and `d` on the results. This file states the correctness of that combiner
once, independently of the resource bound: polynomial-time and logspace clients choose their
own block size and composite query map, prove that they are computable, and apply
`mem_iff_truthTableCompCombiner`.

## Main definitions

* `Cslib.Complexity.truthTableCompCombiner`: the combiner of the composite reduction.

## Main results

* `Cslib.Complexity.mem_iff_truthTableCompCombiner`: the composite combiner decides `L` from the
  answers to the composite queries, provided block `i` of the composite queries lists the
  second-stage queries of `q (a, i)`.
* `Cslib.Complexity.truthTableCompCombiner_mono`: the composite combiner is monotone in the
  answers when both combiners are.
-/

public section

namespace Cslib.Complexity

variable {α β γ : Type} {L : Set α} {B : Set β} {C : Set γ}

/-- The combiner of a composite truth-table reduction: block `i` of the answer word, of length
`r' (q (a, i))` and starting at `i * M a`, is decided by `d'`, and `d` combines the `r a`
decisions. -/
@[expose] def truthTableCompCombiner (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool)
    (r' : β → ℕ) (d' : β × List Bool → Bool) (M : α → ℕ) (x : α × List Bool) : Bool :=
  d (x.1, (List.range (r x.1)).map fun i =>
    d' (q (x.1, i), (x.2.drop (i * M x.1)).take (r' (q (x.1, i)))))

/-- **Correctness of the composite combiner.** If block `i` of the composite queries `Q`, of
length `M a`, starts with the `r' (q (a, i))` second-stage queries of `q (a, i)`, then the
composite combiner decides `L` from the answers to the `r a * M a` composite queries. -/
theorem mem_iff_truthTableCompCombiner {r : α → ℕ} {q : α × ℕ → β}
    {d : α × List Bool → Bool} {r' : β → ℕ} {q' : β × ℕ → γ} {d' : β × List Bool → Bool}
    {M : α → ℕ} {Q : α × ℕ → γ}
    (hL : ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true)
    (hB : ∀ b, b ∈ B ↔ d' (b, truthTableAnswers (q' ⁻¹' C) r' b) = true)
    (hM : ∀ a, ∀ i < r a, r' (q (a, i)) ≤ M a)
    (hQ : ∀ a, ∀ i < r a, ∀ j < r' (q (a, i)), Q (a, i * M a + j) = q' (q (a, i), j)) (a : α) :
    a ∈ L ↔ truthTableCompCombiner r q d r' d' M
      (a, truthTableAnswers (Q ⁻¹' C) (fun a => r a * M a) a) = true := by
  classical
  rw [hL a, truthTableCompCombiner, truthTableAnswers_eq_map_range]
  dsimp only
  suffices hmap : ((List.range (r a)).map fun i => d' (q (a, i),
      ((truthTableAnswers (Q ⁻¹' C) (fun a => r a * M a) a).drop (i * M a)).take
        (r' (q (a, i))))) = (List.range (r a)).map fun i => decide ((a, i) ∈ q ⁻¹' B) by
    rw [hmap]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have hend : i * M a + r' (q (a, i)) ≤ r a * M a :=
    calc i * M a + r' (q (a, i)) ≤ i * M a + M a := Nat.add_le_add_left (hM a i hi) _
      _ = (i + 1) * M a := (Nat.succ_mul i (M a)).symm
      _ ≤ r a * M a := Nat.mul_le_mul_right _ hi
  have hblock : ((truthTableAnswers (Q ⁻¹' C) (fun a => r a * M a) a).drop (i * M a)).take
      (r' (q (a, i))) = truthTableAnswers (q' ⁻¹' C) r' (q (a, i)) := by
    refine List.ext_getElem (by simp only [List.length_take, List.length_drop,
      length_truthTableAnswers]; omega) fun j hj₁ hj₂ => ?_
    rw [length_truthTableAnswers] at hj₂
    simp [truthTableAnswers, hQ a i hi j hj₂]
  rw [hblock]
  cases h : d' (q (a, i), truthTableAnswers (q' ⁻¹' C) r' (q (a, i))) <;> simp [hB, h]

/-- The composite combiner is monotone in the answers when both combiners are. -/
theorem truthTableCompCombiner_mono {r : α → ℕ} {q : α × ℕ → β}
    {d : α × List Bool → Bool} {r' : β → ℕ} {d' : β × List Bool → Bool} {M : α → ℕ}
    (hd : ∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v))
    (hd' : ∀ b u v, List.Forall₂ (· ≤ ·) u v → d' (b, u) ≤ d' (b, v)) (a : α)
    (u v : List Bool) (huv : List.Forall₂ (· ≤ ·) u v) :
    truthTableCompCombiner r q d r' d' M (a, u) ≤ truthTableCompCombiner r q d r' d' M (a, v) := by
  refine hd _ _ _ ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun i _ => hd' _ _ _ ?_
  exact List.forall₂_take _ (List.forall₂_drop _ huv)

end Cslib.Complexity

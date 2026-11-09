/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Closure.Approximator
public import Complexity.Computability.Circuit.Monotone.Clique.Negative

/-!
# Negative errors of closed clique approximators

On the complete multipartite graph of a colouring `c` with `g` colours, a set of vertices has all
edges inside exactly when `c` is injective on it. Intersecting and joining families makes no
negative errors; only closing does. One closure step adds a set `W` implied by `r` members `V i` of
the family, and errs on `c` only when `c` is injective on `W` but on none of the `V i`. Equal
members would lie inside `W`, so the `V i` are distinct, and they meet only inside `W`: they form a
sunflower with core `W`, except that they need only meet inside the core. So one step errs on at
most `(l ^ 2) ^ r * g ^ (n - r)` colourings
(`Cslib.Circuits.Monotone.Negative.card_sunflowerBad_le`), the counting form of
[Alon and Boppana, Lemma 3.6][AlonBoppana1987].

The closure takes at most as many steps as there are sets of at most `l` vertices
(`Cslib.Circuits.Monotone.Closure.relatesInSteps_closure`). Alon and Boppana bound the number of
steps of their closure algorithm more sharply, by `2 r ^ l` (their Lemma 3.5), but note that the
cruder bound suffices.

## Main definitions

* `Cslib.Circuits.Monotone.Closure.Negative.errorCap`,
  `Cslib.Circuits.Monotone.Closure.Negative.exceptions`: the per-gate negative error cap and the
  negative exceptions of a gate.
* `Cslib.Circuits.Monotone.Closure.Negative.scheme`: the approximation scheme on multipartite
  graphs.

## Main results

* `Cslib.Circuits.Monotone.Closure.Negative.card_stepExceptions_closure_le`: the negative errors of
  closing a family.

## References

* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*][AlonBoppana1987]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone.Closure.Negative

open Cslib.Circuits.Clique Finset Relation Cslib.Circuits.Monotone.Closure.Approximator
open Cslib.Circuits.Monotone.Negative (stepExceptions mem_stepExceptions stepExceptions_subset
  card_sunflowerBad_le pluckErrorCap)

variable {n g r l : ℕ}

/-- One closure step makes at most `pluckErrorCap n g r l` negative errors. -/
theorem card_stepExceptions_le_of_step {F G : Finset (Finset (Fin n))} (h : Step r l F G)
    (hF : ∀ s ∈ F, s.card ≤ l) : (stepExceptions g F G).card ≤ pluckErrorCap n g r l := by
  classical
  obtain ⟨W, -, ⟨-, ⟨V, hV, hVW⟩ | ⟨-, V, hV, hV1⟩⟩, rfl⟩ := h
  · have hexc (c) (hc : c ∈ stepExceptions g F (insert W F)) :
        Set.InjOn c W ∧ ∀ i, ¬Set.InjOn c (V i) := by
      obtain ⟨⟨t, ht, hct⟩, hF'⟩ := mem_stepExceptions.1 hc
      rcases mem_insert.1 ht with rfl | ht
      · exact ⟨contains_ofColoring_iff.1 hct,
          fun i hi => hF' ⟨V i, hV i, contains_ofColoring_iff.2 hi⟩⟩
      · exact absurd ⟨t, ht, hct⟩ hF'
    by_cases hinj : Function.Injective V
    · refine (card_le_card fun c hc => ?_).trans (card_sunflowerBad_le (S := univ.image V)
        (K := W) ?_ ?_ fun s hs => ?_)
      · obtain ⟨hcW, hcV⟩ := hexc c hc
        refine mem_filter.2 ⟨mem_univ _, hcW, fun s hs => ?_⟩
        obtain ⟨i, -, rfl⟩ := mem_image.1 hs
        exact hcV i
      · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
      · rintro s hs t ht hst
        obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hs)
        obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_coe.1 ht)
        exact hVW i j fun hij => hst (hij ▸ rfl)
      · obtain ⟨i, -, rfl⟩ := mem_image.1 hs
        exact hF _ (hV i)
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, hij, hne⟩ := hinj
      have hViW : V i ⊆ W := by simpa [← hij] using hVW i j hne
      refine (card_eq_zero.2 (eq_empty_of_forall_notMem fun c hc => ?_)).trans_le (Nat.zero_le _)
      obtain ⟨hcW, hcV⟩ := hexc c hc
      exact hcV i (hcW.mono hViW)
  · refine (card_eq_zero.2 (eq_empty_of_forall_notMem fun c hc => ?_)).trans_le (Nat.zero_le _)
    exact (mem_stepExceptions.1 hc).2 ⟨V, hV, contains_of_card_le_one _ hV1⟩

/-- `m` closure steps make at most `m` times `pluckErrorCap n g r l` negative errors. -/
theorem card_stepExceptions_le_of_relatesInSteps {F G : Finset (Finset (Fin n))} {m : ℕ}
    (h : RelatesInSteps (Step r l) F G m) (hF : ∀ s ∈ F, s.card ≤ l) :
    (stepExceptions g F G).card ≤ m * pluckErrorCap n g r l := by
  induction h with
  | refl => simp [stepExceptions]
  | tail G H m hFG hGH ih =>
    calc (stepExceptions g F H).card
        ≤ (stepExceptions g F G ∪ stepExceptions g G H).card :=
          card_le_card (stepExceptions_subset g F G H)
      _ ≤ m * pluckErrorCap n g r l + pluckErrorCap n g r l :=
          (card_union_le _ _).trans (Nat.add_le_add ih (card_stepExceptions_le_of_step hGH
            (forall_card_le_of_relatesInSteps_step hFG hF)))
      _ = (m + 1) * pluckErrorCap n g r l := (Nat.succ_mul _ _).symm

/-- The number of negative errors charged to any gate. -/
def errorCap (n g r l : ℕ) : ℕ :=
  (smallSets n l).card * pluckErrorCap n g r l

/-- Closing a family of sets of at most `l` vertices makes at most `errorCap n g r l` negative
errors. -/
theorem card_stepExceptions_closure_le {F : Finset (Finset (Fin n))} (hF : ∀ s ∈ F, s.card ≤ l) :
    (stepExceptions g F (closure r l F)).card ≤ errorCap n g r l :=
  let ⟨_, hm, h⟩ := relatesInSteps_closure (r := r) (l := l) F
  (card_stepExceptions_le_of_relatesInSteps h hF).trans (Nat.mul_le_mul_right _ hm)

/-- The negative errors of a gate: those of closing the family produced at the gate. -/
noncomputable def exceptions (g : ℕ) (op : Op) (A : Fin (signature.Arity op) → Approximator n r l) :
    Finset (Coloring n g) :=
  stepExceptions g (Approximator.gateTerms op fun i => (A i).terms)
    (closure r l (Approximator.gateTerms op fun i => (A i).terms))

/-- Away from its exceptions, a gate is negatively correct on multipartite graphs. -/
theorem gate_correct (op : Op) (A : Fin (signature.Arity op) → Approximator n r l)
    (c : Coloring n g) (hc : c ∉ exceptions g op A) :
    (Approximator.interpretation op A).decode (ofColoring c) ≤
      Monotone.interpretation op fun i => (A i).decode (ofColoring c) := by
  rw [Bool.le_iff_imp, decode_eq_true, terms_interpretation]
  intro h
  have hG : Accepts (Approximator.gateTerms op fun i => (A i).terms) (ofColoring c) :=
    not_not.1 fun hG => hc (mem_stepExceptions.2 ⟨h, hG⟩)
  obtain ⟨s, hs, hcs⟩ := hG
  cases op with
  | const b => cases b <;> simp_all [Approximator.gateTerms]
  | or =>
    rw [interpretation_or, Bool.or_eq_true, decode_eq_true, decode_eq_true]
    rcases mem_union.1 hs with hs | hs
    · exact Or.inl ⟨s, hs, hcs⟩
    · exact Or.inr ⟨s, hs, hcs⟩
  | and =>
    rw [interpretation_and, Bool.and_eq_true, decode_eq_true, decode_eq_true]
    exact ⟨⟨s, (mem_inter.1 hs).1, hcs⟩, ⟨s, (mem_inter.1 hs).2, hcs⟩⟩

variable [Fact (2 ≤ r)]

/-- **Negative errors.** The approximation scheme on the complete multipartite graphs of colourings
with `g` colours: the approximate value is at most the exact one away from the errors of
closing. -/
noncomputable def scheme (hl : 2 ≤ l) :
    Approximation.Scheme Monotone.interpretation (Approximator.interpretation (n := n) (r := r))
      (fun (A : Approximator n r l) (c : Coloring n g) => A.decode (ofColoring c))
      ofColoring Approximator.input where
  relation u v := v ≤ u
  relation_trans h h' := h'.trans h
  map_relation op _ _ h := interpretation_mono op h
  errorCost _ := errorCap n g r l
  exceptions := exceptions g
  input_correct c i := by rw [decode_input hl]
  gate_correct := gate_correct
  exceptions_card_le op A :=
    card_stepExceptions_closure_le fun _ => Approximator.card_le_of_mem_gateTerms A

end Cslib.Circuits.Monotone.Closure.Negative

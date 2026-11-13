/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Logics.Propositional.CSP.Planar.Normalization

/-!
# Ordered normalization regression cases

These tests exercise actual ordered operations and primitive-positive witnesses. The finite
families are supporting examples; arbitrary arity is proved by `exists_construction`.
-/

open Cslib Cslib.BitString Cslib.Logic.PL Cslib.Logic.PL.CSP.Normalization

private def twoDifferences (n : ℕ) : Set (Fin n → Bool) :=
  {x | cyclicDifference x = (fun _ => false) ∨ cyclicDifference x = (fun _ => true)}

private instance (n : ℕ) : DecidablePred (· ∈ twoDifferences n) := fun x =>
  inferInstanceAs (Decidable (cyclicDifference x = (fun _ => false) ∨
    cyclicDifference x = (fun _ => true)))

private instance (P : Set (Fin 4 → Bool)) [DecidablePred (· ∈ P)] :
    Decidable (IsStandardizedInconsistent P) := by
  change Decidable ((∀ x : Fin 4 → Bool, x ∈ P ↔ (fun i => !x i) ∈ P) ∧
    (∀ x : Fin 4 → Bool, x ∈ cross → x ∈ P) ∧
    ∀ x : Fin 4 → Bool, x ∈ P → x 0 = x 1 ∨ (x 0 = x 2 ∧ x 0 ≠ x 1 ∧ x 1 = x 3))
  infer_instance

private theorem mem_twoDifferences_image {n : ℕ}
    (hp : parityOn Finset.univ (fun _ : Fin n => true) = false) (d : Fin n → Bool) :
    d ∈ cyclicDifferenceRelation (twoDifferences n) ↔
      d = (fun _ => false) ∨ d = (fun _ => true) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · rintro (rfl | rfl)
    · exact ⟨fun _ => false, Or.inl (cyclicDifference_const n false),
        cyclicDifference_const n false⟩
    · have he := cyclicDifference_cyclicIntegral (fun _ : Fin n => true) hp
      exact ⟨_, Or.inr he, he⟩

private theorem twoDifferences_obstruction (n : ℕ)
    (hp : parityOn Finset.univ (fun _ : Fin (n + 1) => true) = false)
    (hpair : ∀ j : Fin (n + 1), j ≠ 0 →
      flipOn {0, j} (fun _ => false) ≠ (fun _ => false) ∧
      flipOn {0, j} (fun _ => false) ≠ (fun _ => true)) :
    CyclicExchangeObstruction (twoDifferences (n + 1)) (fun _ => true) := by
  refine ⟨?_, Or.inl (cyclicDifference_const _ false), ?_, rfl, ?_⟩
  · exact isSelfComplementary_preimage_cyclicDifference
      {d | d = (fun _ => false) ∨ d = (fun _ => true)}
  · exact (mem_twoDifferences_image hp _).mpr (Or.inr rfl)
  · intro j hj _ hf
    rcases (mem_twoDifferences_image hp _).mp hf with he | he
    · exact (hpair j hj).1 he
    · exact (hpair j hj).2 he

private theorem six_obstruction :
    CyclicExchangeObstruction (twoDifferences 6) (fun _ => true) :=
  twoDifferences_obstruction 5 (by decide) (by decide)

private theorem eight_obstruction :
    CyclicExchangeObstruction (twoDifferences 8) (fun _ => true) :=
  twoDifferences_obstruction 7 (by decide) (by decide)

private theorem twelve_obstruction :
    CyclicExchangeObstruction (twoDifferences 12) (fun _ => true) :=
  twoDifferences_obstruction 11 (by decide) (by decide)

-- Full-support families force repeated caps rather than a feasible quartet finish.
private theorem twoDifferences_no_quartet {n : ℕ}
    (hp : parityOn Finset.univ (fun _ : Fin (n + 4) => true) = false)
    (hq : ∀ k : Fin (n + 4), 3 ≤ k.val →
      flipOn {0, 1, 2, k} (fun _ => false) ≠ (fun _ => false) ∧
      flipOn {0, 1, 2, k} (fun _ => false) ≠ (fun _ => true)) :
    ∀ k : Fin (n + 4), 3 ≤ k.val →
      flipOn {0, 1, 2, k} (fun _ => false) ∉
        cyclicDifferenceRelation (twoDifferences (n + 4)) := by
  intro k hk hf
  rcases (mem_twoDifferences_image hp _).mp hf with he | he
  · exact (hq k hk).1 he
  · exact (hq k hk).2 he

private def sixToFour : Program 6 4 := .cap (by decide) (.done 4)
private def eightToFour : Program 8 4 := .cap (by decide) sixToFour
private def twelveToFour : Program 12 4 :=
  .cap (by decide) (.cap (by decide) eightToFour)

example : IsStandardizedInconsistent (sixToFour.eval (twoDifferences 6)) := by
  exact (six_obstruction.cap (twoDifferences_no_quartet (by decide) (by decide))).standardized

example : IsStandardizedInconsistent (eightToFour.eval (twoDifferences 8)) := by
  simp only [eightToFour, sixToFour, Program.eval]
  decide
example : IsStandardizedInconsistent (twelveToFour.eval (twoDifferences 12)) := by
  simp only [twelveToFour, eightToFour, sixToFour, Program.eval]
  decide

example : eightToFour.reductions = 2 ∧ eightToFour.caps = 2 := by decide
example : twelveToFour.reductions = 4 ∧ twelveToFour.caps = 4 := by decide

private theorem cross_eq_twoDifferences : cross = twoDifferences 4 := by
  ext x
  exact (by decide : ∀ x : Fin 4 → Bool, x ∈ cross ↔ x ∈ twoDifferences 4) x

private theorem cross_obstruction : CyclicExchangeObstruction cross (fun _ => true) := by
  rw [cross_eq_twoDifferences]
  exact twoDifferences_obstruction 3 (by decide) (by decide)

example : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation cross) :=
  cross_obstruction.not_isEvenDeltaMatroid
example : IsStandardizedInconsistent cross := cross_obstruction.standardized
example : Nonempty (Construction cross) :=
  (exists_construction cross ⟨_, cross_obstruction.zero_mem⟩ cross_obstruction.selfComplementary
    cross_obstruction.not_isEvenDeltaMatroid).2

-- The full input hypotheses are realized at arities six, eight and twelve.
example : 4 ≤ 6 ∧ Nonempty (Construction (twoDifferences 6)) :=
  exists_construction _ ⟨_, six_obstruction.zero_mem⟩ six_obstruction.selfComplementary
    six_obstruction.not_isEvenDeltaMatroid
example : 4 ≤ 8 ∧ Nonempty (Construction (twoDifferences 8)) :=
  exists_construction _ ⟨_, eight_obstruction.zero_mem⟩ eight_obstruction.selfComplementary
    eight_obstruction.not_isEvenDeltaMatroid
example : 4 ≤ 12 ∧ Nonempty (Construction (twoDifferences 12)) :=
  exists_construction _ ⟨_, twelve_obstruction.zero_mem⟩ twelve_obstruction.selfComplementary
    twelve_obstruction.not_isEvenDeltaMatroid

-- A feasible quartet must supply the full witness after conditioned deletion.
private def quartetFamily : Set (Fin 6 → Bool) :=
  {x | cyclicDifference x = (fun _ => false) ∨
    cyclicDifference x = flipOn {0, 1, 2, 5} (fun _ => false) ∨
    cyclicDifference x = (fun _ => true)}
private instance : DecidablePred (· ∈ quartetFamily) := fun x =>
  inferInstanceAs (Decidable (cyclicDifference x = (fun _ => false) ∨
    cyclicDifference x = flipOn {0, 1, 2, 5} (fun _ => false) ∨
    cyclicDifference x = (fun _ => true)))
private def quartetFinish : Program 6 4 := .zero 4 (.zero 3 (.done 4))
example : IsStandardizedInconsistent (quartetFinish.eval quartetFamily) := by
  simp only [quartetFinish, Program.eval, zeroRestriction, quartetFamily]
  decide
example : (fun _ => false) ∈ quartetFinish.eval quartetFamily := by
  simp only [quartetFinish, Program.eval, zeroRestriction, quartetFamily]
  decide
example : ![false, true, false, true] ∈ quartetFinish.eval quartetFamily := by
  simp only [quartetFinish, Program.eval, zeroRestriction, quartetFamily]
  decide
example : ![false, true, true, true] ∉ quartetFinish.eval quartetFamily := by
  simp only [quartetFinish, Program.eval, zeroRestriction, quartetFamily]
  decide

-- Interior and last-edge identifications condition on a zero difference.
example : zeroPort (n := 4) 5 5 = 0 := by decide
example : zeroPort (n := 4) 5 0 = 0 := by decide
example : cyclicDifference (![false, true, true, false, false] ∘ zeroPort 5) 5 = false := by
  exact cyclicDifference_zeroPort _ _
example : cyclicDifference (![false, true, true, false, false] ∘ zeroPort 3) ∘
    differencePort 3 = cyclicDifference ![false, true, true, false, false] :=
  cyclicDifference_zeroPort_differencePort _ _
example : ![false, true, false, true, false] ∉ zeroRestriction 5 (twoDifferences 6) := by decide

-- Proper initial support with distinguished old edge 2 and a last-edge deletion.
private def properSupportFamily : Set (Fin 8 → Bool) :=
  {x | cyclicDifference x = (fun _ => false) ∨
    cyclicDifference x = flipOn {2, 3, 4, 7} (fun _ => false)}
private instance : DecidablePred (· ∈ properSupportFamily) := fun x =>
  inferInstanceAs (Decidable (cyclicDifference x = (fun _ => false) ∨
    cyclicDifference x = flipOn {2, 3, 4, 7} (fun _ => false)))
private def properSupportTrace : Program 8 4 :=
  .rotate 2 (.zero 7 (.zero 6 (.zero 4 (.zero 3 (.done 4)))))
example : IsStandardizedInconsistent (properSupportTrace.eval properSupportFamily) := by
  simp only [properSupportTrace, Program.eval]
  decide
example : properSupportTrace.reductions = 4 ∧ properSupportTrace.caps = 0 := by decide

-- The cap identifies exactly old ports 1 and 3 and gives old port 2 a fresh label.
example : List.ofFn (@capPort 2) =
    [Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inl 1, Sum.inl 2, Sum.inl 3] := by decide
example : List.ofFn (@capDifferencePort 2) = [0, 3, 4, 5] := by decide
-- At the smallest arity the retained differences still skip exactly coordinates 1 and 2.
example : List.ofFn (@capDifferencePort 0) = [0, 3] := by decide
example : cyclicDifference ((Sum.elim ![false, true, false, true]
    (fun _ : Fin 1 => false)) ∘ capPort) 1 =
      cyclicDifference ((Sum.elim ![false, true, false, true]
        (fun _ : Fin 1 => false)) ∘ capPort) 2 := cyclicDifference_capPort_pair _ _

example : ![false, true, false, true] ∈ capRelation (twoDifferences 6) := by decide
example : ![false, true, true, true] ∉ capRelation (twoDifferences 6) := by decide

-- The all-false twist uses two disequalities per spoke; all-true uses one.
example : (twistBody (fun _ : Fin 6 => false)).length = 13 := by decide
example : (twistBody (fun _ : Fin 6 => true)).length = 7 := by decide
example : ((twistBody ![false, true, false, true]).map (fun c => c.scope.length)) =
    [4, 2, 2, 2, 2, 2, 2] := by decide

-- Actual satisfying and rejecting auxiliary assignments, rather than only a correctness type.
example : (twistBody (fun _ : Fin 6 => false)).eval (sem (twoDifferences 6))
    (Sum.elim (fun _ => false) (Fin.addCases (fun _ => false) (fun _ => true))) = true := by
  rw [eval_twistBody_iff]
  constructor
  · simpa only [Fin.addCases_left] using six_obstruction.zero_mem
  · intro i
    simp only [Fin.addCases_left, Fin.addCases_right, Bool.false_eq_true, ite_false]
    decide

example : (twistBody (fun _ : Fin 6 => false)).eval (sem (twoDifferences 6))
    (Sum.elim (fun _ => false) (fun _ => false)) ≠ true := by
  intro hf
  rw [eval_twistBody_iff] at hf
  obtain ⟨_, h⟩ := hf
  have hi := h 0
  simp at hi

-- Exact auxiliaries and scope lengths of an executed multiple-cap gadget.
example : (twelveToFour.gadget (twistGadget (twoDifferences 12) (fun _ => false))).numAux = 28 := by
  rw [Program.gadget_numAux]
  rfl
example :
    (sixToFour.gadget (twistGadget (twoDifferences 6) (fun _ => false))).body.map Constraint.rel =
      (twistBody (fun _ : Fin 6 => false)).map Constraint.rel := Program.gadget_symbols _ _

example : ((twelveToFour.gadget
    (twistGadget (twoDifferences 12) (fun _ => false))).body.map (fun c => c.scope.length)) =
      12 :: List.replicate 24 2 := by decide

-- Nullary nonempty relations cannot trigger the exchange obstruction; empty input is excluded.
example : IsEvenDeltaMatroid (cyclicDifferenceRelation (Set.univ : Set (Fin 0 → Bool))) := by
  have he : cyclicDifferenceRelation (Set.univ : Set (Fin 0 → Bool)) = {fun _ => false} := by
    ext x
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      exact ⟨x, Set.mem_univ _, Subsingleton.elim _ _⟩
  rw [he]
  exact isEvenDeltaMatroid_singleton _
example : ¬(∅ : Set (Fin 0 → Bool)).Nonempty := Set.not_nonempty_empty

-- The fixed symbol interpretation rejects malformed original and disequality scopes.
example : sem cross .relation [false, true, false] = false := by simp [sem]
example : sem cross .disequality [false] = false := by simp [sem]

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.Immune
import CslibFrontier.Computability.Kolmogorov.Incompleteness

/-!
Regression clients for Chaitin's incompleteness theorem for plain Kolmogorov complexity: the
hypothesis `MinorizesPartrec` holds for `universal` and a string method and fails for `literal`,
the theorem applies to a collection of trivially true statements, and the incompressible strings
and numbers are immune to the r.e. sets.
-/

namespace ComplexityTests.KolmogorovIncompleteness

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Cslib.Complexity Encodable

/-! ### The hypothesis `MinorizesPartrec` -/

/-- A description method of binary strings: `universal`, read through the decoding of `ℕ`. -/
noncomputable def universalBits : DescriptionMethod (List Bool) :=
  universal.map fun n => (decode (α := List Bool) n).getD []

-- `universalBits` minorizes every partial recursive decoder, so the string results apply to it.
theorem minorizesPartrec_universalBits : universalBits.MinorizesPartrec :=
  minorizesPartrec_universal.map Computable.encode fun y => by simp [encodek]

-- The literal method does not: the decoder `p ↦ p ++ p` doubles lengths.
example : ¬ literal.MinorizesPartrec := fun h => by
  obtain ⟨c, hc⟩ := h (fun p => Part.some (p ++ p))
    (Computable.list_append.comp Computable.id Computable.id).partrec
  have := hc (List.replicate (c + 1) true) _ (Part.mem_some _)
  simp only [ecomplexity_literal, List.length_append, List.length_replicate] at this
  norm_cast at this
  omega

/-! ### Nonvacuity: a collection of trivially true statements -/

-- The statements `0 ≤ C(x)` are true, and the set of them is r.e.
example : ∃ c : ℕ, ∀ x n, (x, n) ∈ {xn : ℕ × ℕ | xn.2 = 0} → n ≤ c :=
  minorizesPartrec_universal.exists_forall_le_of_rePred
    ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).computablePred.to_re.of_eq fun _ => Iff.rfl)
    fun x n h => by simp only [Set.mem_ofPred_eq] at h; simp [h]

-- The quantitative form, stated with the `ℕ`-valued complexity `K = universal.complexity`.
example : ∃ c : ℕ, ∀ (e : Nat.Partrec.Code) (S : Set (ℕ × ℕ)),
    (∀ xn, xn ∈ S ↔ (e.eval (encode xn)).Dom) →
    (∀ x n, (x, n) ∈ S → n ≤ universal.complexity x) →
    ∀ x n, (x, n) ∈ S → n ≤ universal.complexity (encode e) + c := by
  obtain ⟨c, hc⟩ := minorizesPartrec_universal.exists_forall_le_complexity_universal_add
  exact ⟨c, fun e S hS hsound => hc e S hS fun x n h => by
    rw [← natCast_complexity_universal]
    exact_mod_cast hsound x n h⟩

-- Incompleteness: some true statement `n ≤ C(x)` about strings is missing from a sound r.e. set.
example {S : Set (List Bool × ℕ)} (hS : REPred (· ∈ S))
    (hsound : ∀ x n, (x, n) ∈ S → (n : ℕ∞) ≤ universalBits.ecomplexity x) :
    ∃ (x : List Bool) (n : ℕ), (n : ℕ∞) ≤ universalBits.ecomplexity x ∧ (x, n) ∉ S :=
  minorizesPartrec_universalBits.exists_notMem_of_rePred hS hsound

/-! ### Immunity -/

-- The incompressible strings are immune to the r.e. sets.
example : IsImmune {B | REPred (· ∈ B)}
    {x : List Bool | (x.length : ℕ∞) ≤ universalBits.ecomplexity x} :=
  ⟨infinite_setOf_length_le_ecomplexity universalBits, fun _ hB hBA =>
    minorizesPartrec_universalBits.finite_of_rePred_of_subset_length_le hB hBA⟩

-- The numbers whose binary length is at most their complexity are immune to the r.e. sets.
example : IsImmune {B | REPred (· ∈ B)} {x : ℕ | x.size ≤ universal.complexity x} :=
  ⟨infinite_setOf_size_le_complexity_universal, fun _ hB hBA =>
    finite_of_rePred_of_subset_size_le_complexity_universal hB hBA⟩

-- Immunity fails for `literal`, which does not minorize partial recursive decoders: every string
-- is incompressible, and the r.e. set of all strings is infinite.
example : ¬ IsImmune {B | REPred (· ∈ B)}
    {x : List Bool | (x.length : ℕ∞) ≤ literal.ecomplexity x} := fun ⟨_, h⟩ =>
  Set.infinite_univ (h Set.univ (ComputablePred.to_re ⟨fun _ => isTrue trivial,
    (Computable.const true).of_eq fun _ => rfl⟩ |>.of_eq fun _ => by simp) (fun x _ => by simp))

end ComplexityTests.KolmogorovIncompleteness

/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleBits

/-!
# Executable validation of raw movement schedules

The Boolean checker rejects incomplete rows, incomplete pairs and aligned `11` pairs. Its
correctness is exactly the canonical-input predicate used by the native endpoint machine.
These are executable semantic checks; a native machine and its linear clock are separate claims.
-/

public section

namespace Turing.MultiTapeTM.ScheduleBits

/-- Check consecutive aligned pairs; an unfinished last pair is invalid. -/
@[expose] def validPairs : List Bool → Bool
  | [] => true
  | [_] => false
  | a :: b :: rest => decide (decodePair a b ≠ none) && validPairs rest

/-- The executable pair checker recognizes precisely the inductive pair representation. -/
theorem validPairs_eq_true_iff : ∀ word, validPairs word = true ↔ ValidPairs word
  | [] => by
    constructor
    · intro _; exact .nil
    · intro _; rfl
  | [_] => by
    constructor
    · intro h; cases h
    · intro h; cases h
  | a :: b :: rest => by
    simp only [validPairs, Bool.and_eq_true, decide_eq_true_eq, validPairs_eq_true_iff rest]
    constructor
    · rintro ⟨h, hr⟩; exact .cons h hr
    · intro h; cases h with | cons hp hr => exact ⟨hp, hr⟩

/-- Check complete input-first rows of two-bit movements. -/
@[expose] def validate (k : ℕ) (word : List Bool) : Bool :=
  decide (word.length % (2 * (k + 1)) = 0) && validPairs word

/-- Success discharges exactly the endpoint machine's canonical raw-input condition. -/
theorem validate_eq_true_iff (k : ℕ) (word : List Bool) :
    validate k word = true ↔ Canonical k word := by
  simp [validate, Canonical, validPairs_eq_true_iff]

/-- Every represented schedule passes the executable raw-input check. -/
theorem validate_rows {k : ℕ} (rs : List (Option (Fin k) → SignType)) :
    validate k (rows rs) = true := (validate_eq_true_iff _ _).mpr (canonical_rows rs)

/-- Valid pairs are actual movement encodings, not merely a syntactic relaxation. -/
theorem ValidPairs.exists_encode {word : List Bool} (h : ValidPairs word) :
    ∃ ss : List SignType, RelativeScan.encode ss = word := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | @cons a b rest hp _ ih =>
    obtain ⟨ss, hs⟩ := ih
    cases a <;> cases b
    · exact ⟨0 :: ss, by simp [RelativeScan.encode, RelativeScan.negative,
        RelativeScan.positive, hs]⟩
    · exact ⟨1 :: ss, by simp [RelativeScan.encode, RelativeScan.negative,
        RelativeScan.positive, hs]⟩
    · exact ⟨(-1) :: ss, by simp [RelativeScan.encode, RelativeScan.negative,
        RelativeScan.positive, hs]⟩
    · exact False.elim (hp rfl)

private theorem exists_rows_encode (k : ℕ) (ss : List SignType)
    (hdiv : k + 1 ∣ ss.length) :
    ∃ rs : List (Option (Fin k) → SignType), rows rs = RelativeScan.encode ss := by
  have aux : ∀ n, ∀ ss : List SignType, ss.length = n → k + 1 ∣ n →
      ∃ rs : List (Option (Fin k) → SignType), rows rs = RelativeScan.encode ss := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro ss hlen hd
      by_cases hn : n = 0
      · have hs : ss = [] := List.eq_nil_of_length_eq_zero (hlen.trans hn)
        subst ss
        exact ⟨[], rfl⟩
      have hle : k + 1 ≤ n := Nat.le_of_dvd (by omega) hd
      let pre := ss.take (k + 1)
      have hp : pre.length = k + 1 := by simp [pre, hlen, Nat.min_eq_left hle]
      let f : Fin (k + 1) → SignType := fun i => pre[i.val]'(by omega)
      let r : Option (Fin k) → SignType := fun o => o.elim (f 0) (fun i => f i.succ)
      have hf : (fun c => r (head c)) = f := by
        funext c
        refine Fin.cases ?_ ?_ c
        · rfl
        · intro i; rfl
      have hpre : List.ofFn f = pre := by
        apply List.ext_getElem (by simp [hp])
        intro i h₁ h₂
        simp only [List.getElem_ofFn, f]
      have hr : row r = RelativeScan.encode pre := by rw [row, hf, hpre]
      have ht : (ss.drop (k + 1)).length < n := by simp only [List.length_drop, hlen]; omega
      have htd : k + 1 ∣ (ss.drop (k + 1)).length := by
        simpa only [List.length_drop, hlen] using Nat.dvd_sub hd (dvd_refl (k + 1))
      obtain ⟨rs, hrs⟩ := ih _ ht (ss.drop (k + 1)) rfl htd
      refine ⟨r :: rs, ?_⟩
      rw [rows, hr, hrs, ← RelativeScan.encode_append]
      exact congrArg RelativeScan.encode (List.take_append_drop (k + 1) ss)
  exact aux ss.length ss rfl hdiv

/-- Every canonical raw table is an actual sequence of represented input-first rows. -/
theorem Canonical.exists_rows {k : ℕ} {word : List Bool} (h : Canonical k word) :
    ∃ rs : List (Option (Fin k) → SignType), rows rs = word := by
  obtain ⟨ss, hs⟩ := h.2.exists_encode
  have hd := Nat.dvd_of_mod_eq_zero h.1
  rw [← hs, RelativeScan.length_encode] at hd
  obtain ⟨rs, hr⟩ := exists_rows_encode k ss
    (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hd)
  exact ⟨rs, hr.trans hs⟩

/-- Validation supplies represented rows, so callers need not assume their existence. -/
theorem validate_eq_true_iff_exists_rows (k : ℕ) (word : List Bool) :
    validate k word = true ↔ ∃ rs : List (Option (Fin k) → SignType), rows rs = word := by
  rw [validate_eq_true_iff]
  exact ⟨Canonical.exists_rows, fun ⟨rs, hr⟩ => hr ▸ canonical_rows rs⟩

end Turing.MultiTapeTM.ScheduleBits

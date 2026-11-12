/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Collusion

/-!
# Single-server private information retrieval

With a single server, perfect privacy forces the server to send the whole database: a correct,
private one-server scheme has some query `q` on which the answer map `x ↦ answer x q` is injective
(`Scheme.exists_injective_answer`), so there are at least `2 ^ n` answers
(`Scheme.two_pow_card_le_card_answer`) and the scheme communicates at least `n` bits
(`Scheme.card_le_communication`). Downloading the database (`PIR.download`) attains the bound, so
`HasScheme ι 1 c` holds exactly when `|ι| ≤ c` (`PIR.hasScheme_one_iff`).

This is the one-round `k = 1` specialization of the full-coalition lower bound in `PIR.Collusion`,
formalizing the one-round case of [Chor, Goldreich, Kushilevitz and Sudan,
Section 5.1][ChorGoldreichKushilevitzSudan1998] (`PIR.Interactive` proves the interactive case).

## Main definitions

* `Cslib.Crypto.Protocols.PIR.download`: the server sends the whole database.

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.exists_injective_answer`: one answer determines the
  database.
* `Cslib.Crypto.Protocols.PIR.Scheme.two_pow_card_le_card_answer`,
  `Cslib.Crypto.Protocols.PIR.Scheme.card_le_communication`: at least `2 ^ n` answers and `n`
  bits.
* `Cslib.Crypto.Protocols.PIR.HasScheme.card_le`, `Cslib.Crypto.Protocols.PIR.hasScheme_one_iff`:
  one server needs exactly `n` bits.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Section 5.1
-/

public section

namespace Cslib.Crypto.Protocols.PIR

namespace Scheme

variable {ι S R Q A β : Type}

/-- **One server must send the database.** In a perfectly correct and perfectly private scheme
with one server, some query `q` makes the answer map `x ↦ P.answer default x q` injective
[CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]. Derived as the `|S| = 1`, `t = 1` case of
`Scheme.exists_injective_answers_of_card_le`. -/
theorem exists_injective_answer {P : Scheme ι S R Q A β} [Unique S] [Nonempty ι]
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    ∃ q : Q, Function.Injective fun x => P.answer default x q := by
  let _ : Fintype S := Unique.fintype
  obtain ⟨q, hq⟩ := P.exists_injective_answers_of_card_le hcorrect
    (P.isTPrivate_one_iff.mpr hprivate) (by simp [Fintype.card_unique])
  refine ⟨q default, fun x y hxy => hq (funext fun s => ?_)⟩
  rw [Subsingleton.elim s default]
  exact hxy

/-- A perfectly correct and perfectly private one-server scheme for `n`-bit databases has at least
`2 ^ n` answers. -/
theorem two_pow_card_le_card_answer {P : Scheme ι S R Q A} [Unique S] [Nonempty ι] [Fintype ι]
    [Fintype A] (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    2 ^ Fintype.card ι ≤ Fintype.card A := by
  classical
  obtain ⟨q, hq⟩ := exists_injective_answer hcorrect hprivate
  have h := Fintype.card_le_of_injective _ hq
  rwa [Fintype.card_fun, Fintype.card_bool] at h

/-- **A perfectly correct and perfectly private one-server scheme for `n`-bit databases
communicates at least `n` bits** [CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]; the
answer alone has at least `n` bits. -/
theorem card_le_communication {P : Scheme ι S R Q A} [Fintype S] [Unique S] [Fintype ι]
    [Fintype Q] [Fintype A] (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    Fintype.card ι ≤ communication S Q A :=
  P.card_le_communication_of_card_le hcorrect (P.isTPrivate_one_iff.mpr hprivate)
    (by simp [Fintype.card_unique])

end Scheme

/-- The trivial one-server scheme: the server sends the whole database `ι → β` and the user reads
the entry it wants. -/
def download (ι : Type) (β : Type := Bool) : Scheme ι Unit Unit Unit (ι → β) β where
  query _ := pure ((), fun _ => ())
  answer _ x _ := x
  reconstruct i _ a := a () i

theorem isCorrect_download (ι : Type) (β : Type := Bool) : (download ι β).IsCorrect :=
  (download ι β).isCorrect_iff.mpr fun _ _ _ _ _ => rfl

theorem isPrivate_download (ι : Type) (β : Type := Bool) : (download ι β).IsPrivate :=
  (download ι β).isPrivate_iff.mpr fun _ _ _ => by
    rw [Scheme.eval_serverQuery, Scheme.eval_serverQuery]
    rfl

theorem communication_download (ι : Type) [Fintype ι] [DecidableEq ι] :
    communication Unit Unit (ι → Bool) = Fintype.card ι := by
  rw [communication_of_card_answer Unit Unit (ι → Bool)
      (by rw [Fintype.card_fun, Fintype.card_bool]),
    Fintype.card_unit, Nat.clog_one_right, zero_add, one_mul]

/-- One server needs at least `n` bits. -/
theorem HasScheme.card_le {ι : Type} [Fintype ι] {c : ℕ} (h : HasScheme ι 1 c) :
    Fintype.card ι ≤ c :=
  (hasTPrivateScheme_one_iff.mpr h).card_le_of_le le_rfl

theorem hasScheme_download (ι : Type) [Fintype ι] : HasScheme ι 1 (Fintype.card ι) := by
  classical
  have h := (isCorrect_download ι).hasScheme (isPrivate_download ι)
  rwa [Fintype.card_unit, communication_download] at h

/-- **One server needs exactly `n` bits**: a perfectly correct and perfectly private one-server
scheme communicating `c` bits exists exactly when `n ≤ c`. -/
theorem hasScheme_one_iff (ι : Type) [Fintype ι] (c : ℕ) :
    HasScheme ι 1 c ↔ Fintype.card ι ≤ c :=
  ⟨HasScheme.card_le, (hasScheme_download ι).mono⟩

end Cslib.Crypto.Protocols.PIR

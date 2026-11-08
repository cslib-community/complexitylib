/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.PIR.Basic

/-!
# Single-server private information retrieval

With a single server, perfect privacy forces the server to send the whole database: a correct,
private one-server scheme has some query `q` on which the answer map `x ↦ answer x q` is injective
(`Scheme.exists_injective_answer`), so there are at least `2 ^ n` answers
(`Scheme.two_pow_card_le_card_answer`) and the scheme communicates at least `n` bits
(`Scheme.card_le_communication`). Downloading the database (`PIR.download`) attains the bound, so
`HasScheme ι 1 c` holds exactly when `|ι| ≤ c` (`PIR.hasScheme_one_iff`).

This is the one-round case of [Chor, Goldreich, Kushilevitz and Sudan,
Section 5.1][ChorGoldreichKushilevitzSudan1998], whose argument also covers interactive protocols;
multi-round protocols are not modelled here. The proof adapts theirs to one round. By privacy, a
query that the user can send for one index can be sent for every index; on that query the user must
recover every bit of the database from the one answer.

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

open Probability

namespace Scheme

variable {ι S R Q A : Type} {P : Scheme ι S R Q A}

/-- **One server must send the database.** In a perfectly correct and perfectly private scheme
with one server, some query `q` makes the answer map `x ↦ P.answer default x q` injective
[CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]. -/
theorem exists_injective_answer [Unique S] [Nonempty ι] (hcorrect : P.IsCorrect)
    (hprivate : P.IsPrivate) : ∃ q : Q, Function.Injective fun x => P.answer default x q := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨⟨r₀, q₀⟩, h₀⟩ := (ProbComp.eval (P.query i₀)).support_nonempty
  refine ⟨q₀ default, fun x y hxy => funext fun i => ?_⟩
  -- By privacy, the query `q₀ default` can also be sent for the index `i`.
  have hq : q₀ default ∈ (ProbComp.eval (P.serverQuery default i)).support := by
    rw [hprivate.eval_serverQuery_eq default i i₀, P.eval_serverQuery]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨_, h₀, rfl⟩
  rw [P.eval_serverQuery] at hq
  obtain ⟨⟨r, q⟩, hrq, hq⟩ := (PMF.mem_support_map_iff _ _ _).1 hq
  change q default = q₀ default at hq
  have hanswers : (fun s => P.answer s x (q s)) = fun s => P.answer s y (q s) := by
    funext s
    rw [Subsingleton.elim s default, hq]
    exact hxy
  rw [← hcorrect.reconstruct_eq x i hrq, ← hcorrect.reconstruct_eq y i hrq, hanswers]

/-- A perfectly correct and perfectly private one-server scheme for `n`-bit databases has at least
`2 ^ n` answers. -/
theorem two_pow_card_le_card_answer [Unique S] [Nonempty ι] [Fintype ι] [Fintype A]
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) : 2 ^ Fintype.card ι ≤ Fintype.card A := by
  classical
  obtain ⟨q, hq⟩ := exists_injective_answer hcorrect hprivate
  have h := Fintype.card_le_of_injective _ hq
  rwa [Fintype.card_fun, Fintype.card_bool] at h

/-- **A perfectly correct and perfectly private one-server scheme for `n`-bit databases
communicates at least `n` bits** [CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]; the
answer alone has at least `n` bits. -/
theorem card_le_communication [Fintype S] [Unique S] [Fintype ι] [Fintype Q] [Fintype A]
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    Fintype.card ι ≤ communication S Q A := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Fintype.card_eq_zero]
    exact Nat.zero_le _
  · have h := two_pow_card_le_card_answer hcorrect hprivate
    have hA : Fintype.card ι ≤ Nat.clog 2 (Fintype.card A) := by
      by_contra hlt
      push Not at hlt
      have := Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card A)
      have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
      omega
    rw [communication_eq, Fintype.card_unique (α := S), one_mul]
    omega

end Scheme

/-- The trivial one-server scheme: the server sends the whole database and the user reads the bit
it wants. -/
def download (ι : Type) : Scheme ι Unit Unit Unit (ι → Bool) where
  query _ := pure ((), fun _ => ())
  answer _ x _ := x
  reconstruct i _ a := a () i

theorem isCorrect_download (ι : Type) : (download ι).IsCorrect :=
  (download ι).isCorrect_iff.mpr fun _ _ _ _ _ => rfl

theorem isPrivate_download (ι : Type) : (download ι).IsPrivate :=
  (download ι).isPrivate_iff.mpr fun _ _ _ => by
    rw [Scheme.eval_serverQuery, Scheme.eval_serverQuery]
    rfl

theorem communication_download (ι : Type) [Fintype ι] [DecidableEq ι] :
    communication Unit Unit (ι → Bool) = Fintype.card ι := by
  rw [communication_rows, Fintype.card_unit, Nat.clog_one_right, zero_add, one_mul]

/-- One server needs at least `n` bits. -/
theorem HasScheme.card_le {ι : Type} [Fintype ι] {c : ℕ} (h : HasScheme ι 1 c) :
    Fintype.card ι ≤ c := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := hasScheme_iff.mp h
  let : Unique S := (Fintype.card_eq_one_iff_nonempty_unique.mp hk).some
  exact (P.card_le_communication hcorrect hprivate).trans hcomm

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

/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Collusion
public import CslibFrontier.Crypto.Protocols.PIR.Cube
public import CslibFrontier.Crypto.Protocols.PIR.SingleServer
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Foundations.Data.Nat.Clog

/-!
# Private block retrieval

[Chor, Goldreich, Kushilevitz and Sudan, Section 4][ChorGoldreichKushilevitzSudan1998] generalizes
private information retrieval from single bits to databases of `n` blocks of `ℓ` bits each
(`PIR_k(n, ℓ)`), hiding the block index `i` while amortizing communication across the block.

In our one-round framework (`PIR.Basic`, `PIR.Collusion`, `PIR.SingleServer`), block schemes reuse
`Scheme ι S R Q A β`, `HasScheme ι k c β`, `HasTPrivateScheme ι t k c β`, and `PIR.download ι β`
directly by instantiating the payload type `β` with `κ → Bool` (`ℓ = |κ|`).

* **Block-to-bit projection (`Scheme.toBitScheme`) and `n · ℓ` lower bounds.** Viewing a scheme for
  `κ → Bool` blocks on `ι` as a single-bit scheme on `ι × κ` reduces full-coalition and
  single-server `n · ℓ`-bit lower bounds (`Scheme.card_mul_le_communication_of_card_le`,
  `Scheme.card_mul_le_communication`, attained by `PIR.download ι (κ → Bool)` in
  `hasBlockScheme_one_iff`) directly to `PIR.Collusion` and `PIR.SingleServer`.
* **Entry-to-block transformation (`Scheme.toBlock`, Proposition 4, Section 4.1).** Sending one
  query of a scheme `P` and having each server answer once for every coordinate `b : κ` of the
  block multiplies only the server-to-user communication by `|κ|` (`communication_toBlock_le`,
  `communication_toBlock_of_card_answer`), preserving `IsCorrect`, `IsPrivate`, and `IsTPrivate`.
* **Answer-compressing XOR-sum transformation (`Scheme.sumChunks`, Proposition 5, Section 4.1) and
  homomorphism reduction (`Scheme.mapAnswerHom`, Section 4.1, p. 12).** When a `PIR_k(n + 1, 1)`
  scheme (`Option ι`, with `none` as the dummy zero bit) reconstructs by XORing one-bit answers
  (`Scheme.HasXorReconstruct`, satisfied by `PIR.twoServer` and `PIR.cube`), running `m`
  independent instances in parallel and XORing the `m` answers at each server yields a
  `PIR_k(m · n, 1)` scheme with `m`-fold queries and **one-bit** server answers. More generally, any
  scheme reconstructing via `g (∑ s, f s (a s))` for an additive homomorphism `g : G →+ Bool`
  reduces to `HasXorReconstruct` via `Scheme.mapAnswerHom`.
* **Block retrieval corollaries (Corollaries 6, 7 and 8, Sections 4.1–4.2).** Composing
  `Scheme.sumChunks` with `Scheme.toBlock` gives Corollary 6 (`hasBlockScheme_of_xorReconstruct`),
  solving `PIR_k(N, ℓ)` within `ℓ` times the query cost of `PIR_k(⌈N / ℓ⌉ + 1, 1)` plus `k · ℓ`
  answer bits (also preserving `t`-privacy via `hasTPrivateBlockScheme_of_xorReconstruct`).
  Specializing `Scheme.toBlock` to `PIR.twoServer` and `PIR.cube (Fin 2)` gives constant-overhead
  block retrieval: `4 ℓ` bits with two servers for `n ≤ ℓ` (Corollary 7, `hasBlockScheme_two_of_le`)
  and `8 ℓ` bits with four servers when `n ≤ m ^ 2` and `2 m ≤ ℓ`, in particular `n ≤ (ℓ / 2) ^ 2`
  (Corollary 8, `hasBlockScheme_four_of_le_sq`, `hasBlockScheme_four_of_le_half_sq`; this replaces
  the paper's unrounded `n ≤ ℓ ^ 2 / 4` (`√n ≤ ℓ / 2`) with the integer subcube side condition
  `2 m ≤ ℓ`, matching `n ≤ ℓ ^ 2 / 4` whenever `ℓ` is even).

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Scheme.toBitScheme`: view an `ℓ`-bit block scheme on `ι` as a
  single-bit scheme on `ι × κ`.
* `Cslib.Crypto.Protocols.PIR.Scheme.toBlock`: Proposition 4's coordinatewise block-lifting
  transformation.
* `Cslib.Crypto.Protocols.PIR.Scheme.HasXorReconstruct`,
  `Cslib.Crypto.Protocols.PIR.Scheme.mapAnswerHom`,
  `Cslib.Crypto.Protocols.PIR.Scheme.sumChunks`: Proposition 5's XOR-sum predicate, group
  homomorphism reduction, and `m`-chunk query-expanding / answer-compressing transformation.

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.card_mul_le_communication_of_card_le`,
  `Cslib.Crypto.Protocols.PIR.Scheme.card_mul_le_communication`,
  `Cslib.Crypto.Protocols.PIR.HasTPrivateScheme.card_mul_le_of_le`,
  `Cslib.Crypto.Protocols.PIR.HasScheme.card_mul_le`,
  `Cslib.Crypto.Protocols.PIR.hasBlockScheme_one_iff`: full-coalition and single-server block
  retrieval require `|ι| * |κ|` bits.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.toBlock`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.toBlock`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate.toBlock`,
  `Cslib.Crypto.Protocols.PIR.communication_toBlock_le`,
  `Cslib.Crypto.Protocols.PIR.communication_toBlock_of_card_answer`: Proposition 4.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.mapAnswerHom`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.sumChunks`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.sumChunks`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate.sumChunks`: Proposition 5 and its group-homomorphism
  extension.
* `Cslib.Crypto.Protocols.PIR.hasBlockScheme_of_xorReconstruct`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateBlockScheme_of_xorReconstruct`,
  `Cslib.Crypto.Protocols.PIR.hasBlockScheme_two_of_le`,
  `Cslib.Crypto.Protocols.PIR.hasBlockScheme_four_of_le_sq`,
  `Cslib.Crypto.Protocols.PIR.hasBlockScheme_four_of_le_half_sq`: Corollaries 6, 7 and 8.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Section 4 (Propositions 4 and 5, Corollaries
  6, 7 and 8, pp. 11–13); numbering of the authors' journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability

/-! ### Reduction of block lower bounds to single-bit PIR -/

namespace Scheme

variable {ι S R Q A β : Type}

/-- View a block scheme retrieving `κ → Bool` blocks as a single-bit scheme on `ι × κ` that sends
the block query for `ib.1` and extracts bit `ib.2` from the reconstructed block. -/
def toBitScheme {κ : Type} (P : Scheme ι S R Q A (κ → Bool)) :
    Scheme (ι × κ) S R Q A where
  query ib := P.query ib.1
  answer s x q := P.answer s (fun i b => x (i, b)) q
  reconstruct ib r a := P.reconstruct ib.1 r a ib.2

theorem query_toBitScheme {κ : Type} (P : Scheme ι S R Q A (κ → Bool)) (ib : ι × κ) :
    P.toBitScheme.query ib = P.query ib.1 := by
  rfl

theorem coalitionQuery_toBitScheme {κ : Type} (P : Scheme ι S R Q A (κ → Bool))
    (T : Finset S) (ib : ι × κ) :
    P.toBitScheme.coalitionQuery T ib = P.coalitionQuery T ib.1 := by
  rw [Scheme.coalitionQuery_eq, query_toBitScheme, Scheme.coalitionQuery_eq]

theorem IsCorrect.toBitScheme {κ : Type} {P : Scheme ι S R Q A (κ → Bool)}
    (h : P.IsCorrect) : P.toBitScheme.IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x ib r q hrq
  exact congrFun (h.reconstruct_eq (fun i b => x (i, b)) ib.1 hrq) ib.2

theorem IsTPrivate.toBitScheme {κ : Type} {P : Scheme ι S R Q A (κ → Bool)} {t : ℕ}
    (h : P.IsTPrivate t) : P.toBitScheme.IsTPrivate t := by
  rw [Scheme.isTPrivate_iff]
  intro T hT ib ib'
  rw [coalitionQuery_toBitScheme, coalitionQuery_toBitScheme]
  exact h.eval_coalitionQuery_eq T hT ib.1 ib'.1

theorem IsPrivate.toBitScheme {κ : Type} {P : Scheme ι S R Q A (κ → Bool)}
    (h : P.IsPrivate) : P.toBitScheme.IsPrivate :=
  Scheme.isTPrivate_one_iff.mp ((Scheme.isTPrivate_one_iff.mpr h).toBitScheme)

/-- Full-coalition (`|S| ≤ t`) private block retrieval of `|ι|` blocks of `|κ|` bits requires at
least `|ι| * |κ|` bits of communication. -/
theorem card_mul_le_communication_of_card_le {κ : Type} [Fintype S] [Fintype ι] [Fintype κ]
    [Fintype Q] [Fintype A] {P : Scheme ι S R Q A (κ → Bool)} {t : ℕ}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    Fintype.card ι * Fintype.card κ ≤ communication S Q A := by
  simpa only [Fintype.card_prod] using
    P.toBitScheme.card_le_communication_of_card_le hcorrect.toBitScheme hprivate.toBitScheme hcard

/-- One-server private block retrieval of `|ι|` blocks of `|κ|` bits requires at least `|ι| * |κ|`
bits of communication. -/
theorem card_mul_le_communication {κ : Type} [Fintype S] [Unique S] [Fintype ι] [Fintype κ]
    [Fintype Q] [Fintype A] {P : Scheme ι S R Q A (κ → Bool)}
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    Fintype.card ι * Fintype.card κ ≤ communication S Q A :=
  card_mul_le_communication_of_card_le hcorrect (isTPrivate_one_iff.mpr hprivate)
    (by simp [Fintype.card_unique])

end Scheme

/-- Every `t`-private block scheme for `κ → Bool` blocks induces a `t`-private single-bit scheme on
`ι × κ` with the same server count and communication bound. -/
theorem HasTPrivateScheme.toBitScheme {ι κ : Type} {t k c : ℕ}
    (h : HasTPrivateScheme ι t k c (κ → Bool)) :
    HasTPrivateScheme (ι × κ) t k c := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := hasTPrivateScheme_iff.mp h
  exact hasTPrivateScheme_iff.mpr
    ⟨S, R, Q, A, _, _, _, P.toBitScheme, hcorrect.toBitScheme, hprivate.toBitScheme, hk, hcomm⟩

/-- Every block scheme for `κ → Bool` blocks induces a single-bit scheme on `ι × κ` with the same
server count and communication bound. -/
theorem HasScheme.toBitScheme {ι κ : Type} {k c : ℕ}
    (h : HasScheme ι k c (κ → Bool)) : HasScheme (ι × κ) k c :=
  hasTPrivateScheme_one_iff.mp (hasTPrivateScheme_one_iff.mpr h).toBitScheme

theorem HasTPrivateScheme.card_mul_le_of_le {ι κ : Type} [Fintype ι] [Fintype κ] {t k c : ℕ}
    (h : HasTPrivateScheme ι t k c (κ → Bool)) (hkt : k ≤ t) :
    Fintype.card ι * Fintype.card κ ≤ c := by
  simpa only [Fintype.card_prod] using h.toBitScheme.card_le_of_le hkt

theorem HasScheme.card_mul_le {ι κ : Type} [Fintype ι] [Fintype κ] {c : ℕ}
    (h : HasScheme ι 1 c (κ → Bool)) :
    Fintype.card ι * Fintype.card κ ≤ c :=
  (hasTPrivateScheme_one_iff.mpr h).card_mul_le_of_le le_rfl

/-- **One-server block retrieval needs exactly `|ι| * |κ|` bits**, attained by `PIR.download`. -/
theorem hasBlockScheme_one_iff (ι κ : Type) [Fintype ι] [Fintype κ] (c : ℕ) :
    HasScheme ι 1 c (κ → Bool) ↔ Fintype.card ι * Fintype.card κ ≤ c := by
  classical
  refine ⟨HasScheme.card_mul_le, fun hc => ?_⟩
  have hdl := (isCorrect_download ι (κ → Bool)).hasScheme (isPrivate_download ι (κ → Bool))
  rw [Fintype.card_unit,
    communication_of_card_answer Unit Unit (ι → κ → Bool)
      (by rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, ← pow_mul,
        Nat.mul_comm (Fintype.card κ)]),
    Fintype.card_unit, Nat.clog_one_right, zero_add, one_mul] at hdl
  exact hdl.mono hc

/-! ### Proposition 4: single-entry PIR to `κ`-coordinate block PIR -/

namespace Scheme

variable {ι S R Q A β : Type}

/-- **Proposition 4** [CGKS, Section 4.1, p. 11][ChorGoldreichKushilevitzSudan1998]: lift a
scheme `P` to retrieve `κ`-indexed blocks `κ → β` by sending one query of `P` for the block index
`i` and answering it once for each coordinate `b : κ` of the block. -/
def toBlock (κ : Type) (P : Scheme ι S R Q A β) : Scheme ι S R Q (κ → A) (κ → β) where
  query i := P.query i
  answer s x q b := P.answer s (fun i' => x i' b) q
  reconstruct i r a b := P.reconstruct i r (fun s => a s b)

theorem query_toBlock (κ : Type) (P : Scheme ι S R Q A β) (i : ι) :
    (P.toBlock κ).query i = P.query i := by
  rfl

theorem serverQuery_toBlock (κ : Type) (P : Scheme ι S R Q A β) (s : S) (i : ι) :
    (P.toBlock κ).serverQuery s i = P.serverQuery s i := by
  rw [Scheme.serverQuery_eq, query_toBlock, Scheme.serverQuery_eq]

theorem coalitionQuery_toBlock (κ : Type) (P : Scheme ι S R Q A β) (T : Finset S) (i : ι) :
    (P.toBlock κ).coalitionQuery T i = P.coalitionQuery T i := by
  rw [Scheme.coalitionQuery_eq, query_toBlock, P.coalitionQuery_eq]

theorem IsCorrect.toBlock (κ : Type) {P : Scheme ι S R Q A β} (h : P.IsCorrect) :
    (P.toBlock κ).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x i r q hrq
  funext b
  exact h.reconstruct_eq (fun i' => x i' b) i hrq

theorem IsPrivate.toBlock (κ : Type) {P : Scheme ι S R Q A β} (h : P.IsPrivate) :
    (P.toBlock κ).IsPrivate := by
  rw [Scheme.isPrivate_iff]
  intro s i i'
  rw [serverQuery_toBlock, serverQuery_toBlock]
  exact h.eval_serverQuery_eq s i i'

theorem IsTPrivate.toBlock (κ : Type) {P : Scheme ι S R Q A β} {t : ℕ} (h : P.IsTPrivate t) :
    (P.toBlock κ).IsTPrivate t := by
  rw [Scheme.isTPrivate_iff]
  intro T hT i i'
  rw [coalitionQuery_toBlock, coalitionQuery_toBlock]
  exact h.eval_coalitionQuery_eq T hT i i'

/-! ### Proposition 5 and the Abelian-group homomorphism reduction -/

/-- A one-bit-answer scheme has *XOR-sum reconstruction* when the user reconstructs the desired bit
as `∑ s : S, a s` over `Bool` (`BooleanRing` addition = exclusive-or), independent of `i` and `r`
[CGKS, Section 4.1, Proposition 5][ChorGoldreichKushilevitzSudan1998]. -/
def HasXorReconstruct [Fintype S] (P : Scheme ι S R Q Bool) : Prop :=
  ∀ i r a, P.reconstruct i r a = ∑ s : S, a s

theorem hasXorReconstruct_iff [Fintype S] (P : Scheme ι S R Q Bool) :
    P.HasXorReconstruct ↔ ∀ i r a, P.reconstruct i r a = ∑ s : S, a s := by
  rw [HasXorReconstruct]

theorem hasXorReconstruct_twoServer (ι : Type) [Fintype ι] [DecidableEq ι] :
    (twoServer ι).HasXorReconstruct := by
  intro i r a
  rw [reconstruct_twoServer, Fintype.sum_bool, add_comm]

theorem hasXorReconstruct_cube (D ι : Type) [Fintype D] [DecidableEq D] [Fintype ι]
    [DecidableEq ι] : (cube D ι).HasXorReconstruct :=
  reconstruct_cube

/-- **Abelian-group homomorphism reduction to XOR-sum reconstruction**
[CGKS, Section 4.1, p. 12][ChorGoldreichKushilevitzSudan1998]: if `P` reconstructs via
`g (∑ s, f s (a s))` for fixed maps `f : S → A → G` into an `AddCommGroup G` and an additive
homomorphism `g : G →+ Bool` (independent of `i` and `r`), letting each server send the single bit
`g (f s (P.answer s x q))` produces a one-bit-answer scheme satisfying `HasXorReconstruct`. -/
def mapAnswerHom [Fintype S] {G : Type} [AddCommGroup G] (P : Scheme ι S R Q A)
    (f : S → A → G) (g : G →+ Bool) : Scheme ι S R Q Bool where
  query := P.query
  answer s x q := g (f s (P.answer s x q))
  reconstruct _ _ b := ∑ s : S, b s

theorem hasXorReconstruct_mapAnswerHom [Fintype S] {G : Type} [AddCommGroup G]
    (P : Scheme ι S R Q A) (f : S → A → G) (g : G →+ Bool) :
    (P.mapAnswerHom f g).HasXorReconstruct :=
  fun _ _ _ => rfl

theorem IsCorrect.mapAnswerHom [Fintype S] {G : Type} [AddCommGroup G] {P : Scheme ι S R Q A}
    (hcorrect : P.IsCorrect) (f : S → A → G) (g : G →+ Bool)
    (hrec : ∀ i r a, P.reconstruct i r a = g (∑ s : S, f s (a s))) :
    (P.mapAnswerHom f g).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x i r q hrq
  change (∑ s : S, g (f s (P.answer s x (q s)))) = x i
  rw [← map_sum, ← hrec i r, hcorrect.reconstruct_eq x i hrq]

theorem coalitionQuery_mapAnswerHom [Fintype S] {G : Type} [AddCommGroup G]
    (P : Scheme ι S R Q A) (f : S → A → G) (g : G →+ Bool) (T : Finset S) (i : ι) :
    (P.mapAnswerHom f g).coalitionQuery T i = P.coalitionQuery T i := by
  rw [Scheme.coalitionQuery_eq, Scheme.coalitionQuery_eq]
  rfl

theorem IsTPrivate.mapAnswerHom [Fintype S] {G : Type} [AddCommGroup G] {P : Scheme ι S R Q A}
    {t : ℕ} (hprivate : P.IsTPrivate t) (f : S → A → G) (g : G →+ Bool) :
    (P.mapAnswerHom f g).IsTPrivate t := by
  rw [Scheme.isTPrivate_iff]
  intro T hT i i'
  rw [coalitionQuery_mapAnswerHom, coalitionQuery_mapAnswerHom]
  exact hprivate.eval_coalitionQuery_eq T hT i i'

theorem IsPrivate.mapAnswerHom [Fintype S] {G : Type} [AddCommGroup G] {P : Scheme ι S R Q A}
    (hprivate : P.IsPrivate) (f : S → A → G) (g : G →+ Bool) :
    (P.mapAnswerHom f g).IsPrivate :=
  isTPrivate_one_iff.mp ((isTPrivate_one_iff.mpr hprivate).mapAnswerHom f g)

/-- **Proposition 5** [CGKS, Section 4.1, pp. 11–12][ChorGoldreichKushilevitzSudan1998]: given a
scheme `P` on `Option ι` (`n` real positions `some i` plus one dummy zero position `none`) with
one-bit answers and XOR-sum reconstruction, `P.sumChunks m` solves `Fin m × ι` (`m * n` bits) by
running `m` independent instances (querying `some i₀` in chunk `j₀` and the dummy `none` in every
other chunk) and having each server XOR its `m` answer bits into a **single** reply bit. -/
def sumChunks [Fintype S] (m : ℕ) (P : Scheme (Option ι) S R Q Bool) :
    Scheme (Fin m × ι) S Unit (Fin m → Q) Bool where
  query ji := do
    let rqs ← OracleComp.pi fun j : Fin m =>
      P.query (if j = ji.1 then some ji.2 else none)
    pure ((), fun s j => (rqs j).2 s)
  answer s x qs := ∑ j : Fin m,
    P.answer s (fun o => Option.elim o false (fun i => x (j, i))) (qs j)
  reconstruct _ _ a := ∑ s : S, a s

theorem hasXorReconstruct_sumChunks [Fintype S] (m : ℕ) (P : Scheme (Option ι) S R Q Bool) :
    (P.sumChunks m).HasXorReconstruct :=
  fun _ _ _ => rfl

/-- **Correctness of Proposition 5**: in chunk `j = ji.1` the servers' answers sum to `x ji`, and
in every other chunk `j ≠ ji.1` they sum to the dummy zero bit `false`. -/
theorem IsCorrect.sumChunks [Fintype S] (m : ℕ) {P : Scheme (Option ι) S R Q Bool}
    (hcorrect : P.IsCorrect) (hxor : P.HasXorReconstruct) :
    (P.sumChunks m).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x ji _ q hrq
  simp only [Scheme.sumChunks, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq,
    ProbComp.mem_support_pi_iff] at hrq
  obtain ⟨rqs, hrqs, -, rfl⟩ := hrq
  change (∑ s : S, ∑ j : Fin m,
    P.answer s (fun o => Option.elim o false (fun i => x (j, i))) ((rqs j).2 s)) = x ji
  rw [Finset.sum_comm]
  have hchunk (j : Fin m) :
      (∑ s : S, P.answer s (fun o => Option.elim o false (fun i => x (j, i))) ((rqs j).2 s)) =
        if j = ji.1 then x ji else false := by
    rw [← hxor (if j = ji.1 then some ji.2 else none) (rqs j).1,
      hcorrect.reconstruct_eq _ _ (hrqs j)]
    by_cases hj : j = ji.1
    · subst hj
      rcases ji with ⟨j, i⟩
      simp
    · simp [hj]
  simp only [hchunk]
  rw [Finset.sum_eq_single ji.1]
  · simp
  · intro j _ hj
    rw [ite_eq_right hj]
    rfl
  · intro hmem
    exact (hmem (Finset.mem_univ ji.1)).elim

/-- `sumChunks` preserves `t`-privacy for every `t` (and hence single-server `IsPrivate` at
`t = 1`), without any finiteness assumptions on `R` or `Q`. -/
theorem IsTPrivate.sumChunks [Fintype S] (m : ℕ)
    {P : Scheme (Option ι) S R Q Bool} {t : ℕ} (hprivate : P.IsTPrivate t) :
    (P.sumChunks m).IsTPrivate t := by
  rw [Scheme.isTPrivate_iff]
  intro T hT ji ji'
  have hlaw (target : Fin m × ι) :
      ProbComp.eval ((P.sumChunks m).coalitionQuery T target) =
        (ProbComp.eval (OracleComp.pi fun j : Fin m =>
          P.coalitionQuery T (if j = target.1 then some target.2 else none))).map
            (fun f (s : T) j => f j s) := by
    rw [Scheme.eval_coalitionQuery, Scheme.sumChunks, ProbComp.eval_bind]
    simp only [ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    have hmap := ProbComp.eval_pi_map
      (fun j : Fin m => P.query (if j = target.1 then some target.2 else none))
      (fun _ rq (s : T) => rq.2 s)
    simp only [← Scheme.coalitionQuery_eq] at hmap
    rw [hmap, PMF.map_comp]
    rfl
  rw [hlaw ji, hlaw ji']
  congr 1
  exact ProbComp.eval_pi_congr fun _ => hprivate.eval_coalitionQuery_eq T hT _ _

theorem IsPrivate.sumChunks [Fintype S] (m : ℕ)
    {P : Scheme (Option ι) S R Q Bool} (hprivate : P.IsPrivate) :
    (P.sumChunks m).IsPrivate :=
  isTPrivate_one_iff.mp ((isTPrivate_one_iff.mpr hprivate).sumChunks m)

end Scheme

/-! ### Communication bounds and Corollaries 6, 7 and 8 -/

/-- General Proposition 4 communication bound for arbitrary finite answer alphabet `A` (including
non-power-of-two field answers such as `ZMod p`). -/
theorem communication_toBlock_le (S Q A κ : Type) [Fintype S] [Fintype Q] [Fintype A]
    [Fintype κ] [DecidableEq κ] :
    communication S Q (κ → A) ≤
      Fintype.card S *
        (Nat.clog 2 (Fintype.card Q) + Fintype.card κ * Nat.clog 2 (Fintype.card A)) := by
  rw [communication_eq, Fintype.card_fun]
  have hA := Nat.clog_pow_le_mul 2 (Fintype.card A) (Fintype.card κ)
  nlinarith

/-- Proposition 4 multiplies `b`-bit server answers (`|A| = 2 ^ b`) by `|κ|`. -/
theorem communication_toBlock_of_card_answer (S Q A κ : Type) [Fintype S] [Fintype Q] [Fintype A]
    [Fintype κ] [DecidableEq κ] {b : ℕ} (hA : Fintype.card A = 2 ^ b) :
    communication S Q (κ → A) =
      Fintype.card S * (Nat.clog 2 (Fintype.card Q) + Fintype.card κ * b) := by
  refine communication_of_card_answer S Q (κ → A) ?_
  rw [Fintype.card_fun, hA, ← pow_mul, Nat.mul_comm]

/-- Proposition 5 uses `m` queries and a `1`-bit answer per server. -/
theorem communication_sumChunks_le (S Q : Type) [Fintype S] [Fintype Q] (m : ℕ) :
    communication S (Fin m → Q) Bool ≤
      Fintype.card S * (m * Nat.clog 2 (Fintype.card Q) + 1) := by
  rw [communication_eq, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.clog_eq_one le_rfl le_rfl]
  have hQ := Nat.clog_pow_le_mul 2 (Fintype.card Q) m
  nlinarith

/-- **`t`-private Corollary 6** [CGKS, Section 4.1, p. 13][ChorGoldreichKushilevitzSudan1998]:
combining Proposition 5 (`sumChunks`) and Proposition 4 (`toBlock`) preserves `t`-privacy while
achieving `|S| * (m * ⌈log₂ |Q|⌉ + ℓ)` bits for `N ≤ m * n` blocks of `ℓ` bits. -/
theorem hasTPrivateBlockScheme_of_xorReconstruct {S R Q : Type} [Fintype S] [Fintype Q]
    {n m N ℓ t : ℕ} {P : Scheme (Option (Fin n)) S R Q Bool}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hxor : P.HasXorReconstruct)
    (hN : N ≤ m * n) :
    HasTPrivateScheme (Fin N) t (Fintype.card S)
      (Fintype.card S * (m * Nat.clog 2 (Fintype.card Q) + ℓ)) (Fin ℓ → Bool) := by
  let e : Fin N ↪ Fin m × Fin n := (Fin.castLEEmb hN).trans finProdFinEquiv.symm.toEmbedding
  have hB := (((hcorrect.sumChunks m hxor).toBlock (Fin ℓ)).comap e
    (fun _ => false)).hasTPrivateScheme
    (((hprivate.sumChunks m).toBlock (Fin ℓ)).comap e (fun _ => false))
  refine hB.mono ?_
  rw [communication_rows, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hQ := Nat.clog_pow_le_mul 2 (Fintype.card Q) m
  nlinarith

/-- **Corollary 6** [CGKS, Section 4.1, p. 13][ChorGoldreichKushilevitzSudan1998]: combining
Proposition 5 (`sumChunks`) and Proposition 4 (`toBlock`), an XOR-reconstruction single-bit scheme
`P` on `Option (Fin n)` (`n + 1` bits) yields an `ℓ`-bit block scheme for any `N ≤ m * n` blocks
with communication at most `|S| * (m * ⌈log₂ |Q|⌉ + ℓ)`. -/
theorem hasBlockScheme_of_xorReconstruct {S R Q : Type} [Fintype S] [Fintype Q]
    {n m N ℓ : ℕ} {P : Scheme (Option (Fin n)) S R Q Bool}
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) (hxor : P.HasXorReconstruct)
    (hN : N ≤ m * n) :
    HasScheme (Fin N) (Fintype.card S)
      (Fintype.card S * (m * Nat.clog 2 (Fintype.card Q) + ℓ)) (Fin ℓ → Bool) :=
  hasTPrivateScheme_one_iff.mp
    (hasTPrivateBlockScheme_of_xorReconstruct hcorrect (Scheme.isTPrivate_one_iff.mpr hprivate)
      hxor hN)

/-- **Corollary 7** [CGKS, Section 4.2, p. 13][ChorGoldreichKushilevitzSudan1998]: when `n ≤ ℓ`,
two servers retrieve an `ℓ`-bit block from `n` blocks with at most `4 * ℓ` bits of communication
(a constant factor of `4` over the block length). -/
theorem hasBlockScheme_two_of_le {n ℓ : ℕ} (h : n ≤ ℓ) :
    HasScheme (Fin n) 2 (4 * ℓ) (Fin ℓ → Bool) := by
  have hB := ((isCorrect_twoServer (ι := Fin n)).toBlock (Fin ℓ)).hasScheme
    ((isPrivate_twoServer (ι := Fin n)).toBlock (Fin ℓ))
  rw [Fintype.card_bool, communication_twoServer_rows, Fintype.card_fin, Fintype.card_fin] at hB
  exact hB.mono (by omega)

/-- **Corollary 8** [CGKS, Section 4.2, p. 13][ChorGoldreichKushilevitzSudan1998]: when `n ≤ m ^ 2`
and `2 * m ≤ ℓ`, four servers (`d = 2` subcube PIR lifted via Proposition 4) retrieve an `ℓ`-bit
block from `n` blocks with at most `8 * ℓ` bits of communication. -/
theorem hasBlockScheme_four_of_le_sq {n m ℓ : ℕ} (hn : n ≤ m * m) (hm : 2 * m ≤ ℓ) :
    HasScheme (Fin n) 4 (8 * ℓ) (Fin ℓ → Bool) := by
  let e : Fin n ↪ (Fin 2 → Fin m) :=
    (Fin.castLEEmb (by simpa [pow_two] using hn)).trans finFunctionFinEquiv.symm.toEmbedding
  have hcube := ((isCorrect_cube (D := Fin 2) (ι := Fin m)).comap e false).toBlock (Fin ℓ)
  have hpriv := ((isPrivate_cube (D := Fin 2) (ι := Fin m)).comap e false).toBlock (Fin ℓ)
  have hB := hcube.hasScheme hpriv
  have hcardS : Fintype.card (Fin 2 → Bool) = 4 := by decide
  rw [hcardS, communication_rows] at hB
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul,
    Nat.clog_pow 2 _ (by norm_num)] at hB
  exact hB.mono (by omega)

/-- Closed-form specialization of Corollary 8 for `n ≤ (ℓ / 2) ^ 2` (replacing the paper's
unrounded `n ≤ ℓ ^ 2 / 4`, and matching it whenever `ℓ` is even). -/
theorem hasBlockScheme_four_of_le_half_sq {n ℓ : ℕ} (h : n ≤ (ℓ / 2) ^ 2) :
    HasScheme (Fin n) 4 (8 * ℓ) (Fin ℓ → Bool) :=
  hasBlockScheme_four_of_le_sq (m := ℓ / 2) (by simpa [pow_two] using h) (Nat.mul_div_le ℓ 2)

end Cslib.Crypto.Protocols.PIR

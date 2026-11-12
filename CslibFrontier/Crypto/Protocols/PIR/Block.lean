/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Collusion
public import CslibFrontier.Crypto.Protocols.PIR.Cube
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Private block retrieval

[Chor, Goldreich, Kushilevitz and Sudan, Section 4][ChorGoldreichKushilevitzSudan1998] generalizes
private information retrieval from single bits to databases of `n` blocks of `ℓ` bits each
(`PIR_k(n, ℓ)`), hiding the block index `i` while amortizing communication across the block.

* **Block schemes (`PIR.BlockScheme`).** `BlockScheme ι β S R Q A` retrieves an entire block
  `x i : β` from `x : ι → β` replicated across servers `S`, with `IsCorrect`, `IsPrivate`,
  `IsTPrivate`, restriction `comap`, and bit-scheme projection `toBitScheme` reducing full-coalition
  and single-server `n · ℓ`-bit lower bounds (`BlockScheme.card_mul_le_communication_of_card_le`,
  `BlockScheme.card_mul_le_communication`, attained by `PIR.blockDownload`) to single-bit PIR.
* **Bit-to-block transformation (`Scheme.toBlock`, Proposition 4, Section 4.1).** Sending one query
  of a single-bit scheme `P` and having each server answer once for every coordinate `b : κ` of the
  `ℓ`-bit block (`κ → Bool`, `ℓ = |κ|`) multiplies only the server-to-user communication by `ℓ`,
  preserving `IsCorrect`, `IsPrivate`, and `IsTPrivate`.
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
  (Corollary 8, `hasBlockScheme_four_of_le_sq`, `hasBlockScheme_four_of_le_half_sq`; the integer
  subcube side `m` refines the paper's real `√n ≤ ℓ / 2` bound `n ≤ ℓ ^ 2 / 4`, agreeing with it
  whenever `ℓ` is even).

## Main definitions

* `Cslib.Crypto.Protocols.PIR.BlockScheme`,
  `Cslib.Crypto.Protocols.PIR.HasBlockScheme`,
  `Cslib.Crypto.Protocols.PIR.HasTPrivateBlockScheme`: one-round block PIR schemes and existence
  predicates.
* `Cslib.Crypto.Protocols.PIR.BlockScheme.toBitScheme`: view an `ℓ`-bit block scheme on `ι` as a
  single-bit scheme on `ι × κ`.
* `Cslib.Crypto.Protocols.PIR.blockDownload`: single-server whole-database block download.
* `Cslib.Crypto.Protocols.PIR.Scheme.toBlock`: Proposition 4's bit-to-block transformation.
* `Cslib.Crypto.Protocols.PIR.Scheme.HasXorReconstruct`,
  `Cslib.Crypto.Protocols.PIR.Scheme.mapAnswerHom`,
  `Cslib.Crypto.Protocols.PIR.Scheme.sumChunks`: Proposition 5's XOR-sum predicate, group
  homomorphism reduction, and `m`-chunk query-expanding / answer-compressing transformation.

## Main results

* `Cslib.Crypto.Protocols.PIR.BlockScheme.card_mul_le_communication_of_card_le`,
  `Cslib.Crypto.Protocols.PIR.BlockScheme.card_mul_le_communication`,
  `Cslib.Crypto.Protocols.PIR.hasBlockScheme_one_iff`: full-coalition and single-server block
  retrieval require `|ι| * |κ|` bits.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.toBlock`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.toBlock`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate.toBlock`,
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
  6, 7 and 8); numbering of the authors' journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability

/-! ### Block PIR schemes -/

/-- A one-round private block retrieval scheme for databases `x : ι → β` of blocks in `β` held by
servers `S`, with user state `R`, queries `Q` and answers `A`
[CGKS, Section 4][ChorGoldreichKushilevitzSudan1998]. -/
structure BlockScheme (ι β S R Q A : Type) where
  /-- The user's query generator: for the block index `i`, a retained state and server queries. -/
  query : ι → ProbComp (R × (S → Q))
  /-- The answer of server `s`, holding the block database `x`, to a query. -/
  answer : S → (ι → β) → Q → A
  /-- The user's reconstruction of the block `x i` from the retained state and the answers. -/
  reconstruct : ι → R → (S → A) → β

namespace BlockScheme

variable {ι β S R Q A : Type}

section Defs

variable (P : BlockScheme ι β S R Q A)

/-- The user's output block on database `x` and block index `i`. -/
def run (x : ι → β) (i : ι) : ProbComp β := do
  let (r, q) ← P.query i
  pure (P.reconstruct i r fun s => P.answer s x (q s))

/-- The query received by server `s` when the user requests block `i`. -/
def serverQuery (s : S) (i : ι) : ProbComp Q :=
  (fun (_, q) => q s) <$> P.query i

/-- The joint query marginal received by a coalition `T : Finset S` on block index `i`. -/
def coalitionQuery (T : Finset S) (i : ι) : ProbComp (T → Q) :=
  (fun (_, q) (s : T) => q s) <$> P.query i

/-- Perfect correctness: on every block database `x` and index `i`, the user recovers `x i` with
probability one. -/
def IsCorrect : Prop :=
  ∀ x i, ProbComp.eval (P.run x i) = PMF.pure (x i)

/-- Perfect single-server privacy: each server's query law is independent of the block index `i`. -/
def IsPrivate : Prop :=
  ∀ s i i', ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i')

/-- Perfect `t`-privacy for block retrieval: every coalition of at most `t` servers sees an
index-independent joint query distribution. -/
def IsTPrivate (t : ℕ) : Prop :=
  ∀ T : Finset S, T.card ≤ t → ∀ i i',
    ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i')

theorem eval_run (x : ι → β) (i : ι) :
    ProbComp.eval (P.run x i) =
      (ProbComp.eval (P.query i)).map
        (fun rq => P.reconstruct i rq.1 fun s => P.answer s x (rq.2 s)) := by
  rw [run, ProbComp.eval_bind]
  rfl

theorem eval_serverQuery (s : S) (i : ι) :
    ProbComp.eval (P.serverQuery s i) = (ProbComp.eval (P.query i)).map (fun rq => rq.2 s) := by
  rw [serverQuery, ProbComp.eval_map]

theorem eval_coalitionQuery (T : Finset S) (i : ι) :
    ProbComp.eval (P.coalitionQuery T i) =
      (ProbComp.eval (P.query i)).map (fun (_, q) (s : T) => q s) := by
  rw [coalitionQuery, ProbComp.eval_map]

theorem isPrivate_iff :
    P.IsPrivate ↔
      ∀ s i i', ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i') := by
  rw [IsPrivate]

theorem isTPrivate_iff (t : ℕ) :
    P.IsTPrivate t ↔ ∀ T : Finset S, T.card ≤ t → ∀ i i',
      ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i') := by
  rw [IsTPrivate]

theorem isCorrect_iff :
    P.IsCorrect ↔ ∀ x i r q, (r, q) ∈ (ProbComp.eval (P.query i)).support →
      P.reconstruct i r (fun s => P.answer s x (q s)) = x i := by
  refine forall_congr' fun x => forall_congr' fun i => ⟨fun h r q hrq => ?_, fun h => ?_⟩
  · have hsupp := congrArg PMF.support ((P.eval_run x i).symm.trans h)
    rw [PMF.support_map, PMF.support_pure] at hsupp
    exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp hsupp _).mp (Set.mem_image_of_mem _ hrq))
  · rw [eval_run, Cslib.Probability.PMF.map_congr_on_support _ _ (Function.const _ (x i))
      fun rq hrq => h rq.1 rq.2 hrq, PMF.map_const]

end Defs

variable {P : BlockScheme ι β S R Q A}

theorem IsCorrect.reconstruct_eq (h : P.IsCorrect) (x : ι → β) (i : ι) {r : R} {q : S → Q}
    (hrq : (r, q) ∈ (ProbComp.eval (P.query i)).support) :
    P.reconstruct i r (fun s => P.answer s x (q s)) = x i :=
  P.isCorrect_iff.mp h x i r q hrq

theorem IsPrivate.eval_serverQuery_eq (h : P.IsPrivate) (s : S) (i i' : ι) :
    ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i') :=
  h s i i'

theorem IsTPrivate.eval_coalitionQuery_eq {t : ℕ} (h : P.IsTPrivate t) (T : Finset S)
    (hT : T.card ≤ t) (i i' : ι) :
    ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i') :=
  h T hT i i'

private def queryScheme (P : BlockScheme ι β S R Q A) : Scheme ι S R Q Unit where
  query := P.query
  answer _ _ _ := ()
  reconstruct _ _ _ := false

/-- `1`-privacy for block schemes agrees with `IsPrivate`. -/
theorem isTPrivate_one_iff : P.IsTPrivate 1 ↔ P.IsPrivate := by
  have hT : P.IsTPrivate 1 ↔ (queryScheme P).IsTPrivate 1 := by
    simp only [isTPrivate_iff, Scheme.isTPrivate_iff, eval_coalitionQuery,
      Scheme.eval_coalitionQuery, queryScheme]
  have h1 : P.IsPrivate ↔ (queryScheme P).IsPrivate := by
    simp only [isPrivate_iff, Scheme.isPrivate_iff, eval_serverQuery,
      Scheme.eval_serverQuery, queryScheme]
  rw [hT, h1, Scheme.isTPrivate_one_iff]

/-- Restrict a block scheme along an embedding `e : ι ↪ ι'`, padding outside `e` with `pad`. -/
noncomputable def comap {ι' : Type} (P : BlockScheme ι' β S R Q A) (e : ι ↪ ι') (pad : β) :
    BlockScheme ι β S R Q A where
  query i := P.query (e i)
  answer s x q := P.answer s (Function.extend e x fun _ => pad) q
  reconstruct i r a := P.reconstruct (e i) r a

theorem IsCorrect.comap {ι' : Type} {P : BlockScheme ι' β S R Q A} (h : P.IsCorrect)
    (e : ι ↪ ι') (pad : β) : (P.comap e pad).IsCorrect := fun x i => by
  have := h (Function.extend e x fun _ => pad) (e i)
  rwa [e.injective.extend_apply] at this

theorem IsPrivate.comap {ι' : Type} {P : BlockScheme ι' β S R Q A} (h : P.IsPrivate)
    (e : ι ↪ ι') (pad : β) : (P.comap e pad).IsPrivate :=
  fun s i i' => h s (e i) (e i')

theorem IsTPrivate.comap {ι' : Type} {P : BlockScheme ι' β S R Q A} {t : ℕ} (h : P.IsTPrivate t)
    (e : ι ↪ ι') (pad : β) : (P.comap e pad).IsTPrivate t :=
  fun T hT i i' => h T hT (e i) (e i')

/-! ### Reduction of block lower bounds to single-bit PIR -/

/-- View a block scheme retrieving `κ → Bool` blocks as a single-bit scheme on `ι × κ` that sends
the block query for `ib.1` and extracts bit `ib.2` from the reconstructed block. -/
def toBitScheme {κ : Type} (P : BlockScheme ι (κ → Bool) S R Q A) :
    Scheme (ι × κ) S R Q A where
  query ib := P.query ib.1
  answer s x q := P.answer s (fun i b => x (i, b)) q
  reconstruct ib r a := P.reconstruct ib.1 r a ib.2

theorem IsCorrect.toBitScheme {κ : Type} {P : BlockScheme ι (κ → Bool) S R Q A}
    (h : P.IsCorrect) : P.toBitScheme.IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x ib r q hrq
  exact congrFun (h.reconstruct_eq (fun i b => x (i, b)) ib.1 hrq) ib.2

theorem IsTPrivate.toBitScheme {κ : Type} {P : BlockScheme ι (κ → Bool) S R Q A} {t : ℕ}
    (h : P.IsTPrivate t) : P.toBitScheme.IsTPrivate t := by
  rw [Scheme.isTPrivate_iff]
  intro T hT ib ib'
  rw [Scheme.eval_coalitionQuery, Scheme.eval_coalitionQuery]
  dsimp only [BlockScheme.toBitScheme]
  rw [← P.eval_coalitionQuery, ← P.eval_coalitionQuery]
  exact h.eval_coalitionQuery_eq T hT ib.1 ib'.1

theorem IsPrivate.toBitScheme {κ : Type} {P : BlockScheme ι (κ → Bool) S R Q A}
    (h : P.IsPrivate) : P.toBitScheme.IsPrivate :=
  Scheme.isTPrivate_one_iff.mp ((isTPrivate_one_iff.mpr h).toBitScheme)

/-- Full-coalition (`|S| ≤ t`) private block retrieval of `|ι|` blocks of `|κ|` bits requires at
least `|ι| * |κ|` bits of communication. -/
theorem card_mul_le_communication_of_card_le {κ : Type} [Fintype S] [Fintype ι] [Fintype κ]
    [Fintype Q] [Fintype A] {P : BlockScheme ι (κ → Bool) S R Q A} {t : ℕ}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    Fintype.card ι * Fintype.card κ ≤ communication S Q A := by
  simpa only [Fintype.card_prod] using
    P.toBitScheme.card_le_communication_of_card_le hcorrect.toBitScheme hprivate.toBitScheme hcard

/-- One-server private block retrieval of `|ι|` blocks of `|κ|` bits requires at least `|ι| * |κ|`
bits of communication. -/
theorem card_mul_le_communication {κ : Type} [Fintype S] [Unique S] [Fintype ι] [Fintype κ]
    [Fintype Q] [Fintype A] {P : BlockScheme ι (κ → Bool) S R Q A}
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    Fintype.card ι * Fintype.card κ ≤ communication S Q A :=
  card_mul_le_communication_of_card_le hcorrect (isTPrivate_one_iff.mpr hprivate)
    (by simp [Fintype.card_unique])

end BlockScheme

/-- The trivial one-server block scheme sending the entire database `ι → β`. -/
def blockDownload (ι β : Type) : BlockScheme ι β Unit Unit Unit (ι → β) where
  query _ := pure ((), fun _ => ())
  answer _ x _ := x
  reconstruct i _ a := a () i

theorem isCorrect_blockDownload (ι β : Type) : (blockDownload ι β).IsCorrect :=
  (blockDownload ι β).isCorrect_iff.mpr fun _ _ _ _ _ => rfl

theorem isPrivate_blockDownload (ι β : Type) : (blockDownload ι β).IsPrivate :=
  fun _ _ _ => rfl

/-- Some `k`-server block scheme for `ι → β` is perfectly correct, perfectly private, and
communicates at most `c` bits. -/
def HasBlockScheme (ι β : Type) (k c : ℕ) : Prop :=
  ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : BlockScheme ι β S R Q A),
    P.IsCorrect ∧ P.IsPrivate ∧ Fintype.card S = k ∧ communication S Q A ≤ c

/-- Some `k`-server block scheme for `ι → β` is perfectly correct, perfectly `t`-private, and
communicates at most `c` bits. -/
def HasTPrivateBlockScheme (ι β : Type) (t k c : ℕ) : Prop :=
  ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : BlockScheme ι β S R Q A),
    P.IsCorrect ∧ P.IsTPrivate t ∧ Fintype.card S = k ∧ communication S Q A ≤ c

theorem BlockScheme.IsCorrect.hasBlockScheme {ι β S R Q A : Type} [Fintype S] [Fintype Q]
    [Fintype A] {P : BlockScheme ι β S R Q A} (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    HasBlockScheme ι β (Fintype.card S) (communication S Q A) :=
  ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, rfl, le_rfl⟩

theorem BlockScheme.IsCorrect.hasTPrivateBlockScheme {ι β S R Q A : Type} [Fintype S] [Fintype Q]
    [Fintype A] {P : BlockScheme ι β S R Q A} {t : ℕ}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) :
    HasTPrivateBlockScheme ι β t (Fintype.card S) (communication S Q A) :=
  ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, rfl, le_rfl⟩

theorem HasBlockScheme.mono {ι β : Type} {k c c' : ℕ} (h : HasBlockScheme ι β k c) (hc : c ≤ c') :
    HasBlockScheme ι β k c' := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := h
  exact ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm.trans hc⟩

theorem HasTPrivateBlockScheme.mono {ι β : Type} {t k c c' : ℕ}
    (h : HasTPrivateBlockScheme ι β t k c) (hc : c ≤ c') :
    HasTPrivateBlockScheme ι β t k c' := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := h
  exact ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm.trans hc⟩

theorem hasBlockScheme_iff {ι β : Type} {k c : ℕ} :
    HasBlockScheme ι β k c ↔
      ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A)
        (P : BlockScheme ι β S R Q A),
        P.IsCorrect ∧ P.IsPrivate ∧ Fintype.card S = k ∧ communication S Q A ≤ c := by
  rw [HasBlockScheme]

theorem hasTPrivateBlockScheme_iff {ι β : Type} {t k c : ℕ} :
    HasTPrivateBlockScheme ι β t k c ↔
      ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A)
        (P : BlockScheme ι β S R Q A),
        P.IsCorrect ∧ P.IsTPrivate t ∧ Fintype.card S = k ∧ communication S Q A ≤ c := by
  rw [HasTPrivateBlockScheme]

theorem hasTPrivateBlockScheme_one_iff {ι β : Type} {k c : ℕ} :
    HasTPrivateBlockScheme ι β 1 k c ↔ HasBlockScheme ι β k c := by
  simp only [hasTPrivateBlockScheme_iff, hasBlockScheme_iff, BlockScheme.isTPrivate_one_iff]

/-- **One-server block retrieval needs exactly `|ι| * |κ|` bits.** -/
theorem hasBlockScheme_one_iff (ι κ : Type) [Fintype ι] [Fintype κ] (c : ℕ) :
    HasBlockScheme ι (κ → Bool) 1 c ↔ Fintype.card ι * Fintype.card κ ≤ c := by
  classical
  constructor
  · rintro ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩
    let : Unique S := (Fintype.card_eq_one_iff_nonempty_unique.mp hk).some
    exact (P.card_mul_le_communication hcorrect hprivate).trans hcomm
  · intro hc
    have hdl := (isCorrect_blockDownload ι (κ → Bool)).hasBlockScheme
      (isPrivate_blockDownload ι (κ → Bool))
    rw [Fintype.card_unit,
      communication_of_card_answer Unit Unit (ι → κ → Bool)
        (by rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, ← pow_mul,
          Nat.mul_comm (Fintype.card κ)]),
      Fintype.card_unit, Nat.clog_one_right, zero_add, one_mul] at hdl
    exact hdl.mono hc

/-! ### Proposition 4: single-bit PIR to `ℓ`-bit block PIR -/

namespace Scheme

variable {ι S R Q A : Type}

/-- **Proposition 4** [CGKS, Section 4.1, p. 11][ChorGoldreichKushilevitzSudan1998]: lift a
single-bit scheme `P` to retrieve `κ`-indexed blocks `κ → Bool` by sending one query of `P` for
the block index `i` and answering it once for each bit coordinate `b : κ` of the block. -/
def toBlock (κ : Type) (P : Scheme ι S R Q A) : BlockScheme ι (κ → Bool) S R Q (κ → A) where
  query i := P.query i
  answer s x q b := P.answer s (fun i' => x i' b) q
  reconstruct i r a b := P.reconstruct i r (fun s => a s b)

theorem IsCorrect.toBlock (κ : Type) {P : Scheme ι S R Q A} (h : P.IsCorrect) :
    (P.toBlock κ).IsCorrect := by
  rw [BlockScheme.isCorrect_iff]
  intro x i r q hrq
  funext b
  exact h.reconstruct_eq (fun i' => x i' b) i hrq

theorem IsPrivate.toBlock (κ : Type) {P : Scheme ι S R Q A} (h : P.IsPrivate) :
    (P.toBlock κ).IsPrivate := by
  rw [BlockScheme.isPrivate_iff]
  intro s i i'
  rw [BlockScheme.eval_serverQuery, BlockScheme.eval_serverQuery]
  dsimp only [Scheme.toBlock]
  rw [← P.eval_serverQuery, ← P.eval_serverQuery]
  exact h.eval_serverQuery_eq s i i'

theorem IsTPrivate.toBlock (κ : Type) {P : Scheme ι S R Q A} {t : ℕ} (h : P.IsTPrivate t) :
    (P.toBlock κ).IsTPrivate t := by
  rw [BlockScheme.isTPrivate_iff]
  intro T hT i i'
  rw [BlockScheme.eval_coalitionQuery, BlockScheme.eval_coalitionQuery]
  dsimp only [Scheme.toBlock]
  rw [← P.eval_coalitionQuery, ← P.eval_coalitionQuery]
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
  have hQ : Nat.clog 2 (Fintype.card Q ^ m) ≤ m * Nat.clog 2 (Fintype.card Q) := by
    refine Nat.clog_le_of_le_pow ?_
    calc Fintype.card Q ^ m ≤ (2 ^ Nat.clog 2 (Fintype.card Q)) ^ m :=
          Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card Q)) m
      _ = 2 ^ (m * Nat.clog 2 (Fintype.card Q)) := by rw [← pow_mul, Nat.mul_comm]
  nlinarith

/-- **`t`-private Corollary 6** [CGKS, Section 4.1, p. 13][ChorGoldreichKushilevitzSudan1998]:
combining Proposition 5 (`sumChunks`) and Proposition 4 (`toBlock`) preserves `t`-privacy while
achieving `|S| * (m * ⌈log₂ |Q|⌉ + ℓ)` bits for `N ≤ m * n` blocks of `ℓ` bits. -/
theorem hasTPrivateBlockScheme_of_xorReconstruct {S R Q : Type} [Fintype S] [Fintype Q]
    {n m N ℓ t : ℕ} {P : Scheme (Option (Fin n)) S R Q Bool}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hxor : P.HasXorReconstruct)
    (hN : N ≤ m * n) :
    HasTPrivateBlockScheme (Fin N) (Fin ℓ → Bool) t (Fintype.card S)
      (Fintype.card S * (m * Nat.clog 2 (Fintype.card Q) + ℓ)) := by
  let e : Fin N ↪ Fin m × Fin n := (Fin.castLEEmb hN).trans finProdFinEquiv.symm.toEmbedding
  have hB := (((hcorrect.sumChunks m hxor).toBlock (Fin ℓ)).comap e
    (fun _ => false)).hasTPrivateBlockScheme
    (((hprivate.sumChunks m).toBlock (Fin ℓ)).comap e (fun _ => false))
  refine hB.mono ?_
  have hchunks := communication_sumChunks_le S Q m
  rw [communication_eq, Fintype.card_bool, Nat.clog_eq_one le_rfl le_rfl] at hchunks
  rw [communication_rows, Fintype.card_fin]
  nlinarith

/-- **Corollary 6** [CGKS, Section 4.1, p. 13][ChorGoldreichKushilevitzSudan1998]: combining
Proposition 5 (`sumChunks`) and Proposition 4 (`toBlock`), an XOR-reconstruction single-bit scheme
`P` on `Option (Fin n)` (`n + 1` bits) yields an `ℓ`-bit block scheme for any `N ≤ m * n` blocks
with communication at most `|S| * (m * ⌈log₂ |Q|⌉ + ℓ)`. -/
theorem hasBlockScheme_of_xorReconstruct {S R Q : Type} [Fintype S] [Fintype Q]
    {n m N ℓ : ℕ} {P : Scheme (Option (Fin n)) S R Q Bool}
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) (hxor : P.HasXorReconstruct)
    (hN : N ≤ m * n) :
    HasBlockScheme (Fin N) (Fin ℓ → Bool) (Fintype.card S)
      (Fintype.card S * (m * Nat.clog 2 (Fintype.card Q) + ℓ)) :=
  hasTPrivateBlockScheme_one_iff.mp
    (hasTPrivateBlockScheme_of_xorReconstruct hcorrect (Scheme.isTPrivate_one_iff.mpr hprivate)
      hxor hN)

/-- **Corollary 7** [CGKS, Section 4.2, p. 13][ChorGoldreichKushilevitzSudan1998]: when `n ≤ ℓ`,
two servers retrieve an `ℓ`-bit block from `n` blocks with at most `4 * ℓ` bits of communication
(a constant factor of `4` over the block length). -/
theorem hasBlockScheme_two_of_le {n ℓ : ℕ} (h : n ≤ ℓ) :
    HasBlockScheme (Fin n) (Fin ℓ → Bool) 2 (4 * ℓ) := by
  have hB := ((isCorrect_twoServer (ι := Fin n)).toBlock (Fin ℓ)).hasBlockScheme
    ((isPrivate_twoServer (ι := Fin n)).toBlock (Fin ℓ))
  rw [Fintype.card_bool, communication_twoServer_rows, Fintype.card_fin, Fintype.card_fin] at hB
  exact hB.mono (by omega)

/-- **Corollary 8** [CGKS, Section 4.2, p. 13][ChorGoldreichKushilevitzSudan1998]: when `n ≤ m ^ 2`
and `2 * m ≤ ℓ`, four servers (`d = 2` subcube PIR lifted via Proposition 4) retrieve an `ℓ`-bit
block from `n` blocks with at most `8 * ℓ` bits of communication. -/
theorem hasBlockScheme_four_of_le_sq {n m ℓ : ℕ} (hn : n ≤ m * m) (hm : 2 * m ≤ ℓ) :
    HasBlockScheme (Fin n) (Fin ℓ → Bool) 4 (8 * ℓ) := by
  let e : Fin n ↪ (Fin 2 → Fin m) :=
    (Fin.castLEEmb (by simpa [pow_two] using hn)).trans finFunctionFinEquiv.symm.toEmbedding
  have hcube := ((isCorrect_cube (D := Fin 2) (ι := Fin m)).comap e).toBlock (Fin ℓ)
  have hpriv := ((isPrivate_cube (D := Fin 2) (ι := Fin m)).comap e).toBlock (Fin ℓ)
  have hB := hcube.hasBlockScheme hpriv
  have hcardS : Fintype.card (Fin 2 → Bool) = 4 := by decide
  rw [hcardS, communication_rows] at hB
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul,
    Nat.clog_pow 2 _ (by norm_num)] at hB
  exact hB.mono (by omega)

/-- Closed-form specialization of Corollary 8 for `n ≤ (ℓ / 2) ^ 2` (matching `n ≤ ℓ ^ 2 / 4`
whenever `ℓ` is even). -/
theorem hasBlockScheme_four_of_le_half_sq {n ℓ : ℕ} (h : n ≤ (ℓ / 2) ^ 2) :
    HasBlockScheme (Fin n) (Fin ℓ → Bool) 4 (8 * ℓ) :=
  hasBlockScheme_four_of_le_sq (m := ℓ / 2) (by simpa [pow_two] using h) (Nat.mul_div_le ℓ 2)

end Cslib.Crypto.Protocols.PIR

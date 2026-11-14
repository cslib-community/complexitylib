/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Collusion
import CslibFrontier.Crypto.Protocols.PIR.SingleServer
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Support

/-!
# Private information retrieval with per-server query and answer types

`PIR.Scheme` assigns a single query alphabet `Q` and answer alphabet `A` to all servers `s : S`,
charging `|S| · (⌈log₂ |Q|⌉ + ⌈log₂ |A|⌉)` bits (`PIR.communication`). In several constructions of
[Chor, Goldreich, Kushilevitz and Sudan][ChorGoldreichKushilevitzSudan1998] — notably the general
covering-code Theorem 1 of Section 3.3 (p. 9, Footnote 1), where server `s` emulates `m_s` assigned
non-codeword neighbours and replies with `1 + m_s · ℓ` bits — different servers send answers of
different fixed lengths.

This module introduces `PIR.IndexedScheme ι S R Q A β` (with `Q A : S → Type` and default payload
`β = Bool`) and its per-server fixed-length bit count
`PIR.indexedCommunication S Q A = ∑ s : S, (⌈log₂ |Q s|⌉ + ⌈log₂ |A s|⌉)`:

* **Uniform embedding (`Scheme.toIndexed`).** Every uniform `P : Scheme ι S R Q A β` embeds into
  `IndexedScheme ι S R (fun _ => Q) (fun _ => A) β` with identical run and query distributions and
  `indexedCommunication S (fun _ => Q) (fun _ => A) = communication S Q A`
  (`indexedCommunication_const`).
* **Dependent-sum reduction to `PIR.Scheme` (`IndexedScheme.toSigmaScheme`).** Embedding per-server
  messages into `Σ s, Q s` and `Σ s, A s` preserves `IsCorrect`, `IsPrivate` and `IsTPrivate` via
  `Probability.PMF.map_injective`, transferring coalition-privacy characterizations and the
  full-coalition / single-server injectivity lower bounds
  (`card_le_indexedCommunication_of_card_le`, `card_le_indexedCommunication`,
  `hasIndexedScheme_one_iff`) from `PIR.Collusion` and `PIR.SingleServer` without duplicating their
  proofs.
* **Transformations (`IndexedScheme.rows`, `IndexedScheme.comap`).** Matrix row repetition and index
  embeddings extend directly to per-server message families.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.IndexedScheme`: one-round schemes with server-indexed query and answer
  types `Q A : S → Type`.
* `Cslib.Crypto.Protocols.PIR.indexedCommunication`: sum of per-server query and answer bit widths.
* `Cslib.Crypto.Protocols.PIR.Scheme.toIndexed`: view a uniform `Scheme` as an `IndexedScheme`.
* `Cslib.Crypto.Protocols.PIR.HasIndexedScheme`,
  `Cslib.Crypto.Protocols.PIR.HasTPrivateIndexedScheme`: existence of correct, (coalition-)private
  per-server schemes within a total bit budget.

## Main results

* `Cslib.Crypto.Protocols.PIR.indexedCommunication_const`: agrees with `PIR.communication` on
  constant message families.
* `Cslib.Crypto.Protocols.PIR.IndexedScheme.isTPrivate_one_iff`,
  `Cslib.Crypto.Protocols.PIR.IndexedScheme.isTPrivate_iff_tuple`: coalition-privacy equivalences.
* `Cslib.Crypto.Protocols.PIR.IndexedScheme.exists_injective_answers_of_card_le`,
  `Cslib.Crypto.Protocols.PIR.IndexedScheme.card_le_indexedCommunication_of_card_le`: full-coalition
  `|S| ≤ t` forces `2 ^ |ι| ≤ ∏ s, |A s|` and `|ι| ≤ indexedCommunication S Q A`.
* `Cslib.Crypto.Protocols.PIR.hasIndexedScheme_one_iff`: a single server still needs `|ι|` bits even
  with server-indexed message types.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Sections 2.1, 2.2, 3.3 and 5.1; numbering of the
  authors' journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability

/-- A one-round private information retrieval scheme with server-indexed query types `Q : S → Type`
and answer types `A : S → Type`, for databases `x : ι → β` (by default `β = Bool`)
[CGKS, Definition 1 and Section 3.3][ChorGoldreichKushilevitzSudan1998]. -/
structure IndexedScheme (ι S R : Type) (Q A : S → Type) (β : Type := Bool) where
  /-- The user's query generator: for the index `i`, a retained state and one query `q s : Q s` per
  server `s`. -/
  query : ι → ProbComp (R × ((s : S) → Q s))
  /-- The deterministic answer of server `s`, holding database `x`, to its query `q : Q s`. -/
  answer : (s : S) → (ι → β) → Q s → A s
  /-- The user's reconstruction of `x i` from the retained state and the servers' answers. -/
  reconstruct : ι → R → ((s : S) → A s) → β

/-- Total fixed-length communication cost of an `IndexedScheme`: the sum over all servers `s : S` of
the binary encoding length `⌈log₂ |Q s|⌉ + ⌈log₂ |A s|⌉` of server `s`'s query and answer. -/
def indexedCommunication (S : Type) [Fintype S] (Q A : S → Type)
    [∀ s, Fintype (Q s)] [∀ s, Fintype (A s)] : ℕ :=
  ∑ s : S, (Nat.clog 2 (Fintype.card (Q s)) + Nat.clog 2 (Fintype.card (A s)))

theorem indexedCommunication_eq (S : Type) [Fintype S] (Q A : S → Type)
    [∀ s, Fintype (Q s)] [∀ s, Fintype (A s)] :
    indexedCommunication S Q A =
      ∑ s : S, (Nat.clog 2 (Fintype.card (Q s)) + Nat.clog 2 (Fintype.card (A s))) := by
  rw [indexedCommunication]

/-- On constant query and answer types, `indexedCommunication` coincides with `PIR.communication`.
-/
@[simp] theorem indexedCommunication_const (S Q A : Type) [Fintype S] [Fintype Q] [Fintype A] :
    indexedCommunication S (fun _ => Q) (fun _ => A) = communication S Q A := by
  rw [indexedCommunication_eq, communication_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- When server `s`'s answers have cardinality `2 ^ (aBits s)`, its answer contributes `aBits s`
bits to `indexedCommunication`. -/
theorem indexedCommunication_of_card_answer (S : Type) [Fintype S] (Q A : S → Type)
    [∀ s, Fintype (Q s)] [∀ s, Fintype (A s)] {aBits : S → ℕ}
    (hA : ∀ s, Fintype.card (A s) = 2 ^ aBits s) :
    indexedCommunication S Q A =
      ∑ s : S, (Nat.clog 2 (Fintype.card (Q s)) + aBits s) := by
  rw [indexedCommunication_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hA s, Nat.clog_pow 2 _ (by norm_num)]

/-- Repeating single-bit per-server answers across rows `ρ` multiplies each server's answer cost by
`|ρ|`. -/
theorem indexedCommunication_rows (S : Type) [Fintype S] (Q : S → Type) [∀ s, Fintype (Q s)]
    (ρ : Type) [Fintype ρ] [DecidableEq ρ] :
    indexedCommunication S Q (fun _ => ρ → Bool) =
      ∑ s : S, (Nat.clog 2 (Fintype.card (Q s)) + Fintype.card ρ) :=
  indexedCommunication_of_card_answer S Q (fun _ => ρ → Bool) fun _ => by
    rw [Fintype.card_fun, Fintype.card_bool]

namespace IndexedScheme

variable {ι S R β : Type} {Q A : S → Type}

section Defs

variable (P : IndexedScheme ι S R Q A β)

/-- Run `P` on database `x` and target index `i`. -/
def run (x : ι → β) (i : ι) : ProbComp β := do
  let (r, q) ← P.query i
  pure (P.reconstruct i r fun s => P.answer s x (q s))

/-- The marginal query received by server `s` when the user requests index `i`. -/
def serverQuery (s : S) (i : ι) : ProbComp (Q s) :=
  (fun ⟨_, q⟩ => q s) <$> P.query i

/-- The joint query marginal seen by a coalition `T : Finset S` when the user requests `i`. -/
def coalitionQuery (T : Finset S) (i : ι) : ProbComp ((s : T) → Q s.1) :=
  (fun ⟨_, q⟩ (s : T) => q s.1) <$> P.query i

/-- The joint query marginal seen by an indexed tuple `servers : τ → S` of servers. -/
def tupleQuery {τ : Type} (servers : τ → S) (i : ι) : ProbComp ((j : τ) → Q (servers j)) :=
  (fun ⟨_, q⟩ j => q (servers j)) <$> P.query i

/-- Perfect correctness: on every database and index, `P.run x i` outputs `x i` with probability 1.
-/
def IsCorrect : Prop :=
  ∀ x i, ProbComp.eval (P.run x i) = PMF.pure (x i)

/-- Perfect single-server privacy: each server's query distribution is independent of `i`. -/
def IsPrivate : Prop :=
  ∀ s i i', ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i')

/-- Perfect `t`-privacy: every coalition of at most `t` servers sees an index-independent joint
query distribution. -/
def IsTPrivate (t : ℕ) : Prop :=
  ∀ T : Finset S, T.card ≤ t → ∀ i i',
    ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i')

theorem serverQuery_eq (s : S) (i : ι) :
    P.serverQuery s i = (fun ⟨_, q⟩ => q s) <$> P.query i := by
  rw [serverQuery]

theorem coalitionQuery_eq (T : Finset S) (i : ι) :
    P.coalitionQuery T i = (fun ⟨_, q⟩ (s : T) => q s.1) <$> P.query i := by
  rw [coalitionQuery]

theorem eval_run (x : ι → β) (i : ι) :
    ProbComp.eval (P.run x i) = (ProbComp.eval (P.query i)).map
      (fun rq => P.reconstruct i rq.1 fun s => P.answer s x (rq.2 s)) := by
  rw [run, ProbComp.eval_bind]
  rfl

theorem eval_serverQuery (s : S) (i : ι) :
    ProbComp.eval (P.serverQuery s i) = (ProbComp.eval (P.query i)).map (fun rq => rq.2 s) := by
  rw [serverQuery, ProbComp.eval_map]

theorem eval_coalitionQuery (T : Finset S) (i : ι) :
    ProbComp.eval (P.coalitionQuery T i) =
      (ProbComp.eval (P.query i)).map (fun rq (s : T) => rq.2 s.1) := by
  rw [coalitionQuery, ProbComp.eval_map]

theorem eval_tupleQuery {τ : Type} (servers : τ → S) (i : ι) :
    ProbComp.eval (P.tupleQuery servers i) =
      (ProbComp.eval (P.query i)).map (fun rq j => rq.2 (servers j)) := by
  rw [tupleQuery, ProbComp.eval_map]

theorem isCorrect_iff : P.IsCorrect ↔ ∀ x i r q, (r, q) ∈ (ProbComp.eval (P.query i)).support →
    P.reconstruct i r (fun s => P.answer s x (q s)) = x i := by
  refine forall_congr' fun x => forall_congr' fun i => ?_
  rw [eval_run, Probability.PMF.map_eq_pure_iff]
  exact ⟨fun h r q hrq => h (r, q) hrq, fun h rq hrq => h rq.1 rq.2 hrq⟩

theorem isPrivate_iff : P.IsPrivate ↔
    ∀ s i i', ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i') := by
  rw [IsPrivate]

theorem isTPrivate_iff (t : ℕ) : P.IsTPrivate t ↔
    ∀ T : Finset S, T.card ≤ t → ∀ i i',
      ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i') := by
  rw [IsTPrivate]

end Defs

variable {P : IndexedScheme ι S R Q A β}

theorem IsCorrect.reconstruct_eq (h : P.IsCorrect) (x : ι → β) (i : ι) {r : R}
    {q : (s : S) → Q s} (hrq : (r, q) ∈ (ProbComp.eval (P.query i)).support) :
    P.reconstruct i r (fun s => P.answer s x (q s)) = x i :=
  P.isCorrect_iff.mp h x i r q hrq

theorem IsPrivate.eval_serverQuery_eq (h : P.IsPrivate) (s : S) (i i' : ι) :
    ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i') :=
  P.isPrivate_iff.mp h s i i'

theorem IsTPrivate.eval_coalitionQuery_eq {t : ℕ} (h : P.IsTPrivate t) (T : Finset S)
    (hT : T.card ≤ t) (i i' : ι) :
    ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i') :=
  h T hT i i'

/-! ### Dependent-sum bridge to uniform `PIR.Scheme` -/

section SigmaBridge

/-- Query-only uniform `Scheme` tagging each server's query with its server index `⟨s, q s⟩`. Used
to transport all privacy characterizations from `PIR.Collusion` without duplicating proofs. -/
private def querySigmaScheme (P : IndexedScheme ι S R Q A β) :
    Scheme ι S R (Σ s, Q s) Unit Unit where
  query i := (fun ⟨r, q⟩ => (r, fun s => ⟨s, q s⟩)) <$> P.query i
  answer _ _ _ := ()
  reconstruct _ _ _ := ()

private theorem querySigmaScheme_isPrivate_iff (P : IndexedScheme ι S R Q A β) :
    P.querySigmaScheme.IsPrivate ↔ P.IsPrivate := by
  rw [Scheme.isPrivate_iff, P.isPrivate_iff]
  refine forall_congr' fun s => forall_congr' fun i => forall_congr' fun i' => ?_
  have hmap (idx : ι) : ProbComp.eval (P.querySigmaScheme.serverQuery s idx) =
      (ProbComp.eval (P.serverQuery s idx)).map (Sigma.mk s) := by
    rw [Scheme.eval_serverQuery, querySigmaScheme, ProbComp.eval_map, PMF.map_comp,
      P.eval_serverQuery, PMF.map_comp]
    rfl
  rw [hmap i, hmap i']
  exact (Probability.PMF.map_injective sigma_mk_injective).eq_iff

private theorem querySigmaScheme_isTPrivate_iff (P : IndexedScheme ι S R Q A β) (t : ℕ) :
    P.querySigmaScheme.IsTPrivate t ↔ P.IsTPrivate t := by
  rw [Scheme.isTPrivate_iff, P.isTPrivate_iff]
  refine forall_congr' fun T => imp_congr_right fun _ =>
    forall_congr' fun i => forall_congr' fun i' => ?_
  let embed : ((s : T) → Q s.1) → (T → Σ u, Q u) := fun f s => ⟨s.1, f s⟩
  have hinj : Function.Injective embed := fun f g hfg =>
    funext fun s => sigma_mk_injective (congrFun hfg s)
  have hmap (idx : ι) : ProbComp.eval (P.querySigmaScheme.coalitionQuery T idx) =
      (ProbComp.eval (P.coalitionQuery T idx)).map embed := by
    rw [Scheme.eval_coalitionQuery, querySigmaScheme, ProbComp.eval_map, PMF.map_comp,
      P.eval_coalitionQuery, PMF.map_comp]
    rfl
  rw [hmap i, hmap i']
  exact (Probability.PMF.map_injective hinj).eq_iff

/-- Full dependent-sum `Scheme` embedding both queries and answers of `P` into `Σ s, Q s` and
`Σ s, A s`, preserving `run`, `IsCorrect`, `IsPrivate` and `IsTPrivate`. -/
noncomputable def toSigmaScheme [DecidableEq S] (P : IndexedScheme ι S R Q A β)
    (defaultA : (s : S) → A s) (fallback : β) : Scheme ι S R (Σ s, Q s) (Σ s, A s) β where
  query i := (fun ⟨r, q⟩ => (r, fun s => ⟨s, q s⟩)) <$> P.query i
  answer s x sq := if h : sq.1 = s then ⟨s, P.answer s x (h ▸ sq.2)⟩ else ⟨s, defaultA s⟩
  reconstruct i r sa :=
    letI := Classical.propDecidable (∀ s, (sa s).1 = s)
    if h : ∀ s, (sa s).1 = s then P.reconstruct i r (fun s => h s ▸ (sa s).2) else fallback

theorem eval_run_toSigmaScheme [DecidableEq S] (P : IndexedScheme ι S R Q A β)
    (defaultA : (s : S) → A s) (fallback : β) (x : ι → β) (i : ι) :
    ProbComp.eval ((P.toSigmaScheme defaultA fallback).run x i) = ProbComp.eval (P.run x i) := by
  let S' := P.toSigmaScheme defaultA fallback
  change ProbComp.eval (S'.run x i) = ProbComp.eval (P.run x i)
  have hquery : S'.query i = (fun ⟨r, q⟩ => (r, fun s => ⟨s, q s⟩)) <$> P.query i := rfl
  rw [Scheme.eval_run, hquery, ProbComp.eval_map, PMF.map_comp, P.eval_run]
  congr 1
  funext ⟨r, q⟩
  simp only [Function.comp_apply]
  have hans : (fun s => S'.answer s x ⟨s, q s⟩) = fun s => ⟨s, P.answer s x (q s)⟩ :=
    funext fun s => by simp [S', toSigmaScheme]
  rw [hans]
  dsimp only [S', toSigmaScheme]
  split_ifs with h
  · rfl
  · exact False.elim (h fun _ => rfl)

@[simp] theorem isCorrect_toSigmaScheme_iff [DecidableEq S] (P : IndexedScheme ι S R Q A β)
    (defaultA : (s : S) → A s) (fallback : β) :
    (P.toSigmaScheme defaultA fallback).IsCorrect ↔ P.IsCorrect := by
  rw [Scheme.isCorrect_iff_eval_run, IsCorrect]
  simp only [eval_run_toSigmaScheme]

@[simp] theorem isTPrivate_toSigmaScheme_iff [DecidableEq S] (P : IndexedScheme ι S R Q A β)
    (defaultA : (s : S) → A s) (fallback : β) (t : ℕ) :
    (P.toSigmaScheme defaultA fallback).IsTPrivate t ↔ P.IsTPrivate t := by
  have hiff : (P.toSigmaScheme defaultA fallback).IsTPrivate t ↔
      P.querySigmaScheme.IsTPrivate t := by
    rw [Scheme.isTPrivate_iff, Scheme.isTPrivate_iff]
    refine forall_congr' fun T => imp_congr_right fun _ =>
      forall_congr' fun i => forall_congr' fun i' => ?_
    simp only [Scheme.eval_coalitionQuery, toSigmaScheme, querySigmaScheme]
  exact hiff.trans (P.querySigmaScheme_isTPrivate_iff t)

@[simp] theorem isPrivate_toSigmaScheme_iff [DecidableEq S] (P : IndexedScheme ι S R Q A β)
    (defaultA : (s : S) → A s) (fallback : β) :
    (P.toSigmaScheme defaultA fallback).IsPrivate ↔ P.IsPrivate := by
  have hiff : (P.toSigmaScheme defaultA fallback).IsPrivate ↔
      P.querySigmaScheme.IsPrivate := by
    rw [Scheme.isPrivate_iff, Scheme.isPrivate_iff]
    refine forall_congr' fun s => forall_congr' fun i => forall_congr' fun i' => ?_
    simp only [Scheme.eval_serverQuery, toSigmaScheme, querySigmaScheme]
  exact hiff.trans P.querySigmaScheme_isPrivate_iff

end SigmaBridge

theorem isTPrivate_zero (P : IndexedScheme ι S R Q A β) : P.IsTPrivate 0 :=
  (P.querySigmaScheme_isTPrivate_iff 0).mp P.querySigmaScheme.isTPrivate_zero

theorem IsTPrivate.mono {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) (h : P.IsTPrivate t₂) : P.IsTPrivate t₁ :=
  (P.querySigmaScheme_isTPrivate_iff t₁).mp
    (((P.querySigmaScheme_isTPrivate_iff t₂).mpr h).mono hle)

/-- `1`-privacy is equivalent to single-server `IsPrivate`. -/
theorem isTPrivate_one_iff : P.IsTPrivate 1 ↔ P.IsPrivate := by
  rw [← P.querySigmaScheme_isTPrivate_iff 1, ← P.querySigmaScheme_isPrivate_iff,
    Scheme.isTPrivate_one_iff]

theorem IsTPrivate.isPrivate {t : ℕ} (ht : 1 ≤ t) (h : P.IsTPrivate t) : P.IsPrivate :=
  isTPrivate_one_iff.mp (h.mono ht)

/-- `Finset`-based `t`-privacy is equivalent to `t`-tuple query independence. -/
theorem isTPrivate_iff_tuple {t : ℕ} :
    P.IsTPrivate t ↔
      ∀ (servers : Fin t → S) (i i' : ι),
        ProbComp.eval (P.tupleQuery servers i) = ProbComp.eval (P.tupleQuery servers i') := by
  rw [← P.querySigmaScheme_isTPrivate_iff t, Scheme.isTPrivate_iff_tuple]
  refine forall_congr' fun servers => forall_congr' fun i => forall_congr' fun i' => ?_
  let embed : ((j : Fin t) → Q (servers j)) → (Fin t → Σ u, Q u) :=
    fun f j => ⟨servers j, f j⟩
  have hinj : Function.Injective embed := fun f g hfg =>
    funext fun j => sigma_mk_injective (congrFun hfg j)
  have hmap (idx : ι) : ProbComp.eval (P.querySigmaScheme.tupleQuery servers idx) =
      (ProbComp.eval (P.tupleQuery servers idx)).map embed := by
    rw [Scheme.eval_tupleQuery, querySigmaScheme, ProbComp.eval_map, PMF.map_comp,
      P.eval_tupleQuery, PMF.map_comp]
    rfl
  rw [hmap i, hmap i']
  exact (Probability.PMF.map_injective hinj).eq_iff

/-! ### Row repetition and index embeddings -/

/-- Matrix row repetition [CGKS, Section 3.4][ChorGoldreichKushilevitzSudan1998] for
`IndexedScheme`. -/
def rows (ρ : Type) (P : IndexedScheme ι S R Q A β) :
    IndexedScheme (ρ × ι) S R Q (fun s => ρ → A s) β where
  query ji := P.query ji.2
  answer s x q j := P.answer s (fun i => x (j, i)) q
  reconstruct ji r a := P.reconstruct ji.2 r fun s => a s ji.1

@[simp] theorem query_rows (ρ : Type) (P : IndexedScheme ι S R Q A β) (ji : ρ × ι) :
    (P.rows ρ).query ji = P.query ji.2 := by
  rfl

@[simp] theorem run_rows (ρ : Type) (P : IndexedScheme ι S R Q A β) (x : ρ × ι → β) (ji : ρ × ι) :
    (P.rows ρ).run x ji = P.run (fun i => x (ji.1, i)) ji.2 := by
  rfl

@[simp] theorem serverQuery_rows (ρ : Type) (P : IndexedScheme ι S R Q A β) (s : S) (ji : ρ × ι) :
    (P.rows ρ).serverQuery s ji = P.serverQuery s ji.2 := by
  rfl

@[simp] theorem coalitionQuery_rows (ρ : Type) (P : IndexedScheme ι S R Q A β) (T : Finset S)
    (ji : ρ × ι) : (P.rows ρ).coalitionQuery T ji = P.coalitionQuery T ji.2 := by
  rfl

theorem IsCorrect.rows (ρ : Type) (h : P.IsCorrect) : (P.rows ρ).IsCorrect := fun x ji =>
  h (fun i => x (ji.1, i)) ji.2

theorem IsPrivate.rows (ρ : Type) (h : P.IsPrivate) : (P.rows ρ).IsPrivate := fun s ji ji' =>
  h s ji.2 ji'.2

theorem IsTPrivate.rows (ρ : Type) {t : ℕ} (h : P.IsTPrivate t) : (P.rows ρ).IsTPrivate t :=
  fun T hT ji ji' => h T hT ji.2 ji'.2

/-- Restrict an `IndexedScheme` along an index embedding `e : ι ↪ ι'`, padding outside the image
with `pad`. -/
noncomputable def comap {ι' : Type} (P : IndexedScheme ι' S R Q A β) (e : ι ↪ ι') (pad : β) :
    IndexedScheme ι S R Q A β where
  query i := P.query (e i)
  answer s x q := P.answer s (Function.extend e x fun _ => pad) q
  reconstruct i r a := P.reconstruct (e i) r a

@[simp] theorem query_comap {ι' : Type} (P : IndexedScheme ι' S R Q A β) (e : ι ↪ ι') (pad : β)
    (i : ι) : (P.comap e pad).query i = P.query (e i) := by
  rfl

@[simp] theorem serverQuery_comap {ι' : Type} (P : IndexedScheme ι' S R Q A β) (e : ι ↪ ι')
    (pad : β) (s : S) (i : ι) : (P.comap e pad).serverQuery s i = P.serverQuery s (e i) := by
  rfl

@[simp] theorem coalitionQuery_comap {ι' : Type} (P : IndexedScheme ι' S R Q A β) (e : ι ↪ ι')
    (pad : β) (T : Finset S) (i : ι) :
    (P.comap e pad).coalitionQuery T i = P.coalitionQuery T (e i) := by
  rfl

theorem IsCorrect.comap {ι' : Type} {P : IndexedScheme ι' S R Q A β} (h : P.IsCorrect)
    (e : ι ↪ ι') (pad : β) : (P.comap e pad).IsCorrect := fun x i => by
  have := h (Function.extend e x fun _ => pad) (e i)
  rwa [e.injective.extend_apply] at this

theorem IsPrivate.comap {ι' : Type} {P : IndexedScheme ι' S R Q A β} (h : P.IsPrivate)
    (e : ι ↪ ι') (pad : β) : (P.comap e pad).IsPrivate := fun s i i' =>
  h s (e i) (e i')

theorem IsTPrivate.comap {ι' : Type} {P : IndexedScheme ι' S R Q A β} {t : ℕ} (h : P.IsTPrivate t)
    (e : ι ↪ ι') (pad : β) : (P.comap e pad).IsTPrivate t := fun T hT i i' =>
  h T hT (e i) (e i')

/-! ### Full-coalition and single-server lower bounds -/

/-- No zero-server `IndexedScheme` is correct on a nonempty index set over a nontrivial payload. -/
theorem not_isCorrect_of_isEmpty [IsEmpty S] [Nonempty ι] [Nontrivial β]
    (hcorrect : P.IsCorrect) : False := by
  let _ : DecidableEq S := isEmptyElim
  obtain ⟨b₀, _⟩ := exists_pair_ne β
  exact Scheme.not_isCorrect_of_isEmpty
    ((P.isCorrect_toSigmaScheme_iff isEmptyElim b₀).mpr hcorrect)

/-- When all servers can collude (`|S| ≤ t`), some joint query tuple `q : (s : S) → Q s` makes the
combined answer map `x ↦ fun s => P.answer s x (q s)` injective, deduced via `toSigmaScheme` from
`Scheme.exists_injective_answers_of_card_le`. -/
theorem exists_injective_answers_of_card_le [Fintype S] [Nonempty ι] {t : ℕ}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    ∃ q : (s : S) → Q s, Function.Injective fun x s => P.answer s x (q s) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨⟨r₀, q₀⟩, _⟩ := (ProbComp.eval (P.query i₀)).support_nonempty
  by_cases hβ : Nonempty β
  · obtain ⟨b₀⟩ := hβ
    let defaultA : (s : S) → A s := fun s => P.answer s (fun _ => b₀) (q₀ s)
    let Psig := P.toSigmaScheme defaultA b₀
    obtain ⟨qsig, hqsig⟩ := Psig.exists_injective_answers_of_card_le
      ((P.isCorrect_toSigmaScheme_iff defaultA b₀).mpr hcorrect)
      ((P.isTPrivate_toSigmaScheme_iff defaultA b₀ t).mpr hprivate) hcard
    refine ⟨fun s => if h : (qsig s).1 = s then h ▸ (qsig s).2 else q₀ s, fun x y hxy => hqsig ?_⟩
    funext s
    change Psig.answer s x (qsig s) = Psig.answer s y (qsig s)
    dsimp only [Psig, toSigmaScheme]
    by_cases hs : (qsig s).1 = s
    · have hxy_s := congrFun hxy s
      simp only [dite_eq_left hs] at hxy_s ⊢
      exact congrArg (Sigma.mk s) hxy_s
    · simp only [dite_eq_right hs]
  · let _ : IsEmpty β := not_nonempty_iff.mp hβ
    exact ⟨q₀, fun x => isEmptyElim (x i₀)⟩

/-- A correct `t`-private Boolean `IndexedScheme` with `|S| ≤ t` satisfies
`2 ^ |ι| ≤ ∏ s : S, |A s|`. -/
theorem two_pow_card_le_prod_card_answer_of_card_le [Fintype S] [Nonempty ι] [Fintype ι]
    [∀ s, Fintype (A s)] {P : IndexedScheme ι S R Q A} {t : ℕ} (hcorrect : P.IsCorrect)
    (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    2 ^ Fintype.card ι ≤ ∏ s : S, Fintype.card (A s) := by
  classical
  obtain ⟨q, hq⟩ := exists_injective_answers_of_card_le hcorrect hprivate hcard
  have h := Fintype.card_le_of_injective _ hq
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_pi] at h

/-- **Full-coalition lower bound for heterogeneous server widths**: if `|S| ≤ t`, any perfectly
correct `t`-private Boolean `IndexedScheme` communicates at least `|ι|` bits in total across the
servers. -/
theorem card_le_indexedCommunication_of_card_le [Fintype S] [Fintype ι]
    [∀ s, Fintype (Q s)] [∀ s, Fintype (A s)] {P : IndexedScheme ι S R Q A} {t : ℕ}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    Fintype.card ι ≤ indexedCommunication S Q A := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Fintype.card_eq_zero]
    exact Nat.zero_le _
  · rcases isEmpty_or_nonempty S with hS | ⟨_⟩
    · exact (not_isCorrect_of_isEmpty hcorrect).elim
    · have hpow := two_pow_card_le_prod_card_answer_of_card_le hcorrect hprivate hcard
      have hprod : ∏ s : S, Fintype.card (A s) ≤
          2 ^ ∑ s : S, Nat.clog 2 (Fintype.card (A s)) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod fun s _ => Nat.le_pow_clog (by norm_num : 1 < 2) _
      have hle : Fintype.card ι ≤ ∑ s : S, Nat.clog 2 (Fintype.card (A s)) :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hpow.trans hprod)
      rw [indexedCommunication_eq]
      exact hle.trans (Finset.sum_le_sum fun s _ => Nat.le_add_left _ _)

/-- **Single-server lower bound for heterogeneous schemes**: with one server, any perfectly correct
and perfectly private Boolean `IndexedScheme` communicates at least `|ι|` bits. -/
theorem card_le_indexedCommunication [Fintype S] [Unique S] [Fintype ι]
    [∀ s, Fintype (Q s)] [∀ s, Fintype (A s)] {P : IndexedScheme ι S R Q A}
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    Fintype.card ι ≤ indexedCommunication S Q A :=
  card_le_indexedCommunication_of_card_le hcorrect (isTPrivate_one_iff.mpr hprivate)
    (by rw [Fintype.card_unique])

end IndexedScheme

/-! ### Embedding uniform `PIR.Scheme` into `PIR.IndexedScheme` -/

/-- View a uniform `P : Scheme ι S R Q A β` as an `IndexedScheme` with constant message types. -/
def Scheme.toIndexed {ι S R Q A β : Type} (P : Scheme ι S R Q A β) :
    IndexedScheme ι S R (fun _ => Q) (fun _ => A) β where
  query := P.query
  answer := P.answer
  reconstruct := P.reconstruct

@[simp] theorem Scheme.query_toIndexed {ι S R Q A β : Type} (P : Scheme ι S R Q A β) (i : ι) :
    P.toIndexed.query i = P.query i := by
  rfl

@[simp] theorem Scheme.answer_toIndexed {ι S R Q A β : Type} (P : Scheme ι S R Q A β) (s : S)
    (x : ι → β) (q : Q) : P.toIndexed.answer s x q = P.answer s x q := by
  rfl

@[simp] theorem Scheme.reconstruct_toIndexed {ι S R Q A β : Type} (P : Scheme ι S R Q A β)
    (i : ι) (r : R) (a : S → A) : P.toIndexed.reconstruct i r a = P.reconstruct i r a := by
  rfl

@[simp] theorem Scheme.eval_run_toIndexed {ι S R Q A β : Type} (P : Scheme ι S R Q A β)
    (x : ι → β) (i : ι) : ProbComp.eval (P.toIndexed.run x i) = ProbComp.eval (P.run x i) := by
  rw [IndexedScheme.eval_run, Scheme.eval_run]
  rfl

@[simp] theorem Scheme.isCorrect_toIndexed_iff {ι S R Q A β : Type} (P : Scheme ι S R Q A β) :
    P.toIndexed.IsCorrect ↔ P.IsCorrect := by
  rw [Scheme.isCorrect_iff_eval_run, IndexedScheme.IsCorrect]
  simp only [eval_run_toIndexed]

@[simp] theorem Scheme.isPrivate_toIndexed_iff {ι S R Q A β : Type} (P : Scheme ι S R Q A β) :
    P.toIndexed.IsPrivate ↔ P.IsPrivate := by
  rw [Scheme.isPrivate_iff, IndexedScheme.isPrivate_iff]
  refine forall_congr' fun s => forall_congr' fun i => forall_congr' fun i' => ?_
  simp only [IndexedScheme.eval_serverQuery, Scheme.eval_serverQuery, Scheme.toIndexed]

@[simp] theorem Scheme.isTPrivate_toIndexed_iff {ι S R Q A β : Type} (P : Scheme ι S R Q A β)
    (t : ℕ) : P.toIndexed.IsTPrivate t ↔ P.IsTPrivate t := by
  rw [Scheme.isTPrivate_iff, IndexedScheme.isTPrivate_iff]
  refine forall_congr' fun T => imp_congr_right fun _ =>
    forall_congr' fun i => forall_congr' fun i' => ?_
  simp only [IndexedScheme.eval_coalitionQuery, Scheme.eval_coalitionQuery, Scheme.toIndexed]

/-! ### Existence of heterogeneous schemes -/

/-- Some `k`-server `IndexedScheme` for databases `ι → β` (by default `β = Bool`) is perfectly
correct and perfectly private and communicates at most `c` bits in total. -/
def HasIndexedScheme (ι : Type) (k c : ℕ) (β : Type := Bool) : Prop :=
  ∃ (S R : Type) (Q A : S → Type) (_ : Fintype S) (_ : ∀ s, Fintype (Q s))
    (_ : ∀ s, Fintype (A s)) (P : IndexedScheme ι S R Q A β),
    P.IsCorrect ∧ P.IsPrivate ∧ Fintype.card S = k ∧ indexedCommunication S Q A ≤ c

/-- Some `k`-server `IndexedScheme` for databases `ι → β` is perfectly correct, perfectly
`t`-private, and communicates at most `c` bits in total. -/
def HasTPrivateIndexedScheme (ι : Type) (t k c : ℕ) (β : Type := Bool) : Prop :=
  ∃ (S R : Type) (Q A : S → Type) (_ : Fintype S) (_ : ∀ s, Fintype (Q s))
    (_ : ∀ s, Fintype (A s)) (P : IndexedScheme ι S R Q A β),
    P.IsCorrect ∧ P.IsTPrivate t ∧ Fintype.card S = k ∧ indexedCommunication S Q A ≤ c

theorem hasIndexedScheme_iff {ι β : Type} {k c : ℕ} :
    HasIndexedScheme ι k c β ↔
      ∃ (S R : Type) (Q A : S → Type) (_ : Fintype S) (_ : ∀ s, Fintype (Q s))
        (_ : ∀ s, Fintype (A s)) (P : IndexedScheme ι S R Q A β),
        P.IsCorrect ∧ P.IsPrivate ∧ Fintype.card S = k ∧ indexedCommunication S Q A ≤ c := by
  rw [HasIndexedScheme]

theorem hasTPrivateIndexedScheme_iff {ι β : Type} {t k c : ℕ} :
    HasTPrivateIndexedScheme ι t k c β ↔
      ∃ (S R : Type) (Q A : S → Type) (_ : Fintype S) (_ : ∀ s, Fintype (Q s))
        (_ : ∀ s, Fintype (A s)) (P : IndexedScheme ι S R Q A β),
        P.IsCorrect ∧ P.IsTPrivate t ∧ Fintype.card S = k ∧ indexedCommunication S Q A ≤ c := by
  rw [HasTPrivateIndexedScheme]

theorem hasTPrivateIndexedScheme_one_iff {ι β : Type} {k c : ℕ} :
    HasTPrivateIndexedScheme ι 1 k c β ↔ HasIndexedScheme ι k c β := by
  simp only [hasTPrivateIndexedScheme_iff, hasIndexedScheme_iff, IndexedScheme.isTPrivate_one_iff]

theorem IndexedScheme.IsCorrect.hasIndexedScheme {ι S R β : Type} {Q A : S → Type} [Fintype S]
    [∀ s, Fintype (Q s)] [∀ s, Fintype (A s)] {P : IndexedScheme ι S R Q A β}
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    HasIndexedScheme ι (Fintype.card S) (indexedCommunication S Q A) β :=
  hasIndexedScheme_iff.mpr ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, rfl, le_rfl⟩

theorem IndexedScheme.IsCorrect.hasTPrivateIndexedScheme {ι S R β : Type} {Q A : S → Type}
    [Fintype S] [∀ s, Fintype (Q s)] [∀ s, Fintype (A s)] {P : IndexedScheme ι S R Q A β} {t : ℕ}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) :
    HasTPrivateIndexedScheme ι t (Fintype.card S) (indexedCommunication S Q A) β :=
  hasTPrivateIndexedScheme_iff.mpr ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, rfl, le_rfl⟩

theorem HasIndexedScheme.mono {ι β : Type} {k c c' : ℕ} (h : HasIndexedScheme ι k c β)
    (hc : c ≤ c') : HasIndexedScheme ι k c' β := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := hasIndexedScheme_iff.mp h
  exact hasIndexedScheme_iff.mpr ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm.trans hc⟩

theorem HasTPrivateIndexedScheme.mono {ι β : Type} {t k c c' : ℕ}
    (h : HasTPrivateIndexedScheme ι t k c β) (hc : c ≤ c') :
    HasTPrivateIndexedScheme ι t k c' β := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ :=
    hasTPrivateIndexedScheme_iff.mp h
  exact hasTPrivateIndexedScheme_iff.mpr
    ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm.trans hc⟩

theorem HasTPrivateIndexedScheme.mono_threshold {ι β : Type} {t₁ t₂ k c : ℕ} (ht : t₁ ≤ t₂)
    (h : HasTPrivateIndexedScheme ι t₂ k c β) : HasTPrivateIndexedScheme ι t₁ k c β := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ :=
    hasTPrivateIndexedScheme_iff.mp h
  exact hasTPrivateIndexedScheme_iff.mpr
    ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate.mono ht, hk, hcomm⟩

theorem HasTPrivateIndexedScheme.hasIndexedScheme {ι β : Type} {t k c : ℕ} (ht : 1 ≤ t)
    (h : HasTPrivateIndexedScheme ι t k c β) : HasIndexedScheme ι k c β :=
  hasTPrivateIndexedScheme_one_iff.mp (h.mono_threshold ht)

/-- Every uniform `HasScheme` witness is also a `HasIndexedScheme` witness at the same cost. -/
theorem HasScheme.hasIndexedScheme {ι β : Type} {k c : ℕ} (h : HasScheme ι k c β) :
    HasIndexedScheme ι k c β := by
  obtain ⟨S, R, Q, A, instS, instQ, instA, P, hcorrect, hprivate, hk, hcomm⟩ := hasScheme_iff.mp h
  let _ := instS
  let _ := instQ
  let _ := instA
  refine hasIndexedScheme_iff.mpr ⟨S, R, fun _ => Q, fun _ => A, instS, fun _ => instQ,
    fun _ => instA, P.toIndexed, P.isCorrect_toIndexed_iff.mpr hcorrect,
    P.isPrivate_toIndexed_iff.mpr hprivate, hk, ?_⟩
  rwa [indexedCommunication_const]

/-- Every uniform `HasTPrivateScheme` witness is also a `HasTPrivateIndexedScheme` witness. -/
theorem HasTPrivateScheme.hasTPrivateIndexedScheme {ι β : Type} {t k c : ℕ}
    (h : HasTPrivateScheme ι t k c β) : HasTPrivateIndexedScheme ι t k c β := by
  obtain ⟨S, R, Q, A, instS, instQ, instA, P, hcorrect, hprivate, hk, hcomm⟩ :=
    hasTPrivateScheme_iff.mp h
  let _ := instS
  let _ := instQ
  let _ := instA
  refine hasTPrivateIndexedScheme_iff.mpr ⟨S, R, fun _ => Q, fun _ => A, instS, fun _ => instQ,
    fun _ => instA, P.toIndexed, P.isCorrect_toIndexed_iff.mpr hcorrect,
    (P.isTPrivate_toIndexed_iff t).mpr hprivate, hk, ?_⟩
  rwa [indexedCommunication_const]

theorem HasTPrivateIndexedScheme.card_le_of_le {ι : Type} [Fintype ι] {t k c : ℕ}
    (h : HasTPrivateIndexedScheme ι t k c) (hkt : k ≤ t) : Fintype.card ι ≤ c := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ :=
    hasTPrivateIndexedScheme_iff.mp h
  exact (P.card_le_indexedCommunication_of_card_le hcorrect hprivate (hk.trans_le hkt)).trans hcomm

theorem HasIndexedScheme.card_le_one {ι : Type} [Fintype ι] {c : ℕ} (h : HasIndexedScheme ι 1 c) :
    Fintype.card ι ≤ c :=
  (hasTPrivateIndexedScheme_one_iff.mpr h).card_le_of_le le_rfl

/-- **One server needs `n` bits even with per-server message types**: a perfectly correct and
perfectly private one-server `IndexedScheme` communicating `c` bits exists iff `|ι| ≤ c`. -/
theorem hasIndexedScheme_one_iff (ι : Type) [Fintype ι] (c : ℕ) :
    HasIndexedScheme ι 1 c ↔ Fintype.card ι ≤ c :=
  ⟨HasIndexedScheme.card_le_one, fun hc => ((hasScheme_one_iff ι c).mpr hc).hasIndexedScheme⟩

end Cslib.Crypto.Protocols.PIR

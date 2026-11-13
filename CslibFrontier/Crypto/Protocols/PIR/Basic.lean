/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Clog
import CslibFrontier.Probability.PMF.Support

/-!
# Private information retrieval

A database `x : ι → β` of entries in `β` (by default single bits `β = Bool`) is replicated on the
servers `S`. A user who wants the entry `x i` sends each server one query and reconstructs `x i`
from the answers. The scheme is *private* when no single server learns anything about `i` from its
query [Chor, Goldreich, Kushilevitz and Sudan, Definition 1][ChorGoldreichKushilevitzSudan1998].

A one-round scheme `P : PIR.Scheme ι S R Q A β` (`β` defaults to `Bool`) consists of

* a query generator `P.query i : ProbComp (R × (S → Q))`: a probabilistic program that, for the
  index `i`, outputs the user's retained state `r : R` and the query `q s : Q` for every server `s`;
* deterministic answer functions `P.answer s x : Q → A`, one per server;
* a reconstruction function `P.reconstruct i r : (S → A) → β`.

`P.run x i` is the user's output. `P.IsCorrect` says that this output is `x i` with probability one,
for every database and index; `P.IsPrivate` says that for every server `s`, the distribution of the
query `P.serverQuery s i` is the same for all indices `i`. Both are exact equalities of
distributions, as in the information-theoretic setting of the source. The randomness is a
`ProbComp` program, so its coins are uniform choices from finite ranges; the source's uniformly
random string `r ∈ {0,1}^ℓ` is the special case of `ProbComp.uniform (Fin ℓ → Bool)`, and its
retained state is the random string itself. Privacy here (`IsPrivate`) is against each single
server; coalitions of servers (`IsTPrivate`) are covered in `PIR.Collusion`, and block-retrieval
transformations (`β = κ → Bool`) in `PIR.Block`. Machine running time of the user and servers
([CGKS, Section 2.4, p. 6][ChorGoldreichKushilevitzSudan1998]) is not modelled here.

The communication cost `PIR.communication S Q A` counts the bits of a fixed-length binary encoding
of every query and answer: `|S| · (⌈log₂ |Q|⌉ + ⌈log₂ |A|⌉)`. For `Q = Fin ℓq → Bool` and
`A = Fin ℓa → Bool` this is the source's `k · (ℓq + ℓa)`.

Two transformations build schemes from schemes. `Scheme.rows` is the generic transformation of
[CGKS, Section 3.4][ChorGoldreichKushilevitzSudan1998], restated as Proposition 4 in Section 4.1: a
database indexed by `ρ × ι` is a matrix with rows indexed by `ρ`, the user sends the query for the
column `i`, and each server answers it once for every row. Its communication is computed for
one-bit answers (`PIR.communication_rows`), the case that Section 3.4 uses. `Scheme.comap`
restricts a scheme along an embedding of indices, padding the database outside the image with a
supplied default entry `pad : β`; it turns a scheme for a grid or a cube into one for `Fin n`.
Both keep the queries of `P` up to reindexing, so `IsPrivate.of_query_eq` transfers privacy to them
and to the transformations of `PIR.Block`.

The existence statement `PIR.HasScheme ι k c β` (some correct, private `k`-server scheme for
databases `ι → β` communicating at most `c` bits) is the `t = 1` case of `PIR.HasTPrivateScheme`
and lives in `PIR.Collusion`.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Scheme`: one-round multi-server schemes (with optional payload type
  `β := Bool`).
* `Cslib.Crypto.Protocols.PIR.Scheme.run`, `Cslib.Crypto.Protocols.PIR.Scheme.serverQuery`: the
  user's output and the query seen by one server.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect`, `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate`:
  perfect correctness and perfect privacy.
* `Cslib.Crypto.Protocols.PIR.communication`: the communication cost.
* `Cslib.Crypto.Protocols.PIR.Scheme.rows`, `Cslib.Crypto.Protocols.PIR.Scheme.comap`: the rows
  transformation and restriction along an embedding.

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.isCorrect_iff`: correctness on the support of the queries.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.of_query_eq`: privacy transfers to a scheme whose
  queries have the law of the queries of a private scheme, up to reindexing.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.rows`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.rows`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.comap`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.comap`: both transformations preserve
  correctness and privacy.
* `Cslib.Crypto.Protocols.PIR.communication_rows`: the rows transformation multiplies the answer
  length by the number of rows.
* `Cslib.Crypto.Protocols.PIR.communication_le_of_clog_le`,
  `Cslib.Crypto.Protocols.PIR.clog_card_fun_le`: communication from per-server query and answer
  lengths, and the length of a tuple of symbols.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], J. ACM 45(6), 1998; numbering of the authors'
  journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability

/-- A one-round private information retrieval scheme for databases `x : ι → β` (by default single
bits `β = Bool`, or blocks in Section 4) held by the servers `S`, with user state `R`, queries `Q`
and answers `A` [CGKS, Definition 1 and Section 4][ChorGoldreichKushilevitzSudan1998]. -/
structure Scheme (ι S R Q A : Type) (β : Type := Bool) where
  /-- The user's query generator: for the index `i`, a retained state and one query per server. -/
  query : ι → ProbComp (R × (S → Q))
  /-- The answer of the server `s`, holding the database `x`, to a query. -/
  answer : S → (ι → β) → Q → A
  /-- The user's reconstruction of the entry `x i` from the retained state and the answers. -/
  reconstruct : ι → R → (S → A) → β

/-- The communication cost of a one-round scheme with servers `S`, queries `Q` and answers `A`:
the number of bits sent and received when each query and each answer is written in a fixed-length
binary encoding, `|S| · (⌈log₂ |Q|⌉ + ⌈log₂ |A|⌉)`. -/
def communication (S Q A : Type) [Fintype S] [Fintype Q] [Fintype A] : ℕ :=
  Fintype.card S * (Nat.clog 2 (Fintype.card Q) + Nat.clog 2 (Fintype.card A))

theorem communication_eq (S Q A : Type) [Fintype S] [Fintype Q] [Fintype A] :
    communication S Q A =
      Fintype.card S * (Nat.clog 2 (Fintype.card Q) + Nat.clog 2 (Fintype.card A)) := by
  rw [communication]

/-- With `2 ^ ℓ` answers, the answers carry `ℓ` bits. -/
theorem communication_of_card_answer (S Q A : Type) [Fintype S] [Fintype Q] [Fintype A] {ℓ : ℕ}
    (hA : Fintype.card A = 2 ^ ℓ) :
    communication S Q A = Fintype.card S * (Nat.clog 2 (Fintype.card Q) + ℓ) := by
  rw [communication_eq, hA, Nat.clog_pow 2 _ (by norm_num)]

/-- Communication is bounded by any per-server bounds on the query and answer lengths. -/
theorem communication_le_of_clog_le {S Q A : Type} [Fintype S] [Fintype Q] [Fintype A] {q a : ℕ}
    (hQ : Nat.clog 2 (Fintype.card Q) ≤ q) (hA : Nat.clog 2 (Fintype.card A) ≤ a) :
    communication S Q A ≤ Fintype.card S * (q + a) := by
  rw [communication_eq]
  gcongr

/-- A `κ`-tuple of symbols is encoded in at most `|κ|` times the bits of one symbol. -/
theorem clog_card_fun_le (κ α : Type) [Fintype κ] [DecidableEq κ] [Fintype α] :
    Nat.clog 2 (Fintype.card (κ → α)) ≤ Fintype.card κ * Nat.clog 2 (Fintype.card α) := by
  rw [Fintype.card_fun]
  exact Nat.clog_pow_le_mul 2 _ _

namespace Scheme

variable {ι S R Q A β : Type}

section Defs

variable (P : Scheme ι S R Q A β)

/-- The user's output on the database `x` and the index `i`: draw the state and the queries, ask
each server, and reconstruct from the answers. -/
def run (x : ι → β) (i : ι) : ProbComp β := do
  let (r, q) ← P.query i
  pure (P.reconstruct i r fun s => P.answer s x (q s))

/-- The query that the server `s` receives when the user wants the entry `i`. -/
def serverQuery (s : S) (i : ι) : ProbComp Q :=
  (fun (_, q) => q s) <$> P.query i

/-- Perfect correctness: on every database, the user outputs the entry it asks for with
probability one. -/
def IsCorrect : Prop :=
  ∀ x i, ProbComp.eval (P.run x i) = PMF.pure (x i)

/-- Perfect privacy: for every server, the distribution of its query does not depend on the index
that the user asks for. -/
def IsPrivate : Prop :=
  ∀ s i i', ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i')

theorem serverQuery_eq (s : S) (i : ι) :
    P.serverQuery s i = (fun (_, q) => q s) <$> P.query i := by
  rw [serverQuery]

theorem eval_run (x : ι → β) (i : ι) :
    ProbComp.eval (P.run x i) = (ProbComp.eval (P.query i)).map
      (fun rq => P.reconstruct i rq.1 fun s => P.answer s x (rq.2 s)) := by
  rw [run, ProbComp.eval_bind]
  rfl

theorem eval_serverQuery (s : S) (i : ι) :
    ProbComp.eval (P.serverQuery s i) = (ProbComp.eval (P.query i)).map (fun rq => rq.2 s) := by
  rw [serverQuery, ProbComp.eval_map]

theorem isCorrect_iff_eval_run : P.IsCorrect ↔ ∀ x i, ProbComp.eval (P.run x i) = PMF.pure (x i) :=
  by rw [IsCorrect]

/-- Perfect correctness holds exactly when every state and every queries that the user can draw
reconstruct the right entry. -/
theorem isCorrect_iff : P.IsCorrect ↔ ∀ x i r q, (r, q) ∈ (ProbComp.eval (P.query i)).support →
    P.reconstruct i r (fun s => P.answer s x (q s)) = x i := by
  refine forall_congr' fun x => forall_congr' fun i => ?_
  rw [eval_run, Probability.PMF.map_eq_pure_iff]
  exact ⟨fun h r q hrq => h (r, q) hrq, fun h rq hrq => h rq.1 rq.2 hrq⟩

theorem isPrivate_iff : P.IsPrivate ↔
    ∀ s i i', ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i') := by
  rw [IsPrivate]

end Defs

variable {P : Scheme ι S R Q A β}

/-- A correct scheme reconstructs the right entry from every state and queries the user can draw. -/
theorem IsCorrect.reconstruct_eq (h : P.IsCorrect) (x : ι → β) (i : ι) {r : R} {q : S → Q}
    (hrq : (r, q) ∈ (ProbComp.eval (P.query i)).support) :
    P.reconstruct i r (fun s => P.answer s x (q s)) = x i :=
  P.isCorrect_iff.mp h x i r q hrq

/-- In a private scheme, each server's query has the same distribution for all indices. -/
theorem IsPrivate.eval_serverQuery_eq (h : P.IsPrivate) (s : S) (i i' : ι) :
    ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i') :=
  P.isPrivate_iff.mp h s i i'

/-- **Privacy transfer.** If the queries that `P'` sends for `i` have the law of the queries that
the private scheme `P` sends for `f i`, then `P'` is private. The retained states, answers and
reconstructions of the two schemes are unconstrained. -/
theorem IsPrivate.of_query_eq {ι' R' A' β' : Type} {P' : Scheme ι' S R' Q A' β'} (h : P.IsPrivate)
    (f : ι' → ι)
    (hq : ∀ i,
      ProbComp.eval (Prod.snd <$> P'.query i) = ProbComp.eval (Prod.snd <$> P.query (f i))) :
    P'.IsPrivate := by
  have hview (i : ι') (s : S) :
      ProbComp.eval (P'.serverQuery s i) = ProbComp.eval (P.serverQuery s (f i)) := by
    have hs := congrArg (PMF.map fun q => q s) (hq i)
    simp only [ProbComp.eval_map, PMF.map_comp] at hs
    rw [eval_serverQuery, eval_serverQuery]
    exact hs
  exact fun s i i' => by rw [hview, hview, h.eval_serverQuery_eq]

/-! ### The rows transformation -/

/-- The rows transformation [CGKS, Section 3.4][ChorGoldreichKushilevitzSudan1998]: a database
indexed by `ρ × ι` is a matrix whose rows `j ↦ x (j, ·)` are databases indexed by `ι`. To read
`x (j, i)`, the user sends the queries of `P` for the column `i`, each server answers them for
every row, and the user reconstructs from the answers for the row `j`. -/
def rows (ρ : Type) (P : Scheme ι S R Q A β) : Scheme (ρ × ι) S R Q (ρ → A) β where
  query ji := P.query ji.2
  answer s x q j := P.answer s (fun i => x (j, i)) q
  reconstruct ji r a := P.reconstruct ji.2 r fun s => a s ji.1

theorem query_rows (ρ : Type) (P : Scheme ι S R Q A β) (ji : ρ × ι) :
    (P.rows ρ).query ji = P.query ji.2 := by
  rfl

theorem run_rows (ρ : Type) (P : Scheme ι S R Q A β) (x : ρ × ι → β) (j : ρ) (i : ι) :
    (P.rows ρ).run x (j, i) = P.run (fun i' => x (j, i')) i := by
  rfl

theorem IsCorrect.rows (ρ : Type) (h : P.IsCorrect) : (P.rows ρ).IsCorrect := fun x ji =>
  h (fun i => x (ji.1, i)) ji.2

theorem IsPrivate.rows (ρ : Type) (h : P.IsPrivate) : (P.rows ρ).IsPrivate :=
  h.of_query_eq Prod.snd fun _ => rfl

/-! ### Restriction along an embedding -/

/-- The scheme `P` for databases indexed by `ι'`, used on databases indexed by `ι` through an
embedding `e : ι ↪ ι'`: the user asks for `e i`, and the servers pad the database with `pad`
outside the image of `e`. -/
noncomputable def comap {ι' : Type} (P : Scheme ι' S R Q A β) (e : ι ↪ ι') (pad : β) :
    Scheme ι S R Q A β where
  query i := P.query (e i)
  answer s x q := P.answer s (Function.extend e x fun _ => pad) q
  reconstruct i r a := P.reconstruct (e i) r a

theorem query_comap {ι' : Type} (P : Scheme ι' S R Q A β) (e : ι ↪ ι') (pad : β) (i : ι) :
    (P.comap e pad).query i = P.query (e i) := by
  rfl

theorem IsCorrect.comap {ι' : Type} {P : Scheme ι' S R Q A β} (h : P.IsCorrect) (e : ι ↪ ι')
    (pad : β) : (P.comap e pad).IsCorrect := fun x i => by
  have := h (Function.extend e x fun _ => pad) (e i)
  rwa [e.injective.extend_apply] at this

theorem IsPrivate.comap {ι' : Type} {P : Scheme ι' S R Q A β} (h : P.IsPrivate) (e : ι ↪ ι')
    (pad : β) : (P.comap e pad).IsPrivate :=
  h.of_query_eq e fun _ => rfl

end Scheme

/-- The rows transformation keeps the queries and multiplies the length of each one-bit answer by
the number of rows [CGKS, Section 3.4][ChorGoldreichKushilevitzSudan1998]; this is the one-bit
answer case of the accounting in Proposition 4 (Section 4.1). -/
theorem communication_rows (S Q ρ : Type) [Fintype S] [Fintype Q] [Fintype ρ] [DecidableEq ρ] :
    communication S Q (ρ → Bool) =
      Fintype.card S * (Nat.clog 2 (Fintype.card Q) + Fintype.card ρ) :=
  communication_of_card_answer S Q _ (by rw [Fintype.card_fun, Fintype.card_bool])

end Cslib.Crypto.Protocols.PIR

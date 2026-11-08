/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Languages.Probabilistic.Basic
public import Mathlib.Data.Nat.Log
import Complexity.Probability.PMF.Map

/-!
# Private information retrieval

A database is a bit string `x : ι → Bool`, replicated on the servers `S`. A user who wants the bit
`x i` sends each server one query and reconstructs `x i` from the answers. The scheme is
*private* when no single server learns anything about `i` from its query
[Chor, Goldreich, Kushilevitz and Sudan, Definition 1][ChorGoldreichKushilevitzSudan1998].

A one-round scheme `P : PIR.Scheme ι S R Q A` consists of

* a query generator `P.query i : ProbComp (R × (S → Q))`: a probabilistic program that, for the
  index `i`, outputs the user's retained state `r : R` and the query `q s : Q` for every server `s`;
* deterministic answer functions `P.answer s x : Q → A`, one per server;
* a reconstruction function `P.reconstruct i r : (S → A) → Bool`.

`P.run x i` is the user's output. `P.IsCorrect` says that this output is `x i` with probability one,
for every database and index; `P.IsPrivate` says that for every server `s`, the distribution of the
query `P.serverQuery s i` is the same for all indices `i`. Both are exact equalities of
distributions, as in the information-theoretic setting of the source. The randomness is a
`ProbComp` program, so its coins are uniform choices from finite ranges; the source's uniformly
random string `r ∈ {0,1}^ℓ` is the special case of `ProbComp.uniform (Fin ℓ → Bool)`, and its
retained state is the random string itself. Privacy is against each single server; coalitions of
servers are not covered.

The communication cost `PIR.communication S Q A` counts the bits of a fixed-length binary encoding
of every query and answer: `|S| · (⌈log₂ |Q|⌉ + ⌈log₂ |A|⌉)`. For `Q = Fin ℓq → Bool` and
`A = Fin ℓa → Bool` this is the source's `k · (ℓq + ℓa)`.

Two transformations build schemes from schemes. `Scheme.rows` is the generic transformation of
[CGKS, Section 3.4 and Proposition 4][ChorGoldreichKushilevitzSudan1998]: a database indexed by
`ρ × ι` is a matrix with rows indexed by `ρ`, the user sends the query for the column `i`, and each
server answers it once for every row. `Scheme.comap` restricts a scheme along an embedding of
indices, padding the database with `false`; it turns a scheme for a grid or a cube into one for
`Fin n`.

`PIR.HasScheme ι k c` says that some `k`-server scheme for databases indexed by `ι` is correct and
private and communicates at most `c` bits.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Scheme`: one-round multi-server schemes.
* `Cslib.Crypto.Protocols.PIR.Scheme.run`, `Cslib.Crypto.Protocols.PIR.Scheme.serverQuery`: the
  user's output and the query seen by one server.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect`, `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate`:
  perfect correctness and perfect privacy.
* `Cslib.Crypto.Protocols.PIR.communication`: the communication cost.
* `Cslib.Crypto.Protocols.PIR.Scheme.rows`, `Cslib.Crypto.Protocols.PIR.Scheme.comap`: the rows
  transformation and restriction along an embedding.
* `Cslib.Crypto.Protocols.PIR.HasScheme`: existence of a correct, private scheme with given
  numbers of servers and bits.

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.isCorrect_iff`: correctness on the support of the queries.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.rows`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.rows`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.comap`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.comap`: both transformations preserve
  correctness and privacy.
* `Cslib.Crypto.Protocols.PIR.communication_rows`: the rows transformation multiplies the answer
  length by the number of rows.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], J. ACM 45(6), 1998; numbering of the authors'
  journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability

/-- A one-round private information retrieval scheme for databases `x : ι → Bool` held by the
servers `S`, with user state `R`, queries `Q` and answers `A`
[Chor, Goldreich, Kushilevitz and Sudan, Definition 1][ChorGoldreichKushilevitzSudan1998]. -/
structure Scheme (ι S R Q A : Type) where
  /-- The user's query generator: for the index `i`, a retained state and one query per server. -/
  query : ι → ProbComp (R × (S → Q))
  /-- The answer of the server `s`, holding the database `x`, to a query. -/
  answer : S → (ι → Bool) → Q → A
  /-- The user's reconstruction of the bit `i` from the retained state and the answers. -/
  reconstruct : ι → R → (S → A) → Bool

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

namespace Scheme

variable {ι S R Q A : Type}

section Defs

variable (P : Scheme ι S R Q A)

/-- The user's output on the database `x` and the index `i`: draw the state and the queries, ask
each server, and reconstruct from the answers. -/
def run (x : ι → Bool) (i : ι) : ProbComp Bool := do
  let (r, q) ← P.query i
  pure (P.reconstruct i r fun s => P.answer s x (q s))

/-- The query that the server `s` receives when the user wants the bit `i`. -/
def serverQuery (s : S) (i : ι) : ProbComp Q :=
  (fun (_, q) => q s) <$> P.query i

/-- Perfect correctness: on every database, the user outputs the bit it asks for with
probability one. -/
def IsCorrect : Prop :=
  ∀ x i, ProbComp.eval (P.run x i) = PMF.pure (x i)

/-- Perfect privacy: for every server, the distribution of its query does not depend on the index
that the user asks for. -/
def IsPrivate : Prop :=
  ∀ s i i', ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i')

theorem eval_run (x : ι → Bool) (i : ι) :
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
reconstruct the right bit. -/
theorem isCorrect_iff : P.IsCorrect ↔ ∀ x i r q, (r, q) ∈ (ProbComp.eval (P.query i)).support →
    P.reconstruct i r (fun s => P.answer s x (q s)) = x i := by
  refine forall_congr' fun x => forall_congr' fun i => ?_
  rw [eval_run]
  constructor
  · intro h r q hrq
    have hmem : P.reconstruct i r (fun s => P.answer s x (q s)) ∈
        ((ProbComp.eval (P.query i)).map
          fun rq => P.reconstruct i rq.1 fun s => P.answer s x (rq.2 s)).support :=
      (PMF.mem_support_map_iff _ _ _).2 ⟨(r, q), hrq, rfl⟩
    rwa [h, PMF.support_pure, Set.mem_singleton_iff] at hmem
  · intro h
    rw [Cslib.Probability.PMF.map_congr_on_support _ _ (Function.const _ (x i))
      fun rq hrq => h rq.1 rq.2 hrq, PMF.map_const]

theorem isPrivate_iff : P.IsPrivate ↔
    ∀ s i i', ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i') := by
  rw [IsPrivate]

end Defs

variable {P : Scheme ι S R Q A}

/-- A correct scheme reconstructs the right bit from every state and queries the user can draw. -/
theorem IsCorrect.reconstruct_eq (h : P.IsCorrect) (x : ι → Bool) (i : ι) {r : R} {q : S → Q}
    (hrq : (r, q) ∈ (ProbComp.eval (P.query i)).support) :
    P.reconstruct i r (fun s => P.answer s x (q s)) = x i :=
  P.isCorrect_iff.mp h x i r q hrq

/-- In a private scheme, each server's query has the same distribution for all indices. -/
theorem IsPrivate.eval_serverQuery_eq (h : P.IsPrivate) (s : S) (i i' : ι) :
    ProbComp.eval (P.serverQuery s i) = ProbComp.eval (P.serverQuery s i') :=
  P.isPrivate_iff.mp h s i i'

/-! ### The rows transformation -/

/-- The rows transformation [CGKS, Section 3.4][ChorGoldreichKushilevitzSudan1998]: a database
indexed by `ρ × ι` is a matrix whose rows `j ↦ x (j, ·)` are databases indexed by `ι`. To read
`x (j, i)`, the user sends the queries of `P` for the column `i`, each server answers them for
every row, and the user reconstructs from the answers for the row `j`. -/
def rows (ρ : Type) (P : Scheme ι S R Q A) : Scheme (ρ × ι) S R Q (ρ → A) where
  query ji := P.query ji.2
  answer s x q j := P.answer s (fun i => x (j, i)) q
  reconstruct ji r a := P.reconstruct ji.2 r fun s => a s ji.1

theorem run_rows (ρ : Type) (P : Scheme ι S R Q A) (x : ρ × ι → Bool) (j : ρ) (i : ι) :
    (P.rows ρ).run x (j, i) = P.run (fun i' => x (j, i')) i := by
  rfl

theorem serverQuery_rows (ρ : Type) (P : Scheme ι S R Q A) (s : S) (j : ρ) (i : ι) :
    (P.rows ρ).serverQuery s (j, i) = P.serverQuery s i := by
  rfl

theorem IsCorrect.rows (ρ : Type) (h : P.IsCorrect) : (P.rows ρ).IsCorrect := fun x ji =>
  h (fun i => x (ji.1, i)) ji.2

theorem IsPrivate.rows (ρ : Type) (h : P.IsPrivate) : (P.rows ρ).IsPrivate := fun s ji ji' =>
  h s ji.2 ji'.2

/-! ### Restriction along an embedding -/

/-- The scheme `P` for databases indexed by `ι'`, used on databases indexed by `ι` through an
embedding `e : ι ↪ ι'`: the user asks for `e i`, and the servers pad the database with `false`
outside the image of `e`. -/
noncomputable def comap {ι' : Type} (P : Scheme ι' S R Q A) (e : ι ↪ ι') : Scheme ι S R Q A where
  query i := P.query (e i)
  answer s x q := P.answer s (Function.extend e x fun _ => false) q
  reconstruct i r a := P.reconstruct (e i) r a

theorem serverQuery_comap {ι' : Type} (P : Scheme ι' S R Q A) (e : ι ↪ ι') (s : S) (i : ι) :
    (P.comap e).serverQuery s i = P.serverQuery s (e i) := by
  rfl

theorem IsCorrect.comap {ι' : Type} {P : Scheme ι' S R Q A} (h : P.IsCorrect) (e : ι ↪ ι') :
    (P.comap e).IsCorrect := fun x i => by
  have := h (Function.extend e x fun _ => false) (e i)
  rwa [e.injective.extend_apply] at this

theorem IsPrivate.comap {ι' : Type} {P : Scheme ι' S R Q A} (h : P.IsPrivate) (e : ι ↪ ι') :
    (P.comap e).IsPrivate := fun s i i' =>
  h s (e i) (e i')

end Scheme

/-- The rows transformation keeps the queries and multiplies the length of each one-bit answer by
the number of rows [CGKS, Proposition 4][ChorGoldreichKushilevitzSudan1998]. -/
theorem communication_rows (S Q ρ : Type) [Fintype S] [Fintype Q] [Fintype ρ] [DecidableEq ρ] :
    communication S Q (ρ → Bool) =
      Fintype.card S * (Nat.clog 2 (Fintype.card Q) + Fintype.card ρ) :=
  communication_of_card_answer S Q _ (by rw [Fintype.card_fun, Fintype.card_bool])

/-! ### Existence of schemes -/

/-- Some `k`-server scheme for databases indexed by `ι` is perfectly correct and perfectly private
and communicates at most `c` bits. -/
def HasScheme (ι : Type) (k c : ℕ) : Prop :=
  ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : Scheme ι S R Q A),
    P.IsCorrect ∧ P.IsPrivate ∧ Fintype.card S = k ∧ communication S Q A ≤ c

theorem hasScheme_iff {ι : Type} {k c : ℕ} : HasScheme ι k c ↔
    ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : Scheme ι S R Q A),
      P.IsCorrect ∧ P.IsPrivate ∧ Fintype.card S = k ∧ communication S Q A ≤ c := by
  rw [HasScheme]

/-- A correct, private scheme witnesses `HasScheme`. -/
theorem Scheme.IsCorrect.hasScheme {ι S R Q A : Type} [Fintype S] [Fintype Q] [Fintype A]
    {P : Scheme ι S R Q A} (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    HasScheme ι (Fintype.card S) (communication S Q A) :=
  hasScheme_iff.mpr ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, rfl, le_rfl⟩

theorem HasScheme.mono {ι : Type} {k c c' : ℕ} (h : HasScheme ι k c) (hc : c ≤ c') :
    HasScheme ι k c' := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := hasScheme_iff.mp h
  exact hasScheme_iff.mpr ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm.trans hc⟩

end Cslib.Crypto.Protocols.PIR

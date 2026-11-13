/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount

/-!
# Typed views of word oracles

An oracle game is often stated twice: once for an adversary that sends named word requests and
reads word replies, and once for an adversary over typed queries and replies. An `OracleCodec`
records how typed queries travel on the word channels: `encodeQuery` writes a query as a request,
`decodeQuery` reads the requests that carry a query, and `encodeReply` writes each reply.

`OracleCodec.adapt` runs a word program against a typed oracle: a request that carries a query is
forwarded and its reply encoded, and any other request is answered `[]` without a call. Dually,
`OracleCodec.wordOracle` is the word oracle that a typed oracle presents. `run_adapt` and
`runWith_adapt` say that the two views agree: the typed run of `c.adapt P` is the word run of `P`
against `c.wordOracle`. A word game therefore equals the typed game of the adapted adversary
exactly when its oracle is `c.wordOracle` of the typed one, that is, when it answers requests
carrying no query with `[]` and leaves its state unchanged on them, and answers the others
through the typed oracle.

## Main definitions

* `Cslib.OracleCodec`: typed queries and replies on named word channels.
* `Cslib.OracleCodec.wordOracle`, `Cslib.OracleCodec.adapt`: the word oracle of a typed oracle,
  and a word program run against a typed oracle.
* `Cslib.OracleCodec.id`, `Cslib.OracleCodec.bitString`, `Cslib.OracleCodec.comap`,
  `Cslib.OracleCodec.withOp`: word requests themselves, fixed-width strings, transport along an
  equivalence of queries, and one copy of a codec per channel.

## Main results

* `Cslib.OracleCodec.interpret_adapt`, `Cslib.OracleCodec.run_adapt`,
  `Cslib.OracleCodec.runWith_adapt`: the typed run of an adapted program is the word run against
  the word oracle.
* `Cslib.OracleCodec.isCostBounded_adapt`, `Cslib.OracleCodec.isQueryBounded_adapt`: adapting
  keeps query budgets.
* `Cslib.OracleCodec.adapt_id`: adapting along the identity codec changes nothing.
-/

public section

namespace Cslib

/-- Typed queries `q : Q` with replies `spec q`, carried on word requests `Op × List Bool` with
word replies. Each query has one request, and `decodeQuery` recognizes exactly these requests;
replies are encoded injectively. -/
structure OracleCodec (Op Q : Type) (spec : Q → Type) where
  /-- The request carrying a query. -/
  encodeQuery : Q → Op × List Bool
  /-- The query carried by a request, if any. -/
  decodeQuery : Op × List Bool → Option Q
  /-- A request carries a query exactly when it is that query's request. -/
  decodeQuery_eq_some_iff (request : Op × List Bool) (q : Q) :
    decodeQuery request = some q ↔ encodeQuery q = request
  /-- The word reply to a query. -/
  encodeReply (q : Q) : spec q ↪ List Bool

namespace OracleCodec

universe v

variable {Op Q α β : Type} {spec : Q → Type} (c : OracleCodec Op Q spec)

/-- A query's request carries that query. -/
@[simp] theorem decodeQuery_encodeQuery (q : Q) : c.decodeQuery (c.encodeQuery q) = some q :=
  (c.decodeQuery_eq_some_iff _ q).mpr rfl

/-- Distinct queries have distinct requests. -/
theorem encodeQuery_injective : Function.Injective c.encodeQuery := fun q q' h =>
  Option.some.inj <| by rw [← c.decodeQuery_encodeQuery q, h, c.decodeQuery_encodeQuery]

/-- The word oracle presented by a typed oracle: a request carrying a query is answered through
the oracle and its reply encoded; any other request is answered `[]` without a call. -/
@[expose] def wordOracle {m : Type → Type v} [Monad m] (oracle : (q : Q) → m (spec q))
    (request : Op × List Bool) : m (List Bool) :=
  match c.decodeQuery request with
  | some q => c.encodeReply q <$> oracle q
  | none => pure []

/-- Run a word program against a typed oracle. Private samples are kept, and each request is
answered as by `c.wordOracle`, with the typed oracle as an external call. -/
@[expose] def adapt (program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α) :
    ProbOracleComp spec α :=
  ProbOracleComp.simulate (c.wordOracle (ProbOracleComp.query (spec := spec))) program

/-- The word oracle answers a query's request through the typed oracle. -/
@[simp] theorem wordOracle_encodeQuery {m : Type → Type v} [Monad m]
    (oracle : (q : Q) → m (spec q)) (q : Q) :
    c.wordOracle oracle (c.encodeQuery q) = c.encodeReply q <$> oracle q := by
  simp [wordOracle]

/-- The word oracle answers a request carrying no query with `[]`. -/
theorem wordOracle_of_decodeQuery_eq_none {m : Type → Type v} [Monad m]
    (oracle : (q : Q) → m (spec q)) {request : Op × List Bool}
    (h : c.decodeQuery request = none) : c.wordOracle oracle request = pure [] := by
  simp [wordOracle, h]

/-- Adapting keeps returned values. -/
@[simp] theorem adapt_pure (a : α) : c.adapt (pure a) = pure a := rfl

/-- Adapting preserves sequencing. -/
@[simp] theorem adapt_bind (program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α)
    (next : α → ProbOracleComp (fun _ : Op × List Bool => List Bool) β) :
    c.adapt (program >>= next) = c.adapt program >>= fun a => c.adapt (next a) :=
  ProbOracleComp.simulate_bind _ _ _

/-- Adapting preserves deterministic postprocessing. -/
@[simp] theorem adapt_map (f : α → β)
    (program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α) :
    c.adapt (f <$> program) = f <$> c.adapt program :=
  ProbOracleComp.simulate_map _ _ _

/-- Adapting keeps private samples. -/
@[simp] theorem adapt_sample (program : ProbComp α) :
    c.adapt (ProbOracleComp.sample program) = ProbOracleComp.sample program :=
  ProbOracleComp.simulate_sample _ _

/-- A word request becomes the word oracle's answer. -/
@[simp] theorem adapt_query (request : Op × List Bool) :
    c.adapt (ProbOracleComp.query request) =
      c.wordOracle (ProbOracleComp.query (spec := spec)) request :=
  ProbOracleComp.simulate_query _ _

/-- Interpreting the typed calls of the word oracle interprets the word oracle of the typed
interpretation. -/
theorem interpret_wordOracle {m : Type → Type v} [Monad m] [LawfulMonad m]
    (random : (n : ℕ) → m (Fin (n + 1))) (oracle : (q : Q) → m (spec q))
    (request : Op × List Bool) :
    OracleComp.interpret (OracleComp.sumHandler random oracle)
        (c.wordOracle (ProbOracleComp.query (spec := spec)) request) =
      c.wordOracle oracle request := by
  unfold wordOracle
  split <;> simp

/-- **Typed and word runs agree**: interpreting an adapted program with a typed oracle
interprets the word program with the word oracle, under the same interpretation of private
samples. -/
theorem interpret_adapt {m : Type → Type v} [Monad m] [LawfulMonad m]
    (random : (n : ℕ) → m (Fin (n + 1))) (oracle : (q : Q) → m (spec q))
    (program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α) :
    OracleComp.interpret (OracleComp.sumHandler random oracle) (c.adapt program) =
      OracleComp.interpret (OracleComp.sumHandler random (c.wordOracle oracle)) program := by
  rw [adapt, ProbOracleComp.interpret_simulate]
  simp only [interpret_wordOracle]

/-- Running an adapted program against a typed oracle runs the word program against its word
oracle. -/
theorem run_adapt (program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α)
    (oracle : (q : Q) → ProbComp (spec q)) :
    (c.adapt program).run oracle = program.run (c.wordOracle oracle) :=
  c.interpret_adapt _ _ _

/-- Against a stateful typed oracle, the joint law of the result and the final state of an
adapted program is that of the word program against the word oracle. -/
theorem runWith_adapt {State : Type} (oracle : (q : Q) → StateT State PMF (spec q))
    (program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α) (s : State) :
    ProbOracleComp.runWith oracle (c.adapt program) s =
      ProbOracleComp.runWith (c.wordOracle oracle) program s := by
  simp only [ProbOracleComp.runWith, OracleComp.runWith, interpret_adapt]

/-- Adapting keeps a cost budget when each query costs at most its request. -/
theorem isCostBounded_adapt {wordCost : Op × List Bool → ℕ} {cost : Q → ℕ}
    (hcost : ∀ q, cost q ≤ wordCost (c.encodeQuery q))
    {program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α} {n : ℕ}
    (h : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) wordCost) program n) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) cost) (c.adapt program) n := by
  refine ProbOracleComp.isCostBounded_simulate (fun request => ?_) h
  unfold wordOracle
  split
  · next q hq =>
    rw [← (c.decodeQuery_eq_some_iff _ _).mp hq]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((ProbOracleComp.isCostBounded_query cost q).mono (hcost q))
  · exact .pure [] _

/-- Adapting keeps a query budget. -/
theorem isQueryBounded_adapt {program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α}
    {n : ℕ} (h : program.IsQueryBounded n) : (c.adapt program).IsQueryBounded n :=
  c.isCostBounded_adapt (fun _ => le_rfl) h

/-! ### Standard codecs -/

/-- Word requests as their own queries, with word replies. -/
@[expose] protected def id (Op : Type) : OracleCodec Op (Op × List Bool) fun _ => List Bool where
  encodeQuery := _root_.id
  decodeQuery := some
  decodeQuery_eq_some_iff _ _ := by simp [eq_comm]
  encodeReply _ := Function.Embedding.refl _

/-- Adapting along the identity codec changes nothing. -/
@[simp] theorem adapt_id (program : ProbOracleComp (fun _ : Op × List Bool => List Bool) α) :
    (OracleCodec.id Op).adapt program = program := by
  have hhandler : OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
      ((OracleCodec.id Op).wordOracle (ProbOracleComp.query (spec := fun _ => List Bool))) =
      fun q => OracleComp.query q := by
    funext q
    rcases q with n | request
    · exact ProbOracleComp.sample_unifFin n
    · simp [wordOracle, OracleCodec.id, ProbOracleComp.query, Function.Embedding.coe_refl]
  rw [adapt, ProbOracleComp.simulate, hhandler, OracleComp.interpret_query_eq_self]

/-- `n`-bit strings on the single word channel: a request carries a query exactly when it has
`n` bits. -/
@[expose] def bitString (n : ℕ) : OracleCodec Unit (BitString n) fun _ => BitString n where
  encodeQuery x := ((), List.ofFn x)
  decodeQuery request := if request.2.length = n then some (BitString.ofList n request.2) else none
  decodeQuery_eq_some_iff := by
    rintro ⟨⟨⟩, word⟩ x
    by_cases hlength : word.length = n
    · simp only [hlength, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
      constructor
      · rintro rfl
        exact BitString.ofFn_ofList hlength
      · rintro rfl
        exact BitString.ofList_ofFn x
    · simp only [hlength, ↓reduceIte, reduceCtorEq, false_iff, Prod.mk.injEq, true_and]
      rintro rfl
      simp at hlength
  encodeReply _ := ⟨List.ofFn, List.ofFn_injective⟩

/-- Transport a codec along an equivalence of queries and embeddings of replies. -/
@[expose] def comap {Q' : Type} {spec' : Q' → Type} (e : Q' ≃ Q)
    (reply : (q : Q') → spec' q ↪ spec (e q)) : OracleCodec Op Q' spec' where
  encodeQuery q := c.encodeQuery (e q)
  decodeQuery request := (c.decodeQuery request).map e.symm
  decodeQuery_eq_some_iff request q := by
    rw [Option.map_eq_some_iff, ← c.decodeQuery_eq_some_iff]
    constructor
    · rintro ⟨q', hq', rfl⟩
      simpa using hq'
    · intro hq
      exact ⟨e q, hq, e.symm_apply_apply q⟩
  encodeReply q := (reply q).trans (c.encodeReply (e q))

/-- One copy of a single-channel codec on each channel `Op`: the query `(op, q)` is the request
of `q` on channel `op`. -/
@[expose] def withOp (Op : Type) {R : Type} (c : OracleCodec Unit Q fun _ => R) :
    OracleCodec Op (Op × Q) fun _ => R where
  encodeQuery q := (q.1, (c.encodeQuery q.2).2)
  decodeQuery request := (c.decodeQuery ((), request.2)).map (request.1, ·)
  decodeQuery_eq_some_iff := by
    rintro ⟨op, word⟩ ⟨op', q⟩
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, c.decodeQuery_eq_some_iff]
    constructor
    · rintro ⟨q', hq', rfl, rfl⟩
      exact ⟨rfl, by rw [hq']⟩
    · rintro ⟨rfl, hq⟩
      exact ⟨q, Prod.ext rfl hq, rfl, rfl⟩
  encodeReply q := c.encodeReply q.2

/-- The word oracle of `withOp` reads the word on any channel with the single-channel codec. -/
theorem wordOracle_withOp {R : Type} {m : Type → Type v} [Monad m]
    (c : OracleCodec Unit Q fun _ => R) (oracle : Op × Q → m R) (request : Op × List Bool) :
    (withOp Op c).wordOracle oracle request =
      c.wordOracle (fun q => oracle (request.1, q)) ((), request.2) := by
  unfold wordOracle withOp
  cases h : c.decodeQuery ((), request.2) <;> simp [h]

end OracleCodec

end Cslib

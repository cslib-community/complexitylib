/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Probability.Product
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Languages.Probabilistic.UntilBad

/-!
# Gap-CDH and the random-oracle Diffie–Hellman KEM

Over a group of prime order `q` with generator `g` from a `PrimeOrderGroupFamily`, the gap
computational Diffie–Hellman (gap-CDH) experiment ([KatzLindell2020], §12.4.4, p. 434) draws
uniform exponents `a, b`, gives the adversary `(a • g, b • g)` together with a decisional
Diffie–Hellman oracle `O_b` answering a query `(U, V)` with `true` exactly when `V = b • U`, and
accepts when the adversary outputs `(a * b) • g`.

The random-oracle KEM of [KatzLindell2020], Construction 12.19 (p. 431), has public key
`h = x • g` for a uniform exponent `x`; encapsulation draws a uniform `y` and outputs the
ciphertext `y • g` with key `H (y • h)`, and decapsulation of `c` returns `H (x • c)`. The
CCA experiment ([KatzLindell2020], Definition 12.13, p. 425) gives the adversary the public key,
the challenge ciphertext and either the real key or an independent key, together with the random
oracle `H` and a decapsulation oracle that refuses the challenge ciphertext.

We prove [KatzLindell2020], Theorem 12.22 (p. 435) as a concrete reduction: the distinguishing
advantage of every CCA adversary against the KEM is at most the success probability of an
explicit gap-CDH adversary `dhKEMToGapCDH`. The reduction runs the KEM adversary, answering hash
and decapsulation queries consistently from a table of past queries by asking the DDH oracle
whether a hash point `z` and a ciphertext `c` satisfy `z = x • c`; it then outputs the first hash
point `z` with `z = x • c⋆` for the challenge ciphertext `c⋆`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOracle`, `Cslib.Crypto.PrimeOrderGroupFamily.runDDH`:
  the oracle `O_b` and the execution of a program against it.
* `Cslib.Crypto.PrimeOrderGroupFamily.gapCDHGame`: the gap-CDH experiment.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhKEMEncaps`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhKEMDecaps`: Construction 12.19 for a fixed hash function.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhKEMCCAGame`: the CCA experiment in the random-oracle model.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhKEMToGapCDH`: the reduction of Theorem 12.22.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.dhKEMDecaps_encaps`: decapsulation recovers the key.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_dhKEMCCAGame_le`: the CCA advantage is at most
  the gap-CDH success probability of `dhKEMToGapCDH`.

## Implementation notes

The statement is concrete for one group of the family. KEM adversaries are deterministic oracle
programs; a randomized adversary reduces to these by fixing its coins, since the bound holds for
every coin sequence. The key distribution is an arbitrary finite sampler, which covers the
uniform `ℓ`-bit keys of Construction 12.19. Unlike the textbook proof, the reduction outputs `0`
when the public key is `0`, which is then the correct answer, so the bound has no additive term.

The proof replaces the eagerly sampled random function by a lazily sampled one
(`Cslib.RandomOracle.interpret_eq_lazy`), programs the real key at the point `x • c⋆`, and
compares the real and ideal runs until the random oracle is first evaluated at `x • c⋆`. The
reduction's tables represent the lazy random-oracle cache exactly, and an evaluation at
`x • c⋆` leaves a hash entry the reduction extracts.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], 3rd edition,
  Construction 12.19, §12.4.4, Theorem 12.22 and Definition 12.13
-/

public section

noncomputable section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open OracleComp Probability

/-- The queries of a CCA adversary against the Diffie–Hellman KEM: random-oracle evaluations and
decapsulations. -/
inductive DHKEMQuery (G : Type) where
  /-- Evaluate the random oracle at a group element. -/
  | hash (point : G)
  /-- Decapsulate a ciphertext. -/
  | decaps (ciphertext : G)

/-- Hash queries return keys; decapsulation queries return a key, or `none` on the challenge. -/
abbrev DHKEMSpec (G K : Type) : OracleSpec (DHKEMQuery G)
  | .hash _ => K
  | .decaps _ => Option K

variable (F : PrimeOrderGroupFamily) (d : F.Desc) {K : Type}

/-- The interface of a DDH oracle: a query `(U, V)` is answered by a bit. -/
abbrev DDHSpec : OracleSpec (F.Carrier d × F.Carrier d) := fun _ => Bool

/-- A gap-CDH adversary maps `(a • g, b • g)` to a guess, with fresh coins and the oracle `O_b`. -/
abbrev GapCDHAdversary := F.Carrier d × F.Carrier d → ProbOracleComp (F.DDHSpec d) (F.Carrier d)

/-- Encapsulation of Construction 12.19 with hash function `H`, public key `h` and exponent `y`:
the ciphertext `y • g` and the key `H (y • h)`. -/
@[expose] def dhKEMEncaps (H : F.Carrier d → K) (h : F.Carrier d) (y : ZMod (F.order d)) :
    F.Carrier d × K :=
  (y • F.generator d, H (y • h))

/-- Decapsulation of Construction 12.19 with hash function `H` and secret key `x`. -/
@[expose]
def dhKEMDecaps (H : F.Carrier d → K) (x : ZMod (F.order d)) (ciphertext : F.Carrier d) : K :=
  H (x • ciphertext)

/-- Decapsulating an encapsulation under the matching secret key recovers its key. -/
theorem dhKEMDecaps_encaps (H : F.Carrier d → K) (x y : ZMod (F.order d)) :
    F.dhKEMDecaps d H x (F.dhKEMEncaps d H (x • F.generator d) y).1 =
      (F.dhKEMEncaps d H (x • F.generator d) y).2 := by
  simp only [dhKEMDecaps, dhKEMEncaps, smul_smul, mul_comm]

/-- A CCA adversary against the KEM maps `(public key, challenge ciphertext, key)` to a guess,
querying the random oracle and the decapsulation oracle. -/
abbrev DHKEMAdversary (K : Type) :=
  F.Carrier d × F.Carrier d × K → OracleComp (DHKEMSpec (F.Carrier d) K) Bool

/-- The reduction's table of answered queries: hash points (`inl`) and decapsulated ciphertexts
(`inr`), each with the key returned for it. -/
abbrev SimTable (K : Type) := List ((F.Carrier d ⊕ F.Carrier d) × K)

variable [DecidableEq (F.Carrier d)]

/-- The DDH oracle `O_y` of [KatzLindell2020], §12.4.4: `(U, V)` is answered `true` exactly
when `V = y • U`. -/
@[expose] def ddhOracle (y : ZMod (F.order d)) (query : F.Carrier d × F.Carrier d) : PMF Bool :=
  PMF.pure (decide (query.2 = y • query.1))

/-- Run a program with fresh uniform coins and the DDH oracle `O_y`. -/
@[expose] def runDDH {α : Type} (y : ZMod (F.order d)) (program : ProbOracleComp (F.DDHSpec d) α) :
    PMF α :=
  OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (F.ddhOracle d y)) program

/-- The gap-CDH experiment ([KatzLindell2020], §12.4.4): on `(a • g, b • g)` and with the oracle
`O_b`, the adversary must output `(a * b) • g`. -/
@[expose] def gapCDHGame (adversary : F.GapCDHAdversary d) : Game := do
  let a ← PMF.uniformOfFintype (ZMod (F.order d))
  let b ← PMF.uniformOfFintype (ZMod (F.order d))
  let guess ← F.runDDH d b (adversary (a • F.generator d, b • F.generator d))
  return decide (guess = (a * b) • F.generator d)

/-- The honest answer to a KEM query, for hash function `H`, secret key `x` and challenge
ciphertext `challenge`. -/
@[expose] def dhKEMAnswer (H : F.Carrier d → K) (x : ZMod (F.order d)) (challenge : F.Carrier d) :
    (q : DHKEMQuery (F.Carrier d)) → DHKEMSpec (F.Carrier d) K q
  | .hash z => H z
  | .decaps c => if c = challenge then none else some (F.dhKEMDecaps d H x c)

/-- The CCA experiment for Construction 12.19 in the random-oracle model
([KatzLindell2020], Definition 12.13): `H` is a random function with keys drawn by `sampleKey`,
and the adversary receives the real key when `bit` is `true` and an independent key otherwise. -/
@[expose] def dhKEMCCAGame [Fintype (F.Carrier d)] [Finite K] (sampleKey : ProbComp K)
    (adversary : F.DHKEMAdversary d K) (bit : Bool) : Game := do
  let x ← PMF.uniformOfFintype (ZMod (F.order d))
  let y ← PMF.uniformOfFintype (ZMod (F.order d))
  let H ← Probability.PMF.pi fun _ : F.Carrier d => ProbComp.eval sampleKey
  let random ← ProbComp.eval sampleKey
  let encapsulation := F.dhKEMEncaps d H (x • F.generator d) y
  OracleComp.interpret (fun q => PMF.pure (F.dhKEMAnswer d H x encapsulation.1 q))
    (adversary (x • F.generator d, encapsulation.1,
      if bit then encapsulation.2 else random))

/-- The first key in a table whose label passes a test made with the DDH oracle. -/
private def findEntry {L : Type} (test : L → ProbOracleComp (F.DDHSpec d) Bool) :
    List (L × K) → ProbOracleComp (F.DDHSpec d) (Option K)
  | [] => pure none
  | entry :: rest => do
    if ← test entry.1 then return some entry.2 else findEntry test rest

/-- Answer a query with the key of the first matching entry, or with a fresh key recorded under
`label`. -/
private def simLookup {L : Type} (sampleKey : ProbComp K)
    (test : L → ProbOracleComp (F.DDHSpec d) Bool) (label : L) :
    StateT (List (L × K)) (ProbOracleComp (F.DDHSpec d)) K := fun table => do
  match ← F.findEntry d test table with
  | some key => return (key, table)
  | none =>
    let key ← ProbOracleComp.sample sampleKey
    return (key, (label, key) :: table)

/-- Does a table label belong to the hash point `z`? A hash entry `z'` does when `z' = z`, and a
decapsulation entry `c` does when `z = x • c`, which the DDH oracle decides. -/
private def hashTest (z : F.Carrier d) :
    F.Carrier d ⊕ F.Carrier d → ProbOracleComp (F.DDHSpec d) Bool
  | .inl z' => pure (decide (z' = z))
  | .inr c => ProbOracleComp.query (c, z)

/-- Does a table label belong to the ciphertext `c`? A hash entry `z` does when `z = x • c`, which
the DDH oracle decides, and a decapsulation entry `c'` does when `c' = c`. -/
private def decapsTest (c : F.Carrier d) :
    F.Carrier d ⊕ F.Carrier d → ProbOracleComp (F.DDHSpec d) Bool
  | .inl z => ProbOracleComp.query (c, z)
  | .inr c' => pure (decide (c' = c))

/-- The reduction's answers to KEM queries: consistent keys from its table, and no answer to the
challenge ciphertext. -/
def simHandler (sampleKey : ProbComp K) (challenge : F.Carrier d) :
    (q : DHKEMQuery (F.Carrier d)) →
      StateT (F.SimTable d K) (ProbOracleComp (F.DDHSpec d)) (DHKEMSpec (F.Carrier d) K q)
  | .hash z => F.simLookup d sampleKey (F.hashTest d z) (.inl z)
  | .decaps c =>
    if c = challenge then pure none
    else some <$> F.simLookup d sampleKey (F.decapsTest d c) (.inr c)

/-- The first hash point `z` of a table with `z = x • challenge`, or `0` if there is none. -/
def extractDH (challenge : F.Carrier d) :
    F.SimTable d K → ProbOracleComp (F.DDHSpec d) (F.Carrier d)
  | [] => pure 0
  | (.inl z, _) :: rest => do
    if ← ProbOracleComp.query (challenge, z) then return z else extractDH challenge rest
  | (.inr _, _) :: rest => extractDH challenge rest

/-- The gap-CDH adversary of [KatzLindell2020], Theorem 12.22: on `(c⋆, h)` it runs the KEM
adversary on public key `h`, challenge ciphertext `c⋆` and a fresh key, answers its queries with
`simHandler`, and outputs the hash point `x • c⋆` if the adversary asked for it. -/
@[expose] def dhKEMToGapCDH (sampleKey : ProbComp K) (adversary : F.DHKEMAdversary d K) :
    F.GapCDHAdversary d := fun input =>
  if input.2 = 0 then pure 0
  else do
    let key ← ProbOracleComp.sample sampleKey
    let result ← (OracleComp.interpret (F.simHandler d sampleKey input.1)
      (adversary (input.2, input.1, key))).run []
    F.extractDH d input.1 result.2

/-! ### Executing the reduction against the DDH oracle -/

section Execution

variable {α β : Type}

@[simp] private theorem runDDH_pure (y : ZMod (F.order d)) (a : α) :
    F.runDDH d y (pure a) = PMF.pure a := rfl

private theorem runDDH_bind (y : ZMod (F.order d)) (program : ProbOracleComp (F.DDHSpec d) α)
    (next : α → ProbOracleComp (F.DDHSpec d) β) :
    F.runDDH d y (program >>= next) = (F.runDDH d y program).bind fun a => F.runDDH d y (next a) :=
  OracleComp.interpret_bind _ _ _

private theorem runDDH_map (y : ZMod (F.order d)) (f : α → β)
    (program : ProbOracleComp (F.DDHSpec d) α) :
    F.runDDH d y (f <$> program) = (F.runDDH d y program).map f :=
  OracleComp.interpret_map _ _ _

private theorem runDDH_query (y : ZMod (F.order d)) (q : F.Carrier d × F.Carrier d) :
    F.runDDH d y (ProbOracleComp.query q) = F.ddhOracle d y q :=
  ProbOracleComp.interpret_query _ _ q

private theorem runDDH_sample (y : ZMod (F.order d)) (program : ProbComp α) :
    F.runDDH d y (ProbOracleComp.sample program) = ProbComp.eval program :=
  ProbOracleComp.interpret_sample _ _ program

/-- A stateful handler over the DDH interface, with every call executed against `O_y`. -/
private def lowerHandler {σ ι : Type} {spec : OracleSpec ι} (y : ZMod (F.order d))
    (handler : (q : ι) → StateT σ (ProbOracleComp (F.DDHSpec d)) (spec q)) (q : ι) :
    StateT σ PMF (spec q) :=
  fun t => F.runDDH d y ((handler q).run t)

/-- Executing a stateful handler against the DDH oracle executes each of its calls. -/
private theorem runDDH_run_interpret {σ ι : Type} {spec : OracleSpec ι} (y : ZMod (F.order d))
    (handler : (q : ι) → StateT σ (ProbOracleComp (F.DDHSpec d)) (spec q))
    (program : OracleComp spec α) (s : σ) :
    F.runDDH d y ((OracleComp.interpret handler program).run s) =
      (OracleComp.interpret (F.lowerHandler d y handler) program).run s := by
  induction program using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_bind, runDDH_bind,
      OracleComp.run_interpret_query, OracleComp.run_interpret_query]
    simp only [ih]
    rfl

private theorem runDDH_findEntry {L : Type} (y : ZMod (F.order d))
    (test : L → ProbOracleComp (F.DDHSpec d) Bool) (decision : L → Bool)
    (htest : ∀ l, F.runDDH d y (test l) = PMF.pure (decision l)) (table : List (L × K)) :
    F.runDDH d y (F.findEntry d test table) =
      PMF.pure ((table.find? fun e => decision e.1).map Prod.snd) := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    rw [findEntry, runDDH_bind, htest, PMF.pure_bind]
    cases h : decision e.1 <;> simp [h, ih]

private theorem runDDH_simLookup_of_some {L : Type} (y : ZMod (F.order d))
    (sampleKey : ProbComp K) (test : L → ProbOracleComp (F.DDHSpec d) Bool) (decision : L → Bool)
    (htest : ∀ l, F.runDDH d y (test l) = PMF.pure (decision l)) (label : L)
    (table : List (L × K)) (key : K)
    (hfind : (table.find? fun e => decision e.1).map Prod.snd = some key) :
    F.runDDH d y ((F.simLookup d sampleKey test label).run table) = PMF.pure (key, table) := by
  simp only [simLookup, StateT.run, runDDH_bind, F.runDDH_findEntry d y test decision htest,
    hfind, PMF.pure_bind]
  rfl

private theorem runDDH_simLookup_of_none {L : Type} (y : ZMod (F.order d))
    (sampleKey : ProbComp K) (test : L → ProbOracleComp (F.DDHSpec d) Bool) (decision : L → Bool)
    (htest : ∀ l, F.runDDH d y (test l) = PMF.pure (decision l)) (label : L)
    (table : List (L × K))
    (hfind : (table.find? fun e => decision e.1).map Prod.snd = none) :
    F.runDDH d y ((F.simLookup d sampleKey test label).run table) =
      (ProbComp.eval sampleKey).map fun key => (key, (label, key) :: table) := by
  simp only [simLookup, StateT.run, runDDH_bind, F.runDDH_findEntry d y test decision htest,
    hfind, PMF.pure_bind, runDDH_sample]
  rfl

end Execution

/-! ### The reduction's tables represent a lazy random-oracle cache -/

section Simulation

/-- KEM queries as random-oracle queries: a hash query at `z` evaluates `H z`, and the
decapsulation of `c ≠ challenge` evaluates `H (x • c)`. -/
private def routeQuery (x : ZMod (F.order d)) (challenge : F.Carrier d) :
    (q : DHKEMQuery (F.Carrier d)) →
      OracleComp (fun _ : F.Carrier d => K) (DHKEMSpec (F.Carrier d) K q)
  | .hash z => OracleComp.query (spec := fun _ : F.Carrier d => K) z
  | .decaps c =>
    if c = challenge then pure none
    else some <$> OracleComp.query (spec := fun _ : F.Carrier d => K) (x • c)

/-- The random-oracle point of a table label for secret key `x`. -/
private def entryPoint (x : ZMod (F.order d)) : F.Carrier d ⊕ F.Carrier d → F.Carrier d
  | .inl z => z
  | .inr c => x • c

/-- The lazy random-oracle cache represented by a table. -/
private def tableCache (x : ZMod (F.order d)) (table : F.SimTable d K) :
    RandomOracle.Cache (fun _ : F.Carrier d => K) :=
  fun z => (table.find? fun e => decide (F.entryPoint d x e.1 = z)).map Prod.snd

private theorem tableCache_nil (x : ZMod (F.order d)) :
    F.tableCache d x ([] : F.SimTable d K) = fun _ => none := rfl

private theorem tableCache_cons (x : ZMod (F.order d)) (label : F.Carrier d ⊕ F.Carrier d)
    (key : K) (table : F.SimTable d K) :
    F.tableCache d x ((label, key) :: table) =
      Function.update (F.tableCache d x table) (F.entryPoint d x label) (some key) := by
  funext z
  by_cases h : F.entryPoint d x label = z
  · subst h
    simp [tableCache]
  · simp [tableCache, h, Function.update_of_ne (Ne.symm h)]

omit [DecidableEq (F.Carrier d)] in
private theorem smul_inj (x : ZMod (F.order d)) (hx : x ≠ 0) {c c' : F.Carrier d} :
    x • c = x • c' ↔ c = c' := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  simpa only [inv_smul_smul₀ hx] using congrArg (x⁻¹ • ·) h

private theorem runDDH_hashTest (x : ZMod (F.order d)) (z : F.Carrier d)
    (label : F.Carrier d ⊕ F.Carrier d) :
    F.runDDH d x (F.hashTest d z label) = PMF.pure (decide (F.entryPoint d x label = z)) := by
  cases label with
  | inl z' => rfl
  | inr c =>
    rw [hashTest, runDDH_query, ddhOracle]
    exact congrArg PMF.pure (decide_eq_decide.mpr eq_comm)

private theorem runDDH_decapsTest (x : ZMod (F.order d)) (hx : x ≠ 0) (c : F.Carrier d)
    (label : F.Carrier d ⊕ F.Carrier d) :
    F.runDDH d x (F.decapsTest d c label) =
      PMF.pure (decide (F.entryPoint d x label = x • c)) := by
  cases label with
  | inl z => rw [decapsTest, runDDH_query]; rfl
  | inr c' => exact congrArg PMF.pure (decide_eq_decide.mpr (F.smul_inj d x hx).symm)

/-- One lookup of the reduction is one lazy random-oracle answer on the represented cache. -/
private theorem simLookup_step (x : ZMod (F.order d)) (sampleKey : ProbComp K)
    (test : F.Carrier d ⊕ F.Carrier d → ProbOracleComp (F.DDHSpec d) Bool) (point : F.Carrier d)
    (label : F.Carrier d ⊕ F.Carrier d)
    (htest : ∀ l, F.runDDH d x (test l) = PMF.pure (decide (F.entryPoint d x l = point)))
    (hlabel : F.entryPoint d x label = point) (table : F.SimTable d K) :
    (F.runDDH d x ((F.simLookup d sampleKey test label).run table)).map
        (fun r => (r.1, F.tableCache d x r.2)) =
      RandomOracle.answer (fun _ => ProbComp.eval sampleKey) point (F.tableCache d x table) := by
  cases hfind : (table.find? fun e => decide (F.entryPoint d x e.1 = point)).map Prod.snd with
  | some key =>
    rw [F.runDDH_simLookup_of_some d x sampleKey test _ htest label table key hfind, PMF.pure_map,
      RandomOracle.answer_of_some (fun _ => ProbComp.eval sampleKey) (F.tableCache d x table) point
        key hfind]
  | none =>
    rw [F.runDDH_simLookup_of_none d x sampleKey test _ htest label table hfind, PMF.map_comp,
      RandomOracle.answer_of_none (fun _ => ProbComp.eval sampleKey) (F.tableCache d x table) point
        hfind]
    congr 1
    funext key
    simp [tableCache_cons, hlabel]

/-- Tables that never record the challenge ciphertext. -/
private def NoChallengeEntry (challenge : F.Carrier d) (table : F.SimTable d K) : Prop :=
  ∀ e ∈ table, e.1 ≠ .inr challenge

private theorem simLookup_support (x : ZMod (F.order d)) (sampleKey : ProbComp K)
    (test : F.Carrier d ⊕ F.Carrier d → ProbOracleComp (F.DDHSpec d) Bool)
    (decision : F.Carrier d ⊕ F.Carrier d → Bool)
    (htest : ∀ l, F.runDDH d x (test l) = PMF.pure (decision l))
    (label : F.Carrier d ⊕ F.Carrier d) (table : F.SimTable d K) (r : K × F.SimTable d K)
    (hr : r ∈ (F.runDDH d x ((F.simLookup d sampleKey test label).run table)).support) :
    r.2 = table ∨ r.2 = (label, r.1) :: table := by
  cases hfind : (table.find? fun e => decision e.1).map Prod.snd with
  | some key =>
    rw [F.runDDH_simLookup_of_some d x sampleKey test decision htest label table key hfind,
      PMF.mem_support_pure_iff] at hr
    exact Or.inl (by rw [hr])
  | none =>
    rw [F.runDDH_simLookup_of_none d x sampleKey test decision htest label table hfind,
      PMF.support_map] at hr
    obtain ⟨key, -, rfl⟩ := hr
    exact Or.inr rfl

private theorem lowerHandler_decaps_self (x : ZMod (F.order d)) (sampleKey : ProbComp K)
    (challenge : F.Carrier d) (table : F.SimTable d K) :
    F.lowerHandler d x (F.simHandler d sampleKey challenge) (.decaps challenge) table =
      PMF.pure (none, table) := by
  simp only [lowerHandler, simHandler, ↓reduceIte]
  rfl

private theorem lowerHandler_decaps_of_ne (x : ZMod (F.order d)) (sampleKey : ProbComp K)
    (challenge c : F.Carrier d) (hc : c ≠ challenge) (table : F.SimTable d K) :
    F.lowerHandler d x (F.simHandler d sampleKey challenge) (.decaps c) table =
      (F.runDDH d x ((F.simLookup d sampleKey (F.decapsTest d c) (.inr c)).run table)).map
        fun r => (some r.1, r.2) := by
  simp only [lowerHandler, simHandler, hc, ↓reduceIte, StateT.run_map, runDDH_map]

private theorem lowerHandler_noChallenge (x : ZMod (F.order d)) (hx : x ≠ 0)
    (sampleKey : ProbComp K) (challenge : F.Carrier d) (q : DHKEMQuery (F.Carrier d))
    (table : F.SimTable d K) (htable : F.NoChallengeEntry d challenge table)
    (a : DHKEMSpec (F.Carrier d) K q) (table' : F.SimTable d K)
    (h : (a, table') ∈ (F.lowerHandler d x (F.simHandler d sampleKey challenge) q table).support) :
    F.NoChallengeEntry d challenge table' := by
  cases q with
  | hash z =>
    rcases F.simLookup_support d x sampleKey _ _ (F.runDDH_hashTest d x z) (.inl z) table _
      h with h' | h'
    · rw [show table' = table from h']
      exact htable
    · rw [show table' = _ from h']
      exact List.forall_mem_cons.mpr ⟨Sum.inl_ne_inr, htable⟩
  | decaps c =>
    by_cases hc : c = challenge
    · rw [hc, lowerHandler_decaps_self, PMF.mem_support_pure_iff] at h
      exact (Prod.mk.inj h).2 ▸ htable
    · rw [F.lowerHandler_decaps_of_ne d x sampleKey challenge c hc, PMF.support_map] at h
      obtain ⟨r, hr, hra⟩ := h
      rw [show table' = r.2 from (Prod.mk.inj hra).2.symm]
      rcases F.simLookup_support d x sampleKey _ _ (F.runDDH_decapsTest d x hx c) (.inr c) table
        r hr with h' | h'
      · rw [h']
        exact htable
      · rw [h']
        exact List.forall_mem_cons.mpr ⟨fun h => hc (Sum.inr_injective h), htable⟩

/-- A simulated query is the lazy random-oracle answer on the represented cache. -/
private theorem lowerHandler_step (x : ZMod (F.order d)) (hx : x ≠ 0) (sampleKey : ProbComp K)
    (challenge : F.Carrier d) (q : DHKEMQuery (F.Carrier d)) (table : F.SimTable d K) :
    (F.lowerHandler d x (F.simHandler d sampleKey challenge) q table).map
        (fun (a, t) => (a, F.tableCache d x t)) =
      OracleComp.interpret (RandomOracle.answer fun _ => ProbComp.eval sampleKey)
        (F.routeQuery d x challenge q) (F.tableCache d x table) := by
  cases q with
  | hash z =>
    simp only [routeQuery, OracleComp.interpret_query]
    exact F.simLookup_step d x sampleKey _ z (.inl z) (F.runDDH_hashTest d x z) rfl table
  | decaps c =>
    by_cases hc : c = challenge
    · rw [hc, lowerHandler_decaps_self, PMF.pure_map]
      simp only [routeQuery, ↓reduceIte]
      rfl
    · rw [F.lowerHandler_decaps_of_ne d x sampleKey challenge c hc, PMF.map_comp]
      simp only [routeQuery, hc, ↓reduceIte, OracleComp.interpret_map,
        OracleComp.interpret_query]
      rw [show (Option.some <$> RandomOracle.answer (fun _ => ProbComp.eval sampleKey) (x • c))
          (F.tableCache d x table) =
          ((RandomOracle.answer (fun _ => ProbComp.eval sampleKey) (x • c))
            (F.tableCache d x table)).map (fun r => (some r.1, r.2)) from rfl,
        ← F.simLookup_step d x sampleKey _ (x • c) (.inr c) (F.runDDH_decapsTest d x hx c) rfl,
        PMF.map_comp]
      rfl

private theorem runDDH_extractDH (x : ZMod (F.order d)) (challenge : F.Carrier d)
    (table : F.SimTable d K) (h : ∃ key, (.inl (x • challenge), key) ∈ table) :
    F.runDDH d x (F.extractDH d challenge table) = PMF.pure (x • challenge) := by
  induction table with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨l, key⟩ := e
    have hrest (hl : l ≠ .inl (x • challenge)) : ∃ key, (.inl (x • challenge), key) ∈ rest := by
      obtain ⟨k, hk⟩ := h
      rcases List.mem_cons.mp hk with hk | hk
      · exact absurd (Prod.mk.inj hk).1.symm hl
      · exact ⟨k, hk⟩
    cases l with
    | inl z =>
      by_cases hz : z = x • challenge
      · simp [extractDH, runDDH_bind, runDDH_query, ddhOracle, hz]
      · simp [extractDH, runDDH_bind, runDDH_query, ddhOracle, hz,
          ih (hrest fun h => hz (Sum.inl_injective h))]
    | inr c => simp [extractDH, ih (hrest Sum.inr_ne_inl)]

private theorem exists_mem_of_tableCache (x : ZMod (F.order d)) (hx : x ≠ 0)
    (challenge : F.Carrier d) (table : F.SimTable d K)
    (hinv : F.NoChallengeEntry d challenge table)
    (h : F.tableCache d x table (x • challenge) ≠ none) :
    ∃ key, (.inl (x • challenge), key) ∈ table := by
  simp only [tableCache, ne_eq, Option.map_eq_none_iff, List.find?_eq_none, not_forall,
    decide_eq_true_eq, not_not] at h
  obtain ⟨⟨l, key⟩, hmem, hl⟩ := h
  cases l with
  | inl z => exact ⟨key, by rwa [show z = x • challenge from hl] at hmem⟩
  | inr c => exact absurd (by rw [(F.smul_inj d x hx).mp hl]) (hinv _ hmem)

end Simulation

/-! ### Programming the random oracle at one point -/

section Programming

omit [DecidableEq (F.Carrier d)] in
private theorem toOuterMeasure_le_bind_apply {α β : Type} (μ : PMF α) (event : Set α)
    (f : α → PMF β) (b : β) (h : ∀ a ∈ μ.support, a ∈ event → f a b = 1) :
    μ.toOuterMeasure event ≤ (μ.bind f) b := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.bind_apply]
  refine tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ event
  · by_cases hs : a ∈ μ.support
    · rw [Set.indicator_of_mem ha, h a hs ha, mul_one]
    · rw [Set.indicator_of_mem ha, (PMF.apply_eq_zero_iff μ a).mpr hs, zero_mul]
  · rw [Set.indicator_of_notMem ha]
    exact zero_le

omit [DecidableEq (F.Carrier d)] in
private theorem answer_support {Q : Type} [DecidableEq Q] {law : Q → PMF K} {q : Q}
    {s : RandomOracle.Cache (fun _ : Q => K)} {r : K × RandomOracle.Cache (fun _ : Q => K)}
    (hr : r ∈ (RandomOracle.answer law q s).support) :
    r.2 q = some r.1 ∧ ∀ z, s z ≠ none → r.2 z ≠ none := by
  cases hs : s q with
  | some v =>
    rw [RandomOracle.answer_of_some law s q v hs, PMF.mem_support_pure_iff] at hr
    subst hr
    exact ⟨hs, fun _ hz => hz⟩
  | none =>
    rw [RandomOracle.answer_of_none law s q hs, PMF.support_map] at hr
    obtain ⟨v, -, rfl⟩ := hr
    refine ⟨by simp, fun z hz => ?_⟩
    by_cases hzq : z = q
    · subst hzq
      simp
    · simpa [Function.update_of_ne hzq] using hz

/-- The key distribution with the point `point` programmed to `key`. -/
private def programmedLaw (law : PMF K) (point : F.Carrier d) (key : K) (z : F.Carrier d) :
    PMF K :=
  if z = point then PMF.pure key else law

/-- Record `key` at `point` unless the cache already answers `point`. -/
private def programCache (point : F.Carrier d) (key : K)
    (cache : RandomOracle.Cache (fun _ : F.Carrier d => K)) :
    RandomOracle.Cache (fun _ : F.Carrier d => K) :=
  if cache point = none then Function.update cache point (some key) else cache

private theorem answer_programmedLaw_of_ne (law : PMF K) (point : F.Carrier d) (key : K)
    (q : F.Carrier d) (hq : q ≠ point) :
    RandomOracle.answer (F.programmedLaw d law point key) q =
      RandomOracle.answer (fun _ => law) q := by
  unfold RandomOracle.answer
  simp only [programmedLaw, ite_eq_right hq]

private theorem programCache_step_of_none (law : PMF K) (point : F.Carrier d) (key : K)
    (q : F.Carrier d) (s : RandomOracle.Cache (fun _ : F.Carrier d => K)) (hs : s point = none) :
    (RandomOracle.answer (F.programmedLaw d law point key) q s).map
        (fun (a, s') => (a, F.programCache d point key s')) =
      RandomOracle.answer (fun _ => law) q (F.programCache d point key s) := by
  rw [show F.programCache d point key s = Function.update s point (some key) from ite_eq_left hs]
  by_cases hq : q = point
  · subst hq
    rw [RandomOracle.answer_of_none _ s q hs, RandomOracle.answer_of_some (fun _ => law) _ q key
      (by simp)]
    simp [programmedLaw, programCache]
  · rw [F.answer_programmedLaw_of_ne d law point key q hq]
    cases hsq : s q with
    | some v =>
      rw [RandomOracle.answer_of_some _ s q v hsq, RandomOracle.answer_of_some (fun _ => law) _ q v
        (by rwa [Function.update_of_ne hq]), PMF.pure_map]
      simp [programCache, hs]
    | none =>
      rw [RandomOracle.answer_of_none _ s q hsq, RandomOracle.answer_of_none (fun _ => law) _ q
        (by rwa [Function.update_of_ne hq]), PMF.map_comp]
      congr 1
      funext v
      simp [programCache, Function.update_of_ne (Ne.symm hq), hs, Function.update_comm hq]

private theorem programCache_step (law : PMF K) (point : F.Carrier d) (key : K)
    (q : F.Carrier d) (s : RandomOracle.Cache (fun _ : F.Carrier d => K)) :
    (RandomOracle.answer (F.programmedLaw d law point key) q s).map
        (fun (a, s') => (a, F.programCache d point key s')) =
      RandomOracle.answer (fun _ => law) q (F.programCache d point key s) := by
  by_cases hs : s point = none
  · exact F.programCache_step_of_none d law point key q s hs
  have hans : RandomOracle.answer (F.programmedLaw d law point key) q s =
      RandomOracle.answer (fun _ => law) q s := by
    by_cases hq : q = point
    · subst hq
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hs
      rw [RandomOracle.answer_of_some _ _ _ v hv, RandomOracle.answer_of_some _ _ _ v hv]
    · rw [F.answer_programmedLaw_of_ne d law point key q hq]
  rw [hans, show F.programCache d point key s = s from ite_eq_right hs]
  calc _ = (RandomOracle.answer (fun _ => law) q s).map id :=
        Probability.PMF.bind_congr_on_support _ _ _ fun r hr => by
          simp [programCache, (answer_support hr).2 point hs]
    _ = _ := PMF.map_id _

/-- Programming `point` agrees with the lazy random oracle until `point` is evaluated. -/
private theorem identicalUntilBad_programmedLaw (law : PMF K) (point : F.Carrier d) (key : K) :
    OracleComp.IdenticalUntilBad (RandomOracle.answer (F.programmedLaw d law point key))
      (RandomOracle.answer fun _ => law) (fun s => s point ≠ none) where
  agree q s _ a s' hs' := by
    by_cases hq : q = point
    · subst hq
      have hzero (law' : F.Carrier d → PMF K) :
          RandomOracle.answer law' q s (a, s') = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr fun h =>
          hs' (by rw [show s' q = some a from (answer_support h).1]; simp)
      rw [hzero, hzero]
    · rw [F.answer_programmedLaw_of_ne d law point key q hq]
  absorb_first _ _ hs _ hr := (answer_support hr).2 _ hs
  absorb_second _ _ hs _ hr := (answer_support hr).2 _ hs

/-- The real run, with `key` stored at `point`, and the ideal run differ by at most the
probability that the ideal run evaluates the random oracle at `point`. -/
private theorem programmed_bounds (law : PMF K)
    (program : OracleComp (fun _ : F.Carrier d => K) Bool) (point : F.Carrier d) (key : K) :
    let bad := ((OracleComp.interpret (RandomOracle.answer fun _ => law) program).run
      fun _ => none).toOuterMeasure {r | r.2 point ≠ none}
    let real := ((OracleComp.interpret (RandomOracle.answer fun _ => law) program).run
      (Function.update (fun _ => none) point (some key))).map Prod.fst
    let ideal := ((OracleComp.interpret (RandomOracle.answer fun _ => law) program).run
      fun _ => none).map Prod.fst
    real true ≤ ideal true + bad ∧ ideal true ≤ real true + bad := by
  intro bad real ideal
  have hrep := OracleComp.run_interpret_map_state _ _ (F.programCache d point key)
    (F.programCache_step d law point key) program fun _ => none
  rw [show F.programCache d point key (fun _ => none) =
    Function.update (fun _ => none) point (some key) from ite_eq_left rfl] at hrep
  have hreal : real = ((OracleComp.interpret (RandomOracle.answer (F.programmedLaw d law point key))
      program).run fun _ => none).map Prod.fst := by
    simp only [real, ← hrep, PMF.map_comp]
    rfl
  have hU := F.identicalUntilBad_programmedLaw d law point key
  have h1 := hU.bind_apply_le program (fun _ => none) (PMF.pure ∘ Prod.fst) true
  have h2 := hU.symm.bind_apply_le program (fun _ => none) (PMF.pure ∘ Prod.fst) true
  rw [hU.bad_eq] at h1
  exact ⟨hreal ▸ h1, hreal ▸ h2⟩

end Programming

/-! ### The CCA experiment with a lazily sampled random oracle -/

section Lazy

/-- The KEM adversary on public key `x • g`, as a program querying only the random oracle. -/
private def roAdversary (x : ZMod (F.order d)) (challenge : F.Carrier d)
    (adversary : F.DHKEMAdversary d K) (key : K) : OracleComp (fun _ : F.Carrier d => K) Bool :=
  OracleComp.interpret (F.routeQuery d x challenge) (adversary (x • F.generator d, challenge, key))

private theorem answer_eq_interpret_routeQuery (H : F.Carrier d → K) (x : ZMod (F.order d))
    (challenge : F.Carrier d) :
    (fun q => PMF.pure (F.dhKEMAnswer d H x challenge q)) =
      fun q => OracleComp.interpret (fun z => PMF.pure (H z)) (F.routeQuery d x challenge q) := by
  funext q
  cases q with
  | hash z => simp [dhKEMAnswer, routeQuery]
  | decaps c => by_cases hc : c = challenge <;> simp [dhKEMAnswer, routeQuery, hc, dhKEMDecaps]

variable [Fintype (F.Carrier d)] [Finite K]

/-- The real CCA experiment for fixed exponents, with the random oracle sampled lazily. -/
private theorem real_eq_lazy (law : PMF K) (adversary : F.DHKEMAdversary d K)
    (x y : ZMod (F.order d)) :
    ((Probability.PMF.pi fun _ : F.Carrier d => law).bind fun H =>
      OracleComp.interpret (fun q => PMF.pure (F.dhKEMAnswer d H x (y • F.generator d) q))
        (adversary (x • F.generator d, y • F.generator d, H (y • x • F.generator d)))) =
      law.bind fun key => ((OracleComp.interpret (RandomOracle.answer fun _ => law)
        (F.roAdversary d x (y • F.generator d) adversary key)).run
          (Function.update (fun _ => none) (x • y • F.generator d) (some key))).map Prod.fst := by
  have hprog (H : F.Carrier d → K) :
      OracleComp.interpret (fun q => PMF.pure (F.dhKEMAnswer d H x (y • F.generator d) q))
        (adversary (x • F.generator d, y • F.generator d, H (y • x • F.generator d))) =
      OracleComp.interpret (fun z => PMF.pure (H z))
        (OracleComp.query (spec := fun _ : F.Carrier d => K) (x • y • F.generator d) >>=
          F.roAdversary d x (y • F.generator d) adversary) := by
    rw [OracleComp.interpret_bind, OracleComp.interpret_query, smul_comm y x,
      answer_eq_interpret_routeQuery, ← OracleComp.interpret_interpret]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
    rfl
  have hlazy := RandomOracle.interpret_eq_lazy (fun _ : F.Carrier d => law)
    (OracleComp.query (spec := fun _ : F.Carrier d => K) (x • y • F.generator d) >>=
      F.roAdversary d x (y • F.generator d) adversary)
  simp only [Probability.PMF.monad_bind_eq_bind] at hlazy
  simp only [hprog, hlazy, OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
    RandomOracle.answer_of_none _ (fun _ => none) _ rfl, Probability.PMF.monad_bind_eq_bind,
    PMF.bind_map, PMF.map_bind]
  rfl

/-- The ideal CCA experiment for fixed exponents, with the random oracle sampled lazily. -/
private theorem ideal_eq_lazy (law : PMF K) (adversary : F.DHKEMAdversary d K)
    (x y : ZMod (F.order d)) :
    ((Probability.PMF.pi fun _ : F.Carrier d => law).bind fun H => law.bind fun key =>
      OracleComp.interpret (fun q => PMF.pure (F.dhKEMAnswer d H x (y • F.generator d) q))
        (adversary (x • F.generator d, y • F.generator d, key))) =
      law.bind fun key => ((OracleComp.interpret (RandomOracle.answer fun _ => law)
        (F.roAdversary d x (y • F.generator d) adversary key)).run fun _ => none).map Prod.fst := by
  rw [PMF.bind_comm]
  refine congrArg law.bind (funext fun key => ?_)
  have hlazy := RandomOracle.interpret_eq_lazy (fun _ : F.Carrier d => law)
    (F.roAdversary d x (y • F.generator d) adversary key)
  simp only [Probability.PMF.monad_bind_eq_bind] at hlazy
  rw [← hlazy]
  refine congrArg _ (funext fun H => ?_)
  rw [answer_eq_interpret_routeQuery, ← OracleComp.interpret_interpret]
  rfl

end Lazy

/-! ### The reduction -/

section Reduction

/-- The gap-CDH experiment for fixed exponents `x` (of the second input) and `y`. -/
private def gapCDHAt (adversary : F.GapCDHAdversary d) (x y : ZMod (F.order d)) : Game :=
  (F.runDDH d x (adversary (y • F.generator d, x • F.generator d))).bind fun guess =>
    PMF.pure (decide (guess = x • y • F.generator d))

private theorem gapCDHGame_eq (adversary : F.GapCDHAdversary d) :
    F.gapCDHGame d adversary = (PMF.uniformOfFintype (ZMod (F.order d))).bind fun x =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun y => F.gapCDHAt d adversary x y := by
  simp only [gapCDHGame, gapCDHAt, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  simp only [smul_smul, mul_comm]

private theorem gapCDHAt_zero (sampleKey : ProbComp K) (adversary : F.DHKEMAdversary d K)
    (y : ZMod (F.order d)) : F.gapCDHAt d (F.dhKEMToGapCDH d sampleKey adversary) 0 y true = 1 := by
  simp [gapCDHAt, dhKEMToGapCDH]

private theorem gapCDHAt_of_ne_zero (sampleKey : ProbComp K) (adversary : F.DHKEMAdversary d K)
    (x : ZMod (F.order d)) (hx : x ≠ 0) (y : ZMod (F.order d)) :
    F.gapCDHAt d (F.dhKEMToGapCDH d sampleKey adversary) x y =
      (ProbComp.eval sampleKey).bind fun key =>
        (((OracleComp.interpret (F.lowerHandler d x (F.simHandler d sampleKey (y • F.generator d)))
          (adversary (x • F.generator d, y • F.generator d, key))).run []).bind fun r =>
            F.runDDH d x (F.extractDH d (y • F.generator d) r.2)).bind fun guess =>
              PMF.pure (decide (guess = x • y • F.generator d)) := by
  have hh : x • F.generator d ≠ 0 := fun h =>
    F.generator_ne_zero d ((F.smul_inj d x hx).mp (by rw [h, smul_zero]))
  simp only [gapCDHAt, dhKEMToGapCDH, hh, ↓reduceIte, runDDH_bind, runDDH_sample,
    F.runDDH_run_interpret, PMF.bind_bind]

/-- The probability that the lazy run evaluates the random oracle at `x • c⋆` is at most the
probability that the reduction outputs `x • c⋆`. -/
private theorem bad_le_extract (x : ZMod (F.order d)) (hx : x ≠ 0) (sampleKey : ProbComp K)
    (adversary : F.DHKEMAdversary d K) (y : ZMod (F.order d)) (key : K) :
    ((OracleComp.interpret (RandomOracle.answer fun _ => ProbComp.eval sampleKey)
        (F.roAdversary d x (y • F.generator d) adversary key)).run fun _ => none).toOuterMeasure
          {r | r.2 (x • y • F.generator d) ≠ none} ≤
      ((((OracleComp.interpret (F.lowerHandler d x (F.simHandler d sampleKey (y • F.generator d)))
        (adversary (x • F.generator d, y • F.generator d, key))).run []).bind fun r =>
          F.runDDH d x (F.extractDH d (y • F.generator d) r.2)).bind fun guess =>
            PMF.pure (decide (guess = x • y • F.generator d))) true := by
  rw [roAdversary, OracleComp.interpret_interpret, ← F.tableCache_nil d x,
    ← OracleComp.run_interpret_map_state _ _ (F.tableCache d x)
      (F.lowerHandler_step d x hx sampleKey (y • F.generator d)),
    PMF.toOuterMeasure_map_apply, PMF.bind_bind]
  refine toOuterMeasure_le_bind_apply _ _ _ _ fun ⟨a, table⟩ hmem hbad => ?_
  have hinv := OracleComp.run_interpret_invariant _ (F.NoChallengeEntry d (y • F.generator d))
    (F.lowerHandler_noChallenge d x hx sampleKey (y • F.generator d)) _ []
    (by simp [NoChallengeEntry]) a table hmem
  rw [F.runDDH_extractDH d x _ table
    (F.exists_mem_of_tableCache d x hx _ table hinv hbad), PMF.pure_bind]
  simp

end Reduction

/-! ### Theorem 12.22 -/

section Security

variable [Fintype (F.Carrier d)] [Finite K]

/-- The CCA experiment for fixed exponents `x` and `y`. -/
private def ccaAt (sampleKey : ProbComp K) (adversary : F.DHKEMAdversary d K) (bit : Bool)
    (x y : ZMod (F.order d)) : Game := do
  let H ← Probability.PMF.pi fun _ : F.Carrier d => ProbComp.eval sampleKey
  let random ← ProbComp.eval sampleKey
  let encapsulation := F.dhKEMEncaps d H (x • F.generator d) y
  OracleComp.interpret (fun q => PMF.pure (F.dhKEMAnswer d H x encapsulation.1 q))
    (adversary (x • F.generator d, encapsulation.1, if bit then encapsulation.2 else random))

private theorem ccaAt_bound (sampleKey : ProbComp K) (adversary : F.DHKEMAdversary d K)
    (x y : ZMod (F.order d)) :
    F.ccaAt d sampleKey adversary true x y true ≤ F.ccaAt d sampleKey adversary false x y true +
        F.gapCDHAt d (F.dhKEMToGapCDH d sampleKey adversary) x y true ∧
      F.ccaAt d sampleKey adversary false x y true ≤ F.ccaAt d sampleKey adversary true x y true +
        F.gapCDHAt d (F.dhKEMToGapCDH d sampleKey adversary) x y true := by
  by_cases hx : x = 0
  · rw [hx, gapCDHAt_zero]
    exact ⟨le_add_left (PMF.coe_le_one _ _), le_add_left (PMF.coe_le_one _ _)⟩
  simp only [ccaAt, dhKEMEncaps, Bool.false_eq_true, ↓reduceIte,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_const]
  rw [F.real_eq_lazy, F.ideal_eq_lazy, F.gapCDHAt_of_ne_zero d sampleKey adversary x hx y]
  refine Game.bind_apply_le_add_bind_apply _ _ _ _ true fun key => ?_
  obtain ⟨h1, h2⟩ := F.programmed_bounds d (ProbComp.eval sampleKey)
    (F.roAdversary d x (y • F.generator d) adversary key) (x • y • F.generator d) key
  have hbad := F.bad_le_extract d x hx sampleKey adversary y key
  exact ⟨h1.trans (add_le_add le_rfl hbad), h2.trans (add_le_add le_rfl hbad)⟩

/-- **[KatzLindell2020], Theorem 12.22.** The CCA advantage of every adversary against the
random-oracle Diffie–Hellman KEM (Construction 12.19) is at most the success probability of the
gap-CDH adversary `dhKEMToGapCDH` built from it. -/
theorem advantage_dhKEMCCAGame_le (sampleKey : ProbComp K) (adversary : F.DHKEMAdversary d K) :
    Game.advantage (F.dhKEMCCAGame d sampleKey adversary true)
        (F.dhKEMCCAGame d sampleKey adversary false) ≤
      Game.succProbability (F.gapCDHGame d (F.dhKEMToGapCDH d sampleKey adversary)) := by
  rw [gapCDHGame_eq]
  exact Game.advantage_bind_le_succProbability_bind _
    (fun x => (PMF.uniformOfFintype _).bind fun y => F.ccaAt d sampleKey adversary true x y)
    (fun x => (PMF.uniformOfFintype _).bind fun y => F.ccaAt d sampleKey adversary false x y)
    _ fun x => Game.bind_apply_le_add_bind_apply _ _ _ _ true fun y =>
      F.ccaAt_bound d sampleKey adversary x y

end Security

end Cslib.Crypto.PrimeOrderGroupFamily

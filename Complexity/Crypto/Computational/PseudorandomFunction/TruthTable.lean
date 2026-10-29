/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.MCSP.Basic
public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Crypto.Computational.PseudorandomFunction
public import Complexity.Foundations.Data.BitString.Enumeration
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Languages.Probabilistic.Iteration
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Circuit.Boolean.Substitution
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Languages.Probabilistic.Oracle.Support
import Complexity.Probability.Uniform

/-!
# Truth tables of word oracles

A distinguisher can read the truth table of a word oracle on few inputs: on the `2 ^ m` words of
length `n` whose first `n - m` bits are `false` (`tableQueries`), the first bits of the replies
form the truth table of a Boolean function on `m` inputs, the *restriction* of the oracle
(`restriction`, `map_tableQueries`). Asking for it is strict oracle PPT
(`isOraclePPTOn_queryTable`).

The restriction of a pseudorandom family is simple: a keyed family computable in polynomial time
has polynomial-size circuits, uniformly in the key, so its restrictions do too
(`exists_complexity_restriction_le`). The restriction of a random function is a uniformly random
Boolean function (`uniformOfFintype_map_restrictTable`). These are the two halves of the
natural-property distinguisher of Kabanets and Cai [KabanetsCai2000], in the spirit of Razborov and
Rudich [RazborovRudich1997], assembled in `Complexity.Crypto.Computational.OneWay.MCSP`; all
declarations here live in the namespace `Cslib.Crypto.KabanetsCai`.

The truth table lists the values in the order of `Cslib.BitString.equivFin`, which is the order of
the enumeration `Cslib.BitString.enumList` (`Cslib.BitString.enumList_eq_ofFn`).

## Main definitions

* `Cslib.Crypto.KabanetsCai.queryTable`: ask a word oracle on a list of words and collect the
  first reply bits.
* `Cslib.Crypto.KabanetsCai.tableQueries`: the words of length `n` with `n - m` leading `false`
  bits.
* `Cslib.Crypto.KabanetsCai.restriction`: the Boolean function a word function computes on those
  words.
* `Cslib.Crypto.KabanetsCai.restrictTable`: the restriction of a finite random-function table.

## Main results

* `Cslib.Crypto.KabanetsCai.isOraclePPTOn_queryTable`,
  `Cslib.Crypto.KabanetsCai.interpret_queryTable`: asking for a table is strict oracle PPT, and
  against a deterministic oracle returns the first reply bits.
* `Cslib.Crypto.KabanetsCai.map_tableQueries`: the first reply bits form the truth table of the
  restriction.
* `Cslib.Crypto.KabanetsCai.exists_complexity_restriction_le`: restrictions of a polynomial-time
  keyed family have polynomial circuits, uniformly in the key.
* `Cslib.Crypto.KabanetsCai.restriction_randomFunctionOracle`,
  `Cslib.Crypto.KabanetsCai.uniformOfFintype_map_restrictTable`: a random function restricts to a
  uniformly random Boolean function.

## References

* [V. Kabanets, J.-Y. Cai, *Circuit minimization problem*][KabanetsCai2000]
* [A. A. Razborov, S. Rudich, *Natural Proofs*][RazborovRudich1997]
-/

@[expose] public section

namespace Cslib.Crypto.KabanetsCai

open Probability Turing.MultiTapeTM ComputableTidilyInPolyTime Circuits Circuits.Boolean

/-! ### Asking an oracle for a truth table -/

/-- One step of `queryTable`: ask the first remaining word, and record the first bit of its
reply. -/
def queryTableStep (s : List (List Bool) × List Bool) :
    WordOracleComp Unit (List (List Bool) × List Bool) :=
  if s.1.isEmpty then pure s else
    (fun reply => (s.1.tail, s.2 ++ [reply.headD false])) <$>
      (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
        ((), s.1.headD []))

/-- Ask the oracle every word of the list, in order, and return the first bits of the replies,
`false` for an empty reply. -/
def queryTable (words : List (List Bool)) : WordOracleComp Unit (List Bool) :=
  Prod.snd <$> OracleComp.iterate words.length queryTableStep (words, [])

/-- **Asking for a table is strict oracle PPT**: each step copies one word onto the query buffer
and reads one reply bit. -/
theorem isOraclePPTOn_queryTable : IsOraclePPTOn (encList encBits) encBits queryTable := by
  unfold queryTable
  refine IsOraclePPTOn.map' (IsOraclePPTOn.iterate_of_bounded_growth'
    (stateEncoding := encPair (encList encBits) encBits) (by fun_prop) (by fun_prop) ?_
    (growth := 0) ?_) (by fun_prop)
  · unfold queryTableStep
    refine IsOraclePPTOn.cond' (by fun_prop) ComputableInPolyTime.id'.isOraclePPTOn ?_
    exact IsOraclePPTOn.map_with' (IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop))
      (by fun_prop)
  · intro state next hnext
    obtain ⟨words, acc⟩ := state
    cases words with
    | nil =>
      simp only [queryTableStep, List.isEmpty_nil, ite_true] at hnext
      rw [ProbOracleComp.eq_of_mem_support_pure hnext]
      simp
    | cons word words =>
      simp only [queryTableStep, List.isEmpty_cons, Bool.false_eq_true, ite_false] at hnext
      obtain ⟨reply, -, rfl⟩ := ProbOracleComp.mem_support_map hnext
      simp only [length_encPair, encBits_apply, List.length_append, List.length_singleton,
        List.tail_cons, length_encList, List.map_cons, List.sum_cons]
      omega

/-- Against a deterministic oracle, `queryTable` returns the first bits of the replies. -/
theorem interpret_queryTable {m : Type → Type*} [Monad m] [LawfulMonad m]
    (random : (n : ℕ) → m (Fin (n + 1))) (oracle : List Bool → List Bool)
    (words : List (List Bool)) :
    OracleComp.interpret (ProbOracleComp.handler random fun request => pure (oracle request.2))
      (queryTable words) = pure (words.map fun word => (oracle word).headD false) := by
  have key : ∀ (words : List (List Bool)) (acc : List Bool),
      OracleComp.interpret (ProbOracleComp.handler random fun request => pure (oracle request.2))
        (OracleComp.iterate words.length queryTableStep (words, acc)) =
        pure ([], acc ++ words.map fun word => (oracle word).headD false) := by
    intro words
    induction words with
    | nil => intro acc; simp
    | cons word words ih =>
      intro acc
      rw [List.length_cons, OracleComp.iterate_succ_bind, OracleComp.interpret_bind]
      have hstep : OracleComp.interpret
          (ProbOracleComp.handler random fun request => pure (oracle request.2))
          (queryTableStep (word :: words, acc)) =
            pure (words, acc ++ [(oracle word).headD false]) := by
        simp only [queryTableStep, List.isEmpty_cons, Bool.false_eq_true, ite_false,
          OracleComp.interpret_map, ProbOracleComp.interpret_query, map_pure, List.tail_cons,
          List.headD_cons]
        cases oracle word <;> rfl
      rw [hstep, pure_bind, ih]
      simp
  simp [queryTable, key]

/-! ### Restrictions of word functions -/

/-- The Boolean function on `m` inputs read from a word function on the words of length `n`
whose first `n - m` bits are `false`: the first bit of the value, `false` when it is empty. -/
def restriction (oracle : List Bool → List Bool) (n m : ℕ) : BooleanFunction m :=
  fun z => (oracle (List.replicate (n - m) false ++ List.ofFn z)).headD false

/-- The queries at arity `m`: the `2 ^ m` words of length `n` with `n - m` leading `false` bits,
in the order of `Cslib.BitString.enumList`. -/
def tableQueries (n m : ℕ) : List (List Bool) :=
  (BitString.enumList m).map (List.replicate (n - m) false ++ ·)

/-- The first bits of the answers of a word function to the queries, in order, form the truth
table of its restriction. -/
theorem map_tableQueries (oracle : List Bool → List Bool) (n m : ℕ) :
    (tableQueries n m).map (fun word => (oracle word).headD false) =
      List.ofFn (MCSP.truthTable m (restriction oracle n m)) := by
  simp only [tableQueries, BitString.enumList_eq_ofFn, List.map_ofFn, Function.comp_def]
  rfl

/-- **Restrictions of a polynomial-time keyed family have polynomial circuits.** For one constant
`c`, every key of length `n` and every `m ≤ n`, the restriction of the family with that key has a
circuit with at most `c (3 n + 2) ^ c + 2` gates: a circuit for the first output bit on inputs of
length `3 n + 1`, with the key and the leading `false` bits substituted. -/
theorem exists_complexity_restriction_le {family : List Bool → List Bool → List Bool}
    (hfamily : ComputableInPolyTime (fun pair : List Bool × List Bool =>
      family pair.1 pair.2) (encPair encBits encBits) encBits) :
    ∃ c : ℕ, ∀ (key : List Bool) (m : ℕ), m ≤ key.length →
      complexity interpretation (single (restriction (family key) key.length m)) ≤
        c * (3 * key.length + 2) ^ c + 2 := by
  have hfamily := hfamily.tidy
  obtain ⟨L, hL, hg⟩ := PPoly.exists_of_polyTime
    (.of_tidy ((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp hfamily))
  obtain ⟨c, hc⟩ := mem_PPoly_iff_exists_mem_SIZE.1 hL
  refine ⟨c, fun key m hm => ?_⟩
  set t : List (Fin m ⊕ Bool) :=
    (frame key ++ List.replicate (key.length - m) false).map Sum.inr ++ List.ofFn Sum.inl
  have hlen : t.length = 3 * key.length + 1 := by
    simp only [t, List.length_append, List.length_map, length_frame, List.length_replicate,
      List.length_ofFn]
    omega
  have hfun : restriction (family key) key.length m =
      fun z => L.slice t.length (substitute (fun j => t[j]) z) := by
    funext z
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
    have hword : List.ofFn (substitute (fun j : Fin t.length => t[j]) z) =
        frame key ++ (List.replicate (key.length - m) false ++ List.ofFn z) := by
      have : List.ofFn (substitute (fun j : Fin t.length => t[j]) z) =
          t.map (fun e => e.elim z id) :=
        List.ext_getElem (by simp) fun i _ _ => by simp [substitute]
      rw [this]
      simp [t, List.map_ofFn, Function.comp_def]
    rw [hword, restriction]
    have := hg (key, List.replicate (key.length - m) false ++ List.ofFn z)
    simpa only [Function.comp_apply, encPair_apply, encBits_apply] using this
  rw [hfun]
  refine (complexity_substitute_le _ _).trans (Nat.add_le_add_right ((hc _).trans ?_) 2)
  rw [hlen]

/-- Reading the first bit of a table at the words of length `n` with `n - m` leading `false`
bits is additive in the table. -/
def restrictTable (n m : ℕ) (hn : 0 < n) : (BitString n → BitString n) →+ BooleanFunction m where
  toFun table z :=
    table (BitString.ofList n (List.replicate (n - m) false ++ List.ofFn z)) ⟨0, hn⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The restriction of a random-function oracle is the restriction of its table. -/
theorem restriction_randomFunctionOracle {n m : ℕ} (hn : 0 < n) (hm : m ≤ n)
    (table : BitString n → BitString n) :
    restriction (randomFunctionOracle n table) n m = restrictTable n m hn table := by
  funext z
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [restriction, randomFunctionOracle, List.length_append, List.length_replicate,
    List.length_ofFn, Nat.sub_add_cancel hm, ite_true, List.ofFn_succ, List.headD_cons]
  rfl

/-- The restriction of a keyed oracle to valid queries is the restriction of the family. -/
theorem restriction_prfOracle {family : List Bool → List Bool → List Bool} {n m : ℕ}
    (hm : m ≤ n) (key : List Bool) :
    restriction (prfOracle family n key) n m = restriction (family key) n m := by
  funext z
  simp only [restriction, prfOracle, List.length_append, List.length_replicate,
    List.length_ofFn, Nat.sub_add_cancel hm, ite_true]

/-- **A random function restricts to a uniformly random function.** -/
theorem uniformOfFintype_map_restrictTable {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) :
    (PMF.uniformOfFintype (BitString n → BitString n)).map (restrictTable n m hn) =
      PMF.uniformOfFintype (BooleanFunction m) := by
  classical
  refine PMF.uniformOfFintype_map_addHom _ fun φ => ?_
  let emb : BitString m → BitString n := fun z =>
    BitString.ofList n (List.replicate (n - m) false ++ List.ofFn z)
  have hemb : Function.Injective emb := fun z z' h => by
    have := congrArg List.ofFn h
    simp only [emb] at this
    have hlen (z : BitString m) : (List.replicate (n - m) false ++ List.ofFn z).length = n := by
      simp only [List.length_append, List.length_replicate, List.length_ofFn]
      omega
    rw [BitString.ofFn_ofList (hlen z), BitString.ofFn_ofList (hlen z')] at this
    exact List.ofFn_injective (List.append_cancel_left this)
  refine ⟨fun x _ => if h : ∃ z, emb z = x then φ h.choose else false, funext fun z => ?_⟩
  have hz : ∃ z', emb z' = emb z := ⟨z, rfl⟩
  change (if h : ∃ z', emb z' = emb z then φ h.choose else false) = φ z
  simp only [hz, dite_true]
  rw [hemb hz.choose_spec]

end Cslib.Crypto.KabanetsCai

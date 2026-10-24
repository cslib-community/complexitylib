/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PCP
public import Complexity.Foundations.Data.BitString.Enumeration
public import Mathlib.Data.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.Nat.PolynomialBound.Log
import Complexity.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# Logarithmic-randomness PCP is contained in NP

Enumerating all random words gives polynomially many queries, even when their binary addresses
are large. The NP certificate records the bits at those addresses. Looking up an address's first
occurrence makes repeated queries consistent. A possibly long PCP proof is reconstructed only
in the soundness argument, never by the polynomial-time verifier.

## Main definitions

* `PCPVerifier.queryTable`: the complete list of binary proof addresses.
* `PCPVerifier.tableVerifier`: an exhaustive checker with consistent first-occurrence lookup.

## Main results

* `PCPVerifier.isPolyTime_tableVerifier`: uniform efficiency, including malformed tables.
* `PCPVerifier.tableVerifier_complete`, `PCPVerifier.tableVerifier_sound`: exact proof transfer.
* `Cslib.Complexity.PCP_log_subset_NP`: logarithmic-randomness PCP is contained in NP.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
-/

@[expose] public section

open Turing.MultiTapeTM

namespace Cslib.Complexity.PCPVerifier

variable {α : Type} (V : PCPVerifier α)

/-- All proof addresses queried on all valid random words, retaining repeated occurrences. -/
def queryTable (a : α) : List ℕ :=
  (BitString.enumList (V.coins a)).flatMap fun word => V.queries (a, word)

/-- Exhaustively check the random words using the bit at each address's first table occurrence. -/
def tableVerifier (input : α × List Bool) : Bool :=
  let addresses := V.queryTable input.1
  (BitString.enumList (V.coins input.1)).all fun word =>
    V.verdict ((input.1, word), (V.queries (input.1, word)).map fun address =>
      input.2.getD (addresses.idxOf address) false)

variable {V} {enc : α ↪ List Bool} {c : ℕ}

private theorem coins_unary (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableTidilyInPolyTime V.coins enc encUnary :=
  .binary_to_unary_bounded hV.1.tidy (by fun_prop) hcoins

private theorem enum_coins (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableTidilyInPolyTime (fun a => BitString.enumList (V.coins a))
      enc (encList encBits) := by
  apply ComputableTidilyInPolyTime.bitsEnumList (coins_unary hV hcoins)
    (size := fun n => 2 ^ (c * (Nat.log 2 n + 1)) * (2 * (c * (Nat.log 2 n + 1)) + 1))
  · have hpow := polynomiallyBounded_two_pow_mul_log c
    fun_prop
  · intro a
    have ha := hcoins a
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (hcoins a)) (by lia)

/-- The complete address table charges every enumerated word and binary address. -/
theorem isPolyTime_queryTable (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.queryTable enc (encList encNat) := by
  refine .of_tidy ?_
  have he := enum_coins hV hcoins
  have hq := hV.2.1.tidy
  unfold queryTable
  fun_prop

/-- Exhaustive verification is polynomial time for every table, including short inputs. -/
theorem isPolyTime_tableVerifier (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.tableVerifier (encPair enc encBits) encBool := by
  refine .of_tidy ?_
  have he := enum_coins hV hcoins
  have hq := hV.2.1.tidy
  have hv := hV.2.2.tidy
  have ht := (isPolyTime_queryTable hV hcoins).tidy
  unfold tableVerifier
  polytime

private theorem mem_queryTable {a : α} {word : List Bool} {address : ℕ}
    (hword : word.length = V.coins a) (haddress : address ∈ V.queries (a, word)) :
    address ∈ V.queryTable a :=
  List.mem_flatMap.mpr ⟨word, BitString.mem_enumList.mpr hword, haddress⟩

/-- A genuine proof supplies a consistent table; trailing padding is never read. -/
theorem tableVerifier_complete (a : α) (proof padding : List Bool)
    (h : ∀ word, word.length = V.coins a → V.accepts a proof word = true) :
    V.tableVerifier (a, answers proof (V.queryTable a) ++ padding) = true := by
  apply List.all_eq_true.mpr
  intro word hword
  convert h word (BitString.mem_enumList.mp hword) using 2
  unfold accepts answers
  congr 2
  apply List.map_congr_left
  intro address haddress
  have hmem := mem_queryTable (BitString.mem_enumList.mp hword) haddress
  have hindex := List.idxOf_lt_length_of_mem hmem
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append,
    List.getElem?_map, List.length_map, hindex, ↓reduceIte, List.getElem?_idxOf hmem,
    Option.map_some, Option.getD_some]

/-- Every table, including malformed or short certificates, is the restriction of a finite proof.
The expanded proof is only a mathematical witness; its length need not be polynomial. -/
theorem tableVerifier_sound (a : α) (table : List Bool)
    (h : V.tableVerifier (a, table) = true) :
    ∃ proof, ∀ word, word.length = V.coins a → V.accepts a proof word = true := by
  let addresses := V.queryTable a
  let proof := (List.range (addresses.sum + 1)).map fun address =>
    table.getD (addresses.idxOf address) false
  refine ⟨proof, fun word hword => ?_⟩
  have hw := List.all_eq_true.mp h word (BitString.mem_enumList.mpr hword)
  convert hw using 2
  unfold accepts answers
  congr 2
  apply List.map_congr_left
  intro address haddress
  have hmem := mem_queryTable hword haddress
  have hbound : address < addresses.sum + 1 := Nat.lt_succ_of_le (List.le_sum_of_mem hmem)
  simp [proof, List.getD_eq_getElem?_getD, hbound, addresses]

end Cslib.Complexity.PCPVerifier

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- Logarithmically many random bits can be checked exhaustively in NP, regardless of the query
bound. Binary proof addresses are represented by a polynomial-length table of queried bits. -/
theorem PCP_log_subset_NP (q : ℕ → ℕ) :
    PCP (fun n => Nat.log 2 n + 1) q enc ⊆ NP enc := by
  rintro A ⟨V, c, d, hV, hcoins, hqueries, hcomplete, hsound⟩
  obtain ⟨p, hlength⟩ :=
    (PCPVerifier.isPolyTime_queryTable hV hcoins).tidy.polyBounded_length.exists_polynomial
  have hbound (a : α) : (V.queryTable a).length ≤ p.eval (enc a).length := by
    exact (length_le_length_encList encNat (V.queryTable a)).trans (hlength a)
  refine ⟨p, V.tableVerifier, (PCPVerifier.isPolyTime_tableVerifier hV hcoins),
    fun a => ?_⟩
  constructor
  · intro ha
    obtain ⟨proof, hproof⟩ := hcomplete a ha
    let table := PCPVerifier.answers proof (V.queryTable a)
    refine ⟨table ++ List.replicate (p.eval (enc a).length - table.length) false, ?_, ?_⟩
    · have htable : table.length ≤ p.eval (enc a).length := by
        simpa [table, PCPVerifier.answers] using hbound a
      simp only [List.length_append, List.length_replicate]
      lia
    · exact PCPVerifier.tableVerifier_complete a proof _ hproof
  · rintro ⟨table, _, htable⟩
    by_contra ha
    obtain ⟨proof, hproof⟩ := PCPVerifier.tableVerifier_sound a table htable
    have hs := hsound a ha proof
    have hc : acceptCount (fun x => V.accepts x.1 proof x.2) a (V.coins a) =
        2 ^ V.coins a := by
      simp [acceptCount, hproof]
    rw [hc] at hs
    have hp : 0 < 2 ^ V.coins a := Nat.two_pow_pos _
    lia

end Cslib.Complexity

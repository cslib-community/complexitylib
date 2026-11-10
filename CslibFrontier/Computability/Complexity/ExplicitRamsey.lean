/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Ramsey.Nagy
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Mathlib.Data.Finset.Sort
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# A strongly explicit Ramsey graph

Erdős's lower bound `2 ^ (k / 2) < R(k, k)` (`SimpleGraph.two_rpow_half_lt_ramseyNumber`) is a
counting argument: it shows that most graphs on `2 ^ (k / 2)` vertices have neither a `k`-clique
nor a `k`-independent set, but names none of them. Constructing such graphs explicitly is a
standard benchmark for derandomization. Here a graph family on `N` vertices is *strongly explicit*
if its vertices have names of length `O(log N)` that can be recognized, and adjacency of two named
vertices can be decided, in time polynomial in the length of the names, that is, polylogarithmic in
`N`.

Nagy's graph `SimpleGraph.nagyGraph (Fin t)` is strongly explicit in this sense:

* a vertex, a `3`-subset of `Fin t`, is named by its elements in increasing order, a triple
  `(a, b, c)` of naturals with `a < b < c < t` (`Cslib.ExplicitRamsey.nagyLabel`), and every such
  triple names exactly one vertex (`Cslib.ExplicitRamsey.nagyLabel_injective`,
  `Cslib.ExplicitRamsey.range_nagyLabel`);
* the names are recognized by `Cslib.ExplicitRamsey.nagyIsLabel`, polynomial time with binary
  naturals (`Cslib.ExplicitRamsey.computableInPolyTime_nagyIsLabel`);
* two vertices are adjacent exactly when exactly one coordinate of the first name occurs in the
  second (`Cslib.ExplicitRamsey.nagyGraph_adj_iff_nagyAdj`), which is polynomial time with binary
  naturals (`Cslib.ExplicitRamsey.computableInPolyTime_nagyAdj`). One machine serves every `t`.

The graph has `C(t, 3)` vertices and neither a clique nor an independent set of size `t + 1`
(`SimpleGraph.cliqueFree_nagyGraph`, `SimpleGraph.indepSetFree_nagyGraph`), so with `k = t + 1` it
is a strongly explicit graph on `Θ(k ^ 3)` vertices with no `k`-clique and no `k`-independent set
[Nagy1972] [Jukna2011, §13.7]. Erdős's bound is exponential in `k`.

The gap is the derandomization problem. Frankl and Wilson's explicit graphs reach
`k ^ Θ(log k / log log k)` vertices [FranklWilson1981]; their bound and strongly explicit names are
in `CslibFrontier.Computability.Complexity.ExplicitRamsey.FranklWilson`. Two-source dispersers and
extractors give explicit graphs on `2 ^ ((log k) ^ c)` vertices for every constant `c` [Cohen2016]
[ChattopadhyayZuckerman2019] and on `2 ^ (k ^ c)` vertices for a constant `c > 0` [Li2023]. An
explicit graph on `2 ^ (Ω(k))` vertices, matching Erdős's bound up to the constant in the
exponent, is open. The disperser and extractor constructions are not formalized here.

## Main definitions

* `Cslib.ExplicitRamsey.nagyLabel`: the name of a vertex of `SimpleGraph.nagyGraph (Fin t)`.
* `Cslib.ExplicitRamsey.nagyIsLabel`: recognizes names.
* `Cslib.ExplicitRamsey.nagyAdj`: adjacency on names.

## Main results

* `Cslib.ExplicitRamsey.nagyLabel_injective`, `Cslib.ExplicitRamsey.range_nagyLabel`: names are a
  bijection onto the increasing triples below `t`.
* `Cslib.ExplicitRamsey.nagyGraph_adj_iff_nagyAdj`: adjacency is `nagyAdj` on names.
* `Cslib.ExplicitRamsey.computableInPolyTime_nagyAdj`,
  `Cslib.ExplicitRamsey.computableInPolyTime_nagyIsLabel`: both predicates are polynomial time.

## References

* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
* [G. Cohen, *Two-source dispersers for polylogarithmic entropy and improved Ramsey
  graphs*][Cohen2016]
* [P. Frankl, R. M. Wilson, *Intersection theorems with geometric consequences*][FranklWilson1981]
* [S. Jukna, *Extremal Combinatorics*][Jukna2011]
* [X. Li, *Two source extractors for asymptotically optimal entropy, and (many) more*][Li2023]
* [Zs. Nagy, *A constructive estimation of the Ramsey numbers*][Nagy1972]
-/

public section

open Finset SimpleGraph Turing.MultiTapeTM

namespace Cslib.ExplicitRamsey

/-- Whether `x` is one of the three coordinates of `q`. -/
@[expose] def memTriple (x : ℕ) : ℕ × ℕ × ℕ → Bool
  | (a, b, c) => x == a || x == b || x == c

/-- Whether exactly one of three Booleans is `true`. -/
@[expose] def exactlyOne (p q r : Bool) : Bool := (p ^^ q ^^ r) && !(p && q && r)

/-- Adjacency of Nagy's graph on names: exactly one coordinate of the first triple occurs in the
second. -/
@[expose] def nagyAdj : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) → Bool
  | ((a, b, c), q) => exactlyOne (memTriple a q) (memTriple b q) (memTriple c q)

/-- Whether `(a, b, c)` names a vertex of `SimpleGraph.nagyGraph (Fin t)`: `a < b < c < t`. -/
@[expose] def nagyIsLabel : ℕ × ℕ × ℕ × ℕ → Bool
  | (t, a, b, c) => decide (a < b) && decide (b < c) && decide (c < t)

/-- The name of a vertex of `SimpleGraph.nagyGraph (Fin t)`: its three elements in increasing
order. -/
def nagyLabel {t : ℕ} (s : {s : Finset (Fin t) // #s = 3}) : ℕ × ℕ × ℕ :=
  (s.1.orderEmbOfFin s.2 0, s.1.orderEmbOfFin s.2 1, s.1.orderEmbOfFin s.2 2)

/-- Distinct vertices have distinct names. -/
theorem nagyLabel_injective {t : ℕ} : Function.Injective (nagyLabel (t := t)) := by
  intro s s' h
  simp only [nagyLabel, Prod.mk.injEq, Fin.val_inj] at h
  obtain ⟨h0, h1, h2⟩ := h
  have he : ∀ i, s.1.orderEmbOfFin s.2 i = s'.1.orderEmbOfFin s'.2 i := by
    intro i; fin_cases i
    exacts [h0, h1, h2]
  apply Subtype.ext
  rw [← image_orderEmbOfFin_univ s.1 s.2, ← image_orderEmbOfFin_univ s'.1 s'.2]
  exact image_congr fun i _ => he i

/-- The names are exactly the triples accepted by `nagyIsLabel`, the increasing triples below
`t`. -/
theorem range_nagyLabel (t : ℕ) :
    Set.range (nagyLabel (t := t)) = {q | nagyIsLabel (t, q) = true} := by
  ext ⟨a, b, c⟩
  simp only [Set.mem_range, Set.mem_ofPred_eq, nagyIsLabel, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs⟩
    simp only [nagyLabel, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    have hm := (s.1.orderEmbOfFin s.2).strictMono
    exact ⟨⟨hm (by decide : (0 : Fin 3) < 1), hm (by decide : (1 : Fin 3) < 2)⟩,
      (s.1.orderEmbOfFin s.2 2).2⟩
  · rintro ⟨⟨hab, hbc⟩, hct⟩
    let f : Fin 3 → Fin t := ![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, hct⟩]
    have hf : StrictMono f := by
      refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      fin_cases i
      · exact Fin.mk_lt_mk.2 hab
      · exact Fin.mk_lt_mk.2 hbc
    have hcard : #(univ.image f) = 3 := by
      rw [card_image_of_injective _ hf.injective, card_univ, Fintype.card_fin]
    have hfs := orderEmbOfFin_unique hcard (fun i => mem_image_of_mem f (mem_univ i)) hf
    refine ⟨⟨univ.image f, hcard⟩, ?_⟩
    simp only [nagyLabel, ← hfs]
    rfl

private theorem card_inter_eq_sum {t : ℕ} (s s' : {s : Finset (Fin t) // #s = 3}) :
    #(s.1 ∩ s'.1) = ∑ i : Fin 3, if s.1.orderEmbOfFin s.2 i ∈ s'.1 then 1 else 0 := by
  rw [← filter_mem_eq_inter]
  conv_lhs => rw [← map_orderEmbOfFin_univ s.1 s.2]
  rw [filter_map, card_map, card_filter]
  rfl

private theorem mem_iff_memTriple {t : ℕ} (x : Fin t) (s : {s : Finset (Fin t) // #s = 3}) :
    x ∈ s.1 ↔ memTriple x (nagyLabel s) = true := by
  rw [← Finset.mem_coe, ← range_orderEmbOfFin s.1 s.2]
  simp only [Set.mem_range, nagyLabel, memTriple, Bool.or_eq_true, beq_iff_eq, Fin.val_inj]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro ((h | h) | h) <;> exact ⟨_, h.symm⟩

private theorem exactlyOne_eq_true_iff (p q r : Bool) :
    exactlyOne p q r = true ↔
      ((if p = true then 1 else 0) + (if q = true then 1 else 0) + (if r = true then 1 else 0) : ℕ)
        = 1 := by
  cases p <;> cases q <;> cases r <;> decide

/-- Adjacency in Nagy's graph is `nagyAdj` on names. -/
theorem nagyGraph_adj_iff_nagyAdj {t : ℕ} (s s' : {s : Finset (Fin t) // #s = 3}) :
    (nagyGraph (Fin t)).Adj s s' ↔ nagyAdj (nagyLabel s, nagyLabel s') = true := by
  rw [nagyGraph_adj, card_inter_eq_sum, Fin.sum_univ_three]
  have h0 := mem_iff_memTriple (s.1.orderEmbOfFin s.2 0) s'
  have h1 := mem_iff_memTriple (s.1.orderEmbOfFin s.2 1) s'
  have h2 := mem_iff_memTriple (s.1.orderEmbOfFin s.2 2) s'
  have he : nagyAdj (nagyLabel s, nagyLabel s') =
      exactlyOne (memTriple (s.1.orderEmbOfFin s.2 0) (nagyLabel s'))
        (memTriple (s.1.orderEmbOfFin s.2 1) (nagyLabel s'))
        (memTriple (s.1.orderEmbOfFin s.2 2) (nagyLabel s')) := rfl
  rw [he, exactlyOne_eq_true_iff]
  simp only [h0, h1, h2]

private theorem memTriple_eq (x : ℕ) (q : ℕ × ℕ × ℕ) :
    memTriple x q = (x == q.1 || x == q.2.1 || x == q.2.2) := rfl

private theorem nagyAdj_eq :
    nagyAdj = fun p => exactlyOne (memTriple p.1.1 p.2) (memTriple p.1.2.1 p.2)
      (memTriple p.1.2.2 p.2) := rfl

private theorem nagyIsLabel_eq :
    nagyIsLabel = fun q => decide (q.2.1 < q.2.2.1) && decide (q.2.2.1 < q.2.2.2) &&
      decide (q.2.2.2 < q.1) := rfl

/-- Adjacency on names is polynomial time in the binary lengths of the two names, uniformly in
`t`. -/
theorem computableInPolyTime_nagyAdj :
    ComputableInPolyTime nagyAdj (encPair (encPair encNat (encPair encNat encNat))
      (encPair encNat (encPair encNat encNat))) encBool := by
  rw [nagyAdj_eq]
  simp only [exactlyOne, memTriple_eq]
  fun_prop

/-- Names are recognized in polynomial time in the binary lengths of `t` and the name. -/
theorem computableInPolyTime_nagyIsLabel :
    ComputableInPolyTime nagyIsLabel
      (encPair encNat (encPair encNat (encPair encNat encNat))) encBool := by
  rw [nagyIsLabel_eq]
  fun_prop

end Cslib.ExplicitRamsey

end

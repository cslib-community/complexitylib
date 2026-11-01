/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dictionary.CuckooHashing.HashFamily
public import Complexity.Languages.Probabilistic.RandomOracle
public import Complexity.Probability.KWiseIndependent.DoubleTabulation
public import Complexity.Probability.PMF.Uniform
import Complexity.Foundations.Data.Nat.Power
import Complexity.Probability.KWiseIndependent.Restriction
import Complexity.Probability.PMF.UniformBound

/-!
# Pagh–Rodler Cuckoo Graph Dichotomy and Walk Tail Bounds for Highly Independent Hash Pairs

This module formalizes the cuckoo graph walk dichotomy and tail-bound analysis of Rasmus Pagh and
Flemming Friche Rodler, *"Cuckoo hashing"* (author-hosted journal manuscript dated 8 December 2003,
<https://www.rasmuspagh.net/papers/cuckoo-jour.pdf>, published in *Journal of Algorithms*
51(2):122–144, 2004) [PaghRodler2004], Section 2.3 ("Analysis", manuscript pp. 6–10; Lemma 1 on
manuscript p. 7, Eqs. (1)–(3) on manuscript p. 9, and the rehash analysis on manuscript p. 10). For
every capacity `n_max : ℕ`, it proves that any independent pair of `(2 * MaxLoop + 2)`-wise
independent hash functions into sub-tables of size `32 * max n_max 4 ≤ m` with eviction cap
`maxEvictions n_max ≤ MaxLoop ≤ m` satisfies `IsCuckooHashPair` with constants `C_walk = 2` and
`C_reh = 3`.

## Scope and relationship to `IsCuckooHashFamily`

This module establishes `IsCuckooHashPair` for uniform random hash pairs
(`isCuckooHashPair_uniform`, connected to lazy random-oracle evaluation via
`uniform_interpret_eq_lazy_hashPair`) and for explicit `(2 * MaxLoop + 2)`-wise independent
polynomial hash pairs (`isCuckooHashPair_trinomialPolyHash`). It does **not** instantiate
`IsCuckooHashFamily` for the concrete Word-RAM hash pair `evalHash1`/`evalHash2` in
`Complexity/Algorithms/WordRAM/Dictionary/CuckooHashing/HashFamily.lean` when `n_max ≥ 3`, for two
reasons:
1. The theorems here assume sub-table size `32 * max n_max 4 ≤ m`, whereas the Word-RAM dictionary
   allocates sub-tables of `tableSize n_max` slots (between `4 * n_max` and `8 * n_max`).
2. The theorems here assume `(2 * MaxLoop + 2)`-wise independence (`Θ(log n_max)`-wise), whereas
   the Word-RAM hash pair combines `7`-wise independent polynomial hashes `f_r, g_r` with random
   tabulation arrays `Z_r`.

Accordingly, the expected-time bound `cuckoo_seq_expected_amortized` for the Word-RAM cuckoo
dictionary remains conditional on `IsCuckooHashFamily` for `n_max ≥ 3`.

## Source statements, assumptions, and notation mapping

In Pagh and Rodler [PaghRodler2004] (8 December 2003 manuscript,
<https://www.rasmuspagh.net/papers/cuckoo-jour.pdf>):
* **Table size and eviction limit (Section 2, manuscript pp. 3–4; Section 2.3, manuscript p. 10)**:
  Two hash tables `T₁, T₂` each consist of `r` words holding a set `S` of `n = |S|` keys (p. 3),
  *"assuming `r ≥ (1 + ε) n` for some constant `ε > 0`"* (pp. 3–4), with
  `MaxLoop = ⌈3 log_{1+ε} r⌉` (p. 10). The Lean theorems below assume the stronger linear-space
  condition `32 * max n_max 4 ≤ m` (`S.card ≤ n_max`) and eviction cap
  `maxEvictions n_max = 6 * (Nat.clog 2 (max n_max 2) + 2) ≤ MaxLoop ≤ m`.
* **Hash-function assumption (Section 1.1, Definition 1, manuscript p. 3; Section 2.1, manuscript
  p. 5; Section 2.3, manuscript p. 7)**: Definition 1 (p. 3) defines a family `{h_i}_{i ∈ I}`,
  `h_i : U → R`, as `(c, k)`-universal if *"for any `k` distinct elements `x₁, …, x_k ∈ U`, any
  `y₁, …, y_k ∈ R`, and uniformly random `i ∈ I`,
  `Pr[h_i(x₁) = y₁, …, h_i(x_k) = y_k] ≤ c / |R|^k`"*.
  Section 2.1 (p. 5) invokes Siegel's construction for *"a hash function family that, when
  restricted to any set of `r²` keys, is `(1, n^δ)`-universal, for some constant `δ > 0`, with
  probability `1 - O(1/n²)`"*, so for `MaxLoop < n^δ` *"with high probability the family will be
  `(1, MaxLoop)`-universal. This means that `h₁` and `h₂` will act like truly random functions on
  any set of keys processed during the insertion loop"* (and Section 2.3, situation (1) on
  manuscript p. 7 separately bounds the event that *"The hash function family used is not
  `(1, MaxLoop)`-universal when restricted to the set of keys in the dictionary (including the key
  being inserted)"* by `O(1/n²)`). The Lean theorems below assume the stronger hypothesis that `h₁`
  and `h₂` are independent families each satisfying `IsKWiseIndependentHash (2 * MaxLoop + 2)` on
  the full universe `Fin U → Fin m` (exact `(1, 2 * MaxLoop + 2)`-universality with zero failure
  probability).
* **Lemma 1 (Section 2.3, manuscript p. 7)**: *"Suppose that the insertion procedure does not enter
  a closed loop. Then for any prefix `x₁, x₂, …, x_p` of the sequence of nestless keys, there must
  be a subsequence of at least `p / 3` consecutive keys without repetitions, starting with an
  occurrence of the key `x₁`, i.e., the key being inserted."* In Lean,
  `cuckooWalk_dichotomy_bicyclic` and `cuckooWalk_dichotomy` prove that any non-terminating
  `r`-round (`p = 2 * r` half-step) eviction walk from `u ∉ S` produces either a simple alternating
  path of length `ℓ = (2 * r + 2) / 3` starting at `u` (`HasAltPath`, Case B) or a bicyclic prefix
  of `L + 1` distinct keys (`2 ≤ L < 2 * r`) satisfying `L + 2` hash-collision equations
  (`HasBicyclicPrefix` and `HasExcessSubset`, Case A).
* **Closed-loop and path tail bounds, expected rounds, and rehash bounds (Section 2.3, manuscript
  pp. 7–10; Eqs. (1)–(3) on p. 9)**: For closed loops (situation (2), introduced on p. 7 and
  bounded on p. 9 following Sanders and Vöcking), the manuscript counts configurations of `v ≤ l`
  distinct nestless keys by `v³ r^{v-1} n^{v-1}` (*"`v²` possible values for `i` and `j`, `v`
  possible positions for `x_l`, `r^{v-1}` possible choices of cells, and `n^{v-1}` possible choices
  of keys other than `x₁`"*), each occurring with probability at most `r^{-2v}`, summing to
  `O(1 / n²)` (p. 9). For simple alternating paths (situation (3), introduced on pp. 7–8 and
  bounded in Eqs. (1)–(2) on p. 9), a sequence of `v = ⌈(2t - 1) / 3⌉` distinct keys (`ℓ = v - 1`
  steps) occurs with probability at most `2 * (n / r)^{v - 1}` (p. 9). Summing over rounds gives
  expected walk length `O(1)` (Eq. (3), p. 9; `expected_walk_le` with `C_walk = 2`) and bounds the
  per-insertion and full-set rehash probabilities (p. 10; `step_rehash_prob_le` with `C_reh = 3`
  and `rehash_prob_le_half`).
* **Original adaptations**:
  - `GoodForSet` (requiring `pureReplay` to succeed for *all* duplicate-free insertion orders
    `ks ⊆ S` simultaneously) and `cuckooWalkRounds` (taking the supremum of `evictRounds` over
    *all* `ValidPlacement h₁ h₂ S tbl` and slot indices) are strengthened definitions from
    `HashFamily.lean`; because neither `HasBicyclicPrefix` / `HasExcessSubset` nor `HasAltPath`
    depends on `tbl` or the insertion order `ks`, the walk dichotomy bounds both uniformly over all
    valid placements and insertion orders.
  - In place of enumerating `r^{v-1}` cell tuples as in `v³ r^{v-1} n^{v-1}` on p. 9, both Case A
    (`HasBicyclicPrefix`) and Case B (`HasAltPath`) are bounded via an original elementary fresh-key
    equation-chain seed-counting argument (`ValidEqChain`), which counts index triples `(p, s, j)`
    (`≤ (L + 1)³` for `v = L + 1`) and key tuples (`≤ S.card^L`) and uses `(2 * MaxLoop + 2)`-wise
    independence directly on `L + 2` fresh-key collision equations (probability `m^{-(L+2)}`). The
    set-level excess-`≥ 1` subgraph predicate `HasExcessSubset` and reduction
    `hasBicyclicPrefix_imp_hasExcessSubset` are likewise original adaptations.

## Main definitions

* `Cslib.Algorithms.Lean.CuckooHashing.HasAltPath`: Case B of the walk dichotomy — existence of a
  simple alternating path of length `ℓ` starting at `u` with subsequent keys in `S`.
* `Cslib.Algorithms.Lean.CuckooHashing.HasBicyclicPrefix`: Case A of the walk dichotomy — existence
  of a walk prefix of `L + 1` distinct keys (`u` and `L` keys in `S`) closing two cycles across
  `L + 2` independent hash-collision equations.
* `Cslib.Algorithms.Lean.CuckooHashing.HasExcessSubset`: set-level Case A predicate — existence of
  a subset `K ⊆ insert u S` containing `u` with `3 ≤ K.card ≤ maxCard` and
  `|(K.image h₁)| + |(K.image h₂)| + 1 ≤ K.card`.

* `Cslib.Algorithms.Lean.CuckooHashing.ProvableHashSeed`,
  `Cslib.Algorithms.Lean.CuckooHashing.provableHash1`,
  `Cslib.Algorithms.Lean.CuckooHashing.provableHash2`: regime-switched hash family parameterized by
  the polynomial universe exponent `c_exp : ℕ` (`U ≤ max n_max 4 ^ c_exp`), using
  `trinomialPolyHash` below `Cslib.Probability.doubleTabThreshold c_exp` and Thorup's
  `doubleTabHash` [Thorup2013] at or above `Cslib.Probability.doubleTabThreshold c_exp`.

## Main results

* `Cslib.Algorithms.Lean.CuckooHashing.hasAltPath_iff`,
  `Cslib.Algorithms.Lean.CuckooHashing.hasBicyclicPrefix_iff`: plain characterizations of
  `HasAltPath` and `HasBicyclicPrefix` directly in terms of injective key sequences and alternating
  / cycle-closing hash collisions, without internal equation-chain helpers.
* `Cslib.Algorithms.Lean.CuckooHashing.hasBicyclicPrefix_imp_hasExcessSubset`: any bicyclic prefix
  of length `L ∈ [2, 2 * r)` yields an excess-`≥ 1` subset `K ⊆ insert u S` of size
  `3 ≤ K.card ≤ 2 * r`.
* `Cslib.Algorithms.Lean.CuckooHashing.cuckooWalk_dichotomy_bicyclic`,
  `Cslib.Algorithms.Lean.CuckooHashing.cuckooWalk_dichotomy`,
  `Cslib.Algorithms.Lean.CuckooHashing.lt_cuckooWalkRounds_imp_dichotomy`: Pagh and Rodler
  [PaghRodler2004], Section 2.3, Lemma 1 (manuscript p. 7) — any non-terminating `r`-round cuckoo
  walk from `u ∉ S` produces either `HasAltPath` of length `(2 * r + 2) / 3` or `HasBicyclicPrefix`
  of length `2 ≤ L < 2 * r` (and `HasExcessSubset` of size `≤ 2 * r`).
* `Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_of_kWiseIndependent`: Pagh and Rodler
  [PaghRodler2004], Section 2.3 (Lemma 1, manuscript p. 7; Eq. (3), manuscript p. 9; rehash
  analysis, manuscript p. 10) — any independent pair of `(2 * MaxLoop + 2)`-wise independent
  hash families satisfies `IsCuckooHashPair` (`C_walk = 2`, `C_reh = 3`) under
  `32 * max n_max 4 ≤ m` and `maxEvictions n_max ≤ MaxLoop ≤ m`.
* `Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_of_whp_kWiseIndependent`: black-box
  conditioning bridge showing that any two-level hash family whose top-level seed yields a
  `(2 * MaxLoop + 2)`-wise independent bottom-level family with failure probability at most
  `1 / (2 * max n_max 1 * max MaxLoop 1)` satisfies `IsCuckooHashPair` (`C_walk = 3`, `C_reh = 4`).
* `Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_doubleTabHash`,
  `Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_provableFamily`: `IsCuckooHashPair` for
  Mikkel Thorup's double tabulation hash family [Thorup2013] and for the unconditional
  regime-switched family (`provableHash1`/`provableHash2`) across all `n_max : ℕ` and
  `U ≤ max n_max 4 ^ c_exp`.
* `Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_trinomialPolyHash`,
  `Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_uniform`,
  `Cslib.Algorithms.Lean.CuckooHashing.uniform_interpret_eq_lazy_hashPair`: specializations to
  explicit trinomial-field polynomial hashing and uniform random hash pairs, plus lazy random-oracle
  equivalence via `Cslib.RandomOracle.uniform_interpret_eq_lazy`.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  <https://www.rasmuspagh.net/papers/cuckoo-jour.pdf>, Section 2.3, "Analysis", pp. 6–10: Lemma 1,
  p. 7; Eqs. (1)–(3), p. 9; rehash analysis, p. 10).
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*, 2nd ed.][MitzenmacherUpfal2017]
* [M. N. Wegman and J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

public section

namespace Cslib.Algorithms.Lean.CuckooHashing

open Cslib.Probability
open Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing
open scoped BigOperators ENNReal Finset

/-! ## Section 1: Fresh-key equation chains and `k`-wise independent counting -/

/-- Conjunction of hash-collision equations `f w = f v` for each pair `(w, v)` in `eqs`. -/
private def EquationChain {U m : ℕ} (f : Fin U → Fin m) : List (Fin U × Fin U) → Prop
  | [] => True
  | (w, v) :: rest => f w = f v ∧ EquationChain f rest

private instance {U m : ℕ} (f : Fin U → Fin m) (eqs : List (Fin U × Fin U)) :
    Decidable (EquationChain f eqs) := by
  induction eqs with
  | nil => exact isTrue trivial
  | cons p rest ih =>
    rcases p with ⟨w, v⟩
    exact @instDecidableAnd _ _ (inferInstanceAs (Decidable (f w = f v))) ih

/-- Finset of all keys appearing in a list of collision equations `eqs`. -/
private def eqChainKeys {U : ℕ} : List (Fin U × Fin U) → Finset (Fin U)
  | [] => ∅
  | (w, v) :: rest => insert w (insert v (eqChainKeys rest))

/-- An equation chain is valid (`ValidEqChain`) if at each head equation `(w, v) :: rest`, the
constrained key `w` is distinct from `v` and does not appear anywhere in `rest`. -/
private def ValidEqChain {U : ℕ} : List (Fin U × Fin U) → Prop
  | [] => True
  | (w, v) :: rest => w ≠ v ∧ w ∉ eqChainKeys rest ∧ ValidEqChain rest

private instance {U : ℕ} (eqs : List (Fin U × Fin U)) : Decidable (ValidEqChain eqs) := by
  induction eqs with
  | nil => exact isTrue trivial
  | cons p rest ih =>
    rcases p with ⟨w, v⟩
    exact @instDecidableAnd _ _ (inferInstanceAs (Decidable (w ≠ v)))
      (@instDecidableAnd _ _ (inferInstanceAs (Decidable (w ∉ eqChainKeys rest))) ih)

private theorem equationChain_congr_of_eqOn {U m : ℕ} {f₁ f₂ : Fin U → Fin m}
    {eqs : List (Fin U × Fin U)} {T : Finset (Fin U)}
    (hsub : eqChainKeys eqs ⊆ T) (heq : ∀ x ∈ T, f₁ x = f₂ x) :
    EquationChain f₁ eqs ↔ EquationChain f₂ eqs := by
  induction eqs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨w, v⟩
    simp only [eqChainKeys, Finset.insert_subset_iff] at hsub
    rcases hsub with ⟨hw, hv, hrest⟩
    simp only [EquationChain, heq w hw, heq v hv, ih hrest]

/-- Extending `y : T → Fin m` to `insert w T` by assigning `w` the value `y ⟨v, hv⟩`. -/
private def extendRestrict {U m : ℕ} {T : Finset (Fin U)} (w : Fin U) {v : Fin U} (hv : v ∈ T)
    (y : T → Fin m) (x : ↥(insert w T)) : Fin m :=
  if hxw : x.1 = w then y ⟨v, hv⟩
  else y ⟨x.1, Finset.mem_of_mem_insert_of_ne x.2 hxw⟩

private theorem restrict_insert_eq_extendRestrict_iff {U m : ℕ} {T : Finset (Fin U)} {w v : Fin U}
    (hw : w ∉ T) (hv : v ∈ T) (f : Fin U → Fin m) (y : T → Fin m) :
    (insert w T).restrict f = extendRestrict w hv y ↔ f w = f v ∧ T.restrict f = y := by
  constructor
  · intro h
    have h_at_w := congrFun h ⟨w, Finset.mem_insert_self w T⟩
    simp only [Finset.restrict, extendRestrict, ↓reduceDIte] at h_at_w
    have h_on_T : T.restrict f = y := by
      funext ⟨x, hx⟩
      have hxw : x ≠ w := fun h' => hw (h' ▸ hx)
      have h_at_x := congrFun h ⟨x, Finset.mem_insert_of_mem hx⟩
      simp only [Finset.restrict, extendRestrict, hxw, ↓reduceDIte] at h_at_x
      exact h_at_x
    have h_at_v : f v = y ⟨v, hv⟩ := congrFun h_on_T ⟨v, hv⟩
    exact ⟨h_at_w.trans h_at_v.symm, h_on_T⟩
  · rintro ⟨hwv, hy⟩
    funext ⟨x, hx⟩
    simp only [Finset.restrict, extendRestrict]
    split_ifs with hxw
    · subst hxw
      have h_at_v : f v = y ⟨v, hv⟩ := congrFun hy ⟨v, hv⟩
      exact hwv.trans h_at_v
    · exact congrFun hy ⟨x, Finset.mem_of_mem_insert_of_ne hx hxw⟩

/-- For each fixed assignment `y : T → Fin m`, adding a fresh key `w ∉ T` constrained by
`h θ w = h θ v` (`v ∈ T`) divides the surviving seed count by `m`. -/
private theorem card_filter_eq_and_restrict_eq {Θ : Type*} [Fintype Θ] {U m k : ℕ} (hm : 0 < m)
    {h : Θ → Fin U → Fin m} (hh : IsKWiseIndependentHash k h)
    {T : Finset (Fin U)} {w v : Fin U} (hw : w ∉ T) (hv : v ∈ T)
    (hcard : #T + 1 ≤ k) (y : T → Fin m) :
    m * #{θ : Θ | h θ w = h θ v ∧ T.restrict (h θ) = y} =
      #{θ : Θ | T.restrict (h θ) = y} := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hcard_ins : #(insert w T) = #T + 1 := Finset.card_insert_of_notMem hw
  have h1 := hh.card_filter_restrict_eq (hcard_ins.le.trans hcard) (extendRestrict w hv y)
  have h2 := hh.card_filter_restrict_eq (by omega : #T ≤ k) y
  simp only [Fintype.card_fin] at h1 h2
  have hfilter : Finset.filter (fun θ : Θ => (insert w T).restrict (h θ) = extendRestrict w hv y)
        Finset.univ =
      Finset.filter (fun θ : Θ => h θ w = h θ v ∧ T.restrict (h θ) = y) Finset.univ := by
    ext θ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact restrict_insert_eq_extendRestrict_iff hw hv (h θ) y
  rw [hfilter, hcard_ins, pow_succ, mul_assoc] at h1
  have hm_pow_pos : 0 < m ^ #T := Nat.pow_pos hm
  exact Nat.eq_of_mul_eq_mul_left hm_pow_pos (h1.trans h2.symm)

/-- **Single-Equation Elimination Lemma**: if `w ∉ T`, `v ∈ T`, `#T + 1 ≤ k`, and `P` depends only
on `T.restrict`, then requiring `h θ w = h θ v` multiplies the surviving seed count by `1 / m`. -/
private theorem card_filter_eq_of_notMem {Θ : Type*} [Fintype Θ] {U m k : ℕ} (hm : 0 < m)
    {h : Θ → Fin U → Fin m} (hh : IsKWiseIndependentHash k h)
    {T : Finset (Fin U)} {w v : Fin U} (hw : w ∉ T) (hv : v ∈ T) (hcard : #T + 1 ≤ k)
    (P : (T → Fin m) → Prop) [DecidablePred P] :
    m * #{θ : Θ | h θ w = h θ v ∧ P (T.restrict (h θ))} =
      #{θ : Θ | P (T.restrict (h θ))} := by
  classical
  let S_y := Finset.univ.filter P
  have hdecomp₁ :
      #{θ : Θ | h θ w = h θ v ∧ P (T.restrict (h θ))} =
        ∑ y ∈ S_y, #{θ : Θ | h θ w = h θ v ∧ T.restrict (h θ) = y} := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext θ
      simp [S_y, and_comm]
    · intro y₁ _ y₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro θ h₁ h₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      exact hne (h₁.2.symm.trans h₂.2)
  have hdecomp₂ :
      #{θ : Θ | P (T.restrict (h θ))} =
        ∑ y ∈ S_y, #{θ : Θ | T.restrict (h θ) = y} := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext θ
      simp [S_y]
    · intro y₁ _ y₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro θ h₁ h₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      exact hne (h₁.symm.trans h₂)
  rw [hdecomp₁, hdecomp₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact card_filter_eq_and_restrict_eq hm hh hw hv hcard y

/-- **Exact seed count for any valid equation chain**: if `ValidEqChain eqs` holds and `eqs`
mentions at most `k` distinct keys, then `m ^ eqs.length` times the number of seeds satisfying
`EquationChain (h θ) eqs` equals `Fintype.card Θ`. -/
private theorem card_filter_equationChain_eq {Θ : Type*} [Fintype Θ] {U m k : ℕ} (hm : 0 < m)
    {h : Θ → Fin U → Fin m} (hh : IsKWiseIndependentHash k h) :
    ∀ {eqs : List (Fin U × Fin U)}, ValidEqChain eqs → #(eqChainKeys eqs) ≤ k →
      m ^ eqs.length * #{θ : Θ | EquationChain (h θ) eqs} = Fintype.card Θ
  | [], _, _ => by
    have htrue : Finset.filter (fun θ : Θ => EquationChain (h θ) []) Finset.univ = Finset.univ :=
      Finset.filter_true_of_mem fun _ _ => trivial
    rw [htrue, List.length_nil, pow_zero, one_mul, Finset.card_univ]
  | (w, v) :: rest, hvalid, hcard => by
    rcases hvalid with ⟨hwv, hwnot, hvalid_rest⟩
    let T : Finset (Fin U) := insert v (eqChainKeys rest)
    have hw_not_T : w ∉ T := by
      simp [T, hwv, hwnot]
    have hv_in_T : v ∈ T := Finset.mem_insert_self v (eqChainKeys rest)
    have hcard_eq : #(eqChainKeys ((w, v) :: rest)) = #T + 1 := by
      change #(insert w T) = #T + 1
      exact Finset.card_insert_of_notMem hw_not_T
    have hT_le : #T + 1 ≤ k := hcard_eq ▸ hcard
    have hrest_sub : eqChainKeys rest ⊆ T := Finset.subset_insert v (eqChainKeys rest)
    have hcard_rest : #(eqChainKeys rest) ≤ k :=
      (Finset.card_le_card hrest_sub).trans (by omega)
    let P : (T → Fin m) → Prop := fun y =>
      EquationChain (fun x => if hx : x ∈ T then y ⟨x, hx⟩ else ⟨0, hm⟩) rest
    have hP_iff : ∀ θ : Θ, P (T.restrict (h θ)) ↔ EquationChain (h θ) rest := by
      intro θ
      refine equationChain_congr_of_eqOn hrest_sub fun x hx => ?_
      simp [Finset.restrict, hx]
    have hstep := card_filter_eq_of_notMem hm hh hw_not_T hv_in_T hT_le P
    have hfilter₁ :
        Finset.filter (fun θ : Θ => h θ w = h θ v ∧ P (T.restrict (h θ))) Finset.univ =
          Finset.filter (fun θ : Θ => EquationChain (h θ) ((w, v) :: rest)) Finset.univ := by
      ext θ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (hP_iff θ).mp h2⟩,
        fun ⟨h1, h2⟩ => ⟨h1, (hP_iff θ).mpr h2⟩⟩
    have hfilter₂ :
        Finset.filter (fun θ : Θ => P (T.restrict (h θ))) Finset.univ =
          Finset.filter (fun θ : Θ => EquationChain (h θ) rest) Finset.univ := by
      ext θ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hP_iff θ
    rw [hfilter₁, hfilter₂] at hstep
    simp only [List.length_cons, pow_succ, mul_assoc, hstep]
    exact card_filter_equationChain_eq hm hh hvalid_rest hcard_rest

/-- Product-space seed count for independent equation chains `(eqs₁, eqs₂)` on `Θ₁ × Θ₂`. -/
private theorem card_filter_prod_equationChain_eq {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k : ℕ} (hm : 0 < m)
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hh₁ : IsKWiseIndependentHash k h₁) (hh₂ : IsKWiseIndependentHash k h₂)
    {eqs₁ eqs₂ : List (Fin U × Fin U)}
    (hv₁ : ValidEqChain eqs₁) (hv₂ : ValidEqChain eqs₂)
    (hc₁ : #(eqChainKeys eqs₁) ≤ k) (hc₂ : #(eqChainKeys eqs₂) ≤ k) :
    m ^ (eqs₁.length + eqs₂.length) *
      #{θ : Θ₁ × Θ₂ | EquationChain (h₁ θ.1) eqs₁ ∧ EquationChain (h₂ θ.2) eqs₂} =
      Fintype.card (Θ₁ × Θ₂) := by
  have hprod :
      #{θ : Θ₁ × Θ₂ | EquationChain (h₁ θ.1) eqs₁ ∧ EquationChain (h₂ θ.2) eqs₂} =
        #{θ₁ : Θ₁ | EquationChain (h₁ θ₁) eqs₁} * #{θ₂ : Θ₂ | EquationChain (h₂ θ₂) eqs₂} := by
    rw [← Finset.card_product]
    congr 1
    ext ⟨θ₁, θ₂⟩
    simp [Finset.mem_product]
  rw [pow_add, hprod, Fintype.card_prod]
  calc (m ^ eqs₁.length * m ^ eqs₂.length) *
        (#{θ₁ : Θ₁ | EquationChain (h₁ θ₁) eqs₁} * #{θ₂ : Θ₂ | EquationChain (h₂ θ₂) eqs₂})
    _ = (m ^ eqs₁.length * #{θ₁ : Θ₁ | EquationChain (h₁ θ₁) eqs₁}) *
          (m ^ eqs₂.length * #{θ₂ : Θ₂ | EquationChain (h₂ θ₂) eqs₂}) := by ring
    _ = Fintype.card Θ₁ * Fintype.card Θ₂ := by
          rw [card_filter_equationChain_eq hm hh₁ hv₁ hc₁,
            card_filter_equationChain_eq hm hh₂ hv₂ hc₂]

/-- The identity hash family `id : (X → Y) → X → Y` (representing a uniformly random function
`f : X → Y`) is `k`-wise independent for every `k : ℕ`. -/
private theorem isKWiseIndependentHash_id {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] (k : ℕ) :
    IsKWiseIndependentHash k (id : (X → Y) → X → Y) where
  dens_filter_restrict_eq {T} _ y := by
    let e : (X → Y) ≃ (T → Y) × ({x : X // x ∉ T} → Y) :=
      { toFun := fun f => (T.restrict f, fun x => f x.1)
        invFun := fun p x => if hx : x ∈ T then p.1 ⟨x, hx⟩ else p.2 ⟨x, hx⟩
        left_inv := fun f => by
          funext x
          dsimp only
          split_ifs <;> rfl
        right_inv := fun ⟨p₁, p₂⟩ => by
          ext ⟨x, hx⟩
          · simp [Finset.restrict, hx]
          · simp [hx] }
    have hcard_filter :
        #{f : X → Y | T.restrict f = y} = Fintype.card ({x : X // x ∉ T} → Y) := by
      rw [← Finset.card_univ]
      refine Finset.card_nbij' (fun f => (e f).2) (fun g => e.symm (y, g)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro g _
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact congrArg Prod.fst (e.apply_symm_apply (y, g))
      · intro f hf
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        have h1 : (e f).1 = y := hf
        calc e.symm (y, (e f).2) = e.symm ((e f).1, (e f).2) := by rw [h1]
          _ = f := e.symm_apply_apply f
      · intro g _
        exact congrArg Prod.snd (e.apply_symm_apply (y, g))
    have hcard_all :
        Fintype.card (X → Y) =
          Fintype.card Y ^ #T * Fintype.card ({x : X // x ∉ T} → Y) := by
      rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe]
    have hrest_ne : (Fintype.card ({x : X // x ∉ T} → Y) : ℚ≥0) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    dsimp only [id_eq]
    rw [Finset.dens_eq_card_div_card, hcard_filter, hcard_all, Nat.cast_mul, Nat.cast_pow,
      div_mul_cancel_right₀ hrest_ne]

/-! ## Section 1B: Index-level equation chains for alternating paths and bicyclic prefixes -/

/-- Index-level equation chain on `Fin N`: at each `(a, b) :: rest`, `a ≠ b` and `a` does not
appear anywhere in `rest`. -/
private def ValidIdxChain {N : ℕ} : List (Fin N × Fin N) → Prop
  | [] => True
  | (a, b) :: rest => a ≠ b ∧ (∀ p ∈ rest, a ≠ p.1 ∧ a ≠ p.2) ∧ ValidIdxChain rest

/-- Map an index-level equation chain on `Fin N` through `g : Fin N → Fin U`. -/
private def mapIdxChain {N U : ℕ} (g : Fin N → Fin U) (eqs : List (Fin N × Fin N)) :
    List (Fin U × Fin U) :=
  eqs.map fun p => (g p.1, g p.2)

@[simp]
private theorem length_mapIdxChain {N U : ℕ} (g : Fin N → Fin U) (eqs : List (Fin N × Fin N)) :
    (mapIdxChain g eqs).length = eqs.length :=
  List.length_map _

private theorem mem_eqChainKeys_mapIdxChain {N U : ℕ} {g : Fin N → Fin U}
    {eqs : List (Fin N × Fin N)} {x : Fin U} (hx : x ∈ eqChainKeys (mapIdxChain g eqs)) :
    ∃ a : Fin N, (∃ p ∈ eqs, a = p.1 ∨ a = p.2) ∧ g a = x := by
  induction eqs with
  | nil => simp [mapIdxChain, eqChainKeys] at hx
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    simp only [mapIdxChain, List.map_cons, eqChainKeys, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨a, ⟨(a, b), List.mem_cons_self .., Or.inl rfl⟩, rfl⟩
    · exact ⟨b, ⟨(a, b), List.mem_cons_self .., Or.inr rfl⟩, rfl⟩
    · obtain ⟨c, ⟨q, hq, hcq⟩, rfl⟩ := ih hx
      exact ⟨c, ⟨q, List.mem_cons_of_mem _ hq, hcq⟩, rfl⟩

private theorem validEqChain_mapIdxChain {N U : ℕ} {g : Fin N → Fin U} (hg : Function.Injective g)
    {eqs : List (Fin N × Fin N)} (hvalid : ValidIdxChain eqs) :
    ValidEqChain (mapIdxChain g eqs) := by
  induction eqs with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    rcases hvalid with ⟨hab, hnot, hrest⟩
    refine ⟨fun h => hab (hg h), ?_, ih hrest⟩
    intro hmem
    obtain ⟨c, ⟨q, hq, rfl | rfl⟩, hgc⟩ := mem_eqChainKeys_mapIdxChain hmem
    · exact (hnot q hq).1 (hg hgc).symm
    · exact (hnot q hq).2 (hg hgc).symm

private theorem card_eqChainKeys_mapIdxChain_le {N U : ℕ} (g : Fin N → Fin U)
    (eqs : List (Fin N × Fin N)) :
    #(eqChainKeys (mapIdxChain g eqs)) ≤ N := by
  have hsub : eqChainKeys (mapIdxChain g eqs) ⊆ Finset.univ.image g := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := mem_eqChainKeys_mapIdxChain hx
    exact Finset.mem_image_of_mem g (Finset.mem_univ a)
  calc #(eqChainKeys (mapIdxChain g eqs))
    _ ≤ #(Finset.univ.image g) := Finset.card_le_card hsub
    _ ≤ #Finset.univ := Finset.card_image_le
    _ = N := by simp

/-- Predecessor index at fresh step `i` (`0 ≤ i < L`) in a walk whose first cycle closes at `p`:
step `i = p` starts the second path from `0` (`u`), while every other step `i` continues from
`i`. -/
private def stepPred (p i : ℕ) : ℕ :=
  if i = p then 0 else i

/-- Sub-table polarity (`false` for `T₁`/`h₁`, `true` for `T₂`/`h₂`) of fresh step `i` when the
first cycle closes at `p` and the initial step uses polarity `b`. -/
private def stepTable (b : Bool) (p i : ℕ) : Bool :=
  if i < p then (i % 2 == 1) != b else ((i - p + 1) % 2 == 1) != b

/-- Build the pair of index-level equation chains `(eqs₁, eqs₂)` on `Fin (L + 1)` for the first
`m ≤ L` fresh steps. -/
private def buildFreshChains (L : ℕ) (b : Bool) (p : ℕ) :
    (m : ℕ) → m ≤ L → List (Fin (L + 1) × Fin (L + 1)) × List (Fin (L + 1) × Fin (L + 1))
  | 0, _ => ([], [])
  | i + 1, hi =>
    let prev := buildFreshChains L b p i (by omega)
    let pair : Fin (L + 1) × Fin (L + 1) :=
      (⟨i + 1, by omega⟩, ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)
    if stepTable b p i then (prev.1, pair :: prev.2) else (pair :: prev.1, prev.2)

private theorem length_buildFreshChains (L : ℕ) (b : Bool) (p : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ L),
      (buildFreshChains L b p m hm).1.length + (buildFreshChains L b p m hm).2.length = m
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := length_buildFreshChains L b p i (by omega)
    unfold buildFreshChains
    dsimp only
    split_ifs <;> simp <;> omega

private theorem mem_buildFreshChains_fst (L : ℕ) (b : Bool) (p : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ L) (q : Fin (L + 1) × Fin (L + 1)),
      q ∈ (buildFreshChains L b p m hm).1 →
      1 ≤ q.1.val ∧ q.1.val ≤ m ∧ q.2.val = stepPred p (q.1.val - 1) ∧
        stepTable b p (q.1.val - 1) = false
  | 0, _, q, hq => by simp [buildFreshChains] at hq
  | i + 1, hi, q, hq => by
    unfold buildFreshChains at hq
    dsimp only at hq
    split_ifs at hq with htab
    · obtain ⟨h1, h2, h3, h4⟩ := mem_buildFreshChains_fst L b p i (by omega) q hq
      exact ⟨h1, by omega, h3, h4⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨by dsimp; omega, by dsimp; omega, rfl, Bool.eq_false_of_ne_true htab⟩
      · obtain ⟨h1, h2, h3, h4⟩ := mem_buildFreshChains_fst L b p i (by omega) q hq
        exact ⟨h1, by omega, h3, h4⟩

private theorem mem_buildFreshChains_snd (L : ℕ) (b : Bool) (p : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ L) (q : Fin (L + 1) × Fin (L + 1)),
      q ∈ (buildFreshChains L b p m hm).2 →
      1 ≤ q.1.val ∧ q.1.val ≤ m ∧ q.2.val = stepPred p (q.1.val - 1) ∧
        stepTable b p (q.1.val - 1) = true
  | 0, _, q, hq => by simp [buildFreshChains] at hq
  | i + 1, hi, q, hq => by
    unfold buildFreshChains at hq
    dsimp only at hq
    split_ifs at hq with htab
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨by dsimp; omega, by dsimp; omega, rfl, htab⟩
      · obtain ⟨h1, h2, h3, h4⟩ := mem_buildFreshChains_snd L b p i (by omega) q hq
        exact ⟨h1, by omega, h3, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := mem_buildFreshChains_snd L b p i (by omega) q hq
      exact ⟨h1, by omega, h3, h4⟩

private theorem validIdxChain_buildFreshChains (L : ℕ) (b : Bool) (p : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ L),
      ValidIdxChain (buildFreshChains L b p m hm).1 ∧
      ValidIdxChain (buildFreshChains L b p m hm).2
  | 0, _ => ⟨trivial, trivial⟩
  | i + 1, hi => by
    obtain ⟨ih1, ih2⟩ := validIdxChain_buildFreshChains L b p i (by omega)
    unfold buildFreshChains
    dsimp only
    have hne : (⟨i + 1, by omega⟩ : Fin (L + 1)) ≠
        ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩ := by
      intro h
      have hval := congrArg Fin.val h
      dsimp only [stepPred] at hval
      split_ifs at hval; omega
    split_ifs with htab
    · refine ⟨ih1, hne, fun q hq => ?_, ih2⟩
      obtain ⟨h1, h2, h3, _⟩ := mem_buildFreshChains_snd L b p i (by omega) q hq
      have hlt2 : q.2.val ≤ i := by
        rw [h3]; dsimp only [stepPred]; split_ifs <;> omega
      exact ⟨fun h => by have := congrArg Fin.val h; dsimp at this; omega,
        fun h => by have := congrArg Fin.val h; dsimp at this; omega⟩
    · refine ⟨⟨hne, fun q hq => ?_, ih1⟩, ih2⟩
      obtain ⟨h1, h2, h3, _⟩ := mem_buildFreshChains_fst L b p i (by omega) q hq
      have hlt2 : q.2.val ≤ i := by
        rw [h3]; dsimp only [stepPred]; split_ifs <;> omega
      exact ⟨fun h => by have := congrArg Fin.val h; dsimp at this; omega,
        fun h => by have := congrArg Fin.val h; dsimp at this; omega⟩

/-- Index-level equation chains for a simple alternating path of length `ℓ` starting with
polarity `b`. -/
private def altPathChains (ℓ : ℕ) (b : Bool) :
    List (Fin (ℓ + 1) × Fin (ℓ + 1)) × List (Fin (ℓ + 1) × Fin (ℓ + 1)) :=
  buildFreshChains ℓ b (ℓ + 1) ℓ le_rfl

private theorem validIdxChain_altPathChains (ℓ : ℕ) (b : Bool) :
    ValidIdxChain (altPathChains ℓ b).1 ∧ ValidIdxChain (altPathChains ℓ b).2 :=
  validIdxChain_buildFreshChains ℓ b (ℓ + 1) ℓ le_rfl

private theorem length_altPathChains (ℓ : ℕ) (b : Bool) :
    (altPathChains ℓ b).1.length + (altPathChains ℓ b).2.length = ℓ :=
  length_buildFreshChains ℓ b (ℓ + 1) ℓ le_rfl

private theorem equationChain_buildFreshChains_iff {U m : ℕ} (h₁ h₂ : Fin U → Fin m)
    (L : ℕ) (b : Bool) (p : ℕ) (y : Fin (L + 1) → Fin U) :
    ∀ (k : ℕ) (hk : k ≤ L),
      (EquationChain h₁ (mapIdxChain y (buildFreshChains L b p k hk).1) ∧
        EquationChain h₂ (mapIdxChain y (buildFreshChains L b p k hk).2)) ↔
      ∀ i < k, ∀ (hi : i < L),
        if stepTable b p i then
          h₂ (y ⟨i + 1, by omega⟩) =
            h₂ (y ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)
        else
          h₁ (y ⟨i + 1, by omega⟩) =
            h₁ (y ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)
  | 0, _ => by
    simp [buildFreshChains, mapIdxChain, EquationChain]
  | i + 1, hi => by
    have ih := equationChain_buildFreshChains_iff h₁ h₂ L b p y i (by omega)
    constructor
    · rintro ⟨hc1, hc2⟩ j hj hjL
      unfold buildFreshChains at hc1 hc2
      dsimp only at hc1 hc2
      split_ifs at hc1 hc2 with htab
      · dsimp only [mapIdxChain, List.map, EquationChain] at hc2
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | rfl
        · exact ih.mp ⟨hc1, hc2.2⟩ j hjlt hjL
        · rw [ite_eq_left htab]
          exact hc2.1
      · dsimp only [mapIdxChain, List.map, EquationChain] at hc1
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | rfl
        · exact ih.mp ⟨hc1.2, hc2⟩ j hjlt hjL
        · rw [ite_eq_right htab]
          exact hc1.1
    · intro hsteps
      obtain ⟨ih1, ih2⟩ := ih.mpr fun j hj hjL => hsteps j (by omega) hjL
      have hcur := hsteps i (by omega) (by omega)
      unfold buildFreshChains
      dsimp only
      split_ifs with htab
      · rw [ite_eq_left htab] at hcur
        exact ⟨ih1, ⟨hcur, ih2⟩⟩
      · rw [ite_eq_right htab] at hcur
        exact ⟨⟨hcur, ih1⟩, ih2⟩

/-- **Case B (`HasAltPath`)**: there exists a simple alternating path of length `ℓ` starting at `u`
with all subsequent keys in `S`. -/
def HasAltPath {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (ℓ : ℕ) :
    Prop :=
  ∃ (b : Bool) (y : Fin (ℓ + 1) → Fin U),
    Function.Injective y ∧ y 0 = u ∧ (∀ i : Fin ℓ, y i.succ ∈ S) ∧
    EquationChain h₁ (mapIdxChain y (altPathChains ℓ b).1) ∧
    EquationChain h₂ (mapIdxChain y (altPathChains ℓ b).2)

/-- Plain characterization of `HasAltPath` without internal equation-chain helpers: `HasAltPath`
holds iff there exist an initial table polarity `b : Bool` and an injective sequence
`y : Fin (ℓ + 1) → Fin U` starting at `y 0 = u` with `y i.succ ∈ S` whose consecutive keys collide
alternately under `h₁` (`false`) and `h₂` (`true`). -/
theorem hasAltPath_iff {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (ℓ : ℕ) :
    HasAltPath h₁ h₂ S u ℓ ↔
      ∃ (b : Bool) (y : Fin (ℓ + 1) → Fin U),
        Function.Injective y ∧ y 0 = u ∧ (∀ i : Fin ℓ, y i.succ ∈ S) ∧
        ∀ i : Fin ℓ,
          if (i.val % 2 == 1) != b then h₂ (y i.succ) = h₂ (y i.castSucc)
          else h₁ (y i.succ) = h₁ (y i.castSucc) := by
  unfold HasAltPath altPathChains
  refine exists_congr fun b => exists_congr fun y => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [equationChain_buildFreshChains_iff h₁ h₂ ℓ b (ℓ + 1) y ℓ le_rfl]
  constructor
  · intro h i
    have hi := h i.val i.isLt i.isLt
    have htab : stepTable b (ℓ + 1) i.val = ((i.val % 2 == 1) != b) := by
      unfold stepTable
      exact ite_eq_left (Nat.lt_succ_of_lt i.isLt)
    have hpred :
        (⟨stepPred (ℓ + 1) i.val, by unfold stepPred; split_ifs <;> omega⟩ : Fin (ℓ + 1)) =
        i.castSucc := by
      ext
      dsimp only [stepPred, Fin.val_castSucc]
      exact ite_eq_right (Nat.ne_of_lt (Nat.lt_succ_of_lt i.isLt))
    rw [htab, hpred] at hi
    exact hi
  · intro h i hi _
    have hi' := h ⟨i, hi⟩
    have htab : stepTable b (ℓ + 1) i = ((i % 2 == 1) != b) := by
      unfold stepTable
      exact ite_eq_left (by omega)
    have hpred : (⟨stepPred (ℓ + 1) i, by unfold stepPred; split_ifs <;> omega⟩ : Fin (ℓ + 1)) =
        (⟨i, hi⟩ : Fin ℓ).castSucc := by
      ext
      dsimp only [stepPred, Fin.val_castSucc]
      exact ite_eq_right (by omega)
    rw [htab, hpred]
    exact hi'

instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (ℓ : ℕ) :
    Decidable (HasAltPath h₁ h₂ S u ℓ) :=
  decidable_of_iff' _ (hasAltPath_iff h₁ h₂ S u ℓ)

/-- Validity condition on index triple `(p, s, j)` for a bicyclic walk prefix of `L` keys in `S`. -/
private def ValidBicyclicIdx (L : ℕ) (p s j : Fin (L + 1)) : Prop :=
  2 ≤ p.val ∧ s.val < p.val ∧ s.val % 2 = p.val % 2 ∧
    (if p.val = L then 1 ≤ j.val ∧ j.val < L else j.val < L)

private instance (L : ℕ) (p s j : Fin (L + 1)) : Decidable (ValidBicyclicIdx L p s j) := by
  unfold ValidBicyclicIdx
  infer_instance

/-- Prepend a pair `q` to the first or second list according to `tab`. -/
private def prependToTable {α : Type*} (tab : Bool) (q : α) (chains : List α × List α) :
    List α × List α :=
  if tab then (chains.1, q :: chains.2) else (q :: chains.1, chains.2)

private theorem mem_prependToTable_iff {α : Type*} (tab₁ tab₂ : Bool) (x q : α)
    (chains : List α × List α) :
    q ∈ (if tab₂ then (prependToTable tab₁ x chains).2 else (prependToTable tab₁ x chains).1) ↔
      (q = x ∧ tab₁ = tab₂) ∨ q ∈ (if tab₂ then chains.2 else chains.1) := by
  unfold prependToTable
  cases tab₁ <;> cases tab₂ <;> simp

private theorem length_prependToTable {α : Type*} (tab : Bool) (q : α) (chains : List α × List α) :
    (prependToTable tab q chains).1.length + (prependToTable tab q chains).2.length =
      chains.1.length + chains.2.length + 1 := by
  unfold prependToTable
  cases tab <;> simp <;> omega

/-- Index-level equation chains for a bicyclic walk prefix of `L` keys with parameters `(p, s, j)`.
-/
private def bicyclicChains (L : ℕ) (p s j : Fin (L + 1)) :
    List (Fin (L + 1) × Fin (L + 1)) × List (Fin (L + 1) × Fin (L + 1)) :=
  let base := buildFreshChains L false p.val L le_rfl
  let c1 := prependToTable (p.val % 2 == 1) (p, s) base
  let endIdx : Fin (L + 1) := ⟨if p.val = L then 0 else L, by split_ifs <;> omega⟩
  prependToTable ((L - p.val + 1) % 2 == 1) (endIdx, j) c1

private theorem length_bicyclicChains (L : ℕ) (p s j : Fin (L + 1)) :
    (bicyclicChains L p s j).1.length + (bicyclicChains L p s j).2.length = L + 2 := by
  unfold bicyclicChains
  dsimp only
  rw [length_prependToTable, length_prependToTable, length_buildFreshChains]

private theorem validIdxChain_prependToTable {N : ℕ} (tab : Bool) (a b : Fin N)
    {chains : List (Fin N × Fin N) × List (Fin N × Fin N)}
    (hvalid : ValidIdxChain chains.1 ∧ ValidIdxChain chains.2)
    (hab : a ≠ b)
    (hnot : ∀ q ∈ (if tab then chains.2 else chains.1), a ≠ q.1 ∧ a ≠ q.2) :
    ValidIdxChain (prependToTable tab (a, b) chains).1 ∧
    ValidIdxChain (prependToTable tab (a, b) chains).2 := by
  rcases hvalid with ⟨hv1, hv2⟩
  unfold prependToTable
  cases tab
  · exact ⟨⟨hab, hnot, hv1⟩, hv2⟩
  · exact ⟨hv1, ⟨hab, hnot, hv2⟩⟩

private theorem validIdxChain_bicyclicChains {L : ℕ} {p s j : Fin (L + 1)}
    (hidx : ValidBicyclicIdx L p s j) :
    ValidIdxChain (bicyclicChains L p s j).1 ∧ ValidIdxChain (bicyclicChains L p s j).2 := by
  rcases hidx with ⟨hp2, hslt, hspar, hj⟩
  have hpL : p.val ≤ L := Nat.lt_succ_iff.mp p.isLt
  have hbase := validIdxChain_buildFreshChains L false p.val L le_rfl
  have hc1 : ValidIdxChain (prependToTable (p.val % 2 == 1) (p, s)
        (buildFreshChains L false p.val L le_rfl)).1 ∧
      ValidIdxChain (prependToTable (p.val % 2 == 1) (p, s)
        (buildFreshChains L false p.val L le_rfl)).2 := by
    refine validIdxChain_prependToTable (p.val % 2 == 1) p s hbase
      (fun h => by have := congrArg Fin.val h; omega) ?_
    intro q hq
    split_ifs at hq with htab1
    · obtain ⟨hq1, hq2, hq3, hq4⟩ := mem_buildFreshChains_snd L false p.val L le_rfl q hq
      have hp_odd : p.val % 2 = 1 := beq_iff_eq.mp htab1
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hval : p.val = q.1.val := congrArg Fin.val h
        have hlt : q.1.val - 1 < p.val := by omega
        simp only [stepTable, hlt, ↓reduceIte, Bool.bne_false, beq_iff_eq] at hq4
        omega
      · have hval : p.val = q.2.val := congrArg Fin.val h
        dsimp only [stepPred] at hq3
        split_ifs at hq3 <;> omega
    · obtain ⟨hq1, hq2, hq3, hq4⟩ := mem_buildFreshChains_fst L false p.val L le_rfl q hq
      have hp_even : p.val % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one p.val with h0 | h1
        · exact h0
        · exfalso; exact htab1 (beq_iff_eq.mpr h1)
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hval : p.val = q.1.val := congrArg Fin.val h
        have hlt : q.1.val - 1 < p.val := by omega
        simp only [stepTable, hlt, ↓reduceIte, Bool.bne_false, beq_eq_false_iff_ne] at hq4
        omega
      · have hval : p.val = q.2.val := congrArg Fin.val h
        dsimp only [stepPred] at hq3
        split_ifs at hq3 <;> omega
  let endIdx : Fin (L + 1) := ⟨if p.val = L then 0 else L, by split_ifs <;> omega⟩
  refine validIdxChain_prependToTable ((L - p.val + 1) % 2 == 1) endIdx j hc1 ?_ ?_
  · intro h
    have hval : (if p.val = L then 0 else L) = j.val := congrArg Fin.val h
    split_ifs at hval hj <;> omega
  · intro q hq
    rw [mem_prependToTable_iff] at hq
    rcases hq with ⟨rfl, htab_eq⟩ | hq_base
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have hval : (if p.val = L then 0 else L) = p.val := congrArg Fin.val h
        split_ifs at hval <;> omega
      · have hval : (if p.val = L then 0 else L) = s.val := congrArg Fin.val h
        split_ifs at hval with hp_eq
        · have htab2 : ((L - p.val + 1) % 2 == 1) = true := by
            rw [hp_eq, Nat.sub_self]; rfl
          have hp_odd : p.val % 2 = 1 := beq_iff_eq.mp (htab_eq.trans htab2)
          omega
        · omega
    · split_ifs at hq_base with htab2
      · obtain ⟨hq1, hq2, hq3, hq4⟩ := mem_buildFreshChains_snd L false p.val L le_rfl q hq_base
        have hpar2 : (L - p.val + 1) % 2 = 1 := beq_iff_eq.mp htab2
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have hval : (if p.val = L then 0 else L) = q.1.val := congrArg Fin.val h
          split_ifs at hval with hp_eq
          · omega
          · have hge : ¬ (q.1.val - 1 < p.val) := by omega
            simp only [stepTable, hge, ↓reduceIte, Bool.bne_false, beq_iff_eq] at hq4
            omega
        · have hval : (if p.val = L then 0 else L) = q.2.val := congrArg Fin.val h
          dsimp only [stepPred] at hq3
          split_ifs at hval hq3 with hp_eq hqp
          · omega
          · have hlt : q.1.val - 1 < p.val := by omega
            simp only [stepTable, hlt, ↓reduceIte, Bool.bne_false, beq_iff_eq] at hq4
            omega
          · omega
          · omega
      · obtain ⟨hq1, hq2, hq3, hq4⟩ := mem_buildFreshChains_fst L false p.val L le_rfl q hq_base
        have hpar2 : (L - p.val + 1) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (L - p.val + 1) with h0 | h1
          · exact h0
          · exfalso; exact htab2 (beq_iff_eq.mpr h1)
        have hp_ne_L : p.val ≠ L := by omega
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have hval : (if p.val = L then 0 else L) = q.1.val := congrArg Fin.val h
          rw [ite_eq_right hp_ne_L] at hval
          have hge : ¬ (q.1.val - 1 < p.val) := by omega
          simp only [stepTable, hge, ↓reduceIte, Bool.bne_false, beq_eq_false_iff_ne] at hq4
          omega
        · have hval : (if p.val = L then 0 else L) = q.2.val := congrArg Fin.val h
          dsimp only [stepPred] at hq3
          split_ifs at hval hq3 <;> omega

private theorem equationChain_prependToTable_iff {U m L : ℕ} (h₁ h₂ : Fin U → Fin m) (tab : Bool)
    (q : Fin (L + 1) × Fin (L + 1)) (y : Fin (L + 1) → Fin U)
    (chains : List (Fin (L + 1) × Fin (L + 1)) × List (Fin (L + 1) × Fin (L + 1))) :
    (EquationChain h₁ (mapIdxChain y (prependToTable tab q chains).1) ∧
      EquationChain h₂ (mapIdxChain y (prependToTable tab q chains).2)) ↔
      (if tab then h₂ (y q.1) = h₂ (y q.2) else h₁ (y q.1) = h₁ (y q.2)) ∧
        (EquationChain h₁ (mapIdxChain y chains.1) ∧
          EquationChain h₂ (mapIdxChain y chains.2)) := by
  unfold prependToTable mapIdxChain
  cases tab <;> simp [EquationChain, and_assoc, and_left_comm]

/-- **Case A (`HasBicyclicPrefix`)**: there exists a walk prefix of `L + 1` pairwise distinct keys
starting at `u` (`y 0 = u`, `y 1, ..., y L ∈ S`) that closes two distinct cycles, forming an
independent system of `L + 2` hash-collision equations across `(h₁, h₂)`. -/
def HasBicyclicPrefix {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (L : ℕ) : Prop :=
  ∃ (p s j : Fin (L + 1)) (y : Fin (L + 1) → Fin U),
    ValidBicyclicIdx L p s j ∧
    Function.Injective y ∧ y 0 = u ∧ (∀ i : Fin L, y i.succ ∈ S) ∧
    EquationChain h₁ (mapIdxChain y (bicyclicChains L p s j).1) ∧
    EquationChain h₂ (mapIdxChain y (bicyclicChains L p s j).2)

/-- Plain characterization of `HasBicyclicPrefix` without internal equation-chain helpers:
`HasBicyclicPrefix h₁ h₂ S u L` holds iff there exist cycle indices `p, s, j : Fin (L + 1)` and an
injective sequence `y : Fin (L + 1) → Fin U` (`y 0 = u`, `y i.succ ∈ S`) satisfying the two
cycle-closing collision equations together with the `L` fresh-step collision equations. -/
theorem hasBicyclicPrefix_iff {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (L : ℕ) :
    HasBicyclicPrefix h₁ h₂ S u L ↔
      ∃ (p s j : Fin (L + 1)) (y : Fin (L + 1) → Fin U),
        (2 ≤ p.val ∧ s.val < p.val ∧ s.val % 2 = p.val % 2 ∧
          (if p.val = L then 1 ≤ j.val ∧ j.val < L else j.val < L)) ∧
        Function.Injective y ∧ y 0 = u ∧ (∀ i : Fin L, y i.succ ∈ S) ∧
        (let endIdx : Fin (L + 1) := ⟨if p.val = L then 0 else L, by split_ifs <;> omega⟩
         if (L - p.val + 1) % 2 == 1 then h₂ (y endIdx) = h₂ (y j)
         else h₁ (y endIdx) = h₁ (y j)) ∧
        (if p.val % 2 == 1 then h₂ (y p) = h₂ (y s) else h₁ (y p) = h₁ (y s)) ∧
        ∀ i : Fin L,
          let pred : Fin (L + 1) := ⟨if i.val = p.val then 0 else i.val, by split_ifs <;> omega⟩
          if (if i.val < p.val then i.val % 2 == 1 else (i.val - p.val + 1) % 2 == 1) then
            h₂ (y i.succ) = h₂ (y pred)
          else
            h₁ (y i.succ) = h₁ (y pred) := by
  unfold HasBicyclicPrefix ValidBicyclicIdx bicyclicChains
  refine exists_congr fun p => exists_congr fun s => exists_congr fun j => exists_congr fun y =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  dsimp only
  rw [equationChain_prependToTable_iff, equationChain_prependToTable_iff,
    equationChain_buildFreshChains_iff h₁ h₂ L false p.val y L le_rfl]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h i
    simpa [stepTable, stepPred, Fin.succ] using h i.val i.isLt i.isLt
  · intro h i hi _
    simpa [stepTable, stepPred, Fin.succ] using h ⟨i, hi⟩

instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (L : ℕ) :
    Decidable (HasBicyclicPrefix h₁ h₂ S u L) :=
  decidable_of_iff' _ (hasBicyclicPrefix_iff h₁ h₂ S u L)

/-- **Set-level excess-`≥ 1` subgraph (`HasExcessSubset`)**: there exists a subset
`K ⊆ insert u S` containing `u` of size `3 ≤ K.card ≤ maxCard` whose images under `h₁` and `h₂`
have combined size at most `K.card - 1`. -/
@[expose]
def HasExcessSubset {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (maxCard : ℕ) : Prop :=
  ∃ K ∈ (insert u S).powerset, u ∈ K ∧ 3 ≤ K.card ∧ K.card ≤ maxCard ∧
    (K.image h₁).card + (K.image h₂).card + 1 ≤ K.card

instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (maxCard : ℕ) :
    Decidable (HasExcessSubset h₁ h₂ S u maxCard) := by
  unfold HasExcessSubset
  infer_instance

/-- Build a tuple `Fin (N + 1) → U` with head `u` and tail in `S`. -/
private def tupleFromFinset {U : Type*} (S : Finset U) (u : U) {N : ℕ} (g : Fin N → S)
    (i : Fin (N + 1)) : U :=
  Fin.cases u (fun j => (g j).val) i

private theorem exists_tupleFromFinset {U : Type*} {S : Finset U} {u : U} {N : ℕ}
    {y : Fin (N + 1) → U} (hy0 : y 0 = u) (hmem : ∀ i : Fin N, y i.succ ∈ S) :
    ∃ g : Fin N → S, tupleFromFinset S u g = y := by
  refine ⟨fun j => ⟨y j.succ, hmem j⟩, funext fun i => ?_⟩
  refine Fin.cases ?_ (fun j => rfl) i
  exact hy0.symm

/-- Seed-count bound for `HasAltPath`: for any `k`-wise independent pair `(h₁, h₂)` with
`ℓ + 1 ≤ k`, the number of seed pairs satisfying `HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ` is at most
`2 * S.card ^ ℓ * Fintype.card (Θ₁ × Θ₂) / m ^ ℓ`. -/
private theorem card_filter_hasAltPath_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k ℓ : ℕ} (hm : 0 < m)
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (S : Finset (Fin U)) (u : Fin U) (hℓk : ℓ + 1 ≤ k) :
    m ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} ≤
      2 * S.card ^ ℓ * Fintype.card (Θ₁ × Θ₂) := by
  classical
  let P (p : Bool × (Fin ℓ → S)) : Prop :=
    Function.Injective (tupleFromFinset S u p.2)
  let E (p : Bool × (Fin ℓ → S)) : Finset (Θ₁ × Θ₂) :=
    Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
      EquationChain (h₁ θ.1) (mapIdxChain (tupleFromFinset S u p.2) (altPathChains ℓ p.1).1) ∧
      EquationChain (h₂ θ.2) (mapIdxChain (tupleFromFinset S u p.2) (altPathChains ℓ p.1).2))
  have hsub : Finset.univ.filter (fun θ : Θ₁ × Θ₂ => HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ) ⊆
      (Finset.univ.filter P).biUnion E := by
    intro θ hθ
    rw [Finset.mem_filter] at hθ
    rcases hθ.2 with ⟨b, y, hinj, hy0, hmem, heq1, heq2⟩
    obtain ⟨g, rfl⟩ := exists_tupleFromFinset hy0 hmem
    rw [Finset.mem_biUnion]
    exact ⟨(b, g), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq1, heq2⟩⟩
  have hcard_le : #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} ≤
      ∑ p ∈ Finset.univ.filter P, (E p).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  calc m ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ}
      ≤ m ^ ℓ * ∑ p ∈ Finset.univ.filter P, (E p).card := Nat.mul_le_mul_left _ hcard_le
    _ = ∑ p ∈ Finset.univ.filter P, m ^ ℓ * (E p).card := by rw [Finset.mul_sum]
    _ = ∑ _p ∈ Finset.univ.filter P, Fintype.card (Θ₁ × Θ₂) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_filter] at hp
        have hvalid := validIdxChain_altPathChains ℓ p.1
        have hv1 := validEqChain_mapIdxChain hp.2 hvalid.1
        have hv2 := validEqChain_mapIdxChain hp.2 hvalid.2
        have hlen := length_altPathChains ℓ p.1
        have hprod := card_filter_prod_equationChain_eq hm hk₁ hk₂ hv1 hv2
          (le_trans (card_eqChainKeys_mapIdxChain_le _ _) hℓk)
          (le_trans (card_eqChainKeys_mapIdxChain_le _ _) hℓk)
        rw [length_mapIdxChain, length_mapIdxChain, hlen] at hprod
        exact hprod
    _ = (Finset.univ.filter P).card * Fintype.card (Θ₁ × Θ₂) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Finset.univ : Finset (Bool × (Fin ℓ → S))).card * Fintype.card (Θ₁ × Θ₂) :=
        Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ = 2 * S.card ^ ℓ * Fintype.card (Θ₁ × Θ₂) := by
        simp [Fintype.card_coe]

/-- Seed-count bound for `HasBicyclicPrefix`: for any `k`-wise independent pair `(h₁, h₂)` with
`L + 1 ≤ k`, the number of seed pairs satisfying `HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u L` is at
most `(L + 1) ^ 3 * S.card ^ L * Fintype.card (Θ₁ × Θ₂) / m ^ (L + 2)`. -/
private theorem card_filter_hasBicyclicPrefix_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k L : ℕ} (hm : 0 < m)
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (S : Finset (Fin U)) (u : Fin U) (hLk : L + 1 ≤ k) :
    m ^ (L + 2) * #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u L} ≤
      (L + 1) ^ 3 * S.card ^ L * Fintype.card (Θ₁ × Θ₂) := by
  classical
  let Idx := Fin (L + 1) × Fin (L + 1) × Fin (L + 1) × (Fin L → S)
  let P (p : Idx) : Prop :=
    ValidBicyclicIdx L p.1 p.2.1 p.2.2.1 ∧
      Function.Injective (tupleFromFinset S u p.2.2.2)
  let E (p : Idx) : Finset (Θ₁ × Θ₂) :=
    Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
      EquationChain (h₁ θ.1)
        (mapIdxChain (tupleFromFinset S u p.2.2.2) (bicyclicChains L p.1 p.2.1 p.2.2.1).1) ∧
      EquationChain (h₂ θ.2)
        (mapIdxChain (tupleFromFinset S u p.2.2.2) (bicyclicChains L p.1 p.2.1 p.2.2.1).2))
  have hsub : Finset.univ.filter (fun θ : Θ₁ × Θ₂ => HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u L) ⊆
      (Finset.univ.filter P).biUnion E := by
    intro θ hθ
    rw [Finset.mem_filter] at hθ
    rcases hθ.2 with ⟨p, s, j, y, hidx, hinj, hy0, hmem, heq1, heq2⟩
    obtain ⟨g, rfl⟩ := exists_tupleFromFinset hy0 hmem
    rw [Finset.mem_biUnion]
    exact ⟨(p, s, j, g), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hidx, hinj⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq1, heq2⟩⟩
  have hcard_le : #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u L} ≤
      ∑ p ∈ Finset.univ.filter P, (E p).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  calc m ^ (L + 2) * #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u L}
      ≤ m ^ (L + 2) * ∑ p ∈ Finset.univ.filter P, (E p).card := Nat.mul_le_mul_left _ hcard_le
    _ = ∑ p ∈ Finset.univ.filter P, m ^ (L + 2) * (E p).card := by rw [Finset.mul_sum]
    _ = ∑ _p ∈ Finset.univ.filter P, Fintype.card (Θ₁ × Θ₂) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_filter] at hp
        have hvalid := validIdxChain_bicyclicChains hp.2.1
        have hv1 := validEqChain_mapIdxChain hp.2.2 hvalid.1
        have hv2 := validEqChain_mapIdxChain hp.2.2 hvalid.2
        have hlen := length_bicyclicChains L p.1 p.2.1 p.2.2.1
        have hprod := card_filter_prod_equationChain_eq hm hk₁ hk₂ hv1 hv2
          (le_trans (card_eqChainKeys_mapIdxChain_le _ _) hLk)
          (le_trans (card_eqChainKeys_mapIdxChain_le _ _) hLk)
        rw [length_mapIdxChain, length_mapIdxChain, hlen] at hprod
        exact hprod
    _ = (Finset.univ.filter P).card * Fintype.card (Θ₁ × Θ₂) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Finset.univ : Finset Idx).card * Fintype.card (Θ₁ × Θ₂) :=
        Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ = (L + 1) ^ 3 * S.card ^ L * Fintype.card (Θ₁ × Θ₂) := by
        have hcard_idx : (Finset.univ : Finset Idx).card = (L + 1) ^ 3 * S.card ^ L := by
          simp only [Idx, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
            Fintype.card_coe]
          ring
        rw [hcard_idx]

/-! ## Section 2: Half-step trace of `pureEvict` and Pagh–Rodler Lemma 1 (`cuckooWalk_dichotomy`) -/

/-- Every valid equation chain `eqs` whose keys lie in `K` reduces the image cardinality
`(K.image h).card` by at least `eqs.length`: `(K.image h).card + eqs.length ≤ K.card`. -/
private theorem card_image_add_length_le_of_validEqChain {U m : ℕ} (h : Fin U → Fin m) :
    ∀ {eqs : List (Fin U × Fin U)} {K : Finset (Fin U)},
      ValidEqChain eqs → eqChainKeys eqs ⊆ K → EquationChain h eqs →
      (K.image h).card + eqs.length ≤ K.card
  | [], K, _, _, _ => by
    simp only [List.length_nil, add_zero]
    exact Finset.card_image_le
  | (w, v) :: rest, K, ⟨hw_ne_v, hw_not_rest, hvalid_rest⟩, hsub, ⟨hw_eq_v, heq_rest⟩ => by
    have hw_mem : w ∈ K := hsub (by simp [eqChainKeys])
    have hv_mem : v ∈ K := hsub (by simp [eqChainKeys])
    have hv_erase : v ∈ K.erase w := Finset.mem_erase.mpr ⟨hw_ne_v.symm, hv_mem⟩
    have hrest_sub : eqChainKeys rest ⊆ K.erase w := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, hsub (by simp [eqChainKeys, hx])⟩
      rintro rfl
      exact hw_not_rest hx
    have himg_eq : K.image h = (K.erase w).image h := by
      conv_lhs => rw [← Finset.insert_erase hw_mem]
      rw [Finset.image_insert, Finset.insert_eq_of_mem]
      rw [hw_eq_v]
      exact Finset.mem_image_of_mem h hv_erase
    have ih := card_image_add_length_le_of_validEqChain h hvalid_rest hrest_sub heq_rest
    have hcard_erase : (K.erase w).card + 1 = K.card := Finset.card_erase_add_one hw_mem
    rw [himg_eq, List.length_cons]
    omega

/-- Any bicyclic walk prefix of parameter `L ∈ [2, 2 * r)` yields a subset `K ⊆ insert u S`
containing `u` with `3 ≤ K.card ≤ 2 * r` and `(K.image h₁).card + (K.image h₂).card + 1 ≤ K.card`.
-/
theorem hasBicyclicPrefix_imp_hasExcessSubset {U m r L : ℕ}
    {h₁ h₂ : Fin U → Fin m} {S : Finset (Fin U)} {u : Fin U}
    (hL2 : 2 ≤ L) (hLr : L < 2 * r) (hbic : HasBicyclicPrefix h₁ h₂ S u L) :
    HasExcessSubset h₁ h₂ S u (2 * r) := by
  rcases hbic with ⟨p, s, j, y, hidx, hinj, hy0, hmem, heq1, heq2⟩
  let K : Finset (Fin U) := Finset.univ.image y
  have hK_card : K.card = L + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hK_sub : K ⊆ insert u S := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨i, _, rfl⟩
    refine Fin.cases ?_ (fun k => Finset.mem_insert_of_mem (hmem k)) i
    rw [hy0]
    exact Finset.mem_insert_self u S
  have hu_mem : u ∈ K := by
    rw [← hy0]
    exact Finset.mem_image_of_mem y (Finset.mem_univ 0)
  have hvalid := validIdxChain_bicyclicChains hidx
  have hv1 := validEqChain_mapIdxChain hinj hvalid.1
  have hv2 := validEqChain_mapIdxChain hinj hvalid.2
  have hsub1 : eqChainKeys (mapIdxChain y (bicyclicChains L p s j).1) ⊆ K := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := mem_eqChainKeys_mapIdxChain hx
    exact Finset.mem_image_of_mem y (Finset.mem_univ a)
  have hsub2 : eqChainKeys (mapIdxChain y (bicyclicChains L p s j).2) ⊆ K := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := mem_eqChainKeys_mapIdxChain hx
    exact Finset.mem_image_of_mem y (Finset.mem_univ a)
  have himg1 := card_image_add_length_le_of_validEqChain h₁ hv1 hsub1 heq1
  have himg2 := card_image_add_length_le_of_validEqChain h₂ hv2 hsub2 heq2
  have hlen := length_bicyclicChains L p s j
  rw [length_mapIdxChain] at himg1
  rw [length_mapIdxChain] at himg2
  refine ⟨K, Finset.mem_powerset.mpr hK_sub, hu_mem, by omega, by omega, by omega⟩

/-- Read a slot from the unified two-table slot space `Fin m ⊕ Fin m`. -/
private def readSlot {U m : ℕ} (tbl : PureTable U m) : Fin m ⊕ Fin m → Option (SlotEntry U)
  | Sum.inl i => tbl.t1 i
  | Sum.inr i => tbl.t2 i

/-- Target slot in `Fin m ⊕ Fin m` probed at half-step `step` for key `k`. -/
private def stepSlot {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (step : ℕ) (k : Fin U) : Fin m ⊕ Fin m :=
  if step % 2 = 0 then Sum.inl (h₁ k) else Sum.inr (h₂ k)

@[simp]
private theorem stepSlot_add_two {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (step : ℕ) (k : Fin U) :
    stepSlot h₁ h₂ (step + 2) k = stepSlot h₁ h₂ step k := by
  unfold stepSlot
  rw [Nat.add_mod_right]

private theorem stepSlot_eq_imp_mod_two_eq {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {i j : ℕ}
    {k₁ k₂ : Fin U} (heq : stepSlot h₁ h₂ i k₁ = stepSlot h₁ h₂ j k₂) :
    i % 2 = j % 2 := by
  unfold stepSlot at heq
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    simp [hi, hj] at heq ⊢

private theorem readSlot_putT1 {U m : ℕ} (h₁ : Fin U → Fin m) (tbl : PureTable U m)
    (e : SlotEntry U) :
    readSlot (putT1 h₁ tbl e).1 =
      Function.update (readSlot tbl) (Sum.inl (h₁ e.key)) (some e) := by
  funext s
  cases s with
  | inl i =>
    dsimp only [readSlot, putT1]
    by_cases h : i = h₁ e.key
    · subst h; simp
    · have hne : (Sum.inl i : Fin m ⊕ Fin m) ≠ Sum.inl (h₁ e.key) := fun hc => h (Sum.inl.inj hc)
      rw [Function.update_of_ne h, Function.update_of_ne hne]
      rfl
  | inr i =>
    dsimp only [readSlot, putT1]
    rw [Function.update_of_ne Sum.inr_ne_inl]
    rfl

private theorem readSlot_putT2 {U m : ℕ} (h₂ : Fin U → Fin m) (tbl : PureTable U m)
    (e : SlotEntry U) :
    readSlot (putT2 h₂ tbl e).1 =
      Function.update (readSlot tbl) (Sum.inr (h₂ e.key)) (some e) := by
  funext s
  cases s with
  | inl i =>
    dsimp only [readSlot, putT2]
    rw [Function.update_of_ne Sum.inl_ne_inr]
    rfl
  | inr i =>
    dsimp only [readSlot, putT2]
    by_cases h : i = h₂ e.key
    · subst h; simp
    · have hne : (Sum.inr i : Fin m ⊕ Fin m) ≠ Sum.inr (h₂ e.key) := fun hc => h (Sum.inr.inj hc)
      rw [Function.update_of_ne h, Function.update_of_ne hne]
      rfl

private theorem readSlot_some_imp_entryIn {U m : ℕ} {tbl : PureTable U m} {s : Fin m ⊕ Fin m}
    {d : SlotEntry U} (h : readSlot tbl s = some d) :
    EntryIn tbl d := by
  cases s with
  | inl i => exact Or.inl ⟨i, h⟩
  | inr i => exact Or.inr ⟨i, h⟩

/-- Half-step trace invariant for `N` consecutive cuckoo displacement half-steps. -/
private structure IsRawWalkTrace {U m : ℕ} (h₁ h₂ : Fin U → Fin m)
    (N : ℕ) (f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)) (es : ℕ → SlotEntry U) : Prop where
  step_read : ∀ i < N, f i (stepSlot h₁ h₂ i (es i).key) = some (es (i + 1))
  step_update : ∀ i < N,
    f (i + 1) = Function.update (f i) (stepSlot h₁ h₂ i (es i).key) (some (es i))
  step_home : ∀ i < N,
    stepSlot h₁ h₂ i (es (i + 1)).key = stepSlot h₁ h₂ i (es i).key
  step_not_in : ∀ i ≤ N, ∀ s d, f i s = some d → d.key ≠ (es i).key

/-- Every non-terminating `r`-round execution `pureEvict h₁ h₂ r tbl₀ e₀ = none` from a well-placed
table `tbl₀` with `¬ HasKey tbl₀ e₀.key` unrolls into a `2 * r`-half-step raw walk trace. -/
private theorem exists_rawWalkTrace_of_pureEvict_eq_none {U m : ℕ} {h₁ h₂ : Fin U → Fin m} :
    ∀ (r : ℕ) {tbl₀ : PureTable U m} {e₀ : SlotEntry U},
      WellPlaced h₁ h₂ tbl₀ → ¬ HasKey tbl₀ e₀.key →
      pureEvict h₁ h₂ r tbl₀ e₀ = none →
      ∃ (f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)) (es : ℕ → SlotEntry U),
        f 0 = readSlot tbl₀ ∧ es 0 = e₀ ∧ IsRawWalkTrace h₁ h₂ (2 * r) f es
  | 0, tbl₀, e₀, _, hno₀, _ => by
    refine ⟨fun _ => readSlot tbl₀, fun _ => e₀, rfl, rfl, ?_⟩
    refine ⟨by intro i hi; omega, by intro i hi; omega, by intro i hi; omega, ?_⟩
    intro i hi s d hread heq
    exact hno₀ ⟨d, readSlot_some_imp_entryIn hread, heq⟩
  | r + 1, tbl₀, e₀, hwp₀, hno₀, hev => by
    unfold pureEvict pureEvictRound at hev
    have hwp₁ : WellPlaced h₁ h₂ (putT1 h₁ tbl₀ e₀).1 := putT1_wellPlaced hwp₀ hno₀
    cases hold₁ : (putT1 h₁ tbl₀ e₀).2 with
    | none => rw [hold₁] at hev; cases hev
    | some e₁ =>
      rw [hold₁] at hev
      dsimp only at hev
      obtain ⟨hno₁, _⟩ := putT1_some_spec hwp₀ hno₀ hold₁
      have hwp₂ : WellPlaced h₁ h₂ (putT2 h₂ (putT1 h₁ tbl₀ e₀).1 e₁).1 :=
        putT2_wellPlaced hwp₁ hno₁
      cases hold₂ : (putT2 h₂ (putT1 h₁ tbl₀ e₀).1 e₁).2 with
      | none =>
        have hpair : putT2 h₂ (putT1 h₁ tbl₀ e₀).1 e₁ =
            ((putT2 h₂ (putT1 h₁ tbl₀ e₀).1 e₁).1, none) := Prod.ext rfl hold₂
        rw [hpair] at hev; cases hev
      | some e₂ =>
        have hpair : putT2 h₂ (putT1 h₁ tbl₀ e₀).1 e₁ =
            ((putT2 h₂ (putT1 h₁ tbl₀ e₀).1 e₁).1, some e₂) := Prod.ext rfl hold₂
        rw [hpair] at hev
        obtain ⟨hno₂, _⟩ := putT2_some_spec hwp₁ hno₁ hold₂
        obtain ⟨f', es', hf'0, hes'0, hraw'⟩ :=
          exists_rawWalkTrace_of_pureEvict_eq_none r hwp₂ hno₂ hev
        let tbl₁ := (putT1 h₁ tbl₀ e₀).1
        let tbl₂ := (putT2 h₂ tbl₁ e₁).1
        let f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)
          | 0 => readSlot tbl₀
          | 1 => readSlot tbl₁
          | k + 2 => f' k
        let es : ℕ → SlotEntry U
          | 0 => e₀
          | 1 => e₁
          | k + 2 => es' k
        refine ⟨f, es, rfl, rfl, ?_⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i hi
          rcases i with _ | _ | k
          · dsimp only [f, es, stepSlot]; exact hold₁
          · dsimp only [f, es, stepSlot]; rw [hes'0]; exact hold₂
          · dsimp only [f, es]
            rw [stepSlot_add_two]
            exact hraw'.step_read k (by omega)
        · intro i hi
          rcases i with _ | _ | k
          · dsimp only [f, es, stepSlot, tbl₁]
            exact readSlot_putT1 h₁ tbl₀ e₀
          · dsimp only [f, es, stepSlot, tbl₂]
            rw [hf'0]
            exact readSlot_putT2 h₂ tbl₁ e₁
          · dsimp only [f, es]
            rw [stepSlot_add_two]
            exact hraw'.step_update k (by omega)
        · intro i hi
          rcases i with _ | _ | k
          · dsimp only [es, stepSlot]
            exact congrArg Sum.inl (hwp₀.t1_home (h₁ e₀.key) e₁ hold₁)
          · dsimp only [es, stepSlot]
            rw [hes'0]
            exact congrArg Sum.inr (hwp₁.t2_home (h₂ e₁.key) e₂ hold₂)
          · dsimp only [es]
            rw [stepSlot_add_two, stepSlot_add_two]
            exact hraw'.step_home k (by omega)
        · intro i hi s d hread heq
          rcases i with _ | _ | k
          · exact hno₀ ⟨d, readSlot_some_imp_entryIn hread, heq⟩
          · exact hno₁ ⟨d, readSlot_some_imp_entryIn hread, heq⟩
          · exact hraw'.step_not_in k (by omega) s d hread heq

/-- If slot `s` is not probed at any step `k` in `[j, i)`, then `f i s = f j s`. -/
private theorem IsRawWalkTrace.f_eq_of_forall_ne {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {j : ℕ} {s : Fin m ⊕ Fin m} :
    ∀ {i : ℕ}, j ≤ i → i ≤ N →
      (∀ k, j ≤ k → k < i → stepSlot h₁ h₂ k (es k).key ≠ s) →
      f i s = f j s
  | 0, hj0, _, _ => by
    have : j = 0 := by omega
    subst this; rfl
  | i + 1, hji, hiN, hne => by
    rcases eq_or_lt_of_le hji with rfl | hjlt
    · rfl
    · have h1 : f (i + 1) s = f i s := by
        rw [htr.step_update i (by omega)]
        exact Function.update_of_ne (Ne.symm (hne i (by omega) (by omega))) _ _
      rw [h1]
      exact htr.f_eq_of_forall_ne (by omega) (by omega) fun k hjk hki => hne k hjk (by omega)

/-- **Fresh-Slot Law**: if step `i < N` probes a slot never probed before step `i`, then the
displaced entry `es (i + 1)` was already sitting in that slot at step `0`, and its key is distinct
from `(es k).key` for every `k ≤ i`. -/
private theorem IsRawWalkTrace.fresh_slot_spec {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {i : ℕ} (hi : i < N)
    (hfresh : ∀ m < i, stepSlot h₁ h₂ m (es m).key ≠ stepSlot h₁ h₂ i (es i).key) :
    f 0 (stepSlot h₁ h₂ i (es i).key) = some (es (i + 1)) ∧
      ∀ k ≤ i, (es (i + 1)).key ≠ (es k).key := by
  refine ⟨?_, fun k hki => ?_⟩
  · have h0 := htr.f_eq_of_forall_ne (Nat.zero_le i) (by omega) fun m _ hmi => hfresh m hmi
    rw [← h0]
    exact htr.step_read i hi
  · have hk := htr.f_eq_of_forall_ne hki (by omega) fun m _ hmi => hfresh m hmi
    have hread : f k (stepSlot h₁ h₂ i (es i).key) = some (es (i + 1)) := by
      rw [← hk]
      exact htr.step_read i hi
    exact htr.step_not_in k (by omega) _ _ hread

/-- **Revisit Law**: if `k < i < N` is the most recent step before `i` that probed the slot of step
`i`, then step `i` evicts `es k` (`es (i + 1) = es k`). -/
private theorem IsRawWalkTrace.revisit_slot_spec {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {k i : ℕ} (hki : k < i) (hi : i < N)
    (heq : stepSlot h₁ h₂ k (es k).key = stepSlot h₁ h₂ i (es i).key)
    (hlast : ∀ m, k < m → m < i → stepSlot h₁ h₂ m (es m).key ≠ stepSlot h₁ h₂ i (es i).key) :
    es (i + 1) = es k := by
  have h1 := htr.f_eq_of_forall_ne (Nat.succ_le_of_lt hki) (by omega) fun m hkm hmi =>
    hlast m hkm hmi
  have h2 : f (k + 1) (stepSlot h₁ h₂ i (es i).key) = some (es k) := by
    rw [htr.step_update k (by omega), ← heq, Function.update_self]
  have h3 : f i (stepSlot h₁ h₂ i (es i).key) = some (es (i + 1)) := htr.step_read i hi
  exact Option.some.inj (h3.symm.trans (h1.trans h2))

/-- **Backtracking at the first revisit**: if `t₁ < N` is the first step that revisits an earlier
slot (`stepSlot h₁ h₂ s (es s).key = stepSlot h₁ h₂ t₁ (es t₁).key` with `s < t₁`, and all steps
`< t₁` are fresh), then for every `0 ≤ d ≤ s` with `t₁ + d < N`, step `t₁ + d` probes
`stepSlot h₁ h₂ (s - d) (es (s - d)).key` and evicts key `(es (s - d)).key`. -/
private theorem IsRawWalkTrace.backtrack_at_first_revisit {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {s t₁ : ℕ} (hst : s < t₁)
    (hfresh_lt : ∀ i < t₁, ∀ k < i, stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ i (es i).key)
    (hrev : stepSlot h₁ h₂ s (es s).key = stepSlot h₁ h₂ t₁ (es t₁).key) :
    ∀ (d : ℕ), d ≤ s → t₁ + d < N →
      stepSlot h₁ h₂ (t₁ + d) (es (t₁ + d)).key = stepSlot h₁ h₂ (s - d) (es (s - d)).key ∧
        (es (t₁ + d + 1)).key = (es (s - d)).key
  | 0, _, htN => by
    simp only [Nat.add_zero, Nat.sub_zero]
    refine ⟨hrev.symm, ?_⟩
    have he := htr.revisit_slot_spec hst htN hrev fun m hsm hmt heqm =>
      hfresh_lt m hmt s hsm (hrev.trans heqm.symm)
    exact congrArg SlotEntry.key he
  | d + 1, hds, htN => by
    obtain ⟨hb_ih, hx_ih⟩ :=
      htr.backtrack_at_first_revisit hst hfresh_lt hrev d (by omega) (by omega)
    have hpar_st : s % 2 = t₁ % 2 := stepSlot_eq_imp_mod_two_eq hrev
    have hpar_step : (t₁ + (d + 1)) % 2 = (s - (d + 1)) % 2 := by omega
    have hhome_prev :
        stepSlot h₁ h₂ (s - (d + 1)) (es (s - d)).key =
          stepSlot h₁ h₂ (s - (d + 1)) (es (s - (d + 1))).key := by
      have h1 := htr.step_home (s - (d + 1)) (by omega)
      have hidx : s - (d + 1) + 1 = s - d := by omega
      rw [hidx] at h1
      exact h1
    have hb_cur :
        stepSlot h₁ h₂ (t₁ + (d + 1)) (es (t₁ + (d + 1))).key =
          stepSlot h₁ h₂ (s - (d + 1)) (es (s - (d + 1))).key := by
      have h1 : stepSlot h₁ h₂ (t₁ + (d + 1)) (es (t₁ + (d + 1))).key =
          stepSlot h₁ h₂ (s - (d + 1)) (es (s - d)).key := by
        have hidx : es (t₁ + (d + 1)) = es (t₁ + d + 1) := congrArg es (by omega)
        unfold stepSlot
        rw [hpar_step, hidx, hx_ih]
      rw [h1, hhome_prev]
    refine ⟨hb_cur, ?_⟩
    have he := htr.revisit_slot_spec (show s - (d + 1) < t₁ + (d + 1) by omega) htN hb_cur.symm ?_
    · exact congrArg SlotEntry.key he
    · intro m hsm hmt heqm
      have heqm' : stepSlot h₁ h₂ m (es m).key =
          stepSlot h₁ h₂ (s - (d + 1)) (es (s - (d + 1))).key := heqm.trans hb_cur
      by_cases hmt₁ : m < t₁
      · exact hfresh_lt m hmt₁ (s - (d + 1)) hsm heqm'.symm
      · obtain ⟨hb_m, _⟩ :=
          htr.backtrack_at_first_revisit hst hfresh_lt hrev (m - t₁) (by omega) (by omega)
        have hm_eq : t₁ + (m - t₁) = m := by omega
        rw [hm_eq] at hb_m
        have hlt_s : s - (d + 1) < s - (m - t₁) := by omega
        exact hfresh_lt (s - (m - t₁)) (by omega) (s - (d + 1)) hlt_s (heqm'.symm.trans hb_m)

private theorem stepSlot_eq_iff {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (i : ℕ) (k₁ k₂ : Fin U) :
    stepSlot h₁ h₂ i k₁ = stepSlot h₁ h₂ i k₂ ↔
      if (i % 2 == 1) then h₂ k₁ = h₂ k₂ else h₁ k₁ = h₁ k₂ := by
  unfold stepSlot
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;> simp [hi]

private theorem equationChain_prependToTable {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (tab : Bool)
    (q : Fin U × Fin U) (chains : List (Fin U × Fin U) × List (Fin U × Fin U))
    (hq : if tab then h₂ q.1 = h₂ q.2 else h₁ q.1 = h₁ q.2)
    (hc : EquationChain h₁ chains.1 ∧ EquationChain h₂ chains.2) :
    EquationChain h₁ (prependToTable tab q chains).1 ∧
      EquationChain h₂ (prependToTable tab q chains).2 := by
  unfold prependToTable
  cases tab
  · exact ⟨⟨hq, hc.1⟩, hc.2⟩
  · exact ⟨hc.1, ⟨hq, hc.2⟩⟩

private theorem mapIdxChain_prependToTable {N U : ℕ} (y : Fin N → Fin U) (tab : Bool)
    (q : Fin N × Fin N) (chains : List (Fin N × Fin N) × List (Fin N × Fin N)) :
    (mapIdxChain y (prependToTable tab q chains).1,
      mapIdxChain y (prependToTable tab q chains).2) =
      prependToTable tab (y q.1, y q.2) (mapIdxChain y chains.1, mapIdxChain y chains.2) := by
  unfold prependToTable mapIdxChain
  cases tab <;> rfl

/-- If `y : Fin (L + 1) → Fin U` satisfies the step collision equation at each `i < m` (with
`m ≤ L`), then `y` satisfies both equation chains produced by `buildFreshChains L b p m hm`. -/
private theorem equationChain_buildFreshChains_of_steps {U m : ℕ} (h₁ h₂ : Fin U → Fin m)
    (L : ℕ) (b : Bool) (p : ℕ) (y : Fin (L + 1) → Fin U) :
    ∀ (k : ℕ) (hk : k ≤ L),
      (∀ i < k, ∀ (hi : i < L),
        if stepTable b p i then
          h₂ (y ⟨i + 1, by omega⟩) =
            h₂ (y ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)
        else
          h₁ (y ⟨i + 1, by omega⟩) =
            h₁ (y ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)) →
      EquationChain h₁ (mapIdxChain y (buildFreshChains L b p k hk).1) ∧
        EquationChain h₂ (mapIdxChain y (buildFreshChains L b p k hk).2)
  | 0, _, _ => ⟨trivial, trivial⟩
  | i + 1, hi, hsteps => by
    obtain ⟨ih1, ih2⟩ :=
      equationChain_buildFreshChains_of_steps h₁ h₂ L b p y i (by omega)
        fun j hj hjL => hsteps j (by omega) hjL
    have hcur := hsteps i (by omega) (by omega)
    unfold buildFreshChains
    dsimp only
    split_ifs with htab
    · rw [ite_eq_left htab] at hcur
      exact ⟨ih1, ⟨hcur, ih2⟩⟩
    · rw [ite_eq_right htab] at hcur
      exact ⟨⟨hcur, ih1⟩, ih2⟩

/-- Any contiguous segment `[start, start + ℓ)` of fresh half-steps starting at `(es start).key = u`
produces a simple alternating path of length `ℓ` starting at `u` (`HasAltPath h₁ h₂ S u ℓ`). -/
private theorem IsRawWalkTrace.hasAltPath_of_fresh_segment {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es)
    (hinit : ∀ s d, f 0 s = some d → d.key ∈ S)
    {start ℓ : ℕ} (hbound : start + ℓ ≤ N) (hstart : (es start).key = u)
    (hfresh : ∀ d < ℓ, ∀ k < start + d,
      stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ (start + d) (es (start + d)).key) :
    HasAltPath h₁ h₂ S u ℓ := by
  let b : Bool := (start % 2 == 1)
  let y : Fin (ℓ + 1) → Fin U := fun i => (es (start + i.val)).key
  have hchains :
      EquationChain h₁ (mapIdxChain y (altPathChains ℓ b).1) ∧
        EquationChain h₂ (mapIdxChain y (altPathChains ℓ b).2) := by
    unfold altPathChains
    refine equationChain_buildFreshChains_of_steps h₁ h₂ ℓ b (ℓ + 1) y ℓ le_rfl ?_
    intro d hd _
    have hhome := htr.step_home (start + d) (by omega)
    rw [stepSlot_eq_iff] at hhome
    have htab_eq : stepTable b (ℓ + 1) d = ((start + d) % 2 == 1) := by
      have hd_lt : d < ℓ + 1 := by omega
      simp only [stepTable, hd_lt, ↓reduceIte, b]
      have hsum : (start + d) % 2 = (start % 2 + d % 2) % 2 := Nat.add_mod start d 2
      rcases Nat.mod_two_eq_zero_or_one start with hs | hs <;>
        rcases Nat.mod_two_eq_zero_or_one d with hd' | hd' <;>
        simp [hs, hd'] at hsum ⊢ <;>
        simp [hsum]
    have hpred_eq : stepPred (ℓ + 1) d = d := by
      unfold stepPred
      rw [ite_eq_right (by omega)]
    dsimp only [y]
    have hidx1 : start + (d + 1) = start + d + 1 := by omega
    have hidx2 : start + stepPred (ℓ + 1) d = start + d := by rw [hpred_eq]
    rw [htab_eq, hidx1, hidx2]
    exact hhome
  refine ⟨b, y, ?_, ?_, ?_, hchains.1, hchains.2⟩
  · intro i₁ i₂ heq
    rcases lt_trichotomy i₁.val i₂.val with hlt | heq_val | hgt
    · exfalso
      have hd : i₂.val - 1 < ℓ := by omega
      have hspec := (htr.fresh_slot_spec (by omega) (hfresh (i₂.val - 1) hd)).2
        (start + i₁.val) (by omega)
      have hidx : start + (i₂.val - 1) + 1 = start + i₂.val := by omega
      rw [hidx] at hspec
      exact hspec heq.symm
    · exact Fin.ext heq_val
    · exfalso
      have hd : i₁.val - 1 < ℓ := by omega
      have hspec := (htr.fresh_slot_spec (by omega) (hfresh (i₁.val - 1) hd)).2
        (start + i₂.val) (by omega)
      have hidx : start + (i₁.val - 1) + 1 = start + i₁.val := by omega
      rw [hidx] at hspec
      exact hspec heq
  · dsimp only [y, Fin.val_zero]
    rw [Nat.add_zero]
    exact hstart
  · intro i
    dsimp only [y, Fin.val_succ]
    have hspec := (htr.fresh_slot_spec (i := start + i.val) (by omega) (hfresh i.val i.isLt)).1
    have hidx : start + i.val + 1 = start + (i.val + 1) := by omega
    rw [hidx] at hspec
    exact hinit _ _ hspec

/-- Map key index `i ∈ [0, L]` of a bicyclic prefix to its half-step entry index in `es`. -/
private def bicyclicKeyStep (t₁ T₁ i : ℕ) : ℕ :=
  if i ≤ t₁ then i else T₁ + (i - t₁)

/-- Map fresh step index `m ∈ [0, L)` of a bicyclic prefix to its half-step index in `es`. -/
private def bicyclicFreshStep (t₁ T₁ m : ℕ) : ℕ :=
  if m < t₁ then m else T₁ + (m - t₁)

private theorem bicyclicKeyStep_succ (t₁ T₁ m : ℕ) :
    bicyclicKeyStep t₁ T₁ (m + 1) = bicyclicFreshStep t₁ T₁ m + 1 := by
  unfold bicyclicKeyStep bicyclicFreshStep
  split_ifs <;> omega

private theorem bicyclicKeyStep_le_freshStep (t₁ T₁ i m : ℕ) (ht : t₁ ≤ T₁) (him : i ≤ m) :
    bicyclicKeyStep t₁ T₁ i ≤ bicyclicFreshStep t₁ T₁ m := by
  unfold bicyclicKeyStep bicyclicFreshStep
  split_ifs <;> omega

/-- If a walk trace has its first revisit at `t₁` (`s₀ < t₁`) and its first subsequent revisit at or
after `T₁ = t₁ + s₀ + 1` at step `t₂ < N`, then `L = t₁ + (t₂ - T₁)` satisfies `2 ≤ L < N` and
`HasBicyclicPrefix h₁ h₂ S u L`. -/
private theorem IsRawWalkTrace.hasBicyclicPrefix_of_two_revisits {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es)
    (hu0 : (es 0).key = u)
    (hinit : ∀ s d, f 0 s = some d → d.key ∈ S)
    {s₀ t₁ t₂ : ℕ} (hst : s₀ < t₁) (ht₁₂ : t₁ + s₀ + 1 ≤ t₂) (ht₂N : t₂ < N)
    (hrev₁ : stepSlot h₁ h₂ s₀ (es s₀).key = stepSlot h₁ h₂ t₁ (es t₁).key)
    (hfresh₁ : ∀ i < t₁, ∀ k < i, stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ i (es i).key)
    (hrev₂ : ∃ k < t₂, stepSlot h₁ h₂ k (es k).key = stepSlot h₁ h₂ t₂ (es t₂).key)
    (hfresh₂ : ∀ m, t₁ + s₀ + 1 ≤ m → m < t₂ → ∀ k < m,
      stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ m (es m).key) :
    ∃ L ∈ Finset.Ico 2 N, HasBicyclicPrefix h₁ h₂ S u L := by
  let T₁ := t₁ + s₀ + 1
  let L := t₁ + (t₂ - T₁)
  have hpar_st : s₀ % 2 = t₁ % 2 := stepSlot_eq_imp_mod_two_eq hrev₁
  have ht₁_ge2 : 2 ≤ t₁ := by omega
  have hL_ge2 : 2 ≤ L := by omega
  have hL_ltN : L < N := by omega
  have hT₁_key : (es T₁).key = u := by
    have hbt := htr.backtrack_at_first_revisit hst hfresh₁ hrev₁ s₀ le_rfl (by omega)
    have hidx : t₁ + s₀ + 1 = T₁ := rfl
    have hsub : s₀ - s₀ = 0 := Nat.sub_self s₀
    rw [hsub, hu0] at hbt
    exact hbt.2
  have hfresh_step : ∀ m < L, ∀ k < bicyclicFreshStep t₁ T₁ m,
      stepSlot h₁ h₂ k (es k).key ≠
        stepSlot h₁ h₂ (bicyclicFreshStep t₁ T₁ m) (es (bicyclicFreshStep t₁ T₁ m)).key := by
    intro m hmL
    unfold bicyclicFreshStep
    split_ifs with hmt₁
    · exact hfresh₁ m hmt₁
    · exact hfresh₂ (T₁ + (m - t₁)) (by omega) (by omega)
  have hstep_ltN : ∀ m < L, bicyclicFreshStep t₁ T₁ m < N := by
    intro m hmL
    unfold bicyclicFreshStep
    split_ifs <;> omega
  let y : Fin (L + 1) → Fin U := fun i => (es (bicyclicKeyStep t₁ T₁ i.val)).key
  have hy0 : y 0 = u := by
    simp only [y, Fin.val_zero, bicyclicKeyStep, Nat.zero_le, ↓reduceIte, hu0]
  have hymem : ∀ i : Fin L, y i.succ ∈ S := by
    intro i
    dsimp only [y, Fin.val_succ]
    rw [bicyclicKeyStep_succ]
    have hspec := (htr.fresh_slot_spec (hstep_ltN i.val i.isLt) (hfresh_step i.val i.isLt)).1
    exact hinit _ _ hspec
  have hyinj : Function.Injective y := by
    intro i₁ i₂ heq
    rcases lt_trichotomy i₁.val i₂.val with hlt | heq_val | hgt
    · exfalso
      have hm : i₂.val - 1 < L := by omega
      have hspec := (htr.fresh_slot_spec (hstep_ltN (i₂.val - 1) hm)
        (hfresh_step (i₂.val - 1) hm)).2 (bicyclicKeyStep t₁ T₁ i₁.val)
        (bicyclicKeyStep_le_freshStep t₁ T₁ i₁.val (i₂.val - 1) (by omega) (by omega))
      have hidx : bicyclicFreshStep t₁ T₁ (i₂.val - 1) + 1 = bicyclicKeyStep t₁ T₁ i₂.val := by
        rw [← bicyclicKeyStep_succ, Nat.sub_add_cancel (by omega)]
      rw [hidx] at hspec
      exact hspec heq.symm
    · exact Fin.ext heq_val
    · exfalso
      have hm : i₁.val - 1 < L := by omega
      have hspec := (htr.fresh_slot_spec (hstep_ltN (i₁.val - 1) hm)
        (hfresh_step (i₁.val - 1) hm)).2 (bicyclicKeyStep t₁ T₁ i₂.val)
        (bicyclicKeyStep_le_freshStep t₁ T₁ i₂.val (i₁.val - 1) (by omega) (by omega))
      have hidx : bicyclicFreshStep t₁ T₁ (i₁.val - 1) + 1 = bicyclicKeyStep t₁ T₁ i₁.val := by
        rw [← bicyclicKeyStep_succ, Nat.sub_add_cancel (by omega)]
      rw [hidx] at hspec
      exact hspec heq
  have hbase_chains :
      EquationChain h₁ (mapIdxChain y (buildFreshChains L false t₁ L le_rfl).1) ∧
        EquationChain h₂ (mapIdxChain y (buildFreshChains L false t₁ L le_rfl).2) := by
    refine equationChain_buildFreshChains_of_steps h₁ h₂ L false t₁ y L le_rfl ?_
    intro m hmL _
    have hhome := htr.step_home (bicyclicFreshStep t₁ T₁ m) (hstep_ltN m hmL)
    rw [stepSlot_eq_iff] at hhome
    have htab_eq : stepTable false t₁ m = (bicyclicFreshStep t₁ T₁ m % 2 == 1) := by
      unfold stepTable bicyclicFreshStep
      split_ifs with hmt₁
      · simp
      · have hmod : (T₁ + (m - t₁)) % 2 = (m - t₁ + 1) % 2 := by dsimp only [T₁]; omega
        simp [hmod]
    have hy_cur : y ⟨m + 1, by omega⟩ = (es (bicyclicFreshStep t₁ T₁ m + 1)).key := by
      dsimp only [y]
      rw [bicyclicKeyStep_succ]
    have hy_pred : y ⟨stepPred t₁ m, by unfold stepPred; split_ifs <;> omega⟩ =
        (es (bicyclicFreshStep t₁ T₁ m)).key := by
      dsimp only [y]
      rcases lt_trichotomy t₁ m with hgt | rfl | hlt
      · have h1 : stepPred t₁ m = m := by unfold stepPred; rw [ite_eq_right (by omega)]
        have h2 : bicyclicKeyStep t₁ T₁ m = T₁ + (m - t₁) := by
          unfold bicyclicKeyStep; rw [ite_eq_right (by omega)]
        have h3 : bicyclicFreshStep t₁ T₁ m = T₁ + (m - t₁) := by
          unfold bicyclicFreshStep; rw [ite_eq_right (by omega)]
        rw [h1, h2, h3]
      · have h1 : stepPred t₁ t₁ = 0 := by unfold stepPred; simp
        have h2 : bicyclicKeyStep t₁ T₁ 0 = 0 := by unfold bicyclicKeyStep; simp
        have h3 : bicyclicFreshStep t₁ T₁ t₁ = T₁ := by unfold bicyclicFreshStep; simp
        rw [h1, h2, h3, hu0, hT₁_key]
      · have h1 : stepPred t₁ m = m := by unfold stepPred; rw [ite_eq_right (by omega)]
        have h2 : bicyclicKeyStep t₁ T₁ m = m := by
          unfold bicyclicKeyStep; rw [ite_eq_left (by omega)]
        have h3 : bicyclicFreshStep t₁ T₁ m = m := by
          unfold bicyclicFreshStep; rw [ite_eq_left hlt]
        rw [h1, h2, h3]
    rw [htab_eq, hy_cur, hy_pred]
    exact hhome
  let p_fin : Fin (L + 1) := ⟨t₁, by omega⟩
  let s_fin : Fin (L + 1) := ⟨s₀, by omega⟩
  let endIdx : Fin (L + 1) := ⟨if t₁ = L then 0 else L, by split_ifs <;> omega⟩
  have hc1_chains :
      EquationChain h₁ (mapIdxChain y (prependToTable (t₁ % 2 == 1) (p_fin, s_fin)
        (buildFreshChains L false t₁ L le_rfl)).1) ∧
      EquationChain h₂ (mapIdxChain y (prependToTable (t₁ % 2 == 1) (p_fin, s_fin)
        (buildFreshChains L false t₁ L le_rfl)).2) := by
    have hmap := mapIdxChain_prependToTable y (t₁ % 2 == 1) (p_fin, s_fin)
      (buildFreshChains L false t₁ L le_rfl)
    have h1 := congrArg Prod.fst hmap
    have h2 := congrArg Prod.snd hmap
    dsimp only at h1 h2
    rw [h1, h2]
    refine equationChain_prependToTable h₁ h₂ (t₁ % 2 == 1) (y p_fin, y s_fin) _ ?_ hbase_chains
    have hyp : y p_fin = (es t₁).key := by
      dsimp only [y, p_fin, bicyclicKeyStep]
      rw [ite_eq_left le_rfl]
    have hys : y s_fin = (es s₀).key := by
      dsimp only [y, s_fin, bicyclicKeyStep]
      rw [ite_eq_left (by omega)]
    rw [hyp, hys]
    have hrev_eq : stepSlot h₁ h₂ t₁ (es t₁).key = stepSlot h₁ h₂ t₁ (es s₀).key := by
      rw [← hrev₁]
      unfold stepSlot
      rw [hpar_st]
    exact (stepSlot_eq_iff h₁ h₂ t₁ (es t₁).key (es s₀).key).mp hrev_eq
  rcases hrev₂ with ⟨k₀, hk₀_lt, hk₀_eq⟩
  have hT₁_odd : T₁ % 2 = 1 := by dsimp only [T₁]; omega
  have hk' : ∃ j : Fin (L + 1),
      (if t₁ = L then 1 ≤ j.val ∧ j.val < L else j.val < L) ∧
      stepSlot h₁ h₂ t₂ (y endIdx) = stepSlot h₁ h₂ t₂ (y j) := by
    have hend : y endIdx = (es t₂).key := by
      dsimp only [y, endIdx]
      by_cases hpL : t₁ = L
      · rw [ite_eq_left hpL]
        have h2 : bicyclicKeyStep t₁ T₁ 0 = 0 := by unfold bicyclicKeyStep; simp
        have h3 : t₂ = T₁ := by dsimp only [L] at hpL; omega
        rw [h2, h3, hu0, hT₁_key]
      · rw [ite_eq_right hpL]
        have h2 : bicyclicKeyStep t₁ T₁ L = t₂ := by
          unfold bicyclicKeyStep
          rw [ite_eq_right (by dsimp only [L] at hpL ⊢; omega)]
          dsimp only [L, T₁]
          omega
        rw [h2]
    by_cases hk_lt : k₀ < t₁
    · refine ⟨⟨k₀, by omega⟩, ?_, ?_⟩
      · dsimp only
        split_ifs with hpL
        · have ht₂_eq : t₂ = T₁ := by omega
          have hpar_k : k₀ % 2 = t₂ % 2 := stepSlot_eq_imp_mod_two_eq hk₀_eq
          rw [ht₂_eq, hT₁_odd] at hpar_k
          omega
        · omega
      · have hyj : y ⟨k₀, by omega⟩ = (es k₀).key := by
          dsimp only [y, bicyclicKeyStep]
          rw [ite_eq_left (by omega)]
        rw [hend, hyj, ← hk₀_eq]
        have hpar_k : k₀ % 2 = t₂ % 2 := stepSlot_eq_imp_mod_two_eq hk₀_eq
        unfold stepSlot
        rw [hpar_k]
    · by_cases hk_mid : k₀ ≤ t₁ + s₀
      · let k₁ := s₀ - (k₀ - t₁)
        have hbt := htr.backtrack_at_first_revisit hst hfresh₁ hrev₁ (k₀ - t₁) (by omega) (by omega)
        have hm_eq : t₁ + (k₀ - t₁) = k₀ := by omega
        rw [hm_eq] at hbt
        have hk₁_eq : stepSlot h₁ h₂ k₁ (es k₁).key = stepSlot h₁ h₂ t₂ (es t₂).key :=
          hbt.1.symm.trans hk₀_eq
        refine ⟨⟨k₁, by omega⟩, ?_, ?_⟩
        · dsimp only
          split_ifs with hpL
          · have ht₂_eq : t₂ = T₁ := by omega
            have hpar_k : k₁ % 2 = t₂ % 2 := stepSlot_eq_imp_mod_two_eq hk₁_eq
            rw [ht₂_eq, hT₁_odd] at hpar_k
            omega
          · omega
        · have hyj : y ⟨k₁, by omega⟩ = (es k₁).key := by
            dsimp only [y, bicyclicKeyStep]
            rw [ite_eq_left (by omega)]
          rw [hend, hyj, ← hk₁_eq]
          have hpar_k : k₁ % 2 = t₂ % 2 := stepSlot_eq_imp_mod_two_eq hk₁_eq
          unfold stepSlot
          rw [hpar_k]
      · have hpL_ne : t₁ ≠ L := by omega
        let j_val := if k₀ = T₁ then 0 else t₁ + (k₀ - T₁)
        refine ⟨⟨j_val, by dsimp only [j_val]; split_ifs <;> omega⟩, ?_, ?_⟩
        · rw [ite_eq_right hpL_ne]
          dsimp only [j_val]
          split_ifs <;> omega
        · have hyj : y ⟨j_val, by dsimp only [j_val]; split_ifs <;> omega⟩ = (es k₀).key := by
            dsimp only [y, j_val, bicyclicKeyStep]
            split_ifs with h1 h2
            · subst h1; rw [hu0, hT₁_key]
            · omega
            · omega
            · exact congrArg (fun idx => (es idx).key) (by omega)
          rw [hend, hyj, ← hk₀_eq]
          have hpar_k : k₀ % 2 = t₂ % 2 := stepSlot_eq_imp_mod_two_eq hk₀_eq
          unfold stepSlot
          rw [hpar_k]
  rcases hk' with ⟨j_fin, hj_valid, hj_slot⟩
  have hchains_all :
      EquationChain h₁ (mapIdxChain y (bicyclicChains L p_fin s_fin j_fin).1) ∧
        EquationChain h₂ (mapIdxChain y (bicyclicChains L p_fin s_fin j_fin).2) := by
    unfold bicyclicChains
    dsimp only [p_fin]
    have hmap := mapIdxChain_prependToTable y ((L - t₁ + 1) % 2 == 1) (endIdx, j_fin)
      (prependToTable (t₁ % 2 == 1) (p_fin, s_fin) (buildFreshChains L false t₁ L le_rfl))
    have h1 := congrArg Prod.fst hmap
    have h2 := congrArg Prod.snd hmap
    dsimp only at h1 h2
    rw [h1, h2]
    refine equationChain_prependToTable h₁ h₂ ((L - t₁ + 1) % 2 == 1) (y endIdx, y j_fin) _ ?_
      hc1_chains
    have hpar_t₂ : ((L - t₁ + 1) % 2 == 1) = (t₂ % 2 == 1) := by
      have hmod : (L - t₁ + 1) % 2 = t₂ % 2 := by dsimp only [L, T₁]; omega
      rw [hmod]
    rw [hpar_t₂]
    exact (stepSlot_eq_iff h₁ h₂ t₂ (y endIdx) (y j_fin)).mp hj_slot
  exact ⟨L, Finset.mem_Ico.mpr ⟨hL_ge2, hL_ltN⟩, p_fin, s_fin, j_fin, y,
    ⟨ht₁_ge2, hst, hpar_st, hj_valid⟩, hyinj, hy0, hymem, hchains_all.1, hchains_all.2⟩

/-- Predicate that half-step `i` probes a slot already probed at some earlier step `s < i`. -/
private def IsRevisit {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (es : ℕ → SlotEntry U) (i : ℕ) : Prop :=
  ∃ s ∈ Finset.range i, stepSlot h₁ h₂ s (es s).key = stepSlot h₁ h₂ i (es i).key

private instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (es : ℕ → SlotEntry U) (i : ℕ) :
    Decidable (IsRevisit h₁ h₂ es i) := by
  unfold IsRevisit
  infer_instance

/-- **Pagh & Rodler (2004), Section 2.3, Lemma 1 (half-step trace dichotomy)**:
In any `N`-half-step walk trace (`2 ≤ N`) starting at `(es 0).key = u` with initial table entries in
`S`, either there is a simple alternating path of length `(N + 2) / 3` starting at `u`, or there is
a bicyclic prefix of length `L ∈ [2, N)` starting at `u`. -/
private theorem IsRawWalkTrace.dichotomy {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) (hN : 2 ≤ N)
    (hu0 : (es 0).key = u)
    (hinit : ∀ s d, f 0 s = some d → d.key ∈ S) :
    HasAltPath h₁ h₂ S u ((N + 2) / 3) ∨
      ∃ L ∈ Finset.Ico 2 N, HasBicyclicPrefix h₁ h₂ S u L := by
  let ℓ := (N + 2) / 3
  by_cases hrev1 : ∃ i, i < N ∧ IsRevisit h₁ h₂ es i
  · let t₁ := Nat.find hrev1
    obtain ⟨ht₁_lt, s₀, hs₀_mem, hs₀_eq⟩ := Nat.find_spec hrev1
    have hs₀_lt : s₀ < t₁ := Finset.mem_range.mp hs₀_mem
    have hfresh₁ : ∀ i < t₁, ∀ k < i,
        stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ i (es i).key := by
      intro i hi k hk heq
      exact Nat.find_min hrev1 hi ⟨by omega, k, Finset.mem_range.mpr hk, heq⟩
    let T₁ := t₁ + s₀ + 1
    by_cases hrev2 : ∃ m, T₁ ≤ m ∧ m < N ∧ IsRevisit h₁ h₂ es m
    · let t₂ := Nat.find hrev2
      obtain ⟨hT₁_le, ht₂_lt, s₂, hs₂_mem, hs₂_eq⟩ := Nat.find_spec hrev2
      have hfresh₂ : ∀ m, T₁ ≤ m → m < t₂ → ∀ k < m,
          stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ m (es m).key := by
        intro m hTm hmt₂ k hk heq
        exact Nat.find_min hrev2 hmt₂ ⟨hTm, by omega, k, Finset.mem_range.mpr hk, heq⟩
      exact Or.inr (htr.hasBicyclicPrefix_of_two_revisits hu0 hinit hs₀_lt hT₁_le ht₂_lt hs₀_eq
        hfresh₁ ⟨s₂, Finset.mem_range.mp hs₂_mem, hs₂_eq⟩ hfresh₂)
    · left
      by_cases hℓ_le : ℓ ≤ t₁
      · refine htr.hasAltPath_of_fresh_segment hinit (start := 0) (by omega) hu0 ?_
        intro d hd k hk
        simp only [Nat.zero_add] at hk ⊢
        exact hfresh₁ d (by omega) k hk
      · have hT₁_bound : T₁ + ℓ ≤ N := by dsimp only [T₁, ℓ] at hℓ_le ⊢; omega
        have hT₁_key : (es T₁).key = u := by
          have hbt := htr.backtrack_at_first_revisit hs₀_lt hfresh₁ hs₀_eq s₀ le_rfl (by omega)
          have hsub : s₀ - s₀ = 0 := Nat.sub_self s₀
          rw [hsub, hu0] at hbt
          exact hbt.2
        refine htr.hasAltPath_of_fresh_segment hinit (start := T₁) hT₁_bound hT₁_key ?_
        intro d hd k hk heq
        exact hrev2 ⟨T₁ + d, by omega, by omega, k, Finset.mem_range.mpr hk, heq⟩
  · left
    refine htr.hasAltPath_of_fresh_segment hinit (start := 0) (by omega) hu0 ?_
    intro d hd k hk heq
    simp only [Nat.zero_add] at hk heq
    exact hrev1 ⟨d, by omega, k, Finset.mem_range.mpr hk, heq⟩

/-- **Pagh & Rodler (2004), Section 2.3, Lemma 1 (bicyclic form)**:
If `pureEvict h₁ h₂ r tbl₀ e₀ = none` (`1 ≤ r`) from a valid placement `tbl₀` of `S` with
`e₀.key = u ∉ S`, then either `HasAltPath h₁ h₂ S u ((2 * r + 2) / 3)` holds or there is some
`L ∈ Finset.Ico 2 (2 * r)` with `HasBicyclicPrefix h₁ h₂ S u L`. -/
theorem cuckooWalk_dichotomy_bicyclic {U m r : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U} {tbl₀ : PureTable U m} {e₀ : SlotEntry U}
    (hr : 1 ≤ r) (hvp : ValidPlacement h₁ h₂ S tbl₀) (hu : u ∉ S) (he₀ : e₀.key = u)
    (hev : pureEvict h₁ h₂ r tbl₀ e₀ = none) :
    HasAltPath h₁ h₂ S u ((2 * r + 2) / 3) ∨
      ∃ L ∈ Finset.Ico 2 (2 * r), HasBicyclicPrefix h₁ h₂ S u L := by
  have hno₀ : ¬ HasKey tbl₀ e₀.key := by
    rw [he₀]
    intro hkey
    exact hu (hvp.2 u hkey)
  obtain ⟨f, es, hf0, hes0, htr⟩ := exists_rawWalkTrace_of_pureEvict_eq_none r hvp.1 hno₀ hev
  refine htr.dichotomy (by omega) (by rw [hes0, he₀]) ?_
  intro s d hread
  rw [hf0] at hread
  exact hvp.2 d.key ⟨d, readSlot_some_imp_entryIn hread, rfl⟩

/-- **Pagh & Rodler (2004), Section 2.3, Lemma 1 (excess-subset form)**:
If `pureEvict h₁ h₂ r tbl₀ e₀ = none` (`1 ≤ r`) from a valid placement `tbl₀` of `S` with
`e₀.key = u ∉ S`, then either `HasAltPath h₁ h₂ S u ((2 * r + 2) / 3)` (Case B) or
`HasExcessSubset h₁ h₂ S u (2 * r)` (Case A) holds. -/
theorem cuckooWalk_dichotomy {U m r : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U} {tbl₀ : PureTable U m} {e₀ : SlotEntry U}
    (hr : 1 ≤ r) (hvp : ValidPlacement h₁ h₂ S tbl₀) (hu : u ∉ S) (he₀ : e₀.key = u)
    (hev : pureEvict h₁ h₂ r tbl₀ e₀ = none) :
    HasAltPath h₁ h₂ S u ((2 * r + 2) / 3) ∨ HasExcessSubset h₁ h₂ S u (2 * r) := by
  rcases cuckooWalk_dichotomy_bicyclic hr hvp hu he₀ hev with halt | ⟨L, hL, hbic⟩
  · exact Or.inl halt
  · rw [Finset.mem_Ico] at hL
    exact Or.inr (hasBicyclicPrefix_imp_hasExcessSubset hL.1 hL.2 hbic)

/-- If `r < evictRounds h₁ h₂ maxLoop tbl e`, then `pureEvict h₁ h₂ r tbl e = none`. -/
private theorem pureEvict_eq_none_of_lt_evictRounds {U m : ℕ} (h₁ h₂ : Fin U → Fin m) :
    ∀ {r maxLoop : ℕ} {tbl : PureTable U m} {e : SlotEntry U},
      r < evictRounds h₁ h₂ maxLoop tbl e → pureEvict h₁ h₂ r tbl e = none
  | 0, _, _, _, _ => rfl
  | r + 1, 0, _, _, hlt => by simp [evictRounds] at hlt
  | r + 1, fuel + 1, tbl, e, hlt => by
    unfold evictRounds at hlt
    unfold pureEvict
    cases h : pureEvictRound h₁ h₂ tbl e with
    | mk tbl' oe =>
      cases oe with
      | none => rw [h] at hlt; dsimp only at hlt; omega
      | some e' =>
        rw [h] at hlt
        dsimp only at hlt ⊢
        exact pureEvict_eq_none_of_lt_evictRounds h₁ h₂ (maxLoop := fuel) (by omega)

/-- If `1 ≤ r` and `r < cuckooWalkRounds h₁ h₂ maxLoop S u` with `u ∉ S`, then either
`HasAltPath h₁ h₂ S u ((2 * r + 2) / 3)` holds or there is `L ∈ Finset.Ico 2 (2 * r)` with
`HasBicyclicPrefix h₁ h₂ S u L`. -/
theorem lt_cuckooWalkRounds_imp_dichotomy {U m maxLoop r : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U} (hr : 1 ≤ r) (hu : u ∉ S)
    (hlt : r < cuckooWalkRounds h₁ h₂ maxLoop S u) :
    HasAltPath h₁ h₂ S u ((2 * r + 2) / 3) ∨
      ∃ L ∈ Finset.Ico 2 (2 * r), HasBicyclicPrefix h₁ h₂ S u L := by
  unfold cuckooWalkRounds at hlt
  let W := {r' : ℕ | ∃ tbl : PureTable U m, ValidPlacement h₁ h₂ S tbl ∧
    ∃ idx : ℕ, r' = evictRounds h₁ h₂ maxLoop tbl ⟨u, idx⟩}
  have hbdd : BddAbove W :=
    ⟨maxLoop, fun _ ⟨tbl, _, idx, h⟩ => h ▸ evictRounds_le h₁ h₂ maxLoop tbl ⟨u, idx⟩⟩
  have hne : W.Nonempty :=
    ⟨_, PureTable.empty U m,
      ⟨wellPlaced_empty h₁ h₂, fun k hk => False.elim (not_hasKey_empty k hk)⟩, 0, rfl⟩
  obtain ⟨r', ⟨tbl, hvp, idx, rfl⟩, hr'⟩ := (lt_csSup_iff hbdd hne).mp hlt
  have hev := pureEvict_eq_none_of_lt_evictRounds h₁ h₂ hr'
  exact cuckooWalk_dichotomy_bicyclic hr hvp hu rfl hev

/-! ## Section 3: Seed-count tail bounds and rehash union bounds -/

/-- Whether some `L ∈ [2, 2 * r)` satisfies `HasBicyclicPrefix h₁ h₂ S u L`. -/
private def HasSomeBicyclicPrefix {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (r : ℕ) : Prop :=
  ∃ L ∈ Finset.Ico 2 (2 * r), HasBicyclicPrefix h₁ h₂ S u L

private instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (r : ℕ) :
    Decidable (HasSomeBicyclicPrefix h₁ h₂ S u r) := by
  unfold HasSomeBicyclicPrefix
  infer_instance

/-- Bad-walk event at round `r` for key `u` and set `S`: either `HasAltPath` of length
`(2 * r + 2) / 3` or `HasSomeBicyclicPrefix` at round `r`. -/
private def WalkBadAt {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (r : ℕ) :
    Prop :=
  HasAltPath h₁ h₂ S u ((2 * r + 2) / 3) ∨ HasSomeBicyclicPrefix h₁ h₂ S u r

private instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (r : ℕ) :
    Decidable (WalkBadAt h₁ h₂ S u r) := by
  unfold WalkBadAt
  infer_instance

private theorem walkBadAt_card_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m r : ℕ}
    (h₁ : Θ₁ → Fin U → Fin m) (h₂ : Θ₂ → Fin U → Fin m)
    (S : Finset (Fin U)) (u : Fin U) :
    #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u r} ≤
      #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ((2 * r + 2) / 3)} +
        #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r} := by
  classical
  have hsub :
      Finset.univ.filter (fun θ : Θ₁ × Θ₂ => WalkBadAt (h₁ θ.1) (h₂ θ.2) S u r) ⊆
        Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
          HasAltPath (h₁ θ.1) (h₂ θ.2) S u ((2 * r + 2) / 3)) ∪
        Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
          HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r) := by
    intro θ hθ
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
    exact hθ
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-- If replaying `ks` succeeds and replaying `ks ++ [u]` fails (with `ks.Nodup`, `u ∉ ks`, and
`1 ≤ maxLoop`), then `WalkBadAt h₁ h₂ ks.toFinset u maxLoop` holds. -/
private theorem step_rehash_imp_walkBadAt {U m maxLoop : ℕ} {h₁ h₂ : Fin U → Fin m}
    (hloop : 1 ≤ maxLoop) {ks : List (Fin U)} {u : Fin U}
    (hnodup : ks.Nodup) (hu : u ∉ ks)
    (hstep : (pureReplay h₁ h₂ maxLoop ks).isSome ∧
      (pureReplay h₁ h₂ maxLoop (ks ++ [u])).isNone) :
    WalkBadAt h₁ h₂ ks.toFinset u maxLoop := by
  rcases Option.isSome_iff_exists.mp hstep.1 with ⟨tbl, hrep⟩
  have hev : pureEvict h₁ h₂ maxLoop tbl ⟨u, ks.length⟩ = none := by
    have happ := pureReplay_append_singleton h₁ h₂ maxLoop ks u
    rw [hrep, Option.bind_some] at happ
    exact Option.isNone_iff_eq_none.mp (happ ▸ hstep.2)
  have hvp : ValidPlacement h₁ h₂ ks.toFinset tbl :=
    pureReplay_validPlacement hnodup (fun v hv => List.mem_toFinset.mpr hv) hrep
  have hu_notMem : u ∉ ks.toFinset := fun h => hu (List.mem_toFinset.mp h)
  exact cuckooWalk_dichotomy_bicyclic hloop hvp hu_notMem rfl hev

/-- If `¬ GoodForSet h₁ h₂ maxLoop S` (`1 ≤ maxLoop`), then there is some key `u ∈ S` such that
`WalkBadAt h₁ h₂ (S.erase u) u maxLoop` holds. -/
private theorem not_goodForSet_imp_exists_walkBadAt {U m maxLoop : ℕ} {h₁ h₂ : Fin U → Fin m}
    (hloop : 1 ≤ maxLoop) {S : Finset (Fin U)}
    (hbad : ¬ GoodForSet h₁ h₂ maxLoop S) :
    ∃ u ∈ S, WalkBadAt h₁ h₂ (S.erase u) u maxLoop := by
  unfold GoodForSet at hbad
  push Not at hbad
  rcases hbad with ⟨ks, hnodup, hsub, hnone⟩
  induction ks using List.reverseRecOn with
  | nil => simp [pureReplay] at hnone
  | append_singleton ks u ih =>
    rw [List.nodup_append_comm, List.singleton_append, List.nodup_cons] at hnodup
    rcases hnodup with ⟨hu_not_ks, hnodup_ks⟩
    have hsub_ks : ∀ v ∈ ks, v ∈ S := fun v hv => hsub v (List.mem_append_left [u] hv)
    have hu_mem : u ∈ S := hsub u (List.mem_append_right ks (List.mem_singleton_self u))
    cases hrep : pureReplay h₁ h₂ maxLoop ks with
    | none =>
      exact ih hnodup_ks hsub_ks (by rw [hrep]; intro h; cases h)
    | some tbl =>
      have hisSome : (pureReplay h₁ h₂ maxLoop ks).isSome = true := by rw [hrep]; rfl
      have hisNone : (pureReplay h₁ h₂ maxLoop (ks ++ [u])).isNone = true :=
        Option.isNone_iff_eq_none.mpr (Option.not_isSome_iff_eq_none.mp hnone)
      have hbad_step := step_rehash_imp_walkBadAt hloop hnodup_ks hu_not_ks ⟨hisSome, hisNone⟩
      have hsub_erase : ks.toFinset ⊆ S.erase u := by
        intro v hv
        rw [List.mem_toFinset] at hv
        exact Finset.mem_erase.mpr ⟨fun hvu => hu_not_ks (hvu ▸ hv), hsub_ks v hv⟩
      refine ⟨u, hu_mem, ?_⟩
      rcases hbad_step with ⟨b, y, hinj, hy0, hymem, heq1, heq2⟩ |
        ⟨L, hL, p, s, j, y, hidx, hinj, hy0, hymem, heq1, heq2⟩
      · exact Or.inl ⟨b, y, hinj, hy0, fun i => hsub_erase (hymem i), heq1, heq2⟩
      · exact Or.inr ⟨L, hL, p, s, j, y, hidx, hinj, hy0,
          fun i => hsub_erase (hymem i), heq1, heq2⟩

/-- Elementary dyadic sum bound in `ℕ`: if `2 ^ (r + 1) * f r ≤ M` for all `r < K`, then
`2 ^ K * (∑ r ∈ Finset.range K, f r) + M ≤ 2 ^ K * M`, and in particular
`∑ r ∈ Finset.range K, f r ≤ M`. -/
private theorem two_pow_mul_sum_range_add_le {f : ℕ → ℕ} {M : ℕ} :
    ∀ (K : ℕ), (∀ r < K, 2 ^ (r + 1) * f r ≤ M) →
      2 ^ K * (∑ r ∈ Finset.range K, f r) + M ≤ 2 ^ K * M
  | 0, _ => by simp
  | K + 1, hle => by
    have ih := two_pow_mul_sum_range_add_le K fun r hr => hle r (by omega)
    have hK := hle K (by omega)
    rw [Finset.sum_range_succ, mul_add, pow_succ']
    calc 2 * 2 ^ K * ∑ x ∈ Finset.range K, f x + 2 * 2 ^ K * f K + M
        = 2 * 2 ^ K * ∑ x ∈ Finset.range K, f x + 2 ^ (K + 1) * f K + M := by
            rw [pow_succ']
      _ ≤ 2 * 2 ^ K * ∑ x ∈ Finset.range K, f x + M + M := by omega
      _ = 2 * (2 ^ K * ∑ x ∈ Finset.range K, f x + M) := by ring
      _ ≤ 2 * (2 ^ K * M) := Nat.mul_le_mul_left 2 ih
      _ = 2 * 2 ^ K * M := by ring

private theorem sum_range_le_of_two_pow_mul_le {f : ℕ → ℕ} {M K : ℕ}
    (hle : ∀ r < K, 2 ^ (r + 1) * f r ≤ M) :
    ∑ r ∈ Finset.range K, f r ≤ M := by
  have h1 := two_pow_mul_sum_range_add_le K hle
  have h2 : 2 ^ K * ∑ r ∈ Finset.range K, f r ≤ 2 ^ K * M := by omega
  exact Nat.le_of_mul_le_mul_left h2 (Nat.pos_of_ne_zero (by positivity))

/-- Elementary polynomial-vs-exponential bound `(d + 3) ^ 3 ≤ 27 * 4 ^ d` for all `d : ℕ`. -/
private theorem add_three_pow_three_le : ∀ d : ℕ, (d + 3) ^ 3 ≤ 27 * 4 ^ d
  | 0 => by decide
  | d + 1 => by
    have ih := add_three_pow_three_le d
    have hpoly : (d + 1 + 3) ^ 3 ≤ 4 * (d + 3) ^ 3 := by
      have : 3 * (d + 3) ^ 2 + 3 * (d + 3) + 1 ≤ 3 * (d + 3) ^ 3 := by nlinarith
      linarith [show (d + 1 + 3) ^ 3 = (d + 3) ^ 3 + (3 * (d + 3) ^ 2 + 3 * (d + 3) + 1) by ring,
        show 4 * (d + 3) ^ 3 = (d + 3) ^ 3 + 3 * (d + 3) ^ 3 by ring]
    calc (d + 1 + 3) ^ 3 ≤ 4 * (d + 3) ^ 3 := hpoly
      _ ≤ 4 * (27 * 4 ^ d) := Nat.mul_le_mul_left 4 ih
      _ = 27 * 4 ^ (d + 1) := by rw [pow_succ']; ring

/-- Under `32 * max n_max 4 ≤ m` and `S.card ≤ max n_max 4`, the number of seeds satisfying
`HasAltPath` of length `ℓ` (`ℓ + 1 ≤ k`) satisfies
`32 ^ ℓ * #{θ | HasAltPath ... ℓ} ≤ 2 * Fintype.card (Θ₁ × Θ₂)`. -/
private theorem thirty_two_pow_mul_card_hasAltPath_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k n_max ℓ : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (hm : 32 * max n_max 4 ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) (hℓk : ℓ + 1 ≤ k) :
    32 ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} ≤
      2 * Fintype.card (Θ₁ × Θ₂) := by
  let n := max n_max 4
  have hn_pos : 0 < n ^ ℓ := Nat.pos_of_ne_zero (by positivity)
  have hm_pos : 0 < m := by omega
  have h1 := card_filter_hasAltPath_le hm_pos hk₁ hk₂ S u hℓk
  have h2 : (32 ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ}) * n ^ ℓ ≤
      (2 * Fintype.card (Θ₁ × Θ₂)) * n ^ ℓ := by
    calc (32 ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ}) * n ^ ℓ
        = (32 * n) ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} := by
            rw [mul_pow]; ring
      _ ≤ m ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm ℓ)
      _ ≤ 2 * S.card ^ ℓ * Fintype.card (Θ₁ × Θ₂) := h1
      _ ≤ 2 * n ^ ℓ * Fintype.card (Θ₁ × Θ₂) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hS ℓ))
      _ = (2 * Fintype.card (Θ₁ × Θ₂)) * n ^ ℓ := by ring
  exact Nat.le_of_mul_le_mul_right h2 hn_pos

/-- Under `32 * max n_max 4 ≤ m` and `S.card ≤ max n_max 4`, the number of seeds satisfying
`HasBicyclicPrefix` of length `L = d + 2` (`d + 3 ≤ k`) satisfies
`32 * m ^ 2 * 8 ^ d * #{θ | HasBicyclicPrefix ... (d + 2)} ≤ Fintype.card (Θ₁ × Θ₂)`. -/
private theorem card_hasBicyclicPrefix_add_two_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k n_max d : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (hm : 32 * max n_max 4 ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) (hdk : d + 3 ≤ k) :
    32 * m ^ 2 * 8 ^ d * #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  let n := max n_max 4
  have hfactor_pos : 0 < 32 * 4 ^ d * n ^ (d + 2) := Nat.pos_of_ne_zero (by positivity)
  have hm_pos : 0 < m := by omega
  have h1 := card_filter_hasBicyclicPrefix_le hm_pos hk₁ hk₂ S u hdk
  have h32_pow : (32 * n) ^ (d + 2) = 32 * 8 ^ d * (32 * 4 ^ d * n ^ (d + 2)) := by
    rw [mul_pow, pow_add 32 d 2]
    have h84 : (32 : ℕ) ^ d = 8 ^ d * 4 ^ d := by rw [← mul_pow]; rfl
    rw [h84]
    ring
  have hcube : (d + 2 + 1) ^ 3 ≤ 32 * 4 ^ d :=
    le_trans (add_three_pow_three_le d) (Nat.mul_le_mul_right _ (by decide))
  have h2 :
      (32 * m ^ 2 * 8 ^ d *
        #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)}) *
        (32 * 4 ^ d * n ^ (d + 2)) ≤
      Fintype.card (Θ₁ × Θ₂) * (32 * 4 ^ d * n ^ (d + 2)) := by
    calc (32 * m ^ 2 * 8 ^ d *
          #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)}) *
          (32 * 4 ^ d * n ^ (d + 2))
        = m ^ 2 * (32 * 8 ^ d * (32 * 4 ^ d * n ^ (d + 2))) *
            #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)} := by ring
      _ = m ^ 2 * (32 * n) ^ (d + 2) *
            #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)} := by
            rw [← h32_pow]
      _ ≤ m ^ 2 * m ^ (d + 2) *
            #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)} :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm (d + 2)))
      _ = m ^ (d + 2 + 2) *
            #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)} := by
            rw [← pow_add, Nat.add_comm 2 (d + 2)]
      _ ≤ (d + 2 + 1) ^ 3 * S.card ^ (d + 2) * Fintype.card (Θ₁ × Θ₂) := h1
      _ ≤ (32 * 4 ^ d) * n ^ (d + 2) * Fintype.card (Θ₁ × Θ₂) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hcube (Nat.pow_le_pow_left hS (d + 2)))
      _ = Fintype.card (Θ₁ × Θ₂) * (32 * 4 ^ d * n ^ (d + 2)) := by ring
  exact Nat.le_of_mul_le_mul_right h2 hfactor_pos

/-- Union-bounding `HasBicyclicPrefix` over all `L ∈ Finset.Ico 2 (2 * r)` (`2 * r + 1 ≤ k`) yields
`4 * m ^ 2 * #{θ | HasSomeBicyclicPrefix ... r} ≤ Fintype.card (Θ₁ × Θ₂)`. -/
private theorem four_mul_m_sq_card_hasSomeBicyclicPrefix_le {Θ₁ Θ₂ : Type*}
    [Fintype Θ₁] [Fintype Θ₂] {U m k n_max r : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (hm : 32 * max n_max 4 ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) (hrk : 2 * r + 1 ≤ k) :
    4 * m ^ 2 *
      #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  classical
  let K := 2 * r - 2
  let E (d : ℕ) : Finset (Θ₁ × Θ₂) :=
    Finset.univ.filter (fun θ : Θ₁ × Θ₂ => HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2))
  have hsub :
      Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
        HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r) ⊆
        (Finset.range K).biUnion E := by
    intro θ hθ
    rw [Finset.mem_filter] at hθ
    rcases hθ.2 with ⟨L, hL, hbic⟩
    rw [Finset.mem_Ico] at hL
    rw [Finset.mem_biUnion]
    refine ⟨L - 2, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hL_eq : L - 2 + 2 = L := by omega
    rw [hL_eq]
    exact hbic
  have hcard_le :
      #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r} ≤
        ∑ d ∈ Finset.range K, (E d).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  calc 4 * m ^ 2 *
        #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r}
      ≤ 4 * m ^ 2 * ∑ d ∈ Finset.range K, (E d).card := Nat.mul_le_mul_left _ hcard_le
    _ = ∑ d ∈ Finset.range K, 4 * m ^ 2 * (E d).card := by rw [Finset.mul_sum]
    _ ≤ Fintype.card (Θ₁ × Θ₂) := by
        refine sum_range_le_of_two_pow_mul_le fun d hd => ?_
        have hstep := card_hasBicyclicPrefix_add_two_le hk₁ hk₂ hm hS u (d := d) (by omega)
        have hpow : 2 ^ (d + 1) ≤ 8 * 8 ^ d := by
          rw [pow_succ']
          exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (by decide) d)
        calc 2 ^ (d + 1) * (4 * m ^ 2 * (E d).card)
            ≤ (8 * 8 ^ d) * (4 * m ^ 2 * (E d).card) := Nat.mul_le_mul_right _ hpow
          _ = 32 * m ^ 2 * 8 ^ d * (E d).card := by ring
          _ ≤ Fintype.card (Θ₁ × Θ₂) := hstep

/-- Summing `WalkBadAt` seed counts over `1 ≤ r < MaxLoop` yields at most
`Fintype.card (Θ₁ × Θ₂)`. -/
private theorem sum_walkBadAt_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) :
    ∑ r ∈ Finset.Ico 1 MaxLoop,
      #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u r} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  let M := Fintype.card (Θ₁ × Θ₂)
  let K := MaxLoop - 1
  have hico_eq :
      ∑ r ∈ Finset.Ico 1 MaxLoop, #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u r} =
        ∑ i ∈ Finset.range K, #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u (i + 1)} := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm 1 i]
  have halt_sum :
      2 * ∑ i ∈ Finset.range K,
        #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ((2 * (i + 1) + 2) / 3)} ≤ M := by
    rw [Finset.mul_sum]
    refine sum_range_le_of_two_pow_mul_le fun i hi => ?_
    let ℓ := (2 * (i + 1) + 2) / 3
    have hstep := thirty_two_pow_mul_card_hasAltPath_le hk₁ hk₂ hm hS u (ℓ := ℓ) (by omega)
    have hpow : 4 * 2 ^ (i + 1) ≤ 32 ^ ℓ := by
      have h32 : (32 : ℕ) ^ ℓ = 2 ^ (5 * ℓ) := by
        change (2 ^ 5) ^ ℓ = 2 ^ (5 * ℓ)
        rw [← pow_mul]
      have h4 : 4 * 2 ^ (i + 1) = 2 ^ (i + 3) := by
        change 2 ^ 2 * 2 ^ (i + 1) = 2 ^ (i + 3)
        rw [← pow_add]
        congr 1; omega
      rw [h32, h4]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hmul := le_trans (Nat.mul_le_mul_right _ hpow) hstep
    have hring :
        2 * (2 ^ (i + 1) *
          (2 * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ})) =
        4 * 2 ^ (i + 1) *
          #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} := by ring
    dsimp only [ℓ] at hmul hring
    omega
  have hbic_sum :
      2 * ∑ i ∈ Finset.range K,
        #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (i + 1)} ≤ M := by
    have hm_pos : 0 < m := by omega
    have h1 :
        (2 * ∑ i ∈ Finset.range K,
          #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (i + 1)}) * m ≤ M * m := by
      calc (2 * ∑ i ∈ Finset.range K,
            #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (i + 1)}) * m
          = (2 * m) * ∑ i ∈ Finset.range K,
              #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (i + 1)} := by ring
        _ = ∑ i ∈ Finset.range K,
              2 * m * #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (i + 1)} := by
              rw [Finset.mul_sum]
        _ ≤ ∑ _i ∈ Finset.range K, M := by
              refine Finset.sum_le_sum fun i hi => ?_
              rw [Finset.mem_range] at hi
              have hstep := four_mul_m_sq_card_hasSomeBicyclicPrefix_le hk₁ hk₂ hm hS u
                (r := i + 1) (by omega)
              have hle_sq : 2 * m ≤ 4 * m ^ 2 := by nlinarith
              exact le_trans (Nat.mul_le_mul_right _ hle_sq) hstep
        _ = K * M := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        _ ≤ m * M := Nat.mul_le_mul_right M (by omega)
        _ = M * m := Nat.mul_comm m M
    exact Nat.le_of_mul_le_mul_right h1 hm_pos
  have hboth :
      ∑ i ∈ Finset.range K, #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u (i + 1)} ≤
        (∑ i ∈ Finset.range K,
          #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ((2 * (i + 1) + 2) / 3)}) +
        ∑ i ∈ Finset.range K,
          #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (i + 1)} := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => walkBadAt_card_le h₁ h₂ S u
  rw [hico_eq]
  omega

/-- Every `c ≤ MaxLoop` is bounded by `1 + #{r ∈ Ico 1 MaxLoop | r < c}`. -/
private theorem le_one_add_card_filter_Ico {c MaxLoop : ℕ} (hc : c ≤ MaxLoop) :
    c ≤ 1 + ((Finset.Ico 1 MaxLoop).filter (fun r => r < c)).card := by
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · simp
  · have hfilter : (Finset.Ico 1 MaxLoop).filter (fun r => r < c) = Finset.Ico 1 c := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [hfilter, Nat.card_Ico]
    omega

/-- The sum of `cuckooWalkRounds` over all seed pairs in `Θ₁ × Θ₂` is at most
`2 * Fintype.card (Θ₁ × Θ₂)`. -/
private theorem sum_cuckooWalkRounds_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card < n_max) {u : Fin U} (hu : u ∉ S) :
    ∑ θ : Θ₁ × Θ₂, cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u ≤
      2 * Fintype.card (Θ₁ × Θ₂) := by
  classical
  have hS_max : S.card ≤ max n_max 4 := by omega
  have htail := sum_walkBadAt_le hk₁ hk₂ hm hloop_le hS_max u
  have hpointwise : ∀ θ : Θ₁ × Θ₂,
      cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u ≤
        1 + ∑ r ∈ Finset.Ico 1 MaxLoop,
          if r < cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u then 1 else 0 := by
    intro θ
    rw [← Finset.card_filter]
    exact le_one_add_card_filter_Ico (cuckooWalkRounds_le_maxLoop (h₁ θ.1) (h₂ θ.2) MaxLoop S u)
  calc ∑ θ : Θ₁ × Θ₂, cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u
      ≤ ∑ θ : Θ₁ × Θ₂, (1 + ∑ r ∈ Finset.Ico 1 MaxLoop,
          if r < cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u then 1 else 0) :=
        Finset.sum_le_sum fun θ _ => hpointwise θ
    _ = Fintype.card (Θ₁ × Θ₂) +
          ∑ r ∈ Finset.Ico 1 MaxLoop, ∑ θ : Θ₁ × Θ₂,
            (if r < cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
          Finset.sum_comm]
    _ ≤ Fintype.card (Θ₁ × Θ₂) +
          ∑ r ∈ Finset.Ico 1 MaxLoop,
            #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u r} := by
        refine Nat.add_le_add_left (Finset.sum_le_sum fun r hr => ?_) _
        rw [← Finset.card_filter]
        refine Finset.card_le_card fun θ hθ => ?_
        rw [Finset.mem_filter] at hθ ⊢
        rw [Finset.mem_Ico] at hr
        exact ⟨Finset.mem_univ _, lt_cuckooWalkRounds_imp_dichotomy hr.1 hu hθ.2⟩
    _ ≤ Fintype.card (Θ₁ × Θ₂) + Fintype.card (Θ₁ × Θ₂) :=
        Nat.add_le_add_left htail _
    _ = 2 * Fintype.card (Θ₁ × Θ₂) := by ring

/-- At `r = MaxLoop ≥ maxEvictions n_max`, the number of seeds satisfying `WalkBadAt` is bounded by
`2 * (max n_max 1 * max MaxLoop 1) * #{θ | WalkBadAt ... MaxLoop} ≤ Fintype.card (Θ₁ × Θ₂)`. -/
private theorem two_mul_walkBadAt_maxLoop_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) :
    2 * (max n_max 1 * max MaxLoop 1) *
      #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u MaxLoop} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  let M := Fintype.card (Θ₁ × Θ₂)
  let ℓ := (2 * MaxLoop + 2) / 3
  have h18 : 18 ≤ MaxLoop := le_trans (eighteen_le_maxEvictions n_max) hloop_ge
  have halt :
      4 * (max n_max 1 * max MaxLoop 1) *
        #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} ≤ M := by
    have hstep := thirty_two_pow_mul_card_hasAltPath_le hk₁ hk₂ hm hS u (ℓ := ℓ) (by omega)
    have hclog_le : max n_max 1 ≤ 2 ^ Nat.clog 2 (max n_max 2) := by
      calc max n_max 1 ≤ max n_max 2 := by omega
        _ ≤ 2 ^ Nat.clog 2 (max n_max 2) := Nat.le_pow_clog (by decide) _
    have hloop_pow : max MaxLoop 1 ≤ 2 ^ MaxLoop := by
      have hmax : max MaxLoop 1 = MaxLoop := by omega
      rw [hmax]
      exact Nat.le_of_lt (Nat.lt_two_pow_self)
    have hexp_le : Nat.clog 2 (max n_max 2) + MaxLoop + 3 ≤ 5 * ℓ := by
      have hdef : 6 * (Nat.clog 2 (max n_max 2) + 2) ≤ MaxLoop := hloop_ge
      dsimp only [ℓ]
      omega
    have hpow_le : 8 * (max n_max 1 * max MaxLoop 1) ≤ 32 ^ ℓ := by
      calc 8 * (max n_max 1 * max MaxLoop 1)
          = 2 ^ 3 * max n_max 1 * max MaxLoop 1 := by ring
        _ ≤ 2 ^ 3 * 2 ^ Nat.clog 2 (max n_max 2) * 2 ^ MaxLoop :=
            Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 3) hclog_le) hloop_pow
        _ = 2 ^ (Nat.clog 2 (max n_max 2) + MaxLoop + 3) := by
            rw [← pow_add, ← pow_add]
            congr 1; omega
        _ ≤ 2 ^ (5 * ℓ) := Nat.pow_le_pow_right (by decide) hexp_le
        _ = 32 ^ ℓ := by
            change 2 ^ (5 * ℓ) = (2 ^ 5) ^ ℓ
            rw [← pow_mul]
    have hmul := le_trans (Nat.mul_le_mul_right _ hpow_le) hstep
    have hring :
        2 * (4 * (max n_max 1 * max MaxLoop 1) *
          #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ}) =
        8 * (max n_max 1 * max MaxLoop 1) *
          #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} := by ring
    omega
  have hbic :
      4 * (max n_max 1 * max MaxLoop 1) *
        #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u MaxLoop} ≤ M := by
    have hstep := four_mul_m_sq_card_hasSomeBicyclicPrefix_le hk₁ hk₂ hm hS u
      (r := MaxLoop) (by omega)
    have hn_le_m : max n_max 1 ≤ m := by omega
    have hl_le_m : max MaxLoop 1 ≤ m := by omega
    have hprod_le : 4 * (max n_max 1 * max MaxLoop 1) ≤ 4 * m ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul hn_le_m hl_le_m)
    exact le_trans (Nat.mul_le_mul_right _ hprod_le) hstep
  have hbad := walkBadAt_card_le h₁ h₂ S u (r := MaxLoop)
  have hbad_mul := Nat.mul_le_mul_left (4 * (max n_max 1 * max MaxLoop 1)) hbad
  rw [mul_add] at hbad_mul
  have hring :
      2 * (2 * (max n_max 1 * max MaxLoop 1) *
        #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u MaxLoop}) =
      4 * (max n_max 1 * max MaxLoop 1) *
        #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u MaxLoop} := by ring
  dsimp only [ℓ] at halt
  omega

open Classical in
/-- Union-bounding `WalkBadAt` over `u ∈ S` shows that at most half of the seed pairs fail
`GoodForSet` for `S` (`S.card ≤ n_max`). -/
private theorem two_mul_card_not_goodForSet_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ n_max) :
    2 * #{θ : Θ₁ × Θ₂ | ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hemp :
        Finset.univ.filter (fun θ : Θ₁ × Θ₂ => ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop ∅) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro θ _
      exact not_not.mpr (goodForSet_empty (h₁ θ.1) (h₂ θ.2) MaxLoop)
    rw [hemp]
    simp
  · have hcard_pos : 0 < S.card := Finset.Nonempty.card_pos hne
    have h18 : 1 ≤ MaxLoop := by
      have := eighteen_le_maxEvictions n_max
      omega
    let E (u : Fin U) : Finset (Θ₁ × Θ₂) :=
      Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
        WalkBadAt (h₁ θ.1) (h₂ θ.2) (S.erase u) u MaxLoop)
    have hsub :
        Finset.univ.filter (fun θ : Θ₁ × Θ₂ => ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S) ⊆
          S.biUnion E := by
      intro θ hθ
      rw [Finset.mem_filter] at hθ
      obtain ⟨u, huS, hbad⟩ := not_goodForSet_imp_exists_walkBadAt h18 hθ.2
      exact Finset.mem_biUnion.mpr ⟨u, huS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩
    have hbi := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have hmul :
        (2 * #{θ : Θ₁ × Θ₂ | ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S}) * S.card ≤
          Fintype.card (Θ₁ × Θ₂) * S.card := by
      calc (2 * #{θ : Θ₁ × Θ₂ | ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S}) * S.card
          = 2 * S.card * #{θ : Θ₁ × Θ₂ | ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S} := by ring
        _ ≤ 2 * S.card * ∑ u ∈ S, (E u).card := Nat.mul_le_mul_left _ hbi
        _ = ∑ u ∈ S, 2 * S.card * (E u).card := by rw [Finset.mul_sum]
        _ ≤ ∑ _u ∈ S, Fintype.card (Θ₁ × Θ₂) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have herase : (S.erase u).card ≤ max n_max 4 := by
              have := Finset.card_erase_lt_of_mem hu
              omega
            have hstep := two_mul_walkBadAt_maxLoop_le hk₁ hk₂ hm hloop_ge hloop_le herase u
            have hscard_le : 2 * S.card ≤ 2 * (max n_max 1 * max MaxLoop 1) := by
              have h1 : S.card ≤ max n_max 1 := by omega
              have h2 : 1 ≤ max MaxLoop 1 := by omega
              calc 2 * S.card ≤ 2 * (max n_max 1 * 1) := by omega
                _ ≤ 2 * (max n_max 1 * max MaxLoop 1) :=
                    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h2)
            exact le_trans (Nat.mul_le_mul_right _ hscard_le) hstep
        _ = S.card * Fintype.card (Θ₁ × Θ₂) := by rw [Finset.sum_const, smul_eq_mul]
        _ = Fintype.card (Θ₁ × Θ₂) * S.card := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hmul hcard_pos

/-! ## Section 4: `IsCuckooHashPair` instances and lazy random-oracle equivalence -/

/-- **Pagh & Rodler (2004), Section 2.3 (`IsCuckooHashPair` for `(2 * MaxLoop + 2)`-wise
independent hash pairs)**:
For any capacity `n_max : ℕ`, sub-table size `m` with `32 * max n_max 4 ≤ m`, eviction cap
`MaxLoop` with `maxEvictions n_max ≤ MaxLoop ≤ m`, and independent hash families
`h₁ : Θ₁ → Fin U → Fin m` and `h₂ : Θ₂ → Fin U → Fin m` each satisfying
`IsKWiseIndependentHash (2 * MaxLoop + 2)`, the uniform product distribution on `Θ₁ × Θ₂` satisfies
`IsCuckooHashPair` with universal constants `C_walk = 2` and `C_reh = 3`. -/
theorem isCuckooHashPair_of_kWiseIndependent {Θ₁ Θ₂ : Type*}
    [Fintype Θ₁] [Nonempty Θ₁]
    [Fintype Θ₂] [Nonempty Θ₂]
    {U m : ℕ} (n_max MaxLoop : ℕ)
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m) :
    IsCuckooHashPair (PMF.uniformOfFintype (Θ₁ × Θ₂))
      (fun θ : Θ₁ × Θ₂ => h₁ θ.1) (fun θ : Θ₁ × Θ₂ => h₂ θ.2)
      n_max MaxLoop 2 3 where
  expected_walk_le S u hS hu := by
    have hsum := sum_cuckooWalkRounds_le hk₁ hk₂ hm hloop_le hS hu
    exact mod_cast PMF.tsum_uniformOfFintype_le_of_sum_le hsum
  rehash_prob_le_half S hS := by
    classical
    have hcard := two_mul_card_not_goodForSet_le hk₁ hk₂ hm hloop_ge hloop_le hS
    have hcard' :
        2 * (Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
          ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S)).card ≤
        1 * Fintype.card (Θ₁ × Θ₂) := by
      simpa only [one_mul] using hcard
    have hmeas := PMF.toOuterMeasure_uniformOfFintype_le_div (by decide : 0 < 2) hcard'
    exact mod_cast hmeas
  step_rehash_prob_le ks u hnodup hlen hu := by
    classical
    let B := max n_max 1 * max MaxLoop 1
    have h18 : 1 ≤ MaxLoop := by
      have := eighteen_le_maxEvictions n_max
      omega
    have hB_pos : 0 < B := by positivity
    have hsub :
        Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
          (pureReplay (h₁ θ.1) (h₂ θ.2) MaxLoop ks).isSome ∧
            (pureReplay (h₁ θ.1) (h₂ θ.2) MaxLoop (ks ++ [u])).isNone) ⊆
          Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
            WalkBadAt (h₁ θ.1) (h₂ θ.2) ks.toFinset u MaxLoop) := by
      intro θ hθ
      rw [Finset.mem_filter] at hθ ⊢
      exact ⟨Finset.mem_univ _, step_rehash_imp_walkBadAt h18 hnodup hu hθ.2⟩
    have hcard_le := Finset.card_le_card hsub
    have hks_card : ks.toFinset.card ≤ max n_max 4 := by
      have := List.toFinset_card_le ks
      omega
    have hwalk := two_mul_walkBadAt_maxLoop_le hk₁ hk₂ hm hloop_ge hloop_le hks_card u
    have hbound :
        B * (Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
          (pureReplay (h₁ θ.1) (h₂ θ.2) MaxLoop ks).isSome ∧
            (pureReplay (h₁ θ.1) (h₂ θ.2) MaxLoop (ks ++ [u])).isNone)).card ≤
          3 * Fintype.card (Θ₁ × Θ₂) := by
      have h1 :
          B * (Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
            (pureReplay (h₁ θ.1) (h₂ θ.2) MaxLoop ks).isSome ∧
              (pureReplay (h₁ θ.1) (h₂ θ.2) MaxLoop (ks ++ [u])).isNone)).card ≤
          2 * B * #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) ks.toFinset u MaxLoop} := by
        calc B * _ ≤ B * #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) ks.toFinset u MaxLoop} :=
              Nat.mul_le_mul_left B hcard_le
          _ ≤ 2 * B * #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) ks.toFinset u MaxLoop} := by
              nlinarith
      exact le_trans h1 (le_trans hwalk (by omega))
    have hmeas := PMF.toOuterMeasure_uniformOfFintype_le_div hB_pos hbound
    have hmax (a : ℕ) : ((max a 1 : ℕ) : ℝ≥0∞) = max (a : ℝ≥0∞) 1 := by
      rcases le_total a 1 with h | h
      · rw [max_eq_right h, max_eq_right (by exact_mod_cast h), Nat.cast_one]
      · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]
    have hB_cast : (B : ℝ≥0∞) = max (n_max : ℝ≥0∞) 1 * max (MaxLoop : ℝ≥0∞) 1 := by
      dsimp only [B]
      rw [Nat.cast_mul, hmax, hmax]
    rw [hB_cast] at hmeas
    exact mod_cast hmeas

/-- **`IsCuckooHashPair` for two independent `trinomialPolyHash` polynomials**:
When `U ≤ 2 ^ (2 * 3 ^ t)`, `M ≤ 2 * 3 ^ t`, `32 * max n_max 4 ≤ 2 ^ M`, and
`maxEvictions n_max ≤ MaxLoop ≤ 2 ^ M`, two independent degree-`< k` (`2 * MaxLoop + 2 ≤ k`)
trinomial-field polynomial hashes `trinomialPolyHash t k U M` satisfy `IsCuckooHashPair` with
`C_walk = 2` and `C_reh = 3`. -/
theorem isCuckooHashPair_trinomialPolyHash {t k U M : ℕ}
    (hU : U ≤ 2 ^ (2 * 3 ^ t)) (hM : M ≤ 2 * 3 ^ t)
    (n_max MaxLoop : ℕ)
    (hdeg : 2 * MaxLoop + 2 ≤ k)
    (hm : 32 * max n_max 4 ≤ 2 ^ M)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ 2 ^ M) :
    IsCuckooHashPair
      (PMF.uniformOfFintype
        ((Fin k → Fin (2 ^ (2 * 3 ^ t))) × (Fin k → Fin (2 ^ (2 * 3 ^ t)))))
      (fun θ => trinomialPolyHash t k U M θ.1)
      (fun θ => trinomialPolyHash t k U M θ.2)
      n_max MaxLoop 2 3 := by
  have hk_ind : IsKWiseIndependentHash k (trinomialPolyHash t k U M) :=
    isKWiseIndependentHash_trinomialPolyHash hU hM
  have hk_mono : IsKWiseIndependentHash (2 * MaxLoop + 2) (trinomialPolyHash t k U M) :=
    hk_ind.mono hdeg
  exact isCuckooHashPair_of_kWiseIndependent n_max MaxLoop hk_mono hk_mono hm hloop_ge hloop_le

/-- **`IsCuckooHashPair` for a uniform random hash pair**:
When `32 * max n_max 4 ≤ m` and `maxEvictions n_max ≤ MaxLoop ≤ m`, sampling `(h₁, h₂)` uniformly
at random from `(Fin U → Fin m) × (Fin U → Fin m)` satisfies `IsCuckooHashPair` with `C_walk = 2`
and `C_reh = 3`. -/
theorem isCuckooHashPair_uniform {U m : ℕ} [NeZero m] (n_max MaxLoop : ℕ)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m) :
    IsCuckooHashPair
      (PMF.uniformOfFintype ((Fin U → Fin m) × (Fin U → Fin m)))
      Prod.fst Prod.snd n_max MaxLoop 2 3 := by
  have hid := isKWiseIndependentHash_id (X := Fin U) (Y := Fin m) (2 * MaxLoop + 2)
  exact isCuckooHashPair_of_kWiseIndependent n_max MaxLoop hid hid hm hloop_ge hloop_le

/-- Equivalence between a pair of hash functions `(Fin U → Fin m) × (Fin U → Fin m)` and a single
table-indexed hash oracle `Bool × Fin U → Fin m`. -/
private def hashPairEquiv (U m : ℕ) :
    ((Fin U → Fin m) × (Fin U → Fin m)) ≃ (Bool × Fin U → Fin m) where
  toFun p q := if q.1 then p.2 q.2 else p.1 q.2
  invFun f := (fun x => f (false, x), fun x => f (true, x))
  left_inv p := by ext <;> rfl
  right_inv f := by
    funext ⟨b, x⟩
    cases b <;> rfl

/-- **Lazy random-oracle equivalence for the uniform cuckoo hash pair**:
Sampling `(h₁, h₂)` eagerly from `PMF.uniformOfFintype ((Fin U → Fin m) × (Fin U → Fin m))` and
interpreting queries `(b, x) : Bool × Fin U` via `if b then h₂ x else h₁ x` has the exact same
output distribution as answering each distinct query `(b, x)` lazily on demand with an independent
uniform bucket in `Fin m` via `RandomOracle.answer`. -/
theorem uniform_interpret_eq_lazy_hashPair {U m : ℕ} [NeZero m] {α : Type}
    (program : OracleComp (fun _ : Bool × Fin U => Fin m) α) :
    (do
      let p ← PMF.uniformOfFintype ((Fin U → Fin m) × (Fin U → Fin m))
      OracleComp.interpret (fun q : Bool × Fin U => PMF.pure (if q.1 then p.2 q.2 else p.1 q.2))
        program) =
      ((OracleComp.interpret (RandomOracle.answer (fun _ => PMF.uniformOfFintype (Fin m)))
        program).run (fun _ => none)).map Prod.fst := by
  have heq :
      (do
        let p ← PMF.uniformOfFintype ((Fin U → Fin m) × (Fin U → Fin m))
        OracleComp.interpret (fun q : Bool × Fin U => PMF.pure (hashPairEquiv U m p q))
          program) =
      (do
        let table ← PMF.uniformOfFintype (Bool × Fin U → Fin m)
        OracleComp.interpret (fun q : Bool × Fin U => PMF.pure (table q)) program) := by
    rw [← PMF.uniformOfFintype_map_equiv (hashPairEquiv U m), PMF.monad_bind_eq_bind,
      PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl
  exact heq.trans (RandomOracle.uniform_interpret_eq_lazy program)

/-! ## Section 5: High-probability `k`-wise independence bridge and Double Tabulation -/

open Classical in
/-- Quarter-failure bound for `GoodForSet` under `(2 * MaxLoop + 2)`-wise independence:
`4 * #{θ | ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S} ≤ |Θ₁ × Θ₂|`. -/
private theorem four_mul_card_not_goodForSet_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ n_max) :
    4 * (Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
      ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S)).card ≤
      Fintype.card (Θ₁ × Θ₂) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hemp :
        Finset.univ.filter (fun θ : Θ₁ × Θ₂ => ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop ∅) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro θ _
      exact not_not.mpr (goodForSet_empty (h₁ θ.1) (h₂ θ.2) MaxLoop)
    rw [hemp]
    simp
  · have hcard_pos : 0 < S.card := Finset.Nonempty.card_pos hne
    have h18 : 18 ≤ MaxLoop := le_trans (eighteen_le_maxEvictions n_max) hloop_ge
    let E (u : Fin U) : Finset (Θ₁ × Θ₂) :=
      Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
        WalkBadAt (h₁ θ.1) (h₂ θ.2) (S.erase u) u MaxLoop)
    have hsub :
        Finset.univ.filter (fun θ : Θ₁ × Θ₂ => ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S) ⊆
          S.biUnion E := by
      intro θ hθ
      rw [Finset.mem_filter] at hθ
      obtain ⟨u, huS, hbad⟩ := not_goodForSet_imp_exists_walkBadAt (by omega) hθ.2
      exact Finset.mem_biUnion.mpr ⟨u, huS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩
    have hbi := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have hmul :
        (4 * #{θ : Θ₁ × Θ₂ | ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S}) * S.card ≤
          Fintype.card (Θ₁ × Θ₂) * S.card := by
      calc (4 * #{θ : Θ₁ × Θ₂ | ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S}) * S.card
          = 4 * S.card * #{θ : Θ₁ × Θ₂ | ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S} := by ring
        _ ≤ 4 * S.card * ∑ u ∈ S, (E u).card := Nat.mul_le_mul_left _ hbi
        _ = ∑ u ∈ S, 4 * S.card * (E u).card := by rw [Finset.mul_sum]
        _ ≤ ∑ _u ∈ S, Fintype.card (Θ₁ × Θ₂) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have herase : (S.erase u).card ≤ max n_max 4 := by
              have := Finset.card_erase_lt_of_mem hu
              omega
            have hstep := two_mul_walkBadAt_maxLoop_le hk₁ hk₂ hm hloop_ge hloop_le herase u
            have hscard_le : 4 * S.card ≤ 2 * (max n_max 1 * max MaxLoop 1) := by
              have h1 : S.card ≤ max n_max 1 := by omega
              have h2 : 2 ≤ max MaxLoop 1 := by omega
              nlinarith
            exact le_trans (Nat.mul_le_mul_right _ hscard_le) hstep
        _ = S.card * Fintype.card (Θ₁ × Θ₂) := by rw [Finset.sum_const, smul_eq_mul]
        _ = Fintype.card (Θ₁ × Θ₂) * S.card := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hmul hcard_pos

private theorem card_badTopPair_le {Θ_top : Type*} [Fintype Θ_top] [DecidableEq Θ_top]
    (GoodTop : Finset Θ_top) :
    (Finset.univ \ (GoodTop ×ˢ GoodTop)).card ≤
      2 * (Fintype.card Θ_top - GoodTop.card) * Fintype.card Θ_top := by
  let Bad := Finset.univ \ GoodTop
  have hBad_card : Bad.card = Fintype.card Θ_top - GoodTop.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ GoodTop), Finset.card_univ]
  have hsub : Finset.univ \ (GoodTop ×ˢ GoodTop) ⊆
      (Bad ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ Bad) := by
    intro ⟨α₁, α₂⟩ h
    simp only [Bad, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_product, Finset.mem_union,
      true_and, and_true] at h ⊢
    tauto
  calc (Finset.univ \ (GoodTop ×ˢ GoodTop)).card
      ≤ ((Bad ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ Bad)).card := Finset.card_le_card hsub
    _ ≤ (Bad ×ˢ Finset.univ).card + (Finset.univ ×ˢ Bad).card := Finset.card_union_le _ _
    _ = 2 * (Fintype.card Θ_top - GoodTop.card) * Fintype.card Θ_top := by
      rw [Finset.card_product, Finset.card_product, Finset.card_univ, hBad_card]
      ring

private theorem sum_prodProd_le_of_goodTop {Θ_top Θ_bot : Type*}
    [Fintype Θ_top] [DecidableEq Θ_top] [Fintype Θ_bot]
    (GoodTop : Finset Θ_top)
    (f : (Θ_top × Θ_bot) × (Θ_top × Θ_bot) → ℕ)
    {C_good C_bad : ℕ}
    (hgood : ∀ α₁ ∈ GoodTop, ∀ α₂ ∈ GoodTop,
      ∑ β : Θ_bot × Θ_bot, f ((α₁, β.1), (α₂, β.2)) ≤ C_good * Fintype.card (Θ_bot × Θ_bot))
    (hbad : ∀ θ, f θ ≤ C_bad) :
    ∑ θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot), f θ ≤
      (C_good * Fintype.card (Θ_top × Θ_top) +
        (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * C_bad) *
      Fintype.card (Θ_bot × Θ_bot) := by
  let e := Equiv.prodProdProdComm Θ_top Θ_bot Θ_top Θ_bot
  have hreindex : ∑ θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot), f θ =
      ∑ α : Θ_top × Θ_top, ∑ β : Θ_bot × Θ_bot, f ((α.1, β.1), (α.2, β.2)) := by
    rw [← Equiv.sum_comp e.symm f, Fintype.sum_prod_type]
    rfl
  rw [hreindex, ← Finset.sum_sdiff (Finset.subset_univ (GoodTop ×ˢ GoodTop))]
  have h₁ : ∑ α ∈ GoodTop ×ˢ GoodTop, ∑ β : Θ_bot × Θ_bot, f ((α.1, β.1), (α.2, β.2)) ≤
      C_good * Fintype.card (Θ_top × Θ_top) * Fintype.card (Θ_bot × Θ_bot) := by
    calc ∑ α ∈ GoodTop ×ˢ GoodTop, ∑ β : Θ_bot × Θ_bot, f ((α.1, β.1), (α.2, β.2))
        ≤ ∑ _α ∈ GoodTop ×ˢ GoodTop, C_good * Fintype.card (Θ_bot × Θ_bot) :=
          Finset.sum_le_sum fun α hα =>
            hgood α.1 (Finset.mem_product.mp hα).1 α.2 (Finset.mem_product.mp hα).2
      _ = (GoodTop ×ˢ GoodTop).card * (C_good * Fintype.card (Θ_bot × Θ_bot)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Fintype.card (Θ_top × Θ_top) * (C_good * Fintype.card (Θ_bot × Θ_bot)) :=
          Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      _ = C_good * Fintype.card (Θ_top × Θ_top) * Fintype.card (Θ_bot × Θ_bot) := by ring
  have h₂ : ∑ α ∈ Finset.univ \ (GoodTop ×ˢ GoodTop),
        ∑ β : Θ_bot × Θ_bot, f ((α.1, β.1), (α.2, β.2)) ≤
      (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * C_bad * Fintype.card (Θ_bot × Θ_bot) := by
    calc ∑ α ∈ Finset.univ \ (GoodTop ×ˢ GoodTop),
          ∑ β : Θ_bot × Θ_bot, f ((α.1, β.1), (α.2, β.2))
        ≤ ∑ _α ∈ Finset.univ \ (GoodTop ×ˢ GoodTop), ∑ _β : Θ_bot × Θ_bot, C_bad :=
          Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hbad _
      _ = (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * C_bad * Fintype.card (Θ_bot × Θ_bot) := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  calc ∑ α ∈ Finset.univ \ (GoodTop ×ˢ GoodTop), ∑ β : Θ_bot × Θ_bot, f ((α.1, β.1), (α.2, β.2)) +
        ∑ α ∈ GoodTop ×ˢ GoodTop, ∑ β : Θ_bot × Θ_bot, f ((α.1, β.1), (α.2, β.2))
      ≤ (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * C_bad * Fintype.card (Θ_bot × Θ_bot) +
          C_good * Fintype.card (Θ_top × Θ_top) * Fintype.card (Θ_bot × Θ_bot) :=
        Nat.add_le_add h₂ h₁
    _ = (C_good * Fintype.card (Θ_top × Θ_top) +
          (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * C_bad) *
        Fintype.card (Θ_bot × Θ_bot) := by ring

private theorem sum_ite_eq_mul_card_filter {γ : Type*} [Fintype γ]
    (Q : γ → Prop) [DecidablePred Q] (K : ℕ) :
    (∑ x : γ, if Q x then K else 0) = K * (Finset.univ.filter Q).card := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    Nat.mul_comm]

private theorem card_filter_prodProd_le_of_goodTop {Θ_top Θ_bot : Type*}
    [Fintype Θ_top] [DecidableEq Θ_top] [Fintype Θ_bot]
    (GoodTop : Finset Θ_top)
    (P : (Θ_top × Θ_bot) × (Θ_top × Θ_bot) → Prop) [DecidablePred P]
    {K A_good : ℕ}
    (hgood : ∀ α₁ ∈ GoodTop, ∀ α₂ ∈ GoodTop,
      K * (Finset.univ.filter fun β : Θ_bot × Θ_bot => P ((α₁, β.1), (α₂, β.2))).card ≤
        A_good * Fintype.card (Θ_bot × Θ_bot)) :
    K * (Finset.univ.filter P).card ≤
      (A_good * Fintype.card (Θ_top × Θ_top) +
        (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * K) *
      Fintype.card (Θ_bot × Θ_bot) := by
  rw [← sum_ite_eq_mul_card_filter P K]
  refine sum_prodProd_le_of_goodTop GoodTop (fun θ => if P θ then K else 0)
    (fun α₁ hα₁ α₂ hα₂ => ?_) (fun θ => ?_)
  · rw [sum_ite_eq_mul_card_filter]
    exact hgood α₁ hα₁ α₂ hα₂
  · split_ifs <;> omega

/-- **Black-box high-probability `k`-wise independence conditioning bridge into
`IsCuckooHashPair`**:
Given a two-level hash family `H : Θ_top → Θ_bot → Fin U → Fin m` and a good top-seed set
`GoodTop : Finset Θ_top` such that:
1. `H α` is `(2 * MaxLoop + 2)`-wise independent for every `α ∈ GoodTop`, and
2. `2 * (|Θ_top| - |GoodTop|) * (max n_max 1 * max MaxLoop 1) ≤ |Θ_top|`,
under `32 * max n_max 4 ≤ m` and `maxEvictions n_max ≤ MaxLoop ≤ m`, two independent draws from
`Θ_top × Θ_bot` satisfy `IsCuckooHashPair` with constants `C_walk = 3` and `C_reh = 4`. -/
theorem isCuckooHashPair_of_whp_kWiseIndependent {Θ_top Θ_bot : Type*}
    [Fintype Θ_top] [Nonempty Θ_top]
    [Fintype Θ_bot] [Nonempty Θ_bot]
    {U m : ℕ} (n_max MaxLoop : ℕ)
    {H : Θ_top → Θ_bot → Fin U → Fin m}
    (GoodTop : Finset Θ_top)
    (hk : ∀ α ∈ GoodTop, IsKWiseIndependentHash (2 * MaxLoop + 2) (H α))
    (hwhp : 2 * (Fintype.card Θ_top - GoodTop.card) * (max n_max 1 * max MaxLoop 1) ≤
      Fintype.card Θ_top)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m) :
    IsCuckooHashPair
      (PMF.uniformOfFintype ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)))
      (fun ((top₁, bottom₁), _) => H top₁ bottom₁)
      (fun (_, (top₂, bottom₂)) => H top₂ bottom₂)
      n_max MaxLoop 3 4 := by
  classical
  let B := max n_max 1 * max MaxLoop 1
  let BadPair := Finset.univ \ (GoodTop ×ˢ GoodTop)
  have h18 : 18 ≤ MaxLoop := le_trans (eighteen_le_maxEvictions n_max) hloop_ge
  have hBad_B : BadPair.card * B ≤ Fintype.card (Θ_top × Θ_top) := by
    calc BadPair.card * B
        ≤ (2 * (Fintype.card Θ_top - GoodTop.card) * Fintype.card Θ_top) * B :=
          Nat.mul_le_mul_right B (card_badTopPair_le GoodTop)
      _ = (2 * (Fintype.card Θ_top - GoodTop.card) * B) * Fintype.card Θ_top := by ring
      _ ≤ Fintype.card Θ_top * Fintype.card Θ_top := Nat.mul_le_mul_right _ hwhp
      _ = Fintype.card (Θ_top × Θ_top) := (Fintype.card_prod Θ_top Θ_top).symm
  have hcard_all :
      Fintype.card (Θ_top × Θ_top) * Fintype.card (Θ_bot × Θ_bot) =
        Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)) := by
    simp only [Fintype.card_prod]
    ring
  refine ⟨fun S u hS hu => ?_, fun S hS => ?_, fun ks u hnodup hlen hu => ?_⟩
  · have hloop_le_B : MaxLoop ≤ B :=
      calc MaxLoop = 1 * MaxLoop := (one_mul MaxLoop).symm
        _ ≤ max n_max 1 * max MaxLoop 1 := Nat.mul_le_mul (by omega) (by omega)
    have hBad_loop : BadPair.card * MaxLoop ≤ Fintype.card (Θ_top × Θ_top) :=
      le_trans (Nat.mul_le_mul_left _ hloop_le_B) hBad_B
    have hsum := sum_prodProd_le_of_goodTop GoodTop
      (fun θ => cuckooWalkRounds (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S u)
      (fun α₁ hα₁ α₂ hα₂ => sum_cuckooWalkRounds_le (hk α₁ hα₁) (hk α₂ hα₂) hm hloop_le hS hu)
      (fun θ => cuckooWalkRounds_le_maxLoop (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S u)
    have hsum3 :
        ∑ θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot),
          cuckooWalkRounds (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S u ≤
        3 * Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)) := by
      calc _ ≤ (2 * Fintype.card (Θ_top × Θ_top) + BadPair.card * MaxLoop) *
            Fintype.card (Θ_bot × Θ_bot) := hsum
        _ ≤ (2 * Fintype.card (Θ_top × Θ_top) + Fintype.card (Θ_top × Θ_top)) *
            Fintype.card (Θ_bot × Θ_bot) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left hBad_loop _)
        _ = 3 * Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)) := by
          rw [← hcard_all]
          ring
    exact mod_cast PMF.tsum_uniformOfFintype_le_of_sum_le hsum3
  · have h4_le_B : 4 ≤ B :=
      calc 4 ≤ 1 * 18 := by decide
        _ ≤ max n_max 1 * max MaxLoop 1 := Nat.mul_le_mul (by omega) (by omega)
    have hBad_4 : BadPair.card * 4 ≤ Fintype.card (Θ_top × Θ_top) :=
      le_trans (Nat.mul_le_mul_left _ h4_le_B) hBad_B
    have hfilt := card_filter_prodProd_le_of_goodTop GoodTop
      (fun θ => ¬ GoodForSet (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S)
      (K := 4) (A_good := 1)
      (fun α₁ hα₁ α₂ hα₂ => by
        simpa only [one_mul] using
          four_mul_card_not_goodForSet_le (hk α₁ hα₁) (hk α₂ hα₂) hm hloop_ge hloop_le hS)
    have hfilt2 :
        2 * (Finset.univ.filter fun θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot) =>
          ¬ GoodForSet (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S).card ≤
        1 * Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)) := by
      have hfilt4 :
          2 * (2 * (Finset.univ.filter fun θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot) =>
            ¬ GoodForSet (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S).card) ≤
          2 * (1 * Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot))) := by
        calc 2 * (2 * _) = 4 * _ := by ring
          _ ≤ (1 * Fintype.card (Θ_top × Θ_top) + BadPair.card * 4) *
                Fintype.card (Θ_bot × Θ_bot) := hfilt
          _ ≤ (1 * Fintype.card (Θ_top × Θ_top) + Fintype.card (Θ_top × Θ_top)) *
                Fintype.card (Θ_bot × Θ_bot) :=
            Nat.mul_le_mul_right _ (Nat.add_le_add_left hBad_4 _)
          _ = 2 * (1 * Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot))) := by
            rw [← hcard_all]
            ring
      exact Nat.le_of_mul_le_mul_left hfilt4 (by decide)
    exact mod_cast PMF.toOuterMeasure_uniformOfFintype_le_div (by decide : 0 < 2) hfilt2
  · have hB_pos : 0 < B := Nat.mul_pos (by omega) (by omega)
    have hks_card : ks.toFinset.card ≤ max n_max 4 := by
      have := List.toFinset_card_le ks
      omega
    have hfilt := card_filter_prodProd_le_of_goodTop GoodTop
      (fun θ => (pureReplay (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop ks).isSome ∧
        (pureReplay (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop (ks ++ [u])).isNone)
      (K := B) (A_good := 3)
      (fun α₁ hα₁ α₂ hα₂ => by
        have hsub :
            Finset.univ.filter (fun β : Θ_bot × Θ_bot =>
              (pureReplay (H α₁ β.1) (H α₂ β.2) MaxLoop ks).isSome ∧
                (pureReplay (H α₁ β.1) (H α₂ β.2) MaxLoop (ks ++ [u])).isNone) ⊆
            Finset.univ.filter (fun β : Θ_bot × Θ_bot =>
              WalkBadAt (H α₁ β.1) (H α₂ β.2) ks.toFinset u MaxLoop) := by
          intro β hβ
          rw [Finset.mem_filter] at hβ ⊢
          exact ⟨Finset.mem_univ _, step_rehash_imp_walkBadAt (by omega) hnodup hu hβ.2⟩
        have hcard_le := Finset.card_le_card hsub
        have hwalk := two_mul_walkBadAt_maxLoop_le (hk α₁ hα₁) (hk α₂ hα₂)
          hm hloop_ge hloop_le hks_card u
        calc B * _ ≤ 2 * B * #{β : Θ_bot × Θ_bot |
              WalkBadAt (H α₁ β.1) (H α₂ β.2) ks.toFinset u MaxLoop} := by
              have := Nat.mul_le_mul_left B hcard_le
              nlinarith
          _ ≤ 3 * Fintype.card (Θ_bot × Θ_bot) := le_trans hwalk (by omega))
    have hfilt4 :
        B * (Finset.univ.filter fun θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot) =>
          (pureReplay (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop ks).isSome ∧
            (pureReplay (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop (ks ++ [u])).isNone).card ≤
        4 * Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)) := by
      calc _ ≤ (3 * Fintype.card (Θ_top × Θ_top) + BadPair.card * B) *
            Fintype.card (Θ_bot × Θ_bot) := hfilt
        _ ≤ (3 * Fintype.card (Θ_top × Θ_top) + Fintype.card (Θ_top × Θ_top)) *
            Fintype.card (Θ_bot × Θ_bot) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left hBad_B _)
        _ = 4 * Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)) := by
          rw [← hcard_all]
          ring
    have hmeas := PMF.toOuterMeasure_uniformOfFintype_le_div hB_pos hfilt4
    have hmax (a : ℕ) : ((max a 1 : ℕ) : ℝ≥0∞) = max (a : ℝ≥0∞) 1 := by
      rcases le_total a 1 with h | h
      · rw [max_eq_right h, max_eq_right (by exact_mod_cast h), Nat.cast_one]
      · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]
    have hB_cast : (B : ℝ≥0∞) = max (n_max : ℝ≥0∞) 1 * max (MaxLoop : ℝ≥0∞) 1 := by
      dsimp only [B]
      rw [Nat.cast_mul, hmax, hmax]
    rw [hB_cast] at hmeas
    exact mod_cast hmeas

/-- **`IsCuckooHashPair` for Mikkel Thorup's Double Tabulation (`[Thorup2013]`, Theorem 1(a),
p. 4)**:
When `1 ≤ c`, `U ≤ 2 ^ (c * b)`, `32 * max n_max 4 ≤ 2 ^ M`,
`maxEvictions n_max ≤ MaxLoop ≤ 2 ^ M`, and
`2 * (max n_max 1 * max MaxLoop 1) * doubleTabCodeBound c (8 * c) 4 (2 * MaxLoop + 2) ≤`
`2 ^ (3 * b)`,
two independent draws from `DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M` satisfy
`IsCuckooHashPair` with constants `C_walk = 3` and `C_reh = 4`. -/
theorem isCuckooHashPair_doubleTabHash {c b U M : ℕ}
    (hc : 1 ≤ c) (hU : U ≤ 2 ^ (c * b))
    (n_max MaxLoop : ℕ)
    (hm : 32 * max n_max 4 ≤ 2 ^ M)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ 2 ^ M)
    (hbound : 2 * (max n_max 1 * max MaxLoop 1) *
      doubleTabCodeBound c (8 * c) 4 (2 * MaxLoop + 2) ≤ 2 ^ (3 * b)) :
    IsCuckooHashPair
      (PMF.uniformOfFintype
        ((DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M) ×
         (DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M)))
      (fun ((top₁, bottom₁), _) => doubleTabHash c (8 * c) b U M top₁ bottom₁)
      (fun (_, (top₂, bottom₂)) => doubleTabHash c (8 * c) b U M top₂ bottom₂)
      n_max MaxLoop 3 4 := by
  classical
  let k := 2 * MaxLoop + 2
  let GoodTop := Finset.univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b =>
    IsKUnique k (simpleTabTuple T₁)
  let BadTop := Finset.univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b =>
    ¬ IsKUnique k (simpleTabTuple T₁)
  let B := max n_max 1 * max MaxLoop 1
  let Code := doubleTabCodeBound c (8 * c) 4 k
  let N_top := Fintype.card (DoubleTabTopSeed c (8 * c) b)
  have hB_ge : 1 ≤ B := Nat.mul_pos (by omega) (by omega)
  have hbound_code : 2 * Code ≤ 2 ^ (3 * b) := by
    calc 2 * Code = 2 * 1 * Code := by ring
      _ ≤ 2 * B * Code := Nat.mul_le_mul_right Code (Nat.mul_le_mul_left 2 hB_ge)
      _ ≤ 2 ^ (3 * b) := hbound
  have hbad_le := card_not_isKUnique_eight_mul_le (b := b) hc hbound_code
  have hsub_card : N_top - GoodTop.card = BadTop.card := by
    have hdisj : Disjoint GoodTop BadTop :=
      Finset.disjoint_filter.mpr fun _ _ h₁ h₂ => h₂ h₁
    have hunion : GoodTop ∪ BadTop = Finset.univ := by
      ext T₁
      simp only [GoodTop, BadTop, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      exact em _
    have hadd : GoodTop.card + BadTop.card = N_top := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    omega
  have hwhp : 2 * (N_top - GoodTop.card) * B ≤ N_top := by
    rw [hsub_card]
    have hmul : 2 ^ (6 * b) * (2 * BadTop.card * B) ≤ 2 ^ (6 * b) * N_top := by
      calc 2 ^ (6 * b) * (2 * BadTop.card * B)
          = (2 * B) * (2 ^ (6 * b) * BadTop.card) := by ring
        _ ≤ (2 * B) * (2 * Code ^ 2 * N_top) := Nat.mul_le_mul_left _ hbad_le
        _ = (2 * B * (2 * Code ^ 2)) * N_top := by ring
        _ ≤ (2 * B * Code) ^ 2 * N_top := by
          refine Nat.mul_le_mul_right N_top ?_
          have hB_sq : B ≤ B * B := Nat.le_mul_of_pos_left B hB_ge
          nlinarith
        _ ≤ (2 ^ (3 * b)) ^ 2 * N_top :=
          Nat.mul_le_mul_right N_top (Nat.pow_le_pow_left hbound 2)
        _ = 2 ^ (6 * b) * N_top := by
          rw [← Nat.pow_mul]
          congr 2
          ring
    exact Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos (6 * b))
  exact isCuckooHashPair_of_whp_kWiseIndependent n_max MaxLoop GoodTop
    (fun T₁ hT₁ => isKWiseIndependentHash_doubleTabHash_of_isKUnique hU
      (Finset.mem_filter.mp hT₁).2)
    hwhp hm hloop_ge hloop_le

/-- Regime-indexed seed space for `ProvableHashSeed`. -/
@[expose] def ProvableHashSeedAux (reg : Bool) (c_exp n_max U M : ℕ) : Type :=
  match reg with
  | true =>
    let k := 2 * maxEvictions n_max + 2
    (Fin k → Fin (2 ^ (2 * 3 ^ trinomialStep U M))) ×
      (Fin k → Fin (2 ^ (2 * 3 ^ trinomialStep U M)))
  | false =>
    let c := 2 * max c_exp 1
    let b := (1 + Nat.clog 2 (max n_max 4)) / 2
    (DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M) ×
      (DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M)

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    Fintype (ProvableHashSeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [ProvableHashSeedAux] <;> infer_instance

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    Nonempty (ProvableHashSeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [ProvableHashSeedAux] <;> infer_instance

/-- Regime-indexed first hash function for `provableHash1`. -/
@[expose] noncomputable def provableHash1Aux (reg : Bool) (c_exp n_max U M : ℕ) :
    ProvableHashSeedAux reg c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  match reg with
  | true => fun (seed₁, _) =>
    trinomialPolyHash (trinomialStep U M) (2 * maxEvictions n_max + 2) U M seed₁
  | false => fun ((top₁, bottom₁), _) =>
    let c := 2 * max c_exp 1
    let b := (1 + Nat.clog 2 (max n_max 4)) / 2
    doubleTabHash c (8 * c) b U M top₁ bottom₁

/-- Regime-indexed second hash function for `provableHash2`. -/
@[expose] noncomputable def provableHash2Aux (reg : Bool) (c_exp n_max U M : ℕ) :
    ProvableHashSeedAux reg c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  match reg with
  | true => fun (_, seed₂) =>
    trinomialPolyHash (trinomialStep U M) (2 * maxEvictions n_max + 2) U M seed₂
  | false => fun (_, (top₂, bottom₂)) =>
    let c := 2 * max c_exp 1
    let b := (1 + Nat.clog 2 (max n_max 4)) / 2
    doubleTabHash c (8 * c) b U M top₂ bottom₂

/-- Seed space for the unconditional regime-switched cuckoo hash family (`trinomialPolyHash` below
`doubleTabThreshold c_exp`, `doubleTabHash` at or above `doubleTabThreshold c_exp`). -/
abbrev ProvableHashSeed (c_exp n_max U M : ℕ) : Type :=
  ProvableHashSeedAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

/-- First hash function of the unconditional regime-switched cuckoo hash family. -/
@[expose] noncomputable def provableHash1 (c_exp n_max U M : ℕ) :
    ProvableHashSeed c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  provableHash1Aux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

/-- Second hash function of the unconditional regime-switched cuckoo hash family. -/
@[expose] noncomputable def provableHash2 (c_exp n_max U M : ℕ) :
    ProvableHashSeed c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  provableHash2Aux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

private theorem maxEvictions_le_thirtyTwo_mul_max (n_max : ℕ) :
    maxEvictions n_max ≤ 32 * max n_max 4 := by
  have hclog : Nat.clog 2 (max n_max 2) ≤ max n_max 2 :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.le_of_lt (max n_max 2).lt_two_pow_self)
  unfold maxEvictions
  omega

/-- **Unconditional `IsCuckooHashPair` for the regime-switched hash family (`trinomialPolyHash` +
`doubleTabHash`) across all capacities `n_max : ℕ` and polynomial universes
`U ≤ max n_max 4 ^ c_exp`**:
Whenever `U ≤ max n_max 4 ^ c_exp` and `32 * max n_max 4 ≤ 2 ^ M`, the uniform distribution on
`ProvableHashSeed c_exp n_max U M` with `(provableHash1, provableHash2)` satisfies
`IsCuckooHashPair ... n_max (maxEvictions n_max) 3 4`. -/
theorem isCuckooHashPair_provableFamily {c_exp n_max U M : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M) :
    IsCuckooHashPair
      (PMF.uniformOfFintype (ProvableHashSeed c_exp n_max U M))
      (provableHash1 c_exp n_max U M)
      (provableHash2 c_exp n_max U M)
      n_max (maxEvictions n_max) 3 4 := by
  have hloop_le : maxEvictions n_max ≤ 2 ^ M :=
    (maxEvictions_le_thirtyTwo_mul_max n_max).trans hm
  unfold ProvableHashSeed provableHash1 provableHash2
  cases hreg : decide (n_max < doubleTabThreshold c_exp)
  · dsimp only [ProvableHashSeedAux, provableHash1Aux, provableHash2Aux]
    have hge : doubleTabThreshold c_exp ≤ n_max :=
      not_lt.mp (of_decide_eq_false hreg)
    let c := 2 * max c_exp 1
    let b := (1 + Nat.clog 2 (max n_max 4)) / 2
    have hc2 : 2 ≤ c := by omega
    have hclog_le : Nat.clog 2 (max n_max 4) ≤ 2 * b := by omega
    have hmax_le_2b : max n_max 4 ≤ 2 ^ (2 * b) :=
      (Nat.le_pow_clog (by decide) (max n_max 4)).trans
        (Nat.pow_le_pow_right (by decide) hclog_le)
    have hU_cb : U ≤ 2 ^ (c * b) := by
      calc U ≤ max n_max 4 ^ c_exp := hU
        _ ≤ max n_max 4 ^ max c_exp 1 :=
          Nat.pow_le_pow_right (by omega) (le_max_left c_exp 1)
        _ ≤ (2 ^ (2 * b)) ^ max c_exp 1 :=
          Nat.pow_le_pow_left hmax_le_2b (max c_exp 1)
        _ = 2 ^ (c * b) := by
          rw [← Nat.pow_mul]
          congr 1
          dsimp only [c]
          ring
    have hb_ge : doubleTabMinB c_exp ≤ b := by
      have hpow_le : 2 ^ (2 * doubleTabMinB c_exp) ≤ 2 ^ Nat.clog 2 (max n_max 4) := by
        rw [← doubleTabThreshold_eq]
        exact (hge.trans (le_max_left n_max 4)).trans (Nat.le_pow_clog (by decide) (max n_max 4))
      have hclog_ge : 2 * doubleTabMinB c_exp ≤ Nat.clog 2 (max n_max 4) :=
        (Nat.pow_le_pow_iff_right (by decide)).mp hpow_le
      omega
    have hb_min_def : doubleTabMinB c_exp = 4 * (24 * c + 8) ^ 2 := doubleTabMinB_eq c_exp
    have hb_8c : 8 * c ≤ b := by nlinarith
    have hb_64 : 64 ≤ b := by nlinarith
    have hclog2_le : Nat.clog 2 (max n_max 2) ≤ 2 * b :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr
        ((by omega : max n_max 2 ≤ max n_max 4).trans hmax_le_2b)
    have hev_le : maxEvictions n_max ≤ 12 * b + 12 := by
      unfold maxEvictions
      omega
    have h18_ev : 18 ≤ maxEvictions n_max := eighteen_le_maxEvictions n_max
    have h2ev_sq : 2 * max (maxEvictions n_max) 1 ≤ b ^ 2 := by
      have : max (maxEvictions n_max) 1 = maxEvictions n_max := by omega
      nlinarith
    have hck_cube : c * (2 * maxEvictions n_max + 2) ≤ b ^ 3 := by
      have h2ev2 : 2 * maxEvictions n_max + 2 ≤ b ^ 2 := by nlinarith
      calc c * (2 * maxEvictions n_max + 2)
          ≤ b * (b ^ 2) := Nat.mul_le_mul (by omega) h2ev2
        _ = b ^ 3 := by ring
    have hcode_pow : doubleTabCodeBound c (8 * c) 4 (2 * maxEvictions n_max + 2) ≤
        b ^ (24 * c + 5) := by
      unfold doubleTabCodeBound
      calc c * ((c * (2 * maxEvictions n_max + 2)) ^ (2 * c) * (8 * c)) ^ 4
          ≤ b * (((b ^ 3) ^ (2 * c) * b) ^ 4) :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left
              (Nat.mul_le_mul (Nat.pow_le_pow_left hck_cube (2 * c)) hb_8c) 4)
        _ = b ^ (24 * c + 5) := by
          rw [← Nat.pow_mul, ← pow_succ, ← Nat.pow_mul, ← pow_succ']
          congr 1
          ring
    have hprod_le : 2 * (max n_max 1 * max (maxEvictions n_max) 1) *
        doubleTabCodeBound c (8 * c) 4 (2 * maxEvictions n_max + 2) ≤ 2 ^ (3 * b) := by
      have hmax1_le : max n_max 1 ≤ 2 ^ (2 * b) :=
        (by omega : max n_max 1 ≤ max n_max 4).trans hmax_le_2b
      calc 2 * (max n_max 1 * max (maxEvictions n_max) 1) *
            doubleTabCodeBound c (8 * c) 4 (2 * maxEvictions n_max + 2)
          = max n_max 1 * (2 * max (maxEvictions n_max) 1) *
              doubleTabCodeBound c (8 * c) 4 (2 * maxEvictions n_max + 2) := by ring
        _ ≤ (2 ^ (2 * b) * b ^ 2) * b ^ (24 * c + 5) :=
            Nat.mul_le_mul (Nat.mul_le_mul hmax1_le h2ev_sq) hcode_pow
        _ = 2 ^ (2 * b) * b ^ (24 * c + 7) := by
            rw [Nat.mul_assoc, ← Nat.pow_add]
            congr 2
            ring
        _ ≤ 2 ^ (2 * b) * b ^ (24 * c + 8) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        _ ≤ 2 ^ (2 * b) * 2 ^ b :=
            Nat.mul_le_mul_left _ (Nat.pow_le_two_pow (by omega) (hb_min_def ▸ hb_ge))
        _ = 2 ^ (3 * b) := by
            rw [← Nat.pow_add]
            congr 1
            ring
    exact isCuckooHashPair_doubleTabHash (by omega) hU_cb n_max (maxEvictions n_max)
      hm le_rfl hloop_le hprod_le
  · dsimp only [ProvableHashSeedAux, provableHash1Aux, provableHash2Aux]
    exact (isCuckooHashPair_trinomialPolyHash (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M)
      n_max (maxEvictions n_max) le_rfl hm le_rfl hloop_le).mono_consts (by decide) (by decide)

end Cslib.Algorithms.Lean.CuckooHashing

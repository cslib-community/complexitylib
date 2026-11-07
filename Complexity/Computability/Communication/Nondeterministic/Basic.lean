/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.FoolingSet
public import Complexity.Computability.Communication.Rectangle
public import Complexity.Foundations.Data.BitString.Basic

/-!
# Nondeterministic communication complexity

Nondeterministic communication complexity for the answer `z : Bool` is defined by covers
[Kushilevitz and Nisan, Definition 2.3, p. 18][KushilevitzNisan1997]. For a relation
`R : X → Y → Bool → Prop`, a *`z`-cover* of `R` on `A × B` by `2 ^ k` rectangles is a family of
rectangles indexed by the `k`-bit guesses such that `z` is an acceptable answer on the part of each
rectangle inside `A × B`, and every pair of `A × B` on which `!z` is not acceptable lies in some
rectangle (`Nondeterministic.IsCover`). The complexity `Nondeterministic.ecomplexity z R A B` is the
least such `k`, or `⊤` if there is none; in particular it is `⊤` if no answer is acceptable on some
pair of `A × B`, as for `Protocol.ecomplexity`. For a function `f : X → Y → Bool`,
`Nondeterministic.ecomplexityFun z f A B` is the complexity of the relation `f x y = b`; its
`z`-covers are families of rectangles on which `f` is `z` inside `A × B` that contain every pair of
`A × B` on which `f` is `z` (`Nondeterministic.isCover_fun_iff`). Thus `ecomplexityFun true f` and
`ecomplexityFun false f` are `⌈log₂ C^z(f)⌉`, where `C^z(f)` is the least number of rectangles in a
`z`-cover [Kushilevitz and Nisan, Definition 2.1(4), p. 17][KushilevitzNisan1997] (and `0` when `f`
never takes the value `z` on `A × B`).

Kushilevitz and Nisan define `N^z(f) = log₂ C^z(f)` for a Boolean function `f` on all of `X × Y`,
without rounding. So for such `f`, `ecomplexityFun z f Set.univ Set.univ` is their `N^z(f)` rounded
up to an integer, and for `n ≥ 1` a lower bound `n ≤ ecomplexityFun z f Set.univ Set.univ` says
`C^z(f) > 2 ^ (n - 1)`, that is, `N^z(f) > n - 1` in their convention.

The model here lies between the total Boolean functions of their Definition 2.1 and the relations
with arbitrary answers of [Kushilevitz and Nisan, Chapter 5][KushilevitzNisan1997]: it covers
partial Boolean functions, which are relations with Boolean answers. For these it is the model NP of
[Göös, Pitassi and Watson, Definition B.1][GoosPitassiWatson2018Landscape]
([author copy](https://par.nsf.gov/servlets/purl/10090758), p. 44): a collection of
`2 ^ k` rectangles indexed by `k`-bit witnesses, whose output is `1` exactly on their union, correct
on the domain of the function, of cost `k`; co-classes are defined by negating the function. A
partial function is a function together with the sets `A` and `B`, or, when its domain is not a
rectangle, a relation that accepts both answers outside its domain; its values there do not matter,
and rectangles are not required to lie inside the domain. Kushilevitz and Nisan remark after
Definition 5.2 that for relations, measures such as `N¹(R)` are less interesting, since the answer
`1` has no special role; with Boolean answers, `N⁰` and `N¹` keep their meaning.

A relation `R : X → Y → Bool → Prop` is their relation `R ⊆ X × Y × Z` with `Z = Bool`
[Kushilevitz and Nisan, Definition 5.1, p. 71][KushilevitzNisan1997]: `R x y b` holds exactly when
`(x, y, b) ∈ R`. A partial Boolean function `f` with domain `D` is the relation
`fun x y b => (x, y) ∈ D → f x y = b`. Kushilevitz and Nisan require a protocol for a relation to be
correct only on legal inputs, those with some acceptable answer, and define the other measures for
relations "in a similar manner"
[Kushilevitz and Nisan, Definition 5.2, p. 71][KushilevitzNisan1997]. Here, as for
`Protocol.ecomplexity`, which is stated for relations, every pair of `A × B` must get an acceptable
answer, so a pair of `A × B` with no acceptable answer makes the complexity `⊤`. Just before
Definition 5.2 they note the alternative of extending a relation to allow every answer on its
illegal pairs; their convention for `R` is this one for that extension, which is no harder than `R`
(`Nondeterministic.ecomplexity_le_of_imp`).

## Covers and protocols

Covers count rectangles; no bits are spent announcing the answer. Protocols must announce it, and
conventions differ on who must learn it. In `Protocol` the answer is a function of the transcript,
so both players know it; for instance, equality on `v`-bit strings has deterministic complexity
`v + 1` for `v ≥ 1` (`Cslib.Communication.ecomplexityFun_equality`). For nondeterministic protocols
in the same convention, where the guessed bits count towards the cost and at the end both players
know whether to accept, the two notions differ by at most two bits:

* a protocol of cost `c` gives a cover by at most `2 ^ c` rectangles, one for each accepting
  transcript, so a lower bound on `ecomplexity` is a lower bound for protocols, whatever the
  convention for announcing the answer;
* a cover by `2 ^ k` rectangles gives a protocol of cost `k + 2`: the `k` guessed bits name a
  rectangle, and Alice and Bob each send one bit saying whether their input lies in its side. If
  only one player needs to learn the answer, Bob need not reply, and the cost is `k + 1`.

So `ecomplexity z R A B ≤ k` gives a protocol of cost `k + 2`, and a protocol of cost `c`, once
converted to a cover, gives `ecomplexity z R A B ≤ c` (`Nondeterministic.ecomplexity_le_iff`).
Deterministic protocols give covers directly (`Nondeterministic.ecomplexity_le_protocol`).

## Main definitions

* `Cslib.Communication.Nondeterministic.IsCover`, `Cslib.Communication.Nondeterministic.HasCover`:
  covers of a relation by rectangles.
* `Cslib.Communication.Nondeterministic.ecomplexity`: nondeterministic communication complexity of a
  relation on `A × B` for the answer `z`.
* `Cslib.Communication.Nondeterministic.ecomplexityFun`: the same for a function, as the relation
  `f x y = b`.

## Main results

* `Cslib.Communication.Nondeterministic.ecomplexity_le_iff`,
  `Cslib.Communication.Nondeterministic.le_ecomplexity_iff`,
  `Cslib.Communication.Nondeterministic.HasCover.ecomplexity_le`: upper and lower bounds through
  covers; `Cslib.Communication.Nondeterministic.ecomplexityFun_le_iff` and
  `Cslib.Communication.Nondeterministic.le_ecomplexityFun_iff` for functions.
* `Cslib.Communication.Nondeterministic.isCover_fun_iff`: covers of a function.
* `Cslib.Communication.Nondeterministic.HasCover.mono_bits`: more guessed bits do no harm.
* `Cslib.Communication.Nondeterministic.HasCover.mono`,
  `Cslib.Communication.Nondeterministic.ecomplexity_mono`,
  `Cslib.Communication.Nondeterministic.ecomplexityFun_mono`: monotonicity in the domain.
* `Cslib.Communication.Nondeterministic.HasCover.of_imp`,
  `Cslib.Communication.Nondeterministic.ecomplexity_le_of_imp`: a weaker relation is no harder.
* `Cslib.Communication.Nondeterministic.ecomplexity_not`,
  `Cslib.Communication.Nondeterministic.ecomplexityFun_not`: `N⁰` is `N¹` of the negation.
* `Cslib.Communication.Nondeterministic.HasCover.card_le`,
  `Cslib.Communication.Nondeterministic.le_ecomplexityFun_of_isFoolingSet`: a fooling set of
  `2 ^ n` pairs with value `z` forces `n`.
* `Cslib.Communication.Nondeterministic.HasCover.card_le_two_pow_mul`: on a finite domain, if every
  `z`-rectangle has at most `K` pairs, then a `z`-cover by `2 ^ k` rectangles covers at most
  `2 ^ k * K` pairs.
* `Cslib.Communication.Protocol.Solves.hasCover`,
  `Cslib.Communication.Nondeterministic.ecomplexity_le_protocol`,
  `Cslib.Communication.Nondeterministic.ecomplexityFun_le_protocol`: nondeterministic complexity is
  at most deterministic complexity.

## References

* [M. Göös, T. Pitassi, T. Watson, *The Landscape of Communication Complexity
  Classes*][GoosPitassiWatson2018Landscape], Appendix B
* [E. Kushilevitz, N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

public section

namespace Cslib.Communication

namespace Nondeterministic

open Finset

variable {X Y : Type*}

/-- `C` is a `z`-cover of the relation `R` on `A × B` by `2 ^ k` rectangles: `z` is an acceptable
answer on the part of each rectangle inside `A × B`, and every pair of `A × B` on which `!z` is not
acceptable lies in some rectangle. -/
@[expose] def IsCover (z : Bool) (R : X → Y → Bool → Prop) (A : Set X) (B : Set Y) {k : ℕ}
    (C : BitString k → Set X × Set Y) : Prop :=
  (∀ w, ∀ x ∈ A, x ∈ (C w).1 → ∀ y ∈ B, y ∈ (C w).2 → R x y z) ∧
    ∀ x ∈ A, ∀ y ∈ B, ¬R x y (!z) → ∃ w, x ∈ (C w).1 ∧ y ∈ (C w).2

/-- The relation `R` has a `z`-cover on `A × B` by `2 ^ k` rectangles. -/
@[expose] def HasCover (z : Bool) (R : X → Y → Bool → Prop) (A : Set X) (B : Set Y) (k : ℕ) :
    Prop :=
  ∃ C : BitString k → Set X × Set Y, IsCover z R A B C

/-- The nondeterministic communication complexity of the relation `R` on `A × B` for the answer
`z`: the least `k` such that `R` has a `z`-cover on `A × B` by `2 ^ k` rectangles, or `⊤` if there
is none. -/
noncomputable def ecomplexity (z : Bool) (R : X → Y → Bool → Prop) (A : Set X) (B : Set Y) : ℕ∞ :=
  ⨅ k : {k : ℕ // HasCover z R A B k}, (k.1 : ℕ∞)

/-- The nondeterministic communication complexity of `f` on `A × B` for the value `z`:
`ecomplexity` of the relation `f x y = b`. `N¹` is `z = true`, and `N⁰` is `z = false`. -/
@[expose] noncomputable def ecomplexityFun (z : Bool) (f : X → Y → Bool) (A : Set X) (B : Set Y) :
    ℕ∞ :=
  ecomplexity z (fun x y b => f x y = b) A B

variable {R R' : X → Y → Bool → Prop} {f : X → Y → Bool} {z : Bool} {A A' : Set X} {B B' : Set Y}
  {j k : ℕ}

/-- A `z`-cover of a function: `f` is `z` on the part of each rectangle inside `A × B`, and every
pair of `A × B` on which `f` is `z` lies in some rectangle. -/
theorem isCover_fun_iff {C : BitString k → Set X × Set Y} :
    IsCover z (fun x y b => f x y = b) A B C ↔
      (∀ w, ∀ x ∈ A, x ∈ (C w).1 → ∀ y ∈ B, y ∈ (C w).2 → f x y = z) ∧
        ∀ x ∈ A, ∀ y ∈ B, f x y = z → ∃ w, x ∈ (C w).1 ∧ y ∈ (C w).2 := by
  simp only [IsCover, Bool.eq_not, not_not]

/-! ### Upper and lower bounds -/

/-- A cover by `2 ^ k` rectangles bounds the complexity by `k`. -/
theorem HasCover.ecomplexity_le (h : HasCover z R A B k) : ecomplexity z R A B ≤ k :=
  iInf_le (fun k : {k : ℕ // HasCover z R A B k} => (k.1 : ℕ∞)) ⟨k, h⟩

/-- A cover by `2 ^ j` rectangles gives one by `2 ^ k` rectangles for `j ≤ k`: ignore the extra
guessed bits. -/
theorem HasCover.mono_bits (hjk : j ≤ k) (h : HasCover z R A B j) : HasCover z R A B k := by
  obtain ⟨C, hmem, hcov⟩ := h
  refine ⟨fun w => C fun i => w (Fin.castLE hjk i), fun w => hmem _, fun x hx y hy hR => ?_⟩
  obtain ⟨w, hw⟩ := hcov x hx y hy hR
  refine ⟨fun i => if hi : (i : ℕ) < j then w ⟨i, hi⟩ else false, ?_⟩
  simpa using hw

/-- Lower bounds on nondeterministic complexity are lower bounds on the number of guessed bits of
every cover. -/
theorem le_ecomplexity_iff {c : ℕ∞} :
    c ≤ ecomplexity z R A B ↔ ∀ k, HasCover z R A B k → c ≤ k := by
  simp [ecomplexity, le_iInf_iff, Subtype.forall]

/-- `R` has nondeterministic complexity at most `k` exactly when it has a `z`-cover by `2 ^ k`
rectangles. -/
theorem ecomplexity_le_iff : ecomplexity z R A B ≤ k ↔ HasCover z R A B k := by
  refine ⟨fun h => ?_, HasCover.ecomplexity_le⟩
  have : Nonempty {k : ℕ // HasCover z R A B k} := by
    rw [← ENat.iInf_natCast_ne_top]
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
  obtain ⟨⟨j, hj⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun k : {k : ℕ // HasCover z R A B k} => (k.1 : ℕ∞))
  exact hj.mono_bits (by exact_mod_cast (hmin.trans_le h : (j : ℕ∞) ≤ k))

/-- `ecomplexity_le_iff` for functions. -/
theorem ecomplexityFun_le_iff :
    ecomplexityFun z f A B ≤ k ↔ HasCover z (fun x y b => f x y = b) A B k :=
  ecomplexity_le_iff

/-- `le_ecomplexity_iff` for functions. -/
theorem le_ecomplexityFun_iff {c : ℕ∞} :
    c ≤ ecomplexityFun z f A B ↔ ∀ k, HasCover z (fun x y b => f x y = b) A B k → c ≤ k :=
  le_ecomplexity_iff

/-! ### Monotonicity -/

/-- A cover on `A × B` is a cover on any smaller domain. -/
theorem HasCover.mono (hA : A' ⊆ A) (hB : B' ⊆ B) (h : HasCover z R A B k) :
    HasCover z R A' B' k := by
  obtain ⟨C, hmem, hcov⟩ := h
  exact ⟨C, fun w x hx hxC y hy hyC => hmem w x (hA hx) hxC y (hB hy) hyC,
    fun x hx y hy hR => hcov x (hA hx) y (hB hy) hR⟩

/-- A cover of `R` is a cover of every weaker relation. -/
theorem HasCover.of_imp (hR : ∀ x y b, R x y b → R' x y b) (h : HasCover z R A B k) :
    HasCover z R' A B k := by
  obtain ⟨C, hmem, hcov⟩ := h
  exact ⟨C, fun w x hx hxC y hy hyC => hR x y z (hmem w x hx hxC y hy hyC),
    fun x hx y hy hR' => hcov x hx y hy fun h => hR' (hR x y _ h)⟩

/-- Nondeterministic complexity is monotone in the domain. -/
theorem ecomplexity_mono (hA : A' ⊆ A) (hB : B' ⊆ B) :
    ecomplexity z R A' B' ≤ ecomplexity z R A B :=
  le_ecomplexity_iff.mpr fun _ hk => (hk.mono hA hB).ecomplexity_le

/-- `ecomplexity_mono` for functions. -/
theorem ecomplexityFun_mono (hA : A' ⊆ A) (hB : B' ⊆ B) :
    ecomplexityFun z f A' B' ≤ ecomplexityFun z f A B :=
  ecomplexity_mono hA hB

/-- A weaker relation is no harder. -/
theorem ecomplexity_le_of_imp (hR : ∀ x y b, R x y b → R' x y b) :
    ecomplexity z R' A B ≤ ecomplexity z R A B :=
  le_ecomplexity_iff.mpr fun _ hk => (hk.of_imp hR).ecomplexity_le

/-! ### Negation -/

/-- Exchanging the answers exchanges `N⁰` and `N¹`. -/
theorem ecomplexity_not :
    ecomplexity z (fun x y b => R x y (!b)) A B = ecomplexity (!z) R A B := by
  have hiff : ∀ k, HasCover z (fun x y b => R x y (!b)) A B k ↔ HasCover (!z) R A B k := fun k => by
    simp only [HasCover, IsCover, Bool.not_not]
  exact le_antisymm (le_ecomplexity_iff.mpr fun k hk => ((hiff k).mpr hk).ecomplexity_le)
    (le_ecomplexity_iff.mpr fun k hk => ((hiff k).mp hk).ecomplexity_le)

/-- `N⁰` of `f` is `N¹` of its negation, and conversely. -/
@[simp] theorem ecomplexityFun_not :
    ecomplexityFun z (fun x y => !f x y) A B = ecomplexityFun (!z) f A B := by
  rw [ecomplexityFun, ecomplexityFun, ← ecomplexity_not]
  simp only [Bool.not_eq_eq_eq_not]

/-! ### Lower bounds -/

/-- **The fooling-set bound, for covers.** A fooling set for `f` with value `z` inside `A × B`
has at most `2 ^ k` pairs if `f` has a `z`-cover on `A × B` by `2 ^ k` rectangles: no rectangle
contains two of its pairs. -/
theorem HasCover.card_le {S : Finset (X × Y)} (hS : IsFoolingSet f z S)
    (hSAB : ∀ q ∈ S, q.1 ∈ A ∧ q.2 ∈ B) (h : HasCover z (fun x y b => f x y = b) A B k) :
    #S ≤ 2 ^ k := by
  classical
  obtain ⟨C, hC⟩ := h
  obtain ⟨hmem, hcov⟩ := isCover_fun_iff.mp hC
  have hw : ∀ q ∈ S, ∃ w, q.1 ∈ (C w).1 ∧ q.2 ∈ (C w).2 := fun q hq =>
    hcov _ (hSAB q hq).1 _ (hSAB q hq).2 (hS.1 q hq)
  choose! g hg using hw
  calc #S ≤ #(univ : Finset (BitString k)) := by
        refine card_le_card_of_injOn g (by intro _ _; exact mem_univ _) ?_
        intro q hq q' hq' hqq
        refine hS.2 q hq q' hq' ?_ ?_
        · exact hmem (g q) _ (hSAB q hq).1 (hg q hq).1 _ (hSAB q' hq').2
            (by rw [hqq]; exact (hg q' hq').2)
        · exact hmem (g q) _ (hSAB q' hq').1 (by rw [hqq]; exact (hg q' hq').1) _
            (hSAB q hq).2 (hg q hq).2
    _ = 2 ^ k := by rw [card_univ, BitString.card]

/-- **The fooling-set bound on nondeterministic complexity.** A fooling set of at least `2 ^ n`
pairs for `f` with value `z` inside `A × B` forces `n`. -/
theorem le_ecomplexityFun_of_isFoolingSet {S : Finset (X × Y)} (hS : IsFoolingSet f z S)
    (hSAB : ∀ q ∈ S, q.1 ∈ A ∧ q.2 ∈ B) {n : ℕ} (hn : 2 ^ n ≤ #S) :
    (n : ℕ∞) ≤ ecomplexityFun z f A B :=
  le_ecomplexityFun_iff.mpr fun _ hk => by
    have := hn.trans (hk.card_le hS hSAB)
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num)).mp this

/-- **The rectangle-size bound.** Let `s` and `t` be finite. If every rectangle inside `s × t` on
which `f` is constantly `z` has at most `K` pairs, then a `z`-cover of `f` on `s × t` by `2 ^ k`
rectangles covers at most `2 ^ k * K` pairs, so `f` is `z` on at most `2 ^ k * K` pairs of
`s × t`. -/
theorem HasCover.card_le_two_pow_mul {s : Finset X} {t : Finset Y} {K : ℕ}
    (hK : ∀ S ⊆ s, ∀ T ⊆ t, (∀ x ∈ S, ∀ y ∈ T, f x y = z) → #S * #T ≤ K)
    (h : HasCover z (fun x y b => f x y = b) s t k) :
    #{q ∈ s ×ˢ t | f q.1 q.2 = z} ≤ 2 ^ k * K := by
  classical
  obtain ⟨C, hC⟩ := h
  obtain ⟨hmem, hcov⟩ := isCover_fun_iff.mp hC
  let S : BitString k → Finset X := fun w => {x ∈ s | x ∈ (C w).1}
  let T : BitString k → Finset Y := fun w => {y ∈ t | y ∈ (C w).2}
  have hsub : {q ∈ s ×ˢ t | f q.1 q.2 = z} ⊆ univ.biUnion fun w => S w ×ˢ T w := by
    intro q hq
    simp only [mem_filter, mem_product] at hq
    obtain ⟨w, hx, hy⟩ := hcov q.1 hq.1.1 q.2 hq.1.2 hq.2
    simp only [mem_biUnion, mem_univ, true_and, mem_product, mem_filter, S, T]
    exact ⟨w, ⟨hq.1.1, hx⟩, hq.1.2, hy⟩
  calc #{q ∈ s ×ˢ t | f q.1 q.2 = z} ≤ #(univ.biUnion fun w => S w ×ˢ T w) := card_le_card hsub
    _ ≤ ∑ w, #(S w ×ˢ T w) := card_biUnion_le
    _ ≤ ∑ _w : BitString k, K := by
        refine sum_le_sum fun w _ => ?_
        rw [card_product]
        refine hK _ (filter_subset _ _) _ (filter_subset _ _) fun x hx y hy => ?_
        simp only [mem_filter, T] at hx hy
        exact hmem w x hx.1 hx.2 y hy.1 hy.2
    _ = 2 ^ k * K := by rw [sum_const, card_univ, BitString.card, smul_eq_mul]

/-! ### Comparison with deterministic complexity -/

/-- The leaves with output `z` of a deterministic protocol solving `R` on `A × B` form a `z`-cover
of `R` by `2 ^ depth` rectangles. -/
theorem _root_.Cslib.Communication.Protocol.Solves.hasCover {p : Protocol X Y Bool}
    (hp : p.Solves R A B) (z : Bool) :
    HasCover z R A B p.depth := by
  classical
  let e := BitString.equivFin p.depth
  refine ⟨fun w => if h : (e w : ℕ) < p.leafCount then
      if p.leafOutput ⟨e w, h⟩ = z then (p.leafAlice ⟨e w, h⟩, p.leafBob ⟨e w, h⟩) else (∅, ∅)
    else (∅, ∅), fun w x hxA hx y hyB hy => ?_, fun x hxA y hyB hR => ?_⟩
  · by_cases h : (e w : ℕ) < p.leafCount
    · by_cases hz : p.leafOutput ⟨e w, h⟩ = z
      · simp only [h, hz, dite_true, ite_true] at hx hy
        have := hp x hxA y hyB
        rwa [Protocol.run_eq_leafOutput hx hy, hz] at this
      · simp [h, hz] at hx
    · simp [h] at hx
  · have hlt : (p.leaf x y : ℕ) < 2 ^ p.depth :=
      (p.leaf x y).2.trans_le p.leafCount_le_two_pow_depth
    refine ⟨e.symm ⟨p.leaf x y, hlt⟩, ?_⟩
    have hrun : p.run x y = z := by
      have := hp x hxA y hyB
      cases hb : p.run x y <;> cases z <;> simp_all
    have hz : p.leafOutput (p.leaf x y) = z := by rw [← Protocol.run_eq_leafOutput_leaf, hrun]
    simp only [Equiv.apply_symm_apply, (p.leaf x y).2, dite_true, Fin.eta, hz, ite_true]
    exact ⟨Protocol.mem_leafAlice_leaf, Protocol.mem_leafBob_leaf⟩

/-- **Nondeterministic complexity is at most deterministic complexity.** -/
theorem ecomplexity_le_protocol (z : Bool) :
    ecomplexity z R A B ≤ Protocol.ecomplexity R A B :=
  le_iInf fun p => (p.2.hasCover z).ecomplexity_le

/-- `ecomplexity_le_protocol` for functions on all inputs. -/
theorem ecomplexityFun_le_protocol (z : Bool) :
    ecomplexityFun z f Set.univ Set.univ ≤ Protocol.ecomplexityFun f :=
  ecomplexity_le_protocol z

end Nondeterministic

end Cslib.Communication

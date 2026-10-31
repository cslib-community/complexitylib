/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.MCSP.Succinct
public import Complexity.Foundations.Data.BitString.Threshold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Anti-checkers

An *anti-checker* for a Boolean function `f` against a family `F` of Boolean functions is a set
`S` of inputs such that every member of `F` differs from `f` somewhere on `S` (`IsAntiChecker`)
[LiptonYoung1994], [OliveiraPichSanthanam2019, Section 4]. Against the functions with circuits
of at most `s` gates, `S` is an anti-checker for `f` exactly when `f` needs more than `s` gates on
`S` (`isAntiChecker_computableFunctions_iff`), that is, when the Succinct MCSP instance of the
values of `f` on `S` with threshold `s` is a no-instance.

Functions without small circuits have small anti-checkers. The combinatorial core is an
ordered-tuple variant of the good-string lemma of Oliveira, Pich and Santhanam
[OliveiraPichSanthanam2019, Section 4.2, Lemma 23, pp. 27:17–18]. Suppose there are at most
`2 ^ m` inputs, and no `m` members of `F`, repetitions allowed, have `f` as
their pointwise strict majority. Then every tuple of `m` members of a subfamily `G` is refuted by
at least half of its entries (at least `m - m / 2` of them) at some input; averaging over the
inputs, one input refutes a `2 ^ -m` share of all tuples, and counting the tuples with at least
half of their entries in the set of members refuted there shows that this set holds a sixteenth of
`G` (`exists_card_le_sixteen_mul`). Removing the refuted members and repeating, `16 b` inputs
refute every member of a family of fewer than `2 ^ b` (`exists_isAntiChecker`). Counting ordered
tuples gives the constant share `1 / 16` where the original counts sets and gets `1 / (2 m)`.

The indexed versions allow distinct descriptions to evaluate to the same Boolean function:
`exists_card_le_sixteen_mul_eval` counts descriptions, and `exists_card_filter_le_eval` bounds
the number of descriptions still consistent after sampling. Thus the counting statements apply
to circuit encodings without assuming their evaluation map is injective.

For circuits (`exists_lt_complexityOn`): the strict majority of `m` circuits with `s` gates each
has a circuit with `m s` gates plus those of a circuit for strict majority, so if `f` needs more
than that, then `f` needs more than `s` gates on some set of `16 b` inputs, for any `b` with
fewer than `2 ^ b` functions computable with `s` gates.

This is the existence of anti-checkers: the worst-case form of the theorem of Lipton and Young,
with an adaptation of the combinatorial proof of Oliveira, Pich and Santhanam. Their
Anti-Checker Lemma [OliveiraPichSanthanam2019, Section 4.1, Lemma 17], which computes an
anti-checker from the truth table by a small circuit if `NP ⊆ P/poly`, is not formalized here.

## Main definitions

* `Cslib.MCSP.IsAntiChecker`: anti-checkers against a family of Boolean functions.

## Main results

* `Cslib.MCSP.exists_card_le_sixteen_mul`: the good-string lemma.
* `Cslib.MCSP.exists_card_le_sixteen_mul_eval`: the good-string lemma counting descriptions.
* `Cslib.MCSP.exists_card_filter_le_eval`: geometric decay of the consistent description count.
* `Cslib.MCSP.exists_isAntiChecker`: small anti-checkers, combinatorially.
* `Cslib.MCSP.exists_isAntiChecker_image`: small anti-checkers against an indexed family.
* `Cslib.MCSP.isAntiChecker_computableFunctions_iff`,
  `Cslib.MCSP.isAntiChecker_computableFunctions_iff_notMem`: anti-checkers against circuits.
* `Cslib.MCSP.complexity_strictMajority_le`: circuit complexity of a pointwise majority.
* `Cslib.MCSP.exists_lt_complexityOn`, `Cslib.MCSP.exists_ofFunction_notMem`: small
  anti-checkers against circuits.

## References

* [R. J. Lipton, N. E. Young, *Simple strategies for large zero-sum games with applications to
  complexity theory*][LiptonYoung1994]
* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

@[expose] public section

namespace Cslib.MCSP

open Finset Circuits Circuits.Boolean

/-- `S` is an *anti-checker* for `f` against the family `F`: every member of `F` differs from `f`
at some input in `S`. -/
def IsAntiChecker {α : Type*} (F : Set (α → Bool)) (f : α → Bool) (S : Set α) : Prop :=
  ∀ g ∈ F, ∃ x ∈ S, g x ≠ f x

variable {α : Type*} [Fintype α] {m : ℕ}

/-! ### Counting refuting tuples -/

/-- Among the tuples of `m` members of `G`, at most `2 ^ m · |D| ^ h · |G| ^ (m - h)` have at
least `h` entries in `D`: choose `h` positions and fill them from `D`. -/
private theorem card_filter_le_card_mem_le {β : Type*} [DecidableEq β] {h : ℕ} (hm : h ≤ m)
    (G D : Finset β) :
    #{t ∈ Fintype.piFinset fun _ : Fin m => G | h ≤ #{i | t i ∈ D}} ≤
      2 ^ m * #D ^ h * #G ^ (m - h) := by
  classical
  calc #{t ∈ Fintype.piFinset fun _ : Fin m => G | h ≤ #{i | t i ∈ D}}
      ≤ #((powersetCard h univ).biUnion fun J =>
          Fintype.piFinset fun i : Fin m => if i ∈ J then D else G) := by
        refine card_le_card fun t ht => ?_
        obtain ⟨htT, hcard⟩ := mem_filter.mp ht
        obtain ⟨J, hJ, rfl⟩ := exists_subset_card_eq hcard
        refine mem_biUnion.mpr ⟨J, mem_powersetCard.mpr ⟨subset_univ J, rfl⟩,
          Fintype.mem_piFinset.mpr fun i => ?_⟩
        split_ifs with hi
        · exact (mem_filter.mp (hJ hi)).2
        · exact Fintype.mem_piFinset.mp htT i
    _ ≤ ∑ J ∈ powersetCard h univ, #(Fintype.piFinset fun i : Fin m => if i ∈ J then D else G) :=
        card_biUnion_le
    _ = ∑ _J ∈ powersetCard h (univ : Finset (Fin m)), #D ^ h * #G ^ (m - h) := by
        refine sum_congr rfl fun J hJ => ?_
        rw [mem_powersetCard] at hJ
        rw [Fintype.card_piFinset]
        simp only [apply_ite card, prod_ite, prod_const, filter_mem_eq_inter, univ_inter, hJ.2]
        rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset hJ.1, hJ.2,
          card_univ, Fintype.card_fin]
    _ ≤ 2 ^ m * #D ^ h * #G ^ (m - h) := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow m h)

/-- **The good-string lemma for an indexed family**, using the tuple-counting variant of
[OliveiraPichSanthanam2019, Section 4.2, Lemma 23]. Suppose there are at most `2 ^ m` inputs and
no `m` members of the nonempty description family `G` evaluate to functions with pointwise strict
majority `f`. Then some input refutes at least a sixteenth of the descriptions in `G`.
The evaluation map need not be injective: distinct descriptions are counted separately. -/
theorem exists_card_le_sixteen_mul_eval {β : Type*} (eval : β → α → Bool)
    (hm : 0 < m) (hα : Fintype.card α ≤ 2 ^ m)
    {G : Finset β} (hG : G.Nonempty) {f : α → Bool}
    (hmaj : ∀ g : Fin m → β, (∀ i, g i ∈ G) →
      (fun x => strictMajority m fun i => eval (g i) x) ≠ f) :
    ∃ x, #G ≤ 16 * #{g ∈ G | eval g x ≠ f x} := by
  classical
  by_contra! hx
  obtain ⟨g₀, hg₀⟩ := hG
  obtain ⟨x₀, -⟩ := Function.ne_iff.mp (hmaj (fun _ => g₀) fun _ => hg₀)
  set r := #G
  set h := m - m / 2
  have hr : 0 < r := card_pos.mpr ⟨g₀, hg₀⟩
  have hh : 0 < h := by omega
  set T := Fintype.piFinset fun _ : Fin m => G
  -- Every tuple is refuted by at least half of its entries at some input.
  have hcover : T ⊆ univ.biUnion fun x =>
      {t ∈ T | h ≤ #{i | t i ∈ {g ∈ G | eval g x ≠ f x}}} := by
    intro t ht
    have htG := Fintype.mem_piFinset.mp ht
    obtain ⟨x, hx⟩ := Function.ne_iff.mp (hmaj t htG)
    refine mem_biUnion.mpr ⟨x, mem_univ x, mem_filter.mpr ⟨ht, ?_⟩⟩
    convert le_card_ne_of_strictMajority_ne hx using 2
    ext i
    simp [htG i]
  have hcount : r ^ m * 16 ^ h ≤
      ∑ x : α, 2 ^ m * (16 ^ h * #{g ∈ G | eval g x ≠ f x} ^ h) * r ^ (m - h) := by
    calc r ^ m * 16 ^ h = #T * 16 ^ h := by simp [T, r]
      _ ≤ (∑ x : α, #{t ∈ T | h ≤ #{i | t i ∈ {g ∈ G | eval g x ≠ f x}}}) * 16 ^ h :=
          Nat.mul_le_mul_right _ ((card_le_card hcover).trans card_biUnion_le)
      _ ≤ (∑ x : α, 2 ^ m * #{g ∈ G | eval g x ≠ f x} ^ h * r ^ (m - h)) * 16 ^ h :=
          Nat.mul_le_mul_right _ (sum_le_sum fun x _ =>
            card_filter_le_card_mem_le (by omega) _ _)
      _ = ∑ x : α, 2 ^ m * (16 ^ h * #{g ∈ G | eval g x ≠ f x} ^ h) * r ^ (m - h) := by
          rw [sum_mul]; exact sum_congr rfl fun x _ => by ring
  -- But at each input fewer than a sixteenth of `G` is refuted.
  have hlt : ∑ x : α, 2 ^ m * (16 ^ h * #{g ∈ G | eval g x ≠ f x} ^ h) * r ^ (m - h) <
      ∑ _x : α, 2 ^ m * r ^ h * r ^ (m - h) := by
    refine sum_lt_sum_of_nonempty ⟨x₀, mem_univ _⟩ fun x _ => ?_
    have := Nat.pow_lt_pow_left (hx x) hh.ne'
    rw [mul_pow] at this
    gcongr
  have hfour : Fintype.card α * 2 ^ m ≤ 16 ^ h := by
    calc Fintype.card α * 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ hα
      _ = 4 ^ m := by rw [← mul_pow]; norm_num
      _ ≤ 4 ^ (2 * h) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 ^ h := by rw [pow_mul]; norm_num
  have : ∑ _x : α, 2 ^ m * r ^ h * r ^ (m - h) ≤ r ^ m * 16 ^ h := by
    rw [sum_const, card_univ, smul_eq_mul, mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega),
      ← mul_assoc, mul_comm (r ^ m)]
    exact Nat.mul_le_mul_right _ hfour
  omega

/-- **The good-string lemma**, in the ordered-tuple variant of
[OliveiraPichSanthanam2019, Section 4.2, Lemma 23]. Suppose there are at most `2 ^ m` inputs and
no `m` members of the nonempty family `G` have `f` as their pointwise strict majority. Then at
some input `x`, at least a sixteenth of the members of `G` differ from `f`. -/
theorem exists_card_le_sixteen_mul (hm : 0 < m) (hα : Fintype.card α ≤ 2 ^ m)
    {G : Finset (α → Bool)} (hG : G.Nonempty) {f : α → Bool}
    (hmaj : ∀ g : Fin m → α → Bool, (∀ i, g i ∈ G) →
      (fun x => strictMajority m fun i => g i x) ≠ f) :
    ∃ x, #G ≤ 16 * #{g ∈ G | g x ≠ f x} :=
  exists_card_le_sixteen_mul_eval id hm hα hG hmaj

/-! ### Small anti-checkers -/

/-- Greedily choosing inputs by the indexed good-string lemma, at most `k` inputs leave at most
a `(15 / 16) ^ k` share of the descriptions in `F` agreeing with `f` on all of them. Distinct
descriptions are counted separately even when they evaluate to the same function. -/
theorem exists_card_filter_le_eval {β : Type*} (eval : β → α → Bool)
    (hm : 0 < m) (hα : Fintype.card α ≤ 2 ^ m)
    (F : Finset β) {f : α → Bool}
    (hmaj : ∀ g : Fin m → β, (∀ i, g i ∈ F) →
      (fun x => strictMajority m fun i => eval (g i) x) ≠ f) (k : ℕ) :
    ∃ S : Finset α, #S ≤ k ∧
      16 ^ k * #{g ∈ F | ∀ x ∈ S, eval g x = f x} ≤ 15 ^ k * #F := by
  induction k with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨S, hS, hcard⟩ := ih
    set G := {g ∈ F | ∀ x ∈ S, eval g x = f x}
    rcases G.eq_empty_or_nonempty with hG | hG
    · refine ⟨S, by omega, ?_⟩
      rw [show {g ∈ F | ∀ x ∈ S, eval g x = f x} = G from rfl, hG, card_empty, mul_zero]
      exact Nat.zero_le _
    obtain ⟨x, hx⟩ := exists_card_le_sixteen_mul_eval eval hm hα hG fun g hg =>
      hmaj g fun i => (mem_filter.mp (hg i)).1
    have hsplit := card_filter_add_card_filter_not (s := G) (fun g => eval g x = f x)
    have hstep : 16 * #{g ∈ G | eval g x = f x} ≤ 15 * #G := by
      simp only [← ne_eq] at hsplit
      omega
    have key : 16 ^ (k + 1) * #{g ∈ G | eval g x = f x} ≤ 15 ^ (k + 1) * #F :=
      calc 16 ^ (k + 1) * #{g ∈ G | eval g x = f x} =
          16 ^ k * (16 * #{g ∈ G | eval g x = f x}) := by ring
        _ ≤ 16 ^ k * (15 * #G) := Nat.mul_le_mul_left _ hstep
        _ = 15 * (16 ^ k * #G) := by ring
        _ ≤ 15 * (15 ^ k * #F) := Nat.mul_le_mul_left _ hcard
        _ = 15 ^ (k + 1) * #F := by ring
    classical
    refine ⟨insert x S, (card_insert_le x S).trans (by omega), ?_⟩
    convert key using 3
    ext g
    simp [G, and_assoc, and_comm (a := eval g x = f x)]

/-- **Small anti-checkers against an indexed family**, using the tuple-counting variant of
[OliveiraPichSanthanam2019, Section 4.2, Lemma 23]. If no `m` descriptions in `F` have evaluations
with pointwise strict majority `f`, and `F` has fewer than `2 ^ b` descriptions, then at most `16 b`
inputs refute every evaluated function. No injectivity of `eval` is assumed. -/
theorem exists_isAntiChecker_image {β : Type*} (eval : β → α → Bool) {b : ℕ}
    (hm : 0 < m) (hα : Fintype.card α ≤ 2 ^ m)
    (F : Finset β) {f : α → Bool}
    (hmaj : ∀ g : Fin m → β, (∀ i, g i ∈ F) →
      (fun x => strictMajority m fun i => eval (g i) x) ≠ f)
    (hb : #F < 2 ^ b) :
    ∃ S : Finset α, #S ≤ 16 * b ∧ IsAntiChecker (eval '' (F : Set β)) f S := by
  obtain ⟨S, hS, hcard⟩ := exists_card_filter_le_eval eval hm hα F hmaj (16 * b)
  refine ⟨S, hS, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  by_contra! hgS
  have hpos : 0 < #{g ∈ F | ∀ x ∈ S, eval g x = f x} :=
    card_pos.mpr ⟨g, mem_filter.mpr ⟨hg, hgS⟩⟩
  have hpow : 15 ^ (16 * b) * 2 ^ b ≤ 16 ^ (16 * b) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) b
  have := Nat.mul_lt_mul_of_pos_left hb (pow_pos (by norm_num : 0 < 15) (16 * b))
  have := Nat.mul_le_mul_left (16 ^ (16 * b)) hpos
  omega

/-- **Small anti-checkers**, by the ordered-tuple variant of
[OliveiraPichSanthanam2019, Section 4.2, Lemma 23]. Suppose there are at most `2 ^ m` inputs,
with `m > 0`, and no `m` members of `F`, repetitions allowed, have `f` as their pointwise strict
majority. If `F` has fewer than `2 ^ b` members, some set of at most `16 b` inputs is an
anti-checker for `f` against `F`. -/
theorem exists_isAntiChecker {b : ℕ} (hm : 0 < m) (hα : Fintype.card α ≤ 2 ^ m)
    (F : Finset (α → Bool)) {f : α → Bool}
    (hmaj : ∀ g : Fin m → α → Bool, (∀ i, g i ∈ F) →
      (fun x => strictMajority m fun i => g i x) ≠ f)
    (hb : #F < 2 ^ b) :
    ∃ S : Finset α, #S ≤ 16 * b ∧ IsAntiChecker F f S := by
  simpa only [Set.image_id] using exists_isAntiChecker_image id hm hα F hmaj hb

/-! ### Anti-checkers against circuits -/

variable {n s : ℕ}

/-- Against the functions computable with at most `s` gates, `S` is an anti-checker for `f`
exactly when `f` needs more than `s` gates on `S`. -/
theorem isAntiChecker_computableFunctions_iff {f : BooleanFunction n} {S : Set (BitString n)} :
    IsAntiChecker (computableFunctions n s) f S ↔ s < complexityOn interpretation S (single f) := by
  rw [← not_le, complexityOn_le_iff]
  simp only [Circuit.computesOn_single_iff]
  constructor
  · rintro hS ⟨c, hc, hsize⟩
    obtain ⟨x, hx, hne⟩ := hS (fun y => c.eval interpretation y 0)
      (Boolean.mem_computableFunctions.mpr
        ⟨c, Circuit.computes_single_iff.mpr fun _ => rfl, hsize⟩)
    exact hne (hc x hx)
  · intro h g hg
    obtain ⟨c, hcg, hsize⟩ := Boolean.mem_computableFunctions.mp hg
    by_contra! hgS
    exact h ⟨c, fun x hx => (Circuit.computes_single_iff.mp hcg x).trans (hgS x hx), hsize⟩

/-- Against the functions computable with at most `s` gates, `S` is an anti-checker for `f`
exactly when the Succinct MCSP instance of the values of `f` on `S`, with threshold `s`, is a
no-instance. -/
theorem isAntiChecker_computableFunctions_iff_notMem {f : BooleanFunction n}
    {S : Finset (BitString n)} :
    IsAntiChecker (computableFunctions n s) f S ↔
      SuccinctMCSP.Instance.ofFunction f S s ∉ SuccinctMCSP := by
  rw [isAntiChecker_computableFunctions_iff, SuccinctMCSP.ofFunction_mem_iff, not_le]

/-- The strict majority of `m` functions costs at most their complexities and that of strict
majority. -/
theorem complexity_strictMajority_le (g : Fin m → BooleanFunction n) :
    complexity interpretation (single fun x => strictMajority m fun i => g i x) ≤
      ∑ i, complexity interpretation (single (g i)) +
        complexity interpretation (single (strictMajority m)) :=
  (complexity_comp_le (fun x i => g i x) (single (strictMajority m))).trans
    (Nat.add_le_add_right (complexity_pi_le g) _)

/-- **Small anti-checkers against circuits**, by the ordered-tuple variant of
[OliveiraPichSanthanam2019, Section 4.2, Lemma 23]. Let `n ≤ m` with `m > 0`. If `f` needs more
than `m s` gates plus the complexity of strict majority on `m` bits, and fewer than `2 ^ b`
functions on `n` inputs have circuits with at most `s` gates, then on some set of at most
`16 b` inputs `f` needs more than `s` gates. -/
theorem exists_lt_complexityOn {m b : ℕ} (hm : 0 < m) (hnm : n ≤ m) {f : BooleanFunction n}
    (hf : m * s + complexity interpretation (single (strictMajority m)) <
      complexity interpretation (single f))
    (hb : #(computableFunctions n s) < 2 ^ b) :
    ∃ S : Finset (BitString n), #S ≤ 16 * b ∧ s < complexityOn interpretation S (single f) := by
  have hα : Fintype.card (BitString n) ≤ 2 ^ m := by
    rw [BitString.card]
    exact Nat.pow_le_pow_right two_pos hnm
  have hmaj (g : Fin m → BooleanFunction n) (hg : ∀ i, g i ∈ computableFunctions n s) :
      (fun x => strictMajority m fun i => g i x) ≠ f := fun heq => by
    have hle := complexity_strictMajority_le g
    rw [heq] at hle
    have hsum : ∑ i, complexity interpretation (single (g i)) ≤ ∑ _i : Fin m, s :=
      sum_le_sum fun i _ => mem_computableFunctions_iff_complexity_le.mp (hg i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    omega
  obtain ⟨S, hS, hanti⟩ := exists_isAntiChecker hm hα _ hmaj hb
  exact ⟨S, hS, isAntiChecker_computableFunctions_iff.mp hanti⟩

/-- **Small anti-checkers against circuits**, as Succinct MCSP: under the hypotheses of
`exists_lt_complexityOn`, the values of `f` on some set of at most `16 b` inputs are a no-instance
of Succinct MCSP at threshold `s`. -/
theorem exists_ofFunction_notMem {m b : ℕ} (hm : 0 < m) (hnm : n ≤ m) {f : BooleanFunction n}
    (hf : m * s + complexity interpretation (single (strictMajority m)) <
      complexity interpretation (single f))
    (hb : #(computableFunctions n s) < 2 ^ b) :
    ∃ S : Finset (BitString n), #S ≤ 16 * b ∧
      SuccinctMCSP.Instance.ofFunction f S s ∉ SuccinctMCSP := by
  obtain ⟨S, hS, hlt⟩ := exists_lt_complexityOn hm hnm hf hb
  exact ⟨S, hS, by rw [SuccinctMCSP.ofFunction_mem_iff, not_le]; exact hlt⟩

end Cslib.MCSP

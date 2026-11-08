/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.Partrec
public import Complexity.Foundations.Computability.ComputablePred
import Complexity.Computability.Kolmogorov.Incompressibility
import Complexity.Computability.Kolmogorov.Uncomputability
import Mathlib.Data.Set.Finite.List

/-!
# Chaitin's incompleteness theorem for plain Kolmogorov complexity

A statement `n ≤ C(x)` ("`x` has complexity at least `n`") is true for infinitely many `n`,
because the complexity is unbounded. Chaitin's incompleteness theorem says that every computably
enumerable collection of such statements that contains only true ones has bounded `n`. More
precisely, the bound is the complexity of a code semi-deciding the collection plus a constant
[Chaitin][Chaitin1974], [Li and Vitányi, Chapter 2][LiVitanyi2019]. The proof is Berry's paradox:
the program "the first `x` in the collection with `n` above my own length" would describe, with
`|p|` bits, an object of complexity above `|p| + O(1)`.

Formal systems are represented by r.e. sets, not by a logic. A *theory* is an r.e. predicate
`T : σ → Prop` on a `Primcodable` type of sentences, with a computable `read : σ → Option (α × ℕ)`
recognizing the sentences that assert `n ≤ C(x)`. Soundness is the hypothesis that every such
sentence of `T` is true.

The complexity is that of any description method `U` for a `Primcodable` type `α` that is at most
an additive constant worse than every partial recursive decoder `List Bool →. α`
(`MinorizesPartrec`). The universal method `DescriptionMethod.universal` for natural numbers has
this property (`minorizesPartrec_universal`), and so does its pushforward along any map with a
computable section (`MinorizesPartrec.map`), for example the decoding to binary strings. The
constant in the quantitative theorem is measured with the plain complexity under `universal` of
the number `encode e` of a code `e` of `Nat.Partrec.Code` semi-deciding the collection.

Following the rest of the library, the complexity here is plain complexity, which Li and Vitányi
write `C`; this file has no prefix-free version.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec`: a description method that is at most an
  additive constant worse than every partial recursive decoder.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.minorizesPartrec_universal`: the universal method minorizes
  every partial recursive decoder.
* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_forall_le_complexity_universal_add`:
  **Chaitin's incompleteness theorem**, quantitative form: if a code `e` semi-decides a set of
  true statements `n ≤ C(x)`, then every such `n` is at most `C(encode e) + c`, for a constant `c`
  independent of `e`. `exists_forall_le_complexity_universal_add_of_read` is the form for theories.
* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_forall_le_of_rePred`,
  `Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_forall_le_of_rePred_of_read`: an
  r.e. sound collection, or theory, proves only boundedly many lower bounds.
* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_notMem_of_rePred`: some true
  statement `n ≤ C(x)` is missing from every r.e. sound collection.
* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.finite_of_rePred`: an r.e. set on which a
  computable `ℓ` with finite sublevel sets is a lower bound for the complexity is finite.
* `Cslib.Kolmogorov.DescriptionMethod.infinite_setOf_length_le_ecomplexity`,
  `Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.finite_of_rePred_of_subset_length_le`: the
  incompressible strings, `|x| ≤ C(x)`, form an infinite set with no infinite r.e. subset.
* `Cslib.Kolmogorov.DescriptionMethod.infinite_setOf_size_le_complexity_universal`,
  `Cslib.Kolmogorov.DescriptionMethod.finite_of_rePred_of_subset_size_le_complexity_universal`:
  the same for natural numbers under `universal`, with the binary length `Nat.size x` in place of
  `|x|`.

## References

* [G. J. Chaitin, *Information-Theoretic Limitations of Formal Systems*][Chaitin1974]
* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

public section

namespace Cslib.Kolmogorov.DescriptionMethod

open Encodable Denumerable Nat.Partrec

variable {α σ : Type*} [Primcodable α] [Primcodable σ]

/-- The description method `U` *minorizes partial recursive decoders*: for every partial recursive
`g : List Bool →. α` there is a constant `c` with `C_U(x) ≤ |p| + c` whenever `x ∈ g p`. This is
the half of additive optimality for the partial recursive description methods
[Li and Vitányi, Section 2.1][LiVitanyi2019] that lower-bound arguments use; `U` itself need not
be partial recursive. -/
@[expose]
def MinorizesPartrec (U : DescriptionMethod α) : Prop :=
  ∀ g : List Bool →. α, Partrec g → ∃ c : ℕ, ∀ p x, x ∈ g p → U.ecomplexity x ≤ p.length + c

/-- A description method that is additively optimal for the partial recursive description methods
of natural numbers minorizes every partial recursive decoder. -/
theorem IsAdditivelyOptimal.minorizesPartrec {U : DescriptionMethod ℕ}
    (hU : U.IsAdditivelyOptimal {M | M.IsPartrec}) : U.MinorizesPartrec := by
  intro g hg
  obtain ⟨c, hc⟩ := Code.exists_code.mp hg
  obtain ⟨d, hd⟩ := hU.exists_ecomplexity_le (ofCode c) (isPartrec_ofCode c)
  refine ⟨d, fun p x hx => ?_⟩
  have hpx : (ofCode c).Produces p x := by
    rw [ofCode_produces_iff, hc]
    simpa [Encodable.encodek] using hx
  exact (hd x).trans (add_le_add_left (ecomplexity_le_length hpx) d)

/-- The universal description method minorizes every partial recursive decoder. -/
theorem minorizesPartrec_universal : universal.MinorizesPartrec :=
  isAdditivelyOptimal_universal.minorizesPartrec

/-- Pushing forward along `f` preserves minorization when `f` has a computable section `s`. -/
theorem MinorizesPartrec.map {β : Type*} [Primcodable β] {U : DescriptionMethod α}
    (hU : U.MinorizesPartrec) {f : α → β} {s : β → α} (hs : Computable s)
    (hfs : ∀ y, f (s y) = y) : (U.map f).MinorizesPartrec := by
  intro g hg
  obtain ⟨c, hc⟩ := hU (fun p => (g p).map s) (hg.map (hs.comp Computable.snd).to₂)
  refine ⟨c, fun p y hy => ?_⟩
  calc (U.map f).ecomplexity y = (U.map f).ecomplexity (f (s y)) := by rw [hfs]
    _ ≤ U.ecomplexity (s y) := U.ecomplexity_map_le f (s y)
    _ ≤ p.length + c := hc p (s y) (Part.mem_map s hy)

/-! ### The Berry search -/

/-- Step `j` of the search of the code `ofNat Code m` for a statement `n ≤ C(x)` with `n > B`:
`j` encodes a sentence `t` and a fuel `s`; the step succeeds with `x` if the code halts on
`encode t` within fuel `s` and `t` reads as `(x, n)` with `B < n`. -/
private def chaitinSearch (read : σ → Option (α × ℕ)) (m B j : ℕ) : Option α :=
  (decode (α := σ × ℕ) j).bind fun ts =>
    ((Code.evaln ts.2 (ofNat Code m) (encode ts.1)).bind fun _ => read ts.1).bind fun xn =>
      bif decide (B < xn.2) then some xn.1 else none

private theorem computable_chaitinSearch {read : σ → Option (α × ℕ)} (hread : Computable read) :
    Computable fun a : (ℕ × ℕ) × ℕ => chaitinSearch read a.1.1 a.1.2 a.2 := by
  have h₃ : Computable₂ fun (B : ℕ) (xn : α × ℕ) =>
      bif decide (B < xn.2) then some xn.1 else none :=
    Computable.cond (Primrec.nat_lt.decide.to_comp.comp Computable.fst
      (Computable.snd.comp Computable.snd))
      (Computable.option_some.comp (Computable.fst.comp Computable.snd)) (Computable.const none)
  have hev : Computable₂ fun (m : ℕ) (ts : σ × ℕ) =>
      Code.evaln ts.2 (ofNat Code m) (encode ts.1) :=
    Code.primrec_evaln.to_comp.comp
      (Computable.pair (Computable.pair (Computable.snd.comp Computable.snd)
        ((Computable.ofNat Code).comp Computable.fst))
        (Computable.encode.comp (Computable.fst.comp Computable.snd)))
  have h₂ : Computable₂ fun (m : ℕ) (ts : σ × ℕ) =>
      (Code.evaln ts.2 (ofNat Code m) (encode ts.1)).bind fun _ => read ts.1 :=
    Computable.option_bind hev (hread.comp (Computable.fst.comp (Computable.snd.comp
      Computable.fst))).to₂
  have h₁ : Computable₂ fun (mB : ℕ × ℕ) (ts : σ × ℕ) =>
      ((Code.evaln ts.2 (ofNat Code mB.1) (encode ts.1)).bind fun _ => read ts.1).bind
        fun xn => bif decide (mB.2 < xn.2) then some xn.1 else none :=
    Computable.option_bind (h₂.comp (Computable.fst.comp Computable.fst) Computable.snd)
      (h₃.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd).to₂
  exact Computable.option_bind (Computable.decode.comp Computable.snd)
    (h₁.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂

/-! ### Chaitin's theorem -/

/-- **Chaitin's incompleteness theorem**, quantitative form for theories
[Chaitin][Chaitin1974], [Li and Vitányi, Chapter 2][LiVitanyi2019]. Let `read` recognize the
sentences asserting `n ≤ C_U(x)`. There is a constant `c` such that every theory semi-decided by a
code `e` all of whose such sentences are true proves `n ≤ C_U(x)` only for `n ≤ C(encode e) + c`,
where `C` is the plain complexity under `universal`.

The proof is Berry's paradox. The program `1^k 0 r`, where `r` describes `encode e`, searches the
theory for a sentence asserting `n ≤ C_U(x)` with `n > |r| + 2k + 1` and outputs `x`; this is a
partial recursive decoder, so `C_U(x) ≤ (|r| + k + 1) + k` when `k` is its constant. -/
theorem MinorizesPartrec.exists_forall_le_complexity_universal_add_of_read
    {U : DescriptionMethod α} (hU : U.MinorizesPartrec)
    {read : σ → Option (α × ℕ)} (hread : Computable read) :
    ∃ c : ℕ, ∀ (e : Code) (T : σ → Prop), (∀ t, T t ↔ (e.eval (encode t)).Dom) →
      (∀ t, T t → ∀ x n, read t = some (x, n) → (n : ℕ∞) ≤ U.ecomplexity x) →
      ∀ t, T t → ∀ x n, read t = some (x, n) → n ≤ universal.complexity (encode e) + c := by
  obtain ⟨f, hf, hfU⟩ := isPartrec_universal
  have hidx : Primrec fun p : List Bool => p.idxOf false :=
    Primrec.list_idxOf.comp (Primrec.const false) Primrec.id
  have hB : Computable fun p : List Bool => p.length + p.idxOf false :=
    (Primrec.nat_add.comp Primrec.list_length hidx).to_comp
  have hpair : Computable fun a : (List Bool × ℕ) × ℕ =>
      ((a.1.2, a.1.1.length + a.1.1.idxOf false), a.2) :=
    (Computable.pair (Computable.snd.comp Computable.fst)
      (hB.comp (Computable.fst.comp Computable.fst))).pair Computable.snd
  have hS : Computable₂ fun (pm : List Bool × ℕ) (j : ℕ) =>
      chaitinSearch read pm.2 (pm.1.length + pm.1.idxOf false) j := by
    -- Elaborating this composition as a term times out; `have` fixes its type first.
    have h := (computable_chaitinSearch hread).comp hpair
    exact h
  have hdrop : Computable fun p : List Bool => p.drop (p.idxOf false + 1) :=
    (Primrec.list_drop.comp (Primrec.succ.comp hidx) Primrec.id).to_comp
  -- The Berry decoder: `1^k 0 r` runs the theory with code `universal(r)` and outputs the first
  -- `x` found with a sentence `n ≤ C_U(x)` such that `n > |1^k 0 r| + k`.
  have hD : Partrec fun p : List Bool => (f (p.drop (p.idxOf false + 1))).bind fun m =>
      Nat.rfindOpt (chaitinSearch read m (p.length + p.idxOf false)) :=
    (hf.comp hdrop).bind (Partrec.rfindOpt hS)
  set B : List Bool → ℕ := fun p => p.length + p.idxOf false with hBdef
  set D : List Bool →. α := fun p => (f (p.drop (p.idxOf false + 1))).bind fun m =>
      Nat.rfindOpt (chaitinSearch read m (B p)) with hDdef
  obtain ⟨k, hk⟩ := hU D hD
  refine ⟨2 * k + 1, fun e T hT hsound t ht x n hxn => ?_⟩
  by_contra! hlt
  obtain ⟨r, hr, hrlen⟩ := exists_length_eq_ecomplexity (ecomplexity_universal_ne_top (encode e))
  rw [← natCast_complexity_universal, Nat.cast_inj] at hrlen
  set p : List Bool := List.replicate k true ++ false :: r with hp
  have hpidx : p.idxOf false = k := by
    rw [hp, List.idxOf_append_of_notMem (by simp), List.length_replicate, List.idxOf_cons_self,
      Nat.add_zero]
  have hpdrop : p.drop (k + 1) = r := by
    rw [hp, ← List.drop_drop, List.drop_left' (List.length_replicate ..), List.drop_one,
      List.tail_cons]
  have hplen : p.length = k + 1 + r.length := by
    simp only [hp, List.length_append, List.length_replicate, List.length_cons]
    omega
  have hBp : B p = p.length + k := by simp only [B, hpidx]
  -- The search succeeds on `p`, at the sentence `t`.
  obtain ⟨y₀, hy₀⟩ := Part.dom_iff_mem.mp ((hT t).mp ht)
  obtain ⟨s, hs⟩ := Code.evaln_complete.mp hy₀
  have hm : encode e ∈ f r := (hfU r (encode e)).mp hr
  have hsearch : x ∈ chaitinSearch read (encode e) (B p) (encode (t, s)) := by
    have hlt' : B p < n := by omega
    simp [chaitinSearch, Option.mem_def.mp hs, hxn, hlt']
  obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp (Nat.rfindOpt_dom.mpr ⟨_, x, hsearch⟩)
  have hzD : z ∈ D p := by
    simp only [D, hpidx, hpdrop]
    exact Part.mem_bind hm hz
  -- Its output `z` comes with a true sentence `n' ≤ C_U(z)` of the theory with `n' > B p`.
  obtain ⟨m, hm', hzm⟩ := Part.mem_bind_iff.mp hzD
  rw [hpidx, hpdrop] at hm'
  have hme : m = encode e := Part.mem_unique hm' hm
  subst hme
  obtain ⟨j, hj⟩ := Nat.rfindOpt_spec hzm
  simp only [chaitinSearch, ofNat_encode, Option.mem_def, Option.bind_eq_some_iff] at hj
  obtain ⟨⟨t', s'⟩, -, ⟨x', n'⟩, ⟨w, hw, hread'⟩, hcond⟩ := hj
  have hT' : T t' := (hT t').mpr (Part.dom_iff_mem.mpr ⟨w, Code.evaln_sound hw⟩)
  have hn' : (n' : ℕ∞) ≤ U.ecomplexity x' := hsound t' hT' x' n' hread'
  by_cases hc : B p < n'
  · simp only [hc, decide_true, Bool.cond_true, Option.some.injEq] at hcond
    subst hcond
    have hk' := hk p x' hzD
    have : n' ≤ p.length + k := by exact_mod_cast hn'.trans hk'
    omega
  · simp [hc] at hcond

/-- **Chaitin's incompleteness theorem**, quantitative form [Chaitin][Chaitin1974],
[Li and Vitányi, Chapter 2][LiVitanyi2019]. There is a constant `c` such that, whenever a code `e`
semi-decides a set `S` of pairs `(x, n)` with `n ≤ C_U(x)` for every member, every member has
`n ≤ C(encode e) + c`, where `C` is the plain complexity under `universal`. -/
theorem MinorizesPartrec.exists_forall_le_complexity_universal_add
    {U : DescriptionMethod α} (hU : U.MinorizesPartrec) :
    ∃ c : ℕ, ∀ (e : Code) (S : Set (α × ℕ)), (∀ xn, xn ∈ S ↔ (e.eval (encode xn)).Dom) →
      (∀ x n, (x, n) ∈ S → (n : ℕ∞) ≤ U.ecomplexity x) →
      ∀ x n, (x, n) ∈ S → n ≤ universal.complexity (encode e) + c := by
  obtain ⟨c, hc⟩ := hU.exists_forall_le_complexity_universal_add_of_read (σ := α × ℕ)
    Computable.option_some
  exact ⟨c, fun e S hS hsound x n hxn => hc e (· ∈ S) hS
    (fun t ht x n h => by cases Option.some.inj h; exact hsound _ _ ht) (x, n) hxn x n rfl⟩

/-- **Chaitin's incompleteness theorem** for theories: a sound r.e. theory proves `n ≤ C_U(x)` only
for boundedly many `n`. -/
theorem MinorizesPartrec.exists_forall_le_of_rePred_of_read
    {U : DescriptionMethod α} (hU : U.MinorizesPartrec)
    {read : σ → Option (α × ℕ)} (hread : Computable read) {T : σ → Prop} (hT : REPred T)
    (hsound : ∀ t, T t → ∀ x n, read t = some (x, n) → (n : ℕ∞) ≤ U.ecomplexity x) :
    ∃ c : ℕ, ∀ t, T t → ∀ x n, read t = some (x, n) → n ≤ c := by
  obtain ⟨c, hc⟩ := hU.exists_forall_le_complexity_universal_add_of_read hread
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp hT
  exact ⟨_, hc e T he hsound⟩

/-- **Chaitin's incompleteness theorem**: an r.e. set of pairs `(x, n)` with `n ≤ C_U(x)` for every
member has bounded `n`. -/
theorem MinorizesPartrec.exists_forall_le_of_rePred
    {U : DescriptionMethod α} (hU : U.MinorizesPartrec) {S : Set (α × ℕ)}
    (hS : REPred (· ∈ S)) (hsound : ∀ x n, (x, n) ∈ S → (n : ℕ∞) ≤ U.ecomplexity x) :
    ∃ c : ℕ, ∀ x n, (x, n) ∈ S → n ≤ c := by
  obtain ⟨c, hc⟩ := hU.exists_forall_le_complexity_universal_add
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp hS
  exact ⟨_, hc e S he hsound⟩

/-- **Incompleteness.** Every r.e. set of true statements `n ≤ C_U(x)` misses one: some `x` has
complexity at least `n` without `(x, n)` belonging to the set. -/
theorem MinorizesPartrec.exists_notMem_of_rePred [Infinite α]
    {U : DescriptionMethod α} (hU : U.MinorizesPartrec) {S : Set (α × ℕ)}
    (hS : REPred (· ∈ S)) (hsound : ∀ x n, (x, n) ∈ S → (n : ℕ∞) ≤ U.ecomplexity x) :
    ∃ (x : α) (n : ℕ), (n : ℕ∞) ≤ U.ecomplexity x ∧ (x, n) ∉ S := by
  obtain ⟨c, hc⟩ := hU.exists_forall_le_of_rePred hS hsound
  obtain ⟨x, hx⟩ := (U.eventually_natCast_le_ecomplexity (c + 1)).exists
  exact ⟨x, c + 1, mod_cast hx, fun h => by have := hc x _ h; omega⟩

/-! ### Immunity of the incompressible objects -/

/-- An r.e. set `A` on which a computable `ℓ` with finite sublevel sets is a lower bound for the
complexity, `ℓ x ≤ C_U(x)`, is finite. -/
theorem MinorizesPartrec.finite_of_rePred
    {U : DescriptionMethod α} (hU : U.MinorizesPartrec) {ℓ : α → ℕ}
    (hℓ : Computable ℓ) (hfin : ∀ n, {x | ℓ x ≤ n}.Finite) {A : Set α} (hA : REPred (· ∈ A))
    (hsound : ∀ x ∈ A, (ℓ x : ℕ∞) ≤ U.ecomplexity x) : A.Finite := by
  have hread : Computable fun x : α => some (x, ℓ x) :=
    Computable.option_some.comp (Computable.id.pair hℓ)
  obtain ⟨c, hc⟩ := hU.exists_forall_le_of_rePred_of_read hread hA fun x hx y n h => by
    cases Option.some.inj h
    exact hsound x hx
  exact (hfin c).subset fun x hx => hc x hx x (ℓ x) rfl

/-- For every description method of binary strings, the incompressible strings, `|x| ≤ C(x)`,
form an infinite set: there is one of every length. -/
theorem infinite_setOf_length_le_ecomplexity (U : DescriptionMethod (List Bool)) :
    {x : List Bool | (x.length : ℕ∞) ≤ U.ecomplexity x}.Infinite := by
  refine Set.Infinite.of_image List.length (Set.infinite_of_not_bddAbove fun ⟨b, hb⟩ => ?_)
  obtain ⟨x, hx, hxc⟩ := U.exists_length_eq_le_ecomplexity (b + 1)
  have := hb ⟨x, by rw [Set.mem_ofPred_eq, hx]; exact hxc, rfl⟩
  omega

/-- **The incompressible strings are immune.** Every r.e. set of incompressible strings,
`|x| ≤ C_U(x)`, is finite. With `infinite_setOf_length_le_ecomplexity`, the incompressible strings
form an infinite set with no infinite r.e. subset. -/
theorem MinorizesPartrec.finite_of_rePred_of_subset_length_le
    {U : DescriptionMethod (List Bool)} (hU : U.MinorizesPartrec)
    {A : Set (List Bool)} (hA : REPred (· ∈ A))
    (hsub : A ⊆ {x | (x.length : ℕ∞) ≤ U.ecomplexity x}) : A.Finite :=
  hU.finite_of_rePred Computable.list_length (fun n => List.finite_length_le Bool n) hA hsub

/-- `Nat.size n` is the least `k` with `n < 2 ^ k`, so it is computable. -/
private theorem computable_size : Computable Nat.size := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hp : ComputablePred fun nk : ℕ × ℕ => nk.1 < 2 ^ nk.2 :=
    (Primrec.nat_lt.decide.comp Primrec.fst
      (hpow.comp (Primrec.const 2) Primrec.snd)).to_comp.computablePred
  refine (Computable.find (P := fun n k => n < 2 ^ k) hp fun n => ⟨_, Nat.lt_size_self n⟩).of_eq
    fun n => le_antisymm (Nat.find_min' _ (Nat.lt_size_self n))
      (Nat.size_le.mpr (Nat.find_spec (⟨_, Nat.lt_size_self n⟩ : ∃ k, n < 2 ^ k)))

/-- The natural numbers whose binary length is at most their plain complexity form an infinite
set. -/
theorem infinite_setOf_size_le_complexity_universal :
    {x : ℕ | x.size ≤ universal.complexity x}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨b, hb⟩ := ((Set.finite_le_nat a).image universal.complexity).bddAbove
  obtain ⟨x, hx, hxc⟩ := universal.exists_mem_le_ecomplexity (s := {x | x < 2 ^ (b + 1)})
    (r := b + 1) (by
      rw [show {x | x < 2 ^ (b + 1)} = ((Finset.range (2 ^ (b + 1)) : Finset ℕ) : Set ℕ) by
        ext; simp, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
      norm_cast)
  rw [← natCast_complexity_universal, Nat.cast_le] at hxc
  refine ⟨x, (Nat.size_le.mpr hx).trans hxc, lt_of_not_ge fun hxa => ?_⟩
  have := hb ⟨x, hxa, rfl⟩
  omega

/-- **Immunity for natural numbers.** Every r.e. set of natural numbers whose binary length is at
most their plain complexity is finite. -/
theorem finite_of_rePred_of_subset_size_le_complexity_universal {A : Set ℕ}
    (hA : REPred (· ∈ A)) (hsub : A ⊆ {x | x.size ≤ universal.complexity x}) : A.Finite :=
  minorizesPartrec_universal.finite_of_rePred computable_size
    (fun n => (Set.finite_lt_nat (2 ^ n)).subset fun _ hx => Nat.size_le.mp hx) hA
    fun x hx => by
      rw [← natCast_complexity_universal]
      exact_mod_cast hsub hx

end Cslib.Kolmogorov.DescriptionMethod

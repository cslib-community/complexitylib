/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BooleanHierarchy.PH
public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
public import CslibFrontier.Computability.Complexity.Problems.SATUNSAT
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Kadin's Theorem

If the Boolean hierarchy over `NP` collapses at any finite level `k` (`coBH k ⊆ BH k`, or
equivalently `BH (k + 1) = BH k`), then the polynomial hierarchy collapses to its third level
`Σ₃ᴾ ∩ Π₃ᴾ` (`PH = Σ₃ᴾ`) [Kadin][Kadin1988]. In particular, if `DP = coDP` (or `SATUNSAT ∈ coDP`),
then `PH = Σ₃ᴾ`.

Kadin's argument shows that a Boolean-hierarchy collapse gives a sparse set `S` with
`coNP ⊆ NP^S`, from which Yap's theorem [Yap][Yap1983] gives `PH ⊆ Σ₃ᴾ` [Kadin][Kadin1988]. The
1988 abstract also claims the stronger collapse `PH ⊆ P^{NP^{NP}[O(log n)]}`, a subclass of
`Δ₃ᴾ`, but that derivation rests on a proof that `S ∈ NP^{NP}` which contains an error, as
recorded in Kadin's erratum [Kadin][Kadin1991] and by [Chang and Kadin][ChangKadin1996]. The
stronger collapse holds by other arguments (survey: [Hemaspaandra, Hemaspaandra and
Hempel][HemaspaandraHemaspaandraHempel1999], Section 3). Wagner showed that `PH` then collapses
to the Boolean closure of `Σ₂ᴾ`, and Chang and Kadin to level `k` of the Boolean hierarchy over
`Σ₂ᴾ` [ChangKadin1996]; both classes lie in `P^{NP^{NP}[O(log n)]}`. Neither the sparse-set
statement nor these deeper collapses are formalized here; the library has no class of
bounded-query `Σ₂ᴾ`-oracle machines.

## Proof overview

To place a language `A ∈ Π₃ᴾ` in `Σ₃ᴾ`, peel off its first two quantifier blocks of lengths `p₁`
and `p₂`; the negated inner quantifier defines a language `E ∈ NP (encPair enc encBits)` such that
`a ∈ A ↔ ∀ u₁ (|u₁| = p₁(n)), ∃ u₂ (|u₂| = p₂(n)), (a, u₁ ++ u₂) ∉ E`, where every queried word
`u₁ ++ u₂` has fixed length `m(n) = (p₁ + p₂)(n)`.

For each `r ≤ k`, an `r`-tuple of words of length `m(n)` is represented as a single concatenated
bit string `s` of length `r * m(n)` paired with `a` under `encPair enc encBits`. The canonical
alternating languages `kadinChain enc m E r ∈ BH (encPair enc encBits) r` satisfy
`(a, s ++ y) ∈ kadinChain enc m E (r + 1) ↔ (a, y) ∈ E ∧ (a, s) ∉ kadinChain enc m E r` whenever
`|s| = r * m(n)`. Assuming `coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k`, the
complement `(kadinChain enc m E k)ᶜ` lies in `BH (encPair enc encBits) k`. Stepping down the nested
difference representation of `(kadinChain enc m E k)ᶜ` from `r = k` to `r = 0` yields at each level
either a hard prefix `s` of length `r * m(n)` that reduces `(a, y) ∉ E` on words of length `m(n)`
to an existential check over `NP`, or completeness for the next level down. Taking the union of
these `k` hard-prefix branches places `A` in `Σ₃ᴾ`.

## Main definitions

* `Cslib.Complexity.kadinChain`: the canonical `BH r` language on concatenated `r`-tuples of fixed
  polynomial word length.
* `Cslib.Complexity.allWordsIn`: the `NP` language checking that `d` concatenated words of fixed
  polynomial length all belong to a given language.

## Main results

* `Cslib.Complexity.exists_mem_BH_encBits_and_polyTimeReducible`: every language in `BH enc r`
  polynomial-time many-one reduces to a language in `BH encBits r`.
* `Cslib.Complexity.coBH_subset_BH_of_coBH_encBits_subset_BH_encBits` and
  `Cslib.Complexity.BH_succ_eq_of_BH_encBits_succ_eq`: Boolean-hierarchy collapse on the canonical
  bit-string encoding `encBits` transfers to every instance encoding `enc`.
* `Cslib.Complexity.PiP_three_subset_SigmaP_three_of_coBH_subset_BH`:
  `coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k → PiP 3 enc ⊆ SigmaP 3 enc`.
* `Cslib.Complexity.SigmaP_three_eq_PiP_three_of_coBH_subset_BH`:
  `coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k → SigmaP 3 enc = PiP 3 enc`.
* `Cslib.Complexity.PH_eq_SigmaP_three_of_coBH_subset_BH`: Kadin's theorem for
  `coBH encBits k ⊆ BH encBits k`.
* `Cslib.Complexity.PH_eq_SigmaP_three_of_BH_succ_eq`: Kadin's theorem for
  `BH encBits (k + 1) = BH encBits k`.
* `Cslib.Complexity.PH_eq_SigmaP_three_of_DP_eq_coDP`: Kadin's theorem for
  `DP encBits = coDP encBits`.
* `Cslib.Complexity.DPComplete.PH_eq_SigmaP_three_of_mem_coDP` and
  `Cslib.Complexity.PH_eq_SigmaP_three_of_SATUNSAT_mem_coDP`: collapse from a single `DP`-complete
  language in `coDP`.

## References

* [J. Kadin, *The Polynomial Time Hierarchy Collapses if the Boolean Hierarchy
  Collapses*][Kadin1988]
* [J. Kadin, *Erratum: The Polynomial Time Hierarchy Collapses if the Boolean Hierarchy
  Collapses*][Kadin1991]
* [R. Chang and J. Kadin, *The Boolean Hierarchy and the Polynomial Hierarchy: A Closer
  Connection*][ChangKadin1996]
* [E. Hemaspaandra, L. A. Hemaspaandra and H. Hempel, *What's Up with Downward Collapse: Using
  the Easy-Hard Technique to Link Boolean and Polynomial Hierarchy
  Collapses*][HemaspaandraHemaspaandraHempel1999]
* [J.-Y. Cai et al., *The Boolean Hierarchy I: Structural Properties*][CaiEtAl1988]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Polynomial

variable {α β : Type} {enc : α ↪ List Bool}

/-! ### Slices of the word component -/

/-- Dropping the first `q |enc a|` bits of the word component is polynomial-time. -/
private theorem polyTimeReducible_drop (q : Polynomial ℕ) (C : Set (α × List Bool)) :
    PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
      {x : α × List Bool | (x.1, x.2.drop (q.eval (enc x.1).length)) ∈ C} C :=
  ⟨fun x => (x.1, x.2.drop (q.eval (enc x.1).length)),
    (fst _ _).prod (bitsDropWithInput (snd _ _)
      ((unary_eval q).comp ((encoding_length enc).comp (fst _ _)))),
    fun _ => Iff.rfl⟩

/-- Keeping the first `q |enc a|` bits of the word component is polynomial-time. -/
private theorem polyTimeReducible_take (q : Polynomial ℕ) (C : Set (α × List Bool)) :
    PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
      {x : α × List Bool | (x.1, x.2.take (q.eval (enc x.1).length)) ∈ C} C :=
  ⟨fun x => (x.1, x.2.take (q.eval (enc x.1).length)),
    (fst _ _).prod (bitsTakeWithInput (snd _ _)
      ((unary_eval q).comp ((encoding_length enc).comp (fst _ _)))),
    fun _ => Iff.rfl⟩

/-! ### Kadin's alternating tuple chain and word-tuple predicates -/

/-- The canonical `BH r` language on concatenated `r`-tuples of words of length `m |enc a|`:
`(a, s ++ y)` belongs to `kadinChain enc m E (r + 1)` when `(a, y) ∈ E` and
`(a, s) ∉ kadinChain enc m E r`. -/
def kadinChain (enc : α ↪ List Bool) (m : Polynomial ℕ) (E : Set (α × List Bool)) :
    ℕ → Set (α × List Bool)
  | 0 => ∅
  | r + 1 =>
    {x : α × List Bool | (x.1, x.2.drop ((r • m).eval (enc x.1).length)) ∈ E} \
      {x : α × List Bool | (x.1, x.2.take ((r • m).eval (enc x.1).length)) ∈ kadinChain enc m E r}

@[simp]
theorem kadinChain_zero (m : Polynomial ℕ) (E : Set (α × List Bool)) :
    kadinChain enc m E 0 = ∅ := rfl

theorem mem_kadinChain_succ_append {m : Polynomial ℕ} {E : Set (α × List Bool)} {r : ℕ}
    {a : α} {s y : List Bool} (hs : s.length = (r • m).eval (enc a).length) :
    (a, s ++ y) ∈ kadinChain enc m E (r + 1) ↔
      (a, y) ∈ E ∧ (a, s) ∉ kadinChain enc m E r := by
  have hs' : s.length = r * m.eval (enc a).length := by simpa using hs
  simp [kadinChain, ← hs']

theorem kadinChain_mem_BH {m : Polynomial ℕ} {E : Set (α × List Bool)}
    (hE : E ∈ NP (encPair enc encBits)) (r : ℕ) :
    kadinChain enc m E r ∈ BH (encPair enc encBits) r := by
  induction r with
  | zero => simp [kadinChain]
  | succ r ih =>
    exact ⟨_, (polyTimeReducible_drop (r • m) E).mem_NP hE, _,
      (polyTimeReducible_take (r • m) _).mem_BH ih, rfl⟩

/-- The `NP` language checking that each of the first `d` consecutive blocks of length `m |enc a|`
in `z` belongs to `E`. -/
def allWordsIn (enc : α ↪ List Bool) (m : Polynomial ℕ) (E : Set (α × List Bool)) :
    ℕ → Set (α × List Bool)
  | 0 => Set.univ
  | d + 1 =>
    {x : α × List Bool | (x.1, x.2.take (m.eval (enc x.1).length)) ∈ E} ∩
      {x : α × List Bool | (x.1, x.2.drop (m.eval (enc x.1).length)) ∈ allWordsIn enc m E d}

@[simp]
theorem allWordsIn_zero (m : Polynomial ℕ) (E : Set (α × List Bool)) :
    allWordsIn enc m E 0 = Set.univ := rfl

theorem mem_allWordsIn_succ_append {m : Polynomial ℕ} {E : Set (α × List Bool)} {d : ℕ}
    {a : α} {y z : List Bool} (hy : y.length = m.eval (enc a).length) :
    (a, y ++ z) ∈ allWordsIn enc m E (d + 1) ↔
      (a, y) ∈ E ∧ (a, z) ∈ allWordsIn enc m E d := by
  simp [allWordsIn, ← hy]

theorem allWordsIn_mem_NP {m : Polynomial ℕ} {E : Set (α × List Bool)}
    (hE : E ∈ NP (encPair enc encBits)) (d : ℕ) :
    allWordsIn enc m E d ∈ NP (encPair enc encBits) := by
  induction d with
  | zero => exact ⟨0, fun _ => true, .const _, by simp [IsVerifier]⟩
  | succ d ih =>
    exact inter_mem_NP ((polyTimeReducible_take m E).mem_NP hE)
      ((polyTimeReducible_drop m _).mem_NP ih)

/-- Unpack a `BH (r + 1)` language `D ⊆ U` (where `U ∈ NP`) into `D = B \ D₁` with
`D₁ ⊆ B ⊆ U`, so that `D₁ = B \ D ⊆ U \ D`. -/
private theorem mem_BH_succ_subset {γ : Type} {encγ : γ ↪ List Bool} {r : ℕ}
    {U D : Set γ} (hU : U ∈ NP encγ) (hD : D ∈ BH encγ (r + 1)) (hDU : D ⊆ U) :
    ∃ B ∈ NP encγ, ∃ D₁ ∈ BH encγ r,
      B ⊆ U ∧ D₁ ⊆ B ∧ D = B \ D₁ ∧ D₁ ⊆ U \ D := by
  obtain ⟨B', hB', D', hD', rfl⟩ := hD
  refine ⟨B' ∩ U, inter_mem_NP hB' hU, D' ∩ (B' ∩ U),
    inter_mem_BH_of_mem_NP hD' (inter_mem_NP hB' hU),
    Set.inter_subset_right, Set.inter_subset_right, ?_, ?_⟩
  · ext x
    have hxU : x ∈ B' \ D' → x ∈ U := fun h => hDU h
    simp only [Set.mem_sdiff, Set.mem_inter_iff] at hxU ⊢
    tauto
  · intro x hx
    simp only [Set.mem_inter_iff, Set.mem_sdiff] at hx ⊢
    tauto

/-! ### Hard-prefix branch at level `r` -/

/-- A prefix `s` of `r` words of length `m |enc a|` is `r`-hard for `D₁` on instance `a` if
`(a, s) ∉ kadinChain enc m E r` and no extension by `y` (of length `m |enc a|`) and `z` (of `d`
words in `E` of length `m |enc a|`) places `(a, s ++ y ++ z)` in `D₁`. -/
private def kadinIsHard (enc : α ↪ List Bool) (m : Polynomial ℕ) (E : Set (α × List Bool))
    (r d : ℕ) (D₁ : Set (α × List Bool)) (a : α) (s : List Bool) : Prop :=
  (a, s) ∉ kadinChain enc m E r ∧
    ∀ w : List Bool, w.length = ((1 + d) • m).eval (enc a).length →
      (a, w.drop (m.eval (enc a).length)) ∈ allWordsIn enc m E d →
      (a, s ++ w) ∉ D₁

/-- Given a hard prefix `s`, the main `Π₂` check for `a ∈ A`: for every `u₁` of length `p₁ |enc a|`,
there exist `u₂` of length `p₂ |enc a|` and `z` of `d` words in `E` (packed as `w = u₂ ++ z` of
length `(p₂ + d • m) |enc a|`) such that `(a, s ++ u₁ ++ w) ∈ B`. -/
private def kadinMain (enc : α ↪ List Bool) (p₁ p₂ m : Polynomial ℕ) (E : Set (α × List Bool))
    (d : ℕ) (B : Set (α × List Bool)) (a : α) (s : List Bool) : Prop :=
  ∀ u₁ : List Bool, u₁.length = p₁.eval (enc a).length →
    ∃ w : List Bool, w.length = (p₂ + d • m).eval (enc a).length ∧
      (a, w.drop (p₂.eval (enc a).length)) ∈ allWordsIn enc m E d ∧
      (a, s ++ u₁ ++ w) ∈ B

/-- The level-`r` hard-prefix branch of Kadin's `Σ₃ᴾ` simulation. -/
private def kadinHardBranch (enc : α ↪ List Bool) (p₁ p₂ m : Polynomial ℕ) (E : Set (α × List Bool))
    (r d : ℕ) (D₁ B : Set (α × List Bool)) : Set α :=
  {a | ∃ s : List Bool, s.length = (r • m).eval (enc a).length ∧
    kadinIsHard enc m E r d D₁ a s ∧
    kadinMain enc p₁ p₂ m E d B a s}

/-- The level-`r` hard-prefix branch is in `Σ₃ᴾ`: an existential prefix `s` of `r` words followed
by the two `Π₂ᴾ` checks `kadinIsHard` and `kadinMain`, whose quantifiers extend `s` in place
(`Cslib.Complexity.mem_PiP_of_forall_append`, `Cslib.Complexity.mem_SigmaP_of_exists_append`). -/
private theorem kadinHardBranch_mem_SigmaP_three {p₁ p₂ m : Polynomial ℕ}
    {E : Set (α × List Bool)} (hE : E ∈ NP (encPair enc encBits)) (r d : ℕ)
    {D₁ B : Set (α × List Bool)} (hD₁ : D₁ ∈ BH (encPair enc encBits) r)
    (hB : B ∈ NP (encPair enc encBits)) :
    kadinHardBranch enc p₁ p₂ m E r d D₁ B ∈ SigmaP 3 enc := by
  have hN (q : Polynomial ℕ) : ComputableInPolyTime
      (fun x : α × List Bool => q.eval (enc x.1).length) (encPair enc encBits) encUnary :=
    (unary_eval q).comp ((encoding_length enc).comp (fst _ _))
  -- the words after the first `q |enc a|` bits are `d` words in `E`
  have hAll (q : Polynomial ℕ) : {x : α × List Bool |
      (x.1, x.2.drop (q.eval (enc x.1).length)) ∈ allWordsIn enc m E d} ∈
        SigmaP 1 (encPair enc encBits) :=
    SigmaP_one (enc := encPair enc encBits) ▸
      (polyTimeReducible_drop q _).mem_NP (allWordsIn_mem_NP (m := m) hE d)
  -- `kadinIsHard`: `s` is outside the chain, and no extension `w` whose last `d` words are in `E`
  -- reaches `D₁`
  have hHard : (kadinChain enc m E r)ᶜ ∩ {x : α × List Bool | ∀ w : List Bool,
      w.length = ((1 + d) • m).eval (enc x.1).length →
        (x.1, x.2 ++ w) ∈ ({y : α × List Bool |
          (y.1, y.2.drop ((r • m + m).eval (enc y.1).length)) ∈ allWordsIn enc m E d} ∩ D₁)ᶜ} ∈
      PiP 2 (encPair enc encBits) :=
    inter_mem_PiP (BooleanHierarchy_subset_SigmaP_two_inter_PiP_two (compl_mem_BooleanHierarchy
        (BH_subset_BooleanHierarchy r (kadinChain_mem_BH (m := m) hE r)))).2
      (mem_PiP_of_forall_append (by decide) (hN _) (compl_mem_PiP_of_mem_SigmaP
        (inter_mem_SigmaP (SigmaP_subset_SigmaP_succ 1 (hAll _))
          (BooleanHierarchy_subset_SigmaP_two_inter_PiP_two (BH_subset_BooleanHierarchy r hD₁)).1)))
  -- `kadinMain`: every `u₁` extends by some `w` whose last `d` words are in `E` and
  -- `(a, s ++ u₁ ++ w) ∈ B`
  have hMain : {x : α × List Bool | ∀ u₁ : List Bool, u₁.length = p₁.eval (enc x.1).length →
      (x.1, x.2 ++ u₁) ∈ {y : α × List Bool | ∃ w : List Bool,
        w.length = (p₂ + d • m).eval (enc y.1).length ∧ (y.1, y.2 ++ w) ∈ {z : α × List Bool |
          (z.1, z.2.drop ((r • m + p₁ + p₂).eval (enc z.1).length)) ∈ allWordsIn enc m E d} ∩ B}} ∈
      PiP 2 (encPair enc encBits) :=
    mem_PiP_of_forall_append (by decide) (hN _) (SigmaP_subset_PiP_succ 1
      (mem_SigmaP_of_exists_append le_rfl (hN _)
        (inter_mem_SigmaP (hAll _) (SigmaP_one (enc := encPair enc encBits) ▸ hB))))
  convert mem_SigmaP_of_exists (k := 3) (by decide)
    (PiP_subset_SigmaP_succ 2 (inter_mem_PiP hHard hMain)) (r • m) using 1
  ext a
  simp only [kadinHardBranch, kadinIsHard, kadinMain, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_compl_iff, not_and]
  refine exists_congr fun s => and_congr_right fun hs => and_congr
    (and_congr_right fun _ => forall_congr' fun w => imp_congr_right fun _ => imp_congr_left ?_)
    (forall_congr' fun u₁ => imp_congr_right fun hu₁ => exists_congr fun w =>
      and_congr_right fun _ => and_congr_left' ?_)
  · rw [show (r • m + m).eval (enc a).length = s.length + m.eval (enc a).length by
      rw [Polynomial.eval_add, hs], ← List.drop_drop, List.drop_left]
  · rw [show (r • m + p₁ + p₂).eval (enc a).length = (s ++ u₁).length + p₂.eval (enc a).length by
      simp [hs, hu₁], ← List.drop_drop, List.drop_left]

/-! ### Downward induction along the Boolean hierarchy -/

/-- A word of length `k + l` splits as a word of length `k` followed by a word of length `l`. -/
private theorem exists_append_of_length_eq_add {w : List Bool} {k l : ℕ}
    (h : w.length = k + l) : ∃ y z, y.length = k ∧ z.length = l ∧ w = y ++ z :=
  ⟨w.take k, w.drop k, by simp [h], by simp [h], (List.take_append_drop _ _).symm⟩

section KadinInduction

variable (enc) (p₁ p₂ m : Polynomial ℕ) (E : Set (α × List Bool))

private def kadinTarget : Set α :=
  {a | ∀ u₁ : List Bool, u₁.length = p₁.eval (enc a).length →
    ∃ u₂ : List Bool, u₂.length = p₂.eval (enc a).length ∧ (a, u₁ ++ u₂) ∉ E}

private def kadinSoundD (r d : ℕ) (D : Set (α × List Bool)) : Prop :=
  ∀ a : α, ∀ s z : List Bool,
    s.length = (r • m).eval (enc a).length →
    z.length = (d • m).eval (enc a).length →
    (a, z) ∈ allWordsIn enc m E d →
    (a, s ++ z) ∈ D →
    (a, s) ∉ kadinChain enc m E r

private def kadinSoundDiff (r d : ℕ) (U D : Set (α × List Bool)) : Prop :=
  ∀ a : α, ∀ s z : List Bool,
    s.length = (r • m).eval (enc a).length →
    z.length = (d • m).eval (enc a).length →
    (a, z) ∈ allWordsIn enc m E d →
    (a, s ++ z) ∈ U \ D →
    (a, s) ∈ kadinChain enc m E r

private def kadinComp (r d : ℕ) (D : Set (α × List Bool)) (a : α) : Prop :=
  ∀ s : List Bool,
    s.length = (r • m).eval (enc a).length →
    (a, s) ∉ kadinChain enc m E r →
    ∃ z : List Bool,
      z.length = (d • m).eval (enc a).length ∧
      (a, z) ∈ allWordsIn enc m E d ∧
      (a, s ++ z) ∈ D

/-- Strong soundness of `D₁`: `(a, s ++ (y ++ z)) ∈ D₁` implies
`(a, y) ∈ E ∧ (a, s) ∉ kadinChain enc m E r`. -/
private theorem kadinStrongSoundD₁ {r d : ℕ} {U D D₁ : Set (α × List Bool)}
    (hD₁UD : D₁ ⊆ U \ D) (hSoundDiff : kadinSoundDiff enc m E (r + 1) d U D)
    (a : α) (s y z : List Bool) (hs : s.length = (r • m).eval (enc a).length)
    (hy : y.length = m.eval (enc a).length) (hz : z.length = (d • m).eval (enc a).length)
    (hzE : (a, z) ∈ allWordsIn enc m E d) (hmem : (a, s ++ (y ++ z)) ∈ D₁) :
    (a, y) ∈ E ∧ (a, s) ∉ kadinChain enc m E r := by
  -- Strong soundness of `D₁`: `(a, s ++ y ++ z) ∈ D₁` implies `(a, y) ∈ E ∧ (a, s) ∉ L r`
  have hsy_len : (s ++ y).length = ((r + 1) • m).eval (enc a).length := by
    simp [hs, hy, add_smul, one_smul]
  have hmem' : (a, (s ++ y) ++ z) ∈ U \ D := by
    rw [List.append_assoc]
    exact hD₁UD hmem
  have hL : (a, s ++ y) ∈ kadinChain enc m E (r + 1) :=
    hSoundDiff a (s ++ y) z hsy_len hz hzE hmem'
  exact (mem_kadinChain_succ_append hs).1 hL

/-- `kadinSoundD` steps down from `(r + 1, d, U \ D)` to `(r, d + 1, D₁)`. -/
private theorem kadinSoundD_succ {r d : ℕ} {U D D₁ : Set (α × List Bool)}
    (hD₁UD : D₁ ⊆ U \ D) (hSoundDiff : kadinSoundDiff enc m E (r + 1) d U D) :
    kadinSoundD enc m E r (d + 1) D₁ := by
  intro a s w hs hw hwE hmem
  have hw' : w.length = m.eval (enc a).length + (d • m).eval (enc a).length := by
    simpa [add_smul, one_smul, Nat.add_comm] using hw
  obtain ⟨y, z, hy, hz, rfl⟩ := exists_append_of_length_eq_add hw'
  obtain ⟨_, hzE⟩ := (mem_allWordsIn_succ_append hy).1 hwE
  exact (kadinStrongSoundD₁ enc m E hD₁UD hSoundDiff a s y z hs hy hz hzE hmem).2

/-- `kadinSoundDiff` steps down from `(r + 1, d, D)` to `(r, d + 1, B, D₁)` when `D = B \ D₁`. -/
private theorem kadinSoundDiff_succ {r d : ℕ} {D B D₁ : Set (α × List Bool)}
    (hDB : D = B \ D₁) (hSoundD : kadinSoundD enc m E (r + 1) d D) :
    kadinSoundDiff enc m E r (d + 1) B D₁ := by
  intro a s w hs hw hwE hmem
  have hw' : w.length = m.eval (enc a).length + (d • m).eval (enc a).length := by
    simpa [add_smul, one_smul, Nat.add_comm] using hw
  obtain ⟨y, z, hy, hz, rfl⟩ := exists_append_of_length_eq_add hw'
  obtain ⟨hyE, hzE⟩ := (mem_allWordsIn_succ_append hy).1 hwE
  have hsy_len : (s ++ y).length = ((r + 1) • m).eval (enc a).length := by
    simp [hs, hy, add_smul, one_smul]
  have hmemD : (a, (s ++ y) ++ z) ∈ D := by
    rw [List.append_assoc, hDB]
    exact hmem
  have hnotL : (a, s ++ y) ∉ kadinChain enc m E (r + 1) :=
    hSoundD a (s ++ y) z hsy_len hz hzE hmemD
  rw [mem_kadinChain_succ_append hs, not_and, not_not] at hnotL
  exact hnotL hyE

/-- Soundness of the hard-prefix branch: every instance in `kadinHardBranch` is in
`kadinTarget`. -/
private theorem kadinHardBranch_subset_kadinTarget (hm : m = p₁ + p₂) {r d : ℕ}
    {D B D₁ : Set (α × List Bool)} (hDB : D = B \ D₁)
    (hSoundD : kadinSoundD enc m E (r + 1) d D) :
    kadinHardBranch enc p₁ p₂ m E r d D₁ B ⊆ kadinTarget enc p₁ p₂ E := by
  rintro a ⟨s, hs, ⟨hs_notL, hs_hard⟩, hmain⟩ u₁ hu₁
  obtain ⟨w, hw, hwE, hBw⟩ := hmain u₁ hu₁
  rw [Polynomial.eval_add] at hw
  obtain ⟨u₂, z, hu₂, hz, rfl⟩ := exists_append_of_length_eq_add hw
  rw [List.drop_left' hu₂] at hwE
  let y := u₁ ++ u₂
  have hy : y.length = m.eval (enc a).length := by simp [y, hm, hu₁, hu₂]
  have hyz_len : (y ++ z).length = ((1 + d) • m).eval (enc a).length := by
    simp [hy, hz, add_smul, one_smul]
  have hnotD₁ : (a, s ++ (y ++ z)) ∉ D₁ :=
    hs_hard (y ++ z) hyz_len (by rwa [List.drop_left' hy])
  have hmemD : (a, (s ++ y) ++ z) ∈ D := by
    rw [hDB]
    exact ⟨by simpa [y, List.append_assoc] using hBw, by simpa [List.append_assoc] using hnotD₁⟩
  have hsy_len : (s ++ y).length = ((r + 1) • m).eval (enc a).length := by
    simp [hs, hy, add_smul, one_smul]
  have hnotL_succ : (a, s ++ y) ∉ kadinChain enc m E (r + 1) :=
    hSoundD a (s ++ y) z hsy_len hz hwE hmemD
  rw [mem_kadinChain_succ_append hs] at hnotL_succ
  exact ⟨u₂, hu₂, fun hyE => hnotL_succ ⟨hyE, hs_notL⟩⟩

/-- When no hard prefix exists at level `r`, `kadinComp` holds at `(r, d + 1, D₁)`. -/
private theorem kadinComp_of_not_exists_kadinIsHard {r d : ℕ} {U D D₁ : Set (α × List Bool)}
    (hD₁UD : D₁ ⊆ U \ D) (hSoundDiff : kadinSoundDiff enc m E (r + 1) d U D) {a : α}
    (hEx : ¬∃ s : List Bool, s.length = (r • m).eval (enc a).length ∧
      kadinIsHard enc m E r d D₁ a s) :
    kadinComp enc m E r (d + 1) D₁ a := by
  intro s hs hs_notL
  have hnotHard : ¬kadinIsHard enc m E r d D₁ a s := fun h => hEx ⟨s, hs, h⟩
  simp only [kadinIsHard, hs_notL, not_false_eq_true, true_and, not_forall, not_not] at hnotHard
  obtain ⟨w, hw, hwE, hmemD₁⟩ := hnotHard
  have hw' : w.length = m.eval (enc a).length + (d • m).eval (enc a).length := by
    simpa [add_smul, one_smul] using hw
  obtain ⟨y, z, hy, hz, rfl⟩ := exists_append_of_length_eq_add hw'
  rw [List.drop_left' hy] at hwE
  have hyE : (a, y) ∈ E := (kadinStrongSoundD₁ enc m E hD₁UD hSoundDiff a s y z hs hy hz hwE
    hmemD₁).1
  refine ⟨y ++ z, by simpa [add_smul, one_smul, Nat.add_comm] using hw, ?_, hmemD₁⟩
  rw [mem_allWordsIn_succ_append hy]
  exact ⟨hyE, hwE⟩

private theorem exists_kadin_sigmaP_three (hm : m = p₁ + p₂)
    (hE : E ∈ NP (encPair enc encBits)) :
    ∀ (r d : ℕ) {U D : Set (α × List Bool)},
      U ∈ NP (encPair enc encBits) →
      D ∈ BH (encPair enc encBits) r →
      D ⊆ U →
      kadinSoundD enc m E r d D →
      kadinSoundDiff enc m E r d U D →
      ∃ H ∈ SigmaP 3 enc,
        H ⊆ kadinTarget enc p₁ p₂ E ∧
        ∀ a ∈ kadinTarget enc p₁ p₂ E, kadinComp enc m E r d D a → a ∈ H
  | 0, d, U, D, _, hD, _, _, _ => by
    have hD0 : D = ∅ := hD
    subst hD0
    have hempty : (∅ : Set α) ∈ SigmaP 3 enc :=
      SigmaP_subset_SigmaP_succ 2 (SigmaP_subset_SigmaP_succ 1
        (SigmaP_one (enc := enc) ▸ ⟨0, fun _ => false, .const _, by simp [IsVerifier]⟩))
    refine ⟨∅, hempty, Set.empty_subset _, fun a _ hComp => ?_⟩
    obtain ⟨z, _, _, hz⟩ := hComp [] (by simp) (by simp [kadinChain])
    exact hz
  | r + 1, d, U, D, hU, hD, hDU, hSoundD, hSoundDiff => by
    obtain ⟨B, hB, D₁, hD₁, hBU, hD₁B, hDB, hD₁UD⟩ := mem_BH_succ_subset hU hD hDU
    obtain ⟨H_r, hH_r_mem, hH_r_sub, hH_r_comp⟩ :=
      exists_kadin_sigmaP_three hm hE r (d + 1) hB hD₁ hD₁B
        (kadinSoundD_succ enc m E hD₁UD hSoundDiff) (kadinSoundDiff_succ enc m E hDB hSoundD)
    let Hard := kadinHardBranch enc p₁ p₂ m E r d D₁ B
    refine ⟨Hard ∪ H_r, union_mem_SigmaP (kadinHardBranch_mem_SigmaP_three hE r d hD₁ hB)
      hH_r_mem, Set.union_subset (kadinHardBranch_subset_kadinTarget enc p₁ p₂ m E hm hDB hSoundD)
        hH_r_sub, fun a ha hComp => ?_⟩
    by_cases hEx : ∃ s : List Bool, s.length = (r • m).eval (enc a).length ∧
        kadinIsHard enc m E r d D₁ a s
    · left
      obtain ⟨s, hs, hHard_s⟩ := hEx
      refine ⟨s, hs, hHard_s, fun u₁ hu₁ => ?_⟩
      obtain ⟨u₂, hu₂, hnotE⟩ := ha u₁ hu₁
      let y := u₁ ++ u₂
      have hy : y.length = m.eval (enc a).length := by simp [y, hm, hu₁, hu₂]
      have hsy_len : (s ++ y).length = ((r + 1) • m).eval (enc a).length := by
        simp [hs, hy, add_smul, one_smul]
      have hnotL_succ : (a, s ++ y) ∉ kadinChain enc m E (r + 1) := by
        rw [mem_kadinChain_succ_append hs]
        exact fun ⟨hyE, _⟩ => hnotE hyE
      obtain ⟨z, hz, hzE, hmemD⟩ := hComp (s ++ y) hsy_len hnotL_succ
      rw [hDB] at hmemD
      refine ⟨u₂ ++ z, by simp [hu₂, hz], by simpa [← hu₂] using hzE,
        by simpa [y, List.append_assoc] using hmemD.1⟩
    · exact Or.inr (hH_r_comp a ha (kadinComp_of_not_exists_kadinIsHard enc m E hD₁UD hSoundDiff
        hEx))

end KadinInduction

/-! ### Reduction to the canonical bit-string Boolean hierarchy -/

/-- Every language in `BH enc r` polynomial-time many-one reduces to a language in the canonical
bit-string Boolean hierarchy `BH encBits r`. -/
theorem exists_mem_BH_encBits_and_polyTimeReducible {r : ℕ} {A : Set α} (hA : A ∈ BH enc r) :
    ∃ B ∈ BH encBits r, PolyTimeReducible enc encBits A B := by
  induction r generalizing A with
  | zero =>
    have hA0 : A = ∅ := hA
    subst hA0
    exact ⟨∅, rfl, ⟨fun _ => [], .const [], fun _ => Iff.rfl⟩⟩
  | succ r ih =>
    obtain ⟨E, hE, D₁, hD₁, rfl⟩ := hA
    obtain ⟨f₀, hf₀, hiff₀⟩ := CookLevin.SAT_npHard enc E hE
    obtain ⟨B₁, hB₁, f₁, hf₁, hiff₁⟩ := ih hD₁
    let B₀ : Set (List Bool) := {w | cnfDecoder.decode w ∈ SAT}
    have hB₀ : B₀ ∈ NP encBits :=
      PolyTimeReducible.mem_NP
        ⟨cnfDecoder.decode, cnfDecoder.computableInPolyTime, fun _ => Iff.rfl⟩
        SAT.mem_NP
    have hunframe : PolyTimeReducible encBits encBits {w | unframe w ∈ B₀} B₀ :=
      ⟨unframe, ComputableInPolyTime.unframe, fun _ => Iff.rfl⟩
    have hdrop : PolyTimeReducible encBits encBits {w | dropFrame w ∈ B₁} B₁ :=
      ⟨dropFrame, ComputableInPolyTime.dropFrame, fun _ => Iff.rfl⟩
    refine ⟨{w | unframe w ∈ B₀} \ {w | dropFrame w ∈ B₁},
      ⟨_, hunframe.mem_NP hB₀, _, hdrop.mem_BH hB₁, rfl⟩,
      fun a => encPair encBits encBits (encCNF (f₀ a), f₁ a),
      (hf₀.encoding_comp.prod hf₁).encoding_comp,
      fun a => ?_⟩
    simp [B₀, unframe_frame_append, dropFrame_frame_append, cnfDecoder.decode_enc, hiff₀ a,
      hiff₁ a]

/-- Collapse of the canonical bit-string Boolean hierarchy `coBH encBits k ⊆ BH encBits k`
transfers to every instance encoding `enc`. -/
theorem coBH_subset_BH_of_coBH_encBits_subset_BH_encBits {k : ℕ}
    (h : coBH encBits k ⊆ BH encBits k) :
    coBH enc k ⊆ BH enc k := by
  intro A hA
  obtain ⟨B, hB, hred⟩ := exists_mem_BH_encBits_and_polyTimeReducible hA
  have hBc : Bᶜ ∈ BH encBits k := h (compl_mem_coBH_iff.mpr hB)
  have hred' : PolyTimeReducible enc encBits A Bᶜ := by
    simpa only [compl_compl] using hred.compl
  exact hred'.mem_BH hBc

/-- Consecutive-level collapse of the canonical bit-string Boolean hierarchy
`BH encBits (k + 1) = BH encBits k` transfers to every instance encoding `enc`. -/
theorem BH_succ_eq_of_BH_encBits_succ_eq {k : ℕ}
    (h : BH encBits (k + 1) = BH encBits k) :
    BH enc (k + 1) = BH enc k :=
  BH_succ_eq_iff_coBH_subset.mpr
    (coBH_subset_BH_of_coBH_encBits_subset_BH_encBits (BH_succ_eq_iff_coBH_subset.mp h))

/-! ### Kadin's collapse theorems -/

/-- **Kadin's theorem at level `3`** [Kadin][Kadin1988]: if `coBH k ⊆ BH k` holds for the pair
encoding `encPair enc encBits`, then `PiP 3 enc ⊆ SigmaP 3 enc`. -/
theorem PiP_three_subset_SigmaP_three_of_coBH_subset_BH {k : ℕ}
    (h : coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k) :
    PiP 3 enc ⊆ SigmaP 3 enc := by
  rintro A ⟨ps, V, hps, hV, hAV⟩
  rcases ps with _ | ⟨p₁, _ | ⟨p₂, _ | ⟨p₃, _ | _⟩⟩⟩ <;> try cases hps
  let E : Set (α × List Bool) :=
    {y | ∃ u₃ : List Bool, u₃.length = p₃.eval (enc y.1).length ∧ (!V (y.1, y.2 ++ u₃)) = true}
  have hE : E ∈ NP (encPair enc encBits) :=
    mem_NP_setOf_exists_append (V := fun x => !V x)
      (ComputableInPolyTime.bool_not.comp hV) p₃
  let m := p₁ + p₂
  have hLk_compl : (kadinChain enc m E k)ᶜ ∈ BH (encPair enc encBits) k :=
    h (compl_mem_coBH_iff.mpr (kadinChain_mem_BH hE k))
  have hU : (Set.univ : Set (α × List Bool)) ∈ NP (encPair enc encBits) :=
    ⟨0, fun _ => true, .const _, by simp [IsVerifier]⟩
  have hSoundD : kadinSoundD enc m E k 0 (kadinChain enc m E k)ᶜ := by
    intro a s z hs hz _ hmem
    have hz0 : z = [] := List.length_eq_zero_iff.1 (by simpa using hz)
    subst hz0
    simpa using hmem
  have hSoundDiff : kadinSoundDiff enc m E k 0 Set.univ (kadinChain enc m E k)ᶜ := by
    intro a s z hs hz _ hmem
    have hz0 : z = [] := List.length_eq_zero_iff.1 (by simpa using hz)
    subst hz0
    simpa using hmem
  obtain ⟨H, hH_mem, hH_sub, hH_comp⟩ :=
    exists_kadin_sigmaP_three enc p₁ p₂ m E rfl hE k 0 hU hLk_compl (Set.subset_univ _)
      hSoundD hSoundDiff
  have hA_eq : A = kadinTarget enc p₁ p₂ E := by
    ext a
    rw [hAV a]
    simp only [kadinTarget, Set.mem_ofPred_eq, List.map_cons, List.map_nil,
      alternation_false_cons, alternation_true_cons, alternation_nil]
    refine forall_congr' fun u₁ => imp_congr_right fun _ => ?_
    refine exists_congr fun u₂ => and_congr_right fun _ => ?_
    simp [E, List.append_assoc]
  have hH_eq : A = H := by
    rw [hA_eq]
    refine Set.Subset.antisymm (fun a ha => hH_comp a ha fun s _ hs => ?_) hH_sub
    exact ⟨[], by simp, trivial, by simpa using hs⟩
  rwa [hH_eq]

/-- **Kadin's theorem at level `3`** [Kadin][Kadin1988]: if `coBH k ⊆ BH k` holds for the pair
encoding `encPair enc encBits`, then `SigmaP 3 enc = PiP 3 enc`. -/
theorem SigmaP_three_eq_PiP_three_of_coBH_subset_BH {k : ℕ}
    (h : coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k) :
    SigmaP 3 enc = PiP 3 enc :=
  (PiP_eq_SigmaP_of_PiP_subset_SigmaP (PiP_three_subset_SigmaP_three_of_coBH_subset_BH h)).symm

/-- **Kadin's theorem** [Kadin][Kadin1988]: if `coBH encBits k ⊆ BH encBits k`, the polynomial
hierarchy collapses to `Σ₃ᴾ`. The deeper collapse into `P^{NP^{NP}[O(log n)]} ⊆ Δ₃ᴾ`, due to later
work, is not formalized; see the module documentation. -/
theorem PH_eq_SigmaP_three_of_coBH_subset_BH {k : ℕ}
    (h : coBH encBits k ⊆ BH encBits k) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by decide) fun _ =>
    PiP_three_subset_SigmaP_three_of_coBH_subset_BH
      (coBH_subset_BH_of_coBH_encBits_subset_BH_encBits h)

/-- **Kadin's theorem** [Kadin][Kadin1988]: if `coBH encBits k ⊆ BH encBits k`, the polynomial
hierarchy collapses to `Σ₃ᴾ ∩ Π₃ᴾ`. The deeper collapse into `P^{NP^{NP}[O(log n)]} ⊆ Δ₃ᴾ`, due to
later work, is not formalized; see the module documentation. -/
theorem PH_eq_SigmaP_three_inter_PiP_three_of_coBH_subset_BH {k : ℕ}
    (h : coBH encBits k ⊆ BH encBits k) :
    PH enc = SigmaP 3 enc ∩ PiP 3 enc := by
  rw [PH_eq_SigmaP_three_of_coBH_subset_BH h,
    ← SigmaP_three_eq_PiP_three_of_coBH_subset_BH
      (coBH_subset_BH_of_coBH_encBits_subset_BH_encBits h),
    Set.inter_self]

/-- **Kadin's theorem from `BH (k + 1) = BH k`** [Kadin][Kadin1988]: if two consecutive levels of
the Boolean hierarchy coincide on `encBits`, then `PH = Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_BH_succ_eq {k : ℕ}
    (h : BH encBits (k + 1) = BH encBits k) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coBH_subset_BH (BH_succ_eq_iff_coBH_subset.mp h)

/-- **Kadin's theorem for `DP`** [Kadin][Kadin1988]: if `coDP (encPair enc encBits) ⊆
DP (encPair enc encBits)`, then `PiP 3 enc ⊆ SigmaP 3 enc`. -/
theorem PiP_three_subset_SigmaP_three_of_coDP_subset_DP
    (h : coDP (encPair enc encBits) ⊆ DP (encPair enc encBits)) :
    PiP 3 enc ⊆ SigmaP 3 enc := by
  rw [← coBH_two, ← BH_two] at h
  exact PiP_three_subset_SigmaP_three_of_coBH_subset_BH h

/-- **Kadin's theorem for `DP`** [Kadin][Kadin1988]: if `coDP (encPair enc encBits) ⊆
DP (encPair enc encBits)`, then `SigmaP 3 enc = PiP 3 enc`. -/
theorem SigmaP_three_eq_PiP_three_of_coDP_subset_DP
    (h : coDP (encPair enc encBits) ⊆ DP (encPair enc encBits)) :
    SigmaP 3 enc = PiP 3 enc :=
  (PiP_eq_SigmaP_of_PiP_subset_SigmaP (PiP_three_subset_SigmaP_three_of_coDP_subset_DP h)).symm

/-- **Kadin's theorem for `coDP ⊆ DP`** [Kadin][Kadin1988]: if `coDP encBits ⊆ DP encBits`,
then `PH = Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_coDP_subset_DP
    (h : coDP encBits ⊆ DP encBits) :
    PH enc = SigmaP 3 enc := by
  rw [← coBH_two, ← BH_two] at h
  exact PH_eq_SigmaP_three_of_coBH_subset_BH h

/-- **Kadin's theorem for `DP = coDP`** [Kadin][Kadin1988]: if `DP encBits = coDP encBits`,
then `PH = Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_DP_eq_coDP
    (h : DP encBits = coDP encBits) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coDP_subset_DP h.symm.subset

/-! ### Collapse from a single `DP`-complete problem in `coDP` -/

/-- If a `DP`-complete problem belongs to `coDP`, then `coDP ⊆ DP` for every instance encoding. -/
theorem DPComplete.coDP_subset_DP_of_mem_coDP {encB : β ↪ List Bool} {B : Set β}
    (hB : DPComplete encB B) (h : B ∈ coDP encB) (enc : α ↪ List Bool) :
    coDP enc ⊆ DP enc := by
  intro A hA
  have hred : PolyTimeReducible enc encB A Bᶜ := by
    simpa only [compl_compl] using (hB.2 enc Aᶜ hA).compl
  exact hred.mem_DP h

/-- If a `DP`-complete problem belongs to `coDP`, then `DP = coDP` for every instance encoding. -/
theorem DPComplete.DP_eq_coDP_of_mem_coDP {encB : β ↪ List Bool} {B : Set β}
    (hB : DPComplete encB B) (h : B ∈ coDP encB) (enc : α ↪ List Bool) :
    DP enc = coDP enc := by
  have hsub := hB.coDP_subset_DP_of_mem_coDP h enc
  exact Set.Subset.antisymm (fun _ hA => hsub (compl_mem_coDP_iff.mpr hA)) hsub

/-- **Kadin's theorem for a `DP`-complete problem** [Kadin][Kadin1988]: if a `DP`-complete problem
belongs to `coDP`, then `PH = Σ₃ᴾ`. -/
theorem DPComplete.PH_eq_SigmaP_three_of_mem_coDP {encB : β ↪ List Bool} {B : Set β}
    (hB : DPComplete encB B) (h : B ∈ coDP encB) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coDP_subset_DP (hB.coDP_subset_DP_of_mem_coDP h encBits)

/-- **Kadin's theorem for `SATUNSAT`** [Kadin][Kadin1988]: if `SATUNSAT ∈ coDP`, the polynomial
hierarchy collapses to `Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_SATUNSAT_mem_coDP
    (h : SATUNSAT ∈ coDP (encPair encCNF encCNF)) :
    PH enc = SigmaP 3 enc :=
  SATUNSAT_dpComplete.PH_eq_SigmaP_three_of_mem_coDP h

end Cslib.Complexity

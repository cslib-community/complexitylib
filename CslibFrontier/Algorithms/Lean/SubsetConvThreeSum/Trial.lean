/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TrimmedYates
public import CslibFrontier.Algorithms.Lean.Yates
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.ZMod

/-!
# One hashing trial of the reduction from 3SUM to subset convolution

One trial of the reduction of [ChanItakuraMaYu2026], Theorem 2.3 (Section 2.2), from deciding
`c ∈ A + B` for every query `c` to selected entries of the ranked subset convolution.

Fix a modulus `p`, a dimension `d` and a rank `t`. A `Seed p` holds the random numbers `ξ, α, β`
of one trial, as elements of `ZMod p`. The trial hashes `f a = a ξ + α`, `g b = b ξ + β` and
`h c = c ξ + α + β` (`Seed.left`, `Seed.right`, `Seed.target`, as numbers below `p`) and views a
number `x < 2 ^ d` as the set `maskSet d x` of its binary digits `1` (the paper's `π`). The
elements `a` whose hash has exactly `t` binary digits `1` below `2 ^ d` (`Ranked d t`) form `A*`
(`starLeft`); likewise `B*` and the queries `C*` with `2 t` digits. For a query `c`, a pair
`(a, b)` *covers* `c` (`Covers`) when the digits of `f a` and `g b` are disjoint and together
are the digits of `h c`. The trial computes

* `σ(c)`, the number of covering pairs (`sigma`), and
* `τ(c) = ∑ (a + b - c) ^ 2` over the covering pairs (`tau`),

and accepts `c` when `h c` is ranked, `σ(c) > 0` and `τ(c) = 0` (`Accepts`). Both are pair sums
(`pairSum`) over the pairs related by a covering relation; the facts about pair sums and the moment
test hold for every relation and are reused by the base-`r` trial of
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorTrial`.

**Soundness** (`exists_add_eq_of_accepts`): an accepted `c` is a sum `a + b` with `a ∈ A` and
`b ∈ B`, since a sum of squares with a term vanishes only if every term does. This holds for every
modulus and seed. **Covering pairs are congruent** (`natCast_add_eq_of_covers`): for a nonzero
`ξ` in a field `ZMod p`, a covering pair satisfies `a + b ≡ c (mod p)`; the probabilistic analysis
uses this in `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Probability`.

`trialM` computes the accepted queries with one selected-entries subset convolution
(`Cslib.Algorithms.Lean.TrimmedYates.solveM`) over the ring `ℤ ^ 6` (`Moments`), whose coordinates
are the six moments `∑ a ^ i * b ^ j` (`i + j ≤ 2`) over the covering pairs; `σ` and `τ` are linear
combinations of them (`tau_eq`, `momentTest_iff`). This is the paper's "`O(1)` similar subset
convolutions" run as one. `ret_trialM` proves that it returns the accepted queries.

**Witnesses** (`accepts_or_exists_covers_ne`): if `c = a + b` and the hashes of `a` and `b` are
disjoint `t`-sets, the trial accepts `c` unless a covering pair sums to a different number. This is
the deterministic core of the completeness analysis.

## Cost model

The `TimeM` unit-cost model of `CslibFrontier.Algorithms.Lean.TrimmedYates`, with the same
conventions: numbers below `N ^ O(1)`, residues modulo `p` and sets of at most `d` coordinates are
words, and dictionary operations cost one tick.

* **Charged (`1` tick):** testing one element (`filterTickM`: hashing it, comparing with `2 ^ d`
  and counting binary digits), inserting one weighted set into a dictionary (`sparseM`), the
  ticks of the `solveM` run, and testing the moments of one query. A tick of `solveM` is one
  operation of `ℤ ^ 6`, that is, six integer operations.
* **Uncharged:** forming the query sets, zipping the answer lists and loop control.

`time_trialM` is exact: `|Ag| + |Bg| + |C| + |A*| + |B*| + |C*|` plus
`3 (d + 1) (∑_{j ≤ s} (d choose j) + |C*| ∑_{s ≤ j ≤ 2 t} (2 t choose j))`. The isolated inputs
`Ag`, `Bg` (the paper's `A \ A_bad`, `B \ B_bad`) are computed once per modulus, outside the trial.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.Seed`: the random numbers of one trial.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.Ranked`, `Isolated`, `Covers`, `pairSum`, `sigma`,
  `tau`, `Accepts`: the quantities of the trial.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.Moments`, `MomentTest`: the six moments of a query.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.trialM`: the trial as a `TimeM` program.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.exists_add_eq_of_pairSum`,
  `exists_add_eq_of_accepts`: soundness.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.natCast_add_eq_of_left_add_right`,
  `natCast_add_eq_of_covers`: covering pairs are congruent to the query.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.momentTest_iff`: the moment test.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.accepts_or_exists_covers_ne`: witnesses.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.ret_trialM`, `time_trialM`: what the program returns
  and its exact cost.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Cslib.Algorithms.Lean.TimeM Cslib.Algorithms.Lean.TrimmedYates
  Cslib.Algorithms.Lean.Yates Cslib.BitString

/-! ### Seeds and hashes -/

/-- The random numbers of one trial: the multiplier `ξ` and the shifts `α`, `β`. -/
structure Seed (p : ℕ) where
  /-- The common multiplier. -/
  ξ : ZMod p
  /-- The shift of the left hash. -/
  α : ZMod p
  /-- The shift of the right hash. -/
  β : ZMod p

namespace Seed

variable {p : ℕ}

/-- Seeds as triples. -/
@[expose] def equiv : Seed p ≃ ZMod p × ZMod p × ZMod p where
  toFun s := (s.ξ, s.α, s.β)
  invFun | (ξ, α, β) => ⟨ξ, α, β⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq (Seed p) := Seed.equiv.injective.decidableEq

instance [NeZero p] : Fintype (Seed p) := Fintype.ofEquiv _ Seed.equiv.symm

/-- The left hash `f a = a ξ + α`, as a number below `p`. -/
@[expose] def left (s : Seed p) (a : ℕ) : ℕ := ((a : ZMod p) * s.ξ + s.α).val

/-- The right hash `g b = b ξ + β`, as a number below `p`. -/
@[expose] def right (s : Seed p) (b : ℕ) : ℕ := ((b : ZMod p) * s.ξ + s.β).val

/-- The target hash `h c = c ξ + α + β`, as a number below `p`. -/
@[expose] def target (s : Seed p) (c : ℕ) : ℕ := ((c : ZMod p) * s.ξ + s.α + s.β).val

end Seed

/-! ### The quantities of a trial -/

/-- `x` is below `2 ^ d` and has exactly `t` binary digits `1`. -/
@[expose] def Ranked (d t x : ℕ) : Prop := x < 2 ^ d ∧ #(maskSet d x) = t

instance (d t x : ℕ) : Decidable (Ranked d t x) := inferInstanceAs (Decidable (_ ∧ _))

/-- `a` is the only element of `A`, counted with multiplicity, in its residue class modulo `p`;
the elements that are not isolated form the paper's `A_bad`. -/
@[expose] def Isolated (p : ℕ) (A : List ℕ) (a : ℕ) : Prop :=
  A.countP (fun a' : ℕ => (a' : ZMod p) = (a : ZMod p)) = 1

instance (p : ℕ) (A : List ℕ) (a : ℕ) : Decidable (Isolated p A a) :=
  inferInstanceAs (Decidable (_ = _))

/-- An isolated element shares its residue class with no other element. -/
theorem Isolated.eq {p : ℕ} {A : List ℕ} {a a' : ℕ} (h : Isolated p A a) (ha : a ∈ A)
    (ha' : a' ∈ A) (hmod : (a' : ZMod p) = a) : a' = a := by
  by_contra hne
  have hsub : ({a, a'} : Finset ℕ) ⊆
      (A.filter fun x : ℕ => decide ((x : ZMod p) = (a : ZMod p))).toFinset := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simpa using ha
    · simpa [hmod] using ha'
  have := (card_le_card hsub).trans (List.toFinset_card_le _)
  have h' : (A.filter fun x : ℕ => decide ((x : ZMod p) = (a : ZMod p))).length = 1 := by
    rw [← List.countP_eq_length_filter]; exact h
  rw [card_pair (Ne.symm hne)] at this
  omega

variable {p : ℕ}

/-- `(a, b)` covers `c` under the seed `s`: the binary digits of `f a` and `g b` below `d` are
disjoint and together are those of `h c`. -/
@[expose] def Covers (d : ℕ) (s : Seed p) (a b c : ℕ) : Prop :=
  Disjoint (maskSet d (s.left a)) (maskSet d (s.right b)) ∧
    maskSet d (s.left a) ∪ maskSet d (s.right b) = maskSet d (s.target c)

instance (d : ℕ) (s : Seed p) (a b c : ℕ) : Decidable (Covers d s a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The elements of `A` whose left hash is ranked: the paper's `A*` when `A` is isolated. -/
@[expose] def starLeft (d t : ℕ) (s : Seed p) (A : List ℕ) : List ℕ :=
  A.filter fun a => decide (Ranked d t (s.left a))

/-- The elements of `B` whose right hash is ranked. -/
@[expose] def starRight (d t : ℕ) (s : Seed p) (B : List ℕ) : List ℕ :=
  B.filter fun b => decide (Ranked d t (s.right b))

/-- The sum of `F a b` over the pairs `(a, b) ∈ A × B` related by `cov`, such as the pairs
covering a query. -/
@[expose] def pairSum {R : Type} [AddCommMonoid R] (cov : ℕ → ℕ → Prop) [DecidableRel cov]
    (A B : List ℕ) (F : ℕ → ℕ → R) : R :=
  (A.map fun a => (B.map fun b => if cov a b then F a b else 0).sum).sum

/-- `σ(c)`: the number of pairs of `A* × B*` covering `c`. -/
@[expose] def sigma (d t : ℕ) (s : Seed p) (A B : List ℕ) (c : ℕ) : ℤ :=
  pairSum (Covers d s · · c) (starLeft d t s A) (starRight d t s B) fun _ _ => 1

/-- `τ(c)`: the sum of `(a + b - c) ^ 2` over the pairs of `A* × B*` covering `c`. -/
@[expose] def tau (d t : ℕ) (s : Seed p) (A B : List ℕ) (c : ℕ) : ℤ :=
  pairSum (Covers d s · · c) (starLeft d t s A) (starRight d t s B) fun a b =>
    ((a : ℤ) + b - c) ^ 2

/-- The trial accepts `c`: `h c` has `2 t` binary digits `1` below `2 ^ d`, some pair covers `c`,
and every covering pair sums to `c`. -/
@[expose] def Accepts (d t : ℕ) (s : Seed p) (A B : List ℕ) (c : ℕ) : Prop :=
  Ranked d (2 * t) (s.target c) ∧ 0 < sigma d t s A B c ∧ tau d t s A B c = 0

instance (d t : ℕ) (s : Seed p) (A B : List ℕ) (c : ℕ) : Decidable (Accepts d t s A B c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Sums over covering pairs -/

private theorem sum_map_nonneg {l : List ℕ} {f : ℕ → ℤ} (h : ∀ x ∈ l, 0 ≤ f x) :
    0 ≤ (l.map f).sum :=
  List.sum_nonneg fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact h x hx

/-- A sum of nonnegative terms over covering pairs is nonnegative. -/
theorem pairSum_nonneg {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ} {F : ℕ → ℕ → ℤ}
    (hF : ∀ a b, 0 ≤ F a b) : 0 ≤ pairSum cov A B F :=
  sum_map_nonneg fun _ _ => sum_map_nonneg fun _ _ => by split_ifs <;> simp [hF]

/-- A nonnegative summand at one covering pair is at most the sum over covering pairs. -/
theorem le_pairSum {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ} {F : ℕ → ℕ → ℤ}
    (hF : ∀ a b, 0 ≤ F a b) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ B) (hc : cov a b) :
    F a b ≤ pairSum cov A B F := by
  have hterm : ∀ a' b', 0 ≤ if cov a' b' then F a' b' else 0 := fun a' b' => by
    split_ifs <;> simp [hF]
  have hrow : ∀ a', 0 ≤ (B.map fun b => if cov a' b then F a' b else 0).sum :=
    fun a' => sum_map_nonneg fun b _ => hterm a' b
  have h1 := List.single_le_sum (List.forall_mem_map.mpr fun b _ => hterm a b) _
    (List.mem_map_of_mem (f := fun b =>
    if cov a b then F a b else 0) hb)
  have h2 := List.single_le_sum (List.forall_mem_map.mpr fun a _ => hrow a) _
    (List.mem_map_of_mem (f := fun a =>
    (B.map fun b => if cov a b then F a b else 0).sum) ha)
  simp only [hc, ite_true] at h1
  exact h1.trans h2

/-- A sum of nonnegative terms over covering pairs vanishes only if every term does. -/
theorem eq_zero_of_pairSum_eq_zero {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ}
    {F : ℕ → ℕ → ℤ} (hF : ∀ a b, 0 ≤ F a b) (h0 : pairSum cov A B F = 0) {a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ B) (hc : cov a b) : F a b = 0 :=
  le_antisymm (h0 ▸ le_pairSum hF ha hb hc) (hF a b)

/-- A positive count of covering pairs has a covering pair. -/
theorem exists_covers_of_pairSum_pos {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ}
    (h : 0 < pairSum cov A B fun _ _ => (1 : ℤ)) : ∃ a ∈ A, ∃ b ∈ B, cov a b := by
  by_contra hno
  push Not at hno
  have : pairSum cov A B (fun _ _ => (1 : ℤ)) = 0 := by
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    refine List.sum_eq_zero fun z hz => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    simp [hno a ha b hb]
  omega

/-- A covering pair makes the count of covering pairs positive. -/
theorem pairSum_one_pos {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ} {a b : ℕ}
    (ha : a ∈ A)
    (hb : b ∈ B) (hc : cov a b) : 0 < pairSum cov A B fun _ _ => (1 : ℤ) :=
  lt_of_lt_of_le one_pos (le_pairSum (fun _ _ => zero_le_one) ha hb hc)

/-- Pair sums only depend on the relation between elements of the two lists. -/
theorem pairSum_congr {R : Type} [AddCommMonoid R] {cov cov' : ℕ → ℕ → Prop} [DecidableRel cov]
    [DecidableRel cov'] {A B : List ℕ} {F : ℕ → ℕ → R}
    (h : ∀ a ∈ A, ∀ b ∈ B, cov a b ↔ cov' a b) : pairSum cov A B F = pairSum cov' A B F := by
  simp only [pairSum]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  congr 1
  refine List.map_congr_left fun b hb => ?_
  simp only [h a ha b hb]

/-- Pair sums are linear in the summand. -/
theorem pairSum_add {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ} (F G : ℕ → ℕ → ℤ) :
    pairSum cov A B (fun a b => F a b + G a b) = pairSum cov A B F + pairSum cov A B G := by
  simp only [pairSum, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  congr 1
  refine List.map_congr_left fun b _ => ?_
  split_ifs <;> simp

/-- Pair sums commute with scalar multiplication. -/
theorem pairSum_mul {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ} (k : ℤ) (F : ℕ → ℕ → ℤ) :
    pairSum cov A B (fun a b => k * F a b) = k * pairSum cov A B F := by
  simp only [pairSum, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  congr 1
  refine List.map_congr_left fun b _ => ?_
  split_ifs <;> simp

/-- `∑ (a + b - c) ^ 2` from the six moments `∑ a ^ i * b ^ j`, `i + j ≤ 2`, over the pairs. -/
theorem pairSum_sq_eq (cov : ℕ → ℕ → Prop) [DecidableRel cov] (A B : List ℕ) (c : ℕ) :
    let M := pairSum cov A B
    M (fun a b => ((a : ℤ) + b - c) ^ 2) = M (fun a _ => (a : ℤ) ^ 2) + M (fun _ b => (b : ℤ) ^ 2) +
      2 * M (fun a b => (a : ℤ) * b) - 2 * c * M (fun a _ => (a : ℤ)) -
      2 * c * M (fun _ b => (b : ℤ)) + (c : ℤ) ^ 2 * M fun _ _ => 1 := by
  intro M
  have h : (fun a b : ℕ => ((a : ℤ) + b - c) ^ 2) = fun a b : ℕ =>
      ((((a : ℤ) ^ 2 + (b : ℤ) ^ 2) + 2 * ((a : ℤ) * b)) + (-(2 * c)) * (a : ℤ)) +
        ((-(2 * c)) * (b : ℤ) + (c : ℤ) ^ 2 * 1) := by
    funext a b; ring
  simp only [h, pairSum_add, pairSum_mul, M]
  ring

/-! ### Soundness and congruence -/

/-- **Soundness of the moment test**: if some pair of `A × B` is related by `cov` and every such
pair `(a, b)` has `(a + b - c) ^ 2 = 0`, then `c = a + b` for one of them. -/
theorem exists_add_eq_of_pairSum {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ} {c : ℕ}
    (hσ : 0 < pairSum cov A B fun _ _ => (1 : ℤ))
    (hτ : pairSum cov A B (fun a b => ((a : ℤ) + b - c) ^ 2) = 0) :
    ∃ a ∈ A, ∃ b ∈ B, cov a b ∧ a + b = c := by
  obtain ⟨a, ha, b, hb, hcov⟩ := exists_covers_of_pairSum_pos hσ
  have := eq_zero_of_pairSum_eq_zero (fun a b => sq_nonneg ((a : ℤ) + b - c)) hτ ha hb hcov
  refine ⟨a, ha, b, hb, hcov, ?_⟩
  have : ((a + b : ℕ) : ℤ) = c := by
    push_cast; linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this]
  exact_mod_cast this

/-- **Soundness of a trial**: if the trial accepts `c`, then `c = a + b` for some `a ∈ A` and
`b ∈ B`. -/
theorem exists_add_eq_of_accepts {d t : ℕ} {s : Seed p} {A B : List ℕ} {c : ℕ}
    (h : Accepts d t s A B c) : ∃ a ∈ A, ∃ b ∈ B, a + b = c := by
  obtain ⟨a, ha, b, hb, -, habc⟩ := exists_add_eq_of_pairSum h.2.1 h.2.2
  exact ⟨a, List.mem_of_mem_filter ha, b, List.mem_of_mem_filter hb, habc⟩

/-- **Hash values adding up are congruent**: if `ξ ≠ 0` in the field `ZMod p` and
`f a + g b = h c` as numbers, then `a + b ≡ c (mod p)`. -/
theorem natCast_add_eq_of_left_add_right [Fact p.Prime] {s : Seed p} (hξ : s.ξ ≠ 0) {a b c : ℕ}
    (hsum : s.left a + s.right b = s.target c) : ((a + b : ℕ) : ZMod p) = c := by
  have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hsum
  simp only [Nat.cast_add, Seed.left, Seed.right, Seed.target, ZMod.natCast_val,
    ZMod.cast_id', id] at hcast
  push_cast
  have : ((a : ZMod p) + b) * s.ξ = c * s.ξ := by linear_combination hcast
  exact mul_right_cancel₀ hξ this

/-- **Covering pairs are congruent to the query**: if `ξ ≠ 0` in the field `ZMod p` and the hashes
of `a`, `b` and `c` are below `2 ^ d`, a pair covering `c` satisfies `a + b ≡ c (mod p)`. -/
theorem natCast_add_eq_of_covers [Fact p.Prime] {d : ℕ} {s : Seed p} (hξ : s.ξ ≠ 0) {a b c : ℕ}
    (ha : s.left a < 2 ^ d) (hb : s.right b < 2 ^ d) (hc : s.target c < 2 ^ d)
    (h : Covers d s a b c) : ((a + b : ℕ) : ZMod p) = c :=
  natCast_add_eq_of_left_add_right hξ (add_eq_of_maskSet_union ha hb hc h.1 h.2)

/-! ### The trial as a program -/

/-- Keep the elements of `l` satisfying `P`, at one tick per element. -/
@[expose] def filterTickM {α : Type} (P : α → Prop) [DecidablePred P] (l : List α) :
    TimeM ℕ (List α) := do
  let r ← l.mapM fun x => do ✓ pure (if P x then some x else none)
  pure r.reduceOption

@[simp] theorem ret_filterTickM {α : Type} (P : α → Prop) [DecidablePred P] (l : List α) :
    (filterTickM P l).ret = l.filter fun x => decide (P x) := by
  simp only [filterTickM, ret_bind, ret_pure, ret_listMapM, List.reduceOption, List.filterMap_map,
    Function.id_comp]
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : P x <;> simp [h, ih]

@[simp] theorem time_filterTickM {α : Type} (P : α → Prop) [DecidablePred P] (l : List α) :
    (filterTickM P l).time = l.length := by
  simp [filterTickM]

section Sparse

variable {R : Type} [AddCommMonoid R]

/-- A dictionary from keys (sets of coordinates, or vectors) to `R`, built by adding the weight of
each entry of `kv` to the value of its key, at one tick per entry. -/
@[expose] def sparseM {κ : Type} [DecidableEq κ] (kv : List (κ × R)) : TimeM ℕ (κ → R) :=
  kv.foldlM (fun F e => do ✓ pure fun S => if S = e.1 then F S + e.2 else F S) 0

theorem ret_sparseM {κ : Type} [DecidableEq κ] (kv : List (κ × R)) (S : κ) :
    (sparseM kv).ret S = (kv.map fun e => if e.1 = S then e.2 else 0).sum := by
  rw [sparseM, ret_foldlM]
  suffices ∀ F₀ : κ → R, (kv.foldl (fun acc e =>
      ((do ✓ pure fun S => if S = e.1 then acc S + e.2 else acc S : TimeM ℕ _)).ret) F₀) S =
      F₀ S + (kv.map fun e => if e.1 = S then e.2 else 0).sum by
    simpa using this 0
  induction kv with
  | nil => simp
  | cons e kv ih =>
    intro F₀
    rw [List.foldl_cons, ih]
    simp only [ret_bind, ret_pure, List.map_cons, List.sum_cons]
    by_cases h : S = e.1
    · subst h; simp [add_assoc]
    · simp [h, Ne.symm h]

@[simp] theorem time_sparseM {κ : Type} [DecidableEq κ] (kv : List (κ × R)) :
    (sparseM kv).time = kv.length := by
  rw [sparseM, time_foldlM_of_time_eq _ _ _ (c := 1) fun _ _ => by simp, mul_one]

end Sparse

theorem covers_iff {d : ℕ} {S T X : Finset (Fin d)} :
    (S ⊆ X ∧ T = X \ S) ↔ (Disjoint S T ∧ S ∪ T = X) := by
  constructor
  · rintro ⟨hS, rfl⟩
    exact ⟨disjoint_sdiff, union_sdiff_of_subset hS⟩
  · rintro ⟨hd, rfl⟩
    exact ⟨subset_union_left, (union_sdiff_cancel_left hd).symm⟩

section Conv

variable {R : Type} [CommRing R]

/-- The subset convolution of two sparse dictionaries sums the products of the weights over the
pairs whose sets partition the query set. -/
theorem subsetConvolution_sparse {d : ℕ} (σ : Seed p) (As Bs : List ℕ) (w v : ℕ → R)
    (X : Finset (Fin d)) :
    subsetConvolution
        (fun S => (As.map fun a => if maskSet d (σ.left a) = S then w a else 0).sum)
        (fun S => (Bs.map fun b => if maskSet d (σ.right b) = S then v b else 0).sum) X =
      (As.map fun a => (Bs.map fun b =>
        if Disjoint (maskSet d (σ.left a)) (maskSet d (σ.right b)) ∧
          maskSet d (σ.left a) ∪ maskSet d (σ.right b) = X then w a * v b else 0).sum).sum := by
  induction As with
  | nil => simp [subsetConvolution]
  | cons a As ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    simp only [subsetConvolution, List.map_cons, List.sum_cons, add_mul, sum_add_distrib]
    congr 1
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq X.powerset (maskSet d (σ.left a))]
    split_ifs with hS
    · rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun b _ => ?_
      simp only [← covers_iff, mem_powerset.mp hS, true_and]
      split_ifs <;> simp
    · symm
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
      simp only [← covers_iff, mem_powerset.not.mp hS, false_and, ite_false]

/-- The selected-entries subset convolution of the trial: the left sets weighted by `w`, the right
sets weighted by `v`, read at the query sets `Q`. -/
@[expose] def convM (d s : ℕ) (σ : Seed p) (As Bs : List ℕ) (Q : List (Finset (Fin d)))
    (w v : ℕ → R) : TimeM ℕ (List R) := do
  let F ← sparseM (As.map fun a => (maskSet d (σ.left a), w a))
  let G ← sparseM (Bs.map fun b => (maskSet d (σ.right b), v b))
  solveM (List.finRange d) s F G Q

private theorem card_of_sparse_ne_zero {d t : ℕ} {l : List ℕ} {m : ℕ → Finset (Fin d)}
    {w : ℕ → R} (hl : ∀ a ∈ l, #(m a) = t) {S : Finset (Fin d)}
    (hS : (sparseM (l.map fun a => (m a, w a))).ret S ≠ 0) : #S = t := by
  rw [ret_sparseM] at hS
  obtain ⟨y, hy, hy0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hS
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  by_cases h : m a = S
  · rw [← h]; exact hl a ha
  · simp [h] at hy0

/-- **What the convolution of the trial returns** at the queries `Cs`: the pair sums of the weight
products. -/
theorem ret_convM {d t s : ℕ} (σ : Seed p) {As Bs Cs : List ℕ}
    (hA : ∀ a ∈ As, Ranked d t (σ.left a)) (hB : ∀ b ∈ Bs, Ranked d t (σ.right b))
    (hC : ∀ c ∈ Cs, Ranked d (2 * t) (σ.target c)) (hs : s ≤ 2 * t) (w v : ℕ → R) :
    (convM d s σ As Bs (Cs.map fun c => maskSet d (σ.target c)) w v).ret =
      Cs.map fun c => pairSum (Covers d σ · · c) As Bs fun a b => w a * v b := by
  simp only [convM, ret_bind]
  rw [ret_solveM (List.nodup_finRange d)
      (fun S hS => card_of_sparse_ne_zero (fun a ha => (hA a ha).2) hS)
      (fun S hS => card_of_sparse_ne_zero (fun b hb => (hB b hb).2) hS)
      (fun X hX => ?_) (by omega), List.map_map]
  · refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply]
    unfold pairSum Covers
    convert subsetConvolution_sparse (d := d) σ As Bs w v (maskSet d (σ.target c)) using 2 <;>
      first
        | rfl
        | (funext S; rw [ret_sparseM]; simp [List.map_map, Function.comp_def])
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hX
    refine ⟨fun i _ => by simp, ?_⟩
    rw [(hC c hc).2]; ring

@[simp] theorem time_convM {d t s : ℕ} (σ : Seed p) {As Bs Cs : List ℕ}
    (hC : ∀ c ∈ Cs, Ranked d (2 * t) (σ.target c)) (w v : ℕ → R) :
    (convM d s σ As Bs (Cs.map fun c => maskSet d (σ.target c)) w v).time =
      As.length + Bs.length + 3 * (d + 1) *
        (∑ j ∈ range (s + 1), d.choose j + Cs.length * ∑ j ∈ Icc s (2 * t), (2 * t).choose j) := by
  simp only [convM, time_bind, time_sparseM, List.length_map]
  rw [time_solveM (List.nodup_finRange d) s t _ _ (fun X hX => ?_), List.length_finRange,
    List.length_map]
  · ring
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hX
    exact ⟨fun i _ => by simp, (hC c hc).2⟩

end Conv

/-! ### Moments and the trial -/

/-- The six moments `∑ a ^ i * b ^ j` (`i + j ≤ 2`) of one query, as a vector: indices `0, …, 5`
hold the moments of `1, a, b, a b, a ^ 2, b ^ 2`. -/
abbrev Moments : Type := Fin 6 → ℤ

/-- The left weights `1, a, 1, a, a ^ 2, 1` of the six moments. -/
@[expose] def leftWeight (a : ℕ) : Moments := ![1, a, 1, a, (a : ℤ) ^ 2, 1]

/-- The right weights `1, 1, b, b, 1, b ^ 2` of the six moments. -/
@[expose] def rightWeight (b : ℕ) : Moments := ![1, 1, b, b, 1, (b : ℤ) ^ 2]

/-- The acceptance test on the moments `m` of the query `c`: `σ = m 0 > 0` and
`τ = m 4 + m 5 + 2 m 3 - 2 c m 1 - 2 c m 2 + c ^ 2 m 0 = 0`. -/
@[expose] def MomentTest (c : ℕ) (m : Moments) : Prop :=
  0 < m 0 ∧ m 4 + m 5 + 2 * m 3 - 2 * c * m 1 - 2 * c * m 2 + (c : ℤ) ^ 2 * m 0 = 0

instance (c : ℕ) (m : Moments) : Decidable (MomentTest c m) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem list_sum_apply {l : List ℕ} (f : ℕ → Moments) (i : Fin 6) :
    (l.map f).sum i = (l.map fun x => f x i).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- A coordinate of a vector-valued pair sum is the pair sum of the coordinates. -/
theorem pairSum_apply (cov : ℕ → ℕ → Prop) [DecidableRel cov] (A B : List ℕ)
    (F : ℕ → ℕ → Moments) (i : Fin 6) :
    pairSum cov A B F i = pairSum cov A B fun a b => F a b i := by
  simp only [pairSum, list_sum_apply]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  congr 1
  refine List.map_congr_left fun b _ => ?_
  split_ifs <;> rfl

/-- The moment test on the moments of the pairs of `A × B` related by `cov` is `σ > 0` and
`τ = 0` for these pairs. -/
theorem momentTest_iff (cov : ℕ → ℕ → Prop) [DecidableRel cov] (A B : List ℕ) (c : ℕ) :
    MomentTest c (pairSum cov A B fun a b => leftWeight a * rightWeight b) ↔
      0 < pairSum cov A B (fun _ _ => (1 : ℤ)) ∧
        pairSum cov A B (fun a b => ((a : ℤ) + b - c) ^ 2) = 0 := by
  simp only [MomentTest, pairSum_apply, Pi.mul_apply, leftWeight, rightWeight, pairSum_sq_eq]
  simp [mul_one, one_mul]

/-- **One trial**: the queries of `C` accepted under the seed `σ`, for isolated inputs `Ag`, `Bg`.
The six moments are computed by one selected-entries subset convolution over `ℤ ^ 6`. -/
@[expose] def trialM (d t s : ℕ) (σ : Seed p) (Ag Bg C : List ℕ) : TimeM ℕ (List ℕ) := do
  let As ← filterTickM (fun a => Ranked d t (σ.left a)) Ag
  let Bs ← filterTickM (fun b => Ranked d t (σ.right b)) Bg
  let Cs ← filterTickM (fun c => Ranked d (2 * t) (σ.target c)) C
  let ms ← convM d s σ As Bs (Cs.map fun c => maskSet d (σ.target c)) leftWeight rightWeight
  let acc ← filterTickM (fun row : ℕ × Moments => MomentTest row.1 row.2) (Cs.zip ms)
  pure (acc.map Prod.fst)

/-- Zipping a list with its image pairs each element with its value. -/
theorem zip_map_self {α γ : Type*} (l : List α) (g : α → γ) :
    l.zip (l.map g) = l.map fun a => (a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The starred inputs and the ranked queries of a trial, as the program computes them. -/
private theorem trial_filters {d t : ℕ} (σ : Seed p) (Ag Bg C : List ℕ) :
    (filterTickM (fun a => Ranked d t (σ.left a)) Ag).ret = starLeft d t σ Ag ∧
    (filterTickM (fun b => Ranked d t (σ.right b)) Bg).ret = starRight d t σ Bg ∧
    (filterTickM (fun c => Ranked d (2 * t) (σ.target c)) C).ret =
      C.filter (fun c => decide (Ranked d (2 * t) (σ.target c))) :=
  ⟨by rw [ret_filterTickM]; rfl, by rw [ret_filterTickM]; rfl, ret_filterTickM _ _⟩

/-- The convolution of a trial returns the moments of the starred inputs. -/
private theorem ret_convM_trial {d t s : ℕ} (σ : Seed p) (Ag Bg C : List ℕ) (hs : s ≤ 2 * t) :
    (convM d s σ (starLeft d t σ Ag) (starRight d t σ Bg)
      ((C.filter fun c => decide (Ranked d (2 * t) (σ.target c))).map
        fun c => maskSet d (σ.target c)) leftWeight rightWeight).ret =
      (C.filter fun c => decide (Ranked d (2 * t) (σ.target c))).map fun c =>
        pairSum (Covers d σ · · c) (starLeft d t σ Ag) (starRight d t σ Bg)
          fun a b => leftWeight a * rightWeight b :=
  ret_convM σ (fun a ha => by simpa using (List.mem_filter.mp ha).2)
    (fun b hb => by simpa using (List.mem_filter.mp hb).2)
    (fun c hc => by simpa using (List.mem_filter.mp hc).2) hs leftWeight rightWeight

/-- **What a trial returns**: the queries of `C` that it accepts, for every threshold
`s ≤ 2 t`. -/
theorem ret_trialM {d t s : ℕ} (σ : Seed p) (Ag Bg C : List ℕ) (hs : s ≤ 2 * t) :
    (trialM d t s σ Ag Bg C).ret = C.filter fun c => decide (Accepts d t σ Ag Bg c) := by
  obtain ⟨e₁, e₂, e₃⟩ := trial_filters (d := d) (t := t) σ Ag Bg C
  rw [trialM]
  simp only [ret_bind, ret_pure]
  rw [e₁, e₂, e₃, ret_convM_trial σ Ag Bg C hs, ret_filterTickM, zip_map_self, List.filter_map,
    List.map_map, List.filter_filter]
  rw [show (Prod.fst ∘ fun c => (c, pairSum (Covers d σ · · c) (starLeft d t σ Ag)
      (starRight d t σ Bg)
      fun a b => leftWeight a * rightWeight b)) = id from rfl, List.map_id]
  refine List.filter_congr fun c _ => ?_
  have := momentTest_iff (Covers d σ · · c) (starLeft d t σ Ag) (starRight d t σ Bg) c
  simp only [Function.comp_apply, Accepts, sigma, tau, ← this, Bool.decide_and, Bool.and_comm]

/-- **The cost of a trial**, exactly: one tick per element of `Ag`, `Bg` and `C`, one per element
of `A*`, `B*` and `C*` (dictionary insertions and the final test), and the preprocessing and the
`|C*|` queries of one selected-entries subset convolution over `ℤ ^ 6`. -/
theorem time_trialM {d t s : ℕ} (σ : Seed p) (Ag Bg C : List ℕ) (hs : s ≤ 2 * t) :
    (trialM d t s σ Ag Bg C).time = Ag.length + Bg.length + C.length +
      (starLeft d t σ Ag).length + (starRight d t σ Bg).length +
      (C.filter fun c => decide (Ranked d (2 * t) (σ.target c))).length +
      3 * (d + 1) * (∑ j ∈ range (s + 1), d.choose j +
        (C.filter fun c => decide (Ranked d (2 * t) (σ.target c))).length *
          ∑ j ∈ Icc s (2 * t), (2 * t).choose j) := by
  have hC : ∀ c ∈ C.filter (fun c => decide (Ranked d (2 * t) (σ.target c))),
      Ranked d (2 * t) (σ.target c) := fun c hc => by simpa using (List.mem_filter.mp hc).2
  have htconv := time_convM (s := s) σ (As := starLeft d t σ Ag) (Bs := starRight d t σ Bg) hC
    leftWeight rightWeight
  obtain ⟨e₁, e₂, e₃⟩ := trial_filters (d := d) (t := t) σ Ag Bg C
  rw [trialM]
  simp only [time_bind, time_pure]
  rw [e₁, e₂, e₃, htconv, ret_convM_trial σ Ag Bg C hs, time_filterTickM, time_filterTickM,
    time_filterTickM, time_filterTickM, zip_map_self, List.length_map]
  ring

/-! ### Witnesses -/

/-- A nonzero sum over covering pairs has a covering pair with a nonzero term. -/
theorem exists_of_pairSum_ne_zero {cov : ℕ → ℕ → Prop} [DecidableRel cov] {A B : List ℕ}
    {F : ℕ → ℕ → ℤ}
    (h : pairSum cov A B F ≠ 0) : ∃ a ∈ A, ∃ b ∈ B, cov a b ∧ F a b ≠ 0 := by
  obtain ⟨y, hy, hy0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero h
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  obtain ⟨z, hz, hz0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hy0
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
  by_cases hc : cov a b
  · exact ⟨a, ha, b, hb, hc, by simpa [hc] using hz0⟩
  · simp [hc] at hz0

/-- If the hashes of a witness `a + b = c` are below `p`, the target hash of `c` is their sum. -/
theorem target_eq_add {s : Seed p} {a b c : ℕ} (habc : a + b = c)
    (hlt : s.left a + s.right b < p) : s.target c = s.left a + s.right b := by
  have hp : NeZero p := ⟨by omega⟩
  unfold Seed.target
  rw [← ZMod.val_natCast_of_lt hlt]
  congr 1
  simp only [Seed.left, Seed.right, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id, ← habc]
  ring

/-- **A witness with disjoint ranked hashes** (the event of the completeness analysis of
[ChanItakuraMaYu2026], Theorem 2.3): if `a ∈ A`, `b ∈ B`, `a + b = c`, the hashes `f a`, `g b`
have `t` binary digits `1` each below `2 ^ d` and no common digit, and `2 ^ d ≤ p`, then the trial
accepts `c` unless some covering pair of `A* × B*` sums to a number other than `c`. -/
theorem accepts_or_exists_covers_ne {d t : ℕ} (hp : 2 ^ d ≤ p) {s : Seed p} {A B : List ℕ}
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hx : Ranked d t (s.left a))
    (hy : Ranked d t (s.right b)) (hxy : Disjoint (maskSet d (s.left a)) (maskSet d (s.right b))) :
    Accepts d t s A B c ∨ ∃ a' ∈ starLeft d t s A, ∃ b' ∈ starRight d t s B,
      Covers d s a' b' c ∧ a' + b' ≠ c := by
  obtain ⟨hlt, hmask⟩ := maskSet_add hx.1 hy.1 hxy
  have htarget := target_eq_add habc (hlt.trans_le hp)
  have hcov : Covers d s a b c := ⟨hxy, by rw [htarget, hmask]⟩
  have haS : a ∈ starLeft d t s A := List.mem_filter.mpr ⟨ha, by simpa using hx⟩
  have hbS : b ∈ starRight d t s B := List.mem_filter.mpr ⟨hb, by simpa using hy⟩
  by_cases hτ : tau d t s A B c = 0
  · refine Or.inl ⟨⟨htarget ▸ hlt, ?_⟩, pairSum_one_pos haS hbS hcov, hτ⟩
    rw [htarget, hmask, card_union_of_disjoint hxy, hx.2, hy.2]; ring
  · obtain ⟨a', ha', b', hb', hc', hne⟩ := exists_of_pairSum_ne_zero hτ
    refine Or.inr ⟨a', ha', b', hb', hc', fun h => hne ?_⟩
    rw [← h]; push_cast; ring

end Cslib.Algorithms.Lean.SubsetConvThreeSum


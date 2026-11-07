/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.Simon
import Complexity.Foundations.Data.BitString.Parity.DotProduct

/-!
# Simon's algorithm finds the hidden string

The **search version of Simon's problem** ([Simon][Simon1997], [de Wolf, §3.2][deWolf2019]) asks
for the hidden string `s` itself, for `f : {0,1}^n → {0,1}^n` with the promise that `f(a) = f(b)`
exactly when `b ∈ {a, a ⊕ s}` (`Cslib.QueryComplexity.SimonPromise`). As in
`Complexity/Computability/QueryComplexity/Quantum/Simon.lean`, the input is the truth table
`X : Fin N → Bool` of the `N = n 2^n` output bits of `f`, and queries are bit queries.

**The algorithm.** Simon's algorithm with `m` rounds (`Cslib.Quantum.simonAlg`) measures `m` rows
`z_1, …, z_m ∈ {0,1}^n`, and the classical post-processing `Cslib.Quantum.simonSolve` outputs the
unique nonzero string orthogonal to all of them, or `0` if there is none or more than one. It
outputs `s` whenever the strings orthogonal to all rows are exactly `0` and `s`
(`Cslib.Quantum.SimonDetermines`, `Cslib.Quantum.simonSolve_eq`).

**Analysis.** Every measured row is orthogonal to `s`, so the post-processing fails only if some
`w ∉ {0, s}` is orthogonal to all rows. For `s = 0` this is the acceptance event of the decision
version, of probability at most `(2^n - 1) / 2^m`
(`Cslib.Quantum.measureProb_simonAlg_le_of_injective`). For `s ≠ 0` every fiber of `f`, applied
rowwise to `m` rows, has at most `2^m` elements (`Cslib.Quantum.card_simonG_fiber_le`), so each
row matrix is measured with probability at most `2^m / 2^{mn}`
(`Cslib.Quantum.measureProb_simonAlg_le`); and two distinct nonzero strings `s, w` are both
orthogonal to all `m` rows of exactly `2^{nm} / 4^m` row matrices
(`Cslib.BitString.card_kernel_pair`). A union bound over the `2^n - 2` strings `w`
gives failure probability at most `(2^n - 1) / 2^m` again
(`Cslib.Quantum.measureProb_not_simonDetermines_le`). So the algorithm finds `s` with probability
at least `1 - (2^n - 1) / 2^m` on every promise input (`Cslib.Quantum.measureProb_simonFound`), and
with `m = n + 2` rounds, `n (n + 2)` bit queries find `s` with probability above `3/4`
(`Cslib.Quantum.simonAlg_search_spec`).

**The separation.** Every randomized decision tree finding `s` with error `1/3` decides Simon's
problem after answering whether its output is nonzero, so it has depth `q` with `2^n ≤ q²`
(`Cslib.QueryComplexity.simon_search_two_pow_le_depth_sq`). This gives the exponential separation
for the search version (`Cslib.Quantum.simon_search_separation`). Both sides count bit queries.

**Source mapping.** de Wolf §3.2 repeats the subroutine `O(n)` times until the measured rows span
`s^⊥`, then solves the linear system. Here the `m` rounds run side by side in one bit-query
algorithm, and the bound `1 - (2^n - 1) / 2^m`, which also covers `s = 0`, is formulated here. The
post-processing `Cslib.Quantum.simonSolve` searches all `2^n` strings; it makes no queries, so it
does not affect the query count, but polynomial-time post-processing by Gaussian elimination is
not formalized.

## Main definitions

* `Cslib.Quantum.simonSolve`: the classical post-processing.
* `Cslib.Quantum.SimonDetermines`: the measured rows determine the hidden string.
* `Cslib.Quantum.simonFound`: the outcomes on which the post-processing outputs `s`.

## Main results

* `Cslib.Quantum.card_simonG_fiber_le`: under the promise, the fibers of `f` applied rowwise to
  `m` rows have at most `2^m` elements.
* `Cslib.Quantum.measureProb_not_simonDetermines_le`: the rows fail to determine `s ≠ 0` with
  probability at most `(2^n - 1) / 2^m`.
* `Cslib.Quantum.measureProb_simonFound`: Simon's algorithm finds `s` with probability at least
  `1 - (2^n - 1) / 2^m`.
* `Cslib.Quantum.simonAlg_search_spec`: `n (n + 2)` bit queries find `s` with probability above
  `3/4`.
* `Cslib.Quantum.simon_search_separation`: the exponential separation for the search version.

## References

* [D. R. Simon, *On the Power of Quantum Computation*][Simon1997]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §3.2
-/

public section

namespace Cslib.Quantum

open Finset BitString QueryComplexity

variable {N n m : ℕ}

/-! ### The classical post-processing -/

/-- The nonzero strings orthogonal to every row `z_r` of the row matrix `zs`. -/
def simonSolutions (zs : Fin m × Fin n → Bool) : Finset (Fin n → Bool) :=
  univ.filter fun w => w ≠ 0 ∧ ∀ r, Function.curry zs r ⬝ᵥ w = false

/-- **The classical post-processing of Simon's algorithm**: the unique nonzero string orthogonal to
every measured row (the sum of the one-element set `Cslib.Quantum.simonSolutions zs`), or `0` if
there is none or more than one. It searches all `2^n` strings and makes no queries. -/
def simonSolve (zs : Fin m × Fin n → Bool) : Fin n → Bool :=
  if #(simonSolutions zs) = 1 then ∑ w ∈ simonSolutions zs, w else 0

/-- The measured rows `zs` **determine** the hidden string `s`: the strings orthogonal to every row
are exactly `0` and `s`. -/
@[expose] def SimonDetermines (zs : Fin m × Fin n → Bool) (s : Fin n → Bool) : Prop :=
  ∀ w, (∀ r, Function.curry zs r ⬝ᵥ w = false) ↔ w = 0 ∨ w = s

instance (zs : Fin m × Fin n → Bool) (s : Fin n → Bool) : Decidable (SimonDetermines zs s) :=
  inferInstanceAs (Decidable (∀ _, _ ↔ _))

/-- **The post-processing outputs the hidden string** when the rows determine it. -/
theorem simonSolve_eq {zs : Fin m × Fin n → Bool} {s : Fin n → Bool}
    (h : SimonDetermines zs s) : simonSolve zs = s := by
  by_cases hs : s = 0
  · subst hs
    have he : simonSolutions zs = ∅ := filter_eq_empty_iff.mpr fun w _ hw =>
      hw.1 ((or_self _).mp ((h w).mp hw.2))
    simp [simonSolve, he]
  · have he : simonSolutions zs = {s} := by
      ext w
      simp only [simonSolutions, mem_filter, mem_univ, true_and, mem_singleton]
      refine ⟨fun hw => ((h w).mp hw.2).resolve_left hw.1, ?_⟩
      rintro rfl
      exact ⟨hs, (h w).mpr (Or.inr rfl)⟩
    simp [simonSolve, he]

/-- The outcomes of Simon's algorithm on which the post-processing outputs `s`. -/
def simonFound (m : ℕ) (s : Fin n → Bool) : Finset (Fin N × Bool × SimonWork m n) :=
  univ.filter fun p => simonSolve p.2.2.1 = s

@[simp] theorem mem_simonFound {s : Fin n → Bool} {p : Fin N × Bool × SimonWork m n} :
    p ∈ simonFound m s ↔ simonSolve p.2.2.1 = s := by
  simp [simonFound]

/-! ### The analysis -/

/-- **The fibers of `f` applied rowwise.** Under Simon's promise, each row of a preimage of `ys` is
one of the two preimages of the corresponding row of `ys`, so the fibers have at most `2^m`
elements. -/
theorem card_simonG_fiber_le {E : Fin N ≃ (Fin n → Bool) × Fin n} {X : Fin N → Bool}
    {s : Fin n → Bool} (hX : SimonPromise (simonFun E X) s) (ys : Fin m × Fin n → Bool) :
    #{a | simonG (m := m) E X a = ys} ≤ 2 ^ m := by
  classical
  rcases (univ.filter fun a => simonG (m := m) E X a = ys).eq_empty_or_nonempty with he | ⟨a₀, ha₀⟩
  · rw [he, card_empty]
    exact Nat.zero_le _
  have hrow : ∀ a ∈ (univ.filter fun a => simonG (m := m) E X a = ys), ∀ r,
      Function.curry a r = Function.curry a₀ r ∨
        Function.curry a r = Function.curry a₀ r + s := by
    intro a ha r
    have hval : simonFun E X (Function.curry a₀ r) = simonFun E X (Function.curry a r) :=
      funext fun j => by
        rw [← simonG_apply E X a₀ (r, j), ← simonG_apply E X a (r, j), (mem_filter.mp ha₀).2,
          (mem_filter.mp ha).2]
    exact (hX _ _).mp hval
  have hinj : Set.InjOn (fun a (r : Fin m) => decide (Function.curry a r = Function.curry a₀ r))
      (univ.filter fun a => simonG (m := m) E X a = ys : Finset _) := by
    intro a ha b hb hab
    have ha' := mem_coe.mp ha
    have hb' := mem_coe.mp hb
    funext k
    have hk := congrFun hab k.1
    simp only [decide_eq_decide] at hk
    have hcur : Function.curry a k.1 = Function.curry b k.1 := by
      by_cases h : Function.curry a k.1 = Function.curry a₀ k.1
      · exact h.trans (hk.mp h).symm
      · have hb0 : Function.curry b k.1 ≠ Function.curry a₀ k.1 := fun h' => h (hk.mpr h')
        exact ((hrow a ha' k.1).resolve_left h).trans ((hrow b hb' k.1).resolve_left hb0).symm
    exact congrFun hcur k.2
  have h := card_le_card_of_injOn _ (fun _ _ => mem_univ _) hinj
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using h

/-- **The rows rarely fail to determine a nonzero hidden string**: for `s ≠ 0` they fail with
probability at most `(2^n - 1) / 2^m`. -/
theorem measureProb_not_simonDetermines_le (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    {X : Fin N → Bool} {s : Fin n → Bool} (hX : SimonPromise (simonFun E X) s) (hs : s ≠ 0) :
    measureProb (run (simonAlg m E i₀) (simonInit i₀) X (m * n))
        (univ.filter fun p => ¬SimonDetermines p.2.2.1 s) ≤
      (2 ^ n - 1) / 2 ^ m := by
  classical
  set Z : Finset (Fin m × Fin n → Bool) := univ.filter fun zs => ¬SimonDetermines zs s with hZ
  have hfilt : (univ.filter fun p : Fin N × Bool × SimonWork m n => ¬SimonDetermines p.2.2.1 s) =
      univ.filter fun p => p.2.2.1 ∈ Z := by
    ext p
    simp [hZ]
  -- the row matrices orthogonal to `s` that do not determine `s`
  set T : Finset (Fin m × Fin n → Bool) := univ.filter fun zs => ∃ w : Fin n → Bool,
    w ≠ 0 ∧ w ≠ s ∧ ∀ r, Function.curry zs r ⬝ᵥ s = false ∧ Function.curry zs r ⬝ᵥ w = false
    with hT
  have hsub : (Z.filter fun zs => ∀ r, Function.curry zs r ⬝ᵥ s = false) ⊆ T := by
    intro zs hzs
    obtain ⟨hzZ, hzs⟩ := mem_filter.mp hzs
    have hnd : ¬SimonDetermines zs s := (mem_filter.mp hzZ).2
    simp only [SimonDetermines, not_forall] at hnd
    obtain ⟨w, hw⟩ := hnd
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hw ⟨fun _ => Or.inl rfl, fun _ r => by simp [Bool.zero_eq_false]⟩
    have hws : w ≠ s := by
      rintro rfl
      exact hw ⟨fun _ => Or.inr rfl, fun _ => hzs⟩
    have hwo : ∀ r, Function.curry zs r ⬝ᵥ w = false := by
      by_contra hc
      exact hw ⟨fun h => absurd h hc, fun h => h.elim (fun h0 => absurd h0 hw0)
        (fun h1 => absurd h1 hws)⟩
    exact mem_filter.mpr ⟨mem_univ _, w, hw0, hws, fun r => ⟨hzs r, hwo r⟩⟩
  have hTsub : T ⊆ ((univ.erase (0 : Fin n → Bool)).erase s).biUnion fun w =>
      (univ.filter fun zs : Fin m × Fin n → Bool => ∀ r,
        Function.curry zs r ⬝ᵥ s = false ∧ Function.curry zs r ⬝ᵥ w = false) := by
    intro zs hzs
    obtain ⟨w, hw0, hws, hw⟩ := (mem_filter.mp hzs).2
    exact mem_biUnion.mpr ⟨w, mem_erase.mpr ⟨hws, mem_erase.mpr ⟨hw0, mem_univ _⟩⟩,
      mem_filter.mpr ⟨mem_univ _, hw⟩⟩
  have hpair : ∀ w ∈ (univ.erase (0 : Fin n → Bool)).erase s,
      #(univ.filter fun zs : Fin m × Fin n → Bool => ∀ r,
        Function.curry zs r ⬝ᵥ s = false ∧ Function.curry zs r ⬝ᵥ w = false) * 4 ^ m =
        2 ^ (m * n) := by
    intro w hw
    obtain ⟨hws, hw0⟩ := mem_erase.mp hw
    have h := card_kernel_pair (c := m) hs (mem_erase.mp hw0).1 (Ne.symm hws)
    rw [mul_comm m n, ← h]
    congr 1
    exact card_equiv (Equiv.curry _ _ _) fun zs => by simp
  have hcard : #T * 4 ^ m ≤ (2 ^ n - 1) * 2 ^ (m * n) := by
    calc #T * 4 ^ m
        ≤ (∑ w ∈ (univ.erase (0 : Fin n → Bool)).erase s,
            #(univ.filter fun zs : Fin m × Fin n → Bool => ∀ r,
              Function.curry zs r ⬝ᵥ s = false ∧ Function.curry zs r ⬝ᵥ w = false)) * 4 ^ m :=
          Nat.mul_le_mul_right _ ((card_le_card hTsub).trans card_biUnion_le)
      _ = ∑ w ∈ (univ.erase (0 : Fin n → Bool)).erase s, 2 ^ (m * n) := by
          rw [sum_mul]
          exact sum_congr rfl hpair
      _ ≤ ∑ w ∈ univ.erase (0 : Fin n → Bool), 2 ^ (m * n) :=
          sum_le_sum_of_subset (erase_subset _ _)
      _ = (2 ^ n - 1) * 2 ^ (m * n) := by
          rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin, smul_eq_mul]
  have hreal : (#T : ℝ) * (2 ^ m * 2 ^ m) ≤ (2 ^ n - 1) * 2 ^ (m * n) := by
    have h1 : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      ring
    rw [← mul_pow, ← h1]
    exact_mod_cast hcard
  have h := measureProb_simonAlg_le E i₀ hX (card_simonG_fiber_le hX) Z
  rw [hfilt]
  refine h.trans ?_
  have hT' : (#(Z.filter fun zs => ∀ r, Function.curry zs r ⬝ᵥ s = false) : ℝ) ≤ #T := by
    exact_mod_cast card_le_card hsub
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpos : (0 : ℝ) ≤ 2 ^ m := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hT' hpos]

/-- The probability of `S` is at least one minus that of a set `T` containing the complement of `S`,
for a unit state. -/
private theorem one_sub_le_measureProb {ι : Type*} [Fintype ι] {ψ : EuclideanSpace ℂ ι}
    (hψ : measureProb ψ univ = 1) {S T : Finset ι} (hST : ∀ p, p ∉ S → p ∈ T) :
    1 - measureProb ψ T ≤ measureProb ψ S := by
  classical
  have hsplit := sum_add_sum_compl S fun p => ‖ψ.ofLp p‖ ^ 2
  have hcT : measureProb ψ Sᶜ ≤ measureProb ψ T :=
    sum_le_sum_of_subset_of_nonneg (fun p hp => hST p (mem_compl.mp hp)) fun _ _ _ => by
      positivity
  simp only [measureProb] at hψ hcT ⊢
  linarith

/-- **Simon's algorithm finds the hidden string**: on every promise input, including `s = 0`, the
post-processing of the measured rows outputs `s` with probability at least `1 - (2^n - 1) / 2^m`.
-/
theorem measureProb_simonFound (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N)
    {X : Fin N → Bool} {s : Fin n → Bool} (hX : SimonPromise (simonFun E X) s) :
    1 - (2 ^ n - 1) / 2 ^ m ≤
      measureProb (run (simonAlg m E i₀) (simonInit i₀) X (m * n)) (simonFound m s) := by
  classical
  have h1 : measureProb (run (simonAlg m E i₀) (simonInit i₀) X (m * n)) univ = 1 := by
    rw [measureProb_univ, norm_run, norm_simonInit, one_pow]
  by_cases hs : s = 0
  · subst hs
    have hf := (simonPromise_zero_iff _).mp hX
    refine le_trans ?_ (one_sub_le_measureProb h1 (T := simonAccept m n) fun p hp => ?_)
    · linarith [measureProb_simonAlg_le_of_injective (m := m) E i₀ hf]
    · rw [mem_simonFound] at hp
      by_contra hacc
      refine hp (simonSolve_eq fun w => ⟨fun hw => Or.inl ?_, ?_⟩)
      · by_contra hw0
        exact hacc (mem_simonAccept.mpr ⟨w, hw0, hw⟩)
      · rintro (rfl | rfl) <;> exact fun r => by simp [Bool.zero_eq_false]
  · refine le_trans ?_ (one_sub_le_measureProb h1
      (T := univ.filter fun p => ¬SimonDetermines p.2.2.1 s) fun p hp => ?_)
    · linarith [measureProb_not_simonDetermines_le (m := m) E i₀ hX hs]
    · rw [mem_simonFound] at hp
      exact mem_filter.mpr ⟨mem_univ _, fun hd => hp (simonSolve_eq hd)⟩

/-- **Simon's algorithm solves the search version with `n (n + 2)` bit queries**: from a unit
initial state, with `n + 2` rounds, the post-processing of the measured rows outputs the hidden
string with probability above `3/4` on every promise input. -/
theorem simonAlg_search_spec (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) :
    ‖(simonInit i₀ : State N (SimonWork (n + 2) n))‖ = 1 ∧
      ∀ X s, SimonPromise (simonFun E X) s →
        3 / 4 < measureProb (run (simonAlg (n + 2) E i₀) (simonInit i₀) X ((n + 2) * n))
          (simonFound (n + 2) s) := by
  refine ⟨norm_simonInit _, fun X s hX => lt_of_lt_of_le ?_ (measureProb_simonFound E i₀ hX)⟩
  have h : ((2 : ℝ) ^ n - 1) / 2 ^ (n + 2) < 1 / 4 := by
    rw [div_lt_iff₀ (by positivity), pow_add]
    linarith
  linarith

/-- **The exponential quantum–classical separation for the search version of Simon's problem**,
in the bit-query model on the truth table `X : Fin N → Bool` of `f : {0,1}^n → {0,1}^n`, for
`n ≥ 1`: Simon's algorithm with classical post-processing finds the hidden string with `n (n + 2)`
queries and probability above `3/4`, while every randomized decision tree finding it with error
`1/3` (as the restriction to the promise inputs of a total function `S`) has depth `q` with
`2^n ≤ q²`. -/
theorem simon_search_separation (E : Fin N ≃ (Fin n → Bool) × Fin n) (i₀ : Fin N) (hn : 1 ≤ n) :
    (∀ X s, SimonPromise (simonFun E X) s →
      3 / 4 < measureProb (run (simonAlg (n + 2) E i₀) (simonInit i₀) X ((n + 2) * n))
        (simonFound (n + 2) s)) ∧
    ∀ (μ : RandomizedDecisionTree (Fin N) (Fin n → Bool)) (S : (Fin N → Bool) → Fin n → Bool),
      (∀ X s, SimonPromise (simonFun E X) s → S X = s) →
      (∀ X s, SimonPromise (simonFun E X) s → μ.errorProb S X ≤ 1 / 3) →
      2 ^ n ≤ μ.depth ^ 2 :=
  ⟨(simonAlg_search_spec E i₀).2, fun μ S hS hμ => simon_search_two_pow_le_depth_sq E μ S hS hμ hn⟩

end Cslib.Quantum

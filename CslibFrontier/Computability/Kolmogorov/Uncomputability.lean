/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.Partrec
public import Mathlib.Order.Filter.Cofinite
import CslibFrontier.Computability.Kolmogorov.Incompressibility
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Growth and uncomputability of plain Kolmogorov complexity

For every description method only finitely many objects have complexity below any given bound
(`eventually_natCast_le_ecomplexity`), so the plain complexity `K(x)` of natural numbers under the
universal description method tends to infinity (`tendsto_complexity_universal`). No computable
unbounded function is a lower bound for `K`: such a function exceeds `K` at some argument
(`exists_complexity_universal_lt_of_computable`), and hence at infinitely many
(`frequently_complexity_universal_lt_of_computable`). In particular `K` is not computable
(`not_computable_complexity_universal`). The proof is Berry's paradox: if `f ≤ K` were
computable and unbounded, the program "the least `x` with `f x ≥ 2 |q|`", run on an input `q`,
would describe a number of complexity at least `2 |q|` by `|q| + O(1)` bits
[Li and Vitányi, Chapter 2][LiVitanyi2019].

The same invariance argument, applied to total computable decoders, shows that
`K(g p) ≤ |p| + O(1)` for every computable `g : List Bool → ℕ`
(`exists_complexity_universal_le_length_add`). Consequently `K(x) ≤ log₂ x + O(1)`
(`exists_complexity_universal_le_size_add`), and computable maps increase `K` by at most a
constant (`exists_complexity_universal_comp_le`).

The statements use the `ℕ`-valued complexity, which is the genuine plain complexity for the
universal method (`natCast_complexity_universal`). The `ℕ∞`-valued complexity does not tend to
`⊤` along the cofinite filter (`not_tendsto_ecomplexity_universal`), because it is never `⊤`.
Following the rest of the library, `K` denotes the plain complexity, which Li and Vitányi write
`C`, reserving `K` for the prefix complexity.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.eventually_natCast_le_ecomplexity`: all but finitely many
  objects have complexity at least `k`, for every description method.
* `Cslib.Kolmogorov.DescriptionMethod.tendsto_complexity_universal`: `K(x) → ∞`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_le_length_add`:
  `K(g p) ≤ |p| + O(1)` for computable `g`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_le_size_add`:
  `K(x) ≤ log₂ x + O(1)`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_comp_le`:
  `K(f x) ≤ K(x) + O(1)` for computable `f`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_lt_of_computable`: no computable
  unbounded function is a lower bound for `K`.
* `Cslib.Kolmogorov.DescriptionMethod.frequently_complexity_universal_lt_of_computable`: a
  computable unbounded function exceeds `K` infinitely often.
* `Cslib.Kolmogorov.DescriptionMethod.not_computable_complexity_universal`: `K` is not computable.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

public section

namespace Cslib.Kolmogorov.DescriptionMethod

open Filter

/-! ### Growth -/

/-- For every description method and every `k`, all but finitely many objects have complexity at
least `k`: fewer than `2 ^ k` objects have complexity below `k`. -/
theorem eventually_natCast_le_ecomplexity {α : Type*} (M : DescriptionMethod α) (k : ℕ) :
    ∀ᶠ x in cofinite, (k : ℕ∞) ≤ M.ecomplexity x := by
  rw [eventually_cofinite]
  refine (Set.finite_of_encard_le_coe (s := {x | M.ecomplexity x < k}) (k := 2 ^ k) ?_).subset
    fun x hx => not_le.mp hx
  exact_mod_cast (M.encard_setOf_ecomplexity_lt k).le

/-- The plain complexity of natural numbers under the universal method tends to infinity. -/
theorem tendsto_complexity_universal : Tendsto universal.complexity atTop atTop := by
  refine tendsto_atTop.2 fun k => ?_
  rw [← Nat.cofinite_eq_atTop]
  refine (universal.eventually_natCast_le_ecomplexity k).mono fun x hx => ?_
  rwa [← natCast_complexity_universal, Nat.cast_le] at hx

/-- The `ℕ∞`-valued complexity under the universal method does not tend to `⊤`, since it is never
`⊤`; this is why `tendsto_complexity_universal` is stated for the `ℕ`-valued complexity. -/
theorem not_tendsto_ecomplexity_universal :
    ¬ Tendsto universal.ecomplexity cofinite atTop := fun h =>
  let ⟨x, hx⟩ := (tendsto_atTop.1 h ⊤).exists
  ecomplexity_universal_ne_top x (top_le_iff.1 hx)

/-- Every bound is exceeded by the complexity of some natural number. -/
theorem exists_le_complexity_universal (k : ℕ) : ∃ x : ℕ, k ≤ universal.complexity x :=
  (tendsto_atTop.1 tendsto_complexity_universal k).exists

/-! ### Upper bounds from computable decoders -/

/-- **Total computable decoders.** If `g` is computable, the complexity of `g p` exceeds the length
of `p` by at most a constant: the description method running `g` is partial recursive, and the
universal method is at most a constant worse than it. -/
theorem exists_complexity_universal_le_length_add {g : List Bool → ℕ} (hg : Computable g) :
    ∃ c : ℕ, ∀ p, universal.complexity (g p) ≤ p.length + c := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_universal_le_of_partrec_eval (M := literal) Partrec.some
    (fun p x => by rw [literal_produces, Part.mem_some_iff, eq_comm]) hg
  refine ⟨c, fun p => ?_⟩
  have h := hc p
  rw [ecomplexity_literal, ← natCast_complexity_universal] at h
  exact_mod_cast h

/-- `K(x) ≤ log₂ x + O(1)`: a number is described by its binary representation, of length
`Nat.size x`. -/
theorem exists_complexity_universal_le_size_add :
    ∃ c : ℕ, ∀ x : ℕ, universal.complexity x ≤ x.size + c := by
  obtain ⟨c, hc⟩ := exists_complexity_universal_le_length_add Primrec.list_foldr_nat_bit.to_comp
  refine ⟨c, fun x => ?_⟩
  simpa only [Nat.foldr_bit_bits, ← Nat.size_eq_bits_len] using hc x.bits

/-- **Computable maps increase complexity by at most a constant**: `K(f x) ≤ K(x) + O(1)` for
every computable `f`. Composing `f` with the universal method is a partial recursive description
method. -/
theorem exists_complexity_universal_comp_le {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : ℕ, ∀ x, universal.complexity (f x) ≤ universal.complexity x + c := by
  obtain ⟨F, hF, hU⟩ := isPartrec_universal
  obtain ⟨c, hc⟩ := exists_ecomplexity_universal_le_of_partrec_eval hF hU hf
  refine ⟨c, fun x => ?_⟩
  have h := hc x
  rw [← natCast_complexity_universal, ← natCast_complexity_universal] at h
  exact_mod_cast h

/-! ### Uncomputability -/

/-- **No computable unbounded lower bound.** A computable unbounded function exceeds the plain
complexity somewhere. Otherwise the search for the least `x` with `f x ≥ 2 |q|` would be a total
computable decoder producing, from a program `q` of length `c + 1`, a number of complexity at least
`2 (c + 1)` but at most `(c + 1) + c` (Berry's paradox). -/
theorem exists_complexity_universal_lt_of_computable {f : ℕ → ℕ} (hf : Computable f)
    (hunb : ∀ k, ∃ x, k ≤ f x) : ∃ x, universal.complexity x < f x := by
  by_contra! hle
  let F : List Bool →. ℕ := fun q => Nat.rfind fun x => decide (2 * q.length ≤ f x)
  have hdec : Computable₂ fun (q : List Bool) (x : ℕ) => decide (2 * q.length ≤ f x) :=
    (Primrec.nat_le.decide.to_comp).comp
      (Primrec.nat_double.to_comp.comp (Computable.list_length.comp Computable.fst))
      (hf.comp Computable.snd)
  have hF : Partrec F := Partrec.rfind hdec.partrec₂
  have hdom (q : List Bool) : (F q).Dom := by
    obtain ⟨x, hx⟩ := hunb (2 * q.length)
    obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun x => decide (2 * q.length ≤ f x)) (m := x)
      (decide_eq_true hx)
    exact Part.dom_iff_mem.mpr ⟨n, hn⟩
  let g (q : List Bool) : ℕ := (F q).get (hdom q)
  have hg : Computable g := hF.of_eq fun q => (Part.some_get (hdom q)).symm
  obtain ⟨c, hc⟩ := exists_complexity_universal_le_length_add hg
  let q : List Bool := List.replicate (c + 1) true
  have hq : q.length = c + 1 := List.length_replicate
  have hspec : 2 * q.length ≤ f (g q) := by
    simpa using Nat.rfind_spec (Part.get_mem (hdom q))
  have := hle (g q)
  have := hc q
  omega

/-- A computable unbounded function exceeds the plain complexity at infinitely many arguments:
beyond any `N`, apply `exists_complexity_universal_lt_of_computable` to the function that vanishes
below `N` and agrees with `f` from `N` on. -/
theorem frequently_complexity_universal_lt_of_computable {f : ℕ → ℕ} (hf : Computable f)
    (hunb : ∀ k, ∃ x, k ≤ f x) : ∃ᶠ x in atTop, universal.complexity x < f x := by
  refine frequently_atTop.2 fun N => ?_
  let g (x : ℕ) : ℕ := if x < N then 0 else f x
  have hc : Computable fun x : ℕ => decide (x < N) :=
    Primrec.nat_lt.decide.to_comp.comp Computable.id (Computable.const N)
  have hg : Computable g :=
    (Computable.cond hc (Computable.const 0) hf).of_eq fun x => by
      by_cases h : x < N <;> simp [g, h]
  have hgunb (k : ℕ) : ∃ x, k ≤ g x := by
    obtain ⟨x, hx⟩ := hunb (k + 1 + ∑ y ∈ Finset.range N, f y)
    refine ⟨x, ?_⟩
    by_cases h : x < N
    · have := Finset.single_le_sum (fun y _ => Nat.zero_le (f y)) (Finset.mem_range.2 h)
      omega
    · simp only [g, h, ↓reduceIte]
      omega
  obtain ⟨x, hx⟩ := exists_complexity_universal_lt_of_computable hg hgunb
  by_cases h : x < N
  · simp [g, h] at hx
  · simp only [g, h, ↓reduceIte] at hx
    exact ⟨x, by omega, hx⟩

/-- **The plain Kolmogorov complexity is not computable.** -/
theorem not_computable_complexity_universal : ¬ Computable universal.complexity := fun h =>
  let ⟨_, hx⟩ := exists_complexity_universal_lt_of_computable h exists_le_complexity_universal
  lt_irrefl _ hx

end Cslib.Kolmogorov.DescriptionMethod

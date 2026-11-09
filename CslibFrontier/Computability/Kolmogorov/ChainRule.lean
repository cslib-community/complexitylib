/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.Basic
public import CslibFrontier.Computability.Kolmogorov.SelfDelimiting

/-!
# Conditional complexity and the chain rule

A *conditional description method* for `α` given `β` is a family `N : β → DescriptionMethod α`:
the description method `N y` has access to the condition `y`. The conditional complexity
`C_N(x | y)` is `(N y).ecomplexity x`, and its time-bounded version `C_N^t(x | y)` is
`(N y).etimeBoundedComplexity t x`. All results about description methods apply to them for a fixed
condition; for instance fewer than `2 ^ r` objects have `C_N(x | y) < r`, for every `y`.

A *composition* of a description method `M` and a conditional description method `N` into a
description method `J` along a pairing `pair` combines a program for `x` under `M` and a program
for `y` given `x` under `N x` into a program for `pair x y` under `J`. If combining costs `ℓ |p|`
bits beyond the lengths of the two programs, then the *chain rule*
`C_J(pair x y) ≤ C_M(x) + C_N(y | x) + ℓ (C_M(x))` holds, and similarly for the time-bounded
complexities. For the combined program to be decodable, the end of the program for `x` must be
marked, and this costs more than a constant number of bits. The self-delimiting code
`selfDelimitingCode p` of `p`, which prefixes `p` with its length in binary, costs
`ℓ n = 2 log₂ n + O(1)` bits [Li and Vitányi, Chapters 1 and 2][LiVitanyi2019]. Doubling the
bits of the program for `x` and marking its end instead costs `|p| + O(1)` bits; this is Sipser's
bound `K(xy) ≤ 2 K(x) + K(y) + c` for the concatenation `xy` of two strings
[Sipser, Section 6.4][Sipser2013].

The canonical composition `M.compose N pair` reads a program as the self-delimiting code of a
program `p` followed by a program `q`, runs `p` under `M` and then `q` under `N x`, where `x` is
the output of `p`, and outputs `pair x y` for the output `y` of `q`. Its clock is the sum of the
two clocks, so it is a composition with length overhead `2 size |p| + 1` and no time overhead
(`Cslib.Kolmogorov.DescriptionMethod.Composition.compose`).

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.Composition`: a combination of programs for `x` and for `y`
  given `x` into programs for `pair x y`.
* `Cslib.Kolmogorov.DescriptionMethod.Composition.ofSelfDelimitingCode`: the composition whose
  combined program is the self-delimiting code of the first program followed by the second.
* `Cslib.Kolmogorov.DescriptionMethod.compose`: the description method that runs a program for
  `x` and then a program for `y` given `x`.
* `Cslib.Kolmogorov.DescriptionMethod.Composition.compose`: `M.compose N pair` is a composition of
  `M` and `N`.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.Composition.ecomplexity_le`: the chain rule
  `C_J(pair x y) ≤ C_M(x) + C_N(y | x) + ℓ (C_M(x))`.
* `Cslib.Kolmogorov.DescriptionMethod.Composition.etimeBoundedComplexity_le_of_le`: the
  time-bounded chain rule.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Kolmogorov

namespace DescriptionMethod

variable {α β γ : Type*}

/-! ### Composition and the chain rule -/

/-- A *composition* of the description method `M` for `α` and the conditional description method
`N` for `β` given `α` into the description method `J` for `γ`, along `pair : α → β → γ`, with
length overhead `ℓ` and time overhead `τ`. If the program `p` outputs `x` under `M` within `t₁`
steps and the program `q` outputs `y` under `N x` within `t₂` steps, then `combine p q` is a
program of length at most `|p| + |q| + ℓ |p|` that outputs `pair x y` under `J` within
`τ (|p| + |q|) (t₁ + t₂)` steps. -/
structure Composition (M : DescriptionMethod α) (N : α → DescriptionMethod β)
    (J : DescriptionMethod γ) (pair : α → β → γ) (ℓ : ℕ → ℕ) (τ : ℕ → ℕ → ℕ) where
  /-- The combination of a program for `x` and a program for `y` given `x`. -/
  combine : List Bool → List Bool → List Bool
  /-- Combining costs at most `ℓ |p|` bits beyond the lengths of the two programs. -/
  length_combine_le (p q : List Bool) : (combine p q).length ≤ p.length + q.length + ℓ p.length
  /-- The combined program outputs the pair, within the time overhead. -/
  mem_runFor_combine {p q : List Bool} {t₁ t₂ : ℕ} {x : α} {y : β} :
    x ∈ (M.run p).runFor t₁ → y ∈ ((N x).run q).runFor t₂ →
      pair x y ∈ (J.run (combine p q)).runFor (τ (p.length + q.length) (t₁ + t₂))

namespace Composition

variable {M : DescriptionMethod α} {N : α → DescriptionMethod β} {J : DescriptionMethod γ}
  {pair : α → β → γ} {ℓ : ℕ → ℕ} {τ : ℕ → ℕ → ℕ}

/-- The composition whose combined program is the self-delimiting code of the program for `x`
followed by the program for `y` given `x`; its length overhead is `2 size |p| + 1`. -/
def ofSelfDelimitingCode
    (h : ∀ {p q : List Bool} {t₁ t₂ : ℕ} {x : α} {y : β}, x ∈ (M.run p).runFor t₁ →
      y ∈ ((N x).run q).runFor t₂ → pair x y ∈
        (J.run (selfDelimitingCode p ++ q)).runFor (τ (p.length + q.length) (t₁ + t₂))) :
    Composition M N J pair (fun n => 2 * n.size + 1) τ where
  combine p q := selfDelimitingCode p ++ q
  length_combine_le p q := by
    rw [List.length_append, length_selfDelimitingCode]
    omega
  mem_runFor_combine := h

theorem produces_combine (S : Composition M N J pair ℓ τ) {p q : List Bool} {x : α} {y : β}
    (hx : M.Produces p x) (hy : (N x).Produces q y) : J.Produces (S.combine p q) (pair x y) :=
  let ⟨_, hx⟩ := produces_iff_exists_mem_runFor.mp hx
  let ⟨_, hy⟩ := produces_iff_exists_mem_runFor.mp hy
  .of_mem_runFor (S.mem_runFor_combine hx hy)

/-- **Chain rule.** `C_J(pair x y) ≤ C_M(x) + C_N(y | x) + ℓ (C_M(x))`. When `C_M(x) = ⊤` the
right-hand side is `⊤`, so the value `ℓ 0` used for `ℓ ⊤` does not matter. -/
theorem ecomplexity_le (S : Composition M N J pair ℓ τ) (x : α) (y : β) :
    J.ecomplexity (pair x y) ≤
      M.ecomplexity x + (N x).ecomplexity y + ℓ (M.ecomplexity x).toNat := by
  by_cases hx : M.ecomplexity x = ⊤
  · simp [hx]
  by_cases hy : (N x).ecomplexity y = ⊤
  · simp [hy]
  obtain ⟨p, hp, hplen⟩ := exists_length_eq_ecomplexity hx
  obtain ⟨q, hq, hqlen⟩ := exists_length_eq_ecomplexity hy
  rw [← hplen, ← hqlen, ENat.toNat_natCast]
  exact (ecomplexity_le_length (S.produces_combine hp hq)).trans (mod_cast S.length_combine_le p q)

/-- **Time-bounded chain rule.** If `C_M^{t₁}(x) ≤ k` and `C_N^{t₂}(y | x) ≤ l`, then
`C_J^{τ (k + l) (t₁ + t₂)}(pair x y) ≤ k + l + ℓ k`, for overheads monotone in the program
lengths. -/
theorem etimeBoundedComplexity_le_of_le (S : Composition M N J pair ℓ τ) (hℓ : Monotone ℓ)
    {t₁ t₂ k l : ℕ} (hτ : Monotone (τ · (t₁ + t₂))) {x : α} {y : β}
    (hx : M.etimeBoundedComplexity t₁ x ≤ k) (hy : (N x).etimeBoundedComplexity t₂ y ≤ l) :
    J.etimeBoundedComplexity (τ (k + l) (t₁ + t₂)) (pair x y) ≤ (k + l + ℓ k : ℕ) := by
  obtain ⟨p, hp, hpx⟩ := etimeBoundedComplexity_le_natCast_iff.mp hx
  obtain ⟨q, hq, hqy⟩ := etimeBoundedComplexity_le_natCast_iff.mp hy
  refine etimeBoundedComplexity_le_natCast_iff.mpr ⟨S.combine p q, ?_, ?_⟩
  · have := hℓ hp
    have := S.length_combine_le p q
    omega
  · exact Computation.mem_runFor_of_le (hτ (Nat.add_le_add hp hq)) (S.mem_runFor_combine hpx hqy)

end Composition

/-! ### The canonical composition -/

/-- The *composition* of the description method `M` for `α` and the conditional description
method `N` for `β` given `α`, along `pair : α → β → γ`: the decoder of the self-delimiting code
splits a program into `p` and `q` (`decodeSelfDelimiting`), then `p` runs under `M` and, once it
has output `x`, `q` runs under `N x`; the output is `pair x y` for the output `y` of `q`. -/
def compose (M : DescriptionMethod α) (N : α → DescriptionMethod β) (pair : α → β → γ) :
    DescriptionMethod γ where
  run r := (M.run (decodeSelfDelimiting r).1).bind fun x =>
    ((N x).run (decodeSelfDelimiting r).2).map (pair x)

@[simp]
theorem compose_run_selfDelimitingCode_append (M : DescriptionMethod α)
    (N : α → DescriptionMethod β) (pair : α → β → γ) (p q : List Bool) :
    (M.compose N pair).run (selfDelimitingCode p ++ q) =
      (M.run p).bind fun x => ((N x).run q).map (pair x) := by
  simp [compose]

namespace Composition

/-- The canonical composition `M.compose N pair` is a composition of `M` and `N` with length
overhead `2 size |p| + 1` and no time overhead: the combined program runs for the sum of the
running times of its two parts. -/
def compose (M : DescriptionMethod α) (N : α → DescriptionMethod β) (pair : α → β → γ) :
    Composition M N (M.compose N pair) pair (fun n => 2 * n.size + 1) fun _ t => t :=
  ofSelfDelimitingCode fun hx hy => by
    rw [compose_run_selfDelimitingCode_append]
    exact Computation.mem_runFor_bind hx (Computation.mem_runFor_map _ hy)

end Composition

end DescriptionMethod

end Cslib.Kolmogorov

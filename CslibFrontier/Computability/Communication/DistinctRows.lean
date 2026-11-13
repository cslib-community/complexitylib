/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Operations
public import CslibFrontier.Computability.Communication.Rank

/-!
# Distinct rows and the rank of the communication matrix

A zero/one matrix of rank `r` over a field has at most `2 ^ r` distinct rows
(`card_image_le_two_pow_rank`): some `r` columns span its column space, and every row is determined
by its zero/one entries on those columns. This gives a rank *upper* bound on deterministic
communication complexity, `C(f) ≤ rank M(f) + 1` (`ecomplexityFun_le_rank_add_one`): Alice names
her row among at most `2 ^ r` candidates in `r` bits, and Bob announces the value. Together with
the rank lower bound `clog_rank_le_ecomplexity`, a function on `n`-bit inputs with pairwise distinct
rows has communication complexity at least `⌈log₂ n⌉` (`clog_le_ecomplexityFun_of_injective`).

These are Exercises 4 (in the corrected form recorded in
`results/arora-barak-2007-exercises.md`; the printed statement lacks its relation symbol) and 6 of
Chapter 12 of [Arora and Barak, draft of 2007-01-08][AroraBarak07].

## Main results

* `Cslib.Communication.card_image_le_two_pow_rank`: a zero/one matrix of rank `r` over a field has
  at most `2 ^ r` distinct rows.
* `Cslib.Communication.ecomplexityFun_le_rank_add_one`: `C(f) ≤ rank_K M(f) + 1` over every field
  `K`.
* `Cslib.Communication.le_rank_of_injective`,
  `Cslib.Communication.clog_le_ecomplexityFun_of_injective`: pairwise distinct rows on `n`-bit
  inputs force rank at least `n` and communication complexity at least `⌈log₂ n⌉`.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07]
-/

public section

namespace Cslib.Communication

open Finset

variable {X Y : Type*} [Fintype Y]

/-- **A zero/one matrix of rank `r` has at most `2 ^ r` distinct rows** over any field `K`
[AroraBarak07, Chapter 12, Exercises 4 and 6]: the rows `f x` of a Boolean function `f` take at
most `2 ^ rank` values, where `rank` is the rank of its communication matrix over `K`. Some
`rank` columns span the column space, and a row is determined by its entries on them. -/
theorem card_image_le_two_pow_rank [Fintype X] (K : Type*) [Field K] [DecidableEq (Y → Bool)]
    (f : X → Y → Bool) :
    #(univ.image f) ≤ 2 ^ (communicationMatrix K f).rank := by
  classical
  set M := communicationMatrix K f
  -- a linearly independent set of columns spanning the column space
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range M.col)
  have hbfin : b.Finite := (Set.finite_range _).subset hbsub
  have : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hbspan, finrank_span_set_eq_card hbli,
      Set.toFinset_card]
  -- a column index for every element of `b`
  have hpre : ∀ v : b, ∃ y, M.col y = v.1 := fun v => hbsub v.2
  choose c hc using hpre
  -- a row is determined by its entries on the columns `c`
  have hdet : ∀ x x', (∀ v, f x (c v) = f x' (c v)) → f x = f x' := by
    intro x x' h
    let φ : (X → K) →ₗ[K] K := LinearMap.proj (R := K) (φ := fun _ : X => K) x - LinearMap.proj x'
    have hb : b ⊆ LinearMap.ker φ := by
      intro w hw
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hw' : w = M.col (c ⟨w, hw⟩) := (hc ⟨w, hw⟩).symm
      rw [hw']
      simp [φ, M, h ⟨w, hw⟩]
    funext y
    have hy : M.col y ∈ LinearMap.ker φ :=
      Submodule.span_le.2 hb (hbspan ▸ Submodule.subset_span (Set.mem_range_self y))
    rw [LinearMap.mem_ker] at hy
    have hxy : M x y = M x' y := by simpa [φ, sub_eq_zero] using hy
    simp only [M, communicationMatrix_apply] at hxy
    cases hfx : f x y <;> cases hfx' : f x' y <;> simp_all
  calc #(univ.image f)
      ≤ Fintype.card (b → Bool) := by
        refine card_le_card_of_injOn (fun r v => r (c v)) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
        intro r hr r' hr' hrr'
        obtain ⟨x, -, rfl⟩ := mem_image.1 hr
        obtain ⟨x', -, rfl⟩ := mem_image.1 hr'
        exact hdet x x' (congrFun hrr')
    _ = 2 ^ M.rank := by simp [hcard]

/-- **The rank upper bound** [AroraBarak07, Chapter 12, Exercise 4, corrected]: for finite input
sets and every field `K`, the deterministic communication complexity of `f` is at most the rank of
its communication matrix over `K` plus one. Alice sends the index of her row among the at most
`2 ^ rank` distinct rows (`card_image_le_two_pow_rank`), and Bob announces the value. The printed
exercise reads "`C(f) rank(M(f)+1`", missing its relation symbol; this is the evident repair. -/
theorem ecomplexityFun_le_rank_add_one [Finite X] (K : Type*) [Field K] (f : X → Y → Bool) :
    Protocol.ecomplexityFun f ≤ (communicationMatrix K f).rank + 1 := by
  classical
  have := Fintype.ofFinite X
  have h := Protocol.ecomplexityFun_le_clog_card_finset_succ (univ.image f) f
    (fun x => mem_image_of_mem f (mem_univ x)) fun r y => r y
  refine h.trans ?_
  gcongr
  exact_mod_cast Nat.clog_le_of_le_pow (card_image_le_two_pow_rank K f)

/-- If a Boolean function on `n`-bit inputs has pairwise distinct rows, its communication matrix
has rank at least `n` over every field. -/
theorem le_rank_of_injective (K : Type*) [Field K] {n : ℕ} {Y : Type*} [Fintype Y]
    {f : BitString n → Y → Bool} (hf : Function.Injective f) :
    n ≤ (communicationMatrix K f).rank := by
  classical
  have h := card_image_le_two_pow_rank K f
  rw [card_image_of_injective _ hf, card_univ, BitString.card] at h
  exact (Nat.pow_le_pow_iff_right one_lt_two).1 h

/-- **Distinct rows force `log₂ n` bits** [AroraBarak07, Chapter 12, Exercise 6]: if
`f : {0,1}ⁿ × {0,1}ⁿ → {0,1}` has pairwise distinct rows, its deterministic communication
complexity is at least `⌈log₂ n⌉`, so at least `log₂ n`. The rank is at least `n`
(`le_rank_of_injective`), and the rank bound `clog_rank_le_ecomplexity` applies. The exercise's
hypothesis `n ≥ 1` is not needed. -/
theorem clog_le_ecomplexityFun_of_injective {n : ℕ} {f : BitString n → BitString n → Bool}
    (hf : Function.Injective f) :
    (Nat.clog 2 n : ℕ∞) ≤ Protocol.ecomplexityFun f :=
  le_trans (by exact_mod_cast Nat.clog_mono_right 2 (le_rank_of_injective ℚ hf))
    (clog_rank_le_ecomplexity ℚ f)

end Cslib.Communication

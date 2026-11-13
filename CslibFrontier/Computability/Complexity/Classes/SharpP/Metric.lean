/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness

/-!
# Metric reductions and #P-hardness under one-query reductions

A *metric reduction* [Krentel][Krentel1988] from `f : α → Y` to `g : β → Z` is a pair of
polynomial-time functions, a query map `r : α → β` and a recovery map `post : α × Z → Y`, with
`f a = post (a, g (r a))`: one query to `g`, whose answer is post-processed together with the
input. Parsimonious reductions are the metric reductions whose recovery returns the answer
(`ParsimoniousReducible.metricReducible`). The reductions of Valiant's theorem
[Valiant][Valiant1979], [Arora and Barak, Section 9.2][AroraBarak07],
[Goldreich, Section 6.2.1][Goldreich2007Draft] are of this form but are not parsimonious: the
permanent of the matrix built from a formula is a fixed power `c ^ m` times the number of
satisfying assignments, and the integer permanent is recovered from a 0/1 permanent by reduction
modulo a large number.

Both books define #P-completeness by polynomial-time oracle (Cook) reductions. A metric reduction
makes one oracle query; `SharpPMetricHard` is #P-hardness under metric reductions, a strengthening
of the books' notion that is weaker than parsimonious hardness (`SharpPHard.sharpPMetricHard`).
It already rules out polynomial-time algorithms unless every function in #P is polynomial-time
computable (`SharpPMetricHard.computableInPolyTime`).

## Main definitions

* `Cslib.Complexity.MetricReducible`: one-query polynomial-time counting reductions.
* `Cslib.Complexity.SharpPMetricHard`, `Cslib.Complexity.SharpPMetricComplete`.

## Main results

* `Cslib.Complexity.MetricReducible.refl`, `Cslib.Complexity.MetricReducible.trans`.
* `Cslib.Complexity.ParsimoniousReducible.metricReducible`: parsimonious reductions are metric.
* `Cslib.Complexity.SharpPHard.sharpPMetricHard`, `Cslib.Complexity.SharpPMetricHard.trans`.
* `Cslib.Complexity.SharpPMetricHard.computableInPolyTime`: a polynomial-time computable
  #P-hard function puts all of #P in polynomial time.

## References

* [M. Krentel, *The complexity of optimization problems*][Krentel1988]
* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ Y Z W : Type}

/-- `f` reduces to `g` by a metric reduction: a polynomial-time query map `r` and a polynomial-time
recovery map `post`, reading the input and the answer of `g`, satisfy `f a = post (a, g (r a))`. -/
def MetricReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (encY : Y ↪ List Bool)
    (encZ : Z ↪ List Bool) (f : α → Y) (g : β → Z) : Prop :=
  ∃ (r : α → β) (post : α × Z → Y), ComputableInPolyTime r encA encB ∧
    ComputableInPolyTime post (encPair encA encZ) encY ∧ ∀ a, f a = post (a, g (r a))

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {encY : Y ↪ List Bool} {encZ : Z ↪ List Bool} {encW : W ↪ List Bool}

/-- Every function reduces to itself by a metric reduction. -/
theorem MetricReducible.refl (encA : α ↪ List Bool) (encY : Y ↪ List Bool) (f : α → Y) :
    MetricReducible encA encA encY encY f f :=
  ⟨id, Prod.snd, ComputableInPolyTime.id', by fun_prop, fun _ => rfl⟩

/-- Metric reductions compose: query the second reduction's instance and recover twice. -/
theorem MetricReducible.trans {f : α → Y} {g : β → Z} {h : γ → W}
    (hfg : MetricReducible encA encB encY encZ f g)
    (hgh : MetricReducible encB encC encZ encW g h) :
    MetricReducible encA encC encY encW f h := by
  obtain ⟨r, post, hr, hpost, hfg⟩ := hfg
  obtain ⟨s, post', hs, hpost', hgh⟩ := hgh
  refine ⟨s ∘ r, fun x => post (x.1, post' (r x.1, x.2)), hs.comp hr, ?_, fun a => ?_⟩
  · have hinner : ComputableInPolyTime (fun x : α × W => (r x.1, x.2)) (encPair encA encW)
        (encPair encB encW) := by fun_prop
    have hmid : ComputableInPolyTime (fun x : α × W => (x.1, post' (r x.1, x.2)))
        (encPair encA encW) (encPair encA encZ) := by
      have := hpost'.comp hinner
      fun_prop
    exact hpost.comp hmid
  · rw [hfg a, hgh (r a)]
    rfl

/-- **Parsimonious reductions are metric reductions**, recovering the answer unchanged. -/
theorem ParsimoniousReducible.metricReducible {f : α → ℕ} {g : β → ℕ}
    (h : ParsimoniousReducible encA encB f g) : MetricReducible encA encB encNat encNat f g :=
  let ⟨r, hr, hfg⟩ := h
  ⟨r, Prod.snd, hr, by fun_prop, hfg⟩

/-- `g` is #P-hard under metric reductions: every function in #P, with any encoding of its
instances, reduces to `g` by a metric reduction. The values of `g` are encoded by `encZ`, so that
integer-valued problems such as the integer permanent are included. -/
def SharpPMetricHard (encB : β ↪ List Bool) (encZ : Z ↪ List Bool) (g : β → Z) : Prop :=
  HardUnder (fun enc => MetricReducible enc encB encNat encZ) @SharpP g

/-- `g` is in #P and #P-hard under metric reductions. -/
def SharpPMetricComplete (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  g ∈ SharpP encB ∧ SharpPMetricHard encB encNat g

/-- Parsimonious #P-hardness implies #P-hardness under metric reductions. -/
theorem SharpPHard.sharpPMetricHard {g : β → ℕ} (hg : SharpPHard encB g) :
    SharpPMetricHard encB encNat g :=
  fun _ _ _ hf => (hg _ _ hf).metricReducible

/-- Parsimonious #P-completeness implies #P-completeness under metric reductions. -/
theorem SharpPComplete.sharpPMetricComplete {g : β → ℕ} (hg : SharpPComplete encB g) :
    SharpPMetricComplete encB g :=
  ⟨hg.1, hg.2.sharpPMetricHard⟩

/-- #P-hardness under metric reductions transfers along a metric reduction. -/
theorem SharpPMetricHard.trans {g : β → Z} {h : γ → W} (hg : SharpPMetricHard encB encZ g)
    (hgh : MetricReducible encB encC encZ encW g h) : SharpPMetricHard encC encW h :=
  fun _ _ _ hf => (hg _ _ hf).trans hgh

/-- If a function that is #P-hard under metric reductions is computable in polynomial time, then
so is every function in #P. -/
theorem SharpPMetricHard.computableInPolyTime {g : β → Z} (hg : SharpPMetricHard encB encZ g)
    (hpoly : ComputableInPolyTime g encB encZ) {enc : α ↪ List Bool} {f : α → ℕ}
    (hf : f ∈ SharpP enc) : ComputableInPolyTime f enc encNat := by
  obtain ⟨r, post, hr, hpost, hfg⟩ := hg _ _ hf
  have hpair : ComputableInPolyTime (fun a => (a, g (r a))) enc (encPair enc encZ) := by
    have := hpoly.comp hr
    fun_prop
  rw [show f = fun a => post (a, g (r a)) from funext hfg]
  exact hpost.comp hpair

end Cslib.Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.MCSP.Basic
public import Mathlib.Basic.Real.Basic
import Complexity.Computability.Circuit.Boolean.SparseSynthesis

/-!
# Succinct MCSP

*Succinct MCSP* asks, given samples `(x₁, b₁), …, (x_t, b_t)` of a Boolean function on `n` inputs
and a threshold `s`, whether some circuit with at most `s` gates takes the value `bᵢ` at `xᵢ` for
every `i` [OliveiraPichSanthanam2019, proof of Theorem 1.4]. Its instances list samples instead
of a whole truth table, so they may be much shorter than the `2 ^ n` bits of an instance of MCSP.
Contradictory samples are allowed; they make a no-instance.

When the samples are the values of `f` on a set `S` of inputs (`Instance.ofFunction`), the
question is whether `f` has complexity at most `s` on `S`, cslib's
`complexityOn interpretation S (single f)` (`ofFunction_mem_iff`). Taking every input as a sample
gives MCSP (`ofFunction_univ_mem_iff`). Sholomov's bound for partial functions gives a Shannon
window here too: on `2 p` inputs, every instance of at most `2 ^ p` consistent samples is a
yes-instance at every threshold of at least `(1 + ε) 2 ^ p / p`, for large `p`
(`eventually_ofFunction_mem`).

## Main definitions

* `Cslib.SuccinctMCSP.Instance`, `Cslib.SuccinctMCSP`: the instances and yes-instances.

## Main results

* `Cslib.SuccinctMCSP.card_samples_ofFunction`: the sample count of `Instance.ofFunction f S s` is
  `S.card`.
* `Cslib.SuccinctMCSP.ofFunction_mem_iff`,
  `Cslib.SuccinctMCSP.ofFunction_mem_iff_exists_mem_computableFunctions`,
  `Cslib.SuccinctMCSP.ofFunction_mem_of_complexity_le`: samples of a function, as complexity on a
  support or agreement with `computableFunctions`.
* `Cslib.SuccinctMCSP.ofFunction_univ_mem_iff`: all samples of a function, as MCSP.
* `Cslib.SuccinctMCSP.eventually_ofFunction_mem`: few samples always have small circuits.

## References

* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
* [L. A. Sholomov, *On the realization of incompletely defined Boolean functions by circuits of
  functional elements*][Sholomov1969]
-/

@[expose] public section

namespace Cslib

open Circuits Circuits.Boolean

namespace SuccinctMCSP

/-- An instance of Succinct MCSP: samples of a Boolean function on `arity` inputs, each an input
and the value required there, and a size threshold. -/
structure Instance where
  /-- The number of inputs of the function. -/
  arity : ℕ
  /-- The samples: an input and the required value at it. -/
  samples : Finset (BitString arity × Bool)
  /-- The number of gates allowed. -/
  threshold : ℕ

/-- The instance whose samples are the values of `f` on the inputs in `S`, with threshold `s`. -/
def Instance.ofFunction {n : ℕ} (f : BooleanFunction n) (S : Finset (BitString n)) (s : ℕ) :
    Instance :=
  ⟨n, S.image fun x => (x, f x), s⟩

/-- The sample set of `Instance.ofFunction f S s` has the same cardinality as `S`. -/
@[simp] theorem card_samples_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.ofFunction f S s).samples.card = S.card :=
  Finset.card_image_of_injective S fun _ _ h => (Prod.mk.inj h).1

end SuccinctMCSP

/-- **Succinct MCSP** [OliveiraPichSanthanam2019]: the instances some De Morgan circuit with at
most `threshold` gates satisfies, taking the value `b` at `x` for every sample `(x, b)`. -/
def SuccinctMCSP : Set SuccinctMCSP.Instance :=
  {x | ∃ c : Circuit signature x.arity 1, c.size ≤ x.threshold ∧
    ∀ p ∈ x.samples, c.eval interpretation p.1 0 = p.2}

namespace SuccinctMCSP

variable {n s : ℕ}

/-- The yes-instances are those satisfied by some function computable within the threshold. -/
theorem mem_iff_exists_mem_computableFunctions {x : Instance} :
    x ∈ SuccinctMCSP ↔
      ∃ g ∈ computableFunctions x.arity x.threshold, ∀ p ∈ x.samples, g p.1 = p.2 := by
  simp only [mem_computableFunctions, Circuit.computes_single_iff]
  exact ⟨fun ⟨c, hc, hp⟩ => ⟨fun y => c.eval interpretation y 0, ⟨c, fun _ => rfl, hc⟩, hp⟩,
    fun ⟨g, ⟨c, hcg, hc⟩, hp⟩ => ⟨c, hc, fun p hpx => (hcg p.1).trans (hp p hpx)⟩⟩

/-- Samples of `f` on `S` are a yes-instance exactly when `f` has complexity at most `s` on `S`. -/
theorem ofFunction_mem_iff {f : BooleanFunction n} {S : Finset (BitString n)} :
    Instance.ofFunction f S s ∈ SuccinctMCSP ↔ complexityOn interpretation S (single f) ≤ s := by
  rw [complexityOn_le_iff]
  simp only [SuccinctMCSP, Instance.ofFunction, Set.mem_ofPred_eq, Finset.mem_image,
    forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq, Circuit.computesOn_single_iff,
    Finset.mem_coe]
  exact exists_congr fun c => ⟨fun ⟨hc, hp⟩ => ⟨fun x hx => hp x (f x) x hx rfl rfl, hc⟩,
    fun ⟨hc, hs⟩ => ⟨hs, by rintro _ _ y hy rfl rfl; exact hc y hy⟩⟩

/-- For `Instance.ofFunction f S s`, membership in `SuccinctMCSP` is equivalent to the existence of
some function `g ∈ computableFunctions n s` agreeing with `f` on `S`. -/
theorem ofFunction_mem_iff_exists_mem_computableFunctions {f : BooleanFunction n}
    {S : Finset (BitString n)} :
    Instance.ofFunction f S s ∈ SuccinctMCSP ↔
      ∃ g ∈ computableFunctions n s, ∀ x ∈ S, g x = f x := by
  rw [mem_iff_exists_mem_computableFunctions]
  exact exists_congr fun g => and_congr_right fun _ =>
    ⟨fun h x hx => h (x, f x) (Finset.mem_image_of_mem _ hx), fun h p hp => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact h x hx⟩

/-- Any subset of samples from a function of circuit complexity at most `s` forms a yes-instance of
`SuccinctMCSP` at threshold `s`. -/
theorem ofFunction_mem_of_complexity_le {f : BooleanFunction n}
    (hf : complexity interpretation (single f) ≤ s) (S : Finset (BitString n)) :
    Instance.ofFunction f S s ∈ SuccinctMCSP :=
  ofFunction_mem_iff.mpr (complexityOn_le_complexity.trans hf)

/-- With every input as a sample, Succinct MCSP is MCSP. -/
theorem ofFunction_univ_mem_iff {f : BooleanFunction n} :
    Instance.ofFunction f Finset.univ s ∈ SuccinctMCSP ↔ ⟨n, MCSP.truthTable n f, s⟩ ∈ MCSP := by
  rw [ofFunction_mem_iff, Finset.coe_univ, MCSP.mk_truthTable_mem_iff]
  rfl

/-- Raising the threshold keeps a yes-instance a yes-instance. -/
theorem mk_mem_of_le {samples : Finset (BitString n × Bool)} {t : ℕ}
    (h : ⟨n, samples, s⟩ ∈ SuccinctMCSP) (hst : s ≤ t) : ⟨n, samples, t⟩ ∈ SuccinctMCSP :=
  let ⟨c, hc, hp⟩ := h
  ⟨c, hc.trans hst, hp⟩

/-- Dropping samples keeps a yes-instance a yes-instance. -/
theorem mk_mem_of_subset {samples samples' : Finset (BitString n × Bool)}
    (h : ⟨n, samples, s⟩ ∈ SuccinctMCSP) (hsub : samples' ⊆ samples) :
    ⟨n, samples', s⟩ ∈ SuccinctMCSP :=
  let ⟨c, hc, hp⟩ := h
  ⟨c, hc, fun p hpx => hp p (hsub hpx)⟩

/-- Contradictory samples make a no-instance. -/
theorem notMem_of_mem_samples {x : Instance} {y : BitString x.arity}
    (htrue : (y, true) ∈ x.samples) (hfalse : (y, false) ∈ x.samples) : x ∉ SuccinctMCSP :=
  fun ⟨_, _, hp⟩ => Bool.true_eq_false_eq_False ((hp _ htrue).symm.trans (hp _ hfalse))

/-- **Few samples have small circuits** [Sholomov1969]. For every `ε > 0` and all large `p`,
every instance of at most `2 ^ p` samples of a function on `2 p` inputs is a yes-instance at every
threshold of at least `(1 + ε) 2 ^ p / p`. -/
theorem eventually_ofFunction_mem (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ (f : BooleanFunction (2 * p)) (S : Finset (BitString (2 * p))),
      S.card ≤ 2 ^ p → ∀ s : ℕ, (1 + ε) * 2 ^ p / p ≤ s →
        Instance.ofFunction f S s ∈ SuccinctMCSP := by
  obtain ⟨p₀, hp₀⟩ := SparseSynthesis.complexityOn_le ε hε
  exact ⟨p₀, fun p hp f S hS s hs => ofFunction_mem_iff.mpr
    (by exact_mod_cast (hp₀ p hp S hS f).trans hs)⟩

end SuccinctMCSP

end Cslib

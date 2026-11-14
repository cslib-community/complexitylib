/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.KWiseIndependent
public import CslibFrontier.Probability.StatisticalDistance.Coupling
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.LawfulXor.Equiv
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Uniform

/-!
# Uniform Restriction and Two-Level Coupling Laws for $k$-Wise Independent Hash Families

Under a uniform finite seed `θ ← PMF.uniformOfFintype Seed`, restricting a `k`-wise independent hash
family `eval : Seed → Fin U → Fin m` to any subset `T : Finset (Fin U)` of size `#T ≤ k` yields the
exact uniform distribution `PMF.uniformOfFintype (T → Fin m)`
(`Cslib.Probability.uniformOfFintype_map_restrict_eq`).

For a two-level hash family `eval : TopSeed → BotSeed → Fin U → Fin m` whose inner family `eval α`
is `k`-wise independent for every good top seed `α ∈ GoodTop`, the restricted distribution on `T`
with `#T ≤ k` is coupled within `(#(Finset.univ \ GoodTop) : ℝ≥0∞) / Fintype.card TopSeed` of
`PMF.uniformOfFintype (T → Fin m)`
(`Cslib.Probability.coupledWithin_uniformOfFintype_prod_restrict`).

## Main results

* `Cslib.Probability.uniformOfFintype_map_of_isKWise`: mapping a `k`-wise independent hash family
  over a finite domain `X` with `Fintype.card X ≤ k` under a uniform seed produces
  `PMF.uniformOfFintype (X → Y)`.
* `Cslib.Probability.uniformOfFintype_map_restrict_eq`: restricting a `k`-wise independent hash
  family to `T` (`#T ≤ k`) under a uniform seed produces `PMF.uniformOfFintype (T → Fin m)`.
* `Cslib.Probability.map_xor_restrict_eq_uniform`: mapping a `k`-wise independent hash family with
  a pointwise XOR shift produces `PMF.uniformOfFintype (T → Fin (2 ^ s))`.
* `Cslib.Probability.coupledWithin_uniformOfFintype_prod_restrict`: two-level coupling bound for
  restricting a hash family whose top seed is `k`-wise independent on `GoodTop`.
-/

public section

open scoped ENNReal Cslib.Probability.PMF
open Cslib.Probability.PMF

namespace Cslib.Probability

universe u v w

/-- If `h : ι → X → Y` is `k`-wise independent and `Fintype.card X ≤ k`, then `h θ` under
`θ ← PMF.uniformOfFintype ι` has the exact uniform distribution `PMF.uniformOfFintype (X → Y)`. -/
theorem uniformOfFintype_map_of_isKWise {ι : Type u} {X : Type v} {Y : Type w}
    [Fintype ι] [Nonempty ι] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    {k : ℕ} {h : ι → X → Y} (hh : IsKWiseIndependentHash k h) (hX : Fintype.card X ≤ k) :
    (PMF.uniformOfFintype ι).map h = PMF.uniformOfFintype (X → Y) := by
  classical
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [toReal_uniformOfFintype_map_apply]
  let y' : (x : (Finset.univ : Finset X)) → Y := fun x => y x.1
  have hcard : (Finset.univ : Finset X).card ≤ k := by simpa using hX
  have hset : (Finset.univ.filter fun s : ι => h s = y) =
      (Finset.univ.filter fun s : ι => (Finset.univ : Finset X).restrict (h s) = y') := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Finset.restrict]
    exact ⟨fun hs x => hs x.1, fun hs x => hs ⟨x, Finset.mem_univ x⟩⟩
  rw [hset, hh.dens_filter_restrict_eq hcard y']
  simp [PMF.uniformOfFintype_apply, Fintype.card_pi]

/-- If `eval : Seed → Fin U → Fin m` is `k`-wise independent, then restricting `eval θ` under
`θ ← PMF.uniformOfFintype Seed` to any subset `T : Finset (Fin U)` of size `#T ≤ k` produces the
exact uniform distribution `PMF.uniformOfFintype (T → Fin m)`. -/
theorem uniformOfFintype_map_restrict_eq {Seed : Type u} {U m : ℕ}
    [Fintype Seed] [Nonempty Seed] [NeZero m] {k : ℕ} {eval : Seed → Fin U → Fin m}
    (hk : IsKWiseIndependentHash k eval)
    {T : Finset (Fin U)} (hT : T.card ≤ k) :
    (PMF.uniformOfFintype Seed).map (fun θ => T.restrict (eval θ)) =
      PMF.uniformOfFintype (T → Fin m) :=
  uniformOfFintype_map_of_isKWise (hk.comp Subtype.val_injective) (by simpa using hT)

/-- Mapping a `k`-wise independent hash family combined with a pointwise XOR shift `base i ^^^ ·`
over `T` with `Fintype.card T ≤ k` and injective input `inp` yields the uniform distribution. -/
theorem map_xor_restrict_eq_uniform {ι T : Type*}
    [Fintype ι] [Nonempty ι] [Fintype T] [DecidableEq T]
    {s s' k : ℕ} {h : ι → Fin (2 ^ s') → Fin (2 ^ s)}
    (hh : IsKWiseIndependentHash k h) (hT : Fintype.card T ≤ k)
    (base : T → Fin (2 ^ s)) {inp : T → Fin (2 ^ s')} (hinj : Function.Injective inp) :
    (PMF.uniformOfFintype ι).map (fun seed i => base i ^^^ h seed (inp i)) =
      PMF.uniformOfFintype (T → Fin (2 ^ s)) := by
  let shiftEq : (T → Fin (2 ^ s)) ≃ (T → Fin (2 ^ s)) :=
    { toFun := fun f i => base i ^^^ f i
      invFun := fun f i => base i ^^^ f i
      left_inv := fun f => by ext i; simp [xor_cancel_left]
      right_inv := fun f => by ext i; simp [xor_cancel_left] }
  calc (PMF.uniformOfFintype ι).map (fun seed i => base i ^^^ h seed (inp i))
      = ((PMF.uniformOfFintype ι).map (fun seed i => h seed (inp i))).map shiftEq := by
          rw [PMF.map_comp]; rfl
    _ = (PMF.uniformOfFintype (T → Fin (2 ^ s))).map shiftEq := by
          rw [uniformOfFintype_map_of_isKWise (hh.comp hinj) hT]
    _ = PMF.uniformOfFintype (T → Fin (2 ^ s)) := uniformOfFintype_map_equiv shiftEq

private theorem uniformOfFintype_prod_map {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (f : α → β → γ) :
    (PMF.uniformOfFintype (α × β)).map (fun p => f p.1 p.2) =
      (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (f a)) := by
  rw [← PMF.uniformOfFintype_prod, PMF.map_bind]
  refine congrArg ((PMF.uniformOfFintype α).bind ·) (funext fun a => ?_)
  simp [PMF.map_comp, Function.comp_def]

private theorem toOuterMeasure_uniformOfFintype_compl_finset {α : Type u}
    [Fintype α] [Nonempty α] [DecidableEq α] (s : Finset α) :
    (PMF.uniformOfFintype α).toOuterMeasure (s : Set α)ᶜ =
      ((Finset.univ \ s).card : ℝ≥0∞) / Fintype.card α := by
  have hcompl : ((s : Set α)ᶜ : Set α) = ((Finset.univ \ s : Finset α) : Set α) := by
    ext a
    simp
  rw [hcompl, PMF.toOuterMeasure_apply_finset]
  simp [PMF.uniformOfFintype_apply, div_eq_mul_inv]

/-- Single-epoch coupling for a two-level hash family: if every `α ∈ GoodTop` induces a `k`-wise
independent family `eval α : BotSeed → Fin U → Fin m`, then restricting `eval p.1 p.2` under
`p ← PMF.uniformOfFintype (TopSeed × BotSeed)` to a set `T` of size `#T ≤ k` is coupled within
`(#(Finset.univ \ GoodTop) : ℝ≥0∞) / Fintype.card TopSeed` of `PMF.uniformOfFintype (T → Fin m)`. -/
theorem coupledWithin_uniformOfFintype_prod_restrict {TopSeed : Type u} {BotSeed : Type v}
    {U m : ℕ} [Fintype TopSeed] [Nonempty TopSeed] [DecidableEq TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    [NeZero m] {k : ℕ} (eval : TopSeed → BotSeed → Fin U → Fin m)
    (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop, IsKWiseIndependentHash k (eval α))
    {T : Finset (Fin U)} (hT : T.card ≤ k) :
    CoupledWithin
      ((PMF.uniformOfFintype (TopSeed × BotSeed)).map (fun p => T.restrict (eval p.1 p.2)))
      (PMF.uniformOfFintype (T → Fin m))
      (((Finset.univ \ GoodTop).card : ℝ≥0∞) / Fintype.card TopSeed) := by
  rw [uniformOfFintype_prod_map (fun α β => T.restrict (eval α β)),
    ← toOuterMeasure_uniformOfFintype_compl_finset GoodTop]
  refine CoupledWithin.bind_of_eq_on (GoodTop : Set TopSeed) fun α _ hα => ?_
  exact uniformOfFintype_map_restrict_eq (hgood α hα) hT

end Cslib.Probability

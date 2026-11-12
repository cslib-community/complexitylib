/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying, Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Init
public import Cslib.Probability.PMF

/-!
# Monad notation and real-valued masses for discrete distributions

Copies of two cslib pull requests that the pinned cslib lacks: simp lemmas turning `do` notation
on `PMF` into `PMF.pure`/`PMF.bind` (cslib #1129), and real-valued probability masses (cslib
#1062). The library's other lemmas about discrete distributions are split by topic:
`Probability/PMF/Event` (event probabilities), `Probability/PMF/Bind` (two-stage experiments),
`Probability/PMF/Uniform` (uniform distributions and resampling) and `Probability/PMF/Map`
(relabeling).

## Main results

* `Cslib.Probability.PMF.monad_pure_eq_pure`, `Cslib.Probability.PMF.monad_bind_eq_bind`:
  `do` notation on `PMF` (cslib #1129).
* `Cslib.Probability.PMF.summable_toReal`, `Cslib.Probability.PMF.tsum_toReal`,
  `Cslib.Probability.PMF.sum_toReal`: real-valued masses sum to one (cslib #1062).
* `Cslib.Probability.PMF.bind_apply_toReal`, `Cslib.Probability.PMF.bind_apply_toReal_tsum`:
  real-valued outcome masses of a two-stage experiment (cslib #1062).
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

universe u

variable {α β : Type*}

/-! ### Monad notation

Copied from cslib PR #1129 at `dbe22c640c85b2e9fbcb2ec16cd3d14ccb37c4e8`.
Remove this block when that PR is in the base pin.
-/

-- upstream: submitted #1129 @dbe22c640c85b2e9fbcb2ec16cd3d14ccb37c4e8

@[simp] theorem monad_pure_eq_pure (a : α) : (pure a : PMF α) = PMF.pure a := rfl

@[simp] theorem monad_bind_eq_bind {α β : Type u} (p : PMF α) (f : α → PMF β) :
    p >>= f = p.bind f := rfl

attribute [simp] _root_.PMF.monad_map_eq_map _root_.PMF.pure_map

/-! ### Real-valued probability masses

Copied from cslib PR #1062 at `b2b8dcdfe7dc7f791a146534ad2ca8eb383b51fd`.
Remove this block when that PR is in the base pin.
-/

-- upstream: submitted #1062 @b2b8dcdfe7dc7f791a146534ad2ca8eb383b51fd

/-- Real-valued probability masses are summable, even on an infinite ambient type. -/
theorem summable_toReal (p : PMF α) : Summable (fun a => (p a).toReal) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

/-- The real-valued masses of any discrete distribution sum to one. -/
@[simp] theorem tsum_toReal (p : PMF α) : ∑' a, (p a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]

/-- The real-valued probabilities of a finite distribution sum to one. -/
theorem sum_toReal [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by simpa using tsum_toReal p

/-- Randomized postprocessing averages the outcome probabilities over any discrete input. -/
theorem bind_apply_toReal_tsum (p : PMF α) (kernel : α → PMF β) (b : β) :
    (p.bind kernel b).toReal = ∑' a, (p a).toReal * (kernel a b).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq (fun a =>
    ENNReal.mul_ne_top (p.apply_ne_top a) ((kernel a).apply_ne_top b))]
  simp

/-- The probability of an outcome after a finite random choice is its weighted average. -/
theorem bind_apply_toReal [Fintype α] (p : PMF α)
    (kernel : α → PMF β) (b : β) :
    (p.bind kernel b).toReal =
      ∑ a, (p a).toReal * (kernel a b).toReal := by
  simpa using bind_apply_toReal_tsum p kernel b

end Cslib.Probability.PMF

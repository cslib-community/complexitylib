/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Braverman.Resilience
public import Complexity.Foundations.BooleanAnalysis.Tribes
import Complexity.Computability.Circuit.FanIn

/-!
# Tribes under bounded independence

The Tribes function `Tribes_{w,s}` (`Cslib.BitString.tribes`) is computed by a depth-two circuit of
the unbounded fan-in basis, an `OR` of `s` `AND`s of `w` inputs each (`tribesCircuit`), with
`s + 1` gates and fan-in `max s w`. Through
[Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019]
(`Cslib.Circuits.Boolean.Braverman.isKWiseResilient_of_isResilient`), the resilience of Tribes
(`Cslib.BitString.isResilient_tribes`) and its near balance
(`Cslib.BitString.abs_expect_bitVal_tribes_sub_half_le`) carry over, with an error `2 ^ (-p)`, to
every `t`-wise independent distribution with `t ≥ (64 p) ^ 157`, where `p ≥ 2`, `2 s + 8 ≤ 2 ^ p`
and `w < 2 ^ p`; for the bias, `t ≥ (64 p) ^ 64` suffices, where `p ≥ 1` and `s, w < 2 ^ p`. These
exponents are those of the library's form of Braverman's theorem at depths `5` and `2`; they are
ours, and Chattopadhyay and Zuckerman's exponent `3 d + 6` is not claimed.

## Main definitions

* `Cslib.Circuits.Boolean.tribesCircuit`: the depth-two circuit computing Tribes.

## Main results

* `Cslib.Circuits.Boolean.eval_tribesCircuit`, `Cslib.Circuits.Boolean.size_tribesCircuit`,
  `Cslib.Circuits.Boolean.depth_tribesCircuit_le`,
  `Cslib.Circuits.Boolean.fanInAtMost_tribesCircuit`: its function, size, depth and fan-in.
* `Cslib.Circuits.Boolean.Braverman.isKWiseResilient_tribes`: Tribes is resilient under bounded
  independence.
* `Cslib.Circuits.Boolean.Braverman.abs_sum_bitVal_tribes_sub_half_le`: Tribes is nearly balanced
  under bounded independence.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
-/

public section

namespace Cslib.Circuits.Boolean

open BitString

variable {w s : ℕ}

/-- The depth-two circuit computing `Tribes_{w,s}`: the `OR` of the `AND`s of the tribes. -/
def tribesCircuit (w s : ℕ) : Circuit Unbounded.signature (s * w) 1 :=
  (Circuit.oneGate (Unbounded.Op.or s) (id : Fin s → Fin s)).comp
    (Circuit.pi fun j => Circuit.oneGate (Unbounded.Op.and w) fun i => finProdFinEquiv (j, i))

/-- `tribesCircuit w s` computes `Tribes_{w,s}`. -/
@[simp] theorem eval_tribesCircuit (x : BitString (s * w)) :
    (tribesCircuit w s).eval Unbounded.interpretation x 0 = tribes w s x := by
  simp [tribesCircuit, tribes]

/-- `tribesCircuit w s` has `s + 1` gates. -/
@[simp] theorem size_tribesCircuit : (tribesCircuit w s).size = s + 1 := by
  simp [tribesCircuit]

/-- `tribesCircuit w s` has depth at most two. -/
theorem depth_tribesCircuit_le : (tribesCircuit w s).depth ≤ 2 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_oneGate]
  exact Nat.add_le_add_left (Circuit.depth_pi_le _ fun _ => (Circuit.depth_oneGate _ _).le) 1

/-- `tribesCircuit w s` has fan-in at most `max s w`. -/
theorem fanInAtMost_tribesCircuit : (tribesCircuit w s).FanInAtMost (max s w) :=
  ((Circuit.fanInAtMost_oneGate _ _ _).2 (le_max_left s w)).comp
    (Circuit.fanInAtMost_pi fun _ => (Circuit.fanInAtMost_oneGate _ _ _).2 (le_max_right s w))

namespace Braverman

/-- **Tribes is resilient under bounded independence**, our instance of
[Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019]: if `p ≥ 2`,
`2 s + 8 ≤ 2 ^ p` and `w < 2 ^ p`, then `Tribes_{w,s}` is `t`-independent
`(q, 2 ^ (q - w) + 2 ^ (-p))`-resilient for every `t ≥ (64 p) ^ 157`. The exponent `157` is
`(2 d + 9) (d + 10) + 1` at the depth `d = 2` of `tribesCircuit`. -/
theorem isKWiseResilient_tribes {p q t : ℕ} (hp : 2 ≤ p) (hs : 2 * s + 8 ≤ 2 ^ p)
    (hw : w < 2 ^ p) (ht : (64 * p) ^ 157 ≤ t) :
    IsKWiseResilient t q (2 ^ q / 2 ^ w + 1 / 2 ^ p) (tribes w s) := by
  have hf : (fun x => (tribesCircuit w s).eval Unbounded.interpretation x 0) = tribes w s :=
    funext eval_tribesCircuit
  have h := isKWiseResilient_of_isResilient (d := 2) hp (tribesCircuit w s)
    (by rw [hf]; exact monotone_tribes w s)
    (fanInAtMost_tribesCircuit.mono (max_le (by omega) (by omega)))
    (by rw [size_tribesCircuit]; omega) depth_tribesCircuit_le
    (by rw [hf]; exact isResilient_tribes w s q) ht
  rwa [hf] at h

/-- **Tribes is nearly balanced under bounded independence**, our instance of
[Chattopadhyay–Zuckerman, Theorem 4.1, bias part][ChattopadhyayZuckerman2019]: if `s` is largest
with `(1 - 2 ^ (-w)) ^ s ≥ 1 / 2` [O'Donnell, Definition 4.11][ODonnell2014], `p ≥ 1` and
`s, w < 2 ^ p`, then under every `t`-wise independent distribution with `t ≥ (64 p) ^ 64`,
`Tribes_{w,s}` is true with probability within `2 ^ (-w) + 2 ^ (-p)` of `1 / 2`. The exponent `64`
is `(2 d + 3) (d + 7) + 1` at `d = 2`. -/
theorem abs_sum_bitVal_tribes_sub_half_le {p t : ℕ} {D : PMF (BitString (s * w))} (hp : 1 ≤ p)
    (hs : s < 2 ^ p) (hw : w < 2 ^ p)
    (h₁ : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) (h₂ : (1 - (2⁻¹ : ℝ) ^ w) ^ (s + 1) < 1 / 2)
    (ht : (64 * p) ^ 64 ≤ t) (hD : IsKWiseIndependent t D) :
    |∑ x, (D x).toReal * bitVal ℝ (tribes w s x) - 1 / 2| ≤ 2⁻¹ ^ w + 1 / 2 ^ p := by
  have h := abs_sum_bitVal_sub_half_le_of_isKWiseIndependent (d := 2) hp (tribesCircuit w s)
    (fanInAtMost_tribesCircuit.mono (max_le (by omega) (by omega)))
    (by rw [size_tribesCircuit]; omega) depth_tribesCircuit_le
    (by simp only [eval_tribesCircuit]; exact abs_expect_bitVal_tribes_sub_half_le h₁ h₂) ht hD
  simpa only [eval_tribesCircuit] using h

end Braverman

end Cslib.Circuits.Boolean

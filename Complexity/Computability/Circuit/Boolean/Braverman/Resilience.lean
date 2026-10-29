/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Braverman.Fooling
public import Complexity.Computability.Circuit.Boolean.Unbounded.Restriction
public import Complexity.Computability.Circuit.Pi
public import Complexity.Probability.Resilience
import Complexity.Computability.Circuit.FanIn

/-!
# Resilient functions under bounded independence

Chattopadhyay and Zuckerman observe that Braverman's theorem transfers resilience from the uniform
distribution to every distribution of polylogarithmic independence, for functions computed by
monotone `AC⁰` circuits [Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019]. The
bias carries over directly. For the influence of a coalition `Q`, monotonicity shows that `f` is
undetermined at `x` by the bits outside `Q` exactly when `f` is `true` with all of `Q` set to
`true` and `false` with all of `Q` set to `false`
(`Cslib.BitString.isUndetermined_iff_of_monotone`).
This event is computed by a constant-depth circuit `E_Q` (`undeterminedCircuit`), and Braverman's
theorem applied to `E_Q` bounds its probability.

The circuit `E_Q` is our construction in the unbounded fan-in basis: it runs two copies of the
circuit `C` on the inputs with the bits of `Q` fixed (`fixCircuit`, a restriction circuit
`Cslib.Circuits.Boolean.Unbounded.restrictCircuit`) and combines them by a circuit of two gates
computing `x₀ ∧ ¬x₁`. If `C` has `m` gates, depth `d` and fan-in `r`, then `E_Q` has
exactly `2 m + 6` gates, depth at most `d + 3` and fan-in at most `max r 2`. Chattopadhyay and
Zuckerman compute `¬(C₀ = C₁)` instead, with size `4 m + 3` and depth `d + 2`, reduced to `d + 1`
[Chattopadhyay–Zuckerman, proof of Theorem 4.1][ChattopadhyayZuckerman2019];
our count of depth includes negations and the constant gates (`Circuit.depth`), and `C₁ ∧ ¬C₀`
suffices since `C₀ ≤ C₁` for monotone `C`.

The required independence is that of the library's Braverman theorem
(`Cslib.Circuits.Boolean.Braverman.fools_of_independence_le`) at depth `d + 3`: with error
`2 ^ (-p)` it is at most `(64 p) ^ ((2 d + 9) (d + 10) + 1)`. The theorem needs `2 m + 6 ≤ 2 ^ p`
for a circuit of `m` gates and, since the fan-in of this model is not bounded by the size, fan-in
`r < 2 ^ p`; taking `p ≥ max (log₂ (2 m + 6)) (max (log₂ (r + 1)) (log₂ (1 / ε)))` gives
`t = (log (max m (r + 1) / ε)) ^ O(d²)`. Chattopadhyay and Zuckerman obtain
`(log (m / ε)) ^ (3 d + 6)` from Tal's form of Braverman's theorem; that exponent is not claimed
here. Monotonicity is assumed of the computed function, which is weaker than their assumption of a
monotone circuit. The statements for almost `t`-wise independent distributions in their
Theorem 4.1, which need a further approximation theorem, are not formalized.

## Main definitions

* `Cslib.Circuits.Boolean.Braverman.fixCircuit`: the inputs with the bits of a set fixed.
* `Cslib.Circuits.Boolean.Braverman.undeterminedCircuit`: the circuit `E_Q`, true where a monotone
  circuit is undetermined by the bits outside `Q`.

## Main results

* `Cslib.Circuits.Boolean.Braverman.size_undeterminedCircuit`,
  `Cslib.Circuits.Boolean.Braverman.depth_undeterminedCircuit_le`,
  `Cslib.Circuits.Boolean.Braverman.fanInAtMost_undeterminedCircuit`: the size, depth and fan-in of
  `E_Q`.
* `Cslib.Circuits.Boolean.Braverman.coalitionInfluence_le_of_independence_le`: the influence part
  of [Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019], for one coalition.
* `Cslib.Circuits.Boolean.Braverman.abs_sum_bitVal_sub_half_le_of_independence_le`,
  `Cslib.Circuits.Boolean.Braverman.abs_sum_bitVal_sub_half_le_of_isKWiseIndependent`: the bias
  part.
* `Cslib.Circuits.Boolean.Braverman.isKWiseResilient_of_isResilient`: resilient monotone `AC⁰`
  functions are resilient under polylogarithmic independence, with the closed-form independence.

## References

* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
* [M. Braverman, *Polylogarithmic independence fools AC⁰ circuits*][Braverman2010]
-/

public section

namespace Cslib.Circuits.Boolean.Braverman

open Finset BitString
open scoped BigOperators

variable {n : ℕ}

/-! ### The circuit `E_Q` -/

/-- The circuit that outputs its inputs with the bits of `Q` replaced by the constant `b`: the
restriction circuit of the partial assignment fixing `Q` to `b`. -/
def fixCircuit (Q : Finset (Fin n)) (b : Bool) : Circuit Unbounded.signature n n :=
  Unbounded.restrictCircuit (PartialAssignment.empty.assign Q fun _ => b)

/-- `fixCircuit Q b` sets the bits of `Q` to `b`. -/
@[simp] theorem eval_fixCircuit (Q : Finset (Fin n)) (b : Bool) (x : BitString n) :
    (fixCircuit Q b).eval Unbounded.interpretation x = Q.piecewise (fun _ => b) x := by
  rw [fixCircuit, Unbounded.eval_restrictCircuit]
  funext i
  by_cases hi : i ∈ Q
  · rw [piecewise_eq_of_mem _ _ _ hi,
      PartialAssignment.fill_of_eq_some (PartialAssignment.assign_of_mem hi _)]
  · rw [piecewise_eq_of_notMem _ _ _ hi, PartialAssignment.fill_of_eq_none
      ((PartialAssignment.assign_of_notMem hi _).trans (PartialAssignment.empty_apply i))]

/-- `fixCircuit Q b` has two gates, one for each constant. -/
@[simp] theorem size_fixCircuit (Q : Finset (Fin n)) (b : Bool) : (fixCircuit Q b).size = 2 :=
  Unbounded.size_restrictCircuit _

/-- `fixCircuit Q b` has depth at most one. -/
theorem depth_fixCircuit_le (Q : Finset (Fin n)) (b : Bool) : (fixCircuit Q b).depth ≤ 1 :=
  Unbounded.depth_restrictCircuit_le _

/-- `fixCircuit Q b` has fan-in at most two. -/
theorem fanInAtMost_fixCircuit (Q : Finset (Fin n)) (b : Bool) :
    (fixCircuit Q b).FanInAtMost 2 :=
  Unbounded.fanInAtMost_restrictCircuit _

/-- The circuit computing `x₀ ∧ ¬x₁`, with two gates. -/
private def andNotCircuit : Circuit Unbounded.signature 2 1 :=
  (Circuit.oneGate (Unbounded.Op.and 2) (id : Fin 2 → Fin 2)).comp
    ((Circuit.wiring Unbounded.signature ![(0 : Fin 2)]).append
      (Circuit.oneGate Unbounded.Op.not ![(1 : Fin 2)]))

/-- `andNotCircuit` computes `x₀ ∧ ¬x₁`. -/
@[simp] private theorem eval_andNotCircuit (v : Fin 2 → Bool) :
    andNotCircuit.eval Unbounded.interpretation v 0 = (v 0 && !v 1) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : Bool, v = ![a, b] :=
    ⟨v 0, v 1, funext fun j => by fin_cases j <;> rfl⟩
  cases a <;> cases b <;> decide

/-- `andNotCircuit` has two gates. -/
@[simp] private theorem size_andNotCircuit : andNotCircuit.size = 2 := by
  simp only [andNotCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
    Circuit.size_oneGate, Nat.zero_add]

/-- `andNotCircuit` has depth at most two. -/
private theorem depth_andNotCircuit_le : andNotCircuit.depth ≤ 2 := by
  have h := Circuit.depth_append_le (Circuit.wiring Unbounded.signature ![(0 : Fin 2)])
    (Circuit.oneGate Unbounded.Op.not ![(1 : Fin 2)])
  rw [Circuit.depth_wiring, Circuit.depth_oneGate] at h
  have h' := Circuit.depth_comp_le (Circuit.oneGate (Unbounded.Op.and 2) (id : Fin 2 → Fin 2))
    ((Circuit.wiring Unbounded.signature ![(0 : Fin 2)]).append
      (Circuit.oneGate Unbounded.Op.not ![(1 : Fin 2)]))
  rw [Circuit.depth_oneGate] at h'
  exact h'.trans (by omega)

/-- `andNotCircuit` has fan-in at most two. -/
private theorem fanInAtMost_andNotCircuit : andNotCircuit.FanInAtMost 2 :=
  ((Circuit.fanInAtMost_oneGate _ _ _).2 le_rfl).comp
    ((Circuit.fanInAtMost_wiring _ _).append ((Circuit.fanInAtMost_oneGate _ _ _).2 one_le_two))

/-- The circuit `E_Q` for a circuit `C` with one output: true at `x` exactly when `C` is true with
the bits of `Q` set to `true` and false with the bits of `Q` set to `false`. For a monotone `C`,
this says that `C` is undetermined at `x` by the bits outside `Q` (`eval_undeterminedCircuit`,
`Cslib.BitString.isUndetermined_iff_of_monotone`). This construction is ours; compare the circuit
of [Chattopadhyay–Zuckerman, proof of Theorem 4.1][ChattopadhyayZuckerman2019]. -/
def undeterminedCircuit (C : Circuit Unbounded.signature n 1) (Q : Finset (Fin n)) :
    Circuit Unbounded.signature n 1 :=
  andNotCircuit.comp ((C.comp (fixCircuit Q true)).append (C.comp (fixCircuit Q false)))

/-- `E_Q` computes `C` with `Q` set to `true` and not `C` with `Q` set to `false`. -/
theorem eval_undeterminedCircuit (C : Circuit Unbounded.signature n 1) (Q : Finset (Fin n))
    (x : BitString n) :
    (undeterminedCircuit C Q).eval Unbounded.interpretation x 0 =
      (C.eval Unbounded.interpretation (Q.piecewise (fun _ => true) x) 0 &&
        !C.eval Unbounded.interpretation (Q.piecewise (fun _ => false) x) 0) := by
  have e0 (a b : Fin 1 → Bool) : (Fin.append a b : Fin 2 → Bool) 0 = a 0 := Fin.append_left a b 0
  have e1 (a b : Fin 1 → Bool) : (Fin.append a b : Fin 2 → Bool) 1 = b 0 := Fin.append_right a b 0
  rw [undeterminedCircuit, Circuit.eval_comp, eval_andNotCircuit, Circuit.eval_append, e0, e1,
    Circuit.eval_comp, Circuit.eval_comp, eval_fixCircuit, eval_fixCircuit]

/-- **The size of `E_Q`**, our count: exactly `2 m + 6` gates for a circuit `C` of `m` gates. -/
@[simp] theorem size_undeterminedCircuit (C : Circuit Unbounded.signature n 1)
    (Q : Finset (Fin n)) : (undeterminedCircuit C Q).size = 2 * C.size + 6 := by
  simp only [undeterminedCircuit, Circuit.size_comp, Circuit.size_append, size_fixCircuit,
    size_andNotCircuit]
  ring

/-- **The depth of `E_Q`**, our count: at most `d + 3` for a circuit `C` of depth `d`. -/
theorem depth_undeterminedCircuit_le (C : Circuit Unbounded.signature n 1) (Q : Finset (Fin n)) :
    (undeterminedCircuit C Q).depth ≤ C.depth + 3 := by
  have h (b : Bool) : (C.comp (fixCircuit Q b)).depth ≤ C.depth + 1 :=
    (Circuit.depth_comp_le _ _).trans (Nat.add_le_add_left (depth_fixCircuit_le Q b) _)
  refine (Circuit.depth_comp_le _ _).trans ?_
  have := (Circuit.depth_append_le (C.comp (fixCircuit Q true)) (C.comp (fixCircuit Q false))).trans
    (max_le (h true) (h false))
  have := depth_andNotCircuit_le
  omega

/-- **The fan-in of `E_Q`**: at most `max r 2` for a circuit `C` of fan-in at most `r`. -/
theorem fanInAtMost_undeterminedCircuit {C : Circuit Unbounded.signature n 1} {r : ℕ}
    (hC : C.FanInAtMost r) (Q : Finset (Fin n)) :
    (undeterminedCircuit C Q).FanInAtMost (max r 2) :=
  (fanInAtMost_andNotCircuit.mono (le_max_right _ _)).comp (Circuit.FanInAtMost.append
    ((hC.mono (le_max_left _ _)).comp ((fanInAtMost_fixCircuit Q true).mono (le_max_right _ _)))
    ((hC.mono (le_max_left _ _)).comp ((fanInAtMost_fixCircuit Q false).mono (le_max_right _ _))))

/-! ### Theorem 4.1 of Chattopadhyay and Zuckerman -/

/-- **Coalition influence under polylogarithmic independence, with the exact independence function
`independence`**
[Chattopadhyay–Zuckerman, Theorem 4.1, influence part][ChattopadhyayZuckerman2019]. Let `C` be a
circuit of the unbounded fan-in basis computing a monotone function `f`, of depth at most `d`, with
`2 size C + 6 ≤ 2 ^ p` and fan-in less than `2 ^ p`, where `p ≥ 2`. If a coalition `Q` has
influence at most `ε₂` on `f` under the uniform distribution, then it has influence at most
`ε₂ + 2 ^ (-p)` under every `independence (d + 3) p`-wise independent distribution.

The size and depth conditions are those of Braverman's theorem for our circuit `E_Q`
(`undeterminedCircuit`); the theorem is stated for one coalition and one distribution. -/
theorem coalitionInfluence_le_of_independence_le {D : PMF (BitString n)} {d p t : ℕ} {ε₂ : ℝ}
    (hp : 2 ≤ p) (C : Circuit Unbounded.signature n 1)
    (hmono : Monotone fun x => C.eval Unbounded.interpretation x 0)
    (hfan : C.FanInAtMost (2 ^ p - 1)) (hsize : 2 * C.size + 6 ≤ 2 ^ p) (hd : C.depth ≤ d)
    (Q : Finset (Fin n))
    (hQ : coalitionInfluence (Probability.PMF.uniformOfFintype (BitString n)) Q
      (fun x => C.eval Unbounded.interpretation x 0) ≤ ε₂)
    (ht : independence (d + 3) p ≤ t) (hD : IsKWiseIndependent t D) :
    coalitionInfluence D Q (fun x => C.eval Unbounded.interpretation x 0) ≤ ε₂ + 1 / 2 ^ p := by
  set E := undeterminedCircuit C Q
  have hE (x : BitString n) :
      (if IsUndetermined Q (fun x => C.eval Unbounded.interpretation x 0) x then (1 : ℝ) else 0) =
        bitVal ℝ (E.eval Unbounded.interpretation x 0) := by
    have h : IsUndetermined Q (fun x => C.eval Unbounded.interpretation x 0) x ↔
        E.eval Unbounded.interpretation x 0 = true := by
      rw [isUndetermined_iff_of_monotone hmono, eval_undeterminedCircuit, Bool.and_eq_true,
        Bool.not_eq_true']
    exact if_congr h rfl rfl
  have h4 : 4 ≤ 2 ^ p := (Nat.pow_le_pow_right two_pos hp).trans' (by norm_num)
  have hfools := fools_of_independence_le (by omega) E
    ((fanInAtMost_undeterminedCircuit hfan Q).mono (max_le le_rfl (by omega)))
    (by rw [size_undeterminedCircuit]; exact hsize)
    ((depth_undeterminedCircuit_le C Q).trans (by omega)) ht hD
  have hX : coalitionInfluence D Q (fun x => C.eval Unbounded.interpretation x 0) =
      ∑ x, (D x).toReal * bitVal ℝ (E.eval Unbounded.interpretation x 0) :=
    sum_congr rfl fun x _ => by rw [hE]
  have hU : coalitionInfluence (Probability.PMF.uniformOfFintype (BitString n)) Q
      (fun x => C.eval Unbounded.interpretation x 0) =
      𝔼 x, bitVal ℝ (E.eval Unbounded.interpretation x 0) := by
    rw [coalitionInfluence_uniformOfFintype]
    exact expect_congr rfl fun x _ => hE x
  rw [hX]
  rw [hU] at hQ
  have := (abs_le.1 hfools).2
  linarith

/-- **The bias under polylogarithmic independence, with the exact independence function
`independence`**
[Chattopadhyay–Zuckerman, Theorem 4.1, bias part][ChattopadhyayZuckerman2019]. Let `C` be a circuit
of the unbounded fan-in basis of depth at most `d`, with at most `2 ^ p` gates and fan-in less than
`2 ^ p`, where `p ≥ 1`. If `C` is true with probability within `ε₁` of `1 / 2` under the uniform
distribution, then it is under every `independence d p`-wise independent distribution with error
`ε₁ + 2 ^ (-p)`. Monotonicity is not needed. -/
theorem abs_sum_bitVal_sub_half_le_of_independence_le {D : PMF (BitString n)} {d p t : ℕ}
    {ε₁ : ℝ} (hp : 1 ≤ p) (C : Circuit Unbounded.signature n 1)
    (hfan : C.FanInAtMost (2 ^ p - 1)) (hsize : C.size ≤ 2 ^ p) (hd : C.depth ≤ d)
    (hbias : |𝔼 x, bitVal ℝ (C.eval Unbounded.interpretation x 0) - 1 / 2| ≤ ε₁)
    (ht : independence d p ≤ t) (hD : IsKWiseIndependent t D) :
    |∑ x, (D x).toReal * bitVal ℝ (C.eval Unbounded.interpretation x 0) - 1 / 2| ≤
      ε₁ + 1 / 2 ^ p := by
  have h := fools_of_independence_le hp C hfan hsize hd ht hD
  unfold Fools at h
  have := abs_sub_le (∑ x, (D x).toReal * bitVal ℝ (C.eval Unbounded.interpretation x 0))
    (𝔼 x, bitVal ℝ (C.eval Unbounded.interpretation x 0)) (1 / 2)
  linarith

/-- **The bias under polylogarithmic independence**
[Chattopadhyay–Zuckerman, Theorem 4.1, bias part][ChattopadhyayZuckerman2019]: the bias part with
the closed-form independence `(64 p) ^ ((2 d + 3) (d + 7) + 1)` of `independence_le`. -/
theorem abs_sum_bitVal_sub_half_le_of_isKWiseIndependent {D : PMF (BitString n)} {d p t : ℕ}
    {ε₁ : ℝ} (hp : 1 ≤ p) (C : Circuit Unbounded.signature n 1)
    (hfan : C.FanInAtMost (2 ^ p - 1)) (hsize : C.size ≤ 2 ^ p) (hd : C.depth ≤ d)
    (hbias : |𝔼 x, bitVal ℝ (C.eval Unbounded.interpretation x 0) - 1 / 2| ≤ ε₁)
    (ht : (64 * p) ^ ((2 * d + 3) * (d + 7) + 1) ≤ t) (hD : IsKWiseIndependent t D) :
    |∑ x, (D x).toReal * bitVal ℝ (C.eval Unbounded.interpretation x 0) - 1 / 2| ≤
      ε₁ + 1 / 2 ^ p :=
  abs_sum_bitVal_sub_half_le_of_independence_le hp C hfan hsize hd hbias
    ((independence_le hp d).trans ht) hD

/-- **Resilient monotone `AC⁰` functions are resilient under polylogarithmic independence**
[Chattopadhyay–Zuckerman, Theorem 4.1, influence part][ChattopadhyayZuckerman2019]. Let `C` be a
circuit of the unbounded fan-in basis computing a monotone `(q, ε₂)`-resilient function, of depth
at most `d`, with `2 size C + 6 ≤ 2 ^ p` and fan-in less than `2 ^ p`, where `p ≥ 2`. Then the
function is `t`-independent `(q, ε₂ + 2 ^ (-p))`-resilient for every
`t ≥ (64 p) ^ ((2 d + 9) (d + 10) + 1)`.

For a circuit of `m` gates and fan-in `r`, taking
`p ≥ max (log₂ (2 m + 6)) (max (log₂ (r + 1)) (log₂ (1 / ε)))` this is
`t = (log (max m (r + 1) / ε)) ^ O(d²)`; the fan-in term is needed since the fan-in of this model is
not bounded by the size. Chattopadhyay and Zuckerman have the exponent
`3 d + 6`, which is not claimed here: the exponent and constants are ours. -/
theorem isKWiseResilient_of_isResilient {d p q t : ℕ} {ε₂ : ℝ} (hp : 2 ≤ p)
    (C : Circuit Unbounded.signature n 1)
    (hmono : Monotone fun x => C.eval Unbounded.interpretation x 0)
    (hfan : C.FanInAtMost (2 ^ p - 1)) (hsize : 2 * C.size + 6 ≤ 2 ^ p) (hd : C.depth ≤ d)
    (hres : IsResilient q ε₂ fun x => C.eval Unbounded.interpretation x 0)
    (ht : (64 * p) ^ ((2 * d + 9) * (d + 10) + 1) ≤ t) :
    IsKWiseResilient t q (ε₂ + 1 / 2 ^ p) fun x => C.eval Unbounded.interpretation x 0 := by
  have he : (2 * (d + 3) + 3) * (d + 3 + 7) + 1 = (2 * d + 9) * (d + 10) + 1 := by ring
  have hi := independence_le (by omega : 1 ≤ p) (d + 3)
  rw [he] at hi
  exact fun Q hQ D hD => coalitionInfluence_le_of_independence_le hp C hmono hfan hsize hd Q
    (hres Q hQ) (hi.trans ht) hD

end Cslib.Circuits.Boolean.Braverman

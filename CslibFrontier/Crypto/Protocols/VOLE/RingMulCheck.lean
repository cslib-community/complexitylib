/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.RingMAC
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformBound

/-!
# The masked multiplication check over `ZMod n`

Hazay and Yang [HazayYang2024], §5.1, Equation (1), check a multiplication `z = x * y` of
IT-MAC-authenticated values over `ZMod (N ^ ζ)` with one extra authenticated random value `r`.
With keys `k_w = w * Δ + m_w`, the prover sends the masked coefficients

`c₁ = x * m_y + y * m_x - m_z + r` and `c₀ = m_x * m_y + m_r`,

and the verifier accepts when `k_r + k_x * k_y - k_z * Δ = c₁ * Δ + c₀`. This file proves the
three properties of this check:

* completeness for every commutative ring (`ringMulCheck_complete`);
* exact simulation of the verifier's view `(k_r, c₁, c₀)` for every finite commutative ring and
  every key: the mask `(r, m_r)` makes `(k_r, c₁)` uniform, and `c₀` is then determined by the
  verification equation (`ringMulCheckView_eq_simulate`);
* soundness over `ZMod n`: if `x * y ≠ z`, the acceptance condition is a quadratic in `Δ` with
  leading coefficient `x * y - z ≠ 0`, so it holds with probability at most `2 / n.minFac` under a
  uniform key (`toOuterMeasure_ringMulCheck_le`, `toOuterMeasure_ringMulCheck_bind_le`). For the
  Damgård–Jurik modulus `(p * q) ^ ζ` with primes `p < q` this is `2 / p` (`Nat.minFac_mul_pow`).

The coefficients reuse `voleMulCrossTerm` and `voleMulConstTerm` from `Basic.lean`; their
soundness counterpart in `MulCheck.lean` needs a field. The results concern a single check with
a key the prover never sees; they do not establish security of the protocols of [HazayYang2024].

## Main definitions

* `Cslib.Crypto.Protocols.VOLE.ringMulCheckReply`: the honest masked coefficients `(c₁, c₀)`.
* `Cslib.Crypto.Protocols.VOLE.RingMulCheckAccepts`: the verifier's equation.
* `Cslib.Crypto.Protocols.VOLE.ringMulCheckView`,
  `Cslib.Crypto.Protocols.VOLE.ringMulCheckSimulate`: the honest view and its simulator.

## Main results

* `Cslib.Crypto.Protocols.VOLE.ringMulCheck_complete`
* `Cslib.Crypto.Protocols.VOLE.ringMulCheckView_eq_simulate`
* `Cslib.Crypto.Protocols.VOLE.card_filter_ringMulCheck_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_ringMulCheck_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_ringMulCheck_bind_le`

## References

* [C. Hazay, Y. Yang, *Toward Malicious Constant-Rate 2PC via Arithmetic
  Garbling*][HazayYang2024]
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability
open scoped ENNReal

section CommRing

variable {R : Type*} [CommRing R]

/-- The honest masked coefficients `(c₁, c₀)` of [HazayYang2024], §5.1, Equation (1), for
authenticated values `x`, `y`, `z` with MAC masks `m_x`, `m_y`, `m_z` and an extra authenticated
random value `r` with mask `m_r`. -/
@[expose] def ringMulCheckReply (x m_x y m_y m_z r m_r : R) : R × R :=
  (voleMulCrossTerm x m_x y m_y m_z + r, voleMulConstTerm m_x m_y + m_r)

/-- The verifier's equation `k_r + k_x * k_y - k_z * Δ = c₁ * Δ + c₀` on keys
`k_x`, `k_y`, `k_z`, `k_r`, global key `Δ` and received coefficients `reply = (c₁, c₀)`. -/
@[expose] def RingMulCheckAccepts (k_x k_y k_z k_r delta : R) (reply : R × R) : Prop :=
  k_r + k_x * k_y - k_z * delta = reply.1 * delta + reply.2

instance [DecidableEq R] (k_x k_y k_z k_r delta : R) (reply : R × R) :
    Decidable (RingMulCheckAccepts k_x k_y k_z k_r delta reply) :=
  inferInstanceAs (Decidable (_ = _))

/-- **Completeness.** If `x * y = z`, the honest coefficients pass the check under every key. -/
theorem ringMulCheck_complete {x y z : R} (m_x m_y m_z r m_r delta : R) (hxyz : x * y = z) :
    RingMulCheckAccepts (x * delta + m_x) (y * delta + m_y) (z * delta + m_z) (r * delta + m_r)
      delta (ringMulCheckReply x m_x y m_y m_z r m_r) := by
  unfold RingMulCheckAccepts ringMulCheckReply
  have h := voleMulCheck (v_x := m_x) (v_y := m_y) (v_z := m_z) (delta := delta) rfl rfl rfl hxyz
  dsimp only
  linear_combination h

/-- The verifier's view `(k_r, c₁, c₀)` of an honest run, as a function of the mask
`rm = (r, m_r)`. The keys `k_x`, `k_y`, `k_z` and `Δ` are fixed by the setup. -/
@[expose] def ringMulCheckView (x m_x y m_y m_z delta : R) (rm : R × R) : R × R × R :=
  (rm.1 * delta + rm.2, ringMulCheckReply x m_x y m_y m_z rm.1 rm.2)

/-- The simulator's view: `(k_r, c₁)` is the given pair and `c₀` is the unique value that
satisfies the verifier's equation for the keys `k_x`, `k_y`, `k_z` and `Δ`. -/
@[expose] def ringMulCheckSimulate (k_x k_y k_z delta : R) (kc : R × R) : R × R × R :=
  (kc.1, kc.2, kc.1 + k_x * k_y - k_z * delta - kc.2 * delta)

/-- The simulated view always satisfies the verifier's equation. -/
theorem ringMulCheckSimulate_accepts (k_x k_y k_z delta : R) (kc : R × R) :
    RingMulCheckAccepts k_x k_y k_z (ringMulCheckSimulate k_x k_y k_z delta kc).1 delta
      (ringMulCheckSimulate k_x k_y k_z delta kc).2 := by
  unfold RingMulCheckAccepts ringMulCheckSimulate
  ring

/-- The mask `(r, m_r) ↦ (k_r, c₁)` is a bijection of `R × R` for every key `Δ`. -/
private def ringMulCheckMaskEquiv (x m_x y m_y m_z delta : R) : R × R ≃ R × R where
  toFun rm := (rm.1 * delta + rm.2, voleMulCrossTerm x m_x y m_y m_z + rm.1)
  invFun kc := (kc.2 - voleMulCrossTerm x m_x y m_y m_z,
    kc.1 - (kc.2 - voleMulCrossTerm x m_x y m_y m_z) * delta)
  left_inv rm := by
    ext <;> dsimp only <;> ring
  right_inv kc := by
    ext <;> dsimp only <;> ring

/-- **Exact simulation of the verifier's view.** If `x * y = z`, then under a uniform mask
`(r, m_r)` the honest view `(k_r, c₁, c₀)` has the simulator's distribution, which uses only the
keys and `Δ`. This holds for every key `Δ` and every finite commutative ring. -/
theorem ringMulCheckView_eq_simulate [Fintype R] [Nonempty R] {x y z : R}
    (m_x m_y m_z delta : R) (hxyz : x * y = z) :
    (PMF.uniformOfFintype (R × R)).map (ringMulCheckView x m_x y m_y m_z delta) =
      (PMF.uniformOfFintype (R × R)).map
        (ringMulCheckSimulate (x * delta + m_x) (y * delta + m_y) (z * delta + m_z) delta) := by
  have hcomp : ringMulCheckView x m_x y m_y m_z delta =
      ringMulCheckSimulate (x * delta + m_x) (y * delta + m_y) (z * delta + m_z) delta ∘
        ringMulCheckMaskEquiv x m_x y m_y m_z delta := by
    funext rm
    have h := ringMulCheck_complete m_x m_y m_z rm.1 rm.2 delta hxyz
    unfold RingMulCheckAccepts at h
    simp only [ringMulCheckView, ringMulCheckSimulate, ringMulCheckMaskEquiv, ringMulCheckReply,
      Function.comp_apply, Equiv.coe_fn_mk, Prod.mk.injEq, true_and] at h ⊢
    linear_combination -h
  rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]

end CommRing

section ZMod

variable {n : ℕ} [NeZero n]

/-- **Soundness, counting form.** If `x * y ≠ z`, then for any fixed masks and any fixed
coefficients `reply`, at most `2 * (n / n.minFac)` keys `Δ ∈ ZMod n` accept. -/
theorem card_filter_ringMulCheck_le {x y z : ZMod n} (m_x m_y m_z r m_r : ZMod n)
    (reply : ZMod n × ZMod n) (hfalse : x * y ≠ z) :
    (Finset.univ.filter fun delta : ZMod n =>
      RingMulCheckAccepts (x * delta + m_x) (y * delta + m_y) (z * delta + m_z)
        (r * delta + m_r) delta reply).card ≤ 2 * (n / n.minFac) := by
  classical
  refine le_trans (Finset.card_le_card fun delta hdelta => ?_)
    (card_filter_quadratic_eq_zero_le (voleMulCrossTerm x m_x y m_y m_z + r - reply.1)
      (voleMulConstTerm m_x m_y + m_r - reply.2) (sub_ne_zero.mpr hfalse))
  rw [Finset.mem_filter] at hdelta ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have hc := hdelta.2
  unfold RingMulCheckAccepts at hc
  have hid := voleMulCheck_sub_eq (x := x) (y := y) (z := z)
    (v_x := m_x) (v_y := m_y) (v_z := m_z) (delta := delta) rfl rfl rfl
  linear_combination hc - hid

/-- **Soundness.** If `x * y ≠ z`, then for any fixed masks and coefficients the check accepts
under a uniform key with probability at most `2 / n.minFac`. -/
theorem toOuterMeasure_ringMulCheck_le {x y z : ZMod n} (m_x m_y m_z r m_r : ZMod n)
    (reply : ZMod n × ZMod n) (hfalse : x * y ≠ z) :
    (PMF.uniformOfFintype (ZMod n)).toOuterMeasure
      {delta | RingMulCheckAccepts (x * delta + m_x) (y * delta + m_y) (z * delta + m_z)
        (r * delta + m_r) delta reply} ≤ 2 / (n.minFac : ℝ≥0∞) := by
  classical
  have h := PMF.toOuterMeasure_uniformOfFintype_le_div (α := ZMod n) (A := 2)
    (B := n.minFac) (P := fun delta => RingMulCheckAccepts (x * delta + m_x) (y * delta + m_y)
      (z * delta + m_z) (r * delta + m_r) delta reply) (Nat.minFac_pos n) (by
    rw [ZMod.card]
    calc n.minFac * _ ≤ n.minFac * (2 * (n / n.minFac)) :=
          Nat.mul_le_mul_left _ (card_filter_ringMulCheck_le m_x m_y m_z r m_r reply hfalse)
      _ = 2 * (n.minFac * (n / n.minFac)) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left _ (Nat.mul_div_le n n.minFac))
  exact_mod_cast h

/-- **Soundness against a randomized prover.** The prover's state `s`, drawn before the
independent uniform key, determines the values, masks and coefficients. The bad event includes
the false multiplication, so no assumption on the prover's distribution is needed. The prover
sees neither the key nor the verifier's keys before committing to its coefficients. -/
theorem toOuterMeasure_ringMulCheck_bind_le {S : Type} (prover : PMF S)
    (x y z m_x m_y m_z r m_r : S → ZMod n) (reply : S → ZMod n × ZMod n) :
    (do
      let s ← prover
      let delta ← PMF.uniformOfFintype (ZMod n)
      return (s, delta)).toOuterMeasure
      {sd : S × ZMod n | x sd.1 * y sd.1 ≠ z sd.1 ∧
        RingMulCheckAccepts (x sd.1 * sd.2 + m_x sd.1) (y sd.1 * sd.2 + m_y sd.1)
          (z sd.1 * sd.2 + m_z sd.1) (r sd.1 * sd.2 + m_r sd.1) sd.2 (reply sd.1)} ≤
        2 / (n.minFac : ℝ≥0∞) := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.toOuterMeasure_bind_apply]
  refine PMF.tsum_mul_le_of_forall_le prover fun s => ?_
  change ((PMF.uniformOfFintype (ZMod n)).map fun delta => (s, delta)).toOuterMeasure _ ≤ _
  rw [PMF.toOuterMeasure_map_apply]
  by_cases hfalse : x s * y s ≠ z s
  · refine le_trans (MeasureTheory.measure_mono ?_)
      (toOuterMeasure_ringMulCheck_le (m_x s) (m_y s) (m_z s) (r s) (m_r s) (reply s) hfalse)
    intro delta hdelta
    exact hdelta.2
  · simp [hfalse]

end ZMod

end Cslib.Crypto.Protocols.VOLE

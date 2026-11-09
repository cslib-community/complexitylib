/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.NOF.TwoParty
import Complexity.Probability.PMF

/-!
Regression clients for number-on-forehead protocols: running a protocol, the trivial protocol, a
lower bound from the definition, cylinder intersections (one example and one non-example), the
discrepancy of a constant function, and, through the two-player bridge, the two-party inner-product
discrepancy bound read as a lower bound on two-player NOF public-coin protocols.
-/

open Cslib Cslib.Communication Cslib.Communication.NOF Finset Probability

namespace CommunicationNOFTests

/-! ### Running a protocol -/

/-- Three players hold bits; player `0` announces the conjunction of the two bits it sees, which
are `x 1` and `x 2`. -/
private def andProtocol : NOF.Protocol (fun _ : Fin 3 => Bool) Bool :=
  .speak 0 (fun v => v ⟨1, by decide⟩ && v ⟨2, by decide⟩) (.output false) (.output true)

example : andProtocol.run ![false, true, true] = true := rfl

example : andProtocol.run ![true, true, false] = false := rfl

example : andProtocol.depth = 1 := rfl

/-- Player `0` cannot see its own bit: the protocol ignores `x 0`. -/
example (x : Fin 3 → Bool) (b : Bool) :
    andProtocol.run (Function.update x 0 b) = andProtocol.run x := by
  simp only [andProtocol, NOF.Protocol.run_speak, NOF.Protocol.run_output, view_update_self]

/-! ### The trivial protocol -/

/-- With three players holding `n`-bit strings, every Boolean function has a protocol with `n + 1`
bits: player `1` writes `x 0`, after which player `0` knows the whole input. -/
example (n : ℕ) (f : (Fin 3 → BitString n) → Bool) : NOF.Protocol.ecomplexityFun f ≤ n + 1 :=
  NOF.Protocol.ecomplexityFun_le_succ (X := fun _ : Fin 3 => BitString n) (i := 0) (j := 1)
    (by decide)
    (fun v => v ⟨0, by decide⟩) id (fun _ => rfl) f

/-! ### A lower bound from the definition -/

/-- The parity of three bits is not constant, so every protocol computing it writes a bit. -/
example : 1 ≤ NOF.Protocol.ecomplexityFun fun x : Fin 3 → Bool => x 0 ^^ x 1 ^^ x 2 := by
  refine NOF.Protocol.le_ecomplexityFun_iff.mpr fun p hp => ?_
  cases p with
  | output z =>
    have h0 := congrFun hp ![false, false, false]
    have h1 := congrFun hp ![true, false, false]
    simp only [NOF.Protocol.run_output] at h0 h1
    exact absurd (h0.symm.trans h1) (by decide)
  | speak i send p₀ p₁ => simp

/-! ### Cylinder intersections -/

/-- With three players, the inputs with `x 0 = x 1` form a cylinder intersection: player `2` sees
both bits and accepts when they agree, and the other players accept everything. -/
example : IsCylinderIntersection {x : Fin 3 → Bool | x 0 = x 1} := by
  refine isCylinderIntersection_iff.mpr
    ⟨fun i v => if h : i = 2 then v ⟨0, by rw [h]; decide⟩ == v ⟨1, by rw [h]; decide⟩ else true,
      ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, mem_cylinderIntersection, Fin.forall_fin_succ, view_apply,
    Fin.isValue, Fin.reduceEq, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, dite_eq_right_iff,
    IsEmpty.forall_iff, and_true, true_and]
  simp

/-- With two players, the inputs with `x 0 = x 1` do not form a cylinder intersection: cylinder
intersections of two players are rectangles. -/
example : ¬IsCylinderIntersection {x : Fin 2 → Bool | x 0 = x 1} := by
  rintro hC
  obtain ⟨φ, hφ⟩ := isCylinderIntersection_iff.mp hC
  have mem (x : Fin 2 → Bool) : x 0 = x 1 ↔ ∀ i, φ i (view i x) = true :=
    Set.ext_iff.mp hφ x
  have h0 := (mem ![false, false]).mp rfl
  have h1 := (mem ![true, true]).mp rfl
  -- The input `(true, false)` passes both tests: player `0` sees `false` and player `1` sees
  -- `true`, as on the inputs `(false, false)` and `(true, true)`.
  have h := (mem ![true, false]).mpr (Fin.forall_fin_two.mpr
    ⟨(view_zero_eq_iff.mpr rfl : view 0 ![true, false] = view 0 ![false, false]) ▸ h0 0,
      (view_one_eq_iff.mpr rfl : view 1 ![true, false] = view 1 ![true, true]) ▸ h1 1⟩)
  exact absurd h (by decide)

/-! ### Discrepancy -/

/-- A constant function has discrepancy one under every distribution. -/
example (ν : PMF (Fin 3 → Bool)) : NOF.discrepancy ν (fun _ => false) = 1 := by
  refine le_antisymm discrepancy_le_one ?_
  have h := abs_sum_le_discrepancy ν (fun _ => false) fun _ _ => true
  simpa [BitString.signVal_false, Cslib.Probability.PMF.sum_toReal] using h

/-- Through the two-player bridge, the two-party bound on the discrepancy of the inner product
is a bound on the NOF discrepancy of the inner product of `x 0` and `x 1`. -/
theorem discrepancy_dotProduct_fin_two_sq_mul_two_pow_le (n : ℕ) :
    NOF.discrepancy (PMF.uniformOfFintype (Fin 2 → BitString n)) (fun x => x 0 ⬝ᵥ x 1) ^ 2 *
      2 ^ n ≤ 1 := by
  rw [discrepancy_fin_two, Cslib.Probability.PMF.uniformOfFintype_map_equiv]
  exact discrepancy_dotProduct_sq_mul_two_pow_le n

/-- So two-player NOF public-coin protocols computing the inner product with error `1 / 2 - γ` and
`c` bits have `(2 γ)² 2 ^ n ≤ 4 ^ c`, as for two-party protocols. -/
example {n c : ℕ} {γ : ℝ} {μ : NOF.PublicCoin (fun _ : Fin 2 => BitString n) Bool}
    (hμ : μ.Solves (1 / 2 - γ) (fun x b => x 0 ⬝ᵥ x 1 = b) Set.univ) (hc : μ.depth ≤ c)
    (hγ : 0 ≤ γ) : (2 * γ) ^ 2 * 2 ^ n ≤ 4 ^ c := by
  set D := NOF.discrepancy (PMF.uniformOfFintype (Fin 2 → BitString n)) fun x => x 0 ⬝ᵥ x 1
  have h : 2 * γ ≤ 2 ^ c * D := hμ.two_mul_le_two_pow_mul_discrepancy hc _
  have hD : D ^ 2 * 2 ^ n ≤ 1 := discrepancy_dotProduct_fin_two_sq_mul_two_pow_le n
  have hsq : (2 * γ) ^ 2 ≤ (2 ^ c * D) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
  have h4 : ((2 : ℝ) ^ c) ^ 2 = 4 ^ c := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc (2 * γ) ^ 2 * 2 ^ n ≤ (2 ^ c * D) ^ 2 * 2 ^ n :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = 4 ^ c * (D ^ 2 * 2 ^ n) := by rw [mul_pow, h4, mul_assoc]
    _ ≤ 4 ^ c * 1 := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = 4 ^ c := mul_one _

end CommunicationNOFTests

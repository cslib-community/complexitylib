/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Cube
public import CslibFrontier.Computability.Communication.NOF.TwoParty
import CslibFrontier.Foundations.Data.BitString.Sign.BigOperators
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.ExpectPi
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# XOR products and discrepancy

The cube expectation tensorizes for coordinatewise XOR products. For two players it is at
most four times uniform discrepancy. Together these give the elementary bound
`disc(g^⊕k)^4 ≤ (4 disc(g))^k`. This is a weaker alternative to the Lee--Shraibman--Špalek
XOR bound used in Chattopadhyay--Filmus--Koroth--Meir--Pitassi, arXiv:1904.13056v4,
Theorem 2.11. It retains exponential decay but loses a factor four in the exponent.
No lifting simulation is claimed in this module.
-/

public section

namespace Cslib.Communication

open Finset BitString Probability
open scoped BigOperators

/-- Multiplying a gadget's sign by two local signs costs at most four times its discrepancy.
The local signs form a four-leaf protocol. -/
theorem abs_sum_mul_local_signs_le {X Y : Type*} [Fintype X] [Fintype Y]
    (ν : PMF (X × Y)) (g : X → Y → Bool) (a : X → Bool) (b : Y → Bool) :
    |∑ x, ∑ y, (ν (x, y)).toReal * signVal (g x y) *
        (signVal (a x) * signVal (b y))| ≤ 4 * discrepancy ν g := by
  let p : Protocol X Y Bool := .alice a
    (.bob b (.output false) (.output true)) (.bob b (.output true) (.output false))
  have hp (x : X) (y : Y) : signVal (p.run x y) = signVal (a x) * signVal (b y) := by
    cases ha : a x <;> cases hb : b y <;> simp [p, ha, hb]
  have h := p.abs_sum_mul_signVal_le ν g
  simp only [hp] at h
  simpa [p] using h

/-- Uniform-average form of the local-sign discrepancy bound. -/
theorem abs_expect_mul_local_signs_le {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (g : X → Y → Bool) (a : X → Bool) (b : Y → Bool) :
    |𝔼 x, 𝔼 y, signVal (g x y) * (signVal (a x) * signVal (b y))| ≤
      4 * discrepancy (PMF.uniformOfFintype (X × Y)) g := by
  have h := abs_sum_mul_local_signs_le (PMF.uniformOfFintype (X × Y)) g a b
  simpa [Fintype.expect_eq_sum_div_card, PMF.uniformOfFintype_apply,
    Fintype.card_prod, ENNReal.toReal_inv, Nat.cast_mul,
    sum_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ← mul_sum] using h

end Cslib.Communication

namespace Cslib.Communication.NOF

open Finset Function BitString Probability
open scoped BigOperators

variable {ι κ Λ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype Λ]

/-- Apply `f` to each coordinate of the players' inputs and XOR the answers. -/
@[expose] def xorProduct (f : (ι → Λ) → Bool) (x : ι → κ → Λ) : Bool :=
  ∑ r, f (fun i => x i r)

/-- The cube expectation tensorizes for XOR products. -/
theorem cubeExpectation_xorProduct (f : (ι → Λ) → Bool) :
    cubeExpectation (xorProduct (κ := κ) f) = cubeExpectation f ^ Fintype.card κ := by
  classical
  let H (a b : ι → Λ) : ℝ := ∏ S : Finset ι, signVal (f (S.piecewise b a))
  have hcorner (a b : ι → κ → Λ) :
      (∏ S : Finset ι, signVal (xorProduct f (S.piecewise b a))) =
        ∏ r, H (fun i => a i r) (fun i => b i r) := by
    simp only [xorProduct, signVal_sum]
    rw [prod_comm]
    refine prod_congr rfl fun r _ => ?_
    dsimp [H]
    refine prod_congr rfl fun S _ => ?_
    congr 2
    funext i
    by_cases hi : i ∈ S <;> simp [Finset.piecewise, hi]
  unfold cubeExpectation
  simp_rw [hcorner]
  rw [Fintype.expect_equiv (Equiv.piComm fun (_ : ι) (_ : κ) => Λ)
    (fun a : ι → κ → Λ => 𝔼 b : ι → κ → Λ,
      ∏ r, H (fun i => a i r) (fun i => b i r))
    (fun a : κ → ι → Λ => 𝔼 b : ι → κ → Λ,
      ∏ r, H (a r) (fun i => b i r)) (fun _ => rfl)]
  have hb (a : κ → ι → Λ) :
      (𝔼 b : ι → κ → Λ, ∏ r, H (a r) (fun i => b i r)) =
        ∏ r, 𝔼 b : ι → Λ, H (a r) b := by
    rw [Fintype.expect_equiv (Equiv.piComm fun (_ : ι) (_ : κ) => Λ)
      (fun b : ι → κ → Λ => ∏ r, H (a r) (fun i => b i r))
      (fun b : κ → ι → Λ => ∏ r, H (a r) (b r)) (fun _ => rfl),
      ← Fintype.prod_expect]
  simp_rw [hb]
  rw [← Fintype.prod_expect (fun (_ : κ) (a : ι → Λ) => 𝔼 b, H a b)]
  simp only [prod_const, card_univ, H]

/-- The discrepancy bound for an XOR product, before estimating its one-copy cube expectation. -/
theorem discrepancy_xorProduct_pow_le [Nonempty ι] [Nonempty Λ]
    (f : (ι → Λ) → Bool) :
    discrepancy (PMF.uniformOfFintype (ι → κ → Λ)) (xorProduct f) ^
      (2 ^ Fintype.card ι) ≤ cubeExpectation f ^ Fintype.card κ := by
  rw [← cubeExpectation_xorProduct]
  exact discrepancy_uniformOfFintype_pow_le _

private theorem expect_fin_two (F : (Fin 2 → Λ) → ℝ) :
    (𝔼 a, F a) = 𝔼 x, 𝔼 y, F ![x, y] := by
  rw [Fintype.expect_equiv (piFinTwoEquiv fun _ : Fin 2 => Λ) F
    (fun p : Λ × Λ => F ![p.1, p.2]) (fun _ => by congr; ext i; fin_cases i <;> rfl),
    Fintype.expect_prod_type]

/-- The two-player cube expectation is at most four times the uniform discrepancy. -/
theorem cubeExpectation_fin_two_le [Nonempty Λ] (f : (Fin 2 → Λ) → Bool) :
    cubeExpectation f ≤ 4 * Communication.discrepancy (PMF.uniformOfFintype (Λ × Λ))
      (fun x y => f ![x, y]) := by
  classical
  let g (x y : Λ) := f ![x, y]
  have hcorner (a b : Fin 2 → Λ) :
      (∏ S : Finset (Fin 2), signVal (f (S.piecewise b a))) =
        signVal (g (b 0) (b 1)) * (signVal (g (b 0) (a 1)) *
          signVal (g (a 0) (b 1))) * signVal (g (a 0) (a 1)) := by
    have hu : (univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
    rw [hu]
    have he (S : Finset (Fin 2)) : S.piecewise b a =
        ![if 0 ∈ S then b 0 else a 0, if 1 ∈ S then b 1 else a 1] := by
      ext i; fin_cases i <;> rfl
    rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_singleton]
    simp_rw [he]
    simp [g, mul_comm, mul_left_comm, mul_assoc]
  have hc : cubeExpectation f = 𝔼 x', 𝔼 y', 𝔼 x, 𝔼 y,
      signVal (g x y) * (signVal (g x y') * signVal (g x' y)) * signVal (g x' y') := by
    unfold cubeExpectation
    simp_rw [hcorner]
    simp_rw [expect_fin_two]
    rfl
  rw [hc]
  refine Finset.expect_le univ_nonempty fun x' _ =>
    Finset.expect_le univ_nonempty fun y' _ => ?_
  simp_rw [← Finset.expect_mul]
  calc
    _ ≤ |(𝔼 x, 𝔼 y, signVal (g x y) * (signVal (g x y') * signVal (g x' y))) *
        signVal (g x' y')| := le_abs_self _
    _ = |𝔼 x, 𝔼 y, signVal (g x y) * (signVal (g x y') * signVal (g x' y))| := by
      rw [abs_mul, abs_signVal, mul_one]
    _ ≤ _ := Communication.abs_expect_mul_local_signs_le g (fun x => g x y') (g x')

/-- Uniform two-player NOF discrepancy, expressed on a Cartesian product. -/
theorem discrepancy_uniform_fin_two [Nonempty Λ] (f : (Fin 2 → Λ) → Bool) :
    discrepancy (PMF.uniformOfFintype (Fin 2 → Λ)) f =
      Communication.discrepancy (PMF.uniformOfFintype (Λ × Λ)) (fun x y => f ![x, y]) := by
  rw [discrepancy_fin_two, PMF.uniformOfFintype_map_equiv]
  rfl

/-- An elementary discrepancy XOR bound: the fourth power of the XOR discrepancy is at most
`(4 disc(f))^k`. This loses a factor four in the exponent compared with the LSS bound. -/
theorem discrepancy_xorProduct_fourth_pow_le [Nonempty Λ] (f : (Fin 2 → Λ) → Bool) :
    discrepancy (PMF.uniformOfFintype (Fin 2 → κ → Λ)) (xorProduct f) ^ 4 ≤
      (4 * Communication.discrepancy (PMF.uniformOfFintype (Λ × Λ))
        (fun x y => f ![x, y])) ^ Fintype.card κ := by
  have h := discrepancy_xorProduct_pow_le (κ := κ) f
  norm_num only [Fintype.card_fin] at h
  have hnonneg : 0 ≤ cubeExpectation f :=
    (pow_nonneg discrepancy_nonneg _).trans (discrepancy_uniformOfFintype_pow_le f)
  exact h.trans (pow_le_pow_left₀ hnonneg (cubeExpectation_fin_two_le f) _)

end Cslib.Communication.NOF

namespace Cslib.Communication

open Finset Probability

/-- The two-party form of the elementary XOR bound, for any finite alphabet and any number
of gadget coordinates (including zero). -/
theorem discrepancy_xor_fourth_pow_le {κ Λ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Λ] [Nonempty Λ] (g : Λ → Λ → Bool) :
    discrepancy (PMF.uniformOfFintype ((κ → Λ) × (κ → Λ)))
      (fun x y => ∑ i, g (x i) (y i)) ^ 4 ≤
        (4 * discrepancy (PMF.uniformOfFintype (Λ × Λ)) g) ^ Fintype.card κ := by
  have h := NOF.discrepancy_xorProduct_fourth_pow_le (κ := κ)
    (fun v : Fin 2 → Λ => g (v 0) (v 1))
  rw [NOF.discrepancy_uniform_fin_two] at h
  simpa only [NOF.xorProduct, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end Cslib.Communication

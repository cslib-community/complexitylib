/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceParityCounter
import Complexity.Foundations.Data.Nat.LogLogSqrtLogPolylog
import Complexity.Foundations.Data.Nat.PolynomialBound.Log
import all Complexity.Computability.Complexity.FineGrained.SparseCountingScale
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Sharp resources for actual native parity leaves

Absorb initial-row search and all candidate evaluations into the single-loglog exponent of
one actual `countParity` certificate. Fixed additive exponents cover every exceptional size.
Only the older module's elementary query-count inequality is reused, not its interpolation
scale or its sparsification schedule. This finishes the polylogarithmic-density leaf step of
[OpenAI2026ETH], Appendix D.3, p. 57, toward [ChenJiangZhu2027], Lemma 3.2.
General-density sparsification and weighted original-input composition remain separate.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString Cslib.GenericRAM Cslib.Complexity Turing.MultiTapeTM
open Cslib.Logic.PL Cslib.Logic.PL.CNF SparseCNFLeafCounter
open SubexponentialSAT.SparseCountingScale

private theorem overhead_bounds (β : ℕ) {q : ℕ → ℕ} (hq : Cslib.PolynomiallyBounded q) :
    ∃ I J : ℕ, ∀ n m : ℕ, m ≤ Nat.clog 2 n ^ β * n →
      q (Nat.clog 2 n ^ β + Nat.log 2 (m + 2)) ≤ Nat.logLogSqrtLogScale n + I ∧
      (3 * n + 1) * (candidateTupleCount m (greedyRowListLength (Nat.clog 2 n ^ β) m) + 1) ≤
        (4 * 2 ^ J) * 2 ^ Nat.logLogSqrtLogScale n := by
  have hbig : Cslib.PolynomiallyBounded (fun n => 2 * Nat.clog 2 n ^ β * n + 4) := by
    fun_prop
  obtain ⟨e, he⟩ := hbig.exists_clog_le_mul_log
  obtain ⟨C, d, hq⟩ := Cslib.polynomiallyBounded_iff_le.mp hq
  let f (t : ℕ) := C * (t ^ β + e * (t + 1) + 1) ^ d
  have hf : Cslib.PolynomiallyBounded f := by dsimp only [f]; fun_prop
  obtain ⟨I, hI⟩ := Nat.exists_polynomial_clog_le_logLogSqrtLogScale_add hf
  let g (t : ℕ) := queryExpCoeff 1 β 20000 2 2 * (t + 1) ^ (β * 2 + 2 + 1)
  have hg : Cslib.PolynomiallyBounded g := by dsimp only [g]; fun_prop
  obtain ⟨J, hJ⟩ := Nat.exists_polynomial_clog_le_logLogSqrtLogScale_add hg
  refine ⟨I, J, fun n m hm => ?_⟩
  have hlog : Nat.log 2 (m + 2) ≤ e * (Nat.clog 2 n + 1) :=
    (Nat.log_le_clog 2 _).trans ((Nat.clog_mono_right 2 (by nlinarith :
      m + 2 ≤ 2 * Nat.clog 2 n ^ β * n + 4)).trans
      ((he n).trans (Nat.mul_le_mul_left e (Nat.add_le_add_right (Nat.log_le_clog 2 n) 1))))
  have hinit : q (Nat.clog 2 n ^ β + Nat.log 2 (m + 2)) ≤ f (Nat.clog 2 n) :=
    (hq _).trans (Nat.mul_le_mul_left C
      (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_left hlog _) 1) d))
  refine ⟨hinit.trans (hI n), ?_⟩
  let P := greedyRowListLength (Nat.clog 2 n ^ β) m
  have hlogm : Nat.log 2 m + 1 ≤ Nat.clog 2 (2 * m + 4) := by
    apply Nat.succ_le_of_lt
    apply (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr
    have hp : 2 ^ Nat.log 2 m ≤ m + 1 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp
      · exact (Nat.pow_log_le_self 2 hm0.ne').trans (Nat.le_succ m)
    omega
  have hP : P ≤ 20000 * (Nat.clog 2 n ^ β) ^ 2 * Nat.clog 2 (2 * m + 4) ^ 2 := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlogm 2)
  have hquery := query_count_le_two_pow_succ_clog_pow hm
    (by simp : Nat.clog 2 n ^ β ≤ 1 * Nat.clog 2 n ^ β) hP
  have hcount : (3 * n + 1) * (candidateTupleCount m P + 1) ≤
      4 * (3 * n * (2 * m + 2) ^ P + 1) := by
    by_cases hn : n = 0
    · subst n
      have hm0 : m = 0 := by omega
      subst m
      cases P <;> simp [candidateTupleCount]
    · have hpow : 1 ≤ (2 * m + 2) ^ P := Nat.one_le_pow _ _ (by omega)
      have hc : candidateTupleCount m P ≤ (2 * m + 2) ^ P :=
        Nat.pow_le_pow_left (by omega) P
      have h1 := Nat.mul_le_mul_left (3 * n) hpow
      have h2 := Nat.mul_le_mul_right ((2 * m + 2) ^ P) (by omega : 1 ≤ 3 * n)
      nlinarith
  calc _ ≤ 4 * 2 ^ g (Nat.clog 2 n) := hcount.trans (Nat.mul_le_mul_left 4 hquery)
    _ ≤ 4 * 2 ^ (Nat.logLogSqrtLogScale n + J) :=
      Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by decide) (hJ n))
    _ = _ := by rw [pow_add]; ring

/-- One actual parity machine has sharp single-loglog time and polynomial space at every size.
Correctness is the density-restricted original-count theorem `countParity_eq_modelCountOn`;
outside that domain the resource bounds still hold, but no counting claim is made. -/
theorem exists_countParity_sharp_certificate (k β : ℕ) (hk : 1 ≤ k) :
    ∃ N₀ : ℕ, ∃ (cs : NativeCertificate (countParity k β N₀)
      (encPair encUnary encCNF) encNat) (A : ℕ), ∀ x : ℕ × CNF ℕ,
      let L := (encPair encUnary encCNF x).length
      cs.time x ≤ A * (L + 1) ^ A * 2 ^ (A * Nat.logLogSqrtLogScale x.1) ∧
      cs.space x ≤ A * (L + 1) ^ A := by
  obtain ⟨N₀, D, cs, poly, qInit, polySys, hpoly, hq, hsys, hc⟩ :=
    exists_countParity_certificate k β hk
  obtain ⟨I, J, hOver⟩ := overhead_bounds β hq
  let H := 4 * 2 ^ J
  let G := 2 ^ I
  let budget (L : ℕ) := D * (polySys L + 1) ^ D
  let p (L : ℕ) := 2 * (poly L + G + H * (poly L + budget L) + 1)
  have hp : Cslib.PolynomiallyBounded p := by dsimp only [p, budget]; fun_prop
  have hsum : Cslib.PolynomiallyBounded (fun L => p L + poly L) := by fun_prop
  obtain ⟨C, d, hCd⟩ := Cslib.polynomiallyBounded_iff_le.mp hsum
  let A := C + d + D + 2
  refine ⟨N₀, cs, A, fun x => ?_⟩
  let L := (encPair encUnary encCNF x).length
  let E := Nat.logLogSqrtLogScale x.1
  have he1 : 1 ≤ 2 ^ E := Nat.one_le_pow _ 2 (by decide)
  have heD : 1 ≤ 2 ^ (D * E) := Nat.one_le_pow _ 2 (by decide)
  have hprod : 2 ^ ((D + 1) * E) = 2 ^ E * 2 ^ (D * E) := by
    rw [Nat.add_mul, one_mul, pow_add, mul_comm]
  have heT : 1 ≤ 2 ^ ((D + 1) * E) := Nat.one_le_pow _ 2 (by decide)
  have he1T : 2 ^ E ≤ 2 ^ ((D + 1) * E) := by
    rw [hprod]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have ht : cs.time x ≤ p L * 2 ^ ((D + 1) * E) := by
    have ht := (hc x).2
    simp only [sparseCNFTimeBound, id_eq] at ht
    split_ifs at ht with hfast
    · have hm := (entersSparseFastPath_eq_true_iff.mp hfast).2.2.2.2
      obtain ⟨hi, hj⟩ := hOver x.1 x.2.length hm
      have hi' : 2 ^ qInit (Nat.clog 2 x.1 ^ β + Nat.log 2 (x.2.length + 2)) ≤
          G * 2 ^ E := by
        calc _ ≤ 2 ^ (E + I) := Nat.pow_le_pow_right (by decide) hi
          _ = _ := by rw [pow_add]; ring
      have hinner : poly L + budget L * 2 ^ (D * E) ≤
          (poly L + budget L) * 2 ^ (D * E) := by nlinarith
      have hcall :
          (3 * x.1 + 1) *
              (candidateTupleCount x.2.length (greedyRowListLength (Nat.clog 2 x.1 ^ β)
                x.2.length) + 1) * (poly L + budget L * 2 ^ (D * E)) ≤
            H * (poly L + budget L) * 2 ^ ((D + 1) * E) := by
        calc _ ≤ (H * 2 ^ E) * ((poly L + budget L) * 2 ^ (D * E)) :=
              Nat.mul_le_mul hj hinner
          _ = _ := by rw [hprod]; ring
      have hpolyT : poly L ≤ poly L * 2 ^ ((D + 1) * E) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have hinitT := hi'.trans (Nat.mul_le_mul_left G he1T)
      exact ht.trans (calc
        _ ≤ 2 * (poly L * 2 ^ ((D + 1) * E) + G * 2 ^ ((D + 1) * E) +
            H * (poly L + budget L) * 2 ^ ((D + 1) * E) + 2 ^ ((D + 1) * E)) :=
          Nat.mul_le_mul_left 2
            (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hpolyT hinitT) hcall) heT)
        _ = _ := by dsimp only [p]; ring)
    · change cs.time x ≤ 2 * (poly L + 1) at ht
      have hG := Nat.zero_le G
      have hH := Nat.zero_le (H * (poly L + budget L))
      exact ht.trans (calc
        _ ≤ 2 * (poly L + G + H * (poly L + budget L) + 1) := by omega
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega))
  have hA : D + 1 ≤ A := by dsimp only [A]; omega
  have hd : d ≤ A := by dsimp only [A]; omega
  have hC : C ≤ A := by dsimp only [A]; omega
  have hpoly : p L ≤ A * (L + 1) ^ A :=
    (Nat.le_add_right _ _).trans ((hCd L).trans
      (Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hd)))
  have hspace : poly L ≤ A * (L + 1) ^ A :=
    (Nat.le_add_left _ _).trans ((hCd L).trans
      (Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hd)))
  exact ⟨ht.trans (Nat.mul_le_mul hpoly
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right E hA))),
    (hc x).1.trans hspace⟩

/-- Real base-two source scale for the actual parity machine, with one iterated logarithm.
The certificate and constants are fixed before the declared size and formula. -/
theorem exists_countParity_real_sharp_certificate (k β : ℕ) (hk : 1 ≤ k) :
    ∃ N₀ : ℕ, ∃ (cs : NativeCertificate (countParity k β N₀)
      (encPair encUnary encCNF) encNat) (A : ℕ), ∀ n, 16 ≤ n → ∀ ψ : CNF ℕ,
      let L := (encPair encUnary encCNF (n, ψ)).length
      (cs.time (n, ψ) : ℝ) ≤ (A : ℝ) * (L + 1 : ℕ) ^ A *
        (2 : ℝ) ^ (((6 * A : ℕ) : ℝ) * Real.logLogSqrtLogScale n) ∧
      cs.space (n, ψ) ≤ A * (L + 1) ^ A := by
  obtain ⟨N₀, cs, A, h⟩ := exists_countParity_sharp_certificate k β hk
  refine ⟨N₀, cs, A, fun n hn ψ => ?_⟩
  obtain ⟨ht, hs⟩ := h (n, ψ)
  refine ⟨?_, hs⟩
  have htR : (cs.time (n, ψ) : ℝ) ≤ (A : ℝ) *
      ((encPair encUnary encCNF (n, ψ)).length + 1 : ℕ) ^ A *
      (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht
  exact htR.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Circuits.Frontier.IncidenceNetwork

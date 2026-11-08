/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceNetworkSize
public import Complexity.Foundations.Data.Nat.Radix
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeRadix
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Sqrt

/-!
# Executable indexing of incidence degree arrays

Read one array from its binary radix index, without materializing the array box. This implements
the `(K+1)^(J²)` traversal in [OpenAI2026ETH], Lemma D.2, PDF p. 55. Every array of length `J²`
with entries at most `K` has exactly one fitting index, including `K=0` and `J=0`.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.arrayCount`: binary count of fixed-width arrays.
* `Cslib.Circuits.Frontier.IncidenceNetwork.arrayAt`: decode one array from its binary index.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.arrayAt_coverage`: unique coverage of bounded arrays.
* `Cslib.Circuits.Frontier.IncidenceNetwork.arrayAt_polytime`: binary polynomial-time decoder.
* `Cslib.Circuits.Frontier.IncidenceNetwork.arrayCount_quarter_le`: source enumeration overhead.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp. 55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Turing.MultiTapeTM

/-- Number of fixed-width degree arrays; this is a binary loop count, not a list allocation. -/
@[expose] def arrayCount (K J : ℕ) : ℕ := (K + 1) ^ (J * J)

/-- Decode one little-endian degree array of the full declared length. -/
@[expose] def arrayAt (K J i : ℕ) : List ℕ :=
  (List.range (J * J)).map fun b => Cslib.Radix.digit (K + 1) i b

@[simp] theorem length_arrayAt (K J i : ℕ) : (arrayAt K J i).length = J * J := by
  simp [arrayAt]

/-- Every written entry lies in `[0,K]`, even for an out-of-range binary index. -/
theorem arrayAt_le (K J i : ℕ) : ∀ d ∈ arrayAt K J i, d ≤ K := by
  intro d hd
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
  rw [Cslib.Radix.digit_eq_div_pow_mod]
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))

private theorem ofDigits_arrayAt (K J i : ℕ) (hi : i < arrayCount K J) :
    Nat.ofDigits (K + 1) (arrayAt K J i) = i := by
  obtain ⟨x, hx, hxi⟩ := Nat.exists_ofDigits_ofFn hi
  have he : arrayAt K J i = List.ofFn x := by
    apply List.ext_getElem (by simp)
    intro b hb hb'
    simp only [arrayAt, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [← hxi]
    exact (Cslib.Radix.digit_ofDigits (by omega) (List.ofFn x)
      (by simpa using hx) b (by simpa using hb')).trans (List.getElem_ofFn hb')
  rw [he, hxi]

/-- Fitting indices cannot produce the same degree array. -/
theorem arrayAt_injective (K J : ℕ) :
    Function.Injective (fun i : Fin (arrayCount K J) => arrayAt K J i) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg (Nat.ofDigits (K + 1)) hij
  simpa only [ofDigits_arrayAt K J i i.isLt, ofDigits_arrayAt K J j j.isLt] using he

/-- Exact coverage without constructing the box: every bounded array has one fitting index. -/
theorem arrayAt_coverage (K J : ℕ) (d : List ℕ) (hlen : d.length = J * J)
    (hd : ∀ x ∈ d, x ≤ K) : ∃! i : Fin (arrayCount K J), arrayAt K J i = d := by
  have hv : Nat.ofDigits (K + 1) d < arrayCount K J := by
    simpa only [arrayCount, hlen] using
      Nat.ofDigits_lt_base_pow_length_of_pos (by omega : 0 < K + 1) d
        (fun x hx => Nat.lt_succ_of_le (hd x hx))
  let i : Fin (arrayCount K J) := ⟨Nat.ofDigits (K + 1) d, hv⟩
  have hi : arrayAt K J i = d := by
    apply List.ext_getElem (by simp [hlen])
    intro b hb hb'
    simp only [arrayAt, List.getElem_map, List.getElem_range]
    exact Cslib.Radix.digit_ofDigits (by omega) d (fun x hx => Nat.lt_succ_of_le (hd x hx)) b hb'
  exact ⟨i, hi, fun j hj => arrayAt_injective K J (hj.trans hi.symm)⟩

/-- A monomial described by its selected incidences in every group pair determines one array.
The total degree bound itself supplies every coordinate bound. -/
theorem selected_degrees_coverage (K J : ℕ) (parts : List (List (ℕ × ℕ)))
    (hlen : parts.length = J * J) (hdegree : (parts.map List.length).sum ≤ K) :
    ∃! i : Fin (arrayCount K J), arrayAt K J i = parts.map List.length := by
  apply arrayAt_coverage K J _ (by simpa using hlen)
  intro d hd
  exact (List.single_le_sum (by simp) d hd).trans hdegree

/-- The actual loop count is computed in binary in polynomial time from unary K and J. -/
@[fun_prop] theorem arrayCount_polytime :
    ComputableInPolyTime (fun p : ℕ × ℕ => arrayCount p.1 p.2)
      (encPair encUnary encUnary) encNat := by
  have hb : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + 1)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have he : ComputableInPolyTime (fun p : ℕ × ℕ => p.2 * p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_pow).comp
    ((ComputableInPolyTime.unary_to_binary.comp hb).prod he)

/-- Decode one actual array with binary index and unary cap/group count. Every digit operation,
position traversal and unary output write is charged; no array-sized advice is supplied. -/
@[fun_prop] theorem arrayAt_polytime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => arrayAt p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encNat) (encList encUnary) := by
  let enc := encPair (encPair encUnary encUnary) encNat
  have hK : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1) enc encUnary := by fun_prop
  have hJ : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2) enc encUnary := by fun_prop
  have hi : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2) enc encNat := by fun_prop
  have hd : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => Cslib.Radix.digit (p.1.1.1 + 1) p.1.2 p.2)
      (encPair enc encUnary) encUnary := by
    apply ComputableInPolyTime.binary_to_unary_bounded
      (bound := fun p => p.1.1.1)
    · exact ComputableInPolyTime.radix_digit.comp
        (((ComputableInPolyTime.unary_to_binary.comp (by fun_prop)).prod (by fun_prop)).prod
          (by fun_prop))
    · fun_prop
    · intro p
      rw [Cslib.Radix.digit_eq_div_pow_mod]
      exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  unfold arrayAt
  exact ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.unary_range' (ComputableInPolyTime.unary_mul' hJ hJ)) hd

/-- At quarter-root groups, the actual number of traversed arrays has the source overhead
`2^O(sqrt(n) log(n))`, with explicit integer constants and no square-log-log factor. -/
theorem arrayCount_quarter_le {K n c : ℕ} (hn : 1 ≤ n) (hK : K ≤ c * n) :
    arrayCount K (Nat.ceilQuarter n) ≤
      2 ^ (4 * n.sqrt * (Nat.clog 2 (c + 1) + Nat.clog 2 n)) := by
  set J := Nat.ceilQuarter n
  have hJ : 0 < J := Nat.ceilQuarter_pos hn
  have hsq : J * J ≤ 4 * n.sqrt := by
    rcases Nat.lt_or_ge J 2 with hsmall | hlarge
    · have he : J = 1 := by omega
      have hs : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa using hn)
      rw [he]
      omega
    · have hmin : ¬ n ≤ (J - 1) ^ 4 :=
        Nat.find_min (⟨n, Nat.le_self_pow (by norm_num) n⟩ : ∃ q, n ≤ q ^ 4)
          (show J - 1 < Nat.ceilQuarter n by omega)
      have hs : (J - 1) ^ 2 ≤ n.sqrt := Nat.le_sqrt.mpr (by nlinarith)
      have hj : J ≤ 2 * (J - 1) := by omega
      nlinarith
  have hb : K + 1 ≤ 2 ^ (Nat.clog 2 (c + 1) + Nat.clog 2 n) := by
    calc K + 1 ≤ (c + 1) * n := by nlinarith
      _ ≤ 2 ^ Nat.clog 2 (c + 1) * 2 ^ Nat.clog 2 n :=
        Nat.mul_le_mul (Nat.le_pow_clog Nat.one_lt_two _) (Nat.le_pow_clog Nat.one_lt_two _)
      _ = _ := (pow_add _ _ _).symm
  calc arrayCount K J ≤ (2 ^ (Nat.clog 2 (c + 1) + Nat.clog 2 n)) ^ (J * J) :=
        Nat.pow_le_pow_left hb _
    _ = 2 ^ ((J * J) * (Nat.clog 2 (c + 1) + Nat.clog 2 n)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hsq)

end Cslib.Circuits.Frontier.IncidenceNetwork

/-
Copyright (c) 2026 Carlos Toledo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlos Toledo
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount
public import Complexity.Computability.WordRAM.OfTuring.Space
import Complexity.Computability.Complexity.FineGrained.BruteForce
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# Subexponential `k`-SAT on the word RAM

`Cslib.Complexity.CountingNativeEndpoint.decidableInSubexpTime_KSAT` decides `k`-SAT on multi-tape
machines in time `2 ^ (δ * n)` times a polynomial, for every `δ > 0`. Its consequence `not_ETH`
passes through `Cslib.Complexity.DecidableInTimeO`, which forgets the work space of the decider.
Here the decider is rebuilt from the native model counter
`Cslib.Complexity.CountingNativeEndpoint.exists_modelCounter`, whose `ComputableInO` contract
keeps the polynomial work space, composed with the polynomial-time width check and the test
`0 < count`. Because the work space is polynomial,
`Cslib.WordRAM.uniformDecidableInTimeLogWord_of_decidableInTimeAndSpace` carries the decider to
one fixed word-RAM program at logarithmic word size, although its running time is not polynomially
bounded, so `Cslib.WordRAM.DTIME_subset_RAMTIME_additive` does not apply.

The word RAM reads the bits of `encCNF φ`, one bit per word, as in `Cslib.WordRAM.RAMTIME`. For
`k = 3`, `Cslib.WordRAM.uniformDecidableInTimeLogWord_KSAT` says that the exponential time
hypothesis `Cslib.Complexity.ETH`, read on the word RAM over `Basis.additive` with words of
`O(log L)` bits, fails as well.

## Main results

* `Cslib.Complexity.CountingNativeEndpoint.exists_decidableInTimeAndSpace_KSAT`: one multi-tape
  machine decides `k`-SAT within time `2 ^ (A * interpolationScale n)` times a polynomial and
  within polynomial work space.
* `Cslib.WordRAM.uniformDecidableInTimeLogWord_KSAT`: for every `δ > 0`, one fixed program over
  `Basis.additive` decides `k`-SAT within `c * (⌈2 ^ (δ * n)⌉ * (L + 1) ^ e) + c` instructions, at
  every word size above a logarithmic threshold in `L`.
-/

@[expose] public section

namespace Cslib.Complexity.CountingNativeEndpoint

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- **`k`-SAT with its work space.** One binary multi-tape machine decides `KSAT k` on
`encCNF φ` within time `c * (⌈2 ^ (A * interpolationScale n)⌉ * (L + 1) ^ E)` and work space
`c * (L + 1) ^ E`, where `n = φ.numVars` and `L = |encCNF φ|`. -/
theorem exists_decidableInTimeAndSpace_KSAT (k : ℕ) :
    ∃ (t s : CNF ℕ → ℕ) (A E c : ℕ), DecidableInTimeAndSpace (KSAT k) encCNF t s ∧
      (∀ φ, t φ ≤ c * (⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ *
        ((encCNF φ).length + 1) ^ E)) ∧
      (∀ φ, s φ ≤ c * ((encCNF φ).length + 1) ^ E) := by
  obtain ⟨count, A, e, b, hspec, hcount⟩ := exists_modelCounter k
  obtain ⟨c₀, -, hlen⟩ := id hcount
  obtain ⟨dw, _, hw⟩ := (computableInPolyTime_all_length_le k).exists_degree
  obtain ⟨dp, _, hp⟩ := computableInPolyTime_pos_nat.exists_degree
  obtain ⟨c, htm, -⟩ := hw.inO.ite (hp.inO.comp hcount) (ComputableInO.const false)
  set E := dw + e + b + b * dp + 1 with hE
  set F := 4 + (2 * c₀ + 1) ^ dp
  refine ⟨_, _, A, E, c * F, decidableInTimeAndSpace_iff.mpr ⟨_, htm, fun φ => ?_⟩,
    fun φ => ?_, fun φ => ?_⟩
  · -- correctness
    simp only [KSAT, Set.mem_ofPred_eq, Function.comp_apply]
    by_cases hwid : (φ.all fun c => decide (c.length ≤ k)) = true
    · have hwid' : ∀ c ∈ φ, c.length ≤ k := by simpa using hwid
      simp only [hwid, ↓reduceIte]
      rw [hspec φ hwid', decide_eq_true_iff, CNF.modelCount_pos_iff]
      exact ⟨fun h => h.2, fun h => ⟨hwid', h⟩⟩
    · simp only [hwid, Bool.false_eq_true, ↓reduceIte, iff_false, not_and]
      intro h
      exact absurd (by simpa using h) hwid
  all_goals
    have hl := hlen φ
    have hX : 1 ≤ ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ :=
      Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity)))
    beta_reduce at hl ⊢
    generalize ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ = X at hX ⊢
    generalize (encNat (count φ)).length = l at hl ⊢
    generalize (encCNF φ).length = L at hl ⊢
    have hY : 1 ≤ L + 1 := by omega
    have hYE : ∀ d ≤ E, (L + 1) ^ d ≤ (L + 1) ^ E := fun d hd => Nat.pow_le_pow_right hY hd
    have hYb : 1 ≤ (L + 1) ^ b := Nat.one_le_pow _ _ hY
    have hlen' : l + 1 ≤ (2 * c₀ + 1) * (L + 1) ^ b := by nlinarith
    have hpowp : (l + 1) ^ dp ≤ (2 * c₀ + 1) ^ dp * (L + 1) ^ E := by
      calc _ ≤ ((2 * c₀ + 1) * (L + 1) ^ b) ^ dp := Nat.pow_le_pow_left hlen' dp
        _ = (2 * c₀ + 1) ^ dp * (L + 1) ^ (b * dp) := by rw [mul_pow, ← pow_mul]
        _ ≤ _ := Nat.mul_le_mul_left _ (hYE _ (by omega))
    have hZ : (L + 1) ^ E ≤ X * (L + 1) ^ E := Nat.le_mul_of_pos_left _ hX
    have h1 : (L + 1) ^ dw ≤ (L + 1) ^ E := hYE _ (by omega)
    have h2 : (L + 1) ^ e ≤ (L + 1) ^ E := hYE _ (by omega)
    have h3 : (L + 1) ^ b ≤ (L + 1) ^ E := hYE _ (by omega)
    have h4 : L + 1 ≤ (L + 1) ^ E := Nat.le_self_pow (by omega) _
    have h5 : X * (L + 1) ^ e ≤ X * (L + 1) ^ E := Nat.mul_le_mul_left _ h2
    have h6 : (2 * c₀ + 1) ^ dp * (L + 1) ^ E ≤ (2 * c₀ + 1) ^ dp * (X * (L + 1) ^ E) :=
      Nat.mul_le_mul_left _ hZ
    have h7 : (4 + (2 * c₀ + 1) ^ dp) * (X * (L + 1) ^ E) =
        4 * (X * (L + 1) ^ E) + (2 * c₀ + 1) ^ dp * (X * (L + 1) ^ E) := by ring
    have h8 : (4 + (2 * c₀ + 1) ^ dp) * (L + 1) ^ E =
        4 * (L + 1) ^ E + (2 * c₀ + 1) ^ dp * (L + 1) ^ E := by ring
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left c ?_
    simp only [F]
    split <;> omega

end Cslib.Complexity.CountingNativeEndpoint

namespace Cslib.WordRAM

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

/-- **Subexponential `k`-SAT on the word RAM.** For every `δ > 0`, one fixed program over
`Basis.additive`, run on the bits of `encCNF φ`, decides `KSAT k` within
`c * (⌈2 ^ (δ * n)⌉ * (L + 1) ^ e) + c` instructions, where `n = φ.numVars` and
`L = |encCNF φ|`, at every word size `w ≥ logWidth k' L` for a constant `k' > 0`. -/
theorem uniformDecidableInTimeLogWord_KSAT (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c e : ℕ, UniformDecidableInTimeLogWord .additive (KSAT k)
      (fun _ φ => (encCNF φ).map Bool.toNat) (fun φ => (encCNF φ).length)
      (fun φ _ => c * (⌈(2 : ℝ) ^ (δ * φ.numVars)⌉₊ * ((encCNF φ).length + 1) ^ e) + c) := by
  obtain ⟨t, s, A, E, c, hd, ht, hs⟩ := CountingNativeEndpoint.exists_decidableInTimeAndSpace_KSAT k
  obtain ⟨C, k', hk', hU⟩ := uniformDecidableInTimeLogWord_of_decidableInTimeAndSpace hd hs
  obtain ⟨K, -, hK⟩ := SubexponentialSAT.exists_two_pow_mul_interpolationScale_le (A : ℝ) hδ
  refine ⟨C * c * ⌈K⌉₊ + C, E, k', hk', hU.mono (fun φ _ => ?_) (fun _ _ h => h)⟩
  set X := ⌈(2 : ℝ) ^ ((A : ℝ) * SubexponentialSAT.interpolationScale φ.numVars)⌉₊ with hXdef
  set Z := ⌈(2 : ℝ) ^ (δ * φ.numVars)⌉₊ with hZdef
  set Y := (encCNF φ).length + 1
  have hXZ : X ≤ ⌈K⌉₊ * Z := by
    rw [hXdef, Nat.ceil_le]
    push_cast
    refine (hK φ.numVars).trans ?_
    exact mul_le_mul (Nat.le_ceil K) (Nat.le_ceil _) (by positivity) (by positivity)
  have htφ : t φ ≤ c * (X * Y ^ E) := ht φ
  have h1 : C * t φ ≤ C * c * ⌈K⌉₊ * (Z * Y ^ E) := by
    calc C * t φ ≤ C * (c * (X * Y ^ E)) := Nat.mul_le_mul_left _ htφ
      _ ≤ C * (c * (⌈K⌉₊ * Z * Y ^ E)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hXZ))
      _ = C * c * ⌈K⌉₊ * (Z * Y ^ E) := by ring
  have h2 : C * c * ⌈K⌉₊ * (Z * Y ^ E) ≤ (C * c * ⌈K⌉₊ + C) * (Z * Y ^ E) :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  change C * t φ + C ≤ (C * c * ⌈K⌉₊ + C) * (Z * Y ^ E) + (C * c * ⌈K⌉₊ + C)
  omega

end Cslib.WordRAM

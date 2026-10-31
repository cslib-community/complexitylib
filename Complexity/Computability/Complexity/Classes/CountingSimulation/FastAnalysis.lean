/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.FastAlgorithm
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionSchedule

/-!
# The resource analysis of the native recursion: the recursion tree

The resource analysis `CountingSimulation.FastAnalysis` of the native recursion
(`FastContraction.nativeMk`) of Theorem D.1 of [OpenAI2026ETH] (Appendix D.4.7, p. 64), reduced to
two bounds about single calls (`CountingSimulation.fastAnalysis_nativeMk_of`):

* **sizes** (`CountingSimulation.FastSizes`): the calls reached from the root, their frames and
  their values are polynomially long in the input;
* **leaves** (`CountingSimulation.FastLeaves`): direct summation at a reached leaf takes time
  `poly(n) 2 ^ O(s / √⌊log₂ s⌋)` and polynomial space.

The rest of the analysis is proved here: the derivation of the root over the reached calls
(`FastContraction.reachInv`), with at most `m + 1` stack levels for every input
(`FastContraction.exists_eval_reachInv`), and, from some size on, with at most
`2 ^ ((245760 C' + 37) m / √⌊log₂ m⌋)` nodes for `C' = ⌊p / m⌋ + 1`
(`FastContraction.exists_eval_onSchedule`), which fit in the clock
(`CountingSimulation.two_mul_sub_one_le_fuel`). The clock's fixed constant serves every precision
because the call count's exponent is linear in `C'`.

## Main definitions

* `Cslib.Complexity.CountingSimulation.FastSizes`: polynomial sizes along the recursion.
* `Cslib.Complexity.CountingSimulation.FastLeaves`: the leaf bounds.

## Main results

* `Cslib.Complexity.CountingSimulation.two_mul_sub_one_le_fuel`: the call count fits in the clock.
* `Cslib.Complexity.CountingSimulation.onSchedule_root_capPrecision`: guarded roots are on the
  schedule.
* `Cslib.Complexity.CountingSimulation.fastAnalysis_nativeMk_of`: the resource analysis from the
  sizes and the leaf bounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53) and
  Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ContractionSchedule
  Cslib.Circuits.Frontier.FastContraction Cslib.GenericRAM Cslib.GenericRAM.StackRecursion
  Turing.MultiTapeTM

/-! ### The clock -/

/-- **The call count fits in the clock.** For a root with `m ≥ D + 2` edges and precision
`p ≤ D m`, a derivation with at most `2 ^ ((245760 C' + 37) m / √⌊log₂ m⌋)` nodes,
`C' = ⌊p / m⌋ + 1`, has `2 N - 1` at most the clock `2 ^ (K₀ (m + p) / √⌊log₂ (m + p)⌋)`: the
exponent is at most `245797 (m + p) / √⌊log₂ m⌋`, and `⌊log₂ (m + p)⌋ ≤ 3 ⌊log₂ m⌋`. -/
theorem two_mul_sub_one_le_fuel {m p N D : ℕ} (hm : D + 2 ≤ m) (hp : p ≤ D * m)
    (hN : N ≤ 2 ^ ((245760 * (p / m + 1) + 37) * m / Nat.sqrt (Nat.log 2 m))) :
    2 * N - 1 ≤ 2 ^ (fuelConst * (m + p) / Nat.sqrt (Nat.log 2 (m + p))) := by
  set L := Nat.log 2 m with hLdef
  set σ := Nat.sqrt L with hσdef
  set Y := m + p with hYdef
  have hm2 : 2 ≤ m := by omega
  have hσ : 1 ≤ σ := Nat.one_le_sqrt_log_two hm2
  -- The exponent of the count.
  have hCm : (p / m + 1) * m ≤ Y := by
    have := Nat.div_mul_le_self p m
    rw [add_mul, one_mul]
    omega
  have hX : (245760 * (p / m + 1) + 37) * m ≤ 245797 * Y := by nlinarith
  -- `⌊log₂ (m + p)⌋ ≤ 3 ⌊log₂ m⌋`.
  have hYm : Y ≤ m * m := by nlinarith
  have hL1 : 1 ≤ L := Nat.le_log_of_pow_le one_lt_two (by simpa using hm2)
  have hL' : Nat.log 2 Y ≤ 3 * L := by
    have h1 : m < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self one_lt_two m
    have h2 : Y < 2 ^ (2 * L + 2) :=
      calc Y ≤ m * m := hYm
        _ < 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_self_lt_mul_self h1
        _ = 2 ^ (2 * L + 2) := by rw [← pow_add]; ring_nf
    have := Nat.log_lt_of_lt_pow (by omega) h2
    omega
  have hσ' : Nat.sqrt (Nat.log 2 Y) ≤ 3 * σ := by
    have h1 : Nat.sqrt (Nat.log 2 Y) ≤ Nat.sqrt (3 * L) := Nat.sqrt_le_sqrt hL'
    have h2 : Nat.sqrt (3 * L) < 2 * σ + 2 := by
      rw [Nat.sqrt_lt']
      have := Nat.lt_succ_sqrt' L
      nlinarith
    omega
  have hσ'0 : 0 < Nat.sqrt (Nat.log 2 Y) :=
    Nat.sqrt_pos.mpr ((Nat.log_mono_right (show m ≤ Y by omega)).trans_lt' hL1)
  -- Comparing the exponents.
  set k := Y / σ with hkdef
  have hk : 1 ≤ k := by
    refine (Nat.le_div_iff_mul_le hσ).mpr ?_
    have h1 : σ ≤ L := Nat.sqrt_le_self L
    have h2 : L < m := Nat.log_lt_self 2 (by omega)
    omega
  have hE1 : (245760 * (p / m + 1) + 37) * m / σ ≤ 245797 * k + 245797 :=
    (Nat.div_le_div_right hX).trans (Nat.mul_div_le_mul_div_add _ _ _)
  have hE2 : 1398101 * k ≤ fuelConst * Y / Nat.sqrt (Nat.log 2 Y) := by
    have h1 : fuelConst * Y / (3 * σ) ≤ fuelConst * Y / Nat.sqrt (Nat.log 2 Y) :=
      Nat.div_le_div_left hσ' hσ'0
    have h2 : fuelConst * Y / (3 * σ) = fuelConst * Y / σ / 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm σ 3]
    have h3 : fuelConst * k ≤ fuelConst * Y / σ := by
      rw [Nat.le_div_iff_mul_le hσ, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self Y σ)
    have h4 : 1398101 * k ≤ fuelConst * k / 3 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      simp only [fuelConst]
      nlinarith
    omega
  have hpow : 2 * N ≤ 2 ^ (fuelConst * Y / Nat.sqrt (Nat.log 2 Y)) :=
    calc 2 * N ≤ 2 * 2 ^ ((245760 * (p / m + 1) + 37) * m / σ) := Nat.mul_le_mul_left 2 hN
      _ = 2 ^ ((245760 * (p / m + 1) + 37) * m / σ + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (fuelConst * Y / Nat.sqrt (Nat.log 2 Y)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The schedule's certificate for every constant up to `D + 1`, from some size on. -/
theorem exists_activeBounds_le (D : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → ∀ C ≤ D + 1, ∀ d M p, Active C s d M p → ActiveBounds C s d M p := by
  choose f hf using exists_activeBounds
  exact ⟨(Finset.range (D + 2)).sup f, fun s hs C hC d M p hA =>
    ((hf C) s ((Finset.le_sup (Finset.mem_range.mpr (by omega))).trans hs)).2 d M p hA⟩

/-! ### The root -/

/-- **Guarded roots are on the schedule**, for every constant `C ≥ 1` with precision at most
`C m`. -/
theorem onSchedule_root_capPrecision {P C : ℕ} {G : ℕ × ExplicitTensorNetwork ℕ} (hg : fastGuard G = true)
    (hC : 1 ≤ C) (hp : (ExplicitTensorNetwork.capPrecision (P, G)).1 ≤ C * G.2.numEdges) :
    OnSchedule C G.2.numEdges (root (ExplicitTensorNetwork.capPrecision (P, G))) := by
  have hdeg : G.2.maxDegree ≤ degreeBound G.2.numEdges := by
    simp only [fastGuard, decide_eq_true_eq] at hg
    exact hg.2.2
  rw [ExplicitTensorNetwork.maxDegree_le_iff] at hdeg
  refine FastContraction.onSchedule_root hC rfl rfl rfl (wf_root P hg) (fun v hv => ?_) rfl rfl hp
  simp only [root, ExplicitTensorNetwork.capPrecision, rootNet, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  exact hdeg w hw

/-- The number of edges of an explicit network is below the length of an encoded input. -/
theorem numEdges_lt_length_encInput (P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ) :
    G.2.numEdges < (FastContraction.encInput (P, G)).length := by
  simp only [FastContraction.encInput, length_encPair, ExplicitTensorNetwork.encExplicitNetwork,
    encOfEquiv, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  simp only [DescribedNetwork.equivProd, Equiv.coe_fn_mk, encUnary_apply, List.length_replicate]
  omega

/-! ### The analysis from the sizes and the leaves -/

/-- **Polynomial sizes along the recursion**: for all constants `C` and `D` there is `K` such that
on every guarded input admissible at size `s ≥ 2` with constant `C` and with precision
`1 ≤ P ≤ D s`, every call reached from the root, its frames and its value are at most
`K (n + 1) ^ K` long, for the input length `n`. -/
@[expose] def FastSizes : Prop :=
  ∀ C D : ℕ, ∃ K : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true →
    ∀ x, Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x →
      (encCall x).length ≤ K * ((FastContraction.encInput (P, G)).length + 1) ^ K ∧
      (∀ a, (reachInv nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G)))).frame x a →
        (encPair encCall encFrame (x, a)).length ≤
          K * ((FastContraction.encInput (P, G)).length + 1) ^ K) ∧
      (encValue (x.depth, value nativeMk x)).length ≤
        K * ((FastContraction.encInput (P, G)).length + 1) ^ K

/-- **The leaf bounds**: for all constants `C` and `D` there is `K` such that on every guarded
input admissible at size `s ≥ 2` with constant `C` and with precision `1 ≤ P ≤ D s`, direct
summation at every reached call that the machine treats as a leaf takes time at most
`K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space at most `K (n + 1) ^ K`. -/
@[expose] def FastLeaves : Prop :=
  ∀ C D : ℕ, ∃ K : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true →
    ∀ x, Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x → active x = false →
      (leafCertificate nativeMk).time x ≤
          K * ((FastContraction.encInput (P, G)).length + 1) ^ K *
            2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        (leafCertificate nativeMk).space x ≤
          K * ((FastContraction.encInput (P, G)).length + 1) ^ K

/-- `a B ^ a ≤ a B ^ K` for `1 ≤ B` and `a ≤ K`. -/
private theorem mul_pow_le_mul_pow {a B K : ℕ} (hB : 1 ≤ B) (ha : a ≤ K) :
    a * B ^ a ≤ a * B ^ K :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB ha)

/-- **The resource analysis of the native recursion**, from polynomial sizes along the recursion
and the leaf bounds. The derivation of the root over the reached calls has at most `m + 1` stack
levels, and, from some size on, its nodes fit in the clock. -/
theorem fastAnalysis_nativeMk_of (hS : FastSizes) (hL : FastLeaves) : FastAnalysis nativeMk := by
  intro C D
  obtain ⟨KS, hKS⟩ := hS C D
  obtain ⟨KL, hKL⟩ := hL C D
  obtain ⟨sA, hsA⟩ := exists_activeBounds_le D
  refine ⟨KS + KL + 1, max sA (D + 2), fun s P G hs hP hPD hA hg => ?_⟩
  set q := ExplicitTensorNetwork.capPrecision (P, G) with hq
  set x₀ := root q with hx₀
  set m := G.2.numEdges with hm
  set n := (FastContraction.encInput (P, G)).length with hn
  have hsm : s ≤ m := hA.2.2.2.2.2
  have hmn : m < n := numEdges_lt_length_encInput P G
  have hp₀ : q.1 ≤ D * m :=
    (min_le_right _ _).trans (hPD.trans (Nat.mul_le_mul_left _ hsm))
  -- The derivation.
  obtain ⟨N, H, he, hN, hH⟩ : ∃ N H, (scheme nativeMk).Eval (reachInv nativeMk x₀) x₀
      (0, value nativeMk x₀) N H ∧ (max sA (D + 2) ≤ s → 2 * N - 1 ≤ fuel q) ∧ H ≤ m + 1 := by
    by_cases hs₀ : max sA (D + 2) ≤ s
    · have hm2 : D + 2 ≤ m := by omega
      have hC1 : q.1 / m + 1 ≤ D + 1 := by
        have := Nat.div_le_div_right (c := m) hp₀
        rw [Nat.mul_div_cancel _ (by omega)] at this
        omega
      have hB := hsA m (by omega) (q.1 / m + 1) hC1
      have hpC : q.1 ≤ (q.1 / m + 1) * m := (Nat.lt_div_mul_add (a := q.1) (b := m) (by omega)).le.trans
        (by rw [add_mul, one_mul])
      obtain ⟨N, H, he, hN, hH⟩ := exists_eval_onSchedule hB
        (onSchedule_root_capPrecision hg (Nat.le_add_left 1 _) hpC) rfl (by omega)
      refine ⟨N, H, he, fun _ => ?_, hH.trans ((Nat.log_lt_self 2 (by omega)).le.trans
        (Nat.le_succ _))⟩
      exact two_mul_sub_one_le_fuel hm2 hp₀ hN
    · obtain ⟨N, H, he, hH⟩ := exists_eval_reachInv (mk := nativeMk) (x₀ := x₀) rfl
      exact ⟨N, H, he, fun h => absurd h hs₀, hH⟩
  -- The bounds.
  obtain hKS' := hKS s P G hs hP hPD hA hg
  obtain hKL' := hKL s P G hs hP hPD hA hg
  set K := KS + KL + 1
  have hB1 : 1 ≤ n + 1 := by omega
  refine ⟨reachInv nativeMk x₀, N, H, KS * (n + 1) ^ KS, KL * (n + 1) ^ KL * 2 ^ (KL * s /
    Nat.sqrt (Nat.log 2 s)), KL * (n + 1) ^ KL, he, hN, fun x hx => ⟨(hKS' x hx).1, fun hl => ?_⟩,
    fun x a ha => (hKS' x ha.1).2.1 a ha, fun v ⟨x, hx, hv⟩ => hv ▸ (hKS' x hx).2.2, ?_, ?_⟩
  · have hl' : active x = false := by simpa [scheme] using hl
    exact hKL' x hx hl'
  · have h1 : H ≤ 1 * (n + 1) ^ K := by
      have : n + 1 ≤ (n + 1) ^ K := Nat.le_self_pow (by omega) _
      omega
    have h2 := mul_pow_le_mul_pow (a := KS) hB1 (show KS ≤ K by omega)
    have h3 := mul_pow_le_mul_pow (a := KL) hB1 (show KL ≤ K by omega)
    calc H + KS * (n + 1) ^ KS + KL * (n + 1) ^ KL
        ≤ 1 * (n + 1) ^ K + KS * (n + 1) ^ K + KL * (n + 1) ^ K := by omega
      _ = K * (n + 1) ^ K := by ring
  · refine Nat.mul_le_mul (mul_pow_le_mul_pow' hB1 (show KL ≤ K by omega))
      (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.mul_le_mul_right _
        (by omega))))
where
  /-- `a B ^ a ≤ K B ^ K` for `1 ≤ B` and `a ≤ K`. -/
  mul_pow_le_mul_pow' {a B K : ℕ} (hB : 1 ≤ B) (ha : a ≤ K) : a * B ^ a ≤ K * B ^ K :=
    Nat.mul_le_mul ha (Nat.pow_le_pow_right hB ha)

end Cslib.Complexity.CountingSimulation

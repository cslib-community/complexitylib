/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.FastAlgorithm
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionSchedule
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionSize
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# The resource analysis of the native recursion: the recursion tree and the sizes

The resource analysis `CountingSimulation.FastAnalysis` of the native recursion
(`FastContraction.nativeMk`) of Theorem D.1 of [OpenAI2026ETH] (Appendix D.4.7, p. 64), reduced to
the leaf bounds (`CountingSimulation.fastAnalysis_nativeMk`): direct summation at a reached leaf
takes time `poly(n) 2 ^ O(s / √⌊log₂ s⌋)` and polynomial space (`CountingSimulation.FastLeaves`).

The rest of the analysis is proved here:

* **the derivation** of the root over the reached calls (`FastContraction.reachInv`), with at most
  `m + 1` stack levels for every input (`FastContraction.exists_eval_reachInv`), and, from some size
  on, with at most `2 ^ ((245760 C' + 37) m / √⌊log₂ m⌋)` nodes for `C' = ⌊p / m⌋ + 1`
  (`FastContraction.exists_eval_onSchedule`), which fit in the clock
  (`CountingSimulation.two_mul_sub_one_le_fuel`). The clock's fixed constant serves every precision
  because the call count's exponent is linear in `C'`;
* **the sizes** (`CountingSimulation.fastSizes`): the reached calls, their frames and their values
  are at most `2 ^ 55 (n + 1) ^ 24` long, from the structural shapes of the calls
  (`FastContraction.Reach.shape`) and the encoded lengths of `FastContraction.Shape.length_le`.

`CountingSimulation.reach_facts` collects what the leaf bounds may use about a reached call: its
scale `m` with `s ≤ m ≤ C s`, at most `2 m` edges, and, from some size on, precision at most `m ^ 4`
and at most `leafSize m` edges at a leaf.

## Main definitions

* `Cslib.Complexity.CountingSimulation.FastSizes`: polynomial sizes along the recursion.
* `Cslib.Complexity.CountingSimulation.FastLeaves`: the leaf bounds, the remaining obligation.

## Main results

* `Cslib.Complexity.CountingSimulation.two_mul_sub_one_le_fuel`: the call count fits in the clock.
* `Cslib.Complexity.CountingSimulation.onSchedule_root_capPrecision`: guarded roots are on the
  schedule.
* `Cslib.Complexity.CountingSimulation.fastAnalysis_nativeMk_of`: the resource analysis from the
  sizes and the leaf bounds.
* `Cslib.Complexity.CountingSimulation.fastSizes`: the sizes.
* `Cslib.Complexity.CountingSimulation.fastAnalysis_nativeMk`: the resource analysis from the leaf
  bounds.
* `Cslib.Complexity.CountingSimulation.reach_facts`: the facts at the reached calls that the leaf
  bounds use.

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
theorem onSchedule_root_capPrecision {P C : ℕ} {G : ℕ × ExplicitTensorNetwork ℕ}
    (hg : fastGuard G = true) (hC : 1 ≤ C)
    (hp : (ExplicitTensorNetwork.capPrecision (P, G)).1 ≤ C * G.2.numEdges) :
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

/-- **Polynomial sizes along the recursion**: for all constants `C` and `D` there are `c` and `d`
such that on every guarded input admissible at size `s ≥ 2` with constant `C` and with precision
`1 ≤ P ≤ D s`, every call reached from the root, its frames and its value are at most
`c (n + 1) ^ d` long, for the input length `n`. -/
@[expose] def FastSizes : Prop :=
  ∀ C D : ℕ, ∃ c d : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true →
    ∀ x, Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x →
      (encCall (encList encNat) x).length ≤ c * ((FastContraction.encInput (P, G)).length + 1) ^ d ∧
      (∀ a, (reachInv tableEntry nativeMk
          (root (ExplicitTensorNetwork.capPrecision (P, G)))).frame x a →
        (encPair (encCall (encList encNat)) encFrame (x, a)).length ≤
          c * ((FastContraction.encInput (P, G)).length + 1) ^ d) ∧
      (encValue (x.depth, value tableEntry nativeMk x)).length ≤
        c * ((FastContraction.encInput (P, G)).length + 1) ^ d

/-- **The leaf bounds**: for all constants `C` and `D` there is `K` such that on every guarded
input admissible at size `s ≥ 2` with constant `C` and with precision `1 ≤ P ≤ D s`, direct
summation at every reached call that the machine treats as a leaf takes time at most
`K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space at most `K (n + 1) ^ K`. -/
@[expose] def FastLeaves : Prop :=
  ∀ C D : ℕ, ∃ K : ℕ, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true →
    ∀ x, Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x → active x = false →
      (leafCertificate tableEntryCertificate nativeMk).time x ≤
          K * ((FastContraction.encInput (P, G)).length + 1) ^ K *
            2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        (leafCertificate tableEntryCertificate nativeMk).space x ≤
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
  obtain ⟨cS, dS, hKS⟩ := hS C D
  obtain ⟨KL, hKL⟩ := hL C D
  obtain ⟨sA, hsA⟩ := exists_activeBounds_le D
  refine ⟨cS + dS + KL + 1, max sA (D + 2), fun s P G hs hP hPD hA hg => ?_⟩
  set q := ExplicitTensorNetwork.capPrecision (P, G) with hq
  set x₀ := root q with hx₀
  set m := G.2.numEdges with hm
  set n := (FastContraction.encInput (P, G)).length with hn
  have hsm : s ≤ m := hA.2.2.2.2.2
  have hmn : m < n := numEdges_lt_length_encInput P G
  have hp₀ : q.1 ≤ D * m :=
    (min_le_right _ _).trans (hPD.trans (Nat.mul_le_mul_left _ hsm))
  -- The derivation.
  obtain ⟨N, H, he, hN, hH⟩ : ∃ N H, (scheme tableEntry nativeMk).Eval
      (reachInv tableEntry nativeMk x₀) x₀ (0, value tableEntry nativeMk x₀) N H ∧
        (max sA (D + 2) ≤ s → 2 * N - 1 ≤ fuel q) ∧ H ≤ m + 1 := by
    by_cases hs₀ : max sA (D + 2) ≤ s
    · have hm2 : D + 2 ≤ m := by omega
      have hC1 : q.1 / m + 1 ≤ D + 1 := by
        have := Nat.div_le_div_right (c := m) hp₀
        rw [Nat.mul_div_cancel _ (by omega)] at this
        omega
      have hB := hsA m (by omega) (q.1 / m + 1) hC1
      have hpC : q.1 ≤ (q.1 / m + 1) * m :=
        (Nat.lt_div_mul_add (a := q.1) (b := m) (by omega)).le.trans (by rw [add_mul, one_mul])
      obtain ⟨N, H, he, hN, hH⟩ := exists_eval_onSchedule tableEntry hB
        (onSchedule_root_capPrecision hg (Nat.le_add_left 1 _) hpC) rfl (by omega)
      refine ⟨N, H, he, fun _ => ?_, hH.trans ((Nat.log_lt_self 2 (by omega)).le.trans
        (Nat.le_succ _))⟩
      exact two_mul_sub_one_le_fuel hm2 hp₀ hN
    · obtain ⟨N, H, he, hH⟩ := exists_eval_reachInv (mk := nativeMk) (x₀ := x₀) rfl
      exact ⟨N, H, he, fun h => absurd h hs₀, hH⟩
  -- The bounds.
  obtain hKS' := hKS s P G hs hP hPD hA hg
  obtain hKL' := hKL s P G hs hP hPD hA hg
  set K := cS + dS + KL + 1
  have hB1 : 1 ≤ n + 1 := by omega
  refine ⟨reachInv tableEntry nativeMk x₀, N, H, cS * (n + 1) ^ dS,
    KL * (n + 1) ^ KL * 2 ^ (KL * s / Nat.sqrt (Nat.log 2 s)), KL * (n + 1) ^ KL, he, hN,
    fun x hx => ⟨(hKS' x hx).1, fun hl => ?_⟩,
    fun x a ha => (hKS' x ha.1).2.1 a ha, fun v ⟨x, hx, hv⟩ => hv ▸ (hKS' x hx).2.2, ?_, ?_⟩
  · have hl' : active x = false := by simpa [scheme] using hl
    exact hKL' x hx hl'
  · have h1 : H ≤ 1 * (n + 1) ^ K := by
      have : n + 1 ≤ (n + 1) ^ K := Nat.le_self_pow (by omega) _
      omega
    have h2 : cS * (n + 1) ^ dS ≤ cS * (n + 1) ^ K :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 (by omega))
    have h3 := mul_pow_le_mul_pow (a := KL) hB1 (show KL ≤ K by omega)
    calc H + cS * (n + 1) ^ dS + KL * (n + 1) ^ KL
        ≤ 1 * (n + 1) ^ K + cS * (n + 1) ^ K + KL * (n + 1) ^ K := by omega
      _ ≤ K * (n + 1) ^ K := by
          rw [← add_mul, ← add_mul]
          exact Nat.mul_le_mul_right _ (by omega)
  · refine Nat.mul_le_mul (mul_pow_le_mul_pow' hB1 (show KL ≤ K by omega))
      (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.mul_le_mul_right _
        (by omega))))
where
  /-- `a B ^ a ≤ K B ^ K` for `1 ≤ B` and `a ≤ K`. -/
  mul_pow_le_mul_pow' {a B K : ℕ} (hB : 1 ≤ B) (ha : a ≤ K) : a * B ^ a ≤ K * B ^ K :=
    Nat.mul_le_mul ha (Nat.pow_le_pow_right hB ha)

/-! ### The sizes -/

/-- The modulus has at most `32 (m + 1) ^ 2` coefficients. -/
theorem length_modulus_le (m : ℕ) : (modulus m).length ≤ 32 * (m + 1) ^ 2 := by
  rw [length_modulus]
  set t := modulusExp m
  have h1 : 2 ^ t ≤ 4 * Nat.log 2 m + 2 := Nat.pow_log_le_self 2 (by omega)
  have h2 : Nat.log 2 m ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · exact (Nat.log_lt_self 2 h.ne').le
  have h3 : 3 ^ t ≤ (2 ^ t) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) t
  have h4 : (2 ^ t) ^ 2 ≤ (4 * (m + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

/-- The coefficients of the modulus are `0` or `1`. -/
theorem le_one_of_mem_modulus {m z : ℕ} (hz : z ∈ modulus m) : z ≤ 1 := by
  simp only [modulus, List.mem_map, List.mem_range] at hz
  obtain ⟨i, -, rfl⟩ := hz
  split_ifs <;> omega

/-- The encoded network is at most the encoded input long. -/
theorem length_encExplicitNetwork_le (P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ) :
    (ExplicitTensorNetwork.encExplicitNetwork G.2).length ≤
      (FastContraction.encInput (P, G)).length := by
  simp only [FastContraction.encInput, length_encPair]
  omega

/-- The vertices of an explicit network, encoded, are at most the encoded network long. -/
theorem length_vertices_le (G : ExplicitTensorNetwork ℕ) :
    G.vertices.length ≤ (ExplicitTensorNetwork.encExplicitNetwork G).length ∧
      ∀ v ∈ G.vertices, (encList encNat v.2).length + 1 ≤
        (ExplicitTensorNetwork.encExplicitNetwork G).length := by
  have hl : (ExplicitTensorNetwork.encExplicitNetwork G).length = 2 * G.numEdges + 1 +
      (G.vertices.map fun v =>
        2 * (encPair (encList encNat) (encList encNat) v).length + 1).sum := by
    simp only [ExplicitTensorNetwork.encExplicitNetwork, encOfEquiv, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, DescribedNetwork.equivProd, Equiv.coe_fn_mk, length_encPair,
      encUnary_apply, List.length_replicate, length_encList]
  refine ⟨?_, fun v hv => ?_⟩
  · have := List.length_le_sum_of_one_le (G.vertices.map fun v =>
      2 * (encPair (encList encNat) (encList encNat) v).length + 1) (fun i hi => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp hi
        omega)
    rw [List.length_map] at this
    omega
  · have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun v =>
      2 * (encPair (encList encNat) (encList encNat) v).length + 1) hv)
    have h2 := length_encPair (enc₁ := encList encNat) (enc₂ := encList encNat) v
    omega

/-- **Polynomial sizes along the recursion**: every call reached from the root of a guarded input,
its frames and its tagged value are at most `2 ^ 55 (n + 1) ^ 24` long. -/
theorem fastSizes : FastSizes := by
  intro C D
  refine ⟨2 ^ 55, 24, fun s P G _ _ _ _ hg x hx => ?_⟩
  set q := ExplicitTensorNetwork.capPrecision (P, G) with hq
  set x₀ := root q with hx₀
  set m := G.2.numEdges with hm
  set n := (FastContraction.encInput (P, G)).length with hn
  set Y := n + 1 with hY
  have hmn : m < n := numEdges_lt_length_encInput P G
  have hnet := length_encExplicitNetwork_le P G
  obtain ⟨hV, hdesc⟩ := length_vertices_le G.2
  have hp₀ : x₀.prec ≤ n := (min_le_left _ _).trans hnet
  have hrows : (encNat x₀.rows).length ≤ n := by
    change (encNat G.1).length ≤ n
    simp only [hn, FastContraction.encInput, length_encPair]
    omega
  have hV₀ : x₀.net.vertices.length ≤ n := by
    change (List.map _ G.2.vertices).length ≤ n
    rw [List.length_map]; omega
  have hsh := Reach.shape (x₀ := x₀) rfl rfl (wf_root P hg) hx
  set Z := 2 ^ 14 * Y ^ 8 with hZ
  have hY1 : 1 ≤ Y := by omega
  have hmY : m + 1 ≤ Y := by omega
  have hY3 : Y ≤ Y ^ 3 := Nat.le_self_pow (by norm_num) _
  have hY8 : Y ^ 3 ≤ Y ^ 8 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hm2 : m ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm5 : (m + 1) ^ 5 ≤ Y ^ 5 := Nat.pow_le_pow_left hmY 5
  have hPm : x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1 ≤ 41 * Y ^ 3 := by
    change x₀.prec + (m + 1) * (40 * m ^ 2) + 1 ≤ 41 * Y ^ 3
    have : (m + 1) * (40 * m ^ 2) ≤ Y * (40 * Y ^ 2) := Nat.mul_le_mul hmY (by omega)
    have : Y * (40 * Y ^ 2) = 40 * Y ^ 3 := by ring
    omega
  have hZ1 : 256 * (x₀.edges + 1) ^ 5 * (x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1) +
      x₀.fl.length ≤ Z := by
    have h1 : 256 * (x₀.edges + 1) ^ 5 * (x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1) ≤
        256 * Y ^ 5 * (41 * Y ^ 3) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm5) hPm
    have h2 : 256 * Y ^ 5 * (41 * Y ^ 3) = 10496 * Y ^ 8 := by ring
    have h3 : x₀.fl.length ≤ 32 * Y ^ 8 := (length_modulus_le m).trans
      (by have := Nat.pow_le_pow_left hmY 2; omega)
    omega
  have hZ2 : x₀.net.vertices.length + (x₀.edges + 1) * x₀.edges ^ 2 + (encNat x₀.rows).length ≤
      Z := by
    have : (x₀.edges + 1) * x₀.edges ^ 2 ≤ Y * Y ^ 2 := Nat.mul_le_mul hmY hm2
    have : Y * Y ^ 2 = Y ^ 3 := by ring
    omega
  have hR₀ : ∀ w ∈ x₀.net.vertices,
      (VertexDesc.enc (encList encNat) w.2).length ≤ 200 * (Z + 1) ^ 2 := by
    intro w hw
    change w ∈ List.map _ G.2.vertices at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rw [length_encSum]
    simp only [Sum.elim_inl]
    have := hdesc v hv
    have : Z ≤ (Z + 1) ^ 2 := (Nat.le_succ Z).trans (Nat.le_self_pow (by norm_num) _)
    omega
  obtain ⟨hc, hv, hf⟩ := hsh.length_le tableEntry rfl rfl rfl hZ1 hZ2
    (fun z hz => le_one_of_mem_modulus hz) hR₀
  -- `1000 (Z + 1) ^ 3 ≤ 2 ^ 55 (n + 1) ^ 24`.
  have hfin : 1000 * (Z + 1) ^ 3 ≤ 2 ^ 55 * Y ^ 24 := by
    have h1 : Z + 1 ≤ 2 ^ 15 * Y ^ 8 := by
      have : 1 ≤ Y ^ 8 := Nat.one_le_pow _ _ hY1
      omega
    have h2 : (Z + 1) ^ 3 ≤ (2 ^ 15 * Y ^ 8) ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : (2 ^ 15 * Y ^ 8) ^ 3 = 2 ^ 45 * Y ^ 24 := by ring
    rw [h3] at h2
    have h4 : 1000 * (2 ^ 45 * Y ^ 24) ≤ 2 ^ 55 * Y ^ 24 := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by norm_num)
    exact (Nat.mul_le_mul_left 1000 h2).trans h4
  refine ⟨hc.trans hfin, fun a ⟨_, ha, c, _, hac⟩ => ?_, hv.trans hfin⟩
  rw [hac]
  exact (hf ha _ c).trans hfin

/-- **The resource analysis of the native recursion**, given the leaf bounds. -/
theorem fastAnalysis_nativeMk (hL : FastLeaves) : FastAnalysis nativeMk :=
  fastAnalysis_nativeMk_of fastSizes hL

/-! ### Facts at the leaves -/

/-- `D m + 40 m ^ 2 (m + 1) ≤ m ^ 4` from `m = D + 81` on. -/
private theorem prec_arith {m D : ℕ} (hm : D + 81 ≤ m) :
    D * m + (m + 1) * (40 * m ^ 2) ≤ m ^ 4 := by
  have h1 : D * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
  have h2 : 81 * m ^ 3 ≤ m ^ 4 := by
    rw [pow_succ m 3, mul_comm (m ^ 3) m]
    exact Nat.mul_le_mul_right _ (by omega)
  have h3 : m * m ≤ m ^ 3 := by nlinarith
  have h4 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e : (m + 1) * (40 * m ^ 2) = 40 * m ^ 3 + 40 * m ^ 2 := by ring
  have h5 : m * m = m ^ 2 := by ring
  omega

/-- **The facts at the reached calls that the leaf bounds use.** For all constants `C` and `D` there
is `s₀` such that on every guarded input admissible at size `s ≥ 2` with constant `C` and with
precision `1 ≤ P ≤ D s`, every call reached from the root has scale `m` with `s ≤ m ≤ C s`, at most
`2 m` edges, and, from `s₀` on, precision at most `m ^ 4`, and at most `leafSize m` edges if the
machine treats it as a leaf. -/
theorem reach_facts (C D : ℕ) : ∃ s₀, ∀ (s P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ), 2 ≤ s →
    1 ≤ P → P ≤ D * s → ExplicitAdmissible C s G → fastGuard G = true →
    ∀ x, Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x →
      s ≤ x.scale ∧ x.scale ≤ C * s ∧ x.edges ≤ 2 * x.scale ∧
        (s₀ ≤ s → x.prec ≤ x.scale ^ 4 ∧ (active x = false → x.edges ≤ leafSize x.scale)) := by
  obtain ⟨sA, hsA⟩ := exists_activeBounds_le D
  refine ⟨max sA (D + 81), fun s P G hs hP hPD hA hg x hx => ?_⟩
  set q := ExplicitTensorNetwork.capPrecision (P, G) with hq
  set m := G.2.numEdges with hm
  have hsm : s ≤ m := hA.2.2.2.2.2
  have hmC : m ≤ C * s := hA.2.1
  have hp₀ : q.1 ≤ D * m :=
    (min_le_right _ _).trans (hPD.trans (Nat.mul_le_mul_left _ hsm))
  have hsh := Reach.shape (x₀ := root q) rfl rfl (wf_root P hg) hx
  have hsc : x.scale = m := hsh.scale_eq
  refine ⟨hsc ▸ hsm, hsc ▸ hmC, hsc ▸ hsh.edges_le, fun hs₀ => ⟨?_, fun hl => ?_⟩⟩
  · have hbd := hsh.bound_add_depth_le
    change x.bound + x.depth ≤ (m + 1) + 0 at hbd
    have hprec : x.prec ≤ q.1 + x.depth * (40 * m ^ 2) := hsh.prec_le
    have : x.depth * (40 * m ^ 2) ≤ (m + 1) * (40 * m ^ 2) := Nat.mul_le_mul_right _ (by omega)
    have := prec_arith (m := m) (D := D) (by omega)
    rw [hsc]
    omega
  · have hm2 : D + 2 ≤ m := by omega
    have hC1 : q.1 / m + 1 ≤ D + 1 := by
      have := Nat.div_le_div_right (c := m) hp₀
      rw [Nat.mul_div_cancel _ (by omega)] at this
      omega
    have hB := hsA m (by omega) (q.1 / m + 1) hC1
    have hpC : q.1 ≤ (q.1 / m + 1) * m :=
      (Nat.lt_div_mul_add (a := q.1) (b := m) (by omega)).le.trans (by rw [add_mul, one_mul])
    have h := hx.onSchedule hB (onSchedule_root_capPrecision hg (Nat.le_add_left 1 _) hpC)
    rw [hsc]
    exact h.edges_le_leafSize hB hl

end Cslib.Complexity.CountingSimulation

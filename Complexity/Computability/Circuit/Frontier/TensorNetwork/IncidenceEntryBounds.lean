/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.BooleanAnalysis.IncidenceBranching
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryCertificate
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceNetworkSize
public import Complexity.Computability.Complexity.Classes.CountingSimulation.TruncatedEntry
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Foundations.Data.Nat.Asymptotics
import Mathlib.Data.List.GetD
import Complexity.Foundations.Data.List.Blocks

/-!
# The incidence entry procedure meets the sharp contraction bound

Discharge the actual entry-resource hypotheses for the networks of [OpenAI2026ETH], Lemma D.2,
PDF pp. 54–56. At size `s = n ceil(log₂ ceil(log₂ n))`, the exponential part of the existing
streaming row evaluator is at most `2 ^ ceil(s ^ (9/10))`; its workspace is polynomial in the
encoded network length. Together with the existing shape bounds this instantiates the proved
truncated contraction algorithm. No contraction oracle or supplied entry budget is assumed.

This is a core resource link toward the single-log-log counting exponent imported in
[ChenJiangZhu2027], Lemma 3.2 (p. 11) and Proposition 4.2 (p. 14). It does not yet assemble all
high-incidence branches, degree arrays, parity queries or the final general-density counter.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_entry_admissible`: the actual evaluator is
  admissible on every constructed network of a sufficiently large bounded-incidence system.
* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_contraction_bound`: actual truncated network
  contraction takes time `poly(L) 2 ^ O(s / sqrt(log₂ s))` and polynomial space.
* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_sparseBranch_contraction_bound`: derive the
  source degree cap from an actual sparse branch.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp. 54–56.
* [ChenJiangZhu2027], Lemma 3.2 (p. 11) and Proposition 4.2 (p. 14).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.Complexity Cslib.GenericRAM Turing.MultiTapeTM

/-- The number of descriptor incidences of a row is the number of incidences in its test group. -/
theorem descInc_rowVertex {J : ℕ} (hJ : 0 < J) (P ℓ : ℕ)
    (sys : List (List (List ℕ))) (d : List ℕ) (g : ℕ) :
    descInc (rowVertex P ℓ J sys d g).2 =
      ((List.residueClass J sys.length g).map fun i =>
        (equationVars (sys.getD i [])).length).sum := by
  simp only [rowVertex, descInc, rowInc, rowBlocks, List.map_map, Function.comp_def,
    List.sum_map_range_eq_sum_range]
  exact sum_length_pairInc_row hJ g

/-- The exponential part of an entry evaluation is bounded by the incidences of one test group,
including on dead arrays and padding vertices. -/
theorem descInc_le {P ℓ J K s n : ℕ} {sys : List (List (List ℕ))} {d : List ℕ}
    (hJ : 0 < J) {S : ℕ} (hS : ∀ eq ∈ sys, (equationVars eq).length ≤ S) :
    ∀ v ∈ (network P ℓ J K s n sys d).2.vertices,
      descInc v.2 ≤ (sys.length / J + 1) * S := by
  intro v hv
  change v ∈ rows P ℓ J K s sys d ++ cols P J K s n sys d at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · split_ifs at hv with hl
      · obtain ⟨g, _, rfl⟩ := List.mem_map.mp hv
        rw [descInc_rowVertex hJ]
        calc _ ≤ (List.residueClass J sys.length g).length * S := by
                refine (List.sum_le_length_nsmul _ S fun x hx => ?_).trans (by simp)
                obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
                have hi' : i < sys.length := List.mem_range.mp (List.mem_filter.mp hi).1
                rw [List.getD_eq_getElem _ _ hi']
                exact hS _ (List.getElem_mem hi')
          _ ≤ _ := Nat.mul_le_mul_right _ (List.length_residueClass_le J sys.length g)
      · rw [List.mem_singleton.mp hv]
        exact Nat.zero_le _
    · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hv
      exact Nat.zero_le _
  · rcases List.mem_append.mp hv with hv | hv
    · split_ifs at hv
      · obtain ⟨g, _, rfl⟩ := List.mem_map.mp hv
        exact Nat.zero_le _
      · simp at hv
    · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hv
      exact Nat.zero_le _

/-- A quarter-root test group with polylogarithmic scopes has at most `ceil(s^(9/10))`
incidences, eventually, uniformly over the degree array and system. -/
theorem exists_groupInc_le (c : ℕ) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (c * n / Nat.ceilQuarter n + 1) * Nat.clog 2 n ^ c ≤ ceilNineTenths (sizeParam n) := by
  let B := (16 * (c ^ 4 + 1)) ^ 10
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    (Nat.eventually_mul_add_one_pow_le_pow_div B (40 * c) 2 one_lt_two (by norm_num))
  refine ⟨2 ^ (L₀ + 2) + 5, fun n hn => ?_⟩
  set lam := Nat.clog 2 n
  set J := Nat.ceilQuarter n
  set a := c * n / J
  have hn5 : 5 ≤ n := (Nat.le_add_left 5 _).trans hn
  have hn1 : 1 ≤ n := by omega
  have hJ : 0 < J := Nat.ceilQuarter_pos hn1
  have hlam : L₀ + 2 ≤ lam := by
    have h := Nat.clog_mono_right 2 ((Nat.le_add_right (2 ^ (L₀ + 2)) 5).trans hn)
    rwa [Nat.clog_pow 2 _ one_lt_two] at h
  have hnu : 1 ≤ Nat.clog 2 lam := Nat.clog_pos one_lt_two (by omega)
  have hns : n ≤ sizeParam n := Nat.le_mul_of_pos_right _ hnu
  have ha4 : a ^ 4 ≤ c ^ 4 * n ^ 3 := div_pow_four_le hJ (Nat.le_ceilQuarter_pow n)
  have ha1 : (a + 1) ^ 4 ≤ 16 * (c ^ 4 + 1) * n ^ 3 := by
    have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn1
    have h16 : (a + 1) ^ 4 ≤ 16 * (a ^ 4 + 1) := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · simp [h0]
      · calc (a + 1) ^ 4 ≤ (2 * a) ^ 4 := Nat.pow_le_pow_left (by omega) _
          _ = 16 * a ^ 4 := by ring
          _ ≤ 16 * (a ^ 4 + 1) := by omega
    calc (a + 1) ^ 4 ≤ 16 * (a ^ 4 + 1) := h16
      _ ≤ 16 * (c ^ 4 * n ^ 3 + n ^ 3) := by omega
      _ = 16 * (c ^ 4 + 1) * n ^ 3 := by ring
  have hB : B * lam ^ (40 * c) ≤ n := by
    have h1 := Nat.mul_le_mul_left B (Nat.pow_le_pow_left (Nat.le_succ lam) (40 * c))
    have h2 := hL₀ lam (by omega)
    have h3 : 2 ^ (lam / 2) ≤ 2 ^ (lam - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (lam - 1) < n := by
      simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self one_lt_two
        (show 1 < n by omega)
    exact h1.trans (h2.trans (h3.trans h4.le))
  apply le_ceilNineTenths_of_pow_le (hn1.trans hns)
  apply (Nat.pow_le_pow_iff_left (n := 4) (by norm_num)).mp
  calc (((a + 1) * lam ^ c) ^ 10) ^ 4 = ((a + 1) ^ 4) ^ 10 * lam ^ (40 * c) := by ring
    _ ≤ (16 * (c ^ 4 + 1) * n ^ 3) ^ 10 * lam ^ (40 * c) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ha1 _)
    _ = n ^ 30 * (B * lam ^ (40 * c)) := by dsimp only [B]; ring
    _ ≤ n ^ 30 * n ^ 6 :=
        Nat.mul_le_mul_left _ (hB.trans (Nat.le_self_pow (by norm_num) _))
    _ = n ^ 36 := by ring
    _ ≤ (sizeParam n ^ 9) ^ 4 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_left hns _

/-- The actual entry evaluator meets Theorem D.1's resource hypotheses at the sharp size `n ν`.
All constants and the exceptional-size threshold are chosen before the instance. -/
theorem exists_entry_admissible (c : ℕ) : ∃ C n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (K : ℕ) (sys : List (List (List ℕ))) (d : List ℕ),
    sys.length ≤ c * n → n ≤ K → K ≤ c * n →
    (∀ eq ∈ sys, (equationVars eq).length ≤ Nat.clog 2 n ^ c) →
    (∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) →
    (∀ v < n, varDegree v sys ≤ Nat.clog 2 n ^ c) →
      TruncEntryAdmissible incCertificate C (sizeParam n) (lemmaNetwork K n sys d) := by
  obtain ⟨C₀, n₀, hshape⟩ := exists_size c
  obtain ⟨n₁, hgroup⟩ := exists_groupInc_le c
  obtain ⟨b, hb⟩ := exists_incCertificate_le
  let C := C₀ + b * 3 ^ b + b + 1
  refine ⟨C, max n₀ n₁ + 5, fun n hn K sys d hsys hnK hKn hS hvars hD => ?_⟩
  obtain ⟨hsm, hmC, hvC, hdeg⟩ := hshape n (by omega) K sys d hsys hnK hKn hS hvars hD
  let G := (lemmaNetwork K n sys d).2
  have hinc : ∀ v ∈ G.vertices, descInc v.2 ≤ ceilNineTenths (sizeParam n) := by
    intro v hv
    have hJ : 0 < Nat.ceilQuarter n := Nat.ceilQuarter_pos (by omega)
    exact (descInc_le hJ hS v hv).trans ((Nat.mul_le_mul_right _
      (Nat.add_le_add_right (Nat.div_le_div_right hsys) 1)).trans (hgroup n (by omega)))
  refine ⟨⟨isRowsFirstBipartite_network, hsm,
    hmC.trans (Nat.mul_le_mul_right _ (by dsimp only [C]; omega)), hdeg, ?_⟩,
    hvC.trans (Nat.mul_le_mul_right _ (by dsimp only [C]; omega))⟩
  intro v hv bs hbs
  change v ∈ G.vertices at hv
  let B := sizeParam n + (DescribedNetwork.encDescribed encDesc G).length + 1
  have hB1 : 1 ≤ B := by dsimp only [B]; omega
  have hq : (encPair encDesc encBits (v.2, bs)).length + 1 ≤ 3 * B := by
    have h1 := length_le_encList_of_mem (encPair (encList encNat) encDesc) hv
    have h2 : (encList (encPair (encList encNat) encDesc) G.vertices).length ≤
        (DescribedNetwork.encDescribed encDesc G).length := by
      change _ ≤ (encPair encUnary (encList (encPair (encList encNat) encDesc))
        (G.numEdges, G.vertices)).length
      rw [length_encPair]
      dsimp only
      omega
    have h3 := length_le_length_encList encNat v.1
    rw [length_encPair] at h1 ⊢
    change 2 * (encDesc v.2).length + 1 + bs.length + 1 ≤ 3 * B
    dsimp only [B]
    omega
  have hpoly : b * ((encPair encDesc encBits (v.2, bs)).length + 1) ^ b ≤ C * B ^ C := by
    calc _ ≤ b * (3 * B) ^ b := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq _)
      _ = b * 3 ^ b * B ^ b := by rw [mul_pow]; ring
      _ ≤ C * B ^ C := Nat.mul_le_mul (by dsimp only [C]; omega)
          (Nat.pow_le_pow_right hB1 (by dsimp only [C]; omega))
  have hexp : 2 ^ descInc v.2 ≤ 2 ^ (C * ceilNineTenths (sizeParam n)) :=
    Nat.pow_le_pow_right (by norm_num) ((hinc v hv).trans
      (Nat.le_mul_of_pos_left _ (by dsimp only [C]; omega)))
  exact ⟨(hb (v.2, bs)).1.trans (Nat.mul_le_mul hpoly hexp), (hb (v.2, bs)).2.trans hpoly⟩

/-- The actual truncated contraction of every constructed network has the sharp `s / sqrt(log s)`
rate at `s=n ν`, polynomial precision/order `n+1` and polynomial workspace. This does not yet sum
all degree arrays or high-incidence branches into a sparse-system counter. -/
theorem exists_contraction_bound (c : ℕ) : ∃ A n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ (K : ℕ) (sys : List (List (List ℕ))) (d : List ℕ),
    sys.length ≤ c * n → n ≤ K → K ≤ c * n →
    (∀ eq ∈ sys, (equationVars eq).length ≤ Nat.clog 2 n ^ c) →
    (∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) →
    (∀ v < n, varDegree v sys ≤ Nat.clog 2 n ^ c) →
    let inp := (n + 1, n + 1, lemmaNetwork K n sys d)
    let L := (encTrunc encDesc inp).length
    (CountingSimulation.truncEntryContractionAlgorithm incCertificate).certificate.time inp ≤
        A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n))) ∧
      (CountingSimulation.truncEntryContractionAlgorithm incCertificate).certificate.space inp ≤
        A * (L + 1) ^ A := by
  obtain ⟨C, n₀, hC⟩ := exists_entry_admissible c
  obtain ⟨A, hA⟩ := (CountingSimulation.truncEntryContractionAlgorithm incCertificate).bound C 2
  refine ⟨A, n₀ + 5, fun n hn K sys d hsys hnK hKn hS hvars hD => ?_⟩
  have hn1 : 1 ≤ Nat.clog 2 (Nat.clog 2 n) := by
    apply Nat.clog_pos one_lt_two
    have h := Nat.clog_mono_right 2 (show 2 ^ 2 ≤ n by omega)
    simp only [Nat.clog_pow 2 2 one_lt_two] at h
    omega
  have hns : n ≤ sizeParam n := Nat.le_mul_of_pos_right _ hn1
  exact hA (sizeParam n) (n + 1) (n + 1) _ _ (by omega) (by omega) (by omega)
    (by omega) (by omega) (hC n (by omega) K sys d hsys hnK hKn hS hvars hD)

/-- On an actual sparse branch, compute the source's degree cap `k (a + 2n)` from the equation
list. No degree cap, entry-time budget or contraction algorithm is supplied as advice. -/
theorem exists_sparseBranch_contraction_bound (k c : ℕ) (hk : 1 ≤ k) :
    ∃ A n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (sys : List (List (List ℕ))) (d : List ℕ),
    SubexponentialSAT.IncidenceBranching.IsSparseBranch k c n sys →
    let inp := (n + 1, n + 1, lemmaNetwork (k * (sys.length + 2 * n)) n sys d)
    let L := (encTrunc encDesc inp).length
    (CountingSimulation.truncEntryContractionAlgorithm incCertificate).certificate.time inp ≤
        A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n))) ∧
      (CountingSimulation.truncEntryContractionAlgorithm incCertificate).certificate.space inp ≤
        A * (L + 1) ^ A := by
  let C := k * (c + 2) + c + 1
  obtain ⟨A, n₀, hA⟩ := exists_contraction_bound C
  refine ⟨A, n₀ + 5, fun n hn sys d hs => ?_⟩
  have hCc : c ≤ C := by dsimp only [C]; omega
  have hlam : 1 ≤ Nat.clog 2 n := Nat.clog_pos one_lt_two (by omega)
  have hpow : Nat.clog 2 n ^ c ≤ Nat.clog 2 n ^ C := Nat.pow_le_pow_right hlam hCc
  apply hA n (by omega) (k * (sys.length + 2 * n)) sys d
  · exact hs.length_le.trans (Nat.mul_le_mul_right _ hCc)
  · calc n ≤ sys.length + 2 * n := by omega
      _ ≤ k * (sys.length + 2 * n) := Nat.le_mul_of_pos_left _ hk
  · calc k * (sys.length + 2 * n) ≤ k * (c * n + 2 * n) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right hs.length_le _)
      _ = (k * (c + 2)) * n := by ring
      _ ≤ C * n := Nat.mul_le_mul_right _ (by dsimp only [C]; omega)
  · exact fun eq heq => (hs.scope_le eq heq).trans hpow
  · exact hs.vars_lt
  · exact fun v hv => (hs.varDegree_le v hv).trans hpow

end Cslib.Circuits.Frontier.IncidenceNetwork

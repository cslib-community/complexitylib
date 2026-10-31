/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceNetworkBounds
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.EntryContraction
import Complexity.Foundations.Data.Nat.Asymptotics

/-!
# The size of the incidence network at `s = n ν`

Lemma D.2 of [OpenAI2026ETH] applies Theorem D.1 to the incidence network
(`Cslib.Circuits.Frontier.IncidenceNetwork.network`) with `J = ⌈n ^ (1/4)⌉` groups, size parameter
`s = n ν` and precision and truncation order `n + 1`, where `λ = ⌈log₂ n⌉` and `ν = ⌈log₂ λ⌉`
(p. 56). This file fixes these parameters (`IncidenceNetwork.lemmaNetwork`) and proves the shape
hypotheses of Theorem D.1 for all sufficiently large `n` (`IncidenceNetwork.exists_size`): at
least `s` and at most `C s` edges, at most `C s` vertices, and degree at most `⌈s ^ (9/10)⌉`.

The hypotheses are those of a reduced branch of Lemma D.2 (p. 54), up to constants: at most `c n`
tests, every scope with at most `λ ^ c` variables, every variable in at most `λ ^ c` scopes, and
`n ≤ K ≤ c n` for the degree cap. The paper's `K = k (a + 2 (ℓ - 1))` with `ℓ = n + 1` satisfies
the last for `k ≥ 1`.

* *Edges.* By (D.3) (`IncidenceNetwork.numWires_le`) with `R = c λ ^ c + 1`, a live array has at
  most `J² + K ⌈log₂ (3 R)⌉ ≤ 4 n + c n (⌈log₂ (3 c + 3)⌉ + c) ν` index wires.
* *Degrees.* A group vertex has at most `(c n / J + 1) λ ^ c` ports
  (`IncidenceNetwork.length_rowPorts_le`, `IncidenceNetwork.length_colPorts_le`), and
  `(c n / J) ^ 4 ≤ c ^ 4 n ³`, so its tenth power is at most `n ^ (15/2) λ ^ (10 c)` up to
  constants, below `s ^ 9` once `λ ^ (40 c)` is below `n ^ 6`.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.ceilQuarter`: `⌈n ^ (1/4)⌉`.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sizeParam`: `s = n ν`.
* `Cslib.Circuits.Frontier.IncidenceNetwork.lemmaNetwork`: the network of Lemma D.2.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.length_ports_le`: the ports of any vertex.
* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_size`: the shape hypotheses of Theorem D.1.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.2 (pp. 54–56).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.Complexity

/-! ### Parameters -/

theorem le_self_pow_four (n : ℕ) : n ≤ n ^ 4 := by
  rcases n with _ | n
  · simp
  · exact Nat.le_self_pow (by norm_num) _

theorem exists_le_pow_four (n : ℕ) : ∃ J, n ≤ J ^ 4 := ⟨n, le_self_pow_four n⟩

/-- **`⌈n ^ (1/4)⌉`**, the least `J` with `n ≤ J ^ 4`: the number of groups of Lemma D.2. -/
@[expose] def ceilQuarter (n : ℕ) : ℕ := Nat.find (exists_le_pow_four n)

theorem le_ceilQuarter_pow (n : ℕ) : n ≤ ceilQuarter n ^ 4 := Nat.find_spec (exists_le_pow_four n)

theorem ceilQuarter_pos {n : ℕ} (hn : 1 ≤ n) : 0 < ceilQuarter n := by
  by_contra h
  have h0 : ceilQuarter n = 0 := by omega
  have := le_ceilQuarter_pow n
  rw [h0] at this
  simp at this
  omega

theorem ceilQuarter_le_self (n : ℕ) : ceilQuarter n ≤ n := Nat.find_min' _ (le_self_pow_four n)

/-- `J² ≤ 4 n` for `J = ⌈n ^ (1/4)⌉` and `n ≥ 1`. -/
theorem ceilQuarter_mul_self_le {n : ℕ} (hn : 1 ≤ n) : ceilQuarter n * ceilQuarter n ≤ 4 * n := by
  set J := ceilQuarter n
  have hJ := ceilQuarter_pos hn
  have hmin : ¬ n ≤ (J - 1) ^ 4 :=
    Nat.find_min (exists_le_pow_four n) (show J - 1 < ceilQuarter n by omega)
  have h2 : (J - 1) * (J - 1) ≤ (J - 1) ^ 4 := by
    rcases Nat.eq_zero_or_pos (J - 1) with h | h
    · simp [h]
    · calc (J - 1) * (J - 1) = (J - 1) ^ 2 := (sq _).symm
        _ ≤ (J - 1) ^ 4 := Nat.pow_le_pow_right h (by norm_num)
  rcases Nat.lt_or_ge J 2 with hJ2 | hJ2
  · have : J = 1 := by omega
    rw [this]
    omega
  · have : J ≤ 2 * (J - 1) := by omega
    nlinarith

/-- **The size parameter of Lemma D.2**: `s = n ν`, for `λ = ⌈log₂ n⌉` and `ν = ⌈log₂ λ⌉`. -/
@[expose] def sizeParam (n : ℕ) : ℕ := n * Nat.clog 2 (Nat.clog 2 n)

/-- **The network of Lemma D.2** for the array `d` of a system on `n` variables with degree cap
`K`: `⌈n ^ (1/4)⌉` groups, size `n ν`, precision and truncation order `n + 1` (p. 56). -/
@[expose] def lemmaNetwork (K n : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :
    ℕ × DescribedNetwork Desc :=
  network (n + 1) (n + 1) (ceilQuarter n) K (sizeParam n) n sys d

/-! ### Ports of all vertices -/

variable {P ℓ J K s n : ℕ} {sys : List (List (List ℕ))} {d : List ℕ}

/-- **The ports of every vertex**: a padding vertex has one, the isolated row none, and a group
vertex at most `(a / J + 1) S` or `(n / J + 1) D` under the hypotheses of the degree bounds. -/
theorem length_ports_le (hJ : 0 < J) {S D : ℕ}
    (hS : ∀ eq ∈ sys, (equationVars eq).length ≤ S)
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) (hD : ∀ v < n, varDegree v sys ≤ D) :
    ∀ v ∈ (network P ℓ J K s n sys d).2.vertices,
      v.1.length ≤ max 1 (max ((sys.length / J + 1) * S) ((n / J + 1) * D)) := by
  intro v hv
  change v ∈ rows P ℓ J K s sys d ++ cols P J K s n sys d at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · by_cases hl : live J K d
      · rw [ite_eq_left hl] at hv
        obtain ⟨g, -, rfl⟩ := List.mem_map.mp hv
        exact (length_rowPorts_le hJ g hS).trans (le_max_of_le_right (le_max_left _ _))
      · rw [ite_eq_right hl] at hv
        rw [List.mem_singleton.mp hv]
        simp [deadRow]
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hv
      simp [padRow]
  · rcases List.mem_append.mp hv with hv | hv
    · by_cases hl : live J K d
      · rw [ite_eq_left hl] at hv
        obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
        exact (length_colPorts_le hJ (List.mem_range.mp hh) hvars hD).trans
          (le_max_of_le_right (le_max_right _ _))
      · rw [ite_eq_right hl] at hv
        simp at hv
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hv
      simp [padCol]

/-! ### Asymptotics -/

/-- `x ≤ ⌈s ^ (9/10)⌉` whenever `x ^ 10 ≤ s ^ 9` and `s ≥ 1`. -/
theorem le_ceilNineTenths_of_pow_le {x s : ℕ} (hs : 1 ≤ s) (h : x ^ 10 ≤ s ^ 9) :
    x ≤ ceilNineTenths s := by
  rw [le_ceilNineTenths_iff hs]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa using Nat.pow_pos (n := 9) hs
  · exact (Nat.pow_lt_pow_left (by omega) (by norm_num)).trans_le h

/-- `(c n / J) ^ 4 ≤ c ^ 4 n ³` when `n ≤ J ^ 4`. -/
theorem div_pow_four_le {c n J : ℕ} (hJ : 0 < J) (hn : n ≤ J ^ 4) :
    (c * n / J) ^ 4 ≤ c ^ 4 * n ^ 3 := by
  have h1 : (c * n / J * J) ^ 4 ≤ (c * n) ^ 4 := Nat.pow_le_pow_left (Nat.div_mul_le_self _ _) _
  have hJ4 : 0 < J ^ 4 := Nat.pow_pos (n := 4) hJ
  refine Nat.le_of_mul_le_mul_right ?_ hJ4
  calc (c * n / J) ^ 4 * J ^ 4 = (c * n / J * J) ^ 4 := (Nat.mul_pow _ _ _).symm
    _ ≤ (c * n) ^ 4 := h1
    _ = c ^ 4 * n ^ 3 * n := by ring
    _ ≤ c ^ 4 * n ^ 3 * J ^ 4 := Nat.mul_le_mul_left _ hn

/-- **The shape hypotheses of Theorem D.1 for the network of Lemma D.2.** For every `c` there are
`C` and `n₀` such that for all `n ≥ n₀`, every system on `n` variables with at most `c n` tests,
scopes of at most `λ ^ c` variables, and every variable in at most `λ ^ c` scopes, every degree cap
`n ≤ K ≤ c n` and every array, the network of Lemma D.2 at size `s = n ν` has between `s` and
`C s` edges, at most `C s` vertices, and maximum degree at most `⌈s ^ (9/10)⌉`. -/
theorem exists_size (c : ℕ) : ∃ C n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (K : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ), sys.length ≤ c * n → n ≤ K → K ≤ c * n →
    (∀ eq ∈ sys, (equationVars eq).length ≤ Nat.clog 2 n ^ c) →
    (∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) →
    (∀ v < n, varDegree v sys ≤ Nat.clog 2 n ^ c) →
    sizeParam n ≤ (lemmaNetwork K n sys d).2.numEdges ∧
      (lemmaNetwork K n sys d).2.numEdges ≤ C * sizeParam n ∧
      (lemmaNetwork K n sys d).2.vertices.length ≤ C * sizeParam n ∧
      ∀ v ∈ (lemmaNetwork K n sys d).2.vertices, v.1.length ≤ ceilNineTenths (sizeParam n) := by
  set c' := c + 1
  set A := Nat.clog 2 (3 * c + 3)
  set B := (16 * (c' ^ 4 + 1)) ^ 10
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    (Nat.eventually_mul_add_one_pow_le_pow_div B (40 * c') 2 one_lt_two (by norm_num))
  refine ⟨5 + c * (A + c), 2 ^ (L₀ + 2) + 5, fun n hn K sys d hsys hnK hKn hS hvars hD => ?_⟩
  set lam := Nat.clog 2 n with hlam
  set nu := Nat.clog 2 lam with hnu
  set J := ceilQuarter n with hJdef
  have hn5 : 5 ≤ n := (Nat.le_add_left 5 _).trans hn
  have hn1 : 1 ≤ n := by omega
  have hJ : 0 < J := ceilQuarter_pos hn1
  -- `λ ≥ L₀ + 2 ≥ 2` and `ν ≥ 1`.
  have hlamL : L₀ + 2 ≤ lam := by
    have := Nat.clog_mono_right 2 ((Nat.le_add_right (2 ^ (L₀ + 2)) 5).trans hn)
    rwa [Nat.clog_pow 2 _ one_lt_two] at this
  have hnu1 : 1 ≤ nu := Nat.clog_pos one_lt_two (by omega)
  have hlam1 : 1 ≤ lam ^ c := Nat.one_le_pow _ _ (by omega)
  have hs : sizeParam n = n * nu := rfl
  have hns : n ≤ sizeParam n := by rw [hs]; exact Nat.le_mul_of_pos_right _ hnu1
  -- The index wires.
  have hM : mainWires J K sys d ≤ (4 + c * (A + c)) * (n * nu) := by
    unfold mainWires
    split_ifs with hl
    · have hinc : numInc sys ≤ c * n * lam ^ c :=
        (List.sum_le_length_nsmul _ _ fun x hx => by
          obtain ⟨eq, heq, rfl⟩ := List.mem_map.mp hx
          exact hS eq heq).trans (by simp only [List.length_map, smul_eq_mul]; nlinarith)
      have hR : numInc sys + K ≤ (c * lam ^ c + 1) * K := by nlinarith
      have hW := numWires_le hJ hl hR
      have hlog : Nat.clog 2 (3 * (c * lam ^ c + 1)) ≤ (A + c) * nu := by
        refine Nat.clog_le_of_le_pow ?_
        have hlamle : lam ≤ 2 ^ nu := Nat.le_pow_clog one_lt_two _
        have hA : 3 * c + 3 ≤ 2 ^ A := Nat.le_pow_clog one_lt_two _
        calc 3 * (c * lam ^ c + 1) ≤ (3 * c + 3) * lam ^ c := by nlinarith
          _ ≤ 2 ^ A * (2 ^ nu) ^ c := Nat.mul_le_mul hA (Nat.pow_le_pow_left hlamle _)
          _ = 2 ^ (A + nu * c) := by rw [← pow_mul, ← pow_add]
          _ ≤ 2 ^ ((A + c) * nu) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have hJJ := ceilQuarter_mul_self_le hn1
      calc numWires J sys d ≤ J * J + K * Nat.clog 2 (3 * (c * lam ^ c + 1)) := hW
        _ ≤ 4 * n + c * n * ((A + c) * nu) := Nat.add_le_add hJJ (Nat.mul_le_mul hKn hlog)
        _ ≤ (4 + c * (A + c)) * (n * nu) := by nlinarith
    · exact Nat.zero_le _
  have hE : (lemmaNetwork K n sys d).2.numEdges = max (mainWires J K sys d) (sizeParam n) :=
    numEdges_network
  refine ⟨hE ▸ le_max_right _ _, ?_, ?_, ?_⟩
  · rw [hE, hs]
    refine max_le (hM.trans (Nat.mul_le_mul_right _ (by omega))) ?_
    nlinarith
  · have hV := length_vertices_network (P := n + 1) (ℓ := n + 1) (J := J) (K := K)
      (s := sizeParam n) (n := n) (sys := sys) (d := d)
    change (network (n + 1) (n + 1) J K (sizeParam n) n sys d).2.vertices.length ≤ _
    rw [hV]
    have hJn : J ≤ n := ceilQuarter_le_self n
    have : (if live J K d = true then 2 * J else 1) ≤ 2 * n := by split_ifs <;> omega
    have h5 : 5 * sizeParam n ≤ (5 + c * (A + c)) * sizeParam n :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · -- Degrees.
    intro v hv
    have hports := length_ports_le (P := n + 1) (ℓ := n + 1) (K := K) (s := sizeParam n)
      (d := d) hJ hS hvars hD v hv
    have hs1 : 1 ≤ sizeParam n := hn1.trans hns
    -- The bound `x = (c' n / J + 1) λ ^ c` on both group degrees.
    set a := c' * n / J with ha
    have hx : (a + 1) * lam ^ c ≤ ceilNineTenths (sizeParam n) := by
      refine le_ceilNineTenths_of_pow_le hs1
        ((Nat.pow_le_pow_iff_left (n := 4) (by norm_num)).mp ?_)
      have ha4 : a ^ 4 ≤ c' ^ 4 * n ^ 3 := div_pow_four_le hJ (le_ceilQuarter_pow n)
      have ha1 : (a + 1) ^ 4 ≤ 16 * (c' ^ 4 + 1) * n ^ 3 := by
        have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn1
        have h16 : (a + 1) ^ 4 ≤ 16 * (a ^ 4 + 1) := by
          rcases Nat.eq_zero_or_pos a with h0 | h0
          · simp [h0]
          · calc (a + 1) ^ 4 ≤ (2 * a) ^ 4 := Nat.pow_le_pow_left (by omega) _
              _ = 16 * a ^ 4 := by ring
              _ ≤ 16 * (a ^ 4 + 1) := by omega
        calc (a + 1) ^ 4 ≤ 16 * (a ^ 4 + 1) := h16
          _ ≤ 16 * (c' ^ 4 * n ^ 3 + n ^ 3) := by omega
          _ = 16 * (c' ^ 4 + 1) * n ^ 3 := by ring
      -- `B λ ^ (40 c) ≤ n`.
      have hB : B * lam ^ (40 * c) ≤ n := by
        have h1 : B * lam ^ (40 * c) ≤ B * (lam + 1) ^ (40 * c') :=
          Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
            (Nat.pow_le_pow_right (by omega) (by omega)))
        have h2 := hL₀ lam (by omega)
        have h3 : 2 ^ (lam / 2) ≤ 2 ^ (lam - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h4 : 2 ^ (lam - 1) < n := by
          have := Nat.pow_pred_clog_lt_self one_lt_two (show 1 < n by omega)
          rwa [Nat.pred_eq_sub_one] at this
        omega
      have hns36 : n ^ 36 ≤ sizeParam n ^ 36 := Nat.pow_le_pow_left hns _
      calc (((a + 1) * lam ^ c) ^ 10) ^ 4 = ((a + 1) ^ 4) ^ 10 * lam ^ (40 * c) := by ring
        _ ≤ (16 * (c' ^ 4 + 1) * n ^ 3) ^ 10 * lam ^ (40 * c) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ha1 _)
        _ = n ^ 30 * (B * lam ^ (40 * c)) := by ring
        _ ≤ n ^ 30 * n ^ 6 := Nat.mul_le_mul_left _ (hB.trans (Nat.le_self_pow (by norm_num) _))
        _ = n ^ 36 := by ring
        _ ≤ (sizeParam n ^ 9) ^ 4 := by rw [← pow_mul]; exact hns36
    refine hports.trans (max_le ?_ (max_le ?_ ?_))
    · exact le_ceilNineTenths_of_pow_le hs1 (by simpa using Nat.one_le_pow 9 _ hs1)
    · refine le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right ?_ 1)) hx
      exact Nat.div_le_div_right (hsys.trans (Nat.mul_le_mul_right _ (by omega)))
    · refine le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right ?_ 1)) hx
      exact Nat.div_le_div_right (Nat.le_mul_of_pos_left _ (by omega))

end Cslib.Circuits.Frontier.IncidenceNetwork

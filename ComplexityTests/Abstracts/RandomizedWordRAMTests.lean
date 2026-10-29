/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.RandomizedWordRAMAbstract

/-!
# Regression tests for `RandomizedWordRAMAbstract`

Concrete checks on the abstract's randomized word-RAM semantics (`rand(0)` returning `0` while
charging one `rand` call, `rand(2 ^ w - 1)` uniformity, `rand` faulting at `2 ^ w`, and
`rand`-free deterministic execution with `0` `rand` calls) and non-vacuous instantiations of
`RandomizedWordRAMAbstract.quicksort` and `RandomizedWordRAMAbstract.quickselect` on
duplicate-heavy, singleton, and out-of-range inputs.
-/

namespace ComplexityTests.Abstracts.RandomizedWordRAMTests

open ComplexityAbstracts.RandomizedWordRAMAbstract

/-- Program executing `R[0] ← rand(R[0]); halt R[0]`. On `init []`, `R[0] = 0`, so this tests
`rand(0)` in `2` instructions (`rand` then `halt`). -/
def randZeroProg : Program 1 :=
  [.rand 0 0, .halt 0]

/-- `rand(0)` halts in `2` steps returning `0`, charges `1` `rand` call (`¬RandCallsBounded ... 0`),
and produces a point-mass distribution on `.halted 0`. -/
theorem randZero_behavior :
    HaltsWithin 3 randZeroProg (init []) 2 ∧
    RandCallsBounded 3 randZeroProg (init []) 2 1 ∧
    ¬RandCallsBounded 3 randZeroProg (init []) 2 0 ∧
    evalRand 3 randZeroProg 2 (init []) =
      PMF.pure (.halted 0 (fun _ => 0) (init (r := 1) []).mem) := by
  have hrun : runRand 3 randZeroProg 2 (.running (init [])) =
      Comp.sample 0 fun k =>
        Comp.pure (.halted ((Function.update (fun _ : Fin 1 => 0) 0 k.val) 0)
          (Function.update (fun _ : Fin 1 => 0) 0 k.val) (init (r := 1) []).mem) := rfl
  have heval : evalRand 3 randZeroProg 2 (init []) =
      PMF.pure (.halted 0 (fun _ => 0) (init (r := 1) []).mem) := by
    rw [evalRand, hrun]
    simp only [Comp.eval]
    have hfun : (fun k : Fin 1 =>
        PMF.pure (Cfg.halted ((Function.update (fun _ : Fin 1 => 0) 0 k.val) 0)
          (Function.update (fun _ : Fin 1 => 0) 0 k.val) (init (r := 1) []).mem)) =
        fun _ => PMF.pure (Cfg.halted 0 (fun _ => 0) (init (r := 1) []).mem) := by
      funext k
      fin_cases k
      simp
    rw [hfun, PMF.bind_const]
  refine ⟨?_, ?_, ?_, heval⟩
  · intro cfg hcfg
    rw [heval, PMF.mem_support_pure_iff] at hcfg
    exact ⟨0, _, _, hcfg⟩
  · rw [RandCallsBounded, hrun]
    intro k
    trivial
  · rw [RandCallsBounded, hrun]
    exact id

/-- Program executing `R[0] := bound; R[0] ← rand(R[0]); halt R[0]`. -/
def randBoundProg (bound : ℕ) : Program 1 :=
  [.const 0 bound, .rand 0 0, .halt 0]

/-- At word size `w = 2`, `rand(2 ^ 2 - 1) = rand(3)` halts in `3` steps with `1` `rand` call,
giving each output `k < 4` probability `1 / 4`. -/
theorem randMaxWord_uniform (k : Fin 4) :
    HaltsWithin 2 (randBoundProg 3) (init []) 3 ∧
    RandCallsBounded 2 (randBoundProg 3) (init []) 3 1 ∧
    evalRand 2 (randBoundProg 3) 3 (init [])
      (.halted k.val (fun _ => k.val) (init (r := 1) []).mem) = (4 : ENNReal)⁻¹ := by
  have hrun : runRand 2 (randBoundProg 3) 3 (.running (init [])) =
      Comp.sample 3 fun j =>
        Comp.pure (.halted
          ((Function.update (Function.update (fun _ : Fin 1 => 0) 0 3) 0 j.val) 0)
          (Function.update (Function.update (fun _ : Fin 1 => 0) 0 3) 0 j.val)
          (init (r := 1) []).mem) := rfl
  have hupd (v : ℕ) :
      Function.update (Function.update (fun _ : Fin 1 => 0) 0 3) 0 v = (fun _ => v) := by
    funext i; fin_cases i; rfl
  have heval : evalRand 2 (randBoundProg 3) 3 (init []) =
      (Cslib.Probability.PMF.uniformOfFintype (Fin 4)).bind fun j =>
        PMF.pure (.halted j.val (fun _ => j.val) (init (r := 1) []).mem) := by
    rw [evalRand, hrun]
    simp only [Comp.eval]
    congr 1
    funext j
    simp [hupd]
  refine ⟨?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [heval, PMF.mem_support_bind_iff] at hcfg
    obtain ⟨j, -, hj⟩ := hcfg
    rw [PMF.mem_support_pure_iff] at hj
    exact ⟨j.val, _, _, hj⟩
  · rw [RandCallsBounded, hrun]
    intro j
    trivial
  · rw [heval, PMF.bind_apply, tsum_fintype]
    fin_cases k <;>
      simp [Cslib.Probability.PMF.uniformOfFintype_apply, PMF.pure_apply, Fin.sum_univ_four]

/-- When a register holds `n ≥ 2 ^ w`, `rand` faults and makes `0` random draws. -/
theorem randOverflow_faults :
    let s : State 1 := ⟨0, fun _ => 4, fun _ => 0⟩
    evalRand 2 [.rand 0 0] 1 s = PMF.pure .faulted ∧
    RandCallsBounded 2 [.rand 0 0] s 1 0 :=
  ⟨rfl, trivial⟩

/-- A `rand`-free program executes with `0` `rand` calls and point-mass output distribution. -/
theorem randFree_pointMass :
    HaltsWithin (r := 1) 3 [.const 0 5, .halt 0] (init []) 2 ∧
    RandCallsBounded (r := 1) 3 [.const 0 5, .halt 0] (init []) 2 0 ∧
    evalRand (r := 1) 3 [.const 0 5, .halt 0] 2 (init []) =
      PMF.pure (.halted 5 (fun _ => 5) (init (r := 1) []).mem) := by
  have hupd : Function.update (fun _ : Fin 1 => 0) 0 5 = (fun _ => 5) := by
    funext i; fin_cases i; rfl
  have heval : evalRand (r := 1) 3 [.const 0 5, .halt 0] 2 (init []) =
      PMF.pure (.halted 5 (fun _ => 5) (init (r := 1) []).mem) := by
    change PMF.pure (Cfg.halted ((Function.update (fun _ : Fin 1 => 0) 0 5) 0)
      (Function.update (fun _ : Fin 1 => 0) 0 5) (init (r := 1) []).mem) = _
    simp [hupd]
  refine ⟨?_, trivial, heval⟩
  intro cfg hcfg
  rw [heval, PMF.mem_support_pure_iff] at hcfg
  exact ⟨5, _, _, hcfg⟩

/-- Non-vacuous instantiation of `RandomizedWordRAMAbstract.quicksort` on `[3, 1, 2, 1, 3]`
(non-monotone, with duplicates) at word size `w = 9`: every path halts within `572` steps and `4`
`rand` calls with `[1, 1, 2, 3, 3]` in `M[1 .. 6)`, preserving `M[0] = 5` and `M[20] = 0`, and
expected running time is at most `1832`. -/
theorem quicksort_duplicate_instance :
    ∃ p : Program 16,
      HaltsWithin 9 p (init [3, 1, 2, 1, 3]) 572 ∧
      RandCallsBounded 9 p (init [3, 1, 2, 1, 3]) 572 4 ∧
      (∀ cfg ∈ (evalRand 9 p 572 (init [3, 1, 2, 1, 3])).support,
        ∃ reg mem, cfg = .halted 0 reg mem ∧
          slice 1 6 mem = [1, 1, 2, 3, 3] ∧
          mem 0 = 5 ∧ mem 20 = 0) ∧
      expectedTime 9 p (init [3, 1, 2, 1, 3]) ≤ (1832 : ENNReal) := by
  obtain ⟨p, hp⟩ := quicksort
  have hw : 3 * (Nat.log 2 ([3, 1, 2, 1, 3] : List ℕ).length + 1) ≤ 9 := by decide
  have hfit : InputFits 9 [3, 1, 2, 1, 3] := ⟨by decide, by decide⟩
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := hp 9 [3, 1, 2, 1, 3] hw hfit
  have hT : 20 * ([3, 1, 2, 1, 3] : List ℕ).length ^ 2 +
      8 * ([3, 1, 2, 1, 3] : List ℕ).length + 32 = 572 := by decide
  have hR : ([3, 1, 2, 1, 3] : List ℕ).length - 1 = 4 := by decide
  have hE : 120 * ([3, 1, 2, 1, 3] : List ℕ).length *
      (Nat.log 2 ([3, 1, 2, 1, 3] : List ℕ).length + 1) + 32 = 1832 := by decide
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · simpa [hT] using hHalts
  · simpa [hT, hR] using hCalls
  · intro cfg hcfg
    rw [← hT] at hcfg
    obtain ⟨reg, mem, rfl, -, -, hperm, hsort, hframe⟩ := hPost cfg hcfg
    have hperm_target : (slice 1 6 mem).Perm [1, 1, 2, 3, 3] :=
      hperm.trans (by decide : ([3, 1, 2, 1, 3] : List ℕ).Perm [1, 1, 2, 3, 3])
    have hslice_eq : slice 1 6 mem = [1, 1, 2, 3, 3] :=
      hperm_target.eq_of_pairwise' hsort (by decide)
    have hm0 : mem 0 = 5 := hframe 0 (Or.inl (by decide))
    have hm20 : mem 20 = 0 := hframe 20 (Or.inr (by decide))
    exact ⟨reg, mem, rfl, hslice_eq, hm0, hm20⟩
  · rw [hE] at hExp
    exact_mod_cast hExp

/-- Boundary instantiation of `RandomizedWordRAMAbstract.quicksort` on the empty list `[]` at word
size `w = 3`: halts within `32` steps with `0` `rand` calls and `expectedTime ≤ 32`. -/
theorem quicksort_empty_instance :
    ∃ p : Program 16,
      HaltsWithin 3 p (init []) 32 ∧
      RandCallsBounded 3 p (init []) 32 0 ∧
      expectedTime 3 p (init []) ≤ (32 : ENNReal) := by
  obtain ⟨p, hp⟩ := quicksort
  obtain ⟨hHalts, hCalls, -, hExp⟩ := hp 3 [] (by decide) ⟨by decide, by simp⟩
  exact ⟨p, hHalts, hCalls, by simpa using hExp⟩

/-- Duplicate-heavy test array `[4, 2, 4, 0, 2, 1]` with sorted order `[0, 1, 2, 2, 4, 4]`. -/
abbrev dup6 : List ℕ := [4, 2, 4, 0, 2, 1]

private theorem dup6_mergeSort : dup6.mergeSort = [0, 1, 2, 2, 4, 4] := by
  have hp6 : dup6.Perm [0, 1, 2, 2, 4, 4] :=
    List.perm_iff_count.mpr fun a => by
      rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ 5 ≤ a) with
        rfl | rfl | rfl | rfl | rfl | ha
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rw [List.count_eq_zero.mpr
            (by simp only [dup6, List.mem_cons, List.not_mem_nil, or_false]; omega),
          List.count_eq_zero.mpr
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)]
  exact ((List.mergeSort_perm dup6 (· ≤ ·)).trans hp6).eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≤ ·) dup6) (by decide)

/-- Non-vacuous instantiation of `RandomizedWordRAMAbstract.quickselect` on
`dup6 = [4, 2, 4, 0, 2, 1]` at word size `w = 6` across any in-range rank `k < 6`: a single program
`p` halts within `375` steps and `5` `rand` calls returning `[0, 1, 2, 2, 4, 4].getD k 0`, permuting
`M[2 .. 8)` around `2 + k`, preserving `M[0] = 7`, `M[1] = k`, and `M[8] = 0` (zero auxiliary
memory words), with `expectedTime ≤ 495`. -/
theorem quickselect_dup6_rank :
    ∃ p : Program 16, ∀ k < 6,
      let ans := ([0, 1, 2, 2, 4, 4] : List ℕ).getD k 0
      HaltsWithin 6 p (init (k :: dup6)) 375 ∧
      RandCallsBounded 6 p (init (k :: dup6)) 375 5 ∧
      (∀ cfg ∈ (evalRand 6 p 375 (init (k :: dup6))).support,
        ∃ reg mem, cfg = .halted ans reg mem ∧
          (slice 2 8 mem).Perm dup6 ∧
          mem (2 + k) = ans ∧
          (∀ i < k, mem (2 + i) ≤ ans) ∧
          (∀ i, k < i → i < 6 → ans ≤ mem (2 + i)) ∧
          mem 0 = 7 ∧ mem 1 = k ∧ mem 8 = 0) ∧
      expectedTime 6 p (init (k :: dup6)) ≤ (495 : ENNReal) := by
  obtain ⟨p, hp_in, -⟩ := quickselect
  refine ⟨p, fun k hk => ?_⟩
  have hw : 2 * (Nat.log 2 dup6.length + 1) ≤ 6 := by decide
  have hfit : InputFits 6 (k :: dup6) := by
    refine ⟨by change 7 < 2 ^ 6; decide, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · omega
    · simp only [dup6, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := hp_in 6 k dup6 (by simpa [dup6] using hk) hw hfit
  have hT : 10 * dup6.length ^ 2 + 15 = 375 := by decide
  have hR : dup6.length - 1 = 5 := rfl
  have hE : 80 * dup6.length + 15 = 495 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hT] using hHalts
  · simpa [hT, hR] using hCalls
  · intro cfg hcfg
    rw [← hT] at hcfg
    obtain ⟨reg, mem, hcfg_eq, -, -, hperm, hm_k, hleft, hright, hframe⟩ := hPost cfg hcfg
    simp only [dup6_mergeSort] at hcfg_eq hm_k hleft hright
    have hm0 : mem 0 = 7 := hframe 0 (Or.inl (by decide))
    have hm1 : mem 1 = k := by
      simpa [init] using hframe 1 (Or.inl (by decide))
    have hm8 : mem 8 = 0 := hframe 8 (Or.inr (by decide))
    exact ⟨reg, mem, hcfg_eq, hperm, hm_k, hleft,
      fun i hki hi6 => hright i hki (by simpa [dup6] using hi6), hm0, hm1, hm8⟩
  · rw [hE] at hExp
    exact_mod_cast hExp

/-- Concrete boundary and duplicate-rank checks (`k = 0, 2, 3, 5`) on `dup6` for a single program
`p`: outputs `0, 2, 2, 4` at `M[2], M[4], M[5], M[7]`. -/
theorem quickselect_dup6_concrete_ranks :
    ∃ p : Program 16,
      (∀ cfg ∈ (evalRand 6 p 375 (init (0 :: dup6))).support,
        ∃ reg mem, cfg = .halted 0 reg mem ∧ mem 2 = 0 ∧ mem 8 = 0) ∧
      (∀ cfg ∈ (evalRand 6 p 375 (init (2 :: dup6))).support,
        ∃ reg mem, cfg = .halted 2 reg mem ∧ mem 4 = 2) ∧
      (∀ cfg ∈ (evalRand 6 p 375 (init (3 :: dup6))).support,
        ∃ reg mem, cfg = .halted 2 reg mem ∧ mem 5 = 2) ∧
      (∀ cfg ∈ (evalRand 6 p 375 (init (5 :: dup6))).support,
        ∃ reg mem, cfg = .halted 4 reg mem ∧ mem 7 = 4) := by
  obtain ⟨p, hp⟩ := quickselect_dup6_rank
  obtain ⟨-, -, h₀, -⟩ := hp 0 (by decide)
  obtain ⟨-, -, h₂, -⟩ := hp 2 (by decide)
  obtain ⟨-, -, h₃, -⟩ := hp 3 (by decide)
  obtain ⟨-, -, h₅, -⟩ := hp 5 (by decide)
  refine ⟨p, fun cfg hc => ?_, fun cfg hc => ?_, fun cfg hc => ?_, fun cfg hc => ?_⟩
  · obtain ⟨reg, mem, hcfg, -, hm2, -, -, -, -, hm8⟩ := h₀ cfg hc
    exact ⟨reg, mem, hcfg, hm2, hm8⟩
  · obtain ⟨reg, mem, hcfg, -, hm4, -⟩ := h₂ cfg hc
    exact ⟨reg, mem, hcfg, hm4⟩
  · obtain ⟨reg, mem, hcfg, -, hm5, -⟩ := h₃ cfg hc
    exact ⟨reg, mem, hcfg, hm5⟩
  · obtain ⟨reg, mem, hcfg, -, hm7, -⟩ := h₅ cfg hc
    exact ⟨reg, mem, hcfg, hm7⟩

/-- Singleton `[7]` at `k = 0`, `w = 3`: `0` `rand` calls, returning `7` with `M[2] = 7` and
`M[3] = 0`. -/
theorem quickselect_singleton_instance :
    ∃ p : Program 16,
      HaltsWithin 3 p (init [0, 7]) 25 ∧
      RandCallsBounded 3 p (init [0, 7]) 25 0 ∧
      (∀ cfg ∈ (evalRand 3 p 25 (init [0, 7])).support,
        ∃ reg mem, cfg = .halted 7 reg mem ∧ mem 2 = 7 ∧ mem 3 = 0) ∧
      expectedTime 3 p (init [0, 7]) ≤ (95 : ENNReal) := by
  obtain ⟨p, hp_in, -⟩ := quickselect
  have hw : 2 * (Nat.log 2 ([7] : List ℕ).length + 1) ≤ 3 := by decide
  have hfit : InputFits 3 (0 :: [7]) := ⟨by decide, by decide⟩
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := hp_in 3 0 [7] (by decide) hw hfit
  have hms1 : ([7] : List ℕ).mergeSort = [7] :=
    (List.mergeSort_perm [7] (· ≤ ·)).eq_of_pairwise'
      (List.pairwise_mergeSort' (· ≤ ·) [7]) (by decide)
  refine ⟨p, hHalts, hCalls, fun cfg hcfg => ?_, by simpa using hExp⟩
  obtain ⟨reg, mem, hcfg_eq, -, -, -, hm2, -, -, hframe⟩ := hPost cfg hcfg
  simp only [hms1, List.getD_cons_zero] at hcfg_eq hm2
  exact ⟨reg, mem, hcfg_eq, hm2, hframe 3 (Or.inr (by decide))⟩

/-- Out-of-range `k ≥ n` (`k = 6` on `dup6` at `w = 6`, and `k = 0` on `[]` at `w = 1`):
deterministic `8`-step halting returning `0` with `0` `rand` calls, untouched memory, and
`expectedTime = 8`. -/
theorem quickselect_out_of_range_instances :
    ∃ p : Program 16,
      (HaltsWithin 6 p (init (6 :: dup6)) 8 ∧
       RandCallsBounded 6 p (init (6 :: dup6)) 8 0 ∧
       (∀ cfg ∈ (evalRand 6 p 8 (init (6 :: dup6))).support,
         ∃ reg mem, cfg = .halted 0 reg mem ∧ mem = (init (r := 16) (6 :: dup6)).mem) ∧
       expectedTime 6 p (init (6 :: dup6)) = 8) ∧
      (HaltsWithin 1 p (init [0]) 8 ∧
       RandCallsBounded 1 p (init [0]) 8 0 ∧
       (∀ cfg ∈ (evalRand 1 p 8 (init [0])).support,
         ∃ reg mem, cfg = .halted 0 reg mem ∧ mem = (init (r := 16) [0]).mem) ∧
       expectedTime 1 p (init [0]) = 8) := by
  obtain ⟨p, -, hp_out⟩ := quickselect
  have h1 := hp_out 6 6 dup6 (by decide) ⟨by decide, by decide⟩
  have h2 := hp_out 1 0 [] (by decide) ⟨by decide, by decide⟩
  exact ⟨p, ⟨h1.1, h1.2.1, fun cfg hc => by
    obtain ⟨reg, mem, hcfg, -, -, hm⟩ := h1.2.2.1 cfg hc
    exact ⟨reg, mem, hcfg, hm⟩, h1.2.2.2⟩,
    ⟨h2.1, h2.2.1, fun cfg hc => by
      obtain ⟨reg, mem, hcfg, -, -, hm⟩ := h2.2.2.1 cfg hc
      exact ⟨reg, mem, hcfg, hm⟩, h2.2.2.2⟩⟩

end ComplexityTests.Abstracts.RandomizedWordRAMTests

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
`RandomizedWordRAMAbstract.quicksort` on duplicate-heavy and boundary inputs.
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

end ComplexityTests.Abstracts.RandomizedWordRAMTests

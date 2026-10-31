/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.AKS.Congruence

/-!
# Step 5 of the AKS algorithm on the word RAM

Step 5 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] tests the congruence
`(X + a)^n ≡ X^n + a (mod X^r - 1, n)` for `a = 1, …, A`. The program runs the test for one `a`
(`Cslib.Algorithms.WordRAM.AKS.Congruence.program`) for each `a` in turn and clears a flag when
one fails.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.CongruenceLoop.program`: the loop.
* `Cslib.Algorithms.WordRAM.AKS.CongruenceLoop.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.CongruenceLoop.exec`: the flag is `1` exactly when the congruence
  holds for every `1 ≤ a ≤ A`, within `time r n A` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.CongruenceLoop

open Cslib.WordRAM Cslib.AKS

/-- Base address of the result block. -/
abbrev R : Fin 29 := 0
/-- Base address of the base block. -/
abbrev B : Fin 29 := 1
/-- Base address of the scratch block. -/
abbrev T : Fin 29 := 2
/-- The number `r` of coefficients. -/
abbrev rr : Fin 29 := 3
/-- The modulus `n`. -/
abbrev nn : Fin 29 := 4
/-- The tested value `a`, which is also the loop index. -/
abbrev av : Fin 29 := 21
/-- The answer of one test. -/
abbrev flag : Fin 29 := 24
/-- The last tested value `A`, preserved. -/
abbrev A : Fin 29 := 25
/-- The loop end `A + 1`. -/
abbrev lim : Fin 29 := 26
/-- `1` while every test so far has passed. -/
abbrev ok : Fin 29 := 27
/-- Constant one. -/
abbrev c1 : Fin 29 := 28

/-- The test for one `a` runs on the first `25` registers. -/
def congMap : Fin 25 → Fin 29 := Fin.castLE (by norm_num)

theorem congMap_injective : congMap.Injective := Fin.castLE_injective _

/-- The test for one `a`. -/
def cong : Code .standard 29 := Congruence.program.rename congMap

/-- Test `a`, record a failure, and advance `a`. -/
def body : Code .standard 29 :=
  .seq cong (ram[ if flag = c1 then [ ok ← ok ] else [ ok ← #0 ]; av ← av + c1 ])

/-- Test `a = 1, …, A`. -/
def program : Code .standard 29 :=
  .seq (ram[ c1 ← #1; lim ← A + c1; av ← c1; ok ← #1 ]) (.loop (.lt av lim) body)

/-- The instruction bound of `program`. -/
def time (r n A : ℕ) : ℕ := A * (Congruence.time r n + 6) + 6

/-- The registers that the test for one `a` preserves. -/
def Keep (j : Fin 29) : Prop :=
  j = R ∨ j = B ∨ j = T ∨ j = rr ∨ j = nn ∨ j = av ∨ j = A ∨ j = lim ∨ j = ok ∨ j = c1

instance : DecidablePred Keep := fun _ => by unfold Keep; infer_instance

private theorem cong_preserves : ∀ j, Keep j → cong.Preserves j := by decide

private theorem cong_exec {w : ℕ} (x : Data 29) {a b t r n v : ℕ} (ha : x.regs R = a)
    (hb : x.regs B = b) (ht : x.regs T = t) (hr : x.regs rr = r) (hn : x.regs nn = n)
    (hv : x.regs av = v) (hr0 : 0 < r) (hn0 : 0 < n) (hab : a + r ≤ b ∨ b + r ≤ a)
    (hta : t + r ≤ a ∨ a + r ≤ t) (htb : t + r ≤ b ∨ b + r ≤ t) (hfa : Fits w (a + r))
    (hfb : Fits w (b + r)) (hft : Fits w (t + r)) (hf2 : Fits w (2 * r))
    (hfn : Fits w (n * n + n)) (hfv : Fits w v) :
    ∃ y, ExecWithin w cong x y (Congruence.time r n) ∧ y.regs flag ≤ 1 ∧
      (y.regs flag = 1 ↔ Congruence n r v) ∧ ∀ j, Keep j → y.regs j = x.regs j := by
  obtain ⟨y, hy, hle, hiff, -⟩ := Congruence.exec (x.comap congMap) ha hb ht hr hn hv hr0 hn0 hab
    hta htb hfa hfb hft hf2 hfn hfv
  have hy' := hy.rename congMap_injective
  have hfl : (y.extend congMap x).regs flag = y.regs Congruence.flag :=
    congMap_injective.extend_apply _ _ Congruence.flag
  exact ⟨_, hy', by rw [hfl]; exact hle, by rw [hfl]; exact hiff,
    fun j hj => hy'.regs_eq (cong_preserves j hj)⟩

/-- **Step 5.** For `r ≥ 1` and `n ≥ 1`, with the three blocks pairwise disjoint and the word size
holding the block ends, `2 r`, `n² + n` and `A + 1`, the program leaves `1` in `ok` exactly when
`(X + a)^n ≡ X^n + a (mod X^r - 1, n)` for every `1 ≤ a ≤ A`, within `time r n A` instructions. -/
theorem exec {w : ℕ} (x : Data 29) {a b t r n A₀ : ℕ} (ha : x.regs R = a) (hb : x.regs B = b)
    (ht : x.regs T = t) (hr : x.regs rr = r) (hn : x.regs nn = n) (hA : x.regs A = A₀)
    (hr0 : 0 < r) (hn0 : 0 < n) (hab : a + r ≤ b ∨ b + r ≤ a) (hta : t + r ≤ a ∨ a + r ≤ t)
    (htb : t + r ≤ b ∨ b + r ≤ t) (hfa : Fits w (a + r)) (hfb : Fits w (b + r))
    (hft : Fits w (t + r)) (hf2 : Fits w (2 * r)) (hfn : Fits w (n * n + n))
    (hfA : Fits w (A₀ + 1)) :
    ∃ y, ExecWithin w program x y (time r n A₀) ∧ y.regs ok ≤ 1 ∧
      (y.regs ok = 1 ↔ ∀ v, 1 ≤ v → v ≤ A₀ → Congruence n r v) ∧
      y.regs R = a ∧ y.regs B = b ∧ y.regs T = t ∧ y.regs rr = r ∧ y.regs nn = n := by
  classical
  have h1 : Fits w 1 := hfA.of_le (by omega)
  let I (y : Data 29) : Prop := y.regs R = a ∧ y.regs B = b ∧ y.regs T = t ∧ y.regs rr = r ∧
    y.regs nn = n ∧ y.regs lim = A₀ + 1 ∧ y.regs c1 = 1 ∧ 1 ≤ y.regs av ∧
    y.regs av ≤ A₀ + 1 ∧ y.regs ok ≤ 1 ∧
    (y.regs ok = 1 ↔ ∀ v, 1 ≤ v → v < y.regs av → Congruence n r v)
  have hstep (y : Data 29) (hy : I y) (hc : (Cond.lt av lim).Holds y) :
      ∃ z, ExecWithin w body y z (Congruence.time r n + 4) ∧ I z ∧
        A₀ + 1 - z.regs av < A₀ + 1 - y.regs av := by
    obtain ⟨hyR, hyB, hyT, hyr, hyn, hyl, hy1, hv1, hvA, hyok, hyiff⟩ := hy
    obtain ⟨V, hV⟩ : ∃ V, y.regs av = V := ⟨_, rfl⟩
    have hVA : V ≤ A₀ := by simp only [Cond.holds_lt, hV, hyl] at hc; omega
    rw [hV] at hv1 hyiff
    obtain ⟨y₁, hrun₁, hle, hiff, hkeep⟩ := cong_exec (w := w) y hyR hyB hyT hyr hyn hV hr0 hn0
      hab hta htb hfa hfb hft hf2 hfn (hfA.of_le (by omega))
    have hk (j : Fin 29) (hj : Keep j) : y₁.regs j = y.regs j := hkeep j hj
    let o := if Congruence n r V then y.regs ok else 0
    let z := (y₁.set ok o).set av (V + 1)
    have hy₁1 : y₁.regs c1 = 1 := by rw [hk c1 (by simp [Keep]), hy1]
    have hy₁ok : y₁.regs ok = y.regs ok := hk ok (by simp [Keep])
    have hy₁v : y₁.regs av = V := by rw [hk av (by simp [Keep]), hV]
    have hfV : Fits w (V + 1) := hfA.of_le (by omega)
    have hrun₂ : ExecWithin (B := .standard) w
        (ram[ if flag = c1 then [ ok ← ok ] else [ ok ← #0 ]; av ← av + c1 ]) y₁ z 4 := by
      by_cases hC : Congruence n r V
      · have hf1 : y₁.regs flag = 1 := hiff.mpr hC
        refine ExecWithin.mono (T := 3) ?_ (by omega)
        ram_eval [z, o, hC, hf1, hy₁1, hy₁ok, hy₁v, hfV]
      · have hf1 : ¬ y₁.regs flag = 1 := fun h => hC (hiff.mp h)
        ram_eval [z, o, hC, hf1, hy₁1, hy₁v, hfV]
    have hz (j : Fin 29) (hj : Keep j) (hjo : j ≠ ok) (hjv : j ≠ av) : z.regs j = y.regs j := by
      simp only [z, Data.set_regs, Function.update_of_ne hjv, Function.update_of_ne hjo]
      exact hk j hj
    have hzv : z.regs av = V + 1 := by simp [z]
    have hzo : z.regs ok = o := by simp +decide [z]
    refine ⟨z, hrun₁.seq hrun₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hz R (by simp [Keep]) (by decide) (by decide), hyR]
    · rw [hz B (by simp [Keep]) (by decide) (by decide), hyB]
    · rw [hz T (by simp [Keep]) (by decide) (by decide), hyT]
    · rw [hz rr (by simp [Keep]) (by decide) (by decide), hyr]
    · rw [hz nn (by simp [Keep]) (by decide) (by decide), hyn]
    · rw [hz lim (by simp [Keep]) (by decide) (by decide), hyl]
    · rw [hz c1 (by simp [Keep]) (by decide) (by decide), hy1]
    · rw [hzv]; omega
    · rw [hzv]; omega
    · rw [hzo]; simp only [o]; split_ifs <;> omega
    · rw [hzo, hzv]
      simp only [o]
      constructor
      · intro h v hv1' hv
        split_ifs at h with hC
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
        · exact hyiff.mp h v hv1' hv
        · exact hC
      · intro h
        have hC : Congruence n r V := h V hv1 (by omega)
        simp only [hC, ↓reduceIte]
        exact hyiff.mpr fun v hv1' hv => h v hv1' (by omega)
    · rw [hzv, hV]; omega
  let x₀ := (((x.set c1 1).set lim (A₀ + 1)).set av 1).set ok 1
  have hrun₀ : ExecWithin (B := .standard) w (ram[ c1 ← #1; lim ← A + c1; av ← c1; ok ← #1 ])
      x x₀ 4 := by
    ram_eval [x₀, hA, h1, hfA]
  have hx₀ : I x₀ := by
    refine ⟨by simp +decide [x₀, ha], by simp +decide [x₀, hb], by simp +decide [x₀, ht],
      by simp +decide [x₀, hr], by simp +decide [x₀, hn], by simp +decide [x₀],
      by simp +decide [x₀], by simp +decide [x₀], by simp +decide [x₀], by simp +decide [x₀], ?_⟩
    have hv : x₀.regs av = 1 := by simp +decide [x₀]
    have ho : x₀.regs ok = 1 := by simp +decide [x₀]
    rw [hv, ho]
    exact ⟨fun _ v hv1 hv => by omega, fun _ => rfl⟩
  obtain ⟨y, hrun, hy, hc⟩ := ExecWithin.loop_invariant I (fun y => A₀ + 1 - y.regs av) hstep hx₀
  obtain ⟨hyR, hyB, hyT, hyr, hyn, hyl, -, -, hvA, hyok, hyiff⟩ := hy
  have hend : y.regs av = A₀ + 1 := by simp only [Cond.holds_lt, hyl] at hc; omega
  refine ⟨y, (hrun₀.seq hrun).mono ?_, hyok, ?_, hyR, hyB, hyT, hyr, hyn⟩
  · have hv : x₀.regs av = 1 := by simp +decide [x₀]
    rw [hv, show A₀ + 1 - 1 = A₀ by omega, show Congruence.time r n + 4 + 2 =
      Congruence.time r n + 6 by ring]
    unfold time
    omega
  · rw [hyiff, hend]
    exact ⟨fun h v hv1 hv => h v hv1 (by omega), fun h v hv1 hv => h v hv1 (by omega)⟩

end Cslib.Algorithms.WordRAM.AKS.CongruenceLoop

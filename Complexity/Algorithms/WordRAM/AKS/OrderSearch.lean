/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.NatGcd
public import Complexity.Computability.WordRAM.RegisterFrame
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# The search for `r` in the AKS algorithm on the word RAM

Step 2 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] finds the least `r` such
that the multiplicative order of `n` modulo `r` exceeds a bound `L`. As in the proof of their
Theorem 5.1, the program tries `r = 2, 3, …` in turn. It accepts `r` when `gcd(n, r) = 1` and
`n^k mod r ≠ 1` for every `1 ≤ k ≤ L`; for `r ≥ 2` this is the order condition
(`Cslib.AKS.lt_orderOf_iff`). The powers are computed by one multiplication modulo `r` each, and
the gcd by Euclid's algorithm (`Cslib.Algorithms.WordRAM.NatGcd.program`). Given any `r₀ ≥ 2`
satisfying the condition, the search stops at some `2 ≤ r ≤ r₀` satisfying it, within a number of
instructions polynomial in `r₀` and `L`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.OrderSearch.Good`: the condition tested for one `r`.
* `Cslib.Algorithms.WordRAM.AKS.OrderSearch.program`: the search.
* `Cslib.Algorithms.WordRAM.AKS.OrderSearch.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.OrderSearch.exec`: the search stops at an `r ≤ r₀` satisfying the
  condition, within `time L r₀` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.OrderSearch

open Cslib.WordRAM

/-- The condition tested for `r`: `n` is coprime to `r` and no `n^k` with `1 ≤ k ≤ L` is `1`
modulo `r`. -/
def Good (n L r : ℕ) : Prop := n.Coprime r ∧ ∀ k, 1 ≤ k → k ≤ L → n ^ k % r ≠ 1

/-- The number `n`, preserved. -/
abbrev n : Fin 13 := 0
/-- The bound `L` on the order, preserved. -/
abbrev L : Fin 13 := 1
/-- The candidate `r`, and the output. -/
abbrev r : Fin 13 := 2
/-- `1` once a candidate is accepted. -/
abbrev found : Fin 13 := 3
/-- Constant one. -/
abbrev one : Fin 13 := 4
/-- `n mod r`. -/
abbrev nr : Fin 13 := 5
/-- The power `n^k mod r`. -/
abbrev p : Fin 13 := 6
/-- The exponent `k`. -/
abbrev k : Fin 13 := 7
/-- `1` while no power `n^j` with `1 ≤ j ≤ k` is `1` modulo `r`. -/
abbrev ok : Fin 13 := 8
/-- First argument of the gcd, and its result. -/
abbrev ga : Fin 13 := 9
/-- Second argument of the gcd. -/
abbrev gb : Fin 13 := 10

/-- Euclid's algorithm runs on `ga`, `gb` and two scratch registers. -/
def gcdMap : Fin 4 → Fin 13 := ![ga, gb, 11, 12]

theorem gcdMap_injective : gcdMap.Injective := by decide

/-- One more power: `p := p · (n mod r) mod r`, and record whether it is `1`. -/
def powBody : Code .standard 13 := ram[
  p ← p * nr; p ← p % r; k ← k + one; if p = one then [ ok ← #0 ] else [ ok ← ok ] ]

/-- Test the powers `n^k mod r` for `1 ≤ k ≤ L`. -/
def powers : Code .standard 13 :=
  .seq (ram[ nr ← n % r; p ← one; k ← #0; ok ← #1 ]) (.loop (.lt k L) powBody)

/-- Accept `r` if `gcd(n, r) = 1` and no small power is `1`; otherwise try `r + 1`. -/
def accept : Code .standard 13 := ram[
  if ga = one then [ if ok = one then [ found ← #1 ] else [ r ← r + one ] ] else [ r ← r + one ] ]

/-- Test one candidate. -/
def body : Code .standard 13 :=
  .seq powers (.seq (ram[ ga ← n; gb ← r ]) (.seq (NatGcd.program.rename gcdMap) accept))

/-- Try `r = 2, 3, …` until one is accepted. -/
def program : Code .standard 13 :=
  .seq (ram[ one ← #1; r ← #2; found ← #0 ]) (.loop (.lt found one) body)

/-- The instruction bound of `program`. -/
def time (L r₀ : ℕ) : ℕ := (2 * r₀ + 1) * (8 * L + 5 * r₀ + 20) + 5

/-- The registers that the power test preserves. -/
private theorem powers_preserves :
    ∀ j ∈ [n, L, r, found, one], powers.Preserves j := by decide

private theorem powers_exec {w : ℕ} (x : Data 13) {N L₀ R : ℕ} (hn : x.regs n = N)
    (hL : x.regs L = L₀) (hr : x.regs r = R) (h1 : x.regs one = 1) (hR : 2 ≤ R)
    (hfN : Fits w N) (hfR : Fits w (R * R)) (hfL : Fits w (L₀ + 1)) :
    ∃ y, ExecWithin w powers x y (8 * L₀ + 6) ∧ y.regs ok ≤ 1 ∧
      (y.regs ok = 1 ↔ ∀ j, 1 ≤ j → j ≤ L₀ → N ^ j % R ≠ 1) ∧
      ∀ j ∈ [n, L, r, found, one], y.regs j = x.regs j := by
  have hR0 : 0 < R := by omega
  have h1f : Fits w 1 := hfL.of_le (by omega)
  let J (y : Data 13) : Prop := y.regs L = L₀ ∧ y.regs r = R ∧ y.regs one = 1 ∧
    y.regs nr = N % R ∧ y.regs k ≤ L₀ ∧ y.regs p = N ^ y.regs k % R ∧ y.regs ok ≤ 1 ∧
    (y.regs ok = 1 ↔ ∀ j, 1 ≤ j → j ≤ y.regs k → N ^ j % R ≠ 1)
  have hstep (y : Data 13) (hy : J y) (hc : (Cond.lt k L).Holds y) :
      ∃ z, ExecWithin w powBody y z 6 ∧ J z ∧ L₀ - z.regs k < L₀ - y.regs k := by
    obtain ⟨hyL, hyr, hy1, hynr, hyk, hyp, hyok, hyiff⟩ := hy
    obtain ⟨K, hK⟩ : ∃ K, y.regs k = K := ⟨_, rfl⟩
    have hKL : K < L₀ := by simpa only [Cond.holds_lt, hK, hyL] using hc
    rw [hK] at hyp hyiff
    have hPR : N ^ K % R < R := Nat.mod_lt _ hR0
    have hNR : N % R < R := Nat.mod_lt _ hR0
    have hmul : N ^ K % R * (N % R) < R * R := Nat.mul_lt_mul'' hPR hNR
    have hmod : N ^ K % R * (N % R) % R = N ^ (K + 1) % R := by
      rw [← Nat.mul_mod, pow_succ]
    have hf₁ : Fits w (N ^ K % R * (N % R)) := hfR.of_le hmul.le
    have hf₂ : Fits w (N ^ (K + 1) % R) := hfR.of_le
      ((Nat.mod_lt _ hR0).le.trans (Nat.le_mul_self R))
    have hf₃ : Fits w (K + 1) := hfL.of_le (by omega)
    have hiff (o : ℕ) : ((∀ j, 1 ≤ j → j ≤ K + 1 → N ^ j % R ≠ 1) ↔
        (∀ j, 1 ≤ j → j ≤ K → N ^ j % R ≠ 1) ∧ N ^ (K + 1) % R ≠ 1) := by
      constructor
      · intro h; exact ⟨fun j hj hjK => h j hj (by omega), h (K + 1) (by omega) le_rfl⟩
      · rintro ⟨h, hK1⟩ j hj hjK
        rcases Nat.lt_or_ge j (K + 1) with hlt | hge
        · exact h j hj (by omega)
        · rw [show j = K + 1 by omega]; exact hK1
    let o := if N ^ (K + 1) % R = 1 then 0 else y.regs ok
    let z := (((y.set p (N ^ K % R * (N % R))).set p (N ^ (K + 1) % R)).set k (K + 1)).set ok o
    have hrun : ExecWithin (B := .standard) w powBody y z 6 := by
      by_cases hP : N ^ (K + 1) % R = 1
      · refine ExecWithin.mono (T := 5) ?_ (by omega)
        ram_eval [powBody, z, o, hyp, hynr, hyr, hK, hy1, hmod, hP, hf₁, hf₂, hf₃, h1f]
      · ram_eval [powBody, z, o, hyp, hynr, hyr, hK, hy1, hmod, hP, hf₁, hf₂, hf₃, h1f]
    have hzk : z.regs k = K + 1 := by simp +decide [z]
    refine ⟨z, hrun, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp +decide [z, hyL]
    · simp +decide [z, hyr]
    · simp +decide [z, hy1]
    · simp +decide [z, hynr]
    · rw [hzk]; omega
    · rw [hzk]; simp +decide [z]
    · simp only [z, o, Data.set_regs, Function.update_self]
      split_ifs <;> omega
    · rw [hzk, hiff 0]
      simp only [z, o, Data.set_regs, Function.update_self]
      split_ifs with hP
      · simp [hP]
      · rw [hyiff]; simp [hP]
    · rw [hzk, hK]; omega
  let x₀ := (((x.set nr (N % R)).set p 1).set k 0).set ok 1
  have hrun₀ : ExecWithin (B := .standard) w (ram[ nr ← n % r; p ← one; k ← #0; ok ← #1 ])
      x x₀ 4 := by
    ram_eval [x₀, hn, hr, h1, h1f, hfN.of_le (Nat.mod_le N R)]
  have hx₀ : J x₀ := by
    have hk : x₀.regs k = 0 := by simp +decide [x₀]
    have hp : x₀.regs p = 1 := by simp +decide [x₀]
    have ho : x₀.regs ok = 1 := by simp +decide [x₀]
    refine ⟨by simp +decide [x₀, hL], by simp +decide [x₀, hr], by simp +decide [x₀, h1],
      by simp +decide [x₀], by rw [hk]; omega, ?_, by rw [ho], ?_⟩
    · rw [hk, hp, pow_zero, Nat.mod_eq_of_lt (by omega : 1 < R)]
    · rw [ho, hk]
      exact ⟨fun _ j hj hj0 => by omega, fun _ => rfl⟩
  obtain ⟨y, hrun, hy, hc⟩ := ExecWithin.loop_invariant J (fun y => L₀ - y.regs k) hstep hx₀
  obtain ⟨hyL, -, -, -, hyk, -, hyok, hyiff⟩ := hy
  have hkL : y.regs k = L₀ := by simp only [Cond.holds_lt, hyL] at hc; omega
  have hrun' := hrun₀.seq hrun
  refine ⟨y, hrun'.mono ?_, hyok, by rw [hyiff, hkL],
    fun j hj => hrun'.regs_eq (powers_preserves j hj)⟩
  have : x₀.regs k = 0 := by simp +decide [x₀]
  rw [this]
  omega

/-- **The search for `r`.** If some `r₀ ≥ 2` satisfies `Good n L r₀`, and the word size holds
`n`, `r₀²` and `L + 1`, the search stops within `time L r₀` instructions at some `2 ≤ r ≤ r₀`
satisfying `Good n L r`, preserving `n` and `L`. -/
theorem exec {w : ℕ} (x : Data 13) {N L₀ r₀ : ℕ} (hn : x.regs n = N) (hL : x.regs L = L₀)
    (hr₀ : 2 ≤ r₀) (hgood : Good N L₀ r₀) (hfN : Fits w N) (hfR : Fits w (r₀ * r₀))
    (hfL : Fits w (L₀ + 1)) :
    ∃ y, ExecWithin w program x y (time L₀ r₀) ∧ 2 ≤ y.regs r ∧ y.regs r ≤ r₀ ∧
      Good N L₀ (y.regs r) ∧ y.regs n = N ∧ y.regs L = L₀ := by
  have h1f : Fits w 1 := hfL.of_le (by omega)
  have hfr₁ : Fits w (r₀ + 1) := hfR.of_le (by nlinarith)
  let I (y : Data 13) : Prop := y.regs n = N ∧ y.regs L = L₀ ∧ y.regs one = 1 ∧ 2 ≤ y.regs r ∧
    y.regs r ≤ r₀ ∧ y.regs found ≤ 1 ∧ (y.regs found = 1 → Good N L₀ (y.regs r))
  have hstep (y : Data 13) (hy : I y) (hc : (Cond.lt found one).Holds y) :
      ∃ z, ExecWithin w body y z (8 * L₀ + 5 * r₀ + 16) ∧ I z ∧
        2 * (r₀ - z.regs r) + (1 - z.regs found) < 2 * (r₀ - y.regs r) + (1 - y.regs found) := by
    obtain ⟨hyn, hyL, hy1, hr2, hrr₀, hyf, -⟩ := hy
    obtain ⟨R, hR⟩ : ∃ R, y.regs r = R := ⟨_, rfl⟩
    rw [hR] at hr2 hrr₀
    have hf0 : y.regs found = 0 := by simp only [Cond.holds_lt, hy1] at hc; omega
    -- The powers.
    obtain ⟨y₁, hrun₁, hok1, hokiff, hy₁⟩ := powers_exec (w := w) y hyn hyL hR hy1 hr2 hfN
      (hfR.of_le (Nat.mul_le_mul hrr₀ hrr₀)) hfL
    have hy₁n : y₁.regs n = N := by rw [hy₁ n (by simp), hyn]
    have hy₁r : y₁.regs r = R := by rw [hy₁ r (by simp), hR]
    -- The gcd.
    let y₂ := (y₁.set ga N).set gb R
    have hrun₂ : ExecWithin (B := .standard) w (ram[ ga ← n; gb ← r ]) y₁ y₂ 2 := by
      ram_eval [y₂, hy₁n, hy₁r]
    obtain ⟨y₃, hrun₃, hg, -⟩ := NatGcd.exec_rename gcdMap gcdMap_injective y₂
      (by simpa +decide [y₂, gcdMap] using hfN)
      (by simpa +decide [y₂, gcdMap] using hfR.of_le (hrr₀.trans (Nat.le_mul_self r₀)))
    have hgcd : y₃.regs ga = Nat.gcd N R := by
      rw [show ga = gcdMap NatGcd.a from rfl, hg]; simp +decide [y₂, gcdMap]
    have hy₃ (j : Fin 13) (hj : j.val < 9) : y₃.regs j = y₁.regs j := by
      rw [hrun₃.regs_eq (Code.preserves_rename_of_forall_ne _ _ _ ?_)]
      · have h9 : j ≠ ga ∧ j ≠ gb := by
          constructor <;> (intro h; subst h; simp at hj)
        simp [y₂, h9.1, h9.2]
      · intro a h; subst h; fin_cases a <;> simp [gcdMap] at hj
    have hy₃1 : y₃.regs one = 1 := by rw [hy₃ one (by simp), hy₁ one (by simp), hy1]
    have hy₃r : y₃.regs r = R := by rw [hy₃ r (by simp), hy₁r]
    have hy₃ok : y₃.regs ok = y₁.regs ok := hy₃ ok (by simp)
    -- Accept or advance.
    have hfR1 : Fits w (R + 1) := hfr₁.of_le (by omega)
    have hgood' : Good N L₀ R ↔ Nat.gcd N R = 1 ∧ y₁.regs ok = 1 := by
      rw [hokiff]; rfl
    by_cases hG : Good N L₀ R
    · obtain ⟨hg1, ho1⟩ := hgood'.mp hG
      let z := y₃.set found 1
      have hrun₄ : ExecWithin (B := .standard) w accept y₃ z 5 := by
        refine ExecWithin.mono (T := 3) ?_ (by omega)
        ram_eval [accept, z, hgcd, hg1, hy₃1, hy₃ok, ho1, h1f]
      refine ⟨z, (hrun₁.seq (hrun₂.seq (hrun₃.seq hrun₄))).mono ?_, ?_, ?_⟩
      · rw [show y₂.regs (gcdMap NatGcd.b) = R by simp +decide [y₂, gcdMap]]
        omega
      · have hz (j : Fin 13) (hj : j ≠ found) : z.regs j = y₃.regs j := by simp [z, hj]
        have hzr : z.regs r = R := by rw [hz r (by decide), hy₃r]
        refine ⟨?_, ?_, ?_, by rw [hzr]; exact hr2, by rw [hzr]; exact hrr₀,
          by simp +decide [z], fun _ => by rw [hzr]; exact hG⟩
        · rw [hz n (by decide), hy₃ n (by simp), hy₁n]
        · rw [hz L (by decide), hy₃ L (by simp), hy₁ L (by simp), hyL]
        · rw [hz one (by decide), hy₃1]
      · simp +decide [z, hy₃r, hR, hf0]
    · have hne : R ≠ r₀ := fun h => hG (h ▸ hgood)
      let z := y₃.set r (R + 1)
      have hrun₄ : ExecWithin (B := .standard) w accept y₃ z 5 := by
        by_cases hg1 : Nat.gcd N R = 1
        · have ho1 : ¬ y₁.regs ok = 1 := fun h => hG (hgood'.mpr ⟨hg1, h⟩)
          ram_eval [accept, z, hgcd, hg1, hy₃1, hy₃ok, ho1, hy₃r, hfR1]
        · refine ExecWithin.mono (T := 3) ?_ (by omega)
          ram_eval [accept, z, hgcd, hg1, hy₃1, hy₃r, hfR1]
      refine ⟨z, (hrun₁.seq (hrun₂.seq (hrun₃.seq hrun₄))).mono ?_, ?_, ?_⟩
      · rw [show y₂.regs (gcdMap NatGcd.b) = R by simp +decide [y₂, gcdMap]]
        omega
      · have hf : z.regs found = 0 := by
          simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte]
          rw [hy₃ found (by simp), hy₁ found (by simp), hf0]
        have hz (j : Fin 13) (hj : j ≠ r) : z.regs j = y₃.regs j := by simp [z, hj]
        have hzr : z.regs r = R + 1 := by simp [z]
        refine ⟨?_, ?_, ?_, by rw [hzr]; omega, by rw [hzr]; omega, by omega, by omega⟩
        · rw [hz n (by decide), hy₃ n (by simp), hy₁n]
        · rw [hz L (by decide), hy₃ L (by simp), hy₁ L (by simp), hyL]
        · rw [hz one (by decide), hy₃1]
      · have hf : z.regs found = 0 := by
          simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte]
          rw [hy₃ found (by simp), hy₁ found (by simp), hf0]
        rw [hf, hf0, hR, show z.regs r = R + 1 by simp [z]]
        omega
  let x₀ := ((x.set one 1).set r 2).set found 0
  have hrun₀ : ExecWithin (B := .standard) w (ram[ one ← #1; r ← #2; found ← #0 ]) x x₀ 3 := by
    ram_eval [x₀, h1f, hfr₁.of_le (by omega : 2 ≤ r₀ + 1)]
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp +decide [x₀, hn, hL, hr₀]
  obtain ⟨y, hrun, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => 2 * (r₀ - y.regs r) + (1 - y.regs found)) hstep hx₀
  obtain ⟨hyn, hyL, hy1, hr2, hrr₀, hyf1, hgoody⟩ := hy
  have hf1 : y.regs found = 1 := by simp only [Cond.holds_lt, hy1] at hc; omega
  refine ⟨y, (hrun₀.seq hrun).mono ?_, hr2, hrr₀, hgoody hf1, hyn, hyL⟩
  have hx₀r : x₀.regs r = 2 := by simp +decide [x₀]
  have hx₀f : x₀.regs found = 0 := by simp +decide [x₀]
  have hμ : 2 * (r₀ - x₀.regs r) + (1 - x₀.regs found) ≤ 2 * r₀ + 1 := by omega
  have := Nat.mul_le_mul hμ (le_refl (8 * L₀ + 5 * r₀ + 16 + 2))
  unfold time
  nlinarith

end Cslib.Algorithms.WordRAM.AKS.OrderSearch

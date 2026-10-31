/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Foundations.NumberTheory.AKS.Coefficients

/-!
# Writing and comparing coefficient arrays on the word RAM

Two linear-time array routines for polynomials modulo `X^r - 1` and `n`, stored as `r` words:
`Fill` writes the coefficients `Cslib.AKS.powAddCoeff n r e a` of `X^e + a` (it clears the block
and then adds `a` at index `0` and `1` at index `e mod r`), and `Compare` tests two blocks for
equality.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.Fill.program`: write the coefficients of `X^e + a`.
* `Cslib.Algorithms.WordRAM.AKS.Compare.program`: compare two blocks.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.Fill.exec`: the block receives `Cslib.AKS.powAddCoeff` within
  `5 r + 13` instructions, and no other cell changes.
* `Cslib.Algorithms.WordRAM.AKS.Compare.exec`: the flag is `1` exactly when the blocks agree,
  within `11 r + 5` instructions, and memory is unchanged.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS

open Cslib.WordRAM

namespace Fill

/-- Base address of the block. -/
abbrev base : Fin 10 := 0
/-- The number `r` of coefficients. -/
abbrev rr : Fin 10 := 1
/-- The modulus `n`. -/
abbrev nn : Fin 10 := 2
/-- The index `e mod r` of the monomial. -/
abbrev er : Fin 10 := 3
/-- The constant term `a`. -/
abbrev aa : Fin 10 := 4
/-- Loop index. -/
abbrev i : Fin 10 := 5
/-- Address scratch. -/
abbrev addr : Fin 10 := 6
/-- Value scratch. -/
abbrev t : Fin 10 := 7
/-- Constant one. -/
abbrev one : Fin 10 := 8
/-- Constant zero. -/
abbrev zero : Fin 10 := 9

/-- Clear one cell. -/
def clearBody : Code .standard 10 := ram[ addr ← base + i; *addr ← zero; i ← i + one ]

/-- Store `a mod n` at index `0`. -/
def storeConst : Code .standard 10 := ram[ t ← aa % nn; *base ← t ]

/-- Add `1` at index `e mod r`, modulo `n`. -/
def addMonomial : Code .standard 10 := ram[
  addr ← base + er; t ← *addr; t ← t + one; t ← t % nn; *addr ← t ]

/-- Store `a mod n` at index `0`, then add `1` at index `e mod r`. -/
def finish : Code .standard 10 := .seq storeConst addMonomial

/-- Clear the block, then write the two nonzero coefficients. -/
def program : Code .standard 10 :=
  .seq (ram[ one ← #1; zero ← #0; i ← #0 ]) (.seq (.loop (.lt i rr) clearBody) finish)

private theorem clear_step {w b r : ℕ} {m : ℕ → ℕ} (hfb : Fits w (b + r)) (y : Data 10)
    (hy : y.regs base = b ∧ y.regs rr = r ∧ y.regs one = 1 ∧ y.regs zero = 0 ∧ y.regs i ≤ r ∧
      ∀ a', y.mem a' = if b ≤ a' ∧ a' < b + y.regs i then 0 else m a')
    (hc : (Cond.lt i rr).Holds y) :
    ∃ z, ExecWithin w clearBody y z 3 ∧
      (z.regs base = b ∧ z.regs rr = r ∧ z.regs one = 1 ∧ z.regs zero = 0 ∧ z.regs i ≤ r ∧
        ∀ a', z.mem a' = if b ≤ a' ∧ a' < b + z.regs i then 0 else m a') ∧
      r - z.regs i < r - y.regs i := by
  obtain ⟨hyb, hyr, hyo, hyz, hyi, hym⟩ := hy
  obtain ⟨I, hI⟩ : ∃ I, y.regs i = I := ⟨_, rfl⟩
  have hlt : I < r := by simpa only [Cond.holds_lt, hyr, hI] using hc
  have hf₁ : Fits w (b + I) := hfb.of_le (by omega)
  have hf₂ : Fits w (I + 1) := hfb.of_le (by omega)
  let z := ((y.set addr (b + I)).write (b + I) 0).set i (I + 1)
  have hrun : ExecWithin (B := .standard) w clearBody y z 3 := by
    ram_eval [clearBody, z, hyb, hI, hyo, hyz, hf₁, hf₂]
  refine ⟨z, hrun, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp +decide [z, hyb]
  · simp +decide [z, hyr]
  · simp +decide [z, hyo]
  · simp +decide [z, hyz]
  · simp only [z, Data.set_regs, Function.update_self]; omega
  · intro a'
    simp only [z, Data.set_mem, Data.write_mem, Data.set_regs, Function.update_self,
      Function.update_apply, hym, hI]
    split_ifs <;> first | rfl | omega
  · simp only [z, Data.set_regs, Function.update_self, hI]; omega

/-- **Writing `X^e + a`.** For `r ≥ 1` and `n ≥ 1`, with `e mod r` in `er` and the block end,
`a`, `n` and `n + 1` fitting a word, the block `[b, b + r)` receives the coefficients
`Cslib.AKS.powAddCoeff n r e a` within `5 r + 13` instructions, and no other cell changes. -/
theorem exec {w : ℕ} (x : Data 10) {b r n e a : ℕ} (hb : x.regs base = b) (hr : x.regs rr = r)
    (hn : x.regs nn = n) (her : x.regs er = e % r) (ha : x.regs aa = a) (hr0 : 0 < r)
    (hn0 : 0 < n) (hfb : Fits w (b + r)) (hfa : Fits w a) (hfn : Fits w (n + 1)) :
    ∃ y, ExecWithin w program x y (5 * r + 13) ∧
      (∀ k < r, y.mem (b + k) = Cslib.AKS.powAddCoeff n r e a k) ∧
      (∀ a', ¬(b ≤ a' ∧ a' < b + r) → y.mem a' = x.mem a') ∧
      y.regs base = b ∧ y.regs rr = r ∧ y.regs nn = n := by
  have h1 : Fits w 1 := hfn.of_le (by omega)
  let x₀ := ((x.set one 1).set zero 0).set i 0
  have hrun₀ : ExecWithin (B := .standard) w (ram[ one ← #1; zero ← #0; i ← #0 ]) x x₀ 3 := by
    ram_eval [x₀, h1]
  have hx₀ : x₀.regs base = b ∧ x₀.regs rr = r ∧ x₀.regs one = 1 ∧ x₀.regs zero = 0 ∧
      x₀.regs i ≤ r ∧ ∀ a', x₀.mem a' = if b ≤ a' ∧ a' < b + x₀.regs i then 0 else x.mem a' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun a' => ?_⟩
    · simp +decide [x₀, hb]
    · simp +decide [x₀, hr]
    · simp +decide [x₀]
    · simp +decide [x₀]
    · simp +decide [x₀]
    · simp only [x₀, Data.set_mem, Data.set_regs, Function.update_self]
      split_ifs <;> first | rfl | omega
  obtain ⟨y, hrun₁, ⟨hyb, hyr, hyo, -, hyi, hym⟩, hc⟩ := ExecWithin.loop_invariant _
    (fun y => r - y.regs i) (clear_step hfb) hx₀
  have hir : y.regs i = r := by simp only [Cond.holds_lt, hyr] at hc; omega
  rw [hir] at hym
  -- The two nonzero coefficients.
  have hyn : y.regs nn = n := by
    rw [hrun₁.regs_eq (by decide), show x₀.regs nn = x.regs nn by simp +decide [x₀], hn]
  have hya : y.regs aa = a := by
    rw [hrun₁.regs_eq (by decide), show x₀.regs aa = x.regs aa by simp +decide [x₀], ha]
  have hye : y.regs er = e % r := by
    rw [hrun₁.regs_eq (by decide), show x₀.regs er = x.regs er by simp +decide [x₀], her]
  have her' : e % r < r := Nat.mod_lt _ hr0
  have hamod : a % n < n := Nat.mod_lt _ hn0
  have hf₁ : Fits w (a % n) := hfa.of_le (Nat.mod_le _ _)
  have hf₂ : Fits w (b + e % r) := hfb.of_le (by omega)
  -- The cell at `e mod r` after the first store.
  obtain ⟨c, hc⟩ : ∃ c, c = if e % r = 0 then a % n else 0 := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', (y.set t (a % n)).write b (a % n) = y' := ⟨_, rfl⟩
  have hrun₂ : ExecWithin (B := .standard) w storeConst y y' 2 := by
    rw [← hy']; ram_eval [storeConst, hya, hyn, hyb, hf₁]
  have hy'b : y'.regs base = b := by rw [← hy']; simp +decide [hyb]
  have hy'e : y'.regs er = e % r := by rw [← hy']; simp +decide [hye]
  have hy'o : y'.regs one = 1 := by rw [← hy']; simp +decide [hyo]
  have hy'n : y'.regs nn = n := by rw [← hy']; simp +decide [hyn]
  have hy'r : y'.regs rr = r := by rw [← hy']; simp +decide [hyr]
  have hy'm : y'.mem = Function.update y.mem b (a % n) := by rw [← hy']; rfl
  have hcell : y'.mem (b + e % r) = c := by
    rw [hy'm]
    by_cases h : e % r = 0
    · simp [hc, h]
    · rw [Function.update_of_ne (by omega), hym]
      simp [hc, h, show b + e % r < b + r by omega]
  have hcn : c < n := by rw [hc]; split_ifs <;> omega
  have hf₃ : Fits w (c + 1) := hfn.of_le (by omega)
  have hf₄ : Fits w ((c + 1) % n) := hfn.of_le (by have := Nat.mod_lt (c + 1) hn0; omega)
  let z := ((((y'.set addr (b + e % r)).set t c).set t (c + 1)).set t ((c + 1) % n)).write
    (b + e % r) ((c + 1) % n)
  have hrun₃ : ExecWithin (B := .standard) w addMonomial y' z 5 := by
    ram_eval [addMonomial, z, hy'b, hy'e, hy'o, hy'n, hcell, hf₂, hf₃, hf₄]
  refine ⟨z, (hrun₀.seq (hrun₁.seq (hrun₂.seq hrun₃))).mono ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : x₀.regs i = 0 := by simp +decide [x₀]
    rw [this]; omega
  · intro k hk
    simp only [z, Data.write_mem, Data.set_mem]
    by_cases hke : k = e % r
    · subst hke
      rw [Function.update_self]
      simp only [Cslib.AKS.powAddCoeff, ↓reduceIte, hc]
      split_ifs with h0
      · rw [Nat.mod_add_mod, Nat.add_comm]
      · simp
    · rw [Function.update_of_ne (by omega), hy'm]
      by_cases hk0 : k = 0
      · subst hk0
        simp only [Nat.add_zero, Function.update_self, Cslib.AKS.powAddCoeff, hke, ↓reduceIte,
          Nat.zero_add]
      · rw [Function.update_of_ne (by omega), hym]
        simp [Cslib.AKS.powAddCoeff, hke, hk0, show b + k < b + r by omega]
  · intro a' ha'
    simp only [z, Data.write_mem, Data.set_mem]
    rw [Function.update_of_ne (by omega), hy'm, Function.update_of_ne (by omega), hym]
    simp [ha']
  · simp +decide [z, hy'b]
  · simp +decide [z, hy'r]
  · simp +decide [z, hy'n]

end Fill

namespace Compare

/-- Base address of the first block. -/
abbrev p : Fin 9 := 0
/-- Base address of the second block. -/
abbrev q : Fin 9 := 1
/-- The number `r` of coefficients. -/
abbrev rr : Fin 9 := 2
/-- Loop index. -/
abbrev k : Fin 9 := 3
/-- Address scratch. -/
abbrev addr : Fin 9 := 4
/-- Coefficient of the first block. -/
abbrev u : Fin 9 := 5
/-- Coefficient of the second block. -/
abbrev v : Fin 9 := 6
/-- The answer: `1` when the blocks agree. -/
abbrev flag : Fin 9 := 7
/-- Constant one. -/
abbrev one : Fin 9 := 8

/-- Compare one pair of coefficients. -/
def body : Code .standard 9 := ram[
  addr ← p + k; u ← *addr; addr ← q + k; v ← *addr;
  if u = v then [ flag ← flag ] else [ flag ← #0 ]; k ← k + one ]

/-- Compare two blocks of `r` words. -/
def program : Code .standard 9 :=
  .seq (ram[ flag ← #1; one ← #1; k ← #0 ]) (.loop (.lt k rr) body)

private theorem step {w a b r : ℕ} {m : ℕ → ℕ} (hfa : Fits w (a + r)) (hfb : Fits w (b + r))
    (y : Data 9)
    (hy : y.regs p = a ∧ y.regs q = b ∧ y.regs rr = r ∧ y.regs one = 1 ∧ y.regs k ≤ r ∧
      y.mem = m ∧ (y.regs flag = if ∀ k' < y.regs k, m (a + k') = m (b + k') then 1 else 0))
    (hc : (Cond.lt k rr).Holds y) :
    ∃ z, ExecWithin w body y z 9 ∧
      (z.regs p = a ∧ z.regs q = b ∧ z.regs rr = r ∧ z.regs one = 1 ∧ z.regs k ≤ r ∧
        z.mem = m ∧ (z.regs flag = if ∀ k' < z.regs k, m (a + k') = m (b + k') then 1 else 0)) ∧
      r - z.regs k < r - y.regs k := by
  classical
  obtain ⟨hya, hyb, hyr, hyo, hyk, hym, hyf⟩ := hy
  obtain ⟨K, hK⟩ : ∃ K, y.regs k = K := ⟨_, rfl⟩
  have hlt : K < r := by simpa only [Cond.holds_lt, hyr, hK] using hc
  rw [hK] at hyf
  have hf₁ : Fits w (a + K) := hfa.of_le (by omega)
  have hf₂ : Fits w (b + K) := hfb.of_le (by omega)
  have hf₃ : Fits w (K + 1) := hfa.of_le (by omega)
  have hiff : (∀ k' < K + 1, m (a + k') = m (b + k')) ↔
      (∀ k' < K, m (a + k') = m (b + k')) ∧ m (a + K) = m (b + K) := by
    constructor
    · intro h; exact ⟨fun k' hk' => h k' (by omega), h K (by omega)⟩
    · rintro ⟨h, hK'⟩ k' hk'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
      · exact h k' hk'
      · exact hK'
  let f := if m (a + K) = m (b + K) then y.regs flag else 0
  let z := ((((((y.set addr (a + K)).set u (m (a + K))).set addr (b + K)).set v
    (m (b + K))).set flag f).set k (K + 1))
  have hrun : ExecWithin (B := .standard) w body y z 9 := by
    by_cases heq : m (a + K) = m (b + K)
    · refine ExecWithin.mono (T := 8) ?_ (by omega)
      ram_eval [body, z, f, hya, hyb, hK, hyo, hym, heq, hf₁, hf₂, hf₃]
    · ram_eval [body, z, f, hya, hyb, hK, hyo, hym, heq, hf₁, hf₂, hf₃]
  refine ⟨z, hrun, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp +decide [z, hya]
  · simp +decide [z, hyb]
  · simp +decide [z, hyr]
  · simp +decide [z, hyo]
  · simp +decide [z]; omega
  · simp +decide [z, hym]
  · simp only [z, f, Data.set_regs, Function.update_self]
    rw [Function.update_of_ne (by decide), Function.update_self]
    simp only [hiff]
    by_cases heq : m (a + K) = m (b + K) <;> simp [heq, hyf]
  · simp +decide [z, hK]; omega

/-- **Comparing blocks.** With both block ends fitting a word, the program leaves `1` in `flag`
exactly when the blocks `[a, a + r)` and `[b, b + r)` agree, and `0` otherwise, within
`11 r + 5` instructions, without changing memory. -/
theorem exec {w : ℕ} (x : Data 9) {a b r : ℕ} (ha : x.regs p = a) (hb : x.regs q = b)
    (hr : x.regs rr = r) (hfa : Fits w (a + r)) (hfb : Fits w (b + r)) (h1 : Fits w 1) :
    ∃ y, ExecWithin w program x y (11 * r + 5) ∧ y.regs flag ≤ 1 ∧
      (y.regs flag = 1 ↔ ∀ k' < r, x.mem (a + k') = x.mem (b + k')) ∧ y.mem = x.mem := by
  classical
  let x₀ := ((x.set flag 1).set one 1).set k 0
  have hrun₀ : ExecWithin (B := .standard) w (ram[ flag ← #1; one ← #1; k ← #0 ]) x x₀ 3 := by
    ram_eval [x₀, h1]
  have hx₀ : x₀.regs p = a ∧ x₀.regs q = b ∧ x₀.regs rr = r ∧ x₀.regs one = 1 ∧
      x₀.regs k ≤ r ∧ x₀.mem = x.mem ∧
      (x₀.regs flag = if ∀ k' < x₀.regs k, x.mem (a + k') = x.mem (b + k') then 1 else 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩ <;> simp +decide [x₀, ha, hb, hr]
  obtain ⟨y, hrun₁, ⟨-, -, hyr, -, hyk, hym, hyf⟩, hc⟩ := ExecWithin.loop_invariant _
    (fun y => r - y.regs k) (step hfa hfb) hx₀
  have hkr : y.regs k = r := by simp only [Cond.holds_lt, hyr] at hc; omega
  rw [hkr] at hyf
  refine ⟨y, (hrun₀.seq hrun₁).mono ?_, ?_, ?_, hym⟩
  · have : x₀.regs k = 0 := by simp +decide [x₀]
    rw [this]; omega
  · rw [hyf]; split_ifs <;> omega
  · rw [hyf]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => rfl⟩
    · exact ⟨fun h' => by simp at h', fun h' => absurd h' h⟩

end Compare

end Cslib.Algorithms.WordRAM.AKS

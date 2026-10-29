/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Bounds

/-!
# Every-wide-width initialized callable product

The width threshold depends only on original row/occurrence counts and the length/word bound of
the protected caller prefix. The actual program never reads physical width. Generic execution
does not assume query sparsity; only the final quantitative saving does.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Positive logarithmic physical width derived entirely from original input and caller data. -/
@[expose] def admissionWidth (caller : List ℕ) (N Q P : ℕ) : ℕ :=
  256 * Nat.clog 2 (inputBase caller + N + Q + P + 5)

/-- The concrete threshold remains positive at all boundary parameters. -/
theorem admissionWidth_pos (caller : List ℕ) (N Q P : ℕ) : 0 < admissionWidth caller N Q P :=
  Nat.mul_pos (by decide) (Nat.clog_pos (by decide) (by omega))

/-- Physical admission covers both the computed virtual window and all caller-prefix words. -/
theorem admission_bounds {W N Q P : ℕ} (caller : List ℕ)
    (hP : ∀ v ∈ caller, v ≤ P) (hW : admissionWidth caller N Q P ≤ W) :
    Fits W (inputBase caller + 4 * windowSize N Q + 1024) ∧
      ∀ v ∈ caller, Fits W v := by
  have hc : Nat.clog 2 (inputBase caller + N + Q + P + 5) ≤ W := by
    unfold admissionWidth at hW
    omega
  refine ⟨physical_fits ?_, ?_⟩
  · have h := Nat.clog_mono_right 2 (by omega :
      inputBase caller + N + Q + 5 ≤ inputBase caller + N + Q + P + 5)
    unfold admissionWidth at hW
    omega
  · intro v hv
    have h := hP v hv
    have hceil := Nat.le_pow_clog (by decide : 1 < (2 : ℕ))
      (inputBase caller + N + Q + P + 5)
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hc
    change v < 2 ^ W
    omega

private theorem context_fits {W b N Q P : ℕ}
    (hW : 256 * Nat.clog 2 (b + N + Q + P + 5) ≤ W) : Fits W P := by
  have hc : Nat.clog 2 (b + N + Q + P + 5) ≤ W := by omega
  have hceil := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (b + N + Q + P + 5)
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hc
  change P < 2 ^ W
  omega

/-- Every native caller prefix is physically word-bounded, including a loaded dirty word
before the following remainder. Here `P` bounds every initial register and memory word,
not merely the source input or normalized values. It is an initial-data bound, not a bound
on intermediates supplied by the caller. -/
theorem caller_prefix_bounded {W b N Q P k : ℕ} {x : Data 163} {z : State 163}
    (hregs : ∀ i, x.regs i ≤ P) (hmem : ∀ a, x.mem a ≤ P)
    (hW : 256 * Nat.clog 2 (b + N + Q + P + 5) ≤ W)
    (hr : Runs W (program.program Reg.result) ⟨0, x⟩ z k) : z.data.Bounded W :=
  hr.bounded ⟨fun i => (context_fits hW).of_le (hregs i),
    fun a => (context_fits hW).of_le (hmem a)⟩

/-- Actual callable flat runs at every admitted physical width, with arbitrary dirty initial
workspace bounded by `P`. This is the interface for a real producer's reachable caller state:
`P` bounds all its initial words, including dirty pre-modulo loads. Original local input words
derive the concrete source execution; no solver, run, time, routing or layout certificate is
assumed. The same final `y` contains exact answers, restored input and the caller frame. -/
theorem runs_caller {W b m N P : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 163) (hb : x.regs Reg.base = b)
    (hinput : ∀ a, a < QueriedProduct.inputEnd m N qs.length →
      x.mem (b + a) =
        (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hN : D m ^ 18 ≤ N) (hregs : ∀ i, x.regs i ≤ P) (hmem : ∀ a, x.mem a ≤ P)
    (hW : 256 * Nat.clog 2 (b + N + qs.length + P + 5) ≤ W) :
    ∃ y n, n ≤ timeBound (m := m) qs ∧
      Runs W (program.program Reg.result) ⟨0, x⟩ ⟨program.size, y⟩ n ∧
      Executes W (program.program Reg.result) ⟨0, x⟩
        (b + QueriedProduct.outputBase (19 * m) m N qs.length) (n + 1) ∧
      y.Bounded W ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length → y.mem (b + a) = x.mem (b + a)) ∧
      (∀ a, a < b ∨ b + windowSize N qs.length ≤ a → y.mem a = x.mem a) := by
  have hfit : Fits W (b + 4 * windowSize N qs.length + 1024) := by
    apply physical_fits
    have h := Nat.clog_mono_right 2 (by omega :
      b + N + qs.length + 5 ≤ b + N + qs.length + P + 5)
    omega
  obtain ⟨y, hy, yr, yb, yM, hv, hi, hf⟩ := exec X Y qs x hb hinput hX hY hN hfit
  have hx : x.Bounded W := ⟨fun i => (context_fits hW).of_le (hregs i),
    fun a => (context_fits hW).of_le (hmem a)⟩
  have ybound := hy.bounded hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨y, n, hn, ?_, ?_, ybound, hv, hi, hf⟩
  · simpa only [Nat.zero_add] using hy.runs (pc := 0)
      (p := program.program Reg.result) (Program.Contains.self _).append_left
  · simpa only [yr] using hy.executes Reg.result

/-- At every admitted physical width, the initialized callable program returns all requested
exact product words and preserves caller/local-input memory. No sparsity premise is used. -/
theorem runs_wide {W m N P : ℕ} (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hP : ∀ v ∈ caller, v ≤ P) (hW : admissionWidth caller N qs.length P ≤ W) :
    InputFits W (input caller X Y qs) ∧
    ∃ y n, n + 1 ≤ timeBound (m := m) qs + 3 ∧
      Runs W (entryProgram.program Reg.result) (State.init (input caller X Y qs))
        ⟨entryProgram.size, y⟩ n ∧
      Executes W (entryProgram.program Reg.result) (State.init (input caller X Y qs))
        (inputBase caller + QueriedProduct.outputBase (19 * m) m N qs.length) (n + 1) ∧
      y.Bounded W ∧
      (∀ i : Fin qs.length,
        y.mem (inputBase caller + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length →
        y.mem (inputBase caller + a) =
          (State.init (input caller X Y qs) : State 163).data.mem (inputBase caller + a)) ∧
      (∀ a, a < inputBase caller ∨ inputBase caller + windowSize N qs.length ≤ a →
        y.mem a = (State.init (input caller X Y qs) : State 163).data.mem a) := by
  obtain ⟨hfit, hcaller⟩ := admission_bounds caller hP hW
  obtain ⟨hi, y, n, hn, hr, he, hy, hv, hin, hf⟩ := runs caller X Y qs hN hX hY hcaller hfit
  exact ⟨hi, y, n, by omega, hr, he, hy, hv, hin, hf⟩

/-- Every initialized prefix, including raw dirty loads before normalization, fits the admitted
physical width. Outside the explicit original input the initialized memory is zero. Thus `P`
in this initialized interface need only bound the protected caller prefix. -/
theorem bounded_reachable {W m N P k : ℕ} (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hP : ∀ v ∈ caller, v ≤ P) (hW : admissionWidth caller N qs.length P ≤ W)
    {z : State 163}
    (hz : Runs W (entryProgram.program Reg.result) (State.init (input caller X Y qs)) z k) :
    z.data.Bounded W := by
  obtain ⟨hfit, hcaller⟩ := admission_bounds caller hP hW
  exact hz.bounded_init (input_fits caller X Y qs hN hX hY hcaller hfit)

/-- Complete actual initialized thin saving, including base loading, all translated memory
accesses, span normalization and halt. The occurrence bound is explicit and stronger than a
distinct-set bound for lists containing duplicate requests. -/
theorem runs_thin {W m N P : ℕ} (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N) (hQ : qs.length * 2 ^ m ≤ N ^ 2)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hP : ∀ v ∈ caller, v ≤ P) (hW : admissionWidth caller N qs.length P ≤ W) :
    InputFits W (input caller X Y qs) ∧
    ∃ y n,
      Runs W (entryProgram.program Reg.result) (State.init (input caller X Y qs))
        ⟨entryProgram.size, y⟩ n ∧
      Executes W (entryProgram.program Reg.result) (State.init (input caller X Y qs))
        (inputBase caller + QueriedProduct.outputBase (19 * m) m N qs.length) (n + 1) ∧
      ((n + 1 : ℕ) : ℝ) ≤
        17301504 * ((19 * m + 1 : ℕ) : ℝ) * (N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) ∧
      y.Bounded W ∧
      (∀ i : Fin qs.length,
        y.mem (inputBase caller + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length →
        y.mem (inputBase caller + a) =
          (State.init (input caller X Y qs) : State 163).data.mem (inputBase caller + a)) ∧
      (∀ a, a < inputBase caller ∨ inputBase caller + windowSize N qs.length ≤ a →
        y.mem a = (State.init (input caller X Y qs) : State 163).data.mem a) := by
  obtain ⟨hi, y, n, hn, hr, he, hy, hv, hin, hf⟩ := runs_wide caller X Y qs hN hX hY hP hW
  have hnR : ((n + 1 : ℕ) : ℝ) ≤ (timeBound (m := m) qs + 3 : ℕ) := by exact_mod_cast hn
  exact ⟨hi, y, n, hr, he, hnR.trans (thin_timeBound_sparse qs hN hQ), hy, hv, hin, hf⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

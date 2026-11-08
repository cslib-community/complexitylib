/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (measure while realization regressions)

public import CslibFrontier.Computability.WordRAM.Realization.While
import CslibFrontier.Computability.WordRAM.Realization.Glue
import Mathlib.Data.Nat.BinaryRec

/-!
# Query-free halving with genuine native early exit

One fixed emitter handles all input words and widths. Its source cutoff is deliberately eight
larger than the logarithmic rank, while its work charges only the actual halving iterations.
Initially zero input also executes at zero word width; no positive constant is installed before
the false guard. Arbitrary bounded old memory and an unrelated caller register are retained.
-/

public section

namespace ComplexityTests.WordRAMRealizationWhile

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

private def zeroInput : Unit ↪ (Fin 1 → ℕ) where
  toFun _ := fun _ => 0
  inj' := by intro a b _; cases a; cases b; rfl

private def word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
private def words := appendWords zeroInput word
private def half (p : Unit × ℕ) : Memory.Prog ℕ := pure (p.2 >>> 1)
private def guard (_ : Unit) (a : ℕ) : Prop := 0 < a
private instance (d : Unit) (a : ℕ) : Decidable (guard d a) := inferInstanceAs (Decidable (0 < a))

private theorem half_realizes (u : Unit ↪ (Fin 1 → ℕ)) :
    Realizes .exact half (appendWords u word) word
    (fun w (_, a) _ => 0 < a ∧ Fits w a) (fun _ _ => 3) := by
  unfold half
  have hp : GlueComputes .exact (fun v : Fin 2 → ℕ => 0 < v 1)
      (fun v => v 1) (fun v => v 1) 1 := GlueComputes.proj 1 (fun _ _ => le_rfl)
  have hc : GlueComputes .exact (fun v : Fin 2 → ℕ => 0 < v 1)
      (fun _ => 1) (fun v => v 1) 1 := GlueComputes.const 1 (fun _ h => h)
  have h := GlueComputes.bin_exact hp hc .shiftRight (fun _ _ => rfl)
    (fun v _ => Nat.shiftRight_le (v 1) 1)
  simpa [appendWords, word, Fin.appendEquiv,
    Fin.append, Fin.addCases, BinOp.eval] using Realizes.glue (appendWords u word) h

private def rank (a : ℕ) : ℕ := if a = 0 then 0 else a.log2 + 1

private theorem rank_eq_zero {a : ℕ} (h : rank a = 0) : a = 0 := by
  by_contra ha
  simp [rank, ha] at h

private theorem rank_half {a : ℕ} (ha : 0 < a) : rank a = rank (a >>> 1) + 1 := by
  by_cases hh : a >>> 1 = 0
  · have ha1 : a = 1 := by
      rw [Nat.shiftRight_eq_div_pow] at hh
      norm_num at hh
      omega
    simp [ha1, rank]
  · have h := Nat.log2_eq_succ_log2_shiftRight hh
    simp only [rank, Nat.ne_of_gt ha, ↓reduceIte, hh] at *
    omega

private theorem halving_realizes :
    Realizes .exact (fun (d, a) => boundedWhile guard half d (rank a + 8) a) words word
      (fun w (_, a) _ => Fits w a ∧ rank a ≤ rank a + 8)
      (fun (d, a) s => whileWork guard half (fun _ _ => 3) d (rank a + 8) a s) := by
  have h := Realizes.whileMeasure zeroInput word (.lt 0 1) (fun (_, a) => rank a + 8)
    (half_realizes zeroInput) (fun w _ a _ => Fits w a) (fun _ a _ => rank a)
    (fun _ _ a _ _ hr => by
      have ha := rank_eq_zero hr
      subst a
      change ¬(0 < 0)
      omega)
    (fun w d a s hi hg _ => by
      change 0 < a at hg
      refine ⟨⟨hg, hi⟩, ?_, ?_⟩
      · exact hi.of_le (Nat.shiftRight_le a 1)
      · change rank (a >>> 1) < rank a
        have := rank_half hg
        omega)
  exact h

private theorem loop_zero (d : Unit) (n a : ℕ) (hr : rank a ≤ n) :
    boundedWhile guard half d n a = pure 0 := by
  induction n generalizing a with
  | zero => have ha := rank_eq_zero (a := a) (by omega); subst a; rfl
  | succ n ih =>
    by_cases ha : 0 < a
    · have hm := rank_half ha
      simpa only [boundedWhile, guard, ha, ↓reduceIte, half, pure_bind] using
        ih (a >>> 1) (by omega)
    · have : a = 0 := by omega
      subst a
      simp [boundedWhile, guard]

private theorem loop_work (d : Unit) (n a : ℕ) (hr : rank a ≤ n) (s : Memory.State) :
    whileWork guard half (fun _ _ => 3) d n a s = 4 * rank a := by
  induction n generalizing a s with
  | zero => have ha := rank_eq_zero (a := a) (by omega); subst a; rfl
  | succ n ih =>
    by_cases ha : 0 < a
    · have hm := rank_half ha
      change (if 0 < a then 3 + whileWork guard half (fun _ _ => 3) d n (a >>> 1) s + 1
        else 0) = _
      rw [ite_eq_left ha, ih (a >>> 1) (by omega) s]
      omega
    · have : a = 0 := by omega
      subst a
      simp [whileWork, guard, rank]

/-- The actual query-free work is logarithmic, independent of the eight unused source steps. -/
private theorem halving_work (d : Unit) (a : ℕ) (s : Memory.State) :
    whileWork guard half (fun _ _ => 3) d (rank a + 8) a s = 4 * rank a :=
  loop_work d (rank a + 8) a (by omega) s

-- Nontrivial early exit: four halvings; eight extra cutoff steps do not add work.
example (s : Memory.State) :
    memoryCost (boundedWhile guard half () 12 15) s = 0 ∧
    whileWork guard half (fun _ _ => 3) () 12 15 s = 16 := by
  rw [loop_zero () 12 15 (by decide)]
  exact ⟨rfl, loop_work () 12 15 (by decide) s⟩

-- A source cutoff cannot truncate a still-positive native guard.
example (s : Memory.State) :
    ¬whileSafe guard half (fun _ _ _ => True) 4 () 0 1 s := by
  change ¬¬(0 < 1)
  decide

private def oneInput : Unit ↪ (Fin 1 → ℕ) where
  toFun _ := fun _ => 1
  inj' := by intro a b _; cases a; cases b; rfl

-- A changed native guard can stop with positive rank: 15 -> 7 -> 3 -> 1, then exit.
example : Realizes .exact
    (fun (d, a) => boundedWhile (fun _ a => 1 < a) half d (rank a + 8) a)
    (appendWords oneInput word) word
    (fun w (_, a) _ => Fits w a ∧ rank a ≤ rank a + 8)
    (fun (d, a) s => whileWork (fun _ a => 1 < a) half (fun _ _ => 3) d (rank a + 8) a s) := by
  apply Realizes.whileMeasure oneInput word (.lt 0 1) (fun (_, a) => rank a + 8)
    (half_realizes oneInput) (fun w _ a _ => Fits w a) (fun _ a _ => rank a)
  · intro w d a s hi hr
    have ha := rank_eq_zero hr
    subst a
    change ¬(1 < 0)
    omega
  · intro w d a s hi hg _
    change 1 < a at hg
    refine ⟨⟨by omega, hi⟩, hi.of_le (Nat.shiftRight_le a 1), ?_⟩
    change rank (a >>> 1) < rank a
    have := rank_half (show 0 < a by omega)
    omega

example (s : Memory.State) :
    (Memory.spec 4).clientResult s (boundedWhile (fun _ : Unit => fun a => 1 < a) half () 12 15)
        = 1 ∧
      whileWork (fun _ : Unit => fun a => 1 < a) half (fun _ _ => 3) () 12 15 s = 12 ∧
      whileSafe (fun _ : Unit => fun a => 1 < a) half
        (fun w (_, a) _ => 0 < a ∧ Fits w a) 4 () 12 15 s := by
  norm_num [boundedWhile, half, whileWork, whileSafe, StateTransitionSpec.clientResult,
    StateTransitionSpec.clientState, ← PFunctor.FreeM.bind_eq_bind,
    StateTransitionSpec.runClient_bind, Fits]

-- The source potential pays every query-free iteration and retains seven unused exit credits.
example (w n a : ℕ) (s : Memory.State) (hr : rank a ≤ n) :
    memoryCost (boundedWhile guard half () n a) s +
      whileWork guard half (fun _ _ => 3) () n a s + 7 ≤ 4 * rank a + 7 := by
  have hsource := loop_zero () n a hr
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard half () n a)) := by
    rw [hsource]
    trivial
  have h := while_charge_le_potential guard half (fun _ _ => 3) w ()
    (fun _ _ => True) (fun a _ => 4 * rank a + 7)
    (fun a s _ hg _ => by
      have hp := rank_half hg
      refine ⟨trivial, ?_⟩
      change 0 + 3 + 1 + (4 * rank (a >>> 1) + 7) ≤ 4 * rank a + 7
      omega) trivial hv
  simpa [hsource, StateTransitionSpec.clientResult, StateTransitionSpec.clientState, rank] using h

/-- A single code/ABI/factor works at every width, even zero, and preserves every old memory cell
and a separate caller word. The native budget uses the actual logarithmic work, not the cutoff. -/
theorem uniform_halving : ∃ n C : ℕ, ∃ code : Code .exact (2 + (1 + n + 1) + 2),
    ∃ out control : Fin (2 + (1 + n + 1) + 2),
      ∀ w a keep mem, Fits w a → Fits w keep → (∀ i, Fits w (mem i)) →
        ∃ x y, x.mem = mem ∧ x.regs (⟨1, by omega⟩ : Fin (2 + (1 + n + 1) + 2)) = a ∧
          x.regs control = keep ∧
          ExecWithin w code x y (C * (4 * (if a = 0 then 0 else a.log2 + 1) + 1)) ∧
          y.regs out = 0 ∧ y.mem = mem ∧ y.regs control = keep := by
  obtain ⟨n, C, emit, he⟩ := halving_realizes
  let r := 2 + (1 + n + 1) + 2
  let src (i : Fin 2) : Fin r := ⟨i.val, by omega⟩
  let tmp (i : Fin (1 + n + 1)) : Fin r := ⟨2 + i.val, by have := i.isLt; omega⟩
  let frontier : Fin r := ⟨r - 1, by omega⟩
  let control : Fin r := ⟨r - 2, by omega⟩
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    change 2 + i.val = 2 + j.val at hh
    omega
  have hd (i : Fin 2) (j : Fin (1 + n + 1)) : src i ≠ tmp j := by
    intro h
    have hh := congrArg Fin.val h
    change i.val = 2 + j.val at hh
    have := i.isLt
    omega
  have hf (j : Fin (1 + n + 1)) : tmp j ≠ frontier := by
    intro h
    have hh := congrArg Fin.val h
    change 2 + j.val = r - 1 at hh
    have := j.isLt
    dsimp only [r] at hh
    omega
  have hs (i : Fin 2) : src i ≠ frontier := by
    intro h
    have hh := congrArg Fin.val h
    change i.val = r - 1 at hh
    have := i.isLt
    dsimp only [r] at hh
    omega
  refine ⟨n, C, emit frontier src tmp, tmp (Fin.castAdd (n + 1) 0), control, ?_⟩
  intro w a keep mem ha hk hm
  let x : Data r := ⟨fun i => if i.val = 1 then a else if i.val = r - 2 then keep else 0, mem⟩
  have hx : x.Bounded w := by
    refine ⟨fun i => ?_, hm⟩
    change Fits w (if i.val = 1 then a else if i.val = r - 2 then keep else 0)
    split_ifs <;> first | exact ha | exact hk | exact fits_zero w
  have hin : x.regs ∘ src = words ((), a) := by
    funext i
    fin_cases i
    · change (if 0 = 1 then a else if 0 = r - 2 then keep else 0) = 0
      simp [r]
    · rfl
  have hsource := loop_zero () (rank a + 8) a (by omega)
  have hsafe : Fits w a ∧ rank a ≤ rank a + 8 := ⟨ha, by omega⟩
  have hvalid : (Memory.spec w).ValidHistory (memoryState frontier x)
      ((Memory.spec w).clientHistory (memoryState frontier x)
        (boundedWhile guard half () (rank a + 8) a)) := by
    rw [hsource]
    trivial
  obtain ⟨y, hy, hmy, hout, hframe⟩ := (he frontier src tmp hi hd hf hs).2
    w ((), a) x hx hin hsafe hvalid
  dsimp only at hy hmy hout
  rw [hsource, memoryCost_pure, halving_work] at hy
  have hyout : y.regs (tmp (Fin.castAdd (n + 1) 0)) = 0 := by
    simpa [hsource, word, StateTransitionSpec.clientResult] using hout 0
  have hxctrl : x.regs control = keep := by
    have hne : r - 2 ≠ 1 := by dsimp only [r]; omega
    simp [x, control, hne]
  have hctrl : y.regs control = keep := by
    have hcf : control ≠ frontier := by
      intro h
      have hh := congrArg Fin.val h
      change r - 2 = r - 1 at hh
      dsimp only [r] at hh
      omega
    have hct (j : Fin (1 + n + 1)) : tmp j ≠ control := by
      intro h
      have hh := congrArg Fin.val h
      change 2 + j.val = r - 2 at hh
      have := j.isLt
      dsimp only [r] at hh
      omega
    rw [hframe control hcf hct]
    exact hxctrl
  refine ⟨x, y, rfl, rfl, hxctrl, ?_, hyout, ?_, hctrl⟩
  · simpa only [Nat.zero_add, rank] using hy
  · rw [hsource] at hmy
    exact congrArg Memory.State.mem hmy

-- The SAME selected native code has an initial false exit at width zero, and four genuine
-- query-free halving iterations at width four, retaining the caller word and dirty memory.
example : ∃ n C : ℕ, ∃ code : Code .exact (2 + (1 + n + 1) + 2),
    ∃ out control : Fin (2 + (1 + n + 1) + 2),
      (∃ x y, ExecWithin 0 code x y C ∧ y.regs out = 0) ∧
      (∃ x y, x.regs (⟨1, by omega⟩ : Fin (2 + (1 + n + 1) + 2)) = 15 ∧
        ExecWithin 4 code x y (C * 17) ∧ y.regs out = 0 ∧
        y.mem 100 = 9 ∧ y.regs control = 9) := by
  obtain ⟨n, C, code, out, control, h⟩ := uniform_halving
  obtain ⟨x₀, y₀, _, _, _, h₀, ho₀, _, _⟩ :=
    h 0 0 0 (fun _ => 0) (by decide) (by decide) (fun _ => by decide)
  obtain ⟨x₁₅, y₁₅, _, hin, _, h₁₅, ho₁₅, hm₁₅, hc₁₅⟩ :=
    h 4 15 9 (fun _ => 9) (by decide) (by decide) (fun _ => by decide)
  refine ⟨n, C, code, out, control, ⟨x₀, y₀, ?_, ho₀⟩,
    x₁₅, y₁₅, hin, ?_, ho₁₅, congrFun hm₁₅ 100, hc₁₅⟩
  · simpa using h₀
  · exact h₁₅

end ComplexityTests.WordRAMRealizationWhile

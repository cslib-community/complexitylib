/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.Instances
public import Complexity.Computability.WordRAM.Width
public import Complexity.Computability.GenericRAM.Signed.Fits
public import Mathlib.Data.Nat.Log

/-!
# Initialized native ExactTriangle preparation

The input supplies only four raw scalar headers and three signed weight arrays. One positive
ceiling-logarithm threshold derived from these original parameters covers the signed residue
calls and every arithmetic/address fit of the actual preparation program. The same fixed flat
program executes at every larger physical width, with the complete output read from its actual
pre-halt state and the final halt charged.

## Main definitions

* `PreparationInput.input`: original unsigned headers and signed-encoded weights.
* `PreparationInput.width`: sufficient positive physical width from the original parameters.
* `PreparationInput.flatProgram`: fixed native code returning the output-record pointer.

## Main results

* `PreparationInput.exec_input`: structured execution for composition, without the final halt.
* `PreparationInput.runs_input`: initialized execution, exact readback, fits and charged halt.
* `PreparationInput.bounded_reachable`: input-derived word and address bounds at every prefix.
* `PreparationInput.width_le_log`, `PreparationInput.wordBound_le_pow`: logarithmic physical
  width and polynomial words and address space when the scalar headers and weights are bounded.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PreparationInput

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Actual raw `(D,g,n,p)` headers followed by the three signed matrix arrays. -/
@[expose]
def input (n D g p : ℕ) (values : List ℤ) : List ℕ :=
  [D, g, n, p] ++ values.map Signed.encode

/-- Original-input numeric envelope; the preparation budget is an explicit polynomial. -/
@[expose]
def envelope (n D g p A : ℕ) : ℕ := Instances.budget n D g p + A + p + 2

/-- Three extra bits supply both the asymmetric signed range and the native signed compiler's
two-bit extension. This is a positive ceiling-logarithm bound in the original headers/weights. -/
@[expose]
def width (n D g p A : ℕ) : ℕ := Nat.clog 2 (envelope n D g p A) + 3

/-- An explicit polynomial in the original numeric parameters bounds every word and address
at every wider admitted width. It does not grow with the physical width chosen by the caller. -/
@[expose]
def wordBound (n D g p A : ℕ) : ℕ := 16 * envelope n D g p A

/-- One fixed 64-register flat program, including the actual halt. -/
@[expose]
def flatProgram : Program .standard 64 := Instances.program.program Instances.output

/-- The code length and width independence are uniform over all runtime inputs. -/
theorem flatProgram_fixed : flatProgram.length ≤ 641 ∧ ¬flatProgram.ReadsWidth := by
  refine ⟨?_, Code.not_readsWidth_program Instances.program_fixed.2 _⟩
  simp only [flatProgram, Code.program, List.length_append, Code.length_assemble,
    List.length_cons, List.length_nil]
  exact Nat.add_le_add_right Instances.program_fixed.1 1

/-- The concrete initialized payload is the original weight sequence, with no supplied table. -/
theorem input_word (n D g p : ℕ) (values : List ℤ) (q : ℕ) :
    (Data.init (input n D g p values) : Data 64).mem (5 + q) =
      Signed.encode (values.getD q 0) := by
  rw [show 5 + q = (4 + q) + 1 by omega, Data.init_mem_succ]
  rw [input, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
  exact List.getD_map values 0 Signed.encode

private theorem budget_bounds (n D g p : ℕ) :
    4 + 3 * (n * n) ≤ Instances.budget n D g p ∧
      D ≤ Instances.budget n D g p ∧ g ≤ Instances.budget n D g p ∧
      n ≤ Instances.budget n D g p ∧ p ≤ Instances.budget n D g p := by
  dsimp only [Instances.budget, Catalogue.budget]
  omega

private theorem budget_le_pow {n D g p : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) :
    Instances.budget n D g p ≤ 286 * n ^ 6 := by
  have h1 : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ hn
  have hn6 : n ≤ n ^ 6 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hn (by decide : 1 ≤ 6)
  have h2 : n ^ 2 ≤ n ^ 6 := Nat.pow_le_pow_right hn (by decide)
  have h3 : n ^ 3 ≤ n ^ 6 := Nat.pow_le_pow_right hn (by decide)
  have h4 : n ^ 4 ≤ n ^ 6 := Nat.pow_le_pow_right hn (by decide)
  have hhigh : p * D * n ^ 4 ≤ n ^ 6 := by
    calc
      _ ≤ (n * n) * n ^ 4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul hp hD)
      _ = n ^ 6 := by ring
  have hpn3 : p * n ^ 3 ≤ n ^ 6 := by
    calc
      _ ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hp
      _ = n ^ 4 := by ring
      _ ≤ n ^ 6 := h4
  have hpn2 : p * n ^ 2 ≤ n ^ 6 := by
    calc
      _ ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hp
      _ = n ^ 3 := by ring
      _ ≤ n ^ 6 := h3
  have hnD : n * D ≤ n ^ 6 := by
    calc
      _ ≤ n * n := Nat.mul_le_mul_left _ hD
      _ = n ^ 2 := by ring
      _ ≤ n ^ 6 := h2
  have hD6 := hD.trans hn6
  have hg6 := hg.trans hn6
  have hp6 := hp.trans hn6
  have heq : Instances.budget n D g p =
      2 * (p * D * n ^ 4) + 4 * n ^ 4 + 7 * (p * n ^ 3) + 30 * (p * n ^ 2) +
        62 * n ^ 2 + 2 * (n * D) + 8 * D + 8 * g + 12 * n + 13 * p + 138 := by
    dsimp only [Instances.budget, Catalogue.budget]
    ring
  rw [heq]
  omega

private theorem envelope_le_pow {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    envelope n D g p A ≤ (n + 2) ^ (κ + 15) := by
  let b := n + 2
  have hb : 1 ≤ b := by dsimp only [b]; omega
  have hpow : n ^ 6 ≤ b ^ (κ + 6) :=
    (Nat.pow_le_pow_left (by dsimp only [b]; omega : n ≤ b) 6).trans
      (Nat.pow_le_pow_right hb (by omega))
  have hbudget := (budget_le_pow hn hD hg hp).trans (Nat.mul_le_mul_left 286 hpow)
  have hAval : A ≤ b ^ (κ + 6) := hA.trans (Nat.pow_le_pow_right hb (by omega))
  have hbpow : b ≤ b ^ (κ + 6) := Nat.le_self_pow (by omega) b
  have hpval : p ≤ b ^ (κ + 6) := hp.trans ((by dsimp only [b]; omega : n ≤ b).trans hbpow)
  have hunit : 1 ≤ b ^ (κ + 6) := by have := pow_pos (by omega : 0 < b) (κ + 6); omega
  have hsum : envelope n D g p A ≤ 290 * b ^ (κ + 6) := by
    dsimp only [envelope]
    omega
  have hcoef : 290 ≤ b ^ 9 := (show 290 ≤ 2 ^ 9 from by decide).trans
    (Nat.pow_le_pow_left (by dsimp only [b]; omega : 2 ≤ b) 9)
  calc
    envelope n D g p A ≤ 290 * b ^ (κ + 6) := hsum
    _ ≤ b ^ 9 * b ^ (κ + 6) := Nat.mul_le_mul_right _ hcoef
    _ = b ^ (κ + 15) := by rw [← Nat.pow_add]; congr 1; omega

/-- For polynomially bounded weights and size-bounded scalar headers, the physical threshold
is explicitly logarithmic in the original outer dimension. The bound on `g` is stated because
its raw input word must fit even when it does not change the resulting piece size. -/
theorem width_le_log {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    width n D g p A ≤ (κ + 18) * Nat.clog 2 (n + 2) := by
  have hbase := Nat.le_pow_clog (by decide : 1 < 2) (n + 2)
  have hpow := (envelope_le_pow hn hD hg hp hA).trans
    (Nat.pow_le_pow_left hbase (κ + 15))
  rw [← Nat.pow_mul] at hpow
  have hclog := Nat.clog_le_of_le_pow hpow
  have hpos : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  dsimp only [width]
  nlinarith only [hclog, hpos]

/-- The same original-size hypotheses turn the every-prefix word/support bound into a
polynomial in the original outer dimension, independent of physical width. -/
theorem wordBound_le_pow {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n D g p A ≤ (n + 2) ^ (κ + 19) := by
  have hc : 16 ≤ (n + 2) ^ 4 := (show 16 ≤ 2 ^ 4 from by decide).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 4)
  calc
    _ ≤ (n + 2) ^ 4 * (n + 2) ^ (κ + 15) :=
      Nat.mul_le_mul hc (envelope_le_pow hn hD hg hp hA)
    _ = (n + 2) ^ (κ + 19) := by rw [← Nat.pow_add]; congr 1; omega

private theorem fits_at_width (n D g p A : ℕ) :
    GenericRAM.Signed.Fits (Nat.clog 2 (envelope n D g p A) + 1) ((A + p + 1 : ℕ) : ℤ) ∧
      Fits (width n D g p A) (Instances.budget n D g p) := by
  let V := envelope n D g p A
  let k := Nat.clog 2 V
  have hpow : V ≤ 2 ^ k := Nat.le_pow_clog (by decide) V
  have hmag : A + p + 1 < 2 ^ k := lt_of_lt_of_le
    (by dsimp only [V, envelope]; omega) hpow
  have hbudget : Instances.budget n D g p < 2 ^ k := lt_of_lt_of_le
    (by dsimp only [V, envelope]; omega) hpow
  refine ⟨⟨by omega, ?_, ?_⟩, (show Fits k (Instances.budget n D g p) from hbudget).mono
    (by dsimp only [width, k, V]; omega)⟩
  · simp only [Nat.add_sub_cancel]
    exact (neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _)
  · simp only [Nat.add_sub_cancel]
    exact_mod_cast hmag

private theorem input_fits {n D g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A) :
    InputFits (width n D g p A) (input n D g p values) := by
  obtain ⟨hmag, hbudget⟩ := fits_at_width n D g p A
  obtain ⟨hlenBound, hD, hg, hn, hp⟩ := budget_bounds n D g p
  refine ⟨?_, ?_⟩
  · simpa only [input, List.length_append, List.length_cons, List.length_nil,
      List.length_map, hlen, Nat.reduceAdd] using hbudget.of_le hlenBound
  · intro v hmem
    rcases List.mem_append.mp hmem with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact hbudget.of_le hD
      · exact hbudget.of_le hg
      · exact hbudget.of_le hn
      · exact hbudget.of_le hp
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
      have hs := hmag.of_natAbs_le ((hv z hz).trans (by omega : A ≤ A + p + 1))
      exact (Signed.encode_fits hs).mono (by dsimp only [width]; omega)

/-- Structured initialized execution for real native caller composition. The budget excludes
only the final halt; all existing original-input, width and exact readback hypotheses remain.
This does not accept an execution, layout or intermediate-fit certificate. -/
theorem exec_input {n D g p A W : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hw : width n D g p A ≤ W) :
    let C := fun rho => Nat.count (fun q => (values.getD q 0 % (p : ℤ)).toNat = rho) (n * n)
    let K := ChunkCatalogue.before C (queryCap n D) p
    ∃ y, ExecWithin W Instances.program (.init (input n D g p values)) y
        (Instances.timeBound n D p K (numPieces n D g) - 1) ∧
      Instances.Output n D g p (fun q => values.getD q 0)
        (.init (input n D g p values)) y ∧
      InputFits W (input n D g p values) ∧ y.Bounded W := by
  obtain ⟨hmag, hbudget⟩ := fits_at_width n D g p A
  have hmod : GenericRAM.Signed.Fits (Nat.clog 2 (envelope n D g p A) + 1) (p : ℤ) :=
    hmag.of_natAbs_le (by simp only [Int.natAbs_natCast]; omega)
  have hvalues (q : ℕ) (hq : q < 3 * (n * n)) :
      GenericRAM.Signed.Fits (Nat.clog 2 (envelope n D g p A) + 1) (values.getD q 0) := by
    have hq' : q < values.length := by omega
    have hmem : values.getD q 0 ∈ values := by
      rw [List.getD_eq_getElem _ _ hq']
      exact List.getElem_mem hq'
    exact hmag.of_natAbs_le ((hv _ hmem).trans (by omega : A ≤ A + p + 1))
  obtain ⟨y, hy, hout⟩ := Instances.exec_at n D g p (fun q => values.getD q 0)
    (.init (input n D g p values)) rfl rfl rfl rfl (fun q _ => input_word n D g p values q)
    hD hDn hg hp hmod hvalues hbudget
  have hew := ExecWithin.mono_width Instances.program_fixed.2 hy hw
  have hi := (input_fits values hlen hv).mono hw
  have hybounded := hew.bounded (Data.Bounded.init hi)
  exact ⟨y, hew, hout, hi, hybounded⟩

/-- Complete initialized execution at every admitted physical width. The prefix witness and
the output predicate use the same actual pre-halt memory, and the bound includes the halt. -/
theorem runs_input {n D g p A W : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hw : width n D g p A ≤ W) :
    let C := fun rho => Nat.count (fun q => (values.getD q 0 % (p : ℤ)).toNat = rho) (n * n)
    let K := ChunkCatalogue.before C (queryCap n D) p
    ∃ y t, t ≤ Instances.timeBound n D p K (numPieces n D g) ∧
      Runs W flatProgram (State.init (input n D g p values)) ⟨Instances.program.size, y⟩
        (t - 1) ∧
      Executes W flatProgram (State.init (input n D g p values)) (y.regs Instances.output) t ∧
      Instances.Output n D g p (fun q => values.getD q 0)
        (.init (input n D g p values)) y ∧
      InputFits W (input n D g p values) ∧ y.Bounded W := by
  obtain ⟨y, hew, hout, hi, hybounded⟩ := exec_input values hlen hD hDn hg hp hv hw
  obtain ⟨t, ht, he⟩ := hew
  have hr := he.runs (pc := 0) (p := flatProgram) (Program.Contains.self _).append_left
  refine ⟨y, t + 1, ?_, ?_, ?_, hout, hi, hybounded⟩
  · let T := Instances.timeBound n D p
      (ChunkCatalogue.before
        (fun rho => Nat.count (fun q => (values.getD q 0 % (p : ℤ)).toNat = rho) (n * n))
        (queryCap n D) p) (numPieces n D g)
    change t ≤ T - 1 at ht
    change t + 1 ≤ T
    have hpos : 1 ≤ T := by
      dsimp only [T, Instances.timeBound]
      omega
    omega
  · simpa only [State.init, Nat.zero_add, Nat.add_sub_cancel] using hr
  · simpa only [flatProgram, State.init] using he.executes Instances.output

private theorem pow_width_lt (n D g p A : ℕ) :
    2 ^ width n D g p A < wordBound n D g p A := by
  let V := envelope n D g p A
  let k := Nat.clog 2 V
  have hV : 1 < V := by dsimp only [V, envelope]; omega
  have hkpos : 0 < k := Nat.clog_pos (by decide) hV
  have hk : k.pred + 1 = k := Nat.succ_pred_eq_of_pos hkpos
  have hpred : 2 ^ k.pred < V := Nat.pow_pred_clog_lt_self (by decide) hV
  change 2 ^ (k + 3) < 16 * V
  calc
    2 ^ (k + 3) = 2 ^ k * 8 := by rw [Nat.pow_add]
    _ = 2 ^ (k.pred + 1) * 8 := congrArg (fun j => 2 ^ j * 8) hk.symm
    _ = (2 ^ k.pred * 2) * 8 := by rw [Nat.pow_succ]
    _ < 16 * V := by omega

/-- All actual run prefixes, at every admitted physical width, have bounded words and zero
memory beyond one original-input polynomial. Width independence identifies each such prefix
with the smaller admitted run; the generic native memory-frame theorem supplies the support
bound. No caller-provided invariant or execution certificate is used. -/
theorem bounded_reachable {n D g p A W : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hw : width n D g p A ≤ W)
    (s : State 64) (steps : ℕ)
    (hr : Runs W flatProgram (State.init (input n D g p values)) s steps) :
    (∀ i, s.data.regs i < wordBound n D g p A) ∧
      (∀ a, s.data.mem a < wordBound n D g p A) ∧
      ∀ a, wordBound n D g p A ≤ a → s.data.mem a = 0 := by
  obtain ⟨_, _, _, _, he, _, hi, -⟩ := runs_input values hlen hD hDn hg hp hv le_rfl
  have hlow := Runs.prefix_at_smaller_width flatProgram_fixed.2 hw hr he
  have hs := Runs.bounded hlow (Data.Bounded.init hi)
  have hword := pow_width_lt n D g p A
  refine ⟨fun i => (hs.1 i).trans hword, fun a => (hs.2 a).trans hword, ?_⟩
  intro a ha
  have habove : 2 ^ width n D g p A ≤ a := hword.le.trans ha
  rw [hlow.mem_above (Data.Bounded.init hi) habove]
  cases a with
  | zero => have := Nat.two_pow_pos (width n D g p A); omega
  | succ a =>
    change (input n D g p values).getD a 0 = 0
    apply List.getD_eq_default
    have hlenFit := hi.1
    dsimp only [Fits] at hlenFit
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.PreparationInput

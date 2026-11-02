/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Flat
public import Complexity.Computability.WordRAM.Width

/-!
# Physical-width-independent prefixes of the caller-safe fixed-prime program

The actual minimum-width solver execution controls every prefix at every larger admitted width.
The initial raw dirty-word bound P applies before any remainder instruction. It is a hypothesis
about the original caller data, not a supplied execution certificate or an algorithm argument.
New address support is bounded independently of physical width; original outside memory is kept.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Original raw words fit at every admitted width, including dirty loads before reduction. -/
theorem original_bounded {W n d g p T b P : ℕ} (x : Data 640)
    (hregs : ∀ i, x.regs i ≤ P) (hmem : ∀ q, x.mem q ≤ P)
    (hW : admissionWidth n d g p T b P ≤ W) : x.Bounded W := by
  have fit : Fits W P := (admission_fits hW).of_le (by omega)
  exact ⟨fun i => fit.of_le (hregs i), fun q => fit.of_le (hmem q)⟩

/-- Every actual caller prefix has an original-input envelope. The complete concrete solver
supplies the comparison run; no run, layout, witness or resource certificate is a premise. -/
theorem bounded_reachable_caller {W m n g p b P k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (x : Data 640) (xn : x.regs Reg.n = n) (xD : x.regs Reg.dimension = D m)
    (xg : x.regs Reg.groups = g) (xp : x.regs Reg.prime = p) (xb : x.regs Reg.base = b)
    (hab : x.regs Reg.ab + n * n ≤ b) (hbc : x.regs Reg.bc + n * n ≤ b)
    (hac : x.regs Reg.ac + n * n ≤ b)
    (vab : ∀ q < n * n, x.mem (x.regs Reg.ab + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, x.mem (x.regs Reg.bc + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, x.mem (x.regs Reg.ac + q) =
      Signed.encode (values.getD (2 * (n * n) + q) 0))
    (hregs : ∀ i, x.regs i ≤ P) (hmem : ∀ q, x.mem q ≤ P)
    (hW : admissionWidth n (D m) g p (rawTotal n values) b P ≤ W)
    {s : State 640} (hr : Runs W (program.program Reg.found) ⟨0, x⟩ s k) :
    (∀ i, s.data.regs i < wordBound n (D m) g p (rawTotal n values) b P) ∧
      (∀ q, s.data.mem q < wordBound n (D m) g p (rawTotal n values) b P) ∧
      ∀ q, wordBound n (D m) g p (rawTotal n values) b P ≤ q → s.data.mem q = x.mem q := by
  let w := admissionWidth n (D m) g p (rawTotal n values) b P
  have hx : x.Bounded w := original_bounded x hregs hmem le_rfl
  have fit : Fits w (b + 4 * windowSize n (D m) g p (rawTotal n values) + 1024) :=
    (admission_fits (le_refl w)).of_le (by omega)
  obtain ⟨a, hout, y, he, -⟩ := exec values hlen hD hg hp hN
    x xn xD xg xp xb hab hbc hac vab vbc vac hx fit
  obtain ⟨t, ht, hex⟩ := he
  have hlow := Runs.prefix_at_smaller_width program_fixed.2 hW hr
    (hex.executes Reg.found)
  have hs := hlow.bounded hx
  have hpow := pow_admissionWidth_le n (D m) g p (rawTotal n values) b P
  refine ⟨fun i => (hs.1 i).trans_le hpow, fun q => (hs.2 q).trans_le hpow, ?_⟩
  exact fun q hq => hlow.mem_above hx (hpow.trans hq)

/-- Numerical envelope for initialized prefix words and newly written addresses. -/
@[expose] def prefixBound (n d g p : ℕ) (values : List ℤ) : ℕ :=
  wordBound n d g p (rawTotal n values) (workspaceBase n) (inputWordBound n d g p values)

/-- Initialized execution, including every reused dirty workspace prefix, has finite support
independent of physical width. The concrete minimum-width run supplies the comparison. -/
theorem bounded_reachable_input {W m n g p k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hW : inputWidth n (D m) g p values ≤ W)
    {s : State 640} (hr : Runs W (entryProgram.program Reg.found)
      (State.init (PreparationInput.input n (D m) g p values)) s k) :
    (∀ i, s.data.regs i < prefixBound n (D m) g p values) ∧
      (∀ q, s.data.mem q < prefixBound n (D m) g p values) ∧
      ∀ q, prefixBound n (D m) g p values ≤ q → s.data.mem q = 0 := by
  obtain ⟨hi, a, hout, y, t, ht, hpref, he, -⟩ :=
    runs_input values hlen hD hg hp hN le_rfl
  have hlow := Runs.prefix_at_smaller_width entryProgram_fixed.2 hW hr he
  have hx := Data.Bounded.init (r := 640) hi
  have hs := hlow.bounded hx
  have hpow := pow_admissionWidth_le n (D m) g p (rawTotal n values) (workspaceBase n)
    (inputWordBound n (D m) g p values)
  refine ⟨fun i => (hs.1 i).trans_le hpow, fun q => (hs.2 q).trans_le hpow, ?_⟩
  intro q hq
  have hq' : 2 ^ inputWidth n (D m) g p values ≤ q := hpow.trans hq
  rw [hlow.mem_above hx hq']
  cases q with
  | zero =>
    have := Nat.two_pow_pos (inputWidth n (D m) g p values)
    omega
  | succ q =>
    change (PreparationInput.input n (D m) g p values).getD q 0 = 0
    apply List.getD_eq_default
    have hlen := hi.1
    dsimp only [Fits] at hlen
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

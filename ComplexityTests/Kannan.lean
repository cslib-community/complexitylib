/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Computability.MCSP.Basic

/-!
# Tests for Kannan's theorem

The parameters of Kannan's language on concrete lengths, truth tables read as functions, the `Σ₃`
verifier on concrete certificates, and non-vacuity of the circuit classes the theorem escapes.
-/

namespace Cslib.Complexity.Tests.Kannan

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Parameters and truth tables -/

-- At length `3`, `k = 0` asks for hard functions of `3 (⌊log₂ 4⌋ + 1) = 9` inputs, with more than
-- `4` gates; truth tables are indexed by the input read least significant bit first.
example :
    Kannan.arity 0 3 = 9 ∧
    Kannan.threshold 0 3 = 4 ∧
    Kannan.arity 1 7 = 16 ∧
    Kannan.threshold 1 2 = 9 ∧
    Kannan.tableBound 0 0 = 8 ∧
    Kannan.certBound 0 0 = 16 ∧
    MCSP.tableFunction 2 [false, true, true, false] ![true, false] = true ∧
    MCSP.tableFunction 2 [false, true, true, false] ![true, true] = false ∧
    Kannan.table 0 0 (List.replicate 10 true) = List.replicate 8 true ∧
    BitString.binaryValue [true, false, true] = 5 := by
  decide

-- Words whose length is not a power of two belong to neither side of GapMCSP.
example (s : ℕ → ℕ) :
    [true, false, true] ∉ (GapMCSP s s fun _ => le_rfl).yes ∧
    [true, false, true] ∉ (GapMCSP s s fun _ => le_rfl).no := by
  have hnot (n : ℕ) (hn : [true, false, true].length = 2 ^ n) : False := by
    match n with
    | 0 => revert hn; decide
    | 1 => revert hn; decide
    | k + 2 =>
      have hlt : 3 < 2 ^ (k + 2) :=
        calc 3 < 2 ^ 2 := by decide
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      exact ne_of_lt (by simpa using hlt) hn
  exact ⟨fun ⟨n, hn, _⟩ => hnot n hn, fun ⟨n, hn, _⟩ => hnot n hn⟩

-- Keep the equal-length decoding client independent of the GapMCSP hypotheses.
example {u v : List Bool} (hlen : u.length = v.length)
    (h : BitString.binaryValue u = BitString.binaryValue v) : u = v :=
  BitString.binaryValue_injective_of_length_eq hlen h

/-! ### The `Σ₃` verifier -/

/-- The truth table on three inputs that is `true` only on the all-`false` input. -/
def T₀ : List Bool := true :: List.replicate 7 false

/-- The certificate of the constant-`false` circuit on three inputs: one constant gate, output
wire `3`. -/
def falseCertificate : List Bool := certificate 3 1 [(.const false, [])] 3

-- On the empty input, `T₀` gives `true`. The second block holds the earlier constant-`false` table
-- and a certificate that is not a circuit for `T₀`, and the third block is a circuit for the
-- earlier table, so the verifier accepts; without a circuit for the earlier table, it rejects.
example :
    falseCertificate.length = Kannan.certBound 0 0 ∧
    Kannan.verifier 0 ([], T₀ ++ (List.replicate 8 false ++ List.replicate 16 false) ++
      falseCertificate) = true ∧
    Kannan.verifier 0 ([], T₀ ++ (List.replicate 8 false ++ List.replicate 16 false) ++
      List.replicate 16 false) = false :=
  ⟨rfl, by decide, by decide⟩

/-! ### Non-vacuity -/

/-- The classes that Kannan's theorem escapes are not empty: the empty language has circuits of
one gate. -/
theorem zero_mem_SIZE {c : ℕ} (hc : 1 ≤ c) (k : ℕ) :
    (0 : Language Bool) ∈ SIZE fun n => c * (n + 1) ^ k := by
  intro n
  have : (0 : Language Bool).slice n = fun _ => false := by
    funext x
    simp [Language.slice]
  rw [this, complexity_const]
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (Nat.succ_ne_zero n)))

-- First hard truth tables exist at all large lengths, `Kannan.language 2` lies in `PH \ SIZE(n²)`,
-- and no polynomial budget of a fixed degree holds all of `Σ₂`.
example (k c : ℕ) :
    (∀ᶠ n in Filter.atTop, ∃ T, Kannan.IsFirstHard k n T) ∧
    (Kannan.language 2 : Set (List Bool)) ∈ PH encBits ∧
    (Kannan.language 2 ∉ SIZE fun n => c * (n + 1) ^ 2) ∧
    ¬∀ L : Language Bool, (L : Set (List Bool)) ∈ SigmaP 2 encBits →
      L ∈ SIZE fun n => c * (n + 1) ^ k :=
  ⟨(Kannan.eventually_exists_isHard k).mono fun _ => Kannan.exists_isFirstHard,
    SigmaP_subset_PH 3 (Kannan.language_mem_SigmaP_three 2),
    Kannan.language_notMem_SIZE 2 c,
    fun h => let ⟨L, hL, hS⟩ := exists_mem_SigmaP_two_notMem_SIZE k; hS c (h L hL)⟩

-- Kannan's statement: no polynomial budget of a fixed degree holds all of `Σ₂ ∩ Π₂`, nor all of
-- `Π₂`.
example (k c : ℕ) :
    (¬∀ L : Language Bool, (L : Set (List Bool)) ∈ SigmaP 2 encBits ∩ PiP 2 encBits →
      L ∈ SIZE fun n => c * (n + 1) ^ k) ∧
    ¬∀ L : Language Bool, (L : Set (List Bool)) ∈ PiP 2 encBits →
      L ∈ SIZE fun n => c * (n + 1) ^ k :=
  let ⟨L, hL, hS⟩ := exists_mem_SigmaP_two_inter_PiP_two_notMem_SIZE k
  ⟨fun h => hS c (h L hL), fun h => hS c (h L hL.2)⟩

end Cslib.Complexity.Tests.Kannan

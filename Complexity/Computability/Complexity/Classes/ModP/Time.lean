/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ModP
public import Complexity.Computability.Complexity.Classes.SharpP.Time

/-!
# Time-bounded parity and modular counting

`Cslib.Complexity.ParityTIME enc t` and `Cslib.Complexity.ModTIME k enc t` are time-parameterized
counterparts of `Cslib.Complexity.ParityP` and `Cslib.Complexity.ModP k`. Membership is the
oddness, respectively a nonzero residue modulo `k`, of a count in
`Cslib.Complexity.SharpTIME enc t`. Such a count is the number of accepting terminal branches of
one fixed nonblocking native counting machine whose branches all halt within time `O(t n)`.

**Why terminal paths.** A terminal path is counted once, so enlarging a sufficient clock does not
change the count (`Cslib.Complexity.SharpTIME_mono`). Padded fair-coin strings, as counted for
`Cslib.Complexity.PPTIME`, behave differently: after a run halts, each further coin doubles its
contribution. That leaves the acceptance probability unchanged but changes residues, so padded
counts suit threshold classes and not modular ones.

As for `Cslib.Complexity.ModP`, the definition is total in `k`. The standard modular counting
classes take `k ≥ 2`, and `ModTIME 2 = ParityTIME` (`Cslib.Complexity.ModTIME_two`). At
polynomial clocks these are the verifier-based classes:
`Cslib.Complexity.mem_ModP_iff_exists_mem_ModTIME` and
`Cslib.Complexity.mem_ParityP_iff_exists_mem_ParityTIME`. Both follow from the equality of
`Cslib.Complexity.SharpP` with the union of the classes `SharpTIME (n ^ d)`
(`Cslib.Complexity.mem_SharpP_iff_exists_mem_SharpTIME`).

## Main definitions

* `Cslib.Complexity.ParityTIME`: odd terminal-path counts within time `O(t n)`.
* `Cslib.Complexity.ModTIME`: terminal-path counts nonzero modulo `k` within time `O(t n)`.

## Main results

* `Cslib.Complexity.ParityTIME_mono`, `Cslib.Complexity.ModTIME_mono`: monotonicity in the clock.
* `Cslib.Complexity.ModTIME_two`: modulo two, a nonzero residue is oddness.
* `Cslib.Complexity.mem_ParityP_iff_exists_mem_ParityTIME`,
  `Cslib.Complexity.mem_ModP_iff_exists_mem_ModTIME`: the polynomial-time unions.

## References

* [C. H. Papadimitriou, S. Zachos, *Two remarks on the power of counting*][PapadimitriouZachos1983]
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {k : ℕ} {t : ℕ → ℕ}

/-- `⊕TIME[t]`: the problems whose members are the instances where some count in
`SharpTIME enc t` is odd. -/
def ParityTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ f ∈ SharpTIME enc t, ∀ a, a ∈ A ↔ Odd (f a)}

/-- `Mod_kTIME[t]`: the problems whose members are the instances where some count in
`SharpTIME enc t` is nonzero modulo `k`. The standard classes take `k ≥ 2`. -/
def ModTIME (k : ℕ) (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ f ∈ SharpTIME enc t, ∀ a, a ∈ A ↔ f a % k ≠ 0}

/-- `ParityTIME` is monotone in the clock. -/
theorem ParityTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    ParityTIME enc t₁ ⊆ ParityTIME enc t₂ := fun _ ⟨f, hf, hA⟩ => ⟨f, SharpTIME_mono h hf, hA⟩

/-- `ModTIME k` is monotone in the clock. -/
theorem ModTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    ModTIME k enc t₁ ⊆ ModTIME k enc t₂ := fun _ ⟨f, hf, hA⟩ => ⟨f, SharpTIME_mono h hf, hA⟩

/-- Modulo two, a nonzero residue is oddness. -/
theorem ModTIME_two : ModTIME 2 enc t = ParityTIME enc t := by
  ext A
  simp only [ModTIME, ParityTIME, Set.mem_ofPred_eq, ← Nat.not_even_iff_odd,
    Nat.even_iff, ne_eq]

/-- **`ModP k` is the union of the classes `ModTIME k (n ^ d)`.** -/
theorem mem_ModP_iff_exists_mem_ModTIME : A ∈ ModP k enc ↔ ∃ d, A ∈ ModTIME k enc (· ^ d) := by
  constructor
  · rintro ⟨f, hf, hA⟩
    obtain ⟨d, hd⟩ := mem_SharpP_iff_exists_mem_SharpTIME.mp hf
    exact ⟨d, f, hd, hA⟩
  · rintro ⟨d, f, hf, hA⟩
    exact ⟨f, SharpTIME.subset_SharpP d hf, hA⟩

/-- **`⊕P` is the union of the classes `ParityTIME (n ^ d)`.** -/
theorem mem_ParityP_iff_exists_mem_ParityTIME :
    A ∈ ParityP enc ↔ ∃ d, A ∈ ParityTIME enc (· ^ d) := by
  simp only [← ModP_two, ← ModTIME_two, mem_ModP_iff_exists_mem_ModTIME]

end Cslib.Complexity

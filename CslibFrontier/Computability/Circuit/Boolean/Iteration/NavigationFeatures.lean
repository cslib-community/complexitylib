/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Depth
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.LabelCircuit
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.NavigationWord

/-!
# Depth and cycle-label feature extraction for pair inputs

Given a pair input `z : BitString (n + n)` split into `inputLeft z` and `inputRight z`, this module
packages the synthesis of the `(n + 3)`-bit transient depth words (`depthWord`) and the cycle-label
components (`canonicalCycle`, `lengthWord`, `phaseWord`) from precomputed depth and cycle-label
circuits.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.inputLeft`: first `n`-bit state of a `(n + n)`-bit input.
* `Cslib.Circuits.Boolean.Iteration.inputRight`: second `n`-bit state of a `(n + n)`-bit input.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_depthWord`: extracts `depthWord f (x z)` from a depth
  circuit.
* `Cslib.Circuits.Boolean.Iteration.synthesis_label_parts`: extracts the canonical cycle
  representative, cycle length word, and phase word from a cycle-label circuit.

## References

* Adapted from lean/Proofs/NavigationFeatures.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n : ℕ}

/-- The first `n`-bit state in a pair input. -/
def inputLeft (z : BitString (n + n)) : BitString n :=
  fun i => z (Fin.castAdd n i)

/-- The second `n`-bit state in a pair input. -/
def inputRight (z : BitString (n + n)) : BitString n :=
  fun i => z (Fin.natAdd n i)

/-- Evaluate a depth circuit on an available state and widen its output to `n + 3` bits. -/
theorem synthesis_depthWord (f : BitString n → BitString n)
    (depth : Circuit signature n (n + 2))
    (hd : ∀ x, word (depth.eval interpretation x) =
      BitVec.ofNat (n + 2) (transientDepth f x))
    (s : Set (BooleanFunction (n + n))) (x : BitString (n + n) → BitString n)
    (hx : wires x ⊆ s) (hz : (fun _ => false) ∈ s) :
    Synthesis interpretation s (wordWires fun z => depthWord f (x z)) depth.size := by
  have hc := Synthesis.circuit (I := interpretation) (s := s) depth
    (fun i z => x z i) (fun bit => hx ⟨bit, rfl⟩)
  let raw := fun z => word (depth.eval interpretation (x z))
  have hraw : wordWires raw ⊆ s ∪ Set.range (fun j z => depth.eval interpretation (x z) j) := by
    rintro _ ⟨bit, rfl⟩
    simp only [raw, getLsbD_word]
    exact Or.inr ⟨bit, rfl⟩
  have hresize := wordWires_setWidth_subset (v := n + 3)
    (s := s ∪ Set.range (fun j z => depth.eval interpretation (x z) j))
    hraw (Or.inl hz)
  have he : (fun z => (raw z).setWidth (n + 3)) = fun z => depthWord f (x z) := by
    funext z
    apply BitVec.eq_of_toNat_eq
    have hlt := transientDepth_lt_two_pow f (x z)
    have hpow2 : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add]; ring
    have hpow3 : 2 ^ (n + 3) = 8 * 2 ^ n := by rw [pow_add]; ring
    have hraw_toNat : (raw z).toNat = transientDepth f (x z) := by
      dsimp only [raw]
      rw [hd (x z), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_setWidth, toNat_depthWord, hraw_toNat, Nat.mod_eq_of_lt (by omega)]
  rw [he] at hresize
  exact hc.trans (Synthesis.of_subset hresize)

/-- Evaluate a cycle-label circuit on an available state and unpack its three fields. -/
theorem synthesis_label_parts (f : BitString n → BitString n)
    (label : Circuit signature n (labelWidth n))
    (hl : ∀ x, label.eval interpretation x = canonicalLabel f x)
    (s : Set (BooleanFunction (n + n))) (x : BitString (n + n) → BitString n)
    (hx : wires x ⊆ s) :
    Synthesis interpretation s
      (wires (fun z => canonicalCycle f (x z)) ∪
        wordWires (fun z => lengthWord f (x z)) ∪
        wordWires (fun z => phaseWord f (x z)))
      label.size := by
  have hc := Synthesis.circuit (I := interpretation) (s := s) label
    (fun i z => x z i) (fun bit => hx ⟨bit, rfl⟩)
  let src := s ∪ Set.range (fun j z => label.eval interpretation (x z) j)
  have hrep : wires (fun z => canonicalCycle f (x z)) ⊆ src := by
    rintro _ ⟨bit, rfl⟩
    refine Or.inr ⟨Fin.castAdd ((n + 3) + (n + 3)) bit, funext fun z => ?_⟩
    have h := congrFun (labelRepresentative_labelBits (canonicalCycle f (x z))
      (BitVec.ofNat (n + 3) (cycleLength f (x z))) (BitVec.ofNat (n + 3) (phase f (x z)))) bit
    simpa only [labelRepresentative, canonicalLabel, hl (x z)] using h
  have hlen : wordWires (fun z => lengthWord f (x z)) ⊆ src := by
    rintro _ ⟨bit, rfl⟩
    refine Or.inr ⟨Fin.natAdd n (Fin.castAdd (n + 3) bit), funext fun z => ?_⟩
    have h := congrArg (fun v => v.getLsbD bit.val)
      (labelLength_labelBits (canonicalCycle f (x z))
        (BitVec.ofNat (n + 3) (cycleLength f (x z))) (BitVec.ofNat (n + 3) (phase f (x z))))
    simpa only [labelLength, canonicalLabel, lengthWord, hl (x z), getLsbD_word] using h
  have hphase : wordWires (fun z => phaseWord f (x z)) ⊆ src := by
    rintro _ ⟨bit, rfl⟩
    refine Or.inr ⟨Fin.natAdd n (Fin.natAdd (n + 3) bit), funext fun z => ?_⟩
    have h := congrArg (fun v => v.getLsbD bit.val)
      (labelPhase_labelBits (canonicalCycle f (x z))
        (BitVec.ofNat (n + 3) (cycleLength f (x z))) (BitVec.ofNat (n + 3) (phase f (x z))))
    simpa only [labelPhase, canonicalLabel, phaseWord, hl (x z), getLsbD_word] using h
  refine hc.trans (Synthesis.of_subset ?_)
  intro g hg
  rcases hg with (hg | hg) | hg
  · exact hrep hg
  · exact hlen hg
  · exact hphase hg

end Cslib.Circuits.Boolean.Iteration

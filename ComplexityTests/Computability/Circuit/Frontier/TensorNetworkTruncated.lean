/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Truncated
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine

/-!
# Tests for contraction at truncation order `ℓ`

The networks have one edge between a row and a column, with tables of `V`-coefficient lists.
With row entries `1, V` and column entries `1 + V, 2`, the contraction is `1 + 3 V`; with row
entries `1 + V, 0` and column entries `1 + V, 5`, it is `(1 + V) ^ 2 = 1 + 2 V + V ^ 2`. The
reduction contracts the networks specialized at digit points of `A_3` by direct summation and
interpolates. At a modulus with enough residues it returns the truncated contraction; through
`DescribedNetwork.interpContract_eq` at the irreducible `FastContraction.modulus 1` this computes
`truncContraction`, which is not computable by itself.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkTruncated

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.DescribedNetwork

/-- Tables of `V`-coefficient lists, read little-endian. -/
def entry (table : List (List ℕ)) (bs : List Bool) : List ℕ :=
  table.getD (BitString.lsbValue bs) []

/-- Direct summation in `A_P` of a specialized network, at the input `(P, fl, r, G)`. -/
def direct : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc (List (List ℕ))) → List ℕ
  | (P, fl, _, G) => sumValue SumOps.galois (specEntry entry) (P, fl) G

/-- Row entries `1, V` and column entries `1 + V, 2`: the contraction `1 + 3 V`. -/
def G₁ : DescribedNetwork (List (List ℕ)) := ⟨1, [([0], [[1], [0, 1]]), ([0], [[1, 1], [2]])]⟩

/-- Row entries `1 + V, 0` and column entries `1 + V, 5`: the contraction `1 + 2 V + V ^ 2`. -/
def G₂ : DescribedNetwork (List (List ℕ)) := ⟨1, [([0], [[1, 1], [0]]), ([0], [[1, 1], [5]])]⟩

/-! ### The reduction, computed -/

-- Three points of `A_3 = (ℤ / 8)[U] / (U ^ 2 + U + 1)` recover `1 + 3 V` at `ℓ = 2`.
example : pointCount 2 G₁ = 3 := rfl

example : interpContract direct [1, 1] 3 2 1 G₁ = [1, 3] := by decide

-- At `ℓ = 1` only the constant coefficient is kept.
example : interpContract direct [1, 1] 3 1 1 G₁ = [1] := by decide

-- Five points of `(ℤ / 8)[U] / (U ^ 3 + U + 1)` recover `1 + 2 V + V ^ 2` at `ℓ = 3`, and the
-- entries are cut to `ℓ` coefficients at `ℓ = 2`.
example : interpContract direct [1, 1, 0] 3 3 1 G₂ = [1, 2, 1] := by decide

example : interpContract direct [1, 1, 0] 3 2 1 G₂ = [1, 2] := by decide

-- Modulo `2 ^ 1` the coefficients are reduced.
example : interpContract direct [1, 1, 0] 1 3 1 G₂ = [1, 0, 1] := by decide

/-! ### The truncated contraction, through correctness -/

/-- Direct summation in `A_P` is correct on every specialized network. -/
theorem direct_correct (P : ℕ) (fl : List ℕ) (r : ℕ)
    (G : DescribedNetwork (SpecDesc (List (List ℕ)))) :
    GaloisRingArith.val P fl (direct (P, fl, r, G)) =
      G.contraction fun d bs => GaloisRingArith.val P fl (specEntry entry d bs) :=
  val_sumValue_galois _ (P, fl) G

/-- The truncated contraction of `G₁` at `ℓ = 2` modulo `8` is `1 + 3 V`. -/
example : G₁.truncContraction entry 3 2 = [1, 3] := by
  rw [← interpContract_eq (core := direct) (r := 1) (FastContraction.irreducible_modulus 1) G₁
    (by decide) fun k _ => direct_correct _ _ _ _]
  decide +kernel

/-- The truncated contraction of `G₂` at `ℓ = 3` modulo `8` is `1 + 2 V + V ^ 2`. -/
example : G₂.truncContraction entry 3 3 = [1, 2, 1] := by
  rw [← interpContract_eq (core := direct) (r := 1) (FastContraction.irreducible_modulus 1) G₂
    (by decide) fun k _ => direct_correct _ _ _ _]
  decide +kernel

/-- The truncated contraction depends only on the entries in `B_{P,ℓ}`: changing the entries by
multiples of `2 ^ P` and past `V ^ ℓ` does not change it. -/
example : G₁.truncContraction entry 1 1 =
    G₁.truncContraction (fun t bs => (entry t bs).map (· + 2)) 1 1 :=
  truncContraction_congr G₁ fun t bs i hi => by
    obtain rfl : i = 0 := by omega
    cases entry t bs <;> simp

end ComplexityTests.TensorNetworkTruncated

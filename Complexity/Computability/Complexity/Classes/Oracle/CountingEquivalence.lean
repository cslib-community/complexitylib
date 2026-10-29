/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.PP
public import Complexity.Computability.Complexity.Classes.PP.Bit
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# PP and counting oracles have the same polynomial-time power

Every PP oracle query is replaced by one bit query to a shifted `#P` count. For a query word `w`,
the new request is the code of `(w, q(|w|))`, where `q` is fixed by the PP verifier. This only
reads the word and its length; it does not decode an instance or recognize valid codes.

The transformed program is fixed before the counting oracle is chosen. Its polynomial-time
certificate follows from open oracle substitution and holds for every external oracle, even one
returning arbitrarily long words: only the first reply bit is read. Against an oracle answering
the specified counting function's bits, the transformed replies induce a language agreeing
with the PP problem on its codes. Arbitrary answers elsewhere are allowed by the original
program's correctness hypothesis.

Together with binary search in the reverse direction, this proves `P^PP = P^#P` for the existing
encoded classes. The result is a uniform polynomial-time simulation, not merely a query bound.

## Main results

* `Cslib.Complexity.PP_subset_PWithSharpPOracle`: one counting-function bit decides a PP problem.
* `Cslib.Complexity.PWithPPOracle_subset_PWithSharpPOracle`: simulate a PP oracle by a bit oracle.
* `Cslib.Complexity.PWithPPOracle_eq_PWithSharpPOracle`: equality of the oracle classes.

## References

* [L. Fortnow, *Counting Complexity*][Fortnow1997], Theorem 4.14 (`P^PP = P^GapP`) and
  Corollary 3.7 (`GapP ⊆ FP^#P`). Here the direct shifted-count construction uses bit queries.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09].
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- Every PP problem is decided by a polynomial-time program making one `#P` bit query. -/
theorem PP_subset_PWithSharpPOracle : PP enc ⊆ PWithSharpPOracle enc := by
  intro A hA
  obtain ⟨f, hf, q, h⟩ := exists_SharpP_testBit_of_mem_PP hA
  exact mem_PWithSharpPOracle_of_testBit hf h

/-- **`P^PP ⊆ P^#P`.** Replace each PP query by one query for a polynomially positioned bit
of a shifted accepting-path count. The program is uniform over every admissible bit oracle,
including arbitrary answers outside the instance codes. -/
theorem PWithPPOracle_subset_PWithSharpPOracle :
    PWithPPOracle enc ⊆ PWithSharpPOracle enc := by
  classical
  rintro L ⟨β, encβ, B, hB, program, hprogram, hL⟩
  obtain ⟨f, hf, p, hp⟩ := exists_SharpP_testBit_of_mem_PP hB
  let request : List Bool → List Bool :=
    fun w => encPair encBits encNat (w, p.eval w.length)
  have hrequest : ComputableInPolyTime request encBits encBits :=
    ComputableInPolyTime.encoding_comp
      (ComputableInPolyTime.id'.prod
        (ComputableInPolyTime.unary_to_binary.comp
          (by fun_prop : ComputableInPolyTime
            (fun w : List Bool => p.eval w.length) encBits encUnary)))
  let handler : Unit × List Bool → WordQueryComp Unit (List Bool) :=
    fun q => List.take 1 <$> OracleComp.query ((), request q.2)
  refine ⟨β, encβ, f, hf, fun a => OracleComp.interpret handler (program a),
    hprogram.interpret_bitQueries hrequest.tidy, fun A hA a => ?_⟩
  let B' : Set (List Bool) := request ⁻¹' A
  have hB' : ∀ b, encβ b ∈ B' ↔ b ∈ B := fun b =>
    (hA b (p.eval (encβ b).length)).trans (hp b).symm
  have hhandler : (fun q => OracleComp.interpret (m := Id) (languageOracle A) (handler q)) =
      languageOracle B' := by
    funext q
    simp only [handler, OracleComp.interpret_map, OracleComp.interpret_query,
      languageOracle_apply, B', Set.mem_preimage]
    rfl
  dsimp only
  rw [hL B' hB' a, OracleComp.interpret_interpret, hhandler]

/-- **`P^PP = P^#P`** under the encoded, bit-by-bit counting oracle convention. -/
theorem PWithPPOracle_eq_PWithSharpPOracle (enc : α ↪ List Bool) :
    PWithPPOracle enc = PWithSharpPOracle enc :=
  Set.Subset.antisymm PWithPPOracle_subset_PWithSharpPOracle
    PWithSharpPOracle_subset_PWithPPOracle

end Cslib.Complexity

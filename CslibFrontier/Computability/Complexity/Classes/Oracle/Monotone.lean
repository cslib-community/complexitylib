/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution

/-!
# Monotonicity of the oracle classes under reductions

If the oracle language `A` reduces to `B` by a polynomial-time map `g`, a computation relative to
`A` becomes one relative to `B`: every request `w` is replaced by the request `g w`, of which one
reply bit is kept (`Cslib.Complexity.ComputableInPolyTimeWithOracle.of_polyTimeReducible`). The
certificate is stateless open oracle substitution
(`Cslib.Probability.IsOraclePPTOn.interpret_bitQueries`): the handler answering requests to `A` is
itself an oracle program querying `B`, charged for computing `g w` and for reading one bit of the
reply. Hence `P^A ⊆ P^B` and `NP^A ⊆ NP^B`
(`Cslib.Complexity.PolyTimeReducible.PWithOracle_subset`,
`Cslib.Complexity.PolyTimeReducible.NPWithOracle_subset`), and polynomial-time equivalent oracles
give the same classes.

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.of_polyTimeReducible`: oracle monotonicity.
* `Cslib.Complexity.PolyTimeReducible.PWithOracle_subset`,
  `Cslib.Complexity.PolyTimeReducible.NPWithOracle_subset`: `P^A ⊆ P^B` and `NP^A ⊆ NP^B`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4.
-/

public section

namespace Cslib.Complexity

open Probability _root_.Turing.MultiTapeTM

variable {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}

open Classical in
/-- **Oracle monotonicity.** If `A` reduces to `B` in polynomial time, then polynomial time
relative to `A` is polynomial time relative to `B`: every request `w` is replaced by the request
`g w`, keeping one bit of the reply. -/
theorem ComputableInPolyTimeWithOracle.of_polyTimeReducible {A B : Set (List Bool)} {f : α → β}
    (hAB : PolyTimeReducible encBits encBits A B)
    (hf : ComputableInPolyTimeWithOracle A f input output) :
    ComputableInPolyTimeWithOracle B f input output := by
  obtain ⟨g, hg, hgAB⟩ := hAB
  obtain ⟨program, hcert, hprogram⟩ := hf
  -- a request to `A` becomes a request to `B`, of which one reply bit is kept
  let G : Unit × List Bool → WordQueryComp Unit (List Bool) := fun q =>
    List.take 1 <$> OracleComp.query ((), g q.2)
  refine ⟨fun a => OracleComp.interpret G (program a), ?_, fun a => ?_⟩
  · -- substitute the handler answering requests to `A` through `B`
    exact hcert.interpret_bitQueries hg.tidy
  · rw [OracleComp.interpret_interpret, ← hprogram a]
    congr 1 with q : 1
    simp only [G, OracleComp.interpret_map, OracleComp.interpret_query, languageOracle_apply]
    rw [show decide (g q.2 ∈ B) = decide (q.2 ∈ A) from decide_eq_decide.mpr (hgAB q.2).symm]
    rfl

/-- **`P` relative to an oracle is monotone under polynomial-time reductions of the oracle.** -/
theorem PolyTimeReducible.PWithOracle_subset {A B : Set (List Bool)}
    (hAB : PolyTimeReducible encBits encBits A B) (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ PWithOracle B enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, hf.of_polyTimeReducible hAB, hL⟩

/-- **`NP` relative to an oracle is monotone under polynomial-time reductions of the oracle.** -/
theorem PolyTimeReducible.NPWithOracle_subset {A B : Set (List Bool)}
    (hAB : PolyTimeReducible encBits encBits A B) (enc : α ↪ List Bool) :
    NPWithOracle A enc ⊆ NPWithOracle B enc := fun _ ⟨p, V, hV, hL⟩ =>
  ⟨p, V, hV.of_polyTimeReducible hAB, hL⟩

end Cslib.Complexity

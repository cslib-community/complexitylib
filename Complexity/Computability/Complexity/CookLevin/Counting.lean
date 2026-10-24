/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Completeness
public import Complexity.Computability.Complexity.Problems.SharpSAT
import Complexity.Computability.Complexity.CookLevin.Parsimonious
import Complexity.Computability.Complexity.CookLevin.PolyTime

/-!
# The parsimonious Cook–Levin theorem

The Cook–Levin reduction is polynomial-time (`computableTidilyInPolyTime_reduce`) and
parsimonious (`modelCount_reduce`): applied to the verifier of a function `f` in `#P`, it maps an
instance `a` to a formula with exactly `f a` satisfying assignments. Together with
`SharpSAT.mem_SharpP`, this proves that `#SAT` is `#P`-complete under parsimonious polynomial-time
reductions [Valiant][Valiant1979], [Papadimitriou, Chapter 18][Papadimitriou94].

The count is exact: `#P` counts the certificates of exactly the verifier's length, the tableau has
one variable for each of their bits, and all its other variables are determined by them.

## Main results

* `Cslib.Complexity.CookLevin.SharpSAT_sharpPHard`: every function in `#P` reduces
  parsimoniously to `#SAT`.
* `Cslib.Complexity.CookLevin.SharpSAT_sharpPComplete`: `#SAT` is `#P`-complete.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Chapter 18.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 17.3.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Cslib.Logic.PL

/-- **The parsimonious Cook–Levin theorem**: every function in `#P` reduces parsimoniously to
`#SAT`, through the tableau of its verifier. -/
theorem SharpSAT_sharpPHard : SharpPHard encCNF SharpSAT := by
  rintro α enc f ⟨p, V, hV, hf⟩
  obtain ⟨t, s, ht, -, k, State, hfin, tm, htm⟩ := hV.tidy
  obtain ⟨c, d, ht⟩ := ht.exists_le
  have := Fintype.ofFinite State
  classical
  have htm' := htm.mono (fun x => ht x) (fun _ => le_rfl)
  exact ⟨reduce tm p c d enc, (computableInPolyTime_reduce tm p c d enc), fun a => by
    rw [hf a, SharpSAT, modelCount_reduce a fun w _ => (htm' (a, w)).runFrom_initCfg]⟩

/-- **`#SAT` is `#P`-complete** under parsimonious polynomial-time reductions. -/
theorem SharpSAT_sharpPComplete : SharpPComplete encCNF SharpSAT :=
  ⟨SharpSAT.mem_SharpP, SharpSAT_sharpPHard⟩

end Cslib.Complexity.CookLevin

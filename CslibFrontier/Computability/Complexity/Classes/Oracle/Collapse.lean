/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.BakerGillSolovay
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Space
public import CslibFrontier.Computability.Complexity.Classes.Oracle.TQBF

/-!
# An oracle relative to which `P` and `NP` coincide

Relative to a `PSPACE`-complete oracle language `A`, polynomial time and nondeterministic
polynomial time are both polynomial space:

`NP^A ⊆ PSPACE ⊆ P^A ⊆ NP^A`

[Baker, Gill and Solovay][BakerGillSolovay1975] [Arora and Barak, Theorem 3.7][AroraBarak09].
The first inclusion holds for every oracle in `PSPACE`
(`Cslib.Complexity.NPWithOracle_subset_PSPACE`). The second holds for every `PSPACE`-hard oracle:
a problem in `PSPACE` reduces to `A` in polynomial time, and one query to `A` answers the reduced
instance (`Cslib.Complexity.PSPACE_subset_PWithOracle`). The words encoding true closed quantified
Boolean formulas form such an oracle (`Cslib.Complexity.image_TQBF_pspaceComplete`), so
`P^TQBF = NP^TQBF` (`Cslib.Complexity.PWithOracle_image_TQBF_eq_NPWithOracle`).

With `Cslib.Complexity.exists_PWithOracle_ssubset_NPWithOracle`, this is the theorem of Baker,
Gill and Solovay (`Cslib.Complexity.baker_gill_solovay`): there are oracles relative to which
`P = NP` and relative to which `P ≠ NP`, so no proof that relativizes settles the question.

## Main results

* `Cslib.Complexity.PSPACE_subset_PWithOracle`: relative to a `PSPACE`-hard oracle, `PSPACE` is
  within `P`.
* `Cslib.Complexity.PWithOracle_eq_PSPACE`, `Cslib.Complexity.NPWithOracle_eq_PSPACE`,
  `Cslib.Complexity.PWithOracle_eq_NPWithOracle`: relative to a `PSPACE`-complete oracle,
  `P = NP = PSPACE`.
* `Cslib.Complexity.PWithOracle_image_TQBF_eq_NPWithOracle`,
  `Cslib.Complexity.exists_PWithOracle_eq_NPWithOracle`: relative to `TQBF`, `P = NP`.
* `Cslib.Complexity.baker_gill_solovay`: relative to some oracle `P = NP`, relative to another
  `P ≠ NP`.

## References

* [T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP Question*][BakerGillSolovay1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {A : Set (List Bool)}

/-- **`PSPACE` is within `P` relative to a `PSPACE`-hard oracle**: a problem in `PSPACE` reduces
to the oracle language in polynomial time, and one query answers the reduced instance. -/
theorem PSPACE_subset_PWithOracle (hA : PSPACEHard encBits A) (enc : α ↪ List Bool) :
    PSPACE enc ⊆ PWithOracle A enc := fun L hL =>
  (hA enc L hL).mem_PWithOracle (mem_PWithOracle_self A)

/-- **Relative to a `PSPACE`-complete oracle, `P = PSPACE`.** -/
theorem PWithOracle_eq_PSPACE (hA : PSPACEComplete encBits A) (enc : α ↪ List Bool) :
    PWithOracle A enc = PSPACE enc :=
  (PWithOracle_subset_PSPACE hA.1).antisymm (PSPACE_subset_PWithOracle hA.2 enc)

/-- **Relative to a `PSPACE`-complete oracle, `NP = PSPACE`.** -/
theorem NPWithOracle_eq_PSPACE (hA : PSPACEComplete encBits A) (enc : α ↪ List Bool) :
    NPWithOracle A enc = PSPACE enc :=
  (NPWithOracle_subset_PSPACE hA.1).antisymm
    ((PSPACE_subset_PWithOracle hA.2 enc).trans (PWithOracle_subset_NPWithOracle A enc))

/-- **Relative to a `PSPACE`-complete oracle, `P = NP`** [Arora and Barak, Theorem
3.7][AroraBarak09]. -/
theorem PWithOracle_eq_NPWithOracle (hA : PSPACEComplete encBits A) (enc : α ↪ List Bool) :
    PWithOracle A enc = NPWithOracle A enc :=
  (PWithOracle_eq_PSPACE hA enc).trans (NPWithOracle_eq_PSPACE hA enc).symm

/-- **Baker–Gill–Solovay, the collapse** [BakerGillSolovay1975], [Arora and Barak, Theorem
3.7][AroraBarak09]: relative to the words encoding true closed quantified Boolean formulas, `P`
and `NP` coincide, for every encoding of instances. -/
theorem PWithOracle_image_TQBF_eq_NPWithOracle (enc : α ↪ List Bool) :
    PWithOracle (encQBF '' TQBF) enc = NPWithOracle (encQBF '' TQBF) enc :=
  PWithOracle_eq_NPWithOracle image_TQBF_pspaceComplete enc

/-- **Baker–Gill–Solovay**: relative to some oracle language, `P = NP`. -/
theorem exists_PWithOracle_eq_NPWithOracle :
    ∃ A : Set (List Bool), PWithOracle A encBits = NPWithOracle A encBits :=
  ⟨_, PWithOracle_image_TQBF_eq_NPWithOracle encBits⟩

/-- **The theorem of Baker, Gill and Solovay** [BakerGillSolovay1975], [Arora and Barak, Theorem
3.7][AroraBarak09]: there is an oracle language relative to which `P = NP`, and one relative to
which `P ≠ NP`. -/
theorem baker_gill_solovay :
    (∃ A : Set (List Bool), PWithOracle A encBits = NPWithOracle A encBits) ∧
      ∃ B : Set (List Bool), PWithOracle B encBits ≠ NPWithOracle B encBits :=
  ⟨exists_PWithOracle_eq_NPWithOracle, exists_PWithOracle_ne_NPWithOracle⟩

end Cslib.Complexity

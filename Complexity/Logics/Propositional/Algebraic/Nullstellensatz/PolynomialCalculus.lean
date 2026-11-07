/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Algebraic.Nullstellensatz.Proof
public import Complexity.Logics.Propositional.Algebraic.PolynomialCalculus.Proof

/-!
# From polynomial calculus to Nullstellensatz

Every polynomial appearing in a polynomial calculus proof from `F` has a Nullstellensatz proof
from the same inputs
(`Cslib.Logic.PL.NS.exists_isProof_of_pc`). The conversion follows
the inference rules: an input line uses its unit multiplier, linear combinations combine the
multiplier families, and multiplication by a variable multiplies every multiplier by that
variable. It gives a certificate for each line, with no size or degree bound.

## Main results

* `Cslib.Logic.PL.NS.exists_isProof_of_pc`: every line of a PC
  proof has an NS certificate.
-/

public section

namespace Cslib.Logic.PL.NS

variable {V R : Type*} [CommSemiring R]

/-- Every polynomial `q` appearing in a PC proof from `F` admits an NS certificate from `F`. -/
theorem exists_isProof_of_pc {F ls : List (MvPolynomial V R)}
    {q : MvPolynomial V R} (hls : PC.IsProof F ls) (hq : q ∈ ls) :
    ∃ P : Fin F.length → MvPolynomial V R, IsProof F P q := by
  induction hls generalizing q with
  | nil => simp at hq
  | mem _ hp ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
      exact ⟨_, IsProof.single F i⟩
    · exact ih hq
  | linear a b _ hp hq' ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · obtain ⟨P, hP⟩ := ih hp
      obtain ⟨Q, hQ⟩ := ih hq'
      exact ⟨_, (hP.mul_left (MvPolynomial.C a)).add (hQ.mul_left (MvPolynomial.C b))⟩
    · exact ih hq
  | mulVar v _ hp ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · obtain ⟨P, hP⟩ := ih hp
      exact ⟨_, hP.mul_left (MvPolynomial.X v)⟩
    · exact ih hq

end Cslib.Logic.PL.NS

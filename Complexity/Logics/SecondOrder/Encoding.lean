/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Encoding
public import Complexity.Logics.SecondOrder.Existential

/-!
# Encodings of finite families of relation variables

`Cslib.Logic.ESO.varLanguage.vocabulary` converts an enumeration of finitely many relation
variables into the vocabulary that serializes their truth tables. It retains the declared
arity of each variable, including nullary relations, and admits an empty family.

## Main definitions

* `Cslib.Logic.ESO.varLanguage.vocabulary`: the vocabulary induced by a variable enumeration.

## Main results

* `Cslib.Logic.ESO.varLanguage.arity_vocabulary`: table arities are the declared arities.
* `Cslib.Logic.ESO.varLanguage.index_vocabulary`: table indices are enumeration positions.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.ESO

namespace varLanguage

variable {ι : Type} {m : ℕ} (arity : ι → ℕ) (e : Fin m ≃ ι)

/-- Enumerate relation variables in the supplied order, retaining their arities. -/
@[expose]
def vocabulary : Vocabulary (varLanguage arity) where
  count := m
  symbol := e.trans (Equiv.sigmaFiberEquiv arity).symm

/-- The arity of a variable in the enumeration is its declared arity. -/
@[simp]
theorem arity_vocabulary (j : Fin m) : (vocabulary arity e).arity j = arity (e j) :=
  rfl

/-- A relation variable's table is at its position in the supplied enumeration. -/
@[simp]
theorem index_vocabulary (r : Σ k, (varLanguage arity).Relations k) :
    (vocabulary arity e).index r = (e.symm r.2.1 : ℕ) :=
  rfl

end varLanguage

end Cslib.Logic.ESO

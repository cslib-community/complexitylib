/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# A unitary on the first register

A quantum system with two registers has computational basis `ι × κ`. A unitary `U` on the first
register acts on the whole system as `U ⊗ I`, the Kronecker product with the identity
(`Cslib.Quantum.onFirst`), with entries `(U ⊗ I)((i, k), (i', k')) = U(i, i') · [k = k']`.

## Main definitions

* `Cslib.Quantum.onFirst`: the unitary `U ⊗ I` on `ι × κ`.

## Main results

* `Cslib.Quantum.onFirst_apply`: its entries.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped Kronecker

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The unitary `U ⊗ I` acting as `U` on the first register of `ι × κ` and trivially on the
second. -/
noncomputable def onFirst (U : unitaryGroup ι ℂ) : unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix κ κ ℂ), kronecker_mem_unitary U.2 (one_mem _)⟩

theorem onFirst_apply (U : unitaryGroup ι ℂ) (p q : ι × κ) :
    (onFirst (κ := κ) U : Matrix (ι × κ) (ι × κ) ℂ) p q =
      (U : Matrix ι ι ℂ) p.1 q.1 * if p.2 = q.2 then 1 else 0 := by
  rfl

end Cslib.Quantum

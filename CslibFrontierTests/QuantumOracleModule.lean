/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Quantum.Oracle.Code
import CslibFrontier.Computability.Circuit.Quantum.Oracle.ValueQuery

/-! Clients of the public oracle-circuit API under module encapsulation. -/

open Cslib.Quantum

-- One mixed program exercises ordinary gates, phase gates and oracle queries.
example (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    let A : Fin 1 ↪ Fin 2 := ⟨![0], fun i j _ => Subsingleton.elim i j⟩
    OracleCircuit.toCircuit 2 H
      [.gate (false, true, 0, []), .gate (true, false, 0, []), .query] =
      [⟨1, Gate.hadamard, A⟩, PlacedGate.ctrlPhase false A,
        xorQuery H (Fin.castLEEmb (by decide))] := by
  simp only [OracleCircuit.toCircuit, List.filterMap_cons, OracleGateCode.toPlacedGate?,
    PhaseGateCode.toPlacedGate?, GateCode.toPlacedGate?, show 0 < 2 by decide,
    show 1 + 1 ≤ 2 by decide, ↓reduceDIte, List.filterMap_nil]
  rfl

-- The forward equation lets a client use an arbitrary basis string directly.
example {a b m : ℕ} (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) (z : Fin m → Bool) :
    (xorQuery H A).eval (ket z) = ket ((queryRegisters A).symm
      (fun i => z (A (Fin.castAdd b i)),
        (fun i => z (A (Fin.natAdd a i))) + H (fun i => z (A (Fin.castAdd b i))),
        fun j => z j.1)) := by
  simpa only [← queryRegisters_apply A z, Equiv.symm_apply_apply] using
    xorQuery_eval_ket H A (fun i => z (A (Fin.castAdd b i)))
      (fun i => z (A (Fin.natAdd a i))) (fun j => z j.1)

-- The same API transports a concrete query into the existing value-query interface.
example :
    let A := Function.Embedding.refl (Fin (1 + 1))
    let reindex := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (queryRegisters (a := 1) (b := 1) A)
    reindex ((xorQuery (id : (Fin 1 → Bool) → Fin 1 → Bool) A).eval (ket ![true, false])) =
      valueOracle addStep id (reindex (ket ![true, false])) :=
  xorQuery_eq_valueOracle (a := 1) (b := 1) (m := 2) id
    (Function.Embedding.refl _) (ket ![true, false])

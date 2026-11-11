/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #4383 M5.4d; not for merge)

public import CslibFrontier.Computability.Circuit.Boolean.Oracle
public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import CslibFrontier.Computability.Circuit.CompositionDepth
public import CslibFrontier.Computability.Circuit.FanIn
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Computability.Circuit.Simulation

/-!
# Spike: one selection round of an oracle circuit

Scratch for #4383 (M5.4d). Not for merge.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ τ : Signature} {n m g : ℕ}

/-- Translating operations composes the cost with the translation. -/
theorem Program.cost_mapOp (φ : σ.Hom τ) (p : Program σ n g) (cost : τ.Op → ℕ) :
    (p.mapOp φ).cost cost = p.cost (cost ∘ φ) := by
  induction p with
  | empty => rfl
  | gate p line ih => simp [ih]

/-- A program whose operations all cost zero has weighted depth zero at every gate. -/
theorem Program.depthsWith_eq_zero (cost : σ.Op → ℕ) (p : Program σ n g)
    (h : ∀ k, cost (p.lines k).op = 0) (k : Fin g) : p.depthsWith cost k = 0 :=
  Nat.eq_zero_of_le_zero <| (p.depthsWith_le_mul_depths (b := 0) (fun k => (h k).le) k).trans
    (by simp)

/-- A circuit whose operations all cost zero has weighted depth zero. -/
theorem Circuit.depthWith_eq_zero (cost : σ.Op → ℕ) (c : Circuit σ n m)
    (h : ∀ k, cost (c.program.lines k).op = 0) : c.depthWith cost = 0 :=
  Nat.eq_zero_of_le_zero <| (c.depthWith_le_mul_depth (b := 0) fun k => (h k).le).trans (by simp)

end Cslib.Circuits

namespace Cslib.Circuits.Boolean

variable {n m g : ℕ}

/-- The lines of a translated program are the translated lines. -/
theorem Program.lines_mapOp_op (p : Program signature n g) (k : Fin g) :
    ((p.mapOp toOracle).lines k).op = OracleOp.base (p.lines k).op := by
  induction p with
  | empty => exact k.elim0
  | gate p line ih =>
    induction k using Fin.lastCases with
    | last => simp [toOracle, DFunLike.coe]
    | cast k => simpa using ih k

/-- A De Morgan circuit, viewed in the oracle basis, has no oracle gates. -/
@[simp] theorem cost_mapOp_toOracle (c : Circuit signature n m) :
    (c.mapOp toOracle).program.cost OracleOp.queryWeight = 0 :=
  (Program.cost_mapOp toOracle c.program _).trans <|
    (c.program.cost_const 0).trans (Nat.zero_mul _)

/-- A De Morgan circuit, viewed in the oracle basis, has oracle depth zero. -/
@[simp] theorem depthWith_mapOp_toOracle (c : Circuit signature n m) :
    (c.mapOp toOracle).depthWith OracleOp.queryWeight = 0 :=
  Circuit.depthWith_eq_zero _ _ fun k =>
    (congrArg OracleOp.queryWeight (Program.lines_mapOp_op c.program k)).trans rfl

/-- Every De Morgan circuit has fan-in at most two. -/
theorem fanInAtMost_two (c : Circuit signature n m) : c.FanInAtMost 2 :=
  Program.fanInAtMost_iff.2 fun k => by
    rcases (c.program.lines k).op with _ | _ | _ | _ <;> simp

end Cslib.Circuits.Boolean

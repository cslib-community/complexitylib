/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Program

/-!
# Fixed registers of the per-record witness controller

This internal invariant contains only ordinary runtime register equalities. It packages
neither execution nor witness, fit, sparse-count or time certificates. The actual header
establishes it from the original scalar words and record; the query loop preserves it.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

/-- The controller's fixed arguments and the verifier's shared array/interval arguments. -/
structure Fixed (n firstVertex spanLen out queryBase queryCount : ℕ) (x : Data 400) : Prop where
  /-- Absolute answer pointer. -/
  output : x.regs Reg.output = out
  /-- Original interleaved query pointer. -/
  queries : x.regs Reg.queries = queryBase
  /-- Actual occurrence count. -/
  count : x.regs Reg.count = queryCount
  /-- Original outer dimension. -/
  size : x.regs Reg.size = n
  /-- Original first piece vertex. -/
  first : x.regs Reg.first = firstVertex
  /-- Number of original piece vertices. -/
  length : x.regs Reg.length = spanLen
  /-- Constant one. -/
  one : x.regs Reg.one = 1
  /-- Constant zero. -/
  zero : x.regs Reg.zero = 0
  /-- Original signed A–B pointer delivered to the verifier. -/
  ab : x.regs (scanBank WitnessScan.Reg.ab) = 5
  /-- Original signed B–C pointer delivered to the verifier. -/
  bc : x.regs (scanBank WitnessScan.Reg.bc) = 5 + n * n
  /-- Original signed A–C pointer delivered to the verifier. -/
  ac : x.regs (scanBank WitnessScan.Reg.ac) = 5 + n * n + n * n
  /-- Verifier outer dimension. -/
  scanSize : x.regs (scanBank WitnessScan.Reg.size) = n
  /-- Verifier original first vertex. -/
  scanFirst : x.regs (scanBank WitnessScan.Reg.first) = firstVertex
  /-- Verifier interval length. -/
  scanLength : x.regs (scanBank WitnessScan.Reg.length) = spanLen

/-- Reuse the fixed ABI under a frame that excludes the query cursor, loaded coordinates,
verifier scratch and result/counter registers. -/
theorem Fixed.of_frame {n first length out queries count : ℕ} {x y : Data 400}
    (hx : Fixed n first length out queries count x)
    (he : ∀ i : Fin 400, i.val < 326 ∨ i = Reg.one ∨ i = Reg.zero ∨
      (345 ≤ i.val ∧ i.val ≤ 348) ∨ (351 ≤ i.val ∧ i.val ≤ 352) →
      y.regs i = x.regs i) : Fixed n first length out queries count y where
  output := (he _ (by decide)).trans hx.output
  queries := (he _ (by decide)).trans hx.queries
  count := (he _ (by decide)).trans hx.count
  size := (he _ (by decide)).trans hx.size
  first := (he _ (by decide)).trans hx.first
  length := (he _ (by decide)).trans hx.length
  one := (he _ (by decide)).trans hx.one
  zero := (he _ (by decide)).trans hx.zero
  ab := (he _ (by decide)).trans hx.ab
  bc := (he _ (by decide)).trans hx.bc
  ac := (he _ (by decide)).trans hx.ac
  scanSize := (he _ (by decide)).trans hx.scanSize
  scanFirst := (he _ (by decide)).trans hx.scanFirst
  scanLength := (he _ (by decide)).trans hx.scanLength

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

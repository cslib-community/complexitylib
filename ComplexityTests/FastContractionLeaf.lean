/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionLeaf

/-! # The leaves of the fast contraction machine: checked instances

The packet shape on a root and on a call with a packet vertex, the row ports and target modes it
bounds, and an input meeting every hypothesis of the leaf bound. -/

namespace ComplexityTests.FastContractionLeaf

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.FastContraction
  Cslib.Circuits.Frontier.NativePacket Cslib.Circuits.Frontier.ContractionSchedule

/-- Two rows `0, 1` and two columns `2, 3`, joined by edges `0 : 0 → 2` and `1 : 1 → 3`. -/
def pair : ℕ × ExplicitTensorNetwork ℕ :=
  (2, ⟨2, [([0], [1, 2]), ([1], [3, 4]), ([0], [1, 1]), ([1], [1, 0])]⟩)

-- The root of `(1, pair)`: scale `2`, two edges, precision `1`.
example : (root (1, pair)).scale = 2 ∧ (root (1, pair)).edges = 2 ∧
    (root (1, pair)).prec = 1 := by decide

-- The root has the packet shape: its vertices are tables.
example : PacketShape (root (1, pair)) := packetShape_root _

-- At `s = 2`, the root meets every hypothesis of `exists_leafCertificate_le` with `C = 1` and
-- `c = 2`, for every `s₀`: `leafSize 2 = 2` and `1 ≤ 2 ^ 2`.
example (s₀ : ℕ) : 2 ≤ 2 ∧ 2 ≤ (root (1, pair)).scale ∧ (root (1, pair)).scale ≤ 1 * 2 ∧
    PacketShape (root (1, pair)) ∧ (root (1, pair)).edges ≤ 2 * (root (1, pair)).scale ∧
    (s₀ ≤ 2 → (root (1, pair)).edges ≤ leafSize (root (1, pair)).scale ∧
      (root (1, pair)).prec ≤ (root (1, pair)).scale ^ 2) :=
  ⟨le_rfl, by decide, by decide, packetShape_root _, by decide, fun _ => by decide⟩

/-- A packet context with `a = 1` slot bit, `i = 0`, two tiles, precision `1` and one exponent per
tile. -/
def ctx : PacketCtx where
  p := 1
  fl := [1]
  a := 1
  L := 2
  i := 0
  tiles := 2
  t := 1
  nb := 1
  e₁ := true
  e₂ := false
  differ := true
  cols := []
  ζ := [0]

/-- A packet vertex with a row port in slot `0` and a column port in slot `1`. -/
def packetVertex : List ℕ × VertexDesc := ([0, 1], .inr (ctx, [(true, 0), (false, 1)], [0, 0]))

/-- A call at scale `4` and precision `1` whose network is the packet vertex alone. -/
def packetCall : Call := ((4, 1, 3, 1, [1], 0), ⟨2, [packetVertex]⟩)

-- The packet vertex has one row port, and at most `2 ⬝ 1` target modes.
example : packetVertex.2.rowPorts [true, false] = 1 := by decide
example : packetVertex.2.modes ≤ 2 := by decide

-- The packet shape is not vacuous on packets. Here `a = 1` exceeds `⌊log₂ 4⌋ / 32768 = 0`, so the
-- shape fails; a call one level down the schedule has `a ≤ ⌊log₂ s⌋ / 32768`.
example : ¬ PacketShape packetCall := by
  intro h
  have h1 : 1 ≤ Nat.log 2 4 / 32768 := (h packetVertex (by simp [packetCall]) _ rfl).2.1
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.log_pow (by norm_num)] at h1
  omega

-- From scale `2 ^ 32768` on, the same vertex has the packet shape.
example (s : ℕ) (hs : 32768 ≤ Nat.log 2 s) :
    PacketShape ((s, 1, 3, 1, [1], 0), ⟨2, [packetVertex]⟩) := by
  intro v hv d hd
  simp only [List.mem_singleton] at hv
  subst hv
  simp only [packetVertex, Sum.inr.injEq] at hd
  subst hd
  refine ⟨by decide, ?_, by decide, le_rfl, by decide, by decide⟩
  change 1 ≤ Nat.log 2 s / 32768
  omega

end ComplexityTests.FastContractionLeaf

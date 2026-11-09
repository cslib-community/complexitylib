/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Protocol

/-!
# Karchmer–Wigderson games

In the *Karchmer–Wigderson game* of a Boolean function `f` on the coordinates `ι`, Alice holds an
input `x : ι → Bool` with `f x = 1`, Bob holds an input `y` with `f y = 0`, and they must name a
coordinate where `x` and `y` differ (`DiffersAt`). In the *monotone* game they must name a
coordinate that is one in `x` and zero in `y` (`ExceedsAt`), which exists when `f` is monotone.
Protocols for both games are deterministic protocols naming a coordinate (`KWProtocol`). The
Karchmer–Wigderson theorems identify the communication complexities of these games with the least
depths of De Morgan and of monotone formulas [KarchmerWigderson1990],
[Jukna, Section 3.3][Jukna2012], [Kushilevitz and Nisan, Chapter 10][KushilevitzNisan1997].

## Main definitions

* `Cslib.Communication.DiffersAt`: the Karchmer–Wigderson relation.
* `Cslib.Communication.ExceedsAt`: the monotone Karchmer–Wigderson relation.
* `Cslib.Communication.KWProtocol`: protocols for Karchmer–Wigderson games.

## Main results

* `Cslib.Communication.ExceedsAt.differsAt`: a solution of the monotone game solves the game.

## References

* [M. Karchmer and A. Wigderson, *Monotone circuits for connectivity require super-logarithmic
  depth*][KarchmerWigderson1990]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

variable {ι : Type*}

/-- The Karchmer–Wigderson relation: Alice's input `x` and Bob's input `y` differ at
coordinate `i`. -/
def DiffersAt (x y : ι → Bool) (i : ι) : Prop :=
  x i ≠ y i

@[simp] theorem differsAt_iff {x y : ι → Bool} {i : ι} : DiffersAt x y i ↔ x i ≠ y i :=
  Iff.rfl

/-- Exchanging the inputs keeps the coordinates where they differ. -/
theorem DiffersAt.symm {x y : ι → Bool} {i : ι} (h : DiffersAt x y i) : DiffersAt y x i :=
  Ne.symm h

/-- The monotone Karchmer–Wigderson relation: coordinate `i` is one in Alice's input `x` and zero
in Bob's input `y`. -/
def ExceedsAt (x y : ι → Bool) (i : ι) : Prop :=
  x i = true ∧ y i = false

@[simp] theorem exceedsAt_iff {x y : ι → Bool} {i : ι} :
    ExceedsAt x y i ↔ x i = true ∧ y i = false :=
  Iff.rfl

/-- A solution of the monotone Karchmer–Wigderson game is a solution of the Karchmer–Wigderson
game. -/
theorem ExceedsAt.differsAt {x y : ι → Bool} {i : ι} (h : ExceedsAt x y i) : DiffersAt x y i := by
  simp [h.1, h.2]

/-- Protocols for Karchmer–Wigderson games on the coordinates `ι`: Alice and Bob hold inputs
`ι → Bool` and the protocol names a coordinate. -/
abbrev KWProtocol (ι : Type*) : Type _ :=
  Protocol (ι → Bool) (ι → Bool) ι

end Cslib.Communication

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.KarchmerWigderson
public import Mathlib.Data.Finset.Defs

/-!
# Protocols with messages from an alphabet

In a *round protocol* (`RoundProtocol X Y M Z d`) Alice holds `x : X`, Bob holds `y : Y`, and the
players send at most `d` messages from an alphabet `M`: at each step the speaker, who may depend on
the messages so far, sends one message computed from their input, and the protocol ends with an
output in `Z` determined by the transcript (`RoundProtocol.run`). Bit protocols are the case of
one-bit messages: a bit protocol of depth at most `d` is a round protocol with `d` messages from
`Bool` (`RoundProtocol.ofProtocol`). Counting messages from a larger alphabet rather than bits is
the measure of protocols with few rounds [Kushilevitz and Nisan, Chapter 4][KushilevitzNisan1997].
As for bit protocols, a round protocol *solves* a relation `R` on `A × B` when its output does
(`RoundProtocol.Solves`, through `Communication.Solves`). Exchanging the speakers exchanges the
inputs (`RoundProtocol.run_swapPlayers`), and relabelling the inputs is precomposition
(`RoundProtocol.run_comap`).

For the Karchmer–Wigderson game on the coordinates `ι` both players hold inputs `ι → Bool` and the
protocol names a coordinate (`KWRoundProtocol`). Such a protocol solves the game of a Boolean
function `f` when, for every `x` with `f x = false` held by Alice and `y` with `f y = true` held by
Bob, the inputs differ at the named coordinate (`RoundProtocol.SolvesKW`). This is the model of the
top-down lower bounds of Korten [Korten, Section 1.1][Korten2026], in which a circuit of AND/OR
depth `d` with `w` wires gives a protocol with `d` messages from an alphabet of size `w`.
Exchanging the speakers solves the game of the negated function
(`RoundProtocol.SolvesKW.swapPlayers`).

Following Korten, `SolvesKW f` gives Alice the input where `f` is false. The Karchmer–Wigderson
theorem for formulas (`Circuits.Boolean.formulaDepth_eq_ecomplexity`) uses the bit protocols of
`Protocol` and gives Alice the input where `f` is true. Such a bit protocol of depth at most `d`
solves, as a round protocol, the game of the negated function in Korten's convention
(`RoundProtocol.solvesKW_not_ofProtocol`), so of `f` after exchanging the players
(`RoundProtocol.solvesKW_swapPlayers_ofProtocol`).

## Main definitions

* `Cslib.Communication.RoundProtocol`: protocols with at most `d` messages from `M`.
* `Cslib.Communication.RoundProtocol.run`, `Cslib.Communication.RoundProtocol.Solves`.
* `Cslib.Communication.RoundProtocol.swapPlayers`, `Cslib.Communication.RoundProtocol.comap`:
  exchanging the players and relabelling the inputs.
* `Cslib.Communication.RoundProtocol.ofProtocol`: a bit protocol as a round protocol.
* `Cslib.Communication.KWRoundProtocol`, `Cslib.Communication.RoundProtocol.SolvesKW`: round
  protocols for Karchmer–Wigderson games.

## Main results

* `Cslib.Communication.RoundProtocol.run_swapPlayers`,
  `Cslib.Communication.RoundProtocol.run_comap`: exchanging the players and relabelling the inputs.
* `Cslib.Communication.RoundProtocol.run_ofProtocol`,
  `Cslib.Communication.RoundProtocol.solvesKW_not_ofProtocol`: bit protocols as round protocols.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.Communication

/-- A protocol between Alice, holding `x : X`, and Bob, holding `y : Y`, with at most `d` messages
from the alphabet `M` and outputs in `Z`. The speaker may depend on the preceding messages, and the
output depends only on the transcript. -/
inductive RoundProtocol (X Y M Z : Type*) : ℕ → Type _
  /-- Output `z`, possibly before exhausting the message budget. -/
  | output {d : ℕ} (z : Z) : RoundProtocol X Y M Z d
  /-- Alice sends one message computed from her input. -/
  | alice {d : ℕ} (send : X → M) (next : M → RoundProtocol X Y M Z d) :
      RoundProtocol X Y M Z (d + 1)
  /-- Bob sends one message computed from his input. -/
  | bob {d : ℕ} (send : Y → M) (next : M → RoundProtocol X Y M Z d) :
      RoundProtocol X Y M Z (d + 1)

namespace RoundProtocol

variable {X Y X' Y' M Z : Type*}

/-- The output of a protocol when Alice holds `x` and Bob holds `y`. -/
def run {d : ℕ} : RoundProtocol X Y M Z d → X → Y → Z
  | .output z, _, _ => z
  | .alice send next, x, y => (next (send x)).run x y
  | .bob send next, x, y => (next (send y)).run x y

@[simp] theorem run_output {d : ℕ} (z : Z) (x : X) (y : Y) :
    (output z : RoundProtocol X Y M Z d).run x y = z :=
  rfl

@[simp] theorem run_alice {d : ℕ} (send : X → M) (next : M → RoundProtocol X Y M Z d) (x : X)
    (y : Y) :
    (alice send next).run x y = (next (send x)).run x y :=
  rfl

@[simp] theorem run_bob {d : ℕ} (send : Y → M) (next : M → RoundProtocol X Y M Z d) (x : X)
    (y : Y) :
    (bob send next).run x y = (next (send y)).run x y :=
  rfl

/-- A protocol solves the relation `R` on `A × B` when its output does: its output on every pair
of inputs from `A × B` is related to them. `Communication.Solves.mono` and
`Communication.Solves.of_imp` apply to it. -/
def Solves {d : ℕ} (P : RoundProtocol X Y M Z d) (R : X → Y → Z → Prop) (A : Set X)
    (B : Set Y) : Prop :=
  Communication.Solves P.run R A B

/-- One message, from players holding inputs of the same type, sent by Bob if `b` and by Alice
otherwise. -/
def speak {d : ℕ} (b : Bool) (msg : X → M) (next : M → RoundProtocol X X M Z d) :
    RoundProtocol X X M Z (d + 1) :=
  if b then .bob msg next else .alice msg next

@[simp] theorem run_speak {d : ℕ} (b : Bool) (msg : X → M) (next : M → RoundProtocol X X M Z d)
    (x y : X) : (speak b msg next).run x y = (next (msg (if b then y else x))).run x y := by
  cases b <;> rfl

/-- Exchange the speakers throughout the protocol. -/
def swapPlayers : {d : ℕ} → RoundProtocol X Y M Z d → RoundProtocol Y X M Z d
  | _, .output z => .output z
  | _, .alice send next => .bob send fun a => (next a).swapPlayers
  | _, .bob send next => .alice send fun a => (next a).swapPlayers

/-- Exchanging the speakers exchanges the inputs. -/
@[simp] theorem run_swapPlayers : ∀ {d : ℕ} (P : RoundProtocol X Y M Z d) (y : Y) (x : X),
    P.swapPlayers.run y x = P.run x y
  | _, .output _, _, _ => rfl
  | _, .alice send next, y, x => run_swapPlayers (next (send x)) y x
  | _, .bob send next, y, x => run_swapPlayers (next (send y)) y x

@[simp] theorem swapPlayers_swapPlayers : ∀ {d : ℕ} (P : RoundProtocol X Y M Z d),
    P.swapPlayers.swapPlayers = P
  | _, .output _ => rfl
  | _, .alice _ next | _, .bob _ next => by
    simp only [swapPlayers, swapPlayers_swapPlayers]

/-- Exchanging the speakers solves the relation with the inputs exchanged. -/
theorem Solves.swapPlayers {d : ℕ} {P : RoundProtocol X Y M Z d} {R : X → Y → Z → Prop} {A : Set X}
    {B : Set Y} (h : P.Solves R A B) : P.swapPlayers.Solves (fun y x => R x y) B A :=
  fun y hy x hx => by simpa using h x hx y hy

/-- Apply `φ` to Alice's input and `ψ` to Bob's input before running the protocol. -/
def comap (φ : X' → X) (ψ : Y' → Y) :
    {d : ℕ} → RoundProtocol X Y M Z d → RoundProtocol X' Y' M Z d
  | _, .output z => .output z
  | _, .alice send next => .alice (send ∘ φ) fun a => (next a).comap φ ψ
  | _, .bob send next => .bob (send ∘ ψ) fun a => (next a).comap φ ψ

/-- Relabelling the inputs is precomposition: `P.comap φ ψ` outputs on `x` and `y` what `P` outputs
on `φ x` and `ψ y`. -/
@[simp] theorem run_comap (φ : X' → X) (ψ : Y' → Y) : ∀ {d : ℕ} (P : RoundProtocol X Y M Z d)
    (x : X') (y : Y'), (P.comap φ ψ).run x y = P.run (φ x) (ψ y)
  | _, .output _, _, _ => rfl
  | _, .alice send next, x, y => run_comap φ ψ (next (send (φ x))) x y
  | _, .bob send next, x, y => run_comap φ ψ (next (send (ψ y))) x y

/-- Relabelling the inputs solves the relation on the preimages. -/
theorem Solves.comap {d : ℕ} {P : RoundProtocol X Y M Z d} {R : X → Y → Z → Prop} {A : Set X}
    {B : Set Y} (h : P.Solves R A B) (φ : X' → X) (ψ : Y' → Y) :
    (P.comap φ ψ).Solves (fun x y => R (φ x) (ψ y)) (φ ⁻¹' A) (ψ ⁻¹' B) :=
  fun x hx y hy => by simpa using h (φ x) hx (ψ y) hy

/-- A bit protocol of depth at most `d` as a round protocol with `d` messages of one bit. -/
def ofProtocol : (p : Protocol X Y Z) → (d : ℕ) → p.depth ≤ d → RoundProtocol X Y Bool Z d
  | .output z, _, _ => .output z
  | .alice _ _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .alice send p₀ p₁, d + 1, h => .alice send fun b =>
    cond b (ofProtocol p₁ d (le_of_max_le_right (Nat.le_of_succ_le_succ h)))
      (ofProtocol p₀ d (le_of_max_le_left (Nat.le_of_succ_le_succ h)))
  | .bob _ _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .bob send p₀ p₁, d + 1, h => .bob send fun b =>
    cond b (ofProtocol p₁ d (le_of_max_le_right (Nat.le_of_succ_le_succ h)))
      (ofProtocol p₀ d (le_of_max_le_left (Nat.le_of_succ_le_succ h)))

/-- A bit protocol of depth at most `d`, run as a round protocol with `d` messages, has the same
output. -/
@[simp] theorem run_ofProtocol : ∀ (p : Protocol X Y Z) (d : ℕ) (h : p.depth ≤ d) (x : X) (y : Y),
    (ofProtocol p d h).run x y = p.run x y
  | .output _, _, _, _, _ => rfl
  | .alice _ _ _, 0, h, _, _ => absurd h (Nat.not_succ_le_zero _)
  | .alice send p₀ p₁, d + 1, h, x, y => by
    change (cond (send x) (ofProtocol p₁ d _) (ofProtocol p₀ d _)).run x y =
      cond (send x) (p₁.run x y) (p₀.run x y)
    cases send x
    · exact run_ofProtocol p₀ d _ x y
    · exact run_ofProtocol p₁ d _ x y
  | .bob _ _ _, 0, h, _, _ => absurd h (Nat.not_succ_le_zero _)
  | .bob send p₀ p₁, d + 1, h, x, y => by
    change (cond (send y) (ofProtocol p₁ d _) (ofProtocol p₀ d _)).run x y =
      cond (send y) (p₁.run x y) (p₀.run x y)
    cases send y
    · exact run_ofProtocol p₀ d _ x y
    · exact run_ofProtocol p₁ d _ x y

/-- A bit protocol and its round protocol solve the same relations. -/
@[simp] theorem solves_ofProtocol_iff {d : ℕ} {p : Protocol X Y Z} {h : p.depth ≤ d}
    {R : X → Y → Z → Prop} {A : Set X} {B : Set Y} :
    (ofProtocol p d h).Solves R A B ↔ p.Solves R A B := by
  simp only [Solves, Protocol.Solves, Communication.Solves, run_ofProtocol]

end RoundProtocol

/-- Round protocols for Karchmer–Wigderson games on the coordinates `ι`: Alice and Bob hold inputs
`ι → Bool`, send at most `d` messages from `M`, and the protocol names a coordinate. -/
abbrev KWRoundProtocol (ι M : Type*) (d : ℕ) : Type _ :=
  RoundProtocol (ι → Bool) (ι → Bool) M ι d

namespace RoundProtocol

variable {ι M : Type*} {d : ℕ}

/-- The protocol solves the Karchmer–Wigderson game of `f`: Alice holds an input with `f x = false`,
Bob one with `f y = true`, and they differ at the named coordinate. -/
def SolvesKW (P : KWRoundProtocol ι M d) (f : (ι → Bool) → Bool) : Prop :=
  ∀ x y, f x = false → f y = true → DiffersAt x y (P.run x y)

theorem solvesKW_iff_solves {P : KWRoundProtocol ι M d} {f : (ι → Bool) → Bool} :
    P.SolvesKW f ↔ P.Solves DiffersAt {x | f x = false} {y | f y = true} :=
  ⟨fun h x hx y hy => h x y hx hy, fun h x y hx hy => h x hx y hy⟩

/-- Exchanging the speakers solves the game of the negated function. -/
theorem SolvesKW.swapPlayers {P : KWRoundProtocol ι M d} {f : (ι → Bool) → Bool}
    (h : P.SolvesKW f) : P.swapPlayers.SolvesKW fun x => !f x := by
  intro x y hx hy
  rw [run_swapPlayers]
  exact (h y x (by simpa using hy) (by simpa using hx)).symm

/-- Negating both players' inputs solves the game of the function of the negated input. -/
theorem SolvesKW.comap_compl {P : KWRoundProtocol ι M d} {f : (ι → Bool) → Bool}
    (h : P.SolvesKW f) : (P.comap compl compl).SolvesKW fun x => f xᶜ := by
  intro x y hx hy
  rw [run_comap]
  intro hxy
  exact h _ _ hx hy (by simp [hxy])

/-- A bit protocol for the Karchmer–Wigderson game of `f` with Alice holding the input where `f` is
true solves, as a round protocol, the game of the negation of `f` in Korten's convention. -/
theorem solvesKW_not_ofProtocol {f : (ι → Bool) → Bool} {p : KWProtocol ι}
    (hp : p.Solves DiffersAt {x | f x = true} {y | f y = false}) (d : ℕ)
    (h : p.depth ≤ d) : (ofProtocol p d h).SolvesKW fun x => !f x := by
  intro x y hx hy
  rw [run_ofProtocol]
  exact hp x (by simpa using hx) y (by simpa using hy)

/-- A bit protocol for the Karchmer–Wigderson game of `f` with Alice holding the input where `f` is
true gives, with the players exchanged, a round protocol solving `SolvesKW f` with one bit per
message. -/
theorem solvesKW_swapPlayers_ofProtocol {f : (ι → Bool) → Bool} {p : KWProtocol ι}
    (hp : p.Solves DiffersAt {x | f x = true} {y | f y = false}) (d : ℕ)
    (h : p.depth ≤ d) : (ofProtocol p d h).swapPlayers.SolvesKW f := by
  simpa using (solvesKW_not_ofProtocol hp d h).swapPlayers

end RoundProtocol

end Cslib.Communication

/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Set.Insert

/-!
# Switch systems

Switch systems are the circuit model of Heath's arithmetic garbling [Heath2024]. A switch system
over a commutative ring `R` has `n` input wires and `N` internal wires carrying values in `R`, and
a list of gates of three kinds:

* an *affine* gate `out := ∑ c • w + b` over earlier wires;
* a *switch* `(src, out, ctrl)`: the control wire `ctrl` carries a bit, and when it is `0` the
  switch is closed and forces `out = src`; when it is `1` the switch is open and imposes nothing;
* a *join* `(left, right)`, which forces `left = right`.

Joins and closed switches act in both directions, so a switch system is a constraint system
rather than a straight-line program: an assignment `σ` of values to wires *satisfies* the system
on input `x` when it agrees with `x` on the input wires, every control wire carries `0` or `1`
and every gate's constraint holds (`SwitchSystem.Satisfies`). Values are found by propagation: a
sweep visits the gates in order and fills in each value a gate determines from known ones
(`SwitchSystem.sweep`), and `SwitchSystem.solve` repeats the sweep once per wire. Propagation is
sound: every value it finds agrees with each satisfying assignment (`SwitchSystem.solve_sound`).

A system is *well formed* when each gate reads only input wires and wires written by earlier
gates, and each internal wire is written at most once (`SwitchSystem.WellFormed`); affine gates
and switches write their output wire, joins write nothing. The garbler of
`Garbling.Switch.Garble` relies on this order.

This differs from Heath's switch systems in four ways. Heath allows wires of different bit widths
`ℤ_{2^k}` with modular reduction and division gates between them; this file has a single value
ring `R` and no width-changing gates. Heath's gates may have several outputs and his affine gates
propagate in every direction, solving any unknown wire from the others; here every gate has a
single output and propagation through an affine gate computes only its output. Finally, Heath's
legality condition (a unique satisfying assignment found by propagation) is replaced, in the
results that use it, by an arbitrary satisfying assignment `σ`.

## Main definitions

* `Cslib.Crypto.Garbling.SwitchGate`, `Cslib.Crypto.Garbling.SwitchSystem`: gates and systems.
* `Cslib.Crypto.Garbling.SwitchSystem.Satisfies`: satisfying assignments.
* `Cslib.Crypto.Garbling.SwitchSystem.WellFormed`: definition before use, single assignment.
* `Cslib.Crypto.Garbling.SwitchSystem.sweep`, `Cslib.Crypto.Garbling.SwitchSystem.solve`:
  propagation.
* `Cslib.Crypto.Garbling.SwitchSystem.controls`: the control bit of each gate under an
  assignment.

## Main results

* `Cslib.Crypto.Garbling.SwitchGate.propagate_sound`,
  `Cslib.Crypto.Garbling.SwitchSystem.sweepGates_sound`: propagation steps keep known values in
  agreement with a satisfying assignment.
* `Cslib.Crypto.Garbling.SwitchSystem.solve_sound`: propagation agrees with every satisfying
  assignment.

## References

* [D. Heath, *Efficient Arithmetic in Garbled Circuits*][Heath2024]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

variable {n N : ℕ} {R : Type}

/-- A gate of a switch system with `n` input wires and `N` internal wires. Input wires are
`Sum.inl i` and internal wires `Sum.inr j`; only internal wires are written. -/
inductive SwitchGate (n N : ℕ) (R : Type) where
  /-- `out := ∑ c • w + const` over the listed `(w, c)`. -/
  | affine (terms : List ((Fin n ⊕ Fin N) × R)) (const : R) (out : Fin N)
  /-- When `ctrl` carries `0`, `out = src`; when it carries `1`, no constraint. -/
  | switch (src : Fin n ⊕ Fin N) (out : Fin N) (ctrl : Fin n ⊕ Fin N)
  /-- `left = right`. -/
  | join (left right : Fin n ⊕ Fin N)

namespace SwitchGate

/-- The weighted sum `∑ c • a w` of a list of terms. -/
def termSum {M : Type} [AddCommMonoid M] [SMul R M] (a : Fin n ⊕ Fin N → M)
    (terms : List ((Fin n ⊕ Fin N) × R)) : M :=
  (terms.map fun p => p.2 • a p.1).sum

/-- The constraint of a gate on an assignment of values to wires. -/
def Holds [Semiring R] (σ : Fin n ⊕ Fin N → R) : SwitchGate n N R → Prop
  | affine terms b y => σ (.inr y) = termSum σ terms + b
  | switch x y c => (σ c = 0 ∨ σ c = 1) ∧ (σ c = 0 → σ (.inr y) = σ x)
  | join x y => σ x = σ y

/-- Whether a gate is an open switch under `σ`: a switch whose control value is not `0`. -/
def isOpen [Zero R] [DecidableEq R] (σ : Fin n ⊕ Fin N → R) : SwitchGate n N R → Bool
  | switch _ _ c => decide (σ c ≠ 0)
  | _ => false

/-- The wires a gate reads. -/
def reads : SwitchGate n N R → List (Fin n ⊕ Fin N)
  | affine terms _ _ => terms.map Prod.fst
  | switch x _ c => [x, c]
  | join x y => [x, y]

/-- The wires known to be defined after a gate, given those defined before it. -/
def define (D : Set (Fin n ⊕ Fin N)) : SwitchGate n N R → Set (Fin n ⊕ Fin N)
  | affine _ _ y => insert (.inr y) D
  | switch _ y _ => insert (.inr y) D
  | join _ _ => D

/-- Wires defined before a gate stay defined after it. -/
theorem mem_define_of_mem {D : Set (Fin n ⊕ Fin N)} {w : Fin n ⊕ Fin N} (g : SwitchGate n N R)
    (hw : w ∈ D) : w ∈ g.define D := by
  cases g <;> simp only [define] <;> first | exact Set.mem_insert_of_mem _ hw | exact hw

/-- A gate is well placed after the defined wires `D`: it reads only defined wires, and its
output, if any, is not yet defined. -/
def WellPlaced (D : Set (Fin n ⊕ Fin N)) : SwitchGate n N R → Prop
  | affine terms _ y => (∀ p ∈ terms, p.1 ∈ D) ∧ Sum.inr y ∉ D
  | switch x y c => x ∈ D ∧ c ∈ D ∧ Sum.inr y ∉ D
  | join x y => x ∈ D ∧ y ∈ D

/-- The weighted sum of the known values of the terms, if all are known. -/
def knownSum {M : Type} [AddCommMonoid M] [SMul R M] (st : Fin n ⊕ Fin N → Option M) :
    List ((Fin n ⊕ Fin N) × R) → Option M
  | [] => some 0
  | (w, c) :: ts => match st w, knownSum st ts with
    | some a, some s => some (c • a + s)
    | _, _ => none

/-- One propagation step through a gate: fill in a value the gate determines from known
values. A switch is used only when its control value is known to be `0`. -/
def propagate [Semiring R] [DecidableEq R] (st : Fin n ⊕ Fin N → Option R) :
    SwitchGate n N R → Fin n ⊕ Fin N → Option R
  | affine terms b y => match st (.inr y), knownSum st terms with
    | none, some s => Function.update st (.inr y) (some (s + b))
    | _, _ => st
  | switch x y c => if st c = some 0 then
      match st x, st (.inr y) with
      | some v, none => Function.update st (.inr y) (some v)
      | none, some v => Function.update st x (some v)
      | _, _ => st
    else st
  | join x y => match st x, st y with
    | some v, none => Function.update st y (some v)
    | none, some v => Function.update st x (some v)
    | _, _ => st

end SwitchGate

/-- A switch system: `n` input wires, `N` internal wires, a list of gates over `R`, and `m`
output wires. -/
structure SwitchSystem (n m N : ℕ) (R : Type) where
  /-- The gates, in order. -/
  gates : List (SwitchGate n N R)
  /-- The output wires. -/
  output : Fin m → Fin n ⊕ Fin N

namespace SwitchSystem

variable {m : ℕ}

/-- `σ` satisfies `S` on input `x`: it agrees with `x` on the input wires and satisfies every
gate. -/
def Satisfies [Semiring R] (S : SwitchSystem n m N R) (x : Fin n → R)
    (σ : Fin n ⊕ Fin N → R) : Prop :=
  (∀ i, σ (.inl i) = x i) ∧ ∀ g ∈ S.gates, g.Holds σ

/-- The control bit of each gate under `σ`: whether it is an open switch, that is, a switch whose
control value is not `0`. -/
def controls [Zero R] [DecidableEq R] (S : SwitchSystem n m N R) (σ : Fin n ⊕ Fin N → R) :
    List Bool :=
  S.gates.map (SwitchGate.isOpen σ)

/-- Gates `gs` are well placed in order, starting from the defined wires `D`. -/
def WellFormedFrom : Set (Fin n ⊕ Fin N) → List (SwitchGate n N R) → Prop
  | _, [] => True
  | D, g :: gs => g.WellPlaced D ∧ WellFormedFrom (g.define D) gs

/-- Every gate reads only input wires and wires written by earlier gates, and every internal
wire is written at most once. -/
def WellFormed (S : SwitchSystem n m N R) : Prop :=
  WellFormedFrom (Set.range Sum.inl) S.gates

/-- The propagation state holding the input and nothing else. -/
def initState (x : Fin n → R) : Fin n ⊕ Fin N → Option R :=
  Sum.elim (fun i => some (x i)) fun _ => none

/-- Propagate through the gates `gs` in order. -/
def sweepGates [Semiring R] [DecidableEq R] :
    List (SwitchGate n N R) → (Fin n ⊕ Fin N → Option R) → Fin n ⊕ Fin N → Option R
  | [], st => st
  | g :: gs, st => sweepGates gs (g.propagate st)

/-- One propagation sweep through all gates of `S`. -/
def sweep [Semiring R] [DecidableEq R] (S : SwitchSystem n m N R)
    (st : Fin n ⊕ Fin N → Option R) : Fin n ⊕ Fin N → Option R :=
  sweepGates S.gates st

/-- Propagation from the input: one sweep per wire. -/
def solve [Semiring R] [DecidableEq R] (S : SwitchSystem n m N R) (x : Fin n → R) :
    Fin n ⊕ Fin N → Option R :=
  S.sweep^[n + N] (initState x)

/-! ### Soundness of propagation -/

section Sound

/-- A state agrees with `σ` where it is known. -/
private def Agrees (σ : Fin n ⊕ Fin N → R) (st : Fin n ⊕ Fin N → Option R) : Prop :=
  ∀ w v, st w = some v → v = σ w

private theorem agrees_update {σ : Fin n ⊕ Fin N → R} {st : Fin n ⊕ Fin N → Option R}
    (h : Agrees σ st) {w : Fin n ⊕ Fin N} {v : R} (hv : v = σ w) :
    Agrees σ (Function.update st w (some v)) := by
  intro u a hu
  by_cases huw : u = w
  · subst huw
    rw [Function.update_self, Option.some.injEq] at hu
    rw [← hu, hv]
  · rw [Function.update_of_ne huw] at hu
    exact h u a hu

variable [Semiring R]

/-- A known weighted sum agrees with `σ` when the known values do. -/
theorem _root_.Cslib.Crypto.Garbling.SwitchGate.knownSum_sound {σ : Fin n ⊕ Fin N → R}
    {st : Fin n ⊕ Fin N → Option R} (h : ∀ w v, st w = some v → v = σ w) :
    ∀ (ts : List ((Fin n ⊕ Fin N) × R)) (s : R), SwitchGate.knownSum st ts = some s →
      s = SwitchGate.termSum σ ts
  | [], s, hs => by
    simp only [SwitchGate.knownSum, Option.some.injEq] at hs
    simp [← hs, SwitchGate.termSum]
  | (w, c) :: ts, s, hs => by
    simp only [SwitchGate.knownSum] at hs
    split at hs
    · rename_i a t ha ht
      simp only [Option.some.injEq] at hs
      rw [← hs, h w a ha, SwitchGate.knownSum_sound h ts t ht]
      simp [SwitchGate.termSum]
    · exact absurd hs (by simp)

variable [DecidableEq R]

private theorem agrees_propagate {σ : Fin n ⊕ Fin N → R} {st : Fin n ⊕ Fin N → Option R}
    (h : Agrees σ st) (g : SwitchGate n N R) (hg : g.Holds σ) : Agrees σ (g.propagate st) := by
  cases g with
  | affine terms b y =>
    simp only [SwitchGate.propagate]
    split
    · rename_i s _ hs
      exact agrees_update h (by rw [SwitchGate.knownSum_sound h terms s hs]; exact hg.symm)
    · exact h
  | switch x y c =>
    simp only [SwitchGate.propagate]
    split_ifs with hc
    · have hc0 : σ c = 0 := (h c 0 hc).symm
      have hxy := hg.2 hc0
      split
      · rename_i v hx _
        exact agrees_update h (by rw [h x v hx, hxy])
      · rename_i v _ hy
        exact agrees_update h (by rw [h _ v hy, hxy])
      · exact h
    · exact h
  | join x y =>
    simp only [SwitchGate.propagate]
    split
    · rename_i v hx _
      exact agrees_update h (by rw [h x v hx]; exact hg)
    · rename_i v _ hy
      exact agrees_update h (by rw [h y v hy]; exact hg.symm)
    · exact h

/-- One propagation step through a gate whose constraint `σ` satisfies keeps the known values in
agreement with `σ`. -/
theorem _root_.Cslib.Crypto.Garbling.SwitchGate.propagate_sound {σ : Fin n ⊕ Fin N → R}
    {st : Fin n ⊕ Fin N → Option R} (h : ∀ w v, st w = some v → v = σ w)
    (g : SwitchGate n N R) (hg : g.Holds σ) :
    ∀ w v, g.propagate st w = some v → v = σ w :=
  agrees_propagate h g hg

/-- Propagating through gates whose constraints `σ` satisfies keeps the known values in agreement
with `σ`. -/
theorem sweepGates_sound {σ : Fin n ⊕ Fin N → R} :
    ∀ (gs : List (SwitchGate n N R)), (∀ g ∈ gs, g.Holds σ) →
      ∀ st, (∀ w v, st w = some v → v = σ w) →
        ∀ w v, sweepGates gs st w = some v → v = σ w
  | [], _, _, h => h
  | g :: gs, hgs, _, h =>
    sweepGates_sound gs (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      _ (g.propagate_sound h (hgs g List.mem_cons_self))

/-- **Soundness of propagation**: every value found by propagation from the input agrees with
every satisfying assignment. -/
theorem solve_sound {S : SwitchSystem n m N R} {x : Fin n → R} {σ : Fin n ⊕ Fin N → R}
    (hσ : S.Satisfies x σ) (w : Fin n ⊕ Fin N) (v : R) (hw : S.solve x w = some v) :
    v = σ w := by
  have key : ∀ t, ∀ w v, S.sweep^[t] (initState x) w = some v → v = σ w := by
    intro t
    induction t with
    | zero =>
      rintro (i | j) a ha
      · simp only [Function.iterate_zero_apply, initState, Sum.elim_inl,
          Option.some.injEq] at ha
        rw [← ha, hσ.1 i]
      · simp [initState] at ha
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact sweepGates_sound S.gates hσ.2 _ ih
  exact key (n + N) w v hw

end Sound

end SwitchSystem

end Cslib.Crypto.Garbling

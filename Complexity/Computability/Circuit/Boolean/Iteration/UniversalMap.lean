/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Cslib.Computability.Circuit.Composition
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.GroupTheory.Perm.ViaEmbedding

import Complexity.Computability.Circuit.Boolean.Substitution

/-!
# Simulation, hardwiring, and a universal step map

If `τ` steps of `U` simulate one step of `F` on encoded states, then `τ * T` steps of `U` simulate
`T` steps of `F` (`iterate_simulation`). When the encoding places the input bits among constant
bits, a circuit for the power of `U` yields one for the power of `F` with at most two more gates,
the two constants of the De Morgan basis (`simulation_circuit`).

The universal step map executes a straight-line program, held in its state, one gate per step, and
after the last gate copies the output wires back into the input registers (`Universal.step`). One
round of `G + 1` steps runs any circuit with at most `G` gates (`Universal.step_round`): each gate
evaluation and the simultaneous output copy/reset each count as one semantic step. Because
`Universal.Description` and `Universal.Config` carry natural-number wire indices and a
natural-number program counter (`pc : ℕ`), `Universal.Config` is an unbounded mathematical
configuration space rather than a finite Boolean state space or the native certified universal
Turing machine; the generic value carrier `V` uses `[Inhabited V]` as the default for out-of-range
wire reads and cleared work registers. The circuit reduction `Universal.universal_power_circuit`
is conditional: it assumes a finite bit encoding `e`, the start-state hardwiring equation `he`, and
a circuit `u` computing `(Universal.step interpretation)^[(G + 1) * T]` on start states, without
constructing a global finite state encoding or a circuit for one universal step. A group
action by a hardwired element (`smul_zpow_circuit`, `smul_iterate_circuit`, `smul_inverse_circuit`),
and either factor of a product map (`prodMap_power_circuit`, `prodMap_power_circuit_left`), are
handled by the same hardwiring argument.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.hardwired`: place input bits and constants on `m` wires.
* `Cslib.Circuits.Boolean.Iteration.prodMap`: product of two maps on concatenated bit strings.
* `Cslib.Circuits.Boolean.Iteration.Universal.Description`: straight-line program description held
  in the state of the universal step map.
* `Cslib.Circuits.Boolean.Iteration.Universal.Config`: configuration of the universal step map.
* `Cslib.Circuits.Boolean.Iteration.Universal.step`: one step of the universal step map.

## Main results

* `Cslib.Circuits.Boolean.Iteration.simulation_circuit`: `C(F^[T]) ≤ C(U^[τ * T]) + 2` under a
  hardwired simulation.
* `Cslib.Circuits.Boolean.Iteration.prodMap_power_circuit`,
  `Cslib.Circuits.Boolean.Iteration.prodMap_power_circuit_left`: factor reductions for product maps.
* `Cslib.Circuits.Boolean.Iteration.smul_zpow_circuit`,
  `Cslib.Circuits.Boolean.Iteration.smul_iterate_circuit`,
  `Cslib.Circuits.Boolean.Iteration.smul_inverse_circuit`: integer powers, iterates, and inverses of
  a group action by a fixed element.
* `Cslib.Circuits.Boolean.Iteration.Universal.step_round`,
  `Cslib.Circuits.Boolean.Iteration.Universal.step_iterate`,
  `Cslib.Circuits.Boolean.Iteration.Universal.universal_power_circuit`: simulation of any circuit of
  at most `G` gates by `G + 1` steps of the universal map.

## References

* Adapted from lean/Proofs/UniversalMap.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits

/-! ### Simulation of powers -/

/-- One step of `F` is `τ` steps of `U` on encoded states, hence `T` steps are `τ * T`. -/
theorem iterate_simulation {α β : Type*} (enc : α → β) (F : α → α) (U : β → β) (τ : ℕ)
    (h : ∀ x, U^[τ] (enc x) = enc (F x)) (T : ℕ) (x : α) :
    U^[τ * T] (enc x) = enc (F^[T] x) := by
  have hs : Function.Semiconj enc F (U^[τ]) := fun x => (h x).symm
  rw [Function.iterate_mul]
  exact (hs.iterate_right T x).symm

/-! ### Hardwiring constants -/

/-- Place input bits and constants on `m` wires. -/
def hardwired {n m : ℕ} (place : Fin m → Fin n ⊕ Bool) (x : BitString n) : BitString m :=
  fun j => Sum.elim x id (place j)

/-- Hardwiring constants and duplicating or permuting inputs costs the two constants. -/
private theorem exists_hardwired_comp {n m p : ℕ} (u : Circuit signature m p)
    (place : Fin m → Fin n ⊕ Bool) :
    ∃ d : Circuit signature n p,
      (∀ x, d.eval interpretation x = u.eval interpretation (hardwired place x)) ∧
      d.size ≤ u.size + 2 := by
  refine ⟨u.comp (substituteCircuit place), fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, eval_substituteCircuit]
    rfl
  · simp only [Circuit.size_comp, size_substituteCircuit, Nat.add_comm]
    exact le_rfl

/-- Hardwire constants, run `u`, and read selected output wires. -/
private theorem exists_hardwired_projection {n m p k : ℕ} (u : Circuit signature m p)
    (place : Fin m → Fin n ⊕ Bool) (select : Fin k → Fin p) :
    ∃ d : Circuit signature n k,
      (∀ x, d.eval interpretation x =
        u.eval interpretation (hardwired place x) ∘ select) ∧
      d.size ≤ u.size + 2 := by
  obtain ⟨d, hd, hs⟩ := exists_hardwired_comp u place
  refine ⟨(Circuit.wiring signature select).comp d, fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, Circuit.eval_wiring, hd x]
  · simpa using hs

/-- The circuit consequence of a simulation: `C(F^[T]) ≤ C(U^[τ * T]) + 2` when the encoding
places the input bits among constants. The circuit for the power of `U` need only be correct on
encoded states. -/
theorem simulation_circuit {n m : ℕ} (F : BitString n → BitString n)
    (U : BitString m → BitString m)
    (place : Fin m → Fin n ⊕ Bool) (select : Fin n → Fin m)
    (hsel : ∀ i, place (select i) = Sum.inl i) (τ : ℕ)
    (hsim : ∀ x, U^[τ] (hardwired place x) = hardwired place (F x)) (T : ℕ)
    (u : Circuit signature m m)
    (hu : ∀ x, u.eval interpretation (hardwired place x) =
      U^[τ * T] (hardwired place x)) :
    ∃ d : Circuit signature n n,
      d.Computes interpretation F^[T] ∧ d.size ≤ u.size + 2 := by
  obtain ⟨d, hd, hs⟩ := exists_hardwired_projection u place select
  refine ⟨d, fun x => ?_, hs⟩
  rw [hd x, hu x, iterate_simulation (hardwired place) F U τ hsim T x]
  funext i
  simp [hardwired, hsel]

/-! ### Products -/

/-- The product of two maps on concatenated bit strings. -/
def prodMap {m k : ℕ} (U : BitString m → BitString m) (P : BitString k → BitString k)
    (z : BitString (m + k)) : BitString (m + k) :=
  Fin.append (U (fun i => z (Fin.castAdd k i))) (P (fun i => z (Fin.natAdd m i)))

/-- Each power of a product map is at least as hard as the same power of its second factor: fix the
first factor's input and read the second factor's outputs. -/
theorem prodMap_power_circuit {m k : ℕ} (U : BitString m → BitString m)
    (P : BitString k → BitString k) (T : ℕ) (u : Circuit signature (m + k) (m + k))
    (hu : u.Computes interpretation (prodMap U P)^[T]) :
    ∃ d : Circuit signature k k,
      d.Computes interpretation P^[T] ∧ d.size ≤ u.size + 2 := by
  let a : BitString m := fun _ => false
  let place : Fin (m + k) → Fin k ⊕ Bool :=
    Fin.append (fun _ : Fin m => Sum.inr false) Sum.inl
  have hpl (y : BitString k) : ∀ b : BitString m, (∀ i, b i = false) →
      hardwired place y = Fin.append b y := by
    intro b hb
    funext j
    induction j using Fin.addCases with
    | left i => simp [hardwired, place, hb]
    | right i => simp [hardwired, place]
  have hsim : ∀ (T : ℕ) (y : BitString k),
      (prodMap U P)^[T] (Fin.append a y) = Fin.append (U^[T] a) (P^[T] y) := by
    intro T
    induction T with
    | zero => intro y; rfl
    | succ T ih =>
      intro y
      rw [Function.iterate_succ_apply', ih y, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      simp [prodMap]
  obtain ⟨d, hd, hs⟩ := exists_hardwired_projection u place (Fin.natAdd m)
  refine ⟨d, fun y => ?_, hs⟩
  rw [hd y, hu, hpl y a (fun _ => rfl), hsim T y]
  funext i
  simp

/-- Each power of a product map is at least as hard as the same power of its first factor. -/
theorem prodMap_power_circuit_left {m k : ℕ} (U : BitString m → BitString m)
    (P : BitString k → BitString k) (T : ℕ) (u : Circuit signature (m + k) (m + k))
    (hu : u.Computes interpretation (prodMap U P)^[T]) :
    ∃ d : Circuit signature m m,
      d.Computes interpretation U^[T] ∧ d.size ≤ u.size + 2 := by
  let a : BitString k := fun _ => false
  let place : Fin (m + k) → Fin m ⊕ Bool :=
    Fin.append Sum.inl (fun _ : Fin k => Sum.inr false)
  have hpl (y : BitString m) : hardwired place y = Fin.append y a := by
    funext j
    induction j using Fin.addCases with
    | left i => simp [hardwired, place]
    | right i => simp [hardwired, place, a]
  have hsim : ∀ (T : ℕ) (y : BitString m),
      (prodMap U P)^[T] (Fin.append y a) = Fin.append (U^[T] y) (P^[T] a) := by
    intro T
    induction T with
    | zero => intro y; rfl
    | succ T ih =>
      intro y
      rw [Function.iterate_succ_apply', ih y, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      simp [prodMap]
  obtain ⟨d, hd, hs⟩ := exists_hardwired_projection u place (Fin.castAdd k)
  refine ⟨d, fun y => ?_, hs⟩
  rw [hd y, hu, hpl y, hsim T y]
  funext i
  simp

/-! ### Group actions by a hardwired element -/

/-- The permutation `x ↦ g • x` of a group action has inverse `x ↦ g⁻¹ • x`. -/
theorem smul_perm_symm {G α : Type*} [Group G] [MulAction G α] (g : G) :
    ⇑(MulAction.toPerm g : Equiv.Perm α).symm = fun x => g⁻¹ • x := by
  funext x
  rfl

/-- If a circuit evaluates a group action on encodings of elements and points, every integer power
of the action of a fixed element, including the inverse permutation, has a circuit with at most two
more gates. -/
theorem smul_zpow_circuit {G α : Type*} [Group G] [MulAction G α] {k n : ℕ}
    (encG : G → BitString k) (enc : α → BitString n)
    (act : Circuit signature (k + n) n)
    (hact : ∀ (g : G) (x : α), act.eval interpretation (Fin.append (encG g) (enc x)) =
      enc (g • x))
    (g : G) (T : ℤ) :
    ∃ d : Circuit signature n n,
      (∀ x, d.eval interpretation (enc x) = enc (g ^ T • x)) ∧
      d.size ≤ act.size + 2 := by
  let place : Fin (k + n) → Fin n ⊕ Bool :=
    Fin.append (fun i => Sum.inr (encG (g ^ T) i)) Sum.inl
  obtain ⟨d, hd, hs⟩ := exists_hardwired_comp act place
  refine ⟨d, fun x => ?_, hs⟩
  rw [hd, ← hact]
  congr 1
  funext j
  induction j using Fin.addCases with
  | left i => simp [hardwired, place]
  | right i => simp [hardwired, place]

/-- Every power of the action of a fixed element, as an iterate. -/
theorem smul_iterate_circuit {G α : Type*} [Group G] [MulAction G α] {k n : ℕ}
    (encG : G → BitString k) (enc : α → BitString n)
    (act : Circuit signature (k + n) n)
    (hact : ∀ (g : G) (x : α), act.eval interpretation (Fin.append (encG g) (enc x)) =
      enc (g • x))
    (g : G) (T : ℕ) :
    ∃ d : Circuit signature n n,
      (∀ x, d.eval interpretation (enc x) = enc ((fun y : α => g • y)^[T] x)) ∧
      d.size ≤ act.size + 2 := by
  obtain ⟨d, hd, hs⟩ := smul_zpow_circuit encG enc act hact g T
  exact ⟨d, fun x => by rw [hd, smul_iterate, zpow_natCast], hs⟩

/-- The inverse of the action of a fixed element. -/
theorem smul_inverse_circuit {G α : Type*} [Group G] [MulAction G α] {k n : ℕ}
    (encG : G → BitString k) (enc : α → BitString n)
    (act : Circuit signature (k + n) n)
    (hact : ∀ (g : G) (x : α), act.eval interpretation (Fin.append (encG g) (enc x)) =
      enc (g • x))
    (g : G) :
    ∃ d : Circuit signature n n,
      (∀ x, d.eval interpretation (enc x) =
        enc ((MulAction.toPerm g : Equiv.Perm α).symm x)) ∧
      d.size ≤ act.size + 2 := by
  obtain ⟨d, hd, hs⟩ := smul_zpow_circuit encG enc act hact g (-1)
  exact ⟨d, fun x => by rw [hd, smul_perm_symm, zpow_neg_one], hs⟩

/-- The iterator of `(g, x) ↦ (g, g • x)` raises the carried element to the `t`th power. -/
theorem pairAction_iterate {G α : Type*} [Monoid G] [MulAction G α] (t : ℕ) (g : G) (x : α) :
    (fun p : G × α => (p.1, p.1 • p.2))^[t] (g, x) = (g, g ^ t • x) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]

/-! ### A universal step map -/

namespace Universal

universe v w
variable {σ : Signature.{v}} {V : Type w} [Inhabited V] {n G : ℕ}

/-- A straight-line program held in the state: each of `G` entries is an operation with operand
indices, and `outputs` lists the wires copied back to the input registers. Index `i < n` names
input `i`, and index `n + j` names work register `j`. -/
structure Description (σ : Signature.{v}) (n G : ℕ) where
  /-- The `G` gate entries, each pairing an operation with its operand wire indices. -/
  entries : Fin G → Σ op : σ.Op, Fin (σ.Arity op) → ℕ
  /-- The indices of the wires copied back into the `n` input registers after a round. -/
  outputs : Fin n → ℕ

/-- A state of the universal map: the program, the input registers, the work registers, and an
unbounded natural-number program counter. Because `desc` carries natural-number wire indices and
`pc : ℕ`, this is an infinite mathematical configuration space rather than a finite Boolean state
space. -/
structure Config (σ : Signature.{v}) (V : Type w) (n G : ℕ) where
  /-- The straight-line program description held in the state. -/
  desc : Description σ n G
  /-- The `n` input registers. -/
  x : Fin n → V
  /-- The `G` work registers. -/
  w : Fin G → V
  /-- The program counter. -/
  pc : ℕ

/-- Read the register with a given index. Indices out of range read the default value of `V`. -/
def read (x : Fin n → V) (w : Fin G → V) (i : ℕ) : V :=
  if h : i < n then x ⟨i, h⟩ else if h' : i - n < G then w ⟨i - n, h'⟩ else default

/-- One semantic step: evaluate entry `pc` into work register `pc`, or, when `pc ≥ G`,
simultaneously copy the outputs into the input registers, clear the work registers to `default`,
and reset the counter. -/
def step (I : Interpretation σ V) (s : Config σ V n G) : Config σ V n G :=
  if h : s.pc < G then
    { s with
      w := Function.update s.w ⟨s.pc, h⟩
        (I (s.desc.entries ⟨s.pc, h⟩).1 fun k => read s.x s.w ((s.desc.entries ⟨s.pc, h⟩).2 k))
      pc := s.pc + 1 }
  else
    { s with
      x := fun i => read s.x s.w (s.desc.outputs i)
      w := fun _ => default
      pc := 0 }

/-- The index of a CSLib wire. -/
def wireIndex {g : ℕ} : Wire n g → ℕ
  | .input i => i
  | .gate j => n + j

/-- The description of a circuit with at most `G` gates, padded by copies of `pad`. -/
def describe (G : ℕ) (c : Circuit σ n n) (pad : σ.Op) : Description σ n G where
  entries k :=
    if h : k.val < c.size then
      ⟨(c.program.lines ⟨k, h⟩).op, fun a => wireIndex ((c.program.lines ⟨k, h⟩).wires a)⟩
    else ⟨pad, fun _ => 0⟩
  outputs i := wireIndex (c.outputs i)

/-- The start state on input `x`. -/
def start (D : Description σ n G) (x : Fin n → V) : Config σ V n G :=
  ⟨D, x, fun _ => default, 0⟩

/-- The widened lines of a program read only earlier gates. -/
private theorem lines_wire_lt {g : ℕ} (p : Program σ n g) (j : Fin g) :
    ∀ (a : Fin (σ.Arity (p.lines j).op)) (b : Fin g),
      (p.lines j).wires a = Wire.gate b → b.val < j.val := by
  induction p with
  | empty => exact Fin.elim0 j
  | @gate g p line ih =>
    induction j using Fin.lastCases with
    | last =>
      rw [Program.lines_gate_last]
      intro a b h
      have h' : (Wire.Renaming.castSucc : Wire.Renaming n g (g + 1)) (line.wires a) =
          Wire.gate b := h
      rw [Wire.Renaming.castSucc_apply] at h'
      cases hw : line.wires a with
      | input i => rw [hw] at h'; cases h'
      | gate b' =>
        rw [hw] at h'
        cases h'
        simp
    | cast j =>
      rw [Program.lines_gate_castSucc]
      intro a b h
      have h' : (Wire.Renaming.castSucc : Wire.Renaming n g (g + 1)) ((p.lines j).wires a) =
          Wire.gate b := h
      rw [Wire.Renaming.castSucc_apply] at h'
      cases hw : (p.lines j).wires a with
      | input i => rw [hw] at h'; cases h'
      | gate b' =>
        rw [hw] at h'
        cases h'
        simpa using ih j a b' hw

/-- Reading a wire by its index, from work registers that hold the gate values. -/
private theorem read_wireIndex {g : ℕ} (x : Fin n → V) (w : Fin G → V) (e : Fin g → V)
    (wire : Wire n g) (hlt : ∀ b : Fin g, wire = Wire.gate b → b.val < G)
    (hw : ∀ (b : Fin g) (h : b.val < G), wire = Wire.gate b → w ⟨b, h⟩ = e b) :
    read x w (wireIndex wire) = Wire.elim x e wire := by
  cases wire with
  | input i => simp [read, wireIndex, Wire.elim]
  | gate b =>
    have hb := hlt b rfl
    have hr : read x w (n + b.val) = w ⟨b, hb⟩ := by
      simp [read, hb]
    simpa [wireIndex, Wire.elim] using hr.trans (hw b hb rfl)

/-- After `k ≤ G` steps from the start state, the first `k` work registers hold the values of the
corresponding gates. -/
theorem run (I : Interpretation σ V) (c : Circuit σ n n) (pad : σ.Op) (hG : c.size ≤ G)
    (x : Fin n → V) :
    ∀ k ≤ G, ∃ w : Fin G → V,
      (step I)^[k] (start (describe G c pad) x) = ⟨describe G c pad, x, w, k⟩ ∧
      ∀ (j : Fin G), j.val < k → ∀ (hs : j.val < c.size),
        w j = c.program.eval I x ⟨j, hs⟩ := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun _ => default, rfl, fun _ hj => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨w, hrun, hw⟩ := ih (by omega)
    have hkG : k < G := by omega
    let v : V := I ((describe G c pad).entries ⟨k, hkG⟩).1 fun a =>
      read x w (((describe G c pad).entries ⟨k, hkG⟩).2 a)
    refine ⟨Function.update w ⟨k, hkG⟩ v, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', hrun]
      simp [step, hkG, v]
    · intro j hj hs
      by_cases hjk : j = ⟨k, hkG⟩
      · subst hjk
        rw [Function.update_self]
        have hks : k < c.size := hs
        have hent : (describe G c pad).entries ⟨k, hkG⟩ =
            ⟨(c.program.lines ⟨k, hks⟩).op,
              fun a => wireIndex ((c.program.lines ⟨k, hks⟩).wires a)⟩ := by simp [describe, hks]
        simp only [v]
        rw [hent, ← Program.lines_eval c.program I x ⟨k, hks⟩]
        unfold Line.eval
        congr 1
        funext a
        simp only [Function.comp_apply]
        apply read_wireIndex
        · intro b hb
          have hbk : b.val < k := lines_wire_lt c.program ⟨k, hks⟩ a b hb
          omega
        · intro b hbG hb
          have hbk : b.val < k := lines_wire_lt c.program ⟨k, hks⟩ a b hb
          exact hw ⟨b, hbG⟩ hbk b.isLt
      · rw [Function.update_of_ne hjk]
        have hjk' : j.val ≠ k := fun h => hjk (Fin.ext h)
        exact hw j (by omega) hs

/-- One round of `G + 1` steps of the universal map runs a circuit with at most `G` gates and
returns to a start state. -/
theorem step_round (I : Interpretation σ V) (c : Circuit σ n n) (pad : σ.Op)
    (hG : c.size ≤ G) (x : Fin n → V) :
    (step I)^[G + 1] (start (describe G c pad) x) = start (describe G c pad) (c.eval I x) := by
  obtain ⟨w, hrun, hw⟩ := run I c pad hG x G le_rfl
  rw [Function.iterate_succ_apply', hrun]
  simp only [step, lt_irrefl, dite_false, start]
  congr 1
  funext i
  simp only [describe, Circuit.eval, Function.comp_apply, Program.trace]
  apply read_wireIndex
  · intro b _
    omega
  · intro b hbG _
    exact hw ⟨b, hbG⟩ hbG b.isLt

/-- `(G + 1) * T` steps of the universal map run `T` rounds of the circuit. -/
theorem step_iterate (I : Interpretation σ V) (c : Circuit σ n n) (pad : σ.Op)
    (hG : c.size ≤ G) (T : ℕ) (x : Fin n → V) :
    (step I)^[(G + 1) * T] (start (describe G c pad) x) =
      start (describe G c pad) ((c.eval I)^[T] x) :=
  iterate_simulation (start (describe G c pad)) (c.eval I) (step I) (G + 1)
    (step_round I c pad hG) T x

/-- The conditional circuit consequence: assuming a bit encoding `e` of universal-map states that
writes the input registers of a start state directly and fixes its other bits to constants
determined by the description (`he`), together with a circuit `u` for the `(G + 1) * T`-th power of
`Universal.step` on those start states (`hu`), one obtains a circuit for the `T`th power of `c`
with at most two more gates. Neither `e` nor a circuit for one universal step is constructed
here. -/
theorem universal_power_circuit {m : ℕ} (c : Circuit signature n n)
    (pad : signature.Op) (hG : c.size ≤ G)
    (e : Config signature Bool n G → BitString m) (place : Fin m → Fin n ⊕ Bool)
    (select : Fin n → Fin m) (hsel : ∀ i, place (select i) = Sum.inl i)
    (he : ∀ x, e (start (describe G c pad) x) = hardwired place x)
    (T : ℕ) (u : Circuit signature m m)
    (hu : ∀ x, u.eval interpretation (e (start (describe G c pad) x)) =
      e ((step interpretation)^[(G + 1) * T] (start (describe G c pad) x))) :
    ∃ d : Circuit signature n n,
      d.Computes interpretation (c.eval interpretation)^[T] ∧
      d.size ≤ u.size + 2 := by
  obtain ⟨d, hd, hs⟩ := exists_hardwired_projection u place select
  refine ⟨d, fun x => ?_, hs⟩
  rw [hd x, ← he, hu, step_iterate _ c pad hG, he]
  funext i
  simp [hardwired, hsel]

end Universal

end Cslib.Circuits.Boolean.Iteration

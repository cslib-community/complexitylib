/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate
public import Complexity.Computability.Circuit.Support
public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Circuit.Depth
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Size lower bounds from bounded fan-in

Unfolding a frontier through a bounded-fan-in program controls how many
original inputs can reach the outputs. Essential inputs therefore give a
lower bound on circuit size.

## Main results

* `Cslib.Circuits.Program.card_biUnion_wireSupport_le_cost`: supporting inputs are bounded by the
  frontier size plus the program cost under any weight bounding arities by `1 + w op`.
* `Cslib.Circuits.Circuit.card_inputSupport_le_size`: a circuit of fan-in `r` with `m` outputs has
  at most `m + (r - 1) size` supporting inputs.
* `Cslib.Circuits.Circuit.essential_le_size`: the same bound for essential inputs of the computed
  function.
* `Cslib.Circuits.Circuit.card_inputSupport_le_depth`, `Cslib.Circuits.Circuit.essential_le_depth`:
  at depth `d`, an output of a circuit of fan-in `r` depends on at most `r ^ d` inputs.
* `Cslib.Circuits.Program.FanInAtMost.mono`, `Cslib.Circuits.Circuit.FanInAtMost.mono`: fan-in
  bounds are monotone in the bound.
* `Cslib.Circuits.Program.FanInAtMost.append`, `Cslib.Circuits.Circuit.FanInAtMost.comp`,
  `Cslib.Circuits.Circuit.FanInAtMost.append`: fan-in bounds of composed programs and circuits.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U V : Type*} {n m g : ℕ}

/-- The original circuit inputs reachable backwards from a frontier of wires in a program. -/
private def Program.reachableInputs :
    ∀ {g : ℕ}, Program σ n g → Finset (Wire n g) → Finset (Fin n)
  | _, .empty, frontier => Finset.univ.filter fun input => Wire.input input ∈ frontier
  | _, @Program.gate _ _ g program line, frontier =>
      let prior := Finset.univ.filter fun wire : Wire n g => wire.castSucc ∈ frontier
      let opened :=
        if Wire.gate (Fin.last g) ∈ frontier then
          prior ∪ Finset.univ.image line.wires
        else
          prior
      program.reachableInputs opened

/-- Embedding a wire into a widened program by `Wire.castSucc` is injective. -/
theorem Wire.castSucc_injective :
    Function.Injective (Wire.castSucc : Wire n g → Wire n (g + 1)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Wire.castSucc]

private def Circuit.frontier (c : Circuit σ n m) :
    Finset (Wire n c.size) :=
  Finset.univ.image c.outputs

@[simp] private theorem Circuit.mem_frontier
    {c : Circuit σ n m}
    {wire : Wire n c.size} :
    wire ∈ c.frontier ↔
      ∃ output, c.outputs output = wire := by
  simp [Cslib.Circuits.Circuit.frontier]

private def Circuit.reachableInputs (c : Circuit σ n m) :
    Finset (Fin n) :=
  c.program.reachableInputs c.frontier

/-- Every input supporting a wire in the frontier is reachable from the frontier. -/
private theorem Program.support_subset_reachableInputs
    (program : Program σ n g) :
    ∀ frontier : Finset (Wire n g),
      frontier.biUnion program.wireSupport ⊆
        program.reachableInputs frontier := by
  induction program with
  | empty =>
      intro frontier i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨wire, wireSelected, hi⟩ := hi
      cases wire with
      | input input =>
          simp only [Program.wireSupport_input, Finset.mem_singleton] at hi
          subst i
          simpa [Cslib.Circuits.Program.reachableInputs] using wireSelected
      | gate impossible => exact Fin.elim0 impossible
  | @gate g program line ih =>
      intro frontier i hi
      let prior := Finset.univ.filter fun wire : Wire n g => wire.castSucc ∈ frontier
      let opened :=
        if Wire.gate (Fin.last g) ∈ frontier then
          prior ∪ Finset.univ.image line.wires
        else
          prior
      change i ∈ program.reachableInputs opened
      apply ih opened
      rw [Finset.mem_biUnion] at hi
      obtain ⟨wire, wireSelected, hi⟩ := hi
      revert wireSelected hi
      induction wire using Wire.lastCases with
      | last =>
        intro lastSelected hi
        rw [Program.wireSupport_gate_last] at hi
        obtain ⟨argument, hi⟩ := Line.mem_inputSupport.mp hi
        exact Finset.mem_biUnion.mpr
          ⟨line.wires argument, by simp [opened, lastSelected], hi⟩
      | castSucc wire =>
        intro wireSelected hi
        rw [Program.wireSupport_gate_castSucc] at hi
        refine Finset.mem_biUnion.mpr ⟨wire, ?_, hi⟩
        by_cases lastSelected : Wire.gate (Fin.last g) ∈ frontier <;>
          simp [opened, lastSelected, prior, wireSelected]

private theorem Circuit.inputSupport_subset_reachableInputs
    (c : Circuit σ n m) :
    c.inputSupport ⊆ c.reachableInputs := by
  intro input present
  apply c.program.support_subset_reachableInputs c.frontier
  simp only [Circuit.mem_inputSupport, Finset.mem_biUnion,
    Cslib.Circuits.Circuit.mem_frontier] at present ⊢
  obtain ⟨output, supported⟩ := present
  exact ⟨c.outputs output, ⟨output, rfl⟩, supported⟩

/-- Opening the last gate `g` along `line` increases the frontier size by at most `w line.op`
whenever `σ.Arity line.op ≤ 1 + w line.op`. -/
private theorem Line.card_opened_le (line : Line σ n g) (w : σ.Op → ℕ)
    (hw : σ.Arity line.op ≤ 1 + w line.op) (frontier : Finset (Wire n (g + 1))) :
    (let prior := Finset.univ.filter fun wire : Wire n g => wire.castSucc ∈ frontier
     if Wire.gate (Fin.last g) ∈ frontier then
       prior ∪ Finset.univ.image line.wires
     else prior).card ≤ frontier.card + w line.op := by
  dsimp only
  let prior := Finset.univ.filter fun wire : Wire n g => wire.castSucc ∈ frontier
  let lineInputs := Finset.univ.image line.wires
  have priorBound : prior.card ≤ frontier.card :=
    Finset.card_le_card_of_injOn Wire.castSucc (fun wire present => by simpa [prior] using present)
      Wire.castSucc_injective.injOn
  have lineBound : lineInputs.card ≤ 1 + w line.op :=
    (Finset.card_image_le.trans_eq (by simp)).trans hw
  split_ifs with lastSelected
  · have priorEraseBound : prior.card ≤ (frontier.erase (Wire.gate (Fin.last g))).card := by
      refine Finset.card_le_card_of_injOn Wire.castSucc (fun wire present => ?_)
        Wire.castSucc_injective.injOn
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, by simpa [prior] using present⟩
      cases wire with
      | input i => simp
      | gate j => simp [Fin.castSucc_ne_last]
    have erased := Finset.card_erase_of_mem lastSelected
    have frontierPositive : 1 ≤ frontier.card := Finset.one_le_card.mpr ⟨_, lastSelected⟩
    calc
      (prior ∪ lineInputs).card ≤ prior.card + lineInputs.card := Finset.card_union_le _ _
      _ ≤ (frontier.erase (Wire.gate (Fin.last g))).card + (1 + w line.op) :=
        Nat.add_le_add priorEraseBound lineBound
      _ = frontier.card + w line.op := by omega
  · exact priorBound.trans (Nat.le_add_right _ _)

/-- In any circuit program, the number of reachable inputs from a frontier of wires is bounded
by the size of the frontier plus the cost of the program, for any weight function that bounds gate
arities by `1 + w op`. -/
private theorem Program.card_reachableInputs_le_cost
    (program : Program σ n g)
    (w : σ.Op → ℕ)
    (hw : ∀ op, σ.Arity op ≤ 1 + w op)
    (frontier : Finset (Wire n g)) :
    (program.reachableInputs frontier).card ≤
      frontier.card + program.cost w := by
  induction program with
  | empty =>
      simp only [Program.reachableInputs, Program.cost_empty, Nat.add_zero]
      apply Finset.card_le_card_of_injOn Wire.input
      · intro input present
        simpa using present
      · intro a _ b _ h
        cases h
        rfl
  | @gate g program line ih =>
      let prior := Finset.univ.filter fun wire : Wire n g => wire.castSucc ∈ frontier
      let lineInputs := Finset.univ.image line.wires
      let opened :=
        if Wire.gate (Fin.last g) ∈ frontier then prior ∪ lineInputs else prior
      have openedBound : opened.card ≤ frontier.card + w line.op :=
        line.card_opened_le w (hw line.op) frontier
      change (program.reachableInputs opened).card ≤ _
      calc
        (program.reachableInputs opened).card ≤ opened.card + program.cost w :=
          ih opened
        _ ≤ frontier.card + w line.op + program.cost w :=
          Nat.add_le_add_right openedBound _
        _ = frontier.card + (program.gate line).cost w := by
          rw [Program.cost_gate]
          omega

/-- The inputs supporting a frontier of wires in a program are bounded by the size of the frontier
plus the cost of the program, for any weight function that bounds gate arities by `1 + w op`. -/
theorem Program.card_biUnion_wireSupport_le_cost
    (program : Program σ n g)
    (w : σ.Op → ℕ)
    (hw : ∀ op, σ.Arity op ≤ 1 + w op)
    (frontier : Finset (Wire n g)) :
    (frontier.biUnion program.wireSupport).card ≤
      frontier.card + program.cost w :=
  (Finset.card_le_card (program.support_subset_reachableInputs frontier)).trans
    (program.card_reachableInputs_le_cost w hw frontier)

private theorem Program.cost_le_of_fanInAtMost (p : Program σ n g) {r : ℕ} (h : p.FanInAtMost r) :
    p.cost (fun op => max (r - 1) (σ.Arity op - 1)) ≤ (r - 1) * g := by
  induction p with
  | empty => simp
  | gate p line ih =>
    obtain ⟨hp, hline⟩ := h
    rw [Program.cost_gate, Nat.mul_succ]
    have hw : max (r - 1) (σ.Arity line.op - 1) = r - 1 := by omega
    rw [hw]
    exact Nat.add_le_add (ih hp) le_rfl

private theorem Program.card_reachableInputs_le
    (program : Program σ n g)
    (r : Nat) :
    ∀ (_bounded : program.FanInAtMost r) (frontier : Finset (Wire n g)),
      (program.reachableInputs frontier).card ≤
        frontier.card + (r - 1) * g := by
  intro bounded frontier
  have hw : ∀ op, σ.Arity op ≤ 1 + max (r - 1) (σ.Arity op - 1) := fun op => by omega
  exact (program.card_reachableInputs_le_cost _ hw frontier).trans
    (Nat.add_le_add_left (program.cost_le_of_fanInAtMost bounded) _)

private theorem Circuit.card_reachableInputs_le_size
    (c : Circuit σ n m)
    (r : Nat)
    (bounded : c.FanInAtMost r) :
    c.reachableInputs.card ≤ m + (r - 1) * c.size := by
  have frontierBound : c.frontier.card ≤ m := by
    simpa [Cslib.Circuits.Circuit.frontier] using
      (Finset.card_image_le :
        (Finset.univ.image c.outputs).card ≤
          (Finset.univ : Finset (Fin m)).card)
  have programBound := c.program.card_reachableInputs_le r bounded c.frontier
  calc
    c.reachableInputs.card ≤ c.frontier.card + (r - 1) * c.size := programBound
    _ ≤ m + (r - 1) * c.size := Nat.add_le_add_right frontierBound _

/-- A fan-in-`r` circuit has at most `m + (r - 1) * c.size`
supporting inputs. -/
theorem Circuit.card_inputSupport_le_size
    (c : Circuit σ n m)
    {r : Nat}
    (bounded : c.FanInAtMost r) :
    c.inputSupport.card ≤ m + (r - 1) * c.size := by
  exact (Finset.card_le_card c.inputSupport_subset_reachableInputs).trans
    (c.card_reachableInputs_le_size r bounded)


/-- If a circuit has fan-in at most `r`, computes `target`, and every input in
`selected` is essential to `target`, then `selected` has at most
`m + (r - 1) * c.size` elements. -/
theorem Circuit.essential_le_size
    (c : Circuit σ n m)
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    {selected : Finset (Fin n)}
    {r : Nat}
    (computes : c.Computes interpretation target)
    (essential : ∀ k ∈ selected, EssentialAt target k)
    (bounded : c.FanInAtMost r) :
    selected.card ≤ m + (r - 1) * c.size := by
  have targetDepends := computes.dependsOn
  exact (Finset.card_le_card fun k hk =>
    (essential k hk).mem_support targetDepends).trans
      (c.card_inputSupport_le_size bounded)


/-! ### Depth -/

/-- In a program of fan-in `r`, a wire of depth `d` is supported by at most `max 1 r ^ d`
inputs. -/
theorem Program.card_wireSupport_le_pow {r : ℕ} :
    ∀ {g : ℕ} {p : Program σ n g}, p.FanInAtMost r →
      ∀ w : Wire n g, (p.wireSupport w).card ≤ max 1 r ^ p.wireDepths w
  | _, .empty, _, .input i => by simp
  | _, .empty, _, .gate j => j.elim0
  | _, @Program.gate _ _ g p line, ⟨hp, hline⟩, w => by
    induction w using Wire.lastCases with
    | last =>
      rw [Program.wireSupport_gate_last]
      change _ ≤ max 1 r ^ (p.gate line).depths (Fin.last g)
      rw [Program.depths_gate_last]
      obtain ⟨d, hd⟩ : ∃ d, line.depth p.wireDepths = d + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (line.depth_pos _)).symm⟩
      have hargs := (line.depth_le_add_one_iff p.wireDepths).1 hd.le
      calc (line.inputSupport p.wireSupport).card
          ≤ (Finset.univ : Finset (Fin (σ.Arity line.op))).card * max 1 r ^ d :=
            Finset.card_biUnion_le_card_mul _ _ _ fun i _ =>
              (card_wireSupport_le_pow hp _).trans
                (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le Nat.one_pos (le_max_left 1 r)) (hargs i))
        _ ≤ max 1 r * max 1 r ^ d := by
            rw [Finset.card_univ, Fintype.card_fin]
            exact Nat.mul_le_mul_right _ (hline.trans (le_max_right _ _))
        _ = max 1 r ^ line.depth p.wireDepths := by rw [hd, pow_succ, Nat.mul_comm]
    | castSucc w =>
      rw [Program.wireSupport_gate_castSucc, Program.wireDepths_gate_castSucc]
      exact card_wireSupport_le_pow hp w

/-- A circuit of fan-in `r` with `m` outputs and depth `d` has at most `m (max 1 r) ^ d`
supporting inputs. -/
theorem Circuit.card_inputSupport_le_depth (c : Circuit σ n m) {r : ℕ} (hc : c.FanInAtMost r) :
    c.inputSupport.card ≤ m * max 1 r ^ c.depth := by
  simpa [Circuit.inputSupport] using Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin m))
    c.outputSupport (max 1 r ^ c.depth) fun o _ =>
      (c.program.card_wireSupport_le_pow hc (c.outputs o)).trans
        (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le Nat.one_pos (le_max_left 1 r))
          (c.outputDepths_le_depth o))

/-- If a circuit of fan-in `r` and depth `d` computes `target`, and every input in `selected` is
essential to `target`, then `selected` has at most `m (max 1 r) ^ d` elements. -/
theorem Circuit.essential_le_depth (c : Circuit σ n m) {I : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U} {selected : Finset (Fin n)} {r : ℕ}
    (hc : c.Computes I target) (h : ∀ k ∈ selected, EssentialAt target k)
    (hr : c.FanInAtMost r) : selected.card ≤ m * max 1 r ^ c.depth :=
  (Finset.card_le_card fun k hk => (h k hk).mem_support hc.dependsOn).trans
    (c.card_inputSupport_le_depth hr)

/-! ### Composition -/

/-- A fan-in bound holds for every larger bound. -/
theorem Program.FanInAtMost.mono {p : Program σ n g} {r s : ℕ} (h : p.FanInAtMost r)
    (hrs : r ≤ s) : p.FanInAtMost s :=
  Program.fanInAtMost_iff.2 fun k => (Program.fanInAtMost_iff.1 h k).trans hrs

/-- Continuing a program by another keeps a common fan-in bound. -/
theorem Program.FanInAtMost.append {k g₁ g₂ r : ℕ} {p : Program σ n g₁}
    {feed : Fin k → Wire n g₁} {q : Program σ k g₂} (hp : p.FanInAtMost r)
    (hq : q.FanInAtMost r) : (p.append feed q).FanInAtMost r := by
  induction q with
  | empty => exact hp
  | gate q line ih => exact ⟨ih hq.1, hq.2⟩

/-- A fan-in bound of a circuit holds for every larger bound. -/
theorem Circuit.FanInAtMost.mono {c : Circuit σ n m} {r s : ℕ} (h : c.FanInAtMost r)
    (hrs : r ≤ s) : c.FanInAtMost s :=
  Program.FanInAtMost.mono h hrs

/-- Sequential composition keeps a common fan-in bound. -/
theorem Circuit.FanInAtMost.comp {p : ℕ} {d : Circuit σ m p} {c : Circuit σ n m} {r : ℕ}
    (hd : d.FanInAtMost r) (hc : c.FanInAtMost r) : (d.comp c).FanInAtMost r :=
  Program.FanInAtMost.append hc hd

/-- Parallel composition keeps a common fan-in bound. -/
theorem Circuit.FanInAtMost.append {p : ℕ} {c : Circuit σ n m} {d : Circuit σ n p} {r : ℕ}
    (hc : c.FanInAtMost r) (hd : d.FanInAtMost r) : (c.append d).FanInAtMost r :=
  Program.FanInAtMost.append hc hd

end Cslib.Circuits

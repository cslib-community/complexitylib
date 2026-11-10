/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.FanIn
public import Mathlib.Data.Fintype.Sigma
import CslibFrontier.Computability.Circuit.Program
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators

/-!
# Critical paths, dead-gate elimination, and the `2n - 2m` structure theorem

Signature-generic wire out-degrees, syntactic dead-gate elimination, isolated variables, critical
paths, and two-variable intersection bottlenecks for bounded-fan-in circuits, following Section 7.1
of Fan, Li, and Yang [FanLiYang2022].

For each input wire `x` of a circuit `C`, the *critical path* `C.criticalPath x` walks forward
along unique outgoing gate slots until reaching a wire `C.criticalEndpoint x` whose out-degree in
`C` is not `1` (Definition 7.1). A circuit has *no dead gates* (`C.NoDeadGates`, called
*normalized* in [FanLiYang2022]) when every internal gate of out-degree `0` is a designated output
wire; syntactic dead-gate elimination (`C.exists_noDeadGates`) removes unused internal gates without
increasing gate count or fan-in. An *isolated variable* (`C.HasIsolatedVar`) is an input wire of
out-degree `0` that is not a designated output wire.

When a fan-in-`2` circuit has no dead gates, no isolated variables, and pairwise disjoint critical
paths, counting outgoing gate slots against critical endpoints gives `2 * n - 2 * m ≤ C.size`
(Lemma 7.4). Conversely, if two distinct inputs `x ≠ y` of a single-output fan-in-`2` circuit with
no dead gates have intersecting critical paths, every `2`-variable restriction to `(x, y)` factors
through a single binary gate operation `opG` via unary pre- and post-processing
(`C.exists_bottleneck_of_not_disjoint_criticalPath`).

## Main definitions

* `Cslib.Circuits.Circuit.outDeg`: out-degree of a wire in a circuit.
* `Cslib.Circuits.Circuit.NoDeadGates`: circuits with no unused non-output internal gates
  (*normalized* in [FanLiYang2022], Definition 7.1).
* `Cslib.Circuits.Circuit.HasIsolatedVar`: circuits with an unused non-output input wire.
* `Cslib.Circuits.Circuit.criticalPath`, `Cslib.Circuits.Circuit.criticalEndpoint`: the critical
  path and its terminal wire starting from each input coordinate.

## Main results

* `Cslib.Circuits.Circuit.exists_noDeadGates`: syntactic dead-gate elimination preserving
  evaluation, size upper bounds, and fan-in bounds.
* `Cslib.Circuits.Circuit.eval_update_of_outDeg_input_eq_zero`: updating an isolated input wire does
  not change circuit evaluation.
* `Cslib.Circuits.Circuit.two_mul_sub_two_mul_le_size`: Lemma 7.4 of [FanLiYang2022].
* `Cslib.Circuits.Circuit.exists_bottleneck_of_not_disjoint_criticalPath`: two-variable restriction
  bottleneck at the first intersection of two critical paths.

## References

* [Z. Fan, J. Li, and T. Yang, *The Exact Complexity of Pseudorandom Functions and the Black-Box
  Natural Proof Barrier for Bootstrapping Results in Computational Complexity*][FanLiYang2022],
  Section 7.1.
-/

public section

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {n m g : ℕ}

/-! ### Wire ranks and gate input slots -/

/-- Topological rank of a wire: `0` for original inputs and `k + 1` for internal gate `k`. -/
@[expose] def Wire.rank : Wire n g → ℕ
  | .input _ => 0
  | .gate k => k.val + 1

@[simp] theorem Wire.rank_input (i : Fin n) : (Wire.input i : Wire n g).rank = 0 := rfl

@[simp] theorem Wire.rank_gate (k : Fin g) : (Wire.gate k : Wire n g).rank = k.val + 1 := rfl

/-- Every wire in a `g`-gate namespace has topological rank at most `g`. -/
theorem Wire.rank_le (w : Wire n g) : w.rank ≤ g := by
  cases w with
  | input _ => exact Nat.zero_le g
  | gate k => exact k.isLt

/-- An input slot `(k, a)` of gate `k` in a circuit `C`. -/
abbrev Circuit.Slot (C : Circuit σ n m) : Type :=
  Σ k : Fin C.size, Fin (σ.Arity (C.program.lines k).op)

/-- The wire read by gate input slot `s` of `C`. -/
@[expose] def Circuit.slotWire (C : Circuit σ n m) (s : C.Slot) : Wire n C.size :=
  (C.program.lines s.1).wires s.2

/-- All gate input slots of `C`, listed in gate and argument order. -/
@[expose] def Circuit.allSlots (C : Circuit σ n m) : List C.Slot :=
  (List.finRange C.size).flatMap fun k =>
    (List.finRange (σ.Arity (C.program.lines k).op)).map fun a => ⟨k, a⟩

/-- Every gate input slot occurs in `C.allSlots`. -/
@[simp] theorem Circuit.mem_allSlots (C : Circuit σ n m) (s : C.Slot) : s ∈ C.allSlots := by
  rcases s with ⟨k, a⟩
  simp [Circuit.allSlots, List.mem_finRange]

/-- Each gate input slot occurs at most once in `C.allSlots`. -/
theorem Circuit.nodup_allSlots (C : Circuit σ n m) : C.allSlots.Nodup := by
  unfold Circuit.allSlots
  rw [List.nodup_flatMap]
  refine ⟨fun k _ => (List.nodup_finRange _).map fun a₁ a₂ h => ?_, ?_⟩
  · exact Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
  · refine (List.nodup_finRange C.size).pairwise_of_forall_ne fun k₁ _ k₂ _ hne => ?_
    dsimp only [Function.onFun]
    rw [List.disjoint_left]
    intro s hs₁ hs₂
    simp only [List.mem_map] at hs₁ hs₂
    obtain ⟨_, _, rfl⟩ := hs₁
    obtain ⟨_, _, heq⟩ := hs₂
    exact hne (congrArg Sigma.fst heq).symm

/-- The gate input slots of `C` that read wire `v`. -/
@[expose] def Circuit.slotReaders (C : Circuit σ n m) (v : Wire n C.size) : List C.Slot :=
  C.allSlots.filter fun s => C.slotWire s == v

/-- Membership in `C.slotReaders v` characterizes slots reading `v`. -/
@[simp] theorem Circuit.mem_slotReaders (C : Circuit σ n m) {s : C.Slot} {v : Wire n C.size} :
    s ∈ C.slotReaders v ↔ C.slotWire s = v := by
  simp [Circuit.slotReaders]

/-- `C.slotReaders v` contains no duplicate slots. -/
theorem Circuit.nodup_slotReaders (C : Circuit σ n m) (v : Wire n C.size) :
    (C.slotReaders v).Nodup :=
  C.nodup_allSlots.filter _

/-- Every slot reading `v` belongs to a gate of strictly larger topological rank than `v`. -/
theorem Circuit.rank_lt_of_slotWire_eq (C : Circuit σ n m) {s : C.Slot} {v : Wire n C.size}
    (hs : C.slotWire s = v) : v.rank < (Wire.gate s.1 : Wire n C.size).rank := by
  cases v with
  | input _ => simp
  | gate j =>
    have hlt := C.program.lt_of_lines_wires_eq_gate s.1 s.2 j hs
    simp only [Wire.rank_gate]
    omega

/-- The out-degree of wire `v` in `C`: the number of gate input slots that read `v`. -/
@[expose] def Circuit.outDeg (C : Circuit σ n m) (v : Wire n C.size) : ℕ :=
  (C.slotReaders v).length

/-- Out-degree equals the cardinality of the fiber of `C.slotWire` over `v`. -/
theorem Circuit.outDeg_eq_card_filter (C : Circuit σ n m) (v : Wire n C.size) :
    C.outDeg v = (Finset.univ.filter fun s : C.Slot => C.slotWire s = v).card := by
  rw [Circuit.outDeg, ← List.toFinset_card_of_nodup (C.nodup_slotReaders v)]
  congr 1
  ext s
  simp

/-- Wire `v` has out-degree `0` precisely when no gate slot reads `v`. -/
theorem Circuit.outDeg_eq_zero_iff (C : Circuit σ n m) {v : Wire n C.size} :
    C.outDeg v = 0 ↔ ∀ s : C.Slot, C.slotWire s ≠ v := by
  simp [Circuit.outDeg, List.eq_nil_iff_forall_not_mem]

/-- Wire `v` has out-degree `1` precisely when `C.slotReaders v` is a singleton list. -/
theorem Circuit.outDeg_eq_one_iff (C : Circuit σ n m) {v : Wire n C.size} :
    C.outDeg v = 1 ↔ ∃ s : C.Slot, C.slotReaders v = [s] :=
  List.length_eq_one_iff

/-- Summing `C.outDeg` over all wires counts every gate input slot of `C`. -/
theorem Circuit.sum_outDeg (C : Circuit σ n m) :
    (∑ v : Wire n C.size, C.outDeg v) = ∑ k : Fin C.size, σ.Arity (C.program.lines k).op := by
  simp_rw [C.outDeg_eq_card_filter]
  have hcard : (∑ v : Wire n C.size,
      (Finset.univ.filter fun s : C.Slot => C.slotWire s = v).card) =
      (Finset.univ : Finset C.Slot).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (f := C.slotWire) (s := Finset.univ) (t := Finset.univ)
      (fun s _ => Finset.mem_univ (C.slotWire s))).symm
  rw [hcard, Finset.card_univ, Fintype.card_sigma]
  simp

/-- Under fan-in bound `r`, the sum of wire out-degrees is at most `r * C.size`. -/
theorem Circuit.sum_outDeg_le_of_fanInAtMost (C : Circuit σ n m) {r : ℕ} (h : C.FanInAtMost r) :
    (∑ v : Wire n C.size, C.outDeg v) ≤ r * C.size := by
  rw [C.sum_outDeg]
  have hle : ∀ k : Fin C.size, σ.Arity (C.program.lines k).op ≤ r :=
    Program.fanInAtMost_iff.mp h
  calc
    (∑ k : Fin C.size, σ.Arity (C.program.lines k).op)
      ≤ ∑ _k : Fin C.size, r := Finset.sum_le_sum fun k _ => hle k
    _ = r * C.size := by
      simp [Nat.mul_comm]

/-! ### Output wires, dead-gate freedom, and isolated variables -/

/-- The finite set of designated output wires of `C`. -/
@[expose] def Circuit.outputsFinset (C : Circuit σ n m) : Finset (Wire n C.size) :=
  Finset.univ.image C.outputs

theorem Circuit.mem_outputsFinset (C : Circuit σ n m) {v : Wire n C.size} :
    v ∈ C.outputsFinset ↔ ∃ j : Fin m, C.outputs j = v := by
  simp [Circuit.outputsFinset]

theorem Circuit.card_outputsFinset_le (C : Circuit σ n m) : C.outputsFinset.card ≤ m := by
  simpa [Circuit.outputsFinset] using Finset.card_image_le (f := C.outputs) (s := Finset.univ)

/-- A circuit has *no dead gates* if every internal gate of out-degree `0` is a designated output
wire (called *normalized* in Fan–Li–Yang [FanLiYang2022], Definition 7.1; named `NoDeadGates` here
to distinguish syntactic dead-gate freedom from semantic duplicate-gate merging in
`Cslib.Circuits.Circuit.Irredundant`). -/
@[expose] def Circuit.NoDeadGates (C : Circuit σ n m) : Prop :=
  ∀ k : Fin C.size, C.outDeg (.gate k) = 0 → .gate k ∈ C.outputsFinset

instance Circuit.instDecidableNoDeadGates (C : Circuit σ n m) : Decidable C.NoDeadGates :=
  inferInstanceAs (Decidable (∀ _ : Fin C.size, _ → _))

/-- A circuit *has an isolated variable* if some input wire has out-degree `0` and is not a
designated output wire (Fan–Li–Yang [FanLiYang2022], Definition 7.1). -/
@[expose] def Circuit.HasIsolatedVar (C : Circuit σ n m) : Prop :=
  ∃ i : Fin n, C.outDeg (.input i) = 0 ∧ .input i ∉ C.outputsFinset

instance Circuit.instDecidableHasIsolatedVar (C : Circuit σ n m) :
    Decidable C.HasIsolatedVar :=
  inferInstanceAs (Decidable (∃ _ : Fin n, _ ∧ _))

private def dropLastWire {n g : ℕ} : (w : Wire n (g + 1)) → w ≠ .gate (Fin.last g) → Wire n g
  | .input i, _ => .input i
  | .gate j, hw => .gate (j.castPred fun hj => hw (congrArg Wire.gate hj))

private def stepDeletedWire {n g' : ℕ} {k' : Fin (g' + 1)}
    (ρ' : ∀ w : Wire n (g' + 1), w ≠ .gate k' → Wire n g') :
    (w : Wire n (g' + 1 + 1)) → w ≠ .gate k'.castSucc → Wire n (g' + 1)
  | .input i, _ => (ρ' (.input i) (by simp)).castSucc
  | .gate j, hw =>
      if hj : j = Fin.last (g' + 1) then
        .gate (Fin.last g')
      else
        (ρ' (.gate (j.castPred hj)) fun heq =>
          hw (by cases heq; simp [Fin.castSucc_castPred])).castSucc

/-- Deleting an internal gate `k₀` that is read by no gate of `p` yields a `g`-gate program and a
partial wire map preserving traces and fan-in bounds. -/
private theorem Program.exists_deleteUnusedGate :
    ∀ {g : ℕ} (p : Program σ n (g + 1)) (k₀ : Fin (g + 1)),
      (∀ (k : Fin (g + 1)) (a : Fin (σ.Arity (p.lines k).op)),
        (p.lines k).wires a ≠ .gate k₀) →
      ∃ (q : Program σ n g) (ρ : ∀ w : Wire n (g + 1), w ≠ .gate k₀ → Wire n g),
        (∀ {U : Type u} (I : Interpretation σ U) (x : Fin n → U) (w : Wire n (g + 1))
          (hw : w ≠ .gate k₀), q.trace I x (ρ w hw) = p.trace I x w) ∧
        (∀ r, p.FanInAtMost r → q.FanInAtMost r)
  | g, .gate q line, k₀ => by
    refine Fin.lastCases (fun _ => ?_) (fun k' hunused => ?_) k₀
    · refine ⟨q, dropLastWire, ?_, fun _ hp => hp.1⟩
      intro U I x w hw
      cases w with
      | input i => rfl
      | gate j =>
        have hj : j ≠ Fin.last g := fun h => hw (congrArg Wire.gate h)
        have hcast : (j.castPred hj).castSucc = j := Fin.castSucc_castPred j hj
        dsimp only [dropLastWire]
        simpa only [Wire.castSucc_gate, hcast] using
          (q.trace_gate_castSucc line I x (.gate (j.castPred hj))).symm
    · cases g with
      | zero => exact k'.elim0
      | succ g' =>
        have hLineAt : ∀ (k : Fin (g' + 1 + 1)) (l : Line σ n (g' + 1 + 1)),
            l = (q.gate line).lines k →
            ∀ a : Fin (σ.Arity l.op), l.wires a ≠ .gate k'.castSucc := by
          intro k l hl
          subst hl
          exact hunused k
        have hqUnused : ∀ (k : Fin (g' + 1)) (a : Fin (σ.Arity (q.lines k).op)),
            (q.lines k).wires a ≠ .gate k' := by
          intro k a heq
          have h := hLineAt k.castSucc ((q.lines k).mapWires Wire.Renaming.castSucc)
            (Program.lines_gate_castSucc q line k).symm a
          exact h (by simp [heq, Wire.Renaming.castSucc])
        have hlineUnused : ∀ a : Fin (σ.Arity line.op), line.wires a ≠ .gate k' := by
          intro a heq
          have h := hLineAt (Fin.last (g' + 1)) (line.mapWires Wire.Renaming.castSucc)
            (Program.lines_gate_last q line).symm a
          exact h (by simp [heq, Wire.Renaming.castSucc])
        obtain ⟨q', ρ', htrace', hfan'⟩ := Program.exists_deleteUnusedGate q k' hqUnused
        let line' : Line σ n g' :=
          { op := line.op
            wires := fun a => ρ' (line.wires a) (hlineUnused a) }
        refine ⟨q'.gate line', stepDeletedWire ρ', ?_, fun r hp => ⟨hfan' r hp.1, hp.2⟩⟩
        intro U I x w hw
        cases w with
        | input i =>
          simp only [stepDeletedWire, Program.trace_gate_castSucc, Program.trace_input]
          exact htrace' I x (.input i) (by simp)
        | gate j =>
          by_cases hj : j = Fin.last (g' + 1)
          · subst hj
            simp only [stepDeletedWire, ↓reduceDIte, Program.trace_gate_last, line']
            congr 1
            funext a
            exact htrace' I x (line.wires a) (hlineUnused a)
          · simp only [stepDeletedWire, hj, ↓reduceDIte, Program.trace_gate_castSucc]
            have hcast : (j.castPred hj).castSucc = j := Fin.castSucc_castPred j hj
            rw [htrace']
            simpa only [Wire.castSucc_gate, hcast] using
              (q.trace_gate_castSucc line I x (.gate (j.castPred hj))).symm

/-- **Dead-gate elimination**: every circuit has an equivalent circuit with `NoDeadGates`
(*normalized* in [FanLiYang2022], Definition 7.1), no more gates, and the same fan-in bounds. -/
theorem Circuit.exists_noDeadGates (C : Circuit σ n m) :
    ∃ C' : Circuit σ n m, C'.NoDeadGates ∧ C'.size ≤ C.size ∧
      (∀ {U : Type u} (I : Interpretation σ U) (x : Fin n → U), C'.eval I x = C.eval I x) ∧
      (∀ r, C.FanInAtMost r → C'.FanInAtMost r) := by
  suffices ∀ s (C : Circuit σ n m), C.size = s →
      ∃ C' : Circuit σ n m, C'.NoDeadGates ∧ C'.size ≤ C.size ∧
        (∀ {U : Type u} (I : Interpretation σ U) (x : Fin n → U), C'.eval I x = C.eval I x) ∧
        (∀ r, C.FanInAtMost r → C'.FanInAtMost r) from this C.size C rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hs
    by_cases hnoDead : C.NoDeadGates
    · exact ⟨C, hnoDead, le_rfl, fun _ _ => rfl, fun _ h => h⟩
    · unfold Circuit.NoDeadGates at hnoDead
      push Not at hnoDead
      obtain ⟨k₀, hout0, hnotOut⟩ := hnoDead
      rcases C with ⟨p, outputs⟩
      cases s with
      | zero => exact (hs ▸ k₀).elim0
      | succ g =>
        subst hs
        have hunused : ∀ (k : Fin (g + 1)) (a : Fin (σ.Arity (p.lines k).op)),
            (p.lines k).wires a ≠ .gate k₀ := by
          intro k a
          exact (Circuit.outDeg_eq_zero_iff ⟨p, outputs⟩).mp hout0 ⟨k, a⟩
        have houtNe : ∀ j : Fin m, outputs j ≠ .gate k₀ := by
          intro j hj
          exact hnotOut (Circuit.mem_outputsFinset ⟨p, outputs⟩ |>.mpr ⟨j, hj⟩)
        obtain ⟨q, ρ, htrace, hfan⟩ := Program.exists_deleteUnusedGate.{v, u} p k₀ hunused
        let C₁ : Circuit σ n m := ⟨q, fun j => ρ (outputs j) (houtNe j)⟩
        obtain ⟨C', hC'noDead, hC'size, hC'eval, hC'fan⟩ := ih g (Nat.lt_succ_self g) C₁ rfl
        refine ⟨C', hC'noDead, hC'size.trans (Nat.le_succ g), ?_,
          fun r hr => hC'fan r (hfan r hr)⟩
        intro U I x
        rw [hC'eval I x]
        funext j
        exact htrace I x (outputs j) (houtNe j)

/-- An input wire of out-degree `0` that is not a designated output wire has no effect on circuit
evaluation under any interpretation. -/
theorem Circuit.eval_update_of_outDeg_input_eq_zero {U : Type u} [DecidableEq (Fin n)]
    (C : Circuit σ n m) (I : Interpretation σ U) {i : Fin n}
    (hout : C.outDeg (.input i) = 0) (hnotOut : .input i ∉ C.outputsFinset)
    (ρ : Fin n → U) (b : U) :
    C.eval I (Function.update ρ i b) = C.eval I ρ := by
  have hwire : ∀ w : Wire n C.size, w ≠ .input i →
      C.program.trace I (Function.update ρ i b) w = C.program.trace I ρ w := by
    intro w
    refine C.program.wire_induction (P := fun w => w ≠ .input i →
      C.program.trace I (Function.update ρ i b) w = C.program.trace I ρ w)
      (fun z hz => ?_) (fun k ih _ => ?_) w
    · have hzi : z ≠ i := fun h => hz (congrArg Wire.input h)
      simp [Function.update_of_ne hzi]
    · rw [C.program.trace_gate, C.program.trace_gate]
      congr 1
      funext a
      exact ih a ((C.outDeg_eq_zero_iff.mp hout) ⟨k, a⟩)
  funext j
  have hj : C.outputs j ≠ .input i := fun h => hnotOut (C.mem_outputsFinset.mpr ⟨j, h⟩)
  exact hwire (C.outputs j) hj

/-! ### Critical paths and Lemma 7.4 -/

/-- If `v` has a unique outgoing slot `s`, return `some s`; otherwise `none`. -/
@[expose] def Circuit.uniqueReaderSlot (C : Circuit σ n m) (v : Wire n C.size) : Option C.Slot :=
  match C.slotReaders v with
  | [s] => some s
  | _ => none

theorem Circuit.uniqueReaderSlot_eq_some_iff (C : Circuit σ n m) {v : Wire n C.size} {s : C.Slot} :
    C.uniqueReaderSlot v = some s ↔ C.slotReaders v = [s] := by
  unfold Circuit.uniqueReaderSlot
  split
  · rename_i s' hs'
    simp [hs']
  · rename_i hnot
    simp only [reduceCtorEq, false_iff]
    intro hs
    exact hnot s hs

theorem Circuit.uniqueReaderSlot_eq_none_iff (C : Circuit σ n m) {v : Wire n C.size} :
    C.uniqueReaderSlot v = none ↔ C.outDeg v ≠ 1 := by
  unfold Circuit.uniqueReaderSlot
  split
  · rename_i s hs
    simp [Circuit.outDeg, hs]
  · rename_i hnot
    simp only [true_iff]
    intro h1
    obtain ⟨s, hs⟩ := C.outDeg_eq_one_iff.mp h1
    exact hnot s hs

/-- Follow unique outgoing gate slots starting from `v` for at most `fuel` steps. -/
@[expose] def Circuit.criticalPathAux (C : Circuit σ n m) :
    ℕ → Wire n C.size → List (Wire n C.size)
  | 0, v => [v]
  | fuel + 1, v =>
      match C.uniqueReaderSlot v with
      | some s => v :: C.criticalPathAux fuel (.gate s.1)
      | none => [v]

/-- `C.criticalPathAux` is never empty. -/
theorem Circuit.criticalPathAux_ne_nil (C : Circuit σ n m) (fuel : ℕ) (v : Wire n C.size) :
    C.criticalPathAux fuel v ≠ [] := by
  cases fuel with
  | zero => simp [Circuit.criticalPathAux]
  | succ fuel =>
    cases h : C.uniqueReaderSlot v <;> simp [Circuit.criticalPathAux, h]

/-- The first wire of `C.criticalPathAux fuel v` is `v`. -/
@[simp] theorem Circuit.head_criticalPathAux (C : Circuit σ n m) (fuel : ℕ) (v : Wire n C.size) :
    (C.criticalPathAux fuel v).head (C.criticalPathAux_ne_nil fuel v) = v := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases h : C.uniqueReaderSlot v <;> simp [Circuit.criticalPathAux, h]

/-- Every wire in the tail of `C.criticalPathAux fuel v` has strictly larger rank than `v`. -/
theorem Circuit.rank_lt_of_mem_tail_criticalPathAux (C : Circuit σ n m) :
    ∀ (fuel : ℕ) (v w : Wire n C.size), w ∈ (C.criticalPathAux fuel v).tail → v.rank < w.rank
  | 0, _, _, hw => by simp [Circuit.criticalPathAux] at hw
  | fuel + 1, v, w, hw => by
    cases h : C.uniqueReaderSlot v with
    | none => simp [Circuit.criticalPathAux, h] at hw
    | some s =>
      simp only [Circuit.criticalPathAux, h, List.tail_cons] at hw
      have hs := C.uniqueReaderSlot_eq_some_iff.mp h
      have hstep : v.rank < (Wire.gate s.1 : Wire n C.size).rank :=
        C.rank_lt_of_slotWire_eq (C.mem_slotReaders.mp (by simp [hs]))
      have hne := C.criticalPathAux_ne_nil fuel (.gate s.1)
      rw [← List.cons_head_tail hne] at hw
      simp only [head_criticalPathAux, List.mem_cons] at hw
      rcases hw with rfl | htail
      · exact hstep
      · exact hstep.trans (C.rank_lt_of_mem_tail_criticalPathAux fuel (.gate s.1) w htail)

/-- Every wire in the tail of `C.criticalPathAux fuel v` is an internal gate wire. -/
theorem Circuit.gate_of_mem_tail_criticalPathAux (C : Circuit σ n m) (fuel : ℕ)
    (v w : Wire n C.size) (hw : w ∈ (C.criticalPathAux fuel v).tail) :
    ∃ k : Fin C.size, w = .gate k := by
  have hlt := C.rank_lt_of_mem_tail_criticalPathAux fuel v w hw
  cases w with
  | input _ => simp at hlt
  | gate k => exact ⟨k, rfl⟩

/-- `C.criticalPathAux fuel v` contains no duplicate wires. -/
theorem Circuit.nodup_criticalPathAux (C : Circuit σ n m) :
    ∀ (fuel : ℕ) (v : Wire n C.size), (C.criticalPathAux fuel v).Nodup
  | 0, v => by simp [Circuit.criticalPathAux]
  | fuel + 1, v => by
    cases h : C.uniqueReaderSlot v with
    | none => simp [Circuit.criticalPathAux, h]
    | some s =>
      simp only [Circuit.criticalPathAux, h, List.nodup_cons]
      refine ⟨fun hmem => ?_, C.nodup_criticalPathAux fuel (.gate s.1)⟩
      have hs := C.uniqueReaderSlot_eq_some_iff.mp h
      have hstep : v.rank < (Wire.gate s.1 : Wire n C.size).rank :=
        C.rank_lt_of_slotWire_eq (C.mem_slotReaders.mp (by simp [hs]))
      have hne := C.criticalPathAux_ne_nil fuel (.gate s.1)
      rw [← List.cons_head_tail hne] at hmem
      simp only [head_criticalPathAux, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · rw [hhead] at hstep
        exact Nat.lt_irrefl _ hstep
      · exact Nat.lt_irrefl _
          (hstep.trans (C.rank_lt_of_mem_tail_criticalPathAux fuel (.gate s.1) v htail))

/-- Along `C.criticalPathAux fuel v`, topological ranks strictly increase with list index. -/
theorem Circuit.rank_lt_criticalPathAux_getElem (C : Circuit σ n m) :
    ∀ (fuel : ℕ) (v : Wire n C.size) {i j : ℕ}
      (hi : i < (C.criticalPathAux fuel v).length)
      (hj : j < (C.criticalPathAux fuel v).length),
      i < j → (C.criticalPathAux fuel v)[i].rank < (C.criticalPathAux fuel v)[j].rank
  | 0, v, i, j, hi, hj, hij => by
    simp only [Circuit.criticalPathAux, List.length_singleton] at hi hj
    omega
  | fuel + 1, v, i, j, hi, hj, hij => by
    cases h : C.uniqueReaderSlot v with
    | none =>
      simp only [Circuit.criticalPathAux, h, List.length_singleton] at hi hj
      omega
    | some s =>
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j' =>
          have hj' : j' < (C.criticalPathAux fuel (.gate s.1)).length := by
            simp only [Circuit.criticalPathAux, h, List.length_cons] at hj
            omega
          have hmem : (C.criticalPathAux fuel (.gate s.1))[j'] ∈
              (C.criticalPathAux (fuel + 1) v).tail := by
            simp only [Circuit.criticalPathAux, h, List.tail_cons]
            exact List.getElem_mem hj'
          have hlt := C.rank_lt_of_mem_tail_criticalPathAux (fuel + 1) v _ hmem
          simpa only [Circuit.criticalPathAux, h, List.getElem_cons_zero,
            List.getElem_cons_succ] using hlt
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          have hi' : i' < (C.criticalPathAux fuel (.gate s.1)).length := by
            simp only [Circuit.criticalPathAux, h, List.length_cons] at hi
            omega
          have hj' : j' < (C.criticalPathAux fuel (.gate s.1)).length := by
            simp only [Circuit.criticalPathAux, h, List.length_cons] at hj
            omega
          simpa only [Circuit.criticalPathAux, h, List.getElem_cons_succ] using
            C.rank_lt_criticalPathAux_getElem fuel (.gate s.1) hi' hj' (by omega)

/-- Every consecutive pair `(p[i], p[i + 1])` in `C.criticalPathAux fuel v` witnesses a unique
outgoing slot reading `p[i]` at gate `p[i + 1]`. -/
theorem Circuit.criticalPathAux_step (C : Circuit σ n m) :
    ∀ (fuel : ℕ) (v : Wire n C.size) {i : ℕ}
      (hi : i + 1 < (C.criticalPathAux fuel v).length),
      ∃ s : C.Slot,
        C.slotReaders ((C.criticalPathAux fuel v)[i]'(Nat.lt_of_succ_lt hi)) = [s] ∧
        (C.criticalPathAux fuel v)[i + 1] = .gate s.1
  | 0, v, i, hi => by
    simp [Circuit.criticalPathAux] at hi
  | fuel + 1, v, i, hi => by
    cases h : C.uniqueReaderSlot v with
    | none =>
      simp [Circuit.criticalPathAux, h] at hi
    | some s =>
      cases i with
      | zero =>
        refine ⟨s, ?_, ?_⟩
        · simpa only [Circuit.criticalPathAux, h, List.getElem_cons_zero] using
            C.uniqueReaderSlot_eq_some_iff.mp h
        · have hpos : 0 < (C.criticalPathAux fuel (.gate s.1)).length :=
            List.length_pos_iff.mpr (C.criticalPathAux_ne_nil fuel (.gate s.1))
          simp only [Circuit.criticalPathAux, h, List.getElem_cons_succ, List.getElem_zero hpos,
            C.head_criticalPathAux]
      | succ i' =>
        have hi' : i' + 1 < (C.criticalPathAux fuel (.gate s.1)).length := by
          simp only [Circuit.criticalPathAux, h, List.length_cons] at hi
          omega
        simpa only [Circuit.criticalPathAux, h, List.getElem_cons_succ] using
          C.criticalPathAux_step fuel (.gate s.1) hi'

/-- When `C.size ≤ fuel + v.rank`, the last wire of `C.criticalPathAux fuel v` does not have
out-degree `1`. -/
theorem Circuit.outDeg_getLast_criticalPathAux_ne_one (C : Circuit σ n m) :
    ∀ (fuel : ℕ) (v : Wire n C.size), C.size ≤ fuel + v.rank →
      C.outDeg ((C.criticalPathAux fuel v).getLast (C.criticalPathAux_ne_nil fuel v)) ≠ 1
  | 0, v, h => by
    simp only [Nat.zero_add] at h
    have h0 : C.outDeg v = 0 := by
      rw [C.outDeg_eq_zero_iff]
      intro s hs
      have hlt := C.rank_lt_of_slotWire_eq hs
      have hle := (Wire.gate s.1 : Wire n C.size).rank_le
      omega
    simp [Circuit.criticalPathAux, h0]
  | fuel + 1, v, h => by
    cases hu : C.uniqueReaderSlot v with
    | none =>
      simp only [Circuit.criticalPathAux, hu, List.getLast_singleton]
      exact C.uniqueReaderSlot_eq_none_iff.mp hu
    | some s =>
      have hs := C.uniqueReaderSlot_eq_some_iff.mp hu
      have hstep : v.rank < (Wire.gate s.1 : Wire n C.size).rank :=
        C.rank_lt_of_slotWire_eq (C.mem_slotReaders.mp (by simp [hs]))
      simp only [Circuit.criticalPathAux, hu,
        List.getLast_cons (C.criticalPathAux_ne_nil fuel (.gate s.1))]
      exact C.outDeg_getLast_criticalPathAux_ne_one fuel (.gate s.1) (by omega)

/-- The *critical path* starting at input `x` in `C` (Fan–Li–Yang [FanLiYang2022],
Definition 7.1). -/
@[expose] def Circuit.criticalPath (C : Circuit σ n m) (x : Fin n) : List (Wire n C.size) :=
  C.criticalPathAux C.size (.input x)

/-- Every critical path is nonempty. -/
theorem Circuit.criticalPath_ne_nil (C : Circuit σ n m) (x : Fin n) :
    C.criticalPath x ≠ [] :=
  C.criticalPathAux_ne_nil C.size (.input x)

/-- The terminal wire of the critical path starting at input `x`. -/
@[expose] def Circuit.criticalEndpoint (C : Circuit σ n m) (x : Fin n) : Wire n C.size :=
  (C.criticalPath x).getLast (C.criticalPath_ne_nil x)

@[simp] theorem Circuit.head_criticalPath (C : Circuit σ n m) (x : Fin n) :
    (C.criticalPath x).head (C.criticalPath_ne_nil x) = .input x :=
  C.head_criticalPathAux C.size (.input x)

@[simp] theorem Circuit.criticalPath_zero_getElem (C : Circuit σ n m) (x : Fin n) :
    (C.criticalPath x)[0]'(List.length_pos_iff.mpr (C.criticalPath_ne_nil x)) = .input x := by
  simp [List.getElem_zero]

theorem Circuit.nodup_criticalPath (C : Circuit σ n m) (x : Fin n) :
    (C.criticalPath x).Nodup :=
  C.nodup_criticalPathAux C.size (.input x)

theorem Circuit.gate_of_mem_tail_criticalPath (C : Circuit σ n m) (x : Fin n)
    {w : Wire n C.size} (hw : w ∈ (C.criticalPath x).tail) :
    ∃ k : Fin C.size, w = .gate k :=
  C.gate_of_mem_tail_criticalPathAux C.size (.input x) w hw

theorem Circuit.criticalEndpoint_mem (C : Circuit σ n m) (x : Fin n) :
    C.criticalEndpoint x ∈ (C.criticalPath x).toFinset :=
  List.mem_toFinset.mpr (List.getLast_mem (C.criticalPath_ne_nil x))

/-- The terminal wire of every critical path has out-degree different from `1`. -/
theorem Circuit.outDeg_criticalEndpoint_ne_one (C : Circuit σ n m) (x : Fin n) :
    C.outDeg (C.criticalEndpoint x) ≠ 1 :=
  C.outDeg_getLast_criticalPathAux_ne_one C.size (.input x) (by simp)

/-- **Fan–Li–Yang Lemma 7.4**: every circuit of fan-in at most `2` with `n` inputs, `m` outputs,
no dead gates (*normalized* in [FanLiYang2022]), no isolated variable, and pairwise disjoint
critical paths has at least `2 * n - 2 * m` gates. -/
theorem Circuit.two_mul_sub_two_mul_le_size (C : Circuit σ n m)
    (hfan : C.FanInAtMost 2) (hnoDead : C.NoDeadGates) (hiso : ¬ C.HasIsolatedVar)
    (hdisj : Pairwise fun x y => Disjoint (C.criticalPath x).toFinset (C.criticalPath y).toFinset) :
    2 * n - 2 * m ≤ C.size := by
  let bonus : Wire n C.size → ℕ := fun v => if v ∈ C.outputsFinset then 2 else 0
  have hzero_out : ∀ v : Wire n C.size, C.outDeg v = 0 → v ∈ C.outputsFinset := by
    intro v hv
    cases v with
    | input i =>
      by_contra hnot
      exact hiso ⟨i, hv, hnot⟩
    | gate k => exact hnoDead k hv
  have hge1 : ∀ v : Wire n C.size, 1 ≤ C.outDeg v + bonus v := by
    intro v
    by_cases hv : C.outDeg v = 0
    · have hout := hzero_out v hv
      simp [bonus, hout]
    · omega
  have hge2_end :
      ∀ x : Fin n, 2 ≤ C.outDeg (C.criticalEndpoint x) + bonus (C.criticalEndpoint x) := by
    intro x
    have hne1 := C.outDeg_criticalEndpoint_ne_one x
    by_cases hv : C.outDeg (C.criticalEndpoint x) = 0
    · have hout := hzero_out _ hv
      simp [bonus, hv, hout]
    · omega
  have hinj : Function.Injective C.criticalEndpoint := by
    intro x y hxy
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne)
      (C.criticalEndpoint_mem x) (hxy ▸ C.criticalEndpoint_mem y)
  let E : Finset (Wire n C.size) := Finset.univ.image C.criticalEndpoint
  have hcardE : E.card = n := by
    simp [E, Finset.card_image_of_injective _ hinj]
  have hcardCompl : Eᶜ.card = C.size := by
    rw [Finset.card_compl, Wire.card, hcardE]
    omega
  have hlowE : 2 * n ≤ ∑ v ∈ E, (C.outDeg v + bonus v) := by
    calc
      2 * n = ∑ _v ∈ E, 2 := by simp [hcardE, Nat.mul_comm]
      _ ≤ ∑ v ∈ E, (C.outDeg v + bonus v) := by
        refine Finset.sum_le_sum fun v hv => ?_
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
        exact hge2_end x
  have hlowCompl : C.size ≤ ∑ v ∈ Eᶜ, (C.outDeg v + bonus v) := by
    calc
      C.size = ∑ _v ∈ Eᶜ, 1 := by simp [hcardCompl]
      _ ≤ ∑ v ∈ Eᶜ, (C.outDeg v + bonus v) :=
        Finset.sum_le_sum fun v _ => hge1 v
  have hsumBonus : (∑ v : Wire n C.size, bonus v) ≤ 2 * m := by
    have hfilter : (∑ v : Wire n C.size, bonus v) = 2 * C.outputsFinset.card := by
      simp [bonus, Nat.mul_comm]
    exact hfilter.trans_le (Nat.mul_le_mul_left 2 C.card_outputsFinset_le)
  have htotalLow : 2 * n + C.size ≤ ∑ v : Wire n C.size, (C.outDeg v + bonus v) := by
    rw [← Finset.sum_add_sum_compl E]
    exact Nat.add_le_add hlowE hlowCompl
  have htotalHigh : (∑ v : Wire n C.size, (C.outDeg v + bonus v)) ≤ 2 * C.size + 2 * m := by
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add (C.sum_outDeg_le_of_fanInAtMost hfan) hsumBonus
  omega

/-! ### Two-variable bottleneck at intersecting critical paths -/

/-- In a single-output circuit with `NoDeadGates`, the designated output wire has out-degree `0`. -/
theorem Circuit.outDeg_output_eq_zero_of_noDeadGates (C : Circuit σ n 1) (hnoDead : C.NoDeadGates) :
    C.outDeg (C.outputs 0) = 0 := by
  by_contra hpos
  let Reach : Wire n C.size → Wire n C.size → Prop :=
    fun w₁ w₂ => ∃ s : C.Slot, C.slotWire s = w₁ ∧ w₂ = .gate s.1
  have hrank : ∀ w₁ w₂, Relation.TransGen Reach w₁ w₂ → w₁.rank < w₂.rank := by
    intro w₁ w₂ htr
    induction htr with
    | single hr =>
      obtain ⟨s, hs, rfl⟩ := hr
      exact C.rank_lt_of_slotWire_eq hs
    | tail _ hr ih =>
      obtain ⟨s, hs, rfl⟩ := hr
      exact ih.trans (C.rank_lt_of_slotWire_eq hs)
  classical
  let S : Finset (Fin C.size) :=
    Finset.univ.filter fun k => Relation.TransGen Reach (C.outputs 0) (.gate k)
  have hne : S.Nonempty := by
    have hnotNil : C.slotReaders (C.outputs 0) ≠ [] := by
      intro hnil
      exact hpos (by simp [Circuit.outDeg, hnil])
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hnotNil
    exact ⟨s.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Relation.TransGen.single ⟨s, C.mem_slotReaders.mp hs, rfl⟩⟩⟩
  let kMax := S.max' hne
  have hkMaxMem : Relation.TransGen Reach (C.outputs 0) (.gate kMax) :=
    (Finset.mem_filter.mp (Finset.max'_mem S hne)).2
  have hkMaxOut0 : C.outDeg (.gate kMax) = 0 := by
    rw [C.outDeg_eq_zero_iff]
    intro s hs
    have hsMem : s.1 ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.TransGen.tail hkMaxMem ⟨s, hs, rfl⟩⟩
    have hle : s.1 ≤ kMax := Finset.le_max' S s.1 hsMem
    have hlt : kMax < s.1 := C.program.lt_of_lines_wires_eq_gate s.1 s.2 kMax hs
    exact Nat.lt_irrefl _ (hlt.trans_le hle)
  obtain ⟨j, hj⟩ := C.mem_outputsFinset.mp (hnoDead kMax hkMaxOut0)
  have hj0 : j = 0 := Subsingleton.elim j 0
  rw [hj0] at hj
  have hlt := hrank _ _ hkMaxMem
  rw [hj] at hlt
  exact Nat.lt_irrefl _ hlt

/-- **Critical-path bottleneck lemma**: if two distinct input variables `x ≠ y` of a single-output
fan-in-`2` circuit `C` with `NoDeadGates` have intersecting critical paths, then there exists a
single binary operation `opG : U → U → U` (determined by the first shared gate `G` and independent
of the restriction `ρ`) such that for every assignment `ρ : Fin n → U` there exist unary functions
`f₁, f₂, f₃ : U → U` satisfying
`C.eval I (Function.update (Function.update ρ x bx) y by_) 0 = f₁ (opG (f₂ bx) (f₃ by_))`
for all `bx, by_ : U`. -/
theorem Circuit.exists_bottleneck_of_not_disjoint_criticalPath {U : Type u} [DecidableEq (Fin n)]
    (C : Circuit σ n 1) (I : Interpretation σ U)
    (hfan : C.FanInAtMost 2) (hnoDead : C.NoDeadGates) {x y : Fin n} (hxy : x ≠ y)
    (hinter : ¬ Disjoint (C.criticalPath x).toFinset (C.criticalPath y).toFinset) :
    ∃ opG : U → U → U, ∀ ρ : Fin n → U, ∃ f₁ f₂ f₃ : U → U, ∀ bx by_ : U,
      C.eval I (Function.update (Function.update ρ x bx) y by_) 0 =
        f₁ (opG (f₂ bx) (f₃ by_)) := by
  classical
  set px := C.criticalPath x
  set py := C.criticalPath y
  rw [Finset.not_disjoint_iff] at hinter
  obtain ⟨wCommon, hwPx, hwPy⟩ := hinter
  rw [List.mem_toFinset] at hwPx hwPy
  obtain ⟨idxCommon, hidxLt, rfl⟩ := List.getElem_of_mem hwPx
  let Ix : Finset (Fin px.length) := Finset.univ.filter fun i => px[i] ∈ py
  have hIxNe : Ix.Nonempty := ⟨⟨idxCommon, hidxLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwPy⟩⟩
  let i₀ : Fin px.length := Ix.min' hIxNe
  have hi₀Mem : px[i₀] ∈ py := (Finset.mem_filter.mp (Finset.min'_mem Ix hIxNe)).2
  have hi₀Min : ∀ (i : ℕ) (hi : i < px.length), i < i₀.val → px[i] ∉ py := by
    intro i hi hlt hmem
    have hle := Finset.min'_le Ix ⟨i, hi⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
    exact Nat.not_lt.mpr hle hlt
  have hinputNotPy : Wire.input x ∉ py := by
    have hpyNe : py ≠ [] := C.criticalPath_ne_nil y
    rw [← List.cons_head_tail hpyNe]
    have hheadY : py.head hpyNe = .input y := C.head_criticalPath y
    rw [hheadY]
    simp only [List.mem_cons, Wire.input.injEq, hxy, false_or]
    intro htail
    obtain ⟨k, hk⟩ := C.gate_of_mem_tail_criticalPath y htail
    cases hk
  have hi₀Pos : 0 < i₀.val := by
    by_contra h0
    have hz : i₀.val = 0 := by omega
    have hhead : px[i₀] = .input x := by simp [px, hz]
    exact hinputNotPy (hhead ▸ hi₀Mem)
  obtain ⟨j₀val, hj₀Lt, hj₀Eq⟩ := List.getElem_of_mem hi₀Mem
  have hj₀Pos : 0 < j₀val := by
    by_contra h0
    have hz : j₀val = 0 := by omega
    have hhead : py[j₀val] = .input y := by simp [py, hz]
    have hmemTail : px[i₀] ∈ px.tail := by
      have htailIdx : i₀.val - 1 < px.tail.length := by
        simp only [List.length_tail]
        omega
      have hget : px.tail[i₀.val - 1] = px[i₀] := by
        rw [List.getElem_tail]
        congr 1
        omega
      rw [← hget]
      exact List.getElem_mem htailIdx
    obtain ⟨k, hk⟩ := C.gate_of_mem_tail_criticalPath x hmemTail
    rw [← hj₀Eq, hhead] at hk
    cases hk
  set a := i₀.val - 1
  set b := j₀val - 1
  have ha1 : a + 1 = i₀.val := by omega
  have hb1 : b + 1 = j₀val := by omega
  have haLt : a + 1 < px.length := ha1 ▸ i₀.isLt
  have hbLt : b + 1 < py.length := hb1 ▸ hj₀Lt
  obtain ⟨sx, hsxRead, hsxGate⟩ := C.criticalPathAux_step C.size (.input x) haLt
  obtain ⟨sy, hsyRead, hsyGate⟩ := C.criticalPathAux_step C.size (.input y) hbLt
  change C.slotReaders (px[a]'(Nat.lt_of_succ_lt haLt)) = [sx] at hsxRead
  change px[a + 1] = .gate sx.1 at hsxGate
  change C.slotReaders (py[b]'(Nat.lt_of_succ_lt hbLt)) = [sy] at hsyRead
  change py[b + 1] = .gate sy.1 at hsyGate
  have hGateEq : (Wire.gate sx.1 : Wire n C.size) = .gate sy.1 := by
    calc
      (Wire.gate sx.1 : Wire n C.size) = px[a + 1] := hsxGate.symm
      _ = px[i₀] := by simp [ha1]
      _ = py[j₀val] := hj₀Eq.symm
      _ = py[b + 1] := by simp [hb1]
      _ = .gate sy.1 := hsyGate
  have hGeq : sx.1 = sy.1 := Wire.gate.inj hGateEq
  set G : Fin C.size := sx.1
  let sySlot : Fin (σ.Arity (C.program.lines G).op) := hGeq ▸ sy.2
  have hsxWire : C.slotWire ⟨G, sx.2⟩ = px[a]'(Nat.lt_of_succ_lt haLt) :=
    C.mem_slotReaders.mp (by simp [G, hsxRead])
  have hsyWire : C.slotWire ⟨G, sySlot⟩ = py[b]'(Nat.lt_of_succ_lt hbLt) := by
    have h1 : C.slotWire sy = py[b]'(Nat.lt_of_succ_lt hbLt) :=
      C.mem_slotReaders.mp (by simp [hsyRead])
    have hsigma : (⟨G, sySlot⟩ : C.Slot) = sy := by
      rcases sy with ⟨gy, ay⟩
      dsimp only [G] at hGeq
      subst hGeq
      rfl
    rwa [hsigma]
  have hslotsNe : sx.2 ≠ sySlot := by
    intro heq
    have hpxaEq : px[a]'(Nat.lt_of_succ_lt haLt) = py[b]'(Nat.lt_of_succ_lt hbLt) := by
      rw [← hsxWire, ← hsyWire, heq]
    exact hi₀Min a (Nat.lt_of_succ_lt haLt) (by omega)
      (hpxaEq ▸ List.getElem_mem (Nat.lt_of_succ_lt hbLt))
  have harityG : σ.Arity (C.program.lines G).op ≤ 2 :=
    Program.fanInAtMost_iff.mp hfan G
  let opG : U → U → U := fun u v =>
    I (C.program.lines G).op fun t => if t = sx.2 then u else v
  have hopG : ∀ val : Fin (σ.Arity (C.program.lines G).op) → U,
      I (C.program.lines G).op val = opG (val sx.2) (val sySlot) := by
    intro val
    dsimp only [opG]
    congr 1
    funext t
    split_ifs with ht
    · rw [ht]
    · have htEq : t = sySlot := by
        apply Fin.ext
        have ht2 : t.val < 2 := t.isLt.trans_le harityG
        have hsx2 : sx.2.val < 2 := sx.2.isLt.trans_le harityG
        have hsy2 : sySlot.val < 2 := sySlot.isLt.trans_le harityG
        have hne1 : sx.2.val ≠ sySlot.val := fun h => hslotsNe (Fin.ext h)
        have hne2 : t.val ≠ sx.2.val := fun h => ht (Fin.ext h)
        omega
      rw [htEq]
  let Px : Finset (Wire n C.size) :=
    Finset.univ.filter fun w => ∃ (i : ℕ) (hi : i < px.length), i ≤ a ∧ px[i] = w
  let Py : Finset (Wire n C.size) :=
    Finset.univ.filter fun w => ∃ (j : ℕ) (hj : j < py.length), j ≤ b ∧ py[j] = w
  have hDisjPxPy : Disjoint Px Py := by
    rw [Finset.disjoint_left]
    intro w hwPx' hwPy'
    obtain ⟨i, hi, _, rfl⟩ := (Finset.mem_filter.mp hwPx').2
    obtain ⟨j, hj, _, heq⟩ := (Finset.mem_filter.mp hwPy').2
    exact hi₀Min i hi (by omega) (heq ▸ List.getElem_mem hj)
  have hRankPx : ∀ w ∈ Px, w.rank < (Wire.gate G : Wire n C.size).rank := by
    intro w hw
    obtain ⟨i, hi, hia, rfl⟩ := (Finset.mem_filter.mp hw).2
    have hlt := C.rank_lt_criticalPathAux_getElem C.size (.input x) hi haLt (by omega)
    change px[i].rank < px[a + 1].rank at hlt
    rwa [hsxGate] at hlt
  have hRankPy : ∀ w ∈ Py, w.rank < (Wire.gate G : Wire n C.size).rank := by
    intro w hw
    obtain ⟨j, hj, hjb, rfl⟩ := (Finset.mem_filter.mp hw).2
    have hlt := C.rank_lt_criticalPathAux_getElem C.size (.input y) hj hbLt (by omega)
    change py[j].rank < py[b + 1].rank at hlt
    rwa [hsyGate, ← hGeq] at hlt
  have hStepPx : ∀ s : C.Slot, C.slotWire s ∈ Px → s.1 = G ∨ Wire.gate s.1 ∈ Px := by
    intro s hs
    obtain ⟨i, _, hia, hwi⟩ := (Finset.mem_filter.mp hs).2
    have hi1 : i + 1 < px.length := by omega
    obtain ⟨si, hsiRead, hsiGate⟩ := C.criticalPathAux_step C.size (.input x) hi1
    change C.slotReaders px[i] = [si] at hsiRead
    change px[i + 1] = .gate si.1 at hsiGate
    have hsMem : s ∈ C.slotReaders px[i] := C.mem_slotReaders.mpr hwi.symm
    rw [hsiRead, List.mem_singleton] at hsMem
    subst hsMem
    by_cases hiaEq : i = a
    · subst hiaEq
      exact Or.inl (Wire.gate.inj (hsiGate.symm.trans hsxGate))
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i + 1, hi1, by omega, hsiGate⟩)
  have hStepPy : ∀ s : C.Slot, C.slotWire s ∈ Py → s.1 = G ∨ Wire.gate s.1 ∈ Py := by
    intro s hs
    obtain ⟨j, _, hjb, hwj⟩ := (Finset.mem_filter.mp hs).2
    have hj1 : j + 1 < py.length := by omega
    obtain ⟨sj, hsjRead, hsjGate⟩ := C.criticalPathAux_step C.size (.input y) hj1
    change C.slotReaders py[j] = [sj] at hsjRead
    change py[j + 1] = .gate sj.1 at hsjGate
    have hsMem : s ∈ C.slotReaders py[j] := C.mem_slotReaders.mpr hwj.symm
    rw [hsjRead, List.mem_singleton] at hsMem
    subst hsMem
    by_cases hjbEq : j = b
    · subst hjbEq
      have hgate : (Wire.gate s.1 : Wire n C.size) = .gate G := by
        rw [← hsjGate, hsyGate, ← hGeq]
      exact Or.inl (Wire.gate.inj hgate)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j + 1, hj1, by omega, hsjGate⟩)
  refine ⟨opG, fun ρ => ?_⟩
  let assign : U → U → Fin n → U := fun bx by_ =>
    Function.update (Function.update ρ x bx) y by_
  have hassign_x : ∀ bx by_, assign bx by_ x = bx := fun bx by_ => by
    simp [assign, Function.update_of_ne hxy]
  have hassign_y : ∀ bx by_, assign bx by_ y = by_ := fun bx by_ => by
    simp [assign]
  have hassign_other : ∀ z, z ≠ x → z ≠ y → ∀ bx by_, assign bx by_ z = ρ z :=
    fun z hzx hzy bx by_ => by simp [assign, Function.update_of_ne hzy, Function.update_of_ne hzx]
  let Inv : Wire n C.size → Prop := fun w =>
    if w ∈ Px then
      ∃ fx : U → U, ∀ bx by_, C.program.trace I (assign bx by_) w = fx bx
    else if w ∈ Py then
      ∃ fy : U → U, ∀ bx by_, C.program.trace I (assign bx by_) w = fy by_
    else if w.rank < (Wire.gate G : Wire n C.size).rank then
      ∃ c : U, ∀ bx by_, C.program.trace I (assign bx by_) w = c
    else
      ∃ fw : U → U, ∀ bx by_,
        C.program.trace I (assign bx by_) w = fw (C.program.trace I (assign bx by_) (.gate G))
  have hInv : ∀ w : Wire n C.size, Inv w := by
    refine C.program.wire_induction (P := Inv) (fun z => ?_) (fun k ih => ?_)
    · by_cases hzx : z = x
      · subst hzx
        have hxPx : Wire.input z ∈ Px := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, 0, by omega, Nat.zero_le a, C.criticalPath_zero_getElem z⟩
        simp only [Inv, hxPx, ↓reduceIte]
        exact ⟨_root_.id, fun bx by_ => hassign_x bx by_⟩
      · by_cases hzy : z = y
        · subst hzy
          have hyPy : Wire.input z ∈ Py := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, 0, by omega, Nat.zero_le b, C.criticalPath_zero_getElem z⟩
          have hyNotPx : Wire.input z ∉ Px := Finset.disjoint_right.mp hDisjPxPy hyPy
          simp only [Inv, hyNotPx, hyPy, ↓reduceIte]
          exact ⟨_root_.id, fun bx by_ => hassign_y bx by_⟩
        · have hzNotPx : Wire.input z ∉ Px := by
            intro hzMem
            obtain ⟨i, hi, _, heq⟩ := (Finset.mem_filter.mp hzMem).2
            cases i with
            | zero =>
              have := C.criticalPath_zero_getElem x
              rw [show px[0] = Wire.input x from this] at heq
              exact hzx (Wire.input.inj heq).symm
            | succ i' =>
              have hmemTail : px[i' + 1] ∈ px.tail := by
                have htailIdx : i' < px.tail.length := by simp only [List.length_tail]; omega
                rw [← List.getElem_tail (i := i')]
                exact List.getElem_mem htailIdx
              obtain ⟨k, hk⟩ := C.gate_of_mem_tail_criticalPath x hmemTail
              rw [heq] at hk
              cases hk
          have hzNotPy : Wire.input z ∉ Py := by
            intro hzMem
            obtain ⟨j, hj, _, heq⟩ := (Finset.mem_filter.mp hzMem).2
            cases j with
            | zero =>
              have := C.criticalPath_zero_getElem y
              rw [show py[0] = Wire.input y from this] at heq
              exact hzy (Wire.input.inj heq).symm
            | succ j' =>
              have hmemTail : py[j' + 1] ∈ py.tail := by
                have htailIdx : j' < py.tail.length := by simp only [List.length_tail]; omega
                rw [← List.getElem_tail (i := j')]
                exact List.getElem_mem htailIdx
              obtain ⟨k, hk⟩ := C.gate_of_mem_tail_criticalPath y hmemTail
              rw [heq] at hk
              cases hk
          have hzRank : (Wire.input z : Wire n C.size).rank <
              (Wire.gate G : Wire n C.size).rank := by simp
          simp only [Inv, hzNotPx, hzNotPy, hzRank, ↓reduceIte]
          exact ⟨ρ z, fun bx by_ => hassign_other z hzx hzy bx by_⟩
    · by_cases hkPx : Wire.gate k ∈ Px
      · have hkRank := hRankPx _ hkPx
        have hkNeG : k ≠ G := fun h => by subst h; exact Nat.lt_irrefl _ hkRank
        have harg : ∀ t : Fin (σ.Arity (C.program.lines k).op),
            ∃ gt : U → U, ∀ bx by_,
              C.program.trace I (assign bx by_) ((C.program.lines k).wires t) = gt bx := by
          intro t
          let u := (C.program.lines k).wires t
          have huRank : u.rank < (Wire.gate G : Wire n C.size).rank :=
            (C.rank_lt_of_slotWire_eq (s := ⟨k, t⟩) rfl).trans hkRank
          have huNotPy : u ∉ Py := by
            intro huPy
            rcases hStepPy ⟨k, t⟩ huPy with hG | hkPy
            · exact hkNeG hG
            · exact Finset.disjoint_left.mp hDisjPxPy hkPx hkPy
          have iht := ih t
          dsimp only [Inv] at iht
          by_cases huPx : u ∈ Px
          · simp only [u, huPx, ↓reduceIte] at iht
            exact iht
          · simp only [u, huPx, huNotPy, huRank, ↓reduceIte] at iht
            obtain ⟨c, hc⟩ := iht
            exact ⟨fun _ => c, hc⟩
        choose g hg using harg
        simp only [Inv, hkPx, ↓reduceIte]
        refine ⟨fun bx => I (C.program.lines k).op fun t => g t bx, fun bx by_ => ?_⟩
        rw [C.program.trace_gate]
        congr 1
        funext t
        exact hg t bx by_
      · by_cases hkPy : Wire.gate k ∈ Py
        · have hkRank := hRankPy _ hkPy
          have hkNeG : k ≠ G := fun h => by subst h; exact Nat.lt_irrefl _ hkRank
          have harg : ∀ t : Fin (σ.Arity (C.program.lines k).op),
              ∃ gt : U → U, ∀ bx by_,
                C.program.trace I (assign bx by_) ((C.program.lines k).wires t) = gt by_ := by
            intro t
            let u := (C.program.lines k).wires t
            have huRank : u.rank < (Wire.gate G : Wire n C.size).rank :=
              (C.rank_lt_of_slotWire_eq (s := ⟨k, t⟩) rfl).trans hkRank
            have huNotPx : u ∉ Px := by
              intro huPx
              rcases hStepPx ⟨k, t⟩ huPx with hG | hkPx'
              · exact hkNeG hG
              · exact hkPx hkPx'
            have iht := ih t
            dsimp only [Inv] at iht
            by_cases huPy : u ∈ Py
            · simp only [u, huNotPx, huPy, ↓reduceIte] at iht
              exact iht
            · simp only [u, huNotPx, huPy, huRank, ↓reduceIte] at iht
              obtain ⟨c, hc⟩ := iht
              exact ⟨fun _ => c, hc⟩
          choose g hg using harg
          simp only [Inv, hkPx, hkPy, ↓reduceIte]
          refine ⟨fun by_ => I (C.program.lines k).op fun t => g t by_, fun bx by_ => ?_⟩
          rw [C.program.trace_gate]
          congr 1
          funext t
          exact hg t bx by_
        · by_cases hkRank : (Wire.gate k : Wire n C.size).rank <
              (Wire.gate G : Wire n C.size).rank
          · have hkNeG : k ≠ G := fun h => by subst h; exact Nat.lt_irrefl _ hkRank
            have harg : ∀ t : Fin (σ.Arity (C.program.lines k).op),
                ∃ ct : U, ∀ bx by_,
                  C.program.trace I (assign bx by_) ((C.program.lines k).wires t) = ct := by
              intro t
              let u := (C.program.lines k).wires t
              have huRank : u.rank < (Wire.gate G : Wire n C.size).rank :=
                (C.rank_lt_of_slotWire_eq (s := ⟨k, t⟩) rfl).trans hkRank
              have huNotPx : u ∉ Px := by
                intro huPx
                rcases hStepPx ⟨k, t⟩ huPx with hG | hkPx'
                · exact hkNeG hG
                · exact hkPx hkPx'
              have huNotPy : u ∉ Py := by
                intro huPy
                rcases hStepPy ⟨k, t⟩ huPy with hG | hkPy'
                · exact hkNeG hG
                · exact hkPy hkPy'
              have iht := ih t
              dsimp only [Inv] at iht
              simpa only [u, huNotPx, huNotPy, huRank, ↓reduceIte] using iht
            choose c hc using harg
            simp only [Inv, hkPx, hkPy, hkRank, ↓reduceIte]
            refine ⟨I (C.program.lines k).op c, fun bx by_ => ?_⟩
            rw [C.program.trace_gate]
            congr 1
            funext t
            exact hc t bx by_
          · simp only [Inv, hkPx, hkPy, hkRank, ↓reduceIte]
            by_cases hkEqG : k = G
            · subst hkEqG
              exact ⟨_root_.id, fun _ _ => rfl⟩
            · have harg : ∀ t : Fin (σ.Arity (C.program.lines k).op),
                  ∃ gt : U → U, ∀ bx by_,
                    C.program.trace I (assign bx by_) ((C.program.lines k).wires t) =
                      gt (C.program.trace I (assign bx by_) (.gate G)) := by
                intro t
                let u := (C.program.lines k).wires t
                have huNotPx : u ∉ Px := by
                  intro huPx
                  rcases hStepPx ⟨k, t⟩ huPx with hG | hkPx'
                  · exact hkEqG hG
                  · exact hkPx hkPx'
                have huNotPy : u ∉ Py := by
                  intro huPy
                  rcases hStepPy ⟨k, t⟩ huPy with hG | hkPy'
                  · exact hkEqG hG
                  · exact hkPy hkPy'
                have iht := ih t
                dsimp only [Inv] at iht
                by_cases huRank : u.rank < (Wire.gate G : Wire n C.size).rank
                · simp only [u, huNotPx, huNotPy, huRank, ↓reduceIte] at iht
                  obtain ⟨c, hc⟩ := iht
                  exact ⟨fun _ => c, hc⟩
                · simpa only [u, huNotPx, huNotPy, huRank, ↓reduceIte] using iht
              choose g hg using harg
              refine ⟨fun v => I (C.program.lines k).op fun t => g t v, fun bx by_ => ?_⟩
              rw [C.program.trace_gate]
              congr 1
              funext t
              exact hg t bx by_
  have hpxaMem : (px[a]'(Nat.lt_of_succ_lt haLt)) ∈ Px :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, Nat.lt_of_succ_lt haLt, le_rfl, rfl⟩
  have hpybMem : (py[b]'(Nat.lt_of_succ_lt hbLt)) ∈ Py :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, Nat.lt_of_succ_lt hbLt, le_rfl, rfl⟩
  have hpybNotPx : (py[b]'(Nat.lt_of_succ_lt hbLt)) ∉ Px :=
    Finset.disjoint_right.mp hDisjPxPy hpybMem
  have hInvX := hInv (px[a]'(Nat.lt_of_succ_lt haLt))
  simp only [Inv, hpxaMem, ↓reduceIte] at hInvX
  obtain ⟨f₂, hf₂⟩ := hInvX
  have hInvY := hInv (py[b]'(Nat.lt_of_succ_lt hbLt))
  simp only [Inv, hpybNotPx, hpybMem, ↓reduceIte] at hInvY
  obtain ⟨f₃, hf₃⟩ := hInvY
  have hGtrace : ∀ bx by_,
      C.program.trace I (assign bx by_) (.gate G) = opG (f₂ bx) (f₃ by_) := by
    intro bx by_
    rw [C.program.trace_gate, hopG]
    change opG (C.program.trace I (assign bx by_) (C.slotWire ⟨G, sx.2⟩))
      (C.program.trace I (assign bx by_) (C.slotWire ⟨G, sySlot⟩)) = _
    rw [hsxWire, hsyWire, hf₂ bx by_, hf₃ bx by_]
  have hout0 := C.outDeg_output_eq_zero_of_noDeadGates hnoDead
  have houtNotPx : C.outputs 0 ∉ Px := by
    intro hmem
    obtain ⟨i, _, hia, heq⟩ := (Finset.mem_filter.mp hmem).2
    have hi1 : i + 1 < px.length := by omega
    obtain ⟨si, hsiRead, _⟩ := C.criticalPathAux_step C.size (.input x) hi1
    change C.slotReaders px[i] = [si] at hsiRead
    have hout1 : C.outDeg px[i] = 1 := by simp [Circuit.outDeg, hsiRead]
    rw [heq] at hout1
    omega
  have houtNotPy : C.outputs 0 ∉ Py := by
    intro hmem
    obtain ⟨j, _, hjb, heq⟩ := (Finset.mem_filter.mp hmem).2
    have hj1 : j + 1 < py.length := by omega
    obtain ⟨sj, hsjRead, _⟩ := C.criticalPathAux_step C.size (.input y) hj1
    change C.slotReaders py[j] = [sj] at hsjRead
    have hout1 : C.outDeg py[j] = 1 := by simp [Circuit.outDeg, hsjRead]
    rw [heq] at hout1
    omega
  have hInvOut := hInv (C.outputs 0)
  dsimp only [Inv] at hInvOut
  by_cases houtRank : (C.outputs 0).rank < (Wire.gate G : Wire n C.size).rank
  · simp only [houtNotPx, houtNotPy, houtRank, ↓reduceIte] at hInvOut
    obtain ⟨c, hc⟩ := hInvOut
    exact ⟨fun _ => c, f₂, f₃, fun bx by_ => hc bx by_⟩
  · simp only [houtNotPx, houtNotPy, houtRank, ↓reduceIte] at hInvOut
    obtain ⟨f₁, hf₁⟩ := hInvOut
    refine ⟨f₁, f₂, f₃, fun bx by_ => ?_⟩
    change C.program.trace I (assign bx by_) (C.outputs 0) = _
    rw [hf₁ bx by_, hGtrace bx by_]

end Cslib.Circuits

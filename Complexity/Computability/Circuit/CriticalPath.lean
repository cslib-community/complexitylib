/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.FanIn
public import Mathlib.Data.Fintype.Sigma
import Complexity.Computability.Circuit.Program
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
            grind [Circuit.criticalPathAux, List.length_cons]
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
            grind [Circuit.criticalPathAux, List.length_cons]
          have hj' : j' < (C.criticalPathAux fuel (.gate s.1)).length := by
            grind [Circuit.criticalPathAux, List.length_cons]
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
          grind [Circuit.criticalPathAux, List.length_cons]
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
  have hge1 : ∀ v : Wire n C.size, 1 ≤ C.outDeg v + bonus v := by grind
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
  have hcardCompl : Eᶜ.card = C.size := by grind [Finset.card_compl, Wire.card]
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
    have hnotNil : C.slotReaders (C.outputs 0) ≠ [] := by grind [Circuit.outDeg]
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

/-- An input wire lies on the critical path from input `y` only if it is `y` itself: every later
wire of the path is a gate. -/
theorem Circuit.input_mem_criticalPath_iff (C : Circuit σ n m) {x y : Fin n} :
    Wire.input x ∈ C.criticalPath y ↔ x = y := by
  constructor
  · intro h
    rw [← List.cons_head_tail (C.criticalPath_ne_nil y), C.head_criticalPath, List.mem_cons] at h
    rcases h with h | h
    · exact Wire.input.inj h
    · obtain ⟨k, hk⟩ := C.gate_of_mem_tail_criticalPath y h
      cases hk
  · rintro rfl
    exact List.mem_of_getElem (C.criticalPath_zero_getElem x)

/-- Consecutive wires of a critical path: the wire at position `i` has a unique reader slot, whose
gate is the wire at position `i + 1`. -/
private theorem Circuit.criticalPath_step (C : Circuit σ n m) (x : Fin n) {i : ℕ}
    (hi : i + 1 < (C.criticalPath x).length) :
    ∃ s : C.Slot, C.slotReaders (C.criticalPath x)[i] = [s] ∧
      (C.criticalPath x)[i + 1] = .gate s.1 :=
  C.criticalPathAux_step C.size (.input x) hi

/-- Every wire strictly before position `i` of a critical path has smaller rank than the wire at
position `i`. -/
private theorem Circuit.rank_lt_of_mem_take_criticalPath (C : Circuit σ n m) (x : Fin n) {i : ℕ}
    (hi : i < (C.criticalPath x).length) {w : Wire n C.size}
    (hw : w ∈ (C.criticalPath x).take i) : w.rank < (C.criticalPath x)[i].rank := by
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hw
  exact C.rank_lt_criticalPathAux_getElem C.size (.input x) _ hi (by omega)

/-- The prefix of a critical path before position `i` is closed under reading: a slot reading one
of its wires belongs to the gate at position `i` or to a gate of the prefix. -/
private theorem Circuit.gate_mem_take_criticalPath (C : Circuit σ n m) (x : Fin n) {i : ℕ}
    (hi : i < (C.criticalPath x).length) {s : C.Slot}
    (hs : C.slotWire s ∈ (C.criticalPath x).take i) :
    Wire.gate s.1 = (C.criticalPath x)[i] ∨ Wire.gate s.1 ∈ (C.criticalPath x).take i := by
  obtain ⟨j, hj, hjs⟩ := List.mem_take_iff_getElem.mp hs
  obtain ⟨r, hr, hrGate⟩ := C.criticalPath_step x (i := j) (by omega)
  obtain rfl : s = r := by
    simpa [hr] using C.mem_slotReaders.mpr hjs.symm
  rw [← hrGate]
  rcases Nat.lt_or_ge (j + 1) i with hlt | hge
  · exact Or.inr (List.mem_take_iff_getElem.mpr ⟨j + 1, by omega, rfl⟩)
  · obtain rfl : j + 1 = i := by omega
    exact Or.inl rfl

/-- Every wire strictly before position `i` of a critical path has out-degree `1`. -/
private theorem Circuit.outDeg_eq_one_of_mem_take_criticalPath (C : Circuit σ n m) (x : Fin n)
    {i : ℕ} (hi : i < (C.criticalPath x).length) {w : Wire n C.size}
    (hw : w ∈ (C.criticalPath x).take i) : C.outDeg w = 1 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hw
  obtain ⟨r, hr, -⟩ := C.criticalPath_step x (i := j) (by omega)
  simp [Circuit.outDeg, hr]

/-- If the critical paths of two distinct inputs `x` and `y` intersect, they first meet at a gate
`G`: the paths reach `G` from positions `a` and `b`, whose wires read `G` through its slots `tx` and
`ty`, and the prefixes of the two paths up to these positions are disjoint. -/
private theorem Circuit.exists_first_meet_criticalPath (C : Circuit σ n m) {x y : Fin n}
    (hxy : x ≠ y)
    (hinter : ¬ Disjoint (C.criticalPath x).toFinset (C.criticalPath y).toFinset) :
    ∃ (a b : ℕ) (ha : a + 1 < (C.criticalPath x).length) (hb : b + 1 < (C.criticalPath y).length)
      (G : Fin C.size) (tx ty : Fin (σ.Arity (C.program.lines G).op)),
      C.slotReaders (C.criticalPath x)[a] = [⟨G, tx⟩] ∧
      C.slotReaders (C.criticalPath y)[b] = [⟨G, ty⟩] ∧
      (C.criticalPath x)[a + 1] = .gate G ∧ (C.criticalPath y)[b + 1] = .gate G ∧
      ((C.criticalPath x).take (a + 1)).Disjoint ((C.criticalPath y).take (b + 1)) := by
  classical
  obtain ⟨w, hwx, hwy⟩ := Finset.not_disjoint_iff.mp hinter
  rw [List.mem_toFinset] at hwx hwy
  -- `i` is the first position of the path from `x` lying on the path from `y`.
  obtain ⟨i, hlt, hmem, hfirst⟩ : ∃ (i : ℕ) (hi : i < (C.criticalPath x).length),
      (C.criticalPath x)[i] ∈ C.criticalPath y ∧
        ∀ (k : ℕ) (hk : k < i), (C.criticalPath x)[k] ∉ C.criticalPath y := by
    have hlt : (C.criticalPath x).findIdx (· ∈ C.criticalPath y) < (C.criticalPath x).length :=
      List.findIdx_lt_length.mpr ⟨w, hwx, by simpa using hwy⟩
    exact ⟨_, hlt, by simpa using List.findIdx_getElem (w := hlt),
      fun k hk => by simpa using List.not_of_lt_findIdx hk⟩
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hmem
  -- Neither meeting position is the start of its path, since the starts are distinct inputs.
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := i) fun h => by
    subst h
    exact hxy ((C.input_mem_criticalPath_iff).mp (by simpa using hmem))
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := j) fun h => by
    subst h
    rw [C.criticalPath_zero_getElem] at hji
    exact hxy ((C.input_mem_criticalPath_iff).mp (hji ▸ List.getElem_mem _)).symm
  obtain ⟨⟨G, tx⟩, hxRead, hxGate⟩ := C.criticalPath_step x hlt
  obtain ⟨⟨G', ty⟩, hyRead, hyGate⟩ := C.criticalPath_step y hj
  obtain rfl : G = G' := Wire.gate.inj (hxGate.symm.trans (hji.symm.trans hyGate))
  refine ⟨a, b, hlt, hj, G, tx, ty, hxRead, hyRead, hxGate, hyGate,
    List.disjoint_left.mpr fun v hvx hvy => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp hvx
  exact hfirst k (by omega) (List.mem_of_mem_take hvy)

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
  obtain ⟨a, b, ha, hb, G, tx, ty, hxRead, hyRead, hxGate, hyGate, hdisj⟩ :=
    C.exists_first_meet_criticalPath hxy hinter
  /- The prefixes `Px` and `Py` of the two paths before `G` are disjoint, lie below `G`, and are
  closed under reading except into `G`. -/
  set px := C.criticalPath x
  set py := C.criticalPath y
  set Px := px.take (a + 1)
  set Py := py.take (b + 1)
  have hrankX : ∀ w ∈ Px, w.rank < (Wire.gate G : Wire n C.size).rank := fun w hw =>
    hxGate ▸ C.rank_lt_of_mem_take_criticalPath x ha hw
  have hrankY : ∀ w ∈ Py, w.rank < (Wire.gate G : Wire n C.size).rank := fun w hw =>
    hyGate ▸ C.rank_lt_of_mem_take_criticalPath y hb hw
  have hclosedX : ∀ s : C.Slot, C.slotWire s ∈ Px → s.1 = G ∨ Wire.gate s.1 ∈ Px := fun s hs =>
    (C.gate_mem_take_criticalPath x ha hs).imp_left fun h => Wire.gate.inj (h.trans hxGate)
  have hclosedY : ∀ s : C.Slot, C.slotWire s ∈ Py → s.1 = G ∨ Wire.gate s.1 ∈ Py := fun s hs =>
    (C.gate_mem_take_criticalPath y hb hs).imp_left fun h => Wire.gate.inj (h.trans hyGate)
  /- `G` reads `px[a]` through slot `tx` and `py[b]` through slot `ty`; these are distinct, and
  by fan-in `2` they are the only slots of `G`. -/
  have hxWire : C.slotWire ⟨G, tx⟩ = px[a] :=
    C.mem_slotReaders.mp (by rw [hxRead]; exact List.mem_singleton_self _)
  have hyWire : C.slotWire ⟨G, ty⟩ = py[b] :=
    C.mem_slotReaders.mp (by rw [hyRead]; exact List.mem_singleton_self _)
  have hxMem : px[a] ∈ Px := List.mem_take_iff_getElem.mpr ⟨a, by omega, rfl⟩
  have hyMem : py[b] ∈ Py := List.mem_take_iff_getElem.mpr ⟨b, by omega, rfl⟩
  have htxy : tx ≠ ty := by
    rintro rfl
    exact List.disjoint_left.mp hdisj hxMem (hxWire.symm.trans hyWire ▸ hyMem)
  have hslots : ∀ t, t = tx ∨ t = ty := by
    have := Program.fanInAtMost_iff.mp hfan G
    have := Fin.val_ne_of_ne htxy
    omega
  let opG : U → U → U := fun u v => I (C.program.lines G).op fun t => if t = tx then u else v
  refine ⟨opG, fun ρ => ?_⟩
  /- Write `T w (bx, by_)` for the value of wire `w` under `ρ` updated to `bx` at `x` and `by_` at
  `y`. -/
  let assign : U × U → Fin n → U := fun p => Function.update (Function.update ρ x p.1) y p.2
  have hassignX : ∀ p, assign p x = p.1 := fun p => by simp [assign, Function.update_of_ne hxy]
  have hassignY : ∀ p, assign p y = p.2 := fun p => by simp [assign]
  have hassign : ∀ p z, z ≠ x → z ≠ y → assign p z = ρ z := fun p z hzx hzy => by
    simp [assign, Function.update_of_ne hzx, Function.update_of_ne hzy]
  let T : Wire n C.size → U × U → U := fun w p => C.program.trace I (assign p) w
  /- A wire off both prefixes is constant below `G`, and otherwise depends on `(bx, by_)` only
  through the value of `G`. -/
  have hout : ∀ w, w ∉ Px → w ∉ Py → ∀ p q,
      (w.rank < (Wire.gate G : Wire n C.size).rank ∨ T (.gate G) p = T (.gate G) q) →
      T w p = T w q := by
    intro w
    induction w using C.program.wire_induction with
    | input z =>
      intro hzPx hzPy p q _
      have hzx : z ≠ x := by
        rintro rfl
        exact hzPx (List.mem_take_iff_getElem.mpr ⟨0, by omega, C.criticalPath_zero_getElem z⟩)
      have hzy : z ≠ y := by
        rintro rfl
        exact hzPy (List.mem_take_iff_getElem.mpr ⟨0, by omega, C.criticalPath_zero_getElem z⟩)
      simp only [T, Program.trace_input, hassign p z hzx hzy, hassign q z hzx hzy]
    | gate k ih =>
      intro hkx hky p q hpq
      by_cases hkG : k = G
      · subst hkG
        exact hpq.resolve_left (lt_irrefl _)
      simp only [T, Program.trace_gate]
      congr 1
      funext t
      have hlt : (C.slotWire ⟨k, t⟩).rank < (Wire.gate k : Wire n C.size).rank :=
        C.rank_lt_of_slotWire_eq rfl
      refine ih t (fun ht => ?_) (fun ht => ?_) p q (hpq.imp_left hlt.trans)
      · exact (hclosedX ⟨k, t⟩ ht).elim hkG hkx
      · exact (hclosedY ⟨k, t⟩ ht).elim hkG hky
  /- A wire of `Px` depends only on `bx`, and a wire of `Py` only on `by_`. -/
  have hX : ∀ w ∈ Px, ∀ p q : U × U, p.1 = q.1 → T w p = T w q := by
    intro w
    induction w using C.program.wire_induction with
    | input z =>
      intro hz p q hpq
      obtain rfl : z = x := (C.input_mem_criticalPath_iff).mp (List.mem_of_mem_take hz)
      simp only [T, Program.trace_input, hassignX, hpq]
    | gate k ih =>
      intro hk p q hpq
      simp only [T, Program.trace_gate]
      congr 1
      funext t
      by_cases ht : C.slotWire ⟨k, t⟩ ∈ Px
      · exact ih t ht p q hpq
      have hlt : (C.slotWire ⟨k, t⟩).rank < (Wire.gate G : Wire n C.size).rank :=
        (C.rank_lt_of_slotWire_eq rfl).trans (hrankX _ hk)
      refine hout _ ht (fun hy => ?_) p q (Or.inl hlt)
      rcases hclosedY ⟨k, t⟩ hy with hkG | hky
      · exact lt_irrefl _ (hkG ▸ hrankX _ hk)
      · exact List.disjoint_left.mp hdisj hk hky
  have hY : ∀ w ∈ Py, ∀ p q : U × U, p.2 = q.2 → T w p = T w q := by
    intro w
    induction w using C.program.wire_induction with
    | input z =>
      intro hz p q hpq
      obtain rfl : z = y := (C.input_mem_criticalPath_iff).mp (List.mem_of_mem_take hz)
      simp only [T, Program.trace_input, hassignY, hpq]
    | gate k ih =>
      intro hk p q hpq
      simp only [T, Program.trace_gate]
      congr 1
      funext t
      by_cases ht : C.slotWire ⟨k, t⟩ ∈ Py
      · exact ih t ht p q hpq
      have hlt : (C.slotWire ⟨k, t⟩).rank < (Wire.gate G : Wire n C.size).rank :=
        (C.rank_lt_of_slotWire_eq rfl).trans (hrankY _ hk)
      refine hout _ (fun hx => ?_) ht p q (Or.inl hlt)
      rcases hclosedX ⟨k, t⟩ hx with hkG | hkx
      · exact lt_irrefl _ (hkG ▸ hrankY _ hk)
      · exact List.disjoint_right.mp hdisj hk hkx
  /- Hence `G` computes `opG (f₂ bx) (f₃ by_)`, and the output factors through `G`, since it has
  out-degree `0` and so lies on neither prefix. -/
  have hG : ∀ p, T (.gate G) p = opG (T px[a] (p.1, p.1)) (T py[b] (p.2, p.2)) := by
    intro p
    simp only [T, Program.trace_gate, opG]
    congr 1
    funext t
    split_ifs with ht
    · subst ht
      exact (congrArg (T · p) hxWire).trans (hX _ hxMem _ _ rfl)
    · obtain rfl := (hslots t).resolve_left ht
      exact (congrArg (T · p) hyWire).trans (hY _ hyMem _ _ rfl)
  have hout0 := C.outDeg_output_eq_zero_of_noDeadGates hnoDead
  have hfactor : (T (C.outputs 0)).FactorsThrough (T (.gate G)) := by
    intro p q hpq
    refine hout _ (fun h => ?_) (fun h => ?_) p q (Or.inr hpq)
    · have := C.outDeg_eq_one_of_mem_take_criticalPath x ha h
      omega
    · have := C.outDeg_eq_one_of_mem_take_criticalPath y hb h
      omega
  refine ⟨Function.extend (T (.gate G)) (T (C.outputs 0)) _root_.id, fun bx => T px[a] (bx, bx),
    fun by_ => T py[b] (by_, by_), fun bx by_ => ?_⟩
  rw [← hG (bx, by_), hfactor.extend_apply]
  rfl

end Cslib.Circuits

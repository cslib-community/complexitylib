/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateReply
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateVectorCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialVectorGate
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitNodeCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.NormalizePoint

/-!
# Native gate replies for the existing encoded tree

Typed paths are routed to the existing descending tree's interval gate, including constant
source padding. Actual padded register coordinates are normalized before the complete native
gate-vector computation. No gate-table oracle or supplier premise is used.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.GateReply

open Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed Cslib.BitString

private theorem resolve_eq_walk {k q : ℕ} (σ : ℕ)
    (path : List (Fin (k * 3 + 1))) :
    Descending.resolve (BlockComputation.child (scheduleOfNat k q σ)) q path =
      ImplicitPath.walk k (σ, q, path.map Fin.val) := by
  have hnext : Descending.next (BlockComputation.child (scheduleOfNat k q σ)) =
      BlockComputation.child (scheduleOfNat k q σ) := by
    funext n j
    cases n with
    | zero => rfl
    | succ n => simp [Descending.next]
  rw [Descending.resolve, hnext, ImplicitPath.walk_eq]

/-- At an internal typed path, lookup uses exactly the interval reached by native navigation. -/
theorem nodeAt_eq_gate {k q s : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (path : List (Fin (k * 3 + 1)))
    (hdepth : path.length < q) :
    (encodedTree (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) e).nodeAt path =
      .gate (codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
        (Encoding.encode e) (Encoding.decode e)
        (ImplicitPath.walk k (σ, q, path.map Fin.val))) := by
  rw [encodedTree, tree, Descending.nodeAt_tree]
  simp only [Descending.lookup, hdepth, ↓reduceIte, resolve_eq_walk]
  congr 1
  unfold Descending.paddedGate
  split_ifs with hz
  · rw [hz]
    rfl
  · rfl

/-- The active branch preserves every physical clock of the vector subroutine. -/
theorem runFrom_inr {k s : ℕ} {Q : Type} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (state : GateVector.State k Q) (t : ℕ) :
    (machine M e).runFrom w (.inr state) t =
      .inr ((GateVector.machine M e).runFrom w state t) := by
  have hstep (q : GateVector.State k Q) :
      (machine M e).step w (.inr q) = .inr ((GateVector.machine M e).step w q) := by
    simp only [QueryMachine.step, QueryMachine.read, machine, Sum.elim_inr]
    by_cases h : (GateVector.machine M e).halted q = true <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte]
  induction t with
  | zero => rfl
  | succ t ih => rw [QueryMachine.runFrom_succ, ih, hstep, QueryMachine.runFrom_succ]

/-- Any explicitly stored point reducing to the canonical typed point gives the existing tree's
requested gate update. The only hypotheses on storage concern its actual representation. -/
theorem exists_runFrom_nodeAt {k q s p r m : ℕ} {Q : Type} [Finite Q] [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (path : List (Fin (k * 3 + 1)))
    (x : Fin (k * 3 + 1) → Fin r → ZMod p) (point : List ℕ)
    (hpoint : NormalizePoint.normalize p point =
      List.ofFn (fun a : Fin ((k * 3 + 1) * r) => (blocksEquiv.symm x a).val))
    (hcapacity : r ≤ ((2 ^ m) ^ ((k * 3 + 1) * r)).size)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (hsp : 2 ^ m ≤ p)
    (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p)) :
    let params : GateVector.Params := (((w.length, b, 0, 0, m, 0, r * m),
      (p, 2 ^ m, (k * 3 + 1) * r), point, (2 ^ m) ^ ((k * 3 + 1) * r)), r)
    let args : Args := ((σ, q, path.map Fin.val), params)
    ∃ T values, (machine M e).halted ((machine M e).runFrom w (initial M e args) T) = true ∧
      answer ((machine M e).runFrom w (initial M e args) T) = (0, values) ∧
      ∀ j : Fin r, (values.getD j.val 0 : ZMod p) =
        match (encodedTree (MultiTapePTM.ofDeterministic M) w b
          (scheduleOfNat k q σ) e).nodeAt path with
        | .gate f => Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb) f x j
        | _ => 0 := by
  classical
  dsimp only
  let params : GateVector.Params := (((w.length, b, 0, 0, m, 0, r * m),
    (p, 2 ^ m, (k * 3 + 1) * r), point, (2 ^ m) ^ ((k * 3 + 1) * r)), r)
  let address : ImplicitPath.WalkArgs := (σ, q, path.map Fin.val)
  let index := ImplicitPath.walk k address
  have hprepare : prepare k (address, params) =
      (QueryGate.gateParams (s := 2 ^ m) (w.length, b, σ, index - 1, m, 0, r * m) x, r) := by
    change (((w.length, b, σ, index - 1, m, 0, r * m),
      (p, 2 ^ m, (k * 3 + 1) * r), NormalizePoint.normalize p point,
      (2 ^ m) ^ ((k * 3 + 1) * r)), r) = _
    rw [hpoint]
    rfl
  have hclass := ImplicitNode.classify_eq_nodeAt (q := q) M e w b σ path
  by_cases hdepth : path.length < q
  · have hnode := nodeAt_eq_gate M e w b σ path hdepth
    have htag : ImplicitNode.classify k address = 2 := by
      simpa only [address, hnode, ImplicitNode.kind] using hclass
    by_cases hz : index = 0
    · have hstart : initial M e (address, params) =
          .inl (0, InitialVector.values M e ((2 ^ m) ^ ((k * 3 + 1) * r), m, r)) := by
        change ((if ImplicitNode.classify k address = 2 then
          if index = 0 then .inl (0, InitialVector.values M e
            ((2 ^ m) ^ ((k * 3 + 1) * r), m, r)) else _ else _) : State k Q) = _
        rw [ite_eq_left htag, ite_eq_left hz]
      refine ⟨0, InitialVector.values M e ((2 ^ m) ^ ((k * 3 + 1) * r), m, r), ?_, ?_, ?_⟩
      · change (machine M e).halted (initial M e (address, params)) = true
        rw [hstart]
        rfl
      · change answer (initial M e (address, params)) = _
        rw [hstart]
        rfl
      · intro j
        rw [hnode]
        change _ = Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb)
          (codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
            (Encoding.encode e) (Encoding.decode e) index) x j
        rw [hz]
        exact InitialVector.values_gateExtension_zero M e w _ b
          (scheduleOfNat k q σ) hcapacity hb h hh x j
    · have hle : index ≤ q := ImplicitPath.walk_le k σ q (path.map Fin.val)
      let i : Fin q := ⟨index - 1, by omega⟩
      have hi : i.val + 1 = index := by dsimp only [i]; omega
      obtain ⟨T, values, hrun, hlength, hcanonical, hvalues, hhalt⟩ :=
        GateVector.exists_runFrom_gateExtension M e w b σ i x hb hm hsp h hh
      have hstart : initial M e (address, params) =
          .inr (GateVector.initial
            (QueryGate.gateParams (s := 2 ^ m) (w.length, b, σ, i.val, m, 0, r * m) x, r)) := by
        simp only [initial, htag, show ImplicitPath.walk k address ≠ 0 from hz,
          ↓reduceIte, hprepare, i]
      refine ⟨T, values, ?_, ?_, ?_⟩
      · rw [hstart, runFrom_inr]
        exact hhalt
      · rw [hstart, runFrom_inr, hrun]
        rfl
      · intro j
        rw [hnode]
        rw [hi] at hvalues
        exact hvalues j
  · have htag : ImplicitNode.classify k address ≠ 2 := by
      rw [show address = (σ, q, path.map Fin.val) from rfl, hclass]
      rw [encodedTree, tree, Descending.nodeAt_tree]
      simp only [Descending.lookup, hdepth, ↓reduceIte]
      split <;> simp [ImplicitNode.kind]
    have hstart : initial M e (address, params) = .inl (0, []) := by
      change ((if ImplicitNode.classify k address = 2 then _ else .inl (0, [])) : State k Q) = _
      rw [ite_eq_right htag]
    refine ⟨0, [], ?_, ?_, ?_⟩
    · change (machine M e).halted (initial M e (address, params)) = true
      rw [hstart]
      rfl
    · change answer (initial M e (address, params)) = _
      rw [hstart]
      rfl
    · intro j
      rw [encodedTree, tree, Descending.nodeAt_tree]
      simp only [Descending.lookup, hdepth, ↓reduceIte]
      by_cases heq : path.length = q <;> simp [heq]

/-- The actual modulus-padded register representation discharges normalization internally. -/
theorem exists_runFrom_nodeAt_padded {k q s p r m : ℕ} {Q : Type} [Finite Q] [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (path : List (Fin (k * 3 + 1)))
    (x : Fin (k * 3 + 1) → Fin r → ZMod p)
    (hcapacity : r ≤ ((2 ^ m) ^ ((k * 3 + 1) * r)).size)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (hsp : 2 ^ m ≤ p)
    (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p)) :
    let point := List.ofFn (fun a : Fin ((k * 3 + 1) * r) => p + (blocksEquiv.symm x a).val)
    let params : GateVector.Params := (((w.length, b, 0, 0, m, 0, r * m),
      (p, 2 ^ m, (k * 3 + 1) * r), point, (2 ^ m) ^ ((k * 3 + 1) * r)), r)
    let args : Args := ((σ, q, path.map Fin.val), params)
    ∃ T values, (machine M e).halted ((machine M e).runFrom w (initial M e args) T) = true ∧
      answer ((machine M e).runFrom w (initial M e args) T) = (0, values) ∧
      ∀ j : Fin r, (values.getD j.val 0 : ZMod p) =
        match (encodedTree (MultiTapePTM.ofDeterministic M) w b
          (scheduleOfNat k q σ) e).nodeAt path with
        | .gate f => Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb) f x j
        | _ => 0 := by
  exact exists_runFrom_nodeAt M e w b σ path x _
    (NormalizePoint.normalize_ofFn (Fact.out : p.Prime).pos (blocksEquiv.symm x))
    hcapacity hb hm hsp h hh

end Turing.MultiTapePTM.BlockComputation.QueryReplay.GateReply

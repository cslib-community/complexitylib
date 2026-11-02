/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateReplyCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateVectorBounds
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Physical space of routed implicit gate replies

Every physical clock of the addressed gate reply is charged, including all native interpolation
and replay clocks. The prepared point and metadata occur only a constant number of times; only
the binary field-element width is multiplied by the number of output coordinates. Immediate
source replies use the same field-width allowance, without a gate-supplier premise.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.GateReply

open MultiTapeTM Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed
open Cslib.BitString

/-- Uniform reply allowance, using the largest requested chunk's binary metadata. -/
@[expose] noncomputable def allowance (k s : ℕ) (Q : Type) (args : Args) : ℕ :=
  let params := prepare k args
  let (gateParams, count) := params
  let maxParams := GateVector.setChunk gateParams count
  let (context, _, _, _) := maxParams
  2 * GateVector.callerSpace params +
    16 * ((QueryGate.encParams Interpolation.encContext maxParams).length + 1) +
      Interpolation.calleeSpace k s Q context + 5

private theorem source_encoding_le {k s p r m : ℕ} {Q : Type} [Finite Q]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (limit b : ℕ) [NeZero b]
    (hcapacity : r ≤ limit.size) (hb : Encoding.width k s b ≤ r * m)
    (hsp : 2 ^ m ≤ p) :
    (encState (.inl (0, InitialVector.values M e (limit, m, r)) : State k Q)).length ≤
      r * (2 * (encNat p).length + 1) + 4 := by
  rw [InitialVector.values_eq_packBits M e limit b hcapacity hb]
  have hlist := length_encList_le encNat
    (List.ofFn fun j : Fin r => (Packed.packBits hb
      (Encoding.encode e (some (initialView (MultiTapePTM.ofDeterministic M) b))) j).val)
    (b := (encNat p).length) (by
      intro value hvalue
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hvalue
      exact length_encNat_mono ((Fin.isLt _).trans_le hsp).le)
  simp only [List.length_ofFn] at hlist
  simp only [encState, encSum_inl, List.length_cons, RawController.encReply, length_encPair]
  have hzero : (encNat 0).length = 0 := rfl
  omega

/-- Any explicitly stored point reducing to the canonical typed point gives the existing tree's
requested gate update. The only hypotheses on storage concern its actual representation. -/
theorem exists_runFrom_nodeAt_bounded {k q s p r m : ℕ} {Q : Type} [Finite Q] [Fact p.Prime]
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
      (∀ j : Fin r, (values.getD j.val 0 : ZMod p) =
        match (encodedTree (MultiTapePTM.ofDeterministic M) w b
          (scheduleOfNat k q σ) e).nodeAt path with
        | .gate f => Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb) f x j
        | _ => 0) ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial M e args) t)).length ≤
        allowance k s Q args := by
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
      refine ⟨0, InitialVector.values M e ((2 ^ m) ^ ((k * 3 + 1) * r), m, r),
        ?_, ?_, ?_, ?_⟩
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
      · intro t ht
        have htzero : t = 0 := by omega
        subst t
        have hsource := source_encoding_le M e ((2 ^ m) ^ ((k * 3 + 1) * r)) b
          hcapacity hb hsp
        change (encState ((machine M e).runFrom w (initial M e (address, params)) 0)).length ≤ _
        rw [QueryMachine.runFrom_zero, hstart]
        rw [allowance, hprepare]
        dsimp only [GateVector.callerSpace, QueryGate.gateParams]
        omega
    · have hle : index ≤ q := ImplicitPath.walk_le k σ q (path.map Fin.val)
      let i : Fin q := ⟨index - 1, by omega⟩
      have hi : i.val + 1 = index := by dsimp only [i]; omega
      obtain ⟨T, values, hrun, hlength, hcanonical, hvalues, hhalt, hsize⟩ :=
        GateVector.exists_runFrom_gateExtension_bounded M e w b σ i x hb hm hsp h hh
      have hstart : initial M e (address, params) =
          .inr (GateVector.initial
            (QueryGate.gateParams (s := 2 ^ m) (w.length, b, σ, i.val, m, 0, r * m) x, r)) := by
        simp only [initial, htag, show ImplicitPath.walk k address ≠ 0 from hz,
          ↓reduceIte, hprepare, i]
      refine ⟨T, values, ?_, ?_, ?_, ?_⟩
      · rw [hstart, runFrom_inr]
        exact hhalt
      · rw [hstart, runFrom_inr, hrun]
        rfl
      · intro j
        rw [hnode]
        rw [hi] at hvalues
        exact hvalues j
      · intro t ht
        change (encState ((machine M e).runFrom w (initial M e (address, params)) t)).length ≤ _
        rw [hstart, runFrom_inr]
        have hlocal := hsize t ht
        change (GateVector.encState ((GateVector.machine M e).runFrom w
          (GateVector.initial (QueryGate.gateParams (s := 2 ^ m)
            (w.length, b, σ, i.val, m, 0, r * m) x, r)) t)).length + 1 ≤ _
        rw [allowance, hprepare]
        dsimp only [i] at hlocal ⊢
        simp only [GateVector.setChunk_gateParams]
        dsimp only [QueryGate.gateParams] at hlocal ⊢
        omega
  · have htag : ImplicitNode.classify k address ≠ 2 := by
      rw [show address = (σ, q, path.map Fin.val) from rfl, hclass]
      rw [encodedTree, tree, Descending.nodeAt_tree]
      simp only [Descending.lookup, hdepth, ↓reduceIte]
      split <;> simp [ImplicitNode.kind]
    have hstart : initial M e (address, params) = .inl (0, []) := by
      change ((if ImplicitNode.classify k address = 2 then _ else .inl (0, [])) : State k Q) = _
      rw [ite_eq_right htag]
    refine ⟨0, [], ?_, ?_, ?_, ?_⟩
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
    · intro t ht
      have htzero : t = 0 := by omega
      subst t
      change (encState ((machine M e).runFrom w (initial M e (address, params)) 0)).length ≤ _
      rw [QueryMachine.runFrom_zero, hstart]
      have hempty : (encState (.inl (0, []) : State k Q)).length = 2 := rfl
      rw [hempty]
      dsimp only [allowance]
      omega

/-- The actual modulus-padded register representation discharges normalization internally. -/
theorem exists_runFrom_nodeAt_padded_bounded {k q s p r m : ℕ} {Q : Type}
    [Finite Q] [Fact p.Prime]
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
      (∀ j : Fin r, (values.getD j.val 0 : ZMod p) =
        match (encodedTree (MultiTapePTM.ofDeterministic M) w b
          (scheduleOfNat k q σ) e).nodeAt path with
        | .gate f => Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb) f x j
        | _ => 0) ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial M e args) t)).length ≤
        allowance k s Q args := by
  exact exists_runFrom_nodeAt_bounded M e w b σ path x _
    (NormalizePoint.normalize_ofFn (Fact.out : p.Prime).pos (blocksEquiv.symm x))
    hcapacity hb hm hsp h hh

end Turing.MultiTapePTM.BlockComputation.QueryReplay.GateReply

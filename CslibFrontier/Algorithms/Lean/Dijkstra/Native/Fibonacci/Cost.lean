/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci.Memory
import CslibFrontier.Algorithms.WordRAM.Dijkstra.Invariant
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode

/-!
# Amortized memory cost of the Fibonacci Dijkstra source

The existing framed potential pays for the actual memory histories, and the existing Dijkstra
operation counts retain the reachable-vertex bound. Dirty initialization is constant because
the original input convention already makes the reserved cells zero. These are memory costs;
the native flat-program proof must additionally charge its real prefix, arithmetic and control.

## Main results

* `run_spec`: original admissibility and distance output, with the sharper reachable-vertex
  memory bound under the unchanged word-size envelope.
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance encodeDist)

private def rate (n : ℕ) : OpKind → ℕ
  | .insert => 43
  | .extractMin => 92 * (Nat.log 2 n + 1)
  | .decreaseKey => 104
  | .inspect => 0
  | .distance => 1
  | .graph => 3

private theorem charge_le_rate {n K V : ℕ} (s : (spec n K V).State)
    (o : (spec n K V).Op) (ho : kind o ≠ .inspect) :
    opCharge n K V s o ≤ rate n (kind o) := by
  cases o with
  | inl o =>
    cases o with
    | isEmpty => exact absurd rfl ho
    | getKey _ => exact absurd rfl ho
    | insert _ _ => exact le_rfl
    | decreaseKey _ _ => exact le_rfl
    | extractMin =>
      have hc : (IndexedMinPQ.dom s.1).card ≤ n :=
        (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
      exact Nat.mul_le_mul_left 92
        (Nat.add_le_add_right (Nat.log_mono_right (b := 2) hc) 1)
  | inr o => rcases o with (_ | _) | (_ | _) <;> exact le_rfl

private theorem budget_le (n m : ℕ) (hn : 0 < n) :
    5 + rateBound (rate n) n m ≤
      400 * (m + min n (m + 1) * (Nat.log 2 n + 1)) := by
  have hL : 1 ≤ Nat.log 2 n + 1 := by omega
  by_cases h : n ≤ m + 1
  · rw [Nat.min_eq_left h]
    apply (Nat.add_le_add_left (min_le_left _ _) 5).trans
    dsimp only [rate]
    have hp : 1 ≤ n * (Nat.log 2 n + 1) := Nat.mul_pos hn hL
    have hl := Nat.mul_le_mul_left n hL
    nlinarith
  · have hmn : m + 1 ≤ n := by omega
    rw [Nat.min_eq_right hmn]
    apply (Nat.add_le_add_left (min_le_right _ _) 5).trans
    dsimp only [rate]
    have hp : 1 ≤ (m + 1) * (Nat.log 2 n + 1) := Nat.mul_pos (by omega) hL
    have hl := Nat.mul_le_mul_left (m + 1) hL
    nlinarith

/-- The actual Fibonacci memory program preserves the original admissibility and output
contract. Its sharper bound includes the five header/allocation queries, and pays the heap's
actual nonzero potential through the existing framed amortized telescope. -/
theorem run_spec (G : ListInstance) {w : ℕ}
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    (Memory.spec w).ValidHistory (Memory.State.init G.encode)
        ((Memory.spec w).clientHistory (Memory.State.init G.encode) run) ∧
      (∀ v : Fin G.n, ((Memory.spec w).clientState (Memory.State.init G.encode) run).mem
        (G.outAddr v) = encodeDist (G.dist G.source v)) ∧
      (Memory.spec w).totalCost Memory.charge (Memory.State.init G.encode)
        ((Memory.spec w).clientHistory (Memory.State.init G.encode) run) ≤
          400 * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1)) := by
  let s₀ := Memory.State.init G.encode
  let f := s₀.frontier
  let K := G.n * G.maxWeight
  let T : Block := ⟨f, G.n⟩
  let base := f + G.n
  let s₁ : Memory.State := ⟨s₀.mem, base + (9 * G.n + 5)⟩
  have hf : (Memory.State.init G.encode).frontier = G.n + 2 * G.m + 4 := by
    simp only [Memory.State.init, G.encode_length]
  have hn : Fits w G.n := hfit.of_le (by nlinarith)
  have hK : Fits w K := hfit.of_le (by dsimp only [K]; nlinarith)
  have hT : Dictionary.Memory.Valid T w G.n (K + 1) :=
    ⟨rfl, hfit.of_le (by dsimp only [K]; nlinarith)⟩
  have hA : (Memory.inputGraph G.n G.m).Valid G.n := ⟨rfl⟩
  have hend : Fits w (base + (9 * G.n + 5)) := by
    apply hfit.of_le
    dsimp only [base, f, s₀]
    rw [hf]
    nlinarith
  let M := framed hn hK base hT hA G.adj
  obtain ⟨hinv, habs⟩ := inv_input G hn hK hT hA hend
  obtain ⟨hvalid, hdist⟩ := dijkstra_correct (K := K) (V := K + 1) G le_rfl (by omega)
  rw [← habs] at hvalid hdist
  obtain ⟨hvE, -, hstate, -⟩ := M.simulates_client (dijkstra G.source) hinv hvalid
  have hcost := (amortized (base := base) hn hK hT hA G.adj).client
    (dijkstra G.source) hinv hvalid
  have hcost' := totalCost_dijkstra_le (K := K) (V := K + 1) G le_rfl (by omega)
    (opCharge G.n K (K + 1)) (rate G.n) charge_le_rate
  rw [← habs] at hcost'
  have hz : ZeroAbove s₀ := zeroAbove_init _
  have hp : (FibonacciHeap.potential G.n ((FibonacciHeap.layout G.n base).abs s₁) + 0) +
      (0 + 0) = 0 := by
    change 24 * (s₀.mem (base + 9 * G.n + 2) +
      2 * s₀.mem (base + 9 * G.n + 3)) + 0 + (0 + 0) = 0
    rw [hz _ (by dsimp only [base, f]; omega), hz _ (by dsimp only [base, f]; omega)]
  rw [hp] at hcost
  have hprog : link (methods G.n 0 0 0 base T (Memory.inputGraph G.n G.m))
      (dijkstra (K := 0) (V := 0) G.source) = link M.methods
        (dijkstra (K := K) (V := K + 1) G.source) := by
    rw [show M.methods = methods G.n K (K + 1) w base T (Memory.inputGraph G.n G.m) from rfl,
      Memory.dijkstra_eq K (K + 1) 0 0, methods_eq G.n K (K + 1) w 0 0 0]
    rfl
  have hclient : Triple w s₁ (link (methods G.n 0 0 0 base T (Memory.inputGraph G.n G.m))
      (dijkstra (K := 0) (V := 0) G.source)) (rateBound (rate G.n) G.n G.m)
      (fun _ s' => ∀ v : Fin G.n, s'.mem (G.outAddr v) = encodeDist (G.dist G.source v)) := by
    rw [hprog]
    refine triple_iff.mpr ⟨hvE, ?_, fun v => ?_⟩
    · simp only [Nat.add_zero] at hcost
      exact (Nat.le_add_right _ _).trans (hcost.trans hcost')
    · obtain ⟨dist, hds, hdv⟩ := hdist
      rw [← hstate] at hds
      have hcell := congrArg (fun x => x.2.1 v) hds
      change Dictionary.Memory.decode
        (((Memory.spec w).clientState s₁ (link M.methods (dijkstra G.source))).mem
          (f + v)) = dist v at hcell
      have ha : G.outAddr v = f + v := by
        dsimp only [ListInstance.outAddr, f, s₀]
        rw [hf]
      rw [ha]
      change _ = encodeDist (G.dist G.source v)
      generalize hword : ((Memory.spec w).clientState s₁
        (link M.methods (dijkstra G.source))).mem (f + v) = value at hcell ⊢
      cases value with
      | zero =>
        have hD : G.dist G.source v = ⊤ := by
          by_contra hD
          obtain ⟨d, he⟩ := ENat.ne_top_iff_exists.mp hD
          have hd := (hdv v d).mpr he.symm
          rw [← hcell] at hd
          cases hd
        simp [hD, encodeDist]
      | succ x =>
        have hd : G.dist G.source v = x := (hdv v x).mp hcell.symm
        simp [hd, encodeDist]
  have htriple : Triple w s₀ run (rateBound (rate G.n) G.n G.m + 5)
      (fun _ s' => ∀ v : Fin G.n, s'.mem (G.outAddr v) = encodeDist (G.dist G.source v)) := by
    have hn1 : s₀.mem 1 = G.n := rfl
    have hsrc : s₀.mem 2 = G.source := rfl
    have hm : s₀.mem (G.n + 3) = G.m := by
      rw [← G.offset_n]
      exact G.init_offset (r := 0) le_rfl
    unfold run
    refine Triple.read_bind (by dsimp only [s₀]; rw [hf]; omega) <|
      Triple.read_bind (by dsimp only [s₀]; rw [hf]; omega) ?_
    rw [hn1, hsrc]
    refine Triple.read_bind (by dsimp only [s₀]; rw [hf]; omega) ?_
    rw [hm]
    refine Triple.allocBlockDirty_bind (hfit.of_le (by dsimp only [s₀]; rw [hf]; nlinarith)) ?_
    rw [triple_iff] at hclient ⊢
    simp only [dite_eq_left G.source.isLt]
    exact ⟨⟨hend, hclient.1⟩,
      (Nat.add_le_add_left hclient.2.1 1).trans_eq (Nat.add_comm 1 _), hclient.2.2⟩
  obtain ⟨hv, hc, hd⟩ := triple_iff.mp htriple
  exact ⟨hv, hd, hc.trans (by
    have h := budget_le G.n G.m (by have := G.source.isLt; omega)
    omega)⟩

end Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci

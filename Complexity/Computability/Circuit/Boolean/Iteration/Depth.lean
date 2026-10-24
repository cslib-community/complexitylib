/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Scan
public import Complexity.Computability.Circuit.Boolean.Iteration.Optimization
public import Complexity.Computability.Circuit.Boolean.Iteration.SharedDictionary
public import Complexity.Foundations.Combinatorics.FunctionalGraph.Projection
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Circuits for transient depths

Let `c` be a circuit of size `s` computing `f` on `n`-bit states. Some circuit of size at most
`50000 * powerBudget n s (2 ^ n) L` computes the transient depth of every state, in `n + 2` bits
(`checkpoint_depth_circuit`), for every `0 < L ≤ 2 ^ n`; with the balanced parameter the size is
at most `150000 * optimizedBudget n s (2 ^ n)` (`checkpoint_depth_optimized`).

The construction compares the first `2 L + 1` states of the orbit of `x` with those of its cycle
projection `f^[(2 ^ n)!] x`, computed by a fixed-power circuit. The two orbits agree exactly from
the transient depth on (`FunctionalGraph.iterate_eq_projection_iff`). If they agree at the end of
the prefix, the first agreement is the depth (`shortDepth_eq`). Otherwise the transient is long,
so the prefix cannot repeat and meets a checkpoint, all of whose prefix states are transient: the
depth is the hardwired depth of the checkpoint plus its time in the prefix. One shared dictionary
answers all prefix states.

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. The checkpoints are chosen nonconstructively, so the
circuits exist for each `L`; nothing here bounds the time to construct them.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.shortDepth`: the first agreement with the projected orbit.
* `Cslib.Circuits.Boolean.Iteration.depthCost`: the gate count of the checkpoint construction.

## Main results

* `Cslib.Circuits.Boolean.Iteration.depth_from_checkpoints`: depths from given checkpoints.
* `Cslib.Circuits.Boolean.Iteration.checkpoint_depth_circuit`,
  `Cslib.Circuits.Boolean.Iteration.checkpoint_depth_optimized`: transient depths.

## References

* Adapted from lean/Proofs/CheckpointDepth.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions], whose
  bounds have the constants `1000000` and `3000000`. The dictionary here is the library's
  `batchOrCircuit` lookup.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n M : ℕ}

/-- The first time up to `K` at which the orbit of `x` agrees with the orbit of its cycle
projection, in `n + 2` bits. -/
def shortDepth (f : BitString n → BitString n) (K : ℕ) (x : BitString n) :
    BitVec (n + 2) :=
  firstIndex fun j : Fin (K + 1) => decide (f^[j.val] x = f^[j.val] (cycleProjection f x))

/-- A transient of length at most `K` is found by the first agreement. -/
theorem shortDepth_eq (f : BitString n → BitString n) (K : ℕ) (x : BitString n)
    (hK : transientDepth f x ≤ K) :
    shortDepth f K x = BitVec.ofNat (n + 2) (transientDepth f x) :=
  firstIndex_spec _ ⟨transientDepth f x, by omega⟩
    (decide_eq_true ((iterate_eq_projection_iff f x _).mpr le_rfl))
    fun i hi => decide_eq_false fun he => absurd ((iterate_eq_projection_iff f x i.val).mp he)
      (not_le.mpr hi)

/-- The gate count of the depth construction from `M` checkpoints with parameter `L`: constants,
the projection, both orbit prefixes, the shared dictionary, and per prefix state an equality
test, an addition and two selection steps, then the final selection. -/
def depthCost (n s M L : ℕ) : ℕ :=
  2 + 40000 * powerBudget n s (2 ^ n) L + 4 * L * s +
    48 * ((2 * L + 1) + M + 1) * (Nat.clog 2 ((2 * L + 1) + M) + 1) ^ 2 * (n + (n + 3) + 1) +
    (2 * L + 1) * (26 * n + 42) + 4 * (n + 2)

/-- **Depths from checkpoints.** Let `cp` be injective checkpoints such that every orbit repeats
among its first `L` states or reaches a checkpoint in fewer than `2 L` steps. Then some circuit of
size at most `depthCost n c.size M L` computes the transient depth of every state in `n + 2`
bits. -/
theorem depth_from_checkpoints (c : Circuit signature n n) (L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) (cp : Fin M → BitString n) (hcp : Function.Injective cp)
    (hcover : ∀ x, Repeats (c.eval interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval interpretation)^[t] x = cp j) :
    ∃ out : Circuit signature n (n + 2),
      (∀ x, word (out.eval interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval interpretation) x)) ∧
      out.size ≤ depthCost n c.size M L := by
  let f := c.eval interpretation
  let K := 2 * L
  let W := n + 2
  let constants : Set (BooleanFunction n) := {fun _ => false, fun _ => true}
  have hconst : Synthesis interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let s0 := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : BitString n => b) ∈ s0 := by cases b <;> simp [s0, constants]
  obtain ⟨project, hp, hps⟩ := fixed_power n c (Fintype.card (BitString n)).factorial L hL hLN
  have hproject : Synthesis interpretation s0 (wires (cycleProjection f)) project.size := by
    refine (Synthesis.circuit (I := interpretation) (s := s0) project (fun i x => x i)
      fun bit => Or.inl ⟨bit, rfl⟩).mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨bit, rfl⟩
    exact ⟨bit, funext fun x => by
      change project.eval interpretation x bit = _
      rw [hp x]
      rfl⟩
  let s1 := s0 ∪ wires (cycleProjection f)
  have hx := Synthesis.orbit (I := interpretation) (s := s1) c id
    (fun bit => Or.inl (Or.inl ⟨bit, rfl⟩)) K
  have hz := Synthesis.orbit (I := interpretation) (s := s1) c (cycleProjection f)
    (fun bit => Or.inr ⟨bit, rfl⟩) K
  let s2 := s1 ∪ (Synthesis.stages (fun j => wires fun x => f^[j] x) K ∪
    Synthesis.stages (fun j => wires fun x => f^[j] (cycleProjection f x)) K)
  have htrace (j : Fin (K + 1)) : wires (fun x => f^[j.val] x) ⊆ s2 := fun _ h =>
    Or.inr (Or.inl (Synthesis.subset_stages _ (Nat.le_of_lt_succ j.isLt) h))
  have hprojected (j : Fin (K + 1)) : wires (fun x => f^[j.val] (cycleProjection f x)) ⊆ s2 :=
    fun _ h => Or.inr (Or.inr (Synthesis.subset_stages _ (Nat.le_of_lt_succ j.isLt) h))
  let depthBits := fun y : BitString n => fun bit : Fin W =>
    (BitVec.ofNat W (transientDepth f y)).getLsbD bit.val
  let stored : Fin M → BitString (W + 1) := fun i => Fin.cons true (depthBits (cp i))
  let queries : BitString n → Fin (K + 1) → BitString n := fun x j => f^[j.val] x
  have hdict := synthesis_lookupOr s2 cp stored queries fun j bit => htrace j ⟨bit, rfl⟩
  let result := fun x (j : Fin (K + 1)) => lookupOr cp stored (queries x j)
  let equal := fun x (j : Fin (K + 1)) => decide (f^[j.val] x = f^[j.val] (cycleProjection f x))
  have heq := Synthesis.family (I := interpretation) (s := s2) (fun j x => equal x j)
    (fun _ => 6 * n + 1) fun j =>
      synthesis_bits_eq s2 (fun x => f^[j.val] x) _ (htrace j) (hprojected j)
  let s3 := s2 ∪ ((⋃ j, wires fun x => result x j) ∪ Set.range fun j x => equal x j)
  have hresult (j : Fin (K + 1)) (bit : Fin (W + 1)) : (fun x => result x j bit) ∈ s3 :=
    Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨j, bit, rfl⟩))
  have hequal (j : Fin (K + 1)) : (fun x => equal x j) ∈ s3 := Or.inr (Or.inr ⟨j, rfl⟩)
  have hc3 (b : Bool) : (fun _ : BitString n => b) ∈ s3 := Or.inl (Or.inl (Or.inl (hc b)))
  let flags := fun x (j : Fin (K + 1)) => result x j 0
  let corrected := fun (j : Fin (K + 1)) x =>
    word (fun bit : Fin W => result x j bit.succ) + BitVec.ofNat W j.val
  have hcorrect := Synthesis.iUnion (fun j => wordWires (corrected j)) (fun _ => 12 * W + 1)
    fun j => Synthesis.word_add (s := s3) (fun x => word fun bit : Fin W => result x j bit.succ)
      (fun _ => BitVec.ofNat W j.val)
      (fun bit => by simpa only [getLsbD_word] using hresult j bit.succ) fun _ => hc3 _
  let s4 := s3 ∪ ⋃ j, wordWires (corrected j)
  let selected := fun x => word (chooseRecord (flags x)
    (fun j (bit : Fin W) => (corrected j x).getLsbD bit.val) (fun _ => false) (K + 1))
  have hselected : Synthesis interpretation s4 (wordWires selected) ((K + 1) * (4 * W)) := by
    simpa only [selected, wordWires, getLsbD_word] using synthesis_chooseRecord s4 flags
      (fun x j bit => (corrected j x).getLsbD bit.val) (fun _ _ => false)
      (fun j => Or.inl (hresult j 0)) (fun j bit => Or.inr (Set.mem_iUnion.mpr ⟨j, bit, rfl⟩))
      fun _ => Or.inl (hc3 false)
  have hshort := synthesis_firstIndex (w := W) s4 equal (fun j => Or.inl (hequal j))
    fun b => Or.inl (hc3 b)
  let s5 := s4 ∪ (wordWires selected ∪ wordWires fun x => firstIndex (w := W) (equal x))
  let last : Fin (K + 1) := ⟨K, Nat.lt_succ_self K⟩
  have hfinal := Synthesis.word_mux (s := s5) (fun x => firstIndex (w := W) (equal x)) selected
    (fun x => equal x last) (Or.inl (Or.inl (hequal last)))
    (fun bit => Or.inr (Or.inr ⟨bit, rfl⟩)) fun bit => Or.inr (Or.inl ⟨bit, rfl⟩)
  have h := hconst.trans (hproject.trans ((hx.union hz).trans ((hdict.union heq).trans
    (hcorrect.trans ((hselected.union hshort).trans hfinal)))))
  obtain ⟨out, ho, hs⟩ := h.exists_circuit_outputs
  refine ⟨out, fun x => ?_, hs.trans ?_⟩
  · rw [ho x, word_getLsbD]
    by_cases hK : transientDepth f x ≤ K
    · have he : equal x last = true := decide_eq_true ((iterate_eq_projection_iff f x K).mpr hK)
      simp only [he, ite_true]
      exact shortDepth_eq f K x hK
    · have he : equal x last = false :=
        decide_eq_false fun hh => hK ((iterate_eq_projection_iff f x K).mp hh)
      simp only [he, Bool.false_eq_true, ite_false]
      have hex : ∃ j : Fin (K + 1), j.val < K + 1 ∧ flags x j = true := by
        rcases hcover x with ⟨i, j, hij, hj, hrep⟩ | ⟨t, ht, i, hi⟩
        · have := transientDepth_add_cycleLength_le_of_iterate_eq f x hij hrep
          omega
        · refine ⟨⟨t, by omega⟩, by simp only; omega, ?_⟩
          exact decide_eq_true ⟨i, hi.symm, rfl⟩
      obtain ⟨j, -, hj, hchosen⟩ := chooseRecord_spec (flags x)
        (fun j (bit : Fin W) => (corrected j x).getLsbD bit.val) (fun _ => false) (K + 1) hex
      change word (chooseRecord _ _ _ _) = _
      rw [hchosen, word_getLsbD]
      obtain ⟨i, hi, -⟩ := (decide_eq_true_iff.mp hj : ∃ i, cp i = _ ∧ stored i 0 = true)
      have hrecord : (word fun bit : Fin W => result x j bit.succ) =
          BitVec.ofNat W (transientDepth f (f^[j.val] x)) := by
        rw [← word_getLsbD (BitVec.ofNat W _)]
        congr 1
        funext bit
        change lookupOr cp stored _ bit.succ = _
        rw [lookupOr_of_eq stored hcp hi]
        simp only [stored, depthBits, Fin.cons_succ, hi]
        rfl
      have hjμ : j.val ≤ transientDepth f x := by have := j.isLt; omega
      change word (fun bit : Fin W => result x j bit.succ) + BitVec.ofNat W j.val = _
      rw [hrecord, transientDepth_iterate, ← BitVec.ofNat_add, Nat.sub_add_cancel hjμ]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs ⊢
    have hps' : project.size ≤ 40000 * powerBudget n c.size (2 ^ n) L := by simpa using hps
    unfold depthCost
    simp only [K, W] at hs ⊢
    nlinarith

/-- The depth construction is within `50000` times the fixed-power tradeoff. -/
private theorem depthCost_le (n s M L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hM : M ≤ 2 ^ n / L) :
    depthCost n s M L ≤ 50000 * powerBudget n s (2 ^ n) L := by
  unfold depthCost powerBudget
  set N := 2 ^ n with hNdef
  set d := Nat.clog 2 ((2 * L + 1) + M)
  set P := (n + 1) ^ 3
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hMN : M ≤ N := hM.trans (Nat.div_le_self _ _)
  have hd : d ≤ n + 2 := by
    apply Nat.clog_le_of_le_pow
    have h4 : 2 ^ (n + 2) = 4 * N := by rw [hNdef, pow_add]; ring
    omega
  have hn1 : n + 1 ≤ P := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < n + 1 by omega) (by decide : 1 ≤ 3)
  have hdict : 48 * ((2 * L + 1) + M + 1) * (d + 1) ^ 2 * (n + (n + 3) + 1) ≤
      6912 * P * (L + N / L + 1) := by
    have h1 : (d + 1) ^ 2 ≤ 9 * (n + 1) ^ 2 := by
      have := Nat.pow_le_pow_left (show d + 1 ≤ 3 * (n + 1) by omega) 2
      nlinarith
    calc 48 * ((2 * L + 1) + M + 1) * (d + 1) ^ 2 * (n + (n + 3) + 1)
        ≤ 48 * (4 * (L + N / L + 1)) * (9 * (n + 1) ^ 2) * (4 * (n + 1)) := by
          gcongr <;> omega
      _ = 6912 * P * (L + N / L + 1) := by simp only [P]; ring
  have hscan : (2 * L + 1) * (26 * n + 42) + 4 * (n + 2) + 2 ≤ 200 * (P * (L + N / L + 1)) := by
    have e1 : (2 * L + 1) * (26 * n + 42) ≤ 3 * L * (42 * P) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hLP : L * P ≤ P * (L + N / L + 1) := by nlinarith
    nlinarith
  nlinarith [Nat.zero_le (L * s)]

/-- **Transient depths.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`50000 * powerBudget n c.size (2 ^ n) L` computes the transient depth of every state in `n + 2`
bits. -/
theorem checkpoint_depth_circuit (c : Circuit signature n n) (L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n (n + 2),
      (∀ x, word (out.eval interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval interpretation) x)) ∧
      out.size ≤ 50000 * powerBudget n c.size (2 ^ n) L := by
  classical
  obtain ⟨H, hcard, hcover⟩ := exists_checkpoints_finite (c.eval interpretation) hL
  let cp : Fin H.card → BitString n := fun j => (H.equivFin.symm j).val
  have hcp : Function.Injective cp := fun _ _ h => H.equivFin.symm.injective (Subtype.ext h)
  have hcov (x : BitString n) : Repeats (c.eval interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval interpretation)^[t] x = cp j := by
    rcases hcover x with hr | ⟨t, ht, hm⟩
    · exact Or.inl hr
    · exact Or.inr ⟨t, ht, H.equivFin ⟨_, hm⟩, by simp [cp]⟩
  obtain ⟨out, ho, hs⟩ := depth_from_checkpoints c L hL hLN cp hcp hcov
  exact ⟨out, ho, hs.trans (depthCost_le _ _ _ _ hL hLN (by simpa using hcard))⟩

/-- **Square-root transient depths.** Some circuit of size at most
`150000 * optimizedBudget n c.size (2 ^ n)` computes the transient depth of every state in
`n + 2` bits. -/
theorem checkpoint_depth_optimized (c : Circuit signature n n) :
    ∃ out : Circuit signature n (n + 2),
      (∀ x, word (out.eval interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval interpretation) x)) ∧
      (out.size : ℝ) ≤ 150000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := checkpoint_depth_circuit c L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤ 50000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
    exact_mod_cast hs
  linarith

end Cslib.Circuits.Boolean.Iteration

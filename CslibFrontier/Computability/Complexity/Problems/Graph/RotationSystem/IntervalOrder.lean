/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Linear ranks and literal directed rotation intervals

Cutting a finite vertex cycle at any one of its darts gives first-hit ranks. These ranks
retain the direction of the supplied rotation, without a geometric realization or any
restriction on the graph's loops or components.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

variable {G : Graph} (r : RotationSystem G)

/-- First-hit distance is bounded by any successful forward iterate. -/
theorem rotationDistance_le {a b : Dart G} (hab : a.vertex = b.vertex) {n : ℕ}
    (hn : (r.rotate ^ n) a = b) : r.rotationDistance a b ≤ n := by
  classical
  rw [rotationDistance, dite_eq_left ((r.sameCycle_iff a b).mpr hab)]
  exact Nat.find_min' _ hn

private theorem period_pos (a : Dart G) : 0 < Function.minimalPeriod r.rotate a :=
  Function.minimalPeriod_pos_of_mem_periodicPts (r.rotate.injective.mem_periodicPts a)

/-- First-hit ranks fit in one complete vertex cycle, including singleton cycles. -/
theorem rotationDistance_lt_period {a b : Dart G} (hab : a.vertex = b.vertex) :
    r.rotationDistance a b < Function.minimalPeriod r.rotate a := by
  have hm : (r.rotate ^ (r.rotationDistance a b % Function.minimalPeriod r.rotate a)) a = b := by
    rw [← r.rotate.iterate_eq_pow, Function.iterate_mod_minimalPeriod_eq,
      r.rotate.iterate_eq_pow]
    exact r.pow_rotationDistance a b hab
  exact (r.rotationDistance_le hab hm).trans_lt (Nat.mod_lt _ (r.period_pos a))

private theorem pow_eq_iff_rank_eq (o a b : Dart G) (hoa : o.vertex = a.vertex)
    (hob : o.vertex = b.vertex) :
    r.rotationDistance o a = r.rotationDistance o b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => congrArg _ h⟩
  rw [← r.pow_rotationDistance o a hoa, ← r.pow_rotationDistance o b hob, h]

/-- The rank of a forward iterate is its exponent reduced modulo the vertex period. -/
theorem rotationDistance_pow (o : Dart G) (k : ℕ) :
    r.rotationDistance o ((r.rotate ^ k) o) = k % Function.minimalPeriod r.rotate o := by
  have hv : o.vertex = ((r.rotate ^ k) o).vertex :=
    (r.sameCycle_iff _ _).mp (Equiv.Perm.sameCycle_pow_right.mpr .rfl)
  apply r.rotationDistance_eq _ _ hv
  · rw [← r.rotate.iterate_eq_pow, Function.iterate_mod_minimalPeriod_eq,
      r.rotate.iterate_eq_pow]
  · intro j hj heq
    have heq' : (r.rotate ^ j) o =
        (r.rotate ^ (k % Function.minimalPeriod r.rotate o)) o := by
      have hmod := Function.iterate_mod_minimalPeriod_eq (f := r.rotate) (x := o) (n := k)
      rw [r.rotate.iterate_eq_pow, r.rotate.iterate_eq_pow] at hmod
      exact heq.trans hmod.symm
    have h := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (hj.trans (Nat.mod_lt _ (r.period_pos o))) (Nat.mod_lt _ (r.period_pos o))).mp
        (show (r.rotate : Dart G → Dart G)^[j] o =
          (r.rotate : Dart G → Dart G)^[k % Function.minimalPeriod r.rotate o] o by
          simpa only [r.rotate.iterate_eq_pow] using heq')
    omega

/-- Forward rotation adds to a rank modulo the same vertex period. -/
theorem rotationDistance_pow_from (o a : Dart G) (hoa : o.vertex = a.vertex) (k : ℕ) :
    r.rotationDistance o ((r.rotate ^ k) a) =
      (r.rotationDistance o a + k) % Function.minimalPeriod r.rotate o := by
  calc
    _ = r.rotationDistance o ((r.rotate ^ (r.rotationDistance o a + k)) o) := by
      rw [Nat.add_comm (r.rotationDistance o a) k, pow_add, Equiv.Perm.mul_apply,
        r.pow_rotationDistance o a hoa]
    _ = _ := r.rotationDistance_pow _ _

private theorem period_eq (o a : Dart G) (hoa : o.vertex = a.vertex) :
    Function.minimalPeriod r.rotate a = Function.minimalPeriod r.rotate o := by
  have h := Function.minimalPeriod_apply_iterate (r.rotate.injective.mem_periodicPts o)
    (r.rotationDistance o a)
  simpa only [r.rotate.iterate_eq_pow, r.pow_rotationDistance o a hoa] using h

private theorem add_mod_eq_iff {a b c n : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) :
    (a + b) % n = c ↔ a + b = c ∨ a + b = c + n := by
  by_cases h : a + b < n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The actual directed rotation interval is the cyclic order of first-hit ranks at
any chosen cut. All three darts must be distinct and belong to that vertex cycle. -/
theorem mem_rotationInterval_iff_ranks (o a b c : Dart G)
    (hoa : o.vertex = a.vertex) (hob : o.vertex = b.vertex) (hoc : o.vertex = c.vertex)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔
      (r.rotationDistance o a < r.rotationDistance o b ∧
        r.rotationDistance o b < r.rotationDistance o c) ∨
      (r.rotationDistance o b < r.rotationDistance o c ∧
        r.rotationDistance o c < r.rotationDistance o a) ∨
      (r.rotationDistance o c < r.rotationDistance o a ∧
        r.rotationDistance o a < r.rotationDistance o b) := by
  classical
  let n := Function.minimalPeriod r.rotate o
  let ra := r.rotationDistance o a
  let rb := r.rotationDistance o b
  let rc := r.rotationDistance o c
  let dist := r.rotationDistance a c
  have ha : ra < n := r.rotationDistance_lt_period hoa
  have hb : rb < n := r.rotationDistance_lt_period hob
  have hc : rc < n := r.rotationDistance_lt_period hoc
  have hd : dist < n := by
    have h := r.rotationDistance_lt_period (hoa.symm.trans hoc)
    rwa [r.period_eq o a hoa] at h
  have hneab : ra ≠ rb := fun h => hab ((r.pow_eq_iff_rank_eq o a b hoa hob).mp h)
  have hnebc : rb ≠ rc := fun h => hbc ((r.pow_eq_iff_rank_eq o b c hob hoc).mp h)
  have hneac : ra ≠ rc := fun h => hac ((r.pow_eq_iff_rank_eq o a c hoa hoc).mp h)
  have hdist : ra + dist = rc ∨ ra + dist = rc + n := by
    apply (add_mod_eq_iff ha hd hc).mp
    have h := r.rotationDistance_pow_from o a hoa dist
    rw [r.pow_rotationDistance a c (hoa.symm.trans hoc)] at h
    exact h.symm
  have pow_iff (k : ℕ) : (r.rotate ^ k) a = b ↔ (ra + k) % n = rb := by
    have hv : o.vertex = ((r.rotate ^ k) a).vertex :=
      hoa.trans ((r.sameCycle_iff _ _).mp
        (Equiv.Perm.sameCycle_pow_right.mpr .rfl))
    rw [← r.pow_eq_iff_rank_eq o _ b hv hob, r.rotationDistance_pow_from o a hoa]
  constructor
  · intro hmem
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hmem
    have hk' : k < dist := Finset.mem_range.mp hk
    have hsum := (add_mod_eq_iff ha (show k + 1 < n by omega) hb).mp
      ((pow_iff (k + 1)).mp heq)
    change (ra < rb ∧ rb < rc) ∨ (rb < rc ∧ rc < ra) ∨ (rc < ra ∧ ra < rb)
    omega
  · intro horder
    change (ra < rb ∧ rb < rc) ∨ (rb < rc ∧ rc < ra) ∨ (rc < ra ∧ ra < rb) at horder
    by_cases hlt : ra < rb
    · have hpos : 0 < rb - ra := by omega
      have hle : rb - ra ≤ dist := by omega
      apply Finset.mem_image.mpr
      refine ⟨rb - ra - 1, Finset.mem_range.mpr (by omega), ?_⟩
      apply (pow_iff _).mpr
      rw [show rb - ra - 1 + 1 = rb - ra by omega]
      apply (add_mod_eq_iff ha (by omega) hb).mpr
      exact Or.inl (by omega)
    · have hpos : 0 < rb + n - ra := by omega
      have hle : rb + n - ra ≤ dist := by omega
      apply Finset.mem_image.mpr
      refine ⟨rb + n - ra - 1, Finset.mem_range.mpr (by omega), ?_⟩
      apply (pow_iff _).mpr
      rw [show rb + n - ra - 1 + 1 = rb + n - ra by omega]
      apply (add_mod_eq_iff ha (by omega) hb).mpr
      exact Or.inr (by omega)

private noncomputable def vertexDart (v : ℕ) (h : ∃ d : Dart G, d.vertex = v) : Dart G :=
  Classical.choose h

/-- A zero-based linear rank of an incident dart, cutting each literal vertex cycle at
one classically chosen dart. Different indexed ends, including loop ends, remain distinct. -/
noncomputable def portRank (d : Dart G) : ℕ :=
  r.rotationDistance (vertexDart d.vertex ⟨d, rfl⟩) d

private theorem portRank_at (a d : Dart G) (had : a.vertex = d.vertex) :
    r.portRank d = r.rotationDistance (vertexDart a.vertex ⟨a, rfl⟩) d := by
  simp only [portRank, ← had]

/-- Ranks distinguish every actual dart at a vertex. -/
theorem portRank_injective (a b : Dart G) (hab : a.vertex = b.vertex)
    (heq : r.portRank a = r.portRank b) : a = b := by
  let o := vertexDart a.vertex ⟨a, rfl⟩
  have hoa : o.vertex = a.vertex := Classical.choose_spec (show ∃ d : Dart G,
    d.vertex = a.vertex from ⟨a, rfl⟩)
  rw [r.portRank_at a a rfl, r.portRank_at a b hab] at heq
  exact (r.pow_eq_iff_rank_eq o a b hoa (hoa.trans hab)).mp heq

/-- The chosen linear ranks retain the supplied clockwise cyclic interval. -/
theorem mem_rotationInterval_iff_portRank (a b c : Dart G)
    (hab : a.vertex = b.vertex) (hbc : b.vertex = c.vertex)
    (hneab : a ≠ b) (hnebc : b ≠ c) (hneac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔
      (r.portRank a < r.portRank b ∧ r.portRank b < r.portRank c) ∨
      (r.portRank b < r.portRank c ∧ r.portRank c < r.portRank a) ∨
      (r.portRank c < r.portRank a ∧ r.portRank a < r.portRank b) := by
  let o := vertexDart a.vertex ⟨a, rfl⟩
  have hoa : o.vertex = a.vertex := Classical.choose_spec (show ∃ d : Dart G,
    d.vertex = a.vertex from ⟨a, rfl⟩)
  rw [r.portRank_at a a rfl, r.portRank_at a b hab, r.portRank_at a c (hab.trans hbc)]
  exact r.mem_rotationInterval_iff_ranks o a b c hoa (hoa.trans hab)
    (hoa.trans (hab.trans hbc)) hneab hnebc hneac

/-- A vertex cycle first reaches its starting dart at exponent zero. -/
@[simp] theorem rotationDistance_self (a : Dart G) : r.rotationDistance a a = 0 := by
  apply r.rotationDistance_eq a a rfl 0 rfl
  intro k hk
  omega

/-- A different dart in the same source cycle has positive first-hit rank. -/
theorem rotationDistance_pos_of_ne {G : Graph} (r : RotationSystem G)
    (o a : Dart G) (hoa : o.vertex = a.vertex) (hne : a ≠ o) :
    0 < r.rotationDistance o a := by
  by_contra hn
  have hzero : r.rotationDistance o a = 0 := by omega
  have h := r.pow_rotationDistance o a hoa
  rw [hzero, pow_zero, Equiv.Perm.one_apply] at h
  exact hne h.symm

/-- A forward source step adds one to the first-hit rank until it returns to the
specified cycle cut. -/
theorem rotationDistance_rotate_of_ne {G : Graph} (r : RotationSystem G)
    (o a : Dart G) (hoa : o.vertex = a.vertex) (hne : r.rotate a ≠ o) :
    r.rotationDistance o (r.rotate a) = r.rotationDistance o a + 1 := by
  let n := Function.minimalPeriod r.rotate o
  let k := r.rotationDistance o a
  have hk : k < n := r.rotationDistance_lt_period hoa
  have hiter : (r.rotate ^ (k + 1)) o = r.rotate a := by
    rw [pow_succ', Equiv.Perm.mul_apply, r.pow_rotationDistance o a hoa]
  have hkn : k + 1 < n := by
    by_contra hn
    have heq : k + 1 = n := by omega
    rw [heq] at hiter
    have hperiod : (r.rotate ^ n) o = o := by
      rw [← r.rotate.iterate_eq_pow]
      exact Function.iterate_minimalPeriod (f := r.rotate) (x := o)
    exact hne (hiter.symm.trans hperiod)
  have h := r.rotationDistance_pow_from o a hoa 1
  simp only [pow_one] at h
  change r.rotationDistance o (r.rotate a) = (k + 1) % n at h
  rw [Nat.mod_eq_of_lt hkn] at h
  exact h

/-- The predecessor of a source cycle cut has its last rank, including unary cycles. -/
theorem rotationDistance_of_rotate_eq {G : Graph} (r : RotationSystem G)
    (o a : Dart G) (hoa : o.vertex = a.vertex) (heq : r.rotate a = o) :
    r.rotationDistance o a = Function.minimalPeriod r.rotate o - 1 := by
  let k := r.rotationDistance o a
  have hperiod : Function.IsPeriodicPt r.rotate (k + 1) o := by
    change (r.rotate : Dart G → Dart G)^[k + 1] o = o
    rw [r.rotate.iterate_eq_pow, pow_succ', Equiv.Perm.mul_apply,
      r.pow_rotationDistance o a hoa, heq]
  have hle := hperiod.minimalPeriod_le (Nat.succ_pos k)
  have hlt := r.rotationDistance_lt_period hoa
  change k = _
  omega

/-- The source vertex cycle after omitting its specified dart, in the original forward
order. A unary vertex cycle gives `Fin 0`, without inventing a corner dart. -/
@[expose] noncomputable def sourceTailEquiv {G : Graph} (r : RotationSystem G) (o : Dart G) :
    {d : Dart G // d.vertex = o.vertex ∧ d ≠ o} ≃
      Fin (Function.minimalPeriod r.rotate o - 1) where
  toFun d := ⟨r.rotationDistance o d.val - 1, by
    have hlt := r.rotationDistance_lt_period d.property.1.symm
    have hpos := r.rotationDistance_pos_of_ne o d.val d.property.1.symm d.property.2
    omega⟩
  invFun i := ⟨(r.rotate ^ (i.val + 1)) o, by
    have hv : ((r.rotate ^ (i.val + 1)) o).vertex = o.vertex :=
      (r.sameCycle_iff _ _).mp (Equiv.Perm.sameCycle_pow_left.mpr .rfl)
    refine ⟨hv, ?_⟩
    intro heq
    have hi : i.val + 1 < Function.minimalPeriod r.rotate o := by omega
    have hzero := r.rotationDistance_self o
    have hrank := r.rotationDistance_pow o (i.val + 1)
    rw [heq, Nat.mod_eq_of_lt hi] at hrank
    omega⟩
  left_inv d := by
    apply Subtype.ext
    have hpos := r.rotationDistance_pos_of_ne o d.val d.property.1.symm d.property.2
    change (r.rotate ^ (r.rotationDistance o d.val - 1 + 1)) o = d.val
    rw [Nat.sub_add_cancel hpos, r.pow_rotationDistance o d.val d.property.1.symm]
  right_inv i := by
    apply Fin.ext
    change r.rotationDistance o ((r.rotate ^ (i.val + 1)) o) - 1 = i.val
    rw [r.rotationDistance_pow, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The actual tail enumeration follows the original successor powers, rather than
reusing contracted distances that have changed when the selected darts were removed. -/
theorem sourceTailEquiv_symm_val {G : Graph} (r : RotationSystem G) (o : Dart G)
    (i : Fin (Function.minimalPeriod r.rotate o - 1)) :
    ((r.sourceTailEquiv o).symm i).val = (r.rotate ^ (i.val + 1)) o := rfl

/-- A strict interval based at its rank origin compares the two terminal ranks. -/
theorem mem_rotationInterval_iff_lt_distance (a b c : Dart G)
    (hab : a.vertex = b.vertex) (hac : a.vertex = c.vertex)
    (hneab : a ≠ b) (hnebc : b ≠ c) (hneac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔ r.rotationDistance a b < r.rotationDistance a c := by
  rw [r.mem_rotationInterval_iff_ranks a a b c rfl hab hac hneab hnebc hneac,
    r.rotationDistance_self]
  have hpos := r.rotationDistance_pos_of_ne a b hab hneab.symm
  omega

/-- Strict literal rotation intervals are cyclic in three distinct incident darts. -/
theorem mem_rotationInterval_cyclic (a b c : Dart G)
    (hab : a.vertex = b.vertex) (hbc : b.vertex = c.vertex)
    (hneab : a ≠ b) (hnebc : b ≠ c) (hneac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔ c ∈ r.rotationInterval b a := by
  rw [r.mem_rotationInterval_iff_portRank a b c hab hbc hneab hnebc hneac,
    r.mem_rotationInterval_iff_portRank b c a hbc (hab.trans hbc).symm
      hnebc hneac.symm hneab.symm]
  tauto

end Cslib.Complexity.Graph.RotationSystem

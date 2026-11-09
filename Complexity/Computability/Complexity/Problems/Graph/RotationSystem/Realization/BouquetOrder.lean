/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.ClosedPassages.Loop
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Linear ranks in a literal vertex rotation

Cutting a finite vertex cycle at any one of its darts gives first-hit ranks. These ranks
retain the direction of the supplied rotation. They are intended for the polygonal loop
construction, without assuming a geometric realization.
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

/-- In numerical genus zero, the linear intervals of two distinct indexed loops at one
vertex are disjoint or strictly nested. This derives the ordering from the numerical
hypothesis; a noncrossing matching is not an input. -/
theorem portRank_loops_laminar
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hr : r.NumericalGenusZero)
    (e f : Fin G.2.length) (hef : e ≠ f)
    (he : (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true))
    (hf : (Dart.vertex (G := G) (f, false)) = Dart.vertex (f, true))
    (hv : (Dart.vertex (G := G) (e, false)) = Dart.vertex (f, false)) :
    max (r.portRank (e, false)) (r.portRank (e, true)) <
        min (r.portRank (f, false)) (r.portRank (f, true)) ∨
      max (r.portRank (f, false)) (r.portRank (f, true)) <
        min (r.portRank (e, false)) (r.portRank (e, true)) ∨
      (min (r.portRank (e, false)) (r.portRank (e, true)) <
          min (r.portRank (f, false)) (r.portRank (f, true)) ∧
        max (r.portRank (f, false)) (r.portRank (f, true)) <
          max (r.portRank (e, false)) (r.portRank (e, true))) ∨
      (min (r.portRank (f, false)) (r.portRank (f, true)) <
          min (r.portRank (e, false)) (r.portRank (e, true)) ∧
        max (r.portRank (e, false)) (r.portRank (e, true)) <
          max (r.portRank (f, false)) (r.portRank (f, true))) := by
  have hends (i : Fin G.2.length) : (i, false) ≠ (i, true) := by simp
  have hcross (b c : Bool) : (e, b) ≠ (f, c) :=
    fun h => hef (congrArg Prod.fst h)
  have hva : (Dart.vertex (G := G) (f, false)) = Dart.vertex (e, false) := hv.symm
  have hvb : (Dart.vertex (G := G) (f, false)) = Dart.vertex (e, true) := hv.symm.trans he
  have hsame : ((e, false) ∈ r.rotationInterval (f, false) (f, true)) ↔
      ((e, true) ∈ r.rotationInterval (f, false) (f, true)) := by
    have hnot : ¬(((e, false) ∈ r.rotationInterval (f, false) (f, true)) ↔
        ((e, true) ∉ r.rotationInterval (f, false) (f, true))) := fun h =>
      r.not_alternates_loops hG hr e f hef he hf
        ⟨hends e, hends f, hcross false false, hcross false true,
          hcross true false, hcross true true, he, hf, hv, h⟩
    constructor
    · intro ha
      by_contra hb
      exact hnot ⟨fun _ => hb, fun _ => ha⟩
    · intro hb
      by_contra ha
      exact hnot ⟨fun h => False.elim (ha h), fun h => False.elim (h hb)⟩
  rw [r.mem_rotationInterval_iff_portRank _ _ _ hva (hv.trans hf)
      (hcross false false).symm (hcross false true) (hends f),
    r.mem_rotationInterval_iff_portRank _ _ _ hvb (he.symm.trans (hv.trans hf))
      (hcross true false).symm (hcross true true) (hends f)] at hsame
  have hneq (b c : Bool) : r.portRank (e, b) ≠ r.portRank (f, c) := by
    have hvertex : (Dart.vertex (G := G) (e, b)) = Dart.vertex (f, c) := by
      cases b <;> cases c <;> omega
    exact fun h => hcross b c (r.portRank_injective _ _ hvertex h)
  have haa : r.portRank (e, false) ≠ r.portRank (e, true) :=
    fun h => hends e (r.portRank_injective _ _ he h)
  have hcc : r.portRank (f, false) ≠ r.portRank (f, true) :=
    fun h => hends f (r.portRank_injective _ _ hf h)
  have hac := hneq false false
  have had := hneq false true
  have hbc := hneq true false
  have hbd := hneq true true
  by_cases hab : r.portRank (e, false) ≤ r.portRank (e, true) <;>
    by_cases hcd : r.portRank (f, false) ≤ r.portRank (f, true) <;>
    simp only [min_def, max_def, hab, hcd, ↓reduceIte] <;> omega

end Cslib.Complexity.Graph.RotationSystem

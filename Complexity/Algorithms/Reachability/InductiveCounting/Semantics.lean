/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.InductiveCounting
public import Complexity.Foundations.Relation.InductiveCounting
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# Semantic invariants of the inductive-counting controller

The sets in this file are ghost state used in the proofs. They are not part of the controller's
registers. A scan selects distinct identifiers because its candidate register increases; equality
of its selected count with the round count then forces exhaustiveness.

## Main definitions

* `Cslib.InductiveCounting.Graph`: the graph restricted to the vertex interval.
* `Cslib.InductiveCounting.roundSet`, `Cslib.InductiveCounting.prefixCount`: the finite set
  represented by a round count and the next-round count below the current target.
* `Cslib.InductiveCounting.Observed`: the predicate observed for one included candidate.
* `Cslib.InductiveCounting.RoundCorrect`, `Cslib.InductiveCounting.ScanContext`,
  `Cslib.InductiveCounting.ScanPrefix`: ghost invariants for the round count and scan loop.
* `Cslib.InductiveCounting.Safe`: no bad vertex is reachable in the restricted input graph.
* `Cslib.InductiveCounting.Invariant`: the semantic assertion at each instruction.

## References

* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Cslib.InductiveCounting

variable {N width source k u v : ℕ} {edge : ℕ → ℕ → Bool} {bad : ℕ → Bool}
  {s : State} {choice : Bool}

/-- The input graph restricted to identifiers less than `N`. -/
def Graph (N : ℕ) (edge : ℕ → ℕ → Bool) (u v : ℕ) : Prop :=
  u < N ∧ v < N ∧ edge u v = true

open scoped Classical in
/-- The ghost set whose cardinality the controller carries. -/
noncomputable def roundSet (N : ℕ) (edge : ℕ → ℕ → Bool) (source k : ℕ) : Finset ℕ :=
  (Finset.range N).filter (· ∈ Relation.reachableWithin (Graph N edge) source k)

private theorem reachable_lt (hsource : source < N)
    (h : Relation.ReflTransGen (Graph N edge) source u) : u < N := by
  induction h with
  | refl => exact hsource
  | tail _ huv _ => exact huv.2.1

/-- Every vertex reachable within `k` steps in the restricted graph lies below `N`. -/
theorem within_lt (hsource : source < N)
    (h : Relation.RelatesWithinSteps (Graph N edge) source u k) : u < N :=
  reachable_lt hsource h.reflTransGen

/-- Membership in `roundSet` characterizes reachability from `source` within `k` steps. -/
theorem mem_roundSet (hsource : source < N) :
    u ∈ roundSet N edge source k ↔
      Relation.RelatesWithinSteps (Graph N edge) source u k := by
  classical
  exact (Finset.mem_filter).trans ⟨And.right, fun h => ⟨Finset.mem_range.mpr
    (within_lt hsource h), h⟩⟩

private theorem roundSet_zero (hsource : source < N) : roundSet N edge source 0 = {source} := by
  ext u
  rw [mem_roundSet hsource, ← Relation.mem_reachableWithin, Relation.reachableWithin_zero]
  simp

/-- Every round set contains at most `N` vertices. -/
theorem roundSet_card_le : (roundSet N edge source k).card ≤ N := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range N)

private theorem mem_roundSet_succ (hsource : source < N) (hv : v < N) :
    v ∈ roundSet N edge source (k + 1) ↔
      ∃ u ∈ roundSet N edge source k, u = v ∨ edge u v = true := by
  rw [mem_roundSet hsource, ← Relation.mem_reachableWithin, Relation.mem_reachableWithin_succ]
  constructor
  · rintro ⟨u, hu, huv⟩
    refine ⟨u, (mem_roundSet hsource).mpr hu, ?_⟩
    cases huv with
    | refl => exact Or.inl rfl
    | single h => exact Or.inr h.2.2
  · rintro ⟨u, hu, huv⟩
    have hu' := (mem_roundSet hsource).mp hu
    refine ⟨u, hu', ?_⟩
    rcases huv with rfl | huv
    · exact .refl
    · exact .single ⟨within_lt hsource hu', hv, huv⟩

/-- Round `N - 1` is already the entire reachable set. -/
private theorem mem_roundSet_final (hsource : source < N) (hk : k + 1 = N) :
    u ∈ roundSet N edge source k ↔ Relation.ReflTransGen (Graph N edge) source u := by
  have hs : {u | Relation.ReflTransGen (Graph N edge) source u} ⊆
      (Finset.range N : Set ℕ) := fun u hu => Finset.mem_range.mpr (reachable_lt hsource hu)
  have he : {u | Relation.ReflTransGen (Graph N edge) source u}.encard ≤ (k + 1 : ℕ) := by
    calc
      _ ≤ (Finset.range N : Set ℕ).encard := Set.encard_mono hs
      _ = N := by rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
      _ = k + 1 := by exact_mod_cast hk.symm
  rw [mem_roundSet hsource, ← Relation.mem_reachableWithin,
    Relation.reachableWithin_eq_of_encard_le he]
  rfl

/-- Count of members of the next round below the current target. -/
noncomputable def prefixCount (N : ℕ) (edge : ℕ → ℕ → Bool) (source k v : ℕ) : ℕ :=
  ((roundSet N edge source (k + 1)).filter (· < v)).card

/-- The prefix count below target `0` is zero. -/
@[simp] theorem prefixCount_zero : prefixCount N edge source k 0 = 0 := by
  simp [prefixCount]

private theorem prefixCount_full : prefixCount N edge source k N =
    (roundSet N edge source (k + 1)).card := by
  classical
  unfold prefixCount
  congr 1
  apply Finset.filter_true_of_mem
  intro u hu
  exact Finset.mem_range.mp (Finset.mem_of_mem_filter u hu)

private theorem prefixCount_succ (v : ℕ) : prefixCount N edge source k (v + 1) =
    prefixCount N edge source k v +
      (if v ∈ roundSet N edge source (k + 1) then 1 else 0) := by
  classical
  have he : (roundSet N edge source (k + 1)).filter (· < v + 1) =
      if v ∈ roundSet N edge source (k + 1) then
        insert v ((roundSet N edge source (k + 1)).filter (· < v))
      else (roundSet N edge source (k + 1)).filter (· < v) := by
    ext u
    split_ifs with hv <;>
      by_cases hu : u ∈ roundSet N edge source (k + 1) <;>
      by_cases huv : u = v <;>
      simp_all [Finset.mem_filter, Finset.mem_insert] <;> omega
  unfold prefixCount
  rw [he]
  split_ifs with hv
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- The predicate observed for one included candidate. -/
def Observed (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool) (s : State) (u : ℕ) : Prop :=
  if s.finalScan then bad u = true else u = s.target ∨ edge u s.target = true

/-- The count and round number are correct. -/
def RoundCorrect (N : ℕ) (edge : ℕ → ℕ → Bool) (source : ℕ) (s : State) : Prop :=
  s.round < N ∧ s.count = (roundSet N edge source s.round).card

/-- The outer loops' ghost invariant during a scan. -/
def ScanContext (N : ℕ) (edge : ℕ → ℕ → Bool) (source : ℕ) (s : State) : Prop :=
  RoundCorrect N edge source s ∧
    if s.finalScan then s.round + 1 = N
    else s.round + 1 < N ∧ s.target < N ∧
      s.nextCount = prefixCount N edge source s.round s.target

/-- The selected identifiers form a subset of the processed prefix. The ghost set `S` is not
stored by the algorithm. Omissions are allowed here and detected by the final count check. -/
def ScanPrefix (N : ℕ) (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool)
    (source : ℕ) (s : State) : Prop :=
  ∃ S : Finset ℕ, S ⊆ roundSet N edge source s.round ∧
    (∀ u ∈ S, u < s.candidate) ∧ s.selected = S.card ∧
    (s.hit = true ↔ ∃ u ∈ S, Observed edge bad s u)

/-- No bad vertex is reachable in the restricted input graph. -/
def Safe (N source : ℕ) (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool) : Prop :=
  ∀ u, Relation.ReflTransGen (Graph N edge) source u → bad u = false

/-- Semantic assertion at every instruction of the explicit controller. -/
def Invariant (N : ℕ) (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool)
    (source : ℕ) (s : State) : Prop :=
  match s.phase with
  | .round => RoundCorrect N edge source s
  | .target => RoundCorrect N edge source s ∧ s.finalScan = false ∧
      s.round + 1 < N ∧ s.target ≤ N ∧
      s.nextCount = prefixCount N edge source s.round s.target
  | .candidate => ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate ≤ N
  | .walk => ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate < N ∧ s.remaining ≤ s.round ∧
      s.current ∈ roundSet N edge source (s.round - s.remaining)
  | .guess => ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate < N ∧ 0 < s.remaining ∧ s.remaining ≤ s.round ∧
      s.current ∈ roundSet N edge source (s.round - s.remaining)
  | .edge => ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate < N ∧ 0 < s.remaining ∧ s.remaining ≤ s.round ∧
      s.current ∈ roundSet N edge source (s.round - s.remaining) ∧ s.guess < N
  | .observe => ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate < N ∧ s.candidate ∈ roundSet N edge source s.round
  | .done => ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧ s.candidate = N
  | .accept => Safe N source edge bad
  | .reject => True

/-- When the selected count matches the round count, `s.hit` reflects the entire round set. -/
theorem scan_exhaustive (hc : RoundCorrect N edge source s)
    (hp : ScanPrefix N edge bad source s) (he : s.selected = s.count) :
    s.hit = true ↔ ∃ u ∈ roundSet N edge source s.round, Observed edge bad s u := by
  obtain ⟨S, hsub, _, hd, hh⟩ := hp
  obtain ⟨_, hc⟩ := hc
  have heq : S = roundSet N edge source s.round :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  simpa only [heq] using hh

private theorem scanPrefix_start (s : State) :
    ScanPrefix N edge bad source { s with candidate := 0, selected := 0, hit := false } := by
  refine ⟨∅, Finset.empty_subset _, ?_⟩
  simp

private theorem scanPrefix_skip (h : ScanPrefix N edge bad source s) :
    ScanPrefix N edge bad source { s with candidate := s.candidate + 1 } := by
  obtain ⟨S, hsub, hlt, hd, hh⟩ := h
  exact ⟨S, hsub, fun u hu => (hlt u hu).trans (Nat.lt_succ_self _), hd, hh⟩

private theorem scanPrefix_observe (h : ScanPrefix N edge bad source s)
    (hu : s.candidate ∈ roundSet N edge source s.round) (hp : s.phase = .observe) :
    ScanPrefix N edge bad source
      (instruction N width source s (answer edge bad s) choice) := by
  classical
  simp only [instruction, hp, ScanPrefix]
  obtain ⟨S, hsub, hlt, hd, hh⟩ := h
  have hnot : s.candidate ∉ S := fun h => Nat.lt_irrefl _ (hlt _ h)
  refine ⟨insert s.candidate S, ?_, ?_, ?_, ?_⟩
  · exact Finset.insert_subset hu hsub
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Nat.lt_succ_self _
    · exact (hlt _ hu).trans (Nat.lt_succ_self _)
  · simpa [Finset.card_insert_of_notMem hnot] using hd
  · cases hf : s.finalScan <;>
      simp_all [answer, query, Observed, Finset.mem_insert, or_assoc, or_left_comm, or_comm]

private theorem scan_hit_succ (hsource : source < N) (hc : RoundCorrect N edge source s)
    (hp : ScanPrefix N edge bad source s) (he : s.selected = s.count)
    (hf : s.finalScan = false) (hv : s.target < N) :
    s.hit = true ↔ s.target ∈ roundSet N edge source (s.round + 1) := by
  rw [scan_exhaustive hc hp he, mem_roundSet_succ hsource hv]
  simp [Observed, hf]

private theorem scan_final_safe (hsource : source < N) (hc : RoundCorrect N edge source s)
    (hp : ScanPrefix N edge bad source s) (he : s.selected = s.count)
    (hf : s.finalScan = true) (hk : s.round + 1 = N) (hh : s.hit = false) :
    Safe N source edge bad := by
  intro u hu
  have hmem := (mem_roundSet_final hsource hk).mpr hu
  have hno : ¬ bad u = true := fun hbad => by
    have := (scan_exhaustive hc hp he).mpr ⟨u, hmem, by simpa [Observed, hf] using hbad⟩
    simp_all
  exact Bool.eq_false_iff.mpr hno

/-- The initial state satisfies the semantic invariant whenever `source < N`. -/
theorem invariant_initial (hsource : source < N) :
    Invariant N edge bad source (initial N source) := by
  have hN : 0 < N := by omega
  simp [initial, hsource, hN, Invariant, RoundCorrect, roundSet_zero hsource]

/-- Every underlying instruction preserves the semantic assertion. A rejected branch has no
proof obligation; dishonest omissions can survive temporarily but cannot pass a count check. -/
private theorem invariant_instruction (hsource : source < N)
    (h : Invariant N edge bad source s) (choice : Bool) :
    Invariant N edge bad source (instruction N width source s (answer edge bad s) choice) := by
  classical
  cases hp : s.phase with
  | round =>
    simp only [Invariant, hp] at h
    change RoundCorrect N edge source s at h
    simp only [instruction, hp]
    split_ifs with hk
    · change RoundCorrect N edge source _ ∧ _
      exact ⟨h, rfl, hk, Nat.zero_le _, by simp⟩
    · change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
      refine ⟨⟨h, ?_⟩, ?_, Nat.zero_le _⟩
      · change s.round + 1 = N
        have := h.1
        omega
      · exact scanPrefix_start { s with finalScan := true }
  | target =>
    simp only [Invariant, hp] at h
    change RoundCorrect N edge source s ∧ s.finalScan = false ∧
      s.round + 1 < N ∧ s.target ≤ N ∧
      s.nextCount = prefixCount N edge source s.round s.target at h
    obtain ⟨hc, hf, hk, hv, hn⟩ := h
    simp only [instruction, hp]
    split_ifs with ht
    · change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
      exact ⟨⟨hc, by simpa [hf] using And.intro hk (And.intro ht hn)⟩,
        scanPrefix_start _, Nat.zero_le _⟩
    · change RoundCorrect N edge source _
      have hv' : s.target = N := by omega
      refine ⟨hk, ?_⟩
      simpa only [hv', prefixCount_full] using hn
  | candidate =>
    simp only [Invariant, hp] at h
    change ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧ s.candidate ≤ N at h
    obtain ⟨hc, hs, hu⟩ := h
    simp only [instruction, hp]
    split_ifs with ht hb
    · change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
      exact ⟨hc, hs, ht, Nat.le_refl _, by simp [roundSet_zero hsource]⟩
    · change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
      exact ⟨hc, scanPrefix_skip hs, by dsimp; omega⟩
    · change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
      exact ⟨hc, hs, by dsimp; omega⟩
  | walk =>
    simp only [Invariant, hp] at h
    change ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate < N ∧ s.remaining ≤ s.round ∧
      s.current ∈ roundSet N edge source (s.round - s.remaining) at h
    obtain ⟨hc, hs, hu, hr, hw⟩ := h
    simp only [instruction, hp]
    split_ifs with hz he
    · change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
      exact ⟨hc, hs, hu, by simpa only [hz, Nat.sub_zero, he] using hw⟩
    · trivial
    · change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
      exact ⟨hc, hs, hu, Nat.pos_of_ne_zero hz, hr, hw⟩
  | guess =>
    simp only [Invariant, hp] at h
    change ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate < N ∧ 0 < s.remaining ∧ s.remaining ≤ s.round ∧
      s.current ∈ roundSet N edge source (s.round - s.remaining) at h
    simp only [instruction, hp]
    split_ifs with hz hv
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hv⟩
    · trivial
    · exact h
  | edge =>
    simp only [Invariant, hp] at h
    change ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate < N ∧ 0 < s.remaining ∧ s.remaining ≤ s.round ∧
      s.current ∈ roundSet N edge source (s.round - s.remaining) ∧ s.guess < N at h
    obtain ⟨hc, hs, hu, hr, hrk, hw, hv⟩ := h
    simp only [instruction, hp]
    split_ifs with he
    · change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
      refine ⟨hc, hs, hu, by dsimp; omega, ?_⟩
      have he' : s.current = s.guess ∨ edge s.current s.guess = true := by
        simpa [answer, query, hp] using he
      have heq : s.round - (s.remaining - 1) = (s.round - s.remaining) + 1 := by omega
      rw [heq, mem_roundSet_succ hsource hv]
      exact ⟨s.current, hw, he'⟩
    · trivial
  | observe =>
    simp only [Invariant, hp] at h
    change ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧
      s.candidate < N ∧ s.candidate ∈ roundSet N edge source s.round at h
    obtain ⟨hc, hs, hu, hw⟩ := h
    simp only [instruction, hp]
    change ScanContext N edge source _ ∧ ScanPrefix N edge bad source _ ∧ _
    refine ⟨hc, ?_, by dsimp; omega⟩
    simpa only [instruction, hp] using
      scanPrefix_observe (width := width) (choice := choice) hs hw hp
  | done =>
    simp only [Invariant, hp] at h
    change ScanContext N edge source s ∧ ScanPrefix N edge bad source s ∧ s.candidate = N at h
    obtain ⟨⟨hc, hm⟩, hs, hu⟩ := h
    simp only [instruction, hp]
    split_ifs with he hf hh
    · trivial
    · exact scan_final_safe hsource hc hs he hf (by simpa [hf] using hm)
        (Bool.eq_false_iff.mpr hh)
    · change RoundCorrect N edge source _ ∧ _
      have hf' : s.finalScan = false := Bool.eq_false_iff.mpr hf
      simp only [hf', Bool.false_eq_true, ↓reduceIte] at hm
      obtain ⟨hk, hv, hn⟩ := hm
      have hh' := scan_hit_succ hsource hc hs he hf' hv
      refine ⟨hc, hf', hk, by dsimp; omega, ?_⟩
      dsimp only
      rw [prefixCount_succ]
      cases hb : s.hit <;> simp_all
    · trivial
  | accept => simpa only [instruction, hp] using h
  | reject => simp [instruction, hp, Invariant]

/-- The checked controller preserves the semantic invariant on every branch. -/
theorem invariant_advance (hsource : source < N) (h : Invariant N edge bad source s)
    (choice : Bool) :
    Invariant N edge bad source (advance N width source s (answer edge bad s) choice) := by
  unfold advance
  split
  · exact h
  · dsimp only
    split
    · exact invariant_instruction hsource h choice
    · trivial

private theorem invariant_replay (hsource : source < N) (h : Invariant N edge bad source s)
    (bs : List Bool) : Invariant N edge bad source (replay N width source edge bad s bs) := by
  induction bs generalizing s with
  | nil => exact h
  | cons b bs ih => exact ih (invariant_advance hsource h b)

/-- An accepting choice replay certifies the absence of every reachable bad vertex. -/
theorem accepts_sound (hsource : source < N) (h : Accepts N width source edge bad) :
    Safe N source edge bad := by
  obtain ⟨bs, hb⟩ := h
  have hi := invariant_replay (width := width) (bad := bad) hsource
    (invariant_initial (edge := edge) (bad := bad) hsource) bs
  simpa only [Invariant, hb] using hi

end Cslib.InductiveCounting

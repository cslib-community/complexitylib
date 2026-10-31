/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.InductiveCounting.Progress
import Mathlib.Tactic.Linarith

/-!
# Honest binary choices for inductive counting

Ghost assertions describe honest scans and the as-yet unguessed suffix of a vertex identifier.
They are used only to construct a successful binary-choice replay.

Honest choices reach the final count check even when a bad vertex is reachable
(`Cslib.InductiveCounting.exists_replay_done_final`); a machine that inspects the count there
learns whether some reachable vertex is bad.

## Main definitions

* `Cslib.InductiveCounting.BinaryExtension`: a vertex extends a partial binary guess.
* `Cslib.InductiveCounting.FullPrefix`: the selected count equals the reachable prefix count.
* `Cslib.InductiveCounting.Honest`: the assertion maintained by honest choices.

## Main results

* `Cslib.InductiveCounting.accepts_iff`: correctness of the executable, binary-choice
  small-register controller.
* `Cslib.InductiveCounting.accepts_iff_not_reachable`: the controller nondeterministically decides
  nonreachability.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Cslib.InductiveCounting

variable {N width source target : ℕ} {edge : ℕ → ℕ → Bool} {bad : ℕ → Bool}
  {s : State} {choice : Bool}

/-- `v` can be obtained from the partial guess `g` by appending `bits` binary choices. -/
inductive BinaryExtension : ℕ → ℕ → ℕ → Prop
  | done (g : ℕ) : BinaryExtension 0 g g
  | bit {n g v : ℕ} (b : Bool) (h : BinaryExtension n (2 * g + b.toNat) v) :
      BinaryExtension (n + 1) g v

variable {n g v bits : ℕ}

private theorem BinaryExtension.le (h : BinaryExtension n g v) : g ≤ v := by
  induction h with
  | done => exact Nat.le_refl _
  | bit b h ih => omega

private theorem binaryExtension_exists (hlo : g * 2 ^ bits ≤ v)
    (hhi : v < (g + 1) * 2 ^ bits) : BinaryExtension bits g v := by
  induction bits generalizing g v with
  | zero =>
    simp only [Nat.pow_zero, Nat.mul_one] at hlo hhi
    have he : v = g := by omega
    subst v
    exact .done g
  | succ bits ih =>
    simp only [Nat.pow_succ] at hlo hhi
    by_cases hm : v < (2 * g + 1) * 2 ^ bits
    · apply BinaryExtension.bit false
      apply ih <;> simp only [Bool.toNat_false, Nat.add_zero] <;> nlinarith
    · apply BinaryExtension.bit true
      apply ih <;> simp only [Bool.toNat_true] <;> nlinarith

private theorem binaryExtension_zero {g v : ℕ} (h : BinaryExtension 0 g v) : g = v := by
  cases h
  rfl

/-- The selected count includes every reachable vertex of the processed prefix. -/
def FullPrefix (N : ℕ) (edge : ℕ → ℕ → Bool) (source : ℕ) (s : State) : Prop :=
  s.selected = ((roundSet N edge source s.round).filter (· < s.candidate)).card

private theorem filter_below_succ (S : Finset ℕ) (u : ℕ) :
    S.filter (· < u + 1) = if u ∈ S then insert u (S.filter (· < u))
      else S.filter (· < u) := by
  classical
  ext v
  split_ifs with hu <;> by_cases hv : v ∈ S <;> by_cases huv : v = u <;>
    simp_all [Finset.mem_filter, Finset.mem_insert] <;> omega

private theorem fullPrefix_start (s : State) :
    FullPrefix N edge source { s with candidate := 0, selected := 0 } := by
  simp [FullPrefix]

private theorem fullPrefix_skip (h : FullPrefix N edge source s)
    (hu : s.candidate ∉ roundSet N edge source s.round) :
    FullPrefix N edge source { s with candidate := s.candidate + 1 } := by
  classical
  simpa only [FullPrefix, filter_below_succ, hu, ↓reduceIte] using h

private theorem fullPrefix_observe (h : FullPrefix N edge source s)
    (hu : s.candidate ∈ roundSet N edge source s.round) :
    FullPrefix N edge source
      { s with candidate := s.candidate + 1, selected := s.selected + 1 } := by
  classical
  unfold FullPrefix at h ⊢
  dsimp only
  rw [filter_below_succ]
  simp only [hu, ↓reduceIte]
  rw [Finset.card_insert_of_notMem (by simp), h]

private theorem fullPrefix_end (h : FullPrefix N edge source s) (hc : RoundCorrect N edge source s)
    (hu : s.candidate = N) : s.selected = s.count := by
  classical
  have he : (roundSet N edge source s.round).filter (· < N) =
      roundSet N edge source s.round := by
    apply Finset.filter_true_of_mem
    intro u hu
    exact Finset.mem_range.mp (Finset.mem_of_mem_filter u hu)
  simpa only [FullPrefix, hu, he, hc.2] using h

/-- Additional ghost information used to construct honest choices. A walk retains a possible
completion; a binary guess retains a vertex extending its guessed prefix. -/
def Honest (N _width : ℕ) (edge : ℕ → ℕ → Bool) (source : ℕ) (s : State) : Prop :=
  match s.phase with
  | .round | .target | .accept => True
  | .candidate | .observe | .done => FullPrefix N edge source s
  | .walk => FullPrefix N edge source s ∧
      Relation.RelatesWithinSteps (Graph N edge) s.current s.candidate s.remaining
  | .guess => FullPrefix N edge source s ∧ ∃ v, BinaryExtension s.bits s.guess v ∧
      v < N ∧ Relation.ReflGen (Graph N edge) s.current v ∧
      Relation.RelatesWithinSteps (Graph N edge) v s.candidate (s.remaining - 1)
  | .edge => FullPrefix N edge source s ∧
      Relation.ReflGen (Graph N edge) s.current s.guess ∧
      Relation.RelatesWithinSteps (Graph N edge) s.guess s.candidate (s.remaining - 1)
  | .reject => False

private theorem honest_initial (hsource : source < N) :
    Honest N width edge source (initial N source) := by simp [initial, hsource, Honest]

/-- At a genuine binary-guess instruction, an honest choice produces a bounded prefix. -/
private def ChoiceFits (N : ℕ) (s : State) (choice : Bool) : Prop :=
  s.phase = .guess → s.bits ≠ 0 → 2 * s.guess + choice.toNat < N

/-- Every honest, semantically valid nonrejecting state has an honest next choice. -/
private theorem exists_honest_instruction (hsource : source < N) (hwidth : N ≤ 2 ^ width)
    (hsafe : s.phase = .done → s.finalScan = true → Safe N source edge bad)
    (hi : Invariant N edge bad source s)
    (hh : Honest N width edge source s) :
    ∃ choice, Honest N width edge source
      (instruction N width source s (answer edge bad s) choice) ∧ ChoiceFits N s choice := by
  classical
  cases hp : s.phase with
  | round =>
    refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
    simp only [instruction, hp]
    split_ifs
    · trivial
    · exact fullPrefix_start { s with finalScan := true }
  | target =>
    refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
    simp only [instruction, hp]
    split_ifs
    · exact fullPrefix_start s
    · trivial
  | candidate =>
    simp only [Honest, hp] at hh
    by_cases hu : s.candidate < N
    · by_cases hm : s.candidate ∈ roundSet N edge source s.round
      · refine ⟨true, ?_, by simp [ChoiceFits, hp]⟩
        simp only [instruction, hp, hu, ↓reduceIte, Honest]
        exact ⟨hh, (mem_roundSet hsource).mp hm⟩
      · refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
        simp only [instruction, hp, hu, ↓reduceIte, Bool.false_eq_true, Honest]
        exact fullPrefix_skip hh hm
    · refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
      simpa only [instruction, hp, hu, ↓reduceIte, Honest, FullPrefix] using hh
  | walk =>
    simp only [Honest, hp] at hh
    obtain ⟨hf, hw⟩ := hh
    by_cases hz : s.remaining = 0
    · have he : s.current = s.candidate := by
        exact Relation.RelatesWithinSteps.zero (hz ▸ hw)
      refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
      simpa only [instruction, hp, hz, he, ↓reduceIte, Honest, FullPrefix] using hf
    · have hr : s.remaining = 1 + (s.remaining - 1) := by omega
      rw [hr, Relation.RelatesWithinSteps.add_iff] at hw
      obtain ⟨v, hv, hw⟩ := hw
      rw [Relation.RelatesWithinSteps.one_iff] at hv
      have hc : s.current < N := by
        simp only [Invariant, hp] at hi
        exact within_lt hsource ((mem_roundSet hsource).mp hi.2.2.2.2)
      have hvN : v < N := by
        cases hv with
        | refl => exact hc
        | single hv => exact hv.2.1
      refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
      simp only [instruction, hp, hz, ↓reduceIte, Honest]
      refine ⟨hf, v, ?_, hvN, hv, ?_⟩
      · apply binaryExtension_exists
        · simp
        · simpa using hvN.trans_le hwidth
      · exact hw
  | guess =>
    simp only [Honest, hp] at hh
    obtain ⟨hf, v, hx, hv, he, hw⟩ := hh
    cases hb : s.bits with
    | zero =>
      have hgv : s.guess = v := binaryExtension_zero (hb ▸ hx)
      refine ⟨false, ?_, by simp [ChoiceFits, hb]⟩
      have hg : s.guess < N := hgv ▸ hv
      simp only [instruction, hp, hb, hg, ↓reduceIte, Honest]
      exact ⟨hf, hgv ▸ he, hgv ▸ hw⟩
    | succ bits =>
      rw [hb] at hx
      cases hx with
      | bit b hx =>
        refine ⟨b, ?_, ?_⟩
        · simp only [instruction, hp, hb, Nat.succ_ne_zero, ↓reduceIte, Honest]
          exact ⟨hf, v, by simpa only [Nat.add_sub_cancel] using hx, hv, he, hw⟩
        · intro _ _
          exact hx.le.trans_lt hv
  | edge =>
    simp only [Honest, hp] at hh
    obtain ⟨hf, he, hw⟩ := hh
    have he' : (s.current == s.guess || answer edge bad s) = true := by
      rw [Relation.reflGen_iff] at he
      rcases he with he | he <;>
        simp_all [answer, query, Graph]
    refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
    simpa only [instruction, hp, he', ↓reduceIte, Honest, FullPrefix] using And.intro hf hw
  | observe =>
    simp only [Honest, hp] at hh
    simp only [Invariant, hp] at hi
    refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
    simpa only [instruction, hp, Honest, FullPrefix] using fullPrefix_observe hh hi.2.2.2
  | done =>
    simp only [Honest, hp] at hh
    simp only [Invariant, hp] at hi
    obtain ⟨hc, hs, hu⟩ := hi
    have he := fullPrefix_end hh hc.1 hu
    refine ⟨false, ?_, by simp [ChoiceFits, hp]⟩
    by_cases hf : s.finalScan = true
    · have hb : s.hit = false := by
        apply Bool.eq_false_iff.mpr
        intro hb
        obtain ⟨u, hu, hbad⟩ := (scan_exhaustive hc.1 hs he).mp hb
        have hbad' : bad u = true := by simpa only [Observed, hf, ↓reduceIte] using hbad
        have := hsafe hp hf u ((mem_roundSet hsource).mp hu).reflTransGen
        simp_all
      simp [instruction, hp, he, hf, hb, Honest, accept]
    · simp [instruction, hp, he, hf, Honest]
  | accept => exact ⟨false, by simp [instruction, hp, Honest], by simp [ChoiceFits, hp]⟩
  | reject => simp [Honest, hp] at hh

/-- Honest guesses pass the uniform register check; no state bound is assumed of an oracle. -/
private theorem bounded_instruction (hsource : source < N) (hi : Invariant N edge bad source s)
    (hb : Bounded N width s) (hc : ChoiceFits N s choice) :
    Bounded N width (instruction N width source s (answer edge bad s) choice) := by
  have hpow : 0 < 2 ^ width := Nat.pow_pos (by omega)
  have hN : N + 1 < registerBound N width := by
    have hp : 0 < 2 ^ width := Nat.pow_pos (by omega)
    unfold registerBound
    omega
  have hw : width < registerBound N width := by unfold registerBound; omega
  cases hp : s.phase with
  | round =>
    simp only [instruction, hp]
    split_ifs <;> simp_all only [Bounded, and_true, true_and] <;> omega
  | target =>
    simp only [Invariant, hp, RoundCorrect] at hi
    simp only [instruction, hp]
    split_ifs <;> simp_all only [Bounded, and_true, true_and] <;> omega
  | candidate =>
    simp only [Invariant, hp] at hi
    simp only [instruction, hp]
    split_ifs <;> simp_all only [Bounded, and_true, true_and] <;> omega
  | walk =>
    simp only [instruction, hp]
    split_ifs
    · exact hb
    · exact bounded_reject
    · simp_all only [Bounded, and_true, true_and]
      omega
  | guess =>
    simp only [instruction, hp]
    split_ifs with hz hv
    · exact hb
    · exact bounded_reject
    · have hg := hc hp hz
      simp_all only [Bounded, true_and]
      constructor <;> omega
  | edge =>
    simp only [instruction, hp]
    split_ifs
    · simp_all only [Bounded, and_true, true_and]
      omega
    · exact bounded_reject
  | observe =>
    simp only [Invariant, hp] at hi
    obtain ⟨_, hs, hu, _⟩ := hi
    obtain ⟨S, hsub, _, he, _⟩ := hs
    have hcard : s.selected ≤ N := by
      rw [he]
      exact (Finset.card_le_card hsub).trans roundSet_card_le
    simp_all only [instruction, Bounded, and_true, true_and]
    constructor <;> omega
  | done =>
    simp only [instruction, hp]
    split_ifs with he hf hh
    · exact bounded_reject
    · exact bounded_accept
    · simp only [Invariant, hp] at hi
      have hf' : s.finalScan = false := Bool.eq_false_iff.mpr hf
      obtain ⟨⟨_, hm⟩, _, _⟩ := hi
      simp only [hf', Bool.false_eq_true, ↓reduceIte] at hm
      obtain ⟨_, hv, hn⟩ := hm
      have hnext : s.nextCount ≤ N := by
        rw [hn]
        exact (Finset.card_filter_le _ _).trans roundSet_card_le
      have hhit : s.hit.toNat ≤ 1 := by cases s.hit <;> decide
      simp_all only [Bounded, and_true, true_and]
      constructor <;> omega
    · exact bounded_reject
  | accept => simpa only [instruction, hp] using hb
  | reject => simpa only [instruction, hp] using hb

/-- Honest next instructions pass both executable checks. -/
private theorem exists_honest_step (hsource : source < N) (hwidth : N ≤ 2 ^ width)
    (hsafe : s.phase = .done → s.finalScan = true → Safe N source edge bad)
    (hi : Invariant N edge bad source s)
    (hb : Bounded N width s) (hh : Honest N width edge source s) :
    ∃ choice, Honest N width edge source (step N width source edge bad s choice) := by
  by_cases hs : halted s = true
  · exact ⟨false, by simpa only [step, advance_halted _ _ hs] using hh⟩
  obtain ⟨b, hh', hc⟩ := exists_honest_instruction hsource hwidth hsafe hi hh
  refine ⟨b, ?_⟩
  have hb' := bounded_instruction hsource hi hb hc
  have hr := rank_instruction_lt (width := width) hi (Bool.eq_false_iff.mpr hs) b
  simpa only [step, advance, hs, Bool.false_eq_true, ↓reduceIte, hb', hr, and_self] using hh'

/-- The initial controller state satisfies the uniform register bound. -/
theorem bounded_initial : Bounded N width (initial N source) := by
  unfold initial
  split
  · simp [Bounded, registerBound]
  · exact bounded_reject

/-- Honest choices yield an accepting replay whenever no bad vertex is reachable. -/
theorem accepts_complete (hsource : source < N) (hwidth : N ≤ 2 ^ width)
    (hsafe : Safe N source edge bad) : Accepts N width source edge bad := by
  suffices h : ∀ n s, rank N width s = n → Invariant N edge bad source s →
      Bounded N width s → Honest N width edge source s →
      ∃ bs, (replay N width source edge bad s bs).phase = .accept by
    exact h _ _ rfl (invariant_initial hsource) bounded_initial (honest_initial hsource)
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro s hr hi hb hh
    by_cases hs : halted s = true
    · refine ⟨[], ?_⟩
      cases hp : s.phase <;> simp_all [halted, Honest, replay]
    · obtain ⟨b, hh'⟩ := exists_honest_step hsource hwidth (fun _ _ => hsafe) hi hb hh
      have hr' := rank_advance_lt (N := N) (width := width) (source := source)
        (answer edge bad s) b (Bool.eq_false_iff.mpr hs)
      obtain ⟨bs, hbs⟩ := ih _ (by simpa only [step, hr] using hr')
        (step N width source edge bad s b) rfl (invariant_advance hsource hi b)
        (bounded_advance _ _ hb) hh'
      exact ⟨b :: bs, hbs⟩

/-- Only the final count check can accept. -/
private theorem advance_ne_accept {ans choice : Bool} (hs : s.phase ≠ .accept)
    (hd : ¬ (s.phase = .done ∧ s.finalScan = true)) :
    (advance N width source s ans choice).phase ≠ .accept := by
  unfold advance
  by_cases hh : halted s = true
  · simp only [hh, ↓reduceIte]
    exact hs
  · simp only [hh, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · cases hp : s.phase <;> simp only [instruction, hp] <;> (try split_ifs) <;> simp_all [reject]
    · simp [reject]

/-- **Honest choices reach the final count check**, whether or not a bad vertex is reachable:
some replay ends in the final scan's `done` instruction with every reachable vertex selected. -/
theorem exists_replay_done_final (hsource : source < N) (hwidth : N ≤ 2 ^ width) :
    ∃ bs, (replay N width source edge bad (initial N source) bs).phase = .done ∧
      (replay N width source edge bad (initial N source) bs).finalScan = true ∧
      (replay N width source edge bad (initial N source) bs).selected =
        (replay N width source edge bad (initial N source) bs).count := by
  suffices h : ∀ n s, rank N width s = n → Invariant N edge bad source s →
      Bounded N width s → Honest N width edge source s → s.phase ≠ .accept →
      ∃ bs, (replay N width source edge bad s bs).phase = .done ∧
        (replay N width source edge bad s bs).finalScan = true ∧
        (replay N width source edge bad s bs).selected =
          (replay N width source edge bad s bs).count by
    exact h _ _ rfl (invariant_initial hsource) bounded_initial (honest_initial hsource)
      (by simp [initial, hsource])
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro s hr hi hb hh hna
    by_cases hdone : s.phase = .done ∧ s.finalScan = true
    · refine ⟨[], hdone.1, hdone.2, ?_⟩
      simp only [Honest, hdone.1] at hh
      simp only [Invariant, hdone.1] at hi
      exact fullPrefix_end hh hi.1.1 hi.2.2
    by_cases hs : halted s = true
    · exfalso
      cases hp : s.phase <;> simp_all [halted, Honest]
    · obtain ⟨b, hh'⟩ := exists_honest_step hsource hwidth
        (fun hp hf => absurd ⟨hp, hf⟩ hdone) hi hb hh
      have hr' := rank_advance_lt (N := N) (width := width) (source := source)
        (answer edge bad s) b (Bool.eq_false_iff.mpr hs)
      obtain ⟨bs, hbs⟩ := ih _ (by simpa only [step, hr] using hr')
        (step N width source edge bad s b) rfl (invariant_advance hsource hi b)
        (bounded_advance _ _ hb) hh' (advance_ne_accept hna hdone)
      exact ⟨b :: bs, hbs⟩

/-- Correctness of the executable, binary-choice small-register controller. -/
theorem accepts_iff (hsource : source < N) (hwidth : N ≤ 2 ^ width) :
    Accepts N width source edge bad ↔ Safe N source edge bad :=
  ⟨accepts_sound hsource, accepts_complete hsource hwidth⟩

/-- In particular, the executable controller nondeterministically decides nonreachability. -/
theorem accepts_iff_not_reachable (hsource : source < N) (hwidth : N ≤ 2 ^ width) :
    Accepts N width source edge (fun u => u == target) ↔
      ¬ Relation.ReflTransGen (Graph N edge) source target := by
  rw [accepts_iff hsource hwidth]
  constructor
  · intro h hr
    have := h target hr
    simp at this
  · intro h u hu
    by_cases he : u = target
    · subst u
      exact False.elim (h hu)
    · simp [he]

end Cslib.InductiveCounting

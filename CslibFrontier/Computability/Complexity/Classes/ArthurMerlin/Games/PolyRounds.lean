/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.Repetition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.BitString.List

/-!
# Public-coin games with polynomially many rounds

Arthur–Merlin games (`Cslib.Complexity.AMPolyGameClass`, `Cslib.Complexity.AMPolyRounds`) whose
move patterns and game shapes vary with the input length `n = (enc a).length`, computed in
polynomial time from `n` in unary. Every fixed-pattern game `AMGameClass enc π` embeds into
`AMPolyGameClass enc (fun _ => π)`, and every `AM[k]` embeds into `AMPolyRounds enc (fun _ => k)`.

The file also supplies the dynamic polynomial-time extraction of `AMGame.copyTranscript` over
runtime shapes (`Cslib.Complexity.AMGame.computableInPolyTime_copyTranscript_dyn`) via
`foldlWith_spec`, plus value-preserving adjacent-Merlin merging and trailing zero-bit Arthur
padding (`Cslib.Complexity.AMGame.value_mergeMerlin`,
`Cslib.Complexity.AMGame.value_append_arthur_zero`).

## Main definitions

* `Cslib.Complexity.encAMMove`, `Cslib.Complexity.encAMShape`: encodings of `AMMove` and of
  public-coin game shapes.
* `Cslib.Complexity.IsAMPolyGameVerifier`, `Cslib.Complexity.AMPolyGameClass`,
  `Cslib.Complexity.AMPolyRounds`: public-coin game verifiers with input-length-dependent shapes.

## Main results

* `Cslib.Complexity.AMGameClass_subset_AMPolyGameClass`,
  `Cslib.Complexity.AMk_subset_AMPolyRounds`: constant-round classes embed into dynamic ones.
* `Cslib.Complexity.AMGame.computableInPolyTime_copyTranscript_dyn`: `copyTranscript` is
  polynomial-time for dynamic game shapes.
* `Cslib.Complexity.AMGame.value_mergeMerlin`,
  `Cslib.Complexity.AMGame.value_append_arthur_zero`: shape normalizations preserving game value.

## References

* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07] (only Theorem 8.8 is cited; other section locators unverified)
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

/-- Boolean tag of a public-coin move: `false` for Arthur, `true` for Merlin. -/
@[expose] def AMMove.toBool : AMMove → Bool
  | .arthur => false
  | .merlin => true

/-- `AMMove.toBool` is injective. -/
theorem AMMove.toBool_injective : Function.Injective AMMove.toBool := by
  intro x y h
  cases x <;> cases y <;> simp_all [AMMove.toBool]

/-- Binary encoding of a public-coin move (`[false]` for Arthur, `[true]` for Merlin). -/
@[expose] def encAMMove : AMMove ↪ List Bool :=
  ⟨fun m => encBool m.toBool, fun _ _ h => AMMove.toBool_injective (encBool.injective h)⟩

/-- Binary encoding of a public-coin game shape as a framed list of `(move, unary length)` pairs. -/
abbrev encAMShape : List (AMMove × ℕ) ↪ List Bool :=
  encList (encPair encAMMove encUnary)

namespace AMGame

/-- The total transcript length is at most the encoded length of a public-coin game shape. -/
theorem transcriptLength_le_length_encAMShape (g : List (AMMove × ℕ)) :
    transcriptLength g ≤ (encAMShape g).length := by
  induction g with
  | nil => simp [transcriptLength]
  | cons x g ih =>
    obtain ⟨m, n⟩ := x
    simp only [transcriptLength, List.map_cons, List.sum_cons, encAMShape, encList_cons,
      List.length_append, length_frame, length_encPair, encUnary_apply,
      List.length_replicate] at ih ⊢
    omega

/-- Evaluating a fixed polynomial shape `G` at unary `n` is polynomial-time. -/
theorem computableInPolyTime_evalShape (G : List (AMMove × Polynomial ℕ)) :
    ComputableInPolyTime (evalShape G) encUnary encAMShape := by
  induction G with
  | nil => exact ComputableInPolyTime.const []
  | cons x G ih =>
    obtain ⟨m, p⟩ := x
    have hlen : ComputableInPolyTime (fun n => p.eval n) encUnary encUnary :=
      ComputableInPolyTime.unary_eval p
    have hpair : ComputableInPolyTime (fun n => (m, p.eval n)) encUnary
        (encPair encAMMove encUnary) :=
      (ComputableInPolyTime.const m).prod hlen
    exact (hpair.cons' ih).of_enc_eq fun n => by simp [evalShape]

/-- Iterative state for extracting copy `i` of a parallel repetition over a runtime shape. -/
private abbrev CopyStepParam := ℕ × ℕ

/-- One step of `copyTranscript`: extract row `i` of the `n`-bit block and drop `m * n` bits. -/
private def copyStep (p : CopyStepParam) (st : List Bool × List Bool) (x : AMMove × ℕ) :
    List Bool × List Bool :=
  (st.1.drop (p.1 * x.2), st.2 ++ BitString.listRow x.2 p.2 st.1)

private theorem foldl_copyStep (m i : ℕ) (g : List (AMMove × ℕ)) (w acc : List Bool) :
    (g.foldl (copyStep (m, i)) (w, acc)).2 = acc ++ copyTranscript m i g w := by
  induction g generalizing w acc with
  | nil => simp [copyTranscript]
  | cons x g ih =>
    obtain ⟨_, n⟩ := x
    simp only [List.foldl_cons, copyStep, ih, copyTranscript, List.append_assoc]

/-- **Dynamic `copyTranscript` is polynomial-time** when `m`, `i`, the game shape `g`, and the
repeated transcript `w` are computed in polynomial time from the input. -/
theorem computableInPolyTime_copyTranscript_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {m i : γ → ℕ} {g : γ → List (AMMove × ℕ)} {w : γ → List Bool}
    (hm : ComputableInPolyTime m encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary)
    (hg : ComputableInPolyTime g encIn encAMShape) (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun x => copyTranscript (m x) (i x) (g x) (w x)) encIn encBits := by
  have hstep : ComputableInPolyTime
      (fun p : (CopyStepParam × (List Bool × List Bool)) × (AMMove × ℕ) =>
        copyStep p.1.1 p.1.2 p.2)
      (encFoldStep (encPair encUnary encUnary) (encPair encBits encBits)
        (encPair encAMMove encUnary))
      (encPair encBits encBits) := by
    unfold copyStep
    fun_prop
  obtain ⟨c₁, d₁, hwlen⟩ := (show PolyBounded (fun x => (encIn x).length) (fun x => (w x).length)
    from by simpa only [encBits_apply] using hw.polyBounded_length).exists_le
  obtain ⟨c₂, d₂, hglen⟩ := hg.polyBounded_length.exists_le
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encPair encUnary encUnary) (encB := encPair encBits encBits)
    (encA := encPair encAMMove encUnary) (encL := encAMShape)
    (par := fun x => (m x, i x)) (list := g) (init := fun x => (w x, []))
    (step := copyStep) (hm.prod hi) hg (hw.prod (ComputableInPolyTime.const [])) hstep
    (fun x pre st => st.1.length ≤ (w x).length ∧ st.2.length = transcriptLength pre)
    (fun x => ⟨le_rfl, rfl⟩)
    (fun x pre st val _ hst => by
      refine ⟨?_, ?_⟩
      · simp only [copyStep, List.length_drop]
        omega
      · simp only [copyStep, List.length_append, BitString.length_listRow, hst.2,
          transcriptLength, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, add_zero])
    (size := fun x =>
      (2 * c₁ + 1 + 2 * c₂) * ((encIn x).length + 1) ^ max d₁ d₂)
    (PolyBounded.of_forall_le _ _ fun x => le_rfl)
    (fun x pre st hpre hst => by
      obtain ⟨sfx, hsfx⟩ := hpre
      have hlen : transcriptLength pre ≤ transcriptLength (g x) := by
        rw [← hsfx]
        simp only [transcriptLength, List.map_append, List.sum_append]
        exact Nat.le_add_right _ _
      have htr := (hlen.trans (transcriptLength_le_length_encAMShape (g x))).trans (hglen x)
      have hp1 : ((encIn x).length + 1) ^ d₁ ≤ ((encIn x).length + 1) ^ max d₁ d₂ :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
      have hp2 : ((encIn x).length + 1) ^ d₂ ≤ ((encIn x).length + 1) ^ max d₁ d₂ :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)
      have hpow : 1 ≤ ((encIn x).length + 1) ^ max d₁ d₂ := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have h1 : (w x).length ≤ c₁ * ((encIn x).length + 1) ^ max d₁ d₂ :=
        (hwlen x).trans (Nat.mul_le_mul_left _ hp1)
      have h2 : transcriptLength pre ≤ c₂ * ((encIn x).length + 1) ^ max d₁ d₂ :=
        htr.trans (Nat.mul_le_mul_left _ hp2)
      simp only [length_encPair, encBits_apply]
      nlinarith)
  exact ((ComputableInPolyTime.snd encBits encBits).comp hspec.1).of_enc_eq fun x => by
    simp only [Function.comp_apply, foldl_copyStep, List.nil_append]

/-- Merging consecutive Merlin moves preserves `AMGame.value true` and `AMGame.arthurBits`. -/
@[expose] def mergeMerlin : List (AMMove × ℕ) → List (AMMove × ℕ)
  | [] => []
  | (.arthur, n) :: g => (.arthur, n) :: mergeMerlin g
  | (.merlin, n) :: g =>
    match mergeMerlin g with
    | (.merlin, n') :: g' => (.merlin, n + n') :: g'
    | g' => (.merlin, n) :: g'

/-- `mergeMerlin` preserves `arthurBits`. -/
theorem arthurBits_mergeMerlin (g : List (AMMove × ℕ)) :
    arthurBits (mergeMerlin g) = arthurBits g := by
  induction g with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp [mergeMerlin, arthurBits, ih]
    · simp only [mergeMerlin]
      cases h : mergeMerlin g with
      | nil => simp [arthurBits, ← ih, h]
      | cons y g' =>
        obtain ⟨_ | _, n'⟩ := y <;> simp [arthurBits, ← ih, h]

/-- `mergeMerlin` preserves `AMGame.value true`. -/
theorem value_mergeMerlin (g : List (AMMove × ℕ)) (f : List Bool → ℚ) :
    value true (mergeMerlin g) f = value true g f := by
  induction g generalizing f with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [mergeMerlin, value_arthur]
      congr 1
      exact sum_congr rfl fun _ _ => ih _
    · simp only [mergeMerlin]
      have hsame : value true ((.merlin, n) :: mergeMerlin g) f =
          value true ((.merlin, n) :: g) f :=
        sup'_congr univ_nonempty rfl fun y _ => ih _
      cases h : mergeMerlin g with
      | nil => simpa [h] using hsame
      | cons y g' =>
        obtain ⟨_ | _, n'⟩ := y
        · simpa [h] using hsame
        · dsimp only
          exact (value_merge_merlin [] g' n n' f).symm.trans (by simpa [h] using hsame)

/-- Appending a zero-bit Arthur move preserves `arthurBits`. -/
theorem arthurBits_append_arthur_zero (g : List (AMMove × ℕ)) :
    arthurBits (g ++ [(.arthur, 0)]) = arthurBits g := by
  induction g with
  | nil => rfl
  | cons x g ih => obtain ⟨_ | _, n⟩ := x <;> simp [arthurBits, ih]

/-- Appending a zero-bit Arthur move preserves `AMGame.value true`. -/
theorem value_append_arthur_zero (g : List (AMMove × ℕ)) (f : List Bool → ℚ) :
    value true (g ++ [(.arthur, 0)]) f = value true g f := by
  simpa using value_insert_zero true g [] .arthur f

end AMGame

open AMGame

/-- `V` is a public-coin poly-round game verifier for `A` with dynamic shape `g` evaluated at
the encoded input length `(enc a).length`. -/
@[expose] def IsAMPolyGameVerifier (enc : α ↪ List Bool) (g : ℕ → List (AMMove × ℕ))
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 * 2 ^ arthurBits (g (enc a).length) ≤ 3 * count (g (enc a).length) fun t =>
      V (a, t)) ∧
    (a ∉ A → 3 * count (g (enc a).length) (fun t => V (a, t)) ≤
      2 ^ arthurBits (g (enc a).length))

/-- Game-value characterization of `IsAMPolyGameVerifier`. -/
theorem isAMPolyGameVerifier_iff_value {enc : α ↪ List Bool} {g : ℕ → List (AMMove × ℕ)}
    {V : α × List Bool → Bool} {A : Set α} :
    IsAMPolyGameVerifier enc g V A ↔ ∀ a,
      (a ∈ A → 2 ≤ 3 * value true (g (enc a).length) (fun t => ((V (a, t)).toNat : ℚ))) ∧
      (a ∉ A → 3 * value true (g (enc a).length) (fun t => ((V (a, t)).toNat : ℚ)) ≤ 1) := by
  refine forall_congr' fun a => and_congr (imp_congr_right fun _ => ?_)
    (imp_congr_right fun _ => ?_)
  all_goals
    rw [← Nat.cast_le (α := ℚ)]
    push_cast
    rw [count_eq]
    have hp : (0 : ℚ) < 2 ^ arthurBits (g (enc a).length) := by positivity
    constructor <;> intro h <;> nlinarith

/-- Problems decided by polynomial-time public-coin game verifiers whose move pattern at input
length `n` is `π n`. -/
@[expose] def AMPolyGameClass (enc : α ↪ List Bool) (π : ℕ → List AMMove) : Set (Set α) :=
  {A | ∃ (g : ℕ → List (AMMove × ℕ)) (V : α × List Bool → Bool),
    (∀ n, (g n).map Prod.fst = π n) ∧
      ComputableInPolyTime g encUnary encAMShape ∧
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsAMPolyGameVerifier enc g V A}

/-- `AM[k(n)]` for input-length-dependent alternating move count `k : ℕ → ℕ`, Arthur first. -/
@[expose] def AMPolyRounds (enc : α ↪ List Bool) (k : ℕ → ℕ) : Set (Set α) :=
  AMPolyGameClass enc (fun n => alternatingMoves .arthur (k n))

/-- Every fixed-pattern public-coin game class embeds into `AMPolyGameClass`. -/
theorem AMGameClass_subset_AMPolyGameClass {enc : α ↪ List Bool} (π : List AMMove) :
    AMGameClass enc π ⊆ AMPolyGameClass enc (fun _ => π) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  refine ⟨evalShape G, V, fun n => ?_, computableInPolyTime_evalShape G, hV, hA⟩
  simp [evalShape, ← hG]

/-- Every constant-round `AM[k]` embeds into `AMPolyRounds`. -/
theorem AMk_subset_AMPolyRounds {enc : α ↪ List Bool} (k : ℕ) :
    AMk enc k ⊆ AMPolyRounds enc (fun _ => k) :=
  AMGameClass_subset_AMPolyGameClass _

end Cslib.Complexity

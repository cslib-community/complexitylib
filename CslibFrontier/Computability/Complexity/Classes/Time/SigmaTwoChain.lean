/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time.SigmaTwo
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockTrace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Guessing a chain of configurations in `Σ₂TIME`

A deterministic process `s ↦ next p s bw` from a fixed start `s₀`, whose `m`-th iterate satisfies a
test `goal`, can be verified in `Σ₂TIME`: the existential block guesses the parameter `bw` and the
iterates `s₁, …, s_m`, written as framed words, and the universal block picks an index `i` and a
position `j`. The verifier replays a machine computing `next` on the guessed word `w_i`, for as
many steps as the certificate is long, and compares the bit at position `j` of its output with the
bit at position `j` of the framed word `w_{i+1}` followed by `true`; at the last word it replays a
machine computing `goal` instead (`Cslib.Complexity.mem_SigmaTwoTIME_of_chain`).

The verifier never decodes a guessed word, and never compares two words of unbounded length: a
deterministic run only appends to its output, so the replay output is always a prefix of the
encoded value (`Turing.MultiTapeTM.ComputesInTimeAndSpace.output_runFrom_prefix`), and agreeing
with a framed word at every position forces equality, by induction along the chain. Both the
replay and the single-position comparison are linear, so the verifier is linear in its input. The
clock is the existential certificate itself, so an honest replay finishes once the certificates
are long enough, and a dishonest certificate cannot make the replay longer.

This is the configuration-guessing step of the time–space speedup of [Kannan][Kannan1984] and of
[Fortnow, Lipton, van Melkebeek and Viglas, Lemma 3.1][FortnowLiptonVanMelkebeekViglas2005], stated
for an arbitrary iterated step so that it serves both the simulation of a machine on its own input
and on a virtually padded input.

## Main results

* `Cslib.Complexity.mem_SigmaTwoTIME_of_chain`: a chain of iterates with a linear threshold is in
  `Σ₂TIME`.

## References

* [R. Kannan, *Towards Separating Nondeterminism from Determinism*][Kannan1984]
* [L. Fortnow, R. Lipton, D. van Melkebeek, A. Viglas, *Time-Space Lower Bounds for
  Satisfiability*][FortnowLiptonVanMelkebeekViglas2005]
-/

public section

open _root_.Turing _root_.Turing.MultiTapeTM

namespace Cslib.Complexity

/-! ### Words agreeing at every position -/

/-- Two words agreeing at every position up to the length of the second one are equal. -/
private theorem eq_of_forall_take_drop {P Q : List Bool}
    (h : ∀ j ≤ Q.length, (P.drop j).take 1 = (Q.drop j).take 1) : P = Q := by
  induction Q generalizing P with
  | nil =>
    have := h 0 le_rfl
    cases P with
    | nil => rfl
    | cons a P => simp at this
  | cons b Q ih =>
    cases P with
    | nil => simpa using h 0 (Nat.zero_le _)
    | cons a P =>
      have h0 := h 0 (Nat.zero_le _)
      simp only [List.drop_zero, List.take_succ_cons, List.take_zero, List.cons.injEq,
        and_true] at h0
      refine h0 ▸ congrArg _ (ih fun j hj => ?_)
      simpa using h (j + 1) (by simp; omega)

/-- A framed word followed by `true` that is a prefix of another framed word followed by `true`
is that word. -/
private theorem eq_of_frame_prefix {w X : List Bool}
    (h : frame w ++ [true] <+: frame X ++ [true]) : w = X := by
  obtain ⟨r, hr⟩ := h
  rw [List.append_assoc] at hr
  exact (frame_append_inj hr).1

/-! ### Counting leading `true`s -/

/-- The number of leading `true`s of a word. -/
private def leadingTrues : List Bool → ℕ
  | true :: v => leadingTrues v + 1
  | _ => 0

/-- The transducer copying the leading `true`s and erasing the rest. -/
private def leadingTruesT : Transducer Bool Bool where
  q₀ := true
  step q b := if q && b then (true, [true]) else (false, [])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

private theorem leadingTruesT_run_false (v : List Bool) : leadingTruesT.run false v = [] := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    have hs : leadingTruesT.step false b = (false, []) := by cases b <;> rfl
    rw [Transducer.run_cons, hs, ih]
    rfl

private theorem leadingTruesT_run (v : List Bool) :
    leadingTruesT.run true v = List.replicate (leadingTrues v) true := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b
    · have hs : leadingTruesT.step true false = (false, []) := rfl
      rw [Transducer.run_cons, hs, leadingTruesT_run_false]
      rfl
    · have hs : leadingTruesT.step true true = (true, [true]) := rfl
      rw [Transducer.run_cons, hs, ih]
      rfl

private theorem leadingTrues_inO :
    ComputableInO leadingTrues encBits encUnary (fun v => (encBits v).length)
      (fun v => (encBits v).length) :=
  (ComputableInDegree.of_transducer leadingTruesT fun v => (leadingTruesT_run v).symm).inO_one

private theorem leadingTrues_replicate_append (i : ℕ) (v : List Bool) :
    leadingTrues (List.replicate i true ++ false :: v) = i := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [List.replicate_succ, leadingTrues] using ih

/-! ### The verifier -/

/-- The guessed words from index `i` of the universal block `v` on: the start `w₀`, then the words
framed in the existential block `u` after the parameter. -/
private def cvRest (w₀ u v : List Bool) : List (List Bool) :=
  (w₀ :: frames (unframe (dropFrame u))).drop (leadingTrues v)

/-- The position chosen by the universal block `v`: the `true`s after its first run. -/
private def cvPos (v : List Bool) : ℕ := leadingTrues (v.drop (leadingTrues v + 1))

/-- **The chain verifier.** On the encoded parameter `pb`, the start word `w₀`, the existential
block `u` and the universal block `v`: from index `i` on, with no word left it accepts, at the last
word `w` it accepts when the replay `rG u (frame pb ++ w)` of the goal test begins with `true`, and
at a word `w` followed by `w'` it accepts when the replay `rF u (frame pb ++ frame w ++ bw)` of the
step agrees at position `j` with `frame w' ++ [true]`. Here `bw` is the parameter framed at the
start of `u`, and `i` and `j` are read off `v` by `cvPos` and `leadingTrues`. -/
private def chainCheck (rF rG : List Bool × List Bool → List Bool) (pb w₀ u v : List Bool) : Bool :=
  (cvRest w₀ u v).isEmpty ||
    ((cvRest w₀ u v).tail.isEmpty &&
      decide (((rG (u, frame pb ++ (cvRest w₀ u v).headD [])).take 2) = [true])) ||
    (!(cvRest w₀ u v).tail.isEmpty &&
      decide ((((rF (u, frame pb ++ (frame ((cvRest w₀ u v).headD []) ++ unframe u))).drop
          (cvPos v)).take 1) =
        (((frame ((cvRest w₀ u v).tail.headD []) ++ [true]).drop (cvPos v)).take 1)))

private theorem chainCheck_nil {rF rG : List Bool × List Bool → List Bool} {pb w₀ u v : List Bool}
    (h : cvRest w₀ u v = []) : chainCheck rF rG pb w₀ u v = true := by
  simp [chainCheck, h]

private theorem chainCheck_single {rF rG : List Bool × List Bool → List Bool}
    {pb w₀ u v w : List Bool} (h : cvRest w₀ u v = [w]) :
    chainCheck rF rG pb w₀ u v = decide (((rG (u, frame pb ++ w)).take 2) = [true]) := by
  simp [chainCheck, h]

private theorem chainCheck_cons_cons {rF rG : List Bool × List Bool → List Bool}
    {pb w₀ u v w w' : List Bool} {r : List (List Bool)} (h : cvRest w₀ u v = w :: w' :: r) :
    chainCheck rF rG pb w₀ u v = decide ((((rF (u, frame pb ++ (frame w ++ unframe u))).drop
        (cvPos v)).take 1) = (((frame w' ++ [true]).drop (cvPos v)).take 1)) := by
  simp [chainCheck, h]

/-! ### The universal choices -/

/-- The universal block choosing the index `i` and the position `j`, padded to length `L`. -/
private def pick (i j L : ℕ) : List Bool :=
  List.replicate i true ++ false :: (List.replicate j true ++ false ::
    List.replicate (L - (i + j + 2)) false)

private theorem length_pick {i j L : ℕ} (h : i + j + 2 ≤ L) : (pick i j L).length = L := by
  simp only [pick, List.length_append, List.length_replicate, List.length_cons]
  omega

private theorem leadingTrues_pick (i j L : ℕ) : leadingTrues (pick i j L) = i :=
  leadingTrues_replicate_append _ _

private theorem drop_replicate_append (i : ℕ) (r : List Bool) :
    (List.replicate i true ++ false :: r).drop (i + 1) = r := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [List.replicate_succ] using ih

private theorem cvPos_pick (i j L : ℕ) : cvPos (pick i j L) = j := by
  rw [cvPos, leadingTrues_pick, pick, drop_replicate_append, leadingTrues_replicate_append]

/-! ### Lengths of guessed words -/

/-- The words framed in `E` before index `i` take at least one bit each, and the word at index `i`
twice its length. -/
private theorem add_two_mul_length_le_of_drop_frames {E : List Bool} {i : ℕ} {w : List Bool}
    {r : List (List Bool)} (h : (frames E).drop i = w :: r) : i + 2 * w.length ≤ E.length := by
  induction i generalizing E with
  | zero =>
    have hE : E ≠ [] := by rintro rfl; simp at h
    rw [List.drop_zero, frames_of_ne_nil hE, List.cons.injEq] at h
    have := length_unframe_add_dropFrame_le E
    rw [h.1] at this
    omega
  | succ i ih =>
    have hE : E ≠ [] := by rintro rfl; simp at h
    rw [frames_of_ne_nil hE, List.drop_succ_cons] at h
    have := ih h
    have := length_dropFrame_lt hE
    omega

/-- At most as many words are framed in `E` as `E` has bits. -/
private theorem length_frames_le (E : List Bool) : (frames E).length ≤ E.length := by
  by_cases hE : E = []
  · simp [hE]
  · rw [frames_of_ne_nil hE, List.length_cons]
    have := length_frames_le (dropFrame E)
    have := length_dropFrame_lt hE
    omega
termination_by E.length
decreasing_by exact length_dropFrame_lt hE

/-! ### The cost of the verifier -/

section Cost

variable {α : Type} {enc : α ↪ List Bool}

/-- The encoding of the inputs of a `Σ₂TIME` verifier. -/
private abbrev eV (enc : α ↪ List Bool) : α × (List Bool × List Bool) ↪ List Bool :=
  encPair enc (encPair encBits encBits)

/-- Linear time and space in the encoded input of the verifier. -/
private abbrev Lin (enc : α ↪ List Bool) {β : Type} (f : α × (List Bool × List Bool) → β)
    (e : β ↪ List Bool) : Prop :=
  ComputableInO f (eV enc) e (fun x => (eV enc x).length) (fun x => (eV enc x).length)

private theorem lin_comp {β γ : Type} {eβ : β ↪ List Bool} {eγ : γ ↪ List Bool} {f : β → γ}
    {g : α × (List Bool × List Bool) → β}
    (hf : ComputableInO f eβ eγ (fun b => (eβ b).length) (fun b => (eβ b).length))
    (hg : Lin enc g eβ) : Lin enc (fun x => f (g x)) eγ :=
  hf.comp_linear hg

private theorem lin_pair {β₁ β₂ γ : Type} {e₁ : β₁ ↪ List Bool} {e₂ : β₂ ↪ List Bool}
    {eγ : γ ↪ List Bool} {f : β₁ × β₂ → γ} {g₁ : α × (List Bool × List Bool) → β₁}
    {g₂ : α × (List Bool × List Bool) → β₂}
    (hf : ComputableInO f (encPair e₁ e₂) eγ (fun b => (encPair e₁ e₂ b).length)
      (fun b => (encPair e₁ e₂ b).length))
    (h₁ : Lin enc g₁ e₁) (h₂ : Lin enc g₂ e₂) : Lin enc (fun x => f (g₁ x, g₂ x)) eγ :=
  hf.comp_linear ((h₁.prod h₂).mono 2 (fun _ => by omega) fun _ => by omega)

/-- Equality of two computed words of length at most two, in linear time. -/
private theorem lin_eq_short {g₁ g₂ : α × (List Bool × List Bool) → List Bool}
    (h₁ : Lin enc g₁ encBits) (h₂ : Lin enc g₂ encBits) (hl₁ : ∀ x, (g₁ x).length ≤ 2)
    (hl₂ : ∀ x, (g₂ x).length ≤ 2) : Lin enc (fun x => decide (g₁ x = g₂ x)) encBool := by
  refine (ComputableInO.eq' h₁ h₂).mono 16 (fun x => ?_) fun x => ?_
  · have := hl₁ x
    have := hl₂ x
    simp only [encBits_apply]
    nlinarith
  · have := hl₁ x
    have := hl₂ x
    simp only [length_encPair, encBits_apply]
    omega

/-- The verifier is linear, given linear replays `rF` and `rG` and a linear parameter. -/
private theorem chainCheck_inO {rF rG : List Bool × List Bool → List Bool} {Pb : α → List Bool}
    (w₀ : List Bool)
    (hrF : ComputableInO rF (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length) (fun p => (encPair encBits encBits p).length))
    (hrG : ComputableInO rG (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length) (fun p => (encPair encBits encBits p).length))
    (hPb : ComputableInO Pb enc encBits (fun a => (enc a).length) (fun a => (enc a).length)) :
    Lin enc (fun x => chainCheck rF rG (Pb x.1) w₀ x.2.1 x.2.2) encBool := by
  -- the parts of the input
  have hid : Lin enc (fun x => x) (eV enc) := ComputableInO.of_eq fun _ => rfl
  have hu : Lin enc (fun x => x.2.1) encBits :=
    (ComputableInO.fst encBits encBits).comp_linear (ComputableInO.snd enc _)
  have hv : Lin enc (fun x => x.2.2) encBits :=
    (ComputableInO.snd encBits encBits).comp_linear (ComputableInO.snd enc _)
  have hpb : Lin enc (fun x => Pb x.1) encBits :=
    (hPb.comp (ComputableInO.fst enc (encPair encBits encBits))).mono 2
      (fun x => by
        have := length_le_encPair_left enc (encPair encBits encBits) x; dsimp only [eV]; omega)
      (fun x => by
        have := length_le_encPair_left enc (encPair encBits encBits) x; dsimp only [eV]; omega)
  -- linear primitives on words
  have hunframe : ComputableInO unframe encBits encBits (fun w => (encBits w).length)
      (fun w => (encBits w).length) := ComputableInO.of_linear (.of_unframe fun _ => rfl)
  have hdrop : ComputableInO dropFrame encBits encBits (fun w => (encBits w).length)
      (fun w => (encBits w).length) := ComputableInO.of_linear (.of_dropFrame fun _ => rfl)
  have hframes := computableInDegree_frames.inO_one
  -- the guessed words from the chosen index on
  have hws : Lin enc (fun x => w₀ :: frames (unframe (dropFrame x.2.1))) (encList encBits) :=
    lin_pair (ComputableInO.cons' (enc := encBits)) (ComputableInO.const w₀)
      (lin_comp hframes (lin_comp hunframe (lin_comp hdrop hu)))
  have hi : Lin enc (fun x => leadingTrues x.2.2) encUnary := lin_comp leadingTrues_inO hv
  have hR : Lin enc (fun x => cvRest w₀ x.2.1 x.2.2) (encList encBits) :=
    lin_pair (ComputableInDegree.dropUnary encBits).inO_one hws hi
  have hj : Lin enc (fun x => cvPos x.2.2) encUnary :=
    lin_comp (g := fun x => x.2.2.drop (leadingTrues x.2.2 + 1)) leadingTrues_inO
      (lin_pair (g₁ := fun x => x.2.2) (g₂ := fun x => leadingTrues x.2.2 + 1)
        ComputableInDegree.bitsDrop.inO_one hv
        (lin_comp (g := fun x => leadingTrues x.2.2) ComputableInO.unarySucc' hi))
  have hw : Lin enc (fun x => (cvRest w₀ x.2.1 x.2.2).headD []) encBits :=
    lin_comp (ComputableInO.headD' (enc := encBits) []) hR
  have htail : Lin enc (fun x => (cvRest w₀ x.2.1 x.2.2).tail) (encList encBits) :=
    lin_comp (ComputableInO.tail' (enc := encBits)) hR
  have hw' : Lin enc (fun x => (cvRest w₀ x.2.1 x.2.2).tail.headD []) encBits :=
    lin_comp (ComputableInO.headD' (enc := encBits) []) htail
  have hbw : Lin enc (fun x => unframe x.2.1) encBits := lin_comp hunframe hu
  have he0 : Lin enc (fun x => (cvRest w₀ x.2.1 x.2.2).isEmpty) encBool :=
    lin_comp (ComputableInDegree.listIsEmpty encBits).inO_one hR
  have he1 : Lin enc (fun x => (cvRest w₀ x.2.1 x.2.2).tail.isEmpty) encBool :=
    lin_comp (ComputableInDegree.listIsEmpty encBits).inO_one htail
  -- the replay of the step and the comparison at the chosen position
  have hinF : Lin enc (fun x => frame (Pb x.1) ++ (frame ((cvRest w₀ x.2.1 x.2.2).headD []) ++
      unframe x.2.1)) encBits :=
    ((lin_pair (ComputableInO.of_eq (f := fun p : List Bool × (List Bool × List Bool) => p)
      (encIn := encPair encBits (encPair encBits encBits)) fun _ => rfl) hpb
      (lin_pair (ComputableInO.of_eq (f := fun p : List Bool × List Bool => p)
        (encIn := encPair encBits encBits) fun _ => rfl) hw hbw))).of_enc_eq fun _ => rfl
  have hrFx : Lin enc (fun x => rF (x.2.1, frame (Pb x.1) ++
      (frame ((cvRest w₀ x.2.1 x.2.2).headD []) ++ unframe x.2.1))) encBits :=
    lin_pair hrF hu hinF
  have hlhs : Lin enc (fun x => ((rF (x.2.1, frame (Pb x.1) ++
      (frame ((cvRest w₀ x.2.1 x.2.2).headD []) ++ unframe x.2.1))).drop (cvPos x.2.2)).take 1)
      encBits :=
    lin_pair ComputableInDegree.bitsTake.inO_one
      (lin_pair ComputableInDegree.bitsDrop.inO_one hrFx hj) (ComputableInO.const 1)
  have hQ : Lin enc (fun x => frame ((cvRest w₀ x.2.1 x.2.2).tail.headD []) ++ [true]) encBits :=
    (lin_pair (ComputableInO.of_eq (f := fun p : List Bool × Bool => p)
      (encIn := encPair encBits encBool) fun _ => rfl) hw' (ComputableInO.const true)).of_enc_eq
      fun _ => rfl
  have hrhs : Lin enc (fun x => ((frame ((cvRest w₀ x.2.1 x.2.2).tail.headD []) ++ [true]).drop
      (cvPos x.2.2)).take 1) encBits :=
    lin_pair ComputableInDegree.bitsTake.inO_one
      (lin_pair ComputableInDegree.bitsDrop.inO_one hQ hj) (ComputableInO.const 1)
  have htc := lin_eq_short hlhs hrhs (fun _ => by simp) (fun _ => by simp)
  -- the replay of the goal test
  have hinG : Lin enc (fun x => frame (Pb x.1) ++ (cvRest w₀ x.2.1 x.2.2).headD []) encBits :=
    (lin_pair (ComputableInO.of_eq (f := fun p : List Bool × List Bool => p)
      (encIn := encPair encBits encBits) fun _ => rfl) hpb hw).of_enc_eq fun _ => rfl
  have hg2 : Lin enc (fun x => (rG (x.2.1, frame (Pb x.1) ++
      (cvRest w₀ x.2.1 x.2.2).headD [])).take 2) encBits :=
    lin_pair ComputableInDegree.bitsTake.inO_one (lin_pair hrG hu hinG) (ComputableInO.const 2)
  have hgc := lin_eq_short hg2 (ComputableInO.const [true]) (fun _ => by simp) (fun _ => by simp)
  -- the verdict
  exact ((he0.or' (he1.and' hgc)).or' (he1.not'.and' htc)).mono 5 (fun _ => by omega)
    fun _ => by omega

end Cost

/-! ### Chains in `Σ₂TIME` -/

/-- The words of an honest chain from index `i` on. -/
private theorem drop_map_range_eq_cons {β : Type} {f : ℕ → β} {m i : ℕ} {w : β} {r : List β}
    (h : ((List.range (m + 1)).map f).drop i = w :: r) :
    i < m + 1 ∧ w = f i ∧ r = ((List.range (m + 1)).map f).drop (i + 1) := by
  have hi : i < m + 1 := by
    by_contra hi
    rw [List.drop_eq_nil_of_le (by simp; omega)] at h
    exact List.cons_ne_nil _ _ h.symm
  rw [List.drop_eq_getElem_cons (by simpa using hi), List.cons.injEq] at h
  exact ⟨hi, by simpa using h.1.symm, h.2.symm⟩

/-- A bound `X ≤ D * T + D` on a cost, scaled by a constant, is below a threshold
`c * T + c ≤ L` with `e * (D + 1) ≤ c`. -/
private theorem mul_succ_le_of_le {e X D T c L : ℕ} (hX : X ≤ D * T + D) (he : e * (D + 1) ≤ c)
    (hL : c * T + c ≤ L) : e * (X + 1) ≤ L :=
  calc e * (X + 1) ≤ e * ((D + 1) * (T + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = e * (D + 1) * (T + 1) := (Nat.mul_assoc _ _ _).symm
    _ ≤ c * (T + 1) := Nat.mul_le_mul_right _ he
    _ ≤ L := by rw [Nat.mul_succ]; exact hL

variable {α : Type} {enc : α ↪ List Bool}

/-- **Chains of iterates are in `Σ₂TIME`.** Let `next` be computable within time `Tn` and `goal`
within time `Tg`, on encoded triples `(p, s, bw)` and pairs `(p, s)`, and let `P` be linear. If
`a ∈ A` exactly when, for some parameter `bw` and some `m`, the `m`-th iterate `s_m` of
`s ↦ next (P a, s, bw)` from `s₀` satisfies `goal (P a, s_m)`, and for `a ∈ A` such a chain exists
whose steps, test and encoded iterates `s₁, …, s_m` (with `bw`) all cost `O(t n)`, then `A` is in
`Σ₂TIME(t)`. Soundness needs no cost bound: dishonest certificates are rejected however long the
honest computation would be. -/
theorem mem_SigmaTwoTIME_of_chain {π σ : Type} {eP : π ↪ List Bool} {eS : σ ↪ List Bool}
    {A : Set α} {t : ℕ → ℕ} {P : α → π} {s₀ : σ} {next : π × (σ × List Bool) → σ}
    {goal : π × σ → Bool} {Tn Sn : π × (σ × List Bool) → ℕ} {Tg Sg : π × σ → ℕ}
    (hP : ComputableInO P enc eP (fun a => (enc a).length) (fun a => (enc a).length))
    (hnext : ComputableInO (fun x => (next x, true)) (encPair eP (encPair eS encBits))
      (encPair eS encBool) Tn Sn)
    (hgoal : ComputableInO goal (encPair eP eS) encBool Tg Sg)
    (hsound : ∀ a bw m, goal (P a, (fun s => next (P a, (s, bw)))^[m] s₀) = true → a ∈ A)
    (hcomplete : ∃ D, ∀ a ∈ A, ∃ bw m,
      goal (P a, (fun s => next (P a, (s, bw)))^[m] s₀) = true ∧
      (∀ i < m, Tn (P a, ((fun s => next (P a, (s, bw)))^[i] s₀, bw)) ≤
        D * t (enc a).length + D) ∧
      Tg (P a, (fun s => next (P a, (s, bw)))^[m] s₀) ≤ D * t (enc a).length + D ∧
      (encPair encBits (encList eS) (bw, (List.range m).map
        fun i => (fun s => next (P a, (s, bw)))^[i + 1] s₀)).length ≤
        D * t (enc a).length + D) :
    A ∈ SigmaTwoTIME enc t := by
  obtain ⟨D, hcomplete⟩ := hcomplete
  obtain ⟨cF, ⟨kF, QF, hQF, MF, hMF⟩, -⟩ := hnext
  obtain ⟨cG, ⟨kG, QG, hQG, MG, hMG⟩, -⟩ := hgoal
  -- the replays, linear in the clock and the input
  let rF : List Bool × List Bool → List Bool := fun p =>
    (MultiTapePTM.ofDeterministic MF).runClosedCoins p.1 p.2
  let rG : List Bool × List Bool → List Bool := fun p =>
    (MultiTapePTM.ofDeterministic MG).runClosedCoins p.1 p.2
  have hrF : ComputableInO rF (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length) (fun p => (encPair encBits encBits p).length) :=
    (MultiTapePTM.computableInDegree_runClosedCoins (MultiTapePTM.ofDeterministic MF)).inO_one
  have hrG : ComputableInO rG (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length) (fun p => (encPair encBits encBits p).length) :=
    (MultiTapePTM.computableInDegree_runClosedCoins (MultiTapePTM.ofDeterministic MG)).inO_one
  -- a replay writes a prefix of the value, and all of it once the clock is long enough
  have hpreF (u : List Bool) (x : π × (σ × List Bool)) :
      rF (u, encPair eP (encPair eS encBits) x) <+: encPair eS encBool (next x, true) := by
    simp only [rF, MultiTapePTM.runClosedCoins_ofDeterministic]
    exact (hMF x).output_runFrom_prefix _
  have heqF (u : List Bool) (x : π × (σ × List Bool)) (hu : cF * (Tn x + 1) ≤ u.length) :
      rF (u, encPair eP (encPair eS encBits) x) = encPair eS encBool (next x, true) := by
    simp only [rF, MultiTapePTM.runClosedCoins_ofDeterministic]
    exact ((hMF x).runFrom_of_le hu).2
  have hpreG (u : List Bool) (x : π × σ) :
      rG (u, encPair eP eS x) <+: encBool (goal x) := by
    simp only [rG, MultiTapePTM.runClosedCoins_ofDeterministic]
    exact (hMG x).output_runFrom_prefix _
  have heqG (u : List Bool) (x : π × σ) (hu : cG * (Tg x + 1) ≤ u.length) :
      rG (u, encPair eP eS x) = encBool (goal x) := by
    simp only [rG, MultiTapePTM.runClosedCoins_ofDeterministic]
    exact ((hMG x).runFrom_of_le hu).2
  refine mem_SigmaTwoTIME_iff.mpr ⟨fun x => chainCheck rF rG (eP (P x.1)) (eS s₀) x.2.1 x.2.2,
    2 * D + 8 + cF * (D + 1) + cG * (D + 1),
    chainCheck_inO (eS s₀) hrF hrG (Pb := fun a => eP (P a)) (hP.of_enc_eq fun _ => rfl),
    fun a L hL => ?_⟩
  have h8 : 8 ≤ L := by omega
  have hL2 : 2 * (D * t (enc a).length + D) + 2 ≤ L := by
    have := mul_succ_le_of_le (e := 2) (X := D * t (enc a).length + D) le_rfl (by omega) hL
    omega
  have hLF {X : ℕ} (hX : X ≤ D * t (enc a).length + D) : cF * (X + 1) ≤ L :=
    mul_succ_le_of_le hX (by omega) hL
  have hLG {X : ℕ} (hX : X ≤ D * t (enc a).length + D) : cG * (X + 1) ≤ L :=
    mul_succ_le_of_le hX (by omega) hL
  constructor
  · -- completeness: the honest chain, padded
    intro ha
    obtain ⟨bw, m, hgoalm, hTn, hTg, hpre⟩ := hcomplete a ha
    set step := fun s => next (P a, (s, bw)) with hstep
    set l := (List.range m).map fun i => step^[i + 1] s₀ with hl
    simp only [length_encPair, encBits_apply] at hpre
    set u := frame bw ++ (frame (encList eS l) ++
      List.replicate (L - (2 * bw.length + 2 * (encList eS l).length + 2)) false) with hu_def
    have hlen : u.length = L := by
      simp only [hu_def, List.length_append, length_frame, List.length_replicate]
      omega
    have hu₁ : unframe u = bw := unframe_frame_append _ _
    have hws : eS s₀ :: frames (unframe (dropFrame u)) =
        (List.range (m + 1)).map fun i => eS (step^[i] s₀) := by
      rw [hu_def, dropFrame_frame_append, unframe_frame_append, frames_encList, hl, List.map_map,
        List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl
    refine ⟨u, hlen, fun v hv => ?_⟩
    change chainCheck rF rG (eP (P a)) (eS s₀) u v = true
    rcases hR : cvRest (eS s₀) u v with _ | ⟨w, _ | ⟨w', r⟩⟩
    · exact chainCheck_nil hR
    · have hR' := hR
      rw [cvRest, hws] at hR'
      obtain ⟨hi, hw, hr⟩ := drop_map_range_eq_cons hR'
      have him : leadingTrues v = m := by
        by_contra hne
        rw [List.drop_eq_getElem_cons (by simp; omega)] at hr
        exact List.cons_ne_nil _ _ hr.symm
      have hg := heqG u (P a, step^[m] s₀) (hlen ▸ hLG hTg)
      simp only [encPair_apply, encBool_apply, hgoalm] at hg
      rw [chainCheck_single hR, hw, him, hg]
      rfl
    · have hR' := hR
      rw [cvRest, hws] at hR'
      obtain ⟨hi, hw, hr⟩ := drop_map_range_eq_cons hR'
      obtain ⟨hi', hw', -⟩ := drop_map_range_eq_cons hr.symm
      rw [chainCheck_cons_cons hR, hu₁, hw, hw']
      have hx := heqF u (P a, (step^[leadingTrues v] s₀, bw))
        (hlen ▸ hLF (hTn _ (by omega)))
      have hnext' : next (P a, (step^[leadingTrues v] s₀, bw)) =
          step^[leadingTrues v + 1] s₀ := by
        rw [Function.iterate_succ_apply']
      rw [hnext'] at hx
      simp only [encPair_apply, encBits_apply, encBool_apply] at hx
      rw [hx]
      simp
  · -- soundness: the guessed words are the iterates, by induction
    rintro ⟨u, hu, hV⟩
    set bw := unframe u with hbw
    set E := unframe (dropFrame u) with hE
    set step := fun s => next (P a, (s, bw)) with hstep
    have hEL : 2 * E.length ≤ L := by
      have h₁ := length_unframe_add_dropFrame_le (dropFrame u)
      have h₂ := length_dropFrame_le u
      rw [← hE] at h₁
      omega
    have hchain : ∀ k ≤ (frames E).length,
        (eS s₀ :: frames E).drop k = eS (step^[k] s₀) :: (frames E).drop k := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have ihk := ih (by omega)
        obtain ⟨w', r, hwr⟩ : ∃ w' r, (frames E).drop k = w' :: r :=
          ⟨_, _, List.drop_eq_getElem_cons (by omega)⟩
        rw [hwr] at ihk
        have hbound := add_two_mul_length_le_of_drop_frames hwr
        -- the replay at index `k` agrees with `w'` at every position
        have hpos : ∀ j ≤ (frame w' ++ [true]).length,
            ((rF (u, frame (eP (P a)) ++ (frame (eS (step^[k] s₀)) ++ bw))).drop j).take 1 =
              ((frame w' ++ [true]).drop j).take 1 := by
          intro j hj
          simp only [List.length_append, length_frame, List.length_singleton] at hj
          have hpick : k + j + 2 ≤ L := by omega
          have hR : cvRest (eS s₀) u (pick k j L) = eS (step^[k] s₀) :: w' :: r := by
            rw [cvRest, leadingTrues_pick]
            exact ihk
          have := hV (pick k j L) (length_pick hpick)
          dsimp only at this
          rw [chainCheck_cons_cons hR, cvPos_pick, decide_eq_true_iff] at this
          exact this
        have hP' := eq_of_forall_take_drop hpos
        have hpre := hpreF u (P a, (step^[k] s₀, bw))
        simp only [encPair_apply, encBits_apply, encBool_apply] at hpre
        rw [hP'] at hpre
        have hw' : w' = eS (step^[k + 1] s₀) := by
          rw [eq_of_frame_prefix hpre, Function.iterate_succ_apply']
        rw [← List.tail_drop, ihk, List.tail_cons, hw', ← List.tail_drop, hwr, List.tail_cons]
    set m := (frames E).length with hm
    have hR : cvRest (eS s₀) u (pick m 0 L) = [eS (step^[m] s₀)] := by
      rw [cvRest, leadingTrues_pick, hchain m le_rfl, List.drop_length]
    have hmE := length_frames_le E
    have := hV (pick m 0 L) (length_pick (by omega))
    dsimp only at this
    rw [chainCheck_single hR, decide_eq_true_iff] at this
    have hpre := hpreG u (P a, step^[m] s₀)
    simp only [encPair_apply, encBool_apply] at hpre
    rw [List.take_of_length_le (hpre.length_le.trans (by simp))] at this
    rw [this] at hpre
    obtain ⟨r, hr⟩ := hpre
    simp only [List.singleton_append, List.cons.injEq] at hr
    exact hsound a bw m hr.1.symm

end Cslib.Complexity

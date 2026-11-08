/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.TwoProverGame
public import Complexity.Probability.ProductConditioning.SideInformation
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Filter
import Complexity.Probability.PMF.Map
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Product.Split

/-!
# The coordinate model of Holenstein's embedding lemma

Holenstein's proof of Lemma 6.4 [Holenstein, Lemma 6.4][Holenstein2009] conditions the questions
of the `n`-fold repetition of a game `G` on the event `W_C` that strategies `ha` and `hb` win every
coordinate in a set `C`, and studies the *free* coordinates `j ∉ C`. Holenstein takes
`C = {k + 1, …, n}`; here `C` is any `Finset (Fin n)`, which removes the relabeling of coordinates
in his proof of Lemma 6.5. The proof adds a uniform bit `D_j` for each free coordinate and reveals
one half of the question pair there: Bob's question `y_j` when `D_j = 0`, Alice's question `x_j`
otherwise. This file builds that model on one finite sample space and identifies its laws.

* **The sample space** `Sample X Y C` holds the bits on the free coordinates and a question pair for
  each of the `n` coordinates. Its law `sampleLaw` draws the bits uniformly and the pairs
  independently from `G.questions`; `condLaw` conditions it on `W_C` (`winsOnSample`). Every law in
  the proof of Lemma 6.4 is the image of `condLaw` under a variable of the model.
* **The variables** of [Holenstein, (6.3)–(6.4)][Holenstein2009]. `T` is `revealed`, a `Revealed`:
  the questions on `C`, and at each free coordinate the revealed half as one value of `X ⊕ Y`,
  whose tag is the bit (`Revealed.bit`, with `false` for `D_j = 0`). `V` is `answers`, the answers
  on `C` only, so `|V| = (|A| |B|)^{#C}`. `U` is the tuple of question pairs on the free
  coordinates. Holenstein's `U_j` is only the hidden half of the pair at `j`; here it is the whole
  pair, which carries the same information once the revealed half in `T` is known. `S` of (6.11) is
  `shared j`, a `Shared`: `T` without its half at `j`, and `V`.
* **The identifications.** The law of `((T, V), U)` is `sideJoint` of the law of `T` and
  `sideKernel` (`map_sampleLaw_eq_sideJoint`): given `T`, the free pairs are independent and the
  pair at `i` is drawn from `pairGiven G` of its revealed half (`map_fst_sideKernel`), which is the
  hypothesis of Holenstein's Corollary 4.3. Under `W_C`, the question tuples have the law of the
  questions of `G.pow n` conditioned on `W_C` (`map_condLaw_questions`), the law in the strategy
  extraction `TwoProverGame.winProbOn_insert_le`. The bits stay uniform and independent of the
  questions (`condLaw_eq_bind`), so `Pr[D_j = b | W_C] = 1 / 2` (`toOuterMeasure_condLaw_bit`), and
  conditioning on `D_j = b` does not change the law of a variable that ignores `D_j`, such as `S`
  (`map_filter_condLaw_bit`).
* **Holenstein's (6.5)** (`sum_dist_condLaw_le`) is Corollary 4.3 (`sum_dist_filter_sideJoint_le`)
  for this model with the event `W_C`. It is stated in nats with the factor `1 / 2` of Pinsker's
  inequality, where Holenstein's `ε_Tot` of (6.6) is in bits.

## Main definitions

* `Cslib.PCP.ParallelRepetition.reveal`, `Cslib.PCP.ParallelRepetition.revealLaw`,
  `Cslib.PCP.ParallelRepetition.pairGiven`: one coordinate, its revealed half and the pair given
  that half.
* `Cslib.PCP.ParallelRepetition.Sample`, `Cslib.PCP.ParallelRepetition.sampleLaw`,
  `Cslib.PCP.ParallelRepetition.winsOnPairs`, `Cslib.PCP.ParallelRepetition.winsOnSample`,
  `Cslib.PCP.ParallelRepetition.condLaw`: the sample space, its law, the event `W_C` and the
  conditioned law.
* `Cslib.PCP.ParallelRepetition.Revealed`, `Cslib.PCP.ParallelRepetition.revealed`,
  `Cslib.PCP.ParallelRepetition.answers`, `Cslib.PCP.ParallelRepetition.Shared`,
  `Cslib.PCP.ParallelRepetition.shared`: the variables `T`, `V` and `S`.
* `Cslib.PCP.ParallelRepetition.sideKernel`: the kernel of Corollary 4.3 for this model.

## Main results

* `Cslib.PCP.ParallelRepetition.bind_reveal_pair`: one coordinate, revealed half first.
* `Cslib.PCP.ParallelRepetition.map_sampleLaw_revealed_pairs`,
  `Cslib.PCP.ParallelRepetition.map_sampleLaw_eq_sideJoint`: the model is an instance of
  Corollary 4.3.
* `Cslib.PCP.ParallelRepetition.map_sampleLaw_questions`,
  `Cslib.PCP.ParallelRepetition.map_condLaw_questions`: the recombined questions.
* `Cslib.PCP.ParallelRepetition.condLaw_eq_bind`,
  `Cslib.PCP.ParallelRepetition.toOuterMeasure_condLaw_bit`,
  `Cslib.PCP.ParallelRepetition.map_filter_condLaw_bit`: the bits under `W_C`.
* `Cslib.PCP.ParallelRepetition.sum_dist_condLaw_le`: Holenstein's (6.5).

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.PCP.ParallelRepetition

open Finset
open Cslib.Probability.PMF (pi conditionalSnd sideJoint uniformOfFintype)
open scoped Cslib.Probability.PMF

variable {X Y A B : Type*}

/-! ### One coordinate -/

/-- The half of a question pair `(x, y)` revealed by the bit `d`: Alice's question `inl x` when
`d` is `true`, Bob's question `inr y` when `d` is `false`. -/
def reveal (d : Bool) (q : X × Y) : X ⊕ Y :=
  bif d then .inl q.1 else .inr q.2

@[simp] theorem reveal_true (q : X × Y) : reveal true q = .inl q.1 := rfl

@[simp] theorem reveal_false (q : X × Y) : reveal false q = .inr q.2 := rfl

/-- The tag of the revealed half is the bit. -/
@[simp] theorem isLeft_reveal (d : Bool) (q : X × Y) : (reveal d q).isLeft = d := by
  cases d <;> rfl

variable (G : TwoProverGame X Y A B)

/-- The law of the revealed half of a question pair of `G`, for a uniform bit. -/
noncomputable def revealLaw : PMF (X ⊕ Y) :=
  (uniformOfFintype Bool).bind fun d => G.questions.map (reveal d)

/-- The law of the question pair of `G` given its revealed half: given Alice's question `x`, Bob's
question is drawn from `P_{Y | X = x}`; given Bob's question `y`, Alice's is drawn from
`P_{X | Y = y}`. -/
noncomputable def pairGiven : X ⊕ Y → PMF (X × Y)
  | .inl x => (conditionalSnd G.questions x).map (x, ·)
  | .inr y => (conditionalSnd (G.questions.map Prod.swap) y).map (·, y)

/-- Drawing Alice's question and then the pair given it is drawing the pair:
`P_X P_{Y | X} = P_{XY}`. -/
theorem bind_pairGiven_inl :
    (G.questions.map Prod.fst).bind (fun x => pairGiven G (.inl x)) = G.questions :=
  Cslib.Probability.PMF.bind_conditionalSnd G.questions

/-- Drawing Bob's question and then the pair given it is drawing the pair:
`P_Y P_{X | Y} = P_{XY}`. -/
theorem bind_pairGiven_inr :
    (G.questions.map Prod.snd).bind (fun y => pairGiven G (.inr y)) = G.questions := by
  have h := congrArg (PMF.map Prod.swap)
    (Cslib.Probability.PMF.bind_conditionalSnd (G.questions.map Prod.swap))
  rw [PMF.map_bind, PMF.map_comp, PMF.map_comp, Prod.swap_swap_eq, PMF.map_id] at h
  simp only [PMF.map_comp, Function.comp_def, Prod.swap_prod_mk] at h
  exact h

/-- Drawing a uniform bit and a question pair, and revealing one half, is drawing the revealed
half and then the pair given that half. -/
theorem bind_reveal_pair :
    ((uniformOfFintype Bool).bind fun d => G.questions.map fun q => (reveal d q, q)) =
      (revealLaw G).bind fun r => (pairGiven G r).map (r, ·) := by
  have hd : ∀ d, G.questions.map (fun q => (reveal d q, q)) =
      (G.questions.map (reveal d)).bind fun r => (pairGiven G r).map (r, ·) := by
    intro d
    cases d
    · have h1 : G.questions.map (reveal false) =
          ((G.questions.map Prod.swap).map Prod.fst).map Sum.inr := by
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      rw [h1, PMF.bind_map]
      conv_lhs => rw [← PMF.map_id G.questions, ← Prod.swap_swap_eq, ← PMF.map_comp,
        ← Cslib.Probability.PMF.bind_conditionalSnd (G.questions.map Prod.swap)]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, reveal, Bool.cond_false, pairGiven,
        Prod.swap_prod_mk]
    · have h1 : G.questions.map (reveal true) = (G.questions.map Prod.fst).map Sum.inl := by
        rw [PMF.map_comp]
        rfl
      rw [h1, PMF.bind_map]
      conv_lhs => rw [← Cslib.Probability.PMF.bind_conditionalSnd G.questions]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, reveal, Bool.cond_true, pairGiven]
  simp only [hd, revealLaw, PMF.bind_bind]

/-! ### The sample space -/

/-- The variable `T` of [Holenstein, (6.3)][Holenstein2009]: the questions on the coordinates in
`C`, and on each free coordinate `i ∉ C` the half of the question pair revealed by the bit `D_i`.
The tag of the half records `D_i` (`Revealed.bit`). -/
structure Revealed (X Y : Type*) {n : ℕ} (C : Finset (Fin n)) where
  /-- The question pairs on the coordinates in `C`. -/
  questions : C → X × Y
  /-- On each free coordinate, Alice's question `inl x` (bit `true`) or Bob's `inr y` (bit
  `false`). -/
  halves : {i // i ∉ C} → X ⊕ Y
  deriving Fintype

/-- The variable `S = (T^{(\j)}, V)` of [Holenstein, (6.8) and (6.11)][Holenstein2009] for a free
coordinate `j`: the variable `T` without the revealed half at `j`, and the answers on `C`. -/
structure Shared (X Y A B : Type*) {n : ℕ} (C : Finset (Fin n)) (j : {i // i ∉ C}) where
  /-- The question pairs on the coordinates in `C`. -/
  questions : C → X × Y
  /-- The revealed halves on the free coordinates other than `j`. -/
  halves : {i : {i // i ∉ C} // i ≠ j} → X ⊕ Y
  /-- The answers on the coordinates in `C`. -/
  answers : C → A × B
  deriving Fintype

/-- The sample space of the coordinate model: a bit `D_i` for each free coordinate `i ∉ C`, and a
question pair for each of the `n` coordinates. -/
abbrev Sample (X Y : Type*) {n : ℕ} (C : Finset (Fin n)) :=
  ({i // i ∉ C} → Bool) × (Fin n → X × Y)

section Model

variable {n : ℕ} {C : Finset (Fin n)}

/-- The bit `D_j` recorded in the tag of the revealed half at a free coordinate `j`. -/
def Revealed.bit (t : Revealed X Y C) (j : {i // i ∉ C}) : Bool :=
  (t.halves j).isLeft

/-- The question pairs with those of `t` on `C` and `u` on the free coordinates. -/
def Revealed.combine (t : Revealed X Y C) (u : {i // i ∉ C} → X × Y) : Fin n → X × Y :=
  (Equiv.piEquivPiSubtypeProd (· ∈ C) fun _ => X × Y).symm (t.questions, u)

/-- Forget the revealed half at `j`, and add the answers. -/
def Shared.ofRevealed (j : {i // i ∉ C}) (t : Revealed X Y C) (v : C → A × B) :
    Shared X Y A B C j :=
  ⟨t.questions, fun i => t.halves i, v⟩

variable (C) in
/-- The variable `T` of [Holenstein, (6.3)][Holenstein2009] on the sample space. -/
def revealed : Sample X Y C → Revealed X Y C :=
  fun (d, q) => ⟨fun i => q i, fun i => reveal (d i) (q i)⟩

variable (C) in
/-- The answers on `C` of the strategies `ha` and `hb` to a tuple of question pairs: the variable
`V` of [Holenstein, (6.4)][Holenstein2009]. -/
def answers (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B)
    (q : Fin n → X × Y) : C → A × B :=
  fun i => (ha (Prod.fst ∘ q) i, hb (Prod.snd ∘ q) i)

/-- The variable `S = (T^{(\j)}, V)` of [Holenstein, (6.11)][Holenstein2009] on the sample
space. -/
def shared (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B) (j : {i // i ∉ C})
    (ω : Sample X Y C) : Shared X Y A B C j :=
  .ofRevealed j (revealed C ω) (answers C ha hb ω.2)

/-- The bit of the revealed half is the bit of the sample. -/
@[simp] theorem bit_revealed (ω : Sample X Y C) (j : {i // i ∉ C}) :
    (revealed C ω).bit j = ω.1 j :=
  isLeft_reveal _ _

/-- Recombining the revealed questions with the free question pairs recovers the sample's
question pairs. -/
@[simp] theorem combine_revealed (ω : Sample X Y C) :
    (revealed C ω).combine (fun i => ω.2 i) = ω.2 :=
  (Equiv.piEquivPiSubtypeProd (· ∈ C) fun _ => X × Y).symm_apply_apply ω.2

/-- The variable `S` ignores the bit at `j`. -/
@[simp] theorem shared_update (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B)
    (j : {i // i ∉ C}) (d : {i // i ∉ C} → Bool) (b : Bool) (q : Fin n → X × Y) :
    shared ha hb j (Function.update d j b, q) = shared ha hb j (d, q) := by
  simp only [shared, revealed, Shared.ofRevealed, Shared.mk.injEq, true_and, and_true]
  funext i
  rw [Function.update_of_ne i.2]

end Model

/-! ### The event `W_C` -/

section Wins

variable {n : ℕ} (C : Finset (Fin n)) (ha : (Fin n → X) → Fin n → A)
  (hb : (Fin n → Y) → Fin n → B)

/-- The event `W_C` [Holenstein, Definition 2.4][Holenstein2009] on tuples of question pairs: the
strategies `ha` and `hb` win every coordinate in `C`. -/
def winsOnPairs : Set (Fin n → X × Y) :=
  (fun q => (Prod.fst ∘ q, Prod.snd ∘ q)) ⁻¹' G.winsOn ha hb C

/-- The event `W_C` on the sample space. -/
def winsOnSample : Set (Sample X Y C) :=
  Prod.snd ⁻¹' winsOnPairs G C ha hb

variable [Finite X] [Finite Y]

/-- The event `W_C` has the same probability under independent question pairs as under the
repetition. -/
theorem toOuterMeasure_pi_winsOnPairs :
    ((pi fun _ : Fin n => G.questions).toOuterMeasure (winsOnPairs G C ha hb)).toReal =
      G.winProbOn ha hb C := by
  rw [TwoProverGame.winProbOn, TwoProverGame.pow, PMF.toOuterMeasure_map_apply]
  rfl

variable {G C ha hb} in
/-- A possible question of the repetition that wins `C` gives a possible tuple of question pairs
that wins `C`. -/
theorem exists_mem_winsOnPairs_support
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∃ q ∈ winsOnPairs G C ha hb, q ∈ (pi fun _ : Fin n => G.questions).support := by
  obtain ⟨xy, hxy, hsupp⟩ := hC
  rw [TwoProverGame.pow, PMF.mem_support_map_iff] at hsupp
  obtain ⟨q, hq, rfl⟩ := hsupp
  exact ⟨q, hxy, hq⟩

end Wins

/-! ### The laws of the model -/

section Laws

variable [Fintype X] [Fintype Y] {n : ℕ} (C : Finset (Fin n))

/-- The law of the sample space: uniform bits, and independent question pairs drawn from
`G.questions`. -/
noncomputable def sampleLaw : PMF (Sample X Y C) :=
  (uniformOfFintype ({i // i ∉ C} → Bool)).bind fun d =>
    (pi fun _ : Fin n => G.questions).map (d, ·)

/-- A sample has the uniform mass of its bits times the masses of its question pairs. -/
theorem sampleLaw_apply (d : {i // i ∉ C} → Bool) (q : Fin n → X × Y) :
    sampleLaw G C (d, q) = (2 ^ #Cᶜ)⁻¹ * ∏ i, G.questions (q i) := by
  rw [sampleLaw, Cslib.Probability.PMF.bind_map_prodMk_apply,
    Cslib.Probability.PMF.uniformOfFintype_apply, Cslib.Probability.PMF.pi_apply,
    Fintype.card_fun, Fintype.card_bool]
  simp only [← Finset.mem_compl, Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat]

/-- The question tuples of the sample have the law of the questions of the repetition. -/
theorem map_sampleLaw_questions :
    (sampleLaw G C).map (fun ω => (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2)) = (G.pow n).questions := by
  rw [sampleLaw, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, PMF.bind_const]
  rfl

/-- **The revealed questions and the free question pairs** [Holenstein, proof of
Lemma 6.4][Holenstein2009]. Given the variable `T`, the question pairs on the free coordinates are
independent, and the pair at `i` is drawn given its revealed half. -/
theorem map_sampleLaw_revealed_pairs :
    (sampleLaw G C).map (fun ω => (revealed C ω, fun i : {i // i ∉ C} => ω.2 i)) =
      ((sampleLaw G C).map (revealed C)).bind fun t =>
        (pi fun i => pairGiven G (t.halves i)).map (t, ·) := by
  classical
  -- For fixed questions `a` on `C`, the bits and the free pairs give the revealed halves and the
  -- free pairs given them, coordinate by coordinate.
  have hinner (a : C → X × Y) :
      ((uniformOfFintype ({i // i ∉ C} → Bool)).bind fun d =>
        (pi fun _ : {i // i ∉ C} => G.questions).map fun b =>
          ((⟨a, fun i => reveal (d i) (b i)⟩ : Revealed X Y C), b)) =
      (pi fun _ : {i // i ∉ C} => revealLaw G).bind fun r =>
        (pi fun i => pairGiven G (r i)).map fun b => ((⟨a, r⟩ : Revealed X Y C), b) := by
    have h1 := Cslib.Probability.PMF.pi_bind_pair (fun _ : {i // i ∉ C} => uniformOfFintype Bool)
      (fun _ _ => G.questions)
    have h2 := Cslib.Probability.PMF.pi_bind_pair (fun _ : {i // i ∉ C} => revealLaw G)
      (fun _ => pairGiven G)
    have h3 := Cslib.Probability.PMF.pi_map
      (fun _ : {i // i ∉ C} => (uniformOfFintype Bool).bind fun c => G.questions.map (c, ·))
      (fun _ cq => (reveal cq.1 cq.2, cq.2))
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, bind_reveal_pair] at h3
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype]
    calc _ = ((pi fun _ : {i // i ∉ C} => uniformOfFintype Bool).bind fun d =>
            (pi fun _ : {i // i ∉ C} => G.questions).map (d, ·)).map
          fun (d, b) => ((⟨a, fun i => reveal (d i) (b i)⟩ : Revealed X Y C), b) := by
          rw [PMF.map_bind]
          simp only [PMF.map_comp, Function.comp_def]
      _ = ((pi fun _ : {i // i ∉ C} => revealLaw G).bind fun r =>
            (pi fun i => pairGiven G (r i)).map (r, ·)).map
          fun (r, b) => ((⟨a, r⟩ : Revealed X Y C), b) := by
          rw [← h1, ← h2, h3, PMF.map_comp, PMF.map_comp, PMF.map_comp]
          rfl
      _ = _ := by
          rw [PMF.map_bind]
          simp only [PMF.map_comp, Function.comp_def]
  -- Split the question pairs into those on `C` and the free ones.
  have hsplit (d : {i // i ∉ C} → Bool) :
      (pi fun _ : Fin n => G.questions).map (fun q =>
          (revealed C (d, q), fun i : {i // i ∉ C} => q i)) =
        (pi fun _ : C => G.questions).bind fun a =>
          (pi fun _ : {i // i ∉ C} => G.questions).map fun b =>
            ((⟨a, fun i => reveal (d i) (b i)⟩ : Revealed X Y C), b) := by
    have h := congrArg (PMF.map fun (a, b) =>
        ((⟨a, fun i => reveal (d i) (b i)⟩ : Revealed X Y C), b))
      (Cslib.Probability.PMF.pi_map_piEquivPiSubtypeProd (· ∈ C) fun _ : Fin n => G.questions)
    rw [PMF.map_comp, PMF.map_bind] at h
    simp only [PMF.map_comp, Function.comp_def] at h
    convert h using 3
    rfl
  have hmain : (sampleLaw G C).map (fun ω => (revealed C ω, fun i : {i // i ∉ C} => ω.2 i)) =
      ((pi fun _ : C => G.questions).bind fun a =>
          (pi fun _ : {i // i ∉ C} => revealLaw G).map fun r => (⟨a, r⟩ : Revealed X Y C)).bind
        fun t => (pi fun i => pairGiven G (t.halves i)).map (t, ·) := by
    rw [sampleLaw, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, hsplit]
    rw [PMF.bind_comm]
    simp only [hinner, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have hT := congrArg (PMF.map Prod.fst) hmain
  rw [PMF.map_comp, Cslib.Probability.PMF.map_fst_bind_pair] at hT
  rw [show (sampleLaw G C).map (revealed C) = _ from hT]
  exact hmain

variable (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B)

/-- The joint law of the free question pairs and the answers on `C`, given the variable `T`: the
kernel `J` of Holenstein's Corollary 4.3 (`sideJoint`). -/
noncomputable def sideKernel (t : Revealed X Y C) :
    PMF (({i // i ∉ C} → X × Y) × (C → A × B)) :=
  (pi fun i => pairGiven G (t.halves i)).map fun u => (u, answers C ha hb (t.combine u))

/-- Given `T`, the free question pairs are independent: the hypothesis of Holenstein's
Corollary 4.3. -/
theorem map_fst_sideKernel (t : Revealed X Y C) :
    (sideKernel G C ha hb t).map Prod.fst = pi fun i => pairGiven G (t.halves i) := by
  rw [sideKernel, PMF.map_comp]
  exact PMF.map_id _

/-- **The coordinate model is an instance of Holenstein's Corollary 4.3** [Holenstein, proof of
Lemma 6.4][Holenstein2009]: the law of `((T, V), U)`, with `U` the free question pairs, is
`sideJoint` of the law of `T` and `sideKernel`. -/
theorem map_sampleLaw_eq_sideJoint :
    (sampleLaw G C).map (fun ω => ((revealed C ω, answers C ha hb ω.2),
        fun i : {i // i ∉ C} => ω.2 i)) =
      sideJoint ((sampleLaw G C).map (revealed C)) (sideKernel G C ha hb) := by
  have h : (fun ω : Sample X Y C => ((revealed C ω, answers C ha hb ω.2),
      fun i : {i // i ∉ C} => ω.2 i)) =
      (fun (t, u) => ((t, answers C ha hb (t.combine u)), u)) ∘
        fun ω : Sample X Y C => (revealed C ω, fun i : {i // i ∉ C} => ω.2 i) := by
    funext ω
    simp only [Function.comp_apply, combine_revealed]
  rw [h, ← PMF.map_comp, map_sampleLaw_revealed_pairs, PMF.map_bind, sideJoint]
  simp only [sideKernel, PMF.map_comp, Function.comp_def]

/-! ### Conditioning on winning `C` -/

/-- The event `W_C` has the same probability on the sample space as under the repetition. -/
theorem toOuterMeasure_sampleLaw_winsOnSample :
    ((sampleLaw G C).toOuterMeasure (winsOnSample G C ha hb)).toReal = G.winProbOn ha hb C := by
  rw [TwoProverGame.winProbOn, ← map_sampleLaw_questions, PMF.toOuterMeasure_map_apply]
  rfl

variable {G C ha hb} in
/-- A possible question of the repetition that wins `C` gives a possible sample that wins `C`. -/
theorem exists_mem_winsOnSample_support
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∃ ω ∈ winsOnSample G C ha hb, ω ∈ (sampleLaw G C).support := by
  obtain ⟨q, hq, hsupp⟩ := exists_mem_winsOnPairs_support hC
  obtain ⟨d⟩ : Nonempty ({i // i ∉ C} → Bool) := inferInstance
  refine ⟨(d, q), hq, ?_⟩
  rw [PMF.mem_support_iff, sampleLaw, Cslib.Probability.PMF.bind_map_prodMk_apply]
  exact mul_ne_zero ((PMF.mem_support_iff _ _).mp
    (Cslib.Probability.PMF.mem_support_uniformOfFintype d)) ((PMF.mem_support_iff _ _).mp hsupp)

/-- The law `P_{Ω | W_C}` of the sample space conditioned on winning every coordinate in `C`. Every
law of [Holenstein, proof of Lemma 6.4][Holenstein2009] is the image of this law under a variable
of the model. -/
noncomputable def condLaw (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    PMF (Sample X Y C) :=
  (sampleLaw G C).filter (winsOnSample G C ha hb) (exists_mem_winsOnSample_support hC)

variable {G C ha hb}

/-- **The bits are independent of the questions under `W_C`** [Holenstein, proof of
Lemma 6.4][Holenstein2009]: `W_C` is an event about the question pairs, so conditioning on it keeps
the bits uniform and independent of the conditioned question pairs. -/
theorem condLaw_eq_bind (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    condLaw G C ha hb hC = (uniformOfFintype ({i // i ∉ C} → Bool)).bind fun d =>
      ((pi fun _ : Fin n => G.questions).filter (winsOnPairs G C ha hb)
        (exists_mem_winsOnPairs_support hC)).map (d, ·) := by
  have hrect : winsOnSample G C ha hb = Set.univ ×ˢ winsOnPairs G C ha hb := by
    ext ω
    simp [winsOnSample]
  have huniv : ∃ d ∈ (Set.univ : Set ({i // i ∉ C} → Bool)),
      d ∈ (uniformOfFintype ({i // i ∉ C} → Bool)).support :=
    ⟨fun _ => true, trivial, Cslib.Probability.PMF.mem_support_uniformOfFintype _⟩
  simp only [condLaw, hrect]
  refine (Cslib.Probability.PMF.filter_bind_pair_prod _ _ _ _ _ huniv
    (exists_mem_winsOnPairs_support hC)).trans ?_
  rw [Cslib.Probability.PMF.filter_eq_self_of_support_subset _ _ _ (Set.subset_univ _)]

/-- Under `W_C`, the question pairs have the law of independent pairs conditioned on `W_C`. -/
theorem map_snd_condLaw (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    (condLaw G C ha hb hC).map Prod.snd =
      (pi fun _ : Fin n => G.questions).filter (winsOnPairs G C ha hb)
        (exists_mem_winsOnPairs_support hC) := by
  rw [condLaw_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, PMF.bind_const]
  exact PMF.map_id _

/-- **The recombined questions** [Holenstein, proof of Lemma 6.4][Holenstein2009]: under `W_C`, the
question tuples of the sample have the law of the questions of the repetition conditioned on
`W_C`. -/
theorem map_condLaw_questions (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    (condLaw G C ha hb hC).map (fun ω => (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2)) =
      (G.pow n).questions.filter (G.winsOn ha hb C) hC := by
  calc _ = ((condLaw G C ha hb hC).map Prod.snd).map fun q => (Prod.fst ∘ q, Prod.snd ∘ q) := by
        rw [PMF.map_comp]
        rfl
    _ = ((pi fun _ : Fin n => G.questions).filter (winsOnPairs G C ha hb)
          (exists_mem_winsOnPairs_support hC)).map fun q => (Prod.fst ∘ q, Prod.snd ∘ q) := by
        rw [map_snd_condLaw]
    _ = _ := (Cslib.Probability.PMF.filter_map _ _ _ hC _).symm

/-- **The bit `D_j` is uniform under `W_C`** [Holenstein, proof of Lemma 6.4][Holenstein2009]: the
event `D_j = b` has probability `1 / 2`, as Claim 6.1 requires in (6.7). -/
theorem toOuterMeasure_condLaw_bit (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support)
    (j : {i // i ∉ C}) (b : Bool) :
    ((condLaw G C ha hb hC).toOuterMeasure {ω | ω.1 j = b}).toReal = 1 / 2 := by
  have hrect : {ω : Sample X Y C | ω.1 j = b} = {d | d j = b} ×ˢ Set.univ := by
    ext ω
    simp
  have hmap : (uniformOfFintype ({i // i ∉ C} → Bool)).map (fun d => d j) =
      uniformOfFintype Bool := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype]
    exact Cslib.Probability.PMF.pi_map_eval _ j
  rw [condLaw_eq_bind, hrect, Cslib.Probability.PMF.toOuterMeasure_bind_pair_prod,
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _), mul_one,
    show {d : {i // i ∉ C} → Bool | d j = b} = (fun d => d j) ⁻¹' {b} from rfl,
    ← PMF.toOuterMeasure_map_apply, hmap, PMF.toOuterMeasure_apply_singleton,
    Cslib.Probability.PMF.uniformOfFintype_apply]
  simp

/-- **Conditioning on the bit `D_j`** [Holenstein, proof of Lemma 6.4, (6.10)][Holenstein2009]:
under `W_C`, conditioning on `D_j = b` does not change the law of a variable that ignores `D_j`. -/
theorem map_filter_condLaw_bit (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support)
    (j : {i // i ∉ C}) (b : Bool) {Z : Type*} (F : Sample X Y C → Z)
    (hF : ∀ d c q, F (Function.update d j c, q) = F (d, q))
    (h : ∃ ω ∈ {ω : Sample X Y C | ω.1 j = b}, ω ∈ (condLaw G C ha hb hC).support) :
    ((condLaw G C ha hb hC).filter {ω | ω.1 j = b} h).map F = (condLaw G C ha hb hC).map F := by
  set K := (pi fun _ : Fin n => G.questions).filter (winsOnPairs G C ha hb)
    (exists_mem_winsOnPairs_support hC)
  have hbit : ∃ d ∈ {d : {i // i ∉ C} → Bool | d j = b},
      d ∈ (uniformOfFintype ({i // i ∉ C} → Bool)).support :=
    ⟨fun _ => b, rfl, Cslib.Probability.PMF.mem_support_uniformOfFintype _⟩
  have hfil : (condLaw G C ha hb hC).filter {ω | ω.1 j = b} h =
      (uniformOfFintype ({i // i ∉ C} → Bool)).bind fun d => K.map (Function.update d j b, ·) := by
    simp only [condLaw_eq_bind]
    refine (Cslib.Probability.PMF.filter_bind_pair _ (fun _ => K)
      {d : {i // i ∉ C} → Bool | d j = b} _ hbit).trans ?_
    rw [Cslib.Probability.PMF.filter_uniformOfFintype_eval_eq, PMF.bind_map]
    rfl
  rw [hfil, condLaw_eq_bind, PMF.map_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, hF]
  rfl

/-! ### Holenstein's (6.5) -/

/-- **Holenstein's (6.5)** [Holenstein, proof of Lemma 6.4, (6.5)–(6.6)][Holenstein2009]:
Corollary 4.3 (`sum_dist_filter_sideJoint_le`) applied to the coordinate model with the event
`W_C`. Under `W_C`, drawing the question pair at each free coordinate `j` given only its revealed
half, rather than from its law given `(T, V)`, changes the law of `((T, V), (x_j, y_j))` little on
average: `∑_{j ∉ C} ‖P_{T V U_j | W} - P_{T V | W} P_{U_j | T}‖` is at most
`√(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])) / 2)`. Here `U_j` is the whole question pair at `j`,
and the logarithms are in nats; Holenstein's `ε_Tot` of (6.6) is in bits and has no factor
`1 / 2`. -/
theorem sum_dist_condLaw_le [Fintype A] [Fintype B]
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∑ j : {i // i ∉ C}, dist
        ((condLaw G C ha hb hC).map fun ω => ((revealed C ω, answers C ha hb ω.2), ω.2 j))
        (((condLaw G C ha hb hC).map fun ω => (revealed C ω, answers C ha hb ω.2)).bind
          fun s => (pairGiven G (s.1.halves j)).map (s, ·)) ≤
      Real.sqrt (#Cᶜ * (#C * Real.log (Fintype.card A * Fintype.card B) +
        Real.log (1 / G.winProbOn ha hb C)) / 2) := by
  classical
  set μ := (sampleLaw G C).map (revealed C)
  set J := sideKernel G C ha hb
  set F := fun ω : Sample X Y C =>
    ((revealed C ω, answers C ha hb ω.2), fun i : {i // i ∉ C} => ω.2 i)
  set W : Set ((Revealed X Y C × (C → A × B)) × ({i // i ∉ C} → X × Y)) :=
    (fun z => z.1.1.combine z.2) ⁻¹' winsOnPairs G C ha hb
  have hFW : F ⁻¹' W = winsOnSample G C ha hb := by
    ext ω
    simp only [F, W, winsOnSample, Set.mem_preimage, combine_revealed]
  have hside : (sampleLaw G C).map F = sideJoint μ J := map_sampleLaw_eq_sideJoint G C ha hb
  have hω := exists_mem_winsOnSample_support hC
  have hW : ∃ x ∈ W, x ∈ (sideJoint μ J).support := by
    obtain ⟨ω, hω, hsupp⟩ := hω
    refine ⟨F ω, ?_, hside ▸ (PMF.mem_support_map_iff _ _ _).mpr ⟨ω, hsupp, rfl⟩⟩
    rw [← Set.mem_preimage, hFW]
    exact hω
  have hfil : (sideJoint μ J).filter W hW = (condLaw G C ha hb hC).map F := by
    simp only [← hside]
    rw [Cslib.Probability.PMF.filter_map _ _ _ _ (hFW ▸ hω)]
    simp only [condLaw, hFW]
  have hprob : ((sideJoint μ J).toOuterMeasure W).toReal = G.winProbOn ha hb C := by
    rw [← hside, PMF.toOuterMeasure_map_apply, hFW, toOuterMeasure_sampleLaw_winsOnSample]
  have hcor := Cslib.Probability.PMF.sum_dist_filter_sideJoint_le μ
    (fun i t => pairGiven G (t.halves i)) J (map_fst_sideKernel G C ha hb) W hW
  rw [hfil, hprob] at hcor
  simp only [PMF.map_comp, Function.comp_def, F] at hcor
  refine hcor.trans (Real.sqrt_le_sqrt (le_of_eq ?_))
  -- `|V| = (|A| |B|)^{#C}`, and the free coordinates are `Cᶜ`.
  have hfree : Fintype.card {i // i ∉ C} = #Cᶜ := by
    simp only [← Finset.mem_compl, Fintype.card_coe]
  have hV : (Fintype.card (C → A × B) : ℝ) = (Fintype.card A * Fintype.card B) ^ #C := by
    rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_coe]
    push_cast
    ring
  have hVpos : (0 : ℝ) < Fintype.card (C → A × B) := by
    obtain ⟨⟨x, y⟩, -⟩ := hC
    have : Nonempty (C → A × B) := ⟨fun i => (ha x i, hb y i)⟩
    exact_mod_cast Fintype.card_pos
  have hp : 0 < G.winProbOn ha hb C := by
    rw [← hprob]
    exact (Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff _ _).mpr hW
  rw [hfree, Real.log_div hVpos.ne' hp.ne', hV, Real.log_pow, one_div, Real.log_inv]
  ring

end Laws

end Cslib.PCP.ParallelRepetition

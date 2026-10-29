/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Complexity.Classes.NP.SelfReduction
public import Complexity.Computability.Complexity.Classes.NP.Witness
public import Complexity.Computability.Complexity.Classes.PH.Collapse
import Complexity.Computability.Circuit.Boolean.Advice
import Complexity.Computability.Complexity.Classes.PH.Projection
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# The Karp–Lipton theorem

If `SAT` has circuits of polynomial size, the polynomial hierarchy collapses to its second level
[Karp and Lipton][KarpLipton1980], [Arora and Barak, Theorem 6.19][AroraBarak09]. The hypothesis is
that some language `L ∈ P/poly` contains exactly the encodings `encCNF φ` of the satisfiable
formulas; it follows from `NP ⊆ P/poly`, for problems with any encoding of their instances.

The proof shows `Π₂ ⊆ Σ₂` (`Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT`). Let
`a ∈ A ↔ ∀ u, ∃ v, V (a, u ++ v)`. The pairs `(a, u)` for which some `v` is accepted form a
problem in `NP` by the witness API (`Cslib.Complexity.mem_NP_setOf_exists_append`), which the
Cook–Levin reduction `f` maps to `SAT`. A `Σ₂` verifier guesses circuits for `SAT` on all the
lengths the self-reduction (`Cslib.Complexity.SAT.search`) of a formula `f (a, u)` asks about, then
checks,
for every `u`, that the self-reduction answered by the guessed circuits finds a satisfying
assignment of `f (a, u)`. A satisfying assignment proves `(a, u)` in the problem whatever circuits
were guessed, and correct circuits always find one when there is one. Since `Π₂ ⊆ Σ₂` holds for
every encoding of instances, the hierarchy collapses to `Σ₂`
(`Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`).

The guessed circuits are listed in an advice string (`Cslib.Circuits.Boolean.familyAdvice`,
`Cslib.Circuits.Boolean.PPoly.exists_evalAdvice`): the circuits `C 0, …, C N`, each in the
certificate format of `Cslib.Circuits.Boolean.readCertificate`, padded to a common length. The
circuit for an input `x` is read from the block at position `x.length` and evaluated on `x`
(`Cslib.Circuits.Boolean.evalAdvice`), in polynomial time.

The same advice-string mechanism eliminates alternating quantifiers nonuniformly: if `M ∈ P/poly`,
replacing `M` by an advice string listing its circuits up to length `2 |x| + 1 + p |x|` turns the
existential quantifier over `w` of length `p |x|` in `frame x ++ w ∈ M` into a language in `NP`,
and hardwiring the advice string (`Cslib.Circuits.Boolean.PPoly.of_advice`) shows that the
existential projection remains in `P/poly` when `NP ⊆ P/poly`
(`Cslib.Complexity.mem_PPoly_of_exists_frame_append`). Together with closure of `P/poly` under
complement (`Cslib.Circuits.Boolean.PPolyOn.compl`) and `P ⊆ P/poly`
(`Cslib.Circuits.Boolean.P_subset_PPolyOn`), induction on `k` gives `Σₖ ⊆ P/poly`,
`Πₖ ⊆ P/poly`, and `PH ⊆ P/poly`
(`Cslib.Complexity.SigmaP_subset_PPolyOn_of_NP_subset_PPoly`,
`Cslib.Complexity.PiP_subset_PPolyOn_of_NP_subset_PPoly`,
`Cslib.Complexity.PH_subset_PPolyOn_of_NP_subset_PPoly`)
[Karp and Lipton, Section 3][KarpLipton1980], [Arora and Barak, Section 6.4][AroraBarak09].
Furthermore, `P/poly` preimages are closed under polynomial-time many-one reductions
(`Cslib.Complexity.PolyTimeReducible.mem_PPolyOn`), so `NP encBits ⊆ PPolyOn encBits` is
equivalent to `SAT ∈ PPolyOn encCNF` (`Cslib.Complexity.NP_subset_PPolyOn_iff_SAT`).

## Main results

* `Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT`: if `SAT` has circuits of polynomial size,
  then `Π₂ ⊆ Σ₂`.
* `Cslib.Complexity.PiP_two_eq_SigmaP_two_of_SAT`: under the same hypothesis, `Π₂ = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_SAT`: **the Karp–Lipton theorem**, if `SAT` has circuits
  of polynomial size, then `PH = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`: if `NP ⊆ P/poly`, then `PH = Σ₂`.
* `Cslib.Complexity.PolyTimeReducible.mem_PPolyOn`: preimages of `P/poly` are closed under
  polynomial-time many-one reductions.
* `Cslib.Complexity.mem_PPoly_of_exists_frame_append`,
  `Cslib.Complexity.PPolyOn.exists_of_computableInPolyTime_length`,
  `Cslib.Complexity.PPolyOn.forall_of_computableInPolyTime_length`: nonuniform existential and
  universal quantifier elimination in `P/poly` under `NP ⊆ P/poly`.
* `Cslib.Complexity.SigmaP_subset_PPolyOn_of_NP_subset_PPoly`,
  `Cslib.Complexity.PiP_subset_PPolyOn_of_NP_subset_PPoly`,
  `Cslib.Complexity.PH_subset_PPolyOn_of_NP_subset_PPoly`: if `NP ⊆ P/poly`, then `Σₖ ⊆ P/poly`,
  `Πₖ ⊆ P/poly`, and `PH ⊆ P/poly`.
* `Cslib.Complexity.NP_subset_PPolyOn_iff_SAT`: equivalence of `NP encBits ⊆ PPolyOn encBits` and
  `SAT ∈ PPolyOn encCNF`.

## References

* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.4][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-! ### The Karp–Lipton verifier -/

namespace KarpLipton

/-- The `Σ₂` verifier of Karp and Lipton for the reduction `f` to `SAT`. On `(a, w₁ ++ u)`, where
`w₁` has `P (enc a).length` bits, it runs the self-reduction of `f (a, u)` with the circuits read
from the advice string `w₁` (with at most `S (enc a).length` gates, in blocks of
`W (enc a).length` bits), and checks the assignment it finds. -/
private def verifier (enc : α ↪ List Bool) (f : α × List Bool → CNF ℕ) (S W P : Polynomial ℕ)
    (x : α × List Bool) : Bool :=
  SAT.verifier (f (x.1, x.2.drop (P.eval (enc x.1).length)),
    SAT.search (fun ψ => evalAdvice (S.eval (enc x.1).length) (W.eval (enc x.1).length)
      (x.2.take (P.eval (enc x.1).length)) (encCNF ψ))
      (f (x.1, x.2.drop (P.eval (enc x.1).length))))

private theorem verifier_append {f : α × List Bool → CNF ℕ} {S W P : Polynomial ℕ} (a : α)
    {w₁ : List Bool} (hw₁ : w₁.length = P.eval (enc a).length) (u : List Bool) :
    verifier enc f S W P (a, w₁ ++ u) = SAT.verifier (f (a, u),
      SAT.search (fun ψ => evalAdvice (S.eval (enc a).length) (W.eval (enc a).length) w₁
        (encCNF ψ)) (f (a, u))) := by
  rw [verifier, ← hw₁, List.drop_left, List.take_left]

private theorem computableInPolyTime_verifier {f : α × List Bool → CNF ℕ}
    (hf : ComputableInPolyTime f (encPair enc encBits) encCNF) (S W P : Polynomial ℕ) :
    ComputableInPolyTime (verifier enc f S W P) (encPair enc encBits) encBool := by
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary :=
    (encoding_length enc).comp (fst _ _)
  have hφ : ComputableInPolyTime (fun x : α × List Bool =>
      f (x.1, x.2.drop (P.eval (enc x.1).length))) (encPair enc encBits) encCNF :=
    hf.comp ((fst _ _).prod (bitsDropWithInput (snd _ _) ((unary_eval P).comp hn)))
  have hD : ComputableInPolyTime (fun p : (α × List Bool) × CNF ℕ =>
      evalAdvice (S.eval (enc p.1.1).length) (W.eval (enc p.1.1).length)
        (p.1.2.take (P.eval (enc p.1.1).length)) (encCNF p.2))
      (encPair (encPair enc encBits) encCNF) encBool := by
    have hn' := hn.comp (fst (encPair enc encBits) encCNF)
    exact computableInPolyTime_evalAdvice_eval S W hn'
      (bitsTakeWithInput ((snd _ _).comp (fst _ _)) ((unary_eval P).comp hn'))
      ((of_eq (f := encCNF) (encOut := encBits) fun _ => rfl).comp (snd _ _))
  exact SAT.computableInPolyTime_verifier.comp (hφ.prod (SAT.computableInPolyTime_search hD hφ))

end KarpLipton

/-! ### `Π₂ ⊆ Σ₂` -/

/-- **Karp–Lipton, `Π₂ ⊆ Σ₂`.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then `Π₂ ⊆ Σ₂`, for every encoding of instances. -/
theorem PiP_two_subset_SigmaP_two_of_SAT (hSAT : SAT ∈ PPolyOn encCNF)
    (enc : α ↪ List Bool) : PiP 2 enc ⊆ SigmaP 2 enc := by
  rintro A ⟨ps, V, hlen, hV, hA⟩
  obtain ⟨p, q, rfl⟩ := List.length_eq_two.1 hlen
  obtain ⟨f, hf, hfB⟩ := CookLevin.SAT_npHard _ _ (mem_NP_setOf_exists_append hV q)
  obtain ⟨L, hL, hSAT⟩ := hSAT
  obtain ⟨c', d', hf'⟩ := hf.polyBounded_length.exists_le
  -- a bound on the length of the formulas `f (a, u)`
  let F : Polynomial ℕ := Polynomial.C c' * (2 * Polynomial.X + 2 + p) ^ d'
  -- a bound on the length of the queries
  let N : Polynomial ℕ := F + (F + 1) * (8 * F + 11)
  obtain ⟨S, W, P, α_adv, hlen_α, -, h_eval⟩ := PPoly.exists_evalAdvice hL N
  have hF (a : α) (u : List Bool) (hu : u.length = p.eval (enc a).length) :
      (encCNF (f (a, u))).length ≤ F.eval (enc a).length := by
    refine (hf' (a, u)).trans (le_of_eq ?_)
    simp only [length_encPair, encBits_apply, hu, F, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  have hN (n : ℕ) : N.eval n = SAT.queryBound (F.eval n) := by
    simp [N, SAT.queryBound, Polynomial.eval_add, Polynomial.eval_mul]
  refine ⟨[P, p], KarpLipton.verifier enc f S W P, rfl,
    KarpLipton.computableInPolyTime_verifier hf S W P, fun a => ?_⟩
  set n := (enc a).length
  -- membership in `A` through `SAT`
  have hA' : a ∈ A ↔ ∀ u : List Bool, u.length = p.eval n → f (a, u) ∈ SAT := by
    rw [hA a]
    simp only [List.map_cons, List.map_nil, alternation_false_cons, alternation_true_cons,
      alternation_nil, List.append_nil]
    exact forall₂_congr fun u _ => hfB (a, u)
  rw [hA']
  simp only [List.map_cons, List.map_nil, alternation_true_cons, alternation_false_cons,
    alternation_nil, List.append_nil]
  constructor
  · intro h
    refine ⟨α_adv n, hlen_α n, fun u hu => ?_⟩
    rw [KarpLipton.verifier_append a (hlen_α n)]
    refine SAT.verifier_search (fun ψ hψ => ?_) (h u hu)
    have hlen : (encCNF ψ).length ≤ N.eval n := by
      rw [hN]
      exact hψ.trans (SAT.queryBound_mono (hF a u hu))
    exact (h_eval n (encCNF ψ) hlen).trans (hSAT ψ).symm
  · rintro ⟨w₁, hw₁, h⟩ u hu
    have := h u hu
    rw [KarpLipton.verifier_append a hw₁] at this
    exact ⟨_, this⟩

/-- **Karp–Lipton, `Π₂ = Σ₂`.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then `Π₂ = Σ₂`, for every encoding of instances. -/
theorem PiP_two_eq_SigmaP_two_of_SAT (hSAT : SAT ∈ PPolyOn encCNF)
    (enc : α ↪ List Bool) : PiP 2 enc = SigmaP 2 enc := by
  refine (PiP_two_subset_SigmaP_two_of_SAT hSAT enc).antisymm fun A hA => ?_
  simpa using compl_mem_PiP_of_mem_SigmaP
    (PiP_two_subset_SigmaP_two_of_SAT hSAT enc (compl_mem_PiP_of_mem_SigmaP hA))

/-! ### The collapse -/

/-- **The Karp–Lipton theorem.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then the polynomial hierarchy collapses to its second level: `PH = Σ₂`, for
every encoding of instances. -/
theorem PH_eq_SigmaP_two_of_SAT (hSAT : SAT ∈ PPolyOn encCNF) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by norm_num) fun encB =>
    PiP_two_subset_SigmaP_two_of_SAT hSAT encB

/-- **The Karp–Lipton theorem, `NP ⊆ P/poly ⇒ PH = Σ₂`.** If every problem in `NP`, with any
encoding of its instances, is the preimage of a language in `P/poly`, then `PH = Σ₂`, for every
encoding of instances. -/
theorem PH_eq_SigmaP_two_of_NP_subset_PPoly
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ PPolyOn encB) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_SAT (h encCNF SAT.mem_NP)

/-! ### Nonuniform quantifier elimination and `PH ⊆ P/poly` -/

/-- **Preimages of `P/poly` are closed under polynomial-time reductions.** If `A` reduces to `B`
in polynomial time and `B` is the preimage under `encB` of a language in `P/poly`, then `A` is
the preimage under `enc` of a language in `P/poly`: evaluating the circuits for `B` up to the
polynomial output-length bound of the reduction from an advice string is polynomial-time, and
hardwiring the advice string (`PPoly.of_advice`) gives circuits of polynomial size. -/
theorem PolyTimeReducible.mem_PPolyOn {β : Type} {encB : β ↪ List Bool} {A : Set α}
    {B : Set β} (hAB : PolyTimeReducible enc encB A B)
    (hB : B ∈ PPolyOn encB) :
    A ∈ PPolyOn enc := by
  obtain ⟨f, hf, hiff⟩ := hAB
  obtain ⟨L_B, hL_B, hLB⟩ := hB
  obtain ⟨c', d', hf'⟩ := hf.polyBounded_length.exists_le
  let N : Polynomial ℕ := Polynomial.C c' * (Polynomial.X + 1) ^ d'
  obtain ⟨S, W, _, α_adv, -, hα, h_eval⟩ := PPoly.exists_evalAdvice hL_B N
  have hN (a : α) : (encB (f a)).length ≤ N.eval (enc a).length := by
    refine (hf' a).trans (le_of_eq ?_)
    simp [N]
  let g : List Bool × α → Bool := fun x =>
    evalAdvice (S.eval (enc x.2).length) (W.eval (enc x.2).length) x.1 (encB (f x.2))
  have hg : ComputableInPolyTime g (encPair encBits enc) encBool :=
    computableInPolyTime_evalAdvice_eval S W ((encoding_length enc).comp (snd _ _)) (fst _ _)
      ((of_eq (f := encB) (encOut := encBits) fun _ => rfl).comp (hf.comp (snd _ _)))
  obtain ⟨M, hM, hgM⟩ := PPoly.exists_of_polyTime hg
  let L : Language Bool := {x : List Bool | frame (α_adv x.length) ++ x ∈ M}
  refine ⟨L, PPoly.of_advice hM α_adv hα (fun _ => Iff.rfl), fun a => ?_⟩
  change a ∈ A ↔ frame (α_adv (enc a).length) ++ enc a ∈ M
  have hgM' := hgM (α_adv (enc a).length, a)
  rw [encPair_apply, encBits_apply] at hgM'
  rw [hiff a, hLB (f a), ← hgM']
  exact (h_eval (enc a).length (encB (f a)) (hN a)).symm

/-- **Nonuniform quantifier elimination.** If every language in `NP` over `Bool` is in `P/poly`
and `M` is in `P/poly`, then the language of words `x` for which `frame x ++ w ∈ M` for some `w` of
length `p |x|` is in `P/poly`: replacing `M` by an advice string listing its circuits up to length
`2 |x| + 1 + p |x|` turns the existential quantifier over `w` into a language in `NP`, and
hardwiring the advice string (`Cslib.Circuits.Boolean.PPoly.of_advice`) gives circuits of
polynomial size [Karp and Lipton, Section 3][KarpLipton1980]. -/
theorem mem_PPoly_of_exists_frame_append
    (hNP : NP encBits ⊆ PPolyOn encBits)
    {M : Language Bool} (hM : M ∈ PPoly) (p : Polynomial ℕ) :
    ({x : List Bool | ∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M} :
      Language Bool) ∈ PPoly := by
  let N : Polynomial ℕ := 2 * Polynomial.X + 1 + p
  obtain ⟨S, W, _, α_adv, -, hα, h_eval⟩ := PPoly.exists_evalAdvice hM N
  have hN (n : ℕ) : N.eval n = 2 * n + 1 + p.eval n := by
    simp [N, Polynomial.eval_add, Polynomial.eval_mul]
  let V : List Bool × List Bool → Bool := fun z =>
    evalAdvice (S.eval (dropFrame z.1).length) (W.eval (dropFrame z.1).length) (unframe z.1)
      (frame (dropFrame z.1) ++ z.2.take (p.eval (dropFrame z.1).length))
  have hV : ComputableInPolyTime V (encPair encBits encBits) encBool := by
    have hx : ComputableInPolyTime (fun z : List Bool × List Bool => dropFrame z.1)
        (encPair encBits encBits) encBits :=
      dropFrame.comp (fst _ _)
    have hu : ComputableInPolyTime (fun z : List Bool × List Bool => unframe z.1)
        (encPair encBits encBits) encBits :=
      unframe.comp (fst _ _)
    have hn : ComputableInPolyTime (fun z : List Bool × List Bool => (dropFrame z.1).length)
        (encPair encBits encBits) encUnary := length_bits.comp hx
    have hw : ComputableInPolyTime
        (fun z : List Bool × List Bool => z.2.take (p.eval (dropFrame z.1).length))
        (encPair encBits encBits) encBits :=
      bitsTakeWithInput (snd _ _) ((unary_eval p).comp hn)
    exact computableInPolyTime_evalAdvice_eval S W hn hu
      (bitsAppend ((bitsFrame encBits).comp hx) hw)
  let D : Language Bool := {z : List Bool | ∃ w : List Bool, w.length = p.eval z.length ∧
    V (z, w) = true}
  have hD : D ∈ PPoly := mem_PPolyOn_encBits_iff.1 (hNP ⟨p, V, hV, fun _ => Iff.rfl⟩)
  refine PPoly.of_advice hD α_adv hα fun x => ?_
  change (∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M) ↔
    (∃ w : List Bool, w.length = p.eval (frame (α_adv x.length) ++ x).length ∧
      V (frame (α_adv x.length) ++ x, w) = true)
  have hle : p.eval x.length ≤ p.eval (frame (α_adv x.length) ++ x).length :=
    p.eval_mono (by simp)
  have hV_frame (w : List Bool) (hw : w.length = p.eval x.length) :
      evalAdvice (S.eval x.length) (W.eval x.length) (α_adv x.length) (frame x ++ w) = true ↔
        frame x ++ w ∈ M :=
    h_eval x.length (frame x ++ w) (by simp [hN, hw])
  constructor
  · rintro ⟨w, hw, hwM⟩
    refine ⟨w ++ List.replicate (p.eval (frame (α_adv x.length) ++ x).length - w.length) false,
      by rw [List.length_append, List.length_replicate, hw, Nat.add_sub_cancel' hle], ?_⟩
    dsimp only [V]
    rw [unframe_frame_append, dropFrame_frame_append, ← hw, List.take_left]
    exact (hV_frame w hw).2 hwM
  · rintro ⟨w, hw, hwV⟩
    dsimp only [V] at hwV
    rw [unframe_frame_append, dropFrame_frame_append] at hwV
    have htake : (w.take (p.eval x.length)).length = p.eval x.length := by
      rw [List.length_take, hw, Nat.min_eq_left hle]
    exact ⟨w.take (p.eval x.length), htake, (hV_frame _ htake).1 hwV⟩

/-- **Nonuniform existential quantifier elimination in `PPolyOn`.** Under `NP ⊆ P/poly`, if a
relation `P : α → List Bool → Prop` is in `PPolyOn (encPair enc encBits)` and the witness length
`N : α → ℕ` is computable in polynomial time in unary, then `{a | ∃ u, u.length = N a ∧ P a u}` is
in `PPolyOn enc`. -/
theorem PPolyOn.exists_of_computableInPolyTime_length
    (hNP : NP encBits ⊆ PPolyOn encBits) {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {P : α → List Bool → Prop}
    (hP : {p : α × List Bool | P p.1 p.2} ∈ PPolyOn (encPair enc encBits)) :
    {a : α | ∃ u : List Bool, u.length = N a ∧ P a u} ∈ PPolyOn enc := by
  let B : Set (α × List Bool) := {p | P p.1 (p.2.take (N p.1))}
  have hred : PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
      B {p : α × List Bool | P p.1 p.2} := by
    refine ⟨fun p => (p.1, p.2.take (N p.1)), ?_, fun _ => Iff.rfl⟩
    exact (fst enc encBits).prod (bitsTakeWithInput (snd enc encBits) (hN.comp (fst enc encBits)))
  obtain ⟨M, hM, hBM⟩ := hred.mem_PPolyOn hP
  obtain ⟨p, hp⟩ := hN.polyBounded.exists_polynomial
  refine ⟨{x : List Bool | ∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M},
    mem_PPoly_of_exists_frame_append hNP hM p, fun a => ?_⟩
  have hle : N a ≤ p.eval (enc a).length := hp a
  constructor
  · rintro ⟨u, hu, hPu⟩
    refine ⟨u ++ List.replicate (p.eval (enc a).length - N a) false,
      by rw [List.length_append, List.length_replicate, hu, Nat.add_sub_cancel' hle], ?_⟩
    have htake : (u ++ List.replicate (p.eval (enc a).length - N a) false).take (N a) = u := by
      rw [← hu, List.take_left]
    have hmem : (a, u ++ List.replicate (p.eval (enc a).length - N a) false) ∈ B := by
      change P a ((u ++ List.replicate (p.eval (enc a).length - N a) false).take (N a))
      rwa [htake]
    simpa [encPair_apply, encBits_apply] using (hBM _).1 hmem
  · rintro ⟨w, hw, hwM⟩
    have hmem : (a, w) ∈ B :=
      (hBM (a, w)).2 (by simpa [encPair_apply, encBits_apply] using hwM)
    refine ⟨w.take (N a), ?_, hmem⟩
    rw [List.length_take, hw, Nat.min_eq_left hle]

/-- **Nonuniform universal quantifier elimination in `PPolyOn`.** Under `NP ⊆ P/poly`, if a
relation `P : α → List Bool → Prop` is in `PPolyOn (encPair enc encBits)` and the bound `N : α → ℕ`
is computable in polynomial time in unary, then `{a | ∀ u, u.length = N a → P a u}` is in
`PPolyOn enc`. -/
theorem PPolyOn.forall_of_computableInPolyTime_length
    (hNP : NP encBits ⊆ PPolyOn encBits) {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {P : α → List Bool → Prop}
    (hP : {p : α × List Bool | P p.1 p.2} ∈ PPolyOn (encPair enc encBits)) :
    {a : α | ∀ u : List Bool, u.length = N a → P a u} ∈ PPolyOn enc := by
  have hex : {a : α | ∃ u : List Bool, u.length = N a ∧ ¬ P a u} ∈ PPolyOn enc :=
    PPolyOn.exists_of_computableInPolyTime_length hNP hN (PPolyOn.compl hP)
  have h_eq : {a : α | ∀ u : List Bool, u.length = N a → P a u} =
      {a : α | ∃ u : List Bool, u.length = N a ∧ ¬ P a u}ᶜ := by
    ext a
    simp
  rw [h_eq]
  exact PPolyOn.compl hex

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ Σₖ ⊆ P/poly`.** If `NP ⊆ P/poly` over bitstrings, then every
level `Σₖ` of the polynomial hierarchy, with any encoding of its instances, is in `P/poly`
[Karp and Lipton, Section 3][KarpLipton1980], [Arora and Barak, Section 6.4][AroraBarak09]. -/
theorem SigmaP_subset_PPolyOn_of_NP_subset_PPoly
    (hNP : NP encBits ⊆ PPolyOn encBits) (k : ℕ) : SigmaP k enc ⊆ PPolyOn enc := by
  induction k generalizing α with
  | zero =>
    intro A hA
    rw [SigmaP_zero] at hA
    exact P_subset_PPolyOn hA
  | succ k ih =>
    intro A hA
    obtain ⟨p, B, hB, hAB⟩ := exists_mem_PiP_of_mem_SigmaP_succ hA
    have hB_PPoly : B ∈ PPolyOn (encPair enc encBits) := by
      simpa using PPolyOn.compl (ih (compl_mem_SigmaP_of_mem_PiP hB))
    have hN : ComputableInPolyTime (fun a : α => p.eval (enc a).length) enc encUnary :=
      (unary_eval p).comp (encoding_length enc)
    have hA_eq : A = {a : α | ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ B} :=
      Set.ext hAB
    rw [hA_eq]
    exact PPolyOn.exists_of_computableInPolyTime_length hNP hN hB_PPoly

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ Πₖ ⊆ P/poly`.** If `NP ⊆ P/poly` over bitstrings, then every
level `Πₖ` of the polynomial hierarchy, with any encoding of its instances, is in `P/poly`. -/
theorem PiP_subset_PPolyOn_of_NP_subset_PPoly
    (hNP : NP encBits ⊆ PPolyOn encBits) (k : ℕ) : PiP k enc ⊆ PPolyOn enc :=
  fun _ hA => by
    simpa using PPolyOn.compl (SigmaP_subset_PPolyOn_of_NP_subset_PPoly hNP k
      (compl_mem_SigmaP_of_mem_PiP hA))

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ PH ⊆ P/poly`.** If `NP ⊆ P/poly` over bitstrings, then the
entire polynomial hierarchy, with any encoding of its instances, is in `P/poly`
[Karp and Lipton, Section 3][KarpLipton1980], [Arora and Barak, Section 6.4][AroraBarak09]. -/
theorem PH_subset_PPolyOn_of_NP_subset_PPoly
    (hNP : NP encBits ⊆ PPolyOn encBits) : PH enc ⊆ PPolyOn enc :=
  Set.iUnion_subset (SigmaP_subset_PPolyOn_of_NP_subset_PPoly hNP)

/-- **Equivalence of `NP ⊆ P/poly` over bitstrings and `SAT ∈ P/poly`.** Having polynomial-size
circuits for every problem in `NP encBits` is equivalent to `SAT` having circuits of polynomial
size. -/
theorem NP_subset_PPolyOn_iff_SAT :
    NP encBits ⊆ PPolyOn encBits ↔ SAT ∈ PPolyOn encCNF :=
  ⟨fun hNP => SigmaP_subset_PPolyOn_of_NP_subset_PPoly hNP 1 (SigmaP_one ▸ SAT.mem_NP),
    fun hSAT _ hB => (CookLevin.SAT_npHard encBits _ hB).mem_PPolyOn hSAT⟩

end Cslib.Complexity

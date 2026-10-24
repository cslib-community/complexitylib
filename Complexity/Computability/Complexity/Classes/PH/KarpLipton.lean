/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding.Certificate
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

The guessed circuits are listed in an advice string (`Cslib.Circuits.Boolean.familyAdvice`): the
circuits `C 0, …, C N`, each in the certificate format of
`Cslib.Circuits.Boolean.readCertificate`, padded to a common length. The circuit for an input `x`
is read from the block at position `x.length` and evaluated on `x`
(`Cslib.Circuits.Boolean.evalAdvice`), in polynomial time.

The same advice-string mechanism eliminates alternating quantifiers nonuniformly: if `M ∈ P/poly`,
replacing `M` by an advice string listing its circuits up to length `2 |x| + 1 + p |x|` turns the
existential quantifier over `w` of length `p |x|` in `frame x ++ w ∈ M` into a language in `NP`,
and hardwiring the advice string (`Cslib.Circuits.Boolean.PPoly.of_advice`) shows that the
existential projection remains in `P/poly` when `NP ⊆ P/poly`
(`Cslib.Complexity.mem_PPoly_of_exists_frame_append`). Together with closure of `P/poly` under
complement (`Cslib.Circuits.Boolean.PPoly.compl`) and `P ⊆ P/poly`
(`Cslib.Circuits.Boolean.PPoly.exists_of_mem_P`), induction on `k` gives `Σₖ ⊆ P/poly`,
`Πₖ ⊆ P/poly`, and `PH ⊆ P/poly` (`Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP`,
`Cslib.Complexity.exists_mem_PPoly_of_mem_PiP`, `Cslib.Complexity.exists_mem_PPoly_of_mem_PH`)
[Karp and Lipton, Section 3][KarpLipton1980], [Arora and Barak, Section 6.4][AroraBarak09].
Furthermore, `P/poly` preimages are closed under polynomial-time many-one reductions
(`Cslib.Complexity.PolyTimeReducible.exists_mem_PPoly`), so the arbitrary-encoding hypothesis
`∀ encB, ∀ B ∈ NP encB, ∃ L ∈ PPoly, …`, the language-level hypothesis on `encBits`, and the
`SAT` hypothesis are all equivalent (`Cslib.Complexity.forall_mem_NP_exists_mem_PPoly_iff`,
`Cslib.Complexity.forall_mem_NP_exists_mem_PPoly_iff_SAT`).

## Main definitions

* `Cslib.Circuits.Boolean.familyAdvice`: the advice string listing a family of circuits.
* `Cslib.Circuits.Boolean.evalAdvice`: evaluation of the circuit for the length of the input read
  from an advice string.

## Main results

* `Cslib.Circuits.Boolean.evalAdvice_familyAdvice`: evaluation from the advice string of a family
  is evaluation of its circuits.
* `Cslib.Circuits.Boolean.computableInPolyTime_evalAdvice`: evaluation from advice strings is
  polynomial-time.
* `Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT`: if `SAT` has circuits of polynomial size,
  then `Π₂ ⊆ Σ₂`.
* `Cslib.Complexity.PiP_two_eq_SigmaP_two_of_SAT`: under the same hypothesis, `Π₂ = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_SAT`: **the Karp–Lipton theorem**, if `SAT` has circuits
  of polynomial size, then `PH = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`: if `NP ⊆ P/poly`, then `PH = Σ₂`.
* `Cslib.Complexity.PolyTimeReducible.exists_mem_PPoly`: preimages of `P/poly` are closed under
  polynomial-time many-one reductions.
* `Cslib.Complexity.mem_PPoly_of_exists_frame_append`: nonuniform existential quantifier
  elimination in `P/poly` under `NP ⊆ P/poly`.
* `Cslib.Complexity.forall_mem_NP_exists_mem_PPoly_iff`,
  `Cslib.Complexity.forall_mem_NP_exists_mem_PPoly_iff_SAT`: equivalence of the arbitrary-encoding,
  `encBits` language-level, and `SAT` formulations of `NP ⊆ P/poly`.
* `Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP`,
  `Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP_of_NP_subset_PPoly`,
  `Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP_of_SAT`,
  `Cslib.Complexity.SigmaP_subset_PPoly_of_NP_subset_PPoly`: if `NP ⊆ P/poly`, then `Σₖ ⊆ P/poly`
  for every `k`.
* `Cslib.Complexity.exists_mem_PPoly_of_mem_PiP`,
  `Cslib.Complexity.exists_mem_PPoly_of_mem_PH`,
  `Cslib.Complexity.PH_subset_PPoly_of_NP_subset_PPoly`: the corresponding inclusions for `Πₖ`
  and `PH`.

## References

* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.4][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-! ### Advice strings for circuit families -/

/-- The advice string listing the circuits `C 0, …, C N`, each with at most `s` gates: block `m`
holds the certificate of `C m` (`certificate`), padded with `false` to `certLength N s` bits. -/
def familyAdvice (N s : ℕ) (C : ∀ m, Circuit signature m 1) : List Bool :=
  (List.range (N + 1)).flatMap fun m =>
    certificate m s (C m).code.1 ((C m).outputs 0).toNat ++
      List.replicate (certLength N s - certLength m s) false

/-- The value on `x` of the circuit for inputs of length `x.length`, read with at most `s` gates
from the block at position `x.length` of an advice string `w` whose blocks have `width` bits.
Every advice string gives a value. -/
def evalAdvice (s width : ℕ) (w x : List Bool) : Bool :=
  evalOutput x (readCertificate x.length s (w.drop (x.length * width))).1
    (readCertificate x.length s (w.drop (x.length * width))).2

section Family

variable {N s : ℕ} {C : ∀ m, Circuit signature m 1}

private theorem length_familyAdvice_block (hs : ∀ m ≤ N, (C m).size ≤ s) {m : ℕ} (hm : m ≤ N) :
    (certificate m s (C m).code.1 ((C m).outputs 0).toNat ++
      List.replicate (certLength N s - certLength m s) false).length = certLength N s := by
  rw [List.length_append, length_certificate_code _ (hs m hm), List.length_replicate,
    Nat.add_sub_cancel' (certLength_mono_left hm s)]

/-- The advice string of circuits with at most `s` gates has `N + 1` blocks of `certLength N s`
bits. -/
theorem length_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) :
    (familyAdvice N s C).length = (N + 1) * certLength N s := by
  rw [familyAdvice, List.length_flatMap, List.map_congr_left fun m hm =>
    length_familyAdvice_block hs (Nat.lt_succ_iff.1 (List.mem_range.1 hm)), List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]

/-- Block `m` of the advice string of a family starts with the certificate of `C m`. -/
private theorem drop_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) {m : ℕ} (hm : m ≤ N) :
    ∃ rest, (familyAdvice N s C).drop (m * certLength N s) =
      certificate m s (C m).code.1 ((C m).outputs 0).toNat ++ rest := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hprefix : ((List.range m).flatMap fun j =>
      certificate j s (C j).code.1 ((C j).outputs 0).toNat ++
        List.replicate (certLength (m + k) s - certLength j s) false).length =
      m * certLength (m + k) s := by
    rw [List.length_flatMap, List.map_congr_left fun j hj =>
      length_familyAdvice_block hs (by have := List.mem_range.1 hj; omega), List.map_const',
      List.length_range, List.sum_replicate, smul_eq_mul]
  rw [familyAdvice, show m + k + 1 = m + (k + 1) by omega, List.range_add, List.flatMap_append,
    List.drop_left' hprefix, List.range_succ_eq_map, List.map_cons, List.flatMap_cons,
    Nat.add_zero, List.append_assoc]
  exact ⟨_, rfl⟩

/-- **Evaluation from the advice string of a family** is evaluation of its circuits, on inputs of
length at most `N`. -/
theorem evalAdvice_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) {x : List Bool}
    (hx : x.length ≤ N) :
    evalAdvice s (certLength N s) (familyAdvice N s C) x =
      (C x.length).eval interpretation (fun i => x[i]) 0 := by
  obtain ⟨rest, hrest⟩ := drop_familyAdvice hs hx
  rw [evalAdvice, hrest, readCertificate_certificate_code_append _ (hs _ hx),
    Circuit.eval_eq_evalOutput]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

end Family

open ComputableTidilyInPolyTime

/-- **Evaluation from advice strings is polynomial-time**, for the number of gates and the block
width in unary. -/
@[fun_prop]
theorem computableInPolyTime_evalAdvice {γ : Type} {encIn : γ ↪ List Bool}
    {s width : γ → ℕ} {w x : γ → List Bool} (hs : ComputableInPolyTime s encIn encUnary)
    (hwidth : ComputableInPolyTime width encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime (fun a => evalAdvice (s a) (width a) (w a) (x a)) encIn
      encBool := by
  have hs := hs.tidy
  have hwidth := hwidth.tidy
  have hw := hw.tidy
  have hx := hx.tidy
  refine .of_tidy ?_
  have hm : ComputableTidilyInPolyTime (fun a => (x a).length) encIn encUnary := length_bits.comp hx
  have hc := (computableInPolyTime_readCertificate (.of_tidy hm) (.of_tidy hs)
    (.of_tidy (bitsDropWithInput hw (unary_mul.comp (hm.prod hwidth))))).tidy
  exact (computableInPolyTime_evalOutput (.of_tidy hx) (.of_tidy hc.fst') (.of_tidy hc.snd')).tidy

end Cslib.Circuits.Boolean

namespace Cslib.Complexity

open Cslib.Logic.PL Circuits Circuits.Boolean Turing.MultiTapeTM ComputableTidilyInPolyTime

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

private theorem computableTidilyInPolyTime_verifier {f : α × List Bool → CNF ℕ}
    (hf : ComputableTidilyInPolyTime f (encPair enc encBits) encCNF) (S W P : Polynomial ℕ) :
    ComputableTidilyInPolyTime (verifier enc f S W P) (encPair enc encBits) encBool := by
  have hn : ComputableTidilyInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary :=
    (encoding_length enc).comp (fst _ _)
  have hφ : ComputableTidilyInPolyTime (fun x : α × List Bool =>
      f (x.1, x.2.drop (P.eval (enc x.1).length))) (encPair enc encBits) encCNF :=
    hf.comp ((fst _ _).prod (bitsDropWithInput (snd _ _) ((unary_eval P).comp hn)))
  have hD : ComputableTidilyInPolyTime (fun p : (α × List Bool) × CNF ℕ =>
      evalAdvice (S.eval (enc p.1.1).length) (W.eval (enc p.1.1).length)
        (p.1.2.take (P.eval (enc p.1.1).length)) (encCNF p.2))
      (encPair (encPair enc encBits) encCNF) encBool := by
    have hn' := hn.comp (fst (encPair enc encBits) encCNF)
    exact (computableInPolyTime_evalAdvice (.of_tidy ((unary_eval S).comp hn'))
      (.of_tidy ((unary_eval W).comp hn'))
        (.of_tidy (bitsTakeWithInput (fst _ _).snd' ((unary_eval P).comp hn')))
      (.of_tidy ((encode encCNF).comp (snd _ _)))).tidy
  exact SAT.computableInPolyTime_verifier.tidy.comp
    (hφ.prod (SAT.computableInPolyTime_search (.of_tidy hD) (.of_tidy hφ)).tidy)

end KarpLipton

/-! ### `Π₂ ⊆ Σ₂` -/

/-- **Karp–Lipton, `Π₂ ⊆ Σ₂`.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then `Π₂ ⊆ Σ₂`, for every encoding of instances. -/
theorem PiP_two_subset_SigmaP_two_of_SAT (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    (enc : α ↪ List Bool) : PiP 2 enc ⊆ SigmaP 2 enc := by
  rintro A ⟨ps, V, hlen, hV, hA⟩
  obtain ⟨p, q, rfl⟩ := List.length_eq_two.1 hlen
  obtain ⟨f, hf, hfB⟩ := CookLevin.SAT_npHard _ _ (mem_NP_setOf_exists_append hV q)
  obtain ⟨L, hL, hSAT⟩ := hSAT
  obtain ⟨C, s, hs, hC⟩ := mem_PPoly_iff_exists_circuits.1 hL
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.1 hs
  obtain ⟨c', d', hf'⟩ := hf.polyBounded_length.exists_le
  -- a bound on the length of the formulas `f (a, u)`
  let F : Polynomial ℕ := Polynomial.C c' * (2 * Polynomial.X + 2 + p) ^ d'
  -- a bound on the length of the queries
  let N : Polynomial ℕ := F + (F + 1) * (8 * F + 11)
  -- a bound on the size of the circuits for `SAT` up to that length
  let S : Polynomial ℕ := Polynomial.C c * (N + 1) ^ d
  -- the length of a block and of the advice string
  let W : Polynomial ℕ := S + (N + S) + S * (3 + 2 * (N + S))
  let P : Polynomial ℕ := (N + 1) * W
  have hF (a : α) (u : List Bool) (hu : u.length = p.eval (enc a).length) :
      (encCNF (f (a, u))).length ≤ F.eval (enc a).length := by
    refine (hf' (a, u)).trans (le_of_eq ?_)
    simp only [length_encPair, encBits_apply, hu, F, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  have hN (n : ℕ) : N.eval n = SAT.queryBound (F.eval n) := by
    simp [N, SAT.queryBound, Polynomial.eval_add, Polynomial.eval_mul]
  have hS (n : ℕ) : S.eval n = c * (N.eval n + 1) ^ d := by simp [S]
  have hW (n : ℕ) : W.eval n = certLength (N.eval n) (S.eval n) := by
    simp [W, certLength]
  have hP (n : ℕ) : P.eval n = (N.eval n + 1) * certLength (N.eval n) (S.eval n) := by
    simp [P, hW]
  have hsize (n : ℕ) : ∀ m ≤ N.eval n, (C m).size ≤ S.eval n := fun m hm =>
    ((hC m).1.trans (hcd m)).trans (by
      rw [hS]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) d))
  refine ⟨[P, p], KarpLipton.verifier enc f S W P, rfl,
    .of_tidy (KarpLipton.computableTidilyInPolyTime_verifier hf.tidy S W P), fun a => ?_⟩
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
    refine ⟨familyAdvice (N.eval n) (S.eval n) C,
      (length_familyAdvice (hsize n)).trans (hP n).symm, fun u hu => ?_⟩
    rw [KarpLipton.verifier_append a ((length_familyAdvice (hsize n)).trans (hP n).symm), hW]
    refine SAT.verifier_search (fun ψ hψ => ?_) (h u hu)
    have hlen : (encCNF ψ).length ≤ N.eval n := by
      rw [hN]
      exact hψ.trans (SAT.queryBound_mono (hF a u hu))
    rw [evalAdvice_familyAdvice (hsize n) hlen, (hC _).2, single_apply,
      Language.slice_eq_true_iff, hSAT]
    simp only [Fin.getElem_fin, List.ofFn_getElem]
  · rintro ⟨w₁, hw₁, h⟩ u hu
    have := h u hu
    rw [KarpLipton.verifier_append a hw₁] at this
    exact ⟨_, this⟩

/-- **Karp–Lipton, `Π₂ = Σ₂`.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then `Π₂ = Σ₂`, for every encoding of instances. -/
theorem PiP_two_eq_SigmaP_two_of_SAT (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    (enc : α ↪ List Bool) : PiP 2 enc = SigmaP 2 enc := by
  refine (PiP_two_subset_SigmaP_two_of_SAT hSAT enc).antisymm fun A hA => ?_
  simpa using compl_mem_PiP_of_mem_SigmaP
    (PiP_two_subset_SigmaP_two_of_SAT hSAT enc (compl_mem_PiP_of_mem_SigmaP hA))

/-! ### The collapse -/

/-- **The Karp–Lipton theorem.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then the polynomial hierarchy collapses to its second level: `PH = Σ₂`, for
every encoding of instances. -/
theorem PH_eq_SigmaP_two_of_SAT (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by norm_num) fun encB =>
    PiP_two_subset_SigmaP_two_of_SAT hSAT encB

/-- **The Karp–Lipton theorem, `NP ⊆ P/poly ⇒ PH = Σ₂`.** If every problem in `NP`, with any
encoding of its instances, is the preimage of a language in `P/poly`, then `PH = Σ₂`, for every
encoding of instances. -/
theorem PH_eq_SigmaP_two_of_NP_subset_PPoly
    (h : ∀ {β : Type} (encB : β ↪ List Bool), ∀ B ∈ NP encB, ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_SAT (h encCNF SAT SAT.mem_NP)

/-! ### Nonuniform quantifier elimination and `PH ⊆ P/poly` -/

/-- **Preimages of `P/poly` are closed under polynomial-time reductions.** If `A` reduces to `B`
in polynomial time and `B` is the preimage under `encB` of a language in `P/poly`, then `A` is
the preimage under `enc` of a language in `P/poly`: evaluating the circuits for `B` up to the
polynomial output-length bound of the reduction from an advice string is polynomial-time, and
hardwiring the advice string (`PPoly.of_advice`) gives circuits of polynomial size. -/
theorem PolyTimeReducible.exists_mem_PPoly {β : Type} {encB : β ↪ List Bool} {A : Set α}
    {B : Set β} (hAB : PolyTimeReducible enc encB A B)
    (hB : ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L := by
  obtain ⟨f, hf, hiff⟩ := hAB
  obtain ⟨L_B, hL_B, hLB⟩ := hB
  obtain ⟨C, s, hs, hC⟩ := mem_PPoly_iff_exists_circuits.1 hL_B
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.1 hs
  obtain ⟨c', d', hf'⟩ := hf.tidy.polyBounded_length.exists_le
  let N : Polynomial ℕ := Polynomial.C c' * (Polynomial.X + 1) ^ d'
  let S : Polynomial ℕ := Polynomial.C c * (N + 1) ^ d
  let W : Polynomial ℕ := S + (N + S) + S * (3 + 2 * (N + S))
  let P : Polynomial ℕ := (N + 1) * W
  have hN (a : α) : (encB (f a)).length ≤ N.eval (enc a).length := by
    refine (hf' a).trans (le_of_eq ?_)
    simp [N]
  have hS (n : ℕ) : S.eval n = c * (N.eval n + 1) ^ d := by simp [S]
  have hW (n : ℕ) : W.eval n = certLength (N.eval n) (S.eval n) := by simp [W, certLength]
  have hP (n : ℕ) : P.eval n = (N.eval n + 1) * certLength (N.eval n) (S.eval n) := by
    simp [P, hW]
  have hsize (n : ℕ) : ∀ m ≤ N.eval n, (C m).size ≤ S.eval n := fun m hm =>
    ((hC m).1.trans (hcd m)).trans (by
      rw [hS]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) d))
  let g : List Bool × α → Bool := fun x =>
    evalAdvice (S.eval (enc x.2).length) (W.eval (enc x.2).length) x.1 (encB (f x.2))
  have hg : ComputableTidilyInPolyTime g (encPair encBits enc) encBool := by
    have hn : ComputableTidilyInPolyTime (fun x : List Bool × α => (enc x.2).length)
        (encPair encBits enc) encUnary :=
      (encoding_length enc).comp (snd _ _)
    exact (computableInPolyTime_evalAdvice (.of_tidy ((unary_eval S).comp hn))
      (.of_tidy ((unary_eval W).comp hn)) (.of_tidy (fst _ _))
        (.of_tidy ((encode encB).comp (hf.tidy.comp (snd _ _))))).tidy
  obtain ⟨M, hM, hgM⟩ := PPoly.exists_of_polyTime (.of_tidy hg)
  let α_adv : ℕ → List Bool := fun n => familyAdvice (N.eval n) (S.eval n) C
  have hα : PolynomiallyBounded fun n => (α_adv n).length := by
    have hlen : (fun n => (α_adv n).length) = fun n => P.eval n :=
      funext fun n => (length_familyAdvice (hsize n)).trans (hP n).symm
    rw [hlen]
    fun_prop
  let L : Language Bool := {x : List Bool | frame (α_adv x.length) ++ x ∈ M}
  refine ⟨L, PPoly.of_advice hM α_adv hα (fun _ => Iff.rfl), fun a => ?_⟩
  change a ∈ A ↔ frame (α_adv (enc a).length) ++ enc a ∈ M
  have hgM' := hgM (α_adv (enc a).length, a)
  rw [encPair_apply, encBits_apply] at hgM'
  rw [hiff a, hLB (f a), ← hgM']
  dsimp only [g, α_adv]
  rw [hW, evalAdvice_familyAdvice (hsize (enc a).length) (hN a), (hC _).2, single_apply,
    Language.slice_eq_true_iff]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

/-- `P/poly` is closed under polynomial-time reductions on languages over `Bool`. -/
theorem PolyTimeReducible.mem_PPoly {A B : Language Bool}
    (hAB : PolyTimeReducible encBits encBits (A : Set (List Bool)) (B : Set (List Bool)))
    (hB : B ∈ PPoly) : A ∈ PPoly := by
  obtain ⟨L, hL, h⟩ := hAB.exists_mem_PPoly ⟨B, hB, fun _ => Iff.rfl⟩
  exact (Language.ext fun w => h w : A = L) ▸ hL

/-- **Nonuniform quantifier elimination.** If every language in `NP` over `Bool` is in `P/poly`
and `M` is in `P/poly`, then the language of words `x` for which `frame x ++ w ∈ M` for some `w` of
length `p |x|` is in `P/poly`: replacing `M` by an advice string listing its circuits up to length
`2 |x| + 1 + p |x|` turns the existential quantifier over `w` into a language in `NP`, and
hardwiring the advice string (`Cslib.Circuits.Boolean.PPoly.of_advice`) gives circuits of
polynomial size [Karp and Lipton, Section 3][KarpLipton1980]. -/
theorem mem_PPoly_of_exists_frame_append
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    {M : Language Bool} (hM : M ∈ PPoly) (p : Polynomial ℕ) :
    ({x : List Bool | ∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M} :
      Language Bool) ∈ PPoly := by
  obtain ⟨C, s, hs, hC⟩ := mem_PPoly_iff_exists_circuits.1 hM
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.1 hs
  let N : Polynomial ℕ := 2 * Polynomial.X + 1 + p
  let S : Polynomial ℕ := Polynomial.C c * (N + 1) ^ d
  let W : Polynomial ℕ := S + (N + S) + S * (3 + 2 * (N + S))
  let P : Polynomial ℕ := (N + 1) * W
  have hN (n : ℕ) : N.eval n = 2 * n + 1 + p.eval n := by
    simp [N, Polynomial.eval_add, Polynomial.eval_mul]
  have hS (n : ℕ) : S.eval n = c * (N.eval n + 1) ^ d := by simp [S]
  have hW (n : ℕ) : W.eval n = certLength (N.eval n) (S.eval n) := by simp [W, certLength]
  have hP (n : ℕ) : P.eval n = (N.eval n + 1) * certLength (N.eval n) (S.eval n) := by
    simp [P, hW]
  have hsize (n : ℕ) : ∀ m ≤ N.eval n, (C m).size ≤ S.eval n := fun m hm =>
    ((hC m).1.trans (hcd m)).trans (by
      rw [hS]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) d))
  let V : List Bool × List Bool → Bool := fun z =>
    evalAdvice (S.eval (dropFrame z.1).length) (W.eval (dropFrame z.1).length) (unframe z.1)
      (frame (dropFrame z.1) ++ z.2.take (p.eval (dropFrame z.1).length))
  have hV : ComputableTidilyInPolyTime V (encPair encBits encBits) encBool := by
    have hx : ComputableTidilyInPolyTime (fun z : List Bool × List Bool => dropFrame z.1)
        (encPair encBits encBits) encBits := dropFrame.comp (fst _ _)
    have hu : ComputableTidilyInPolyTime (fun z : List Bool × List Bool => unframe z.1)
        (encPair encBits encBits) encBits := unframe.comp (fst _ _)
    have hn : ComputableTidilyInPolyTime (fun z : List Bool × List Bool => (dropFrame z.1).length)
        (encPair encBits encBits) encUnary := length_bits.comp hx
    have hw : ComputableTidilyInPolyTime
        (fun z : List Bool × List Bool => z.2.take (p.eval (dropFrame z.1).length))
        (encPair encBits encBits) encBits :=
      bitsTakeWithInput (snd _ _) ((unary_eval p).comp hn)
    exact (computableInPolyTime_evalAdvice (.of_tidy ((unary_eval S).comp hn))
      (.of_tidy ((unary_eval W).comp hn)) (.of_tidy hu)
        (.of_tidy (bitsAppend ((bitsFrame encBits).comp hx) hw))).tidy
  let D : Language Bool := {z : List Bool | ∃ w : List Bool, w.length = p.eval z.length ∧
    V (z, w) = true}
  have hD : D ∈ PPoly := hNP D ⟨p, V, .of_tidy hV, fun _ => Iff.rfl⟩
  let α_adv : ℕ → List Bool := fun n => familyAdvice (N.eval n) (S.eval n) C
  have hα : PolynomiallyBounded fun n => (α_adv n).length := by
    have hlen : (fun n => (α_adv n).length) = fun n => P.eval n :=
      funext fun n => (length_familyAdvice (hsize n)).trans (hP n).symm
    rw [hlen]
    fun_prop
  refine PPoly.of_advice hD α_adv hα fun x => ?_
  change (∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M) ↔
    (∃ w : List Bool, w.length = p.eval (frame (α_adv x.length) ++ x).length ∧
      V (frame (α_adv x.length) ++ x, w) = true)
  have hle : p.eval x.length ≤ p.eval (frame (α_adv x.length) ++ x).length :=
    p.eval_mono (by simp)
  have hV_frame (w : List Bool) (hw : w.length = p.eval x.length) :
      evalAdvice (S.eval x.length) (W.eval x.length) (α_adv x.length) (frame x ++ w) = true ↔
        frame x ++ w ∈ M := by
    have hlen : (frame x ++ w).length ≤ N.eval x.length := by
      simp [hN, hw]
    rw [hW, evalAdvice_familyAdvice (hsize x.length) hlen, (hC _).2, single_apply,
      Language.slice_eq_true_iff]
    simp only [Fin.getElem_fin, List.ofFn_getElem]
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

/-- If every language in `NP` over `Bool` is in `P/poly`, then every problem in `NP`, with any
encoding of its instances, is the preimage of a language in `P/poly`. -/
theorem exists_mem_PPoly_of_mem_NP
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    {A : Set α} (hA : A ∈ NP enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L := by
  obtain ⟨p, V, hV, hAV⟩ := hA
  obtain ⟨M, hM, hVM⟩ := PPoly.exists_of_polyTime hV
  refine ⟨{x : List Bool | ∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M},
    mem_PPoly_of_exists_frame_append hNP hM p, fun a => (hAV a).trans ?_⟩
  exact exists_congr fun w => and_congr_right fun _ => by
    rw [hVM (a, w), encPair_apply, encBits_apply]

/-- If `SAT` has circuits of polynomial size, then every problem in `NP`, with any encoding of its
instances, is the preimage of a language in `P/poly`. -/
theorem exists_mem_PPoly_of_mem_NP_of_SAT
    (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    {A : Set α} (hA : A ∈ NP enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  (CookLevin.SAT_npHard enc A hA).exists_mem_PPoly hSAT

/-- **Equivalence of `NP ⊆ P/poly` formulations (`encB` vs. `encBits`).** Having polynomial-size
circuits for every problem in `NP` under every instance encoding is equivalent to having
polynomial-size circuits for every language in `NP encBits`. -/
theorem forall_mem_NP_exists_mem_PPoly_iff :
    (∀ {β : Type} (encB : β ↪ List Bool), ∀ B ∈ NP encB, ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L) ↔
      (∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly) := by
  refine ⟨fun h B hB => ?_, fun h _ _ _ hB => exists_mem_PPoly_of_mem_NP h hB⟩
  obtain ⟨L, hL, hBL⟩ := h encBits (B : Set (List Bool)) hB
  exact (Language.ext fun w => hBL w : B = L) ▸ hL

/-- **Equivalence of `NP ⊆ P/poly` formulations (`encB` vs. `SAT`).** Having polynomial-size
circuits for every problem in `NP` under every instance encoding is equivalent to `SAT` having
circuits of polynomial size. -/
theorem forall_mem_NP_exists_mem_PPoly_iff_SAT :
    (∀ {β : Type} (encB : β ↪ List Bool), ∀ B ∈ NP encB, ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L) ↔
      (∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L) :=
  ⟨fun h => h encCNF SAT SAT.mem_NP, fun hSAT _ _ _ hB => exists_mem_PPoly_of_mem_NP_of_SAT hSAT hB⟩

/-- **Equivalence of `NP ⊆ P/poly` formulations (`encBits` vs. `SAT`).** Having polynomial-size
circuits for every language in `NP encBits` is equivalent to `SAT` having circuits of polynomial
size. -/
theorem forall_mem_NP_encBits_mem_PPoly_iff_SAT :
    (∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly) ↔
      (∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L) :=
  forall_mem_NP_exists_mem_PPoly_iff.symm.trans forall_mem_NP_exists_mem_PPoly_iff_SAT

/-- **The Karp–Lipton theorem, `NP ⊆ P/poly ⇒ PH = Σ₂`** (from the language-level `NP`
hypothesis on `encBits`). If every language in `NP` over `Bool` is in `P/poly`, then `PH = Σ₂`,
for every encoding of instances. -/
theorem PH_eq_SigmaP_two_of_NP_encBits_subset_PPoly
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_NP_subset_PPoly (forall_mem_NP_exists_mem_PPoly_iff.2 hNP)

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ Σₖ ⊆ P/poly`.** If every language in `NP` over `Bool` is in
`P/poly`, then every problem in `Σₖ`, with any encoding of its instances, is the preimage of a
language in `P/poly` [Karp and Lipton, Section 3][KarpLipton1980],
[Arora and Barak, Section 6.4][AroraBarak09]. -/
theorem exists_mem_PPoly_of_mem_SigmaP
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly) {k : ℕ} :
    ∀ {α : Type} {enc : α ↪ List Bool} {A : Set α}, A ∈ SigmaP k enc →
      ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L := by
  induction k with
  | zero =>
    intro α enc A hA
    rw [SigmaP_zero] at hA
    exact PPoly.exists_of_mem_P hA
  | succ k ih =>
    intro α enc A hA
    obtain ⟨p, B, hB, hAB⟩ := exists_mem_PiP_of_mem_SigmaP_succ hA
    obtain ⟨M₀, hM₀, hBM₀⟩ := ih (compl_mem_SigmaP_of_mem_PiP hB)
    have hM : M₀ᶜ ∈ PPoly := PPoly.compl hM₀
    refine ⟨{x : List Bool | ∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M₀ᶜ},
      mem_PPoly_of_exists_frame_append hNP hM p, fun a => (hAB a).trans ?_⟩
    exact exists_congr fun w => and_congr_right fun _ => by
      have := (hBM₀ (a, w)).not
      rwa [Set.mem_compl_iff, Classical.not_not, encPair_apply, encBits_apply] at this

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ Πₖ ⊆ P/poly`.** If every language in `NP` over `Bool` is in
`P/poly`, then every problem in `Πₖ`, with any encoding of its instances, is the preimage of a
language in `P/poly`. -/
theorem exists_mem_PPoly_of_mem_PiP
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly) {k : ℕ}
    {A : Set α} (hA : A ∈ PiP k enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L := by
  obtain ⟨L, hL, hAL⟩ := exists_mem_PPoly_of_mem_SigmaP hNP (compl_mem_SigmaP_of_mem_PiP hA)
  refine ⟨Lᶜ, PPoly.compl hL, fun a => ?_⟩
  have := (hAL a).not
  rwa [Set.mem_compl_iff, Classical.not_not] at this

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ PH ⊆ P/poly`.** If every language in `NP` over `Bool` is in
`P/poly`, then every problem in `PH`, with any encoding of its instances, is the preimage of a
language in `P/poly` [Karp and Lipton, Section 3][KarpLipton1980],
[Arora and Barak, Section 6.4][AroraBarak09]. -/
theorem exists_mem_PPoly_of_mem_PH
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    {A : Set α} (hA : A ∈ PH enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L := by
  obtain ⟨k, hA⟩ := mem_PH.1 hA
  exact exists_mem_PPoly_of_mem_SigmaP hNP hA

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ Σₖ ⊆ P/poly`** (arbitrary-encoding `NP` hypothesis). -/
theorem exists_mem_PPoly_of_mem_SigmaP_of_NP_subset_PPoly {k : ℕ} {A : Set α}
    (h : ∀ {β : Type} (encB : β ↪ List Bool), ∀ B ∈ NP encB,
      ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L)
    (hA : A ∈ SigmaP k enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  exists_mem_PPoly_of_mem_SigmaP (forall_mem_NP_exists_mem_PPoly_iff.1 h) hA

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ Πₖ ⊆ P/poly`** (arbitrary-encoding `NP` hypothesis). -/
theorem exists_mem_PPoly_of_mem_PiP_of_NP_subset_PPoly {k : ℕ} {A : Set α}
    (h : ∀ {β : Type} (encB : β ↪ List Bool), ∀ B ∈ NP encB,
      ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L)
    (hA : A ∈ PiP k enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  exists_mem_PPoly_of_mem_PiP (forall_mem_NP_exists_mem_PPoly_iff.1 h) hA

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ PH ⊆ P/poly`** (arbitrary-encoding `NP` hypothesis). -/
theorem exists_mem_PPoly_of_mem_PH_of_NP_subset_PPoly {A : Set α}
    (h : ∀ {β : Type} (encB : β ↪ List Bool), ∀ B ∈ NP encB,
      ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L)
    (hA : A ∈ PH enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  exists_mem_PPoly_of_mem_PH (forall_mem_NP_exists_mem_PPoly_iff.1 h) hA

/-- **Karp–Lipton, `SAT ∈ P/poly ⇒ Σₖ ⊆ P/poly`.** If `SAT` has circuits of polynomial size, then
every problem in `Σₖ`, with any encoding of its instances, is the preimage of a language in
`P/poly`. -/
theorem exists_mem_PPoly_of_mem_SigmaP_of_SAT {k : ℕ} {A : Set α}
    (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    (hA : A ∈ SigmaP k enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  exists_mem_PPoly_of_mem_SigmaP_of_NP_subset_PPoly
    (forall_mem_NP_exists_mem_PPoly_iff_SAT.2 hSAT) hA

/-- **Karp–Lipton, `SAT ∈ P/poly ⇒ Πₖ ⊆ P/poly`.** If `SAT` has circuits of polynomial size, then
every problem in `Πₖ`, with any encoding of its instances, is the preimage of a language in
`P/poly`. -/
theorem exists_mem_PPoly_of_mem_PiP_of_SAT {k : ℕ} {A : Set α}
    (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    (hA : A ∈ PiP k enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  exists_mem_PPoly_of_mem_PiP_of_NP_subset_PPoly
    (forall_mem_NP_exists_mem_PPoly_iff_SAT.2 hSAT) hA

/-- **Karp–Lipton, `SAT ∈ P/poly ⇒ PH ⊆ P/poly`.** If `SAT` has circuits of polynomial size, then
every problem in `PH`, with any encoding of its instances, is the preimage of a language in
`P/poly`. -/
theorem exists_mem_PPoly_of_mem_PH_of_SAT {A : Set α}
    (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    (hA : A ∈ PH enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  exists_mem_PPoly_of_mem_PH_of_NP_subset_PPoly
    (forall_mem_NP_exists_mem_PPoly_iff_SAT.2 hSAT) hA

/-- **`NP ⊆ P/poly ⇒ Σₖ ⊆ P/poly`** for languages over `Bool`, with words encoded as themselves. -/
theorem mem_PPoly_of_mem_SigmaP_of_NP_subset_PPoly {k : ℕ} {A : Language Bool}
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    (hA : (A : Set (List Bool)) ∈ SigmaP k encBits) : A ∈ PPoly := by
  obtain ⟨L, hL, h⟩ := exists_mem_PPoly_of_mem_SigmaP hNP hA
  exact (Language.ext fun w => h w : A = L) ▸ hL

/-- **`NP ⊆ P/poly ⇒ Πₖ ⊆ P/poly`** for languages over `Bool`, with words encoded as themselves. -/
theorem mem_PPoly_of_mem_PiP_of_NP_subset_PPoly {k : ℕ} {A : Language Bool}
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    (hA : (A : Set (List Bool)) ∈ PiP k encBits) : A ∈ PPoly := by
  obtain ⟨L, hL, h⟩ := exists_mem_PPoly_of_mem_PiP hNP hA
  exact (Language.ext fun w => h w : A = L) ▸ hL

/-- **`NP ⊆ P/poly ⇒ PH ⊆ P/poly`** for languages over `Bool`, with words encoded as themselves. -/
theorem mem_PPoly_of_mem_PH_of_NP_subset_PPoly {A : Language Bool}
    (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    (hA : (A : Set (List Bool)) ∈ PH encBits) : A ∈ PPoly := by
  obtain ⟨L, hL, h⟩ := exists_mem_PPoly_of_mem_PH hNP hA
  exact (Language.ext fun w => h w : A = L) ▸ hL

/-- **`NP ⊆ P/poly ⇒ Σₖ ⊆ P/poly`** as a set inclusion on languages over `Bool`. -/
theorem SigmaP_subset_PPoly_of_NP_subset_PPoly
    (hNP : {B : Language Bool | (B : Set (List Bool)) ∈ NP encBits} ⊆ PPoly) (k : ℕ) :
    {A : Language Bool | (A : Set (List Bool)) ∈ SigmaP k encBits} ⊆ PPoly :=
  fun _ hA => mem_PPoly_of_mem_SigmaP_of_NP_subset_PPoly (fun _ hB => hNP hB) hA

/-- **`NP ⊆ P/poly ⇒ Πₖ ⊆ P/poly`** as a set inclusion on languages over `Bool`. -/
theorem PiP_subset_PPoly_of_NP_subset_PPoly
    (hNP : {B : Language Bool | (B : Set (List Bool)) ∈ NP encBits} ⊆ PPoly) (k : ℕ) :
    {A : Language Bool | (A : Set (List Bool)) ∈ PiP k encBits} ⊆ PPoly :=
  fun _ hA => mem_PPoly_of_mem_PiP_of_NP_subset_PPoly (fun _ hB => hNP hB) hA

/-- **`NP ⊆ P/poly ⇒ PH ⊆ P/poly`** as a set inclusion on languages over `Bool`. -/
theorem PH_subset_PPoly_of_NP_subset_PPoly
    (hNP : {B : Language Bool | (B : Set (List Bool)) ∈ NP encBits} ⊆ PPoly) :
    {A : Language Bool | (A : Set (List Bool)) ∈ PH encBits} ⊆ PPoly :=
  fun _ hA => mem_PPoly_of_mem_PH_of_NP_subset_PPoly (fun _ hB => hNP hB) hA

end Cslib.Complexity

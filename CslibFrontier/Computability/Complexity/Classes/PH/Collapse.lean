/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Extension
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Collapses of the polynomial hierarchy

If `Πₖ ⊆ Σₖ` for some `k ≥ 1`, for problems with any encoding of their instances, then the
polynomial hierarchy collapses to its level `k`: `PH = Σₖ`
(`Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`) [Arora and Barak, Theorem 5.4][AroraBarak09],
[Stockmeyer][Stockmeyer1976]. Consequently `NP = coNP` collapses the hierarchy to `NP`
(`Cslib.Complexity.PH_eq_NP_of_coNP_subset_NP`) and `P = NP` collapses it to `P`
(`Cslib.Complexity.PH_eq_P_of_NP_subset_P`).

The collapse goes one level at a time (`Cslib.Complexity.SigmaP_succ_subset_SigmaP`). A problem
`A` in `Σₖ₊₁` is the projection of a problem `B` in `Πₖ` on pairs `(a, w₁)` of an instance and a
first certificate (`Cslib.Complexity.exists_mem_PiP_of_mem_SigmaP_succ`). Then `B` is in `Σₖ`, and
the existential quantifier over `w₁` merges with the first quantifier of `B`, whose block lengths
are polynomials in the length of the encoded pair `(a, w₁)`, hence in the length of `enc a`.

Every problem in `Σₖ` or `Πₖ` on an explicit encoding `enc` is the preimage `enc ⁻¹' B` of a
raw-word language `B` in `Σₖ` or `Πₖ` on `encBits`, obtained by extending its polynomial-time
verifier to all bit words (`Cslib.Complexity.exists_mem_SigmaP_encBits_preimage`,
`Cslib.Complexity.exists_mem_PiP_encBits_preimage`). Consequently, the fixed-domain bit-language
hypotheses `PiP k encBits = SigmaP k encBits`, `SigmaP (k + 1) encBits = SigmaP k encBits`,
`NP encBits = coNP encBits` and `P encBits = NP encBits` transfer to every instance encoding and
collapse `PH` (`Cslib.Complexity.PH_eq_SigmaP_of_PiP_encBits_eq_SigmaP`,
`Cslib.Complexity.PH_eq_P_of_P_encBits_eq_NP`) [Arora and Barak, Theorem 5.6][AroraBarak07],
[Goldreich, Proposition 3.10][Goldreich2007DraftR2]. Conversely, `PH = Σₖ` forces `Σₖ₊₁ = Σₖ` and
`Πₖ = Σₖ` (`Cslib.Complexity.SigmaP_succ_eq_SigmaP_of_PH_eq_SigmaP`,
`Cslib.Complexity.PiP_eq_SigmaP_of_PH_eq_SigmaP`).

## Main results

* `Cslib.Complexity.mem_SigmaP_succ_iff`: `Σₖ₊₁` consists of the projections of `Πₖ`.
* `Cslib.Complexity.SigmaP_succ_subset_SigmaP`: one level of the collapse.
* `Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`: `Πₖ ⊆ Σₖ` collapses `PH` to `Σₖ`.
* `Cslib.Complexity.PH_eq_NP_of_coNP_subset_NP`: `NP = coNP` collapses `PH` to `NP`.
* `Cslib.Complexity.PH_eq_P_of_NP_subset_P`: `P = NP` collapses `PH` to `P`.
* `Cslib.Complexity.PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP`: `Σₖ₊₁ ⊆ Σₖ` collapses `PH` to
  `Σₖ`, for every `k`.
* `Cslib.Complexity.exists_mem_SigmaP_encBits_preimage`,
  `Cslib.Complexity.exists_mem_PiP_encBits_preimage`: every `Σₖ`/`Πₖ` problem is the preimage
  along `enc` of a raw-word `Σₖ`/`Πₖ` language on `encBits`.
* `Cslib.Complexity.PH_eq_SigmaP_of_PiP_encBits_eq_SigmaP`,
  `Cslib.Complexity.PH_eq_SigmaP_of_SigmaP_succ_encBits_eq_SigmaP`,
  `Cslib.Complexity.PH_eq_NP_of_NP_encBits_eq_coNP`,
  `Cslib.Complexity.PH_eq_P_of_P_encBits_eq_NP`: fixed-domain `encBits` collapse corollaries.
* `Cslib.Complexity.SigmaP_succ_eq_SigmaP_of_PH_eq_SigmaP`,
  `Cslib.Complexity.PiP_eq_SigmaP_of_PH_eq_SigmaP`,
  `Cslib.Complexity.forall_PH_eq_SigmaP_iff_PiP_encBits_eq_SigmaP`,
  `Cslib.Complexity.forall_PH_eq_SigmaP_iff_SigmaP_succ_encBits_eq_SigmaP`: Goldreich's converse
  and equivalences.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2007DraftR2]
* [L. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-! ### One level of the collapse -/

variable {α : Type} {enc : α ↪ List Bool}

/-- A word of length `a + b` is a word of length `a` followed by one of length `b`. -/
private theorem exists_length_add_iff {a b : ℕ} {P : List Bool → Prop} :
    (∃ w : List Bool, w.length = a + b ∧ P w) ↔
      ∃ u : List Bool, u.length = a ∧ ∃ v : List Bool, v.length = b ∧ P (u ++ v) := by
  constructor
  · rintro ⟨w, hw, hP⟩
    refine ⟨w.take a, by simp [hw], w.drop a, by simp [hw], by rwa [List.take_append_drop]⟩
  · rintro ⟨u, hu, v, hv, hP⟩
    exact ⟨u ++ v, by simp [hu, hv], hP⟩

/-- **`Σₖ` is closed under polynomially bounded existential quantification**, for `k ≥ 1`: if
`B ∈ Σₖ` as a problem on pairs of an instance and a word, then so is its projection along words of
length `p |enc a|`. The new quantifier merges with the first quantifier of `B`, whose block lengths
are polynomials in the length of the encoded pair, hence in `|enc a|`. -/
theorem mem_SigmaP_of_exists {k : ℕ} (hk : 1 ≤ k) {B : Set (α × List Bool)}
    (hB : B ∈ SigmaP k (encPair enc encBits)) (p : Polynomial ℕ) :
    {a | ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ B} ∈ SigmaP k enc := by
  obtain ⟨rs, V', hrs, hV', hB'⟩ := hB
  obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one
    (show rs.length = (k - 1) + 1 by omega)
  let L : Polynomial ℕ := 2 * Polynomial.X + 1 + p
  have hL (a : α) (w : List Bool) (hw : w.length = p.eval (enc a).length) :
      (encPair enc encBits (a, w)).length = L.eval (enc a).length := by
    simp only [length_encPair, encBits_apply, hw, L, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  refine ⟨(p + r.comp L) :: rs.map (·.comp L),
    fun x => V' ((x.1, x.2.take (p.eval (enc x.1).length)), x.2.drop (p.eval (enc x.1).length)),
    by simp only [List.length_cons, List.length_map]; omega, ?_, fun a => ?_⟩
  · have hn : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      ((ComputableInPolyTime.unary_eval p).comp
        (ComputableInPolyTime.encoding_length enc)).comp (.fst _ _)
    exact hV'.comp (((ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.bitsTakeWithInput (.snd _ _) hn)).prod
        (ComputableInPolyTime.bitsDropWithInput (.snd _ _) hn))
  · simp only [Set.mem_ofPred_eq, List.map_cons, alternation_true_cons, Polynomial.eval_add,
      Polynomial.eval_comp, List.map_map, Function.comp_def]
    rw [exists_length_add_iff]
    refine exists_congr fun w => and_congr_right fun hw => ?_
    have hmem := hB' (a, w)
    simp only [List.map_cons, alternation_true_cons, hL a w hw] at hmem
    rw [hmem]
    refine exists_congr fun v => and_congr_right fun hv => alternation_congr fun u => ?_
    simp [hw, List.append_assoc]

/-- **`Σₖ₊₁` consists of the projections of `Πₖ`**: the problems `{a | ∃ w, |w| = p |enc a| ∧
(a, w) ∈ B}` for a polynomial `p` and a problem `B` in `Πₖ` on pairs of an instance and a word. -/
theorem mem_SigmaP_succ_iff {k : ℕ} {A : Set α} :
    A ∈ SigmaP (k + 1) enc ↔ ∃ (p : Polynomial ℕ) (B : Set (α × List Bool)),
      B ∈ PiP k (encPair enc encBits) ∧
        A = {a | ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ B} := by
  refine ⟨fun hA => ?_, ?_⟩
  · obtain ⟨p, B, hB, hAB⟩ := exists_mem_PiP_of_mem_SigmaP_succ hA
    exact ⟨p, B, hB, Set.ext hAB⟩
  · rintro ⟨p, B, hB, rfl⟩
    exact mem_SigmaP_of_exists (Nat.le_add_left 1 k) (PiP_subset_SigmaP_succ k hB) p

/-- **One level of the collapse.** If `Πₖ ⊆ Σₖ` for problems on pairs of an instance and a word,
for some `k ≥ 1`, then `Σₖ₊₁ ⊆ Σₖ`: the pairs `(a, w₁)` from which the last `k` quantifiers
accept form a problem in `Πₖ`, hence in `Σₖ`, and the quantifier over `w₁` merges with its first
quantifier (`Cslib.Complexity.mem_SigmaP_of_exists`). -/
theorem SigmaP_succ_subset_SigmaP {k : ℕ} (hk : 1 ≤ k)
    (h : PiP k (encPair enc encBits) ⊆ SigmaP k (encPair enc encBits)) :
    SigmaP (k + 1) enc ⊆ SigmaP k enc := by
  intro A hA
  -- the pairs of an instance and a first certificate from which the last `k` quantifiers accept
  obtain ⟨p, B, hB, rfl⟩ := mem_SigmaP_succ_iff.mp hA
  exact mem_SigmaP_of_exists hk (h hB) p

/-! ### The collapses -/

/-- **`Πₖ ⊆ Σₖ` collapses the polynomial hierarchy to `Σₖ`**, for `k ≥ 1`
[Arora and Barak, Theorem 5.4][AroraBarak09]: if `Πₖ ⊆ Σₖ` for problems with any encoding of their
instances, then `PH = Σₖ`. -/
theorem PH_eq_SigmaP_of_PiP_subset_SigmaP {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), PiP k encB ⊆ SigmaP k encB) :
    PH enc = SigmaP k enc := by
  -- every level from `k` on is within `Σₖ`, for every encoding
  have hlevel (j : ℕ) :
      ∀ {β : Type} (encB : β ↪ List Bool), SigmaP (k + j) encB ⊆ SigmaP k encB := by
    induction j with
    | zero => intro β encB; exact le_rfl
    | succ j ih =>
      intro β encB
      refine (SigmaP_succ_subset_SigmaP (k := k + j) (by omega) fun A hA => ?_).trans
        (ih encB)
      -- `Πₖ₊ⱼ` is the complement of `Σₖ₊ⱼ ⊆ Σₖ`, within `Πₖ ⊆ Σₖ ⊆ Σₖ₊ⱼ`
      have hc : Aᶜ ∈ SigmaP k _ := ih _ (compl_mem_SigmaP_iff.mpr hA)
      exact SigmaP_mono (Nat.le_add_right k j) (h _ (compl_mem_SigmaP_iff.mp hc))
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (SigmaP_subset_PH k)
  rcases le_total j k with hj | hj
  · exact SigmaP_mono hj
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact hlevel i enc

/-- **`NP = coNP` collapses the polynomial hierarchy to `NP`** [Arora and Barak, Theorem 5.4]
[AroraBarak09]. -/
theorem PH_eq_NP_of_coNP_subset_NP (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NP encB) :
    PH enc = NP enc := by
  rw [← SigmaP_one]
  exact PH_eq_SigmaP_of_PiP_subset_SigmaP le_rfl fun encB => by
    rw [PiP_one_eq_coNP, SigmaP_one]
    exact h encB

/-- **`P = NP` collapses the polynomial hierarchy to `P`** [Arora and Barak, Theorem 5.4]
[AroraBarak09]: then `coNP ⊆ NP`, since `P` is closed under complement. -/
theorem PH_eq_P_of_NP_subset_P (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) :
    PH enc = P enc := by
  have hNP : ∀ {β : Type} (encB : β ↪ List Bool), NP encB = P encB := fun encB =>
    (h encB).antisymm (SigmaP_one ▸ SigmaP_zero ▸ SigmaP_mono (Nat.zero_le 1))
  rw [PH_eq_NP_of_coNP_subset_NP fun encB A hA => ?_, hNP]
  obtain ⟨f, hf, hfA⟩ := h encB hA
  rw [hNP]
  exact ⟨fun a => !f a, (ComputableInPolyTime.bool_not.comp hf), fun a => by
    simpa using (hfA a).not⟩

/-- **`Σₖ₊₁ ⊆ Σₖ` collapses the polynomial hierarchy to `Σₖ`**, for every `k`: then
`Πₖ ⊆ Σₖ₊₁ ⊆ Σₖ`, and for `k = 0` the hypothesis is `NP ⊆ P`. -/
theorem PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP {k : ℕ}
    (h : ∀ {β : Type} (encB : β ↪ List Bool), SigmaP (k + 1) encB ⊆ SigmaP k encB) :
    PH enc = SigmaP k enc := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [SigmaP_zero]
    exact PH_eq_P_of_NP_subset_P fun encB => by
      simpa only [zero_add, SigmaP_one, SigmaP_zero] using h encB
  · exact PH_eq_SigmaP_of_PiP_subset_SigmaP hk fun encB =>
      (PiP_subset_SigmaP_succ k).trans (h encB)

/-! ### Raw-word transfer and fixed-domain collapses -/

/-- Pulling a raw-word `Σₖ` language on `encBits` back along `enc` gives a `Σₖ` problem on
`enc`. -/
theorem preimage_enc_mem_SigmaP {k : ℕ} {B : Set (List Bool)} (hB : B ∈ SigmaP k encBits) :
    enc ⁻¹' B ∈ SigmaP k enc := by
  obtain ⟨ps, V, hps, hV, hB⟩ := hB
  exact ⟨ps, fun x => V (enc x.1, x.2), hps,
    hV.comp (ComputableInPolyTime.of_eq fun _ => rfl), fun a => hB (enc a)⟩

/-- Pulling a raw-word `Πₖ` language on `encBits` back along `enc` gives a `Πₖ` problem on
`enc`. -/
theorem preimage_enc_mem_PiP {k : ℕ} {B : Set (List Bool)} (hB : B ∈ PiP k encBits) :
    enc ⁻¹' B ∈ PiP k enc := by
  obtain ⟨ps, V, hps, hV, hB⟩ := hB
  exact ⟨ps, fun x => V (enc x.1, x.2), hps,
    hV.comp (ComputableInPolyTime.of_eq fun _ => rfl), fun a => hB (enc a)⟩

/-- **Raw-word preimage representation for `Σₖ`:** every `A ∈ SigmaP k enc` is `enc ⁻¹' B` for a
raw-word language `B ∈ SigmaP k encBits`. -/
theorem exists_mem_SigmaP_encBits_preimage {k : ℕ} {A : Set α} (hA : A ∈ SigmaP k enc) :
    ∃ B ∈ SigmaP k encBits, enc ⁻¹' B = A := by
  obtain ⟨ps, V, hps, hV, hAV⟩ := hA
  obtain ⟨W, hW, hWV⟩ := hV.exists_pair_bool_extension
  refine ⟨{u | Alternation true (ps.map fun p => p.eval u.length) fun w => W (u, w) = true},
    ⟨ps, W, hps, hW, fun _ => Iff.rfl⟩, Set.ext fun a => ?_⟩
  rw [Set.mem_preimage, Set.mem_ofPred_eq, hAV a]
  exact alternation_congr fun w => by rw [hWV a w]

/-- **Raw-word preimage representation for `Πₖ`:** every `A ∈ PiP k enc` is `enc ⁻¹' B` for a
raw-word language `B ∈ PiP k encBits`. -/
theorem exists_mem_PiP_encBits_preimage {k : ℕ} {A : Set α} (hA : A ∈ PiP k enc) :
    ∃ B ∈ PiP k encBits, enc ⁻¹' B = A := by
  obtain ⟨B, hB, hBA⟩ := exists_mem_SigmaP_encBits_preimage (compl_mem_SigmaP_iff.mpr hA)
  exact ⟨Bᶜ, compl_mem_PiP_of_mem_SigmaP hB, by rw [Set.preimage_compl, hBA, compl_compl]⟩

/-- `A ∈ SigmaP k enc` iff `A` is the preimage along `enc` of a language in `SigmaP k encBits`. -/
theorem mem_SigmaP_iff_exists_encBits {k : ℕ} {A : Set α} :
    A ∈ SigmaP k enc ↔ ∃ B ∈ SigmaP k encBits, enc ⁻¹' B = A :=
  ⟨exists_mem_SigmaP_encBits_preimage, fun ⟨_, hB, hBA⟩ => hBA ▸ preimage_enc_mem_SigmaP hB⟩

/-- `A ∈ PiP k enc` iff `A` is the preimage along `enc` of a language in `PiP k encBits`. -/
theorem mem_PiP_iff_exists_encBits {k : ℕ} {A : Set α} :
    A ∈ PiP k enc ↔ ∃ B ∈ PiP k encBits, enc ⁻¹' B = A :=
  ⟨exists_mem_PiP_encBits_preimage, fun ⟨_, hB, hBA⟩ => hBA ▸ preimage_enc_mem_PiP hB⟩

/-- `A ∈ PH enc` iff `A` is the preimage along `enc` of a language in `PH encBits`. -/
theorem mem_PH_iff_exists_encBits {A : Set α} :
    A ∈ PH enc ↔ ∃ B ∈ PH encBits, enc ⁻¹' B = A := by
  simp only [mem_PH]
  constructor
  · rintro ⟨k, hA⟩
    obtain ⟨B, hB, hBA⟩ := exists_mem_SigmaP_encBits_preimage hA
    exact ⟨B, ⟨k, hB⟩, hBA⟩
  · rintro ⟨B, ⟨k, hB⟩, hBA⟩
    exact hBA ▸ ⟨k, preimage_enc_mem_SigmaP hB⟩

/-- **`Πₖ ⊆ Σₖ` on bit strings transfers to every instance encoding.** -/
theorem PiP_encBits_subset_SigmaP_iff {k : ℕ} :
    PiP k encBits ⊆ SigmaP k encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), PiP k encB ⊆ SigmaP k encB :=
  ⟨fun h _ _ _ hA =>
    let ⟨_, hB, hBA⟩ := exists_mem_PiP_encBits_preimage hA
    hBA ▸ preimage_enc_mem_SigmaP (h hB),
    fun h => h encBits⟩

/-- **`Πₖ = Σₖ` on bit strings transfers to every instance encoding.** -/
theorem PiP_encBits_eq_SigmaP_iff {k : ℕ} :
    PiP k encBits = SigmaP k encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), PiP k encB = SigmaP k encB :=
  ⟨fun h _ encB => PiP_eq_SigmaP_of_PiP_subset_SigmaP (PiP_encBits_subset_SigmaP_iff.mp h.le encB),
    fun h => h encBits⟩

/-- **`Σₖ₊₁ ⊆ Σₖ` on bit strings transfers to every instance encoding.** -/
theorem SigmaP_succ_encBits_subset_SigmaP_iff {k : ℕ} :
    SigmaP (k + 1) encBits ⊆ SigmaP k encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), SigmaP (k + 1) encB ⊆ SigmaP k encB :=
  ⟨fun h _ _ _ hA =>
    let ⟨_, hB, hBA⟩ := exists_mem_SigmaP_encBits_preimage hA
    hBA ▸ preimage_enc_mem_SigmaP (h hB),
    fun h => h encBits⟩

/-- **`Σₖ₊₁ = Σₖ` on bit strings transfers to every instance encoding.** -/
theorem SigmaP_succ_encBits_eq_SigmaP_iff {k : ℕ} :
    SigmaP (k + 1) encBits = SigmaP k encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), SigmaP (k + 1) encB = SigmaP k encB :=
  ⟨fun h _ encB =>
    (SigmaP_succ_encBits_subset_SigmaP_iff.mp h.le encB).antisymm (SigmaP_subset_SigmaP_succ k),
    fun h => h encBits⟩

/-- **`coNP ⊆ NP` on bit strings transfers to every instance encoding.** -/
theorem coNP_encBits_subset_NP_iff :
    coNP encBits ⊆ NP encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NP encB := by
  simpa only [← PiP_one_eq_coNP, ← SigmaP_one] using PiP_encBits_subset_SigmaP_iff (k := 1)

/-- **`NP = coNP` on bit strings transfers to every instance encoding.** -/
theorem NP_encBits_eq_coNP_iff :
    NP encBits = coNP encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), NP encB = coNP encB := by
  rw [eq_comm, ← PiP_one_eq_coNP, ← SigmaP_one, PiP_encBits_eq_SigmaP_iff]
  exact ⟨fun h _ encB => by rw [← SigmaP_one, ← PiP_one_eq_coNP, h encB],
    fun h _ encB => by rw [PiP_one_eq_coNP, SigmaP_one, h encB]⟩

/-- **`NP ⊆ P` on bit strings transfers to every instance encoding.** -/
theorem NP_encBits_subset_P_iff :
    NP encBits ⊆ P encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB := by
  simpa only [zero_add, SigmaP_one, SigmaP_zero] using
    SigmaP_succ_encBits_subset_SigmaP_iff (k := 0)

/-- **`P = NP` on bit strings transfers to every instance encoding.** -/
theorem P_encBits_eq_NP_iff :
    P encBits = NP encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), P encB = NP encB := by
  rw [eq_comm, ← SigmaP_one, ← SigmaP_zero, SigmaP_succ_encBits_eq_SigmaP_iff (k := 0)]
  exact ⟨fun h _ encB => by rw [← SigmaP_zero, ← SigmaP_one, h encB],
    fun h _ encB => by rw [zero_add, SigmaP_one, SigmaP_zero, h encB]⟩

/-- **Arora–Barak Theorem 5.6 / Goldreich Proposition 3.10 (fixed-domain inclusion form):** if
`Πₖ ⊆ Σₖ` for bit-string languages (`encBits`), with `1 ≤ k`, then `PH = Σₖ` for every instance
encoding. -/
theorem PH_eq_SigmaP_of_PiP_encBits_subset_SigmaP {k : ℕ} (hk : 1 ≤ k)
    (h : PiP k encBits ⊆ SigmaP k encBits) : PH enc = SigmaP k enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP hk (PiP_encBits_subset_SigmaP_iff.mp h)

/-- **Arora–Barak Theorem 5.6 / Goldreich Proposition 3.10 (fixed-domain equality form):** if
`Πₖ = Σₖ` for bit-string languages (`encBits`), with `1 ≤ k`, then `PH = Σₖ` for every instance
encoding. -/
theorem PH_eq_SigmaP_of_PiP_encBits_eq_SigmaP {k : ℕ} (hk : 1 ≤ k)
    (h : PiP k encBits = SigmaP k encBits) : PH enc = SigmaP k enc :=
  PH_eq_SigmaP_of_PiP_encBits_subset_SigmaP hk h.le

/-- **Goldreich Proposition 3.10 (fixed-domain consecutive-level inclusion form):** if
`Σₖ₊₁ ⊆ Σₖ` for bit-string languages (`encBits`), then `PH = Σₖ` for every instance encoding. -/
theorem PH_eq_SigmaP_of_SigmaP_succ_encBits_subset_SigmaP {k : ℕ}
    (h : SigmaP (k + 1) encBits ⊆ SigmaP k encBits) : PH enc = SigmaP k enc :=
  PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP (SigmaP_succ_encBits_subset_SigmaP_iff.mp h)

/-- **Goldreich Proposition 3.10 (fixed-domain consecutive-level equality form):** if
`Σₖ₊₁ = Σₖ` for bit-string languages (`encBits`), then `PH = Σₖ` for every instance encoding. -/
theorem PH_eq_SigmaP_of_SigmaP_succ_encBits_eq_SigmaP {k : ℕ}
    (h : SigmaP (k + 1) encBits = SigmaP k encBits) : PH enc = SigmaP k enc :=
  PH_eq_SigmaP_of_SigmaP_succ_encBits_subset_SigmaP h.le

/-- **`coNP ⊆ NP` on bit strings collapses `PH` to `NP` at every encoding.** -/
theorem PH_eq_NP_of_coNP_encBits_subset_NP (h : coNP encBits ⊆ NP encBits) :
    PH enc = NP enc :=
  PH_eq_NP_of_coNP_subset_NP (coNP_encBits_subset_NP_iff.mp h)

/-- **`NP = coNP` on bit strings collapses `PH` to `NP` at every encoding**
[Arora and Barak, Theorem 5.6][AroraBarak07]. -/
theorem PH_eq_NP_of_NP_encBits_eq_coNP (h : NP encBits = coNP encBits) :
    PH enc = NP enc :=
  PH_eq_NP_of_coNP_encBits_subset_NP h.ge

/-- **`NP ⊆ P` on bit strings collapses `PH` to `P` at every encoding.** -/
theorem PH_eq_P_of_NP_encBits_subset_P (h : NP encBits ⊆ P encBits) :
    PH enc = P enc :=
  PH_eq_P_of_NP_subset_P (NP_encBits_subset_P_iff.mp h)

/-- **`P = NP` on bit strings collapses `PH` to `P` at every encoding**
[Arora and Barak, Theorem 5.6][AroraBarak07]. -/
theorem PH_eq_P_of_P_encBits_eq_NP (h : P encBits = NP encBits) :
    PH enc = P enc :=
  PH_eq_P_of_NP_encBits_subset_P h.ge

/-! ### Converse and equivalences (Goldreich Proposition 3.10) -/

/-- **Goldreich Proposition 3.10 (converse for `Σₖ₊₁`):** if `PH = Σₖ`, then `Σₖ₊₁ = Σₖ`. -/
theorem SigmaP_succ_eq_SigmaP_of_PH_eq_SigmaP {k : ℕ} (h : PH enc = SigmaP k enc) :
    SigmaP (k + 1) enc = SigmaP k enc :=
  (h ▸ SigmaP_subset_PH (k + 1)).antisymm (SigmaP_subset_SigmaP_succ k)

/-- **Goldreich Proposition 3.10 (converse for `Πₖ`):** if `PH = Σₖ`, then `Πₖ = Σₖ`. -/
theorem PiP_eq_SigmaP_of_PH_eq_SigmaP {k : ℕ} (h : PH enc = SigmaP k enc) :
    PiP k enc = SigmaP k enc :=
  PiP_eq_SigmaP_of_PiP_subset_SigmaP (h ▸ PiP_subset_PH k)

/-- **`PH = Σₖ` on bit strings transfers to every instance encoding.** -/
theorem PH_encBits_eq_SigmaP_iff {k : ℕ} :
    PH encBits = SigmaP k encBits ↔
      ∀ {β : Type} (encB : β ↪ List Bool), PH encB = SigmaP k encB :=
  ⟨fun h _ _ => PH_eq_SigmaP_of_SigmaP_succ_encBits_eq_SigmaP
    (SigmaP_succ_eq_SigmaP_of_PH_eq_SigmaP h),
    fun h => h encBits⟩

/-- **Goldreich Proposition 3.10:** `PH = Σₖ` at every encoding iff `Σₖ₊₁ = Σₖ` on bit strings. -/
theorem forall_PH_eq_SigmaP_iff_SigmaP_succ_encBits_eq_SigmaP {k : ℕ} :
    (∀ {β : Type} (encB : β ↪ List Bool), PH encB = SigmaP k encB) ↔
      SigmaP (k + 1) encBits = SigmaP k encBits :=
  ⟨fun h => SigmaP_succ_eq_SigmaP_of_PH_eq_SigmaP (h encBits),
    fun h _ _ => PH_eq_SigmaP_of_SigmaP_succ_encBits_eq_SigmaP h⟩

/-- **Goldreich Proposition 3.10:** for `1 ≤ k`, `PH = Σₖ` at every encoding iff `Πₖ = Σₖ` on bit
strings. -/
theorem forall_PH_eq_SigmaP_iff_PiP_encBits_eq_SigmaP {k : ℕ} (hk : 1 ≤ k) :
    (∀ {β : Type} (encB : β ↪ List Bool), PH encB = SigmaP k encB) ↔
      PiP k encBits = SigmaP k encBits :=
  ⟨fun h => PiP_eq_SigmaP_of_PH_eq_SigmaP (h encBits),
    fun h _ _ => PH_eq_SigmaP_of_PiP_encBits_eq_SigmaP hk h⟩

/-- **Goldreich Proposition 3.10 (fixed-domain `encBits` equivalence for `Σₖ₊₁`):**
`PH encBits = SigmaP k encBits ↔ SigmaP (k + 1) encBits = SigmaP k encBits`. -/
theorem PH_encBits_eq_SigmaP_iff_SigmaP_succ_encBits_eq_SigmaP {k : ℕ} :
    PH encBits = SigmaP k encBits ↔ SigmaP (k + 1) encBits = SigmaP k encBits :=
  PH_encBits_eq_SigmaP_iff.trans forall_PH_eq_SigmaP_iff_SigmaP_succ_encBits_eq_SigmaP

/-- **Goldreich Proposition 3.10 (fixed-domain `encBits` equivalence for `Πₖ`):** for `1 ≤ k`,
`PH encBits = SigmaP k encBits ↔ PiP k encBits = SigmaP k encBits`. -/
theorem PH_encBits_eq_SigmaP_iff_PiP_encBits_eq_SigmaP {k : ℕ} (hk : 1 ≤ k) :
    PH encBits = SigmaP k encBits ↔ PiP k encBits = SigmaP k encBits :=
  PH_encBits_eq_SigmaP_iff.trans (forall_PH_eq_SigmaP_iff_PiP_encBits_eq_SigmaP hk)

/-- **`PH = P` at every encoding iff `P = NP` on bit strings.** -/
theorem forall_PH_eq_P_iff_P_encBits_eq_NP :
    (∀ {β : Type} (encB : β ↪ List Bool), PH encB = P encB) ↔
      P encBits = NP encBits := by
  simpa only [zero_add, SigmaP_zero, SigmaP_one, eq_comm] using
    forall_PH_eq_SigmaP_iff_SigmaP_succ_encBits_eq_SigmaP (k := 0)

/-- **`PH encBits = P encBits ↔ P encBits = NP encBits`.** -/
theorem PH_encBits_eq_P_iff_P_encBits_eq_NP :
    PH encBits = P encBits ↔ P encBits = NP encBits := by
  simpa only [zero_add, SigmaP_zero, SigmaP_one, eq_comm] using
    PH_encBits_eq_SigmaP_iff_SigmaP_succ_encBits_eq_SigmaP (k := 0)

end Cslib.Complexity

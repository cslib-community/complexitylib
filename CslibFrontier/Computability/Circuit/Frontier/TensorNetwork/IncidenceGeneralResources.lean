/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralCounter
import all CslibFrontier.Computability.Complexity.FineGrained.CountingSparsificationUniform
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter
import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.CountingParametersPolyTime
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Complexity.Problems.SAT.SizeBound

/-!
# Whole-machine sharp resources for general-density counting

Instantiate uniform disjoint traversal with actual normalized native parity leaves, retaining
original declared variables and charging intermediate encodings, binary declared counts,
normalization, accumulation and bounded-size dispatch. No resource oracle is assumed.
This is the whole-search resource composition of [OpenAI2026ETH], Appendix D.3, p. 57,
used by [ChenJiangZhu2027], Lemma 3.2 (PDF p. 11): fixed width k≥2, n≥20, unrestricted
clause density, exact counts over all declared variables, deterministic binary time polynomial
in n plus the clause count times the single-loglog exponential, and polynomial bit space.
Weighted input reconstruction is separate.

## Main results

* `exists_countGeneralParity_sharp_certificate`: global rounded time and polynomial workspace.
* `exists_countGeneralParity_real_sharp_certificate`: the real base-two eta exponent.
* `exists_countGeneralParity_source_certificate`: polynomial prefactors in n plus clause count.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.GenericRAM Cslib.Complexity Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Logic.PL.ClauseSet.Sparsification CountingSparsify Turing.MultiTapeTM
open ExhaustiveCountFallback Cslib.Logic.PL.CNF.Sparsification

private abbrev Input := ℕ × CNF ℕ
private abbrev Context := Unit × ℕ
private abbrev FullInput := Unit × ℕ × CNF ℕ
private abbrev LeafInput := Context × CNF ℕ
private abbrev encInput := encPair encUnary encCNF
private abbrev encContext := encPair encUnit encUnary
private abbrev encFull := encPair encUnit encInput
private abbrev encLeaf := encPair encContext encCNF

private def dropLeaf (x : LeafInput) : Input := (x.1.2, x.2)
private def prepare (x : Input) : FullInput := ((), x)
private def threshold (k : ℕ) (p : Context) := countingThresholdBase k (sharpSearchDivisor p.2)
private def depth (k : ℕ) (n : ℕ) := countingDepthCoeff k (threshold k ((), n))
private noncomputable def leafCount (k β N₀ : ℕ) : LeafInput → ℕ :=
  normalizeDeclaredLeaf Prod.snd (countParity k β N₀ ∘ dropLeaf)

private theorem dropLeaf_polytime : ComputableInPolyTime dropLeaf encLeaf encInput := by
  unfold dropLeaf
  fun_prop

private theorem prepare_polytime : ComputableInPolyTime prepare encInput encFull := by
  unfold prepare
  fun_prop

private theorem leaf_certificate (k β : ℕ) (hk : 1 ≤ k) :
    ∃ N₀ : ℕ, ∃ cg : NativeCertificate (leafCount k β N₀) encLeaf encNat,
    ∃ C d A : ℕ,
      (∀ x, cg.time x ≤ C * ((encLeaf x).length + 1) ^ d *
        2 ^ (A * Nat.logLogSqrtLogScale x.1.2)) ∧
      PolyBounded (fun x => (encLeaf x).length) cg.space := by
  obtain ⟨N₀, cp, A, hcp⟩ := exists_countParity_sharp_certificate k β hk
  let cd := NativeCertificate.ofPolyTime dropLeaf_polytime
  have hd := NativeCertificate.ofPolyTime_isPolynomial dropLeaf_polytime
  have hcpS : PolyBounded (fun x : Input => (encInput x).length) cp.space :=
    (PolyBounded.of_polynomiallyBounded _ (bound := fun L => A * (L + 1) ^ A)
      (by fun_prop)).mono (fun x => (hcp x).2)
  let raw := cp.comp cd
  have hraw : PolyBounded (fun x : LeafInput => (encLeaf x).length) raw.space :=
    SparseCNFLeafCounter.polyBounded_comp_space cp cd hcpS hd.2
  have hout := SparseCNFLeafCounter.polyBounded_output_of_space raw hraw
  obtain ⟨b, hnorm⟩ := exists_computableInO_normalizeDeclaredLeaf
    (ComputableInPolyTime.snd encUnit encUnary) raw.computes
  let post (x : LeafInput) :=
    ((encLeaf x).length + (encNat ((countParity k β N₀ ∘ dropLeaf) x)).length + 1) ^ b
  let cg : NativeCertificate (leafCount k β N₀) encLeaf encNat :=
    ⟨fun x => raw.time x + post x, fun x => raw.space x + post x, hnorm⟩
  have hpost : PolyBounded (fun x : LeafInput => (encLeaf x).length) post :=
    ((PolyBounded.self.add hout).add (.const 1)).pow b
  let V (x : LeafInput) := cd.time x + post x + A * ((encInput (dropLeaf x)).length + 1) ^ A
  have hV : PolyBounded (fun x : LeafInput => (encLeaf x).length) V :=
    (hd.1.add hpost).add ((PolyBounded.const A).mul
      ((dropLeaf_polytime.polyBounded_length.add (.const 1)).pow A))
  obtain ⟨C, d, hCd⟩ := hV.exists_le
  refine ⟨N₀, cg, C, d, A, fun x => ?_, hraw.add hpost⟩
  have ht := (hcp (dropLeaf x)).1
  change cp.time (dropLeaf x) ≤ A * ((encInput (dropLeaf x)).length + 1) ^ A *
    2 ^ (A * Nat.logLogSqrtLogScale x.1.2) at ht
  have hp : cd.time x + post x ≤ (cd.time x + post x) *
      2 ^ (A * Nat.logLogSqrtLogScale x.1.2) :=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  calc cg.time x = (cd.time x + post x) + cp.time (dropLeaf x) := by
        change cd.time x + cp.time (dropLeaf x) + post x = _
        omega
    _ ≤ (cd.time x + post x) * 2 ^ (A * Nat.logLogSqrtLogScale x.1.2) +
        A * ((encInput (dropLeaf x)).length + 1) ^ A *
          2 ^ (A * Nat.logLogSqrtLogScale x.1.2) := Nat.add_le_add hp ht
    _ = V x * 2 ^ (A * Nat.logLogSqrtLogScale x.1.2) := by dsimp only [V]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (hCd x)

private def leafSize (k : ℕ) (x : FullInput) : ℕ :=
  2 * x.2.1 + 3 + nodeBound k (depth k x.2.1) x.2.2

private theorem size_bounds (k : ℕ) (hk : 2 ≤ k) :
    PolyBounded (fun x : FullInput => (encFull x).length) (fun x => depth k x.2.1) ∧
    PolyBounded (fun x : FullInput => (encFull x).length) (leafSize k) := by
  obtain ⟨p, hp, hb⟩ := sharp_parameters_polylog hk
  have hp' : Cslib.PolynomiallyBounded (fun n => p (Nat.clog 2 n)) := by fun_prop
  obtain ⟨C, d, hCd⟩ := Cslib.polynomiallyBounded_iff_le.mp hp'
  have hN (x : Input) : x.1 ≤ (encInput x).length := by
    simp only [encInput, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hDI : PolyBounded (fun x : Input => (encInput x).length) (fun x => depth k x.1) :=
    PolyBounded.of_forall_le C d fun x => ((hb x.1).1.trans (hCd x.1)).trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right (hN x) 1) d))
  have hdrop := ComputableInPolyTime.snd encUnit encInput
  have hD := hDI.comp hdrop.polyBounded_length
  have hn : PolyBounded (fun x : FullInput => (encFull x).length) (fun x => x.2.1) :=
    (PolyBounded.self.mono hN).comp hdrop.polyBounded_length
  have hnode := (CountingSparsify.nodeBound_runtime_polyBounded (encP := encUnary) k hDI).comp
    hdrop.polyBounded_length
  exact ⟨hD, (((PolyBounded.const 2).mul hn).add (.const 3)).add hnode⟩

private theorem prefix_bounds (k : ℕ) (hk : 1 ≤ k) (g : LeafInput → ℕ) (x : FullInput)
    (hx : validDeclaredInput k x.2.1 x.2.2 = true) (i : ℕ)
    (ha : let p := (x.1, x.2.1)
      let st := (step (threshold k p) k (fun ψ => g (p, ψ)))^[i] (init k x.2.2)
      st.2.1.isEmpty = false ∧
        isSparse (countingThreshold (threshold k p)) k (st.2.1.headD []) = true) :
    let p := (x.1, x.2.1)
    let ψ := ((step (threshold k p) k (fun ψ => g (p, ψ)))^[i] (init k x.2.2)).2.1.headD []
    ψ.vars.toFinset ⊆ Finset.range x.2.1 ∧ (encLeaf (p, ψ)).length ≤ leafSize k x := by
  have hb := (iterate_step_prefix_bounds
    ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase k (sharpSearchDivisor x.2.1))) hk
    (two_le_countingThresholdBase k (sharpSearchDivisor x.2.1)) (le_refl k)
    (sharp_countingTreeBound hk x.2.1) (fun ψ => g ((x.1, x.2.1), ψ)) x.2.2 i).2.2.2 ha
  refine ⟨hb.2.1.trans (validDeclaredInput_eq_true_iff.mp hx).2, ?_⟩
  simp only [encLeaf, encContext, length_encPair, encUnit_apply, List.length_nil,
    encUnary_apply, List.length_replicate, leafSize, depth, threshold]
  dsimp only [threshold, depth] at hb
  have := hb.2.2.2.2
  omega

private theorem rounds_bound (k : ℕ) (x : FullInput)
    (hx : validDeclaredInput k x.2.1 x.2.2 = true) :
    rounds (sharpSearchDivisor x.2.1) x.2.2 + 1 ≤
      33 * 2 ^ Nat.logLogSqrtLogScale x.2.1 := by
  have hv := (validDeclaredInput_eq_true_iff.mp hx).2
  have he := Nat.two_pow_pos (Nat.logLogSqrtLogScale x.2.1)
  by_cases hn : 4 ≤ x.2.1
  · have ht := sharp_rounds_le hn hv
    omega
  · have hnvars : x.2.2.numVars ≤ x.2.1 := by
      simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hv
    have hdiv := Nat.div_le_self x.2.2.numVars (sharpSearchDivisor x.2.1)
    have hround : rounds (sharpSearchDivisor x.2.1) x.2.2 ≤ 32 := by
      rw [rounds, CNF.length_distinctVars]
      exact Nat.pow_le_pow_right (by decide) (by omega :
        x.2.2.numVars / sharpSearchDivisor x.2.1 + 2 ≤ 5)
    omega

private noncomputable def fullSearch (k β N₀ : ℕ) (x : FullInput) : ℕ :=
  searchDeclaredWith Prod.snd (threshold k) (fun p => sharpSearchDivisor p.2) k k
    (leafCount k β N₀) (x.1, x.2.1) x.2.2

private theorem search_certificate (k β : ℕ) (hk : 2 ≤ k) :
    ∃ N₀ A : ℕ, ∃ cs : NativeCertificate (fullSearch k β N₀) encFull encNat,
    ∃ V : FullInput → ℕ,
      PolyBounded (fun x => (encFull x).length) V ∧
      (∀ x, validDeclaredInput k x.2.1 x.2.2 = true →
        cs.time x ≤ V x * 2 ^ ((A + 1) * Nat.logLogSqrtLogScale x.2.1)) ∧
      (∀ x, cs.space x ≤ V x) := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨N₀, cg, C, d, A, ht, hs⟩ := leaf_certificate k β hk1
  obtain ⟨Cs, ds, hCs⟩ := hs.exists_le
  have hB := sharpSearchDivisor_polytime.comp (ComputableInPolyTime.snd encUnit encUnary)
  have hM := (computableInPolyTime_countingThresholdBase k).comp hB
  have hθ : ComputableInPolyTime
      (fun x : Context × ℕ × ℕ => decide (countingThreshold (threshold k x.1) x.2.1 ≤ x.2.2))
      (encPair encContext (encPair encUnary encUnary)) encBool :=
    computableInPolyTime_countingThreshold_le_binary.comp
      ((hM.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  let R (x : FullInput) := C * (leafSize k x + 1) ^ d *
    2 ^ (A * Nat.logLogSqrtLogScale x.2.1)
  let Q (x : FullInput) := Cs * (leafSize k x + 1) ^ ds
  have hsize := size_bounds k hk
  have hQ : PolyBounded (fun x : FullInput => (encFull x).length) Q :=
    (PolyBounded.const Cs).mul ((hsize.2.add (.const 1)).pow ds)
  obtain ⟨c, e, hsearch, hS⟩ := exists_computableInO_searchDeclaredWith
    hB hθ (fun p => (by decide : 1 ≤ 2).trans
      (two_le_countingThresholdBase k (sharpSearchDivisor p.2))) hk1
    (fun p => two_le_countingThresholdBase k (sharpSearchDivisor p.2)) (le_refl k)
    (fun p => sharp_countingTreeBound hk1 p.2) hsize.1 cg.computes
    (fun x hx i _ ha => by
      have hv := (prefix_bounds k hk1 (leafCount k β N₀) x hx i ha).1
      exact normalizeDeclaredLeaf_le_two_pow_numVars hv (countParity_le k β N₀ _))
    (R := R) (Q := Q)
    (fun x hx i _ ha => (ht _).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C
      (Nat.pow_le_pow_left (Nat.add_le_add_right
        (prefix_bounds k hk1 (leafCount k β N₀) x hx i ha).2 1) d))))
    (fun x hx i _ ha => (hCs _).trans (Nat.mul_le_mul_left Cs
      (Nat.pow_le_pow_left (Nat.add_le_add_right
        (prefix_bounds k hk1 (leafCount k β N₀) x hx i ha).2 1) ds))) hQ
  let S (x : FullInput) := c * ((encFull x).length + 1) ^ e + Q x
  let cs : NativeCertificate (fullSearch k β N₀) encFull encNat :=
    ⟨fun x => c * ((encFull x).length + 1) ^ e +
      (rounds (sharpSearchDivisor x.2.1) x.2.2 + 1) *
        (c * ((encFull x).length + 1) ^ e + R x), S, hsearch⟩
  let P (x : FullInput) := c * ((encFull x).length + 1) ^ e
  let U (x : FullInput) := C * (leafSize k x + 1) ^ d
  let V (x : FullInput) := P x + 33 * (P x + U x) + S x
  have hP : PolyBounded (fun x : FullInput => (encFull x).length) P :=
    (PolyBounded.const c).mul ((PolyBounded.self.add (.const 1)).pow e)
  have hU : PolyBounded (fun x : FullInput => (encFull x).length) U :=
    (PolyBounded.const C).mul ((hsize.2.add (.const 1)).pow d)
  refine ⟨N₀, A, cs, V, (hP.add ((PolyBounded.const 33).mul (hP.add hU))).add hS,
    fun x hx => ?_, fun x => by dsimp only [cs, V]; omega⟩
  let E := Nat.logLogSqrtLogScale x.2.1
  have hr := rounds_bound k x hx
  have hp1 : 1 ≤ 2 ^ (A * E) := Nat.one_le_pow _ 2 (by decide)
  have hprod : 2 ^ ((A + 1) * E) = 2 ^ E * 2 ^ (A * E) := by
    rw [Nat.add_mul, one_mul, pow_add, mul_comm]
  have hinner : P x + U x * 2 ^ (A * E) ≤ (P x + U x) * 2 ^ (A * E) := by
    nlinarith
  have hcall : (rounds (sharpSearchDivisor x.2.1) x.2.2 + 1) *
        (P x + U x * 2 ^ (A * E)) ≤ 33 * (P x + U x) * 2 ^ ((A + 1) * E) := by
    calc _ ≤ (33 * 2 ^ E) * ((P x + U x) * 2 ^ (A * E)) := Nat.mul_le_mul hr hinner
      _ = _ := by rw [hprod]; ring
  have hpT : P x ≤ P x * 2 ^ ((A + 1) * E) :=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  calc cs.time x = P x + (rounds (sharpSearchDivisor x.2.1) x.2.2 + 1) *
        (P x + U x * 2 ^ (A * E)) := rfl
    _ ≤ P x * 2 ^ ((A + 1) * E) + 33 * (P x + U x) * 2 ^ ((A + 1) * E) :=
      Nat.add_le_add hpT hcall
    _ = (P x + 33 * (P x + U x)) * 2 ^ ((A + 1) * E) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

private theorem fullSearch_prepare (k β N₀ : ℕ) (x : Input) :
    fullSearch k β N₀ (prepare x) = searchDeclaredWith id
      (fun n => countingThresholdBase k (sharpSearchDivisor n)) sharpSearchDivisor k k
      (normalizeDeclaredLeaf id (countParity k β N₀)) x.1 x.2 := by
  simp only [fullSearch, prepare, searchDeclaredWith_eq_ite_mul, threshold, leafCount,
    normalizeDeclaredLeaf_eq_div, Function.comp_apply, dropLeaf, id_eq]

private theorem general_resources (k β Ncut : ℕ) (hk : 2 ≤ k) :
    ∃ N₀ : ℕ, ∃ (cs : NativeCertificate (countGeneralParity k β N₀ Ncut) encInput encNat)
      (D : ℕ), ∀ x : Input,
      cs.time x ≤ D * ((encInput x).length + 1) ^ D *
        2 ^ (D * Nat.logLogSqrtLogScale x.1) ∧
      cs.space x ≤ D * ((encInput x).length + 1) ^ D := by
  obtain ⟨N₀, A, cfull, V, hV, htFull, hsFull⟩ := search_certificate k β hk
  let hp := prepare_polytime
  let prep := NativeCertificate.ofPolyTime hp
  have hprep := NativeCertificate.ofPolyTime_isPolynomial hp
  have hv := SparseCNFLeafCounter.computableInPolyTime_validDeclaredInput k
    (ComputableInPolyTime.id' (encIn := encUnary))
  let cv := NativeCertificate.ofPolyTime hv
  have hcv := NativeCertificate.ofPolyTime_isPolynomial hv
  have hsmall : ComputableInPolyTime (fun x : Input => decide (x.1 < Ncut)) encInput encBool := by
    unfold encInput
    fun_prop
  let cm := NativeCertificate.ofPolyTime hsmall
  have hcm := NativeCertificate.ofPolyTime_isPolynomial hsmall
  let cr : NativeCertificate (fun _ : Input => (0 : ℕ)) encInput encNat :=
    NativeCertificate.ofPolyTime (ComputableInPolyTime.const 0)
  have hcr := NativeCertificate.ofPolyTime_isPolynomial
    (show ComputableInPolyTime (fun _ : Input => (0 : ℕ)) encInput encNat from
      ComputableInPolyTime.const 0)
  let cs : NativeCertificate (countGeneralParity k β N₀ Ncut) encInput encNat :=
    (NativeCertificate.branch cv
      (NativeCertificate.branch cm countCNFExhaustiveCertificate (cfull.comp prep)) cr).congr
        fun x => by
          rw [countGeneralParity]
          by_cases hvalid : validDeclaredInput k x.1 x.2 = true
          · simp only [hvalid, ↓reduceIte]
            by_cases hn : x.1 < Ncut
            · simp [hn]
            · simp only [hn, decide_false,
                Bool.false_eq_true, ↓reduceIte, Function.comp_apply]
              exact fullSearch_prepare k β N₀ x
          · simp [hvalid]
  obtain ⟨P, Q, hP, hQ, hex⟩ := exists_countCNFExhaustive_time_le
  let W (x : Input) := cv.time x + cv.space x + cm.time x + cm.space x +
    prep.time x + prep.space x + cr.time x + cr.space x +
    ((2 ^ Ncut + 1) * P x + Q x) + countCNFExhaustiveCertificate.space x + V (prepare x)
  have hW : PolyBounded (fun x : Input => (encInput x).length) W :=
    (((((((((hcv.1.add hcv.2).add hcm.1).add hcm.2).add hprep.1).add hprep.2).add
      hcr.1).add hcr.2).add (((PolyBounded.const (2 ^ Ncut + 1)).mul hP).add hQ)).add
      polyBounded_countCNFExhaustive_space).add (hV.comp hp.polyBounded_length)
  obtain ⟨C, d, hCd⟩ := hW.exists_le
  let D := C + d + A + 2
  refine ⟨N₀, cs, D, fun x => ?_⟩
  let E := 2 ^ ((A + 1) * Nat.logLogSqrtLogScale x.1)
  have hE : 0 < E := Nat.two_pow_pos _
  have hraw : cs.time x ≤ W x * E ∧ cs.space x ≤ W x := by
    change cv.time x + (if validDeclaredInput k x.1 x.2 then cm.time x +
      (if decide (x.1 < Ncut) then countCNFExhaustiveCertificate.time x
       else prep.time x + cfull.time (prepare x)) else cr.time x) ≤ _ ∧
      cv.space x + (if validDeclaredInput k x.1 x.2 then cm.space x +
      (if decide (x.1 < Ncut) then countCNFExhaustiveCertificate.space x
       else prep.space x + cfull.space (prepare x)) else cr.space x) ≤ _
    by_cases hvalid : validDeclaredInput k x.1 x.2 = true
    · simp only [hvalid, ↓reduceIte]
      by_cases hn : x.1 < Ncut
      · simp only [hn, decide_true, ↓reduceIte]
        have hext := (hex x).trans (Nat.add_le_add_right
          (Nat.mul_le_mul_right (P x) (Nat.add_le_add_right
            (Nat.pow_le_pow_right (by decide : 0 < 2) hn.le) 1)) (Q x))
        have hbare : cv.time x + (cm.time x + countCNFExhaustiveCertificate.time x) ≤ W x := by
          dsimp only [W]
          omega
        exact ⟨hbare.trans (Nat.le_mul_of_pos_right _ hE), by dsimp only [W]; omega⟩
      · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
        have ht := htFull (prepare x) hvalid
        change cfull.time (prepare x) ≤ V (prepare x) * E at ht
        have hs := hsFull (prepare x)
        have hpoly : cv.time x + cm.time x + prep.time x ≤
            (cv.time x + cm.time x + prep.time x) * E := Nat.le_mul_of_pos_right _ hE
        constructor
        · calc _ = (cv.time x + cm.time x + prep.time x) + cfull.time (prepare x) := by omega
            _ ≤ (cv.time x + cm.time x + prep.time x) * E + V (prepare x) * E :=
              Nat.add_le_add hpoly ht
            _ = (cv.time x + cm.time x + prep.time x + V (prepare x)) * E := by ring
            _ ≤ _ := Nat.mul_le_mul_right E (by dsimp only [W]; omega)
        · dsimp only [W]
          omega
    · simp only [hvalid, Bool.false_eq_true, ↓reduceIte]
      have ht : cv.time x + cr.time x ≤ W x := by dsimp only [W]; omega
      exact ⟨ht.trans (Nat.le_mul_of_pos_right _ hE), by dsimp only [W]; omega⟩
  have hC : C ≤ D := by dsimp only [D]; omega
  have hd : d ≤ D := by dsimp only [D]; omega
  have hA : A + 1 ≤ D := by dsimp only [D]; omega
  have hpoly : W x ≤ D * ((encInput x).length + 1) ^ D :=
    (hCd x).trans (Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hd))
  exact ⟨hraw.1.trans (Nat.mul_le_mul hpoly
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hA))), hraw.2.trans hpoly⟩

/-- One actual general-density counter, exact on every valid declared input, with sharp
single-loglog native time and independent polynomial workspace. No resource premise remains. -/
theorem exists_countGeneralParity_sharp_certificate (k : ℕ) (hk : 2 ≤ k) :
    ∃ β N₀ Ncut : ℕ, ∃ (cs : NativeCertificate (countGeneralParity k β N₀ Ncut)
      (encPair encUnary encCNF) encNat) (D : ℕ),
      (∀ x : ℕ × CNF ℕ, cs.time x ≤ D * ((encPair encUnary encCNF x).length + 1) ^ D *
        2 ^ (D * Nat.logLogSqrtLogScale x.1) ∧
        cs.space x ≤ D * ((encPair encUnary encCNF x).length + 1) ^ D) ∧
      (∀ x : ℕ × CNF ℕ, countGeneralParity k β N₀ Ncut x =
        if validDeclaredInput k x.1 x.2 then x.2.modelCountOn (Finset.range x.1) else 0) := by
  obtain ⟨β, Ncut, hcorrect⟩ := exists_countGeneralParity_eq_modelCountOn k hk
  obtain ⟨N₀, cs, D, hresource⟩ := general_resources k β Ncut hk
  refine ⟨β, N₀, Ncut, cs, D, hresource, fun x => ?_⟩
  by_cases hv : validDeclaredInput k x.1 x.2 = true
  · rw [ite_eq_left hv]
    exact hcorrect N₀ x.1 x.2 (validDeclaredInput_eq_true_iff.mp hv).1
      (validDeclaredInput_eq_true_iff.mp hv).2
  · simp only [countGeneralParity, hv, Bool.false_eq_true, ↓reduceIte]

/-- The actual unrestricted-density machine satisfies the real source eta bound for n≥16.
In particular the source's n≥20 range needs no further size exception. -/
theorem exists_countGeneralParity_real_sharp_certificate (k : ℕ) (hk : 2 ≤ k) :
    ∃ β N₀ Ncut : ℕ, ∃ (cs : NativeCertificate (countGeneralParity k β N₀ Ncut)
      (encPair encUnary encCNF) encNat) (D : ℕ),
      (∀ x : ℕ × CNF ℕ, countGeneralParity k β N₀ Ncut x =
        if validDeclaredInput k x.1 x.2 then x.2.modelCountOn (Finset.range x.1) else 0) ∧
      ∀ n, 16 ≤ n → ∀ φ : CNF ℕ,
        let L := (encPair encUnary encCNF (n, φ)).length
        (cs.time (n, φ) : ℝ) ≤ (D : ℝ) * (L + 1 : ℕ) ^ D *
          (2 : ℝ) ^ (((6 * D : ℕ) : ℝ) * Real.logLogSqrtLogScale n) ∧
        cs.space (n, φ) ≤ D * (L + 1) ^ D := by
  obtain ⟨β, N₀, Ncut, cs, D, hresource, hcorrect⟩ :=
    exists_countGeneralParity_sharp_certificate k hk
  refine ⟨β, N₀, Ncut, cs, D, hcorrect, fun n hn φ => ?_⟩
  obtain ⟨ht, hs⟩ := hresource (n, φ)
  refine ⟨?_, hs⟩
  have htR : (cs.time (n, φ) : ℝ) ≤ (D : ℝ) *
      ((encPair encUnary encCNF (n, φ)).length + 1 : ℕ) ^ D *
      (2 : ℝ) ^ (D * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht
  exact htR.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le D hn) (by positivity))

/-- Source Lemma 3.2: every fixed width k≥2 admits one unrestricted-density declared counter
with deterministic bit time polynomial in N+M times the single-loglog exponential, and
polynomial bit space. Input validity is exactly width and declaration; unused variables count.
The constants and machine are fixed before every N≥20 and every clause list. -/
theorem exists_countGeneralParity_source_certificate (k : ℕ) (hk : 2 ≤ k) :
    ∃ β N₀ Ncut : ℕ, ∃ cs : NativeCertificate (countGeneralParity k β N₀ Ncut)
      (encPair encUnary encCNF) encNat, ∃ C e A : ℕ,
      (∀ x : ℕ × CNF ℕ, countGeneralParity k β N₀ Ncut x =
        if validDeclaredInput k x.1 x.2 then x.2.modelCountOn (Finset.range x.1) else 0) ∧
      ∀ n, 20 ≤ n → ∀ φ : CNF ℕ, validDeclaredInput k n φ = true →
        (cs.time (n, φ) : ℝ) ≤ (C : ℝ) * (n + φ.length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n) ∧
        cs.space (n, φ) ≤ C * (n + φ.length + 1) ^ e := by
  obtain ⟨β, N₀, Ncut, cs, D, hcorrect, hresource⟩ :=
    exists_countGeneralParity_real_sharp_certificate k hk
  let C := D * (20 * k + 4) ^ D
  let e := 2 * D
  refine ⟨β, N₀, Ncut, cs, C, e, 6 * D, hcorrect, fun n hn φ hv => ?_⟩
  have hpoly : D * ((encInput (n, φ)).length + 1) ^ D ≤ C * (n + φ.length + 1) ^ e := by
    calc _ ≤ D * ((20 * k + 4) * (n + φ.length + 1) ^ 2) ^ D :=
          Nat.mul_le_mul_left D (Nat.pow_le_pow_left (SAT.length_declaredInput_le hv) D)
      _ = _ := by dsimp only [C, e]; rw [mul_pow, ← pow_mul]; ring
  obtain ⟨ht, hs⟩ := hresource n (by omega) φ
  exact ⟨ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hpoly) (by positivity)),
    hs.trans hpoly⟩

end Cslib.Circuits.Frontier.IncidenceNetwork

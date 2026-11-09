/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Multiplication.Blocks
import CslibFrontier.Logics.FirstOrder.Ordered.Multiplication.Bounds
import Mathlib.Tactic.Linarith

/-!
# The native TIMES formula

Multiplication is defined over canonical order and BIT by counting each binary multiplication
column and checking its carries. Eight global words store the block-boundary carries, and
sixteen local words store each block. Both ends of every block agree with the global words.
The first and last carries are zero; exact PLUS and shifts prohibit modular overflow.

One fixed finite formula covers small inputs. The packed branch has witnesses for every universe
of size at least 257, including sizes between powers of two. Neither branch uses multiplication
in its syntax: only fixed literal scales, PLUS, exact shifts, and the proved native Bit Sum.

## Main definitions

* `Cslib.Logic.FO.Ordered.multiplication`: one native multiplication formula.

## Main results

* `Cslib.Logic.FO.Ordered.realize_multiplication`: exact natural-number product semantics.
* `Cslib.Logic.FO.Ordered.not_realize_multiplication_of_le`: rejection of every overflow candidate.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 1.17(1), using Lemma 1.18.
  The Bit Sum Lemma is historically due to Barrington, Immerman and Straubing
  [BarringtonImmermanStraubing1990]. This packed carry-table construction is a proved variant
  of the source's alternating padded blocks and short running sums, not a transcription.
-/

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

namespace Multiplication

variable (L : Language)

private noncomputable def parameters {α : Type*} (h e s m k : (language L).Term α) :
    (language L).Formula α :=
  highestBit L (max L) h ⊓ powerOfTwo L s e ⊓ powerOfTwo L k m ⊓ le L e m ⊓ le L s h ⊓
  Formula.iExs (Fin 7)
    (scaleEq L 16 (h.relabel Sum.inl) (.var (.inr 0)) ⊓
     addEq L (h.relabel Sum.inl) (one L) (.var (.inr 1)) ⊓
     scaleEq L 2 (.var (.inr 1)) (.var (.inr 2)) ⊓ le L (.var (.inr 2)) (k.relabel Sum.inl) ⊓
     scaleEq L 8 (h.relabel Sum.inl) (.var (.inr 3)) ⊓
     addEq L (k.relabel Sum.inl) (s.relabel Sum.inl) (.var (.inr 4)) ⊓
     le L (.var (.inr 4)) (.var (.inr 3)) ⊓
     addEq L (s.relabel Sum.inl) (one L) (.var (.inr 5)) ⊓
     shiftLeft L (.var (.inr 5)) (e.relabel Sum.inl) (.var (.inr 6)) ⊓
     le L (.var (.inr 6)) (.var (.inr 0)))

private noncomputable def allBlocks {α : Type*} (h e s k x y z : (language L).Term α)
    (g : Fin 8 → (language L).Term α) : (language L).Formula α := Formula.iAlls (Fin 2)
  ((shiftLeft L (.var (.inr 0)) (e.relabel Sum.inl) (.var (.inr 1)) ⊓
    (le L (k.relabel Sum.inl) (.var (.inr 1))).not).imp
    (blockChecks L (h.relabel Sum.inl) (e.relabel Sum.inl) (s.relabel Sum.inl)
      (x.relabel Sum.inl) (y.relabel Sum.inl) (z.relabel Sum.inl) (.var (.inr 1))
      (fun r => (g r).relabel Sum.inl)))

private noncomputable def packedFormula : (language L).Formula (Fin 3) :=
  Formula.iExs (Fin 5 ⊕ Fin 8) (
    let h : (language L).Term (Fin 3 ⊕ (Fin 5 ⊕ Fin 8)) := .var (.inr (.inl 0))
    let e := .var (.inr (.inl 1))
    let s := .var (.inr (.inl 2))
    let m := .var (.inr (.inl 3))
    let k := .var (.inr (.inl 4))
    let g := fun r : Fin 8 => Term.var (.inr (.inr r))
    parameters L h e s m k ⊓
    packedField L h g (zero L) s (zero L) ⊓ packedField L h g k s (zero L) ⊓
    allBlocks L h e s k (.var (.inl 0)) (.var (.inl 1)) (.var (.inl 2)) g)

private noncomputable def smallFormula : (language L).Formula (Fin 3) :=
  Formula.iSup fun a : Fin 256 => natEq L a.val (.var 0) ⊓ scaleEq L a.val (.var 1) (.var 2)

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

private theorem realize_parameters (h e s m k : (language L).Term α) (v : α → Fin n) :
    (parameters L h e s m k).Realize v ↔
      2 ^ (h.realize v).val ≤ n - 1 ∧ n - 1 < 2 ^ ((h.realize v).val + 1) ∧
      (s.realize v).val = 2 ^ (e.realize v).val ∧
      (k.realize v).val = 2 ^ (m.realize v).val ∧ (e.realize v).val ≤ (m.realize v).val ∧
      (s.realize v).val ≤ (h.realize v).val ∧ 16 * (h.realize v).val < n ∧
      2 * ((h.realize v).val + 1) ≤ (k.realize v).val ∧
      (k.realize v).val + (s.realize v).val ≤ 8 * (h.realize v).val ∧
      ((s.realize v).val + 1) * (s.realize v).val ≤ 16 * (h.realize v).val := by
  simp only [parameters, Formula.realize_inf, realize_highestBit, realize_powerOfTwo,
    realize_le, realize_max_val, Fin.le_def, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun hs =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_scaleEq, realize_addEq,
    realize_le, realize_shiftLeft, Term.realize_var, Term.realize_relabel, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, realize_one_val, Fin.le_def, and_assoc]
  constructor
  · rintro ⟨u, ho, hw, hw2, hkw, ho8, hks, hsize, hs1, hcap, hcap'⟩
    have hn := (u 0).isLt
    rw [← hs] at hcap
    exact ⟨by lia, by lia, by lia, by nlinarith⟩
  · rintro ⟨hspace, hkw, hks, hcap⟩
    have hk := (k.realize v).isLt
    have hw : (h.realize v).val + 1 < n := by lia
    have hw2 : 2 * ((h.realize v).val + 1) < n := by lia
    have ho8 : 8 * (h.realize v).val < n := by lia
    have hsize : (k.realize v).val + (s.realize v).val < n := by lia
    have hspos : 0 < (s.realize v).val := hs ▸ Nat.two_pow_pos _
    have hs1 : (s.realize v).val + 1 < n := by nlinarith
    have hcapn : ((s.realize v).val + 1) * (s.realize v).val < n := by lia
    refine ⟨![⟨_, hspace⟩, ⟨_, hw⟩, ⟨_, hw2⟩, ⟨_, ho8⟩,
      ⟨_, hsize⟩, ⟨_, hs1⟩, ⟨_, hcapn⟩], rfl, rfl, rfl, hkw, rfl, rfl, hks, rfl, ?_, hcap⟩
    dsimp
    rw [hs]

private theorem block_end_le {q s k : ℕ} (_hs : 0 < s) (hks : s ∣ k) (hq : q * s < k) :
    q * s + s ≤ k := by
  obtain ⟨r, hr⟩ := hks
  have hqr : q < r := by nlinarith
  nlinarith

private theorem packedFormula_sound (v : Fin 3 → Fin n)
    (hf : (packedFormula L).Realize v) : (v 0).val * (v 1).val = (v 2).val := by
  simp only [packedFormula, Formula.realize_iExs, Formula.realize_inf, realize_parameters,
    Term.realize_var, Sum.elim_inr, and_assoc] at hf
  obtain ⟨u, hlo, hhi, hs, hk, he, hsh, hspace, hkw, hks, hcap, hzero, hend, hblocks⟩ := hf
  have hp : 2 ^ (u (.inl 0)).val < n := by lia
  have hspos : 0 < (u (.inl 2)).val := hs ▸ Nat.two_pow_pos _
  have hdiv : (u (.inl 2)).val ∣ (u (.inl 4)).val := by
    rw [hs, hk]
    exact Nat.pow_dvd_pow 2 he
  have hwidth : 2 ^ (u (.inl 2)).val < n :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hsh) hp
  have hcapn : ((u (.inl 2)).val + 1) * (u (.inl 2)).val < n := by lia
  rw [realize_packedField _ _ _ _ _ _ (by simpa using (show 8 * (u (.inl 0)).val < n by lia))]
    at hzero hend
  simp only [Term.realize_var, Sum.elim_inr, realize_zero_val] at hzero hend
  simp only [allBlocks, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_not, realize_shiftLeft, realize_le, Term.realize_var, Term.realize_relabel,
    Function.comp_def, Sum.elim_inr, Sum.elim_inl, not_le] at hblocks
  have hinput (i : Fin 3) : (v i).val < 2 ^ ((u (.inl 0)).val + 1) := by
    have := (v i).isLt
    lia
  apply BitString.mul_eq_of_blocks (hinput 0) (hinput 1)
    (lt_of_lt_of_le (hinput 2) (Nat.pow_le_pow_right (by decide) (by lia))) hkw hspos hdiv
    (fun a => BitString.readPackedField (u (.inl 0)).val (fun r => (u (.inr r)).val)
      a (u (.inl 2)).val) hzero.symm hend.symm
  intro q hq
  have hqn : q < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hspos)
    (lt_trans hq (u (.inl 4)).isLt)
  have hjn : q * (u (.inl 2)).val < n := lt_trans hq (u (.inl 4)).isLt
  let a : Fin 2 → Fin n := ![⟨q, hqn⟩, ⟨_, hjn⟩]
  have hb := hblocks a ⟨by dsimp [a]; rw [hs], hq⟩
  have hjend := lt_of_le_of_lt (block_end_le hspos hdiv hq) (u (.inl 4)).isLt
  rw [realize_blockChecks _ _ _ _ _ _ _ _ _ (by simpa using hs)
    (by simpa using hcapn) (by simpa [a] using hjend)
    (by simpa using hwidth) (by simpa using hspace)] at hb
  simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr] at hb
  obtain ⟨w, h0, hs', ht⟩ := hb
  refine ⟨fun t => BitString.readPackedField (u (.inl 0)).val (fun r => (w r).val)
    (t * (u (.inl 2)).val) (u (.inl 2)).val, ?_, ?_, ?_⟩
  · simpa [a] using h0
  · simpa [a] using hs'
  · intro t hts
    simpa [a] using (ht t hts).1

omit [Fact (2 ≤ n)] in
private theorem exists_local_carries (v : Fin 3 → Fin n) {h s j : ℕ} {g : Fin 8 → Fin n}
    (hp : 2 ^ h < n) (hspace : 16 * h < n) (hcap : (s + 1) * s ≤ 16 * h)
    (hspos : 0 < s) (hcwidth : h + 1 < 2 ^ s) (hx : (v 0).val < 2 ^ (h + 1))
    (hprod : (v 0).val * (v 1).val = (v 2).val)
    (hgj : BitString.readPackedField h (fun r => (g r).val) j s =
      BitString.mulCarry (v 0).val (v 1).val j)
    (hgj' : BitString.readPackedField h (fun r => (g r).val) (j + s) s =
      BitString.mulCarry (v 0).val (v 1).val (j + s)) :
    ∃ w : Fin 16 → Fin n,
      let c := fun t => BitString.readPackedField h (fun r => (w r).val) (t * s) s
      c 0 = BitString.readPackedField h (fun r => (g r).val) j s ∧
      c s = BitString.readPackedField h (fun r => (g r).val) (j + s) s ∧
      ∀ t < s,
        c t + BitString.mulColumn (v 0).val (v 1).val (j + t) =
          ((v 2).val.testBit (j + t)).toNat + 2 * c (t + 1) ∧
        c t + BitString.mulColumn (v 0).val (v 1).val (j + t) < n := by
  let c := BitString.mulCarry (v 0).val (v 1).val
  have hc (t : ℕ) : c t ≤ h + 1 := BitString.mulCarry_le hx _ _
  let w : Fin 16 → Fin n := fun r =>
    ⟨BitString.packWords (fun b => (c (j + b / s)).testBit (b % s)) h 16 r,
      lt_trans (BitString.packWords_lt ..) hp⟩
  have hw (t : ℕ) (ht : t ≤ s) :
      BitString.readPackedField h (fun r => (w r).val) (t * s) s = c (j + t) :=
    BitString.readPackedField_fields (fun t => c (j + t)) hspos
      (by nlinarith) (lt_of_le_of_lt (hc _) hcwidth)
  refine ⟨w, ?_, ?_, ?_⟩
  · change BitString.readPackedField h (fun r => (w r).val) (0 * s) s =
      BitString.readPackedField h (fun r => (g r).val) j s
    rw [hw 0 (by lia), hgj, Nat.add_zero]
  · change BitString.readPackedField h (fun r => (w r).val) (s * s) s =
      BitString.readPackedField h (fun r => (g r).val) (j + s) s
    rw [hw s (le_refl _), hgj']
  · intro t ht
    change BitString.readPackedField h (fun r => (w r).val) (t * s) s +
        BitString.mulColumn (v 0).val (v 1).val (j + t) =
          ((v 2).val.testBit (j + t)).toNat +
            2 * BitString.readPackedField h (fun r => (w r).val) ((t + 1) * s) s ∧
      BitString.readPackedField h (fun r => (w r).val) (t * s) s +
        BitString.mulColumn (v 0).val (v 1).val (j + t) < n
    rw [hw t (by lia), hw (t + 1) (by lia)]
    constructor
    · have heq := BitString.mulCarry_add_column (v 0).val (v 1).val (j + t)
      rw [hprod] at heq
      simpa only [c, Nat.add_assoc] using heq
    · have := hc (j + t)
      have := BitString.mulColumn_le hx (v 1).val (j + t)
      lia

private theorem packedFormula_complete (v : Fin 3 → Fin n) (hn : 257 ≤ n)
    (hprod : (v 0).val * (v 1).val = (v 2).val) : (packedFormula L).Realize v := by
  obtain ⟨h, e, m, hlo, hhi, hh, hspace, hem, hsh, hcwidth, hkw, hks, hcap⟩ :=
    exists_parameters hn
  let s := 2 ^ e
  let k := 2 ^ m
  change s ≤ h at hsh
  change h + 1 < 2 ^ s at hcwidth
  change 2 * (h + 1) ≤ k at hkw
  change k + s ≤ 8 * h at hks
  change (s + 1) * s ≤ 16 * h at hcap
  have hp : 2 ^ h < n := by lia
  have hhn : h < n := by lia
  have hsn : s < n := by lia
  have hkn : k < n := by lia
  have hmn : m < n := lt_trans Nat.lt_two_pow_self hkn
  have hen : e < n := lt_of_le_of_lt hem hmn
  have hspos : 0 < s := Nat.two_pow_pos e
  have hdiv : s ∣ k := Nat.pow_dvd_pow 2 hem
  have hdivmul : k / s * s = k := Nat.div_mul_cancel hdiv
  have hwidth : 2 ^ s < n := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hsh) hp
  have hcapn : (s + 1) * s < n := by lia
  have hinput (i : Fin 3) : (v i).val < 2 ^ (h + 1) := by have := (v i).isLt; lia
  let c := BitString.mulCarry (v 0).val (v 1).val
  have hc (t : ℕ) : c t ≤ h + 1 := BitString.mulCarry_le (hinput 0) _ _
  let g : Fin 8 → Fin n := fun r =>
    ⟨BitString.packWords (fun a => (c (a / s * s)).testBit (a % s)) h 8 r,
      lt_trans (BitString.packWords_lt ..) hp⟩
  have hg (q : ℕ) (hq : q * s + s ≤ 8 * h) :
      BitString.readPackedField h (fun r => (g r).val) (q * s) s = c (q * s) :=
    BitString.readPackedField_fields (fun q => c (q * s)) hspos hq
      (lt_of_le_of_lt (hc _) hcwidth)
  have hg0 := hg 0 (by lia)
  simp only [Nat.zero_mul, c, BitString.mulCarry_zero] at hg0
  have hgk := hg (k / s) (by rw [hdivmul]; exact hks)
  rw [hdivmul] at hgk
  have hck : c k = 0 := BitString.mulCarry_eq_zero (hinput 0) (hinput 1) hkw
  rw [hck] at hgk
  let u : (Fin 5 ⊕ Fin 8) → Fin n :=
    Sum.elim ![⟨h, hhn⟩, ⟨e, hen⟩, ⟨s, hsn⟩, ⟨m, hmn⟩, ⟨k, hkn⟩] g
  simp only [packedFormula, Formula.realize_iExs]
  refine ⟨u, ?_⟩
  simp only [Formula.realize_inf, and_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [realize_parameters]
    exact ⟨hlo, hhi, rfl, rfl, hem, hsh, hspace, hkw, hks, hcap⟩
  · rw [realize_packedField _ _ _ _ _ _ (by simpa [u] using (show 8 * h < n by lia))]
    simpa [u] using hg0.symm
  · rw [realize_packedField _ _ _ _ _ _ (by simpa [u] using (show 8 * h < n by lia))]
    simpa [u] using hgk.symm
  · simp only [allBlocks, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      Formula.realize_not, realize_shiftLeft, realize_le, Term.realize_var,
      Term.realize_relabel, Function.comp_def, Sum.elim_inr, Sum.elim_inl, not_le]
    intro a ⟨haj, hak⟩
    change (a 0).val * s = (a 1).val at haj
    change (a 1).val < k at hak
    have hjend : (a 1).val + s ≤ k := by
      rw [← haj]
      exact block_end_le hspos hdiv (by rwa [haj])
    rw [realize_blockChecks _ _ _ _ _ _ _ _ _ (by rfl)
      (by simpa [u] using hcapn) (by simpa [u] using (show (a 1).val + s < n by lia))
      (by simpa [u] using hwidth) (by simpa [u] using hspace)]
    simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr]
    refine exists_local_carries v (h := h) (s := s) (j := (a 1).val) (g := g)
      hp hspace hcap hspos hcwidth (hinput 0) hprod ?_ ?_
    · rw [← haj]
      exact hg (a 0).val (by rw [haj]; lia)
    · have ht := hg ((a 0).val + 1) (by rw [Nat.add_mul, Nat.one_mul, haj]; lia)
      simpa only [Nat.add_mul, Nat.one_mul, haj] using ht

end Multiplication

/-- Native TIMES over canonical order and BIT, with ordinary, nonmodular product semantics. -/
public noncomputable def multiplication (L : Language) : (language L).Formula (Fin 3) :=
  Multiplication.smallFormula L ⊔ Multiplication.packedFormula L

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The single native formula realizes exactly natural-number multiplication. In particular,
no candidate output satisfies it when the product is outside `Fin n`. -/
@[simp, fo_realize]
public theorem realize_multiplication (v : Fin 3 → Fin n) :
    (multiplication L).Realize v ↔ (v 0).val * (v 1).val = (v 2).val := by
  simp only [multiplication, Formula.realize_sup]
  constructor
  · rintro (hsmall | hlarge)
    · simp only [Multiplication.smallFormula, Formula.realize_iSup, Formula.realize_inf,
        realize_natEq, realize_scaleEq, Term.realize_var] at hsmall
      obtain ⟨a, ha, he⟩ := hsmall
      simpa only [ha] using he
    · exact Multiplication.packedFormula_sound v hlarge
  · intro hprod
    by_cases hx : (v 0).val < 256
    · left
      simp only [Multiplication.smallFormula, Formula.realize_iSup, Formula.realize_inf,
        realize_natEq, realize_scaleEq, Term.realize_var]
      exact ⟨⟨(v 0).val, hx⟩, rfl, hprod⟩
    · right
      exact Multiplication.packedFormula_complete v (by have := (v 0).isLt; lia) hprod

/-- No element represents a product outside the universe; truncation is not accepted. -/
public theorem not_realize_multiplication_of_le (v : Fin 3 → Fin n)
    (h : n ≤ (v 0).val * (v 1).val) : ¬(multiplication L).Realize v := by
  rw [realize_multiplication]
  have := (v 2).isLt
  lia

/-- Every representable ordinary product has exactly one output. -/
public theorem existsUnique_multiplication (x y : Fin n) (hxy : x.val * y.val < n) :
    ∃! z : Fin n, (multiplication L).Realize ![x, y, z] := by
  refine ⟨⟨x.val * y.val, hxy⟩, ?_, ?_⟩
  · exact (realize_multiplication _).mpr rfl
  · intro z hz
    rw [realize_multiplication] at hz
    exact Fin.ext hz.symm

end Cslib.Logic.FO.Ordered

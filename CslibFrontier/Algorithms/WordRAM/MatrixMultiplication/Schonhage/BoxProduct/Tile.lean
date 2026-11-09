/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Arguments
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Charges
public import CslibFrontier.Algorithms.MatrixMultiplication.Schonhage.Magnitude

/-!
# One actual routed tile against shared box geometry

The real saved offsets determine the query span. Its typed codes, inner-coordinate count,
source encodings and original matrix coordinates are recovered from the existing native
producer contracts. One retained table, sparse batch and actual answer copy are charged.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

set_option maxRecDepth 4096 in
-- The fixed caller frame check unfolds the existing 32-member 160-register protocol.
/-- One actual tile builds retained values, answers its real grouped span and delivers all
signed matrix-product answers, retaining the one shared geometry and producer arrays. -/
theorem exec_tileStep {w L m t N A j : ℕ} (hw : 0 < w) (hm : m ≤ L) (ht : t ≤ m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (old : ℕ → ℕ) (x : Data 160)
    (hp : QueriedProduct.Parameters L m N qs.length x) (hb : Parameters L m t N qs.length x)
    (hx : x.regs QueriedProduct.Reg.index = j) (hj : j < numBands L m N ^ 2)
    (hg : QueriedProduct.SavedGroups L m N qs.length old x.mem)
    (he : QueriedProduct.EncodedBands hm X Y x.mem) (hgeom : Geometry L m t N qs.length x.mem)
    (hvalues : ∀ i : Fin qs.length,
      old (Wanted.codeAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (hoffsets : ∀ s ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N qs.length + s) =
        Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < s) qs.length)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k i, |Y k i| ≤ (A : ℤ))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m t N qs.length)) :
    let a := x.mem (QueriedProduct.offsetBase L m N qs.length + j)
    let b := x.mem (QueriedProduct.offsetBase L m N qs.length + j + 1)
    ∃ y, ExecWithin (w + 2) tileStep x y
        (328 * (boxes L m t).card + (b - a) * (batchUnit L m t + 7) + 63) ∧
      QueriedProduct.Parameters L m N qs.length y ∧ Parameters L m t N qs.length y ∧
      y.regs QueriedProduct.Reg.index = j + 1 ∧
      QueriedProduct.SavedGroups L m N qs.length old y.mem ∧
      QueriedProduct.EncodedBands hm X Y y.mem ∧ Geometry L m t N qs.length y.mem ∧
      (∀ i : Fin qs.length, (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i.val = j →
        y.mem (QueriedProduct.groupedBase L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
            Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ p, ¬(QueriedProduct.groupedBase L m N qs.length + a ≤ p ∧
          p < QueriedProduct.groupedBase L m N qs.length + b) →
        ¬(directoryBase L m N qs.length ≤ p ∧ p < memoryEnd L m t N qs.length) →
          y.mem p = x.mem p) := by
  dsimp only
  let B := numBands L m N
  let a := x.mem (QueriedProduct.offsetBase L m N qs.length + j)
  let b := x.mem (QueriedProduct.offsetBase L m N qs.length + j + 1)
  let β := j / B
  let γ := j % B
  let pa := BandPreparation.catalogueBase L m N + β * 10 ^ L
  let pb := BandPreparation.catalogueBase L m N + (B + γ) * 10 ^ L
  let encA := encodingL (bandArrayL (MaskTable.layout hm) X β)
  let encB := encodingR (bandArrayR (MaskTable.layout hm) Y γ)
  let D0 := directoryBase L m N qs.length
  let R0 := recordBase L m t N qs.length
  let V := valueBase L m t N qs.length
  let K := (boxes L m t).card
  let O := resultBase L m t N qs.length
  have habQ := hg.span_bounds (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) hoffsets hj
  have hB : 0 < B := by dsimp only [B] at *; nlinarith only [hj, Nat.zero_le j]
  have hβ : β < B := (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [B, pow_two] using hj)
  have hγ : γ < B := Nat.mod_lt j hB
  have hT : (β, γ) ∈ tiles L m N :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hβ, Finset.mem_range.mpr hγ⟩
  have hnum : β * numBands L m N + γ = j := by
    simpa only [β, γ, B, Nat.mul_comm] using Nat.div_add_mod j B
  have hcode (k : ℕ) (hk : k < qs.length) :
      x.mem (QueriedProduct.codeBase L m N qs.length + k) < 10 ^ L := by
    rw [hg.codes k hk]
    exact QueriedProduct.router_code_lt hm qs old hvalues k hk
  let queries : Fin (b - a) → OutStr L := fun i => PrunedQuery.queryAt
    ⟨x.mem (QueriedProduct.codeBase L m N qs.length + (a + i.val)),
      hcode _ (by have := i.isLt; omega)⟩
  let wanted := List.ofFn queries
  have hinput (i : Fin (b - a)) :
      x.mem (QueriedProduct.codeBase L m N qs.length + (a + i.val)) =
        (PrunedQuery.queryIndex (queries i)).val := by
    simp only [queries, PrunedQuery.queryIndex_queryAt]
  have hset : Finset.univ.image queries =
      wantedStrings (MaskTable.layout hm) qs.toFinset β γ :=
    hg.span_queries hm qs hvalues hoffsets (β, γ) hT a b (by rw [hnum])
      (by rw [hnum]; rfl) queries hinput
  have hinner : ∀ η ∈ wanted, (innerSetO η).card = m := by
    intro η hη
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hη
    apply card_innerSetO_of_mem_wantedStrings (MaskTable.layout hm) qs.toFinset β γ
    rw [← hset]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨arg, har, arp, arb, arm, ari, arc, arinner, arth, arV, arK,
      arA, arB, arq, ars, aro, ard, arlen⟩ :=
    exec_tileArguments x hp hb hx hj rfl rfl habQ.1 habQ.2 hfit
  change (arg.comap boxBank).regs BoxTable.Reg.arrayA = pa at arA
  change (arg.comap boxBank).regs BoxTable.Reg.arrayB = pb at arB
  change (arg.comap boxBank).regs BoxTable.Reg.values = V at arV
  change (arg.comap boxBank).regs BoxTable.Reg.count = K at arK
  have hpab : pa + 10 ^ L ≤ BandPreparation.memoryEnd L m N ∧
      pb + 10 ^ L ≤ BandPreparation.memoryEnd L m N := by
    have hl := BandPreparation.catalogue_block_le false hβ
    have hr := BandPreparation.catalogue_block_le true hγ
    simpa only [BandPreparation.catalogueAddress, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add, Nat.add_zero, pa, pb, B] using And.intro hl hr
  have horder := allocation_order L m t N qs.length
  have hbefore : BandPreparation.memoryEnd L m N ≤ D0 := horder.1
  have hgroup : QueriedProduct.groupedBase L m N qs.length + qs.length ≤ D0 := horder.2.1
  have hqueries : QueriedProduct.codeBase L m N qs.length + qs.length ≤ D0 := horder.2.2.1
  have hVorder : D0 ≤ R0 ∧ R0 ≤ V ∧ V + K ≤ O := horder.2.2.2
  have hpaD : pa ≤ D0 := (Nat.le_add_right pa (10 ^ L)).trans (hpab.1.trans hbefore)
  have hpbD : pb ≤ D0 := (Nat.le_add_right pb (10 ^ L)).trans (hpab.2.trans hbefore)
  have hpaV : pa + 10 ^ L ≤ V :=
    hpab.1.trans (hbefore.trans (hVorder.1.trans hVorder.2.1))
  have hpbV : pb + 10 ^ L ≤ V :=
    hpab.2.trans (hbefore.trans (hVorder.1.trans hVorder.2.1))
  have hqD : QueriedProduct.codeBase L m N qs.length + a ≤ D0 :=
    (Nat.add_le_add_left (habQ.1.trans habQ.2) _).trans hqueries
  have hleft (c : Fin (10 ^ L)) :
      arg.mem (pa + c.val) = Signed.encode (encA (BoxTable.leafAt c)) := by
    rw [arm]
    simpa only [pa, encA, BandPreparation.catalogueAddress, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add, Nat.add_assoc, BoxTable.leafIndex_leafAt] using
        he.left β hβ (BoxTable.leafAt c)
  have hright (c : Fin (10 ^ L)) :
      arg.mem (pb + c.val) = Signed.encode (encB (BoxTable.leafAt c)) := by
    rw [arm]
    simpa only [pb, encB, B, BandPreparation.catalogueAddress, ↓reduceIte,
      Nat.add_assoc, BoxTable.leafIndex_leafAt] using he.right γ hγ (BoxTable.leafAt c)
  have haB (τ : Leaf L) : (encA τ).natAbs ≤ encodedBound L A := by
    have h := abs_encodingL_le (abs_bandArrayL_le (MaskTable.layout hm) (by positivity) hX β) τ
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hbB (τ : Leaf L) : (encB τ).natAbs ≤ encodedBound L A := by
    have h := abs_encodingR_le (abs_bandArrayR_le (MaskTable.layout hm) (by positivity) hY γ) τ
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have htablemag : GenericRAM.Signed.Fits w
      (encodedBound L A + encodedBound L A + 10 ^ L * (encodedBound L A * encodedBound L A) : ℕ) :=
    (box_magnitude hw hmag).of_natAbs_le (by
      simpa only [Int.natAbs_natCast] using BoxQuery.table_magnitudeBound_le L
        (encodedBound L A) (encodedBound L A))
  have hspan : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨z, hz, zv, zf, zregs⟩ := BoxTable.exec_tile (arg.comap boxBank) encA encB haB hbB arc
    arV arA arB (by rw [arK, BoxTable.count_eligible_eq_card_boxes])
    (by simpa only [Data.comap_mem, arm] using hgeom.catalogue)
    (by rfl) (by rw [BoxTable.count_eligible_eq_card_boxes]; rfl)
    hpaV hpbV hleft hright (tile_fits hfit hpaD hpbD) htablemag
  rw [BoxTable.count_eligible_eq_card_boxes] at hz zf
  let u := z.extend boxBank arg
  have hu := hz.rename boxBank_injective
  have ur (i : Fin 160) (hi : 64 ≤ i.val) : u.regs i = arg.regs i := boxBank_extend_high z arg i hi
  have up : QueriedProduct.Parameters L m N qs.length u := arp.reframe (fun i hi => ur i (by omega))
  have ub : Parameters L m t N qs.length u := arb.extend z
  have ulow (i : Fin 64) (hi : ¬BoxTable.TileLocal i) :
      (u.comap boxBank).regs i = (arg.comap boxBank).regs i := by
    simpa only [u, Data.comap_extend boxBank_injective] using zregs i hi
  have uread : BoxQuery.Readback m t D0 V pa pb encA encB u.mem := by
    change BoxQuery.Readback m t D0 V pa pb encA encB z.mem
    constructor
    · intro c
      rw [zf _ (by have := c.isLt; omega)]
      exact hleft c
    · intro c
      rw [zf _ (by have := c.isLt; omega)]
      exact hright c
    · intro s hs
      rw [zf _ (by dsimp only [D0, V]; unfold valueBase recordBase; omega), Data.comap_mem, arm]
      exact hgeom.directory s hs
    · exact zv
  have ux : BoxBatch.Arguments L t pa pb D0 V K (u.comap boxBank) :=
    ⟨(ulow _ (by decide)).trans arc.levels, (ulow _ (by decide)).trans arth,
      (ulow _ (by decide)).trans arc.span, (ulow _ (by decide)).trans arA,
      (ulow _ (by decide)).trans arB, (ulow _ (by decide)).trans arc.directory,
      (ulow _ (by decide)).trans arV, (ulow _ (by decide)).trans arK⟩
  have uwanted (i : Fin wanted.length) : u.mem
      (QueriedProduct.codeBase L m N qs.length + a + i.val) =
        (PrunedQuery.queryIndex (wanted.get i)).val := by
    change z.mem _ = _
    rw [zf _ (by have := i.isLt; simp only [wanted, List.length_ofFn] at this; omega),
      Data.comap_mem, arm]
    simpa only [wanted, List.get_eq_getElem, List.getElem_ofFn, Nat.add_assoc] using
      hinput ⟨i.val, by simpa only [wanted, List.length_ofFn] using i.isLt⟩
  obtain ⟨q, hq, _, _, _, _, qv, _, qf⟩ := BoxBatch.exec_queryProgram wanted (u.comap boxBank)
    ux ((ulow _ (by decide)).trans arq)
    (by
      calc
        (u.comap boxBank).regs BoxBatch.Reg.stop = QueriedProduct.codeBase L m N qs.length + b := by
          simpa only [b, Nat.add_assoc] using (ulow _ (by decide)).trans ars
        _ = (QueriedProduct.codeBase L m N qs.length + a) + wanted.length := by
          simp only [wanted, List.length_ofFn]
          omega) ((ulow _ (by decide)).trans aro)
    encA encB haB hbB hinner uwanted rfl (by omega) (by omega)
    (by dsimp only [D0, V]; unfold valueBase recordBase; omega)
    (by simp only [wanted, List.length_ofFn]; omega) (by rfl) uread
    (batch_fits hfit hpaD hpbD hqD (by
      simp only [wanted, List.length_ofFn]; omega)) (box_magnitude hw hmag)
  have hqtime : BoxBatch.queryTime m t wanted = (b - a) * batchUnit L m t + 2 := by
    simpa only [wanted, List.length_ofFn, batchUnit] using
      BoxBatch.queryTime_eq_alpha wanted hinner
  rw [hqtime] at hq
  let v := q.extend boxBank u
  have hv := hq.rename boxBank_injective
  have vr (i : Fin 160) (hi : 64 ≤ i.val) : v.regs i = u.regs i := boxBank_extend_high q u i hi
  have vp : QueriedProduct.Parameters L m N qs.length v := up.reframe (fun i hi => vr i (by omega))
  have vb : Parameters L m t N qs.length v := ub.extend q
  have vd : v.regs QueriedProduct.Reg.destination =
      QueriedProduct.groupedBase L m N qs.length + a :=
    (vr _ (by decide)).trans ((ur _ (by decide)).trans ard)
  have vl : v.regs QueriedProduct.Reg.length = b - a :=
    (vr _ (by decide)).trans ((ur _ (by decide)).trans arlen)
  let c := v.set QueriedProduct.Reg.source O
  have hc : ExecWithin (B := .standard) (w + 2)
      (ram[QueriedProduct.Reg.source ← Reg.results]) v c 1 := by
    ram_eval [c, vb.results, O]
  have cp : QueriedProduct.Parameters L m N qs.length c :=
    vp.set_work _ (by decide) _
  have cs : c.regs QueriedProduct.Reg.source = O := by simp [c]
  have cd : c.regs QueriedProduct.Reg.destination =
      QueriedProduct.groupedBase L m N qs.length + a :=
    (hc.regs_eq (by decide)).trans vd
  have cl : c.regs QueriedProduct.Reg.length = b - a := (hc.regs_eq (by decide)).trans vl
  obtain ⟨d, hd, dm, dr⟩ := QueriedProduct.exec_copyCall c
    (hfit.of_le (by unfold wordBudget; omega))
    (by rw [cs, cl]; apply allocated_fits hfit; dsimp only [O]; unfold memoryEnd; omega)
    (by rw [cd, cl]; apply allocated_fits hfit; unfold memoryEnd; dsimp only [O] at *; omega)
    (by rw [cs, cd, cl]; exact Or.inr (Or.inl (by omega)))
  have dp : QueriedProduct.Parameters L m N qs.length d := cp.reframe (fun i hi => dr i (by omega))
  have di : d.regs QueriedProduct.Reg.index = j :=
    (dr _ (by decide)).trans ((hc.regs_eq (by decide)).trans
      ((vr _ (by decide)).trans ((ur _ (by decide)).trans ari)))
  have fnext : Fits (w + 2) (j + 1) := index_fits hfit hj
  let y := d.set QueriedProduct.Reg.index (j + 1)
  have hy : ExecWithin (B := .standard) (w + 2)
      (ram[QueriedProduct.Reg.index ← QueriedProduct.Reg.index + QueriedProduct.Reg.one])
      d y 1 := by
    ram_eval [y, di, dp.one, fnext]
  have yp : QueriedProduct.Parameters L m N qs.length y := dp.set_work _ (by decide) _
  have native : ExecWithin (w + 2) tileStep x y
      (328 * K + (b - a) * (batchUnit L m t + 7) + 63) := by
    apply (har.seq (hu.seq (hv.seq ((hc.seq hd).seq hy)))).mono
    rw [cl]
    simp only [Nat.mul_add]
    omega
  have vframe (p : ℕ) (hf : ¬(V ≤ p ∧ p < memoryEnd L m t N qs.length)) :
      v.mem p = x.mem p := by
    change q.mem p = x.mem p
    have hO : V + K + 5 * BoxQuery.stackCapacity L = O := rfl
    have hEnd : memoryEnd L m t N qs.length = O + qs.length := rfl
    rw [qf p (by
      simp only [wanted, List.length_ofFn]
      change ¬((V + K ≤ p ∧ p < V + K + 5 * BoxQuery.stackCapacity L) ∨
        (O ≤ p ∧ p < O + (b - a)))
      rw [hO]
      rw [hEnd] at hf
      omega)]
    change z.mem p = x.mem p
    rw [zf p (by rw [hEnd] at hf; omega), Data.comap_mem, arm]
  have ym : y.mem = ArrayCopy.copyPrefix v.mem O
      (QueriedProduct.groupedBase L m N qs.length + a) (b - a) := by
    simpa only [y, Data.set_mem, cs, cd, cl, c] using dm
  have strongframe (p : ℕ)
      (ho : ¬(QueriedProduct.groupedBase L m N qs.length + a ≤ p ∧
        p < QueriedProduct.groupedBase L m N qs.length + b))
      (hf : ¬(V ≤ p ∧ p < memoryEnd L m t N qs.length)) : y.mem p = x.mem p := by
    rw [ym, ArrayCopy.copyPrefix_outside (by omega), vframe p hf]
  have frame (p : ℕ)
      (ho : ¬(QueriedProduct.groupedBase L m N qs.length + a ≤ p ∧
        p < QueriedProduct.groupedBase L m N qs.length + b))
      (hf : ¬(D0 ≤ p ∧ p < memoryEnd L m t N qs.length)) : y.mem p = x.mem p :=
    strongframe p ho (by omega)
  refine ⟨y, native, yp, ?_, by simp [y], ?_, ?_, ?_, ?_, frame⟩
  · exact ⟨(native.regs_eq (by decide)).trans hb.threshold,
      (native.regs_eq (by decide)).trans hb.directory,
      (native.regs_eq (by decide)).trans hb.records,
      (native.regs_eq (by decide)).trans hb.values,
      (native.regs_eq (by decide)).trans hb.count,
      (native.regs_eq (by decide)).trans hb.results⟩
  · exact hg.reframe (fun p hp hbefore => frame p (by omega) (by omega))
  · exact he.reframe (fun p hp => frame p
      (by have h := band_before_grouped L m N qs.length; omega) (by omega))
  · exact hgeom.reframe (fun p hD hV => strongframe p (by omega) (by omega))
  · intro i hkey
    let p := CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i
    have hp : p < qs.length := CountingSort.position_lt _ i.isLt
    have hspan : a ≤ p ∧ p < b := by
      have hs := (CountingSort.position_mem_iff
        (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i.isLt j).mpr hkey
      have ha := (hg.offsets j hj.le).trans (hoffsets j hj.le)
      have hb := (hg.offsets (j + 1) (by omega)).trans (hoffsets (j + 1) (by omega))
      change a = _ at ha
      change b = _ at hb
      simpa only [← ha, ← hb] using hs
    let k : Fin (b - a) := ⟨p - a, by omega⟩
    have hak : a + k.val = p := by dsimp only [k]; omega
    have hquery : queries k = outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2 := by
      have hr := hinput k
      rw [hak, hg.codes p hp, hvalues i] at hr
      simpa only [PrunedQuery.queryAt_queryIndex] using
        congrArg PrunedQuery.queryAt (Fin.ext hr.symm)
    have htile : Wanted.tileKey L m N ((qs.get i).1.val, (qs.get i).2.val) =
        β * numBands L m N + γ := by
      simpa only [Function.comp_apply, Wanted.inputPairs_get, hnum] using hkey
    have hbands := (Wanted.tileKey_eq_iff hm (qs.get i).1 (qs.get i).2 (β, γ) hT).mp htile
    change bandOf L m (qs.get i).1.val = β ∧ bandOf L m (qs.get i).2.val = γ at hbands
    have hr := qv ⟨k.val, by simp only [wanted, List.length_ofFn]; exact k.isLt⟩
    simp only [wanted, List.get_eq_getElem, List.getElem_ofFn] at hr
    rw [hquery, BoxQuery.queryValue_encoding ht _
      (card_innerSetO_of_mem_wantedStrings (MaskTable.layout hm) qs.toFinset β γ _ (by
        rw [← hset]; exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hquery⟩))] at hr
    change q.mem (O + k.val) = _ at hr
    rw [ym]
    have hcopy := ArrayCopy.copyPrefix_read (mem := v.mem) (src := O)
      (dst := QueriedProduct.groupedBase L m N qs.length + a) (k := b - a) k.isLt
    have haddr : QueriedProduct.groupedBase L m N qs.length + a + k.val =
        QueriedProduct.groupedBase L m N qs.length + p := by omega
    rw [haddr] at hcopy
    rw [hcopy]
    change v.mem (O + k.val) = _ at hr
    rw [hr]
    congr 1
    rw [← hbands.1, ← hbands.2]
    exact bilinearProduct_bandArray_eq_mul (MaskTable.layout hm) X Y _ _

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

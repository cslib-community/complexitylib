/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram

/-!
# Actual header loads, native powers and concrete band addresses

## Main results

* `BandPreparation.exec_powerCode`: exact reuse of the five-register native power routine.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Renaming the actual power routine has no instruction overhead and changes only its
accumulator, counter and constant-one register. -/
theorem exec_powerCode {w : ℕ} (v b n : Fin 96)
    (hinj : Function.Injective (powerRegisters v b n)) (B M : ℕ) (hB : 1 ≤ B)
    (x : Data 96) (hb : x.regs b = B) (hn : x.regs n = M)
    (hfit : Fits w (B ^ M + M + 2)) :
    ∃ y, ExecWithin w (powerCode v b n) x y (4 * M + 5) ∧
      y.regs v = B ^ M ∧ y.regs one = 1 ∧ y.mem = x.mem ∧
      (∀ i, i ≠ v → i ≠ counter → i ≠ one → y.regs i = x.regs i) := by
  obtain ⟨z, hz, hv, _, ho, hm, _, _⟩ :=
    Power.exec B M hB (x.comap (powerRegisters v b n)) hb hn hfit
  have he := hz.rename hinj
  refine ⟨z.extend (powerRegisters v b n) x, he, ?_, ?_, hm, ?_⟩
  · have h := congrArg (fun d : Data 5 => d.regs Power.value) (Data.comap_extend hinj z x)
    exact h.trans hv
  · have h := congrArg (fun d : Data 5 => d.regs Power.one) (Data.comap_extend hinj z x)
    exact h.trans ho
  · intro i hv hc ho
    apply he.regs_eq
    simp [Power.program, Power.body, Code.rename, Code.Preserves, Op.rename, Op.dest, Op.bin,
      powerRegisters, Power.value, Power.counter, Power.base, Power.exponent, Power.one,
      Ne.symm hv, Ne.symm hc, Ne.symm ho]

/-- Scalar parameters loaded from the three actual input headers and small constants. -/
structure BasicParameters (L m N : ℕ) (x : Data 96) : Prop where
  /-- Input depth. -/
  levels : x.regs levels = L
  /-- Input inner cardinality. -/
  inner : x.regs inner = m
  /-- Input matrix dimension. -/
  rows : x.regs rows = N
  /-- Constant zero. -/
  zero : x.regs zero = 0
  /-- Constant one. -/
  one : x.regs one = 1
  /-- Constant two. -/
  two : x.regs two = 2
  /-- Constant three. -/
  three : x.regs three = 3
  /-- Constant four. -/
  four : x.regs four = 4
  /-- Constant seven. -/
  seven : x.regs seven = 7
  /-- Constant ten. -/
  ten : x.regs ten = 10

private def basicRegisters : Finset (Fin 96) :=
  {levels, inner, rows, zero, two, three, four, seven, ten}

private theorem BasicParameters.of_frame {L m N : ℕ} {x y : Data 96}
    (hx : BasicParameters L m N x) (hone : y.regs BandPreparation.one = 1)
    (h : ∀ i ∈ basicRegisters, y.regs i = x.regs i) : BasicParameters L m N y :=
  ⟨(h _ (by decide)).trans hx.levels, (h _ (by decide)).trans hx.inner,
    (h _ (by decide)).trans hx.rows, (h _ (by decide)).trans hx.zero, hone,
    (h _ (by decide)).trans hx.two, (h _ (by decide)).trans hx.three,
    (h _ (by decide)).trans hx.four, (h _ (by decide)).trans hx.seven,
    (h _ (by decide)).trans hx.ten⟩

private theorem BasicParameters.after_power {L m N : ℕ} {v : Fin 96} {x y : Data 96}
    (hx : BasicParameters L m N x) (hv : v ∉ basicRegisters)
    (hone : y.regs BandPreparation.one = 1)
    (hf : ∀ i, i ≠ v → i ≠ counter → i ≠ BandPreparation.one → y.regs i = x.regs i) :
    BasicParameters L m N y := hx.of_frame hone (by
  intro i hi
  have hstatic : ∀ i ∈ basicRegisters, i ≠ counter ∧ i ≠ BandPreparation.one := by decide
  exact hf i (fun heq => hv (heq ▸ hi)) (hstatic i hi).1 (hstatic i hi).2)

/-- The global numerical budget bounds every final header power and its exponent. -/
theorem power_fits {w L m N : ℕ} (hfit : Fits w (wordBudget L m N))
    (b n : ℕ) (hb : b ≤ 10) (hn : n ≤ L) : Fits w (b ^ n + n + 2) := by
  have hp : b ^ n ≤ 10 ^ L :=
    (Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right (by decide) hn)
  have hpos : 1 ≤ 10 ^ L := Nat.one_le_pow L 10 (by decide)
  apply hfit.of_le
  unfold wordBudget
  nlinarith only [hp, hn, hpos, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (2 * numBands L m N * 10 ^ L)]

/-- All header powers are computed by five actual native loops. Their register embeddings
are injective and their complete cost is linear in the original depth. -/
theorem exec_headerPowers {w L m N : ℕ} (hm : m ≤ L) (x : Data 96)
    (hx : BasicParameters L m N x) (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w headerPowers x y (16 * L + 26) ∧ BasicParameters L m N y ∧
      y.regs columns = D m ∧ y.regs outerSize = N0 L m ∧ y.regs masks = 2 ^ L ∧
      y.regs cells = 7 ^ L ∧ y.regs leaves = 10 ^ L ∧ y.mem = x.mem := by
  obtain ⟨x1, h1, hD, ho1, hm1, hf1⟩ := exec_powerCode columns four inner (by decide)
    4 m (by decide) x hx.four hx.inner (power_fits hfit 4 m (by decide) hm)
  have hp1 : BasicParameters L m N x1 := hx.after_power (by decide) ho1 hf1
  let x2 := x1.set temporary (L - m)
  have hsub : ExecWithin w (ram[ temporary ← levels - inner ]) x1 x2 1 := by
    have hL := power_fits hfit 1 L (by decide) le_rfl
    have hs : Fits w (L - m) := hL.of_le (by simp only [one_pow]; omega)
    ram_eval [x2, hp1.levels, hp1.inner, hs, temporary, levels, inner]
  have ho2 : x2.regs one = 1 := by simpa [x2, temporary, one] using hp1.one
  have hp2 : BasicParameters L m N x2 := hp1.of_frame ho2 (by
    intro i hi
    apply hsub.regs_eq
    have hf : ∀ i ∈ basicRegisters, (ram[ temporary ← levels - inner ]).Preserves i := by
      simp only [Code.Preserves, Op.dest_bin]
      decide
    exact hf i hi)
  have htemp : x2.regs temporary = L - m := by simp [x2]
  obtain ⟨x3, h3, hN0, ho3, hm3, hf3⟩ := exec_powerCode outerSize three temporary (by decide)
    3 (L - m) (by decide) x2 hp2.three htemp
    (power_fits hfit 3 (L - m) (by decide) (Nat.sub_le _ _))
  have hp3 : BasicParameters L m N x3 := hp2.after_power (by decide) ho3 hf3
  obtain ⟨x4, h4, hS2, ho4, hm4, hf4⟩ := exec_powerCode masks two levels (by decide)
    2 L (by decide) x3 hp3.two hp3.levels (power_fits hfit 2 L (by decide) le_rfl)
  have hp4 : BasicParameters L m N x4 := hp3.after_power (by decide) ho4 hf4
  obtain ⟨x5, h5, hS7, ho5, hm5, hf5⟩ := exec_powerCode cells seven levels (by decide)
    7 L (by decide) x4 hp4.seven hp4.levels (power_fits hfit 7 L (by decide) le_rfl)
  have hp5 : BasicParameters L m N x5 := hp4.after_power (by decide) ho5 hf5
  obtain ⟨y, h6, hS10, ho6, hm6, hf6⟩ := exec_powerCode leaves ten levels (by decide)
    10 L (by decide) x5 hp5.ten hp5.levels (power_fits hfit 10 L (by decide) le_rfl)
  refine ⟨y, ?_, hp5.after_power (by decide) ho6 hf6, ?_, ?_, ?_, ?_, hS10, ?_⟩
  · apply (h1.seq (hsub.seq (h3.seq (h4.seq (h5.seq h6))))).mono
    omega
  · have hD2 : x2.regs columns = 4 ^ m := by simpa [x2, temporary, columns] using hD
    exact (hf6 columns (by decide) (by decide) (by decide)).trans
      ((hf5 columns (by decide) (by decide) (by decide)).trans
        ((hf4 columns (by decide) (by decide) (by decide)).trans
          ((hf3 columns (by decide) (by decide) (by decide)).trans hD2)))
  · exact (hf6 outerSize (by decide) (by decide) (by decide)).trans
      ((hf5 outerSize (by decide) (by decide) (by decide)).trans
        ((hf4 outerSize (by decide) (by decide) (by decide)).trans hN0))
  · exact (hf6 masks (by decide) (by decide) (by decide)).trans
      ((hf5 masks (by decide) (by decide) (by decide)).trans hS2)
  · exact (hf6 cells (by decide) (by decide) (by decide)).trans hS7
  · exact hm6.trans (hm5.trans (hm4.trans (hm3.trans hm1)))

/-- Concrete computed powers and addresses after native header initialization. -/
structure HeaderPost (L m N : ℕ) (x : Data 96) : Prop where
  /-- Original scalar headers and constants. -/
  fixed : BasicParameters L m N x
  /-- Thin dimension. -/
  columns : x.regs columns = D m
  /-- Outer block dimension. -/
  outerSize : x.regs outerSize = N0 L m
  /-- Complete mask scan range. -/
  masks : x.regs masks = 2 ^ L
  /-- Flat input length of each band array. -/
  cells : x.regs cells = 7 ^ L
  /-- Flat output length of each band encoding. -/
  leaves : x.regs leaves = 10 ^ L
  /-- Original initialized prefix length. -/
  prefixSize : x.regs prefixSize = inputEnd m N
  /-- Protected original-input copy address. -/
  snapshot : x.regs snapshot = snapshotBase L m N
  /-- Dense inverse-table address. -/
  inverse : x.regs inverse = inverseBase L m N
  /-- Selected-mask forward-table address. -/
  table : x.regs table = tableBase L m N
  /-- Shared band-encoding output address. -/
  catalogue : x.regs catalogue = catalogueBase L m N

/-- Header parameters are loaded from real memory, all five powers are computed natively,
and every concrete address calculation is charged. Header zero and all unrelated cells may
contain arbitrary words; initialization reads only addresses one through three. -/
theorem exec_header {w L m N : ℕ} (hm : m ≤ L) (x : Data 96)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w header x y (16 * L + 49) ∧ HeaderPost L m N y ∧ y.mem = x.mem := by
  have h256 : 256 ≤ wordBudget L m N := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hsmall (v : ℕ) (hv : v ≤ 256) : Fits w v := hfit.of_le (hv.trans h256)
  let x0 := (((((((((((((x.set address 1).set levels L).set address 2).set inner m).set
    address 3).set rows N).set zero 0).set one 1).set two 2).set three 3).set four 4).set
    seven 7).set ten 10)
  have hs : ExecWithin w headerLoads x x0 13 := by
    ram_eval [headerLoads, x0, hL, hmemory, hN, hsmall 0 (by decide), hsmall 1 (by decide),
      hsmall 2 (by decide), hsmall 3 (by decide), hsmall 4 (by decide),
      hsmall 7 (by decide), hsmall 10 (by decide),
      address, levels, inner, rows, zero, one, two, three, four, seven, ten, Fin.mk.injEq]
  have hp : BasicParameters L m N x0 := by
    constructor <;> simp [x0, address, levels, inner, rows, zero, one, two, three, four, seven, ten]
  obtain ⟨z, hz, hbasic, hD, hN0, hS2, hS7, hS10, hzmem⟩ := exec_headerPowers hm x0 hp hfit
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have h2 : 2 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have hlocal : Fits w (4 * (N * D m) + 8 * 10 ^ L + 16) := by
    apply hfit.of_le
    unfold wordBudget
    nlinarith only [Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
      Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L),
      Nat.zero_le (2 * numBands L m N * 10 ^ L)]
  let B := N * D m * 2 + 4
  let S := 10 ^ L * 2 + 7 ^ L + 2 + B
  let I := S + B
  let T := I + 2 ^ L
  let C := T + 2 ^ L
  have hnd : Fits w (N * D m) := hlocal.of_le (by omega)
  have hnd2 : Fits w (N * D m * 2) := hlocal.of_le (by omega)
  have hB : Fits w B := hlocal.of_le (by dsimp [B]; omega)
  have ht2 : Fits w (10 ^ L * 2) := hlocal.of_le (by omega)
  have hts : Fits w (10 ^ L * 2 + 7 ^ L) := hlocal.of_le (by omega)
  have hts2 : Fits w (10 ^ L * 2 + 7 ^ L + 2) := hlocal.of_le (by omega)
  have hS : Fits w S := hlocal.of_le (by dsimp [S, B]; omega)
  have hI : Fits w I := hlocal.of_le (by dsimp [I, S, B]; omega)
  have hT : Fits w T := hlocal.of_le (by dsimp [T, I, S, B]; omega)
  have hC : Fits w C := hlocal.of_le (by dsimp [C, T, I, S, B]; omega)
  let y := ((((((((((z.set prefixSize (N * D m)).set prefixSize (N * D m * 2)).set
    prefixSize B).set snapshot (10 ^ L * 2)).set snapshot (10 ^ L * 2 + 7 ^ L)).set
    snapshot (10 ^ L * 2 + 7 ^ L + 2)).set snapshot S).set inverse I).set table T).set catalogue C)
  have hy : ExecWithin w headerLayout z y 10 := by
    ram_eval [headerLayout, y, B, S, I, T, C, hbasic.rows, hbasic.two, hbasic.four,
      hS2, hS7, hS10, hD, hnd, hnd2, hB, ht2, hts, hts2, hS, hI, hT, hC,
      prefixSize, snapshot, inverse, table, catalogue, rows, columns, leaves, cells,
      masks, two, four, Fin.mk.injEq, Function.update_idem]
  have hfixed : BasicParameters L m N y := hbasic.of_frame (by
    simpa [y, prefixSize, snapshot, inverse, table, catalogue, one] using hbasic.one) (by
      intro i hi
      apply hy.regs_eq
      have hf : ∀ i ∈ basicRegisters, headerLayout.Preserves i := by
        simp only [headerLayout, Code.Preserves, Op.dest_bin]
        decide
      exact hf i hi)
  refine ⟨y, ?_, ?_, hzmem⟩
  · exact (hs.seq (hz.seq hy)).mono (by omega)
  · constructor
    · exact hfixed
    · simpa [y, prefixSize, snapshot, inverse, table, catalogue, columns] using hD
    · simpa [y, prefixSize, snapshot, inverse, table, catalogue, outerSize] using hN0
    · simpa [y, prefixSize, snapshot, inverse, table, catalogue, masks] using hS2
    · simpa [y, prefixSize, snapshot, inverse, table, catalogue, cells] using hS7
    · simpa [y, prefixSize, snapshot, inverse, table, catalogue, leaves] using hS10
    · have hb : y.regs prefixSize = B := by
        simp +decide [y, prefixSize, snapshot, inverse, table, catalogue]
      rw [hb]
      dsimp only [B, inputEnd]
      omega
    · have hs : y.regs snapshot = S := by
        simp +decide [y, prefixSize, snapshot, inverse, table, catalogue]
      rw [hs]
      dsimp only [S, B, snapshotBase, inputEnd, Encoding.scratchBase, Encoding.outputBase]
      omega
    · have hi : y.regs inverse = I := by
        simp +decide [y, prefixSize, snapshot, inverse, table, catalogue]
      rw [hi]
      dsimp only [I, S, B, inverseBase, snapshotBase, inputEnd,
        Encoding.scratchBase, Encoding.outputBase]
      omega
    · have ht : y.regs table = T := by
        simp +decide [y, prefixSize, snapshot, inverse, table, catalogue]
      rw [ht]
      dsimp only [T, I, S, B, tableBase, inverseBase, snapshotBase, inputEnd,
        Encoding.scratchBase, Encoding.outputBase]
      omega
    · have hc : y.regs catalogue = C := by simp [y]
      rw [hc]
      dsimp only [C, T, I, S, B, catalogueBase, tableBase, inverseBase, snapshotBase,
        inputEnd, Encoding.scratchBase, Encoding.outputBase]
      omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

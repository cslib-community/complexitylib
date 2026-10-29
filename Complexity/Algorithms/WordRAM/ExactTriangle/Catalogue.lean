/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ChunkCatalogue
public import Complexity.Algorithms.WordRAM.ExactTriangle.Parameters
public import Complexity.Algorithms.WordRAM.ExactTriangle.ResidueClasses

/-!
# Computing an ExactTriangle instance catalogue

The fixed input format is `(D,g,n,p)` followed by the three signed weight matrices. The program
computes residues and query classes, computes the splitting parameters from `D,g,n`, and
concatenates the actual query-chunk descriptors. The caller supplies neither the parameters nor
a class, prefix or descriptor table. Subsequent matrix preparation consumes this catalogue.

This is native composition of the existing Theorem 17 residue, parameter, class and chunk
kernels. The modulus remains a supplied positive argument; prime selection belongs to the outer
ExactTriangle host.

## Main definitions

* `Catalogue.program`: fixed thirty-two-register native catalogue computation.
* `Catalogue.budget`: input-derived numeric bound for arithmetic and allocated addresses.
* `Catalogue.cost`: charged cost before the final halt.
* `Catalogue.Output`: computed parameters, residues, queries, descriptors and memory frame.

## Main results

* `Catalogue.exec_at`: actual execution from the fixed input header, exact parameters, residue
  and query readback, concatenated descriptors and a combined memory frame.

## References

The class/query layout follows the pinned
[Theorem 17 construction](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Classes.lean).
The native composition and instruction bounds are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Catalogue

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Computed maximum vertices per piece, preserved by descriptor enumeration. -/
abbrev pieceLength : Fin 32 := 28
/-- Computed number of pieces, preserved by descriptor enumeration. -/
abbrev pieces : Fin 32 := 29

/-- Existing parameter computation in the lower register bank. -/
@[expose]
def parameters : Code .standard 32 := Parameters.program.rename (Fin.castLE (by decide))

/-- Internal argument delivery from the fixed `D,g,n,p` header. -/
@[expose]
def deliverParameters : Code .standard 32 :=
  let header : Fin 32 := 0
  let one : Fin 32 := 31
  let n : Fin 32 := 6
  let D : Fin 32 := 7
  let g : Fin 32 := 8
  ram[ one ← #1; header ← #1; D ← *header; header ← header + one;
    g ← *header; header ← header + one; n ← *header ]

/-- Internal argument delivery and allocation after the computed query blocks. Copying the
count/query pointers precedes overwriting their old registers with the computed piece data. -/
@[expose]
def deliverChunks : Code .standard 32 :=
  let n : Fin 32 := 6
  let cap : Fin 32 := 10
  let len : Fin 32 := 11
  let num : Fin 32 := 12
  let oldCounts : Fin 32 := 28
  let oldQueries : Fin 32 := 29
  let counts := ChunkCatalogue.counts
  let queries := ChunkCatalogue.queries
  let size := ChunkCatalogue.size
  let capacity := ChunkCatalogue.capacity
  let modulus := ChunkCatalogue.modulus
  let dst := ChunkCatalogue.dst
  let header := ChunkCatalogue.addr
  ram[ counts ← oldCounts; queries ← oldQueries; size ← n; capacity ← cap;
    pieceLength ← len; pieces ← num; header ← #4; modulus ← *header;
    dst ← size * size; dst ← dst + dst; dst ← dst * modulus; dst ← dst + queries ]

/-- All class, parameter and chunk work is performed by actual native instructions. -/
@[expose]
def program : Code .standard 32 :=
  .seq (ResidueClasses.programAt 3) (.seq deliverParameters
    (.seq parameters (.seq deliverChunks ChunkCatalogue.program)))

/-- One finite instruction graph, independent of runtime sizes and physical width. -/
theorem program_fixed : program.size ≤ 320 ∧ ¬program.ReadsWidth := by decide

/-- A single explicit bound covering the fourth-power square-root input, all ceiling
temporaries and the worst-case descriptor reservation. Signed payloads have a separate bound. -/
@[expose]
def budget (n D g p : ℕ) : ℕ :=
  4 * ((n * n) * (n * n)) + 20 * p * (n * n) + 30 * (n * n) +
    8 * D + 8 * g + 8 * n + 8 * p + 64

/-- Every setup, parameter, signed residue, class scan and descriptor instruction is charged;
the final halt is added by the flat caller. -/
@[expose]
def cost (n D p : ℕ) : ℕ :=
  69 * (n * n) + p * (31 * (n * n) + 34) +
    5 * sOf D + 5 * queryCap n D + 85

private abbrev bank : Fin 15 → Fin 32 := Fin.castLE (by decide)

private theorem bank_injective : Function.Injective bank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 32 => k.val) h)

private theorem parameters_preserves : ∀ i : Fin 32, 15 ≤ i.val → parameters.Preserves i := by
  decide

private theorem chunks_preserves : ∀ i : Fin 32,
    28 ≤ i.val → ChunkCatalogue.program.Preserves i := by decide

/-- Exact computed parameters, residue/query arrays, concatenated descriptors and memory
frame. This is the readback established by the actual native catalogue execution. -/
@[expose]
def Output (n D g p : ℕ) (values : ℕ → ℤ) (initial y : Data 32) : Prop :=
    let N := n * n
    let R := fun q => (values q % (p : ℤ)).toNat
    let C := fun rho => Nat.count (fun q => R q = rho) N
    let out := 5 + 6 * N + p + 2 * N * p
    y.regs ChunkCatalogue.size = n ∧ y.regs ChunkCatalogue.modulus = p ∧
    y.regs ChunkCatalogue.counts = 5 + 6 * N ∧
    y.regs ChunkCatalogue.queries = 5 + 6 * N + p ∧
    y.regs ChunkCatalogue.dst = out ∧
    y.regs ChunkCatalogue.capacity = queryCap n D ∧
    y.regs pieceLength = pieceSize D g ∧ y.regs pieces = numPieces n D g ∧
    y.regs ChunkCatalogue.written = ChunkCatalogue.before C (queryCap n D) p ∧
    y.regs ChunkCatalogue.heap = out + 3 * y.regs ChunkCatalogue.written ∧
    (∀ q < 3 * N, y.mem (5 + 3 * N + q) = R q) ∧
    (∀ rho < p, y.mem (5 + 6 * N + rho) = C rho) ∧
    (∀ rho < p, ∀ q < N, R q = rho →
      y.mem (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q) = q / n ∧
      y.mem (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q + 1) = q % n) ∧
    (∀ rho < p, ∀ k < C rho ⌈/⌉ queryCap n D,
      y.mem (out + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k)) = rho ∧
      y.mem (out + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1) =
        5 + 6 * N + p + 2 * rho * N + 2 * (k * queryCap n D) ∧
      y.mem (out + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 2) =
        min (queryCap n D) (C rho - k * queryCap n D)) ∧
    (∀ a, a < 5 + 3 * N ∨ out + 3 * y.regs ChunkCatalogue.written ≤ a →
      y.mem a = initial.mem a)

/-- Prepare the actual catalogue at the fixed header, computing both splitting parameters and
every class/chunk. The result contains no supplied layout or execution certificates. The two
input-dependent fit premises cover ordinary signed values and the explicit numeric budget. -/
theorem exec_at {w : ℕ} (n D g p : ℕ) (values : ℕ → ℤ) (initial : Data 32)
    (hDHeader : initial.mem 1 = D) (hgHeader : initial.mem 2 = g)
    (hnHeader : initial.mem 3 = n) (hpHeader : initial.mem 4 = p)
    (hinput : ∀ q < 3 * (n * n), initial.mem (5 + q) = Signed.encode (values q))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < 3 * (n * n), GenericRAM.Signed.Fits w (values q))
    (hbudget : Fits (w + 2) (budget n D g p)) :
    ∃ y, ExecWithin (w + 2) program initial y (cost n D p) ∧
      Output n D g p values initial y := by
  let N := n * n
  let R (q : ℕ) := (values q % (p : ℤ)).toNat
  let C (rho : ℕ) := Nat.count (fun q => R q = rho) N
  let countBase := 5 + 6 * N
  let queryBase := countBase + p
  let out := queryBase + 2 * N * p
  change Fits (w + 2)
    (4 * (N * N) + 20 * p * N + 30 * N + 8 * D + 8 * g + 8 * n + 8 * p + 64) at hbudget
  obtain ⟨a, ha, har, hac, haq, hares, hacounts, hapairs, haframe⟩ :=
    ResidueClasses.exec_at (w := w) 3 n p values initial hnHeader hpHeader hinput hp hmod
      hvalues (hbudget.of_le (by dsimp [ResidueClasses.addressBoundAt, N]; nlinarith only []))
  change a.regs ResidueClasses.counts = countBase at hac
  change a.regs ResidueClasses.queries = queryBase at haq
  have ha1 : a.mem 1 = D := (haframe 1 (Or.inl (by omega))).trans hDHeader
  have ha2 : a.mem 2 = g := (haframe 2 (Or.inl (by omega))).trans hgHeader
  have ha3 : a.mem 3 = n := (haframe 3 (Or.inl (by omega))).trans hnHeader
  have ha4 : a.mem 4 = p := (haframe 4 (Or.inl (by omega))).trans hpHeader
  have h1 : Fits (w + 2) 1 := hbudget.of_le (by omega)
  have h2 : Fits (w + 2) (1 + 1) := hbudget.of_le (by omega)
  have h3 : Fits (w + 2) (1 + 1 + 1) := hbudget.of_le (by omega)
  have h4 : Fits (w + 2) 4 := hbudget.of_le (by omega)
  let b := a.set 31 1 |>.set 0 1 |>.set 7 D |>.set 0 2 |>.set 8 g |>.set 0 3 |>.set 6 n
  have hb : ExecWithin (w + 2) deliverParameters a b 7 := by
    ram_eval [deliverParameters, b, ha1, ha2, ha3, h1, h2, h3, Fin.mk.injEq]
  have hb6 : (b.comap bank).regs Parameters.size = n := by
    simp +decide [b, bank, Parameters.size]
  have hb7 : (b.comap bank).regs Parameters.dimension = D := by
    simp +decide [b, bank, Parameters.dimension]
  have hb8 : (b.comap bank).regs Parameters.divisor = g := by
    simp +decide [b, bank, Parameters.divisor]
  have hs : sOf D ≤ D := Nat.sqrt_le_self D
  have hpiece : pieceSize D g ≤ D := (pieceSize_le_sOf hg).trans hs
  obtain ⟨v, hv, hvs, hvq, hvB, hvH, hvn, -, -, hvm⟩ := Parameters.exec (b.comap bank)
    (by rw [hb7]; exact hbudget.of_le (by omega))
    (by rw [hb6]; exact hbudget.of_le (by dsimp [N]; omega))
    (by rw [hb7, hb8]; exact hbudget.of_le (by omega))
    (by rw [hb6, hb7, hb8]; exact hbudget.of_le (by omega))
  let c := v.extend bank b
  have hc : ExecWithin (w + 2) parameters b c (5 * sOf D + 5 * queryCap n D + 27) := by
    simpa only [parameters, c, hb6, hb7] using hv.rename bank_injective
  have hcLow (i : Fin 15) : c.regs (bank i) = v.regs i := by
    change Function.extend bank v.regs b.regs (bank i) = _
    exact bank_injective.extend_apply _ _ i
  have hc6 : c.regs 6 = n := by
    change c.regs (bank Parameters.size) = n
    rw [hcLow]
    exact hvn.trans hb6
  have hc10 : c.regs 10 = queryCap n D := by
    change c.regs (bank Parameters.capacity) = _
    rw [hcLow]
    simpa only [hb6, hb7] using hvq
  have hc11 : c.regs 11 = pieceSize D g := by
    change c.regs (bank Parameters.pieceLength) = _
    rw [hcLow]
    simpa only [hb7, hb8] using hvB
  have hc12 : c.regs 12 = numPieces n D g := by
    change c.regs (bank Parameters.pieces) = _
    rw [hcLow]
    simpa only [hb6, hb7, hb8] using hvH
  have hc28 : c.regs 28 = countBase := by
    have h := hc.regs_eq (parameters_preserves 28 (by decide))
    exact h.trans ((by simp +decide [b] : b.regs 28 = a.regs 28).trans hac)
  have hc29 : c.regs 29 = queryBase := by
    have h := hc.regs_eq (parameters_preserves 29 (by decide))
    exact h.trans ((by simp +decide [b] : b.regs 29 = a.regs 29).trans haq)
  have hcmem : c.mem = a.mem := hvm
  let d := c.set 14 countBase |>.set 15 queryBase |>.set 16 n |>.set 19 (queryCap n D)
    |>.set pieceLength (pieceSize D g) |>.set pieces (numPieces n D g)
    |>.set 25 4 |>.set 17 p |>.set 18 N |>.set 18 (N + N)
    |>.set 18 ((N + N) * p) |>.set 18 ((N + N) * p + queryBase)
  have hN : Fits (w + 2) (n * n) := hbudget.of_le (by dsimp [N]; omega)
  have h2N : Fits (w + 2) (n * n + n * n) := hbudget.of_le (by dsimp [N]; omega)
  have h2Np : Fits (w + 2) ((n * n + n * n) * p) :=
    hbudget.of_le (by dsimp [N]; nlinarith only [])
  have hOut : Fits (w + 2) ((n * n + n * n) * p + queryBase) :=
    hbudget.of_le (by dsimp [N, queryBase, countBase]; nlinarith only [])
  have hd : ExecWithin (w + 2) deliverChunks c d 12 := by
    have hc4 : c.mem 4 = p := (congrFun hcmem 4).trans ha4
    ram_eval [deliverChunks, d, hc28, hc29, hc6, hc10, hc11, hc12, hc4,
      h4, hN, h2N, h2Np, hOut, N, pieceLength, pieces, ChunkCatalogue.counts,
      ChunkCatalogue.queries, ChunkCatalogue.size, ChunkCatalogue.capacity,
      ChunkCatalogue.modulus, ChunkCatalogue.dst, ChunkCatalogue.addr, Fin.mk.injEq]
  have hd14 : d.regs ChunkCatalogue.counts = countBase := by
    simp +decide [d, ChunkCatalogue.counts, pieceLength, pieces]
  have hd15 : d.regs ChunkCatalogue.queries = queryBase := by
    simp +decide [d, ChunkCatalogue.queries, pieceLength, pieces]
  have hd16 : d.regs ChunkCatalogue.size = n := by
    simp +decide [d, ChunkCatalogue.size, pieceLength, pieces]
  have hd17 : d.regs ChunkCatalogue.modulus = p := by
    simp +decide [d, ChunkCatalogue.modulus, pieceLength, pieces]
  have hd18 : d.regs ChunkCatalogue.dst = out := by
    simp +decide [d, ChunkCatalogue.dst, out, pieceLength, pieces, two_mul, Nat.add_comm]
  have hd19 : d.regs ChunkCatalogue.capacity = queryCap n D := by
    simp +decide [d, ChunkCatalogue.capacity, pieceLength, pieces]
  have hdmem : d.mem = a.mem := hcmem
  have hC : ∀ rho < p, C rho ≤ N := fun rho _ => Nat.count_le _
  obtain ⟨y, hy, hycount, hyheap, hymeta, hycells, hyframe⟩ := ChunkCatalogue.exec d C
    (by
      rw [hd17]
      intro rho hrho
      rw [hd14, hdmem]
      exact hacounts rho hrho)
    (by rw [hd17, hd16]; exact hC)
    (by rw [hd19]; exact one_le_queryCap hD hDn)
    (by rw [hd14, hd17, hd18]; dsimp [out, queryBase]; omega)
    (by rw [hd15, hd17, hd16, hd18]; dsimp [out, N]; nlinarith only [])
    (hbudget.of_le (by
      rw [hd18, hd17, hd16, hd14, hd15]
      dsimp [out, queryBase, countBase, N]
      nlinarith only []))
  rw [hd17, hd16] at hy
  rw [hd19, hd17] at hycount
  rw [hd18] at hyheap
  rw [hd17, hd19, hd18, hd15, hd16] at hycells
  rw [hd18] at hyframe
  have hymeta' (i : Fin 32) (hi : 14 ≤ i.val) (hi' : i.val < 20) :
      y.regs i = d.regs i := hymeta i hi hi'
  have hlen : y.regs pieceLength = pieceSize D g := by
    rw [hy.regs_eq (chunks_preserves pieceLength (by decide))]
    simp +decide [d, pieceLength, pieces]
  have hpieces : y.regs pieces = numPieces n D g := by
    rw [hy.regs_eq (chunks_preserves pieces (by decide))]
    simp +decide [d, pieces]
  have hyold (a' : ℕ) (ha' : a' < out) : y.mem a' = a.mem a' :=
    (hyframe a' (by omega)).trans (congrFun hdmem a')
  refine ⟨y, ?_, (hymeta' _ (by decide) (by decide)).trans hd16,
    (hymeta' _ (by decide) (by decide)).trans hd17,
    (hymeta' _ (by decide) (by decide)).trans hd14,
    (hymeta' _ (by decide) (by decide)).trans hd15,
    (hymeta' _ (by decide) (by decide)).trans hd18,
    (hymeta' _ (by decide) (by decide)).trans hd19,
    hlen, hpieces, hycount, hyheap, ?_, ?_, ?_, hycells, ?_⟩
  · convert ha.seq (hb.seq (hc.seq (hd.seq hy))) using 1
    · rfl
    · dsimp [cost, N]
      ring
  · intro q hq
    rw [hyold _ (by dsimp [out, queryBase, countBase]; omega)]
    exact hares q hq
  · intro rho hrho
    rw [hyold _ (by dsimp [out, queryBase, countBase]; omega)]
    exact hacounts rho hrho
  · intro rho hrho q hq hRq
    have hcount : Nat.count (fun k => R k = rho) q ≤ q := Nat.count_le _
    have hbound := Nat.mul_le_mul_left (2 * N) (Nat.succ_le_of_lt hrho)
    rw [Nat.mul_succ] at hbound
    have h0 : 5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q < out := by dsimp [out, queryBase, countBase]; omega
    have h1 : 5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q + 1 < out := by
      dsimp [out, queryBase, countBase]
      omega
    rw [hyold _ h0, hyold _ h1]
    exact hapairs rho hrho q hq hRq
  · intro a' ha'
    change a' < 5 + 3 * N ∨ out + 3 * y.regs ChunkCatalogue.written ≤ a' at ha'
    have hframe : ¬(out ≤ a' ∧ a' < out + 3 * y.regs ChunkCatalogue.written) := by
      rcases ha' with h | h
      · have hlt : a' < out := by dsimp [out, queryBase, countBase]; omega
        omega
      · omega
    rw [hyframe a' hframe, hdmem]
    apply haframe a'
    rcases ha' with h | h
    · exact Or.inl h
    · apply Or.inr
      change out ≤ a'
      omega

end Cslib.Algorithms.WordRAM.ExactTriangle.Catalogue

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith

/-!
# Quantitative selected-parameter bounds for schedule search

These estimates separate linear bank and assignment-capacity storage from logarithmic metadata.
In particular, the chunk width used at each stack level is bounded by the binary block width,
not by the block width itself. This distinction prevents a spurious horizon-times-block term.
The final estimate assembles these bounds with one candidate and one suspended caller.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleSearch

open MultiTapeTM Cslib.TreeEval.Ary.Packed
open QueryReplay MultiTapeNTM.ChoiceTable

/-- A fixed-machine linear bound on the complete encoded block-value width. -/
@[expose] def widthConstant (k s : ℕ) : ℕ := 7 * k + (s + 1).size + 4

/-- Positive blocks absorb the fixed header overhead into a fixed multiplicative constant. -/
theorem width_le_mul (k s : ℕ) {b : ℕ} (hb : 0 < b) :
    Encoding.width k s b ≤ widthConstant k s * b := by
  have h := Encoding.width_le k s b
  have hheader := Nat.le_mul_of_pos_right ((s + 1).size + 3) hb
  dsimp only [widthConstant]
  nlinarith

/-- Measuring the encoded value width adds only a fixed number of bits to the block width. -/
theorem width_size_le (k s : ℕ) {b : ℕ} (hb : 0 < b) :
    (Encoding.width k s b).size ≤ (widthConstant k s).size + b.size :=
  (Nat.size_le_size (width_le_mul k s hb)).trans (Nat.size_mul_le _ _)

/-- The selected chunk width is logarithmic in the block width, uniformly in the horizon. -/
theorem selected_chunkWidth_le (k s : ℕ) {b : ℕ} (hb : 0 < b) :
    chunkWidth (k * 3 + 1) (Encoding.width k s b) ≤
      (k * 3 + 1).size + (widthConstant k s).size + b.size := by
  have h := Nat.size_mul_le (k * 3 + 1) (Encoding.width k s b)
  have hw := width_size_le k s hb
  change ((k * 3 + 1) * Encoding.width k s b).size ≤ _
  omega

/-- This is the logarithmic estimate needed inside the horizon-dependent stack term. -/
theorem horizon_chunkWidth_le (k s q : ℕ) {b : ℕ} (hb : 0 < b) :
    q * (chunkWidth (k * 3 + 1) (Encoding.width k s b) + 1) ≤
      ((k * 3 + 1).size + (widthConstant k s).size + 1) * q * (b.size + 1) := by
  have hm := selected_chunkWidth_le k s hb
  have hscalar : chunkWidth (k * 3 + 1) (Encoding.width k s b) + 1 ≤
      ((k * 3 + 1).size + (widthConstant k s).size + 1) * (b.size + 1) := by
    nlinarith
  have h := Nat.mul_le_mul_left q hscalar
  nlinarith

/-- The selected raw evaluator contributes linear bank storage and logarithmic storage per level.
The context and supplier allowances are retained with their existing constant coefficients. -/
theorem selected_queryStateBound_le (k s : ℕ) : ∃ C, ∀ contextBits supplierBits b q : ℕ,
    0 < b →
    RawController.Query.queryStateBound contextBits
      (fieldModulus (k * 3 + 1) (Encoding.width k s b)) (k * 3 + 1)
      (chunkCount (k * 3 + 1) (Encoding.width k s b)) q supplierBits ≤
      4 * contextBits + supplierBits + C * (b + q * (b.size + 1) + 1) := by
  let d := k * 3 + 1
  let A := widthConstant k s
  let L := d.size + A.size + 1
  refine ⟨200 * (d + 1) * (A + L + d.size + 1) + 4, ?_⟩
  intro contextBits supplierBits b q hb
  have hraw := RawController.Query.queryStateBound_packed_le contextBits supplierBits
    (d := d) (b := Encoding.width k s b) (H := q) (by dsimp only [d]; omega)
    (Encoding.width_pos k s b)
  have hwidth := width_le_mul k s hb
  have hstack := horizon_chunkWidth_le k s q hb
  have hinner : Encoding.width k s b +
      q * (chunkWidth d (Encoding.width k s b) + 1) + d.size + 1 ≤
      (A + L + d.size + 1) * (b + q * (b.size + 1) + 1) := by
    let R := b + q * (b.size + 1) + 1
    have hw : Encoding.width k s b ≤ A * R :=
      hwidth.trans (Nat.mul_le_mul_left A (by dsimp only [R]; omega))
    have hq : q * (chunkWidth d (Encoding.width k s b) + 1) ≤ L * R := by
      calc
        _ ≤ L * q * (b.size + 1) := hstack
        _ = L * (q * (b.size + 1)) := Nat.mul_assoc _ _ _
        _ ≤ L * R := Nat.mul_le_mul_left L (by dsimp only [R]; omega)
    have hc : d.size + 1 ≤ (d.size + 1) * R :=
      Nat.le_mul_of_pos_right _ (by dsimp only [R]; omega)
    calc
      _ ≤ A * R + L * R + (d.size + 1) * R := by omega
      _ = _ := by dsimp only [R]; ring
  have hmul := Nat.mul_le_mul_left (200 * (d + 1)) hinner
  nlinarith

/-- The selected assignment capacity is a power of two with its exact binary length charged. -/
theorem assignment_limit_size (d B : ℕ) :
    ((2 ^ chunkWidth d B) ^ (d * chunkCount d B)).size =
      d * (chunkCount d B * chunkWidth d B) + 1 := by
  rw [← pow_mul, Nat.size_pow]
  congr 1
  ring

/-- Capacity bits are linear in the value width; the number of assignments is never charged. -/
theorem assignment_limit_size_le {d B : ℕ} (hd : 0 < d) (hB : 0 < B) :
    ((2 ^ chunkWidth d B) ^ (d * chunkCount d B)).size ≤
      d * (B + chunkWidth d B) + 1 := by
  rw [assignment_limit_size]
  have h := Nat.mul_le_mul_left d (chunkCount_mul_lt hd hB).le
  omega

/-- A full interpolation point has linear field-cell storage at the selected parameters. -/
theorem selected_point_cost_le {d B : ℕ} (hd : 0 < d) (hB : 0 < B) :
    d * chunkCount d B * (2 * (fieldModulus d B).size + 1) ≤
      17 * d * (B + chunkWidth d B) := by
  have hp := chunkCount_mul_fieldModulus_size_le hd hB
  have hr := chunkCount_le hd hB
  have hscalar : chunkCount d B * (2 * (fieldModulus d B).size + 1) ≤
      17 * (B + chunkWidth d B) := by nlinarith
  have h := Nat.mul_le_mul_left d hscalar
  nlinarith

/-- Explicit output-count and alphabet/modulus storage also fit one linear bank allowance. -/
theorem selected_bank_cost_le {d B : ℕ} (hd : 0 < d) (hB : 0 < B) :
    chunkCount d B * ((fieldModulus d B).size +
      (2 ^ chunkWidth d B).size + 1) ≤ 12 * (B + chunkWidth d B) := by
  have halphabet := Nat.size_le_size (alphabetSize_lt hd hB).le
  have hp : 0 < (fieldModulus d B).size :=
    Nat.size_pos.mpr (fieldModulus_prime d B).pos
  have hregister := chunkCount_mul_fieldModulus_size_le hd hB
  have hscalar : (fieldModulus d B).size + (2 ^ chunkWidth d B).size + 1 ≤
      3 * (fieldModulus d B).size := by omega
  have h := Nat.mul_le_mul_left (chunkCount d B) hscalar
  nlinarith

/-- Native parameter initialization already supplies a uniform binary metadata-size estimate. -/
theorem prepared_metadata_le (k s : ℕ) : ∃ C, ∀ N b σ q : ℕ,
    (Initializer.encMetadata ((Initializer.prepare k s (N, b, σ, q)).1)).length ≤
      C * (N.size + b.size + σ.size + q.size + 1) := by
  obtain ⟨c, hc⟩ := MultiTapeTM.ComputableInSpace.length_le (Initializer.prepare_inSpace k s)
  refine ⟨4 * c, ?_⟩
  intro N b σ q
  have h := hc (N, b, σ, q)
  simp only [Initializer.encState, Initializer.encArgs, Initializer.prepare,
    length_encPair, length_encNat_eq_size] at h ⊢
  nlinarith

/-- Binary selected interpolation metadata retains the assignment capacity only once. -/
theorem selected_metadataSpace_le (N b σ q d B : ℕ) (hd : 0 < d) (hB : 0 < B) :
    ConcreteSupplier.metadataSpace N b σ q (chunkWidth d B) (2 ^ chunkWidth d B)
      ((2 ^ chunkWidth d B) ^ (d * chunkCount d B)) (fieldModulus d B) d
      (chunkCount d B) ≤
      100 * (d + 1) * (N.size + b.size + σ.size + q.size + B + chunkWidth d B + d.size + 1) := by
  have hr := chunkCount_le hd hB
  have hrsize := Nat.size_le_size hr
  have hBsize := length_encNat_le_self B
  have hmSize := length_encNat_le_self (chunkWidth d B)
  have hstride := Nat.size_mul_le (chunkCount d B) (chunkWidth d B)
  have hpoint := Nat.size_mul_le d (chunkCount d B)
  have hp := fieldModulus_size_le hd hB
  have hlimit := assignment_limit_size_le hd hB
  simp only [length_encNat_eq_size] at hBsize hmSize
  simp only [ConcreteSupplier.metadataSpace, QueryGate.encParams, Interpolation.encContext,
    encNat3, length_encPair, length_encNat_eq_size, Nat.size_pow]
  have hempty : (encList encNat []).length = 0 := rfl
  rw [hempty]
  nlinarith

private theorem context_le_metadataSpace (N b σ q m alphabet limit p d r : ℕ) :
    (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length ≤
      ConcreteSupplier.metadataSpace N b σ q m alphabet limit p d r := by
  simp only [ConcreteSupplier.encContext, ConcreteSupplier.metadataSpace, QueryGate.encParams,
    Interpolation.encContext, encNat3, length_encPair]
  omega

private theorem log2_le_size (N : ℕ) : Nat.log2 N ≤ N.size := by
  by_cases hz : N = 0
  · subst N; decide
  · exact ((Nat.log2_lt hz).mpr (Nat.lt_size_self N)).le

/-- One selected candidate has linear bank storage and logarithmic storage per tree level. -/
theorem initialized_allowance_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N b σ q : ℕ, 0 < b →
    InitializedEvaluator.allowance k s Q N b σ q ≤
      C * (b + q * (b.size + 1) + N.size + σ.size + 1) := by
  let d := k * 3 + 1
  let A := widthConstant k s
  let M := d.size + A
  let H := 100 * (d + 1) * (A + M + d.size + 2)
  let P := 17 * d * (A + M)
  let row := Fintype.card (Option (Fin k)) * (2 * Nat.card SignType + 1)
  let replay := 4 * M + 3 * A + 8 + 2 * row + 10 +
    1024 * (k + 1) * (Nat.card (Option Q) + Nat.card OutputTrack + 3)
  let reply := 48 * (H + 2 * P + 1) + 16 * A + 3 * P + replay + 14
  obtain ⟨ci, hci⟩ := prepared_metadata_le k s
  obtain ⟨cr, hcr⟩ := selected_queryStateBound_le k s
  let init := 16 * ci + 16 + 192 * (d + 1) * (2 * A + d.size)
  refine ⟨init + 4 * H + reply + cr + 2, ?_⟩
  intro N b σ q hb
  let B := Encoding.width k s b
  let m := chunkWidth d B
  let r := chunkCount d B
  let p := fieldModulus d B
  let alphabet := 2 ^ m
  let limit := alphabet ^ (d * r)
  let R := b + q * (b.size + 1) + N.size + σ.size + 1
  have hd : 0 < d := by dsimp only [d]; omega
  have hB : 0 < B := Encoding.width_pos k s b
  have hR : 0 < R := by dsimp only [R]; omega
  have hbs : b.size ≤ b := by simpa only [length_encNat_eq_size] using length_encNat_le_self b
  have hqs : q.size ≤ q := by simpa only [length_encNat_eq_size] using length_encNat_le_self q
  have hqmul : q ≤ q * (b.size + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hqR : q ≤ R := by dsimp only [R]; omega
  have hargs : N.size + b.size + σ.size + q.size + 1 ≤ R := by
    dsimp only [R]; omega
  have hbR : b ≤ R := by dsimp only [R]; omega
  have hNR : N.size ≤ R := by dsimp only [R]; omega
  have hqsizeR : q.size ≤ R := hqs.trans hqR
  have hBR : B ≤ A * R := (width_le_mul k s hb).trans (Nat.mul_le_mul_left A hbR)
  have hmR : m ≤ M * R := by
    have hm := chunkWidth_le d B
    have hc := Nat.le_mul_of_pos_right d.size hR
    dsimp only [M]
    nlinarith only [hm, hc, hBR]
  have hrB : r ≤ B := chunkCount_le hd hB
  have hrs : r.size ≤ B := by
    have h := length_encNat_le_self r
    rw [length_encNat_eq_size] at h
    omega
  have hms : m.size ≤ m := by simpa only [length_encNat_eq_size] using length_encNat_le_self m
  have hds : d.size ≤ d.size * R := Nat.le_mul_of_pos_right _ hR
  have hR0 : N.size + b.size + σ.size + q.size + B + m + d.size + 1 ≤
      (A + M + d.size + 2) * R := by nlinarith only [hargs, hBR, hmR, hds]
  have hmeta0 := selected_metadataSpace_le N b σ q d B hd hB
  have hmeta1 := Nat.mul_le_mul_left (100 * (d + 1)) hR0
  have hmeta : ConcreteSupplier.metadataSpace N b σ q m alphabet limit p d r ≤ H * R := by
    calc
      _ ≤ 100 * (d + 1) *
          (N.size + b.size + σ.size + q.size + B + m + d.size + 1) := hmeta0
      _ ≤ 100 * (d + 1) * ((A + M + d.size + 2) * R) := hmeta1
      _ = H * R := by dsimp only [H]; ring
  have hcontext : (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length ≤ H * R :=
    (context_le_metadataSpace _ _ _ _ _ _ _ _ _ _).trans hmeta
  have hpoint0 := selected_point_cost_le hd hB
  have hsum : B + m ≤ (A + M) * R := by nlinarith only [hBR, hmR]
  have hpoint1 := Nat.mul_le_mul_left (17 * d) hsum
  have hpoint : d * r * (2 * p.size + 1) ≤ P * R := by
    calc
      _ ≤ 17 * d * (B + m) := hpoint0
      _ ≤ 17 * d * ((A + M) * R) := hpoint1
      _ = P * R := by dsimp only [P]; ring
  have hcell : r * (2 * p.size + 1) ≤ P * R := by
    calc
      _ ≤ d * (r * (2 * p.size + 1)) := Nat.le_mul_of_pos_left _ hd
      _ = d * r * (2 * p.size + 1) := by ring
      _ ≤ P * R := hpoint
  have hlog := log2_le_size N
  have hsmall : b + Nat.log2 N + Nat.card (Option Q) + Nat.card OutputTrack + 1 ≤
      (Nat.card (Option Q) + Nat.card OutputTrack + 3) * R := by
    have hc := Nat.le_mul_of_pos_right
      (Nat.card (Option Q) + Nat.card OutputTrack + 1) hR
    have hbN : b + N.size ≤ R := by dsimp only [R]; omega
    nlinarith only [hc, hbN, hlog]
  have hreplay0 := Nat.mul_le_mul_left (1024 * (k + 1)) hsmall
  have hreplay : ConcreteSupplier.replaySpace k s Q N b q m r ≤ replay * R := by
    simp only [ConcreteSupplier.replaySpace, SupplierChunk.encContext, length_encPair,
      length_encNat_eq_size]
    change 2 * (2 * m.size + 1 + r.size) + 1 + (B + 1) +
      (2 * (4 * q.size + row + 2) + 2 +
        1024 * (k + 1) *
          (b + Nat.log2 N + Nat.card (Option Q) + Nat.card OutputTrack + 1)) ≤ replay * R
    dsimp only [replay]
    nlinarith only [hms, hrs, hmR, hBR, hqsizeR, hreplay0, hR]
  have hreply : ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r ≤ reply * R := by
    simp only [ConcreteSupplier.replySpace, ConcreteSupplier.gateSpace, length_encNat_eq_size]
    dsimp only [reply]
    nlinarith only [hmeta, hpoint, hcell, hreplay, hrs, hBR, hR]
  have hmetadata := hci N b σ q
  have hmetadataR : (Initializer.encMetadata
      ((Initializer.prepare k s (N, b, σ, q)).1)).length ≤ ci * R :=
    hmetadata.trans (Nat.mul_le_mul_left ci hargs)
  have hinit0 := Initializer.space_prepare_le k s N b σ q
  have hinit1 := Nat.mul_le_mul_left (192 * (d + 1))
    (show 2 * B + d.size ≤ (2 * A + d.size) * R by
      nlinarith only [hBR, hds])
  have hinit : Initializer.space k ((Initializer.prepare k s (N, b, σ, q)).1) ≤ init * R := by
    change Initializer.space k ((Initializer.prepare k s (N, b, σ, q)).1) ≤
      16 * ((Initializer.encMetadata ((Initializer.prepare k s (N, b, σ, q)).1)).length + 1) +
        192 * (d + 1) * (2 * B + d.size) at hinit0
    dsimp only [init]
    nlinarith only [hinit0, hinit1, hmetadataR, hR]
  have hraw := hcr (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length
    (ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r) b q hb
  change RawController.Query.queryStateBound
    (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length p d r q
    (ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r) ≤
      4 * (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length +
        ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r +
        cr * (b + q * (b.size + 1) + 1) at hraw
  have hraw1 := Nat.mul_le_mul_left cr
    (show b + q * (b.size + 1) + 1 ≤ R by dsimp only [R]; omega)
  change Initializer.space k ((Initializer.prepare k s (N, b, σ, q)).1) +
      RawController.Query.queryStateBound
        (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length p d r q
        (ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r) + 2 ≤ _
  change _ ≤ (init + 4 * H + reply + cr + 2) * R
  nlinarith only [hinit, hraw, hraw1, hcontext, hreply, hR]

/-- The complete sequential search has the fixed-machine square-root-simulation storage shape. -/
theorem space_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N b q : ℕ, 0 < b →
    space k s Q N b q ≤ C * (b + q * (b.size + 1) + N.size + 1) := by
  obtain ⟨c, hc⟩ := initialized_allowance_le k s Q
  refine ⟨c * (2 * (k + 1) + 2) + 64 * (k + 2) + 2, ?_⟩
  intro N b q hb
  let R := b + q * (b.size + 1) + N.size + 1
  have hbs : b.size ≤ b := by simpa only [length_encNat_eq_size] using length_encNat_le_self b
  have hqs : q.size ≤ q := by simpa only [length_encNat_eq_size] using length_encNat_le_self q
  have hq : q ≤ q * (b.size + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hcounter := counter_encoding_le k q (3 ^ ((k + 1) * q)) le_rfl
  rw [length_encNat_eq_size] at hcounter
  have hbound := hc N b (3 ^ ((k + 1) * q)) q hb
  have harg : b + q * (b.size + 1) + N.size + (3 ^ ((k + 1) * q)).size + 1 ≤
      (2 * (k + 1) + 2) * R := by dsimp only [R]; nlinarith
  have hmul := Nat.mul_le_mul_left c harg
  have hcaller : 2 * callerSpace k (N, b, q) + 2 ≤ (64 * (k + 2) + 2) * R := by
    simp only [callerSpace, encArgs, length_encPair, length_encNat_eq_size]
    dsimp only [R]
    nlinarith
  have hinit := hbound.trans hmul
  change 2 * callerSpace k (N, b, q) +
    InitializedEvaluator.allowance k s Q N b (3 ^ ((k + 1) * q)) q + 2 ≤ _
  calc
    _ ≤ (64 * (k + 2) + 2) * R + c * ((2 * (k + 1) + 2) * R) := by omega
    _ = _ := by dsimp only [R]; ring

end Turing.MultiTapePTM.BlockComputation.ScheduleSearch

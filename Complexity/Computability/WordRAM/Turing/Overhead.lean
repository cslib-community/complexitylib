/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Turing
public import Complexity.Computability.WordRAM.NativeDegree
public import Complexity.Computability.GenericRAM.Simulation.Degree
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Explicit overhead of the word-RAM simulation by Turing machines

`Program.ComputesInTime.turingComputableInPolyTime_of_width` simulates a word-RAM program by a
multi-tape Turing machine in polynomial time of unnamed degree. Here the degree is explicit. If
every primitive of the basis has degree `d` (`Model.NativePrimitives.HasDegree`), a run of at most
`T` instructions on `n` input words at word size `w` costs
`O((T + 1) · ((n + T + 1)(w + 1)) ^ max 3 d)` machine steps, on top of computing the word size,
the input words and the step budget. Only the constant factor is hidden. For `Basis.additive`,
whose primitives are quadratic (`Basis.additive.quadraticPrimitives`), the exponent is `3`. The
cube comes from scanning the association-list memory of the simulator
(`SparseMemory.scanTime_le_cube`), not from the word-RAM model.

The simulation is the same as in `Complexity.Computability.WordRAM.Turing`. The new ingredients are
the degree-tracking certificates of `Complexity.Computability.GenericRAM.Simulation.Degree`, a
cubic initialization certificate (`initMemory_degree`, a counted fold), and quadratic certificates
for the conventions of `Complexity.Computability.WordRAM.Invariance` with logarithmic word size:
the bit list of the input as words (`bitsToNats_degree`) and the word size `k (size n + 1)`
(`logWidthBound_degree`).

## Main results

* `Cslib.WordRAM.initMemory_degree`: building the initial memory is cubic.
* `Cslib.WordRAM.Program.ComputesInTime.computableInO_of_width`: the simulation at a supplied
  width schedule, with time `O(|x| + Tw + Te + Ts + (T + 1) · ((n + T + 1)(w + 1)) ^ max 3 d)`.
* `Cslib.WordRAM.Program.ComputesInTime.computableInO_of_width_additive`: the case of
  `Basis.additive`, with exponent `3`.
* `Cslib.WordRAM.bitsToNats_degree`, `Cslib.WordRAM.logWidthBound_degree`: quadratic input
  conversion and word size for the bit-list convention.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM Cslib.GenericRAM ComputableInDegree

/-! ## Encoded lengths -/

section Lengths

/-- A word list that fits `w`-bit words has encoded length at most `n (2 w + 1)`. -/
theorem length_encList_le_of_inputFits {w : ℕ} {l : List ℕ} (h : InputFits w l) :
    (encList encNat l).length ≤ l.length * (2 * w + 1) := by
  rw [length_encList]
  have hle : ∀ x ∈ l, 2 * (encNat x).length + 1 ≤ 2 * w + 1 := fun x hx => by
    have := length_encNat_le_of_lt_two_pow (h.2 x hx)
    omega
  calc (l.map fun x => 2 * (encNat x).length + 1).sum
      ≤ (l.map fun _ => 2 * w + 1).sum := List.sum_le_sum hle
    _ = l.length * (2 * w + 1) := by simp

/-- `stateBound` is linear in the number of stored cells and in the word size. -/
theorem stateBound_le (r L w E : ℕ) :
    stateBound r L w E ≤ (2 * (encNat L).length + 4 * r + 14) * ((E + 1) * (w + 1)) := by
  unfold stateBound
  have h1 : 1 ≤ (E + 1) * (w + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : w + 1 ≤ (E + 1) * (w + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : E + 1 ≤ (E + 1) * (w + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

end Lengths

/-! ## Initialization with an explicit degree -/

section Init

/-- One step of the counted fold that builds the stored cells of `State.init`. -/
def initStep (q : ℕ × List (ℕ × ℕ)) (x : ℕ) : ℕ × List (ℕ × ℕ) :=
  (q.1 + 1, q.2 ++ [(q.1 + 1, x)])

theorem foldl_initStep (l : List ℕ) (k : ℕ) (acc : List (ℕ × ℕ)) :
    l.foldl initStep (k, acc) =
      (k + l.length, acc ++ (l.zipIdx k).map fun e => (e.2 + 1, e.1)) := by
  induction l generalizing k acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, initStep, ih, List.zipIdx_cons]
    simp only [List.length_cons, List.map_cons, List.append_assoc, List.singleton_append,
      Prod.mk.injEq, and_true]
    omega

/-- The stored cells of `State.init` as the result of the counted fold. -/
theorem initEntries_eq_foldl (input : List ℕ) :
    initEntries input = (0, (input.foldl initStep (0, [])).1) ::
      (input.foldl initStep (0, [])).2 := by
  simp [initEntries, foldl_initStep]

private theorem length_encList_zipIdx_le (l : List ℕ) (k : ℕ) :
    (encList (encPair encNat encNat) ((l.zipIdx k).map fun e => (e.2 + 1, e.1))).length ≤
      2 * (encList encNat l).length + l.length * (4 * (k + l.length) + 3) := by
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
    have h1 := length_encNat_le_self (k + 1)
    have h2 := ih (k + 1)
    simp only [List.zipIdx_cons, List.map_cons, length_encList, List.sum_cons,
      List.length_cons, length_encPair] at h2 ⊢
    nlinarith

/-- The counted fold is cubic, with quadratic output. -/
theorem initFold_degree :
    ComputableInDegree (fun l : List ℕ => l.foldl initStep (0, [])) (encList encNat)
      (encPair encNat (encList (encPair encNat encNat))) 3 2 := by
  have hk : ComputableInDegree (fun p : (ℕ × List (ℕ × ℕ)) × ℕ => p.1.1 + 1)
      (encPair (encPair encNat (encList (encPair encNat encNat))) encNat) encNat 1 1 :=
    (natSucc.comp ((fst _ _).comp (fst _ _))).mono
  have hacc : ComputableInDegree (fun p : (ℕ × List (ℕ × ℕ)) × ℕ => p.1.2)
      (encPair (encPair encNat (encList (encPair encNat encNat))) encNat)
      (encList (encPair encNat encNat)) 1 1 :=
    ((snd _ _).comp (fst _ _)).mono
  have hnew : ComputableInDegree (fun p : (ℕ × List (ℕ × ℕ)) × ℕ => p.1.2 ++ [(p.1.1 + 1, p.2)])
      (encPair (encPair encNat (encList (encPair encNat encNat))) encNat)
      (encList (encPair encNat encNat)) 1 1 :=
    ((snoc (encPair encNat encNat)).comp (hacc.prod (hk.prod (snd _ _)))).mono
  have hstep : ComputableInDegree (fun p : (ℕ × List (ℕ × ℕ)) × ℕ => initStep p.1 p.2)
      (encPair (encPair encNat (encList (encPair encNat encNat))) encNat)
      (encPair encNat (encList (encPair encNat encNat))) 1 1 :=
    (hk.prod hnew).mono
  have h := foldl' (encA := encNat) (encL := encList encNat)
    (encB := encPair encNat (encList (encPair encNat encNat)))
    (list := fun l => l) (init := fun _ => ((0 : ℕ), ([] : List (ℕ × ℕ)))) (step := initStep)
    (of_eq fun _ => rfl) (const _) hstep
    (B := fun l => 8 * ((encList encNat l).length + 1) ^ 2) ⟨8, fun _ => le_rfl⟩
    (fun l i hi => by
      rw [foldl_initStep]
      have hlen := length_le_length_encList encNat l
      have htake := length_encList_take_le encNat l i
      have hti : (l.take i).length ≤ l.length := List.length_take_le' i l
      have hz := length_encList_zipIdx_le (l.take i) 0
      have hn := length_encNat_le_self (0 + (l.take i).length)
      simp only [List.nil_append, length_encPair] at hz ⊢
      nlinarith)
  exact h.mono

/-- **Building the initial memory is cubic** in the encoded input words, with quadratic output. -/
theorem initMemory_degree :
    ComputableInDegree initMemory (encList encNat) (SparseMemory.encoding encNat encNat) 3 2 := by
  have h : ComputableInDegree
      (fun l : List ℕ => (0, (l.foldl initStep (0, [])).1) :: (l.foldl initStep (0, [])).2)
      (encList encNat) (encList (encPair encNat encNat)) 3 2 :=
    ((cons (encPair encNat encNat)).comp ((((const 0).prod ((fst _ _).comp initFold_degree))).prod
      ((snd _ _).comp initFold_degree))).mono
  refine h.of_enc_eq fun l => ?_
  simp only [SparseMemory.encoding_apply, entries_initMemory, initEntries_eq_foldl]

/-- The certificate of `initMemory`, cubic in the encoded input words. -/
def initMemoryCertificate :
    NativeCertificate initMemory (encList encNat) (SparseMemory.encoding encNat encNat) :=
  ⟨fun l => ((encList encNat l).length + 1) ^ 3, fun l => ((encList encNat l).length + 1) ^ 3,
    initMemory_degree.inO⟩

end Init

/-! ## The simulation with an explicit degree -/

section Main

variable {B : Basis} {r : ℕ} {α : Type} {encIn : α ↪ List Bool}

/-- **Word-RAM time gives Turing-machine time with an explicit polynomial overhead.**

Let every primitive of the basis have degree `d` (`Model.NativePrimitives.HasDegree`), and let `p`
compute `f` (`Program.ComputesInTime`). Suppose a machine computes the word size `width a` in unary
in time `O(Tw a)`, the input words `encode (width a) a` in time `O(Te a)` and a step budget
`steps a ≥ time a (width a)` in binary in time `O(Ts a)`; the word size must be admitted and the
input words must fit it. Then `f` is computable with binary output in time
`O(|encIn a| + Tw a + Te a + Ts a + (steps a + 1) · R ^ max 3 d)`, where
`R = (n + steps a + 1) · (width a + 1)` and `n` is the number of input words. The degree is
explicit; only the constant factor is hidden. -/
theorem Program.ComputesInTime.computableInO_of_width
    {N : B.genericModel.NativePrimitives B.encoding} {d : ℕ} (hN : N.HasDegree d)
    {p : Program B r} {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {f : α → ℕ}
    (h : p.ComputesInTime encode time allowed f) {width steps Tw Sw Te Se Ts Ss : α → ℕ}
    (hwidth : Turing.MultiTapeTM.ComputableInO width encIn encUnary Tw Sw)
    (hallowed : ∀ a, allowed a (width a))
    (hfits : ∀ a, InputFits (width a) (encode (width a) a))
    (hencode : Turing.MultiTapeTM.ComputableInO (fun a => encode (width a) a) encIn
      (encList encNat) Te Se)
    (hsteps : Turing.MultiTapeTM.ComputableInO steps encIn encNat Ts Ss)
    (htime : ∀ a, time a (width a) ≤ steps a) :
    Turing.MultiTapeTM.ComputableInO f encIn encNat
      (fun a => (encIn a).length + Tw a + Te a + Ts a + (steps a + 1) *
        (((encode (width a) a).length + steps a + 1) * (width a + 1)) ^ max 3 d)
      (fun a => (encIn a).length + Sw a + Se a + Ss a +
        (((encode (width a) a).length + steps a + 1) * (width a + 1)) ^ max 3 d) := by
  have hD : 3 ≤ max 3 d := le_max_left _ _
  have hN' := hN.mono (le_max_right 3 d)
  have hExec (a : α) : ∃ m ≤ steps a, GenericRAM.Executes (width a) p.toGeneric
      (initState B r (encode (width a) a)).denote (f a) m := by
    obtain ⟨m, hm, hle⟩ := h a (width a) (hallowed a) (hfits a)
    refine ⟨m, hle.trans (htime a), ?_⟩
    rw [denote_initState]
    exact executes_toGeneric_iff.mpr hm
  -- Every simulated outcome is a word-bounded state with at most `n + 1 + steps` cells.
  have hOutLen (a : α) (j : ℕ) (hj : j ≤ steps a) :
      (FiniteState.resultEncoding B.encoding (FiniteState.run (width a) p.toGeneric j
        (initState B r (encode (width a) a)))).length ≤
        stateBound r (labelBound p.toGeneric) (width a)
          ((encode (width a) a).length + 1 + steps a) := by
    have hrun := (wordBounded_initState (B := B) (r := r) (hfits a)).length_resultEncoding_run_le
      (p := p.toGeneric) (by simp) j
    rw [length_entries_initState] at hrun
    refine hrun.trans ?_
    simp only [stateBound]
    have := Nat.mul_le_mul_right (6 * width a + 3)
      (show (encode (width a) a).length + 1 + j ≤ (encode (width a) a).length + 1 + steps a by
        omega)
    omega
  have ht := FiniteState.transport_inO_of_hasDegree B.encoding N hN' hD p.toGeneric
    (⟨Ts, Ss, hsteps⟩ : NativeCertificate steps encIn encNat)
    (⟨Tw, Sw, hwidth⟩ : NativeCertificate width encIn encUnary)
    (FiniteState.initConstCertificate (r := r) B.encoding (NativeCertificate.const 0)
      (NativeCertificate.const 0)
      (initMemoryCertificate.comp (⟨Te, Se, hencode⟩ :
        NativeCertificate (fun a => encode (width a) a) encIn (encList encNat))))
    hExec hOutLen
  -- The constants: the state-bound factor, and its `max 3 d`-th power.
  set KL := 2 * (encNat (labelBound p.toGeneric)).length + 4 * r + 14 with hKL
  set C := (2 * KL + 4) ^ max 3 d with hC
  refine ht.mono (r + 2 * KL + C + 40) (fun a => ?_) (fun a => ?_) <;>
  · -- Shared estimates, with `R = (n + steps + 1)(w + 1)` and `P = R ^ max 3 d`.
    obtain ⟨R, hR⟩ : ∃ R, R = ((encode (width a) a).length + steps a + 1) * (width a + 1) :=
      ⟨_, rfl⟩
    have hR1 : 1 ≤ R := hR ▸ Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hwR : width a + 1 ≤ R := hR ▸ Nat.le_mul_of_pos_left _ (by omega)
    have hTR : steps a + 1 ≤ R := hR ▸ (show steps a + 1 ≤ _ + steps a + 1 by omega).trans
      (Nat.le_mul_of_pos_right _ (by omega))
    have hRP : R ≤ R ^ max 3 d := Nat.le_self_pow (by omega) R
    have hBd : stateBound r (labelBound p.toGeneric) (width a)
        ((encode (width a) a).length + 1 + steps a) ≤ KL * (2 * R) := by
      refine (stateBound_le _ _ _ _).trans (Nat.mul_le_mul_left _ ?_)
      rw [hR]
      nlinarith
    have hXD : (2 * width a + stateBound r (labelBound p.toGeneric) (width a)
        ((encode (width a) a).length + 1 + steps a) + 2) ^ max 3 d ≤ C * R ^ max 3 d := by
      rw [hC, ← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith) _
    have hsq : ((encNat (steps a)).length + 1) ^ 2 ≤ R ^ max 3 d := by
      have h1 := length_encNat_le_self (steps a)
      calc ((encNat (steps a)).length + 1) ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ R ^ max 3 d := Nat.pow_le_pow_right hR1 (by omega)
    have hinit : ((encList encNat (encode (width a) a)).length + 1) ^ 3 ≤ 27 * R ^ max 3 d := by
      have h1 := length_encList_le_of_inputFits (hfits a)
      have h2 : (encList encNat (encode (width a) a)).length + 1 ≤ 3 * R := by
        have : (encode (width a) a).length * (2 * width a + 1) ≤ 2 * R := by rw [hR]; nlinarith
        omega
      calc ((encList encNat (encode (width a) a)).length + 1) ^ 3 ≤ (3 * R) ^ 3 :=
            Nat.pow_le_pow_left h2 3
        _ = 27 * R ^ 3 := by ring
        _ ≤ 27 * R ^ max 3 d := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_right hR1 hD)
    have hencS : (FiniteState.encoding B.encoding (initState B r (encode (width a) a))).length ≤
        stateBound r (labelBound p.toGeneric) (width a)
          ((encode (width a) a).length + 1 + steps a) := by
      have := hOutLen a 0 (Nat.zero_le _)
      simp only [FiniteState.run_zero, FiniteState.resultEncoding, encOption_some,
        encSum_inl, List.length_cons] at this
      omega
    have hQ := Nat.mul_le_mul_left (steps a + 1) (Nat.add_le_add hXD hsq)
    have hPQ : R ^ max 3 d ≤ (steps a + 1) * R ^ max 3 d := Nat.le_mul_of_pos_left _ (by omega)
    have hencT := length_encNat_le_self (steps a)
    have hKLP : KL * (2 * R) ≤ 2 * (KL * R ^ max 3 d) := by
      rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hRP)
    have hKLQ : KL * R ^ max 3 d ≤ KL * ((steps a + 1) * R ^ max 3 d) :=
      Nat.mul_le_mul_left _ hPQ
    have hCQ : (steps a + 1) * (C * R ^ max 3 d + R ^ max 3 d) =
        C * ((steps a + 1) * R ^ max 3 d) + (steps a + 1) * R ^ max 3 d := by ring
    obtain ⟨K, hK⟩ : ∃ K, K = r + 2 * KL + C + 40 := ⟨_, rfl⟩
    have hK1 := Nat.mul_le_mul_right (encIn a).length (show r + 3 ≤ K by omega)
    have hK2 := Nat.mul_le_mul_right ((steps a + 1) * R ^ max 3 d)
      (show 2 * KL + C + 34 ≤ K by omega)
    have hK3 := Nat.mul_le_mul_right (R ^ max 3 d) (show 2 * KL + C + 34 ≤ K by omega)
    have hKpos : 1 ≤ K := by omega
    have hKT (x : ℕ) : x ≤ K * x := Nat.le_mul_of_pos_left x hKpos
    have hTw := hKT (Tw a)
    have hTe := hKT (Te a)
    have hTs := hKT (Ts a)
    have hSw := hKT (Sw a)
    have hSe := hKT (Se a)
    have hSs := hKT (Ss a)
    simp only [initState, FiniteState.initConstCertificate, FiniteState.initCertificate_time,
      FiniteState.initCertificate_space, FiniteState.constRegsCertificate,
      NativeCertificate.const_time, NativeCertificate.const_space, NativeCertificate.comp_time,
      NativeCertificate.comp_space, initMemoryCertificate, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, FiniteState.runInputEncoding, FiniteState.inputEncoding,
      length_encPair, Basis.encoding, encUnary_apply, List.length_replicate, Function.comp_apply,
      ← hR, ← hK] at hencS ⊢
    linarith

/-- **The additive word RAM with an explicit cubic overhead.** A run of `Basis.additive` within
`steps a` instructions on `n` input words at word size `w` costs
`O(|encIn a| + Tw a + Te a + Ts a + (steps a + 1) · ((n + steps a + 1)(w + 1)) ^ 3)` Turing-machine
steps; see `Program.ComputesInTime.computableInO_of_width`. -/
theorem Program.ComputesInTime.computableInO_of_width_additive
    {p : Program .additive r} {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {f : α → ℕ}
    (h : p.ComputesInTime encode time allowed f) {width steps Tw Sw Te Se Ts Ss : α → ℕ}
    (hwidth : Turing.MultiTapeTM.ComputableInO width encIn encUnary Tw Sw)
    (hallowed : ∀ a, allowed a (width a))
    (hfits : ∀ a, InputFits (width a) (encode (width a) a))
    (hencode : Turing.MultiTapeTM.ComputableInO (fun a => encode (width a) a) encIn
      (encList encNat) Te Se)
    (hsteps : Turing.MultiTapeTM.ComputableInO steps encIn encNat Ts Ss)
    (htime : ∀ a, time a (width a) ≤ steps a) :
    Turing.MultiTapeTM.ComputableInO f encIn encNat
      (fun a => (encIn a).length + Tw a + Te a + Ts a + (steps a + 1) *
        (((encode (width a) a).length + steps a + 1) * (width a + 1)) ^ 3)
      (fun a => (encIn a).length + Sw a + Se a + Ss a +
        (((encode (width a) a).length + steps a + 1) * (width a + 1)) ^ 3) :=
  h.computableInO_of_width Basis.additive.quadraticPrimitives_hasDegree hwidth hallowed hfits
    hencode hsteps htime

end Main

/-! ## The bit-list convention with logarithmic word size -/

section Bits

private theorem foldl_snoc_map {β γ : Type} (g : β → γ) (l : List β) (acc : List γ) :
    l.foldl (fun acc b => acc ++ [g b]) acc = acc ++ l.map g := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih => simp [ih]

private theorem foldl_succ (l : List Bool) (m : ℕ) :
    l.foldl (fun n _ => n + 1) m = m + l.length := by
  induction l generalizing m with
  | nil => simp
  | cons b l ih => simp only [List.foldl_cons, ih, List.length_cons]; omega

/-- **The bits of a list as words, in quadratic time.** -/
theorem bitsToNats_degree :
    ComputableInDegree (fun l : List Bool => l.map Bool.toNat) encBits (encList encNat) 2 1 := by
  have hstep : ComputableInDegree (fun p : List ℕ × Bool => p.1 ++ [p.2.toNat])
      (encPair (encList encNat) encBool) (encList encNat) 1 1 :=
    ((snoc encNat).comp ((fst _ _).prod ((of_finite Bool.toNat).comp (snd _ _)))).mono
  have h := foldl' (encA := encBool) (encL := encBits) (encB := encList encNat)
    (list := fun l => l) (init := fun _ => ([] : List ℕ))
    (step := fun acc b => acc ++ [b.toNat]) (of_eq fun _ => rfl) (const _) hstep
    (B := fun l => 3 * (encBits l).length) (DegreeBounded.self.smul 3)
    (fun l i hi => by
      rw [foldl_snoc_map, List.nil_append, length_encList]
      have hle : ∀ x ∈ (l.take i).map Bool.toNat, 2 * (encNat x).length + 1 ≤ 3 := by
        intro x hx
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
        have := length_encNat_le_self b.toNat
        cases b <;> simp_all
      calc (((l.take i).map Bool.toNat).map fun x => 2 * (encNat x).length + 1).sum
          ≤ (((l.take i).map Bool.toNat).map fun _ => 3).sum := List.sum_le_sum hle
        _ ≤ 3 * (encBits l).length := by
          simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul,
            encBits_apply]
          have := List.length_take_le' i l
          omega)
  convert h.mono (d' := 2) (e' := 1) using 1
  funext l
  rw [foldl_snoc_map, List.nil_append]

/-- The length of a bit list in binary, in quadratic time. -/
theorem lengthBinary_degree :
    ComputableInDegree (fun l : List Bool => l.length) encBits encNat 2 1 := by
  have h := foldl' (encA := encBool) (encL := encBits) (encB := encNat)
    (list := fun l => l) (init := fun _ => (0 : ℕ)) (step := fun n _ => n + 1)
    (of_eq fun _ => rfl) (const _) ((natSucc.comp (fst encNat encBool)).mono (d' := 1) (e' := 1))
    (B := fun l => (encBits l).length) DegreeBounded.self
    (fun l i hi => by
      rw [foldl_succ, Nat.zero_add]
      have := length_encNat_le_self (l.take i).length
      have := List.length_take_le' i l
      simp only [encBits_apply]
      omega)
  convert h.mono (d' := 2) (e' := 1) using 1
  funext l
  rw [foldl_succ, Nat.zero_add]

/-- Multiplying a unary number by a constant is linear. -/
theorem unaryMulConst_degree (k : ℕ) :
    ComputableInDegree (fun m : ℕ => k * m) encUnary encUnary 1 1 := by
  induction k with
  | zero =>
    convert (const (encIn := encUnary) (encMid := encUnary) 0).mono (d' := 1) (e' := 1)
      using 1
    funext m
    simp
  | succ k ih =>
    convert unaryAdd ih (of_eq (f := fun m : ℕ => m) fun _ => rfl) (d := 1) (e := 1)
      (by omega) (by omega) using 1
    funext m
    rw [Nat.succ_mul]

/-- **The word size `k (size n + 1)` of an input of length `n`, in unary, in quadratic time.** It
is at least the logarithmic threshold `logWidth k n`. -/
theorem logWidthBound_degree (k : ℕ) :
    ComputableInDegree (fun l : List Bool => k * (Nat.size l.length + 1)) encBits encUnary 2 1 := by
  have hsize : ComputableInDegree (fun l : List Bool => (encNat l.length).length) encBits
      encUnary 2 1 :=
    (((ComputableInO.lengthUnary.comp_enc encNat).computableInDegree (d := 1) (e := 1)
      ⟨1, fun _ => by simp⟩ ⟨1, fun _ => by simp⟩ le_rfl).comp lengthBinary_degree).mono
  have h := ((unaryMulConst_degree k).comp (unary_succ.comp hsize)).mono (d' := 2) (e' := 1)
  convert h using 1
  funext l
  simp [encNat_apply, Nat.size_eq_bits_len]

/-- The logarithmic threshold is at most the word size `k (size n + 1)`. -/
theorem logWidth_le_mul_size_succ (k n : ℕ) : logWidth k n ≤ k * (Nat.size n + 1) := by
  refine Nat.mul_le_mul_left k (Nat.add_le_add_right ?_ 1)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.log_lt_of_lt_pow (by omega) (Nat.lt_size_self n)).le

/-- The bits of an input of length `n` fit words of `k (size n + 1)` bits when `k ≥ 1`. -/
theorem inputFits_map_toNat {k : ℕ} (hk : 1 ≤ k) (l : List Bool) :
    InputFits (k * (Nat.size l.length + 1)) (l.map Bool.toNat) := by
  have hw : Nat.size l.length + 1 ≤ k * (Nat.size l.length + 1) := Nat.le_mul_of_pos_left _ hk
  refine ⟨?_, fun v hv => ?_⟩
  · rw [fits_iff, List.length_map]
    exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hv
    rw [fits_iff]
    calc b.toNat < 2 ^ 1 := by cases b <;> simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

end Bits

end Cslib.WordRAM

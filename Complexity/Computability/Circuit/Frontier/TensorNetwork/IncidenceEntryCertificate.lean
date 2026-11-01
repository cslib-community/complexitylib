/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryPolyTime
public import Complexity.Computability.GenericRAM.Native.BooleanFold
public import Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# The native certificate of the entries of the incidence network

One native machine evaluates every entry of the incidence network of Lemma D.2 of
[OpenAI2026ETH] (`Cslib.Circuits.Frontier.IncidenceNetwork.incEntry`, p. 56)
(`IncidenceNetwork.incCertificate`). A row runs the streaming Boolean fold
`Cslib.GenericRAM.BooleanFold` over the `2 ^ |sel|` words on its selected incidences, one
polynomial-time term each (`IncidenceNetwork.rowSumCertificate`); everything else is
polynomial-time. So on a descriptor and bits of encoded length `m`, with `N` incidences in the
blocks of a row descriptor (`IncidenceNetwork.descInc`, none for other descriptors), the machine
takes time at most `c (m + 1) ^ c 2 ^ N` and space at most `c (m + 1) ^ c`
(`IncidenceNetwork.exists_incCertificate_le`). The source evaluates a test-group entry in
`2 ^ λ ^ O(1)` bit operations and polynomial space (p. 56), summing one test at a time over the
`2 ^ |S_i|` subsets; here one sum runs over the subsets of all selected incidences of the group,
so the exponent is bounded by the incidences of the group.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.rowSumCertificate`: the sum of a row.
* `Cslib.Circuits.Frontier.IncidenceNetwork.rowCertificate`: the entries of rows.
* `Cslib.Circuits.Frontier.IncidenceNetwork.incCertificate`: the entry procedure.
* `Cslib.Circuits.Frontier.IncidenceNetwork.descInc`: the incidences of a row descriptor.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_incCertificate_le`: time and space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.2 (p. 56).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Turing.MultiTapeTM Cslib.GenericRAM GaloisRingArith Cslib.BitString

/-! ### The sum of a row -/

/-- The number of selected incidences of a context, in unary. -/
theorem rowDim_polyTime :
    ComputableInPolyTime (fun ((_, _, _, sel) : RowCtx) => sel.length) encRowCtx encUnary :=
  ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
      (ComputableInPolyTime.snd _ _)))).of_enc_eq fun (_, _, _, _) => rfl

/-- The initial state of the sum of a row: the context and zero. -/
theorem rowInit_polyTime :
    ComputableInPolyTime
      (fun ((P, ℓ, tests, sel) : RowCtx) => ((P, ℓ, tests, sel), zero (truncFl ℓ))) encRowCtx
      encRowState := by
  have hℓ := (ComputableInPolyTime.fst encUnary (encPair (encList (encList (encList encNat)))
    (encList (encPair encNat encNat)))).comp (ComputableInPolyTime.snd encUnary
      (encPair encUnary (encPair (encList (encList (encList encNat)))
        (encList (encPair encNat encNat)))))
  have hfl := truncFl_polyTime.comp hℓ
  have hz := computableInPolyTime_tabulate (g := fun (_ : RowCtx) (_ : ℕ) => 0)
    ((ComputableInPolyTime.length_list encNat).comp hfl) (ComputableInPolyTime.const 0)
  exact (ComputableInPolyTime.id'.prod (hz.of_enc_eq fun _ => rfl)).of_enc_eq
    fun (_, _, _, _) => rfl

/-- The streaming fold of the sum of a row. -/
noncomputable def rowLoopCertificate :=
  BooleanFold.certificate (encIn := encRowCtx) (encB := encRowState)
    (dimension := fun ((_, _, _, sel) : RowCtx) => sel.length)
    (initial := fun ((P, ℓ, tests, sel) : RowCtx) => ((P, ℓ, tests, sel), zero (truncFl ℓ)))
    (body := rowBody)
    (NativeCertificate.ofPolyTime rowDim_polyTime) (NativeCertificate.ofPolyTime rowInit_polyTime)
    (NativeCertificate.ofPolyTime rowBody_polyTime)

/-- The streaming fold computes the sum of a row. -/
private theorem run_rowBody (P ℓ : ℕ) (tests : List (List (List ℕ))) (sel : List (ℕ × ℕ)) :
    (BooleanFold.run rowBody sel.length ((P, ℓ, tests, sel), zero (truncFl ℓ))).2.2.2 =
      rowSum (P, ℓ, tests, sel) := by
  rw [BooleanFold.run_accumulator]
  rfl

/-- **The native certificate of the sum of a row.** -/
noncomputable def rowSumCertificate : NativeCertificate rowSum encRowCtx (encList encNat) :=
  rowLoopCertificate.snd.snd.snd.congr fun (P, ℓ, tests, sel) => run_rowBody P ℓ tests sel

/-- A term keeps the context. -/
theorem fst_rowBody (n : ℕ) (w : List Bool) (ctx : RowCtx) (acc : List ℕ) :
    (rowBody ((n, w), ctx, acc)).1 = ctx := by
  obtain ⟨_, _, _, _⟩ := ctx
  rfl

/-- A term leaves a reduced accumulator: `ℓ` coefficients below `2 ^ P`. -/
theorem reduced_rowBody (n : ℕ) (w : List Bool) (P ℓ : ℕ) (tests : List (List (List ℕ)))
    (sel : List (ℕ × ℕ)) (acc : List ℕ) :
    (rowBody ((n, w), (P, ℓ, tests, sel), acc)).2.length = ℓ ∧
      ∀ x ∈ (rowBody ((n, w), (P, ℓ, tests, sel), acc)).2, x < 2 ^ P := by
  simp only [rowBody]
  split_ifs
  · exact ⟨by simp, fun x hx => lt_of_mem_add hx⟩
  · exact ⟨by simp [sub], fun x hx => lt_of_mem_add hx⟩

/-- Every prefix of the sum of a row keeps the context and a reduced accumulator. -/
theorem foldl_rowBody {α : Type*} (P ℓ : ℕ) (tests : List (List (List ℕ)))
    (sel : List (ℕ × ℕ)) (n : ℕ) (word : α → List Bool) (l : List α) (acc : List ℕ)
    (hlen : acc.length = ℓ) (hlt : ∀ x ∈ acc, x < 2 ^ P) :
    (l.foldl (fun st i => rowBody ((n, word i), st)) ((P, ℓ, tests, sel), acc)).1 =
        (P, ℓ, tests, sel) ∧
      (l.foldl (fun st i => rowBody ((n, word i), st)) ((P, ℓ, tests, sel), acc)).2.length = ℓ ∧
      ∀ x ∈ (l.foldl (fun st i => rowBody ((n, word i), st)) ((P, ℓ, tests, sel), acc)).2,
        x < 2 ^ P := by
  induction l generalizing acc with
  | nil => exact ⟨rfl, hlen, hlt⟩
  | cons i l ih =>
    rw [List.foldl_cons]
    have h := reduced_rowBody n (word i) P ℓ tests sel acc
    have hst : rowBody ((n, word i), ((P, ℓ, tests, sel), acc)) =
        ((P, ℓ, tests, sel), (rowBody ((n, word i), ((P, ℓ, tests, sel), acc))).2) :=
      Prod.ext (fst_rowBody _ _ _ _) rfl
    rw [hst]
    exact ih _ h.1 h.2

/-- The bound on the states of the sum of a row. -/
theorem length_encRowState_le (P ℓ : ℕ) (tests : List (List (List ℕ))) (sel : List (ℕ × ℕ))
    (acc : List ℕ) (hlen : acc.length = ℓ) (hlt : ∀ x ∈ acc, x < 2 ^ P) :
    (encRowState ((P, ℓ, tests, sel), acc)).length ≤
      2 * (encRowCtx (P, ℓ, tests, sel)).length + 1 +
        (encRowCtx (P, ℓ, tests, sel)).length *
          (2 * (encRowCtx (P, ℓ, tests, sel)).length + 1) := by
  have h1 := GaloisRingArith.length_encList_le hlen hlt
  have hP : P ≤ (encRowCtx (P, ℓ, tests, sel)).length := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hℓ : ℓ ≤ (encRowCtx (P, ℓ, tests, sel)).length := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  have h0 : (encRowState ((P, ℓ, tests, sel), acc)).length =
      2 * (encRowCtx (P, ℓ, tests, sel)).length + 1 + (encList encNat acc).length :=
    length_encPair _
  have := Nat.mul_le_mul hℓ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hP) 1)
  omega

/-- **The sum of a row in time `(2 ^ |sel| + 1)` times a polynomial and polynomial space.** -/
theorem rowSumCertificate_bounds :
    PolyBounded (fun ctx => (encRowCtx ctx).length) rowSumCertificate.space ∧
      ∃ T : RowCtx → ℕ, PolyBounded (fun ctx => (encRowCtx ctx).length) T ∧
        ∀ (P ℓ : ℕ) (tests : List (List (List ℕ))) (sel : List (ℕ × ℕ)),
          rowSumCertificate.time (P, ℓ, tests, sel) ≤
            (2 ^ sel.length + 1) * T (P, ℓ, tests, sel) := by
  have h := BooleanFold.certificate_bounds (encIn := encRowCtx) (encB := encRowState)
    (dimension := fun ((_, _, _, sel) : RowCtx) => sel.length)
    (initial := fun ((P, ℓ, tests, sel) : RowCtx) => ((P, ℓ, tests, sel), zero (truncFl ℓ)))
    (body := rowBody)
    (cn := NativeCertificate.ofPolyTime rowDim_polyTime)
    (ci := NativeCertificate.ofPolyTime rowInit_polyTime)
    (cb := NativeCertificate.ofPolyTime rowBody_polyTime)
    (NativeCertificate.ofPolyTime_isPolynomial _) (NativeCertificate.ofPolyTime_isPolynomial _)
    (NativeCertificate.ofPolyTime_isPolynomial _)
    (B := fun ctx => 2 * (encRowCtx ctx).length + 1 +
      (encRowCtx ctx).length * (2 * (encRowCtx ctx).length + 1))
    ((((PolyBounded.const 2).mul .self).add (.const 1)).add
      (PolyBounded.self.mul (((PolyBounded.const 2).mul .self).add (.const 1))))
    (fun (P, ℓ, tests, sel) j _ => by
      rw [BooleanFold.prefix_accumulator]
      have hz : (zero (truncFl ℓ)).length = ℓ := by simp
      have hz' : ∀ x ∈ zero (truncFl ℓ), x < 2 ^ P := fun x hx => by
        simp only [zero, List.mem_map] at hx
        obtain ⟨_, -, rfl⟩ := hx
        exact Nat.two_pow_pos _
      obtain ⟨h1, h2, h3⟩ := foldl_rowBody P ℓ tests sel sel.length (lowBits sel.length)
        (List.range j) _ hz hz'
      have heq : List.foldl (fun acc i => rowBody ((sel.length, lowBits sel.length i), acc))
          ((P, ℓ, tests, sel), zero (truncFl ℓ)) (List.range j) =
          ((P, ℓ, tests, sel), (List.foldl (fun acc i => rowBody ((sel.length,
            lowBits sel.length i), acc)) ((P, ℓ, tests, sel), zero (truncFl ℓ))
              (List.range j)).2) :=
        Prod.ext h1 rfl
      rw [heq]
      exact length_encRowState_le P ℓ tests sel _ h2 h3)
  exact ⟨h.1, h.2.imp fun _ hT => ⟨hT.1, fun P ℓ tests sel => hT.2 (P, ℓ, tests, sel)⟩⟩

/-! ### Rows -/

/-- **The native certificate of the entries of rows.** -/
noncomputable def rowCertificate :
    NativeCertificate (fun q : RowDesc × List Bool => rowEntry q.1 q.2)
      (encPair encRowDesc encBits) (encList encNat) :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime rowValid_polyTime)
    (rowSumCertificate.comp (NativeCertificate.ofPolyTime rowContext_polyTime))
    (NativeCertificate.const [])).congr fun ((_, _, _, _), _) => rfl

/-- The incidences of the blocks of a row descriptor. -/
@[expose] def rowInc : RowDesc → ℕ
  | (_, _, _, blocks) => (blocks.map fun b => b.1.length).sum

/-- **The entries of rows in time `2 ^ N` times a polynomial and polynomial space**, for `N` the
incidences of the blocks. -/
theorem rowCertificate_bounds :
    PolyBounded (fun q => (encPair encRowDesc encBits q).length) rowCertificate.space ∧
      ∃ T : RowDesc × List Bool → ℕ,
        PolyBounded (fun q => (encPair encRowDesc encBits q).length) T ∧
        ∀ q, rowCertificate.time q ≤ 2 ^ rowInc q.1 * T q := by
  obtain ⟨hS, Tl, hTl, hle⟩ := rowSumCertificate_bounds
  have hv := NativeCertificate.ofPolyTime_isPolynomial rowValid_polyTime
  have hc := NativeCertificate.ofPolyTime_isPolynomial rowContext_polyTime
  have hlen := rowContext_polyTime.polyBounded_length
  refine ⟨(((hv.2.add hc.2).add (hS.comp hlen)).add .self).mono fun q => ?_,
    fun q => (NativeCertificate.ofPolyTime rowValid_polyTime).time q +
      (NativeCertificate.ofPolyTime rowContext_polyTime).time q +
      (encPair encRowDesc encBits q).length + 2 * Tl (rowContext q.1 q.2),
    (((hv.1.add hc.1).add .self).add ((PolyBounded.const 2).mul (hTl.comp hlen))),
    fun q => ?_⟩
  · have hsp : rowCertificate.space q = (NativeCertificate.ofPolyTime rowValid_polyTime).space q +
        if validIndices q.1.2.2.2 (blockIndices q.1.2.2.2 q.2) then
          (NativeCertificate.ofPolyTime rowContext_polyTime).space q +
            rowSumCertificate.space (rowContext q.1 q.2)
        else (encPair encRowDesc encBits q).length := rfl
    rw [hsp]
    split_ifs <;> omega
  · obtain ⟨⟨P, ℓ, tests, blocks⟩, bs⟩ := q
    have htm : rowCertificate.time ((P, ℓ, tests, blocks), bs) =
        (NativeCertificate.ofPolyTime rowValid_polyTime).time ((P, ℓ, tests, blocks), bs) +
        if validIndices blocks (blockIndices blocks bs) then
          (NativeCertificate.ofPolyTime rowContext_polyTime).time ((P, ℓ, tests, blocks), bs) +
            rowSumCertificate.time (P, ℓ, tests, selected blocks (blockIndices blocks bs))
        else (encPair encRowDesc encBits ((P, ℓ, tests, blocks), bs)).length := rfl
    rw [htm]
    dsimp only [rowContext]
    have hdim : (selected blocks (blockIndices blocks bs)).length ≤ rowInc (P, ℓ, tests, blocks) :=
      length_selected_le _ _
    have h2 : 2 ^ (selected blocks (blockIndices blocks bs)).length ≤
        2 ^ rowInc (P, ℓ, tests, blocks) :=
      Nat.pow_le_pow_right (by norm_num) hdim
    have h1 : 1 ≤ 2 ^ rowInc (P, ℓ, tests, blocks) := Nat.one_le_two_pow
    have hl := hle P ℓ tests (selected blocks (blockIndices blocks bs))
    have h3 := Nat.mul_le_mul_right (Tl (P, ℓ, tests, selected blocks (blockIndices blocks bs)))
      (Nat.add_le_add h2 h1)
    split_ifs
    · nlinarith
    · nlinarith

/-! ### All descriptors -/

/-- The entries of columns and tables, from a descriptor that is not a row. -/
@[expose] def restEntry (q : Desc × List Bool) : List ℕ :=
  (((q.1.getRight?).getD (.inr [])).getLeft?).elim
    (tableEntry ((((q.1.getRight?).getD (.inr [])).getRight?).getD []) q.2)
    (fun col => colEntry col q.2)

/-- The entries of columns and tables are polynomial-time. -/
theorem restEntry_polyTime :
    ComputableInPolyTime restEntry (encPair encDesc encBits) (encList encNat) := by
  have hright := (ComputableInO.getRight?_deg encRowDesc (encSum encColDesc (encList encNat))
    ).computableInPolyTime.comp (ComputableInPolyTime.fst encDesc encBits)
  have hr := ComputableInPolyTime.optionGetDWithInput hright (ComputableInPolyTime.const (.inr []))
  have hleft :=
    (ComputableInO.getLeft?_deg encColDesc (encList encNat)).computableInPolyTime.comp hr
  have htab :=
    (ComputableInO.getRight?_deg encColDesc (encList encNat)).computableInPolyTime.comp hr
  have htab' := ComputableInPolyTime.optionGetDWithInput htab (ComputableInPolyTime.const [])
  have hfallback := tableEntry_polyTime.comp (htab'.prod (ComputableInPolyTime.snd encDesc encBits))
  have hbody := colEntry_polyTime.comp ((ComputableInPolyTime.snd _ _).prod
    ((ComputableInPolyTime.snd encDesc encBits).comp (ComputableInPolyTime.fst _ _)))
  exact (ComputableInPolyTime.optionElimWithInput hleft hfallback hbody).of_enc_eq fun _ => rfl

/-- The row descriptor of a descriptor, the default for others, with the bits. -/
theorem leftInput_polyTime :
    ComputableInPolyTime (fun q : Desc × List Bool => ((q.1.getLeft?).getD default, q.2))
      (encPair encDesc encBits) (encPair encRowDesc encBits) := by
  have hleft := (ComputableInO.getLeft?_deg encRowDesc (encSum encColDesc (encList encNat))
    ).computableInPolyTime.comp (ComputableInPolyTime.fst encDesc encBits)
  exact (ComputableInPolyTime.optionGetDWithInput hleft (ComputableInPolyTime.const default)).prod
    (ComputableInPolyTime.snd encDesc encBits)

/-- Whether a descriptor is a row. -/
theorem isRow_polyTime :
    ComputableInPolyTime (fun q : Desc × List Bool => (q.1.getLeft?).isSome)
      (encPair encDesc encBits) encBool :=
  ((ComputableInO.getLeft?_deg encRowDesc (encSum encColDesc (encList encNat))
    ).computableInPolyTime.comp (ComputableInPolyTime.fst encDesc encBits)).optionIsSome

/-- **The native certificate of the entry procedure of the incidence network.** -/
noncomputable def incCertificate :
    NativeCertificate (fun q : Desc × List Bool => incEntry q.1 q.2) (encPair encDesc encBits)
      (encList encNat) :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime isRow_polyTime)
    (rowCertificate.comp (NativeCertificate.ofPolyTime leftInput_polyTime))
    (NativeCertificate.ofPolyTime restEntry_polyTime)).congr fun q => by
      rcases q with ⟨row | col | t, bs⟩ <;> rfl

/-- **The incidences of a descriptor**: those of the blocks of a row, and none otherwise. -/
@[expose] def descInc : Desc → ℕ
  | .inl row => rowInc row
  | .inr _ => 0

/-- **Time and space of the entry procedure.** On a descriptor and bits of encoded length `m`, the
certificate takes time at most `c (m + 1) ^ c 2 ^ N`, for `N` the incidences of the descriptor,
and space at most `c (m + 1) ^ c`. -/
theorem exists_incCertificate_le : ∃ c : ℕ, ∀ q : Desc × List Bool,
    incCertificate.time q ≤ c * ((encPair encDesc encBits q).length + 1) ^ c * 2 ^ descInc q.1 ∧
      incCertificate.space q ≤ c * ((encPair encDesc encBits q).length + 1) ^ c := by
  obtain ⟨hS, T, hT, hle⟩ := rowCertificate_bounds
  have hi := NativeCertificate.ofPolyTime_isPolynomial isRow_polyTime
  have hl := NativeCertificate.ofPolyTime_isPolynomial leftInput_polyTime
  have hr := NativeCertificate.ofPolyTime_isPolynomial restEntry_polyTime
  have hlen := leftInput_polyTime.polyBounded_length
  obtain ⟨c₁, d₁, h₁⟩ := ((((hi.1.add hl.1).add hr.1).add (hT.comp hlen))).exists_le
  obtain ⟨c₂, d₂, h₂⟩ := ((((hi.2.add hl.2).add hr.2).add (hS.comp hlen))).exists_le
  refine ⟨c₁ + c₂ + d₁ + d₂ + 1, fun q => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, (encPair encDesc encBits q).length = m := ⟨_, rfl⟩
  have hpow (c d : ℕ) (hc : c ≤ c₁ + c₂ + d₁ + d₂ + 1) (hd : d ≤ c₁ + c₂ + d₁ + d₂ + 1) :
      c * (m + 1) ^ d ≤ (c₁ + c₂ + d₁ + d₂ + 1) * (m + 1) ^ (c₁ + c₂ + d₁ + d₂ + 1) :=
    Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd)
  have h1 := h₁ q
  have h2 := h₂ q
  rw [hm] at h1 h2
  rw [hm]
  have hp1 := hpow c₁ d₁ (by omega) (by omega)
  have hp2 := hpow c₂ d₂ (by omega) (by omega)
  have htm : incCertificate.time q = (NativeCertificate.ofPolyTime isRow_polyTime).time q +
      if (q.1.getLeft?).isSome then
        (NativeCertificate.ofPolyTime leftInput_polyTime).time q +
          rowCertificate.time ((q.1.getLeft?).getD default, q.2)
      else (NativeCertificate.ofPolyTime restEntry_polyTime).time q := rfl
  have hsp : incCertificate.space q = (NativeCertificate.ofPolyTime isRow_polyTime).space q +
      if (q.1.getLeft?).isSome then
        (NativeCertificate.ofPolyTime leftInput_polyTime).space q +
          rowCertificate.space ((q.1.getLeft?).getD default, q.2)
      else (NativeCertificate.ofPolyTime restEntry_polyTime).space q := rfl
  rw [htm, hsp]
  rcases q with ⟨row | rest, bs⟩
  · have hrow := hle (row, bs)
    have hd : descInc (Sum.inl row) = rowInc row := rfl
    simp only [Sum.getLeft?_inl, Option.isSome_some, Option.getD_some, ↓reduceIte, hd] at h1 h2 ⊢
    have h2p : 1 ≤ 2 ^ rowInc row := Nat.one_le_two_pow
    constructor
    · calc _ ≤ 2 ^ rowInc row * ((NativeCertificate.ofPolyTime isRow_polyTime).time (.inl row, bs) +
            (NativeCertificate.ofPolyTime leftInput_polyTime).time (.inl row, bs) +
            (NativeCertificate.ofPolyTime restEntry_polyTime).time (.inl row, bs) +
            T (row, bs)) := by nlinarith
        _ ≤ 2 ^ rowInc row * (c₁ * (m + 1) ^ d₁) := Nat.mul_le_mul_left _ h1
        _ ≤ _ := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hp1
    · omega
  · have hd : descInc (Sum.inr rest) = 0 := rfl
    simp only [Sum.getLeft?_inr, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hd,
      pow_zero, mul_one] at h1 h2 ⊢
    exact ⟨by omega, by omega⟩

end Cslib.Circuits.Frontier.IncidenceNetwork

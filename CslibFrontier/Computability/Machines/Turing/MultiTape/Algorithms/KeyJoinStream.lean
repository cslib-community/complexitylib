/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFlatMapBounds
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Output-sensitive bit execution of grouped occurrence joins

Retained classes use real nested record streaming rather than a polynomial-time
callback in a whole bucket. Each replay of the opposite run is charged to its
emitted Cartesian pairs. Input and retained output are charged alongside all
callback and framing temporaries. This is a class producer component; it does
not supply the missing persistent retained-tape opposite probe or global solver
resource theorem of [WangLvShenZhang2027], Lemma 8/Theorem 7 (PDF pp. 21–22).

## Main definitions

* `volume`, `width`: actual class input/output volume and physical maximum row width.

## Main results

* `join_record_wire`: binary output-pair width from actual tagged quarter records.
* `pairs_computable`: filtered bucket emission with output-sensitive bit resources.
* `volume_eq`: the resource volume is quarter input plus class output and group control.
* `join_computable`: uniform grouped emission, including simultaneous materialized output.
-/

public section
namespace Turing.MultiTapeTM.KeyJoinStream

private abbrev er := RadixPartition.recordEncoding
private abbrev el := encList er

private def emit (q : SortedMatch.Record × SortedMatch.Record) : List (ℕ × ℕ) :=
  [(q.1.2 / 2, q.2.2 / 2)]

private theorem emit_polyTime : ComputableInPolyTime emit (encPair er er) el := by
  have pair : ComputableTidilyInPolyTime (fun q : SortedMatch.Record × SortedMatch.Record =>
      (q.1.2 / 2, q.2.2 / 2)) (encPair er er) er := by
    dsimp only [er]
    apply ComputableTidilyInPolyTime.prod <;>
      (apply ComputableTidilyInPolyTime.binary_div' <;> fun_prop)
  have single : ComputableTidilyInPolyTime (fun r : ℕ × ℕ => [r]) er el :=
    .of_linear (.of_frame (fun _ => by simp))
  exact .of_tidy (single.comp pair)

/-- Generated quarter pairs have binary wire bounded by the actual tagged input records.
Both packed coordinates are divided by two when the direction tags are removed. -/
theorem join_record_wire (groups : List (List (ℕ × ℕ))) (B : ℕ)
    (rows : ∀ r ∈ groups.flatten, (RadixPartition.recordEncoding r).length ≤ B) :
    ∀ pair ∈ KeyJoin.join groups, (RadixPartition.recordEncoding pair).length ≤ 3*B+1 := by
  intro pair hp
  simp only [KeyJoin.join, KeyJoin.pairs, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨group, hg, a, ha, b, hb, rfl⟩ := hp
  have aw := rows a (List.mem_flatten.mpr ⟨group, hg, (List.mem_filter.mp ha).1⟩)
  have bw := rows b (List.mem_flatten.mpr ⟨group, hg, (List.mem_filter.mp hb).1⟩)
  have aSize : (encNat (a.2/2)).length ≤ (encNat a.2).length := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
      Nat.size_le_size (Nat.div_le_self a.2 2)
  have bSize : (encNat (b.2/2)).length ≤ (encNat b.2).length := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
      Nat.size_le_size (Nat.div_le_self b.2 2)
  simp only [RadixPartition.recordEncoding, length_encPair] at aw bw ⊢
  omega

/-- Nested occurrence enumeration, holding the right run while streaming the left run. -/
private def cross (input : List SortedMatch.Record × List SortedMatch.Record) : List (ℕ × ℕ) :=
  let (right, left) := input
  left.flatMap (fun a => right.map (fun b => (a.2 / 2, b.2 / 2)))

/-- The maximum physical row widths, with one unit for empty lists. -/
private def crossWidth (input : List SortedMatch.Record × List SortedMatch.Record) : ℕ :=
  let (right, left) := input
  streamRecordLength er right + streamRecordLength er left + 1

private theorem list_wire (rows : List SortedMatch.Record) :
    (el rows).length ≤ rows.length * (2 * streamRecordLength er rows + 1) :=
  length_encList_le er rows (fun _ hr => le_listMax (f := fun row => (er row).length) hr)

/-- Real Cartesian emission costs a polynomial only in physical row width, times input and
output occurrence volumes. The charged prefix space includes the materialized output. -/
private theorem cross_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO cross (encPair (encList RadixPartition.recordEncoding)
      (encList RadixPartition.recordEncoding)) (encList RadixPartition.recordEncoding)
      (fun (right, left) =>
        (left.length + 1) * (right.length + 1) * P (crossWidth (right, left)))
      (fun (right, left) =>
        (left.length + 1) * (right.length + 1) * P (crossWidth (right, left))) := by
  obtain ⟨P, hp, hm, hi⟩ := ComputableInO.flatMap_stream emit_polyTime
  have swap := (ComputableInO.snd el er).prod (ComputableInO.fst el er)
  let W : List SortedMatch.Record × SortedMatch.Record → ℕ := fun q =>
    2 * (encPair el er q).length + (encPair er el (q.2, q.1)).length +
      (q.1.length + 1) * P (streamFilterWidth er er (q.2, q.1))
  have hc : ComputableInO (fun q : List SortedMatch.Record × SortedMatch.Record =>
      q.1.map (fun b => (q.2.2 / 2, b.2 / 2))) (encPair el er) el W W := by
    have h := (hi.comp swap).of_enc_eq
      (g := fun q : List SortedMatch.Record × SortedMatch.Record =>
        q.1.map (fun b => (q.2.2 / 2, b.2 / 2))) (encC := el)
      (fun q => by dsimp only [Function.comp_def]; rw [List.map_eq_flatMap]; rfl)
    convert h using 1 <;> (funext q; simp only [W, two_mul, Nat.add_assoc])
  obtain ⟨cO, outputBound⟩ := hc.length_le
  have hs := hc.flatMap_stream_sum
  let Q := fun B => P B + 100 * B + 100
  have hq : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have mq : Monotone Q := by intro a b hab; have := hm hab; dsimp only [Q]; omega
  have rowWork (input : List SortedMatch.Record × List SortedMatch.Record)
      (a : SortedMatch.Record) (ha : a ∈ input.2) :
      W (input.1, a) + (encPair el er (input.1, a)).length + 1 ≤
        (input.1.length + 1) * Q (crossWidth input) := by
    have hr := list_wire input.1
    have ha' := le_listMax (f := fun r => (er r).length) ha
    change (er a).length ≤ streamRecordLength er input.2 at ha'
    have hb : streamFilterWidth er er (a, input.1) ≤ crossWidth input := by
      dsimp only [streamFilterWidth, crossWidth]
      omega
    have hP := hm hb
    have hmul := Nat.mul_le_mul_left (input.1.length + 1) hP
    dsimp only [W, Q, crossWidth]
    dsimp only [crossWidth] at hmul
    simp only [length_encPair]
    nlinarith
  have inputWork (input : List SortedMatch.Record × List SortedMatch.Record) :
      (encPair el el input).length ≤
        2 * ((input.2.length + 1) * (input.1.length + 1) * Q (crossWidth input)) := by
    have hr := list_wire input.1
    have hl := list_wire input.2
    have hQ : 2 * crossWidth input + 2 ≤ Q (crossWidth input) := by dsimp only [Q]; omega
    have hb₁ : 2 * streamRecordLength er input.1 + 1 ≤ 2 * crossWidth input + 2 := by
      dsimp only [crossWidth]; omega
    have hb₂ : 2 * streamRecordLength er input.2 + 1 ≤ 2 * crossWidth input + 2 := by
      dsimp only [crossWidth]; omega
    have h₁ := hr.trans (Nat.mul_le_mul_left input.1.length (hb₁.trans hQ))
    have h₂ := hl.trans (Nat.mul_le_mul_left input.2.length (hb₂.trans hQ))
    simp only [length_encPair]
    nlinarith [Nat.zero_le (input.1.length * input.2.length * Q (crossWidth input))]
  refine ⟨Q, hq, mq, hs.mono (2*cO+10) ?_ ?_⟩
  · rintro ⟨right, left⟩
    let input := (right, left)
    have hi := inputWork input
    have hw := List.sum_le_sum (fun a ha => rowWork input a ha)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hw
    change (encPair el el input).length +
      (input.2.map (fun a => W (input.1, a) + (encPair el er (input.1, a)).length+1)).sum ≤
        (2*cO+10)*((input.2.length+1)*(input.1.length+1)*Q (crossWidth input)+1)
    change (input.2.map (fun a => W (input.1, a) +
      (encPair el er (input.1, a)).length + 1)).sum ≤ _ at hw
    nlinarith [Nat.zero_le (cO * ((input.2.length+1)*(input.1.length+1)*Q (crossWidth input)+1))]
  · rintro ⟨right, left⟩
    let input := (right, left)
    let H := (input.2.length+1)*(input.1.length+1)*Q (crossWidth input)
    have hi : (encPair el el input).length ≤ 2*H := inputWork input
    have hw : ∀ a ∈ input.2, W (input.1, a) ≤ H := by
      intro a ha
      have hh := rowWork input a ha
      have hm := Nat.mul_le_mul_right ((input.1.length+1)*Q (crossWidth input))
        (by omega : 1 ≤ input.2.length+1)
      dsimp only [H]
      nlinarith
    have hmax : listMax (fun a => W (input.1, a)) input.2 ≤ H := listMax_le hw
    have hout : (el (cross input)).length ≤ cO * (H + input.2.length) := by
      have outRow (a : SortedMatch.Record) (ha : a ∈ input.2) :
          (el (input.1.map (fun b => (a.2/2, b.2/2)))).length ≤
            cO * ((input.1.length+1)*Q (crossWidth input)+1) := by
        have ho := outputBound (input.1, a)
        have h := rowWork input a ha
        exact ho.trans (Nat.mul_le_mul_left cO (by omega))
      have aux (rows : List SortedMatch.Record) (sub : ∀ a ∈ rows, a ∈ input.2) :
          (el (rows.flatMap (fun a => input.1.map (fun b => (a.2/2, b.2/2))))).length ≤
            rows.length * (cO * ((input.1.length+1)*Q (crossWidth input)+1)) := by
        induction rows with
        | nil => simp
        | cons a rows ih =>
          have ho := outRow a (sub a (by simp))
          have ht := ih (fun a ha => sub a (List.mem_cons_of_mem _ ha))
          simp only [List.flatMap_cons, encList_append, List.length_append, List.length_cons]
          nlinarith
      have hh := aux input.2 (fun _ h => h)
      change (el (input.2.flatMap _)).length ≤ _
      dsimp only [H]
      nlinarith [Nat.zero_le (cO * ((input.1.length+1)*Q (crossWidth input)))]
    have hn : input.2.length ≤ H := by
      have hQ : 1 ≤ Q (crossWidth input) := by dsimp only [Q]; omega
      dsimp only [H]
      nlinarith [Nat.mul_le_mul_left ((input.2.length+1)*(input.1.length+1)) hQ]
    change (encPair el el input).length + listMax (fun a => W (input.1, a)) input.2 +
      (el (cross input)).length ≤ (2*cO+10)*(H+1)
    nlinarith

private theorem test_polyTime : ComputableInPolyTime
    (fun q : Bool × SortedMatch.Record => decide (q.2.2 % 2 = if q.1 then 1 else 0))
    (encPair encBool er) encBool := by
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.decide_eq' (encB := encNat)
  · apply ComputableTidilyInPolyTime.binary_mod' <;> dsimp only [er] <;> fun_prop
  · exact (ComputableTidilyInPolyTime.fst encBool er).cond (.const 1) (.const 0)

/-- A bucket is filtered into its actual two side runs, then emitted by nested streaming.
The charged prefix space includes both filtered runs and the retained Cartesian output. -/
theorem pairs_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO KeyJoin.pairs (encList RadixPartition.recordEncoding)
      (encList RadixPartition.recordEncoding)
      (fun group => (group.length + KeyJoin.population group + 1) *
        P (streamRecordLength RadixPartition.recordEncoding group + 1))
      (fun group => (group.length + KeyJoin.population group + 1) *
        P (streamRecordLength RadixPartition.recordEncoding group + 1)) := by
  obtain ⟨F, hf, mf, filter⟩ := ComputableInO.filter_stream test_polyTime
  obtain ⟨P, hp, mp, cartesian⟩ := cross_computable
  have prepare (right : Bool) := (ComputableInO.const (encIn := el) (encMid := encBool) right).prod
    (ComputableInO.id' (encMid := el))
  have side (right : Bool) := (filter.comp (prepare right)).of_enc_eq
    (g := KeyJoin.side right) (encC := el) (fun _ => rfl)
  have both := (side true).prod (side false)
  have actual := (cartesian.comp both).of_enc_eq (g := KeyJoin.pairs) (encC := el) (fun _ => rfl)
  let Q := fun B => 20*B+20 + 2 * F (B+2) + 2 * P (2*B+1)
  have hQ : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have mQ : Monotone Q := by
    intro a b hab
    have hF := mf (by omega : a+2 ≤ b+2)
    have hP := mp (by omega : 2*a+1 ≤ 2*b+1)
    dsimp only [Q]
    omega
  have sizes (group : List SortedMatch.Record) :
      (KeyJoin.side false group).length ≤ group.length ∧
      (KeyJoin.side true group).length ≤ group.length :=
    ⟨List.length_filter_le _ _, List.length_filter_le _ _⟩
  have width (right : Bool) (group : List SortedMatch.Record) :
      streamRecordLength er (KeyJoin.side right group) ≤ streamRecordLength er group := by
    apply listMax_le
    intro row hr
    exact le_listMax (f := fun row => (er row).length) (List.mem_filter.mp hr).1
  have cross_width (group : List SortedMatch.Record) :
      crossWidth (KeyJoin.side true group, KeyJoin.side false group) ≤
        2 * (streamRecordLength er group+1) + 1 := by
    have h₁ := width false group
    have h₂ := width true group
    dsimp only [crossWidth]
    omega
  refine ⟨Q, hQ, mQ, actual.mono 10 ?_ ?_⟩ <;> intro group
  -- The same input/output volume bounds dominate both independent machine profiles.
  all_goals
    have hwire := list_wire group
    have hn := sizes group
    have hm := mp (cross_width group)
    have hF := mf (by
      simp only [streamFilterWidth, encBool_apply, List.length_singleton]
      omega : streamFilterWidth encBool er (false, group) ≤
      (streamRecordLength er group+1)+2)
    have hcount : ((KeyJoin.side false group).length+1)*((KeyJoin.side true group).length+1) ≤
        2*(group.length+KeyJoin.population group+1) := by
      dsimp only [KeyJoin.population]
      nlinarith [hn.1, hn.2]
    have hcross := Nat.mul_le_mul hcount hm
    have vlen : group.length+1 ≤ group.length+KeyJoin.population group+1 := by omega
    have qF : 2 * F (streamFilterWidth encBool er (false, group)) ≤
        Q (streamRecordLength er group+1) := by dsimp only [Q]; omega
    have qP : 2 * P (2*(streamRecordLength er group+1)+1) ≤
        Q (streamRecordLength er group+1) := by dsimp only [Q]; omega
    have qB : 20*(streamRecordLength er group+1)+20 ≤
        Q (streamRecordLength er group+1) := by dsimp only [Q]; omega
    have scaleF := Nat.mul_le_mul vlen qF
    have scaleP := Nat.mul_le_mul_left (group.length+KeyJoin.population group+1) qP
    have scaleB := Nat.mul_le_mul vlen qB
    dsimp only [el, er] at *
    simp only [length_encPair, streamFilterWidth, encBool_apply, List.length_singleton] at *
    nlinarith

/-- Input occurrences, emitted pairs and one unit per bucket, including empty buckets. -/
def volume (groups : List (List SortedMatch.Record)) : ℕ :=
  (groups.map (fun group => group.length + KeyJoin.population group + 1)).sum + 1

/-- Physical maximum row width, independent of the complete bucket volume. -/
def width (groups : List (List SortedMatch.Record)) : ℕ :=
  streamRecordLength er groups.flatten + 1

/-- The work measure is the actual quarter volume plus the actual class population. -/
theorem volume_eq (groups : List (List SortedMatch.Record)) :
    volume groups = groups.flatten.length + KeyJoin.count groups + groups.length + 1 := by
  simp only [volume, KeyJoin.count, List.length_flatten, List.sum_map_add,
    List.map_const', List.sum_replicate, smul_eq_mul, mul_one]

/-- Actual grouped joins have time and charged every-prefix space proportional to quarter
input plus emitted class size, times a polynomial only in physical record width. -/
theorem join_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO KeyJoin.join KeyGrouping.outputEncoding (encList RadixPartition.recordEncoding)
      (fun groups => volume groups * P (width groups))
      (fun groups => volume groups * P (width groups)) := by
  obtain ⟨P, hp, mp, pair⟩ := pairs_computable
  let w := fun group : List SortedMatch.Record => group.length + KeyJoin.population group + 1
  let W : Unit × List SortedMatch.Record → ℕ := fun q =>
    (encPair encUnit el q).length + w q.2 * P (streamRecordLength er q.2+1)
  have callback : ComputableInO (fun q : Unit × List SortedMatch.Record => KeyJoin.pairs q.2)
      (encPair encUnit el) el W W := pair.comp (ComputableInO.snd encUnit el)
  obtain ⟨cO, ho⟩ := callback.length_le
  let eg := encList el
  have prepare := (ComputableInO.const (encIn := eg) (encMid := encUnit) ()).prod
    (ComputableInO.id' (encMid := eg))
  have actual := (callback.flatMap_stream_sum.comp prepare).of_enc_eq
    (g := KeyJoin.join) (encC := el) (fun _ => rfl)
  let Q := fun B => P B + 20*B+20
  have hQ : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have mQ : Monotone Q := by intro a b hab; have := mp hab; dsimp only [Q]; omega
  have rowWork (groups : List (List SortedMatch.Record)) (group : List SortedMatch.Record)
      (hg : group ∈ groups) :
      W ((), group) + (encPair encUnit el ((), group)).length + 1 ≤ w group * Q (width groups) := by
    have hb : streamRecordLength er group + 1 ≤ width groups := by
      apply Nat.add_le_add_right
      apply listMax_le
      intro row hr
      exact le_listMax (f := fun row => (er row).length) (List.mem_flatten.mpr ⟨group, hg, hr⟩)
    have hm := Nat.mul_le_mul_left (w group) (mp hb)
    have hw := list_wire group
    have hB : streamRecordLength er group ≤ width groups := by omega
    have hs : group.length+1 ≤ w group := by dsimp only [w]; omega
    have hscale := Nat.mul_le_mul hs (by dsimp only [Q]; omega :
      20*width groups+20 ≤ Q (width groups))
    dsimp only [W]
    simp only [length_encPair, encUnit_apply, List.length_nil]
    have hq : w group * P (width groups) + w group * (20*width groups+20) =
        w group * Q (width groups) := by dsimp only [Q]; ring
    nlinarith [Nat.mul_le_mul_left group.length hB]
  have sumWeight (groups : List (List SortedMatch.Record)) :
      (groups.map w).sum + 1 = volume groups := rfl
  have inputWork (groups : List (List SortedMatch.Record)) :
      (eg groups).length ≤ volume groups * Q (width groups) := by
    have aux (rows : List (List SortedMatch.Record)) (sub : ∀ g ∈ rows, g ∈ groups) :
        (eg rows).length ≤ (rows.map w).sum * Q (width groups) := by
      induction rows with
      | nil => simp [eg]
      | cons g rows ih =>
        have hg := rowWork groups g (sub g (by simp))
        have ht := ih (fun g hg => sub g (List.mem_cons_of_mem _ hg))
        dsimp only [eg] at ht ⊢
        simp only [encList_cons, List.length_append, length_frame, List.map_cons, List.sum_cons]
        dsimp only [W] at hg
        simp only [length_encPair, encUnit_apply, List.length_nil] at hg
        nlinarith
    have h := aux groups (fun _ h => h)
    have hs := sumWeight groups
    nlinarith
  refine ⟨Q, hQ, mQ, actual.mono (4*cO+20) ?_ ?_⟩
  · intro groups
    have hi := inputWork groups
    have hsum := List.sum_le_sum (fun g hg => rowWork groups g hg)
    rw [List.sum_map_mul_right] at hsum
    have hw := sumWeight groups
    change (eg groups).length + (eg groups).length +
      ((encPair encUnit eg ((), groups)).length + _) ≤ _
    simp only [length_encPair, encUnit_apply, List.length_nil] at hsum ⊢
    nlinarith [Nat.zero_le (cO * (volume groups*Q (width groups)+1))]
  · intro groups
    let H := volume groups * Q (width groups)
    have hi : (eg groups).length ≤ H := inputWork groups
    have weightBound (g : List SortedMatch.Record) (hg : g ∈ groups) : w g ≤ volume groups := by
      have h : w g ≤ (groups.map w).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨g, hg, rfl⟩)
      have hs := sumWeight groups
      omega
    have maxWork : listMax (fun g => W ((),g)) groups ≤ H := by
      apply listMax_le
      intro g hg
      have h := rowWork groups g hg
      have ht := Nat.mul_le_mul_right (Q (width groups)) (weightBound g hg)
      dsimp only [H]
      omega
    have outputWork : (el (KeyJoin.join groups)).length ≤ cO * (2*H) := by
      have aux (rows : List (List SortedMatch.Record)) (sub : ∀ g ∈ rows, g ∈ groups) :
          (el (KeyJoin.join rows)).length ≤
            (rows.map (fun g => cO * (w g * Q (width groups)+1))).sum := by
        induction rows with
        | nil => rfl
        | cons g rows ih =>
          have ht := ih (fun g hg => sub g (List.mem_cons_of_mem _ hg))
          have ho := ho ((), g)
          have hw := rowWork groups g (sub g (by simp))
          simp only [KeyJoin.join, List.flatMap_cons, encList_append, List.length_append,
            List.map_cons, List.sum_cons] at *
          exact Nat.add_le_add (ho.trans (Nat.mul_le_mul_left cO (by omega))) ht
      have h := aux groups (fun _ h => h)
      simp only [List.sum_map_mul_left, List.sum_map_add, List.map_const',
        List.sum_replicate, smul_eq_mul, mul_one] at h
      rw [List.sum_map_mul_right] at h
      have hv := sumWeight groups
      have hn : groups.length ≤ volume groups := by rw [volume_eq]; omega
      have hQ : 1 ≤ Q (width groups) := by dsimp only [Q]; omega
      have hh := Nat.mul_le_mul_left (volume groups) hQ
      dsimp only [H]
      exact h.trans (Nat.mul_le_mul_left cO (by nlinarith))
    change (eg groups).length + (eg groups).length +
      ((encPair encUnit eg ((),groups)).length + listMax (fun g => W ((),g)) groups +
        (el (KeyJoin.join groups)).length) ≤ (4*cO+20)*(H+1)
    simp only [length_encPair, encUnit_apply, List.length_nil]
    nlinarith

end Turing.MultiTapeTM.KeyJoinStream

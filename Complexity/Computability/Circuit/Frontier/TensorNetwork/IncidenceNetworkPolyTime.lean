/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceArrays
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Mathlib.Data.List.GetD

/-!
# Binary polynomial-time writing of the incidence network

Charge actual incidence discovery, binomial index widths, ports, descriptors and padding in the
network construction of [OpenAI2026ETH], Lemma D.2, PDF pp. 55–56. Widths and structural counters
are unary; variable indices and tensor coordinates are binary. No tensor table is expanded.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.network_polytime`: binary polynomial-time writing of
  the actual described network, including all intermediate arithmetic and serialized output.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp. 55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

private abbrev encSys := encList (encList (encList encNat))
private abbrev encInc := encList (encPair encNat encNat)

private theorem sumUnary_polytime :
    ComputableInPolyTime List.sum (encList encUnary) encUnary := by
  have hc := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_sum).comp
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary.map)
  have hc' : ComputableInPolyTime List.sum (encList encUnary) encNat :=
    hc.of_enc_eq fun l => by simp
  refine binary_to_unary_bounded hc' (encoding_length _) ?_
  intro l
  induction l with
  | nil => simp
  | cons n l ih =>
    simp only [List.sum_cons, encList_cons, List.length_append, length_frame, encUnary_apply,
      List.length_replicate]
    omega

private theorem residue_polytime {α : Type} {enc : α ↪ List Bool} {J m g : α → ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun x => List.residueClass (J x) (m x) (g x)) enc (encList encUnary) := by
  unfold List.residueClass
  apply filterWithInput (unary_range' hm)
  fun_prop

private theorem pairInc_polytime {α : Type} {enc : α ↪ List Bool}
    {J g h : α → ℕ} {sys : α → List (List (List ℕ))}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hg : ComputableInPolyTime g enc encUnary) (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun x => pairInc (J x) (sys x) (g x) (h x)) enc encInc := by
  have hr := residue_polytime hJ ((length_list _).comp hsys) hg
  have hz := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.zipIdx encUnary)).comp hr
  unfold pairInc
  apply flatMapWithInput hz
  have hv : ComputableInPolyTime
      (fun q : α × (ℕ × ℕ) => equationVars ((sys q.1).getD q.2.1 []))
      (encPair enc (encPair encUnary encUnary)) (encList encNat) := by
    exact computableInPolyTime_equationVars.comp
      (listGetDWithInput (hsys.comp (fst enc (encPair encUnary encUnary)))
        (by fun_prop) [])
  apply mapWithInput (filterWithInput hv ?_)
  · have hpos : ComputableInPolyTime (fun q : (α × (ℕ × ℕ)) × ℕ => q.1.2.2)
        (encPair (encPair enc (encPair encUnary encUnary)) encNat) encUnary := by fun_prop
    exact (unary_to_binary.comp hpos).prod (by fun_prop)
  · have hJb := unary_to_binary.comp (hJ.comp (fst enc (encPair encUnary encUnary)))
    have hhb := unary_to_binary.comp (hh.comp (fst enc (encPair encUnary encUnary)))
    have hm := binary_mod.comp ((snd _ encNat).prod (hJb.comp (fst _ encNat)))
    exact decide_eq' hm (hhb.comp (fst _ encNat))

private theorem width_polytime {α : Type} {enc : α ↪ List Bool}
    {J g h : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hg : ComputableInPolyTime g enc encUnary) (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun x => width (J x) (sys x) (d x) (g x) (h x)) enc encUnary := by
  have hp := pairInc_polytime hJ hsys hg hh
  have hi : ComputableInPolyTime (fun x => g x * J x + h x) enc encUnary := by fun_prop
  exact binary_clog_two.comp (binary_choose' ((length_list _).comp hp)
    ((listGetD 0).comp (hd.prod hi)))

private theorem blockWidth_polytime {α : Type} {enc : α ↪ List Bool}
    {J b : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun x => blockWidth (J x) (sys x) (d x) (b x)) enc encUnary :=
  width_polytime hJ hsys hd (unary_div.comp (hb.prod hJ)) (unary_mod.comp (hb.prod hJ))

private theorem start_polytime {α : Type} {enc : α ↪ List Bool} {w : α → ℕ → ℕ} {b : α → ℕ}
    (hw : ComputableInPolyTime (fun p : α × ℕ => w p.1 p.2) (encPair enc encUnary) encUnary)
    (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun x => List.blockStart (w x) (b x)) enc encUnary :=
  sumUnary_polytime.comp (mapWithInput (unary_range' hb) hw)

private theorem rangeFrom_polytime {α : Type} {enc : α ↪ List Bool} {a n : α → ℕ}
    (ha : ComputableInPolyTime a enc encUnary) (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun x => List.range' (a x) (n x)) enc (encList encNat) := by
  have h := mapWithInput (f := fun x b => a x + b) (unary_range' hn) (unary_to_binary.comp
    (show ComputableInPolyTime (fun p : α × ℕ => a p.1 + p.2)
      (encPair enc encUnary) encUnary by fun_prop))
  apply h.of_enc_eq
  intro x
  simp only [List.range_eq_range', List.map_add_range', Nat.add_zero]

private theorem blockRange_polytime {α : Type} {enc : α ↪ List Bool}
    {J b : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun x => List.blockRange (blockWidth (J x) (sys x) (d x)) (b x))
      enc (encList encNat) := by
  have hw := blockWidth_polytime (hJ.comp (fst enc encUnary)) (hsys.comp (fst enc encUnary))
    (hd.comp (fst enc encUnary)) (snd enc encUnary)
  exact rangeFrom_polytime (start_polytime hw hb) (blockWidth_polytime hJ hsys hd hb)

private theorem numWires_polytime {α : Type} {enc : α ↪ List Bool}
    {J : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary)) :
    ComputableInPolyTime (fun x => numWires (J x) (sys x) (d x)) enc encUnary :=
  start_polytime (blockWidth_polytime (hJ.comp (fst enc encUnary))
    (hsys.comp (fst enc encUnary)) (hd.comp (fst enc encUnary)) (snd enc encUnary))
    (unary_mul' hJ hJ)

private theorem rowPorts_polytime {α : Type} {enc : α ↪ List Bool}
    {J g : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun x => rowPorts (J x) (sys x) (d x) (g x)) enc (encList encNat) := by
  unfold rowPorts
  apply flatMapWithInput (unary_range' hJ)
  apply blockRange_polytime (hJ.comp (fst enc encUnary)) (hsys.comp (fst enc encUnary))
    (hd.comp (fst enc encUnary))
  fun_prop

private theorem colPorts_polytime {α : Type} {enc : α ↪ List Bool}
    {J h : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun x => colPorts (J x) (sys x) (d x) (h x)) enc (encList encNat) := by
  unfold colPorts
  apply flatMapWithInput (unary_range' hJ)
  apply blockRange_polytime (hJ.comp (fst enc encUnary)) (hsys.comp (fst enc encUnary))
    (hd.comp (fst enc encUnary))
  fun_prop

private theorem rowBlocks_polytime {α : Type} {enc : α ↪ List Bool}
    {J g : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun x => rowBlocks (J x) (sys x) (d x) (g x)) enc (encList encBlock) := by
  unfold rowBlocks
  apply mapWithInput (unary_range' hJ)
  exact (pairInc_polytime (hJ.comp (fst enc encUnary)) (hsys.comp (fst enc encUnary))
    (hg.comp (fst enc encUnary)) (snd enc encUnary)).prod
      (listGetDWithInput (hd.comp (fst enc encUnary)) (by fun_prop) 0)

private theorem colBlocks_polytime {α : Type} {enc : α ↪ List Bool}
    {J h : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun x => colBlocks (J x) (sys x) (d x) (h x)) enc (encList encBlock) := by
  unfold colBlocks
  apply mapWithInput (unary_range' hJ)
  exact (pairInc_polytime (hJ.comp (fst enc encUnary)) (hsys.comp (fst enc encUnary))
    (snd enc encUnary) (hh.comp (fst enc encUnary))).prod
      (listGetDWithInput (hd.comp (fst enc encUnary)) (by fun_prop) 0)

private abbrev encVertex := encPair (encList encNat) encDesc

private theorem rowVertex_polytime {α : Type} {enc : α ↪ List Bool}
    {P ℓ J g : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hP : ComputableInPolyTime P enc encUnary) (hℓ : ComputableInPolyTime ℓ enc encUnary)
    (hJ : ComputableInPolyTime J enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun x => rowVertex (P x) (ℓ x) (J x) (sys x) (d x) (g x))
      enc encVertex := by
  have ht := mapWithInput (f := fun x i => (sys x).getD i [])
    (residue_polytime hJ ((length_list _).comp hsys) hg)
    (listGetDWithInput (hsys.comp (fst enc encUnary)) (snd enc encUnary) [])
  exact (rowPorts_polytime hJ hsys hd hg).prod
    ((sumInl encRowDesc (encSum encColDesc (encList encNat))).comp
      (hP.prod (hℓ.prod (ht.prod (rowBlocks_polytime hJ hsys hd hg)))))

private theorem colVertex_polytime {α : Type} {enc : α ↪ List Bool}
    {P J n h : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hP : ComputableInPolyTime P enc encUnary) (hJ : ComputableInPolyTime J enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary))
    (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun x => colVertex (P x) (J x) (n x) (sys x) (d x) (h x))
      enc encVertex := by
  have hv₀ := (of_tidy ComputableTidilyInPolyTime.unary_to_binary.map).comp
    (residue_polytime hJ hn hh)
  have hv : ComputableInPolyTime (fun x => List.residueClass (J x) (n x) (h x))
      enc (encList encNat) := hv₀.of_enc_eq fun x => by simp
  exact (colPorts_polytime hJ hsys hd hh).prod
    ((sumInr encRowDesc (encSum encColDesc (encList encNat))).comp
      ((sumInl encColDesc (encList encNat)).comp
        (hP.prod (hv.prod (colBlocks_polytime hJ hsys hd hh)))))

private theorem live_polytime {α : Type} {enc : α ↪ List Bool}
    {J K : α → ℕ} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hK : ComputableInPolyTime K enc encUnary)
    (hd : ComputableInPolyTime d enc (encList encUnary)) :
    ComputableInPolyTime (fun x => live (J x) (K x) (d x)) enc encBool := by
  have hl := mapWithInput (f := fun x b => (d x).getD b 0)
    (unary_range' (unary_mul' hJ hJ))
    (listGetDWithInput (hd.comp (fst enc encUnary)) (snd enc encUnary) 0)
  exact unary_le.comp ((sumUnary_polytime.comp hl).prod hK)

private theorem mainWires_polytime {α : Type} {enc : α ↪ List Bool}
    {J K : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hJ : ComputableInPolyTime J enc encUnary) (hK : ComputableInPolyTime K enc encUnary)
    (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary)) :
    ComputableInPolyTime (fun x => mainWires (J x) (K x) (sys x) (d x)) enc encUnary :=
  (live_polytime hJ hK hd).ite' (numWires_polytime hJ hsys hd) (const 0)

private theorem rows_polytime {α : Type} {enc : α ↪ List Bool}
    {P ℓ J K s : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hP : ComputableInPolyTime P enc encUnary) (hℓ : ComputableInPolyTime ℓ enc encUnary)
    (hJ : ComputableInPolyTime J enc encUnary) (hK : ComputableInPolyTime K enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary)) :
    ComputableInPolyTime (fun x => rows (P x) (ℓ x) (J x) (K x) (s x) (sys x) (d x))
      enc (encList encVertex) := by
  have hm := mainWires_polytime hJ hK hsys hd
  have hmain := mapWithInput (f := fun x g => rowVertex (P x) (ℓ x) (J x) (sys x) (d x) g)
    (unary_range' hJ) (rowVertex_polytime (hP.comp (fst enc encUnary))
      (hℓ.comp (fst enc encUnary)) (hJ.comp (fst enc encUnary))
      (hsys.comp (fst enc encUnary)) (hd.comp (fst enc encUnary)) (snd enc encUnary))
  have hpad : ComputableInPolyTime
      (fun q : α × ℕ => padRow (mainWires (J q.1) (K q.1) (sys q.1) (d q.1) + q.2))
      (encPair enc encUnary) encVertex := by
    have he := unary_to_binary.comp
      (unary_add' (hm.comp (fst enc encUnary)) (snd enc encUnary))
    exact (cons' he (const [])).prod (const (.inr (.inr [1, 0]) : Desc))
  exact ((live_polytime hJ hK hd).ite' hmain (const [deadRow])).listAppend'
    (mapWithInput (unary_range' (unary_sub' hs hm)) hpad)

private theorem cols_polytime {α : Type} {enc : α ↪ List Bool}
    {P J K s n : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hP : ComputableInPolyTime P enc encUnary) (hJ : ComputableInPolyTime J enc encUnary)
    (hK : ComputableInPolyTime K enc encUnary) (hs : ComputableInPolyTime s enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary) (hsys : ComputableInPolyTime sys enc encSys)
    (hd : ComputableInPolyTime d enc (encList encUnary)) :
    ComputableInPolyTime (fun x => cols (P x) (J x) (K x) (s x) (n x) (sys x) (d x))
      enc (encList encVertex) := by
  have hm := mainWires_polytime hJ hK hsys hd
  have hmain := mapWithInput (f := fun x h => colVertex (P x) (J x) (n x) (sys x) (d x) h)
    (unary_range' hJ) (colVertex_polytime (hP.comp (fst enc encUnary))
      (hJ.comp (fst enc encUnary)) (hn.comp (fst enc encUnary))
      (hsys.comp (fst enc encUnary)) (hd.comp (fst enc encUnary)) (snd enc encUnary))
  have hpad : ComputableInPolyTime
      (fun q : α × ℕ => padCol (mainWires (J q.1) (K q.1) (sys q.1) (d q.1) + q.2))
      (encPair enc encUnary) encVertex := by
    have he := unary_to_binary.comp
      (unary_add' (hm.comp (fst enc encUnary)) (snd enc encUnary))
    exact (cons' he (const [])).prod (const (.inr (.inr [1, 1]) : Desc))
  exact ((live_polytime hJ hK hd).ite' hmain (const [])).listAppend'
    (mapWithInput (unary_range' (unary_sub' hs hm)) hpad)

/-- The actual network writer is binary polynomial-time, including incidence discovery,
binomial widths, ports, tags, descriptor copying and padding. These closure premises
are discharged by actual computed parameters downstream; no output/resource budget
is advice. -/
theorem network_polytime {α : Type} {enc : α ↪ List Bool}
    {P ℓ J K s n : α → ℕ} {sys : α → List (List (List ℕ))} {d : α → List ℕ}
    (hP : ComputableInPolyTime P enc encUnary) (hℓ : ComputableInPolyTime ℓ enc encUnary)
    (hJ : ComputableInPolyTime J enc encUnary) (hK : ComputableInPolyTime K enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary) (hn : ComputableInPolyTime n enc encUnary)
    (hsys : ComputableInPolyTime sys enc (encList (encList (encList encNat))))
    (hd : ComputableInPolyTime d enc (encList encUnary)) :
    ComputableInPolyTime (fun x => network (P x) (ℓ x) (J x) (K x) (s x) (n x) (sys x) (d x))
      enc (encPair encNat (DescribedNetwork.encDescribed encDesc)) := by
  have hr := rows_polytime hP hℓ hJ hK hs hsys hd
  have hc := cols_polytime hP hJ hK hs hn hsys hd
  have hm := mainWires_polytime hJ hK hsys hd
  have he : ComputableInPolyTime
      (fun x => mainWires (J x) (K x) (sys x) (d x) + (s x - mainWires (J x) (K x) (sys x) (d x)))
      enc encUnary := by fun_prop
  have ho := (unary_to_binary.comp ((length_list encVertex).comp hr)).prod
    (he.prod (hr.listAppend' hc))
  exact ho.of_enc_eq fun _ => rfl

end Cslib.Circuits.Frontier.IncidenceNetwork

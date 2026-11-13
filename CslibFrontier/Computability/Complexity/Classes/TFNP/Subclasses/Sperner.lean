/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.Completeness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Foundations.Combinatorics.Sperner
public import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import Mathlib.Data.FinEnum

/-!
# Circuit `2D-SPERNER` is in `PPAD`

An instance `(m, C)` of `Sperner2D` is a unary size parameter `m` and a Boolean circuit code `C`.
It colours the points of the `2 ^ m × 2 ^ m` grid (`Sperner2D.color`): boundary points receive the
Sperner boundary colour `Cslib.Sperner.boundaryColor`, and an interior point `(x, y)` receives the
colour read off the outputs of `C` on the `m`-bit codes of `x` and `y` (`Sperner2D.outputColor`). A
solution is the `2m + 1`-bit code of a trichromatic triangle (`Sperner2D.encodeTriangle`). Every
instance colours the grid by a Sperner colouring, so every instance has a solution by Sperner's
lemma (`Cslib.Sperner.IsSpernerColoring.exists_trichromatic`).

The proof of Sperner's lemma by following doors is the `PPAD` argument. Transported to triangle
codes, the door graph `Cslib.Sperner.next`, `Cslib.Sperner.prev` is computed in polynomial time
(`Sperner2D.succ`, `Sperner2D.pred`), its distinguished source `Cslib.Sperner.start` has code
`zeroVertex (2m + 1)`, and `Sperner2D` is *equal* to the end-of-line relation of this graph
(`Sperner2D.eq_endOfLineRel`). Membership in `PPAD` and the search reduction to `EndOfLine` follow
from the general results for `endOfLineRel`.

`Sperner2D` is the two-dimensional discrete Brouwer problem of Chen, Deng and Teng
[ChenDengTeng2009] (Section 4.1, Definitions 4.2, 4.4 and 4.5 with `d = 2`), up to the following
presentation choices.

* The grid has the points `0, …, 2 ^ m` in each coordinate rather than `0, …, 2 ^ m - 1`, so that
  the `2 ^ (2m + 1)` triangle codes are exactly the triangles. The circuit receives the `m`-bit
  codes of the coordinates of interior points only, rather than codes of all grid points.
* The boundary colouring is imposed by the problem rather than promised by the circuit, and the
  outputs of the circuit are decoded into a colour on every input: colour `1` if output bit `0` is
  set, otherwise colour `2` if output bit `2` is set, otherwise colour `0` (their colour `3`). With
  their output order `Δ₁⁺, Δ₁⁻, Δ₂⁺, Δ₂⁻`, outputs in their Case `i` decode to colour `i`. Hence
  there is no promise: every instance is valid and `Sperner2D` is a total search problem.
* Solutions are the trichromatic triangles of the triangulation cutting each unit square along its
  main diagonal. For a given colouring, each such triangle is a panchromatic simplex in the sense
  of their Definition 4.2.

Because of the different grid size and input encoding, an instance of `Sperner2D` is not literally
an instance of their problem.

The membership in `PPAD` is due to Papadimitriou [Papadimitriou1994PPAD]; this file formalizes the
door-following reduction to `EndOfLine` for this presentation.

## Main definitions

* `Cslib.Complexity.Sperner2D`: circuit `2D-SPERNER`, with instance encoding
  `Cslib.Complexity.encSperner2D`.
* `Cslib.Complexity.Sperner2D.color`: the Sperner colouring presented by an instance.
* `Cslib.Complexity.Sperner2D.succ`, `Cslib.Complexity.Sperner2D.pred`: the door graph on triangle
  codes.

## Main results

* `Cslib.Complexity.Sperner2D.eq_endOfLineRel`: `Sperner2D` is the end-of-line relation of the door
  graph.
* `Cslib.Complexity.Sperner2D_mem_PPAD`: `Sperner2D ∈ PPAD`.
* `Cslib.Complexity.Sperner2D_mem_TFNP`: `Sperner2D ∈ TFNP`.
* `Cslib.Complexity.Sperner2D_searchReducible_EndOfLine`: `Sperner2D` reduces to `EndOfLine`.

## References

* [X. Chen, X. Deng and S.-H. Teng, *Settling the complexity of computing two-player Nash
  equilibria*][ChenDengTeng2009]
* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
-/

public section

namespace Cslib.Complexity

open Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Sperner Cslib.Sperner.GridTriangle
open Turing.MultiTapeTM ComputableInPolyTime

namespace Sperner2D

/-- The colour read off the output bits of a colouring circuit: colour `1` if output bit `0` is set,
otherwise colour `2` if output bit `2` is set, otherwise colour `0`. On outputs in the case encoding
`Δ₁⁺, Δ₁⁻, Δ₂⁺, Δ₂⁻` of Chen, Deng and Teng, Case `i` decodes to colour `i` (Case `3` to `0`). -/
@[expose] def outputColor (out : List Bool) : Fin 3 :=
  if out.getD 0 false then 1 else if out.getD 2 false then 2 else 0

/-- The colouring of the `2 ^ m × 2 ^ m` grid presented by the instance `(m, code)`: the boundary
colour on the boundary, and the colour computed by `code` from the `m`-bit codes of the coordinates
(least significant bit first) elsewhere. -/
@[expose] def color (inst : ℕ × CircuitCode) (p : ℕ × ℕ) : Fin 3 :=
  if p.1 = 0 ∨ p.2 = 0 ∨ p.1 = 2 ^ inst.1 ∨ p.2 = 2 ^ inst.1 then boundaryColor p
  else outputColor (evalCircuitOutputs inst.2 (lowBits inst.1 p.1 ++ lowBits inst.1 p.2))

/-- The `2m + 1`-bit code of a triangle: its orientation bit, then the `m`-bit codes of `x` and `y`
(least significant bit first). -/
@[expose] def encodeTriangle (m : ℕ) (t : GridTriangle) : List Bool :=
  t.lower :: (lowBits m t.x ++ lowBits m t.y)

/-- Decode a `2m + 1`-bit word as a triangle; inverse to `encodeTriangle` on the grid. -/
@[expose] def decodeTriangle (m : ℕ) (w : List Bool) : GridTriangle :=
  ⟨w.headD false, lsbValue (w.tail.take m), lsbValue (w.tail.drop m)⟩

/-- The successor function of the door graph on triangle codes. -/
@[expose] def succ (p : (ℕ × CircuitCode) × List Bool) : List Bool :=
  encodeTriangle p.1.1 (next (color p.1) (2 ^ p.1.1) (2 ^ p.1.1) (decodeTriangle p.1.1 p.2))

/-- The predecessor function of the door graph on triangle codes. -/
@[expose] def pred (p : (ℕ × CircuitCode) × List Bool) : List Bool :=
  encodeTriangle p.1.1 (prev (color p.1) (2 ^ p.1.1) (2 ^ p.1.1) (decodeTriangle p.1.1 p.2))

end Sperner2D

open Sperner2D

/-- Instances `(m, code)` of `Sperner2D`: the size parameter `m` in unary (framed), then the circuit
code. -/
abbrev encSperner2D : (ℕ × CircuitCode) ↪ List Bool := encPair encUnary encCode

/-- **Circuit `2D-SPERNER`.** A solution of the instance `(m, code)` is the `2m + 1`-bit code of a
trichromatic triangle of the colouring `Sperner2D.color (m, code)` of the `2 ^ m × 2 ^ m` grid. -/
@[expose] def Sperner2D (inst : ℕ × CircuitCode) (w : List Bool) : Prop :=
  w.length = 2 * inst.1 + 1 ∧ Trichromatic (color inst) (decodeTriangle inst.1 w)

instance (inst : ℕ × CircuitCode) (w : List Bool) : Decidable (Sperner2D inst w) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace Sperner2D

/-- Decoding inverts encoding on the triangles of the grid. -/
theorem decodeTriangle_encodeTriangle {m : ℕ} {t : GridTriangle} (ht : InGrid (2 ^ m) (2 ^ m) t) :
    decodeTriangle m (encodeTriangle m t) = t := by
  obtain ⟨l, x, y⟩ := t
  obtain ⟨hx, hy⟩ := ht
  simp only [decodeTriangle, encodeTriangle, List.headD_cons, List.tail_cons,
    List.take_left' (length_lowBits m x), List.drop_left' (length_lowBits m x),
    lsbValue_lowBits hx, lsbValue_lowBits hy]

theorem length_encodeTriangle (m : ℕ) (t : GridTriangle) :
    (encodeTriangle m t).length = 2 * m + 1 := by
  simp only [encodeTriangle, List.length_cons, List.length_append, length_lowBits]
  omega

/-- Every word of length `2m + 1` is the code of its decoding. -/
theorem encodeTriangle_decodeTriangle {m : ℕ} {w : List Bool} (hw : w.length = 2 * m + 1) :
    encodeTriangle m (decodeTriangle m w) = w := by
  obtain _ | ⟨b, w⟩ := w
  · simp at hw
  · simp only [encodeTriangle, decodeTriangle, List.headD_cons, List.tail_cons]
    have e1 := lowBits_lsbValue (w.take m)
    have e2 := lowBits_lsbValue (w.drop m)
    rw [List.length_take_of_le (by simp at hw; omega)] at e1
    rw [List.length_drop, show w.length - m = m by simp at hw; omega] at e2
    rw [e1, e2, List.take_append_drop]

/-- Every word of length `2m + 1` decodes to a triangle of the grid. -/
theorem inGrid_decodeTriangle {m : ℕ} {w : List Bool} (hw : w.length = 2 * m + 1) :
    InGrid (2 ^ m) (2 ^ m) (decodeTriangle m w) := by
  have h1 : (w.tail.take m).length = m := by simp; omega
  have h2 : (w.tail.drop m).length = m := by simp; omega
  have e1 := lsbValue_lt (w.tail.take m)
  have e2 := lsbValue_lt (w.tail.drop m)
  rw [h1] at e1
  rw [h2] at e2
  exact ⟨e1, e2⟩

/-- The distinguished source `start` has the all-zero code. -/
theorem encodeTriangle_start (m : ℕ) : encodeTriangle m start = zeroVertex (2 * m + 1) := by
  have h0 : ∀ n, lowBits n 0 = List.replicate n false := fun n => by
    rw [lowBits, List.eq_replicate_iff]
    simp
  simp only [encodeTriangle, start, h0, zeroVertex, ← List.replicate_add]
  rw [show 2 * m + 1 = (m + m) + 1 by omega, List.replicate_succ]

theorem encodeTriangle_inj {m : ℕ} {t t' : GridTriangle} (ht : InGrid (2 ^ m) (2 ^ m) t)
    (ht' : InGrid (2 ^ m) (2 ^ m) t') : encodeTriangle m t = encodeTriangle m t' ↔ t = t' :=
  ⟨fun h => by rw [← decodeTriangle_encodeTriangle ht, h, decodeTriangle_encodeTriangle ht'],
    congrArg _⟩

/-- Every instance presents a Sperner colouring. -/
theorem isSpernerColoring_color (inst : ℕ × CircuitCode) :
    IsSpernerColoring (2 ^ inst.1) (color inst) := by
  intro x y _ _ h
  exact ite_eq_left h

/-- A triangle code has an outgoing edge exactly when the triangle has an exit door. -/
theorem hasOut_encodeTriangle {inst : ℕ × CircuitCode} {t : GridTriangle}
    (ht : InGrid (2 ^ inst.1) (2 ^ inst.1) t) :
    hasOut (fun inst => 2 * inst.1 + 1) pred succ inst (encodeTriangle inst.1 t) = true ↔
      HasExit (color inst) t := by
  have hnext := inGrid_next (c := color inst) ht
  have hs : InGrid (2 ^ inst.1) (2 ^ inst.1) start := inGrid_start_iff.mpr (Nat.two_pow_pos _)
  simp only [hasOut, succ, pred, decodeTriangle_encodeTriangle ht,
    decodeTriangle_encodeTriangle hnext, ← encodeTriangle_start, ne_eq,
    encodeTriangle_inj (inGrid_prev hnext) ht, encodeTriangle_inj hnext ht,
    encodeTriangle_inj hnext hs, decide_eq_true_eq]
  exact (isSpernerColoring_color inst).door_out_iff ht

/-- A triangle code has an incoming edge exactly when the triangle has an entry door and is not
`start`. -/
theorem hasIn_encodeTriangle {inst : ℕ × CircuitCode} {t : GridTriangle}
    (ht : InGrid (2 ^ inst.1) (2 ^ inst.1) t) :
    hasIn (fun inst => 2 * inst.1 + 1) pred succ inst (encodeTriangle inst.1 t) = true ↔
      HasEntry (color inst) t ∧ t ≠ start := by
  have hprev := inGrid_prev (c := color inst) ht
  have hs : InGrid (2 ^ inst.1) (2 ^ inst.1) start := inGrid_start_iff.mpr (Nat.two_pow_pos _)
  simp only [hasIn, succ, pred, decodeTriangle_encodeTriangle ht,
    decodeTriangle_encodeTriangle hprev, ← encodeTriangle_start, ne_eq,
    encodeTriangle_inj (inGrid_next hprev) ht, encodeTriangle_inj hprev ht,
    encodeTriangle_inj ht hs, decide_eq_true_eq]
  exact (isSpernerColoring_color inst).door_in_iff ht

/-- `Sperner2D` is the end-of-line problem of the door graph on triangle codes. -/
theorem eq_endOfLineRel :
    Sperner2D = endOfLineRel (fun inst => 2 * inst.1 + 1) pred succ := by
  funext inst u
  apply propext
  refine and_congr_right fun hu => ?_
  obtain ⟨t, ht, rfl⟩ : ∃ t, InGrid (2 ^ inst.1) (2 ^ inst.1) t ∧ encodeTriangle inst.1 t = u :=
    ⟨_, inGrid_decodeTriangle hu, encodeTriangle_decodeTriangle hu⟩
  have hs : InGrid (2 ^ inst.1) (2 ^ inst.1) start := inGrid_start_iff.mpr (Nat.two_pow_pos _)
  have hin := hasIn_encodeTriangle ht
  have hout := hasOut_encodeTriangle ht
  have hz : encodeTriangle inst.1 t = zeroVertex (2 * inst.1 + 1) ↔ t = start := by
    rw [← encodeTriangle_start, encodeTriangle_inj ht hs]
  rw [decodeTriangle_encodeTriangle ht, (isSpernerColoring_color inst).trichromatic_iff ht,
    ← hin, ← hout, ← hz]
  generalize hasIn (fun inst => 2 * inst.1 + 1) pred succ inst (encodeTriangle inst.1 t) = a
  generalize hasOut (fun inst => 2 * inst.1 + 1) pred succ inst (encodeTriangle inst.1 t) = b
  by_cases h : encodeTriangle inst.1 t = zeroVertex (2 * inst.1 + 1) <;>
    cases a <;> cases b <;> simp [h]


/-! ### Polynomial-time door graph -/

/-- Grid triangles encoded as triples, for the polynomial-time proofs below. (`enc_structure` would
add public `ComputableInO` rules that these proofs do not use.) -/
private def encTri : GridTriangle ↪ List Bool :=
  equivProd.toEmbedding.trans (encPair encBool (encPair encNat encNat))

private theorem mk_tri {α : Type} {enc : α ↪ List Bool} {l : α → Bool} {x y : α → ℕ}
    (hl : ComputableInPolyTime l enc encBool) (hx : ComputableInPolyTime x enc encNat)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun a => (⟨l a, x a, y a⟩ : GridTriangle)) enc encTri :=
  (hl.prod (hx.prod hy)).of_enc_eq fun _ => rfl

private theorem toTriple {α : Type} {enc : α ↪ List Bool} {t : α → GridTriangle}
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun a => ((t a).lower, (t a).x, (t a).y)) enc
      (encPair encBool (encPair encNat encNat)) :=
  ht.of_enc_eq fun _ => rfl

private theorem lower_tri {α : Type} {enc : α ↪ List Bool} {t : α → GridTriangle}
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun a => (t a).lower) enc encBool :=
  (toTriple ht).fst'

private theorem x_tri {α : Type} {enc : α ↪ List Bool} {t : α → GridTriangle}
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun a => (t a).x) enc encNat :=
  (toTriple ht).snd'.fst'

private theorem y_tri {α : Type} {enc : α ↪ List Bool} {t : α → GridTriangle}
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun a => (t a).y) enc encNat :=
  (toTriple ht).snd'.snd'

attribute [local fun_prop] mk_tri lower_tri x_tri y_tri

private theorem corner_eq (t : GridTriangle) (k : Fin 3) :
    t.corner k =
      (if k = 0 then t.x else if k = 1 then t.x + 1 else if t.lower then t.x + 1 else t.x,
        if k = 0 then t.y else if k = 1 then (if t.lower then t.y else t.y + 1) else t.y + 1) := by
  obtain ⟨_ | _, x, y⟩ := t <;> fin_cases k <;> rfl

private theorem corner_tri {α : Type} {enc : α ↪ List Bool} {t : α → GridTriangle} (k : Fin 3)
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun a => (t a).corner k) enc (encPair encNat encNat) := by
  simp only [corner_eq]
  fun_prop

attribute [local fun_prop] corner_tri

private theorem color_poly {α : Type} {enc : α ↪ List Bool} {a : α → ℕ × CircuitCode}
    {p : α → ℕ × ℕ} (ha : ComputableInPolyTime a enc encSperner2D)
    (hp : ComputableInPolyTime p enc (encPair encNat encNat)) :
    ComputableInPolyTime (fun b => color (a b) (p b)) enc (encFinEnum (Fin 3)) := by
  unfold color boundaryColor outputColor
  fun_prop

attribute [local fun_prop] color_poly

private theorem interior_eq (W H : ℕ) (t : GridTriangle) (k : Fin 3) :
    interior W H t k =
      if k = 0 then (if t.lower then decide (0 < t.y) else true)
      else if k = 1 then (if t.lower then decide (t.x + 1 < W) else decide (t.y + 1 < H))
      else (if t.lower then true else decide (0 < t.x)) := by
  obtain ⟨_ | _, x, y⟩ := t <;> fin_cases k <;> rfl

private theorem interior_tri {α : Type} {enc : α ↪ List Bool} {t : α → GridTriangle}
    {W H : α → ℕ} (k : Fin 3) (hW : ComputableInPolyTime W enc encNat)
    (hH : ComputableInPolyTime H enc encNat) (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun a => interior (W a) (H a) (t a) k) enc encBool := by
  simp only [interior_eq]
  fun_prop

private theorem across_eq (t : GridTriangle) (k : Fin 3) :
    t.across k =
      ⟨!t.lower,
        if k = 0 then t.x else if k = 1 then (if t.lower then t.x + 1 else t.x)
        else (if t.lower then t.x else t.x - 1),
        if k = 0 then (if t.lower then t.y - 1 else t.y)
        else if k = 1 then (if t.lower then t.y else t.y + 1) else t.y⟩ := by
  obtain ⟨_ | _, x, y⟩ := t <;> fin_cases k <;> rfl

private theorem across_tri {α : Type} {enc : α ↪ List Bool} {t : α → GridTriangle} (k : Fin 3)
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun a => (t a).across k) enc encTri := by
  simp only [across_eq]
  fun_prop

attribute [local fun_prop] interior_tri across_tri

private theorem isExit_tri {α : Type} {enc : α ↪ List Bool} {a : α → ℕ × CircuitCode}
    {t : α → GridTriangle} (k : Fin 3) (ha : ComputableInPolyTime a enc encSperner2D)
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun b => decide (IsExit (color (a b)) (t b) k)) enc encBool := by
  unfold IsExit
  fun_prop

private theorem isEntry_tri {α : Type} {enc : α ↪ List Bool} {a : α → ℕ × CircuitCode}
    {t : α → GridTriangle} (k : Fin 3) (ha : ComputableInPolyTime a enc encSperner2D)
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun b => decide (IsEntry (color (a b)) (t b) k)) enc encBool := by
  unfold IsEntry
  fun_prop

attribute [local fun_prop] isExit_tri isEntry_tri

private theorem next_tri {α : Type} {enc : α ↪ List Bool} {a : α → ℕ × CircuitCode}
    {t : α → GridTriangle} (ha : ComputableInPolyTime a enc encSperner2D)
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun b => next (color (a b)) (2 ^ (a b).1) (2 ^ (a b).1) (t b)) enc
      encTri := by
  unfold next
  fun_prop

private theorem prev_tri {α : Type} {enc : α ↪ List Bool} {a : α → ℕ × CircuitCode}
    {t : α → GridTriangle} (ha : ComputableInPolyTime a enc encSperner2D)
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun b => prev (color (a b)) (2 ^ (a b).1) (2 ^ (a b).1) (t b)) enc
      encTri := by
  unfold prev
  fun_prop

attribute [local fun_prop] next_tri prev_tri

private theorem decodeTriangle_tri {α : Type} {enc : α ↪ List Bool} {m : α → ℕ}
    {w : α → List Bool} (hm : ComputableInPolyTime m enc encUnary)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime (fun a => decodeTriangle (m a) (w a)) enc encTri := by
  simp only [decodeTriangle, ← ofBits_eq_lsbValue]
  fun_prop

private theorem encodeTriangle_tri {α : Type} {enc : α ↪ List Bool} {m : α → ℕ}
    {t : α → GridTriangle} (hm : ComputableInPolyTime m enc encUnary)
    (ht : ComputableInPolyTime t enc encTri) :
    ComputableInPolyTime (fun a => encodeTriangle (m a) (t a)) enc encBits := by
  unfold encodeTriangle
  fun_prop

attribute [local fun_prop] decodeTriangle_tri encodeTriangle_tri

/-- The successor function of the door graph is computable in polynomial time. -/
theorem computableInPolyTime_succ :
    ComputableInPolyTime succ (encPair encSperner2D encBits) encBits := by
  unfold succ
  fun_prop

/-- The predecessor function of the door graph is computable in polynomial time. -/
theorem computableInPolyTime_pred :
    ComputableInPolyTime pred (encPair encSperner2D encBits) encBits := by
  unfold pred
  fun_prop

/-- The length `2m + 1` of triangle codes is computable in polynomial time, in unary. -/
theorem computableInPolyTime_length :
    ComputableInPolyTime (fun inst : ℕ × CircuitCode => 2 * inst.1 + 1) encSperner2D encUnary := by
  fun_prop

theorem length_succ (p : (ℕ × CircuitCode) × List Bool) : (succ p).length = 2 * p.1.1 + 1 :=
  length_encodeTriangle _ _

theorem length_pred (p : (ℕ × CircuitCode) × List Bool) : (pred p).length = 2 * p.1.1 + 1 :=
  length_encodeTriangle _ _

end Sperner2D

open Sperner2D

/-- **Circuit `2D-SPERNER` is in `PPAD`.** -/
theorem Sperner2D_mem_PPAD : Sperner2D ∈ PPAD encSperner2D := by
  rw [eq_endOfLineRel]
  exact endOfLineRel_mem_PPAD computableInPolyTime_length computableInPolyTime_pred
    computableInPolyTime_succ (fun a u _ => length_pred (a, u))
    (fun a u _ => length_succ (a, u))

/-- Circuit `2D-SPERNER` is a total search problem in `FNP`. -/
theorem Sperner2D_mem_TFNP : Sperner2D ∈ TFNP encSperner2D := by
  rw [eq_endOfLineRel]
  exact endOfLineRel_mem_TFNP computableInPolyTime_length computableInPolyTime_pred
    computableInPolyTime_succ (fun a u _ => length_succ (a, u))

/-- Circuit `2D-SPERNER` reduces to `EndOfLine`, mapping the colouring circuit to circuits for the
door graph and returning the vertex found. -/
theorem Sperner2D_searchReducible_EndOfLine :
    SearchReducible encSperner2D encEndOfLine Sperner2D EndOfLine := by
  rw [eq_endOfLineRel]
  exact endOfLineRel_searchReducible_EndOfLine computableInPolyTime_length
    computableInPolyTime_pred computableInPolyTime_succ (fun a u _ => length_pred (a, u))
    (fun a u _ => length_succ (a, u))

end Cslib.Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Hierarchy.Time
public import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Computability.Complexity.Classes.Time.BoundedExists
import Complexity.Computability.Complexity.Classes.Time.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# A nondeterministic time hierarchy by lazy diagonalization

For every degree `d`, nondeterministic time `O((n + 1) ^ d)` is strictly contained in
nondeterministic time `O((n + 1) ^ e)` on bit strings whenever `6 * d + 14 ≤ e`
(`Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le`). This is a coarse form of the
nondeterministic time hierarchy theorem [Arora and Barak, Theorem 3.3][AroraBarak07], proved by
lazy diagonalization [Žák][Zak1983]. The separating problem is explicit: the lazy diagonal
`Cslib.Complexity.lazyDiagonal d`.

## The lazy diagonal

A diagonal for nondeterministic time cannot simply negate the answer of the machine it
simulates: that answer is an existential over certificates. Lazy diagonalization negates it only
once per interval of lengths, where the input is long enough to try every certificate.

An input `x` carries a word `w` framed at its start, and `w` carries the description
`unframe w` of a deterministic verifier on pairs framed at its start, followed by arbitrary
padding. The padding of `w` gives each description infinitely many words `w`. The interval of
`w` consists of the lengths from `P = 2 * w.length + 1`, the length of `frame w`, to
`2 ^ clock d P - 1`, where `clock d m = (m + 1) ^ (d + 3)`. On the input `x` of length `n` in
this interval, with a certificate `v` of length `certLen d (n + 1) = (n + 2) ^ (d + 2)`, the
verifier `Cslib.Complexity.LazyDiagonal.verifier d`

* below the end of the interval, runs the described verifier on the one bit longer input
  `x ++ [false]` and the certificate `v` for `clock d (n + 1)` steps with the universal function
  (`Cslib.Complexity.LazyDiagonal.accepts`);
* at the end of the interval, accepts when the described verifier accepts no certificate of
  length `certLen d P` on `frame w`, trying them all.

The lazy diagonal is the problem of the inputs with an accepted certificate.

* **Upper bound** (`Cslib.Complexity.lazyDiagonal_mem_NTIME`). Guess the certificate and run the
  verifier (`Cslib.Complexity.setOf_exists_mem_NTIME`). The simulation takes time
  `O((n + 1) ^ (6 * d + 14))`: polynomial in the input, the certificate and the clock, through the
  native universal machine. The brute force takes time `2 ^ O((P + 1) ^ (d + 2))`
  (`Cslib.Complexity.exists_computableInO_any_enumList`), which is `O(n)` at the end of the
  interval, where `n + 1 = 2 ^ ((P + 1) ^ (d + 3))`.
* **Lower bound** (`Cslib.Complexity.lazyDiagonal_notMem_NTIME`). A nondeterministic machine
  deciding the problem within time `O((n + 1) ^ d)` has a deterministic verifier on pairs within
  linear time, accepting certificates of every length at least `c * (n + 1) ^ d + c`
  (`Cslib.Complexity.exists_verifier_of_mem_NTIME`). On the interval of a word `w` describing that
  verifier, with enough padding, the universal function runs it exactly. Then each input of the
  interval is in the problem exactly when the next one is, and the last exactly when the first is
  not.

Arora and Barak enumerate nondeterministic machines and use one global sequence of intervals; this
construction gives each word `w` its own interval instead, and diagonalizes against verifiers.
The gap `6 * d + 14` is the polynomial overhead of the native universal machine and of the
certificate length, not the textbook `f (n + 1) = o (g n)`.

## Main definitions

* `Cslib.Complexity.LazyDiagonal.verifier`: the verifier of the lazy diagonal.
* `Cslib.Complexity.lazyDiagonal`: the lazy diagonal problem for degree `d`.

## Main results

* `Cslib.Complexity.lazyDiagonal_mem_NTIME`: the lazy diagonal is in
  `NTIME ((n + 1) ^ (6 * d + 14))`.
* `Cslib.Complexity.lazyDiagonal_notMem_NTIME`: the lazy diagonal is not in `NTIME ((n + 1) ^ d)`.
* `Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le`: the hierarchy.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
* [S. Žák, *A Turing machine time hierarchy*][Zak1983]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

namespace LazyDiagonal

/-- The certificate length of the lazy diagonal on words of length `m`: `(m + 1) ^ (d + 2)`. -/
def certLen (d m : ℕ) : ℕ := (m + 1) ^ (d + 2)

/-- The clock of the lazy diagonal on words of length `m`: `(m + 1) ^ (d + 3)`. It bounds the
simulated steps on `m`, and the interval of lengths starting at `m` ends below `2 ^ clock d m`. -/
def clock (d m : ℕ) : ℕ := (m + 1) ^ (d + 3)

/-- The machine described by `c`, run as a verifier on the pair `(y, v)` (encoded as
`frame y ++ v`) for `clock d y.length` steps with the universal function, has halted with output
`[true]`. -/
def accepts (d : ℕ) (c y v : List Bool) : Bool :=
  !Diagonal.verdict (universal (decodeDesc c, (frame y ++ v).map eBit, clock d y.length))

/-- **The verifier of the lazy diagonal**, on an input `x` of length `n` and a certificate `v`.
The input carries a word `w` framed at its start, and `w` carries the description `unframe w`
framed at its start. When the description is short (`Cslib.Complexity.Diagonal.shortDesc w`),
let `P = 2 * w.length + 1`; the lengths from `P` to `2 ^ clock d P - 1` form the interval of `w`.

* If `n + 1 < 2 ^ clock d P`, below the end of the interval, accept when the described verifier
  accepts `v` on the input one bit longer.
* If `n + 1 = 2 ^ clock d P`, at the end of the interval, accept when the described verifier
  accepts no certificate on `frame w`, the input of length `P`, by trying them all.
* Otherwise, and when the description is not short, reject. -/
def verifier (d : ℕ) (p : List Bool × List Bool) : Bool :=
  if Diagonal.shortDesc (unframe p.1) then
    if Nat.size (p.1.length + 1) ≤ clock d (2 * (unframe p.1).length + 1) then
      accepts d (unframe (unframe p.1)) (p.1 ++ [false]) p.2
    else if Nat.size p.1.length ≤ clock d (2 * (unframe p.1).length + 1) then
      !(Cslib.BitString.enumList (certLen d (2 * (unframe p.1).length + 1))).any
        (accepts d (unframe (unframe p.1)) (frame (unframe p.1)))
    else false
  else false

end LazyDiagonal

open LazyDiagonal

/-- **The lazy diagonal language** for degree `d`: the words `x` with a certificate of length
`(x.length + 2) ^ (d + 2)` accepted by `Cslib.Complexity.LazyDiagonal.verifier d`. -/
def lazyDiagonal (d : ℕ) : Set (List Bool) :=
  {x | ∃ v : List Bool, v.length = certLen d (x.length + 1) ∧ verifier d (x, v) = true}

/-! ### The lazy diagonal is not in `NTIME ((n + 1) ^ d)` -/

/-- The lengths at which certificates of length `certLen d m` and `clock d m` simulated steps
suffice for a verifier with constants `c` and `c₂`. -/
private theorem exists_le_certLen_clock (d c c₂ : ℕ) : ∃ M, ∀ m, M ≤ m →
    c * (m + 1) ^ d + c ≤ certLen d m ∧ c₂ * (2 * m + 1 + certLen d m + 1) ≤ clock d m := by
  refine ⟨2 * c + 3 * c₂, fun m hm => ⟨?_, ?_⟩⟩
  · have hX : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have e : certLen d m = (m + 1) ^ d * ((m + 1) * (m + 1)) := by
      simp only [certLen]; ring
    rw [e]
    have : 2 * c ≤ (m + 1) * (m + 1) := by nlinarith
    nlinarith
  · have hX : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have e₁ : certLen d m = (m + 1) ^ d * ((m + 1) * (m + 1)) := by
      simp only [certLen]; ring
    have e₂ : clock d m = (m + 1) ^ d * ((m + 1) * (m + 1)) * (m + 1) := by
      simp only [clock]; ring
    rw [e₁, e₂]
    set Y := (m + 1) ^ d * ((m + 1) * (m + 1))
    have hY : 2 * m + 2 ≤ 2 * Y := by
      have h₁ : m + 1 ≤ (m + 1) * (m + 1) := Nat.le_mul_of_pos_left _ (by omega)
      have h₂ : (m + 1) * (m + 1) ≤ Y := Nat.le_mul_of_pos_left _ hX
      omega
    have : c₂ * (2 * m + 1 + Y + 1) ≤ c₂ * (3 * Y) := Nat.mul_le_mul_left _ (by omega)
    nlinarith

/-- **The lazy diagonal is not decidable in nondeterministic time `O((n + 1) ^ d)`.** A
nondeterministic machine deciding it has a verifier on pairs within linear time
(`Cslib.Complexity.exists_verifier_of_mem_NTIME`), described by a word `code`. On the interval of
lengths of `w = frame code ++ pad` with a long enough `pad`, the universal function runs that
verifier exactly. Each word of the interval is then in the language exactly when the next one is,
and the last exactly when the first is not. -/
theorem lazyDiagonal_notMem_NTIME (d : ℕ) :
    lazyDiagonal d ∉ NTIME encBits fun n => (n + 1) ^ d := by
  intro hD
  obtain ⟨V, c, hV, hmem⟩ := exists_verifier_of_mem_NTIME hD
  obtain ⟨c₂, ⟨k, State, hfin, tm, htm⟩, -⟩ := hV
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set code := eDesc (desc eS eBit tm) with hcode
  obtain ⟨M, hM⟩ := exists_le_certLen_clock d c c₂
  -- the universal function runs the verifier exactly on long enough words
  have hsim (y v : List Bool) (hy : M ≤ y.length) (hv : v.length = certLen d y.length) :
      accepts d code y v = V (y, v) := by
    have hclock : c₂ * ((encPair encBits encBits (y, v)).length + 1) ≤ clock d y.length := by
      have := (hM y.length hy).2
      simp only [encPair_apply, encBits_apply, List.length_append, length_frame, hv]
      omega
    obtain ⟨hhalt, hout⟩ := (htm (y, v)).runFrom_of_le hclock
    simp only [encPair_apply, encBits_apply, encBool_apply] at hhalt hout
    rw [accepts, hcode, decodeDesc_eDesc, universal_desc, hout]
    simp only [List.map_cons, List.map_nil, Cfg.Halted] at hhalt ⊢
    rw [hhalt]
    cases V (y, v) <;> simp [Diagonal.verdict, eBit]
  -- on long enough words, membership is acceptance by the simulated verifier
  have hiff (y : List Bool) (hy : M ≤ y.length) : y ∈ lazyDiagonal d ↔
      ∃ v : List Bool, v.length = certLen d y.length ∧ accepts d code y v = true := by
    have h := hmem y (certLen d y.length) (by simpa [encBits_apply] using (hM y.length hy).1)
    rw [h]
    exact exists_congr fun v => and_congr_right fun hv => by rw [hsim y v hy hv]
  -- the interval of `w`
  set w := frame code ++ List.replicate (2 ^ code.length + M) true with hw
  set P := 2 * w.length + 1 with hP
  set E := clock d P with hE
  set x : ℕ → List Bool := fun m => frame w ++ List.replicate (m - P) false with hx
  have hwlen : w.length = 2 * code.length + 1 + (2 ^ code.length + M) := by
    simp [w]
  have hMP : M ≤ P := by
    have := hwlen
    generalize 2 ^ code.length = e at this
    omega
  have hxlen (m : ℕ) (hm : P ≤ m) : (x m).length = m := by
    simp only [x, List.length_append, length_frame, List.length_replicate]
    omega
  have hshort : Diagonal.shortDesc w = true := by
    have hc : unframe w = code := unframe_frame_append _ _
    rw [Diagonal.shortDesc, decide_eq_true_eq, hc, hwlen]
    omega
  have hverifier (m : ℕ) (hm : P ≤ m) (v : List Bool) : verifier d (x m, v) =
      if Nat.size (m + 1) ≤ E then accepts d code (x m ++ [false]) v
      else if Nat.size m ≤ E then
        !(Cslib.BitString.enumList (certLen d P)).any (accepts d code (frame w))
      else false := by
    have hu : unframe (x m) = w := unframe_frame_append _ _
    have hc : unframe w = code := unframe_frame_append _ _
    simp only [verifier, hu, hc, hshort, hxlen m hm, ← hP, ← hE, ↓reduceIte]
  have hPE : P + 1 < 2 ^ E := by
    have : P + 1 ≤ E := by
      simp only [hE, clock]
      exact (Nat.le_self_pow (by omega) _)
    exact this.trans_lt Nat.lt_two_pow_self
  set U := 2 ^ E - 1 with hU
  -- each word below the end of the interval is in the language exactly when the next one is
  have hstep (m : ℕ) (hm : P ≤ m) (hmU : m < U) :
      x m ∈ lazyDiagonal d ↔ x (m + 1) ∈ lazyDiagonal d := by
    have hsize : Nat.size (m + 1) ≤ E := Nat.size_le.mpr (by omega)
    have hnext : x m ++ [false] = x (m + 1) := by
      simp only [x, List.append_assoc, ← List.replicate_succ']
      congr 2
      omega
    rw [hiff (x (m + 1)) (by rw [hxlen _ (by omega)]; omega), lazyDiagonal, Set.mem_ofPred_eq,
      hxlen (m + 1) (by omega), hxlen m hm]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    simp only [hverifier m hm v, hsize, ↓reduceIte, hnext]
  -- the end of the interval is in the language exactly when its start is not
  have hend : x U ∈ lazyDiagonal d ↔ x P ∉ lazyDiagonal d := by
    have hUP : P ≤ U := by omega
    have hsize₁ : ¬Nat.size (U + 1) ≤ E := by
      rw [Nat.size_le, hU, Nat.sub_add_cancel Nat.one_le_two_pow]
      exact lt_irrefl _
    have hsize₂ : Nat.size U ≤ E := Nat.size_le.mpr (by omega)
    have hbase : x P = frame w := by simp [x]
    rw [hiff (x P) (by rw [hxlen P le_rfl]; omega), hxlen P le_rfl, hbase, lazyDiagonal,
      Set.mem_ofPred_eq]
    simp only [hverifier U hUP, hsize₁, hsize₂, ↓reduceIte, Bool.not_eq_true',
      List.any_eq_false, Cslib.BitString.mem_enumList, not_exists, not_and, Bool.not_eq_true]
    constructor
    · rintro ⟨-, -, h⟩ v hv
      exact h v hv
    · intro h
      exact ⟨List.replicate _ false, List.length_replicate .., h⟩
  -- the chain from the start of the interval to its end
  have hchain (j : ℕ) (hj : j ≤ U - P) : x (U - j) ∈ lazyDiagonal d ↔ x U ∈ lazyDiagonal d := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih (by omega), hstep (U - (j + 1)) (by omega) (by omega)]
      congr! 2
      omega
  have h := hchain (U - P) le_rfl
  rw [Nat.sub_sub_self (by omega), hend] at h
  exact iff_not_self h

/-! ### The lazy diagonal is in nondeterministic polynomial time -/

/-- The bound on the simulation of `Cslib.Complexity.LazyDiagonal.accepts`, for a decoder of
degree below `D`. -/
private def accBound (d D : ℕ) (q : List Bool × List Bool × List Bool) : ℕ :=
  ((q.1.length + 1) ^ D + q.2.1.length + q.2.2.length + 1) ^ 4 * (q.2.1.length + 1) ^ (2 * d + 6)

/-- The binary length of the clock is linear in the length of the input. -/
private theorem length_encNat_clock_le (d y : ℕ) :
    (encNat ((y + 1) ^ (d + 3))).length ≤ (d + 3) * (y + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le, mul_comm, pow_mul]
  exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)

/-- The numeric core of the resources of the simulation: for an encoded input of length `N`, a
decoding time `A`, a word `W = frame y ++ v`, a decoded description of encoded length `Dl`, encoded
symbols of length `Nl`, a clock `Y` of `Ll` binary digits and a result of encoded length `E`,
everything is within `K * X ^ 4 * Y ^ 2`. -/
private theorem accBound_aux (d cD cO : ℕ) : ∃ K, ∀ {N A W Dl Nl Ll X Y E : ℕ},
    N ≤ 2 * X → A ≤ X → W ≤ 2 * X → Dl ≤ cD * (N + A + 1) → Nl ≤ 3 * W →
    Ll ≤ (d + 4) * X → 1 ≤ X → 1 ≤ Y →
    E ≤ cO * (N + A + (N + W + (N + Y)) + (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 2 * (Y + 1) + 1) →
    N + A + (N + W + (N + Y)) + (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 4 * (Y + 1) ^ 2 +
        (E + 1) ^ 2 + 1 ≤ K * (X ^ 4 * Y ^ 2) ∧
      N + A + (N + W + (N + Y)) + (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 2 * (Y + 1) + E + 1 ≤
        K * (X ^ 4 * Y ^ 2) := by
  set C₁ := 8 * cD + d + 19
  set C₂ := 11 + 2 * C₁ ^ 2
  refine ⟨10 + 4 * C₁ ^ 4 + (cO * C₂ + 1) ^ 2 + 1 + C₂ * (cO + 1),
    fun {N A W Dl Nl Ll X Y E} hN hA hW hD hNl hLl hX hY hE => ?_⟩
  have hIn : 2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1 ≤ C₁ * X := by
    have h₁ : cD * (N + A + 1) ≤ cD * (4 * X) := Nat.mul_le_mul_left _ (by omega)
    have h₂ : (d + 4) * X = d * X + 4 * X := by ring
    have h₃ : d * X ≤ d * X := le_rfl
    have e : C₁ * X = 8 * (cD * X) + d * X + 19 * X := by simp only [C₁]; ring
    have e' : cD * (4 * X) = 4 * (cD * X) := by ring
    omega
  have hXY : X * Y ≤ X ^ 2 * Y := Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
  have hX2Y : X ^ 2 * Y ≤ X ^ 4 * Y ^ 2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hX (by norm_num)) (Nat.le_self_pow (by norm_num) _)
  have hpre : N + A + (N + W + (N + Y)) ≤ 10 * (X * Y) := by
    have h₁ : X ≤ X * Y := Nat.le_mul_of_pos_right _ hY
    have h₂ : Y ≤ X * Y := Nat.le_mul_of_pos_left _ hX
    omega
  have hY1 : Y + 1 ≤ 2 * Y := by omega
  have hU₂ : (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 2 * (Y + 1) ≤ 2 * C₁ ^ 2 * (X ^ 2 * Y) :=
    calc _ ≤ (C₁ * X) ^ 2 * (2 * Y) := Nat.mul_le_mul (Nat.pow_le_pow_left hIn 2) hY1
      _ = 2 * C₁ ^ 2 * (X ^ 2 * Y) := by ring
  have hU₄ : (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 4 * (Y + 1) ^ 2 ≤
      4 * C₁ ^ 4 * (X ^ 4 * Y ^ 2) :=
    calc _ ≤ (C₁ * X) ^ 4 * (2 * Y) ^ 2 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hIn 4) (Nat.pow_le_pow_left hY1 2)
      _ = 4 * C₁ ^ 4 * (X ^ 4 * Y ^ 2) := by ring
  have hS : N + A + (N + W + (N + Y)) + (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 2 * (Y + 1) + 1 ≤
      C₂ * (X ^ 2 * Y) := by
    have h₁ : 1 ≤ X ^ 2 * Y := Nat.mul_pos (Nat.pow_pos hX) hY
    have e : C₂ * (X ^ 2 * Y) = 11 * (X ^ 2 * Y) + 2 * C₁ ^ 2 * (X ^ 2 * Y) := by
      simp only [C₂]; ring
    omega
  have hE' : E ≤ cO * C₂ * (X ^ 2 * Y) :=
    hE.trans ((Nat.mul_le_mul_left cO hS).trans_eq (by ring))
  have hE2 : (E + 1) ^ 2 ≤ (cO * C₂ + 1) ^ 2 * (X ^ 4 * Y ^ 2) := by
    have h₁ : 1 ≤ X ^ 2 * Y := Nat.mul_pos (Nat.pow_pos hX) hY
    have h₂ : E + 1 ≤ (cO * C₂ + 1) * (X ^ 2 * Y) := by
      have e : (cO * C₂ + 1) * (X ^ 2 * Y) = cO * C₂ * (X ^ 2 * Y) + X ^ 2 * Y := by ring
      omega
    calc (E + 1) ^ 2 ≤ ((cO * C₂ + 1) * (X ^ 2 * Y)) ^ 2 := Nat.pow_le_pow_left h₂ 2
      _ = (cO * C₂ + 1) ^ 2 * (X ^ 4 * Y ^ 2) := by ring
  have h1 : 1 ≤ X ^ 4 * Y ^ 2 := Nat.mul_pos (Nat.pow_pos hX) (Nat.pow_pos hY)
  have hXYW : X * Y ≤ X ^ 4 * Y ^ 2 := hXY.trans hX2Y
  have hU₂' := hU₂.trans (Nat.mul_le_mul_left (2 * C₁ ^ 2) hX2Y)
  constructor
  · have e : (10 + 4 * C₁ ^ 4 + (cO * C₂ + 1) ^ 2 + 1 + C₂ * (cO + 1)) * (X ^ 4 * Y ^ 2) =
        10 * (X ^ 4 * Y ^ 2) + 4 * C₁ ^ 4 * (X ^ 4 * Y ^ 2) +
          (cO * C₂ + 1) ^ 2 * (X ^ 4 * Y ^ 2) + X ^ 4 * Y ^ 2 +
            C₂ * (cO + 1) * (X ^ 4 * Y ^ 2) := by
      ring
    have := Nat.mul_le_mul_left 10 hXYW
    omega
  · have e : (10 + 4 * C₁ ^ 4 + (cO * C₂ + 1) ^ 2 + 1 + C₂ * (cO + 1)) * (X ^ 4 * Y ^ 2) =
        10 * (X ^ 4 * Y ^ 2) + 4 * C₁ ^ 4 * (X ^ 4 * Y ^ 2) +
          (cO * C₂ + 1) ^ 2 * (X ^ 4 * Y ^ 2) + X ^ 4 * Y ^ 2 +
            (C₂ * (X ^ 4 * Y ^ 2) + cO * C₂ * (X ^ 4 * Y ^ 2)) := by
      ring
    have h₁ := Nat.mul_le_mul_left C₂ hX2Y
    have h₂ := Nat.mul_le_mul_left (cO * C₂) hX2Y
    omega

/-- The simulation runs within time polynomial in the description, the input and the
certificate. -/
private theorem exists_computableInO_accepts (d : ℕ) : ∃ D, ComputableInO
    (fun q : List Bool × List Bool × List Bool => accepts d q.1 q.2.1 q.2.2)
    (encPair encBits (encPair encBits encBits)) encBool (accBound d D) (accBound d D) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  set enc := encPair encBits (encPair encBits encBits)
  have hdesc := hdec.inO.comp (ComputableInO.fst encBits (encPair encBits encBits))
  have hword : ComputableInO (fun q : List Bool × List Bool × List Bool => frame q.2.1 ++ q.2.2)
      enc encBits (fun q => (enc q).length) (fun q => (enc q).length) :=
    (ComputableInO.snd encBits (encPair encBits encBits)).of_enc_eq fun _ => rfl
  have hsym := Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO.comp hword
  have hy := (ComputableInO.snd encBits (encPair encBits encBits)).fst'
  have hclock := (timeConstructible_succ_pow (k := d + 3) (by omega)).computableInO.comp hy
  have hU := computableInO_universal.comp (hdesc.prod (hsym.prod hclock))
  have hv := Diagonal.computableInO_verdict.comp hU
  have hnot := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp hv
  obtain ⟨cD, hcD⟩ := hdesc.length_le
  obtain ⟨cO, hcO⟩ := hU.length_le
  obtain ⟨K, hK⟩ := accBound_aux d cD cO
  have hbounds (q : List Bool × List Bool × List Bool) := by
    have hD := hcD q
    have hE := hcO q
    have hNl : (encList encUnary ((frame q.2.1 ++ q.2.2).map eBit)).length ≤
        3 * (frame q.2.1 ++ q.2.2).length :=
      (length_encList_le encUnary _ (b := 1) fun s hs => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
        cases b
        · exact Nat.zero_le _
        · exact le_rfl).trans (by rw [List.length_map]; omega)
    have hc : q.1.length + 1 ≤ (q.1.length + 1) ^ (dd + 1) :=
      Nat.le_self_pow (by omega) _
    have hA : (q.1.length + 1) ^ dd ≤ (q.1.length + 1) ^ (dd + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hL := length_encNat_clock_le d q.2.1.length
    simp only [Function.comp_apply, encBits_apply, enc, length_encPair, List.length_append,
      length_frame] at hD hE hNl ⊢
    refine hK (X := (q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1)
      (by omega) (by omega) (by omega) hD hNl ?_ (by omega) (Nat.one_le_pow _ _ (by omega)) hE
    have : (d + 3) * (q.2.1.length + 1) ≤ (d + 4) * (q.2.1.length + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have : (d + 4) * (q.2.1.length + 1) ≤
        (d + 4) * ((q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have e (q : List Bool × List Bool × List Bool) : accBound d (dd + 1) q =
      ((q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1) ^ 4 *
        ((q.2.1.length + 1) ^ (d + 3)) ^ 2 := by
    rw [accBound, ← pow_mul, show (d + 3) * 2 = 2 * d + 6 by ring]
  have hb (b : Bool) : (encBool b).length = 1 := rfl
  refine ⟨dd + 1, (hnot.mono K (fun q => ?_) fun q => ?_).of_enc_eq fun q => rfl⟩
  · refine le_trans ?_ (Nat.mul_le_mul_left K (Nat.le_succ _))
    rw [e]
    have h := (hbounds q).1
    simp only [Function.comp_apply, encBits_apply, enc, length_encPair, List.length_append,
      length_frame] at ⊢
    simp only [hb] at h ⊢
    omega
  · refine le_trans ?_ (Nat.mul_le_mul_left K (Nat.le_succ _))
    rw [e]
    have h := (hbounds q).2
    simp only [Function.comp_apply, encBits_apply, enc, length_encPair, List.length_append,
      length_frame] at ⊢
    simp only [hb] at h ⊢
    omega

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' in
/-- The brute force at the end of an interval runs within time exponential in the description,
the input and the certificate length. -/
private theorem exists_computableInO_brute (d : ℕ) : ∃ K, ComputableInO
    (fun q : List Bool × List Bool =>
      (Cslib.BitString.enumList (certLen d q.2.length)).any (accepts d q.1 q.2))
    (encPair encBits encBits) encBool
    (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen d q.2.length)))
    (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen d q.2.length))) := by
  obtain ⟨D, hacc⟩ := exists_computableInO_accepts d
  set enc := encPair (encPair encBits encBits) encBits
  have hre := ((ComputableInO.fst (encPair encBits encBits) encBits).fst').prod
    (((ComputableInO.fst (encPair encBits encBits) encBits).snd').prod
      (ComputableInO.snd (encPair encBits encBits) encBits))
  have hf := hacc.comp hre
  have hsize (q : (List Bool × List Bool) × List Bool) :
      q.1.1.length ≤ (enc q).length ∧ q.1.2.length ≤ (enc q).length ∧
        q.2.length ≤ (enc q).length := by
    simp only [enc, length_encPair, encBits_apply]
    omega
  have hpoly : PolyBounded (fun q => (enc q).length) fun q =>
      (enc q).length + ((enc q).length + (enc q).length) +
        accBound d D (q.1.1, q.1.2, q.2) :=
    ((PolyBounded.self.add (PolyBounded.self.add .self)).add
      ((PolyBounded.of_polynomiallyBounded (fun q => (enc q).length)
        (bound := fun n => ((n + 1) ^ D + n + n + 1) ^ 4 * (n + 1) ^ (2 * d + 6))
        (by fun_prop)).mono fun q => by
          obtain ⟨h₁, h₂, h₃⟩ := hsize q
          simp only [accBound]
          gcongr))
  have hℓ : ComputableInPolyTime (fun q : List Bool × List Bool => certLen d q.2.length)
      (encPair encBits encBits) encUnary := by
    unfold certLen
    fun_prop
  exact exists_computableInO_any_enumList hf hpoly hpoly hℓ

/-- The cost of the tests of the verifier: quadratic in the encoded input, times a power of the
length of the input that pays for the clock in unary. -/
private def cheap (d : ℕ) (p : List Bool × List Bool) : ℕ :=
  ((encPair encBits encBits p).length + 1) ^ 2 * ((p.1.length + 1) ^ (d + 3)) ^ 2

/-- The numeric facts behind `cheap`, for an encoded input of length `N`, an input of length `n`
and a clock `Z` of at most `G * Y`. -/
private theorem cheap_aux (G : ℕ) {N n Z Y : ℕ} (hn : n ≤ N) (hY : 1 ≤ Y) (hZ : Z ≤ G * Y) :
    N + 1 ≤ (N + 1) ^ 2 * Y ^ 2 ∧ (Z + 1) ^ 2 ≤ (G + 4) ^ 2 * ((N + 1) ^ 2 * Y ^ 2) ∧
      (2 * N + 4 + Z) ^ 2 ≤ (G + 4) ^ 2 * ((N + 1) ^ 2 * Y ^ 2) := by
  have hY2 : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ hY
  have hN2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq : (2 * N + 4 + Z) ^ 2 ≤ (G + 4) ^ 2 * ((N + 1) ^ 2 * Y ^ 2) :=
    calc (2 * N + 4 + Z) ^ 2 ≤ ((G + 4) * ((N + 1) * Y)) ^ 2 := by
          apply Nat.pow_le_pow_left
          have h₁ : N + 1 ≤ (N + 1) * Y := Nat.le_mul_of_pos_right _ hY
          have h₂ : Y ≤ (N + 1) * Y := Nat.le_mul_of_pos_left _ (by omega)
          have e : (G + 4) * ((N + 1) * Y) = G * ((N + 1) * Y) + 4 * ((N + 1) * Y) := by ring
          have := Nat.mul_le_mul_left G h₂
          omega
      _ = (G + 4) ^ 2 * ((N + 1) ^ 2 * Y ^ 2) := by ring
  refine ⟨hN2.trans (Nat.le_mul_of_pos_right _ hY2),
    (Nat.pow_le_pow_left (by omega) 2).trans hsq, hsq⟩

/-- **The verifier of the lazy diagonal is computable**, within the cost of its tests plus the
cost of the branch taken: the simulation, or the brute force at the end of an interval. -/
private theorem exists_computableInO_verifier (d : ℕ) :
    ∃ (D K : ℕ) (S : List Bool × List Bool → ℕ),
    ComputableInO (verifier d) (encPair encBits encBits) encBool
      (fun p => cheap d p + if Diagonal.shortDesc (unframe p.1) then
        (cheap d p + if Nat.size (p.1.length + 1) ≤ clock d (2 * (unframe p.1).length + 1) then
          cheap d p + accBound d D (unframe (unframe p.1), p.1 ++ [false], p.2)
        else (cheap d p + if Nat.size p.1.length ≤ clock d (2 * (unframe p.1).length + 1) then
          cheap d p + 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
            frame (unframe p.1))).length + certLen d (2 * (unframe p.1).length + 1)))
          else cheap d p))
        else cheap d p) S := by
  obtain ⟨D, hacc⟩ := exists_computableInO_accepts d
  obtain ⟨K, hbrute⟩ := exists_computableInO_brute d
  have hx := ComputableInO.fst encBits encBits
  have hun : ComputableInO unframe encBits encBits (fun z => z.length) (fun z => z.length) :=
    ComputableInO.of_linear (.of_unframe fun _ => rfl)
  have hfr : ComputableInO frame encBits encBits (fun z => z.length) (fun z => z.length) :=
    ComputableInO.of_linear (.of_frame fun _ => rfl)
  have hw := hun.comp hx
  have hcode := hun.comp hw
  have hbase := hfr.comp hw
  have hsnoc : ComputableInO (fun p : List Bool × List Bool => p.1 ++ [false])
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length) :=
    hx.append (ComputableInO.const (encMid := encBits) [false]) fun _ => rfl
  have hsz : ComputableInO (fun z : List Bool => Nat.size z.length) encBits encUnary
      (fun z => (z.length + 1) ^ 2 + (encNat z.length).length)
      (fun z => z.length + 1 + (encNat z.length).length) :=
    (ComputableInO.lengthUnary.comp (ComputableInO.lengthNat.of_enc_eq (encC := encBits)
      (g := fun z : List Bool => encNat z.length) fun _ => rfl)).of_enc_eq fun z => by
        simp [encNat_apply, Nat.size_eq_bits_len]
  have hE := ComputableInO.natToUnary.comp
    ((timeConstructible_succ_pow (k := d + 3) (by omega)).computableInO.comp hbase)
  -- the numeric facts about the tests
  set G := 2 ^ (d + 3)
  have hfacts (p : List Bool × List Bool) : (unframe p.1).length ≤ p.1.length ∧
      p.1.length ≤ (encPair encBits encBits p).length ∧
      (encPair encBits encBits p).length + 1 ≤ cheap d p ∧
      ((2 * (unframe p.1).length + 1 + 1) ^ (d + 3) + 1) ^ 2 ≤ (G + 4) ^ 2 * cheap d p ∧
      (2 * (encPair encBits encBits p).length + 4 +
        (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 ≤ (G + 4) ^ 2 * cheap d p := by
    have hu := length_unframe_le p.1
    have hn : p.1.length ≤ (encPair encBits encBits p).length := by
      simp only [length_encPair, encBits_apply]
      omega
    have hZ : (2 * (unframe p.1).length + 1 + 1) ^ (d + 3) ≤
        2 ^ (d + 3) * (p.1.length + 1) ^ (d + 3) := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by omega) _
    exact ⟨hu, hn, cheap_aux G hn (Nat.one_le_pow _ _ (by omega)) hZ⟩
  have e (p : List Bool × List Bool) : (8 + 4 * (G + 4) ^ 2) * (cheap d p + 1) =
      8 * cheap d p + 4 * ((G + 4) ^ 2 * cheap d p) + (8 + 4 * (G + 4) ^ 2) := by ring
  have hc₀ := (Diagonal.computableInO_shortDesc.comp hw).mono_time (T' := cheap d)
      (8 + 4 * (G + 4) ^ 2) fun p => by
    obtain ⟨hu, hn, h₁, -, h₃⟩ := hfacts p
    have : ((unframe p.1).length + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [Function.comp_apply] at ⊢
    have := e p
    omega
  have hc₁ := (ComputableInO.unaryLe.comp ((hsz.comp hsnoc).prod hE)).mono_time
      (T' := cheap d) (8 + 4 * (G + 4) ^ 2) fun p => by
    obtain ⟨hu, hn, h₁, h₂, h₃⟩ := hfacts p
    have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.1.length + 1))
    have he := Universal.length_encNat_le (p.1.length + 1)
    have hsq : (p.1.length + 1 + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : (2 * Nat.size (p.1.length + 1) + 1 + (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)
        + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
          (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hZ : (2 * (unframe p.1).length + 1 + 1) ^ (d + 3) ≤
        ((2 * (unframe p.1).length + 1 + 1) ^ (d + 3) + 1) ^ 2 := by
      nlinarith [Nat.le_self_pow (n := 2) (by norm_num)
        ((2 * (unframe p.1).length + 1 + 1) ^ (d + 3) + 1)]
    simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
      encUnary_apply, List.length_replicate, List.length_append, List.length_singleton,
      length_frame] at ⊢
    have := e p
    omega
  have hc₂ := (ComputableInO.unaryLe.comp ((hsz.comp hx).prod hE)).mono_time
      (T' := cheap d) (8 + 4 * (G + 4) ^ 2) fun p => by
    obtain ⟨hu, hn, h₁, h₂, h₃⟩ := hfacts p
    have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.1.length))
    have he := Universal.length_encNat_le p.1.length
    have hsq : (p.1.length + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : (2 * Nat.size p.1.length + 1 + (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)
        + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
          (2 * (unframe p.1).length + 1 + 1) ^ (d + 3)) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hZ : (2 * (unframe p.1).length + 1 + 1) ^ (d + 3) ≤
        ((2 * (unframe p.1).length + 1 + 1) ^ (d + 3) + 1) ^ 2 := by
      nlinarith [Nat.le_self_pow (n := 2) (by norm_num)
        ((2 * (unframe p.1).length + 1 + 1) ^ (d + 3) + 1)]
    simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
      encUnary_apply, List.length_replicate, length_frame] at ⊢
    have := e p
    omega
  have hc₁' := hc₁.of_enc_eq (encC := encBool) (g := fun p : List Bool × List Bool =>
      decide (Nat.size (p.1.length + 1) ≤ clock d (2 * (unframe p.1).length + 1))) fun p => by
    simp only [Function.comp_apply, clock, length_frame, List.length_append,
      List.length_singleton]
    rfl
  have hc₂' := hc₂.of_enc_eq (encC := encBool) (g := fun p : List Bool × List Bool =>
      decide (Nat.size p.1.length ≤ clock d (2 * (unframe p.1).length + 1))) fun p => by
    simp only [Function.comp_apply, clock, length_frame]
    rfl
  have hf₁ := (hacc.comp (hcode.prod (hsnoc.prod (ComputableInO.snd encBits encBits)))).mono_time
      (T' := fun p => cheap d p + accBound d D (unframe (unframe p.1), p.1 ++ [false], p.2)) 7
      fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    simp only [Function.comp_apply] at ⊢
    have e : 7 * (cheap d p + accBound d D (unframe (unframe p.1), p.1 ++ [false], p.2) + 1) =
        7 * cheap d p + 7 * accBound d D (unframe (unframe p.1), p.1 ++ [false], p.2) + 7 := by
      ring
    omega
  have hf₂ := ((ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp (hbrute.comp (hcode.prod hbase))).mono_time
      (T' := fun p => cheap d p + 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
        frame (unframe p.1))).length + certLen d (2 * (unframe p.1).length + 1)))) 7
      fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    have hb : (encBool ((Cslib.BitString.enumList (certLen d (frame (unframe p.1)).length)).any
        (accepts d (unframe (unframe p.1)) (frame (unframe p.1))))).length = 1 := rfl
    simp only [Function.comp_apply, hb] at ⊢
    rw [length_frame]
    set B := 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
        frame (unframe p.1))).length + certLen d (2 * (unframe p.1).length + 1)))
    have e : 7 * (cheap d p + B + 1) = 7 * cheap d p + 7 * B + 7 := by ring
    omega
  have hfalse := (ComputableInO.const (encIn := encPair encBits encBits) (encMid := encBool)
    false).mono_time (T' := cheap d) 1 fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    omega
  have h := hc₀.ite (hc₁'.ite hf₁ (hc₂'.ite hf₂ hfalse)) hfalse
  refine ⟨D, K, _, (h.of_enc_eq fun p => ?_).mono_le (fun p => le_of_eq ?_) fun p => le_rfl⟩
  · congr 1
    simp only [verifier, Function.comp_apply, decide_eq_true_eq, length_frame]
  · simp only [Function.comp_apply, decide_eq_true_eq]

/-- **The lazy diagonal is decidable in nondeterministic time `O((n + 1) ^ (6 * d + 14))`.** Guess
a certificate of length `(n + 2) ^ (d + 2)` and run the verifier
(`Cslib.Complexity.setOf_exists_mem_NTIME`). Below the end of an interval, the verifier simulates
a verifier on the input one bit longer with a certificate of that length, within time polynomial
in both. At the end of an interval of start `P`, it tries every certificate on the input of
length `P`, within time `2 ^ O((P + 1) ^ (d + 2))`, which is linear in the length `n` of the
input, since `n + 1 = 2 ^ ((P + 1) ^ (d + 3))` there. -/
theorem lazyDiagonal_mem_NTIME (d : ℕ) :
    lazyDiagonal d ∈ NTIME encBits fun n => (n + 1) ^ (6 * d + 14) := by
  obtain ⟨D, K, S, hV⟩ := exists_computableInO_verifier d
  have hsnoc : ComputableInO (fun x : List Bool => x ++ [false]) encBits encBits
      (fun x => x.length + x.length) (fun x => x.length + x.length) :=
    (ComputableInO.of_eq (f := fun x : List Bool => x) (encIn := encBits) (encMid := encBits)
      fun _ => rfl).append (ComputableInO.const (encMid := encBits) [false]) fun _ => rfl
  have hℓ := (ComputableInO.natToUnary.comp
    ((timeConstructible_succ_pow (k := d + 2) (by omega)).computableInO.comp hsnoc)).of_enc_eq
      (encC := encUnary) (g := fun x : List Bool => certLen d (x.length + 1)) fun x => by
    simp [certLen]
  obtain ⟨CD, hCD⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun m => (m + 1) ^ D)
    (by fun_prop)
  set B₀ := 3 * K * (3 * K) ^ (d + 2)
  set A₁ := 9 * 2 ^ (2 * d + 4)
  set A₂ := (CD + 3) ^ 4 * 2 ^ (6 * d + 14)
  set A₃ := 7 * 2 ^ (2 * d + 4)
  refine setOf_exists_mem_NTIME hℓ hV (C := 2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀) fun x v hv => ?_
  simp only [encBits_apply]
  set n := x.length with hn
  have hv' : v.length = (n + 2) ^ (d + 2) := by
    rw [hv]
    rfl
  set M := (n + 1) ^ (6 * d + 14)
  have h2 (k : ℕ) : (n + 2) ^ k ≤ 2 ^ k * (n + 1) ^ k := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) k
  have hMk (k : ℕ) (hk : k ≤ 6 * d + 14) : (n + 1) ^ k ≤ M := Nat.pow_le_pow_right (by omega) hk
  have hnM : n + 1 ≤ M := by simpa using hMk 1 (by omega)
  -- the tests
  have hcheap : cheap d (x, v) ≤ A₁ * M := by
    have hN : (encPair encBits encBits (x, v)).length + 1 ≤ 3 * (n + 2) ^ (d + 2) := by
      simp only [length_encPair, encBits_apply, hv']
      have : n + 2 ≤ (n + 2) ^ (d + 2) := Nat.le_self_pow (by omega) _
      omega
    calc cheap d (x, v) = ((encPair encBits encBits (x, v)).length + 1) ^ 2 *
          ((n + 1) ^ (d + 3)) ^ 2 := rfl
      _ ≤ (3 * (n + 2) ^ (d + 2)) ^ 2 * ((n + 1) ^ (d + 3)) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 2)
      _ = 9 * (n + 2) ^ (2 * d + 4) * (n + 1) ^ (2 * d + 6) := by ring
      _ ≤ 9 * (2 ^ (2 * d + 4) * (n + 1) ^ (2 * d + 4)) * (n + 1) ^ (2 * d + 6) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (h2 _))
      _ = A₁ * (n + 1) ^ (4 * d + 10) := by ring
      _ ≤ A₁ * M := Nat.mul_le_mul_left _ (hMk _ (by omega))
  -- the simulation, when the description is short
  have hacc (h₀ : Diagonal.shortDesc (unframe x) = true) :
      accBound d D (unframe (unframe x), x ++ [false], v) ≤ A₂ * M := by
    have hs : 2 ^ (unframe (unframe x)).length ≤ (unframe x).length := of_decide_eq_true h₀
    have hu := length_unframe_le x
    have hD : ((unframe (unframe x)).length + 1) ^ D ≤ CD * n :=
      (hCD _).trans (Nat.mul_le_mul_left _ (hs.trans hu))
    have hb : ((unframe (unframe x)).length + 1) ^ D + (n + 1) + (n + 2) ^ (d + 2) + 1 ≤
        (CD + 3) * (n + 2) ^ (d + 2) := by
      have h₁ : n + 2 ≤ (n + 2) ^ (d + 2) := Nat.le_self_pow (by omega) _
      have h₂ : CD * n ≤ CD * (n + 2) ^ (d + 2) := Nat.mul_le_mul_left _ (by omega)
      have e : (CD + 3) * (n + 2) ^ (d + 2) = CD * (n + 2) ^ (d + 2) + 3 * (n + 2) ^ (d + 2) := by
        ring
      omega
    calc accBound d D (unframe (unframe x), x ++ [false], v) =
          (((unframe (unframe x)).length + 1) ^ D + (n + 1) + (n + 2) ^ (d + 2) + 1) ^ 4 *
            (n + 2) ^ (2 * d + 6) := by
          simp only [accBound, List.length_append, List.length_singleton, hv', ← hn, add_assoc,
            Nat.reduceAdd]
      _ ≤ ((CD + 3) * (n + 2) ^ (d + 2)) ^ 4 * (n + 2) ^ (2 * d + 6) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hb 4)
      _ = (CD + 3) ^ 4 * (n + 2) ^ (6 * d + 14) := by ring
      _ ≤ (CD + 3) ^ 4 * (2 ^ (6 * d + 14) * M) := Nat.mul_le_mul_left _ (h2 _)
      _ = A₂ * M := by ring
  -- the brute force, at the end of an interval
  have hbrute (h₁ : ¬Nat.size (n + 1) ≤ clock d (2 * (unframe x).length + 1)) :
      2 ^ (K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen d (2 * (unframe x).length + 1))) ≤ n + 1 + 2 ^ B₀ := by
    set P := 2 * (unframe x).length + 1 with hP
    have hE : 2 ^ clock d P ≤ n + 1 := by
      rw [Nat.size_le, not_lt] at h₁
      exact h₁
    have hc := length_unframe_le (unframe x)
    have hlen : (encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen d P ≤ 3 * (P + 1) ^ (d + 2) := by
      simp only [length_encPair, encBits_apply, length_frame, certLen]
      have : P + 1 ≤ (P + 1) ^ (d + 2) := Nat.le_self_pow (by omega) _
      omega
    rcases le_or_gt (3 * K) (P + 1) with hK | hK
    · have hle : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
          certLen d P) ≤ clock d P :=
        calc _ ≤ K * (3 * (P + 1) ^ (d + 2)) := Nat.mul_le_mul_left _ hlen
          _ = 3 * K * (P + 1) ^ (d + 2) := by ring
          _ ≤ (P + 1) * (P + 1) ^ (d + 2) := Nat.mul_le_mul_right _ hK
          _ = clock d P := by rw [clock]; ring
      exact ((Nat.pow_le_pow_right (by norm_num) hle).trans hE).trans (Nat.le_add_right _ _)
    · have hle : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
          certLen d P) ≤ B₀ :=
        calc _ ≤ K * (3 * (P + 1) ^ (d + 2)) := Nat.mul_le_mul_left _ hlen
          _ = 3 * K * (P + 1) ^ (d + 2) := by ring
          _ ≤ 3 * K * (3 * K) ^ (d + 2) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK.le _)
      exact (Nat.pow_le_pow_right (by norm_num) hle).trans (Nat.le_add_left _ _)
  -- the certificate length
  have hTℓ : n + n + ((x ++ [false]).length + 1) ^ (d + 2) +
      (((fun x : List Bool => (x.length + 1) ^ (d + 2)) ∘ fun x => x ++ [false]) x + 1) ^ 2 ≤
        A₃ * M := by
    simp only [Function.comp_apply, List.length_append, List.length_singleton, add_assoc,
      Nat.reduceAdd, ← hn]
    have h₁ : n + 2 ≤ (n + 2) ^ (d + 2) := Nat.le_self_pow (by omega) _
    have h₂ : ((n + 2) ^ (d + 2) + 1) ^ 2 ≤ 4 * (n + 2) ^ (2 * d + 4) := by
      calc _ ≤ (2 * (n + 2) ^ (d + 2)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * (n + 2) ^ (2 * d + 4) := by ring
    have h₃ : (n + 2) ^ (d + 2) ≤ (n + 2) ^ (2 * d + 4) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h₄ : 7 * (n + 2) ^ (2 * d + 4) ≤ A₃ * M :=
      calc _ ≤ 7 * (2 ^ (2 * d + 4) * (n + 1) ^ (2 * d + 4)) := Nat.mul_le_mul_left _ (h2 _)
        _ = A₃ * (n + 1) ^ (2 * d + 4) := by ring
        _ ≤ A₃ * M := Nat.mul_le_mul_left _ (hMk _ (by omega))
    omega
  have e : (2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀) * M =
      2 * M + A₃ * M + 4 * (A₁ * M) + A₂ * M + 2 ^ B₀ * M := by ring
  have hB : 2 ^ B₀ ≤ 2 ^ B₀ * M := Nat.le_mul_of_pos_right _ (by omega)
  clear_value M A₁ A₂ A₃ B₀
  generalize 2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀ = C at *
  generalize 2 ^ B₀ = P at *
  split_ifs with h₀ h₁ h₂
  · have := hacc h₀
    omega
  · have := hbrute h₁
    omega
  · omega
  · omega

/-! ### The hierarchy -/

/-- **A nondeterministic time hierarchy for polynomial degrees.** For every degree `d`,
nondeterministic time `O((n + 1) ^ d)` is strictly contained in nondeterministic time
`O((n + 1) ^ e)` whenever `6 * d + 14 ≤ e`. The lazy diagonal `Cslib.Complexity.lazyDiagonal d`
separates them (`Cslib.Complexity.lazyDiagonal_mem_NTIME`,
`Cslib.Complexity.lazyDiagonal_notMem_NTIME`). This is a coarse form of the nondeterministic time
hierarchy theorem [Arora and Barak, Theorem 3.3][AroraBarak07]: the gap is the polynomial
overhead of the native universal machine and of the certificates, not `f (n + 1) = o (g n)`. -/
theorem NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le {d e : ℕ} (h : 6 * d + 14 ≤ e) :
    NTIME encBits (fun n => (n + 1) ^ d) ⊂ NTIME encBits fun n => (n + 1) ^ e := by
  have hsub : ∀ {a b : ℕ}, a ≤ b →
      NTIME encBits (fun n => (n + 1) ^ a) ⊆ NTIME encBits fun n => (n + 1) ^ b :=
    fun hab => NTIME_mono fun n => Nat.pow_le_pow_right (by omega) hab
  exact (Set.ssubset_iff_of_subset (hsub (by omega))).mpr
    ⟨lazyDiagonal d, hsub h (lazyDiagonal_mem_NTIME d), lazyDiagonal_notMem_NTIME d⟩

end Cslib.Complexity

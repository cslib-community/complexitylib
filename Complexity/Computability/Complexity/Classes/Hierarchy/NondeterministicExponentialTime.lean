/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Hierarchy.Time
public import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Computability.Complexity.Classes.Time.BoundedExists
import Complexity.Computability.Complexity.Classes.Time.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# A nondeterministic exponential time hierarchy by lazy diagonalization

For every `k`, nondeterministic time `O(2 ^ (k * n))` is strictly contained in nondeterministic
time `O(2 ^ (e * n))` on bit strings whenever `8 * k + 16 ≤ e`
(`Cslib.Complexity.NTIME_two_pow_ssubset_NTIME_two_pow_of_le`). In particular `NE` is not contained
in `NTIME (2 ^ (k * n))` for any `k` (`Cslib.Complexity.exists_mem_NE_notMem_NTIME_two_pow`). This
is a coarse exponential form of the nondeterministic time hierarchy theorem
[Arora and Barak, Theorem 3.3][AroraBarak07], proved by lazy diagonalization [Žák][Zak1983].
The separating problem is explicit: `Cslib.Complexity.expLazyDiagonal k`.

Padding transfers inclusions between nondeterministic time classes only upward, so the
polynomial hierarchy of `Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le` does not give
this separation; the lazy diagonal is run again with exponential certificates.

## The lazy diagonal

An input `x` carries a word `w` framed at its start, and `w` carries the description
`unframe w` of a deterministic verifier on pairs framed at its start, followed by arbitrary
padding. The interval of `w` consists of the lengths from `P = 2 * w.length + 1`, the length of
`frame w`, to `2 ^ horizon k P - 1`, where `horizon k m = 2 ^ ((k + 2) * (m + 1))`. On the input `x`
of length `n` in this interval, with a certificate `v` of length
`certLen k (n + 1) = 2 ^ ((k + 1) * (n + 2))`, the verifier
`Cslib.Complexity.ExpLazyDiagonal.verifier k`

* below the end of the interval, runs the described verifier on the one bit longer input
  `x ++ [false]` and the certificate `v` with the universal function, for the square of the
  length of the encoded pair (`Cslib.Complexity.ExpLazyDiagonal.accepts`);
* at the end of the interval, accepts when the described verifier accepts no certificate of
  length `certLen k P` on `frame w`, trying them all.

The lazy diagonal is the problem of the inputs with an accepted certificate.

* **Upper bound** (`Cslib.Complexity.expLazyDiagonal_mem_NTIME`). Guess the certificate and run the
  verifier (`Cslib.Complexity.setOf_exists_mem_NTIME`). The simulation takes time polynomial in the
  certificate, `O(2 ^ ((8 * k + 16) * n))`. The brute force takes time `2 ^ O(certLen k P)`
  (`Cslib.Complexity.exists_computableInO_any_enumList`), which is `O(n)` at the end of the
  interval, where `n + 1 = 2 ^ horizon k P` and `horizon k P = 2 ^ (P + 1) * certLen k P`.
* **Lower bound** (`Cslib.Complexity.expLazyDiagonal_notMem_NTIME`). A nondeterministic machine
  deciding the problem within time `O(2 ^ (k * n))` has a deterministic verifier on pairs within
  linear time, accepting certificates of every length at least `c * 2 ^ (k * n) + c`
  (`Cslib.Complexity.exists_verifier_of_mem_NTIME`). On the interval of a word `w` describing that
  verifier, with enough padding, the universal function runs it exactly. Then each input of the
  interval is in the problem exactly when the next one is, and the last exactly when the first is
  not.

Unlike `Cslib.Complexity.lazyDiagonal`, the simulation clock is the square of the length of the
simulated pair rather than a function of the input length alone. It is then polynomial in the
certificate, so the brute force at the end of an interval is a polynomial-time test tried on every
certificate.

## Main definitions

* `Cslib.Complexity.ExpLazyDiagonal.verifier`: the verifier of the lazy diagonal.
* `Cslib.Complexity.expLazyDiagonal`: the exponential lazy diagonal problem for `k`.

## Main results

* `Cslib.Complexity.expLazyDiagonal_mem_NTIME`: the lazy diagonal is in
  `NTIME (2 ^ ((8 * k + 16) * n))`.
* `Cslib.Complexity.expLazyDiagonal_notMem_NTIME`: the lazy diagonal is not in
  `NTIME (2 ^ (k * n))`.
* `Cslib.Complexity.NTIME_two_pow_ssubset_NTIME_two_pow_of_le`: the hierarchy.
* `Cslib.Complexity.exists_mem_NE_notMem_NTIME_two_pow`: `NE ⊄ NTIME (2 ^ (k * n))`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
* [S. Žák, *A Turing machine time hierarchy*][Zak1983]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

namespace ExpLazyDiagonal

/-- The certificate length of the lazy diagonal on words of length `m`:
`2 ^ ((k + 1) * (m + 1))`. -/
def certLen (k m : ℕ) : ℕ := 2 ^ ((k + 1) * (m + 1))

/-- The horizon of the lazy diagonal: the interval of lengths starting at `m` ends below
`2 ^ horizon k m`, where `horizon k m = 2 ^ ((k + 2) * (m + 1)) = 2 ^ (m + 1) * certLen k m`. -/
def horizon (k m : ℕ) : ℕ := 2 ^ ((k + 2) * (m + 1))

/-- The machine described by `c`, run as a verifier on the pair `(y, v)` (encoded as
`frame y ++ v`) with the universal function for `((frame y ++ v).length + 1) ^ 2` steps, has
halted with output `[true]`. -/
def accepts (c y v : List Bool) : Bool :=
  !Diagonal.verdict
    (universal (decodeDesc c, (frame y ++ v).map eBit, ((frame y ++ v).length + 1) ^ 2))

/-- **The verifier of the exponential lazy diagonal**, on an input `x` of length `n` and a
certificate `v`. The input carries a word `w` framed at its start, and `w` carries the description
`unframe w` framed at its start. When the description is short
(`Cslib.Complexity.Diagonal.shortDesc w`), let `P = 2 * w.length + 1`; the lengths from `P` to
`2 ^ horizon k P - 1` form the interval of `w`.

* If `n + 1 < 2 ^ horizon k P`, below the end of the interval, accept when the described verifier
  accepts `v` on the input one bit longer.
* If `n + 1 = 2 ^ horizon k P`, at the end of the interval, accept when the described verifier
  accepts no certificate on `frame w`, the input of length `P`, by trying them all.
* Otherwise, and when the description is not short, reject. -/
def verifier (k : ℕ) (p : List Bool × List Bool) : Bool :=
  if Diagonal.shortDesc (unframe p.1) then
    if Nat.size (p.1.length + 1) ≤ horizon k (2 * (unframe p.1).length + 1) then
      accepts (unframe (unframe p.1)) (p.1 ++ [false]) p.2
    else if Nat.size p.1.length ≤ horizon k (2 * (unframe p.1).length + 1) then
      !(Cslib.BitString.enumList (certLen k (2 * (unframe p.1).length + 1))).any
        (accepts (unframe (unframe p.1)) (frame (unframe p.1)))
    else false
  else false

end ExpLazyDiagonal

open ExpLazyDiagonal

/-- **The exponential lazy diagonal language** for `k`: the words `x` with a certificate of length
`2 ^ ((k + 1) * (x.length + 2))` accepted by `Cslib.Complexity.ExpLazyDiagonal.verifier k`. -/
def expLazyDiagonal (k : ℕ) : Set (List Bool) :=
  {x | ∃ v : List Bool, v.length = certLen k (x.length + 1) ∧ verifier k (x, v) = true}

/-! ### The lazy diagonal is not in `NTIME (2 ^ (k * n))` -/

/-- The lengths at which certificates of length `certLen k m` suffice for a verifier with constant
`c`. -/
private theorem exists_le_certLen (k c : ℕ) :
    ∃ M, ∀ m, M ≤ m → c * 2 ^ (k * m) + c ≤ certLen k m := by
  refine ⟨c, fun m hm => ?_⟩
  have hX : 1 ≤ 2 ^ (k * m) := Nat.one_le_two_pow
  have hc : 2 * c ≤ 2 ^ (m + 1) := by
    have := Nat.lt_two_pow_self (n := m)
    rw [pow_succ]
    omega
  have e : certLen k m = 2 ^ (k * m) * 2 ^ k * 2 ^ (m + 1) := by
    simp only [certLen, ← pow_add]
    congr 1
    ring
  rw [e]
  calc c * 2 ^ (k * m) + c ≤ 2 * c * 2 ^ (k * m) := by nlinarith
    _ ≤ 2 ^ (m + 1) * 2 ^ (k * m) := Nat.mul_le_mul_right _ hc
    _ ≤ 2 ^ (k * m) * 2 ^ k * 2 ^ (m + 1) := by
      rw [mul_comm (2 ^ (m + 1)), mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ Nat.one_le_two_pow)

/-- **The exponential lazy diagonal is not decidable in nondeterministic time
`O(2 ^ (k * n))`.** A nondeterministic machine deciding it has a verifier on pairs within linear
time (`Cslib.Complexity.exists_verifier_of_mem_NTIME`), described by a word `code`. On the interval
of lengths of `w = frame code ++ pad` with a long enough `pad`, the universal function runs that
verifier exactly. Each word of the interval is then in the language exactly when the next one is,
and the last exactly when the first is not. -/
theorem expLazyDiagonal_notMem_NTIME (k : ℕ) :
    expLazyDiagonal k ∉ NTIME encBits fun n => 2 ^ (k * n) := by
  intro hD
  obtain ⟨V, c, hV, hmem⟩ := exists_verifier_of_mem_NTIME hD
  obtain ⟨c₂, ⟨k', State, hfin, tm, htm⟩, -⟩ := hV
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set code := eDesc (desc eS eBit tm) with hcode
  obtain ⟨M₁, hM₁⟩ := exists_le_certLen k c
  set M := M₁ + c₂ with hM
  -- the universal function runs the verifier exactly on long enough words
  have hsim (y v : List Bool) (hy : M ≤ y.length) : accepts code y v = V (y, v) := by
    have hclock : c₂ * ((encPair encBits encBits (y, v)).length + 1) ≤
        ((frame y ++ v).length + 1) ^ 2 := by
      simp only [encPair_apply, encBits_apply, List.length_append, length_frame]
      rw [sq]
      exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨hhalt, hout⟩ := (htm (y, v)).runFrom_of_le hclock
    simp only [encPair_apply, encBits_apply, encBool_apply] at hhalt hout
    rw [accepts, hcode, decodeDesc_eDesc, universal_desc, hout]
    simp only [List.map_cons, List.map_nil, Cfg.Halted] at hhalt ⊢
    rw [hhalt]
    cases V (y, v) <;> simp [Diagonal.verdict, eBit]
  -- on long enough words, membership is acceptance by the simulated verifier
  have hiff (y : List Bool) (hy : M ≤ y.length) : y ∈ expLazyDiagonal k ↔
      ∃ v : List Bool, v.length = certLen k y.length ∧ accepts code y v = true := by
    have h := hmem y (certLen k y.length)
      (by simpa [encBits_apply] using hM₁ y.length (by omega))
    rw [h]
    exact exists_congr fun v => and_congr_right fun _ => by rw [hsim y v hy]
  -- the interval of `w`
  set w := frame code ++ List.replicate (2 ^ code.length + M) true with hw
  set P := 2 * w.length + 1 with hP
  set E := horizon k P with hE
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
  have hverifier (m : ℕ) (hm : P ≤ m) (v : List Bool) : verifier k (x m, v) =
      if Nat.size (m + 1) ≤ E then accepts code (x m ++ [false]) v
      else if Nat.size m ≤ E then
        !(Cslib.BitString.enumList (certLen k P)).any (accepts code (frame w))
      else false := by
    have hu : unframe (x m) = w := unframe_frame_append _ _
    have hc : unframe w = code := unframe_frame_append _ _
    simp only [verifier, hu, hc, hshort, hxlen m hm, ← hP, ← hE, ↓reduceIte]
  have hPE : P + 1 < 2 ^ E := by
    have : P + 1 ≤ E :=
      calc P + 1 ≤ 2 ^ (P + 1) := Nat.lt_two_pow_self.le
        _ ≤ E := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
    exact this.trans_lt Nat.lt_two_pow_self
  set U := 2 ^ E - 1 with hU
  -- each word below the end of the interval is in the language exactly when the next one is
  have hstep (m : ℕ) (hm : P ≤ m) (hmU : m < U) :
      x m ∈ expLazyDiagonal k ↔ x (m + 1) ∈ expLazyDiagonal k := by
    have hsize : Nat.size (m + 1) ≤ E := Nat.size_le.mpr (by omega)
    have hnext : x m ++ [false] = x (m + 1) := by
      simp only [x, List.append_assoc, ← List.replicate_succ']
      congr 2
      omega
    rw [hiff (x (m + 1)) (by rw [hxlen _ (by omega)]; omega), expLazyDiagonal, Set.mem_ofPred_eq,
      hxlen (m + 1) (by omega), hxlen m hm]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    simp only [hverifier m hm v, hsize, ↓reduceIte, hnext]
  -- the end of the interval is in the language exactly when its start is not
  have hend : x U ∈ expLazyDiagonal k ↔ x P ∉ expLazyDiagonal k := by
    have hUP : P ≤ U := by omega
    have hsize₁ : ¬Nat.size (U + 1) ≤ E := by
      rw [Nat.size_le, hU, Nat.sub_add_cancel Nat.one_le_two_pow]
      exact lt_irrefl _
    have hsize₂ : Nat.size U ≤ E := Nat.size_le.mpr (by omega)
    have hbase : x P = frame w := by simp [x]
    rw [hiff (x P) (by rw [hxlen P le_rfl]; omega), hxlen P le_rfl, hbase, expLazyDiagonal,
      Set.mem_ofPred_eq]
    simp only [hverifier U hUP, hsize₁, hsize₂, ↓reduceIte, Bool.not_eq_true',
      List.any_eq_false, Cslib.BitString.mem_enumList, not_exists, not_and, Bool.not_eq_true]
    constructor
    · rintro ⟨-, -, h⟩ v hv
      exact h v hv
    · intro h
      exact ⟨List.replicate _ false, List.length_replicate .., h⟩
  -- the chain from the start of the interval to its end
  have hchain (j : ℕ) (hj : j ≤ U - P) :
      x (U - j) ∈ expLazyDiagonal k ↔ x U ∈ expLazyDiagonal k := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih (by omega), hstep (U - (j + 1)) (by omega) (by omega)]
      congr! 2
      omega
  have h := hchain (U - P) le_rfl
  rw [Nat.sub_sub_self (by omega), hend] at h
  exact iff_not_self h

/-! ### The lazy diagonal is in nondeterministic exponential time -/

/-- The bound on the simulation of `Cslib.Complexity.ExpLazyDiagonal.accepts`, for a decoder of
degree below `D`: polynomial in the description, the input and the certificate. -/
private def accBound (D : ℕ) (q : List Bool × List Bool × List Bool) : ℕ :=
  ((q.1.length + 1) ^ D + q.2.1.length + q.2.2.length + 1) ^ 4 *
    ((frame q.2.1 ++ q.2.2).length + 1) ^ 4

/-- The binary length of the clock is linear in the length of the simulated word. -/
private theorem length_encNat_sq_le (W : ℕ) : (encNat ((W + 1) ^ 2)).length ≤ 2 * (W + 1) := by
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
private theorem exists_computableInO_accepts : ∃ D, ComputableInO
    (fun q : List Bool × List Bool × List Bool => accepts q.1 q.2.1 q.2.2)
    (encPair encBits (encPair encBits encBits)) encBool (accBound D) (accBound D) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  set enc := encPair encBits (encPair encBits encBits)
  have hdesc := hdec.inO.comp (ComputableInO.fst encBits (encPair encBits encBits))
  have hword : ComputableInO (fun q : List Bool × List Bool × List Bool => frame q.2.1 ++ q.2.2)
      enc encBits (fun q => (enc q).length) (fun q => (enc q).length) :=
    (ComputableInO.snd encBits (encPair encBits encBits)).of_enc_eq fun _ => rfl
  have hsym := Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO.comp hword
  have hclock := timeConstructible_succ_sq.computableInO.comp hword
  have hU := computableInO_universal.comp (hdesc.prod (hsym.prod hclock))
  have hv := Diagonal.computableInO_verdict.comp hU
  have hnot := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp hv
  obtain ⟨cD, hcD⟩ := hdesc.length_le
  obtain ⟨cO, hcO⟩ := hU.length_le
  obtain ⟨K, hK⟩ := accBound_aux 0 cD cO
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
    have hL := length_encNat_sq_le (frame q.2.1 ++ q.2.2).length
    simp only [Function.comp_apply, encBits_apply, enc, length_encPair, List.length_append,
      length_frame] at hD hE hNl hL ⊢
    refine hK (X := (q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1)
      (by omega) (by omega) (by omega) hD hNl (by omega) (by omega) (Nat.one_le_pow _ _ (by omega))
      hE
  have e (q : List Bool × List Bool × List Bool) : accBound (dd + 1) q =
      ((q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1) ^ 4 *
        (((frame q.2.1 ++ q.2.2).length + 1) ^ 2) ^ 2 := by
    rw [accBound, ← pow_mul]
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

/-- A polynomially bounded resource function is within a constant multiple of `2 ^ size`. -/
private theorem PolyBounded.exists_le_mul_two_pow' {α : Type*} {size u : α → ℕ}
    (h : PolyBounded size u) : ∃ C, ∀ a, u a ≤ C * 2 ^ size a := by
  obtain ⟨c, d, hcd⟩ := h.exists_le
  obtain ⟨C, hC⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => c * (n + 1) ^ d) (by fun_prop)
  exact ⟨C, fun a => (hcd a).trans (hC _)⟩

/-- **`2 ^ L x` in unary**, for an exponent `L x` computable in unary in polynomial time, within
time `O(2 ^ |x| + 4 ^ L x)` and space `O(2 ^ |x| + 2 ^ L x)`. -/
private theorem exists_computableInO_unary_two_pow {α : Type} {enc : α ↪ List Bool} {L : α → ℕ}
    (hL : ComputableInPolyTime L enc encUnary) :
    ∃ C, ComputableInO (fun x => 2 ^ L x) enc encUnary
      (fun x => C * 2 ^ (enc x).length + 4 ^ L x) (fun x => C * 2 ^ (enc x).length + 2 ^ L x) := by
  obtain ⟨T, S, hT, hS, h⟩ := hL.exists_computableInO
  obtain ⟨C₁, hC₁⟩ := PolyBounded.exists_le_mul_two_pow' hT
  obtain ⟨C₂, hC₂⟩ := PolyBounded.exists_le_mul_two_pow' hS
  refine ⟨C₁ + C₂, (ComputableInO.unary_two_pow.comp h).mono_le (fun x => ?_) fun x => ?_⟩
  · have h₁ := hC₁ x
    have h₂ : (L x + 1) * 2 ^ L x ≤ 4 ^ L x := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow]
      exact Nat.mul_le_mul_right _ Nat.lt_two_pow_self
    have h₃ : C₁ * 2 ^ (enc x).length ≤ (C₁ + C₂) * 2 ^ (enc x).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have h₁ := hC₂ x
    have h₃ : C₂ * 2 ^ (enc x).length ≤ (C₁ + C₂) * 2 ^ (enc x).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- The numeric facts behind the bound of the brute force: the encoded pair of length `N`, the
certificate length `c`, the unary certificate length and the search. -/
private theorem brute_bound_aux (C K₀ N c : ℕ) (hc : 1 ≤ c) :
    N + (C * 2 ^ N + c * c) + 2 ^ (K₀ * (2 * N + 1 + c + c)) ≤
      (C + 3) * (2 ^ ((3 * K₀ + 4) * (N + c)) + 1) := by
  set B := 2 ^ ((3 * K₀ + 4) * (N + c))
  have hN : 2 ^ N ≤ B := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hN' : N < 2 ^ N := Nat.lt_two_pow_self
  have hcc : c * c ≤ B := by
    have h₁ : c * c ≤ 2 ^ c * 2 ^ c :=
      Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le
    rw [← pow_add] at h₁
    exact h₁.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hs : 2 ^ (K₀ * (2 * N + 1 + c + c)) ≤ B :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hC : C * 2 ^ N ≤ C * B := Nat.mul_le_mul_left _ hN
  have e : (C + 3) * (B + 1) = C * B + 3 * B + (C + 3) := by ring
  omega

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' in
/-- The brute force at the end of an interval runs within time exponential in the description,
the input and the certificate length. The certificate length is first written in unary, and every
certificate of that length is tried with the polynomial-time simulation. -/
private theorem exists_computableInO_brute (k : ℕ) : ∃ K, ComputableInO
    (fun q : List Bool × List Bool =>
      (Cslib.BitString.enumList (certLen k q.2.length)).any (accepts q.1 q.2))
    (encPair encBits encBits) encBool
    (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen k q.2.length)))
    (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen k q.2.length))) := by
  obtain ⟨D, hacc⟩ := exists_computableInO_accepts
  set encQ := encPair encBits encBits with hencQ
  set encB := encPair encQ encUnary with hencB
  set enc := encPair encB encBits with henc
  -- the search, with the certificate length given in unary
  have hB := ComputableInO.fst encB encBits
  have hre := (hB.fst'.fst').prod (hB.fst'.snd'.prod (ComputableInO.snd encB encBits))
  have hf := hacc.comp hre
  have hlen (r : ((List Bool × List Bool) × ℕ) × List Bool) :
      r.1.1.1.length ≤ (enc r).length ∧ r.1.1.2.length ≤ (enc r).length ∧
        r.2.length ≤ (enc r).length ∧ (encB r.1).length ≤ (enc r).length := by
    have e₁ : (enc r).length = 2 * (encB r.1).length + 1 + r.2.length := by
      rw [henc, length_encPair, encBits_apply]
    have e₂ : (encB r.1).length = 2 * (encQ r.1.1).length + 1 + r.1.2 := by
      rw [hencB, length_encPair, encUnary_apply, List.length_replicate]
    have e₃ : (encQ r.1.1).length = 2 * r.1.1.1.length + 1 + r.1.1.2.length := by
      rw [hencQ, length_encPair, encBits_apply, encBits_apply]
    omega
  have hf' : ComputableInO (fun r : ((List Bool × List Bool) × ℕ) × List Bool =>
      accepts r.1.1.1 r.1.1.2 r.2) enc encBool
      (fun r => 6 * (enc r).length + accBound D (r.1.1.1, r.1.1.2, r.2))
      (fun r => 6 * (enc r).length + accBound D (r.1.1.1, r.1.1.2, r.2)) := by
    refine hf.mono_le (fun r => ?_) (fun r => ?_) <;>
    · rw [← henc]
      omega
  have hpoly : PolyBounded (fun r => (enc r).length) fun r =>
      6 * (enc r).length + accBound D (r.1.1.1, r.1.1.2, r.2) :=
    (PolyBounded.of_polynomiallyBounded (fun r => (enc r).length)
      (bound := fun n => 6 * n + ((n + 1) ^ D + n + n + 1) ^ 4 * (2 * n + 1 + n + 1) ^ 4)
      (by fun_prop)).mono fun r => by
        obtain ⟨h₁, h₂, h₃, -⟩ := hlen r
        simp only [accBound, List.length_append, length_frame]
        gcongr
  have hℓ : ComputableInPolyTime (fun b : (List Bool × List Bool) × ℕ => b.2) encB encUnary := by
    fun_prop
  obtain ⟨K₀, hsearch⟩ := exists_computableInO_any_enumList hf' hpoly hpoly hℓ
  -- the certificate length in unary
  have hL : ComputableInPolyTime (fun q : List Bool × List Bool => (k + 1) * (q.2.length + 1))
      encQ encUnary := by
    fun_prop
  obtain ⟨C, hcl⟩ := exists_computableInO_unary_two_pow hL
  have hpair := (ComputableInO.of_eq (f := fun q : List Bool × List Bool => q) (encIn := encQ)
    (encMid := encQ) fun _ => rfl).prod hcl
  have h := hsearch.comp hpair
  -- the bounds
  refine ⟨3 * K₀ + 4, (h.mono (C + 3) (fun q => ?_) fun q => ?_).of_enc_eq fun q => rfl⟩
  all_goals
    have e₁ : (encB (q, 2 ^ ((k + 1) * (q.2.length + 1)))).length =
        2 * (encQ q).length + 1 + 2 ^ ((k + 1) * (q.2.length + 1)) := by
      rw [hencB, length_encPair, encUnary_apply, List.length_replicate]
    have e₂ : (4 : ℕ) ^ ((k + 1) * (q.2.length + 1)) =
        2 ^ ((k + 1) * (q.2.length + 1)) * 2 ^ ((k + 1) * (q.2.length + 1)) := by
      rw [← mul_pow]
      norm_num
    have hc : 1 ≤ 2 ^ ((k + 1) * (q.2.length + 1)) := Nat.one_le_two_pow
    have h := brute_bound_aux C K₀ (encQ q).length _ hc
    have hcc := Nat.le_mul_of_pos_left (2 ^ ((k + 1) * (q.2.length + 1))) hc
    simp only [e₁, e₂, certLen] at h ⊢
    omega

/-- Weaken only the time bound, keeping the space bound. -/
private theorem computableInO_mono_time {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {T S T' : α → ℕ}
    (h : ComputableInO f encIn encOut T S) (k : ℕ) (hT : ∀ a, T a ≤ k * (T' a + 1)) :
    ComputableInO f encIn encOut T' S :=
  h.mono (k + 1) (fun a => (hT a).trans (Nat.mul_le_mul_right _ (Nat.le_succ k)))
    fun _ => (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos k))

/-- The cost of the tests of the verifier: quadratic in the encoded input, times the square of a
bound `4 ^ ((k + 2) * (n + 1))` on the horizon, which the tests write in unary. -/
private def cheap (k : ℕ) (p : List Bool × List Bool) : ℕ :=
  ((encPair encBits encBits p).length + 1) ^ 2 * (4 ^ ((k + 2) * (p.1.length + 1))) ^ 2

/-- The numeric facts behind `cheap`, for an encoded input of length `N`, an input of length `n`
and a horizon `Z` of at most `G * Y`. -/
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

/-- The horizon of the interval of `unframe x` is at most `4 ^ ((k + 2) * (x.length + 1))`, and the
cost of writing it in unary is at most twice that bound plus its square. -/
private theorem horizon_le (k C : ℕ) (x : List Bool) :
    horizon k (2 * (unframe x).length + 1) ≤ 4 ^ ((k + 2) * (x.length + 1)) ∧
      C * 2 ^ (2 * (unframe x).length + 1) + 4 ^ ((k + 2) * (2 * (unframe x).length + 1 + 1)) ≤
        2 * C * 4 ^ ((k + 2) * (x.length + 1)) + (4 ^ ((k + 2) * (x.length + 1))) ^ 2 := by
  have hu := length_unframe_le x
  have h4 (a : ℕ) : (4 : ℕ) ^ a = 2 ^ (2 * a) := by rw [pow_mul]; norm_num
  refine ⟨?_, ?_⟩
  · rw [horizon, h4]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  · have h₁ : 2 ^ (2 * (unframe x).length + 1) ≤ 2 * 4 ^ ((k + 2) * (x.length + 1)) := by
      rw [h4, pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    have h₂ : 4 ^ ((k + 2) * (2 * (unframe x).length + 1 + 1)) ≤
        (4 ^ ((k + 2) * (x.length + 1))) ^ 2 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have := Nat.mul_le_mul_left C h₁
    have e : C * (2 * 4 ^ ((k + 2) * (x.length + 1))) = 2 * C * 4 ^ ((k + 2) * (x.length + 1)) := by
      ring
    omega

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' in
/-- **The verifier of the exponential lazy diagonal is computable**, within the cost of its tests
plus the cost of the branch taken: the simulation, or the brute force at the end of an interval. -/
private theorem exists_computableInO_verifier (k : ℕ) :
    ∃ (D K : ℕ) (S : List Bool × List Bool → ℕ),
    ComputableInO (verifier k) (encPair encBits encBits) encBool
      (fun p => cheap k p + if Diagonal.shortDesc (unframe p.1) then
        (cheap k p + if Nat.size (p.1.length + 1) ≤ horizon k (2 * (unframe p.1).length + 1) then
          cheap k p + accBound D (unframe (unframe p.1), p.1 ++ [false], p.2)
        else (cheap k p + if Nat.size p.1.length ≤ horizon k (2 * (unframe p.1).length + 1) then
          cheap k p + 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
            frame (unframe p.1))).length + certLen k (2 * (unframe p.1).length + 1)))
          else cheap k p))
        else cheap k p) S := by
  obtain ⟨D, hacc⟩ := exists_computableInO_accepts
  obtain ⟨K, hbrute⟩ := exists_computableInO_brute k
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
  have hL : ComputableInPolyTime (fun z : List Bool => (k + 2) * (z.length + 1)) encBits
      encUnary := by
    fun_prop
  obtain ⟨CE, hE₀⟩ := exists_computableInO_unary_two_pow hL
  have hE := hE₀.comp hbase
  -- the numeric facts about the tests
  have hfacts (p : List Bool × List Bool) : (unframe p.1).length ≤ p.1.length ∧
      p.1.length ≤ (encPair encBits encBits p).length ∧
      (encPair encBits encBits p).length + 1 ≤ cheap k p ∧
      (horizon k (2 * (unframe p.1).length + 1) + 1) ^ 2 ≤ 25 * cheap k p ∧
      (2 * (encPair encBits encBits p).length + 4 +
        horizon k (2 * (unframe p.1).length + 1)) ^ 2 ≤ 25 * cheap k p ∧
      CE * 2 ^ (2 * (unframe p.1).length + 1) +
        4 ^ ((k + 2) * (2 * (unframe p.1).length + 1 + 1)) ≤ (2 * CE + 1) * cheap k p := by
    have hu := length_unframe_le p.1
    have hn : p.1.length ≤ (encPair encBits encBits p).length := by
      simp only [length_encPair, encBits_apply]
      omega
    obtain ⟨hZ, hE'⟩ := horizon_le k CE p.1
    set Y := 4 ^ ((k + 2) * (p.1.length + 1))
    have hY : 1 ≤ Y := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨h₁, h₂, h₃⟩ := cheap_aux 1 hn hY
      (Z := horizon k (2 * (unframe p.1).length + 1)) (by omega)
    have hc : cheap k p = ((encPair encBits encBits p).length + 1) ^ 2 * Y ^ 2 := rfl
    have hY₁ : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
    have hY₂ : Y ^ 2 ≤ cheap k p := by
      rw [hc]
      exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
    have e : (2 * CE + 1) * cheap k p = 2 * CE * cheap k p + cheap k p := by ring
    have := Nat.mul_le_mul_left (2 * CE) (hY₁.trans hY₂)
    norm_num only at h₂ h₃
    rw [hc]
    exact ⟨hu, hn, hc ▸ h₁, h₂, h₃, by rw [← hc]; omega⟩
  set A := 8 + 4 * 25 + (2 * CE + 1)
  have e (p : List Bool × List Bool) : A * (cheap k p + 1) =
      8 * cheap k p + 4 * (25 * cheap k p) + (2 * CE + 1) * cheap k p + A := by ring
  have hc₀ := computableInO_mono_time (Diagonal.computableInO_shortDesc.comp hw) (T' := cheap k)
      A fun p => by
    obtain ⟨hu, hn, h₁, -, h₃, -⟩ := hfacts p
    have : ((unframe p.1).length + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        horizon k (2 * (unframe p.1).length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [Function.comp_apply] at ⊢
    have := e p
    omega
  have hc₁ := computableInO_mono_time (ComputableInO.unaryLe.comp ((hsz.comp hsnoc).prod hE))
      (T' := cheap k) A fun p => by
    obtain ⟨hu, hn, h₁, h₂, h₃, h₄⟩ := hfacts p
    have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.1.length + 1))
    have he := Universal.length_encNat_le (p.1.length + 1)
    have hsq : (p.1.length + 1 + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        horizon k (2 * (unframe p.1).length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : (2 * Nat.size (p.1.length + 1) + 1 + horizon k (2 * (unframe p.1).length + 1)
        + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
          horizon k (2 * (unframe p.1).length + 1)) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
      encUnary_apply, List.length_replicate, List.length_append, List.length_singleton,
      length_frame, encBits_apply] at ⊢
    simp only [horizon] at hsq hsq' h₂ h₃
    have := e p
    omega
  have hc₂ := computableInO_mono_time (ComputableInO.unaryLe.comp ((hsz.comp hx).prod hE))
      (T' := cheap k) A fun p => by
    obtain ⟨hu, hn, h₁, h₂, h₃, h₄⟩ := hfacts p
    have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.1.length))
    have he := Universal.length_encNat_le p.1.length
    have hsq : (p.1.length + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
        horizon k (2 * (unframe p.1).length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : (2 * Nat.size p.1.length + 1 + horizon k (2 * (unframe p.1).length + 1)
        + 1) ^ 2 ≤ (2 * (encPair encBits encBits p).length + 4 +
          horizon k (2 * (unframe p.1).length + 1)) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
      encUnary_apply, List.length_replicate, length_frame, encBits_apply] at ⊢
    simp only [horizon] at hsq hsq' h₂ h₃
    have := e p
    omega
  have hc₁' := hc₁.of_enc_eq (encC := encBool) (g := fun p : List Bool × List Bool =>
      decide (Nat.size (p.1.length + 1) ≤ horizon k (2 * (unframe p.1).length + 1))) fun p => by
    simp only [Function.comp_apply, horizon, length_frame, List.length_append,
      List.length_singleton]
    rfl
  have hc₂' := hc₂.of_enc_eq (encC := encBool) (g := fun p : List Bool × List Bool =>
      decide (Nat.size p.1.length ≤ horizon k (2 * (unframe p.1).length + 1))) fun p => by
    simp only [Function.comp_apply, horizon, length_frame]
    rfl
  have hf₁ := computableInO_mono_time
      (hacc.comp (hcode.prod (hsnoc.prod (ComputableInO.snd encBits encBits))))
      (T' := fun p => cheap k p + accBound D (unframe (unframe p.1), p.1 ++ [false], p.2)) 7
      fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    simp only [Function.comp_apply] at ⊢
    have e : 7 * (cheap k p + accBound D (unframe (unframe p.1), p.1 ++ [false], p.2) + 1) =
        7 * cheap k p + 7 * accBound D (unframe (unframe p.1), p.1 ++ [false], p.2) + 7 := by
      ring
    omega
  have hf₂ := computableInO_mono_time ((ComputableInDegree.of_finite (encIn := encBool)
    (encMid := encBool) (fun b : Bool => !b)).inO_one.comp (hbrute.comp (hcode.prod hbase)))
      (T' := fun p => cheap k p + 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
        frame (unframe p.1))).length + certLen k (2 * (unframe p.1).length + 1)))) 7
      fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    have hb : (encBool ((Cslib.BitString.enumList (certLen k (frame (unframe p.1)).length)).any
        (accepts (unframe (unframe p.1)) (frame (unframe p.1))))).length = 1 := rfl
    simp only [Function.comp_apply, hb] at ⊢
    rw [length_frame]
    set B := 2 ^ (K * ((encPair encBits encBits (unframe (unframe p.1),
        frame (unframe p.1))).length + certLen k (2 * (unframe p.1).length + 1)))
    have e : 7 * (cheap k p + B + 1) = 7 * cheap k p + 7 * B + 7 := by ring
    omega
  have hfalse := computableInO_mono_time (ComputableInO.const (encIn := encPair encBits encBits)
    (encMid := encBool) false) (T' := cheap k) 1 fun p => by
    obtain ⟨hu, hn, h₁, -⟩ := hfacts p
    omega
  have h := hc₀.ite (hc₁'.ite hf₁ (hc₂'.ite hf₂ hfalse)) hfalse
  refine ⟨D, K, _, (h.of_enc_eq fun p => ?_).mono_le (fun p => le_of_eq ?_) fun p => le_rfl⟩
  · congr 1
    simp only [verifier, Function.comp_apply, decide_eq_true_eq, length_frame]
  · simp only [Function.comp_apply, decide_eq_true_eq]

/-- `2 ^ a ≤ 2 ^ b * 2 ^ c` whenever `a ≤ c + b`. -/
private theorem two_pow_le_two_pow_mul {a b c : ℕ} (h : a ≤ c + b) : 2 ^ a ≤ 2 ^ b * 2 ^ c := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The exponential lazy diagonal is decidable in nondeterministic time
`O(2 ^ ((8 * k + 16) * n))`.** Guess a certificate of length `2 ^ ((k + 1) * (n + 2))` and run the
verifier (`Cslib.Complexity.setOf_exists_mem_NTIME`). Below the end of an interval, the verifier
simulates a verifier on the input one bit longer with a certificate of that length, within time
polynomial in the certificate. At the end of an interval of start `P`, it tries every certificate
on the input of length `P`, within time `2 ^ O(certLen k P)`, which is linear in the length `n` of
the input, since `n + 1 = 2 ^ horizon k P` there and `horizon k P = 2 ^ (P + 1) * certLen k P`. -/
theorem expLazyDiagonal_mem_NTIME (k : ℕ) :
    expLazyDiagonal k ∈ NTIME encBits fun n => 2 ^ ((8 * k + 16) * n) := by
  obtain ⟨D, K, S, hV⟩ := exists_computableInO_verifier k
  have hL : ComputableInPolyTime (fun x : List Bool => (k + 1) * (x.length + 2)) encBits
      encUnary := by
    fun_prop
  obtain ⟨Cℓ, hℓ₀⟩ := exists_computableInO_unary_two_pow hL
  have hℓ := hℓ₀.of_enc_eq (encC := encUnary)
    (g := fun x : List Bool => certLen k (x.length + 1)) fun x => rfl
  obtain ⟨CD, hCD⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun m => (m + 1) ^ D)
    (by fun_prop)
  set B₀ := 3 * K * 2 ^ ((k + 1) * (3 * K))
  set A₁ := 2 ^ (8 * k + 14)
  set A₂ := 81 * (CD + 3) ^ 4 * 2 ^ (16 * k + 16)
  set A₃ := Cℓ + 2 ^ (4 * k + 4)
  refine setOf_exists_mem_NTIME hℓ hV (C := 2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀) fun x v hv => ?_
  simp only [encBits_apply]
  set n := x.length with hn
  set V := 2 ^ ((k + 1) * (n + 2)) with hVdef
  have hv' : v.length = V := by
    rw [hv]
    rfl
  set M := 2 ^ ((8 * k + 16) * n)
  have hnV : 4 * n + 4 ≤ V :=
    calc 4 * n + 4 ≤ 2 ^ (n + 2) := by
          have := Nat.lt_two_pow_self (n := n)
          rw [pow_succ, pow_succ]
          omega
      _ ≤ V := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
  have hnM : n + 1 ≤ M := by
    calc n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      _ ≤ M := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
  -- the tests
  have hcheap : cheap k (x, v) ≤ A₁ * M := by
    have hN : (encPair encBits encBits (x, v)).length + 1 ≤ 2 * V := by
      simp only [length_encPair, encBits_apply, hv', ← hn]
      omega
    calc cheap k (x, v) = ((encPair encBits encBits (x, v)).length + 1) ^ 2 *
          (4 ^ ((k + 2) * (n + 1))) ^ 2 := rfl
      _ ≤ (2 * V) ^ 2 * (4 ^ ((k + 2) * (n + 1))) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 2)
      _ = 2 ^ (2 + 2 * ((k + 1) * (n + 2)) + 4 * ((k + 2) * (n + 1))) := by
          rw [hVdef, show (4 : ℕ) = 2 ^ 2 by rfl]
          simp only [mul_pow, ← pow_mul, ← pow_add]
          ring_nf
      _ ≤ A₁ * M := two_pow_le_two_pow_mul (by ring_nf; nlinarith [Nat.zero_le (k * n)])
  -- the simulation, when the description is short
  have hacc (h₀ : Diagonal.shortDesc (unframe x) = true) :
      accBound D (unframe (unframe x), x ++ [false], v) ≤ A₂ * M := by
    have hs : 2 ^ (unframe (unframe x)).length ≤ (unframe x).length := of_decide_eq_true h₀
    have hu := length_unframe_le x
    have hD : ((unframe (unframe x)).length + 1) ^ D ≤ CD * n :=
      (hCD _).trans (Nat.mul_le_mul_left _ (hs.trans hu))
    have hb : ((unframe (unframe x)).length + 1) ^ D + (n + 1) + V + 1 ≤ (CD + 3) * V := by
      have h₂ : CD * n ≤ CD * V := Nat.mul_le_mul_left _ (by omega)
      have e : (CD + 3) * V = CD * V + 3 * V := by ring
      omega
    have hw : (frame (x ++ [false]) ++ v).length + 1 ≤ 3 * V := by
      simp only [List.length_append, length_frame, List.length_singleton, hv', ← hn]
      omega
    calc accBound D (unframe (unframe x), x ++ [false], v) =
          (((unframe (unframe x)).length + 1) ^ D + (n + 1) + V + 1) ^ 4 *
            ((frame (x ++ [false]) ++ v).length + 1) ^ 4 := by
          simp only [accBound, List.length_append, List.length_singleton, hv', ← hn]
      _ ≤ ((CD + 3) * V) ^ 4 * (3 * V) ^ 4 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hb 4) (Nat.pow_le_pow_left hw 4)
      _ = 81 * (CD + 3) ^ 4 * 2 ^ (8 * ((k + 1) * (n + 2))) := by
          rw [hVdef]
          simp only [mul_pow, ← pow_mul]
          ring
      _ ≤ 81 * (CD + 3) ^ 4 * (2 ^ (16 * k + 16) * M) :=
          Nat.mul_le_mul_left _ (two_pow_le_two_pow_mul (by ring_nf; nlinarith))
      _ = A₂ * M := by ring
  -- the brute force, at the end of an interval
  have hbrute (h₁ : ¬Nat.size (n + 1) ≤ horizon k (2 * (unframe x).length + 1)) :
      2 ^ (K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen k (2 * (unframe x).length + 1))) ≤ n + 1 + 2 ^ B₀ := by
    set P := 2 * (unframe x).length + 1 with hP
    have hE : 2 ^ horizon k P ≤ n + 1 := by
      rw [Nat.size_le, not_lt] at h₁
      exact h₁
    have hc := length_unframe_le (unframe x)
    have hPc : P + 1 ≤ certLen k P :=
      calc P + 1 ≤ 2 ^ (P + 1) := Nat.lt_two_pow_self.le
        _ ≤ certLen k P := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
    have hlen : (encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen k P ≤ 3 * certLen k P := by
      simp only [length_encPair, encBits_apply, length_frame]
      omega
    rcases le_or_gt (3 * K) (2 ^ (P + 1)) with hK | hK
    · have hle : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
          certLen k P) ≤ horizon k P :=
        calc _ ≤ K * (3 * certLen k P) := Nat.mul_le_mul_left _ hlen
          _ = 3 * K * certLen k P := by ring
          _ ≤ 2 ^ (P + 1) * certLen k P := Nat.mul_le_mul_right _ hK
          _ = horizon k P := by
              rw [certLen, horizon, ← pow_add]
              congr 1
              ring
      exact ((Nat.pow_le_pow_right (by norm_num) hle).trans hE).trans (Nat.le_add_right _ _)
    · have hP3 : P + 1 ≤ 3 * K := (Nat.lt_two_pow_self.trans hK).le
      have hle : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
          certLen k P) ≤ B₀ :=
        calc _ ≤ K * (3 * certLen k P) := Nat.mul_le_mul_left _ hlen
          _ = 3 * K * certLen k P := by ring
          _ ≤ 3 * K * 2 ^ ((k + 1) * (3 * K)) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
                (Nat.mul_le_mul_left _ hP3))
      exact (Nat.pow_le_pow_right (by norm_num) hle).trans (Nat.le_add_left _ _)
  -- the certificate length
  have hTℓ : Cℓ * 2 ^ n + 4 ^ ((k + 1) * (n + 2)) ≤ A₃ * M := by
    have h₁ : 2 ^ n ≤ M := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
    have h₂ : 4 ^ ((k + 1) * (n + 2)) ≤ 2 ^ (4 * k + 4) * M := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
      exact two_pow_le_two_pow_mul (by ring_nf; nlinarith)
    have e : A₃ * M = Cℓ * M + 2 ^ (4 * k + 4) * M := by ring
    have := Nat.mul_le_mul_left Cℓ h₁
    omega
  have e : (2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀) * M =
      2 * M + A₃ * M + 4 * (A₁ * M) + A₂ * M + 2 ^ B₀ * M := by ring
  have hB : 2 ^ B₀ ≤ 2 ^ B₀ * M := Nat.le_mul_of_pos_right _ (by omega)
  clear_value M A₁ A₂ A₃ B₀
  generalize 2 + A₃ + 4 * A₁ + A₂ + 2 ^ B₀ = C at *
  generalize 2 ^ B₀ = Q at *
  split_ifs with h₀ h₁ h₂
  · have := hacc h₀
    omega
  · have := hbrute h₁
    omega
  · omega
  · omega

/-! ### The hierarchy -/

/-- **A nondeterministic exponential time hierarchy.** For every `k`, nondeterministic time
`O(2 ^ (k * n))` is strictly contained in nondeterministic time `O(2 ^ (e * n))` whenever
`8 * k + 16 ≤ e`. The exponential lazy diagonal `Cslib.Complexity.expLazyDiagonal k` separates them
(`Cslib.Complexity.expLazyDiagonal_mem_NTIME`, `Cslib.Complexity.expLazyDiagonal_notMem_NTIME`).
This is a coarse exponential form of the nondeterministic time hierarchy theorem
[Arora and Barak, Theorem 3.3][AroraBarak07]. -/
theorem NTIME_two_pow_ssubset_NTIME_two_pow_of_le {k e : ℕ} (h : 8 * k + 16 ≤ e) :
    NTIME encBits (fun n => 2 ^ (k * n)) ⊂ NTIME encBits fun n => 2 ^ (e * n) := by
  have hsub : ∀ {a b : ℕ}, a ≤ b →
      NTIME encBits (fun n => 2 ^ (a * n)) ⊆ NTIME encBits fun n => 2 ^ (b * n) :=
    fun hab => NTIME_mono fun n => Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hab)
  exact (Set.ssubset_iff_of_subset (hsub (by omega))).mpr
    ⟨expLazyDiagonal k, hsub h (expLazyDiagonal_mem_NTIME k), expLazyDiagonal_notMem_NTIME k⟩

/-- **`NE` is not contained in `NTIME (2 ^ (k * n))`**, for any `k`: the exponential lazy diagonal
`Cslib.Complexity.expLazyDiagonal k` is in `NE` and not in `NTIME (2 ^ (k * n))`. -/
theorem exists_mem_NE_notMem_NTIME_two_pow (k : ℕ) :
    ∃ H ∈ NE encBits, H ∉ NTIME encBits fun n => 2 ^ (k * n) :=
  ⟨expLazyDiagonal k, Set.mem_iUnion.mpr ⟨_, expLazyDiagonal_mem_NTIME k⟩,
    expLazyDiagonal_notMem_NTIME k⟩

end Cslib.Complexity

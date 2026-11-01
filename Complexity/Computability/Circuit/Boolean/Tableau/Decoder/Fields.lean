/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tseitin
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size

/-!
# Field arithmetic for the decoder of the succinct tableau

The first stage of the decoder of the tableau formula on bit-field labels
(`Complexity/Computability/Circuit/Boolean/Tableau/Succinct.lean`). Its inputs are the bits of a
clause number: two bits of the clause, two bits of the tag, then a payload of `P = s + cb + tb`
bits made of the slot (`s` bits), the column `c` (`cb` bits) and the block `t` (`tb` bits). It is an
explicit De Morgan gate list (`fieldGates`) of

* two constants and the negations of the inputs;
* fourteen *comparison chains* of `P` gates each (`chainGate`): bit-serial comparisons of a field
  with a constant, least significant bit first, one gate per bit. They compare the column with
  `0`, `1`, `n`, `n + 1`, `2 T` and `T`, the block with `0` and `T`, the payload with `0`, `1` and
  the length of `x`, and give the borrows and carries of `c - 1`, `c + 1` and `t - 1`;
* a *decoder tree* of `2 ^ (m + 1) - 1` gates (`treeGates`), whose last level is the indicator of
  the low `m = Nat.size x.length` bits of the payload, and a chain of `x.length` disjunctions
  (`orGate`) that looks up the bit of the hardwired `x` at the payload.

There are `2 + (4 + P) + 14 P + (2 ^ (m + 1) - 1) + x.length` gates, linear in the field widths and
in the length of `x`; in particular there is no carry-lookahead adder, whose size is not linear.

Correctness is proved wire by wire: the intended value of every wire (`fieldVal`) is consistent
with its gate (`allGates_consistentAt_fieldGates`), so it is the value the list computes
(`getD_evalCode_of_allGates`).

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.Decoder.AllGates`: a property of every gate of a list at its
  wire.
* `Cslib.Circuits.Boolean.Tableau.Decoder.cmp`: the comparison computed by a chain.
* `Cslib.Circuits.Boolean.Tableau.Decoder.Chain`, `Cslib.Circuits.Boolean.Tableau.Decoder.chain`:
  the fourteen comparison chains.
* `Cslib.Circuits.Boolean.Tableau.Decoder.fieldGates`: the gate list.
* `Cslib.Circuits.Boolean.Tableau.Decoder.fieldVal`: the intended values of its wires.

## Main results

* `Cslib.Circuits.Boolean.Tableau.Decoder.getD_evalCode_of_allGates`: a valuation consistent with
  every gate of a well-formed list is its evaluation.
* `Cslib.Circuits.Boolean.Tableau.Decoder.getD_evalCode_fieldGates`: the gate list computes the
  intended values.
* `Cslib.Circuits.Boolean.Tableau.Decoder.length_fieldGates`: its number of gates.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Tableau.Decoder

/-! ### Gate lists checked gate by gate -/

/-- Every gate of `gates`, the first one at wire `base`, satisfies `p` at its wire. -/
def AllGates (p : ℕ → Op × List ℕ → Prop) (base : ℕ) (gates : List (Op × List ℕ)) : Prop :=
  ∀ g (hg : g < gates.length), p (base + g) gates[g]

theorem allGates_append {p : ℕ → Op × List ℕ → Prop} {b : ℕ} {l₁ l₂ : List (Op × List ℕ)} :
    AllGates p b (l₁ ++ l₂) ↔ AllGates p b l₁ ∧ AllGates p (b + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · have := h g (by simp only [List.length_append]; omega)
      rwa [List.getElem_append_left hg] at this
    · have := h (l₁.length + g) (by simp only [List.length_append]; omega)
      simpa [List.getElem_append_right, Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ g hg
    by_cases hg₁ : g < l₁.length
    · rw [List.getElem_append_left hg₁]
      exact h₁ g hg₁
    · rw [List.getElem_append_right (by omega)]
      have := h₂ (g - l₁.length) (by simp only [List.length_append] at hg; omega)
      rwa [show b + l₁.length + (g - l₁.length) = b + g by omega] at this

@[simp] theorem allGates_nil {p : ℕ → Op × List ℕ → Prop} {b : ℕ} : AllGates p b [] := by
  simp [AllGates]

theorem allGates_cons {p : ℕ → Op × List ℕ → Prop} {b : ℕ} {g : Op × List ℕ}
    {l : List (Op × List ℕ)} : AllGates p b (g :: l) ↔ p b g ∧ AllGates p (b + 1) l := by
  have := allGates_append (p := p) (b := b) (l₁ := [g]) (l₂ := l)
  simp only [List.singleton_append, List.length_singleton] at this
  rw [this]
  refine and_congr_left' ⟨fun h => by simpa using h 0 (by simp), fun h g hg => ?_⟩
  obtain rfl : g = 0 := by simpa using hg
  simpa using h

theorem allGates_map_range {p : ℕ → Op × List ℕ → Prop} {b w : ℕ} {f : ℕ → Op × List ℕ} :
    AllGates p b ((List.range w).map f) ↔ ∀ i < w, p (b + i) (f i) := by
  simp only [AllGates, List.length_map, List.length_range, List.getElem_map, List.getElem_range]

theorem allGates_flatMap_range {p : ℕ → Op × List ℕ → Prop} {b w : ℕ}
    {f : ℕ → List (Op × List ℕ)} :
    AllGates p b ((List.range w).flatMap f) ↔
      ∀ i < w, AllGates p (b + ((List.range i).map fun j => (f j).length).sum) (f i) := by
  induction w with
  | zero => simp [AllGates]
  | succ w ih =>
    rw [List.range_succ, List.flatMap_append, allGates_append, ih, List.flatMap_singleton,
      List.length_flatMap]
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h₁ i hi
      · exact h₂
    · exact fun h => ⟨fun i hi => h i (by omega), h w (by omega)⟩

/-- Blocks of a common length `len` start at multiples of `len`. -/
theorem sum_range_map_const {len : ℕ} {f : ℕ → List (Op × List ℕ)} (hf : ∀ j, (f j).length = len)
    (i : ℕ) : ((List.range i).map fun j => (f j).length).sum = i * len := by
  induction i with
  | zero => simp
  | succ i ih => simp [List.range_succ, hf, Nat.succ_mul]

/-- Blocks of lengths `2 ^ j` start at `2 ^ i - 1`. -/
theorem sum_range_two_pow (i : ℕ) : ((List.range i).map fun j => 2 ^ j).sum = 2 ^ i - 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    have := Nat.one_le_two_pow (n := i)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.pow_succ]
    omega

/-- A gate reads only wires below its own, with the arity of its operation. -/
def WellFormedAt (w : ℕ) (g : Op × List ℕ) : Prop :=
  g.2.length = signature.Arity g.1 ∧ ∀ i ∈ g.2, i < w

/-- The wire of a gate carries, under `σ`, the value of the gate on the values of its arguments. -/
def ConsistentAt (σ : ℕ → Bool) (w : ℕ) (g : Op × List ℕ) : Prop :=
  σ w = g.1.value (σ (g.2.getD 0 0)) (σ (g.2.getD 1 0))

/-- A list of well-formed gates is the code of a program. -/
theorem isCodeFrom_of_allGates {n : ℕ} {gates : List (Op × List ℕ)}
    (h : AllGates WellFormedAt n gates) : Program.IsCodeFrom signature n 0 gates :=
  Program.isCodeFrom_of_getElem fun j hj => by simpa [WellFormedAt] using h j hj

/-- **A valuation consistent with every gate is the evaluation** of a well-formed gate list. -/
theorem getD_evalCode_of_allGates {n : ℕ} {gates : List (Op × List ℕ)}
    (hwf : AllGates WellFormedAt n gates) (σ : ℕ → Bool) (hσ : AllGates (ConsistentAt σ) n gates)
    {w : ℕ} (hw : w < n + gates.length) :
    (evalCode interpretation false (List.ofFn fun i : Fin n => σ i) gates).getD w false = σ w :=
  ((eval_tseitinCNF_eq_true_iff_evalCode (isCodeFrom_of_allGates hwf) σ).1
    ((eval_tseitinCNF_eq_true_iff n gates σ).2 fun g hg => hσ g hg) w hw).symm

/-- A conjunction (`false`) or a disjunction (`true`). -/
def andOr (b : Bool) : Op := if b then .or else .and

@[simp] theorem value_andOr (b x y : Bool) :
    (andOr b).value x y = if b then x || y else x && y := by
  cases b <;> rfl

theorem wellFormedAt_const {w : ℕ} (b : Bool) : WellFormedAt w (.const b, []) :=
  ⟨rfl, by simp⟩

theorem wellFormedAt_not {w a : ℕ} (ha : a < w) : WellFormedAt w (.not, [a]) :=
  ⟨rfl, by simpa using ha⟩

theorem wellFormedAt_two {w a b : ℕ} {op : Op} (hop : signature.Arity op = 2) (ha : a < w)
    (hb : b < w) : WellFormedAt w (op, [a, b]) :=
  ⟨by simpa using hop.symm, by simp [ha, hb]⟩

theorem arity_andOr (b : Bool) : signature.Arity (andOr b) = 2 := by
  cases b <;> rfl

theorem consistentAt_const {σ : ℕ → Bool} {w : ℕ} {b : Bool} :
    ConsistentAt σ w (.const b, []) ↔ σ w = b := Iff.rfl

theorem consistentAt_not {σ : ℕ → Bool} {w a : ℕ} :
    ConsistentAt σ w (.not, [a]) ↔ σ w = !σ a := Iff.rfl

theorem consistentAt_two {σ : ℕ → Bool} {w a b : ℕ} {op : Op} :
    ConsistentAt σ w (op, [a, b]) ↔ σ w = op.value (σ a) (σ b) := Iff.rfl

/-! ### Bit-serial comparison -/

/-- The comparison computed by a chain: `a < b` (for `gt = false`) or `b < a` (for `gt = true`),
with ties decided by `e`. -/
def cmp (gt : Bool) (a b : ℕ) (e : Bool) : Bool :=
  if gt then decide (b < a) || (decide (a = b) && e) else decide (a < b) || (decide (a = b) && e)

/-- The low `i + 1` bits of a number: its bit `i` above its low `i` bits. -/
theorem mod_two_pow_succ (v i : ℕ) : v % 2 ^ (i + 1) = v % 2 ^ i + 2 ^ i * (v.testBit i).toNat := by
  rw [Nat.mod_pow_succ, Nat.toNat_testBit]

/-- **One step of a comparison chain**: comparing one more bit is a disjunction or a conjunction of
the literal of the bit with the comparison of the lower bits, by the bit of the constant. -/
theorem cmp_succ (gt : Bool) (v K i : ℕ) (e : Bool) :
    cmp gt (v % 2 ^ (i + 1)) (K % 2 ^ (i + 1)) e =
      (andOr (K.testBit i ^^ gt)).value (if gt then v.testBit i else !v.testBit i)
        (cmp gt (v % 2 ^ i) (K % 2 ^ i) e) := by
  rw [mod_two_pow_succ v, mod_two_pow_succ K]
  have hv := Nat.mod_lt v (Nat.two_pow_pos i)
  have hK := Nat.mod_lt K (Nat.two_pow_pos i)
  generalize v % 2 ^ i = a at hv ⊢
  generalize K % 2 ^ i = b at hK ⊢
  generalize 2 ^ i = X at hv hK ⊢
  cases v.testBit i <;> cases K.testBit i <;> cases gt <;> cases e <;>
    simp [cmp] <;> omega

/-- A comparison of numbers below `2 ^ w` on all `w` bits. -/
theorem cmp_mod_of_lt {gt : Bool} {v K w : ℕ} {e : Bool} (hv : v < 2 ^ w) (hK : K < 2 ^ w) :
    cmp gt (v % 2 ^ w) (K % 2 ^ w) e = cmp gt v K e := by
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hK]

/-! ### The layout -/

/-- A comparison chain: the offset and the width of the field it reads, its direction (`gt`:
`K < v` rather than `v < K`), the constant `K` and the tie value `init`. -/
structure Chain where
  /-- The input offset of the field. -/
  off : ℕ
  /-- The width of the field. -/
  width : ℕ
  /-- Whether the chain decides `K < v` rather than `v < K`. -/
  gt : Bool
  /-- The constant. -/
  K : ℕ
  /-- The value on equal numbers. -/
  init : Bool

/-- The fourteen comparison chains, for slot, column and block widths `s`, `cb` and `tb`, an
input bound `n`, a step bound `T` and a hardwired prefix of length `X`: the offset and the width
of the field read, the direction, the constant and the tie value. Chains `0`, `1` and `2` give
the borrows of `c - 1`, the carries of `c + 1` and the borrows of `t - 1`. -/
def chain (s cb tb X n T : ℕ) (k : ℕ) : Chain :=
  if k = 0 then ⟨4 + s, cb, false, 0, true⟩                  -- c % 2 ^ i = 0
  else if k = 1 then ⟨4 + s, cb, true, 2 ^ (s + cb + tb) - 1, true⟩ -- c % 2 ^ i = 2 ^ i - 1
  else if k = 2 then ⟨4 + s + cb, tb, false, 0, true⟩        -- t % 2 ^ i = 0
  else if k = 3 then ⟨4 + s, cb, true, 1, false⟩             -- 1 < c
  else if k = 4 then ⟨4 + s, cb, true, n, false⟩             -- n < c
  else if k = 5 then ⟨4 + s, cb, true, n + 1, false⟩         -- n + 1 < c
  else if k = 6 then ⟨4 + s, cb, false, 2 * T, false⟩        -- c < 2 T
  else if k = 7 then ⟨4 + s, cb, true, 2 * T, false⟩         -- 2 T < c
  else if k = 8 then ⟨4 + s, cb, false, T, false⟩            -- c < T
  else if k = 9 then ⟨4 + s, cb, true, T, false⟩             -- T < c
  else if k = 10 then ⟨4 + s + cb, tb, true, T, false⟩       -- T < t
  else if k = 11 then ⟨4, s + cb + tb, false, X, false⟩      -- p < X
  else if k = 12 then ⟨4, s + cb + tb, false, 0, true⟩       -- p = 0
  else ⟨4, s + cb + tb, true, 1, false⟩                      -- 1 < p

/-- The start of the comparison chains, after the `N` inputs, the two constants and the `N`
negations. -/
def chainBase (N : ℕ) : ℕ := 2 * N + 2

/-- The start of the decoder tree, after the fourteen chains of `P` gates. -/
def treeBase (N P : ℕ) : ℕ := chainBase N + 14 * P

/-- The start of the lookup chain, after the `2 ^ (m + 1) - 1` gates of the tree. -/
def orBase (N P m : ℕ) : ℕ := treeBase N P + (2 ^ (m + 1) - 1)

/-- Gate `i` of chain `k`, comparing the field of width `w` at input offset `off`, padded with
zeros to `P` bits, with the constant `K`: its literal is the bit of the field (`gt`) or its
negation, and it combines it with the previous gate of the chain (or the tie value `init`). -/
def chainGate (N P k : ℕ) (spec : Chain) (i : ℕ) : Op × List ℕ :=
  (andOr (spec.K.testBit i ^^ spec.gt),
    [if i < spec.width then (if spec.gt then spec.off + i else N + 2 + (spec.off + i))
      else (if spec.gt then N else N + 1),
     if i = 0 then (if spec.init then N + 1 else N) else chainBase N + k * P + (i - 1)])

/-- Node `q` of level `ℓ` of the decoder tree: true at level `0`, and otherwise the node `q % 2 ^ ℓ`
of the level below together with bit `ℓ` of the payload, negated when bit `ℓ` of `q` is clear. -/
def treeGate (N base ℓ q : ℕ) : Op × List ℕ :=
  if ℓ = 0 then (.const true, [])
  else (.and, [base + (2 ^ (ℓ - 1) - 1) + q % 2 ^ (ℓ - 1),
    if q.testBit (ℓ - 1) then 4 + (ℓ - 1) else N + 2 + (4 + (ℓ - 1))])

/-- The decoder tree on the low `m` bits of the payload, level by level. -/
def treeGates (N base m : ℕ) : List (Op × List ℕ) :=
  (List.range (m + 1)).flatMap fun ℓ => (List.range (2 ^ ℓ)).map (treeGate N base ℓ)

/-- Gate `i` of the lookup chain: the disjunction of the previous gate with the indicator of the
payload `i` when `x[i]` is true. -/
def orGate (N tbase m obase : ℕ) (x : List Bool) (i : ℕ) : Op × List ℕ :=
  (.or, [if i = 0 then N else obase + (i - 1),
    if x.getD i false then tbase + (2 ^ m - 1) + i else N])

/-- **The field stage of the decoder**, for slot, column and block widths `s`, `cb` and `tb`, a
hardwired input prefix `x`, an input length `n` and a step bound `T`. -/
def fieldGates (s cb tb : ℕ) (x : List Bool) (n T : ℕ) : List (Op × List ℕ) :=
  [(.const false, []), (.const true, [])] ++
    (List.range (4 + (s + cb + tb))).map (fun i => (.not, [i])) ++
    (List.range 14).flatMap (fun k => (List.range (s + cb + tb)).map
      (chainGate (4 + (s + cb + tb)) (s + cb + tb) k (chain s cb tb x.length n T k))) ++
    treeGates (4 + (s + cb + tb)) (treeBase (4 + (s + cb + tb)) (s + cb + tb))
      (Nat.size x.length) ++
    (List.range x.length).map (orGate (4 + (s + cb + tb))
      (treeBase (4 + (s + cb + tb)) (s + cb + tb)) (Nat.size x.length)
      (orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length)) x)

theorem length_treeGates (N base m : ℕ) : (treeGates N base m).length = 2 ^ (m + 1) - 1 := by
  rw [treeGates, List.length_flatMap]
  simpa using sum_range_two_pow (m + 1)

/-- **The number of gates of the field stage.** -/
theorem length_fieldGates (s cb tb : ℕ) (x : List Bool) (n T : ℕ) :
    (fieldGates s cb tb x n T).length =
      2 + (4 + (s + cb + tb)) + 14 * (s + cb + tb) + (2 ^ (Nat.size x.length + 1) - 1) +
        x.length := by
  simp only [fieldGates, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range, length_treeGates, List.length_flatMap, List.map_const', List.sum_replicate,
    smul_eq_mul]

/-! ### The intended values -/

/-- The comparison of chain `spec` after `j` bits, on the clause number `idx`. -/
def chainVal (spec : Chain) (idx j : ℕ) : Bool :=
  cmp spec.gt (idx / 2 ^ spec.off % 2 ^ spec.width % 2 ^ j) (spec.K % 2 ^ j) spec.init

/-- **The intended value of each wire** of the field stage on the bits of the clause number
`idx`: the inputs, the constants, the negations, the chains after each bit, the indicators of
the low bits of the payload `p = idx / 16`, and the lookup of `x` at `p`. -/
def fieldVal (s cb tb : ℕ) (x : List Bool) (n T idx w : ℕ) : Bool :=
  if w < 4 + (s + cb + tb) then idx.testBit w
  else if w = 4 + (s + cb + tb) then false
  else if w = 4 + (s + cb + tb) + 1 then true
  else if w < chainBase (4 + (s + cb + tb)) then !idx.testBit (w - (4 + (s + cb + tb) + 2))
  else if w < treeBase (4 + (s + cb + tb)) (s + cb + tb) then
    chainVal (chain s cb tb x.length n T ((w - chainBase (4 + (s + cb + tb))) / (s + cb + tb)))
      idx ((w - chainBase (4 + (s + cb + tb))) % (s + cb + tb) + 1)
  else if w < orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) then
    decide (idx / 16 % 2 ^ Nat.log 2 (w - treeBase (4 + (s + cb + tb)) (s + cb + tb) + 1) =
      w - treeBase (4 + (s + cb + tb)) (s + cb + tb) + 1 -
        2 ^ Nat.log 2 (w - treeBase (4 + (s + cb + tb)) (s + cb + tb) + 1))
  else decide (idx / 16 % 2 ^ Nat.size x.length ≤
      w - orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length)) &&
    x.getD (idx / 16 % 2 ^ Nat.size x.length) false

/-! ### Correctness -/

section Correctness

variable {s cb tb : ℕ} {x : List Bool} {n T : ℕ}

private theorem ite_pred {α : Type} {p : α → Prop} {c : Prop} [Decidable c] {a b : α} (ha : p a)
    (hb : p b) : p (if c then a else b) := by
  split <;> assumption

/-- The fields read by the chains lie within the inputs. -/
theorem chain_off_add_width_le (k : ℕ) :
    (chain s cb tb x.length n T k).off + (chain s cb tb x.length n T k).width ≤
      4 + (s + cb + tb) := by
  unfold chain
  repeat (refine ite_pred (p := fun spec : Chain =>
    spec.off + spec.width ≤ 4 + (s + cb + tb)) ?_ ?_; · dsimp only; omega)
  dsimp only; omega

private theorem chainWire_lt {k i P : ℕ} (hk : k < 14) (hi : i < P) : k * P + i < 14 * P := by
  have : k * P + P ≤ 14 * P := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  omega

private theorem chainWire_div {k i P : ℕ} (hi : i < P) : (k * P + i) / P = k := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]

private theorem chainWire_mod {k i P : ℕ} (hi : i < P) : (k * P + i) % P = i := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

theorem fieldVal_input (idx : ℕ) {w : ℕ} (hw : w < 4 + (s + cb + tb)) :
    fieldVal s cb tb x n T idx w = idx.testBit w := by
  simp only [fieldVal, hw, ↓reduceIte]

theorem fieldVal_false (idx : ℕ) : fieldVal s cb tb x n T idx (4 + (s + cb + tb)) = false := by
  simp [fieldVal]

theorem fieldVal_true (idx : ℕ) : fieldVal s cb tb x n T idx (4 + (s + cb + tb) + 1) = true := by
  simp [fieldVal]

theorem fieldVal_not (idx : ℕ) {j : ℕ} (hj : j < 4 + (s + cb + tb)) :
    fieldVal s cb tb x n T idx (4 + (s + cb + tb) + 2 + j) = !idx.testBit j := by
  have h₁ : ¬ 4 + (s + cb + tb) + 2 + j < 4 + (s + cb + tb) := by omega
  have h₂ : 4 + (s + cb + tb) + 2 + j ≠ 4 + (s + cb + tb) := by omega
  have h₃ : 4 + (s + cb + tb) + 2 + j ≠ 4 + (s + cb + tb) + 1 := by omega
  have h₄ : 4 + (s + cb + tb) + 2 + j < chainBase (4 + (s + cb + tb)) := by
    simp only [chainBase]; omega
  simp only [fieldVal, h₁, h₂, h₃, h₄, ↓reduceIte, Nat.add_sub_cancel_left]

theorem fieldVal_chain (idx : ℕ) {k i : ℕ} (hk : k < 14) (hi : i < s + cb + tb) :
    fieldVal s cb tb x n T idx (chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + i) =
      chainVal (chain s cb tb x.length n T k) idx (i + 1) := by
  have hw := chainWire_lt hk hi
  have h₁ : ¬ chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + i < 4 + (s + cb + tb) := by
    simp only [chainBase]; omega
  have h₂ : chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + i ≠ 4 + (s + cb + tb) := by
    simp only [chainBase]; omega
  have h₃ : chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + i ≠ 4 + (s + cb + tb) + 1 := by
    simp only [chainBase]; omega
  have h₄ : ¬ chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + i <
      chainBase (4 + (s + cb + tb)) := by omega
  have h₅ : chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + i <
      treeBase (4 + (s + cb + tb)) (s + cb + tb) := by simp only [treeBase]; omega
  have h₆ : chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + i -
      chainBase (4 + (s + cb + tb)) = k * (s + cb + tb) + i := by omega
  simp only [fieldVal, h₁, h₂, h₃, h₄, h₅, h₆, ↓reduceIte, chainWire_div hi,
    chainWire_mod hi]

theorem fieldVal_tree (idx : ℕ) {ℓ q : ℕ} (hℓ : ℓ ≤ Nat.size x.length) (hq : q < 2 ^ ℓ) :
    fieldVal s cb tb x n T idx (treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q) =
      decide (idx / 16 % 2 ^ ℓ = q) := by
  have hpow : 2 ^ ℓ + q < 2 ^ (Nat.size x.length + 1) :=
    calc 2 ^ ℓ + q < 2 ^ (ℓ + 1) := by rw [Nat.pow_succ]; omega
      _ ≤ 2 ^ (Nat.size x.length + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 := Nat.one_le_two_pow (n := ℓ)
  have h₀ : ¬ treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q <
      treeBase (4 + (s + cb + tb)) (s + cb + tb) := by omega
  have h₁ : ¬ treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q <
      4 + (s + cb + tb) := by simp only [treeBase, chainBase]; omega
  have h₂ : treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q ≠ 4 + (s + cb + tb) := by
    simp only [treeBase, chainBase]; omega
  have h₃ : treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q ≠
      4 + (s + cb + tb) + 1 := by simp only [treeBase, chainBase]; omega
  have h₄ : ¬ treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q <
      chainBase (4 + (s + cb + tb)) := by simp only [treeBase]; omega
  have h₅ : treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q <
      orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) := by
    simp only [orBase]; omega
  have h₆ : treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q -
      treeBase (4 + (s + cb + tb)) (s + cb + tb) + 1 = 2 ^ ℓ + q := by omega
  have hlog : Nat.log 2 (2 ^ ℓ + q) = ℓ :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [Nat.pow_succ]; omega)
  simp only [fieldVal, h₀, h₁, h₂, h₃, h₄, h₅, h₆, ↓reduceIte, hlog,
    Nat.add_sub_cancel_left]

theorem fieldVal_or (idx : ℕ) (i : ℕ) :
    fieldVal s cb tb x n T idx (orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + i) =
      (decide (idx / 16 % 2 ^ Nat.size x.length ≤ i) &&
        x.getD (idx / 16 % 2 ^ Nat.size x.length) false) := by
  have h₀ : ¬ orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + i <
      orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) := by omega
  have h₁ : ¬ orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + i <
      4 + (s + cb + tb) := by simp only [orBase, treeBase, chainBase]; omega
  have h₂ : orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + i ≠
      4 + (s + cb + tb) := by simp only [orBase, treeBase, chainBase]; omega
  have h₃ : orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + i ≠
      4 + (s + cb + tb) + 1 := by simp only [orBase, treeBase, chainBase]; omega
  have h₄ : ¬ orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + i <
      chainBase (4 + (s + cb + tb)) := by simp only [orBase, treeBase]; omega
  have h₅ : ¬ orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + i <
      treeBase (4 + (s + cb + tb)) (s + cb + tb) := by simp only [orBase]; omega
  simp only [fieldVal, h₀, h₁, h₂, h₃, h₄, h₅, ↓reduceIte, Nat.add_sub_cancel_left]

/-- The literal of a chain gate is the bit of its field, or its negation. -/
private theorem fieldVal_chainLit (idx : ℕ) (k i : ℕ) :
    fieldVal s cb tb x n T idx
        (if i < (chain s cb tb x.length n T k).width then
          (if (chain s cb tb x.length n T k).gt then (chain s cb tb x.length n T k).off + i
            else 4 + (s + cb + tb) + 2 + ((chain s cb tb x.length n T k).off + i))
        else (if (chain s cb tb x.length n T k).gt then 4 + (s + cb + tb)
          else 4 + (s + cb + tb) + 1)) =
      if (chain s cb tb x.length n T k).gt then
        (idx / 2 ^ (chain s cb tb x.length n T k).off %
          2 ^ (chain s cb tb x.length n T k).width).testBit i
      else !(idx / 2 ^ (chain s cb tb x.length n T k).off %
        2 ^ (chain s cb tb x.length n T k).width).testBit i := by
  have hle := chain_off_add_width_le (s := s) (cb := cb) (tb := tb) (x := x) (n := n) (T := T) k
  generalize chain s cb tb x.length n T k = spec at hle ⊢
  obtain ⟨off, w, gt, K, init⟩ := spec
  simp only at hle ⊢
  by_cases hi : i < w
  · cases gt
    · simp [hi, fieldVal_not idx (show off + i < 4 + (s + cb + tb) by omega),
        Nat.testBit_div_two_pow, Nat.add_comm i off]
    · simp [hi, fieldVal_input idx (show off + i < 4 + (s + cb + tb) by omega),
        Nat.testBit_div_two_pow, Nat.add_comm i off]
  · cases gt
    · simp [hi, fieldVal_true]
    · simp [hi, fieldVal_false]

/-- **The gates of the field stage, region by region.** -/
theorem allGates_fieldGates {p : ℕ → Op × List ℕ → Prop}
    (hc₀ : p (4 + (s + cb + tb)) (.const false, []))
    (hc₁ : p (4 + (s + cb + tb) + 1) (.const true, []))
    (hnot : ∀ i < 4 + (s + cb + tb), p (4 + (s + cb + tb) + 2 + i) (.not, [i]))
    (hchain : ∀ k < 14, ∀ i < s + cb + tb,
      p (chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + i)
        (chainGate (4 + (s + cb + tb)) (s + cb + tb) k (chain s cb tb x.length n T k) i))
    (htree : ∀ ℓ ≤ Nat.size x.length, ∀ q < 2 ^ ℓ,
      p (treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ ℓ - 1) + q)
        (treeGate (4 + (s + cb + tb)) (treeBase (4 + (s + cb + tb)) (s + cb + tb)) ℓ q))
    (hor : ∀ i < x.length,
      p (orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + i)
        (orGate (4 + (s + cb + tb)) (treeBase (4 + (s + cb + tb)) (s + cb + tb))
          (Nat.size x.length) (orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length)) x i)) :
    AllGates p (4 + (s + cb + tb)) (fieldGates s cb tb x n T) := by
  have hlen : ((List.range 14).flatMap fun k => (List.range (s + cb + tb)).map
      (chainGate (4 + (s + cb + tb)) (s + cb + tb) k (chain s cb tb x.length n T k))).length =
      14 * (s + cb + tb) := by
    simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const',
      List.sum_replicate, smul_eq_mul]
  simp only [fieldGates, allGates_append, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_range, hlen, length_treeGates, allGates_cons, allGates_nil,
    and_true]
  refine ⟨⟨⟨⟨⟨hc₀, hc₁⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allGates_map_range]
    intro i hi
    simpa [Nat.add_assoc] using hnot i hi
  · rw [allGates_flatMap_range]
    intro k hk
    rw [sum_range_map_const (len := s + cb + tb) (fun j => by simp), allGates_map_range]
    intro i hi
    have := hchain k hk i hi
    convert this using 2
    simp only [chainBase]
    omega
  · rw [treeGates, allGates_flatMap_range]
    intro ℓ hℓ
    simp only [List.length_map, List.length_range]
    rw [sum_range_two_pow, allGates_map_range]
    intro q hq
    have := htree ℓ (by omega) q hq
    convert this using 2
    simp only [treeBase, chainBase]
    omega
  · rw [allGates_map_range]
    intro i hi
    have := hor i hi
    convert this using 2
    simp only [orBase, treeBase, chainBase]
    omega

/-- **The field stage is a well-formed gate list**, when the decoder tree reads only payload
bits. -/
theorem allGates_wellFormedAt_fieldGates (hm : Nat.size x.length ≤ s + cb + tb) :
    AllGates WellFormedAt (4 + (s + cb + tb)) (fieldGates s cb tb x n T) := by
  have hX := Nat.lt_size_self x.length
  refine allGates_fieldGates (wellFormedAt_const _) (wellFormedAt_const _)
    (fun i hi => wellFormedAt_not (by omega)) (fun k hk i hi => ?_) (fun ℓ hℓ q hq => ?_)
    (fun i hi => ?_)
  · have hle := chain_off_add_width_le (s := s) (cb := cb) (tb := tb) (x := x) (n := n) (T := T) k
    refine wellFormedAt_two (arity_andOr _) ?_ ?_
    · simp only [chainBase]
      split_ifs <;> omega
    · simp only [chainBase]
      split_ifs <;> omega
  · unfold treeGate
    split_ifs with h₀ h₁
    · exact wellFormedAt_const _
    · have hq' := Nat.mod_lt q (Nat.two_pow_pos (ℓ - 1))
      have hpow : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      refine wellFormedAt_two rfl ?_ ?_ <;> simp only [treeBase, chainBase] <;> omega
    · have hq' := Nat.mod_lt q (Nat.two_pow_pos (ℓ - 1))
      have hpow : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      refine wellFormedAt_two rfl ?_ ?_ <;> simp only [treeBase, chainBase] <;> omega
  · have hpow : 2 ^ (Nat.size x.length + 1) = 2 * 2 ^ Nat.size x.length := Nat.pow_succ'
    refine wellFormedAt_two rfl ?_ ?_ <;> simp only [orBase, treeBase, chainBase] <;>
      split_ifs <;> omega

/-- The low `ℓ + 1` bits of two numbers agree exactly when their low `ℓ` bits and their bits `ℓ`
agree. -/
theorem mod_two_pow_succ_eq_iff {p q ℓ : ℕ} (hq : q < 2 ^ (ℓ + 1)) :
    p % 2 ^ (ℓ + 1) = q ↔ p % 2 ^ ℓ = q % 2 ^ ℓ ∧ p.testBit ℓ = q.testBit ℓ := by
  conv_lhs => rw [← Nat.mod_eq_of_lt hq, mod_two_pow_succ p, mod_two_pow_succ q]
  have ha := Nat.mod_lt p (Nat.two_pow_pos ℓ)
  have hb := Nat.mod_lt q (Nat.two_pow_pos ℓ)
  generalize p % 2 ^ ℓ = a at ha ⊢
  generalize q % 2 ^ ℓ = b at hb ⊢
  generalize 2 ^ ℓ = X at ha hb ⊢
  cases p.testBit ℓ <;> cases q.testBit ℓ <;> simp <;> omega

/-- **The intended values are consistent with the gates** of the field stage. -/
theorem allGates_consistentAt_fieldGates (hm : Nat.size x.length ≤ s + cb + tb) (idx : ℕ) :
    AllGates (ConsistentAt (fieldVal s cb tb x n T idx)) (4 + (s + cb + tb))
      (fieldGates s cb tb x n T) := by
  have hX := Nat.lt_size_self x.length
  refine allGates_fieldGates (consistentAt_const.2 (fieldVal_false idx))
    (consistentAt_const.2 (fieldVal_true idx))
    (fun i hi => consistentAt_not.2 (by rw [fieldVal_not idx hi, fieldVal_input idx hi]))
    (fun k hk i hi => ?_) (fun ℓ hℓ q hq => ?_) (fun i hi => ?_)
  · rw [chainGate, consistentAt_two, fieldVal_chain idx hk hi, fieldVal_chainLit]
    have hprev : fieldVal s cb tb x n T idx
        (if i = 0 then (if (chain s cb tb x.length n T k).init then 4 + (s + cb + tb) + 1
          else 4 + (s + cb + tb))
        else chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + (i - 1)) =
        chainVal (chain s cb tb x.length n T k) idx i := by
      by_cases h₀ : i = 0
      · subst h₀
        cases h₁ : (chain s cb tb x.length n T k).init
        · simp only [↓reduceIte, Bool.false_eq_true, fieldVal_false, chainVal, cmp, pow_zero,
            Nat.mod_one, h₁]
          simp
        · simp only [↓reduceIte, fieldVal_true, chainVal, cmp, pow_zero, Nat.mod_one, h₁]
          simp
      · simp only [h₀, ↓reduceIte]
        rw [fieldVal_chain idx hk (by omega), Nat.sub_add_cancel (by omega)]
    rw [hprev, chainVal, chainVal, cmp_succ]
  · rw [treeGate]
    by_cases h₀ : ℓ = 0
    · subst h₀
      simp only [↓reduceIte]
      rw [consistentAt_const, fieldVal_tree idx hℓ hq]
      simp only [pow_zero, Nat.lt_one_iff] at hq
      simp [hq, Nat.mod_one]
    · simp only [h₀, ↓reduceIte]
      obtain ⟨ℓ, rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hlit : fieldVal s cb tb x n T idx (if q.testBit ℓ then 4 + ℓ else 4 + (s + cb + tb) + 2 +
          (4 + ℓ)) = decide ((idx / 16).testBit ℓ = q.testBit ℓ) := by
        have h16 : idx / 16 = idx / 2 ^ 4 := rfl
        rw [h16, Nat.testBit_div_two_pow, Nat.add_comm ℓ 4]
        split_ifs with hb
        · rw [fieldVal_input idx (by omega), hb]; cases idx.testBit (4 + ℓ) <;> rfl
        · rw [fieldVal_not idx (by omega)]
          simp only [Bool.not_eq_true] at hb
          rw [hb]; cases idx.testBit (4 + ℓ) <;> rfl
      rw [consistentAt_two, fieldVal_tree idx hℓ hq,
        fieldVal_tree idx (by omega) (Nat.mod_lt q (Nat.two_pow_pos ℓ)), hlit]
      simp only [Op.value, Bool.decide_and, mod_two_pow_succ_eq_iff hq]
  · rw [orGate, consistentAt_two, fieldVal_or idx]
    have hsel : fieldVal s cb tb x n T idx (if x.getD i false then
        treeBase (4 + (s + cb + tb)) (s + cb + tb) + (2 ^ Nat.size x.length - 1) + i
          else 4 + (s + cb + tb)) =
        (x.getD i false && decide (idx / 16 % 2 ^ Nat.size x.length = i)) := by
      split_ifs with hxi
      · rw [fieldVal_tree idx le_rfl (by omega), hxi, Bool.true_and]
      · simp only [Bool.not_eq_true] at hxi
        rw [fieldVal_false, hxi, Bool.false_and]
    rw [hsel]
    by_cases h₀ : i = 0
    · subst h₀
      simp only [↓reduceIte]
      rw [fieldVal_false]
      cases h : decide (idx / 16 % 2 ^ Nat.size x.length = 0) <;> simp_all [Op.value]
    · simp only [h₀, ↓reduceIte]
      rw [fieldVal_or idx]
      by_cases hlt : idx / 16 % 2 ^ Nat.size x.length < i
      · have h₁ : idx / 16 % 2 ^ Nat.size x.length ≤ i - 1 := by omega
        have h₂ : idx / 16 % 2 ^ Nat.size x.length ≠ i := by omega
        simp [Op.value, h₁, hlt.le, h₂]
      · by_cases heq : idx / 16 % 2 ^ Nat.size x.length = i
        · have h₁ : ¬ idx / 16 % 2 ^ Nat.size x.length ≤ i - 1 := by omega
          simp [Op.value, heq]
        · have h₁ : ¬ idx / 16 % 2 ^ Nat.size x.length ≤ i - 1 := by omega
          have h₂ : ¬ idx / 16 % 2 ^ Nat.size x.length ≤ i := by omega
          simp [Op.value, h₁, h₂, heq]

/-- **The field stage computes the intended values** of its wires on the bits of a clause
number. -/
theorem getD_evalCode_fieldGates (hm : Nat.size x.length ≤ s + cb + tb) (idx : ℕ) {w : ℕ}
    (hw : w < 4 + (s + cb + tb) + (fieldGates s cb tb x n T).length) :
    (evalCode interpretation false (List.ofFn fun i : Fin (4 + (s + cb + tb)) => idx.testBit i)
      (fieldGates s cb tb x n T)).getD w false = fieldVal s cb tb x n T idx w := by
  have h := getD_evalCode_of_allGates (allGates_wellFormedAt_fieldGates hm) _
    (allGates_consistentAt_fieldGates (n := n) (T := T) hm idx) hw
  rwa [show (List.ofFn fun i : Fin (4 + (s + cb + tb)) => fieldVal s cb tb x n T idx i) =
    List.ofFn fun i => idx.testBit i from
      congrArg List.ofFn (funext fun i => fieldVal_input idx i.isLt)] at h

end Correctness

end Cslib.Circuits.Boolean.Tableau.Decoder

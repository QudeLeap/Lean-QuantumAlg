/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Oracle
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import Mathlib.Data.Fintype.Fin

/-!
# Walsh-Hadamard transform and the XOR phase-query pipeline

The reusable machinery shared by the single-query Hadamard-oracle-Hadamard
algorithms (Deutsch-Jozsa, Bernstein-Vazirani): the `n`-qubit Hadamard layer
in Walsh-Hadamard closed form [dW19, qcnotes.tex:1005-1006], and the
XOR-oracle phase-query pipeline that runs a Boolean oracle on the uniform
input register with a `|−⟩` target.

The central bridge `postOracleState_eq_afterPhaseQuery_tensor` rewrites the
actual XOR-oracle query as the phase pattern `(√(2^n))⁻¹ ∑ x (-1)^{f x}|x⟩`
tensored with the unchanged `|−⟩` target, so a single query followed by the
second Hadamard layer (`finalJointState`) factors through the input-register
`finalState`.

These pieces sit in a `Primitives` module so the Deutsch-Jozsa and
Bernstein-Vazirani algorithms can both build on them without importing one
another; each algorithm keeps only its target-specific content (the
constant/balanced promise and amplitude test for Deutsch-Jozsa; Walsh-character
orthogonality and string recovery for Bernstein-Vazirani).

## Main definitions

- `QuantumAlg.WalshHadamard.Oracle n` — a Boolean function on `2^n` labels,
  queried mathematically through `xorOracleOp` and implemented through
  `Gate.xorOracle`.
- `QuantumAlg.WalshHadamard.walshSign` — the Walsh-Hadamard sign `(-1)^{x·y}`,
  and `hadamardLayerOperator` its closed-form `n`-qubit operator.
- `QuantumAlg.WalshHadamard.uniformState` — the uniform superposition.
- `QuantumAlg.WalshHadamard.finalJointState` — the post-circuit joint state,
  with `finalJointState_eq_finalState_tensor` factoring off the `|−⟩` target.
-/

section

namespace QuantumAlg

namespace WalshHadamard

open NormalizedVector Gate

noncomputable section

variable {n : ℕ}

/-- A Boolean oracle on `2^n` input labels. -/
public abbrev Oracle (n : ℕ) : Type := Fin (2 ^ n) → Bool

/-- The metadata-free XOR query operator for a Boolean oracle. -/
abbrev oracleOperator (f : Oracle n) : UnitaryOperator (Qubits (n + 1)) :=
  xorOracleOp f

/-- The standard sealed XOR query circuit for a Boolean oracle. -/
abbrev oracleGate (f : Oracle n) : UnitaryCircuit (Qubits (n + 1)) := Gate.xorOracle f

/-- The phase `(-1)^{f x}`, written as a complex scalar. -/
def phaseSign (f : Oracle n) (x : Fin (2 ^ n)) : ℂ :=
  if f x then -1 else 1

/-! ### The Walsh-Hadamard transform -/

/-- The bit of a basis label used in the Walsh-Hadamard character. The bit
order only affects nonzero rows; the zero row used by Deutsch-Jozsa is
independent of it. -/
def bit (x : Fin (2 ^ n)) (k : Fin n) : Bool := x.val.testBit k.val

/-- Parity of the bitwise inner product of two basis labels. -/
def dotParity (x y : Fin (2 ^ n)) : Bool :=
  Odd ((Finset.univ.filter fun k : Fin n => bit x k && bit y k).card)

/-- The Walsh-Hadamard sign `(-1)^{x · y}`. -/
def walshSign (x y : Fin (2 ^ n)) : ℂ := if dotParity x y then -1 else 1

/-- `(√(2^n))⁻¹`, the normalization scalar of the `n`-qubit Hadamard layer. -/
def invSqrtCard (n : ℕ) : ℂ := (Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ)⁻¹

@[simp]
theorem star_invSqrtCard (n : ℕ) : star (invSqrtCard n) = invSqrtCard n := by
  rw [invSqrtCard, star_inv₀, Complex.star_def, Complex.conj_ofReal]

@[simp]
theorem norm_invSqrtCard (n : ℕ) :
    ‖invSqrtCard n‖ = (Real.sqrt ((2 ^ n : ℕ) : ℝ))⁻¹ := by
  rw [invSqrtCard, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_sq_invSqrtCard (n : ℕ) :
    ‖invSqrtCard n‖ ^ 2 = (((2 ^ n : ℕ) : ℝ)⁻¹) := by
  rw [norm_invSqrtCard, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]

@[simp]
theorem walshSign_zero_left (x : Fin (2 ^ n)) :
    walshSign (0 : Fin (2 ^ n)) x = 1 := by
  unfold walshSign dotParity bit
  simp

@[simp]
theorem walshSign_zero_right (x : Fin (2 ^ n)) :
    walshSign x (0 : Fin (2 ^ n)) = 1 := by
  unfold walshSign dotParity bit
  simp

theorem dotParity_comm (x y : Fin (2 ^ n)) : dotParity x y = dotParity y x := by
  have hset : (Finset.univ.filter fun k : Fin n => bit x k && bit y k)
      = Finset.univ.filter fun k : Fin n => bit y k && bit x k := by
    apply Finset.filter_congr
    intro k _
    rw [Bool.and_comm]
  unfold dotParity
  rw [hset]

@[simp]
theorem bit_prodEquiv_zero (left : Fin (2 ^ n)) (right : Fin (2 ^ 1)) :
    bit (prodEquiv (m := n) (n := 1) (left, right)) 0 = bit right 0 := by
  exact prodEquiv_testBit_right left right 0

@[simp]
theorem bit_prodEquiv_succ (left : Fin (2 ^ n)) (right : Fin (2 ^ 1))
    (k : Fin n) :
    bit (prodEquiv (m := n) (n := 1) (left, right)) k.succ = bit left k := by
  simpa [bit, Nat.add_comm] using prodEquiv_testBit_left left right k

@[simp]
private theorem decide_even_eq_not_decide_odd (value : Nat) :
    decide (Even value) = !decide (Odd value) := by
  rw [← decide_not, decide_eq_decide, Nat.not_odd_iff_even]

/-- Appending one low qubit adds its Boolean product to the Walsh inner-product
parity. This pins the analytical bit convention to the structural tensor
convention used by `UnitaryCircuit.tensorQubits`. -/
theorem dotParity_prodEquiv (leftX leftY : Fin (2 ^ n))
    (rightX rightY : Fin (2 ^ 1)) :
    dotParity (prodEquiv (m := n) (n := 1) (leftX, rightX))
        (prodEquiv (m := n) (n := 1) (leftY, rightY)) =
      (dotParity leftX leftY ^^
        Bool.and (bit rightX 0) (bit rightY 0)) := by
  unfold dotParity
  rw [Fin.card_filter_univ_succ]
  simp only [bit_prodEquiv_zero, bit_prodEquiv_succ]
  cases hx : bit rightX 0 <;> cases hy : bit rightY 0 <;>
    simp [Nat.odd_add_one]

@[simp]
theorem dotParity_one (x y : Fin (2 ^ 1)) :
    dotParity x y = Bool.and (bit x 0) (bit y 0) := by
  unfold dotParity
  rw [Fin.card_filter_univ_succ]
  cases hx : bit x 0 <;> cases hy : bit y 0 <;> simp

/-- The Walsh character of a big-endian product label factors into the
characters of its high and low components. -/
theorem walshSign_prodEquiv (leftX leftY : Fin (2 ^ n))
    (rightX rightY : Fin (2 ^ 1)) :
    walshSign (prodEquiv (m := n) (n := 1) (leftX, rightX))
        (prodEquiv (m := n) (n := 1) (leftY, rightY)) =
      walshSign leftX leftY * walshSign rightX rightY := by
  unfold walshSign
  rw [dotParity_prodEquiv, dotParity_one]
  cases hleft : dotParity leftX leftY <;>
    cases hright : Bool.and (bit rightX 0) (bit rightY 0) <;>
    simp

theorem walshSign_comm (x y : Fin (2 ^ n)) : walshSign x y = walshSign y x := by
  unfold walshSign
  rw [dotParity_comm]

@[simp]
theorem walshSign_mul_self (x y : Fin (2 ^ n)) :
    walshSign x y * walshSign x y = 1 := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

@[simp]
theorem star_walshSign (x y : Fin (2 ^ n)) :
    star (walshSign x y) = walshSign x y := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

@[simp]
theorem norm_walshSign (x y : Fin (2 ^ n)) : ‖walshSign x y‖ = 1 := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

/-! ### Walsh-character orthogonality -/

/-- Flip bit `k` of a basis label. -/
def flipBit (x : Fin (2 ^ n)) (k : Fin n) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ k.val,
    Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right one_lt_two k.isLt)⟩

theorem bit_flipBit (x : Fin (2 ^ n)) (k k' : Fin n) :
    bit (flipBit x k) k' = (bit x k' ^^ decide (k = k')) := by
  change (x.val ^^^ 2 ^ k.val).testBit k'.val = (bit x k' ^^ decide (k = k'))
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  rw [decide_eq_decide]
  exact Fin.val_inj

theorem flipBit_flipBit (x : Fin (2 ^ n)) (k : Fin n) :
    flipBit (flipBit x k) k = x := by
  unfold flipBit
  ext
  simp

theorem flipBit_ne (x : Fin (2 ^ n)) (k : Fin n) : flipBit x k ≠ x := by
  intro h
  have hb := congrArg (fun y : Fin (2 ^ n) => bit y k) h
  simp [bit_flipBit] at hb

/-- Flipping bit `k` of `x` toggles the parity `x · z` exactly when bit `k`
of `z` is set. -/
theorem dotParity_flipBit (x z : Fin (2 ^ n)) (k : Fin n) :
    dotParity (flipBit x k) z = (dotParity x z ^^ bit z k) := by
  unfold dotParity
  cases hz : bit z k
  · rw [Bool.xor_false]
    have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
        = Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
      apply Finset.filter_congr
      intro k' _
      rcases eq_or_ne k k' with rfl | hk
      · simp [bit_flipBit, hz]
      · simp [bit_flipBit, hk]
    rw [hset]
  · rw [Bool.xor_true]
    by_cases hx : bit x k
    · have hmem : k ∈ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx, hz]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k').erase k := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, ← decide_not, decide_eq_decide,
        ← Finset.card_erase_add_one hmem, Nat.odd_add_one, not_not]
    · have hnot : k ∉ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = insert k (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k') := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx, hz]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, Finset.card_insert_of_notMem hnot, ← decide_not,
        decide_eq_decide, Nat.odd_add_one]

/-- Two distinct labels differ at some bit. -/
theorem exists_bit_ne {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∃ k : Fin n, bit y k ≠ bit s k := by
  by_contra hall
  push Not at hall
  refine h (Fin.val_injective (Nat.eq_of_testBit_eq fun i => ?_))
  by_cases hi : i < n
  · exact hall ⟨i, hi⟩
  · push Not at hi
    have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    have hs : s.val < 2 ^ i := lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    rw [Nat.testBit_lt_two_pow hy, Nat.testBit_lt_two_pow hs]

private theorem if_xor_true (a : Bool) :
    (if (a ^^ true) = true then (-1 : ℂ) else 1) = -(if a = true then -1 else 1) := by
  cases a <;> simp

/-- Flipping a bit on which `y` and `s` disagree negates the product of their
Walsh signs. -/
theorem walshSign_mul_walshSign_flipBit {y s : Fin (2 ^ n)} {k : Fin n}
    (hk : bit y k ≠ bit s k) (x : Fin (2 ^ n)) :
    walshSign y (flipBit x k) * walshSign s (flipBit x k)
      = -(walshSign y x * walshSign s x) := by
  unfold walshSign
  simp only [dotParity_comm y (flipBit x k), dotParity_comm s (flipBit x k),
    dotParity_flipBit, dotParity_comm x y, dotParity_comm x s]
  cases hy : bit y k <;> cases hs : bit s k
  · exact absurd (hy.trans hs.symm) hk
  · rw [Bool.xor_false, if_xor_true]
    ring
  · rw [Bool.xor_false, if_xor_true]
    ring
  · exact absurd (hy.trans hs.symm) hk

/-- Walsh-character orthogonality: for `y ≠ s` the signed sum over all basis
labels cancels in pairs under the bit-flip involution. -/
theorem sum_walshSign_mul_walshSign {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∑ x, walshSign y x * walshSign s x = 0 := by
  obtain ⟨k, hk⟩ := exists_bit_ne h
  refine Finset.sum_involution (fun x _ => flipBit x k)
    (fun x _ => ?_) (fun x _ _ => flipBit_ne x k)
    (fun x _ => Finset.mem_univ _) (fun x _ => flipBit_flipBit x k)
  rw [walshSign_mul_walshSign_flipBit hk x]
  ring

theorem sum_walshSign_mul_walshSign_eq (y s : Fin (2 ^ n)) :
    ∑ x, walshSign y x * walshSign s x =
      if y = s then ((2 ^ n : ℕ) : ℂ) else 0 := by
  by_cases hys : y = s
  · subst hys
    rw [if_pos rfl]
    simp only [walshSign_mul_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · rw [if_neg hys, sum_walshSign_mul_walshSign hys]

@[simp]
theorem invSqrtCard_mul_self (n : ℕ) :
    invSqrtCard n * invSqrtCard n = (((2 ^ n : ℕ) : ℂ)⁻¹) := by
  rw [invSqrtCard, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]
  norm_num

/-- The Walsh normalization factors multiplicatively when one low qubit is
appended to the register. -/
theorem invSqrtCard_succ (n : ℕ) :
    invSqrtCard (n + 1) = invSqrtCard n * invSqrt2 := by
  rw [invSqrtCard, invSqrtCard, invSqrt2]
  rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]
  norm_num
  ac_rfl

/-- A Boolean phase has unit norm. -/
@[simp]
theorem norm_phaseSign (f : Oracle n) (x : Fin (2 ^ n)) :
    ‖phaseSign f x‖ = 1 := by
  unfold phaseSign
  by_cases h : f x <;> simp [h]

/-- Certified metadata-free Walsh-Hadamard operator. -/
def hadamardLayerOperator (n : ℕ) : UnitaryOperator (Qubits n) :=
  let op : HilbertOperator (Qubits n) :=
    fun y x => invSqrtCard n * walshSign y x
  UnitaryOperator.ofMatrix op
    (by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext y s
      rw [Matrix.mul_apply]
      calc
        ∑ x, (invSqrtCard n * walshSign y x) *
              star (invSqrtCard n * walshSign s x)
            = ∑ x, (invSqrtCard n * invSqrtCard n) *
                (walshSign y x * walshSign s x) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [star_mul, star_invSqrtCard, star_walshSign]
              ring
        _ = (invSqrtCard n * invSqrtCard n) *
              ∑ x, walshSign y x * walshSign s x := by
              rw [Finset.mul_sum]
        _ = (((2 ^ n : ℕ) : ℂ)⁻¹) *
              (if y = s then ((2 ^ n : ℕ) : ℂ) else 0) := by
              rw [invSqrtCard_mul_self, sum_walshSign_mul_walshSign_eq]
        _ = (1 : HilbertOperator (Qubits n)) y s := by
              by_cases hys : y = s
              · subst s
                rw [if_pos rfl, Matrix.one_apply_eq]
                exact inv_mul_cancel₀
                  (Nat.cast_ne_zero.mpr (pow_ne_zero n two_ne_zero))
              · rw [if_neg hys, Matrix.one_apply_ne hys, mul_zero])

@[simp]
theorem hadamardLayerOperator_apply (n : ℕ) (y x : Fin (2 ^ n)) :
    hadamardLayerOperator n y x = invSqrtCard n * walshSign y x := rfl



/-- Strict event coordinate emitted by one sealed Hadamard leaf. -/
def hadamardEvent : Resource.Event .quantum :=
  .gate (.builtin "hadamard")

/-- Strict event coordinate emitted by one XOR-oracle query. -/
def xorOracleEvent (n : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (xorOracleSubroutineLabel n).quantum

/-- Strict event critical path of a parallel layer of Hadamard leaves. -/
def parallelHadamardEventDepth : (n : ℕ) → DepthExpr (Resource.Event .quantum)
  | 0 => .id
  | n + 1 =>
      .tensor (parallelHadamardEventDepth n) (.atom hadamardEvent)

/-- Ordered strict events of a parallel Hadamard layer. -/
def parallelHadamardEventTrace : (n : Nat) → List (Resource.Event .quantum)
  | 0 => []
  | n + 1 => parallelHadamardEventTrace n ++ [hadamardEvent]

theorem hadamardCircuit_eventTrace :
    Gate.H.eventTrace = [hadamardEvent] :=
  rfl

theorem hadamardCircuit_eventCost :
    Gate.H.eventCost = ResourcePool.singleton hadamardEvent :=
  rfl

theorem hadamardCircuit_eventDepth :
    Gate.H.eventDepth = .atom hadamardEvent :=
  rfl

/-- Recursive parallel tensor of one declared Hadamard primitive per logical
qubit, together with its canonical physical layout. -/
def parallelHadamardCircuitData :
    (n : ℕ) → { circuit : UnitaryCircuit (Qubits n) // circuit.physical_idx = List.range n }
  | 0 =>
      ⟨UnitaryCircuit.identity (Qubits 0) [] (by simp), rfl⟩
  | n + 1 => by
      let left := parallelHadamardCircuitData n
      let right := UnitaryCircuit.shiftPhysicalIdx n Gate.H
      let layout : PhysicalLayout.DisjointMerge left.val.physical_idx right.physical_idx :=
        { left_nodup := left.val.physical_idx_nodup
          right_nodup := right.physical_idx_nodup
          disjoint := by
            rw [left.property]
            simp [right, UnitaryCircuit.shiftPhysicalIdx_physical_idx, Gate.H_system_idx] }
      let circuit := UnitaryCircuit.tensorQubits left.val right layout
      refine ⟨circuit, ?_⟩
      change layout.merged = List.range (n + 1)
      rw [PhysicalLayout.DisjointMerge.merged_eq_append]
      rw [left.property]
      simp [right, UnitaryCircuit.shiftPhysicalIdx_physical_idx, Gate.H_system_idx,
        List.range_succ]

/-- The actual `n`-qubit Hadamard layer: a parallel tensor of `n` sealed
single-qubit Hadamard leaves. -/
def parallelHadamardCircuit (n : ℕ) : UnitaryCircuit (Qubits n) :=
  (parallelHadamardCircuitData n).val

@[simp]
theorem parallelHadamardCircuit_physical_idx (n : ℕ) :
    (parallelHadamardCircuit n).physical_idx = List.range n :=
  (parallelHadamardCircuitData n).property





/-- The strict event pool of the parallel Hadamard circuit records exactly
one Hadamard event per logical qubit. -/
@[simp]
theorem parallelHadamardCircuit_eventCost (n : ℕ) :
    (parallelHadamardCircuit n).eventCost =
      ResourcePool.singleton hadamardEvent n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [parallelHadamardCircuit, parallelHadamardCircuitData,
        UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex_eventCost,
        UnitaryCircuit.tensor_eventCost, UnitaryCircuit.shiftPhysicalIdx_eventCost,
        hadamardCircuit_eventCost]
      change (parallelHadamardCircuit n).eventCost +
          ResourcePool.singleton hadamardEvent =
        ResourcePool.singleton hadamardEvent (n + 1)
      rw [ih, Multiset.add_comm]
      simp [ResourcePool.singleton, Multiset.replicate_succ]

/-- The strict event critical path of the parallel Hadamard circuit retains
its tensor structure rather than flattening it into a legacy unit-depth view. -/
@[simp]
theorem parallelHadamardCircuit_eventDepth (n : ℕ) :
    (parallelHadamardCircuit n).eventDepth = parallelHadamardEventDepth n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [parallelHadamardCircuit, parallelHadamardCircuitData,
        UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex_eventDepth,
        UnitaryCircuit.tensor_eventDepth, UnitaryCircuit.shiftPhysicalIdx_eventDepth,
        hadamardCircuit_eventDepth, parallelHadamardEventDepth]
      change DepthExpr.tensor (parallelHadamardCircuit n).eventDepth
          (DepthExpr.atom hadamardEvent) =
        DepthExpr.tensor (parallelHadamardEventDepth n)
          (DepthExpr.atom hadamardEvent)
      rw [ih]

/-- The recursive tensor circuit exposes one ordered Hadamard event per
logical qubit. -/
@[simp]
theorem parallelHadamardCircuit_eventTrace (n : Nat) :
    (parallelHadamardCircuit n).eventTrace = parallelHadamardEventTrace n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [parallelHadamardCircuit, parallelHadamardCircuitData,
        UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex_eventTrace,
        UnitaryCircuit.tensor_eventTrace, UnitaryCircuit.shiftPhysicalIdx_eventTrace,
        hadamardCircuit_eventTrace, parallelHadamardEventTrace]
      change (parallelHadamardCircuit n).eventTrace ++ [hadamardEvent] =
        parallelHadamardEventTrace (n + 1)
      rw [ih]
      rfl

/-- Any strict event assignment giving the literal Hadamard event unit
duration makes a nonempty parallel Hadamard block one layer deep. -/
theorem parallelHadamardEventDepth_eval (n : ℕ)
    (assign : Resource.Event .quantum → Nat)
    (hHadamard : assign hadamardEvent = 1) :
    DepthExpr.depthEval assign (parallelHadamardEventDepth n) =
      if n = 0 then 0 else 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases h : n = 0 <;>
        simp [parallelHadamardEventDepth, ih, h, hHadamard]

/-- Unit event durations give one layer for every nonempty parallel strict
Hadamard block and zero layers for the empty block. -/
@[simp]
theorem parallelHadamardEventDepth_unit_depth (n : ℕ) :
    DepthExpr.depthEval (fun _ => 1) (parallelHadamardEventDepth n) =
      if n = 0 then 0 else 1 :=
  parallelHadamardEventDepth_eval n (fun _ => 1) rfl

/-- The recursive tensor circuit implements the closed-form Walsh-Hadamard
operator. This is the semantic bridge that keeps the analytical correctness
proofs and the structurally derived resource ledger on the same circuit. -/
@[simp]
theorem parallelHadamardCircuit_matrix (n : ℕ) :
    (parallelHadamardCircuit n).matrix = hadamardLayerOperator n := by
  induction n with
  | zero =>
      ext i j
      fin_cases i
      fin_cases j
      norm_num [parallelHadamardCircuit, parallelHadamardCircuitData,
        invSqrtCard, walshSign, dotParity, bit]
  | succ n ih =>
      ext i j
      rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨iLeft, iRight⟩, rfl⟩
      rcases (prodEquiv (m := n) (n := 1)).surjective j with ⟨⟨jLeft, jRight⟩, rfl⟩
      simp only [parallelHadamardCircuit, parallelHadamardCircuitData,
        UnitaryCircuit.tensorQubits_matrix, UnitaryCircuit.shiftPhysicalIdx_matrix, Gate.H_matrix,
        UnitaryOperator.tensor_apply, Equiv.symm_apply_apply]
      change (parallelHadamardCircuit n).matrix iLeft jLeft * HOp iRight jRight =
        hadamardLayerOperator (n + 1)
          (prodEquiv (m := n) (n := 1) (iLeft, iRight))
          (prodEquiv (m := n) (n := 1) (jLeft, jRight))
      rw [ih, hadamardLayerOperator_apply, hadamardLayerOperator_apply,
        invSqrtCard_succ, walshSign_prodEquiv]
      fin_cases iRight <;> fin_cases jRight <;> simp [HOp, walshSign, dotParity, bit]



/-- The `n`-qubit Hadamard layer as the actual recursive tensor circuit. -/
def hadamardLayer (n : ℕ) : UnitaryCircuit (Qubits n) :=
  parallelHadamardCircuit n

@[simp]
theorem hadamardLayer_physical_idx (n : ℕ) :
    (hadamardLayer n).physical_idx = List.range n :=
  parallelHadamardCircuit_physical_idx n

@[simp]
theorem hadamardLayer_matrix (n : ℕ) :
    (hadamardLayer n).matrix = hadamardLayerOperator n :=
  parallelHadamardCircuit_matrix n





/-- The strict event pool of the reusable Hadamard layer. -/
@[simp]
theorem hadamardLayer_eventCost (n : ℕ) :
    (hadamardLayer n).eventCost = ResourcePool.singleton hadamardEvent n :=
  parallelHadamardCircuit_eventCost n

/-- The strict event critical path of the reusable Hadamard layer. -/
@[simp]
theorem hadamardLayer_eventDepth (n : ℕ) :
    (hadamardLayer n).eventDepth = parallelHadamardEventDepth n :=
  parallelHadamardCircuit_eventDepth n

/-- Ordered strict execution events of the reusable Hadamard layer. -/
@[simp]
theorem hadamardLayer_eventTrace (n : Nat) :
    (hadamardLayer n).eventTrace = parallelHadamardEventTrace n :=
  parallelHadamardCircuit_eventTrace n

/-- The uniform normalized vector produced by the first Hadamard layer. -/
def uniformState (n : ℕ) : NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 fun _ => invSqrtCard n)
    (by
      rw [EuclideanSpace.norm_eq]
      have hsum :
          ∑ _i : Fin (2 ^ n), ‖invSqrtCard n‖ ^ 2 = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, norm_sq_invSqrtCard]
        norm_num
      rw [hsum, Real.sqrt_one])

@[simp]
theorem uniformState_apply (x : Fin (2 ^ n)) : uniformState n x = invSqrtCard n :=
  rfl

/-- The metadata-free Hadamard operator sends `|0^n⟩` to the uniform
superposition. -/
@[simp]
theorem hadamardLayerOperator_apply_zero :
    (hadamardLayerOperator n).apply
        (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n))) =
      uniformState n := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec (hadamardLayerOperator n : HilbertOperator (Qubits n))
      (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
        HilbertVector (Qubits n)) i = _
  rw [HilbertOperator.applyVec_ket]
  rw [hadamardLayerOperator_apply]
  simp [walshSign, dotParity, bit]

/-! ### The XOR phase-query pipeline -/

/-- Normalized algorithm input `|0^n⟩ ⊗ |1⟩`. The target Hadamard that
prepares `|−⟩` is part of the circuit rather than hidden in the input. -/
def input (n : ℕ) : NormalizedVector (Qubits (n + 1)) :=
  (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n))).tensor ket1

/-- Metadata-free first Hadamard layer. -/
def initialHadamardOperator (n : ℕ) : UnitaryOperator (Qubits (n + 1)) :=
  (hadamardLayerOperator n).tensor HOp

/-- First circuit layer: `H` on all input qubits and on the target qubit. -/
def initialHadamardLayer (n : ℕ) : UnitaryCircuit (Qubits (n + 1)) := by
  let left := hadamardLayer n
  let right := UnitaryCircuit.shiftPhysicalIdx n Gate.H
  let layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx :=
    { left_nodup := left.physical_idx_nodup
      right_nodup := right.physical_idx_nodup
      disjoint := by
        simp [left, right, UnitaryCircuit.shiftPhysicalIdx_physical_idx,
          Gate.H_system_idx, hadamardLayer, parallelHadamardCircuit_physical_idx] }
  exact UnitaryCircuit.tensorQubits left right layout

@[simp]
theorem initialHadamardLayer_physical_idx (n : ℕ) :
    (initialHadamardLayer n).physical_idx = List.range (n + 1) := by
  change (hadamardLayer n).physical_idx ++
      (UnitaryCircuit.shiftPhysicalIdx n Gate.H).physical_idx = List.range (n + 1)
  rw [hadamardLayer_physical_idx, UnitaryCircuit.shiftPhysicalIdx_physical_idx]
  simp [Gate.H_system_idx, List.range_succ]

@[simp]
theorem initialHadamardLayer_matrix (n : ℕ) :
    (initialHadamardLayer n).matrix = initialHadamardOperator n := by
  simp [initialHadamardLayer, initialHadamardOperator]





/-- Exact strict event pool of the initial parallel Hadamard layer. -/
@[simp]
theorem initialHadamardLayer_eventCost (n : ℕ) :
    (initialHadamardLayer n).eventCost =
      ResourcePool.singleton hadamardEvent (n + 1) := by
  simp only [initialHadamardLayer, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.shiftPhysicalIdx_eventCost, hadamardLayer_eventCost,
    hadamardCircuit_eventCost]
  rw [Multiset.add_comm]
  simp [ResourcePool.singleton, Multiset.replicate_succ]

/-- Exact strict event critical path of the initial Hadamard layer. -/
@[simp]
theorem initialHadamardLayer_eventDepth (n : ℕ) :
    (initialHadamardLayer n).eventDepth =
      .tensor (parallelHadamardEventDepth n) (.atom hadamardEvent) := by
  simp only [initialHadamardLayer, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
    UnitaryCircuit.shiftPhysicalIdx_eventDepth, hadamardLayer_eventDepth,
    hadamardCircuit_eventDepth]

/-- Ordered strict execution events of the initial Hadamard layer. -/
@[simp]
theorem initialHadamardLayer_eventTrace (n : Nat) :
    (initialHadamardLayer n).eventTrace =
      parallelHadamardEventTrace n ++ [hadamardEvent] := by
  simp only [initialHadamardLayer, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventTrace, UnitaryCircuit.tensor_eventTrace,
    UnitaryCircuit.shiftPhysicalIdx_eventTrace, hadamardLayer_eventTrace,
    hadamardCircuit_eventTrace]

/-- Metadata-free final Hadamard layer. -/
def finalHadamardOperator (n : ℕ) : UnitaryOperator (Qubits (n + 1)) :=
  (hadamardLayerOperator n).tensor (1 : UnitaryOperator (Qubits 1))

/-- Final circuit layer: `H` on the input register and identity on the target. -/
def finalHadamardLayer (n : ℕ) : UnitaryCircuit (Qubits (n + 1)) := by
  let left := hadamardLayer n
  let right := UnitaryCircuit.identity (Qubits 1) [n] (by simp)
  let layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx :=
    { left_nodup := left.physical_idx_nodup
      right_nodup := right.physical_idx_nodup
      disjoint := by
        have hleft : left.physical_idx = List.range n := by
          simp [left]
        have hright : right.physical_idx = [n] := rfl
        rw [hleft, hright]
        simp }
  exact UnitaryCircuit.tensorQubits left right layout

@[simp]
theorem finalHadamardLayer_physical_idx (n : ℕ) :
    (finalHadamardLayer n).physical_idx = List.range (n + 1) := by
  change (hadamardLayer n).physical_idx ++ [n] = List.range (n + 1)
  rw [hadamardLayer_physical_idx]
  simpa only [Nat.succ_eq_add_one] using (List.range_succ (n := n)).symm

@[simp]
theorem finalHadamardLayer_matrix (n : ℕ) :
    (finalHadamardLayer n).matrix = finalHadamardOperator n := by
  simp only [finalHadamardLayer, UnitaryCircuit.tensorQubits_matrix,
    hadamardLayer_matrix]
  rfl





/-- Exact strict event pool of the final Hadamard layer. -/
@[simp]
theorem finalHadamardLayer_eventCost (n : ℕ) :
    (finalHadamardLayer n).eventCost =
      ResourcePool.singleton hadamardEvent n := by
  simp only [finalHadamardLayer, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    hadamardLayer_eventCost, UnitaryCircuit.identity_eventCost, add_zero]

/-- Exact strict event critical path of the final Hadamard layer. -/
@[simp]
theorem finalHadamardLayer_eventDepth (n : ℕ) :
    (finalHadamardLayer n).eventDepth =
      .tensor (parallelHadamardEventDepth n) .id := by
  simp only [finalHadamardLayer, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
    hadamardLayer_eventDepth, UnitaryCircuit.identity_eventDepth]

/-- Ordered strict execution events of the final Hadamard layer. -/
@[simp]
theorem finalHadamardLayer_eventTrace (n : Nat) :
    (finalHadamardLayer n).eventTrace = parallelHadamardEventTrace n := by
  simp only [finalHadamardLayer, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventTrace, UnitaryCircuit.tensor_eventTrace,
    hadamardLayer_eventTrace, UnitaryCircuit.identity_eventTrace, List.append_nil]

/-- The joint state queried by the XOR oracle, obtained by applying the first
Hadamard layer to `|0^n⟩ ⊗ |1⟩`. -/
def initialState (n : ℕ) : NormalizedVector (Qubits (n + 1)) :=
  (initialHadamardOperator n).apply (input n)

/-- The queried state is the uniform input register tensored with `|−⟩`. -/
theorem initialState_eq_uniform_tensor :
    initialState n = (uniformState n).tensor ketMinus := by
  have hH : HOp.apply ket1 = ketMinus := by
    simpa only [UnitaryCircuit.applyNormalized, H_matrix] using H_apply_ket1
  rw [initialState, input, initialHadamardOperator,
    UnitaryOperator.tensor_apply_tensor, hadamardLayerOperator_apply_zero, hH]

/-- The post-query normalized joint state under the metadata-free XOR oracle. -/
def postOracleState (f : Oracle n) : NormalizedVector (Qubits (n + 1)) :=
  (oracleOperator f).apply (initialState n)

/-- Normalized input-register vector after the phase query. -/
def afterPhaseQuery (f : Oracle n) : NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 fun x => invSqrtCard n * phaseSign f x)
    (by
      rw [EuclideanSpace.norm_eq]
      have hsum :
          ∑ x : Fin (2 ^ n), ‖invSqrtCard n * phaseSign f x‖ ^ 2 = 1 := by
        calc
          ∑ x : Fin (2 ^ n), ‖invSqrtCard n * phaseSign f x‖ ^ 2
              = ∑ _x : Fin (2 ^ n), ‖invSqrtCard n‖ ^ 2 := by
                  refine Finset.sum_congr rfl fun x _ => ?_
                  rw [norm_mul, norm_phaseSign, mul_one]
          _ = 1 := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul, norm_sq_invSqrtCard]
                  norm_num
      rw [hsum, Real.sqrt_one])

@[simp]
theorem afterPhaseQuery_apply (f : Oracle n) (x : Fin (2 ^ n)) :
    afterPhaseQuery f x = invSqrtCard n * phaseSign f x := rfl

/-- The actual XOR-oracle query on the uniform input register and `|−⟩`
target is exactly the phase-query state tensored with the unchanged target. -/
theorem postOracleState_eq_afterPhaseQuery_tensor (f : Oracle n) :
    postOracleState f = (afterPhaseQuery f).tensor ketMinus := by
  apply NormalizedVector.ext
  intro i
  change (oracleOperator f).applyVec (initialState n : HilbertVector (Qubits (n + 1))) i =
    (((afterPhaseQuery f).tensor ketMinus : NormalizedVector (Qubits (n + 1))) :
      HilbertVector (Qubits (n + 1))) i
  rw [initialState_eq_uniform_tensor]
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨x, b⟩, rfl⟩
  rw [xorOracleOp_apply, NormalizedVector.tensor_apply_prod,
    NormalizedVector.tensor_apply_prod]
  simp only [Equiv.symm_apply_apply, xorPerm_apply]
  by_cases h : f x
  · fin_cases b <;> simp [h, phaseSign, ketMinus_apply]
  · simp [h, phaseSign, ketMinus_apply]

/-- The normalized final input-register state after the second Hadamard layer. -/
def finalState (f : Oracle n) : NormalizedVector (Qubits n) :=
  (hadamardLayerOperator n).apply (afterPhaseQuery f)

/-- The actual final joint state: apply the second Hadamard layer to the
input register and leave the target qubit alone. -/
def finalJointState (f : Oracle n) : NormalizedVector (Qubits (n + 1)) :=
  (finalHadamardOperator n).apply (postOracleState f)

/-- The actual final joint state factors as the final input-register state
and the unchanged `|−⟩` target. -/
theorem finalJointState_eq_finalState_tensor (f : Oracle n) :
    finalJointState f = (finalState f).tensor ketMinus := by
  have hOne : (1 : UnitaryOperator (Qubits 1)).apply ketMinus = ketMinus := by
    apply NormalizedVector.ext
    intro i
    change (1 : UnitaryOperator (Qubits 1)).applyVec
        (ketMinus : HilbertVector (Qubits 1)) i = ketMinus i
    rw [UnitaryOperator.one_applyVec]
  rw [finalJointState, postOracleState_eq_afterPhaseQuery_tensor,
    finalHadamardOperator, UnitaryOperator.tensor_apply_tensor, finalState, hOne]

/-! ### Typed circuit and derived resources -/

/-- The shared three-layer circuit used by Deutsch-Jozsa and
Bernstein-Vazirani. -/
def circuit (f : Oracle n) : UnitaryCircuit (Qubits (n + 1)) :=
  UnitaryCircuit.seq
    (UnitaryCircuit.seq
      (initialHadamardLayer n)
      (oracleGate f))
    (finalHadamardLayer n)

@[simp]
theorem circuit_physical_idx (f : Oracle n) :
    (circuit f).physical_idx = List.range (n + 1) := by
  simp only [circuit, UnitaryCircuit.seq, initialHadamardLayer_physical_idx,
    finalHadamardLayer_physical_idx, oracleGate, Gate.xorOracle,
    UnitaryCircuit.ofLeaf, Gate.xorOracleLeaf, Gate.xorOracleLeafAt,
    UnitaryLeaf.subroutine_systemIdx]
  rw [UnitaryCircuit.unionPhysicalIdx_self, UnitaryCircuit.unionPhysicalIdx_self]



/-- Exact strict event pool of the shared Deutsch-Jozsa and
Bernstein-Vazirani circuit. -/
def eventPool (n : ℕ) : ResourcePool .quantum :=
  (ResourcePool.singleton hadamardEvent (n + 1) +
    ResourcePool.singleton (xorOracleEvent n)) +
    ResourcePool.singleton hadamardEvent n

/-- Exact strict symbolic critical path of the shared three-layer circuit. -/
def eventCriticalPath (n : ℕ) : DepthExpr (Resource.Event .quantum) :=
  .seq
    (.seq
      (.tensor (parallelHadamardEventDepth n) (.atom hadamardEvent))
      (.atom (xorOracleEvent n)))
    (.tensor (parallelHadamardEventDepth n) .id)

/-- Ordered strict execution trace of the shared three-layer circuit. -/
def executionEventTrace (n : Nat) : List (Resource.Event .quantum) :=
  (parallelHadamardEventTrace n ++ [hadamardEvent]) ++
    [xorOracleEvent n] ++ parallelHadamardEventTrace n

theorem oracleGate_eventTrace (f : Oracle n) :
    (oracleGate f).eventTrace = [xorOracleEvent n] :=
  rfl

theorem oracleGate_eventCost (f : Oracle n) :
    (oracleGate f).eventCost = ResourcePool.singleton (xorOracleEvent n) :=
  rfl

theorem oracleGate_eventDepth (f : Oracle n) :
    (oracleGate f).eventDepth = .atom (xorOracleEvent n) :=
  rfl

/-- The typed circuit computes the same final state used by both correctness
proofs. -/
@[simp]
theorem circuit_applyNormalized (f : Oracle n) :
    UnitaryCircuit.applyNormalized (circuit f) (input n) = finalJointState f := by
  apply NormalizedVector.ext
  intro i
  change UnitaryCircuit.applyVec (circuit f)
      (input n : HilbertVector (Qubits (n + 1))) i =
    (finalJointState f : HilbertVector (Qubits (n + 1))) i
  rw [circuit, UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq]
  simp only [UnitaryCircuit.applyVec, initialHadamardLayer_matrix,
    finalHadamardLayer_matrix, Gate.xorOracle_matrix]
  rw [finalJointState, postOracleState, initialState]
  rfl



/-- The shared Deutsch-Jozsa and Bernstein-Vazirani circuit has the exact
strict event pool obtained from its own three-layer syntax. -/
@[simp]
theorem circuit_eventCost (f : Oracle n) :
    (circuit f).eventCost = eventPool n := by
  simp only [circuit, UnitaryCircuit.seq_eventCost, initialHadamardLayer_eventCost,
    oracleGate_eventCost, finalHadamardLayer_eventCost, eventPool]

/-- The shared Deutsch-Jozsa and Bernstein-Vazirani circuit has the exact
strict event critical path obtained from that same syntax. -/
@[simp]
theorem circuit_eventDepth (f : Oracle n) :
    (circuit f).eventDepth = eventCriticalPath n := by
  simp only [circuit, UnitaryCircuit.seq_eventDepth, initialHadamardLayer_eventDepth,
    oracleGate_eventDepth, finalHadamardLayer_eventDepth, eventCriticalPath]

/-- The shared circuit's ordered strict execution trace is derived from the
same initial, oracle, and final circuit blocks. -/
@[simp]
theorem circuit_eventTrace (f : Oracle n) :
    (circuit f).eventTrace = executionEventTrace n := by
  simp only [circuit, UnitaryCircuit.seq_eventTrace,
    initialHadamardLayer_eventTrace, oracleGate_eventTrace,
    finalHadamardLayer_eventTrace, executionEventTrace]

/-- Unit event durations recover the exact two- or three-layer strict circuit
critical path, including the degenerate empty input register. -/
@[simp]
theorem eventCriticalPath_unit_depth (n : ℕ) :
    DepthExpr.depthEval (fun _ => 1) (eventCriticalPath n) =
      if n = 0 then 2 else 3 := by
  by_cases h : n = 0 <;>
    simp [eventCriticalPath, h]

/-- Linearizing the shared circuit's strict event critical path yields its
exact strict event pool. -/
theorem circuit_resourcesFromEventDepth (f : Oracle n) :
    (circuit f).resourcesFromEventDepth = eventPool n := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost, circuit_eventCost]

/-- The strict event pool of the shared Deutsch-Jozsa and Bernstein-Vazirani
circuit contains exactly `2 * n + 1` Hadamard events. -/
theorem circuit_eventCost_hadamard_count (f : Oracle n) :
    ResourcePool.count hadamardEvent (circuit f).eventCost = 2 * n + 1 := by
  have different : hadamardEvent ≠ xorOracleEvent n := by
    simp [hadamardEvent, xorOracleEvent]
  rw [circuit_eventCost]
  simp [eventPool, ResourcePool.count_singleton_of_ne different]
  omega

/-- The strict event pool of the shared Deutsch-Jozsa and Bernstein-Vazirani
circuit contains exactly one XOR-oracle query event. -/
theorem circuit_eventCost_xorOracle_count (f : Oracle n) :
    ResourcePool.count (xorOracleEvent n) (circuit f).eventCost = 1 := by
  have different : xorOracleEvent n ≠ hadamardEvent := by
    simp [hadamardEvent, xorOracleEvent]
  rw [circuit_eventCost]
  simp [eventPool, ResourcePool.count_singleton_of_ne different]







end

end WalshHadamard

end QuantumAlg

end

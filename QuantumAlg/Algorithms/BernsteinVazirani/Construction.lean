/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Util.FinPow

import all QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Primitives.WalshHadamard.Uniform
import all QuantumAlg.Primitives.WalshHadamard.Pipeline
import all QuantumAlg.Primitives.WalshHadamard.Initialization
import all QuantumAlg.Primitives.WalshHadamard.Initialization.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

public import QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Bernstein-Vazirani character orthogonality and exact recovery

For every n and hidden string s, the oracle is the parity inner product
`x dot s mod 2` [dW19, qcnotes.tex:1282-1283]. The shared Walsh-Hadamard circuit
produces exactly `|s> tensor |->`, and the mathematical readout recovers the
big-endian encoding of s with probability one [dW19, qcnotes.tex:1288-1297].

The original involution proof of character orthogonality and the exact
all-width state theorem remain here. Canonical layout and readout geometry
belong to the shared primitive. The endpoint separately proves that these
mathematical probabilities are observations of its actual execution.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

variable {n : ℕ}

namespace BernsteinVazirani

open WalshHadamard WalshHadamard.Readout

/-- The Bernstein-Vazirani oracle for hidden string `s`: the inner-product
function `x ↦ x · s mod 2` [dW19, qcnotes.tex:1283], queried through
`Gate.xorOracle` like any Deutsch-Jozsa oracle. -/
public def oracle (s : Fin (2 ^ n)) : WalshHadamard.Oracle n := fun x => dotParity x s

/-! ### Walsh-sign algebra -/

/-- The bitwise inner-product parity is symmetric. -/
theorem dotParity_comm (x y : Fin (2 ^ n)) : dotParity x y = dotParity y x := by
  have hset : (Finset.univ.filter fun k : Fin n => bit x k && bit y k)
      = Finset.univ.filter fun k : Fin n => bit y k && bit x k := by
    apply Finset.filter_congr
    intro k _
    rw [Bool.and_comm]
  unfold WalshHadamard.dotParity
  rw [hset]

/-- The Walsh sign is symmetric. -/
theorem walshSign_comm (x y : Fin (2 ^ n)) : walshSign x y = walshSign y x := by
  unfold WalshHadamard.walshSign
  rw [dotParity_comm]

/-- A Walsh sign squares to `1`. -/
theorem walshSign_mul_self (x y : Fin (2 ^ n)) :
    walshSign x y * walshSign x y = 1 := by
  unfold WalshHadamard.walshSign
  by_cases h : dotParity x y <;> simp [h]

/-! ### Bit-flip involution -/

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
  unfold WalshHadamard.dotParity
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
    · -- `k` is in the original index set; flipping removes it.
      have hmem : k ∈ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
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
    · -- `k` is not in the original index set; flipping inserts it.
      have hnot : k ∉ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
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
  unfold WalshHadamard.walshSign
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

/-! ### Circuit correctness -/

/-- Querying the inner-product oracle phases each basis label by its Walsh
sign with the hidden string [dW19, qcnotes.tex:1293]. -/
theorem phaseSign_oracle (s x : Fin (2 ^ n)) :
    phaseSign (oracle s) x = walshSign s x := by
  unfold WalshHadamard.phaseSign WalshHadamard.walshSign oracle
  rw [dotParity_comm]

/-- The second Hadamard layer maps the Bernstein-Vazirani phase pattern
exactly to the classical state `|s⟩` [dW19, qcnotes.tex:1296]. -/
theorem finalState_oracle (s : Fin (2 ^ n)) :
    finalState (oracle s) = NormalizedVector.ket (R := Qubits n) s := by
  apply NormalizedVector.ext
  intro y
  rw [WalshHadamard.finalState]
  change (hadamardLayerOperator n).applyVec
      (afterPhaseQuery (oracle s) : HilbertVector (Qubits n)) y = _
  rw [UnitaryOperator.applyVec_apply, ket_apply]
  have hterm : ∀ j, hadamardLayerOperator n y j * afterPhaseQuery (oracle s) j
      = ((2 ^ n : ℕ) : ℂ)⁻¹ * (walshSign y j * walshSign s j) := fun j => by
    change (invSqrtCard n * walshSign y j)
        * (invSqrtCard n * phaseSign (oracle s) j) = _
    rw [phaseSign_oracle, mul_mul_mul_comm, invSqrtCard_mul_self]
  simp only [hterm]
  rw [← Finset.mul_sum]
  by_cases hys : y = s
  · subst hys
    rw [if_pos rfl]
    simp only [walshSign_mul_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    exact inv_mul_cancel₀ (pow_ne_zero n two_ne_zero)
  · rw [if_neg hys, sum_walshSign_mul_walshSign hys, mul_zero]

/-- Running the shared Walsh-Hadamard circuit with the inner-product oracle
recovers the hidden string in the input register. -/
theorem finalJointState_oracle (s : Fin (2 ^ n)) :
    WalshHadamard.finalJointState (oracle s) =
      NormalizedVector.tensor
        (NormalizedVector.ket (R := Qubits n) s) ketMinus := by
  rw [WalshHadamard.finalJointState_eq_finalState_tensor, finalState_oracle]

/-! ### Canonical terminal-measurement semantics -/

/-- The typed canonical input has exactly the normalized state expected by
the Walsh-Hadamard circuit theorem. -/
@[simp] theorem inputState_normalized (n : ℕ) :
    (inputState n).normalized = WalshHadamard.input n := rfl

/-- Embed the two unmeasured target basis values into the terminal-measurement
fiber for one recovered hidden string. -/
def measurementFiberEmbedding (s : Fin (2 ^ n)) :
    Fin (2 ^ 1) ↪ Fin (2 ^ (n + 1)) where
  toFun := fun target => prodEquiv (s, target)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

/-- The measurement-fiber embedding has the expected product-basis action. -/
@[simp] theorem measurementFiberEmbedding_apply (s : Fin (2 ^ n))
    (target : Fin (2 ^ 1)) :
    measurementFiberEmbedding s target = prodEquiv (s, target) := rfl

private theorem measurementOutcome_fiber (s : Fin (2 ^ n)) :
    Finset.univ.filter
        (fun basis : Fin (2 ^ (n + 1)) =>
          (measurement n).readout basis = measurementOutcome n s) =
      Finset.univ.map (measurementFiberEmbedding s) := by
  ext basis
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [measurement_readout_eq_outcome_iff]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [measurementFiberEmbedding_apply, ← hleft]
    exact Equiv.apply_symm_apply (prodEquiv (m := n) (n := 1)) basis
  · intro hmem
    obtain ⟨target, _, htarget⟩ := Finset.mem_map.mp hmem
    change prodEquiv (s, target) = basis at htarget
    rw [← htarget, Equiv.symm_apply_apply]

/-- The original mathematical final joint state on the canonical physical wires. -/
def evolvedState (s : Fin (2 ^ n)) : QubitLayout.State (layout n) :=
  WalshHadamard.Readout.evolvedState (oracle s)

/-- The original final state is exactly the recovered string tensored with the minus target. -/
@[simp] theorem evolvedState_normalized (s : Fin (2 ^ n)) :
    (evolvedState s).normalized =
      NormalizedVector.tensor (NormalizedVector.ket (R := Qubits n) s) ketMinus :=
  finalJointState_oracle s

/-- Each basis point in the recovered-string fiber has the target-qubit
amplitude of `|−⟩`. -/
theorem evolvedState_apply_prod (s : Fin (2 ^ n))
    (target : Fin (2 ^ 1)) :
    (evolvedState s).normalized (prodEquiv (s, target)) = ketMinus target := by
  rw [evolvedState_normalized, NormalizedVector.tensor_apply_prod,
    NormalizedVector.ket_apply, if_pos rfl, one_mul]

/-- The actual Born PMF of the canonical partial terminal measurement returns
the big-endian encoding of the hidden string with probability one. -/
theorem measurementOutcome_probability_one (s : Fin (2 ^ n)) :
    (measurement n).outcomePMF (evolvedState s) (measurementOutcome n s) = 1 := by
  rw [TerminalZMeasure.outcomePMF_apply, measurementOutcome_fiber s,
    Finset.sum_map]
  simp_rw [measurementFiberEmbedding_apply, evolvedState_apply_prod]
  have htarget :
      ∑ target : Fin (2 ^ 1), ENNReal.ofReal (‖ketMinus target‖ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    rw [← EuclideanSpace.norm_sq_eq, ketMinus.norm_eq_one]
    norm_num
  rw [htarget]

/-- One actual zero-input native word yields the complete recovered-string state
[dW19, qcnotes.tex:1296], with its own gate, query and dependency counts. -/
theorem circuitMain (s : Fin (2 ^ n)) :
    ∃ body : UnitaryCircuit AlgorithmGate.model (XorOracle.model (oracle s))
        (Gate.HadamardLayer.layout (n + 1)),
      body.binaryMatrix.apply (NormalizedVector.ket (R := Qubits (n + 1)) 0) =
        NormalizedVector.tensor (NormalizedVector.ket (R := Qubits n) s) ketMinus ∧
      body.eventCost =
        (2 * n + 2) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (XorOracle.model (oracle s)))
          (.gate AlgorithmGate.Coordinate.singleQubit) +
          ResourcePool.singleton
            (model := .quantum AlgorithmGate.model (XorOracle.model (oracle s)))
            (.oracle XorOracle.Coordinate.xor) ∧
      body.evaluatedEventDepth (fun _ => 1) = if n = 0 then 3 else 4 := by
  refine ⟨WalshHadamard.Native.zeroInputProgram (oracle s), ?_,
    WalshHadamard.Native.walshNative_zeroInputProgram_eventCost (oracle s),
    WalshHadamard.Native.walshNative_zeroInputProgram_unit_depth (oracle s)⟩
  rw [WalshHadamard.Native.walshNative_zeroInputProgram_apply_zero]
  exact finalJointState_oracle s

end BernsteinVazirani

end

end QuantumAlg

end

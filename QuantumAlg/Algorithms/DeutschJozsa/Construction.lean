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

import QuantumAlg.Init
public import QuantumAlg.Primitives.WalshHadamard
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Primitives.PhaseKickback.Xor

/-!
# Deutsch-Jozsa promise, amplitudes, and circuit mathematics

The Deutsch-Jozsa problem gives oracle access to a Boolean function on
`N = 2^n` inputs, promised either constant or balanced: all values equal,
or exactly half zero and half one [dW19, qcnotes.tex:1179, 1181-1182].

The algorithm uses one phase query between two layers of Hadamards
[dW19, qcnotes.tex:1193]. The Walsh-Hadamard layer and the XOR phase-query
pipeline are the shared `QuantumAlg.WalshHadamard` primitive; this module adds
only the Deutsch-Jozsa-specific content. After the query, the second Hadamard
layer makes the amplitude of `|0^n⟩` equal to
`(2^n)⁻¹ * ∑ x, (-1)^{f x}` [dW19, qcnotes.tex:1245, 1251]. This scalar is
`1` or `-1` for constant inputs
and `0` for balanced inputs [dW19, qcnotes.tex:1253, 1255]. A terminal Z
measurement of the first `n` logical qubits therefore returns `0^n` with
probability one exactly in the constant case, and with probability zero in the
balanced case. The target qubit is left unmeasured and its complete Born fiber
is summed rather than selecting one joint coordinate.

## Main results

- `QuantumAlg.deutschJozsa_query_phase` — one XOR query with a `|−⟩` target
  is the phase query used by the algorithm (via `WalshHadamard` + phase
  kickback).
- `QuantumAlg.DeutschJozsa.allZeroOutcome_probability` — the Born probability
  of terminally reading `0^n` is the squared norm of the signed phase average.
- `QuantumAlg.DeutschJozsa.circuitMain` — under the explicit constant/balanced
  promise, one concrete circuit has correct terminal decision probability one;
  the same witness supplies the exact native gate, query, and depth counts.

The normalized-state Born distribution below is a mathematical observation.
The complete native endpoint separately proves its actual measured Store
output agrees with these amplitudes; this file does not define an execution
engine or a prepared-attempt wrapper.
-/

section

namespace QuantumAlg

open NormalizedVector Gate WalshHadamard

noncomputable section

variable {n : ℕ}

namespace DeutschJozsa

open WalshHadamard.Readout

/-! ### The constant/balanced promise -/

/-- The constant side of the Deutsch-Jozsa promise. -/
@[expose] public def IsConstant (f : Oracle n) : Prop := ∃ c : Bool, ∀ x, f x = c

/-- Inputs on which the oracle returns `true`. -/
@[expose] public def trueInputs (f : Oracle n) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter fun x => f x

/-- Inputs on which the oracle returns `false`. -/
@[expose] public def falseInputs (f : Oracle n) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter fun x => ! f x

/-- The balanced side of the Deutsch-Jozsa promise: exactly as many `true`
inputs as `false` inputs. -/
@[expose] public def IsBalanced (f : Oracle n) : Prop :=
  (trueInputs f).card = (falseInputs f).card

/-- The explicit Deutsch-Jozsa promise. -/
@[expose] public def Promise (f : Oracle n) : Prop := IsConstant f ∨ IsBalanced f

/-! ### The `|0^n⟩` amplitude -/

/-- The final input-register amplitude of the all-zero basis state `|0^n⟩`,
in the phase-query view. -/
def inputZeroAmplitude (f : Oracle n) : ℂ := finalState f 0

/-- The numerator of the final `|0^n⟩` amplitude after the second Hadamard
layer: `∑ x, (-1)^{f x}`. -/
def zeroAmplitudeNumerator (f : Oracle n) : ℂ :=
  ∑ x, phaseSign f x

/-- The standard signed-average formula for the final `|0^n⟩` amplitude. -/
def zeroAmplitude (f : Oracle n) : ℂ :=
  ((2 ^ n : ℕ) : ℂ)⁻¹ * zeroAmplitudeNumerator f

private theorem sum_phaseSign_eq_false_sub_true (f : Oracle n)
    (s : Finset (Fin (2 ^ n))) :
    s.sum (fun x => phaseSign f x) =
      ((s.filter (fun x => ! f x)).card : ℂ) -
        ((s.filter (fun x => f x)).card : ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih]
      by_cases h : f a
      · simp [phaseSign, h, ha, Finset.filter_insert,
          Finset.card_insert_of_notMem]
        ring
      · simp [phaseSign, h, ha, Finset.filter_insert,
          Finset.card_insert_of_notMem]
        ring

/-- The signed phase sum is the number of `false` inputs minus the number of
`true` inputs. -/
theorem zeroAmplitudeNumerator_eq_card_sub (f : Oracle n) :
    zeroAmplitudeNumerator f =
      ((falseInputs f).card : ℂ) - ((trueInputs f).card : ℂ) := by
  rw [zeroAmplitudeNumerator, sum_phaseSign_eq_false_sub_true]
  rfl

/-- Applying the closed-form second Hadamard layer to the post-query input
state makes the final `|0^n⟩` amplitude equal to the standard signed average. -/
theorem inputZeroAmplitude_eq_zeroAmplitude (f : Oracle n) :
    inputZeroAmplitude f = zeroAmplitude f := by
  rw [inputZeroAmplitude, finalState, zeroAmplitude, zeroAmplitudeNumerator]
  change (hadamardLayerOperator n).applyVec
      (afterPhaseQuery f : HilbertVector (Qubits n)) 0 = _
  rw [UnitaryOperator.applyVec_apply]
  calc
    ∑ j, hadamardLayerOperator n 0 j * afterPhaseQuery f j
        = ∑ j, (((2 ^ n : ℕ) : ℂ)⁻¹ * phaseSign f j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          change (invSqrtCard n * walshSign (0 : Fin (2 ^ n)) j)
              * (invSqrtCard n * phaseSign f j)
            = (((2 ^ n : ℕ) : ℂ)⁻¹ * phaseSign f j)
          rw [walshSign_zero_left, mul_one, ← mul_assoc, invSqrtCard_mul_self]
    _ = ((2 ^ n : ℕ) : ℂ)⁻¹ * ∑ x, phaseSign f x := by
          rw [Finset.mul_sum]

/-- Balanced oracles have zero final `|0^n⟩` amplitude. -/
theorem zeroAmplitude_of_balanced (f : Oracle n) (hf : IsBalanced f) :
    zeroAmplitude f = 0 := by
  rw [zeroAmplitude, zeroAmplitudeNumerator_eq_card_sub]
  unfold IsBalanced at hf
  rw [hf]
  ring

/-- Constant oracles have final `|0^n⟩` amplitude exactly `1` or `-1`,
depending on the constant value. -/
theorem zeroAmplitude_of_constant (f : Oracle n) (hf : IsConstant f) :
    ∃ c : Bool, zeroAmplitude f = if c then (-1 : ℂ) else 1 := by
  rcases hf with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  cases c
  · rw [zeroAmplitude, zeroAmplitudeNumerator]
    simp [phaseSign, hc, Finset.sum_const, Fintype.card_fin]
  · rw [zeroAmplitude, zeroAmplitudeNumerator]
    simp [phaseSign, hc, Finset.sum_const, Fintype.card_fin]

/-! ### Canonical layout and deterministic terminal decision -/

/-- The terminal all-zero input-register outcome. -/
def allZeroOutcome (n : ℕ) : TerminalZMeasure.Outcome n :=
  measurementOutcome n 0

/-- A terminal outcome makes the correct promise decision when it reports
constant exactly for the all-zero input-register result. -/
def CorrectDecision (f : Oracle n)
    (outcome : TerminalZMeasure.Outcome n) : Prop :=
  (outcome = allZeroOutcome n) ↔ IsConstant f

/-- Embed the unmeasured target basis into the all-zero input-register
measurement fiber. -/
def zeroFiberEmbedding (n : ℕ) : Fin (2 ^ 1) ↪ Fin (2 ^ (n + 1)) where
  toFun := fun target => prodEquiv ((0 : Fin (2 ^ n)), target)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

@[simp] theorem zeroFiberEmbedding_apply (target : Fin (2 ^ 1)) :
    zeroFiberEmbedding n target = prodEquiv ((0 : Fin (2 ^ n)), target) := rfl

private theorem mem_nativeListUnion_right
    (left : List Nat) {right : List Nat} {value : Nat}
    (hvalue : value ∈ right) : value ∈ left.union right := by
  induction left with
  | nil => exact hvalue
  | cons head tail ih =>
      change value ∈ (tail.union right).insert head
      exact List.mem_insert_of_mem ih

private theorem nativeListUnion_eq_right_of_subset
    (left right : List Nat) (hsubset : left ⊆ right) :
    left.union right = right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      change (tail.union right).insert head = right
      rw [List.insert_of_mem
        (mem_nativeListUnion_right tail (hsubset List.mem_cons_self))]
      exact ih (fun value hvalue =>
        hsubset (List.mem_cons_of_mem head hvalue))

private theorem allZeroOutcome_fiber :
    Finset.univ.filter
        (fun basis : Fin (2 ^ (n + 1)) =>
          (measurement n).readout basis = allZeroOutcome n) =
      Finset.univ.map (zeroFiberEmbedding n) := by
  ext basis
  rw [Finset.mem_filter]
  simp only [allZeroOutcome, Finset.mem_univ, true_and]
  rw [measurement_readout_eq_outcome_iff]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [zeroFiberEmbedding_apply, ← hleft]
    exact Equiv.apply_symm_apply (prodEquiv (m := n) (n := 1)) basis
  · intro hmem
    obtain ⟨target, _, htarget⟩ := Finset.mem_map.mp hmem
    change prodEquiv ((0 : Fin (2 ^ n)), target) = basis at htarget
    rw [← htarget, Equiv.symm_apply_apply]

theorem evolvedState_apply_zero_prod (f : Oracle n)
    (target : Fin (2 ^ 1)) :
    (evolvedState f).normalized
        (prodEquiv ((0 : Fin (2 ^ n)), target)) =
      zeroAmplitude f * ketMinus target := by
  change WalshHadamard.finalJointState f
      (prodEquiv ((0 : Fin (2 ^ n)), target)) = _
  rw [
    WalshHadamard.finalJointState_eq_finalState_tensor,
    NormalizedVector.tensor_apply_prod]
  change inputZeroAmplitude f * ketMinus target = _
  rw [inputZeroAmplitude_eq_zeroAmplitude]

/-- Born probability of the all-zero input-register outcome. Both target-qubit
basis states are summed because the target is not measured. -/
theorem allZeroOutcome_probability (f : Oracle n) :
    (measurement n).outcomePMF
        (evolvedState f)
        (allZeroOutcome n) =
      ENNReal.ofReal (‖zeroAmplitude f‖ ^ 2) := by
  rw [TerminalZMeasure.outcomePMF_apply, allZeroOutcome_fiber,
    Finset.sum_map]
  simp_rw [zeroFiberEmbedding_apply, evolvedState_apply_zero_prod, norm_mul,
    mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← Finset.mul_sum]
  have htarget :
      ∑ target : Fin (2 ^ 1), ENNReal.ofReal (‖ketMinus target‖ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    rw [← EuclideanSpace.norm_sq_eq, ketMinus.norm_eq_one]
    norm_num
  rw [htarget, mul_one]

theorem allZeroOutcome_probability_of_constant (f : Oracle n)
    (hf : IsConstant f) :
    (measurement n).outcomePMF
        (evolvedState f)
        (allZeroOutcome n) = 1 := by
  rw [allZeroOutcome_probability]
  rcases zeroAmplitude_of_constant f hf with ⟨value, hvalue⟩
  rw [hvalue]
  cases value <;> norm_num

theorem allZeroOutcome_probability_of_balanced (f : Oracle n)
    (hf : IsBalanced f) :
    (measurement n).outcomePMF
        (evolvedState f)
        (allZeroOutcome n) = 0 := by
  rw [allZeroOutcome_probability, zeroAmplitude_of_balanced f hf]
  norm_num

/-- Decision probability of a complete normalized joint state on the original physical wires. -/
def correctDecisionProbability (f : Oracle n)
    (state : NormalizedVector (Qubits (n + 1))) : ENNReal :=
  ((measurement n).outcomePMF
    { state := PureState.ofNormalized state (WalshHadamard.Readout.layout n).systemIdx
      system_idx_eq := rfl }).toOuterMeasure {outcome | CorrectDecision f outcome}

theorem correctDecision_probability_one (f : Oracle n) (hf : Promise f) :
    correctDecisionProbability f (WalshHadamard.finalJointState f) = 1 := by
  rw [correctDecisionProbability, PMF.toOuterMeasure_apply_eq_one_iff]
  intro outcome houtcome
  change outcome ∈ ((measurement n).outcomePMF (evolvedState f)).support at houtcome
  by_cases hconstant : IsConstant f
  · have hprob := allZeroOutcome_probability_of_constant f hconstant
    have hsupport :
        ((measurement n).outcomePMF
          (evolvedState f)).support =
          {allZeroOutcome n} :=
      (PMF.apply_eq_one_iff _ _).mp hprob
    have houtcome_eq : outcome = allZeroOutcome n := by
      rw [hsupport] at houtcome
      simpa using houtcome
    change CorrectDecision f outcome
    simp [CorrectDecision, hconstant, houtcome_eq]
  · have hbalanced : IsBalanced f := hf.resolve_left hconstant
    have hzero := allZeroOutcome_probability_of_balanced f hbalanced
    have houtcome_ne : outcome ≠ allZeroOutcome n := by
      intro houtcome_eq
      subst outcome
      exact ((PMF.mem_support_iff _ _).mp houtcome) hzero
    change CorrectDecision f outcome
    simp [CorrectDecision, hconstant, houtcome_ne]

/-- One Deutsch-Jozsa oracle query with the target qubit in `|-⟩` is the
phase query `|x⟩ ↦ (-1)^{f x}|x⟩`. -/
theorem deutschJozsa_query_phase (f : WalshHadamard.Oracle n) (x : Fin (2 ^ n)) :
    (xorOracleOp f).applyVec
        (HilbertVector.tensor
          ((ket x : NormalizedVector (Qubits n)) : HilbertVector (Qubits n))
          (ketMinus : HilbertVector (Qubits 1)))
      =
      WalshHadamard.phaseSign f x
        • HilbertVector.tensor
            ((ket x : NormalizedVector (Qubits n)) : HilbertVector (Qubits n))
            (ketMinus : HilbertVector (Qubits 1)) := by
  exact PhaseKickback.xor_action f x

/-- One actual native word realizes the exact original joint state and certain decision,
with its own single-qubit, XOR-query and dependency counts. -/
theorem circuitMain (f : WalshHadamard.Oracle n) (hf : Promise f) :
    ∃ body : UnitaryCircuit AlgorithmGate.model (XorOracle.model f)
        (Gate.HadamardLayer.layout (n + 1)),
      body.binaryMatrix.apply (NormalizedVector.ket (R := Qubits (n + 1)) 0) =
        WalshHadamard.finalJointState f ∧
      correctDecisionProbability f
        (body.binaryMatrix.apply (NormalizedVector.ket (R := Qubits (n + 1)) 0)) = 1 ∧
      body.eventCost =
        (2 * n + 2) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (XorOracle.model f))
          (.gate AlgorithmGate.Coordinate.singleQubit) +
          ResourcePool.singleton
            (model := .quantum AlgorithmGate.model (XorOracle.model f))
            (.oracle XorOracle.Coordinate.xor) ∧
      body.evaluatedEventDepth (fun _ => 1) = if n = 0 then 3 else 4 := by
  refine ⟨WalshHadamard.Native.zeroInputProgram f,
    WalshHadamard.Native.walshNative_zeroInputProgram_apply_zero f, ?_,
    WalshHadamard.Native.walshNative_zeroInputProgram_eventCost f,
    WalshHadamard.Native.walshNative_zeroInputProgram_unit_depth f⟩
  rw [WalshHadamard.Native.walshNative_zeroInputProgram_apply_zero]
  exact correctDecision_probability_one f hf

end DeutschJozsa

end

end QuantumAlg

end

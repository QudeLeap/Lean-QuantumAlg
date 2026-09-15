/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Gates
public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Kets
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Depth.Expr

/-!
# The Hadamard test

The Hadamard test estimates `Re <psi| U |psi>` for a unitary `U`: prepare
`|0> ⊗ psi`, apply `H` on the control, the controlled `U`, and `H` again,
then measure the control qubit. The outcome probabilities are

`P(0) = (1 + Re <psi| U |psi>)/2`, `P(1) = (1 - Re <psi| U |psi>)/2`.

State normalization and operator unitarity are carried by `NormalizedVector`
and `UnitaryOperator`.  The resource-aware realization is assembled only from
sealed `UnitaryCircuit` leaves.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

variable {n : ℕ}

/-- Strict event coordinate of each Hadamard-test boundary Hadamard. -/
def hadamardTestHadamardEvent : Resource.Event .quantum :=
  Gate.atomicEvent (.builtin "hadamard")

/-- Metadata-free Hadamard action on the leading control qubit. -/
def hadamardTestHadamardOp (n : ℕ) : UnitaryOperator (Qubits (1 + n)) :=
  Gate.leadingHadamardOp n

/-- Sealed leading-control Hadamard leaf.  Its operator is the actual `H ⊗ I`,
and its gate coordinate is projected from this same occurrence. -/
def hadamardTestHadamardLeaf (n : ℕ) : UnitaryLeaf (Qubits (1 + n)) :=
  Gate.leadingHadamardLeafAt n [0]

/-- One canonical Hadamard leaf on the control qubit. -/
def hadamardTestHadamardLayer (n : ℕ) : UnitaryCircuit (Qubits (1 + n)) :=
  UnitaryCircuit.ofLeaf (hadamardTestHadamardLeaf n)
    (by simp [hadamardTestHadamardLeaf, Gate.leadingHadamardLeafAt])

@[simp]
theorem hadamardTestHadamardLayer_matrix (n : ℕ) :
    (hadamardTestHadamardLayer n).matrix = hadamardTestHadamardOp n :=
  rfl

@[simp]
theorem hadamardTestHadamardLayer_eventTrace (n : ℕ) :
    (hadamardTestHadamardLayer n).eventTrace =
      [hadamardTestHadamardEvent] :=
  rfl

@[simp]
theorem hadamardTestHadamardLayer_eventCost (n : ℕ) :
    (hadamardTestHadamardLayer n).eventCost =
      ResourcePool.singleton hadamardTestHadamardEvent :=
  rfl

@[simp]
theorem hadamardTestHadamardLayer_eventDepth (n : ℕ) :
    (hadamardTestHadamardLayer n).eventDepth =
      .atom hadamardTestHadamardEvent :=
  rfl





/-- Resource-aware controlled unitary on the canonical `(control, target)`
layout. Its operator comes from the metadata-free controlled construction. -/
def hadamardTestControlledLayer (U : UnitaryCircuit (Qubits n)) :
    UnitaryCircuit (Qubits (1 + n)) :=
  let shifted := UnitaryCircuit.shiftPhysicalIdx 1 U
  UnitaryCircuit.controlQubitsAt [0] shifted
    { left_nodup := by simp
      right_nodup := shifted.physical_idx_nodup
      disjoint := by
        simp [shifted, UnitaryCircuit.shiftPhysicalIdx] }
    (1 : Fin 2)

@[simp]
theorem hadamardTestControlledLayer_applyVec (U : UnitaryCircuit (Qubits n))
    (state : HilbertVector (Qubits (1 + n))) :
    (hadamardTestControlledLayer U).applyVec state =
      (UnitaryOperator.controlledQubits U.matrix).applyVec state := by
  simp [hadamardTestControlledLayer, UnitaryOperator.controlledQubits,
    UnitaryCircuit.applyVec]

@[simp]
theorem hadamardTestControlledLayer_matrix (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestControlledLayer U).matrix =
      UnitaryOperator.controlledQubits U.matrix := by
  simp [hadamardTestControlledLayer, UnitaryOperator.controlledQubits]

@[simp]
theorem hadamardTestControlledLayer_eventTrace (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestControlledLayer U).eventTrace =
      U.eventTrace.map (fun event => event.controlForDimension 2) := by
  simp [hadamardTestControlledLayer]

@[simp]
theorem hadamardTestControlledLayer_eventCost (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestControlledLayer U).eventCost =
      ResourcePool.controlForDimension 2 U.eventCost := by
  simp [hadamardTestControlledLayer]

@[simp]
theorem hadamardTestControlledLayer_eventDepth (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestControlledLayer U).eventDepth =
      .controlled "circuit-control"
        (DepthExpr.controlEventsForDimension 2 U.eventDepth) := by
  simp [hadamardTestControlledLayer]

/-- A body event keeps its exact multiplicity at the transformed controlled
coordinate. -/
theorem hadamardTestControlledLayer_event_count
    (focus : Resource.Event .quantum) (U : UnitaryCircuit (Qubits n)) :
    ResourcePool.count (focus.controlForDimension 2)
        (hadamardTestControlledLayer U).eventCost =
      ResourcePool.count focus U.eventCost := by
  simp [hadamardTestControlledLayer]

/-- Strict controlled-query depth counts every source occurrence at the
transformed coordinate, since the controlled events share one control wire. -/
@[simp]
theorem hadamardTestControlledLayer_eventQueryDepth
    (focus : Resource.Event .quantum) (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestControlledLayer U).eventQueryDepth
        (focus.controlForDimension 2) =
      DepthExpr.costEval (DepthExpr.indicator focus) U.eventDepth := by
  have hshift :
      DepthExpr.costEval (DepthExpr.indicator focus)
          (UnitaryCircuit.shiftPhysicalIdx 1 U).eventDepth =
        DepthExpr.costEval (DepthExpr.indicator focus) U.eventDepth := by
    exact congrArg (DepthExpr.costEval (DepthExpr.indicator focus))
      (UnitaryCircuit.shiftPhysicalIdx_eventDepth 1 U)
  simpa only [hadamardTestControlledLayer,
    UnitaryCircuit.eventQueryDepth_controlQubitsAt] using hshift





/-- The Hadamard test as three structural circuit blocks, in execution order. -/
def hadamardTestCircuit (U : UnitaryCircuit (Qubits n)) : UnitaryCircuit (Qubits (1 + n)) :=
  UnitaryCircuit.seq
    (UnitaryCircuit.seq
      (hadamardTestHadamardLayer n)
      (hadamardTestControlledLayer U))
    (hadamardTestHadamardLayer n)

/-- Metadata-free Hadamard-test unitary. -/
public def hadamardTest (U : UnitaryOperator (Qubits n)) :
    UnitaryOperator (Qubits (1 + n)) :=
  hadamardTestHadamardOp n *
    (UnitaryOperator.controlledQubits U * hadamardTestHadamardOp n)

/-- The typed realization has exactly the metadata-free Hadamard-test
semantics of its underlying operator. -/
@[simp]
theorem hadamardTestCircuit_matrix (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestCircuit U).matrix = hadamardTest U.matrix := by
  change (hadamardTestHadamardLayer n).matrix *
      ((hadamardTestControlledLayer U).matrix *
        (hadamardTestHadamardLayer n).matrix) = hadamardTest U.matrix
  rw [hadamardTestHadamardLayer_matrix, hadamardTestControlledLayer_matrix]
  rfl

/-- Ordered strict execution events of the three Hadamard-test blocks. -/
@[simp]
theorem hadamardTestCircuit_eventTrace (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestCircuit U).eventTrace =
      [hadamardTestHadamardEvent] ++
        U.eventTrace.map (fun event => event.controlForDimension 2) ++
          [hadamardTestHadamardEvent] := by
  simp only [hadamardTestCircuit, UnitaryCircuit.seq_eventTrace,
    hadamardTestHadamardLayer_eventTrace,
    hadamardTestControlledLayer_eventTrace, List.append_assoc]

/-- Exact strict event pool of the three Hadamard-test blocks. -/
@[simp]
theorem hadamardTestCircuit_eventCost (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestCircuit U).eventCost =
      ResourcePool.singleton hadamardTestHadamardEvent +
        ResourcePool.controlForDimension 2 U.eventCost +
          ResourcePool.singleton hadamardTestHadamardEvent := by
  simp only [hadamardTestCircuit, UnitaryCircuit.seq_eventCost,
    hadamardTestHadamardLayer_eventCost,
    hadamardTestControlledLayer_eventCost]

/-- Exact strict symbolic critical path of the three Hadamard-test blocks. -/
@[simp]
theorem hadamardTestCircuit_eventDepth (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestCircuit U).eventDepth =
      .seq
        (.seq (.atom hadamardTestHadamardEvent)
          (.controlled "circuit-control"
            (DepthExpr.controlEventsForDimension 2 U.eventDepth)))
        (.atom hadamardTestHadamardEvent) := by
  simp only [hadamardTestCircuit, UnitaryCircuit.seq_eventDepth,
    hadamardTestHadamardLayer_eventDepth,
    hadamardTestControlledLayer_eventDepth]

/-- With unit duration per strict event, the controlled body contributes one
sequential layer per event and the two boundary Hadamards add two more. -/
theorem hadamardTestCircuit_evaluatedEventDepth_of_one
    (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestCircuit U).evaluatedEventDepth (fun _event => 1) =
      DepthExpr.costEval (fun _event => 1) U.eventDepth + 2 := by
  have hcontrolled :
      (hadamardTestControlledLayer U).evaluatedEventDepth (fun _event => 1) =
        DepthExpr.costEval (fun _event => 1) U.eventDepth := by
    change DepthExpr.depthEval (fun _event => 1)
        (hadamardTestControlledLayer U).eventDepth =
      DepthExpr.costEval (fun _event => 1) U.eventDepth
    rw [hadamardTestControlledLayer_eventDepth,
      DepthExpr.depthEval_controlled,
      DepthExpr.depthEval_controlEventsForDimension]
  have hhadamard :
      (hadamardTestHadamardLayer n).evaluatedEventDepth (fun _event => 1) = 1 := by
    change DepthExpr.depthEval (fun _event => 1)
        (hadamardTestHadamardLayer n).eventDepth = 1
    rw [hadamardTestHadamardLayer_eventDepth]
    rfl
  rw [hadamardTestCircuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, hcontrolled, hhadamard]
  omega

/-- Linearizing the strict Hadamard-test critical path recovers its exact
event pool. -/
theorem hadamardTestCircuit_resourcesFromEventDepth
    (U : UnitaryCircuit (Qubits n)) :
    (hadamardTestCircuit U).resourcesFromEventDepth =
      ResourcePool.singleton hadamardTestHadamardEvent +
        ResourcePool.controlForDimension 2 U.eventCost +
          ResourcePool.singleton hadamardTestHadamardEvent := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    hadamardTestCircuit_eventCost]





private theorem tensor_H_one_applyVec_ket0
    (ψ : HilbertVector (Qubits n)) :
    (hadamardTestHadamardOp n).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ)
      = HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ := by
  change HilbertOperator.applyVec
      (HilbertOperator.tensor (HOp : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits n)))
      (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ)
    = HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ
  rw [HilbertOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor (HOp.applyVec (ket0 : HilbertVector (Qubits 1)))
      (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n)) ψ)
    = HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ
  have hH : HOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) :=
    congrArg (fun v : NormalizedVector (Qubits 1) =>
      (v : HilbertVector (Qubits 1))) H_apply_ket0
  rw [hH, HilbertOperator.one_applyVec]

private theorem ketPlus_tensor (ψ : HilbertVector (Qubits n)) :
    HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ
      = invSqrt2 •
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ
          + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) ψ) := by
  rw [ketPlus_coe, HilbertVector.smul_tensor, HilbertVector.add_tensor]

private theorem controlled_applyVec_ketPlus_tensor
    (U : UnitaryOperator (Qubits n)) (ψ : HilbertVector (Qubits n)) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ)
      = invSqrt2 •
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ
          + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (U.applyVec ψ)) := by
  rw [ketPlus_tensor, UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_add,
    UnitaryOperator.controlledQubits_applyVec_ket0_tensor,
    UnitaryOperator.controlledQubits_applyVec_ket1_tensor]

private theorem tensor_H_one_finish
    (U : UnitaryOperator (Qubits n)) (ψ : NormalizedVector (Qubits n)) :
    (hadamardTestHadamardOp n).applyVec
        (invSqrt2 •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ψ : HilbertVector (Qubits n))
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              (U.applyVec (ψ : HilbertVector (Qubits n)))))
      =
        (2 : ℂ)⁻¹ •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) + U.applyVec ψ)
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) - U.applyVec ψ)) := by
  rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_add]
  change invSqrt2 •
      (HilbertOperator.applyVec
          (HilbertOperator.tensor (HOp : HilbertOperator (Qubits 1))
            (1 : HilbertOperator (Qubits n)))
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (ψ : HilbertVector (Qubits n)))
        + HilbertOperator.applyVec
          (HilbertOperator.tensor (HOp : HilbertOperator (Qubits 1))
            (1 : HilbertOperator (Qubits n)))
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
            (U.applyVec (ψ : HilbertVector (Qubits n))))) = _
  rw [HilbertOperator.tensor_applyVec_tensor, HilbertOperator.tensor_applyVec_tensor]
  change invSqrt2 •
      (HilbertVector.tensor (HOp.applyVec (ket0 : HilbertVector (Qubits 1)))
          (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n))
            (ψ : HilbertVector (Qubits n)))
        + HilbertVector.tensor (HOp.applyVec (ket1 : HilbertVector (Qubits 1)))
          (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n))
            (U.applyVec (ψ : HilbertVector (Qubits n)))))
      =
        (2 : ℂ)⁻¹ •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) + U.applyVec ψ)
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) - U.applyVec ψ))
  have hH0 : HOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) :=
    congrArg (fun v : NormalizedVector (Qubits 1) =>
      (v : HilbertVector (Qubits 1))) H_apply_ket0
  have hH1 : HOp.applyVec (ket1 : HilbertVector (Qubits 1)) =
      (ketMinus : HilbertVector (Qubits 1)) :=
    congrArg (fun v : NormalizedVector (Qubits 1) =>
      (v : HilbertVector (Qubits 1))) H_apply_ket1
  rw [hH0, hH1, HilbertOperator.one_applyVec, HilbertOperator.one_applyVec]
  apply WithLp.ofLp_injective
  funext i
  simp [ketPlus_coe, ketMinus_coe, HilbertVector.tensor_apply,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, smul_add,
    smul_sub, smul_smul, invSqrt2_mul_self]
  ring

/-- Raw-vector proof of the Hadamard-test pre-measurement state. -/
private theorem hadamardTest_applyVec_ket0_tensor
    (U : UnitaryOperator (Qubits n)) (ψ : NormalizedVector (Qubits n)) :
    (hadamardTest U).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ψ : HilbertVector (Qubits n)))
      =
        (2 : ℂ)⁻¹ •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) + U.applyVec ψ)
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) - U.applyVec ψ)) := by
  rw [hadamardTest, UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec,
    tensor_H_one_applyVec_ket0, controlled_applyVec_ketPlus_tensor,
    tensor_H_one_finish]

/-- The pre-measurement state of the Hadamard test. -/
theorem hadamardTest_apply_ket0_tensor (U : UnitaryOperator (Qubits n))
    (ψ : NormalizedVector (Qubits n)) :
    (hadamardTest U).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ψ : HilbertVector (Qubits n)))
      =
        (2 : ℂ)⁻¹ •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) + U.applyVec ψ)
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) - U.applyVec ψ)) := by
  exact hadamardTest_applyVec_ket0_tensor U ψ

/-- Hadamard test, outcome 0, in operator form. -/
theorem hadamardTest_probQubit0_zero {U : UnitaryOperator (Qubits n)}
    (ψ : NormalizedVector (Qubits n)) :
    NormalizedVector.probQubit0
        ((hadamardTest U).apply (ket0.tensor ψ)) 0
      = (1 + (inner ℂ (ψ : HilbertVector (Qubits n)) (U.applyVec ψ)).re) / 2 := by
  change HilbertVector.leadingQubitWeight ((hadamardTest U).applyVec
      (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ψ : HilbertVector (Qubits n)))) 0 = _
  rw [hadamardTest_apply_ket0_tensor, HilbertVector.leadingQubitWeight_smul,
    leadingQubitWeight_ket0_tensor_add_ket1_tensor,
    norm_add_sq (𝕜 := ℂ), ψ.norm_eq_one]
  have hU_norm : ‖U.applyVec (ψ : HilbertVector (Qubits n))‖ = 1 := by
    rw [U.norm_applyVec, ψ.norm_eq_one]
  rw [hU_norm]
  have h2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = (4 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [h2]
  simp only [RCLike.re_to_complex]
  ring

/-- **Hadamard test, outcome 1**. -/
theorem hadamardTest_probQubit0_one {U : UnitaryOperator (Qubits n)}
    (ψ : NormalizedVector (Qubits n)) :
    NormalizedVector.probQubit0
        ((hadamardTest U).apply (ket0.tensor ψ)) 1
      = (1 - (inner ℂ (ψ : HilbertVector (Qubits n)) (U.applyVec ψ)).re) / 2 := by
  change HilbertVector.leadingQubitWeight ((hadamardTest U).applyVec
      (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ψ : HilbertVector (Qubits n)))) 1 = _
  rw [hadamardTest_apply_ket0_tensor, HilbertVector.leadingQubitWeight_smul,
    leadingQubitWeight_one_ket0_tensor_add_ket1_tensor,
    norm_sub_sq (𝕜 := ℂ), ψ.norm_eq_one]
  have hU_norm : ‖U.applyVec (ψ : HilbertVector (Qubits n))‖ = 1 := by
    rw [U.norm_applyVec, ψ.norm_eq_one]
  rw [hU_norm]
  have h2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = (4 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [h2]
  simp only [RCLike.re_to_complex]
  ring

end

end QuantumAlg

end

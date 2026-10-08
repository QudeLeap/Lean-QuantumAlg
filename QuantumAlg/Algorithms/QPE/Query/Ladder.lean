/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Query
import all QuantumAlg.Algorithms.QPE.Query
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr
import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual binary-power source-query ladder

Every controlled power is implemented by its actual repeated granted query.
The ladder therefore makes 2^t - 1 controlled source calls, including zero
calls when t = 0 [Lin22, phaseestimation.tex:514-523].
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

open scoped BigOperators

/-- Execute the original binary stages in increasing exponent order. -/
public def queryLadder (gates : GateModel) (phaseWidth : Nat) {systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) :
    UnitaryCircuit gates (UnitarySource.model unitary true)
      (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout :=
  UnitaryCircuit.indexedProduct "qpe-controlled-source-ladder" phaseWidth
    (UnitaryCircuit.identity gates (UnitarySource.model unitary true)
      (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout)
    (powerStage gates unitary)

private theorem sum_stage_queries (width : Nat) :
    (∑ index : Fin width, 2 ^ index.val) = 2 ^ width - 1 := by
  induction width with
  | zero => simp
  | succ width ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, pow_succ]
      have positive : 0 < 2 ^ width := pow_pos (by decide) _
      omega

/-- An actual repeated-query stage has one abstract dependency step per source call. -/
public theorem qpeNative_powerStage_unit_depth (gates : GateModel)
    {phaseWidth systemWidth : Nat} (unitary : UnitaryOperator (Qubits systemWidth))
    (stage : Fin phaseWidth) :
    (powerStage gates unitary stage).evaluatedEventDepth (fun _ => 1) = 2 ^ stage.val := by
  change 2 ^ stage.val * 1 = 2 ^ stage.val
  exact mul_one _

/-- The complete source ladder counts every actual controlled query repetition. -/
public theorem qpeNative_queryLadder_eventCost (gates : GateModel) (phaseWidth : Nat)
    {systemWidth : Nat} (unitary : UnitaryOperator (Qubits systemWidth)) :
    (queryLadder gates phaseWidth unitary).eventCost = (2 ^ phaseWidth - 1) •
      ResourcePool.singleton (model := .quantum gates (UnitarySource.model unitary true))
        (.oracle UnitarySource.Coordinate.controlled) := by
  rw [queryLadder, UnitaryCircuit.indexedProduct_eventCost,
    UnitaryCircuit.identity_eventCost, zero_add]
  simp only [qpeNative_powerStage_eventCost]
  rw [Finset.sum_nsmul_assoc, sum_stage_queries]

/-- Sequential binary stages retain the actual sum of their query durations. -/
public theorem qpeNative_queryLadder_unit_depth (gates : GateModel) (phaseWidth : Nat)
    {systemWidth : Nat} (unitary : UnitaryOperator (Qubits systemWidth)) :
    (queryLadder gates phaseWidth unitary).evaluatedEventDepth (fun _ => 1) =
      2 ^ phaseWidth - 1 := by
  change 0 + (∑ stage : Fin phaseWidth,
    (powerStage gates unitary stage).evaluatedEventDepth (fun _ => 1)) = _
  simp only [zero_add, qpeNative_powerStage_unit_depth]
  exact sum_stage_queries phaseWidth

end

end QuantumAlg.QuantumPhaseEstimation.Native

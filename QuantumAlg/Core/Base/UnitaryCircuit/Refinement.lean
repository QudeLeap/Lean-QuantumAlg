/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Placement
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Oracle.Placement

/-!
# Exact native-word substitution on the same physical systems

Every replacement is an actual circuit with the original application operator.
The construction retains ordering, disjoint placements, repetitions and macro
bodies. Events and depth are computed from the resulting construction.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Exact implementations of source instructions in a specified target language. -/
public structure InstructionRealizations (sourceGates : GateModel) (sourceOracles : OracleModel)
    (targetGates : GateModel) (targetOracles : OracleModel) where
  /-- Relate semantic environments without inspecting them during circuit construction. -/
  interpretation : targetOracles.Interpretation → sourceOracles.Interpretation
  /-- Replace each native occurrence on exactly its existing physical systems. -/
  native : {count : Nat} → {layout : QuantumLayout count} →
    (application : GateModel.Application sourceGates layout) →
      ExactRealization targetGates targetOracles layout (fun _ => application.operator)
  /-- Implement a query using only access actually granted by the target model. -/
  query : {count : Nat} → {layout : QuantumLayout count} →
    (application : OracleModel.Application sourceOracles layout) →
      ExactRealization targetGates targetOracles layout (fun environment => application.operator
        (interpretation environment))

variable {sourceGates targetGates : GateModel} {sourceOracles targetOracles : OracleModel}

private def realizeLeaf
    (implementations : InstructionRealizations sourceGates sourceOracles targetGates targetOracles)
    {count : Nat} {layout : QuantumLayout count}
    (leaf : UnitaryLeaf sourceGates sourceOracles layout) :
    ExactRealization targetGates targetOracles layout (fun environment => leaf.operator
      (implementations.interpretation environment)) :=
  match leaf with
  | .gate application => implementations.native application
  | .oracle application => implementations.query application

private def realizeSequence
    (implementations :
      InstructionRealizations sourceGates sourceOracles targetGates targetOracles) :
    {count : Nat} → {layout : QuantumLayout count} →
      (sequence : UnitarySequence sourceGates sourceOracles layout) →
        ExactRealization targetGates targetOracles layout (fun environment =>
          sequence.toUnitary (implementations.interpretation environment))
  | _, layout, .id _ =>
      { circuit := identity targetGates targetOracles layout
        matrix_eq := fun _ => rfl }
  | _, _, .leaf leaf => realizeLeaf implementations leaf
  | _, _, .seq left right =>
      { circuit := (realizeSequence implementations left).circuit.seq
          (realizeSequence implementations right).circuit
        matrix_eq := by
          intro environment
          rw [seq_matrix, (realizeSequence implementations left).matrix_eq,
            (realizeSequence implementations right).matrix_eq]
          rfl }
  | _, _, .embed placement body =>
      { circuit := (realizeSequence implementations body).circuit.embed placement
        matrix_eq := by
          intro environment
          rw [embed_matrix, (realizeSequence implementations body).matrix_eq]
          rfl }
  | _, _, .parallel left right leftPlacement rightPlacement disjoint =>
      { circuit := parallel (realizeSequence implementations left).circuit
          (realizeSequence implementations right).circuit leftPlacement rightPlacement disjoint
        matrix_eq := by
          intro environment
          change
            rightPlacement.liftOperator ((realizeSequence implementations right).circuit.matrix
              environment) *
            leftPlacement.liftOperator ((realizeSequence implementations left).circuit.matrix
              environment) = _
          rw [(realizeSequence implementations left).matrix_eq,
            (realizeSequence implementations right).matrix_eq]
          rfl }
  | _, _, .iterate repetitions body =>
      { circuit := iterate repetitions (realizeSequence implementations body).circuit
        matrix_eq := by
          intro environment
          rw [iterate_matrix, (realizeSequence implementations body).matrix_eq]
          rfl }
  | _, _, .indexedProduct label steps start step =>
      { circuit := indexedProduct label steps (realizeSequence implementations start).circuit
          (fun index => (realizeSequence implementations (step index)).circuit)
        matrix_eq := by
          intro environment
          rw [indexedProduct_matrix, (realizeSequence implementations start).matrix_eq]
          change (List.ofFn fun index =>
            ((realizeSequence implementations (step index)).circuit.matrix environment)).foldl
              (fun accumulated next => next * accumulated) (start.toUnitary
                (implementations.interpretation environment)) = _
          simp only [(realizeSequence implementations _).matrix_eq]
          rfl }
  | _, _, .macroCall name body =>
      { circuit := macroCall name (realizeSequence implementations body).circuit
        matrix_eq := by
          intro environment
          rw [macroCall_matrix]
          exact (realizeSequence implementations body).matrix_eq environment }

/-- Substitute the supplied actual native words throughout the complete construction. -/
public def refine {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout)
    (implementations :
      InstructionRealizations sourceGates sourceOracles targetGates targetOracles) :
    UnitaryCircuit targetGates targetOracles layout :=
  (realizeSequence implementations circuit.sequence).circuit

/-- Substitution preserves the full operator, including phase and all spectator systems. -/
public lemma refine_matrix {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout)
    (implementations :
      InstructionRealizations sourceGates sourceOracles targetGates targetOracles)
    (environment : targetOracles.Interpretation) :
    ((circuit.refine implementations).matrix environment) = (circuit.matrix
      (implementations.interpretation environment)) :=
  (realizeSequence implementations circuit.sequence).matrix_eq environment

end

end QuantumAlg.UnitaryCircuit

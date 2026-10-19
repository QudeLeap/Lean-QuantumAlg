/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.Depth.Expr

/-!
# Dependency depth of exact native-word substitutions

Leaf durations come from the actual replacement circuits. Sequential sums,
disjoint parallel maxima and indexed repetitions retain their original structure.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {sourceGates targetGates : GateModel} {sourceOracles targetOracles : OracleModel}

private lemma realizeSequence_depth
    (implementations : InstructionRealizations sourceGates sourceOracles targetGates targetOracles)
    (sourceDuration : Resource.Event (.quantum sourceGates sourceOracles) → Nat)
    (targetDuration : Resource.Event (.quantum targetGates targetOracles) → Nat)
    (leafDepth : ∀ {count : Nat} {layout : QuantumLayout count}
      (leaf : UnitaryLeaf sourceGates sourceOracles layout),
      (realizeLeaf implementations leaf).circuit.evaluatedEventDepth targetDuration =
        sourceDuration leaf.event)
    {count : Nat} {layout : QuantumLayout count}
    (sequence : UnitarySequence sourceGates sourceOracles layout) :
    (realizeSequence implementations sequence).circuit.evaluatedEventDepth targetDuration =
      DepthExpr.depthEval sourceDuration sequence.eventDepth := by
  induction sequence with
  | id layout => rfl
  | leaf leaf => exact leafDepth leaf
  | seq left right leftIH rightIH =>
      change (realizeSequence implementations left).circuit.evaluatedEventDepth targetDuration +
        (realizeSequence implementations right).circuit.evaluatedEventDepth targetDuration =
          DepthExpr.depthEval sourceDuration left.eventDepth +
            DepthExpr.depthEval sourceDuration right.eventDepth
      rw [leftIH, rightIH]
  | embed placement body ih => exact ih
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      change max
        ((realizeSequence implementations left).circuit.evaluatedEventDepth targetDuration)
        ((realizeSequence implementations right).circuit.evaluatedEventDepth targetDuration) =
          max (DepthExpr.depthEval sourceDuration left.eventDepth)
            (DepthExpr.depthEval sourceDuration right.eventDepth)
      rw [leftIH, rightIH]
  | iterate repetitions body ih =>
      change repetitions *
        (realizeSequence implementations body).circuit.evaluatedEventDepth targetDuration =
          repetitions * DepthExpr.depthEval sourceDuration body.eventDepth
      rw [ih]
  | indexedProduct label steps start step startIH stepIH =>
      change (realizeSequence implementations start).circuit.evaluatedEventDepth targetDuration +
        (∑ index, (realizeSequence implementations (step index)).circuit.evaluatedEventDepth
          targetDuration) = _
      rw [startIH]
      simp only [stepIH]
      rfl
  | macroCall name body ih => exact ih

/-- Actual replacement words determine the complete dependency depth from their leaf durations. -/
public lemma refine_evaluatedEventDepth
    {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout)
    (implementations : InstructionRealizations sourceGates sourceOracles targetGates targetOracles)
    (sourceDuration : Resource.Event (.quantum sourceGates sourceOracles) → Nat)
    (targetDuration : Resource.Event (.quantum targetGates targetOracles) → Nat)
    (nativeDepth : ∀ {count : Nat} {layout : QuantumLayout count}
      (application : GateModel.Application sourceGates layout),
      (implementations.native application).circuit.evaluatedEventDepth targetDuration =
        sourceDuration (.gate application.coordinate))
    (queryDepth : ∀ {count : Nat} {layout : QuantumLayout count}
      (application : OracleModel.Application sourceOracles layout),
      (implementations.query application).circuit.evaluatedEventDepth targetDuration =
        sourceDuration (.oracle application.coordinate)) :
    (circuit.refine implementations).evaluatedEventDepth targetDuration =
      circuit.evaluatedEventDepth sourceDuration := by
  apply realizeSequence_depth implementations sourceDuration targetDuration
  intro count layout leaf
  cases leaf with
  | gate application => exact nativeDepth application
  | oracle application => exact queryDepth application

end

end QuantumAlg.UnitaryCircuit

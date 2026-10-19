/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.Depth.Expr

/-!
# Dependency depth of generated adjoints

Depth preservation requires a duration equation for each actual replacement.
Reversal preserves sequential sums and physically disjoint parallel maxima.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {sourceGates targetGates : GateModel} {sourceOracles targetOracles : OracleModel}

private lemma reverseWords_depth {count : Nat} {layout : QuantumLayout count}
    (duration : Resource.Event (.quantum targetGates targetOracles) → Nat)
    (words : List (UnitaryCircuit targetGates targetOracles layout)) :
    (reverseWords words).evaluatedEventDepth duration =
      (words.map fun word => word.evaluatedEventDepth duration).sum := by
  induction words with
  | nil => rfl
  | cons next rest ih =>
      change (reverseWords rest |>.seq next).evaluatedEventDepth duration = _
      rw [evaluatedEventDepth_seq, ih, List.map_cons, List.sum_cons]
      exact add_comm _ _

private lemma inverseSequence_depth
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles)
    (sourceDuration : Resource.Event (.quantum sourceGates sourceOracles) → Nat)
    (targetDuration : Resource.Event (.quantum targetGates targetOracles) → Nat)
    (leafDepth : ∀ {count : Nat} {layout : QuantumLayout count}
      (leaf : UnitaryLeaf sourceGates sourceOracles layout),
      (inverseLeaf implementations leaf).circuit.evaluatedEventDepth targetDuration =
        sourceDuration leaf.event)
    {count : Nat} {layout : QuantumLayout count}
    (sequence : UnitarySequence sourceGates sourceOracles layout) :
    (inverseSequence implementations sequence).circuit.evaluatedEventDepth targetDuration =
      DepthExpr.depthEval sourceDuration sequence.eventDepth := by
  induction sequence with
  | id layout => rfl
  | leaf leaf => exact leafDepth leaf
  | seq left right leftIH rightIH =>
      change (inverseSequence implementations right).circuit.evaluatedEventDepth targetDuration +
        (inverseSequence implementations left).circuit.evaluatedEventDepth targetDuration =
          DepthExpr.depthEval sourceDuration left.eventDepth +
            DepthExpr.depthEval sourceDuration right.eventDepth
      rw [leftIH, rightIH, add_comm]
  | embed placement body ih => exact ih
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      change max
        ((inverseSequence implementations right).circuit.evaluatedEventDepth targetDuration)
        ((inverseSequence implementations left).circuit.evaluatedEventDepth targetDuration) =
          max (DepthExpr.depthEval sourceDuration left.eventDepth)
            (DepthExpr.depthEval sourceDuration right.eventDepth)
      rw [leftIH, rightIH, max_comm]
  | iterate repetitions body ih =>
      change repetitions *
        (inverseSequence implementations body).circuit.evaluatedEventDepth targetDuration =
          repetitions * DepthExpr.depthEval sourceDuration body.eventDepth
      rw [ih]
  | indexedProduct label steps start step startIH stepIH =>
      change ((reverseWords (List.ofFn fun index =>
        (inverseSequence implementations (step index)).circuit)).seq
          (inverseSequence implementations start).circuit).evaluatedEventDepth targetDuration =
        DepthExpr.depthEval sourceDuration start.eventDepth +
          ∑ index, DepthExpr.depthEval sourceDuration (step index).eventDepth
      rw [evaluatedEventDepth_seq, reverseWords_depth, startIH]
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, stepIH]
      exact add_comm _ _
  | macroCall name body ih => exact ih

/-- Actual inverse words with matching leaf durations preserve the complete dependency depth. -/
public lemma dagger_evaluatedEventDepth
    {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout)
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles)
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
    (circuit.dagger implementations).evaluatedEventDepth targetDuration =
      circuit.evaluatedEventDepth sourceDuration := by
  apply inverseSequence_depth implementations sourceDuration targetDuration
  intro count layout leaf
  cases leaf with
  | gate application => exact nativeDepth application
  | oracle application => exact queryDepth application

end

end QuantumAlg.UnitaryCircuit

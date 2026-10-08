/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence

/-!
# Existing descriptive macros under actual adjoint generation

Reversal preserves macro multiplicities when the supplied inverse leaf words
introduce none of the observed name. The premise refers to those actual words;
it cannot replace native expansion or grant inverse oracle access.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {sourceGates targetGates : GateModel} {sourceOracles targetOracles : OracleModel}

private theorem reverseWords_macroCount (name : String)
    {count : Nat} {layout : QuantumLayout count}
    (words : List (UnitaryCircuit targetGates targetOracles layout)) :
    (reverseWords words).macroCount name = (words.map fun word => word.macroCount name).sum := by
  induction words with
  | nil => rfl
  | cons next rest ih =>
      change (reverseWords rest |>.seq next).macroCount name = _
      rw [macroCount_seq, ih, List.map_cons, List.sum_cons]
      exact add_comm _ _

private theorem inverseSequence_macroCount (name : String)
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles)
    (leafEmpty : ∀ {count : Nat} {layout : QuantumLayout count}
      (leaf : UnitaryLeaf sourceGates sourceOracles layout),
      (inverseLeaf implementations leaf).circuit.macroCount name = 0)
    {count : Nat} {layout : QuantumLayout count}
    (sequence : UnitarySequence sourceGates sourceOracles layout) :
    (inverseSequence implementations sequence).circuit.macroCount name =
      sequence.macroTrace.count name := by
  induction sequence with
  | id layout => rfl
  | leaf leaf => exact leafEmpty leaf
  | seq left right leftIH rightIH =>
      change ((inverseSequence implementations right).circuit.seq
        (inverseSequence implementations left).circuit).macroCount name = _
      rw [macroCount_seq, leftIH, rightIH]
      simp only [UnitarySequence.macroTrace, List.count_append, add_comm]
  | embed placement body ih =>
      exact (macroCount_embed placement _ name).trans ih
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      change (parallel (inverseSequence implementations right).circuit
        (inverseSequence implementations left).circuit rightPlacement leftPlacement
        disjoint.symm).macroCount name = _
      rw [macroCount_parallel, leftIH, rightIH]
      simp only [UnitarySequence.macroTrace, List.count_append, add_comm]
  | iterate repetitions body ih =>
      simp only [inverseSequence, macroCount, iterate, UnitarySequence.macroTrace,
        List.count_flatten, List.map_replicate, List.sum_replicate, nsmul_eq_mul] at ⊢
      exact congrArg (repetitions * ·) ih
  | indexedProduct label steps start step startIH stepIH =>
      change ((reverseWords (List.ofFn fun index =>
        (inverseSequence implementations (step index)).circuit)).seq
          (inverseSequence implementations start).circuit).macroCount name = _
      rw [macroCount_seq, reverseWords_macroCount, startIH]
      simp only [UnitarySequence.macroTrace, List.count_append, List.count_flatten,
        List.map_ofFn, List.sum_ofFn, Function.comp_def, stepIH, add_comm]
  | macroCall label body ih =>
      change (macroCall label (inverseSequence implementations body).circuit).macroCount name = _
      rw [macroCount_macroCall, ih]
      simp only [UnitarySequence.macroTrace, List.count_cons, beq_iff_eq]
      split <;> omega

/-- Macro-free inverse replacements preserve every occurrence already in the source word. -/
public theorem dagger_macroCount (name : String)
    {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout)
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles)
    (nativeEmpty : ∀ {count : Nat} {layout : QuantumLayout count}
      (application : GateModel.Application sourceGates layout),
      (implementations.native application).circuit.macroCount name = 0)
    (queryEmpty : ∀ {count : Nat} {layout : QuantumLayout count}
      (application : OracleModel.Application sourceOracles layout),
      (implementations.query application).circuit.macroCount name = 0) :
    (circuit.dagger implementations).macroCount name = circuit.macroCount name := by
  apply inverseSequence_macroCount name implementations
  intro count layout leaf
  cases leaf with
  | gate application => exact nativeEmpty application
  | oracle application => exact queryEmpty application

end

end QuantumAlg.UnitaryCircuit

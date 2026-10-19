/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Native
import all QuantumAlg.Components.Gates.ControlledPhase.Semantics
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
import all QuantumAlg.Components.Gates.Swap
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-! # Descriptive expansion annotations, separate from native source accounting -/

namespace QuantumAlg.QuantumFourierTransform.Lowering
noncomputable section

/-- One descriptive annotation is introduced by each native source instruction. -/
public def macroWeight (name : String) :
    Resource.Event (.quantum FourierGate.model .empty) → Nat
  | .gate .hadamard => if "hadamard" = name then 1 else 0
  | .gate .controlledPhase => if "controlled-phase" = name then 1 else 0
  | .gate .swap => if "swap" = name then 1 else 0
  | _ => 0

/-- Count the annotations introduced by actual lowered instruction words. -/
public def macroBudget (name : String) :
    ResourcePool (.quantum FourierGate.model .empty) →+ Nat where
  toFun pool := (pool.map (macroWeight name)).sum
  map_zero' := rfl
  map_add' _ _ := by simp

/-- Repeating a native source instruction repeats its introduced annotation. -/
public lemma macroBudget_singleton (name : String)
    (event : Resource.Event (.quantum FourierGate.model .empty)) (multiplicity : Nat) :
    macroBudget name (ResourcePool.singleton event multiplicity) =
      multiplicity * macroWeight name event := by
  change (Multiset.map (macroWeight name) (Multiset.replicate multiplicity event)).sum = _
  simp

private lemma nativeRealization_macroCount (name : String) (oracles : OracleModel)
    {count : Nat} {layout : QuantumLayout count}
    (application : GateModel.Application FourierGate.model layout) :
    (nativeRealization oracles application).circuit.macroCount name =
      macroBudget name (ResourcePool.singleton (.gate application.coordinate)) := by
  rw [macroBudget_singleton]
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  change (UnitaryCircuit.placeAt _ _ _ _
    (localRealization oracles token).circuit).macroCount name = _
  rw [UnitaryCircuit.placeAt_macroCount]
  cases token with
  | hadamard =>
      change ["hadamard"].count name = 1 * (if "hadamard" = name then 1 else 0)
      simp only [List.count_cons, List.count_nil, Nat.zero_add, Nat.one_mul, beq_iff_eq]
  | controlledPhase angle =>
      change ["controlled-phase"].count name =
        1 * (if "controlled-phase" = name then 1 else 0)
      simp only [List.count_cons, List.count_nil, Nat.zero_add, Nat.one_mul, beq_iff_eq]
  | swap =>
      change ["swap"].count name = 1 * (if "swap" = name then 1 else 0)
      simp only [List.count_cons, List.count_nil, Nat.zero_add, Nat.one_mul, beq_iff_eq]

private lemma realizeSequence_macroCount (name : String) (oracles : OracleModel)
    {count : Nat} {layout : QuantumLayout count}
    (sequence : UnitarySequence FourierGate.model .empty layout) :
    (UnitaryCircuit.realizeSequence (instructions oracles) sequence).circuit.macroCount name =
      sequence.macroTrace.count name + macroBudget name sequence.eventCost := by
  induction sequence with
  | id layout => simp [UnitaryCircuit.realizeSequence, UnitarySequence.macroTrace,
      UnitarySequence.eventCost, UnitaryCircuit.macroCount, UnitaryCircuit.identity]
  | leaf leaf =>
      cases leaf with
      | gate application =>
          simpa only [UnitarySequence.macroTrace, List.count_nil,
            UnitarySequence.eventCost, Nat.zero_add, UnitaryCircuit.realizeSequence,
            UnitaryCircuit.realizeLeaf, instructions, UnitaryLeaf.event] using
            nativeRealization_macroCount name oracles application
      | oracle application =>
          exact False.elim
            (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)
  | seq left right leftIH rightIH =>
      change ((UnitaryCircuit.realizeSequence (instructions oracles) left).circuit.seq
        (UnitaryCircuit.realizeSequence (instructions oracles) right).circuit).macroCount name = _
      rw [UnitaryCircuit.macroCount_seq, leftIH, rightIH]
      simp only [UnitarySequence.macroTrace, List.count_append, UnitarySequence.eventCost, map_add]
      omega
  | embed placement body ih =>
      exact (UnitaryCircuit.macroCount_embed placement _ name).trans ih
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      change (UnitaryCircuit.parallel
        (UnitaryCircuit.realizeSequence (instructions oracles) left).circuit
        (UnitaryCircuit.realizeSequence (instructions oracles) right).circuit
        leftPlacement rightPlacement disjoint).macroCount name = _
      rw [UnitaryCircuit.macroCount_parallel, leftIH, rightIH]
      simp only [UnitarySequence.macroTrace, List.count_append, UnitarySequence.eventCost, map_add]
      omega
  | iterate repetitions body ih =>
      simp only [UnitaryCircuit.realizeSequence, UnitaryCircuit.macroCount,
        UnitaryCircuit.iterate, UnitarySequence.macroTrace, List.count_flatten,
        List.map_replicate, List.sum_replicate, nsmul_eq_mul,
        UnitarySequence.eventCost, map_nsmul] at ⊢
      change repetitions *
        (UnitaryCircuit.realizeSequence (instructions oracles) body).circuit.macroCount name = _
      rw [ih]
      simp only [Nat.cast_id, Nat.mul_add]
  | indexedProduct label steps start step startIH stepIH =>
      simp only [UnitaryCircuit.realizeSequence, UnitaryCircuit.macroCount,
        UnitaryCircuit.indexedProduct, UnitarySequence.macroTrace, List.count_append,
        List.count_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def,
        UnitarySequence.eventCost, map_add, map_sum]
      change (UnitaryCircuit.realizeSequence (instructions oracles) start).circuit.macroCount name +
        (∑ index, (UnitaryCircuit.realizeSequence
          (instructions oracles) (step index)).circuit.macroCount name) = _
      rw [startIH]
      simp only [stepIH, Finset.sum_add_distrib]
      omega
  | macroCall label body ih =>
      change (UnitaryCircuit.macroCall label
        (UnitaryCircuit.realizeSequence (instructions oracles) body).circuit).macroCount name = _
      rw [UnitaryCircuit.macroCount_macroCall, ih]
      simp only [UnitarySequence.macroTrace, List.count_cons, beq_iff_eq,
        UnitarySequence.eventCost]
      split <;> omega

/-- Legacy annotations are observed on the actual lowered circuit, never used as native costs. -/
public lemma lower_macroCount (name : String) (oracles : OracleModel)
    {count : Nat} {layout : QuantumLayout count}
    (source : UnitaryCircuit FourierGate.model .empty layout) :
    (lower oracles source).macroCount name =
      source.macroCount name + macroBudget name source.eventCost :=
  realizeSequence_macroCount name oracles source.sequence

end
end QuantumAlg.QuantumFourierTransform.Lowering

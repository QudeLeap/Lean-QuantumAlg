/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Program
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Resources of one actual original-width oracle sample

The one-shot trace charges its actual basis preparation, every exponent Z,
and its final finite-bit packing operation. The original unitary retains its
own tensor critical path; its depth is not replaced by a sum of all gates.
All classical result cells stay resident beside the original quantum bank.
No reset or repetition budget is asserted here.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

/-- Original member events plus the actual preparation, terminal Zs and one paid packing. -/
def sampleEventBudget (N : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (preparation N).event +
    ((ShortDLP.preparationCircuit (parameters N)).eventCost +
      (ResourcePool.singleton (ShortDLP.oracleEvent N (parameters N)) +
        (ShortDLP.readoutCircuit (parameters N)).eventCost)) +
    (measurementBits N • ResourcePool.singleton (Circuit.zEvent 2) +
      ResourcePool.singleton
        (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))))

/-- The original unitary critical path surrounded by the actual chronological boundary events. -/
def sampleDuration (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  duration (preparation N).event +
    DepthExpr.depthEval duration
      (.seq (ShortDLP.preparationCircuit (parameters N)).eventDepth
        (.seq (.atom (ShortDLP.oracleEvent N (parameters N)))
          (ShortDLP.readoutCircuit (parameters N)).eventDepth)) +
    (measurementBits N * duration (Circuit.zEvent 2) +
      duration (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem readouts_events (path : (Circuit.measurementSequence
    (readouts base noQuantum N)).Path) :
    (Circuit.measurementSequence (readouts base noQuantum N)).eventTrace path =
      List.replicate (measurementBits N) (Circuit.zEvent 2) := by
  rw [Circuit.measurementSequence_eventTrace, readouts, List.map_ofFn]
  simp only [nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N)]
  exact List.ofFn_const _ _

private theorem readouts_duration (duration : Resource.Event .quantum → Nat)
    (path : (Circuit.measurementSequence (readouts base noQuantum N)).Path) :
    (Circuit.measurementSequence (readouts base noQuantum N)).depth duration path =
      measurementBits N * duration (Circuit.zEvent 2) := by
  rw [Circuit.measurementSequence_depth, readouts, List.map_ofFn]
  simp only [nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N)]
  simp only [Function.comp_def, List.ofFn_const, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]

/-- Exact ordered events retain the actual parameter-selected member and all boundary charges. -/
theorem nativeOracle_eventTrace (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).eventTrace path =
      [(preparation N).event] ++
        (ShortDLP.circuit (encoding input) (parameterUnit path.2.2.1.1)
          (parameterTarget path.2.2.1.1)).eventTrace ++
        (List.replicate (measurementBits N) (Circuit.zEvent 2) ++
          [.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))]) := by
  change [(preparation N).event] ++
    (((MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N)).eventTrace
      path.2.1.1 ++ []) ++
        ((member N (nativeOracle_context_wires base noQuantum N) input path.2.2.1.1).eventTrace ++
          ((Circuit.measurementSequence (readouts base noQuantum N)).eventTrace path.2.2.2.1 ++
            [.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))]))) = _
  rw [MeasurementCells.allocate_eventTrace, readouts_events]
  simp only [member, UnitaryCircuit.reindex_eventTrace, List.nil_append, List.append_nil,
    List.append_assoc]

/-- Every actual path has the same original oracle pool plus its charged boundary events. -/
theorem nativeOracle_resourcePool (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).resourcePool path = sampleEventBudget N := by
  rw [Circuit.resourcePool, nativeOracle_eventTrace]
  simp only [ResourcePool.ofList_append, ResourcePool.ofList_cons,
    ResourcePool.ofList_nil, add_zero,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, ShortDLP.circuit_eventCost,
    ResourcePool.ofList_replicate, ResourcePool.scale, sampleEventBudget]

/-- Arbitrary event durations preserve the original tensor depth and each real boundary step. -/
theorem nativeOracle_depth (input : Input N)
    (parameter : CInputRef base (ParameterShape N)) (duration : Resource.Event .quantum → Nat)
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).depth duration path = sampleDuration N duration := by
  change duration (preparation N).event +
    (((MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N)).depth
      duration path.2.1.1 + 0) +
      (DepthExpr.depthEval duration
        (member N (nativeOracle_context_wires base noQuantum N) input path.2.2.1.1).eventDepth +
        ((Circuit.measurementSequence (readouts base noQuantum N)).depth duration path.2.2.2.1 +
          duration
            (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N))))))) = _
  rw [MeasurementCells.allocate_depth, readouts_duration]
  simp only [member, UnitaryCircuit.reindex_eventDepth, ShortDLP.circuit_eventDepth,
    Nat.zero_add, Nat.add_zero, sampleDuration, Nat.add_assoc]

/-- The final resident context counts both result representations and the actual original bank. -/
theorem nativeOracle_context_residentSpace :
    (context base noQuantum N).residentSpace =
      SpacePool.ofShape (.bits (measurementBits N)) +
        measurementBits N • SpacePool.ofShape (.finite 2) +
          SpacePool.ofQuantumLayout (layout N) + base.residentSpace := by
  simp only [context, RuntimeCtx.residentSpace_addRetained, cellsContext,
    MeasurementCells.context_residentSpace, bankContext, RuntimeCtx.residentSpace_addOwnedLayout,
    add_assoc]

/-- New cells are owned; the original context determines its pre-existing auxiliary role. -/
theorem nativeOracle_context_auxiliarySpace :
    (context base noQuantum N).auxiliarySpace =
      SpacePool.ofShape (.bits (measurementBits N)) +
        measurementBits N • SpacePool.ofShape (.finite 2) +
          SpacePool.ofQuantumLayout (layout N) + base.auxiliarySpace := by
  simp only [context, RuntimeCtx.auxiliarySpace_addRetained, cellsContext,
    MeasurementCells.context_auxiliarySpace, bankContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    add_assoc]


private theorem visited (input : Input N) (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code base noQuantum N input parameter).visitedContexts path) :
    frame = base ∨
      (∃ used, used ≤ measurementBits N ∧
        frame = MeasurementCells.context (bankContext base noQuantum N) 2 used) ∨
      frame = context base noQuantum N := by
  change frame ∈ [base, bankContext base noQuantum N] ++
    (((MeasurementCells.allocate (bankContext base noQuantum N) 2
      (measurementBits N)).visitedContexts
      path.2.1.1 ++ [cellsContext base noQuantum N, context base noQuantum N]) ++
      ([context base noQuantum N] ++
        ((Circuit.measurementSequence (readouts base noQuantum N)).visitedContexts path.2.2.2.1 ++
          [context base noQuantum N]))) at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with (first | bank) | (allocation | (cells | final)) | final | measured | final
  · exact Or.inl first
  · exact Or.inr (Or.inl ⟨0, Nat.zero_le _, bank⟩)
  · exact Or.inr (Or.inl (MeasurementCells.allocate_visitedContexts _ _ _ _ _ allocation))
  · exact Or.inr (Or.inl ⟨measurementBits N, le_rfl, cells⟩)
  · exact Or.inr (Or.inr final)
  · exact Or.inr (Or.inr final)
  · exact Or.inr (Or.inr (List.mem_replicate.mp measured).2)
  · exact Or.inr (Or.inr final)

/-- The same path's resident peak is its complete final bank and real retained results. -/
theorem nativeOracle_peakResidentSpace (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).peakResidentSpace path =
      (context base noQuantum N).residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro frame present
    rcases visited base noQuantum N input parameter path frame present with first | cells | final
    · subst frame
      rw [nativeOracle_context_residentSpace]
      intro axis
      exact Nat.le_add_left _ _
    · obtain ⟨used, bounded, rfl⟩ := cells
      refine (MeasurementCells.context_residentSpace_mono _ 2 bounded).trans ?_
      change (cellsContext base noQuantum N).residentSpace ≤
        SpacePool.ofShape (.bits (measurementBits N)) +
          (cellsContext base noQuantum N).residentSpace
      intro axis
      exact Nat.le_add_left _ _
    · subst frame
      exact le_rfl
  · exact Circuit.output_residentSpace_le_peak _ path

/-- Auxiliary peak uses those same actual owned cells and keeps the original caller roles. -/
theorem nativeOracle_peakAuxiliarySpace (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).peakAuxiliarySpace path =
      (context base noQuantum N).auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro frame present
    rcases visited base noQuantum N input parameter path frame present with first | cells | final
    · subst frame
      rw [nativeOracle_context_auxiliarySpace]
      intro axis
      exact Nat.le_add_left _ _
    · obtain ⟨used, bounded, rfl⟩ := cells
      refine (MeasurementCells.context_auxiliarySpace_mono _ 2 bounded).trans ?_
      change (cellsContext base noQuantum N).auxiliarySpace ≤
        SpacePool.ofShape (.bits (measurementBits N)) +
          (cellsContext base noQuantum N).auxiliarySpace
      intro axis
      exact Nat.le_add_left _ _
    · subst frame
      exact le_rfl
  · exact Circuit.output_auxiliarySpace_le_peak _ path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

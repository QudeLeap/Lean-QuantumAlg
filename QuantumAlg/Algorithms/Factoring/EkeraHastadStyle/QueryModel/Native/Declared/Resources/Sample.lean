/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Independent resources for one declared original-width sample

The bank has one real zero-preparation occurrence per physical qubit. Its
preparations run in parallel, followed by the original Hadamard, query and
parallel inverse-Fourier dependencies. Exponent measurements and the paid
packing instruction follow in order. The allowances depend on the public
widths and fixed oracle model, never on the selected parameter or path.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

variable {N : Nat}

/-- One zero-preparation coordinate for each system in the original bank. -/
def preparationEventBudget (input : Input N) : ResourcePool (model input) :=
  ShortDLP.totalQubits (Native.parameters N) •
    ResourcePool.singleton (model := model input) (.preparation (2 : ℕ+))

/-- The fixed original member has a Hadamard word, one group query and two inverse QFTs. -/
def memberEventBudget (input : Input N) : ResourcePool (model input) :=
  (ShortDLP.DeclaredStage.prepare (Native.encoding input)).eventCost BitWord.model .empty +
    (ResourcePool.singleton (model := model input) (.oracle .groupOperation) +
      (ShortDLP.DeclaredStage.readout (Native.encoding input)).eventCost BitWord.model .empty) +
    (measurementBits N • ResourcePool.singleton (model := model input) (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model input)
        (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))))

/-- The independent one-shot allowance includes the real preparation of the whole bank. -/
def sampleEventBudget (input : Input N) : ResourcePool (model input) :=
  preparationEventBudget input + memberEventBudget input

/-- Independent fresh systems prepare in one parallel layer, including the empty case. -/
def preparationDuration (input : Input N) (duration : Resource.Event (model input) → Nat) : Nat :=
  if ShortDLP.totalQubits (Native.parameters N) = 0 then 0
  else duration (.preparation (2 : ℕ+))

/-- The primitive dependency expressions retain the two parallel inverse Fourier words. -/
def memberDuration (input : Input N) (duration : Resource.Event (model input) → Nat) : Nat :=
  DepthExpr.depthEval duration
    (.seq ((ShortDLP.DeclaredStage.prepare (Native.encoding input)).eventDepth BitWord.model .empty)
      (.seq (.atom (.oracle .groupOperation))
        ((ShortDLP.DeclaredStage.readout (Native.encoding input)).eventDepth
          BitWord.model .empty))) +
    (measurementBits N * duration (.measurement (2 : ℕ+)) +
      duration (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))))

/-- Preparation precedes the complete original member and its actual terminal instructions. -/
def sampleDuration (input : Input N) (duration : Resource.Event (model input) → Nat) : Nat :=
  preparationDuration input duration + memberDuration input duration

private theorem parallel_replicate_depth {Event : Type} (duration : Event → Nat)
    (event : Event) (count : Nat) :
    DepthExpr.depthEval duration ((List.replicate count event).foldr
      (fun item depth => DepthExpr.tensor (.atom item) depth) .id) =
        if count = 0 then 0 else duration event := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.foldr_cons, DepthExpr.depthEval, ih,
        Nat.succ_ne_zero, ↓reduceIte]
      split <;> simp

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- Actual zero preparation emits the dimension-two allowance on every path. -/
theorem declaredSample_prepare_resourcePool (path : (prepare base noQuantum N input).Path) :
    (prepare base noQuantum N input).resourcePool path = preparationEventBudget input := by
  exact ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (ShortDLP.declaredModel (Native.encoding input)) (Native.layout N) 2
    (fun _ => rfl) BitWord.model .empty

/-- The real preparation dependency is one parallel layer for every nonempty bank. -/
theorem declaredSample_prepare_depth (duration : Resource.Event (model input) → Nat)
    (path : (prepare base noQuantum N input).Path) :
    (prepare base noQuantum N input).depth duration path =
      preparationDuration input duration := by
  change DepthExpr.depthEval duration
    (ZeroPreparation.eventDepth AlgorithmGate.model
      (ShortDLP.declaredModel (Native.encoding input)) (Native.layout N) BitWord.model .empty) = _
  rw [ZeroPreparation.eventDepth,
    ZeroPreparation.zeroPreparation_uniform_trace AlgorithmGate.model
      (ShortDLP.declaredModel (Native.encoding input)) (Native.layout N) 2
      (fun _ => rfl) BitWord.model .empty]
  exact parallel_replicate_depth duration _ _

private theorem readouts_depth (duration : Resource.Event (model input) → Nat)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      (operations := BitWord.model) (readouts base noQuantum N)).Path) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      (operations := BitWord.model) (readouts base noQuantum N)).depth duration path =
        measurementBits N * duration (.measurement (2 : ℕ+)) := by
  rw [Circuit.measurementSequence_depth, readouts, List.map_ofFn]
  simp only [Native.nativeOracle_context_qubits N
    (Native.nativeOracle_context_wires base noQuantum N)]
  simp only [Function.comp_def, Circuit.zEvent, List.ofFn_const,
    List.sum_replicate, nsmul_eq_mul, Nat.cast_id]

/-- Parameter selection cannot change the member's declared event multiplicities. -/
theorem declaredSample_body_resourcePool (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).resourcePool path = memberEventBudget input := by
  change (selected base noQuantum N input parameter).resourcePool path.1 +
    (ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      (operations := BitWord.model) (readouts base noQuantum N)).eventTrace path.2.1) +
      ResourcePool.singleton (model := model input)
        (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N))))) = _
  rw [selected_resourcePool, readouts_events, ResourcePool.ofList_replicate]
  rfl

/-- Arbitrary native durations retain the actual member's parallel dependency expression. -/
theorem declaredSample_body_depth (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event (model input) → Nat)
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).depth duration path =
      memberDuration input duration := by
  change DepthExpr.depthEval duration
    ((Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
      input path.1.1).eventDepth BitWord.model .empty) +
    ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      (operations := BitWord.model) (readouts base noQuantum N)).depth duration path.2.1 +
      duration (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N))))) = _
  rw [readouts_depth]
  rfl

/-- The same actual one-shot execution meets its independent complete event allowance exactly. -/
theorem declaredSample_resourcePool (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).resourcePool path = sampleEventBudget input := by
  rw [code_resourcePool]
  have prepared := declaredSample_prepare_resourcePool base noQuantum N input path.1
  change ResourcePool.ofList ((prepare base noQuantum N input).eventTrace path.1) = _ at prepared
  rw [prepared]
  rfl

/-- Zero preparation, the selected stage and terminal writes keep their real dependency order. -/
theorem declaredSample_depth (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event (model input) → Nat)
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).depth duration path =
      sampleDuration input duration := by
  change (prepare base noQuantum N input).depth duration path.1 +
    (((MeasurementCells.allocate (model := model input)
      (Native.bankContext base noQuantum N) 2 (measurementBits N)).depth duration path.2.1.1 + 0) +
      (body base noQuantum N input parameter).depth duration path.2.2) = _
  rw [declaredSample_prepare_depth, MeasurementCells.allocate_depth, Nat.zero_add,
    declaredSample_body_depth]
  rfl

/-- The complete final bank contains both actual measurement representations. -/
theorem declaredSample_context_residentSpace :
    (Native.context base noQuantum N).residentSpace =
      SpacePool.ofShape (.bits (measurementBits N)) +
        measurementBits N • SpacePool.ofShape (.finite 2) +
          SpacePool.ofQuantumLayout (Native.layout N) + base.residentSpace := by
  simp only [Native.context, RuntimeCtx.residentSpace_addRetained, Native.cellsContext,
    MeasurementCells.context_residentSpace, Native.bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout, add_assoc]

/-- Every new cell is owned while all caller auxiliary roles retain their original meaning. -/
theorem declaredSample_context_auxiliarySpace :
    (Native.context base noQuantum N).auxiliarySpace =
      SpacePool.ofShape (.bits (measurementBits N)) +
        measurementBits N • SpacePool.ofShape (.finite 2) +
          SpacePool.ofQuantumLayout (Native.layout N) + base.auxiliarySpace := by
  simp only [Native.context, RuntimeCtx.auxiliarySpace_addRetained, Native.cellsContext,
    MeasurementCells.context_auxiliarySpace, Native.bankContext,
    RuntimeCtx.auxiliarySpace_addOwnedLayout, add_assoc]

private theorem body_visited (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (body base noQuantum N input parameter).visitedContexts path) :
    frame = Native.context base noQuantum N := by
  change frame ∈ List.append (α := RuntimeCtx .quantum) [Native.context base noQuantum N]
    (List.append (α := RuntimeCtx .quantum)
      ((Circuit.measurementSequence (gates := AlgorithmGate.model)
        (oracles := ShortDLP.declaredModel (Native.encoding input))
        (operations := BitWord.model) (readouts base noQuantum N)).visitedContexts path.2.1)
      [Native.context base noQuantum N]) at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  simp only [List.append_eq, List.mem_append, List.mem_singleton] at present
  rcases present with same | measured | same
  · exact same
  · exact (List.mem_replicate.mp measured).2
  · exact same

/-- The selected stage and its writes use exactly the original live resident context. -/
theorem declaredSample_body_peakResidentSpace (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).peakResidentSpace path =
      (Native.context base noQuantum N).residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro frame present
    rw [body_visited base noQuantum N input parameter path frame present]
  · exact Circuit.output_residentSpace_le_peak _ path

/-- The unchanged complete body context determines its actual auxiliary peak. -/
theorem declaredSample_body_peakAuxiliarySpace (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).peakAuxiliarySpace path =
      (Native.context base noQuantum N).auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro frame present
    rw [body_visited base noQuantum N input parameter path frame present]
  · exact Circuit.output_auxiliarySpace_le_peak _ path

private theorem sample_visited (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code base noQuantum N input parameter).visitedContexts path) :
    frame = base ∨
      (∃ used, used ≤ measurementBits N ∧
        frame = MeasurementCells.context (Native.bankContext base noQuantum N) 2 used) ∨
      frame = Native.context base noQuantum N := by
  change frame ∈ List.append (α := RuntimeCtx .quantum)
    [base, Native.bankContext base noQuantum N]
    (List.append (α := RuntimeCtx .quantum)
      (List.append (α := RuntimeCtx .quantum)
        ((MeasurementCells.allocate (model := model input)
          (Native.bankContext base noQuantum N) 2 (measurementBits N)).visitedContexts path.2.1.1)
        [Native.cellsContext base noQuantum N, Native.context base noQuantum N])
      ((body base noQuantum N input parameter).visitedContexts path.2.2)) at present
  simp only [List.append_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with (first | bank) | (allocation | (cells | final)) | sampled
  · exact Or.inl first
  · exact Or.inr (Or.inl ⟨0, Nat.zero_le _, bank⟩)
  · exact Or.inr (Or.inl (MeasurementCells.allocate_visitedContexts _ _ _ _ _ allocation))
  · exact Or.inr (Or.inl ⟨measurementBits N, le_rfl, cells⟩)
  · exact Or.inr (Or.inr final)
  · exact Or.inr (Or.inr (body_visited base noQuantum N input parameter path.2.2 frame sampled))

/-- The complete one-shot peak is the final bank together with both retained result formats. -/
theorem declaredSample_peakResidentSpace (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).peakResidentSpace path =
      (Native.context base noQuantum N).residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro frame present
    rcases sample_visited base noQuantum N input parameter path frame present with
      first | cells | final
    · subst frame
      rw [declaredSample_context_residentSpace]
      intro axis
      exact Nat.le_add_left _ _
    · obtain ⟨used, bounded, rfl⟩ := cells
      refine (MeasurementCells.context_residentSpace_mono _ 2 bounded).trans ?_
      change (Native.cellsContext base noQuantum N).residentSpace ≤
        SpacePool.ofShape (.bits (measurementBits N)) +
          (Native.cellsContext base noQuantum N).residentSpace
      intro axis
      exact Nat.le_add_left _ _
    · subst frame
      exact le_rfl
  · exact Circuit.output_residentSpace_le_peak _ path

/-- The same actual path counts owned allocations and preserves all pre-existing roles. -/
theorem declaredSample_peakAuxiliarySpace (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).peakAuxiliarySpace path =
      (Native.context base noQuantum N).auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro frame present
    rcases sample_visited base noQuantum N input parameter path frame present with
      first | cells | final
    · subst frame
      rw [declaredSample_context_auxiliarySpace]
      intro axis
      exact Nat.le_add_left _ _
    · obtain ⟨used, bounded, rfl⟩ := cells
      refine (MeasurementCells.context_auxiliarySpace_mono _ 2 bounded).trans ?_
      change (Native.cellsContext base noQuantum N).auxiliarySpace ≤
        SpacePool.ofShape (.bits (measurementBits N)) +
          (Native.cellsContext base noQuantum N).auxiliarySpace
      intro axis
      exact Nat.le_add_left _ _
    · subst frame
      exact le_rfl
  · exact Circuit.output_auxiliarySpace_le_peak _ path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

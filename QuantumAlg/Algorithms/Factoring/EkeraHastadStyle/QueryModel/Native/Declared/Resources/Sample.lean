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
def preparationEventBudget (N : Nat) : ResourcePool (model N) :=
  ShortDLP.totalQubits (Native.parameters N) •
    ResourcePool.singleton (model := model N) (.preparation (2 : ℕ+))

/-- The fixed original member has a Hadamard word, one group query and two inverse QFTs. -/
def memberEventBudget (N : Nat) : ResourcePool (model N) :=
  (ShortDLP.DeclaredStage.prepare N (Native.parameters N)).eventCost BitWord.model .empty +
    (ResourcePool.singleton (model := model N) (.oracle .groupOperation) +
      (ShortDLP.DeclaredStage.readout N (Native.parameters N)).eventCost BitWord.model .empty) +
    (measurementBits N • ResourcePool.singleton (model := model N) (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model N)
        (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))))

/-- The independent one-shot allowance includes the real preparation of the whole bank. -/
def sampleEventBudget (N : Nat) : ResourcePool (model N) :=
  preparationEventBudget N + memberEventBudget N

/-- Independent fresh systems prepare in one parallel layer, including the empty case. -/
def preparationDuration (N : Nat) (duration : Resource.Event (model N) → Nat) : Nat :=
  if ShortDLP.totalQubits (Native.parameters N) = 0 then 0
  else duration (.preparation (2 : ℕ+))

/-- The primitive dependency expressions retain the two parallel inverse Fourier words. -/
def memberDuration (N : Nat) (duration : Resource.Event (model N) → Nat) : Nat :=
  DepthExpr.depthEval duration
    (.seq ((ShortDLP.DeclaredStage.prepare N (Native.parameters N)).eventDepth BitWord.model .empty)
      (.seq (.atom (.oracle .groupOperation))
        ((ShortDLP.DeclaredStage.readout N (Native.parameters N)).eventDepth
          BitWord.model .empty))) +
    (measurementBits N * duration (.measurement (2 : ℕ+)) +
      duration (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))))

/-- Preparation precedes the complete original member and its actual terminal instructions. -/
def sampleDuration (N : Nat) (duration : Resource.Event (model N) → Nat) : Nat :=
  preparationDuration N duration + memberDuration N duration

private lemma parallel_replicate_depth {Event : Type} (duration : Event → Nat)
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
  (N : Nat)

/-- Actual zero preparation emits the dimension-two allowance on every path. -/
lemma declaredSample_prepare_resourcePool (path : (prepare base noQuantum N).Path) :
    (prepare base noQuantum N).resourcePool path = preparationEventBudget N := by
  exact ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (ShortDLP.declaredModel N (Native.parameters N)) (Native.layout N) 2
    (fun _ => rfl) BitWord.model .empty

/-- The real preparation dependency is one parallel layer for every nonempty bank. -/
lemma declaredSample_prepare_depth (duration : Resource.Event (model N) → Nat)
    (path : (prepare base noQuantum N).Path) :
    (prepare base noQuantum N).depth duration path =
      preparationDuration N duration := by
  change DepthExpr.depthEval duration
    (ZeroPreparation.eventDepth AlgorithmGate.model
      (ShortDLP.declaredModel N (Native.parameters N)) (Native.layout N) BitWord.model .empty) = _
  rw [ZeroPreparation.eventDepth,
    ZeroPreparation.zeroPreparation_uniform_trace AlgorithmGate.model
      (ShortDLP.declaredModel N (Native.parameters N)) (Native.layout N) 2
      (fun _ => rfl) BitWord.model .empty]
  exact parallel_replicate_depth duration _ _

private lemma readouts_depth (duration : Resource.Event (model N) → Nat)
    (path : (Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel N (Native.parameters N))
      (operations := BitWord.model) (readouts base noQuantum N)).Path) :
    (Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel N (Native.parameters N))
      (operations := BitWord.model) (readouts base noQuantum N)).depth duration path =
        measurementBits N * duration (.measurement (2 : ℕ+)) := by
  rw [Circuit.measurementSequence_depth, readouts, List.map_ofFn]
  simp only [Native.nativeOracle_context_qubits N
    (Native.nativeOracle_context_wires base noQuantum N)]
  simp only [Function.comp_def, Circuit.zEvent, List.ofFn_const,
    List.sum_replicate, nsmul_eq_mul, Nat.cast_id]

/-- Parameter selection cannot change the member's declared event multiplicities. -/
lemma declaredSample_body_resourcePool (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N parameter).Path) :
    (body base noQuantum N parameter).resourcePool path = memberEventBudget N := by
  change (selected base noQuantum N parameter).resourcePool path.1 +
    (ResourcePool.ofList ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel N (Native.parameters N))
      (operations := BitWord.model) (readouts base noQuantum N)).eventTrace path.2.1) +
      ResourcePool.singleton (model := model N)
        (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N))))) = _
  rw [selected_resourcePool, readouts_events, ResourcePool.ofList_replicate]
  rfl

/-- Arbitrary native durations retain the actual member's parallel dependency expression. -/
lemma declaredSample_body_depth (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event (model N) → Nat)
    (path : (body base noQuantum N parameter).Path) :
    (body base noQuantum N parameter).depth duration path =
      memberDuration N duration := by
  change DepthExpr.depthEval duration
    ((Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
      path.1.1).eventDepth BitWord.model .empty) +
    ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel N (Native.parameters N))
      (operations := BitWord.model) (readouts base noQuantum N)).depth duration path.2.1 +
      duration (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N))))) = _
  rw [readouts_depth]
  rfl

/-- The same actual one-shot execution meets its independent complete event allowance exactly. -/
lemma declaredSample_resourcePool (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N parameter).Path) :
    (code base noQuantum N parameter).resourcePool path = sampleEventBudget N := by
  rw [code_resourcePool]
  have prepared := declaredSample_prepare_resourcePool base noQuantum N path.1
  change ResourcePool.ofList ((prepare base noQuantum N).eventTrace path.1) = _ at prepared
  rw [prepared]
  rfl

/-- Zero preparation, the selected stage and terminal writes keep their real dependency order. -/
lemma declaredSample_depth (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event (model N) → Nat)
    (path : (code base noQuantum N parameter).Path) :
    (code base noQuantum N parameter).depth duration path =
      sampleDuration N duration := by
  change (prepare base noQuantum N).depth duration path.1 +
    (((MeasurementCells.allocate (model := model N)
      (Native.bankContext base noQuantum N) 2 (measurementBits N)).depth duration path.2.1.1 + 0) +
      (body base noQuantum N parameter).depth duration path.2.2) = _
  rw [declaredSample_prepare_depth, MeasurementCells.allocate_depth, Nat.zero_add,
    declaredSample_body_depth]
  rfl

/-- The complete final bank contains both actual measurement representations. -/
lemma declaredSample_context_residentSpace :
    (Native.context base noQuantum N).residentSpace =
      SpacePool.ofShape (.bits (measurementBits N)) +
        measurementBits N • SpacePool.ofShape (.finite 2) +
          SpacePool.ofQuantumLayout (Native.layout N) + base.residentSpace := by
  simp only [Native.context, RuntimeCtx.residentSpace_addRetained, Native.cellsContext,
    MeasurementCells.context_residentSpace, Native.bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout, add_assoc]

/-- Every new cell is owned while all caller auxiliary roles retain their original meaning. -/
lemma declaredSample_context_auxiliarySpace :
    (Native.context base noQuantum N).auxiliarySpace =
      SpacePool.ofShape (.bits (measurementBits N)) +
        measurementBits N • SpacePool.ofShape (.finite 2) +
          SpacePool.ofQuantumLayout (Native.layout N) + base.auxiliarySpace := by
  simp only [Native.context, RuntimeCtx.auxiliarySpace_addRetained, Native.cellsContext,
    MeasurementCells.context_auxiliarySpace, Native.bankContext,
    RuntimeCtx.auxiliarySpace_addOwnedLayout, add_assoc]

private lemma body_visited (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N parameter).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (body base noQuantum N parameter).visitedContexts path) :
    frame = Native.context base noQuantum N := by
  change frame ∈ List.append (α := RuntimeCtx .quantum) [Native.context base noQuantum N]
    (List.append (α := RuntimeCtx .quantum)
      ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
        (oracles := ShortDLP.declaredModel N (Native.parameters N))
        (operations := BitWord.model) (readouts base noQuantum N)).visitedContexts path.2.1)
      [Native.context base noQuantum N]) at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  simp only [List.append_eq, List.mem_append, List.mem_singleton] at present
  rcases present with same | measured | same
  · exact same
  · exact (List.mem_replicate.mp measured).2
  · exact same

/-- The selected stage and its writes use exactly the original live resident context. -/
lemma declaredSample_body_peakResidentSpace (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N parameter).Path) :
    (body base noQuantum N parameter).peakResidentSpace path =
      (Native.context base noQuantum N).residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro frame present
    rw [body_visited base noQuantum N parameter path frame present]
  · exact Circuit.output_residentSpace_le_peak _ path

/-- The unchanged complete body context determines its actual auxiliary peak. -/
lemma declaredSample_body_peakAuxiliarySpace (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N parameter).Path) :
    (body base noQuantum N parameter).peakAuxiliarySpace path =
      (Native.context base noQuantum N).auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro frame present
    rw [body_visited base noQuantum N parameter path frame present]
  · exact Circuit.output_auxiliarySpace_le_peak _ path

private lemma sample_visited (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N parameter).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code base noQuantum N parameter).visitedContexts path) :
    frame = base ∨
      (∃ used, used ≤ measurementBits N ∧
        frame = MeasurementCells.context (Native.bankContext base noQuantum N) 2 used) ∨
      frame = Native.context base noQuantum N := by
  change frame ∈ List.append (α := RuntimeCtx .quantum)
    [base, Native.bankContext base noQuantum N]
    (List.append (α := RuntimeCtx .quantum)
      (List.append (α := RuntimeCtx .quantum)
        ((MeasurementCells.allocate (model := model N)
          (Native.bankContext base noQuantum N) 2 (measurementBits N)).visitedContexts path.2.1.1)
        [Native.cellsContext base noQuantum N, Native.context base noQuantum N])
      ((body base noQuantum N parameter).visitedContexts path.2.2)) at present
  simp only [List.append_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with (first | bank) | (allocation | (cells | final)) | sampled
  · exact Or.inl first
  · exact Or.inr (Or.inl ⟨0, Nat.zero_le _, bank⟩)
  · exact Or.inr (Or.inl (MeasurementCells.allocate_visitedContexts _ _ _ _ _ allocation))
  · exact Or.inr (Or.inl ⟨measurementBits N, le_rfl, cells⟩)
  · exact Or.inr (Or.inr final)
  · exact Or.inr (Or.inr (body_visited base noQuantum N parameter path.2.2 frame sampled))

/-- The complete one-shot peak is the final bank together with both retained result formats. -/
lemma declaredSample_peakResidentSpace (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N parameter).Path) :
    (code base noQuantum N parameter).peakResidentSpace path =
      (Native.context base noQuantum N).residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro frame present
    rcases sample_visited base noQuantum N parameter path frame present with
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
lemma declaredSample_peakAuxiliarySpace (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N parameter).Path) :
    (code base noQuantum N parameter).peakAuxiliarySpace path =
      (Native.context base noQuantum N).auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro frame present
    rcases sample_visited base noQuantum N parameter path frame present with
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

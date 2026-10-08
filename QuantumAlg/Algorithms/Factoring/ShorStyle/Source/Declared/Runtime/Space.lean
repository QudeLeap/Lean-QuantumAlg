/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Space
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Independent full live-space allowances for actual complete Shor rounds

Both ledgers retain the caller, the original source sample and full parameter,
all physical phase outcomes and the packed word. Simultaneous sampler and
complete arithmetic scratch are bounded alongside those surviving cells.
The final bank reset uses one real lexical measurement cell.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

/-- The real packed phase word and each retained finite readout. -/
def Storage.resultSpace (N : Nat) : SpacePool .quantum :=
  phaseBits N • SpacePool.ofShape (.finite 2) + SpacePool.ofShape (.bits (phaseBits N))

/-- Full simultaneous sampler and recovery allowance, with the one real reset cell. -/
def completionAdditionalSpace (N : Nat) : SpacePool .quantum :=
  Sampler.Retained.additionalSpace .quantum (modulusBits N) + Storage.resultSpace N +
    FactorRecovery.NativeFactorScope.spaceBound .quantum N + SpacePool.ofShape (.finite 2)

/-- Real observation cells retain their full capacity beside the incoming frame. -/
theorem Storage.context_resident (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Storage.context ctx N).residentSpace = ctx.residentSpace + Storage.resultSpace N := by
  rw [Storage.context, MeasurementCells.context_residentSpace, Storage.resultContext,
    RuntimeCtx.residentSpace_addRetained]
  unfold Storage.resultSpace
  ac_rfl

/-- All actual sampled and measured cells coexist in the completed round's live frame. -/
theorem Iteration.context_resident (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Iteration.context ctx N).residentSpace = ctx.residentSpace +
      (Sampler.Retained.resultSpace .quantum (modulusBits N) + Storage.resultSpace N) := by
  rw [Iteration.context, Storage.context_resident, Iteration.sampledContext,
    Sampler.Retained.samplerRetained_context_resident]
  exact add_assoc _ _ _

private theorem selected_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (selected ctx N input sameWires parameter).Path) :
    (selected ctx N input sameWires parameter).peakResidentSpace path ≤
      (Storage.context ctx N).residentSpace := by
  rcases path with ⟨value, selectedPath⟩
  exact (Circuit.peakResidentSpace_unitary (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    (member N ((Storage.quantumWires ctx N).trans sameWires) input value) selectedPath).le

private theorem readouts_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts ctx N sameWires)).Path) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts ctx N sameWires)).peakResidentSpace path ≤
        (Storage.context ctx N).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  rw [Circuit.measurementSequence_visitedContexts] at present
  have same : frame = Storage.context ctx N := (List.mem_replicate.mp present).2
  subst frame
  exact le_rfl

private theorem allocation_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (path : (allocate ctx N input).Path) :
    (allocate ctx N input).peakResidentSpace path ≤ (Storage.context ctx N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (Circuit.retain (model := executionModel input) ctx ctx.canonicalFreshKey
      (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (MeasurementCells.allocate (model := executionModel input) (Storage.resultContext ctx N)
      2 (phaseBits N)) path).le.trans ?_
  apply SpacePool.max_le
  · rw [Circuit.peakResidentSpace_retain]
    change (Storage.resultContext ctx N).residentSpace ≤
      (MeasurementCells.context (Storage.resultContext ctx N) 2 (phaseBits N)).residentSpace
    rw [MeasurementCells.context_residentSpace]
    exact fun axis => Nat.le_add_left _ _
  · exact MeasurementCells.allocate_peakResidentSpace (model := executionModel input)
      (Storage.resultContext ctx N) 2 (phaseBits N) path.2

private theorem body_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (body ctx N input sameWires parameter).Path) :
    (body ctx N input sameWires parameter).peakResidentSpace path ≤
      (Storage.context ctx N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq (selected ctx N input sameWires parameter)
    ((Circuit.measurementSequence (readouts ctx N sameWires)).seq
      (Circuit.classical (BitWord.application (packing ctx N)))) path).le.trans ?_
  apply SpacePool.max_le
  · exact selected_resident_le ctx N input sameWires parameter path.1
  · refine (Circuit.peakResidentSpace_seq (Circuit.measurementSequence (readouts ctx N sameWires))
      (Circuit.classical (BitWord.application (packing ctx N))) path.2).le.trans ?_
    exact SpacePool.max_le (readouts_resident_le ctx N input sameWires path.2.1)
      (Circuit.peakResidentSpace_classical (model := executionModel input)
        (BitWord.application (packing ctx N)) path.2.2).le

/-- The genuine observation allocation and body fit their complete surviving storage frame. -/
theorem code_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (Runtime.code ctx N input sameWires parameter).Path) :
    (Runtime.code ctx N input sameWires parameter).peakResidentSpace path ≤
      (Storage.context ctx N).residentSpace :=
  (Circuit.peakResidentSpace_seq (allocate ctx N input)
    (body ctx N input sameWires parameter) path).le.trans
      (SpacePool.max_le (allocation_resident_le ctx N input path.1)
        (body_resident_le ctx N input sameWires parameter path.2))

private theorem retained_resident_le (N : Nat) :
    Sampler.Retained.resultSpace .quantum (modulusBits N) ≤
      Sampler.Retained.additionalSpace .quantum (modulusBits N) := by
  intro axis
  cases axis with
  | classicalBits =>
      simp [Sampler.Retained.resultSpace, Sampler.Retained.additionalSpace, SpacePool.ofShape]
      omega
  | quantumSystems dimension =>
      simp [Sampler.Retained.resultSpace, Sampler.Retained.additionalSpace, SpacePool.ofShape]

/-- The actual sampler and observation count all temporary and retained storage together. -/
theorem Iteration.code_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (path : (Iteration.code ctx N input sameWires).Path) :
    (Iteration.code ctx N input sameWires).peakResidentSpace path ≤
      ctx.residentSpace + (Sampler.Retained.additionalSpace .quantum (modulusBits N) +
        Storage.resultSpace N) := by
  refine (Circuit.peakResidentSpace_seq
    (Sampler.Retained.circuit (model := executionModel input) ctx N)
    (Runtime.code (Iteration.sampledContext ctx N) N input
      ((Iteration.sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)) path).le.trans ?_
  apply SpacePool.max_le
  · have sampled : (Sampler.Retained.circuit (model := executionModel input)
        ctx N).peakResidentSpace path.1 ≤
          ctx.residentSpace + Sampler.Retained.additionalSpace .quantum (modulusBits N) :=
        Sampler.Retained.samplerRetained_resident_le (model := executionModel input) ctx N path.1
    exact sampled.trans (fun axis => by
      simp only [Pi.add_apply]
      omega)
  · have observed := Runtime.code_resident_le (Iteration.sampledContext ctx N) N input
      ((Iteration.sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef) path.2
    have storage : (Storage.context (Iteration.sampledContext ctx N) N).residentSpace =
        (ctx.residentSpace + Sampler.Retained.resultSpace .quantum (modulusBits N)) +
          Storage.resultSpace N :=
      (Storage.context_resident (Iteration.sampledContext ctx N) N).trans
        (congrArg (fun pool => pool + Storage.resultSpace N)
          (Sampler.Retained.samplerRetained_context_resident ctx N))
    have bounded := observed.trans_eq storage
    exact bounded.trans (fun axis => by
      have capacity := retained_resident_le N axis
      simp only [Pi.add_apply] at *
      omega)

/-- Recovery and reset scratch remain beside every surviving result and caller. -/
theorem Completion.code_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Completion.code ctx N input sameWires cells result).Path) :
    (Completion.code ctx N input sameWires cells result).peakResidentSpace path ≤
      ctx.residentSpace + completionAdditionalSpace N := by
  rcases path with ⟨iterationPath, recoveryPath, resetPath⟩
  refine (Circuit.peakResidentSpace_seq (Iteration.code ctx N input sameWires)
    ((Completion.feedback ctx N input cells result).seq
      (reset (Iteration.context ctx N) N input
        ((Iteration.quantumWires ctx N).trans sameWires)))
      ⟨iterationPath, recoveryPath, resetPath⟩).le.trans ?_
  apply SpacePool.max_le
  · exact (Iteration.code_resident_le ctx N input sameWires iterationPath).trans (fun axis => by
      simp only [completionAdditionalSpace, Pi.add_apply] at *
      omega)
  · refine (Circuit.peakResidentSpace_seq (Completion.feedback ctx N input cells result)
      (reset (Iteration.context ctx N) N input
        ((Iteration.quantumWires ctx N).trans sameWires)) ⟨recoveryPath, resetPath⟩).le.trans ?_
    apply SpacePool.max_le
    · have recovered := NativeFactorScan.visit_resident_le (model := executionModel input)
        input (Completion.inputs ctx N) (Completion.cells ctx N cells)
        (Completion.liftWrite ctx N result) recoveryPath
      change _ ≤ (Iteration.context ctx N).residentSpace +
        FactorRecovery.NativeFactorScope.spaceBound .quantum N at recovered
      rw [Iteration.context_resident] at recovered
      exact recovered.trans (fun axis => by
        have capacity := retained_resident_le N axis
        change _ ≤ _
        simp only [completionAdditionalSpace, Pi.add_apply] at *
        omega)
    · have resetPeak : (reset (Iteration.context ctx N) N input
          ((Iteration.quantumWires ctx N).trans sameWires)).peakResidentSpace resetPath =
            SpacePool.ofShape (.finite 2) + (Iteration.context ctx N).residentSpace :=
        ZReset.BankScope.zResetBankScope_peakResidentSpace
        (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
        (operations := BitWord.model)
        (shorDeclared_context_qubits N ((Iteration.quantumWires ctx N).trans sameWires))
        resetPath
      rw [resetPeak, Iteration.context_resident]
      intro axis
      have capacity := retained_resident_le N axis
      change _ ≤ _
      simp only [completionAdditionalSpace, Pi.add_apply] at *
      omega

/-- Real observation cells retain their full capacity beside the incoming frame. -/
theorem Storage.context_auxiliary (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Storage.context ctx N).auxiliarySpace = ctx.auxiliarySpace + Storage.resultSpace N := by
  rw [Storage.context, MeasurementCells.context_auxiliarySpace, Storage.resultContext,
    RuntimeCtx.auxiliarySpace_addRetained]
  unfold Storage.resultSpace
  ac_rfl

/-- All actual sampled and measured cells coexist in the completed round's live frame. -/
theorem Iteration.context_auxiliary (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Iteration.context ctx N).auxiliarySpace = ctx.auxiliarySpace +
      (Sampler.Retained.resultSpace .quantum (modulusBits N) + Storage.resultSpace N) := by
  rw [Iteration.context, Storage.context_auxiliary, Iteration.sampledContext,
    Sampler.Retained.samplerRetained_context_auxiliary]
  exact add_assoc _ _ _

private theorem selected_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (selected ctx N input sameWires parameter).Path) :
    (selected ctx N input sameWires parameter).peakAuxiliarySpace path ≤
      (Storage.context ctx N).auxiliarySpace := by
  rcases path with ⟨value, selectedPath⟩
  exact (Circuit.peakAuxiliarySpace_unitary (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    (member N ((Storage.quantumWires ctx N).trans sameWires) input value) selectedPath).le

private theorem readouts_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts ctx N sameWires)).Path) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts ctx N sameWires)).peakAuxiliarySpace path ≤
        (Storage.context ctx N).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  rw [Circuit.measurementSequence_visitedContexts] at present
  have same : frame = Storage.context ctx N := (List.mem_replicate.mp present).2
  subst frame
  exact le_rfl

private theorem allocation_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (path : (allocate ctx N input).Path) :
    (allocate ctx N input).peakAuxiliarySpace path ≤ (Storage.context ctx N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Circuit.retain (model := executionModel input) ctx ctx.canonicalFreshKey
      (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (MeasurementCells.allocate (model := executionModel input) (Storage.resultContext ctx N)
      2 (phaseBits N)) path).le.trans ?_
  apply SpacePool.max_le
  · rw [Circuit.peakAuxiliarySpace_retain]
    change (Storage.resultContext ctx N).auxiliarySpace ≤
      (MeasurementCells.context (Storage.resultContext ctx N) 2 (phaseBits N)).auxiliarySpace
    rw [MeasurementCells.context_auxiliarySpace]
    exact fun axis => Nat.le_add_left _ _
  · exact MeasurementCells.allocate_peakAuxiliarySpace (model := executionModel input)
      (Storage.resultContext ctx N) 2 (phaseBits N) path.2

private theorem body_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (body ctx N input sameWires parameter).Path) :
    (body ctx N input sameWires parameter).peakAuxiliarySpace path ≤
      (Storage.context ctx N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (selected ctx N input sameWires parameter)
    ((Circuit.measurementSequence (readouts ctx N sameWires)).seq
      (Circuit.classical (BitWord.application (packing ctx N)))) path).le.trans ?_
  apply SpacePool.max_le
  · exact selected_auxiliary_le ctx N input sameWires parameter path.1
  · refine (Circuit.peakAuxiliarySpace_seq (Circuit.measurementSequence (readouts ctx N sameWires))
      (Circuit.classical (BitWord.application (packing ctx N))) path.2).le.trans ?_
    exact SpacePool.max_le (readouts_auxiliary_le ctx N input sameWires path.2.1)
      (Circuit.peakAuxiliarySpace_classical (model := executionModel input)
        (BitWord.application (packing ctx N)) path.2.2).le

/-- The genuine observation allocation and body fit their complete surviving storage frame. -/
theorem code_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (Runtime.code ctx N input sameWires parameter).Path) :
    (Runtime.code ctx N input sameWires parameter).peakAuxiliarySpace path ≤
      (Storage.context ctx N).auxiliarySpace :=
  (Circuit.peakAuxiliarySpace_seq (allocate ctx N input)
    (body ctx N input sameWires parameter) path).le.trans
      (SpacePool.max_le (allocation_auxiliary_le ctx N input path.1)
        (body_auxiliary_le ctx N input sameWires parameter path.2))

private theorem retained_auxiliary_le (N : Nat) :
    Sampler.Retained.resultSpace .quantum (modulusBits N) ≤
      Sampler.Retained.additionalSpace .quantum (modulusBits N) := by
  intro axis
  cases axis with
  | classicalBits =>
      simp [Sampler.Retained.resultSpace, Sampler.Retained.additionalSpace, SpacePool.ofShape]
      omega
  | quantumSystems dimension =>
      simp [Sampler.Retained.resultSpace, Sampler.Retained.additionalSpace, SpacePool.ofShape]

/-- The actual sampler and observation count all temporary and retained storage together. -/
theorem Iteration.code_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (path : (Iteration.code ctx N input sameWires).Path) :
    (Iteration.code ctx N input sameWires).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + (Sampler.Retained.additionalSpace .quantum (modulusBits N) +
        Storage.resultSpace N) := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Sampler.Retained.circuit (model := executionModel input) ctx N)
    (Runtime.code (Iteration.sampledContext ctx N) N input
      ((Iteration.sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)) path).le.trans ?_
  apply SpacePool.max_le
  · have sampled : (Sampler.Retained.circuit (model := executionModel input)
        ctx N).peakAuxiliarySpace path.1 ≤
          ctx.auxiliarySpace + Sampler.Retained.additionalSpace .quantum (modulusBits N) :=
        Sampler.Retained.samplerRetained_auxiliary_le (model := executionModel input) ctx N path.1
    exact sampled.trans (fun axis => by
      simp only [Pi.add_apply]
      omega)
  · have observed := Runtime.code_auxiliary_le (Iteration.sampledContext ctx N) N input
      ((Iteration.sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef) path.2
    have storage : (Storage.context (Iteration.sampledContext ctx N) N).auxiliarySpace =
        (ctx.auxiliarySpace + Sampler.Retained.resultSpace .quantum (modulusBits N)) +
          Storage.resultSpace N :=
      (Storage.context_auxiliary (Iteration.sampledContext ctx N) N).trans
        (congrArg (fun pool => pool + Storage.resultSpace N)
          (Sampler.Retained.samplerRetained_context_auxiliary ctx N))
    have bounded := observed.trans_eq storage
    exact bounded.trans (fun axis => by
      have capacity := retained_auxiliary_le N axis
      simp only [Pi.add_apply] at *
      omega)

/-- Recovery and reset scratch remain beside every surviving result and caller. -/
theorem Completion.code_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Completion.code ctx N input sameWires cells result).Path) :
    (Completion.code ctx N input sameWires cells result).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + completionAdditionalSpace N := by
  rcases path with ⟨iterationPath, recoveryPath, resetPath⟩
  refine (Circuit.peakAuxiliarySpace_seq (Iteration.code ctx N input sameWires)
    ((Completion.feedback ctx N input cells result).seq
      (reset (Iteration.context ctx N) N input
        ((Iteration.quantumWires ctx N).trans sameWires)))
      ⟨iterationPath, recoveryPath, resetPath⟩).le.trans ?_
  apply SpacePool.max_le
  · exact (Iteration.code_auxiliary_le ctx N input sameWires iterationPath).trans (fun axis => by
      simp only [completionAdditionalSpace, Pi.add_apply] at *
      omega)
  · refine (Circuit.peakAuxiliarySpace_seq (Completion.feedback ctx N input cells result)
      (reset (Iteration.context ctx N) N input
        ((Iteration.quantumWires ctx N).trans sameWires)) ⟨recoveryPath, resetPath⟩).le.trans ?_
    apply SpacePool.max_le
    · have recovered := NativeFactorScan.visit_auxiliary_le (model := executionModel input)
        input (Completion.inputs ctx N) (Completion.cells ctx N cells)
        (Completion.liftWrite ctx N result) recoveryPath
      change _ ≤ (Iteration.context ctx N).auxiliarySpace +
        FactorRecovery.NativeFactorScope.spaceBound .quantum N at recovered
      rw [Iteration.context_auxiliary] at recovered
      exact recovered.trans (fun axis => by
        have capacity := retained_auxiliary_le N axis
        change _ ≤ _
        simp only [completionAdditionalSpace, Pi.add_apply] at *
        omega)
    · have resetPeak : (reset (Iteration.context ctx N) N input
          ((Iteration.quantumWires ctx N).trans sameWires)).peakAuxiliarySpace resetPath =
            SpacePool.ofShape (.finite 2) + (Iteration.context ctx N).auxiliarySpace :=
        ZReset.BankScope.zResetBankScope_peakAuxiliarySpace
        (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
        (operations := BitWord.model)
        (shorDeclared_context_qubits N ((Iteration.quantumWires ctx N).trans sameWires))
        resetPath
      rw [resetPeak, Iteration.context_auxiliary]
      intro axis
      have capacity := retained_auxiliary_le N axis
      change _ ≤ _
      simp only [completionAdditionalSpace, Pi.add_apply] at *
      omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

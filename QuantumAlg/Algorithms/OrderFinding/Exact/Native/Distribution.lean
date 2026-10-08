/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution
import all QuantumAlg.Components.Classical.TerminalDecode.Retained.Semantics
import all QuantumAlg.Util.Classical.TerminalDecode
import all QuantumAlg.Core.Execution.MappedTail
import all QuantumAlg.Core.Execution.Retained.Distribution
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Distribution

/-!
# Actual decoded result of the native exact sample

The retained decoder reads the phase word written by the source sampler and
materializes its big-endian unsigned value through real shift and increment
instructions.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- One real retained decoding step on the source sample's store. -/
def decodedStep {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (store : Store (samplePost t width)) :=
  ClassicalRoutines.TerminalDecode.retainedStep
    (model := Sampling.Native.model access)
    (samplePost t width) t .bigEndian (sampleInput t width)
    (resultKey t width) (resultFresh t width) store

/-- Pure unsigned interpretation of the packed phase bits. -/
def decodedValue {t : Nat} : CShape.Value (.bits t) →
    CShape.Value (.unsignedWord t)
  | .bits bits =>
      .unsignedWord (ClassicalAlgorithms.TerminalDecode.fullRegisterIndex bits)

/-- The actual retained result equals the interpretation of the original stored phase bits. -/
theorem decodedStep_output {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (store : Store (samplePost t width)) :
    (decodedStep access store).1.read
        (ClassicalRoutines.TerminalDecode.resultRef
          (samplePost t width) t (resultKey t width)
          (resultFresh t width)) =
      decodedValue (store.read (sampleInput t width)) := by
  cases measured : store.read (sampleInput t width) with
  | bits bits =>
      have decoded :=
        ClassicalRoutines.TerminalDecode.terminalDecode_retainedStep_read_output
          (model := Sampling.Native.model access)
          (samplePost t width) t .bigEndian (sampleInput t width)
          (resultKey t width) (resultFresh t width) store
      rw [measured] at decoded
      cases actual : (decodedStep access store).1.read
          (ClassicalRoutines.TerminalDecode.resultRef
            (samplePost t width) t (resultKey t width)
            (resultFresh t width)) with
      | unsignedWord word =>
          change ClassicalRoutines.TerminalDecode.decodeOutput
              ((decodedStep access store).1.read
                (ClassicalRoutines.TerminalDecode.resultRef
                  (samplePost t width) t (resultKey t width)
                  (resultFresh t width))) = _ at decoded
          rw [actual] at decoded
          have same : word =
              ClassicalAlgorithms.TerminalDecode.fullRegisterIndex bits := by
            simpa [decodedStep, ClassicalRoutines.TerminalDecode.decodeOutput,
              ClassicalRoutines.TerminalDecode.decodeInput,
              ClassicalAlgorithms.TerminalDecode.fullRegisterIndex] using decoded
          simp [decodedValue, same]

/-- Append the real decoder's output store and path to a native sample record. -/
def decodedRecord {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (record : (sampleRun access).Record) : (run access).Record :=
  ((decodedStep access record.1).1,
    (record.2.1, (record.2.2.1,
      (record.2.2.2, (decodedStep access record.1).2))))

/-- The final interpreter maps the same source-sample density blocks. -/
theorem execute_eq_map {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (Reference : Register)
    (state : ExecutionState
      (Store Sampling.Native.pre × (Sampling.Native.model access).HiddenState)
      (Register.prod Sampling.Native.pre.register Reference)) :
    (run access).execute Reference state =
      ((sampleRun access).execute Reference state).mapClassical
        (decodedRecord access) := by
  refine (Circuit.execute_seq_retained_mapClassical_tail
    (model := Sampling.Native.model access)
    (resultKey t width) (.unsignedWord t) (resultFresh t width)
    (sampleCode access) (decoderCode access)
    (fun entry =>
      (((decodedStep access entry.1).1, entry.2),
        (decodedStep access entry.1).2))
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_execute
      (model := Sampling.Native.model access)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width)) Reference
    (state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
  exact congrArg (fun decision : DecidableEq (run access).Record =>
    @ExecutionState.mapClassical (sampleRun access).Record
      (run access).Record _ _
      (Register.prod (samplePost t width).register Reference) decision
      ((sampleRun access).execute Reference state)
      (decodedRecord access))
    (Subsingleton.elim _ _)

/-- The complete record PMF is the image of the genuine source-sample law. -/
theorem executionDistribution_eq_map {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model access).classicalOracles Sampling.Native.pre Reference) :
    (run access).executionDistribution input =
      ((sampleRun access).executionDistribution input).map
        (decodedRecord access) := by
  exact AlgorithmRun.RetainedRecord.executionDistribution_eq_map
    (key := resultKey t width) (shape := .unsignedWord t)
    (fresh := resultFresh t width)
    (sampleRun access) (run access) (decodedRecord access)
    (fun Reference state => execute_eq_map access Reference state) input

/-- The complete result reads the word written by the actual decoder. -/
theorem decodedRecord_result {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (record : (sampleRun access).Record) :
    (run access).result (decodedRecord access record) =
      decodedValue ((sampleRun access).result record) := by
  change (decodedStep access record.1).1.read
      (ClassicalRoutines.TerminalDecode.resultRef
        (samplePost t width) t (resultKey t width)
        (resultFresh t width)) =
      decodedValue (record.1.read (sampleInput t width))
  exact decodedStep_output access record.1

/-- The actual final word law maps the actual source sample's phase bits. -/
theorem outputDistribution_eq_decode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model access).classicalOracles Sampling.Native.pre Reference) :
    (run access).outputDistribution input =
      ((sampleRun access).outputDistribution input).map decodedValue := by
  change ((run access).executionDistribution input).map (run access).result =
    (((sampleRun access).executionDistribution input).map
      (sampleRun access).result).map decodedValue
  rw [executionDistribution_eq_map, PMF.map_comp, PMF.map_comp]
  congr 1
  funext record
  exact decodedRecord_result access record

/-- The empty-input native sample has the Born law of its actual source word. -/
theorem sample_outputDistribution_eq_source {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model access).classicalOracles Sampling.Native.pre Reference) :
    (sampleRun access).outputDistribution input =
      (OrderFinding.Native.sourceOutcomePMF access).map CShape.Value.bits := by
  exact Sampling.Native.Framed.outputDistribution_eq
    Sampling.Native.pre samplePreNoQuantum access input

/-- The complete decoded run maps the actual native source Born distribution. -/
theorem outputDistribution_eq_source {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model access).classicalOracles Sampling.Native.pre Reference) :
    (run access).outputDistribution input =
      (OrderFinding.Native.sourceOutcomePMF access).map
        (fun outcome => decodedValue (.bits outcome)) := by
  rw [outputDistribution_eq_decode access input,
    sample_outputDistribution_eq_source access input, PMF.map_comp]
  rfl

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint

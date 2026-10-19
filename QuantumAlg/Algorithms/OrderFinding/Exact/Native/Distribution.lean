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
def decodedStep (t width : Nat)
    (store : Store (samplePost t width)) :=
  ClassicalRoutines.TerminalDecode.retainedStep
    (model := Sampling.Native.model t width)
    (samplePost t width) t .bigEndian (sampleInput t width)
    (resultKey t width) (resultFresh t width) store

/-- Pure unsigned interpretation of the packed phase bits. -/
def decodedValue {t : Nat} : CShape.Value (.bits t) →
    CShape.Value (.unsignedWord t)
  | .bits bits =>
      .unsignedWord (ClassicalAlgorithms.TerminalDecode.fullRegisterIndex bits)

/-- The actual retained result equals the interpretation of the original stored phase bits. -/
lemma decodedStep_output (t width : Nat)
    (store : Store (samplePost t width)) :
    (decodedStep t width store).1.read
        (ClassicalRoutines.TerminalDecode.resultRef
          (samplePost t width) t (resultKey t width)
          (resultFresh t width)) =
      decodedValue (store.read (sampleInput t width)) := by
  cases measured : store.read (sampleInput t width) with
  | bits bits =>
      have decoded :=
        ClassicalRoutines.TerminalDecode.terminalDecode_retainedStep_read_output
          (model := Sampling.Native.model t width)
          (samplePost t width) t .bigEndian (sampleInput t width)
          (resultKey t width) (resultFresh t width) store
      rw [measured] at decoded
      cases actual : (decodedStep t width store).1.read
          (ClassicalRoutines.TerminalDecode.resultRef
            (samplePost t width) t (resultKey t width)
            (resultFresh t width)) with
      | unsignedWord word =>
          change ClassicalRoutines.TerminalDecode.decodeOutput
              ((decodedStep t width store).1.read
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
def decodedRecord (t width : Nat)
    (record : (sampleRun t width).Record) : (run t width).Record :=
  ((decodedStep t width record.1).1,
    (record.2.1, (record.2.2.1,
      (record.2.2.2, (decodedStep t width record.1).2))))

/-- The final interpreter maps the same source-sample density blocks. -/
lemma execute_eq_map (t width : Nat)
    (environment : (Sampling.Native.model t width).Environment) (Reference : Register)
    (state : ExecutionState
      (Store Sampling.Native.pre × (Sampling.Native.model t width).HiddenState)
      (Register.prod Sampling.Native.pre.register Reference)) :
    (run t width).execute environment Reference state =
      ((sampleRun t width).execute environment Reference state).mapClassical
        (decodedRecord t width) := by
  refine (Circuit.execute_seq_retained_mapClassical_tail
    (model := Sampling.Native.model t width)
    (resultKey t width) (.unsignedWord t) (resultFresh t width)
    (sampleCode t width) (decoderCode t width) environment
    (fun entry =>
      (((decodedStep t width entry.1).1, entry.2),
        (decodedStep t width entry.1).2))
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_execute
      (model := Sampling.Native.model t width) (environment := environment)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width)) Reference
    (state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
  exact congrArg (fun decision : DecidableEq (run t width).Record =>
    @ExecutionState.mapClassical (sampleRun t width).Record
      (run t width).Record _ _
      (Register.prod (samplePost t width).register Reference) decision
      ((sampleRun t width).execute environment Reference state)
      (decodedRecord t width))
    (Subsingleton.elim _ _)

/-- The complete record PMF is the image of the genuine source-sample law. -/
lemma executionDistribution_eq_map (t width : Nat)
    (environment : (Sampling.Native.model t width).Environment)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model t width).classicalOracles Sampling.Native.pre Reference) :
    (run t width).executionDistribution environment input =
      ((sampleRun t width).executionDistribution environment input).map
        (decodedRecord t width) := by
  exact AlgorithmRun.RetainedRecord.executionDistribution_eq_map
    (key := resultKey t width) (shape := .unsignedWord t)
    (fresh := resultFresh t width)
    (sampleRun t width) (run t width) environment (decodedRecord t width)
    (fun Reference state => execute_eq_map t width environment Reference state) input

/-- The complete result reads the word written by the actual decoder. -/
lemma decodedRecord_result (t width : Nat)
    (record : (sampleRun t width).Record) :
    (run t width).result (decodedRecord t width record) =
      decodedValue ((sampleRun t width).result record) := by
  change (decodedStep t width record.1).1.read
      (ClassicalRoutines.TerminalDecode.resultRef
        (samplePost t width) t (resultKey t width)
        (resultFresh t width)) =
      decodedValue (record.1.read (sampleInput t width))
  exact decodedStep_output t width record.1

/-- The actual final word law maps the actual source sample's phase bits. -/
lemma outputDistribution_eq_decode (t width : Nat)
    (environment : (Sampling.Native.model t width).Environment)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model t width).classicalOracles Sampling.Native.pre Reference) :
    (run t width).outputDistribution environment input =
      ((sampleRun t width).outputDistribution environment input).map decodedValue := by
  change ((run t width).executionDistribution environment input).map (run t width).result =
    (((sampleRun t width).executionDistribution environment input).map
      (sampleRun t width).result).map decodedValue
  rw [executionDistribution_eq_map, PMF.map_comp, PMF.map_comp]
  congr 1
  funext record
  exact decodedRecord_result t width record

/-- The empty-input native sample has the Born law of its actual source word. -/
lemma sample_outputDistribution_eq_source {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model t width).classicalOracles Sampling.Native.pre Reference) :
    (sampleRun t width).outputDistribution (Sampling.Native.environment access) input =
      (OrderFinding.Native.sourceOutcomePMF access).map CShape.Value.bits := by
  exact Sampling.Native.Framed.outputDistribution_eq
    Sampling.Native.pre samplePreNoQuantum access input

/-- The complete decoded run maps the actual native source Born distribution. -/
lemma outputDistribution_eq_source {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model t width).classicalOracles Sampling.Native.pre Reference) :
    (run t width).outputDistribution (Sampling.Native.environment access) input =
      (OrderFinding.Native.sourceOutcomePMF access).map
        (fun outcome => decodedValue (.bits outcome)) := by
  rw [outputDistribution_eq_decode t width (Sampling.Native.environment access) input,
    sample_outputDistribution_eq_source access input, PMF.map_comp]
  rfl

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint

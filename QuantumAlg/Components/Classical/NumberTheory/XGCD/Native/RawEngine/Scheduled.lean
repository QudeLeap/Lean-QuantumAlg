/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Initialization
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Output

/-!
# Actual initialized XGCD schedule and its three returned words

The original initialization, guarded loop and final copies share one actual
store-path record. Its three outputs decode to the original final state.
Internal initialization and zero premises are discharged by the enclosing
lexical allocations; no intermediate coefficient ranges are caller premises.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The three actual raw outputs decode to the corresponding original state fields. -/
def RawOutputs.MatchesState (outputs : RawOutputs ctx width) (store : Store ctx)
    (expected : PureXGCD.State) : Prop :=
  (store.read (GCD.cellRead outputs.gcd)).toNat = expected.second ∧
    decodeRawSignedWord (store.read (GCD.cellRead outputs.leftCoefficient)) =
      expected.secondLeftCoefficient ∧
    decodeRawSignedWord (store.read (GCD.cellRead outputs.rightCoefficient)) =
      expected.secondRightCoefficient

/-- Structural transport retains the original distinct destination identities. -/
theorem xgcdNativeRawOutputs_distinct_transport {outer : RuntimeCtx kind}
    (outputs : RawOutputs outer width) (transport : Transport outer ctx)
    (distinct : outputs.Distinct) : (outputs.transport transport).Distinct := by
  simpa only [RawOutputs.Distinct, RawOutputs.transport, transport.liftWrite_key] using distinct

/-- Caller agreement transfers all three decoded actual outputs across lexical boundaries. -/
theorem xgcdNativeRawOutputs_matches_transport {outer : RuntimeCtx kind}
    (outputs : RawOutputs outer width) (transport : Transport outer ctx)
    (source : Store outer) (after : Store ctx) (reads : transport.ReadsAs source after)
    (expected : PureXGCD.State) :
    (outputs.transport transport).MatchesState after expected ↔
      outputs.MatchesState source expected := by
  have gcdRead : after.read (GCD.cellRead (transport.liftWrite outputs.gcd)) =
      source.read (GCD.cellRead outputs.gcd) := reads (GCD.cellRead outputs.gcd)
  have leftRead : after.read (GCD.cellRead (transport.liftWrite outputs.leftCoefficient)) =
      source.read (GCD.cellRead outputs.leftCoefficient) :=
    reads (GCD.cellRead outputs.leftCoefficient)
  have rightRead : after.read (GCD.cellRead (transport.liftWrite outputs.rightCoefficient)) =
      source.read (GCD.cellRead outputs.rightCoefficient) :=
    reads (GCD.cellRead outputs.rightCoefficient)
  simp only [RawOutputs.MatchesState, RawOutputs.transport, gcdRead, leftRead, rightRead]

/-- The right-associated actual schedule records initialization, the loop and all final copies. -/
def scheduledRawRecord (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (loopRecord : Store ctx → Store ctx ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)).Path) :
    Store ctx → Store ctx × (scheduledRawBody cells input zero outputs).Path :=
  Circuit.sequenceRecord (initializationBody cells input zero)
    (.seq (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive cells zero)) (copyRawOutputs cells outputs))
    (fun before => (initializationStore cells input zero before,
      ((), ((), ((), ((), ((), ())))))))
    (Circuit.sequenceRecord
      (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width) (guardedActive cells zero))
      (copyRawOutputs cells outputs) loopRecord
      (fun before => (copyRawOutputsStore cells outputs before, ((), ((), ())))))

/-- One actual record supplies full execution, caller framing and the original decoded result. -/
theorem xgcdNativeScheduledRaw_actualRecord {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) (outputs : RawOutputs outer width)
    (outputsDistinct : outputs.Distinct) :
    ∃ record : Store ctx → Store ctx ×
        (scheduledRawBody cells (transport.liftInput input) (transport.liftInput zero)
          (outputs.transport transport)).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (scheduledRawBody cells (transport.liftInput input) (transport.liftInput zero)
          (outputs.transport transport)).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef outer shape),
          outputs.gcd.key ∉ other.storageKeys →
          outputs.leftCoefficient.key ∉ other.storageKeys →
          outputs.rightCoefficient.key ∉ other.storageKeys →
            ((record before).1).read (transport.liftInput other) =
              before.read (transport.liftInput other)) ∧
        (cells.Initialized before →
          (before.read (transport.liftInput zero)).toNat = 0 →
            (outputs.transport transport).MatchesState (record before).1
              (PureXGCD.finalState (GCD.decodeOperands
                (before.read (transport.liftInput input))))) := by
  obtain ⟨loopRecord, loopEquation, loopCorrect⟩ := xgcdNativeInitializedLoop_actualRecord
    cells distinct transport separated input zero
  let liftedInput := transport.liftInput input
  let liftedZero := transport.liftInput zero
  let liftedOutputs := outputs.transport transport
  let loop := Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
    (guardedActive cells liftedZero)
  let copyRecord := fun before =>
    (copyRawOutputsStore cells liftedOutputs before, ((), ((), ())))
  refine ⟨scheduledRawRecord cells liftedInput liftedZero liftedOutputs loopRecord, ?_, ?_⟩
  · intro reference history historyFinite state
    apply Circuit.execute_sequenceRecord (initializationBody cells liftedInput liftedZero)
      (.seq loop (copyRawOutputs cells liftedOutputs))
      (fun before => (initializationStore cells liftedInput liftedZero before,
        ((), ((), ((), ((), ((), ())))))))
      (Circuit.sequenceRecord loop (copyRawOutputs cells liftedOutputs) loopRecord copyRecord)
    · intro reference history historyFinite state
      refine (xgcdNativeInitialization_execute
        cells liftedInput liftedZero reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
    · intro reference history historyFinite state
      exact Circuit.execute_sequenceRecord loop (copyRawOutputs cells liftedOutputs)
        loopRecord copyRecord loopEquation (by
          intro reference history historyFinite state
          refine (xgcdNativeCopyRawOutputs_execute cells liftedOutputs reference state).trans ?_
          congr 1
          exact Subsingleton.elim _ _) reference state
  · intro before
    let intermediate := (loopRecord (initializationStore cells liftedInput liftedZero before)).1
    change (∀ {shape : CShape} (other : CInputRef outer shape),
      outputs.gcd.key ∉ other.storageKeys → outputs.leftCoefficient.key ∉ other.storageKeys →
      outputs.rightCoefficient.key ∉ other.storageKeys →
      (copyRawOutputsStore cells liftedOutputs intermediate).read (transport.liftInput other) =
        before.read (transport.liftInput other)) ∧ _
    constructor
    · intro shape other gcdFree leftFree rightFree
      exact (xgcdNativeCopyRawOutputs_read_other cells liftedOutputs intermediate
        (transport.liftInput other)
        (by simpa only [liftedOutputs, RawOutputs.transport, transport.liftWrite_key,
          transport.liftInput_storageKeys] using gcdFree)
        (by simpa only [liftedOutputs, RawOutputs.transport, transport.liftWrite_key,
          transport.liftInput_storageKeys] using leftFree)
        (by simpa only [liftedOutputs, RawOutputs.transport, transport.liftWrite_key,
          transport.liftInput_storageKeys] using rightFree)).trans ((loopCorrect before).1 other)
    · intro initialized zeroValue
      have finalState := ((loopCorrect before).2 initialized zeroValue).2
      have values := xgcdNativeRawResultStore_values cells liftedOutputs
        (xgcdNativeRawOutputs_distinct_transport outputs transport outputsDistinct) intermediate
      change liftedOutputs.MatchesState (copyRawOutputsStore cells liftedOutputs intermediate) _
      rw [xgcdNativeCopyRawOutputs_placed_store cells transport separated outputs intermediate]
      unfold RawOutputs.MatchesState
      rw [values.1, values.2.1, values.2.2]
      exact ⟨congrArg (fun state : PureXGCD.State => state.second) finalState,
        congrArg (fun state : PureXGCD.State => state.secondLeftCoefficient) finalState,
        congrArg (fun state : PureXGCD.State => state.secondRightCoefficient) finalState⟩

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

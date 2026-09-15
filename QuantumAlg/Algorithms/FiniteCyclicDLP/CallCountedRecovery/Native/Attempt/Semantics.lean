/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Power.Semantics
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Semantics

/-!
# Full-state records of the actual single recovery attempt

Actual raw recovery, all three exposure copies, the fresh declared-power scan
and the three literal tests share one chronological record. The complete
quantum-reference blocks and prior history are retained. Initialization comes
from the actual six-cell allocation and nested accumulator scope.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines.FiniteCyclicDLP

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum} {width : Nat}

private def literalRecord {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (store : Store ctx) : Store ctx × (Circuit.classical op).Path :=
  (store.applyOp op, ())

private theorem literal_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.classical op).execute Reference state = state.mapClassical (fun entry =>
      ((literalRecord op entry.1).1, (entry.2, (literalRecord op entry.1).2))) := by
  refine (Circuit.execute_classical_mapClassical op Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The two conjunctions read their actual predecessor stores in their original order. -/
def acceptanceRecord (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) :
    Store ctx → Store ctx × (acceptanceSuffix powered target refs).Path :=
  Circuit.sequenceRecord (.classical (powerEqualityOp powered target refs))
    (.seq (.classical (rawAcceptanceOp refs)) (.classical (candidateAcceptanceOp refs)))
    (literalRecord (powerEqualityOp powered target refs))
    (Circuit.sequenceRecord (.classical (rawAcceptanceOp refs))
      (.classical (candidateAcceptanceOp refs))
      (literalRecord (rawAcceptanceOp refs)) (literalRecord (candidateAcceptanceOp refs)))

/-- Every reference block follows the same real equality and both conjunction instructions. -/
theorem acceptanceSuffix_execute (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (acceptanceSuffix powered target refs).execute Reference state =
      state.mapClassical (fun entry =>
        ((acceptanceRecord powered target refs entry.1).1,
          (entry.2, (acceptanceRecord powered target refs entry.1).2))) := by
  exact Circuit.execute_sequenceRecord _ _ _ _
    (literal_execute (powerEqualityOp powered target refs))
    (Circuit.execute_sequenceRecord _ _ _ _ (literal_execute (rawAcceptanceOp refs))
      (literal_execute (candidateAcceptanceOp refs))) Reference state

/-- The complete final store contains exactly the three original chronological writes. -/
theorem acceptanceRecord_store (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (store : Store ctx) :
    (acceptanceRecord powered target refs store).1 =
      ((store.applyOp (powerEqualityOp powered target refs)).applyOp
        (rawAcceptanceOp refs)).applyOp (candidateAcceptanceOp refs) := rfl

/-- The real three writes preserve every structural read outside their actual destinations. -/
theorem acceptanceRecord_preserves_read (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape)
    (avoidEquality : refs.powerEqualsTarget.key ∉ other.storageKeys)
    (avoidRaw : refs.rawAccepted.key ∉ other.storageKeys)
    (avoidAccepted : refs.acceptedCandidate.key ∉ other.storageKeys) :
    (acceptanceRecord powered target refs store).1.read other = store.read other := by
  rw [acceptanceRecord_store]
  exact (Store.read_applyOp_of_not_mem_storageKeys _ (candidateAcceptanceOp refs) other
    avoidAccepted).trans ((Store.read_applyOp_of_not_mem_storageKeys _ (rawAcceptanceOp refs)
      other avoidRaw).trans (Store.read_applyOp_of_not_mem_storageKeys _
        (powerEqualityOp powered target refs) other avoidEquality))

/-- The complete actual raw, power and test stages have a single full-state record.

The continuation supplies its own execution equation, so this compositional
interface introduces no candidate, success or initialized-store certificate.
-/
theorem attemptBody_actualRecord (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : AttemptRefs ctx P.width)
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord P.width) →
      CInputRef inner .bit → Transport ctx inner → Circuit inner inner)
    (bodyContract : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner),
      ∃ record : Store inner → Store inner × (body candidate accepted transport).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body candidate accepted transport).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2)))) :
    ∃ record : Store ctx → Store ctx × (attemptBody P input target refs body).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (attemptBody P input target refs body).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2))) := by
  obtain ⟨rawRecord, rawEquation, _rawValues⟩ := RawRecovery.Native.singleIntoCells_actualRecord
    P.spec input refs.inverseSuccess refs.candidate refs.reconstruction
  let continued := fun {inner : RuntimeCtx .quantum}
      (powered : CInputRef inner (.unsignedWord P.width)) (transport : Transport ctx inner) =>
    let lifted := refs.lift transport
    (acceptanceSuffix powered (transport.liftInput target) lifted).seq
      (body (.storage lifted.candidate.toCStorageRef)
        (.storage lifted.acceptedCandidate.toCStorageRef) transport)
  have continuation : ∀ {inner : RuntimeCtx .quantum}
      (powered : CInputRef inner (.unsignedWord P.width)) (transport : Transport ctx inner),
      ∃ record : Store inner → Store inner × (continued powered transport).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (continued powered transport).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2))) := by
    intro inner powered transport
    let lifted := refs.lift transport
    obtain ⟨bodyRecord, bodyEquation⟩ := bodyContract
      (.storage lifted.candidate.toCStorageRef) (.storage lifted.acceptedCandidate.toCStorageRef)
      transport
    exact ⟨Circuit.sequenceRecord _ _
      (acceptanceRecord powered (transport.liftInput target) lifted) bodyRecord,
      Circuit.execute_sequenceRecord _ _ _ _
        (acceptanceSuffix_execute powered (transport.liftInput target) lifted) bodyEquation⟩
  obtain ⟨powerRecord, powerEquation⟩ := groupPowerAccumulator_actualRecord P.access P.generator
    (.storage refs.candidate.toCStorageRef) continued
    (fun powered transport => Classical.choose (continuation powered transport))
    (fun powered transport => Classical.choose_spec (continuation powered transport))
  exact ⟨Circuit.sequenceRecord _ _ rawRecord powerRecord,
    Circuit.execute_sequenceRecord _ _ _ _ rawEquation powerEquation⟩

/-- Actual allocation and release surround the same complete recovery record. -/
theorem withAttempt_actualRecord (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width))
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord P.width) →
      CInputRef inner .bit → Transport ctx inner → Circuit inner inner)
    (bodyContract : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner),
      ∃ record : Store inner → Store inner × (body candidate accepted transport).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body candidate accepted transport).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2)))) :
    ∃ record : Store ctx → Store ctx × (withAttempt P input target body).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withAttempt P input target body).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2))) := by
  obtain ⟨record, equation, _⟩ :=
    withCells_actualRecord_initialized_restricted_post ctx (attemptShapes P.width)
      (fun cells _ transport _ =>
        attemptBody P (transport.liftInput input) (transport.liftInput target) (attemptRefs cells)
          (fun candidate accepted innerTransport =>
            body candidate accepted (transport.compose innerTransport)))
      (fun _ _ => True) (by
        intro inner cells distinct transport separated
        obtain ⟨record, equation⟩ := attemptBody_actualRecord P (transport.liftInput input)
          (transport.liftInput target) (attemptRefs cells) _
          (fun candidate accepted innerTransport =>
            bodyContract candidate accepted (transport.compose innerTransport))
        exact ⟨record, equation, by intros; trivial⟩)
  exact ⟨record, equation⟩

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt.Values

/-!
# Actual initialized recovery and continuation values

The original raw output supplies the candidate range. Actual allocation then
supplies the group identity and every workspace separation condition. The
complete state equation and its store relation refer to the same record,
retaining arbitrary quantum-reference blocks and incoming history.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines.FiniteCyclicDLP

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

local instance : DecidableEq Nat := Nat.decEq

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum}

private theorem power_post (P : Parameters G)
    (candidate : CInputRef ctx (.unsignedWord P.width))
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord P.width) →
      Transport ctx inner → Circuit inner inner)
    (Post : Store ctx → Store ctx → CShape.Value (.unsignedWord P.width) → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx .quantum}
      (powered : CInputRef inner (.unsignedWord P.width)) (transport : Transport ctx inner),
      ∃ record : Store inner → Store inner × (body powered transport).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body powered transport).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
        ∀ before : Store inner,
          Post (transport.restrict before) (transport.restrict (record before).1)
            (before.read powered)) :
    ∃ record : Store ctx → Store ctx ×
        (withPowerAccumulator P.access P.generator candidate body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withPowerAccumulator P.access P.generator candidate body).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (before.read candidate).toNat < P.spec.modulus →
        Post before (record before).1
          (P.access.encode (P.generator ^ (before.read candidate).toNat)) := by
  apply withCells_actualRecord_initialized_restricted_post ctx [.unsignedWord P.width]
    (fun cells _ transport _ =>
      .seq (powerScan P.access P.generator (transport.liftInput candidate) cells.head.ref
        (Or.inl cells.head.role)) (body (powerRead cells.head.ref) transport))
    (fun before after => (before.read candidate).toNat < P.spec.modulus →
      Post before after (P.access.encode (P.generator ^ (before.read candidate).toNat)))
  intro inner cells _distinct transport separated
  obtain ⟨later, laterEquation, laterPost⟩ := bodyContract (powerRead cells.head.ref) transport
  let scan := powerScan P.access P.generator (transport.liftInput candidate)
    cells.head.ref (Or.inl cells.head.role)
  let first := powerRangeRecord P.access P.generator (P.width - 1)
    (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex P.width index))
    cells.head.ref (Or.inl cells.head.role)
  refine ⟨Circuit.sequenceRecord scan (body (powerRead cells.head.ref) transport)
    first later, ?_, ?_⟩
  · exact Circuit.execute_sequenceRecord scan (body (powerRead cells.head.ref) transport)
      first later
      (groupPowerRange_execute P.access P.generator (P.width - 1)
        (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex P.width index))
        cells.head.ref (Or.inl cells.head.role)) laterEquation
  · intro before initialized bound
    have candidateRead := transport.workspaceTransport_restrict_readsAs before candidate
    have bound' : (before.read (transport.liftInput candidate)).toNat < P.spec.modulus := by
      rw [candidateRead]
      exact bound
    have computed := groupPowerAccumulator_initialized P candidate cells transport separated
      before initialized bound'
    have following := laterPost (first before).1
    rw [computed.1, computed.2, candidateRead] at following
    exact following

private def attemptKeys {width : Nat} (refs : AttemptRefs ctx width) : List StorageKey :=
  [refs.acceptedCandidate.key, refs.rawAccepted.key, refs.powerEqualsTarget.key,
    refs.reconstruction.key, refs.candidate.key, refs.inverseSuccess.key]

private theorem attemptKeys_cells {width : Nat} (cells : Cells ctx (attemptShapes width)) :
    attemptKeys (attemptRefs cells) = cells.keys := by
  cases cells with
  | cons accepted rest =>
      cases rest with
      | cons raw rest =>
          cases rest with
          | cons equality rest =>
              cases rest with
              | cons reconstruction rest =>
                  cases rest with
                  | cons candidate rest =>
                      cases rest with
                      | cons inverse rest => cases rest; rfl

private theorem tests_post {outer : RuntimeCtx .quantum} (P : Parameters G)
    (powered target : CInputRef ctx (.unsignedWord P.width)) (refs : AttemptRefs ctx P.width)
    (transport : Transport outer ctx)
    (distinct : (attemptKeys refs).Nodup)
    (free : ∀ key ∈ attemptKeys refs, ∀ {shape : CShape} (input : CInputRef outer shape),
      key ∉ (transport.liftInput input).storageKeys)
    (Post : Store outer → Store outer → CShape.Value (.unsignedWord P.width) → Bool → Prop)
    (body : Circuit ctx ctx) (record : Store ctx → Store ctx × body.Path)
    (bodyPost : ∀ before : Store ctx,
      Post (transport.restrict before) (transport.restrict (record before).1)
        (before.read (.storage refs.candidate.toCStorageRef))
        (before.read (.storage refs.acceptedCandidate.toCStorageRef)).toBool)
    (before : Store ctx) :
    Post (transport.restrict before)
      (transport.restrict (record (acceptanceRecord powered target refs before).1).1)
      (before.read (.storage refs.candidate.toCStorageRef))
      (((before.read (.storage refs.inverseSuccess.toCStorageRef)).toBool &&
        (before.read (.storage refs.reconstruction.toCStorageRef)).toBool) &&
          decide ((before.read powered).toNat = (before.read target).toNat)) := by
  have equalityInverse : refs.powerEqualsTarget.key ≠ refs.inverseSuccess.key := by
    intro same
    simp [attemptKeys, same] at distinct
  have equalityReconstruction : refs.powerEqualsTarget.key ≠ refs.reconstruction.key := by
    intro same
    simp [attemptKeys, same] at distinct
  have rawEquality : refs.rawAccepted.key ≠ refs.powerEqualsTarget.key := by
    intro same
    simp [attemptKeys, same] at distinct
  have unchanged : transport.restrict (acceptanceRecord powered target refs before).1 =
      transport.restrict before := by
    apply transport.workspaceTransport_readsAs_restrict_iff.mp
    intro shape input
    exact (acceptanceRecord_preserves_read powered target refs before
      (transport.liftInput input) (free _ (by simp [attemptKeys]) input)
      (free _ (by simp [attemptKeys]) input) (free _ (by simp [attemptKeys]) input)).trans
        (transport.workspaceTransport_restrict_readsAs before input)
  have candidateSame := acceptanceRecord_preserves_read powered target refs before
    (.storage refs.candidate.toCStorageRef)
    (by
      simp only [CInputRef.storageKeys, List.mem_singleton]
      intro same
      simp [attemptKeys, same] at distinct)
    (by
      simp only [CInputRef.storageKeys, List.mem_singleton]
      intro same
      simp [attemptKeys, same] at distinct)
    (by
      simp only [CInputRef.storageKeys, List.mem_singleton]
      intro same
      simp [attemptKeys, same] at distinct)
  have accepted := groupAttempt_acceptanceRecord_value powered target refs before
    equalityInverse equalityReconstruction rawEquality
  have result := bodyPost (acceptanceRecord powered target refs before).1
  rw [unchanged, candidateSame, accepted, CShape.Value.toBool] at result
  exact result

private theorem raw_reads (P : Parameters G) (refs : AttemptRefs ctx P.width)
    (distinct : (attemptKeys refs).Nodup) (before : Store ctx)
    (raw : CShape.Value (.product .bit (ClassicalRoutines.FiniteCyclicDLP.OutputShape P.width))) :
    let after := RawRecovery.Native.exposureWrite refs.inverseSuccess refs.candidate
      refs.reconstruction before raw
    after.read (.storage refs.inverseSuccess.toCStorageRef) = raw.first ∧
      after.read (.storage refs.candidate.toCStorageRef) = raw.second.first ∧
      after.read (.storage refs.reconstruction.toCStorageRef) = raw.second.second := by
  have candidateInverse : refs.candidate.key ≠ refs.inverseSuccess.key := by
    intro same
    simp [attemptKeys, same] at distinct
  have reconstructionInverse : refs.reconstruction.key ≠ refs.inverseSuccess.key := by
    intro same
    simp [attemptKeys, same] at distinct
  have reconstructionCandidate : refs.reconstruction.key ≠ refs.candidate.key := by
    intro same
    simp [attemptKeys, same] at distinct
  dsimp only
  unfold RawRecovery.Native.exposureWrite
  refine ⟨?_, ?_, Store.read_write_same _ _ _⟩
  · rw [Store.read_write_other _ refs.reconstruction refs.inverseSuccess.toCStorageRef
      _ reconstructionInverse]
    rw [Store.read_write_other _ refs.candidate refs.inverseSuccess.toCStorageRef
      _ candidateInverse, Store.read_write_same]
  · rw [Store.read_write_other _ refs.reconstruction refs.candidate.toCStorageRef
      _ reconstructionCandidate, Store.read_write_same]

private theorem post_raw {outer : RuntimeCtx .quantum} (P : Parameters G)
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : AttemptRefs ctx P.width)
    (transport : Transport outer ctx) (distinct : (attemptKeys refs).Nodup)
    (free : ∀ key ∈ attemptKeys refs, ∀ {shape : CShape} (input : CInputRef outer shape),
      key ∉ (transport.liftInput input).storageKeys)
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord P.width) →
      CInputRef inner .bit → Transport outer inner → Circuit inner inner)
    (Post : Store outer → Store outer → CShape.Value (.unsignedWord P.width) → Bool → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (moved : Transport outer inner),
      (∀ key ∈ candidate.storageKeys, ∀ {shape : CShape} (input : CInputRef outer shape),
        key ∉ (moved.liftInput input).storageKeys) →
      (∀ key ∈ accepted.storageKeys, ∀ {shape : CShape} (input : CInputRef outer shape),
        key ∉ (moved.liftInput input).storageKeys) →
      ∃ record : Store inner → Store inner × (body candidate accepted moved).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body candidate accepted moved).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
        ∀ before : Store inner,
          Post (moved.restrict before) (moved.restrict (record before).1)
            (before.read candidate) (before.read accepted).toBool) :
    let continued := fun {inner : RuntimeCtx .quantum}
      (powered : CInputRef inner (.unsignedWord P.width)) (moved : Transport ctx inner) =>
        let lifted := refs.lift moved
        (acceptanceSuffix powered (moved.liftInput target) lifted).seq
          (body (.storage lifted.candidate.toCStorageRef)
            (.storage lifted.acceptedCandidate.toCStorageRef) (transport.compose moved))
    ∃ record : Store ctx → Store ctx ×
        (withPowerAccumulator P.access P.generator (.storage refs.candidate.toCStorageRef)
          continued).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withPowerAccumulator P.access P.generator (.storage refs.candidate.toCStorageRef)
          continued).execute Reference state = state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (before.read (.storage refs.candidate.toCStorageRef)).toNat < P.spec.modulus →
        Post (transport.restrict before) (transport.restrict (record before).1)
          (before.read (.storage refs.candidate.toCStorageRef))
          (((before.read (.storage refs.inverseSuccess.toCStorageRef)).toBool &&
            (before.read (.storage refs.reconstruction.toCStorageRef)).toBool) &&
              decide ((P.access.encode (P.generator ^
                (before.read (.storage refs.candidate.toCStorageRef)).toNat)).toNat =
                  (before.read target).toNat)) := by
  dsimp only
  apply power_post P (.storage refs.candidate.toCStorageRef) _
    (fun before after powered =>
      Post (transport.restrict before) (transport.restrict after)
        (before.read (.storage refs.candidate.toCStorageRef))
        (((before.read (.storage refs.inverseSuccess.toCStorageRef)).toBool &&
          (before.read (.storage refs.reconstruction.toCStorageRef)).toBool) &&
            decide (powered.toNat = (before.read target).toNat)))
  intro inner powered moved
  let lifted := refs.lift moved
  obtain ⟨later, laterEquation, laterPost⟩ := bodyContract
    (.storage lifted.candidate.toCStorageRef) (.storage lifted.acceptedCandidate.toCStorageRef)
    (transport.compose moved)
    (by
      intro key present shape input
      simp only [CInputRef.storageKeys, List.mem_singleton] at present
      subst key
      simpa only [lifted, AttemptRefs.lift, moved.liftWrite_key,
        Transport.liftInput_compose, moved.liftInput_storageKeys] using
        free refs.candidate.key (by simp [attemptKeys]) input)
    (by
      intro key present shape input
      simp only [CInputRef.storageKeys, List.mem_singleton] at present
      subst key
      simpa only [lifted, AttemptRefs.lift, moved.liftWrite_key,
        Transport.liftInput_compose, moved.liftInput_storageKeys] using
        free refs.acceptedCandidate.key (by simp [attemptKeys]) input)
  refine ⟨Circuit.sequenceRecord _ _
    (acceptanceRecord powered (moved.liftInput target) lifted) later, ?_, ?_⟩
  · exact Circuit.execute_sequenceRecord _ _ _ _
      (acceptanceSuffix_execute powered (moved.liftInput target) lifted) laterEquation
  · intro before
    have liftedDistinct : (attemptKeys lifted).Nodup := by
      simpa only [lifted, attemptKeys, AttemptRefs.lift, moved.liftWrite_key] using distinct
    have liftedFree : ∀ key ∈ attemptKeys lifted,
        ∀ {shape : CShape} (input : CInputRef outer shape),
          key ∉ ((transport.compose moved).liftInput input).storageKeys := by
      intro key present shape input
      have present' : key ∈ attemptKeys refs := by
        simpa only [lifted, attemptKeys, AttemptRefs.lift, moved.liftWrite_key] using present
      simpa only [Transport.liftInput_compose, moved.liftInput_storageKeys] using
        free key present' input
    have following := tests_post P powered (moved.liftInput target) lifted
      (transport.compose moved) liftedDistinct liftedFree Post _ later laterPost before
    simp only [Transport.workspaceTransport_restrict_compose, lifted, AttemptRefs.lift,
      ← moved.liftWrite_input] at following
    rw [moved.workspaceTransport_restrict_readsAs before
      (.storage refs.candidate.toCStorageRef),
      moved.workspaceTransport_restrict_readsAs before (.storage refs.inverseSuccess.toCStorageRef),
      moved.workspaceTransport_restrict_readsAs before (.storage refs.reconstruction.toCStorageRef),
      moved.workspaceTransport_restrict_readsAs before target] at following
    simp only [Circuit.sequenceRecord]
    convert following using 1
    congr 1

/-- Actual allocation, raw recovery and power supply the original candidate and acceptance values.

The continuation's postcondition describes that same actual code on its
actual inputs. It introduces no caller initialization, candidate correctness,
raw-success or group-equation hypothesis.
-/
theorem groupAttempt_actualRecord_correct (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width))
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord P.width) →
      CInputRef inner .bit → Transport ctx inner → Circuit inner inner)
    (Post : Store ctx → Store ctx → CShape.Value (.unsignedWord P.width) → Bool → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner),
      (∀ key ∈ candidate.storageKeys, ∀ {shape : CShape} (input : CInputRef ctx shape),
        key ∉ (transport.liftInput input).storageKeys) →
      (∀ key ∈ accepted.storageKeys, ∀ {shape : CShape} (input : CInputRef ctx shape),
        key ∉ (transport.liftInput input).storageKeys) →
      ∃ record : Store inner → Store inner × (body candidate accepted transport).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body candidate accepted transport).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
        ∀ before : Store inner,
          Post (transport.restrict before) (transport.restrict (record before).1)
            (before.read candidate) (before.read accepted).toBool) :
    ∃ record : Store ctx → Store ctx × (withAttempt P input target body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withAttempt P input target body).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        Post before (record before).1 (attemptCandidateValue P (before.read input))
          (attemptAcceptedValue P (before.read input) (before.read target)) := by
  apply withCells_actualRecord_initialized_restricted_post ctx (attemptShapes P.width)
    (fun cells _ transport _ =>
      attemptBody P (transport.liftInput input) (transport.liftInput target) (attemptRefs cells)
        (fun candidate accepted moved => body candidate accepted (transport.compose moved)))
    (fun before after => Post before after (attemptCandidateValue P (before.read input))
      (attemptAcceptedValue P (before.read input) (before.read target)))
  intro inner cells distinct transport separated
  let refs := attemptRefs cells
  have distinctRefs : (attemptKeys refs).Nodup := by
    rw [attemptKeys_cells]
    exact cells.workspaceCells_distinct_keys_nodup distinct
  have free : ∀ key ∈ attemptKeys refs,
      ∀ {shape : CShape} (observed : CInputRef ctx shape),
        key ∉ (transport.liftInput observed).storageKeys := by
    intro key present shape observed
    have actual : key ∈ cells.keys := by simpa only [refs, attemptKeys_cells] using present
    exact cells.workspaceCells_transportSeparated_avoids_of_mem transport separated actual observed
  obtain ⟨rawRecord, rawEquation, rawValues⟩ := RawRecovery.Native.singleIntoCells_actualRecord
    P.spec (transport.liftInput input) refs.inverseSuccess refs.candidate refs.reconstruction
  obtain ⟨later, laterEquation, laterPost⟩ := post_raw P (transport.liftInput target) refs
    transport distinctRefs free body Post bodyContract
  refine ⟨Circuit.sequenceRecord _ _ rawRecord later,
    Circuit.execute_sequenceRecord _ _ _ _ rawEquation laterEquation, ?_⟩
  intro before _initialized
  let raw := RawRecovery.outputCells P.spec
    (RawRecovery.Native.preparationInput (before.read (transport.liftInput input)))
  have observed :
      (rawRecord before).1.read (.storage refs.inverseSuccess.toCStorageRef) = raw.first ∧
      (rawRecord before).1.read (.storage refs.candidate.toCStorageRef) = raw.second.first ∧
      (rawRecord before).1.read (.storage refs.reconstruction.toCStorageRef) =
        raw.second.second := by
    rw [rawValues]
    exact raw_reads P refs distinctRefs before raw
  have originalReads : transport.ReadsAs (transport.restrict before) (rawRecord before).1 := by
    intro shape other
    rw [rawValues]
    exact (RawRecovery.Native.exposureWrite_read_other refs.inverseSuccess refs.candidate
      refs.reconstruction before raw (transport.liftInput other)
      (free _ (by simp [attemptKeys]) other) (free _ (by simp [attemptKeys]) other)
      (free _ (by simp [attemptKeys]) other)).trans
        (transport.workspaceTransport_restrict_readsAs before other)
  have unchanged := transport.workspaceTransport_readsAs_restrict_iff.mp originalReads
  have bound : ((rawRecord before).1.read (.storage refs.candidate.toCStorageRef)).toNat <
      P.spec.modulus := by
    rw [observed.2.1]
    exact groupAttempt_candidate_lt P (before.read (transport.liftInput input))
  have following := laterPost (rawRecord before).1 bound
  rw [unchanged, observed.1, observed.2.1, observed.2.2, originalReads target] at following
  have inputRead := transport.workspaceTransport_restrict_readsAs before input
  simp only [Circuit.sequenceRecord, attemptCandidateValue, attemptAcceptedValue, raw,
    inputRead] at following ⊢
  convert following using 1
  congr 1

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

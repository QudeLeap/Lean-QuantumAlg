/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Scheduled
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Complete actual raw XGCD execution through its original lexical scopes

The seven actual state allocations discharge initialization and internal
separation. The independent outer zero-word allocation discharges the final
zero premise. One complete state-path record returns all three original raw
results while preserving every caller read outside their destinations.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Seven real state allocations supply the initialized schedule and preserve all caller reads. -/
theorem xgcdNativeWithRawState_actualRecord
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (distinct : outputs.Distinct) :
    ∃ record : Store ctx → Store ctx × (withRawState input zero outputs).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withRawState input zero outputs).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          outputs.gcd.key ∉ other.storageKeys →
          outputs.leftCoefficient.key ∉ other.storageKeys →
          outputs.rightCoefficient.key ∉ other.storageKeys →
            ((record before).1).read other = before.read other) ∧
        ((before.read zero).toNat = 0 → outputs.MatchesState (record before).1
          (PureXGCD.finalState (GCD.decodeOperands (before.read input)))) := by
  let Post (before after : Store ctx) : Prop :=
    (∀ {shape : CShape} (other : CInputRef ctx shape),
      outputs.gcd.key ∉ other.storageKeys → outputs.leftCoefficient.key ∉ other.storageKeys →
      outputs.rightCoefficient.key ∉ other.storageKeys → after.read other = before.read other) ∧
    ((before.read zero).toNat = 0 → outputs.MatchesState after
      (PureXGCD.finalState (GCD.decodeOperands (before.read input))))
  refine withCells_actualRecord_initialized_restricted_post ctx (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody cells
      (transport.liftInput input) (transport.liftInput zero) (outputs.transport transport)) Post ?_
  intro inner cells cellsDistinct transport separated
  obtain ⟨record, equation, correct⟩ := xgcdNativeScheduledRaw_actualRecord
    cells cellsDistinct transport separated input zero outputs distinct
  refine ⟨record, equation, ?_⟩
  intro before initialized
  have entered : transport.ReadsAs (transport.restrict before) before :=
    transport.workspaceTransport_restrict_readsAs before
  have returned : transport.ReadsAs
      (transport.restrict (record before).1) (record before).1 :=
    transport.workspaceTransport_restrict_readsAs (record before).1
  constructor
  · intro shape other gcdFree leftFree rightFree
    exact (returned other).symm.trans (((correct before).1 other
      gcdFree leftFree rightFree).trans (entered other))
  · intro zeroValue
    have actual := (correct before).2 initialized (by
      rw [entered zero]
      exact zeroValue)
    have result := (xgcdNativeRawOutputs_matches_transport outputs transport
      (transport.restrict (record before).1) (record before).1 returned
      (PureXGCD.finalState (GCD.decodeOperands
        (before.read (transport.liftInput input))))).mp actual
    rw [entered input] at result
    exact result

/-- The original independent zero scope closes all internal initialization conditions. -/
theorem xgcdNativeRawEngine_actualRecord
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (distinct : outputs.Distinct) :
    ∃ record : Store ctx → Store ctx × (rawEngine input outputs).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (rawEngine input outputs).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          outputs.gcd.key ∉ other.storageKeys →
          outputs.leftCoefficient.key ∉ other.storageKeys →
          outputs.rightCoefficient.key ∉ other.storageKeys →
            ((record before).1).read other = before.read other) ∧
        outputs.MatchesState (record before).1
          (PureXGCD.finalState (GCD.decodeOperands (before.read input))) := by
  let key := ctx.canonicalFreshKey
  let shape := CShape.unsignedWord width
  let fresh := ctx.canonicalFreshKey_fresh
  let liftedInput := input.underWorkspace key shape fresh
  let zero := GCD.cellRead (CWriteRef.workspaceHead ctx key shape fresh)
  let liftedOutputs := outputs.underZero
  let body := withRawState liftedInput zero liftedOutputs
  have liftedDistinct : liftedOutputs.Distinct := distinct
  obtain ⟨bodyRecord, equation, correct⟩ :=
    xgcdNativeWithRawState_actualRecord liftedInput zero liftedOutputs liftedDistinct
  refine ⟨Circuit.workspaceRecord key shape fresh body bodyRecord, ?_, ?_⟩
  · intro reference history historyFinite state
    exact Circuit.execute_workspaceRecord key shape fresh body bodyRecord equation reference state
  · intro before
    let entered := before.pushWorkspace key shape fresh
    let final := (bodyRecord entered).1
    let returned := Store.popWorkspace key shape fresh final
    let transport := (Transport.id ctx).underWorkspace key shape fresh
    have returnedReads : transport.ReadsAs returned final :=
      ((Transport.id ctx).workspaceTransport_readsAs_underWorkspace_iff key shape fresh).mpr
        (Transport.workspaceTransport_readsAs_id returned)
    change (∀ {observed : CShape} (other : CInputRef ctx observed),
      outputs.gcd.key ∉ other.storageKeys → outputs.leftCoefficient.key ∉ other.storageKeys →
      outputs.rightCoefficient.key ∉ other.storageKeys →
        returned.read other = before.read other) ∧ _
    constructor
    · intro observed other gcdFree leftFree rightFree
      have bodyFrame := (correct entered).1 (other.underWorkspace key shape fresh)
        (by
          change outputs.gcd.key ∉ (other.underWorkspace key shape fresh).storageKeys
          simpa only [CInputRef.storageKeys_underWorkspace] using gcdFree)
        (by
          change outputs.leftCoefficient.key ∉ (other.underWorkspace key shape fresh).storageKeys
          simpa only [CInputRef.storageKeys_underWorkspace] using leftFree)
        (by
          change outputs.rightCoefficient.key ∉ (other.underWorkspace key shape fresh).storageKeys
          simpa only [CInputRef.storageKeys_underWorkspace] using rightFree)
      exact (Store.read_popWorkspace_underWorkspace key shape fresh final other).trans
        (bodyFrame.trans (Store.read_pushWorkspace_underWorkspace before key shape fresh other))
    · have zeroValue : (entered.read zero).toNat = 0 := rfl
      have actual := (correct entered).2 zeroValue
      have result := (xgcdNativeRawOutputs_matches_transport outputs transport returned final
        returnedReads
        (PureXGCD.finalState (GCD.decodeOperands (entered.read liftedInput)))).mp actual
      have inputRead : entered.read liftedInput = before.read input :=
        Store.read_pushWorkspace_underWorkspace before key shape fresh input
      rw [inputRead] at result
      exact result

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

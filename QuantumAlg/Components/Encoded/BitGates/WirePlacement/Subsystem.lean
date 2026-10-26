/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Native subsystem placement with the complete unchanged complement

An injection of actual binary wire positions determines the remaining wires
and a complete position bijection. Padding the actual body by identity and
using the existing wire-certified placement leaves that complement untouched.
No arbitrary basis isomorphism supplies a free operation, and no new wire is
allocated by this construction.
-/

namespace QuantumAlg.EncodedBit

/-- Every selected bit has a distinct actual position in the complete target frame. -/
structure WireSubsystem {Source Target : Type}
    (source : BinaryLabelEncoding Source) (target : BinaryLabelEncoding Target) where
  wires : Fin source.width ↪ Fin target.width

namespace WireSubsystem

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {Source Target : Type}
  {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
  (placement : WireSubsystem source target)

/-- Precisely the existing physical positions outside the selected subsystem. -/
def Complement := {index : Fin target.width // index ∉ Set.range placement.wires}

/-- The complement is finite because every position belongs to the existing finite frame. -/
instance complementFintype : Fintype placement.Complement := by
  classical
  unfold Complement
  infer_instance

/-- Count the actual existing complementary positions. -/
def complementWidth : Nat := Fintype.card placement.Complement

/-- Keep every unselected bit in a full binary complement word. -/
def paddedEncoding : BinaryLabelEncoding (Source × Fin (2 ^ placement.complementWidth)) :=
  .prod source (BinaryLabelEncoding.finIdentity placement.complementWidth)

/-- Complete the subsystem injection by the actual unselected physical positions. -/
def completedWires : Fin placement.paddedEncoding.width ≃ Fin target.width :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.ofInjective placement.wires placement.wires.injective)
      (Fintype.equivFin placement.Complement).symm).trans
        (Equiv.Set.sumCompl (Set.range placement.wires)))

/-- The completion retains every declared source position literally. -/
lemma completedWires_source (index : Fin source.width) :
    placement.completedWires (Fin.castAdd placement.complementWidth index) =
      placement.wires index := by
  change (Equiv.Set.sumCompl (Set.range placement.wires))
    ((Equiv.sumCongr (Equiv.ofInjective placement.wires placement.wires.injective)
      (Fintype.equivFin placement.Complement).symm)
        (finSumFinEquiv.symm (Fin.castAdd (Fintype.card placement.Complement) index))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- Every complementary coordinate names its original unselected physical position. -/
lemma completedWires_complement (index : Fin (Fintype.card placement.Complement)) :
    placement.completedWires (Fin.natAdd source.width index) =
      ((Fintype.equivFin placement.Complement).symm index).val := by
  change (Equiv.Set.sumCompl (Set.range placement.wires))
    ((Equiv.sumCongr (Equiv.ofInjective placement.wires placement.wires.injective)
      (Fintype.equivFin placement.Complement).symm)
        (finSumFinEquiv.symm (Fin.natAdd source.width index))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

private lemma paddedEncoding_surjective (onto : Function.Surjective source.encode) :
    Function.Surjective placement.paddedEncoding.encode := by
  intro label
  obtain ⟨⟨left, right⟩, rfl⟩ :=
    (prodEquiv (m := source.width) (n := placement.complementWidth)).surjective label
  obtain ⟨value, rfl⟩ := onto left
  exact ⟨(value, right), rfl⟩

/-- Full semantic coordinates are derived from the same completed physical position map. -/
def full (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) :
    FullPlacement placement.paddedEncoding target :=
  FullPlacement.ofWires placement.paddedEncoding target
    (placement.paddedEncoding_surjective sourceOnto) targetOnto placement.completedWires

/-- Source grouping reads the selected target position, without interpreting the complement. -/
lemma full_source_read (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (sourceBit : _root_.QuantumAlg.EncodedBit source)
    (targetBit : _root_.QuantumAlg.EncodedBit target)
    (same : placement.wires sourceBit.wire = targetBit.wire) (state : Target) :
    sourceBit.get ((placement.full sourceOnto targetOnto).grouping state).1 =
      targetBit.get state := by
  exact FullPlacement.ofWires_read placement.paddedEncoding target
    (placement.paddedEncoding_surjective sourceOnto) targetOnto placement.completedWires
    (BinaryLabelEncoding.prodLeftBit source
      (BinaryLabelEncoding.finIdentity placement.complementWidth) sourceBit)
    targetBit ((placement.completedWires_source sourceBit.wire).trans same) state

/-- The selected output coordinate is the original action on exactly its grouped input. -/
lemma full_step_source_read (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (sourceBit : _root_.QuantumAlg.EncodedBit source)
    (targetBit : _root_.QuantumAlg.EncodedBit target)
    (same : placement.wires sourceBit.wire = targetBit.wire)
    (action : Source → Source) (state : Target) :
    targetBit.get ((placement.full sourceOnto targetOnto).step
      (fun pair => (action pair.1, pair.2)) state) =
      sourceBit.get (action ((placement.full sourceOnto targetOnto).grouping state).1) := by
  have read := placement.full_source_read sourceOnto targetOnto sourceBit targetBit same
    ((placement.full sourceOnto targetOnto).step (fun pair => (action pair.1, pair.2)) state)
  simpa only [FullPlacement.step, Equiv.apply_symm_apply] using read.symm

/-- A coordinate outside the actual subsystem reads the unchanged complement word. -/
lemma full_complement_read (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (targetBit : _root_.QuantumAlg.EncodedBit target)
    (outside : targetBit.wire ∉ Set.range placement.wires) (state : Target) :
    (BinaryLabelEncoding.finIdentityBit placement.complementWidth
      (Fintype.equivFin placement.Complement ⟨targetBit.wire, outside⟩)).get
        ((placement.full sourceOnto targetOnto).grouping state).2 = targetBit.get state := by
  let index := Fintype.equivFin placement.Complement ⟨targetBit.wire, outside⟩
  apply FullPlacement.ofWires_read placement.paddedEncoding target
    (placement.paddedEncoding_surjective sourceOnto) targetOnto placement.completedWires
    (BinaryLabelEncoding.prodRightBit source
      (BinaryLabelEncoding.finIdentity placement.complementWidth)
      (BinaryLabelEncoding.finIdentityBit placement.complementWidth index)) targetBit
  change placement.completedWires (Fin.natAdd source.width index) = targetBit.wire
  rw [placement.completedWires_complement]
  exact congrArg Subtype.val
    ((Fintype.equivFin placement.Complement).symm_apply_apply ⟨targetBit.wire, outside⟩)

/-- An arbitrary subsystem action leaves every actual outside observable unchanged. -/
lemma full_step_other_read (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (targetBit : _root_.QuantumAlg.EncodedBit target)
    (outside : targetBit.wire ∉ Set.range placement.wires)
    (action : Source → Source) (state : Target) :
    targetBit.get ((placement.full sourceOnto targetOnto).step
      (fun pair => (action pair.1, pair.2)) state) = targetBit.get state := by
  have after := placement.full_complement_read sourceOnto targetOnto targetBit outside
    ((placement.full sourceOnto targetOnto).step (fun pair => (action pair.1, pair.2)) state)
  have before := placement.full_complement_read sourceOnto targetOnto targetBit outside state
  exact after.symm.trans (by
    simpa only [FullPlacement.step, Equiv.apply_symm_apply] using before)

variable {gates : GateModel} {oracles : OracleModel}

/-- Place the original native body, retaining all existing complementary systems. -/
def program (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source.width).toQuantum) :
    UnitaryCircuit gates oracles (QubitLayout.canonical target.width).toQuantum :=
  (placement.full sourceOnto targetOnto).place
    (UnitaryCircuit.onBinaryPrefix placement.complementWidth body)

/-- The complete complement remains correlated with the exact realized subsystem action. -/
lemma program_realizes (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    {body : UnitaryCircuit gates oracles (QubitLayout.canonical source.width).toQuantum}
    {action : Source → Source} {environment : oracles.Interpretation}
    (realizes : UnitaryCircuit.Realizes source body environment action) :
    UnitaryCircuit.Realizes target (placement.program sourceOnto targetOnto body) environment
      ((placement.full sourceOnto targetOnto).step (fun pair => (action pair.1, pair.2))) :=
  (placement.full sourceOnto targetOnto).place_realizes
    (UnitaryCircuit.Realizes.onBinaryPrefix realizes)

/-- Actual placement and identity padding preserve every native event occurrence. -/
lemma program_eventTrace (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source.width).toQuantum) :
    (placement.program sourceOnto targetOnto body).eventTrace = body.eventTrace := by
  exact ((placement.full sourceOnto targetOnto).place_eventTrace
    (UnitaryCircuit.onBinaryPrefix placement.complementWidth body)).trans
      (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventTrace _ _)

/-- Placement preserves the dependency depth under every duration assignment. -/
lemma program_evaluatedEventDepth (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source.width).toQuantum)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (placement.program sourceOnto targetOnto body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  exact ((placement.full sourceOnto targetOnto).place_evaluatedEventDepth
    (UnitaryCircuit.onBinaryPrefix placement.complementWidth body) duration).trans
      (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth _ _ _)

end

end WireSubsystem

end QuantumAlg.EncodedBit

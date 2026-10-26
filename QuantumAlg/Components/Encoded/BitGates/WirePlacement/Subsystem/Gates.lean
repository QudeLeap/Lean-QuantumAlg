/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Literal native subsystem gates with the complete complement

The selected subsystem injection determines every emitted primitive wire.
The retained complement supplies no gate and no allocation. Keeping the
native list explicit permits later controlled streaming to be compared
against exactly the same original arithmetic source instructions.
-/

namespace QuantumAlg.EncodedBit.WireSubsystem

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
  {target : BinaryLabelEncoding Target} (placement : WireSubsystem source target)

private def paddedBit (bit : EncodedBit source) : EncodedBit placement.paddedEncoding :=
  BinaryLabelEncoding.prodLeftBit source
    (BinaryLabelEncoding.finIdentity placement.complementWidth) bit

private lemma paddedBit_ne (first second : EncodedBit source)
    (different : first.wire ≠ second.wire) :
    (placement.paddedBit first).wire ≠ (placement.paddedBit second).wire := by
  intro same
  apply different
  exact Fin.ext (congrArg (fun index : Fin placement.paddedEncoding.width => index.val) same)

private def paddedGate : GateSpec source → GateSpec placement.paddedEncoding
  | .x bit => .x (placement.paddedBit bit)
  | .cnot control bit different =>
      .cnot (placement.paddedBit control) (placement.paddedBit bit)
        (placement.paddedBit_ne control bit different)
  | .toffoli first second bit distinct firstTarget secondTarget =>
      .toffoli (placement.paddedBit first) (placement.paddedBit second) (placement.paddedBit bit)
        (placement.paddedBit_ne first second distinct)
        (placement.paddedBit_ne first bit firstTarget)
        (placement.paddedBit_ne second bit secondTarget)

private lemma paddedGate_step (gate : GateSpec source)
    (state : Source × Fin (2 ^ placement.complementWidth)) :
    (placement.paddedGate gate).step state = (gate.step state.1, state.2) := by
  cases gate with
  | x bit => rfl
  | cnot control bit different =>
      change (if control.get state.1 then (bit.flip state.1, state.2) else state) = _
      cases selected : control.get state.1 <;>
        simp [GateSpec.step, cnotStep, selected]
  | toffoli first second bit distinct firstTarget secondTarget =>
      change (if first.get state.1 && second.get state.1 then
        (bit.flip state.1, state.2) else state) = _
      cases selected : first.get state.1 && second.get state.1 <;>
        simp [GateSpec.step, toffoliStep, selected]

private lemma paddedGates_step (gates : List (GateSpec source))
    (state : Source × Fin (2 ^ placement.complementWidth)) :
    GateSpec.stepList (gates.map placement.paddedGate) state =
      (GateSpec.stepList gates state.1, state.2) := by
  induction gates generalizing state with
  | nil => rfl
  | cons gate rest ih =>
      simp only [List.map_cons, GateSpec.stepList]
      rw [placement.paddedGate_step, ih]

/-- A literal source bit is located at its actual selected target position. -/
def placeBit (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) (bit : EncodedBit source) :
    EncodedBit target :=
  (placement.full sourceOnto targetOnto).placeBit (placement.paddedBit bit)

/-- The complete placement retains the originally declared subsystem wire exactly. -/
lemma placeBit_wire (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) (bit : EncodedBit source) :
    (placement.placeBit sourceOnto targetOnto bit).wire = placement.wires bit.wire := by
  change (⟨FullPlacement.wireAddress placement.paddedEncoding target placement.completedWires
      (placement.paddedBit bit).wire.val, _⟩ : Fin target.width) = _
  apply Fin.ext
  calc
    _ = (placement.completedWires (placement.paddedBit bit).wire).val :=
      dif_pos (placement.paddedBit bit).wire.isLt
    _ = _ := congrArg Fin.val (placement.completedWires_source bit.wire)

/-- The original finite primitive is emitted on its actual native subsystem wires. -/
def placeGate (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) (gate : GateSpec source) : GateSpec target :=
  (placement.full sourceOnto targetOnto).placeGate (placement.paddedGate gate)

/-- One literal native primitive has its exact subsystem action and unchanged full complement. -/
lemma placeGate_step (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) (gate : GateSpec source) (state : Target) :
    (placement.placeGate sourceOnto targetOnto gate).step state =
      (placement.full sourceOnto targetOnto).step
        (fun pair => (gate.step pair.1, pair.2)) state := by
  rw [placeGate, FullPlacement.placeGate_step]
  unfold FullPlacement.step
  rw [placement.paddedGate_step]

/-- The complete native word has the original ordered source action on the declared subsystem. -/
lemma placeGates_step (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) (gates : List (GateSpec source))
    (state : Target) :
    GateSpec.stepList (gates.map (placement.placeGate sourceOnto targetOnto)) state =
      (placement.full sourceOnto targetOnto).step
        (fun pair => (GateSpec.stepList gates pair.1, pair.2)) state := by
  have actual := (placement.full sourceOnto targetOnto).placeGates_step
    (gates.map placement.paddedGate) state
  rw [List.map_map] at actual
  change GateSpec.stepList (gates.map (placement.placeGate sourceOnto targetOnto)) state = _
    at actual
  rw [FullPlacement.step, placement.paddedGates_step] at actual
  exact actual

/-- Relocating a source instruction preserves its original native event coordinate. -/
@[simp] lemma placeGate_event (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) (oracles : OracleModel)
    (gate : GateSpec source) :
    (placement.placeGate sourceOnto targetOnto gate).event oracles = gate.event oracles := by
  rw [placeGate, FullPlacement.placeGate_event]
  cases gate <;> rfl

end

end QuantumAlg.EncodedBit.WireSubsystem

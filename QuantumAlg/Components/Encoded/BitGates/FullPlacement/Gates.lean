/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Place literal reversible gate lists on a complete frame

Each semantic bit is transported along the same full wire placement as the
program. This retains an explicit X/CNOT/Toffoli list for later native control
lowering, instead of hiding the instructions behind a semantic permutation.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
  {target : BinaryLabelEncoding Target}
variable (placement : FullPlacement source target)

private def mappedWire (index : Fin source.width) : Fin target.width :=
  ⟨placement.physicalIndex index.val, placement.wire_within index⟩

private theorem mappedWire_injective : Function.Injective placement.mappedWire := by
  intro left right same
  exact placement.wire_injective (congrArg Fin.val same)

private theorem bitIndex_rev_value {width : Nat} (index : Fin width) :
    (WireAddress.bitIndex index).val = index.rev.val := by
  rw [WireAddress.bitIndex_val, Fin.val_rev]
  omega

private theorem mappedWire_bit (label : Fin (2 ^ source.width)) (index : Fin source.width) :
    (placement.basis label).val.testBit
        (WireAddress.bitIndex (placement.mappedWire index)).val =
      label.val.testBit (WireAddress.bitIndex index).val := by
  have same := congrArg finTwoEquiv (placement.basis_position label index)
  simpa only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply,
    bitIndex_rev_value, mappedWire] using same

private theorem mappedWire_flip (wire : Fin source.width) (label : Fin (2 ^ source.width)) :
    placement.basis (WireAddress.flipBit wire label) =
      WireAddress.flipBit (placement.mappedWire wire) (placement.basis label) := by
  apply (BinaryBasis.bigEndianEquiv target.width).symm.injective
  funext targetWire
  obtain ⟨index, rfl⟩ := placement.wire_surjective targetWire
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  change (placement.basis (WireAddress.flipBit wire label)).val.testBit
      (placement.mappedWire index).rev.val =
    (WireAddress.flipBit (placement.mappedWire wire) (placement.basis label)).val.testBit
      (placement.mappedWire index).rev.val
  rw [← bitIndex_rev_value, placement.mappedWire_bit]
  by_cases same : wire = index
  · subst index
    rw [WireAddress.bit_flipBit_self, WireAddress.bit_flipBit_self, placement.mappedWire_bit]
  · rw [WireAddress.bit_flipBit_of_ne same,
      WireAddress.bit_flipBit_of_ne (fun equal => same (placement.mappedWire_injective equal)),
      placement.mappedWire_bit]

/-- The original semantic bit, read and flipped at its proved target wire. -/
def placeBit (bit : EncodedBit source) : EncodedBit target where
  wire := placement.mappedWire bit.wire
  get state := bit.get (placement.grouping state)
  flip state := placement.grouping.symm (bit.flip (placement.grouping state))
  get_eq state := by
    rw [← placement.basis_encode state, placement.mappedWire_bit, bit.get_eq]
  encode_flip state := by
    rw [← placement.basis_encode
      (placement.grouping.symm (bit.flip (placement.grouping state)))]
    rw [Equiv.apply_symm_apply, bit.encode_flip, placement.mappedWire_flip,
      placement.basis_encode]

private theorem placeBit_wire_ne {first second : EncodedBit source}
    (different : first.wire ≠ second.wire) :
    (placement.placeBit first).wire ≠ (placement.placeBit second).wire :=
  fun same => different (placement.mappedWire_injective same)

/-- Relocate the actual source primitive without changing its native gate kind. -/
def placeGate : GateSpec source → GateSpec target
  | .x bit => .x (placement.placeBit bit)
  | .cnot control bit different =>
      .cnot (placement.placeBit control) (placement.placeBit bit)
        (placement.placeBit_wire_ne different)
  | .toffoli first second bit distinct firstTarget secondTarget =>
      .toffoli (placement.placeBit first) (placement.placeBit second) (placement.placeBit bit)
        (placement.placeBit_wire_ne distinct) (placement.placeBit_wire_ne firstTarget)
        (placement.placeBit_wire_ne secondTarget)

/-- The placed primitive has the full transported basis action, including unchanged fields. -/
theorem placeGate_step (gate : GateSpec source) (state : Target) :
    (placement.placeGate gate).step state = placement.step gate.step state := by
  cases gate with
  | x bit => rfl
  | cnot control bit different =>
      by_cases selected : control.get (placement.grouping state) = true
      · simp [placeGate, GateSpec.step, cnotStep, placeBit, step, selected]
      · simp [placeGate, GateSpec.step, cnotStep, placeBit, step, selected]
  | toffoli first second bit distinct firstTarget secondTarget =>
      by_cases selected :
          (first.get (placement.grouping state) && second.get (placement.grouping state)) = true
      · simp [placeGate, GateSpec.step, toffoliStep, placeBit, step, selected]
      · simp [placeGate, GateSpec.step, toffoliStep, placeBit, step, selected]

/-- Each native event remains attached to the same original primitive. -/
@[simp] theorem placeGate_event (oracles : OracleModel) (gate : GateSpec source) :
    (placement.placeGate gate).event oracles = gate.event oracles := by
  cases gate <;> rfl

/-- Exact action of the relocated literal list in its original execution order. -/
theorem placeGates_step (gates : List (GateSpec source)) (state : Target) :
    GateSpec.stepList (gates.map placement.placeGate) state =
      placement.step (GateSpec.stepList gates) state := by
  induction gates generalizing state with
  | nil => exact (placement.grouping.symm_apply_apply state).symm
  | cons gate rest ih =>
      change GateSpec.stepList (rest.map placement.placeGate)
        ((placement.placeGate gate).step state) = _
      rw [placement.placeGate_step, ih]
      simp only [step, Equiv.apply_symm_apply, GateSpec.stepList]

/-- The emitted native program realizes precisely the original grouped action. -/
theorem placeGates_realizes (layout : QubitLayout target.width) (oracles : OracleModel)
    (gates : List (GateSpec source)) :
    UnitaryCircuit.Realizes (layout := layout) target
      (GateSpec.programList layout oracles (gates.map placement.placeGate))
      (placement.step (GateSpec.stepList gates)) :=
  GateSpec.realizesList_congrStep layout oracles _ (placement.placeGates_step gates)

/-- Explicit placement retains the complete ordered source trace. -/
theorem placeGates_eventTrace (layout : QubitLayout target.width) (oracles : OracleModel)
    (gates : List (GateSpec source)) :
    (GateSpec.programList layout oracles (gates.map placement.placeGate)).eventTrace =
      gates.map (GateSpec.event oracles) := by
  rw [GateSpec.programList_eventTrace]
  simp only [List.map_map, Function.comp_def, placeGate_event]

end

end QuantumAlg.EncodedBit.FullPlacement

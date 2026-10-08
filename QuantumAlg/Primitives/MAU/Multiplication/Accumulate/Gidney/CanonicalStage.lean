/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources

/-!
# The actual internally borrowed accumulation stage

For word width `extra + 3`, the source supplies the leading selector, the
`extra` untouched coordinates, and the two arbitrary bits required by the
modular offset. The remaining word is the target. Coherent control of the
actual offset preserves every source field exactly on both branches.
This intermediate layout contains exactly the two original words; later
placement identifies its fields with the selected source coordinates.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open Nat.FixedWidth BinaryLabelEncoding EncodedBit GateSpec

/-- Selector, untouched source coordinates, borrowed flag, target, borrowed helper. -/
abbrev CanonicalRegisters (extra : Nat) :=
  Bool × (Fin (2 ^ extra) × Addition.Gidney.Registers (extra + 3))

/-- Complete physical order of the selector, unused source bits, flag, target and helper. -/
def canonicalEncoding (extra : Nat) : BinaryLabelEncoding (CanonicalRegisters extra) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity extra)
      (Addition.Gidney.encoding (extra + 3)))

/-- The three source roles and all untouched coordinates retain their initial values. -/
def canonicalOutput {extra : Nat} (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) (state : CanonicalRegisters extra) :
    CanonicalRegisters extra :=
  (state.1, (state.2.1, (state.2.2.1,
    (if state.1 then modularWordOutput modulus constant state.2.2.2.1 else state.2.2.2.1,
      state.2.2.2.2))))

private theorem singleBit_wire (position : Fin bool.width) : boolBit.wire = position := by
  apply Fin.ext
  have bound : position.val < 1 := position.isLt
  change 0 = position.val
  omega

private def offsetBits (width : Nat) : Fin (Addition.Gidney.encoding width).width →
    EncodedBit (Addition.Gidney.encoding width) :=
  productBit (fun _ => boolBit) (Addition.Gidney.oneDirtyBits width)

private theorem offsetBits_wire (width : Nat)
    (position : Fin (Addition.Gidney.encoding width).width) :
    (offsetBits width position).wire = position := by
  exact productBit_wire (left := bool) (right := Addition.HRS.oneDirtyEncoding width)
    (fun _ => boolBit) (Addition.Gidney.oneDirtyBits width)
    singleBit_wire (Addition.Gidney.gidneyOneDirtyBits_wire width) position

private abbrev bodyEncoding (extra : Nat) :=
  prod (finIdentity extra) (Addition.Gidney.encoding (extra + 3))

private def bodyBits (extra : Nat) : Fin (bodyEncoding extra).width →
    EncodedBit (bodyEncoding extra) :=
  productBit (finIdentityBit extra) (offsetBits (extra + 3))

private theorem bodyBits_wire (extra : Nat) (position : Fin (bodyEncoding extra).width) :
    (bodyBits extra position).wire = position := by
  exact productBit_wire (left := finIdentity extra) (right := Addition.Gidney.encoding (extra + 3))
    (finIdentityBit extra) (offsetBits (extra + 3))
    (fun _ => rfl) (offsetBits_wire (extra + 3)) position

private def bodyGates (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : List (GateSpec (bodyEncoding extra)) :=
  (Addition.Gidney.modularOffsetGates (extra + 3) modulus constant).map
    (GateSpec.prodRight (finIdentity extra))

private theorem bodyCapacity (extra : Nat) : 5 ≤ bool.width + (bodyEncoding extra).width := by
  change 5 ≤ 1 + (extra + (1 + ((extra + 3) + 1)))
  omega

/-- Expand the selected modular offset into actual native gates on the existing two words. -/
def canonicalGates (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : List (GateSpec (canonicalEncoding extra)) :=
  controlRightList (fun _ => boolBit) (bodyBits extra)
    singleBit_wire (bodyBits_wire extra) (bodyCapacity extra) boolBit
    (bodyGates extra modulus constant)

/-- Both control branches restore every source field, including both arbitrary borrowed bits. -/
theorem gidneyCanonicalGates_step (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (state : CanonicalRegisters extra) :
    stepList (canonicalGates extra modulus constant) state =
      canonicalOutput modulus constant state := by
  have bodyAction : stepList (bodyGates extra modulus constant) state.2 =
      (state.2.1, Addition.Gidney.modularOffsetOutput modulus constant state.2.2) :=
    (stepList_prodRight (finIdentity extra)
      (Addition.Gidney.modularOffsetGates (extra + 3) modulus constant) state.2).trans
        (congrArg (fun output => (state.2.1, output))
          (Addition.Gidney.gidneyModularOffsetGates_step (extra + 3) modulus constant state.2.2))
  have controlled := controlRightList_step (fun _ => boolBit) (bodyBits extra)
    singleBit_wire (bodyBits_wire extra) (bodyCapacity extra) boolBit
    (bodyGates extra modulus constant) state
  rw [bodyAction] at controlled
  apply controlled.trans
  rcases state with ⟨selected, unused, flag, target, helper⟩
  cases selected <;> rfl

/-- Execute the literal default-model expansion on its fixed complete carrier. -/
def canonicalProgram (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (canonicalEncoding extra).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (canonicalGates extra modulus constant)

/-- Exact joint-basis semantics of the actual controlled native construction. -/
theorem gidneyCanonicalStage_realizes (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (canonicalEncoding extra)
      (canonicalProgram extra modulus constant) (canonicalOutput modulus constant) :=
  realizesList_congrStep _ _ _ (gidneyCanonicalGates_step extra modulus constant)

/-- The ledger consists of the gates actually emitted by the control expansion. -/
theorem gidneyCanonicalStage_eventCost (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).eventCost =
      ResourcePool.ofList ((canonicalGates extra modulus constant).map (event .empty)) :=
  programList_eventCost _ _ _

/-- Unit-duration depth counts the full literal sequence, including borrowed-wire restoration. -/
theorem gidneyCanonicalStage_depth_eq_events (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).evaluatedEventDepth (fun _ => 1) =
      (canonicalProgram extra modulus constant).eventCost.card := by
  rw [canonicalProgram, programList_evaluatedEventDepth_unit, programList_eventCost_card]

/-- Each source gate expands into at most four actual native instructions. -/
theorem gidneyCanonicalStage_event_count_bound (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).eventCost.card ≤
      4 * Addition.Gidney.modularOffsetEventBound (extra + 3) := by
  have bound := controlRightList_length_bound (fun _ => boolBit) (bodyBits extra)
    singleBit_wire (bodyBits_wire extra) (bodyCapacity extra) boolBit
    (bodyGates extra modulus constant)
  have bodyLength : (bodyGates extra modulus constant).length =
      (Addition.Gidney.modularOffsetProgram (extra + 3) modulus constant).eventCost.card := by
    rw [Addition.Gidney.modularOffsetProgram, programList_eventCost_card]
    exact List.length_map (GateSpec.prodRight (finIdentity extra))
  rw [canonicalProgram, programList_eventCost_card]
  exact bound.trans (by
    rw [bodyLength]
    exact Nat.mul_le_mul_left 4
      (Addition.Gidney.gidneyModularOffset_event_count_bound (extra + 3) modulus constant))

/-- The original two words are the complete carrier; borrowed fields allocate no additional wire. -/
theorem gidneyCanonicalStage_qubit_count (extra : Nat) :
    (canonicalEncoding extra).width = 2 * (extra + 3) := by
  change 1 + (extra + (1 + ((extra + 3) + 1))) = 2 * (extra + 3)
  omega

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.FullCoordinates
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement

/-!
# Place the actual grouped-window native program on the original frame

The complete grouped body may use both operand windows, Sign, and the
existing complementary control/work bits. Its exact field encoding is
reassembled into the original complete source frame, and every native
address follows the explicit full coordinate map. No mathematical
arithmetic permutation is declared as a gate, and the body supplies its
actual native program and its own realization proof
[LYL+26, sec_EEA/sub_regshare.tex:16-26,263-278].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowPlacement

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowEncoding ArithmeticWindowFullCoordinates

private def placement {width : Nat} (window : Window width) :
    EncodedBit.FullPlacement (groupedEncoding window) (encoding width) where
  grouping := grouping window
  basis := indexEquiv window
  basis_encode := indexEquiv_encode window
  physicalIndex := physicalIndex window
  wire_injective := physicalIndex_injective window
  wire_within := physicalIndex_within window

/-- Reassemble and physically place the existing body, retaining the full original live frame. -/
def place {width : Nat} (window : Window width)
    (body : UnitaryCircuit (Qubits (groupedEncoding window).width))
    (within : body.physical_idx ⊆ List.range (groupedEncoding window).width) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  (placement window).place body within

/-- Reassemble the actual full grouped action through the exact inverse field splitting. -/
def placedStep {width : Nat} (window : Window width)
    (action : Addition.TTK.OverflowRegisters window.length × Complement window →
      Addition.TTK.OverflowRegisters window.length × Complement window)
    (state : Registers width) : Registers width :=
  (grouping window).symm (action (grouping window state))

/-- Exact basis amplitudes of the actual body survive the original-coordinate placement. -/
theorem place_realizes {width : Nat} (window : Window width)
    {body : UnitaryCircuit (Qubits (groupedEncoding window).width)}
    {action : Addition.TTK.OverflowRegisters window.length × Complement window →
      Addition.TTK.OverflowRegisters window.length × Complement window}
    (within : body.physical_idx ⊆ List.range (groupedEncoding window).width)
    (realizes : UnitaryCircuit.Realizes (groupedEncoding window) body action) :
    UnitaryCircuit.Realizes (encoding width) (place window body within)
      (placedStep window action) :=
  (placement window).place_realizes (body := body) (action := action) within realizes

/-- The actual declared footprint is the original complete frame, with no new helper wire. -/
theorem place_physical {width : Nat} (window : Window width)
    (body : UnitaryCircuit (Qubits (groupedEncoding window).width))
    (within : body.physical_idx ⊆ List.range (groupedEncoding window).width) :
    (place window body within).physical_idx = List.range (encoding width).width :=
  (placement window).place_physical body within

/-- Every actual native event remains present and ordered after physical placement. -/
theorem place_eventTrace {width : Nat} (window : Window width)
    (body : UnitaryCircuit (Qubits (groupedEncoding window).width))
    (within : body.physical_idx ⊆ List.range (groupedEncoding window).width) :
    (place window body within).eventTrace = body.eventTrace :=
  (placement window).place_eventTrace body within

/-- Placement preserves the actual body's depth for every native duration assignment. -/
theorem place_evaluatedEventDepth {width : Nat} (window : Window width)
    (body : UnitaryCircuit (Qubits (groupedEncoding window).width))
    (within : body.physical_idx ⊆ List.range (groupedEncoding window).width)
    (duration : Resource.Event .quantum → Nat) :
    (place window body within).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration :=
  (placement window).place_evaluatedEventDepth body within duration

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowPlacement

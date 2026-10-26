/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Schedule.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Schedule.Time
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Time
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Square.Resources

/-!
# Exact native ledgers on the complete original point frame

Actual wire placement retains the whole ordered event ledger and quantum
duration of the already generated body. These proofs instantiate abstract
placement laws and the symbolic schedule ledgers; they do not expand the
256-stage Horner or MAC syntax. Both source traversals and the complete
original-word square copy and uncopy remain charged.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

noncomputable section

open QuantumAlg.EncodedBit

private lemma placed_count {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (layout : FullPlacement source target)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical source.width).toQuantum)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) (amount : Nat)
    (law : ResourcePool.count focus body.eventCost = amount) :
    ResourcePool.count focus (layout.place body).eventCost = amount := by
  have ledger : (layout.place body).eventCost = body.eventCost :=
    UnitaryCircuit.placeAt_eventCost _ _ _ _ body
  exact (congrArg (ResourcePool.count (model := .quantum AlgorithmGate.model .empty) focus)
    ledger).trans law

variable (ports : PortAssignment) (control : Control) (multiplier : Multiplier)

lemma cleanProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (cleanProgram ports control multiplier).eventCost = 18059173 :=
  placed_count (Placement.layout ports) _ _ _
    (Horner.cleanProgram_toffoli_count (Placement.savedEncoding ports)
      (quantumMultiplier ports multiplier) (outerBit ports control)
      (outer_multiplier_ne ports control multiplier))

lemma cleanProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (cleanProgram ports control multiplier).eventCost = 685693 :=
  placed_count (Placement.layout ports) _ _ _
    (Horner.cleanProgram_cnot_count (Placement.savedEncoding ports)
      (quantumMultiplier ports multiplier) (outerBit ports control)
      (outer_multiplier_ne ports control multiplier))

lemma cleanProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (cleanProgram ports control multiplier).eventCost = 129540 :=
  placed_count (Placement.layout ports) _ _ _
    (Horner.cleanProgram_x_count (Placement.savedEncoding ports)
      (quantumMultiplier ports multiplier) (outerBit ports control)
      (outer_multiplier_ne ports control multiplier))

lemma cleanProgram_quantumTime :
    (cleanProgram ports control multiplier).evaluatedEventDepth
      Resource.Event.quantumDuration = 18874406 :=
  ((Placement.layout ports).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Horner.cleanProgram_quantumTime (Placement.savedEncoding ports)
      (quantumMultiplier ports multiplier) (outerBit ports control)
      (outer_multiplier_ne ports control multiplier))

lemma macProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (macProgram ports control).eventCost = 22717258 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.program_toffoli_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

lemma macProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (macProgram ports control).eventCost = 1241338 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.program_cnot_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

lemma macProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (macProgram ports control).eventCost = 259080 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.program_x_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

lemma macProgram_quantumTime :
    (macProgram ports control).evaluatedEventDepth Resource.Event.quantumDuration = 24217676 :=
  ((Placement.layout ports).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Accumulate.program_quantumTime (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

lemma inverseMacProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (inverseMacProgram ports control).eventCost = 22717258 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.Inverse.program_toffoli_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

lemma inverseMacProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (inverseMacProgram ports control).eventCost = 1241338 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.Inverse.program_cnot_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

lemma inverseMacProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (inverseMacProgram ports control).eventCost = 259080 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.Inverse.program_x_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

lemma inverseMacProgram_quantumTime :
    (inverseMacProgram ports control).evaluatedEventDepth
      Resource.Event.quantumDuration = 24217676 :=
  ((Placement.layout ports).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Accumulate.Inverse.program_quantumTime (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

lemma subtractSquareProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (subtractSquareProgram control).eventCost = 22717258 :=
  placed_count (Placement.layout squarePorts) _ _ _
    (Accumulate.Square.program_toffoli_count (Placement.restEncoding squarePorts)
      (controlBit squarePorts control))

lemma subtractSquareProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (subtractSquareProgram control).eventCost = 1241850 :=
  placed_count (Placement.layout squarePorts) _ _ _
    (Accumulate.Square.program_cnot_count (Placement.restEncoding squarePorts)
      (controlBit squarePorts control))

lemma subtractSquareProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (subtractSquareProgram control).eventCost = 259080 :=
  placed_count (Placement.layout squarePorts) _ _ _
    (Accumulate.Square.program_x_count (Placement.restEncoding squarePorts)
      (controlBit squarePorts control))

lemma subtractSquareProgram_quantumTime :
    (subtractSquareProgram control).evaluatedEventDepth Resource.Event.quantumDuration = 24218188 :=
  ((Placement.layout squarePorts).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Accumulate.Square.program_quantumTime (Placement.restEncoding squarePorts)
      (controlBit squarePorts control))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

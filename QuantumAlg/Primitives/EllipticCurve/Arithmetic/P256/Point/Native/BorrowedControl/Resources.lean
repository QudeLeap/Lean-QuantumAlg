/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Resources

/-!
# Actual F560-selected arithmetic coordinates and quantum duration

The existing generated bodies use the same exact complete physical placement.
F560 changes only the supplied outer-control wire. Both square-copy words,
every source-restoration instruction and the original layer depth remain paid.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

namespace BorrowedControl

noncomputable section

variable (ports : PortAssignment) (multiplier : Multiplier)

lemma cleanProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (cleanProgram ports multiplier).eventCost = 18059173 :=
  placed_count (Placement.layout ports) _ _ _
    (Horner.cleanProgram_toffoli_count (Placement.savedEncoding ports)
      (quantumMultiplier ports multiplier) (outerBit ports)
      (outer_multiplier_ne ports multiplier))

lemma cleanProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (cleanProgram ports multiplier).eventCost = 685693 :=
  placed_count (Placement.layout ports) _ _ _
    (Horner.cleanProgram_cnot_count (Placement.savedEncoding ports)
      (quantumMultiplier ports multiplier) (outerBit ports)
      (outer_multiplier_ne ports multiplier))

lemma cleanProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (cleanProgram ports multiplier).eventCost = 129540 :=
  placed_count (Placement.layout ports) _ _ _
    (Horner.cleanProgram_x_count (Placement.savedEncoding ports)
      (quantumMultiplier ports multiplier) (outerBit ports)
      (outer_multiplier_ne ports multiplier))

lemma cleanProgram_quantumTime :
    (cleanProgram ports multiplier).evaluatedEventDepth
      Resource.Event.quantumDuration = 18874406 :=
  ((Placement.layout ports).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Horner.cleanProgram_quantumTime (Placement.savedEncoding ports)
      (quantumMultiplier ports multiplier) (outerBit ports)
      (outer_multiplier_ne ports multiplier))

lemma macProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (macProgram ports).eventCost = 22717258 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.program_toffoli_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports)))

lemma macProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (macProgram ports).eventCost = 1241338 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.program_cnot_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports)))

lemma macProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (macProgram ports).eventCost = 259080 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.program_x_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports)))

lemma macProgram_quantumTime :
    (macProgram ports).evaluatedEventDepth Resource.Event.quantumDuration = 24217676 :=
  ((Placement.layout ports).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Accumulate.program_quantumTime (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports)))

lemma inverseMacProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (inverseMacProgram ports).eventCost = 22717258 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.Inverse.program_toffoli_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports)))

lemma inverseMacProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (inverseMacProgram ports).eventCost = 1241338 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.Inverse.program_cnot_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports)))

lemma inverseMacProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (inverseMacProgram ports).eventCost = 259080 :=
  placed_count (Placement.layout ports) _ _ _
    (Accumulate.Inverse.program_x_count (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports)))

lemma inverseMacProgram_quantumTime :
    (inverseMacProgram ports).evaluatedEventDepth
      Resource.Event.quantumDuration = 24217676 :=
  ((Placement.layout ports).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Accumulate.Inverse.program_quantumTime (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports)))

lemma subtractSquareProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (subtractSquareProgram).eventCost = 22717258 :=
  placed_count (Placement.layout squarePorts) _ _ _
    (Accumulate.Square.program_toffoli_count (Placement.restEncoding squarePorts)
      (controlBit squarePorts))

lemma subtractSquareProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (subtractSquareProgram).eventCost = 1241850 :=
  placed_count (Placement.layout squarePorts) _ _ _
    (Accumulate.Square.program_cnot_count (Placement.restEncoding squarePorts)
      (controlBit squarePorts))

lemma subtractSquareProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (subtractSquareProgram).eventCost = 259080 :=
  placed_count (Placement.layout squarePorts) _ _ _
    (Accumulate.Square.program_x_count (Placement.restEncoding squarePorts)
      (controlBit squarePorts))

lemma subtractSquareProgram_quantumTime :
    (subtractSquareProgram).evaluatedEventDepth Resource.Event.quantumDuration = 24218188 :=
  ((Placement.layout squarePorts).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Accumulate.Square.program_quantumTime (Placement.restEncoding squarePorts)
      (controlBit squarePorts))

end

end BorrowedControl

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

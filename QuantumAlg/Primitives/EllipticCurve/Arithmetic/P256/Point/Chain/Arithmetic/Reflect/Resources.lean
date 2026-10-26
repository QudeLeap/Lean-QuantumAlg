/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Reflect.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Resources
import all QuantumAlg.Primitives.MAU.Addition.TTK.Reflection.Resources

/-!
# Actual placed retained-enable reflection ledger

The fixed public modulus supplies only a 256-bit constant mask. Every
constant load/unload, target complement and controlled TTK instruction is
charged. The same original A/X words and arbitrary borrowed W are used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic

namespace Reflect

noncomputable section

attribute [local irreducible] EncodedBit.WireSubsystem.complementWidth

lemma constant_ones : (EncodedBit.Word.constantOneIndices constant).length = 129 := by
  decide +kernel

lemma program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      program.eventCost = 3314 :=
  Native.placed_count layout _ _ _
    (MAU.Addition.TTK.Reflection.Controlled.program_toffoli_count restEncoding 256 constant
      controlBit borrowedBit control_borrowed_ne)

lemma program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      program.eventCost = 514 := by
  have actual := Native.placed_count layout _ _ _
    (MAU.Addition.TTK.Reflection.Controlled.program_cnot_count restEncoding 256 constant
      controlBit borrowedBit control_borrowed_ne)
  simpa only [program, constant_ones] using actual

lemma program_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      program.eventCost = 0 :=
  Native.placed_count layout _ _ _
    (MAU.Addition.TTK.Reflection.Controlled.program_x_count restEncoding 256 constant
      controlBit borrowedBit control_borrowed_ne)

lemma program_quantumTime :
    program.evaluatedEventDepth Resource.Event.quantumDuration = 3828 := by
  have actual := (layout.place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (MAU.Addition.TTK.Reflection.Controlled.program_quantumTime restEncoding 256 constant
      controlBit borrowedBit control_borrowed_ne)
  simpa only [program, constant_ones] using actual

end

end Reflect

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic

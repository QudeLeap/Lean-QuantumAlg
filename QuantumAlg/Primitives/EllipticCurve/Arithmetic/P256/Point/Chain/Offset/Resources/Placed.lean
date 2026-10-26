/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Resources

/-! # Exact placed ledger of the selected quantum table-word addition -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

namespace Placed

noncomputable section

/-- Physical placement keeps every native Toffoli occurrence. -/
lemma program_toffoli_count (ports : PortAssignment) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program ports).eventCost = 52346 :=
  Native.placed_count (Placement.layout ports) _ _ _
    (Offset.program_toffoli_count (Placement.savedEncoding ports) (selector ports))

/-- The selector-copy and selector-clear CNOTs are actual placed instructions. -/
lemma program_cnot_count (ports : PortAssignment) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program ports).eventCost = 510 :=
  Native.placed_count (Placement.layout ports) _ _ _
    (Offset.program_cnot_count (Placement.savedEncoding ports) (selector ports))

lemma program_x_count (ports : PortAssignment) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program ports).eventCost = 0 :=
  Native.placed_count (Placement.layout ports) _ _ _
    (Offset.program_x_count (Placement.savedEncoding ports) (selector ports))

/-- Only the physical placement changes; the actual certified dependency schedule is retained. -/
lemma program_quantumTime (ports : PortAssignment) :
    (program ports).evaluatedEventDepth Resource.Event.quantumDuration = 52856 :=
  ((Placement.layout ports).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Offset.program_quantumTime (Placement.savedEncoding ports) (selector ports))

end

end Placed

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

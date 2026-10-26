/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Coherent
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber.Path

/-!
# Exact completeness of the physical point-reset outcomes

This is the same map from a result word to its actual ordered measurement
path. Its bijectivity concerns classical retained records and introduces
no executed permutation or quantum state-space identification.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset

noncomputable section

open Execution EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2))

/-- Every real ordered outcome is named once, using its original physical measured positions. -/
lemma outcomePath_bijective (state : Window.Raw) :
    Function.Bijective fun value : Fin (2 ^ 256) =>
      outcomePath (services := services) port sameWires output value state :=
  namedResultPath_bijective (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires (Window.resultWord port)
    (Window.resultWord_distinct port) output state

/-- The actual physical outcome family has its full result-word cardinality. -/
lemma outcome_card :
    Fintype.card ((Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts (QubitLayout.canonical _) sameWires (Window.resultWord port) output)).Path) =
      2 ^ 256 :=
  resultMeasurement_card (oracles := .empty) (services := services) (QubitLayout.canonical _)
    sameWires (Window.resultWord port) output

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset

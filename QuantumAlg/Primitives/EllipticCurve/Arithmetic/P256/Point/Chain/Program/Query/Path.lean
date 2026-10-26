/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query

/-!
# Explicit paths for the same actual query measurements

The parameter projections give the literal original readout list. Transport
therefore uses equality of that list and its measurement code, without
normalizing the recursive measurement sequence or its finite path instance.
No measurement, record or physical system is added or discarded.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup Window

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

attribute [local irreducible] Circuit.measurementSequence resultReadouts

/-- Projecting the actual query parameters gives the original ordered readout list. -/
lemma queryParameters_readouts_eq (occurrence : Fin 6) :
    resultReadouts (parameters.queryParameters occurrence).physical
        (parameters.queryParameters occurrence).sameWires
        (parameters.queryParameters occurrence).frame.result
        (parameters.queryParameters occurrence).output =
      resultReadouts (QubitLayout.canonical Window.encoding.width) parameters.sameWires
        (resultWord (QueryColumns.assignment occurrence).source) parameters.output := by
  rfl

/-- The actual measurement code before choosing its path representation. -/
def queryMeasurement (occurrence : Fin 6) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  Circuit.measurementSequence
    (resultReadouts (parameters.queryParameters occurrence).physical
      (parameters.queryParameters occurrence).sameWires
      (parameters.queryParameters occurrence).frame.result
      (parameters.queryParameters occurrence).output)

/-- The two presentations are exactly the same measurement code. -/
lemma queryMeasurement_eq (occurrence : Fin 6) :
    parameters.queryMeasurement (services := services) occurrence =
      Circuit.measurementSequence
        (resultReadouts (QubitLayout.canonical Window.encoding.width) parameters.sameWires
          (resultWord (QueryColumns.assignment occurrence).source) parameters.output) := by
  exact congrArg (fun readouts => Circuit.measurementSequence
    (gates := AlgorithmGate.model) (oracles := .empty) (operations := BitWord.model)
    (classicalOracles := services) (allowAllocation := false) readouts)
      (parameters.queryParameters_readouts_eq occurrence)

/-- Path types are transported from the code equality, without inspecting any path. -/
lemma queryOutcome_type_eq (occurrence : Fin 6) :
    (parameters.queryMeasurement (services := services) occurrence).Path =
      parameters.QueryOutcome (services := services) occurrence :=
  congrArg (fun code :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false =>
      code.Path) (parameters.queryMeasurement_eq occurrence)

/-- Every actual parameter-derived outcome corresponds to one original query outcome. -/
def queryOutcomeEquiv (occurrence : Fin 6) :
    (parameters.queryMeasurement (services := services) occurrence).Path ≃
      parameters.QueryOutcome (services := services) occurrence :=
  Equiv.cast (parameters.queryOutcome_type_eq occurrence)

/-- The forward map is precisely equality transport of the original path. -/
lemma queryOutcomeEquiv_apply (occurrence : Fin 6)
    (path : (parameters.queryMeasurement (services := services) occurrence).Path) :
    parameters.queryOutcomeEquiv occurrence path =
      cast (parameters.queryOutcome_type_eq occurrence) path := rfl

/-- The inverse map uses the reverse of the same path-type equality. -/
lemma queryOutcomeEquiv_symm_apply (occurrence : Fin 6)
    (path : parameters.QueryOutcome (services := services) occurrence) :
    (parameters.queryOutcomeEquiv occurrence).symm path =
      cast (parameters.queryOutcome_type_eq occurrence).symm path := rfl

/-- Outcome transport preserves all records, including every overwrite collision. -/
lemma queryOutcomeEquiv_bijective (occurrence : Fin 6) :
    Function.Bijective (parameters.queryOutcomeEquiv (services := services) occurrence) :=
  (parameters.queryOutcomeEquiv occurrence).bijective

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument

/-!
# Literal chronological instruments of all five original point phases

Every component is the actual placed native, query or arithmetic
instrument. Sequential composition reads the literal returned Store and
retains each original record. Products below describe mathematical
outcomes only; they allocate no physical systems or classical cells.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

/-- Actual source seed followed by the two original first-difference queries. -/
def differencesInstrument :
    Execution.Instrument (parameters.differences (services := services))
      (Unit × (parameters.QueryOutcome (services := services) 0 ×
        parameters.QueryOutcome (services := services) 1)) environment :=
  (parameters.nativeFragmentInstrument environment
    (Window.suffixProgram Inversion.Seed.program)).seq
    ((parameters.queryFragmentInstrument environment 0).seq
      (parameters.queryFragmentInstrument environment 1))

/-- The real first enable, measured division and inverse enable, with no omitted path. -/
def divisionInstrument :
    Execution.Instrument (parameters.division (services := services))
      (Unit × (Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
        parameters.output × Unit)) environment :=
  (parameters.nativeFragmentInstrument environment
    (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
    ((parameters.arithmeticFragmentInstrument environment .division).seq
      (parameters.nativeFragmentInstrument environment
        (Window.Enable.inverseProgram parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)))

/-- The original second-difference query, square, genuine normal and measured multiplication. -/
def multiplicationInstrument :
    Execution.Instrument (parameters.multiplication (services := services))
      (parameters.QueryOutcome (services := services) 2 × (Unit × (Unit × (Unit ×
        (Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
          parameters.output × Unit))))) environment :=
  (parameters.queryFragmentInstrument environment 2).seq
    ((parameters.nativeFragmentInstrument environment
      (Window.Enable.program parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
      ((parameters.nativeFragmentInstrument environment
        (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram)).seq
        ((parameters.nativeFragmentInstrument environment Normal.program).seq
          ((parameters.arithmeticFragmentInstrument environment .multiplication).seq
            (parameters.nativeFragmentInstrument environment
              (Window.Enable.inverseProgram parameters.stream
                (parameters.highRemaining + parameters.lowWidth) parameters.addressBound))))))

/-- The original exceptional query precedes inverse normal and the retained-F reflection. -/
def reflectionInstrument :
    Execution.Instrument (parameters.reflection (services := services))
      (parameters.QueryOutcome (services := services) 3 × (Unit × (Unit × (Unit × Unit))))
      environment :=
  (parameters.queryFragmentInstrument environment 3).seq
    ((parameters.nativeFragmentInstrument environment
      (Window.Enable.program parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
      ((parameters.nativeFragmentInstrument environment Normal.inverseProgram).seq
        ((parameters.nativeFragmentInstrument environment
          (Window.suffixProgram Arithmetic.Reflect.program)).seq
          (parameters.nativeFragmentInstrument environment
            (Window.Enable.inverseProgram parameters.stream
              (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)))))

/-- The final two original queries and the exact adjoint of the same paid quantum seed. -/
def finishInstrument :
    Execution.Instrument (parameters.finish (services := services))
      (parameters.QueryOutcome (services := services) 4 ×
        (parameters.QueryOutcome (services := services) 5 × Unit)) environment :=
  (parameters.queryFragmentInstrument environment 4).seq
    ((parameters.queryFragmentInstrument environment 5).seq
      (parameters.nativeFragmentInstrument environment
        (Window.suffixProgram
          (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))))

/-- All actual twenty fragments compose in exactly the original five-phase program order. -/
def pointProgramInstrument :=
  (parameters.differencesInstrument environment).seq
    ((parameters.divisionInstrument environment).seq
      ((parameters.multiplicationInstrument environment).seq
        ((parameters.reflectionInstrument environment).seq
          (parameters.finishInstrument environment))))

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

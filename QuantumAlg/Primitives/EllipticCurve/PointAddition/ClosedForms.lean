/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Closed resource formulas for controlled elliptic-curve point addition

This module isolates the pure natural-number normalization of the production
resource ledger.  The raw expressions deliberately mirror the arithmetic
definitions used by the circuit modules, including the logarithmic inversion
counter.  The endpoint connects them to the actual ledger by definitional
equality, so a circuit-side formula change makes that bridge fail instead of
silently changing the published bound.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ControlledPointAddition

/-- Exact logical carrier width of one controlled affine point addition. -/
public def logicalQubitCount (fieldWidth : Nat) : Nat :=
  37 * fieldWidth + 27 + 3 * Nat.clog 2 (2 * fieldWidth)

/-- Auxiliary carrier after excluding the public control and mutable affine
point from the complete controlled-addition layout. -/
public def auxiliaryQubitCount (fieldWidth : Nat) : Nat :=
  35 * fieldWidth + 26 + 3 * Nat.clog 2 (2 * fieldWidth)

/-- The public logical carrier equals its explicit scalar formula. -/
public lemma logicalQubitCount_eq_closed (fieldWidth : Nat) :
    logicalQubitCount fieldWidth =
      37 * fieldWidth + 27 + 3 * Nat.clog 2 (2 * fieldWidth) := by
  rfl

/-- The public auxiliary carrier equals its explicit scalar formula. -/
public lemma auxiliaryQubitCount_eq_closed (fieldWidth : Nat) :
    auxiliaryQubitCount fieldWidth =
      35 * fieldWidth + 26 + 3 * Nat.clog 2 (2 * fieldWidth) := by
  rfl

/-- The complete carrier splits into the public control and affine point plus
the stated auxiliary carrier. -/
lemma logicalQubitCount_eq_public_add_auxiliary (fieldWidth : Nat) :
    logicalQubitCount fieldWidth =
      (1 + 2 * fieldWidth) + auxiliaryQubitCount fieldWidth := by
  unfold logicalQubitCount auxiliaryQubitCount
  omega

namespace ClosedForms

/-- Quadratic variable-multiplication primitive-event upper bound. -/
def variableEvent (f : Nat) : Nat :=
  230 * f ^ 2 + 119 * f

/-- Quadratic variable-multiplication CNOT upper bound. -/
def variableCnot (f : Nat) : Nat :=
  62 * f ^ 2 + 43 * f

/-- Quadratic variable-multiplication Toffoli upper bound. -/
def variableToffoli (f : Nat) : Nat :=
  168 * f ^ 2 + 14 * f

/-- Source-sized arithmetic word used by the inversion schedule. -/
def arithmeticWidth (f : Nat) : Nat := (f - 1).succ

/-- Logarithmic Kaliski padding-counter width for exactly `2f` rounds. -/
def counterWidth (f : Nat) : Nat := Nat.clog 2 (2 * f)

/-- Primitive length of one terminating inversion routing branch. -/
def terminatingRouteGateLength (tail counter : Nat) : Nat :=
  8 * (tail + 1) + 24 * counter + 5

/-- Primitive length of one active inversion routing branch. -/
def activeRouteGateLength (tail counter : Nat) : Nat :=
  2 * terminatingRouteGateLength tail counter + 370 * tail + 274

/-- Primitive length of one complete fixed-round inversion body. -/
def roundGateLength (tail counter : Nat) : Nat :=
  24 * counter + 11 + 3 * activeRouteGateLength tail counter

/-- Primitive length of the forward-and-reverse inversion round fold. -/
def foldGateLength (tail counter : Nat) : Nat :=
  2 * (tail + 1) * roundGateLength tail counter

/-- Primitive length of one unit-multiplication correction. -/
def unitMultiplicationGateLength (tail : Nat) : Nat :=
  108 * (tail + 1) ^ 2 + 105 * (tail + 1)

/-- Primitive length of one counter-controlled correction bit. -/
def counterCorrectionBitGateLength (tail : Nat) : Nat :=
  3 * unitMultiplicationGateLength tail

/-- Primitive length of the complete inversion correction computation. -/
def correctionComputeGateLength (tail counter : Nat) : Nat :=
  99 * (tail + 1) + 92 +
    counter * counterCorrectionBitGateLength tail +
      unitMultiplicationGateLength tail

/-- Primitive length of the staged target-addition cleanup. -/
def stagedTargetAddGateLength (tail : Nat) : Nat :=
  56 * (tail + 1) + 45

/-- CNOT count of one unit-multiplication correction. -/
def unitMultiplicationCnot (tail : Nat) : Nat :=
  48 * (tail + 1) ^ 2 + 43 * (tail + 1)

/-- CNOT count of the complete inversion correction computation. -/
def correctionComputeCnot (tail counter : Nat) : Nat :=
  39 * (tail + 1) + 30 + counter * (2 * (tail + 1)) +
    unitMultiplicationCnot tail

/-- CNOT count of the staged target-addition cleanup. -/
def stagedTargetAddCnot (tail : Nat) : Nat :=
  26 * (tail + 1) + 14

/-- Toffoli count of one unit-multiplication correction. -/
def unitMultiplicationToffoli (tail : Nat) : Nat :=
  60 * (tail + 1) ^ 2

/-- Toffoli count of one counter-controlled correction bit. -/
def counterCorrectionBitToffoli (tail : Nat) : Nat :=
  228 * (tail + 1) ^ 2 + 43 * (tail + 1)

/-- Toffoli count of the complete inversion correction computation. -/
def correctionComputeToffoli (tail counter : Nat) : Nat :=
  60 * (tail + 1) +
    counter * counterCorrectionBitToffoli tail +
      unitMultiplicationToffoli tail

/-- Toffoli count of the staged target-addition cleanup. -/
def stagedTargetAddToffoli (tail : Nat) : Nat :=
  30 * (tail + 1)

/-- Raw scale-removing modular-inversion primitive-event bound. -/
def inversionGateLength (f : Nat) : Nat :=
  2 * foldGateLength (f - 1) (counterWidth f) +
    2 * correctionComputeGateLength (f - 1) (counterWidth f) +
      2 * unitMultiplicationGateLength (f - 1) +
        stagedTargetAddGateLength (f - 1)

/-- Raw scale-removing modular-inversion CNOT bound. -/
def inversionCnot (f : Nat) : Nat :=
  2 * (2 * arithmeticWidth f * (4 * (f - 1) + 13)) +
    2 * correctionComputeCnot (f - 1) (counterWidth f) +
      2 * unitMultiplicationCnot (f - 1) +
        stagedTargetAddCnot (f - 1)

/-- Raw scale-removing modular-inversion Toffoli bound. -/
def inversionToffoli (f : Nat) : Nat :=
  2 * (2 * arithmeticWidth f *
    (1114 * (f - 1) + 8 * counterWidth f +
      72 * (counterWidth f - 1) + 801)) +
    2 * correctionComputeToffoli (f - 1) (counterWidth f) +
      2 * unitMultiplicationToffoli (f - 1) +
        stagedTargetAddToffoli (f - 1)

/-- Raw modular-division primitive-event bound. -/
def divisionGateLength (f : Nat) : Nat :=
  2 * inversionGateLength f + 2 * f + variableEvent f

/-- Raw clean generic-addition primitive-event bound. -/
def additionGateLength (f : Nat) : Nat :=
  76 * f + 20 + 10 * (116 * f + 15) + 6 * variableEvent f +
    2 * divisionGateLength f

/-- Raw clean generic-addition CNOT bound. -/
def additionCnot (f : Nat) : Nat :=
  76 * f + 10 * (8 * f + 1) + 6 * variableCnot f +
    2 * (2 * inversionCnot f + 2 * f + variableCnot f)

/-- Raw clean generic-addition Toffoli bound. -/
def additionToffoli (f : Nat) : Nat :=
  10 * (108 * f + 14) + 6 * variableToffoli f +
    2 * (2 * inversionToffoli f + variableToffoli f)

/-- Raw complete controlled-translation Toffoli bound. -/
def translationToffoli (f : Nat) : Nat :=
  20 * f + 6 + additionGateLength f + 3 * additionCnot f +
    11 * additionToffoli f

/-- Raw complete controlled-translation unit-depth bound. -/
def translationDepth (f : Nat) : Nat :=
  34 * f + 16 + 2 * additionGateLength f + 2 * additionCnot f +
    10 * additionToffoli f

end ClosedForms

/-- Width-only Toffoli upper bound of one controlled affine point addition. -/
public def toffoliCountBound (fieldWidth : Nat) : Nat :=
  ClosedForms.translationToffoli fieldWidth

/-- Published polynomial form of the controlled point-addition Toffoli bound. -/
public def publishedToffoliCountBound (fieldWidth : Nat) : Nat :=
  let height := Nat.clog 2 (2 * fieldWidth)
  (22656 * height + 247488) * fieldWidth ^ 2 +
    (23120 * height - 41836) * fieldWidth + 3550

/-- The published Toffoli ceiling equals its explicit scalar polynomial. -/
public lemma publishedToffoliCountBound_eq_closed (fieldWidth : Nat) :
    publishedToffoliCountBound fieldWidth =
        (22656 * Nat.clog 2 (2 * fieldWidth) + 247488) * fieldWidth ^ 2 +
          (23120 * Nat.clog 2 (2 * fieldWidth) - 41836) * fieldWidth + 3550 := by
  rfl

/-- The actual arithmetic-ledger bound normalizes to the published polynomial.
The lower bounds make every predecessor and coefficient subtraction exact. -/
lemma toffoliCountBound_eq_published (fieldWidth : Nat)
    (fieldWidthPositive : 0 < fieldWidth)
    (heightAtLeastTwo : 2 ≤ Nat.clog 2 (2 * fieldWidth)) :
    toffoliCountBound fieldWidth = publishedToffoliCountBound fieldWidth := by
  obtain ⟨fieldTail, rfl⟩ := Nat.exists_eq_add_of_le fieldWidthPositive
  generalize heightEq : Nat.clog 2 (2 * (1 + fieldTail)) = height at heightAtLeastTwo ⊢
  obtain ⟨heightTail, rfl⟩ := Nat.exists_eq_add_of_le heightAtLeastTwo
  have coefficient :
      23120 * (2 + heightTail) - 41836 = 4404 + 23120 * heightTail := by
    omega
  have heightPred : 2 + heightTail - 1 = 1 + heightTail := by
    omega
  unfold toffoliCountBound publishedToffoliCountBound
  unfold ClosedForms.translationToffoli ClosedForms.additionGateLength
    ClosedForms.additionCnot ClosedForms.additionToffoli ClosedForms.divisionGateLength
    ClosedForms.inversionGateLength ClosedForms.inversionCnot
    ClosedForms.inversionToffoli ClosedForms.foldGateLength
    ClosedForms.roundGateLength ClosedForms.activeRouteGateLength
    ClosedForms.terminatingRouteGateLength ClosedForms.correctionComputeGateLength
    ClosedForms.correctionComputeCnot ClosedForms.correctionComputeToffoli
    ClosedForms.counterCorrectionBitGateLength
    ClosedForms.counterCorrectionBitToffoli ClosedForms.unitMultiplicationGateLength
    ClosedForms.unitMultiplicationCnot ClosedForms.unitMultiplicationToffoli
    ClosedForms.stagedTargetAddGateLength ClosedForms.stagedTargetAddCnot
    ClosedForms.stagedTargetAddToffoli ClosedForms.variableEvent
    ClosedForms.variableCnot ClosedForms.variableToffoli ClosedForms.arithmeticWidth
    ClosedForms.counterWidth
  simp only [heightEq, coefficient, heightPred, Nat.add_sub_cancel_left,
    Nat.succ_eq_add_one]
  ring

/-- Width-only sequential unit-gate-depth upper bound of one controlled affine
point addition. -/
public def circuitDepthBound (fieldWidth : Nat) : Nat :=
  ClosedForms.translationDepth fieldWidth

end ControlledPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end

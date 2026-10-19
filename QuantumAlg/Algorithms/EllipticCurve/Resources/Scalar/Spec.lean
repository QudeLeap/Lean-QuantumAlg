/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Cardinality
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Cardinality

/-!
# Independent scalar allowances for arbitrary-width native ECC

These arithmetic expressions contain no circuit, multiset, execution path,
operand maximum or binary-gap table. The actual source-supported preparation
is retained; its symbolic register-width ceiling replaces fixed gap counting.
The arithmetic components retain their existing native expansion allowances.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources.Scalar

open MAU.Inversion.SharedEEA

/-- Native one-qubit and Toffoli allowance of the two-word multiplier. -/
public def multiplierSingle (width : Nat) : Nat :=
  2 * (width * MAU.Multiplication.Accumulate.Gidney.stageEventBound width)

/-- The same multiplier also charges its actual three-CNOT word exchanges. -/
public def multiplierCnot (width : Nat) : Nat := multiplierSingle width + 3 * width

/-- The serial multiplier allowance has the same independent arithmetic expression. -/
lemma multiplierTime_eq (width : Nat) :
    MAU.Multiplication.Gidney.eventBound width = multiplierCnot width := rfl

/-- Total cardinality of the independent three-coordinate multiplier allowance. -/
public def multiplierEvents (width : Nat) : Nat := 3 * multiplierSingle width + 3 * width

/-- The two controlled measured arithmetic bodies supply this one-qubit allowance. -/
public def pointSingle (width : Nat) : Nat :=
  8 + 12 * width + 4 * MAU.Multiplication.VariableGidney.eventBound width

/-- Literal surrounding controls and both measured bodies supply this CNOT allowance. -/
public def pointCnot (width : Nat) : Nat :=
  5 * MAU.Addition.Gidney.modularOffsetEventBound width +
    12 * width + 7 * MAU.Multiplication.VariableGidney.eventBound width +
    2 * MAU.Addition.Gidney.comparisonEventBound width +
    MAU.Addition.Gidney.pivotEventBound width +
    4 * ForwardResources.inPlaceBound width + 10

/-- Both measured bodies and the actual outer control expansions are included. -/
public def pointToffoli (width : Nat) : Nat :=
  36 * MAU.Addition.Gidney.modularOffsetEventBound width +
    16 * MAU.Multiplication.VariableGidney.eventBound width +
    8 * MAU.Addition.Gidney.comparisonEventBound width +
    4 * MAU.Addition.Gidney.pivotEventBound width +
    16 * ForwardResources.inPlaceBound width + 2 * width

/-- Every native coordinate of the complete measured point-addition allowance. -/
public def pointEvents (width : Nat) : Nat :=
  20 * ForwardResources.inPlaceBound width +
    27 * MAU.Multiplication.VariableGidney.eventBound width +
    41 * MAU.Addition.Gidney.modularOffsetEventBound width +
    5 * MAU.Addition.Gidney.pivotEventBound width +
    10 * MAU.Addition.Gidney.comparisonEventBound width + 28 * width + 18

/-- The measured addition retains parallel Hadamards in its serial quantum-time allowance. -/
public def pointDepth (width : Nat) : Nat :=
  20 * ForwardResources.inPlaceBound width +
    27 * MAU.Multiplication.VariableGidney.eventBound width +
    41 * MAU.Addition.Gidney.modularOffsetEventBound width +
    5 * MAU.Addition.Gidney.pivotEventBound width +
    10 * MAU.Addition.Gidney.comparisonEventBound width + 26 * width + 20

/-- The independent scalar formula is the existing measured-addition depth allowance. -/
lemma pointDepth_eq (width : Nat) :
    PrimeFieldShortWeierstrass.MeasuredPointAddition.depthBound width = pointDepth width :=
  PrimeFieldShortWeierstrass.MeasuredPointAddition.measuredPointAddition_depthBound_eq width

/-- Every physical system of the original complete terminal context is a qubit. -/
public def qubits (fieldWidth sampleWidth : Nat) : Nat :=
  3 * fieldWidth + 4 * fieldWidth.size + 12 + 2 * sampleWidth

/-- The actual streaming bank reuses one memory wire and one control wire. -/
public def streamingQubits (fieldWidth : Nat) : Nat :=
  3 * fieldWidth + 4 * fieldWidth.size + 14

/-- Every reset and converted sampling round contributes this independent quantum time. -/
public def quantumTime (fieldWidth sampleWidth count : Nat) : Nat :=
  count * (streamingQubits fieldWidth +
    (4 * multiplierCnot fieldWidth +
      2 * sampleWidth * (pointDepth fieldWidth + 2 * sampleWidth + 13)))

/-- The fixed load acts on no more than the independently sized auxiliary word. -/
public def loadBits (fieldWidth : Nat) : Nat := fieldWidth + 4 * fieldWidth.size + 11

/-- Actual auxiliary and selector zero preparations, and a width-bounded X load. -/
public def initializationEvents (fieldWidth : Nat) : Nat := 2 * loadBits fieldWidth + 1

/-- Both actual inverse QFT words' one-qubit coordinates. -/
public def readoutSingle (sampleWidth : Nat) : Nat :=
  2 * (sampleWidth + 3 * sampleWidth.choose 2)

/-- Both actual inverse QFT words' CNOT coordinates, including their real swaps. -/
public def readoutCnot (sampleWidth : Nat) : Nat :=
  2 * (2 * sampleWidth.choose 2 + 3 * (sampleWidth / 2))

/-- Complete reused quantum round, including real reset and original range preparation. -/
public def roundSingle (fieldWidth sampleWidth : Nat) : Nat :=
  qubits fieldWidth sampleWidth + 22 * sampleWidth +
    4 * multiplierSingle fieldWidth + 2 * sampleWidth * pointSingle fieldWidth +
    readoutSingle sampleWidth

/-- Complete quantum-round CNOT allowance, using the symbolic preparation ceiling. -/
public def roundCnot (fieldWidth sampleWidth : Nat) : Nat :=
  6 * sampleWidth + 4 * multiplierCnot fieldWidth +
    2 * sampleWidth * pointCnot fieldWidth + readoutCnot sampleWidth

/-- All Toffolis in the round belong to its actual arithmetic calls. -/
public def roundToffoli (fieldWidth sampleWidth : Nat) : Nat :=
  4 * multiplierSingle fieldWidth + 2 * sampleWidth * pointToffoli fieldWidth

/-- Total quantum-round allowance, including preparation and measurement occurrences. -/
public def roundEvents (fieldWidth sampleWidth : Nat) : Nat :=
  2 * qubits fieldWidth sampleWidth + 28 * sampleWidth +
    4 * multiplierEvents fieldWidth + 2 * sampleWidth * pointEvents fieldWidth +
    readoutSingle sampleWidth + readoutCnot sampleWidth + 2 * sampleWidth

/-- Checked recovery, original candidate verification and retained selection. -/
public def recoveryEvents (coordinateWidth sampleWidth : Nat) : Nat :=
  42 * sampleWidth + sampleWidth * (248 * coordinateWidth + 644) + 119

/-- Independent complete-run event-count ceiling, also bounding quantum computation time. -/
public def wholeRunEvents (fieldWidth coordinateWidth sampleWidth count : Nat) : Nat :=
  initializationEvents fieldWidth + count *
    (roundEvents fieldWidth sampleWidth + recoveryEvents coordinateWidth sampleWidth) + 1

/-- A quadratic ceiling for the original widened XGCD coefficient encoding. -/
public def coefficientBits (width : Nat) : Nat :=
  (width + 1) * (2 * (width + 1) + 1) + 3

/-- Successive classical scratch scopes reuse the larger complete workspace. -/
public def scratchBits (coordinateWidth sampleWidth : Nat) : Nat :=
  max (25 * sampleWidth + 9 * coefficientBits sampleWidth + 16)
    (27 * coordinateWidth + 9 * coefficientBits coordinateWidth + 15)

/-- Complete classical resident storage, including both borrowed public points. -/
public def residentBits (fieldWidth coordinateWidth sampleWidth : Nat) : Nat :=
  scratchBits coordinateWidth sampleWidth +
    6 * coordinateWidth + 4 * sampleWidth + fieldWidth + 7

/-- Auxiliary classical storage excludes only the borrowed public-point encodings. -/
public def auxiliaryBits (fieldWidth coordinateWidth sampleWidth : Nat) : Nat :=
  scratchBits coordinateWidth sampleWidth +
    2 * coordinateWidth + 4 * sampleWidth + fieldWidth + 5

end QuantumAlg.EllipticCurve.LogicalResources.Scalar

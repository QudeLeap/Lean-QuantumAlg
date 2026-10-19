/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Semantics
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Semantics
public import QuantumAlg.Components.Gates.SingleQubit.First.Binary
public import QuantumAlg.Components.Gates.Pauli
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Components.Gates.Pauli
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
import all QuantumAlg.Util.Classical.EllipticCurve
import all QuantumAlg.Util.EllipticCurve
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual zero-to-identity initialization of the ECDLP point bank

The infinity tag is one and both field coordinates are zero. One actual
native X instruction sets the point tag after zero allocation; every exponent
and coordinate qubit is retained. No arbitrary-state preparation is granted.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] problem Layout.pointEncoding Layout.pointWidth

private lemma zero_tensor (leftWidth rightWidth : Nat) :
    (NormalizedVector.ket (R := Qubits (leftWidth + rightWidth)) 0) =
      (NormalizedVector.ket (R := Qubits leftWidth) 0).tensor
        (NormalizedVector.ket (R := Qubits rightWidth) 0) := by
  rw [NormalizedVector.tensor_ket]
  congr 1

private lemma identity_encoding (E : PrimeFieldShortWeierstrass p) :
    (Layout.pointEncoding E).encode (1 : GroupPoint E) =
      prodEquiv (m := 1) (n := 2 * Layout.fieldWidth E) (1, 0) := by
  apply Fin.ext
  have identity : (1 : GroupPoint E).toMathlib = 0 := rfl
  have code : Layout.pointCode E (1 : GroupPoint E) =
      ClassicalAlgorithms.EllipticCurve.Code.infinity (Layout.fieldWidth E) := by
    change ClassicalAlgorithms.EllipticCurve.encode (Layout.curveSpec E)
      (1 : GroupPoint E).toMathlib = _
    rw [identity]
    rfl
  simp [Layout.pointEncoding, code, Layout.pointCodeEncoding,
    Layout.pointCodeEquiv, BinaryLabelEncoding.prod, BinaryLabelEncoding.relabel,
    BinaryLabelEncoding.bool, BinaryLabelEncoding.finIdentity, BinaryLabelEncoding.ofEquiv,
    ClassicalAlgorithms.EllipticCurve.Code.infinity,
    ClassicalAlgorithms.wordOfNat, prodEquiv, finProdFinEquiv, pow_add,
    two_mul]

/-- One native X sets the point's infinity tag and fixes its two coordinates. -/
public def pointInitializer (I : ECDLPInstance E) :
    UnitaryCircuit AlgorithmGate.model (model I)
      (QuantumSignature.qubits (Layout.pointWidth E)).canonicalPlacement.layout :=
  Gate.singleQubitAt
    (QuantumSignature.qubits (1 + 2 * Layout.fieldWidth E)).canonicalPlacement.layout
    (model I) Gate.XOp (0 : Fin (1 + 2 * Layout.fieldWidth E)) rfl

/-- Set only the existing point tag, retaining both full exponent registers. -/
public def initializer (I : ECDLPInstance E) :
    UnitaryCircuit AlgorithmGate.model (model I) (layout I) :=
  UnitaryCircuit.onBinarySuffix
    (FiniteCyclicDLP.orderWidth (problem I) + FiniteCyclicDLP.orderWidth (problem I))
    (pointInitializer I)

/-- The actual initializer produces the original encoded group identity from zero. -/
public lemma initializer_apply_zero (I : ECDLPInstance E)
    (environment : (model I).Interpretation) :
    ((initializer I).binaryMatrix environment).apply
        (NormalizedVector.ket (R := Qubits (Layout.totalQubits I)) 0) = inputState I := by
  rw [initializer, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    zero_tensor, UnitaryOperator.tensor_apply_tensor, UnitaryOperator.one_apply,
    pointInitializer, Gate.singleQubitAt_first_binaryMatrix,
    zero_tensor (1) (2 * Layout.fieldWidth E),
    UnitaryOperator.tensor_apply_tensor, UnitaryOperator.one_apply]
  have flip : Gate.XOp.apply (NormalizedVector.ket (R := Qubits 1) 0) =
      NormalizedVector.ket (R := Qubits 1) 1 := Gate.pauliXOperator_apply_ket0
  rw [flip, NormalizedVector.tensor_ket, ← identity_encoding, zero_tensor]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Circuit
public import QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Circuit
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero

/-!
# Native-dimensional Born state of the known-order experiment

This module fixes the semantic coordinates of the actual all-order circuit.
The group tail is the supplied finite group itself, rather than a binary
encoding.  Each intermediate vector is obtained from the same native word
used by execution and resource accounting.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBornBridge

noncomputable section

universe u v

local instance {α : Type v} : DecidableEq α := Classical.decEq α

variable {G : Type u} [Group G] [Fintype G]

local instance : DecidableEq G := Classical.decEq G

/-- Physical basis label named by its two binary exponent values and abstract
group value. -/
@[expose] public def fullBasis (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    (OrderOracle.layout P).Basis :=
  (OrderOracle.basisEquiv P).symm ((left, right), tail)

@[simp] public lemma basisEquiv_fullBasis (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    OrderOracle.basisEquiv P (fullBasis P left right tail) = ((left, right), tail) :=
  (OrderOracle.basisEquiv P).apply_symm_apply ((left, right), tail)

/-- Fixed zero preparation is exactly the logical `(0,0,1_G)` basis state. -/
public lemma fullBasis_zero (P : KnownOrderProblem G) :
    fullBasis P 0 0 1 = (OrderOracle.layout P).zeroLabel := by
  apply (OrderOracle.basisEquiv P).injective
  rw [basisEquiv_fullBasis, OrderOracle.basisEquiv_zero]

/-- Raw zero vector consumed by the native unitary stage. -/
public def inputVec (P : KnownOrderProblem G) :
    HilbertVector (OrderOracle.layout P).register :=
  (NormalizedVector.ket (R := (OrderOracle.layout P).register)
    (OrderOracle.layout P).zeroLabel :
    HilbertVector (OrderOracle.layout P).register)

/-- State produced by the two actual range-preparation words. -/
public def preparedVec (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    HilbertVector (OrderOracle.layout P).register :=
  ((OrderCircuit.preparations P expansion).matrix (OrderOracle.interpretation P)).applyVec (inputVec
    P)

/-- State after the sole declared `U_x` query. -/
public def postOracleVec (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    HilbertVector (OrderOracle.layout P).register :=
  ((OrderOracle.circuit AlgorithmGate.model P).matrix (OrderOracle.interpretation P)).applyVec
    (preparedVec P expansion)

/-- Normalized terminal state of the exact preparation-query-inverse-QFT word. -/
public def evolvedState (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    NormalizedVector (OrderOracle.layout P).register :=
  ((OrderCircuit.circuit P expansion).applyNormalized (OrderOracle.interpretation P))
    (NormalizedVector.ket (OrderOracle.layout P).zeroLabel)

/-- The circuit's sequential structure exposes the same stored queried vector
to the two generated inverse-QFT words. -/
public lemma circuit_applyVec_zero (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((OrderCircuit.circuit P expansion).applyVec (OrderOracle.interpretation P)) (inputVec P) =
      ((OrderCircuit.inverseQFTs P).applyVec (OrderOracle.interpretation P))
        (postOracleVec P expansion) := by
  rw [OrderCircuit.circuit, UnitaryCircuit.applyVec_seq,
    UnitaryCircuit.applyVec_seq]
  rfl

/-- Pointwise action of the sole query in semantic group coordinates. -/
public lemma oracle_applyVec_fullBasis (P : KnownOrderProblem G)
    (state : HilbertVector (OrderOracle.layout P).register)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    (OrderOracle.operator P).applyVec state (fullBasis P left right tail) =
      state (fullBasis P left right
        (tail * (P.toSourceScope.oracleMultiplier left.val right.val)⁻¹)) := by
  rw [OrderOracle.operator, UnitaryOperator.ofPerm_applyVec]
  have labelSame :
      (OrderOracle.physicalAction P).symm (fullBasis P left right tail) =
        fullBasis P left right
          (tail * (P.toSourceScope.oracleMultiplier left.val right.val)⁻¹) := by
    apply (OrderOracle.basisEquiv P).injective
    simp [fullBasis, OrderOracle.physicalAction, OrderOracle.actionEquiv]
  rw [labelSame]

/-- The stored post-query vector has the exact source-level pullback formula. -/
public lemma postOracleVec_apply (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    postOracleVec P expansion (fullBasis P left right tail) =
      preparedVec P expansion (fullBasis P left right
        (tail * (P.toSourceScope.oracleMultiplier left.val right.val)⁻¹)) := by
  rw [postOracleVec, OrderOracle.circuit_matrix]
  exact oracle_applyVec_fullBasis P (preparedVec P expansion) left right tail


private def physicalBinaryVec (P : KnownOrderProblem G)
    (state : HilbertVector (Qubits (OrderPreparation.width P))) :
    HilbertVector (OrderPreparation.layout P).register :=
  HilbertVector.reindex
    (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).symm state

private def physicalZeroVec (P : KnownOrderProblem G) :
    HilbertVector (OrderPreparation.layout P).register :=
  physicalBinaryVec P
    (NormalizedVector.ket (R := Qubits (OrderPreparation.width P)) 0)

private def physicalRangeVec (P : KnownOrderProblem G) :
    HilbertVector (OrderPreparation.layout P).register :=
  physicalBinaryVec P (OrderPreparation.state P)

private def secondPhysicalBinaryVec (P : KnownOrderProblem G)
    (state : HilbertVector (Qubits (OrderPreparation.width P))) :
    HilbertVector (OrderCircuit.secondLayout P).register :=
  HilbertVector.reindex
    (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).symm state

private def secondPhysicalZeroVec (P : KnownOrderProblem G) :
    HilbertVector (OrderCircuit.secondLayout P).register :=
  secondPhysicalBinaryVec P
    (NormalizedVector.ket (R := Qubits (OrderPreparation.width P)) 0)

private def secondPhysicalRangeVec (P : KnownOrderProblem G) :
    HilbertVector (OrderCircuit.secondLayout P).register :=
  secondPhysicalBinaryVec P (OrderPreparation.state P)

omit [Fintype G] in
@[simp] private lemma physicalRangeVec_apply (P : KnownOrderProblem G)
    (basis : (OrderPreparation.layout P).Basis) :
    physicalRangeVec P basis =
      OrderPreparation.state P
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) basis) :=
  rfl

omit [Fintype G] in
@[simp] private lemma secondPhysicalRangeVec_apply (P : KnownOrderProblem G)
    (basis : (OrderCircuit.secondLayout P).Basis) :
    secondPhysicalRangeVec P basis =
      OrderPreparation.state P
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) basis) :=
  rfl

private lemma native_apply_zero (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((OrderPreparation.Native.circuit (OrderOracle.model P) P expansion).matrix
      (OrderOracle.interpretation P)).applyVec
        (physicalZeroVec P) = physicalRangeVec P := by
  have transported := UnitaryOperator.reindex_applyVec
    (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).symm
    ((OrderPreparation.Native.circuit (OrderOracle.model P) P expansion).binaryMatrix
      (OrderOracle.interpretation P))
    (NormalizedVector.ket (R := Qubits (OrderPreparation.width P)) 0 :
      HilbertVector (Qubits (OrderPreparation.width P)))
  rw [UnitaryCircuit.binaryMatrix_eq_reindex,
    UnitaryOperator.unitaryOperator_reindex_cancel] at transported
  have binaryAction := OrderPreparation.Native.circuit_applyVec_zero
    (environment := OrderOracle.interpretation P)
    (OrderOracle.model P) P expansion
  exact (by
    simpa only [physicalZeroVec, physicalRangeVec, physicalBinaryVec,
      UnitaryCircuit.applyBinaryVec] using
        transported.trans (congrArg
          (HilbertVector.reindex
            (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).symm)
          binaryAction))


private lemma inverseQFT_apply_physicalBinaryVec (P : KnownOrderProblem G)
    (state : HilbertVector (Qubits (OrderPreparation.width P))) :
    ((QuantumFourierTransform.Native.inverseCircuit
        (OrderOracle.model P) (OrderPreparation.width P)).matrix (OrderOracle.interpretation
          P)).applyVec
        (physicalBinaryVec P state) =
      physicalBinaryVec P
        ((star (QFTOperator (OrderPreparation.width P))).applyVec state) := by
  rw [QuantumFourierTransform.Native.qftNative_inverseCircuit_physicalMatrix]
  simpa only [physicalBinaryVec] using
    (UnitaryOperator.reindex_applyVec
      (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).symm
      (star (QFTOperator (OrderPreparation.width P))) state)


private lemma inverseQFT_matrix_entry (P : KnownOrderProblem G)
    (output input : (OrderPreparation.layout P).Basis) :
    ((QuantumFourierTransform.Native.inverseCircuit
        (OrderOracle.model P) (OrderPreparation.width P)).matrix (OrderOracle.interpretation P))
          output input =
      (star (QFTOperator (OrderPreparation.width P)))
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) output)
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) input) := by
  have entry := congrArg
    (fun operator : UnitaryOperator (Qubits (OrderPreparation.width P)) =>
      operator
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) output)
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) input))
    (QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
      (OrderOracle.model P) (OrderPreparation.width P) (OrderOracle.interpretation P))
  unfold QuantumFourierTransform.Native.onBinaryLabels at entry
  simpa only [UnitaryOperator.coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply] using entry

private lemma inverseQFT_relabel_matrix_entry (P : KnownOrderProblem G)
    (output input : (OrderCircuit.secondLayout P).Basis) :
    (((QuantumFourierTransform.Native.inverseCircuit
        (OrderOracle.model P) (OrderPreparation.width P)).relabel
          (OrderCircuit.secondShift P)).matrix (OrderOracle.interpretation P)) output input =
      (star (QFTOperator (OrderPreparation.width P)))
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) output)
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) input) := by
  rw [UnitaryCircuit.relabel_matrix]
  exact inverseQFT_matrix_entry P output input


private lemma pairCircuit_matrix_entry (P : KnownOrderProblem G)
    (left : UnitaryCircuit AlgorithmGate.model (OrderOracle.model P)
      (OrderPreparation.layout P))
    (right : UnitaryCircuit AlgorithmGate.model (OrderOracle.model P)
      (OrderCircuit.secondLayout P))
    (row column : (OrderOracle.exponentLayout P).Basis) :
    ((OrderCircuit.pairCircuit P left right).matrix (OrderOracle.interpretation P)) row column =
      (left.matrix (OrderOracle.interpretation P))
          (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
            (OrderCircuit.secondLayout P) (OrderCircuit.exponentLayouts_disjoint P)
            ((OrderCircuit.pairLayout_eq_exponentLayout P).symm ▸ row)).1
          (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
            (OrderCircuit.secondLayout P) (OrderCircuit.exponentLayouts_disjoint P)
            ((OrderCircuit.pairLayout_eq_exponentLayout P).symm ▸ column)).1 *
        (right.matrix (OrderOracle.interpretation P))
          (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
            (OrderCircuit.secondLayout P) (OrderCircuit.exponentLayouts_disjoint P)
            ((OrderCircuit.pairLayout_eq_exponentLayout P).symm ▸ row)).2
          (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
            (OrderCircuit.secondLayout P) (OrderCircuit.exponentLayouts_disjoint P)
            ((OrderCircuit.pairLayout_eq_exponentLayout P).symm ▸ column)).2 := by
  rw [OrderCircuit.pairCircuit, UnitaryCircuit.castLayout_matrix_entry,
    UnitaryCircuit.tensor_native_matrix_entry]


omit [Fintype G] in
private lemma exponentBasisEquiv_split (P : KnownOrderProblem G)
    (basis : (OrderOracle.exponentLayout P).Basis) :
    OrderOracle.exponentBasisEquiv P basis =
      (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)
        (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
          (OrderCircuit.secondLayout P) (OrderCircuit.exponentLayouts_disjoint P)
          ((OrderCircuit.pairLayout_eq_exponentLayout P).symm ▸ basis)).1,
       QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)
        (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
          (OrderCircuit.secondLayout P) (OrderCircuit.exponentLayouts_disjoint P)
          ((OrderCircuit.pairLayout_eq_exponentLayout P).symm ▸ basis)).2) := by
  let same := OrderCircuit.pairLayout_eq_exponentLayout P
  let pairBasis := same.symm ▸ basis
  let split := QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
    (OrderCircuit.secondLayout P) (OrderCircuit.exponentLayouts_disjoint P) pairBasis
  let left := QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) split.1
  let right := QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) split.2
  let joinedBits : Fin (OrderPreparation.width P + OrderPreparation.width P) → Fin 2 :=
    Fin.addCases
      ((BinaryBasis.bigEndianEquiv (OrderPreparation.width P)).symm left)
      ((BinaryBasis.bigEndianEquiv (OrderPreparation.width P)).symm right)
  have transportedBasis : same ▸ pairBasis = basis :=
    UnitaryCircuit.castLayout_symm_basis same basis
  have basisBits :
      (basis : Fin (OrderPreparation.width P + OrderPreparation.width P) → Fin 2) =
        joinedBits := by
    funext index
    refine Fin.addCases (fun first => ?_) (fun second => ?_) index
    · simp only [joinedBits, Fin.addCases_left]
      apply Fin.ext
      have transported := UnitaryCircuit.castLayout_basis_value same pairBasis
        (Fin.castAdd (OrderPreparation.width P) first)
      rw [transportedBasis] at transported
      calc
        (basis (Fin.castAdd (OrderPreparation.width P) first)).val =
            (pairBasis (Fin.castAdd (OrderPreparation.width P) first)).val := transported
        _ = (split.1 first).val := by rfl
        _ = ((BinaryBasis.bigEndianEquiv (OrderPreparation.width P)).symm left first).val := by
          have decoded := congrArg (fun value => (value first).val)
            ((QuantumSignature.qubitsIndexEquiv
              (OrderPreparation.width P)).symm_apply_apply split.1)
          exact decoded.symm
    · simp only [joinedBits, Fin.addCases_right]
      apply Fin.ext
      have transported := UnitaryCircuit.castLayout_basis_value same pairBasis
        (Fin.natAdd (OrderPreparation.width P) second)
      rw [transportedBasis] at transported
      calc
        (basis (Fin.natAdd (OrderPreparation.width P) second)).val =
            (pairBasis (Fin.natAdd (OrderPreparation.width P) second)).val := transported
        _ = (split.2 second).val := by rfl
        _ = ((BinaryBasis.bigEndianEquiv (OrderPreparation.width P)).symm right second).val := by
          have decoded := congrArg (fun value => (value second).val)
            ((QuantumSignature.qubitsIndexEquiv
              (OrderPreparation.width P)).symm_apply_apply split.2)
          exact decoded.symm
  have packed :
      QuantumSignature.qubitsIndexEquiv
          (OrderPreparation.width P + OrderPreparation.width P) basis =
        prodEquiv (left, right) := by
    change BinaryBasis.bigEndianEquiv
      (OrderPreparation.width P + OrderPreparation.width P) basis = _
    calc
      _ = BinaryBasis.bigEndianEquiv
          (OrderPreparation.width P + OrderPreparation.width P)
          ((BinaryBasis.bigEndianEquiv
            (OrderPreparation.width P + OrderPreparation.width P)).symm
              (prodEquiv (left, right))) := by
            apply congrArg
            exact basisBits.trans
              (show joinedBits =
                  (BinaryBasis.bigEndianEquiv
                    (OrderPreparation.width P + OrderPreparation.width P)).symm
                      (prodEquiv (left, right)) from
                (BinaryBasis.bigEndianEquiv_symm_prod left right).symm)
      _ = prodEquiv (left, right) := Equiv.apply_symm_apply _ _
  unfold OrderOracle.exponentBasisEquiv
  simp only [Equiv.trans_apply]
  change (prodEquiv.symm
    (QuantumSignature.qubitsIndexEquiv
      (OrderPreparation.width P + OrderPreparation.width P) basis)) = (left, right)
  rw [packed, Equiv.symm_apply_apply]


private lemma pairInverseQFT_matrix_entry (P : KnownOrderProblem G)
    (row column : (OrderOracle.exponentLayout P).Basis) :
    ((OrderCircuit.pairCircuit P
      (QuantumFourierTransform.Native.inverseCircuit
        (OrderOracle.model P) (OrderPreparation.width P))
      ((QuantumFourierTransform.Native.inverseCircuit
        (OrderOracle.model P) (OrderPreparation.width P)).relabel
          (OrderCircuit.secondShift P))).matrix (OrderOracle.interpretation P)) row column =
      (star (QFTOperator (OrderPreparation.width P)))
          (OrderOracle.exponentBasisEquiv P row).1
          (OrderOracle.exponentBasisEquiv P column).1 *
        (star (QFTOperator (OrderPreparation.width P)))
          (OrderOracle.exponentBasisEquiv P row).2
          (OrderOracle.exponentBasisEquiv P column).2 := by
  rw [pairCircuit_matrix_entry, inverseQFT_matrix_entry,
    inverseQFT_relabel_matrix_entry]
  have rowSemantic := exponentBasisEquiv_split P row
  have columnSemantic := exponentBasisEquiv_split P column
  rw [rowSemantic, columnSemantic]


public lemma inverseQFTs_matrix_fullBasis (P : KnownOrderProblem G)
    (outputLeft outputRight inputLeft inputRight :
      Fin (2 ^ OrderPreparation.width P))
    (outputTail inputTail : G) :
    ((OrderCircuit.inverseQFTs P).matrix (OrderOracle.interpretation P))
        (fullBasis P outputLeft outputRight outputTail)
        (fullBasis P inputLeft inputRight inputTail) =
      @ite ℂ (outputTail = inputTail) (Classical.propDecidable _)
        ((star (QFTOperator (OrderPreparation.width P)))
            outputLeft inputLeft *
          (star (QFTOperator (OrderPreparation.width P)))
            outputRight inputRight)
        0 := by
  classical
  unfold OrderCircuit.inverseQFTs OrderCircuit.withWorkspace
  rw [UnitaryCircuit.tensor_native_matrix_entry,
    pairInverseQFT_matrix_entry, UnitaryCircuit.identity_matrix]
  have outputSemantic :=
    basisEquiv_fullBasis P outputLeft outputRight outputTail
  have inputSemantic :=
    basisEquiv_fullBasis P inputLeft inputRight inputTail
  unfold OrderOracle.basisEquiv at outputSemantic inputSemantic
  simp only [Equiv.trans_apply] at outputSemantic inputSemantic
  change
    (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).1,
      OrderOracle.workspaceBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).2) =
        ((outputLeft, outputRight), outputTail) at outputSemantic
  change
    (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).1,
      OrderOracle.workspaceBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).2) =
        ((inputLeft, inputRight), inputTail) at inputSemantic
  have outputExponent := congrArg Prod.fst outputSemantic
  have inputExponent := congrArg Prod.fst inputSemantic
  have outputWorkspace :
      OrderOracle.workspaceBasisEquiv P
          (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
            (OrderOracle.workspaceLayout P)
            (OrderOracle.exponent_workspace_disjoint P)
            (fullBasis P outputLeft outputRight outputTail)).2 = outputTail := by
    simpa only [Prod.snd] using congrArg Prod.snd outputSemantic
  have inputWorkspace :
      OrderOracle.workspaceBasisEquiv P
          (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
            (OrderOracle.workspaceLayout P)
            (OrderOracle.exponent_workspace_disjoint P)
            (fullBasis P inputLeft inputRight inputTail)).2 = inputTail := by
    simpa only [Prod.snd] using congrArg Prod.snd inputSemantic
  have outputLeftCoordinate :
      (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).1).1 = outputLeft := by
    simpa only [Prod.fst] using congrArg Prod.fst outputExponent
  have outputRightCoordinate :
      (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).1).2 = outputRight := by
    simpa only [Prod.snd] using congrArg Prod.snd outputExponent
  have inputLeftCoordinate :
      (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).1).1 = inputLeft := by
    simpa only [Prod.fst] using congrArg Prod.fst inputExponent
  have inputRightCoordinate :
      (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).1).2 = inputRight := by
    simpa only [Prod.snd] using congrArg Prod.snd inputExponent
  rw [outputLeftCoordinate, outputRightCoordinate,
    inputLeftCoordinate, inputRightCoordinate]
  have workspaceSame :
      (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).2 =
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).2 ↔
      outputTail = inputTail := by
    constructor
    · intro same
      calc
        outputTail = OrderOracle.workspaceBasisEquiv P
            (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
              (OrderOracle.workspaceLayout P)
              (OrderOracle.exponent_workspace_disjoint P)
              (fullBasis P outputLeft outputRight outputTail)).2 := outputWorkspace.symm
        _ = OrderOracle.workspaceBasisEquiv P
            (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
              (OrderOracle.workspaceLayout P)
              (OrderOracle.exponent_workspace_disjoint P)
              (fullBasis P inputLeft inputRight inputTail)).2 := congrArg _ same
        _ = inputTail := inputWorkspace
    · intro same
      apply (OrderOracle.workspaceBasisEquiv P).injective
      rw [outputWorkspace, inputWorkspace, same]
  change
    (star (QFTOperator (OrderPreparation.width P))) outputLeft inputLeft *
        (star (QFTOperator (OrderPreparation.width P))) outputRight inputRight *
          (if (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
              (OrderOracle.workspaceLayout P)
              (OrderOracle.exponent_workspace_disjoint P)
              (fullBasis P outputLeft outputRight outputTail)).2 =
            (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
              (OrderOracle.workspaceLayout P)
              (OrderOracle.exponent_workspace_disjoint P)
              (fullBasis P inputLeft inputRight inputTail)).2 then 1 else 0) =
      if outputTail = inputTail then
        (star (QFTOperator (OrderPreparation.width P))) outputLeft inputLeft *
          (star (QFTOperator (OrderPreparation.width P))) outputRight inputRight
      else 0
  rw [if_congr workspaceSame rfl rfl]
  by_cases same : outputTail = inputTail <;> simp [same]


private def pairZeroVec (P : KnownOrderProblem G) :
    HilbertVector (OrderOracle.exponentLayout P).register :=
  OrderCircuit.pairLayout_eq_exponentLayout P ▸
    UnitaryCircuit.appendVector (OrderCircuit.exponentLayouts_disjoint P)
      (physicalZeroVec P) (secondPhysicalZeroVec P)

private def pairRangeVec (P : KnownOrderProblem G) :
    HilbertVector (OrderOracle.exponentLayout P).register :=
  OrderCircuit.pairLayout_eq_exponentLayout P ▸
    UnitaryCircuit.appendVector (OrderCircuit.exponentLayouts_disjoint P)
      (physicalRangeVec P) (secondPhysicalRangeVec P)

private lemma pairCircuit_apply_zero (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((OrderCircuit.pairCircuit P
      (OrderPreparation.Native.circuit (OrderOracle.model P) P expansion)
      ((OrderPreparation.Native.circuit (OrderOracle.model P) P expansion).relabel
        (OrderCircuit.secondShift P))).matrix (OrderOracle.interpretation P)).applyVec (pairZeroVec
          P) =
      pairRangeVec P := by
  unfold OrderCircuit.pairCircuit pairZeroVec pairRangeVec
  change
    ((UnitaryCircuit.castLayout (OrderCircuit.pairLayout_eq_exponentLayout P)
      (UnitaryCircuit.tensor
        (OrderPreparation.Native.circuit (OrderOracle.model P) P expansion)
        ((OrderPreparation.Native.circuit (OrderOracle.model P) P expansion).relabel
          (OrderCircuit.secondShift P))
        (OrderCircuit.exponentLayouts_disjoint P))).applyVec (OrderOracle.interpretation P))
      (OrderCircuit.pairLayout_eq_exponentLayout P ▸
        UnitaryCircuit.appendVector (OrderCircuit.exponentLayouts_disjoint P)
          (physicalZeroVec P) (secondPhysicalZeroVec P)) = _
  let same := OrderCircuit.pairLayout_eq_exponentLayout P
  have tensorAction :
      ((UnitaryCircuit.tensor
        (OrderPreparation.Native.circuit (OrderOracle.model P) P expansion)
        ((OrderPreparation.Native.circuit (OrderOracle.model P) P expansion).relabel
          (OrderCircuit.secondShift P))
        (OrderCircuit.exponentLayouts_disjoint P)).matrix (OrderOracle.interpretation P)).applyVec
          (UnitaryCircuit.appendVector (OrderCircuit.exponentLayouts_disjoint P)
            (physicalZeroVec P) (secondPhysicalZeroVec P)) =
        UnitaryCircuit.appendVector (OrderCircuit.exponentLayouts_disjoint P)
          (physicalRangeVec P) (secondPhysicalRangeVec P) := by
    have rightAction :
        (((OrderPreparation.Native.circuit (OrderOracle.model P) P expansion).relabel
          (OrderCircuit.secondShift P)).matrix (OrderOracle.interpretation P)).applyVec
            (secondPhysicalZeroVec P) =
        secondPhysicalRangeVec P := by
      have zeroCoordinates : secondPhysicalZeroVec P =
          HilbertVector.reindex
            (QuantumLayout.relabelBasis (OrderPreparation.layout P)
              (OrderCircuit.secondShift P)) (physicalZeroVec P) := by
        rfl
      have rangeCoordinates : secondPhysicalRangeVec P =
          HilbertVector.reindex
            (QuantumLayout.relabelBasis (OrderPreparation.layout P)
              (OrderCircuit.secondShift P)) (physicalRangeVec P) := by
        rfl
      rw [zeroCoordinates, rangeCoordinates]
      change
        (((OrderPreparation.Native.circuit (OrderOracle.model P) P expansion).relabel
            (OrderCircuit.secondShift P)).applyVec (OrderOracle.interpretation P))
          (HilbertVector.reindex
            (QuantumLayout.relabelBasis (OrderPreparation.layout P)
              (OrderCircuit.secondShift P)) (physicalZeroVec P)) =
        HilbertVector.reindex
          (QuantumLayout.relabelBasis (OrderPreparation.layout P)
            (OrderCircuit.secondShift P)) (physicalRangeVec P)
      rw [UnitaryCircuit.relabel_applyVec_reindex]
      exact congrArg
        (HilbertVector.reindex
          (QuantumLayout.relabelBasis (OrderPreparation.layout P)
            (OrderCircuit.secondShift P)))
        (native_apply_zero P expansion)
    rw [UnitaryCircuit.tensor_native_applyVec_appendVector,
      native_apply_zero, rightAction]
  rw [UnitaryCircuit.castLayout_applyVec]
  exact congrArg (fun state => same ▸ state) tensorAction

private def workspaceZeroVec (P : KnownOrderProblem G) :
    HilbertVector (OrderOracle.workspaceLayout P).register :=
  (NormalizedVector.ket (R := (OrderOracle.workspaceLayout P).register)
    (OrderOracle.workspaceLayout P).zeroLabel :
      HilbertVector (OrderOracle.workspaceLayout P).register)

private def fullInputTensor (P : KnownOrderProblem G) :
    HilbertVector (OrderOracle.layout P).register :=
  UnitaryCircuit.appendVector (OrderOracle.exponent_workspace_disjoint P)
    (pairZeroVec P) (workspaceZeroVec P)

private def fullPreparedTarget (P : KnownOrderProblem G) :
    HilbertVector (OrderOracle.layout P).register :=
  UnitaryCircuit.appendVector (OrderOracle.exponent_workspace_disjoint P)
    (pairRangeVec P) (workspaceZeroVec P)

private lemma preparations_apply_tensor_zero (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((OrderCircuit.preparations P expansion).matrix (OrderOracle.interpretation P)).applyVec
      (fullInputTensor P) =
      fullPreparedTarget P := by
  unfold OrderCircuit.preparations OrderCircuit.withWorkspace
  unfold fullInputTensor fullPreparedTarget
  rw [UnitaryCircuit.tensor_native_applyVec_appendVector,
    pairCircuit_apply_zero]
  congr 1
  exact UnitaryCircuit.applyVec_identity (workspaceZeroVec P) (OrderOracle.interpretation P)


omit [Fintype G] in
private lemma physicalZeroVec_eq_ket_zero (P : KnownOrderProblem G) :
    physicalZeroVec P =
      (NormalizedVector.ket (R := (OrderPreparation.layout P).register)
        (OrderPreparation.layout P).zeroLabel :
        HilbertVector (OrderPreparation.layout P).register) := by
  unfold physicalZeroVec physicalBinaryVec
  rw [HilbertVector.reindex_ket]
  congr 2
  apply (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).injective
  rw [(QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).apply_symm_apply]
  unfold QuantumSignature.qubitsIndexEquiv
  rw [show (OrderPreparation.layout P).zeroLabel =
      (fun _ : Fin (OrderPreparation.width P) => (0 : Fin 2)) by
    funext index
    apply Fin.ext
    rfl]
  exact (BinaryBasis.bigEndianEquiv_zero _).symm

omit [Fintype G] in
private lemma secondPhysicalZeroVec_eq_ket_zero (P : KnownOrderProblem G) :
    secondPhysicalZeroVec P =
      (NormalizedVector.ket (R := (OrderCircuit.secondLayout P).register)
        (OrderCircuit.secondLayout P).zeroLabel :
        HilbertVector (OrderCircuit.secondLayout P).register) := by
  change physicalZeroVec P =
    (NormalizedVector.ket (R := (OrderPreparation.layout P).register)
      (OrderPreparation.layout P).zeroLabel :
      HilbertVector (OrderPreparation.layout P).register)
  exact physicalZeroVec_eq_ket_zero P

omit [Fintype G] in
private lemma pairZeroVec_eq_ket_zero (P : KnownOrderProblem G) :
    pairZeroVec P =
      (NormalizedVector.ket (R := (OrderOracle.exponentLayout P).register)
        (OrderOracle.exponentLayout P).zeroLabel :
        HilbertVector (OrderOracle.exponentLayout P).register) := by
  unfold pairZeroVec
  rw [physicalZeroVec_eq_ket_zero, secondPhysicalZeroVec_eq_ket_zero,
    UnitaryCircuit.appendVector_ket, UnitaryCircuit.castLayout_ket,
    QuantumLayout.appendJoinBasis_zero, UnitaryCircuit.castLayout_zeroLabel]

private lemma fullInputTensor_eq_inputVec (P : KnownOrderProblem G) :
    fullInputTensor P = inputVec P := by
  unfold fullInputTensor workspaceZeroVec inputVec
  rw [pairZeroVec_eq_ket_zero, UnitaryCircuit.appendVector_ket]
  rw [QuantumLayout.appendJoinBasis_zero]
  unfold OrderOracle.layout
  rfl

private lemma preparations_apply_input (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((OrderCircuit.preparations P expansion).matrix (OrderOracle.interpretation P)).applyVec
      (inputVec P) =
      fullPreparedTarget P := by
  rw [← fullInputTensor_eq_inputVec]
  exact preparations_apply_tensor_zero P expansion





omit [Fintype G] in
private lemma pairRangeVec_apply (P : KnownOrderProblem G)
    (basis : (OrderOracle.exponentLayout P).Basis) :
    pairRangeVec P basis =
      OrderPreparation.state P (OrderOracle.exponentBasisEquiv P basis).1 *
        OrderPreparation.state P (OrderOracle.exponentBasisEquiv P basis).2 := by
  unfold pairRangeVec
  rw [UnitaryCircuit.castLayout_vector_apply,
    UnitaryCircuit.appendVector_apply, physicalRangeVec_apply,
    secondPhysicalRangeVec_apply]
  have semantic := exponentBasisEquiv_split P basis
  rw [semantic]


private lemma fullPreparedTarget_apply (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    fullPreparedTarget P (fullBasis P left right tail) =
      @ite ℂ (tail = 1) (Classical.propDecidable _)
        (OrderPreparation.state P left * OrderPreparation.state P right)
        0 := by
  classical
  unfold fullPreparedTarget
  unfold workspaceZeroVec
  rw [UnitaryCircuit.appendVector_apply, NormalizedVector.ket_apply]
  have semantic := basisEquiv_fullBasis P left right tail
  unfold OrderOracle.basisEquiv at semantic
  simp only [Equiv.trans_apply] at semantic
  change
    (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P left right tail)).1,
      OrderOracle.workspaceBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P left right tail)).2) = ((left, right), tail) at semantic
  have exponentSemantic := congrArg Prod.fst semantic
  have workspaceSemantic := congrArg Prod.snd semantic
  have leftSemantic := congrArg Prod.fst exponentSemantic
  have rightSemantic := congrArg Prod.snd exponentSemantic
  have tailSemantic :
      OrderOracle.workspaceBasisEquiv P
          (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
            (OrderOracle.workspaceLayout P)
            (OrderOracle.exponent_workspace_disjoint P)
            (fullBasis P left right tail)).2 = tail := by
    simpa only [Prod.snd] using workspaceSemantic
  rw [pairRangeVec_apply, leftSemantic, rightSemantic]
  by_cases tailIdentity : tail = 1
  · rw [if_pos tailIdentity]
    have physicalIdentity :
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P left right tail)).2 =
            (OrderOracle.workspaceLayout P).zeroLabel := by
      apply (OrderOracle.workspaceBasisEquiv P).injective
      rw [OrderOracle.workspaceBasisEquiv_zero, tailSemantic, tailIdentity]
    rw [if_pos physicalIdentity, mul_one]
  · rw [if_neg tailIdentity]
    have physicalNotIdentity :
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (OrderOracle.workspaceLayout P)
          (OrderOracle.exponent_workspace_disjoint P)
          (fullBasis P left right tail)).2 ≠
            (OrderOracle.workspaceLayout P).zeroLabel := by
      intro physicalIdentity
      apply tailIdentity
      rw [← tailSemantic, physicalIdentity,
        OrderOracle.workspaceBasisEquiv_zero]
    rw [if_neg physicalNotIdentity, mul_zero]


public lemma preparedVec_apply (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    preparedVec P expansion (fullBasis P left right tail) =
      @ite ℂ (tail = 1) (Classical.propDecidable _)
        (if right.val < P.order then
          if left.val < P.order then
            OrderPreparation.invSqrtOrder P.order *
              OrderPreparation.invSqrtOrder P.order
          else 0
        else 0)
        0 := by
  classical
  unfold preparedVec
  rw [preparations_apply_input, fullPreparedTarget_apply,
    OrderPreparation.state_apply, OrderPreparation.state_apply]
  by_cases tailIdentity : tail = 1 <;>
    by_cases rightInRange : right.val < P.order <;>
      by_cases leftInRange : left.val < P.order <;>
        simp [tailIdentity, rightInRange, leftInRange]


public lemma postOracleVec_support (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    postOracleVec P expansion (fullBasis P left right tail) =
      if right.val < P.order then
        if left.val < P.order then
          @ite ℂ (tail = P.toSourceScope.oracleMultiplier left.val right.val)
              (Classical.propDecidable _)
            (OrderPreparation.invSqrtOrder P.order *
              OrderPreparation.invSqrtOrder P.order)
            0
        else 0
      else 0 := by
  classical
  rw [postOracleVec_apply, preparedVec_apply]
  simp only [mul_inv_eq_one]
  by_cases rightInRange : right.val < P.order <;>
    by_cases leftInRange : left.val < P.order <;>
      simp [rightInRange, leftInRange]


/-- Double Fourier sum for the complete post-circuit amplitude at one output basis. -/
public def circuitAmplitude (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) : ℂ :=
  ∑ sourceLeft : Fin (2 ^ OrderPreparation.width P),
    ∑ sourceRight : Fin (2 ^ OrderPreparation.width P),
      star (invSqrtN (OrderPreparation.width P) *
        ω (OrderPreparation.width P) ^ (sourceLeft.val * left.val)) *
      star (invSqrtN (OrderPreparation.width P) *
        ω (OrderPreparation.width P) ^ (sourceRight.val * right.val)) *
      postOracleVec P expansion (fullBasis P sourceLeft sourceRight tail)

public lemma circuit_amplitude (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    evolvedState P expansion (fullBasis P left right tail) =
      circuitAmplitude P expansion left right tail := by
  unfold evolvedState
  unfold UnitaryCircuit.applyNormalized
  rw [UnitaryOperator.apply_coe]
  change ((OrderCircuit.circuit P expansion).applyVec (OrderOracle.interpretation P)) (inputVec P)
      (fullBasis P left right tail) = _
  rw [circuit_applyVec_zero]
  change HilbertOperator.applyVec
      (((OrderCircuit.inverseQFTs P).matrix (OrderOracle.interpretation P)) :
        HilbertOperator (OrderOracle.layout P).register)
      (postOracleVec P expansion) (fullBasis P left right tail) = _
  rw [HilbertOperator.applyVec_apply]
  change (∑ sourceBasis : (OrderOracle.layout P).Basis,
      ((OrderCircuit.inverseQFTs P).matrix (OrderOracle.interpretation P)) (fullBasis P left right
        tail) sourceBasis *
        postOracleVec P expansion sourceBasis) = _
  rw [← Equiv.sum_comp (OrderOracle.basisEquiv P).symm,
    Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  change (∑ sourceLeft : Fin (2 ^ OrderPreparation.width P),
      ∑ sourceRight : Fin (2 ^ OrderPreparation.width P),
      ∑ sourceTail : G,
        ((OrderCircuit.inverseQFTs P).matrix (OrderOracle.interpretation P))
            (fullBasis P left right tail)
            (fullBasis P sourceLeft sourceRight sourceTail) *
          postOracleVec P expansion
            (fullBasis P sourceLeft sourceRight sourceTail)) = _
  rw [circuitAmplitude]
  apply Finset.sum_congr rfl
  intro sourceLeft _
  apply Finset.sum_congr rfl
  intro sourceRight _
  rw [Finset.sum_eq_single tail]
  · rw [inverseQFTs_matrix_fullBasis, if_pos rfl]
    change
      star (QFTOperator (OrderPreparation.width P) sourceLeft left) *
          star (QFTOperator (OrderPreparation.width P) sourceRight right) *
            postOracleVec P expansion (fullBasis P sourceLeft sourceRight tail) =
        star (invSqrtN (OrderPreparation.width P) *
            ω (OrderPreparation.width P) ^ (sourceLeft.val * left.val)) *
          star (invSqrtN (OrderPreparation.width P) *
            ω (OrderPreparation.width P) ^ (sourceRight.val * right.val)) *
          postOracleVec P expansion (fullBasis P sourceLeft sourceRight tail)
    rw [QFTOperator_entry, QFTOperator_entry]
  · intro sourceTail _ different
    rw [inverseQFTs_matrix_fullBasis, if_neg (Ne.symm different)]
    simp
  · simp

end

end QuantumAlg.FiniteCyclicDLP.OrderBornBridge

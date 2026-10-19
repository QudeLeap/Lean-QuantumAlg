/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Circuit
public import QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Circuit
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero

/-!
# Exact preparation and Fourier amplitudes on the binary DLP bank

The same generated range-preparation and inverse-QFT words act on the two
physical exponent blocks. The remaining group block is a binary register;
its unoccupied labels are retained in the complete physical basis. No gate or
probability claim is inferred from dimension counting [Sho95, source.tex:1713-1784].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary.Fourier

noncomputable section

universe u v

local instance {α : Type v} : DecidableEq α := Classical.decEq α

variable {G : Type u} [Group G]

local instance : DecidableEq G := Classical.decEq G

/-- Physical basis label named by its two binary exponent values and binary
group label. -/
@[expose] public def fullBasis (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : Fin (2 ^ groupWidth P)) :
    (Oracle.layout P).Basis :=
  (Oracle.basisEquiv P).symm ((left, right), tail)

@[simp] public lemma binaryFourier_basisEquiv_fullBasis (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : Fin (2 ^ groupWidth P)) :
    Oracle.basisEquiv P (fullBasis P left right tail) = ((left, right), tail) :=
  (Oracle.basisEquiv P).apply_symm_apply ((left, right), tail)

/-- Fixed zero preparation is exactly the logical `(0,0,0)` basis state. -/
public lemma binaryFourier_fullBasis_zero (P : KnownOrderProblem G) :
    fullBasis P 0 0 0 = (Oracle.layout P).zeroLabel := by
  apply (Oracle.basisEquiv P).injective
  rw [binaryFourier_basisEquiv_fullBasis, Oracle.binaryOracle_basisEquiv_zero]

/-- Raw zero vector consumed by the native unitary stage. -/
public def inputVec (P : KnownOrderProblem G) :
    HilbertVector (Oracle.layout P).register :=
  (NormalizedVector.ket (R := (Oracle.layout P).register)
    (Oracle.layout P).zeroLabel :
    HilbertVector (Oracle.layout P).register)

/-- State produced by the two actual range-preparation words. -/
public def preparedVec (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    HilbertVector (Oracle.layout P).register :=
  ((Binary.Circuit.preparations P expansion).matrix (Oracle.interpretation P)).applyVec (inputVec P)

/-- State after the sole declared `U_x` query. -/
public def postOracleVec (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    HilbertVector (Oracle.layout P).register :=
  ((Oracle.circuit AlgorithmGate.model P).matrix (Oracle.interpretation P)).applyVec
    (preparedVec P expansion)

/-- Normalized terminal state of the exact preparation-query-inverse-QFT word. -/
public def evolvedState (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    NormalizedVector (Oracle.layout P).register :=
  ((Binary.Circuit.circuit P expansion).applyNormalized (Oracle.interpretation P))
    (NormalizedVector.ket (Oracle.layout P).zeroLabel)

/-- The circuit's sequential structure exposes the same stored queried vector
to the two generated inverse-QFT words. -/
public lemma binaryFourier_circuit_applyVec_zero (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((Binary.Circuit.circuit P expansion).applyVec (Oracle.interpretation P)) (inputVec P) =
      ((Binary.Circuit.inverseQFTs P).applyVec (Oracle.interpretation P))
        (postOracleVec P expansion) := by
  rw [Binary.Circuit.circuit, UnitaryCircuit.applyVec_seq,
    UnitaryCircuit.applyVec_seq]
  rfl

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
    HilbertVector (Binary.Circuit.secondLayout P).register :=
  HilbertVector.reindex
    (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).symm state

private def secondPhysicalZeroVec (P : KnownOrderProblem G) :
    HilbertVector (Binary.Circuit.secondLayout P).register :=
  secondPhysicalBinaryVec P
    (NormalizedVector.ket (R := Qubits (OrderPreparation.width P)) 0)

private def secondPhysicalRangeVec (P : KnownOrderProblem G) :
    HilbertVector (Binary.Circuit.secondLayout P).register :=
  secondPhysicalBinaryVec P (OrderPreparation.state P)

@[simp] private lemma physicalRangeVec_apply (P : KnownOrderProblem G)
    (basis : (OrderPreparation.layout P).Basis) :
    physicalRangeVec P basis =
      OrderPreparation.state P
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) basis) :=
  rfl

@[simp] private lemma secondPhysicalRangeVec_apply (P : KnownOrderProblem G)
    (basis : (Binary.Circuit.secondLayout P).Basis) :
    secondPhysicalRangeVec P basis =
      OrderPreparation.state P
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) basis) :=
  rfl

private lemma native_apply_zero (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((OrderPreparation.Native.circuit (Oracle.model P) P expansion).matrix (Oracle.interpretation
      P)).applyVec
        (physicalZeroVec P) = physicalRangeVec P := by
  have transported := UnitaryOperator.reindex_applyVec
    (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)).symm
    ((OrderPreparation.Native.circuit (Oracle.model P) P expansion).binaryMatrix
      (Oracle.interpretation P))
    (NormalizedVector.ket (R := Qubits (OrderPreparation.width P)) 0 :
      HilbertVector (Qubits (OrderPreparation.width P)))
  rw [UnitaryCircuit.binaryMatrix_eq_reindex,
    UnitaryOperator.unitaryOperator_reindex_cancel] at transported
  have binaryAction := OrderPreparation.Native.circuit_applyVec_zero
    (environment := Oracle.interpretation P)
    (Oracle.model P) P expansion
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
        (Oracle.model P) (OrderPreparation.width P)).matrix (Oracle.interpretation P)).applyVec
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
        (Oracle.model P) (OrderPreparation.width P)).matrix (Oracle.interpretation P)) output input
          =
      (star (QFTOperator (OrderPreparation.width P)))
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) output)
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) input) := by
  have entry := congrArg
    (fun operator : UnitaryOperator (Qubits (OrderPreparation.width P)) =>
      operator
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) output)
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) input))
    (QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
      (Oracle.model P) (OrderPreparation.width P) (Oracle.interpretation P))
  unfold QuantumFourierTransform.Native.onBinaryLabels at entry
  simpa only [UnitaryOperator.coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply] using entry

private lemma inverseQFT_relabel_matrix_entry (P : KnownOrderProblem G)
    (output input : (Binary.Circuit.secondLayout P).Basis) :
    (((QuantumFourierTransform.Native.inverseCircuit
        (Oracle.model P) (OrderPreparation.width P)).relabel
          (Binary.Circuit.secondShift P)).matrix (Oracle.interpretation P)) output input =
      (star (QFTOperator (OrderPreparation.width P)))
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) output)
        (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P) input) := by
  rw [UnitaryCircuit.relabel_matrix]
  exact inverseQFT_matrix_entry P output input


private lemma pairCircuit_matrix_entry (P : KnownOrderProblem G)
    (left : UnitaryCircuit AlgorithmGate.model (Oracle.model P)
      (OrderPreparation.layout P))
    (right : UnitaryCircuit AlgorithmGate.model (Oracle.model P)
      (Binary.Circuit.secondLayout P))
    (row column : (OrderOracle.exponentLayout P).Basis) :
    ((Binary.Circuit.pairCircuit P left right).matrix (Oracle.interpretation P)) row column =
      (left.matrix (Oracle.interpretation P))
          (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
            (Binary.Circuit.secondLayout P)
              (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
            ((Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P).symm ▸ row)).1
          (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
            (Binary.Circuit.secondLayout P)
              (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
            ((Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P).symm ▸ column)).1 *
        (right.matrix (Oracle.interpretation P))
          (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
            (Binary.Circuit.secondLayout P)
              (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
            ((Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P).symm ▸ row)).2
          (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
            (Binary.Circuit.secondLayout P)
              (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
            ((Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P).symm ▸ column)).2 := by
  rw [Binary.Circuit.pairCircuit, UnitaryCircuit.castLayout_matrix_entry,
    UnitaryCircuit.tensor_native_matrix_entry]


private lemma exponentBasisEquiv_split (P : KnownOrderProblem G)
    (basis : (OrderOracle.exponentLayout P).Basis) :
    OrderOracle.exponentBasisEquiv P basis =
      (QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)
        (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
          (Binary.Circuit.secondLayout P) (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
          ((Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P).symm ▸ basis)).1,
       QuantumSignature.qubitsIndexEquiv (OrderPreparation.width P)
        (QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
          (Binary.Circuit.secondLayout P) (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
          ((Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P).symm ▸ basis)).2) := by
  let same := Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P
  let pairBasis := same.symm ▸ basis
  let split := QuantumLayout.appendBasisEquiv (OrderPreparation.layout P)
    (Binary.Circuit.secondLayout P) (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
      pairBasis
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
    ((Binary.Circuit.pairCircuit P
      (QuantumFourierTransform.Native.inverseCircuit
        (Oracle.model P) (OrderPreparation.width P))
      ((QuantumFourierTransform.Native.inverseCircuit
        (Oracle.model P) (OrderPreparation.width P)).relabel
          (Binary.Circuit.secondShift P))).matrix (Oracle.interpretation P)) row column =
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


public lemma binaryFourier_inverseQFTs_matrix_fullBasis (P : KnownOrderProblem G)
    (outputLeft outputRight inputLeft inputRight :
      Fin (2 ^ OrderPreparation.width P))
    (outputTail inputTail : Fin (2 ^ groupWidth P)) :
    ((Binary.Circuit.inverseQFTs P).matrix (Oracle.interpretation P))
        (fullBasis P outputLeft outputRight outputTail)
        (fullBasis P inputLeft inputRight inputTail) =
      @ite ℂ (outputTail = inputTail) (Classical.propDecidable _)
        ((star (QFTOperator (OrderPreparation.width P)))
            outputLeft inputLeft *
          (star (QFTOperator (OrderPreparation.width P)))
            outputRight inputRight)
        0 := by
  classical
  unfold Binary.Circuit.inverseQFTs Binary.Circuit.withWorkspace
  rw [UnitaryCircuit.tensor_native_matrix_entry,
    pairInverseQFT_matrix_entry, UnitaryCircuit.identity_matrix]
  have outputSemantic :=
    binaryFourier_basisEquiv_fullBasis P outputLeft outputRight outputTail
  have inputSemantic :=
    binaryFourier_basisEquiv_fullBasis P inputLeft inputRight inputTail
  unfold Oracle.basisEquiv at outputSemantic inputSemantic
  simp only [Equiv.trans_apply] at outputSemantic inputSemantic
  change
    (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).1,
      Oracle.workspaceBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).2) =
        ((outputLeft, outputRight), outputTail) at outputSemantic
  change
    (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).1,
      Oracle.workspaceBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).2) =
        ((inputLeft, inputRight), inputTail) at inputSemantic
  have outputExponent := congrArg Prod.fst outputSemantic
  have inputExponent := congrArg Prod.fst inputSemantic
  have outputWorkspace :
      Oracle.workspaceBasisEquiv P
          (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
            (Oracle.workspaceLayout P)
            (Oracle.binaryOracle_exponent_workspace_disjoint P)
            (fullBasis P outputLeft outputRight outputTail)).2 = outputTail := by
    simpa only [Prod.snd] using congrArg Prod.snd outputSemantic
  have inputWorkspace :
      Oracle.workspaceBasisEquiv P
          (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
            (Oracle.workspaceLayout P)
            (Oracle.binaryOracle_exponent_workspace_disjoint P)
            (fullBasis P inputLeft inputRight inputTail)).2 = inputTail := by
    simpa only [Prod.snd] using congrArg Prod.snd inputSemantic
  have outputLeftCoordinate :
      (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).1).1 = outputLeft := by
    simpa only [Prod.fst] using congrArg Prod.fst outputExponent
  have outputRightCoordinate :
      (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).1).2 = outputRight := by
    simpa only [Prod.snd] using congrArg Prod.snd outputExponent
  have inputLeftCoordinate :
      (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).1).1 = inputLeft := by
    simpa only [Prod.fst] using congrArg Prod.fst inputExponent
  have inputRightCoordinate :
      (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).1).2 = inputRight := by
    simpa only [Prod.snd] using congrArg Prod.snd inputExponent
  rw [outputLeftCoordinate, outputRightCoordinate,
    inputLeftCoordinate, inputRightCoordinate]
  have workspaceSame :
      (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P outputLeft outputRight outputTail)).2 =
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P inputLeft inputRight inputTail)).2 ↔
      outputTail = inputTail := by
    constructor
    · intro same
      calc
        outputTail = Oracle.workspaceBasisEquiv P
            (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
              (Oracle.workspaceLayout P)
              (Oracle.binaryOracle_exponent_workspace_disjoint P)
              (fullBasis P outputLeft outputRight outputTail)).2 := outputWorkspace.symm
        _ = Oracle.workspaceBasisEquiv P
            (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
              (Oracle.workspaceLayout P)
              (Oracle.binaryOracle_exponent_workspace_disjoint P)
              (fullBasis P inputLeft inputRight inputTail)).2 := congrArg _ same
        _ = inputTail := inputWorkspace
    · intro same
      apply (Oracle.workspaceBasisEquiv P).injective
      rw [outputWorkspace, inputWorkspace, same]
  rw [Matrix.UnitaryGroup.one_apply, Matrix.one_apply]
  rw [if_congr workspaceSame rfl rfl]
  by_cases same : outputTail = inputTail <;> simp [same]


private def pairZeroVec (P : KnownOrderProblem G) :
    HilbertVector (OrderOracle.exponentLayout P).register :=
  Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P ▸
    UnitaryCircuit.appendVector (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
      (physicalZeroVec P) (secondPhysicalZeroVec P)

private def pairRangeVec (P : KnownOrderProblem G) :
    HilbertVector (OrderOracle.exponentLayout P).register :=
  Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P ▸
    UnitaryCircuit.appendVector (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
      (physicalRangeVec P) (secondPhysicalRangeVec P)

private lemma pairCircuit_apply_zero (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((Binary.Circuit.pairCircuit P
      (OrderPreparation.Native.circuit (Oracle.model P) P expansion)
      ((OrderPreparation.Native.circuit (Oracle.model P) P expansion).relabel
        (Binary.Circuit.secondShift P))).matrix (Oracle.interpretation P)).applyVec (pairZeroVec P)
          =
      pairRangeVec P := by
  unfold Binary.Circuit.pairCircuit pairZeroVec pairRangeVec
  change
    ((UnitaryCircuit.castLayout (Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P)
      (UnitaryCircuit.tensor
        (OrderPreparation.Native.circuit (Oracle.model P) P expansion)
        ((OrderPreparation.Native.circuit (Oracle.model P) P expansion).relabel
          (Binary.Circuit.secondShift P))
        (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P))).applyVec (Oracle.interpretation
          P))
      (Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P ▸
        UnitaryCircuit.appendVector (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
          (physicalZeroVec P) (secondPhysicalZeroVec P)) = _
  let same := Binary.Circuit.binaryCircuit_pairLayout_eq_exponentLayout P
  have tensorAction :
      ((UnitaryCircuit.tensor
        (OrderPreparation.Native.circuit (Oracle.model P) P expansion)
        ((OrderPreparation.Native.circuit (Oracle.model P) P expansion).relabel
          (Binary.Circuit.secondShift P))
        (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)).matrix (Oracle.interpretation
          P)).applyVec
          (UnitaryCircuit.appendVector (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
            (physicalZeroVec P) (secondPhysicalZeroVec P)) =
        UnitaryCircuit.appendVector (Binary.Circuit.binaryCircuit_exponentLayouts_disjoint P)
          (physicalRangeVec P) (secondPhysicalRangeVec P) := by
    have rightAction :
        (((OrderPreparation.Native.circuit (Oracle.model P) P expansion).relabel
          (Binary.Circuit.secondShift P)).matrix (Oracle.interpretation P)).applyVec
            (secondPhysicalZeroVec P) =
        secondPhysicalRangeVec P := by
      have zeroCoordinates : secondPhysicalZeroVec P =
          HilbertVector.reindex
            (QuantumLayout.relabelBasis (OrderPreparation.layout P)
              (Binary.Circuit.secondShift P)) (physicalZeroVec P) := by
        rfl
      have rangeCoordinates : secondPhysicalRangeVec P =
          HilbertVector.reindex
            (QuantumLayout.relabelBasis (OrderPreparation.layout P)
              (Binary.Circuit.secondShift P)) (physicalRangeVec P) := by
        rfl
      rw [zeroCoordinates, rangeCoordinates]
      change
        (((OrderPreparation.Native.circuit (Oracle.model P) P expansion).relabel
            (Binary.Circuit.secondShift P)).applyVec (Oracle.interpretation P))
          (HilbertVector.reindex
            (QuantumLayout.relabelBasis (OrderPreparation.layout P)
              (Binary.Circuit.secondShift P)) (physicalZeroVec P)) =
        HilbertVector.reindex
          (QuantumLayout.relabelBasis (OrderPreparation.layout P)
            (Binary.Circuit.secondShift P)) (physicalRangeVec P)
      rw [UnitaryCircuit.relabel_applyVec_reindex]
      exact congrArg
        (HilbertVector.reindex
          (QuantumLayout.relabelBasis (OrderPreparation.layout P)
            (Binary.Circuit.secondShift P)))
        (native_apply_zero P expansion)
    rw [UnitaryCircuit.tensor_native_applyVec_appendVector,
      native_apply_zero, rightAction]
  rw [UnitaryCircuit.castLayout_applyVec]
  exact congrArg (fun state => same ▸ state) tensorAction

private def workspaceZeroVec (P : KnownOrderProblem G) :
    HilbertVector (Oracle.workspaceLayout P).register :=
  (NormalizedVector.ket (R := (Oracle.workspaceLayout P).register)
    (Oracle.workspaceLayout P).zeroLabel :
      HilbertVector (Oracle.workspaceLayout P).register)

private def fullInputTensor (P : KnownOrderProblem G) :
    HilbertVector (Oracle.layout P).register :=
  UnitaryCircuit.appendVector (Oracle.binaryOracle_exponent_workspace_disjoint P)
    (pairZeroVec P) (workspaceZeroVec P)

private def fullPreparedTarget (P : KnownOrderProblem G) :
    HilbertVector (Oracle.layout P).register :=
  UnitaryCircuit.appendVector (Oracle.binaryOracle_exponent_workspace_disjoint P)
    (pairRangeVec P) (workspaceZeroVec P)

private lemma preparations_apply_tensor_zero (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((Binary.Circuit.preparations P expansion).matrix (Oracle.interpretation P)).applyVec
      (fullInputTensor P) =
      fullPreparedTarget P := by
  unfold Binary.Circuit.preparations Binary.Circuit.withWorkspace
  unfold fullInputTensor fullPreparedTarget
  rw [UnitaryCircuit.tensor_native_applyVec_appendVector,
    pairCircuit_apply_zero]
  congr 1
  exact UnitaryCircuit.applyVec_identity (workspaceZeroVec P) (Oracle.interpretation P)


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

private lemma secondPhysicalZeroVec_eq_ket_zero (P : KnownOrderProblem G) :
    secondPhysicalZeroVec P =
      (NormalizedVector.ket (R := (Binary.Circuit.secondLayout P).register)
        (Binary.Circuit.secondLayout P).zeroLabel :
        HilbertVector (Binary.Circuit.secondLayout P).register) := by
  change physicalZeroVec P =
    (NormalizedVector.ket (R := (OrderPreparation.layout P).register)
      (OrderPreparation.layout P).zeroLabel :
      HilbertVector (OrderPreparation.layout P).register)
  exact physicalZeroVec_eq_ket_zero P

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
  unfold Oracle.layout
  rfl

private lemma preparations_apply_input (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ((Binary.Circuit.preparations P expansion).matrix (Oracle.interpretation P)).applyVec (inputVec
      P) =
      fullPreparedTarget P := by
  rw [← fullInputTensor_eq_inputVec]
  exact preparations_apply_tensor_zero P expansion





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
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : Fin (2 ^ groupWidth P)) :
    fullPreparedTarget P (fullBasis P left right tail) =
      @ite ℂ (tail = 0) (Classical.propDecidable _)
        (OrderPreparation.state P left * OrderPreparation.state P right)
        0 := by
  classical
  unfold fullPreparedTarget
  unfold workspaceZeroVec
  rw [UnitaryCircuit.appendVector_apply, NormalizedVector.ket_apply]
  have semantic := binaryFourier_basisEquiv_fullBasis P left right tail
  unfold Oracle.basisEquiv at semantic
  simp only [Equiv.trans_apply] at semantic
  change
    (OrderOracle.exponentBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P left right tail)).1,
      Oracle.workspaceBasisEquiv P
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P left right tail)).2) = ((left, right), tail) at semantic
  have exponentSemantic := congrArg Prod.fst semantic
  have workspaceSemantic := congrArg Prod.snd semantic
  have leftSemantic := congrArg Prod.fst exponentSemantic
  have rightSemantic := congrArg Prod.snd exponentSemantic
  have tailSemantic :
      Oracle.workspaceBasisEquiv P
          (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
            (Oracle.workspaceLayout P)
            (Oracle.binaryOracle_exponent_workspace_disjoint P)
            (fullBasis P left right tail)).2 = tail := by
    simpa only [Prod.snd] using workspaceSemantic
  rw [pairRangeVec_apply, leftSemantic, rightSemantic]
  by_cases tailIdentity : tail = 0
  · rw [if_pos tailIdentity]
    have physicalIdentity :
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P left right tail)).2 =
            (Oracle.workspaceLayout P).zeroLabel := by
      apply (Oracle.workspaceBasisEquiv P).injective
      rw [Oracle.binaryOracle_workspaceBasisEquiv_zero, tailSemantic, tailIdentity]
    rw [if_pos physicalIdentity, mul_one]
  · rw [if_neg tailIdentity]
    have physicalNotIdentity :
        (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
          (Oracle.workspaceLayout P)
          (Oracle.binaryOracle_exponent_workspace_disjoint P)
          (fullBasis P left right tail)).2 ≠
            (Oracle.workspaceLayout P).zeroLabel := by
      intro physicalIdentity
      apply tailIdentity
      rw [← tailSemantic, physicalIdentity,
        Oracle.binaryOracle_workspaceBasisEquiv_zero]
    rw [if_neg physicalNotIdentity, mul_zero]


public lemma binaryFourier_preparedVec_apply (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : Fin (2 ^ groupWidth P)) :
    preparedVec P expansion (fullBasis P left right tail) =
      @ite ℂ (tail = 0) (Classical.propDecidable _)
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
  by_cases tailIdentity : tail = 0 <;>
    by_cases rightInRange : right.val < P.order <;>
      by_cases leftInRange : left.val < P.order <;>
        simp [tailIdentity, rightInRange, leftInRange]


end

end QuantumAlg.FiniteCyclicDLP.Binary.Fourier

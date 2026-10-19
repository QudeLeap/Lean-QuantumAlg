/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Mathematics
public import QuantumAlg.Core.Measure.Kraus
public import QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Algorithms.Teleportation.Mathematics
import all QuantumAlg.Core.Measure.Kraus
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Pauli
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Corrected teleportation branches on arbitrary joint states

The Bell resource is inserted beside the unknown input. Alice's CNOT and
Hadamard precede an actual computational-basis projector, after which Bob
applies the correction selected by the two measured bits
[dW19, qcnotes.tex:785,790,802,804]. The resulting rectangular Kraus operator
is one half of the identity, including its phase. Tensoring this identity
with an arbitrary reference preserves every off-diagonal matrix entry, as
required by the source's entanglement statement [dW19, qcnotes.tex:809].

These are matrix identities used to prove the native interpreter's channel.
They do not define another execution or an independently supplied outcome.
-/

namespace QuantumAlg.QuantumTeleportation

noncomputable section

open NormalizedVector Gate

/-- The computational-basis value represented by one measured bit. -/
def bitValue (bit : Bool) : Fin 2 := if bit then 1 else 0

/-- Big-endian encoding of Alice's two actual measurement outcomes. -/
def outcomeValue (first second : Bool) : Fin 4 :=
  finProdFinEquiv (bitValue first, bitValue second)

/-- Insert the shared Bell vector while leaving every unknown input amplitude unchanged. -/
def bellInsertion : Matrix (Fin 8) (Fin 2) ℂ :=
  fun row column =>
    HilbertVector.tensor (ket (R := Qubits 1) column : HilbertVector (Qubits 1))
      (bell : HilbertVector (Qubits 2)) row

/-- Alice's computational-basis projector, with Bob's qubit retained. -/
def aliceProjector (first second : Bool) : Matrix (Fin 2) (Fin 8) ℂ :=
  fun row column =>
    MeasurementInstrument.selectHead (outcomeValue first second) row
      (finProdFinEquiv.symm column)

/-- The exact corrected branch, with the rightmost factor applied first. -/
public def correctedKraus (first second : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (teleportCorrection first second : HilbertOperator (Qubits 1)) *
    aliceProjector first second *
    (teleportBellMeasure : HilbertOperator (Qubits 3)) * bellInsertion

/-- Every measured branch transfers the unknown qubit with the same exact scalar. -/
public lemma teleportation_correctedKraus_eq_half_identity (first second : Bool) :
    correctedKraus first second = (2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext row column
  cases first <;> cases second <;> fin_cases row <;> fin_cases column <;>
    simp +decide [correctedKraus, aliceProjector, MeasurementInstrument.selectHead,
      outcomeValue, bitValue, bellInsertion, teleportCorrection, teleportBellMeasure,
      HilbertOperator.tensor, HOp, XOp, ZOp, CNOTOp, bell_coe,
      UnitaryOperator.ofPerm, UnitaryOperator.ofMatrix, NormalizedVector.ket,
      HilbertVector.tensor, prodEquiv, Matrix.mul_apply, Matrix.smul_apply,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.one_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_eight, Fin.sum_univ_two]

/-- Tensor a corrected branch with identity on an arbitrary external reference. -/
public def correctedKrausWithReference (first second : Bool) (Reference : Register) :
    HilbertOperator ((Qubits 1).prod Reference) :=
  fun row column => correctedKraus first second row.1 column.1 *
    if row.2 = column.2 then 1 else 0

/-- The same operator identity retains the entire external reference. -/
public lemma teleportation_correctedKraus_reference (first second : Bool)
    (Reference : Register) :
    correctedKrausWithReference first second Reference =
      (2 : ℂ)⁻¹ • (1 : HilbertOperator ((Qubits 1).prod Reference)) := by
  classical
  ext row column
  rcases row with ⟨row, rowRef⟩
  rcases column with ⟨column, columnRef⟩
  simp only [correctedKrausWithReference, teleportation_correctedKraus_eq_half_identity,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases localSame : row = column <;>
    by_cases referenceSame : rowRef = columnRef <;>
    simp [localSame, referenceSame]

/-- A branch has exactly one quarter of the original joint matrix, even for entangled inputs. -/
public lemma teleportation_correctedBranch_joint (first second : Bool)
    (Reference : Register) (state : HilbertOperator ((Qubits 1).prod Reference)) :
    correctedKrausWithReference first second Reference * state *
      (correctedKrausWithReference first second Reference).conjTranspose =
        (4 : ℂ)⁻¹ • state := by
  rw [teleportation_correctedKraus_reference]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  norm_num

end

end QuantumAlg.QuantumTeleportation

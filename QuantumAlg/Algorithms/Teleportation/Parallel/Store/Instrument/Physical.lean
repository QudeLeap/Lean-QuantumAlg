/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Store.Instrument
import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource.Insertion
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Physical
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Projector
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Insertion
import all QuantumAlg.Algorithms.Teleportation.Parallel.Channel.Retained
import all QuantumAlg.Algorithms.Teleportation.Parallel.Tensor
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Channel

/-!
# Actual physical teleportation instrument with retained Alice labels

The native Alice operator, actual measurement projector, store-selected Bob
correction and original Bell insertion compose into the retained branch
matrix [dW19, qcnotes.tex:790,802,804,809]. This identity retains every original
quantum system; it introduces no execution preparation or discarded subsystem.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.PhysicalInstrument

noncomputable section

open Execution StoreInstrument BellInsertion PhysicalNative
open ProjectorCoordinates InsertionCoordinates RetainedSource

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Mathematical insertion of the actual Alice labels and unchanged arbitrary Bob input labels. -/
def retainedPhysicalInsertion (count : Nat) (stored : Store (context count)) :
    Matrix (context count).register.Index (inputRegister count).Index ℂ :=
  fun row column => tensorEntries count (fun block =>
    (selector (outcomeValue (storedBits (stored.read (resultInput count)) block).1
      (storedBits (stored.read (resultInput count)) block).2)).conjTranspose)
        (contextBankBasis count row) column

/-- The actual physical `C * P * A * V` has the exact retained-Alice branch matrix. -/
lemma actualInstrument_insert_eq
    (environment : model.Environment) (count : Nat) (stored : Store (context count)) :
    actualInstrument environment count stored * physicalInsertion count =
      ((2 : ℂ)⁻¹ ^ count) • retainedPhysicalInsertion count stored := by
  let coordinates : (Fin count → Fin 8) ≃ (context count).register.Index :=
    (contextBankBasis count).symm
  let bits : Fin count → Bool × Bool := storedBits (stored.read (resultInput count))
  let C : HilbertOperator (context count).register :=
    ((selectedCorrection count (stored.read (resultInput count))).matrix environment.quantum)
  let P : HilbertOperator (context count).register := actualProjector count stored
  let A : HilbertOperator (context count).register :=
    ((onContext count (aliceWord count)).matrix environment.quantum)
  let V : Matrix (context count).register.Index (inputRegister count).Index ℂ :=
    physicalInsertion count
  have correction : C.submatrix coordinates coordinates = tensorEntries count (fun block =>
      HilbertOperator.tensor (1 : HilbertOperator (Qubits 2))
        (teleportCorrection (bits block).1 (bits block).2 : HilbertOperator (Qubits 1))) := by
    ext row column
    exact correction_matrix_entry count (stored.read (resultInput count)) row column
      environment.quantum
  have projection : P.submatrix coordinates coordinates = tensorEntries count (fun block =>
      sourceProjector (outcomeValue (bits block).1 (bits block).2)) := by
    ext row column
    exact actualProjector_native_entry count stored row column
  have alice : A.submatrix coordinates coordinates =
      tensorEntries count (fun _ => (teleportBellMeasure : HilbertOperator (Qubits 3))) := by
    ext row column
    exact alice_matrix_entry count row column environment.quantum
  have insertion : V.submatrix coordinates id = tensorEntries count (fun _ => bellInsertion) := by
    ext row column
    exact physicalInsertion_native_entry count row column
  have multiply (first second : HilbertOperator (context count).register) :
      (first * second).submatrix coordinates coordinates =
        first.submatrix coordinates coordinates * second.submatrix coordinates coordinates :=
    (Matrix.submatrix_mul_equiv first second coordinates coordinates coordinates).symm
  have together : (C * P * A * V).submatrix coordinates id =
      tensorEntries count (fun block => retainedSourceKraus (bits block).1 (bits block).2) := by
    rw [← Matrix.submatrix_mul_equiv (C * P * A) V coordinates coordinates id,
      multiply, multiply, correction, projection, alice, insertion,
      tensorEntries_mul, tensorEntries_mul, tensorEntries_mul]
    rfl
  have scalar := together.trans (tensor_retainedSourceKraus count bits)
  ext row column
  have entry := congrArg (fun matrix : Matrix (Fin count → Fin 8)
      (inputRegister count).Index ℂ => matrix (contextBankBasis count row) column) scalar
  simpa only [Matrix.submatrix_apply, Matrix.smul_apply, id_eq, coordinates,
    Equiv.symm_apply_apply, C, P, A, V, actualInstrument,
    retainedPhysicalInsertion, bits] using entry

end

end QuantumAlg.QuantumTeleportation.Parallel.PhysicalInstrument

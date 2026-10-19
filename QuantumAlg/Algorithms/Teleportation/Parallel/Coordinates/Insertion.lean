/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Physical
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Native
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates
import all QuantumAlg.Algorithms.Teleportation.Parallel.NativeMatrices
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource.Insertion
import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource
import all QuantumAlg.Algorithms.Teleportation.Channel
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Original Bell-resource insertion in native block coordinates

Each block keeps the original unknown-input wire first and the two original
Bell-resource wires second and third [dW19, qcnotes.tex:785,789]. The
mathematical insertion of the supplied Bell vector therefore agrees entry
by entry with the tensor of the source's one-block insertions. This identity
does not add any preparation to the actual execution, and it imposes no
factorization on the unknown inputs or their external reference.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.InsertionCoordinates

noncomputable section

open Execution NativeCoordinates PhysicalNative BellInsertion
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Native labels regroup into the original unknown-input wire and both original Bell wires. -/
lemma inputBellBasis_native (count : Nat) (labels : Fin count → Fin 8) :
    inputBellBasis count ((contextBankBasis count).symm labels) =
      ((fun block => (BinaryBasis.bigEndianEquiv 3).symm (labels block) 0),
       (fun block => finProdFinEquiv
         ((BinaryBasis.bigEndianEquiv 3).symm (labels block) 1,
          (BinaryBasis.bigEndianEquiv 3).symm (labels block) 2))) := by
  let physical := basisOfEqualWires (layout count) (context count).quantumLayout
    (context_wires count)
  let decoded := (BinaryBasis.bigEndianEquiv (width count)).symm
    ((bankBinaryBasis count).symm labels)
  have transported : physical.symm ((contextBankBasis count).symm labels) = decoded :=
    physical.symm_apply_apply decoded
  refine (congrArg (fun basis : (layout count).register.Index =>
    splitBank count (tripleBasis count basis)) transported).trans ?_
  apply Prod.ext
  · funext block
    exact congrArg (fun basis : Fin 3 → Fin 2 => basis 0)
      (tripleBasis_native_decode count labels block)
  · funext block
    exact congrArg (fun basis : Fin 3 → Fin 2 => finProdFinEquiv (basis 1, basis 2))
      (tripleBasis_native_decode count labels block)

/-- The source insertion uses the same most-significant input bit and two Bell bits. -/
lemma bellInsertion_entry (row : Fin 8) (input : Fin 2) :
    bellInsertion row input =
      if (BinaryBasis.bigEndianEquiv 3).symm row 0 = input then
        bell (finProdFinEquiv ((BinaryBasis.bigEndianEquiv 3).symm row 1,
          (BinaryBasis.bigEndianEquiv 3).symm row 2))
      else 0 := by
  have parts : (prodEquiv (m := 1) (n := 2)).symm row =
      ((BinaryBasis.bigEndianEquiv 3).symm row 0,
        finProdFinEquiv ((BinaryBasis.bigEndianEquiv 3).symm row 1,
          (BinaryBasis.bigEndianEquiv 3).symm row 2)) := by
    fin_cases row <;> decide
  simp only [bellInsertion, HilbertVector.tensor_apply, NormalizedVector.ket_apply, parts]
  by_cases same : (BinaryBasis.bigEndianEquiv 3).symm row 0 = input <;> simp [same]

/-- The independent physical Bell insertion is precisely the tensor of source insertions. -/
lemma physicalInsertion_native_entry (count : Nat) (row : Fin count → Fin 8)
    (input : (inputRegister count).Index) :
    physicalInsertion count ((contextBankBasis count).symm row) input =
      ∏ block : Fin count, bellInsertion (row block) (input block) := by
  unfold physicalInsertion insertAlong
  rw [inputBellBasis_native, bellBank_apply]
  simp_rw [bellInsertion_entry]
  by_cases same : (fun block => (BinaryBasis.bigEndianEquiv 3).symm (row block) 0) = input
  · rw [if_pos same]
    symm
    apply Finset.prod_congr rfl
    intro block _
    exact if_pos (congrFun same block)
  · rw [if_neg same]
    have missing : ¬(∀ block, (BinaryBasis.bigEndianEquiv 3).symm (row block) 0 = input block) :=
      fun matched => same (funext matched)
    obtain ⟨block, absent⟩ := not_forall.mp missing
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ block) (if_neg absent)

end

end QuantumAlg.QuantumTeleportation.Parallel.InsertionCoordinates

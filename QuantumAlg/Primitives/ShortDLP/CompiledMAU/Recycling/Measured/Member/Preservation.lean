/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Source
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record.Readout
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual original member records preserve every separate caller cell

All quantum arithmetic writes belong to the original vent bank and every
exponent write belongs to its original retained result bank. Parent cells
outside those real addresses keep their full values on every actual record,
including arbitrary old Stores [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberPreserveCtx := context base noQuantum m ell width

variable {shape : CShape} (observed : CStorageRef (MemberPreserveCtx base noQuantum m ell width)
  shape)
  (vents : ∀ vent, (ventCell base noQuantum m ell width vent).key ≠ observed.key)

include vents

/-- A complete actual native stage writes no parent cell outside its vent and output addresses. -/
lemma stageRecord_read_other (modulus : BitVec width) (wide : 2 ≤ width) (inverse : Bool)
    {bits : Nat}
    (outputs : Fin bits → CWriteRef (MemberPreserveCtx base noQuantum m ell width) (.finite 2))
    (separate : ∀ index, (outputs index).key ≠ observed.key)
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)
    (store : Store (MemberPreserveCtx base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((MemberPreserveCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    (stageRecord base noQuantum m ell width modulus wide inverse outputs unit position store
      measured outcome).1.read (.storage observed) = store.read (.storage observed) := by
  change ((stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
    measured).1.write (finiteOutput (control_qubit base noQuantum m ell width)
      (outputs position)) (.finite outcome)).read (.storage observed) = _
  rw [finiteOutput_write, Store.read_write_other _ _ _ _ (separate position)]
  exact wordActualRecord_read_other (Physical.qubits width)
    (context_wires base noQuantum m ell width) (ventCell base noQuantum m ell width)
    observed vents _ store measured

/-- Every chronological actual suffix preserves the same separate caller value. -/
lemma exponentActualRecord_read_other (modulus : BitVec width) (wide : 2 ≤ width) {bits : Nat}
    (unit : (ZMod modulus.toNat)ˣ) (inverse : Bool)
    (outputs : Fin bits → CWriteRef (MemberPreserveCtx base noQuantum m ell width) (.finite 2))
    (separate : ∀ index, (outputs index).key ≠ observed.key)
    (remaining position : Nat) (bounded : position + remaining ≤ bits)
    (store : Store (MemberPreserveCtx base noQuantum m ell width))
    (outcomes : ExponentOutcomes base noQuantum m ell width modulus wide unit remaining position
      bounded) :
    (exponentActualRecord base noQuantum m ell width modulus wide unit inverse outputs remaining
      position bounded store outcomes).1.read (.storage observed) =
        store.read (.storage observed) := by
  induction remaining generalizing position store with
  | zero => rfl
  | succ remaining induction =>
      change (exponentActualRecord base noQuantum m ell width modulus wide unit inverse outputs
        remaining (position + 1) (by omega)
        (stageRecord base noQuantum m ell width modulus wide inverse outputs unit
          ⟨position, by omega⟩ store outcomes.1.1 outcomes.1.2).1 outcomes.2).1.read
            (.storage observed) = _
      exact (induction (position + 1) (by omega) _ outcomes.2).trans
        (stageRecord_read_other base noQuantum m ell width observed vents modulus wide inverse
          outputs separate unit ⟨position, by omega⟩ store outcomes.1.1 outcomes.1.2)

variable (results : ∀ result, (resultCell base noQuantum m ell width result).key ≠ observed.key)

include results

/-- Both actual exponent streams preserve every original separate parent storage reference. -/
lemma memberActualRecord_read_other (modulus : BitVec width) (wide : 2 ≤ width)
    (generator target : (ZMod modulus.toNat)ˣ)
    (store : Store (MemberPreserveCtx base noQuantum m ell width))
    (outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target) :
    (memberActualRecord base noQuantum m ell width modulus wide generator target store
      outcomes).1.read (.storage observed) = store.read (.storage observed) := by
  have first := exponentActualRecord_read_other base noQuantum m ell width observed vents modulus
    wide generator true (firstCell base noQuantum m ell width)
    (fun index => results (Fin.castAdd ell index)) (ell + m) 0 (by omega) store outcomes.1
  have second := exponentActualRecord_read_other base noQuantum m ell width observed vents modulus
    wide target⁻¹ true (secondCell base noQuantum m ell width)
    (fun index => results (Fin.natAdd (ell + m) index)) ell 0 (by omega)
    (exponentActualRecord base noQuantum m ell width modulus wide generator true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) store outcomes.1).1 outcomes.2
  exact second.trans first

omit vents in
/-- The independent chronological result-write Store preserves every separate caller cell. -/
lemma exponentOutputStore_read_other {bits : Nat} (selection : Fin bits → Fin (resultBits m ell))
    (remaining position : Nat) (bounded : position + remaining ≤ bits)
    (store : Store (MemberPreserveCtx base noQuantum m ell width))
    (readout : QuantumFourierTransform.Semiclassical.Bits remaining) :
    (exponentOutputStore base noQuantum m ell width selection remaining position bounded store
      readout).read (.storage observed) = store.read (.storage observed) := by
  induction remaining generalizing position store with
  | zero => rfl
  | succ remaining induction =>
      exact (induction (position + 1) (by omega) _ readout.2).trans
        (Store.read_write_other store _ observed _ (results (selection ⟨position, by omega⟩)))

omit vents in
/-- The canonical original result writes retain exactly the same parent values. -/
lemma memberReadoutStore_read_other
    (store : Store (MemberPreserveCtx base noQuantum m ell width))
    (readout : MemberReadouts m ell) :
    (memberReadoutStore base noQuantum m ell width store readout).read (.storage observed) =
      store.read (.storage observed) :=
  (exponentOutputStore_read_other base noQuantum m ell width observed results
    (fun index : Fin ell => Fin.natAdd (ell + m) index) ell 0 (by omega) _ readout.2).trans
    (exponentOutputStore_read_other base noQuantum m ell width observed results
      (fun index : Fin (ell + m) => Fin.castAdd ell index) (ell + m) 0 (by omega) store readout.1)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

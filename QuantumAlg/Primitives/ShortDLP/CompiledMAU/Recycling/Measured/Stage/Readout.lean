/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Record
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record.Readout

/-!
# Actual complete retained-output read after a measured stage

The new exponent bit overwrites its original addressed output cell. All
other retained bits are unchanged by the arithmetic vent bank. The statement
keeps every original output value and arbitrary old Store [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured EncodedBit.MeasuredUncompute
open MAU.Addition.Gidney.Measured.Instruction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ReadCtx := context base noQuantum m ell width

/-- The retained exponent positions name physically distinct original output cells. -/
lemma measuredResultCell_key_injective :
    Function.Injective (fun index => (resultCell base noQuantum m ell width index).key) := by
  intro first second same
  have indices : Fin.castAdd (width - 2) first = Fin.castAdd (width - 2) second :=
    cells_distinct base noQuantum m ell width same
  apply Fin.ext
  exact congrArg (fun index : Fin (resultBits m ell + (width - 2)) => index.val) indices

/-- Reading every retained result after a real output write changes exactly that position. -/
lemma measuredResultRead_write (store : Store (ReadCtx base noQuantum m ell width))
    (written : Fin (resultBits m ell)) (value : CShape.Value (.finite 2)) :
    (resultRead base noQuantum m ell width).eval
        (store.write (resultCell base noQuantum m ell width written) value) =
      CShape.Value.fixedVector (fun index => if index = written then value else
        store.read (.storage (resultCell base noQuantum m ell width index).toCStorageRef)) := by
  apply congrArg CShape.Value.fixedVector
  funext index
  by_cases selected : index = written
  · subst index
    rw [if_pos rfl]
    exact Store.read_write_same store _ value
  · rw [if_neg selected]
    exact Store.read_write_other store _ _ value (fun same =>
      selected ((measuredResultCell_key_injective base noQuantum m ell width same).symm))

variable (modulus : BitVec width) [NeZero modulus.toNat]

omit [NeZero modulus.toNat] in
/-- Dropping arithmetic paths still retains the new measured bit and every earlier result bit. -/
lemma stageRecord_resultRead (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (selection : Fin bits → Fin (resultBits m ell))
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)
    (store : Store (ReadCtx base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((ReadCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    (resultRead base noQuantum m ell width).eval
        (stageRecord base noQuantum m ell width modulus wide inverse
          (fun index => resultCell base noQuantum m ell width (selection index))
          unit position store measured outcome).1 =
      (resultRead base noQuantum m ell width).eval
        (store.write (resultCell base noQuantum m ell width (selection position))
          (.finite (placedOutcome (Physical.layout width).control (Physical.qubits width)
            (ReadCtx base noQuantum m ell width) (context_wires base noQuantum m ell width)
            outcome))) := by
  change (resultRead base noQuantum m ell width).eval
    ((stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
      measured).1.write
      (finiteOutput (control_qubit base noQuantum m ell width)
        (resultCell base noQuantum m ell width (selection position))) (.finite outcome)) = _
  rw [finiteOutput_write, measuredResultRead_write, measuredResultRead_write]
  apply congrArg CShape.Value.fixedVector
  funext index
  split_ifs
  · rfl
  · exact wordActualRecord_read_other (Physical.qubits width)
      (context_wires base noQuantum m ell width) (ventCell base noQuantum m ell width)
      (resultCell base noQuantum m ell width index).toCStorageRef
      (fun vent => vent_result_distinct base noQuantum m ell width vent index) _ store measured

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

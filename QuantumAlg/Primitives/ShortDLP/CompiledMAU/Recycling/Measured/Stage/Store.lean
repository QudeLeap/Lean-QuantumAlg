/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Readout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Feedback
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Projection

/-!
# Actual arithmetic histories preserve the complete retained-output Store

Agreement below concerns only the physically allocated retained result cells.
Actual vent writes and chronological paths remain unrestricted. The real next
feedback scalar depends only on these retained values [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured EncodedBit.MeasuredUncompute

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev StageStoreCtx := context base noQuantum m ell width

/-- Every retained result cell has its original full value in both actual Stores. -/
def ResultStoreAgree (first second : Store (StageStoreCtx base noQuantum m ell width)) : Prop :=
  ∀ index : Fin (resultBits m ell),
    first.read (.storage (resultCell base noQuantum m ell width index).toCStorageRef) =
      second.read (.storage (resultCell base noQuantum m ell width index).toCStorageRef)

/-- Equality of the whole actual output read retains equality at each original physical cell. -/
lemma measuredResultRead_eq_imp_read
    (first second : Store (StageStoreCtx base noQuantum m ell width))
    (same : (resultRead base noQuantum m ell width).eval first =
      (resultRead base noQuantum m ell width).eval second) :
    ResultStoreAgree base noQuantum m ell width first second := by
  have functions :
      (fun index => first.read
        (.storage (resultCell base noQuantum m ell width index).toCStorageRef)) =
      (fun index => second.read
        (.storage (resultCell base noQuantum m ell width index).toCStorageRef)) :=
    CShape.Value.fixedVector.inj same
  intro index
  exact congrFun functions index

/-- The same real result write preserves agreement at every retained physical address. -/
lemma resultStoreAgree_write (first second : Store (StageStoreCtx base noQuantum m ell width))
    (same : ResultStoreAgree base noQuantum m ell width first second)
    (written : Fin (resultBits m ell)) (value : CShape.Value (.finite 2)) :
    ResultStoreAgree base noQuantum m ell width
      (first.write (resultCell base noQuantum m ell width written) value)
      (second.write (resultCell base noQuantum m ell width written) value) := by
  intro index
  by_cases selected : index = written
  · subst index
    rw [Store.read_write_same, Store.read_write_same]
  · have different : (resultCell base noQuantum m ell width written).key ≠
        (resultCell base noQuantum m ell width index).key :=
      fun hit => selected ((measuredResultCell_key_injective base noQuantum m ell width hit).symm)
    rw [Store.read_write_other first _ _ value different,
      Store.read_write_other second _ _ value different]
    exact same index

/-- The finite source readout coordinate is that of exactly the same original physical qubit. -/
lemma placedOutcome_eq_exponentReadoutEquiv
    (outcome : Fin ((StageStoreCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    placedOutcome (Physical.layout width).control (Physical.qubits width)
        (StageStoreCtx base noQuantum m ell width) (context_wires base noQuantum m ell width)
        outcome = exponentReadoutEquiv base noQuantum m ell width outcome := rfl

variable (modulus : BitVec width)

/-- The actual stage extends exactly the same retained-output Store despite all real vent writes. -/
lemma stageRecord_resultStoreAgree (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (selection : Fin bits → Fin (resultBits m ell)) (unit : (ZMod modulus.toNat)ˣ)
    (position : Fin bits) (first second : Store (StageStoreCtx base noQuantum m ell width))
    (same : ResultStoreAgree base noQuantum m ell width first second)
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((StageStoreCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    ResultStoreAgree base noQuantum m ell width
      (stageRecord base noQuantum m ell width modulus wide inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) unit position first
        measured outcome).1
      (second.write (resultCell base noQuantum m ell width (selection position))
        (.finite (exponentReadoutEquiv base noQuantum m ell width outcome))) := by
  have actual := measuredResultRead_eq_imp_read base noQuantum m ell width _ _
    (stageRecord_resultRead base noQuantum m ell width modulus wide inverse selection unit position
      first measured outcome)
  rw [placedOutcome_eq_exponentReadoutEquiv] at actual
  intro index
  exact (actual index).trans
    (resultStoreAgree_write base noQuantum m ell width first second same (selection position)
      (.finite (exponentReadoutEquiv base noQuantum m ell width outcome)) index)

/-- Actual paid feedback agrees whenever the retained physical result values agree. -/
lemma feedbackScalar_resultStoreAgree (inverse : Bool) {bits : Nat}
    (selection : Fin bits → Fin (resultBits m ell)) (position : Fin bits)
    (first second : Store (StageStoreCtx base noQuantum m ell width))
    (same : ResultStoreAgree base noQuantum m ell width first second)
    (count : Nat) (bounded : count ≤ position.val) :
    feedbackScalar base noQuantum m ell width inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) position count
        bounded first =
      feedbackScalar base noQuantum m ell width inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) position count
        bounded second :=
  feedbackScalar_congr base noQuantum m ell width inverse _ position first second
    (fun index => same (selection index)) count bounded

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

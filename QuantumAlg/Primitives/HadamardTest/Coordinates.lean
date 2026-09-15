/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Preparation.Borrowed.Positions
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# The physical control and its actual classical outcome

The allocated control is the leading factor of the source's binary basis.
The actual Z write records exactly that factor in the retained result cell
[AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

open Execution

private theorem singleQubit_value
    (basis : (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout.register.Index) :
    ((OwnedQubitPrefix.prefixLayout 1).binaryIndexEquiv basis).val = (basis 0).val := by
  obtain ⟨label, rfl⟩ := (OwnedQubitPrefix.prefixLayout 1).binaryIndexEquiv.symm.surjective basis
  rw [Equiv.apply_symm_apply]
  fin_cases label <;> rfl

/-- The physical measurement wire is exactly the leading source qubit. -/
theorem controlWire_value (width : Nat) (basis : (post width).register.Index) :
    (basis (controlWire width)).val =
      ((prodEquiv (m := 1) (n := width)).symm (outputBasisEquiv width basis)).1.val := by
  obtain ⟨⟨fresh, original⟩, rfl⟩ := (OwnedQubitPrefix.assembly 1 width).surjective basis
  change ((OwnedQubitPrefix.assembly 1 width (fresh, original)) (controlWire width)).val =
    ((prodEquiv (m := 1) (n := width)).symm
      (OwnedQubitPrefix.basisEquiv 1 width
        (OwnedQubitPrefix.assembly 1 width (fresh, original)))).1.val
  rw [OwnedQubitPrefix.basisEquiv_assembly, Equiv.symm_apply_apply, singleQubit_value]
  exact ((pre width).addOwnedLayout_basis_value_preserved ⟨0⟩
    (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout
    (OwnedQubitPrefix.prefix_fresh 1 width) (OwnedQubitPrefix.prefix_disjoint 1 width) _
    (Fin.castAdd (pre width).systemCount (0 : Fin 1))).trans
      (QuantumLayout.appendJoinBasis_left_value _ _ _ fresh original 0)

private theorem transported_read_value {ctx : RuntimeCtx .quantum} {actual intended : ℕ+}
    (same : actual = intended) (ref : CWriteRef ctx (.finite intended)) (store : Store ctx) :
    (store.read (.storage
      (Eq.mpr (congrArg (fun dimension => CWriteRef ctx (.finite dimension)) same)
        ref).toCStorageRef)).toFin.val = (store.read (.storage ref.toCStorageRef)).toFin.val := by
  cases same
  rfl

private theorem readout_read_value (width : Nat) (store : Store (post width)) :
    (store.read (.storage (readout width).output.toCStorageRef)).toFin.val =
      (store.read (.storage (resultRef width).toCStorageRef)).toFin.val :=
  transported_read_value (controlWire_dimension width) _ store

/-- Reading the retained cell after its real Z write gives the exact source control outcome. -/
theorem measured_value (width : Nat) (store : Store (post width))
    (basis : (post width).register.Index) :
    (Circuit.writeMeasurementPath [readout width] store
      (Circuit.measurementBasisPath [readout width] basis)).read
        (.storage (resultRef width).toCStorageRef) =
      CShape.Value.finite (cardinality := 2)
        ((prodEquiv (m := 1) (n := width)).symm (outputBasisEquiv width basis)).1 := by
  have actual := Circuit.writeMeasurementBasis_read [readout width]
    (List.nodup_singleton _) (readout width) (List.mem_singleton_self _) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  change _ = (basis (controlWire width)).val at numeric
  rw [readout_read_value, controlWire_value] at numeric
  generalize valueEq : (Circuit.writeMeasurementPath [readout width] store
    (Circuit.measurementBasisPath [readout width] basis)).read
      (.storage (resultRef width).toCStorageRef) = value at numeric ⊢
  cases value with
  | finite result => exact congrArg CShape.Value.finite (Fin.ext numeric)

end

end QuantumAlg.HadamardTest

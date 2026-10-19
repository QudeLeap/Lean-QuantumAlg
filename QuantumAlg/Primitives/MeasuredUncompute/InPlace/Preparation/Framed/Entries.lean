/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation.Framed
import all QuantumAlg.Core.Execution.Context.Union.Preparation.Density

/-!
# Complete joint entries of actual framed arithmetic loading

The physical zero allocation and fixed X program retain every original word,
resident frame and external-reference coordinate. The existing full-state
frame theorem transports the established native loading equation back to the
actual union. The prepared density is only its mathematical specification.
-/

namespace QuantumAlg.MeasuredUncompute.InPlacePreparation.Framed

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution ContextUnion MAU.Inversion.SharedEEA

variable (modulus : Nat) (frame : RuntimeCtx .quantum)
  (separate : RuntimeCtx.StorageDisjoint (InversePreparation.after modulus.size) frame)
  {Reference : Register} {History : Type} [Fintype History]

/-- The real zero/X sequence establishes the fixed factor beside the complete incoming density. -/
lemma execute_preparedDensity
    (state : State ((InversePreparation.before modulus.size).disjointUnion frame
      (preparation_original_disjoint InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (InversePreparation.auxiliary_fresh modulus.size)
        (InversePreparation.auxiliary_disjoint modulus.size) separate))
      Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    ((circuit modulus frame separate).execute environment Reference state).quantumMarginal =
      preparedDensity InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (preparation_fresh_union InversePreparation.auxiliaryKey _
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size) separate)
        (preparation_wires_union InversePreparation.auxiliaryKey _
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size) separate)
        (InPlacePreparation.preparation modulus).normalized Reference state.quantumMarginal := by
  exact prepareFramed_execute_preparedDensity
    (ctx := InversePreparation.before modulus.size) (frame := frame)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (services := .empty)
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) separate environment
    (InPlacePreparation.loadProgram modulus) (InPlacePreparation.preparation modulus) state
    (InPlacePreparation.execute_preparedDensity (runtimeEnvironment := environment)
      (Reference := Register.prod frame.register Reference) (H := Store frame × History)
      modulus (splitServiceState (InversePreparation.before modulus.size) frame
        (preparation_original_disjoint InversePreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size) separate) state))

/-- Every joint matrix entry retains all old coherences and all resident frame correlations. -/
lemma execute_joined_entry
    (state : State ((InversePreparation.before modulus.size).disjointUnion frame
      (preparation_original_disjoint InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (InversePreparation.auxiliary_fresh modulus.size)
        (InversePreparation.auxiliary_disjoint modulus.size) separate))
      Reference (ClassicalOracleModel.empty.HiddenState × History))
    (newRow newColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod
      ((InversePreparation.before modulus.size).disjointUnion frame
        (preparation_original_disjoint InversePreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size) separate)).register
      Reference).Index) :
    ((circuit modulus frame separate).execute environment Reference state).quantumMarginal.matrix
      (preparedFramedBasisEquiv InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (InversePreparation.auxiliary_fresh modulus.size)
        (InversePreparation.auxiliary_disjoint modulus.size) separate (newRow, oldRow.1), oldRow.2)
      (preparedFramedBasisEquiv InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (InversePreparation.auxiliary_fresh modulus.size)
        (InversePreparation.auxiliary_disjoint modulus.size) separate
          (newColumn, oldColumn.1), oldColumn.2) =
      ((InPlacePreparation.preparation modulus).normalized.vec newRow *
        star ((InPlacePreparation.preparation modulus).normalized.vec newColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn := by
  rw [execute_preparedDensity]
  exact preparedDensity_joined_entry InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (preparation_fresh_union InversePreparation.auxiliaryKey _
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size) separate)
    (preparation_wires_union InversePreparation.auxiliaryKey _
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size) separate)
    (InPlacePreparation.preparation modulus).normalized state.quantumMarginal
    newRow newColumn oldRow oldColumn

end

end QuantumAlg.MeasuredUncompute.InPlacePreparation.Framed

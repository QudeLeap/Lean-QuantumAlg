/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation
import all QuantumAlg.Core.Execution.Context.Union.Preparation.State

/-!
# Actual fixed arithmetic preparation beside a resident frame

The original two input words and every supplied frame system stay present.
The auxiliary bank is allocated in zero and its nonzero fixed bits are loaded
by the same native X program used by the unframed preparation.
-/

namespace QuantumAlg.MeasuredUncompute.InPlacePreparation.Framed

noncomputable section

open Execution ContextUnion MAU.Inversion.SharedEEA

variable (modulus : Nat) (frame : RuntimeCtx .quantum)
  (separate : RuntimeCtx.StorageDisjoint
    (InversePreparation.after modulus.size) frame)

/-- The same concrete two-stage preparation, with the complete frame resident. -/
def circuit :
    Circuit (.quantum AlgorithmGate.model .empty)
      ((InversePreparation.before modulus.size).disjointUnion frame
        (preparation_original_disjoint InversePreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size) separate))
      ((InversePreparation.after modulus.size).disjointUnion frame separate) :=
  prepareFramed InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) separate
    (InPlacePreparation.loadProgram modulus)

/-- Zero allocation and every fixed-bit X gate are counted in this framed circuit. -/
theorem eventTrace (path : (circuit modulus frame separate).Path) :
    (circuit modulus frame separate).eventTrace path =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
        (InPlacePreparation.loadProgram modulus).eventTrace :=
  prepareFramed_eventTrace InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) separate
    (InPlacePreparation.loadProgram modulus) path

set_option maxHeartbeats 800000 in
-- Instantiating the general frame theorem reduces the full fixed auxiliary layout.
/-- The same complete joint state is prepared beside arbitrary resident systems. -/
theorem execute {Reference : Register} {History : Type} [Fintype History]
    (state : State
      ((InversePreparation.before modulus.size).disjointUnion frame
        (preparation_original_disjoint InversePreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size) separate))
      Reference (Unit × History)) :
    splitServiceState (InversePreparation.after modulus.size) frame separate
      ((circuit modulus frame separate).execute Reference state) =
      (((Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
            (operations := .empty) (classicalOracles := .empty)
            (InversePreparation.before modulus.size) InversePreparation.auxiliaryKey
            (InputPreparation.auxiliaryLayout modulus.size)
            (InversePreparation.auxiliary_fresh modulus.size)
            (InversePreparation.auxiliary_disjoint modulus.size)).seq
          (Circuit.unitary (operations := .empty) (classicalOracles := .empty)
            (InPlacePreparation.loadProgram modulus))).execute
        (Register.prod frame.register Reference)
        (splitServiceState (InversePreparation.before modulus.size) frame
          (preparation_original_disjoint InversePreparation.auxiliaryKey
            (InputPreparation.auxiliaryLayout modulus.size)
            (InversePreparation.auxiliary_fresh modulus.size)
            (InversePreparation.auxiliary_disjoint modulus.size) separate) state)).mapHistory
              (fun record =>
                (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) := by
  exact prepareFramed_execute
    (ctx := InversePreparation.before modulus.size) (frame := frame)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (services := .empty)
    InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) separate
    (InPlacePreparation.loadProgram modulus) state

end

end QuantumAlg.MeasuredUncompute.InPlacePreparation.Framed

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Reference
import all QuantumAlg.Components.Encoded.BitGates.IterationLaws

/-!
# Actual symbolic repetition of the complete scanned microstep

The loop count is a public circuit parameter. Internal trajectory
invariants justify the original action at each reached basis state;
they do not choose a circuit from the quantum input. The same actual
native word executes at every position and returns the complete pool.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

/-- Actual native repetition has the original iterated action on an internally clean trajectory. -/
lemma iterate_apply_source (width count : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (trajectory : ∀ index, index < count →
      ((SharedEEA.NativeMicrostep.step width)^[index] state.1).control = false) :
    (UnitaryCircuit.iterate count (program width enough)).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          ((SharedEEA.NativeMicrostep.step width)^[count] state.1, state.2))) := by
  let ket (value : Data width) := NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((encoding width).encode value))
  rw [UnitaryCircuit.iterate_applyNormalized]
  revert trajectory
  induction count with
  | zero =>
      intro _
      rfl
  | succ count ih =>
      intro trajectory
      rw [Function.iterate_succ_apply', ih (fun index within => trajectory index (by omega))]
      let current : Data width :=
        ((SharedEEA.NativeMicrostep.step width)^[count] state.1, state.2)
      have actual := program_apply_source width enough environment current prefixZero addressZero
        borrowZero (trajectory count (by omega))
      change (program width enough).applyNormalized environment (ket current) =
        ket (SharedEEA.NativeMicrostep.step width current.1, state.2) at actual
      exact actual.trans (congrArg (fun result => ket (result, state.2))
        (Function.iterate_succ_apply' (SharedEEA.NativeMicrostep.step width) count state.1).symm)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

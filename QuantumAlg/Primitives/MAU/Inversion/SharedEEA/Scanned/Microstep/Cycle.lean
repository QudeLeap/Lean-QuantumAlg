/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.History
import all QuantumAlg.Components.Encoded.BitGates.IterationLaws

/-!
# Actual static three-prefix and one-complete shared-EEA cycle

This emitted four-step word is independent of the input. Its generic
semantic helper exposes precisely the original-trajectory obligations
at the omitted positions. Concrete schedule endpoints must discharge
these obligations internally from the actual source-phase history.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

/-- Three actual seven-block prefixes and one actual complete eight-block microstep. -/
def cycleProgram (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (bodyProgram width enough).seq ((bodyProgram width enough).seq
    ((bodyProgram width enough).seq (program width enough)))

/-- The static cycle has the original four-step action and returns the same entire pool. -/
lemma cycleProgram_apply_source (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (trajectory : ∀ index, index < 4 →
      ((SharedEEA.NativeMicrostep.step width)^[index] state.1).control = false)
    (boundaryIdentity : ∀ index, index < 3 →
      SharedEEA.NativeMicrostep.step width
          ((SharedEEA.NativeMicrostep.step width)^[index] state.1) =
        bodyStep width ((SharedEEA.NativeMicrostep.step width)^[index] state.1)) :
    (cycleProgram width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          ((SharedEEA.NativeMicrostep.step width)^[4] state.1, state.2))) := by
  let ket (value : Data width) := NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((encoding width).encode value))
  have body (index : Nat) (before : index < 3) :
      (bodyProgram width enough).applyNormalized environment
          (ket ((SharedEEA.NativeMicrostep.step width)^[index] state.1, state.2)) =
        ket ((SharedEEA.NativeMicrostep.step width)^[index + 1] state.1, state.2) := by
    let current : Data width :=
      ((SharedEEA.NativeMicrostep.step width)^[index] state.1, state.2)
    have actual := bodyProgram_apply_source width enough environment current
      prefixZero addressZero borrowZero (trajectory index (by omega))
    have omitted := congrArg (fun result => ket (result, state.2))
      (boundaryIdentity index before).symm
    have next := congrArg (fun result => ket (result, state.2))
      (Function.iterate_succ_apply' (SharedEEA.NativeMicrostep.step width) index state.1).symm
    exact actual.trans (omitted.trans next)
  have last :
      (program width enough).applyNormalized environment
          (ket ((SharedEEA.NativeMicrostep.step width)^[3] state.1, state.2)) =
        ket ((SharedEEA.NativeMicrostep.step width)^[4] state.1, state.2) := by
    let current : Data width := ((SharedEEA.NativeMicrostep.step width)^[3] state.1, state.2)
    have actual := program_apply_source width enough environment current
      prefixZero addressZero borrowZero (trajectory 3 (by omega))
    exact actual.trans (congrArg (fun result => ket (result, state.2))
      (Function.iterate_succ_apply' (SharedEEA.NativeMicrostep.step width) 3 state.1).symm)
  have first : (bodyProgram width enough).applyNormalized environment (ket state) =
      ket ((SharedEEA.NativeMicrostep.step width)^[1] state.1, state.2) := by
    simpa only [Function.iterate_zero_apply] using body 0 (by omega)
  change (cycleProgram width enough).applyNormalized environment (ket state) = _
  rw [cycleProgram, UnitaryCircuit.applyNormalized_seq, first,
    UnitaryCircuit.applyNormalized_seq, body 1 (by omega),
    UnitaryCircuit.applyNormalized_seq, body 2 (by omega), last]

/-- Actual repetition of the same static cycle matches the full source orbit. -/
lemma iterate_cycle_apply_source (width count : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (trajectory : ∀ index, index < 4 * count →
      ((SharedEEA.NativeMicrostep.step width)^[index] state.1).control = false)
    (boundaryIdentity : ∀ index, index < 4 * count → (index + 1) % 4 ≠ 0 →
      SharedEEA.NativeMicrostep.step width
          ((SharedEEA.NativeMicrostep.step width)^[index] state.1) =
        bodyStep width ((SharedEEA.NativeMicrostep.step width)^[index] state.1)) :
    (UnitaryCircuit.iterate count (cycleProgram width enough)).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          ((SharedEEA.NativeMicrostep.step width)^[4 * count] state.1, state.2))) := by
  let ket (value : Data width) := NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((encoding width).encode value))
  rw [UnitaryCircuit.iterate_applyNormalized]
  revert trajectory boundaryIdentity
  induction count with
  | zero =>
      intro _ _
      rfl
  | succ count ih =>
      intro trajectory boundaryIdentity
      rw [Function.iterate_succ_apply', ih
        (fun index within => trajectory index (by omega))
        (fun index within nonfourth => boundaryIdentity index (by omega) nonfourth)]
      let current : Data width :=
        ((SharedEEA.NativeMicrostep.step width)^[4 * count] state.1, state.2)
      have shifted (index : Nat) :
          (SharedEEA.NativeMicrostep.step width)^[index] current.1 =
            (SharedEEA.NativeMicrostep.step width)^[index + 4 * count] state.1 :=
        (Function.iterate_add_apply (SharedEEA.NativeMicrostep.step width)
          index (4 * count) state.1).symm
      have actual := cycleProgram_apply_source width enough environment current
        prefixZero addressZero borrowZero
        (fun index within => by
          rw [shifted]
          exact trajectory (index + 4 * count) (by omega))
        (fun index within => by
          rw [shifted]
          exact boundaryIdentity (index + 4 * count) (by omega) (by omega))
      have endpoint : (SharedEEA.NativeMicrostep.step width)^[4] current.1 =
          (SharedEEA.NativeMicrostep.step width)^[4 * (count + 1)] state.1 := by
        rw [shifted, show 4 + 4 * count = 4 * (count + 1) by omega]
      exact actual.trans (congrArg (fun result => ket (result, state.2)) endpoint)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

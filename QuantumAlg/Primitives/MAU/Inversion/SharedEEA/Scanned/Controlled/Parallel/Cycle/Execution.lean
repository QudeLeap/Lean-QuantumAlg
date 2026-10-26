/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Body.Execution
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Cycle
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Cycle

/-!
# Direct original-source execution of the actual four-body cycle

Four independent mathematical bodies precede the complete unchanged
terminal boundary. This exact cycle action is stated for every original
finite source with the original pool/internal-control premises. Native
trajectory equations are used only to connect reached mathematical
states to the existing terminal number-theory result.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

/-- Independent source order of the same four bodies and complete boundary. -/
def cycleSource (width : Nat) (state : Registers width) : Registers width :=
  SharedEEA.TerminalBoundary.step
    (bodySource width (bodySource width (bodySource width (bodySource width state))))

private lemma cycleSource_eq (width : Nat) :
    cycleSource width = (fun source => SharedEEA.TerminalBoundary.step
      (bodySource width (bodySource width (bodySource width (bodySource width source))))) := rfl

def cycleStep (width : Nat) : ControlledFrame.Data width → ControlledFrame.Data width :=
  ControlledSource.step width (cycleSource width)

/-- The actual full cycle has its direct source action without a reached-trajectory premise. -/
lemma cycleProgram_apply_source (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false) :
    (cycleProgram width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (cycleStep width state))) := by
  let first := bodyStep width state
  let second := bodyStep width first
  let third := bodyStep width second
  let fourth := bodyStep width third
  have firstControl : first.1.1.control = false := bodyStep_control width state control
  have secondControl : second.1.1.control = false := bodyStep_control width first firstControl
  have thirdControl : third.1.1.control = false := bodyStep_control width second secondControl
  have fourthControl : fourth.1.1.control = false := bodyStep_control width third thirdControl
  have firstActual := bodyProgram_apply_source width enough environment state
    prefixZero addressZero borrowZero control
  have secondActual := bodyProgram_apply_source width enough environment first
    prefixZero addressZero borrowZero firstControl
  have thirdActual := bodyProgram_apply_source width enough environment second
    prefixZero addressZero borrowZero secondControl
  have fourthActual := bodyProgram_apply_source width enough environment third
    prefixZero addressZero borrowZero thirdControl
  have lastActual := ControlledBoundary.program_apply_encoded_ket width enough environment fourth
    prefixZero addressZero borrowZero fourthControl
  have actual := UnitaryCircuit.applyNormalized_seq_of_eq firstActual
    (UnitaryCircuit.applyNormalized_seq_of_eq secondActual
      (UnitaryCircuit.applyNormalized_seq_of_eq thirdActual
        (UnitaryCircuit.applyNormalized_seq_of_eq fourthActual lastActual)))
  change (cycleProgram width enough).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding width).encode
        (ControlledSource.step width SharedEEA.TerminalBoundary.step
          (bodyStep width (bodyStep width (bodyStep width (bodyStep width state))))))) at actual
  simpa only [cycleStep, cycleSource_eq, bodyStep, ControlledSource.step_step] using actual

/-- Arbitrary inactive finite sources retain all original source, pool and external systems. -/
lemma cycleProgram_apply_disabled (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false)
    (disabled : state.2.1 = false) :
    (cycleProgram width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state)) := by
  have actual := cycleProgram_apply_source width enough environment state
    prefixZero addressZero borrowZero control
  rw [cycleStep, ControlledSource.step_disabled width _ state disabled] at actual
  exact actual

private lemma cycleSource_eq_native_iterate (width : Nat) (state : Registers width)
    (trajectory : ∀ index, index < 4 →
      ((SharedEEA.NativeMicrostep.step width)^[index] state).control = false)
    (boundaryIdentity : ∀ index, index < 3 →
      SharedEEA.NativeMicrostep.step width
          ((SharedEEA.NativeMicrostep.step width)^[index] state) =
        NativeMicrostep.bodyStep width ((SharedEEA.NativeMicrostep.step width)^[index] state)) :
    cycleSource width state = (SharedEEA.NativeMicrostep.step width)^[4] state := by
  have body (index : Nat) (within : index < 3) :
      bodySource width ((SharedEEA.NativeMicrostep.step width)^[index] state) =
        (SharedEEA.NativeMicrostep.step width)^[index + 1] state :=
    (bodySource_eq_native width _ (trajectory index (by omega))).trans
      ((boundaryIdentity index within).symm.trans
        (Function.iterate_succ_apply' (SharedEEA.NativeMicrostep.step width) index state).symm)
  have first : bodySource width state = (SharedEEA.NativeMicrostep.step width)^[1] state :=
    body 0 (by omega)
  unfold cycleSource
  rw [first, body 1 (by omega), body 2 (by omega),
    bodySource_eq_native width _ (trajectory 3 (by omega))]
  exact (NativeMicrostep.source_step_eq_boundary width _).symm.trans
    (Function.iterate_succ_apply' (SharedEEA.NativeMicrostep.step width) 3 state).symm

private lemma cycleProgram_apply_active (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (selected : state.2.1 = true)
    (trajectory : ∀ index, index < 4 →
      ((SharedEEA.NativeMicrostep.step width)^[index] state.1.1).control = false)
    (boundaryIdentity : ∀ index, index < 3 →
      SharedEEA.NativeMicrostep.step width
          ((SharedEEA.NativeMicrostep.step width)^[index] state.1.1) =
        NativeMicrostep.bodyStep width ((SharedEEA.NativeMicrostep.step width)^[index] state.1.1)) :
    (cycleProgram width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode
          (((SharedEEA.NativeMicrostep.step width)^[4] state.1.1, state.1.2), state.2))) := by
  have actual := cycleProgram_apply_source width enough environment state
    prefixZero addressZero borrowZero (trajectory 0 (by omega))
  have orbit := cycleSource_eq_native_iterate width state.1.1 trajectory boundaryIdentity
  simpa only [cycleStep, ControlledSource.step, selected, if_true, orbit] using actual

/-- Repetition is symbolic in the public count and retains the same complete original trajectory. -/
private lemma iterate_cycle_apply_active (width count : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (selected : state.2.1 = true)
    (trajectory : ∀ index, index < 4 * count →
      ((SharedEEA.NativeMicrostep.step width)^[index] state.1.1).control = false)
    (boundaryIdentity : ∀ index, index < 4 * count → (index + 1) % 4 ≠ 0 →
      SharedEEA.NativeMicrostep.step width
          ((SharedEEA.NativeMicrostep.step width)^[index] state.1.1) =
        NativeMicrostep.bodyStep width ((SharedEEA.NativeMicrostep.step width)^[index] state.1.1)) :
    (UnitaryCircuit.iterate count (cycleProgram width enough)).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode
          (((SharedEEA.NativeMicrostep.step width)^[4 * count] state.1.1,
            state.1.2), state.2))) := by
  let ket (source : Registers width) :=
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding width).encode ((source, state.1.2), state.2)))
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
      let current : ControlledFrame.Data width :=
        (((SharedEEA.NativeMicrostep.step width)^[4 * count] state.1.1, state.1.2), state.2)
      have shifted (index : Nat) :
          (SharedEEA.NativeMicrostep.step width)^[index] current.1.1 =
            (SharedEEA.NativeMicrostep.step width)^[index + 4 * count] state.1.1 :=
        (Function.iterate_add_apply (SharedEEA.NativeMicrostep.step width)
          index (4 * count) state.1.1).symm
      have actual := cycleProgram_apply_active width enough environment current
        prefixZero addressZero borrowZero selected
        (fun index within => by
          rw [shifted]
          exact trajectory (index + 4 * count) (by omega))
        (fun index within => by
          rw [shifted]
          exact boundaryIdentity (index + 4 * count) (by omega) (by omega))
      have endpoint : (SharedEEA.NativeMicrostep.step width)^[4] current.1.1 =
          (SharedEEA.NativeMicrostep.step width)^[4 * (count + 1)] state.1.1 := by
        rw [shifted, show 4 + 4 * count = 4 * (count + 1) by omega]
      exact actual.trans (congrArg ket endpoint)

/-- The same public symbolic repetition is identity on an inactive arbitrary original source. -/
private lemma iterate_cycle_apply_disabled (width count : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false)
    (disabled : state.2.1 = false) :
    (UnitaryCircuit.iterate count (cycleProgram width enough)).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state)) := by
  have one := cycleProgram_apply_disabled width enough environment state
    prefixZero addressZero borrowZero control disabled
  rw [UnitaryCircuit.iterate_applyNormalized]
  induction count with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply', ih, one]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

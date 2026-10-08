/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.WorkspaceReuse
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Forward.Gates
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Trace
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# The actual forward EEA and its adjoint on reused arithmetic words

The forward program acts on the original X/A shared frame and retains
the complete existing Y word. Its identical adjoint is then placed with
reset Y in the old A role, retaining the computed result in A and every
small history coordinate [LYL+26, sec_point_add/sec_point_add.tex:51-79].

The exact admitted-input equations include all fields and amplitudes.
Their source states are the original prime-domain EEA results; the
surrounding measured arithmetic must establish these states from its
actual product, Hadamard, Z-write and selected reset operations.
-/

namespace QuantumAlg.MeasuredUncompute.NativeEEAFrame

noncomputable section

open ProductPlacement MAU.Inversion SharedEEA EncodedBit GateSpec

/-- Place every real shared-forward instruction before the existing arbitrary numerator word. -/
def forwardGates (modulus : Nat) (prime : Nat.Prime modulus) :
    List (GateSpec (frameEncoding modulus.size)) :=
  (InPlaceForward.gates modulus prime.one_lt).map
    (GateSpec.prodLeft (BinaryLabelEncoding.finIdentity modulus.size))

/-- The full native forward retains the arbitrary complementary word on all source labels. -/
theorem nativeEEAFrame_forwardGates_step (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    stepList (forwardGates modulus prime) state =
      (InPlaceForward.step modulus state.1, state.2) := by
  erw [forwardGates, stepList_prodLeft, InPlaceForward.inPlaceForward_gates_step]

-- Generic list realization does not evaluate the complete recursive arithmetic generator.
attribute [local irreducible] forwardGates

private def forwardBody (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix modulus.size (InPlaceForward.nativeProgram modulus prime.one_lt)

/-- The actual forward keeps the existing numerator word in the complete live frame. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (forwardGates modulus prime)

/-- The emitted full forward has exact phases for every original frame and numerator value. -/
theorem nativeEEAFrame_forward_realizes (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit.Realizes (frameEncoding modulus.size) (forward modulus prime)
      (fun state => (InPlaceForward.step modulus state.1, state.2)) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (nativeEEAFrame_forwardGates_step modulus prime)

private theorem forwardBody_realizes (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit.Realizes (frameEncoding modulus.size) (forwardBody modulus prime)
      (fun state => (InPlaceForward.step modulus state.1, state.2)) :=
  (InPlaceForward.inPlaceForward_nativeProgram_realizes modulus prime.one_lt).onBinaryPrefix

private theorem forward_basis (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    (forward modulus prime).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
        ((frameEncoding modulus.size).encode state))) =
    (forwardBody modulus prime).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
        ((frameEncoding modulus.size).encode state))) :=
  ((nativeEEAFrame_forward_realizes modulus prime).apply_encoded_ket state).trans
    ((forwardBody_realizes modulus prime).apply_encoded_ket state).symm

theorem forward_physical (modulus : Nat) (_prime : Nat.Prime modulus) :
    (QubitLayout.canonical (frameEncoding modulus.size).width).systemIdx =
      List.range (frameEncoding modulus.size).width :=
  QubitLayout.canonical_systemIdx _

/-- Every original input amplitude retains its complete numerator while EEA produces the inverse. -/
theorem forward_initial (modulus : Nat) (prime : Nat.Prime modulus)
    (input numerator : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (forward modulus prime).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            (InitialPortProgram.inputFrame modulus input, numerator)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            (InPlaceForward.result modulus input.val positive bounded, numerator))) := by
  rw [forward_basis]
  have coprime := (Nat.coprime_of_lt_prime (Nat.ne_of_gt positive) bounded prime).symm
  exact UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (SharedEEA.encoding modulus.size) (BinaryLabelEncoding.finIdentity modulus.size)
    (InPlaceForward.nativeProgram modulus prime.one_lt) _ _ numerator
    (InPlaceForward.inPlaceForward_nativeProgram_initial modulus prime.one_lt input coprime
      positive bounded)

private theorem reverse_realizes {Data : Type} {source : BinaryLabelEncoding Data}
    (instructions : List (GateSpec source))
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical source.width).toQuantum)
    (realizes : UnitaryCircuit.Realizes source body (stepList instructions)) :
    UnitaryCircuit.Realizes source (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty))
      (stepList instructions.reverse) where
  apply_encoded_ket := by
    intro state
    have cancel : stepList instructions (stepList instructions.reverse state) = state := by
      simpa only [List.reverse_reverse] using stepList_reverse_stepList instructions.reverse state
    have actual := realizes.apply_encoded_ket (stepList instructions.reverse state)
    rw [cancel] at actual
    exact (congrArg (fun vector =>
      (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized vector)
        actual).symm.trans
        (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized body
          (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty))
          (by rw [UnitaryCircuit.dagger_matrix]; exact Unitary.star_eq_inv _) _)

/-- Each reversed primitive is physically placed by the complete workspace-reuse bijection. -/
def backwardGates (modulus : Nat) (prime : Nat.Prime modulus) :
    List (GateSpec (frameEncoding modulus.size)) :=
  (forwardGates modulus prime).reverse.map (WorkspaceReuse.placement modulus.size).placeGate

/-- Exact reverse action through the original full physical grouping. -/
def backwardStep (modulus : Nat) (prime : Nat.Prime modulus) :
    Frame modulus.size → Frame modulus.size :=
  (WorkspaceReuse.placement modulus.size).step (stepList (forwardGates modulus prime).reverse)

/-- Literal placed reversal retains every original dirty label without an auxiliary hypothesis. -/
theorem nativeEEAFrame_backwardGates_step (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    stepList (backwardGates modulus prime) state = backwardStep modulus prime state :=
  (WorkspaceReuse.placement modulus.size).placeGates_step _ state

private def backwardBody (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  (WorkspaceReuse.placement modulus.size).place
    ((forward modulus prime).dagger (AlgorithmGate.oracleFreeAdjoints .empty))

/-- Execute the actual reversed native word on the same full reused workspace. -/
def backward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (backwardGates modulus prime)

attribute [local irreducible] backwardGates

/-- Complete phases and all frame coordinates agree with the physically placed reverse action. -/
theorem nativeEEAFrame_backward_realizes (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit.Realizes (frameEncoding modulus.size) (backward modulus prime)
      (backwardStep modulus prime) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (nativeEEAFrame_backwardGates_step modulus prime)

private theorem backwardBody_realizes (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit.Realizes (frameEncoding modulus.size) (backwardBody modulus prime)
      (backwardStep modulus prime) :=
  (WorkspaceReuse.placement modulus.size).place_realizes
    (reverse_realizes (forwardGates modulus prime) (forward modulus prime)
      (realizesList (QubitLayout.canonical _) .empty _))

/-- Every complete basis label has the exact phase of the original placed adjoint. -/
theorem nativeEEAFrame_backward_basis (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    (backward modulus prime).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
        ((frameEncoding modulus.size).encode state))) =
    (backwardBody modulus prime).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
        ((frameEncoding modulus.size).encode state))) :=
  ((nativeEEAFrame_backward_realizes modulus prime).apply_encoded_ket state).trans
    ((backwardBody_realizes modulus prime).apply_encoded_ket state).symm

/-- The full placed backward restores an arbitrary incoming frame after the matching forward. -/
theorem nativeEEAFrame_backward_restores (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    stepList (backwardGates modulus prime)
      ((WorkspaceReuse.placement modulus.size).grouping.symm
        (stepList (forwardGates modulus prime) state)) =
      (WorkspaceReuse.placement modulus.size).grouping.symm state := by
  rw [nativeEEAFrame_backwardGates_step]
  unfold backwardStep FullPlacement.step
  rw [Equiv.apply_symm_apply, stepList_reverse_stepList]

/-- Reversal retains the arbitrary saved word in the source coordinates of the reused frame. -/
theorem nativeEEAFrame_backward_saved (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    ((WorkspaceReuse.placement modulus.size).grouping
      (stepList (backwardGates modulus prime) state)).2 =
    ((WorkspaceReuse.placement modulus.size).grouping state).2 := by
  rw [nativeEEAFrame_backwardGates_step]
  unfold backwardStep FullPlacement.step
  rw [Equiv.apply_symm_apply]
  erw [forwardGates, ← List.map_reverse, stepList_prodLeft]

/-- Exact adjoint recovery on the original prime domain includes all saved data and history. -/
theorem backward_result (modulus : Nat) (prime : Nat.Prime modulus)
    (input saved : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (backward modulus prime).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            ((WorkspaceReuse.placement modulus.size).grouping.symm
              (InPlaceForward.result modulus input.val positive bounded, saved))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            ((WorkspaceReuse.placement modulus.size).grouping.symm
              (InitialPortProgram.inputFrame modulus input, saved)))) := by
  rw [nativeEEAFrame_backward_basis]
  unfold backwardBody
  apply (WorkspaceReuse.placement modulus.size).place_ket_of_eq
  have actual := forward_initial modulus prime input saved positive bounded
  let inverse := (forward modulus prime).dagger (AlgorithmGate.oracleFreeAdjoints .empty)
  have inverse_eq : inverse.matrix = (forward modulus prime).matrix⁻¹ := by
    change ((forward modulus prime).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).matrix = _
    rw [UnitaryCircuit.dagger_matrix]
    exact Unitary.star_eq_inv _
  exact (congrArg inverse.applyNormalized actual).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (forward modulus prime) inverse inverse_eq _)

/-- Workspace reuse retains exactly the same original full physical frame. -/
theorem backward_physical (modulus : Nat) (_prime : Nat.Prime modulus) :
    (QubitLayout.canonical (frameEncoding modulus.size).width).systemIdx =
      List.range (frameEncoding modulus.size).width :=
  QubitLayout.canonical_systemIdx _

/-- The placed forward keeps the actual original event word, without an added permutation gate. -/
theorem nativeEEAFrame_forward_trace (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).eventTrace =
      (InPlaceForward.nativeProgram modulus prime.one_lt).eventTrace := by
  erw [forward, programList_eventTrace, forwardGates, map_event_prodLeft,
    InPlaceForward.nativeProgram, programList_eventTrace]

/-- The actual inverse events are precisely the reverse of this same forward program. -/
theorem backward_trace (modulus : Nat) (prime : Nat.Prime modulus) :
    (backward modulus prime).eventTrace =
      ((forward modulus prime).dagger (AlgorithmGate.oracleFreeAdjoints .empty)).eventTrace := by
  rw [backward, programList_eventTrace, backwardGates]
  simp only [List.map_map, Function.comp_def, FullPlacement.placeGate_event]
  rw [List.map_reverse, AlgorithmGate.oracleFreeAdjoints_eventTrace,
    forward, programList_eventTrace]

end

end QuantumAlg.MeasuredUncompute.NativeEEAFrame

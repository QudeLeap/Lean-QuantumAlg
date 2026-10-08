/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Native.EEAFrame
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources

/-!
# Actual forward inversion using the reset Y workspace

Measured multiplication first saves X*Y in A and resets Y. The same
shared EEA must therefore run on X with Y in the large-workspace role.
Its exact native program is the adjoint of the already placed reused
backward program; no new arithmetic oracle or physical permutation is
introduced [LYL+26, sec_point_add/sec_point_add.tex:32-36,119-122].

Only the preserved denominator X is inverted. The saved product can be
zero, and every bit of its value and the small EEA history is retained.
-/

namespace QuantumAlg.MeasuredUncompute.NativeReusedEEA

noncomputable section

open ProductPlacement MAU.Inversion.SharedEEA EncodedBit GateSpec

/-- Reverse every actually placed backward instruction on the same complete physical frame. -/
def forwardGates (modulus : Nat) (prime : Nat.Prime modulus) :
    List (GateSpec (frameEncoding modulus.size)) :=
  (NativeEEAFrame.backwardGates modulus prime).reverse

/-- The reversed reused word consists of the original forward gates at the same actual placement. -/
theorem nativeReusedEEA_forwardGates_placed (modulus : Nat) (prime : Nat.Prime modulus) :
    forwardGates modulus prime = (NativeEEAFrame.forwardGates modulus prime).map
      (WorkspaceReuse.placement modulus.size).placeGate := by
  rw [forwardGates, NativeEEAFrame.backwardGates, ← List.map_reverse, List.reverse_reverse]

/-- The source-forward action is transported through the complete existing workspace bijection. -/
def step (modulus : Nat) : Frame modulus.size → Frame modulus.size :=
  (WorkspaceReuse.placement modulus.size).step
    (fun state => (InPlaceForward.step modulus state.1, state.2))

/-- Every original dirty state and saved target follows the same complete placed forward action. -/
theorem nativeReusedEEA_forwardGates_step (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    stepList (forwardGates modulus prime) state = step modulus state := by
  rw [nativeReusedEEA_forwardGates_placed, FullPlacement.placeGates_step]
  unfold FullPlacement.step
  rw [NativeEEAFrame.nativeEEAFrame_forwardGates_step]
  rfl

private def forwardBody (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  (NativeEEAFrame.backward modulus prime).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

/-- Execute every literal instruction of the same complete reused forward program. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (forwardGates modulus prime)

attribute [local irreducible] forwardGates

/-- The reused emitted list preserves exact phases on every complete input label. -/
theorem nativeReusedEEA_forward_realizes (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit.Realizes (frameEncoding modulus.size) (forward modulus prime) (step modulus) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (nativeReusedEEA_forwardGates_step modulus prime)

private theorem forwardBody_realizes (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit.Realizes (frameEncoding modulus.size) (forwardBody modulus prime)
      (step modulus) :=
  (NativeEEAFrame.reverse_realizes (NativeEEAFrame.backwardGates modulus prime)
    (NativeEEAFrame.backward modulus prime)
    (realizesList (QubitLayout.canonical _) .empty _)).congrStep (fun state => by
      simpa only [forwardGates] using nativeReusedEEA_forwardGates_step modulus prime state)

/-- The emitted reused forward equals the original full adjoint on every encoded basis label. -/
theorem nativeReusedEEA_forward_basis (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    (forward modulus prime).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
        ((frameEncoding modulus.size).encode state))) =
    (forwardBody modulus prime).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
        ((frameEncoding modulus.size).encode state))) :=
  ((nativeReusedEEA_forward_realizes modulus prime).apply_encoded_ket state).trans
    ((forwardBody_realizes modulus prime).apply_encoded_ket state).symm

/-- The whole arbitrary dirty frame is restored after a matching backward/forward pair. -/
theorem nativeReusedEEA_forward_backward_restores (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    stepList (forwardGates modulus prime)
      (stepList (NativeEEAFrame.backwardGates modulus prime) state) = state := by
  rw [forwardGates]
  exact stepList_reverse_stepList _ _

/-- The arbitrary saved target is unchanged in the original coordinates of the reused frame. -/
theorem nativeReusedEEA_forward_saved (modulus : Nat) (prime : Nat.Prime modulus)
    (state : Frame modulus.size) :
    ((WorkspaceReuse.placement modulus.size).grouping
      (stepList (forwardGates modulus prime) state)).2 =
    ((WorkspaceReuse.placement modulus.size).grouping state).2 := by
  rw [nativeReusedEEA_forwardGates_step]
  simp only [step, FullPlacement.step, Equiv.apply_symm_apply]

/-- The actual reused forward inverts X and retains every saved A bit, including saved zero. -/
theorem forward_initial (modulus : Nat) (prime : Nat.Prime modulus)
    (input saved : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (forward modulus prime).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode
              ((WorkspaceReuse.placement modulus.size).grouping.symm
                (InitialPortProgram.inputFrame modulus input, saved))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            ((WorkspaceReuse.placement modulus.size).grouping.symm
              (InPlaceForward.result modulus input.val positive bounded, saved)))) := by
  rw [nativeReusedEEA_forward_basis]
  have backward := NativeEEAFrame.backward_result modulus prime input saved positive bounded
  let inverse := forwardBody modulus prime
  have inverse_eq : inverse.matrix = (NativeEEAFrame.backward modulus prime).matrix⁻¹ := by
    change ((NativeEEAFrame.backward modulus prime).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).matrix = _
    rw [UnitaryCircuit.dagger_matrix]
    exact Unitary.star_eq_inv _
  exact (congrArg inverse.applyNormalized backward).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (NativeEEAFrame.backward modulus prime) inverse inverse_eq _)

/-- The reused forward acts on exactly the same existing full frame. -/
theorem forward_physical (modulus : Nat) (_prime : Nat.Prime modulus) :
    (QubitLayout.canonical (frameEncoding modulus.size).width).systemIdx =
      List.range (frameEncoding modulus.size).width :=
  QubitLayout.canonical_systemIdx _

/-- Reversing the complete reused backward trace restores every original forward event. -/
theorem forward_trace (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).eventTrace =
      ((NativeEEAFrame.backward modulus prime).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).eventTrace := by
  rw [forward, programList_eventTrace, forwardGates, List.map_reverse,
    AlgorithmGate.oracleFreeAdjoints_eventTrace, NativeEEAFrame.backward, programList_eventTrace]

/-- Both opposite reused passes carry the identical full native multiplicity ledger. -/
theorem forward_cost (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).eventCost =
      (NativeEEAFrame.backward modulus prime).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, forward_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost]
  change Multiset.map (AlgorithmGate.oracleFreeEvent .empty) _ = _
  have eventId : AlgorithmGate.oracleFreeEvent .empty = id := by
    funext event
    cases event with
    | classicalOperation impossible => cases impossible
    | classicalQuery impossible => cases impossible
    | oracle impossible => cases impossible
    | gate _ => rfl
    | preparation _ => rfl
    | measurement _ => rfl
  rw [eventId, Multiset.map_id]

end

end QuantumAlg.MeasuredUncompute.NativeReusedEEA

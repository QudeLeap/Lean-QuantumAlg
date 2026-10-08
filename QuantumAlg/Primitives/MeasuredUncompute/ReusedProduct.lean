/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.WorkspaceReuse
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Ports
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Frame
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Selection

/-!
# Actual product recomputation into the reset measurement word

After the inverse EEA has used Y as its large workspace, the original
X and the computed result in A reproduce the measured word in Y.
The same native product is placed on X/A/Y, followed by the selected
literal Z gates on Y and the identical product adjoint. Every retained
field is part of the complete basis action
[LYL+26, sec_point_add/sec_point_add.tex:85-105].
-/

namespace QuantumAlg.MeasuredUncompute.ReusedProduct

noncomputable section

open ProductPlacement MAU.Multiplication EncodedBit.Word

/-- Execute the same actual product with A as its second input and reset Y as its target. -/
def compute (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding width).width).toQuantum :=
  (WorkspaceReuse.placement width).place (NativeProductFrame.program width modulus)

/-- Complete arithmetic action through the identical physical workspace permutation. -/
def computeStep (width : Nat) (modulus : Fin (2 ^ width + 1)) : Frame width → Frame width :=
  (WorkspaceReuse.placement width).step (NativeProductFrame.step width modulus)

/-- Exact full-label action of the actual X/A/Y product. -/
theorem reusedProduct_realizes (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (frameEncoding width) (compute width modulus)
      (computeStep width modulus) :=
  (WorkspaceReuse.placement width).place_realizes
    (NativeProductFrame.nativeProductFrame_realizes width modulus)

/-- The recomputed Y word is read in the measurement mask's little-endian bit order. -/
def measuredWord (width : Nat) : EncodedBit.Word (frameEncoding width) width :=
  ⟨fun index => (FramePorts.numerator width).bit index.rev⟩

theorem measuredWord_read (width : Nat) (index : Fin width) (state : Frame width) :
    ((measuredWord width).bit index).get state = state.2.val.testBit index.val := by
  rw [measuredWord, FramePorts.numerator_read, Fin.rev_rev]

/-- Recompute Y, apply its actual selected Z sequence, and reverse that same recomputation. -/
def correction (width : Nat) (modulus : Fin (2 ^ width + 1)) (mask : Fin width → Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding width).width).toQuantum :=
  Recompute.program (QubitLayout.canonical _) (compute width modulus)
    (measuredWord width) mask

/-- The complete original label is restored with precisely the recomputed Y character. -/
theorem correction_ket (width : Nat) (modulus : Fin (2 ^ width + 1))
    (outcome : Fin (2 ^ width)) (state : Frame width) :
    (correction width modulus (fun index => outcome.val.testBit index.val)).applyVec
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
          ((frameEncoding width).encode state))).vec =
      WalshHadamard.walshSign outcome (computeStep width modulus state).2 •
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
            ((frameEncoding width).encode state))).vec := by
  rw [correction, Recompute.recompute_phase_ket (QubitLayout.canonical _) _
    (reusedProduct_realizes width modulus)]
  exact congrArg (fun phase : ℂ => phase •
    (NormalizedVector.ket
      ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
        ((frameEncoding width).encode state))).vec)
    (measuredCorrection_sign_walsh (measuredWord width) _ _ outcome
      (fun index => measuredWord_read width index _))

/-- Every reference column receives the same exact phase while all local history is restored. -/
theorem correction_reference (width : Nat) (modulus : Fin (2 ^ width + 1))
    (outcome : Fin (2 ^ width)) (state : Frame width) {Reference : Register}
    (row : (QubitLayout.canonical (frameEncoding width).width).toQuantum.register.Index)
    (left right : Reference.Index) :
    UnitaryOperator.prodTensor
      (correction width modulus (fun index => outcome.val.testBit index.val)).matrix
      (1 : UnitaryOperator Reference)
      (row, left)
      ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
        ((frameEncoding width).encode state), right) =
      if row = (QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
          ((frameEncoding width).encode state) ∧ left = right then
        WalshHadamard.walshSign outcome (computeStep width modulus state).2 else 0 := by
  rw [correction, Recompute.recompute_reference_entry (QubitLayout.canonical _) _
    (reusedProduct_realizes width modulus)]
  rw [measuredCorrection_sign_walsh (measuredWord width) _ _ outcome
    (fun index => measuredWord_read width index _)]

/-- Reusing the physical ports keeps every original product event in its original order. -/
theorem compute_trace (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (compute width modulus).eventTrace = (VariableGidney.program width modulus).eventTrace := by
  rw [compute, EncodedBit.FullPlacement.place_eventTrace,
    NativeProductFrame.nativeProductFrame_trace]

/-- The actual reused product meets the original independent native coordinate budget. -/
theorem compute_budget (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (compute width modulus).eventCost ≤ VariableGidney.nativeBudget width := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, compute_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  exact VariableGidney.variableGidney_native_budget width modulus

/-- Both actual product passes and the selected Z gates fit the independently stated allowance. -/
theorem correction_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (correction width modulus mask).eventCost ≤ NativeProductCorrection.nativeBudget width := by
  have phase : (PhaseCorrection.program (QubitLayout.canonical _) .empty
      (measuredWord width) mask).eventCost ≤
      width • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) := by
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, PhaseCorrection.program,
      PhaseCorrection.phaseCorrection_sequence_trace, ResourcePool.ofList_replicate]
    apply ResourcePool.le_iff_count.mpr
    intro event
    rw [ResourcePool.count_scale, ResourcePool.count_nsmul]
    exact Nat.mul_le_mul_right _ (PhaseCorrection.phaseCorrection_selected_count_le mask)
  unfold correction Recompute.program NativeProductCorrection.nativeBudget
  rw [UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost]
  have inverseCost : (AlgorithmGate.oracleFreePool .empty)
      (compute width modulus).eventCost = (compute width modulus).eventCost := by
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
  rw [inverseCost]
  exact add_le_add (compute_budget width modulus) (add_le_add phase (compute_budget width modulus))

end

end QuantumAlg.MeasuredUncompute.ReusedProduct

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.WorkspaceReuse
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Placement
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

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

open ProductPlacement MAU.Inversion SharedEEA

private def forwardBody (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit (Qubits (frameEncoding modulus.size).width) :=
  UnitaryCircuit.prodLeft (n := modulus.size) (InPlaceForward.program modulus prime.one_lt)

private theorem forwardBody_within (modulus : Nat) (prime : Nat.Prime modulus) :
    (forwardBody modulus prime).physical_idx ⊆ List.range (frameEncoding modulus.size).width :=
  UnitaryCircuit.prodLeft_physical_idx_subset_range _
    (InPlacePlacement.program_within modulus prime.one_lt)

/-- The actual forward keeps the existing numerator word in the complete live frame. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit (Qubits (frameEncoding modulus.size).width) :=
  (forwardBody modulus prime).seq
    (.identity _ (List.range (frameEncoding modulus.size).width) List.nodup_range)

theorem forward_physical (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).physical_idx = List.range (frameEncoding modulus.size).width :=
  (forwardBody_within modulus prime).union_eq_right

/-- Every original input amplitude retains its complete numerator while EEA produces the inverse. -/
theorem forward_initial (modulus : Nat) (prime : Nat.Prime modulus)
    (input numerator : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (forward modulus prime).applyNormalized
      (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          (InitialPortProgram.inputFrame modulus input, numerator))) =
      NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          (InPlaceForward.result modulus input.val positive bounded, numerator)) := by
  rw [forward, UnitaryCircuit.applyNormalized_seq, UnitaryCircuit.applyNormalized_identity]
  have coprime := (Nat.coprime_of_lt_prime (Nat.ne_of_gt positive) bounded prime).symm
  exact UnitaryCircuit.Realizes.prodLeft_applyNormalized_encoded_ket_of_eq
    (SharedEEA.encoding modulus.size) (BinaryLabelEncoding.finIdentity modulus.size)
    (InPlaceForward.program modulus prime.one_lt) _ _ numerator
    (InPlaceForward.program_initial modulus prime.one_lt input coprime positive bounded)

private theorem reverse_within (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).dagger.physical_idx ⊆
      List.range (frameEncoding modulus.size).width := by
  rw [UnitaryCircuit.dagger_physical_idx, forward_physical]
  exact List.Subset.refl _

/-- The identical complete adjoint runs on reset Y as workspace and preserves the saved A word. -/
def backward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit (Qubits (frameEncoding modulus.size).width) :=
  (WorkspaceReuse.placement modulus.size).place (forward modulus prime).dagger
    (reverse_within modulus prime)

/-- Exact adjoint recovery on the original prime domain includes all saved data and history. -/
theorem backward_result (modulus : Nat) (prime : Nat.Prime modulus)
    (input saved : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (backward modulus prime).applyNormalized
      (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          ((WorkspaceReuse.placement modulus.size).grouping.symm
            (InPlaceForward.result modulus input.val positive bounded, saved)))) =
      NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          ((WorkspaceReuse.placement modulus.size).grouping.symm
            (InitialPortProgram.inputFrame modulus input, saved))) := by
  unfold backward
  apply EncodedBit.FullPlacement.place_ket_of_eq
  have actual := forward_initial modulus prime input saved positive bounded
  exact (congrArg (forward modulus prime).dagger.applyNormalized actual).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized (forward modulus prime) _)

/-- Workspace reuse retains exactly the same original full physical frame. -/
theorem backward_physical (modulus : Nat) (prime : Nat.Prime modulus) :
    (backward modulus prime).physical_idx = List.range (frameEncoding modulus.size).width :=
  EncodedBit.FullPlacement.place_physical _ _ _

/-- The actual inverse events are precisely the reverse of this same forward program. -/
theorem backward_trace (modulus : Nat) (prime : Nat.Prime modulus) :
    (backward modulus prime).eventTrace = (forward modulus prime).eventTrace.reverse := by
  rw [backward, EncodedBit.FullPlacement.place_eventTrace, UnitaryCircuit.dagger_eventTrace]

end

end QuantumAlg.MeasuredUncompute.NativeEEAFrame

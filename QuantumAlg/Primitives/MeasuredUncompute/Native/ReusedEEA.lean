/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Native.EEAFrame

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

open ProductPlacement MAU.Inversion.SharedEEA

/-- Run the literal adjoint of the identical reused backward gate program. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit (Qubits (frameEncoding modulus.size).width) :=
  (NativeEEAFrame.backward modulus prime).dagger

/-- The actual reused forward inverts X and retains every saved A bit, including saved zero. -/
theorem forward_initial (modulus : Nat) (prime : Nat.Prime modulus)
    (input saved : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (forward modulus prime).applyNormalized
        (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
          ((frameEncoding modulus.size).encode
            ((WorkspaceReuse.placement modulus.size).grouping.symm
              (InitialPortProgram.inputFrame modulus input, saved)))) =
      NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          ((WorkspaceReuse.placement modulus.size).grouping.symm
            (InPlaceForward.result modulus input.val positive bounded, saved))) := by
  have backward := NativeEEAFrame.backward_result modulus prime input saved positive bounded
  have reversed := congrArg (NativeEEAFrame.backward modulus prime).dagger.applyNormalized backward
  exact reversed.symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (NativeEEAFrame.backward modulus prime) _)

/-- The reused forward acts on exactly the same existing full frame. -/
theorem forward_physical (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).physical_idx = List.range (frameEncoding modulus.size).width := by
  rw [forward, UnitaryCircuit.dagger_physical_idx, NativeEEAFrame.backward_physical]

/-- Reversing the complete reused backward trace restores every original forward event. -/
theorem forward_trace (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).eventTrace = (NativeEEAFrame.forward modulus prime).eventTrace := by
  rw [forward, UnitaryCircuit.dagger_eventTrace, NativeEEAFrame.backward_trace,
    List.reverse_reverse]

/-- Both opposite reused passes carry the identical full native multiplicity ledger. -/
theorem forward_cost (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).eventCost = (NativeEEAFrame.backward modulus prime).eventCost :=
  UnitaryCircuit.dagger_eventCost _

end

end QuantumAlg.MeasuredUncompute.NativeReusedEEA

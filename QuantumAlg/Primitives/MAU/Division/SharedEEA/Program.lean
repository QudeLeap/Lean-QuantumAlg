/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Layout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Program
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

/-!
# Actual compute, division accumulation, and full shared-EEA uncomputation

The existing corrected forward produces the inverse in Work2. The actual
variable Gidney product accumulator adds inverse times numerator into the
separate target and preserves the complete computed frame and numerator.
The adjoint of the very same forward then restores all history. There is
no inverse copy or extra word.
-/

namespace QuantumAlg.MAU.Division.SharedEEA

noncomputable section

open Inversion.SharedEEA
open Multiplication

private def middleBody (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (sourceEncoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (historyWidth width) (VariableGidney.program width modulus)

/-- Actual variable-product MAC at the inverse, numerator, and independent target ports. -/
def middleProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding width).width).toQuantum :=
  (placement width).place (middleBody width modulus)

/-- All-label arithmetic preserves every original shared-EEA field and numerator exactly. -/
def middleStep (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width) : Frame width :=
  (state.1, state.2.1,
    (VariableGidney.prefixOutput modulus width
      (OutputCopy.value state.1, state.2.1, state.2.2)).2.2)

private theorem middle_grouping (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width) :
    (placement width).step (fun value =>
      (VariableGidney.prefixOutput modulus width value.1, value.2)) state =
        middleStep width modulus state := by
  apply (placement width).grouping.injective
  rw [EncodedBit.FullPlacement.step, Equiv.apply_symm_apply]
  apply Prod.ext
  · apply Prod.ext
    · change ((placement width).grouping state).1.1 = _
      rw [divisionGrouping_source, divisionGrouping_source]
      rfl
    · apply Prod.ext
      · change ((placement width).grouping state).1.2.1 = _
        rw [divisionGrouping_numerator, divisionGrouping_numerator]
        rfl
      · rw [divisionGrouping_target]
        change (VariableGidney.prefixOutput modulus width
          ((placement width).grouping state).1).2.2 = _
        have words : ((placement width).grouping state).1 =
            (OutputCopy.value state.1, state.2.1, state.2.2) :=
          Prod.ext (divisionGrouping_source width state)
            (Prod.ext (divisionGrouping_numerator width state)
              (divisionGrouping_target width state))
        rw [words]
        rfl
  · exact divisionGrouping_history width state.1 state.2.1 state.2.2 _

/-- Full-frame basis equality for the actual placed MAC, including arbitrary history and target. -/
theorem divisionMiddle_realizes (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (frameEncoding width) (middleProgram width modulus)
      (middleStep width modulus) :=
  ((placement width).place_realizes
    (UnitaryCircuit.Realizes.onBinaryPrefix
      (right := BinaryLabelEncoding.finIdentity (historyWidth width))
      (VariableGidney.variableGidney_realizes width modulus))).congrStep
        (middle_grouping width modulus)

/-- Canonical targets receive the complete inverse-port value times the unchanged numerator. -/
theorem divisionMiddle_target (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width) (valid : state.2.2.val < modulus.val) :
    (middleStep width modulus state).2.2.val =
      (state.2.2.val + (OutputCopy.value state.1).val * state.2.1.val) % modulus.val :=
  (VariableGidney.variableGidney_valid width modulus
    (OutputCopy.value state.1, state.2.1, state.2.2) valid).2.2

/-- The full corrected forward runs beside both independent live words. -/
def forwardProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  UnitaryCircuit.prodLeft (n := modulus.size + modulus.size)
    (CorrectedSchedule.program modulus nontrivial)

/-- Execute the actual forward, actual modular accumulator, and the same complete adjoint. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  (forwardProgram modulus nontrivial).seq
    ((middleProgram modulus.size (Inversion.SharedEEA.Accumulate.fittedModulus modulus)).seq
      ((forwardProgram modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)))

end

end QuantumAlg.MAU.Division.SharedEEA

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Layout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.CorrectedSchedule
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

/-!
# Actual compute, modular addition, and full shared-EEA uncomputation

The existing corrected forward produces the inverse in Work2. The actual
coefficient-one Gidney accumulator adds that word into the separate target
and preserves the complete computed frame. The adjoint of the very same
forward then restores all history. There is no inverse copy or extra word.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Accumulate

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Multiplication.Accumulate

private def middleBody (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (sourceEncoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (historyWidth width) (Gidney.program width modulus 1)

/-- Actual coefficient-one MAC at the inverse and independent target ports. -/
def middleProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding width).width).toQuantum :=
  (placement width).place (middleBody width modulus)

/-- All-label arithmetic preserves every original shared-EEA field exactly. -/
def middleStep (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width) : Frame width :=
  (state.1, (Gidney.prefixOutput modulus 1 width (OutputCopy.value state.1, state.2)).2)

private lemma middle_grouping (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width) :
    (placement width).step (fun value =>
      (Gidney.prefixOutput modulus 1 width value.1, value.2)) state =
        middleStep width modulus state := by
  apply (placement width).grouping.injective
  rw [EncodedBit.FullPlacement.step, Equiv.apply_symm_apply]
  apply Prod.ext
  · apply Prod.ext
    · change ((placement width).grouping state).1.1 = _
      rw [accumulateGrouping_source, accumulateGrouping_source]
      rfl
    · rw [accumulateGrouping_target]
      change (Gidney.prefixOutput modulus 1 width ((placement width).grouping state).1).2 = _
      have words : ((placement width).grouping state).1 =
          (OutputCopy.value state.1, state.2) :=
        Prod.ext (accumulateGrouping_source width state) (accumulateGrouping_target width state)
      rw [words]
      rfl
  · exact accumulateGrouping_history width state.1 state.2 _

/-- Full-frame basis equality for the actual placed MAC, including arbitrary history and target. -/
lemma accumulateMiddle_realizes (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (frameEncoding width) (middleProgram width modulus) environment
      (middleStep width modulus) :=
  ((placement width).place_realizes
    (UnitaryCircuit.Realizes.onBinaryPrefix
      (right := BinaryLabelEncoding.finIdentity (historyWidth width))
      (Gidney.gidneyAccumulate_realizes width modulus 1))).congrStep
        (middle_grouping width modulus)

/-- Every canonical target receives modular addition of the complete physical source read. -/
lemma accumulateMiddle_target (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width) (valid : state.2.val < modulus.val) :
    (middleStep width modulus state).2.val =
      (state.2.val + (OutputCopy.value state.1).val) % modulus.val := by
  simpa only [middleStep, one_mul] using
    Gidney.gidneyAccumulate_valid width modulus 1 (OutputCopy.value state.1, state.2) valid

/-- Noncanonical target labels are fixed by the same actual all-label binary extension. -/
lemma accumulateMiddle_outside (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width) (outside : modulus.val ≤ state.2.val) :
    middleStep width modulus state = state := by
  have actual := Gidney.gidneyAccumulate_outside width modulus 1
    (OutputCopy.value state.1, state.2) outside
  apply Prod.ext
  · rfl
  · exact congrArg (fun value : Gidney.Registers width => value.2) actual

/-- Fit the original modulus at its canonical input width without a caller fit assumption. -/
def fittedModulus (modulus : Nat) : Fin (2 ^ modulus.size + 1) :=
  ⟨modulus, (Nat.lt_size_self modulus).trans_le (Nat.le_succ _)⟩

/-- The full corrected forward runs beside the independent live target. -/
def forwardProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  UnitaryCircuit.prodLeft (n := modulus.size) (CorrectedSchedule.program modulus nontrivial)

/-- Execute the actual forward, actual modular accumulator, and the same complete adjoint. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum :=
  (forwardProgram modulus nontrivial).seq
    ((middleProgram modulus.size (fittedModulus modulus)).seq
      ((forwardProgram modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Accumulate

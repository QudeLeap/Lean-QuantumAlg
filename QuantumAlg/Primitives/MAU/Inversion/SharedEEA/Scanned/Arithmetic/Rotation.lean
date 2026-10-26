/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Preservation
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Resources

/-!
# Real metadata-controlled permutations of the original work words

The chosen work word retains every original bit. Each fixed displacement is
lowered to a linear-size Fredkin word, controlled by an actual metadata wire
outside both work words. No address or prefix storage is consumed. The exact
wire permutation and all complement readouts are retained for subsequent
window alignment and its actual unitary inverse.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticRotation

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Both choices address only the original work-word systems. -/
def bit (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    EncodedBit (encoding width) :=
  sourceBit width (if first then SharedEEA.firstWordBit width index
    else SharedEEA.secondWordBit width index)

private lemma bit_value (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (bit width first index).wire.val = (if first then 0 else width + 3) + index.val := by
  cases first with
  | false => rfl
  | true =>
      change index.val = 0 + index.val
      omega

/-- An unchanged source metadata position controls one unchanged work-word carrier. -/
def frame (width : Nat) (first : Bool) (control : EncodedBit (SharedEEA.encoding width))
    (afterWords : 2 * (width + 3) ≤ control.wire.val) :
    PermutationFrame (encoding width) (width + 3) where
  control := sourceBit width control
  bit := bit width first
  distinct := by
    intro left right same
    apply Fin.ext
    have values := congrArg Fin.val same
    rw [bit_value, bit_value] at values
    omega
  separate := by
    intro index same
    have values := congrArg Fin.val same
    rw [sourceBit_wire, bit_value] at values
    have within := index.isLt
    cases first <;> simp only [Bool.false_eq_true, if_false, if_true] at values <;> omega

/-- Static displacement selects only a public finite wire permutation. -/
def permutation (width displacement : Nat) : Equiv.Perm (Fin (width + 3)) :=
  finRotate (width + 3) ^ displacement

/-- Compile actual Fredkin instructions without allocating from the shared pool. -/
def program (width : Nat) (first : Bool) (control : EncodedBit (SharedEEA.encoding width))
    (afterWords : 2 * (width + 3) ≤ control.wire.val) (displacement : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty
    ((frame width first control afterWords).gates
      (Permutation.transpositions (permutation width displacement)))

/-- Every output work bit comes from the exact selected original physical position. -/
lemma program_bit_get (width : Nat) (first : Bool)
    (control : EncodedBit (SharedEEA.encoding width))
    (afterWords : 2 * (width + 3) ≤ control.wire.val) (displacement : Nat)
    (index : Fin (width + 3)) (state : Data width) :
    (bit width first index).get
      (GateSpec.stepList ((frame width first control afterWords).gates
        (Permutation.transpositions (permutation width displacement))) state) =
      if control.get state.1 then
        (bit width first (permutation width displacement index)).get state
      else (bit width first index).get state :=
  (frame width first control afterWords).fixed_permutation_get _ index state

/-- Every original metadata and pool coordinate outside that word remains unchanged. -/
lemma program_get_outside (width : Nat) (first : Bool)
    (control : EncodedBit (SharedEEA.encoding width))
    (afterWords : 2 * (width + 3) ≤ control.wire.val) (displacement : Nat)
    (observed : EncodedBit (encoding width))
    (outside : ∀ index, (bit width first index).wire ≠ observed.wire) (state : Data width) :
    observed.get (GateSpec.stepList ((frame width first control afterWords).gates
      (Permutation.transpositions (permutation width displacement))) state) =
        observed.get state :=
  (frame width first control afterWords).gates_get_outside _ observed outside state

/-- The same real rotation charges its Toffolis, CNOTs and common-control duration. -/
lemma program_resources (width : Nat) (first : Bool)
    (control : EncodedBit (SharedEEA.encoding width))
    (afterWords : 2 * (width + 3) ≤ control.wire.val) (displacement : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program width first control afterWords displacement).eventCost ≤ width + 3 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program width first control afterWords displacement).eventCost
        ≤ 2 * (width + 3) ∧
      (program width first control afterWords displacement).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 3 * (width + 3) :=
  (frame width first control afterWords).fixed_resources _ .empty _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticRotation

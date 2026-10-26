/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Registers.BitExt

/-!
# The existing scan prefix word as an actual address-addition operand

The prefix is an arbitrary preserved addend on all labels. At the later
clean scan boundary its least significant position holds the paid phase
correction, so this same native adder supplies zero or one. No controlled
borrowed increment or additional quantum workspace is required.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.PrefixAddition

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- All original prefix positions, in the same most-significant-first order. -/
def source (width : Nat) : Word (encoding width) (ScanMetadata.addressWidth width) :=
  ⟨prefixBit width⟩

/-- All complete address positions retain the carry bit. -/
def target (width : Nat) : Word (encoding width) (ScanMetadata.addressWidth width) :=
  ⟨addressBit width⟩

/-- Two actual nonoverlapping existing pool words supply the complete native placement. -/
def placement (width : Nat) : Addition.TTK.WordPlacement (encoding width)
    (ScanMetadata.addressWidth width) where
  addend := source width
  target := target width
  addendDistinct := by
    intro left right same
    by_contra different
    exact prefix_prefix_ne width left right different same
  targetDistinct := by
    intro left right same
    by_contra different
    exact address_address_ne width left right different same
  separate := fun left right => (address_prefix_ne width right left).symm
  onto := encoding_surjective width

/-- The paid parallel TTK program uses the existing prefix and address, with no allocation. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement width).program

/-- Exact whole-frame semantics derived from the native operand placement. -/
def step (width : Nat) (state : Data width) : Data width :=
  (placement width).step state

private lemma step_observed (width : Nat) (state : Data width)
    (bit : EncodedBit (encoding width))
    (outside : ∀ index, (addressBit width index).wire ≠ bit.wire) :
    bit.get (step width state) = bit.get state :=
  (placement width).step_get_of_target_ne state bit outside

/-- The entire complete source frame is retained, including the phase used by preparation. -/
lemma step_source (width : Nat) (state : Data width) :
    (step width state).1 = state.1 := by
  apply Registers.eq_of_bit_get_eq
  intro bit
  exact step_observed width state (sourceBit width bit)
    (fun index => (source_address_ne width bit index).symm)

/-- The existing prefix addend is completely restored, even on dirty labels. -/
lemma step_prefix (width : Nat) (state : Data width) :
    (step width state).2.2.1 = state.2.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  simpa only [prefixBit_get] using
    step_observed width state (prefixBit width ⟨index, within⟩)
      (fun other => address_prefix_ne width other ⟨index, within⟩)

/-- The separate conjunction is outside both actual operand words. -/
lemma step_conjunction (width : Nat) (state : Data width) :
    (step width state).2.2.2 = state.2.2.2 :=
  step_observed width state (conjunctionBit width) (address_conjunction_ne width)

/-- The complete existing prefix is added into the complete existing address. -/
lemma step_address (width : Nat) (state : Data width) :
    (step width state).2.1 = state.2.2.1 + state.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := (placement width).step_target_get state state.2.2.1 state.2.1
    (fun index => prefixBit_get width index state)
    (fun index => addressBit_get width index state) ⟨index, within⟩
  change (addressBit width ⟨index, within⟩).get (step width state) = _ at actual
  simpa only [addressBit_get] using actual

/-- The complete coherent action changes only the address, on all finite labels. -/
lemma step_eq (width : Nat) (state : Data width) :
    step width state = (state.1, (state.2.2.1 + state.2.1, state.2.2)) :=
  Prod.ext (step_source width state)
    (Prod.ext (step_address width state)
      (Prod.ext (step_prefix width state) (step_conjunction width state)))

/-- Actual native gates implement this exact source-and-workspace-preserving addition. -/
lemma program_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment
      (fun state => (state.1, (state.2.2.1 + state.2.1, state.2.2))) :=
  ((placement width).program_realizes environment).congrStep (step_eq width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.PrefixAddition

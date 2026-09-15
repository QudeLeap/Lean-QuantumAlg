/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources

/-!
# The actual internally borrowed accumulation stage

For word width `extra + 3`, the source supplies the leading selector, the
`extra` untouched coordinates, and the two arbitrary bits required by the
modular offset. The remaining word is the target. Coherent control of the
actual offset preserves every source field exactly on both branches.
This intermediate layout contains exactly the two original words; later
placement identifies its fields with the selected source coordinates.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open Nat.FixedWidth

/-- Selector, untouched source coordinates, borrowed flag, target, borrowed helper. -/
abbrev CanonicalRegisters (extra : Nat) :=
  Bool × (Fin (2 ^ extra) × Addition.Gidney.Registers (extra + 3))

def canonicalEncoding (extra : Nat) : BinaryLabelEncoding (CanonicalRegisters extra) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity extra)
      (Addition.Gidney.encoding (extra + 3)))

/-- The three source roles and all untouched coordinates retain their initial values. -/
def canonicalOutput {extra : Nat} (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) (state : CanonicalRegisters extra) :
    CanonicalRegisters extra :=
  (state.1, (state.2.1, (state.2.2.1,
    (if state.1 then modularWordOutput modulus constant state.2.2.2.1 else state.2.2.2.1,
      state.2.2.2.2))))

/-- The existing target-and-borrowed circuit is carried past the untouched source coordinates. -/
def canonicalBody (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit (Qubits (extra + (Addition.Gidney.encoding (extra + 3)).width)) :=
  UnitaryCircuit.prodRight (m := extra)
    (Addition.Gidney.modularOffsetProgram (extra + 3) modulus constant)

/-- Actual coherent control of the shared borrowed-bit modular offset. -/
def canonicalProgram (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit (Qubits (canonicalEncoding extra).width) :=
  UnitaryCircuit.controlLeading (canonicalBody extra modulus constant)

/-- Exact joint-basis semantics includes arbitrary initial values of both borrowed source bits. -/
theorem gidneyCanonicalStage_realizes (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (canonicalEncoding extra)
      (canonicalProgram extra modulus constant) (canonicalOutput modulus constant) := by
  have hbody := (Addition.Gidney.gidneyModularOffset_realizes
    (extra + 3) modulus constant).prodRight (left := BinaryLabelEncoding.finIdentity extra)
  have hshift : UnitaryCircuit.Realizes
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity extra)
        (Addition.Gidney.encoding (extra + 3)))
      (UnitaryCircuit.shiftPhysicalIdx 1 (canonicalBody extra modulus constant))
      (fun state => (state.1, Addition.Gidney.modularOffsetOutput modulus constant state.2)) := by
    refine ⟨?_⟩
    intro state
    rw [UnitaryCircuit.shiftPhysicalIdx_applyNormalized]
    exact hbody.apply_encoded_ket state
  apply (hshift.controlOnTrue [0]
    (UnitaryCircuit.leadingControlLayout (canonicalBody extra modulus constant))).congrStep
  rintro ⟨selected, unused, flag, target, helper⟩
  cases selected <;> rfl

/-- The actual circuit stays within the same two words. -/
theorem gidneyCanonicalStage_physical_range (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).physical_idx ⊆ List.range (2 * (extra + 3)) := by
  have hoffset : (Addition.Gidney.modularOffsetProgram
      (extra + 3) modulus constant).physical_idx ⊆
        List.range (Addition.Gidney.encoding (extra + 3)).width := by
    rw [Addition.Gidney.gidneyModularOffset_physical]
    have hwidth : (Addition.Gidney.encoding (extra + 3)).width = extra + 3 + 2 := by
      change 1 + ((extra + 3) + 1) = extra + 3 + 2
      omega
    rw [hwidth]
    exact fun _ h => h
  have hbody := UnitaryCircuit.prodRight_physical_idx_subset_range (m := extra)
    (Addition.Gidney.modularOffsetProgram (extra + 3) modulus constant) hoffset
  have h := UnitaryCircuit.controlLeading_physical_idx_subset_range
    (canonicalBody extra modulus constant) hbody
  have hwidth : 1 + (extra + (Addition.Gidney.encoding (extra + 3)).width) =
      2 * (extra + 3) := by
    change 1 + (extra + (1 + ((extra + 3) + 1))) = 2 * (extra + 3)
    omega
  unfold canonicalProgram
  simpa only [hwidth] using h

/-- The native ledger is exactly one coherent-control transform of the executed offset ledger. -/
theorem gidneyCanonicalStage_eventCost (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).eventCost =
      ResourcePool.controlForDimension 2
        (Addition.Gidney.modularOffsetProgram (extra + 3) modulus constant).eventCost := by
  exact (UnitaryCircuit.controlLeading_eventCost (canonicalBody extra modulus constant)).trans
    (congrArg (ResourcePool.controlForDimension 2)
      (UnitaryCircuit.prodRight_eventCost (m := extra)
        (Addition.Gidney.modularOffsetProgram (extra + 3) modulus constant)))

theorem gidneyCanonicalStage_event_count (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).eventCost.card =
      (Addition.Gidney.modularOffsetProgram (extra + 3) modulus constant).eventCost.card := by
  rw [gidneyCanonicalStage_eventCost]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions, Multiset.card_map]

theorem gidneyCanonicalStage_event_count_bound (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).eventCost.card ≤
      Addition.Gidney.modularOffsetEventBound (extra + 3) := by
  rw [gidneyCanonicalStage_event_count]
  exact Addition.Gidney.gidneyModularOffset_event_count_bound (extra + 3) modulus constant

theorem gidneyCanonicalStage_qubit_count (extra : Nat) :
    (canonicalEncoding extra).width = 2 * (extra + 3) := by
  change 1 + (extra + (1 + ((extra + 3) + 1))) = 2 * (extra + 3)
  omega

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney

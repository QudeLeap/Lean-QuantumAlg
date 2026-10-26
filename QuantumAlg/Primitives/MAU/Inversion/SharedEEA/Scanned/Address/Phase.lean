/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Paid preparation of the phase-two address correction

Two X gates and one CNOT XOR the complement of the retained Phase1 into the
least significant prefix position. The source phase is restored. On the
true clean-prefix boundary this prepares the exact zero-or-one TTK addend.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressPhase

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The original phase bit remains in the complete source frame. -/
def phase (width : Nat) : EncodedBit (encoding width) :=
  sourceBit width (phase1Bit width)

/-- The actual least significant prefix position, valid also at zero source width. -/
def work (width : Nat) : EncodedBit (encoding width) :=
  prefixBit width ⟨ScanMetadata.addressWidth width - 1, by
    unfold ScanMetadata.addressWidth
    omega⟩

private lemma separate (width : Nat) : (phase width).wire ≠ (work width).wire :=
  source_prefix_ne width _ _

/-- Literal native negative-control preparation; no predicate is evaluated for free. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  [.x (phase width), .cnot (phase width) (work width) (separate width), .x (phase width)]

/-- XOR only the selected least significant prefix bit when Phase1 is false. -/
def step (width : Nat) (state : Data width) : Data width :=
  if (phase width).get state then state else (work width).flip state

/-- The same complete phase, source data and all other pool fields are retained. -/
lemma gates_step (width : Nat) (state : Data width) :
    GateSpec.stepList (gates width) state = step width state := by
  change (phase width).flip
    (cnotStep (phase width) (work width) ((phase width).flip state)) = _
  unfold cnotStep
  rw [get_flip_self]
  cases chosen : (phase width).get state <;>
    simp [step, chosen, EncodedBit.flip_comm, EncodedBit.flip_flip]

private lemma work_prefix (width : Nat) (state : Data width) :
    ((work width).flip state).2.2.1 = state.2.2.1 ^^^ 1#(ScanMetadata.addressWidth width) := by
  apply BitVec.eq_of_toNat_eq
  change state.2.2.1.toNat ^^^
    2 ^ (ScanMetadata.addressWidth width - 1 - (ScanMetadata.addressWidth width - 1)) = _
  have one : 1 < 2 ^ ScanMetadata.addressWidth width :=
    Nat.one_lt_two_pow (by unfold ScanMetadata.addressWidth; omega)
  rw [Nat.sub_self, Nat.pow_zero, BitVec.toNat_xor, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt one]

/-- Exact dirty-prefix action of the three actual preparation gates. -/
lemma step_eq (width : Nat) (state : Data width) :
    step width state =
      (state.1, (state.2.1, (if state.1.flags.first then state.2.2.1
        else state.2.2.1 ^^^ 1#(ScanMetadata.addressWidth width), state.2.2.2))) := by
  unfold step
  change (if state.1.flags.first then state else (work width).flip state) = _
  split
  · rfl
  · exact Prod.ext rfl (Prod.ext rfl (Prod.ext (work_prefix width state) rfl))

/-- At the actual clean boundary the prefix word holds precisely the required phase correction. -/
lemma step_prefix_clean (width : Nat) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (step width state).2.2.1 =
      if state.1.flags.first then 0#(ScanMetadata.addressWidth width)
      else 1#(ScanMetadata.addressWidth width) := by
  rw [step_eq]
  simp only [clean, BitVec.zero_xor]

/-- The paid preparation is self inverse, including arbitrary dirty prefix contents. -/
lemma step_step (width : Nat) (state : Data width) :
    step width (step width state) = state := by
  by_cases chosen : (phase width).get state
  · simp only [step, chosen, if_true]
  · have preserved := get_flip_of_wire_ne (work width) (phase width) (separate width).symm state
    simp only [step, chosen, Bool.false_eq_true, if_false, preserved, EncodedBit.flip_flip]

/-- The three native gates run on the unchanged full source-plus-pool frame. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width)

/-- Full coherent semantics retain all phase and reference correlations. -/
lemma program_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment (step width) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _ (gates_step width) environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressPhase

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Payload.Assembly
import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Resources
import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Execution.Specification

/-!
# Actual division input, numerator, arbitrary target, and supplied flag

All three source data words and the original flag are supplied owned systems.
The unchanged source auxiliary preparation is separate. Binary reassociation
preserves the numerical label and every native wire identity; no physical
permutation or uncharged external field is introduced.
-/

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionLayout

noncomputable section

open Execution Inversion.SharedEEA

/-- Both modular payload words and the supplied flag remain actual owned quantum bits. -/
def payloadWidth (width : Nat) : Nat := (width + width) + 1

/-- Actual supplied denominator, numerator, arbitrary target, and original live flag. -/
abbrev before (width : Nat) := PayloadPreparation.before width (payloadWidth width)

/-- Every supplied and prepared system remains in the actual output context. -/
abbrev after (width : Nat) := PayloadPreparation.after width (payloadWidth width)

/-- Pack numerator, target, and flag in their original big-endian physical order. -/
def payloadEquiv (width : Nat) :
    ((Fin (2 ^ width) × Fin (2 ^ width)) × Bool) ≃ Fin (2 ^ payloadWidth width) :=
  (Equiv.prodCongr (prodEquiv (m := width) (n := width)) finTwoEquiv.symm).trans
    (prodEquiv (m := width + width) (n := 1))

/-- The flag's mathematical zero/one label matches its actual binary physical encoding. -/
theorem divisionPayload_encode (width : Nat)
    (value : (Fin (2 ^ width) × Fin (2 ^ width)) × Bool) :
    payloadEquiv width value =
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
          (BinaryLabelEncoding.finIdentity width)) BinaryLabelEncoding.bool).encode value := by
  rcases value with ⟨⟨numerator, target⟩, flag⟩
  cases flag <;> rfl

/-- Read every original data field through the actual supplied wire identities. -/
def inputBasisEquiv (width : Nat) :
    (before width).register.Index ≃ ExecutionSpecification.Labels width :=
  (PayloadPreparation.inputBasisEquiv width (payloadWidth width)).trans
    (Equiv.prodCongr (Equiv.refl _) (payloadEquiv width).symm)

/-- Repacking all decoded payload fields recovers the original supplied binary word exactly. -/
theorem divisionPayload_input (width : Nat) (old : (before width).register.Index) :
    payloadEquiv width (inputBasisEquiv width old).2 =
      (PayloadPreparation.inputBasisEquiv width (payloadWidth width) old).2 :=
  (payloadEquiv width).apply_symm_apply _

/-- Extend the real native division frame by its physically supplied flag. -/
def nativeEncoding (width : Nat) : BinaryLabelEncoding (Frame width × Bool) :=
  BinaryLabelEncoding.prod (frameEncoding width) BinaryLabelEncoding.bool

/-- The two associations enumerate precisely the same full native wire set. -/
theorem divisionPayload_width (width : Nat) :
    (nativeEncoding width).width =
      (PayloadPreparation.frameEncoding width (payloadWidth width)).width := by
  change ((Inversion.SharedEEA.encoding width).width + (width + width)) + 1 =
    (Inversion.SharedEEA.encoding width).width + ((width + width) + 1)
  omega

/-- Reassociation keeps each numerical label, hence every bit at its existing physical address. -/
def nativeLabelEquiv (width : Nat) :
    (Qubits (nativeEncoding width).width).Index ≃
      (Qubits (PayloadPreparation.frameEncoding width (payloadWidth width)).width).Index :=
  finCongr (congrArg (fun count => 2 ^ count) (divisionPayload_width width))

/-- The complete frame and payload have identical binary values before and after reassociation. -/
theorem divisionPayload_native_encode (width : Nat) (frame : Inversion.SharedEEA.Registers width)
    (numerator target : Fin (2 ^ width)) (flag : Bool) :
    nativeLabelEquiv width ((nativeEncoding width).encode ((frame, numerator, target), flag)) =
      (PayloadPreparation.frameEncoding width (payloadWidth width)).encode
        (frame, payloadEquiv width ((numerator, target), flag)) := by
  apply Fin.ext
  cases flag
  · change 0 + 2 * ((target.val + 2 ^ width * numerator.val) +
        2 ^ (width + width) * ((Inversion.SharedEEA.encoding width).encode frame).val) =
      (0 + 2 * (target.val + 2 ^ width * numerator.val)) +
        2 ^ ((width + width) + 1) * ((Inversion.SharedEEA.encoding width).encode frame).val
    rw [pow_succ]
    ring
  · change 1 + 2 * ((target.val + 2 ^ width * numerator.val) +
        2 ^ (width + width) * ((Inversion.SharedEEA.encoding width).encode frame).val) =
      (1 + 2 * (target.val + 2 ^ width * numerator.val)) +
        2 ^ ((width + width) + 1) * ((Inversion.SharedEEA.encoding width).encode frame).val
    rw [pow_succ]
    ring

/-- One fixed preparation yields the exact complete initial EEA frame and all untouched data. -/
theorem divisionPayload_prepared_initial (modulus : Nat)
    (old : (before modulus.size).register.Index) :
    PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size)
        (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
          ((InputPreparation.preparation modulus).value, old)) =
      nativeLabelEquiv modulus.size
        ((nativeEncoding modulus.size).encode
          ((InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
            (inputBasisEquiv modulus.size old).2.1.1,
            (inputBasisEquiv modulus.size old).2.1.2),
            (inputBasisEquiv modulus.size old).2.2)) := by
  rw [divisionPayload_native_encode, divisionPayload_input]
  exact PayloadAssembly.payloadAssembly_prepared_initial modulus (payloadWidth modulus.size) old

/-- Local allowed support requires only unit denominator and canonical numerator/target words. -/
def admissible (modulus : Nat) (old : (before modulus.size).register.Index) : Prop :=
  ExecutionSpecification.admissible modulus (inputBasisEquiv modulus.size old)

/-- Every joint density and reference extension is allowed whenever its local support is valid. -/
def valid (modulus : Nat)
    (state : ExecutionState (Store (before modulus.size)) (before modulus.size).register) : Prop :=
  ∀ basis, ¬admissible modulus basis → state.quantumMarginal.matrix basis basis = 0

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionLayout

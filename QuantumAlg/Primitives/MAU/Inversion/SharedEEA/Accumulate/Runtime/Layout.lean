/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Payload.Assembly
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Specification

/-!
# Actual modular-add inverse input, arbitrary target, and supplied flag

The supplied payload contains the entire target word and one real flag
qubit. Auxiliary preparation is the fixed source preparation. The
associative binary regrouping below preserves every numerical label;
it introduces no physical permutation and no uncharged reference field.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AccumulateRuntime

noncomputable section

open Execution

/-- The supplied input includes the unit word, arbitrary modular target, and original flag. -/
abbrev before (width : Nat) := PayloadPreparation.before width (width + 1)

/-- The prepared context retains every original supplied bit and every source auxiliary bit. -/
abbrev after (width : Nat) := PayloadPreparation.after width (width + 1)

/-- Exact big-endian packing of the supplied target and its trailing flag. -/
def payloadEquiv (width : Nat) : (Fin (2 ^ width) × Bool) ≃ Fin (2 ^ (width + 1)) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans (prodEquiv (m := width) (n := 1))

/-- The mathematical flag uses the same zero/one label as its actual physical encoding. -/
lemma accumulatePayload_encode (width : Nat) (value : Fin (2 ^ width) × Bool) :
    payloadEquiv width value =
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
        BinaryLabelEncoding.bool).encode value := by
  rcases value with ⟨target, flag⟩
  cases flag <;> rfl

/-- Decode all original data fields through their actual supplied wire identities. -/
def inputBasisEquiv (width : Nat) :
    (before width).register.Index ≃ AccumulateSpecification.Labels width :=
  (PayloadPreparation.inputBasisEquiv width (width + 1)).trans
    (Equiv.prodCongr (Equiv.refl _) (payloadEquiv width).symm)

/-- Repacking the decoded target and flag recovers the identical original payload word. -/
lemma accumulatePayload_input (width : Nat) (old : (before width).register.Index) :
    payloadEquiv width (inputBasisEquiv width old).2 =
      (PayloadPreparation.inputBasisEquiv width (width + 1) old).2 :=
  (payloadEquiv width).apply_symm_apply _

/-- Extend the actual native frame encoding by the separately supplied live flag qubit. -/
def nativeEncoding (width : Nat) : BinaryLabelEncoding (Accumulate.Frame width × Bool) :=
  BinaryLabelEncoding.prod (Accumulate.frameEncoding width) BinaryLabelEncoding.bool

/-- Both binary associations occupy precisely the same full set of native wire positions. -/
lemma accumulatePayload_width (width : Nat) :
    (nativeEncoding width).width = (PayloadPreparation.frameEncoding width (width + 1)).width := by
  change ((encoding width).width + width) + 1 = (encoding width).width + (width + 1)
  omega

/-- Reassociation preserves the numerical binary label rather than permuting physical bits. -/
def nativeLabelEquiv (width : Nat) :
    (Qubits (nativeEncoding width).width).Index ≃
      (Qubits (PayloadPreparation.frameEncoding width (width + 1)).width).Index :=
  finCongr (congrArg (fun count => 2 ^ count) (accumulatePayload_width width))

/-- The regrouped full frame and payload encode exactly the same value on every physical wire. -/
lemma accumulatePayload_native_encode (width : Nat) (frame : Registers width)
    (target : Fin (2 ^ width)) (flag : Bool) :
    nativeLabelEquiv width ((nativeEncoding width).encode ((frame, target), flag)) =
      (PayloadPreparation.frameEncoding width (width + 1)).encode
        (frame, payloadEquiv width (target, flag)) := by
  apply Fin.ext
  cases flag
  · change 0 + 2 * (target.val + 2 ^ width * ((encoding width).encode frame).val) =
      (0 + 2 * target.val) + 2 ^ (width + 1) * ((encoding width).encode frame).val
    rw [pow_succ]
    ring
  · change 1 + 2 * (target.val + 2 ^ width * ((encoding width).encode frame).val) =
      (1 + 2 * target.val) + 2 ^ (width + 1) * ((encoding width).encode frame).val
    rw [pow_succ]
    ring

/-- One actual fixed preparation gives the complete source initial frame and unchanged data. -/
lemma accumulatePayload_prepared_initial (modulus : Nat)
    (old : (before modulus.size).register.Index) :
    PayloadAssembly.basisEquiv modulus.size (modulus.size + 1)
        (PayloadPreparation.assembly modulus.size (modulus.size + 1)
          ((InputPreparation.preparation modulus).value, old)) =
      nativeLabelEquiv modulus.size
        ((nativeEncoding modulus.size).encode
          ((InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
            (inputBasisEquiv modulus.size old).2.1), (inputBasisEquiv modulus.size old).2.2)) := by
  rw [accumulatePayload_native_encode, accumulatePayload_input]
  exact PayloadAssembly.payloadAssembly_prepared_initial modulus (modulus.size + 1) old

end

end QuantumAlg.MAU.Inversion.SharedEEA.AccumulateRuntime

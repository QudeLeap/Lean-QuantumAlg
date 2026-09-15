/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Encoding
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Execution.Store

/-!
# Actual nominal base, recovered-order and factor writes

These are the existing closed representation instructions in the real tail.
Base packing preserves the raw word without adding a modulus-validity claim.
Optional order decoding and final factor packaging preserve the exact stored
tags and payloads, including absent results and the early-factor branch.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem encode_some_word (value : CShape.Word (modulusBits N)) :
    encodeOutput (N := N) (some value.toNat) = .optionSome value := by
  cases value with
  | unsignedWord value =>
    apply congrArg CShape.Value.optionSome
    apply congrArg CShape.Value.unsignedWord
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt

private theorem packOption_numeric (tag : CShape.Value .bit)
    (payload : CShape.Word (modulusBits N)) :
    CShape.packOption (.product tag payload) =
      encodeOutput (N := N) (if tag.toBool then some payload.toNat else none) := by
  cases tag with
  | bit value =>
    cases value
    · rfl
    · exact (encode_some_word payload).symm

/-- The actual canonical-residue pack preserves the original stored raw base word. -/
theorem packBase_result (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Cells ctx N) (store : Store ctx) :
    ((store.applyOp (packBaseOp parameter cells)).read
      (.storage cells.base.toCStorageRef)).residueEncoding.val =
        (store.read parameter).first.toNat :=
  (congrArg (fun value => value.residueEncoding.val)
    (Store.read_applyOp_output store (packBaseOp parameter cells))).trans
      (ClassicalOp.eval_packCanonicalResidue_encoding (modulusBits N) ctx
        (.first parameter) cells.base (store.read (.first parameter)))

/-- The actual unpack writes precisely the original optional word's nominal pair. -/
theorem unpackOrder_result (cells : Cells ctx N) (store : Store ctx) :
    (store.applyOp (unpackOrderOp cells)).read (expandedRead cells) =
      CShape.unpackOption (store.read (.storage cells.order.toCStorageRef)) :=
  Store.read_applyOp_output store (unpackOrderOp cells)

/-- A stored native recovery result exposes exactly its real acceptance tag and finite word. -/
theorem unpackOrder_encoded (cells : Cells ctx N) (store : Store ctx)
    (recovered : Option (Fin (2 ^ (phaseBits N + 1))))
    (stored : store.read (.storage cells.order.toCStorageRef) =
      ClassicalRoutines.OrderRecovery.Native.encodeOutput recovered) :
    (store.applyOp (unpackOrderOp cells)).read (expandedRead cells) =
      match recovered with
      | none => .product (.bit false) (CShape.wordOfNat (phaseBits N + 1) 0)
      | some word => .product (.bit true) (.unsignedWord word) := by
  refine (unpackOrder_result cells store).trans ((congrArg CShape.unpackOption stored).trans ?_)
  cases recovered <;> rfl

/-- Final option packing uses exactly the actual active bit and actual half-power payload. -/
theorem packOutput_result (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (store.applyOp (packOutputOp cells output)).read (.storage output.toCStorageRef) =
      encodeOutput (N := N)
        (if (store.read (activeRead cells)).toBool then
          some (store.read (halfRead cells)).toNat else none) :=
  (Store.read_applyOp_output store (packOutputOp cells output)).trans
    (packOption_numeric (store.read (activeRead cells)) (store.read (halfRead cells)))

/-- The actual early-factor pack preserves both the sampler's stored tag and its payload. -/
theorem packEarly_result (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (store.applyOp (packEarlyOp parameter output)).read (.storage output.toCStorageRef) =
      encodeOutput (N := N)
        (if (store.read parameter).second.first.toBool then
          some (store.read parameter).second.second.toNat else none) := by
  refine (Store.read_applyOp_output store (packEarlyOp parameter output)).trans ?_
  change CShape.packOption (store.read parameter).second = _
  cases (store.read parameter).second with
  | product tag payload => exact packOption_numeric tag payload

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

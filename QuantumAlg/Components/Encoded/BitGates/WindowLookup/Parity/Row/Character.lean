/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Store

/-!
# Selected character of actual paid row parity

The phase program is selected by the actual stored parity vector. On an
explicitly promised unary target it contributes precisely the original
measured-mask dot product of that selected table column. The computation,
stored read and physical phase are the same ones present in the row circuit.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- Each bit of the actual selected phase constant is its real computed column parity. -/
lemma storedRowConstant_testBit (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit)
    (distinct : Function.Injective (fun index => (parity index).key))
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (table : Fin columns → Fin (2 ^ wordWidth)) (store : Store ctx) (label : Fin columns) :
    (storedConstant ((rowRecord (oracles := oracles) (services := services) measured parity table
      (List.ofFn fun index : Fin columns => index) store).1.read (rowInput parity))).val.testBit
        label.val = value (selectedInputs measured (table label)) store := by
  rw [storedConstant_testBit]
  change (((rowRecord (oracles := oracles) (services := services) measured parity table
    (List.ofFn fun index : Fin columns => index) store).1).read
      (.storage (parity label).toCStorageRef)).toBool = _
  exact rowRecord_read_parity measured parity distinct separate table _
    (List.nodup_ofFn_ofInjective (fun _ _ same => same)) label
    (List.mem_ofFn.mpr ⟨label, rfl⟩) store

/-- The real selected physical word phase cancels the corresponding measured character. -/
lemma storedRowPhase_applyVec (physical : QubitLayout encoding.width)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (parityDistinct : Function.Injective (fun index => (parity index).key))
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (table : Fin columns → Fin (2 ^ wordWidth)) (store : Store ctx)
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (height : Nat) (covered : columns ≤ 2 ^ height) (environment : oracles.Interpretation)
    (label : Fin columns) (state : Data)
    (oneHot : ∀ index, (target.bit index).get state = decide (index = label)) :
    UnitaryCircuit.applyVec
      (wordMaskParityPhaseProgram physical oracles target distinct selector outside
        (storedConstant ((rowRecord (oracles := oracles) (services := services)
          measured parity table (List.ofFn fun index : Fin columns => index) store).1.read
            (rowInput parity))) height)
        environment (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      (if selector.get state = true ∧ value (selectedInputs measured (table label)) store = true
        then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  rw [wordMaskParityPhaseProgram_applyVec _ _ _ _ _ _ _ _ covered,
    wordMaskParity_oneHot _ _ label state oneHot,
    storedRowConstant_testBit measured parity parityDistinct separate]

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity

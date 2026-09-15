/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual full-width Fourier frequency rescaling

The original raw word and the one-bit-wider stored order are multiplied into
their complete combined width. Actual division by a stored denominator then
writes its quotient and remainder, and one resize materializes the quotient.
Lexical placement and native loading of the power-of-two denominator are
separate. No truncated product or supplied inverse replaces an instruction.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Both actual division results retain the original full numerator and denominator widths. -/
def scaleDivisionShape (width : Nat) : CShape :=
  .product (.unsignedWord (width + (width + 1))) (.unsignedWord (width + 1))

/-- Structural read of one actually written scaling cell. -/
def scaleRead {shape : CShape} (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- The complete original product has exactly the sum of the two source widths. -/
def scaleProductOp (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1)))) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord (width + 1)))
      (.unsignedWord (width + (width + 1))) ctx ctx :=
  .mulFull width (width + 1) ctx (.product raw modulus) product

/-- Actual unsigned division reads the complete product and actual stored denominator. -/
def scaleDivisionOp (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (division : CWriteRef ctx (scaleDivisionShape width)) :
    ClassicalOp (scaleDivisionShape width) (scaleDivisionShape width) ctx ctx :=
  .divRem (width + (width + 1)) (width + 1) ctx
    (.product (scaleRead product) denominator) division

/-- Materialize the computed quotient through one native narrowing instruction. -/
def scaleQuotientOp (division : CWriteRef ctx (scaleDivisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord (width + (width + 1))) (.unsignedWord width) ctx ctx :=
  .wordResize (width + (width + 1)) width ctx (.first (scaleRead division)) output

/-- The literal original full-product, division and quotient materialization sequence. -/
def scaleBody (raw : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (scaleProductOp raw modulus product))
    (.seq (.classical (scaleDivisionOp product denominator division))
      (.classical (scaleQuotientOp division output)))

/-- Actual store after precisely the three scaling instructions. -/
def scaleStore (raw : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  ((store.applyOp (scaleProductOp raw modulus product)).applyOp
    (scaleDivisionOp product denominator division)).applyOp (scaleQuotientOp division output)

/-- Finite-word expression computed by those same actual instructions. -/
def scaleWordValue (raw : CShape.Word width)
    (modulus denominator : CShape.Word (width + 1)) : CShape.Word width :=
  CShape.wordResize width
    (CShape.divRem (width + (width + 1)) (width + 1)
      (.product (CShape.mulFull width (width + 1) (.product raw modulus)) denominator)).first

/-- Full actual classical execution retains every complete quantum-reference matrix block. -/
theorem scaleBody_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scaleBody raw modulus denominator product division output).execute Reference state =
      state.mapClassical (fun entry =>
        (scaleStore raw modulus denominator product division output entry.1,
          (entry.2, ((), ((), ()))))) := by
  simp only [scaleBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Product storage preserves the later-read denominator; every scratch start is arbitrary. -/
theorem scaleBody_result (raw : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (output : CWriteRef ctx (.unsignedWord width))
    (separate : product.key ∉ denominator.storageKeys) (store : Store ctx) :
    (scaleStore raw modulus denominator product division output store).read (scaleRead output) =
      scaleWordValue (store.read raw) (store.read modulus) (store.read denominator) := by
  change (((store.applyOp (scaleProductOp raw modulus product)).applyOp
    (scaleDivisionOp product denominator division)).applyOp (scaleQuotientOp division output)).read
      (.storage (scaleQuotientOp division output).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change CShape.wordResize width
    (((store.applyOp (scaleProductOp raw modulus product)).applyOp
      (scaleDivisionOp product denominator division)).read
        (.storage (scaleDivisionOp product denominator division).outputRef.toCStorageRef)).first = _
  rw [Store.read_applyOp_output]
  change CShape.wordResize width
    (CShape.divRem (width + (width + 1)) (width + 1) (.product
      ((store.applyOp (scaleProductOp raw modulus product)).read (scaleRead product))
      ((store.applyOp (scaleProductOp raw modulus product)).read denominator))).first = _
  have productRead : (store.applyOp (scaleProductOp raw modulus product)).read (scaleRead product) =
      CShape.mulFull width (width + 1) (.product (store.read raw) (store.read modulus)) :=
    Store.read_applyOp_output store (scaleProductOp raw modulus product)
  rw [productRead, Store.read_applyOp_of_not_mem_storageKeys
    store (scaleProductOp raw modulus product) denominator separate]
  rfl

/-- The full-width product and quotient are exact before the last native narrowing. -/
theorem scaleWordValue_toNat (raw : CShape.Word width)
    (modulus denominator : CShape.Word (width + 1)) :
    (scaleWordValue raw modulus denominator).toNat =
      (raw.toNat * modulus.toNat / denominator.toNat) % 2 ^ width := by
  have full : raw.toNat * modulus.toNat < 2 ^ (width + (width + 1)) :=
    ClassicalOp.mulFull_product_lt width (width + 1) (.product raw modulus)
  have quotient : raw.toNat * modulus.toNat / denominator.toNat <
      2 ^ (width + (width + 1)) :=
    (Nat.div_le_self (raw.toNat * modulus.toNat) denominator.toNat).trans_lt full
  change (((raw.toNat * modulus.toNat) % 2 ^ (width + (width + 1)) /
    denominator.toNat) % 2 ^ (width + (width + 1))) % 2 ^ width = _
  rw [Nat.mod_eq_of_lt full, Nat.mod_eq_of_lt quotient]

/-- A bounded raw frequency rescales strictly below the original group order. -/
theorem scaleQuotient_lt (spec : ModulusSpec width) (raw : CShape.Word width) :
    raw.toNat * spec.modulus / 2 ^ width < spec.modulus := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos width)).2
  simpa only [Nat.mul_comm] using
    Nat.mul_lt_mul_of_pos_right raw.toNat_lt (modulusSpec_modulus_pos spec)

/-- The native quotient already lies in the original canonical residue range. -/
theorem scaleWordValue_original (spec : ModulusSpec width) (raw : CShape.Word width)
    (modulus denominator : CShape.Word (width + 1))
    (orderValue : modulus.toNat = spec.modulus) (powerValue : denominator.toNat = 2 ^ width) :
    (scaleWordValue raw modulus denominator).toNat = (scaleFrequency spec raw.toNat).val := by
  have below := scaleQuotient_lt spec raw
  have fits : raw.toNat * spec.modulus / 2 ^ width < 2 ^ width :=
    below.trans_le spec.le_capacity
  rw [scaleWordValue_toNat, orderValue, powerValue, Nat.mod_eq_of_lt fits]
  exact (Nat.mod_eq_of_lt below).symm

/-- Every original structural read outside the actual three written cells remains unchanged. -/
theorem scaleBody_read_other (raw : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (productFree : product.key ∉ other.storageKeys)
    (divisionFree : division.key ∉ other.storageKeys) (outputFree : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (scaleStore raw modulus denominator product division output store).read other =
      store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys _ (scaleQuotientOp division output)
    other outputFree).trans
    ((Store.read_applyOp_of_not_mem_storageKeys _ (scaleDivisionOp product denominator division)
      other divisionFree).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (scaleProductOp raw modulus product)
        other productFree))

/-- Independent original full-width multiplication, division and quotient resize coordinates. -/
def scaleBodyEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.mulFull width (width + 1)),
    .classicalOperation (.divRem (width + (width + 1)) (width + 1)),
    .classicalOperation (.wordResize (width + (width + 1)) width)]

/-- The original three native instructions are the complete actual chronological trace. -/
theorem scaleBody_eventTrace (raw : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (scaleBody raw modulus denominator product division output).Path) :
    (scaleBody raw modulus denominator product division output).eventTrace path =
      scaleBodyEvents kind width := rfl

/-- Every scaling operation depends on the original preceding result. -/
theorem scaleBody_depth (raw : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (scaleBody raw modulus denominator product division output).Path) :
    (scaleBody raw modulus denominator product division output).depth (fun _ => 1) path = 3 := rfl

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.Reduce.Native
import all QuantumAlg.Util.Classical.Modular.Basic

/-!
# Exact actual quotient/remainder reduction

The scratch division pair is internal. Both operands are read before the
original destination is written, so the destination may alias an operand.
The full classical-store update preserves every quantum-reference block.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.Reduce.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- Actual full quantum-reference execution of the two chronological native instructions. -/
theorem reductionBody_execute (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (division : CWriteRef ctx (divisionShape sourceWidth width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (reductionBody numerator modulus division output).execute Reference state =
      state.mapClassical (fun entry =>
        ((reductionBodyStep numerator modulus division output entry.1).1,
          (entry.2, (reductionBodyStep numerator modulus division output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (.classical (reductionDivideOp numerator modulus division))
    (.classical (reductionResizeOp division output))
    (fun store => (store.applyOp (reductionDivideOp numerator modulus division), ()))
    (fun store => (store.applyOp (reductionResizeOp division output), ()))
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical
        (reductionDivideOp numerator modulus division) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical
        (reductionResizeOp division output) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Finite raw result of the original quotient/remainder and remainder-resize instructions. -/
def reductionValue (numerator : CShape.Word sourceWidth) (modulus : CShape.Word (width + 1)) :
    CShape.Word width :=
  CShape.wordResize width
    (CShape.divRem sourceWidth (width + 1) (.product numerator modulus)).second

/-- The unplaced two-operation body reads both operands before its final output write. -/
theorem reductionBody_value (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (division : CWriteRef ctx (divisionShape sourceWidth width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (reductionBodyStep numerator modulus division output store).1.read (reductionRead output) =
      reductionValue (store.read numerator) (store.read modulus) := by
  let divided := store.applyOp (reductionDivideOp numerator modulus division)
  have result : divided.read (reductionRead division) =
      CShape.divRem sourceWidth (width + 1)
        (.product (store.read numerator) (store.read modulus)) :=
    Store.read_applyOp_output store (reductionDivideOp numerator modulus division)
  have written : (divided.applyOp (reductionResizeOp division output)).read (reductionRead output) =
      CShape.wordResize width (divided.read (reductionRead division)).second :=
    Store.read_applyOp_output divided (reductionResizeOp division output)
  exact written.trans (congrArg (fun value => CShape.wordResize width value.second) result)

/-- The unplaced body preserves every structural read outside the two actual output keys. -/
theorem reductionBody_read_other (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (division : CWriteRef ctx (divisionShape sourceWidth width))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (divisionFree : division.key ∉ other.storageKeys) (outputFree : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (reductionBodyStep numerator modulus division output store).1.read other =
      store.read other := by
  unfold reductionBodyStep
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (reductionResizeOp division output) other
    outputFree, Store.read_applyOp_of_not_mem_storageKeys _
      (reductionDivideOp numerator modulus division) other divisionFree]

/-- The real lexical entry, both instructions and matching release preserve full reference data. -/
theorem reduceWord_execute (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (reduceWord numerator modulus output).execute Reference state =
      state.mapClassical (fun entry =>
        ((reduceWordStep numerator modulus output entry.1).1,
          (entry.2, (reduceWordStep numerator modulus output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (divisionShape sourceWidth width) ctx.canonicalFreshKey_fresh
    (reductionPlaced numerator modulus output)
    (reductionBodyStep (underReduction numerator sourceWidth width)
      (underReduction modulus sourceWidth width) (divisionCell ctx sourceWidth width)
      (writeUnderReduction output sourceWidth width))
    (reductionBody_execute (underReduction numerator sourceWidth width)
      (underReduction modulus sourceWidth width) (divisionCell ctx sourceWidth width)
      (writeUnderReduction output sourceWidth width)) Reference state).trans ?_
  congr 1

/-- The actual released result is the finite native value of the original two operand reads. -/
theorem reduceWord_value (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (reduceWordStep numerator modulus output store).1.read (reductionRead output) =
      reductionValue (store.read numerator) (store.read modulus) := by
  unfold reduceWordStep
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ (reductionRead output)]
  change (reductionBodyStep _ _ _ _ _).1.read
    (reductionRead (writeUnderReduction output sourceWidth width)) = _
  rw [reductionBody_value]
  simp only [underReduction, Store.read_pushWorkspace_underWorkspace]

/-- Once its internal division pair is released only the original destination may change. -/
theorem reduceWord_read_other (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (reduceWordStep numerator modulus output store).1.read other = store.read other := by
  unfold reduceWordStep
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ other]
  change (reductionBodyStep _ _ _ _ _).1.read (underReduction other sourceWidth width) = _
  rw [reductionBody_read_other]
  · exact Store.read_pushWorkspace_underWorkspace _ _ _ _ other
  · simp only [underReduction, CInputRef.storageKeys_underWorkspace]
    exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)
  · change output.key ∉ (underReduction other sourceWidth width).storageKeys
    simpa only [underReduction, CInputRef.storageKeys_underWorkspace] using separate

/-- Positive fitted actual moduli make both native remainder representations lossless. -/
theorem reductionValue_toNat (numerator : CShape.Word sourceWidth)
    (modulus : CShape.Word (width + 1)) (positive : 0 < modulus.toNat)
    (fits : modulus.toNat ≤ 2 ^ width) :
    (reductionValue numerator modulus).toNat = numerator.toNat % modulus.toNat := by
  have remainderBound := Nat.mod_lt numerator.toNat positive
  change ((numerator.toNat % modulus.toNat) % 2 ^ (width + 1)) % 2 ^ width = _
  rw [Nat.mod_eq_of_lt (lt_trans remainderBound modulus.toNat_lt),
    Nat.mod_eq_of_lt (lt_of_lt_of_le remainderBound fits)]

/-- The actual released destination is the exact remainder of the original stored numerator. -/
theorem reduceWord_toNat (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (positive : 0 < (store.read modulus).toNat)
    (fits : (store.read modulus).toNat ≤ 2 ^ width) :
    ((reduceWordStep numerator modulus output store).1.read (reductionRead output)).toNat =
      (store.read numerator).toNat % (store.read modulus).toNat := by
  rw [reduceWord_value]
  exact reductionValue_toNat _ _ positive fits

/-- Original intrinsic modulus data include the capacity-modulus boundary without narrowing. -/
theorem reduceWord_original_value (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width) (store : Store ctx)
    (orderValue : (store.read modulus).toNat = spec.modulus) :
    ((reduceWordStep numerator modulus output store).1.read (reductionRead output)).toNat =
      (store.read numerator).toNat % spec.modulus := by
  rw [reduceWord_toNat _ _ _ store (orderValue ▸ modulusSpec_modulus_pos spec)
    (orderValue ▸ spec.le_capacity), orderValue]

end

end QuantumAlg.ClassicalRoutines.Modular.Reduce.Native

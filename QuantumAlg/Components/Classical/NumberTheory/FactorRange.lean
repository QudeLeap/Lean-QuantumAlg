/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual nontrivial-factor comparison of a stored GCD word

Two genuine unsigned comparisons read the stored candidate, one and modulus.
One genuine bit conjunction writes their combined decision. The enclosing
factor-recovery scope supplies the physically separate cells and loads its
constants; no arithmetic predicate callback enters the instruction stream.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.FactorRange

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The exact operands and two writable comparison bits in the factor-recovery scope. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  candidate : CInputRef ctx (.unsignedWord width)
  one : CInputRef ctx (.unsignedWord width)
  modulus : CInputRef ctx (.unsignedWord width)
  lower : CWriteRef ctx .bit
  upper : CWriteRef ctx .bit

def lowerOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx (.product refs.one refs.candidate) refs.lower

def upperOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx (.product refs.candidate refs.modulus) refs.upper

def combineOp (refs : Refs ctx width) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (.storage refs.lower.toCStorageRef)
    (.storage refs.upper.toCStorageRef)) refs.lower

/-- The real complete store produced by those three closed instructions. -/
def storeStep (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp (lowerOp refs)).applyOp (upperOp refs)).applyOp (combineOp refs)

variable {model : ExecutionModel} {environment : model.Environment}
  [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Execute both stored-word comparisons and materialize their actual conjunction. -/
def code (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (lowerOp refs))
    (.seq (BitWord.instruction (execution := model) (upperOp refs))
      (BitWord.instruction (execution := model) (combineOp refs)))

/-- Complete returned record of the real comparisons and conjunction. -/
def executionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (code (model := model) refs).Path :=
  let lower := BitWord.instructionStep (execution := model) (lowerOp refs) store
  let upper := BitWord.instructionStep (execution := model) (upperOp refs) lower.1
  let combined := BitWord.instructionStep (execution := model) (combineOp refs) upper.1
  (combined.1, (lower.2, (upper.2, combined.2)))

/-- The actual native record has the original chronological comparison store. -/
lemma executionStep_store (refs : Refs ctx width) (store : Store ctx) :
    (executionStep (model := model) refs store).1 = storeStep refs store := rfl

/-- The same three native writes preserve all history, service and quantum-reference blocks. -/
lemma code_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) refs).execute environment Reference state =
      state.mapClassical (fun entry =>
      let actual := executionStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [code, executionStep, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The stored result is precisely the two comparisons on the original actual operand values. -/
lemma result (refs : Refs ctx width) (store : Store ctx)
    (lowerFree : refs.lower.key ∉ (CInputRef.product refs.candidate refs.modulus).storageKeys)
    (distinct : refs.upper.key ≠ refs.lower.key) :
    ((storeStep refs store).read (.storage refs.lower.toCStorageRef)).toBool =
      (decide ((store.read refs.one).toNat < (store.read refs.candidate).toNat) &&
        decide ((store.read refs.candidate).toNat < (store.read refs.modulus).toNat)) := by
  let lowered := store.applyOp (lowerOp refs)
  let compared := lowered.applyOp (upperOp refs)
  have upperInputs := Store.read_applyOp_of_not_mem_storageKeys store
    (lowerOp refs) (.product refs.candidate refs.modulus) lowerFree
  have lowerSame : compared.read (.storage refs.lower.toCStorageRef) =
      (lowerOp refs).eval (store.read (.product refs.one refs.candidate)) := by
    refine (Store.read_applyOp_of_not_mem_storageKeys lowered (upperOp refs)
      (.storage refs.lower.toCStorageRef) ?_).trans
      (Store.read_applyOp_output store (lowerOp refs))
    exact fun member => distinct (List.mem_singleton.mp member)
  have upperValue : compared.read (.storage refs.upper.toCStorageRef) =
      (upperOp refs).eval (store.read (.product refs.candidate refs.modulus)) :=
    (Store.read_applyOp_output lowered (upperOp refs)).trans
      (congrArg (upperOp refs).eval upperInputs)
  refine (congrArg CShape.Value.toBool
    (Store.read_applyOp_output compared (combineOp refs))).trans ?_
  change (Resource.BitOpcode.eval .and
    (.product (compared.read (.storage refs.lower.toCStorageRef))
      (compared.read (.storage refs.upper.toCStorageRef)))).toBool = _
  rw [lowerSame, upperValue]
  rfl

/-- No structural operand outside the two genuine written bits changes its stored value. -/
lemma read_other (refs : Refs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (lowerFree : refs.lower.key ∉ other.storageKeys)
    (upperFree : refs.upper.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep refs store).read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys
    ((store.applyOp (lowerOp refs)).applyOp (upperOp refs)) (combineOp refs) other lowerFree).trans
    ((Store.read_applyOp_of_not_mem_storageKeys (store.applyOp (lowerOp refs))
      (upperOp refs) other upperFree).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (lowerOp refs) other lowerFree))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.FactorRange

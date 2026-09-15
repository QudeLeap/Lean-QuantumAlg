/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Initialization
import all QuantumAlg.Components.Classical.Modular.NativePower.PowerSemantics
import all QuantumAlg.Components.Classical.Modular.NativePower.ScopeExecution

/-!
# Original modular-power result from actual stored inputs

Source representation is equality of the original base and exponent reads.
Fresh lexical placement supplies all separation and initialization facts.
The actual finite exponent fold therefore reaches the intrinsic source power,
which the actual final copy exposes after all scratch heads are released.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width exponentWidth : Nat}

/-- The intrinsic source input is represented by the actual base and exponent values. -/
def InputRepresents (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth)) (store : Store ctx)
    (input : Pow.Input spec exponentWidth) : Prop :=
  store.read base = .canonicalResidue input.base.toWord ∧
    store.read exponent = .unsignedWord input.exponent

private theorem oneValue (spec : ModulusSpec width) :
    CShape.wordOfNat width 1 = residueValue (Residue.one spec) := by
  apply congrArg CShape.Value.unsignedWord
  apply Fin.ext
  change 1 % 2 ^ width = (Residue.one spec).val
  rw [Residue.residueOne_val]
  exact Nat.mod_eq_of_lt ((modulusSpec_one_lt spec).trans_le spec.le_capacity)

/-- The actual initialized exponent fold reaches exactly the original intrinsic power. -/
theorem nativePower_initialized_fold_result (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth)) (store : Store ctx)
    (input : Pow.Input spec exponentWidth)
    (represented : InputRepresents spec base exponent store input) :
    ((foldStep (wordRead (baseCell ctx width)) (wordRead (modulusCell ctx width))
      (accumulatorCell ctx width)
      (List.ofFn (fun index : Fin exponentWidth =>
        CInputRef.wordBitGet (underPower exponent width) index))
      (initializedStore spec base (enterPower store width))).1).read
        (wordRead (accumulatorCell ctx width)) = residueValue (Pow.eval spec input) := by
  let initial := initializedStore spec base (enterPower store width)
  let bits := List.ofFn (fun index : Fin exponentWidth =>
    CInputRef.wordBitGet (underPower exponent width) index)
  have baseValue : initial.read (wordRead (baseCell ctx width)) = residueValue input.base := by
    rw [nativePower_initialized_base, represented.1]
    rfl
  have modulusValue := nativePower_initialized_modulus spec base store
  have accumulatorValue : initial.read (wordRead (accumulatorCell ctx width)) =
      residueValue (Residue.one spec) :=
    (nativePower_initialized_accumulator spec base store).trans (oneValue spec)
  have exponentValue : initial.read (underPower exponent width) = .unsignedWord input.exponent :=
    (nativePower_initialized_read_original spec base store exponent).trans represented.2
  have separation := nativePower_scope_separation ctx width
  have baseFree : (accumulatorCell ctx width).key ∉
      (wordRead (baseCell ctx width)).storageKeys :=
    fun present => separation.2.2 (List.mem_singleton.mp present)
  have modulusFree : (accumulatorCell ctx width).key ∉
      (wordRead (modulusCell ctx width)).storageKeys :=
    fun present => separation.2.1 (List.mem_singleton.mp present)
  have bitsFree : ∀ bit ∈ bits, (accumulatorCell ctx width).key ∉ bit.storageKeys := by
    intro bit present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    exact (nativePower_input_separation exponent width).2.2
  have actual := nativePower_fold_read_output (wordRead (baseCell ctx width))
    (wordRead (modulusCell ctx width)) (accumulatorCell ctx width) bits
    baseFree modulusFree bitsFree initial
  have sampledBits : bits.map (fun bit => (initial.read bit).toBool) =
      List.ofFn (Pow.exponentBit input.exponent) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext index
    change ((initial.read (underPower exponent width)).wordBitGet index).toBool = _
    rw [exponentValue]
    rfl
  rw [sampledBits, baseValue, modulusValue, accumulatorValue] at actual
  exact actual.trans (nativePower_math_fold spec input)

/-- The real final copy writes the source power into the original result cell under the scopes. -/
theorem nativePower_body_result (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (input : Pow.Input spec exponentWidth)
    (represented : InputRepresents spec base exponent store input) :
    ((powerBodyStep spec base exponent output (enterPower store width)).1).read
      (wordRead (writeUnderPower output width)) = residueValue (Pow.eval spec input) := by
  let powered := foldStep (wordRead (baseCell ctx width)) (wordRead (modulusCell ctx width))
    (accumulatorCell ctx width)
    (List.ofFn (fun index : Fin exponentWidth =>
      CInputRef.wordBitGet (underPower exponent width) index))
    (initializedStore spec base (enterPower store width))
  change (powered.1.applyOp (copyResultOp output)).read
    (.storage (copyResultOp output).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  exact nativePower_initialized_fold_result spec base exponent store input represented

/-- Releasing only the real scratch cells preserves the exact modular-power result. -/
theorem nativePower_into_result (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (input : Pow.Input spec exponentWidth)
    (represented : InputRepresents spec base exponent store input) :
    ((intoStep spec base exponent output store).1).read (wordRead output) =
      residueValue (Pow.eval spec input) := by
  unfold intoStep
  rw [nativePower_leavePower_read, ← nativePower_writeUnderPower_read]
  exact nativePower_body_result spec base exponent output store input represented

/-- The actual written natural value is the original modular power of the stored source input. -/
theorem nativePower_into_toNat (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (input : Pow.Input spec exponentWidth)
    (represented : InputRepresents spec base exponent store input) :
    (((intoStep spec base exponent output store).1).read (wordRead output)).toNat =
      input.base.val ^ input.exponent.val % spec.modulus := by
  rw [nativePower_into_result spec base exponent output store input represented]
  rfl

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower

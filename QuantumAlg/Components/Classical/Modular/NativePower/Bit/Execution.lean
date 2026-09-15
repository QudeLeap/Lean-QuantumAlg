/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Circuit
import all QuantumAlg.Components.Classical.Modular.NativePower.ScopedLaws

/-!
# Same-store execution of selected modular multiplications

The square's actual output store determines the exponent bit read by the
following branch. These concrete records contain that value and only the
selected path; their equations are derived from the existing interpreter.
Every complete quantum-reference density block is preserved throughout.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The real update and branch path selected by a stored Boolean. -/
def multiplyChoiceStep (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx × (multiplyChoice base modulus output value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => scopedMultiplyStep (wordRead output) base modulus output store

private theorem multiplyChoice_execute (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (multiplyChoice base modulus output value).execute Reference state =
      state.mapClassical (fun entry =>
        ((multiplyChoiceStep base modulus output value entry.1).1,
          (entry.2, (multiplyChoiceStep base modulus output value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · refine (nativePower_scopedMultiply_execute (wordRead output) base modulus output
          Reference state).trans ?_
        congr 1

/-- The actual square store supplies the following branch's concrete exponent bit. -/
def bitStep (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (store : Store ctx) : Store ctx × (bitCircuit base modulus output bit).Path :=
  let squared := scopedMultiplyStep (wordRead output) (wordRead output) modulus output store
  let value := squared.1.read bit
  let selected := multiplyChoiceStep base modulus output value squared.1
  (selected.1, (squared.2, ⟨value, selected.2⟩))

/-- Actual square-and-multiply execution records exactly its same-store classical selection. -/
theorem nativePower_bit_execute (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (bitCircuit base modulus output bit).execute Reference state =
      state.mapClassical (fun entry =>
        ((bitStep base modulus output bit entry.1).1,
          (entry.2, (bitStep base modulus output bit entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (scopedMultiply (wordRead output) (wordRead output) modulus output)
    (.branch bit (multiplyChoice base modulus output))
    (scopedMultiplyStep (wordRead output) (wordRead output) modulus output)
    (fun store =>
      ((multiplyChoiceStep base modulus output (store.read bit) store).1,
        ⟨store.read bit, (multiplyChoiceStep base modulus output (store.read bit) store).2⟩))
    (nativePower_scopedMultiply_execute (wordRead output) (wordRead output) modulus output)
    (fun reference {_} _ initial => Circuit.execute_branch_mapClassical bit _
      (multiplyChoiceStep base modulus output) (multiplyChoice_execute base modulus output)
      reference initial)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Concrete records for the finite composition of exponent-bit circuits. -/
def foldStep (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (bits : List (CInputRef ctx .bit)) → Store ctx →
      Store ctx × (foldBits base modulus output bits).Path
  | [], store => (store, ())
  | bit :: rest, store =>
      let first := bitStep base modulus output bit store
      let later := foldStep base modulus output rest first.1
      (later.1, (first.2, later.2))

/-- Every finite exponent prefix is interpreted by the same actual store/path composition. -/
theorem nativePower_fold_execute (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (foldBits base modulus output bits).execute Reference state =
      state.mapClassical (fun entry =>
        ((foldStep base modulus output bits entry.1).1,
          (entry.2, (foldStep base modulus output bits entry.1).2))) := by
  induction bits generalizing Reference History with
  | nil =>
      refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
  | cons bit rest ih =>
      refine (Circuit.execute_seq_mapClassical (bitCircuit base modulus output bit)
        (foldBits base modulus output rest) (bitStep base modulus output bit)
        (foldStep base modulus output rest)
        (nativePower_bit_execute base modulus output bit)
        (fun reference {_} _ initial => ih reference initial)
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower

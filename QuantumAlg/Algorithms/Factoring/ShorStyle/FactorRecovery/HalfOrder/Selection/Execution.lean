/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Packing
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Execution

/-!
# Actual left-priority GCD selection records

Each record below is the deterministic store and path of the existing real
instructions. The stored left comparison controls the actual branch: the
right GCD runs only in the rejecting arm. The equalities preserve complete
quantum-reference density blocks throughout that same execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open ClassicalRoutines.NumberTheory

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The real comparison record is followed by actual option packaging. -/
def checkedPackStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (FactorRange.code (checkRefs cells)) (pack cells output)).Path :=
  let next := packStep cells output (FactorRange.storeStep (checkRefs cells) store)
  (next.1, (((), ((), ())), next.2))

/-- The right arm records its real GCD, actual comparisons and actual final writes. -/
def rightStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (right halfPower cells output).Path :=
  let reduced := NativeHalfGCD.step true halfPower cells.candidate store
  let next := checkedPackStep cells output reduced.1
  (next.1, (reduced.2, next.2))

/-- The selected branch records only the instructions that really execute. -/
def chooseArmStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (value : CShape.Value .bit) → Store ctx → Store ctx ×
      (if value.toBool then pack cells output else right halfPower cells output).Path
  | .bit false, store => rightStep halfPower cells output store
  | .bit true, store => packStep cells output store

/-- Read the real left decision and retain the selected path in the actual branch record. -/
def chooseStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (choose halfPower cells output).Path :=
  let value := store.read (.storage cells.lower.toCStorageRef)
  let next := chooseArmStep halfPower cells output value store
  (next.1, ⟨value, next.2⟩)

/-- The actual first comparison feeds its real stored bit into the left-priority branch. -/
def checkedChooseStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store ctx) : Store ctx ×
      (Circuit.seq (FactorRange.code (checkRefs cells))
        (choose halfPower cells output)).Path :=
  let next := chooseStep halfPower cells output
    (FactorRange.storeStep (checkRefs cells) store)
  (next.1, (((), ((), ())), next.2))

/-- The complete factor-selection record begins with its actual left GCD call. -/
def step (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code halfPower cells output).Path :=
  let reduced := NativeHalfGCD.step false halfPower cells.candidate store
  let next := checkedChooseStep halfPower cells output reduced.1
  (next.1, (reduced.2, next.2))

private theorem check_execute (cells : Cells ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (FactorRange.code (checkRefs cells)).execute Reference state =
      state.mapClassical (fun entry =>
        (FactorRange.storeStep (checkRefs cells) entry.1,
          ((entry.2, ((), ((), ()))) :
            History × (FactorRange.code (checkRefs cells)).Path))) := by
  refine (FactorRange.code_execute (checkRefs cells) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq
        (Store ctx × (History × (FactorRange.code (checkRefs cells)).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => (FactorRange.storeStep (checkRefs cells) entry.1,
          (entry.2, ((), ((), ())))))) (Subsingleton.elim _ _)

private theorem checkedPack_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (FactorRange.code (checkRefs cells)) (pack cells output)).execute
        Reference state =
      state.mapClassical (fun entry => ((checkedPackStep cells output entry.1).1,
        (entry.2, (checkedPackStep cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (FactorRange.code (checkRefs cells))
    (pack cells output) (fun store => (FactorRange.storeStep (checkRefs cells) store,
      ((), ((), ())))) (packStep cells output)
    (check_execute cells) (pack_execute cells output)
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History ×
        (Circuit.seq (FactorRange.code (checkRefs cells)) (pack cells output)).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((checkedPackStep cells output entry.1).1,
          (entry.2, (checkedPackStep cells output entry.1).2)))) (Subsingleton.elim _ _)

private theorem right_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (right halfPower cells output).execute Reference state =
      state.mapClassical (fun entry => ((rightStep halfPower cells output entry.1).1,
        (entry.2, (rightStep halfPower cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (NativeHalfGCD.code true halfPower cells.candidate)
    (.seq (FactorRange.code (checkRefs cells)) (pack cells output))
    (NativeHalfGCD.step true halfPower cells.candidate) (checkedPackStep cells output)
    (NativeHalfGCD.code_execute true halfPower cells.candidate) (checkedPack_execute cells output)
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (right halfPower cells output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((rightStep halfPower cells output entry.1).1,
          (entry.2, (rightStep halfPower cells output entry.1).2)))) (Subsingleton.elim _ _)

private theorem chooseArm_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (if value.toBool then pack cells output else right halfPower cells output).execute
        Reference state =
      state.mapClassical (fun entry => ((chooseArmStep halfPower cells output value entry.1).1,
        (entry.2, (chooseArmStep halfPower cells output value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · exact right_execute halfPower cells output Reference state
      · exact pack_execute cells output Reference state

private theorem choose_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (choose halfPower cells output).execute Reference state =
      state.mapClassical (fun entry => ((chooseStep halfPower cells output entry.1).1,
        (entry.2, (chooseStep halfPower cells output entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical (.storage cells.lower.toCStorageRef)
    (fun value => if value.toBool then pack cells output else right halfPower cells output)
    (chooseArmStep halfPower cells output) (chooseArm_execute halfPower cells output)
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (choose halfPower cells output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((chooseStep halfPower cells output entry.1).1,
          (entry.2, (chooseStep halfPower cells output entry.1).2)))) (Subsingleton.elim _ _)

private theorem checkedChoose_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (FactorRange.code (checkRefs cells))
        (choose halfPower cells output)).execute
        Reference state =
      state.mapClassical (fun entry => ((checkedChooseStep halfPower cells output entry.1).1,
        (entry.2, (checkedChooseStep halfPower cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (FactorRange.code (checkRefs cells))
    (choose halfPower cells output)
    (fun store => (FactorRange.storeStep (checkRefs cells) store, ((), ((), ()))))
    (chooseStep halfPower cells output)
    (check_execute cells) (choose_execute halfPower cells output)
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (Circuit.seq
        (FactorRange.code (checkRefs cells)) (choose halfPower cells output)).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((checkedChooseStep halfPower cells output entry.1).1,
          (entry.2, (checkedChooseStep halfPower cells output entry.1).2))))
    (Subsingleton.elim _ _)

/-- The real left-priority circuit executes exactly its actual store and path on full CQ blocks. -/
theorem code_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code halfPower cells output).execute Reference state =
      state.mapClassical (fun entry => ((step halfPower cells output entry.1).1,
        (entry.2, (step halfPower cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (NativeHalfGCD.code false halfPower cells.candidate)
    (.seq (FactorRange.code (checkRefs cells)) (choose halfPower cells output))
    (NativeHalfGCD.step false halfPower cells.candidate) (checkedChooseStep halfPower cells output)
    (NativeHalfGCD.code_execute false halfPower cells.candidate)
    (checkedChoose_execute halfPower cells output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (code halfPower cells output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((step halfPower cells output entry.1).1,
          (entry.2, (step halfPower cells output entry.1).2)))) (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

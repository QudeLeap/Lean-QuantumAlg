/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.EvenModulus
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Execution

/-!
# Complete CQ execution of the original even-modulus exception

The existing native instruction and constant-load execution equations compose
on the actual store. The record preserves all complete quantum-reference
blocks and counts the real flag initialization, payload load and option pack.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem two_execute (cells : Cells ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (ConstantWord.circuit cells.halfPower 2).execute Reference state =
      state.mapClassical (fun entry => ((twoStep cells entry.1).1,
        (entry.2, (twoStep cells entry.1).2))) := by
  refine (ConstantWord.constantWord_fold_execute cells.halfPower
    (List.ofFn (ConstantWord.constantBits (modulusBits N) 2)) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq
        (Store ctx × (History × (ConstantWord.circuit cells.halfPower 2).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((twoStep cells entry.1).1, (entry.2, (twoStep cells entry.1).2))))
    (Subsingleton.elim _ _)

private theorem twoPack_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (ConstantWord.circuit cells.halfPower 2)
      (.classical (packOutputOp cells output))).execute Reference state =
      state.mapClassical (fun entry => ((twoPackStep cells output entry.1).1,
        (entry.2, (twoPackStep cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (ConstantWord.circuit cells.halfPower 2)
    (.classical (packOutputOp cells output)) (twoStep cells)
    (fun store => (store.applyOp (packOutputOp cells output), ())) (two_execute cells)
    (fun reference _ _ initial =>
      NativeHalfPower.classical_path_execute (packOutputOp cells output) reference initial _)
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History ×
        (Circuit.seq (ConstantWord.circuit cells.halfPower 2)
          (.classical (packOutputOp cells output))).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((twoPackStep cells output entry.1).1,
          (entry.2, (twoPackStep cells output entry.1).2)))) (Subsingleton.elim _ _)

private theorem setTwoPack_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (.classical (setActiveOp cells))
      (.seq (ConstantWord.circuit cells.halfPower 2)
        (.classical (packOutputOp cells output)))).execute Reference state =
      state.mapClassical (fun entry => ((setTwoPackStep cells output entry.1).1,
        (entry.2, (setTwoPackStep cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (setActiveOp cells))
    (.seq (ConstantWord.circuit cells.halfPower 2) (.classical (packOutputOp cells output)))
    (fun store => (store.applyOp (setActiveOp cells), ())) (twoPackStep cells output)
    (fun reference _ _ initial =>
      NativeHalfPower.classical_path_execute (setActiveOp cells) reference initial _)
    (twoPack_execute cells output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History ×
        (Circuit.seq (.classical (setActiveOp cells))
          (.seq (ConstantWord.circuit cells.halfPower 2)
            (.classical (packOutputOp cells output)))).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((setTwoPackStep cells output entry.1).1,
          (entry.2, (setTwoPackStep cells output entry.1).2)))) (Subsingleton.elim _ _)

/-- The real even-modulus branch has its exact complete store and genuine instruction record. -/
theorem even_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (evenModulus cells output).execute Reference state =
      state.mapClassical (fun entry => ((evenStep cells output entry.1).1,
        (entry.2, (evenStep cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (clearActiveOp cells))
    (.seq (.classical (setActiveOp cells))
      (.seq (ConstantWord.circuit cells.halfPower 2) (.classical (packOutputOp cells output))))
    (fun store => (store.applyOp (clearActiveOp cells), ())) (setTwoPackStep cells output)
    (fun reference _ _ initial =>
      NativeHalfPower.classical_path_execute (clearActiveOp cells) reference initial _)
    (setTwoPack_execute cells output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (evenModulus cells output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((evenStep cells output entry.1).1,
          (entry.2, (evenStep cells output entry.1).2)))) (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

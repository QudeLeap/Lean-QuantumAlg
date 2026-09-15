/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.EvenModulus.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Order.Execution

/-!
# The actual factor tail includes the original even-modulus exception

The modulus selects the same genuine circuit as in the construction. Its
record is the already derived real execution record of that selected circuit;
the complete quantum-reference block is unchanged by these classical steps.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem execute_code_eq (first second : Circuit ctx ctx) (same : first = second)
    (update : Store ctx → Store ctx × second.Path)
    (actual : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      second.execute Reference state = state.mapClassical (fun entry =>
        ((update entry.1).1, (entry.2, (update entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    first.execute Reference state = state.mapClassical (fun entry =>
      ((update entry.1).1, (entry.2, (congrArg Circuit.Path same).mpr (update entry.1).2))) := by
  cases same
  refine (actual Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × first.Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((update entry.1).1, (entry.2, (update entry.1).2))))
    (Subsingleton.elim _ _)

/-- The actual path and store of the circuit selected by the known modulus. -/
def step (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code source parameter phase cells output).Path :=
  if exceptional : 2 < N ∧ Even N then
    let selected := evenStep cells output store
    (selected.1, by simpa only [code, if_pos exceptional] using selected.2)
  else
    let selected := recoveredStep source parameter phase cells output store
    (selected.1, by simpa only [code, if_neg exceptional] using selected.2)

/-- Both original modulus branches execute with the exact corresponding native record. -/
theorem code_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code source parameter phase cells output).execute Reference state =
      state.mapClassical (fun entry => ((step source parameter phase cells output entry.1).1,
        (entry.2, (step source parameter phase cells output entry.1).2))) := by
  by_cases exceptional : 2 < N ∧ Even N
  · have same : code source parameter phase cells output = evenModulus cells output :=
      if_pos exceptional
    simpa only [step, dif_pos exceptional] using
      execute_code_eq (code source parameter phase cells output) (evenModulus cells output)
        same (evenStep cells output) (even_execute cells output) Reference state
  · have same : code source parameter phase cells output =
        recovered source parameter phase cells output := if_neg exceptional
    simpa only [step, dif_neg exceptional] using
      execute_code_eq (code source parameter phase cells output)
        (recovered source parameter phase cells output) same
        (recoveredStep source parameter phase cells output)
        (recovered_execute source parameter phase cells output) Reference state

/-- The real exceptional branch has exactly the already derived native even-case store. -/
theorem step_even_store (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (exceptional : 2 < N ∧ Even N) :
    (step source parameter phase cells output store).1 = (evenStep cells output store).1 := by
  simp only [step, dif_pos exceptional]

/-- The real ordinary branch has exactly the already derived stored-input recovery store. -/
theorem step_recovered_store (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (ordinary : ¬ (2 < N ∧ Even N)) :
    (step source parameter phase cells output store).1 =
      (recoveredStep source parameter phase cells output store).1 := by
  simp only [step, dif_neg ordinary]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

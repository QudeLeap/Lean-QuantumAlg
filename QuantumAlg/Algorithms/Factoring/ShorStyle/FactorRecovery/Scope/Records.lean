/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Result
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Store
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Separation

/-!
# Complete real factor-scope records and source result

Every write-separation condition of the native tail follows from the seven
actual fresh storage identities. Scope exit retains the computed original
factor result while releasing exactly those heads. Only identification of the
source base and the same stored terminal bits remains in the result statement.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual inner record is the already derived record of this exact native tail. -/
def bodyStep (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Store (context ctx N) → Store (context ctx N) × (body source parameter phase output).Path :=
  NativeFactorTail.step source (liftInput parameter) (liftInput phase)
    (cells ctx N) (liftWrite output)

/-- Actual entry, execution and exit preserve the genuine tail path and release all seven heads. -/
def step (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code source parameter phase output).Path :=
  let selected := bodyStep source parameter phase output (enter N store)
  (leave N selected.1, selected.2)

/-- Actual fresh geometry discharges every internal source-tail write condition. -/
theorem body_result (source : Input N)
    (semantic : ClassicalAlgorithms.OrderRecovery.Input (recoverySpec source))
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N))
    (baseValue : (store.read (liftInput parameter)).first.toNat = semantic.base.val)
    (phaseValue : store.read (liftInput phase) = .bits semantic.terminalBits) :
    (bodyStep source parameter phase output store).1.read
      (.storage (liftWrite output).toCStorageRef) =
      encodeOutput (N := N) (outputOfRecovered (store.read (liftInput parameter))
        (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
          (recoverySpec source) semantic)) := by
  exact NativeFactorTail.result source semantic (liftInput parameter) (liftInput phase)
    (cells ctx N) (liftWrite output) store (guard_separated ctx N)
    (scratchKeys_ne ctx N 0 2 (by decide))
    (scratchKeys_ne ctx N 3 6 (by decide))
    (scratchKeys_ne ctx N 2 6 (by decide))
    (scratchKeys_ne ctx N 1 6 (by decide))
    (scratchKeys_ne ctx N 5 6 (by decide))
    (scratchKeys_ne ctx N 4 6 (by decide))
    (scratchKeys_input_separate phase _ (List.get_mem (scratchKeys ctx N) (6 : Fin 7)))
    (scratchKeys_input_separate parameter _ (List.get_mem (scratchKeys ctx N) (6 : Fin 7)))
    (scratchKeys_input_separate parameter _ (List.get_mem (scratchKeys ctx N) (5 : Fin 7)))
    (scratchKeys_input_separate parameter _ (List.get_mem (scratchKeys ctx N) (4 : Fin 7)))
    baseValue phaseValue

/-- The released actual factor scope returns the source result on the original stored input. -/
theorem result (source : Input N)
    (semantic : ClassicalAlgorithms.OrderRecovery.Input (recoverySpec source))
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (baseValue : (store.read parameter).first.toNat = semantic.base.val)
    (phaseValue : store.read phase = .bits semantic.terminalBits) :
    (step source parameter phase output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N) (outputOfRecovered (store.read parameter)
        (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
          (recoverySpec source) semantic)) := by
  have enteredBase : ((enter N store).read (liftInput parameter)).first.toNat =
      semantic.base.val :=
    (congrArg (fun value => value.first.toNat) (enter_read parameter store)).trans baseValue
  have enteredPhase : (enter N store).read (liftInput phase) = .bits semantic.terminalBits :=
    (enter_read phase store).trans phaseValue
  refine (leave_read (.storage output.toCStorageRef)
    (bodyStep source parameter phase output (enter N store)).1).trans
      ((body_result source semantic parameter phase output (enter N store)
        enteredBase enteredPhase).trans ?_)
  exact congrArg (fun value => encodeOutput (N := N) (outputOfRecovered value
    (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
      (recoverySpec source) semantic))) (enter_read parameter store)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

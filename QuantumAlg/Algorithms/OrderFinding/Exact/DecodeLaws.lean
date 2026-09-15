/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Mathematics
import all QuantumAlg.Algorithms.OrderFinding.Exact.Context
import all QuantumAlg.Algorithms.OrderFinding.Exact.Execution
import all QuantumAlg.Components.Classical.TerminalDecode.Encoding
import all QuantumAlg.Components.Classical.TerminalDecode.Retained.Semantics
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Borrowed.State

/-!
# Actual stored-word semantics of exact order-finding decoding

The semantic record below is the existing decoder's proved store and path.
Its actual execution equation preserves every quantum-reference block. The
returned word is the canonical big-endian value of the same stored sample;
no measurement distribution or resource witness is supplied by a caller.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- The concrete store and path of the already proved retained decoding program. -/
def decodedStep (t n : Nat) (store : Store (Sampling.post t n)) :
    Store (post t n) × (decoderCode t n).Path :=
  ClassicalRoutines.TerminalDecode.retainedStep
    (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n) store

/-- The actual decoder updates the same block carrier, retaining all histories and references. -/
theorem decoderCode_execute (t n : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State (Sampling.post t n) Reference History) :
    (decoderCode t n).execute Reference state =
      state.mapClassical (fun entry =>
        ((decodedStep t n entry.1).1, (entry.2, (decodedStep t n entry.1).2))) :=
  ClassicalRoutines.TerminalDecode.terminalDecode_routine_execute
    (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
    Reference state

/-- The actually materialized word decodes the original packed stored value. -/
theorem decodedStep_output_of_bits (t n : Nat) (store : Store (Sampling.post t n))
    (bits : Fin t → Bool) (measured : store.read (packedInput t n) = .bits bits) :
    (decodedStep t n store).1.read (resultRef t n) = OrderFinding.encodedOutcome bits := by
  have decoded :=
    ClassicalRoutines.TerminalDecode.terminalDecode_retainedStep_read_output
      (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n) store
  have exactWord : ClassicalRoutines.TerminalDecode.decodeOutput
      ((decodedStep t n store).1.read (resultRef t n)) =
        ClassicalAlgorithms.TerminalDecode.fullRegisterIndex bits := by
    simpa only [decodedStep, resultRef, measured,
      ClassicalRoutines.TerminalDecode.decodeInput,
      ClassicalAlgorithms.TerminalDecode.fullRegisterIndex] using decoded
  cases output : (decodedStep t n store).1.read (resultRef t n) with
  | unsignedWord word =>
      rw [output] at exactWord
      change word = ClassicalAlgorithms.TerminalDecode.fullRegisterIndex bits
        at exactWord
      exact congrArg CShape.Value.unsignedWord exactWord

/-- The exact-grid predicate is transported through the real decoder's written output. -/
theorem decodedStep_success_iff (r t n : Nat) (store : Store (Sampling.post t n))
    (bits : Fin t → Bool) (measured : store.read (packedInput t n) = .bits bits) :
    OrderFinding.SuccessfulOutcome r ((decodedStep t n store).1.read (resultRef t n)) ↔
      OrderFinding.ExactOutcome r t bits := by
  rw [decodedStep_output_of_bits t n store bits measured]
  exact OrderFinding.successful_encodedOutcome_iff bits

/-- Every earlier actual classical read survives the full decoding tail. -/
theorem decodedStep_read_original (t n : Nat) (store : Store (Sampling.post t n))
    {shape : CShape} (observed : CInputRef (Sampling.post t n) shape) :
    (decodedStep t n store).1.read
      (observed.underRetained (resultKey t n) (.unsignedWord t) (resultFresh t n)) =
        store.read observed :=
  ClassicalRoutines.TerminalDecode.terminalDecode_retainedStep_read_original
    (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
    store observed

/-- The classical tail restores the complete borrowed state jointly with every reference. -/
theorem decoderCode_borrowedRestored (t n : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State (Sampling.post t n) Reference History) :
    (decoderCode t n).BorrowedRestored Reference state
      ((decoderCode t n).execute Reference state) :=
  ClassicalRoutines.TerminalDecode.terminalDecode_routine_borrowedRestored
    (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
    Reference state

end

end QuantumAlg.OrderFinding.Exact

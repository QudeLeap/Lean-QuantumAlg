/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Construction
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Construction
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Context
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Borrowed restoration for complete measured Fourier execution

The Fourier input bank is a supplied mutable register. Its measurement is part
of the output contract, while every borrowed resource remains subject to the
separate complete-execution restoration obligation. The existing circuit law
applies because this interface has no borrowed quantum wires, including when
the input has an arbitrary external reference [GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

open Execution

noncomputable section

private lemma input_noBorrowedQuantum (n : Nat) :
    (inputContext n).borrowedQuantumWires = [] := rfl

/-- The actual allocation and adaptive circuit preserve the complete borrowed observation. -/
public lemma qftSemiclassical_complete_borrowedRestored {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (inputContext n) Reference (model.HiddenState × History)) :
    (completeCode inverse n).BorrowedRestored Reference state
      (((completeCode inverse n).execute environment) Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (completeCode inverse n) environment
    (input_noBorrowedQuantum n) Reference state

/-- Recording the initial store as mathematical history preserves the same restoration law. -/
public lemma qftSemiclassical_algorithm_restoresBorrowed {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat)
    {Reference : Register} (input : OracleInput .empty (inputContext n) Reference) :
    ((algorithm inverse n).run.RestoresBorrowed environment) input := by
  apply AlgorithmRun.restoresBorrowed_of_circuit
  intro reference history _ state
  exact qftSemiclassical_complete_borrowedRestored inverse n reference state

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

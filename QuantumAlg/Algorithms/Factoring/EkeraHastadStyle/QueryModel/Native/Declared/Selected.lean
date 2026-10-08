/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Born
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Selected.Store

/-!
# Selected declared short-DLP state with full store and reference

The parameter is read from the original classical store. The selected
model-owned query keeps that store and its complete external reference state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The stored parameter selects a declared member without replacing the
classical store or its reference operator. -/
theorem selected_execute (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History)) :
    (selected base noQuantum N input parameter).execute Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
          input (entry.1.read (Native.liftInput base noQuantum N parameter))).matrix
        (1 : UnitaryOperator Reference)).mapClassical
          (fun entry => (entry.1,
            (entry.2.1, (entry.2.2,
              ⟨entry.1.read (Native.liftInput base noQuantum N parameter), ()⟩)))) :=
  Circuit.selectedUnitary_execute _ _ state

/-- Each complete store retains its reference matrix and gains precisely the
declared short-DLP output vector selected by that store's parameter. -/
theorem selected_seed_entry (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (seeded : BasisSeeded.Holds
      (Native.context base noQuantum N).quantumLayout.zeroLabel state)
    (original : Store (Native.context base noQuantum N))
    (left right : (Native.context base noQuantum N).register.Index)
    (leftRef rightRef : Reference.Index) :
    (((selected base noQuantum N input parameter).execute Reference state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      (ShortDLP.BornProbability.evolvedState (Native.encoding input)
        (parameterUnit (original.read (Native.liftInput base noQuantum N parameter)))
        (parameterTarget (original.read (Native.liftInput base noQuantum N parameter)))).normalized
          (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N) left) *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          ((Native.context base noQuantum N).quantumLayout.zeroLabel, leftRef)
          ((Native.context base noQuantum N).quantumLayout.zeroLabel, rightRef) *
        star ((ShortDLP.BornProbability.evolvedState (Native.encoding input)
          (parameterUnit (original.read (Native.liftInput base noQuantum N parameter)))
          (parameterTarget
            (original.read (Native.liftInput base noQuantum N parameter)))).normalized
            (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N) right)) := by
  dsimp +instances only [selected]
  rw [Circuit.selectedUnitary_store_matrix]
  refine (BasisSeeded.unitary_entry
    (Native.context base noQuantum N).quantumLayout.zeroLabel state seeded
    (Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
      input (original.read (Native.liftInput base noQuantum N parameter))).matrix
    original left right leftRef rightRef).trans ?_
  rw [declared_member_zero_amplitude, declared_member_zero_amplitude]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

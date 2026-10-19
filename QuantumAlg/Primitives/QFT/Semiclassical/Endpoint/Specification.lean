/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Context
public import QuantumAlg.Primitives.QFT.Mathematics
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Execution.State.Requirement
public import QuantumAlg.Core.Execution.Reindex
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Context
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Util.FinPow.BitReverse

/-!
# Independent measured Fourier specification

The ideal target first applies the mathematical Fourier operator, then forgets
coherence between distinct measured bank labels. This specifies the entire
bank-reference density operator without mentioning the implementation circuit.
A second requirement ties each actual stored vector to its physical bank ket.
Together they determine the output probabilities and the complete conditional
reference blocks, admitting arbitrary mixed inputs and every external reference.
The reversed frequency label describes the retained physical wire order
[GN96, 9511007.tex:100-114,214-266].
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The mathematical Fourier matrix with its output rows in the retained physical wire order. -/
public def idealOperator (inverse : Bool) (n : Nat) : UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofPerm (qftReverseBitsPerm n) *
    (if inverse then (QFTOperator n)⁻¹ else QFTOperator n)

/-- The input's complete bank-reference state in the bank's explicit binary coordinates. -/
public def binaryInput (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    DensityOperator (Register.prod (Qubits n) Reference) :=
  input.state.quantumMarginal.reindex
    (Equiv.prodCongr (inputBasisEquiv n) (Equiv.refl Reference.Index))

/-- The independent Fourier action followed by ideal computational-basis dephasing. -/
public def idealBinaryState (inverse : Bool) (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    DensityOperator (Register.prod (Qubits n) Reference) :=
  ((ExecutionState.ofValue ()
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (idealOperator inverse n) (1 : UnitaryOperator Reference))
      (binaryInput n Reference input))).measureZ (fun basis => basis.1)).quantumMarginal

/-- Ideal measurement preserves the full input mass without normalizing individual outcomes. -/
public lemma qftSemiclassical_idealBinaryState_normalized
    (inverse : Bool) (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    (idealBinaryState inverse n Reference input).IsNormalized := by
  change (idealBinaryState inverse n Reference input).mass = 1
  unfold idealBinaryState binaryInput
  rw [ExecutionState.quantumMarginal_mass, ExecutionState.measureZ_mass,
    ExecutionState.ofValue_mass, DensityOperator.applyUnitary_mass,
    DensityOperator.reindex_mass, ExecutionState.quantumMarginal_mass]
  exact input.normalized

/-- Return those same mathematical matrix entries to the actual output bank's coordinates. -/
public def idealOutputState (inverse : Bool) (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    DensityOperator (Register.prod (outputContext n).register Reference) :=
  (idealBinaryState inverse n Reference input).reindex
    (Equiv.prodCongr (outputBasisEquiv n).symm (Equiv.refl Reference.Index))

/-- Observe every retained physical wire jointly with the arbitrary reference. -/
public def targetState (inverse : Bool) (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    DensityOperator (Register.prod
      ((outputContext n).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (outputContext n).quantumLayout
    Finset.univ Reference (idealOutputState inverse n Reference input)

private lemma targetState_normalized (inverse : Bool) (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    (targetState inverse n Reference input).IsNormalized := by
  change (targetState inverse n Reference input).mass = 1
  unfold targetState idealOutputState
  rw [DensityOperator.observeSelectionWithReference_mass, DensityOperator.reindex_mass]
  exact qftSemiclassical_idealBinaryState_normalized inverse n Reference input

/-- The unconditional bank-reference density fixes the ideal outcome weights and correlations. -/
public def instrumentRequirement (inverse : Bool) (n : Nat) :
    StateRequirement (inputContext n) (outputContext n) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (targetState inverse n Reference input)
      (targetState_normalized inverse n Reference input)

/-- A stored vector must describe its measured bank ket; the joint requirement fixes its weight. -/
public def storedResultRequirement (n : Nat) :
    StateRequirement (inputContext n) (outputContext n) :=
  .marginal Finset.univ (resultRead n) fun _ value =>
    .pure (NormalizedVector.ket
      ((outputContext n).quantumLayout.restrictSelectedBasis Finset.univ
        ((outputBasisEquiv n).symm (physicalLabel n value))))

/-- Independent worst-case native events: n Hadamards, at most n choose 2 phases, n measurements. -/
public def eventBudget (n : Nat) : ResourcePool model :=
  n • ResourcePool.singleton
      (model := .quantum SemiclassicalFourierGate.model .empty) (.gate .hadamard) +
    (n.choose 2) • ResourcePool.singleton
      (model := .quantum SemiclassicalFourierGate.model .empty) (.gate .phase) +
    n • ResourcePool.singleton
      (model := .quantum SemiclassicalFourierGate.model .empty) (.measurement (2 : ℕ+))

/-- All supplied systems and actual result bits remain resident. -/
public def residentBudget (n : Nat) : SpacePool .quantum
  | .classicalBits => n
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then n else 0

/-- Only the n retained classical results are auxiliary; no quantum system is allocated. -/
public def auxiliaryBudget (n : Nat) : SpacePool .quantum
  | .classicalBits => n
  | .quantumSystems _ => 0

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

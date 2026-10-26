/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Forward.Execution
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Direct paired EEA execution with arbitrary coherent original/reference correlations

One fixed actual program acts on any finite coherent family mixing the
original admitted active inputs and arbitrary original inactive sources.
Every physical pool and external flag belongs to the complete label.
No case chooses an executable backend or supplies a replacement operator.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

open scoped BigOperators

/-- Exactly the two original source-domain cases of the same controlled unitary. -/
inductive ForwardCase (modulus : Nat) where
  | active (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
      (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
      (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
      (flags : Bool × Bool) (selected : flags.1 = true)
  | disabled (state : ControlledFrame.Data modulus.size)
      (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
      (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false)
      (selected : state.2.1 = false)

namespace ForwardCase

def initial {modulus : Nat} : ForwardCase modulus → ControlledFrame.Data modulus.size
  | .active input _ _ _ pool _ _ _ flags _ =>
      ((InitialPortProgram.inputFrame modulus input, pool), flags)
  | .disabled state _ _ _ _ _ => state

def result {modulus : Nat} : ForwardCase modulus → ControlledFrame.Data modulus.size
  | .active input _ positive bounded pool _ _ _ flags _ =>
      ((SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool), flags)
  | .disabled state _ _ _ _ _ => state

/-- Each complete original label has the directly proved action of this same actual program. -/
lemma program_apply (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input : ForwardCase modulus) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding modulus.size).encode input.initial))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode input.result)) := by
  cases input with
  | active input coprime positive bounded pool addressZero prefixZero borrowZero flags selected =>
      exact program_initial_active_direct modulus nontrivial environment input coprime positive
        bounded pool addressZero prefixZero borrowZero flags selected
  | disabled state prefixZero addressZero borrowZero control selected =>
      exact program_apply_disabled_direct modulus nontrivial environment state
        prefixZero addressZero borrowZero control selected

/-- The actual adjoint of the same program reverses each complete original admitted label. -/
lemma dagger_apply (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input : ForwardCase modulus) :
    ((program modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
          (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((ControlledFrame.encoding modulus.size).encode input.result))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode input.initial)) :=
  EncodedBit.PredicateCompute.dagger_apply_encoded_ket_of_apply
    (encoding := ControlledFrame.encoding modulus.size) (program modulus nontrivial)
    environment input.initial input.result (program_apply modulus nontrivial environment input)

end ForwardCase

private lemma reference_ket_of_actual {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation) (initial final : layout.register.Index)
    (actual : body.applyNormalized environment (NormalizedVector.ket initial) =
      NormalizedVector.ket final) {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor (body.matrix environment) (1 : UnitaryOperator Reference) :
        HilbertOperator (layout.register.prod Reference))
        (NormalizedVector.ket (R := layout.register.prod Reference) (initial, reference)).vec =
      (NormalizedVector.ket (R := layout.register.prod Reference) (final, reference)).vec := by
  have pure := congrArg NormalizedVector.vec actual
  change (body.matrix environment).applyVec (NormalizedVector.ket initial).vec =
    (NormalizedVector.ket final).vec at pure
  change (UnitaryOperator.prodTensor (body.matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    pure, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

private lemma reference_sum_of_actual {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation) {Index : Type} [Fintype Index]
    (initial final : Index → layout.register.Index)
    (actual : ∀ index, body.applyNormalized environment (NormalizedVector.ket (initial index)) =
      NormalizedVector.ket (final index)) {Reference : Register}
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor (body.matrix environment) (1 : UnitaryOperator Reference) :
        HilbertOperator (layout.register.prod Reference))
        (∑ index, amplitude index • (NormalizedVector.ket
          (R := layout.register.prod Reference) (initial index, reference index)).vec) =
      ∑ index, amplitude index • (NormalizedVector.ket
        (R := layout.register.prod Reference) (final index, reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  exact congrArg (fun value => amplitude index • value)
    (reference_ket_of_actual body environment _ _ (actual index) (reference index))

/-- Full physical labels are retained beside arbitrary untouched reference labels. -/
def referenceVector (width : Nat) {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → ControlledFrame.Data width) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertVector (Register.prod
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum.register
      Reference) :=
  ∑ index, amplitude index • (NormalizedVector.ket
    (R := (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum.register.prod
      Reference) ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (state index)), reference index)).vec

/-- Arbitrary original active/inactive and dirty/reference correlations keep every amplitude. -/
lemma program_coherent_reference_direct (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (input : Index → ForwardCase modulus)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor ((program modulus nontrivial).matrix environment)
        (1 : UnitaryOperator Reference) : HilbertOperator
          (Register.prod
            (QubitLayout.canonical (ControlledFrame.encoding modulus.size).width).toQuantum.register
            Reference))
      (referenceVector modulus.size (fun index => (input index).initial) reference amplitude) =
        referenceVector modulus.size (fun index => (input index).result) reference amplitude :=
  reference_sum_of_actual (program modulus nontrivial) environment _ _
    (fun index => ForwardCase.program_apply modulus nontrivial environment (input index))
    reference amplitude

/-- The same actual unitary adjoint retains all coherent original/reference correlations. -/
lemma dagger_coherent_reference_direct (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (input : Index → ForwardCase modulus)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor
        (((program modulus nontrivial).dagger
          (AlgorithmGate.oracleFreeAdjoints .empty)).matrix environment)
        (1 : UnitaryOperator Reference) : HilbertOperator
          (Register.prod
            (QubitLayout.canonical (ControlledFrame.encoding modulus.size).width).toQuantum.register
            Reference))
      (referenceVector modulus.size (fun index => (input index).result) reference amplitude) =
        referenceVector modulus.size (fun index => (input index).initial) reference amplitude :=
  reference_sum_of_actual ((program modulus nontrivial).dagger
    (AlgorithmGate.oracleFreeAdjoints .empty)) environment _ _
    (fun index => ForwardCase.dagger_apply modulus nontrivial environment (input index))
    reference amplitude

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

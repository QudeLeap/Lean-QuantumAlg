/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Group.Action
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Stages
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Source
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Primitives.WalshHadamard.Pipeline
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact agreement of the new group-action gates with the existing Born state

The actual selected-unit programs map the unchanged uniform exponent
preparation and canonical two-word workspace to the original source graph
state. Exact vector equality preserves all source amplitudes and phases;
the ideal oracle appears only as the independent analysis target.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- The matrix column of every canonical clean input is fixed by the actual
`UnitaryCircuit.Realizes` proof for the same circuit used by accounting. -/
theorem compiledGroupActionProgram_matrix_clean
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (output :
      Fin
        (2 ^ (firstBits (registerParameters m ell width) + ell +
          workspaceBits width)))
    (a : Fin (2 ^ firstBits (registerParameters m ell width)))
    (b : Fin (2 ^ ell))
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    ((compiledGroupActionProgram m ell width N g x).binaryMatrix :
        HilbertOperator
          (Qubits
            (firstBits (registerParameters m ell width) + ell +
              workspaceBits width))) output
        (cleanLabel m ell width N a b 1) =
      if output =
          cleanLabel m ell width N a b
            (oracleValue g x a.val b.val) then
        1
      else
        0 := by
  let basis := (QubitLayout.canonical
    (totalQubits (registerParameters m ell width))).basisEquiv
  have haction := congrArg
    (fun state : NormalizedVector
        (QubitLayout.canonical
          (totalQubits (registerParameters m ell width))).toQuantum.register =>
      (state : HilbertVector
        (QubitLayout.canonical
          (totalQubits (registerParameters m ell width))).toQuantum.register)
        (basis.symm output))
    (compiledGroupActionProgram_applyLabel_clean
      m ell width N g x a b 1 hNgtOne hN)
  simp only [UnitaryCircuit.applyNormalized, UnitaryOperator.apply_coe,
    UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply, mul_one] at haction
  have labels :
      basis.symm output = basis.symm
        (cleanLabel m ell width N a b (oracleValue g x a.val b.val)) ↔
      output = cleanLabel m ell width N a b (oracleValue g x a.val b.val) :=
    basis.symm.injective.eq_iff
  change (compiledGroupActionProgram m ell width N g x).binaryMatrix output
      (cleanLabel m ell width N a b 1) =
    if basis.symm output = basis.symm
      (cleanLabel m ell width N a b (oracleValue g x a.val b.val)) then 1 else 0 at haction
  simpa only [labels] using haction

private theorem invSqrtCard_add (left right : Nat) :
    WalshHadamard.invSqrtCard (left + right) =
      WalshHadamard.invSqrtCard left * WalshHadamard.invSqrtCard right := by
  induction right with
  | zero => simp [WalshHadamard.invSqrtCard]
  | succ right ih =>
      rw [Nat.add_succ, WalshHadamard.invSqrtCard_succ, ih,
        WalshHadamard.invSqrtCard_succ]
      ring

/-- The actual native Hadamard prefix has its Walsh operator and leaves the
entire arithmetic workspace untouched. -/
theorem preparationCircuit_binaryMatrix (params : RegisterParameters) :
    (preparationCircuit params).binaryMatrix =
      (WalshHadamard.hadamardLayerOperator (firstBits params + params.ell)).tensor
        (1 : UnitaryOperator (Qubits params.workspaceBits)) := by
  rw [preparationCircuit, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  exact congrArg
    (fun operator : UnitaryOperator (Qubits (firstBits params + params.ell)) =>
      operator.tensor (1 : UnitaryOperator (Qubits params.workspaceBits)))
    (WalshHadamard.Native.native_binary_matrix .empty (firstBits params + params.ell))

/-- Native preparation produces the two source uniform exponent vectors for
any supplied computational-basis workspace, including the clean unit word. -/
theorem preparationCircuit_apply_basisWorkspace (params : RegisterParameters)
    (workspace : Fin (2 ^ params.workspaceBits)) :
    (preparationCircuit params).applyBinaryVec
        (NormalizedVector.ket (R := Qubits (totalQubits params))
          (tripleIndex params 0 0 workspace) :
          HilbertVector (Qubits (totalQubits params))) =
      HilbertVector.tensor
        (HilbertVector.tensor
          (WalshHadamard.uniformState (firstBits params) :
            HilbertVector (Qubits (firstBits params)))
          (WalshHadamard.uniformState params.ell : HilbertVector (Qubits params.ell)))
        (NormalizedVector.ket (R := Qubits params.workspaceBits) workspace :
          HilbertVector (Qubits params.workspaceBits)) := by
  have prepared :
      (preparationCircuit params).binaryMatrix.apply
          (NormalizedVector.ket
            (prodEquiv ((0 : Fin (2 ^ (firstBits params + params.ell))), workspace))) =
        (WalshHadamard.uniformState (firstBits params + params.ell)).tensor
          (NormalizedVector.ket (R := Qubits params.workspaceBits) workspace) := by
    rw [← NormalizedVector.tensor_ket, preparationCircuit_binaryMatrix,
      UnitaryOperator.tensor_apply_tensor,
      WalshHadamard.hadamardLayerOperator_apply_zero, UnitaryOperator.one_apply]
  have split :
      (WalshHadamard.uniformState (firstBits params + params.ell) :
        HilbertVector (Qubits (firstBits params + params.ell))) =
      HilbertVector.tensor
        (WalshHadamard.uniformState (firstBits params) :
          HilbertVector (Qubits (firstBits params)))
        (WalshHadamard.uniformState params.ell : HilbertVector (Qubits params.ell)) := by
    apply WithLp.ofLp_injective
    funext label
    rw [HilbertVector.tensor_apply, WalshHadamard.uniformState_apply,
      WalshHadamard.uniformState_apply, WalshHadamard.uniformState_apply,
      invSqrtCard_add]
  have zeroPair :
      prodEquiv ((0 : Fin (2 ^ firstBits params)), (0 : Fin (2 ^ params.ell))) =
        (0 : Fin (2 ^ (firstBits params + params.ell))) := by
    apply Fin.ext
    simp [prodEquiv]
  have raw := congrArg
    (fun state : NormalizedVector (Qubits (totalQubits params)) =>
      (state : HilbertVector (Qubits (totalQubits params)))) prepared
  simp only [UnitaryOperator.apply_coe, NormalizedVector.coe_tensor] at raw
  change (preparationCircuit params).binaryMatrix.applyVec
    (NormalizedVector.ket (R := Qubits (totalQubits params))
      (prodEquiv (prodEquiv (0, 0), workspace)) :
      HilbertVector (Qubits (totalQubits params))) = _
  rw [zeroPair, raw, split]

/-- The actual two-selected-exponentiation group-action circuit maps the physically prepared clean
workspace state to exactly the graph state used by the short-DLP Born analysis.
No oracle leaf or detached resource metadata occurs in this bridge. -/
theorem compiledGroupActionProgram_apply_preparation
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    (compiledGroupActionProgram m ell width N g x).applyBinaryVec
        ((preparationCircuit (registerParameters m ell width)).applyBinaryVec
          (NormalizedVector.ket
            (R := Qubits
              (totalQubits (registerParameters m ell width)))
            (tripleIndex (registerParameters m ell width) 0 0
              (cleanUnitLabel width N 1)) :
            HilbertVector
              (Qubits
                (totalQubits (registerParameters m ell width))))) =
      BornProbability.postOracleVec
        (unitEncoding width N hNgtOne hN) g x := by
  rw [preparationCircuit_apply_basisWorkspace]
  apply WithLp.ofLp_injective
  funext output
  let params := registerParameters m ell width
  let outputTriple := (tripleEquiv params).symm output
  change
    (∑ source : Fin
        (2 ^ (firstBits params + params.ell + params.workspaceBits)),
      (compiledGroupActionProgram m ell width N g x).binaryMatrix output source *
        HilbertVector.tensor
          (HilbertVector.tensor
            (WalshHadamard.uniformState (firstBits params) :
              HilbertVector (Qubits (firstBits params)))
            (WalshHadamard.uniformState params.ell :
              HilbertVector (Qubits params.ell)))
          (NormalizedVector.ket
            (R := Qubits params.workspaceBits)
            (cleanUnitLabel width N 1) :
            HilbertVector (Qubits params.workspaceBits)) source) =
      if outputTriple.2 =
          cleanUnitLabel width N
            (oracleValue g x outputTriple.1.1.val outputTriple.1.2.val) then
        WalshHadamard.invSqrtCard (firstBits params) *
          WalshHadamard.invSqrtCard params.ell
      else
        0
  rw [← Equiv.sum_comp
    (prodEquiv
      (m := firstBits params + params.ell)
      (n := params.workspaceBits)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp
    (prodEquiv (m := firstBits params) (n := params.ell)),
    Fintype.sum_prod_type]
  change
    (∑ sourceA : Fin (2 ^ firstBits params),
      ∑ sourceB : Fin (2 ^ params.ell),
        ∑ sourceWorkspace : Fin (2 ^ params.workspaceBits),
          (compiledGroupActionProgram m ell width N g x).binaryMatrix output
              (tripleIndex params sourceA sourceB sourceWorkspace) *
            HilbertVector.tensor
              (HilbertVector.tensor
                (WalshHadamard.uniformState (firstBits params) :
                  HilbertVector (Qubits (firstBits params)))
                (WalshHadamard.uniformState params.ell :
                  HilbertVector (Qubits params.ell)))
              (NormalizedVector.ket
                (R := Qubits params.workspaceBits)
                (cleanUnitLabel width N 1) :
                HilbertVector (Qubits params.workspaceBits))
              (tripleIndex params sourceA sourceB sourceWorkspace)) = _
  have htensor
      (sourceA : Fin (2 ^ firstBits params))
      (sourceB : Fin (2 ^ params.ell))
      (sourceWorkspace : Fin (2 ^ params.workspaceBits)) :
      HilbertVector.tensor
          (HilbertVector.tensor
            (WalshHadamard.uniformState (firstBits params) :
              HilbertVector (Qubits (firstBits params)))
            (WalshHadamard.uniformState params.ell :
              HilbertVector (Qubits params.ell)))
          (NormalizedVector.ket
            (R := Qubits params.workspaceBits)
            (cleanUnitLabel width N 1) :
            HilbertVector (Qubits params.workspaceBits))
          (tripleIndex params sourceA sourceB sourceWorkspace) =
        (WalshHadamard.invSqrtCard (firstBits params) *
            WalshHadamard.invSqrtCard params.ell) *
          (if sourceWorkspace = cleanUnitLabel width N 1 then 1 else 0) := by
    change
      HilbertVector.tensor
          (HilbertVector.tensor
            (WalshHadamard.uniformState (firstBits params) :
              HilbertVector (Qubits (firstBits params)))
            (WalshHadamard.uniformState params.ell :
              HilbertVector (Qubits params.ell)))
          (NormalizedVector.ket
            (R := Qubits params.workspaceBits)
            (cleanUnitLabel width N 1) :
            HilbertVector (Qubits params.workspaceBits))
          (prodEquiv (prodEquiv (sourceA, sourceB), sourceWorkspace)) = _
    rw [HilbertVector.tensor_apply_prod, HilbertVector.tensor_apply_prod,
      WalshHadamard.uniformState_apply,
      WalshHadamard.uniformState_apply,
      NormalizedVector.ket_apply]
  simp only [htensor, mul_ite, mul_zero, Fintype.sum_ite_eq']
  have hmatrix
      (sourceA : Fin (2 ^ firstBits params))
      (sourceB : Fin (2 ^ params.ell)) :
      (compiledGroupActionProgram m ell width N g x).binaryMatrix output
          (tripleIndex params sourceA sourceB
            (cleanUnitLabel width N 1)) =
        if output = tripleIndex params sourceA sourceB
            (cleanUnitLabel width N
              (oracleValue g x sourceA.val sourceB.val)) then 1 else 0 := by
    calc
      _ = (compiledGroupActionProgram m ell width N g x).binaryMatrix output
          (cleanLabel m ell width N sourceA sourceB 1) :=
        congrArg
          (fun source : Fin (2 ^ totalQubits params) =>
            (compiledGroupActionProgram m ell width N g x).binaryMatrix output source)
          (cleanLabel_eq_tripleIndex m ell width N sourceA sourceB 1).symm
      _ = if output = cleanLabel m ell width N sourceA sourceB
          (oracleValue g x sourceA.val sourceB.val) then 1 else 0 :=
        compiledGroupActionProgram_matrix_clean
          m ell width N g x output sourceA sourceB hNgtOne hN
      _ = _ := congrArg
        (fun target : Fin (2 ^ totalQubits params) =>
          if output = target then (1 : Complex) else 0)
        (cleanLabel_eq_tripleIndex m ell width N sourceA sourceB
          (oracleValue g x sourceA.val sourceB.val))
  simp_rw [hmatrix]
  have outputTriple_eq :
      tripleEquiv params outputTriple = output :=
    (tripleEquiv params).apply_symm_apply output
  have tripleEquiv_apply
      (first : Fin (2 ^ firstBits params))
      (second : Fin (2 ^ params.ell))
      (workspace : Fin (2 ^ params.workspaceBits)) :
      tripleEquiv params ((first, second), workspace) =
        tripleIndex params first second workspace :=
    rfl
  have output_eq_tripleIndex_iff
      (workspace : Fin (2 ^ params.workspaceBits)) :
      output = tripleIndex params outputTriple.1.1 outputTriple.1.2 workspace ↔
        outputTriple.2 = workspace := by
    constructor
    · intro heq
      have htuple :
          outputTriple =
            ((outputTriple.1.1, outputTriple.1.2), workspace) := by
        apply (tripleEquiv params).injective
        rw [outputTriple_eq, tripleEquiv_apply]
        exact heq
      exact congrArg (fun triple => triple.2) htuple
    · intro hworkspace
      calc
        output = tripleEquiv params outputTriple := outputTriple_eq.symm
        _ = tripleEquiv params
              ((outputTriple.1.1, outputTriple.1.2), outputTriple.2) := rfl
        _ = tripleIndex params outputTriple.1.1 outputTriple.1.2
              outputTriple.2 := tripleEquiv_apply _ _ _
        _ = tripleIndex params outputTriple.1.1 outputTriple.1.2 workspace := by
          rw [hworkspace]
  rw [Fintype.sum_eq_single outputTriple.1.1]
  · rw [Fintype.sum_eq_single outputTriple.1.2]
    · have hselected := output_eq_tripleIndex_iff
          (cleanUnitLabel width N
            (oracleValue g x outputTriple.1.1.val outputTriple.1.2.val))
      simp only [hselected]
      by_cases hclean : outputTriple.2 =
          cleanUnitLabel width N
            (oracleValue g x outputTriple.1.1.val outputTriple.1.2.val)
      · simp only [if_pos hclean, one_mul, mul_one]
      · simp only [if_neg hclean, zero_mul]
    · intro sourceB hne
      have hcond :
          ¬ output = tripleIndex params outputTriple.1.1 sourceB
            (cleanUnitLabel width N
              (oracleValue g x outputTriple.1.1.val sourceB.val)) := by
        intro heq
        have htuple :
            outputTriple =
              ((outputTriple.1.1, sourceB),
                cleanUnitLabel width N
                  (oracleValue g x outputTriple.1.1.val sourceB.val)) := by
          have heq' :
              output = tripleIndex (registerParameters m ell width)
                outputTriple.1.1 sourceB
                (cleanUnitLabel width N
                  (oracleValue g x outputTriple.1.1.val sourceB.val)) := by
            simpa only [params] using heq
          have htuple' :
              (tripleEquiv (registerParameters m ell width)).symm output =
                ((outputTriple.1.1, sourceB),
                  cleanUnitLabel width N
                    (oracleValue g x outputTriple.1.1.val sourceB.val)) := by
            apply (Equiv.symm_apply_eq
              (tripleEquiv (registerParameters m ell width))).2
            exact heq'
          simpa only [outputTriple, params] using htuple'
        have hsourceB : outputTriple.1.2 = sourceB :=
          congrArg (fun triple => triple.1.2) htuple
        exact hne hsourceB.symm
      simp only [if_neg hcond, zero_mul]
  · intro sourceA hne
    apply Finset.sum_eq_zero
    intro sourceB _
    have hcond :
        ¬ output = tripleIndex params sourceA sourceB
          (cleanUnitLabel width N
            (oracleValue g x sourceA.val sourceB.val)) := by
      intro heq
      have htuple :
          outputTriple =
            ((sourceA, sourceB),
              cleanUnitLabel width N
                (oracleValue g x sourceA.val sourceB.val)) := by
        have heq' :
            output = tripleIndex (registerParameters m ell width)
              sourceA sourceB
              (cleanUnitLabel width N
                (oracleValue g x sourceA.val sourceB.val)) := by
          simpa only [params] using heq
        have htuple' :
            (tripleEquiv (registerParameters m ell width)).symm output =
              ((sourceA, sourceB),
                cleanUnitLabel width N
                  (oracleValue g x sourceA.val sourceB.val)) := by
          apply (Equiv.symm_apply_eq
            (tripleEquiv (registerParameters m ell width))).2
          exact heq'
        simpa only [outputTriple, params] using htuple'
      have hsourceA : outputTriple.1.1 = sourceA :=
        congrArg (fun triple => triple.1.1) htuple
      exact hne hsourceA.symm
    simp only [if_neg hcond, zero_mul]

end

end QuantumAlg.ShortDLP.CompiledMAU

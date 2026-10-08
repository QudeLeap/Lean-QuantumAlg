/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.BornProbability.Amplitude
import all QuantumAlg.Primitives.ShortDLP.Measurement

/-!
# Terminal Born distribution of the declared short-DLP stage

The source Fourier-fiber formula is attached to the actual declared
prepare/query/readout circuit before measuring its exponent registers.
-/

section

namespace QuantumAlg

open NormalizedVector
open scoped BigOperators

noncomputable section

namespace ShortDLP
namespace BornProbability

/-- The normalized state produced by the complete declared short-DLP stage. -/
def evolvedState {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : QubitLayout.State (layout params) where
  state := PureState.ofNormalized
    ((DeclaredStage.circuit encoding g x).binaryMatrix.apply
      (NormalizedVector.ket (R := Qubits (totalQubits params))
        (prodEquiv
          ((0 : Fin (2 ^ (firstBits params + params.ell))),
            (0 : Fin (2 ^ params.workspaceBits))))))
    (layout params).systemIdx
  system_idx_eq := rfl

/-- Every terminal basis amplitude of the declared stage is the source's
explicit double inverse-Fourier sum. -/
theorem shortDLPCircuit_amplitude {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) :
    (evolvedState encoding g x).normalized
        (tripleEquiv params ((j, k), y)) =
      circuitAmplitude encoding g x j k y := by
  change (DeclaredStage.circuit encoding g x).binaryMatrix.applyVec
      (NormalizedVector.ket (R := Qubits (totalQubits params))
        (prodEquiv
          ((0 : Fin (2 ^ (firstBits params + params.ell))),
            (0 : Fin (2 ^ params.workspaceBits)))) :
        HilbertVector (Qubits (totalQubits params)))
      (tripleEquiv params ((j, k), y)) = _
  exact declaredCircuit_amplitude encoding g x j k y

/-! ## Terminal-measurement fibers -/


/-- Big-endian terminal outcome for the combined pair of exponent registers. -/
def shortDLPMeasurementOutcome (params : RegisterParameters)
    (value : Fin (2 ^ (firstBits params + params.ell))) : Outcome params :=
  fun outputIndex =>
    value.val.testBit
      (firstBits params + params.ell - 1 - outputIndex.val)

@[simp]
theorem fullRegisterIndex_shortDLPMeasurementOutcome
    (params : RegisterParameters)
    (value : Fin (2 ^ (firstBits params + params.ell))) :
    TerminalZMeasure.fullRegisterIndex
        (shortDLPMeasurementOutcome params value) = value := by
  apply Fin.val_injective
  change Nat.ofBits
      ((shortDLPMeasurementOutcome params value) ∘ Fin.rev) = value.val
  have hbits :
      (shortDLPMeasurementOutcome params value) ∘ Fin.rev =
        fun bit : Fin (firstBits params + params.ell) =>
          value.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, shortDLPMeasurementOutcome]
    apply congrArg value.val.testBit
    calc
      firstBits params + params.ell - 1 - (Fin.rev bit).val =
          firstBits params + params.ell - ((Fin.rev bit).val + 1) := by
        omega
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]

theorem shortDLPMeasurementOutcome_injective (params : RegisterParameters) :
    Function.Injective (shortDLPMeasurementOutcome params) := by
  intro left right h
  have hindex := congrArg TerminalZMeasure.fullRegisterIndex h
  simpa using hindex

private theorem shortDLPMeasurementOutcome_bijective
    (params : RegisterParameters) :
    Function.Bijective (shortDLPMeasurementOutcome params) := by
  apply (Fintype.bijective_iff_injective_and_card
    (shortDLPMeasurementOutcome params)).2
  refine ⟨shortDLPMeasurementOutcome_injective params, ?_⟩
  simp [Outcome]

@[simp]
theorem decodeOutcome_shortDLPMeasurementOutcome
    (params : RegisterParameters)
    (leftRight : Fin (2 ^ (firstBits params + params.ell))) :
    decodeOutcome params (shortDLPMeasurementOutcome params leftRight) =
      prodEquiv.symm leftRight := by
  simp [decodeOutcome]

@[simp]
theorem shortDLPMeasurement_readout_triple (params : RegisterParameters)
    (leftRight : Fin (2 ^ (firstBits params + params.ell)))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    (measurement params).readout (prodEquiv (leftRight, workspace)) =
      shortDLPMeasurementOutcome params leftRight := by
  funext outputIndex
  change (prodEquiv (leftRight, workspace)).val.testBit
      (totalQubits params - 1 - outputIndex.val) =
    leftRight.val.testBit
      (firstBits params + params.ell - 1 - outputIndex.val)
  have hindex :
      totalQubits params - 1 - outputIndex.val =
        params.workspaceBits +
          (firstBits params + params.ell - 1 - outputIndex.val) := by
    unfold totalQubits
    omega
  rw [hindex]
  exact prodEquiv_testBit_left leftRight workspace
    ⟨firstBits params + params.ell - 1 - outputIndex.val, by omega⟩

theorem shortDLPMeasurement_readout_eq_outcome_iff
    (params : RegisterParameters)
    (basis : Fin (2 ^ totalQubits params))
    (leftRight : Fin (2 ^ (firstBits params + params.ell))) :
    (measurement params).readout basis =
        shortDLPMeasurementOutcome params leftRight ↔
      (prodEquiv.symm basis).1 = leftRight := by
  have hself :
      (measurement params).readout basis =
        shortDLPMeasurementOutcome params (prodEquiv.symm basis).1 := by
    simpa using shortDLPMeasurement_readout_triple params
      (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro h
    exact shortDLPMeasurementOutcome_injective params (hself.symm.trans h)
  · intro h
    exact hself.trans (congrArg (shortDLPMeasurementOutcome params) h)

/-- Embed the unmeasured group-workspace basis into one exponent-readout
fiber. -/
def shortDLPMeasurementFiberEmbedding {params : RegisterParameters}
    (leftRight : Fin (2 ^ (firstBits params + params.ell))) :
    Fin (2 ^ params.workspaceBits) ↪ Fin (2 ^ totalQubits params) where
  toFun := fun workspace => prodEquiv (leftRight, workspace)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

@[simp]
theorem shortDLPMeasurementFiberEmbedding_apply
    {params : RegisterParameters}
    (leftRight : Fin (2 ^ (firstBits params + params.ell)))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    shortDLPMeasurementFiberEmbedding leftRight workspace =
      prodEquiv (leftRight, workspace) := rfl

theorem shortDLPMeasurement_fiber (params : RegisterParameters)
    (leftRight : Fin (2 ^ (firstBits params + params.ell))) :
    Finset.univ.filter
        (fun basis : Fin (2 ^ totalQubits params) =>
          (measurement params).readout basis =
            shortDLPMeasurementOutcome params leftRight) =
      Finset.univ.map (shortDLPMeasurementFiberEmbedding leftRight) := by
  ext basis
  rw [Finset.mem_filter,
    shortDLPMeasurement_readout_eq_outcome_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [shortDLPMeasurementFiberEmbedding_apply, ← hleft]
    exact (Equiv.apply_symm_apply
      (prodEquiv
        (m := firstBits params + params.ell)
        (n := params.workspaceBits)) basis)
  · intro hmem
    obtain ⟨workspace, _, hworkspace⟩ := Finset.mem_map.mp hmem
    change prodEquiv (leftRight, workspace) = basis at hworkspace
    rw [← hworkspace, Equiv.symm_apply_apply]

/-- The actual terminal Born probability is the marginal over the unmeasured
group workspace of the same stored circuit amplitude. -/
theorem shortDLPBornOutcomeProbability_eq_workspaceMarginal
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    (measurement params).outcomePMF (evolvedState encoding g x)
        (shortDLPMeasurementOutcome params (prodEquiv (j, k))) =
      ∑ workspace : Fin (2 ^ params.workspaceBits),
        ENNReal.ofReal
          (‖circuitAmplitude encoding g x j k workspace‖ ^ 2) := by
  classical
  rw [TerminalZMeasure.outcomePMF_apply,
    shortDLPMeasurement_fiber, Finset.sum_map]
  simp_rw [shortDLPMeasurementFiberEmbedding_apply]
  change (∑ workspace : Fin (2 ^ params.workspaceBits),
      ENNReal.ofReal
        (‖(evolvedState encoding g x).normalized
          (tripleEquiv params ((j, k), workspace))‖ ^ 2)) = _
  simp_rw [shortDLPCircuit_amplitude]

end BornProbability
end ShortDLP

end

end QuantumAlg

end

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Physical placement at an amplitude-estimation power stage

A supplied actual circuit has one leading control position and its source
positions. The canonical phase-power stage places that control among the
original phase wires and retains all other phase values unchanged. The only
input evidence concerns the supplied circuit's real physical positions;
its operator, native events and depth remain its own interpreted sequence.
-/

namespace QuantumAlg.AmplitudeEstimation.StagePlacement

noncomputable section

private def sourceWire {t : Nat} (stage : Fin t) (index : Nat) : Nat :=
  if index = 0 then qpeStagePrefixWidth stage else t + (index - 1)

private theorem sourceWire_injective {t : Nat} (stage : Fin t) :
    Function.Injective (sourceWire stage) := by
  intro left right same
  have beforeSystem : qpeStagePrefixWidth stage < t := by
    unfold qpeStagePrefixWidth
    omega
  by_cases leftZero : left = 0 <;> by_cases rightZero : right = 0 <;>
    simp only [sourceWire, leftZero, rightZero, if_true, if_false] at same <;> omega

/-- Place the control on its selected phase wire and the source on the final
`n` wires. Logical order here is still control followed by source. -/
def stageSource {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n))) (stage : Fin t) :
    UnitaryCircuit (Qubits (1 + n)) :=
  source.relabel
    { toFun := sourceWire stage
      map_layout := rfl
      old_nodup := source.physical_idx_nodup
      new_nodup := source.physical_idx_nodup.map (sourceWire_injective stage) }

private theorem stageSource_member {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t) {wire : Nat}
    (present : wire ∈ (stageSource source stage).physical_idx) :
    wire = qpeStagePrefixWidth stage ∨ t ≤ wire ∧ wire < t + n := by
  change wire ∈
    source.physical_idx.map
      (sourceWire stage) at present
  rw [placed] at present
  obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp present
  have indexBound := List.mem_range.mp inRange
  by_cases zeroIndex : index = 0
  · simp [sourceWire, zeroIndex]
  · right
    simp only [sourceWire, zeroIndex, if_false]
    omega

/-- The untouched lower phase wires, followed logically by control and source. -/
def stageSuffixBody {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (stage.val + (1 + n))) :=
  let suffix := UnitaryCircuit.identity (Qubits stage.val)
    (List.range' (qpeStagePrefixWidth stage + 1) stage.val) List.nodup_range'
  let selected := stageSource source stage
  UnitaryCircuit.tensorQubits suffix selected
    { left_nodup := suffix.physical_idx_nodup
      right_nodup := selected.physical_idx_nodup
      disjoint := by
        rw [List.disjoint_left]
        intro wire inSuffix inSource
        have suffixBounds := List.mem_range'.mp inSuffix
        have sourceBounds := stageSource_member source placed stage inSource
        have decomposition : qpeStagePrefixWidth stage + 1 + stage.val = t := by
          unfold qpeStagePrefixWidth
          omega
        rcases sourceBounds with atControl | inSystem <;> omega }

/-- The complete phase/source circuit before its explicit basis reassociation. -/
def stageRaw {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (qpeStagePrefixWidth stage + (stage.val + (1 + n)))) :=
  let leading := UnitaryCircuit.identity (Qubits (qpeStagePrefixWidth stage))
    (List.range (qpeStagePrefixWidth stage)) List.nodup_range
  let body := stageSuffixBody source placed stage
  UnitaryCircuit.tensorQubits leading body
    { left_nodup := leading.physical_idx_nodup
      right_nodup := body.physical_idx_nodup
      disjoint := by
        rw [List.disjoint_left]
        intro wire inPrefix inBody
        have prefixBound := List.mem_range.mp inPrefix
        change wire ∈ List.range' (qpeStagePrefixWidth stage + 1) stage.val ++
          (stageSource source stage).physical_idx at inBody
        rcases List.mem_append.mp inBody with inSuffix | inSource
        · have suffixBound := List.left_le_of_mem_range' inSuffix
          omega
        · have sourceBounds := stageSource_member source placed stage inSource
          have beforeSystem : qpeStagePrefixWidth stage < t := by
            unfold qpeStagePrefixWidth
            omega
          rcases sourceBounds with atControl | inSystem <;> omega }

private theorem stageRaw_contained {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t) :
    (stageRaw source placed stage).physical_idx ⊆ List.range (t + n) := by
  intro wire present
  change wire ∈ List.range (qpeStagePrefixWidth stage) ++
    (List.range' (qpeStagePrefixWidth stage + 1) stage.val ++
      (stageSource source stage).physical_idx) at present
  have decomposition : qpeStagePrefixWidth stage + 1 + stage.val = t := by
    unfold qpeStagePrefixWidth
    omega
  apply List.mem_range.mpr
  rcases List.mem_append.mp present with inPrefix | inBody
  · have bound := List.mem_range.mp inPrefix
    omega
  · rcases List.mem_append.mp inBody with inSuffix | inSource
    · have bound := List.mem_range'.mp inSuffix
      omega
    · have bounds := stageSource_member source placed stage inSource
      rcases bounds with atControl | inSystem <;> omega

/-- Move the control ahead of the suffix in the basis description, preserving
the individual control, suffix and source values. -/
def gapBasisEquiv (gap n : Nat) :
    Fin (2 ^ (gap + (1 + n))) ≃ Fin (2 ^ (1 + (gap + n))) :=
  (prodEquiv (m := gap) (n := 1 + n)).symm |>.trans
    (Equiv.prodCongr (Equiv.refl _) (prodEquiv (m := 1) (n := n)).symm) |>.trans
    (Equiv.prodAssoc (Fin (2 ^ gap)) (Fin 2) (Fin (2 ^ n))).symm |>.trans
    (Equiv.prodCongr (Equiv.prodComm (Fin (2 ^ gap)) (Fin 2)) (Equiv.refl _)) |>.trans
    (Equiv.prodAssoc (Fin 2) (Fin (2 ^ gap)) (Fin (2 ^ n))) |>.trans
    (Equiv.prodCongr (Equiv.refl _) (prodEquiv (m := gap) (n := n))) |>.trans
    (prodEquiv (m := 1) (n := gap + n))

/-- Reassociate all actual phase wires and the source into canonical order. -/
def stageBasisEquiv {t n : Nat} (stage : Fin t) :
    Fin (2 ^ (qpeStagePrefixWidth stage + (stage.val + (1 + n)))) ≃
      Fin (2 ^ (t + n)) :=
  (prodEquiv (m := qpeStagePrefixWidth stage) (n := stage.val + (1 + n))).symm |>.trans
    (Equiv.prodCongr (Equiv.refl _) (gapBasisEquiv stage.val n)) |>.trans
    (prodEquiv (m := qpeStagePrefixWidth stage) (n := 1 + (stage.val + n))) |>.trans
    (qpeStageReindexEquiv stage)

theorem stageBasisEquiv_apply {t n : Nat} (stage : Fin t)
    (leading : Fin (2 ^ qpeStagePrefixWidth stage)) (control : Fin 2)
    (suffix : Fin (2 ^ stage.val)) (system : Fin (2 ^ n)) :
    stageBasisEquiv stage (prodEquiv (leading, prodEquiv (suffix, prodEquiv (control, system)))) =
      prodEquiv (qpeStagePhaseEquiv stage (leading, control, suffix), system) := by
  calc
    _ = qpeStageReindexEquiv stage
        (prodEquiv (leading, prodEquiv (control, prodEquiv (suffix, system)))) := by
      simp [stageBasisEquiv, gapBasisEquiv]
    _ = _ := qpeStageReindexEquiv_apply stage leading control suffix system

theorem stageBasisEquiv_symm_apply {t n : Nat} (stage : Fin t)
    (leading : Fin (2 ^ qpeStagePrefixWidth stage)) (control : Fin 2)
    (suffix : Fin (2 ^ stage.val)) (system : Fin (2 ^ n)) :
    (stageBasisEquiv stage).symm
        (prodEquiv (qpeStagePhaseEquiv stage (leading, control, suffix), system)) =
      prodEquiv (leading, prodEquiv (suffix, prodEquiv (control, system))) := by
  apply (stageBasisEquiv stage).injective
  rw [Equiv.apply_symm_apply]
  exact (stageBasisEquiv_apply stage leading control suffix system).symm

/-- One actual control/source call with the canonical complete interface.
The final structural identity fixes interface order and emits no event. -/
def stageCall {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (t + n)) :=
  (UnitaryCircuit.reindex (stageBasisEquiv stage) (stageRaw source placed stage)).seq
    (UnitaryCircuit.identity (Qubits (t + n)) (List.range (t + n)) List.nodup_range)

theorem stageCall_physical_idx {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t) :
    (stageCall source placed stage).physical_idx = List.range (t + n) :=
  UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _
    (stageRaw_contained source placed stage)


/-- Relabeling positions retains the actual circuit's complete operator. -/
theorem stageSource_matrix {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (stage : Fin t) : (stageSource source stage).matrix = source.matrix := by
  apply Subtype.ext
  exact UnitaryCircuit.relabel_matrix _ _

/-- The structural full-interface identity contributes no change to the placed operator. -/
theorem stageCall_matrix_reindex {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t) :
    (stageCall source placed stage).matrix =
      UnitaryOperator.reindex (stageBasisEquiv stage) (stageRaw source placed stage).matrix := by
  apply Subtype.ext
  change (1 : HilbertOperator (Qubits (t + n))) * _ = _
  exact one_mul _

/-- Prefix and suffix values remain untouched around the actual control/source operation. -/
theorem stageCall_matrix_apply {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t)
    (prefixIn prefixOut : Fin (2 ^ qpeStagePrefixWidth stage))
    (controlIn controlOut : Fin 2) (suffixIn suffixOut : Fin (2 ^ stage.val))
    (systemIn systemOut : Fin (2 ^ n)) :
    (stageCall source placed stage).matrix
        (prodEquiv (qpeStagePhaseEquiv stage (prefixIn, controlIn, suffixIn), systemIn))
        (prodEquiv (qpeStagePhaseEquiv stage (prefixOut, controlOut, suffixOut), systemOut)) =
      if prefixIn = prefixOut then
        if suffixIn = suffixOut then
          source.matrix (prodEquiv (controlIn, systemIn)) (prodEquiv (controlOut, systemOut))
        else 0
      else 0 := by
  rw [stageCall_matrix_reindex, UnitaryOperator.coe_reindex,
    Matrix.reindex_apply, Matrix.submatrix_apply,
    stageBasisEquiv_symm_apply, stageBasisEquiv_symm_apply]
  rw [stageRaw, UnitaryCircuit.tensorQubits_matrix, UnitaryOperator.tensor_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [stageSuffixBody, UnitaryCircuit.tensorQubits_matrix, UnitaryOperator.tensor_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, stageSource_matrix]
  by_cases prefixEqual : prefixIn = prefixOut <;>
    by_cases suffixEqual : suffixIn = suffixOut <;> simp [prefixEqual, suffixEqual]

/-- A genuinely controlled source operator acts on exactly the original selected phase bit. -/
theorem stageCall_matrix_controlled {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (operator : UnitaryOperator (Qubits n))
    (controlled : source.matrix = UnitaryOperator.controlledQubits operator) (stage : Fin t) :
    (stageCall source placed stage).matrix = qpeControlledBitOp t operator stage := by
  calc
    _ = (qpeControlledPowerCallFull t operator stage).matrix := by
      ext row column
      obtain ⟨⟨phaseIn, systemIn⟩, rfl⟩ := (prodEquiv (m := t) (n := n)).surjective row
      obtain ⟨⟨phaseOut, systemOut⟩, rfl⟩ := (prodEquiv (m := t) (n := n)).surjective column
      obtain ⟨⟨prefixIn, controlIn, suffixIn⟩, rfl⟩ :=
        (qpeStagePhaseEquiv stage).surjective phaseIn
      obtain ⟨⟨prefixOut, controlOut, suffixOut⟩, rfl⟩ :=
        (qpeStagePhaseEquiv stage).surjective phaseOut
      rw [stageCall_matrix_apply]
      conv_rhs =>
        rw [← qpeStageReindexEquiv_apply stage prefixIn controlIn suffixIn systemIn]
        rw [← qpeStageReindexEquiv_apply stage prefixOut controlOut suffixOut systemOut]
      rw [qpeControlledPowerCallFull_matrix_apply, qpeControlledPowerCall_matrix_apply, controlled]
      simp only [UnitaryOperator.controlledQubits, UnitaryOperator.coe_reindex,
        Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        UnitaryOperator.controlled_apply]
      fin_cases controlIn <;> fin_cases controlOut <;>
        by_cases prefixEqual : prefixIn = prefixOut <;>
        by_cases suffixEqual : suffixIn = suffixOut <;>
        by_cases systemEqual : systemIn = systemOut <;>
        simp [qpeControlledPowerBody_matrix_apply, prefixEqual, suffixEqual, systemEqual]
    _ = _ := qpeControlledPowerCallFull_matrix t operator stage

/-- Physical placement preserves every actual native occurrence. -/
theorem stageCall_eventCost {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t) :
    (stageCall source placed stage).eventCost = source.eventCost := by
  simp only [stageCall, UnitaryCircuit.seq_eventCost, UnitaryCircuit.reindex_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero, stageRaw, stageSuffixBody,
    UnitaryCircuit.tensorQubits_eventCost, zero_add, stageSource,
    UnitaryCircuit.relabel_eventCost]

/-- Untouched phase positions add no duration under any actual native event weights. -/
theorem stageCall_evaluatedEventDepth {n t : Nat} (source : UnitaryCircuit (Qubits (1 + n)))
    (placed : source.physical_idx = List.range (1 + n)) (stage : Fin t)
    (weight : Resource.Event .quantum → Nat) :
    (stageCall source placed stage).evaluatedEventDepth weight =
      source.evaluatedEventDepth weight := by
  simp only [UnitaryCircuit.evaluatedEventDepth, stageCall, UnitaryCircuit.seq_eventDepth,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.identity_eventDepth, stageRaw,
    stageSuffixBody, UnitaryCircuit.tensorQubits_eventDepth, stageSource,
    UnitaryCircuit.relabel_eventDepth, DepthExpr.depthEval, Nat.zero_max, add_zero]

end

end QuantumAlg.AmplitudeEstimation.StagePlacement

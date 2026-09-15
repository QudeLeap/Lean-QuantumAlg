/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Basic
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Util.Real.ReciprocalSquareTail
import Mathlib.Data.Nat.Bitwise
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The actual QPE unitary and its mathematical Born readout

The initial Hadamard layer, explicit controlled-power ladder and inverse QFT
form one executable unitary. Its exact action on an eigenstate gives the
source geometric amplitudes and native query/readout counts
[Lin22, phaseestimation.tex:510-521,647-715].

The layout and Born readout below describe this mathematical state. Runtime
preparation, stored Z outcomes, complete Output and borrowed restoration
belong to the separate native endpoint; no execution engine is defined here.
-/

section

namespace QuantumAlg

open NormalizedVector Gate
open scoped BigOperators

noncomputable section

/-! ### One typed QPE circuit -/

/-- Canonical disjoint placement of a complete phase-register circuit and the
untouched eigenstate register. -/
theorem qpePhaseSystemLayout (t n : Nat) (phase : UnitaryCircuit (Qubits t))
    (hphase : phase.physical_idx = List.range t) :
    PhysicalLayout.DisjointMerge phase.physical_idx (List.range' t n) :=
  { left_nodup := phase.physical_idx_nodup
    right_nodup := List.nodup_range'
    disjoint := by
      rw [hphase, List.disjoint_left]
      intro index hleft hright
      have hlt := List.mem_range.mp hleft
      have hle := List.left_le_of_mem_range' hright
      omega }

/-- Hadamards on the phase register and structural identity on the eigenstate
register. -/
def qpePreparationCircuit (t n : Nat) : UnitaryCircuit (Qubits (t + n)) :=
  let system := UnitaryCircuit.identity (Qubits n) (List.range' t n) List.nodup_range'
  UnitaryCircuit.tensorQubits (WalshHadamard.hadamardLayer t) system
    (qpePhaseSystemLayout t n _ (WalshHadamard.hadamardLayer_physical_idx t))

private theorem qpe_range_append_range' (t n : Nat) :
    List.range t ++ List.range' t n = List.range (t + n) := by
  simpa [List.range_eq_range'] using
    (List.range'_append_1 (s := 0) (m := t) (n := n))

@[simp]
theorem qpePreparationCircuit_physical_idx (t n : Nat) :
    (qpePreparationCircuit t n).physical_idx = List.range (t + n) := by
  simp only [qpePreparationCircuit, UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex,
    UnitaryCircuit.tensor, PhysicalLayout.DisjointMerge.merged_eq_append,
    WalshHadamard.hadamardLayer_physical_idx]
  exact qpe_range_append_range' t n

namespace QuantumPhaseEstimation.EndpointDeclarations

/-- Stable opaque coordinate for the caller-supplied source unitary.  Quantum
control is added structurally by `UnitaryCircuit.control`; it is not baked into this
base declaration. -/
def qpeSourceUnitarySubroutineLabel (n : Nat) :
    QuantumAlg.Resource.SubroutineLabel where
  family := "qpe"
  name := "source-unitary"
  parameters := [n]

/-- Declared source-unitary endpoint at a caller-supplied placement. -/
def qpeSourceUnitaryLeafAt {n : Nat} (U : UnitaryOperator (Qubits n))
    (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.subroutine (qpeSourceUnitarySubroutineLabel n) systemIdx U

end QuantumPhaseEstimation.EndpointDeclarations

/-- The strict base source-unitary event. -/
public def qpeSourceUnitaryEvent (n : Nat) : Resource.Event .quantum :=
  .quantumSubroutine
    (QuantumPhaseEstimation.EndpointDeclarations.qpeSourceUnitarySubroutineLabel n).quantum

/-- The normalized one-qubit-controlled source-unitary event. -/
public def qpeControlledSourceUnitaryEvent (n : Nat) : Resource.Event .quantum :=
  (qpeSourceUnitaryEvent n).controlForDimension 2

/-- The base and controlled source-unitary coordinates are structurally
distinct. -/
theorem qpeSourceUnitaryEvent_ne_controlled (n : Nat) :
    qpeSourceUnitaryEvent n ≠ qpeControlledSourceUnitaryEvent n := by
  exact (Resource.Event.quantumSubroutine_controlForDimension_ne
    (QuantumPhaseEstimation.EndpointDeclarations.qpeSourceUnitarySubroutineLabel n)
    2).symm

/-- A nested control accumulates another normalized control dimension. -/
theorem qpeControlledSourceUnitaryEvent_nested (n : Nat) :
    (qpeControlledSourceUnitaryEvent n).controlForDimension 2 =
      (qpeSourceUnitaryEvent n).controlForDimensions [2, 2] := by
  simp [qpeControlledSourceUnitaryEvent]

/-- Source-unitary circuit on the borrowed eigenstate placement. -/
def qpeSourceUnitaryCircuit {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) : UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf
    (QuantumPhaseEstimation.EndpointDeclarations.qpeSourceUnitaryLeafAt U
      (List.range' t n))
    List.nodup_range'

@[simp] theorem qpeSourceUnitaryCircuit_physical_idx {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeSourceUnitaryCircuit t U).physical_idx = List.range' t n := rfl

@[simp] theorem qpeSourceUnitaryCircuit_eventCost {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeSourceUnitaryCircuit t U).eventCost =
      ResourcePool.singleton (qpeSourceUnitaryEvent n) := by
  rfl

/-- Number of phase wires preceding the little-endian stage bit in the
canonical big-endian physical layout. -/
def qpeStagePrefixWidth {t : Nat} (stage : Fin t) : Nat :=
  t - 1 - stage.val

theorem qpeStageWidth_eq {t n : Nat} (stage : Fin t) :
    qpeStagePrefixWidth stage + (1 + (stage.val + n)) = t + n := by
  unfold qpeStagePrefixWidth
  omega

theorem qpeStagePhaseWidth_eq {t : Nat} (stage : Fin t) :
    qpeStagePrefixWidth stage + (1 + stage.val) = t := by
  unfold qpeStagePrefixWidth
  omega

/-- Directional packed-index bridges retained for the subsequent reindex proofs. -/
@[simp, nolint simpNF] theorem qpe_prodEquiv_symm_apply_fst {m n : Nat}
    (left : Fin (2 ^ m)) (right : Fin (2 ^ n)) :
    ((prodEquiv (m := m) (n := n)).symm (prodEquiv (left, right))).1 = left := by
  rw [Equiv.symm_apply_apply]

@[simp, nolint simpNF] theorem qpe_prodEquiv_symm_apply_snd {m n : Nat}
    (left : Fin (2 ^ m)) (right : Fin (2 ^ n)) :
    ((prodEquiv (m := m) (n := n)).symm (prodEquiv (left, right))).2 = right := by
  rw [Equiv.symm_apply_apply]

/-- Pack the phase-register decomposition `prefix x (control x suffix)` back
into the canonical phase label. -/
def qpeStagePhaseEquiv {t : Nat} (stage : Fin t) :
    (Fin (2 ^ qpeStagePrefixWidth stage) ×
      (Fin (2 ^ 1) × Fin (2 ^ stage.val))) ≃ Fin (2 ^ t) :=
  ((Equiv.prodCongr (Equiv.refl _)
      (prodEquiv (m := 1) (n := stage.val))).trans
    (prodEquiv (m := qpeStagePrefixWidth stage)
      (n := 1 + stage.val))).trans
    (finCongr (congrArg (fun width : Nat => 2 ^ width)
      (qpeStagePhaseWidth_eq stage)))

/-- Reassociate the stage-local decomposition
`prefix x (control x (suffix x system))` into the canonical
`phase x system` basis order. -/
def qpeStageReindexEquiv {t n : Nat} (stage : Fin t) :
    Fin (2 ^ (qpeStagePrefixWidth stage + (1 + (stage.val + n)))) ≃
      Fin (2 ^ (t + n)) :=
  let splitPrefix := prodEquiv (m := qpeStagePrefixWidth stage)
    (n := 1 + (stage.val + n)) |>.symm
  let splitControl := Equiv.prodCongr (Equiv.refl _)
    (prodEquiv (m := 1) (n := stage.val + n)).symm
  let splitBody := Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.refl _)
      (prodEquiv (m := stage.val) (n := n)).symm)
  let reassociateBody := Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodAssoc (Fin (2 ^ 1)) (Fin (2 ^ stage.val))
      (Fin (2 ^ n))).symm
  let reassociateAll :=
    (Equiv.prodAssoc (Fin (2 ^ qpeStagePrefixWidth stage))
      (Fin (2 ^ 1) × Fin (2 ^ stage.val)) (Fin (2 ^ n))).symm
  splitPrefix |>.trans splitControl |>.trans splitBody |>.trans
    reassociateBody |>.trans reassociateAll |>.trans
    (Equiv.prodCongr (qpeStagePhaseEquiv stage) (Equiv.refl _)) |>.trans
    (prodEquiv (m := t) (n := n))

@[simp] theorem qpeStageReindexEquiv_apply {t n : Nat} (stage : Fin t)
    (phasePrefix : Fin (2 ^ qpeStagePrefixWidth stage))
    (control : Fin 2) (suffix : Fin (2 ^ stage.val))
    (system : Fin (2 ^ n)) :
    qpeStageReindexEquiv stage
        (prodEquiv (phasePrefix,
          prodEquiv (control, prodEquiv (suffix, system)))) =
      prodEquiv
        (qpeStagePhaseEquiv stage (phasePrefix, control, suffix), system) := by
  simp [qpeStageReindexEquiv]

@[simp] theorem qpeStageReindexEquiv_symm_apply {t n : Nat} (stage : Fin t)
    (phasePrefix : Fin (2 ^ qpeStagePrefixWidth stage))
    (control : Fin 2) (suffix : Fin (2 ^ stage.val))
    (system : Fin (2 ^ n)) :
    (qpeStageReindexEquiv stage).symm
        (prodEquiv
          (qpeStagePhaseEquiv stage (phasePrefix, control, suffix), system)) =
      prodEquiv (phasePrefix,
        prodEquiv (control, prodEquiv (suffix, system))) := by
  apply (qpeStageReindexEquiv stage).injective
  rw [Equiv.apply_symm_apply]
  exact (qpeStageReindexEquiv_apply stage phasePrefix control suffix system).symm

@[simp] theorem qpeStagePhaseEquiv_testBit {t : Nat} (stage : Fin t)
    (phasePrefix : Fin (2 ^ qpeStagePrefixWidth stage))
    (control : Fin (2 ^ 1)) (suffix : Fin (2 ^ stage.val)) :
    ((qpeStagePhaseEquiv stage
      (phasePrefix, control, suffix)).val.testBit stage.val).toNat =
      control.val := by
  change ((prodEquiv (phasePrefix, prodEquiv (control, suffix))).val.testBit
    stage.val).toNat = control.val
  rw [prodEquiv_testBit_right phasePrefix (prodEquiv (control, suffix))
    ⟨stage.val, by omega⟩]
  have highBit := prodEquiv_testBit_left control suffix ⟨0, by omega⟩
  simp only [Nat.add_zero] at highBit
  rw [highBit]
  fin_cases control <;> rfl

/-- The lower phase bits and the borrowed system form the controlled body.
The source-unitary leaf remains the only non-identity atom. -/
def qpeControlledPowerBody {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (stage.val + n)) :=
  let prefixWidth := qpeStagePrefixWidth stage
  let suffix := UnitaryCircuit.identity (Qubits stage.val)
    (List.range' (prefixWidth + 1) stage.val) List.nodup_range'
  let source := qpeSourceUnitaryCircuit t U
  UnitaryCircuit.tensorQubits suffix source
    { left_nodup := suffix.physical_idx_nodup
      right_nodup := source.physical_idx_nodup
      disjoint := by
        rw [List.disjoint_left]
        intro index hsuffix hsource
        have hsuffixBounds := List.mem_range'.mp hsuffix
        have hsourceBounds := List.mem_range'.mp hsource
        dsimp [prefixWidth] at hsuffixBounds
        have hprefix : qpeStagePrefixWidth stage + 1 + stage.val = t := by
          unfold qpeStagePrefixWidth
          omega
        omega }

/-- Explicitly bridge the product-register index carried by `UnitaryCircuit.control`
to the canonical packed qubit index. -/
def qpeControlFlattenEquiv (k : Nat) :
    (Register.prod (Qubits 1) (Qubits k)).Index ≃
      (Qubits (1 + k)).Index :=
  (Register.prodIndexEquiv (Qubits 1) (Qubits k)).symm |>.trans
    (prodEquiv (m := 1) (n := k))

/-- Directional controlled-coordinate bridge for the literal control matrix. -/
@[simp, nolint simpNF] private theorem qpe_controlled_prodIndexEquiv_apply {R : Register}
    (control : Register) (activationValue : control.Index)
    (U : UnitaryOperator R) (controlIn controlOut : control.Index)
    (bodyIn bodyOut : R.Index) :
    UnitaryOperator.controlled control activationValue U
        (Register.prodIndexEquiv control R (controlIn, bodyIn))
        (Register.prodIndexEquiv control R (controlOut, bodyOut)) =
      if controlIn = controlOut then
        if controlIn = activationValue then U bodyIn bodyOut
        else if bodyIn = bodyOut then 1 else 0
      else 0 := by
  rw [UnitaryOperator.controlled_apply]
  rfl

@[simp] theorem qpeControlFlattenEquiv_symm_apply (k : Nat)
    (control : Fin 2) (body : Fin (2 ^ k)) :
    (qpeControlFlattenEquiv k).symm (prodEquiv (control, body)) =
      Register.prodIndexEquiv (Qubits 1) (Qubits k) (control, body) := by
  simp [qpeControlFlattenEquiv]

/-- One genuine controlled source-unitary call on the stage wire.  This
definition mentions `UnitaryCircuit.control` directly so the normalized controlled
coordinate is derived by the circuit tree rather than supplied by QPE. -/
def qpeControlledPowerCall {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (1 + (stage.val + n))) :=
  let prefixWidth := qpeStagePrefixWidth stage
  let body := qpeControlledPowerBody t U stage
  let controlled := UnitaryCircuit.control (Qubits 1) [prefixWidth] body
    { left_nodup := by simp
      right_nodup := body.physical_idx_nodup
      disjoint := by
        rw [List.disjoint_left]
        intro index hcontrol hbody
        simp only [List.mem_singleton] at hcontrol
        subst index
        change prefixWidth ∈
          List.range' (prefixWidth + 1) stage.val ++ List.range' t n at hbody
        rcases List.mem_append.mp hbody with hsuffix | hsource
        · have hsuffixBounds := List.mem_range'.mp hsuffix
          omega
        · have hsourceBounds := List.mem_range'.mp hsource
          have hprefix : prefixWidth < t := by
            dsimp [prefixWidth, qpeStagePrefixWidth]
            omega
          omega }
    (activationValue := (1 : Fin 2))
  UnitaryCircuit.reindex (qpeControlFlattenEquiv (stage.val + n)) controlled

/-- One stage call lifted into the full phase-system register. -/
def qpeControlledPowerCallFull {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (t + n)) :=
  let prefixWidth := qpeStagePrefixWidth stage
  let prefixIdentity := UnitaryCircuit.identity (Qubits prefixWidth)
    (List.range prefixWidth) List.nodup_range
  let controlled := qpeControlledPowerCall t U stage
  let raw := UnitaryCircuit.tensorQubits prefixIdentity controlled
    { left_nodup := prefixIdentity.physical_idx_nodup
      right_nodup := controlled.physical_idx_nodup
      disjoint := by
        rw [List.disjoint_left]
        intro index hprefix hcontrolled
        have hprefixBound := List.mem_range.mp hprefix
        change index ∈ [qpeStagePrefixWidth stage] ++
          (List.range' (qpeStagePrefixWidth stage + 1) stage.val ++
            List.range' t n) at hcontrolled
        rcases List.mem_append.mp hcontrolled with htarget | hbody
        · simp only [List.mem_singleton] at htarget
          omega
        · rcases List.mem_append.mp hbody with hsuffix | hsource
          · have hsuffixBound := List.mem_range'.mp hsuffix
            omega
          · have hsourceBound := List.mem_range'.mp hsource
            have hprefixLe : qpeStagePrefixWidth stage ≤ t := by
              unfold qpeStagePrefixWidth
              omega
            omega }
  UnitaryCircuit.reindex (qpeStageReindexEquiv stage) raw

/-- Stage `s` contains exactly `2^s` genuine calls to its sealed controlled-U
leaf. -/
def qpeControlledPowerStage {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (t + n)) :=
  UnitaryCircuit.iterate (2 ^ stage.val)
    (qpeControlledPowerCallFull t U stage)

@[simp] theorem qpeControlledPowerCallFull_physical_idx {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    (qpeControlledPowerCallFull t U stage).physical_idx =
      List.range (t + n) := by
  simp only [qpeControlledPowerCallFull, qpeControlledPowerCall,
    qpeControlledPowerBody, qpeSourceUnitaryCircuit,
    UnitaryCircuit.reindex, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.tensor, UnitaryCircuit.control,
    UnitaryCircuit.controlAt, UnitaryCircuit.ofLeaf,
    PhysicalLayout.DisjointMerge.merged_eq_append]
  change List.range (qpeStagePrefixWidth stage) ++
      ([qpeStagePrefixWidth stage] ++
        (List.range' (qpeStagePrefixWidth stage + 1) stage.val ++
          List.range' t n)) = List.range (t + n)
  have hwidth : qpeStagePrefixWidth stage + 1 + stage.val = t := by
    unfold qpeStagePrefixWidth
    omega
  calc
    _ = ((List.range (qpeStagePrefixWidth stage) ++
          [qpeStagePrefixWidth stage]) ++
          List.range' (qpeStagePrefixWidth stage + 1) stage.val) ++
          List.range' t n := by simp [List.append_assoc]
    _ = (List.range (qpeStagePrefixWidth stage + 1) ++
          List.range' (qpeStagePrefixWidth stage + 1) stage.val) ++
          List.range' t n := by rw [List.range_succ]
    _ = List.range t ++ List.range' t n := by
      congr 1
      simpa [List.range_eq_range', hwidth, List.append_assoc] using
        (List.range'_append_1 (s := 0)
          (m := qpeStagePrefixWidth stage + 1) (n := stage.val))
    _ = List.range (t + n) := qpe_range_append_range' t n

/-- Structural controlled-power ladder in increasing binary-weight order. -/
def qpeControlledPowerCircuit {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) : UnitaryCircuit (Qubits (t + n)) :=
  UnitaryCircuit.indexedProductNamed "qpe-controlled-power-ladder" t
    (UnitaryCircuit.identity (Qubits (t + n)) (List.range (t + n)) List.nodup_range)
    (qpeControlledPowerStage t U)

@[simp]
theorem qpeControlledPowerStage_physical_idx {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    (qpeControlledPowerStage t U stage).physical_idx = List.range (t + n) := by
  rw [qpeControlledPowerStage, UnitaryCircuit.iterate]
  exact qpeControlledPowerCallFull_physical_idx t U stage

private theorem foldl_unionPhysicalIdx_eq_self (layout : List Nat)
    (layouts : List (List Nat)) (hlayouts : ∀ item ∈ layouts, item = layout) :
    layouts.foldl UnitaryCircuit.unionPhysicalIdx layout = layout := by
  induction layouts with
  | nil => rfl
  | cons head tail ih =>
      rw [List.foldl_cons, hlayouts head (by simp), UnitaryCircuit.unionPhysicalIdx_self]
      exact ih (fun item hitem => hlayouts item (by simp [hitem]))

@[simp]
theorem qpeControlledPowerCircuit_physical_idx {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeControlledPowerCircuit t U).physical_idx = List.range (t + n) := by
  rw [qpeControlledPowerCircuit, UnitaryCircuit.indexedProductNamed]
  apply foldl_unionPhysicalIdx_eq_self
  intro layout hlayout
  obtain ⟨stage, rfl⟩ := List.mem_ofFn.mp hlayout
  exact qpeControlledPowerStage_physical_idx t U stage

/-- Exponent contributed by one repeated binary-weight stage on one phase
basis label. -/
def qpeStageExponent {t : Nat} (stage : Fin t) (a : Fin (2 ^ t)) : Nat :=
  2 ^ stage.val * (a.val.testBit stage.val).toNat

/-- Pointwise exponent accumulator matching the right-fold execution order of
the indexed circuit product. -/
def qpeStageExponentFold {t : Nat} (stages : List (Fin t))
    (initial : Fin (2 ^ t) → Nat) : Fin (2 ^ t) → Nat :=
  stages.foldl
    (fun accumulated stage a => qpeStageExponent stage a + accumulated a)
    initial

theorem qpeStageExponentFold_apply {t : Nat} (stages : List (Fin t))
    (initial : Fin (2 ^ t) → Nat) (a : Fin (2 ^ t)) :
    qpeStageExponentFold stages initial a =
      initial a + (stages.map (fun stage => qpeStageExponent stage a)).sum := by
  induction stages generalizing initial with
  | nil => simp [qpeStageExponentFold]
  | cons stage stages ih =>
      rw [qpeStageExponentFold, List.foldl_cons]
      change qpeStageExponentFold stages
          (fun a => qpeStageExponent stage a + initial a) a = _
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm]

theorem qpeStageExponentFold_all {t : Nat} (a : Fin (2 ^ t)) :
    qpeStageExponentFold (List.ofFn fun stage : Fin t => stage)
        (fun _ => 0) a = a.val := by
  rw [qpeStageExponentFold_apply]
  simp only [zero_add]
  rw [show
      (List.ofFn fun stage : Fin t => stage).map
          (fun stage => qpeStageExponent stage a) =
        List.ofFn (fun stage : Fin t => qpeStageExponent stage a) by
    exact (List.ofFn_comp' (fun stage : Fin t => stage)
      (fun stage => qpeStageExponent stage a)).symm]
  rw [List.sum_ofFn]
  simp_rw [qpeStageExponent, Nat.mul_comm]
  rw [← natOfBits_eq_sum]
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt a.isLt]

/-- Packed-index semantics of one structurally controlled source call. -/
@[simp] theorem qpeControlledPowerCall_matrix_apply {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t)
    (controlIn controlOut : Fin 2)
    (suffixIn suffixOut : Fin (2 ^ stage.val))
    (systemIn systemOut : Fin (2 ^ n)) :
    (qpeControlledPowerCall t U stage).matrix
        (prodEquiv (controlIn, prodEquiv (suffixIn, systemIn)))
        (prodEquiv (controlOut, prodEquiv (suffixOut, systemOut))) =
      if controlIn = controlOut then
        if controlIn = 1 then
          (qpeControlledPowerBody t U stage).matrix
            (prodEquiv (suffixIn, systemIn))
            (prodEquiv (suffixOut, systemOut))
        else if prodEquiv (suffixIn, systemIn) =
            prodEquiv (suffixOut, systemOut) then 1 else 0
      else 0 := by
  unfold qpeControlledPowerCall
  rw [UnitaryCircuit.reindex_matrix]
  rw [UnitaryOperator.coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rw [qpeControlFlattenEquiv_symm_apply,
    qpeControlFlattenEquiv_symm_apply]
  rw [UnitaryCircuit.control, UnitaryCircuit.controlAt_matrix,
    qpe_controlled_prodIndexEquiv_apply]

/-- Packed-index semantics of the suffix identity tensored with the source
unitary. -/
@[simp] theorem qpeControlledPowerBody_matrix_apply {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t)
    (suffixIn suffixOut : Fin (2 ^ stage.val))
    (systemIn systemOut : Fin (2 ^ n)) :
    (qpeControlledPowerBody t U stage).matrix
        (prodEquiv (suffixIn, systemIn))
        (prodEquiv (suffixOut, systemOut)) =
      if suffixIn = suffixOut then U systemIn systemOut else 0 := by
  unfold qpeControlledPowerBody
  rw [UnitaryCircuit.tensorQubits_matrix, UnitaryOperator.tensor_apply]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases hsuffix : suffixIn = suffixOut <;>
    simp [hsuffix, qpeSourceUnitaryCircuit,
      QuantumPhaseEstimation.EndpointDeclarations.qpeSourceUnitaryLeafAt]

/-- Packed-index semantics after lifting one controlled call through the
leading phase-prefix identity and the stage reassociation. -/
@[simp, nolint simpNF] theorem qpeControlledPowerCallFull_matrix_apply {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t)
    (prefixIn prefixOut : Fin (2 ^ qpeStagePrefixWidth stage))
    (controlIn controlOut : Fin 2)
    (suffixIn suffixOut : Fin (2 ^ stage.val))
    (systemIn systemOut : Fin (2 ^ n)) :
    (qpeControlledPowerCallFull t U stage).matrix
        (qpeStageReindexEquiv stage
          (prodEquiv (prefixIn,
            prodEquiv (controlIn, prodEquiv (suffixIn, systemIn)))))
        (qpeStageReindexEquiv stage
          (prodEquiv (prefixOut,
            prodEquiv (controlOut, prodEquiv (suffixOut, systemOut))))) =
      if prefixIn = prefixOut then
        (qpeControlledPowerCall t U stage).matrix
          (prodEquiv (controlIn, prodEquiv (suffixIn, systemIn)))
          (prodEquiv (controlOut, prodEquiv (suffixOut, systemOut)))
      else 0 := by
  unfold qpeControlledPowerCallFull
  rw [UnitaryCircuit.reindex_matrix]
  rw [UnitaryOperator.coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [UnitaryCircuit.tensorQubits_matrix]
  rw [UnitaryOperator.tensor_apply]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases hprefix : prefixIn = prefixOut <;>
    simp [hprefix]

/-- The structurally controlled stage call denotes the customary block
controlled by the corresponding little-endian phase bit. -/
@[simp] theorem qpeControlledPowerCallFull_matrix {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    (qpeControlledPowerCallFull t U stage).matrix =
      qpeControlledBitOp t U stage := by
  ext i j
  rw [← Equiv.apply_symm_apply
      (prodEquiv (m := t) (n := n)) i,
    ← Equiv.apply_symm_apply
      (prodEquiv (m := t) (n := n)) j]
  generalize (prodEquiv (m := t) (n := n)).symm i = phaseSystemIn
  generalize (prodEquiv (m := t) (n := n)).symm j = phaseSystemOut
  rcases phaseSystemIn with ⟨phaseIn, systemIn⟩
  rcases phaseSystemOut with ⟨phaseOut, systemOut⟩
  rw [← Equiv.apply_symm_apply
      (qpeStagePhaseEquiv stage) phaseIn,
    ← Equiv.apply_symm_apply
      (qpeStagePhaseEquiv stage) phaseOut]
  generalize (qpeStagePhaseEquiv stage).symm phaseIn = phasePartsIn
  generalize (qpeStagePhaseEquiv stage).symm phaseOut = phasePartsOut
  rcases phasePartsIn with ⟨prefixIn, controlIn, suffixIn⟩
  rcases phasePartsOut with ⟨prefixOut, controlOut, suffixOut⟩
  conv_lhs =>
    rw [← qpeStageReindexEquiv_apply stage prefixIn controlIn suffixIn systemIn]
    rw [← qpeStageReindexEquiv_apply stage prefixOut controlOut suffixOut systemOut]
  rw [qpeControlledPowerCallFull_matrix_apply,
    qpeControlledPowerCall_matrix_apply]
  simp only [qpeControlledBitOp, qpeExponentOp_apply]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [qpeStagePhaseEquiv_testBit]
  fin_cases controlIn <;> fin_cases controlOut <;>
    by_cases hprefix : prefixIn = prefixOut <;>
    by_cases hsuffix : suffixIn = suffixOut <;>
    by_cases hsystem : systemIn = systemOut <;>
    simp [qpeControlledPowerBody_matrix_apply,
      hprefix, hsuffix, hsystem]

@[simp]
theorem qpeControlledPowerStage_matrix {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    (qpeControlledPowerStage t U stage).matrix =
      qpeExponentOp t U (qpeStageExponent stage) := by
  change (qpeControlledPowerCallFull t U stage).matrix ^ (2 ^ stage.val) = _
  rw [qpeControlledPowerCallFull_matrix]
  rw [qpeControlledBitOp, qpeExponentOp_pow]
  congr 1

theorem qpeControlledStageMatrixFold {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stages : List (Fin t))
    (initial : Fin (2 ^ t) → Nat) :
    (stages.map (fun stage => (qpeControlledPowerStage t U stage).matrix)).foldl
        (fun accumulated next => next * accumulated)
        (qpeExponentOp t U initial) =
      qpeExponentOp t U (qpeStageExponentFold stages initial) := by
  induction stages generalizing initial with
  | nil => rfl
  | cons stage stages ih =>
      rw [List.map_cons, List.foldl_cons, qpeControlledPowerStage_matrix,
        qpeExponentOp_mul]
      exact ih (fun a => qpeStageExponent stage a + initial a)

/-- The structural binary ladder denotes the usual block-diagonal `U^a`
operator; no detached operator metadata is stored in the circuit. -/
@[simp]
theorem qpeControlledPowerCircuit_matrix {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeControlledPowerCircuit t U).matrix = qpeControlledPowerOp t U := by
  change
    (List.ofFn (fun stage : Fin t =>
        (qpeControlledPowerStage t U stage).matrix)).foldl
          (fun accumulated next => next * accumulated) 1 = _
  rw [show (1 : UnitaryOperator (Qubits (t + n))) =
      qpeExponentOp t U (fun _ => 0) from (qpeExponentOp_zero t U).symm]
  rw [show List.ofFn (fun stage : Fin t =>
      (qpeControlledPowerStage t U stage).matrix) =
        (List.ofFn fun stage : Fin t => stage).map
          (fun stage => (qpeControlledPowerStage t U stage).matrix) by
    exact List.ofFn_comp' (fun stage : Fin t => stage)
      (fun stage => (qpeControlledPowerStage t U stage).matrix)]
  rw [qpeControlledStageMatrixFold]
  change qpeExponentOp t U
      (qpeStageExponentFold (List.ofFn fun stage : Fin t => stage)
        (fun _ => 0)) = qpeExponentOp t U Fin.val
  congr 1
  funext a
  exact qpeStageExponentFold_all a

private theorem qpe_sum_two_pow_range (t : Nat) :
    Finset.sum (Finset.range t) (fun s => 2 ^ s) = 2 ^ t - 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega

@[simp] theorem qpeControlledPowerCircuit_eventCost {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeControlledPowerCircuit t U).eventCost =
      (2 ^ t - 1) • ResourcePool.singleton
        (qpeControlledSourceUnitaryEvent n) := by
  rw [qpeControlledPowerCircuit, UnitaryCircuit.indexedProductNamed_eventCost,
    UnitaryCircuit.identity_eventCost]
  simp only [zero_add, qpeControlledPowerStage, UnitaryCircuit.iterate_eventCost]
  have hcall : ∀ stage : Fin t,
      (qpeControlledPowerCallFull t U stage).eventCost =
        ResourcePool.singleton (qpeControlledSourceUnitaryEvent n) := by
    intro stage
    simp [qpeControlledPowerCallFull, qpeControlledPowerCall,
      qpeControlledPowerBody, qpeSourceUnitaryCircuit,
      QuantumPhaseEstimation.EndpointDeclarations.qpeSourceUnitaryLeafAt,
      qpeControlledSourceUnitaryEvent, qpeSourceUnitaryEvent,
      UnitaryCircuit.tensorQubits, ResourcePool.controlForDimension]
  simp_rw [hcall]
  rw [Finset.sum_nsmul_assoc]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  exact qpe_sum_two_pow_range t

/-- Inverse QFT on the phase register and structural identity on the
eigenstate register. -/
def qpeReadoutFullCircuit (t n : Nat) : UnitaryCircuit (Qubits (t + n)) :=
  let system := UnitaryCircuit.identity (Qubits n) (List.range' t n) List.nodup_range'
  UnitaryCircuit.tensorQubits (qpeReadoutCircuit t) system
    (qpePhaseSystemLayout t n _ (by simp [qpeReadoutCircuit]))

@[simp]
theorem qpeReadoutFullCircuit_physical_idx (t n : Nat) :
    (qpeReadoutFullCircuit t n).physical_idx = List.range (t + n) := by
  simp only [qpeReadoutFullCircuit, UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex,
    UnitaryCircuit.tensor, PhysicalLayout.DisjointMerge.merged_eq_append]
  rw [show (qpeReadoutCircuit t).physical_idx = List.range t by
    simp [qpeReadoutCircuit]]
  exact qpe_range_append_range' t n

/-- Full structural QPE circuit: preparation, controlled powers, inverse-QFT
readout. -/
def qpeCircuit {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit (Qubits (t + n)) :=
  UnitaryCircuit.seq (qpePreparationCircuit t n)
    (UnitaryCircuit.seq (qpeControlledPowerCircuit t U) (qpeReadoutFullCircuit t n))

/-- Literal source order of the three circuit segments used by the canonical
QPE run. -/
@[simp] theorem qpeCircuit_eventTrace {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeCircuit t U).eventTrace =
      (qpePreparationCircuit t n).eventTrace ++
        (qpeControlledPowerCircuit t U).eventTrace ++
          (qpeReadoutFullCircuit t n).eventTrace := by
  rw [qpeCircuit, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace]
  rw [List.append_assoc]

/-- The full semantic operator is computed from the same three structural
circuit segments used for resource accounting. -/
@[simp]
theorem qpeCircuit_matrix {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeCircuit t U).matrix =
      (qpeReadoutFullCircuit t n).matrix * qpeControlledPowerOp t U *
        (qpePreparationCircuit t n).matrix := by
  apply Subtype.ext
  rw [qpeCircuit, UnitaryCircuit.seq_matrix, UnitaryCircuit.seq_matrix,
    qpeControlledPowerCircuit_matrix]
  rfl

@[simp] theorem qpeCircuit_physical_idx {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeCircuit t U).physical_idx = List.range (t + n) := by
  rw [qpeCircuit, UnitaryCircuit.seq]
  rw [UnitaryCircuit.seq]
  simp

@[simp] theorem qpeCircuit_eventCost {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (qpeCircuit t U).eventCost =
      ResourcePool.singleton WalshHadamard.hadamardEvent t +
        ((2 ^ t - 1) • ResourcePool.singleton
          (qpeControlledSourceUnitaryEvent n)) +
        (qpeReadoutCircuit t).eventCost := by
  simp [qpeCircuit, qpePreparationCircuit, qpeControlledPowerCircuit_eventCost,
    qpeReadoutFullCircuit, UnitaryCircuit.tensorQubits]
  ac_rfl

private theorem qftPhaseLayerPrefix_quantumSubroutineCount_zero
    (label : Resource.QuantumSubroutineLabel) (n count : Nat)
    (hcount : count ≤ n) :
    ResourcePool.count (.quantumSubroutine label)
        (qftPhaseLayerPrefix n count hcount).eventCost = 0 := by
  induction count with
  | zero => simp [qftPhaseLayerPrefix]
  | succ count ih =>
      rw [qftPhaseLayerPrefix, UnitaryCircuit.seq_eventCost,
        ResourcePool.count_add, ih (by omega)]
      change ResourcePool.count (.quantumSubroutine label)
          (ResourcePool.singleton (.gate qftControlledPhaseLabel)) = 0
      exact ResourcePool.count_singleton_of_ne (by
        intro equality
        cases equality) 1

private theorem qftBitReversePrefix_quantumSubroutineCount_zero
    (label : Resource.QuantumSubroutineLabel) (n count : Nat)
    (hcount : count ≤ n / 2) :
    ResourcePool.count (.quantumSubroutine label)
        (qftBitReversePrefix n count hcount).eventCost = 0 := by
  induction count with
  | zero => simp [qftBitReversePrefix]
  | succ count ih =>
      rw [qftBitReversePrefix, UnitaryCircuit.seq_eventCost,
        ResourcePool.count_add, ih (by omega)]
      change ResourcePool.count (.quantumSubroutine label)
          (ResourcePool.singleton (.gate (.builtin "swap"))) = 0
      exact ResourcePool.count_singleton_of_ne (by
        intro equality
        cases equality) 1

private theorem qftNoSwapCircuit_quantumSubroutineCount_zero
    (label : Resource.QuantumSubroutineLabel) (n : Nat) :
    ResourcePool.count (.quantumSubroutine label)
        (qftNoSwapCircuit n).eventCost = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ResourcePool.count (.quantumSubroutine label)
          ((qftLeadingHadamard n).eventCost +
            ((qftPhaseLayer n).eventCost +
              (qftTailLayer n (qftNoSwapCircuit n)
                (qftNoSwapCircuit_physical_idx n)).eventCost)) = 0
      rw [ResourcePool.count_add, ResourcePool.count_add]
      have leading : ResourcePool.count (.quantumSubroutine label)
          (qftLeadingHadamard n).eventCost = 0 := by
        change ResourcePool.count (.quantumSubroutine label)
            (ResourcePool.singleton WalshHadamard.hadamardEvent) = 0
        exact ResourcePool.count_singleton_of_ne (by
          intro equality
          cases equality) 1
      have phase : ResourcePool.count (.quantumSubroutine label)
          (qftPhaseLayer n).eventCost = 0 := by
        exact qftPhaseLayerPrefix_quantumSubroutineCount_zero label n n le_rfl
      have tail : ResourcePool.count (.quantumSubroutine label)
          (qftTailLayer n (qftNoSwapCircuit n)
            (qftNoSwapCircuit_physical_idx n)).eventCost = 0 := by
        simpa [qftTailLayer] using ih
      rw [leading, phase, tail]

private theorem qpeReadoutCircuit_quantumSubroutineCount_zero
    (label : Resource.QuantumSubroutineLabel) (t : Nat) :
    ResourcePool.count (.quantumSubroutine label)
        (qpeReadoutCircuit t).eventCost = 0 := by
  have noSwap := qftNoSwapCircuit_quantumSubroutineCount_zero label t
  have reverse := qftBitReversePrefix_quantumSubroutineCount_zero
    label t (t / 2) le_rfl
  change ResourcePool.count (.quantumSubroutine label)
      (QFTCircuit t).eventCost = 0
  rw [QFTCircuit,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  simpa [qftBitReverseCircuit] using congrArg₂ Nat.add noSwap reverse

/-- The exact controlled-source multiplicity is derived from the full QPE
circuit, including the proof that preparation and inverse-QFT readout do not
use that coordinate. -/
theorem qpeCircuit_controlledMultiplicity {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    ResourcePool.count (qpeControlledSourceUnitaryEvent n)
        (qpeCircuit t U).eventCost = 2 ^ t - 1 := by
  have readout : ResourcePool.count (qpeControlledSourceUnitaryEvent n)
      (qpeReadoutCircuit t).eventCost = 0 := by
    exact qpeReadoutCircuit_quantumSubroutineCount_zero
      ((QuantumPhaseEstimation.EndpointDeclarations.qpeSourceUnitarySubroutineLabel n).quantum
        |>.controlForDimension 2) t
  have preparation : ResourcePool.count (qpeControlledSourceUnitaryEvent n)
      (ResourcePool.singleton WalshHadamard.hadamardEvent t) = 0 := by
    exact ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) t
  have ladder : ResourcePool.count (qpeControlledSourceUnitaryEvent n)
      ((2 ^ t - 1) • ResourcePool.singleton
        (qpeControlledSourceUnitaryEvent n)) = 2 ^ t - 1 := by
    simp [ResourcePool.count, ResourcePool.singleton, Multiset.count_nsmul]
  rw [qpeCircuit_eventCost, ResourcePool.count_add,
    ResourcePool.count_add, preparation, ladder, readout]
  omega

/-- The full QPE circuit never pools a controlled source call into the base
source-unitary coordinate. -/
theorem qpeCircuit_baseMultiplicity {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    ResourcePool.count (qpeSourceUnitaryEvent n)
        (qpeCircuit t U).eventCost = 0 := by
  have readout : ResourcePool.count (qpeSourceUnitaryEvent n)
      (qpeReadoutCircuit t).eventCost = 0 := by
    simpa only [qpeSourceUnitaryEvent] using
      qpeReadoutCircuit_quantumSubroutineCount_zero
        (QuantumPhaseEstimation.EndpointDeclarations.qpeSourceUnitarySubroutineLabel n).quantum t
  have preparation : ResourcePool.count (qpeSourceUnitaryEvent n)
      (ResourcePool.singleton WalshHadamard.hadamardEvent t) = 0 := by
    exact ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) t
  have ladder : ResourcePool.count (qpeSourceUnitaryEvent n)
      ((2 ^ t - 1) • ResourcePool.singleton
        (qpeControlledSourceUnitaryEvent n)) = 0 := by
    simp [ResourcePool.count, ResourcePool.singleton,
      qpeSourceUnitaryEvent_ne_controlled n]
  rw [qpeCircuit_eventCost, ResourcePool.count_add,
    ResourcePool.count_add, preparation, ladder, readout]

/-- Metadata-free normalized QPE input with a zeroed phase register and the
supplied eigenstate. -/
def qpeInput {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    NormalizedVector (Qubits (t + n)) :=
  (NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t))).tensor P.eigenstate

private theorem qpeCircuit_apply_input_coe {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) :
    UnitaryCircuit.applyVec (qpeCircuit t P.unitary)
        (qpeInput P t : HilbertVector (Qubits (t + n))) =
      HilbertVector.tensor
        (UnitaryCircuit.applyVec (qpeReadoutCircuit t)
          (phaseState t P.phase : HilbertVector (Qubits t)))
        (P.eigenstate : HilbertVector (Qubits n)) := by
  have hprep :
      UnitaryCircuit.applyVec (qpePreparationCircuit t n)
          (qpeInput P t : HilbertVector (Qubits (t + n))) =
        HilbertVector.tensor
          (WalshHadamard.uniformState t : HilbertVector (Qubits t))
          (P.eigenstate : HilbertVector (Qubits n)) := by
    have hH :
        (WalshHadamard.hadamardLayer t).matrix.applyVec
            (NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t)) :
              HilbertVector (Qubits t)) =
          (WalshHadamard.uniformState t : HilbertVector (Qubits t)) :=
      by
        rw [WalshHadamard.hadamardLayer_matrix]
        exact congrArg (fun v : NormalizedVector (Qubits t) =>
          (v : HilbertVector (Qubits t)))
          WalshHadamard.hadamardLayerOperator_apply_zero
    rw [qpePreparationCircuit, qpeInput]
    change
      (UnitaryOperator.tensor (WalshHadamard.hadamardLayer t).matrix 1).applyVec
          (HilbertVector.tensor
            (NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t)) :
              HilbertVector (Qubits t))
            (P.eigenstate : HilbertVector (Qubits n))) = _
    rw [UnitaryOperator.tensor_applyVec_tensor, hH]
    change HilbertVector.tensor
        (WalshHadamard.uniformState t : HilbertVector (Qubits t))
        (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n))
          (P.eigenstate : HilbertVector (Qubits n))) = _
    rw [HilbertOperator.one_applyVec]
  have hcontrol :
      UnitaryCircuit.applyVec (qpeControlledPowerCircuit t P.unitary)
          (HilbertVector.tensor
            (WalshHadamard.uniformState t : HilbertVector (Qubits t))
            (P.eigenstate : HilbertVector (Qubits n))) =
        HilbertVector.tensor (phaseState t P.phase : HilbertVector (Qubits t))
          (P.eigenstate : HilbertVector (Qubits n)) := by
    change (qpeControlledPowerCircuit t P.unitary).matrix.applyVec _ = _
    rw [qpeControlledPowerCircuit_matrix]
    simpa using congrArg
      (fun ψ : NormalizedVector (Qubits (t + n)) =>
        (ψ : HilbertVector (Qubits (t + n))))
      (qpeControlledPowerOp_apply_uniform_eigenstate P t)
  have hreadout :
      UnitaryCircuit.applyVec (qpeReadoutFullCircuit t n)
          (HilbertVector.tensor (phaseState t P.phase : HilbertVector (Qubits t))
            (P.eigenstate : HilbertVector (Qubits n))) =
        HilbertVector.tensor
          (UnitaryCircuit.applyVec (qpeReadoutCircuit t)
            (phaseState t P.phase : HilbertVector (Qubits t)))
          (P.eigenstate : HilbertVector (Qubits n)) := by
    rw [qpeReadoutFullCircuit]
    change
      (UnitaryOperator.tensor (qpeReadoutCircuit t).matrix 1).applyVec
          (HilbertVector.tensor
            (phaseState t P.phase : HilbertVector (Qubits t))
            (P.eigenstate : HilbertVector (Qubits n))) = _
    rw [UnitaryOperator.tensor_applyVec_tensor]
    change HilbertVector.tensor
        (UnitaryCircuit.applyVec (qpeReadoutCircuit t)
          (phaseState t P.phase : HilbertVector (Qubits t)))
        (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n))
          (P.eigenstate : HilbertVector (Qubits n))) = _
    rw [HilbertOperator.one_applyVec]
  rw [qpeCircuit, UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq]
  rw [hprep, hcontrol, hreadout]

/-- The full QPE circuit maps its normalized input to the normalized tensor
of the inverse-QFT readout and the supplied eigenstate. -/
theorem qpeCircuit_applyNormalized_input {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) :
    UnitaryCircuit.applyNormalized (qpeCircuit t P.unitary) (qpeInput P t) =
      NormalizedVector.tensor
        (UnitaryCircuit.applyNormalized (qpeReadoutCircuit t) (phaseState t P.phase))
        P.eigenstate := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits (t + n)) => ψ i)
    (qpeCircuit_apply_input_coe P t)

/-! ### Canonical layout and terminal phase-register measurement -/

/-- Canonical physical placement of the phase and eigenstate registers. -/
def qpeLayout (t n : Nat) : QubitLayout (t + n) where
  physical_idx := fun i => i.val
  physical_idx_injective := fun _ _ h => Fin.ext h

@[simp] theorem qpeLayout_systemIdx (t n : Nat) :
    (qpeLayout t n).systemIdx = List.range (t + n) := by
  simp [qpeLayout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- Normalized, canonically placed QPE input. -/
def qpeInputState {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    QubitLayout.State (qpeLayout t n) where
  state := PureState.ofNormalized (qpeInput P t)
    (qpeLayout t n).systemIdx
  system_idx_eq := rfl

/-- Select the complete phase register in logical order. -/
def qpeMeasurement (t n : Nat) : TerminalZMeasure (qpeLayout t n) t :=
  zMeasureAt (qpeLayout t n)
    (fun i => ⟨i.val, Nat.lt_add_right n i.isLt⟩)
    (fun _ _ h => Fin.ext (Fin.mk.inj h))

/-- Big-endian terminal outcome corresponding to dyadic index `j`. -/
def qpeOutcome (t : Nat) (j : Fin (2 ^ t)) :
    TerminalZMeasure.Outcome t :=
  fun outputIndex => j.val.testBit (t - 1 - outputIndex.val)

/-- The canonical full-register big-endian decoder recovers the QPE phase-grid
index from its terminal bit vector. -/
@[simp] theorem qpeOutcome_fullRegisterIndex (t : Nat)
    (j : Fin (2 ^ t)) :
    TerminalZMeasure.fullRegisterIndex (qpeOutcome t j) = j := by
  apply Fin.val_injective
  change Nat.ofBits ((qpeOutcome t j) ∘ Fin.rev) = j.val
  have hbits :
      (qpeOutcome t j) ∘ Fin.rev =
        fun bit : Fin t => j.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, qpeOutcome]
    apply congrArg j.val.testBit
    calc
      t - 1 - (Fin.rev bit).val = t - ((Fin.rev bit).val + 1) := by
        rw [Nat.sub_sub, Nat.add_comm]
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt j.isLt]

theorem qpeOutcome_injective (t : Nat) :
    Function.Injective (qpeOutcome t) := by
  intro left right h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < t
  · let outputIndex : Fin t := ⟨t - 1 - bit, by omega⟩
    have hreverse : t - 1 - outputIndex.val = bit := by
      dsimp [outputIndex]
      omega
    have hout := congrFun h outputIndex
    simpa [qpeOutcome, hreverse] using hout
  · have htbit : t ≤ bit := Nat.le_of_not_gt hbit
    have hpow : 2 ^ t ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) htbit
    rw [Nat.testBit_eq_false_of_lt (left.isLt.trans_le hpow),
      Nat.testBit_eq_false_of_lt (right.isLt.trans_le hpow)]

@[simp] theorem qpeMeasurement_readout_prod {t n : Nat}
    (j : Fin (2 ^ t)) (y : Fin (2 ^ n)) :
    (qpeMeasurement t n).readout (prodEquiv (j, y)) = qpeOutcome t j := by
  funext outputIndex
  change (prodEquiv (j, y)).val.testBit
      (t + n - 1 - outputIndex.val) =
    j.val.testBit (t - 1 - outputIndex.val)
  have hindex :
      t + n - 1 - outputIndex.val = n + (t - 1 - outputIndex.val) := by
    omega
  rw [hindex]
  exact prodEquiv_testBit_left j y
    ⟨t - 1 - outputIndex.val, by omega⟩

theorem qpeMeasurement_readout_eq_outcome_iff {t n : Nat}
    (basis : Fin (2 ^ (t + n))) (j : Fin (2 ^ t)) :
    (qpeMeasurement t n).readout basis = qpeOutcome t j ↔
      (prodEquiv.symm basis).1 = j := by
  have hself :
      (qpeMeasurement t n).readout basis =
        qpeOutcome t (prodEquiv.symm basis).1 := by
    simpa using qpeMeasurement_readout_prod
      (n := n) (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro h
    exact qpeOutcome_injective t (hself.symm.trans h)
  · intro h
    exact hself.trans (congrArg (qpeOutcome t) h)

/-! ### Measurement probability from the evolved state -/

/-- The normalized state after the exact circuit stored in the algorithm run. -/
def qpeEvolvedState {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    QubitLayout.State (qpeLayout t n) :=
  { state := PureState.ofNormalized
      (UnitaryCircuit.applyNormalized (qpeCircuit t P.unitary) (qpeInput P t))
      (qpeLayout t n).systemIdx
    system_idx_eq := rfl }

theorem qpeEvolvedState_apply_prod {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat)
    (j : Fin (2 ^ t)) (y : Fin (2 ^ n)) :
    (qpeEvolvedState P t).normalized (prodEquiv (j, y)) =
      phaseRegisterGeometricAmplitude t P.phase j * P.eigenstate y := by
  change UnitaryCircuit.applyNormalized (qpeCircuit t P.unitary)
      (qpeInput P t) (prodEquiv (j, y)) = _
  rw [qpeCircuit_applyNormalized_input, NormalizedVector.tensor_apply_prod]
  change (invQFT t).apply (phaseState t P.phase) j * P.eigenstate y = _
  rw [invQFT_phaseState_apply_geometricSum]

/-- Embed the unmeasured eigenstate-register basis into one fixed phase-index
measurement fiber. -/
def qpeFiberEmbedding {t n : Nat} (j : Fin (2 ^ t)) :
    Fin (2 ^ n) ↪ Fin (2 ^ (t + n)) where
  toFun := fun y => prodEquiv (j, y)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

@[simp] theorem qpeFiberEmbedding_apply {t n : Nat} (j : Fin (2 ^ t))
    (y : Fin (2 ^ n)) :
    qpeFiberEmbedding j y = prodEquiv (j, y) := rfl

theorem qpeMeasurement_fiber {t n : Nat} (j : Fin (2 ^ t)) :
    Finset.univ.filter
        (fun basis : Fin (2 ^ (t + n)) =>
          (qpeMeasurement t n).readout basis = qpeOutcome t j) =
      Finset.univ.map (qpeFiberEmbedding j) := by
  ext basis
  rw [Finset.mem_filter, qpeMeasurement_readout_eq_outcome_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [qpeFiberEmbedding_apply, ← hleft]
    exact
      (Equiv.apply_symm_apply (prodEquiv (m := t) (n := n)) basis)
  · intro hmem
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hmem
    change prodEquiv (j, y) = basis at hy
    rw [← hy, Equiv.symm_apply_apply]

theorem qpeMeasurement_outcomePMF_apply {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) (j : Fin (2 ^ t)) :
    (qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)
        (qpeOutcome t j) =
      ENNReal.ofReal
        (‖phaseRegisterGeometricAmplitude t P.phase j‖ ^ 2) := by
  rw [TerminalZMeasure.outcomePMF_apply, qpeMeasurement_fiber,
    Finset.sum_map]
  simp_rw [qpeFiberEmbedding_apply, qpeEvolvedState_apply_prod, norm_mul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← Finset.mul_sum]
  have heigen :
      ∑ y : Fin (2 ^ n), ENNReal.ofReal (‖P.eigenstate y‖ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    rw [← EuclideanSpace.norm_sq_eq, P.eigenstate.norm_eq_one]
    norm_num
  rw [heigen, mul_one]

theorem qpeNearestOutcome_probability_ge {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) :
    ENNReal.ofReal (4 / Real.pi ^ 2) ≤
      (qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)
        (qpeOutcome t (qpeNearestIndex t P.phase)) := by
  rw [qpeMeasurement_outcomePMF_apply,
    phaseRegisterGeometricAmplitude_nearest_eq_errorAmplitude]
  apply ENNReal.ofReal_le_ofReal
  have hnorm := qpeErrorAmplitude_norm_lower_bound t (qpeRoundedError t P.phase)
    (qpeRoundedError_abs_le t P.phase)
  have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ 2 / Real.pi) hnorm
  calc
    4 / Real.pi ^ 2 = (2 / Real.pi) * (2 / Real.pi) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ ‖qpeErrorAmplitude t (qpeRoundedError t P.phase)‖ *
        ‖qpeErrorAmplitude t (qpeRoundedError t P.phase)‖ := hsquare
    _ = ‖qpeErrorAmplitude t (qpeRoundedError t P.phase)‖ ^ 2 := by ring

end

end QuantumAlg

end

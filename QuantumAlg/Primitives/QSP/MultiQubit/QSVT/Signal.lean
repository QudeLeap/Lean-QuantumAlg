/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
public import QuantumAlg.Components.Oracle.BlockEncoding
public import QuantumAlg.Util.Asymptotics
public import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition
import all QuantumAlg.Util.Asymptotics

/-!
# Hermitian QSVT endpoints

Hermitian block-encoding endpoints derived from projected QSVT.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder
open ReflectionQSPPhaseSynthesis

namespace QSVT



/-- Stable signal-oracle family for Hermitian QSVT resource accounting. -/
def hermitianQSVTOracleLabel : Resource.SubroutineLabel :=
  { family := "qsvt"
    name := "qsvt-hermitian-signal" }

























































/-- Source-facing Hermitian QSVT counters projected only from strict events.
Live qubits are deliberately absent and are reported through `SpacePool`. -/
public structure HermitianEventProfile where
  /-- Number of source Hermitian-oracle queries. -/
  oracleQueries : ℕ
  /-- Number of controlled Hermitian-oracle queries. -/
  controlledOracleQueries : ℕ
  /-- Number of elementary non-oracle events. -/
  elementaryEvents : ℕ
deriving DecidableEq

namespace HermitianEventProfile

@[ext] theorem ext (left right : HermitianEventProfile)
    (horacle : left.oracleQueries = right.oracleQueries)
    (hcontrolled : left.controlledOracleQueries = right.controlledOracleQueries)
    (helementary : left.elementaryEvents = right.elementaryEvents) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Recognize the structural QSVT signal family and return its explicit list
of control-register dimensions. -/
def signalControlDimensions : Resource.Event .quantum → Option (List ℕ)
  | .quantumSubroutine label =>
      if label.base.family = "qsvt" ∧ label.base.name = "qsvt-signal-unitary"
      then some label.controlDimensions else none
  | _ => none

/-- One for every direct, daggered, or structurally controlled signal event. -/
def signalQueryWeight (event : Resource.Event .quantum) : ℕ :=
  if (signalControlDimensions event).isSome then 1 else 0

/-- One exactly for a signal event carrying at least one control register. -/
def controlledSignalQueryWeight (event : Resource.Event .quantum) : ℕ :=
  match signalControlDimensions event with
  | some [] => 0
  | some (_ :: _) => 1
  | none => 0

/-- Every non-signal execution event contributes one local elementary-event
unit.  This is a QSVT-local projection, not a global resource conversion. -/
def elementaryEventWeight (event : Resource.Event .quantum) : ℕ :=
  if (signalControlDimensions event).isSome then 0 else 1

/-- Evaluate one explicitly supplied local event weight on a strict pool. -/
def weightedTotal (weight : Resource.Event .quantum → ℕ)
    (events : ResourcePool .quantum) : ℕ :=
  (events.map weight).sum

@[simp] theorem weightedTotal_zero (weight : Resource.Event .quantum → ℕ) :
    weightedTotal weight (0 : ResourcePool .quantum) = 0 := rfl

@[simp] theorem weightedTotal_add (weight : Resource.Event .quantum → ℕ)
    (left right : ResourcePool .quantum) :
    weightedTotal weight (left + right) =
      weightedTotal weight left + weightedTotal weight right := by
  simp [weightedTotal]

@[simp] theorem weightedTotal_singleton
    (weight : Resource.Event .quantum → ℕ)
    (event : Resource.Event .quantum) (multiplicity : ℕ) :
    weightedTotal weight (ResourcePool.singleton event multiplicity) =
      multiplicity * weight event := by
  simp [weightedTotal, ResourcePool.singleton]

@[simp] theorem signalQueryWeight_controlForDimension
    (event : Resource.Event .quantum) (dimension : ℕ) :
    signalQueryWeight (event.controlForDimension dimension) =
      signalQueryWeight event := by
  cases event with
  | quantumSubroutine label =>
      by_cases hsignal :
          label.base.family = "qsvt" ∧ label.base.name = "qsvt-signal-unitary"
      <;> simp [signalQueryWeight, signalControlDimensions,
        Resource.Event.controlForDimension,
        Resource.Event.controlForDimensions,
        Resource.QuantumSubroutineLabel.controlForDimensions, hsignal]
  | classicalOperation | classicalSubroutine | gate | preparation | measurement =>
      simp [signalQueryWeight, signalControlDimensions,
        Resource.Event.controlForDimension,
        Resource.Event.controlForDimensions]

@[simp] theorem controlledSignalQueryWeight_controlForDimension
    (event : Resource.Event .quantum) (dimension : ℕ) :
    controlledSignalQueryWeight (event.controlForDimension dimension) =
      signalQueryWeight event := by
  cases event with
  | quantumSubroutine label =>
      by_cases hsignal :
          label.base.family = "qsvt" ∧ label.base.name = "qsvt-signal-unitary"
      · have hnonempty : label.controlDimensions ++ [dimension] ≠ [] := by simp
        simp only [Resource.Event.controlForDimension,
          Resource.Event.controlForDimensions,
          Resource.QuantumSubroutineLabel.controlForDimensions,
          controlledSignalQueryWeight, signalQueryWeight,
          signalControlDimensions, hsignal, and_self, ↓reduceIte,
          Option.isSome_some]
        cases hcontrols : label.controlDimensions ++ [dimension] with
        | nil => exact (hnonempty hcontrols).elim
        | cons head tail => rfl
      · simp [controlledSignalQueryWeight, signalQueryWeight,
          signalControlDimensions, Resource.Event.controlForDimension,
          Resource.Event.controlForDimensions,
          Resource.QuantumSubroutineLabel.controlForDimensions, hsignal]
  | classicalOperation | classicalSubroutine | gate | preparation | measurement =>
      simp [controlledSignalQueryWeight, signalQueryWeight,
        signalControlDimensions, Resource.Event.controlForDimension,
        Resource.Event.controlForDimensions]

@[simp] theorem signalQueryWeight_controlForDimensions_singleton
    (event : Resource.Event .quantum) (dimension : ℕ) :
    signalQueryWeight (event.controlForDimensions [dimension]) =
      signalQueryWeight event := by
  simpa only [Resource.Event.controlForDimension] using
    signalQueryWeight_controlForDimension event dimension

@[simp] theorem controlledSignalQueryWeight_controlForDimensions_singleton
    (event : Resource.Event .quantum) (dimension : ℕ) :
    controlledSignalQueryWeight (event.controlForDimensions [dimension]) =
      signalQueryWeight event := by
  simpa only [Resource.Event.controlForDimension] using
    controlledSignalQueryWeight_controlForDimension event dimension

@[simp] theorem elementaryEventWeight_controlForDimension
    (event : Resource.Event .quantum) (dimension : ℕ) :
    elementaryEventWeight (event.controlForDimension dimension) =
      elementaryEventWeight event := by
  cases event with
  | quantumSubroutine label =>
      by_cases hsignal :
          label.base.family = "qsvt" ∧ label.base.name = "qsvt-signal-unitary"
      <;> simp [elementaryEventWeight, signalControlDimensions,
        Resource.Event.controlForDimension,
        Resource.Event.controlForDimensions,
        Resource.QuantumSubroutineLabel.controlForDimensions, hsignal]
  | classicalOperation | classicalSubroutine | gate | preparation | measurement =>
      simp [elementaryEventWeight, signalControlDimensions,
        Resource.Event.controlForDimension,
        Resource.Event.controlForDimensions]

@[simp] theorem elementaryEventWeight_controlForDimensions_singleton
    (event : Resource.Event .quantum) (dimension : ℕ) :
    elementaryEventWeight (event.controlForDimensions [dimension]) =
      elementaryEventWeight event := by
  simpa only [Resource.Event.controlForDimension] using
    elementaryEventWeight_controlForDimension event dimension

@[simp] theorem weightedTotal_signalQueryWeight_controlForDimension
    (dimension : ℕ) (events : ResourcePool .quantum) :
    weightedTotal signalQueryWeight
        (ResourcePool.controlForDimension dimension events) =
      weightedTotal signalQueryWeight events := by
  simp only [weightedTotal, ResourcePool.controlForDimension,
    ResourcePool.controlForDimensions, Multiset.map_map,
    Function.comp_apply, signalQueryWeight_controlForDimensions_singleton]

@[simp] theorem weightedTotal_controlledSignalQueryWeight_controlForDimension
    (dimension : ℕ) (events : ResourcePool .quantum) :
    weightedTotal controlledSignalQueryWeight
        (ResourcePool.controlForDimension dimension events) =
      weightedTotal signalQueryWeight events := by
  simp only [weightedTotal, ResourcePool.controlForDimension,
    ResourcePool.controlForDimensions, Multiset.map_map,
    Function.comp_apply,
    controlledSignalQueryWeight_controlForDimensions_singleton]

@[simp] theorem weightedTotal_elementaryEventWeight_controlForDimension
    (dimension : ℕ) (events : ResourcePool .quantum) :
    weightedTotal elementaryEventWeight
        (ResourcePool.controlForDimension dimension events) =
      weightedTotal elementaryEventWeight events := by
  simp only [weightedTotal, ResourcePool.controlForDimension,
    ResourcePool.controlForDimensions, Multiset.map_map,
    Function.comp_apply, elementaryEventWeight_controlForDimensions_singleton]

/-- Read the Hermitian counters from the typed circuit's strict event pool. -/
def ofEvents (events : ResourcePool .quantum) : HermitianEventProfile where
  oracleQueries := weightedTotal signalQueryWeight events
  controlledOracleQueries := weightedTotal controlledSignalQueryWeight events
  elementaryEvents := weightedTotal elementaryEventWeight events

/-- Exact same-circuit binding for a readable strict-event profile. -/
public def HasExactEvents (profile : HermitianEventProfile)
    (events : ResourcePool .quantum) : Prop :=
  ofEvents events = profile

/-- Exact closed counter claim for a strict-event profile. -/
public def HasExactCounts (profile : HermitianEventProfile)
    (oracleQueries controlledOracleQueries elementaryEvents : ℕ) : Prop :=
  profile.oracleQueries = oracleQueries ∧
    profile.controlledOracleQueries = controlledOracleQueries ∧
    profile.elementaryEvents = elementaryEvents

theorem ofEvents_hasExactEvents (events : ResourcePool .quantum) :
    HasExactEvents (ofEvents events) events := rfl

/-- Event-profile transformation induced by the explicit binary selector. -/
def binarySelector (left right : HermitianEventProfile) :
    HermitianEventProfile where
  oracleQueries := 2 * left.oracleQueries + right.oracleQueries
  controlledOracleQueries :=
    left.controlledOracleQueries + left.oracleQueries + right.oracleQueries
  elementaryEvents := 2 * left.elementaryEvents + right.elementaryEvents + 2

/-- Adding one closed non-signal phase event changes only the local elementary
projection. -/
def addElementaryEvent (profile : HermitianEventProfile) :
    HermitianEventProfile where
  oracleQueries := profile.oracleQueries
  controlledOracleQueries := profile.controlledOracleQueries
  elementaryEvents := profile.elementaryEvents + 1

end HermitianEventProfile

/-- Number of non-signal declared leaves in one structural matching-parity
branch.  Degree zero is the sealed scalar-dilation leaf; a positive branch has
two wrapper Hadamards and three non-signal leaves per phase slot. -/
public def matchingParityElementaryGates (L : Nat) : Nat :=
  if L = 0 then 1 else 3 * L + 2









/-- Strict-event target for one matching-parity Hermitian branch. -/
@[nolint unusedArguments]
def matchingParityEventProfile (_m L : Nat) : HermitianEventProfile where
  oracleQueries := L
  controlledOracleQueries := 0
  elementaryEvents := matchingParityElementaryGates L

/-- Strict-event target for the real matching-parity endpoint. -/
@[nolint unusedArguments]
public def realParityEventProfile (_m L : ℕ) : HermitianEventProfile where
  oracleQueries := L
  controlledOracleQueries := 0
  elementaryEvents := 3 * L + 2

/-- Strict-event target for the shared-control complex support shape. -/
@[nolint unusedArguments]
def hermitianComplexEventProfile (_m L : ℕ) : HermitianEventProfile where
  oracleQueries :=
    2 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
      ReflectionQSPPhaseSynthesis.oddBranchDegree L
  controlledOracleQueries :=
    ReflectionQSPPhaseSynthesis.evenBranchDegree L +
      ReflectionQSPPhaseSynthesis.oddBranchDegree L
  elementaryEvents :=
    2 * matchingParityElementaryGates
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) +
      matchingParityElementaryGates
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) + 2

/-- Strict-event target for the four-real-branch complex endpoint. -/
@[nolint unusedArguments]
public def hermitianComplexFourBranchEventProfile (_m L : ℕ) :
    HermitianEventProfile where
  oracleQueries :=
    6 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
      3 * ReflectionQSPPhaseSynthesis.oddBranchDegree L
  controlledOracleQueries :=
    5 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
      3 * ReflectionQSPPhaseSynthesis.oddBranchDegree L
  elementaryEvents :=
    6 * matchingParityElementaryGates
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) +
      3 * matchingParityElementaryGates
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) + 11







theorem realParityEventProfile_exact (m L : ℕ) :
    HermitianEventProfile.HasExactCounts
      (realParityEventProfile m L) L 0 (3 * L + 2) := by
  simp [HermitianEventProfile.HasExactCounts, realParityEventProfile]

theorem hermitianComplexEventProfile_exact (m L : ℕ) :
    HermitianEventProfile.HasExactCounts
      (hermitianComplexEventProfile m L)
      (2 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
        ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (ReflectionQSPPhaseSynthesis.evenBranchDegree L +
        ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (2 * matchingParityElementaryGates
          (ReflectionQSPPhaseSynthesis.evenBranchDegree L) +
        matchingParityElementaryGates
          (ReflectionQSPPhaseSynthesis.oddBranchDegree L) + 2) := by
  simp [HermitianEventProfile.HasExactCounts, hermitianComplexEventProfile]

theorem hermitianComplexFourBranchEventProfile_exact (m L : ℕ) :
    HermitianEventProfile.HasExactCounts
      (hermitianComplexFourBranchEventProfile m L)
      (6 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
        3 * ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (5 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
        3 * ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (6 * matchingParityElementaryGates
          (ReflectionQSPPhaseSynthesis.evenBranchDegree L) +
        3 * matchingParityElementaryGates
          (ReflectionQSPPhaseSynthesis.oddBranchDegree L) + 11) := by
  simp [HermitianEventProfile.HasExactCounts,
    hermitianComplexFourBranchEventProfile]







theorem matchingParityElementaryGates_le (L : Nat) :
    matchingParityElementaryGates L ≤ 3 * L + 2 := by
  simp only [matchingParityElementaryGates]
  split <;> omega



theorem matchingParityEventProfile_eq_realParityEventProfile {m L : Nat}
    (hL : 0 < L) :
    matchingParityEventProfile m L = realParityEventProfile m L := by
  apply HermitianEventProfile.ext <;>
    simp [matchingParityEventProfile, realParityEventProfile,
      matchingParityElementaryGates, Nat.ne_of_gt hL]







theorem realParityEventOracleQueries_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (realParityEventProfile m L).oracleQueries)
      (fun L : ℕ => L) := by
  simpa [NatBigO, realParityEventProfile, Function.id_def] using
    (NatBigO.refl (fun L : ℕ => L))

theorem hermitianComplexEventOracleQueries_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (hermitianComplexEventProfile m L).oracleQueries)
      (fun L : ℕ => L) := by
  apply NatBigO.of_eventually_le_const_mul 3
  filter_upwards with L
  simp only [hermitianComplexEventProfile]
  have he := ReflectionQSPPhaseSynthesis.evenBranchDegree_le L
  have ho := ReflectionQSPPhaseSynthesis.oddBranchDegree_le L
  omega

theorem hermitianComplexFourBranchEventOracleQueries_bigO (m : ℕ) :
    NatBigO
      (fun L : ℕ => (hermitianComplexFourBranchEventProfile m L).oracleQueries)
      (fun L : ℕ => L) := by
  apply NatBigO.of_eventually_le_const_mul 9
  filter_upwards with L
  simp only [hermitianComplexFourBranchEventProfile]
  have he := ReflectionQSPPhaseSynthesis.evenBranchDegree_le L
  have ho := ReflectionQSPPhaseSynthesis.oddBranchDegree_le L
  omega

theorem realParityElementaryEvents_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (realParityEventProfile m L).elementaryEvents)
      (fun L : ℕ => (m + 1) * L) := by
  apply NatBigO.of_eventually_le_const_mul 5
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with L hL
  simp only [realParityEventProfile]
  have hm : 1 ≤ m + 1 := by omega
  have hscale : L ≤ (m + 1) * L := by
    simpa using Nat.mul_le_mul_right L hm
  omega

theorem hermitianComplexElementaryEvents_bigO (m : ℕ) :
    NatBigO
      (fun L : ℕ => (hermitianComplexEventProfile m L).elementaryEvents)
      (fun L : ℕ => (m + 1) * L) := by
  apply NatBigO.of_eventually_le_const_mul 17
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with L hL
  simp only [hermitianComplexEventProfile]
  have he := ReflectionQSPPhaseSynthesis.evenBranchDegree_le L
  have ho := ReflectionQSPPhaseSynthesis.oddBranchDegree_le L
  have hge := matchingParityElementaryGates_le
    (ReflectionQSPPhaseSynthesis.evenBranchDegree L)
  have hgo := matchingParityElementaryGates_le
    (ReflectionQSPPhaseSynthesis.oddBranchDegree L)
  have hm : 1 ≤ m + 1 := by omega
  have hscale : L ≤ (m + 1) * L := by
    simpa using Nat.mul_le_mul_right L hm
  omega

theorem hermitianComplexFourBranchElementaryEvents_bigO (m : ℕ) :
    NatBigO
      (fun L : ℕ =>
        (hermitianComplexFourBranchEventProfile m L).elementaryEvents)
      (fun L : ℕ => (m + 1) * L) := by
  apply NatBigO.of_eventually_le_const_mul 56
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with L hL
  simp only [hermitianComplexFourBranchEventProfile]
  have he := ReflectionQSPPhaseSynthesis.evenBranchDegree_le L
  have ho := ReflectionQSPPhaseSynthesis.oddBranchDegree_le L
  have hge := matchingParityElementaryGates_le
    (ReflectionQSPPhaseSynthesis.evenBranchDegree L)
  have hgo := matchingParityElementaryGates_le
    (ReflectionQSPPhaseSynthesis.oddBranchDegree L)
  have hm : 1 ≤ m + 1 := by omega
  have hscale : L ≤ (m + 1) * L := by
    simpa using Nat.mul_le_mul_right L hm
  omega











/-! ### Hermitian QSVT endpoint contracts -/

/-- A lightweight source-level Hermitian QSVT circuit word.

The `signal` field is the source block-encoding oracle, while the output operator is
derived from `circuit.matrix`.  The canonical readable event profile is certified
against that same circuit's strict event ledger.  The certificate also keeps the source
block-encoding proof and public total-ancilla accounting (`m` source ancillas
plus `a` transformation ancillas), so endpoint theorems cannot silently forget
the input oracle. -/
public structure HermitianQSVTWord (m a n : Nat) (A : HilbertOperator (Qubits n)) where
  /-- Source block-encoding oracle used as the Hermitian QSVT signal. -/
  signal : UnitaryOperator (Qubits (m + n))
  /-- Typed output circuit carrying both semantics and resources. -/
  circuit : UnitaryCircuit (Qubits (a + n))
  sourceBlockEncoding : ExactBlockEncoding m n signal A
  /-- Transformation ancillas added on top of the source block-encoding ancillas. -/
  extraAncillaQubits : Nat
  /-- Total block ancillas exposed by the output block encoding. -/
  totalBlockAncilla : Nat
  totalBlockAncilla_eq : totalBlockAncilla = m + extraAncillaQubits
  /-- The output circuit's typed ancilla width is the advertised total. -/
  totalBlockAncilla_eq_a : totalBlockAncilla = a

namespace HermitianQSVTWord

/-- Canonical typed layout of the output circuit interface.  The word argument
fixes the indexed carrier while the layout depends only on its output width. -/
@[nolint unusedArguments]
def outputLayout {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (_word : HermitianQSVTWord m a n A) : QubitLayout (a + n) :=
  qsvtCanonicalQubitLayout (a + n)

/-- Live space of the typed output interface, kept separate from execution
events. -/
public def liveSpace {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) : SpacePool .quantum :=
  SpacePool.ofQuantumLayout word.outputLayout.toQuantumLayout

/-- Canonical typed layout of only the transformation ancillas. -/
def extraAncillaLayout {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) :
    QubitLayout word.extraAncillaQubits :=
  qsvtCanonicalQubitLayout word.extraAncillaQubits

/-- Transformation-ancilla capacity, never an event coordinate. -/
public def extraAncillaSpace {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) : SpacePool .quantum :=
  SpacePool.ofQuantumLayout word.extraAncillaLayout.toQuantumLayout

@[simp] theorem liveSpace_logicalQubits {m a n : Nat}
    {A : HilbertOperator (Qubits n)} (word : HermitianQSVTWord m a n A) :
    SpacePool.count (.quantumSystems 2) word.liveSpace = a + n := by
  exact (QubitLayout.toQuantumLayout_dimensionCount word.outputLayout 2).trans (if_pos rfl)

@[simp] theorem extraAncillaSpace_logicalQubits {m a n : Nat}
    {A : HilbertOperator (Qubits n)} (word : HermitianQSVTWord m a n A) :
    SpacePool.count (.quantumSystems 2) word.extraAncillaSpace =
      word.extraAncillaQubits := by
  exact (QubitLayout.toQuantumLayout_dimensionCount word.extraAncillaLayout 2).trans (if_pos rfl)

/-- The circuit carrier's ancilla width is exactly the source width plus the
proved transformation workspace. -/
theorem outputAncillaWidth_eq {m a n : Nat}
    {A : HilbertOperator (Qubits n)} (word : HermitianQSVTWord m a n A) :
    a = m + word.extraAncillaQubits := by
  calc
    a = word.totalBlockAncilla := word.totalBlockAncilla_eq_a.symm
    _ = m + word.extraAncillaQubits := word.totalBlockAncilla_eq

/-- Canonical readable counters projected from the stored circuit's strict
event ledger. -/
public def eventProfile {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) : HermitianEventProfile :=
  HermitianEventProfile.ofEvents word.circuit.eventCost

/-- The canonical profile is tied definitionally to the same typed circuit. -/
theorem circuit_events {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) :
    HermitianEventProfile.HasExactEvents word.eventProfile
      word.circuit.eventCost := rfl





/-- The word uses the registered source block encoding as its signal oracle. -/
public def UsesSignal {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A)
    (U : UnitaryOperator (Qubits (m + n))) : Prop :=
  word.signal = U

/-- Output semantics are derived, never stored independently. -/
def output {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) : UnitaryOperator (Qubits (a + n)) :=
  word.circuit.matrix

theorem output_matrix_eq {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) :
    (word.output : HilbertOperator (Qubits (a + n))) =
      (word.circuit.matrix : HilbertOperator (Qubits (a + n))) := rfl

/-- The derived output operator is the mathematical matrix of the stored circuit. -/
theorem output_eq_circuit_matrix {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) :
    (word.output : HilbertOperator (Qubits (a + n))) =
      (word.circuit.matrix : HilbertOperator (Qubits (a + n))) := rfl

end HermitianQSVTWord

/-- Circuit-level wrapper for the Hadamard phase ancilla and reassociation used
by Hermitian real-parity endpoints. The history keeps the projected-QSVT circuit
as a subhistory, instead of replacing it by an unrelated opaque output circuit. -/
noncomputable def phaseHadamardReassociateCircuit {m n : Nat}
    (body : UnitaryCircuit (Qubits (1 + (m + n)))) :
    UnitaryCircuit (Qubits ((1 + m) + n)) :=
  reassociatePhaseAncillaGate (m := m) (n := n) (phaseHadamardWrapper body)

@[simp]
theorem phaseHadamardReassociateCircuit_matrix {m n : Nat}
    (body : UnitaryCircuit (Qubits (1 + (m + n)))) :
    (phaseHadamardReassociateCircuit (m := m) (n := n) body).matrix =
      reassociatePhaseAncillaOperator (m := m) (n := n)
        (phaseHadamardWrapperOperator body.matrix) := by
  simp [phaseHadamardReassociateCircuit]



/-- Reassociation preserves the literal events and the wrapper contributes
the two actual Hadamard coordinates. -/
@[simp] theorem phaseHadamardReassociateCircuit_eventCost {m n : Nat}
    (body : UnitaryCircuit (Qubits (1 + (m + n)))) :
    (phaseHadamardReassociateCircuit (m := m) (n := n) body).eventCost =
      ResourcePool.singleton (.gate (.builtin "hadamard")) + body.eventCost +
        ResourcePool.singleton (.gate (.builtin "hadamard")) := by
  rw [phaseHadamardReassociateCircuit, reassociatePhaseAncillaGate,
    UnitaryCircuit.reindex_eventCost]
  simp [phaseHadamardWrapper, Gate.H, Gate.hadamardLeaf,
    Gate.hadamardLeafAt]



/-- Closed strict-event formula for the positive-degree real-parity circuit. -/
def realParityCircuitEvents (N L : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (.gate (.builtin "hadamard")) +
    qsvtProjectedCircuitEventResource N L +
    ResourcePool.singleton (.gate (.builtin "hadamard"))







/-- The strict projected-QSVT ledger contains one signal event per slot. -/
theorem qsvtProjectedCircuitEventResource_signalQueries (N L : Nat) :
    HermitianEventProfile.weightedTotal HermitianEventProfile.signalQueryWeight
        (qsvtProjectedCircuitEventResource N L) = L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      rw [qsvtProjectedCircuitEventResource]
      by_cases hparity : (L + 1) % 2 = 0 <;>
        simp [HermitianEventProfile.signalQueryWeight,
          HermitianEventProfile.signalControlDimensions,
          qsvtOracleEvent, qsvtOracleLabel, qsvtProjectorOracleEvent,
          qsvtProjectorOracleLabel, qsvtLeftProjectorOracleLabel,
          qsvtRightProjectorOracleLabel, qsvtControlledPhaseEvent,
          qsvtControlledPhaseLabel, hparity, ih]

/-- Projected matching-parity words do not structurally control the signal
event; projector subroutines remain separate coordinates. -/
theorem qsvtProjectedCircuitEventResource_controlledSignalQueries (N L : Nat) :
    HermitianEventProfile.weightedTotal
        HermitianEventProfile.controlledSignalQueryWeight
        (qsvtProjectedCircuitEventResource N L) = 0 := by
  induction L with
  | zero => rfl
  | succ L ih =>
      rw [qsvtProjectedCircuitEventResource]
      by_cases hparity : (L + 1) % 2 = 0 <;>
        simp [HermitianEventProfile.controlledSignalQueryWeight,
          HermitianEventProfile.signalControlDimensions,
          qsvtOracleEvent, qsvtOracleLabel, qsvtProjectorOracleEvent,
          qsvtProjectorOracleLabel, qsvtLeftProjectorOracleLabel,
          qsvtRightProjectorOracleLabel, qsvtControlledPhaseEvent,
          qsvtControlledPhaseLabel, hparity, ih]

/-- Each projected slot has two projector events and one phase event outside
the signal family. -/
theorem qsvtProjectedCircuitEventResource_elementaryEvents (N L : Nat) :
    HermitianEventProfile.weightedTotal
        HermitianEventProfile.elementaryEventWeight
        (qsvtProjectedCircuitEventResource N L) = 3 * L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      rw [qsvtProjectedCircuitEventResource]
      by_cases hparity : (L + 1) % 2 = 0 <;>
        simp [HermitianEventProfile.elementaryEventWeight,
          HermitianEventProfile.signalControlDimensions,
          qsvtOracleEvent, qsvtOracleLabel, qsvtProjectorOracleEvent,
          qsvtProjectorOracleLabel, qsvtLeftProjectorOracleLabel,
          qsvtRightProjectorOracleLabel, qsvtControlledPhaseEvent,
          qsvtControlledPhaseLabel, hparity, ih] <;> omega



/-- The real-parity source profile is computed from the strict events of the
explicit wrapper and projected word. -/
theorem realParityCircuitEvents_profile (m n L : Nat) :
    HermitianEventProfile.ofEvents (realParityCircuitEvents (m + n) L) =
      realParityEventProfile m L := by
  apply HermitianEventProfile.ext <;>
    simp [realParityCircuitEvents, realParityEventProfile,
      HermitianEventProfile.ofEvents,
      HermitianEventProfile.signalQueryWeight,
      HermitianEventProfile.controlledSignalQueryWeight,
      HermitianEventProfile.elementaryEventWeight,
      HermitianEventProfile.signalControlDimensions,
      qsvtProjectedCircuitEventResource_signalQueries,
      qsvtProjectedCircuitEventResource_controlledSignalQueries,
      qsvtProjectedCircuitEventResource_elementaryEvents]
  all_goals omega



/-- Circuit-level selector average of two branch circuits. -/
noncomputable def averageProjectedBlockCircuit {a n : Nat}
    (left right : UnitaryCircuit (Qubits (a + n))) :
    UnitaryCircuit (Qubits ((1 + a) + n)) :=
  averageProjectedBlockGate (a := a) (n := n) left right

@[simp]
theorem averageProjectedBlockCircuit_matrix {a n : Nat}
    (left right : UnitaryCircuit (Qubits (a + n))) :
    (averageProjectedBlockCircuit (a := a) (n := n) left right).matrix =
      averageProjectedBlockOperator (a := a) (n := n) left.matrix right.matrix := by
  simp [averageProjectedBlockCircuit]



/-- Exact strict-event ledger of the binary selector average. -/
@[simp] theorem averageProjectedBlockCircuit_eventCost {a n : Nat}
    (left right : UnitaryCircuit (Qubits (a + n))) :
    (averageProjectedBlockCircuit (a := a) (n := n) left right).eventCost =
      ResourcePool.singleton (.gate (.builtin "hadamard")) +
        (left.eventCost +
          ResourcePool.controlForDimension 2 (left.eventCost + right.eventCost)) +
        ResourcePool.singleton (.gate (.builtin "hadamard")) := by
  rw [averageProjectedBlockCircuit, averageProjectedBlockGate,
    reassociatePhaseAncillaGate, UnitaryCircuit.reindex_eventCost]
  simp [phaseHadamardWrapper, Gate.H, Gate.hadamardLeaf,
    Gate.hadamardLeafAt]



/-- The selector's readable counters are projected from its actual strict
events, preserving controlled signal coordinates. -/
theorem averageProjectedBlockCircuit_eventProfile {a n : Nat}
    (left right : UnitaryCircuit (Qubits (a + n))) :
    HermitianEventProfile.ofEvents
        (averageProjectedBlockCircuit (a := a) (n := n) left right).eventCost =
      HermitianEventProfile.binarySelector
        (HermitianEventProfile.ofEvents left.eventCost)
        (HermitianEventProfile.ofEvents right.eventCost) := by
  rw [averageProjectedBlockCircuit_eventCost]
  apply HermitianEventProfile.ext <;>
    simp [HermitianEventProfile.ofEvents,
      HermitianEventProfile.binarySelector,
      HermitianEventProfile.signalQueryWeight,
      HermitianEventProfile.controlledSignalQueryWeight,
      HermitianEventProfile.elementaryEventWeight,
      HermitianEventProfile.signalControlDimensions] <;>
    omega





/-- One explicit global phase primitive. -/
noncomputable def qsvtBranchPhase {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) : UnitaryCircuit R :=
  UnitaryCircuit.ofLeaf (qsvtBranchPhaseLeaf ζ hζ) (by
    simp [qsvtBranchPhaseLeaf, qsvtBranchPhaseLeafAt])

/-- The degree-zero scalar dilation is a sealed primitive with one fixed unit;
callers cannot attach an arbitrary resource profile to the semantic operator. -/
noncomputable def qsvtScalarDilationLeaf {m n : Nat} (c : ℂ)
    (hc : Complex.normSq c ≤ 1) : UnitaryLeaf (Qubits ((1 + m) + n)) :=
  qsvtScalarDilationLeafAt (m := m) (n := n) c hc
    (List.range ((1 + m) + n))



/-- One closed scalar-dilation circuit. -/
noncomputable def qsvtScalarDilationCircuit {m n : Nat} (c : ℂ)
    (hc : Complex.normSq c ≤ 1) : UnitaryCircuit (Qubits ((1 + m) + n)) :=
  UnitaryCircuit.ofLeaf (qsvtScalarDilationLeaf (m := m) (n := n) c hc) (by
    simpa only [qsvtScalarDilationLeaf, qsvtScalarDilationLeafAt,
      UnitaryLeaf.gate_systemIdx] using
      (List.nodup_range : (List.range ((1 + m) + n)).Nodup))



/-- The degree-zero scalar dilation contributes its one literal non-signal
event and no signal query. -/
theorem qsvtScalarDilationCircuit_eventProfile {m n : Nat} (c : ℂ)
    (hc : Complex.normSq c ≤ 1) :
    HermitianEventProfile.ofEvents
        (qsvtScalarDilationCircuit (m := m) (n := n) c hc).eventCost =
      matchingParityEventProfile m 0 := by
  apply HermitianEventProfile.ext <;>
    simp [qsvtScalarDilationCircuit, qsvtScalarDilationLeaf,
      qsvtScalarDilationLeafAt,
      matchingParityEventProfile, matchingParityElementaryGates,
      HermitianEventProfile.ofEvents,
      HermitianEventProfile.signalQueryWeight,
      HermitianEventProfile.controlledSignalQueryWeight,
      HermitianEventProfile.elementaryEventWeight,
      HermitianEventProfile.signalControlDimensions]

/-- Circuit-level global phase applied to one branch. -/
noncomputable def phaseScaledCircuit {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) (body : UnitaryCircuit R) :
    UnitaryCircuit R :=
  UnitaryCircuit.seq body (qsvtBranchPhase ζ hζ)



/-- A branch phase adds its literal strict event. -/
@[simp] theorem phaseScaledCircuit_eventCost {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) (body : UnitaryCircuit R) :
    (phaseScaledCircuit ζ hζ body).eventCost =
      body.eventCost + ResourcePool.singleton qsvtBranchPhaseEvent := by
  simp [phaseScaledCircuit, qsvtBranchPhase, qsvtBranchPhaseLeaf,
    qsvtBranchPhaseLeafAt, qsvtBranchPhaseEvent]



/-- The strict profile of a phased branch increments only the local
non-signal-event projection. -/
theorem phaseScaledCircuit_eventProfile {R : Register}
    (ζ : ℂ) (hζ : Complex.normSq ζ = 1) (body : UnitaryCircuit R) :
    HermitianEventProfile.ofEvents (phaseScaledCircuit ζ hζ body).eventCost =
      HermitianEventProfile.addElementaryEvent
        (HermitianEventProfile.ofEvents body.eventCost) := by
  rw [phaseScaledCircuit_eventCost]
  apply HermitianEventProfile.ext <;>
    simp [HermitianEventProfile.ofEvents,
      HermitianEventProfile.addElementaryEvent,
      HermitianEventProfile.signalQueryWeight,
      HermitianEventProfile.controlledSignalQueryWeight,
      HermitianEventProfile.elementaryEventWeight,
      HermitianEventProfile.signalControlDimensions,
      qsvtBranchPhaseEvent, qsvtBranchPhaseLabel]

@[simp]
theorem phaseScaledCircuit_matrix {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) (body : UnitaryCircuit R) :
    (phaseScaledCircuit ζ hζ body).matrix =
      phaseScaledOperator ζ hζ body.matrix := by
  apply Subtype.ext
  simp [phaseScaledCircuit, qsvtBranchPhase, qsvtBranchPhaseLeaf,
    qsvtBranchPhaseLeafAt, qsvtBranchPhaseOp, phaseScaledOperatorRaw]

/-- Circuit-level carrier for the source alternating phase sequence `U_Φ`. -/
noncomputable def sourceAlternatingPhaseCircuit {N : Nat}
    (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    UnitaryCircuit (Qubits N) :=
  sourceAlternatingPhaseModulation U left right phases

@[simp]
theorem sourceAlternatingPhaseCircuit_matrix {N : Nat}
    (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ((sourceAlternatingPhaseCircuit U left right phases).matrix :
      HilbertOperator (Qubits N)) =
      (sourceAlternatingPhaseModulation U left right phases :
        HilbertOperator (Qubits N)) := rfl

/-- Circuit-level selector average of four branch circuits. -/
noncomputable def fourWayAverageProjectedBlockCircuit {a n : Nat}
    (c00 c01 c10 c11 : UnitaryCircuit (Qubits (a + n))) :
    UnitaryCircuit (Qubits ((1 + (1 + a)) + n)) :=
  fourWayAverageProjectedBlockGate (a := a) (n := n) c00 c01 c10 c11

@[simp]
theorem fourWayAverageProjectedBlockCircuit_matrix {a n : Nat}
    (c00 c01 c10 c11 : UnitaryCircuit (Qubits (a + n))) :
    (fourWayAverageProjectedBlockCircuit (a := a) (n := n)
      c00 c01 c10 c11).matrix =
      fourWayAverageProjectedBlockOperator (a := a) (n := n)
        c00.matrix c01.matrix c10.matrix c11.matrix := by
  unfold fourWayAverageProjectedBlockCircuit fourWayAverageProjectedBlockGate
    fourWayAverageProjectedBlockOperator
  rw [averageProjectedBlockGate_matrix, averageProjectedBlockGate_matrix,
    averageProjectedBlockGate_matrix]



/-- The nested four-way selector profile is projected from its strict event
ledger at each selector layer. -/
theorem fourWayAverageProjectedBlockCircuit_eventProfile {a n : Nat}
    (c00 c01 c10 c11 : UnitaryCircuit (Qubits (a + n))) :
    HermitianEventProfile.ofEvents
        (fourWayAverageProjectedBlockCircuit (a := a) (n := n)
          c00 c01 c10 c11).eventCost =
      HermitianEventProfile.binarySelector
        (HermitianEventProfile.binarySelector
          (HermitianEventProfile.ofEvents c00.eventCost)
          (HermitianEventProfile.ofEvents c01.eventCost))
        (HermitianEventProfile.binarySelector
          (HermitianEventProfile.ofEvents c10.eventCost)
          (HermitianEventProfile.ofEvents c11.eventCost)) := by
  change HermitianEventProfile.ofEvents
      (averageProjectedBlockCircuit (a := 1 + a) (n := n)
        (averageProjectedBlockCircuit (a := a) (n := n) c00 c01)
        (averageProjectedBlockCircuit (a := a) (n := n) c10 c11)).eventCost = _
  rw [averageProjectedBlockCircuit_eventProfile,
    averageProjectedBlockCircuit_eventProfile,
    averageProjectedBlockCircuit_eventProfile]



/-- Circuit-level selector averaging preserves the complex even/odd block
encoding theorem while keeping the implementation carrier explicit. -/
theorem exactBlockEncoding_complexEvenOddDoubleAverageProjectedBlockCircuit
    {a n : Nat} (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    (evenCircuit oddCircuit : UnitaryCircuit (Qubits (a + n)))
    (hEven : ExactBlockEncoding a n evenCircuit.matrix
      (polynomialOperator ((2 : ℂ) • complexPolynomialEvenPart P) A))
    (hOdd : ExactBlockEncoding a n oddCircuit.matrix
      (polynomialOperator ((2 : ℂ) • complexPolynomialOddPart P) A)) :
    ExactBlockEncoding (1 + a) n
      (averageProjectedBlockCircuit (a := a) (n := n)
        evenCircuit oddCircuit).matrix
      (polynomialOperator P A) := by
  rw [averageProjectedBlockCircuit_matrix]
  exact exactBlockEncoding_complexEvenOddDoubleAverageProjectedBlockOperator
    (a := a) (n := n) P A hEven hOdd

/-- Circuit-level four-way selector averaging for the real/imaginary,
even/odd decomposition of a complex polynomial. -/
theorem exactBlockEncoding_complexFourPartAverageProjectedBlockCircuit
    {a n : Nat} (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    (reEvenCircuit reOddCircuit imEvenCircuit imOddCircuit :
      UnitaryCircuit (Qubits (a + n)))
    (hReEven : ExactBlockEncoding a n reEvenCircuit.matrix
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) A))
    (hReOdd : ExactBlockEncoding a n reOddCircuit.matrix
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) A))
    (hImEven : ExactBlockEncoding a n imEvenCircuit.matrix
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P))) A))
    (hImOdd : ExactBlockEncoding a n imOddCircuit.matrix
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P))) A)) :
    ExactBlockEncoding (1 + (1 + a)) n
      (fourWayAverageProjectedBlockCircuit (a := a) (n := n)
        reEvenCircuit reOddCircuit
        (phaseScaledCircuit Complex.I complex_normSq_I imEvenCircuit)
        (phaseScaledCircuit Complex.I complex_normSq_I imOddCircuit)).matrix
      ((1 / 4 : ℂ) • polynomialOperator P A) := by
  have hImEvenScaled :
      ExactBlockEncoding a n
        (phaseScaledCircuit Complex.I complex_normSq_I imEvenCircuit).matrix
        (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A) := by
    rw [phaseScaledCircuit_matrix]
    exact exactBlockEncoding_phaseScaledOperator
      Complex.I complex_normSq_I hImEven
  have hImOddScaled :
      ExactBlockEncoding a n
        (phaseScaledCircuit Complex.I complex_normSq_I imOddCircuit).matrix
        (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A) := by
    rw [phaseScaledCircuit_matrix]
    exact exactBlockEncoding_phaseScaledOperator
      Complex.I complex_normSq_I hImOdd
  have hAverage :=
    exactBlockEncoding_fourWayAverageProjectedBlockOperator
      (a := a) (n := n) hReEven hReOdd hImEvenScaled hImOddScaled
  have hCircuit :
      ExactBlockEncoding (1 + (1 + a)) n
        (fourWayAverageProjectedBlockCircuit (a := a) (n := n)
          reEvenCircuit reOddCircuit
          (phaseScaledCircuit Complex.I complex_normSq_I imEvenCircuit)
          (phaseScaledCircuit Complex.I complex_normSq_I imOddCircuit)).matrix
        ((1 / 4 : ℂ) • polynomialOperator
            (realPolynomialToComplex
              (realPolynomialEvenPart (complexPolynomialRealPart P))) A +
          (1 / 4 : ℂ) • polynomialOperator
            (realPolynomialToComplex
              (realPolynomialOddPart (complexPolynomialRealPart P))) A +
          ((1 / 4 : ℂ) • Complex.I • polynomialOperator
              (realPolynomialToComplex
                (realPolynomialEvenPart (complexPolynomialImagPart P))) A +
            (1 / 4 : ℂ) • Complex.I • polynomialOperator
              (realPolynomialToComplex
                (realPolynomialOddPart (complexPolynomialImagPart P))) A)) := by
    rw [fourWayAverageProjectedBlockCircuit_matrix]
    exact hAverage
  have htarget :
      (1 / 4 : ℂ) • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialRealPart P))) A +
        (1 / 4 : ℂ) • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialRealPart P))) A +
        ((1 / 4 : ℂ) • Complex.I • polynomialOperator
            (realPolynomialToComplex
              (realPolynomialEvenPart (complexPolynomialImagPart P))) A +
          (1 / 4 : ℂ) • Complex.I • polynomialOperator
            (realPolynomialToComplex
              (realPolynomialOddPart (complexPolynomialImagPart P))) A) =
        (1 / 4 : ℂ) • polynomialOperator P A := by
    simpa [smul_smul] using polynomialOperator_complex_fourPart_average_recompose P A
  constructor
  intro i j
  exact (hCircuit.block_entry i j).trans (congrFun (congrFun htarget i) j)

/-- Normalization-four block-encoding view of the same four-branch circuit. -/
theorem blockEncoding_complexFourPartAverageProjectedBlockCircuit
    {a n : Nat} (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    (reEvenCircuit reOddCircuit imEvenCircuit imOddCircuit :
      UnitaryCircuit (Qubits (a + n)))
    (hReEven : ExactBlockEncoding a n reEvenCircuit.matrix
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) A))
    (hReOdd : ExactBlockEncoding a n reOddCircuit.matrix
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) A))
    (hImEven : ExactBlockEncoding a n imEvenCircuit.matrix
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P))) A))
    (hImOdd : ExactBlockEncoding a n imOddCircuit.matrix
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P))) A)) :
    BlockEncoding 4 (1 + (1 + a)) n 0
      (fourWayAverageProjectedBlockCircuit (a := a) (n := n)
        reEvenCircuit reOddCircuit
        (phaseScaledCircuit Complex.I complex_normSq_I imEvenCircuit)
        (phaseScaledCircuit Complex.I complex_normSq_I imOddCircuit)).matrix
      (polynomialOperator P A) := by
  have hExact := exactBlockEncoding_complexFourPartAverageProjectedBlockCircuit
    (a := a) (n := n) P A reEvenCircuit reOddCircuit imEvenCircuit imOddCircuit
    hReEven hReOdd hImEven hImOdd
  have hExactScaled :
      ExactBlockEncoding (1 + (1 + a)) n
        (fourWayAverageProjectedBlockCircuit (a := a) (n := n)
          reEvenCircuit reOddCircuit
          (phaseScaledCircuit Complex.I complex_normSq_I imEvenCircuit)
          (phaseScaledCircuit Complex.I complex_normSq_I imOddCircuit)).matrix
        (((4 : ℝ)⁻¹ : ℂ) • polynomialOperator P A) := by
    simpa [one_div] using hExact
  exact ExactBlockEncoding.toScaledBlockEncoding
    (α := 4) (by norm_num) hExactScaled

/-- The zero-ancilla projected source block has the same top-left block as the
underlying source unitary.  This is the bookkeeping bridge from the source
projected statement to ordinary block-encoding notation. -/
theorem projectedBlock_sourceProjectedBlock_zeroAncilla {m n : Nat}
    (V : UnitaryOperator (Qubits (m + n))) :
    projectedBlock m n
        (sourceProjectedBlock (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) V) =
      projectedBlock m n (V : HilbertOperator (Qubits (m + n))) := by
  unfold sourceProjectedBlock
  rw [← zeroAncillaEmbeddedOperator_one (a := m) (n := n)]
  rw [projectedBlock_mul_zeroAncillaEmbeddedOperator_right]
  rw [projectedBlock_zeroAncillaEmbeddedOperator_mul_left]
  simp

/-- Source-level projected QSVT, specialized to an exact Hermitian block
encoding, yields an exact block encoding of the corresponding polynomial.

This is the endpoint form used by shared-control QSVT combinations: the branch
gate is the source alternating phase sequence itself, rather than an already
Hadamard-wrapped public-real branch [GSLW19, BlockHam.tex:768-887,1936-1952]. -/
theorem exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
    {m n d : Nat} {U : UnitaryOperator (Qubits (m + n))}
    {A : HilbertOperator (Qubits n)} {P : Polynomial ℂ}
    {phases : List ℝ}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hparity : HasParity P d)
    (hblock :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d P phases) :
    ExactBlockEncoding m n
      (sourceAlternatingPhaseModulation U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) phases).matrix
      (polynomialOperator P A) := by
  let zero := OrthogonalProjector.zeroAncilla m n
  constructor
  intro i j
  have hout : projectedOutputProjector zero zero d = zero := by
    simp [projectedOutputProjector]
  have hprojected := congrArg (projectedBlock m n) hblock
  have hsource :
      projectedBlock m n
          (sourceAlternatingPhaseModulation U zero zero phases :
            HilbertOperator (Qubits (m + n))) =
        projectedBlock m n
          (singularValuePolynomial zero d P
            (projectedUnitaryBlock zero zero U)) := by
    rw [← projectedBlock_sourceProjectedBlock_zeroAncilla
      (m := m) (n := n)
          (sourceAlternatingPhaseModulation U zero zero phases).matrix]
    simpa [zero, hout] using hprojected
  have henc :=
    (exactBlockEncoding_to_projectedUnitaryEncoding hbe).block_eq
  have htarget :
      projectedBlock m n
          (singularValuePolynomial zero d P
            (projectedUnitaryBlock zero zero U)) =
        polynomialOperator P A := by
    rw [henc]
    exact
      projectedBlock_singularValuePolynomial_zeroAncillaEmbeddedOperator_of_hermitian
        (a := m) (n := n) (L := d) P A hA hparity
  have htop :
      projectedBlock m n
          (sourceAlternatingPhaseModulation U zero zero phases :
            HilbertOperator (Qubits (m + n))) =
        polynomialOperator P A := by
    rw [hsource, htarget]
  exact congrFun (congrFun htop i) j

/-- Four source-level projected-QSVT branches can be averaged with two shared
selector ancillas.  Unlike the fallback `m+3` bookkeeping theorem, each branch
here is the source alternating phase sequence itself, so the output has exactly
`m+2` block-encoding ancillas [GSLW19, BlockHam.tex:886-887,1936-1952]. -/
theorem exactBlockEncoding_fourWaySourceAlternatingPhaseModulation
    {m n d00 d01 d10 d11 : Nat}
    {U : UnitaryOperator (Qubits (m + n))}
    {A : HilbertOperator (Qubits n)}
    {P00 P01 P10 P11 : Polynomial ℂ}
    {phases00 phases01 phases10 phases11 : List ℝ}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hparity00 : HasParity P00 d00)
    (hparity01 : HasParity P01 d01)
    (hparity10 : HasParity P10 d10)
    (hparity11 : HasParity P11 d11)
    (hblock00 :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d00 P00 phases00)
    (hblock01 :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d01 P01 phases01)
    (hblock10 :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d10 P10 phases10)
    (hblock11 :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d11 P11 phases11) :
    ExactBlockEncoding (1 + (1 + m)) n
      (fourWayAverageProjectedBlockOperator (a := m) (n := n)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases00).matrix
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases01).matrix
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases10).matrix
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases11).matrix)
      ((1 / 4 : ℂ) • polynomialOperator P00 A +
        (1 / 4 : ℂ) • polynomialOperator P01 A +
      ((1 / 4 : ℂ) • polynomialOperator P10 A +
        (1 / 4 : ℂ) • polynomialOperator P11 A)) := by
  have h00 :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases00).matrix
        (polynomialOperator P00 A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparity00 hblock00
  have h01 :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases01).matrix
        (polynomialOperator P01 A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparity01 hblock01
  have h10 :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases10).matrix
        (polynomialOperator P10 A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparity10 hblock10
  have h11 :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases11).matrix
        (polynomialOperator P11 A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparity11 hblock11
  exact exactBlockEncoding_fourWayAverageProjectedBlockOperator
    (a := m) (n := n) h00 h01 h10 h11

/-- Four source-level real/imaginary and even/odd phase branches give the
normalization-four complex Hermitian block-encoding shape with two shared
selector ancillas.  This is the conditional source-circuit form of the complex
note after `thm:arbParity`: the branches are source alternating phase sequences,
not already wrapped real-QSVT outputs [GSLW19, BlockHam.tex:1936-1952]. -/
theorem exactBlockEncoding_complexFourPartSourceAlternatingPhaseModulation
    {m n dReEven dReOdd dImEven dImOdd : Nat}
    {U : UnitaryOperator (Qubits (m + n))}
    {A : HilbertOperator (Qubits n)}
    {P : Polynomial Complex}
    {phasesReEven phasesReOdd phasesImEven phasesImOdd : List Real}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hparityReEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) dReEven)
    (hparityReOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) dReOdd)
    (hparityImEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P))) dImEven)
    (hparityImOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P))) dImOdd)
    (hblockReEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P)))
        phasesReEven)
    (hblockReOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P)))
        phasesReOdd)
    (hblockImEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P)))
        phasesImEven)
    (hblockImOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P)))
        phasesImOdd) :
    ExactBlockEncoding (1 + (1 + m)) n
      (fourWayAverageProjectedBlockOperator (a := m) (n := n)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReEven).matrix
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReOdd).matrix
        (phaseScaledOperator Complex.I complex_normSq_I
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesImEven).matrix)
        (phaseScaledOperator Complex.I complex_normSq_I
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesImOdd).matrix))
      ((1 / 4 : Complex) • polynomialOperator P A) := by
  have hReEven :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReEven).matrix
        (polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialRealPart P))) A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparityReEven hblockReEven
  have hReOdd :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReOdd).matrix
        (polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialRealPart P))) A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparityReOdd hblockReOdd
  have hImEven :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesImEven).matrix
        (polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparityImEven hblockImEven
  have hImOdd :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesImOdd).matrix
        (polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparityImOdd hblockImOdd
  exact
    exactBlockEncoding_complexFourPartAverageProjectedBlockOperator
      (a := m) (n := n) P A hReEven hReOdd hImEven hImOdd

/-- Block-encoding form of
`exactBlockEncoding_complexFourPartSourceAlternatingPhaseModulation`: the same
shared source-level four-way circuit is a `(4,m+2,0)` block encoding of the
complex Hermitian polynomial target. -/
theorem blockEncoding_complexFourPartSourceAlternatingPhaseModulation
    {m n dReEven dReOdd dImEven dImOdd : Nat}
    {U : UnitaryOperator (Qubits (m + n))}
    {A : HilbertOperator (Qubits n)}
    {P : Polynomial Complex}
    {phasesReEven phasesReOdd phasesImEven phasesImOdd : List Real}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hparityReEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) dReEven)
    (hparityReOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) dReOdd)
    (hparityImEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P))) dImEven)
    (hparityImOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P))) dImOdd)
    (hblockReEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P)))
        phasesReEven)
    (hblockReOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P)))
        phasesReOdd)
    (hblockImEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P)))
        phasesImEven)
    (hblockImOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P)))
        phasesImOdd) :
    BlockEncoding 4 (1 + (1 + m)) n 0
      (fourWayAverageProjectedBlockOperator (a := m) (n := n)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReEven).matrix
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReOdd).matrix
        (phaseScaledOperator Complex.I complex_normSq_I
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesImEven).matrix)
        (phaseScaledOperator Complex.I complex_normSq_I
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesImOdd).matrix))
      (polynomialOperator P A) := by
  have hExact :=
    exactBlockEncoding_complexFourPartSourceAlternatingPhaseModulation
      (m := m) (n := n) (U := U) (A := A) (P := P)
      hbe hA hparityReEven hparityReOdd hparityImEven hparityImOdd
      hblockReEven hblockReOdd hblockImEven hblockImOdd
  have hScaled :
      ExactBlockEncoding (1 + (1 + m)) n
        (fourWayAverageProjectedBlockOperator (a := m) (n := n)
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesReEven).matrix
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesReOdd).matrix
          (phaseScaledOperator Complex.I complex_normSq_I
            (sourceAlternatingPhaseModulation U
              (OrthogonalProjector.zeroAncilla m n)
              (OrthogonalProjector.zeroAncilla m n) phasesImEven).matrix)
          (phaseScaledOperator Complex.I complex_normSq_I
            (sourceAlternatingPhaseModulation U
              (OrthogonalProjector.zeroAncilla m n)
              (OrthogonalProjector.zeroAncilla m n) phasesImOdd).matrix))
        (((4 : Real)⁻¹ : Complex) • polynomialOperator P A) := by
    simpa [one_div] using hExact
  exact ExactBlockEncoding.toScaledBlockEncoding (α := 4) (by norm_num) hScaled

namespace Signal.HermitianRealParity

/-! ### Event-native real matching-parity endpoint -/

/-- The real matching-parity Hermitian QSVT endpoint.  Its semantics and exact
event profile are both derived from the returned typed circuit. -/
theorem sourceMain {m n L : Nat}
    {U : UnitaryOperator (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (hLpos : 0 < L) :
    ∃ word : HermitianQSVTWord m (1 + m) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + m) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 1 ∧
        word.eventProfile = realParityEventProfile m L ∧
        (realPolynomialToComplex PRe).natDegree ≤ L ∧
        HasParity (realPolynomialToComplex PRe) L := by
  let zero := OrthogonalProjector.zeroAncilla m n
  let projected :=
    realProjectedQSVTOfMatchingParity (U := U) zero zero hP hLpos
  let circuit :=
    phaseHadamardReassociateCircuit (m := m) (n := n) projected.circuit
  let output := circuit.matrix
  have houtput :
      ExactBlockEncoding (1 + m) n output
        (polynomialOperator (realPolynomialToComplex PRe) A) := by
    constructor
    intro i j
    have hout : projectedOutputProjector zero zero L = zero := by
      simp [projectedOutputProjector]
    have hprojected := congrArg (projectedBlock m n) projected.block_eq
    have hprojected' :
        projectedBlock m n
            (projectedPhasePlusBlock zero zero projected.circuit.matrix) =
          projectedBlock m n
            (singularValuePolynomial zero L (realPolynomialToComplex PRe)
              (projectedUnitaryBlock zero zero U)) := by
      simpa [hout, zero] using hprojected
    have henc :=
      (exactBlockEncoding_to_projectedUnitaryEncoding hbe).block_eq
    have htarget :
        projectedBlock m n
            (singularValuePolynomial zero L (realPolynomialToComplex PRe)
              (projectedUnitaryBlock zero zero U)) =
          polynomialOperator (realPolynomialToComplex PRe) A := by
      rw [henc]
      exact
        projectedBlock_singularValuePolynomial_zeroAncillaEmbeddedOperator_of_hermitian
          (a := m) (n := n) (L := L) (realPolynomialToComplex PRe) A hA
          (ReflectionQSPPhaseSynthesis.hasParity_realPolynomialToComplex hP.parity)
    have hblock :
        projectedBlock (1 + m) n
            (output : HilbertOperator (Qubits ((1 + m) + n))) =
          polynomialOperator (realPolynomialToComplex PRe) A := by
      unfold output circuit
      rw [phaseHadamardReassociateCircuit_matrix]
      rw [projectedBlock_reassociatedPhaseHadamardWrapper]
      rw [← projectedBlock_projectedPhasePlusBlock_zeroAncilla
        projected.circuit.matrix]
      rw [hprojected', htarget]
    exact congrFun (congrFun hblock i) j
  have hprojectedEvents :
      projected.circuit.eventCost =
        qsvtProjectedCircuitEventResource (m + n) L :=
    projected.resources_exact
  have hcircuitEvents :
      circuit.eventCost = realParityCircuitEvents (m + n) L := by
    unfold circuit
    rw [phaseHadamardReassociateCircuit_eventCost, hprojectedEvents]
    rfl
  have heventProfile :
      HermitianEventProfile.ofEvents circuit.eventCost =
        realParityEventProfile m L := by
    rw [hcircuitEvents]
    exact realParityCircuitEvents_profile m n L
  refine ⟨{
      signal := U,
      circuit := circuit,
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 1,
      totalBlockAncilla := 1 + m,
      totalBlockAncilla_eq := by omega
      totalBlockAncilla_eq_a := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, by simp; omega,
    by simpa [HermitianQSVTWord.eventProfile] using heventProfile,
    by simpa [realPolynomialToComplex_natDegree] using hP.degree_le,
    ReflectionQSPPhaseSynthesis.hasParity_realPolynomialToComplex hP.parity⟩

/-- A matching-parity branch has the source circuit at positive degree and a
sealed scalar-dilation circuit at degree zero.  Both cases expose only the
event profile of the returned circuit. -/
theorem exists_word_of_matchingParity {m n d : Nat}
    {U : UnitaryOperator (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity d PRe) :
    ∃ word : HermitianQSVTWord m (1 + m) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + m) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.extraAncillaQubits = 1 ∧
        word.eventProfile = matchingParityEventProfile m d := by
  by_cases hpos : 0 < d
  · rcases sourceMain (m := m) (n := n) (L := d) (U := U) (A := A)
        PRe hbe hA hP hpos with
      ⟨word, huses, henc, htotal, hevents, -, -⟩
    have hextra : word.extraAncillaQubits = 1 := by
      have hfield := word.totalBlockAncilla_eq
      omega
    exact ⟨word, huses, henc, hextra,
      hevents.trans
        (matchingParityEventProfile_eq_realParityEventProfile hpos).symm⟩
  · have hd0 : d = 0 := by omega
    have hdegRe : PRe.natDegree = 0 := by
      have hle0 : PRe.natDegree ≤ 0 := by
        simpa [hd0] using hP.degree_le
      exact Nat.eq_zero_of_le_zero hle0
    have hdeg : (realPolynomialToComplex PRe).natDegree = 0 := by
      simp [realPolynomialToComplex_natDegree, hdegRe]
    have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> norm_num
    have hcoeffNorm :
        ‖(realPolynomialToComplex PRe).coeff 0‖ ≤ 1 := by
      have hbounded := hP.bounded 0 hzero
      have hcoeffAbs : |PRe.coeff 0| ≤ 1 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hbounded
      simpa [realPolynomialToComplex, Polynomial.coeff_map] using hcoeffAbs
    have hcoeffSq :
        ‖(realPolynomialToComplex PRe).coeff 0‖ ^ 2 ≤ (1 : ℝ) := by
      nlinarith [hcoeffNorm,
        norm_nonneg ((realPolynomialToComplex PRe).coeff 0)]
    have hcontract :
        Complex.normSq ((realPolynomialToComplex PRe).coeff 0) ≤ 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hcoeffSq
    let circuit :=
      qsvtScalarDilationCircuit (m := m) (n := n)
        ((realPolynomialToComplex PRe).coeff 0) hcontract
    have henc :
        ExactBlockEncoding (1 + m) n circuit.matrix
          (polynomialOperator (realPolynomialToComplex PRe) A) := by
      change ExactBlockEncoding (1 + m) n
        (scalarDilationWithSourceAncillas (m := m) (n := n)
          ((realPolynomialToComplex PRe).coeff 0) hcontract) _
      exact exactBlockEncoding_constantPolynomialWithSourceAncillas
        (m := m) (n := n) (P := realPolynomialToComplex PRe) A hdeg hcontract
    have hevents :
        HermitianEventProfile.ofEvents circuit.eventCost =
          matchingParityEventProfile m 0 := by
      unfold circuit
      exact qsvtScalarDilationCircuit_eventProfile _ _
    refine ⟨{
        signal := U,
        circuit := circuit,
        sourceBlockEncoding := hbe,
        extraAncillaQubits := 1,
        totalBlockAncilla := 1 + m,
        totalBlockAncilla_eq := by omega
        totalBlockAncilla_eq_a := by omega
      }, rfl, henc, rfl, ?_⟩
    change HermitianEventProfile.ofEvents circuit.eventCost =
      matchingParityEventProfile m d
    simpa [hd0] using hevents





end Signal.HermitianRealParity

namespace Signal.HermitianRealArbitrary

/-! ### Event-native real arbitrary-parity endpoint -/

/-- Real arbitrary-parity Hermitian QSVT, assembled from two event-certified
matching-parity branch circuits and their explicit selector circuit. -/
theorem sourceMain {m n L : Nat}
    {U : UnitaryOperator (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : PRe.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |PRe.eval x| ≤ (1 / 2 : ℝ)) :
    ∃ word : HermitianQSVTWord m (1 + (1 + m)) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + (1 + m)) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 2 ∧
        word.eventProfile = hermitianComplexEventProfile m L := by
  let Peven : Polynomial ℝ := (2 : ℝ) • realPolynomialEvenPart PRe
  let Podd : Polynomial ℝ := (2 : ℝ) • realPolynomialOddPart PRe
  have hPeven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) Peven := by
    simpa [Peven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_twoEvenPart_branch_of_boundedByHalf
        (L := L) PRe hdegree hbound
  have hPodd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) Podd := by
    simpa [Podd] using
      realBoundedMatchingParity_twoOddPart_branch_of_boundedByHalf_including_constant
        (L := L) PRe hdegree hbound
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity
      (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) Peven hbe hA hPeven with
    ⟨evenWord, -, hEvenEnc, -, hEvenEvents⟩
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity
      (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) Podd hbe hA hPodd with
    ⟨oddWord, -, hOddEnc, -, hOddEvents⟩
  have hEvenEncCircuit :
      ExactBlockEncoding (1 + m) n evenWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex Peven) A) := by
    simpa only [HermitianQSVTWord.output] using hEvenEnc
  have hOddEncCircuit :
      ExactBlockEncoding (1 + m) n oddWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex Podd) A) := by
    simpa only [HermitianQSVTWord.output] using hOddEnc
  let circuit :=
    averageProjectedBlockCircuit (a := 1 + m) (n := n)
      evenWord.circuit oddWord.circuit
  let output := circuit.matrix
  have houtput :
      ExactBlockEncoding (1 + (1 + m)) n output
        (polynomialOperator (realPolynomialToComplex PRe) A) := by
    unfold output circuit
    rw [averageProjectedBlockCircuit_matrix]
    simpa [Peven, Podd] using
      exactBlockEncoding_realEvenOddDoubleAverageProjectedBlockOperator
        (a := 1 + m) (n := n) PRe A hEvenEncCircuit hOddEncCircuit
  simp only [HermitianQSVTWord.eventProfile] at hEvenEvents hOddEvents
  have hevents :
      HermitianEventProfile.ofEvents circuit.eventCost =
        hermitianComplexEventProfile m L := by
    unfold circuit
    rw [averageProjectedBlockCircuit_eventProfile,
      hEvenEvents, hOddEvents]
    apply HermitianEventProfile.ext <;>
      simp [HermitianEventProfile.binarySelector,
        matchingParityEventProfile, hermitianComplexEventProfile]
  refine ⟨{
      signal := U,
      circuit := circuit,
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 2,
      totalBlockAncilla := m + 2,
      totalBlockAncilla_eq := by omega
      totalBlockAncilla_eq_a := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, rfl,
    by simpa [HermitianQSVTWord.eventProfile] using hevents⟩





end Signal.HermitianRealArbitrary

namespace Signal.HermitianComplex

/-! ### Event-native complex Hermitian endpoint -/

/-- Complex Hermitian QSVT through four real matching-parity branch circuits.
The returned word records only the event profile projected from their explicit
phase and selector composition. -/
theorem sourceMain {m n L : Nat}
    {U : UnitaryOperator (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (P : Polynomial ℂ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : P.natDegree ≤ L)
    (hbound :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ word : HermitianQSVTWord m (1 + (1 + (1 + m))) n A,
      word.UsesSignal U ∧
        BlockEncoding 4 (1 + (1 + (1 + m))) n 0 word.output
          (polynomialOperator P A) ∧
        word.totalBlockAncilla = m + 3 ∧
        word.eventProfile = hermitianComplexFourBranchEventProfile m L ∧
        P.natDegree ≤ L := by
  let PReEven : Polynomial ℝ :=
    realPolynomialEvenPart (complexPolynomialRealPart P)
  let PReOdd : Polynomial ℝ :=
    realPolynomialOddPart (complexPolynomialRealPart P)
  let PImEven : Polynomial ℝ :=
    realPolynomialEvenPart (complexPolynomialImagPart P)
  let PImOdd : Polynomial ℝ :=
    realPolynomialOddPart (complexPolynomialImagPart P)
  have hReEven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) PReEven := by
    simpa [PReEven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_realEvenPart_branch_of_normSq_le
        (L := L) P hdegree hbound
  have hReOdd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) PReOdd := by
    simpa [PReOdd] using
      realBoundedMatchingParity_realOddPart_branch_of_normSq_le_including_constant
        (L := L) P hdegree hbound
  have hImEven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) PImEven := by
    simpa [PImEven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_imagEvenPart_branch_of_normSq_le
        (L := L) P hdegree hbound
  have hImOdd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) PImOdd := by
    simpa [PImOdd] using
      realBoundedMatchingParity_imagOddPart_branch_of_normSq_le_including_constant
        (L := L) P hdegree hbound
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity
      (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) PReEven hbe hA hReEven with
    ⟨reEvenWord, -, hReEvenEnc, -, hReEvenEvents⟩
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity
      (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) PReOdd hbe hA hReOdd with
    ⟨reOddWord, -, hReOddEnc, -, hReOddEvents⟩
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity
      (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) PImEven hbe hA hImEven with
    ⟨imEvenWord, -, hImEvenEnc, -, hImEvenEvents⟩
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity
      (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) PImOdd hbe hA hImOdd with
    ⟨imOddWord, -, hImOddEnc, -, hImOddEvents⟩
  have hReEvenCircuit :
      ExactBlockEncoding (1 + m) n reEvenWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex PReEven) A) := by
    simpa only [HermitianQSVTWord.output] using hReEvenEnc
  have hReOddCircuit :
      ExactBlockEncoding (1 + m) n reOddWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex PReOdd) A) := by
    simpa only [HermitianQSVTWord.output] using hReOddEnc
  have hImEvenCircuit :
      ExactBlockEncoding (1 + m) n imEvenWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex PImEven) A) := by
    simpa only [HermitianQSVTWord.output] using hImEvenEnc
  have hImOddCircuit :
      ExactBlockEncoding (1 + m) n imOddWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex PImOdd) A) := by
    simpa only [HermitianQSVTWord.output] using hImOddEnc
  let imEvenCircuit :=
    phaseScaledCircuit Complex.I complex_normSq_I imEvenWord.circuit
  let imOddCircuit :=
    phaseScaledCircuit Complex.I complex_normSq_I imOddWord.circuit
  let circuit :=
    fourWayAverageProjectedBlockCircuit (a := 1 + m) (n := n)
      reEvenWord.circuit reOddWord.circuit imEvenCircuit imOddCircuit
  let output := circuit.matrix
  have hExact :
      ExactBlockEncoding (1 + (1 + (1 + m))) n output
        ((1 / 4 : ℂ) • polynomialOperator P A) := by
    unfold output circuit imEvenCircuit imOddCircuit
    apply exactBlockEncoding_complexFourPartAverageProjectedBlockCircuit
      (a := 1 + m) (n := n) P A reEvenWord.circuit reOddWord.circuit
      imEvenWord.circuit imOddWord.circuit
    · simpa [PReEven] using hReEvenCircuit
    · simpa [PReOdd] using hReOddCircuit
    · simpa [PImEven] using hImEvenCircuit
    · simpa [PImOdd] using hImOddCircuit
  have houtput :
      BlockEncoding 4 (1 + (1 + (1 + m))) n 0 output
        (polynomialOperator P A) := by
    have hExactScaled :
        ExactBlockEncoding (1 + (1 + (1 + m))) n output
          (((4 : ℝ)⁻¹ : ℂ) • polynomialOperator P A) := by
      simpa [one_div] using hExact
    exact ExactBlockEncoding.toScaledBlockEncoding
      (α := 4) (by norm_num) hExactScaled
  simp only [HermitianQSVTWord.eventProfile] at hReEvenEvents hReOddEvents
  simp only [HermitianQSVTWord.eventProfile] at hImEvenEvents hImOddEvents
  have hImEvenEventProfile :
      HermitianEventProfile.ofEvents imEvenCircuit.eventCost =
        HermitianEventProfile.addElementaryEvent
          (matchingParityEventProfile m
            (ReflectionQSPPhaseSynthesis.evenBranchDegree L)) := by
    unfold imEvenCircuit
    rw [phaseScaledCircuit_eventProfile, hImEvenEvents]
  have hImOddEventProfile :
      HermitianEventProfile.ofEvents imOddCircuit.eventCost =
        HermitianEventProfile.addElementaryEvent
          (matchingParityEventProfile m
            (ReflectionQSPPhaseSynthesis.oddBranchDegree L)) := by
    unfold imOddCircuit
    rw [phaseScaledCircuit_eventProfile, hImOddEvents]
  have hevents :
      HermitianEventProfile.ofEvents circuit.eventCost =
        hermitianComplexFourBranchEventProfile m L := by
    unfold circuit
    rw [fourWayAverageProjectedBlockCircuit_eventProfile,
      hReEvenEvents, hReOddEvents,
      hImEvenEventProfile, hImOddEventProfile]
    apply HermitianEventProfile.ext <;>
      simp [HermitianEventProfile.binarySelector,
        HermitianEventProfile.addElementaryEvent,
        matchingParityEventProfile,
        hermitianComplexFourBranchEventProfile] <;>
      omega
  refine ⟨{
      signal := U,
      circuit := circuit,
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 3,
      totalBlockAncilla := m + 3,
      totalBlockAncilla_eq := by omega
      totalBlockAncilla_eq_a := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, rfl,
    by simpa [HermitianQSVTWord.eventProfile] using hevents,
    hdegree⟩







end Signal.HermitianComplex

end QSVT

namespace QSVT.Signal



/-- Namespace-local spelling of strict Hermitian QSVT event counters. -/
abbrev HermitianEventProfile :=
  QuantumAlg.QSP.MultiQubit.QSVT.HermitianEventProfile

/-- Namespace-local spelling of a Hermitian QSVT word. -/
abbrev HermitianQSVTWord (m a n : Nat) (A : HilbertOperator (Qubits n)) :=
  QuantumAlg.QSP.MultiQubit.QSVT.HermitianQSVTWord m a n A







/-- Namespace-local real-parity strict event profile. -/
abbrev realParityEventProfile (m L : ℕ) :=
  QuantumAlg.QSP.MultiQubit.QSVT.realParityEventProfile m L

/-- Namespace-local shared-control complex strict event profile. -/
abbrev hermitianComplexEventProfile (m L : ℕ) :=
  QuantumAlg.QSP.MultiQubit.QSVT.hermitianComplexEventProfile m L

/-- Namespace-local four-branch complex strict event profile. -/
abbrev hermitianComplexFourBranchEventProfile (m L : ℕ) :=
  QuantumAlg.QSP.MultiQubit.QSVT.hermitianComplexFourBranchEventProfile m L

end QSVT.Signal

end QSP.MultiQubit

end QuantumAlg

end

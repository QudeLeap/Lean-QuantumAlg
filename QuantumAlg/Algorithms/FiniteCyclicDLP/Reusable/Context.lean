/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Circuit
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Components.Classical.Oracle.FiniteGroup
public import QuantumAlg.Core.Execution.Context.Layout.Unitary
public import QuantumAlg.Core.Execution.Measurement.Cells
public import QuantumAlg.Core.Execution.QubitReadouts
public import QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# One physical binary bank with retained finite-cyclic samples

Exactly one `2t+n` qubit bank is allocated. Distinct classical cells retain
every exponent sample, and a separate single classical bit is reused by all
physical resets. Increasing the attempt count adds classical sample storage,
never another quantum bank [Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G]

/-- The sole binary quantum query and the original ambient finite-group classical service. -/
public abbrev model [Fintype G] (P : KnownOrderProblem G) : ExecutionModel :=
  .quantum AlgorithmGate.model (Binary.Oracle.model P) BitWord.model
    (ClassicalFiniteGroupOracle.model G)

/-- The source instance interprets both granted interfaces without choosing the stored program. -/
@[expose] public def sourceEnvironment [Fintype G] (P : KnownOrderProblem G) :
    (model P).Environment where
  quantum := Binary.Oracle.interpretation P
  classical := ClassicalFiniteGroupOracle.interpretation G

/-- Matching both source interpretations fixes the environment, independently of hidden state. -/
public lemma sourceEnvironment_eq [Fintype G] (P : KnownOrderProblem G)
    (environment : (model P).Environment)
    (quantum : environment.quantum = Binary.Oracle.interpretation P)
    (classical : environment.classical = ClassicalFiniteGroupOracle.interpretation G) :
    environment = sourceEnvironment P := by
  rcases environment with ⟨quantumEnvironment, classicalEnvironment⟩
  change quantumEnvironment = _ at quantum
  change classicalEnvironment = _ at classical
  subst quantumEnvironment
  subst classicalEnvironment
  rfl

/-- The sampler has no physical or classical caller input. -/
@[expose, reducible] public def pre : RuntimeCtx .quantum := RuntimeCtx.empty

/-- Number of actual exponent measurement cells per retained sample. -/
public abbrev sampleWidth (P : KnownOrderProblem G) :=
  OrderPreparation.width P + OrderPreparation.width P

/-- Number of actual physical qubits, independent of the attempt count. -/
public abbrev bankWidth (P : KnownOrderProblem G) := sampleWidth P + Binary.groupWidth P

private lemma bankFresh : (pre : RuntimeCtx .quantum).canonicalFreshKey ∉ pre.keys :=
  RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh pre

private lemma bankDisjoint (P : KnownOrderProblem G) :
    List.Disjoint (Binary.Oracle.layout P).identities pre.physicalIdx := by
  rw [pre, RuntimeCtx.runtimeCtx_empty_physicalIdx]
  exact List.disjoint_nil_right _

/-- The same one owned binary bank persists throughout the complete execution. -/
@[expose] public def bankContext (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  pre.addOwnedLayout pre.canonicalFreshKey (Binary.Oracle.layout P)
    (by exact bankFresh) (by exact bankDisjoint P)

/-- Every sample has its own retained classical exponent cells. -/
@[expose] public def sampleContext (P : KnownOrderProblem G) (count : Nat) :
    RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext P) 2 (count * sampleWidth P)

/-- One additional retained two-valued scratch cell is shared by every physical reset. -/
@[expose] public def context (P : KnownOrderProblem G) (count : Nat) : RuntimeCtx .quantum :=
  (sampleContext P count).addRetained (sampleContext P count).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count))

/-- Only this cell may be overwritten by the physical reset sequence. -/
public def scratch (P : KnownOrderProblem G) (count : Nat) :
    CWriteRef (context P count) (.finite 2) :=
  CWriteRef.retainedHead (sampleContext P count) (sampleContext P count).canonicalFreshKey
    (.finite 2) (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count))

/-- One distinct sample bit under the independently allocated reset scratch. -/
public def cell (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (index : Fin (sampleWidth P)) : CWriteRef (context P count) (.finite 2) :=
  (MeasurementCells.reference (bankContext P) 2 (count * sampleWidth P)
    (finProdFinEquiv (slot, index))).underRetained
      (sampleContext P count).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count))

/-- Read the actual ordered bit cells of one retained sample. -/
public def sampleInput (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    CInputRef (context P count) (.fixedVector (sampleWidth P) (.finite 2)) :=
  .fixedVector fun index => .storage (cell P slot index).toCStorageRef

/-- Read every retained sample in chronological order without computing another value. -/
public def samplesInput (P : KnownOrderProblem G) (count : Nat) :
    CInputRef (context P count)
      (.fixedVector count (.fixedVector (sampleWidth P) (.finite 2))) :=
  .fixedVector fun slot => sampleInput P slot

/-- Classical storage never changes the ordered physical wires of the one binary bank. -/
public lemma reusableDLP_sourceWires (P : KnownOrderProblem G) (count : Nat) :
    (Binary.Oracle.layout P).wires = (context P count).quantumLayout.wires := by
  have bank : (bankContext P).quantumWires = (Binary.Oracle.layout P).wires := by
    change (Binary.Oracle.layout P).wires ++ ([] : List QuantumWire) = _
    exact List.append_nil _
  rw [RuntimeCtx.quantumLayout_wires]
  change (Binary.Oracle.layout P).wires = (sampleContext P count).quantumWires
  rw [sampleContext, MeasurementCells.context_quantumWires, bank]

/-- Physical positions correspond without adding or deleting any system. -/
public def wireEquiv (P : KnownOrderProblem G) (count : Nat) :
    Fin (bankWidth P) ≃ Fin (context P count).systemCount :=
  Execution.positionsOfEqualWires (Binary.Oracle.layout P) (context P count).quantumLayout
    (reusableDLP_sourceWires P count)

/-- The actual runtime bank has exactly the stated number of physical systems. -/
public lemma context_systemCount (P : KnownOrderProblem G) (count : Nat) :
    (context P count).systemCount = bankWidth P := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (wireEquiv P count)).symm

/-- Runtime labels and native circuit labels identify the same physical basis. -/
public def basisEquiv (P : KnownOrderProblem G) (count : Nat) :
    (context P count).register.Index ≃ (Binary.Oracle.layout P).Basis :=
  (Execution.basisOfEqualWires (Binary.Oracle.layout P) (context P count).quantumLayout
    (reusableDLP_sourceWires P count)).symm

/-- Equal-wire transport preserves each actual finite basis value. -/
public lemma reusableDLP_basisEquiv_wire_value (P : KnownOrderProblem G) (count : Nat)
    (basis : (context P count).register.Index) (index : Fin (bankWidth P)) :
    (basis (wireEquiv P count index)).val = (basisEquiv P count basis index).val := by
  let correspondence := Execution.basisOfEqualWires
    (Binary.Oracle.layout P) (context P count).quantumLayout (reusableDLP_sourceWires P count)
  have value := Execution.basisOfEqualWires_value (Binary.Oracle.layout P)
    (context P count).quantumLayout (reusableDLP_sourceWires P count)
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis) (wireEquiv P count index)).val = _
    at value
  rw [Equiv.apply_symm_apply] at value
  exact value

/-- Physical zero is the same label under the unchanged ordered-wire correspondence. -/
@[simp] public lemma reusableDLP_basisEquiv_zero (P : KnownOrderProblem G) (count : Nat) :
    basisEquiv P count (context P count).quantumLayout.zeroLabel =
      (Binary.Oracle.layout P).zeroLabel := by
  funext index
  apply Fin.ext
  simpa only [QuantumLayout.zeroLabel, Fin.val_zero] using
    (reusableDLP_basisEquiv_wire_value P count (context P count).quantumLayout.zeroLabel index).symm

/-- Every actual resident quantum system is a qubit. -/
public lemma qubits (P : KnownOrderProblem G) (count : Nat)
    (wire : Fin (context P count).systemCount) :
    ((context P count).quantumLayout.wire wire).dimension = 2 := by
  have same := Execution.wireAtCorrespondingPosition (Binary.Oracle.layout P)
    (context P count).quantumLayout (reusableDLP_sourceWires P count) ((wireEquiv P count).symm
      wire)
  change ((context P count).quantumLayout.wire
    (wireEquiv P count ((wireEquiv P count).symm wire))) = _ at same
  rw [Equiv.apply_symm_apply] at same
  rw [same]
  exact Binary.Oracle.layout_qubits P _

/-- Position of one measured exponent wire in the unchanged bank. -/
public def exponentPosition (P : KnownOrderProblem G) (count : Nat)
    (index : Fin (sampleWidth P)) : Fin (context P count).systemCount :=
  wireEquiv P count (Fin.castAdd (Binary.groupWidth P) index)

/-- One literal Z measurement writes one actual exponent bit of the selected sample. -/
public def readout (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (index : Fin (sampleWidth P)) : ZReadout (context P count) :=
  QubitReadouts.readout (exponentPosition P count index)
    (qubits P count _) (cell P slot index)

/-- Ordered measurement instructions for one actual attempt. -/
public def readouts (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    List (ZReadout (context P count)) := List.ofFn (readout P slot)

variable [Fintype G]

/-- Allocate and zero-initialize the binary bank exactly once. -/
public def preparationCode (P : KnownOrderProblem G) :
    QuantumAlg.Circuit (model P) pre (bankContext P) :=
  .prepareZero pre pre.canonicalFreshKey (Binary.Oracle.layout P)
    (by exact bankFresh) (by exact bankDisjoint P)

/-- Allocate all retained sample bits and the one shared reset scratch, with no new qubit. -/
public def allocationCode (P : KnownOrderProblem G) (count : Nat) :
    QuantumAlg.Circuit (model P) (bankContext P) (context P count) :=
  (MeasurementCells.allocate (model := model P) (bankContext P) 2
    (count * sampleWidth P)).seq
    (.retain (model := model P) (sampleContext P count)
      (sampleContext P count).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count)))

/-- The single physical preparation and all real classical allocation form the actual prefix. -/
public def initialCode (P : KnownOrderProblem G) (count : Nat) :
    QuantumAlg.Circuit (model P) pre (context P count) :=
  (preparationCode P).seq (allocationCode P count)

/-- Execute the binary native word on that same already-owned physical bank. -/
public def nativeProgram (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    UnitaryCircuit AlgorithmGate.model (Binary.Oracle.model P)
      (context P count).quantumLayout :=
  Execution.unitaryOfEqualWires (Binary.Oracle.layout P) (context P count).quantumLayout
    (reusableDLP_sourceWires P count) (Binary.Circuit.circuit P expansion)

end

end QuantumAlg.FiniteCyclicDLP.Reusable

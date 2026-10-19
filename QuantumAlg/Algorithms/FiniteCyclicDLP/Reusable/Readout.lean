/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Probability
public import QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Probability
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Measurement.Sequence

/-!
# Actual retained samples of the sequential binary DLP circuit

Every round writes its own distinct exponent cells. The reset scratch is
independent of the complete sample vector. The physical readout therefore
has precisely the interpretation used by the binary Born bridge
[Sho95, source.tex:1784-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G]

/-- Decode the actual retained two-valued cells into ordered exponent bits. -/
public def observedOutcome (P : KnownOrderProblem G)
    (value : (CShape.fixedVector (sampleWidth P) (.finite 2)).Value) :
    TerminalZMeasure.Outcome (sampleWidth P) :=
  fun index => decide ((value.get index).toFin.val = 1)

/-- Decode all actually retained samples in their chronological order. -/
public def observedVector (P : KnownOrderProblem G) (count : Nat)
    (value : (CShape.fixedVector count
      (.fixedVector (sampleWidth P) (.finite 2))).Value) :
    List.Vector (TerminalZMeasure.Outcome (sampleWidth P)) count :=
  List.Vector.ofFn fun slot => observedOutcome P (value.get slot)

/-- A coordinate of the retained vector is the same structural sample read. -/
@[simp] public lemma samplesInput_get (P : KnownOrderProblem G) {count : Nat}
    (store : Store (context P count)) (slot : Fin count) :
    (store.read (samplesInput P count)).get slot = store.read (sampleInput P slot) := by rfl

/-- Every sample and bit pair has a distinct physical classical destination. -/
public lemma reusableDLP_cell_keys_injective (P : KnownOrderProblem G) (count : Nat) :
    Function.Injective (fun pair : Fin count × Fin (sampleWidth P) =>
      (cell P pair.1 pair.2).key) := by
  intro left right same
  change (MeasurementCells.reference (bankContext P) 2 (count * sampleWidth P)
      (finProdFinEquiv left)).key =
    (MeasurementCells.reference (bankContext P) 2 (count * sampleWidth P)
      (finProdFinEquiv right)).key at same
  exact finProdFinEquiv.injective
    (MeasurementCells.reference_key_injective (bankContext P) 2
      (count * sampleWidth P) same)

/-- One sampling word never overwrites another bit in its own measured exponent pair. -/
public lemma reusableDLP_readouts_nodup (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) :
    ((readouts P slot).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  simp only [Function.comp_def, readout, QubitReadouts.readout_key] at same
  have injective := reusableDLP_cell_keys_injective P count
  have pairs : (slot, left) = (slot, right) :=
    @injective (slot, left) (slot, right) same
  exact congrArg Prod.snd pairs

/-- The one real reset scratch cannot occur in a retained sample read. -/
public lemma scratch_separate_sample (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) : (scratch P count).key ∉ (sampleInput P slot).storageKeys := by
  let original : CInputRef (sampleContext P count)
      (.fixedVector (sampleWidth P) (.finite 2)) :=
    .fixedVector fun index => .storage
      (MeasurementCells.reference (bankContext P) 2 (count * sampleWidth P)
        (finProdFinEquiv (slot, index))).toCStorageRef
  change (sampleContext P count).canonicalFreshKey ∉
    (original.underRetained (sampleContext P count).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count))).storageKeys
  exact CInputRef.fresh_not_mem_storageKeys_underRetained original
    (sampleContext P count).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count))

/-- The complete retained vector excludes the shared reset destination as well. -/
public lemma scratch_separate_samples (P : KnownOrderProblem G) (count : Nat) :
    (scratch P count).key ∉ (samplesInput P count).storageKeys := by
  let original : CInputRef (sampleContext P count)
      (.fixedVector count (.fixedVector (sampleWidth P) (.finite 2))) :=
    .fixedVector fun slot => .fixedVector fun index => .storage
      (MeasurementCells.reference (bankContext P) 2 (count * sampleWidth P)
        (finProdFinEquiv (slot, index))).toCStorageRef
  change (sampleContext P count).canonicalFreshKey ∉
    (original.underRetained (sampleContext P count).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count))).storageKeys
  exact CInputRef.fresh_not_mem_storageKeys_underRetained original
    (sampleContext P count).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count))

variable [Fintype G]

/-- Real stores produced by this round's ordered measurements and actual basis path. -/
public def measuredStore (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (store : Store (context P count)) (basis : (context P count).register.Index) :
    Store (context P count) :=
  QuantumAlg.Circuit.writeMeasurementPath (allowAllocation := true)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
    (readouts P slot) store
    (QuantumAlg.Circuit.measurementBasisPath (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
      (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
      (readouts P slot) basis)

/-- One real readout writes the finite value of exactly its named physical qubit. -/
public lemma reusableDLP_measured_cell (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (store : Store (context P count)) (basis : (context P count).register.Index)
    (index : Fin (sampleWidth P)) :
    ((measuredStore P slot store basis).read
      (.storage (cell P slot index).toCStorageRef)).toFin.val =
      (basis (exponentPosition P count index)).val := by
  have actual := QuantumAlg.Circuit.writeMeasurementBasis_read (allowAllocation := true)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (services := ClassicalFiniteGroupOracle.model G)
    (readouts P slot) (reusableDLP_readouts_nodup P slot) (readout P slot index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  simp only [readout, QubitReadouts.readout] at numeric
  rw [QubitReadouts.outputAt_read] at numeric
  exact numeric

/-- The measured sample is the complete actual binary circuit's exponent outcome. -/
public lemma observed_after_measurement (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (store : Store (context P count))
    (basis : (context P count).register.Index) :
    observedOutcome P ((measuredStore P slot store basis).read (sampleInput P slot)) =
      Binary.readout P (basisEquiv P count basis) := by
  funext index
  change decide (((measuredStore P slot store basis).read
    (.storage (cell P slot index).toCStorageRef)).toFin.val = 1) = _
  rw [reusableDLP_measured_cell]
  have same := reusableDLP_basisEquiv_wire_value P count basis
    (Fin.castAdd (Binary.groupWidth P) index)
  change decide ((basis (wireEquiv P count (Fin.castAdd (Binary.groupWidth P) index))).val = 1) = _
  rw [same, Binary.binaryDLP_readout_apply]

/-- Measuring one actual slot leaves every other retained sample unchanged. -/
public lemma observed_other_after_measurement (P : KnownOrderProblem G) {count : Nat}
    (slot other : Fin count) (different : slot ≠ other)
    (store : Store (context P count)) (basis : (context P count).register.Index) :
    observedOutcome P ((measuredStore P slot store basis).read (sampleInput P other)) =
      observedOutcome P (store.read (sampleInput P other)) := by
  funext index
  apply congrArg (fun value : (CShape.finite 2).Value => decide (value.toFin.val = 1))
  apply QuantumAlg.Circuit.writeMeasurementPath_read_unwritten (allowAllocation := true)
    (readouts P slot) (cell P other index).toCStorageRef
  intro item present same
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp present
  have keys : (cell P slot position).key = (cell P other index).key := by
    simpa only [readout, QubitReadouts.readout_key] using same
  have injective := reusableDLP_cell_keys_injective P count
  have pairs : (slot, position) = (other, index) :=
    @injective (slot, position) (other, index) keys
  exact different (congrArg Prod.fst pairs)

end

end QuantumAlg.FiniteCyclicDLP.Reusable

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Probability
public import QuantumAlg.Core.Base.Layout.Quantum.Embedding
public import QuantumAlg.Core.Base.UnitaryCircuit.Tensor.Matrix
public import QuantumAlg.Core.Execution.Classical.Composition.Range
public import QuantumAlg.Core.Execution.Context.Layout
public import QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Independent known-order samples on fresh native-dimensional banks

Every sample owns a distinct copy of both exponent registers and the native
group system. The complete bank family is prepared at zero once. The source
circuit then acts on every physical copy before one terminal measurement pass
writes all retained cells in chronological bank order. No reset operation or
group encoding is introduced.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBatch

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Number of physical systems in one complete source bank. -/
public abbrev bankSize (P : KnownOrderProblem G) : Nat :=
  OrderPreparation.width P + OrderPreparation.width P + 1

/-- Consecutive physical identities assigned to one bank in the family. -/
public def bankShift (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    Nat ↪ Nat where
  toFun identity := identity + bankSize P * slot.val
  inj' := fun _ _ same => Nat.add_right_cancel same

/-- All fresh banks in chronological slot order. -/
@[expose, implicit_reducible] public def layout (P : KnownOrderProblem G) (count : Nat) :
    QuantumLayout (count * bankSize P) where
  wire := fun index =>
    let bankIndex := (finProdFinEquiv.symm index).2
    { identity := index.val
      dimension := ((OrderOracle.layout P).wire bankIndex).dimension }
  identityInjective := by
    intro left right same
    apply Fin.ext
    exact same

/-- The physical copy selected by one slot appears as an exact subsystem of
the complete family layout. -/
@[expose] public def bankEmbedding (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    QuantumLayout.Embedding
      ((OrderOracle.layout P).relabel (bankShift P slot))
      (layout P count) where
  position :=
    { toFun := fun index => finProdFinEquiv (slot, index)
      inj' := fun _ _ same => by
        exact congrArg Prod.snd (finProdFinEquiv.injective same) }
  wire_eq := by
    intro index
    apply QuantumWire.ext
    · change (finProdFinEquiv (slot, index)).val =
        (bankShift P slot) ((OrderOracle.layout P).wire index).identity
      rw [OrderOracle.layout_wire_identity]
      rfl
    · change ((OrderOracle.layout P).wire
          (finProdFinEquiv.symm (finProdFinEquiv (slot, index))).2).dimension =
        ((OrderOracle.layout P).wire index).dimension
      rw [Equiv.symm_apply_apply]

/-- Restrict a complete bank-family basis to one source bank in its original coordinates. -/
@[expose] public noncomputable def bankBasis (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (basis : (layout P count).Basis) : (OrderOracle.layout P).Basis :=
  (QuantumLayout.relabelBasis (OrderOracle.layout P) (bankShift P slot)).symm
    ((bankEmbedding P slot).splitBasis basis).1

/-- Restriction reads exactly the corresponding physical value of the selected bank. -/
public theorem bankBasis_value (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (basis : (layout P count).Basis) (index : Fin (bankSize P)) :
    (bankBasis P slot basis index).val =
      (basis (finProdFinEquiv (slot, index))).val := by
  unfold bankBasis
  exact QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (bankEmbedding P slot) basis index

/-- Every selected bank sees the zero label of the complete fresh family as its own zero. -/
public theorem bankBasis_zero (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    bankBasis P slot (layout P count).zeroLabel = (OrderOracle.layout P).zeroLabel := by
  funext index
  apply Fin.ext
  rw [bankBasis_value]
  rfl

/-- Different bank slots occupy disjoint physical selections. -/
public theorem bankEmbedding_disjoint (P : KnownOrderProblem G) {count : Nat}
    {left right : Fin count} (different : left ≠ right) :
    Disjoint (bankEmbedding P left).selection (bankEmbedding P right).selection := by
  rw [Finset.disjoint_left]
  intro position inLeft inRight
  obtain ⟨leftIndex, _, leftPosition⟩ := Finset.mem_map.mp inLeft
  obtain ⟨rightIndex, _, rightPosition⟩ := Finset.mem_map.mp inRight
  apply different
  have samePosition : finProdFinEquiv (left, leftIndex) =
      finProdFinEquiv (right, rightIndex) := by
    exact leftPosition.trans rightPosition.symm
  exact congrArg Prod.fst (finProdFinEquiv.injective samePosition)

/-- Final slot of a nonempty bank family. -/
@[expose] public def lastSlot (count : Nat) : Fin (count + 1) :=
  ⟨count, by omega⟩

/-- The prefix family occupies the initial physical positions of the enlarged family. -/
@[expose] public def prefixEmbedding (P : KnownOrderProblem G) (count : Nat) :
    QuantumLayout.Embedding (layout P count) (layout P (count + 1)) where
  position :=
    { toFun := fun index => ⟨index.val, by
        have bound := index.isLt
        exact bound.trans_le (Nat.mul_le_mul_right (bankSize P) (Nat.le_succ count))⟩
      inj' := by
        intro left right same
        apply Fin.ext
        exact congrArg
          (fun position : Fin ((count + 1) * bankSize P) => position.val) same }
  wire_eq := by
    intro index
    apply QuantumWire.ext
    · rfl
    · apply congrArg (fun bankIndex => ((OrderOracle.layout P).wire bankIndex).dimension)
      apply Fin.ext
      rfl

/-- The prefix and final bank use disjoint positions of the enlarged family. -/
public theorem prefix_last_disjoint (P : KnownOrderProblem G) (count : Nat) :
    Disjoint (prefixEmbedding P count).selection
      (bankEmbedding P (lastSlot count)).selection := by
  rw [Finset.disjoint_left]
  intro position inPrefix inLast
  obtain ⟨prefixIndex, _, prefixEq⟩ := Finset.mem_map.mp inPrefix
  obtain ⟨bankIndex, _, lastEq⟩ := Finset.mem_map.mp inLast
  have same := congrArg Fin.val (prefixEq.trans lastEq.symm)
  change prefixIndex.val = bankIndex.val + bankSize P * count at same
  have prefixBound := prefixIndex.isLt
  have prefixBound' : prefixIndex.val < bankSize P * count := by
    simpa only [Nat.mul_comm count (bankSize P)] using prefixBound
  omega

/-- The final bank is exactly the complement of the prefix family. -/
public theorem prefix_last_partition (P : KnownOrderProblem G) (count : Nat) :
    (bankEmbedding P (lastSlot count)).selection =
      (prefixEmbedding P count).selectionᶜ := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.subset_compl_iff_disjoint_right.mpr
      (prefix_last_disjoint P count).symm
  · simp only [QuantumLayout.Embedding.selection, Finset.card_compl,
      Finset.card_map, Finset.card_univ, Fintype.card_fin]
    change (count + 1) * bankSize P - count * bankSize P ≤ bankSize P
    rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]

/-- The source circuit relocated to the final bank of the enlarged family. -/
@[expose] public def lastProgram (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    UnitaryCircuit AlgorithmGate.model (OrderOracle.model P)
      ((OrderOracle.layout P).relabel (bankShift P (lastSlot count))) :=
  (OrderCircuit.circuit P expansion).relabel (bankShift P (lastSlot count))

/-- All source words, composed through certified parallel placement on pairwise
disjoint complete banks. -/
@[expose] public def familyProgram (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    (count : Nat) →
      UnitaryCircuit AlgorithmGate.model (OrderOracle.model P) (layout P count)
  | 0 => UnitaryCircuit.identity AlgorithmGate.model (OrderOracle.model P) (layout P 0)
  | count + 1 =>
      UnitaryCircuit.parallel (familyProgram P expansion count)
        (lastProgram P count expansion) (prefixEmbedding P count)
        (bankEmbedding P (lastSlot count)) (prefix_last_disjoint P count)

/-- The empty caller context shares no physical identity with the complete bank family. -/
public theorem bankDisjoint (P : KnownOrderProblem G) (count : Nat) :
    List.Disjoint (layout P count).identities OrderExecution.pre.physicalIdx := by
  rw [OrderExecution.pre, RuntimeCtx.runtimeCtx_empty_physicalIdx]
  exact List.disjoint_nil_right _

/-- All fresh banks are owned by one actual runtime context. -/
@[expose] public def bankContext (P : KnownOrderProblem G) (count : Nat) :
    RuntimeCtx .quantum :=
  OrderExecution.pre.addOwnedLayout OrderExecution.pre.canonicalFreshKey
    (layout P count) OrderExecution.bankFresh (bankDisjoint P count)

/-- One retained two-valued cell for every sample and exponent position. -/
@[expose] public def post (P : KnownOrderProblem G) (count : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext P count) 2 (count * OrderExecution.sampleWidth P)

/-- Adding all banks to the empty context preserves their exact wire order. -/
public theorem bankContext_wires (P : KnownOrderProblem G) (count : Nat) :
    (bankContext P count).quantumWires = (layout P count).wires := by
  change (layout P count).wires ++ ([] : List QuantumWire) = _
  rw [List.append_nil]

/-- Retaining the measurements changes no bank wire. -/
public theorem post_wires (P : KnownOrderProblem G) (count : Nat) :
    (post P count).quantumWires = (layout P count).wires := by
  rw [post, MeasurementCells.context_quantumWires, bankContext_wires]

public theorem sourceWires (P : KnownOrderProblem G) (count : Nat) :
    (layout P count).wires = (post P count).quantumLayout.wires :=
  ((RuntimeCtx.quantumLayout_wires (post P count)).trans (post_wires P count)).symm

/-- Runtime basis labels and complete bank-family labels preserve every wire value. -/
public def basisEquiv (P : KnownOrderProblem G) (count : Nat) :
    (post P count).register.Index ≃ (layout P count).register.Index :=
  (Execution.basisOfEqualWires (layout P count) (post P count).quantumLayout
    (sourceWires P count)).symm

/-- Reversing the public runtime-to-source correspondence recovers the
equal-wire transport used by the native family circuit. -/
public theorem basisEquiv_symm (P : KnownOrderProblem G) (count : Nat) :
    (basisEquiv P count).symm =
      Execution.basisOfEqualWires (layout P count) (post P count).quantumLayout
        (sourceWires P count) := by
  rfl

/-- The complete basis correspondence changes only dependent coordinate types. -/
public theorem basisEquiv_wire_value (P : KnownOrderProblem G) (count : Nat)
    (basis : (post P count).register.Index) (index : Fin (count * bankSize P)) :
    (basis (Execution.positionsOfEqualWires (layout P count)
      (post P count).quantumLayout (sourceWires P count) index)).val =
      (basisEquiv P count basis index).val := by
  let correspondence := Execution.basisOfEqualWires
    (layout P count) (post P count).quantumLayout (sourceWires P count)
  have value := Execution.basisOfEqualWires_value
    (layout P count) (post P count).quantumLayout (sourceWires P count)
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (Execution.positionsOfEqualWires (layout P count)
      (post P count).quantumLayout (sourceWires P count) index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  exact value

/-- Select one source-bank basis directly from an actual terminal runtime basis. -/
@[expose] public noncomputable def outputBankBasis (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (basis : (post P count).register.Index) :
    (OrderOracle.layout P).Basis :=
  bankBasis P slot (basisEquiv P count basis)

/-- Actual runtime position of one system in one bank. -/
public def bankPosition (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (index : Fin (bankSize P)) : Fin (post P count).systemCount :=
  Execution.positionsOfEqualWires (layout P count) (post P count).quantumLayout
    (sourceWires P count) (finProdFinEquiv (slot, index))

/-- Runtime bank restriction reads the exact value at every corresponding wire. -/
public theorem outputBankBasis_value (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (basis : (post P count).register.Index)
    (index : Fin (bankSize P)) :
    (outputBankBasis P slot basis index).val =
      (basis (bankPosition P slot index)).val := by
  unfold outputBankBasis bankPosition
  rw [bankBasis_value, basisEquiv_wire_value]

/-- Position of an exponent qubit inside one source bank. -/
@[expose] public def exponentPosition (P : KnownOrderProblem G)
    (index : Fin (OrderExecution.sampleWidth P)) : Fin (bankSize P) :=
  ⟨index.val, by
    have bound := index.isLt
    unfold OrderExecution.sampleWidth bankSize at *
    omega⟩

/-- Cell index corresponding to one sample and exponent position. -/
@[expose] public def cellIndex (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (index : Fin (OrderExecution.sampleWidth P)) :
    Fin (count * OrderExecution.sampleWidth P) :=
  finProdFinEquiv (slot, index)

/-- One actual retained destination for one measured exponent qubit. -/
@[expose] public def cell (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (index : Fin (OrderExecution.sampleWidth P)) :
    CWriteRef (post P count) (.finite 2) :=
  MeasurementCells.reference (bankContext P count) 2
    (count * OrderExecution.sampleWidth P) (cellIndex P slot index)

/-- The selected bank position is an actual qubit. -/
public theorem exponent_dimension (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (index : Fin (OrderExecution.sampleWidth P)) :
    ((post P count).quantumLayout.wire
      (bankPosition P slot (exponentPosition P index))).dimension = 2 := by
  unfold bankPosition
  rw [Execution.wireAtCorrespondingPosition
    (layout P count) (post P count).quantumLayout (sourceWires P count)]
  change ((OrderOracle.layout P).wire
    (finProdFinEquiv.symm
      (finProdFinEquiv (slot, exponentPosition P index))).2).dimension = 2
  rw [Equiv.symm_apply_apply]
  change ((OrderOracle.layout P).wire (exponentPosition P index)).dimension = 2
  let exponentIndex : Fin
      (OrderPreparation.width P + OrderPreparation.width P) :=
    ⟨(exponentPosition P index).val, by
      have bound := index.isLt
      unfold OrderExecution.sampleWidth at bound
      exact bound⟩
  have position : exponentPosition P index = Fin.castAdd 1 exponentIndex := by
    apply Fin.ext
    rfl
  rw [position]
  simp only [OrderOracle.layout, QuantumLayout.append, Fin.append_left]
  rfl

/-- One Z readout writes the selected exponent value into its own cell. -/
@[expose] public def readout (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (index : Fin (OrderExecution.sampleWidth P)) :
    ZReadout (post P count) :=
  QubitReadouts.readout
    (bankPosition P slot (exponentPosition P index))
    (exponent_dimension P slot index) (cell P slot index)

/-- Both exponent registers of one bank are measured in source order. -/
@[expose] public def readouts (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) : List (ZReadout (post P count)) :=
  List.ofFn (readout P slot)

/-- All terminal measurements, ordered first by bank and then by exponent position. -/
@[expose] public def allReadouts (P : KnownOrderProblem G) (count : Nat) :
    List (ZReadout (post P count)) :=
  (List.ofFn (readouts P)).flatten

/-- One sample is a structural read of its real measurement cells. -/
@[expose] public def sampleInput (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    CInputRef (post P count)
      (.fixedVector (OrderExecution.sampleWidth P) (.finite 2)) :=
  .fixedVector fun index => .storage (cell P slot index).toCStorageRef

/-- The chronological sample vector introduces no copied storage. -/
@[expose] public def samplesInput (P : KnownOrderProblem G) (count : Nat) :
    CInputRef (post P count)
      (.fixedVector count
        (.fixedVector (OrderExecution.sampleWidth P) (.finite 2))) :=
  .fixedVector (sampleInput P)

/-- Prepare every independent native-dimensional bank at basis zero. -/
@[expose] public def preparationCode (P : KnownOrderProblem G) (count : Nat) :
    Circuit (OrderExecution.model P) OrderExecution.pre (bankContext P count) :=
  .prepareZero OrderExecution.pre OrderExecution.pre.canonicalFreshKey
    (layout P count) OrderExecution.bankFresh (bankDisjoint P count)

/-- Allocate exactly all terminal result cells. -/
@[expose] public def allocationCode (P : KnownOrderProblem G) (count : Nat) :
    Circuit (OrderExecution.model P) (bankContext P count) (post P count) :=
  MeasurementCells.allocate (model := OrderExecution.model P) (bankContext P count) 2
    (count * OrderExecution.sampleWidth P)

/-- Transport the complete parallel family word through retained-cell allocation. -/
public def nativeFamilyProgram (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    UnitaryCircuit AlgorithmGate.model (OrderOracle.model P) (post P count).quantumLayout :=
  Execution.unitaryOfEqualWires (layout P count) (post P count).quantumLayout
    (sourceWires P count) (familyProgram P expansion count)

/-- Apply the source word once to every fresh bank through its certified
disjoint parallel construction. -/
@[expose] public def programs (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    Circuit (OrderExecution.model P) (post P count) (post P count) :=
  .unitary (nativeFamilyProgram P count expansion)

/-- Measure all exponent registers after all independent source words finish. -/
@[expose] public def readoutCode (P : KnownOrderProblem G) (count : Nat) :
    Circuit (OrderExecution.model P) (post P count) (post P count) :=
  .measurementSequence (allReadouts P count)

/-- Coherent prefix before the terminal measurement pass. -/
@[expose] public def beforeMeasurement (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    Circuit (OrderExecution.model P) OrderExecution.pre (post P count) :=
  .seq (preparationCode P count)
    (.seq (allocationCode P count) (programs P count expansion))

/-- Fresh-bank preparation, all source words and one terminal readout pass. -/
@[expose] public def code (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    Circuit (OrderExecution.model P) OrderExecution.pre (post P count) :=
  .seq (beforeMeasurement P count expansion) (readoutCode P count)

/-- Complete repeated sampler retaining every bank and every measured value. -/
public def run (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    AlgorithmRun (OrderExecution.model P) OrderExecution.pre (post P count)
      (.fixedVector count
        (.fixedVector (OrderExecution.sampleWidth P) (.finite 2))) where
  code := code P count expansion
  output := Output.all (post P count) (.read (samplesInput P count))

end

end QuantumAlg.FiniteCyclicDLP.OrderBatch

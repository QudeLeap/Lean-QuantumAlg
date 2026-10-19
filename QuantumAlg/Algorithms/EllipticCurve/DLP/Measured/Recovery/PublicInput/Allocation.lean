/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Frame
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Resources
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Preparation
import all QuantumAlg.Core.Execution.Time

/-!
# Actual zero allocation of the reduced public streaming context

The two borrowed public point cells are already present. Five real owned
preparations allocate the original three indexed qubits, two coordinate words
and arithmetic auxiliary layout, in reverse entry order. The original
numerator and terminal retain instructions then create their original cells.
Every physical identity, key and role agrees with the reduced terminal.

 It loads no arithmetic
seed and executes no reset or sampler. Exact allocation peaks and the complete
borrowed classical/reference observation concern this allocating parent alone.
The later reset-to-initialized-columns and common instrument equations remain
separate obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
namespace Allocation

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement MAU.Inversion.SharedEEA

local instance {α : Type} : DecidableEq α := Classical.decEq α

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty

private lemma context_eq (left right : RuntimeCtx .quantum)
    (same : left.entries = right.entries) : left = right := by
  cases left
  cases right
  cases same
  rfl

private lemma union_parts {left right framed : RuntimeCtx .quantum}
    (original : RuntimeCtx.StorageDisjoint left right)
    (separate : RuntimeCtx.StorageDisjoint (left.disjointUnion right original) framed) :
    RuntimeCtx.StorageDisjoint left framed ∧ RuntimeCtx.StorageDisjoint right framed := by
  have keys := (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp separate.1
  have physical := (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp separate.2
  rw [RuntimeCtx.keys_disjointUnion] at keys
  rw [RuntimeCtx.physicalIdx_disjointUnion] at physical
  have keyParts := List.disjoint_append_left.mp keys
  have wireParts := List.disjoint_append_left.mp physical
  exact ⟨⟨(RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr keyParts.1,
    (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr wireParts.1⟩,
    ⟨(RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr keyParts.2,
      (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr wireParts.2⟩⟩

private lemma union_frame {left right framed : RuntimeCtx .quantum}
    (original : RuntimeCtx.StorageDisjoint left right)
    (first : RuntimeCtx.StorageDisjoint left framed)
    (second : RuntimeCtx.StorageDisjoint right framed) :
    RuntimeCtx.StorageDisjoint (left.disjointUnion right original) framed := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    rw [RuntimeCtx.keys_disjointUnion]
    exact List.disjoint_append_left.mpr
      ⟨(RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp first.1,
        (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp second.1⟩
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    rw [RuntimeCtx.physicalIdx_disjointUnion]
    exact List.disjoint_append_left.mpr
      ⟨(RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp first.2,
        (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp second.2⟩

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)

private abbrev indexed : RuntimeCtx .quantum :=
  indexedContext p.size (List.range 3) List.nodup_range

private lemma bank_disjoint :
    RuntimeCtx.StorageDisjoint (Recovery.Layout.bank p.size) (Recovery.PublicInput.frame E m) :=
  MeasurementCells.original_disjoint _ _ 2 (2 * m) (Recovery.PublicInput.terminal_disjoint E m)

private lemma numerator_disjoint :
    RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context p.size) (Recovery.PublicInput.frame
      E m) :=
  (union_parts (indexedContext_disjoint p.size (List.range 3) List.nodup_range)
    (bank_disjoint E m)).1

private lemma indexed_disjoint :
    RuntimeCtx.StorageDisjoint (indexed (p := p)) (Recovery.PublicInput.frame E m) :=
  (union_parts (indexedContext_disjoint p.size (List.range 3) List.nodup_range)
    (bank_disjoint E m)).2

private lemma inverse_disjoint :
    RuntimeCtx.StorageDisjoint (InversePreparation.after p.size) (Recovery.PublicInput.frame E m) :=
  MeasurementCells.original_disjoint _ _ 2 p.size (numerator_disjoint E m)

private lemma inverse_indexed_disjoint :
    RuntimeCtx.StorageDisjoint (InversePreparation.after p.size) (indexed (p := p)) :=
  MeasurementCells.original_disjoint _ _ 2 p.size
    (indexedContext_disjoint p.size (List.range 3) List.nodup_range)

private def quantumContext : RuntimeCtx .quantum :=
  ((InversePreparation.after p.size).disjointUnion (indexed (p := p))
    (inverse_indexed_disjoint (p := p))).disjointUnion (Recovery.PublicInput.frame E m)
      (union_frame (inverse_indexed_disjoint (p := p))
        (inverse_disjoint E m) (indexed_disjoint E m))

private lemma drop_fresh (tail : RuntimeCtx .quantum) (n : Nat) (key : StorageKey)
    {count : Nat} (layout : QuantumLayout count)
    (same : (quantumContext E m).entries.drop n =
      RuntimeEntry.ownedLayout key layout :: tail.entries) : key ∉ tail.keys := by
  have distinct := ((List.drop_sublist n (quantumContext E m).entries).map
    RuntimeEntry.key).nodup (quantumContext E m).keysNodup
  rw [same, List.map_cons] at distinct
  exact (List.nodup_cons.mp distinct).1

private lemma drop_physical (tail : RuntimeCtx .quantum) (n : Nat) (key : StorageKey)
    {count : Nat} (layout : QuantumLayout count)
    (same : (quantumContext E m).entries.drop n =
      RuntimeEntry.ownedLayout key layout :: tail.entries) :
    List.Disjoint layout.identities tail.physicalIdx := by
  have distinct := (((List.drop_sublist n (quantumContext E m).entries).flatMap
    RuntimeEntry.quantumWires).map QuantumWire.identity).nodup
      (quantumContext E m).identitiesNodup
  rw [same, List.flatMap_cons, List.map_append] at distinct
  change ((layout.wires.map QuantumWire.identity) ++ tail.physicalIdx).Nodup at distinct
  rw [← layout_identities_eq_map_wires] at distinct
  exact (List.nodup_append'.mp distinct).2.2

private def withThird : RuntimeCtx .quantum :=
  (Recovery.PublicInput.frame E m).addOwnedLayout (indexedKey p.size 2) (indexedLayout p.size 2)
    (drop_fresh E m _ 4 _ _ rfl) (drop_physical E m _ 4 _ _ rfl)

private def withSecond : RuntimeCtx .quantum :=
  (withThird E m).addOwnedLayout (indexedKey p.size 1) (indexedLayout p.size 1)
    (drop_fresh E m _ 3 _ _ rfl) (drop_physical E m _ 3 _ _ rfl)

private def withFirst : RuntimeCtx .quantum :=
  (withSecond E m).addOwnedLayout (indexedKey p.size 0) (indexedLayout p.size 0)
    (drop_fresh E m _ 2 _ _ rfl) (drop_physical E m _ 2 _ _ rfl)

private def withCoordinates : RuntimeCtx .quantum :=
  (withFirst E m).addOwnedLayout ⟨0⟩ (InversePreparation.inputLayout p.size)
    (drop_fresh E m _ 1 _ _ rfl) (drop_physical E m _ 1 _ _ rfl)

private def withAuxiliary : RuntimeCtx .quantum :=
  (withCoordinates E m).addOwnedLayout InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout p.size)
    (drop_fresh E m _ 0 _ _ rfl) (drop_physical E m _ 0 _ _ rfl)

private lemma withAuxiliary_eq : withAuxiliary E m = quantumContext E m :=
  context_eq _ _ rfl

private def castCircuit {pre post pre' post' : RuntimeCtx .quantum}
    (input : pre = pre') (output : post = post') (code : Circuit Model pre post) :
    Circuit Model pre' post' := input ▸ output ▸ code

private lemma castCircuit_resident {pre post pre' post' : RuntimeCtx .quantum}
    (input : pre = pre') (output : post = post') (code : Circuit Model pre post)
    (exactPeak : ∀ path, code.peakResidentSpace path = post.residentSpace)
    (path : (castCircuit input output code).Path) :
    (castCircuit input output code).peakResidentSpace path = post'.residentSpace := by
  cases input
  cases output
  exact exactPeak path

private lemma castCircuit_auxiliary {pre post pre' post' : RuntimeCtx .quantum}
    (input : pre = pre') (output : post = post') (code : Circuit Model pre post)
    (exactPeak : ∀ path, code.peakAuxiliarySpace path = post.auxiliarySpace)
    (path : (castCircuit input output code).Path) :
    (castCircuit input output code).peakAuxiliarySpace path = post'.auxiliarySpace := by
  cases input
  cases output
  exact exactPeak path

private def zeroBankRaw : Circuit Model (Recovery.PublicInput.frame E m) (withAuxiliary E m) :=
  ((((Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty) (Recovery.PublicInput.frame E m)
    (indexedKey p.size 2) (indexedLayout p.size 2)
    (drop_fresh E m _ 4 _ _ rfl) (drop_physical E m _ 4 _ _ rfl)).seq
      (.prepareZero (withThird E m) (indexedKey p.size 1) (indexedLayout p.size 1)
        (drop_fresh E m _ 3 _ _ rfl) (drop_physical E m _ 3 _ _ rfl))).seq
      (.prepareZero (withSecond E m) (indexedKey p.size 0) (indexedLayout p.size 0)
        (drop_fresh E m _ 2 _ _ rfl) (drop_physical E m _ 2 _ _ rfl))).seq
      (.prepareZero (withFirst E m) ⟨0⟩ (InversePreparation.inputLayout p.size)
        (drop_fresh E m _ 1 _ _ rfl) (drop_physical E m _ 1 _ _ rfl))).seq
      (.prepareZero (withCoordinates E m) InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout p.size)
        (drop_fresh E m _ 0 _ _ rfl) (drop_physical E m _ 0 _ _ rfl))

private def zeroBank : Circuit Model (Recovery.PublicInput.frame E m) (quantumContext E m) :=
  castCircuit rfl (withAuxiliary_eq E m) (zeroBankRaw E m)

private lemma numerator_rest_disjoint : RuntimeCtx.StorageDisjoint
    (NumeratorMeasurement.context p.size)
    ((indexed (p := p)).disjointUnion (Recovery.PublicInput.frame E m) (indexed_disjoint E m)) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    rw [RuntimeCtx.keys_disjointUnion]
    exact List.disjoint_append_right.mpr
      ⟨(RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp
        (indexedContext_disjoint p.size (List.range 3) List.nodup_range).1,
        (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp (numerator_disjoint E m).1⟩
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    rw [RuntimeCtx.physicalIdx_disjointUnion]
    exact List.disjoint_append_right.mpr
      ⟨(RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp
        (indexedContext_disjoint p.size (List.range 3) List.nodup_range).2,
        (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp (numerator_disjoint E m).2⟩

private def bankContext : RuntimeCtx .quantum :=
  (Recovery.Layout.bank p.size).disjointUnion (Recovery.PublicInput.frame E m) (bank_disjoint E m)

private def numeratorCellsRaw :=
  MeasurementCells.allocateFramed (model := Model) (InversePreparation.after p.size)
    ((indexed (p := p)).disjointUnion (Recovery.PublicInput.frame E m) (indexed_disjoint E m))
    2 p.size (numerator_rest_disjoint E m)

private lemma numeratorCells_input :
    (InversePreparation.after p.size).disjointUnion
      ((indexed (p := p)).disjointUnion (Recovery.PublicInput.frame E m) (indexed_disjoint E m))
      (MeasurementCells.original_disjoint _ _ 2 p.size (numerator_rest_disjoint E m)) =
        quantumContext E m := by
  apply context_eq
  exact (List.append_assoc _ _ _).symm

private lemma numeratorCells_output :
    (NumeratorMeasurement.context p.size).disjointUnion
      ((indexed (p := p)).disjointUnion (Recovery.PublicInput.frame E m) (indexed_disjoint E m))
      (numerator_rest_disjoint E m) = bankContext E m := by
  apply context_eq
  exact (List.append_assoc _ _ _).symm

private def numeratorCells : Circuit Model (quantumContext E m) (bankContext E m) :=
  castCircuit (numeratorCells_input E m) (numeratorCells_output E m) (numeratorCellsRaw E m)

private def terminalCells : Circuit Model (bankContext E m) (Recovery.PublicInput.context E m) :=
  MeasurementCells.allocateFramed (model := Model) (Recovery.Layout.bank p.size)
    (Recovery.PublicInput.frame E m) 2 (2 * m) (Recovery.PublicInput.terminal_disjoint E m)

/-- Five actual owned zero preparations precede the two original retained-cell families. -/
def circuit : Circuit Model (Recovery.PublicInput.frame E m) (Recovery.PublicInput.context E m) :=
  ((zeroBank E m).seq (numeratorCells E m)).seq (terminalCells E m)

/-- The endpoint is the exact original terminal entry list beside the borrowed frame. -/
lemma target_entries : (Recovery.PublicInput.context E m).entries =
    (Recovery.Layout.terminal p.size m).entries ++ (Recovery.PublicInput.frame E m).entries := rfl

/-- Allocation leaves each original quantum identity at its declared reduced-terminal position. -/
lemma target_physicalIdx : (Recovery.PublicInput.context E m).physicalIdx =
    (Recovery.Layout.terminal p.size m).physicalIdx :=
  Recovery.PublicInput.context_physicalIdx E m

private lemma append_zero_resident {pre middle : RuntimeCtx .quantum}
    (first : Circuit Model pre middle) (key : StorageKey) {count : Nat}
    (layout : QuantumLayout count) (fresh : key ∉ middle.keys)
    (disjoint : List.Disjoint layout.identities middle.physicalIdx)
    (exactPrefix : ∀ path, first.peakResidentSpace path = middle.residentSpace)
    (path : (first.seq (.prepareZero middle key layout fresh disjoint)).Path) :
    (first.seq (.prepareZero middle key layout fresh disjoint)).peakResidentSpace path =
      (middle.addOwnedLayout key layout fresh disjoint).residentSpace := by
  rw [Circuit.peakResidentSpace_seq, exactPrefix, Circuit.prepare_peakResidentSpace]
  apply SpacePool.max_eq_right
  rw [RuntimeCtx.residentSpace_addOwnedLayout]
  exact fun axis => Nat.le_add_left _ _

private lemma append_zero_auxiliary {pre middle : RuntimeCtx .quantum}
    (first : Circuit Model pre middle) (key : StorageKey) {count : Nat}
    (layout : QuantumLayout count) (fresh : key ∉ middle.keys)
    (disjoint : List.Disjoint layout.identities middle.physicalIdx)
    (exactPrefix : ∀ path, first.peakAuxiliarySpace path = middle.auxiliarySpace)
    (path : (first.seq (.prepareZero middle key layout fresh disjoint)).Path) :
    (first.seq (.prepareZero middle key layout fresh disjoint)).peakAuxiliarySpace path =
      (middle.addOwnedLayout key layout fresh disjoint).auxiliarySpace := by
  rw [Circuit.peakAuxiliarySpace_seq, exactPrefix, Circuit.prepare_peakAuxiliarySpace]
  apply SpacePool.max_eq_right
  rw [RuntimeCtx.auxiliarySpace_addOwnedLayout]
  exact fun axis => Nat.le_add_left _ _

private lemma zeroBankRaw_resident (path : (zeroBankRaw E m).Path) :
    (zeroBankRaw E m).peakResidentSpace path = (withAuxiliary E m).residentSpace := by
  unfold zeroBankRaw
  apply append_zero_resident
  intro path
  apply append_zero_resident
  intro path
  apply append_zero_resident
  intro path
  apply append_zero_resident
  intro path
  exact Circuit.prepare_peakResidentSpace _ _ _ _ _ path

private lemma zeroBankRaw_auxiliary (path : (zeroBankRaw E m).Path) :
    (zeroBankRaw E m).peakAuxiliarySpace path = (withAuxiliary E m).auxiliarySpace := by
  unfold zeroBankRaw
  apply append_zero_auxiliary
  intro path
  apply append_zero_auxiliary
  intro path
  apply append_zero_auxiliary
  intro path
  apply append_zero_auxiliary
  intro path
  exact Circuit.prepare_peakAuxiliarySpace _ _ _ _ _ path

private lemma zeroBank_resident (path : (zeroBank E m).Path) :
    (zeroBank E m).peakResidentSpace path = (quantumContext E m).residentSpace :=
  castCircuit_resident rfl (withAuxiliary_eq E m) (zeroBankRaw E m)
    (zeroBankRaw_resident E m) path

private lemma zeroBank_auxiliary (path : (zeroBank E m).Path) :
    (zeroBank E m).peakAuxiliarySpace path = (quantumContext E m).auxiliarySpace :=
  castCircuit_auxiliary rfl (withAuxiliary_eq E m) (zeroBankRaw E m)
    (zeroBankRaw_auxiliary E m) path

private lemma numeratorCells_resident (path : (numeratorCells E m).Path) :
    (numeratorCells E m).peakResidentSpace path = (bankContext E m).residentSpace := by
  apply castCircuit_resident
  intro path
  exact (MeasurementCells.allocateFramed_peakResidentSpace _ _ _ _ _ path).trans
    (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm

private lemma numeratorCells_auxiliary (path : (numeratorCells E m).Path) :
    (numeratorCells E m).peakAuxiliarySpace path = (bankContext E m).auxiliarySpace := by
  apply castCircuit_auxiliary
  intro path
  exact (MeasurementCells.allocateFramed_peakAuxiliarySpace _ _ _ _ _ path).trans
    (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm

private lemma terminalCells_resident (path : (terminalCells E m).Path) :
    (terminalCells E m).peakResidentSpace path = (Recovery.PublicInput.context E m).residentSpace :=
  (MeasurementCells.allocateFramed_peakResidentSpace _ _ _ _ _ path).trans
    (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm

private lemma terminalCells_auxiliary (path : (terminalCells E m).Path) :
    (terminalCells E m).peakAuxiliarySpace path = (Recovery.PublicInput.context E
      m).auxiliarySpace :=
  (MeasurementCells.allocateFramed_peakAuxiliarySpace _ _ _ _ _ path).trans
    (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm

private lemma quantum_bank_resident :
    (quantumContext E m).residentSpace ≤ (bankContext E m).residentSpace := by
  have smaller := MeasurementCells.context_residentSpace_mono
    (InversePreparation.after p.size) 2 (Nat.zero_le p.size)
  change (InversePreparation.after p.size).residentSpace ≤
    (NumeratorMeasurement.context p.size).residentSpace at smaller
  rw [quantumContext, bankContext, RuntimeCtx.residentSpace_disjointUnion,
    RuntimeCtx.residentSpace_disjointUnion, RuntimeCtx.residentSpace_disjointUnion,
    RuntimeCtx.residentSpace_disjointUnion]
  exact fun axis => Nat.add_le_add_right
    (Nat.add_le_add_right (smaller axis) ((indexed (p := p)).residentSpace axis)) _

private lemma quantum_bank_auxiliary :
    (quantumContext E m).auxiliarySpace ≤ (bankContext E m).auxiliarySpace := by
  have smaller := MeasurementCells.context_auxiliarySpace_mono
    (InversePreparation.after p.size) 2 (Nat.zero_le p.size)
  change (InversePreparation.after p.size).auxiliarySpace ≤
    (NumeratorMeasurement.context p.size).auxiliarySpace at smaller
  rw [quantumContext, bankContext, RuntimeCtx.auxiliarySpace_disjointUnion,
    RuntimeCtx.auxiliarySpace_disjointUnion, RuntimeCtx.auxiliarySpace_disjointUnion,
    RuntimeCtx.auxiliarySpace_disjointUnion]
  exact fun axis => Nat.add_le_add_right
    (Nat.add_le_add_right (smaller axis) ((indexed (p := p)).auxiliarySpace axis)) _

private lemma bank_terminal_resident :
    (bankContext E m).residentSpace ≤ (Recovery.PublicInput.context E m).residentSpace := by
  have smaller := MeasurementCells.context_residentSpace_mono
    (Recovery.Layout.bank p.size) 2 (Nat.zero_le (2 * m))
  change (Recovery.Layout.bank p.size).residentSpace ≤
    (Recovery.Layout.terminal p.size m).residentSpace at smaller
  calc
    (bankContext E m).residentSpace =
        (Recovery.Layout.bank p.size).residentSpace + (Recovery.PublicInput.frame E
          m).residentSpace :=
      RuntimeCtx.residentSpace_disjointUnion _ _ (bank_disjoint E m)
    _ ≤ (Recovery.Layout.terminal p.size m).residentSpace + (Recovery.PublicInput.frame E
      m).residentSpace :=
      fun axis => Nat.add_le_add_right (smaller axis) _
    _ = (Recovery.PublicInput.context E m).residentSpace :=
      (RuntimeCtx.residentSpace_disjointUnion _ _ (Recovery.PublicInput.terminal_disjoint E m)).symm

private lemma bank_terminal_auxiliary :
    (bankContext E m).auxiliarySpace ≤ (Recovery.PublicInput.context E m).auxiliarySpace := by
  have smaller := MeasurementCells.context_auxiliarySpace_mono
    (Recovery.Layout.bank p.size) 2 (Nat.zero_le (2 * m))
  change (Recovery.Layout.bank p.size).auxiliarySpace ≤
    (Recovery.Layout.terminal p.size m).auxiliarySpace at smaller
  calc
    (bankContext E m).auxiliarySpace =
        (Recovery.Layout.bank p.size).auxiliarySpace + (Recovery.PublicInput.frame E
          m).auxiliarySpace :=
      RuntimeCtx.auxiliarySpace_disjointUnion _ _ (bank_disjoint E m)
    _ ≤ (Recovery.Layout.terminal p.size m).auxiliarySpace + (Recovery.PublicInput.frame E
      m).auxiliarySpace :=
      fun axis => Nat.add_le_add_right (smaller axis) _
    _ = (Recovery.PublicInput.context E m).auxiliarySpace :=
      (RuntimeCtx.auxiliarySpace_disjointUnion _ _ (Recovery.PublicInput.terminal_disjoint E
        m)).symm

/-- The actual allocating parent peaks at its exact complete final resident context. -/
lemma circuit_peakResidentSpace (path : (circuit E m).Path) :
    (circuit E m).peakResidentSpace path = (Recovery.PublicInput.context E m).residentSpace := by
  change (((zeroBank E m).seq (numeratorCells E m)).seq (terminalCells E m)).Path at path
  change (((zeroBank E m).seq (numeratorCells E m)).seq (terminalCells E m)).peakResidentSpace
    path = (Recovery.PublicInput.context E m).residentSpace
  rw [Circuit.peakResidentSpace_seq, Circuit.peakResidentSpace_seq,
    zeroBank_resident, numeratorCells_resident, terminalCells_resident,
    SpacePool.max_eq_right (quantum_bank_resident E m)]
  exact SpacePool.max_eq_right (bank_terminal_resident E m)

/-- All owned zero systems and retained cells contribute to the exact auxiliary peak. -/
lemma circuit_peakAuxiliarySpace (path : (circuit E m).Path) :
    (circuit E m).peakAuxiliarySpace path = (Recovery.PublicInput.context E m).auxiliarySpace := by
  change (((zeroBank E m).seq (numeratorCells E m)).seq (terminalCells E m)).Path at path
  change (((zeroBank E m).seq (numeratorCells E m)).seq (terminalCells E m)).peakAuxiliarySpace
    path = (Recovery.PublicInput.context E m).auxiliarySpace
  rw [Circuit.peakAuxiliarySpace_seq, Circuit.peakAuxiliarySpace_seq,
    zeroBank_auxiliary, numeratorCells_auxiliary, terminalCells_auxiliary,
    SpacePool.max_eq_right (quantum_bank_auxiliary E m)]
  exact SpacePool.max_eq_right (bank_terminal_auxiliary E m)

/-- The peak includes both original borrowed point encodings at their full resident shapes. -/
lemma circuit_peakResidentSpace_points (path : (circuit E m).Path) :
    (circuit E m).peakResidentSpace path =
      (Recovery.Layout.terminal p.size m).residentSpace +
        2 • SpacePool.ofShape (ECDLP.Canonical.Runtime.Context.PointShape E) :=
  (circuit_peakResidentSpace E m path).trans (Recovery.PublicInput.context_resident E m)

variable {Reference : Register} {History : Type} [Fintype History]

/-- The actual complete output includes every Store, service, history and allocating path.
The equality only reassociates the real sequential histories. -/
lemma circuit_execute
    (state : State (Recovery.PublicInput.frame E m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (circuit E m).execute environment Reference state =
      ((terminalCells E m).execute environment Reference
        (((zeroBank E m).seq (numeratorCells E m)).execute environment Reference state)).mapHistory
          (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  Circuit.execute_seq (environment := environment) ((zeroBank E m).seq (numeratorCells E m))
    (terminalCells E m) state

/-- Every borrowed point value and its full external-reference correlation is restored. -/
lemma circuit_borrowedRestored
    (state : State (Recovery.PublicInput.frame E m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (circuit E m).BorrowedRestored Reference state ((circuit E m).execute environment Reference
      state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment) (circuit E m) rfl
    Reference state

/-- The actual allocating execution preserves arbitrary subnormalized total mass. -/
lemma circuit_execute_mass
    (state : State (Recovery.PublicInput.frame E m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((circuit E m).execute environment Reference state).mass = state.mass :=
  Circuit.execute_mass (circuit E m) environment Reference state

private lemma castCircuit_quantumTime {pre post pre' post' : RuntimeCtx .quantum}
    (input : pre = pre') (output : post = post') (code : Circuit Model pre post)
    (zero : ∀ path, code.quantumTime path = 0)
    (path : (castCircuit input output code).Path) :
    (castCircuit input output code).quantumTime path = 0 := by
  cases input
  cases output
  exact zero path

private lemma append_zero_quantumTime {pre middle : RuntimeCtx .quantum}
    (first : Circuit Model pre middle) (key : StorageKey) {count : Nat}
    (layout : QuantumLayout count) (fresh : key ∉ middle.keys)
    (disjoint : List.Disjoint layout.identities middle.physicalIdx)
    (prefixZero : ∀ path, first.quantumTime path = 0)
    (path : (first.seq (.prepareZero middle key layout fresh disjoint)).Path) :
    (first.seq (.prepareZero middle key layout fresh disjoint)).quantumTime path = 0 := by
  rcases path with ⟨prefixPath, preparePath⟩
  rw [Circuit.quantumTime_seq, prefixZero, Circuit.quantumTime_prepareZero, Nat.zero_add]

/-- Actual preparation events remain charged; fresh zeros and retains add no gate or query time. -/
lemma circuit_quantumTime (path : (circuit E m).Path) :
    (circuit E m).quantumTime path = 0 := by
  have rawZero (rawPath : (zeroBankRaw E m).Path) :
      (zeroBankRaw E m).quantumTime rawPath = 0 := by
    unfold zeroBankRaw
    apply append_zero_quantumTime
    intro prefixPath
    apply append_zero_quantumTime
    intro prefixPath
    apply append_zero_quantumTime
    intro prefixPath
    apply append_zero_quantumTime
    intro preparePath
    exact Circuit.quantumTime_prepareZero _ _ _ _ _ preparePath
  have bankZero (bankPath : (zeroBank E m).Path) :
      (zeroBank E m).quantumTime bankPath = 0 :=
    castCircuit_quantumTime rfl (withAuxiliary_eq E m) (zeroBankRaw E m) rawZero bankPath
  have numeratorZero (cellPath : (numeratorCells E m).Path) :
      (numeratorCells E m).quantumTime cellPath = 0 := by
    apply castCircuit_quantumTime (numeratorCells_input E m) (numeratorCells_output E m)
      (numeratorCellsRaw E m)
    intro rawPath
    exact MeasurementCells.allocateFramed_depth (model := Model) (InversePreparation.after p.size)
      ((indexed (p := p)).disjointUnion (Recovery.PublicInput.frame E m) (indexed_disjoint E m))
      2 p.size (numerator_rest_disjoint E m) Resource.Event.quantumDuration rawPath
  have terminalZero (cellPath : (terminalCells E m).Path) :
      (terminalCells E m).quantumTime cellPath = 0 :=
    MeasurementCells.allocateFramed_depth (model := Model) (Recovery.Layout.bank p.size)
      (Recovery.PublicInput.frame E m) 2 (2 * m) (Recovery.PublicInput.terminal_disjoint E m)
      Resource.Event.quantumDuration cellPath
  rcases path with ⟨⟨bankPath, numeratorPath⟩, terminalPath⟩
  change (((zeroBank E m).seq (numeratorCells E m)).seq (terminalCells E m)).quantumTime
    ((bankPath, numeratorPath), terminalPath) = 0
  rw [Circuit.quantumTime_seq, Circuit.quantumTime_seq, bankZero, numeratorZero,
    terminalZero, Nat.zero_add]

end

end Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput

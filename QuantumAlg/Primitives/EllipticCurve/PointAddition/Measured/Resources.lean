/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Runtime
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Native.Resources

/-!
# Independent resources of the actual measured point-addition body

The complete three-word bank retains both real quantum controls and all n
finite result cells. Independent native budgets count the actual controlled
offsets, square, selector and exchanges in addition to both measured bodies.
This is the project's concrete schedule, including its reachable exceptional
arm, for the measured arithmetic ingredients of LYL+26.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

open Execution MeasuredUncompute MAU.Inversion.SharedEEA

/-- Every live system is charged, including N and the reused finite measurement cells. -/
def space (width : Nat) : SpacePool .quantum :=
  width • SpacePool.ofShape (.finite 2) + OwnedQubits.space (3 * width + 4 * width.size + 13)

private def cnotBudget : ResourcePool .quantum :=
  ResourcePool.singleton (.gate (.builtin "cnot"))

private def offsetBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.controlForDimension 2 (MAU.Addition.Gidney.modularOffsetNativeBudget width)

private def comparisonBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.controlForDimension 2
    (MAU.Addition.Gidney.comparisonEventBound width • EncodedBit.GateSpec.primitiveAlphabet)

private def pivotBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.controlForDimension 2
    (MAU.Addition.Gidney.pivotEventBound width • MAU.Addition.Gidney.offsetAlphabet)

private def squareBudget (width : Nat) : ResourcePool .quantum :=
  width • cnotBudget +
    (ResourcePool.controlForDimension 2 (MAU.Multiplication.VariableGidney.nativeBudget width) +
      width • cnotBudget)

private def selectorBudget (width : Nat) : ResourcePool .quantum :=
  cnotBudget + comparisonBudget width

/-- Two controlled canonical coordinate differences precede the first measured call. -/
def beforeBudget (width : Nat) : ResourcePool .quantum := offsetBudget width + offsetBudget width

/-- The middle stage uses the existing A, computes N, and executes three actual CNOT exchanges. -/
def middleBudget (width : Nat) : ResourcePool .quantum :=
  offsetBudget width + (squareBudget width + (selectorBudget width + 3 • cnotBudget))

/-- The final stage restores C/N and both output coordinates, including the exceptional arm. -/
def afterBudget (width : Nat) : ResourcePool .quantum :=
  3 • cnotBudget +
    (ResourcePool.controlForDimension 4 (MAU.Addition.Gidney.modularOffsetNativeBudget width) +
      (selectorBudget width + (pivotBudget width + (offsetBudget width + offsetBudget width))))

/-- Independent allowance follows the same five concrete execution stages. -/
def events (width : Nat) : ResourcePool .quantum :=
  beforeBudget width + (InPlaceControlled.events .division width +
    (middleBudget width + (InPlaceControlled.events .multiplication width + afterBudget width)))

/-- Explicit serial duration includes both measured bodies and every actual native occurrence. -/
def depthBound (width : Nat) : Nat :=
  InPlaceControlled.depthBound .division width +
    InPlaceControlled.depthBound .multiplication width +
    6 * MAU.Addition.Gidney.modularOffsetEventBound width +
    MAU.Addition.Gidney.pivotEventBound width + MAU.Multiplication.VariableGidney.eventBound width +
    2 * MAU.Addition.Gidney.comparisonEventBound width + 2 * width + 8

private theorem placement_cost {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (placement : EncodedBit.FullPlacement source target)
    (program : UnitaryCircuit (Qubits source.width))
    (within : program.physical_idx ⊆ List.range source.width) :
    (placement.place program within).eventCost = program.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    EncodedBit.FullPlacement.place_eventTrace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private theorem prefix_cost {width : Nat} (count : Nat) (active : Fin (2 ^ count))
    (program : UnitaryCircuit (Qubits width)) :
    (prefixControl count active program).eventCost =
      ResourcePool.controlForDimension (2 ^ count) program.eventCost := by
  simp only [prefixControl, UnitaryCircuit.reindex_eventCost, UnitaryCircuit.controlAt_eventCost,
    UnitaryCircuit.shiftPhysicalIdx_eventCost, Fintype.card_fin]

private theorem arithmetic_cost (width : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (program : UnitaryCircuit (Qubits (MAU.Addition.Gidney.encoding width).width))
    (within : program.physical_idx ⊆ List.range (MAU.Addition.Gidney.encoding width).width) :
    (placedArithmetic width control coordinate program within).eventCost =
      ResourcePool.controlForDimension (2 ^ controlWidth control) program.eventCost := by
  rw [placedArithmetic, placement_cost, prefix_cost, UnitaryCircuit.prodLeft_eventCost]

private theorem offset_bound (modulus : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) :
    (offset modulus control coordinate constant).eventCost ≤
      ResourcePool.controlForDimension (2 ^ controlWidth control)
        (MAU.Addition.Gidney.modularOffsetNativeBudget modulus.size) := by
  rw [offset, arithmetic_cost]
  apply (ResourcePool.controlForDimension_le_controlForDimension_iff _).mpr
  exact MAU.Addition.Gidney.gidneyModularOffset_native_bound _ _ _

private theorem reflect_bound (modulus : Nat) :
    (reflect modulus).eventCost ≤ pivotBudget modulus.size := by
  rw [reflect, arithmetic_cost]
  apply (ResourcePool.controlForDimension_le_controlForDimension_iff 2).mpr
  exact ResourcePool.le_scaled_of_support_card_le _ _ _
    (MAU.Addition.Gidney.gidneyPivot_native_support _ _)
    (MAU.Addition.Gidney.gidneyPivot_event_count_bound _ _)

private theorem comparison_bound (width : Nat) :
    (compareZero width).eventCost ≤ comparisonBudget width := by
  rw [compareZero, placement_cost, prefix_cost, UnitaryCircuit.prodLeft_eventCost]
  apply (ResourcePool.controlForDimension_le_controlForDimension_iff 2).mpr
  exact ResourcePool.le_scaled_of_support_card_le _ _ _
    (MAU.Addition.Gidney.gidneyComparison_native_support _ _)
    (MAU.Addition.Gidney.gidneyComparison_event_count_bound _ _)

private theorem exchange_cost (width : Nat) :
    (exchangeControls width).eventCost = 3 • cnotBudget := by
  have trace : (exchangeControls width).eventTrace =
      List.replicate 3 (.gate (.builtin "cnot")) := by
    rw [exchangeControls, EncodedBit.swapProgram, EncodedBit.GateSpec.programList_eventTrace]
    rfl
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, trace, ResourcePool.ofList_replicate]
  rfl

private theorem copy_cost (width : Nat) : (squareCopy width).eventCost = width • cnotBudget := by
  have trace : (squareCopy width).eventTrace =
      List.replicate width (.gate (.builtin "cnot")) := by
    rw [squareCopy, EncodedBit.Word.xorIntoProgram, EncodedBit.GateSpec.programList_eventTrace,
      EncodedBit.Word.xorIntoGates, List.map_ofFn]
    change List.ofFn (fun _ : Fin width =>
      (Resource.Event.gate (.builtin "cnot") : Resource.Event .quantum)) = _
    exact List.ofFn_const _ _
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, trace, ResourcePool.ofList_replicate]
  rfl

private theorem square_bound (modulus : Nat) :
    (subtractSquare modulus).eventCost ≤ squareBudget modulus.size := by
  have product : (squareSubtract modulus).eventCost ≤ ResourcePool.controlForDimension 2
      (MAU.Multiplication.VariableGidney.nativeBudget modulus.size) := by
    rw [squareSubtract, placement_cost]
    change (@prefixControl ((ProductPlacement.frameEncoding modulus.size).width + 1) 1 1
      (UnitaryCircuit.prodLeft (n := 1)
        (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)).dagger)
      ).eventCost ≤ _
    rw [prefix_cost, UnitaryCircuit.prodLeft_eventCost,
      UnitaryCircuit.dagger_eventCost]
    apply (ResourcePool.controlForDimension_le_controlForDimension_iff 2).mpr
    exact NativeProductFrame.nativeProductFrame_budget _ _
  rw [subtractSquare, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost, copy_cost]
  exact add_le_add (le_refl _) (add_le_add product (le_refl _))

private theorem selector_bound (width : Nat) :
    (selectNormal width).eventCost ≤ selectorBudget width := by
  rw [selectNormal, UnitaryCircuit.seq_eventCost, EncodedBit.GateSpec.program_eventCost]
  exact add_le_add (le_refl _) (comparison_bound width)

theorem beforeDivision_budget {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : (beforeDivision Q).eventCost ≤ beforeBudget p.size := by
  rw [beforeDivision, UnitaryCircuit.seq_eventCost]
  exact add_le_add (offset_bound _ _ _ _) (offset_bound _ _ _ _)

theorem beforeMultiplication_budget {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : (beforeMultiplication Q).eventCost ≤ middleBudget p.size := by
  simp only [beforeMultiplication, UnitaryCircuit.seq_eventCost]
  exact add_le_add (offset_bound _ _ _ _) (add_le_add (square_bound _)
    (add_le_add (selector_bound _) (exchange_cost _).le))

theorem afterMultiplication_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : (afterMultiplication E Q).eventCost ≤ afterBudget p.size := by
  simp only [afterMultiplication, UnitaryCircuit.seq_eventCost, UnitaryCircuit.dagger_eventCost]
  exact add_le_add (exchange_cost _).le (add_le_add (offset_bound _ _ _ _)
    (add_le_add (selector_bound _) (add_le_add (reflect_bound _)
      (add_le_add (offset_bound _ _ _ _) (offset_bound _ _ _ _)))))

private theorem native_pool (width : Nat)
    (program : UnitaryCircuit (Qubits (encoding width).width))
    (within : program.physical_idx ⊆ List.range (encoding width).width)
    (path : (nativeCode width program within).Path) :
    (nativeCode width program within).resourcePool path = program.eventCost := by
  change ResourcePool.ofList (runtimeProgram width program).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, runtimeProgram_cost]

private theorem arithmetic_budget (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (arithmetic operation modulus prime).Path) :
    (arithmetic operation modulus prime).resourcePool path ≤
      InPlaceControlled.events operation modulus.size := by
  obtain ⟨original, rfl⟩ := (ContextUnion.frameLocalPathEquiv
    (InPlaceControlled.body operation modulus prime) (InPlaceControlled.body_isLocal _ _ _)
      (selectorContext modulus.size) (selector_disjoint modulus.size)).surjective path
  exact (ContextUnion.frameLocal_resourcePool _ _ _ _ original).le.trans
    (InPlaceControlled.body_budget operation modulus prime original)

/-- Every actual path pays for both measured calls and every explicitly placed native stage. -/
theorem body_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (body E Q).Path) :
    (body E Q).resourcePool path ≤ events p.size := by
  change ResourcePool.ofList
    ((nativeCode p.size (beforeDivision Q) (beforeDivision_within Q)).eventTrace path.1 ++
      ((arithmetic .division p Fact.out).eventTrace path.2.1 ++
        ((nativeCode p.size (beforeMultiplication Q) (beforeMultiplication_within Q)).eventTrace
          path.2.2.1 ++ ((arithmetic .multiplication p Fact.out).eventTrace path.2.2.2.1 ++
            (nativeCode p.size (afterMultiplication E Q)
              (afterMultiplication_within E Q)).eventTrace path.2.2.2.2)))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add ((native_pool _ _ _ _).le.trans (beforeDivision_budget Q))
    (add_le_add (arithmetic_budget _ _ _ _) (add_le_add
      ((native_pool _ _ _ _).le.trans (beforeMultiplication_budget Q))
      (add_le_add (arithmetic_budget _ _ _ _)
        ((native_pool _ _ _ _).le.trans (afterMultiplication_budget E Q)))))

private theorem count_of_budget {pre post : RuntimeCtx .quantum} (code : Circuit pre post)
    (path : code.Path) (budget : ResourcePool .quantum)
    (bounded : code.resourcePool path ≤ budget) :
    (code.eventTrace path).length ≤ budget.card :=
  Multiset.card_le_card bounded

/-- The actual event count is bounded by the independent native-coordinate allowance. -/
theorem body_event_count {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (body E Q).Path) :
    ((body E Q).eventTrace path).length ≤ (events p.size).card :=
  count_of_budget (body E Q) path (events p.size) (body_budget E Q path)

private theorem controlled_card (count : Nat) (pool : ResourcePool .quantum) :
    (ResourcePool.controlForDimension count pool).card = pool.card :=
  Multiset.card_map _ _

private theorem offset_count (modulus : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) :
    (offset modulus control coordinate constant).eventCost.card ≤
      MAU.Addition.Gidney.modularOffsetEventBound modulus.size := by
  rw [offset, arithmetic_cost, controlled_card]
  exact MAU.Addition.Gidney.gidneyModularOffset_event_count_bound _ _ _

private theorem reflect_count (modulus : Nat) :
    (reflect modulus).eventCost.card ≤ MAU.Addition.Gidney.pivotEventBound modulus.size := by
  rw [reflect, arithmetic_cost, controlled_card]
  exact MAU.Addition.Gidney.gidneyPivot_event_count_bound _ _

private theorem selector_count (width : Nat) :
    (selectNormal width).eventCost.card ≤ 1 + MAU.Addition.Gidney.comparisonEventBound width := by
  rw [selectNormal, UnitaryCircuit.seq_eventCost, Multiset.card_add,
    EncodedBit.GateSpec.program_eventCost, compareZero, placement_cost, prefix_cost,
    UnitaryCircuit.prodLeft_eventCost, controlled_card]
  exact Nat.add_le_add_left (MAU.Addition.Gidney.gidneyComparison_event_count_bound _ _) 1

private theorem exchange_count (width : Nat) : (exchangeControls width).eventCost.card = 3 := by
  rw [exchange_cost]
  simp [cnotBudget, ResourcePool.singleton]

private theorem square_count (modulus : Nat) :
    (subtractSquare modulus).eventCost.card ≤
      2 * modulus.size + MAU.Multiplication.VariableGidney.eventBound modulus.size := by
  have product : (squareSubtract modulus).eventCost.card ≤
      MAU.Multiplication.VariableGidney.eventBound modulus.size := by
    rw [squareSubtract, placement_cost]
    change (@prefixControl ((ProductPlacement.frameEncoding modulus.size).width + 1) 1 1
      (UnitaryCircuit.prodLeft (n := 1)
        (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)).dagger)
      ).eventCost.card ≤ _
    rw [prefix_cost, UnitaryCircuit.prodLeft_eventCost,
      UnitaryCircuit.dagger_eventCost, controlled_card]
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
      NativeProductFrame.nativeProductFrame_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]
    exact MAU.Multiplication.VariableGidney.variableGidney_event_count _ _
  rw [subtractSquare, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    Multiset.card_add, Multiset.card_add, copy_cost]
  have copies : (modulus.size • cnotBudget).card = modulus.size := by
    simp [cnotBudget, ResourcePool.singleton]
  rw [copies]
  omega

private theorem before_count {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : (beforeDivision Q).eventCost.card ≤
      2 * MAU.Addition.Gidney.modularOffsetEventBound p.size := by
  rw [beforeDivision, UnitaryCircuit.seq_eventCost, Multiset.card_add]
  have left := offset_count p .supplied .x (constantWord (-Q.x))
  have right := offset_count p .supplied .y (constantWord (-Q.y))
  omega

private theorem middle_count {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : (beforeMultiplication Q).eventCost.card ≤
      MAU.Addition.Gidney.modularOffsetEventBound p.size + 2 * p.size +
        MAU.Multiplication.VariableGidney.eventBound p.size +
          MAU.Addition.Gidney.comparisonEventBound p.size + 4 := by
  simp only [beforeMultiplication, UnitaryCircuit.seq_eventCost, Multiset.card_add, exchange_count]
  have offset := offset_count p .supplied .x (constantWord (3 * Q.x))
  have product := square_count p
  have selector := selector_count p.size
  omega

private theorem after_count {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : (afterMultiplication E Q).eventCost.card ≤
      3 * MAU.Addition.Gidney.modularOffsetEventBound p.size +
        MAU.Addition.Gidney.pivotEventBound p.size +
          MAU.Addition.Gidney.comparisonEventBound p.size + 4 := by
  simp only [afterMultiplication, UnitaryCircuit.seq_eventCost, UnitaryCircuit.dagger_eventCost,
    Multiset.card_add, exchange_count]
  have exceptional := offset_count p .exceptional .y (constantWord (-exceptionalSlope E Q))
  have x := offset_count p .supplied .x (constantWord (Q.x + 1))
  have y := offset_count p .supplied .y (constantWord (-Q.y))
  have selector := selector_count p.size
  have pivot := reflect_count p
  omega

private theorem native_depth (width : Nat)
    (program : UnitaryCircuit (Qubits (encoding width).width))
    (within : program.physical_idx ⊆ List.range (encoding width).width)
    (path : (nativeCode width program within).Path) :
    (nativeCode width program within).depth (fun _ => 1) path ≤ program.eventCost.card := by
  change program.evaluatedEventDepth (fun _ => 1) + 0 ≤ _
  rw [Nat.add_zero]
  exact ShiftResources.unitDepth_le_count program

private theorem arithmetic_depth (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (arithmetic operation modulus prime).Path) :
    (arithmetic operation modulus prime).depth (fun _ => 1) path ≤
      InPlaceControlled.depthBound operation modulus.size := by
  obtain ⟨original, rfl⟩ := (ContextUnion.frameLocalPathEquiv
    (InPlaceControlled.body operation modulus prime) (InPlaceControlled.body_isLocal _ _ _)
      (selectorContext modulus.size) (selector_disjoint modulus.size)).surjective path
  exact (ContextUnion.frameLocal_depth _ _ _ _ (fun _ => 1) original).le.trans
    (InPlaceControlled.body_depth operation modulus prime original)

/-- The actual five-stage execution meets the independent complete serial depth allowance. -/
theorem body_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (body E Q).Path) :
    (body E Q).depth (fun _ => 1) path ≤ depthBound p.size := by
  have before := (native_depth p.size (beforeDivision Q) (beforeDivision_within Q) path.1).trans
    (before_count Q)
  have division := arithmetic_depth .division p Fact.out path.2.1
  have middle := (native_depth p.size (beforeMultiplication Q) (beforeMultiplication_within Q)
    path.2.2.1).trans (middle_count Q)
  have multiplication := arithmetic_depth .multiplication p Fact.out path.2.2.2.1
  have after := (native_depth p.size (afterMultiplication E Q) (afterMultiplication_within E Q)
    path.2.2.2.2).trans (after_count E Q)
  change (nativeCode p.size (beforeDivision Q) (beforeDivision_within Q)).depth (fun _ => 1)
      path.1 + ((arithmetic .division p Fact.out).depth (fun _ => 1) path.2.1 +
        ((nativeCode p.size (beforeMultiplication Q) (beforeMultiplication_within Q)).depth
          (fun _ => 1) path.2.2.1 +
            ((arithmetic .multiplication p Fact.out).depth (fun _ => 1) path.2.2.2.1 +
              (nativeCode p.size (afterMultiplication E Q) (afterMultiplication_within E Q)).depth
                (fun _ => 1) path.2.2.2.2))) ≤ _
  unfold depthBound
  omega

private theorem selector_resident (width : Nat) :
    (selectorContext width).residentSpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (selectorQubitLayout width).toQuantumLayout_dimensionCount dimension

private theorem selector_auxiliary (width : Nat) :
    (selectorContext width).auxiliarySpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (selectorQubitLayout width).toQuantumLayout_dimensionCount dimension

private theorem selector_space (width : Nat) :
    InPlaceControlled.space width + OwnedQubits.space 1 = space width := by
  rw [InPlaceControlled.space, add_assoc, ← InPlaceControlled.ownedSpace_add]
  have count : 3 * width + 4 * width.size + 12 + 1 = 3 * width + 4 * width.size + 13 := by omega
  rw [count]
  rfl

/-- The complete allocated context owns exactly the independently prescribed storage. -/
theorem context_resident (width : Nat) : (context width).residentSpace = space width := by
  rw [context, RuntimeCtx.residentSpace_disjointUnion,
    InPlaceControlled.context_resident, selector_resident]
  exact selector_space width

theorem context_auxiliary (width : Nat) : (context width).auxiliarySpace = space width := by
  rw [context, RuntimeCtx.auxiliarySpace_disjointUnion,
    InPlaceControlled.context_auxiliary, selector_auxiliary]
  exact selector_space width

/-- Every actual path retains exactly the complete field/history/control frame and result cells. -/
theorem body_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (body E Q).Path) :
    (body E Q).peakResidentSpace path = space p.size := by
  have upper := (body E Q).peakResidentSpace_le_of_visited path
    (context p.size).residentSpace (by
      intro visited present
      rw [ContextUnion.local_visited _ (body_isLocal E Q) path visited present])
  have lower := (body E Q).residentSpace_le_peak_of_visited path
    (context p.size) (ContextUnion.local_pre_mem _ (body_isLocal E Q) path)
  exact (le_antisymm upper lower).trans (context_resident p.size)

theorem body_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (body E Q).Path) :
    (body E Q).peakAuxiliarySpace path = space p.size := by
  have upper := (body E Q).peakAuxiliarySpace_le_of_visited path
    (context p.size).auxiliarySpace (by
      intro visited present
      rw [ContextUnion.local_visited _ (body_isLocal E Q) path visited present])
  have lower := (body E Q).auxiliarySpace_le_peak_of_visited path
    (context p.size) (ContextUnion.local_pre_mem _ (body_isLocal E Q) path)
  exact (le_antisymm upper lower).trans (context_auxiliary p.size)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

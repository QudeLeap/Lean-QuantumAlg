/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Components.GateModel.Algorithm
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
open BinaryLabelEncoding EncodedBit.GateSpec

private lemma pool_add_mono
    {a b c d : ResourcePool (.quantum AlgorithmGate.model .empty)}
    (left : a ≤ b) (right : c ≤ d) : a + c ≤ b + d := add_le_add left right

private lemma pool_trans
    {a b c : ResourcePool (.quantum AlgorithmGate.model .empty)}
    (left : a ≤ b) (right : b ≤ c) : a ≤ c := left.trans right

private lemma pool_add_six
    {a b c d e f A B C D E F : ResourcePool (.quantum AlgorithmGate.model .empty)}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) (he : e ≤ E) (hf : f ≤ F) :
    a + b + c + d + e + f ≤ A + B + C + D + E + F :=
  pool_add_mono (pool_add_mono (pool_add_mono (pool_add_mono (pool_add_mono ha hb) hc) hd) he) hf

/-- Every live system includes both controls and the reused measurement cells. -/
def space (width : Nat) : SpacePool .quantum :=
  width • SpacePool.ofShape (.finite 2) + OwnedQubits.space (3 * width + 4 * width.size + 13)

private def cnotBudget : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.singleton (.gate .cnot)

private def controlledBudget (control : OffsetControl) (count : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (match control with | .supplied => count | .exceptional => 2) • cnotBudget +
    (match control with | .supplied => 4 * count | .exceptional => 16 * count) •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.toffoli)

private def offsetBudget (width : Nat) (control : OffsetControl := .supplied) :=
  controlledBudget control (MAU.Addition.Gidney.modularOffsetEventBound width)

private def comparisonBudget (width : Nat) :=
  controlledBudget .supplied (MAU.Addition.Gidney.comparisonEventBound width)

private def pivotBudget (width : Nat) :=
  controlledBudget .supplied (MAU.Addition.Gidney.pivotEventBound width)

private def squareBudget (width : Nat) :=
  width • cnotBudget + controlledBudget .supplied
    (MAU.Multiplication.VariableGidney.eventBound width) + width • cnotBudget

private def selectorBudget (width : Nat) := cnotBudget + comparisonBudget width

/-- Two real controlled coordinate offsets precede the measured division. -/
def beforeBudget (width : Nat) := offsetBudget width + offsetBudget width

/-- The middle allowance charges the actual square, selector and three-CNOT swap. -/
def middleBudget (width : Nat) :=
  offsetBudget width + squareBudget width + selectorBudget width + 3 • cnotBudget

/-- Mixed-polarity cleanup includes both controlled X gates and the reversed selector word. -/
def afterBudget (width : Nat) :=
  3 • cnotBudget + offsetBudget width .exceptional + selectorBudget width +
    pivotBudget width + offsetBudget width + offsetBudget width

/-- Independent native-coordinate allowances for all five executed stages. -/
public def events (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  beforeBudget width + (InPlaceControlled.events .division width +
    (middleBudget width + (InPlaceControlled.events .multiplication width + afterBudget width)))

/-- The measured point-addition allowance's one-qubit coordinate comes from its
two controlled arithmetic bodies; the surrounding controls use other gates. -/
lemma events_singleQubit_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (events width) =
      8 + 12 * width + 4 * MAU.Multiplication.VariableGidney.eventBound width := by
  simp [events, beforeBudget, middleBudget, afterBudget, offsetBudget,
    comparisonBudget, pivotBudget, squareBudget, selectorBudget, cnotBudget,
    controlledBudget, InPlaceControlled.events_singleQubit_count]
  omega

/-- Both controlled arithmetic bodies and the literal outer CNOT controls
contribute to the point-addition CNOT allowance. -/
lemma events_cnot_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (events width) =
      5 * MAU.Addition.Gidney.modularOffsetEventBound width +
      12 * width + 7 * MAU.Multiplication.VariableGidney.eventBound width +
      2 * MAU.Addition.Gidney.comparisonEventBound width +
      MAU.Addition.Gidney.pivotEventBound width +
      4 * ForwardResources.inPlaceBound width + 10 := by
  simp [events, beforeBudget, middleBudget, afterBudget, offsetBudget,
    comparisonBudget, pivotBudget, squareBudget, selectorBudget, cnotBudget,
    controlledBudget, InPlaceControlled.events_cnot_count]
  omega

/-- The two controlled arithmetic bodies and outer controls give the Toffoli allowance. -/
lemma events_toffoli_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (events width) =
      36 * MAU.Addition.Gidney.modularOffsetEventBound width +
      16 * MAU.Multiplication.VariableGidney.eventBound width +
      8 * MAU.Addition.Gidney.comparisonEventBound width +
      4 * MAU.Addition.Gidney.pivotEventBound width +
      16 * ForwardResources.inPlaceBound width + 2 * width := by
  simp [events, beforeBudget, middleBudget, afterBudget, offsetBudget,
    comparisonBudget, pivotBudget, squareBudget, selectorBudget, cnotBudget,
    controlledBudget, InPlaceControlled.events_toffoli_count]
  omega

/-- The actual 256-bit measured point-addition one-qubit allowance. -/
public lemma events_singleQubit_count_256 :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (events 256) = 12384882134024 := by
  rw [events_singleQubit_count, MAU.Multiplication.VariableGidney.eventBound_256]

/-- The actual 256-bit measured point-addition CNOT allowance. -/
public lemma events_cnot_count_256 :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (events 256) = 54175995030980682952 := by
  rw [events_cnot_count]
  decide

/-- The actual 256-bit measured point-addition Toffoli allowance. -/
public lemma events_toffoli_count_256 :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (events 256) = 216703942969323571736 := by
  rw [events_toffoli_count]
  decide

/-- Serial native stages and the accepted measured arithmetic depth allowances. -/
def depthBound (width : Nat) : Nat :=
  (beforeBudget width).card + InPlaceControlled.depthBound .division width +
    (middleBudget width).card + InPlaceControlled.depthBound .multiplication width +
      (afterBudget width).card

private def gatePool {Data : Type} {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding)) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.ofList (gates.map (event .empty))

private lemma gatePool_append {Data : Type} {encoding : BinaryLabelEncoding Data}
    (first second : List (EncodedBit.GateSpec encoding)) :
    gatePool (first ++ second) = gatePool first + gatePool second := by
  simp only [gatePool, List.map_append, ResourcePool.ofList_append]

private lemma gatePool_reverse {Data : Type} {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding)) : gatePool gates.reverse = gatePool gates := by
  simp [gatePool, List.map_reverse, ResourcePool.ofList]

private lemma gatePool_place {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (placement : EncodedBit.FullPlacement source target)
    (gates : List (EncodedBit.GateSpec source)) :
    gatePool (gates.map placement.placeGate) = gatePool gates := by
  simp only [gatePool, List.map_map, Function.comp_def,
    EncodedBit.FullPlacement.placeGate_event]

private lemma prefix_budget {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (control : OffsetControl)
    (source : List (EncodedBit.GateSpec data)) (count : Nat) (bounded : source.length ≤ count) :
    gatePool (prefixControlGates data bits bitsWire capacity control source) ≤
      controlledBudget control count := by
  let gates := prefixControlGates data bits bitsWire capacity control source
  have counts := pointPrefixControlGates_counts data bits bitsWire capacity control source
  have sourceLength := length_eq_multiplicity_sums source
  have cost : gatePool gates =
      (programList (QubitLayout.canonical _) .empty gates).eventCost :=
    (programList_eventCost _ _ gates).symm
  rw [cost]
  apply ResourcePool.le_iff_count.mpr
  intro focus
  by_cases single : focus = .gate .singleQubit
  · subst focus
    rw [programList_x_count_eq_sum, counts.1]
    exact Nat.zero_le _
  by_cases cnot : focus = .gate .cnot
  · subst focus
    rw [programList_cnot_count_eq_sum, counts.2.1]
    cases control <;>
      simp only [controlledBudget, cnotBudget, ResourcePool.count_add,
        ResourcePool.count_nsmul, ResourcePool.count_singleton, ↓reduceIte,
        mul_one] <;> omega
  by_cases toffoli : focus = .gate .toffoli
  · subst focus
    rw [programList_toffoli_count_eq_sum, counts.2.2]
    cases control <;>
      simp only [controlledBudget, cnotBudget, ResourcePool.count_add,
        ResourcePool.count_nsmul, ResourcePool.count_singleton, ↓reduceIte,
        mul_one] <;> omega
  have outside : focus ∉ primitiveAlphabet := by
    simpa [primitiveAlphabet, ResourcePool.ofList] using And.intro single (And.intro cnot toffoli)
  rw [programList_count_zero_of_not_mem_primitiveAlphabet _ _ _ outside]
  exact Nat.zero_le _

private lemma arithmetic_bound (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (source : List (EncodedBit.GateSpec
      (MAU.Addition.Gidney.encoding width))) (count : Nat) (bounded : source.length ≤ count) :
    gatePool (placedArithmeticGates width control coordinate source) ≤
      controlledBudget control count := by
  rw [placedArithmeticGates, gatePool_place, arithmeticControlGates]
  apply prefix_budget
  simpa only [List.length_map] using bounded

private lemma offset_bound (modulus : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) :
    gatePool (offsetGates modulus control coordinate constant) ≤
      offsetBudget modulus.size control := by
  apply arithmetic_bound
  have bounded := MAU.Addition.Gidney.gidneyModularOffset_event_count_bound modulus.size
    (InPlaceArithmetic.modulusWord modulus) (fittedConstant modulus constant)
  simpa only [MAU.Addition.Gidney.modularOffsetProgram, programList_eventCost_card] using bounded

private lemma reflect_bound (modulus : Nat) :
    gatePool (reflectGates modulus) ≤ pivotBudget modulus.size := by
  apply arithmetic_bound
  have bounded := MAU.Addition.Gidney.gidneyPivot_event_count_bound modulus.size
    (InPlaceArithmetic.modulusWord modulus)
  simpa only [MAU.Addition.Gidney.pivotProgram, programList_eventCost_card] using bounded

private lemma comparison_bound (width : Nat) :
    gatePool (compareZeroGates width) ≤ comparisonBudget width := by
  rw [compareZeroGates, gatePool_place, arithmeticControlGates]
  apply prefix_budget
  simp only [List.length_map]
  exact MAU.Addition.Gidney.gidneyComparisonGates_length_bound _ _

private lemma exchange_cost (width : Nat) :
    gatePool (exchangeControlGates width) = 3 • cnotBudget := by
  have trace : (exchangeControlGates width).map (event .empty) =
      List.replicate 3 (.gate AlgorithmGate.Coordinate.cnot) := rfl
  rw [gatePool, trace, ResourcePool.ofList_replicate]
  rfl

private lemma copy_cost (width : Nat) :
    gatePool (squareCopyGates width) = width • cnotBudget := by
  have trace : (squareCopyGates width).map (event .empty) =
      List.replicate width (.gate .cnot) := by
    rw [squareCopyGates, EncodedBit.Word.xorIntoGates, List.map_ofFn]
    change List.ofFn (fun _ : Fin width =>
      (.gate AlgorithmGate.Coordinate.cnot :
        Resource.Event (.quantum AlgorithmGate.model .empty))) = _
    exact List.ofFn_const _ _
  rw [gatePool, trace, ResourcePool.ofList_replicate]
  rfl

private lemma square_bound (modulus : Nat) :
    gatePool (subtractSquareGates modulus) ≤ squareBudget modulus.size := by
  have product : gatePool (squareSubtractGates modulus) ≤ controlledBudget .supplied
      (MAU.Multiplication.VariableGidney.eventBound modulus.size) := by
    rw [squareSubtractGates, gatePool_place]
    apply prefix_budget
    simp only [List.length_map, List.length_reverse]
    exact NativeProductFrame.nativeProductFrame_gates_length_bound _ _
  rw [subtractSquareGates, gatePool_append, gatePool_append, copy_cost]
  exact add_le_add (add_le_add (le_refl _) product) (le_refl _)

private lemma selector_bound (width : Nat) :
    gatePool (selectNormalGates width) ≤ selectorBudget width := by
  rw [selectNormalGates, gatePool_append]
  exact add_le_add (le_refl _) (comparison_bound width)

-- Resource algebra uses the compiled words through their proved interfaces.
attribute [local irreducible] offsetGates subtractSquareGates selectNormalGates
  exchangeControlGates reflectGates constantWord exceptionalSlope
  controlledBudget offsetBudget comparisonBudget pivotBudget squareBudget selectorBudget

lemma beforeDivision_budget {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : (beforeDivision Q).eventCost ≤ beforeBudget p.size := by
  rw [beforeDivision, programList_eventCost]
  change gatePool (beforeDivisionGates Q) ≤ _
  rw [beforeDivisionGates, gatePool_append]
  exact add_le_add (offset_bound _ _ _ _) (offset_bound _ _ _ _)

lemma beforeMultiplication_budget {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : (beforeMultiplication Q).eventCost ≤ middleBudget p.size := by
  rw [beforeMultiplication, programList_eventCost]
  change gatePool (beforeMultiplicationGates Q) ≤ _
  simp only [beforeMultiplicationGates, gatePool_append]
  exact add_le_add (add_le_add (add_le_add (offset_bound _ _ _ _)
    (square_bound _)) (selector_bound _)) (exchange_cost _).le

lemma afterMultiplication_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : (afterMultiplication E Q).eventCost ≤ afterBudget p.size := by
  rw [afterMultiplication, programList_eventCost]
  change gatePool (afterMultiplicationGates E Q) ≤ _
  simp only [afterMultiplicationGates, gatePool_append, gatePool_reverse]
  exact pool_add_six (exchange_cost p.size).le
    (offset_bound p .exceptional .y (constantWord (-exceptionalSlope E Q)))
    (selector_bound p.size) (reflect_bound p)
    (offset_bound p .supplied .x (constantWord (Q.x + 1)))
    (offset_bound p .supplied .y (constantWord (-Q.y)))

attribute [local irreducible] beforeDivision beforeMultiplication afterMultiplication
  InPlaceControlled.body beforeBudget middleBudget afterBudget

private lemma native_pool {allowAllocation : Bool} (width : Nat) (program : NativeCircuit width)
    (path : (nativeCode width program allowAllocation).Path) :
    (nativeCode width program allowAllocation).resourcePool path = program.eventCost := by
  change ResourcePool.ofList (runtimeProgram width program).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, runtimeProgram_cost]

private lemma native_budget {allowAllocation : Bool} (width : Nat) (program : NativeCircuit width)
    (budget : ResourcePool (.quantum AlgorithmGate.model .empty))
    (bounded : program.eventCost ≤ budget) (path : (nativeCode width program
      allowAllocation).Path) :
    (nativeCode width program allowAllocation).resourcePool path ≤ budget :=
  pool_trans (native_pool (allowAllocation := allowAllocation) width program path).le bounded

private lemma arithmetic_budget {allowAllocation : Bool} (operation : InPlaceTarget.Operation)
    (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (arithmetic operation modulus prime allowAllocation).Path) :
    (arithmetic operation modulus prime allowAllocation).resourcePool path ≤
      InPlaceControlled.events operation modulus.size := by
  exact (Circuit.resourcePool_embed (allowAllocation := allowAllocation)
    (ContextEmbedding.alongUnion (InPlaceControlled.context modulus.size)
      (selectorContext modulus.size) (selector_disjoint modulus.size))
    (InPlaceControlled.body operation modulus prime (allowAllocation := false)) path).le.trans
      (InPlaceControlled.body_budget (allowAllocation := false) operation modulus prime path)

/-- Every actual path pays for both measured calls and all literal native stages. -/
lemma body_budget {allowAllocation : Bool} {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact
    p.Prime]
    (Q : AffinePoint E) (path : (body E Q allowAllocation).Path) :
    (body E Q allowAllocation).resourcePool path ≤ events p.size := by
  change ResourcePool.ofList
    ((nativeCode p.size (beforeDivision Q) allowAllocation).eventTrace path.1 ++
      ((arithmetic .division p Fact.out allowAllocation).eventTrace path.2.1 ++
        ((nativeCode p.size (beforeMultiplication Q) allowAllocation).eventTrace path.2.2.1 ++
          ((arithmetic .multiplication p Fact.out allowAllocation).eventTrace path.2.2.2.1 ++
            (nativeCode p.size (afterMultiplication E Q) allowAllocation).eventTrace
              path.2.2.2.2)))) ≤ _
  simp only [ResourcePool.ofList_append]
  unfold events
  apply add_le_add
  · exact (native_pool (allowAllocation := allowAllocation) p.size (beforeDivision Q)
    path.1).le.trans (beforeDivision_budget Q)
  · apply add_le_add
    · exact arithmetic_budget (allowAllocation := allowAllocation) .division p Fact.out path.2.1
    · apply add_le_add
      · exact (native_pool (allowAllocation := allowAllocation) p.size (beforeMultiplication Q)
        path.2.2.1).le.trans
          (beforeMultiplication_budget Q)
      · apply add_le_add
        · exact arithmetic_budget (allowAllocation := allowAllocation)
            .multiplication p Fact.out path.2.2.2.1
        · exact native_budget (allowAllocation := allowAllocation) p.size
            (afterMultiplication E Q) (afterBudget p.size)
            (afterMultiplication_budget E Q) path.2.2.2.2

/-- Exact emitted events are bounded by the independent native-coordinate allowance. -/
lemma body_event_count {allowAllocation : Bool} {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime]
    (Q : AffinePoint E) (path : (body E Q allowAllocation).Path) :
    ((body E Q allowAllocation).eventTrace path).length ≤ (events p.size).card :=
  Multiset.card_le_card (body_budget (allowAllocation := allowAllocation) E Q path)

private lemma native_depth {allowAllocation : Bool} (width : Nat) (program : NativeCircuit width)
    (path : (nativeCode width program allowAllocation).Path) :
    (nativeCode width program allowAllocation).depth (fun _ => 1) path ≤ program.eventCost.card
      := by
  change (runtimeProgram width program).evaluatedEventDepth (fun _ => 1) + 0 ≤ _
  rw [Nat.add_zero, ← runtimeProgram_cost width program]
  exact ShiftResources.unitDepth_le_count _

private lemma arithmetic_depth {allowAllocation : Bool} (operation : InPlaceTarget.Operation)
    (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (arithmetic operation modulus prime allowAllocation).Path) :
    (arithmetic operation modulus prime allowAllocation).depth (fun _ => 1) path ≤
      InPlaceControlled.depthBound operation modulus.size := by
  change (InPlaceControlled.body operation modulus prime (allowAllocation := false)).depth
    (fun _ => 1) path ≤ _
  exact InPlaceControlled.body_depth (allowAllocation := false) operation modulus prime path

/-- Serial depth is charged from actual native stages and the accepted measured depth laws. -/
lemma body_depth {allowAllocation : Bool} {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact
    p.Prime]
    (Q : AffinePoint E) (path : (body E Q allowAllocation).Path) :
    (body E Q allowAllocation).depth (fun _ => 1) path ≤ depthBound p.size := by
  have before := (native_depth (allowAllocation := allowAllocation) p.size (beforeDivision Q)
    path.1).trans
    (Multiset.card_le_card (beforeDivision_budget Q))
  have division := arithmetic_depth (allowAllocation := allowAllocation) .division p Fact.out
    path.2.1
  have middle := (native_depth (allowAllocation := allowAllocation) p.size (beforeMultiplication
    Q) path.2.2.1).trans
    (Multiset.card_le_card (beforeMultiplication_budget Q))
  have multiplication := arithmetic_depth (allowAllocation := allowAllocation) .multiplication p
    Fact.out path.2.2.2.1
  have after := (native_depth (allowAllocation := allowAllocation) p.size (afterMultiplication E
    Q) path.2.2.2.2).trans
    (Multiset.card_le_card (afterMultiplication_budget E Q))
  change (nativeCode p.size (beforeDivision Q) allowAllocation).depth (fun _ => 1) path.1 +
    ((arithmetic .division p Fact.out allowAllocation).depth (fun _ => 1) path.2.1 +
      ((nativeCode p.size (beforeMultiplication Q) allowAllocation).depth (fun _ => 1) path.2.2.1 +
        ((arithmetic .multiplication p Fact.out allowAllocation).depth (fun _ => 1) path.2.2.2.1 +
          (nativeCode p.size (afterMultiplication E Q) allowAllocation).depth (fun _ => 1)
            path.2.2.2.2))) ≤ _
  unfold depthBound
  omega

private lemma selector_resident (width : Nat) :
    (selectorContext width).residentSpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (selectorQubitLayout width).toQuantumLayout_dimensionCount dimension

private lemma selector_auxiliary (width : Nat) :
    (selectorContext width).auxiliarySpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (selectorQubitLayout width).toQuantumLayout_dimensionCount dimension

private lemma selector_space (width : Nat) :
    InPlaceControlled.space width + OwnedQubits.space 1 = space width := by
  rw [InPlaceControlled.space, add_assoc, ← InPlaceControlled.ownedSpace_add]
  have count : 3 * width + 4 * width.size + 12 + 1 = 3 * width + 4 * width.size + 13 := by omega
  rw [count]
  rfl

/-- The complete allocated context owns exactly the independently prescribed storage. -/
lemma context_resident (width : Nat) : (context width).residentSpace = space width := by
  rw [context, RuntimeCtx.residentSpace_disjointUnion,
    InPlaceControlled.context_resident, selector_resident]
  exact selector_space width

lemma context_auxiliary (width : Nat) : (context width).auxiliarySpace = space width := by
  rw [context, RuntimeCtx.auxiliarySpace_disjointUnion,
    InPlaceControlled.context_auxiliary, selector_auxiliary]
  exact selector_space width

/-- Every actual path retains exactly the complete field/history/control frame and result cells. -/
lemma body_resident {allowAllocation : Bool} {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact
    p.Prime]
    (Q : AffinePoint E) (path : (body E Q allowAllocation).Path) :
    (body E Q allowAllocation).peakResidentSpace path = space p.size := by
  have upper := (body E Q allowAllocation).peakResidentSpace_le_of_visited path
    (context p.size).residentSpace (by
      intro visited present
      have same : visited = context p.size := by
        simpa only [body_visited (allowAllocation := allowAllocation), List.mem_cons,
          List.not_mem_nil, or_false, or_self] using present
      rw [same])
  have lower := (body E Q allowAllocation).residentSpace_le_peak_of_visited path
    (context p.size) (by rw [body_visited (allowAllocation := allowAllocation)]; exact
      List.mem_cons_self)
  exact (le_antisymm upper lower).trans (context_resident p.size)

lemma body_auxiliary {allowAllocation : Bool} {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact
    p.Prime]
    (Q : AffinePoint E) (path : (body E Q allowAllocation).Path) :
    (body E Q allowAllocation).peakAuxiliarySpace path = space p.size := by
  have upper := (body E Q allowAllocation).peakAuxiliarySpace_le_of_visited path
    (context p.size).auxiliarySpace (by
      intro visited present
      have same : visited = context p.size := by
        simpa only [body_visited (allowAllocation := allowAllocation), List.mem_cons,
          List.not_mem_nil, or_false, or_self] using present
      rw [same])
  have lower := (body E Q allowAllocation).auxiliarySpace_le_peak_of_visited path
    (context p.size) (by rw [body_visited (allowAllocation := allowAllocation)]; exact
      List.mem_cons_self)
  exact (le_antisymm upper lower).trans (context_auxiliary p.size)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

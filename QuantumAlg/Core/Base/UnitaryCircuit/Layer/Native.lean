/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Layer
import all QuantumAlg.Core.Base.UnitaryCircuit.Layer
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator

/-!
# A finite layer of disjoint actual native applications

Disjointness concerns the native applications after physical placement. The
constructor compacts and joins exactly those supports, then embeds the resulting
parallel word into the original layout. It preserves the serial native operator
and every event while giving one quantum-time step for a nonempty layer.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {count : Nat}
  {ambient : QuantumLayout count}

/-- The union of the positions touched by the actual native applications. -/
public def nativeSupport : List (GateModel.Application gates ambient) → Finset (Fin count)
  | [] => ∅
  | first :: rest => first.embedding.selection ∪ nativeSupport rest

private lemma disjoint_nativeSupport (first : GateModel.Application gates ambient)
    (rest : List (GateModel.Application gates ambient))
    (separate : ∀ next ∈ rest, Disjoint first.embedding.selection next.embedding.selection) :
    Disjoint first.embedding.selection (nativeSupport rest) := by
  induction rest with
  | nil => simp [nativeSupport]
  | cons next rest ih =>
      apply Finset.disjoint_union_right.mpr
      constructor
      · exact separate next (List.mem_cons_self ..)
      · exact ih (fun other present => separate other (List.mem_cons_of_mem _ present))

private def buildNativeLayer :
    (applications : List (GateModel.Application gates ambient)) →
    applications.Pairwise (fun first second =>
      Disjoint first.embedding.selection second.embedding.selection) →
    {part : LayerPart gates oracles ambient //
      part.placement.selection = nativeSupport applications}
  | [], _ => ⟨LayerPart.empty, LayerPart.layerPart_empty_selection⟩
  | first :: rest, separate =>
      let tail := buildNativeLayer rest (List.pairwise_cons.mp separate).2
      let disjoint : Disjoint (LayerPart.native (oracles := oracles) first).placement.selection
          tail.val.placement.selection := by
        change Disjoint first.embedding.selection _
        rw [tail.property]
        exact disjoint_nativeSupport first rest (List.pairwise_cons.mp separate).1
      ⟨LayerPart.join (LayerPart.native first) tail.val disjoint, by
        rw [LayerPart.layerPart_join_selection, tail.property]
        rfl⟩

/-- Execute a complete finite native layer on certified disjoint physical supports. -/
public def nativeLayer (applications : List (GateModel.Application gates ambient))
    (separate : applications.Pairwise (fun first second =>
      Disjoint first.embedding.selection second.embedding.selection)) :
    UnitaryCircuit gates oracles ambient := (buildNativeLayer applications separate).val.program

/-- Parallel scheduling preserves the exact deterministic traversal of native events. -/
public lemma nativeLayer_eventTrace (applications : List (GateModel.Application gates ambient))
    (separate : applications.Pairwise (fun first second =>
      Disjoint first.embedding.selection second.embedding.selection)) :
    (nativeLayer (oracles := oracles) applications separate).eventTrace =
      applications.map (fun application => .gate application.coordinate) := by
  induction applications with
  | nil => rfl
  | cons first rest ih =>
      change (LayerPart.join (LayerPart.native first) _ _).program.eventTrace = _
      rw [LayerPart.layerPart_join_eventTrace, LayerPart.layerPart_native_eventTrace]
      change [.gate first.coordinate] ++ (nativeLayer rest _).eventTrace = _
      rw [ih]
      rfl

/-- Every original native coordinate has exactly the same multiplicity. -/
public lemma nativeLayer_eventCost (applications : List (GateModel.Application gates ambient))
    (separate : applications.Pairwise (fun first second =>
      Disjoint first.embedding.selection second.embedding.selection)) :
    (nativeLayer (oracles := oracles) applications separate).eventCost =
      ResourcePool.ofList (model := .quantum gates oracles)
        (applications.map (fun application => .gate application.coordinate)) := by
  rw [← ofList_eventTrace_eq_eventCost, nativeLayer_eventTrace]

private def serialNative : List (GateModel.Application gates ambient) →
    UnitaryCircuit gates oracles ambient
  | [] => identity gates oracles ambient
  | first :: rest => (UnitaryCircuit.native first).seq (serialNative rest)

private lemma nativeLayer_matrix_serial (applications : List (GateModel.Application gates ambient))
    (separate : applications.Pairwise (fun first second =>
      Disjoint first.embedding.selection second.embedding.selection))
    (environment : oracles.Interpretation) :
    (nativeLayer applications separate).matrix environment =
      (serialNative applications).matrix environment := by
  induction applications with
  | nil =>
      change (LayerPart.empty (gates := gates) (oracles := oracles)
        (ambient := ambient)).placement.liftOperator 1 = 1
      exact QuantumLayout.Embedding.embedding_liftOperator_one _
  | cons first rest ih =>
      change (LayerPart.join (LayerPart.native first) _ _).program.matrix environment = _
      rw [LayerPart.layerPart_join_matrix, seq_matrix, LayerPart.layerPart_native_matrix]
      change (nativeLayer rest _).matrix environment *
        (UnitaryCircuit.native first).matrix environment = _
      rw [ih]
      rfl

/-- Parallel scheduling retains the full ambient operator of the original ordered word. -/
public lemma nativeLayer_matrix (applications : List (GateModel.Application gates ambient))
    (separate : applications.Pairwise (fun first second =>
      Disjoint first.embedding.selection second.embedding.selection))
    (environment : oracles.Interpretation) :
    (nativeLayer applications separate).matrix environment =
      ((applications.map (fun application =>
        (UnitaryCircuit.native application).matrix environment)).reverse).prod := by
  rw [nativeLayer_matrix_serial]
  induction applications with
  | nil => rfl
  | cons first rest ih =>
      simp only [serialNative, seq_matrix, List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [ih (List.pairwise_cons.mp separate).2]

/-- Native gates have unit quantum duration; disjoint nonempty layers take one step. -/
public lemma nativeLayer_quantumTime (applications : List (GateModel.Application gates ambient))
    (separate : applications.Pairwise (fun first second =>
      Disjoint first.embedding.selection second.embedding.selection)) :
    (nativeLayer (oracles := oracles) applications separate).evaluatedEventDepth
      Resource.Event.quantumDuration = if applications = [] then 0 else 1 := by
  induction applications with
  | nil => rfl
  | cons first rest ih =>
      change (LayerPart.join (LayerPart.native first) _ _).program.evaluatedEventDepth _ = _
      rw [LayerPart.layerPart_join_depth, LayerPart.layerPart_native_depth]
      change max 1 ((nativeLayer rest _).evaluatedEventDepth _) = _
      rw [ih]
      simp only [List.cons_ne_nil, if_false]
      split <;> rfl

/-- The same empty/nonempty depth law holds when every native event has duration one. -/
public lemma nativeLayer_unitDepth (applications : List (GateModel.Application gates ambient))
    (separate : applications.Pairwise (fun first second =>
      Disjoint first.embedding.selection second.embedding.selection)) :
    (nativeLayer (oracles := oracles) applications separate).evaluatedEventDepth
      (fun _ => 1) = if applications = [] then 0 else 1 := by
  induction applications with
  | nil => rfl
  | cons first rest ih =>
      change (LayerPart.join (LayerPart.native first) _ _).program.evaluatedEventDepth _ = _
      rw [LayerPart.layerPart_join_depth, LayerPart.layerPart_native_depth]
      change max 1 ((nativeLayer rest _).evaluatedEventDepth _) = _
      rw [ih]
      simp only [List.cons_ne_nil, if_false]
      split <;> rfl

end

end QuantumAlg.UnitaryCircuit

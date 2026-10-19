/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Encoding
public import QuantumAlg.Core.Base.Layout.Quantum.Relabeling
public import Mathlib.GroupTheory.Perm.ViaEmbedding
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Oracle
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# A real qubit oracle for the finite cyclic group action

Both exponent registers and the group register consist of physical qubits.
The granted oracle acts by the source permutation on every valid encoded group
element and fixes every unused binary label. The action therefore has a total
unitary extension, rather than a promise on zero input alone
[Sho95, source.tex:1756-1784].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary.Oracle

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The binary group block follows the two exponent blocks. -/
public def workspaceShift (P : KnownOrderProblem G) : Nat ↪ Nat where
  toFun position := OrderPreparation.width P + OrderPreparation.width P + position
  inj' := fun _ _ same => Nat.add_left_cancel same

/-- Exactly `ceil(log₂ N)` actual qubits carry the group value. -/
public abbrev workspaceLayout (P : KnownOrderProblem G) : QuantumLayout (groupWidth P) :=
  (QuantumSignature.qubits (groupWidth P)).canonicalPlacement.layout.relabel
    (workspaceShift P)

/-- All binary group wires follow both exponent registers and share none of their identities. -/
public lemma binaryOracle_exponent_workspace_disjoint (P : KnownOrderProblem G) :
    List.Disjoint (OrderOracle.exponentLayout P).identities
      (workspaceLayout P).identities := by
  apply List.disjoint_left.mpr
  intro identity inExponent inWorkspace
  obtain ⟨exponent, exponentSame⟩ := List.mem_ofFn.mp inExponent
  obtain ⟨workspace, workspaceSame⟩ := List.mem_ofFn.mp inWorkspace
  change exponent.val = identity at exponentSame
  change OrderPreparation.width P + OrderPreparation.width P + workspace.val = identity
    at workspaceSame
  omega

/-- One full physical bank, with no native-dimensional group system. -/
@[expose, implicit_reducible]
public def layout (P : KnownOrderProblem G) :
    QuantumLayout (OrderPreparation.width P + OrderPreparation.width P + groupWidth P) :=
  QuantumLayout.append (OrderOracle.exponentLayout P) (workspaceLayout P)
    (binaryOracle_exponent_workspace_disjoint P)

/-- Every system counted in the full bank is physically a qubit. -/
public lemma layout_qubits (P : KnownOrderProblem G)
    (wire : Fin (OrderPreparation.width P + OrderPreparation.width P + groupWidth P)) :
    ((layout P).wire wire).dimension = 2 := by
  refine Fin.addCases (fun index => ?_) (fun index => ?_) wire
  · simp only [layout, QuantumLayout.append, Fin.append_left]
    rfl
  · simp only [layout, QuantumLayout.append, Fin.append_right]
    rfl

/-- Physical placement does not change the binary value of the group register. -/
public def workspaceBasisEquiv (P : KnownOrderProblem G) :
    (workspaceLayout P).Basis ≃ Fin (2 ^ groupWidth P) :=
  QuantumSignature.qubitsIndexEquiv (groupWidth P)

/-- The full physical basis consists of two exponent values and one binary group label. -/
@[expose] public def basisEquiv (P : KnownOrderProblem G) :
    (layout P).Basis ≃
      ((Fin (2 ^ OrderPreparation.width P) × Fin (2 ^ OrderPreparation.width P)) ×
        Fin (2 ^ groupWidth P)) :=
  (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P) (workspaceLayout P)
    (binaryOracle_exponent_workspace_disjoint P)).trans
    (Equiv.prodCongr (OrderOracle.exponentBasisEquiv P) (workspaceBasisEquiv P))

/-- Place a complete logical group state at its actual exponent and binary group labels. -/
public def logicalEmbedding (P : KnownOrderProblem G) :
    OrderOracle.LogicalBasis (subgroupProblem P) ↪ (layout P).Basis where
  toFun state := (basisEquiv P).symm (state.1, encodeGroup P state.2)
  inj' := by
    intro left right same
    have coordinates := (basisEquiv P).symm.injective same
    exact Prod.ext
      (congrArg (fun state :
        (Fin (2 ^ OrderPreparation.width P) × Fin (2 ^ OrderPreparation.width P)) ×
          Fin (2 ^ groupWidth P) => state.1) coordinates)
      (encodeGroup_injective P
        (congrArg (fun state :
          (Fin (2 ^ OrderPreparation.width P) × Fin (2 ^ OrderPreparation.width P)) ×
            Fin (2 ^ groupWidth P) => state.2) coordinates))

/-- This injection relates the old subgroup physical basis to the real binary bank. -/
public def sourceEmbedding (P : KnownOrderProblem G) :
    (OrderOracle.layout (subgroupProblem P)).Basis ↪ (layout P).Basis where
  toFun state := logicalEmbedding P (OrderOracle.basisEquiv (subgroupProblem P) state)
  inj' := (logicalEmbedding P).injective.comp
    (OrderOracle.basisEquiv (subgroupProblem P)).injective

/-- The all-zero binary workspace denotes the encoded group identity. -/
public lemma binaryOracle_workspaceBasisEquiv_zero (P : KnownOrderProblem G) :
    workspaceBasisEquiv P (workspaceLayout P).zeroLabel = 0 := by
  change QuantumSignature.qubitsIndexEquiv (groupWidth P)
      (fun _ : Fin (groupWidth P) => (0 : Fin 2)) = 0
  exact BinaryBasis.bigEndianEquiv_zero _

/-- Logical zero exponents and the identity occupy the full physical zero label. -/
public lemma binaryOracle_basisEquiv_zero (P : KnownOrderProblem G) :
    basisEquiv P (layout P).zeroLabel = ((0, 0), 0) := by
  have splitZero :
      QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P) (workspaceLayout P)
          (binaryOracle_exponent_workspace_disjoint P) (layout P).zeroLabel =
        ((OrderOracle.exponentLayout P).zeroLabel, (workspaceLayout P).zeroLabel) := by
    apply Prod.ext <;> funext index <;> apply Fin.ext <;> rfl
  have exponentZero : OrderOracle.exponentBasisEquiv P
      (OrderOracle.exponentLayout P).zeroLabel = (0, 0) := by
    have original := OrderOracle.basisEquiv_zero (subgroupProblem P)
    have exponent := congrArg Prod.fst original
    exact exponent
  change (Equiv.prodCongr (OrderOracle.exponentBasisEquiv P) (workspaceBasisEquiv P))
      (QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P) (workspaceLayout P)
        (binaryOracle_exponent_workspace_disjoint P) (layout P).zeroLabel) = _
  rw [splitZero]
  exact Prod.ext exponentZero (binaryOracle_workspaceBasisEquiv_zero P)

/-- The actual zero preparation is the encoded old identity preparation, with no extra gates. -/
public lemma sourceEmbedding_zero (P : KnownOrderProblem G) :
    sourceEmbedding P (OrderOracle.layout (subgroupProblem P)).zeroLabel =
      (layout P).zeroLabel := by
  apply (basisEquiv P).injective
  change basisEquiv P ((basisEquiv P).symm
      ((OrderOracle.basisEquiv (subgroupProblem P)
        (OrderOracle.layout (subgroupProblem P)).zeroLabel).1,
       encodeGroup P (OrderOracle.basisEquiv (subgroupProblem P)
        (OrderOracle.layout (subgroupProblem P)).zeroLabel).2)) = _
  rw [Equiv.apply_symm_apply, OrderOracle.basisEquiv_zero, encodeGroup_one,
    binaryOracle_basisEquiv_zero]
  rfl

/-- Extend the full source action by identity on the unused binary labels. -/
@[expose] public def physicalAction (P : KnownOrderProblem G) :
    Equiv.Perm (layout P).Basis :=
  (OrderOracle.physicalAction (subgroupProblem P)).viaEmbedding (sourceEmbedding P)

/-- Every source basis value evolves to the encoded original source output. -/
public lemma physicalAction_source (P : KnownOrderProblem G)
    (state : (OrderOracle.layout (subgroupProblem P)).Basis) :
    physicalAction P (sourceEmbedding P state) =
      sourceEmbedding P (OrderOracle.physicalAction (subgroupProblem P) state) :=
  Equiv.Perm.viaEmbedding_apply _ _ state

/-- No behavior is left unspecified on unused physical basis labels. -/
public lemma physicalAction_unused (P : KnownOrderProblem G)
    (state : (layout P).Basis) (unused : state ∉ Set.range (sourceEmbedding P)) :
    physicalAction P state = state :=
  Equiv.Perm.viaEmbedding_apply_of_notMem _ _ state unused

/-- The granted binary oracle is the certified permutation on the actual qubit bank. -/
@[expose] public def operator (P : KnownOrderProblem G) :
    UnitaryOperator (layout P).register :=
  UnitaryOperator.ofPerm (physicalAction P).symm

/-- Exact source action on each valid binary basis state. -/
public lemma operator_apply_source (P : KnownOrderProblem G)
    (state : (OrderOracle.layout (subgroupProblem P)).Basis) :
    (operator P).apply (NormalizedVector.ket (sourceEmbedding P state)) =
      NormalizedVector.ket
        (sourceEmbedding P (OrderOracle.physicalAction (subgroupProblem P) state)) := by
  rw [operator, UnitaryOperator.ofPerm_apply_ket, Equiv.Perm.inv_def, Equiv.symm_symm,
    physicalAction_source]

/-- Exact identity action on every unused binary basis state. -/
public lemma operator_apply_unused (P : KnownOrderProblem G)
    (state : (layout P).Basis) (unused : state ∉ Set.range (sourceEmbedding P)) :
    (operator P).apply (NormalizedVector.ket state) = NormalizedVector.ket state := by
  rw [operator, UnitaryOperator.ofPerm_apply_ket, Equiv.Perm.inv_def, Equiv.symm_symm,
    physicalAction_unused P state unused]

/-- The binary implementation has exactly the original sole quantum query coordinate. -/
@[expose, implicit_reducible] public def model (P : KnownOrderProblem G) : OracleModel where
  Query := Unit
  Coordinate := OrderOracle.Coordinate
  coordinateDecidableEq := inferInstance
  signature _ := (layout P).signature
  coordinate _ := .ux

/-- The public source instance supplies the operator only to the query interpreter. -/
@[expose] public def interpretation (P : KnownOrderProblem G) :
    (model P).Interpretation where
  operator _ := operator P

/-- One literal query on the whole binary bank. -/
@[expose] public def circuit (gates : GateModel) (P : KnownOrderProblem G) :
    UnitaryCircuit gates (model P) (layout P) :=
  .query (OracleModel.Application.onPlacement
    (model P) () (layout P).signaturePlacement)

/-- The native query has exactly the declared binary permutation matrix. -/
@[simp] public lemma binaryOracle_circuit_matrix (gates : GateModel) (P : KnownOrderProblem G) :
    (circuit gates P).matrix (interpretation P) = operator P := by
  change (OracleModel.Application.onPlacement
    (model P) () (layout P).signaturePlacement).operator (interpretation P) = _
  rw [OracleModel.Application.queryApplication_onPlacement_operator]
  apply Subtype.ext
  rfl

/-- One granted query contributes one native oracle occurrence and no hidden gate. -/
public lemma binaryOracle_circuit_eventCost (gates : GateModel) (P : KnownOrderProblem G) :
    (circuit gates P).eventCost =
      ResourcePool.singleton (model := .quantum gates (model P)) (.oracle .ux) := by
  rfl

/-- The declared query has unit query duration. -/
public lemma binaryOracle_circuit_unit_depth (gates : GateModel) (P : KnownOrderProblem G) :
    (circuit gates P).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

end

end QuantumAlg.FiniteCyclicDLP.Binary.Oracle

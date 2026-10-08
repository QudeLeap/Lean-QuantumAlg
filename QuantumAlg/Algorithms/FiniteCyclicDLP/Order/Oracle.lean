/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
public import QuantumAlg.Core.Base.Gate.Unitary.Permutation
public import QuantumAlg.Core.Base.Layout.Quantum.Append
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Util.FinPow
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# The sole finite-cyclic DLP quantum oracle

The oracle owns one group-valued physical system in addition to the two
exponent registers.  Its dimension is the actual cardinality of the supplied
finite group.  No binary encoding of group elements and no qubit-memory bound
derived from the known order are introduced.

The only granted query has the source action
`(a, b, y) ↦ (a, b, y * g^a * x⁻ᵇ)`.  Its group system remains visible in the
native-dimensional space ledger, while the public logical-qubit projection
counts the two exponent registers separately.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderOracle

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The only quantum-oracle accounting coordinate in the finite-cyclic experiment. -/
public inductive Coordinate where
  | ux
  deriving DecidableEq

/-- Two consecutive reviewed-width exponent registers. -/
public abbrev exponentLayout (P : KnownOrderProblem G) :
    QuantumLayout (OrderPreparation.width P + OrderPreparation.width P) :=
  (QuantumSignature.qubits
    (OrderPreparation.width P + OrderPreparation.width P)).canonicalPlacement.layout

/-- The group workspace is one system with the actual finite-group dimension. -/
@[expose] public def workspaceDimension (G : Type u) [Group G] [Fintype G] : ℕ+ := by
  letI : Nonempty G := ⟨1⟩
  exact ⟨Fintype.card G, Fintype.card_pos⟩

/-- The group system follows both exponent registers in physical order. -/
public def workspaceLayout [Fintype G] (P : KnownOrderProblem G) : QuantumLayout 1 :=
  QuantumLayout.uniform 1 (workspaceDimension G)
    (fun _ => OrderPreparation.width P + OrderPreparation.width P)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- The group system has a fresh physical identity after all exponent qubits. -/
public theorem exponent_workspace_disjoint [Fintype G] (P : KnownOrderProblem G) :
    List.Disjoint (exponentLayout P).identities (workspaceLayout P).identities := by
  apply List.disjoint_left.mpr
  intro identity exponentMember workspaceMember
  obtain ⟨exponent, exponentSame⟩ := List.mem_ofFn.mp exponentMember
  obtain ⟨workspace, workspaceSame⟩ := List.mem_ofFn.mp workspaceMember
  change exponent.val = identity at exponentSame
  change OrderPreparation.width P + OrderPreparation.width P = identity at workspaceSame
  omega

/-- Complete physical layout of the declared query. -/
@[expose, implicit_reducible]
public def layout [Fintype G] (P : KnownOrderProblem G) :
    QuantumLayout (OrderPreparation.width P + OrderPreparation.width P + 1) :=
  QuantumLayout.append (exponentLayout P) (workspaceLayout P)
    (exponent_workspace_disjoint P)

/-- The canonical query bank uses its logical position as its physical identity. -/
public theorem layout_wire_identity [Fintype G] (P : KnownOrderProblem G)
    (index : Fin (OrderPreparation.width P + OrderPreparation.width P + 1)) :
    ((layout P).wire index).identity = index.val := by
  refine Fin.addCases (m := OrderPreparation.width P + OrderPreparation.width P)
    (fun exponent => ?_) (fun workspace => ?_) index
  · simp [layout, exponentLayout, QuantumLayout.append,
      QuantumSignature.canonicalPlacement, QuantumSignature.place,
      QuantumSignature.qubits]
  · fin_cases workspace
    simp [layout, workspaceLayout, QuantumLayout.append, QuantumLayout.uniform]

/-- Logical basis named by two exponent values and one abstract group element. -/
public abbrev LogicalBasis (P : KnownOrderProblem G) :=
  (Fin (2 ^ OrderPreparation.width P) × Fin (2 ^ OrderPreparation.width P)) × G

/-- The two qubit blocks decode without changing the group workspace. -/
@[expose] public def exponentBasisEquiv (P : KnownOrderProblem G) :
    (exponentLayout P).Basis ≃
      Fin (2 ^ OrderPreparation.width P) × Fin (2 ^ OrderPreparation.width P) :=
  (QuantumSignature.qubitsIndexEquiv
    (OrderPreparation.width P + OrderPreparation.width P)).trans
      (prodEquiv (m := OrderPreparation.width P) (n := OrderPreparation.width P)).symm

/-- A one-system group basis is named directly by group elements, not bit strings. -/
public def groupBasisEquiv [Fintype G] : Fin (workspaceDimension G) ≃ G :=
  (Equiv.swap 0 (Fintype.equivFin G 1)).trans (Fintype.equivFin G).symm

/-- Physical basis zero denotes the group identity, so fixed zero preparation starts at `y = 1`. -/
public theorem groupBasisEquiv_zero [Fintype G] : groupBasisEquiv (G := G) 0 = 1 := by
  change (Fintype.equivFin G).symm
    (Equiv.swap 0 (Fintype.equivFin G 1) 0) = 1
  rw [Equiv.swap_apply_left]
  exact (Fintype.equivFin G).symm_apply_apply 1

/-- A one-system group basis is named directly by group elements, with zero fixed at identity. -/
public def workspaceBasisEquiv [Fintype G] (P : KnownOrderProblem G) :
    (workspaceLayout P).Basis ≃ G :=
  (Equiv.funUnique (Fin 1) (Fin (workspaceDimension G))).trans
    groupBasisEquiv

/-- The physical zero of the group system denotes the group identity. -/
@[simp] public theorem workspaceBasisEquiv_zero [Fintype G]
    (P : KnownOrderProblem G) :
    workspaceBasisEquiv P (workspaceLayout P).zeroLabel = 1 := by
  change groupBasisEquiv
    ((Equiv.funUnique (Fin 1) (Fin (workspaceDimension G)))
      (workspaceLayout P).zeroLabel) = 1
  rw [show (Equiv.funUnique (Fin 1) (Fin (workspaceDimension G)))
      (workspaceLayout P).zeroLabel = 0 by apply Fin.ext; rfl]
  exact groupBasisEquiv_zero

/-- Exact equivalence between the physical basis and the source-level oracle basis. -/
@[expose] public def basisEquiv [Fintype G] (P : KnownOrderProblem G) :
    (layout P).Basis ≃ LogicalBasis P :=
  (QuantumLayout.appendBasisEquiv (exponentLayout P) (workspaceLayout P)
    (exponent_workspace_disjoint P)).trans
    (Equiv.prodCongr (exponentBasisEquiv P) (workspaceBasisEquiv P))

/-- Semantic coordinates of a physically joined exponent and group label. -/
@[simp] public theorem basisEquiv_appendJoin [Fintype G]
    (P : KnownOrderProblem G) (exponent : (exponentLayout P).Basis)
    (workspace : (workspaceLayout P).Basis) :
    basisEquiv P
        (QuantumLayout.appendJoinBasis (exponentLayout P) (workspaceLayout P)
          (exponent_workspace_disjoint P) exponent workspace) =
      (exponentBasisEquiv P exponent, workspaceBasisEquiv P workspace) := by
  unfold basisEquiv
  rw [Equiv.trans_apply, QuantumLayout.appendBasisEquiv_join]
  rfl

/-- The complete physical zero label is exactly `(a,b,y) = (0,0,1_G)`. -/
public theorem basisEquiv_zero [Fintype G] (P : KnownOrderProblem G) :
    basisEquiv P (layout P).zeroLabel = ((0, 0), 1) := by
  have splitZero :
      QuantumLayout.appendBasisEquiv (exponentLayout P) (workspaceLayout P)
          (exponent_workspace_disjoint P) (layout P).zeroLabel =
        ((exponentLayout P).zeroLabel, (workspaceLayout P).zeroLabel) := by
    apply Prod.ext <;> funext index <;> apply Fin.ext <;> rfl
  have exponentZero :
      exponentBasisEquiv P (exponentLayout P).zeroLabel = (0, 0) := by
    have encodedZero :
        QuantumSignature.qubitsIndexEquiv
            (OrderPreparation.width P + OrderPreparation.width P)
            (exponentLayout P).zeroLabel = 0 := by
      unfold QuantumSignature.qubitsIndexEquiv
      rw [show (exponentLayout P).zeroLabel =
          (fun _ : Fin (OrderPreparation.width P + OrderPreparation.width P) =>
            (0 : Fin 2)) by funext index; apply Fin.ext; rfl]
      exact BinaryBasis.bigEndianEquiv_zero _
    unfold exponentBasisEquiv
    rw [Equiv.trans_apply, encodedZero]
    apply Prod.ext
    · apply Fin.ext
      simpa using (prodEquiv_symm_fst_val (m := OrderPreparation.width P)
        (n := OrderPreparation.width P) 0)
    · apply Fin.ext
      simpa using (prodEquiv_symm_snd_val (m := OrderPreparation.width P)
        (n := OrderPreparation.width P) 0)
  have workspaceZero :
      workspaceBasisEquiv P (workspaceLayout P).zeroLabel = 1 := by
    change groupBasisEquiv
      ((Equiv.funUnique (Fin 1) (Fin (workspaceDimension G)))
        (workspaceLayout P).zeroLabel) = 1
    rw [show (Equiv.funUnique (Fin 1) (Fin (workspaceDimension G)))
        (workspaceLayout P).zeroLabel = 0 by apply Fin.ext; rfl]
    exact groupBasisEquiv_zero
  change (Equiv.prodCongr (exponentBasisEquiv P) (workspaceBasisEquiv P))
      (QuantumLayout.appendBasisEquiv (exponentLayout P) (workspaceLayout P)
        (exponent_workspace_disjoint P) (layout P).zeroLabel) = ((0, 0), 1)
  rw [splitZero]
  change (exponentBasisEquiv P (exponentLayout P).zeroLabel,
      workspaceBasisEquiv P (workspaceLayout P).zeroLabel) = ((0, 0), 1)
  rw [exponentZero, workspaceZero]

/-- Source-level action of `U_x` on one logical basis value. -/
@[expose]
public def logicalAction (P : KnownOrderProblem G) (state : LogicalBasis P) :
    LogicalBasis P :=
  (state.1, state.2 *
    P.toSourceScope.oracleMultiplier state.1.1.val state.1.2.val)

/-- The source action is a permutation because right multiplication is invertible. -/
@[expose]
public def actionEquiv (P : KnownOrderProblem G) : Equiv.Perm (LogicalBasis P) where
  toFun := logicalAction P
  invFun := fun state =>
    (state.1, state.2 *
      (P.toSourceScope.oracleMultiplier state.1.1.val state.1.2.val)⁻¹)
  left_inv := by
    intro state
    rcases state with ⟨⟨left, right⟩, workspace⟩
    simp [logicalAction, mul_assoc]
  right_inv := by
    intro state
    rcases state with ⟨⟨left, right⟩, workspace⟩
    simp [logicalAction, mul_assoc]

/-- The source action transported to the actual native-dimensional physical basis. -/
@[expose]
public def physicalAction [Fintype G] (P : KnownOrderProblem G) :
    Equiv.Perm (layout P).Basis :=
  (basisEquiv P).trans ((actionEquiv P).trans (basisEquiv P).symm)

/-- Fixed physical permutation operator implementing the advertised source action. -/
@[expose]
public def operator [Fintype G]
    (P : KnownOrderProblem G) : UnitaryOperator (layout P).register :=
  UnitaryOperator.ofPerm (physicalAction P).symm

/-- The transported operator has exactly the advertised group-action basis semantics. -/
public theorem operator_apply_basis [Fintype G]
    (P : KnownOrderProblem G) (state : LogicalBasis P) :
    (operator P).apply (NormalizedVector.ket ((basisEquiv P).symm state)) =
      NormalizedVector.ket ((basisEquiv P).symm (logicalAction P state)) := by
  rw [operator, UnitaryOperator.ofPerm_apply_ket]
  apply congrArg NormalizedVector.ket
  simp [physicalAction, actionEquiv]

/-- Problem-selected oracle model granting exactly `U_x`. -/
@[expose, implicit_reducible]
public def model [Fintype G] (P : KnownOrderProblem G) : OracleModel where
  Query := Unit
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature _ := (layout P).signature
  operator _ := operator P
  coordinate _ := .ux

/-- One actual occurrence of the sole declared query on its complete placement. -/
@[expose]
public def circuit [Fintype G]
    (gates : GateModel) (P : KnownOrderProblem G) :
    UnitaryCircuit gates (model P) (layout P) :=
  .query (OracleModel.Application.onPlacement
    (model P) () (layout P).signaturePlacement)

/-- The sole query circuit carries exactly the declared permutation operator. -/
@[simp] public theorem circuit_matrix [Fintype G]
    (gates : GateModel) (P : KnownOrderProblem G) :
    (circuit gates P).matrix = operator P := by
  change (OracleModel.Application.onPlacement
    (model P) () (layout P).signaturePlacement).operator = _
  rw [OracleModel.Application.queryApplication_onPlacement_operator]
  apply Subtype.ext
  rfl

/-- The query contributes exactly one oracle event and no native gate event. -/
public theorem circuit_eventCost [Fintype G]
    (gates : GateModel) (P : KnownOrderProblem G) :
    (circuit gates P).eventCost =
      ResourcePool.singleton (model := .quantum gates (model P)) (.oracle .ux) := by
  rfl

/-- One abstract query occupies one dependency step. -/
public theorem circuit_unit_depth [Fintype G]
    (gates : GateModel) (P : KnownOrderProblem G) :
    (circuit gates P).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

end

end QuantumAlg.FiniteCyclicDLP.OrderOracle

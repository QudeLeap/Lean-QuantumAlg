/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Base.Oracle.Placement.Construction

/-!
# One owned declared Shor bank and complete phase-result storage

The bank contains the original phase register and one modulus-width XOR target.
The actual retained sampler remains a separate charged prefix. Earlier classical
storage and arbitrary references survive. No native modular-arithmetic bank is
allocated alongside the declared query.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

/-- The declared query owns one phase register and one complete XOR target. -/
def bankQubits (N : Nat) : Nat := phaseBits N + modulusBits N

/-- The real owned wires agree exactly with the declared member's placement. -/
def layout (N : Nat) : QuantumLayout (bankQubits N) :=
  (QuantumSignature.qubits (bankQubits N)).canonicalPlacement.layout

/-- The standard phase width gives the declared bank three modulus widths. -/
lemma bankQubits_eq_three_mul (N : Nat) : bankQubits N = 3 * modulusBits N := by
  unfold bankQubits phaseBits
  omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

include noQuantum in
lemma allocationDisjoint : List.Disjoint (layout N).identities base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- The actual preparation extends the caller by precisely one owned bank. -/
def bankContext : RuntimeCtx .quantum :=
  base.addOwnedLayout base.canonicalFreshKey (layout N) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum N)

/-- The initializer contributes precisely the declared bank's complete wire list. -/
lemma bankContext_wires :
    (bankContext base noQuantum N).quantumWires = (layout N).wires := by
  change (layout N).wires ++ base.quantumWires = _
  rw [noQuantum, List.append_nil]

variable {ctx : RuntimeCtx .quantum} (N : Nat) (sameWires : ctx.quantumWires = (layout N).wires)

include sameWires in
private lemma layoutWires : (layout N).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- Corresponding positions preserve complete wire identities and dimensions. -/
def wireEquiv : Fin (bankQubits N) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (layout N) ctx.quantumLayout (layoutWires N sameWires)

/-- The actual wire at each source position retains its physical identity and dimension. -/
lemma shorDeclared_wire_preserved (wire : Fin (bankQubits N)) :
    ctx.quantumLayout.wire (wireEquiv N sameWires wire) = (layout N).wire wire :=
  Execution.wireAtCorrespondingPosition (layout N) ctx.quantumLayout (layoutWires N sameWires) wire

include sameWires in
/-- Every actual bank wire has dimension two. -/
lemma shorDeclared_context_qubits (wire : Fin ctx.systemCount) :
    (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨original, rfl⟩ := (wireEquiv N sameWires).surjective wire
  exact congrArg QuantumWire.dimension (shorDeclared_wire_preserved N sameWires original)

/-- Binary source labels identify the same actual ordered physical wires. -/
def basisEquiv : ctx.register.Index ≃ (Qubits (bankQubits N)).Index :=
  (Execution.basisOfEqualWires (layout N) ctx.quantumLayout (layoutWires N sameWires)).symm.trans
    (QuantumSignature.qubitsIndexEquiv (bankQubits N))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

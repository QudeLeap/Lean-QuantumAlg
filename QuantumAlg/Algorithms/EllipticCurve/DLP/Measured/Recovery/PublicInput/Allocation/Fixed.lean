/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Allocation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.Space
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Exact peak of actual public allocation followed by a fixed local execution

Five real owned preparations and the real measurement-cell allocations precede
an allocation-free local child, embedded beside both borrowed point inputs.
The actual parent peak is its complete public terminal context. Every child
path is covered, without a support or validity premise. This lemma applies to
the reset and sampler after their actual fixed code is supplied; it neither
proves their semantics nor claims a bound for later recovery or retry scopes.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
namespace AllocatedFixed

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)

/-- Physical identity embedding retains both actual borrowed point inputs. -/
def placement : ContextEmbedding (Recovery.Layout.terminal p.size m)
  (Recovery.PublicInput.context E m) :=
  ContextEmbedding.alongUnion (Recovery.Layout.terminal p.size m) (Recovery.PublicInput.frame E m)
    (Recovery.PublicInput.terminal_disjoint E m)

/-- The allocating parent executes its real allocation before the actual fixed child. -/
def code (body : Circuit Model (Recovery.Layout.terminal p.size m)
    (Recovery.Layout.terminal p.size m) false) :
    Circuit Model (Recovery.PublicInput.frame E m) (Recovery.PublicInput.context E m) :=
  (Allocation.circuit E m).seq
    (Circuit.embed (allowAllocation := true) (placement E m) body)

/-- The same actual parent path charges the complete resident caller at its peak. -/
lemma code_resident (body : Circuit Model (Recovery.Layout.terminal p.size m)
    (Recovery.Layout.terminal p.size m) false) (path : (code E m body).Path) :
    (code E m body).peakResidentSpace path = (Recovery.PublicInput.context E m).residentSpace := by
  change ((Allocation.circuit E m).seq
    (Circuit.embed (allowAllocation := true) (placement E m) body)).Path at path
  change ((Allocation.circuit E m).seq
    (Circuit.embed (allowAllocation := true) (placement E m) body)).peakResidentSpace path = _
  rw [Circuit.peakResidentSpace_seq, Allocation.circuit_peakResidentSpace]
  change SpacePool.max (Recovery.PublicInput.context E m).residentSpace
    (SpacePool.max (Recovery.PublicInput.context E m).residentSpace 0) = _
  rw [SpacePool.max_zero, SpacePool.max_self]

/-- The complete actual auxiliary roles are charged on the same parent path. -/
lemma code_auxiliary (body : Circuit Model (Recovery.Layout.terminal p.size m)
    (Recovery.Layout.terminal p.size m) false) (path : (code E m body).Path) :
    (code E m body).peakAuxiliarySpace path = (Recovery.PublicInput.context E
      m).auxiliarySpace := by
  change ((Allocation.circuit E m).seq
    (Circuit.embed (allowAllocation := true) (placement E m) body)).Path at path
  change ((Allocation.circuit E m).seq
    (Circuit.embed (allowAllocation := true) (placement E m) body)).peakAuxiliarySpace path = _
  rw [Circuit.peakAuxiliarySpace_seq, Allocation.circuit_peakAuxiliarySpace]
  change SpacePool.max (Recovery.PublicInput.context E m).auxiliarySpace
    (SpacePool.max (Recovery.PublicInput.context E m).auxiliarySpace 0) = _
  rw [SpacePool.max_zero, SpacePool.max_self]

/-- Borrowed public point encodings add classical storage and no quantum systems. -/
lemma public_quantum_count (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (Recovery.PublicInput.context E m).residentSpace =
      if 2 = dimension then 3 * p.size + 4 * p.size.size + 14 else 0 := by
  rw [Recovery.PublicInput.context_resident]
  simp only [SpacePool.count_add]
  have borrowed : SpacePool.count (.quantumSystems dimension)
      (2 • SpacePool.ofShape (ECDLP.Canonical.Runtime.Context.PointShape E)) = 0 := by
    simp [SpacePool.count, SpacePool.ofShape]
  rw [borrowed, add_zero]
  exact (Recovery.Layout.streamingTerminal_quantumSystems p.size m dimension).1

/-- Actual allocation and every fixed child path have this exact quantum peak. -/
lemma code_quantum_count (body : Circuit Model (Recovery.Layout.terminal p.size m)
    (Recovery.Layout.terminal p.size m) false) (path : (code E m body).Path) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) ((code E m body).peakResidentSpace path) =
      if 2 = dimension then 3 * p.size + 4 * p.size.size + 14 else 0 := by
  rw [code_resident]
  exact public_quantum_count E m dimension

/-- At field width 256, the actual allocation-plus-fixed-execution parent peaks at 818 qubits. -/
lemma code_width256_qubits (width : p.size = 256)
    (body : Circuit Model (Recovery.Layout.terminal p.size m) (Recovery.Layout.terminal p.size
      m) false)
    (path : (code E m body).Path) :
    SpacePool.count (.quantumSystems 2) ((code E m body).peakResidentSpace path) = 818 := by
  rw [code_quantum_count, if_pos rfl, width]
  decide

end

end AllocatedFixed
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word37Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word37State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word37Step0 :
    word37Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word37State1 := by decide +kernel

private def word37Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word37State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word37Step1 :
    word37Chunk1.foldl (fun acc a => a.applyPacked acc)
      word37State1 = word37State2 := by decide +kernel

private def word37Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word37State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word37Step2 :
    word37Chunk2.foldl (fun acc a => a.applyPacked acc)
      word37State2 = word37State3 := by decide +kernel

private def word37Chunk3 : List Letter := [.s, .s, .s, .h, .s, .s, .h, .t]
private def word37State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word37Step3 :
    word37Chunk3.foldl (fun acc a => a.applyPacked acc)
      word37State3 = word37State4 := by decide +kernel

private def word37Chunk4 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word37State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word37Step4 :
    word37Chunk4.foldl (fun acc a => a.applyPacked acc)
      word37State4 = word37State5 := by decide +kernel

private def word37Chunk5 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word37State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word37Step5 :
    word37Chunk5.foldl (fun acc a => a.applyPacked acc)
      word37State5 = word37State6 := by decide +kernel

private def word37Chunk6 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word37State7 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word37Step6 :
    word37Chunk6.foldl (fun acc a => a.applyPacked acc)
      word37State6 = word37State7 := by decide +kernel

private def word37Chunk7 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word37State8 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word37Step7 :
    word37Chunk7.foldl (fun acc a => a.applyPacked acc)
      word37State7 = word37State8 := by decide +kernel

private def word37Chunk8 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word37State9 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((7 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word37Step8 :
    word37Chunk8.foldl (fun acc a => a.applyPacked acc)
      word37State8 = word37State9 := by decide +kernel

private def word37Chunk9 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word37State10 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((17 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word37Step9 :
    word37Chunk9.foldl (fun acc a => a.applyPacked acc)
      word37State9 = word37State10 := by decide +kernel

private def word37Chunk10 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word37State11 : PackedMat2 :=
    ⟨⟨⟨((-41 : Dyadic) * half ^ 6),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((45 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 7)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 7)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 5),
        ((45 : Dyadic) * half ^ 7)⟩,
       ⟨((-41 : Dyadic) * half ^ 6),
        ((15 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word37Step10 :
    word37Chunk10.foldl (fun acc a => a.applyPacked acc)
      word37State10 = word37State11 := by decide +kernel

private def word37Chunk11 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word37State12 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 6)⟩,
       ⟨((-23 : Dyadic) * half ^ 6),
        ((51 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 7)⟩,
       ⟨((63 : Dyadic) * half ^ 7),
        ((31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 7)⟩,
       ⟨((-63 : Dyadic) * half ^ 7),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 6),
        ((17 : Dyadic) * half ^ 6)⟩,
       ⟨((-23 : Dyadic) * half ^ 6),
        ((51 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word37Step11 :
    word37Chunk11.foldl (fun acc a => a.applyPacked acc)
      word37State11 = word37State12 := by decide +kernel

private def word37Chunk12 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word37State13 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 8),
        ((-25 : Dyadic) * half ^ 7)⟩,
       ⟨((33 : Dyadic) * half ^ 8),
        ((-111 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-43 : Dyadic) * half ^ 8),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((43 : Dyadic) * half ^ 8),
        ((121 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((91 : Dyadic) * half ^ 8),
        ((43 : Dyadic) * half ^ 8)⟩,
       ⟨((151 : Dyadic) * half ^ 8),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((61 : Dyadic) * half ^ 8),
        ((-7 : Dyadic) * half ^ 7)⟩,
       ⟨((161 : Dyadic) * half ^ 8),
        ((-19 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word37Step12 :
    word37Chunk12.foldl (fun acc a => a.applyPacked acc)
      word37State12 = word37State13 := by decide +kernel

private def word37Chunk13 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word37State14 : PackedMat2 :=
    ⟨⟨⟨((33 : Dyadic) * half ^ 8),
        ((67 : Dyadic) * half ^ 7)⟩,
       ⟨((-29 : Dyadic) * half ^ 6),
        ((55 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 7),
        ((-83 : Dyadic) * half ^ 9)⟩,
       ⟨((15 : Dyadic) * half ^ 7),
        ((-41 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 8),
        ((-23 : Dyadic) * half ^ 7)⟩,
       ⟨((31 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-79 : Dyadic) * half ^ 8),
        ((-149 : Dyadic) * half ^ 9)⟩,
       ⟨((189 : Dyadic) * half ^ 8),
        ((-83 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word37Step13 :
    word37Chunk13.foldl (fun acc a => a.applyPacked acc)
      word37State13 = word37State14 := by decide +kernel

private def word37Chunk14 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word37State15 : PackedMat2 :=
    ⟨⟨⟨((141 : Dyadic) * half ^ 9),
        ((-321 : Dyadic) * half ^ 10)⟩,
       ⟨((25 : Dyadic) * half ^ 5),
        ((107 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 7),
        ((-117 : Dyadic) * half ^ 10)⟩,
       ⟨((35 : Dyadic) * half ^ 9),
        ((-157 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((35 : Dyadic) * half ^ 9),
        ((-157 : Dyadic) * half ^ 10)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        ((-117 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 5),
        ((-107 : Dyadic) * half ^ 10)⟩,
       ⟨((-141 : Dyadic) * half ^ 9),
        ((321 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word37Step14 :
    word37Chunk14.foldl (fun acc a => a.applyPacked acc)
      word37State14 = word37State15 := by decide +kernel

private def word37Chunk15 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word37State16 : PackedMat2 :=
    ⟨⟨⟨((-701 : Dyadic) * half ^ 10),
        ((9 : Dyadic) * half ^ 8)⟩,
       ⟨((385 : Dyadic) * half ^ 10),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 9),
        ((35 : Dyadic) * half ^ 8)⟩,
       ⟨((-83 : Dyadic) * half ^ 8),
        ((247 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 9),
        ((-35 : Dyadic) * half ^ 8)⟩,
       ⟨((-83 : Dyadic) * half ^ 8),
        ((247 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-701 : Dyadic) * half ^ 10),
        ((9 : Dyadic) * half ^ 8)⟩,
       ⟨((-385 : Dyadic) * half ^ 10),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word37Step15 :
    word37Chunk15.foldl (fun acc a => a.applyPacked acc)
      word37State15 = word37State16 := by decide +kernel

private def word37Chunk16 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word37State17 : PackedMat2 :=
    ⟨⟨⟨((-569 : Dyadic) * half ^ 10),
        ((111 : Dyadic) * half ^ 11)⟩,
       ⟨((399 : Dyadic) * half ^ 10),
        ((-205 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-597 : Dyadic) * half ^ 11),
        ((-259 : Dyadic) * half ^ 11)⟩,
       ⟨((-375 : Dyadic) * half ^ 11),
        ((-797 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 6),
        ((-243 : Dyadic) * half ^ 10)⟩,
       ⟨((269 : Dyadic) * half ^ 10),
        ((-111 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((299 : Dyadic) * half ^ 11),
        ((85 : Dyadic) * half ^ 10)⟩,
       ⟨((-521 : Dyadic) * half ^ 11),
        ((121 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word37Step16 :
    word37Chunk16.foldl (fun acc a => a.applyPacked acc)
      word37State16 = word37State17 := by decide +kernel

private def word37Chunk17 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word37State18 : PackedMat2 :=
    ⟨⟨⟨((-951 : Dyadic) * half ^ 12),
        ((-1525 : Dyadic) * half ^ 12)⟩,
       ⟨((-2555 : Dyadic) * half ^ 12),
        ((325 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-941 : Dyadic) * half ^ 12),
        ((305 : Dyadic) * half ^ 11)⟩,
       ⟨((-1053 : Dyadic) * half ^ 12),
        ((-745 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((941 : Dyadic) * half ^ 12),
        ((-305 : Dyadic) * half ^ 11)⟩,
       ⟨((-1053 : Dyadic) * half ^ 12),
        ((-745 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-951 : Dyadic) * half ^ 12),
        ((-1525 : Dyadic) * half ^ 12)⟩,
       ⟨((2555 : Dyadic) * half ^ 12),
        ((-325 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word37Step17 :
    word37Chunk17.foldl (fun acc a => a.applyPacked acc)
      word37State17 = word37State18 := by decide +kernel

private def word37Chunk18 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word37State19 : PackedMat2 :=
    ⟨⟨⟨((-4191 : Dyadic) * half ^ 13),
        ((545 : Dyadic) * half ^ 11)⟩,
       ⟨((-4003 : Dyadic) * half ^ 13),
        ((-2345 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2175 : Dyadic) * half ^ 13),
        ((-199 : Dyadic) * half ^ 12)⟩,
       ⟨((571 : Dyadic) * half ^ 13),
        ((-1955 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2175 : Dyadic) * half ^ 13),
        ((-199 : Dyadic) * half ^ 12)⟩,
       ⟨((-571 : Dyadic) * half ^ 13),
        ((1955 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((4191 : Dyadic) * half ^ 13),
        ((-545 : Dyadic) * half ^ 11)⟩,
       ⟨((-4003 : Dyadic) * half ^ 13),
        ((-2345 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word37Step18 :
    word37Chunk18.foldl (fun acc a => a.applyPacked acc)
      word37State18 = word37State19 := by decide +kernel

private def word37Chunk19 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word37State20 : PackedMat2 :=
    ⟨⟨⟨((-1253 : Dyadic) * half ^ 12),
        ((5695 : Dyadic) * half ^ 14)⟩,
       ⟨((-2003 : Dyadic) * half ^ 13),
        ((-3639 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((4353 : Dyadic) * half ^ 13),
        ((2655 : Dyadic) * half ^ 14)⟩,
       ⟨((1621 : Dyadic) * half ^ 12),
        ((-1411 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((311 : Dyadic) * half ^ 12),
        ((7595 : Dyadic) * half ^ 14)⟩,
       ⟨((2033 : Dyadic) * half ^ 13),
        ((1111 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-257 : Dyadic) * half ^ 11),
        ((4509 : Dyadic) * half ^ 14)⟩,
       ⟨((-4667 : Dyadic) * half ^ 13),
        ((503 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word37Step19 :
    word37Chunk19.foldl (fun acc a => a.applyPacked acc)
      word37State19 = word37State20 := by decide +kernel

private def word37Chunk20 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word37State21 : PackedMat2 :=
    ⟨⟨⟨((1983 : Dyadic) * half ^ 12),
        ((6595 : Dyadic) * half ^ 15)⟩,
       ⟨((8713 : Dyadic) * half ^ 14),
        ((-5727 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((5913 : Dyadic) * half ^ 14),
        ((2497 : Dyadic) * half ^ 15)⟩,
       ⟨((855 : Dyadic) * half ^ 13),
        ((-10045 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-855 : Dyadic) * half ^ 13),
        ((10045 : Dyadic) * half ^ 15)⟩,
       ⟨((-5913 : Dyadic) * half ^ 14),
        ((-2497 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((8713 : Dyadic) * half ^ 14),
        ((-5727 : Dyadic) * half ^ 15)⟩,
       ⟨((1983 : Dyadic) * half ^ 12),
        ((6595 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word37Step20 :
    word37Chunk20.foldl (fun acc a => a.applyPacked acc)
      word37State20 = word37State21 := by decide +kernel

private def word37Chunk21 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word37State22 : PackedMat2 :=
    ⟨⟨⟨((-8389 : Dyadic) * half ^ 15),
        ((4347 : Dyadic) * half ^ 14)⟩,
       ⟨((-1569 : Dyadic) * half ^ 15),
        ((7911 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1737 : Dyadic) * half ^ 13),
        ((10545 : Dyadic) * half ^ 15)⟩,
       ⟨((-2283 : Dyadic) * half ^ 14),
        ((-1341 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1737 : Dyadic) * half ^ 13),
        ((10545 : Dyadic) * half ^ 15)⟩,
       ⟨((2283 : Dyadic) * half ^ 14),
        ((1341 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((8389 : Dyadic) * half ^ 15),
        ((-4347 : Dyadic) * half ^ 14)⟩,
       ⟨((-1569 : Dyadic) * half ^ 15),
        ((7911 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word37Step21 :
    word37Chunk21.foldl (fun acc a => a.applyPacked acc)
      word37State21 = word37State22 := by decide +kernel

private def word37Chunk22 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word37State23 : PackedMat2 :=
    ⟨⟨⟨((12009 : Dyadic) * half ^ 16),
        ((-8689 : Dyadic) * half ^ 14)⟩,
       ⟨((18689 : Dyadic) * half ^ 16),
        ((1761 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((17267 : Dyadic) * half ^ 16),
        ((10503 : Dyadic) * half ^ 15)⟩,
       ⟨((-2211 : Dyadic) * half ^ 16),
        ((-9843 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-30849 : Dyadic) * half ^ 16),
        ((-9739 : Dyadic) * half ^ 16)⟩,
       ⟨((11163 : Dyadic) * half ^ 16),
        ((941 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-36517 : Dyadic) * half ^ 16),
        ((-835 : Dyadic) * half ^ 14)⟩,
       ⟨((32995 : Dyadic) * half ^ 16),
        ((-15349 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word37Step22 :
    word37Chunk22.foldl (fun acc a => a.applyPacked acc)
      word37State22 = word37State23 := by decide +kernel

private def word37Chunk23 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word37State24 : PackedMat2 :=
    ⟨⟨⟨((-23261 : Dyadic) * half ^ 17),
        ((-31689 : Dyadic) * half ^ 16)⟩,
       ⟨((-5093 : Dyadic) * half ^ 17),
        ((28635 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((24279 : Dyadic) * half ^ 17),
        ((-6959 : Dyadic) * half ^ 14)⟩,
       ⟨((11985 : Dyadic) * half ^ 17),
        ((1941 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((24279 : Dyadic) * half ^ 17),
        ((-6959 : Dyadic) * half ^ 14)⟩,
       ⟨((-11985 : Dyadic) * half ^ 17),
        ((-1941 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((23261 : Dyadic) * half ^ 17),
        ((31689 : Dyadic) * half ^ 16)⟩,
       ⟨((-5093 : Dyadic) * half ^ 17),
        ((28635 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word37Step23 :
    word37Chunk23.foldl (fun acc a => a.applyPacked acc)
      word37State23 = word37State24 := by decide +kernel

private def word37Chunk24 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word37State25 : PackedMat2 :=
    ⟨⟨⟨((-87697 : Dyadic) * half ^ 17),
        ((-8441 : Dyadic) * half ^ 16)⟩,
       ⟨((-5901 : Dyadic) * half ^ 16),
        ((-15581 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-44293 : Dyadic) * half ^ 17),
        ((36515 : Dyadic) * half ^ 18)⟩,
       ⟨((60087 : Dyadic) * half ^ 17),
        ((-34603 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((60087 : Dyadic) * half ^ 17),
        ((-34603 : Dyadic) * half ^ 18)⟩,
       ⟨((-44293 : Dyadic) * half ^ 17),
        ((36515 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((5901 : Dyadic) * half ^ 16),
        ((15581 : Dyadic) * half ^ 16)⟩,
       ⟨((87697 : Dyadic) * half ^ 17),
        ((8441 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word37Step24 :
    word37Chunk24.foldl (fun acc a => a.applyPacked acc)
      word37State24 = word37State25 := by decide +kernel

private def word37Chunk25 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word37State26 : PackedMat2 :=
    ⟨⟨⟨((9429 : Dyadic) * half ^ 15),
        ((-62111 : Dyadic) * half ^ 19)⟩,
       ⟨((-4079 : Dyadic) * half ^ 15),
        ((-4419 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-17829 : Dyadic) * half ^ 18),
        ((-4389 : Dyadic) * half ^ 15)⟩,
       ⟨((14941 : Dyadic) * half ^ 14),
        ((6879 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-41991 : Dyadic) * half ^ 18),
        ((-256885 : Dyadic) * half ^ 19)⟩,
       ⟨((28233 : Dyadic) * half ^ 18),
        ((-221227 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((14423 : Dyadic) * half ^ 17),
        ((-3377 : Dyadic) * half ^ 14)⟩,
       ⟨((-33265 : Dyadic) * half ^ 18),
        ((2675 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word37Step25 :
    word37Chunk25.foldl (fun acc a => a.applyPacked acc)
      word37State25 = word37State26 := by decide +kernel

private def word37Chunk26 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word37State27 : PackedMat2 :=
    ⟨⟨⟨((209577 : Dyadic) * half ^ 19),
        ((169041 : Dyadic) * half ^ 20)⟩,
       ⟨((831 : Dyadic) * half ^ 13),
        ((-197599 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-34581 : Dyadic) * half ^ 16),
        ((-44997 : Dyadic) * half ^ 20)⟩,
       ⟨((-79503 : Dyadic) * half ^ 19),
        ((469999 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-79503 : Dyadic) * half ^ 19),
        ((469999 : Dyadic) * half ^ 20)⟩,
       ⟨((-34581 : Dyadic) * half ^ 16),
        ((-44997 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-831 : Dyadic) * half ^ 13),
        ((197599 : Dyadic) * half ^ 20)⟩,
       ⟨((-209577 : Dyadic) * half ^ 19),
        ((-169041 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word37Step26 :
    word37Chunk26.foldl (fun acc a => a.applyPacked acc)
      word37State26 = word37State27 := by decide +kernel

private def word37Chunk27 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word37State28 : PackedMat2 :=
    ⟨⟨⟨((-24161 : Dyadic) * half ^ 18),
        ((121613 : Dyadic) * half ^ 18)⟩,
       ⟨((67369 : Dyadic) * half ^ 18),
        ((236277 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((20227 : Dyadic) * half ^ 20),
        ((-380267 : Dyadic) * half ^ 20)⟩,
       ⟨((376671 : Dyadic) * half ^ 20),
        ((-23805 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((50509 : Dyadic) * half ^ 17),
        ((-198449 : Dyadic) * half ^ 20)⟩,
       ⟨((178231 : Dyadic) * half ^ 19),
        ((89111 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((722729 : Dyadic) * half ^ 20),
        ((5401 : Dyadic) * half ^ 16)⟩,
       ⟨((250175 : Dyadic) * half ^ 20),
        ((-45765 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word37Step27 :
    word37Chunk27.foldl (fun acc a => a.applyPacked acc)
      word37State27 = word37State28 := by decide +kernel

private def word37Chunk28 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word37State29 : PackedMat2 :=
    ⟨⟨⟨((1080099 : Dyadic) * half ^ 21),
        ((-178363 : Dyadic) * half ^ 20)⟩,
       ⟨((396137 : Dyadic) * half ^ 21),
        ((375661 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1406681 : Dyadic) * half ^ 21),
        ((-192245 : Dyadic) * half ^ 21)⟩,
       ⟨((69261 : Dyadic) * half ^ 21),
        ((-7657 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((297803 : Dyadic) * half ^ 21),
        ((-737971 : Dyadic) * half ^ 21)⟩,
       ⟨((682293 : Dyadic) * half ^ 21),
        ((334355 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((732387 : Dyadic) * half ^ 21),
        ((-341981 : Dyadic) * half ^ 21)⟩,
       ⟨((18935 : Dyadic) * half ^ 21),
        ((369059 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word37Step28 :
    word37Chunk28.foldl (fun acc a => a.applyPacked acc)
      word37State28 = word37State29 := by decide +kernel

private def word37Chunk29 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word37State30 : PackedMat2 :=
    ⟨⟨⟨((-43981 : Dyadic) * half ^ 17),
        ((1442409 : Dyadic) * half ^ 22)⟩,
       ⟨((143641 : Dyadic) * half ^ 19),
        ((-629299 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-593069 : Dyadic) * half ^ 21),
        ((-143663 : Dyadic) * half ^ 20)⟩,
       ⟨((-150357 : Dyadic) * half ^ 18),
        ((-430551 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-150357 : Dyadic) * half ^ 18),
        ((-430551 : Dyadic) * half ^ 21)⟩,
       ⟨((-593069 : Dyadic) * half ^ 21),
        ((-143663 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-143641 : Dyadic) * half ^ 19),
        ((629299 : Dyadic) * half ^ 22)⟩,
       ⟨((43981 : Dyadic) * half ^ 17),
        ((-1442409 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word37Step29 :
    word37Chunk29.foldl (fun acc a => a.applyPacked acc)
      word37State29 = word37State30 := by decide +kernel

private def word37Chunk30 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word37State31 : PackedMat2 :=
    ⟨⟨⟨((-2661 : Dyadic) * half ^ 18),
        ((-1683501 : Dyadic) * half ^ 22)⟩,
       ⟨((1784457 : Dyadic) * half ^ 22),
        ((-1159263 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((55029 : Dyadic) * half ^ 22),
        ((113647 : Dyadic) * half ^ 23)⟩,
       ⟨((-1392171 : Dyadic) * half ^ 22),
        ((-2864377 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((372253 : Dyadic) * half ^ 20),
        ((45225 : Dyadic) * half ^ 18)⟩,
       ⟨((1375365 : Dyadic) * half ^ 22),
        ((668571 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((262119 : Dyadic) * half ^ 21),
        ((1827033 : Dyadic) * half ^ 23)⟩,
       ⟨((-710691 : Dyadic) * half ^ 20),
        ((1741881 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word37Step30 :
    word37Chunk30.foldl (fun acc a => a.applyPacked acc)
      word37State30 = word37State31 := by decide +kernel

private def word37Chunk31 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word37State32 : PackedMat2 :=
    ⟨⟨⟨((-3022581 : Dyadic) * half ^ 22),
        ((-643737 : Dyadic) * half ^ 24)⟩,
       ⟨((3755131 : Dyadic) * half ^ 23),
        ((-2411295 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2914599 : Dyadic) * half ^ 23),
        ((-100999 : Dyadic) * half ^ 24)⟩,
       ⟨((-575479 : Dyadic) * half ^ 21),
        ((-2370897 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-308987 : Dyadic) * half ^ 21),
        ((612683 : Dyadic) * half ^ 24)⟩,
       ⟨((1134949 : Dyadic) * half ^ 23),
        ((5216515 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((381879 : Dyadic) * half ^ 21),
        ((2290031 : Dyadic) * half ^ 24)⟩,
       ⟨((-883779 : Dyadic) * half ^ 23),
        ((9800293 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word37Step31 :
    word37Chunk31.foldl (fun acc a => a.applyPacked acc)
      word37State31 = word37State32 := by decide +kernel

private def word37Chunk32 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word37State33 : PackedMat2 :=
    ⟨⟨⟨((6088409 : Dyadic) * half ^ 24),
        ((-1711565 : Dyadic) * half ^ 23)⟩,
       ⟨((-9025893 : Dyadic) * half ^ 24),
        ((231053 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1641857 : Dyadic) * half ^ 22),
        ((2083037 : Dyadic) * half ^ 23)⟩,
       ⟨((3867849 : Dyadic) * half ^ 23),
        ((235643 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1641857 : Dyadic) * half ^ 22),
        ((-2083037 : Dyadic) * half ^ 23)⟩,
       ⟨((3867849 : Dyadic) * half ^ 23),
        ((235643 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((6088409 : Dyadic) * half ^ 24),
        ((-1711565 : Dyadic) * half ^ 23)⟩,
       ⟨((9025893 : Dyadic) * half ^ 24),
        ((-231053 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word37Step32 :
    word37Chunk32.foldl (fun acc a => a.applyPacked acc)
      word37State32 = word37State33 := by decide +kernel

private def word37Chunk33 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word37State34 : PackedMat2 :=
    ⟨⟨⟨((-5340289 : Dyadic) * half ^ 25),
        ((2660051 : Dyadic) * half ^ 23)⟩,
       ⟨((17017101 : Dyadic) * half ^ 25),
        ((1335479 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-14720037 : Dyadic) * half ^ 25),
        ((2571299 : Dyadic) * half ^ 25)⟩,
       ⟨((5732365 : Dyadic) * half ^ 25),
        ((784421 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-14720037 : Dyadic) * half ^ 25),
        ((2571299 : Dyadic) * half ^ 25)⟩,
       ⟨((-5732365 : Dyadic) * half ^ 25),
        ((-784421 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((5340289 : Dyadic) * half ^ 25),
        ((-2660051 : Dyadic) * half ^ 23)⟩,
       ⟨((17017101 : Dyadic) * half ^ 25),
        ((1335479 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word37Step33 :
    word37Chunk33.foldl (fun acc a => a.applyPacked acc)
      word37State33 = word37State34 := by decide +kernel

private def word37Chunk34 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word37State35 : PackedMat2 :=
    ⟨⟨⟨((-1357341 : Dyadic) * half ^ 23),
        ((-545483 : Dyadic) * half ^ 24)⟩,
       ⟨((3655053 : Dyadic) * half ^ 25),
        ((18941753 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2846479 : Dyadic) * half ^ 24),
        ((-21432367 : Dyadic) * half ^ 26)⟩,
       ⟨((1230385 : Dyadic) * half ^ 22),
        ((-2875031 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((1230385 : Dyadic) * half ^ 22),
        ((-2875031 : Dyadic) * half ^ 26)⟩,
       ⟨((2846479 : Dyadic) * half ^ 24),
        ((-21432367 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-3655053 : Dyadic) * half ^ 25),
        ((-18941753 : Dyadic) * half ^ 25)⟩,
       ⟨((1357341 : Dyadic) * half ^ 23),
        ((545483 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word37Step34 :
    word37Chunk34.foldl (fun acc a => a.applyPacked acc)
      word37State34 = word37State35 := by decide +kernel

private def word37Chunk35 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word37State36 : PackedMat2 :=
    ⟨⟨⟨((-15680065 : Dyadic) * half ^ 26),
        ((-45867203 : Dyadic) * half ^ 27)⟩,
       ⟨((836287 : Dyadic) * half ^ 21),
        ((26560541 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-13810197 : Dyadic) * half ^ 25),
        ((52144453 : Dyadic) * half ^ 27)⟩,
       ⟨((-2611437 : Dyadic) * half ^ 26),
        ((-3928139 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-24108157 : Dyadic) * half ^ 26),
        ((30231831 : Dyadic) * half ^ 27)⟩,
       ⟨((-3504537 : Dyadic) * half ^ 23),
        ((25008957 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-9653331 : Dyadic) * half ^ 26),
        ((11081119 : Dyadic) * half ^ 27)⟩,
       ⟨((-2263367 : Dyadic) * half ^ 22),
        ((-42441249 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word37Step35 :
    word37Chunk35.foldl (fun acc a => a.applyPacked acc)
      word37State35 = word37State36 := by decide +kernel

private def word37Chunk36 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word37State37 : PackedMat2 :=
    ⟨⟨⟨((-24260115 : Dyadic) * half ^ 26),
        ((-44076251 : Dyadic) * half ^ 27)⟩,
       ⟨((9729193 : Dyadic) * half ^ 25),
        ((-271153 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((64409221 : Dyadic) * half ^ 27),
        ((-7799221 : Dyadic) * half ^ 25)⟩,
       ⟨((4665339 : Dyadic) * half ^ 27),
        ((22340707 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((64409221 : Dyadic) * half ^ 27),
        ((-7799221 : Dyadic) * half ^ 25)⟩,
       ⟨((-4665339 : Dyadic) * half ^ 27),
        ((-22340707 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((24260115 : Dyadic) * half ^ 26),
        ((44076251 : Dyadic) * half ^ 27)⟩,
       ⟨((9729193 : Dyadic) * half ^ 25),
        ((-271153 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word37Step36 :
    word37Chunk36.foldl (fun acc a => a.applyPacked acc)
      word37State36 = word37State37 := by decide +kernel

private def word37Chunk37 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word37State38 : PackedMat2 :=
    ⟨⟨⟨((73751541 : Dyadic) * half ^ 27),
        ((-67956909 : Dyadic) * half ^ 28)⟩,
       ⟨((-24797 : Dyadic) * half ^ 20),
        ((-28488195 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((51854721 : Dyadic) * half ^ 28),
        ((27702017 : Dyadic) * half ^ 27)⟩,
       ⟨((65642699 : Dyadic) * half ^ 28),
        ((3232083 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-79415345 : Dyadic) * half ^ 27),
        ((-29374355 : Dyadic) * half ^ 27)⟩,
       ⟨((24011311 : Dyadic) * half ^ 27),
        ((6893989 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-124933299 : Dyadic) * half ^ 28),
        ((70577525 : Dyadic) * half ^ 28)⟩,
       ⟨((-10980519 : Dyadic) * half ^ 28),
        ((76925557 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word37Step37 :
    word37Chunk37.foldl (fun acc a => a.applyPacked acc)
      word37State37 = word37State38 := by decide +kernel

private def word37Chunk38 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word37State39 : PackedMat2 :=
    ⟨⟨⟨((4316695 : Dyadic) * half ^ 23),
        ((-90024389 : Dyadic) * half ^ 29)⟩,
       ⟨((-60450485 : Dyadic) * half ^ 27),
        ((-142226199 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-60874633 : Dyadic) * half ^ 27),
        ((-3078331 : Dyadic) * half ^ 27)⟩,
       ⟨((-56830627 : Dyadic) * half ^ 28),
        ((55066901 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((56830627 : Dyadic) * half ^ 28),
        ((-55066901 : Dyadic) * half ^ 28)⟩,
       ⟨((60874633 : Dyadic) * half ^ 27),
        ((3078331 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-60450485 : Dyadic) * half ^ 27),
        ((-142226199 : Dyadic) * half ^ 29)⟩,
       ⟨((4316695 : Dyadic) * half ^ 23),
        ((-90024389 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word37Step38 :
    word37Chunk38.foldl (fun acc a => a.applyPacked acc)
      word37State38 = word37State39 := by decide +kernel

private def word37Chunk39 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word37State40 : PackedMat2 :=
    ⟨⟨⟨((10963401 : Dyadic) * half ^ 26),
        ((308360877 : Dyadic) * half ^ 30)⟩,
       ⟨((117657307 : Dyadic) * half ^ 29),
        ((-319513005 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-76383667 : Dyadic) * half ^ 29),
        ((-495858533 : Dyadic) * half ^ 30)⟩,
       ⟨((15814847 : Dyadic) * half ^ 26),
        ((-215998967 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-177964375 : Dyadic) * half ^ 28),
        ((50135109 : Dyadic) * half ^ 30)⟩,
       ⟨((-139929783 : Dyadic) * half ^ 29),
        ((-202902443 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((43563 : Dyadic) * half ^ 22),
        ((-205364515 : Dyadic) * half ^ 30)⟩,
       ⟨((-313936941 : Dyadic) * half ^ 29),
        ((29950099 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word37Step39 :
    word37Chunk39.foldl (fun acc a => a.applyPacked acc)
      word37State39 = word37State40 := by decide +kernel

private def word37Chunk40 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word37State41 : PackedMat2 :=
    ⟨⟨⟨((-25009563 : Dyadic) * half ^ 28),
        ((193350297 : Dyadic) * half ^ 31)⟩,
       ⟨((-193636007 : Dyadic) * half ^ 30),
        ((-861444593 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((283424555 : Dyadic) * half ^ 30),
        ((-491532407 : Dyadic) * half ^ 31)⟩,
       ⟨((-358638841 : Dyadic) * half ^ 29),
        ((11365071 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((358638841 : Dyadic) * half ^ 29),
        ((-11365071 : Dyadic) * half ^ 31)⟩,
       ⟨((-283424555 : Dyadic) * half ^ 30),
        ((491532407 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-193636007 : Dyadic) * half ^ 30),
        ((-861444593 : Dyadic) * half ^ 31)⟩,
       ⟨((-25009563 : Dyadic) * half ^ 28),
        ((193350297 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word37Step40 :
    word37Chunk40.foldl (fun acc a => a.applyPacked acc)
      word37State40 = word37State41 := by decide +kernel

private def word37Chunk41 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word37State42 : PackedMat2 :=
    ⟨⟨⟨((-957727075 : Dyadic) * half ^ 31),
        ((386242851 : Dyadic) * half ^ 31)⟩,
       ⟨((-537647149 : Dyadic) * half ^ 31),
        ((-626612229 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((59640911 : Dyadic) * half ^ 27),
        ((-18826503 : Dyadic) * half ^ 30)⟩,
       ⟨((-10295767 : Dyadic) * half ^ 28),
        ((-837109935 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-874762941 : Dyadic) * half ^ 31),
        ((108986055 : Dyadic) * half ^ 29)⟩,
       ⟨((799456929 : Dyadic) * half ^ 31),
        ((129577589 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((120184689 : Dyadic) * half ^ 30),
        ((93460889 : Dyadic) * half ^ 28)⟩,
       ⟨((-126606885 : Dyadic) * half ^ 28),
        ((210039963 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word37Step41 :
    word37Chunk41.foldl (fun acc a => a.applyPacked acc)
      word37State41 = word37State42 := by decide +kernel

private def word37Chunk42 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word37State43 : PackedMat2 :=
    ⟨⟨⟨((1392498987 : Dyadic) * half ^ 32),
        ((505995089 : Dyadic) * half ^ 32)⟩,
       ⟨((-3165206109 : Dyadic) * half ^ 32),
        ((-28437823 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-530587025 : Dyadic) * half ^ 32),
        ((582376141 : Dyadic) * half ^ 31)⟩,
       ⟨((-1677692369 : Dyadic) * half ^ 32),
        ((266223709 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-898528573 : Dyadic) * half ^ 32),
        ((-17923521 : Dyadic) * half ^ 27)⟩,
       ⟨((1430975991 : Dyadic) * half ^ 32),
        ((-1104139697 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((619746381 : Dyadic) * half ^ 32),
        ((569713137 : Dyadic) * half ^ 30)⟩,
       ⟨((-392243797 : Dyadic) * half ^ 32),
        ((886353561 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word37Step42 :
    word37Chunk42.foldl (fun acc a => a.applyPacked acc)
      word37State42 = word37State43 := by decide +kernel

private def word37Chunk43 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word37State44 : PackedMat2 :=
    ⟨⟨⟨((-549344207 : Dyadic) * half ^ 33),
        ((-84267225 : Dyadic) * half ^ 30)⟩,
       ⟨((-3389937243 : Dyadic) * half ^ 33),
        ((1102794495 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2414739421 : Dyadic) * half ^ 33),
        ((1976402757 : Dyadic) * half ^ 32)⟩,
       ⟨((4136764191 : Dyadic) * half ^ 33),
        ((-1493177899 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2414739421 : Dyadic) * half ^ 33),
        ((1976402757 : Dyadic) * half ^ 32)⟩,
       ⟨((-4136764191 : Dyadic) * half ^ 33),
        ((1493177899 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((549344207 : Dyadic) * half ^ 33),
        ((84267225 : Dyadic) * half ^ 30)⟩,
       ⟨((-3389937243 : Dyadic) * half ^ 33),
        ((1102794495 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word37Step43 :
    word37Chunk43.foldl (fun acc a => a.applyPacked acc)
      word37State43 = word37State44 := by decide +kernel

private def word37Chunk44 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word37State45 : PackedMat2 :=
    ⟨⟨⟨((427255155 : Dyadic) * half ^ 33),
        ((-3849689267 : Dyadic) * half ^ 33)⟩,
       ⟨((493603759 : Dyadic) * half ^ 32),
        ((-1242408861 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((94129319 : Dyadic) * half ^ 33),
        ((8047597419 : Dyadic) * half ^ 34)⟩,
       ⟨((2247728721 : Dyadic) * half ^ 33),
        ((2217845505 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-2914875957 : Dyadic) * half ^ 33),
        ((1076799701 : Dyadic) * half ^ 33)⟩,
       ⟨((2566360731 : Dyadic) * half ^ 32),
        ((292732255 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1303640203 : Dyadic) * half ^ 32),
        ((-559952363 : Dyadic) * half ^ 34)⟩,
       ⟨((318256133 : Dyadic) * half ^ 29),
        ((-1414462673 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word37Step44 :
    word37Chunk44.foldl (fun acc a => a.applyPacked acc)
      word37State44 = word37State45 := by decide +kernel

private def word37Chunk45 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word37State46 : PackedMat2 :=
    ⟨⟨⟨((-1734154759 : Dyadic) * half ^ 32),
        ((11777843295 : Dyadic) * half ^ 35)⟩,
       ⟨((-519329029 : Dyadic) * half ^ 34),
        ((-1458240099 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-2034262489 : Dyadic) * half ^ 34),
        ((-12978994689 : Dyadic) * half ^ 35)⟩,
       ⟨((2017805047 : Dyadic) * half ^ 32),
        ((6757147281 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-2017805047 : Dyadic) * half ^ 32),
        ((-6757147281 : Dyadic) * half ^ 35)⟩,
       ⟨((2034262489 : Dyadic) * half ^ 34),
        ((12978994689 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-519329029 : Dyadic) * half ^ 34),
        ((-1458240099 : Dyadic) * half ^ 35)⟩,
       ⟨((-1734154759 : Dyadic) * half ^ 32),
        ((11777843295 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word37Step45 :
    word37Chunk45.foldl (fun acc a => a.applyPacked acc)
      word37State45 = word37State46 := by decide +kernel

private def word37Chunk46 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word37State47 : PackedMat2 :=
    ⟨⟨⟨((3852024007 : Dyadic) * half ^ 33),
        ((-2306494459 : Dyadic) * half ^ 33)⟩,
       ⟨((736605925 : Dyadic) * half ^ 34),
        ((10422333957 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-15890413279 : Dyadic) * half ^ 35),
        ((-4570405081 : Dyadic) * half ^ 34)⟩,
       ⟨((11340926489 : Dyadic) * half ^ 35),
        ((-101682635 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-5383866161 : Dyadic) * half ^ 34),
        ((-2274743395 : Dyadic) * half ^ 35)⟩,
       ⟨((-3756944001 : Dyadic) * half ^ 34),
        ((-3403917471 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1196356121 : Dyadic) * half ^ 35),
        ((-8440653939 : Dyadic) * half ^ 35)⟩,
       ⟨((19648311793 : Dyadic) * half ^ 35),
        ((-6967442089 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word37Step46 :
    word37Chunk46.foldl (fun acc a => a.applyPacked acc)
      word37State46 = word37State47 := by decide +kernel

private def word37Chunk47 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word37State48 : PackedMat2 :=
    ⟨⟨⟨((-47297351993 : Dyadic) * half ^ 36),
        ((3496342573 : Dyadic) * half ^ 36)⟩,
       ⟨((7617352297 : Dyadic) * half ^ 36),
        ((-12411663869 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-4160757333 : Dyadic) * half ^ 36),
        ((-11288591501 : Dyadic) * half ^ 36)⟩,
       ⟨((-18350760297 : Dyadic) * half ^ 36),
        ((-8378036743 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((4160757333 : Dyadic) * half ^ 36),
        ((11288591501 : Dyadic) * half ^ 36)⟩,
       ⟨((-18350760297 : Dyadic) * half ^ 36),
        ((-8378036743 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-47297351993 : Dyadic) * half ^ 36),
        ((3496342573 : Dyadic) * half ^ 36)⟩,
       ⟨((-7617352297 : Dyadic) * half ^ 36),
        ((12411663869 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word37Step47 :
    word37Chunk47.foldl (fun acc a => a.applyPacked acc)
      word37State47 = word37State48 := by decide +kernel

private def word37Chunk48 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word37State49 : PackedMat2 :=
    ⟨⟨⟨((-380759321 : Dyadic) * half ^ 33),
        ((-29569025737 : Dyadic) * half ^ 37)⟩,
       ⟨((-15623584057 : Dyadic) * half ^ 34),
        ((-142063945 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((12046623803 : Dyadic) * half ^ 36),
        ((-1857754499 : Dyadic) * half ^ 34)⟩,
       ⟨((-4086479785 : Dyadic) * half ^ 35),
        ((-4899675975 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-2531342021 : Dyadic) * half ^ 36),
        ((20219583373 : Dyadic) * half ^ 37)⟩,
       ⟨((12330693971 : Dyadic) * half ^ 36),
        ((-3873664233 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((229898139 : Dyadic) * half ^ 30),
        ((-14862065415 : Dyadic) * half ^ 35)⟩,
       ⟨((-14855544841 : Dyadic) * half ^ 36),
        ((-16385102699 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word37Step48 :
    word37Chunk48.foldl (fun acc a => a.applyPacked acc)
      word37State48 = word37State49 := by decide +kernel

private def word37Chunk49 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word37State50 : PackedMat2 :=
    ⟨⟨⟨((48295587879 : Dyadic) * half ^ 37),
        ((109378934715 : Dyadic) * half ^ 38)⟩,
       ⟨((28461705395 : Dyadic) * half ^ 36),
        ((-98841036821 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((4154237321 : Dyadic) * half ^ 36),
        ((-14567290345 : Dyadic) * half ^ 38)⟩,
       ⟨((-6966655439 : Dyadic) * half ^ 37),
        ((-66729430605 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-6966655439 : Dyadic) * half ^ 37),
        ((-66729430605 : Dyadic) * half ^ 38)⟩,
       ⟨((4154237321 : Dyadic) * half ^ 36),
        ((-14567290345 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-28461705395 : Dyadic) * half ^ 36),
        ((98841036821 : Dyadic) * half ^ 38)⟩,
       ⟨((-48295587879 : Dyadic) * half ^ 37),
        ((-109378934715 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word37Step49 :
    word37Chunk49.foldl (fun acc a => a.applyPacked acc)
      word37State49 = word37State50 := by decide +kernel

private def word37Chunk50 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word37State51 : PackedMat2 :=
    ⟨⟨⟨((75366524765 : Dyadic) * half ^ 38),
        ((4346351797 : Dyadic) * half ^ 37)⟩,
       ⟨((127985670989 : Dyadic) * half ^ 38),
        ((-94736710209 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((102521371943 : Dyadic) * half ^ 38),
        ((49672205959 : Dyadic) * half ^ 37)⟩,
       ⟨((66300989669 : Dyadic) * half ^ 38),
        ((19379456693 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-79964955225 : Dyadic) * half ^ 38),
        ((-18110191137 : Dyadic) * half ^ 38)⟩,
       ⟨((118723868611 : Dyadic) * half ^ 38),
        ((42205590403 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((103429413803 : Dyadic) * half ^ 38),
        ((-3288696639 : Dyadic) * half ^ 35)⟩,
       ⟨((86044006615 : Dyadic) * half ^ 38),
        ((-101676097877 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word37Step50 :
    word37Chunk50.foldl (fun acc a => a.applyPacked acc)
      word37State50 = word37State51 := by decide +kernel

private def word37Chunk51 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word37State52 : PackedMat2 :=
    ⟨⟨⟨((301111487445 : Dyadic) * half ^ 39),
        ((-35039098673 : Dyadic) * half ^ 37)⟩,
       ⟨((132713862815 : Dyadic) * half ^ 39),
        ((198267273635 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((213423816435 : Dyadic) * half ^ 39),
        ((32043502015 : Dyadic) * half ^ 39)⟩,
       ⟨((89589287921 : Dyadic) * half ^ 39),
        ((50514065045 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-68984628075 : Dyadic) * half ^ 39),
        ((61917264257 : Dyadic) * half ^ 39)⟩,
       ⟨((-133071632105 : Dyadic) * half ^ 39),
        ((-75753276089 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((338423668327 : Dyadic) * half ^ 39),
        ((-84198812315 : Dyadic) * half ^ 39)⟩,
       ⟨((58110878943 : Dyadic) * half ^ 39),
        ((108456337565 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word37Step51 :
    word37Chunk51.foldl (fun acc a => a.applyPacked acc)
      word37State51 = word37State52 := by decide +kernel

private def word37Chunk52 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word37State53 : PackedMat2 :=
    ⟨⟨⟨((-358889132665 : Dyadic) * half ^ 40),
        ((-32389637619 : Dyadic) * half ^ 40)⟩,
       ⟨((-349794382257 : Dyadic) * half ^ 40),
        ((181716264373 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((95562255333 : Dyadic) * half ^ 40),
        ((2493962515 : Dyadic) * half ^ 33)⟩,
       ⟨((179954150301 : Dyadic) * half ^ 40),
        ((472321957627 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-95562255333 : Dyadic) * half ^ 40),
        ((-2493962515 : Dyadic) * half ^ 33)⟩,
       ⟨((179954150301 : Dyadic) * half ^ 40),
        ((472321957627 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-358889132665 : Dyadic) * half ^ 40),
        ((-32389637619 : Dyadic) * half ^ 40)⟩,
       ⟨((349794382257 : Dyadic) * half ^ 40),
        ((-181716264373 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word37Step52 :
    word37Chunk52.foldl (fun acc a => a.applyPacked acc)
      word37State52 = word37State53 := by decide +kernel

private def word37Chunk53 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word37State54 : PackedMat2 :=
    ⟨⟨⟨((-31658378283 : Dyadic) * half ^ 37),
        ((-215019966057 : Dyadic) * half ^ 39)⟩,
       ⟨((260535340267 : Dyadic) * half ^ 40),
        ((-42498509049 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((394771572333 : Dyadic) * half ^ 40),
        ((-731101459755 : Dyadic) * half ^ 41)⟩,
       ⟨((322192002111 : Dyadic) * half ^ 40),
        ((494633977017 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-322192002111 : Dyadic) * half ^ 40),
        ((-494633977017 : Dyadic) * half ^ 41)⟩,
       ⟨((-394771572333 : Dyadic) * half ^ 40),
        ((731101459755 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((260535340267 : Dyadic) * half ^ 40),
        ((-42498509049 : Dyadic) * half ^ 38)⟩,
       ⟨((-31658378283 : Dyadic) * half ^ 37),
        ((-215019966057 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word37Step53 :
    word37Chunk53.foldl (fun acc a => a.applyPacked acc)
      word37State53 = word37State54 := by decide +kernel

private def word37Chunk54 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word37State55 : PackedMat2 :=
    ⟨⟨⟨((-18635058569 : Dyadic) * half ^ 38),
        ((-30698004355 : Dyadic) * half ^ 42)⟩,
       ⟨((-500968616455 : Dyadic) * half ^ 41),
        ((-585403048055 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-482466315285 : Dyadic) * half ^ 39),
        ((316315366963 : Dyadic) * half ^ 42)⟩,
       ⟨((-305700067065 : Dyadic) * half ^ 41),
        ((-1022574228859 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-88282357737 : Dyadic) * half ^ 39),
        ((-2235565328205 : Dyadic) * half ^ 42)⟩,
       ⟨((669444797911 : Dyadic) * half ^ 41),
        ((-1624165194075 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((308050526205 : Dyadic) * half ^ 41),
        ((650049085007 : Dyadic) * half ^ 42)⟩,
       ⟨((-138676260925 : Dyadic) * half ^ 40),
        ((-351888147903 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word37Step54 :
    word37Chunk54.foldl (fun acc a => a.applyPacked acc)
      word37State54 = word37State55 := by decide +kernel

private def word37Chunk55 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word37State56 : PackedMat2 :=
    ⟨⟨⟨((-1002463654283 : Dyadic) * half ^ 42),
        ((321076141819 : Dyadic) * half ^ 41)⟩,
       ⟨((349537688763 : Dyadic) * half ^ 42),
        ((28975943361 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((763522648667 : Dyadic) * half ^ 40),
        ((-55450520489 : Dyadic) * half ^ 39)⟩,
       ⟨((-1239131620739 : Dyadic) * half ^ 41),
        ((-741039390219 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1184643554131 : Dyadic) * half ^ 42),
        ((-287913676595 : Dyadic) * half ^ 42)⟩,
       ⟨((-297435226307 : Dyadic) * half ^ 42),
        ((-2766176918073 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((552883688707 : Dyadic) * half ^ 41),
        ((-40807872845 : Dyadic) * half ^ 39)⟩,
       ⟨((89268594931 : Dyadic) * half ^ 41),
        ((-676000671523 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word37Step55 :
    word37Chunk55.foldl (fun acc a => a.applyPacked acc)
      word37State55 = word37State56 := by decide +kernel

private def word37Chunk56 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word37State57 : PackedMat2 :=
    ⟨⟨⟨((-1543496362965 : Dyadic) * half ^ 43),
        ((-1103559069139 : Dyadic) * half ^ 42)⟩,
       ⟨((2978857127937 : Dyadic) * half ^ 43),
        ((548085808489 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((1241517224891 : Dyadic) * half ^ 43),
        ((3331514891111 : Dyadic) * half ^ 43)⟩,
       ⟨((2574475468513 : Dyadic) * half ^ 43),
        ((-891004922257 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((6895534580139 : Dyadic) * half ^ 43),
        ((-666479121811 : Dyadic) * half ^ 43)⟩,
       ⟨((232504797917 : Dyadic) * half ^ 43),
        ((-953998173351 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((2755203946767 : Dyadic) * half ^ 43),
        ((2261176745451 : Dyadic) * half ^ 43)⟩,
       ⟨((-1659032329789 : Dyadic) * half ^ 43),
        ((358840191243 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word37Step56 :
    word37Chunk56.foldl (fun acc a => a.applyPacked acc)
      word37State56 = word37State57 := by decide +kernel

private def word37Chunk57 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word37State58 : PackedMat2 :=
    ⟨⟨⟨((-1691260045063 : Dyadic) * half ^ 42),
        ((1480937636683 : Dyadic) * half ^ 43)⟩,
       ⟨((-3711451522791 : Dyadic) * half ^ 43),
        ((-167782451731 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((378649938417 : Dyadic) * half ^ 40),
        ((114111484595 : Dyadic) * half ^ 44)⟩,
       ⟨((-388619925563 : Dyadic) * half ^ 41),
        ((6596412788563 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-388619925563 : Dyadic) * half ^ 41),
        ((6596412788563 : Dyadic) * half ^ 44)⟩,
       ⟨((378649938417 : Dyadic) * half ^ 40),
        ((114111484595 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((3711451522791 : Dyadic) * half ^ 43),
        ((167782451731 : Dyadic) * half ^ 39)⟩,
       ⟨((1691260045063 : Dyadic) * half ^ 42),
        ((-1480937636683 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word37Step57 :
    word37Chunk57.foldl (fun acc a => a.applyPacked acc)
      word37State57 = word37State58 := by decide +kernel

private def word37Chunk58 : List Letter := [.h, .s, .t, .h, .s, .t, .h]
private def word37State59 : PackedMat2 :=
    ⟨⟨⟨((14614690613875 : Dyadic) * half ^ 44),
        ((4210814419775 : Dyadic) * half ^ 45)⟩,
       ⟨((-1028950202583 : Dyadic) * half ^ 42),
        ((5820621325429 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-3512288866055 : Dyadic) * half ^ 44),
        ((4967126549347 : Dyadic) * half ^ 45)⟩,
       ⟨((943371120447 : Dyadic) * half ^ 42),
        ((-5336512931549 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((3512288866055 : Dyadic) * half ^ 44),
        ((-4967126549347 : Dyadic) * half ^ 45)⟩,
       ⟨((943371120447 : Dyadic) * half ^ 42),
        ((-5336512931549 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((14614690613875 : Dyadic) * half ^ 44),
        ((4210814419775 : Dyadic) * half ^ 45)⟩,
       ⟨((1028950202583 : Dyadic) * half ^ 42),
        ((-5820621325429 : Dyadic) * half ^ 45)⟩⟩⟩
private lemma word37Step58 :
    word37Chunk58.foldl (fun acc a => a.applyPacked acc)
      word37State58 = word37State59 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word37_check : check word37 37 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word37 = word37State59.toMatrix := by
    unfold evalRingPacked
    change ((
      word37Chunk0 ++ word37Chunk1 ++ word37Chunk2 ++ word37Chunk3 ++
      word37Chunk4 ++ word37Chunk5 ++ word37Chunk6 ++ word37Chunk7 ++
      word37Chunk8 ++ word37Chunk9 ++ word37Chunk10 ++ word37Chunk11 ++
      word37Chunk12 ++ word37Chunk13 ++ word37Chunk14 ++ word37Chunk15 ++
      word37Chunk16 ++ word37Chunk17 ++ word37Chunk18 ++ word37Chunk19 ++
      word37Chunk20 ++ word37Chunk21 ++ word37Chunk22 ++ word37Chunk23 ++
      word37Chunk24 ++ word37Chunk25 ++ word37Chunk26 ++ word37Chunk27 ++
      word37Chunk28 ++ word37Chunk29 ++ word37Chunk30 ++ word37Chunk31 ++
      word37Chunk32 ++ word37Chunk33 ++ word37Chunk34 ++ word37Chunk35 ++
      word37Chunk36 ++ word37Chunk37 ++ word37Chunk38 ++ word37Chunk39 ++
      word37Chunk40 ++ word37Chunk41 ++ word37Chunk42 ++ word37Chunk43 ++
      word37Chunk44 ++ word37Chunk45 ++ word37Chunk46 ++ word37Chunk47 ++
      word37Chunk48 ++ word37Chunk49 ++ word37Chunk50 ++ word37Chunk51 ++
      word37Chunk52 ++ word37Chunk53 ++ word37Chunk54 ++ word37Chunk55 ++
      word37Chunk56 ++ word37Chunk57 ++ word37Chunk58
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word37Step0, word37Step1, word37Step2, word37Step3, word37Step4,
      word37Step5, word37Step6, word37Step7, word37Step8, word37Step9,
      word37Step10, word37Step11, word37Step12, word37Step13, word37Step14,
      word37Step15, word37Step16, word37Step17, word37Step18, word37Step19,
      word37Step20, word37Step21, word37Step22, word37Step23, word37Step24,
      word37Step25, word37Step26, word37Step27, word37Step28, word37Step29,
      word37Step30, word37Step31, word37Step32, word37Step33, word37Step34,
      word37Step35, word37Step36, word37Step37, word37Step38, word37Step39,
      word37Step40, word37Step41, word37Step42, word37Step43, word37Step44,
      word37Step45, word37Step46, word37Step47, word37Step48, word37Step49,
      word37Step50, word37Step51, word37Step52, word37Step53, word37Step54,
      word37Step55, word37Step56, word37Step57, word37Step58]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end

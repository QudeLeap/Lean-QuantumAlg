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
private def word32Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word32State1 : PackedMat2 :=
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
private lemma word32Step0 :
    word32Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word32State1 := by decide +kernel

private def word32Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word32State2 : PackedMat2 :=
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
private lemma word32Step1 :
    word32Chunk1.foldl (fun acc a => a.applyPacked acc)
      word32State1 = word32State2 := by decide +kernel

private def word32Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word32State3 : PackedMat2 :=
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
private lemma word32Step2 :
    word32Chunk2.foldl (fun acc a => a.applyPacked acc)
      word32State2 = word32State3 := by decide +kernel

private def word32Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .s]
private def word32State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word32Step3 :
    word32Chunk3.foldl (fun acc a => a.applyPacked acc)
      word32State3 = word32State4 := by decide +kernel

private def word32Chunk4 : List Letter := [.s, .h, .s, .t, .h, .s, .t, .h]
private def word32State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word32Step4 :
    word32Chunk4.foldl (fun acc a => a.applyPacked acc)
      word32State4 = word32State5 := by decide +kernel

private def word32Chunk5 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word32State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word32Step5 :
    word32Chunk5.foldl (fun acc a => a.applyPacked acc)
      word32State5 = word32State6 := by decide +kernel

private def word32Chunk6 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word32State7 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩⟩
private lemma word32Step6 :
    word32Chunk6.foldl (fun acc a => a.applyPacked acc)
      word32State6 = word32State7 := by decide +kernel

private def word32Chunk7 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word32State8 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word32Step7 :
    word32Chunk7.foldl (fun acc a => a.applyPacked acc)
      word32State7 = word32State8 := by decide +kernel

private def word32Chunk8 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word32State9 : PackedMat2 :=
    ⟨⟨⟨((-19 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩,
       ⟨((-13 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 5)⟩,
       ⟨((-13 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word32Step8 :
    word32Chunk8.foldl (fun acc a => a.applyPacked acc)
      word32State8 = word32State9 := by decide +kernel

private def word32Chunk9 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word32State10 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-13 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word32Step9 :
    word32Chunk9.foldl (fun acc a => a.applyPacked acc)
      word32State9 = word32State10 := by decide +kernel

private def word32Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word32State11 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 6),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((21 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 7)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((-41 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 6),
        ((63 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((21 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((27 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word32Step10 :
    word32Chunk10.foldl (fun acc a => a.applyPacked acc)
      word32State10 = word32State11 := by decide +kernel

private def word32Chunk11 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word32State12 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 6),
        ((-21 : Dyadic) * half ^ 6)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((33 : Dyadic) * half ^ 6)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((-41 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-33 : Dyadic) * half ^ 6)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((-41 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 6),
        ((-21 : Dyadic) * half ^ 6)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word32Step11 :
    word32Chunk11.foldl (fun acc a => a.applyPacked acc)
      word32State11 = word32State12 := by decide +kernel

private def word32Chunk12 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word32State13 : PackedMat2 :=
    ⟨⟨⟨((-121 : Dyadic) * half ^ 8),
        ((-57 : Dyadic) * half ^ 8)⟩,
       ⟨((-101 : Dyadic) * half ^ 8),
        ((-23 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((121 : Dyadic) * half ^ 8),
        ((-7 : Dyadic) * half ^ 6)⟩,
       ⟨((81 : Dyadic) * half ^ 8),
        ((-9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((121 : Dyadic) * half ^ 8),
        ((-7 : Dyadic) * half ^ 6)⟩,
       ⟨((-81 : Dyadic) * half ^ 8),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((121 : Dyadic) * half ^ 8),
        ((57 : Dyadic) * half ^ 8)⟩,
       ⟨((-101 : Dyadic) * half ^ 8),
        ((-23 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word32Step12 :
    word32Chunk12.foldl (fun acc a => a.applyPacked acc)
      word32State12 = word32State13 := by decide +kernel

private def word32Chunk13 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word32State14 : PackedMat2 :=
    ⟨⟨⟨((87 : Dyadic) * half ^ 9),
        ((-199 : Dyadic) * half ^ 9)⟩,
       ⟨((-211 : Dyadic) * half ^ 9),
        ((-89 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-217 : Dyadic) * half ^ 9),
        ((41 : Dyadic) * half ^ 8)⟩,
       ⟨((-57 : Dyadic) * half ^ 9),
        ((43 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 9),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((125 : Dyadic) * half ^ 9),
        ((-137 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 9),
        ((149 : Dyadic) * half ^ 9)⟩,
       ⟨((377 : Dyadic) * half ^ 9),
        ((31 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word32Step13 :
    word32Chunk13.foldl (fun acc a => a.applyPacked acc)
      word32State13 = word32State14 := by decide +kernel

private def word32Chunk14 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word32State15 : PackedMat2 :=
    ⟨⟨⟨((-101 : Dyadic) * half ^ 8),
        ((347 : Dyadic) * half ^ 10)⟩,
       ⟨((-53 : Dyadic) * half ^ 8),
        ((-453 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((67 : Dyadic) * half ^ 9),
        ((-61 : Dyadic) * half ^ 10)⟩,
       ⟨((-171 : Dyadic) * half ^ 9),
        ((-153 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((171 : Dyadic) * half ^ 9),
        ((153 : Dyadic) * half ^ 10)⟩,
       ⟨((-67 : Dyadic) * half ^ 9),
        ((61 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-53 : Dyadic) * half ^ 8),
        ((-453 : Dyadic) * half ^ 10)⟩,
       ⟨((-101 : Dyadic) * half ^ 8),
        ((347 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word32Step14 :
    word32Chunk14.foldl (fun acc a => a.applyPacked acc)
      word32State14 = word32State15 := by decide +kernel

private def word32Chunk15 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word32State16 : PackedMat2 :=
    ⟨⟨⟨((879 : Dyadic) * half ^ 10),
        ((163 : Dyadic) * half ^ 11)⟩,
       ⟨((-27 : Dyadic) * half ^ 7),
        ((553 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 8),
        ((-1 : Dyadic) * half ^ 11)⟩,
       ⟨((-71 : Dyadic) * half ^ 10),
        ((335 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((167 : Dyadic) * half ^ 10),
        ((-27 : Dyadic) * half ^ 11)⟩,
       ⟨((-21 : Dyadic) * half ^ 7),
        ((115 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-179 : Dyadic) * half ^ 9),
        ((-663 : Dyadic) * half ^ 11)⟩,
       ⟨((195 : Dyadic) * half ^ 10),
        ((-1095 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word32Step15 :
    word32Chunk15.foldl (fun acc a => a.applyPacked acc)
      word32State15 = word32State16 := by decide +kernel

private def word32Chunk16 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word32State17 : PackedMat2 :=
    ⟨⟨⟨((423 : Dyadic) * half ^ 11),
        ((301 : Dyadic) * half ^ 10)⟩,
       ⟨((1503 : Dyadic) * half ^ 11),
        ((-151 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-809 : Dyadic) * half ^ 11),
        ((-205 : Dyadic) * half ^ 11)⟩,
       ⟨((163 : Dyadic) * half ^ 11),
        ((205 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((809 : Dyadic) * half ^ 11),
        ((205 : Dyadic) * half ^ 11)⟩,
       ⟨((163 : Dyadic) * half ^ 11),
        ((205 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((423 : Dyadic) * half ^ 11),
        ((301 : Dyadic) * half ^ 10)⟩,
       ⟨((-1503 : Dyadic) * half ^ 11),
        ((151 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word32Step16 :
    word32Chunk16.foldl (fun acc a => a.applyPacked acc)
      word32State16 = word32State17 := by decide +kernel

private def word32Chunk17 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word32State18 : PackedMat2 :=
    ⟨⟨⟨((-299 : Dyadic) * half ^ 12),
        ((201 : Dyadic) * half ^ 11)⟩,
       ⟨((-591 : Dyadic) * half ^ 12),
        ((1619 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-873 : Dyadic) * half ^ 12),
        ((-1977 : Dyadic) * half ^ 12)⟩,
       ⟨((-1303 : Dyadic) * half ^ 12),
        ((249 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1303 : Dyadic) * half ^ 12),
        ((-249 : Dyadic) * half ^ 11)⟩,
       ⟨((873 : Dyadic) * half ^ 12),
        ((1977 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-591 : Dyadic) * half ^ 12),
        ((1619 : Dyadic) * half ^ 12)⟩,
       ⟨((-299 : Dyadic) * half ^ 12),
        ((201 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word32Step17 :
    word32Chunk17.foldl (fun acc a => a.applyPacked acc)
      word32State17 = word32State18 := by decide +kernel

private def word32Chunk18 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word32State19 : PackedMat2 :=
    ⟨⟨⟨((1349 : Dyadic) * half ^ 12),
        ((-151 : Dyadic) * half ^ 9)⟩,
       ⟨((953 : Dyadic) * half ^ 11),
        ((447 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1621 : Dyadic) * half ^ 12),
        ((31 : Dyadic) * half ^ 10)⟩,
       ⟨((-11 : Dyadic) * half ^ 9),
        ((-1439 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1315 : Dyadic) * half ^ 12),
        ((-1709 : Dyadic) * half ^ 13)⟩,
       ⟨((1563 : Dyadic) * half ^ 12),
        ((-1533 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((157 : Dyadic) * half ^ 11),
        ((-3255 : Dyadic) * half ^ 13)⟩,
       ⟨((1051 : Dyadic) * half ^ 11),
        ((557 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word32Step18 :
    word32Chunk18.foldl (fun acc a => a.applyPacked acc)
      word32State18 = word32State19 := by decide +kernel

private def word32Chunk19 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word32State20 : PackedMat2 :=
    ⟨⟨⟨((-85 : Dyadic) * half ^ 13),
        ((-4017 : Dyadic) * half ^ 13)⟩,
       ⟨((-939 : Dyadic) * half ^ 12),
        ((2675 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1741 : Dyadic) * half ^ 13),
        ((-2025 : Dyadic) * half ^ 13)⟩,
       ⟨((357 : Dyadic) * half ^ 12),
        ((405 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-357 : Dyadic) * half ^ 12),
        ((-405 : Dyadic) * half ^ 11)⟩,
       ⟨((1741 : Dyadic) * half ^ 13),
        ((2025 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-939 : Dyadic) * half ^ 12),
        ((2675 : Dyadic) * half ^ 13)⟩,
       ⟨((-85 : Dyadic) * half ^ 13),
        ((-4017 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word32Step19 :
    word32Chunk19.foldl (fun acc a => a.applyPacked acc)
      word32State19 = word32State20 := by decide +kernel

private def word32Chunk20 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word32State21 : PackedMat2 :=
    ⟨⟨⟨((-2511 : Dyadic) * half ^ 14),
        ((-3065 : Dyadic) * half ^ 15)⟩,
       ⟨((1215 : Dyadic) * half ^ 12),
        ((-12817 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-179 : Dyadic) * half ^ 8),
        ((-4929 : Dyadic) * half ^ 15)⟩,
       ⟨((2841 : Dyadic) * half ^ 14),
        ((-659 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-1397 : Dyadic) * half ^ 13),
        ((-8615 : Dyadic) * half ^ 15)⟩,
       ⟨((-2135 : Dyadic) * half ^ 14),
        ((-14297 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((7941 : Dyadic) * half ^ 14),
        ((-2349 : Dyadic) * half ^ 15)⟩,
       ⟨((-1219 : Dyadic) * half ^ 12),
        ((7371 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word32Step20 :
    word32Chunk20.foldl (fun acc a => a.applyPacked acc)
      word32State20 = word32State21 := by decide +kernel

private def word32Chunk21 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word32State22 : PackedMat2 :=
    ⟨⟨⟨((3911 : Dyadic) * half ^ 14),
        ((-20125 : Dyadic) * half ^ 16)⟩,
       ⟨((-15401 : Dyadic) * half ^ 15),
        ((-18629 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-879 : Dyadic) * half ^ 15),
        ((-16851 : Dyadic) * half ^ 16)⟩,
       ⟨((1777 : Dyadic) * half ^ 13),
        ((-20301 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((1161 : Dyadic) * half ^ 11),
        ((-6229 : Dyadic) * half ^ 16)⟩,
       ⟨((-1725 : Dyadic) * half ^ 15),
        ((7987 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-19377 : Dyadic) * half ^ 15),
        ((-7579 : Dyadic) * half ^ 16)⟩,
       ⟨((-187 : Dyadic) * half ^ 13),
        ((23223 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word32Step21 :
    word32Chunk21.foldl (fun acc a => a.applyPacked acc)
      word32State21 = word32State22 := by decide +kernel

private def word32Chunk22 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word32State23 : PackedMat2 :=
    ⟨⟨⟨((-5603 : Dyadic) * half ^ 16),
        ((8711 : Dyadic) * half ^ 16)⟩,
       ⟨((-17915 : Dyadic) * half ^ 16),
        ((-15313 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-31781 : Dyadic) * half ^ 16),
        ((9667 : Dyadic) * half ^ 15)⟩,
       ⟨((-36581 : Dyadic) * half ^ 16),
        ((-1329 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-31781 : Dyadic) * half ^ 16),
        ((9667 : Dyadic) * half ^ 15)⟩,
       ⟨((36581 : Dyadic) * half ^ 16),
        ((1329 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((5603 : Dyadic) * half ^ 16),
        ((-8711 : Dyadic) * half ^ 16)⟩,
       ⟨((-17915 : Dyadic) * half ^ 16),
        ((-15313 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word32Step22 :
    word32Chunk22.foldl (fun acc a => a.applyPacked acc)
      word32State22 = word32State23 := by decide +kernel

private def word32Chunk23 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word32State24 : PackedMat2 :=
    ⟨⟨⟨((-16387 : Dyadic) * half ^ 15),
        ((3719 : Dyadic) * half ^ 16)⟩,
       ⟨((-8485 : Dyadic) * half ^ 16),
        ((-6001 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((91 : Dyadic) * half ^ 13),
        ((9373 : Dyadic) * half ^ 14)⟩,
       ⟨((2795 : Dyadic) * half ^ 16),
        ((-81 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((8725 : Dyadic) * half ^ 14),
        ((3523 : Dyadic) * half ^ 17)⟩,
       ⟨((10021 : Dyadic) * half ^ 14),
        ((-2067 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((8283 : Dyadic) * half ^ 16),
        ((41259 : Dyadic) * half ^ 17)⟩,
       ⟨((-15721 : Dyadic) * half ^ 16),
        ((24289 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word32Step23 :
    word32Chunk23.foldl (fun acc a => a.applyPacked acc)
      word32State23 = word32State24 := by decide +kernel

private def word32Chunk24 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word32State25 : PackedMat2 :=
    ⟨⟨⟨((-18977 : Dyadic) * half ^ 17),
        ((-45067 : Dyadic) * half ^ 18)⟩,
       ⟨((-48431 : Dyadic) * half ^ 16),
        ((-7465 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((31953 : Dyadic) * half ^ 16),
        ((-34619 : Dyadic) * half ^ 18)⟩,
       ⟨((11265 : Dyadic) * half ^ 17),
        ((56285 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-31953 : Dyadic) * half ^ 16),
        ((34619 : Dyadic) * half ^ 18)⟩,
       ⟨((11265 : Dyadic) * half ^ 17),
        ((56285 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-18977 : Dyadic) * half ^ 17),
        ((-45067 : Dyadic) * half ^ 18)⟩,
       ⟨((48431 : Dyadic) * half ^ 16),
        ((7465 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word32Step24 :
    word32Chunk24.foldl (fun acc a => a.applyPacked acc)
      word32State24 = word32State25 := by decide +kernel

private def word32Chunk25 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word32State26 : PackedMat2 :=
    ⟨⟨⟨((-30765 : Dyadic) * half ^ 18),
        ((67181 : Dyadic) * half ^ 19)⟩,
       ⟨((-30605 : Dyadic) * half ^ 16),
        ((-105781 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((48647 : Dyadic) * half ^ 17),
        ((-206999 : Dyadic) * half ^ 19)⟩,
       ⟨((66927 : Dyadic) * half ^ 18),
        ((138313 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-34343 : Dyadic) * half ^ 18),
        ((164221 : Dyadic) * half ^ 19)⟩,
       ⟨((-10791 : Dyadic) * half ^ 14),
        ((30367 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((4825 : Dyadic) * half ^ 16),
        ((153185 : Dyadic) * half ^ 19)⟩,
       ⟨((-86481 : Dyadic) * half ^ 18),
        ((-91655 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word32Step25 :
    word32Chunk25.foldl (fun acc a => a.applyPacked acc)
      word32State25 = word32State26 := by decide +kernel

private def word32Chunk26 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word32State27 : PackedMat2 :=
    ⟨⟨⟨((63897 : Dyadic) * half ^ 19),
        ((198499 : Dyadic) * half ^ 19)⟩,
       ⟨((-3355 : Dyadic) * half ^ 19),
        ((36051 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((187353 : Dyadic) * half ^ 19),
        ((-6637 : Dyadic) * half ^ 15)⟩,
       ⟨((35991 : Dyadic) * half ^ 19),
        ((213823 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((35991 : Dyadic) * half ^ 19),
        ((213823 : Dyadic) * half ^ 19)⟩,
       ⟨((187353 : Dyadic) * half ^ 19),
        ((-6637 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3355 : Dyadic) * half ^ 19),
        ((-36051 : Dyadic) * half ^ 17)⟩,
       ⟨((-63897 : Dyadic) * half ^ 19),
        ((-198499 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word32Step26 :
    word32Chunk26.foldl (fun acc a => a.applyPacked acc)
      word32State26 = word32State27 := by decide +kernel

private def word32Chunk27 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word32State28 : PackedMat2 :=
    ⟨⟨⟨((265857 : Dyadic) * half ^ 20),
        ((139233 : Dyadic) * half ^ 19)⟩,
       ⟨((477065 : Dyadic) * half ^ 20),
        ((-31259 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-596641 : Dyadic) * half ^ 20),
        ((-58173 : Dyadic) * half ^ 20)⟩,
       ⟨((-306367 : Dyadic) * half ^ 20),
        ((76565 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-364433 : Dyadic) * half ^ 20),
        ((-145137 : Dyadic) * half ^ 20)⟩,
       ⟨((-248087 : Dyadic) * half ^ 20),
        ((28219 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-309725 : Dyadic) * half ^ 20),
        ((26401 : Dyadic) * half ^ 18)⟩,
       ⟨((247207 : Dyadic) * half ^ 20),
        ((371461 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word32Step27 :
    word32Chunk27.foldl (fun acc a => a.applyPacked acc)
      word32State27 = word32State28 := by decide +kernel

private def word32Chunk28 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word32State29 : PackedMat2 :=
    ⟨⟨⟨((169127 : Dyadic) * half ^ 19),
        ((355289 : Dyadic) * half ^ 21)⟩,
       ⟨((-25757 : Dyadic) * half ^ 19),
        ((1061791 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((227939 : Dyadic) * half ^ 20),
        ((-624435 : Dyadic) * half ^ 21)⟩,
       ⟨((-230593 : Dyadic) * half ^ 20),
        ((-333281 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-239429 : Dyadic) * half ^ 19),
        ((-1327 : Dyadic) * half ^ 20)⟩,
       ⟨((-145577 : Dyadic) * half ^ 20),
        ((114633 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-177135 : Dyadic) * half ^ 18),
        ((-71685 : Dyadic) * half ^ 19)⟩,
       ⟨((353251 : Dyadic) * half ^ 20),
        ((-48721 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word32Step28 :
    word32Chunk28.foldl (fun acc a => a.applyPacked acc)
      word32State28 = word32State29 := by decide +kernel

private def word32Chunk29 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word32State30 : PackedMat2 :=
    ⟨⟨⟨((-631145 : Dyadic) * half ^ 20),
        ((5253 : Dyadic) * half ^ 15)⟩,
       ⟨((-476361 : Dyadic) * half ^ 21),
        ((449559 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-439619 : Dyadic) * half ^ 20),
        ((-418371 : Dyadic) * half ^ 21)⟩,
       ⟨((-509247 : Dyadic) * half ^ 21),
        ((-531523 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((509247 : Dyadic) * half ^ 21),
        ((531523 : Dyadic) * half ^ 21)⟩,
       ⟨((439619 : Dyadic) * half ^ 20),
        ((418371 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-476361 : Dyadic) * half ^ 21),
        ((449559 : Dyadic) * half ^ 21)⟩,
       ⟨((-631145 : Dyadic) * half ^ 20),
        ((5253 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word32Step29 :
    word32Chunk29.foldl (fun acc a => a.applyPacked acc)
      word32State29 = word32State30 := by decide +kernel

private def word32Chunk30 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word32State31 : PackedMat2 :=
    ⟨⟨⟨((1035593 : Dyadic) * half ^ 22),
        ((-3053707 : Dyadic) * half ^ 23)⟩,
       ⟨((-656533 : Dyadic) * half ^ 21),
        ((-1668823 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-220431 : Dyadic) * half ^ 21),
        ((-1481359 : Dyadic) * half ^ 23)⟩,
       ⟨((-2728035 : Dyadic) * half ^ 22),
        ((-116585 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-199743 : Dyadic) * half ^ 20),
        ((-3168897 : Dyadic) * half ^ 23)⟩,
       ⟨((-682387 : Dyadic) * half ^ 22),
        ((2287173 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((2361265 : Dyadic) * half ^ 22),
        ((277473 : Dyadic) * half ^ 23)⟩,
       ⟨((346221 : Dyadic) * half ^ 21),
        ((-2348659 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word32Step30 :
    word32Chunk30.foldl (fun acc a => a.applyPacked acc)
      word32State30 = word32State31 := by decide +kernel

private def word32Chunk31 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word32State32 : PackedMat2 :=
    ⟨⟨⟨((669781 : Dyadic) * half ^ 23),
        ((-1974765 : Dyadic) * half ^ 23)⟩,
       ⟨((-384003 : Dyadic) * half ^ 23),
        ((-5120043 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((795759 : Dyadic) * half ^ 23),
        ((-546253 : Dyadic) * half ^ 22)⟩,
       ⟨((-125245 : Dyadic) * half ^ 23),
        ((-901911 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-177829 : Dyadic) * half ^ 21),
        ((-230251 : Dyadic) * half ^ 22)⟩,
       ⟨((-362041 : Dyadic) * half ^ 20),
        ((335257 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1572639 : Dyadic) * half ^ 22),
        ((131723 : Dyadic) * half ^ 21)⟩,
       ⟨((886851 : Dyadic) * half ^ 20),
        ((-142889 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word32Step31 :
    word32Chunk31.foldl (fun acc a => a.applyPacked acc)
      word32State31 = word32State32 := by decide +kernel

private def word32Chunk32 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word32State33 : PackedMat2 :=
    ⟨⟨⟨((5308865 : Dyadic) * half ^ 24),
        ((-691405 : Dyadic) * half ^ 22)⟩,
       ⟨((-7662309 : Dyadic) * half ^ 24),
        ((-330193 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((3452481 : Dyadic) * half ^ 24),
        ((-4071163 : Dyadic) * half ^ 24)⟩,
       ⟨((11188735 : Dyadic) * half ^ 24),
        ((1663973 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((3452481 : Dyadic) * half ^ 24),
        ((-4071163 : Dyadic) * half ^ 24)⟩,
       ⟨((-11188735 : Dyadic) * half ^ 24),
        ((-1663973 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-5308865 : Dyadic) * half ^ 24),
        ((691405 : Dyadic) * half ^ 22)⟩,
       ⟨((-7662309 : Dyadic) * half ^ 24),
        ((-330193 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word32Step32 :
    word32Chunk32.foldl (fun acc a => a.applyPacked acc)
      word32State32 = word32State33 := by decide +kernel

private def word32Chunk33 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word32State34 : PackedMat2 :=
    ⟨⟨⟨((-3604067 : Dyadic) * half ^ 25),
        ((1380755 : Dyadic) * half ^ 24)⟩,
       ⟨((5074511 : Dyadic) * half ^ 25),
        ((-17748537 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-17886213 : Dyadic) * half ^ 25),
        ((-4697079 : Dyadic) * half ^ 25)⟩,
       ⟨((2694035 : Dyadic) * half ^ 25),
        ((2970425 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((10637929 : Dyadic) * half ^ 25),
        ((2572531 : Dyadic) * half ^ 23)⟩,
       ⟨((1243771 : Dyadic) * half ^ 25),
        ((-7596089 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((20510047 : Dyadic) * half ^ 25),
        ((-4339289 : Dyadic) * half ^ 25)⟩,
       ⟨((14987027 : Dyadic) * half ^ 25),
        ((-367611 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word32Step33 :
    word32Chunk33.foldl (fun acc a => a.applyPacked acc)
      word32State33 = word32State34 := by decide +kernel

private def word32Chunk34 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word32State35 : PackedMat2 :=
    ⟨⟨⟨((9167361 : Dyadic) * half ^ 25),
        ((18841549 : Dyadic) * half ^ 26)⟩,
       ⟨((-18203553 : Dyadic) * half ^ 25),
        ((13776871 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-3923065 : Dyadic) * half ^ 24),
        ((-21065553 : Dyadic) * half ^ 26)⟩,
       ⟨((-692439 : Dyadic) * half ^ 22),
        ((15745493 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((692439 : Dyadic) * half ^ 22),
        ((-15745493 : Dyadic) * half ^ 26)⟩,
       ⟨((3923065 : Dyadic) * half ^ 24),
        ((21065553 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-18203553 : Dyadic) * half ^ 25),
        ((13776871 : Dyadic) * half ^ 26)⟩,
       ⟨((9167361 : Dyadic) * half ^ 25),
        ((18841549 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word32Step34 :
    word32Chunk34.foldl (fun acc a => a.applyPacked acc)
      word32State34 = word32State35 := by decide +kernel

private def word32Chunk35 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word32State36 : PackedMat2 :=
    ⟨⟨⟨((17108043 : Dyadic) * half ^ 26),
        ((-20992999 : Dyadic) * half ^ 27)⟩,
       ⟨((25763127 : Dyadic) * half ^ 25),
        ((17094039 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-11611717 : Dyadic) * half ^ 25),
        ((16790313 : Dyadic) * half ^ 27)⟩,
       ⟨((4200713 : Dyadic) * half ^ 26),
        ((-31355139 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-7282413 : Dyadic) * half ^ 26),
        ((-19022721 : Dyadic) * half ^ 27)⟩,
       ⟨((12036363 : Dyadic) * half ^ 25),
        ((-27424147 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((243685 : Dyadic) * half ^ 23),
        ((-68634297 : Dyadic) * half ^ 27)⟩,
       ⟨((19043519 : Dyadic) * half ^ 26),
        ((34418211 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word32Step35 :
    word32Chunk35.foldl (fun acc a => a.applyPacked acc)
      word32State35 = word32State36 := by decide +kernel

private def word32Chunk36 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word32State37 : PackedMat2 :=
    ⟨⟨⟨((-94960229 : Dyadic) * half ^ 27),
        ((-12385493 : Dyadic) * half ^ 26)⟩,
       ⟨((-12294965 : Dyadic) * half ^ 27),
        ((390389 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((45044927 : Dyadic) * half ^ 27),
        ((-40746809 : Dyadic) * half ^ 27)⟩,
       ⟨((-15663041 : Dyadic) * half ^ 27),
        ((31770471 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-45044927 : Dyadic) * half ^ 27),
        ((40746809 : Dyadic) * half ^ 27)⟩,
       ⟨((-15663041 : Dyadic) * half ^ 27),
        ((31770471 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-94960229 : Dyadic) * half ^ 27),
        ((-12385493 : Dyadic) * half ^ 26)⟩,
       ⟨((12294965 : Dyadic) * half ^ 27),
        ((-390389 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word32Step36 :
    word32Chunk36.foldl (fun acc a => a.applyPacked acc)
      word32State36 = word32State37 := by decide +kernel

private def word32Chunk37 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word32State38 : PackedMat2 :=
    ⟨⟨⟨((-90211653 : Dyadic) * half ^ 28),
        ((-55865305 : Dyadic) * half ^ 27)⟩,
       ⟨((-125967579 : Dyadic) * half ^ 28),
        ((58870011 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((39436665 : Dyadic) * half ^ 28),
        ((-56264781 : Dyadic) * half ^ 28)⟩,
       ⟨((6938937 : Dyadic) * half ^ 28),
        ((-16025327 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-6938937 : Dyadic) * half ^ 28),
        ((16025327 : Dyadic) * half ^ 26)⟩,
       ⟨((-39436665 : Dyadic) * half ^ 28),
        ((56264781 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-125967579 : Dyadic) * half ^ 28),
        ((58870011 : Dyadic) * half ^ 28)⟩,
       ⟨((-90211653 : Dyadic) * half ^ 28),
        ((-55865305 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word32Step37 :
    word32Chunk37.foldl (fun acc a => a.applyPacked acc)
      word32State37 = word32State38 := by decide +kernel

private def word32Chunk38 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word32State39 : PackedMat2 :=
    ⟨⟨⟨((41486175 : Dyadic) * half ^ 27),
        ((47550761 : Dyadic) * half ^ 29)⟩,
       ⟨((-1558825 : Dyadic) * half ^ 25),
        ((-294939101 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-45699837 : Dyadic) * half ^ 28),
        ((28525337 : Dyadic) * half ^ 29)⟩,
       ⟨((-129234491 : Dyadic) * half ^ 28),
        ((48902291 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-129234491 : Dyadic) * half ^ 28),
        ((48902291 : Dyadic) * half ^ 29)⟩,
       ⟨((-45699837 : Dyadic) * half ^ 28),
        ((28525337 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((1558825 : Dyadic) * half ^ 25),
        ((294939101 : Dyadic) * half ^ 29)⟩,
       ⟨((-41486175 : Dyadic) * half ^ 27),
        ((-47550761 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word32Step38 :
    word32Chunk38.foldl (fun acc a => a.applyPacked acc)
      word32State38 = word32State39 := by decide +kernel

private def word32Chunk39 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word32State40 : PackedMat2 :=
    ⟨⟨⟨((-14245655 : Dyadic) * half ^ 28),
        ((391733581 : Dyadic) * half ^ 30)⟩,
       ⟨((-73951057 : Dyadic) * half ^ 29),
        ((441516949 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((177216451 : Dyadic) * half ^ 29),
        ((301046127 : Dyadic) * half ^ 30)⟩,
       ⟨((19638059 : Dyadic) * half ^ 28),
        ((-242862043 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-14546021 : Dyadic) * half ^ 28),
        ((-216492569 : Dyadic) * half ^ 30)⟩,
       ⟨((-271954085 : Dyadic) * half ^ 29),
        ((-137940333 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((416625265 : Dyadic) * half ^ 29),
        ((-102442367 : Dyadic) * half ^ 30)⟩,
       ⟨((-6222921 : Dyadic) * half ^ 27),
        ((45459747 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word32Step39 :
    word32Chunk39.foldl (fun acc a => a.applyPacked acc)
      word32State39 = word32State40 := by decide +kernel

private def word32Chunk40 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word32State41 : PackedMat2 :=
    ⟨⟨⟨((53301065 : Dyadic) * half ^ 27),
        ((-127818763 : Dyadic) * half ^ 30)⟩,
       ⟨((58952297 : Dyadic) * half ^ 28),
        ((-14303665 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((23477369 : Dyadic) * half ^ 27),
        ((519405947 : Dyadic) * half ^ 30)⟩,
       ⟨((-47068451 : Dyadic) * half ^ 29),
        ((96416493 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((23477369 : Dyadic) * half ^ 27),
        ((519405947 : Dyadic) * half ^ 30)⟩,
       ⟨((47068451 : Dyadic) * half ^ 29),
        ((-96416493 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-53301065 : Dyadic) * half ^ 27),
        ((127818763 : Dyadic) * half ^ 30)⟩,
       ⟨((58952297 : Dyadic) * half ^ 28),
        ((-14303665 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word32Step40 :
    word32Chunk40.foldl (fun acc a => a.applyPacked acc)
      word32State40 = word32State41 := by decide +kernel

private def word32Chunk41 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word32State42 : PackedMat2 :=
    ⟨⟨⟨((-573610189 : Dyadic) * half ^ 31),
        ((385565853 : Dyadic) * half ^ 30)⟩,
       ⟨((128310141 : Dyadic) * half ^ 31),
        ((-153768551 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-386350595 : Dyadic) * half ^ 31),
        ((-636275229 : Dyadic) * half ^ 31)⟩,
       ⟨((1422836961 : Dyadic) * half ^ 31),
        ((75986835 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((788248899 : Dyadic) * half ^ 31),
        ((452296889 : Dyadic) * half ^ 30)⟩,
       ⟨((-484301559 : Dyadic) * half ^ 31),
        ((518243183 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((924900257 : Dyadic) * half ^ 31),
        ((-350960165 : Dyadic) * half ^ 31)⟩,
       ⟨((-617363155 : Dyadic) * half ^ 31),
        ((27831253 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word32Step41 :
    word32Chunk41.foldl (fun acc a => a.applyPacked acc)
      word32State41 = word32State42 := by decide +kernel

private def word32Chunk42 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word32State43 : PackedMat2 :=
    ⟨⟨⟨((3123003 : Dyadic) * half ^ 25),
        ((92003525 : Dyadic) * half ^ 31)⟩,
       ⟨((-290975703 : Dyadic) * half ^ 31),
        ((936458549 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-209515745 : Dyadic) * half ^ 29),
        ((-123163935 : Dyadic) * half ^ 30)⟩,
       ⟨((1374817761 : Dyadic) * half ^ 31),
        ((34666027 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((211661843 : Dyadic) * half ^ 31),
        ((-536754781 : Dyadic) * half ^ 32)⟩,
       ⟨((280993897 : Dyadic) * half ^ 31),
        ((2212880741 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((514231037 : Dyadic) * half ^ 30),
        ((-91103511 : Dyadic) * half ^ 32)⟩,
       ⟨((-52778439 : Dyadic) * half ^ 27),
        ((490847895 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word32Step42 :
    word32Chunk42.foldl (fun acc a => a.applyPacked acc)
      word32State42 = word32State43 := by decide +kernel

private def word32Chunk43 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word32State44 : PackedMat2 :=
    ⟨⟨⟨((-1189438793 : Dyadic) * half ^ 31),
        ((1149915273 : Dyadic) * half ^ 32)⟩,
       ⟨((1825748955 : Dyadic) * half ^ 32),
        ((1596397307 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-5406285 : Dyadic) * half ^ 31),
        ((94673235 : Dyadic) * half ^ 29)⟩,
       ⟨((368950091 : Dyadic) * half ^ 32),
        ((-463270677 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((368950091 : Dyadic) * half ^ 32),
        ((-463270677 : Dyadic) * half ^ 32)⟩,
       ⟨((-5406285 : Dyadic) * half ^ 31),
        ((94673235 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-1825748955 : Dyadic) * half ^ 32),
        ((-1596397307 : Dyadic) * half ^ 32)⟩,
       ⟨((1189438793 : Dyadic) * half ^ 31),
        ((-1149915273 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word32Step43 :
    word32Chunk43.foldl (fun acc a => a.applyPacked acc)
      word32State43 = word32State44 := by decide +kernel

private def word32Chunk44 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word32State45 : PackedMat2 :=
    ⟨⟨⟨((384098397 : Dyadic) * half ^ 32),
        ((-7592412265 : Dyadic) * half ^ 34)⟩,
       ⟨((2034573585 : Dyadic) * half ^ 33),
        ((5571565795 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1600490911 : Dyadic) * half ^ 33),
        ((1458044845 : Dyadic) * half ^ 34)⟩,
       ⟨((-245435945 : Dyadic) * half ^ 32),
        ((6457298483 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-247354479 : Dyadic) * half ^ 29),
        ((2091362801 : Dyadic) * half ^ 34)⟩,
       ⟨((2499626819 : Dyadic) * half ^ 33),
        ((1109619021 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1010423235 : Dyadic) * half ^ 33),
        ((2802770379 : Dyadic) * half ^ 34)⟩,
       ⟨((-3290994515 : Dyadic) * half ^ 32),
        ((-1266376791 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word32Step44 :
    word32Chunk44.foldl (fun acc a => a.applyPacked acc)
      word32State44 = word32State45 := by decide +kernel

private def word32Chunk45 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word32State46 : PackedMat2 :=
    ⟨⟨⟨((840435819 : Dyadic) * half ^ 33),
        ((-6226285241 : Dyadic) * half ^ 34)⟩,
       ⟨((3442566295 : Dyadic) * half ^ 33),
        ((-466022175 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1929237939 : Dyadic) * half ^ 33),
        ((-4946693409 : Dyadic) * half ^ 34)⟩,
       ⟨((873781631 : Dyadic) * half ^ 31),
        ((2572834785 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1929237939 : Dyadic) * half ^ 33),
        ((-4946693409 : Dyadic) * half ^ 34)⟩,
       ⟨((-873781631 : Dyadic) * half ^ 31),
        ((-2572834785 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-840435819 : Dyadic) * half ^ 33),
        ((6226285241 : Dyadic) * half ^ 34)⟩,
       ⟨((3442566295 : Dyadic) * half ^ 33),
        ((-466022175 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word32Step45 :
    word32Chunk45.foldl (fun acc a => a.applyPacked acc)
      word32State45 = word32State46 := by decide +kernel

private def word32Chunk46 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word32State47 : PackedMat2 :=
    ⟨⟨⟨((-19138726911 : Dyadic) * half ^ 35),
        ((8037280451 : Dyadic) * half ^ 35)⟩,
       ⟨((-10275580041 : Dyadic) * half ^ 35),
        ((-226760309 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-9725310275 : Dyadic) * half ^ 35),
        ((-2785097903 : Dyadic) * half ^ 34)⟩,
       ⟨((19444055909 : Dyadic) * half ^ 35),
        ((4645690115 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((19444055909 : Dyadic) * half ^ 35),
        ((4645690115 : Dyadic) * half ^ 35)⟩,
       ⟨((-9725310275 : Dyadic) * half ^ 35),
        ((-2785097903 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((10275580041 : Dyadic) * half ^ 35),
        ((226760309 : Dyadic) * half ^ 33)⟩,
       ⟨((19138726911 : Dyadic) * half ^ 35),
        ((-8037280451 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word32Step46 :
    word32Chunk46.foldl (fun acc a => a.applyPacked acc)
      word32State46 = word32State47 := by decide +kernel

private def word32Chunk47 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word32State48 : PackedMat2 :=
    ⟨⟨⟨((3453042517 : Dyadic) * half ^ 35),
        ((-11438687895 : Dyadic) * half ^ 35)⟩,
       ⟨((-2806874777 : Dyadic) * half ^ 34),
        ((416487027 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-20430013781 : Dyadic) * half ^ 35),
        ((-7639020813 : Dyadic) * half ^ 35)⟩,
       ⟨((-4893164239 : Dyadic) * half ^ 34),
        ((10955570277 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-414568683 : Dyadic) * half ^ 32),
        ((30216342259 : Dyadic) * half ^ 36)⟩,
       ⟨((9297295545 : Dyadic) * half ^ 34),
        ((10643685303 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-9772739787 : Dyadic) * half ^ 35),
        ((-2160707037 : Dyadic) * half ^ 36)⟩,
       ⟨((-13104636003 : Dyadic) * half ^ 35),
        ((9066792071 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word32Step47 :
    word32Chunk47.foldl (fun acc a => a.applyPacked acc)
      word32State47 = word32State48 := by decide +kernel

private def word32Chunk48 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word32State49 : PackedMat2 :=
    ⟨⟨⟨((14893609397 : Dyadic) * half ^ 35),
        ((-4478333235 : Dyadic) * half ^ 36)⟩,
       ⟨((20735342779 : Dyadic) * half ^ 36),
        ((20321991379 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-22098266187 : Dyadic) * half ^ 35),
        ((1264384611 : Dyadic) * half ^ 34)⟩,
       ⟨((4003312283 : Dyadic) * half ^ 36),
        ((-16101842465 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((4003312283 : Dyadic) * half ^ 36),
        ((-16101842465 : Dyadic) * half ^ 36)⟩,
       ⟨((-22098266187 : Dyadic) * half ^ 35),
        ((1264384611 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-20735342779 : Dyadic) * half ^ 36),
        ((-20321991379 : Dyadic) * half ^ 36)⟩,
       ⟨((-14893609397 : Dyadic) * half ^ 35),
        ((4478333235 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word32Step48 :
    word32Chunk48.foldl (fun acc a => a.applyPacked acc)
      word32State48 = word32State49 := by decide +kernel

private def word32Chunk49 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word32State50 : PackedMat2 :=
    ⟨⟨⟨((-20368156635 : Dyadic) * half ^ 36),
        ((-21262765261 : Dyadic) * half ^ 38)⟩,
       ⟨((91590582461 : Dyadic) * half ^ 37),
        ((-15685825569 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-9731893539 : Dyadic) * half ^ 37),
        ((-106711941391 : Dyadic) * half ^ 38)⟩,
       ⟨((-25799946345 : Dyadic) * half ^ 36),
        ((9069825439 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((6102632247 : Dyadic) * half ^ 34),
        ((61331786229 : Dyadic) * half ^ 38)⟩,
       ⟨((57890883415 : Dyadic) * half ^ 37),
        ((-41867999151 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-18474295415 : Dyadic) * half ^ 37),
        ((50854269191 : Dyadic) * half ^ 38)⟩,
       ⟨((-1394234923 : Dyadic) * half ^ 36),
        ((-132326895731 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word32Step49 :
    word32Chunk49.foldl (fun acc a => a.applyPacked acc)
      word32State49 = word32State50 := by decide +kernel

private def word32Chunk50 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word32State51 : PackedMat2 :=
    ⟨⟨⟨((-7656681879 : Dyadic) * half ^ 35),
        ((-37428313205 : Dyadic) * half ^ 38)⟩,
       ⟨((-11672561325 : Dyadic) * half ^ 36),
        ((67157585263 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((284988545 : Dyadic) * half ^ 31),
        ((-22109719043 : Dyadic) * half ^ 38)⟩,
       ⟨((-20699190685 : Dyadic) * half ^ 37),
        ((-1806050719 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((93477526973 : Dyadic) * half ^ 38),
        ((38938457565 : Dyadic) * half ^ 38)⟩,
       ⟨((137696965059 : Dyadic) * half ^ 38),
        ((2459923805 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((171743483731 : Dyadic) * half ^ 38),
        ((3640802433 : Dyadic) * half ^ 37)⟩,
       ⟨((96886857321 : Dyadic) * half ^ 38),
        ((-26985925083 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word32Step50 :
    word32Chunk50.foldl (fun acc a => a.applyPacked acc)
      word32State50 = word32State51 := by decide +kernel

private def word32Chunk51 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word32State52 : PackedMat2 :=
    ⟨⟨⟨((-121643908083 : Dyadic) * half ^ 39),
        ((-234507083123 : Dyadic) * half ^ 39)⟩,
       ⟨((69679920961 : Dyadic) * half ^ 39),
        ((-43289241155 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-174564540447 : Dyadic) * half ^ 39),
        ((72392087455 : Dyadic) * half ^ 38)⟩,
       ⟨((-291582815593 : Dyadic) * half ^ 39),
        ((-9536250247 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-291582815593 : Dyadic) * half ^ 39),
        ((-9536250247 : Dyadic) * half ^ 39)⟩,
       ⟨((-174564540447 : Dyadic) * half ^ 39),
        ((72392087455 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-69679920961 : Dyadic) * half ^ 39),
        ((43289241155 : Dyadic) * half ^ 38)⟩,
       ⟨((121643908083 : Dyadic) * half ^ 39),
        ((234507083123 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word32Step51 :
    word32Chunk51.foldl (fun acc a => a.applyPacked acc)
      word32State51 = word32State52 := by decide +kernel

private def word32Chunk52 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word32State53 : PackedMat2 :=
    ⟨⟨⟨((-51892306425 : Dyadic) * half ^ 36),
        ((-11150419005 : Dyadic) * half ^ 38)⟩,
       ⟨((-234682706575 : Dyadic) * half ^ 39),
        ((-5010746813 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((127867811113 : Dyadic) * half ^ 38),
        ((-39224903945 : Dyadic) * half ^ 39)⟩,
       ⟨((-35996566429 : Dyadic) * half ^ 39),
        ((10963555305 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-4629317275 : Dyadic) * half ^ 39),
        ((-219739055797 : Dyadic) * half ^ 40)⟩,
       ⟨((83079125165 : Dyadic) * half ^ 39),
        ((-291732188655 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-8080582909 : Dyadic) * half ^ 37),
        ((-649821157975 : Dyadic) * half ^ 40)⟩,
       ⟨((-47966189 : Dyadic) * half ^ 31),
        ((-180455744825 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word32Step52 :
    word32Chunk52.foldl (fun acc a => a.applyPacked acc)
      word32State52 = word32State53 := by decide +kernel

private def word32Chunk53 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word32State54 : PackedMat2 :=
    ⟨⟨⟨((381806191365 : Dyadic) * half ^ 40),
        ((-37361273663 : Dyadic) * half ^ 41)⟩,
       ⟨((-124387321445 : Dyadic) * half ^ 39),
        ((-586671404303 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-358978316181 : Dyadic) * half ^ 39),
        ((237871878085 : Dyadic) * half ^ 41)⟩,
       ⟨((531044212505 : Dyadic) * half ^ 40),
        ((73623792719 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-358978316181 : Dyadic) * half ^ 39),
        ((237871878085 : Dyadic) * half ^ 41)⟩,
       ⟨((-531044212505 : Dyadic) * half ^ 40),
        ((-73623792719 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-381806191365 : Dyadic) * half ^ 40),
        ((37361273663 : Dyadic) * half ^ 41)⟩,
       ⟨((-124387321445 : Dyadic) * half ^ 39),
        ((-586671404303 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word32Step53 :
    word32Chunk53.foldl (fun acc a => a.applyPacked acc)
      word32State53 = word32State54 := by decide +kernel

private def word32Chunk54 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word32State55 : PackedMat2 :=
    ⟨⟨⟨((-506543263135 : Dyadic) * half ^ 41),
        ((794077832559 : Dyadic) * half ^ 41)⟩,
       ⟨((-735909425443 : Dyadic) * half ^ 41),
        ((-304267176081 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-674978525785 : Dyadic) * half ^ 41),
        ((-368043945945 : Dyadic) * half ^ 40)⟩,
       ⟨((-893107482533 : Dyadic) * half ^ 41),
        ((89161112349 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((546366170643 : Dyadic) * half ^ 40),
        ((-54532239187 : Dyadic) * half ^ 40)⟩,
       ⟨((-189721721247 : Dyadic) * half ^ 40),
        ((-784043004159 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((2145205095 : Dyadic) * half ^ 32),
        ((57341540577 : Dyadic) * half ^ 40)⟩,
       ⟨((-244905328239 : Dyadic) * half ^ 40),
        ((621226344289 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word32Step54 :
    word32Chunk54.foldl (fun acc a => a.applyPacked acc)
      word32State54 = word32State55 := by decide +kernel

private def word32Chunk55 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word32State56 : PackedMat2 :=
    ⟨⟨⟨((2295904069127 : Dyadic) * half ^ 42),
        ((515503273363 : Dyadic) * half ^ 41)⟩,
       ⟨((547531279933 : Dyadic) * half ^ 42),
        ((-743337355335 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((130509043355 : Dyadic) * half ^ 42),
        ((363148797845 : Dyadic) * half ^ 42)⟩,
       ⟨((-916012769507 : Dyadic) * half ^ 42),
        ((1747230469081 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((130509043355 : Dyadic) * half ^ 42),
        ((363148797845 : Dyadic) * half ^ 42)⟩,
       ⟨((916012769507 : Dyadic) * half ^ 42),
        ((-1747230469081 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-2295904069127 : Dyadic) * half ^ 42),
        ((-515503273363 : Dyadic) * half ^ 41)⟩,
       ⟨((547531279933 : Dyadic) * half ^ 42),
        ((-743337355335 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word32Step55 :
    word32Chunk55.foldl (fun acc a => a.applyPacked acc)
      word32State55 = word32State56 := by decide +kernel

private def word32Chunk56 : List Letter := [.s, .t, .h, .t, .h]
private def word32State57 : PackedMat2 :=
    ⟨⟨⟨((3164088020557 : Dyadic) * half ^ 42),
        ((1745080832737 : Dyadic) * half ^ 43)⟩,
       ⟨((1559127576211 : Dyadic) * half ^ 42),
        ((-2204939368297 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-257948859903 : Dyadic) * half ^ 41),
        ((729589552147 : Dyadic) * half ^ 43)⟩,
       ⟨((137347871331 : Dyadic) * half ^ 39),
        ((-1553913779195 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((257948859903 : Dyadic) * half ^ 41),
        ((-729589552147 : Dyadic) * half ^ 43)⟩,
       ⟨((137347871331 : Dyadic) * half ^ 39),
        ((-1553913779195 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((3164088020557 : Dyadic) * half ^ 42),
        ((1745080832737 : Dyadic) * half ^ 43)⟩,
       ⟨((-1559127576211 : Dyadic) * half ^ 42),
        ((2204939368297 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word32Step56 :
    word32Chunk56.foldl (fun acc a => a.applyPacked acc)
      word32State56 = word32State57 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word32_check : check word32 32 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word32 = word32State57.toMatrix := by
    unfold evalRingPacked
    change ((
      word32Chunk0 ++ word32Chunk1 ++ word32Chunk2 ++ word32Chunk3 ++
      word32Chunk4 ++ word32Chunk5 ++ word32Chunk6 ++ word32Chunk7 ++
      word32Chunk8 ++ word32Chunk9 ++ word32Chunk10 ++ word32Chunk11 ++
      word32Chunk12 ++ word32Chunk13 ++ word32Chunk14 ++ word32Chunk15 ++
      word32Chunk16 ++ word32Chunk17 ++ word32Chunk18 ++ word32Chunk19 ++
      word32Chunk20 ++ word32Chunk21 ++ word32Chunk22 ++ word32Chunk23 ++
      word32Chunk24 ++ word32Chunk25 ++ word32Chunk26 ++ word32Chunk27 ++
      word32Chunk28 ++ word32Chunk29 ++ word32Chunk30 ++ word32Chunk31 ++
      word32Chunk32 ++ word32Chunk33 ++ word32Chunk34 ++ word32Chunk35 ++
      word32Chunk36 ++ word32Chunk37 ++ word32Chunk38 ++ word32Chunk39 ++
      word32Chunk40 ++ word32Chunk41 ++ word32Chunk42 ++ word32Chunk43 ++
      word32Chunk44 ++ word32Chunk45 ++ word32Chunk46 ++ word32Chunk47 ++
      word32Chunk48 ++ word32Chunk49 ++ word32Chunk50 ++ word32Chunk51 ++
      word32Chunk52 ++ word32Chunk53 ++ word32Chunk54 ++ word32Chunk55 ++
      word32Chunk56
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word32Step0, word32Step1, word32Step2, word32Step3, word32Step4,
      word32Step5, word32Step6, word32Step7, word32Step8, word32Step9,
      word32Step10, word32Step11, word32Step12, word32Step13, word32Step14,
      word32Step15, word32Step16, word32Step17, word32Step18, word32Step19,
      word32Step20, word32Step21, word32Step22, word32Step23, word32Step24,
      word32Step25, word32Step26, word32Step27, word32Step28, word32Step29,
      word32Step30, word32Step31, word32Step32, word32Step33, word32Step34,
      word32Step35, word32Step36, word32Step37, word32Step38, word32Step39,
      word32Step40, word32Step41, word32Step42, word32Step43, word32Step44,
      word32Step45, word32Step46, word32Step47, word32Step48, word32Step49,
      word32Step50, word32Step51, word32Step52, word32Step53, word32Step54,
      word32Step55, word32Step56]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end

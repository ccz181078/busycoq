From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE0LB_1RA1RF_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition N n := [1;0]^^n++[0].
Fixpoint Ns ls :=
match ls with
| [] => []
| n::ls0 => Ns ls0 <+ N n
end.

Definition S1 l a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a1 <* Ns [8;8;12;1;5] <* (Ns [5;0])^^a0 <* Ns [5;2;5;0;4;1;3;2;2;4;0] <* (Ns [5;0])^^a <* Ns [4;0;4;1;3;2;2;4;0] <* (Ns [3;1])^^b <* Ns [5;11;9;4;2] <* (Ns [2;3])^^c <* Ns [0;1] {{A}}> 0inf)%nat.

Lemma init:
  exists l, c0 -->* S1 l 55 49 49 1 0.
Proof.
  eexists.
  stepn' 6328236%N.
Qed.

Open Scope string.

Lemma Inc1 l a1 a0 a b c:
  S1 l a1 a0 (1+a) b c -->*
  S1 l a1 a0 a (1+b) (1+c).
Proof.
  unfold S1.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs1 l a1 a0 a b c:
  S1 l a1 a0 a b c -->*
  S1 l a1 a0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc1.
Qed.

Definition S2 l a2 a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a2 <* Ns [8;8;12;1;5] <* (Ns [5;0])^^a1 <* Ns [3;1;3;2;2;4;0] <* (Ns [2;2]^^a0) <* Ns [3;1;3;3;3;3;2] <* (Ns [2;2])^^a <* Ns [6;10;10;3;3] <* (Ns [3;2])^^b <* Ns [5;2] <* (Ns [2;3])^^c <* Ns [0;1] {{A}}> 0inf)%nat.

Lemma Inc2 l a2 a1 a0 a b c:
  S2 l a2 (1+a1) a0 a b c -->*
  S2 l a2 a1 (1+a0) a b (1+c).
Proof.
  unfold S2.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs2 l a2 a1 a0 a b c:
  S2 l a2 a1 a0 a b c -->*
  S2 l a2 0 (a1+a0) a b (a1+c).
Proof.
  gen a0 c.
  ind a1 Inc2.
Qed.

Lemma Ov1 l a1 a0 b c:
  S1 l a1 (1+a0) 0 b c -->+
  S2 l a1 a0 1 (3+b) (2+c) 0.
Proof.
  unfold S1,S2.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Definition S3 l a2 a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a2 <* Ns [2;1;2;3] <* (Ns [1;2])^^a1 <* Ns [3;5;10;10;3;2;2;2] <* (Ns [2;2]^^a0) <* Ns [3;1;3;3;3;3;2] <* (Ns [2;2])^^a <* Ns [6;10;10;3;3] <* (Ns [3;2])^^b <* Ns [5;2] <* (Ns [2;3])^^c <* Ns [0;1] {{A}}> 0inf)%nat.

Lemma Inc3 l a2 a1 a0 a b c:
  S3 l (1+a2) a1 a0 a b c -->*
  S3 l a2 (1+a1) a0 a b (1+c).
Proof.
  unfold S3.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs3 l a2 a1 a0 a b c:
  S3 l a2 a1 a0 a b c -->*
  S3 l 0 (a2+a1) a0 a b (a2+c).
Proof.
  gen a1 c.
  ind a2 Inc3.
Qed.

Lemma Ov2 l a2 a0 a b c:
  S2 l (3+a2) 0 a0 a b c -->*
  S3 l a2 0 (3+a0) a b (4+c).
Proof.
  unfold S2,S3.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Ov3 {l a1 a0 a b c}:
  exists l',
  S3 l 0 a1 (3+a0) a (4+b) (5+c) -->*
  S1 l' a b c 1 0.
Proof.
  unfold S3,S1.
  exists ((Ns [4;0])^^a0 *> Ns [5;3;12;8;5;0;4;0] *> (Ns [3;0])^^(1+a1) *> Ns [4;0;4;0;4;2;4;1;4;0;3;1;2;3;0] *> l)%nat.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Definition S' '(l,a1,a0,a) := S1 l (7+a1) (2+a0) (4+a) 1 0.

Lemma BigStep l a1 a0 a:
  exists l',
  S' (l,a1,a0,a) -->+
  S' (l',1+a,a,a1+a0).
Proof.
  unfold S'.
  epose proof Ov3 as [l' Ov3].
  eexists.
  follow Incs1.
  follow10 Ov1.
  follow Incs2.
  follow Ov2.
  follow Incs3.
  cbn[Nat.add] in *.
  repeat (rewrite <-Nat.add_succ_comm || rewrite Nat.add_0_r).
  follow Ov3.
  fold Nat.add.
  eapply evstep_refl'.
  f_equal; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof init as [l0 I1].
  eapply multistep_nonhalt with (c':=S' (_,_,_,_)).
  1: apply I1.
  eapply progress_nonhalt_simple.
  intros [[[l a1] a0] a].
  epose proof (BigStep _ _ _ _) as [l1 I2].
  eexists (_,_,_,_).
  apply I2.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_1RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition N n := [1;0]^^n++[0].
Fixpoint Ns ls :=
match ls with
| [] => []
| n::ls0 => Ns ls0 <+ N n
end.

Definition S1 l a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a1 <* Ns [8;8;12;1;5] <* (Ns [5;0])^^a0 <* Ns [5;2;5;0;4;1;3;2;2;4;0] <* (Ns [5;0])^^a <* Ns [4;0;4;1;3;2;2;4;0] <* (Ns [3;1])^^b <* Ns [5;11;9;4;2] <* (Ns [2;3])^^c <* Ns [0;1] {{B}}> 0inf)%nat.

Lemma init:
  exists l, c0 -->* S1 l 39 33 75 1 0.
Proof.
  eexists.
  stepn' 5502455%N.
Qed.

Open Scope string.

Lemma Inc1 l a1 a0 a b c:
  S1 l a1 a0 (1+a) b c -->*
  S1 l a1 a0 a (1+b) (1+c).
Proof.
  unfold S1.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs1 l a1 a0 a b c:
  S1 l a1 a0 a b c -->*
  S1 l a1 a0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc1.
Qed.

Definition S2 l a2 a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a2 <* Ns [8;8;12;1;5] <* (Ns [5;0])^^a1 <* Ns [3;1;3;2;2;4;0] <* (Ns [2;2]^^a0) <* Ns [3;1;3;3;3;3;2] <* (Ns [2;2])^^a <* Ns [6;10;10;3;3] <* (Ns [3;2])^^b <* Ns [5;2] <* (Ns [2;3])^^c <* Ns [0;1] {{B}}> 0inf)%nat.

Lemma Inc2 l a2 a1 a0 a b c:
  S2 l a2 (1+a1) a0 a b c -->*
  S2 l a2 a1 (1+a0) a b (1+c).
Proof.
  unfold S2.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs2 l a2 a1 a0 a b c:
  S2 l a2 a1 a0 a b c -->*
  S2 l a2 0 (a1+a0) a b (a1+c).
Proof.
  gen a0 c.
  ind a1 Inc2.
Qed.

Lemma Ov1 l a1 a0 b c:
  S1 l a1 (1+a0) 0 b c -->+
  S2 l a1 a0 1 (3+b) (2+c) 0.
Proof.
  unfold S1,S2.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Definition S3 l a2 a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a2 <* Ns [2;1;2;3] <* (Ns [1;2])^^a1 <* Ns [3;5;10;10;3;2;2;2] <* (Ns [2;2]^^a0) <* Ns [3;1;3;3;3;3;2] <* (Ns [2;2])^^a <* Ns [6;10;10;3;3] <* (Ns [3;2])^^b <* Ns [5;2] <* (Ns [2;3])^^c <* Ns [0;1] {{B}}> 0inf)%nat.

Lemma Inc3 l a2 a1 a0 a b c:
  S3 l (1+a2) a1 a0 a b c -->*
  S3 l a2 (1+a1) a0 a b (1+c).
Proof.
  unfold S3.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs3 l a2 a1 a0 a b c:
  S3 l a2 a1 a0 a b c -->*
  S3 l 0 (a2+a1) a0 a b (a2+c).
Proof.
  gen a1 c.
  ind a2 Inc3.
Qed.

Lemma Ov2 l a2 a0 a b c:
  S2 l (3+a2) 0 a0 a b c -->*
  S3 l a2 0 (3+a0) a b (4+c).
Proof.
  unfold S2,S3.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Ov3 {l a1 a0 a b c}:
  exists l',
  S3 l 0 a1 (3+a0) a (4+b) (5+c) -->*
  S1 l' a b c 1 0.
Proof.
  unfold S3,S1.
  exists ((Ns [4;0])^^a0 *> Ns [5;3;12;8;5;0;4;0] *> (Ns [3;0])^^(1+a1) *> Ns [4;0;4;0;4;2;4;1;4;0;3;1;2;3;0] *> l)%nat.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Definition S' '(l,a1,a0,a) := S1 l (7+a1) (2+a0) (4+a) 1 0.

Lemma BigStep l a1 a0 a:
  exists l',
  S' (l,a1,a0,a) -->+
  S' (l',1+a,a,a1+a0).
Proof.
  unfold S'.
  epose proof Ov3 as [l' Ov3].
  eexists.
  follow Incs1.
  follow10 Ov1.
  follow Incs2.
  follow Ov2.
  follow Incs3.
  cbn[Nat.add] in *.
  repeat (rewrite <-Nat.add_succ_comm || rewrite Nat.add_0_r).
  follow Ov3.
  fold Nat.add.
  eapply evstep_refl'.
  f_equal; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof init as [l0 I1].
  eapply multistep_nonhalt with (c':=S' (_,_,_,_)).
  1: apply I1.
  eapply progress_nonhalt_simple.
  intros [[[l a1] a0] a].
  epose proof (BigStep _ _ _ _) as [l1 I2].
  eexists (_,_,_,_).
  apply I2.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0LC0LA_0LD0LA_1RE1RF_1RA0RD_1RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition N n := [1;0]^^n++[0].
Fixpoint Ns ls :=
match ls with
| [] => []
| n::ls0 => Ns ls0 <+ N n
end.

Definition S1 l a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a1 <* Ns [8;8;12;1;5] <* (Ns [5;0])^^a0 <* Ns [5;2;5;0;4;1;3;2;2;4;0] <* (Ns [5;0])^^a <* Ns [4;0;4;1;3;2;2;4;0] <* (Ns [3;1])^^b <* Ns [5;11;9;4;2] <* (Ns [2;3])^^c <* Ns [2] {{A}}> 0inf)%nat.

Lemma init:
  exists l, c0 -->* S1 l 55 49 49 1 0.
Proof.
  eexists.
  stepn' 13669814%N.
Qed.

Open Scope string.

Lemma Inc1 l a1 a0 a b c:
  S1 l a1 a0 (1+a) b c -->*
  S1 l a1 a0 a (1+b) (1+c).
Proof.
  unfold S1.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs1 l a1 a0 a b c:
  S1 l a1 a0 a b c -->*
  S1 l a1 a0 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc1.
Qed.

Definition S2 l a2 a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a2 <* Ns [8;8;12;1;5] <* (Ns [5;0])^^a1 <* Ns [3;1;3;2;2;4;0] <* (Ns [2;2]^^a0) <* Ns [3;1;3;3;3;3;2] <* (Ns [2;2])^^a <* Ns [6;10;10;3;3] <* (Ns [3;2])^^b <* Ns [5;2] <* (Ns [2;3])^^c <* Ns [2] {{A}}> 0inf)%nat.

Lemma Inc2 l a2 a1 a0 a b c:
  S2 l a2 (1+a1) a0 a b c -->*
  S2 l a2 a1 (1+a0) a b (1+c).
Proof.
  unfold S2.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs2 l a2 a1 a0 a b c:
  S2 l a2 a1 a0 a b c -->*
  S2 l a2 0 (a1+a0) a b (a1+c).
Proof.
  gen a0 c.
  ind a1 Inc2.
Qed.

Lemma Ov1 l a1 a0 b c:
  S1 l a1 (1+a0) 0 b c -->+
  S2 l a1 a0 1 (3+b) (2+c) 0.
Proof.
  unfold S1,S2.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Definition S3 l a2 a1 a0 a b c :=
  (l <* Ns [1;3;1;5;1;5;0;4;0;4;0;4;0] <* (Ns [0;4])^^a2 <* Ns [2;1;2;3] <* (Ns [1;2])^^a1 <* Ns [3;5;10;10;3;2;2;2] <* (Ns [2;2]^^a0) <* Ns [3;1;3;3;3;3;2] <* (Ns [2;2])^^a <* Ns [6;10;10;3;3] <* (Ns [3;2])^^b <* Ns [5;2] <* (Ns [2;3])^^c <* Ns [2] {{A}}> 0inf)%nat.

Lemma Inc3 l a2 a1 a0 a b c:
  S3 l (1+a2) a1 a0 a b c -->*
  S3 l a2 (1+a1) a0 a b (1+c).
Proof.
  unfold S3.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Incs3 l a2 a1 a0 a b c:
  S3 l a2 a1 a0 a b c -->*
  S3 l 0 (a2+a1) a0 a b (a2+c).
Proof.
  gen a1 c.
  ind a2 Inc3.
Qed.

Lemma Ov2 l a2 a0 a b c:
  S2 l (3+a2) 0 a0 a b c -->*
  S3 l a2 0 (3+a0) a b (4+c).
Proof.
  unfold S2,S3.
  pose (fun (s:string) =>
  if s=?"a2" then a2 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Lemma Ov3 {l a1 a0 a b c}:
  exists l',
  S3 l 0 a1 (3+a0) a (4+b) (5+c) -->*
  S1 l' a b c 1 0.
Proof.
  unfold S3,S1.
  exists ((Ns [4;0])^^a0 *> Ns [5;3;12;8;5;0;4;0] *> (Ns [3;0])^^(1+a1) *> Ns [4;0;4;0;4;2;4;1;4;0;3;1;2;3;0] *> l)%nat.
  pose (fun (s:string) =>
  if s=?"a1" then a1 else
  if s=?"a0" then a0 else
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O) as nmp.
  pose (fun (s:string) =>
  if s=?"l" then l else
  0inf) as smp.
  es_v3.
Qed.

Definition S' '(l,a1,a0,a) := S1 l (7+a1) (2+a0) (4+a) 1 0.

Lemma BigStep l a1 a0 a:
  exists l',
  S' (l,a1,a0,a) -->+
  S' (l',1+a,a,a1+a0).
Proof.
  unfold S'.
  epose proof Ov3 as [l' Ov3].
  eexists.
  follow Incs1.
  follow10 Ov1.
  follow Incs2.
  follow Ov2.
  follow Incs3.
  cbn[Nat.add] in *.
  repeat (rewrite <-Nat.add_succ_comm || rewrite Nat.add_0_r).
  follow Ov3.
  fold Nat.add.
  eapply evstep_refl'.
  f_equal; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof init as [l0 I1].
  eapply multistep_nonhalt with (c':=S' (_,_,_,_)).
  1: apply I1.
  eapply progress_nonhalt_simple.
  intros [[[l a1] a0] a].
  epose proof (BigStep _ _ _ _) as [l1 I2].
  eexists (_,_,_,_).
  apply I2.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1LF_0RD1RC_1LE0RA_1LB---_1LA1LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w4 := [0;1;0;1;1;1;1].
Notation w3 := [0;1;0;1;1;1].
Notation w43 := (w4++w3).
Notation w34 := (w3++w4).

Definition S1 a b c r :=
  0inf <{{B}} [1;1] *> [0;1;0]^^a *> w4^^b *> [0;0;1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a b (2+c) r -->*
  S1 (1+a) (1+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a b (n*2+c) r -->*
  S1 (n+a) (n+b) c r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c d e r :=
  0inf <{{B}} [1;1] *> [0;1;0]^^a *> w4^^b *> w3 *> w34^^c *> (w34++[1;1;1])^^d *> [0;1;1] *> w34^^e *> r.

Lemma Inc2 a b c d e r:
  S2 a (2+b) c d (1+e) r -->*
  S2 (2+a) b (1+c) (1+d) e r.
Proof.
  es.
Qed.

Lemma Incs2 n a b c d e r:
  S2 a (n*2+b) c d (n+e) r -->*
  S2 (n*2+a) b (n+c) (n+d) e r.
Proof.
  gen a b c d e.
  ind n Inc2.
Qed.

Lemma Ov12 a b r:
  S1 a a 0 ([0] *> w4 *> w34^^b *> r) -->+
  S2 (1+a) a 0 0 b r.
Proof.
  es.
Qed.

Lemma Ov21 a b r:
  exists r',
  S2 a 1 (1+b) (1+b) 0 (w3 *> [1;1;1] *> r) -->*
  S1 0 0 (1+a) ([0] *> w34^^(3+b) *> [1;1;1] *> r').
Proof.
  eexists.
  es.
Qed.

Definition S3 a b c d e r :=
  0inf <{{B}} [1;1] *> [0;1;0]^^a *> w4^^b *> w34^^c *> (w34++[1;1;1])^^d *> [0;1;1] *> w34^^e *> r.

Lemma Inc3 a b c d e r:
  S3 a (2+b) c d (1+e) r -->*
  S3 (2+a) b (1+c) (1+d) e r.
Proof.
  es.
Qed.

Lemma Incs3 n a b c d e r:
  S3 a (n*2+b) c d (n+e) r -->*
  S3 (n*2+a) b (n+c) (n+d) e r.
Proof.
  gen a b c d e.
  ind n Inc3.
Qed.

Lemma Ov13 a b r:
  S1 a a 1 ([0] *> w34^^(1+b) *> r) -->*
  S3 (2+a) a 0 1 b r.
Proof.
  es.
Qed.

Lemma Ov31 a b r:
  exists r',
  S3 a 1 b (1+b) 1 ([1;1;1] *> r) -->*
  S1 0 0 (1+a) ([0] *> w4 *> w34^^(1+b) *> [1;1;1] *> r').
Proof.
  eexists.
  es.
Qed.

Lemma Ov21' a b r:
  exists r',
  S2 a 0 (1+b) (1+b) 0 ([1;1;1]*>r) -->*
  S1 0 0 a ([0] *> w34^^(2+b) *> w3 *> [1;1;1] *> r').
Proof.
  eexists.
  es.
Qed.

Lemma Ov31' a b r:
  exists r',
  S3 a 0 b (1+b) 0 (w3 *> [1;1;1] *> r) -->*
  S1 0 0 a ([0] *> w43^^(1+b) *> [1;1;1] *> r').
Proof.
  eexists.
  es.
Qed.

Definition S' '(n,r) := S1 (3+n*2) (3+n*2) 0 ([0]*>w4*>w34^^(1+n)*>w3*>[1;1;1]*>r).

Lemma init:
  exists r,
  c0 -->* S' (7,r).
Proof.
  eexists.
  stepn' 408921%N.
Qed.

Ltac flia := repeat (lia||f_equal).

Ltac follow' H :=
  eapply evstep_trans; [|follow H]; [apply evstep_refl'; flia|].

Lemma BigStep n r:
  exists r',
  S' (n,r) -->+
  S' (1+n,r').
Proof.
  epose proof (Incs2 (1+n) _ 1 0 0 0 _) as I1.
  epose proof (Ov21 (6+n*4) n _) as [r2 I2].
  epose proof (Incs1 (3+n*2) 0 0 1 _) as I3.
  epose proof (Ov13 (3+n*2) (2+n) _) as I4.
  epose proof (Incs3 (1+n) _ 1 _ _ 1 _) as I5.
  epose proof (Ov31 (7+n*4) (1+n) _) as [r6 I6].
  epose proof (Incs1 (4+n*2) _ _ 0 _) as I7.
  epose proof (Ov12 (4+n*2) (2+n) _) as I8.
  epose proof (Incs2 (2+n) _ 0 _ _ 0 _) as I9.
  epose proof (Ov21' (9+n*4) (1+n) _) as [r10 I10].
  epose proof (Incs1 (4+n*2) _ _ 1 _) as I11.
  epose proof (Ov13 (4+n*2) (2+n) _) as I12.
  epose proof (Incs3 (2+n) _ 0 _ _ 0 _) as I13.
  epose proof (Ov31' (10+n*4) (2+n) _) as [r14 I14].
  epose proof (Incs1 (5+n*2) _ _ 0 _) as I15.
  exists r14.
  unfold S'.
  follow10 Ov12.
  follow' I1.
  follow' I2.
  follow' I3.
  follow' I4.
  follow' I5.
  follow' I6.
  follow' I7.
  apply progress_evstep in I8.
  follow' I8.
  follow' I9.
  follow' I10.
  follow' I11.
  follow' I12.
  follow' I13.
  follow' I14.
  follow' I15.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  epose proof init as [r' I1].
  eapply multistep_nonhalt.
  1: apply I1.
  eapply progress_nonhalt_simple.
  intros [n r].
  epose proof (BigStep n r) as [r0 I2].
  eexists (_,_).
  apply I2.
Qed.

End TM4.



(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md for numbering. *)

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_R2carry.v. *)
Module SOC23_R2carry.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0: forall l r n m,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0^^m *> rd1 *> r.
Hypothesis ROv2_1: forall l r n m,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.

Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC ((m*2+1)*2^i*2+1).
Proof. solve_rule ROv2_0. Qed.
Lemma RC2_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => 1<=len /\ n+m<k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbitS_cases m.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); arith.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_R2carry.

(* SOC23_R2carry.TM99 *)
Module TM99.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2carry.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_1LD0LC_1RB0RF_1RD0RB_1RA1LC").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{D}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 6 36 <| Counter.RC 1.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=D) (QR:=B) (len:=6) (k:=36) (n:=1%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM99.

(* SOC23_R2carry.TM128 *)
Module TM128.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2carry.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_0RF1LB_0LD---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 4 9 <| Counter.RC 1.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (len:=4) (k:=9) (n:=1%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM128.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_R2carry01.v. *)
Module SOC23_R2carry01.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3) |> [0;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0: forall l r n m,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0^^m *> rd1 *> r.
Hypothesis ROv2_1: forall l r n m,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.

Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 <| 0inf.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> RC 0.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC ((m*2+1)*2^i*2+1).
Proof. solve_rule ROv2_0. Qed.
Lemma RC2_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)+1) ((k*2+1)*2^(a*3+2)*2+1) <| RC 0.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2+1) |> RC' h ((2^h-1)*2+1).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2+1) with (2^len*2+((2^len-1)*2+1)) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => 1<=len /\ n+m<k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma append0_bounds len k s: k<2^len ->
  k*2<(k*2+1)*2^s<2^(len+1+s) /\
  (k*2+1)*2^s+1<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append0_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append0_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbitS_cases m.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); arith.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_R2carry01.

(* SOC23_R2carry01.TM16 *)
Module TM16.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2carry01.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LB_1RD0RA_1RC---_1RF0RA_1RA0RE").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3) |> [0;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 <| 0inf.
Proof. intros; st; sr_r; do 9 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 5 20 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (len:=5) (k:=20) (n:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM16.

(* SOC23_R2carry01.TM17 *)
Module TM17.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2carry01.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0RA_1LD1RA_0LE0LD_1RF0RC_1RE---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{E}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3) |> [0;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 <| 0inf.
Proof. intros; st; sr_r; do 9 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 7 73 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=E) (QR:=C) (len:=7) (k:=73) (n:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM17.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_R2half.v. *)
Module SOC23_R2half.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0_0: forall l r n m,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^(m+1) *> rd1 *> r.
Hypothesis ROv2_0_1: forall l r n m,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.
Hypothesis ROv2_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 |> r.

Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (((m*2+1)*2^i-1)*2) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 (i+1) ((2^(i+1)-1)*2) m.
Proof. solve_rule ROv2_0_0. Qed.
Lemma RC2_Ov_0_1 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (((m*2+1)*2^i-1)*2+1) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_0_1. Qed.
Lemma RC2_Ov_1 len k a m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 m -->+
  LC (len+1+(a*3+2)+1) ((k*2+1)*2^(a*3+2)*2+1) |> RC m.
Proof. solve_rule ROv2_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => 1<=len /\ n+m<k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma append_end0_bounds len k s: k<2^len ->
  (k*2+1)*2^s*2+1<2^(len+1+s+1) /\
  (k*2+1)*2^s*2+1+k+1<2^(len+1+s+1)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + divmod2_cases m; lowbitS_cases n'0.
      * eexists (cfgR1 _ _ _ _ _); split; [apply RC2_Ov_0_0; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)).
        pose proof (split_bound_v2 x (i+1)); arith.
      * eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_0_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_1; lia|].
      cbn [P]; pose proof (append_end0_bounds len k (n'*3+2) ltac:(lia)); lia.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_R2half.

(* SOC23_R2half.TM108 *)
Module TM108.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2half.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0RB---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_0_1 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 |> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 2 0 <| Counter.RC 6.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=A) (QR:=B) (len:=2) (k:=0%nat) (n:=6).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0_0|exact ROv2_0_1|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM108.

(* SOC23_R2half.TM109 *)
Module TM109.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2half.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_1RF1LB_0RA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_0_1 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 |> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 4 9 <| Counter.RC 1.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (len:=4) (k:=9) (n:=1%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0_0|exact ROv2_0_1|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM109.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_R2parity.v. *)
Module SOC23_R2parity.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0_0: forall l r n m,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^(m+1) *> rd1 *> r.
Hypothesis ROv2_0_1: forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0 *> r.
Hypothesis ROv2_1_0: forall l r n m,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd0^^(m+1) *> rd1 *> r.
Hypothesis ROv2_1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0 *> r.

Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (((m*2+1)*2^i-1)*2) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 (i+1) ((2^(i+1)-1)*2) m.
Proof. solve_rule ROv2_0_0. Qed.
Lemma RC2_Ov_0_1 len k a m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (m*2+1) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC (m*2*2+1).
Proof. solve_rule ROv2_0_1. Qed.
Lemma RC2_Ov_1_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 (((m*2+1)*2^i-1)*2) -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)-1) |> RC ((m*2+1)*2^(i+1)).
Proof. solve_rule ROv2_1_0. Qed.
Lemma RC2_Ov_1_1 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 ((m*2+1)*2^i*2+1) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 (i+1) ((2^(i+1)-1)*2+1) m.
Proof. solve_rule ROv2_1_1. Qed.
Lemma RC2_Ov_1_1_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 1 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. solve_rule ROv2_1_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => 1<=len /\ n+m<k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; divmod2_cases m.
    + lowbitS_cases n'0.
      eexists (cfgR1 _ _ _ _ _); split; [apply RC2_Ov_0_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)).
      pose proof (split_bound_v2 x (i+1)); arith.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_0_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); arith.
    + lowbitS_cases n'0.
      eexists (cfgR _ _ _); split; [apply RC2_Ov_1_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+3) ltac:(lia)); arith.
    + lowbit_cases n'0.
      * eexists (cfgR _ _ _); split; [apply RC2_Ov_1_1_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
      * eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_1_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
        pose proof (split_bound_v2 x (i+1)); arith.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_R2parity.

(* SOC23_R2parity.TM96 *)
Module TM96.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2parity.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1RC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_0_1 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0 *> r.
Proof. es. Qed.
Lemma ROv2_1_0 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0 *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 2 0 <| Counter.RC 6.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=A) (QR:=B) (len:=2) (k:=0%nat) (n:=6).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0_0|exact ROv2_0_1|exact ROv2_1_0|exact ROv2_1_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM96.

(* SOC23_R2parity.TM97 *)
Module TM97.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2parity.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_1RF1LB_1RB---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_0_1 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0 *> r.
Proof. es. Qed.
Lemma ROv2_1_0 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0 *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 4 9 <| Counter.RC 1.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (len:=4) (k:=9) (n:=1%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0_0|exact ROv2_0_1|exact ROv2_1_0|exact ROv2_1_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM97.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_R2split.v. *)
Module SOC23_R2split.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q) (odd_left:bool).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0: forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> r.
Hypothesis ROv2_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> r.

Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  (if odd_left then l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf
   else l <* ld0 <* ld1^^(n*3+2) |> 0inf).

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule ROv2_0. Qed.
Lemma RC2_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2) 0 0 -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC 1.
Proof. epose proof (ROv2_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC2_Ov_1 len k a m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 m -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)-1) |> RC m.
Proof. solve_rule ROv2_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  (if odd_left then LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1
   else LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |> RC 0).
Proof. destruct odd_left; epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m | cfgR2 len k h n m =>
    1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- case_eq odd_left; intros Eodd; [eexists (cfgL _ _ _)|eexists (cfgR _ _ _)]; split.
           1,3: eapply progress_evstep_trans; [apply corner_case|];
             apply progress_evstep; epose proof RC'_Ov_1 as Hodd;
             rewrite Eodd in Hodd; apply Hodd; arith.
           all: cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + lowbit_cases m.
      * eexists (cfgR _ _ _); split; [apply RC2_Ov_0_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)); lia.
      * eexists (cfgR1 _ _ _ _ _); split; [apply RC2_Ov_0; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+3) ltac:(lia)); lia.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_R2split.

(* SOC23_R2split.TM87 *)
Module TM87.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2split.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LE---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 6 36 <| Counter.RC 1.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=A) (QR:=B) (odd_left:=true) (len:=6) (k:=36) (n:=1%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM87.

(* SOC23_R2split.TM181 *)
Module TM181.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2split.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_1RF0LD_1LE---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 4 10 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (odd_left:=false) (len:=4) (k:=10) (n:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM181.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_R2weighted.v. *)
Module SOC23_R2weighted.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0_0: forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.
Hypothesis ROv2_1_0: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd1 *> r.
Hypothesis ROv2_01_1: forall l r n,
  l |> rd1^^n *> [1;0;1;0;0] *> rd1 *> r -->+
  l <| [0;0] *> rd0^^(n+2) *> r.

Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((m*2+1)*2^i*2) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_0_0. Qed.
Lemma RC2_Ov_0_0_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2) 0 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv2_0_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC2_Ov_1_0 len k a m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 (m*2) -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)-1) |> RC (m*2+1).
Proof. solve_rule ROv2_1_0. Qed.
Lemma RC2_Ov len k h i m:
  LC len k |> RC2 h 0 ((m*2+1)*2^i*2+1) -->+
  LC len k <| RC2 (h+i+2) (2^(h+i+2+1)-1) m.
Proof. solve_rule ROv2_01_1. Qed.
Lemma RC2_Ov_blank len k h:
  LC len k |> RC2 h 0 1 -->+ LC len k <| RC 0.
Proof.
  epose proof (ROv2_01_1 (LC len k) 0inf h) as H.
  unfold LC,RC2,RC in *; rw_Bin; cbn [Str_app] in *.
  repeat rewrite <-(const_unfold _ 0) in *.
  rewrite lpow_all0 in H by solve_const0_eq.
  repeat rewrite <-const_unfold in H |- *.
  exact H.
Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |> RC 0.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => 1<=len /\ n+m*2^(h+2)<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgR _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases m.
    + divmod2_cases h.
      * lowbit_cases n'.
        -- eexists (cfgR _ _ _); split; [apply RC2_Ov_0_0_blank; lia|].
           cbn [P]; pose proof (append_bounds len k (n'0*3+2) ltac:(lia)); lia.
        -- eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_0_0; lia|].
           cbn [P]; pose proof (append_bounds len k (n'0*3+2) ltac:(lia)); arith.
      * eexists (cfgR _ _ _); split; [apply RC2_Ov_1_0; lia|].
        cbn [P]; pose proof (append_bounds len k (n'0*3+3) ltac:(lia)); arith.
    + lowbit_cases n'.
      * eexists (cfgL _ _ _); split; [apply RC2_Ov_blank|cbn [P]; arith].
      * destruct k as [|k]; [arith|].
        eexists (cfgR2 _ _ _ _ _); split.
        -- eapply progress_evstep_trans; [apply RC2_Ov|].
           apply progress_evstep; apply LC_Inc; lia.
        -- cbn [P]; arith.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_R2weighted.

(* SOC23_R2weighted.TM173 *)
Module TM173.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2weighted.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1RC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.
Proof. es. Qed.
Lemma ROv2_1_0 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_01_1 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> rd1 *> r -->+
  l <| [0;0] *> rd0^^(n+2) *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 2 1 <| Counter.RC 4.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=A) (QR:=B) (len:=2) (k:=1%nat) (n:=4).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0_0|exact ROv2_1_0|exact ROv2_01_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM173.

(* SOC23_R2weighted.TM174 *)
Module TM174.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_R2weighted.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0LB_1RF1RD_1RA0LE_1RC0RF_1LB1RE").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.
Proof. es. Qed.
Lemma ROv2_1_0 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_01_1 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> rd1 *> r -->+
  l <| [0;0] *> rd0^^(n+2) *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 4 10 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=F) (len:=4) (k:=10) (n:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0_0|exact ROv2_1_0|exact ROv2_01_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM174.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String Compare_dec.

(* Shared definitions from SOC23_ShortSplit.v. *)
Module SOC23_ShortSplit.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String Compare_dec.


Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q) (qL:list Sym).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{QL}} qL *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_01_0: forall l r n,
  l |> rd1^^n *> [1;0;1;0;0] *> rd0 *> r -->+ l <| rd0^^(n+2) *> [0;1] *> r.
Hypothesis ROv2_0_1: forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [1;0] *> r.
Hypothesis ROv2_1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> [0] *> r.
Hypothesis ROv3_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1] *> r -->+ l <* ld0 <* ld1^^(n*3) |> r.
Hypothesis ROv3_1_0: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.
Hypothesis ROv3_1_S: forall l r n m,
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^(m+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> rd1 *> rd0^^m *> [0] *> rd1 *> r.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0] len n ([1] *> RC m).
Definition RC4 len n := BinDec2 [0] [1] [0;0] len n ([1;0;0;1;1;0;0] *> 0inf).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC3,RC4,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_zero h n: RC3 h n 0 = RC1 h n 0.
Proof. unfold RC3,RC1,RC; rewrite BinInc_O; cbn [Str_app]; repeat rewrite <-const_unfold; reflexivity. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov len k h m:
  LC len k |> RC2 h 0 (m*2) -->+ LC len k <| RC3 (h+2) (2^(h+2+1)-1) m.
Proof. solve_rule ROv2_01_0. Qed.
Lemma RC2_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (((m*2+1)*2^i)*2+1) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv2_0_1. Qed.
Lemma RC2_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2) 0 1 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 1.
Proof. solve_rule ROv2_0_1. Qed.
Lemma RC2_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 (((m*2+1)*2^i)*2+1) -->+
  LC (len+1+(a*3+4)) ((k*2+1)*2^(a*3+4)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_1_1. Qed.
Lemma RC2_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 1 -->+
  LC (len+1+(a*3+4)) ((k*2+1)*2^(a*3+4)-1) |> RC 0.
Proof. solve_rule ROv2_1_1. Qed.
Lemma RC3_Ov_0 len k a m: k<2^len ->
  LC len k |> RC3 (a*2) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> RC m.
Proof. solve_rule ROv3_0. Qed.
Lemma RC3_Ov_1_0 len k a i m: k<2^len ->
  LC len k |> RC3 (a*2+1) 0 (((m*2+1)*2^i)*2) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv3_1_0. Qed.
Lemma RC3_Ov_1_0_blank len k a: k<2^len ->
  LC len k |> RC3 (a*2+1) 0 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv3_1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC3_Ov_1_S len k a i m: k<2^len ->
  LC len k |> RC3 (a*2+1) 0 ((m*2+1)*2^(i+1)-1) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 (i+1) ((2^(i+1)-1)*2) m.
Proof. solve_rule ROv3_1_S. Qed.
Lemma RC4_Inc len n l: 1+n<2^(len+1) ->
  l |> RC4 len (1+n) -->+ l <| RC4 len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC4_Ov_0 len k a: k<2^len ->
  LC len k |> RC4 (a*2) 0 -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC' 0 0.
Proof. solve_rule ROv1_0. Qed.
Lemma RC4_Ov_1 len k a: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0;1;1;0;0] *> 0inf.
Proof. solve_rule ROv1_1. Qed.
Lemma tiny len k: 1+k<2^len ->
  LC len (1+k) |> [0;1;1;0;0] *> 0inf -->+ LC (len+1) (k*2+1) |> RC 1.
Proof.
  intros Hk; follow10 (RInc (LC len (1+k)) ([1;1;0;0] *> 0inf) 0).
  eapply evstep_trans; [apply progress_evstep; apply LC_Inc; lia|].
  epose proof (ROv3_0 _ _ 0) as H; apply progress_evstep; solve_rule H.
Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Lemma RC2_Incs len k h n m: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC2 h n m -->* LC len k |> RC2 h 0 m.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC2_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma LC_Ov_extra0 len h:
  LC len 0 <| RC1 (h+1) ((1*2+1)*2^h-1) 0 -->+
  LC len (2^len-1) |> RC3 h ((2^h-1)*2) 2.
Proof.
  rewrite (Nat.add_comm h 1); unfold LC,RC1,RC3,RC; rw_Bin.
  all: try solve[arith]; try solve[solve_pow2_lt].
  follow_rule LOv.
Qed.
Lemma LC_Ov_extra1 len h:
  LC len 0 <| RC1 (h+1) ((0*2+1)*2^h-1) 0 -->+
  LC len (2^len-1) |> RC4 h ((2^h-1)*2).
Proof.
  rewrite (Nat.add_comm h 1); unfold LC,RC1,RC4,RC; rw_Bin.
  all: try solve[arith]; try solve[solve_pow2_lt].
  follow_rule LOv.
Qed.
Lemma left_RC1_Incs len k h n: k<2^len -> n+k<2^(h+1) ->
  LC len k <| RC1 h (n+k) 0 -->* LC len 0 <| RC1 h n 0.
Proof.
  induction k; intros; [rewrite Nat.add_0_r; finish|].
  follow_inc LC_Inc.
  replace (n+S k) with (1+(n+k)) by lia; follow_inc RC1_Inc.
  follow IHk; try lia; finish.
Qed.
Lemma corner_start len h: 2^(h+1)<=2^len ->
  LC len 0 <| RC (2^(h+1)+1) -->+
  LC (len+1) (2^len*2-2^(h+1)) <| RC1 (h+2) (2^(h+2+1)-1) 0.
Proof.
  intros Hlen.
  replace (2^(h+1)+1) with ((2^h*2+1)*2^0) by arith.
  follow10 LC_Ov.
  replace (2^h) with ((0*2+1)*2^h) by arith.
  follow100 (RC1_Ov_0 len (2^len-1) 0 h 0 ltac:(arith)).
  repeat rewrite Nat.add_0_r.
  replace (((2^len-1)*2+1)*2^(0*3)-1) with
    ((2^len*2-2^(h+1))+(2^h-1)*2) by arith.
  follow RC2_Incs; [arith|arith|].
  follow100 (RC2_Ov (len+1) (2^len*2-2^(h+1)) h 0).
  rewrite RC3_zero; finish.
Qed.
Lemma corner_plus len:
  LC (len+1) 0 <| RC (2^(len+1)+1) -->+
  LC (len+1+1) (2^(len+1+1)-1) |> RC3 (len+1) ((2^(len+1)-1)*2) 2.
Proof.
  follow10 (corner_start (len+1) len ltac:(lia)).
  replace (2^(len+2+1)-1) with
    (((1*2+1)*2^(len+1)-1)+(2^(len+1)*2-2^(len+1))) by arith.
  follow left_RC1_Incs; [arith|arith|].
  replace (len+2) with (len+1+1) by lia.
  follow100 LC_Ov_extra0; finish.
Qed.
Lemma corner_half_plus len:
  LC (len+2) 0 <| RC (2^(len+1)+1) -->+
  LC (len+2+1) (2^(len+2+1)-1) |> RC4 (len+1) ((2^(len+1)-1)*2).
Proof.
  follow10 (corner_start (len+2) len ltac:(arith)).
  replace (2^(len+2+1)-1) with
    (((0*2+1)*2^(len+1)-1)+(2^(len+2)*2-2^(len+1))) by arith.
  follow left_RC1_Incs; [arith|arith|].
  replace (len+2) with (len+1+1) by lia.
  follow100 LC_Ov_extra1; finish; repeat (arith || f_equal).
Qed.
Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat)
  | cfgR3 (len k h n m:nat) | cfgR4 (len k h n:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
| cfgR3 len k h n m => LC len k |> RC3 h n m
| cfgR4 len k h n => LC len k |> RC4 h n
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => (1<=len /\ n+m<=k<2^len /\ n<2^(h+1)) /\
    (h=0 -> forall i, m=2^i -> n+2^i*5<=k+1)
| cfgR2 len k h n m => (1<=len /\ n+m<=k<2^len /\ n<2^(h+1)) /\
    (m mod 2=0 -> n+m/2+2^(h+3)<=k)
| cfgR3 len k h n m => (1<=len /\ n<=k<2^len /\ n+m<=k+1 /\ n<2^(h+1)) /\
    (m mod 2=1 -> n+m<=k)
| cfgR4 len k h n => 1<=len /\ n<k<2^len /\ n<2^(h+1)
end.
Hypothesis tail_safe: forall len k h, 1<=len -> k<2^len ->
  exists y, LC len k |> RC' h 0 -->+ to_config y /\ P y.

Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma append0_bounds len k s: k<2^len ->
  k*2<(k*2+1)*2^s<2^(len+1+s) /\
  (k*2+1)*2^s+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma pure_bound len j:
  2^j*2+1<2^(len+1)*2 -> 2^j*2+1<>2^(len+1)+1 ->
  2^j*2+1<>2^len+1 -> 2^j*5<=2^(len+1).
Proof.
  intros H E0 E1; destruct (le_dec (j+2) len) as [Hj|Hj].
  - assert (2^(j+2)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith.
  - assert (j<len+1) by (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
    destruct (Nat.eq_dec j len); [subst j; arith|].
    replace len with (j+1) in * by lia; arith.
Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k h n m|len k h n];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct len as [|len]; [cbn in HP; lia|].
      replace (S len) with (len+1) in * by lia.
      destruct (Nat.eq_dec m (2^(len+1))) as [E|E].
      * subst m.
        destruct (tail_safe (len+1+1) (2^len*2) len ltac:(lia) ltac:(arith)) as [y [Hy Py]].
        exists y; split; [eapply progress_trans; [apply corner_case|exact Hy]|exact Py].
      * destruct (Nat.eq_dec m (2^(len+1)+1)) as [E0|E0].
        -- subst m; eexists (cfgR3 _ _ _ _ _); split; [apply corner_plus|].
           cbn [P]; split; [arith|intros H; lia].
        -- destruct (Nat.eq_dec m (2^len+1)) as [E1|E1].
           ++ subst m; destruct len as [|len]; [cbn in E; lia|].
              replace (S len) with (len+1) in * by lia.
              replace (len+1+1) with (len+2) in * by lia.
              eexists (cfgR4 _ _ _ _); split; [apply corner_half_plus|cbn [P]; arith].
           ++ lowbit_cases m; [lia|].
              eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
              cbn [P]; split.
              ** pose proof (split_bound_v3 x i (len+1) ltac:(lia) E); arith.
              ** intros Ei j Ex; subst i x.
                 pose proof (pure_bound len j ltac:(arith) ltac:(arith) ltac:(arith)); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct HP as [HP Hpower]; destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; split; [lia|].
        intros Eh j Ej; specialize (Hpower Eh j Ej); lia. }
    divmod2_cases h; rename n' into a; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * intros Hx; destruct a as [|a].
        -- destruct x as [|x]; [specialize (Hpower ltac:(lia) i ltac:(arith)); arith|].
           destruct x; [lia|arith].
        -- replace (S a*3) with (a*3+3) in * by lia; arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * intros Ei j Ex; subst i x; arith.
  - destruct HP as [HP Heven]; destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; split; [lia|intros E; specialize (Heven E); lia]. }
    divmod2_cases m; rename n' into q.
    + specialize (Heven ltac:(lia)); destruct k as [|k]; [arith|].
      eexists (cfgR3 _ _ _ _ _); split.
      * eapply progress_evstep_trans; [apply RC2_Ov|].
        apply progress_evstep; apply LC_Inc; lia.
      * cbn [P]; split; [arith|intros; arith].
    + divmod2_cases h; rename n' into a; lowbit_cases q.
      * eexists (cfgR _ _ _); split; [apply RC2_Ov_0_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)); lia.
      * eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_0; lia|].
        cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)); split;
          [arith|intros; arith].
      * eexists (cfgR _ _ _); split; [apply RC2_Ov_1_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (a*3+4) ltac:(lia)); lia.
      * eexists (cfgR1 _ _ _ _ _); split; [apply RC2_Ov_1; lia|].
        cbn [P]; pose proof (append_bounds len k (a*3+4) ltac:(lia)); split.
        -- arith.
        -- intros Ei j Ex; subst i x; arith.
  - destruct HP as [HP Hodd]; destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR3 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC3_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; split; [lia|intros E; specialize (Hodd E); lia]. }
    divmod2_cases h; rename n' into a.
    + eexists (cfgR _ _ _); split; [apply RC3_Ov_0; lia|].
      cbn [P]; pose proof (append0_bounds len k (a*3) ltac:(lia)); lia.
    + divmod2_cases m; rename n' into q.
      * lowbit_cases q.
        -- eexists (cfgR _ _ _); split; [apply RC3_Ov_1_0_blank; lia|].
           cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)); lia.
        -- eexists (cfgR2 _ _ _ _ _); split; [apply RC3_Ov_1_0; lia|].
           cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)); split;
             [arith|intros; arith].
      * specialize (Hodd ltac:(lia)); lowbitS_cases q.
        replace (((x*2+1)*2^i-1)*2+1) with ((x*2+1)*2^(i+1)-1) in * by arith.
        eexists (cfgR1 _ _ _ _ _); split; [apply RC3_Ov_1_S; lia|].
        cbn [P]; pose proof (append_bounds len k (a*3+1) ltac:(lia)); split; [arith|lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR4 _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC4_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; rename n' into a.
    + destruct (tail_safe (len+1+a*3) ((k*2+1)*2^(a*3)-1) 0
        ltac:(lia) ltac:(arith)) as [y [Hy Py]].
      exists y; split; [eapply progress_trans; [apply RC4_Ov_0; lia|exact Hy]|exact Py].
    + eexists (cfgR _ _ _); split.
      * eapply progress_trans; [apply RC4_Ov_1; lia|].
        replace ((k*2+1)*2^(a*3+2)-1) with (1+((k*2+1)*2^(a*3+2)-2)) by arith.
        apply tiny; arith.
      * cbn [P]; arith.
Qed.
Lemma nonhalt_from len k m: P (cfgL len k m) ->
  c0 -->* LC len k <| RC m -> ~halts tm c0.
Proof.
  intros HP Hinit; eapply multistep_nonhalt; [exact Hinit|].
  change (~halts tm (to_config (cfgL len k m))).
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac solve_tail H := intros; unfold Counter.LC,Counter.RC',Counter.RC;
  rw_Bin; try solve[solve_pow2_lt];
  epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
End SOC23_ShortSplit.

(* SOC23_ShortSplit.TM19 *)
Module TM19.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String Compare_dec.

Import SOC23_ShortSplit.

Definition tm := Eval compute in (TM_from_str "1LB1RF_0LC0LB_0RD0RA_1LE---_1RA1RC_1RE1LE").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_01_0 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> rd0 *> r -->+ l <| rd0^^(n+2) *> [0;1] *> r.
Proof. es. Qed.
Lemma ROv2_0_1 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv2_1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> [0] *> r.
Proof. es. Qed.
Lemma ROv3_0 l r n:
  l |> rd1^^(n*2) *> [1;1] *> r -->+ l <* ld0 <* ld1^^(n*3) |> r.
Proof. es. Qed.
Lemma ROv3_1_0 l r n:
  l |> rd1^^(n*2+1) *> [1;1] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.
Proof. es. Qed.
Lemma ROv3_1_S l r n m:
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^(m+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> rd1 *> rd0^^m *> [0] *> rd1 *> r.
Proof. es. Qed.


Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) |> 0inf.
Proof. intros; st; sr_r; do 4 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+3) <| 0inf.
Proof. intros; st; sr_r; do 9 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma tail_safe len k h: 1<=len -> k<2^len ->
  exists y, Counter.LC len k |> Counter.RC' h 0 -->+
    Counter.to_config C A [0;1] y /\ Counter.P y.
Proof.
  intros HL Hk; divmod2_cases h; rename n' into a.
  - exists (Counter.cfgR (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) 0); split.
    + cbn [Counter.to_config]; epose proof (ROv'_0 _ a) as H; solve_tail H.
    + cbn [Counter.P]; arith.
  - exists (Counter.cfgL (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) 0); split.
    + cbn [Counter.to_config]; epose proof (ROv'_1 _ a) as H; solve_tail H.
    + cbn [Counter.P]; arith.
Qed.
Lemma init: c0 -->* Counter.LC 4 10 <| Counter.RC 1.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (qL:=[0;1]) (len:=4) (k:=10) (m:=1%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_01_0|exact ROv2_0_1|exact ROv2_1_1|exact ROv3_0|
    exact ROv3_1_0|exact ROv3_1_S|exact tail_safe|exact init|cbn [Counter.P]; lia].
Qed.
End TM19.

(* SOC23_ShortSplit.TM149 *)
Module TM149.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String Compare_dec.

Import SOC23_ShortSplit.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_1LC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_01_0 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> rd0 *> r -->+ l <| rd0^^(n+2) *> [0;1] *> r.
Proof. es. Qed.
Lemma ROv2_0_1 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv2_1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> [0] *> r.
Proof. es. Qed.
Lemma ROv3_0 l r n:
  l |> rd1^^(n*2) *> [1;1] *> r -->+ l <* ld0 <* ld1^^(n*3) |> r.
Proof. es. Qed.
Lemma ROv3_1_0 l r n:
  l |> rd1^^(n*2+1) *> [1;1] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.
Proof. es. Qed.
Lemma ROv3_1_S l r n m:
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^(m+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> rd1 *> rd0^^m *> [0] *> rd1 *> r.
Proof. es. Qed.


Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma tail_safe len k h: 1<=len -> k<2^len ->
  exists y, Counter.LC len k |> Counter.RC' h 0 -->+
    Counter.to_config C A [1;1] y /\ Counter.P y.
Proof.
  intros HL Hk; divmod2_cases h; rename n' into a.
  - exists (Counter.cfgL (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) 0); split.
    + cbn [Counter.to_config]; epose proof (ROv'_0 _ a) as H; solve_tail H.
    + cbn [Counter.P]; arith.
  - exists (Counter.cfgR (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) 0); split.
    + cbn [Counter.to_config]; epose proof (ROv'_1 _ a) as H; solve_tail H.
    + cbn [Counter.P]; arith.
Qed.
Lemma init: c0 -->* Counter.LC 4 10 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (qL:=[1;1]) (len:=4) (k:=10) (m:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_01_0|exact ROv2_0_1|exact ROv2_1_1|exact ROv3_0|
    exact ROv3_1_0|exact ROv3_1_S|exact tail_safe|exact init|cbn [Counter.P]; lia].
Qed.
End TM149.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM1.TM1 *)
Module TM1.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Definition tm := Eval compute in (TM_from_str "1RB1LA_1LB1RC_0RD0RB_1LE0RF_0LE1LA_0RC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{A}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n:
  ldh <* ld1^^n <| rd0 *> r -->+ ldh <* ld0^^(n+1) |> [0;0] *> r.
Proof. es. Qed.
Lemma LOv_1 r n:
  ldh <* ld1^^n <| rd1 *> r -->+ ldh <* ld0^^(n+2) |> r.
Proof. es. Qed.
Lemma ROv2_0_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld0^^(n*3+3) |> [0;0] *> r.
Proof. es. Qed.
Lemma ROv2_0_1 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld0^^(n*3+4) |> r.
Proof. es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld0^^(n*3+4) |> r.
Proof. es. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC2 len n m := BinDec2 [0;0] [1;0] [0] len n (rd1 *> BinInc rd1 m).
Lemma append_lt len k s: k<2^len -> (k+1)*2^s-1<2^(len+s).
Proof. intros; rewrite Nat.pow_add_r; pose proof (Nat.pow_nonzero 2 s); nia. Qed.
Ltac follow_rule H := intros; epose proof H as HX; cbn[Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC,RC2;
  rw_Bin; try solve[solve_pow2_lt]; try solve[apply append_lt; assumption]; follow_rule H.

Lemma LC_Inc len n r: 1+n<2^len ->
  LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) ->
  l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov_0 len n i:
  LC len 0 <| RC ((n*2+1)*2^i*2) -->+
  LC (len+1) (2^(len+1)-1) |> RC2 i ((2^i-1)*2+1) n.
Proof. solve_rule LOv_0. Qed.
Lemma LC_Ov_0_blank len:
  LC len 0 <| RC 0 -->+ LC (len+1) (2^(len+1)-1) |> RC 0.
Proof. epose proof (LOv_0 0inf len) as H; solve_rule H. Qed.
Lemma LC_Ov_1 len n:
  LC len 0 <| RC (n*2+1) -->+
  LC (len+2) (2^(len+2)-1) |> RC n.
Proof. solve_rule LOv_1. Qed.

Lemma RC2_Ov_0_0 len a k i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((m*2+1)*2^i*2) -->+
  LC (len+(a*3+3)) ((k+1)*2^(a*3+3)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_0_0. Qed.
Lemma RC2_Ov_0_0_blank len a k: k<2^len ->
  LC len k |> RC2 (a*2) 0 0 -->+
  LC (len+(a*3+3)) ((k+1)*2^(a*3+3)-1) |> RC 0.
Proof. epose proof (ROv2_0_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC2_Ov_0_1 len a k m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (m*2+1) -->+
  LC (len+(a*3+4)) ((k+1)*2^(a*3+4)-1) |> RC m.
Proof. solve_rule ROv2_0_1. Qed.
Lemma RC2_Ov_1 len a k m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 m -->+
  LC (len+(a*3+4)) ((k+1)*2^(a*3+4)-1) |> RC m.
Proof. solve_rule ROv2_1. Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => k+n<2^len*2 /\ k<2^len
| cfgR len k n => k+n+1<2^len*2 /\ k<2^len
| cfgR2 len k h n m => n+m<=k<2^len /\ n<2^(h+1)
end.

(* Appending all-zero left digits increases the remaining decrement budget. *)
Lemma append_bounds len k s m: k<2^len -> m<=k ->
  ((k+1)*2^s-1)+m+1<2^(len+s)*2 /\
  k<=((k+1)*2^s-1)<2^(len+s).
Proof. intros; rewrite Nat.pow_add_r; pose proof (Nat.pow_nonzero 2 s); nia. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m]; cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + divmod2_cases m.
      * lowbit_cases n'.
        -- eexists (cfgR _ _ _); split; [apply LC_Ov_0_blank|].
           cbn [P]; rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
        -- eexists (cfgR2 _ _ _ _ _); split; [apply LC_Ov_0|].
           cbn [P]; pose proof (split_bound_v2 x i).
           repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
      * eexists (cfgR _ _ _); split; [apply LC_Ov_1|].
        cbn [P]; rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + divmod2_cases m.
      * lowbit_cases n'0.
        -- eexists (cfgR _ _ _); split; [apply RC2_Ov_0_0_blank; lia|].
           cbn [P]; pose proof (append_bounds len k (n'*3+3) 0 ltac:(lia) ltac:(lia)); lia.
        -- eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_0_0; lia|].
           cbn [P]; pose proof (append_bounds len k (n'*3+3) 0 ltac:(lia) ltac:(lia)).
           pose proof (split_bound_v2 x i); rewrite (Nat.pow_add_r 2 i 1); cbn [Nat.pow]; lia.
      * eexists (cfgR _ _ _); split; [apply RC2_Ov_0_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+4) n'0 ltac:(lia) ltac:(lia)); lia.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+4) m ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma init: c0 -->* to_config (cfgL 6 15 1).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM1.

From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2.
Require Import NArith Lia ZifyNat List String.

(* Shared definitions from SOC23_TM102Halt.v. *)
Module SOC23_TM102Halt.
(* Checked fixed-width counter pairs, with primitive execution everywhere else. *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.Eqb BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia ZifyNat List String.


Module Core.
Section Machine.
Variables (tm:TM) (QL QR QE:Q).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Definition addN p k := match k with N0=>p | Npos k=>Pos.add p k end.
Lemma addN_succ p k: addN p (N.succ k) = addN (Pos.succ p) k.
Proof. destruct k; cbn [addN N.succ]; lia. Qed.

Lemma paired k p q l r:
  (k<=rest p)%N -> (k<=rest q)%N ->
  BinaryCounter ld0 ld1 l p |> BinaryCounter rd0 rd1 r q -->*
  BinaryCounter ld0 ld1 l (addN p k) |> BinaryCounter rd0 rd1 r (addN q k).
Proof.
  revert p q; induction k using N.peano_ind; intros p q Hp Hq.
  - apply evstep_refl.
  - assert (Hp0: rest p<>0%N) by lia.
    assert (Hq0: rest q<>0%N) by lia.
    pose proof (rest_S p Hp0); pose proof (rest_S q Hq0).
    rewrite !addN_succ.
    eapply evstep_trans.
    + apply progress_evstep; apply BinaryCounter.RInc.
      * intros; change (rd0^^n *> rd1 *> r0) with (rd0^^n *> [1] *> [0;0] *> r0).
        apply RInc.
      * apply not_full_iff_rest; exact Hq0.
    + eapply evstep_trans.
      * apply progress_evstep; apply BinaryCounter.LInc; [apply LInc|].
        apply not_full_iff_rest; exact Hp0.
      * apply IHk; lia.
Qed.

(* Binary words have a leading sentinel in their positive representation;
   it is not a tape digit.  No unary large integer is computed. *)
Fixpoint word (d0 d1:list Sym) p := match p with
  | xH=>nil | xO p=>d0++word d0 d1 p | xI p=>d1++word d0 d1 p end.
Lemma word_spec d0 d1 p r:
  word d0 d1 p *> r = BinaryCounter d0 d1 r p.
Proof. induction p; cbn; rewrite ?Str_app_assoc, ?IHp; reflexivity. Qed.

(* This check permits omitted trailing blanks, but never treats a failed
   match as a halt.  Proposal parsers need no soundness assumptions. *)
Fixpoint peel (w s:list Sym) : option (list Sym) := match w with
  | nil=>Some s
  | b::w=>match s with
    | nil=>if sym_eqb b 0 then peel w nil else None
    | c::s=>if sym_eqb b c then peel w s else None end end.
Lemma peel_spec w s r: peel w s=Some r -> s *> 0inf = w *> r *> 0inf.
Proof.
  revert s; induction w as [|b w IH]; intros s H; cbn in H.
  - injection H as <-; reflexivity.
  - destruct s as [|c s].
    + destruct (sym_eqb_spec b 0); try discriminate; subst.
      specialize (IH _ H); cbn; rewrite <-IH; apply const_unfold.
    + destruct (sym_eqb_spec b c); try discriminate; subst.
      specialize (IH _ H); cbn; rewrite <-IH; reflexivity.
Qed.

Definition State := (Q * list Sym * list Sym)%type.
Definition denote (s:State) := let '(q,l,r):=s in l *> 0inf {{q}}> r *> 0inf.
Fixpoint room p : N := match p with
  | xH=>N0 | xI p=>N.double (room p) | xO p=>N.succ_double (room p) end.
Lemma room_spec p: room p=rest p.
Proof.
  induction p; cbn [room]; rewrite ?IHp.
  - unfold rest; cbn [log2 pow2']; pose proof (pow2'_log2_ge p).
    rewrite N.double_spec; lia.
  - rewrite N.succ_double_spec,rest_mul2; lia.
  - reflexivity.
Qed.

Fixpoint decode_left (l:list Sym) : positive * list Sym := match l with
  | S0::S1::l=>let '(p,r):=decode_left l in (xO p,r)
  | S1::S1::l=>let '(p,r):=decode_left l in (xI p,r)
  | _=>(xH,l) end.
Lemma decode_left_spec l p r: decode_left l=(p,r) ->
  l *> 0inf=BinaryCounter ld0 ld1 (r *> 0inf) p.
Proof.
  revert l p r; fix IH 1; intros [|[] [|[] l]] p r H;
    cbn [decode_left] in H; try (injection H as <- <-; reflexivity).
  all: destruct (decode_left l) as [p' r'] eqn:E; injection H as <- <-;
    cbn [BinaryCounter Str_app]; rewrite (IH _ _ _ E); reflexivity.
Qed.
Definition put b (v:positive * list Sym) :=
  let '(p,r):=v in (match b with S0=>xO p | S1=>xI p end,r).
Fixpoint decode_right n (r:list Sym) : positive * list Sym := match n with
  | O=>(xH,r)
  | S n=>match r with
    | b::S0::S0::r=>put b (decode_right n r)
    | nil=>put S0 (decode_right n nil)
    | b::nil | b::S0::nil=>put b (decode_right n nil)
    | _=>(xH,r) end end.
Lemma decode_right_spec n r p t: decode_right n r=(p,t) ->
  r *> 0inf=BinaryCounter rd0 rd1 (t *> 0inf) p.
Proof.
  revert r p t; induction n as [|n IHn]; intros r p t H.
  - injection H as <- <-; reflexivity.
  - destruct r as [|[] [|[] [|[] r]]]; cbn [decode_right] in H;
      try (injection H as <- <-; reflexivity).
    all: match type of H with context[decode_right ?n ?r] =>
      destruct (decode_right n r) as [p' t'] eqn:E;
      cbn [put] in H; injection H as <- <-;
      cbn [BinaryCounter Str_app]; rewrite <- (IHn _ _ _ E);
      repeat rewrite <-const_unfold; reflexivity end.
Qed.
Definition right_start (r:list Sym) := match r with
  | _::S1::_ | _::_::S1::_=>false | _=>true end.
Definition accelerate (s:State) : option State :=
  let '(q,l,r):=s in if q_eqb q QR then match l with
  | S0::S1::l=>if right_start r then
    let '(p,l'):=decode_left l in
    match room p with
    | N0=>None
    | k=>let '(q,r'):=decode_right (S (log2 p)) r in
      match N.min k (room q) with
      | N0=>None
      | k=>Some (QR,[0;1]++word ld0 ld1 (addN p k)++l',
                       word rd0 rd1 (addN q k)++r') end end else None
  | _=>None end else None.
Lemma accelerate_spec s t: accelerate s=Some t -> denote s -[tm]->* denote t.
Proof.
  destruct s as [[state l] r]; unfold accelerate.
  destruct (q_eqb_spec state QR); try discriminate; subst.
  do 2 (destruct l as [|[] l]; try discriminate).
  destruct (right_start r); try discriminate.
  destruct (decode_left l) as [p l'] eqn:Hl.
  destruct (room p) eqn:Hp; try discriminate.
  destruct (decode_right (S (log2 p)) r) as [q r'] eqn:Hr.
  destruct (N.min (N.pos p0) (room q)) eqn:Hk; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf |> r *> 0inf -[tm]->*
    (word ld0 ld1 (addN p (N.pos p1))++l') *> 0inf |>
    (word rd0 rd1 (addN q (N.pos p1))++r') *> 0inf).
  apply decode_left_spec in Hl; apply decode_right_spec in Hr.
  rewrite Hl,Hr,!Str_app_assoc,!word_spec.
  apply paired; rewrite <-!room_spec,<-Hk; [rewrite Hp; apply N.le_min_l|apply N.le_min_r].
Qed.

Definition make_left q (l r:list Sym) : State := match l with
  | nil=>(q,nil,S0::r) | b::l=>(q,l,b::r) end.
Lemma make_left_spec q l r:
  denote (make_left q l r)=l *> 0inf <{{q}} r *> 0inf.
Proof. destruct l; reflexivity. Qed.
Inductive Shift := Keep | Erase | Digits | Twins | Aux | ReturnDigits.
Definition shift_q tag := match tag with
  | Keep | ReturnDigits=>QL | Erase=>QE | Digits | Twins=>QR | Aux=>D end.
Definition shift_left tag n : list Sym := match tag with
  | Keep | Erase=>[1]^^n | _=>nil end.
Definition shift_right tag n : list Sym := match tag with
  | Keep=>[1;1] | Erase=>[1] | Digits=>rd1^^(1+n)
  | Twins=>[1;1]^^(1+n) | Aux=>[0;1;0;0]^^(1+n)
  | ReturnDigits=>[0;1;0]^^(1+n) end.
Definition shift_target tag n (l r:list Sym) : State := match tag with
  | Keep=>make_left QL l ([1]^^(n+2)++r)
  | Erase=>make_left QE l ([0]^^(1+n)++r)
  | Digits=>(QR,[1;1;1]^^(1+n)++l,r)
  | Twins=>(QR,[0;1]^^(1+n)++l,r)
  | Aux=>(D,<[1;0;1;1]^^(1+n)++l,r)
  | ReturnDigits=>(QL,[1;1;1]^^(1+n)++l,r) end.
Hypothesis shift_rule: forall tag n (l r:list Sym),
  denote (shift_q tag,shift_left tag n++l,shift_right tag n++r) -->*
  denote (shift_target tag n l r).
Definition checked_shift tag n (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q (shift_q tag) then
    match peel (shift_left tag n) l,peel (shift_right tag n) r with
    | Some l,Some r=>Some (shift_target tag n l r) | _,_=>None end
  else None.
Lemma checked_shift_spec tag n s t:
  checked_shift tag n s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_shift.
  destruct (q_eqb_spec q (shift_q tag)); try discriminate; subst.
  destruct (peel (shift_left tag n) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel (shift_right tag n) r) as [r'|] eqn:Hr; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf {{shift_q tag}}> r *> 0inf -->* denote (shift_target tag n l' r')).
  apply peel_spec in Hl; apply peel_spec in Hr.
  rewrite Hl,Hr,<-!Str_app_assoc; apply shift_rule.
Qed.

Fixpoint ones (l:list Sym) := match l with S1::l=>S (ones l) | _=>O end.
Fixpoint twins (r:list Sym) := match r with
  | S1::S1::r=>S (twins r) | _=>O end.
Fixpoint digits (r:list Sym) := match r with
  | S1::S0::S0::r=>S (digits r) | _=>O end.
Fixpoint auxiliary (r:list Sym) := match r with
  | S0::S1::S0::S0::r=>S (auxiliary r) | _=>O end.
Fixpoint returning (r:list Sym) := match r with
  | S0::S1::S0::r=>S (returning r) | _=>O end.
Definition scan_proposal (s:State) : option (Shift*nat) :=
  let '(q,l,r):=s in
  if q_eqb q QL then match r with
    | S1::S1::_=>Some (Keep,ones l)
    | _=>match returning r with S n=>Some (ReturnDigits,n) | _=>None end end
  else if q_eqb q QE then match r with
    | S1::_=>Some (Erase,ones l) | _=>None end
  else if q_eqb q QR then match r with
    | S1::S1::r=>Some (Twins,twins r)
    | _=>match digits r with S n=>Some (Digits,n) | _=>None end end
  else if q_eqb q D then
    match auxiliary r with S n=>Some (Aux,n) | _=>None end
  else None.
Definition scan (s:State) := match scan_proposal s with
  | Some (tag,n)=>checked_shift tag n s | None=>None end.
Lemma scan_spec s t: scan s=Some t -> denote s -->* denote t.
Proof.
  unfold scan; destruct (scan_proposal s) as [[tag n]|]; try discriminate.
  apply checked_shift_spec.
Qed.
Definition primitive (s:State) : option State :=
  let '(q,l,r):=s in let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
  match tm (q,b) with
  | None=>None
  | Some (b,R,q)=>Some (q,b::l,r)
  | Some (b,L,q)=>match l with nil=>Some (q,nil,S0::b::r) | a::l=>Some (q,l,a::b::r) end
  end.
Lemma primitive_spec s t: primitive s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; cbn [primitive];
    [destruct (tm (@pair Q sym q S0)) as [[[a d] q']|] eqn:E |
     destruct (tm (@pair Q sym q b)) as [[[a d] q']|] eqn:E]; try discriminate.
  all: destruct d; try destruct l as [|b' l]; intros H; injection H as <-.
  all: eapply evstep_step; [apply step_c_spec;
      cbn [step_c denote Str_app move_left move_right Streams.hd Streams.tl const];
      fold Q Sym in E; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma primitive_halt s: primitive s=None -> halts tm (denote s).
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; cbn [primitive];
    [destruct (tm (@pair Q sym q S0)) as [[[a d] q']|] eqn:E |
     destruct (tm (@pair Q sym q b)) as [[[a d] q']|] eqn:E].
  all: try (destruct d; try destruct l; discriminate).
  all: intros _; apply halted_halts; exact E.
Qed.


Definition next (s:State) : State+unit := match accelerate s with
  | Some t=>inl t
  | None=>match scan s with
    | Some t=>inl t
    | None=>match primitive s with Some t=>inl t | None=>inr tt end end end.
Lemma next_spec s:
  match next s with inl t=>denote s -->* denote t | inr _=>halts tm (denote s) end.
Proof.
  unfold next; destruct (accelerate s) as [t|] eqn:E.
  - eapply accelerate_spec; exact E.
  - destruct (scan s) as [t|] eqn:G.
    + eapply scan_spec; exact G.
    + destruct (primitive s) as [t|] eqn:H.
      * eapply primitive_spec; exact H.
      * apply primitive_halt; exact H.
Qed.
Definition check_from (initial:State) fuel := match N_iter_until next (inl initial) fuel with
  | inr _=>true | inl _=>false end.
Lemma check_from_spec initial fuel: check_from initial fuel=true -> halts tm (denote initial).
Proof.
  pose proof (@N_iter_until_spec State unit next (inl initial) fuel
    (fun s=>denote initial -->* denote s) (fun _=>halts tm (denote initial))) as H.
  assert (K: forall s, denote initial -->* denote s ->
    match next s with inl t=>denote initial -->* denote t | inr _=>halts tm (denote initial) end).
  { intros s Hs; pose proof (next_spec s) as Hn; destruct (next s).
    - eapply evstep_trans; eassumption.
    - eapply halts_evstep; eassumption. }
  specialize (H K (evstep_refl _ _)); unfold check_from.
  destruct (N_iter_until next (inl initial) fuel); cbn in H |- *;
    intros Hc; try discriminate; exact H.
Qed.

End Machine.
End Core.
End SOC23_TM102Halt.

(* SOC23_TM102Halt.TM102 *)
Module TM102.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.Eqb BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia ZifyNat List String.

Import SOC23_TM102Halt.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_1RF1LB_1RD---").
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Lemma LInc l r n:
  l <* <[1;0] <* <[1;1]^^n <| r -[tm]->+ l <* <[1;1] <* <[1;0]^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> [1;0;0]^^n *> [0] *> r -[tm]->+ l <| [0;0;0]^^n *> [1] *> r.
Proof. es. Qed.
Lemma shift_rule tag n (l r:list Sym):
  Core.denote (Core.shift_q C A B tag,Core.shift_left tag n++l,Core.shift_right tag n++r) -[tm]->*
  Core.denote (Core.shift_target C A B tag n l r).
Proof.
  destruct tag; cbn [Core.shift_q Core.shift_left Core.shift_right Core.shift_target];
    rewrite ?Core.make_left_spec; unfold Core.denote; rewrite !Str_app_assoc;
    generalize (l *> 0inf), (r *> 0inf); intros l' r'; clear l r.
  all: es.
Qed.
Theorem halt: halts tm c0.
Proof.
  apply (Core.check_from_spec tm C A B LInc RInc shift_rule (A,nil,nil) 100000%N).
  native_check_eq.
Qed.
End TM102.

(* SOC23_TM102Halt.TM136 *)
Module TM136.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.Eqb BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia ZifyNat List String.

Import SOC23_TM102Halt.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LF_1LA---").
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Lemma LInc l r n:
  l <* <[1;0] <* <[1;1]^^n <| r -[tm]->+ l <* <[1;1] <* <[1;0]^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> [1;0;0]^^n *> [0] *> r -[tm]->+ l <| [0;0;0]^^n *> [1] *> r.
Proof. es. Qed.
Lemma shift_rule tag n (l r:list Sym):
  Core.denote (Core.shift_q A B C tag,Core.shift_left tag n++l,Core.shift_right tag n++r) -[tm]->*
  Core.denote (Core.shift_target A B C tag n l r).
Proof.
  destruct tag; cbn [Core.shift_q Core.shift_left Core.shift_right Core.shift_target];
    rewrite ?Core.make_left_spec; unfold Core.denote; rewrite !Str_app_assoc;
    generalize (l *> 0inf), (r *> 0inf); intros l' r'; clear l r.
  all: es.
Qed.
Theorem halt: halts tm c0.
Proof.
  apply (Core.check_from_spec tm A B C LInc RInc shift_rule (A,nil,nil) 100000%N).
  native_check_eq.
Qed.
End TM136.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM114.TM114 *)
Module TM114.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_0RF1LB_1RC---").
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation rm1 := [1;1;0;0].
Notation rm3 := [1;0;1;0;0].
Notation cd0 := <[0;0;1].
Notation cd1 := <[1;1;1].
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Definition LC len n := BinDec ld0 ld1 len n ldh.

Lemma LInc l r n: l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n: l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n: ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Lemma CoreEnter l r n: l |> rd1^^n *> rm3 *> r -->+
  l <* [0;1] <* cd1^^n <* [1;1] <* cd0 {{C}}> r.
Proof. es' n & l r. Qed.
Lemma CoreD l r: l {{C}}> rd1 *> r -->+ l <* cd0 {{C}}> r.
Proof. es' & l r. Qed.
Lemma CoreT l r: l {{C}}> [0;1;0] *> r -->+ l <* cd1 {{C}}> r.
Proof. es' & l r. Qed.
Lemma CoreZ l r n: l <* cd0 <* cd1^^n {{C}}> rd0 *> r -->+
  l <* cd1 {{C}}> rd0^^n *> [0;1;0] *> r.
Proof. es' n & l r. Qed.
Lemma ShortEven l r n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) <| r.
Proof. es' n & l r. Qed.
Lemma ShortOdd l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> r.
Proof. es' n & l r. Qed.
Lemma DoubleCorner l n:
  l |> rd1^^n *> [1;0;1;0;0;0;1] *> 0inf -->+
  l <| rd0^^(n+2) *> rd1^^2 *> 0inf.
Proof. es' n & l. Qed.
Lemma init: c0 -[ tm ]->* (LC 4 9 <| rd1 *> 0inf).
Proof. esx. Qed.

Definition RC n := BinInc rd1 n.
Notation td := [0;1;0].
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

(* n is the virtual value, w the weight of the unconsumed shifted tail. *)
Inductive Num: nat -> nat -> side -> Prop :=
| NumOrd n: Num n 0 (RC n)
| NumShort0 m: Num (m*6) m ([0;0] *> RC m)
| NumShort1 m: Num (m*6+1) m ([1;0] *> RC m)
| NumZ n w r: Num n w r -> Num (n*2) (w*2) (rd0 *> r)
| NumD n w r: Num n w r -> Num (n*2+1) (w*2) (rd1 *> r).

Lemma Num_bound n w r: Num n w r -> 0<w -> n<w*8.
Proof. induction 1; intros; lia. Qed.
Lemma Num_ordinary n w r: Num n w r -> w=0%nat -> r=RC n.
Proof.
  induction 1; intros Hw.
  - reflexivity.
  - subst m; unfold RC; rewrite BinInc_O; cbn [Str_app];
      repeat rewrite <-(const_unfold _ 0); reflexivity.
  - subst m; unfold RC; rewrite BinInc_O.
    change ([1;0] *> 0inf = BinInc rd1 (0*2+1)).
    rewrite BinInc_mul2add1, BinInc_O; unfold Sym; cbn [Str_app];
      repeat rewrite <-(const_unfold _ 0); reflexivity.
  - rewrite IHNum by lia; unfold RC; rewrite BinInc_mul2; reflexivity.
  - rewrite IHNum by lia; unfold RC; rewrite BinInc_mul2add1; reflexivity.
Qed.
Lemma Num_zeros n w r a: Num n w r -> Num (n*2^a) (w*2^a) (rd0^^a *> r).
Proof.
  intros H; induction a; cbn [lpow].
  - applys_eq H; flia.
  - rewrite Nat.pow_succ_r'.
    applys_eq (NumZ _ _ _ IHa); flia.
Qed.

(* Generated Z/T prefix, followed by the untouched ordinary input. *)
Inductive Input: nat -> nat -> side -> Prop :=
| InputEnd m: Input (m*6) m (RC m)
| InputZ v w r: Input v w r -> Input (v*2) (w*2) (rd0 *> r)
| InputT v w r: Input v w r -> Input (v*2+2) (w*2) (td *> r).

Lemma Input_zeros v w r a: Input v w r -> Input (v*2^a) (w*2^a) (rd0^^a *> r).
Proof.
  intros H; induction a; cbn [lpow].
  - applys_eq H; flia.
  - rewrite Nat.pow_succ_r'.
    applys_eq (InputZ _ _ _ IHa); flia.
Qed.
Lemma Input_Num v w r: Input v w r ->
  Num v w ([0;0] *> r) /\ Num (v+1) w ([1;0] *> r).
Proof.
  induction 1 as [m|v w r H [H0 H1]|v w r H [H0 H1]]; split.
  - apply NumShort0.
  - apply NumShort1.
  - change (Num (v*2) (w*2) (rd0 *> [0;0] *> r)); apply NumZ,H0.
  - change (Num (v*2+1) (w*2) (rd1 *> [0;0] *> r)); apply NumD,H0.
  - change (Num (v*2+2) (w*2) (rd0 *> [1;0] *> r)).
    applys_eq (NumZ _ _ _ H1); flia.
  - change (Num (v*2+2+1) (w*2) (rd1 *> [1;0] *> r)).
    applys_eq (NumD _ _ _ H1); flia.
Qed.

Lemma Input_cases v w r: Input v w r ->
  (exists v' w' r', Input v' w' r' /\ r=rd0 *> r' /\ v=v'*2 /\ w=w'*2) \/
  (exists v' w' r', Input v' w' r' /\ r=td *> r' /\ v=v'*2+2 /\ w=w'*2) \/
  (exists v' w' r', Input v' w' r' /\ r=rd1 *> r' /\ v=v'*2+6 /\ w=w'*2+1).
Proof.
  destruct 1.
  - divmod2_cases m; unfold RC; rw_Bin; cbn [BinaryCounter.d0].
    + left; exists (n'*6),n',(RC n'); repeat split; try apply InputEnd; try reflexivity; lia.
    + right; right; exists (n'*6),n',(RC n'); repeat split; try apply InputEnd; try reflexivity; lia.
  - left; eauto 8.
  - right; left; eauto 8.
Qed.

(* q counts words; z is the binary weight of the 0011 words. *)
Inductive Stack (base:side): nat -> nat -> side -> Prop :=
| StackNil: Stack base 0 0 base
| StackD q z l: Stack base q z l -> Stack base (q+1) (z+2^q) (l <* cd0)
| StackT q z l: Stack base q z l -> Stack base (q+1) z (l <* cd1).

Lemma Stack_cases base q z l: Stack base q z l ->
  (z=0%nat /\ l=base <* cd1^^q) \/
  (exists q' z' l' j, Stack base q' z' l' /\ q=q'+1+j /\ z=z'+2^q' /\
    l=l' <* cd0 <* cd1^^j).
Proof.
  induction 1 as [|q z l H IH|q z l H IH].
  - left; split; reflexivity.
  - right; exists q,z,l,0%nat; repeat split; auto; lia.
  - destruct IH as [[-> ->]|[q' [z' [l' [j [HS [-> [-> ->]]]]]]]].
    + left; split; [reflexivity|]; rewrite Nat.add_1_r, lpow_S; reflexivity.
    + right; exists q',z',l',(j+1); repeat split; auto; try lia.
      rewrite Nat.add_1_r, lpow_S; reflexivity.
Qed.

Definition CV h q z v := (v+2)*2^(h+q)+z*4*2^h.
Definition CW h q z w := z*2^h+w*2^(h+q).
Definition rank f u p := f*(u+1)-p.
Definition measure h q z v w := rank (CV h q z v) (CW h q z w) (2^(h+q)).

Lemma rank_forward f u p: 0<p -> p*2<=f -> rank f u (p*2)<rank f u p.
Proof. unfold rank; nia. Qed.
Lemma rank_backward f u u' p p': u'<u -> 0<p' -> p<=f -> p'<=f ->
  rank f u' p'<rank f u p.
Proof. unfold rank; nia. Qed.
Lemma CV_bound h q z v: 2^(h+q)<=CV h q z v.
Proof. unfold CV; nia. Qed.
Lemma CV_D h q z v: CV h (q+1) (z+2^q) v = CV h q z (v*2+6).
Proof. unfold CV; arith. Qed.
Lemma CW_D h q z w: CW h (q+1) (z+2^q) w = CW h q z (w*2+1).
Proof. unfold CW; arith. Qed.
Lemma CV_T h q z v: CV h (q+1) z v = CV h q z (v*2+2).
Proof. unfold CV; arith. Qed.
Lemma CW_T h q z w: CW h (q+1) z w = CW h q z (w*2).
Proof. unfold CW; arith. Qed.
Lemma CV_Z h q z j v:
  CV h (q+1) z ((v*2+2)*2^j) = CV h (q+1+j) (z+2^q) (v*2).
Proof. unfold CV; arith. Qed.
Lemma CW_Z h q z j w:
  CW h (q+1) z (w*2*2^j)+2^(h+q) = CW h (q+1+j) (z+2^q) (w*2).
Proof. unfold CW; arith. Qed.

Lemma measure_D h q z v w:
  measure h (q+1) (z+2^q) v w < measure h q z (v*2+6) (w*2+1).
Proof.
  unfold measure; rewrite CV_D,CW_D.
  replace (2^(h+(q+1))) with (2^(h+q)*2) by arith.
  apply rank_forward; unfold CV; arith.
Qed.
Lemma measure_T h q z v w:
  measure h (q+1) z v w < measure h q z (v*2+2) (w*2).
Proof.
  unfold measure; rewrite CV_T,CW_T.
  replace (2^(h+(q+1))) with (2^(h+q)*2) by arith.
  apply rank_forward; unfold CV; arith.
Qed.
Lemma measure_Z h q z j v w:
  measure h (q+1) z ((v*2+2)*2^j) (w*2*2^j) <
  measure h (q+1+j) (z+2^q) (v*2) (w*2).
Proof.
  unfold measure; rewrite CV_Z.
  apply rank_backward.
  - rewrite <-CW_Z; arith.
  - arith.
  - apply CV_bound.
  - rewrite <-CV_Z; apply CV_bound.
Qed.

Lemma CoreExit_split l r h q:
  l <* [0;1] <* cd1^^h <* [1;1] <* cd1^^q {{C}}> rd0 *> r -->+
  l <| rd0^^(h+q+1) *> [1;0] *> r.
Proof. es' h q & l r. Qed.

Lemma CoreReturn l h q z s v w r:
  Stack (l <* [0;1] <* cd1^^h <* [1;1]) q z s -> Input v w r ->
  exists w' r', Num (CV h q z v) w' r' /\ w'<=w*2^(h+q) /\
    s {{C}}> r -->* l <| r'.
Proof.
  remember (measure h q z v w) as t eqn:E; gen q z s v w r.
  induction t using strong_induction; intros q z s v w E r HS HI.
  destruct (Input_cases _ _ _ HI) as
    [[v' [w' [r' [HR [-> [-> ->]]]]]]|
    [[v' [w' [r' [HR [-> [-> ->]]]]]]|[v' [w' [r' [HR [-> [-> ->]]]]]]]].
  - destruct (Stack_cases _ _ _ _ HS) as [[-> ->]|[q' [z' [s' [j [HL [-> [-> ->]]]]]]]].
    + exists (w'*2^(h+q+1)),(rd0^^(h+q+1) *> [1;0] *> r'); repeat split.
      * replace (CV h q 0 (v'*2)) with ((v'+1)*2^(h+q+1)) by (unfold CV; arith).
        apply Num_zeros, (proj2 (Input_Num _ _ _ HR)).
      * arith.
      * apply progress_evstep, CoreExit_split.
    + destruct (H _ ltac:(rewrite E; apply measure_Z) _ _ _ _ _ eq_refl _
        (StackT _ _ _ _ HL) (Input_zeros _ _ _ j (InputT _ _ _ HR)))
        as [ww [rr [HN [HW HE]]]].
      exists ww,rr; split; [rewrite <-CV_Z; exact HN|]; split; [arith|].
      follow100 CoreZ; exact HE.
  - destruct (H _ ltac:(rewrite E; apply measure_T) _ _ _ _ _ eq_refl _
      (StackT _ _ _ _ HS) HR) as [ww [rr [HN [HW HE]]]].
    exists ww,rr; split; [rewrite <-CV_T; exact HN|]; split; [arith|].
    follow100 CoreT; exact HE.
  - destruct (H _ ltac:(rewrite E; apply measure_D) _ _ _ _ _ eq_refl _
      (StackD _ _ _ _ HS) HR) as [ww [rr [HN [HW HE]]]].
    exists ww,rr; split; [rewrite <-CV_D; exact HN|]; split; [arith|].
    follow100 CoreD; exact HE.
Qed.

Lemma CoreCall l h m:
  exists w r, Num ((m*12+8)*2^h) w r /\ w<=m*2^(h+1) /\
    l |> rd1^^h *> rm3 *> RC m -->+ l <| r.
Proof.
  destruct (CoreReturn l h 1 1 _ _ _ _ (StackD _ _ _ _ (StackNil _)) (InputEnd m))
    as [w [r [HN [HW HE]]]].
  exists w,r; split; [|split; [exact HW|follow10 CoreEnter; exact HE]].
  replace ((m*12+8)*2^h) with (CV h 1 1 (m*6)) by (unfold CV; arith).
  exact HN.
Qed.

Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX; finish.
Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC_ones n a: rd1^^a *> RC n = RC ((n+1)*2^a-1).
Proof.
  induction a.
  - cbn [lpow]; replace ((n+1)*2^0-1) with n by arith; reflexivity.
  - rewrite lpow_S; change (rd1 *> (rd1^^a *> RC n) = RC ((n+1)*2^S a-1)).
    rewrite IHa; unfold RC.
    replace ((n+1)*2^S a-1) with (((n+1)*2^a-1)*2+1) by arith.
    rewrite BinInc_mul2add1; reflexivity.
Qed.

Lemma RNum n w r: Num n w r -> forall l a,
  exists w' r', Num ((n+1)*2^a) w' r' /\ w'<=w*2^a /\
    l |> rd1^^a *> r -->+ l <| r'.
Proof.
  induction 1 as [n|m|m|n w r H IH|n w r H IH]; intros l a.
  - exists 0%nat,(RC ((n+1)*2^a)); split; [apply NumOrd|]; split; [lia|].
    rewrite RC_ones.
    assert (0<(n+1)*2^a) by arith.
    applys_eq (RC_Inc ((n+1)*2^a-1) l); flia.
  - exists (m*2^a),(rd0^^a *> [1;0] *> RC m); repeat split.
    + apply Num_zeros,NumShort1.
    + lia.
    + follow10 RInc; finish.
  - divmod2_cases m.
    + exists (n'*2^(a+1)),(rd0^^(a+1) *> [1;0] *> RC n'); split.
      * replace ((n'*2*6+1+1)*2^a) with ((n'*6+1)*2^(a+1)) by arith.
        apply Num_zeros,NumShort1.
      * split; [arith|]. unfold RC; rewrite BinInc_mul2; cbn [BinaryCounter.d0].
        change (l |> rd1^^a *> rd1 *> [0;0] *> RC n' -->+
          l <| rd0^^(a+1) *> [1;0] *> RC n').
        rewrite lpow_add' with (n2:=1%nat).
        follow10 RInc; finish.
    + destruct (CoreCall l a n') as [w [r [HN [HW HE]]]].
      exists w,r; split.
      * replace (((n'*2+1)*6+1+1)*2^a) with ((n'*12+8)*2^a) by arith; exact HN.
      * split; [arith|]. unfold RC; rewrite BinInc_mul2add1; exact HE.
  - exists (w*2*2^a),(rd0^^a *> rd1 *> r); repeat split.
    + apply Num_zeros,NumD,H.
    + lia.
    + follow10 RInc; finish.
  - destruct (IH l (a+1)) as [w' [r' [HN [HW HE]]]].
    exists w',r'; split.
    + replace ((n*2+1+1)*2^a) with ((n+1)*2^(a+1)) by arith; exact HN.
    + split; [arith|].
      change (l |> rd1^^a *> rd1 *> r -->+ l <| r').
      rewrite lpow_add' with (n2:=1%nat); exact HE.
Qed.

Lemma Num_step n w r l: Num n w r ->
  exists w' r', Num (n+1) w' r' /\ w'<=w /\ l |> r -->+ l <| r'.
Proof.
  intros H; destruct (RNum _ _ _ H l 0) as [w' [r' [HN [HW HE]]]].
  cbn [Nat.pow lpow] in *; repeat rewrite Nat.mul_1_r in *; eauto 8.
Qed.

Lemma Num_increments len k n w r: k<2^len -> Num n w r ->
  exists w' r', Num (n+k+1) w' r' /\ w'<=w /\
    LC len k |> r -->+ LC len 0 <| r'.
Proof.
  gen n w r; induction k; intros n w r HK HN.
  - rewrite Nat.add_0_r; apply Num_step,HN.
  - destruct (Num_step _ _ _ (LC len (S k)) HN) as [w1 [r1 [HN1 [HW1 HE1]]]].
    destruct (IHk _ _ _ ltac:(lia) HN1) as [w2 [r2 [HN2 [HW2 HE2]]]].
    exists w2,r2; split.
    + applys_eq HN2; flia.
    + split; [lia|]. follow11 HE1.
      change (LC len (1+k) <| r1 -->+ LC len 0 <| r2).
      eapply progress_trans; [apply LC_Inc; lia|exact HE2].
Qed.
Lemma Finish_num len k n w r: k<2^len -> w*8<=n+k+1 -> Num n w r ->
  LC len k |> r -->+ LC len 0 <| RC (n+k+1).
Proof.
  intros HK HB HN; destruct (Num_increments _ _ _ _ _ HK HN) as [w' [r' [HN' [HW HE]]]].
  assert (w'=0%nat) by (pose proof (Num_bound _ _ _ HN'); lia).
  rewrite (Num_ordinary _ _ _ HN' H) in HE; exact HE.
Qed.


Definition cfg len n := LC len 0 <| RC n.
Definition RP h n r := BinDec2 [0] [1] [0;0] h n r.
Lemma RP_Inc h n r l: 1+n<2^(h+1) ->
  l |> RP h (1+n) r -->+ l <| RP h n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RP_Incs len k h n r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RP h n r -->* LC len k |> RP h 0 r.
Proof.
  gen k; induction n; intros k HK Hn; [finish|].
  eapply evstep_trans; [apply progress_evstep,RP_Inc; lia|].
  rewrite Nat.add_succ_r.
  eapply evstep_trans; [apply progress_evstep,LC_Inc; lia|].
  follow IHn; try lia; finish.
Qed.
Lemma RP_Drain len k h n r: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RP h (n+k+1) r -->+ LC len 0 <| RP h n r.
Proof.
  gen n; induction k; intros n HK Hn.
  - replace (n+0+1) with (1+n) by lia; apply RP_Inc; lia.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    eapply progress_evstep_trans; [apply RP_Inc; lia|].
    change (LC len (1+k) <| RP h (n+k+1) r -->* LC len 0 <| RP h n r).
    eapply evstep_trans; [apply progress_evstep,LC_Inc; lia|].
    apply progress_evstep,IHk; lia.
Qed.
Lemma Low_run len k h r: k+(2^(h+1)-2)<2^len ->
  LC len (k+(2^(h+1)-2)) |> [1] *> rd0^^h *> r -->*
  LC len k |> rd1^^h *> [1] *> r.
Proof.
  intros HK.
  replace (2^(h+1)-2) with ((2^h-1)*2) in * by arith.
  epose proof (RP_Incs len k h ((2^h-1)*2) r HK ltac:(arith)) as H.
  unfold RP in H; rewrite BinDec2_O,BinDec2_mul2,BinDec_full in H; exact H.
Qed.
Lemma Low_run0 len k h r: k+(2^(h+1)-1)<2^len ->
  LC len (k+(2^(h+1)-1)) |> [0] *> rd0^^h *> r -->*
  LC len k |> rd1^^h *> [1] *> r.
Proof.
  intros HK; epose proof (RP_Incs len k h (2^(h+1)-1) r HK ltac:(arith)) as H.
  unfold RP in H; rewrite BinDec2_O,BinDec2_full in H.
  rewrite lpow_rotate' in H; exact H.
Qed.
Lemma LC_Ov len r: LC len 0 <| r -->+ LC len (2^len-1) |> [1] *> r.
Proof. unfold LC; rewrite BinDec_O,BinDec_full; apply LOv. Qed.
Lemma Append0 len k a r: k<2^len ->
  LC len k |> rd1^^(a*2) *> rm1 *> r -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> [1;0] *> r.
Proof.
  intros HK; unfold LC; follow10 ROv1_0.
  rewrite BinDec_mulpow2sub1 by arith; finish.
Qed.
Lemma Append1 len k a r: k<2^len ->
  LC len k |> rd1^^(a*2+1) *> rm1 *> r -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0] *> r.
Proof.
  intros HK; unfold LC; follow10 ROv1_1.
  rewrite BinDec_mulpow2sub1 by arith; finish.
Qed.
Lemma Finish_left len k v w r: 0<k<2^len -> w*8<=v+k -> Num v w r ->
  LC len k <| r -->+ cfg len (v+k).
Proof.
  intros HK HB HN; destruct k; [lia|].
  eapply progress_evstep_trans; [apply LC_Inc; lia|]. unfold cfg.
  replace (v+S k) with (v+k+1) by lia.
  apply progress_evstep,Finish_num with (w:=w); assumption || lia.
Qed.
Lemma Finish_short len k m: k<2^len -> m*2<=k+2 ->
  LC len k |> [1;0] *> RC m -->+ cfg len (k+2+m*6).
Proof.
  intros; unfold cfg; replace (k+2+m*6) with (m*6+1+k+1) by lia.
  apply Finish_num with (w:=m); try lia; apply NumShort1.
Qed.

Lemma Start_low len h m: h<len ->
  cfg len ((m*2+1)*2^h) -->+
  LC len (2^len+1-2^(h+1)) |> rd1^^h *> rm1 *> RC m.
Proof.
  intros HH; assert (HP:2^(h+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  unfold cfg; follow10 LC_Ov.
  unfold RC; rewrite BinInc_mulpow2,BinInc_mul2add1; cbn [BinaryCounter.d0]; fold RC.
  replace (2^len-1) with ((2^len+1-2^(h+1))+(2^(h+1)-2)) by arith.
  eapply evstep_trans; [apply Low_run; arith|finish].
Qed.
Lemma Zero_low len k h m: k<2^len -> 2^(h+1)<=k+1 ->
  LC len k |> [0] *> RC ((m*2+1)*2^h) -->*
  LC len (k+1-2^(h+1)) |> rd1^^h *> rm1 *> RC m.
Proof.
  intros HK HH; unfold RC.
  rewrite BinInc_mulpow2,BinInc_mul2add1; cbn [BinaryCounter.d0]; fold RC.
  replace k with ((k+1-2^(h+1))+(2^(h+1)-1)) at 1 by arith.
  eapply evstep_trans; [apply Low_run0; arith|finish].
Qed.
Lemma zero_budget len k h m s: k<2^len -> ((m*2+1)*2^h)*2<=k+1 ->
  let k' := ((k+1-2^(h+1))*2+1)*2^s-1 in
  k'<2^(len+1+s) /\ m*2<=k'+1 /\ 0<k'+2+m*6<2^(len+1+s+1).
Proof.
  intros HK HM; cbn zeta.
  assert (HP: 2^(h+1)<=k+1) by arith.
  assert (HM':m*4+2<=2^len) by nia.
  arith.
Qed.

Lemma Zero_return m: forall len k, 2<=len -> k<2^len -> m*2<=k+1 ->
  exists len' n, 2<=len' /\ 0<n<2^(len'+1) /\
    LC len k |> [0] *> RC m -->+ cfg len' n.
Proof.
  induction m using strong_induction; intros len k HL HK HM.
  lowbit_cases m.
  - exists len,(k+1); split; [lia|]; split; [arith|].
    replace (k+1) with (0+k+1) by lia; unfold cfg.
    change (LC len k |> RC 0 -->+ LC len 0 <| RC (0+k+1)).
    apply Finish_num with (w:=0%nat); try lia; apply NumOrd.
  - assert (HP:2^(i+1)<=k+1) by arith.
    divmod2_cases i.
    + pose proof (zero_budget len k (n'*2) x (n'*3) HK HM) as [HK' [HM' HN]].
      exists (len+1+n'*3),(((k+1-2^(n'*2+1))*2+1)*2^(n'*3)-1+2+x*6).
      split; [lia|]; split; [exact HN|].
      eapply evstep_progress_trans; [apply Zero_low; assumption|].
      eapply progress_evstep_trans; [apply Append0; arith|].
      apply progress_evstep,Finish_short; lia.
    + pose proof (zero_budget len k (n'*2+1) x (n'*3+2) HK HM) as [HK' [HM' HN]].
      destruct (H x ltac:(arith) (len+1+(n'*3+2))
        (((k+1-2^(n'*2+1+1))*2+1)*2^(n'*3+2)-1) ltac:(lia) HK' HM')
        as [len' [v [HL' [HV HE]]]].
      exists len',v; split; [exact HL'|]; split; [exact HV|].
      eapply evstep_progress_trans; [apply Zero_low; assumption|].
      eapply progress_evstep_trans; [apply Append1; arith|].
      apply progress_evstep; exact HE.
Qed.

Lemma RP_initial h r: RP h (2^(h+1)-2) r = [1] *> rd0^^h *> r.
Proof.
  unfold RP; replace (2^(h+1)-2) with ((2^h-1)*2) by arith.
  rewrite BinDec2_mul2,BinDec_full; reflexivity.
Qed.
Lemma RP_middle h r: RP (h+1) (2^(h+1)-2) r = [1] *> rd0^^h *> [0;0;1] *> r.
Proof.
  unfold RP; replace (2^(h+1)-2) with (((0*2+1)*2^h-1)*2) by arith.
  rewrite BinDec2_mul2; replace (h+1) with (0+1+h) by lia.
  rewrite BinDec_mulpow2sub1 by arith; rewrite BinDec_O; reflexivity.
Qed.
Lemma Corner_mid h r:
  LC (h+1) 0 <| rd0^^(h+1) *> r -->+
  LC (h+1) 0 <| [1] *> rd0^^h *> [0;0;1] *> r.
Proof.
  follow10 LC_Ov; rewrite <-RP_initial,<-RP_middle.
  replace (2^(h+1+1)-2) with ((2^(h+1)-2)+(2^(h+1)-1)+1) by arith.
  apply progress_evstep,RP_Drain; arith.
Qed.
Lemma Corner_front h r:
  LC (h+1) 0 <| rd0^^(h+1) *> r -->+
  LC (h+2) (2^(h+1)) |> rd1^^h *> [1;0;1] *> r.
Proof.
  follow10 Corner_mid; follow100 LC_Ov.
  change (LC (h+1) (2^(h+1)-1) |> [1;1] *> rd0^^h *> [0;0] *> [1] *> r -->*
    LC (h+2) (2^(h+1)) |> rd1^^h *> [1;0;1] *> r).
  rewrite (lpow_rotate' [0] [0;0]).
  change (LC (h+1) (2^(h+1)-1) |> rd1^^0 *> rm1 *> rd0^^h *> [1] *> r -->*
    LC (h+2) (2^(h+1)) |> rd1^^h *> [1;0;1] *> r).
  eapply evstep_trans; [apply progress_evstep,(Append0 _ _ 0); arith|].
  replace (h+1+1+0*3) with (h+2) by lia.
  replace (((2^(h+1)-1)*2+1)*2^(0*3)-1) with (2^(h+1)*2-2) by arith.
  change (LC (h+2) (2^(h+1)*2-2) |> [1] *> [0] *> rd0^^h *> [1] *> r -->*
    LC (h+2) (2^(h+1)) |> rd1^^h *> [1;0;1] *> r).
  rewrite <-(lpow_rotate' [0;0] [0]).
  replace (2^(h+1)*2-2) with (2^(h+1)+(2^(h+1)-2)) by arith.
  eapply evstep_trans; [apply Low_run; arith|finish].
Qed.

Inductive Valid: nat -> nat -> Prop :=
| ValidSmall len n: 2<=len -> 0<n -> n<2^(len+1) -> Valid len n
| ValidEven len n: 2<=len -> 0<n -> n<2^(len+1) -> Valid len (n*2).

Lemma Round_odd len m: 2<=len -> m<2^len ->
  cfg len (m*2+1) -->+ cfg (len+1) (2^(len+1)+m*6).
Proof.
  intros HL HM; replace (m*2+1) with ((m*2+1)*2^0) at 1 by arith.
  eapply progress_evstep_trans; [apply Start_low; lia|].
  change (LC len (2^len+1-2) |> rd1^^(0*2) *> rm1 *> RC m -->*
    cfg (len+1) (2^(len+1)+m*6)).
  eapply evstep_trans; [apply progress_evstep,(Append0 _ _ 0); arith|].
  replace (len+1+0*3) with (len+1) by lia.
  replace (2^(len+1)+m*6) with
    (((2^len+1-2)*2+1)*2^(0*3)-1+2+m*6) by arith.
  apply progress_evstep,Finish_short; arith.
Qed.
Lemma Round_odd_valid len m: 2<=len -> m<2^len ->
  Valid (len+1) (2^(len+1)+m*6).
Proof.
  intros; replace (2^(len+1)+m*6) with ((2^len+m*3)*2) by arith.
  apply ValidEven; try lia; arith.
Qed.
Lemma low_budget len i m s: 0<i -> i<len -> 2<=s -> (m*2+1)*2^i<2^len*4 ->
  let k := ((2^len+1-2^(i+1))*2+1)*2^s-1 in
  k<2^(len+1+s) /\ m*2<=k+1 /\ 0<k+2+m*6<2^(len+1+s+1).
Proof.
  intros HI HL HS HM; cbn zeta.
  assert (HP:2^(i+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  assert (HU:2<=2^i) by (change (2^1<=2^i); apply Nat.pow_le_mono_r; lia).
  assert (HZ:4<=2^s) by (change (2^2<=2^s); apply Nat.pow_le_mono_r; lia).
  assert (HB:m<=((2^len+1-2^(i+1))*2+1)*2) by arith.
  assert (Hm:m<2^len) by nia.
  arith.
Qed.
Lemma Round_low len i m: 0<i -> i<len -> (m*2+1)*2^i<2^len*4 ->
  exists len' n, cfg len ((m*2+1)*2^i) -->+ cfg len' n /\ Valid len' n.
Proof.
  intros HI HL HM; assert (HP:2^(i+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  divmod2_cases i.
  - pose proof (low_budget len (n'*2) m (n'*3) HI HL ltac:(lia) HM) as [HK [HB HN]].
    exists (len+1+n'*3),(((2^len+1-2^(n'*2+1))*2+1)*2^(n'*3)-1+2+m*6); split.
    + eapply progress_evstep_trans; [apply Start_low; lia|].
      eapply evstep_trans; [apply progress_evstep,Append0; arith|].
      apply progress_evstep,Finish_short; lia.
    + apply ValidSmall; lia.
  - pose proof (low_budget len (n'*2+1) m (n'*3+2) HI HL ltac:(lia) HM) as [HK [HB HN]].
    destruct (Zero_return m (len+1+(n'*3+2))
      (((2^len+1-2^(n'*2+1+1))*2+1)*2^(n'*3+2)-1) ltac:(lia) HK HB)
      as [len' [v [HL' [HV HE]]]].
    exists len',v; split.
    + eapply progress_evstep_trans; [apply Start_low; lia|].
      eapply evstep_trans; [apply progress_evstep,Append1; arith|].
      apply progress_evstep; exact HE.
    + apply ValidSmall; lia.
Qed.

Lemma Short_even_cut len k a r: k<2^len ->
  LC len k |> rd1^^(a*2) *> [1;0;1;1] *> r -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| r.
Proof.
  intros HK; unfold LC; follow10 ShortEven.
  rewrite BinDec_mulpow2,BinDec_mul2add1 by arith; finish.
Qed.
Lemma Short_odd_cut len k a r: k<2^len ->
  LC len k |> rd1^^(a*2+1) *> [1;0;1;1;0;0] *> r -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| rd1 *> r.
Proof.
  intros HK; unfold LC; follow10 ShortOdd.
  rewrite BinDec_mulpow2,BinDec_mul2add1 by arith; finish.
Qed.
Lemma corner_budget len s: 2<=len ->
  8<=(2^len*2+1)*2^s /\ (2^len*2+1)*2^s+6<2^(len+2+s).
Proof.
  intros HL; assert (4<=2^len) by (change (2^2<=2^len); apply Nat.pow_le_mono_r; lia).
  arith.
Qed.
Lemma Round_corner_odd len m: 2<=len -> m<=1 ->
  exists len' n, cfg len ((m*2+1)*2^len) -->+ cfg len' n /\ Valid len' n.
Proof.
  intros HL HM; destruct len as [|h]; [lia|].
  replace (S h) with (h+1) in * by lia; divmod2_cases h.
  - pose proof (corner_budget (n'*2+1) (n'*3+1) HL) as [HK HB].
    exists (n'*2+2+1+(n'*3+1)),(m*6+(2^(n'*2+1)*2+1)*2^(n'*3+1)); split.
    + unfold cfg at 1; unfold RC.
      rewrite BinInc_mulpow2,BinInc_mul2add1; cbn [BinaryCounter.d0]; fold RC.
      follow10 Corner_front.
      eapply evstep_trans; [apply progress_evstep,Short_even_cut; arith|].
      apply progress_evstep,Finish_left with (w:=m); try arith; apply NumShort0.
    + apply ValidSmall; try lia; arith.
  - pose proof (corner_budget (n'*2+1+1) (n'*3+2) HL) as [HK HB].
    exists (n'*2+1+2+1+(n'*3+2)),(m*2+1+(2^(n'*2+1+1)*2+1)*2^(n'*3+2)); split.
    + unfold cfg at 1; unfold RC.
      rewrite BinInc_mulpow2,BinInc_mul2add1; cbn [BinaryCounter.d0]; fold RC.
      follow10 Corner_front.
      eapply evstep_trans; [apply progress_evstep,Short_odd_cut; arith|].
      apply progress_evstep,Finish_left with (w:=0%nat); try arith.
      rewrite <-BinInc_mul2add1; apply NumOrd.
    + apply ValidSmall; try lia; arith.
Qed.
Lemma Round_corner_double len: 2<=len ->
  cfg len (2^len*2) -->+ cfg (len+1) (2^len*7).
Proof.
  intros HL; destruct len as [|h]; [lia|]. replace (S h) with (h+1) in * by lia.
  unfold cfg at 1; unfold RC.
  rewrite Nat.mul_comm,BinInc_mulpow2; cbn [BinaryCounter.d0].
  change (LC (h+1) 0 <| rd0^^(h+1) *> [0;0;0;1;0;0] *> 0inf -->+
    cfg (h+1+1) (2^(h+1)*7)).
  follow10 Corner_front; cbn [Str_app]; repeat rewrite <-(const_unfold _ 0).
  follow100 DoubleCorner.
  replace (h+1+1) with (h+2) by lia.
  replace (2^(h+1)*7) with (2^(h+1)*6+2^(h+1)) by lia.
  apply progress_evstep,Finish_left with (w:=0%nat); try arith.
  replace (2^(h+1)*6) with (3*2^(h+2)) by arith.
  replace (rd0^^(h+2) *> rd1^^2 *> 0inf) with (RC (3*2^(h+2))).
  - apply NumOrd.
  - unfold RC; rewrite BinInc_mulpow2; reflexivity.
Qed.

Lemma Valid_bounds len n: Valid len n -> 2<=len /\ 0<n /\ n<2^len*4.
Proof. destruct 1; arith. Qed.
Lemma Valid_odd_bound len m: Valid len (m*2+1) -> m<2^len.
Proof. inversion 1; subst; arith. Qed.
Lemma Valid_double len: 2<=len -> Valid (len+1) (2^len*7).
Proof.
  intros HL; destruct len as [|len]; [lia|].
  rewrite Nat.pow_succ_r'.
  replace (2*2^len*7) with ((2^len*7)*2) by lia.
  apply ValidEven; try lia; arith.
Qed.
Lemma closed len n: Valid len n ->
  exists len' n', cfg len n -->+ cfg len' n' /\ Valid len' n'.
Proof.
  intros HV; pose proof (Valid_bounds _ _ HV) as [HL [HN HB]].
  lowbit_cases n; [lia|].
  destruct i as [|i].
  - replace ((x*2+1)*2^0) with (x*2+1) in * by arith.
    pose proof (Valid_odd_bound _ _ HV) as HX.
    exists (len+1),(2^(len+1)+x*6); split;
      [apply Round_odd|apply Round_odd_valid]; assumption.
  - destruct (Nat.lt_ge_cases (S i) len) as [HI|HI].
    + apply Round_low; lia.
    + set (t := (x*2+1)*2^(S i-len)).
      assert (E:(x*2+1)*2^S i=t*2^len).
      { unfold t; replace (S i) with (len+(S i-len)) at 1 by lia; arith. }
      assert (HT:t=1%nat \/ t=2%nat \/ t=3%nat) by nia.
      rewrite E; destruct HT as [-> | [-> | ->]].
      * change (exists len' n', cfg len ((0*2+1)*2^len) -->+ cfg len' n' /\ Valid len' n').
        apply Round_corner_odd; lia.
      * rewrite Nat.mul_comm.
        exists (len+1),(2^len*7); split; [apply Round_corner_double|apply Valid_double]; lia.
      * change (exists len' n', cfg len ((1*2+1)*2^len) -->+ cfg len' n' /\ Valid len' n').
        apply Round_corner_odd; lia.
Qed.
Lemma cfg_nonhalt len n: Valid len n -> ~halts tm (cfg len n).
Proof.
  intros HV.
  apply (progress_nonhalt_cond tm (nat*nat) (len,n)
    (fun '(l,n)=>cfg l n) (fun '(l,n)=>Valid l n)).
  - intros [L n0] H; destruct (closed _ _ H) as [L' [n' [HE HV']]].
    exists (L',n'); auto.
  - exact HV.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt with (c':=cfg 4 10).
  - change (LC 4 9 <| RC 1 -->* cfg 4 (1+9)).
    apply progress_evstep,Finish_left with (w:=0%nat); try (cbn; lia); apply NumOrd.
  - apply cfg_nonhalt,ValidSmall; cbn; lia.
Qed.
End TM114.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_TM115.v. *)
Module SOC23_TM115.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
End SOC23_TM115.

(* SOC23_TM115.TM115 *)
Module TM115.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC23_TM115.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_0RF1LB_0LB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2 l r n m:
  l |> rd1^^n *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(n+m+2) *> [1;0] *> r.
Proof. es. Qed.


Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. es' n & l. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. es' n & l. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.


Lemma RC2_Merge len k h b i m:
  LC len k |> RC2 h 0 (((((m*2+1)*2^i)*2+1)*2^b)-1) -->+
  LC len k <| RC2 (i+(h+b+2)) (((2^i-1)*2+1)*2^(h+b+2)-1) m.
Proof. solve_rule ROv2. Qed.
Lemma RC2_Merge_blank len k h b:
  LC len k |> RC2 h 0 ((0*2+1)*2^b-1) -->+ LC len k <| RC (2^(h+b+2)).
Proof. solve_rule ROv2. Qed.

Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => 1<=len /\ n+m*2^(h+2)<=k<2^len /\ n<2^(h+1) /\ h+2<=len
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma merge_height len h b:
  h+2<=len -> (2^b-1)*2^(h+2)<2^len -> h+b+2<=len.
Proof.
  destruct b as [|b]; intros; [lia|].
  assert (h+b+2<len) by (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
  lia.
Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      assert (i<len) by (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    destruct (lowbitS_cases' m) as [u b].
    destruct (lowbit_cases' u) as [|m i].
    + eexists (cfgL _ _ _); split; [apply RC2_Merge_blank|].
      assert (h+b+2<=len) by (apply merge_height; arith).
      assert (2^(h+b+2)<=2^len) by (apply Nat.pow_le_mono_r; lia).
      cbn [P]; arith.
    + destruct k as [|k]; [arith|].
      eexists (cfgR2 _ _ _ _ _); split.
      * eapply progress_evstep_trans; [apply RC2_Merge|].
        apply progress_evstep,LC_Inc; lia.
      * assert (i+(h+b+2)+1<len) by (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
        cbn [P]; arith.
Qed.

Lemma init: c0 -->* to_config (cfgL 4 9 1).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM115.

From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2.
Require Import NArith Lia ZifyNat List String.

(* SOC23_TM119Halt.TM119 *)
Module TM119.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.Eqb BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia ZifyNat List String.


Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_0RF1LB_1RD---").
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Definition addN p k := match k with N0=>p | Npos k=>Pos.add p k end.
Lemma addN_succ p k: addN p (N.succ k) = addN (Pos.succ p) k.
Proof. destruct k; cbn [addN N.succ]; lia. Qed.

Lemma paired k p q l r:
  (k<=rest p)%N -> (k<=rest q)%N ->
  BinaryCounter ld0 ld1 l p |> BinaryCounter rd0 rd1 r q -->*
  BinaryCounter ld0 ld1 l (addN p k) |> BinaryCounter rd0 rd1 r (addN q k).
Proof.
  revert p q; induction k using N.peano_ind; intros p q Hp Hq.
  - apply evstep_refl.
  - assert (Hp0: rest p<>0%N) by lia.
    assert (Hq0: rest q<>0%N) by lia.
    pose proof (rest_S p Hp0); pose proof (rest_S q Hq0).
    rewrite !addN_succ.
    eapply evstep_trans.
    + apply progress_evstep; apply BinaryCounter.RInc.
      * intros; change (rd0^^n *> rd1 *> r0) with (rd0^^n *> [1] *> [0;0] *> r0).
        apply RInc.
      * apply not_full_iff_rest; exact Hq0.
    + eapply evstep_trans.
      * apply progress_evstep; apply BinaryCounter.LInc; [apply LInc|].
        apply not_full_iff_rest; exact Hp0.
      * apply IHk; lia.
Qed.

(* Binary words have a leading sentinel in their positive representation;
   it is not a tape digit.  No unary large integer is computed. *)
Fixpoint word (d0 d1:list Sym) p := match p with
  | xH=>nil | xO p=>d0++word d0 d1 p | xI p=>d1++word d0 d1 p end.
Lemma word_spec d0 d1 p r:
  word d0 d1 p *> r = BinaryCounter d0 d1 r p.
Proof. induction p; cbn; rewrite ?Str_app_assoc, ?IHp; reflexivity. Qed.

(* This check permits omitted trailing blanks, but never treats a failed
   match as a halt.  Proposal parsers need no soundness assumptions. *)
Fixpoint peel (w s:list Sym) : option (list Sym) := match w with
  | nil=>Some s
  | b::w=>match s with
    | nil=>if sym_eqb b 0 then peel w nil else None
    | c::s=>if sym_eqb b c then peel w s else None end end.
Lemma peel_spec w s r: peel w s=Some r -> s *> 0inf = w *> r *> 0inf.
Proof.
  revert s; induction w as [|b w IH]; intros s H; cbn in H.
  - injection H as <-; reflexivity.
  - destruct s as [|c s].
    + destruct (sym_eqb_spec b 0); try discriminate; subst.
      specialize (IH _ H); cbn; rewrite <-IH; apply const_unfold.
    + destruct (sym_eqb_spec b c); try discriminate; subst.
      specialize (IH _ H); cbn; rewrite <-IH; reflexivity.
Qed.

Definition State := (Q * list Sym * list Sym)%type.
Definition denote (s:State) := let '(q,l,r):=s in l *> 0inf {{q}}> r *> 0inf.
Fixpoint room p : N := match p with
  | xH=>N0 | xI p=>N.double (room p) | xO p=>N.succ_double (room p) end.
Lemma room_spec p: room p=rest p.
Proof.
  induction p; cbn [room]; rewrite ?IHp.
  - unfold rest; cbn [log2 pow2']; pose proof (pow2'_log2_ge p).
    rewrite N.double_spec; lia.
  - rewrite N.succ_double_spec,rest_mul2; lia.
  - reflexivity.
Qed.

Fixpoint decode_left (l:list Sym) : positive * list Sym := match l with
  | S0::S1::l=>let '(p,r):=decode_left l in (xO p,r)
  | S1::S1::l=>let '(p,r):=decode_left l in (xI p,r)
  | _=>(xH,l) end.
Lemma decode_left_spec l p r: decode_left l=(p,r) ->
  l *> 0inf=BinaryCounter ld0 ld1 (r *> 0inf) p.
Proof.
  revert l p r; fix IH 1; intros [|[] [|[] l]] p r H;
    cbn [decode_left] in H; try (injection H as <- <-; reflexivity).
  all: destruct (decode_left l) as [p' r'] eqn:E; injection H as <- <-;
    cbn [BinaryCounter Str_app]; rewrite (IH _ _ _ E); reflexivity.
Qed.
Definition put b (v:positive * list Sym) :=
  let '(p,r):=v in (match b with S0=>xO p | S1=>xI p end,r).
Fixpoint decode_right n (r:list Sym) : positive * list Sym := match n with
  | O=>(xH,r)
  | S n=>match r with
    | b::S0::S0::r=>put b (decode_right n r)
    | nil=>put S0 (decode_right n nil)
    | b::nil | b::S0::nil=>put b (decode_right n nil)
    | _=>(xH,r) end end.
Lemma decode_right_spec n r p t: decode_right n r=(p,t) ->
  r *> 0inf=BinaryCounter rd0 rd1 (t *> 0inf) p.
Proof.
  revert r p t; induction n as [|n IHn]; intros r p t H.
  - injection H as <- <-; reflexivity.
  - destruct r as [|[] [|[] [|[] r]]]; cbn [decode_right] in H;
      try (injection H as <- <-; reflexivity).
    all: match type of H with context[decode_right ?n ?r] =>
      destruct (decode_right n r) as [p' t'] eqn:E;
      cbn [put] in H; injection H as <- <-;
      cbn [BinaryCounter Str_app]; rewrite <- (IHn _ _ _ E);
      repeat rewrite <-const_unfold; reflexivity end.
Qed.
Definition right_start (r:list Sym) := match r with
  | _::S1::_ | _::_::S1::_=>false | _=>true end.
Definition accelerate (s:State) := match s with
  | (A,S0::S1::l,r)=>
    if right_start r then
    let '(p,l'):=decode_left l in
    match room p with
    | N0=>None
    | k=>let '(q,r'):=decode_right (S (log2 p)) r in
      match N.min k (room q) with
      | N0=>None
      | k=>Some (A,[0;1]++word ld0 ld1 (addN p k)++l',
                       word rd0 rd1 (addN q k)++r') end end else None
  | _=>None end.
Lemma accelerate_spec s t: accelerate s=Some t -> denote s -[tm]->* denote t.
Proof.
  unfold accelerate; destruct s as [[state l] r]; destruct state; try discriminate.
  do 2 (destruct l as [|[] l]; try discriminate).
  destruct (right_start r); try discriminate.
  destruct (decode_left l) as [p l'] eqn:Hl.
  destruct (room p) eqn:Hp; try discriminate.
  destruct (decode_right (S (log2 p)) r) as [q r'] eqn:Hr.
  destruct (N.min (N.pos p0) (room q)) eqn:Hk; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf |> r *> 0inf -[tm]->*
    (word ld0 ld1 (addN p (N.pos p1))++l') *> 0inf |>
    (word rd0 rd1 (addN q (N.pos p1))++r') *> 0inf).
  apply decode_left_spec in Hl; apply decode_right_spec in Hr.
  rewrite Hl,Hr,!Str_app_assoc,!word_spec.
  apply paired; rewrite <-!room_spec,<-Hk; [rewrite Hp; apply N.le_min_l|apply N.le_min_r].
Qed.

(* A finite zero boundary also covers the infinite blank boundary. *)
Definition edge_left n := [0;1]++ld0^^n++[1].
Lemma edge_rule n l r:
  (ld1^^n++[0]) *> l {{C}}> [1;1;1] *> r -->*
  edge_left n *> l {{A}}> [1] *> r.
Proof. unfold edge_left; es. Qed.

Definition checked_edge n (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q C then match peel (ld1^^n++[0]) l, peel [1;1;1] r with
  | Some l,Some r=>Some (A,edge_left n++l,S1::r)
  | _,_=>None end else None.
Lemma checked_edge_spec n s t:
  checked_edge n s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_edge.
  destruct (q_eqb_spec q C); try discriminate; subst.
  destruct (peel (ld1^^n++[0]) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel [1;1;1] r) as [r'|] eqn:Hr; try discriminate.
  intros H; injection H as <-; unfold denote.
  apply peel_spec in Hl; apply peel_spec in Hr.
  rewrite Hl,Hr.
  change ((ld1^^n++[0]) *> l' *> 0inf {{C}}> [1;1;1] *> r' *> 0inf -->*
    (edge_left n++l') *> 0inf {{A}}> [1] *> r' *> 0inf).
  rewrite (Str_app_assoc (edge_left n)); apply edge_rule.
Qed.
Fixpoint left_zeros (l:list Sym) := match l with
  | S1::S1::l=>S (left_zeros l) | _=>O end.
Definition overflow (s:State) := match s with
  | (C,l,S1::S1::S1::r)=>checked_edge (left_zeros l) s
  | _=>None end.
Lemma overflow_spec s t: overflow s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold overflow; destruct q; try discriminate.
  do 3 (destruct r as [|[] r]; try discriminate).
  apply checked_edge_spec.
Qed.

Definition make_left q (l r:list Sym) : State := match l with
  | nil=>(q,nil,S0::r) | b::l=>(q,l,b::r) end.
Lemma make_left_spec q l r:
  denote (make_left q l r)=l *> 0inf <{{q}} r *> 0inf.
Proof. destruct l; reflexivity. Qed.

Inductive Extra := R1Even | R1Odd | R2Zero | R2Even | R2Odd | Prepare.
Definition extra_left tag : list Sym := match tag with Prepare=>nil | _=>[0;1] end.
Definition extra_input tag n : list Sym := match tag with
  | R1Even=>rd1^^(n*2)++[1;1;0;0]
  | R1Odd=>rd1^^(n*2+1)++[1;1;0;0]
  | R2Zero=>rd1^^n++[1;0;1;0;0;0;0;0]
  | R2Even=>rd1^^(n*2)++[1;0;1;0;0;1;0;0;0;0;0]
  | R2Odd=>rd1^^(n*2+1)++[1;0;1;0;0;1;0;0;0;0;0]
  | Prepare=>[1;0;1;0;0]++rd1^^(n*2) end.
Definition extra_target tag n (l r:list Sym) : State := match tag with
  | R1Even=>(A,[0;1]++ld0^^(n*3)++ld1++l,[1;0]++r)
  | R1Odd=>(A,[0;1]++ld0^^(n*3+2)++ld1++l,[0]++r)
  | R2Zero=>make_left C l ([1;1]++rd0^^(n+2)++[1;1]++r)
  | R2Even=>make_left C (ld1^^(n*3+1)++ld0++l) ([1;1;1;0;0;0;1;1;0]++r)
  | R2Odd=>make_left C (ld0++ld1^^(n*3+2)++ld0++l) ([1;1;1;0;0;0;1;0]++r)
  | Prepare=>(A,[0;1;1;0;1;1]^^n++l,[1;0;1;0;0]++r) end.
Lemma prepare_one l r:
  l {{A}}> [1;0;1;0;0] *> rd1^^2 *> r -[tm]->+
  l <* <[1;1;0;1;1;0] {{A}}> [1;0;1;0;0] *> r.
Proof. es. Qed.
Lemma prepare_rule l r n:
  l {{A}}> [1;0;1;0;0] *> rd1^^(n*2) *> r -->*
  l <* (<[1;1;0;1;1;0])^^n {{A}}> [1;0;1;0;0] *> r.
Proof.
  gen l; induction n; intros; [finish|].
  follow100 prepare_one; follow IHn; finish; simpl_rotate; reflexivity.
Qed.
Lemma extra_rule tag n l r:
  denote (A,extra_left tag++l,extra_input tag n++r) -->* denote (extra_target tag n l r).
Proof.
  destruct tag; cbn [extra_left extra_input extra_target];
    rewrite ?make_left_spec; unfold denote; repeat rewrite Str_app_assoc.
  - es.
  - es.
  - es.
  - st; sr_r; do 45 (simpl_rotate; step1); finish; simpl_rotate; reflexivity.
  - st; sr_r; do 31 (simpl_rotate; step1); finish; simpl_rotate; reflexivity.
  - apply prepare_rule.
Qed.
Definition checked_extra tag n (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q A then match peel (extra_left tag) l, peel (extra_input tag n) r with
  | Some l,Some r=>Some (extra_target tag n l r) | _,_=>None end else None.
Lemma checked_extra_spec tag n s t:
  checked_extra tag n s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_extra.
  destruct (q_eqb_spec q A); try discriminate; subst.
  destruct (peel (extra_left tag) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel (extra_input tag n) r) as [r'|] eqn:Hr; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf {{A}}> r *> 0inf -->* denote (extra_target tag n l' r')).
  apply peel_spec in Hl; apply peel_spec in Hr.
  rewrite Hl,Hr,<-!Str_app_assoc; apply extra_rule.
Qed.
Fixpoint right_ones (r:list Sym) : nat * list Sym := match r with
  | S1::S0::S0::r=>let '(n,r):=right_ones r in (S n,r)
  | _=>(O,r) end.
Definition right_extra (l r:list Sym) : option (Extra*nat) := match l with
  | S0::S1::_=>let '(j,t):=right_ones r in
    match peel [1;1;0;0] t with
    | Some _=>Some (if Nat.odd j then R1Odd else R1Even,Nat.div j 2)
    | None=>match peel [1;0;1;0;0;0;0;0] t with
      | Some _=>Some (R2Zero,j)
      | None=>match peel [1;0;1;0;0;1;0;0;0;0;0] t with
        | Some _=>Some (if Nat.odd j then R2Odd else R2Even,Nat.div j 2)
        | None=>None end end end
  | _=>None end.
Definition select_extra l r := match right_extra l r with
  | Some p=>Some p
  | None=>match peel [1;0;1;0;0] r with
    | Some t=>let '(j,_):=right_ones t in match Nat.div j 2 with
      | O=>None | S n=>Some (Prepare,S n) end
    | None=>None end end.
Definition extra (s:State) := match s with
  | (A,l,r)=>match select_extra l r with
    | Some (tag,n)=>checked_extra tag n s | None=>None end
  | _=>None end.
Lemma extra_spec s t: extra s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct q; cbn [extra]; try discriminate.
  destruct (select_extra l r) as [[tag n]|]; try discriminate.
  apply checked_extra_spec.
Qed.

Definition primitive (s:State) : option State :=
  let '(q,l,r):=s in let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
  match tm (q,b) with
  | None=>None
  | Some (b,R,q)=>Some (q,b::l,r)
  | Some (b,L,q)=>match l with nil=>Some (q,nil,S0::b::r) | a::l=>Some (q,l,a::b::r) end
  end.
Local Opaque tm.
Lemma primitive_spec s t: primitive s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E; try discriminate;
    destruct d; try destruct l as [|b' l]; intros H; injection H as <-.
  all: eapply evstep_step; [apply step_c_spec;
      cbn [step_c denote Str_app move_left move_right Streams.hd Streams.tl const];
      fold Q Sym in E; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma primitive_halt s: primitive s=None -> halts tm (denote s).
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E.
  all: try (destruct d; try destruct l; discriminate).
  all: intros _; apply halted_halts; exact E.
Qed.
Local Transparent tm.

Definition next (s:State) : State+unit := match accelerate s with
  | Some t=>inl t
  | None=>match overflow s with
    | Some t=>inl t
    | None=>match extra s with
      | Some t=>inl t
      | None=>match primitive s with Some t=>inl t | None=>inr tt end end end end.
Lemma next_spec s:
  match next s with inl t=>denote s -->* denote t | inr _=>halts tm (denote s) end.
Proof.
  unfold next; destruct (accelerate s) as [t|] eqn:E.
  - eapply accelerate_spec; exact E.
  - destruct (overflow s) as [t|] eqn:F.
    + eapply overflow_spec; exact F.
    + destruct (extra s) as [t|] eqn:G.
      * eapply extra_spec; exact G.
      * destruct (primitive s) as [t|] eqn:H.
        -- eapply primitive_spec; exact H.
        -- apply primitive_halt; exact H.
Qed.
Definition check_from (initial:State) fuel := match N_iter_until next (inl initial) fuel with
  | inr _=>true | inl _=>false end.
Lemma check_from_spec initial fuel: check_from initial fuel=true -> halts tm (denote initial).
Proof.
  pose proof (@N_iter_until_spec State unit next (inl initial) fuel
    (fun s=>denote initial -->* denote s) (fun _=>halts tm (denote initial))) as H.
  assert (K: forall s, denote initial -->* denote s ->
    match next s with inl t=>denote initial -->* denote t | inr _=>halts tm (denote initial) end).
  { intros s Hs; pose proof (next_spec s) as Hn; destruct (next s).
    - eapply evstep_trans; eassumption.
    - eapply halts_evstep; eassumption. }
  specialize (H K (evstep_refl _ _)); unfold check_from.
  destruct (N_iter_until next (inl initial) fuel); cbn in H |- *;
    intros Hc; try discriminate; exact H.
Qed.
Definition initial:State := (A,nil,nil).
Definition check := check_from initial.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof. apply check_from_spec. Qed.
Theorem halt: halts tm c0.
Proof. apply check_spec with (fuel:=4000000%N); native_check_eq. Qed.
End TM119.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM148.TM148 *)
Module TM148.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_0LA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> r -->+ l <| rd0^^(n+1) *> [1;0] *> r.
Proof. es. Qed.
Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov len k h i m:
  LC len k |> RC2 h 0 ((m*2+1)*2^i) -->+
  LC len k <| RC2 (h+i+1) (((2^i-1)*2+1)*2^(h+1)-1) m.
Proof. replace (h+i+1) with (i+(h+1)) by lia; solve_rule ROv2. Qed.
Lemma RC2_Ov_blank len k h:
  LC len k |> RC2 h 0 0 -->+ LC len k <| RC (2^(h+1)).
Proof. epose proof (ROv2 _ 0inf h) as H; solve_rule H. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |> RC 0.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
(* b is the bit length, with Size 0 0.  Constructors follow the ROv2 split. *)
Inductive Size: nat -> nat -> Prop :=
| size0: Size 0 0
| sizeS x b i: Size x b -> Size ((x*2+1)*2^i) (b+i+1).
Lemma size_bounds m b: Size m b -> m<2^b<=m*2+1.
Proof. induction 1; [cbn; lia|arith]. Qed.
Lemma size_exists m: exists b, Size m b.
Proof.
  induction m using strong_induction; lowbit_cases m.
  - exists 0; constructor.
  - destruct (H x ltac:(nia)) as [b Hb]; eexists; constructor; exact Hb.
Qed.

Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => exists b, Size m b /\ 1<=len /\ k<2^len /\
    n<2^(h+1) /\ n+(2^b-1)*2^(h+1)<=k /\ k-n+2^(h+1)<2^len*2
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgR _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + destruct (size_exists x) as [b Hb].
      eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; exists b; split; [exact Hb|].
      pose proof (size_bounds _ _ Hb).
      pose proof (append_bounds len k (n'*3) ltac:(lia)); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct HP as [b [Hb HP]]; destruct n as [|n].
    2: { destruct k as [|k]; [nia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; exists b; split; [exact Hb|lia]. }
    destruct Hb as [|m b i Hb].
    + eexists (cfgL _ _ _); split; [apply RC2_Ov_blank|cbn [P]; arith].
    + destruct k as [|k]; [arith|].
      eexists (cfgR2 _ _ _ _ _); split.
      * eapply progress_evstep_trans; [apply RC2_Ov|].
        apply progress_evstep; apply LC_Inc; lia.
      * cbn [P]; exists b; split; [exact Hb|arith].
Qed.

Lemma init: c0 -->* to_config (cfgL 4 10 0).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM148.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String Compare_dec.

(* SOC23_TM150.TM150 *)
Module TM150.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String Compare_dec.


Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_0LC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> r -->+ l <| rd0^^(n+1) *> [0;1] *> r.
Proof. es. Qed.
Lemma ROv3_0 l r n:
  l |> rd1^^(n*2) *> [1;1] *> r -->+ l <* ld0 <* ld1^^(n*3) |> r.
Proof. es. Qed.
Lemma ROv3_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0] len n ([1] *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC3,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_zero h n: RC3 h n 0 = RC1 h n 0.
Proof. unfold RC3,RC1,RC; rewrite BinInc_O; cbn [Str_app]; repeat rewrite <-const_unfold; reflexivity. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov len k h m:
  LC len k |> RC2 h 0 m -->+ LC len k <| RC3 (h+1) (2^(h+1+1)-1) m.
Proof. solve_rule ROv2. Qed.
Lemma RC3_Ov_0 len k a m: k<2^len ->
  LC len k |> RC3 (a*2) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> RC m.
Proof. solve_rule ROv3_0. Qed.
Lemma RC3_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC3 (a*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule ROv3_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |> RC 0.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Lemma RC2_Incs len k h n m: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC2 h n m -->* LC len k |> RC2 h 0 m.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC2_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma LC_Ov_extra len h:
  LC len 0 <| RC1 (h+1) ((2^h-1)*2+1) 0 -->+
  LC len (2^len-1) |> RC3 (h+1) ((2^(h+1)-1)*2) 1.
Proof. rewrite (Nat.add_comm h 1); replace (2^h) with ((0*2+1)*2^h) by arith; solve_rule LOv. Qed.
Lemma corner_plus len:
  LC (len+1) 0 <| RC (2^(len+1)+1) -->+
  LC (len+1+1) (2^(len+1+1)-1) |> RC3 (len+1) ((2^(len+1)-1)*2) 1.
Proof.
  replace (2^(len+1)+1) with ((2^len*2+1)*2^0) by arith.
  follow10 LC_Ov.
  replace (2^len) with ((0*2+1)*2^len) by arith.
  follow100 (RC1_Ov_0 (len+1) (2^(len+1)-1) 0 len 0 ltac:(arith)).
  repeat rewrite Nat.add_0_r.
  replace (((2^(len+1)-1)*2+1)*2^(0*3)-1) with
    (2^(len+1)+((2^len-1)*2)) by arith.
  follow RC2_Incs; [arith|arith|].
  follow100 RC2_Ov; rewrite RC3_zero.
  replace (2^(len+1)) with (1+(2^(len+1)-1)) by arith.
  eapply evstep_trans; [apply progress_evstep; apply LC_Inc; arith|].
  replace (2^(len+1+1)-1) with
    (((2^len-1)*2+1)+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov_extra; finish; repeat (arith || f_equal).
Qed.
Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat) | cfgR3 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
| cfgR3 len k h n m => LC len k |> RC3 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => (1<=len /\ n+m<=k<2^len /\ n<2^(h+1)) /\
    (h=0 -> forall i, m=2^i -> n+2^i*3<=k+1)
| cfgR2 len k h n m => 1<=len /\ n+m+2^(h+2)<=k<2^len /\ n<2^(h+1)
| cfgR3 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma append0_bounds len k s: k<2^len ->
  k*2<(k*2+1)*2^s<2^(len+1+s) /\
  (k*2+1)*2^s+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma pure_bound len j:
  2^j*2+1<2^len*2 -> 2^j*2+1<>2^len+1 -> 2^j*3<=2^len.
Proof.
  intros H E; destruct (le_dec (j+2) len) as [Hj|Hj].
  - assert (2^(j+2)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith.
  - destruct (le_dec len j) as [Hl|Hl].
    + assert (2^len<=2^j) by (apply Nat.pow_le_mono_r; lia); lia.
    + replace len with (j+1) in * by lia; arith.
Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgR _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * destruct (Nat.eq_dec m (2^len+1)) as [E1|E1].
        -- subst m; destruct len as [|len]; [cbn in HP; lia|].
           replace (S len) with (len+1) by lia.
           eexists (cfgR3 _ _ _ _ _); split; [apply corner_plus|cbn [P]; arith].
        -- lowbit_cases m; [lia|].
           eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
           cbn [P]; split.
           ++ pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
           ++ intros Ei j Ex; subst i x.
              pose proof (pure_bound len j ltac:(arith) ltac:(arith)); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct HP as [HP Hpower]; destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; split; [lia|].
        intros Eh j Ej; specialize (Hpower Eh j Ej); lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      destruct n' as [|a].
      * destruct x as [|x]; [specialize (Hpower ltac:(lia) i ltac:(arith))|]; arith.
      * replace (S a*3) with (a*3+3) in * by lia; arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * intros Ei j Ex; subst i x; arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [arith|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    destruct k as [|k]; [arith|].
    eexists (cfgR3 _ _ _ _ _); split.
    + eapply progress_evstep_trans; [apply RC2_Ov|].
      apply progress_evstep; apply LC_Inc; lia.
    + cbn [P]; arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR3 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC3_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + eexists (cfgR _ _ _); split; [apply RC3_Ov_0; lia|].
      cbn [P]; pose proof (append0_bounds len k (n'*3) ltac:(lia)); lia.
    + lowbitS_cases m.
      eexists (cfgR1 _ _ _ _ _); split; [apply RC3_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * intros Ei j Ex; subst i x; arith.
Qed.

Lemma init: c0 -->* to_config (cfgL 4 10 0).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM150.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM151.TM151 *)
Module TM151.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_1LA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> r -->+ l <| rd0^^(n+1) *> [1;1] *> r.
Proof. es. Qed.
Lemma ROv3_0 l r n:
  l |> rd1^^(n*2) *> [1;1] *> r -->+ l <* ld0 <* ld1^^(n*3) |> r.
Proof. es. Qed.
Lemma ROv3_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0] len n ([1] *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC3,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov len k h m:
  LC len k |> RC2 h 0 m -->+ LC len k <| RC3 (h+1) (2^(h+1)-1) m.
Proof.
  replace (2^(h+1)) with ((0*2+1)*2^(h+1)) by arith.
  unfold RC3; rewrite (BinDec2_mulpow2sub1 _ _ _ 0 0 (h+1)) by arith.
  solve_rule ROv2.
Qed.
Lemma RC3_Ov_0 len k a m: k<2^len ->
  LC len k |> RC3 (a*2) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> RC m.
Proof. solve_rule ROv3_0. Qed.
Lemma RC3_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC3 (a*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule ROv3_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |> RC 0.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat) | cfgR3 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
| cfgR3 len k h n m => LC len k |> RC3 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => (1<=len /\ n+m<=k<2^len /\ n<2^(h+1)) /\
    (h=0 -> forall i, m=2^i -> n+2^i*2<=k+1)
| cfgR2 len k h n m => 1<=len /\ n+m+2^(h+1)<=k<2^len /\ n<2^(h+1)
| cfgR3 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma append0_bounds len k s: k<2^len ->
  k*2<(k*2+1)*2^s<2^(len+1+s) /\
  (k*2+1)*2^s+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgR _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; split.
        -- pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
        -- intros Ei j Ex; subst i x.
           assert (j<len) by
             (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
           assert (2^(j+1)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct HP as [HP Hpower]; destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; split; [lia|].
        intros Eh j Ej; specialize (Hpower Eh j Ej); lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      destruct n' as [|a].
      * destruct x as [|x]; [specialize (Hpower ltac:(lia) i ltac:(arith))|]; arith.
      * replace (S a*3) with (a*3+3) in * by lia; arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * intros Ei j Ex; subst i x; arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [arith|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    destruct k as [|k]; [arith|].
    eexists (cfgR3 _ _ _ _ _); split.
    + eapply progress_evstep_trans; [apply RC2_Ov|].
      apply progress_evstep; apply LC_Inc; lia.
    + cbn [P]; arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR3 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC3_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + eexists (cfgR _ _ _); split; [apply RC3_Ov_0; lia|].
      cbn [P]; pose proof (append0_bounds len k (n'*3) ltac:(lia)); lia.
    + lowbitS_cases m.
      eexists (cfgR1 _ _ _ _ _); split; [apply RC3_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * intros Ei j Ex; subst i x; arith.
Qed.

Lemma init: c0 -->* to_config (cfgL 4 10 0).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM151.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String Compare_dec.

(* SOC23_TM153.TM153 *)
Module TM153.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String Compare_dec.


Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_0RD---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es' n & l r. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es' n & l r. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_01_00 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> rd0 *> rd0 *> r -->+
  l <| rd0^^(n+3) *> [0;1] *> r.
Proof. es. Qed.

Lemma ROv2_0_01 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2_0_10 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.

Lemma ROv2_0_11 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^(m+2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd1 *> rd0^^m *> rd1 *> r.
Proof. es. Qed.

Lemma ROv2_1_01 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+5) |> [1;0] *> r.
Proof. es. Qed.

Lemma ROv2_1_10 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> [1] *> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.

Lemma ROv2_1_11 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^(m+2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+5) |> [0;0] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.

Lemma ROv3_0 l r n:
  l |> rd1^^(n*2) *> [1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3) |> r.
Proof. es. Qed.

Lemma ROv3_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.


Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Definition digit (b:bool) := if b then ld0 else ld1.
Lemma Tail4even l n b c d:
  l <* ld0 <* ld1^^n <* digit b <* digit c <* digit d |>
    [1;0;1;0;0;0;1;0;0] *> 0inf -->+
  l <* ld1 <* ld0^^n <* digit b <* digit c <* digit d
    <* ld0 <* ld1^^2 <* ld0 <| rd0^^2 *> rd1 *> 0inf.
Proof. destruct b,c,d; cbn [digit]; es' n & l. Qed.
Lemma Tail5even l n:
  l <* ld0 <* ld1^^n |> [1;0;1;0;0;1;1;0;0] *> 0inf -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0^^4 <* ld1^^2 <| 0inf.
Proof. es' n & l. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LCpred_rule len k (F G:side->Q*tape):
  1+k<2^len ->
  (forall l n, F (l <* ld0 <* ld1^^n) -->+ G (l <* ld1 <* ld0^^n)) ->
  F (LC len (1+k)) -->+ G (LC len k).
Proof.
  intros HK Hrule; lowbitS_cases k.
  replace (1+((x*2+1)*2^i-1)) with ((x*2+1)*2^i) in * by arith.
  pose proof (lowbit_split_lt _ _ _ HK).
  unfold LC; rewrite (lowbit_split _ _ _ HK); rw_Bin.
  all: try solve[arith].
  apply Hrule.
Qed.

Lemma Tail5even_num len k: 1+k<2^len ->
  LC len (1+k) |> [1;0;1;0;0;1;1;0;0] *> 0inf -->+
  LC (len+7) (k*2^7+60) <| RC 0.
Proof.
  intros Hk; unfold LC.
  pose proof (BinDigits.BinDec_app ld0 ld1 len k ldh
    [BinDigits.D1;BinDigits.D1;BinDigits.D0;BinDigits.D0;BinDigits.D0;BinDigits.D0;BinDigits.D1] ltac:(lia)) as E.
  cbn [BinDigits.val0 Datatypes.length Nat.add Nat.mul] in E; rewrite E.
  change (LC len (1+k) |> [1;0;1;0;0;1;1;0;0] *> 0inf -->+
    LC len k <* ld1 <* ld0^^4 <* ld1^^2 <| 0inf).
  apply (LCpred_rule len k (fun l=>l |> [1;0;1;0;0;1;1;0;0] *> 0inf)
    (fun l=>l <* ld1 <* ld0^^4 <* ld1^^2 <| 0inf)); [lia|apply Tail5even].
Qed.

Definition bd (b:bool) := if b then BinDigits.D0 else BinDigits.D1.
Lemma mp_bd b: BinDigits.mp ld0 ld1 (bd b)=digit b.
Proof. destruct b; reflexivity. Qed.
Close Scope sym.
Lemma splitbit k: exists (b:bool) q, k=q*2+(if b then 1 else 0).
Proof. divmod2_cases k; [exists false,n'|exists true,n']; lia. Qed.
Lemma low3 k: exists b c d q, k=q*2^3+BinDigits.val0 [bd d;bd c;bd b].
Proof.
  destruct (splitbit k) as [d [k1 E0]], (splitbit k1) as [c [k2 E1]],
    (splitbit k2) as [b [q E2]].
  exists b,c,d,q; subst; destruct b,c,d; cbn; lia.
Qed.
Open Scope sym.
Lemma Tail4even_num len k: 8+k<2^len ->
  LC len (8+k) |> [1;0;1;0;0;0;1;0;0] *> 0inf -->+
  LC (len+4) (k*2^4+9) <| RC 4.
Proof.
  intros Hk; destruct len as [|[|[|len]]]; try (cbn in Hk; lia).
  replace (S (S (S len))) with (len+3) in * by lia.
  destruct (low3 k) as [b [c [d [q E]]]]; subst k.
  replace (8+(q*2^3+BinDigits.val0 [bd d;bd c;bd b])) with
    ((1+q)*2^3+BinDigits.val0 [bd d;bd c;bd b]) by lia.
  unfold LC.
  pose proof (BinDigits.BinDec_app ld0 ld1 (len+3)
    (q*2^3+BinDigits.val0 [bd d;bd c;bd b]) ldh
    [BinDigits.D0;BinDigits.D1;BinDigits.D1;BinDigits.D0] ltac:(arith)) as E4.
  cbn [Datatypes.length BinDigits.val0 Nat.add Nat.mul] in E4.
  cbn [BinDigits.val0 Nat.add Nat.mul]; rewrite E4.
  pose proof (BinDigits.BinDec_app ld0 ld1 len (1+q) ldh [bd d;bd c;bd b] ltac:(arith)) as E0.
  pose proof (BinDigits.BinDec_app ld0 ld1 len q ldh [bd d;bd c;bd b] ltac:(arith)) as E1.
  cbn [Datatypes.length BinDigits.val0 Nat.add Nat.mul] in E0,E1.
  rewrite E0,E1.
  cbn [List.flat_map]; repeat rewrite mp_bd.
  repeat rewrite List.app_nil_r; repeat rewrite Str_app_assoc.
  unfold RC; change 4%nat with (2^2); rewrite BinInc_pow2.
  change (LC len (1+q) <* digit b <* digit c <* digit d |>
    [1;0;1;0;0;0;1;0;0] *> 0inf -->+
    LC len q <* digit b <* digit c <* digit d <* ld0 <* ld1^^2 <* ld0 <|
    rd0^^2 *> rd1 *> 0inf).
  apply (LCpred_rule len q
    (fun l=> l <* digit b <* digit c <* digit d |> [1;0;1;0;0;0;1;0;0] *> 0inf)
    (fun l=> l <* digit b <* digit c <* digit d <* ld0 <* ld1^^2 <* ld0 <| rd0^^2 *> rd1 *> 0inf));
    [arith|intros; apply Tail4even].
Qed.

Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0] len n ([1] *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Definition RC4 len n := BinDec2 [0] [1] [0;0] len n ([1;0;0;1;0;0;0;1;0;0] *> 0inf).
Definition RC5 len n := BinDec2 [0] [1] [0;0] len n ([1;0;0;1;0;0;1;1;0;0] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [BinaryCounter.d0 Datatypes.length List.repeat Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC3,RC',RC4,RC5,RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_zero h n: RC3 h n 0 = RC1 h n 0.
Proof. unfold RC3,RC1,RC; rewrite BinInc_O; cbn [Str_app]; repeat rewrite <-const_unfold; reflexivity. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov len k h m:
  LC len k |> RC2 h 0 (m*4) -->+ LC len k <| RC3 (h+3) (2^(h+3+1)-1) m.
Proof.
  replace (m*4) with (m*2*2) by lia.
  solve_rule ROv2_01_00.
Qed.
Lemma RC3_Ov_0 len k a m: k<2^len ->
  LC len k |> RC3 (a*2) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> RC m.
Proof. solve_rule ROv3_0. Qed.
Lemma RC3_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC3 (a*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule ROv3_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |> RC 0.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Lemma RC2_Incs len k h n m: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC2 h n m -->* LC len k |> RC2 h 0 m.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC2_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.

Lemma RC2_Ov_0_01 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((((m*2+1)*2^i)*2+1)*2) -->+
  LC (len+1+(a*3+4)) ((k*2+1)*2^(a*3+4)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_0_01. Qed.
Lemma RC2_Ov_1_01 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 ((((m*2+1)*2^i)*2+1)*2) -->+
  LC (len+1+(a*3+5)) ((k*2+1)*2^(a*3+5)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv2_1_01. Qed.
Lemma RC2_Ov_0_01_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2) 0 2 -->+
  LC (len+1+(a*3+4)) ((k*2+1)*2^(a*3+4)-1) |> RC 0.
Proof. unfold RC2,RC; rewrite (BinInc_mul2 _ 1),BinInc_1; solve_rule ROv2_0_01. Qed.
Lemma RC2_Ov_1_01_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 2 -->+
  LC (len+1+(a*3+5)) ((k*2+1)*2^(a*3+5)-1) |> RC 1.
Proof. unfold RC2,RC; rewrite (BinInc_mul2 _ 1),BinInc_1; solve_rule ROv2_1_01. Qed.
Lemma RC2_Ov_0_10 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((((m*2+1)*2^i-1)*2)*2+1) -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)-1) |> RC ((m*2+1)*2^(i+1)).
Proof. solve_rule ROv2_0_10. Qed.
Lemma RC2_Ov_0_11 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((((m*2+1)*2^i-1)*2+1)*2+1) -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)-1) |> RC (((m*2+1)*2^i)*2+1).
Proof. pose proof (fun l r=>ROv2_0_11 l r a i) as H; rewrite (Nat.add_comm i 2),(lpow_add _ 2 i) in H; solve_rule H. Qed.
Lemma RC2_Ov_1_10 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 ((((m*2+1)*2^i-1)*2)*2+1) -->+
  LC (len+1+(a*3+4)) ((k*2+1)*2^(a*3+4)-1) |> RC1 (i+1) ((2^(i+1)-1)*2) m.
Proof. solve_rule ROv2_1_10. Qed.
Lemma RC2_Ov_1_11 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 ((((m*2+1)*2^i-1)*2+1)*2+1) -->+
  LC (len+1+(a*3+5)) ((k*2+1)*2^(a*3+5)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. pose proof (fun l r=>ROv2_1_11 l r a i) as H; rewrite (Nat.add_comm i 2),(lpow_add _ 2 i) in H; solve_rule H. Qed.

Lemma RC4_Inc len n l: 1+n<2^(len+1) -> l |> RC4 len (1+n) -->+ l <| RC4 len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC5_Inc len n l: 1+n<2^(len+1) -> l |> RC5 len (1+n) -->+ l <| RC5 len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC4_Ov_0 len k a: k<2^len ->
  LC len k |> RC4 (a*2) 0 -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> [1;0;1;0;0;0;1;0;0] *> 0inf.
Proof. solve_rule ROv1_0. Qed.
Lemma RC4_Ov_1 len k a: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0;1] *> RC 2.
Proof. unfold RC; rewrite (BinInc_mul2 _ 1),BinInc_1; solve_rule ROv1_1. Qed.
Lemma RC5_Ov_0 len k a: k<2^len ->
  LC len k |> RC5 (a*2) 0 -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> [1;0;1;0;0;1;1;0;0] *> 0inf.
Proof. solve_rule ROv1_0. Qed.
Lemma RC5_Ov_1 len k a: k<2^len ->
  LC len k |> RC5 (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0;1;0;0;1;1;0;0] *> 0inf.
Proof. solve_rule ROv1_1. Qed.
Lemma Tail01 len k m: 1+k<2^len ->
  LC len (1+k) |> [0;1] *> RC m -->+
  LC (len+1) (k*2+1) |> RC m.
Proof.
  intros HK; follow10 (RInc (LC len (1+k)) ([1] *> RC m) 0).
  follow100 (LC_Inc len k ([1;1] *> RC m) HK).
  change (LC len k |> RC3 (0*2) 0 m -->* LC (len+1) (k*2+1) |> RC m).
  follow100 (RC3_Ov_0 len k 0 m ltac:(lia)); finish.
Qed.
Lemma Tail5odd_num len k: 1+k<2^len ->
  LC len (1+k) |> [0;1;0;0;1;1;0;0] *> 0inf -->+
  LC (len+3) (k*2^3+2) <| RC 0.
Proof.
  intros HK; unfold LC.
  pose proof (BinDigits.BinDec_app ld0 ld1 len k ldh
    [BinDigits.D1;BinDigits.D0;BinDigits.D1] ltac:(lia)) as E.
  cbn [BinDigits.val0 Datatypes.length Nat.add Nat.mul] in E; rewrite E.
  change (LC len (1+k) |> [0;1;0;0;1;1;0;0] *> 0inf -->+
    LC len k <* ld1 <* ld0 <* ld1 <| 0inf).
  apply (LCpred_rule len k (fun l=>l |> [0;1;0;0;1;1;0;0] *> 0inf)
    (fun l=>l <* ld1 <* ld0 <* ld1 <| 0inf)); [lia|].
  intros l n; es' n & l.
Qed.

Lemma LC_Ov_extra0 len h:
  LC len 0 <| RC1 (h+2) ((3*2+1)*2^h-1) 0 -->+
  LC len (2^len-1) |> RC3 h ((2^h-1)*2) 4.
Proof.
  rewrite (Nat.add_comm h 2); unfold RC1,RC3,RC.
  rewrite (BinInc_pow2 _ 2); solve_rule LOv.
Qed.
Lemma LC_Ov_extra1 len h:
  LC len 0 <| RC1 (h+2) ((2*2+1)*2^h-1) 0 -->+
  LC len (2^len-1) |> RC4 h ((2^h-1)*2).
Proof. rewrite (Nat.add_comm h 2); solve_rule LOv. Qed.
Lemma LC_Ov_extra2 len h:
  LC len 0 <| RC1 (h+2) ((0*2+1)*2^h-1) 0 -->+
  LC len (2^len-1) |> RC5 h ((2^h-1)*2).
Proof. rewrite (Nat.add_comm h 2); solve_rule LOv. Qed.
Lemma left_RC1_Incs len k h n: k<2^len -> n+k<2^(h+1) ->
  LC len k <| RC1 h (n+k) 0 -->* LC len 0 <| RC1 h n 0.
Proof.
  induction k; intros; [rewrite Nat.add_0_r; finish|].
  follow_inc LC_Inc.
  replace (n+S k) with (1+(n+k)) by lia; follow_inc RC1_Inc.
  follow IHk; try lia; finish.
Qed.
Lemma corner_start len h: 2^(h+1)<=2^len ->
  LC len 0 <| RC (2^(h+1)+1) -->+
  LC (len+1) (2^len*2-2^(h+1)) <| RC1 (h+3) (2^(h+3+1)-1) 0.
Proof.
  intros Hlen.
  replace (2^(h+1)+1) with ((2^h*2+1)*2^0) by arith.
  follow10 LC_Ov.
  replace (2^h) with ((0*2+1)*2^h) by arith.
  follow100 (RC1_Ov_0 len (2^len-1) 0 h 0 ltac:(arith)).
  repeat rewrite Nat.add_0_r.
  replace (((2^len-1)*2+1)*2^(0*3)-1) with
    ((2^len*2-2^(h+1))+(2^h-1)*2) by arith.
  follow RC2_Incs; [arith|arith|].
  follow100 (RC2_Ov (len+1) (2^len*2-2^(h+1)) h 0).
  rewrite RC3_zero; finish.
Qed.
Lemma corner_plus len:
  LC (len+1) 0 <| RC (2^(len+1)+1) -->+
  LC (len+1+1) (2^(len+1+1)-1) |> RC3 (len+1) ((2^(len+1)-1)*2) 4.
Proof.
  follow10 (corner_start (len+1) len ltac:(lia)).
  replace (2^(len+3+1)-1) with
    (((3*2+1)*2^(len+1)-1)+(2^(len+1)*2-2^(len+1))) by arith.
  follow left_RC1_Incs; [arith|arith|].
  replace (len+3) with (len+1+2) by lia.
  follow100 LC_Ov_extra0; finish.
Qed.
Lemma corner_half_plus len:
  LC (len+2) 0 <| RC (2^(len+1)+1) -->+
  LC (len+2+1) (2^(len+2+1)-1) |> RC4 (len+1) ((2^(len+1)-1)*2).
Proof.
  follow10 (corner_start (len+2) len ltac:(arith)).
  replace (2^(len+3+1)-1) with
    (((2*2+1)*2^(len+1)-1)+(2^(len+2)*2-2^(len+1))) by arith.
  follow left_RC1_Incs; [arith|arith|].
  replace (len+3) with (len+1+2) by lia.
  follow100 LC_Ov_extra1; finish; repeat (arith || f_equal).
Qed.
Lemma corner_quarter_plus len:
  LC (len+3) 0 <| RC (2^(len+1)+1) -->+
  LC (len+3+1) (2^(len+3+1)-1) |> RC5 (len+1) ((2^(len+1)-1)*2).
Proof.
  follow10 (corner_start (len+3) len ltac:(arith)).
  replace (2^(len+3+1)-1) with
    (((0*2+1)*2^(len+1)-1)+(2^(len+3)*2-2^(len+1))) by arith.
  follow left_RC1_Incs; [arith|arith|].
  replace (len+3) with (len+1+2) by lia.
  follow100 LC_Ov_extra2; finish; repeat (arith || f_equal).
Qed.
Lemma corner_small:
  LC 1 0 <| RC 3 -->+ LC 5 31 |> RC3 3 14 2.
Proof. cbn [LC RC RC3]; esx. Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat)
  | cfgR3 (len k h n m:nat) | cfgR4 (len k h n:nat) | cfgR5 (len k h n:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
| cfgR3 len k h n m => LC len k |> RC3 h n m
| cfgR4 len k h n => LC len k |> RC4 h n
| cfgR5 len k h n => LC len k |> RC5 h n
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => (1<=len /\ n+m<=k<2^len /\ n<2^(h+1)) /\
    (h=0 -> forall i, m=2^i -> n+2^i*9<=k+1) /\
    (h=2 -> forall i, m=2^i -> n*8+2^i*9<=k*8+4)
| cfgR2 len k h n m => (1<=len /\ n+m<=k<2^len /\ n<2^(h+1)) /\
    (m mod 4=0 -> n+m/4+2^(h+4)<=k)
| cfgR3 len k h n m => (1<=len /\ k<2^len /\ n<2^(h+1)) /\
    ((n+m<=k /\ (h=1 -> forall i, m=2^i*2 -> n*4+2^i*9<=k*4+2)) \/
     (m=4 /\ 2<=h /\ n<k))
| cfgR4 len k h n => 1<=len /\ n+4<=k<2^len /\ n<2^(h+1)
| cfgR5 len k h n => 1<=len /\ n<k<2^len /\ n<2^(h+1)
end.

Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma append0_bounds len k s: k<2^len ->
  k*2<(k*2+1)*2^s<2^(len+1+s) /\
  (k*2+1)*2^s+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma pure_bound len j:
  2^j*2+1<2^(len+2)*2 -> 2^j*2+1<>2^(len+2)+1 ->
  2^j*2+1<>2^(len+1)+1 -> 2^j*2+1<>2^len+1 -> 2^j*9<=2^(len+2).
Proof.
  intros H E0 E1 E2; destruct (le_dec (j+2) len) as [Hj|Hj].
  - assert (2^(j+2)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith.
  - assert (j<len+2) by (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
    destruct (Nat.eq_dec j (len+1)); [subst j; arith|].
    destruct (Nat.eq_dec j len); [subst j; arith|].
    replace len with (j+1) in * by lia; arith.
Qed.
Lemma pure2_bound len j:
  (2^j*2+1)*2^2<2^len*2 -> 6*8+2^j*9<=(2^len-1)*8+4.
Proof.
  intros H; assert (j+2<len) by (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
  assert (2^(j+3)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith.
Qed.

Lemma closed_R1 len k h n m: P (cfgR1 len k h n m) ->
  exists y, to_config (cfgR1 len k h n m) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros [HP [Hpower0 Hpower2]]; destruct n as [|n].
  2: { destruct k as [|k]; [lia|].
    eexists (cfgR1 _ _ _ _ _); split.
    - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    - cbn [P]; repeat split; try lia.
      + intros Eh j Ej; specialize (Hpower0 Eh j Ej); lia.
      + intros Eh j Ej; specialize (Hpower2 Eh j Ej); lia. }
  divmod2_cases h; lowbit_cases m.
  - eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
    cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
  - eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
    cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); split.
    + pose proof (split_bound_v2 x i); arith.
    + intros Hmod; destruct n' as [|[|a]].
      * destruct x as [|x]; [specialize (Hpower0 ltac:(lia) i ltac:(arith)); arith|].
        assert (4<=S x) by lia; arith.
      * destruct x as [|x]; [specialize (Hpower2 ltac:(lia) i ltac:(arith)); arith|].
        assert (4<=S x) by lia; arith.
      * replace (S (S a)*3) with (a*3+6) in * by lia; arith.
  - eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
    cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
  - eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
    cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); split.
    + pose proof (split_bound_v2 x i); arith.
    + split; intros Ei j Ex; subst i x; arith.
Qed.

Lemma closed_R2 len k h n m: P (cfgR2 len k h n m) ->
  exists y, to_config (cfgR2 len k h n m) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros [HP Hbudget]; destruct n as [|n].
  2: { destruct k as [|k]; [lia|].
    eexists (cfgR2 _ _ _ _ _); split.
    - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    - cbn [P]; split; [lia|intros HM; specialize (Hbudget HM); lia]. }
  divmod2_cases m; rename n' into m0; divmod2_cases m0; rename n' into q.
  - replace (q*2*2) with (q*4) in * by lia.
    specialize (Hbudget ltac:(lia)); destruct k as [|k]; [arith|].
    eexists (cfgR3 _ _ _ _ _); split.
    + eapply progress_evstep_trans; [apply RC2_Ov|].
      apply progress_evstep; apply LC_Inc; lia.
    + cbn [P]; split; [arith|left; split; [arith|intros; lia]].
  - divmod2_cases h; lowbit_cases q.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_0_01_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+4) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC2_Ov_0_01; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+4) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * split; intros Ei j Ex; subst i x; arith.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_1_01_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+5) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_1_01; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+5) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * intros; arith.
  - divmod2_cases h; lowbitS_cases q.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_0_10; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+3) ltac:(lia)); arith.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC2_Ov_1_10; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+4) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * split; intros Ei j Ex; [lia|].
        assert (i=1) by lia; subst i x; arith.
  - divmod2_cases h; lowbitS_cases q.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_0_11; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+3) ltac:(lia)); arith.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_1_11; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+5) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * intros; arith.
Qed.

Lemma closed_R3 len k h n m: P (cfgR3 len k h n m) ->
  exists y, to_config (cfgR3 len k h n m) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros [HP HT]; destruct n as [|n].
  2: { destruct k as [|k]; [destruct HT as [[H _]|H]; lia|].
    eexists (cfgR3 _ _ _ _ _); split.
    - eapply progress_evstep_trans; [apply RC3_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    - cbn [P]; split; [lia|].
      destruct HT as [[H Hpower]|H]; [left|right; lia].
      split; [lia|intros Eh j Ej; specialize (Hpower Eh j Ej); lia]. }
  destruct HT as [[Hbudget Hpower]|[Em Hspecial]].
  - divmod2_cases h.
    + eexists (cfgR _ _ _); split; [apply RC3_Ov_0; lia|].
      cbn [P]; pose proof (append0_bounds len k (n'*3) ltac:(lia)); lia.
    + lowbitS_cases m.
      eexists (cfgR1 _ _ _ _ _); split; [apply RC3_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)); split.
      * pose proof (split_bound_v2 x i); arith.
      * split; intros Ei j Ex; subst i x.
        -- destruct n' as [|a].
           ++ specialize (Hpower ltac:(lia) j ltac:(arith)); arith.
           ++ replace (S a*3+1) with (a*3+4) in * by lia; arith.
        -- arith.
  - subst m; divmod2_cases h.
    + eexists (cfgR _ _ _); split; [apply RC3_Ov_0; lia|].
      cbn [P]; pose proof (append0_bounds len k (n'*3) ltac:(lia)).
      destruct n' as [|a]; [lia|].
      replace (S a*3) with (a*3+3) in * by lia; arith.
    + eexists (cfgR1 _ _ _ _ _); split.
      * apply (RC3_Ov_1 len k n' 0 2); lia.
      * cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)); split.
        -- arith.
        -- split; intros Eh j Ej; [|lia].
           destruct n' as [|a]; [lia|].
           replace (S a*3+1) with (a*3+4) in * by lia; arith.
Qed.

Lemma closed_R4 len k h n: P (cfgR4 len k h n) ->
  exists y, to_config (cfgR4 len k h n) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros HP; destruct n as [|n].
  2: { destruct k as [|k]; [lia|].
    eexists (cfgR4 _ _ _ _); split.
    - eapply progress_evstep_trans; [apply RC4_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    - cbn [P]; lia. }
  divmod2_cases h.
  - pose proof (append_bounds len k (n'*3) ltac:(lia)).
    eexists (cfgL _ _ _); split.
    + eapply progress_evstep_trans; [apply RC4_Ov_0; lia|].
      replace ((k*2+1)*2^(n'*3)-1) with
        (8+((k*2+1)*2^(n'*3)-1-8)) by lia.
      apply progress_evstep; apply Tail4even_num; lia.
    + cbn [P]; arith.
  - pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
    eexists (cfgR _ _ _); split.
    + eapply progress_evstep_trans; [apply RC4_Ov_1; lia|].
      replace ((k*2+1)*2^(n'*3+2)-1) with
        (1+((k*2+1)*2^(n'*3+2)-1-1)) by lia.
      apply progress_evstep; apply Tail01; lia.
    + cbn [P]; arith.
Qed.
Lemma closed_R5 len k h n: P (cfgR5 len k h n) ->
  exists y, to_config (cfgR5 len k h n) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros HP; destruct n as [|n].
  2: { destruct k as [|k]; [lia|].
    eexists (cfgR5 _ _ _ _); split.
    - eapply progress_evstep_trans; [apply RC5_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    - cbn [P]; lia. }
  divmod2_cases h.
  - pose proof (append_bounds len k (n'*3) ltac:(lia)).
    eexists (cfgL _ _ _); split.
    + eapply progress_evstep_trans; [apply RC5_Ov_0; lia|].
      replace ((k*2+1)*2^(n'*3)-1) with
        (1+((k*2+1)*2^(n'*3)-1-1)) by lia.
      apply progress_evstep; apply Tail5even_num; lia.
    + cbn [P]; arith.
  - pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
    eexists (cfgL _ _ _); split.
    + eapply progress_evstep_trans; [apply RC5_Ov_1; lia|].
      replace ((k*2+1)*2^(n'*3+2)-1) with
        (1+((k*2+1)*2^(n'*3+2)-1-1)) by lia.
      apply progress_evstep; apply Tail5odd_num; lia.
    + cbn [P]; arith.
Qed.

Lemma closed_corner len:
  exists y, LC (len+1) 0 <| RC (2^(len+1)) -->+ to_config y /\ P y.
Proof.
  divmod2_cases len.
  - eexists (cfgL _ _ _); split.
    + eapply progress_evstep_trans; [apply corner_case|].
      apply progress_evstep; apply RC'_Ov_0; arith.
    + cbn [P]; arith.
  - eexists (cfgR _ _ _); split.
    + eapply progress_evstep_trans; [apply corner_case|].
      apply progress_evstep; apply RC'_Ov_1; arith.
    + cbn [P]; arith.
Qed.
Lemma closed_L0 len m: P (cfgL len 0 m) ->
  exists y, to_config (cfgL len 0 m) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros HP; destruct len as [|[|len]]; [lia| |].
  - destruct m as [|[|[|m]]]; [lia| | |].
    + eexists (cfgR1 _ _ _ _ _); split; [apply (LC_Ov 1 0 0)|].
      cbn [P]; repeat split; try lia; intros; arith.
    + apply (closed_corner 0).
    + assert (m=0) by (cbn in HP; lia); subst m.
      eexists (cfgR3 _ _ _ _ _); split; [apply corner_small|].
      cbn [P]; split; [lia|left; split; [lia|intros; lia]].
  - replace (S (S len)) with (len+2) in * by lia.
    destruct (Nat.eq_dec m (2^(len+2))) as [E|E].
    + subst m; replace (len+2) with (len+1+1) by lia; apply closed_corner.
    + destruct (Nat.eq_dec m (2^(len+2)+1)) as [E0|E0].
      * subst m; replace (len+2) with (len+1+1) by lia.
        eexists (cfgR3 _ _ _ _ _); split; [apply corner_plus|].
        cbn [P]; split; [arith|right; arith].
      * destruct (Nat.eq_dec m (2^(len+1)+1)) as [E1|E1].
        -- subst m; eexists (cfgR4 _ _ _ _); split; [apply corner_half_plus|cbn [P]; arith].
        -- destruct (Nat.eq_dec m (2^len+1)) as [E2|E2].
           ++ subst m; destruct len as [|len].
              ** eexists (cfgR1 _ _ _ _ _); split; [apply (LC_Ov 2 0 1)|].
                 cbn [P]; repeat split; try lia; intros; arith.
              ** replace (S len) with (len+1) by lia.
                 replace (len+1+2) with (len+3) by lia.
                 eexists (cfgR5 _ _ _ _); split; [apply corner_quarter_plus|cbn [P]; arith].
           ++ lowbit_cases m; [lia|].
              eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
              cbn [P]; split.
              ** pose proof (split_bound_v3 x i (len+2) ltac:(lia) E); arith.
              ** split; intros Ei j Ex; subst i x.
                 --- pose proof (pure_bound len j ltac:(arith) ltac:(arith) ltac:(arith) ltac:(arith)); arith.
                 --- pose proof (pure2_bound (len+2) j ltac:(arith)); arith.
Qed.
Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x; try solve [apply closed_R1|apply closed_R2|apply closed_R3|apply closed_R4|apply closed_R5].
  - destruct k; [apply closed_L0|].
    cbn [P to_config]; intros HP; eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - cbn [P to_config]; intros HP; eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
Qed.
Lemma init: c0 -->* to_config (cfgL 4 10 0).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.

End TM153.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String Compare_dec.

(* Shared definitions from SOC23_TM156.v. *)
Module SOC23_TM156.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String Compare_dec.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_zero0: forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) <* ld0 <| r.
Hypothesis ROv2_zero1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+4) <| r.
Hypothesis ROv2_inc: forall l r n m,
  l |> rd1^^n *> [1;0;1;0;0;1;0;0] *> rd1^^m *> [0] *> r -->+
  l <| rd0^^(n+2) *> [0;1] *> rd0^^m *> [1] *> r.
Hypothesis ROv2_short0: forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) <| r.
Hypothesis ROv11_split: forall l r n,
  l |> rd1^^(n*2+2) *> [1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 <| r.
Hypothesis ROv11_zero: forall l r,
  l |> [1;1] *> r -->+ l <* ld0 |> r.
Hypothesis ROv11_inc: forall l r n m,
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^m *> [0] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) |> [0] *> rd0^^m *> [1] *> r.
Hypothesis ROv2_short1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.


Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0] len n ([1] *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Definition Tail len n := BinDec2 [0] [1] [0;0] len n ([1;0;0;1;1;1;0;0] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC3,RC',Tail,RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.


Lemma ROv3_0 l r a:
  l |> rd1^^(a*2) *> [1;1] *> r -->+ l <* ld0 <* ld1^^(a*3) |> r.
Proof.
  destruct a as [|a]; [cbn; apply ROv11_zero|].
  replace (S a*2) with (a*2+2) by lia.
  replace (S a*3) with (a*3+2+1) by lia.
  follow10 ROv11_split; apply progress_evstep.
  rewrite (Nat.add_comm (a*3+2) 1),lpow_add; simpl_rotate; simpl_tape.
  apply (LInc _ _ 0).
Qed.

Lemma RC2_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (((m*2+1)*2^i)*2) -->+
  LC (len+1+(a*3+1)+1) ((k*2+1)*2^(a*3+1)*2+1) <| RC2 i (2^(i+1)-1) m.
Proof. solve_rule ROv2_zero0. Qed.
Lemma RC2_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 (((m*2+1)*2^i)*2) -->+
  LC (len+1+(a*3+4)) ((k*2+1)*2^(a*3+4)) <| RC1 i (2^(i+1)-1) m.
Proof. solve_rule ROv2_zero1. Qed.
Lemma RC2_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2) 0 0 -->+
  LC (len+1+(a*3+1)+1) ((k*2+1)*2^(a*3+1)*2+1) <| RC 0.
Proof. epose proof (ROv2_zero0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC2_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 0 -->+
  LC (len+1+(a*3+4)) ((k*2+1)*2^(a*3+4)) <| RC 0.
Proof. epose proof (ROv2_zero1 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC2_Ov_inc len k h m:
  LC len k |> RC2 h 0 (m*2+1) -->+
  LC len k <| RC3 (h+2) (2^(h+2+1)-1) (m+1).
Proof.
  lowbitS_cases m; replace ((x*2+1)*2^i-1+1) with ((x*2+1)*2^i) by arith.
  solve_rule ROv2_inc.
Qed.
Lemma RC3_Ov_0 len k a m: k<2^len ->
  LC len k |> RC3 (a*2) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> RC m.
Proof. solve_rule ROv3_0. Qed.
Lemma RC3_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC3 (a*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) |> RC1 i (2^(i+1)-1) m.
Proof. solve_rule ROv11_inc. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv2_short0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |> RC 0.
Proof. epose proof (ROv2_short1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Lemma RC2_Incs len k h n m: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC2 h n m -->* LC len k |> RC2 h 0 m.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC2_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma RC3_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC3 h (n+k+1) m -->* LC len 0 <| RC3 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC3_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC3_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma Tail_Inc len n l: 1+n<2^(len+1) -> l |> Tail len (1+n) -->+ l <| Tail len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma Tail_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> Tail h n -->* LC len k |> Tail h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc Tail_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma LC_Ov_tail len h:
  LC len 0 <| RC3 (h+1) ((0*2+1)*2^h-1) 1 -->+
  LC len (2^len-1) |> Tail h ((2^h-1)*2).
Proof. rewrite (Nat.add_comm h 1); solve_rule LOv. Qed.

Lemma corner_three_front len:
  LC (len+2) 0 <| RC (2^(len+1)*3+1) -->+
  LC (len+3) (2^(len+2)+1) |> Tail (len+1) 0.
Proof.
  replace (2^(len+1)*3+1) with ((((1*2+1)*2^len)*2+1)*2^0) by arith.
  follow10 LC_Ov.
  follow100 (RC1_Ov_0 (len+2) (2^(len+2)-1) 0 len 1 ltac:(arith)).
  repeat rewrite Nat.add_0_r.
  replace (((2^(len+2)-1)*2+1)*2^(0*3)-1) with
    (2^(len+1)*3+(2^len-1)*2) by arith.
  follow RC2_Incs; [arith|arith|].
  replace (len+2+1) with (len+3) by lia.
  follow100 (RC2_Ov_inc (len+3) (2^(len+1)*3) len 0).
  replace (2^(len+1)*3) with (1+(2^(len+1)*3-1)) by arith.
  eapply evstep_trans; [apply progress_evstep; apply LC_Inc; arith|].
  replace (2^(len+2+1)-1) with
    (((0*2+1)*2^(len+1)-1)+(2^(len+1)*3-1)+1) by arith.
  follow RC3_Incs; [arith|arith|].
  replace (len+2) with (len+1+1) by lia.
  follow100 LC_Ov_tail.
  replace (2^(len+3)-1) with (2^(len+2)+1+(2^(len+1)-1)*2) by arith.
  follow Tail_Incs; [arith|arith|finish; f_equal; lia].
Qed.

Lemma Tail_Ov_0 len k a: k<2^len ->
  LC len k |> Tail (a*2) 0 -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> [1;0;1;1;1;0;0] *> 0inf.
Proof. solve_rule ROv1_0. Qed.
Lemma Tail_Ov_1 len k a: k<2^len ->
  LC len k |> Tail (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0;1;1;1;0;0] *> 0inf.
Proof. solve_rule ROv1_1. Qed.
Lemma Tail_end0 len k: k<2^len ->
  LC len k |> [1;0;1;1;1;0;0] *> 0inf -->+
  LC (len+2) ((k*2+1)*2) <| RC 1.
Proof.
  replace (len+2) with (len+1+1) by lia.
  epose proof (ROv2_short0 _ (rd1 *> 0inf) 0) as H; solve_rule H.
Qed.
Lemma Tail_end1 len k: 1+k<2^len ->
  LC len (1+k) |> [0;1;1;1;0;0] *> 0inf -->+
  LC (len+2) ((k*2+1)*2) |> RC 1.
Proof.
  intros; epose proof (RInc (LC len (1+k)) ([1;1;1;0;0] *> 0inf) 0) as H0.
  follow10 H0; follow_inc LC_Inc.
  replace (len+2) with (len+1+1) by lia.
  unfold LC,RC; rw_Bin; try solve[arith].
  follow100 ROv11_zero; epose proof (ROv1_0 _ 0inf 0) as H1; follow100 H1.
  finish; simpl_rotate; simpl_tape; reflexivity.
Qed.

Lemma LC_Inc' len k r: 0<k<2^len -> LC len k <| r -->+ LC len (k-1) |> r.
Proof. destruct k; intros; [lia|]; replace (S k-1) with k by lia; apply LC_Inc; lia. Qed.
Lemma LC_Ov_blank len:
  LC len 0 <| RC 0 -->+ LC len (2^len-1) |> RC 1.
Proof. solve_rule LOv. Qed.

Close Scope sym.
Inductive Config := cfgL (len k m:nat) | cfgR (len k m:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat) | cfgR3 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k m => LC len k <| RC m
| cfgR len k m => LC len k |> RC m
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
| cfgR3 len k h n m => LC len k |> RC3 h n m
end.
Definition P x := match x with
| cfgL len k m => 2<=len /\ k<2^len /\ k+m<2^len*2
| cfgR len k m => 2<=len /\ k<2^len /\ k+m+1<2^len*2
| cfgR1 len k h n m => (2<=len /\ n+m<=k<2^len /\ n<2^(h+1)) /\
    (h=0 -> forall i, m=2^i*3 -> n+2^i*5<=k)
| cfgR2 len k h n m => (2<=len /\ n+m<=k<2^len /\ n<2^(h+1)) /\
    (forall q, m=q*2+1 -> n+q+2^(h+3)+1<=k)
| cfgR3 len k h n m => 2<=len /\ n+m<=k<2^len /\ n<2^(h+1)
end.

Lemma closed_R1 len k h n m: P (cfgR1 len k h n m) ->
  exists y, to_config (cfgR1 len k h n m) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros [HP HG]; destruct n as [|n].
  2: { destruct k as [|k]; [lia|].
    eexists (cfgR1 _ _ _ _ _); split.
    - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    - cbn [P]; split; [lia|intros Eh i Em; specialize (HG Eh i Em); lia]. }
  divmod2_cases h; lowbit_cases m.
  - eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|cbn [P]; arith].
  - eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
    cbn [P]; split; [arith|].
    intros q Eq; subst x; destruct n' as [|a].
    + destruct q as [|q].
      * specialize (HG eq_refl i ltac:(arith)); arith.
      * arith.
    + replace (S a*3) with (a*3+3) in * by lia; arith.
  - eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|cbn [P]; arith].
  - eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
    cbn [P]; split; [arith|intros Ei j Ex; subst i x; arith].
Qed.

Lemma closed_R2 len k h n m: P (cfgR2 len k h n m) ->
  exists y, to_config (cfgR2 len k h n m) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros [HP HG]; destruct n as [|n].
  2: { destruct k as [|k]; [lia|].
    eexists (cfgR2 _ _ _ _ _); split.
    - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    - cbn [P]; split; [lia|intros q E; specialize (HG q E); lia]. }
  divmod2_cases m; rename n' into q.
  - divmod2_cases h; lowbit_cases q.
    + eexists (cfgL _ _ _); split; [apply RC2_Ov_0_blank; lia|cbn [P]; arith].
    + eexists (cfgR2 _ _ _ _ _); split.
      * eapply progress_evstep_trans; [apply RC2_Ov_0; lia|].
        apply progress_evstep; apply LC_Inc'; arith.
      * cbn [P]; split; [arith|intros q Eq; subst x; arith].
    + eexists (cfgL _ _ _); split; [apply RC2_Ov_1_blank; lia|cbn [P]; arith].
    + eexists (cfgR1 _ _ _ _ _); split.
      * eapply progress_evstep_trans; [apply RC2_Ov_1; lia|].
        apply progress_evstep; apply LC_Inc'; arith.
      * cbn [P]; split; [arith|intros Ei j Ex; subst i x; arith].
  - specialize (HG q eq_refl); eexists (cfgR3 _ _ _ _ _); split.
    + eapply progress_evstep_trans; [apply RC2_Ov_inc|].
      apply progress_evstep; apply LC_Inc'; arith.
    + cbn [P]; arith.
Qed.

Lemma closed_R3 len k h n m: P (cfgR3 len k h n m) ->
  exists y, to_config (cfgR3 len k h n m) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros HP; destruct n as [|n].
  2: { destruct k as [|k]; [lia|].
    eexists (cfgR3 _ _ _ _ _); split.
    - eapply progress_evstep_trans; [apply RC3_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    - cbn [P]; lia. }
  divmod2_cases h.
  - eexists (cfgR _ _ _); split; [apply RC3_Ov_0; lia|cbn [P]; arith].
  - lowbitS_cases m; eexists (cfgR1 _ _ _ _ _); split; [apply RC3_Ov_1; lia|].
    cbn [P]; split; [arith|intros Ei j Ex; subst i x; arith].
Qed.

Lemma closed_corner len: 1<=len ->
  exists y, LC (len+1) 0 <| RC (2^(len+1)) -->+ to_config y /\ P y.
Proof.
  intros Hlen; divmod2_cases len.
  - eexists (cfgL _ _ _); split.
    + eapply progress_evstep_trans; [apply corner_case|].
      apply progress_evstep; apply RC'_Ov_0; arith.
    + cbn [P]; arith.
  - eexists (cfgR _ _ _); split.
    + eapply progress_evstep_trans; [apply corner_case|].
      apply progress_evstep; apply RC'_Ov_1; arith.
    + cbn [P]; arith.
Qed.
Lemma closed_tail len k h: 2<=len -> k<2^len ->
  exists y, LC len k |> Tail h 0 -->+ to_config y /\ P y.
Proof.
  intros Hlen Hk; divmod2_cases h.
  - eexists (cfgL _ _ _); split.
    + eapply progress_evstep_trans; [apply Tail_Ov_0; lia|].
      apply progress_evstep; apply Tail_end0; arith.
    + cbn [P]; arith.
  - eexists (cfgR _ _ _); split.
    + eapply progress_evstep_trans; [apply Tail_Ov_1; lia|].
      replace ((k*2+1)*2^(n'*3+2)-1) with (1+((k*2+1)*2^(n'*3+2)-2)) by arith.
      apply progress_evstep; apply Tail_end1; arith.
    + cbn [P]; arith.
Qed.
Lemma closed_three len:
  exists y, LC (len+2) 0 <| RC (2^(len+1)*3+1) -->+ to_config y /\ P y.
Proof.
  destruct (closed_tail (len+3) (2^(len+2)+1) (len+1) ltac:(lia) ltac:(arith)) as [y [H HP]].
  exists y; split; [|exact HP].
  eapply progress_evstep_trans; [apply corner_three_front|apply progress_evstep; exact H].
Qed.

Lemma three_power_bound len i:
  2^i*6+1<2^(len+2)*2 -> 2^i*6+1<>2^(len+1)*3+1 -> 2^i*5<=2^(len+2)-1.
Proof.
  intros H E; assert (i<len+1) by (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
  destruct (Nat.eq_dec i len); [subst; arith|].
  assert (2^(i+1)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith.
Qed.
Lemma closed_L0 len m: P (cfgL len 0 m) ->
  exists y, to_config (cfgL len 0 m) -->+ to_config y /\ P y.
Proof.
  cbn [P to_config]; intros HP; destruct len as [|[|len]]; [lia|lia|].
  replace (S (S len)) with (len+2) in * by lia.
  destruct m as [|m].
  - eexists (cfgR _ _ _); split; [apply LC_Ov_blank|cbn [P]; arith].
  - destruct (Nat.eq_dec (S m) (2^(len+2))) as [E|E].
    + rewrite E; replace (len+2) with (len+1+1) by lia; apply closed_corner; lia.
    + destruct (Nat.eq_dec (S m) (2^(len+1)*3+1)) as [E3|E3].
      * rewrite E3; apply closed_three.
      * lowbitS_cases m.
        replace (S ((x*2+1)*2^i-1)) with ((x*2+1)*2^i) in * by arith.
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; split.
        -- pose proof (split_bound_v3 x i (len+2) ltac:(lia) E); arith.
        -- intros Ei j Ex; subst i x; apply three_power_bound; arith.
Qed.
Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x; try solve [apply closed_R1|apply closed_R2|apply closed_R3].
  - destruct k; [apply closed_L0|].
    cbn [P to_config]; intros HP; eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - cbn [P to_config]; intros HP; eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
Qed.
Theorem nonhalt_from len k m:
  c0 -->* to_config (cfgL len k m) -> P (cfgL len k m) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.

End Counter.
End Counter.

Open Scope sym.
Notation LC := Counter.LC.
Notation RC := Counter.RC.
End SOC23_TM156.

(* SOC23_TM156.TM156 *)
Module TM156.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String Compare_dec.

Import SOC23_TM156.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_0RA---").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2_zero0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) <* ld0 <| r.
Proof. es. Qed.
Lemma ROv2_zero1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+4) <| r.
Proof. es. Qed.
Lemma ROv2_inc l r n m:
  l |> rd1^^n *> [1;0;1;0;0;1;0;0] *> rd1^^m *> [0] *> r -->+
  l <| rd0^^(n+2) *> [0;1] *> rd0^^m *> [1] *> r.
Proof. es. Qed.

Lemma ROv2_short0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) <| r.
Proof. st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv11_split l r n:
  l |> rd1^^(n*2+2) *> [1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 <| r.
Proof. es. Qed.
Lemma ROv11_zero l r:
  l |> [1;1] *> r -->+ l <* ld0 |> r.
Proof. es. Qed.

Lemma ROv11_inc l r n m:
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^m *> [0] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) |> [0] *> rd0^^m *> [1] *> r.
Proof.
  st; sr_r; do 5 (simpl_rotate; step1); sr_r; step1; sr_l;
    do 4 (simpl_rotate; step1); finish; simpl_rotate; reflexivity.
Qed.

Lemma ROv2_short1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. st; sr_r; do 8 (simpl_rotate; step1); finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -[tm]->* (LC 4 10 <| RC 0).
Proof. unfold LC, RC; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (Counter.nonhalt_from tm C A LInc RInc LOv ROv1_0 ROv1_1
    ROv2_zero0 ROv2_zero1 ROv2_inc ROv2_short0 ROv11_split ROv11_zero ROv11_inc ROv2_short1);
    [exact init|cbn [Counter.P]; lia].
Qed.
End TM156.

(* SOC23_TM156.TM155 *)
Module TM155.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String Compare_dec.

Import SOC23_TM156.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_0RF0LD_0RB---").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2_zero0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) <* ld0 <| r.
Proof. es. Qed.
Lemma ROv2_zero1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+4) <| r.
Proof. es. Qed.
Lemma ROv2_inc l r n m:
  l |> rd1^^n *> [1;0;1;0;0;1;0;0] *> rd1^^m *> [0] *> r -->+
  l <| rd0^^(n+2) *> [0;1] *> rd0^^m *> [1] *> r.
Proof. es. Qed.

Lemma ROv2_short0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) <| r.
Proof. st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv11_split l r n:
  l |> rd1^^(n*2+2) *> [1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <* ld0 <| r.
Proof. es. Qed.
Lemma ROv11_zero l r:
  l |> [1;1] *> r -->+ l <* ld0 |> r.
Proof. es. Qed.

Lemma ROv11_inc l r n m:
  l |> rd1^^(n*2+1) *> [1;1] *> rd1^^m *> [0] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) |> [0] *> rd0^^m *> [1] *> r.
Proof.
  st; sr_r; do 5 (simpl_rotate; step1); sr_r; step1; sr_l;
    do 4 (simpl_rotate; step1); finish; simpl_rotate; reflexivity.
Qed.

Lemma ROv2_short1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. st; sr_r; do 8 (simpl_rotate; step1); finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -[tm]->* (LC 3 5 <| RC 3).
Proof. unfold LC, RC; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (Counter.nonhalt_from tm A B LInc RInc LOv ROv1_0 ROv1_1
    ROv2_zero0 ROv2_zero1 ROv2_inc ROv2_short0 ROv11_split ROv11_zero ROv11_inc ROv2_short1);
    [exact init|cbn [Counter.P]; lia].
Qed.
End TM155.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_TM191.v. *)
Module SOC23_TM191.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR QG:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1] {{QR}}> r) (at level 30).
Notation "l |G>" := (l <* [0;1] {{QG}}> [1] *> 0inf) (at level 30).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.

Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.

Hypothesis LOv_0: forall r n a b,
  ldh <* ld1^^n <| rd0^^(a*2) *> rd1^^(b+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(a*3+2) |> rd0^^b *> rd1 *> r.

Hypothesis LOv_1: forall r n a b,
  ldh <* ld1^^n <| rd0^^(a*2+1) *> rd1^^(b+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(a*3+3) |> [0] *> rd0^^b *> rd1 *> r.

Hypothesis ROv_00: forall l r a,
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) |> [0] *> r.

Hypothesis ROv_010: forall l r a b c,
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> rd0^^(b*2) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) <* ld1^^(b*3+2) |> rd0^^c *> rd1 *> r.

Hypothesis ROv_011: forall l r a b c,
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> rd0^^(b*2+1) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) <* ld1^^(b*3+3) |> [0] *> rd0^^c *> rd1 *> r.

Hypothesis ROv_10: forall l r a b c,
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> rd0^^(b*2) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+3) <* ld1^^(b*3+1) |> rd0^^c *> rd1 *> r.

Hypothesis ROv_11: forall l r a b c,
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> rd0^^(b*2+1) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+3) <* ld1^^(b*3+2) |> [0] *> rd0^^c *> rd1 *> r.

Hypothesis Glider: forall l,
  l |G> -->+ l <* ld1 |G>.

Hypothesis Blank0: forall l a,
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> 0inf -->+
  l <* ld1 <* ld0^^(a*3+2) |G>.

Hypothesis Blank1: forall l a,
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> 0inf -->+
  l <* ld1 <* ld0^^(a*3+3) |G>.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition RC1 h n m := BinDec2 [0] [1] [0;0] h n (rd1 *> RC m).
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC; rw_Bin;
  try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.

Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc m l: l |> RC m -->+ l <| RC (1+m).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc h n m l: 1+n<2^(h+1) ->
  l |> RC1 h (1+n) m -->+ l <| RC1 h n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov_0 len a b m:
  LC len 0 <| RC (((m*2+1)*2^(b+1)-1)*2^(a*2)) -->+
  LC (len+(a*3+2)) ((2^len-1)*2^(a*3+2)) |> RC ((m*2+1)*2^b).
Proof. solve_rule LOv_0. Qed.
Lemma LC_Ov_1 len a b m:
  LC len 0 <| RC (((m*2+1)*2^(b+1)-1)*2^(a*2+1)) -->+
  LC (len+(a*3+3)) ((2^len-1)*2^(a*3+3)) |> RC1 b ((2^b-1)*2+1) m.
Proof. solve_rule LOv_1. Qed.
Lemma RC1_Ov_00 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i*2) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv_00. Qed.
Lemma RC1_Ov_00_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv_00 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_010 len k a b c m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((((m*2+1)*2^(c+1)-1)*2^(b*2))*2+1) -->+
  LC (len+1+(a*3+2)+(b*3+2)) (((k*2+1)*2^(a*3+2)-1)*2^(b*3+2)) |> RC ((m*2+1)*2^c).
Proof. solve_rule ROv_010. Qed.
Lemma RC1_Ov_011 len k a b c m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((((m*2+1)*2^(c+1)-1)*2^(b*2+1))*2+1) -->+
  LC (len+1+(a*3+2)+(b*3+3)) (((k*2+1)*2^(a*3+2)-1)*2^(b*3+3)) |> RC1 c ((2^c-1)*2+1) m.
Proof. solve_rule ROv_011. Qed.
Lemma RC1_Ov_10 len k a b c m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 (((m*2+1)*2^(c+1)-1)*2^(b*2)) -->+
  LC (len+1+(a*3+3)+(b*3+1)) (((k*2+1)*2^(a*3+3)-1)*2^(b*3+1)) |> RC ((m*2+1)*2^c).
Proof. solve_rule ROv_10. Qed.
Lemma RC1_Ov_11 len k a b c m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 (((m*2+1)*2^(c+1)-1)*2^(b*2+1)) -->+
  LC (len+1+(a*3+3)+(b*3+2)) (((k*2+1)*2^(a*3+3)-1)*2^(b*3+2)) |> RC1 c ((2^c-1)*2+1) m.
Proof. solve_rule ROv_11. Qed.
Lemma RC1_Blank0 len k a:
  LC len k |> RC1 (a*2) 0 1 -->+
  LC len k <* ld1 <* ld0^^(a*3+2) |G>.
Proof. unfold RC1,RC; rw_Bin; apply Blank0. Qed.
Lemma RC1_Blank1 len k a:
  LC len k |> RC1 (a*2+1) 0 0 -->+
  LC len k <* ld1 <* ld0^^(a*3+3) |G>.
Proof. unfold RC1,RC; rw_Bin; apply Blank1. Qed.

Close Scope sym.
Inductive Config := cfgL (len k m:nat) | cfgR (len k m:nat)
  | cfgT (len k h n m:nat) | cfgG (l:Stream sym).
Definition to_config x := match x with
| cfgL len k m => LC len k <| RC m
| cfgR len k m => LC len k |> RC m
| cfgT len k h n m => LC len k |> RC1 h n m
| cfgG l => l |G>
end.
Definition P x := match x with
| cfgL len k m => 1<=len /\ k<2^len /\ 1<=k+m<2^len*2
| cfgR len k m => 1<=len /\ k<2^len /\ 1<=k+m+1<2^len*2
| cfgT len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgG _ => True
end.

Lemma runs_cases m: 0<m -> exists a b u,
  m=((u*2+1)*2^(b+1)-1)*2^a.
Proof.
  intros H; destruct (lowbit_cases' m) as [|x a]; [lia|].
  destruct (lowbitS_cases' x) as [u b].
  exists a,b,u; arith.
Qed.
Lemma runs_bounds a b u:
  (2^b-1)*2+1+u <= ((u*2+1)*2^(b+1)-1)*2^a /\
  (u*2+1)*2^b <= ((u*2+1)*2^(b+1)-1)*2^a.
Proof. arith. Qed.
Lemma capacity len: 1<=len -> 2<=2^len.
Proof. destruct len; cbn [Nat.pow]; intros; nia. Qed.
Lemma append_bounds len k s: k<2^len ->
  k<=(k*2+1)*2^s-1<2^(len+1+s).
Proof. intros; arith. Qed.
Lemma shift_good_R len k s m: 1<=len -> k<2^len -> m<=k ->
  P (cfgR (len+s) (k*2^s) m).
Proof. cbn [P]; intros; arith. Qed.
Lemma shift_good_T len k s b m: 1<=len -> k<2^len ->
  (2^b-1)*2+1+m<=k ->
  P (cfgT (len+s) (k*2^s) b ((2^b-1)*2+1) m).
Proof. cbn [P]; intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|l];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (runs_cases m ltac:(lia)) as [a [b [u ->]]].
      pose proof (capacity len ltac:(lia)).
      divmod2_cases a; rename n' into a.
      * eexists (cfgR _ _ _); split; [apply LC_Ov_0|].
        cbn [P]; pose proof (runs_bounds (a*2) b u); arith.
      * eexists (cfgT _ _ _ _ _); split; [apply LC_Ov_1|].
        cbn [P]; pose proof (runs_bounds (a*2+1) b u); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgT _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; rename n' into a.
    + divmod2_cases m; rename n' into b.
      * lowbit_cases b.
        -- eexists (cfgR _ _ _); split; [apply RC1_Ov_00_blank; lia|].
           cbn [P]; arith.
        -- eexists (cfgT _ _ _ _ _); split; [apply RC1_Ov_00; lia|].
           cbn [P]; pose proof (split_bound_v2 x i); arith.
      * destruct b as [|b].
        -- eexists (cfgG _); split; [apply RC1_Blank0|exact I].
        -- destruct (runs_cases (S b) ltac:(lia)) as [c [d [u E]]].
           rewrite E in HP |- *; divmod2_cases c; rename n' into c.
           ++ eexists (cfgR _ _ _); split; [apply RC1_Ov_010; lia|].
              pose proof (append_bounds len k (a*3+2) ltac:(lia)).
              pose proof (runs_bounds (c*2) d u); apply shift_good_R; lia.
           ++ eexists (cfgT _ _ _ _ _); split; [apply RC1_Ov_011; lia|].
              pose proof (append_bounds len k (a*3+2) ltac:(lia)).
              pose proof (runs_bounds (c*2+1) d u); apply shift_good_T; lia.
    + destruct m as [|m].
      * eexists (cfgG _); split; [apply RC1_Blank1|exact I].
      * destruct (runs_cases (S m) ltac:(lia)) as [b [c [u E]]].
        rewrite E in HP |- *; divmod2_cases b; rename n' into b.
        -- eexists (cfgR _ _ _); split; [apply RC1_Ov_10; lia|].
           pose proof (append_bounds len k (a*3+3) ltac:(lia)).
           pose proof (runs_bounds (b*2) c u); apply shift_good_R; lia.
        -- eexists (cfgT _ _ _ _ _); split; [apply RC1_Ov_11; lia|].
           pose proof (append_bounds len k (a*3+3) ltac:(lia)).
           pose proof (runs_bounds (b*2+1) c u); apply shift_good_T; lia.
  - exists (cfgG (l <* ld1)); split; [apply Glider|exact I].
Qed.

Theorem nonhalt_from len k m:
  c0 -->* to_config (cfgL len k m) -> P (cfgL len k m) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_TM191.

(* SOC23_TM191.TM191 *)
Module TM191.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC23_TM191.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC1LB_1RF1RD_0RE0RC_1LA1RC_1RE---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{B}} [1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1] {{E}}> r) (at level 30).
Notation "l |G>" := (l <* [0;1] {{C}}> [1] *> 0inf) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv_0 r n a b:
  ldh <* ld1^^n <| rd0^^(a*2) *> rd1^^(b+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(a*3+2) |> rd0^^b *> rd1 *> r.
Proof. es. Qed.

Lemma LOv_1 r n a b:
  ldh <* ld1^^n <| rd0^^(a*2+1) *> rd1^^(b+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(a*3+3) |> [0] *> rd0^^b *> rd1 *> r.
Proof. es. Qed.

Lemma ROv_00 l r a:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) |> [0] *> r.
Proof. es. Qed.

Lemma ROv_010 l r a b c:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> rd0^^(b*2) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) <* ld1^^(b*3+2) |> rd0^^c *> rd1 *> r.
Proof. es. Qed.

Lemma ROv_011 l r a b c:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> rd0^^(b*2+1) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) <* ld1^^(b*3+3) |> [0] *> rd0^^c *> rd1 *> r.
Proof. es. Qed.

Lemma ROv_10 l r a b c:
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> rd0^^(b*2) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+3) <* ld1^^(b*3+1) |> rd0^^c *> rd1 *> r.
Proof. es. Qed.

Lemma ROv_11 l r a b c:
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> rd0^^(b*2+1) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+3) <* ld1^^(b*3+2) |> [0] *> rd0^^c *> rd1 *> r.
Proof. es. Qed.

Lemma Glider l:
  l |G> -->+ l <* ld1 |G>.
Proof. es. Qed.

Lemma Blank0_gen l r a:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) <* [0;1] {{C}}> rd1 *> r.
Proof. es. Qed.
Lemma Blank1_gen l r a:
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*3+3) <* [0;1] {{C}}> [1] *> r.
Proof. es. Qed.
Lemma Blank0 l a:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> 0inf -->+
  l <* ld1 <* ld0^^(a*3+2) |G>.
Proof.
  pose proof (Blank0_gen l 0inf a) as H; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; exact H.
Qed.

Lemma Blank1 l a:
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> 0inf -->+
  l <* ld1 <* ld0^^(a*3+3) |G>.
Proof. apply Blank1_gen. Qed.
Lemma init: c0 -->* Counter.LC 7 60 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=B) (QR:=E) (QG:=C)
    (len:=7) (k:=60) (m:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv_0|exact LOv_1|exact ROv_00|
    exact ROv_010|exact ROv_011|exact ROv_10|exact ROv_11|exact Glider|
    exact Blank0|exact Blank1|exact init|cbn [Counter.P]; lia].
Qed.
End TM191.

(* SOC23_TM191.TM192 *)
Module TM192.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC23_TM191.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RD1LC_1RF1RE_0RA0RD_1RA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1] {{A}}> r) (at level 30).
Notation "l |G>" := (l <* [0;1] {{D}}> [1] *> 0inf) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv_0 r n a b:
  ldh <* ld1^^n <| rd0^^(a*2) *> rd1^^(b+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(a*3+2) |> rd0^^b *> rd1 *> r.
Proof. es. Qed.

Lemma LOv_1 r n a b:
  ldh <* ld1^^n <| rd0^^(a*2+1) *> rd1^^(b+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(a*3+3) |> [0] *> rd0^^b *> rd1 *> r.
Proof. es. Qed.

Lemma ROv_00 l r a:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) |> [0] *> r.
Proof. es. Qed.

Lemma ROv_010 l r a b c:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> rd0^^(b*2) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) <* ld1^^(b*3+2) |> rd0^^c *> rd1 *> r.
Proof. es. Qed.

Lemma ROv_011 l r a b c:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> rd0^^(b*2+1) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) <* ld1^^(b*3+3) |> [0] *> rd0^^c *> rd1 *> r.
Proof. es. Qed.

Lemma ROv_10 l r a b c:
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> rd0^^(b*2) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+3) <* ld1^^(b*3+1) |> rd0^^c *> rd1 *> r.
Proof. es. Qed.

Lemma ROv_11 l r a b c:
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> rd0^^(b*2+1) *> rd1^^(c+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(a*3+3) <* ld1^^(b*3+2) |> [0] *> rd0^^c *> rd1 *> r.
Proof. es. Qed.

Lemma Glider l:
  l |G> -->+ l <* ld1 |G>.
Proof. es. Qed.

Lemma Blank0_gen l r a:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(a*3+2) <* [0;1] {{D}}> rd1 *> r.
Proof. es. Qed.
Lemma Blank1_gen l r a:
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*3+3) <* [0;1] {{D}}> [1] *> r.
Proof. es. Qed.
Lemma Blank0 l a:
  l |> rd1^^(a*2) *> [1;1;0;0] *> rd1 *> 0inf -->+
  l <* ld1 <* ld0^^(a*3+2) |G>.
Proof.
  pose proof (Blank0_gen l 0inf a) as H; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; exact H.
Qed.

Lemma Blank1 l a:
  l |> rd1^^(a*2+1) *> [1;1;0;0] *> 0inf -->+
  l <* ld1 <* ld0^^(a*3+3) |G>.
Proof. apply Blank1_gen. Qed.
Lemma init: c0 -->* Counter.LC 8 188 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (QG:=D)
    (len:=8) (k:=188) (m:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv_0|exact LOv_1|exact ROv_00|
    exact ROv_010|exact ROv_011|exact ROv_10|exact ROv_11|exact Glider|
    exact Blank0|exact Blank1|exact init|cbn [Counter.P]; lia].
Qed.
End TM192.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_TM193.v. *)
Module SOC23_TM193.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
End SOC23_TM193.

(* SOC23_TM193.TM193 *)
Module TM193.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC23_TM193.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RD1LC_1RF1RE_0RB0RD_1RA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1] {{A}}> r) (at level 30).
Notation "l |E> r" := (l <* <[1] {{E}}> r) (at level 30).
Notation "l |Z> r" := (l {{E}}> r) (at level 30).
Notation "l |T> r" := (l <* <[0;1;1] {{A}}> r) (at level 30).
Notation "l <I r" := (l <{{C}} [1] *> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n m k:
  ldh <* ld1^^n <| rd0^^(m*2) *> rd1^^(k+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0^^(m*3+1) |> rd0^^k *> rd1 *> r.
Proof. es. Qed.
Lemma LOv_1 r n m:
  ldh <* ld1^^n <| rd0^^(m*2+1) *> rd1 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0^^(m*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma R_short0 l r n:
  l |> rd1^^(n*2) *> [1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) |Z> r.
Proof. es. Qed.
Lemma R_short1 l r n:
  l |> rd1^^(n*2+1) *> [1;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+3) |E> r.
Proof. es. Qed.
Lemma E_shift l r n:
  l |E> [0;0]^^n *> r -->* l <* ld1^^n |E> r.
Proof. es. Qed.
Lemma E_delim0 l r:
  l |E> [0;1;0;0] *> r -->+ l <| [0] *> r.
Proof. es. Qed.
Lemma E_pairs l r n:
  l |E> [0;0]^^n *> rd1 *> r -->+ l <* ld1^^n |> r.
Proof. es. Qed.
Lemma E_delim l r n:
  l |E> [0;0]^^n *> [0;1;0;0] *> r -->+ l <* ld1^^n <| [0] *> r.
Proof. follow E_shift. apply E_delim0. Qed.
Lemma Z_pairs l r n:
  l |Z> [0;0]^^n *> rd1 *> r -->+ l <* ld1^^n |T> r.
Proof. es. Qed.
Lemma Z_delim l r n:
  l |Z> [0;0]^^n *> [0;1;0;0] *> r -->+ l <* ld1^^n <I rd0 *> r.
Proof. es. Qed.
Lemma I_inc l r n:
  l <* ld0 <* ld1^^n <I r -->+ l <* ld1 <* ld0^^n |E> r.
Proof. es. Qed.
Lemma T_start l r n:
  l |T> rd1^^n *> rd0 *> r -->+ l <I [0]^^(n*3+2) *> rd1 *> r.
Proof. es. Qed.
Lemma E_glider l: l |E> 0inf -->+ l <* ld1 |E> 0inf.
Proof. es. Qed.
Lemma Z_glider l: l |Z> 0inf -->+ l <* ld1 |Z> 0inf.
Proof. es. Qed.
Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC n := BinInc rd1 n.
Definition MC h n m := BinDec2 [0] [1] [0;0] h n (rd1 *> RC m).
Definition Bits a m := [0]^^a *> rd1 *> RC m.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC,MC,Bits; rw_Bin;
  try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.

Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma IC_Inc len k r: 1+k<2^len -> LC len (1+k) <I r -->+ LC len k |E> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule I_inc. Qed.
Lemma RC_Inc l n: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma MC_Inc l h n m: 1+n<2^(h+1) ->
  l |> MC h (1+n) m -->+ l <| MC h n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov0 len a b m:
  LC len 0 <| RC (((m*2+1)*2^(b+1)-1)*2^(a*2)) -->+
  LC (len+1+(a*3+1)) (((2^len-1)*2+1)*2^(a*3+1)-1) |> RC ((m*2+1)*2^b).
Proof. solve_rule LOv_0. Qed.
Lemma LC_Ov1 len a m:
  LC len 0 <| RC ((m*2+1)*2^(a*2+1)) -->+
  LC (len+1+(a*3+2)) (((2^len-1)*2+1)*2^(a*3+2)-1) |> [0] *> RC m.
Proof. solve_rule LOv_1. Qed.
Lemma MC_Ov0 len k a r: k<2^len ->
  LC len k |> MC (a*2) 0 r -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |Z> [0;0] *> RC r.
Proof. solve_rule R_short0. Qed.
Lemma MC_Ov1 len k a r: k<2^len ->
  LC len k |> MC (a*2+1) 0 r -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) |E> [0;0] *> RC r.
Proof. solve_rule R_short1. Qed.
Lemma E_even len k a m: k<2^len ->
  LC len k |E> Bits (a*2) m -->+ LC (len+a) (k*2^a) |> RC m.
Proof. unfold Bits; rewrite lpow_mul; solve_rule E_pairs. Qed.
Lemma E_odd len k a m: k<2^len ->
  LC len k |E> Bits (a*2+1) m -->+ LC (len+a) (k*2^a) <| [0] *> RC m.
Proof. unfold Bits; st; solve_rule E_delim. Qed.
Lemma Z_even len k a m: k<2^len ->
  LC len k |Z> Bits (a*2) m -->+ LC (len+a) (k*2^a) |T> RC m.
Proof. unfold Bits; rewrite lpow_mul; solve_rule Z_pairs. Qed.
Lemma Z_odd len k a m: k<2^len ->
  LC len k |Z> Bits (a*2+1) m -->+ LC (len+a) (k*2^a) <I RC (m*2).
Proof. unfold Bits; st; solve_rule Z_delim. Qed.
Lemma T_step len k a m:
  LC len k |T> RC ((m*2+1)*2^a-1) -->+ LC len k <I Bits (a*3+2) m.
Proof. solve_rule T_start. Qed.

Lemma Bits_low a i m:
  [0]^^a *> RC ((m*2+1)*2^i) = Bits (a+i*3) m.
Proof. unfold RC,Bits; rw_Bin; st; reflexivity. Qed.
Lemma Bits_zero a: [0]^^a *> RC 0 = 0inf.
Proof. unfold RC; rw_Bin; apply lpow_all0_1. Qed.

Lemma init: c0 -->* LC 4 0 <| RC 16.
Proof. unfold LC,RC; esx. Qed.

(* Whole-tape phase budgets; see SOC_ANALYSIS.md, section 49. *)
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgM (len k h n m:nat) | cfgE (len k a m:nat) | cfgZ (len k a m:nat)
  | cfgT (len k m:nat) | cfgG (isE:bool) (l:side).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgM len k h n m => LC len k |> MC h n m
| cfgE len k a m => LC len k |E> Bits a m
| cfgZ len k a m => LC len k |Z> Bits a m
| cfgT len k m => LC len k |T> RC m
| cfgG true l => l |E> 0inf
| cfgG false l => l |Z> 0inf
end.
Close Scope sym.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 0<k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 0<k+n+1<2^len*2
| cfgM len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgE len k a m => 1<=len /\ m*2+2<=k<2^len
| cfgZ len k _ m | cfgT len k m => 1<=len /\ m*2+3<=k<2^len
| cfgG _ _ => True
end.
Open Scope sym.

Lemma zero_mark len k m: 1<=len -> m*2<=k<2^len ->
  exists y, (LC len k |> [0] *> RC m) = to_config y /\ P y.
Proof.
  intros HL HK; lowbit_cases m.
  - exists (cfgR len k 0); split.
    + cbn [to_config]; unfold RC; rw_Bin; st; reflexivity.
    + cbn [P]; arith.
  - exists (cfgM len k i ((2^i-1)*2+1) x); split.
    + cbn [to_config]; unfold RC,MC; rw_Bin; st; reflexivity.
    + cbn [P]; pose proof (split_bound_v2 x i); arith.
Qed.

Lemma tail_ready (isE:bool) len k a m: 1<=len -> m+2<=k<2^len ->
  exists y, (if isE then LC len k |E> [0]^^a *> RC m
             else LC len k |Z> [0]^^a *> RC m) = to_config y /\ P y.
Proof.
  intros HL HK; destruct isE; lowbit_cases m.
  - exists (cfgG true (LC len k)); split; [rewrite Bits_zero; reflexivity|exact I].
  - exists (cfgE len k (a+i*3) x); split.
    + rewrite Bits_low; reflexivity.
    + cbn [P]; arith.
  - exists (cfgG false (LC len k)); split; [rewrite Bits_zero; reflexivity|exact I].
  - exists (cfgZ len k (a+i*3) x); split.
    + rewrite Bits_low; reflexivity.
    + cbn [P]; arith.
Qed.

Lemma capacity len: 1<=len -> 2<=2^len.
Proof. destruct len; cbn [Nat.pow]; intros; nia. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k a m|len k a m|len k m|isE l];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + lowbit_cases m; [lia|].
      pose proof (capacity len ltac:(lia)).
      divmod2_cases i; rename n' into a.
      * lowbitS_cases x.
        replace (((x0*2+1)*2^i-1)*2+1) with ((x0*2+1)*2^(i+1)-1) in * by arith.
        eexists (cfgR _ _ _); split; [apply LC_Ov0|cbn [P]; arith].
      * destruct (zero_mark (len+1+(a*3+2))
          (((2^len-1)*2+1)*2^(a*3+2)-1) x ltac:(lia) ltac:(arith)) as [y [Ey Hy]].
        exists y; split; [rewrite <-Ey; apply LC_Ov1|exact Hy].
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgM _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply MC_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; rename n' into a.
    + destruct (tail_ready false (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) 2 m
        ltac:(lia) ltac:(arith)) as [y [Ey Hy]].
      exists y; split; [rewrite <-Ey; apply MC_Ov0; lia|exact Hy].
    + destruct (tail_ready true (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) 2 m
        ltac:(lia) ltac:(arith)) as [y [Ey Hy]].
      exists y; split; [rewrite <-Ey; apply MC_Ov1; lia|exact Hy].
  - divmod2_cases a; rename n' into a.
    + eexists (cfgR _ _ _); split; [apply E_even; lia|cbn [P]; arith].
    + destruct (zero_mark (len+a) (k*2^a-1) m ltac:(lia) ltac:(arith)) as [y [Ey Hy]].
      exists y; split; [rewrite <-Ey|exact Hy].
      eapply progress_evstep_trans; [apply E_odd; lia|].
      assert (0<k*2^a) by arith.
      apply progress_evstep; applys_eq LC_Inc; [flia|arith].
  - divmod2_cases a; rename n' into a.
    + eexists (cfgT _ _ _); split; [apply Z_even; lia|cbn [P]; arith].
    + destruct (tail_ready true (len+a) (k*2^a-1) 0 (m*2)
        ltac:(lia) ltac:(arith)) as [y [Ey Hy]].
      exists y; split; [rewrite <-Ey|exact Hy].
      eapply progress_evstep_trans; [apply Z_odd; lia|].
      assert (0<k*2^a) by arith.
      apply progress_evstep; applys_eq IC_Inc; [flia|arith].
  - lowbitS_cases m.
    destruct k as [|k]; [lia|].
    eexists (cfgE _ _ _ _); split.
    + eapply progress_evstep_trans; [apply T_step|].
      apply progress_evstep; apply IC_Inc; lia.
    + cbn [P]; arith.
  - destruct isE.
    + exists (cfgG true (l <* ld1)); split; [apply E_glider|exact I].
    + exists (cfgG false (l <* ld1)); split; [apply Z_glider|exact I].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  change (~halts tm (to_config (cfgL 4 0 16))).
  eapply progress_nonhalt_cond with (P:=P); [apply closed|].
  cbn [P]; lia.
Qed.

End TM193.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_TM212.v. *)
Module SOC23_TM212.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation d := [1;0;0].
Notation z := [0;0;0].
Notation M := [1;0;1;1;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q) (wl wr:list sym).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} wl *> r) (at level 30).
Notation "l |> r" := (l <* wr {{QR}}> r) (at level 30).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> d^^n *> [0] *> r -->+ l <| z^^n *> [1] *> r.
Hypothesis LOv_0: forall r n,
  ldh <* ld1^^(n+1) <| z *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0 |> [0;0] *> r.
Hypothesis LOv_1: forall r n,
  ldh <* ld1^^(n+1) <| d *> r -->+
  ldh <* ld0^^n <* ld1 <* ld1 <* ld0 |> r.
Hypothesis ROv2: forall l r n,
  l |> d^^n *> [1;0;1;0;0] *> r -->+ l <| z^^n *> [0;0;1;1;0] *> r.
Hypothesis ROv3_odd: forall l r a,
  l |> d^^(a*2+1) *> M *> r -->+ l <* ld0 <* ld1^^(a*3+3) |> r.
Hypothesis ROv3_even0: forall l r a,
  l |> d^^(a*2) *> M *> z *> r -->+
  l <* ld1 <* ld0^^(a*3) <* ld1 <* ld1 <* ld0 |> r.
Hypothesis ROv3_even_head: forall l r a,
  l |> d^^(a*2) *> M *> r -->+ l <* ld0 <* ld1^^(a*3+1) <* <[1] |> r.
Hypothesis Half_zero: forall l r n,
  l <* ld0 <* ld1^^(n+1) <* <[1] <| z *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0 |> [0;0] *> r.
Hypothesis Half_one: forall l r n,
  l <* ld0 <* ld1^^(n+1) <* <[1] <| d *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld1 <* ld0 |> r.
Hypothesis ROv3_even1: forall l r a b,
  l |> d^^(a*2) *> M *> d^^(b+1) *> z *> r -->+
  l <* ld1 <* ld0^^(a*3) <* ld1 <* ld0 |> z^^b *> [0;0;1;0;0] *> r.
Hypothesis Corner_prefix: forall r n h,
  ldh <* ld1^^(3+n) <| [0] *> [0;0;1]^^(2+h) *> [0;1;1;0] *> r -->+
  ldh <* ld0^^(1+n) <* ld1 <* ld0 <* ld1 |> M *> d^^h *> M *> r.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc d m.
Definition T2 h n m := BinDec2 [0] [1] [0;0] h n ([0;1;0;0] *> RC m).
Definition T3 h n m := BinDec2 [0] [1] [0;0] h n ([0;1;1;0] *> RC m).
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,T2,T3,RC; rw_Bin;
  try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.
Ltac inc H := eapply evstep_trans; [apply progress_evstep; apply H; first[lia|arith]|].

Lemma Left_Inc l len k r: 1+k<2^len ->
  BinDec ld0 ld1 len (1+k) l <| r -->+ BinDec ld0 ld1 len k l |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. apply Left_Inc. Qed.
Lemma RC_Inc l m: l |> RC m -->+ l <| RC (1+m).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma Mark_Inc l h n r: 1+n<2^(h+1) ->
  l |> BinDec2 [0] [1] [0;0] h (1+n) r -->+
  l <| BinDec2 [0] [1] [0;0] h n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma Sweep l len k m: k<2^len ->
  BinDec ld0 ld1 len k l |> RC m -->+ l <* ld1^^len <| RC (m+k+1).
Proof.
  gen m; induction k; intros m Hk.
  - rewrite BinDec_O. replace (m+0+1) with (1+m) by lia; apply RC_Inc.
  - follow10 RC_Inc; follow100 (Left_Inc l len k (RC (1+m)) Hk).
    replace (m+S k+1) with (1+m+k+1) by lia.
    apply progress_evstep,IHk; lia.
Qed.
Lemma Mark_pairs len k h n r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> BinDec2 [0] [1] [0;0] h n r -->*
  LC len k |> BinDec2 [0] [1] [0;0] h 0 r.
Proof.
  gen k; induction n; intros k Hk Hn; [rewrite Nat.add_0_r; finish|].
  inc Mark_Inc. rewrite Nat.add_succ_r.
  inc LC_Inc. apply IHn; lia.
Qed.
Lemma Mark_left len k h n r: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> BinDec2 [0] [1] [0;0] h (n+k+1) r -->*
  LC len 0 <| BinDec2 [0] [1] [0;0] h n r.
Proof.
  induction k; intros Hk Hn.
  - replace (n+0+1) with (1+n) by lia; apply progress_evstep,Mark_Inc; lia.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    inc Mark_Inc. inc LC_Inc. apply IHk; lia.
Qed.

Lemma Double_odd l a:
  l |> M *> d^^(a*2+1) *> M *> 0inf -->+
  l <* ld0 <* ld1^^(a*3+5) <* <[1] <| RC (2^(a*3+3)+1).
Proof.
  follow10 (ROv3_even_head l (d^^(a*2+1) *> M *> 0inf) 0);
    cbn [Nat.mul Nat.add lpow Str_app].
  follow100 ROv3_odd.
  pose proof (Sweep (l <* ld0 <* ld1 <* <[1]) (1+(a*3+3)) ((0*2+1)*2^(a*3+3)) 0
    ltac:(arith)) as H.
  revert H; rw_Bin; try solve[arith]; intro H.
  follow100 H.
  repeat (simpl_rotate || simpl_tape); finish.
Qed.
Lemma Double_even l a:
  l |> M *> d^^(a*2) *> M *> 0inf -->+
  l <* ld0 <* ld1^^(a*3+5) <* <[1] <| RC (2^(a*3+3)-6).
Proof.
  follow10 (ROv3_even_head l (d^^(a*2) *> M *> 0inf) 0);
    cbn [Nat.mul Nat.add lpow Str_app].
  pose proof (ROv3_even0 (l <* ld0 <* ld1 <* <[1]) 0inf a) as E.
  cbn [Str_app] in E; repeat rewrite <-(const_unfold _ 0) in E.
  cbn [Str_app List.app]; repeat rewrite <-(const_unfold _ 0); follow100 E.
  pose proof (Sweep (l <* ld0 <* ld1 <* <[1]) (1+a*3+1+1+1)
    (((((0*2+1)*2^(a*3)-1)*2)*2)*2+1) 0 ltac:(arith)) as H.
  revert H; rw_Bin; try solve[arith]; intro H.
  follow100 H.
  replace (0+(((((0*2+1)*2^(a*3)-1)*2)*2)*2+1)+1) with (2^(a*3+3)-6) by arith.
  clear E H. replace (1+a*3+1+1+1) with (1+(a*3+3)) by lia.
  do 2 (try simpl_rotate; try simpl_tape); finish.
Qed.
Lemma LC_tail3 len k q: k<2^len ->
  LC (len+1+q+3) ((k*2+1)*2^(q+3)-7) =
  LC len k <* ld1 <* ld0^^q <* ld1 <* ld1 <* ld0.
Proof.
  intros Hk; unfold LC.
  replace (len+1+q+3) with (len+1+q+1+1+1) by lia.
  replace ((k*2+1)*2^(q+3)-7) with (((((k*2+1)*2^q-1)*2)*2)*2+1) by arith.
  rw_Bin; try solve[arith]; reflexivity.
Qed.
Lemma LC_tail2 len k q: k<2^len ->
  LC (len+1+q+2) ((k*2+1)*2^(q+2)-3) =
  LC len k <* ld1 <* ld0^^q <* ld1 <* ld0.
Proof.
  intros Hk; unfold LC.
  replace (len+1+q+2) with (len+1+q+1+1) by lia.
  replace ((k*2+1)*2^(q+2)-3) with ((((k*2+1)*2^q-1)*2)*2+1) by arith.
  rw_Bin; try solve[arith]; reflexivity.
Qed.
Lemma LC_Ov_0 len h m:
  LC (len+1) 0 <| RC ((m*2+1)*2^(h+1)) -->+
  LC (len+2) ((2^len-1)*2*2+1) |> T2 h (2^(h+1)-1) m.
Proof.
  replace (len+2) with (len+1+1) by lia.
  rewrite (Nat.add_comm h 1) at 1; solve_rule LOv_0.
Qed.
Lemma LC_Ov_1 len m:
  LC (len+1) 0 <| RC (m*2+1) -->+
  LC (len+3) ((2^len-1)*2*2*2+1) |> RC m.
Proof. replace (len+3) with (len+1+1+1) by lia; solve_rule LOv_1. Qed.
Lemma T2_Ov len k h m:
  LC len k |> T2 h 0 m -->+ LC len k <| T3 h (2^(h+1)-1) m.
Proof. solve_rule ROv2. Qed.
Lemma T3_Odd len k a m: k<2^len ->
  LC len k |> T3 (a*2+1) 0 m -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) |> RC m.
Proof. solve_rule ROv3_odd. Qed.
Lemma T3_Even0 len k a m: k<2^len ->
  LC len k |> T3 (a*2) 0 (m*2) -->+
  LC (len+1+a*3+3) ((k*2+1)*2^(a*3+3)-7) |> RC m.
Proof. intros H; rewrite LC_tail3 by lia; solve_rule ROv3_even0. Qed.
Lemma T3_Even1 len k a b m: k<2^len ->
  LC len k |> T3 (a*2) 0 ((m*2+1)*2^(b+1)-1) -->+
  LC (len+1+a*3+2) ((k*2+1)*2^(a*3+2)-3) |> T2 b (2^(b+1)-1) m.
Proof. intros H; rewrite LC_tail2 by lia; solve_rule ROv3_even1. Qed.
Lemma Double_Odd len k a: k<2^len ->
  LC len k |> M *> d^^(a*2+1) *> M *> 0inf -->+
  LC (len+1+(a*3+4)+3) ((k*2+1)*2^(a*3+4+3)-7) |> RC (2^(a*3+2)).
Proof.
  intros H; rewrite LC_tail3 by lia; follow10 Double_odd.
  replace (a*3+5) with (a*3+4+1) by lia.
  replace (2^(a*3+3)+1) with (2^(a*3+2)*2+1) by arith.
  unfold RC; rw_Bin; apply progress_evstep; follow_rule Half_one.
Qed.
Lemma Double_Even len k a: k<2^len ->
  LC len k |> M *> d^^(a*2) *> M *> 0inf -->+
  LC (len+1+(a*3+4)+2) ((k*2+1)*2^(a*3+4+2)-3) |> T2 0 1 (2^(a*3+1)-2).
Proof.
  intros H; rewrite LC_tail2 by lia; follow10 Double_even.
  replace (a*3+5) with (a*3+4+1) by lia.
  replace (2^(a*3+3)-6) with (((2^(a*3+1)-2)*2+1)*2) by arith.
  unfold T2,RC; rw_Bin; apply progress_evstep; follow_rule Half_zero.
Qed.
Lemma Corner_ready len: 1<=len ->
  LC (len+1) 0 <| RC (2^(len+1)) -->+ LC (len+2) 0 <| T3 len 1 0.
Proof.
  intros Hl; assert (2<=2^len) by (destruct len; cbn [Nat.pow] in *; lia).
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) at 1 by lia.
  follow10 LC_Ov_0.
  replace ((2^len-1)*2*2+1) with ((2^(len+1)-2)+(2^(len+1)-1)) by arith.
  unfold T2 at 1; follow Mark_pairs; [arith|arith|].
  follow100 T2_Ov.
  replace (2^(len+1)-2) with (1+(2^(len+1)-3)) by arith; inc LC_Inc.
  replace (2^(len+1)-1) with (1+(2^(len+1)-3)+1) by arith.
  unfold T3 at 1; follow Mark_left; [arith|arith|finish].
Qed.
Lemma Corner_start n:
  LC (n+3) 0 <| RC (2^(n+3)) -->+
  LC (n+5) (2^(n+5)-6) |> M *> d^^n *> M *> 0inf.
Proof.
  replace (n+3) with (n+2+1) by lia.
  follow10 (Corner_ready (n+2) ltac:(lia)).
  replace (n+5) with (n+2+1+1+1) by lia.
  replace (2^(n+2+1+1+1)-6) with (((2^(n+2)-1)*2*2+1)*2) by arith.
  unfold LC,T3,RC; rewrite (BinDec2_mul2add1 [0] [1] [0;0] (n+2) 0).
  rw_Bin; try solve[arith].
  pose proof (Corner_prefix 0inf (n+1) n) as H.
  replace (3+(n+1)) with (n+2+2) in H by lia.
  replace (1+(n+1)) with (n+2) in H by lia.
  replace (2+n) with (n+2) in H by lia.
  apply progress_evstep; follow_rule H.
Qed.
Close Scope sym.
Inductive Config := cfgL (len k m:nat) | cfgR (len k m:nat)
  | cfg2 (len k h n m:nat) | cfg3 (len k h n m:nat) | cfgD (len k h:nat).
Definition to_config x := match x with
| cfgL len k m => LC len k <| RC m
| cfgR len k m => LC len k |> RC m
| cfg2 len k h n m => LC len k |> T2 h n m
| cfg3 len k h n m => LC len k |> T3 h n m
| cfgD len k h => LC len k |> M *> d^^h *> M *> 0inf%sym
end.
Definition P x := match x with
| cfgL len k m => 3<=len /\ k<2^len /\ 1<=k+m<2^(len+1)
| cfgR len k m => 3<=len /\ k<2^len /\ 1<=k+m+1<2^(len+1)
| cfg2 len k h n m => 3<=len /\ k<2^len /\ n<2^(h+1) /\ n+2^(h+1)+m<=k
| cfg3 len k h n m => 3<=len /\ k<2^len /\ n<2^(h+1) /\ n+m<=k
| cfgD len k _ => 3<=len /\ k<2^len
end.
Lemma capacity len: 3<=len -> 8<=2^len.
Proof. destruct len as [|[|[|len]]]; cbn [Nat.pow]; intros; lia. Qed.
Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k h];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|[|[|n]]]; try (cbn in HP; lia).
        replace (S (S (S n))) with (n+3) in * by lia.
        exists (cfgD (n+5) (2^(n+5)-6) n); split; [apply Corner_start|].
        cbn [P]; arith.
      * destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) in * by lia.
        pose proof (capacity (len+1) ltac:(lia)).
        destruct (lowbit_cases' m) as [|u i]; [lia|].
        destruct i as [|i].
        -- cbn [Nat.pow] in *; rewrite Nat.mul_1_r in *.
           exists (cfgR (len+3) ((2^len-1)*2*2*2+1) u); split; [apply LC_Ov_1|].
           cbn [P]; arith.
        -- replace (S i) with (i+1) in * by lia.
           pose proof (split_bound_v3 u (i+1) (len+1) ltac:(arith) E).
           exists (cfg2 (len+2) ((2^len-1)*2*2+1) i (2^(i+1)-1) u).
           split; [apply LC_Ov_0|cbn [P]; arith].
    + exists (cfgR len k m); split; [apply LC_Inc; lia|cbn [P]; lia].
  - exists (cfgL len k (1+m)); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n]; destruct k as [|k]; try (cbn in HP; lia).
    + exists (cfg3 len k h (2^(h+1)-1) m); split.
      * eapply progress_evstep_trans; [apply T2_Ov|].
        apply progress_evstep,LC_Inc; lia.
      * cbn [P]; lia.
    + exists (cfg2 len k h n m); split.
      * eapply progress_evstep_trans; [apply Mark_Inc; lia|].
        apply progress_evstep,LC_Inc; lia.
      * cbn [P]; lia.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      exists (cfg3 len k h n m); split.
      - eapply progress_evstep_trans; [apply Mark_Inc; lia|].
        apply progress_evstep,LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; rename n' into a.
    + divmod2_cases m; rename n' into b.
      * exists (cfgR (len+1+a*3+3) ((k*2+1)*2^(a*3+3)-7) b).
        split; [apply T3_Even0; lia|cbn [P]; arith].
      * destruct (lowbitS_cases' b) as [u j].
        replace (((u*2+1)*2^j-1)*2+1) with ((u*2+1)*2^(j+1)-1) in * by arith.
        exists (cfg2 (len+1+a*3+2) ((k*2+1)*2^(a*3+2)-3) j (2^(j+1)-1) u).
        split; [apply T3_Even1; lia|cbn [P]; arith].
    + exists (cfgR (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) m).
      split; [apply T3_Odd; lia|cbn [P]; arith].
  - divmod2_cases h; rename n' into a.
    + exists (cfg2 (len+1+(a*3+4)+2) ((k*2+1)*2^(a*3+4+2)-3) 0 1 (2^(a*3+1)-2)).
      split; [apply Double_Even; lia|cbn [P]; arith].
    + exists (cfgR (len+1+(a*3+4)+3) ((k*2+1)*2^(a*3+4+3)-7) (2^(a*3+2))).
      split; [apply Double_Odd; lia|cbn [P]; arith].
Qed.
Theorem nonhalt_from len k m:
  c0 -->* to_config (cfgL len k m) -> P (cfgL len k m) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_TM212.

(* SOC23_TM212.TM212 *)
Module TM212.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC23_TM212.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0RD_1RD0LC_1LE---_1RF1LE_1LB1RA").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{E}} [1;1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;0;1;1] {{B}}> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> d^^n *> [0] *> r -->+ l <| z^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n:
  ldh <* ld1^^(n+1) <| z *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0 |> [0;0] *> r.
Proof. es. Qed.
Lemma LOv_1 r n:
  ldh <* ld1^^(n+1) <| d *> r -->+
  ldh <* ld0^^n <* ld1 <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma ROv2 l r n:
  l |> d^^n *> [1;0;1;0;0] *> r -->+ l <| z^^n *> [0;0;1;1;0] *> r.
Proof. es. Qed.
Lemma ROv3_odd l r a:
  l |> d^^(a*2+1) *> [1;0;1;1;0] *> r -->+
  l <* ld0 <* ld1^^(a*3+3) |> r.
Proof. es. Qed.
Lemma ROv3_even0 l r a:
  l |> d^^(a*2) *> [1;0;1;1;0] *> z *> r -->+
  l <* ld1 <* ld0^^(a*3) <* ld1 <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma ROv3_even_head l r a:
  l |> d^^(a*2) *> [1;0;1;1;0] *> r -->+
  l <* ld0 <* ld1^^(a*3+1) <* <[1] |> r.
Proof. es. Qed.
Lemma Half_zero l r n:
  l <* ld0 <* ld1^^(n+1) <* <[1] <| z *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0 |> [0;0] *> r.
Proof. es. Qed.
Lemma Half_one l r n:
  l <* ld0 <* ld1^^(n+1) <* <[1] <| d *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma ROv3_even1 l r a b:
  l |> d^^(a*2) *> [1;0;1;1;0] *> d^^(b+1) *> z *> r -->+
  l <* ld1 <* ld0^^(a*3) <* ld1 <* ld0 |> z^^b *> [0;0;1;0;0] *> r.
Proof.
  follow10 ROv3_even_head; follow100 RInc.
  rewrite (Nat.add_comm b 1),(lpow_add sym 1 b z); cbn [lpow List.app Str_app].
  follow100 Half_zero.
  repeat (simpl_rotate || simpl_tape); finish.
Qed.
Lemma Corner_prefix r n h:
  ldh <* ld1^^(3+n) <| [0] *> [0;0;1]^^(2+h) *> [0;1;1;0] *> r -->+
  ldh <* ld0^^(1+n) <* ld1 <* ld0 <* ld1 |>
  [1;0;1;1;0] *> d^^h *> [1;0;1;1;0] *> r.
Proof. es' n h & r. Qed.
Lemma init: c0 -[tm]->* (BinDec ld0 ld1 12 2571 ldh <| BinInc d 23).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=E) (QR:=B) (wl:=[1;1;1;0]) (wr:=[1;1;0;1])
    (len:=12) (k:=2571) (m:=23).
  all: try solve[eauto using LInc,RInc,LOv_0,LOv_1,ROv2,ROv3_odd,
    ROv3_even0,ROv3_even_head,Half_zero,Half_one,ROv3_even1,Corner_prefix,init].
  cbn [Counter.P]; lia.
Qed.
End TM212.

(* SOC23_TM212.TM221 *)
Module TM221.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC23_TM212.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC0LB_1RD0RF_1RA1RE_1LF0RD_---1LB").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;0;1] {{A}}> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> d^^n *> [0] *> r -->+ l <| z^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n:
  ldh <* ld1^^(n+1) <| z *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0 |> [0;0] *> r.
Proof. es. Qed.
Lemma LOv_1 r n:
  ldh <* ld1^^(n+1) <| d *> r -->+
  ldh <* ld0^^n <* ld1 <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma ROv2 l r n:
  l |> d^^n *> [1;0;1;0;0] *> r -->+ l <| z^^n *> [0;0;1;1;0] *> r.
Proof. es. Qed.
Lemma ROv3_odd l r a:
  l |> d^^(a*2+1) *> [1;0;1;1;0] *> r -->+
  l <* ld0 <* ld1^^(a*3+3) |> r.
Proof. es. Qed.
Lemma ROv3_even0 l r a:
  l |> d^^(a*2) *> [1;0;1;1;0] *> z *> r -->+
  l <* ld1 <* ld0^^(a*3) <* ld1 <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma ROv3_even_head l r a:
  l |> d^^(a*2) *> [1;0;1;1;0] *> r -->+
  l <* ld0 <* ld1^^(a*3+1) <* <[1] |> r.
Proof. es. Qed.
Lemma Half_zero l r n:
  l <* ld0 <* ld1^^(n+1) <* <[1] <| z *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0 |> [0;0] *> r.
Proof. es. Qed.
Lemma Half_one l r n:
  l <* ld0 <* ld1^^(n+1) <* <[1] <| d *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma ROv3_even1 l r a b:
  l |> d^^(a*2) *> [1;0;1;1;0] *> d^^(b+1) *> z *> r -->+
  l <* ld1 <* ld0^^(a*3) <* ld1 <* ld0 |> z^^b *> [0;0;1;0;0] *> r.
Proof.
  follow10 ROv3_even_head; follow100 RInc.
  rewrite (Nat.add_comm b 1),(lpow_add sym 1 b z); cbn [lpow List.app Str_app].
  follow100 Half_zero.
  repeat (simpl_rotate || simpl_tape); finish.
Qed.
Lemma Corner_prefix r n h:
  ldh <* ld1^^(3+n) <| [0] *> [0;0;1]^^(2+h) *> [0;1;1;0] *> r -->+
  ldh <* ld0^^(1+n) <* ld1 <* ld0 <* ld1 |>
  [1;0;1;1;0] *> d^^h *> [1;0;1;1;0] *> r.
Proof. es' n h & r. Qed.
Lemma init: c0 -[tm]->* (BinDec ld0 ld1 12 2571 ldh <| BinInc d 23).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (wl:=[1;1;0]) (wr:=[1;0;1])
    (len:=12) (k:=2571) (m:=23).
  all: try solve[eauto using LInc,RInc,LOv_0,LOv_1,ROv2,ROv3_odd,
    ROv3_even0,ROv3_even_head,Half_zero,Half_one,ROv3_even1,Corner_prefix,init].
  cbn [Counter.P]; lia.
Qed.
End TM221.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM214.TM214 *)
Module TM214.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0RD_1RE1RA_---1LA_1LF1RB_1LD0LF").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{B}} [1;1;1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;0;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n:
  ldh <* ld1^^n <| rd0 *> r -->+ ldh <* ld0^^(n+1) |> [1;0] *> r.
Proof. es. Qed.
Lemma LOv_1 r n m:
  ldh <* ld1^^n <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^(n+1) <* ld1 |> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_0_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*3+1) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv2_0_1 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*3+1) <* ld1 |> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*3+2) |> r.
Proof. es. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC2 len n m := BinDec2 [0;0] [1;0] [0] len n (rd1 *> BinInc rd1 m).
Ltac follow_rule H := intros; epose proof H as HX; cbn[Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC,RC2;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.

Lemma LC_Inc len n r: 1+n<2^len ->
  LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) ->
  l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov_0 len n i:
  LC len 0 <| RC ((n*2+1)*2^i*2) -->+
  LC (len+1) (2^(len+1)-1) |> RC2 i ((2^i-1)*2) n.
Proof. solve_rule LOv_0. Qed.
Lemma LC_Ov_0_blank len:
  LC len 0 <| RC 0 -->+ LC (len+1) (2^(len+1)-1) |> RC 1.
Proof. epose proof (LOv_0 0inf len) as H; solve_rule H. Qed.
Lemma LC_Ov_1 len n i:
  LC len 0 <| RC (((n*2+1)*2^i-1)*2+1) -->+
  LC (len+1+1) ((2^(len+1)-1)*2) |> RC ((n*2+1)*2^i).
Proof. solve_rule LOv_1. Qed.

Lemma RC2_Ov_0_0 len a k i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((m*2+1)*2^i*2) -->+
  LC (len+1+1+(a*3+1)) (((k*2+1)*2+1)*2^(a*3+1)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv2_0_0. Qed.
Lemma RC2_Ov_0_0_blank len a k: k<2^len ->
  LC len k |> RC2 (a*2) 0 0 -->+
  LC (len+1+1+(a*3+1)) (((k*2+1)*2+1)*2^(a*3+1)-1) |> RC 1.
Proof. epose proof (ROv2_0_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC2_Ov_0_1 len a k i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (((m*2+1)*2^i-1)*2+1) -->+
  LC (len+1+1+(a*3+1)+1) ((((k*2+1)*2+1)*2^(a*3+1)-1)*2) |> RC ((m*2+1)*2^i).
Proof. solve_rule ROv2_0_1. Qed.
Lemma RC2_Ov_1 len a k m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 m -->+
  LC (len+1+1+(a*3+2)) (((k*2+1)*2+1)*2^(a*3+2)-1) |> RC m.
Proof. solve_rule ROv2_1. Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => k+n<2^len*2 /\ k<2^len
| cfgR len k n => k+n+1<2^len*2 /\ k<2^len
| cfgR2 len k h n m => n+m<=k<2^len /\ n<2^(h+1)
end.

Lemma append_bounds len k s: k<2^len ->
  k<=((k*2+1)*2+1)*2^s-1<2^(len+1+1+s) /\
  (((k*2+1)*2+1)*2^s-1)+k+2<2^(len+1+1+s)*2 /\
  (((k*2+1)*2+1)*2^s-1)*2+k+2<2^(len+1+1+s+1)*2.
Proof. intros; repeat rewrite Nat.pow_add_r; cbn [Nat.pow];
  pose proof (Nat.pow_nonzero 2 s); nia. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m]; cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + divmod2_cases m.
      * lowbit_cases n'.
        -- eexists (cfgR _ _ _); split; [apply LC_Ov_0_blank|].
           cbn [P]; rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
        -- eexists (cfgR2 _ _ _ _ _); split; [apply LC_Ov_0|].
           cbn [P]; pose proof (split_bound_v2 x i).
           repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
      * lowbitS_cases n'.
        eexists (cfgR _ _ _); split; [apply LC_Ov_1|].
        cbn [P]; repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + divmod2_cases m.
      * lowbit_cases n'0.
        -- eexists (cfgR _ _ _); split; [apply RC2_Ov_0_0_blank; lia|].
           cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)); lia.
        -- eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_0_0; lia|].
           cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)).
           pose proof (split_bound_v2 x i); rewrite (Nat.pow_add_r 2 i 1); cbn [Nat.pow]; lia.
      * lowbitS_cases n'0.
        eexists (cfgR _ _ _); split; [apply RC2_Ov_0_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)).
        rewrite (Nat.pow_add_r 2 (len+1+1+(n'*3+1)) 1); cbn [Nat.pow]; lia.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
Qed.

Lemma init: c0 -->* to_config (cfgL 4 13 2).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM214.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM223.TM223 *)
Module TM223.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LE_1RA1LC_0RC0RA_0LF0LC_---0LB").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* ld0 {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma R11 l r: l |> [1;1] *> r -->+ l <* ld0 |> r.
Proof. es. Qed.
Lemma R_d l r n m:
  l <* ld1 |> rd1^^(1+n) *> [1;0;1;0;0] *> rd1^^m *> [0] *> r -->+
  l <| [0;0;1;0;0;0;0;1] *> [0;0;1]^^n *> [0;0] *> rd0^^m *> [1] *> r.
Proof. es' n m & l r. Qed.
Lemma Shrink_step l r:
  l <* ld0 <* ld1 <| [0;0;1;0;0;0;0;1] *> r -->+
  l <* ld1 <| [0;0;1;0;0;0;0;1] *> [0;1] *> r.
Proof. es. Qed.
Lemma Shrink l r n:
  l <* ld0^^n <* ld1 <| [0;0;1;0;0;0;0;1] *> r -->*
  l <* ld1 <| [0;0;1;0;0;0;0;1] *> [0;1]^^n *> r.
Proof. revert r; induction n; intros; st; [finish|].
  follow100 Shrink_step; follow IHn; finish; simpl_rotate; reflexivity.
Qed.
Lemma Edge r n m:
  ldh <* ld1 <| [0;0;1;0;0;0;0;1] *> [0;1]^^n *> [0;0] *> rd1^^m *> [0] *> r -->+
  ldh <* ld1^^2 <* ld0 <* ld1 <* ld0^^n |> rd1 *> rd0 *> rd0^^m *> [1] *> r.
Proof. es. Qed.
Lemma Stage3 l r n:
  l <* ld0^^4 <* ld1^^2 <| [0;0;1;0;0;0;0;1;0;0;1;0;0] *> rd1^^n *> [0] *> r -->+
  l <* ld1^^2 <* ld0 <* ld1 <* ld0 <* ld1 <* ld0^^2 |> rd1 *> rd0^^2 *> rd0^^n *> [1] *> r.
Proof. es' n & l r. Qed.
Lemma Stage4 l r n:
  l <* ld0^^5 <* ld1^^3 <| [0;0;1;0;0;0;0;1] *> [0;0;1]^^2 *> [0;0] *> rd1^^n *> [0] *> r -->+
  l <* ld0^^2 <* ld1 <* ld0 <* ld1 <* ld0^^2 <* ld1 <* ld0^^2 |> rd1 *> rd0^^3 *> rd0^^n *> [1] *> r.
Proof. es' n & l r. Qed.
Lemma Stage5 l r n:
  l <* ld0^^4 <* ld1^^4 <| [0;0;1;0;0;0;0;1] *> [0;0;1]^^3 *> [0;0] *> rd1^^n *> [0] *> r -->+
  l <* ld0^^2 <* ld1^^2 <* ld0^^3 <* ld1 <* ld0^^2 |> rd1 *> rd0^^4 *> rd0^^n *> [1] *> r.
Proof. es' n & l r. Qed.
Lemma Stage6 l r n:
  l <* ld0^^3 <* ld1^^5 <| [0;0;1;0;0;0;0;1] *> [0;0;1]^^4 *> [0;0] *> rd1^^n *> [0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^5 <* ld1 <* ld0^^2 |> rd1 *> rd0^^5 *> rd0^^n *> [1] *> r.
Proof. es' n & l r. Qed.
Lemma Stage_ge7 l r n m:
  l <* ld0 <* ld1^^(6+n) <| [0;0;1;0;0;0;0;1] *> [0;0;1]^^(5+n) *> [0;0] *> rd1^^m *> [0] *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0^^4 <* ld1 <* ld0^^2 |> rd1 *> rd0^^(6+n) *> rd0^^m *> [1] *> r.
Proof. es' n m & l r. Qed.
Lemma init_tape: c0 -->* ldh <* ld1^^14 <|
  rd1 *> rd0^^2 *> rd1 *> rd0^^4 *> rd1 *> rd0^^5 *> rd1 *> 0inf.
Proof. esx. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition MC h n u := BinDec2 [0] [1] [0;0] h n ([0] *> rd1 *> RC u).
Definition W h u := [0;0;1;0;0;0;0;1] *> [0;0;1]^^h *> [0;0] *> RC u.

Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac farith := first [solve[arith] | progress f_equal; farith].
Ltac rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; rule LInc. Qed.
Lemma RC_Inc l n: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; rule RInc. Qed.
Lemma MC_Inc l h n u: 1+n<2^(h+1) -> l |> MC h (1+n) u -->+ l <| MC h n u.
Proof. intros; apply RBinDec2_spec; try lia; rule RInc. Qed.

Lemma RC_calls len k n: k<2^len ->
  LC len k |> RC n -->+ LC len 0 <| RC (k+n+1).
Proof.
  revert n; induction k; intros.
  - applys_eq RC_Inc; flia.
  - follow10 RC_Inc.
    follow_inc LC_Inc.
    eapply progress_evstep. applys_eq IHk; flia.
Qed.
Lemma MC_calls len k h n u c: k+c<2^len -> n+c<2^(h+1) ->
  LC len (k+c) |> MC h (n+c) u -->* LC len k |> MC h n u.
Proof.
  induction c; intros; [applys_eq evstep_refl; flia|].
  replace (k+S c) with (1+(k+c)) by lia.
  replace (n+S c) with (1+(n+c)) by lia.
  follow_inc MC_Inc; follow_inc LC_Inc.
  apply IHc; lia.
Qed.
Lemma RC_lift (f g: side -> Q*tape) u:
  (forall r n, f (rd1^^n *> [0] *> r) -->+ g (rd0^^n *> [1] *> r)) ->
  f (RC u) -->+ g (RC (1+u)).
Proof.
  intros H; lowbitS_cases u; unfold RC.
  rewrite BinInc_mulpow2sub1.
  replace (1+((x*2+1)*2^i-1)) with ((x*2+1)*2^i) by
    (pose proof (Nat.pow_nonzero 2 i); nia).
  rewrite BinInc_mulpow2, BinInc_mul2add1.
  apply (H ([0;0] *> BinInc rd1 x) i).
Qed.
Lemma Start len h u:
  LC len 0 <| RC (((u*2+1)*2^(h+1))*2+1) -->+
  LC (len+1) (2^(len+1)-1) |> MC (h+1) (2^(h+1+1)-1) u.
Proof.
  unfold LC,RC,MC; rw_Bin.
  follow10 LOv; follow100 R11; st; finish; simpl_rotate; reflexivity.
Qed.
Ltac lift_RC u H :=
  cbn [Nat.add];
  lazymatch goal with |- ?s -->+ ?t =>
    let up:=eval cbn [Nat.add] in (1+u) in
    let sf:=eval pattern (RC u) in s in
    let tf:=eval pattern (RC up) in t in
    lazymatch sf with ?f _ => lazymatch tf with ?g _ =>
      let rr:=fresh "rr" in let nn:=fresh "nn" in
      apply (RC_lift f g u); intros rr nn;
      applys_eq (H rr nn); simpl_rotate; reflexivity
    end end
  end.
Lemma R_d_RC l h u:
  l <* ld1 |> rd1^^(1+h) *> [1;0;1;0;0] *> RC u -->+ l <| W h (1+u).
Proof.
  apply (RC_lift (fun r=>l <* ld1 |> rd1^^(1+h) *> [1;0;1;0;0] *> r)
    (fun r=>l <| [0;0;1;0;0;0;0;1] *> [0;0;1]^^h *> [0;0] *> r) u).
  intros; apply R_d.
Qed.
Lemma Pre p h u:
  LC (p+1+(h+1)) 0 <| RC (((u*2+1)*2^(h+1))*2+1) -->+
  ldh <* ld0^^(p+1) <* ld1^^(h+1) <| W h (1+u).
Proof.
  follow10 Start.
  eapply evstep_trans with (c':=LC ((p+1)+(h+2)) ((2^(p+1)-1)*2^(h+2)) |> MC (h+1) 0 u).
  - replace (p+1+(h+1)+1) with (p+1+(h+2)) by lia.
    replace (h+1+1) with (h+2) by lia.
    replace (2^(p+1+(h+2))-1) with
      ((2^(p+1)-1)*2^(h+2)+(2^(h+2)-1)) by arith.
    apply (MC_calls _ _ _ 0 u _); arith.
  - unfold LC,MC; rw_Bin; try solve[arith].
    replace (h+2) with (1+(h+1)) by lia; cbn [lpow].
    apply progress_evstep; applys_eq R_d_RC; flia.
Qed.
Lemma RC_prefix h u: rd1 *> rd0^^h *> RC u = RC ((u*2^h)*2+1).
Proof. unfold RC; rewrite BinInc_mul2add1, BinInc_mulpow2; reflexivity. Qed.
Lemma Edge_RC n u:
  ldh <* ld1 <| [0;0;1;0;0;0;0;1] *> [0;1]^^n *> [0;0] *> RC u -->+
  ldh <* ld1^^2 <* ld0 <* ld1 <* ld0^^n |> rd1 *> rd0 *> RC (1+u).
Proof.
  lift_RC u (fun r m=>Edge r n m).
Qed.
Lemma LC_edge n:
  LC (3+1+n) ((1*2+1)*2^n-1) = ldh <* ld1^^2 <* ld0 <* ld1 <* ld0^^n.
Proof.
  unfold LC; rewrite BinDec_mulpow2sub1 by solve_pow2_lt.
  unfold BinDec; reflexivity.
Qed.
Import BinDigits.
Lemma LC_full_suffix a (ds:list BinDigit):
  LC (a+List.length ds) ((2^a-1)*2^List.length ds+val0 ds) =
  ldh <* ld0^^a <* List.flat_map (mp ld0 ld1) ds.
Proof. unfold LC; rewrite BinDigits.BinDec_app by solve_pow2_lt;
  rewrite BinDec_full; reflexivity. Qed.
Ltac pack_full a ds :=
  let E:=fresh "Ebits" in pose proof (LC_full_suffix a ds) as E;
  cbn [List.length val0 Nat.mul Nat.add] in E; rewrite E; clear E.
Lemma LC_ge7 p h:
  LC (p+1+h+8) ((((2^p-1)*2+1)*2^h-1)*2^8+123) =
  ldh <* ld0^^p <* ld1 <* ld0^^h <* ld1 <* ld0^^4 <* ld1 <* ld0^^2.
Proof.
  unfold LC; pose proof (BinDigits.BinDec_app ld0 ld1 (p+1+h)
    (((2^p-1)*2+1)*2^h-1) ldh [D0;D0;D1;D0;D0;D0;D0;D1] ltac:(solve_pow2_lt)) as E.
  cbn [List.length val0 Nat.mul Nat.add] in E; rewrite E.
  rewrite BinDec_mulpow2sub1 by solve_pow2_lt; rewrite BinDec_full.
  st; reflexivity.
Qed.
Lemma Edge_num n u:
  ldh <* ld1 <| [0;0;1;0;0;0;0;1] *> [0;1]^^n *> [0;0] *> RC u -->+
  LC (3+1+n) ((1*2+1)*2^n-1) |> RC (((1+u)*2^1)*2+1).
Proof. rewrite LC_edge, <-RC_prefix; apply Edge_RC. Qed.
Lemma Stage3_num a u:
  ldh <* ld0^^(a+6) <* ld1^^2 <| W 1 u -->+
  LC (a+2+8) ((2^(a+2)-1)*2^8+43) |> RC (((1+u)*2^2)*2+1).
Proof.
  pack_full (a+2) [D0;D0;D1;D0;D1;D0;D1;D1]; rewrite <-RC_prefix.
  unfold W; replace (a+6) with (4+(a+2)) by lia;
  lift_RC u (Stage3 (ldh <* ld0^^(a+2))).
Qed.
Lemma Stage4_num a u:
  ldh <* ld0^^(a+5) <* ld1^^3 <| W 2 u -->+
  LC (a+10) ((2^a-1)*2^10+859) |> RC (((1+u)*2^3)*2+1).
Proof.
  pack_full a [D0;D0;D1;D0;D0;D1;D0;D1;D0;D0]; rewrite <-RC_prefix.
  unfold W; replace (a+5) with (5+a) by lia; lift_RC u (Stage4 (ldh <* ld0^^a)).
Qed.
Lemma Stage5_num a u:
  ldh <* ld0^^(a+4) <* ld1^^4 <| W 3 u -->+
  LC (a+10) ((2^a-1)*2^10+827) |> RC (((1+u)*2^4)*2+1).
Proof.
  pack_full a [D0;D0;D1;D0;D0;D0;D1;D1;D0;D0]; rewrite <-RC_prefix.
  unfold W; replace (a+4) with (4+a) by lia; lift_RC u (Stage5 (ldh <* ld0^^a)).
Qed.
Lemma Stage6_num a u:
  ldh <* ld0^^(a+3) <* ld1^^5 <| W 4 u -->+
  LC (a+10) ((2^a-1)*2^10+763) |> RC (((1+u)*2^5)*2+1).
Proof.
  pack_full a [D0;D0;D1;D0;D0;D0;D0;D0;D1;D0]; rewrite <-RC_prefix.
  unfold W; replace (a+3) with (3+a) by lia; lift_RC u (Stage6 (ldh <* ld0^^a)).
Qed.
Lemma Stage_ge7_num p h u:
  ldh <* ld0^^(p+1) <* ld1^^(6+h) <| W (5+h) u -->+
  LC (p+1+h+8) ((((2^p-1)*2+1)*2^h-1)*2^8+123) |> RC (((1+u)*2^(6+h))*2+1).
Proof. rewrite LC_ge7, <-RC_prefix; unfold W; replace (p+1) with (1+p) by lia;
  lift_RC u (fun r m=>Stage_ge7 (ldh <* ld0^^p) r h m). Qed.
Ltac consume := eapply evstep_trans;
  [apply progress_evstep; apply RC_calls; first[solve[solve_pow2_lt]|arith]|]; finish; farith.
Lemma Next2 a u:
  LC (a+8) 0 <| RC ((u*2+1)*4+1) -->+
  LC (a+11) 0 <| RC ((3*2^(a+5)+u+2)*4+1).
Proof.
  eapply progress_evstep_trans; [applys_eq (Pre (a+6) 0 u); farith|].
  unfold W; cbn [lpow]; follow Shrink; follow100 Edge_num; consume.
Qed.
Lemma Next3 a u:
  LC (a+8) 0 <| RC ((u*2+1)*8+1) -->+
  LC (a+10) 0 <| RC ((2^(a+8)+u*2-49)*4+1).
Proof.
  eapply progress_evstep_trans; [applys_eq (Pre (a+5) 1 u); farith|].
  eapply evstep_trans; [apply progress_evstep; applys_eq (Stage3_num a (1+u)); farith|].
  consume.
Qed.
Ltac round p h u H :=
  eapply progress_evstep_trans; [applys_eq (Pre p h u); farith|];
  eapply evstep_trans; [apply progress_evstep; applys_eq H; farith|]; consume.
Lemma Next4 a u:
  LC (a+8) 0 <| RC ((u*2+1)*16+1) -->+
  LC (a+10) 0 <| RC ((2^(a+8)+u*4-33)*4+1).
Proof. round (a+4) 2 u (Stage4_num a (1+u)). Qed.
Lemma Next5 a u:
  LC (a+8) 0 <| RC ((u*2+1)*32+1) -->+
  LC (a+10) 0 <| RC ((2^(a+8)+u*8-33)*4+1).
Proof. round (a+3) 3 u (Stage5_num a (1+u)). Qed.
Lemma Next6 a u:
  LC (a+8) 0 <| RC ((u*2+1)*64+1) -->+
  LC (a+10) 0 <| RC ((2^(a+8)+u*16-33)*4+1).
Proof. round (a+2) 4 u (Stage6_num a (1+u)). Qed.
Lemma Next_ge7 p h u:
  LC (p+7+h) 0 <| RC ((u*2+1)*2^(7+h)+1) -->+
  LC (p+9+h) 0 <| RC ((2^(p+7+h)+u*2^(h+5)-33)*4+1).
Proof. round p (5+h) u (Stage_ge7_num p h (1+u)). Qed.

Definition to_config (x:nat*nat) := let '(a,n):=x in LC (a+8) 0 <| RC (n*4+1).
Definition P (x:nat*nat) := let '(a,n):=x in 0<n /\ n*4+1<2^(a+9).
Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [a n]; cbn [P to_config]; intros HP.
  lowbit_cases n; [lia|].
  destruct i as [|[|[|[|[|h]]]]].
  - exists (a+3, 3*2^(a+5)+x+2); split.
    + cbn [to_config]; applys_eq (Next2 a x); farith.
    + cbn [P]; arith.
  - exists (a+2, 2^(a+8)+x*2-49); split.
    + cbn [to_config]; applys_eq (Next3 a x); farith.
    + cbn [P]; arith.
  - exists (a+2, 2^(a+8)+x*4-33); split.
    + cbn [to_config]; applys_eq (Next4 a x); farith.
    + cbn [P]; arith.
  - exists (a+2, 2^(a+8)+x*8-33); split.
    + cbn [to_config]; applys_eq (Next5 a x); farith.
    + cbn [P]; arith.
  - exists (a+2, 2^(a+8)+x*16-33); split.
    + cbn [to_config]; applys_eq (Next6 a x); farith.
    + cbn [P]; arith.
  - assert (HB: h+7<a+9) by (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
    exists (a+2, 2^(a+8)+x*2^(h+5)-33); split.
    + cbn [to_config]; applys_eq (Next_ge7 (a+1-h) h x); farith.
    + cbn [P]; arith.
Qed.
Lemma initial_right:
  RC ((2^12+2^6+2)*4+1) =
  rd1 *> rd0^^2 *> rd1 *> rd0^^4 *> rd1 *> rd0^^5 *> rd1 *> 0inf.
Proof.
  replace ((2^12+2^6+2)*4+1) with ((((((1*2^5)*2+1)*2^4)*2+1)*2^2)*2+1) by lia.
  repeat rewrite <-RC_prefix.
  unfold RC; rewrite BinInc_1; reflexivity.
Qed.
Lemma initial: c0 -->* to_config (6,2^12+2^6+2).
Proof.
  cbn [to_config]; unfold LC; rewrite BinDec_O,initial_right; apply init_tape.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply initial|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|].
  cbn [P]; lia.
Qed.
End TM223.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM226.TM226 *)
Module TM226.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1LF_---1LD_1LE0LD_1RA0RC_1RE0RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{E}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0;0] *> r -->+ l <| rd0^^n *> [1;0] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma Odd l r n:
  l |> rd1^^(n*2+1) *> [0;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+1) |> [1] *> r.
Proof. es' n & l r. Qed.
Lemma Even l r n m:
  l |> rd1^^(n*2+2) *> [0;1;0;0] *> rd1^^m *> [0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <| [1;0;0;0] *> rd0^^m *> [1;0] *> r.
Proof. es' n m & l r. Qed.
Lemma EvenR l r n m:
  l |> rd1^^(n*2+2) *> [0;1;0;0] *> rd1^^m *> [0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [1;0;0;0] *> rd0^^m *> [1;0] *> r.
Proof. follow10 Even; follow100 LInc; finish. Qed.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC n := BinInc rd1 n.
Definition MC h n m := BinDec rd0 rd1 h n ([0] *> rd1 *> RC m).
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,MC,RC; rw_Bin;
  try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.

Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc l n: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma MC_Inc l h n m: 1+n<2^h -> l |> MC h (1+n) m -->+ l <| MC h n m.
Proof. intros; apply RBinDec_spec; try lia; follow_rule RInc. Qed.
Lemma LC_Ov len m h:
  LC len 0 <| RC (((m*2+1)*2^h)*2) -->+
  LC len (2^len-1) |> MC (h+1) ((2^h-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma MC_Odd len k a m: k<2^len ->
  LC len k |> MC (a*2+1) 0 m -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) |> RC (m*2+1).
Proof. solve_rule Odd. Qed.
Lemma MC_Even len k a m i: k<2^len ->
  LC len k |> MC (a*2+2) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> MC (i+1) ((2^i-1)*2) m.
Proof. solve_rule EvenR. Qed.

Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgM (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgM len k h n m => LC len k |> MC h n m
end.
Close Scope sym.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 0<k+n<2^(len+1) /\ (k+n) mod 2=0
| cfgR len k n => 1<=len /\ k<2^len /\ 0<k+n+1<2^(len+1) /\ (k+n+1) mod 2=0
| cfgM len k h n m => 1<=len /\ 1<=h /\ n+m<=k<2^len /\ n<2^h
end.
Open Scope sym.
Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m]; cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + divmod2_cases m; [|lia].
      lowbit_cases n'; [lia|].
      exists (cfgM len (2^len-1) (i+1) ((2^i-1)*2) x); split.
      * apply LC_Ov.
      * cbn [P]; pose proof (split_bound_v1 x i len ltac:(arith)); arith.
    + exists (cfgR len k m); split; [apply LC_Inc; lia|cbn [P]; lia].
  - exists (cfgL len k (1+m)); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    + divmod2_cases h.
      * destruct n' as [|a]; [lia|]; lowbitS_cases m.
        exists (cfgM (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1)
          (i+1) ((2^i-1)*2) x); split.
        -- applys_eq (MC_Even len k a x i); flia.
        -- cbn [P]; arith.
      * exists (cfgR (len+1+(n'*3+1)) ((k*2+1)*2^(n'*3+1)) (m*2+1)); split.
        -- apply MC_Odd; lia.
        -- cbn [P]; arith.
    + destruct k as [|k]; [lia|].
      exists (cfgM len k h n m); split.
      * eapply progress_evstep_trans; [apply MC_Inc; lia|].
        apply progress_evstep, LC_Inc; lia.
      * cbn [P]; lia.
Qed.
Lemma init: c0 -->* to_config (cfgL 3 4 4).
Proof. unfold to_config,LC,RC; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM226.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import String Lia ZifyNat PeanoNat.

(* SOC23_TM46.TM46 *)
Module TM46.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import String Lia ZifyNat PeanoNat.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LB_1RD1LC_0RF1RE_1RC0RD_0LA1RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0;0] *> r -->+ l <| rd0^^n *> [1;0] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma R11 l r: l |> [1;1] *> r -->+ l <* ld0 |> r.
Proof. es. Qed.
Lemma R110_odd l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <| [0] *> r.
Proof. es' n & l r. Qed.
Lemma R101_even l r n:
  l |> rd1^^(n*2) *> [1;0;1] *> r -->+
  l <* ld0 <* ld1^^(n*3) <| [1] *> r.
Proof. es' n & l r. Qed.
Lemma R101_odd l r n:
  l |> rd1^^(n*2+1) *> [1;0;1] *> r -->+
  l <* ld0 <* ld1^^(n*3+2) <| r.
Proof. es' n & l r. Qed.
Lemma R010 l r: l |> [0;1;0] *> r -->+ l <* ld1 <| [1] *> r.
Proof. es. Qed.

Lemma R11_evenR l r n:
  l |> rd1^^(n*2+2) *> [1;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+3) |> [0;0] *> r.
Proof. es' n & l r. Qed.
Lemma R110_oddR l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. follow10 R110_odd; follow100 LInc; finish. Qed.
Lemma R010_oddR l r n:
  l |> rd1^^(n*2+1) *> [0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) <* ld1 <* ld0 |> [1] *> r.
Proof. es' n & l r. Qed.
Lemma R010_evenR l r n:
  l |> rd1^^(n*2+2) *> [0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) <* ld1 |> [1;0] *> r.
Proof. es' n & l r. Qed.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC n := BinInc rd1 n.
Definition MC (b:bool) h n m :=
  BinDec rd0 rd1 h n ((if b then [1;1;0;0] else [0;1;0;0]) *> RC m).
Definition MB h n m := BinDec2 [0;0] [1;0] [0] h n (rd1 *> RC m).
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish; try flia.
Ltac solve_rule H := intros; unfold LC,MC,MB,RC; rw_Bin;
  try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.

Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc l n: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma MC_Inc l b h n m: 1+n<2^h -> l |> MC b h (1+n) m -->+ l <| MC b h n m.
Proof. intros; apply RBinDec_spec; try lia; follow_rule RInc. Qed.
Lemma MB_Inc l h n m: 1+n<2^(h+1) -> l |> MB h (1+n) m -->+ l <| MB h n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma LC_Ov len m:
  LC len 0 <| RC m -->+ LC len (2^len-1) |> [1] *> RC m.
Proof. solve_rule LOv. Qed.
Lemma A1_zero len k m: k<2^len ->
  LC len k |> MC true 0 0 m -->+ LC (len+1) (k*2+1) |> [0;0] *> RC m.
Proof. solve_rule R11. Qed.
Lemma A1_even len k a m: k<2^len ->
  LC len k |> MC true (a*2+2) 0 m -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) |> [0;0] *> RC m.
Proof. solve_rule R11_evenR. Qed.
Lemma A1_odd len k a m: k<2^len ->
  LC len k |> MC true (a*2+1) 0 m -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0] *> RC m.
Proof. solve_rule R110_oddR. Qed.
Lemma A0_zero len k m: k<2^len ->
  LC len k |> MC false 0 0 m -->+ LC (len+1) (k*2) <| [1;0] *> RC m.
Proof. solve_rule R010. Qed.
Lemma A0_odd len k a m: k<2^len ->
  LC len k |> MC false (a*2+1) 0 m -->+
  LC (len+1+a*3+1+1) ((((k*2+1)*2^(a*3)-1)*2)*2+1) |> [1] *> RC m.
Proof. solve_rule R010_oddR. Qed.
Lemma A0_even len k a m: k<2^len ->
  LC len k |> MC false (a*2+2) 0 m -->+
  LC (len+1+(a*3+2)+1) (((k*2+1)*2^(a*3+2)-1)*2) |> [1;0] *> RC m.
Proof. solve_rule R010_evenR. Qed.
Lemma B_even len k a m: k<2^len ->
  LC len k |> MB (a*2) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) <| RC (m*2+1).
Proof. solve_rule R101_even. Qed.
Lemma B_odd len k a m: k<2^len ->
  LC len k |> MB (a*2+1) 0 m -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0;0] *> RC m.
Proof.
  intros. unfold LC,MB; rw_Bin; try solve[solve_pow2_lt].
  follow10 R101_odd; follow100 LInc; repeat (simpl_rotate || simpl_tape); finish.
Qed.
Inductive P: (Q*tape)%type -> Prop :=
| PL len k m: 1<=len -> k<2^len -> 0<k+m<2^(len+1) ->
    P (LC len k <| RC m)
| PR len k m: 1<=len -> k<2^len -> 0<k+m+1<2^(len+1) ->
    P (LC len k |> RC m)
| PA len k b h n m: 1<=len -> n+m<=k<2^len -> n<2^h ->
    P (LC len k |> MC b h n m)
| PB len k h n m: 1<=len -> n+m<=k<2^len -> n<2^(h+1) ->
    P (LC len k |> MB h n m).
Ltac safe H := applys_eq H; try solve[arith]; unfold MC,MB,RC; rw_Bin;
  try solve[arith]; repeat (simpl_rotate || simpl_tape); reflexivity.

Lemma good_0 len k m: 1<=len -> k<2^len -> m<=k ->
  P (LC len k |> [0] *> RC m).
Proof.
  intros; lowbit_cases m.
  - safe (PR len k 0).
  - safe (PA len k false i (2^i-1) x).
Qed.
Lemma good_1 len k m: 1<=len -> k<2^len -> m<=k ->
  P (LC len k |> [1] *> RC m).
Proof.
  intros; assert (1<2^len) by (change (2^0<2^len); apply Nat.pow_lt_mono_r; lia).
  divmod2_cases m.
  - lowbit_cases n'.
    + safe (PR len k 1).
    + safe (PA len k false (i+1) ((2^i-1)*2) x).
  - safe (PA len k true 0 0 n').
Qed.
Lemma good_00 len k m: 1<=len -> k<2^len -> m*2<=k ->
  P (LC len k |> [0;0] *> RC m).
Proof.
  intros; lowbit_cases m.
  - safe (PR len k 0).
  - safe (PB len k i (2^(i+1)-1) x).
Qed.
Lemma good_10 len k m: 1<=len -> k<2^len -> m*2<=k+1 ->
  P (LC len k |> [1;0] *> RC m).
Proof.
  intros; assert (1<2^len) by (change (2^0<2^len); apply Nat.pow_lt_mono_r; lia).
  lowbit_cases m.
  - safe (PR len k 1).
  - safe (PB len k i ((2^i-1)*2) x).
Qed.
Lemma good_1_full len m: 1<=len -> 0<m<2^(len+1) ->
  P (LC len (2^len-1) |> [1] *> RC m).
Proof.
  intros; divmod2_cases m.
  - lowbit_cases n'; [lia|].
    pose proof (split_bound_v1 x i len ltac:(arith)).
    safe (PA len (2^len-1) false (i+1) ((2^i-1)*2) x).
  - safe (PA len (2^len-1) true 0 0 n').
Qed.

Lemma closed c: P c -> exists c', c -->+ c' /\ P c'.
Proof.
  intros HP; destruct HP as [len k m HL HK HM|len k m HL HK HM|
    len k b h n m HL HK HN|len k h n m HL HK HN].
  - destruct k as [|k].
    + eexists; split; [apply LC_Ov|apply good_1_full; lia].
    + eexists; split; [apply LC_Inc; lia|apply PR; lia].
  - eexists; split; [apply RC_Inc|apply PL; lia].
  - destruct n as [|n].
    + destruct b.
      * destruct h as [|h].
        -- eexists; split; [apply A1_zero; lia|apply good_00; arith].
        -- divmod2_cases h.
           ++ eexists; split; [applys_eq (A1_odd len k n' m); flia|apply good_0; arith].
           ++ eexists; split; [applys_eq (A1_even len k n' m); flia|apply good_00; arith].
      * destruct h as [|h].
        -- destruct m as [|m].
           ++ exists (LC (len+1) (k*2) <| RC 1); split.
              ** eapply progress_evstep_trans; [apply A0_zero; lia|].
                 unfold RC; rw_Bin; repeat (simpl_rotate || simpl_tape); finish.
              ** apply PL; arith.
           ++ exists (LC (len+1) (k*2-1) |> [1;0] *> RC (S m)); split.
              ** eapply progress_evstep_trans; [apply A0_zero; lia|].
                 apply progress_evstep; applys_eq (LC_Inc (len+1) (k*2-1)); flia; arith.
              ** apply good_10; arith.
        -- divmod2_cases h.
           ++ eexists; split; [applys_eq (A0_odd len k n' m); flia|apply good_1; arith].
           ++ eexists; split; [applys_eq (A0_even len k n' m); flia|apply good_10; arith].
    + destruct k as [|k]; [lia|].
      exists (LC len k |> MC b h n m); split.
      * eapply progress_evstep_trans; [apply MC_Inc; lia|].
        apply progress_evstep, LC_Inc; lia.
      * apply PA; lia.
  - destruct n as [|n].
    + divmod2_cases h.
      * eexists; split; [apply B_even; lia|apply PL; arith].
      * eexists; split; [apply B_odd; lia|apply good_00; arith].
    + destruct k as [|k]; [lia|].
      exists (LC len k |> MB h n m); split.
      * eapply progress_evstep_trans; [apply MB_Inc; lia|].
        apply progress_evstep, LC_Inc; lia.
      * apply PB; lia.
Qed.

Lemma init: c0 -->* LC 4 7 <| RC 4.
Proof. unfold LC,RC; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (C:=fun c=>c) (P:=P); [apply closed|apply PL; lia].
Qed.
End TM46.

From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2.
Require Import NArith Lia ZifyNat List String.

(* Shared definitions from SOC23_TM71Halt.v. *)
Module TM71.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LB_1LE1RD_1RC---_1RF0RA_1RA1LF").
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.Eqb BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia ZifyNat List String.

Module Core.
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* <[1;0;1;1;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} [1;1;1;0;0] *> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Definition addN p k := match k with N0=>p | Npos k=>Pos.add p k end.
Lemma addN_succ p k: addN p (N.succ k) = addN (Pos.succ p) k.
Proof. destruct k; cbn [addN N.succ]; lia. Qed.

Lemma paired k p q l r:
  (k<=rest p)%N -> (k<=rest q)%N ->
  BinaryCounter ld0 ld1 l p |> BinaryCounter rd0 rd1 r q -->*
  BinaryCounter ld0 ld1 l (addN p k) |> BinaryCounter rd0 rd1 r (addN q k).
Proof.
  revert p q; induction k using N.peano_ind; intros p q Hp Hq.
  - apply evstep_refl.
  - assert (Hp0: rest p<>0%N) by lia.
    assert (Hq0: rest q<>0%N) by lia.
    pose proof (rest_S p Hp0); pose proof (rest_S q Hq0).
    rewrite !addN_succ.
    eapply evstep_trans.
    + apply progress_evstep; apply BinaryCounter.RInc.
      * intros; change (rd0^^n *> rd1 *> r0) with (rd0^^n *> [1] *> [0;0] *> r0).
        apply RInc.
      * apply not_full_iff_rest; exact Hq0.
    + eapply evstep_trans.
      * apply progress_evstep; apply BinaryCounter.LInc; [apply LInc|].
        apply not_full_iff_rest; exact Hp0.
      * apply IHk; lia.
Qed.

(* Binary words have a leading sentinel in their positive representation;
   it is not a tape digit.  No unary large integer is computed. *)
Fixpoint word (d0 d1:list Sym) p := match p with
  | xH=>nil | xO p=>d0++word d0 d1 p | xI p=>d1++word d0 d1 p end.
Lemma word_spec d0 d1 p r:
  word d0 d1 p *> r = BinaryCounter d0 d1 r p.
Proof. induction p; cbn; rewrite ?Str_app_assoc, ?IHp; reflexivity. Qed.

(* This check permits omitted trailing blanks, but never treats a failed
   match as a halt.  Proposal parsers need no soundness assumptions. *)
Fixpoint peel (w s:list Sym) : option (list Sym) := match w with
  | nil=>Some s
  | b::w=>match s with
    | nil=>if sym_eqb b 0 then peel w nil else None
    | c::s=>if sym_eqb b c then peel w s else None end end.
Lemma peel_spec w s r: peel w s=Some r -> s *> 0inf = w *> r *> 0inf.
Proof.
  revert s; induction w as [|b w IH]; intros s H; cbn in H.
  - injection H as <-; reflexivity.
  - destruct s as [|c s].
    + destruct (sym_eqb_spec b 0); try discriminate; subst.
      specialize (IH _ H); cbn; rewrite <-IH; apply const_unfold.
    + destruct (sym_eqb_spec b c); try discriminate; subst.
      specialize (IH _ H); cbn; rewrite <-IH; reflexivity.
Qed.

Definition State := (Q * list Sym * list Sym)%type.
Definition denote (s:State) := let '(q,l,r):=s in l *> 0inf {{q}}> r *> 0inf.
Fixpoint room p : N := match p with
  | xH=>N0 | xI p=>N.double (room p) | xO p=>N.succ_double (room p) end.
Lemma room_spec p: room p=rest p.
Proof.
  induction p; cbn [room]; rewrite ?IHp.
  - unfold rest; cbn [log2 pow2']; pose proof (pow2'_log2_ge p).
    rewrite N.double_spec; lia.
  - rewrite N.succ_double_spec,rest_mul2; lia.
  - reflexivity.
Qed.

Fixpoint decode_left (l:list Sym) : positive * list Sym := match l with
  | S0::S1::l=>let '(p,r):=decode_left l in (xO p,r)
  | S1::S1::l=>let '(p,r):=decode_left l in (xI p,r)
  | _=>(xH,l) end.
Lemma decode_left_spec l p r: decode_left l=(p,r) ->
  l *> 0inf=BinaryCounter ld0 ld1 (r *> 0inf) p.
Proof.
  revert l p r; fix IH 1; intros [|[] [|[] l]] p r H;
    cbn [decode_left] in H; try (injection H as <- <-; reflexivity).
  all: destruct (decode_left l) as [p' r'] eqn:E; injection H as <- <-;
    cbn [BinaryCounter Str_app]; rewrite (IH _ _ _ E); reflexivity.
Qed.
Definition put b (v:positive * list Sym) :=
  let '(p,r):=v in (match b with S0=>xO p | S1=>xI p end,r).
Fixpoint decode_right n (r:list Sym) : positive * list Sym := match n with
  | O=>(xH,r)
  | S n=>match r with
    | b::S0::S0::r=>put b (decode_right n r)
    | nil=>put S0 (decode_right n nil)
    | b::nil | b::S0::nil=>put b (decode_right n nil)
    | _=>(xH,r) end end.
Lemma decode_right_spec n r p t: decode_right n r=(p,t) ->
  r *> 0inf=BinaryCounter rd0 rd1 (t *> 0inf) p.
Proof.
  revert r p t; induction n as [|n IHn]; intros r p t H.
  - injection H as <- <-; reflexivity.
  - destruct r as [|[] [|[] [|[] r]]]; cbn [decode_right] in H;
      try (injection H as <- <-; reflexivity).
    all: match type of H with context[decode_right ?n ?r] =>
      destruct (decode_right n r) as [p' t'] eqn:E;
      cbn [put] in H; injection H as <- <-;
      cbn [BinaryCounter Str_app]; rewrite <- (IHn _ _ _ E);
      repeat rewrite <-const_unfold; reflexivity end.
Qed.
Definition right_start (r:list Sym) := match r with
  | _::S1::_ | _::_::S1::_=>false | _=>true end.
Definition accelerate (s:State) := match s with
  | (A,S1::S1::S1::S0::S1::l,r)=>if right_start r then
    let '(p,l'):=decode_left l in
    match room p with
    | N0=>None
    | k=>let '(q,r'):=decode_right (S (log2 p)) r in
      match N.min k (room q) with
      | N0=>None
      | k=>Some (A,[1;1;1;0;1]++word ld0 ld1 (addN p k)++l',
                       word rd0 rd1 (addN q k)++r') end end else None
  | _=>None end.
Lemma accelerate_spec s t: accelerate s=Some t -> denote s -[tm]->* denote t.
Proof.
  unfold accelerate; destruct s as [[state l] r]; destruct state; try discriminate.
  do 5 (destruct l as [|[] l]; try discriminate).
  destruct (right_start r); try discriminate.
  destruct (decode_left l) as [p l'] eqn:Hl.
  destruct (room p) eqn:Hp; try discriminate.
  destruct (decode_right (S (log2 p)) r) as [q r'] eqn:Hr.
  destruct (N.min (N.pos p0) (room q)) eqn:Hk; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf |> r *> 0inf -[tm]->*
    (word ld0 ld1 (addN p (N.pos p1))++l') *> 0inf |>
    (word rd0 rd1 (addN q (N.pos p1))++r') *> 0inf).
  apply decode_left_spec in Hl; apply decode_right_spec in Hr.
  rewrite Hl,Hr,!Str_app_assoc,!word_spec.
  apply paired; rewrite <-!room_spec,<-Hk; [rewrite Hp; apply N.le_min_l|apply N.le_min_r].
Qed.


Definition make_left q (l r:list Sym) : State := match l with
  | nil=>(q,nil,S0::r) | b::l=>(q,l,b::r) end.
Lemma make_left_spec q l r:
  denote (make_left q l r)=l *> 0inf <{{q}} r *> 0inf.
Proof. destruct l; reflexivity. Qed.
Inductive Shift := Keep | Erase | Digits | Add | Bdd | DTwins | BTwins.
Definition shift_q tag := match tag with
  | Keep=>F | Erase=>B | Digits | DTwins=>A | Add=>C | Bdd | BTwins=>E end.
Definition shift_left tag n : list Sym := match tag with
  | Keep | Erase=>[1]^^n | _=>nil end.
Definition shift_right tag n : list Sym := match tag with
  | Keep | Erase=>[1] | Digits=>rd1^^(1+n)
  | Add | Bdd=>[1;0;0;1;0;0]^^(1+n)
  | DTwins | BTwins=>[1;1]^^(1+n) end.
Definition shift_target tag n (l r:list Sym) : State := match tag with
  | Keep=>make_left F l ([1]^^(1+n)++r)
  | Erase=>make_left B l ([0]^^(1+n)++r)
  | Digits=>(A,[1;1;1]^^(1+n)++l,r)
  | Add=>(C,<[1;0;1;0;1;1]^^(1+n)++l,r)
  | Bdd=>(E,<[0;1;1;1;0;1]^^(1+n)++l,r)
  | DTwins=>(A,[0;1]^^(1+n)++l,r)
  | BTwins=>(E,[1;0]^^(1+n)++l,r) end.
Lemma shift_rule tag n (l r:list Sym):
  denote (shift_q tag,shift_left tag n++l,shift_right tag n++r) -->*
  denote (shift_target tag n l r).
Proof.
  destruct tag; cbn [shift_q shift_left shift_right shift_target];
    rewrite ?make_left_spec; unfold denote; rewrite !Str_app_assoc;
    generalize (l *> 0inf), (r *> 0inf); intros l' r'; clear l r.
  all: es.
Qed.
Definition checked_shift tag n (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q (shift_q tag) then
    match peel (shift_left tag n) l,peel (shift_right tag n) r with
    | Some l,Some r=>Some (shift_target tag n l r) | _,_=>None end
  else None.
Lemma checked_shift_spec tag n s t:
  checked_shift tag n s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_shift.
  destruct (q_eqb_spec q (shift_q tag)); try discriminate; subst.
  destruct (peel (shift_left tag n) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel (shift_right tag n) r) as [r'|] eqn:Hr; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf {{shift_q tag}}> r *> 0inf -->* denote (shift_target tag n l' r')).
  apply peel_spec in Hl; apply peel_spec in Hr.
  rewrite Hl,Hr,<-!Str_app_assoc; apply shift_rule.
Qed.

Fixpoint ones (l:list Sym) := match l with S1::l=>S (ones l) | _=>O end.
Fixpoint twins (r:list Sym) := match r with
  | S1::S1::r=>S (twins r) | _=>O end.
Fixpoint digits (r:list Sym) := match r with
  | S1::S0::S0::r=>S (digits r) | _=>O end.
Fixpoint doubles (r:list Sym) := match r with
  | S1::S0::S0::S1::S0::S0::r=>S (doubles r) | _=>O end.
Definition scan_proposal (s:State) : option (Shift*nat) := match s with
  | (F,l,S1::_)=>Some (Keep,ones l)
  | (B,l,S1::_)=>Some (Erase,ones l)
  | (A,_,S1::S1::r)=>Some (DTwins,twins r)
  | (A,_,r)=>match digits r with S n=>Some (Digits,n) | _=>None end
  | (C,_,r)=>match doubles r with S n=>Some (Add,n) | _=>None end
  | (E,_,S1::S1::r)=>Some (BTwins,twins r)
  | (E,_,r)=>match doubles r with S n=>Some (Bdd,n) | _=>None end
  | _=>None end.
Definition scan (s:State) := match scan_proposal s with
  | Some (tag,n)=>checked_shift tag n s | None=>None end.
Lemma scan_spec s t: scan s=Some t -> denote s -->* denote t.
Proof.
  unfold scan; destruct (scan_proposal s) as [[tag n]|]; try discriminate.
  apply checked_shift_spec.
Qed.
Definition primitive (s:State) : option State :=
  let '(q,l,r):=s in let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
  match tm (q,b) with
  | None=>None
  | Some (b,R,q)=>Some (q,b::l,r)
  | Some (b,L,q)=>match l with nil=>Some (q,nil,S0::b::r) | a::l=>Some (q,l,a::b::r) end
  end.
Local Opaque tm.
Lemma primitive_spec s t: primitive s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E; try discriminate;
    destruct d; try destruct l as [|b' l]; intros H; injection H as <-.
  all: eapply evstep_step; [apply step_c_spec;
      cbn [step_c denote Str_app move_left move_right Streams.hd Streams.tl const];
      fold Q Sym in E; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma primitive_halt s: primitive s=None -> halts tm (denote s).
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E.
  all: try (destruct d; try destruct l; discriminate).
  all: intros _; apply halted_halts; exact E.
Qed.
Local Transparent tm.


Definition next (s:State) : State+unit := match accelerate s with
  | Some t=>inl t
  | None=>match scan s with
    | Some t=>inl t
    | None=>match primitive s with Some t=>inl t | None=>inr tt end end end.
Lemma next_spec s:
  match next s with inl t=>denote s -->* denote t | inr _=>halts tm (denote s) end.
Proof.
  unfold next; destruct (accelerate s) as [t|] eqn:E.
  - eapply accelerate_spec; exact E.
  - destruct (scan s) as [t|] eqn:G.
    + eapply scan_spec; exact G.
    + destruct (primitive s) as [t|] eqn:H.
      * eapply primitive_spec; exact H.
      * apply primitive_halt; exact H.
Qed.
Definition check_from (initial:State) fuel := match N_iter_until next (inl initial) fuel with
  | inr _=>true | inl _=>false end.
Lemma check_from_spec initial fuel: check_from initial fuel=true -> halts tm (denote initial).
Proof.
  pose proof (@N_iter_until_spec State unit next (inl initial) fuel
    (fun s=>denote initial -->* denote s) (fun _=>halts tm (denote initial))) as H.
  assert (K: forall s, denote initial -->* denote s ->
    match next s with inl t=>denote initial -->* denote t | inr _=>halts tm (denote initial) end).
  { intros s Hs; pose proof (next_spec s) as Hn; destruct (next s).
    - eapply evstep_trans; eassumption.
    - eapply halts_evstep; eassumption. }
  specialize (H K (evstep_refl _ _)); unfold check_from.
  destruct (N_iter_until next (inl initial) fuel); cbn in H |- *;
    intros Hc; try discriminate; exact H.
Qed.
End Core.

Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.Eqb BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia ZifyNat List String.


Theorem halt: halts tm c0.
Proof.
  apply Core.check_from_spec with (initial:=(A,nil,nil)) (fuel:=200000%N).
  native_check_eq.
Qed.
End TM71.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM91.TM91 *)
Module TM91.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2_0_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.

Lemma ROv2_0_1 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.
Proof. es. Qed.

Lemma ROv2_1_0 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> rd0^^(m+1) *> rd1 *> r.
Proof. es. Qed.

Lemma ROv2_1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> rd1 *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (((m*2+1)*2^i-1)*2) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC (((m*2+1)*2^(i+1))*2+1).
Proof. solve_rule ROv2_0_0. Qed.
Lemma RC2_Ov_0_1 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 (((m*2+1)*2^i)*2+1) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_0_1. Qed.
Lemma RC2_Ov_0_1_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2) 0 1 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. solve_rule ROv2_0_1. Qed.
Lemma RC2_Ov_1_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 (((m*2+1)*2^i-1)*2) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 (i+1) ((2^(i+1)-1)*2+1) m.
Proof. solve_rule ROv2_1_0. Qed.
Lemma RC2_Ov_1_1 len k a m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 (m*2+1) -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)-1) |> RC (m*2+1).
Proof. solve_rule ROv2_1_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => 1<=len /\ n+m+2<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; rename n' into a; divmod2_cases m; rename n' into q.
    + lowbitS_cases q.
      eexists (cfgR _ _ _); split; [apply RC2_Ov_0_0; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3) ltac:(lia)); arith.
    + lowbit_cases q.
      * eexists (cfgR _ _ _); split; [apply RC2_Ov_0_1_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)); lia.
      * eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_0_1; lia|].
        cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
    + lowbitS_cases q.
      eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_1_0; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_1_1; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3+3) ltac:(lia)); lia.
Qed.

Lemma init: c0 -->* to_config (cfgL 5 17 1).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM91.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC23_TM92.v. *)
Module SOC23_TM92.
(* Two SOC23 machines. The shared proof uses only the nine stated word rules;
   each transition table proves these independently. *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q) (odd_left:bool).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0: forall l r n m,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^m *> rd1 *> r.
Hypothesis ROv2_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+3) |> r.

Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  (if odd_left then l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf
   else l <* ld0 <* ld1^^(n*3+2) |> 0inf).

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((m*2+1)*2^i-1) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule ROv2_0. Qed.
Lemma RC2_Ov_1 len k a m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 m -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) |> RC m.
Proof. solve_rule ROv2_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  (if odd_left then LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1
   else LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) |> RC 0).
Proof. destruct odd_left; epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m | cfgR2 len k h n m =>
    1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma append0_bounds len k s: k<2^len ->
  k*2<(k*2+1)*2^s<2^(len+1+s) /\
  (k*2+1)*2^s+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- case_eq odd_left; intros Eodd; [eexists (cfgL _ _ _)|eexists (cfgR _ _ _)]; split.
           1,3: eapply progress_evstep_trans; [apply corner_case|];
             apply progress_evstep; epose proof RC'_Ov_1 as Hodd;
             rewrite Eodd in Hodd; apply Hodd; arith.
           all: cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + lowbitS_cases m.
      eexists (cfgR1 _ _ _ _ _); split; [apply RC2_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_1; lia|].
      cbn [P]; pose proof (append0_bounds len k (n'*3+3) ltac:(lia)); lia.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC23_TM92.

(* SOC23_TM92.TM92 *)
Module TM92.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_TM92.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1LA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+3) |> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 7 73 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=A) (QR:=B) (odd_left:=true) (len:=7) (k:=73) (n:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM92.

(* SOC23_TM92.TM172 *)
Module TM172.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC23_TM92.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_1RF0LD_0RA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.
Lemma ROv2_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> rd0^^m *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3+3) |> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 7 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) |> 0inf.
Proof. intros; st; sr_r; do 8 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 4 10 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (odd_left:=false) (len:=4) (k:=10) (n:=0%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv2_0|exact ROv2_1|exact ROv'_0|exact ROv'_1|exact init|cbn [Counter.P]; lia].
Qed.
End TM172.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* SOC23_TM94.TM94 *)
Module TM94.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0LC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. es. Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> r.
Proof. es. Qed.

Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC2_Ov_0 len k a m: k<2^len ->
  LC len k |> RC2 (a*2) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC (m*2+1).
Proof. solve_rule ROv2_0. Qed.
Lemma RC2_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv2_1. Qed.
Lemma RC2_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv2_1 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m | cfgR2 len k h n m =>
    1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + eexists (cfgR2 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + eexists (cfgR1 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + eexists (cfgR _ _ _); split; [apply RC2_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + lowbit_cases m.
      * eexists (cfgR _ _ _); split; [apply RC2_Ov_1_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
      * eexists (cfgR2 _ _ _ _ _); split; [apply RC2_Ov_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
Qed.

Lemma init: c0 -->* to_config (cfgL 4 10 0).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM94.

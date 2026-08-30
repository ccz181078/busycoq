From BusyCoq Require Import Individual62.

Require Import ZArith ZifyNat Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal NatMod_v2 ES_v3.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA0LF_1LD---_1RE0RA_1RF0RE_1LB0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;1;0]).
Notation hL := (B,[1]).
Notation hLw := (B,[1;0;1;0;1]).
Notation hRL := [(hR,hL)].
Notation hRLw := [(hR,hLw)].
Notation hR' := (F,<[0;1;0;1;1;0;1]).
Notation hRL' := [(hR',hL)].
Notation w := [0;1;0;1].
Notation d := [0;1;1;1].

Definition mh := w++d++w^^2.

Fixpoint RC0 ls :=
match ls with
| [] => 0inf
| a::ls => d *> w^^(2+a) *> RC0 ls
end.

Fixpoint RIncs0 k ls :=
match ls with
| [] => []
| a::ls => k+a::RIncs0 (k*3) ls
end.

Lemma RIncs0_spec k ls:
  sideRLs tm (hRLw^^k) (RC0 ls) (RC0 (RIncs0 k ls)).
Proof.
  gen k.
  induction ls; cbn[RC0 RIncs0]; intros.
  - eapply sideRLs_wall; esx.
  - repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply (IHls (k*3)).
    clear.
    induction k.
    1: esx.
    replace (S k) with (k+1) by lia.
    replace ((k+1)*3) with (k*3+3) by lia.
    eapply segRLs_trans_add.
    1: apply IHk.
    esx.
Qed.

Fixpoint RC0n n :=
match n with
| O => []
| S n => 3::RIncs0 9 (RC0n n)
end.

Definition RC1 n :=
  mh *> RC0 (RC0n n).

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^5); reflexivity).

Lemma RInc1 n:
  sideRLs tm hRL' (RC1 n) (RC1 (1+n)).
Proof.
  unfold RC1.
  cbn[RC0n RC0 Nat.add].
  repeat rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: eapply RIncs0_spec.
  esc.
Qed.

Definition S1 l m n :=
  l <* <[1;0]^^m {{{ (hL,L) }}} RC1 n.

Lemma Inc1 l m n:
  S1 l (3+m) n -->*
  S1 l m (1+n).
Proof.
  epose proof (RInc1 n) as I1.
  eapply sideRLs_1 in I1.
  unfold S1.
  remember (RC1 n) as v1.
  remember (RC1 (1+n)) as v2.
  er.
  follow100 I1.
  finish.
Qed.

Lemma Incs1 l m m0 n:
  S1 l (m*3+m0) n -->*
  S1 l m0 (m+n).
Proof.
  gen n.
  ind m Inc1.
Qed.

Lemma init:
  c0 -->*
  S1 (0inf<*<[1;0;1;0;0;0;1]) 20 0.
Proof.
  esx.
Qed.

Definition P1 ls n :=
  (forall l, l {{D}}> RC0 (RIncs0 1 ls) -->* l <* <[1;0]^^n {{D}}> 0inf).

Lemma P1_O: P1 [] 0.
Proof.
  unfold P1.
  intros.
  finish.
Qed.

Lemma P1_S a ls n:
  P1 (RIncs0 3 ls) n ->
  P1 (a::ls) (9+n+a*2).
Proof.
  unfold P1.
  intros.
  epose proof (RIncs0_spec 1 (RIncs0 3 ls)) as I1.
  eapply sideRLs_1 in I1.
  es; er.
  follow100 I1.
  es; er.
  follow H.
  er.
Qed.

Fixpoint p1 c ls :=
match ls with
| [] => O
| a::ls => 9+(a+c)*2+p1 (c*3+3) ls
end.

Lemma RIncs0_add a b ls:
  RIncs0 a (RIncs0 b ls) = RIncs0 (a+b) ls.
Proof.
  gen a b.
  induction ls; intros; cbn; trivial.
  rewrite IHls; flia.
Qed.

Lemma p1_spec c ls:
  P1 (RIncs0 c ls) (p1 c ls).
Proof.
  gen c.
  induction ls; intros.
  - apply P1_O.
  - cbn[RIncs0 p1].
    applys_eq (P1_S (c+a) (RIncs0 (c*3) ls) (p1 (c*3+3) ls)).
    1: flia.
    rewrite RIncs0_add.
    applys_eq IHls; flia.
Qed.

Lemma p1_RIncs0_RC0n c a i:
  p1 c (RIncs0 a (RC0n i)) = (c + a + 6) * (3^i - 1) + 3 * i.
Proof.
  gen c a.
  induction i; cbn[p1 RIncs0 RC0n]; intros.
  1: lia.
  rewrite RIncs0_add,IHi.
  cbn[Nat.pow].
  nia.
Qed.

Lemma RIncs_O ls:
  ls = RIncs0 0 ls.
Proof.
  induction ls; cbn; congruence.
Qed.

Lemma P1_n i:
  P1 (RC0n i) ((3^i-1)*6+i*3).
Proof.
  applys_eq (p1_spec 0).
  1: apply RIncs_O.
  rewrite (RIncs_O (RC0n i)).
  rewrite p1_RIncs0_RC0n.
  lia.
Qed.

Definition S2 (l:side) n :=
  l {{A}}> RC1 n.

Lemma S2_Ov l i:
  S2 l i -->*
  S1 (l<*<[0;1]) ((3^i-1)*6+i*3+5) 0.
Proof.
  epose proof (P1_n i) as H.
  remember ((3^i-1)*6+i*3) as n.
  unfold P1,S2,S1,RC1 in *.
  intros.
  epose proof (RIncs0_spec 1 (RC0n i)) as I1.
  eapply sideRLs_1 in I1.
  er.
  follow100 I1.
  er.
  follow H.
  er.
Qed.

Lemma S1_Ov1 n:
  S1 (0inf<*<[1;0;1;0;0;0;1]) 2 n -->*
  S2 (0inf<*<[1;0;1;0;1;0;0;0;1;0;1;0;1;0;0]) n.
Proof.
  unfold S1,S2.
  er.
Qed.

Lemma S1_Ov2 n:
  S1 (0inf<*<[1;0;1;0;1;0;0;0;1;0;1;0;1;0;0;0;1]) 2 n -->*
  S2 (0inf<*<[1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;1;1;0;0]) n.
Proof.
  unfold S1,S2.
  er.
Qed.

Lemma S1_Ov3 n:
  halts tm (S1 (0inf<*<[1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;1;1;0;0;0;1]) 2 n).
Proof.
  unfold S1.
  esx.
Qed.

Import NatModTactics.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...
  follow' Incs1...
  follow' S1_Ov1...
  follow' S2_Ov...
  follow' Incs1...
  rewrite <-Str_app_assoc; cbn[app].
  follow' S1_Ov2...
  follow' S2_Ov...
  follow' Incs1...
  rewrite <-Str_app_assoc; cbn[app].
  finish.
  }
  apply S1_Ov3.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0LC_1RC0LD_1LA1RD_0RB1RE_1RB0RF_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[0]).
Notation hL := (A,[1;0;1;0]).
Notation hRL := [(hR,hL)].
Notation w := [1;1;0].
Notation d := [1;1;1;1;1].

Notation RC0 := (flat_map (fun a => d++w^^a)).

Fixpoint RIncs0 k ls :=
match ls with
| [] => []
| a::ls => k+a::RIncs0 (k*2) ls
end.

Lemma RIncs0_spec k ls:
  sideRLs tm (hRL^^k) (RC0 ls *> 0inf) (RC0 (RIncs0 k ls) *> 0inf).
Proof.
  gen k.
  induction ls; cbn[flat_map RIncs0]; intros.
  - eapply sideRLs_wall; esx; st; er.
  - repeat rewrite (Str_app_assoc _ (RC0 _)).
    eapply segRLs_sideRLs_concat.
    2: apply (IHls (k*2)).
    clear.
    induction k.
    1: esx.
    replace (S k) with (k+1) by lia.
    replace ((k+1)*2) with (k*2+2) by lia.
    eapply segRLs_trans_add.
    1: apply IHk.
    esx.
Qed.

Definition L1 n := <[0] <+ <[1]^^n.
Definition L2 n := <[0] <+ <[1]^^n <+ <[0].

Notation "l <| r" := (l {{{ (hL,L) }}} r) (at level 30).
Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).
Notation "l |b> r" := (l {{{ (B,<[1],R) }}} r) (at level 30).
Notation "l |c> r" := (l {{{ (C,<[1],R) }}} r) (at level 30).

Ltac fol H := eapply evstep_trans; [apply H; try lia|].

Lemma L2_LR l n r:
  l <* L2 (2+n) <| r -->*
  l <* L1 (6+n) |> r.
Proof.
  es.
Qed.

Lemma L1_LL l n r:
  l <* L1 (1+n) <| r -->*
  l <| L1 (1+n) *> r.
Proof.
  es.
Qed.

Lemma L17_LL l r:
  l <* L1 7 <| RC0 r *> 0inf -->*
  l <| RC0 (1%nat::r) *> 0inf.
Proof.
  fol L1_LL.
  finish.
Qed.

Lemma L23_LL l r:
  l <* L2 3 <| RC0 r *> 0inf -->*
  l <| RC0 (1%nat::RIncs0 1 r) *> 0inf.
Proof.
  epose proof (RIncs0_spec 1 r) as I1.
  eapply sideRLs_1 in I1.
  fol L2_LR.
  follow100 I1.
  apply L17_LL.
Qed.

Fixpoint RIncs1 n r :=
match n with
| O => r
| S n => 1%nat::RIncs0 1 (RIncs1 n r)
end.

Definition L23 := L2 3.

Lemma L23_LLs l n r:
  l <* L23^^n <| RC0 r *> 0inf -->*
  l <| RC0 (RIncs1 n r) *> 0inf.
Proof.
  gen l r.
  induction n; cbn[RIncs1]; intros.
  1: finish.
  replace (S n) with (n+1) by lia.
  rewrite <-lpow_add'.
  follow IHn.
  apply L23_LL.
Qed.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; repeat rewrite <-const_unfold; try reflexivity.

Lemma init:
  c0 -->*
  0inf <* L2 8 <* L2 3 <* L1 35 <* L23^^5 <* L1 7 <* L23^^81 <| RC0 [2] *> 0inf.
Proof.
  stepn' 106746%N.
Qed.

Lemma L1_RR_0 l n r:
  l |> L1 (n*5) *> r -->*
  l <* L23^^n <* L1 0 |c> r.
Proof.
  ut; es.
Qed.

Lemma L1_RR_0' l n r:
  n mod 5 = O ->
  l |> L1 n *> r -->*
  l <* L23^^(n/5) <* L1 0 |c> r.
Proof.
  intros.
  applys_eq (L1_RR_0 l (n/5) r); flia.
Qed.

Lemma RIncs0_0 r:
  RIncs0 0 r = r.
Proof.
  induction r; cbn;
  congruence.
Qed.

Lemma RIncs0_app n a b:
  RIncs0 n (a++b) = RIncs0 n a ++ RIncs0 (n*2^(length a)) b.
Proof.
  gen n.
  induction a; cbn; intros.
  - flia.
  - rewrite IHa; flia.
Qed.

Lemma RIncs0_add m n r:
  RIncs0 m (RIncs0 n r) = RIncs0 (m+n) r.
Proof.
  gen m n.
  induction r; cbn; intros.
  - trivial.
  - rewrite IHr; flia.
Qed.

Lemma RIncs0_length n r:
  length (RIncs0 n r) = length r.
Proof.
  gen n.
  induction r; cbn; intros.
  - trivial.
  - rewrite IHr; trivial.
Qed.

Lemma all0_length n:
  length ([O]^^n) = n.
Proof.
  rewrite lpow_length; cbn; lia.
Qed.

Lemma RIncs0_cons n a r:
  RIncs0 n (a::r) = (n+a)::RIncs0 (n*2) r.
Proof. trivial. Qed.

Lemma RIncs0_nil n:
  RIncs0 n [] = [].
Proof. trivial. Qed.


Hint Rewrite RIncs0_app RIncs0_cons RIncs0_nil RIncs0_add all0_length RIncs0_length : rincs0.

Ltac rw0 := autorewrite with rincs0.

Lemma RIncs1_spec n r:
  RIncs1 n r = RIncs0 1 ([O]^^n) ++ RIncs0 (2^n-1) r.
Proof.
  gen r.
  induction n; intros.
  - cbn.
    rewrite RIncs0_0; trivial.
  - cbn.
    rewrite IHn.
    rw0.
    flia.
Qed.

Hint Rewrite RIncs1_spec : rincs0.

Lemma RR_c_0 l a b r:
  l <* L1 a |c> RC0 (b*2+0::r) *> 0inf -->*
  l <* L2 (3+a) <* L1 (b*2*3) |c> RC0 r *> 0inf.
Proof.
  ut; es.
Qed.

Lemma RR_c_1 l a b r:
  l <* L1 a |c> RC0 (b*2+1::r) *> 0inf -->*
  l <* L2 (3+a) <* L1 ((b*2+1)*3) |b> RC0 r *> 0inf.
Proof.
  ut; es.
Qed.

Lemma RR_b_0 l a b r:
  l <* L1 a |b> RC0 (b*2+0::r) *> 0inf -->*
  l <* L1 (b*2*3+a+5) |b> RC0 r *> 0inf.
Proof.
  ut; es.
Qed.

Lemma RR_b_1 l a b r:
  l <* L1 a |b> RC0 (b*2+1::r) *> 0inf -->*
  l <* L1 ((b*2+1)*3+a+5) |c> RC0 r *> 0inf.
Proof.
  ut; es.
Qed.

Lemma RIncs0_Os_S a b r:
  RIncs0 a ([O]^^(S b)) ++ r = a :: RIncs0 (a*2) ([O]^^b) ++ r.
Proof.
  cbn; flia.
Qed.

Fixpoint sum r :=
match r with
| [] => O
| a::r => a+sum r
end.

Ltac fnia := repeat (nia || f_equal).

Lemma RRs_b_0s l a b c r:
  l <* L1 a |b> RC0 (RIncs0 (b*2+0) ([O]^^c) ++ r) *> 0inf -->*
  l <* L1 (a+b*2*(2^c-1)*3+c*5) |b> RC0 r *> 0inf.
Proof.
  gen a b.
  induction c; intros.
  - finish.
  - rewrite RIncs0_Os_S by lia.
    fol RR_b_0.
    replace ((b*2+0)*2) with (b*2*2+0) by lia.
    fol IHc.
    cbn[Nat.pow].
    finish.
    fnia.
Qed.

Fixpoint LC0 a n l :=
match n with
| O => l
| S n => LC0 a n l <* <[1;1;1;0] <* L1 (a*2^n)
end.

Lemma LC0_L1 a b n l:
  LC0 b (S n) (l <* L1 a) =
  LC0 (b*2) n (l <* L2 (3+a) <* L1 b).
Proof.
  gen b.
  induction n; intros.
  - ut; st; trivial.
  - remember (S n) as n'.
    cbn[LC0].
    rewrite IHn.
    subst.
    cbn[LC0 Nat.pow].
    flia.
Qed.

Lemma RRs_c_0s l a b c r:
  l <* L1 a |c> RC0 (RIncs0 (b*2+0) ([O]^^c) ++ r) *> 0inf -->*
  LC0 (b*2*3) c (l <* L1 a) |c> RC0 r *> 0inf.
Proof.
  gen l a b.
  induction c; intros.
  - finish.
  - rewrite RIncs0_Os_S by lia.
    fol RR_c_0.
    replace ((b*2+0)*2) with (b*2*2+0) by lia.
    fol IHc.
    rewrite LC0_L1.
    finish.
Qed.

Fixpoint LC1 a n l :=
match n with
| O => l
| S n => LC1 a n l <* L2 (a*2^n+3)
end.

Lemma LC0_LC1 a b n l:
  LC0 b (S n) (l <* L1 a) =
  LC1 b n (l <* L2 (3+a)) <* L1 (b*2^n).
Proof.
  gen a b l.
  induction n; intros; cbn[LC0 LC1] in *.
  - ut; st; trivial.
  - rewrite IHn.
    rewrite (Nat.add_comm (b*2^n) 3).
    ut; st; trivial.
Qed.

Lemma RRs_c_0s' l a b c r:
  l <* L1 a |c> RC0 (RIncs0 (b*2+0) ([O]^^(1+c)) ++ r) *> 0inf -->*
  LC1 (b*2*3) c (l <* L2 (3+a)) <* L1 (b*2*3*2^c) |c> RC0 r *> 0inf.
Proof.
  intros.
  fol RRs_c_0s.
  rewrite LC0_LC1.
  finish.
Qed.

Lemma RRs_c_10s l a b c r:
  l <* L1 a |c> RC0 (RIncs0 (b*2+1) ([O]^^(1+c)) ++ r) *> 0inf -->*
  l <* L2 (3+a) <* L1 ((b*2+1)*(2^c*6-3)+c*5) |b> RC0 r *> 0inf.
Proof.
  rewrite RIncs0_Os_S by lia.
  fol RR_c_1.
  rewrite <-(Nat.add_0_r ((b*2+1)*2)).
  fol RRs_b_0s.
  finish.
  fnia.
Qed.

Lemma RRs_b_10s l a b c r:
  l <* L1 a |b> RC0 (RIncs0 (b*2+1) ([O]^^(2+c)) ++ r) *> 0inf -->*
  LC1 ((b*2+1)*6) c (l <* L2 ((b*2+1)*3+a+8)) <* L1 ((b*2+1)*6*2^c) |c> RC0 r *> 0inf.
Proof.
  intros.
  cbn[Nat.add].
  rewrite RIncs0_Os_S by lia.
  fol RR_b_1.
  rewrite <-(Nat.add_0_r ((b*2+1)*2)).
  fol RRs_c_0s'.
  finish.
Qed.

Lemma RL_b l a:
  l <* L1 a |b> RC0 [] *> 0inf -->*
  l <* L1 (1+a) <| RC0 [] *> 0inf.
Proof.
  ut; es.
Qed.

Lemma L1_RL_7 l a:
  l |> L1 (a*5+7) *> RC0 [] *> 0inf -->*
  l <* L23^^a <| RC0 [2] *> 0inf.
Proof.
  ut; es.
Qed.

Lemma LC1_S a n l r:
  LC1 a (1+n) l <| r -->*
  LC1 a n l <* L2 (a*2^n+3) <| r.
Proof.
  finish.
Qed.
  
Lemma L1_6 l a b r:
  halts tm (l |> L1 (a*5+6) *> RC0 (RIncs1 (1+b) r) *> 0inf).
Proof.
  ut; esx.
Qed.

Import NatModTactics.

Ltac fol H ::=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr | rw_all].

Lemma halt:
  halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  fol init.
  fol L23_LLs.
  fol L17_LL.
  fol L23_LLs.
  fol L1_LL.
  fol L2_LR.
  fol L1_RR_0'.
  rw0; rw_all.
  fol RRs_c_10s.
  fol RR_b_0.
  fol RRs_b_10s.
  fol RR_c_1.
  fol RL_b.
  fol L1_LL.
  fol L2_LR.
  fol L1_RL_7.
  fol L23_LLs.
  fol L1_LL.
  fol LC1_S.
  fol L2_LR.
  finish.
  }
  eapply Peq; [|apply L1_6]; match_Nexpr.
Time Qed.

End TM2.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC1LC_1LD1RE_1LB0LC_0RF0RA_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[1]).
Notation hL := (C,[0;1;0]).
Notation hR' := (F,<[1;0;0;0]).
Notation hR'' := (A,<[1;1;1;0;1;0]).
Notation h := [(hR,hL)].
Notation w := [1;0].
Notation d := [1;1;1;0].

Notation RC0 := (flat_map (fun a => d++w^^a)).

Fixpoint RIncs0 k ls :=
match ls with
| [] => []
| a::ls => k+a::RIncs0 (k*2) ls
end.

Lemma RIncs0_spec k ls:
  segRLs tm (h^^k) (h^^(k*2^(length ls))) (RC0 ls) (RC0 (RIncs0 k ls)).
Proof.
  gen k.
  induction ls; cbn[flat_map RIncs0 length]; intros.
  - rewrite Nat.mul_1_r.
    eapply segRLs_wall''; esx.
  - eapply segRLs_concat.
    2: applys_eq (IHls (k*2)); cbn; flia.
    clear.
    induction k.
    1: esx.
    replace (S k) with (k+1) by lia.
    replace ((k+1)*2) with (k*2+2) by lia.
    eapply segRLs_trans_add.
    1: apply IHk.
    esx.
Qed.

Lemma RH_Incs k n:
  sideRLs tm (h^^k) (RC0 [n] *> 0inf) (RC0 [n+k*3] *> 0inf).
Proof.
  sideRLs_ind k.
Qed.

Definition RC1 '(r,n) := RC0 r *> RC0 [n] *> 0inf.

Definition RIncs1 k '(r,n) := (RIncs0 k r,n+k*2^(length r)*3).

Lemma RIncs1_spec k x:
  sideRLs tm (h^^k) (RC1 x) (RC1 (RIncs1 k x)).
Proof.
  unfold RC1,RIncs1.
  destruct x as [r n].
  eapply segRLs_sideRLs_concat.
  1: apply RIncs0_spec.
  apply RH_Incs.
Qed.

Notation "l <| r" := (l {{{ (hL,L) }}} r) (at level 30).
Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).
Notation "l |f> r" := (l {{{ (hR',R) }}} r) (at level 30).
Notation "l |fw> r" := (l {{{ (hR'',R) }}} r) (at level 30).

Notation l24 := <[1;1;0;1;1;1;1;0].
Notation w' := <[1;0].
Notation d' := <[1;1;1;0].
Notation d0' := <[1;0;0;0].

Lemma init:
  c0 -->*
  0inf <* <[1;1;0] <* w' <* d' <* <[1;0;0;0;1;0;0;1;1;0] <* w' <* d'^^2 <* w' <* d' |fw> RC0 [23] *> 0inf. 
Proof.
  esx.
Qed.

Definition Rcons a (x:(list nat)*nat) :=
let '(r,n):=x in (a::r,n).

Lemma RC1_RL l x:
  l |> RC1 x -->*
  l <| RC1 (RIncs1 1 x).
Proof.
  epose proof (RIncs1_spec 1 x) as H.
  eapply sideRLs_1 in H.
  follow100 H.
  finish.
Qed.

Lemma LR1 l r:
  l <* <[1;0;0;0;1;0;0;1;1;0] <* w' <* d'^^2 <* w' <* d' <* l24 <| r -->*
  l <* <[1;1;1;0;0;1;1;0] <* d0' <* w' <* d0'^^2 <* w' <* d0' <* <[1;0;0;0;1] |f> r.
Proof.
  unfold to_DH_config.
  es' & l r.
Qed.

Lemma RIncs1_Rcons k n x:
  RIncs1 k (Rcons n x) =
  Rcons (n+k) (RIncs1 (k*2) x).
Proof.
  destruct x as [r r0].
  unfold Rcons,RIncs1.
  cbn.
  flia.
Qed.

Lemma RIncs0_0 r:
  RIncs0 0 r = r.
Proof.
  induction r; cbn;
  congruence.
Qed.

Lemma RIncs0_add m n r:
  RIncs0 m (RIncs0 n r) = RIncs0 (m+n) r.
Proof.
  gen m n.
  induction r; cbn; intros.
  - trivial.
  - rewrite IHr; flia.
Qed.

Lemma RIncs0_length n r:
  length (RIncs0 n r) = length r.
Proof.
  gen n.
  induction r; cbn; intros.
  - trivial.
  - rewrite IHr; trivial.
Qed.

Lemma RIncs1_0 x:
  RIncs1 0 x = x.
Proof.
  unfold RIncs1.
  destruct x as [r n].
  rewrite RIncs0_0.
  flia.
Qed.

Lemma RIncs1_add a b x:
  RIncs1 a (RIncs1 b x) =
  RIncs1 (a+b) x.
Proof.
  destruct x as [r r0].
  unfold RIncs1.
  rewrite RIncs0_add.
  rewrite RIncs0_length.
  flia.
Qed.

Lemma Rcons_spec a x:
  RC1 (Rcons a x) = d *> w^^a *> RC1 x.
Proof.
  unfold RC1,Rcons.
  destruct x as [r n].
  cbn[RC0].
  st; trivial.
Qed.

Lemma f_RR_Rcons_1 l a x:
  l |f> RC1 (Rcons (a*2+1) x) -->*
  l <* d' <* w' <* d'^^a |fw> RC1 (RIncs1 1 x).
Proof.
  rewrite Rcons_spec.
  es; er.
  follow RC1_RL.
  es; er.
Qed.

Lemma f_RR_Rcons_0 l a x:
  l |f> RC1 (Rcons (a*2+0) x) -->*
  l <* d' <* w' <* d'^^a |f> RC1 (RIncs1 1 x).
Proof.
  rewrite Rcons_spec.
  es; er.
  follow RC1_RL.
  es; er.
Qed.

Notation l3102 := <[1;1;1;0;1;0;0;1;1;0].

Lemma fw_RR_Rcons_1 l a x:
  l |fw> RC1 (Rcons (a*2+3) x) -->*
  l <* l3102 <* d'^^a |fw> RC1 x.
Proof.
  rewrite Rcons_spec.
  es.
Qed.

Lemma fw_RR_Rcons_0 l a x:
  l |fw> RC1 (Rcons (a*2+2) x) -->*
  l <* l3102 <* d'^^a |f> RC1 x.
Proof.
  rewrite Rcons_spec.
  es.
Qed.

Lemma f_RIncs1_nil l k n:
  l |f> RC1 (RIncs1 k ([],n)) -->*
  l |f> RC0 [n+k*3] *> 0inf.
Proof.
  cbn.
  finish.
Qed.

Lemma f_RH_1 l n:
  halts tm (l |f> RC0 [n*2+1] *> 0inf).
Proof.
  esx.
Qed.

Definition Rapp0s a (x:(list nat)*nat) :=
  let '(r,n):=x in ([O]^^a++r,n).

Lemma f_RH_0 l n:
  l |f> RC0 [n*2+0] *> 0inf -->*
  l <| RC1 (Rcons 1 (Rapp0s n ([],2))).
Proof.
  cbn.
  repeat rewrite flat_map_app.
  repeat rewrite flat_map_lpow.
  st.
  es' n & l.
Qed.

Lemma fw_RH_0 l n:
  halts tm (l |fw> RC0 [n*2+0] *> 0inf).
Proof.
  cbn.
  st.
  es' n & l.
Qed.

Lemma fw_RH_1 l n:
  l |fw> RC0 [n*2+1] *> 0inf -->*
  l <* l24 <| RC1 (RIncs1 1 (Rapp0s n ([],2))).
Proof.
  eapply evstep_trans.
  2: apply RC1_RL.
  cbn.
  repeat rewrite flat_map_app.
  repeat rewrite flat_map_lpow.
  st.
  es' n & l.
Qed.

Lemma LL_d's l n x:
  l <* d'^^n <| RC1 x -->*
  l <| RC1 (Rapp0s n x).
Proof.
  unfold RC1,Rapp0s.
  destruct x as [r n0].
  rewrite flat_map_app.
  rewrite flat_map_lpow.
  es.
Qed.

Notation r24 := [1;1;0;1;1;1;1;0].

Hint Rewrite RIncs1_add RIncs1_Rcons: rw1.
Ltac rw1 := autorewrite with rw1.

Lemma LL_l3102 l x:
  l <* l3102 <| RC1 x -->*
  l <| r24 *> RC1 (Rcons 1 (RIncs1 2 x)).
Proof.
  rewrite Rcons_spec.
  er.
  follow RC1_RL.
  er.
  follow RC1_RL.
  er.
  rw1.
  finish.
Qed.

Lemma LR_l3102_d's_r24 l n r:
  l <* l3102 <* d'^^n <| r24 *> r -->*
  l <* l24 <* d0'^^(1+n) <* <[1;0;0;0;1] |f> r.
Proof.
  es.
Qed.

Lemma Rapp0s_S n x:
  Rapp0s (S n) x =
  Rcons 0 (Rapp0s n x).
Proof.
  destruct x as [r n0].
  trivial.
Qed.

Lemma RIncs1_Rapp0s_S k n x:
  RIncs1 k (Rapp0s (S n) x) =
  Rcons k (RIncs1 (k*2) (Rapp0s n x)).
Proof.
  rewrite Rapp0s_S.
  rewrite RIncs1_Rcons.
  flia.
Qed.

Definition L1 k l :=
  d'^^k*>w'*>d'*>l.

Lemma f_RR_Rapp0s_1_1 l k n x:
  l |f> RC1 (RIncs1 (k*2+1) (Rapp0s (1+n) x)) -->*
  L1 k l |fw> RC1 (RIncs1 (k*2*2+3) (Rapp0s n x)).
Proof.
  cbn[Nat.add].
  rewrite RIncs1_Rapp0s_S.
  follow f_RR_Rcons_1.
  rw1.
  finish.
Qed.

Definition L2 k l := d'^^(k*2)*>l3102*>L1 k l.

Lemma f_RR_Rapp0s_1_2 l k n x:
  l |f> RC1 (RIncs1 (k*2+1) (Rapp0s (2+n) x)) -->*
  L2 k l |fw> RC1 (RIncs1 ((k*4+2)*2+2) (Rapp0s n x)).
Proof.
  cbn[Nat.add].
  follow f_RR_Rapp0s_1_1.
  rewrite RIncs1_Rapp0s_S.
  follow fw_RR_Rcons_1.
  finish.
Qed.

Definition L3 k l := d'^^(k*4+2)*>l3102*>L2 k l.

Lemma f_RR_Rapp0s_1_3 l k n x:
  l |f> RC1 (RIncs1 (k*2+1) (Rapp0s (3+n) x)) -->*
  L3 k l |f> RC1 (RIncs1 ((k*8+6)*2+0) (Rapp0s n x)).
Proof.
  cbn[Nat.add].
  follow f_RR_Rapp0s_1_2.
  rewrite RIncs1_Rapp0s_S.
  follow fw_RR_Rcons_0.
  finish.
Qed.

Definition L4 k l := d'^^(k*8+6)*>w'*>d'*>L3 k l.

Lemma f_RR_Rapp0s_1_4 l k n x:
  l |f> RC1 (RIncs1 (k*2+1) (Rapp0s (4+n) x)) -->*
  L4 k l |f> RC1 (RIncs1 ((k*16+12)*2+1) (Rapp0s n x)).
Proof.
  cbn[Nat.add].
  follow f_RR_Rapp0s_1_3.
  rewrite RIncs1_Rapp0s_S.
  follow f_RR_Rcons_0.
  rw1.
  finish.
Qed.

Definition L4a k l :=
  d' ^^ (k * 8 + 10) *> w' *> d' ^^ (1 + (k * 4 + 4)) *> l3102 *> d' ^^ (k * 2 + 1) *> l3102 *> d' ^^ (k + 1) *> w' *> d' *> l.

Lemma f_RR_Rcons1_Rapp0s_1_3 l k n x:
  l |f> RC1 (RIncs1 (k*2+2) (Rcons 1 (Rapp0s (3+n) x))) -->*
  L4a k l |f> RC1 (RIncs1 ((k*16+20)*2+1) (Rapp0s n x)).
Proof.
  cbn[Nat.add].
  rw1.
  replace (1+(k*2+2)) with ((k+1)*2+1) by lia.
  follow f_RR_Rcons_1.
  rw1.
  rewrite RIncs1_Rapp0s_S.
  replace (1+(k*2+2)*2) with ((k*2+1)*2+3) by lia.
  follow fw_RR_Rcons_1.
  rewrite RIncs1_Rapp0s_S.
  replace (((k*2+1)*2+3)*2) with ((k*4+4)*2+2) by lia.
  follow fw_RR_Rcons_0.
  rewrite RIncs1_Rapp0s_S.
  replace (((k*4+4)*2+2)*2) with ((k*8+10)*2+0) by lia.
  follow f_RR_Rcons_0.
  rw1.
  finish.
Qed.

Lemma f_Rapp0s_O l k x:
  l |f> RC1 (RIncs1 k (Rapp0s 0 x)) -->*
  l |f> RC1 (RIncs1 k x).
Proof.
  destruct x.
  finish.
Qed.

Definition L3' k l := [1;0;0;0;1]*>d0'^^(1+k*2)*>l24*>L1 k l.

Lemma f_RR_Rapp0s_1_3' l k n:
  l |f> RC1 (RIncs1 (k*2+1) (Rapp0s 3 ([],n*2+0))) -->*
  L3' k l |f> RC1 (RIncs1 1 (Rapp0s (k*4+3) (Rcons 1 (Rapp0s (n+k*24+18) ([],2))))).
Proof.
  follow f_RR_Rapp0s_1_3.
  follow f_Rapp0s_O.
  follow f_RIncs1_nil.
  replace (n*2+0+((k*8+6)*2+0)*3) with ((n+(k*8+6)*3)*2+0) by lia.
  follow f_RH_0.
  unfold L3,L2.

  follow LL_d's.
  follow LL_l3102.
  follow LR_l3102_d's_r24.

  replace (k*4+3) with (S(k*4+2)) by lia.
  rewrite Rapp0s_S.
  rw1.
  finish.
Qed.

Fixpoint L4s k n l :=
match n with
| O => l
| S n => L4 (k*2^(n*4)+(2^(n*4)-1)*4/5) (L4s k n l)
end.

Lemma pow16_mod5 n:
  2^(n*4) mod 5 = 1%nat.
Proof.
  induction n; cbn - [Nat.modulo]; lia.
Qed.

Lemma f_RR_Rapp0s_1_4n l k n n0 x:
  l |f> RC1 (RIncs1 (k*2+1) (Rapp0s (n*4+n0) x)) -->*
  L4s k n l |f> RC1 (RIncs1 ((k*2^(n*4)+(2^(n*4)-1)*4/5)*2+1) (Rapp0s n0 x)).
Proof.
  gen n0.
  induction n; intros.
  - finish.
  - follow (IHn (4+n0)).
    follow f_RR_Rapp0s_1_4.
    epose proof (pow16_mod5 n).
    cbn[L4s].
    replace (S n*4) with (4+n*4) by lia.
    rewrite Nat.pow_add_r.
    finish.
Qed.

Import NatModTactics.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr | ].

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow' init...
  follow' fw_RH_1...
  follow' LR1...

  follow' f_RR_Rapp0s_1_4n...
  follow' f_RR_Rapp0s_1_3'...

  follow' f_RR_Rapp0s_1_4n...
  follow' f_RR_Rapp0s_1_3...
  follow' f_Rapp0s_O...

  follow' f_RR_Rcons1_Rapp0s_1_3...
  follow' f_RR_Rapp0s_1_4n...
  follow' f_Rapp0s_O...

  follow' f_RIncs1_nil...
  finish.
  }
  eapply Peq; [|apply f_RH_1]; match_Nexpr.
Time Qed.

End TM4.



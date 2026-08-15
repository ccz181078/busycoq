From BusyCoq Require Import Individual62.

Require Import ZArith ZifyNat Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal NatMod_v2.

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

Compute (rev ([1; 0; 0; 0; 1; 0; 1; 0; 1; 0; 0; 0; 1; 0; 1; 0; 1])).

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



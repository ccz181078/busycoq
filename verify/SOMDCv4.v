From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import String List PeanoNat NArith ZifyNat Lia.
From BusyCoq Require Import SimplPow2.
Open Scope sym.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.segRLs_c_spec with (T:=10^6); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Lemma LBC_IncsOv tm h w n:
  segRLs tm h (h^^2) w w ->
  segRLs tm h (h^^(2^n)) (w^^n) (w^^n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    apply segRLs_nil.
  - cbn.
    rewrite Nat.add_0_r,lpow_add.
    eapply segRLs_concat.
    1: apply H.
    cbn.
    rewrite app_nil_r.
    eapply segRLs_trans; apply IHn.
Qed.

Notation ld := [1;1].
Notation m1 := [1;1;1;0].
Notation d0 := [0;0].
Notation d1 := [1;0].
Notation d001 := (d0++d0++d1).

Definition RC tp i :=
match tp with
| 0%nat => ld^^(i*60+6)*>m1*>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+1)*>0inf
| 1%nat => ld^^(i*60+5)*>m1*>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+1)*>0inf
| 2 => ld^^(i*60+5)*>m1*>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+1)*>0inf
| 3 => ld^^(i*60+12)*>m1*>1>>0>>0>>0>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+2)*>0inf
| 4 => ld^^(i*60+11)*>m1*>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>0>>0>>1>>0>>0>>0>>0>>0>>d001^^(i*20+3)*>0inf
| 5 => ld^^(i*60+11)*>m1*>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+3)*>0inf
| 6 => ld^^(i*60+18)*>m1*>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+4)*>0inf
| 7 => ld^^(i*60+20)*>m1*>0>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+5)*>0inf
| 8 => ld^^(i*60+22)*>m1*>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+6)*>0inf
| 9 => ld^^(i*60+20)*>m1*>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>0>>0>>0>>0>>d001^^(i*20+6)*>0inf
| 10 => ld^^(i*60+20)*>m1*>1>>1>>1>>1>>1>>0>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>0>>0>>1>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+6)*>0inf
| 11 => ld^^(i*60+24)*>m1*>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+7)*>0inf
| 12 => ld^^(i*60+30)*>m1*>1>>0>>0>>0>>0>>0>>0>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+8)*>0inf
| 13 => ld^^(i*60+26)*>m1*>1>>0>>1>>0>>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+7)*>0inf
| 14 => ld^^(i*60+26)*>m1*>1>>1>>1>>1>>1>>0>>0>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+8)*>0inf
| 15 => ld^^(i*60+30)*>m1*>0>>0>>0>>0>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+9)*>0inf
| 16 => ld^^(i*60+32)*>m1*>1>>0>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>0>>0>>0>>0>>d001^^(i*20+10)*>0inf
| 17 => ld^^(i*60+32)*>m1*>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>0>>0>>1>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+10)*>0inf
| 18 => ld^^(i*60+42)*>m1*>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+11)*>0inf
| 19 => ld^^(i*60+40)*>m1*>1>>0>>1>>0>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>1>>0>>1>>0>>0>>0>>0>>0>>d001^^(i*20+12)*>0inf
| 20 => ld^^(i*60+40)*>m1*>1>>1>>1>>1>>1>>0>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>0>>0>>0>>0>>d001^^(i*20+13)*>0inf
| 21 => ld^^(i*60+44)*>m1*>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+13)*>0inf
| 22 => ld^^(i*60+50)*>m1*>1>>0>>0>>0>>1>>0>>1>>0>>0>>0>>1>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+14)*>0inf
| 23 => ld^^(i*60+49)*>m1*>1>>0>>1>>1>>1>>1>>1>>1>>1>>0>>0>>0>>1>>0>>0>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+15)*>0inf
| 24 => ld^^(i*60+49)*>m1*>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>1>>0>>0>>0>>1>>0>>0>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+16)*>0inf
| 25 => ld^^(i*60+56)*>m1*>0>>0>>1>>0>>0>>0>>0>>0>>0>>0>>0>>0>>d001^^(i*20+17)*>0inf
| 26 => ld^^(i*60+58)*>m1*>0>>0>>0>>0>>0>>0>>0>>0>>0>>0>>d001^^(i*20+18)*>0inf
| 27 => ld^^(i*60+60)*>m1*>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+18)*>0inf
| 28 => ld^^(i*60+60)*>m1*>1>>1>>1>>1>>1>>0>>0>>0>>1>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+19)*>0inf
| 29 => ld^^(i*60+64)*>m1*>0>>0>>0>>0>>1>>0>>1>>0>>0>>0>>d001^^(i*20+20)*>0inf
| _ => ld^^(i*60+66)*>m1*>1>>0>>0>>0>>1>>0>>0>>0>>d001^^(i*20+21)*>0inf
end.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC1RB_1LD1RC_1LA0LE_0LF1RB_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (B,<[1;1]).

Notation h1 := [((C,[]),(D,[]))].
Notation h2 := [((C,[1]),(E,[0]))].
Notation h3 := [(hR',(D,[]))].

Lemma LIncs n:
  segRLs tm h3 (h3++h1^^(2^n-1)) (ld^^n) (ld^^n).
Proof.
  induction n.
  - rewrite app_nil_r.
    apply segRLs_nil.
  - replace (2^S n-1) with (2^n-1+2^n) by (cbn; lia).
    rewrite lpow_add,app_assoc.
    cbn[lpow].
    eapply segRLs_concat.
    2: eapply segRLs_trans.
    2: apply IHn.
    2: apply LBC_IncsOv; esc.
    esc.
Qed.

Lemma LIncs' k i r r' j j0:
  sideRLs tm (h3++h1^^(2^(i*60+k)-1)) (ld^^j*>r) (ld^^j0*>r') ->
  sideRLs tm h3 (ld^^(i*60+(k+j))*>r) (ld^^(i*60+(k+j0))*>r').
Proof.
  intro H.
  do 2 rewrite Nat.add_assoc.
  do 2 rewrite <-(lpow_add' ld (i*60+k)).
  eapply segRLs_sideRLs_concat.
  1: apply LIncs.
  apply H.
Qed.

Lemma MIncs n b a c r r':
  let w:=Str_firstn n r in
  let n':=2+n in
  let w':=Str_firstn n' r' in
  segRLs tm h3 (h2^^b) w w' ->
  segRLs tm h1 (h2^^(2^a)) w' w' ->
  sideRLs tm (h2^^(c*(2^a)+b)) (Str_nth_tl n r) (Str_nth_tl n' r') ->
  sideRLs tm (h3++h1^^c) (r) (r').
Proof.
  intros.
  rewrite (Str_firstn_spec n r).
  rewrite (Str_firstn_spec n' r').
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  rewrite Nat.add_comm,lpow_add.
  eapply segRLs_trans.
  1: apply H.
  applys_eq (@segRLs_wall'' tm h1 (h2^^(2^a)) w' c).
  2: apply H0.
  rewrite lpow_mul.
  reflexivity.
Qed.

Lemma RInc_d0 n r r':
  n mod 2 = 0%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d0*>r) (d0*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d1 n r r':
  n mod 2 = 0%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d1*>r) (d1*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d0_d1 n r r':
  n mod 2 = 1%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d0*>r) (d1*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 1 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d1_d0 n r r':
  n mod 2 = 1%nat ->
  sideRLs tm (h2^^(n/2+1)) r r' ->
  sideRLs tm (h2^^n) (d1*>r) (d0*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 1 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d001_S i k r:
  d001^^(i+(S k))*>r =
  0>>0>>0>>0>>1>>0>>d001^^(i+k)*>r.
Proof.
  st; simpl_rotate; reflexivity.
Qed.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

Ltac RIncs :=
  repeat 
  ((eapply RInc_d0; [lia'|]) ||
  (eapply RInc_d1; [lia'|]) ||
  (eapply RInc_d0_d1; [lia'|]) ||
  (eapply RInc_d1_d0; [lia'|]); simpl_nat).

Lemma RIncs_001 i k k0:
  k0=k*3+2 ->
  sideRLs tm (h2 ^^ (2 ^ (i * 60 + k0) + 0)) (d001 ^^ (i * 20 + k) *> 0inf)
  (d001 ^^ (i * 20 + (S k)) *> 0inf).
Proof.
  intro; subst.
  remember (i*20+k) as n.
  replace (i*20+S k) with (n+1) by lia.
  replace (i*60+(k*3+2)) with (n*3+2) by lia.
  clear.
  induction n.
  - esc.
  - cbn[lpow Nat.add].
    do 2 rewrite (Str_app_assoc d001).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (segRLs_addmul_v2 8 1 (2^(n*3+2)) 0 0); unfold DH0.
    1,2: cbn; flia.
    1,2: esc.
Qed.

Ltac solve_v2 :=
  rewrite d001_S; RIncs; try rewrite <-d001_S.

Ltac solve_v3 :=
  apply RIncs_001; reflexivity.

Ltac solve_v1 a b c d :=
  apply (LIncs' a);
  apply (MIncs b c d); [esc|esc|cbn - [Nat.pow];
  cbn[Nat.pow]; rewrite Nat.mul_1_r;
  repeat rewrite Nat.mul_assoc;
  RIncs; try solve[solve_v3|solve_v2; solve_v3]].

Lemma RC_spec tp i:
  tp<30 ->
  sideRLs tm h3 (RC tp i) (RC (S tp) i).
Proof.
  intro Htp.
  do 30 (destruct tp as [|tp]; [unfold RC; shelve|]).
  lia.
  Unshelve.
  - solve_v1 4 14 1%nat 2.
  - solve_v1 5 14 8 4.
  - solve_v1 5 16 112 7.
  - solve_v1 10 14 1%nat 2.
  - solve_v1 11 14 8 4.
  - solve_v1 11 16 112 7.
  - solve_v1 18 6 3 2.
  - solve_v1 20 6 3 2.
  - solve_v1 18 20 1%nat 3.
  - solve_v1 20 18 8 4.
  - solve_v1 20 20 112 7.
  - solve_v1 24 14 56 6.
  - solve_v1 22 32 1%nat 5.
    solve_v2.
    solve_v2.
    solve_v3.
  - solve_v1 25 28 32 5.
  - solve_v1 26 28 128 7.
  - solve_v1 30 22 32 6.
  - solve_v1 32 20 64 7.
  - solve_v1 32 22 896 10.
  - solve_v1 38 20 1%nat 3.
  - solve_v1 40 18 8 4.
  - solve_v1 40 20 112 7.
  - solve_v1 44 14 56 6.
  - solve_v1 48 14 1%nat 2.
  - solve_v1 49 14 8 4.
  - solve_v1 49 16 112 7.
  - solve_v1 56 6 3 2.
  - solve_v1 58 6 3 2.
  - solve_v1 60 8 1%nat 1%nat.
  - solve_v1 60 10 14 4.
  - solve_v1 64 6 3 2.
Time Qed.

Definition S' '(tp,i) := 0inf {{{ (hR',R) }}} RC tp i.

Lemma BigStep tp i:
  tp<30 ->
  S' (tp,i) -->+ S' (S tp,i).
Proof.
  unfold S'.
  intro H.
  eapply RC_spec in H.
  eapply sideRLs_1 in H.
  follow10 H.
  remember (RC (S tp) i).
  er.
Qed.

Lemma S'_Ov i:
  S' (30,i) = S' (O,S i).
Proof.
  unfold S',RC.
  flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(tp,i) => tp<30).
  2: lia.
  intros [tp i] HP.
  assert (S tp<30\/tp=29) as [E|E] by lia.
  - eexists; split.
    1: apply BigStep,HP.
    cbn; lia.
  - eexists; split.
    + rewrite <-S'_Ov.
      rewrite E.
      apply BigStep; lia.
    + cbn; lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC1LA_0RF1RD_0LE1RC_---0LD_1LA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (D,<[1;1]).

Notation h1 := [((F,[]),(A,[]))].
Notation h2 := [((F,[1]),(D,[0]))].
Notation h3 := [(hR',(A,[]))].

Lemma LIncs n:
  segRLs tm h3 (h3++h1^^(2^n-1)) (ld^^n) (ld^^n).
Proof.
  induction n.
  - rewrite app_nil_r.
    apply segRLs_nil.
  - replace (2^S n-1) with (2^n-1+2^n) by (cbn; lia).
    rewrite lpow_add,app_assoc.
    cbn[lpow].
    eapply segRLs_concat.
    2: eapply segRLs_trans.
    2: apply IHn.
    2: apply LBC_IncsOv; esc.
    esc.
Qed.

Lemma LIncs' k i r r' j j0:
  sideRLs tm (h3++h1^^(2^(i*60+k)-1)) (ld^^j*>r) (ld^^j0*>r') ->
  sideRLs tm h3 (ld^^(i*60+(k+j))*>r) (ld^^(i*60+(k+j0))*>r').
Proof.
  intro H.
  do 2 rewrite Nat.add_assoc.
  do 2 rewrite <-(lpow_add' ld (i*60+k)).
  eapply segRLs_sideRLs_concat.
  1: apply LIncs.
  apply H.
Qed.

Lemma MIncs n b a c r r':
  let w:=Str_firstn n r in
  let n':=2+n in
  let w':=Str_firstn n' r' in
  segRLs tm h3 (h2^^b) w w' ->
  segRLs tm h1 (h2^^(2^a)) w' w' ->
  sideRLs tm (h2^^(c*(2^a)+b)) (Str_nth_tl n r) (Str_nth_tl n' r') ->
  sideRLs tm (h3++h1^^c) (r) (r').
Proof.
  intros.
  rewrite (Str_firstn_spec n r).
  rewrite (Str_firstn_spec n' r').
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  rewrite Nat.add_comm,lpow_add.
  eapply segRLs_trans.
  1: apply H.
  applys_eq (@segRLs_wall'' tm h1 (h2^^(2^a)) w' c).
  2: apply H0.
  rewrite lpow_mul.
  reflexivity.
Qed.

Lemma RInc_d0 n r r':
  n mod 2 = 0%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d0*>r) (d0*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d1 n r r':
  n mod 2 = 0%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d1*>r) (d1*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d0_d1 n r r':
  n mod 2 = 1%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d0*>r) (d1*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 1 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d1_d0 n r r':
  n mod 2 = 1%nat ->
  sideRLs tm (h2^^(n/2+1)) r r' ->
  sideRLs tm (h2^^n) (d1*>r) (d0*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 1 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d001_S i k r:
  d001^^(i+(S k))*>r =
  0>>0>>0>>0>>1>>0>>d001^^(i+k)*>r.
Proof.
  st; simpl_rotate; reflexivity.
Qed.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

Ltac RIncs :=
  repeat 
  ((eapply RInc_d0; [lia'|]) ||
  (eapply RInc_d1; [lia'|]) ||
  (eapply RInc_d0_d1; [lia'|]) ||
  (eapply RInc_d1_d0; [lia'|]); simpl_nat).

Lemma RIncs_001 i k k0:
  k0=k*3+2 ->
  sideRLs tm (h2 ^^ (2 ^ (i * 60 + k0) + 0)) (d001 ^^ (i * 20 + k) *> 0inf)
  (d001 ^^ (i * 20 + (S k)) *> 0inf).
Proof.
  intro; subst.
  remember (i*20+k) as n.
  replace (i*20+S k) with (n+1) by lia.
  replace (i*60+(k*3+2)) with (n*3+2) by lia.
  clear.
  induction n.
  - esc.
  - cbn[lpow Nat.add].
    do 2 rewrite (Str_app_assoc d001).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (segRLs_addmul_v2 8 1 (2^(n*3+2)) 0 0); unfold DH0.
    1,2: cbn; flia.
    1,2: esc.
Qed.

Ltac solve_v2 :=
  rewrite d001_S; RIncs; try rewrite <-d001_S.

Ltac solve_v3 :=
  apply RIncs_001; reflexivity.

Ltac solve_v1 a b c d :=
  apply (LIncs' a);
  apply (MIncs b c d); [esc|esc|cbn - [Nat.pow];
  cbn[Nat.pow]; rewrite Nat.mul_1_r;
  repeat rewrite Nat.mul_assoc;
  RIncs; try solve[solve_v3|solve_v2; solve_v3]].

Lemma RC_spec tp i:
  tp<30 ->
  sideRLs tm h3 (RC tp i) (RC (S tp) i).
Proof.
  intro Htp.
  do 30 (destruct tp as [|tp]; [unfold RC; shelve|]).
  lia.
  Unshelve.
  - solve_v1 4 14 1%nat 2.
  - solve_v1 5 14 8 4.
  - solve_v1 5 16 112 7.
  - solve_v1 10 14 1%nat 2.
  - solve_v1 11 14 8 4.
  - solve_v1 11 16 112 7.
  - solve_v1 18 6 3 2.
  - solve_v1 20 6 3 2.
  - solve_v1 18 20 1%nat 3.
  - solve_v1 20 18 8 4.
  - solve_v1 20 20 112 7.
  - solve_v1 24 14 56 6.
  - solve_v1 22 32 1%nat 5.
    solve_v2.
    solve_v2.
    solve_v3.
  - solve_v1 25 28 32 5.
  - solve_v1 26 28 128 7.
  - solve_v1 30 22 32 6.
  - solve_v1 32 20 64 7.
  - solve_v1 32 22 896 10.
  - solve_v1 38 20 1%nat 3.
  - solve_v1 40 18 8 4.
  - solve_v1 40 20 112 7.
  - solve_v1 44 14 56 6.
  - solve_v1 48 14 1%nat 2.
  - solve_v1 49 14 8 4.
  - solve_v1 49 16 112 7.
  - solve_v1 56 6 3 2.
  - solve_v1 58 6 3 2.
  - solve_v1 60 8 1%nat 1%nat.
  - solve_v1 60 10 14 4.
  - solve_v1 64 6 3 2.
Time Qed.

Definition S' '(tp,i) := 0inf {{{ (hR',R) }}} RC tp i.

Lemma BigStep tp i:
  tp<30 ->
  S' (tp,i) -->+ S' (S tp,i).
Proof.
  unfold S'.
  intro H.
  eapply RC_spec in H.
  eapply sideRLs_1 in H.
  follow10 H.
  remember (RC (S tp) i).
  er.
Qed.

Lemma S'_Ov i:
  S' (30,i) = S' (O,S i).
Proof.
  unfold S',RC.
  flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(tp,i) => tp<30).
  2: lia.
  intros [tp i] HP.
  assert (S tp<30\/tp=29) as [E|E] by lia.
  - eexists; split.
    1: apply BigStep,HP.
    cbn; lia.
  - eexists; split.
    + rewrite <-S'_Ov.
      rewrite E.
      apply BigStep; lia.
    + cbn; lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC1RE_1LD1RC_1LA0LF_---1RB_0LD1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (E,<[1;1]).

Notation h1 := [((C,[]),(D,[]))].
Notation h2 := [((C,[1]),(F,[0]))].
Notation h3 := [(hR',(D,[]))].

Lemma LIncs n:
  segRLs tm h3 (h3++h1^^(2^n-1)) (ld^^n) (ld^^n).
Proof.
  induction n.
  - rewrite app_nil_r.
    apply segRLs_nil.
  - replace (2^S n-1) with (2^n-1+2^n) by (cbn; lia).
    rewrite lpow_add,app_assoc.
    cbn[lpow].
    eapply segRLs_concat.
    2: eapply segRLs_trans.
    2: apply IHn.
    2: apply LBC_IncsOv; esc.
    esc.
Qed.

Lemma LIncs' k i r r' j j0:
  sideRLs tm (h3++h1^^(2^(i*60+k)-1)) (ld^^j*>r) (ld^^j0*>r') ->
  sideRLs tm h3 (ld^^(i*60+(k+j))*>r) (ld^^(i*60+(k+j0))*>r').
Proof.
  intro H.
  do 2 rewrite Nat.add_assoc.
  do 2 rewrite <-(lpow_add' ld (i*60+k)).
  eapply segRLs_sideRLs_concat.
  1: apply LIncs.
  apply H.
Qed.

Lemma MIncs n b a c r r':
  let w:=Str_firstn n r in
  let n':=2+n in
  let w':=Str_firstn n' r' in
  segRLs tm h3 (h2^^b) w w' ->
  segRLs tm h1 (h2^^(2^a)) w' w' ->
  sideRLs tm (h2^^(c*(2^a)+b)) (Str_nth_tl n r) (Str_nth_tl n' r') ->
  sideRLs tm (h3++h1^^c) (r) (r').
Proof.
  intros.
  rewrite (Str_firstn_spec n r).
  rewrite (Str_firstn_spec n' r').
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  rewrite Nat.add_comm,lpow_add.
  eapply segRLs_trans.
  1: apply H.
  applys_eq (@segRLs_wall'' tm h1 (h2^^(2^a)) w' c).
  2: apply H0.
  rewrite lpow_mul.
  reflexivity.
Qed.

Lemma RInc_d0 n r r':
  n mod 2 = 0%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d0*>r) (d0*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d1 n r r':
  n mod 2 = 0%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d1*>r) (d1*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d0_d1 n r r':
  n mod 2 = 1%nat ->
  sideRLs tm (h2^^(n/2)) r r' ->
  sideRLs tm (h2^^n) (d0*>r) (d1*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 1 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RInc_d1_d0 n r r':
  n mod 2 = 1%nat ->
  sideRLs tm (h2^^(n/2+1)) r r' ->
  sideRLs tm (h2^^n) (d1*>r) (d0*>r').
Proof.
  intros H H0.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  applys_eq (segRLs_addmul_v2 2 1 (n/2) 1 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d001_S i k r:
  d001^^(i+(S k))*>r =
  0>>0>>0>>0>>1>>0>>d001^^(i+k)*>r.
Proof.
  st; simpl_rotate; reflexivity.
Qed.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

Ltac RIncs :=
  repeat 
  ((eapply RInc_d0; [lia'|]) ||
  (eapply RInc_d1; [lia'|]) ||
  (eapply RInc_d0_d1; [lia'|]) ||
  (eapply RInc_d1_d0; [lia'|]); simpl_nat).

Lemma RIncs_001 i k k0:
  k0=k*3+2 ->
  sideRLs tm (h2 ^^ (2 ^ (i * 60 + k0) + 0)) (d001 ^^ (i * 20 + k) *> 0inf)
  (d001 ^^ (i * 20 + (S k)) *> 0inf).
Proof.
  intro; subst.
  remember (i*20+k) as n.
  replace (i*20+S k) with (n+1) by lia.
  replace (i*60+(k*3+2)) with (n*3+2) by lia.
  clear.
  induction n.
  - esc.
  - cbn[lpow Nat.add].
    do 2 rewrite (Str_app_assoc d001).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (segRLs_addmul_v2 8 1 (2^(n*3+2)) 0 0); unfold DH0.
    1,2: cbn; flia.
    1,2: esc.
Qed.

Ltac solve_v2 :=
  rewrite d001_S; RIncs; try rewrite <-d001_S.

Ltac solve_v3 :=
  apply RIncs_001; reflexivity.

Ltac solve_v1 a b c d :=
  apply (LIncs' a);
  apply (MIncs b c d); [esc|esc|cbn - [Nat.pow];
  cbn[Nat.pow]; rewrite Nat.mul_1_r;
  repeat rewrite Nat.mul_assoc;
  RIncs; try solve[solve_v3|solve_v2; solve_v3]].

Lemma RC_spec tp i:
  tp<30 ->
  sideRLs tm h3 (RC tp i) (RC (S tp) i).
Proof.
  intro Htp.
  do 30 (destruct tp as [|tp]; [unfold RC; shelve|]).
  lia.
  Unshelve.
  - solve_v1 4 14 1%nat 2.
  - solve_v1 5 14 8 4.
  - solve_v1 5 16 112 7.
  - solve_v1 10 14 1%nat 2.
  - solve_v1 11 14 8 4.
  - solve_v1 11 16 112 7.
  - solve_v1 18 6 3 2.
  - solve_v1 20 6 3 2.
  - solve_v1 18 20 1%nat 3.
  - solve_v1 20 18 8 4.
  - solve_v1 20 20 112 7.
  - solve_v1 24 14 56 6.
  - solve_v1 22 32 1%nat 5.
    solve_v2.
    solve_v2.
    solve_v3.
  - solve_v1 25 28 32 5.
  - solve_v1 26 28 128 7.
  - solve_v1 30 22 32 6.
  - solve_v1 32 20 64 7.
  - solve_v1 32 22 896 10.
  - solve_v1 38 20 1%nat 3.
  - solve_v1 40 18 8 4.
  - solve_v1 40 20 112 7.
  - solve_v1 44 14 56 6.
  - solve_v1 48 14 1%nat 2.
  - solve_v1 49 14 8 4.
  - solve_v1 49 16 112 7.
  - solve_v1 56 6 3 2.
  - solve_v1 58 6 3 2.
  - solve_v1 60 8 1%nat 1%nat.
  - solve_v1 60 10 14 4.
  - solve_v1 64 6 3 2.
Time Qed.

Definition S' '(tp,i) := 0inf {{{ (hR',R) }}} RC tp i.

Lemma BigStep tp i:
  tp<30 ->
  S' (tp,i) -->+ S' (S tp,i).
Proof.
  unfold S'.
  intro H.
  eapply RC_spec in H.
  eapply sideRLs_1 in H.
  follow10 H.
  remember (RC (S tp) i).
  er.
Qed.

Lemma S'_Ov i:
  S' (30,i) = S' (O,S i).
Proof.
  unfold S',RC.
  flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,O)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(tp,i) => tp<30).
  2: lia.
  intros [tp i] HP.
  assert (S tp<30\/tp=29) as [E|E] by lia.
  - eexists; split.
    1: apply BigStep,HP.
    cbn; lia.
  - eexists; split.
    + rewrite <-S'_Ov.
      rewrite E.
      apply BigStep; lia.
    + cbn; lia.
Qed.

End TM3.



From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Longitudinal.
From BusyCoq Require Import DivModCases.
From BusyCoq Require Import BinaryCounter_v2.


Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.


Ltac flia := repeat (lia || f_equal).

Fixpoint sideRL_rec(tm:TM)(l:list sym)(r:side)(q:Q)(T:nat) :=
match T with
| O => None
| S T =>
  match r with
  | m>>r =>
    match tm (q,m) with
    | Some (m,L,q) =>
      match l with
      | m'::l => sideRL_rec tm l (m'>>m>>r) q T
      | [] => Some (q,m>>r)
      end
    | Some (m,R,q) => sideRL_rec tm (m::l) r q T
    | None => None
    end
  end
end.

Lemma sideRL_rec_spec tm l r q T q' r':
  sideRL_rec tm l r q T = Some (q',r') ->
  (forall l0, l0 <* l {{q}}> r -[tm]->+ l0 <{{q'}} r').
Proof.
  gen l r q q' r'.
  induction T; cbn[sideRL_rec]; intros.
  1: congruence.
  destruct r as [m r].
  destruct (tm (q,m)) as [[[m0 []] q0]|] eqn:E.
  - destruct l as [|m' l].
    + inverts H.
      do 2 econstructor; apply E.
    + eapply progress_step.
      1: econstructor; apply E.
      cbn.
      eapply IHT in H.
      apply H.
  - eapply progress_step.
    1: econstructor; apply E.
    cbn.
    eapply IHT in H.
    apply H.
  - congruence.
Qed.

Import Eqb.

Fixpoint Str_firstn{A}(n:nat)(r:Stream A) :=
match n with
| O => []
| S n => hd r :: Str_firstn n (tl r)
end.

Lemma Str_firstn_spec{A} n (r:Stream A):
  r = Str_firstn n r *> Str_nth_tl n r.
Proof.
  gen r.
  induction n; intros; cbn.
  - trivial.
  - rewrite <-(IHn (tl r)).
    destruct r; trivial.
Qed.

Definition skip_prefix(r0:list sym)(r:side) :=
let len := List.length r0 in
if Eqb.eqb r0 (Str_firstn len r) then Some (Str_nth_tl len r) else None.

Lemma skip_prefix_spec r0 r r':
  skip_prefix r0 r = Some r' ->
  r = r0 *> r'.
Proof.
  unfold skip_prefix.
  intros.
  destruct (eqb_spec r0 (Str_firstn (List.length r0) r)).
  2: congruence.
  inverts H.
  epose proof (Str_firstn_spec (List.length r0) r) as I1.
  rewrite <-e in I1.
  apply I1.
Qed.

Definition sideRL_c tm '(QR,qR) '(QL,qL) r T :=
sideRL_rec tm qR r QR T &&& (fun '(q',r') =>
if Eqb.eqb QL q' then
skip_prefix qL r'
else None
).

Lemma sideRL_c_spec tm hR hL r r' T:
  sideRL_c tm hR hL r T = Some r' ->
  sideRL tm hR hL r r'.
Proof.
  unfold sideRL_c,if_Some.
  intros.
  destruct hR as [QR qR].
  destruct hL as [QL qL].
  destruct (sideRL_rec tm qR r QR T) as [[q' r'0]|] eqn:E.
  2: congruence.
  destruct (eqb_spec QL q'); [subst|congruence].
  apply skip_prefix_spec in H.
  subst.
  intro l.
  unfold to_DH_config.
  eapply sideRL_rec_spec in E.
  apply E.
Qed.

Definition divge(a b:N) :=
if N.leb b a then Some (N.div_eucl a b) else None.

Lemma divge_spec a b c d:
  divge a b = Some (c,d) ->
  (a = c*b+d)%N.
Proof.
  unfold divge.
  destruct (N.leb b a).
  2: congruence.
  intros.
  inverts H.
  epose proof (N.div_eucl_spec a b) as I1.
  rewrite H1 in I1.
  lia.
Qed.

Definition N_OS(n:N) :=
match n with
| N0 => None
| _ => Some (N.pred n)
end.

Lemma N_OS_spec n:
(match N_OS n with
| None => n=N0
| Some n0 => n=1+n0
end)%N.
Proof.
  unfold N_OS.
  destruct n; lia.
Qed.

Lemma sideRLs_trans_add tm h n1 n2 w1 w2 w3:
  sideRLs tm (h^^n1) w1 w3 ->
  sideRLs tm (h^^n2) w3 w2 ->
  sideRLs tm (h^^(n1+n2)) w1 w2.
Proof.
  intros.
  rewrite lpow_add.
  eapply sideRLs_trans; eassumption.
Qed.

Lemma segRLs_addmul_v2 a a' x b b' tm h w1 w2:
  segRLs tm (h^^b) (h^^b') w1 w2 ->
  segRLs tm (h^^a) (h^^a') w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^(x*a'+b')) w1 w2.
Proof.
  intros.
  rewrite (Nat.add_comm _ b).
  rewrite (Nat.add_comm _ b').
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  1: apply H.
  induction x; cbn[Nat.mul].
  - cbn.
    constructor.
  - cbn[lpow].
    do 2 rewrite lpow_add.
    eapply segRLs_trans.
    2: apply IHx.
    apply H0.
Qed.

Definition if_None {A} (a:option A) b :=
match a with
| None => b tt
| _ => a
end.

Notation "a ||| b" := (if_None a b) (at level 30, right associativity).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0LB_0RD1LB_1RA0RE_0LF1RD_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld0 := <[0;1].
Notation ld1 := <[1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [0;1;1].
Notation rd1x := [0;1;1;1;1].
Notation rd1xx := [0;1;1;1;1;1;1].
Notation rd1xxx := [0;1;1;1;1;1;1;1;1].

Notation hR := (D,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation "l <| r" := (l <{{B}} [] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{D}}> r) (at level 30).

Fixpoint nxt(n:N)(r:side)(d:nat) :=
match d with
| O => None
| S d =>
  (skip_prefix rd1xxx r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 11 &&& (fun '(n1,n2) =>
  nxt (n1*8) r d &&& (fun r => nxt n2 (rd1xxx*>r) d))))) |||
  (fun _ =>
  (skip_prefix rd1xx r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 8 &&& (fun '(n1,n2) =>
  nxt (n1*4) r d &&& (fun r => nxt n2 (rd1xx*>r) d))))) |||
  (fun _ =>
  (skip_prefix rd1x r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 5 &&& (fun '(n1,n2) =>
  nxt (n1*2) r d &&& (fun r => nxt n2 (rd1x*>r) d))))) |||
  (fun _ =>
  (skip_prefix rd1 r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 2 &&& (fun '(n1,n2) =>
  nxt (n1*1) r d &&& (fun r => nxt n2 (rd1*>r) d))))) |||
  (fun _ =>
  (match N_OS n with
  | Some n => sideRL_c tm hR hL r d &&& (fun r => nxt n r d)
  | None => Some r
  end)))))
end.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite Nnat.N2Nat.inj_add in * ||
  rewrite Nnat.N2Nat.inj_sub in * ||
  rewrite Nnat.N2Nat.inj_mul in * ||
  rewrite Nnat.N2Nat.inj_pow in * ||
  rewrite Nnat.N2Nat.id in * ||
  rewrite Nnat.Nat2N.id in *
  ).

Ltac des_if_None H :=
  cbn[if_None] in H;
  match type of H with
  | ?a ||| _ = _ =>
    destruct a eqn:E
  end.

Lemma nxt_spec n r d r':
  nxt n r d = Some r' ->
  sideRLs tm (hRL^^(N.to_nat n)) r r'.
Proof with try congruence.
  gen n r r'.
  induction d; cbn[nxt]; intros...
  unfold if_Some in H.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1xxx r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 11) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 8) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 11 8 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  clear E.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1xx r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 8) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 4) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 8 4 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  clear E.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1x r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 5) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 2) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 5 2 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  clear E.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1 r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 2) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 1) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 2 1 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  cbn[if_None] in H.
  epose proof (N_OS_spec n) as I1.
  destruct (N_OS n); subst n.
  - destruct (sideRL_c tm hR hL r d) eqn:E0...
    apply IHd in H.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply H.
    apply sideRL_c_spec in E0.
    econstructor.
    2: constructor.
    apply E0.
  - inverts H.
    constructor.
Qed.

Definition LC len n := BinDec ld0 ld1 len n 0inf.

Lemma LInc len n r:
  1+n<2^len ->
  LC len (n+1) <| r -->+
  LC len n |> r.
Proof.
  unfold LC.
  intros.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  rewrite (lowbit_split x i len) by lia.
  epose proof (lowbit_split_lt x i len).
  rw_Bin; solve_pow2_lt.
  remember (len-i-1) as len'.
  assert (x=2^len'-1\/x<2^len'-1) as [E|E] by lia.
  - subst x.
    rw_Bin.
    es.
  - lowbitS_cases x.
    rewrite (lowbit_split x0 i0 len') by lia.
    epose proof (lowbit_split_lt x0 i0 len').
    rw_Bin; solve_pow2_lt.
    es.
Qed.

Lemma LIncs len n:
  n<2^len ->
  sideRLs (flip tm) (hLR^^n) (LC len n) (LC len 0).
Proof.
  induction n; intros.
  - esx.
  - cbn[lpow].
    eapply sideRLs_trans.
    2: apply IHn; lia.
    econstructor.
    2: constructor.
    replace (S n) with (n+1) by lia.
    unfold sideRL; intros.
    epose proof (LInc _ _ _ H) as I1.
    apply flip_progress in I1.
    apply I1.
Qed.

Definition S0 len n (r:side) :=
  LC len (N.to_nat n) |> r.

Lemma Eat11 len n r:
  (n<2^(N.of_nat len))%N ->
  S0 len n (1>>1>>r) -->*
  S0 (S len) (n*2+1) r.
Proof.
  unfold S0,LC.
  intros.
  replace (S len) with (len+1) by lia.
  simpl_N_to_nat.
  rw_Bin; solve_pow2_lt.
  er.
Qed.

Lemma Eat10 len n r:
  (n<2^(N.of_nat len))%N ->
  S0 len n (1>>0>>r) -->*
  S0 (S len) (n*2) r.
Proof.
  unfold S0,LC.
  intros.
  replace (S len) with (len+1) by lia.
  simpl_N_to_nat.
  rw_Bin; solve_pow2_lt.
  er.
Qed.

Definition S1 len (r:side) :=
  LC len 0 <| r.

Lemma LOv len r:
  S1 len (0>>r) -->*
  S0 (S len) ((2^(N.of_nat len)-1)*2) r.
Proof.
  unfold S0,S1,LC.
  replace (S len) with (len+1) by lia.
  simpl_N_to_nat.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Definition maxT:nat := 1000.

Lemma BigStep len n r r':
  (n<2^(N.of_nat len))%N ->
  nxt (n+1) r maxT = Some r' ->
  S0 len n r -->*
  S1 len r'.
Proof.
  intros.
  eapply nxt_spec in H0.
  simpl_N_to_nat.
  unfold S0,S1.
  epose proof (sideRLs_concat) as I1.
  erewrite (lrcons_lpow1 _ _ (N.to_nat n + 1)) in I1 by lia.
  rewrite Nat.add_sub in I1.
  epose proof (I1 (LIncs _ _ _) H0) as I1.
  follow100 I1.
  finish.
  Unshelve.
  lia.
Qed.

Lemma Halt n0 len n r r':
  (n<2^(N.of_nat len))%N ->
  (n0<=n)%N ->
  nxt n0 r maxT = Some r' ->
  (forall l, halts tm (l |> r')) ->
  halts tm (S0 len n r).
Proof.
  intros.
  eapply nxt_spec in H1.
  epose proof (LIncs len (N.to_nat n) _) as I2.
  replace (N.to_nat n) with (N.to_nat n0+(N.to_nat (n-n0))) in I2 by lia.
  rewrite lpow_add in I2.
  eapply sideRLs_split in I2.
  destruct I2 as [r3 [I2a I2b]].
  epose proof (sideRLs_concat_1 H1 I2a) as I1.
  eapply halts_evstep.
  2:{
    unfold S0.
    applys_eq I1.
    unfold to_DH_config.
    flia.
  }
  apply H2.
  Unshelve.
  lia.
Qed.

Ltac crefl := vm_compute; reflexivity.

Ltac mstep :=
match goal with
| |- S1 _ _ -->* _ => follow LOv
| |- S0 _ _ (1>>1>>_) -->* _ => follow Eat11; [crefl|] 
| |- S0 _ _ (1>>0>>_) -->* _ => follow Eat10; [crefl|] 
| |- S0 _ _ (0>>_) -->* _ => follow BigStep; [crefl|crefl|]
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep with (c':=S1 2 (rd1^^2*>0inf)).
  2: unfold S1; esx.
  eapply halts_evstep.
  2:{
    cbn.
    do 158 mstep.
    finish.
  }
  eapply (Halt 2).
  1: crefl.
  1: vm_compute; congruence.
  1: crefl.
  esx.
Time Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0LA_0RC1LA_1RF0RD_0LE1RC_1RB---_1RA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld0 := <[0;1].
Notation ld1 := <[1;0].
Notation rd0 := [0;0;0].
Notation rd1 := [0;1;1].
Notation rd1x := [0;1;1;1;1].
Notation rd1xx := [0;1;1;1;1;1;1].
Notation rd1xxx := [0;1;1;1;1;1;1;1;1].
Notation rd1xxxx := [0;1;1;1;1;1;1;1;1;1;1].

Notation hR := (C,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation "l <| r" := (l <{{A}} [] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{C}}> r) (at level 30).

Fixpoint nxt(n:N)(r:side)(d:nat) :=
match d with
| O => None
| S d =>
  (skip_prefix rd1xxxx r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 14 &&& (fun '(n1,n2) =>
  nxt (n1*16) r d &&& (fun r => nxt n2 (rd1xxxx*>r) d))))) |||
  (fun _ =>
  (skip_prefix rd1xxx r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 11 &&& (fun '(n1,n2) =>
  nxt (n1*8) r d &&& (fun r => nxt n2 (rd1xxx*>r) d))))) |||
  (fun _ =>
  (skip_prefix rd1xx r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 8 &&& (fun '(n1,n2) =>
  nxt (n1*4) r d &&& (fun r => nxt n2 (rd1xx*>r) d))))) |||
  (fun _ =>
  (skip_prefix rd1x r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 5 &&& (fun '(n1,n2) =>
  nxt (n1*2) r d &&& (fun r => nxt n2 (rd1x*>r) d))))) |||
  (fun _ =>
  (skip_prefix rd1 r &&& (fun r =>
  skip_prefix [0] r &&& (fun _ =>
  divge n 2 &&& (fun '(n1,n2) =>
  nxt (n1*1) r d &&& (fun r => nxt n2 (rd1*>r) d))))) |||
  (fun _ =>
  (match N_OS n with
  | Some n => sideRL_c tm hR hL r d &&& (fun r => nxt n r d)
  | None => Some r
  end))))))
end.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite Nnat.N2Nat.inj_add in * ||
  rewrite Nnat.N2Nat.inj_sub in * ||
  rewrite Nnat.N2Nat.inj_mul in * ||
  rewrite Nnat.N2Nat.inj_pow in * ||
  rewrite Nnat.N2Nat.id in * ||
  rewrite Nnat.Nat2N.id in *
  ).

Ltac des_if_None H :=
  cbn[if_None] in H;
  match type of H with
  | ?a ||| _ = _ =>
    destruct a eqn:E
  end.

Lemma nxt_spec n r d r':
  nxt n r d = Some r' ->
  sideRLs tm (hRL^^(N.to_nat n)) r r'.
Proof with try congruence.
  gen n r r'.
  induction d; cbn[nxt]; intros...
  unfold if_Some in H.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1xxxx r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 14) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 16) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 14 16 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  clear E.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1xxx r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 11) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 8) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 11 8 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  clear E.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1xx r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 8) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 4) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 8 4 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  clear E.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1x r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 5) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 2) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 5 2 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  clear E.
  des_if_None H.
  {
    inverts H.
    destruct (skip_prefix rd1 r) eqn:E0...
    destruct (skip_prefix [0] s) eqn:E1...
    destruct (divge n 2) as [[n1 n2]|] eqn:E2...
    destruct (nxt (n1 * 1) s d) eqn:E3...
    apply divge_spec in E2.
    apply skip_prefix_spec in E0.
    subst.
    apply IHd in E,E3.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply E.
    eapply segRLs_sideRLs_concat.
    2: apply E3.
    applys_eq (segRLs_addmul_v2 2 1 (N.to_nat n1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
  }
  cbn[if_None] in H.
  epose proof (N_OS_spec n) as I1.
  destruct (N_OS n); subst n.
  - destruct (sideRL_c tm hR hL r d) eqn:E0...
    apply IHd in H.
    simpl_N_to_nat.
    eapply sideRLs_trans_add.
    2: apply H.
    apply sideRL_c_spec in E0.
    econstructor.
    2: constructor.
    apply E0.
  - inverts H.
    constructor.
Qed.

Definition LC len n := BinDec ld0 ld1 len n 0inf.

Lemma LInc len n r:
  1+n<2^len ->
  LC len (n+1) <| r -->+
  LC len n |> r.
Proof.
  unfold LC.
  intros.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  rewrite (lowbit_split x i len) by lia.
  epose proof (lowbit_split_lt x i len).
  rw_Bin; solve_pow2_lt.
  remember (len-i-1) as len'.
  assert (x=2^len'-1\/x<2^len'-1) as [E|E] by lia.
  - subst x.
    rw_Bin.
    es.
  - lowbitS_cases x.
    rewrite (lowbit_split x0 i0 len') by lia.
    epose proof (lowbit_split_lt x0 i0 len').
    rw_Bin; solve_pow2_lt.
    es.
Qed.

Lemma LIncs len n:
  n<2^len ->
  sideRLs (flip tm) (hLR^^n) (LC len n) (LC len 0).
Proof.
  induction n; intros.
  - esx.
  - cbn[lpow].
    eapply sideRLs_trans.
    2: apply IHn; lia.
    econstructor.
    2: constructor.
    replace (S n) with (n+1) by lia.
    unfold sideRL; intros.
    epose proof (LInc _ _ _ H) as I1.
    apply flip_progress in I1.
    apply I1.
Qed.

Definition S0 len n (r:side) :=
  LC len (N.to_nat n) |> r.

Lemma Eat11 len n r:
  (n<2^(N.of_nat len))%N ->
  S0 len n (1>>1>>r) -->*
  S0 (S len) (n*2+1) r.
Proof.
  unfold S0,LC.
  intros.
  replace (S len) with (len+1) by lia.
  simpl_N_to_nat.
  rw_Bin; solve_pow2_lt.
  er.
Qed.

Lemma Eat10 len n r:
  (n<2^(N.of_nat len))%N ->
  S0 len n (1>>0>>r) -->*
  S0 (S len) (n*2) r.
Proof.
  unfold S0,LC.
  intros.
  replace (S len) with (len+1) by lia.
  simpl_N_to_nat.
  rw_Bin; solve_pow2_lt.
  er.
Qed.

Definition S1 len (r:side) :=
  LC len 0 <| r.

Lemma LOv len r:
  S1 len (0>>r) -->*
  S0 (S len) ((2^(N.of_nat len)-1)*2) r.
Proof.
  unfold S0,S1,LC.
  replace (S len) with (len+1) by lia.
  simpl_N_to_nat.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Definition maxT:nat := 1000.

Lemma BigStep len n r r':
  (n<2^(N.of_nat len))%N ->
  nxt (n+1) r maxT = Some r' ->
  S0 len n r -->*
  S1 len r'.
Proof.
  intros.
  eapply nxt_spec in H0.
  simpl_N_to_nat.
  unfold S0,S1.
  epose proof (sideRLs_concat) as I1.
  erewrite (lrcons_lpow1 _ _ (N.to_nat n + 1)) in I1 by lia.
  rewrite Nat.add_sub in I1.
  epose proof (I1 (LIncs _ _ _) H0) as I1.
  follow100 I1.
  finish.
  Unshelve.
  lia.
Qed.

Lemma Halt n0 len n r r':
  (n<2^(N.of_nat len))%N ->
  (n0<=n)%N ->
  nxt n0 r maxT = Some r' ->
  (forall l, halts tm (l |> r')) ->
  halts tm (S0 len n r).
Proof.
  intros.
  eapply nxt_spec in H1.
  epose proof (LIncs len (N.to_nat n) _) as I2.
  replace (N.to_nat n) with (N.to_nat n0+(N.to_nat (n-n0))) in I2 by lia.
  rewrite lpow_add in I2.
  eapply sideRLs_split in I2.
  destruct I2 as [r3 [I2a I2b]].
  epose proof (sideRLs_concat_1 H1 I2a) as I1.
  eapply halts_evstep.
  2:{
    unfold S0.
    applys_eq I1.
    unfold to_DH_config.
    flia.
  }
  apply H2.
  Unshelve.
  lia.
Qed.

Ltac crefl := vm_compute; reflexivity.

Ltac mstep :=
match goal with
| |- S1 _ _ -->* _ => follow LOv
| |- S0 _ _ (1>>1>>_) -->* _ => follow Eat11; [crefl|] 
| |- S0 _ _ (1>>0>>_) -->* _ => follow Eat10; [crefl|] 
| |- S0 _ _ (0>>_) -->* _ => follow BigStep; [crefl|crefl|]
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep with (c':=S1 3 (rd0*>rd1^^2*>0inf)).
  2: unfold S1; esx.
  eapply halts_evstep.
  2:{
    cbn.
    do 169 mstep.
    finish.
  }
  eapply (Halt 3).
  1: crefl.
  1: vm_compute; congruence.
  1: crefl.
  esx.
Time Qed.

End TM2.


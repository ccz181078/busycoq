From BusyCoq Require Import Individual25 DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

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


Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB4LA1LB2LA0RB_2LB3RB4LA---1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[]).
Notation hR' := (A,<[1]).
Notation hL := (A,[]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].

Notation ld := [4;4].
Notation d0 := [2;2].
Notation d1 := [4;2].

Lemma ld_Incs k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d00_Incs k:
  segRLs tm (h^^(k*2)) (h^^k) d0 d0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d01_Incs k:
  segRLs tm (h^^(1+k*2)) (h^^k) d0 d1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 1 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Notation rh := ([4;2;4]*>0inf).

Inductive RD := D0|D1|LD.

Fixpoint toRC ls :=
match ls with
| [] => rh
| D0::t => d0 *> toRC t
| D1::t => d1 *> toRC t
| LD::t => ld *> toRC t
end.

Inductive RC: nat->(list RD)->Prop :=
| RC_0: RC O []
| RC_1 k r: RC k r -> RC (1+k*2) (D0::r)
| RC_2 k r: RC k r -> RC (2+k*2) (D1::r).

Ltac ec := econstructor.

Lemma RC_ex k:
  exists r, RC k r.
Proof.
  induction k using lt_wf_ind; intros.
  destruct (mod2 k); subst.
  - destruct a.
    + ec; ec.
    + unshelve epose proof (H a _) as [r I1].
      1: lia.
      ec; ec; apply I1.
  - unshelve epose proof (H a _) as [r I1].
    1: lia.
    ec; ec; apply I1.
Qed.

Lemma RC_spec k r:
  RC k r ->
  sideRLs tm (h^^k) rh (toRC r).
Proof.
  gen r.
  induction k using lt_wf_ind; intros.
  assert ((k=0 \/ k=1+k/2*2 \/ k=2+(k/2-1)*2)%nat) as [E|[E|E]] by lia.
  - subst.
    inverts H0.
    esc.
  - inverts H0; try lia.
    rewrite lpow_add.
    eapply @sideRLs_trans with (r2:=d0*>rh).
    1: esc.
    eapply segRLs_sideRLs_concat.
    1: apply d00_Incs.
    eapply H; eauto 1; lia.
  - inverts H0; try lia.
    change (2+k0*2) with (1+(1+k0*2)).
    rewrite lpow_add.
    eapply @sideRLs_trans with (r2:=d0*>rh).
    1: esc.
    eapply segRLs_sideRLs_concat.
    1: apply d01_Incs.
    eapply H; eauto 1; lia.
Qed.

Inductive RIncs: nat->(list RD)->(list RD)->Prop :=
| RIncs_O k r:
  RC (k*4) r ->
  RIncs (1+k) [] (LD::LD::r)
| RIncs_ld k r r':
  RIncs (1+k*2) r r' ->
  RIncs k (LD::r) (LD::r')
| RIncs_d1 k r r':
  RIncs (k*2) r r' ->
  RIncs k (D1::r) (LD::r')
| RIncs_d00 k r r':
  RIncs k r r' ->
  RIncs (2+k*2) (D0::r) (D0::r')
| RIncs_d01 k r r':
  RIncs k r r' ->
  RIncs (3+k*2) (D0::r) (D1::r')
.

Lemma RIncs_spec k r r':
  RIncs k r r' ->
  sideRLs tm (h'++h^^k) (toRC r) (toRC r').
Proof.
  intro H.
  induction H.
  { rewrite lpow_add,app_assoc.
    apply RC_spec in H.
    eapply @sideRLs_trans with (r2:=ld*>ld*>rh).
    1: esc.
    eapply segRLs_sideRLs_concat.
    1: apply ld_Incs.
    eapply segRLs_sideRLs_concat.
    1: apply ld_Incs.
    applys_eq H; flia. }
  { eapply segRLs_sideRLs_concat; [|apply IHRIncs].
    rewrite lpow_add,app_assoc.
    eapply segRLs_trans.
    2: apply ld_Incs.
    esc. }
  { eapply segRLs_sideRLs_concat; [|apply IHRIncs].
    eapply segRLs_trans.
    2: apply ld_Incs.
    esc. }
  { eapply segRLs_sideRLs_concat; [|apply IHRIncs].
    rewrite lpow_add,app_assoc.
    eapply segRLs_trans.
    2: apply d00_Incs.
    esc. }
  { eapply segRLs_sideRLs_concat; [|apply IHRIncs].
    change (3+k*2) with (2+(1+k*2)).
    rewrite lpow_add,app_assoc.
    eapply segRLs_trans.
    2: apply d01_Incs.
    esc. }
Qed.

Inductive full: nat->Prop :=
| full_O: full 0
| full_S k: full k -> full (1+k*2).

Inductive notfull: nat->Prop :=
| notfull_0 k: full k -> notfull (2+k*2)
| notfull_1 k: notfull k -> notfull (1+k*2)
| notfull_2 k: notfull k -> notfull (2+k*2)
.

Lemma notfull_ge2 [k]:
  notfull k ->
  2<=k.
Proof.
  intro H.
  induction H; lia.
Qed.

Lemma RC_RIncs_full [k r k']:
  RC k r ->
  1+k*3<=k' ->
  full k ->
  exists r', RIncs k' r r'.
Proof.
  intro H.
  gen k'.
  induction H; intros.
  - destruct (sub k' 1); [subst|lia].
    epose proof (RC_ex _) as [r I1].
    ec; ec; apply I1.
  - inverts H1.
    replace k0 with k in * by lia.
    destruct (sub k' 2); [subst|lia].
    destruct (mod2 c); subst.
    + epose proof (IHRC a _ H3) as [r' I1].
      ec; ec; apply I1.
    + epose proof (IHRC a _ H3) as [r' I1].
      ec; ec; apply I1.
  - inverts H1; lia.
  Unshelve. all: lia.
Qed.


Lemma RC_RIncs_notfull [k r k']:
  RC k r ->
  k<=1+k' ->
  notfull k ->
  exists r', RIncs k' r r'.
Proof.
  intro H.
  gen k'.
  induction H; intros.
  - inverts H0.
  - inverts H1; try lia.
    replace k0 with k in * by lia.
    epose proof (notfull_ge2 H3).
    destruct (sub k' 2); [subst|lia].
    destruct (mod2 c); subst.
    + epose proof (IHRC a _ H3) as [r' I1].
      ec; ec; apply I1.
    + epose proof (IHRC a _ H3) as [r' I1].
      ec; ec; apply I1.
  - inverts H1; try lia.
    + replace k0 with k in * by lia.
      eapply (RC_RIncs_full) with (k':=k'*2) in H; eauto 1.
      2: lia.
      destruct H as [r' I1].
      ec; ec; apply I1.
    + replace k0 with k in * by lia.
      epose proof (IHRC (k'*2) _ H3) as [r' I1].
      ec; ec; apply I1.
  Unshelve. all: lia.
Qed.

Lemma RC_full_cases [k r]:
  RC k r ->
  full k \/ notfull k.
Proof.
  intro H.
  induction H.
  - left; ec.
  - destruct IHRC as [I|I]; (left+right); ec; apply I.
  - destruct IHRC as [I|I]; (left+right); ec; apply I.
Qed.

Lemma RIncs_nxt k r r':
  RIncs k r r' ->
  forall k',
  k<=k' ->
  exists r'',
  RIncs k' r' r''.
Proof.
  intros H.
  induction H; intros. 
  - destruct (RC_full_cases H) as [I|I].
    + pose proof I as I0.
      inverts I0; try lia.
      epose proof (RC_RIncs_full H _ I) as [r' I1].
      do 3 ec; apply I1.
    + epose proof (RC_RIncs_notfull H _ I) as [r' I1].
      do 3 ec; apply I1.
  - epose proof (IHRIncs (1+k'*2) _) as [r'' I1].
    ec; ec; apply I1.
  - epose proof (IHRIncs (1+k'*2) _) as [r'' I1].
    ec; ec; apply I1.
  - destruct (sub k' 2); [subst|lia].
    destruct (mod2 c); subst.
    + epose proof (IHRIncs a _) as [r'' I1].
      ec; ec; apply I1.
    + epose proof (IHRIncs a _) as [r'' I1].
      ec; ec; apply I1.
  - epose proof (IHRIncs (k'*2) _) as [r'' I1].
    ec; ec; apply I1.
  Unshelve. all: try lia.
Qed.

Notation lh := (0inf<*[1]).
Definition S' r := lh {{{ (hR',R) }}} toRC r.

Lemma BigStep r r':
  RIncs 0 r r' ->
  S' r -->+
  S' r'.
Proof.
  intro H.
  apply RIncs_spec in H.
  unfold S'.
  epose proof (sideRLs_concat (sideRLseq_O _ _) H) as I1.
  follow10 I1.
  er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [LD;LD;LD;D1;D1]).
  1: er.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs 0 r r').
  2:{
    epose proof (RC_ex _) as [r' I1].
    eexists.
    do 6 ec; apply I1.
  }
  intros r [r' I1].
  exists r'; split.
  - apply BigStep,I1.
  - eapply RIncs_nxt; eauto 1.
Qed.

End TM1.


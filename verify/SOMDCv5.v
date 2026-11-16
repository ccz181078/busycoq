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


Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC0RA_1RD0RB_0LE1LF_---1LF_1RB1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[1]).
Notation hL := (F,[1]).
Notation h := [(hR,hL)].

Notation ld := [1;1;0;1;1].
Notation ld' := [1;0;1;1;1].
Notation d0 := [0;1;1].
Notation d1 := [1;1;1].
Notation w1011 := [1;0;1;1].
Notation w11 := [1;1].
Notation lh := (0inf<*<[1;1]).
Notation rh := (ld*>0inf).
Notation dw := (ld++d1^^2++ld++d1++ld^^3++d1^^2++ld++d1^^3).
Notation du := (d1^^2++d0^^2).


Lemma w11_d0 r:
  w11*>d0*>r = ld*>r.
Proof. trivial. Qed.

Lemma w11_d1 r:
  w11*>d1*>r = d1*>w11*>r.
Proof. trivial. Qed.

Lemma w11_ld r:
  w11*>ld*>r = d1*>w1011*>r.
Proof. trivial. Qed.

Lemma w1011_d1 r:
  w1011*>d1*>r = ld'*>w11*>r.
Proof. trivial. Qed.

Lemma w1011_ld r:
  w1011*>ld*>r = ld'*>w1011*>r.
Proof. trivial. Qed.

Lemma w11_lds a b r:
  w11*>ld^^(a+S b)*>r =
  d1*>ld'^^(a+b)*>w1011*>r.
Proof.
  st; simpl_rotate; trivial.
Qed.

Lemma w11_lds' b r:
  w11*>ld^^(S b)*>r =
  d1*>ld'^^(b)*>w1011*>r.
Proof.
  st; simpl_rotate; trivial.
Qed.

Notation dw' := (ld'++d1^^2++ld'++d1++ld'^^3++d1^^2++ld'++d1^^3).

Lemma w11_dws n r:
  w11 *> dw^^n *> ld *> r = d1 *> dw'^^n *> w1011 *> r.
Proof.
  st; simpl_rotate; trivial.
Qed.

Ltac rw_rot :=
  repeat (
  rewrite w11_d0 ||
  rewrite w11_d1 ||
  rewrite w11_ld ||
  rewrite w11_lds ||
  rewrite w11_lds' ||
  rewrite w11_dws ||
  rewrite w1011_d1 ||
  rewrite w1011_ld).


Definition RC tp i :=
match tp with
| O => ld*>d1*>d0*>ld^^(i*6+8)*>d1*>ld^^4*>d1*>dw^^i*>ld*>d1*>ld^^2*>d0*>d1^^3*>ld*>d1*>d0*>ld*>d1*>d0*>d1*>d0*>du^^(i+1)*>rh
| 1%nat => ld*>d1*>ld^^(i*6+9)*>d1*>ld^^4*>d1*>dw^^i*>ld*>d1*>ld^^2*>d0*>d1^^3*>ld*>d1*>d0*>ld*>d1*>d0*>d1*>d0*>du^^(i+1)*>d1*>rh
| 2 => ld*>d1*>d0*>ld^^(i*6+9)*>d1*>ld^^4*>d1*>dw^^i*>ld*>d1^^2*>ld^^3*>d0*>ld*>d1^^2*>ld*>d1*>d0*>d1*>d0*>du^^(i+2)*>rh
| 3 => ld*>d1*>ld^^(i*6+10)*>d1*>ld^^4*>d1*>dw^^i*>ld*>d1^^2*>ld^^3*>d0*>ld*>d1^^2*>ld*>d1*>d0*>d1*>d0*>du^^(i+2)*>d1*>rh
| 4 => ld*>d1*>d0*>ld^^(i*6+10)*>d1*>ld^^4*>d1*>dw^^i*>ld*>d1^^2*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>du^^(i+3)*>rh
| 5 => ld*>d1*>ld^^(i*6+11)*>d1*>ld^^4*>d1*>dw^^i*>ld*>d1^^2*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>du^^(i+3)*>d1*>rh
| 6 => ld*>d1*>d0*>ld^^(i*6+11)*>d1*>ld^^4*>d1*>dw^^i*>ld*>d1^^2*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>d1*>ld*>d0*>du^^(i+3)*>rh
| 7 => ld*>d1*>ld^^(i*6+12)*>d1*>ld^^4*>d1*>dw^^i*>ld*>d1^^2*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>d1*>ld*>d0*>du^^(i+3)*>d1*>rh
| 8 => ld*>d1*>d0*>ld^^(i*6+12)*>d1*>ld^^4*>d1*>dw^^(i+1)*>ld*>d1*>ld^^2*>d1*>d0^^3*>d1*>d0*>du^^(i+2)*>rh
| 9 => ld*>d1*>ld^^(i*6+13)*>d1*>ld^^4*>d1*>dw^^(i+1)*>ld*>d1*>ld^^2*>d1*>d0^^3*>d1*>d0*>du^^(i+2)*>d1*>rh
| 10 => ld*>d1*>d0*>ld^^(i*6+13)*>d1*>ld^^4*>d1*>dw^^(i+1)*>ld*>d1*>ld^^3*>d0^^2*>d1*>d0*>du^^(i+3)*>rh
| 11 => ld*>d1*>ld^^(i*6+14)*>d1*>ld^^4*>d1*>dw^^(i+1)*>ld*>d1*>ld^^3*>d0^^2*>d1*>d0*>du^^(i+3)*>d1*>rh
| _ => ld*>d1*>d0*>ld^^(i*6+14)*>d1*>ld^^4*>d1*>dw^^(i+1)*>ld*>d1*>ld^^2*>d0*>d1^^3*>ld*>d1*>d0*>ld*>d1*>d0*>d1*>d0*>du^^(i+2)*>rh
end.

Lemma LRst r:
  lh {{{ (hL,L) }}} ld*>r -->*
  lh {{{ (hR,R) }}} ld'*>w11*>r.
Proof.
  es.
Qed.

Lemma ld_Incs k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld'_Incs k:
  k<>O ->
  segRLs tm (h^^k) (h^^(k*2)) ld' ld.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 1 2 (k-1) 1 2); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld's_Incs k n:
  k<>O ->
  segRLs tm (h^^k) (h^^(k*2^n)) (ld'^^n) (ld^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    eapply segRLs_concat.
    1: apply ld'_Incs; lia.
    applys_eq (IHn (k*2)); flia.
Qed.

Lemma lds_Incs k n:
  segRLs tm (h^^k) (h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    eapply segRLs_concat.
    1: apply ld_Incs; lia.
    applys_eq (IHn (k*2)); flia.
Qed.

Lemma d0_Incs k:
  k mod 2 = O ->
  segRLs tm (h^^k) (h^^(k/2)) d0 d0.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 2 1 (k/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d0_Incs' k:
  k mod 2 <> O ->
  segRLs tm (h^^k) (h^^(k/2)) d0 d1.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 2 1 (k/2) 1 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d1_Incs k:
  k mod 2 = O ->
  segRLs tm (h^^k) (h^^(k/2)) d1 d1.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 2 1 (k/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld's_Incs' v1 a b b' c r r':
  v1 = 1%nat ->
  b+c = b' ->
  sideRLs tm (h^^(2^(a+b)+0)) r (ld^^c*>r') ->
  sideRLs tm (h^^v1) (ld'^^(a+b)*>r) (ld^^(a+b')*>r').
Proof.
  rewrite Nat.add_0_r.
  intros.
  subst.
  replace (a+(b+c)) with (a+b+c) by lia.
  rewrite <-(lpow_add' _ _ c).
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  applys_eq ld's_Incs; flia.
Qed.

Lemma lds_Incs' v1 a b b' c r r':
  v1 = 1%nat ->
  1+b+c = b' ->
  sideRLs tm (h^^(2^(a+(S b))+0)) r (ld^^c*>r') ->
  sideRLs tm (h^^v1) (ld*>ld^^(a+b)*>r) (ld^^(a+b')*>r').
Proof.
  rewrite Nat.add_0_r.
  intros.
  subst.
  change (ld*>ld^^(a+b)*>r) with (ld^^(1+a+b)*>r).
  replace (a+(1+b+c)) with (1+a+b+c) by lia.
  rewrite <-(lpow_add' _ _ c).
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  applys_eq lds_Incs.
  rewrite Nat.mul_1_l; flia.
Qed.

Lemma d1_Incs' k:
  k mod 2 <> O ->
  segRLs tm (h^^k) (h^^(k/2+1)) d1 d0.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 2 1 (k/2) 1 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma dw_Incs k:
  segRLs tm (h^^(k*4)) (h^^k) dw dw.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 4 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma dw'_Incs k:
  k<>O ->
  segRLs tm (h^^(k*4)) (h^^k) dw' dw.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 4 1 (k-1) 4 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma dws_Incs k n:
  segRLs tm (h^^(k*2^(n*2))) (h^^k) (dw^^n) (dw^^n).
Proof.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul Nat.pow].
    eapply segRLs_concat.
    2: apply IHn; lia.
    rw_pa.
    applys_eq (dw_Incs (k*2^(n*2))); flia.
Qed.

Lemma dw's_Incs k n:
  k<>O ->
  segRLs tm (h^^(k*2^(n*2))) (h^^k) (dw'^^n) (dw^^n).
Proof.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul Nat.pow].
    eapply segRLs_concat.
    2: apply IHn; lia.
    rw_pa.
    applys_eq (dw'_Incs (k*2^(n*2))); flia.
Qed.

Lemma dws_Incs' i a b b' b0 c r r':
  b+b0=b' ->
  b*2+c=a ->
  sideRLs tm (h^^(2^(i*4+c)+0)) r (dw^^b0*>r') ->
  sideRLs tm (h^^(2^(i*6+a)+0)) (dw^^(i+b)*>r) (dw^^(i+b')*>r').
Proof.
  intros.
  subst b'.
  rewrite Nat.add_assoc.
  rewrite <-(lpow_add' _ _ b0).
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  replace (i*6+a) with (i*4+c+(i+b)*2) by lia.
  applys_eq (dws_Incs (2^(i*4+c)) (i+b)); rw_pa; flia.
Qed.

Lemma dw's_Incs' i a b b' b0 c r r':
  b+b0=b' ->
  b*2+c=a ->
  sideRLs tm (h^^(2^(i*4+c)+0)) r (dw^^b0*>r') ->
  sideRLs tm (h^^(2^(i*6+a)+0)) (dw'^^(i+b)*>r) (dw^^(i+b')*>r').
Proof.
  intros.
  subst b'.
  rewrite Nat.add_assoc.
  rewrite <-(lpow_add' _ _ b0).
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  replace (i*6+a) with (i*4+c+(i+b)*2) by lia.
  applys_eq (dw's_Incs (2^(i*4+c)) (i+b)); rw_pa; flia.
Qed.

Lemma lpow_0_Str_app a (r:side):
  a^^0*>r = r.
Proof.
  trivial.
Qed.

Lemma lpow_S_Str_app w a (r:side):
  w^^(S a)*>r =
  w*>w^^a*>r.
Proof.
  st; tauto.
Qed.

Lemma du_Incs k:
  segRLs tm (h^^(k*16)) (h^^k) du du.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 16 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma dus_Incs k n:
  segRLs tm (h^^(k*2^(n*4))) (h^^k) (du^^n) (du^^n).
Proof.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul Nat.pow].
    eapply segRLs_concat.
    2: apply IHn; lia.
    rw_pa.
    applys_eq (du_Incs (k*2^(n*4))); flia.
Qed.


Lemma dus_Incs'1 i a a0:
  a0 = 1+a*4 ->
  sideRLs tm (h ^^ (2 ^ (i * 4 + a0) + 0)) (du ^^ (i + a) *> rh) (du ^^ (i + a) *> d1 *> rh).
Proof.
  intros.
  subst a0.
  replace (i*4+(1+a*4)) with (1+(i+a)*4) by lia.
  remember (i+a) as n.
  clear Heqn i a.
  rw_pa.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: apply dus_Incs.
  esc.
Qed.

Lemma dus_Incs'4 i a a0:
  a0 = 4+a*4 ->
  sideRLs tm (h ^^ (2 ^ (i * 4 + a0) + 0)) (du ^^ (i + a) *> d1 *> rh) (du ^^ (i + (S a)) *> rh).
Proof.
  intros.
  subst a0.
  replace (i*4+(4+a*4)) with (4+(i+a)*4) by lia.
  replace (i+S a) with (i+a+1) by lia.
  remember (i+a) as n.
  clear Heqn i a.
  rewrite <-lpow_add'.
  rw_pa.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: apply dus_Incs.
  esc.
Qed.

Lemma sideRLs_tr1 a r r' r0:
  sideRLs tm (h) r r0 ->
  sideRLs tm (h^^(2^a-1)) r0 r' ->
  sideRLs tm (h^^(2^a+0)) r r'.
Proof.
  intros.
  replace (2^a+0) with (1+(2^a-1)) by lia.
  eapply sideRLs_trans_add; eauto 1.
Qed.

Lemma dus_S b a r:
  du^^(a+S b)*>r=
  d1*>d1*>d0*>d0*>du^^(a+b)*>r.
Proof.
  st; simpl_rotate; trivial.
Qed.

Ltac ssc :=
  (eapply segRLs_sideRLs_concat; [(apply ld_Incs || apply ld'_Incs || apply d1_Incs || apply d1_Incs' || apply d0_Incs || apply d0_Incs'); rw_pa; lia|]) ||
  ((eapply lds_Incs'||eapply ld's_Incs'||eapply dws_Incs'||eapply dw's_Incs'); [reflexivity|reflexivity|]) ||
  rewrite lpow_0_Str_app ||
  rewrite lpow_S_Str_app ||
  ((apply dus_Incs'1 || apply dus_Incs'4); reflexivity).

Ltac sscs := repeat (ssc; simpl_nat).

Definition S' '(tp,i) :=
  lh {{{ (hL,L) }}} RC tp i.

Lemma RC_spec tp i:
  tp<12 ->
  S' (tp,i) -->+
  S' (S tp,i).
Proof.
  unfold S',RC.
  intros.
  do 12 (destruct tp as [|tp]; [shelve|]).
  lia.
  Unshelve.
  all: follow LRst; eapply sideRLs_1.
  all: change h with (h^^1).
  all: replace (dw^^i) with (dw^^(i+0)) by flia.
  { rw_rot. sscs. }
  { rw_rot. sscs.
    eapply sideRLs_tr1 with (r0:=d0*>ld^^3*>d0*>ld*>d1^^2*>ld*>d1*>d0^^2*>d1*>du^^(i+1)*>d1*>rh).
    1: esc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    rewrite (dus_S 1).
    rewrite (dus_S 2).
    eapply sideRLs_tr1 with (r0:=ld*>d1*>d0*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>d1*>d0*>d1*>d0*>du^^(i+1)*>d1*>rh).
    1: esc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    rewrite (dus_S 2).
    rewrite (dus_S 1).
    rewrite (dus_S 2).
    eapply sideRLs_tr1 with (r0:=ld*>d1*>d0*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>d1*>ld*>d0^^3*>d1*>d0*>du^^(i+1)*>d1*>rh).
    1: esc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    rewrite (dus_S 2).
    rewrite (dus_S 1).
    eapply sideRLs_tr1 with (r0:=ld*>d1*>d0*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>d0*>ld*>d1*>ld^^2*>d1*>d0*>d1*>d0*>d1*>d0*>du^^(i+1)*>d1*>rh).
    1: esc.
    repeat rewrite Str_app_assoc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    eapply sideRLs_tr1 with (r0:=ld*>d0*>d1*>d1*>d0*>du^^(i+2)*>d1*>rh).
    1: esc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    rewrite (dus_S 2).
    rewrite (dus_S 1).
    eapply sideRLs_tr1 with (d1^^4*>ld*>d1*>d0*>ld*>d1*>d0*>d1*>d0*>du^^(i+1)*>d1*>rh).
    1: esc.
    sscs. }
Time Qed.

Lemma S'_12 i:
  S' (12,i) = S' (O,(S i)).
Proof.
  ut.
  st; simpl_rotate; trivial.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,O)).
  1: stepn' 1154741%N; st; reflexivity.
  eapply progress_nonhalt_cond with (P:=fun '(tp,i) => tp<12).
  2: lia.
  intros [tp i] HP.
  assert (S tp<12\/tp=11) as [E|E] by lia.
  - eexists; split.
    1: apply RC_spec,HP.
    cbn; lia.
  - eexists; split.
    + rewrite <-S'_12.
      rewrite E.
      apply RC_spec; lia.
    + cbn; lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC1RF_1RD0RB_0LE1LA_---1LA_1LF1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[1]).
Notation hL := (A,[1]).
Notation h := [(hR,hL)].

Notation ld := [1;1;0;1;1].
Notation ld' := [1;0;1;1;1].
Notation d0 := [0;1;1].
Notation d1 := [1;1;1].
Notation w1011 := [1;0;1;1].
Notation w11 := [1;1].
Notation lh := (0inf<*<[1;1]).
Notation rh := (ld*>0inf).
Notation dw := (ld++d1^^2++ld++d1++ld^^3++d1^^2++ld++d1^^3).
Notation du := (d1^^2++d0^^2).


Lemma w11_d0 r:
  w11*>d0*>r = ld*>r.
Proof. trivial. Qed.

Lemma w11_d1 r:
  w11*>d1*>r = d1*>w11*>r.
Proof. trivial. Qed.

Lemma w11_ld r:
  w11*>ld*>r = d1*>w1011*>r.
Proof. trivial. Qed.

Lemma w1011_d1 r:
  w1011*>d1*>r = ld'*>w11*>r.
Proof. trivial. Qed.

Lemma w1011_ld r:
  w1011*>ld*>r = ld'*>w1011*>r.
Proof. trivial. Qed.

Lemma w11_lds a b r:
  w11*>ld^^(a+S b)*>r =
  d1*>ld'^^(a+b)*>w1011*>r.
Proof.
  st; simpl_rotate; trivial.
Qed.

Lemma w11_lds' b r:
  w11*>ld^^(S b)*>r =
  d1*>ld'^^(b)*>w1011*>r.
Proof.
  st; simpl_rotate; trivial.
Qed.

Notation dw' := (ld'++d1^^2++ld'++d1++ld'^^3++d1^^2++ld'++d1^^3).

Lemma w11_dws n r:
  w11 *> dw^^n *> ld *> r = d1 *> dw'^^n *> w1011 *> r.
Proof.
  st; simpl_rotate; trivial.
Qed.

Ltac rw_rot :=
  repeat (
  rewrite w11_d0 ||
  rewrite w11_d1 ||
  rewrite w11_ld ||
  rewrite w11_lds ||
  rewrite w11_lds' ||
  rewrite w11_dws ||
  rewrite w1011_d1 ||
  rewrite w1011_ld).


Definition RC tp i :=
match tp with
| O => ld*>d1*>d0*>ld^^(i*6+8)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^i*>ld*>d1*>ld^^2*>d0*>d1^^3*>ld*>d1*>d0*>ld*>d1*>d0*>d1*>d0*>du^^(i+1)*>rh
| 1%nat => ld*>d1*>ld^^(i*6+9)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^i*>ld*>d1*>ld^^2*>d0*>d1^^3*>ld*>d1*>d0*>ld*>d1*>d0*>d1*>d0*>du^^(i+1)*>d1*>rh
| 2 => ld*>d1*>d0*>ld^^(i*6+9)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^i*>ld*>d1^^2*>ld^^3*>d0*>ld*>d1^^2*>ld*>d1*>d0*>d1*>d0*>du^^(i+2)*>rh
| 3 => ld*>d1*>ld^^(i*6+10)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^i*>ld*>d1^^2*>ld^^3*>d0*>ld*>d1^^2*>ld*>d1*>d0*>d1*>d0*>du^^(i+2)*>d1*>rh
| 4 => ld*>d1*>d0*>ld^^(i*6+10)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^i*>ld*>d1^^2*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>du^^(i+3)*>rh
| 5 => ld*>d1*>ld^^(i*6+11)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^i*>ld*>d1^^2*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>du^^(i+3)*>d1*>rh
| 6 => ld*>d1*>d0*>ld^^(i*6+11)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^i*>ld*>d1^^2*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>d1*>ld*>d0*>du^^(i+3)*>rh
| 7 => ld*>d1*>ld^^(i*6+12)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^i*>ld*>d1^^2*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>d1*>ld*>d0*>du^^(i+3)*>d1*>rh
| 8 => ld*>d1*>d0*>ld^^(i*6+12)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^(i+1)*>ld*>d1*>ld^^2*>d1*>d0^^3*>d1*>d0*>du^^(i+2)*>rh
| 9 => ld*>d1*>ld^^(i*6+13)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^(i+1)*>ld*>d1*>ld^^2*>d1*>d0^^3*>d1*>d0*>du^^(i+2)*>d1*>rh
| 10 => ld*>d1*>d0*>ld^^(i*6+13)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^(i+1)*>ld*>d1*>ld^^3*>d0^^2*>d1*>d0*>du^^(i+3)*>rh
| 11 => ld*>d1*>ld^^(i*6+14)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^(i+1)*>ld*>d1*>ld^^3*>d0^^2*>d1*>d0*>du^^(i+3)*>d1*>rh
| _ => ld*>d1*>d0*>ld^^(i*6+14)*>d1*>ld^^2*>d1*>ld^^3*>d1*>dw^^(i+1)*>ld*>d1*>ld^^2*>d0*>d1^^3*>ld*>d1*>d0*>ld*>d1*>d0*>d1*>d0*>du^^(i+2)*>rh
end.

Lemma LRst r:
  lh {{{ (hL,L) }}} ld*>r -->*
  lh {{{ (hR,R) }}} ld'*>w11*>r.
Proof.
  es.
Qed.

Lemma ld_Incs k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld'_Incs k:
  k<>O ->
  segRLs tm (h^^k) (h^^(k*2)) ld' ld.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 1 2 (k-1) 1 2); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld's_Incs k n:
  k<>O ->
  segRLs tm (h^^k) (h^^(k*2^n)) (ld'^^n) (ld^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    eapply segRLs_concat.
    1: apply ld'_Incs; lia.
    applys_eq (IHn (k*2)); flia.
Qed.

Lemma lds_Incs k n:
  segRLs tm (h^^k) (h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    eapply segRLs_concat.
    1: apply ld_Incs; lia.
    applys_eq (IHn (k*2)); flia.
Qed.

Lemma d0_Incs k:
  k mod 2 = O ->
  segRLs tm (h^^k) (h^^(k/2)) d0 d0.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 2 1 (k/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d0_Incs' k:
  k mod 2 <> O ->
  segRLs tm (h^^k) (h^^(k/2)) d0 d1.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 2 1 (k/2) 1 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d1_Incs k:
  k mod 2 = O ->
  segRLs tm (h^^k) (h^^(k/2)) d1 d1.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 2 1 (k/2) 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld's_Incs' v1 a b b' c r r':
  v1 = 1%nat ->
  b+c = b' ->
  sideRLs tm (h^^(2^(a+b)+0)) r (ld^^c*>r') ->
  sideRLs tm (h^^v1) (ld'^^(a+b)*>r) (ld^^(a+b')*>r').
Proof.
  rewrite Nat.add_0_r.
  intros.
  subst.
  replace (a+(b+c)) with (a+b+c) by lia.
  rewrite <-(lpow_add' _ _ c).
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  applys_eq ld's_Incs; flia.
Qed.

Lemma lds_Incs' v1 a b b' c r r':
  v1 = 1%nat ->
  1+b+c = b' ->
  sideRLs tm (h^^(2^(a+(S b))+0)) r (ld^^c*>r') ->
  sideRLs tm (h^^v1) (ld*>ld^^(a+b)*>r) (ld^^(a+b')*>r').
Proof.
  rewrite Nat.add_0_r.
  intros.
  subst.
  change (ld*>ld^^(a+b)*>r) with (ld^^(1+a+b)*>r).
  replace (a+(1+b+c)) with (1+a+b+c) by lia.
  rewrite <-(lpow_add' _ _ c).
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  applys_eq lds_Incs.
  rewrite Nat.mul_1_l; flia.
Qed.

Lemma d1_Incs' k:
  k mod 2 <> O ->
  segRLs tm (h^^k) (h^^(k/2+1)) d1 d0.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 2 1 (k/2) 1 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma dw_Incs k:
  segRLs tm (h^^(k*4)) (h^^k) dw dw.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 4 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma dw'_Incs k:
  k<>O ->
  segRLs tm (h^^(k*4)) (h^^k) dw' dw.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 4 1 (k-1) 4 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma dws_Incs k n:
  segRLs tm (h^^(k*2^(n*2))) (h^^k) (dw^^n) (dw^^n).
Proof.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul Nat.pow].
    eapply segRLs_concat.
    2: apply IHn; lia.
    rw_pa.
    applys_eq (dw_Incs (k*2^(n*2))); flia.
Qed.

Lemma dw's_Incs k n:
  k<>O ->
  segRLs tm (h^^(k*2^(n*2))) (h^^k) (dw'^^n) (dw^^n).
Proof.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul Nat.pow].
    eapply segRLs_concat.
    2: apply IHn; lia.
    rw_pa.
    applys_eq (dw'_Incs (k*2^(n*2))); flia.
Qed.

Lemma dws_Incs' i a b b' b0 c r r':
  b+b0=b' ->
  b*2+c=a ->
  sideRLs tm (h^^(2^(i*4+c)+0)) r (dw^^b0*>r') ->
  sideRLs tm (h^^(2^(i*6+a)+0)) (dw^^(i+b)*>r) (dw^^(i+b')*>r').
Proof.
  intros.
  subst b'.
  rewrite Nat.add_assoc.
  rewrite <-(lpow_add' _ _ b0).
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  replace (i*6+a) with (i*4+c+(i+b)*2) by lia.
  applys_eq (dws_Incs (2^(i*4+c)) (i+b)); rw_pa; flia.
Qed.

Lemma dw's_Incs' i a b b' b0 c r r':
  b+b0=b' ->
  b*2+c=a ->
  sideRLs tm (h^^(2^(i*4+c)+0)) r (dw^^b0*>r') ->
  sideRLs tm (h^^(2^(i*6+a)+0)) (dw'^^(i+b)*>r) (dw^^(i+b')*>r').
Proof.
  intros.
  subst b'.
  rewrite Nat.add_assoc.
  rewrite <-(lpow_add' _ _ b0).
  eapply segRLs_sideRLs_concat.
  2: apply H1.
  replace (i*6+a) with (i*4+c+(i+b)*2) by lia.
  applys_eq (dw's_Incs (2^(i*4+c)) (i+b)); rw_pa; flia.
Qed.

Lemma lpow_0_Str_app a (r:side):
  a^^0*>r = r.
Proof.
  trivial.
Qed.

Lemma lpow_S_Str_app w a (r:side):
  w^^(S a)*>r =
  w*>w^^a*>r.
Proof.
  st; tauto.
Qed.

Lemma du_Incs k:
  segRLs tm (h^^(k*16)) (h^^k) du du.
Proof.
  intros.
  applys_eq (segRLs_addmul_v2 16 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma dus_Incs k n:
  segRLs tm (h^^(k*2^(n*4))) (h^^k) (du^^n) (du^^n).
Proof.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul Nat.pow].
    eapply segRLs_concat.
    2: apply IHn; lia.
    rw_pa.
    applys_eq (du_Incs (k*2^(n*4))); flia.
Qed.


Lemma dus_Incs'1 i a a0:
  a0 = 1+a*4 ->
  sideRLs tm (h ^^ (2 ^ (i * 4 + a0) + 0)) (du ^^ (i + a) *> rh) (du ^^ (i + a) *> d1 *> rh).
Proof.
  intros.
  subst a0.
  replace (i*4+(1+a*4)) with (1+(i+a)*4) by lia.
  remember (i+a) as n.
  clear Heqn i a.
  rw_pa.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: apply dus_Incs.
  esc.
Qed.

Lemma dus_Incs'4 i a a0:
  a0 = 4+a*4 ->
  sideRLs tm (h ^^ (2 ^ (i * 4 + a0) + 0)) (du ^^ (i + a) *> d1 *> rh) (du ^^ (i + (S a)) *> rh).
Proof.
  intros.
  subst a0.
  replace (i*4+(4+a*4)) with (4+(i+a)*4) by lia.
  replace (i+S a) with (i+a+1) by lia.
  remember (i+a) as n.
  clear Heqn i a.
  rewrite <-lpow_add'.
  rw_pa.
  rewrite Nat.add_0_r.
  eapply segRLs_sideRLs_concat.
  1: apply dus_Incs.
  esc.
Qed.

Lemma sideRLs_tr1 a r r' r0:
  sideRLs tm (h) r r0 ->
  sideRLs tm (h^^(2^a-1)) r0 r' ->
  sideRLs tm (h^^(2^a+0)) r r'.
Proof.
  intros.
  replace (2^a+0) with (1+(2^a-1)) by lia.
  eapply sideRLs_trans_add; eauto 1.
Qed.

Lemma dus_S b a r:
  du^^(a+S b)*>r=
  d1*>d1*>d0*>d0*>du^^(a+b)*>r.
Proof.
  st; simpl_rotate; trivial.
Qed.

Ltac ssc :=
  (eapply segRLs_sideRLs_concat; [(apply ld_Incs || apply ld'_Incs || apply d1_Incs || apply d1_Incs' || apply d0_Incs || apply d0_Incs'); rw_pa; lia|]) ||
  ((eapply lds_Incs'||eapply ld's_Incs'||eapply dws_Incs'||eapply dw's_Incs'); [reflexivity|reflexivity|]) ||
  rewrite lpow_0_Str_app ||
  rewrite lpow_S_Str_app ||
  ((apply dus_Incs'1 || apply dus_Incs'4); reflexivity).

Ltac sscs := repeat (ssc; simpl_nat).

Definition S' '(tp,i) :=
  lh {{{ (hL,L) }}} RC tp i.

Lemma RC_spec tp i:
  tp<12 ->
  S' (tp,i) -->+
  S' (S tp,i).
Proof.
  unfold S',RC.
  intros.
  do 12 (destruct tp as [|tp]; [shelve|]).
  lia.
  Unshelve.
  all: follow LRst; eapply sideRLs_1.
  all: change h with (h^^1).
  all: replace (dw^^i) with (dw^^(i+0)) by flia.
  { rw_rot. sscs. }
  { rw_rot. sscs.
    eapply sideRLs_tr1 with (r0:=d0*>ld^^3*>d0*>ld*>d1^^2*>ld*>d1*>d0^^2*>d1*>du^^(i+1)*>d1*>rh).
    1: esc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    rewrite (dus_S 1).
    rewrite (dus_S 2).
    eapply sideRLs_tr1 with (r0:=ld*>d1*>d0*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>d1*>d0*>d1*>d0*>du^^(i+1)*>d1*>rh).
    1: esc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    rewrite (dus_S 2).
    rewrite (dus_S 1).
    rewrite (dus_S 2).
    eapply sideRLs_tr1 with (r0:=ld*>d1*>d0*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>ld*>d1*>ld*>d0^^3*>d1*>d0*>du^^(i+1)*>d1*>rh).
    1: esc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    rewrite (dus_S 2).
    rewrite (dus_S 1).
    eapply sideRLs_tr1 with (r0:=ld*>d1*>d0*>ld*>d1*>ld^^3*>d1^^2*>ld*>d1^^2*>d0*>ld*>d1*>ld^^2*>d1*>d0*>d1*>d0*>d1*>d0*>du^^(i+1)*>d1*>rh).
    1: esc.
    repeat rewrite Str_app_assoc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    eapply sideRLs_tr1 with (r0:=ld*>d0*>d1*>d1*>d0*>du^^(i+2)*>d1*>rh).
    1: esc.
    sscs. }
  { rw_rot. sscs. }
  { rw_rot. sscs.
    rewrite (dus_S 2).
    rewrite (dus_S 1).
    eapply sideRLs_tr1 with (d1^^4*>ld*>d1*>d0*>ld*>d1*>d0*>d1*>d0*>du^^(i+1)*>d1*>rh).
    1: esc.
    sscs. }
Time Qed.

Lemma S'_12 i:
  S' (12,i) = S' (O,(S i)).
Proof.
  ut.
  st; simpl_rotate; trivial.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,O)).
  1: stepn' 1006379%N; st; reflexivity.
  eapply progress_nonhalt_cond with (P:=fun '(tp,i) => tp<12).
  2: lia.
  intros [tp i] HP.
  assert (S tp<12\/tp=11) as [E|E] by lia.
  - eexists; split.
    1: apply RC_spec,HP.
    cbn; lia.
  - eexists; split.
    + rewrite <-S'_12.
      rewrite E.
      apply RC_spec; lia.
    + cbn; lia.
Qed.

End TM2.



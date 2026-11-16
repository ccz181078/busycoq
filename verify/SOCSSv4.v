From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal ES_v3.
From BusyCoq Require Import DivModCases.
Require Import String List PeanoNat NArith Lia.
Open Scope sym.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac cat :=
  eapply segRLs_sideRLs_concat ||
  eapply segRLs_concat.

Ltac tr :=
  eapply sideRLs_trans ||
  eapply segRLs_trans.

Ltac cat1 H :=
  cat; [apply H|].

Ltac wal := apply segRLs_wall''; esc.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.



Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RA_0RF0LD_1LE1LC_1RA0RC_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;0;1;0].
Notation d0 := [0;0;0;0].
Notation d1 := [1;0;0;0].
Notation w := [1;0;1;0;1;0;0;0].

Notation hR := (B,<[]).
Notation hL := (C,[]).
Notation h := [(hR,hL)].
Notation hRx := (A,<[]).
Notation hLx := (D,[0;1;0]).
Notation hx := [(hRx,hLx)].
Notation hR' := (B,<[0;1]).
Notation hL' := (E,[1;0]).
Notation h' := [(hR',hL')].

Notation lh := (0inf<*<[1;1;1]).
Notation hLxR := [(hLx,hR)].
Notation hLRx := [(hL,hRx)].
Notation hLR := [(hL,hR)].
Notation hR'L := [(hR',hL)].
Notation hRL' := [(hR,hL')].

Lemma LRst:
  sideRLs (flip tm) ((hLxR++hLR^^2++hLRx)^^9) lh lh.
Proof.
  apply sideRLs_wall.
  esc.
Qed.

Lemma LRst':
  sideRLs (flip tm) [(hLx,hR');(hL,hRx)] lh lh.
Proof.
  esc.
Qed.

Open Scope nat.

Lemma ld_Incs k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  am 1 2 k 0 0.
Qed.

Lemma d0_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) d0 d0.
Proof.
  am 2 1 k 0 0.
Qed.

Lemma d1_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) d1 d1.
Proof.
  am 2 1 k 0 0.
Qed.

Lemma ld_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(k*2)) ld ld.
Proof.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Ltac nz k :=
  intro Hk;
  destruct k; [lia|];
  cbn[Nat.mul Nat.add lpow];
  repeat rewrite app_assoc.

Lemma d0_OvIncs k:
  k<>O ->
  segRLs tm (hx++h'^^(k*2)) (hx++h'^^k) d0 d0.
Proof.
  nz k.
  tr.
  2: apply d0_Incs.
  esc.
Qed.

Lemma d1_OvIncs k:
  k<>O ->
  segRLs tm (hx++h'^^(k*2)) (hx++h'^^k) d1 d1.
Proof.
  nz k.
  tr.
  2: apply d1_Incs.
  esc.
Qed.

Lemma w_OvIncs01 k:
  k<>O ->
  segRLs tm (hx++h^^k) (hx++h'^^k) w w.
Proof.
  nz k.
  tr; [|wal]; esc.
Qed.

Lemma w_OvIncs10 k:
  k<>O ->
  segRLs tm (hx++h'^^k) (hx++h^^k) w w.
Proof.
  nz k.
  tr; [|wal]; esc.
Qed.

Ltac seg_nil :=
  repeat (rewrite Nat.mul_1_r || rewrite Nat.add_sub);
  apply segRLs_nil.

Lemma lds_OvIncs k n:
  segRLs tm (hx++h^^k) (hx++h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  gen k.
  induction n; intros.
  - seg_nil.
  - cbn[lpow Nat.pow].
    cat1 ld_OvIncs.
    applys_eq (IHn (k*2)); flia.
Qed.

Lemma d0s_OvIncs k n:
  k<>O ->
  segRLs tm (hx++h'^^(k*2^n)) (hx++h'^^k) (d0^^n) (d0^^n).
Proof.
  intro Hk.
  induction n; intros.
  - seg_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: apply IHn.
    applys_eq (d0_OvIncs); flia.
Qed.

Definition RD n :=
  w ++ ld^^(n+4) ++ w ++ d1 ++ d0 ++ d1 ++ d0^^n ++ d1 ++ d1.

Ltac rw_pa := repeat rewrite Nat.pow_add_r.

Lemma RD_OvIncs k n:
  k<>O ->
  segRLs tm (hx++h'^^(k*2)) (hx++h'^^k) (RD n) (RD n).
Proof.
  intro Hk.
  unfold RD.
  cat1 w_OvIncs10; [lia|].
  cat1 lds_OvIncs.
  cat1 w_OvIncs01; [lia|].
  replace (k*2*2^(n+4)) with (k*2*2*2^n*2*2*2) by (rw_pa; lia).
  cat1 d1_OvIncs; [lia|].
  cat1 d0_OvIncs; [lia|].
  cat1 d1_OvIncs; [lia|].
  cat1 d0s_OvIncs; [lia|].
  cat1 d1_OvIncs; [lia|].
  apply d1_OvIncs; lia.
Qed.

Definition L0 n :=
  ld^^n ++ w.

Definition L1 n :=
  ld^^(n+5) ++ w ++ d1 ++ d0 ++ d1 ++ d0 ++ d1.

Lemma L0_OvIncs n:
  segRLs tm (hx++h^^3) (hx++h'^^(3*2^n)) (L0 n) (L0 n).
Proof.
  cat1 lds_OvIncs.
  apply w_OvIncs01; lia.
Qed.

Lemma L1_OvIncs n:
  segRLs tm (hx++h^^3) (hx++h'^^(3*2^n)) (L1 n) (L1 n).
Proof.
  cat1 lds_OvIncs.
  cat1 w_OvIncs01; [lia|].
  replace (3*2^(n+5)) with (3*2^n*2*2*2*2*2) by (rw_pa; lia).
  cat1 d1_OvIncs; [lia|].
  cat1 d0_OvIncs; [lia|].
  cat1 d1_OvIncs; [lia|].
  cat1 d0_OvIncs; [lia|].
  apply d1_OvIncs; lia.
Qed.


Lemma d1_OvIncs' k0 k:
  segRLs tm (hx++h'^^(k0*2)++hR'L++h^^k) (hx++h'^^k0++hR'L++h^^(k*2)) d1 ld.
Proof.
  repeat rewrite app_assoc.
  tr.
  2: apply ld_Incs.
  destruct k0.
  1: esc.
  tr.
  1: apply d1_OvIncs; lia.
  esc.
Qed.

Lemma d0_OvIncs' k0 k:
  segRLs tm (hx++h'^^(k0*2+1)++hR'L++h^^k) (hx++h'^^k0++hR'L++h^^(k*2)) d0 ld.
Proof.
  rewrite lpow_add.
  repeat rewrite app_assoc.
  tr.
  2: apply ld_Incs.
  destruct k0.
  1: esc.
  rewrite <-app_assoc.
  tr.
  1: apply d0_OvIncs; lia.
  esc.
Qed.

Lemma d0s_OvIncs' k0 k n:
  segRLs tm (hx++h'^^((k0+1)*2^n-1)++hR'L++h^^k) (hx++h'^^k0++hR'L++h^^(k*2^n)) (d0^^n) (ld^^n).
Proof.
  gen k0 k.
  induction n; intros.
  - seg_nil.
  - cbn[Nat.pow lpow].
    cat.
    2: applys_eq (IHn k0 (k*2)); flia.
    applys_eq d0_OvIncs'; flia.
Qed.

Lemma w_OvIncs'2 k0 k:
  segRLs tm (hx++h^^k0++hR'L++h^^k) (hx++h'^^k0++hR'L++h^^((k*2+1)*2)) w (ld++ld).
Proof.
  replace ((k*2+1)*2) with (2+k*2*2) by lia.
  destruct k0.
  2:{
  do 2 rewrite (app_assoc hx).
  tr.
  1: apply w_OvIncs01; lia.
  rewrite lpow_add,app_assoc.
  tr.
  2: cat1 ld_Incs; apply ld_Incs.
  esc. }
  {
    rewrite lpow_add.
    repeat rewrite app_assoc.
    tr.
    2: cat1 ld_Incs; apply ld_Incs.
    esc. }
Qed.

Lemma ld_OvIncs'' k0 k:
  segRLs tm (hx++h^^k0++hRL'++h^^k) (hx++h^^(k0*2)++hR'L++h^^k) ld [].
Proof.
  do 2 rewrite (app_assoc hx).
  tr.
  1: apply ld_OvIncs.
  tr.
  2: seg_nil.
  esc.
Qed.

Lemma ld2_OvIncs'a k0 k:
  segRLs tm (hx++h^^k0++hRL'++h^^k) (hx++h^^(k0*2*2+1)++hRL'++h'^^k) (ld++ld) w.
Proof.
  rewrite lpow_add.
  repeat rewrite <-app_assoc.
  do 2 rewrite (app_assoc hx).
  tr.
  1: cat1 ld_OvIncs; apply ld_OvIncs.
  rewrite app_assoc.
  tr.
  2: wal.
  esc.
Qed.

Lemma ld2_OvIncs'b k0 k:
  segRLs tm (hx++h^^k0++hRL'++h'^^k) (hx++h^^(k0*2*2+1)++hRL'++h^^k) (ld++ld) w.
Proof.
  rewrite lpow_add.
  repeat rewrite <-app_assoc.
  do 2 rewrite (app_assoc hx).
  tr.
  1: cat1 ld_OvIncs; apply ld_OvIncs.
  rewrite app_assoc.
  tr.
  2: wal.
  esc.
Qed.

Lemma ld_OvIncs0' k0 k:
  segRLs tm (hx++h^^k0++hRL'++h'^^(k*2)) (hx++h^^(k0*2+1)++hRL'++h'^^k) ld d0.
Proof.
  rewrite lpow_add.
  repeat rewrite <-app_assoc.
  do 2 rewrite (app_assoc hx).
  tr.
  1: apply ld_OvIncs.
  rewrite app_assoc.
  tr.
  2: apply d0_Incs.
  esc.
Qed.

Lemma lds_OvIncs0' k0 k n:
  segRLs tm (hx++h^^k0++hRL'++h'^^(k*2^n)) (hx++h^^((k0+1)*2^n-1)++hRL'++h'^^k) (ld^^n) (d0^^n).
Proof.
  gen k0 k.
  induction n; intros.
  - seg_nil.
  - cbn[lpow Nat.pow].
    cat.
    1: applys_eq (ld_OvIncs0' k0 (k*2^n)); flia.
    applys_eq (IHn (k0*2+1)); flia.
Qed.

Lemma ld_OvIncs1' k0 k:
  segRLs tm (hx++h^^k0++hRL'++h'^^(k*2+1)) (hx++h^^(k0*2+1)++hRL'++h'^^k) ld d1.
Proof.
  eassert (I1:_). {
    eapply @segRLs_trans with (ls4:=[]) (ls3:=h') (w3:=d1).
    1: apply (ld_OvIncs0' k0 k).
    esc.
  }
  rewrite lpow_add.
  repeat rewrite app_assoc in *.
  rewrite app_nil_r in *.
  apply I1.
Qed.

Lemma mulpow2sub1 a b:
  ((a+1)*2^b-1)*2+1 = (a+1)*2^(S b)-1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2ssub1 a b c:
  ((a+1)*2^b-1+1)*2^c-1 = (a+1)*2^(b+c)-1.
Proof.
  rw_pa.
  nia.
Qed.

Lemma w_OvIncs'3 k0 k:
  segRLs tm (hx++h'^^k0++hR'L++h^^k) (hx++h^^k0++hRL'++h^^((k*2+1)*2*2+1)) w (ld++ld++ld).
Proof.
  replace ((k*2+1)*2*2+1) with (5+k*2*2*2) by lia.
  do 2 rewrite (app_assoc hx).
  destruct k0.
  { rewrite lpow_add.
  repeat rewrite app_assoc.
  tr.
  2: rewrite <-app_assoc.
  2: do 2 cat1 ld_Incs; apply ld_Incs.
  esc. }
  { tr.
  1: apply w_OvIncs10; lia.
  rewrite lpow_add,app_assoc.
  tr.
  2: do 2 cat1 ld_Incs; apply ld_Incs.
  esc. }
Qed.

Lemma RD_OvIncs' k0 k n:
  segRLs tm
  (hx++h'^^(k0*2)++hR'L++h^^((((k*2+1)*2+1)*2^n)))
  (hx++h'^^k0++hR'L++h^^((k*2+1)*2*2*2*2*2^(n+6)*2*2))
  (w++(ld++ld)++ld++ld++ld++ld^^n++ld++ld++(ld++ld)++ld++w++d1++d0++d1++d0^^(n+6)++d1++d1)
  (ld^^3++w++d1++d0++d1++d0^^n++d1++d1++w++[]++(ld++ld)++ld++ld++ld++ld^^(n+6)++ld++ld).
Proof.
  cat1 w_OvIncs'3.
  cat1 ld2_OvIncs'a.
  replace (k0*2*2*2+1) with ((k0*2*2+1)*2^1-1) by lia.
  cat1 ld_OvIncs1'.
  cat1 ld_OvIncs0'.
  cat1 ld_OvIncs1'.
  do 3 rewrite mulpow2sub1.
  cat1 lds_OvIncs0'.
  rewrite mulpow2ssub1.
  cat1 ld_OvIncs1'.
  cat1 ld_OvIncs1'.
  do 2 rewrite mulpow2sub1.
  replace (S(S (4+n))) with (n+6) by lia.
  cat1 ld2_OvIncs'b.
  cat1 ld_OvIncs''.
  cat1 w_OvIncs'2.
  cat1 d1_OvIncs'.
  cat1 d0_OvIncs'.
  cat1 d1_OvIncs'.
  cat1 d0s_OvIncs'.
  cat1 d1_OvIncs'.
  apply d1_OvIncs'.
Qed.

Definition RD1 n :=
  (ld^^3++w++d1++d0++d1++d0^^n++d1++d1).

Definition RD2 n := w++ld^^(13+n).

Definition RD' n :=
  RD1 n ++ RD2 n.

Ltac st' :=
  repeat
  (rewrite lpow_add || rewrite <-app_assoc || rewrite lpow_rotate_list ||
  rewrite app_nil_r || cbn[app lpow]).

Lemma RD_RD21 n:
  RD (12+n) = RD2 n ++ RD1 (12+n).
Proof.
  unfold RD,RD2,RD1.
  st'.
  trivial.
Qed.

Lemma RD_OvIncs'' k n:
  segRLs tm
  (hx++hR'L++h^^((((k*2+1)*2+1)*2^n)))
  (hx++hR'L++h^^((k*2+1)*2^(n+12)))
  (RD (n+6))
  (RD' n).
Proof.
  unfold RD,RD',RD1,RD2.
  applys_eq (RD_OvIncs' 0 k n).
  - rewrite app_nil_l.
    rw_pa; flia.
  - st'.
    trivial.
  - st'.
    trivial.
Qed.

Fixpoint RDs n m :=
match n with
| O => []
| S n => RD m ++ RDs n (m+12)
end.

Fixpoint RDs' n m :=
match n with
| O => []
| S n => RD' m ++ RDs' n (m+12)
end.

Lemma RDs_OvIncs' k n m:
  segRLs tm
  (hx++hR'L++h^^((((k*2+1+1)*2^n-1)*2^m)))
  (hx++hR'L++h^^((k*2+1)*2^(m+n*12)))
  (RDs n (m+6))
  (RDs' n m).
Proof.
  gen k m.
  induction n; intros; cbn[RDs RDs'].
  - rewrite Nat.add_0_r.
    seg_nil.
  - cbn[Nat.pow].
    cat.
    1: applys_eq (RD_OvIncs'' ((k+1)*2^n-1)); flia.
    applys_eq (IHn k (m+12)); flia.
Qed.

Lemma RDs'_rot n m:
  RDs' n m ++ RD1 (n*12+m) = RD1 m ++ RDs n (12+m).
Proof.
  gen m.
  induction n; intros; cbn[RDs' RDs].
  - rewrite app_nil_r.
    trivial.
  - replace (S n*12+m) with (n*12+(m+12)) by lia.
    repeat rewrite <-app_assoc.
    rewrite IHn.
    rewrite RD_RD21.
    unfold RD'.
    repeat rewrite <-app_assoc.
    flia.
Qed.

Definition rh := (w*>d1*>d1*>[0;1]*>0inf)%sym.

Lemma w_Incs01 k:
  segRLs tm (h^^k) (h'^^k) w w.
Proof.
  wal.
Qed.

Lemma d0s_Incs k n:
  segRLs tm (h'^^(k*2^n)) (h'^^k) (d0^^n) (d0^^n).
Proof.
  induction n.
  - seg_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: apply IHn.
    applys_eq (d0_Incs); flia.
Qed.

Lemma rh_OvIncs n:
  sideRLs tm (hx++hR'L++h^^(3*2^n)) rh (RD1 n*>0inf).
Proof.
  unfold rh,RD1.
  repeat rewrite Str_app_assoc.
  rewrite app_assoc.
  eapply @sideRLs_trans with (r2:=ld^^3*>w*>d1*>d0*>d1*>d0^^n*>0inf).
  1: rewrite lpow_all0 by solve_const0_eq; esc.
  cbn[lpow].
  repeat rewrite app_nil_r.
  repeat rewrite Str_app_assoc.
  do 3 cat1 ld_Incs.
  cat1 w_Incs01.
  cat1 d1_Incs.
  cat1 d0_Incs.
  cat1 d1_Incs.
  cat1 d0s_Incs.
  esc.
Qed.

Lemma RDs_OvIncs n m:
  sideRLs tm 
  (hx++hR'L++h^^((((1*2+1+1)*2^n-1)*2^m)))
  (RDs n (m+6) *> rh)
  (RD1 m *> RDs n (12+m) *> 0inf).
Proof.
  rewrite <-Str_app_assoc.
  rewrite <-RDs'_rot.
  rewrite Str_app_assoc.
  cat1 RDs_OvIncs'.
  applys_eq rh_OvIncs; flia.
Qed.

Definition RC0 n :=
  L0 n ++ RDs n 6.

Definition RC1 n :=
  L1 n ++ RDs n 12.

Lemma RDs_OvIncs_0 n:
  sideRLs tm 
  (hx++hR'L++h^^(((4*2^n-1)*2^4)))
  (RDs n 10 *> rh)
  (RD1 4 *> RDs n 16 *> 0inf).
Proof.
  apply (RDs_OvIncs n 4).
Qed.

Lemma ld_OvIncs'_ld k:
  segRLs tm (hx++hR'L++h^^k) (hx++hR'L++h^^(1+k*2)) ld ld.
Proof.
  rewrite lpow_add.
  repeat rewrite app_assoc.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Lemma lds_OvIncs'_ld n:
  segRLs tm (hx++hR'L) (hx++hR'L++h^^(2^n-1)) (ld^^n) (ld^^n).
Proof.
  induction n.
  1: seg_nil.
  replace (S n) with (n+1) by lia.
  rewrite (lpow_add _ n 1).
  cat1 IHn.
  applys_eq (ld_OvIncs'_ld); rw_pa; flia.
Qed.

Lemma RD_OvIncs'_0 n:
  segRLs tm (hx++hR'L) (hx++h'^^0++hR'L++h^^(((2^n-1)*2+1)*2*2*2*2*2^(0+6)*2*2)) (ld^^n++w++w++(ld++ld)++ld++ld++ld++ld++ld++(ld++ld)++ld++w++d1++d0++d1++d0^^(0+6)++d1++d1) (ld^^n++ld^^2++ld^^3++w++d1++d0++d1++d0++d1++w++[]++(ld++ld)++ld++ld++ld++ld^^(0+6)++ld++ld).
Proof.
  cat1 lds_OvIncs'_ld.
  change (hx++hR'L++h^^(2^n-1)) with (hx++h^^0++hR'L++h^^(2^n-1)).
  cat1 w_OvIncs'2.
  cat1 w_OvIncs'3.
  cat1 ld2_OvIncs'a.
  replace (0*2*2+1) with ((0*2*2+1)*2^(0+1)-1) by lia.
  cat1 ld_OvIncs1'.
  cat1 ld_OvIncs0'.
  cat1 ld_OvIncs1'.
  cat1 ld_OvIncs0'.
  cat1 ld_OvIncs1'.
  do 5 rewrite mulpow2sub1.
  replace (S(S(S(S(S(0+1)))))) with (0+6) by lia.
  cat1 ld2_OvIncs'b.
  cat1 ld_OvIncs''.
  cat1 w_OvIncs'2.
  cat1 d1_OvIncs'.
  cat1 d0_OvIncs'.
  cat1 d1_OvIncs'.
  cat1 d0s_OvIncs'.
  cat1 d1_OvIncs'.
  apply d1_OvIncs'.
Qed.

Lemma RD_OvIncs''_0 n:
  segRLs tm (hx++hR'L) (hx++h'^^0++hR'L++h^^(((2^n-1)*2+1)*2^12)) (L0 n ++ RD 6) (L1 n ++ RD2 0).
Proof.
  unfold L0,L1,RD.
  applys_eq (RD_OvIncs'_0 n).
  - flia.
  - st'; trivial.
  - st'; trivial.
Qed.

Lemma ROv0 n:
  sideRLs tm (hx++hR'L) (RC0 n *> rh) (RC1 n *> 0inf).
Proof.
  destruct n.
  1: esc.
  unfold RC0,RC1.
  cbn[RDs].
  change (RD 12) with (RD (12+0)).
  rewrite (RD_RD21 0).
  repeat rewrite <-app_assoc.
  repeat rewrite Str_app_assoc.
  do 2 rewrite <-(Str_app_assoc (_ (S n))).
  cat1 RD_OvIncs''_0.
  rewrite app_nil_l.
  applys_eq (RDs_OvIncs n 12).
  rewrite Nat.pow_succ_r by lia.
  flia.
Qed.

Lemma ld_OvIncs''' k0 k:
  segRLs tm (hx++h^^k0++hR'L++h^^k) (hx++h^^k0++hRL'++h^^(k*2+1)) [] ld.
Proof.
  rewrite Nat.add_comm.
  do 2 rewrite (app_assoc hx).
  tr.
  1: seg_nil.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Lemma RD_OvIncs'_1 n:
  segRLs tm
  (hx ++ hR'L)
  (hx ++ h'^^0 ++ hR'L ++ h ^^ ((((2^n-1)*2+1)*2+1)*2*2*2*2*2*2))
  (ld^^n++[]++ld^^2++ld^^2++ld++w++d1++d0++d1++d0++d1)
  (ld^^n++ld++w++w++[]++ld^^2++ld++ld++ld++ld++ld).
Proof.
  cat1 lds_OvIncs'_ld.
  cat1 (ld_OvIncs''' 0).
  cat1 ld2_OvIncs'a.
  cat1 ld2_OvIncs'b.
  cat1 ld_OvIncs''.
  cat1 w_OvIncs'2.
  cat1 d1_OvIncs'.
  cat1 d0_OvIncs'.
  cat1 d1_OvIncs'.
  cat1 d0_OvIncs'.
  apply d1_OvIncs'.
Qed.

Lemma ROv1 n:
  sideRLs tm (hx++hR'L) (RC1 n *> rh) (RC0 (S n) *> 0inf).
Proof.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (RD_OvIncs'_1 n).
    applys_eq (RDs_OvIncs n 6).
    rewrite app_nil_l.
    flia.
  }
  unfold RC0,RC1,L0,L1.
  cbn[RDs].
  change (RD 6) with (w++ld^^7++RD1 6).
  repeat rewrite Str_app_assoc in *.
  applys_eq I1; st; simpl_rotate; reflexivity.
Qed.

Lemma RDs_Incs n m:
  segRLs tm (hx++h'^^(3*2^n)) (hx++h'^^3) (RDs n m) (RDs n m).
Proof.
  gen m.
  induction n; intros; cbn[RDs].
  - seg_nil.
  - unfold RD.
    repeat rewrite <-app_assoc.
    cbn[Nat.pow].
    cat1 w_OvIncs10; [lia|].
    cat1 lds_OvIncs.
    cat1 w_OvIncs01; [lia|].
    replace (3*(2*2^n)*(2^(m+4))) with (3*2^n*2*2*2^m*2*2*2) by (rw_pa; lia).
    cat1 d1_OvIncs; [lia|].
    cat1 d0_OvIncs; [lia|].
    cat1 d1_OvIncs; [lia|].
    cat1 d0s_OvIncs; [lia|].
    cat1 d1_OvIncs; [lia|].
    cat1 d1_OvIncs; [lia|].
    apply (IHn (m+12)).
Qed.

Lemma RIncs0 n:
  sideRLs tm ((hx++h^^3)^^9) (RC0 n *> 0inf) (RC0 n *> rh).
Proof.
  unfold RC0.
  repeat rewrite Str_app_assoc in *.
  cat.
  1: eapply segRLs_wall'',L0_OvIncs.
  cat.
  1: eapply segRLs_wall'',RDs_Incs.
  esc.
Qed.

Lemma RIncs1 n:
  sideRLs tm ((hx++h^^3)^^9) (RC1 n *> 0inf) (RC1 n *> rh).
Proof.
  unfold RC1.
  repeat rewrite Str_app_assoc in *.
  cat.
  1: eapply segRLs_wall'',L1_OvIncs.
  cat.
  1: eapply segRLs_wall'',RDs_Incs.
  esc.
Qed.

Lemma Incs0 n:
  lh {{{ (hRx,R) }}} RC0 n *> 0inf -->*
  lh {{{ (hRx,R) }}} RC0 n *> rh.
Proof.
  epose proof (sideRLs_concat_v2 _ _ LRst (RIncs0 n)) as I1.
  follow100 I1.
  finish.
  Unshelve.
  - reflexivity.
  - cbn; congruence.
Qed.

Lemma Incs1 n:
  lh {{{ (hRx,R) }}} RC1 n *> 0inf -->*
  lh {{{ (hRx,R) }}} RC1 n *> rh.
Proof.
  epose proof (sideRLs_concat_v2 _ _ LRst (RIncs1 n)) as I1.
  follow100 I1.
  finish.
  Unshelve.
  - reflexivity.
  - cbn; congruence.
Qed.

Definition S' n := lh {{{ (hRx,R) }}} RC0 n *> rh.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: esx.
  eapply progress_nonhalt_simple.
  intro n.
  exists (S n).
  unfold S'.
  epose proof (sideRLs_concat_v2 _ _ LRst' (ROv0 n)) as I1.
  follow10 I1.
  epose proof (sideRLs_concat_v2 _ _ LRst (RIncs1 n)) as I2.
  follow100 I2.
  epose proof (sideRLs_concat_v2 _ _ LRst' (ROv1 n)) as I3.
  follow100 I3.
  epose proof (sideRLs_concat_v2 _ _ LRst (RIncs0 (S n))) as I4.
  follow100 I4.
  finish.
  Unshelve.
  all: try reflexivity.
  all: cbn; congruence.
Qed.

End TM1.


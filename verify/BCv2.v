From BusyCoq Require Import Individual62.

Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require DivModCases.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1RC0RE_1LD0RB_1LE0LD_0LA1RB_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,<[1;0;1]).
Notation hL := (D,[0;0;0]).
Notation hRL := [(hR,hL)].

Notation hR' := (B,<[1;0]).
Notation hL' := (D,[0;0]).
Notation hRL' := [(hR',hL')].

Notation hR00' := (B,<[1;1;1;0]).

Notation hLx := (E,[1;0;0]).
Notation hRLx := [(hR,hLx)].

Notation hRy := (B,<[0;1]).
Notation hRLy := [(hRy,hLx);(hR00',hL')].

Definition D0 a b c := [0;0;1;0]^^a ++ [0;1]^^b ++ [1] ++ [0;0]^^c.

Lemma D0_Ov k a:
  segRLs tm (hRLx++hRL'^^k) (hRLy++hRL'^^(a+k)) (D0 a 1 0) ([0;0]^^(1+a*2)).
Proof.
  gen k.
  induction a; intros.
  - rewrite lpow_add,app_assoc.
    eapply segRLs_trans.
    1: esx.
    eapply segRLs_wall''; esx.
  - change (D0 (S a) 1 0) with ([0;0;1;0]++(D0 a 1 0)).
    replace (1+S a*2) with (2+(1+a*2)) by lia.
    rewrite (lpow_add _ 2 (1+a*2)).
    eapply segRLs_concat.
    2: applys_eq (IHa (1+k)); flia.
    rewrite lpow_add,app_assoc.
    eapply segRLs_trans.
    1: esx.
    eapply segRLs_wall''; esx.
Qed.

Definition Lo k := [0;0;0;1;0]++[0;0]^^k.
Definition Le k := [0;0;0;1]++[0;0]^^k.

Lemma Lo_Ov k0 k:
  segRLs tm (hRLy++hRL'^^k0) (hRLx++hRL'^^k0) (Lo k) (Lo k++[1]).
Proof.
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_wall''; esx.
Qed.

Definition D1 k c :=
  (Lo k ++ [1]) ++ [0;0]^^c.

Definition D2 k b c :=
  Le k ++ D0 0 b c.

Definition D3 k a b c :=
  Lo k ++ D0 a b c.

Lemma Incs2 k0 k b c:
  segRLs tm (hRL'^^k0) [] (D2 k b (k0+c)) (D2 k (k0+b) c).
Proof.
  gen b.
  induction k0; intros.
  - esx.
  - cbn[lpow].
    eapply @segRLs_trans with (ls2:=[]).
    2: applys_eq (IHk0 (1+b)); flia.
    ut; esx.
Qed.

Lemma Incs3 k0 k a b c:
  segRLs tm (hRL'^^k0) [] (D3 k a (1+k0+b) (k0+c)) (D3 k (k0+a) (1+b) c).
Proof.
  gen a.
  induction k0; intros.
  - esx.
  - cbn[lpow].
    eapply @segRLs_trans with (ls2:=[]).
    2: applys_eq (IHk0 (1+a)); flia.
    ut; esx.
Qed.

Lemma Ov1 k c:
  segRLs tm hRLy hRL' (D1 k c) (D2 (1+k) 0 c).
Proof.
  ut; esx.
Qed.

Lemma Ov2 k b c:
  segRLs tm hRLy [] (D2 k b (1+c)) (D3 k 0 (1+b) c).
Proof.
  ut; esx.
Qed.

Lemma Ov3 k0 k a:
  segRLs tm (hRLy++hRL'^^k0) (hRLy++hRL'^^(a+k0)) (D3 k a 1 0) (D1 k (1+a*2)).
Proof.
  unfold D3,D1.
  eapply segRLs_concat.
  1: apply Lo_Ov.
  apply D0_Ov.
Qed.

Lemma Ov0 c:
  sideRLs tm hRLy 0inf (D2 0 0 c*>0inf).
Proof.
  ut.
  rewrite lpow_all0; [|solve_const0_eq].
  esx.
Qed.

Definition hs k1 := hRLy++hRL'^^k1.

Lemma segRLs_trans_0 tm h1 h2 h3 w1 w2 w3:
  segRLs tm h1 [] w1 w2 ->
  segRLs tm h2 h3 w2 w3 ->
  segRLs tm (h1++h2) h3 w1 w3.
Proof.
  intros.
  eapply @segRLs_trans with (ls2:=[]); eauto 1.
Qed.

Lemma OvIncs k1 k:
  let b:=k1+0 in
  let c:=0+(1+(k1+0)) in
  segRLs tm ((hs k1)^^3) (hs ((k1+0+k1)+1)) (D2 k b c) (D2 (1+k) b c).
Proof.
  unfold hs.
  remember (k1+0+k1) as k3.
  cbn[lpow].
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans_0.
  1: apply Ov2.
  replace (1+((k1+0))) with (1+(k1)+0) by lia.
  eapply segRLs_trans_0.
  1: apply Incs3.
  rewrite app_assoc.
  rewrite (app_assoc hRLy (hRL'^^k3)).
  eapply segRLs_trans.
  1: applys_eq Ov3; flia.
  eapply segRLs_trans.
  1: apply Ov1.
  rewrite app_nil_r.
  applys_eq Incs2; flia.
Qed.

Lemma OvIncs_0 k1:
  sideRLs tm (hs k1) 0inf (D2 0 (k1+0) (k1+1) *> 0inf).
Proof.
  unfold hs.
  eapply sideRLs_trans.
  1: apply Ov0.
  eapply segRLs_sideRLs_concat.
  1: apply Incs2.
  esx.
Qed.

Definition tm' := flip tm.
Definition LC n := 0inf <* <[1;1]^^(2+n) <* <[0].
Notation hLR := [(hLx,hR00');(hL',hR');(hL',hRy)].

Lemma LIncs k n:
  sideRLs tm' (hLR^^k) (LC n) (LC (k*4+n)).
Proof.
  unfold LC.
  induction k.
  1: esx.
  replace (S k) with (k+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHk.
  esx.
Qed.

Inductive RC: nat->(list Sym)->Prop :=
| RC_O: RC 0 []
| RC_S i w k:
  RC i w ->
  RC (S i) (w++D2 k (2^i*2-1) (2^i*2)).

Lemma RC_Incs i w:
  RC i w ->
  exists w', segRLs tm ((hs 1)^^(3^i)) (hs (2^i*2-1)) w w' /\ RC i w'.
Proof.
  gen w.
  induction i; intros.
  - inverts H.
    eexists; split.
    2: apply RC_O.
    esx.
  - inverts H.
    eapply IHi in H1.
    destruct H1 as [w1 [I1 I2]].
    eapply IHi in I2.
    destruct I2 as [w2 [I2 I3]].
    eapply IHi in I3.
    destruct I3 as [w3 [I3 I4]].
    eexists; split.
    + eapply segRLs_concat.
      * cbn[Nat.pow Nat.mul].
        repeat rewrite lpow_add.
        do 3 (eapply segRLs_trans; [eauto 1|]).
        esx.
      * applys_eq (OvIncs (2^i*2-1) k); cbn[Nat.pow]; flia.
    + applys_eq RC_S.
      1: flia.
      eauto 1.
Qed.

Lemma RC_Incs_0 i w:
  RC i w ->
  exists w', sideRLs tm ((hs 1)^^(3^i)) (w*>0inf) (w'*>0inf) /\ RC (S i) w'.
Proof.
  intro H.
  apply RC_Incs in H.
  destruct H as [w' [I1 I2]].
  eexists (_++_); split.
  - rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    1: apply I1.
    eapply OvIncs_0.
  - applys_eq RC_S.
    1: flia.
    eauto 1.
Qed.

Definition S' '(n,w) := LC n {{{ (hRy,R) }}} w *> 0inf.

Lemma lcons_hRy k:
  lcons hRy (hLR^^k) = (hs 1^^k,hRy).
Proof.
  induction k; cbn; trivial.
  rewrite IHk; trivial.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (6,[0;0;0;1;0;1;1;0;0;0;0])).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(_,w) => exists i, RC i w).
  2: exists 1%nat; eapply RC_S with (w:=[]) (k:=O),RC_O.
  intros [n w] [i HP].
  apply RC_Incs_0 in HP.
  destruct HP as [w' [I1 I2]].
  eexists (_,_); split.
  2: eexists; apply I2.
  unfold S'.
  eapply sideRLs_concat_v2.
  4: apply I1.
  3: apply LIncs.
  1: apply lcons_hRy.
  destruct (3^i) eqn:E; [lia|cbn; congruence].
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0RE_1LC0LB_0LD1RE_1RE1LF_1RA0RC_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,<[1;0;1]).
Notation hL := (B,[0;0;0]).
Notation hRL := [(hR,hL)].

Notation hR' := (E,<[1;0]).
Notation hL' := (B,[0;0]).
Notation hRL' := [(hR',hL')].

Notation hR00' := (E,<[1;1;1;0]).

Notation hLx := (C,[1;0;0]).
Notation hRLx := [(hR,hLx)].

Notation hRy := (E,<[0;1]).
Notation hRLy := [(hRy,hLx);(hR00',hL')].

Definition D0 a b c := [0;0;1;0]^^a ++ [0;1]^^b ++ [1] ++ [0;0]^^c.

Lemma D0_Ov k a:
  segRLs tm (hRLx++hRL'^^k) (hRLy++hRL'^^(a+k)) (D0 a 1 0) ([0;0]^^(1+a*2)).
Proof.
  gen k.
  induction a; intros.
  - rewrite lpow_add,app_assoc.
    eapply segRLs_trans.
    1: esx.
    eapply segRLs_wall''; esx.
  - change (D0 (S a) 1 0) with ([0;0;1;0]++(D0 a 1 0)).
    replace (1+S a*2) with (2+(1+a*2)) by lia.
    rewrite (lpow_add _ 2 (1+a*2)).
    eapply segRLs_concat.
    2: applys_eq (IHa (1+k)); flia.
    rewrite lpow_add,app_assoc.
    eapply segRLs_trans.
    1: esx.
    eapply segRLs_wall''; esx.
Qed.

Definition Lo k := [0;0;0;1;0]++[0;0]^^k.
Definition Le k := [0;0;0;1]++[0;0]^^k.

Lemma Lo_Ov k0 k:
  segRLs tm (hRLy++hRL'^^k0) (hRLx++hRL'^^k0) (Lo k) (Lo k++[1]).
Proof.
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_wall''; esx.
Qed.

Definition D1 k c :=
  (Lo k ++ [1]) ++ [0;0]^^c.

Definition D2 k b c :=
  Le k ++ D0 0 b c.

Definition D3 k a b c :=
  Lo k ++ D0 a b c.

Lemma Incs2 k0 k b c:
  segRLs tm (hRL'^^k0) [] (D2 k b (k0+c)) (D2 k (k0+b) c).
Proof.
  gen b.
  induction k0; intros.
  - esx.
  - cbn[lpow].
    eapply @segRLs_trans with (ls2:=[]).
    2: applys_eq (IHk0 (1+b)); flia.
    ut; esx.
Qed.

Lemma Incs3 k0 k a b c:
  segRLs tm (hRL'^^k0) [] (D3 k a (1+k0+b) (k0+c)) (D3 k (k0+a) (1+b) c).
Proof.
  gen a.
  induction k0; intros.
  - esx.
  - cbn[lpow].
    eapply @segRLs_trans with (ls2:=[]).
    2: applys_eq (IHk0 (1+a)); flia.
    ut; esx.
Qed.

Lemma Ov1 k c:
  segRLs tm hRLy hRL' (D1 k c) (D2 (1+k) 0 c).
Proof.
  ut; esx.
Qed.

Lemma Ov2 k b c:
  segRLs tm hRLy [] (D2 k b (1+c)) (D3 k 0 (1+b) c).
Proof.
  ut; esx.
Qed.

Lemma Ov3 k0 k a:
  segRLs tm (hRLy++hRL'^^k0) (hRLy++hRL'^^(a+k0)) (D3 k a 1 0) (D1 k (1+a*2)).
Proof.
  unfold D3,D1.
  eapply segRLs_concat.
  1: apply Lo_Ov.
  apply D0_Ov.
Qed.

Lemma Ov0 c:
  sideRLs tm hRLy 0inf (D2 0 0 c*>0inf).
Proof.
  ut.
  rewrite lpow_all0; [|solve_const0_eq].
  esx.
Qed.

Definition hs k1 := hRLy++hRL'^^k1.

Lemma segRLs_trans_0 tm h1 h2 h3 w1 w2 w3:
  segRLs tm h1 [] w1 w2 ->
  segRLs tm h2 h3 w2 w3 ->
  segRLs tm (h1++h2) h3 w1 w3.
Proof.
  intros.
  eapply @segRLs_trans with (ls2:=[]); eauto 1.
Qed.

Lemma OvIncs k1 k:
  let b:=k1+0 in
  let c:=0+(1+(k1+0)) in
  segRLs tm ((hs k1)^^3) (hs ((k1+0+k1)+1)) (D2 k b c) (D2 (1+k) b c).
Proof.
  unfold hs.
  remember (k1+0+k1) as k3.
  cbn[lpow].
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans_0.
  1: apply Ov2.
  replace (1+((k1+0))) with (1+(k1)+0) by lia.
  eapply segRLs_trans_0.
  1: apply Incs3.
  rewrite app_assoc.
  rewrite (app_assoc hRLy (hRL'^^k3)).
  eapply segRLs_trans.
  1: applys_eq Ov3; flia.
  eapply segRLs_trans.
  1: apply Ov1.
  rewrite app_nil_r.
  applys_eq Incs2; flia.
Qed.

Lemma OvIncs_0 k1:
  sideRLs tm (hs k1) 0inf (D2 0 (k1+0) (k1+1) *> 0inf).
Proof.
  unfold hs.
  eapply sideRLs_trans.
  1: apply Ov0.
  eapply segRLs_sideRLs_concat.
  1: apply Incs2.
  esx.
Qed.

Definition tm' := flip tm.
Definition LC n := 0inf <* <[1;1]^^(2+n) <* <[0].
Notation hLR := [(hLx,hR00');(hL',hR');(hL',hRy)].

Lemma LIncs k n:
  sideRLs tm' (hLR^^k) (LC n) (LC (k*4+n)).
Proof.
  unfold LC.
  induction k.
  1: esx.
  replace (S k) with (k+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHk.
  esx.
Qed.

Inductive RC: nat->(list Sym)->Prop :=
| RC_O: RC 0 []
| RC_S i w k:
  RC i w ->
  RC (S i) (w++D2 k (2^i*2-1) (2^i*2)).

Lemma RC_Incs i w:
  RC i w ->
  exists w', segRLs tm ((hs 1)^^(3^i)) (hs (2^i*2-1)) w w' /\ RC i w'.
Proof.
  gen w.
  induction i; intros.
  - inverts H.
    eexists; split.
    2: apply RC_O.
    esx.
  - inverts H.
    eapply IHi in H1.
    destruct H1 as [w1 [I1 I2]].
    eapply IHi in I2.
    destruct I2 as [w2 [I2 I3]].
    eapply IHi in I3.
    destruct I3 as [w3 [I3 I4]].
    eexists; split.
    + eapply segRLs_concat.
      * cbn[Nat.pow Nat.mul].
        repeat rewrite lpow_add.
        do 3 (eapply segRLs_trans; [eauto 1|]).
        esx.
      * applys_eq (OvIncs (2^i*2-1) k); cbn[Nat.pow]; flia.
    + applys_eq RC_S.
      1: flia.
      eauto 1.
Qed.

Lemma RC_Incs_0 i w:
  RC i w ->
  exists w', sideRLs tm ((hs 1)^^(3^i)) (w*>0inf) (w'*>0inf) /\ RC (S i) w'.
Proof.
  intro H.
  apply RC_Incs in H.
  destruct H as [w' [I1 I2]].
  eexists (_++_); split.
  - rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    1: apply I1.
    eapply OvIncs_0.
  - applys_eq RC_S.
    1: flia.
    eauto 1.
Qed.

Definition S' '(n,w) := LC n {{{ (hRy,R) }}} w *> 0inf.

Lemma lcons_hRy k:
  lcons hRy (hLR^^k) = (hs 1^^k,hRy).
Proof.
  induction k; cbn; trivial.
  rewrite IHk; trivial.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (5,[0;0;0;1;0;1;1;0;0;0;0])).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(_,w) => exists i, RC i w).
  2: exists 1%nat; eapply RC_S with (w:=[]) (k:=O),RC_O.
  intros [n w] [i HP].
  apply RC_Incs_0 in HP.
  destruct HP as [w' [I1 I2]].
  eexists (_,_); split.
  2: eexists; apply I2.
  unfold S'.
  eapply sideRLs_concat_v2.
  4: apply I1.
  3: apply LIncs.
  1: apply lcons_hRy.
  destruct (3^i) eqn:E; [lia|cbn; congruence].
Qed.

End TM2.


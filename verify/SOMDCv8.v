From BusyCoq Require Import Individual62 Longitudinal ES_v3 DivModCases.
Require Import Arith ZifyNat Lia List String.
Import ListNotations.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC1RF_0LD1LB_1RE1LC_0RB0RE_0RE0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation Z := [S1;S1;S0;S0].
Notation T := [S1;S0;S1;S0].
Notation hb := (((B,[]),(B,[])):DH0*DH0).
Notation hc := (((B,[]),(C,[])):DH0*DH0).
Notation lh := (0inf <* <[1;0]).

Ltac esc := apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.

Lemma Z_inc : segRLs tm [hb] [] Z T.
Proof. esc. Qed.
Lemma T_inc : segRLs tm [hb] [hb] T Z.
Proof. esc. Qed.
Lemma T_bc : segRLs tm [hb] [hc;hb] T T.
Proof. esc. Qed.
Lemma T_cc : segRLs tm [hc] [hc;hc] T T.
Proof. esc. Qed.
Lemma sep_b : segRLs tm [hc] [hb] [1;0;0] [1;0;0].
Proof. esc. Qed.
Lemma sep_cc : segRLs tm [hb] [hc;hc] [1;0;0] [1;1;0].
Proof. esc. Qed.
Lemma mark_b : segRLs tm [hb] [] [1;1;0] [1;0;1].
Proof. esc. Qed.
Lemma zero_c : segRLs tm [hc] [] [0] [0].
Proof. esc. Qed.
Lemma mark_c : segRLs tm [hc] [hb] [1;0;1;1;0] [1;0;1;0;0].
Proof. esc. Qed.

Lemma left_b r : lh <{{B}} r -->+ lh {{B}}> [0;1;0]*>r.
Proof. es' & r. Qed.
Lemma left_c r : lh <{{C}} r -->+ lh {{B}}> [1;0]*>r.
Proof. es' & r. Qed.

(* Both values of a fixed-width binary word: ordinary and bit-reversed. *)
Inductive Num : nat -> nat -> nat -> list sym -> Prop :=
| Num_nil : Num 0 0 0 []
| Num_Z d a b w : Num d a b w -> Num (1+d) (a*2) b (Z++w)
| Num_T d a b w : Num d a b w -> Num (1+d) (1+a*2) (2^d+b) (T++w).

Lemma Num_bounds d a b w : Num d a b w -> a<2^d /\ b<2^d.
Proof. intro H; induction H; cbn[Nat.pow Nat.add] in *; lia. Qed.

Lemma Num_zero d : Num d 0 0 (Z^^d).
Proof.
  induction d; [constructor|].
  applys_eq (Num_Z _ _ _ _ IHd); flia.
Qed.

Lemma Num_rev_ex d b : b<2^d -> exists a w, Num d a b w.
Proof.
  gen b; induction d; intros b Hb.
  - assert (b=O) by (cbn in Hb; lia); subst; eexists; eexists; constructor.
  - destruct (lt_dec b (2^d)).
    + destruct (IHd _ l) as [a [w H]].
      eexists; eexists; apply Num_Z, H.
    + assert (b-2^d<2^d) by (cbn[Nat.pow] in Hb; lia).
      destruct (IHd _ H) as [a [w I]].
      eexists; eexists; applys_eq (Num_T _ _ _ _ I); flia.
Qed.

Lemma T_pair : segRLs tm [hb;hb] [hb] T T.
Proof. esc. Qed.

Lemma T_counts n :
  segRLs tm ([hb]^^(n*2)++[hc]) ([hb]^^n++[hc;hc]) T T.
Proof.
  induction n; [apply T_cc|].
  change (segRLs tm ([hb;hb]++([hb]^^(n*2)++[hc]))
    ([hb]++([hb]^^n++[hc;hc])) T T).
  eapply segRLs_trans; [apply T_pair|apply IHn].
Qed.

Lemma Z_counts n :
  segRLs tm ([hb]^^(1+n*2)++[hc]) ([hb]^^n++[hc;hc]) Z T.
Proof.
  change (segRLs tm ([hb]++([hb]^^(n*2)++[hc]))
    ([]++([hb]^^n++[hc;hc])) Z T).
  eapply segRLs_trans; [apply Z_inc|apply T_counts].
Qed.

Lemma T_C d : segRLs tm [hc] ([hc]^^(2^d)) (T^^d) (T^^d).
Proof.
  induction d.
  - apply segRLs_nil.
  - replace (2^S d) with (2^d+2^d) by (cbn[Nat.pow]; lia).
    change (segRLs tm [hc] ([hc]^^(2^d+2^d)) (T++T^^d) (T++T^^d)).
    eapply segRLs_concat; [apply T_cc|].
    rewrite lpow_add.
    change [hc;hc] with ([hc]++[hc]).
    eapply segRLs_trans; eassumption.
Qed.

Lemma fixed_C k r :
  sideRLs tm [hc] (T^^k*>[0]*>r) (T^^k*>[0]*>r).
Proof.
  eapply segRLs_sideRLs_concat; [apply T_C|].
  apply sideRLs_wall.
  eapply segRLs_sideRLs_concat; [apply zero_c|constructor].
Qed.

Definition Normal n k t r :=
  sideRLs tm ([hb]^^n++[hc]) r (T^^k*>[0]*>t).

Lemma Normal_C n k t r c : Normal n k t r ->
  sideRLs tm ([hb]^^n++[hc]^^(1+c)) r (T^^k*>[0]*>t).
Proof.
  intro H; rewrite lpow_add, app_assoc.
  eapply sideRLs_trans; [apply H|apply sideRLs_wall, fixed_C].
Qed.

Lemma Normal_Z n k t r : Normal n k t r ->
  Normal (1+n*2) (1+k) t (Z*>r).
Proof.
  intro H; unfold Normal; change (T^^(1+k)) with (T++T^^k); rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat; [apply Z_counts|].
  apply (Normal_C _ _ _ _ 1 H).
Qed.

Lemma Normal_T n k t r : Normal n k t r ->
  Normal (n*2) (1+k) t (T*>r).
Proof.
  intro H; unfold Normal; change (T^^(1+k)) with (T++T^^k); rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat; [apply T_counts|].
  apply (Normal_C _ _ _ _ 1 H).
Qed.

Lemma Normal_num d a b w : Num d a b w -> forall n k t r,
  Normal n k t r -> Normal ((n+1)*2^d-1-a) (d+k) t (w*>r).
Proof.
  intro H; induction H; intros.
  - applys_eq H; flia.
  - epose proof (Num_bounds _ _ _ _ H).
    applys_eq (Normal_Z _ _ _ _ (IHNum _ _ _ _ H0)); cbn[Nat.pow Nat.add]; try nia; flia.
  - epose proof (Num_bounds _ _ _ _ H).
    applys_eq (Normal_T _ _ _ _ (IHNum _ _ _ _ H0)); cbn[Nat.pow Nat.add]; try nia; flia.
Qed.

Lemma scan_pass d :
  segRLs tm [hc] ([hb]^^(2^d)) (T^^d++[1;0;0]) (T^^d++[1;0;0]).
Proof.
  induction d; [apply sep_b|].
  replace (2^S d) with (2^d+2^d) by (cbn[Nat.pow]; lia).
  change (segRLs tm [hc] ([hb]^^(2^d+2^d))
    (T++(T^^d++[1;0;0])) (T++(T^^d++[1;0;0]))).
  eapply segRLs_concat; [apply T_cc|].
  rewrite lpow_add; change [hc;hc] with ([hc]++[hc]).
  eapply segRLs_trans; eassumption.
Qed.

Lemma scan_split d a b w : Num d a b w ->
  segRLs tm [hb] ([hb]^^b++[hc;hc]) (T^^d++[1;0;0]) (w++[1;1;0]).
Proof.
  intro H; induction H; [apply sep_cc| |].
  - change (segRLs tm [hb] ([hb]^^b++[hc;hc])
      (T++(T^^d++[1;0;0])) (Z++(w++[1;1;0]))).
    eapply segRLs_concat; [apply T_inc|apply IHNum].
  - change (segRLs tm [hb] ([hb]^^(2^d+b)++[hc;hc])
      (T++(T^^d++[1;0;0])) (T++(w++[1;1;0]))).
    eapply segRLs_concat; [apply T_bc|].
    rewrite lpow_add, <-app_assoc.
    change [hc;hb] with ([hc]++[hb]).
    eapply segRLs_trans; [apply scan_pass|apply IHNum].
Qed.

Lemma rotate10 n : [1;0]++T^^n = T^^n++[1;0].
Proof.
  induction n; [reflexivity|].
  change (T++([1;0]++T^^n)=T++(T^^n++[1;0])).
  now rewrite IHn.
Qed.

Lemma mark_normal d a b w n t r : Num d a b w -> Normal b n t r ->
  Normal 1 1 (w*>[1;1;0]*>T^^n*>[0]*>t) ([1;1;0]*>T^^(1+d)*>[0]*>r).
Proof.
  intros HN HR; unfold Normal.
  change ([hb]^^1++[hc]) with ([hb]++[hc]).
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat; [apply mark_b|constructor].
  - change (sideRLs tm [hc] ([1;0;1;1;0]*>[1;0]*>T^^d*>[0]*>r)
      ([1;0;1;0;0]*>w*>[1;1;0]*>T^^n*>[0]*>t)).
    rewrite <-(Str_app_assoc [1;0]), rotate10, Str_app_assoc.
    eapply segRLs_sideRLs_concat; [apply mark_c|].
    change ([1;0]*>[0]*>r) with ([1;0;0]*>r).
    rewrite <-(Str_app_assoc (T^^d)), <-(Str_app_assoc w).
    eapply segRLs_sideRLs_concat; [apply (scan_split _ _ _ _ HN)|].
    apply (Normal_C _ _ _ _ 1 HR).
Qed.

Lemma Num_reverse_zero d a b w : Num d a b w -> b=O -> a=O /\ w=Z^^d.
Proof.
  intro H; induction H; intro Hb.
  - auto.
  - destruct (IHNum Hb); subst; auto.
  - exfalso; epose proof (Nat.pow_nonzero 2 d); lia.
Qed.

(* The final Base is all zero; allowing arbitrary Base values loses the
   lower bound needed by the reset invariant. *)
Inductive RC : nat -> nat -> side -> Prop :=
| RC_base d : RC d (2^d-1) (Z^^d*>0inf)
| RC_node d a b w h k q r :
    Num d a b w -> RC k q r -> k<h -> h<=d ->
    RC (1+d) (2^(1+d)-1-a) (w*>[1;1;0]*>T^^h*>[0]*>r).

Lemma RC_bounds k q r : RC k q r ->
  q<2^k /\ (k>O -> 2^(k-1)<=q).
Proof.
  intro H; destruct H.
  - split; [lia|]; destruct d; cbn[Nat.pow Nat.sub]; intros; try lia.
    rewrite Nat.sub_0_r; lia.
  - epose proof (Num_bounds _ _ _ _ H).
    cbn[Nat.pow Nat.add]; split; [lia|].
    replace (S d-1) with d by lia; lia.
Qed.

Lemma RC_zero q r : RC 0 q r -> q=O /\ r=0inf.
Proof. intro H; inverts H; auto. Qed.

Lemma RC_lift d a q w k r k' q' t :
  Num d a q w -> RC k q r -> RC k' q' t ->
  (k=O /\ k'=O \/ k'<k) -> k<=d ->
  RC (1+d) (2^(1+d)-1-a) (w*>[1;1;0]*>T^^k*>[0]*>t).
Proof.
  intros HN HR HT Hk Hd; destruct k.
  - destruct (RC_zero _ _ HR); subst.
    assert (k'=O) by lia; subst.
    destruct (RC_zero _ _ HT); subst.
    destruct (Num_reverse_zero _ _ _ _ HN eq_refl); subst.
    change ([1;1;0]*>T^^0*>[0]*>0inf) with (Z*>0inf).
    rewrite lpow_shift'.
    applys_eq (RC_base (1+d)); flia.
  - eapply RC_node; eauto; lia.
Qed.

Lemma RC_spec k q r : RC k q r -> exists k' q' t,
  RC k' q' t /\ (k=O /\ k'=O \/ k'<k) /\ Normal q k t r.
Proof.
  intro H; induction H.
  - exists O, O, 0inf; split; [apply (RC_base 0)|].
    split; [destruct d; lia|].
    applys_eq (Normal_num _ _ _ _ (Num_zero d) O O 0inf 0inf); try flia.
    unfold Normal; applys_eq (fixed_C 0 0inf); simpl_tape; reflexivity.
  - destruct IHRC as [k' [q' [t [Ht [Hk HN]]]]].
    destruct h as [|h]; [lia|].
    assert (q<2^h) as Hq.
    { epose proof (RC_bounds _ _ _ H0).
      epose proof (Nat.pow_le_mono_r 2 k h); lia. }
    destruct (Num_rev_ex h q Hq) as [a' [w' Hw]].
    exists (1+h), (2^(1+h)-1-a'), (w'*>[1;1;0]*>T^^k*>[0]*>t).
    split; [eapply RC_lift; eauto; lia|].
    split; [lia|].
    applys_eq (Normal_num _ _ _ _ H _ _ _ _ (mark_normal _ _ _ _ _ _ _ Hw HN));
      cbn[Nat.pow Nat.add]; try nia; flia.
Qed.

Definition reset w h r := lh {{B}}> [0;1;0]*>w*>[1;1;0]*>T^^h*>[0]*>r.

Lemma Normal_split n m k t r : Normal (n+m) k t r -> exists r',
  sideRLs tm ([hb]^^n) r r' /\ Normal m k t r'.
Proof.
  unfold Normal; rewrite lpow_add, <-app_assoc; apply sideRLs_split.
Qed.

Lemma call_C r r' : sideRLs tm [hc] r r' -> forall l, l {{B}}> r -->+ l <{{C}} r'.
Proof. intros H l; apply (sideRLs_1 _ _ _ _ _ H l). Qed.
Lemma call_B r r' : sideRLs tm [hb] r r' -> forall l, l {{B}}> r -->+ l <{{B}} r'.
Proof. intros H l; apply (sideRLs_1 _ _ _ _ _ H l). Qed.

Lemma left_scan i r r' : sideRLs tm ([hb]^^(2^i)) r r' ->
  lh {{B}}> T^^i*>[0]*>r -->+ lh {{B}}> T^^(1+i)*>[0]*>r'.
Proof.
  intro H.
  follow10 (call_C _ _ (fixed_C i r) lh).
  follow100 left_c.
  rewrite <-(Str_app_assoc [1;0]), rotate10, Str_app_assoc.
  change ([1;0]*>[0]*>r) with ([1;0;0]*>r).
  rewrite <-(Str_app_assoc (T^^i)).
  follow100 (call_C _ _ (segRLs_sideRLs_concat (scan_pass i) H) lh).
  follow100 left_c.
  rewrite Str_app_assoc, <-(Str_app_assoc [1;0]), rotate10, Str_app_assoc.
  change ([1;0]*>[1;0;0]*>r') with (T*>[0]*>r').
  rewrite lpow_shift'.
  finish.
Qed.

Lemma left_stop i a b w k t r : Num i a b w -> Normal b k t r ->
  lh {{B}}> T^^i*>[0]*>r -->+ reset w k t.
Proof.
  intros HN HR.
  follow10 (call_C _ _ (fixed_C i r) lh).
  follow100 left_c.
  rewrite <-(Str_app_assoc [1;0]), rotate10, Str_app_assoc.
  change ([1;0]*>[0]*>r) with ([1;0;0]*>r).
  rewrite <-(Str_app_assoc (T^^i)).
  follow100 (call_B _ _ (segRLs_sideRLs_concat
    (scan_split _ _ _ _ HN) (Normal_C _ _ _ _ 1 HR)) lh).
  follow100 left_b.
  unfold reset; rewrite Str_app_assoc; finish.
Qed.

Lemma left_return n : forall i a b w q k t r,
  Num (n+i) a b w -> q+2^i=2^(n+i)+b -> Normal q k t r ->
  lh {{B}}> T^^i*>[0]*>r -->+ reset w k t.
Proof.
  induction n; intros i a b w q k t r HN Hq HR.
  - assert (q=b) by (cbn[Nat.add] in Hq; lia); subst.
    eapply left_stop; eauto.
  - assert (q=2^i+(q-2^i)) as E.
    { epose proof (Nat.pow_le_mono_r 2 (1+i) (S n+i)).
      cbn[Nat.pow Nat.add] in *; lia. }
    rewrite E in HR; apply Normal_split in HR as [r' [H1 H2]].
    follow11 (left_scan _ _ _ H1).
    eapply (IHn (1+i)); [applys_eq HN; flia| |apply H2].
    rewrite Nat.add_succ_comm in Hq.
    cbn[Nat.pow Nat.add]; cbn[Nat.pow Nat.add] in Hq; lia.
Qed.

Lemma init : c0 -->* reset (Z++T++Z) 3 (Z*>0inf).
Proof. unfold reset; esx. Qed.

Lemma bridge_pair : segRLs tm [hb;hb] [hb] [1;0;1;1;0;0] [1;0;1;1;0;0].
Proof. esc. Qed.
Lemma bridge_end : segRLs tm [hb] [hc;hc] [1;0;1;1;0;0] [1;0;1;1;1;0].
Proof. esc. Qed.
Lemma bridge_counts n : segRLs tm ([hb]^^(1+n*2)) ([hb]^^n++[hc;hc])
  [1;0;1;1;0;0] [1;0;1;1;1;0].
Proof.
  induction n; [apply bridge_end|].
  change (segRLs tm ([hb;hb]++[hb]^^(1+n*2)) ([hb]++([hb]^^n++[hc;hc]))
    [1;0;1;1;0;0] [1;0;1;1;1;0]).
  eapply segRLs_trans; [apply bridge_pair|apply IHn].
Qed.

Lemma defect_start r : sideRLs tm [hc] r r -> forall l,
  l {{B}}> [1;0;1;1;1;0]*>r -->* l <* <[1;0;1;0;1;0] {{E}}> r.
Proof.
  intros H l; epose proof (call_C _ _ H) as HC.
  es; er; follow100 HC; es; er; follow100 HC; es.
Qed.

Lemma defect_first0 : segRLs tm [hc] [hb] [1;0;1;1;1;0;0] [1;0;1;0;1;0;0].
Proof. esc. Qed.

Lemma E10 l r : l {{E}}> [1;0]*>r -->* l <* <[0;0] {{B}}> r.
Proof. es' & l r. Qed.

Lemma defect_ready s r l :
  l {{B}}> [1;0;1;1;1;0]*>T^^(1+s)*>[0]*>r -->*
  l <* <[1;0;1;0;1;0;0;0] {{B}}> (T^^s++[1;0;0])*>r.
Proof.
  follow (defect_start _ (fixed_C (1+s) r) l).
  follow E10.
  change (l <* <[1;0;1;0;1;0;0;0] {{B}}> [1;0]*>T^^s*>[0]*>r -->*
    l <* <[1;0;1;0;1;0;0;0] {{B}}> (T^^s++[1;0;0])*>r).
  rewrite Str_app_assoc, <-(Str_app_assoc [1;0]), rotate10, Str_app_assoc; finish.
Qed.

Lemma defect_restart l r : l <* <[1;0;1;0;1;0;0;0] <{{C}} r -->*
  l <* <[1;0;1;0;1;0;1;0] {{B}}> r.
Proof. es' & l r. Qed.
Lemma T2_back_C l r : l <* <[1;0;1;0;1;0;1;0] <{{C}} r -->*
  l <{{C}} T*>T*>r.
Proof. es' & l r. Qed.
Lemma T2_back_B l r : l <* <[1;0;1;0;1;0;1;0] <{{B}} r -->*
  l <{{B}} T*>T*>r.
Proof. es' & l r. Qed.

Lemma defect_first s r r' : sideRLs tm ([hb]^^(2^s)) r r' ->
  sideRLs tm [hc] ([1;0;1;1;1;0]*>T^^s*>[0]*>r)
    (T^^(1+s)*>[1;0;0]*>r').
Proof.
  intro H; destruct s.
  - change (sideRLs tm [hc] ([1;0;1;1;1;0;0]*>r) ([1;0;1;0;1;0;0]*>r')).
    eapply segRLs_sideRLs_concat; [apply defect_first0|apply H].
  - replace (2^S s) with (2^s+2^s) in H by (cbn[Nat.pow]; lia).
    rewrite lpow_add in H; apply sideRLs_split in H as [r1 [H1 H2]].
    econstructor; [|constructor]; intro l.
    follow (defect_ready s r l).
    follow10 (call_C _ _ (segRLs_sideRLs_concat (scan_pass s) H1)
      (l <* <[1;0;1;0;1;0;0;0])).
    follow defect_restart.
    follow100 (call_C _ _ (segRLs_sideRLs_concat (scan_pass s) H2)
      (l <* <[1;0;1;0;1;0;1;0])).
    follow T2_back_C; rewrite Str_app_assoc; finish.
Qed.

Lemma Normal_B n k t r r' : sideRLs tm [hb] r r' -> Normal n k t r' ->
  Normal (1+n) k t r.
Proof. unfold Normal; intros; change ([hb]^^(1+n)) with ([hb]++[hb]^^n).
  rewrite <-app_assoc; eapply sideRLs_trans; eauto. Qed.

Lemma scan_many j n : segRLs tm ([hc]^^n) ([hb]^^(n*2^j))
  (T^^j++[1;0;0]) (T^^j++[1;0;0]).
Proof.
  rewrite lpow_mul.
  apply segRLs_wall'', scan_pass.
Qed.

Lemma scan_finish j a b w k t r u : Num j a b w -> Normal b k t r ->
  Normal 1 1 u ([1;1;0]*>T^^k*>[0]*>t) ->
  Normal (2^(1+j)-a) (1+j) u ((T^^j++[1;0;0])*>r).
Proof.
  intros HN HR HM; epose proof (Num_bounds _ _ _ _ HN).
  epose proof (segRLs_sideRLs_concat (scan_split _ _ _ _ HN)
    (Normal_C _ _ _ _ 1 HR)) as H1.
  rewrite (Str_app_assoc w) in H1.
  applys_eq (Normal_B _ _ _ _ _ H1
    (Normal_num _ _ _ _ HN _ _ _ _ HM));
    cbn[Nat.pow Nat.add]; try lia; rewrite Str_app_assoc; reflexivity.
Qed.

Lemma defect_high s m a b w k t r u : Num (1+s) a b w ->
  Normal (2^s+m*2^(1+s)+b) k t r ->
  Normal 1 1 u ([1;1;0]*>T^^k*>[0]*>t) ->
  sideRLs tm ([hc]^^(1+m)++([hb]^^(2^(2+s)-a)++[hc]))
    ([1;0;1;1;1;0]*>T^^s*>[0]*>r) (T^^(2+s)*>[0]*>u).
Proof.
  intros HN HR HM.
  replace (2^s+m*2^(1+s)+b) with (2^s+(m*2^(1+s)+b)) in HR by lia.
  apply Normal_split in HR as [r1 [H1 H2]].
  apply Normal_split in H2 as [r2 [H2 H3]].
  change ([hc]^^(1+m)) with ([hc]++[hc]^^m).
  rewrite <-app_assoc.
  eapply sideRLs_trans; [eapply defect_first; apply H1|].
  rewrite <-(Str_app_assoc (T^^(1+s))).
  eapply sideRLs_trans.
  - eapply segRLs_sideRLs_concat; [apply scan_many|apply H2].
  - apply (scan_finish _ _ _ _ _ _ _ _ HN H3 HM).
Qed.

Lemma defect_low_first s a b w k t r : Num s a b w -> Normal (2^s+b) k t r ->
  sideRLs tm [hb] ([1;0;1;1;1;0]*>T^^(1+s)*>[0]*>r)
    (T*>T*>w*>[1;1;0]*>T^^k*>[0]*>t).
Proof.
  intros HN HR; apply Normal_split in HR as [r1 [H1 H2]].
  econstructor; [|constructor]; intro l.
  follow (defect_ready s r l).
  follow10 (call_C _ _ (segRLs_sideRLs_concat (scan_pass s) H1)
    (l <* <[1;0;1;0;1;0;0;0])).
  follow defect_restart.
  follow100 (call_B _ _ (segRLs_sideRLs_concat
    (scan_split _ _ _ _ HN) (Normal_C _ _ _ _ 1 H2))
    (l <* <[1;0;1;0;1;0;1;0])).
  follow T2_back_B; rewrite Str_app_assoc; finish.
Qed.

Lemma defect_low s a b w k t r u : Num s a b w -> Normal (2^s+b) k t r ->
  Normal 1 1 u ([1;1;0]*>T^^k*>[0]*>t) ->
  Normal (2^(3+s)-3-a*4) (3+s) u ([1;0;1;1;1;0]*>T^^(1+s)*>[0]*>r).
Proof.
  intros HN HR HM; epose proof (Num_bounds _ _ _ _ HN).
  applys_eq (Normal_B _ _ _ _ _ (defect_low_first _ _ _ _ _ _ _ HN HR)
    (Normal_T _ _ _ _ (Normal_T _ _ _ _ (Normal_num _ _ _ _ HN _ _ _ _ HM))));
    cbn[Nat.pow Nat.add]; try nia; flia.
Qed.

Lemma T_B n : segRLs tm ([hb]^^(n*2)) ([hb]^^n) T T.
Proof.
  induction n; [constructor|].
  change (segRLs tm ([hb;hb]++[hb]^^(n*2)) ([hb]++[hb]^^n) T T).
  eapply segRLs_trans; [apply T_pair|apply IHn].
Qed.
Lemma Z_B n : segRLs tm ([hb]^^(1+n*2)) ([hb]^^n) Z T.
Proof.
  change (segRLs tm ([hb]++[hb]^^(n*2)) ([]++[hb]^^n) Z T).
  eapply segRLs_trans; [apply Z_inc|apply T_B].
Qed.
Lemma Num_B d a b w : Num d a b w -> forall n,
  segRLs tm ([hb]^^((n+1)*2^d-1-a)) ([hb]^^n) w (T^^d).
Proof.
  intro H; induction H; intro n.
  - applys_eq (@segRLs_nil tm ([hb]^^n)); flia.
  - epose proof (Num_bounds _ _ _ _ H).
    applys_eq (segRLs_concat (Z_B _) (IHNum n));
      cbn[Nat.pow Nat.add]; try nia; flia.
  - epose proof (Num_bounds _ _ _ _ H).
    applys_eq (segRLs_concat (T_B _) (IHNum n));
      cbn[Nat.pow Nat.add]; try nia; flia.
Qed.

Lemma T_Bs j n : segRLs tm ([hb]^^(n*2^j)) ([hb]^^n) (T^^j) (T^^j).
Proof.
  gen n; induction j; intro n.
  - applys_eq (@segRLs_nil tm ([hb]^^n)); flia.
  - applys_eq (segRLs_concat (T_B _) (IHj n)); cbn[Nat.pow]; try nia; flia.
Qed.

Lemma filter_split j a b w : Num j a b w ->
  segRLs tm [hb] ([hc]^^b++[hb]) (T^^j) w.
Proof.
  intro H; induction H; [apply segRLs_nil| |].
  - change (segRLs tm [hb] ([hc]^^b++[hb]) (T++T^^d) (Z++w)).
    eapply segRLs_concat; [apply T_inc|apply IHNum].
  - change (segRLs tm [hb] ([hc]^^(2^d+b)++[hb]) (T++T^^d) (T++w)).
    eapply segRLs_concat; [apply T_bc|].
    rewrite lpow_add, <-app_assoc; change [hc;hb] with ([hc]++[hb]).
    eapply segRLs_trans; [apply T_C|apply IHNum].
Qed.

Lemma filter_run j a b w n : Num j a b w ->
  segRLs tm ([hb]^^((1+n)*2^j-a)) ([hc]^^b++[hb]^^(1+n)) (T^^j) (T^^j).
Proof.
  intro H; epose proof (Num_bounds _ _ _ _ H).
  replace ((1+n)*2^j-a) with (1+((n+1)*2^j-1-a)) by nia.
  change ([hb]^^(1+((n+1)*2^j-1-a))) with ([hb]++[hb]^^((n+1)*2^j-1-a)).
  change ([hb]^^(1+n)) with ([hb]++[hb]^^n).
  rewrite app_assoc.
  eapply segRLs_trans; [apply (filter_split _ _ _ _ H)|apply (Num_B _ _ _ _ H)].
Qed.

Lemma filter_stream j a b w p n : Num j a b w ->
  segRLs tm ([hb]^^((p+1+n)*2^j-a)++[hc])
    ([hb]^^p++[hc]^^b++[hb]^^(1+n)++[hc]^^(2^j)) (T^^j) (T^^j).
Proof.
  intro H; epose proof (Num_bounds _ _ _ _ H).
  epose proof (segRLs_trans (T_Bs j p)
    (segRLs_trans (filter_run _ _ _ _ n H) (T_C j))) as H1.
  repeat rewrite <-app_assoc in H1.
  rewrite app_assoc, <-lpow_add in H1.
  applys_eq H1; try (repeat rewrite <-app_assoc; reflexivity).
  f_equal; f_equal; nia.
Qed.

Lemma Num_snoc_Z d a b w : Num d a b w -> Num (1+d) a (b*2) (w++Z).
Proof.
  intro H; induction H; [apply (Num_Z _ _ _ _ Num_nil)| |].
  - applys_eq (Num_Z _ _ _ _ IHNum); flia.
  - applys_eq (Num_T _ _ _ _ IHNum); cbn[Nat.pow Nat.add]; flia.
Qed.
Lemma Num_snoc_T d a b w : Num d a b w -> Num (1+d) (2^d+a) (1+b*2) (w++T).
Proof.
  intro H; induction H; [apply (Num_T _ _ _ _ Num_nil)| |].
  - applys_eq (Num_Z _ _ _ _ IHNum); cbn[Nat.pow Nat.add]; flia.
  - applys_eq (Num_T _ _ _ _ IHNum); cbn[Nat.pow Nat.add]; flia.
Qed.
Lemma Num_reverse d a b w : Num d a b w -> exists w', Num d b a w'.
Proof.
  intro H; induction H.
  - exists (@nil sym); constructor.
  - destruct IHNum as [w' H']; eexists; apply Num_snoc_Z, H'.
  - destruct IHNum as [w' H']; eexists; apply Num_snoc_T, H'.
Qed.
Lemma Num_complement d a b w : Num d a b w ->
  exists w', Num d (2^d-1-a) (2^d-1-b) w'.
Proof.
  intro H; induction H.
  - exists (@nil sym); constructor.
  - destruct IHNum as [w' H']; epose proof (Num_bounds _ _ _ _ H).
    exists (T++w'); applys_eq (Num_T _ _ _ _ H'); cbn[Nat.pow Nat.add]; flia.
  - destruct IHNum as [w' H']; epose proof (Num_bounds _ _ _ _ H).
    exists (Z++w'); applys_eq (Num_Z _ _ _ _ H'); cbn[Nat.pow Nat.add]; flia.
Qed.

Lemma Normal_prefix p n k t r r' : sideRLs tm ([hb]^^p) r r' -> Normal n k t r' ->
  Normal (p+n) k t r.
Proof. unfold Normal; rewrite lpow_add, <-app_assoc; eapply sideRLs_trans. Qed.

Lemma even_core s a b w q e we r v t u :
  Num s a b w -> Num s e q we ->
  Normal 1 1 v ([1;1;0]*>T^^(1+s)*>[0]*>r) ->
  Normal (2^(1+s)-1-e) (1+s) t v ->
  Normal 1 1 u ([1;1;0]*>T^^(1+s)*>[0]*>t) ->
  Normal (2^(3+s)-a*2+q*4) (3+s) u
    ([1;0]*>Z*>w*>[1;1;0]*>T^^(1+s)*>[0]*>r).
Proof.
  intros HN HQ HM HR HM'.
  destruct (Num_reverse _ _ _ _ HQ) as [wq Hq].
  destruct (Num_complement _ _ _ _ Hq) as [wq' Hq'].
  epose proof (Num_bounds _ _ _ _ HN); epose proof (Num_bounds _ _ _ _ HQ).
  assert (HR': Normal (2^s+(2^s-1-e)) (1+s) t v).
  { applys_eq HR; cbn[Nat.pow Nat.add]; flia. }
  epose proof (Normal_C _ _ _ _ 1 (Normal_num _ _ _ _ HN _ _ _ _ HM)) as HP.
  epose proof (segRLs_sideRLs_concat (bridge_counts _) HP) as Hpre.
  rewrite (Nat.add_comm s 1) in Hpre.
  epose proof (defect_low _ _ _ _ _ _ _ _ Hq' HR' HM') as Hpost.
  applys_eq (Normal_prefix _ _ _ _ _ _ Hpre Hpost);
    cbn[Nat.pow Nat.add]; try nia; flia.
Qed.

Lemma allones_ready0 r : sideRLs tm [hc] r r -> forall l,
  l {{B}}> [1;0;1;1;0;1;0;1;0]*>r -->*
  l <* <[1;1;0;1;0;0;0] {{B}}> [1;0]*>r.
Proof.
  intros H l; epose proof (call_C _ _ H) as HC.
  es; er; follow100 HC; es; er; follow100 HC; es; er;
  follow100 HC; es; er; follow100 HC; es.
Qed.

Lemma allones_ready h r l :
  l {{B}}> [1;0]*>[1;1;0]*>T^^(1+h)*>[0]*>r -->*
  l <* <[1;1;0;1;0;0;0] {{B}}> (T^^h++[1;0;0])*>r.
Proof.
  follow (allones_ready0 _ (fixed_C h r) l).
  rewrite Str_app_assoc, <-(Str_app_assoc [1;0]), rotate10, Str_app_assoc; finish.
Qed.

Lemma allones_back l r : l <* <[1;1;0;1;0;0;0] <{{B}} r -->*
  l <{{B}} [1;0;1;1;1;0;0]*>r.
Proof. es' & l r. Qed.

Lemma allones_first h a q w k t r : Num h a q w -> Normal q k t r ->
  sideRLs tm [hb] ([1;0]*>[1;1;0]*>T^^(1+h)*>[0]*>r)
    ([1;0;1;1;1;0;0]*>w*>[1;1;0]*>T^^k*>[0]*>t).
Proof.
  intros HN HR; econstructor; [|constructor]; intro l.
  follow (allones_ready h r l).
  follow10 (call_B _ _ (segRLs_sideRLs_concat
    (scan_split _ _ _ _ HN) (Normal_C _ _ _ _ 1 HR))
    (l <* <[1;1;0;1;0;0;0])).
  follow allones_back; rewrite Str_app_assoc; finish.
Qed.

Lemma fixed_more hs k t r c : sideRLs tm (hs++[hc]) r (T^^k*>[0]*>t) ->
  sideRLs tm (hs++[hc]^^(1+c)) r (T^^k*>[0]*>t).
Proof.
  intro H; rewrite lpow_add, app_assoc.
  eapply sideRLs_trans; [apply H|apply sideRLs_wall, fixed_C].
Qed.

Lemma filter_normal j a b w p n k t r : Num j a b w ->
  sideRLs tm ([hb]^^p++[hc]^^b++[hb]^^(1+n)++[hc]) r (T^^k*>[0]*>t) ->
  Normal ((p+1+n)*2^j-a) (j+k) t (T^^j*>r).
Proof.
  intros HN HR; unfold Normal; rewrite lpow_add, Str_app_assoc.
  eapply segRLs_sideRLs_concat; [apply (filter_stream _ _ _ _ p n HN)|].
  repeat rewrite app_assoc in HR |- *.
  applys_eq (fixed_more _ _ _ _ (2^j-1) HR); flia.
Qed.

Lemma Num_unique d a b w : Num d a b w -> forall b' w', Num d a b' w' -> b=b' /\ w=w'.
Proof.
  intro H; induction H; intros b' w' H'; inverts H'; try lia; auto.
  - assert (a0=a) by lia; subst.
    match goal with H': Num d a _ _ |- _ => apply IHNum in H'; destruct H'; subst; auto end.
  - assert (a0=a) by lia; subst.
    match goal with H': Num d a _ _ |- _ => apply IHNum in H'; destruct H'; subst; auto end.
Qed.

(* Incrementing an ordinary binary word has one carry chain.  Its reversed
   value changes by -2^d+3*2^e, where e<d is the terminating digit. *)
Lemma Num_succ d a b w : Num d a b w -> a+1<2^d ->
  exists e b' w', e<d /\ Num d (1+a) b' w' /\
    b'+2^d=b+3*2^e /\ 2^e<=b'<2^(1+e).
Proof.
  intro H; induction H; intro Ha; cbn[Nat.pow Nat.add] in Ha; try lia.
  - exists d, (2^d+b), (T++w); split; [lia|]; split.
    + apply Num_T, H.
    + epose proof (Num_bounds _ _ _ _ H); cbn[Nat.pow Nat.add]; lia.
  - destruct IHNum as [e [b' [w' [He [HN [Hb Hbound]]]]]]; [lia|].
    exists e, b', (Z++w'); split; [lia|]; split.
    + applys_eq (Num_Z _ _ _ _ HN); flia.
    + split; [cbn[Nat.pow Nat.add]; lia|apply Hbound].
Qed.

Lemma Num_half_Z j c z w : Num j c z w -> z>O -> exists e f wf,
  O<e /\ e<=j /\ 2^(e-1)<=z<2^e /\
  Num (1+j) f (2^(1+j)-c) wf /\ f+z*2+1=3*2^e.
Proof.
  intros HN Hz; epose proof (Num_bounds _ _ _ _ HN).
  assert (c>O) as Hc.
  { destruct c; [|lia].
    destruct (Num_unique _ _ _ _ (Num_zero j) _ _ HN); lia. }
  destruct (Num_complement _ _ _ _ (Num_snoc_Z _ _ _ _ HN)) as [w' Hcomp].
  destruct (Num_succ _ _ _ _ Hcomp ltac:(cbn[Nat.pow Nat.add]; lia)) as
    [e [f [wf [He [Hf [Hsum Hbound]]]]]].
  cbn[Nat.pow Nat.add] in Hsum.
  destruct (Num_reverse _ _ _ _ Hf) as [wf' Hf'].
  exists e, f, wf'; split.
  - destruct e; [cbn in Hbound; cbn[Nat.pow] in Hsum; lia|lia].
  - split; [lia|]; split.
    + destruct e; [cbn in Hbound; cbn[Nat.pow] in Hsum; lia|].
      cbn[Nat.sub]; rewrite Nat.sub_0_r.
      cbn[Nat.pow Nat.add] in Hsum,Hbound |- *; lia.
    + split; [applys_eq Hf'; cbn[Nat.pow Nat.add]; flia|lia].
Qed.

Lemma Num_half_T j c z w : Num j c z w -> exists wf,
  Num (1+j) (2^(1+j)-1-z*2) (2^(1+j)-1-c) wf.
Proof.
  intro HN; destruct (Num_complement _ _ _ _ (Num_snoc_Z _ _ _ _ HN)) as [w' H].
  apply Num_reverse in H; apply H.
Qed.

Lemma Normal_blank : Normal 0 0 0inf 0inf.
Proof. unfold Normal; applys_eq (fixed_C 0 0inf); simpl_tape; reflexivity. Qed.

Lemma RC_mark d k q r : RC k q r -> k<=d -> exists a w k' q' t,
  Num d a q w /\ RC k' q' t /\ (k=O /\ k'=O \/ k'<k) /\
  Normal q k t r /\
  RC (1+d) (2^(1+d)-1-a) (w*>[1;1;0]*>T^^k*>[0]*>t) /\
  Normal 1 1 (w*>[1;1;0]*>T^^k*>[0]*>t) ([1;1;0]*>T^^(1+d)*>[0]*>r).
Proof.
  intros HR Hd; destruct (RC_spec _ _ _ HR) as [k' [q' [t [Ht [Hk HN]]]]].
  assert (q<2^d) as Hq.
  { epose proof (RC_bounds _ _ _ HR); epose proof (Nat.pow_le_mono_r 2 k d); lia. }
  destruct (Num_rev_ex d q Hq) as [a [w Hw]].
  exists a, w, k', q', t; repeat split; auto.
  - eapply RC_lift; eauto.
  - apply (mark_normal _ _ _ _ _ _ _ Hw HN).
Qed.

Lemma RC_lift_normal d a q w k r k' q' t :
  Num d a q w -> RC k q r -> RC k' q' t ->
  (k=O /\ k'=O \/ k'<k) -> k<=d -> exists q2 u,
  RC k q2 u /\ Normal (2^(1+d)-1-a) (1+d) u (w*>[1;1;0]*>T^^k*>[0]*>t).
Proof.
  intros HN HR HT Hk Hd; destruct k.
  - assert (k'=O) by lia; subst.
    destruct (RC_zero _ _ HT); subst.
    exists O, 0inf; split; [apply (RC_base 0)|].
    applys_eq (Normal_num _ _ _ _ HN _ _ _ _ (Normal_Z _ _ _ _ Normal_blank));
      cbn[Nat.pow Nat.add]; try nia; flia.
  - destruct (RC_mark k k' q' t HT ltac:(lia)) as
      [a2 [w2 [k2 [q2 [t2 [HN2 [HT2 [Hk2 [Hchild [HU HM]]]]]]]]]].
    eexists; eexists; split; [apply HU|].
    applys_eq (Normal_num _ _ _ _ HN _ _ _ _ HM);
      cbn[Nat.pow Nat.add]; try nia; flia.
Qed.

Lemma RC_mark_odd d a b w : Num (1+d) a b w -> b<2^d ->
  exists n, 2^(2+d)-1-a=1+n*2.
Proof.
  intros HN Hb; inverts HN.
  - match goal with H: Num _ _ _ _ |- _ => epose proof (Num_bounds _ _ _ _ H) end.
    exists (2^(1+d)-1-a0); cbn[Nat.pow Nat.add]; lia.
  - lia.
Qed.

Lemma filter_after j a b w p n k t r r' : Num j a b w ->
  sideRLs tm ([hb]^^p) r r' ->
  sideRLs tm ([hc]^^b++[hb]^^(1+n)++[hc]) r' (T^^k*>[0]*>t) ->
  Normal ((p+1+n)*2^j-a) (j+k) t (T^^j*>r).
Proof.
  intros HN HP HR; eapply filter_normal; [apply HN|].
  eapply sideRLs_trans; eauto.
Qed.

Lemma odd_core j s b z wb e v we p k t r r0 u :
  Num (1+j) b z wb -> Num s e v we -> O<z ->
  Normal (2^(2+j+s)-1-e-2^s*b) k t r ->
  Normal 1 1 u ([1;1;0]*>T^^k*>[0]*>t) ->
  sideRLs tm ([hb]^^p) r0 ([1;0;1;1;1;0]*>T^^s*>[0]*>r) ->
  exists f Q, O<f /\ f<=1+j /\ 2^(f-1)<=z<2^f /\
    Normal Q (3+j+s) u (T^^(1+j)*>r0) /\
    Q+3*2^f=(p+2^(1+s)+2+v*2)*2^(1+j)+z*2+1.
Proof.
  intros HZ HV Hz HR HM HP.
  epose proof (Num_bounds _ _ _ _ HV) as HVb.
  destruct (Num_complement _ _ _ _ HV) as [wc HC].
  inverts HZ.
  - match goal with H: Num j _ _ _ |- _ => rename H into HZ end.
    epose proof (Num_bounds _ _ _ _ HZ) as HZb.
    destruct (Num_half_Z _ _ _ _ HZ Hz) as [f [b' [wf [Hf [Hfj [Hfz [HF HE]]]]]]].
    destruct (Num_reverse _ _ _ _ (Num_snoc_Z _ _ _ _ HC)) as [wr Hrem].
    assert (HR': Normal (2^s+(2^(1+j)-a-1)*2^(1+s)+(2^s-1-e)) k t r).
    { applys_eq HR; rewrite ?Nat.pow_add_r; cbn[Nat.pow Nat.add]; nia. }
    epose proof (defect_high _ _ _ _ _ _ _ _ _ Hrem HR' HM) as HD.
    assert (HD': sideRLs tm ([hc]^^(2^(1+j)-a)++[hb]^^(1+(2^(1+s)+1+v*2))++[hc])
      ([1;0;1;1;1;0]*>T^^s*>[0]*>r) (T^^(2+s)*>[0]*>u)).
    { applys_eq HD; cbn[Nat.pow Nat.add]; flia. }
    epose proof (filter_after _ _ _ _ _ _ _ _ _ _ HF HP HD') as HH.
    exists f, ((p+1+(2^(1+s)+1+v*2))*2^(1+j)-b').
    repeat split; try assumption; try lia.
    + applys_eq HH; flia.
    + epose proof (Num_bounds _ _ _ _ HF); nia.
  - match goal with H: Num j _ _ _ |- _ => rename H into HZ end.
    epose proof (Num_bounds _ _ _ _ HZ) as HZb.
    destruct (Num_half_T _ _ _ _ HZ) as [wf HF].
    destruct (Num_reverse _ _ _ _ (Num_snoc_T _ _ _ _ HC)) as [wr Hrem].
    assert (HR': Normal (2^s+(2^(1+j)-a-2)*2^(1+s)+(2^s+(2^s-1-e))) k t r).
    { applys_eq HR; rewrite ?Nat.pow_add_r; cbn[Nat.pow Nat.add]; nia. }
    epose proof (defect_high _ _ _ _ _ _ _ _ _ Hrem HR' HM) as HD.
    assert (HD': sideRLs tm ([hc]^^(2^(1+j)-1-a)++[hb]^^(1+(2^(1+s)+v*2))++[hc])
      ([1;0;1;1;1;0]*>T^^s*>[0]*>r) (T^^(2+s)*>[0]*>u)).
    { applys_eq HD; cbn[Nat.pow Nat.add]; flia. }
    epose proof (filter_after _ _ _ _ _ _ _ _ _ _ HF HP HD') as HH.
    exists (1+j), ((p+1+(2^(1+s)+v*2))*2^(1+j)-(2^(1+j)-1-b0*2)).
    repeat split; try lia.
    + replace (1+j-1) with j by lia; lia.
    + cbn[Nat.pow Nat.add]; lia.
    + applys_eq HH; flia.
    + epose proof (Num_bounds _ _ _ _ HF); cbn[Nat.pow Nat.add]; nia.
Qed.

Lemma Num_prepare d a b w : Num d a b w -> forall r v,
  Normal 1 1 v r -> sideRLs tm [hb] ([1;0]*>r) ([1;0;1;1;1;0;0]*>v) ->
  exists j s p r0, d=j+s /\
    [1;0]*>w*>r=T^^j*>r0 /\ p*2^j+a+1=2^(1+d) /\
    (j<d -> a+2^j<2^d) /\ (a+1<2^d -> j<d) /\
    (j=O -> exists m, a=m*2) /\
    sideRLs tm ([hb]^^p) r0 ([1;0;1;1;1;0]*>T^^s*>[0]*>v).
Proof.
  intro H; induction H; intros r v HM HB.
  - exists O, O, 1%nat, ([1;0]*>r); repeat split; try reflexivity; try lia; auto.
    exists O; reflexivity.
  - epose proof (Num_bounds _ _ _ _ H) as Hbound.
    exists O, (1+d), (1+((1+1)*2^d-1-a)*2), ([1;0;1;1;0;0]*>w*>r).
    repeat split; try reflexivity; try (cbn[Nat.pow Nat.add]; lia).
    + intros; exists a; reflexivity.
    + epose proof (segRLs_sideRLs_concat (bridge_counts _)
        (Normal_C _ _ _ _ 1 (Normal_num _ _ _ _ H _ _ _ _ HM))) as HP.
      applys_eq HP; flia.
  - destruct (IHNum _ _ HM HB) as (j & s & p & r0 & Hd & Hw & Hp & Ha & Hj & Hpar & HP).
    exists (1+j), s, p, r0; repeat split; try lia.
    + change (T*>[1;0]*>w*>r=T*>T^^j*>r0); now rewrite Hw.
    + cbn[Nat.pow Nat.add] in Hp |- *; nia.
    + intro Hj'; specialize (Ha ltac:(lia)); cbn[Nat.pow Nat.add]; lia.
    + cbn[Nat.pow Nat.add]; lia.
    + apply HP.
Qed.

Lemma RC_prepare d k q r : RC k q r -> k<=d ->
  exists a w v q2 t qu u,
  Num d a q w /\ RC (1+d) (2^(1+d)-1-a) v /\
  Normal 1 1 v ([1;1;0]*>T^^(1+d)*>[0]*>r) /\
  sideRLs tm [hb] ([1;0]*>[1;1;0]*>T^^(1+d)*>[0]*>r) ([1;0;1;1;1;0;0]*>v) /\
  RC k q2 t /\ Normal (2^(1+d)-1-a) (1+d) t v /\
  RC (1+d) qu u /\ Normal 1 1 u ([1;1;0]*>T^^(1+d)*>[0]*>t) /\
  (k<d -> exists m, qu=1+m*2).
Proof.
  intros HR Hd.
  destruct (RC_mark _ _ _ _ HR Hd) as
    [a [w [k' [q' [t' [HN [HT [Hk [HNR [HV HM]]]]]]]]]].
  destruct (RC_lift_normal _ _ _ _ _ _ _ _ _ HN HR HT Hk Hd) as [q2 [t [HT2 HNV]]].
  destruct (RC_mark _ _ _ _ HT2 Hd) as
    [a2 [w2 [k2 [q3 [t2 [HN2 [HT3 [Hk2 [HNT [HU HM2]]]]]]]]]].
  do 7 eexists; repeat split; eauto using allones_first.
  intro Hkd; destruct d; [lia|].
  eapply RC_mark_odd; [apply HN2|].
  epose proof (RC_bounds _ _ _ HT2); epose proof (Nat.pow_le_mono_r 2 k d); lia.
Qed.

Lemma Num_split n : forall d a b w, Num (n+d) a b w ->
  exists a1 b1 w1 a2 b2 w2, Num n a1 b1 w1 /\ Num d a2 b2 w2 /\
    a=a1+2^n*a2 /\ b=b1*2^d+b2 /\ w=w1++w2.
Proof.
  induction n; intros d a b w H.
  - exists O, O, (@nil sym), a, b, w; repeat split; try constructor; auto; lia.
  - inverts H.
    + match goal with HH: Num _ _ _ _ |- _ => rename HH into HT end.
      destruct (IHn _ _ _ _ HT) as [a1 [b1 [w1 [a2 [b2 [w2 [H1 [H2 [Ha [Hb Hw]]]]]]]]]].
      exists (a1*2), b1, (Z++w1), a2, b2, w2.
      repeat split; try (apply Num_Z,H1); try assumption; subst;
        cbn[Nat.pow Nat.add]; try nia; reflexivity.
    + match goal with HH: Num _ _ _ _ |- _ => rename HH into HT end.
      destruct (IHn _ _ _ _ HT) as [a1 [b1 [w1 [a2 [b2 [w2 [H1 [H2 [Ha [Hb Hw]]]]]]]]]].
      exists (1+a1*2), (2^n+b1), (T++w1), a2, b2, w2.
      repeat split; try (apply Num_T,H1); try assumption; subst;
        rewrite ?Nat.pow_add_r; cbn[Nat.pow Nat.add]; try nia; reflexivity.
Qed.

Definition OCount d a q Q := exists j f z v,
  j<=d /\ O<f /\ f<=j /\ 2^(f-1)<=z<2^f /\
  q=v*2^j+z /\ Q+a+3*2^f=2^(2+d)+q*2+2^(1+j) /\
  (j<d -> a+2^j<2^d) /\ (a+1<2^d -> j<d).

Lemma odd_normal d a b w k q r : Num d (1+a*2) b w -> RC k (1+q*2) r -> k<=d ->
  exists Q qu u, RC (1+d) qu u /\
    Normal Q (2+d) u ([1;0]*>w*>[1;1;0]*>T^^(1+d)*>[0]*>r) /\
    OCount d (1+a*2) (1+q*2) Q /\ (k<d -> exists m, qu=1+m*2).
Proof.
  intros HN HR Hd.
  destruct (RC_prepare _ _ _ _ HR Hd) as
    (e & we & v & q2 & t & qu & u & HE & HV & HM & HB & HT & HNV & HU & HM2 & Hpar).
  destruct (Num_prepare _ _ _ _ HN _ _ HM HB) as
    (j & s & p & r0 & Hds & Hword & Hp & Ha & Hj & Hpar' & HP).
  destruct j; [destruct (Hpar' eq_refl); lia|].
  assert (HE': Num (s+(1+j)) e (1+q*2) we) by (applys_eq HE; flia).
  destruct (Num_split _ _ _ _ _ HE') as
    (e0 & v0 & w0 & b0 & z & wz & HE0 & HZ & He & Hq & Hw).
  assert (O<z) as Hz.
  { cbn[Nat.pow Nat.add] in Hq; nia. }
  assert (HNV': Normal (2^(2+j+s)-1-e0-2^s*b0) (1+d) t v).
  { applys_eq HNV; subst d e; cbn[Nat.pow Nat.add]; lia. }
  destruct (odd_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ HZ HE0 Hz HNV' HM2 HP) as
    (f & Q & Hf & Hfj & Hfz & Hnormal & HQ).
  exists Q, qu, u; split; [apply HU|]; split.
  - rewrite Hword; applys_eq Hnormal; flia.
  - split; [|apply Hpar].
    exists (1+j), f, z, v0; repeat split; try lia.
    subst d; rewrite ?Nat.pow_add_r in Hp,HQ |- *;
      cbn[Nat.pow Nat.add] in Hp,HQ,Hq |- *; nia.
    apply Ha.
Qed.

Lemma even_normal s a b w k q r : Num s a b w -> RC k q r -> k<=s ->
  exists qu u, RC (1+s) qu u /\
    Normal (2^(3+s)-a*2+q*4) (3+s) u
      ([1;0]*>Z*>w*>[1;1;0]*>T^^(1+s)*>[0]*>r) /\
    (k<s -> exists m, qu=1+m*2).
Proof.
  intros HN HR Hk.
  destruct (RC_prepare _ _ _ _ HR Hk) as
    (e & we & v & q2 & t & qu & u & HE & HV & HM & HB & HT & HNV & HU & HM2 & Hpar).
  exists qu, u; split; [apply HU|]; split; [eapply even_core; eauto|apply Hpar].
Qed.

Lemma OCount_bounds d a q Q : a<2^d -> q<2^d -> OCount d a q Q ->
  3*2^d<Q+1<6*2^d.
Proof.
  intros Ha Hq (j & f & z & v & Hjd & Hf & Hfj & Hz & Hqv & HQ & Ha' & Hj').
  assert (2^f<=2^j) as HPJ by (apply Nat.pow_le_mono_r; lia).
  assert (2^f<=z*2) as HPz.
  { destruct f; [lia|]; cbn[Nat.sub] in Hz; rewrite Nat.sub_0_r in Hz;
      cbn[Nat.pow]; lia. }
  assert (exists l, d=j+l) as [l Hd] by (exists (d-j); lia).
  assert (q+2^j<=2^d+z) as Hcap.
  { subst d; rewrite Nat.pow_add_r in Hq |- *.
    assert (v<2^l) by nia; nia. }
  cbn[Nat.pow Nat.add] in HQ; split; nia.
Qed.

Lemma OCount_odd d a q Q : OCount d (1+a*2) q Q -> exists m, Q=1+m*2.
Proof.
  intros (j & f & z & v & Hjd & Hf & Hfj & Hz & Hqv & HQ & Ha' & Hj').
  destruct f; [lia|]; cbn[Nat.pow Nat.add] in HQ.
  destruct (mod2 Q); subst; [lia|eauto].
Qed.

Lemma OCount_large d a q Q : d>O -> a+1<2^d -> 2^(d-1)<=q ->
  OCount d a q Q -> 2^(2+d)<Q.
Proof.
  intros Hd Ha Hq (j & f & z & v & Hjd & Hf & Hfj & Hz & Hqv & HQ & Ha' & Hj').
  specialize (Ha' (Hj' Ha)).
  assert (2^f<=2^j) by (apply Nat.pow_le_mono_r; lia).
  assert (2^d<=q*2).
  { destruct d; [lia|]; cbn[Nat.sub] in Hq; rewrite Nat.sub_0_r in Hq;
      cbn[Nat.pow]; lia. }
  cbn[Nat.pow Nat.add] in HQ |- *; lia.
Qed.

Lemma Num_even_notmax d a m w : d>O -> Num d a (m*2) w -> a+1<2^d.
Proof.
  intros Hd H; destruct (Num_reverse _ _ _ _ H) as [w' H'].
  inverts H'; try lia.
  match goal with H: Num _ _ _ _ |- _ => epose proof (Num_bounds _ _ _ _ H) end.
  cbn[Nat.pow Nat.add]; lia.
Qed.

Inductive Inv : (state*tape)%type -> Prop :=
| Inv_E s a b w k q r : Num s a b w -> RC k q r -> k<=s ->
    Inv (reset (Z++w) (1+s) r)
| Inv_O s a b w k q r : Num s a b w -> RC k (1+q*2) r -> k<=1+s ->
    (k=1+s -> a+1<2^s) -> Inv (reset (T++w) (2+s) r).

Lemma reset_next d Q r k q t : d>O -> Normal Q (2+d) t r -> RC k q t -> k<=1+d ->
  3*2^d<Q+1<6*2^d ->
  (Q+1<2^(2+d) -> (exists m, q=1+m*2) /\ (k=1+d -> exists m, Q=1+m*2)) ->
  exists c, lh {{B}}> [0]*>r -->+ c /\ Inv c.
Proof.
  intros Hd HN HR Hk HQ Hlow.
  destruct (le_lt_dec (2^(2+d)) (Q+1)) as [HH|HL].
  - assert (Q+1-2^(2+d)<2^(1+d)) as Hb by (cbn[Nat.pow Nat.add] in *; lia).
    destruct (Num_rev_ex _ _ Hb) as [a [w HW]].
    exists (reset (Z++w) (2+d) t); split.
    + eapply (left_return (2+d) O) with (q:=Q).
      * applys_eq (Num_Z _ _ _ _ HW); flia.
      * rewrite Nat.add_0_r; cbn[Nat.pow Nat.add]; cbn[Nat.pow Nat.add] in HH; lia.
      * apply HN.
    + applys_eq (Inv_E _ _ _ _ _ _ _ HW HR Hk); flia.
  - destruct (Hlow HL) as [[m Hm] Hodd]; subst q.
    assert (Q+1-3*2^d<2^d) as Hb by (cbn[Nat.pow Nat.add] in HL; lia).
    destruct (Num_rev_ex _ _ Hb) as [a [w HW]].
    exists (reset (T++w) (2+d) t); split.
    + eapply (left_return (1+d) O) with (q:=Q).
      * applys_eq (Num_T _ _ _ _ HW); flia.
      * rewrite Nat.add_0_r; cbn[Nat.pow Nat.add]; lia.
      * apply HN.
    + eapply Inv_O; eauto.
      intro Heq; destruct (Hodd Heq) as [v Hv].
      destruct (mod2 (Q+1-3*2^d)) as [n Hn|n Hn].
      * rewrite Hn in HW; eapply Num_even_notmax; eauto.
      * destruct d; [lia|]; cbn[Nat.pow] in Hn; lia.
Qed.

Lemma RC_upper d k q r : RC k q r -> k<=d -> q<2^d.
Proof.
  intros H Hd; epose proof (RC_bounds _ _ _ H); epose proof (Nat.pow_le_mono_r 2 k d); lia.
Qed.

Lemma Inv_step c : Inv c -> exists c', c -->+ c' /\ Inv c'.
Proof.
  intro H; destruct H as [s a b w k q r HN HR Hk|s a b w k q r HN HR Hk Ha].
  - destruct (even_normal _ _ _ _ _ _ _ HN HR Hk) as (qu & u & HU & HM & Hpar).
    epose proof (Num_bounds _ _ _ _ HN) as HNbound.
    epose proof (RC_upper _ _ _ _ HR Hk) as HRbound.
    eapply (reset_next (1+s)); [lia|apply HM|apply HU|lia| |].
    + cbn[Nat.pow Nat.add]; lia.
    + intro Hlow; assert (k<s) as Hks.
      { destruct (lt_dec k s); [assumption|].
        assert (k=s) by lia; subst k.
        epose proof (RC_bounds _ _ _ HR) as Hbound.
        destruct s; [cbn[Nat.pow Nat.add] in *; lia|].
        specialize (proj2 Hbound ltac:(lia)); intro Hq.
        cbn[Nat.sub] in Hq; rewrite Nat.sub_0_r in Hq.
        cbn[Nat.pow Nat.add] in Hlow,HNbound; lia. }
      split; [apply Hpar,Hks|lia].
  - epose proof (Num_T _ _ _ _ HN) as HW.
    destruct (odd_normal _ _ _ _ _ _ _ HW HR Hk) as (Q & qu & u & HU & HM & HC & Hpar).
    epose proof (Num_bounds _ _ _ _ HW) as HNbound.
    epose proof (RC_upper _ _ _ _ HR Hk) as HRbound.
    eapply (reset_next (1+s)); [lia|apply HM|apply HU|lia| |].
    + eapply OCount_bounds; [apply (proj1 HNbound)|apply HRbound|apply HC].
    + intro Hlow; assert (k<1+s) as Hks.
      { destruct (lt_dec k (1+s)); [assumption|].
        assert (k=1+s) by lia; subst k.
        specialize (Ha eq_refl).
        epose proof (RC_bounds _ _ _ HR) as Hbound.
        assert (1+a*2+1<2^(1+s)) by (cbn[Nat.pow Nat.add]; lia).
        epose proof (OCount_large (1+s) _ _ _ ltac:(lia) H (proj2 Hbound ltac:(lia)) HC); lia. }
      split; [apply Hpar,Hks|intros; eapply OCount_odd; apply HC].
Qed.

Lemma invariant_nonhalt c : Inv c -> ~halts tm c.
Proof.
  apply (progress_nonhalt tm Inv).
  intros x H; destruct (Inv_step _ H) as (y & Hy & HI); eauto.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply invariant_nonhalt; eapply Inv_E; [repeat constructor|apply (RC_base 1)|lia].
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LC---").
Definition rename q := match q with
  | A => D | B => E | C => B | D => C | E => F | F => A end.
Lemma perm : Perm tm TM1.tm rename.
Proof.
  split; intros [] [] * H; cbn in H; try discriminate; inverts H; reflexivity.
Qed.

Lemma init : c0 -[tm]->*
  0inf <* <[1;0] {{C}}>
  [0;1;0]*>[1;1;0;0]*>[1;0;1;0]*>[1;1;0]*>[1;0;1;0]^^2*>[0]*>0inf.
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (@perm_nonhalt tm TM1.tm rename C _); [apply perm|].
  apply TM1.invariant_nonhalt.
  change (TM1.Inv (TM1.reset ([1;1;0;0]++[1;0;1;0]) 2 0inf)).
  eapply TM1.Inv_E; [repeat constructor|apply (TM1.RC_base 0)|lia].
Qed.

End TM2.

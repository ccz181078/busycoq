From BusyCoq Require Import Individual62 Longitudinal ES_v3.
From BusyCoq Require Import BLECv2.
Require Import String List Arith ZArith Lia ZifyNat.
Import ListNotations.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB0LA_0RC0RA_1LF1RD_1RE0RD_1RC1RF_---1LA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation w := [0;0;1;1].
Notation d := [0;0;1;1;1;1].
Notation h := [((D,[0]),(B,[1]))].
Notation p := [((D,[1]),(A,[0]))].
Notation qh := [((D,[1]),(B,[1]))].
Definition G n r s := sideRLs tm (h^^n) r s.
Definition P n r s := sideRLs tm (p^^n) r s.

Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=500); reflexivity.

Lemma G_add a b r s t : G a r s -> G b s t -> G (a+b) r t.
Proof. unfold G; apply sideRLs_trans_add. Qed.
Lemma G_split a b r t : G (a+b) r t -> exists s, G a r s /\ G b s t.
Proof. unfold G; rewrite lpow_add; apply sideRLs_split. Qed.

Lemma wp n a : segRLs tm (h^^n) (h^^n) (w^^a) (w^^a).
Proof.
  induction a; [apply segRLs_nil|].
  cbn[lpow]; eapply segRLs_concat; [|apply IHa].
  eapply segRLs_wall''; finite_rule.
Qed.
Lemma G_w n a r s : G n r s -> G n (w^^a*>r) (w^^a*>s).
Proof. intro H; eapply segRLs_sideRLs_concat; [apply wp|exact H]. Qed.

Inductive Num : nat -> side -> Prop :=
| Num0 : Num 0 0inf
| Num00 n r : Num n r -> Num (n*3) ([0;0;0]*>r)
| Num01 n r : Num n r -> Num (n*3+1) ([0;1;1]*>r)
| Num02 n r : Num n r -> Num (n*3+2) ([0;0;1]*>r).

Lemma P_inc n r : Num n r -> exists s, Num (1+n) s /\ P 1 r s.
Proof.
  intro H; induction H.
  - exists ([0;1;1]*>0inf); split; [apply (Num01 0), Num0|].
    unfold P; es'.
  - exists ([0;1;1]*>r); split; [applys_eq (Num01 _ _ H); flia|].
    eapply segRLs_sideRLs_concat; [|constructor]; finite_rule.
  - exists ([0;0;1]*>r); split; [applys_eq (Num02 _ _ H); flia|].
    eapply segRLs_sideRLs_concat; [|constructor]; finite_rule.
  - destruct IHNum as [s [Hs Hp]].
    exists ([0;0;0]*>s); split; [applys_eq (Num00 _ _ Hs); flia|].
    eapply segRLs_sideRLs_concat; [|exact Hp]; finite_rule.
Qed.

Lemma G_inc n r : Num n r -> exists s, Num (1+n) s /\ G 1 r s.
Proof.
  intro H; destruct H.
  - exists ([0;1;1]*>0inf); split; [apply (Num01 0), Num0|].
    unfold G; es'.
  - exists ([0;1;1]*>r); split; [applys_eq (Num01 _ _ H); flia|].
    eapply segRLs_sideRLs_concat; [|constructor]; finite_rule.
  - exists ([0;0;1]*>r); split; [applys_eq (Num02 _ _ H); flia|].
    eapply segRLs_sideRLs_concat; [|constructor]; finite_rule.
  - destruct (P_inc _ _ H) as [s [Hs Hp]].
    exists ([0;0;0]*>s); split; [applys_eq (Num00 _ _ Hs); flia|].
    eapply segRLs_sideRLs_concat; [|exact Hp]; finite_rule.
Qed.

Lemma G_incs k n r : Num n r -> exists s, Num (n+k) s /\ G k r s.
Proof.
  gen n r; induction k; intros n r H.
  - exists r; split; [applys_eq H; flia|constructor].
  - destruct (G_inc _ _ H) as [s [Hs H1]].
    destruct (IHk _ _ Hs) as [t [Ht Hk]].
    exists t; split; [applys_eq Ht; flia|].
    change (G (1+k) r t); eapply G_add; eassumption.
Qed.

Lemma dw a : segRLs tm h (h^^2)
  (d++w^^(2+a)) (w^^2++d++w^^a).
Proof.
  change (segRLs tm h (h^^2) ((d++w++w)++w^^a) ((w++w++d)++w^^a)).
  eapply segRLs_concat; [|apply (wp 2 a)]; finite_rule.
Qed.

Lemma G_dw n a r s : G (n*2) r s ->
  G n (d*>w^^(n*2+a)*>r) (w^^(n*2)*>d*>w^^a*>s).
Proof.
  gen r s; induction n; intros r s H.
  - inverts H; constructor.
  - destruct (G_split 2 (n*2) r s H) as [t [H2 Hn]].
    eapply G_add with (a:=1%nat) (b:=n).
    + unfold G; cbn[lpow app].
      applys_eq (segRLs_sideRLs_concat (dw (n*2+a)) H2); flia.
    + applys_eq (G_w n 2 _ _ (IHn _ _ Hn)); flia.
Qed.

Lemma extra n r s : G 1 r s ->
  G 1 ([0;0;1]^^(1+n)*>1>>r) (w*>[0;0;0]^^n*>s).
Proof.
  intro H; unfold G; econstructor; [intros l; cbn[to_DH_config]|constructor].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H).
  cbn[to_DH_config]; es' n & l s.
Qed.

Lemma fill_digit t :
  segRLs tm (p^^(t*3+2)) (p^^t) [0;0;0] [0;0;1] /\
  segRLs tm (h^^(t*3+2)) (p^^t) [0;0;0] [0;0;1].
Proof.
  assert (Hp:segRLs tm (p^^3) (p^^1) [0;0;1] [0;0;1]) by finite_rule.
  assert (Hg:segRLs tm (h^^3) (p^^1) [0;0;1] [0;0;1]) by finite_rule.
  induction t as [|t [Ip Ig]]; [split; finite_rule|].
  split.
  - applys_eq (segRLs_trans Ip Hp); repeat rewrite <-lpow_add; unfold DH0; flia.
  - applys_eq (segRLs_trans Ig Hg); repeat rewrite <-lpow_add; unfold DH0; flia.
Qed.

Lemma fill_digits j :
  segRLs tm (p^^(3^j-1)) [] ([0;0;0]^^j) ([0;0;1]^^j) /\
  segRLs tm (h^^(3^j-1)) [] ([0;0;0]^^j) ([0;0;1]^^j).
Proof.
  induction j as [|j [Ip Ig]]; [split; constructor|].
  replace (3^S j-1) with ((3^j-1)*3+2) by (cbn[Nat.pow]; lia).
  split; cbn[lpow]; eapply segRLs_concat;
    [apply fill_digit|apply Ip|apply fill_digit|apply Ip].
Qed.

Lemma Num_zeros j n r : Num n r -> Num (n*3^j) ([0;0;0]^^j*>r).
Proof.
  intro H; induction j; cbn[lpow Nat.pow].
  - applys_eq H; flia.
  - applys_eq (Num00 _ _ IHj); flia.
Qed.

Lemma recover1 j n r : Num n r -> exists s,
  Num ((n+1)*3^j) s /\
  G (3^j) ([0;0;0]^^j*>[0;0;1]*>1>>r) (w*>s).
Proof.
  intro H; destruct (G_inc _ _ H) as [s [Hs Hg]].
  exists ([0;0;0]^^j*>s); split.
  - applys_eq (Num_zeros j _ _ Hs); flia.
  - replace (3^j) with ((3^j-1)+1) at 1 by lia.
    eapply G_add.
    + eapply segRLs_sideRLs_concat; [apply fill_digits|constructor].
    + rewrite lpow_shift'; apply extra; exact Hg.
Qed.

Lemma recover2 j n r : Num n r -> exists s,
  Num ((n+1)*3^j) s /\
  G (3^(1+j)) ([0;0;0]^^(1+j)*>1>>r) (w*>s).
Proof.
  intro H; destruct (G_inc _ _ H) as [s [Hs Hg]].
  exists ([0;0;0]^^j*>s); split.
  - applys_eq (Num_zeros j _ _ Hs); flia.
  - replace (3^(1+j)) with ((3^(1+j)-1)+1) at 1 by lia.
    eapply G_add.
    + eapply segRLs_sideRLs_concat; [apply fill_digits|constructor].
    + apply extra; exact Hg.
Qed.

Lemma zero_cases n r : Num n r -> 0<n -> exists j c s, Num c s /\
  ((n=(c*3+1)*3^j /\ 0>>r=[0;0;0]^^j*>[0;0;1]*>1>>s) \/
   (n=(c*3+2)*3^j /\ 0>>r=[0;0;0]^^(1+j)*>1>>s)).
Proof.
  intro H; induction H; intro Hn; [lia| | |].
  - destruct (IHNum ltac:(lia)) as [j [c [s [Hs [[He Hr]|[He Hr]]]]]];
      exists (1+j), c, s; split; [exact Hs| |exact Hs|].
    + left; split; [change (n*3=(c*3+1)*(3*3^j)); nia|].
      change ([0;0;0]*>0>>r = [0;0;0]*>([0;0;0]^^j*>[0;0;1]*>1>>s)).
      rewrite Hr; reflexivity.
    + right; split; [change (n*3=(c*3+2)*(3*3^j)); nia|].
      change ([0;0;0]*>0>>r = [0;0;0]*>([0;0;0]^^(1+j)*>1>>s)).
      rewrite Hr; reflexivity.
  - exists 0%nat, n, r; split; [exact H|left; split; [lia|reflexivity]].
  - exists 0%nat, n, r; split; [exact H|right; split; [lia|reflexivity]].
Qed.

Lemma zero_recover n r : Num n r -> 0<n -> exists t v s,
  Num v s /\ G t (0>>r) (w*>s) /\ t*2<=n*3 /\ v*3<=t*3+n.
Proof.
  intros H Hn; destruct (zero_cases _ _ H Hn) as [j [c [s [Hs [[He Hr]|[He Hr]]]]]].
  - destruct (recover1 j _ _ Hs) as [s' [Hv Hg]].
    exists (3^j), ((c+1)*3^j), s'; repeat split; try assumption.
    + rewrite Hr; exact Hg.
    + nia.
    + nia.
  - destruct (recover2 j _ _ Hs) as [s' [Hv Hg]].
    exists (3^(1+j)), ((c+1)*3^j), s'; repeat split; try assumption.
    + rewrite Hr; exact Hg.
    + change ((3*3^j)*2<=n*3); nia.
    + change ((c+1)*3^j*3<=(3*3^j)*3+n); nia.
Qed.

Inductive TailB : nat -> side -> Prop :=
| TB0 n r : Num n r -> TailB (n*3) (1>>r)
| TB1 n r : Num (n+1) r -> TailB (n*3+1) (0>>r)
| TB2 n r : Num (n+2) r -> TailB (n*3+2) (0>>r).

Lemma G_one n r : Num n r -> exists s, Num (n+2) s /\ G 1 (1>>r) (0>>s).
Proof.
  intro H; destruct (G_inc _ _ H) as [s [Hs Hg]].
  destruct (P_inc _ _ Hs) as [t [Ht Hp]].
  exists t; split; [applys_eq Ht; flia|].
  change (G 1 ([1]*>r) ([0]*>t)).
  eapply segRLs_sideRLs_concat; [|apply (sideRLs_trans Hg Hp)]; finite_rule.
Qed.

Lemma B_recover n r : TailB n r -> exists t v s,
  Num v s /\ G t r (w*>s) /\ t*2<=n+8 /\ v*9<=t*9+n+4.
Proof.
  intro H; destruct H.
  - destruct (G_one _ _ H) as [s [Hs H1]].
    destruct (zero_recover _ _ Hs ltac:(lia)) as [t [v [s' [Hv [Hg [Hb Hc]]]]]].
    exists (1+t), v, s'; repeat split; try assumption; try lia.
    eapply G_add; eassumption.
  - destruct (zero_recover _ _ H ltac:(lia)) as [t [v [s [Hv [Hg [Hb Hc]]]]]].
    exists t, v, s; repeat split; assumption || lia.
  - destruct (zero_recover _ _ H ltac:(lia)) as [t [v [s [Hv [Hg [Hb Hc]]]]]].
    exists t, v, s; repeat split; assumption || lia.
Qed.

Lemma G_d n r : Num n r -> exists s, TailB n s /\ G 1 (d*>r) (w^^2*>s).
Proof.
  intro H; destruct H.
  - exists (1>>0inf); split; [apply (TB0 0), Num0|unfold G; es'].
  - exists (1>>r); split; [constructor; assumption|].
    change (G 1 ((d++[0;0;0])*>r) ((w++w++[1])*>r)).
    eapply segRLs_sideRLs_concat; [|constructor]; finite_rule.
  - destruct (P_inc _ _ H) as [s [Hs Hp]].
    exists (0>>s); split; [constructor; applys_eq Hs; flia|].
    change (G 1 ((d++[0;1;1])*>r) ((w++w++[0])*>s)).
    eapply segRLs_sideRLs_concat; [|exact Hp]; finite_rule.
  - destruct (P_inc _ _ H) as [s [Hs Hp]].
    destruct (G_inc _ _ Hs) as [t [Ht Hg]].
    exists (0>>t); split; [constructor; applys_eq Ht; flia|].
    change (G 1 ((d++[0;0;1])*>r) ((w++w++[0])*>t)).
    eapply segRLs_sideRLs_concat; [|apply (sideRLs_trans Hp Hg)]; finite_rule.
Qed.

Inductive Twice : side -> side -> Prop :=
| Twice_intro r s t : G 1 r s -> G 1 (0>>s) t -> Twice r (0>>t).
Definition SM m r t := exists s, G m r s /\ Twice s t.

Lemma zero_w r : G 1 (0>>w*>r) ([0;1;1;1;1]*>r).
Proof. unfold G; es' & r. Qed.

Lemma Twice_hit r s : G 1 r (w*>s) -> Twice r (d*>s).
Proof. intro H; econstructor; [exact H|apply zero_w]. Qed.

Lemma Twice_w r s : G 1 r s -> Twice (w*>r) (d*>s).
Proof. intro H; apply Twice_hit, (G_w 1 1), H. Qed.

Lemma dw1 r s : SM 1 r s -> G 1 (d*>w*>r) (w^^2*>s).
Proof.
  intros [u [Hu Ht]]; inversion Ht as [v x y Hx Hy]; subst.
  unfold G; econstructor; [intros l; cbn[to_DH_config]|constructor].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ Hu).
  cbn[to_DH_config]; es; er.
  follow100 (sideRLs_1 _ _ _ _ _ Hx).
  cbn[to_DH_config].
  mid ([0;1;1;1;1;0;1;1;1;0]*>l {{D}}> 0>>x); [es' & l x|].
  follow100 (sideRLs_1 _ _ _ _ _ Hy); cbn[to_DH_config]; es' & l y.
Qed.

Lemma SM_col m r s : SM (m*2+1) r s ->
  SM m (d*>w^^(m*2+1)*>r) (d*>w^^(m*2+1)*>s).
Proof.
  intros [u [Hu Ht]]; destruct (G_split (m*2) 1 _ _ Hu) as [v [Hv H1]].
  assert (Hd: G 1 (d*>w*>v) (w^^2*>s)) by (apply dw1; exists u; auto).
  exists (w^^(m*2)*>d*>w*>v); split.
  - apply G_dw, Hv.
  - destruct m as [|m].
    + apply Twice_hit, Hd.
    + replace (S m*2+1) with ((m*2+1)+2) by lia.
      replace (S m*2) with (1+(m*2+1)) by lia.
      rewrite (lpow_add _ 1 (m*2+1)), (lpow_add _ (m*2+1) 2).
      repeat rewrite Str_app_assoc.
      exact (Twice_w _ _ (G_w 1 (m*2+1) _ _ Hd)).
Qed.

Definition cfg (r:side) := 0inf << 1 {{D}}> r.

Lemma root2 r s : G 1 r s -> cfg (w*>r) -->+ cfg (w*>0>>s).
Proof.
  intro H; unfold cfg; es; er.
  follow100 (sideRLs_1 _ _ _ _ _ H); cbn[to_DH_config]; es; er.
Qed.

Lemma root4 r s : Twice r s -> cfg (w*>r) -->+ cfg (w*>s).
Proof.
  intro H; destruct H; eapply progress_trans; apply root2; eassumption.
Qed.

Inductive Frame : nat -> list Sym -> Prop :=
| Frame0 : Frame 0 w
| FrameS a xs : Frame a xs -> Frame (a*2+1) (xs++d++w^^(a*2+1)).

Lemma Frame_run a xs : Frame a xs -> forall r s, SM a r s ->
  cfg (xs*>r) -->+ cfg (xs*>s).
Proof.
  intro H; induction H; intros r s [u [Hu Ht]].
  - inverts Hu; apply root4, Ht.
  - repeat rewrite Str_app_assoc; apply IHFrame, SM_col; exists u; auto.
Qed.

Lemma Frame_round a xs z y : Frame a xs -> G (a+1) (d*>z) (w*>y) ->
  cfg (xs*>d*>z) -->+ cfg (xs*>d*>y).
Proof.
  intros Hf Hg; apply (Frame_run _ _ Hf).
  destruct (G_split a 1 _ _ Hg) as [r [Ha H1]].
  exists r; split; [exact Ha|apply Twice_hit, H1].
Qed.

Inductive Suffix : nat -> nat -> side -> Prop :=
| SN q r : Num q r -> Suffix 0 q r
| SMixed j n r s : Num n s -> G (j*2) r (w*>s) ->
    Suffix (j+1) (n+2) (w^^(j*2+1)*>r).

Lemma Suffix_run i q z : Suffix i q z -> exists r,
  Num q r /\ G i (d*>z) (w^^(i*2)*>d*>r).
Proof.
  intro H; destruct H.
  - exists r; split; [exact H|constructor].
  - destruct (G_incs 2 _ _ H) as [t [Ht Hg]].
    exists t; split; [exact Ht|].
    eapply G_add with (a:=j) (b:=1%nat).
    + apply (G_dw j 1 _ _ H0).
    + replace ((j+1)*2) with (j*2+2) by lia.
      rewrite (lpow_add _ (j*2) 2), Str_app_assoc.
      exact (G_w 1 (j*2) _ _ (G_dw 1 0 _ _ Hg)).
Qed.

Inductive Inv : (Q * tape)%type -> Prop :=
| Inv_intro a xs i q z : Frame a xs -> 32<=a+1 -> i<=a+1 ->
    q*2<=(a+1+i)*3 -> Suffix i q z -> Inv (cfg (xs*>d*>z)).

Lemma Inv_step c : Inv c -> exists c', Inv c' /\ c -->+ c'.
Proof.
  intro H; destruct H as [a xs i q z Hf Ha Hi Hq Hz].
  destruct (Suffix_run _ _ _ Hz) as [r [Hr Hrun]].
  destruct (Nat.eq_dec i (a+1)) as [He|He].
  - subst i.
    exists (cfg ((xs++d++w^^(a*2+1))*>d*>r)); split.
    + eapply Inv_intro with (i:=0%nat) (q:=q); [constructor; exact Hf|lia|lia|lia|].
      constructor; exact Hr.
    + repeat rewrite Str_app_assoc; apply (Frame_round _ _ _ _ Hf).
      replace ((a+1)*2) with (1+(a*2+1)) in Hrun by lia.
      rewrite lpow_add, Str_app_assoc in Hrun; exact Hrun.
  - assert (Hi':i<=a) by lia.
    destruct (G_d _ _ Hr) as [b [Hb Hd]].
    destruct (B_recover _ _ Hb) as [tau [v [s [Hs [Htau [Ht Hv]]]]]].
    assert (Hbound:tau<=a+i) by lia.
    destruct (G_incs (a+i-tau) _ _ Hs) as [t [Ht_num Ht_run]].
    assert (Hall:G (a+i) b (w*>t)).
    { replace (a+i) with (tau+(a+i-tau)) by lia.
      eapply G_add; [exact Htau|apply (G_w _ 1), Ht_run]. }
    replace (a+i) with ((a-i)+i*2) in Hall by lia.
    destruct (G_split (a-i) (i*2) _ _ Hall) as [u [Hu Hrest]].
    exists (cfg (xs*>d*>w^^(i*2+1)*>u)); split.
    + eapply Inv_intro with (i:=i+1) (q:=v+(a+i-tau)+2);
        [exact Hf|lia|lia|lia|].
      econstructor; eassumption.
    + apply (Frame_round _ _ _ _ Hf).
      replace (a+1) with (i+(1+(a-i))) by lia.
      eapply G_add; [exact Hrun|].
      eapply G_add with (a:=1%nat) (b:=a-i).
      * apply (G_w _ (i*2)), Hd.
      * rewrite <-Str_app_assoc, <-lpow_add.
        replace (i*2+2) with (1+(i*2+1)) by lia.
        apply (G_w _ 1), (G_w _ (i*2+1)), Hu.
Qed.

Fixpoint prefix n := match n with
| O => w
| S n => prefix n ++ d ++ w^^(2^(1+n)-1)
end.

Lemma prefix_spec n : Frame (2^n-1) (prefix n).
Proof.
  induction n; [apply Frame0|].
  cbn[prefix]; replace (2^S n-1) with ((2^n-1)*2+1) by (cbn[Nat.pow]; lia).
  replace (2^(1+n)-1) with ((2^n-1)*2+1) by (change ((2^n-1)*2+1=2*2^n-1); lia).
  constructor; exact IHn.
Qed.

Definition initial := cfg (prefix 5 *> d *> [0;0;1;0;0;1;0;0;0;0;1;1] *> 0inf).

Lemma init : c0 -->* initial.
Proof.
  apply without_counter with (n:=305021).
  apply multistep_c_spec; vm_compute; repeat f_equal.
  change (0>>0inf=0inf); rewrite <-const_unfold; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt; [apply Inv_step|].
  unfold initial; eapply Inv_intro with (i:=0%nat) (q:=35%nat).
  - apply prefix_spec.
  - cbn; lia.
  - cbn; lia.
  - cbn; lia.
  - constructor; apply (Num02 11), (Num02 3), (Num00 1), (Num01 0), Num0.
Qed.

End TM5.

Module TM4.
Module O := BLECv2.TM4.
Import O.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LE_1RD0RC_1RE1RC_1LF0LE_1LA0LB").
Notation Hs := [((A,[]),(E,[]))].
Notation z0 := [0;0;0;0].
Notation z1 := [0;0;0;1].
Notation v := [0;0;0;1;1].
Definition LH n l l' := sideRLs (flip O.tm) (Hs^^n) l l'.

Definition rename q := match q with A=>E | B=>F | C=>A | D=>B | E=>C | F=>D end.
Lemma correspondence : Perm O.tm tm rename.
Proof. split; intros [] [] * H; cbn in H; inversion H; reflexivity. Qed.

Lemma LH_add a b l l' l'' : LH a l l' -> LH b l' l'' -> LH (a+b) l l''.
Proof. unfold LH; apply sideRLs_trans_add. Qed.

Lemma LH_inc m k ls l : LC k ls l -> exists l', LC (k+m) ls l' /\ LH m l l'.
Proof. apply LIncs. Qed.

Lemma LH_word n l l' : LH n l l' -> LH n (v*>l) (v*>l').
Proof.
  intro H; eapply segRLs_sideRLs_concat; [|exact H].
  apply segRLs_wall''; apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.
Qed.

Lemma LH_zero n l l' : LH n l l' -> LH (n*2) (z0*>l) (z0*>l').
Proof.
  intro H; eapply segRLs_sideRLs_concat; [|exact H].
  replace (n*2) with (n*2+0) by lia.
  eapply segRLs_addmul'';
    apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.
Qed.

Lemma LH_cross l l' : LH 3 l l' -> LH 2 (0>>v*>l) (v*>0>>l').
Proof.
  intro H; change (LH 2 ([0;0;0;0;1;1]*>l) ([0;0;0;1;1;0]*>l')).
  eapply segRLs_sideRLs_concat; [|exact H].
  apply BoundedConfig.segRLs_c_spec with (T:=200); reflexivity.
Qed.

Definition up ls := match ls with []=>[] | h::ls => (1+h)::ls end.

Lemma LC_even_intro n ls l : LC n ls l -> LC (n*2) (up ls) (z0*>l).
Proof.
  intro H; destruct ls as [|h ls].
  - destruct n.
    + inversion H; subst; try lia.
      change (LC 0 [] (0>>0>>0>>0>>0inf)); repeat rewrite <-const_unfold; constructor.
    + applys_eq (LC_2 n _ H); flia.
  - apply LC_0', H.
Qed.

Lemma LC_even n ls l : LC (n*2) (up ls) l ->
  exists l', LC n ls l' /\ l=z0*>l'.
Proof.
  destruct ls as [|h ls]; intro H; inversion H; subst; cbn[up] in *; try discriminate; try lia.
  - exists 0inf; split; [applys_eq LC_0; flia|].
    change (0inf=0>>0>>0>>0>>0inf); repeat rewrite <-const_unfold; reflexivity.
  - eexists; split; [applys_eq H1; flia|reflexivity].
  - eexists; split; [applys_eq H4; flia|reflexivity].
Qed.

Lemma LC_odd n ls l : LC (n*2+1) (up ls) l ->
  exists l', LC n ls l' /\ l=z1*>l'.
Proof.
  destruct ls as [|h ls]; intro H; inversion H; subst; cbn[up] in *; try discriminate; try lia.
  - eexists; split; [applys_eq H1; flia|reflexivity].
  - eexists; split; [applys_eq H4; flia|reflexivity].
Qed.

Inductive Reset : nat -> list nat -> nat -> nat -> list nat -> Prop :=
| RZero : Reset 0 [] 0 0 []
| ROdd n ls : Reset (n*2+1) (up ls) 1 n (O::ls)
| REven n ls c k ls' : Reset n ls c k ls' ->
    Reset (n*2) (up ls) (c*2) (k*2) (up ls')
| RMark n ls c k ls' : Reset (n+3) ls c k ls' ->
    Reset n (O::ls) (2+c) k (O::ls').

Lemma Reset_spec n ls c k ls' : Reset n ls c k ls' -> forall l,
  LC n ls l -> exists l', LC k ls' l' /\ LH c (0>>l) l'.
Proof.
  intro H; induction H; intros l Hl.
  - inversion Hl; subst; try lia. exists 0inf; split; [constructor|].
    rewrite <-const_unfold; constructor.
  - destruct (LC_odd _ _ _ Hl) as [l' [Hl' ->]].
    exists (v*>l'); split; [constructor; exact Hl'|].
    unfold LH; es' & l'.
  - destruct (LC_even _ _ _ Hl) as [l0 [Hl0 ->]].
    destruct (IHReset _ Hl0) as [l' [Hl' Hr]].
    exists (z0*>l'); split; [apply LC_even_intro, Hl'|apply LH_zero, Hr].
  - inversion Hl; subst; try lia.
    destruct (LH_inc 3 _ _ _ H2) as [l1 [Hl0 H3]].
    destruct (IHReset _ Hl0) as [l' [Hl' Hr]].
    exists (v*>l'); split; [constructor; exact Hl'|].
    eapply LH_add; [apply LH_cross, H3|apply LH_word, Hr].
Qed.

Lemma flip_back_step c c' : c -[flip O.tm]-> c' ->
  flip_conf c -[O.tm]-> flip_conf c'.
Proof.
  intro H; inversion H; subst; cbn[flip_conf flip_tape move_left move_right];
    apply step_right || apply step_left;
    match goal with H:flip O.tm (?q,?s)=_ |- _ => destruct q,s; cbn in H |- *;
      inversion H; reflexivity end.
Qed.

Lemma flip_back c c' : c -[flip O.tm]->+ c' ->
  flip_conf c -[O.tm]->+ flip_conf c'.
Proof. intro H; induction H; eauto using flip_back_step. Qed.

Lemma LH_first n l l' : LH (1+n) l l' -> exists l0,
  LH n l0 l' /\ forall r, l <{{A}} r -[O.tm]->+ l0 {{E}}> r.
Proof.
  intro H; inversion H; subst.
  eexists; split; [eassumption|].
  intro r; match goal with Hcall:sideRL _ _ _ _ _ |- _ =>
    apply (flip_back _ _ (Hcall r)) end.
Qed.

Lemma phase_calls n l l' r r' : LH (1+n) l l' ->
  sideRLs O.tm ([((E,[]),(A,[]))]^^n) r r' ->
  l <{{A}} r -[O.tm]->+ l' {{E}}> r'.
Proof.
  gen l l' r r'; induction n; intros l l' r r' HL HR.
  - inversion HR; subst; destruct (LH_first _ _ _ HL) as [l0 [HL0 Hleft]].
    inversion HL0; subst; apply Hleft.
  - destruct (LH_first _ _ _ HL) as [l0 [HL0 Hleft]].
    inversion HR; subst.
    eapply progress_trans; [apply Hleft|].
    eapply progress_trans;
      [match goal with Hcall:sideRL _ _ _ _ _ |- _ => apply Hcall end|].
    eapply IHn; eassumption.
Qed.

Lemma Phase n t r l l' : RC (n*3+5) t r -> LH (n+4+offset t) (0>>l) l' ->
  exists r', RC (n*3+5) (nxt t) r' /\ l {{E}}> r -[O.tm]->+ l' {{E}}> r'.
Proof.
  intros Hr Hl; destruct (ROv _ _ _ Hr) as [r0 [Hr0 H0]].
  destruct (RIncs ((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2)) _ _ _ Hr0)
    as [r' [Hr' H1]].
  assert (He:((n+1+offset t)/3+(1-((n*2+(1-offset t)) mod 3)/2))*3+
      (2-(S(n*2+(1-offset t))) mod 3)=n+3+offset t) by (destruct t; cbn[offset]; lia).
  exists r'; split.
  - applys_eq Hr'; destruct t; cbn[offset] in *; lia.
  - eapply evstep_progress_trans; [apply H0|].
    apply (phase_calls (n+3+offset t)).
    + applys_eq Hl; flia.
    + rewrite He in H1; exact H1.
Qed.

Lemma Phase_reset n t r k ls c k' ls' l : RC (n*3+5) t r -> LC k ls l ->
  Reset k ls c k' ls' -> c<=n+4+offset t ->
  exists l' r', LC (k'+(n+4+offset t-c)) ls' l' /\
    RC (n*3+5) (nxt t) r' /\ l {{E}}> r -[O.tm]->+ l' {{E}}> r'.
Proof.
  intros Hr Hl Hreset Hc; destruct (Reset_spec _ _ _ _ _ Hreset _ Hl) as [l0 [Hl0 H0]].
  destruct (LH_inc (n+4+offset t-c) _ _ _ Hl0) as [l' [Hl' H1]].
  assert (H2:LH (n+4+offset t) (0>>l) l').
  { replace (n+4+offset t) with (c+(n+4+offset t-c)) by lia.
    eapply LH_add; eassumption. }
  destruct (Phase _ _ _ _ _ Hr H2) as [r' [Hr' Hrun]].
  exists l', r'; auto.
Qed.

Inductive State := st (k:nat) (ls:list nat) (n:nat) (t:Tp).
Inductive Next : State -> State -> Prop :=
| Drop k ls n t : Next (st k (O::ls) n t) (st (k+3) ls (n+1) t)
| Reset_next k ls n t c k' ls' : Reset k ls c k' ls' -> c<=n+4+offset t ->
    Next (st k ls n t) (st (k'+(n+4+offset t-c)) ls' n (nxt t)).
Definition Denote s l r := match s with st k ls n t => LC k ls l /\ RC (n*3+5) t r end.

Lemma Next_spec s s' : Next s s' -> forall l r, Denote s l r ->
  exists l' r', Denote s' l' r' /\ l {{E}}> r -[O.tm]->+ l' {{E}}> r'.
Proof.
  intro H; destruct H; intros l r [Hl Hr].
  - destruct (BigStep0 Hl Hr) as [l' [r' [Hl' [Hr' Hrun]]]].
    exists l', r'; split; [split; applys_eq Hl' || applys_eq Hr'; flia|exact Hrun].
  - destruct (Phase_reset _ _ _ _ _ _ _ _ _ Hr Hl H H0) as [l' [r' [Hl' [Hr' Hrun]]]].
    exists l', r'; split; [split; assumption|exact Hrun].
Qed.

Definition shift i ls := match ls with []=>[] | h::ls=>(i+h)::ls end.
Lemma Reset_scale i n ls c k ls' : Reset n ls c k ls' ->
  Reset (n*2^i) (shift i ls) (c*2^i) (k*2^i) (shift i ls').
Proof.
  intro H; induction i.
  - destruct ls, ls'; cbn[shift Nat.pow]; applys_eq H; flia.
  - applys_eq (REven _ _ _ _ _ IHi); destruct ls, ls'; cbn[shift up Nat.pow]; flia.
Qed.

Inductive Steps : State -> State -> Prop :=
| Done s : Steps s s
| Advance s t u : Next s t -> Steps t u -> Steps s u.

Lemma Steps_spec s s' : Steps s s' -> forall l r, Denote s l r ->
  exists l' r', Denote s' l' r' /\ l {{E}}> r -[O.tm]->* l' {{E}}> r'.
Proof.
  intro H; induction H; intros l r Hd.
  - exists l, r; split; [exact Hd|finish].
  - destruct (Next_spec _ _ H _ _ Hd) as [l0 [r0 [Hmid Hrun]]].
    destruct (IHSteps _ _ Hmid) as [l' [r' [H' Hrun']]].
    exists l', r'; split; [exact H'|apply progress_evstep; eapply progress_evstep_trans; eassumption].
Qed.

Lemma Reset_odd k ls n ls' : k=n*2+1 -> ls=up ls' -> Reset k ls 1 n (O::ls').
Proof. intros -> ->; constructor. Qed.
Lemma Reset_even k ls n ls0 c k' ls' : k=n*2 -> ls=up ls0 -> Reset n ls0 c k' ls' ->
  Reset k ls (c*2) (k'*2) (up ls').
Proof. intros -> ->; apply REven. Qed.

Ltac reset_bits tail_ls k :=
  first [solve [eapply Reset_odd with (n:=k/2) (ls':=tail_ls); cbn[up]; flia]
  | eapply Reset_even with (n:=k/2) (ls0:=tail_ls);
      [lia|cbn[up]; flia|reset_solve]]
with reset_solve :=
  cbn[up Nat.add Nat.sub];
  lazymatch goal with
  | |- Reset ?k (O::?ls) _ _ _ => eapply RMark; reset_solve
  | |- Reset ?k [] _ _ _ => reset_bits (@nil nat) k
  | |- Reset ?k (?h::?ls) _ _ _ => reset_bits ((h-1)::ls) k
  end.

Ltac phase :=
  repeat lazymatch goal with
  | |- Steps (st _ (O::_) _ _) _ => eapply Advance; [apply Drop|]
  end;
  eapply Advance; [eapply Reset_next; [reset_solve|cbn[offset]; lia]|];
  cbn[up nxt offset Nat.sub Nat.add Nat.mul].

Ltac phase_as k_new n_new :=
  phase; lazymatch goal with |-Steps (st ?k ?ls ?n ?t) _ =>
    replace (st k ls n t) with (st k_new ls n_new t) by flia end.

Definition RootG n := st (n*2+7) [0%nat] n t5.
Definition RootD h n := st (n*2+7-3*2^(h-1)) [0%nat;h] n t5.
Definition RootE n := st (n*2+3) [1%nat;0%nat] n t5.
Definition RootF n := st (n*2+3) [0%nat;0%nat;1%nat] n t5.

Lemma E_cycle n : 64<=n -> n mod 8=2 -> Steps (RootE n) (RootG (n+9)).
Proof.
  intros Hn Hmod; unfold RootE, RootG.
  phase_as (n*2+5) n; phase_as (n*2+11) (n+3).
  phase_as (n*2+12) (n+3); phase_as (n*2+15) (n+5).
  phase_as (n*2+16) (n+5); phase_as (n*2+19) (n+7).
  phase_as (n*2+19) (n+7); phase_as ((n+9)*2+7) (n+9); constructor.
Qed.

Lemma F_cycle n : 64<=n -> n mod 8=1%nat -> Steps (RootF n) (RootG (n+10)).
Proof.
  intros Hn Hmod; unfold RootF, RootG.
  phase_as (n*2+10) (n+2); phase_as (n*2+13) (n+4).
  phase_as (n*2+14) (n+4); phase_as (n*2+17) (n+6).
  phase_as (n*2+18) (n+6); phase_as (n*2+21) (n+8).
  phase_as (n*2+21) (n+8); phase_as ((n+10)*2+7) (n+10); constructor.
Qed.

Lemma D_shrink j n : 384*2^j<=n -> n mod 8=2 ->
  Steps (RootD (9+j) n) (RootD (1+j) (n+8)).
Proof.
  intros Hn Hmod; unfold RootD.
  replace (9+j-1) with (8+j) by lia.
  replace (1+j-1) with j by lia.
  rewrite Nat.pow_add_r; cbn[Nat.pow].
  phase_as (n*2+8-384*2^j) (n+1).
  phase_as (n*2+5-192*2^j) (n+1).
  phase_as (n*2+7-96*2^j) (n+1).
  phase_as (n*2+10-48*2^j) (n+4).
  phase_as (n*2+11-24*2^j) (n+4).
  phase_as (n*2+12-12*2^j) (n+4).
  phase_as (n*2+20-6*2^j) (n+7).
  phase_as ((n+8)*2+7-3*2^j) (n+8).
  applys_eq (Done (st ((n+8)*2+7-3*2^j) [0%nat;1+j] (n+8) t5)); flia.
Qed.


Lemma D_small h n : 1<=h<=5 -> 64<=n -> n mod 8=2 ->
  Steps (RootD h n) (RootG (n+9)).
Proof.
  intros Hh Hn Hmod; destruct h as [|[|[|[|[|[|h]]]]]]; try lia;
    unfold RootD, RootG; cbn[Nat.pow Nat.sub].
  - phase_as (n*2+8) (n+1);
    phase_as (n*2+11) (n+3);
    phase_as (n*2+12) (n+3);
    phase_as (n*2+15) (n+5);
    phase_as (n*2+16) (n+5);
    phase_as (n*2+19) (n+7);
    phase_as (n*2+19) (n+7);
    phase_as (n*2+25) (n+9);
    applys_eq (Done (st ((n+9)*2+7) [0%nat] (n+9) t5)); flia.
  - phase_as (n*2+0) (n+1);
    phase_as (n*2-5) (n+1);
    phase_as (n*2+2) (n+1);
    phase_as (n*2+7) (n+2);
    phase_as (n*2+19) (n+6);
    phase_as (n*2+19) (n+7);
    phase_as (n*2+19) (n+7);
    phase_as (n*2+25) (n+9);
    applys_eq (Done (st ((n+9)*2+7) [0%nat] (n+9) t5)); flia.
  - phase_as (n*2+2) (n+1);
    phase_as (n*2-9) (n+1);
    phase_as (n*2+0) (n+1);
    phase_as (n*2+1) (n+3);
    phase_as (n*2+7) (n+3);
    phase_as (n*2+14) (n+5);
    phase_as (n*2+22) (n+8);
    phase_as (n*2+25) (n+9);
    applys_eq (Done (st ((n+9)*2+7) [0%nat] (n+9) t5)); flia.
  - phase_as (n*2-4) (n+1);
    phase_as (n*2-1) (n+1);
    phase_as (n*2+4) (n+1);
    phase_as (n*2+13) (n+4);
    phase_as (n*2+19) (n+6);
    phase_as (n*2+19) (n+7);
    phase_as (n*2+19) (n+7);
    phase_as (n*2+25) (n+9);
    applys_eq (Done (st ((n+9)*2+7) [0%nat] (n+9) t5)); flia.
  - phase_as (n*2-16) (n+1);
    phase_as (n*2-7) (n+1);
    phase_as (n*2+1) (n+1);
    phase_as (n*2+10) (n+4);
    phase_as (n*2+9) (n+4);
    phase_as (n*2+11) (n+4);
    phase_as (n*2+22) (n+8);
    phase_as (n*2+25) (n+9);
    applys_eq (Done (st ((n+9)*2+7) [0%nat] (n+9) t5)); flia.
Qed.

Lemma D7 n : 96<=n -> n mod 8=2 ->
  Steps (RootD 7 n) (RootF (n+7)).
Proof.
  intros Hn Hmod; unfold RootD, RootF; cbn[Nat.pow Nat.sub].
  phase_as (n*2-88) (n+1);
  phase_as (n*2-43) (n+1);
  phase_as (n*2-17) (n+1);
  phase_as (n*2-2) (n+4);
  phase_as (n*2+5) (n+4);
  phase_as (n*2+9) (n+4);
  phase_as (n*2+13) (n+7);
  phase_as (n*2+17) (n+7);
  applys_eq (Done (st ((n+7)*2+3) [0%nat;0%nat;1%nat] (n+7) t5)); flia.
Qed.

Lemma D8 n : 192<=n -> n mod 8=2 ->
  Steps (RootD 8 n) (RootE (n+8)).
Proof.
  intros Hn Hmod; unfold RootD, RootE; cbn[Nat.pow Nat.sub].
  phase_as (n*2-184) (n+1);
  phase_as (n*2-91) (n+1);
  phase_as (n*2-41) (n+1);
  phase_as (n*2-14) (n+4);
  phase_as (n*2-1) (n+4);
  phase_as (n*2+6) (n+4);
  phase_as (n*2+17) (n+7);
  phase_as (n*2+19) (n+8);
  applys_eq (Done (st ((n+8)*2+3) [1%nat;0%nat] (n+8) t5)); flia.
Qed.

Lemma D6_even n : 64<=n -> n mod 16=10 ->
  Steps (RootD 6 n) (RootE (n+8)).
Proof.
  intros Hn Hmod; unfold RootD, RootE; cbn[Nat.pow Nat.sub].
  phase_as (n*2-40) (n+1);
  phase_as (n*2-19) (n+1);
  phase_as (n*2-5) (n+1);
  phase_as (n*2-18) (n+4);
  phase_as (n*2-3) (n+4);
  phase_as (n*2+5) (n+4);
  phase_as (n*2+14) (n+6);
  phase_as (n*2+19) (n+8);
  applys_eq (Done (st ((n+8)*2+3) [1%nat;0%nat] (n+8) t5)); flia.
Qed.

Lemma init : exists l r, Denote (RootG 11) l r /\ c0 -[tm]->* l {{C}}> r.
Proof.
  do 2 eexists; split.
  - split.
    + apply LC_w, (LC_1 14), (LC_2 6), (LC_1 3), (LC_1 1), (LC_1 0), LC_0.
    + apply (RC_5 11), (RC_4 6), (RC_4 3), (RC_3 1), (RC_3 0), RC_0.
  - apply without_counter with (n:=11347); apply multistep_c_spec.
    vm_compute; repeat f_equal; try reflexivity.
Qed.

Lemma Reset_power i u :
  Reset ((u*2+1)*2^i) [] (2^i) (u*2^i) [i].
Proof.
  applys_eq (Reset_scale i _ _ _ _ _ (ROdd u [])); cbn[shift]; flia.
Qed.

Lemma Reset_cross a u : Reset ((u*2+3)*32*2^a-24) [3%nat]
  (16+32*2^a) ((u+1)*32*2^a) [3%nat;a+2].
Proof.
  assert (H:Reset (((u*2+3)*2^(a+2)-3)+3) [] (2^(a+2)) ((u+1)*2^(a+2)) [a+2]).
  { applys_eq (Reset_power (a+2) (u+1)); rewrite Nat.pow_add_r; cbn[Nat.pow]; nia. }
  apply RMark in H; apply (Reset_scale 3) in H.
  cbn[shift Nat.pow] in H; rewrite Nat.pow_add_r in H; cbn[Nat.pow] in H.
  applys_eq H; nia.
Qed.

Lemma D6_odd_ge3 a u n : 64<=n -> n+14=(u*2+3)*16*2^a ->
  Steps (RootD 6 n) (RootD (1+a) (n+8)).
Proof.
  intros Hn Hval.
  assert (Hlow:48*2^a<=n+14) by (rewrite Hval; apply Nat.mul_le_mono_r; lia).
  assert (Hmod:n mod 8=2).
  { replace ((u*2+3)*16*2^a) with (((u*2+3)*2^a)*16) in Hval by ring; lia. }
  unfold RootD; replace (1+a-1) with a by lia; cbn[Nat.pow Nat.sub].
  phase_as (n*2-40) (n+1).
  phase_as (n*2-19) (n+1).
  phase_as (n*2-5) (n+1).
  do 3 (eapply Advance; [apply Drop|]).
  eapply Advance; [eapply Reset_next|].
  - applys_eq (Reset_cross a u); nia.
  - cbn[offset]; nia.
  - cbn[nxt offset].
    lazymatch goal with |-Steps (st ?k ?ls ?n0 ?t) _ =>
      replace (st k ls n0 t) with (st (n*2+6-48*2^a) ls (n+4) t) by (f_equal; nia) end.
    phase_as (n*2+9-24*2^a) (n+4).
    phase_as (n*2+11-12*2^a) (n+4).
    phase_as (n*2+17-6*2^a) (n+6).
    phase_as ((n+8)*2+7-3*2^a) (n+8).
    applys_eq (Done (st ((n+8)*2+7-3*2^a) [0%nat;1+a] (n+8) t5)); flia.
Qed.

Lemma LH_one n l l' : LH n l l' -> LH (n*2) (z1*>l) (z1*>l').
Proof.
  intro H; eapply segRLs_sideRLs_concat; [|exact H].
  replace (n*2) with (n*2+0) by lia.
  eapply segRLs_addmul'';
    apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.
Qed.

Lemma LH_zeros j n l l' : LH n l l' -> LH (n*2^j) (z0^^j*>l) (z0^^j*>l').
Proof.
  intro H; induction j.
  - applys_eq H; flia.
  - applys_eq (LH_zero _ _ _ IHj); cbn[lpow Nat.pow]; flia.
Qed.

Lemma G_start j u n : 2<=j -> n+5=(u*2+3)*2^(1+j) ->
  Steps (RootG n) (st (n*2+9-3*2^j) [0%nat;1+j] (n+1) t7).
Proof.
  intros Hj Hval.
  change (n+5=(u*2+3)*(2*2^j)) in Hval.
  assert (Hlow:6*2^j<=n+5).
  { rewrite Hval; nia. }
  unfold RootG; eapply Advance; [apply Drop|].
  eapply Advance; [eapply Reset_next|].
  - applys_eq (Reset_power (2+j) (u+1)).
    change (n*2+7+3=((u+1)*2+1)*(2*(2*2^j))); nia.
  - change (2*(2*2^j)<=n+1+4+1); lia.
  - cbn[nxt offset].
    replace (st ((u+1)*2^(2+j)+(n+1+4+1-2^(2+j))) [2+j] (n+1) t6)
      with (st (n*2+11-6*2^j) [2+j] (n+1) t6).
    2: { change (st (n*2+11-6*2^j) [2+j] (n+1) t6 =
        st ((u+1)*(2*(2*2^j))+(n+1+4+1-2*(2*2^j))) [2+j] (n+1) t6); f_equal; nia. }
    phase_as (n*2+9-3*2^j) (n+1).
    applys_eq (Done (st (n*2+9-3*2^j) [0%nat;1+j] (n+1) t7)); flia.
Qed.

Lemma LH_set l : LH 1 (z0*>l) (z1*>l).
Proof. unfold LH; es' & l. Qed.
Lemma LH_absorb l : LH 1 (0>>z1*>l) (v*>l).
Proof. unfold LH; es' & l. Qed.
Lemma LH_last l : LH 1 (z1*>0>>z1*>l) (z0*>v*>l).
Proof. unfold LH; es' & l. Qed.

Lemma LH_fill j n l l' : LH n l l' ->
  LH ((n+1)*2^j-1) (z0^^j*>l) (z1^^j*>l').
Proof.
  intro H; induction j.
  - applys_eq H; cbn[Nat.pow]; flia.
  - change (LH ((n+1)*2^(S j)-1) (z0*>z0^^j*>l) (z1*>z1^^j*>l'));
    replace ((n+1)*2^(S j)-1) with (((n+1)*2^j-1)*2+1)
      by (cbn[Nat.pow]; lia).
    eapply segRLs_sideRLs_concat; [|exact IHj].
    eapply segRLs_addmul''; apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.
Qed.

Lemma LH_clear j l l' : LH 1 l l' ->
  LH 1 (z1^^j*>l) (z0^^j*>l').
Proof.
  intro H; induction j; [exact H|].
  change (LH 1 (z1*>z1^^j*>l) (z0*>z0^^j*>l'));
    eapply segRLs_sideRLs_concat; [|exact IHj].
  apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.
Qed.

Lemma LH_partial_D j :
  LH (2^(5+j)-22)
    (z0*>z0*>z0*>v*>z0*>z0*>z0^^j*>z0*>0>>z1*>0inf)
    (z0*>z1*>z0*>v*>z1*>z0*>z1^^j*>z0*>0>>z1*>0inf).
Proof.
  rewrite Nat.pow_add_r; change (2^5) with 32.
  replace (32*2^j-22) with (((2^j-1)*4+1)*8+2) by lia.
  unfold LH; change (sideRLs (flip O.tm) (Hs^^(((2^j-1)*4+1)*8+2))
    ((z0++z0++z0++v)*>z0*>z0*>z0^^j*>z0*>0>>z1*>0inf)
    ((z0++z1++z0++v)*>z1*>z0*>z1^^j*>z0*>0>>z1*>0inf)).
  eapply segRLs_sideRLs_concat.
  - eapply segRLs_addmul''; apply BoundedConfig.segRLs_c_spec with (T:=2000); reflexivity.
  - change (LH ((2^j-1)*4+1) ((z0++z0)*>z0^^j*>z0*>0>>z1*>0inf)
        ((z1++z0)*>z1^^j*>z0*>0>>z1*>0inf)).
    eapply segRLs_sideRLs_concat.
    + eapply segRLs_addmul''; apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
    + applys_eq (LH_fill j 0 (z0*>0>>z1*>0inf) _ (sideRLseq_O _ _)); flia.
Qed.

Lemma LH_partial j r :
  LH (1+2^j*2) (z0*>z0^^j*>z0*>0>>z1*>r)
    (z1*>z0^^j*>z1*>0>>z1*>r).
Proof.
  eapply LH_add with (a:=1%nat) (b:=2^j*2); [apply LH_set|].
  apply LH_one; applys_eq (LH_zeros j _ _ _ (LH_set (0>>z1*>r))); flia.
Qed.

Lemma LC_zero_words j ls l : LC 0 ls l -> LC 0 (shift j ls) (z0^^j*>l).
Proof.
  intro H; induction j.
  - destruct ls; apply H.
  - applys_eq (LC_even_intro 0 _ _ IHj); destruct ls; cbn[up shift]; flia.
Qed.

Lemma LH_partial_finish j : exists l', LC (2^j-1) [0%nat;1+j] l' /\
  LH (2^j*2) (0>>z1*>z0^^j*>z1*>0>>z1*>0inf) l'.
Proof.
  assert (Hnum:LC 0 [0%nat;1+j] (v*>z0^^j*>z0*>v*>0inf)).
  { apply LC_w; rewrite lpow_shift'.
    applys_eq (LC_zero_words (S j) _ _ (LC_w _ _ _ LC_0)); cbn[shift]; flia. }
  destruct (LH_inc (2^j-1) _ _ _ Hnum) as [l' [Hl' Hrun]].
  exists l'; split; [applys_eq Hl'; flia|].
  replace (2^j*2) with (1+(2^j+(2^j-1))) by lia.
  eapply LH_add; [apply LH_absorb|].
  eapply LH_add; [|exact Hrun].
  apply LH_word; applys_eq (LH_zeros j _ _ _ (LH_last 0inf)); flia.
Qed.

Lemma LC_unzeros j n ls l : LC (n*2^j) (shift j ls) l ->
  exists l', LC n ls l' /\ l=z0^^j*>l'.
Proof.
  gen l; induction j; intros l H.
  - exists l; split; [destruct ls; applys_eq H; cbn[shift Nat.pow]; flia|reflexivity].
  - assert (He:LC ((n*2^j)*2) (up (shift j ls)) l).
    { applys_eq H; destruct ls; cbn[shift up Nat.pow]; flia. }
    destruct (LC_even _ _ _ He) as [l0 [Hl0 ->]].
    destruct (IHj _ Hl0) as [l' [Hl' ->]].
    exists l'; auto.
Qed.

Lemma LC_pow j l : LC (2^j) [] l -> l=z0^^j*>z1*>0inf.
Proof.
  intro H; assert (He:LC (1*2^j) (shift j []) l) by (applys_eq H; cbn[shift]; flia).
  destruct (LC_unzeros j _ _ _ He) as [l0 [Hl0 ->]].
  destruct (LC_odd 0 [] _ Hl0) as [l' [Hl' ->]].
  inversion Hl'; subst; try lia; reflexivity.
Qed.

Lemma zero_move j l : 0>>(z0^^j*>l)=z0^^j*>(0>>l).
Proof. induction j; [reflexivity|cbn[lpow app Str_app]; rewrite IHj; reflexivity]. Qed.

Lemma LC_mark k ls l : LC k (O::ls) l -> exists l', LC k ls l' /\ l=v*>l'.
Proof. intro H; inversion H; subst; try lia; eauto. Qed.

Lemma LH_partial_D_start j k l : k+24=2^(6+j) -> LC k [3%nat] l ->
  LH (2^(5+j)-6) (0>>l)
    (z0*>z1*>z0*>v*>z1*>z0*>z1^^j*>z0*>0>>z1*>0inf).
Proof.
  intros Hk Hl.
  assert (He:LC ((2^(3+j)-3)*2^3) (shift 3 [0%nat]) l).
  { applys_eq Hl; rewrite Nat.pow_add_r in Hk |- *; cbn[Nat.pow]; nia. }
  destruct (LC_unzeros 3 _ _ _ He) as [l0 [Hl0 ->]].
  destruct (LC_mark _ _ _ Hl0) as [l1 [Hl1 ->]].
  destruct (LH_inc 3 _ _ _ Hl1) as [l2 [Hl2 Hinc]].
  assert (Hpow:LC (2^(3+j)) [] l2).
  { applys_eq Hl2; rewrite Nat.pow_add_r; cbn[Nat.pow]; lia. }
  apply LC_pow in Hpow; subst l2.
  replace (2^(5+j)-6) with (16+(2^(5+j)-22))
    by (rewrite Nat.pow_add_r; cbn[Nat.pow]; lia).
  rewrite zero_move.
  eapply LH_add; [applys_eq (LH_zeros 3 _ _ _ (LH_cross _ _ Hinc)); reflexivity|].
  rewrite zero_move.
  replace (3+j) with (2+(j+1)) by lia.
  rewrite (lpow_add _ 2 (j+1)), Str_app_assoc.
  rewrite (lpow_add _ j 1), Str_app_assoc.
  apply LH_partial_D.
Qed.

Lemma LH_partial_D_recover j :
  LH (2^(4+j)+12)
    (z0*>v*>z0*>v*>z1*>z0*>z1^^j*>z0*>0>>z1*>0inf)
    (z0*>v*>z0*>v*>z0*>z0*>z0^^j*>z0*>v*>0inf).
Proof.
  rewrite Nat.pow_add_r; change (2^4) with 16.
  replace (16*2^j+12) with (((1+2^j)*4-1)*2*2) by lia.
  apply LH_zero, LH_word, LH_zero, LH_word.
  change (LH ((1+2^j)*4-1) ((z1++z0)*>z1^^j*>z0*>0>>z1*>0inf)
      ((z0++z0)*>z0^^j*>z0*>v*>0inf)).
  replace ((1+2^j)*4-1) with (2^j*4+3) by lia.
  eapply segRLs_sideRLs_concat.
  - eapply segRLs_addmul with (c:=1%nat);
      apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
  - change (LH (2^j+1) (z1^^j*>z0*>0>>z1*>0inf) (z0^^j*>z0*>v*>0inf)).
    replace (2^j+1) with (1+2^j) by lia.
    eapply LH_add; [apply LH_clear, LH_set|].
    applys_eq (LH_zeros j _ _ _ (LH_last 0inf)); flia.
Qed.

Lemma LH_partial_D_finish j : 2<=j -> exists l',
  LC (2^(4+j)-19) [1%nat;1%nat;3+j] l' /\
  LH (2^(5+j)-5)
    (0>>z0*>z1*>z0*>v*>z1*>z0*>z1^^j*>z0*>0>>z1*>0inf) l'.
Proof.
  intro Hj.
  assert (Hpow:32<=2^(4+j)).
  { assert (4<=2^j) by (change (2^2<=2^j); apply Nat.pow_le_mono_r; lia).
    rewrite Nat.pow_add_r; change (2^4) with 16; lia. }
  assert (Hnum:LC 0 [1%nat;1%nat;3+j]
    (z0*>v*>z0*>v*>z0*>z0*>z0^^j*>z0*>v*>0inf)).
  { apply (LC_0' 0), LC_w, (LC_0' 0), LC_w, (LC_0' 0), (LC_0' 0).
    rewrite lpow_shift'; applys_eq (LC_zero_words (1+j) _ _ (LC_w _ _ _ LC_0));
      cbn[shift]; flia. }
  destruct (LH_inc (2^(4+j)-19) _ _ _ Hnum) as [l' [Hl' Hrun]].
  exists l'; split; [exact Hl'|].
  replace (2^(5+j)-5) with (2+(2^(4+j)+12+(2^(4+j)-19))).
  2: { rewrite (Nat.pow_add_r 2 4 j) in Hpow |- *.
    rewrite (Nat.pow_add_r 2 5 j); cbn[Nat.pow] in Hpow |- *; lia. }
  eapply LH_add; [apply (LH_zero 1), LH_absorb|].
  eapply LH_add; [apply LH_partial_D_recover|exact Hrun].
Qed.

Lemma G_partial j n : n+5=2^(1+j) -> forall l r, Denote (RootG n) l r ->
  exists l' r', Denote (st (2^j-1) [0%nat;1+j] (n+1) t7) l' r' /\
    l {{E}}> r -[O.tm]->+ l' {{E}}> r'.
Proof.
  intros Hn l r [Hl Hr].
  destruct (BigStep0 Hl Hr) as [l0 [r0 [Hl0 [Hr0 Hdrop]]]].
  replace (S n) with (n+1) in Hr0 by lia.
  assert (He:LC (2^(2+j)) [] l0).
  { applys_eq Hl0; change (2*(2*2^j)=3+(n*2+7)); change (n+5=2*2^j) in Hn; lia. }
  apply LC_pow in He; subst l0.
  pose (z1*>z0^^j*>z1*>0>>z1*>0inf) as midleft.
  assert (Hfirst:LH (n+1+4+offset t5) (0>>z0^^(2+j)*>z1*>0inf) midleft).
  { rewrite zero_move; replace (2+j) with ((1+j)+1) by lia.
    rewrite (lpow_add _ (1+j) 1), Str_app_assoc.
    unfold midleft; applys_eq (LH_partial j 0inf).
    change (n+1+4+1=1+2^j*2); change (n+5=2*2^j) in Hn; lia. }
  destruct (Phase _ _ _ _ _ Hr0 Hfirst) as [r1 [Hr1 Hphase1]].
  destruct (LH_partial_finish j) as [l' [Hl' Hfinish]].
  assert (Hlast:LH (n+1+4+offset t6) (0>>midleft) l').
  { applys_eq Hfinish; change (n+1+4+0=2^j*2); change (n+5=2*2^j) in Hn; lia. }
  destruct (Phase _ _ _ _ _ Hr1 Hlast) as [r' [Hr' Hphase2]].
  exists l', r'; split; [split; assumption|].
  eapply progress_trans; [exact Hdrop|]; eapply progress_trans; eassumption.
Qed.

Lemma D6_partial j n : 2<=j -> n+14=2^(5+j) ->
  forall l r, Denote (RootD 6 n) l r ->
  exists l' r', Denote (RootD (2+j) (n+8)) l' r' /\
    l {{E}}> r -[O.tm]->+ l' {{E}}> r'.
Proof.
  intros Hj Hn l r Hd.
  assert (Hpow:4<=2^j) by (change (2^2<=2^j); apply Nat.pow_le_mono_r; lia).
  assert (Hval:n+14=32*2^j) by (rewrite Hn, Nat.pow_add_r; reflexivity).
  assert (Hmod:n mod 8=2) by lia.
  assert (Hfirst:Steps (RootD 6 n) (st (n*2+4) [3%nat] (n+4) t0)).
  { unfold RootD; cbn[Nat.pow Nat.sub].
    phase_as (n*2-40) (n+1).
    phase_as (n*2-19) (n+1).
    phase_as (n*2-5) (n+1).
    do 3 (eapply Advance; [apply Drop|]).
    applys_eq (Done (st (n*2+4) [3%nat] (n+4) t0)); flia. }
  destruct (Steps_spec _ _ Hfirst _ _ Hd) as [l0 [r0 [[Hl0 Hr0] Hrun0]]].
  assert (Hstart:(n*2+4)+24=2^(6+j)).
  { rewrite Nat.pow_add_r; change (2^6) with 64; lia. }
  pose proof (LH_partial_D_start j _ _ Hstart Hl0) as Hleft.
  replace (2^(5+j)-6) with (n+4+4+offset t0) in Hleft by (cbn[offset]; lia).
  destruct (Phase _ _ _ _ _ Hr0 Hleft) as [r1 [Hr1 Hrun1]].
  destruct (LH_partial_D_finish j Hj) as [l1 [Hl1 Hleft1]].
  replace (2^(5+j)-5) with (n+4+4+offset t1) in Hleft1 by (cbn[offset]; lia).
  destruct (Phase _ _ _ _ _ Hr1 Hleft1) as [r2 [Hr2 Hrun2]].
  assert (Htail:Steps (st (2^(4+j)-19) [1%nat;1%nat;3+j] (n+4) t2)
    (RootD (2+j) (n+8))).
  { replace (2^(4+j)-19) with (n*2+9-24*2^(1+j)).
    2: { rewrite (Nat.pow_add_r 2 4 j), (Nat.pow_add_r 2 1 j); cbn[Nat.pow]; lia. }
    rewrite (Nat.pow_add_r 2 1 j); change (2^1) with 2.
    phase_as (n*2+11-24*2^j) (n+4).
    phase_as (n*2+17-12*2^j) (n+6).
    phase_as ((n+8)*2+7-6*2^j) (n+8).
    applys_eq (Done (RootD (2+j) (n+8))); unfold RootD;
      replace (2+j-1) with (1+j) by lia;
      rewrite (Nat.pow_add_r 2 1 j); cbn[Nat.pow]; flia. }
  destruct (Steps_spec _ _ Htail _ _ (conj Hl1 Hr2)) as [l' [r' [Hd' Hrun3]]].
  exists l', r'; split; [exact Hd'|].
  eapply evstep_progress_trans; [exact Hrun0|].
  eapply progress_trans; [exact Hrun1|].
  eapply progress_evstep_trans; eassumption.
Qed.

Lemma G_large_tail a n : 2^15*2^a<=n+5 -> n mod 8=3 ->
  Steps (st (n*2+9-3*2^14*2^a) [0%nat;15+a] (n+1) t7)
    (RootD (1+a) (n+15)).
Proof.
  intros Hlow Hmod; unfold RootD; replace (1+a-1) with a by lia.
  phase_as (n*2+10-3*2^13*2^a) (n+2).
  phase_as (n*2+7-3*2^12*2^a) (n+2).
  phase_as (n*2+9-3*2^11*2^a) (n+2).
  phase_as (n*2+6-3*2^10*2^a) (n+5).
  phase_as (n*2+6-1536*2^a) (n+5).
  phase_as (n*2+3-768*2^a) (n+5).
  phase_as (n*2+10-384*2^a) (n+5).
  phase_as (n*2+15-192*2^a) (n+6).
  phase_as (n*2+27-96*2^a) (n+10).
  phase_as (n*2+24-48*2^a) (n+11).
  phase_as (n*2+25-24*2^a) (n+11).
  phase_as (n*2+26-12*2^a) (n+11).
  phase_as (n*2+34-6*2^a) (n+14).
  phase_as ((n+15)*2+7-3*2^a) (n+15).
  applys_eq (Done (st ((n+15)*2+7-3*2^a) [0%nat;1+a] (n+15) t5)); flia.
Qed.

Ltac phase_linear param base :=
  phase; lazymatch goal with |-Steps (st ?k ?ls ?n ?t) _ =>
    let fk:=eval pattern param in k in
    let fn:=eval pattern param in n in
    lazymatch fk with ?f param => lazymatch fn with ?g param =>
      let k0:=eval vm_compute in (Z.of_nat (f base)) in
      let delta:=eval vm_compute in (g base-base) in
      let sign:=eval vm_compute in (Z.leb (Z.of_nat (base*2)) k0) in
      let knew:=lazymatch sign with
      | true => let c:=eval vm_compute in (Z.sub k0 (Z.of_nat (base*2))) in constr:(param*2+Z.to_nat c)
      | false => let c:=eval vm_compute in (Z.sub (Z.of_nat (base*2)) k0) in constr:(param*2-Z.to_nat c)
      end in
      replace (st k ls n t) with (st knew ls (param+delta) t) by flia
    end end
  end.

Ltac small_tail :=
  lazymatch goal with
  | |- Steps (st _ [O;?h] _ _) (RootG (?n+?delta)) =>
    let base := constr:(3*2^h-5) in
    let count := eval vm_compute in (delta-2) in
    let rec loop k := lazymatch k with
      | O => idtac | S ?k' => phase_linear n base; loop k' end in
    loop count;
    applys_eq (Done (RootG (n+delta))); unfold RootG; flia
  end.

Local Opaque Nat.pow Z.to_nat.
Lemma G_small_tail j n : 2<=j<=13 -> 11<=n ->
  n mod 2^(j+2)=2^(j+1)-5 ->
  Steps (st (n*2+9-3*2^j) [0%nat;1+j] (n+1) t7)
    (RootG (n+8*((j+13)/8))).
Proof.
  intros Hj Hn Hmod.
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]]; try lia;
    small_tail.
Qed.

Local Transparent Nat.pow Z.to_nat.

Definition Forward s s' := forall l r, Denote s l r -> exists l' r',
  Denote s' l' r' /\ l {{E}}> r -[O.tm]->+ l' {{E}}> r'.

Lemma Steps_forward s s' : s<>s' -> Steps s s' -> Forward s s'.
Proof.
  intros Hneq Hsteps l r Hd; destruct Hsteps; [contradiction|].
  destruct (Next_spec _ _ H _ _ Hd) as [l0 [r0 [Hd0 Hrun0]]].
  destruct (Steps_spec _ _ Hsteps _ _ Hd0) as [l' [r' [Hd' Hrun']]].
  exists l', r'; split; [exact Hd'|]; eapply progress_evstep_trans; eassumption.
Qed.

Lemma Forward_steps s t u : Forward s t -> Steps t u -> Forward s u.
Proof.
  intros H0 H1 l r Hd.
  destruct (H0 _ _ Hd) as [l0 [r0 [Hd0 Hrun0]]].
  destruct (Steps_spec _ _ H1 _ _ Hd0) as [l' [r' [Hd' Hrun']]].
  exists l', r'; split; [exact Hd'|]; eapply progress_evstep_trans; eassumption.
Qed.

Lemma factor2 n : 0<n -> exists i u, n=(u*2+1)*2^i.
Proof.
  induction n using lt_wf_ind; intro Hn.
  destruct (Nat.eq_dec (n mod 2) 1) as [Hodd|Heven].
  - exists 0%nat, (n/2); cbn[Nat.pow]; lia.
  - destruct (H (n/2)) as [i [u Hu]]; try lia.
    exists (S i), u; cbn[Nat.pow]; nia.
Qed.

Lemma G_begin j u n : 2<=j -> n+5=(u*2+1)*2^(1+j) ->
  Forward (RootG n) (st (n*2+9-3*2^j) [0%nat;1+j] (n+1) t7).
Proof.
  intros Hj Hval; destruct u.
  - replace ((0*2+1)*2^(1+j)) with (2^(1+j)) in Hval by lia.
    intros l r Hd; destruct (G_partial _ _ Hval _ _ Hd) as [l' [r' [Hd' Hrun]]].
    exists l', r'; split; [|exact Hrun].
    applys_eq Hd'; change (n+5=2*2^j) in Hval; flia.
  - eapply Steps_forward.
    + unfold RootG; intro He; inversion He; lia.
    + apply G_start with (u:=u); [exact Hj|]; nia.
Qed.

Inductive Ready : State -> Prop :=
| ReadyG n : 11<=n -> n mod 8=3 -> Ready (RootG n)
| ReadyD h n : 1<=h -> 64<=n -> n mod 8=2 -> 3*2^(h-1)<=n*2 -> Ready (RootD h n)
| ReadyE n : 64<=n -> n mod 8=2 -> Ready (RootE n)
| ReadyF n : 64<=n -> n mod 8=1%nat -> Ready (RootF n).

Lemma G_ready n : 11<=n -> n mod 8=3 ->
  exists s, Ready s /\ Forward (RootG n) s.
Proof.
  intros Hn Hmod.
  destruct (factor2 ((n+5)/8)) as [i [u Hu]]; [lia|].
  assert (Hval:n+5=(u*2+1)*2^(3+i)).
  { rewrite Nat.pow_add_r; cbn[Nat.pow]; nia. }
  assert (Hlow:2^(3+i)<=n+5) by (rewrite Hval; nia).
  pose proof (G_begin (2+i) u n ltac:(lia) Hval) as Hbegin.
  destruct (le_dec i 11) as [Hi|Hi].
  - exists (RootG (n+8*((2+i+13)/8))); split.
    + apply ReadyG; lia.
    + eapply Forward_steps; [exact Hbegin|].
      apply G_small_tail; try lia.
      assert (Hp:4<=2^(2+i)).
      { rewrite Nat.pow_add_r; cbn[Nat.pow]; lia. }
      replace (3+i) with ((2+i)+1) in Hval by lia.
      rewrite (Nat.pow_add_r 2 (2+i) 2), (Nat.pow_add_r 2 (2+i) 1) in *.
      cbn[Nat.pow] in *; symmetry; apply Nat.mod_unique with (q:=u); nia.
  - set (a:=i-12).
    assert (Hi':i=12+a) by (unfold a; lia).
    assert (Hbound:2^15*2^a<=n+5).
    { applys_eq Hlow; rewrite Hi'. replace (3+(12+a)) with (15+a) by lia.
      rewrite Nat.pow_add_r; reflexivity. }
    exists (RootD (1+a) (n+15)); split.
    + apply ReadyD; try lia.
      replace (1+a-1) with a by lia; cbn[Nat.pow] in Hbound; lia.
    + eapply Forward_steps; [exact Hbegin|].
      applys_eq (G_large_tail a n Hbound Hmod); rewrite Hi'.
      * replace (2+(12+a)) with (14+a) by lia.
        rewrite (Nat.pow_add_r 2 14 a); flia.
Qed.

Lemma D6_ready n : 64<=n -> n mod 8=2 ->
  exists s, Ready s /\ Forward (RootD 6 n) s.
Proof.
  intros Hn Hmod; destruct (Nat.eq_dec (n mod 16) 10) as [He|He].
  - exists (RootE (n+8)); split; [apply ReadyE; lia|].
    eapply Steps_forward; [unfold RootD, RootE; intro H; inversion H; lia|].
    apply D6_even; assumption.
  - assert (Hrem:n mod 16=2) by lia.
    destruct (factor2 ((n+14)/16)) as [i [u Hu]]; [lia|].
    assert (Hval:n+14=(u*2+1)*16*2^i) by nia.
    assert (Hlow:16*2^i<=n+14) by (rewrite Hval; nia).
    exists (RootD (1+i) (n+8)); split.
    + apply ReadyD; try lia; replace (1+i-1) with i by lia; lia.
    + destruct u.
      * destruct i as [|[|[|i]]]; cbn[Nat.pow] in Hval; try lia.
        assert (Hcase:n+14=2^(5+(2+i))).
        { replace (5+(2+i)) with (7+i) by lia.
          rewrite Nat.pow_add_r; cbn[Nat.pow]; nia. }
        exact (D6_partial (2+i) n ltac:(lia) Hcase).
      * eapply Steps_forward; [unfold RootD; intro H; inversion H; lia|].
        apply D6_odd_ge3 with (a:=i) (u:=u); [exact Hn|]; nia.
Qed.

Lemma D_ready h n : 1<=h -> 64<=n -> n mod 8=2 -> 3*2^(h-1)<=n*2 ->
  exists s, Ready s /\ Forward (RootD h n) s.
Proof.
  intros Hh Hn Hmod Hbound.
  destruct (le_dec 9 h) as [Hlarge|Hsmall].
  - set (j:=h-9); assert (Hj:h=9+j) by (unfold j; lia).
    assert (Hlow:384*2^j<=n).
    { rewrite Hj in Hbound; replace (9+j-1) with (8+j) in Hbound by lia.
      rewrite Nat.pow_add_r in Hbound; cbn[Nat.pow] in Hbound; lia. }
    exists (RootD (1+j) (n+8)); split.
    + apply ReadyD; try lia; replace (1+j-1) with j by lia; lia.
    + rewrite Hj; eapply Steps_forward; [unfold RootD; intro H; inversion H; lia|].
      apply D_shrink; assumption.
  - destruct (le_dec h 5) as [Hfive|Hfive].
    + exists (RootG (n+9)); split; [apply ReadyG; lia|].
      eapply Steps_forward; [unfold RootD, RootG; intro H; inversion H; lia|].
      apply D_small; lia.
    + assert (Hcases:h=6 \/ h=7 \/ h=8) by lia.
      destruct Hcases as [Hcase|[Hcase|Hcase]]; subst h.
      * apply D6_ready; assumption.
      * exists (RootF (n+7)); split; [apply ReadyF; lia|].
        eapply Steps_forward; [unfold RootD, RootF; intro H; inversion H; lia|].
        apply D7; [cbn[Nat.pow Nat.sub] in Hbound; lia|exact Hmod].
      * exists (RootE (n+8)); split; [apply ReadyE; lia|].
        eapply Steps_forward; [unfold RootD, RootE; intro H; inversion H; lia|].
        apply D8; [cbn[Nat.pow Nat.sub] in Hbound; lia|exact Hmod].
Qed.

Lemma Ready_step s : Ready s -> exists s', Ready s' /\ Forward s s'.
Proof.
  intro H; destruct H.
  - apply G_ready; assumption.
  - apply D_ready; assumption.
  - exists (RootG (n+9)); split; [apply ReadyG; lia|].
    eapply Steps_forward; [unfold RootE, RootG; intro He; inversion He; lia|].
    apply E_cycle; assumption.
  - exists (RootG (n+10)); split; [apply ReadyG; lia|].
    eapply Steps_forward; [unfold RootF, RootG; intro He; inversion He; lia|].
    apply F_cycle; assumption.
Qed.

Definition Inv c := exists s l r, Ready s /\ Denote s l r /\ c=l {{E}}> r.

Lemma Inv_step c : Inv c -> exists c', Inv c' /\ c -[O.tm]->+ c'.
Proof.
  intros [s [l [r [Hs [Hd ->]]]]].
  destruct (Ready_step _ Hs) as [s' [Hs' Hstep]].
  destruct (Hstep _ _ Hd) as [l' [r' [Hd' Hrun]]].
  exists (l' {{E}}> r'); split; [exists s', l', r'; auto|exact Hrun].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  destruct init as [l [r [Hd Hrun]]].
  eapply multistep_nonhalt; [exact Hrun|].
  apply (perm_nonhalt' O.tm tm rename E _ correspondence).
  eapply progress_nonhalt; [apply Inv_step|].
  exists (RootG 11), l, r; split; [apply ReadyG; reflexivity || lia|auto].
Qed.

End TM4.

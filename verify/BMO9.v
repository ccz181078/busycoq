From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith NArith.
Require Import String.
Require Import List.

Module Prefix.
Local Open Scope nat_scope.

Definition mass := fold_right Nat.add 0.

(* The index counts E steps, so every step increases mass by three times
   its index.  Explicit zeros remain part of the finite prefix. *)
Inductive Step : nat -> list nat -> list nat -> Prop :=
| E n v w r : Step 1 (2*n::v::w::r) ((2*n+v+w+3)::r)
| O n v w r : 1<=n+v ->
    Step 0 ((2*n+1)::v::w::r) ((n+v-1)::0::1::(w+n+1)::r).

Inductive Run : nat -> list nat -> list nat -> Prop :=
| refl xs : Run 0 xs xs
| cons e f xs ys zs : Step e xs ys -> Run f ys zs -> Run (e+f) xs zs.

Lemma one e xs ys : Step e xs ys -> Run e xs ys.
Proof. intro H. replace e with (e+0) by lia. eapply cons; [exact H|constructor]. Qed.

Lemma trans e f xs ys zs : Run e xs ys -> Run f ys zs -> Run (e+f) xs zs.
Proof.
  intros H. induction H as [xs|e g xs ys ws Hs Hr IH]; intros H'; [exact H'|].
  replace (e+g+f) with (e+(g+f)) by lia.
  eapply cons; [exact Hs|apply IH; exact H'].
Qed.

Lemma step_app e xs ys r : Step e xs ys -> Step e (xs++r) (ys++r).
Proof. intros H; destruct H; cbn; constructor; assumption. Qed.

Lemma app e xs ys r : Run e xs ys -> Run e (xs++r) (ys++r).
Proof. intro H. induction H; [constructor|]. eapply cons; eauto using step_app. Qed.

Lemma step_mass e xs ys : Step e xs ys -> mass ys=mass xs+3*e.
Proof. intros H; destruct H; cbn [mass fold_right]; lia. Qed.

Lemma run_mass e xs ys : Run e xs ys -> mass ys=mass xs+3*e.
Proof. intro H. induction H; [lia|]. pose proof (step_mass _ _ _ H). lia. Qed.

Lemma step_length e xs ys : Step e xs ys -> length xs<=length ys+2*e.
Proof. intro H; destruct H; cbn; lia. Qed.

Lemma run_length e xs ys : Run e xs ys -> length xs<=length ys+2*e.
Proof. intro H. induction H; [lia|]. pose proof (step_length _ _ _ H). lia. Qed.

Lemma step_last e xs ys : Step e xs ys ->
  forall p z, xs=p++[z] ->
  exists q d, ys=q++[z+d] /\ forall z', Step e (p++[z']) (q++[z'+d]).
Proof.
  intro H. destruct H as [n v w r|n v w r Hsafe]; intros p z Hx;
    destruct r as [|h r].
  - change ([2*n;v]++[w]=p++[z]) in Hx.
    apply app_inj_tail in Hx. destruct Hx as [<- <-].
    exists ([]:list nat),(2*n+v+3). split; [cbn [List.app]; flia|].
    intro z'. cbn [List.app]. applys_eq (E n v z' []); flia.
  - destruct (@exists_last nat (h::r) ltac:(discriminate)) as [p0 [z0 Hr]].
    rewrite Hr in *. change ((2*n::v::w::p0)++[z0]=p++[z]) in Hx.
    apply app_inj_tail in Hx. destruct Hx as [<- <-].
    exists ((2*n+v+w+3)::p0),0. rewrite !Nat.add_0_r. split; [reflexivity|].
    intro z'. try rewrite Nat.add_0_r. apply E.
  - change ([2*n+1;v]++[w]=p++[z]) in Hx.
    apply app_inj_tail in Hx. destruct Hx as [<- <-].
    exists [n+v-1;0;1],(n+1). split; [cbn [List.app]; flia|].
    intro z'. cbn [List.app]. applys_eq (O n v z' [] Hsafe); flia.
  - destruct (@exists_last nat (h::r) ltac:(discriminate)) as [p0 [z0 Hr]].
    rewrite Hr in *. change (((2*n+1)::v::w::p0)++[z0]=p++[z]) in Hx.
    apply app_inj_tail in Hx. destruct Hx as [<- <-].
    exists ((n+v-1)::0::1::(w+n+1)::p0),0. rewrite !Nat.add_0_r.
    split; [reflexivity|]. intro z'. try rewrite Nat.add_0_r. apply O,Hsafe.
Qed.

Lemma run_last e xs ys : Run e xs ys ->
  forall p z, xs=p++[z] ->
  exists q d, ys=q++[z+d] /\ forall z', Run e (p++[z']) (q++[z'+d]).
Proof.
  intro H. induction H as [xs|e f xs ys zs Hs Hr IH]; intros p z Hx.
  - exists p,0. rewrite Nat.add_0_r. split; [exact Hx|].
    intro z'. rewrite Nat.add_0_r. constructor.
  - destruct (step_last e xs ys Hs p z Hx) as [p1 [d1 [Hy Hstep]]].
    destruct (IH p1 (z+d1) Hy) as [p2 [d2 [Hz Hrun]]].
    exists p2,(d1+d2). split; [rewrite Nat.add_assoc; exact Hz|].
    intro z'. rewrite Nat.add_assoc. eapply cons; [apply Hstep|apply Hrun].
Qed.

Fixpoint geometric k q :=
  match k with 0 => [] | S k => q::geometric k (2*q) end.
Definition F k q := (q+1)::geometric k q.
Definition G k q :=
  match k with 0 => [q] | S k => F k q++[2^k*q-1] end.

Lemma geometric_snoc k q : geometric (1+k) q=geometric k q++[2^k*q].
Proof.
  revert q. induction k; intros q.
  - cbn. f_equal; lia.
  - change (q::geometric (1+k) (2*q)=q::(geometric k (2*q)++[2^(S k)*q])).
    rewrite IHk. do 3 f_equal. cbn [Nat.pow]; nia.
Qed.

Lemma geometric_length k q : length (geometric k q)=k.
Proof. revert q. induction k; intros; cbn; auto. Qed.

Lemma geometric_mass k q : mass (geometric k q)+q=2^k*q.
Proof. revert q. induction k; intros; cbn [geometric mass fold_right Nat.pow].
  - lia.
  - specialize (IHk (2*q)). nia.
Qed.

Lemma F_snoc k q : F (1+k) q=F k q++[2^k*q].
Proof. unfold F. rewrite geometric_snoc. reflexivity. Qed.

Lemma F_to_G e k q ys a : 0<q ->
  Run e (F (1+k) q) (ys++[1+a]) -> Run e (G (1+k) q) (ys++[a]).
Proof.
  intros Hq H. destruct (run_last _ _ _ H _ _ (F_snoc k q))
    as [p [d [He Hr]]].
  apply app_inj_tail in He. destruct He as [<- Ha].
  assert (Hp : 0<2^k) by (pose proof (Nat.pow_nonzero 2 k); lia).
  applys_eq (Hr (2^k*q-1)); cbn [G Nat.add]; flia.
Qed.

Lemma odd_descent k t w r :
  Run 1 ((2^k*(3+2*t)-3)::0::1::w::r)
    ((4+2*t)::geometric k (3+2*t)++w::r).
Proof.
  revert w r. induction k; intros w r.
  - cbn [Nat.pow geometric].
    applys_eq (one _ _ _ (E t 0 1 (w::r))); flia.
  - assert (Hp : 3<=2^k*(3+2*t)).
    { assert (0<2^k) by (pose proof (Nat.pow_nonzero 2 k); lia). nia. }
    replace (S k) with (1+k) by lia. rewrite geometric_snoc.
    rewrite <- app_assoc.
    rewrite Nat.pow_add_r. change (2^1) with 2%nat.
    eapply cons with (e:=0) (f:=1).
    + applys_eq (O (2^k*(3+2*t)-2) 0 1 (w::r) ltac:(lia)); repeat first [solve [nia]|f_equal].
    + applys_eq (IHk (2^k*(3+2*t)) (w::r)); flia.
Qed.

Lemma odd_expand k t n v w r : n+v+2=2^k*(3+2*t) ->
  Run 1 ((2*n+1)::v::w::r)
    ((4+2*t)::geometric k (3+2*t)++(w+n+1)::r).
Proof.
  intro H. assert (Hp : 3<=2^k*(3+2*t)).
  { assert (0<2^k) by (pose proof (Nat.pow_nonzero 2 k); lia). nia. }
  eapply cons with (e:=0) (f:=1).
  - apply O; lia.
  - applys_eq (odd_descent k t (w+n+1) r); flia.
Qed.

Lemma odd_lookup k t n v w r e ys a :
  n+v+2=2^k*(3+2*t) -> Run e (F (1+k) (3+2*t)) (ys++[a]) ->
  Run (1+e) ((2*n+1)::v::w::r) ((ys++[a+w-v-1])++r).
Proof.
  intros Hn Hr.
  assert (HF : F (1+k) (3+2*t)=F k (3+2*t)++[2^k*(3+2*t)]).
  { unfold F. rewrite geometric_snoc. reflexivity. }
  destruct (run_last _ _ _ Hr _ _ HF) as [p [d [Hlast Hrun]]].
  apply app_inj_tail in Hlast. destruct Hlast as [<- Ha].
  eapply trans with (ys:=(F k (3+2*t)++[w+n+1])++r).
  - applys_eq (odd_expand k t n v w r Hn); unfold F; rewrite <- app_assoc;
      cbn [List.app]; flia.
  - apply app. applys_eq (Hrun (w+n+1)); flia.
Qed.

(* Unlike Run, Exec may expose another zero from the infinite right tail. *)
Inductive Exec : nat -> list nat -> list nat -> Prop :=
| stop xs : Exec 0 xs xs
| take e f xs ys zs : Step e xs ys -> Exec f ys zs -> Exec (e+f) xs zs
| zero e xs ys : Exec e (xs++[0]) ys -> Exec e xs ys.

Lemma run_exec e xs ys : Run e xs ys -> Exec e xs ys.
Proof. intro H. induction H; [constructor|eapply take; eassumption]. Qed.

Lemma exec_trans e f xs ys zs : Exec e xs ys -> Exec f ys zs -> Exec (e+f) xs zs.
Proof.
  intro H. induction H as [xs|e g xs ys ws Hs Hr IH|e xs ys H IH]; intro H'.
  - exact H'.
  - replace (e+g+f) with (e+(g+f)) by lia. eapply take; [exact Hs|apply IH,H'].
  - apply zero,IH,H'.
Qed.

Lemma mass_zero xs : mass (xs++[0])=mass xs.
Proof. unfold mass. rewrite fold_right_app. reflexivity. Qed.

Lemma exec_mass e xs ys : Exec e xs ys -> mass ys=mass xs+3*e.
Proof.
  intro H. induction H.
  - lia.
  - pose proof (step_mass _ _ _ H). lia.
  - rewrite mass_zero in IHExec. exact IHExec.
Qed.

Lemma split2 n : 0<n -> exists k t, n=2^k*(1+2*t).
Proof.
  induction n using lt_wf_ind. intro Hn.
  destruct (Nat.Even_or_Odd n) as [[a Ha]|[a Ha]].
  - destruct (H a ltac:(lia) ltac:(lia)) as [k [t Hk]].
    exists (1+k),t. rewrite Nat.pow_add_r. change (2^1) with 2%nat. nia.
  - exists 0,a. cbn. lia.
Qed.

Lemma pow2_mod3 n : 2^n mod 3=1 \/ 2^n mod 3=2.
Proof.
  induction n; [now left|]. rewrite Nat.pow_succ_r, Nat.mul_mod by lia.
  destruct IHn as [-> | ->]; cbn; auto.
Qed.

Lemma single_returns :
  (forall k t, exists e m, Exec e (G (1+k) (1+2*t)) [m]) ->
  forall j, exists e m, Exec (1+e) [3*j] [m].
Proof.
  intros HG j. destruct (Nat.Even_or_Odd (3*j)) as [[n Hn]|[n Hn]].
  - exists 0,(2*n+3). rewrite Hn. apply zero,zero,run_exec.
    cbn [List.app]. applys_eq (one _ _ _ (E n 0 0 [])); flia.
  - destruct (split2 (n+2) ltac:(lia)) as [k [t Hk]].
    assert (Ht : 1<=t).
    { destruct t; [|lia].
      assert (Hp : 2^(1+k)=(j+1)*3).
      { rewrite Nat.pow_add_r. change (2^1) with 2%nat. nia. }
      pose proof (pow2_mod3 (1+k)) as Hmod.
      rewrite Hp, Nat.mod_mul in Hmod by lia. lia. }
    destruct (HG k t) as [e [m Hr]]. exists e,m.
    apply zero,zero. cbn [List.app]. rewrite Hn.
    eapply exec_trans with (e:=1) (f:=e); [apply run_exec|exact Hr].
    pose proof (odd_expand k (t-1) n 0 0 [] ltac:(nia)) as Ho.
    replace (3+2*(t-1)) with (1+2*t) in Ho by lia.
    applys_eq Ho; cbn [G F Nat.add List.app]; flia.
Qed.

End Prefix.


Module Block.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Record kernel := Kernel { den:Z; num:Z; bias:Z; gain:Z }.
Definition good k := 0<den k /\ 0<num k /\ 2*num k<=den k /\
  1<=bias k /\ bias k+2<=gain k.
Definition call k S H S' H' := S'=S+gain k /\
  den k*H'=2*den k*S-num k*H+den k*(2*gain k+3-bias k).

Record summary := Summary { scale:Z; sc:Z; hc:Z; offset:Z; added:Z }.
Definition identity := Summary 1 0 1 0 0.
Definition push k z := Summary
  (den k*scale z) (2*den k*scale z-num k*sc z) (-num k*hc z)
  (den k*scale z*(2*added z+2*gain k+3-bias k)-num k*offset z)
  (added z+gain k).
Definition denotes z S H S' H' := S'=S+added z /\
  scale z*H'=sc z*S+hc z*H+offset z.
Definition bounded z := 0<scale z /\ 0<=sc z<=2*scale z /\
  0<=added z /\ 0<=offset z<=scale z*(2*added z+2).

Lemma identity_bounded : bounded identity.
Proof. unfold bounded,identity; cbn; lia. Qed.

Lemma push_bounded k z : good k -> bounded z ->
  bounded (push k z) /\ scale (push k z)<=sc (push k z) /\ 0<offset (push k z).
Proof.
  destruct k as [q p b lam],z as [Q A B C M].
  cbv beta iota zeta delta [good bounded push den num bias gain scale sc hc offset added].
  intros [Hq [Hp [Hqp [Hb Hl]]]] [HQ [HA [HM HC]]].
  assert (HpA : 0<=p*A<=q*Q).
  { pose proof (Z.mul_le_mono_nonneg_l A (2*Q) p ltac:(lia) ltac:(lia)). nia. }
  assert (HpC : 0<=p*C<=q*Q*(M+1)).
  { pose proof (Z.mul_le_mono_nonneg_l C (Q*(2*M+2)) p ltac:(lia) ltac:(lia)).
    assert (p*Q*(2*M+2)<=q*Q*(M+1)) by
      (pose proof (Z.mul_le_mono_nonneg_r (2*p) q (Q*(M+1)) ltac:(nia) Hqp); nia).
    nia. }
  assert (Hprod : 0<q*Q) by nia.
  repeat split; nia.
Qed.

Lemma push_sound k z S H S1 H1 S2 H2 :
  denotes z S H S1 H1 -> call k S1 H1 S2 H2 -> denotes (push k z) S H S2 H2.
Proof.
  destruct k as [q p b lam],z as [Q A B C M].
  cbv beta iota zeta delta [denotes call push den num bias gain scale sc hc offset added].
  intros [HS1 HH1] [HS2 HH2]. split; [lia|].
  rewrite HS1 in HH2.
  pose proof (f_equal (fun x => Q*x) HH2).
  pose proof (f_equal (fun x => p*x) HH1).
  ring_simplify in H0. ring_simplify in H3. ring_simplify. lia.
Qed.

Inductive calls : list kernel -> Z -> Z -> Z -> Z -> Prop :=
| no_calls S H : calls [] S H S H
| more_calls k ks S H S1 H1 S2 H2 : call k S H S1 H1 ->
  calls ks S1 H1 S2 H2 -> calls (k::ks) S H S2 H2.

Lemma fold_sound ks S H S' H' : calls ks S H S' H' ->
  forall z S0 H0, denotes z S0 H0 S H ->
    denotes (fold_left (fun z k => push k z) ks z) S0 H0 S' H'.
Proof.
  intro Hrun. induction Hrun; intros z Sbase Hbase Hz; cbn; [exact Hz|].
  apply IHHrun. eapply push_sound; eassumption.
Qed.

Lemma fold_bounded ks z : Forall good ks -> bounded z ->
  bounded (fold_left (fun z k => push k z) ks z).
Proof.
  intro H. revert z. induction H; intros z Hz; cbn; [exact Hz|].
  apply IHForall. apply (push_bounded x z H Hz).
Qed.

(* The same summary record in (S,u) coordinates, used for the low part
   following a high call. *)
Definition low_call k S u S' u' := S'=S+gain k /\
  den k*u'=num k*(2*S-u+3)+den k*bias k.
Definition low_push k z := Summary
  (den k*scale z) (num k*(2*scale z-sc z)) (-num k*hc z)
  (num k*scale z*(2*added z+3)-num k*offset z+den k*scale z*bias k)
  (added z+gain k).
Definition low_bounded z := 0<scale z /\ 0<=sc z<=scale z /\
  -scale z<=hc z<=scale z /\ 0<=added z /\ 0<=offset z<=scale z*added z.

Lemma call_coordinates k S u S' u' :
  call k S (2*S-u+3) S' (2*S'-u'+3) <-> low_call k S u S' u'.
Proof.
  unfold call,low_call. split; intros [-> H]; split; [reflexivity|nia|reflexivity|nia].
Qed.

Lemma low_identity_bounded : low_bounded identity.
Proof. unfold low_bounded,identity; cbn; lia. Qed.

Lemma low_push_bounded k z : good k -> low_bounded z ->
  low_bounded (low_push k z) /\
  -scale (low_push k z)<=2*hc (low_push k z)<=scale (low_push k z).
Proof.
  destruct k as [q p b lam],z as [Q E T V K].
  cbv beta iota zeta delta [good low_bounded low_push den num bias gain scale sc hc offset added].
  intros [Hq [Hp [Hqp [Hb Hl]]]] [HQ [HE [HT [HK HV]]]].
  assert (HpE : 0<=p*E<=p*Q).
  { pose proof (Z.mul_le_mono_nonneg_l E Q p ltac:(lia) ltac:(lia)). nia. }
  assert (HpT : -p*Q<=p*T<=p*Q).
  { pose proof (Z.mul_le_mono_nonneg_l (-Q) T p ltac:(lia) ltac:(lia)).
    pose proof (Z.mul_le_mono_nonneg_l T Q p ltac:(lia) ltac:(lia)). nia. }
  assert (HpV : 0<=p*V<=p*Q*K).
  { pose proof (Z.mul_le_mono_nonneg_l V (Q*K) p ltac:(lia) ltac:(lia)). nia. }
  assert (H2K : 2*p*Q*K<=q*Q*K).
  { pose proof (Z.mul_le_mono_nonneg_r (2*p) q (Q*K) ltac:(nia) Hqp). nia. }
  assert (Hbias : 3*p*Q+q*Q*b<=q*Q*lam).
  { assert (H : 3*p+q*b<=q*lam) by nia.
    pose proof (Z.mul_le_mono_nonneg_l _ _ Q ltac:(lia) H). nia. }
  repeat split; nia.
Qed.

Lemma low_push_sound k z S u S1 u1 S2 u2 :
  denotes z S u S1 u1 -> low_call k S1 u1 S2 u2 -> denotes (low_push k z) S u S2 u2.
Proof.
  destruct k as [q p b lam],z as [Q E T V K].
  cbv beta iota zeta delta [denotes low_call low_push den num bias gain scale sc hc offset added].
  intros [HS1 Hu1] [HS2 Hu2]. split; [lia|]. rewrite HS1 in Hu2.
  pose proof (f_equal (fun x => Q*x) Hu2) as H0.
  pose proof (f_equal (fun x => p*x) Hu1) as H1.
  ring_simplify in H0. ring_simplify in H1. ring_simplify. lia.
Qed.

Lemma low_fold_bounded ks z : Forall good ks -> low_bounded z ->
  low_bounded (fold_left (fun z k => low_push k z) ks z).
Proof.
  intro H. revert z. induction H; intros z Hz; cbn; [exact Hz|].
  apply IHForall. apply (low_push_bounded x z H Hz).
Qed.

Definition high_low k z := Summary
  (den k*scale z) (den k*(2*scale z-sc z)) (-num k*hc z)
  (den k*((2*scale z-sc z)*gain k+2*scale z*added z-offset z+3*scale z-hc z*bias k))
  (gain k+added z).

Lemma high_low_identity k : high_low k identity=push k identity.
Proof.
  destruct k. cbv beta iota zeta delta [high_low push identity den num bias gain scale sc hc offset added].
  f_equal; ring.
Qed.

Lemma high_low_push h k z : push k (high_low h z)=high_low h (low_push k z).
Proof.
  destruct h,k,z.
  cbv beta iota zeta delta [high_low push low_push den num bias gain scale sc hc offset added].
  f_equal; ring.
Qed.

Lemma high_low_fold h ks z :
  fold_left (fun z k => push k z) ks (high_low h z)=
  high_low h (fold_left (fun z k => low_push k z) ks z).
Proof. revert z. induction ks; intros z; cbn; [reflexivity|].
  rewrite high_low_push. apply IHks.
Qed.

Lemma high_low_word h ks :
  fold_left (fun z k => push k z) (h::ks) identity=
  high_low h (fold_left (fun z k => low_push k z) ks identity).
Proof. cbn. rewrite <-high_low_identity. apply high_low_fold. Qed.

Lemma low_fold_half ks z : Forall good ks -> low_bounded z -> ks<>[] ->
  let r := fold_left (fun z k => low_push k z) ks z in -scale r<=2*hc r<=scale r.
Proof.
  intro H. revert z. induction H; intros z Hz Hne; [contradiction|].
  cbn. destruct l as [|k ks].
  - cbn. apply (low_push_bounded x z H Hz).
  - apply IHForall; [apply (low_push_bounded x z H Hz)|discriminate].
Qed.

Lemma divisible_small m z : 0<m -> (m|z) -> Z.abs z<m -> z=0.
Proof.
  intros Hm [k Hk] Hz. apply Z.abs_lt in Hz.
  assert (k=0) by nia. nia.
Qed.

(* Integer form of the three-high-call identity: the denominators of the
   two blocks may differ.  Their product, not their maximum, is used. *)
Lemma exact_descent m S H0 H1 H2 Q0 Q1 A0 A1 B0 B1 C0 C1 mass :
  0<m -> (m|H0) -> (m|H1) -> (m|H2) ->
  Q0*H1=A0*S+B0*H0+C0 ->
  Q1*H2=A1*(S+mass)+B1*H1+C1 ->
  Z.abs (A0*A1*mass+A0*C1-A1*C0)<m ->
  A0*C1=A1*(C0-A0*mass).
Proof.
  intros Hm Hd0 Hd1 Hd2 E0 E1 Hbound.
  assert (E : A0*A1*mass+A0*C1-A1*C0 =
    A0*Q1*H2-(A1*Q0+A0*B1)*H1+A1*B0*H0).
  { pose proof (f_equal (fun z => A1*z) E0).
    pose proof (f_equal (fun z => A0*z) E1). nia. }
  assert (Hd : (m|A0*A1*mass+A0*C1-A1*C0)).
  { rewrite E. destruct Hd0 as [k0 ->],Hd1 as [k1 ->],Hd2 as [k2 ->].
    exists (A0*Q1*k2-(A1*Q0+A0*B1)*k1+A1*B0*k0). ring. }
  pose proof (divisible_small _ _ Hm Hd Hbound). nia.
Qed.

Lemma cross_bound Q0 Q1 A0 A1 C0 C1 mass M :
  0<Q0 -> 0<Q1 -> 0<=mass<=M ->
  0<=A0<=2*Q0 -> 0<=A1<=2*Q1 ->
  0<=C0<=Q0*(2*M+2) -> 0<=C1<=Q1*(2*M+2) ->
  Z.abs (A0*A1*mass+A0*C1-A1*C0)<=Q0*Q1*(12*M+8).
Proof.
  intros HQ0 HQ1 Hmass HA0 HA1 HC0 HC1.
  assert (Haa : 0<=A0*A1<=4*Q0*Q1) by nia.
  pose proof (Z.mul_le_mono_nonneg (A0*A1) (4*Q0*Q1) mass M
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_le_mono_nonneg A0 (2*Q0) C1 (Q1*(2*M+2))
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_le_mono_nonneg A1 (2*Q1) C0 (Q0*(2*M+2))
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply Z.abs_le. nia.
Qed.

Lemma dyadic_descent m D d0 d1 S H0 H1 H2 A0 A1 B0 B1 C0 C1 mass M :
  0<=m -> 0<=d0<=D -> 0<=d1<=D -> 0<=mass<=M ->
  0<=A0<=2*2^d0 -> 0<=A1<=2*2^d1 ->
  0<=C0<=2^d0*(2*M+2) -> 0<=C1<=2^d1*(2*M+2) ->
  (2^(m+1)|H0) -> (2^(m+1)|H1) -> (2^(m+1)|H2) ->
  2^d0*H1=A0*S+B0*H0+C0 ->
  2^d1*H2=A1*(S+mass)+B1*H1+C1 ->
  2^(2*D)*(12*M+8)<2^(m+1) ->
  A0*C1=A1*(C0-A0*mass).
Proof.
  intros Hm Hd0 Hd1 Hmass HA0 HA1 HC0 HC1 HH0 HH1 HH2 E0 E1 Hbound.
  assert (HQ0 : 0<2^d0) by (apply Z.pow_pos_nonneg; lia).
  assert (HQ1 : 0<2^d1) by (apply Z.pow_pos_nonneg; lia).
  assert (HQ : 2^d0*2^d1<=2^(2*D)).
  { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  eapply (exact_descent (2^(m+1)) S H0 H1 H2 (2^d0) (2^d1)
    A0 A1 B0 B1 C0 C1 mass); try eassumption.
  - apply Z.pow_pos_nonneg; lia.
  - eapply Z.le_lt_trans with (m:=2^d0*2^d1*(12*M+8));
      [apply cross_bound; eassumption|].
    eapply Z.le_lt_trans; [apply Z.mul_le_mono_nonneg_r; [lia|exact HQ]|exact Hbound].
Qed.

(* In a nonempty low block, |theta|<=1/2.  Everything below is already
   multiplied by the common denominator Q. *)
Lemma contraction_nonempty Q A T V K b lam C :
  0<Q<=A -> -Q<=2*T<=Q -> 0<=V -> 0<=K -> 0<=b<=lam ->
  C=A*lam+2*Q*K-V+3*Q-T*b ->
  2*C<=A*(3*(lam+K)+2*K+6).
Proof.
  intros HQ HT HV HK Hb HC.
  assert (-2*T*b<=Q*b) by nia.
  assert (Q*b<=A*lam) by nia. nia.
Qed.

Lemma contraction_empty Q b lam C :
  0<Q -> 1<=b<=lam -> C=2*Q*lam+3*Q-Q*b ->
  2*C<=(2*Q)*(3*lam+6).
Proof. intros; nia. Qed.

Lemma word_contraction h ks : good h -> Forall good ks ->
  let z := fold_left (fun z k => low_push k z) ks identity in
  let r := fold_left (fun z k => push k z) (h::ks) identity in
  2*offset r<=sc r*(3*added r+2*added z+6).
Proof.
  intros Hh Hks. rewrite high_low_word.
  pose proof (low_fold_bounded _ _ Hks low_identity_bounded) as Hz.
  destruct ks as [|k ks].
  - cbn [fold_left] in *. destruct h as [q p b lam].
    cbv beta iota zeta delta [identity high_low good low_bounded den num bias gain scale sc hc offset added] in *.
    destruct Hh as [Hq [Hp [Hqp [Hb Hl]]]].
    pose proof (contraction_empty 1 b lam (2*lam+3-b) ltac:(lia) ltac:(lia) ltac:(ring)) as Hc.
    pose proof (Z.mul_le_mono_nonneg_l _ _ q ltac:(lia) Hc). nia.
  - pose proof (low_fold_half _ _ Hks low_identity_bounded ltac:(discriminate)) as Hhalf.
    remember (fold_left (fun z k => low_push k z) (k::ks) identity) as z in *.
    destruct h as [q p b lam],z as [Q E T V K].
    cbv beta iota zeta delta [high_low good low_bounded den num bias gain scale sc hc offset added] in *.
    destruct Hh as [Hq [Hp [Hqp [Hb Hl]]]],Hz as [HQ [HE [HT [HK HV]]]].
    pose proof (contraction_nonempty Q (2*Q-E) T V K b lam
      ((2*Q-E)*lam+2*Q*K-V+3*Q-T*b)
      ltac:(lia) Hhalf ltac:(lia) HK ltac:(lia) eq_refl) as Hc.
    pose proof (Z.mul_le_mono_nonneg_l _ _ q ltac:(lia) Hc).
    ring_simplify in Hc. nia.
Qed.

Lemma contract A0 A1 C0 C1 mass K :
  0<A1 -> A0*C1=A1*(C0-A0*mass) ->
  2*C0<=A0*(3*mass+2*K+6) ->
  3*A0*C1<=A1*C0+(2*K+6)*A0*A1.
Proof.
  intros HA E H.
  pose proof (Z.mul_le_mono_nonneg_l _ _ A1 ltac:(lia) H). nia.
Qed.

(* Once exact descent holds, all successive roots share the denominator
   of the first root.  Their numerators alone suffice for the estimates. *)
Lemma propagate_root A C A0 C0 A1 C1 T mass :
  0<A0 -> A*C0=A0*(C-A*T) ->
  A0*C1=A1*(C0-A0*mass) ->
  A*C1=A1*(C-A*(T+mass)).
Proof.
  intros HA H0 H1.
  assert (H : A0*(A*C1-A1*(C-A*(T+mass)))=0).
  { pose proof (f_equal (fun z => A*z) H1) as H2.
    pose proof (f_equal (fun z => A1*z) H0) as H3.
    ring_simplify in H2. ring_simplify in H3. ring_simplify. lia. }
  nia.
Qed.

Lemma shrink_bound (f:nat->Z) C n :
  (forall i, (i<n)%nat -> 3*f (S i)<=f i+2*C) ->
  3^Z.of_nat n*f n<=f 0%nat+(3^Z.of_nat n-1)*C.
Proof.
  induction n; intro H.
  { change (1*f 0%nat<=f 0%nat+(1-1)*C). lia. }
  specialize (IHn ltac:(intros; apply H; lia)).
  pose proof (H n ltac:(lia)) as Hstep.
  assert (Hp : 0<3^Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mul_le_mono_nonneg_l _ _ (3^Z.of_nat n) ltac:(lia) Hstep).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma linear_descent (f:nat->Z) gap n :
  (forall i, (i<n)%nat -> f (S i)<f i-gap) ->
  f n<=f 0%nat-Z.of_nat n*(gap+1).
Proof.
  induction n; intro H.
  { change (f 0%nat<=f 0%nat-0*(gap+1)). lia. }
  specialize (IHn ltac:(intros; apply H; lia)).
  pose proof (H n ltac:(lia)). rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma high_count (f:nat->Z) A B V m t q n :
  0<A -> 0<=B -> 0<m -> 0<=V ->
  V<=3^Z.of_nat t -> B+4<=Z.of_nat q*m ->
  f 0%nat<=A*V -> 0<f n ->
  (forall i, (i<n)%nat -> 3*f (S i)<=f i+2*A*(B+3)) ->
  (forall i, (i<n)%nat -> f (S i)<f i-A*m) ->
  (n<t+q)%nat.
Proof.
  intros HA HB Hm HV Hpow Hq Hstart Hend Hshrink Hdrop.
  destruct (Nat.lt_ge_cases n t) as [Hnt|Hnt]; [lia|].
  pose proof (shrink_bound f (A*(B+3)) t
    ltac:(intros i Hi; pose proof (Hshrink i ltac:(lia)); nia)) as Ht.
  assert (Hp : 0<3^Z.of_nat t) by (apply Z.pow_pos_nonneg; lia).
  assert (Hmid : f t<=A*(B+4)).
  { assert (Hinitial : f 0%nat<=A*3^Z.of_nat t) by nia. nia. }
  pose proof (linear_descent (fun i => f (t+i)%nat) (A*m) (n-t)
    ltac:(intros i Hi; cbv beta; replace (t+S i)%nat with (S (t+i)) by lia;
      apply Hdrop; lia)) as Htail.
  cbv beta in Htail.
  rewrite Nat.add_0_r in Htail. replace (t+(n-t))%nat with n in Htail by lia.
  rewrite Nat2Z.inj_sub in Htail by lia.
  destruct (Nat.lt_ge_cases n (t+q)); [assumption|].
  assert (Hcount : Z.of_nat q<=Z.of_nat n-Z.of_nat t) by lia.
  pose proof (Z.mul_le_mono_nonneg_l _ _ A ltac:(lia) Hq) as Hbound.
  pose proof (Z.mul_le_mono_nonneg_r _ _ (A*m) ltac:(nia) Hcount) as Hlast.
  ring_simplify in Hbound. ring_simplify in Hlast. ring_simplify in Htail. nia.
Qed.

End Block.



Module Table.

Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition nums := map Z.to_nat.
Definition F k q := Prefix.F (Z.to_nat k) (Z.to_nat q).
Definition G k q := Prefix.G (Z.to_nat k) (Z.to_nat q).
Definition run e xs ys := Prefix.Run e (nums xs) (nums ys).
Definition exec e xs ys := Prefix.Exec e (nums xs) (nums ys).

Lemma pow_split k d : 0<=d<=k -> 2^k=2^d*2^(k-d).
Proof. intro H. rewrite <-Z.pow_add_r by lia. f_equal; lia. Qed.

Lemma pow_pos k : 0<=k -> 0<2^k.
Proof. intro H. apply Z.pow_pos_nonneg; lia. Qed.

Lemma run_even u v w r : 0<=u -> 0<=v -> 0<=w -> Z.Even u ->
  run 1 (u::v::w::r) ((u+v+w+3)::r).
Proof.
  intros Hu Hv Hw [n Hn]. assert (Hn0 : 0<=n) by lia.
  unfold run,nums; cbn [map].
  applys_eq (Prefix.one _ _ _ (Prefix.E (Z.to_nat n) (Z.to_nat v) (Z.to_nat w) (map Z.to_nat r)));
    rewrite ?Z2Nat.inj_add, ?Z2Nat.inj_mul by lia; flia.
Qed.

Lemma odd_lookup u v w s q r e ys z :
  0<=u -> 0<=v -> 0<=w -> Z.Odd u -> 1<=s -> 3<=q -> Z.Odd q ->
  u+2*v+3=2^s*q ->
  Prefix.Run e (F s q) (nums ys++[Z.to_nat z]) -> 0<=z -> 0<=z+w-v-1 ->
  run (1+e) (u::v::w::r) ((ys++[z+w-v-1])++r).
Proof.
  intros Hu Hv Hw [n Hn] Hs Hq [t Ht] HH Hr Hzn Hz.
  assert (Hn0 : 0<=n) by lia. assert (Ht0 : 0<=t-1) by lia.
  assert (Hhalf : n+v+2=2^(s-1)*(3+2*(t-1))).
  { rewrite (pow_split s 1) in HH by lia. change (2^1) with 2 in HH. nia. }
  assert (Hnat : (Z.to_nat n+Z.to_nat v+2=
    2^Z.to_nat (s-1)*(3+2*Z.to_nat (t-1)))%nat).
  { apply Nat2Z.inj.
    repeat first [rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul|rewrite Nat2Z.inj_pow|
      rewrite Z2Nat.id by lia].
    exact Hhalf. }
  assert (HF : F s q=Prefix.F (1+Z.to_nat (s-1)) (3+2*Z.to_nat (t-1))).
  { unfold F. f_equal; lia. }
  rewrite HF in Hr.
  pose proof (Prefix.odd_lookup (Z.to_nat (s-1)) (Z.to_nat (t-1))
    (Z.to_nat n) (Z.to_nat v) (Z.to_nat w) (nums r) e _ _ Hnat Hr) as H.
  unfold run,nums. rewrite !map_app. cbn [map].
  applys_eq H; rewrite ?Z2Nat.inj_add, ?Z2Nat.inj_sub by lia; flia.
Qed.

Record pair := Pair { p:Z; d:Z; b:Z; c:Z }.
Definition coefficient k x := p x*2^(k-d x).
Definition left k q x := coefficient k x*q+b x.
Definition right k q x := (2^k-coefficient k x)*q+c x.
Definition values k q x := [left k q x;right k q x].
Definition h x := b x+2*c x+3.
Definition sane k x := 0<=d x<=k /\ 0<p x<2^d x /\ Z.Odd (p x) /\
  1<=b x /\ -1<=c x.
Definition table_pair k x := sane k x /\ 2*p x<=2^d x /\ 0<=c x.

Lemma coefficient_bounds k x : sane k x -> 0<coefficient k x<2^k.
Proof.
  destruct x as [p0 d0 b0 c0].
  cbv beta iota zeta delta [sane coefficient p d b c].
  intros [Hd [Hp H]]. rewrite (pow_split k d0) by lia.
  pose proof (pow_pos (k-d0) ltac:(lia)). nia.
Qed.

Lemma values_nonnegative k q x : sane k x -> 1<=q ->
  1<=left k q x /\ 0<=right k q x.
Proof.
  intros H Hq. pose proof (coefficient_bounds _ _ H).
  unfold sane in H. unfold left,right. nia.
Qed.

Lemma h_positive k x : sane k x -> 2<=h x.
Proof. unfold sane,h; intros; lia. Qed.

Definition separated k x s r := 1<=s<k-d x /\ h x=2^s*r /\ Z.Odd r.
Definition quotient k q x s r := (2^(d x+1)-p x)*2^(k-d x-s)*q+r.

Lemma quotient_spec k q x s r : sane k x -> 1<=q -> Z.Odd q ->
  separated k x s r ->
  3<=quotient k q x s r /\ Z.Odd (quotient k q x s r) /\
  left k q x+2*right k q x+3=2^s*quotient k q x s r.
Proof.
  intros Hx Hq Hqo [[Hs Hsk] [Hh Hr]].
  destruct x as [p0 d0 b0 c0].
  cbv beta iota zeta delta [sane separated quotient left right coefficient h p d b c] in *.
  destruct Hx as [Hd [Hp [Hpo [Hb Hc]]]].
  assert (Hsp : 0<2^s) by (apply pow_pos; lia).
  assert (Hr0 : 1<=r) by nia.
  assert (Hk : 1<=k-d0-s) by lia.
  pose proof (pow_pos (k-d0-s-1) ltac:(lia)) as Hpositive.
  assert (HE : 2^(k-d0-s)=2*2^(k-d0-s-1)).
  { rewrite (pow_split (k-d0-s) 1) by lia. reflexivity. }
  assert (HD : 2^(d0+1)=2*2^d0).
  { rewrite Z.pow_add_r by lia. change (2^1) with 2. ring. }
  split; [rewrite HE,HD; nia|]. split.
  - destruct Hr as [v Hv]. exists ((2^(d0+1)-p0)*2^(k-d0-s-1)*q+v).
    rewrite HE. nia.
  - rewrite (pow_split k d0), (pow_split (k-d0) s) by lia.
    rewrite HD. nia.
Qed.

Lemma values_sum k q x : left k q x+right k q x=2^k*q+b x+c x.
Proof. unfold left,right; ring. Qed.

Lemma left_odd k q x : sane k x -> d x<k -> Z.Odd (b x) -> Z.Odd (left k q x).
Proof.
  intros H Hd [t Ht]. unfold left,coefficient.
  exists (p x*2^(k-d x-1)*q+t).
  rewrite (pow_split (k-d x) 1) by lia. change (2^1) with 2. nia.
Qed.

Definition delta s r y := p y*2^(s-d y)*r.
Definition next x s r y := Pair
  (p y*(2^(d x+1)-p x)) (d x+d y)
  (delta s r y+b y) (h x-delta s r y+c y-c x-1).
Definition widen x := Pair (p x) (d x+1) (b x) (c x).

Lemma next_mass x s r y : b (next x s r y)+c (next x s r y)=b x+c x+b y+c y+2.
Proof. cbv beta iota zeta delta [next h b c]. ring. Qed.

Lemma delta_exact k x s r y : separated k x s r -> table_pair s y ->
  2^d y*delta s r y=p y*h x.
Proof.
  intros [_ [Hh Hr]] [[Hd H] Hother]. unfold delta.
  rewrite Hh, (pow_split s (d y)) by lia. ring.
Qed.

Lemma next_sane k x s r y : sane k x -> separated k x s r -> table_pair s y ->
  sane k (next x s r y) /\ 1<=c (next x s r y).
Proof.
  intros Hx Hs Hy. pose proof (delta_exact _ _ _ _ _ Hs Hy) as He.
  destruct x as [px dx bx cx],y as [py dy by0 cy].
  cbv beta iota zeta delta [sane table_pair separated next h p d b c] in *.
  destruct Hx as [Hdx [Hpx [Hox [Hbx Hcx]]]],
    Hs as [[Hs Hsk] [Hh Hr]],
    Hy as [[Hdy [Hpy [Hoy [Hby Hcy]]]] [Hhalf Hcy0]].
  assert (HD : 2^(dx+1)=2*2^dx).
  { rewrite Z.pow_add_r by lia. change (2^1) with 2. ring. }
  assert (HDs : 2^(dx+dy)=2^dx*2^dy) by (apply Z.pow_add_r; lia).
  rewrite HD,HDs in *. remember (delta s r {|p:=py;d:=dy;b:=by0;c:=cy|}) as z in *.
  assert (Hxpos : 0<2^dx) by (apply pow_pos; lia).
  assert (Hypos : 0<2^dy) by (apply pow_pos; lia).
  assert (Hnewp : 0<py*(2*2^dx-px)<2^dx*2^dy).
  { pose proof (Z.mul_le_mono_nonneg_r _ _ (2*2^dx-px) ltac:(lia) Hhalf). nia. }
  assert (Hnewc : 1<=bx+2*cx+3-z+cy-cx-1).
  { assert (H1 : 0<=(2^dy-py)*(bx-1)) by nia.
    assert (H2 : 0<=(2^dy-2*py)*(cx+2)) by nia. nia. }
  assert (Hnewb : 1<=z+by0) by nia.
  split; [|exact Hnewc]. repeat split; try lia.
  destruct Hox as [a Ha],Hoy as [v Hv].
  exists ((2*v+1)*(2^dx-a)-v-1). nia.
Qed.

Lemma widen_table k x : sane k x -> 0<=c x -> table_pair (k+1) (widen x).
Proof.
  destruct x as [px dx bx cx].
  cbv beta iota zeta delta [sane table_pair widen p d b c].
  intros [Hd [Hp [Ho [Hb Hc]]]] Hc0.
  rewrite Z.pow_add_r by lia. change (2^1) with 2.
  repeat split; try lia; assumption.
Qed.

Lemma widen_values k q x : 0<=k ->
  values (k+1) q (widen x)=[left k q x;right k q x+2^k*q].
Proof.
  intro H. destruct x.
  cbv beta iota zeta delta [values widen left right coefficient p d b c].
  replace (k+1-(d0+1)) with (k-d0) by lia.
  rewrite Z.pow_add_r by lia. change (2^1) with 2. f_equal. f_equal. ring.
Qed.

Lemma next_left k q x s r y : sane k x -> separated k x s r -> table_pair s y ->
  left s (quotient k q x s r) y=left k q (next x s r y).
Proof.
  intros Hx Hs Hy. destruct x as [px dx bx cx],y as [py dy by0 cy].
  cbv beta iota zeta delta [sane table_pair separated quotient next left coefficient delta h p d b c] in *.
  destruct Hx as [Hdx Hx],Hs as [[Hs Hsk] Hr],Hy as [[Hdy Hy] Hy0].
  assert (HP : 2^(s-dy)*2^(k-dx-s)=2^(k-(dx+dy))).
  { rewrite <-Z.pow_add_r by lia. f_equal; lia. }
  rewrite <-HP. ring.
Qed.

Lemma next_right k q x s r y : sane k x -> 1<=q -> Z.Odd q ->
  separated k x s r -> table_pair s y ->
  right s (quotient k q x s r) y-right k q x-1=right k q (next x s r y).
Proof.
  intros Hx Hq Ho Hs Hy.
  pose proof (quotient_spec _ _ _ _ _ Hx Hq Ho Hs) as [_ [_ HH]].
  pose proof (next_left k q x s r y Hx Hs Hy) as HL.
  pose proof (values_sum k q x) as HS0.
  pose proof (values_sum s (quotient k q x s r) y) as HS1.
  pose proof (values_sum k q (next x s r y)) as HS2.
  assert (HC : b (next x s r y)+c (next x s r y)=b x+c x+b y+c y+2).
  { cbv beta iota zeta delta [next h b c]. ring. }
  lia.
Qed.

Definition head_constant k x := if d x <? k then b x else p x+b x.
Definition even_head k x := Z.even (head_constant k x).

Lemma head_parity k q x : sane k x -> Z.Odd q ->
  exists a, left k q x=head_constant k x+2*a.
Proof.
  intros Hx [t Ht]. unfold head_constant.
  destruct (d x <? k) eqn:Hdk.
  - apply Z.ltb_lt in Hdk. exists (p x*2^(k-d x-1)*q).
    unfold left,coefficient. rewrite (pow_split (k-d x) 1) by lia.
    change (2^1) with 2. ring.
  - apply Z.ltb_ge in Hdk. assert (H : d x=k) by (unfold sane in Hx; lia).
    exists (p x*t). unfold left,coefficient. rewrite H, Z.sub_diag, Z.pow_0_r. nia.
Qed.

Lemma even_head_spec k q x : sane k x -> Z.Odd q -> even_head k x=true ->
  Z.Even (left k q x).
Proof.
  intros Hx Hq He. destruct (head_parity _ _ _ Hx Hq) as [a Ha].
  apply Z.even_spec in He. destruct He as [v Hv]. exists (v+a). lia.
Qed.

Lemma odd_head_spec k x s r : separated k x s r -> even_head k x=false -> Z.Odd (b x).
Proof.
  intros [[Hs Hsk] Hr] He. unfold even_head,head_constant in He.
  assert (Hdk : (d x <? k)=true) by (apply Z.ltb_lt; lia). rewrite Hdk in He.
  apply Z.odd_spec. rewrite <-Z.negb_even,He. reflexivity.
Qed.

Inductive entry := One (constant count:Z) | Two (state:pair) (count:Z).
Definition steps f := match f with One _ e | Two _ e => e end.
Definition eval k q f := match f with One v _ => [2^k*q+v] | Two x _ => values k q x end.
Definition well_formed k f := 0<=k /\ 0<=steps f /\
  match f with
  | One v e => v=1+3*e
  | Two x e => table_pair k x /\ b x+c x=1+3*e
  end.
Definition realizes k f := forall q, 1<=q -> Z.Odd q ->
  Prefix.Run (Z.to_nat (steps f)) (F k q) (nums (eval k q f)).
Definition valid k f := well_formed k f /\ realizes k f.

Lemma lookup_two k q x s r y e w : sane k x -> 1<=q -> Z.Odd q ->
  separated k x s r -> even_head k x=false -> valid s (Two y e) -> 0<=w ->
  run (1+Z.to_nat e)
    [left k q x;right k q x;w]
    [left k q (next x s r y);right k q (next x s r y)+w].
Proof.
  intros Hx Hq Ho Hs He [Hy Hreal] Hw.
  destruct Hy as [Hs0 [He0 [Hy Hmass]]].
  pose proof (quotient_spec _ _ _ _ _ Hx Hq Ho Hs) as [HQ [HQo HH]].
  pose proof (values_nonnegative _ _ _ Hx Hq) as [Hu Hv].
  pose proof (next_sane _ _ _ _ _ Hx Hs Hy) as [Hnext Hc].
  pose proof (values_nonnegative _ _ _ Hnext Hq) as [Hu' Hv'].
  pose proof (values_nonnegative s (quotient k q x s r) y (proj1 Hy) ltac:(lia)) as [HU HV].
  specialize (Hreal (quotient k q x s r) ltac:(lia) HQo).
  change (Prefix.Run (Z.to_nat e) (F s (quotient k q x s r))
    (nums [left s (quotient k q x s r) y]++[Z.to_nat (right s (quotient k q x s r) y)])) in Hreal.
  pose proof (next_right _ _ _ _ _ _ Hx Hq Ho Hs Hy) as HR.
  pose proof (odd_lookup (left k q x) (right k q x) w s (quotient k q x s r) []
    (Z.to_nat e) [left s (quotient k q x s r) y] (right s (quotient k q x s r) y)
    ltac:(lia) Hv Hw (left_odd _ _ _ Hx ltac:(unfold separated in Hs; lia)
      (odd_head_spec _ _ _ _ Hs He)) ltac:(unfold separated in Hs; lia)
    HQ HQo HH Hreal HV ltac:(lia)) as Hrun.
  rewrite (next_left k q x s r y Hx Hs Hy) in Hrun.
  replace (right k q (next x s r y)+w) with
    (right s (quotient k q x s r) y+w-right k q x-1) by lia.
  exact Hrun.
Qed.

Lemma lookup_one k q x s r v e w : sane k x -> 1<=q -> Z.Odd q ->
  separated k x s r -> even_head k x=false -> valid s (One v e) -> 0<=w ->
  run (1+Z.to_nat e) [left k q x;right k q x;w]
    [2^k*q+b x+c x+v+2+w].
Proof.
  intros Hx Hq Ho Hs He [[Hs0 [He0 Hv]] Hreal] Hw.
  change (0<=e) in He0. change (v=1+3*e) in Hv.
  pose proof (quotient_spec _ _ _ _ _ Hx Hq Ho Hs) as [HQ [HQo HH]].
  pose proof (values_nonnegative _ _ _ Hx Hq) as [Hu Hright].
  pose proof (values_sum k q x) as Hsum.
  specialize (Hreal (quotient k q x s r) ltac:(lia) HQo).
  change (Prefix.Run (Z.to_nat e) (F s (quotient k q x s r))
    (nums []++[Z.to_nat (2^s*quotient k q x s r+v)])) in Hreal.
  pose proof (odd_lookup (left k q x) (right k q x) w s (quotient k q x s r) []
    (Z.to_nat e) [] (2^s*quotient k q x s r+v)
    ltac:(lia) Hright Hw (left_odd _ _ _ Hx ltac:(unfold separated in Hs; lia)
      (odd_head_spec _ _ _ _ Hs He)) ltac:(unfold separated in Hs; lia)
    HQ HQo HH Hreal ltac:(lia) ltac:(lia)) as Hrun.
  replace (2^k*q+b x+c x+v+2+w) with
    (2^s*quotient k q x s r+v+w-right k q x-1) by lia.
  exact Hrun.
Qed.

Lemma snoc k q : 0<=k -> 0<=q ->
  F (k+1) q=F k q++nums [2^k*q].
Proof.
  intros Hk Hq. unfold F,nums. cbn [map].
  replace (Z.to_nat (k+1)) with (1+Z.to_nat k)%nat by lia.
  rewrite Prefix.F_snoc. do 2 f_equal.
  rewrite Z2Nat.inj_mul, Z2Nat.inj_pow by lia. reflexivity.
Qed.

Lemma realizes_append k f q : realizes k f -> 0<=k -> 1<=q -> Z.Odd q ->
  Prefix.Run (Z.to_nat (steps f)) (F (k+1) q) (nums (eval k q f++[2^k*q])).
Proof.
  intros H Hk Hq Ho. rewrite snoc by lia. unfold nums; rewrite map_app.
  apply Prefix.app,H; assumption.
Qed.

Lemma valid_root : valid 0 (One 1 0).
Proof.
  split; [repeat split; reflexivity || lia|].
  intros q Hq Ho. unfold F,Prefix.F,eval,steps,nums. cbn [Prefix.geometric map Z.to_nat].
  replace (Z.to_nat q+1)%nat with (Z.to_nat (2^0*q+1)) by lia. constructor.
Qed.

Lemma valid_add_one k v e : valid k (One v e) ->
  valid (k+1) (Two (Pair 1 1 v 0) e).
Proof.
  intros [[Hk [He Hv]] Hreal]. change (0<=e) in He. change (v=1+3*e) in Hv.
  split.
  - cbv beta iota zeta delta [well_formed steps table_pair sane p d b c].
    repeat split; try lia. exists 0. reflexivity.
  - intros q Hq Ho. pose proof (realizes_append k (One v e) q Hreal Hk Hq Ho) as H.
    change (Prefix.Run (Z.to_nat e) (F (k+1) q) (nums (values (k+1) q (Pair 1 1 v 0)))).
    replace (values (k+1) q (Pair 1 1 v 0)) with [2^k*q+v;2^k*q]; [exact H|].
    cbv beta iota zeta delta [values left right coefficient p d b c].
    replace (k+1-1) with k by lia. rewrite Z.pow_add_r by lia.
    change (2^1) with 2. f_equal; [ring|]. f_equal; ring.
Qed.

Lemma valid_add_even k x e : valid k (Two x e) -> even_head k x=true ->
  valid (k+1) (One (b x+c x+3) (e+1)).
Proof.
  intros [[Hk [He [Hx Hmass]]] Hreal] Heven.
  change (0<=e) in He.
  split; [change (0<=k+1 /\ 0<=e+1 /\ b x+c x+3=1+3*(e+1)); repeat split; lia|].
  intros q Hq Ho. pose proof (realizes_append k (Two x e) q Hreal Hk Hq Ho) as H.
  pose proof (values_nonnegative _ _ _ (proj1 Hx) Hq) as [Hu Hv].
  pose proof (pow_pos k Hk) as HP.
  pose proof (run_even (left k q x) (right k q x) (2^k*q) [] ltac:(lia) Hv ltac:(nia)
    (even_head_spec _ _ _ (proj1 Hx) Ho Heven)) as Hr.
  pose proof (Prefix.trans _ _ _ _ _ H Hr) as Hrun.
  unfold eval,steps. rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
  replace (2^(k+1)*q+(b x+c x+3)) with (left k q x+right k q x+2^k*q+3).
  - exact Hrun.
  - rewrite values_sum, Z.pow_add_r by lia. change (2^1) with 2. ring.
Qed.

Lemma valid_add_lookup_one k x e s r v f : valid k (Two x e) ->
  separated k x s r -> even_head k x=false -> valid s (One v f) ->
  valid (k+1) (One (b x+c x+v+2) (e+1+f)).
Proof.
  intros [[Hk [He [Hx Hmass]]] Hreal] Hs Ho Hsmall.
  destruct (proj1 Hsmall) as [Hs0 [Hf Hv]].
  change (0<=e) in He. change (0<=f) in Hf. change (v=1+3*f) in Hv.
  split; [change (0<=k+1 /\ 0<=e+1+f /\ b x+c x+v+2=1+3*(e+1+f)); repeat split; lia|].
  intros q Hq Hqo. pose proof (realizes_append k (Two x e) q Hreal Hk Hq Hqo) as H.
  pose proof (pow_pos k Hk) as HP.
  pose proof (lookup_one k q x s r v f (2^k*q) (proj1 Hx) Hq Hqo Hs Ho Hsmall ltac:(nia)) as Hr.
  pose proof (Prefix.trans _ _ _ _ _ H Hr) as Hrun.
  unfold eval,steps. rewrite !Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
  replace (Z.to_nat e+1+Z.to_nat f)%nat with (Z.to_nat e+(1+Z.to_nat f))%nat by lia.
  replace (2^(k+1)*q+(b x+c x+v+2)) with (2^k*q+b x+c x+v+2+2^k*q).
  - exact Hrun.
  - rewrite Z.pow_add_r by lia. change (2^1) with 2. ring.
Qed.

Lemma valid_add_lookup_two k x e s r y f : valid k (Two x e) ->
  separated k x s r -> even_head k x=false -> valid s (Two y f) ->
  valid (k+1) (Two (widen (next x s r y)) (e+1+f)).
Proof.
  intros [[Hk [He [Hx Hmass]]] Hreal] Hs Ho Hsmall.
  destruct (proj1 Hsmall) as [Hs0 [Hf [Hy Hmass']]].
  change (0<=e) in He. change (0<=f) in Hf.
  pose proof (next_sane _ _ _ _ _ (proj1 Hx) Hs Hy) as [Hnext Hc].
  split.
  - change (0<=k+1 /\ 0<=e+1+f /\ table_pair (k+1) (widen (next x s r y)) /\
      b (widen (next x s r y))+c (widen (next x s r y))=1+3*(e+1+f)).
    split; [lia|]. split; [lia|]. split.
    + apply widen_table; [exact Hnext|lia].
    + change (b (next x s r y)+c (next x s r y)=1+3*(e+1+f)).
      rewrite next_mass. lia.
  - intros q Hq Hqo. pose proof (realizes_append k (Two x e) q Hreal Hk Hq Hqo) as H.
    pose proof (pow_pos k Hk) as HP.
    pose proof (lookup_two k q x s r y f (2^k*q) (proj1 Hx) Hq Hqo Hs Ho Hsmall ltac:(nia)) as Hr.
    pose proof (Prefix.trans _ _ _ _ _ H Hr) as Hrun.
    unfold eval,steps. rewrite widen_values by lia.
    rewrite !Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
    replace (Z.to_nat e+1+Z.to_nat f)%nat with (Z.to_nat e+(1+Z.to_nat f))%nat by lia.
    exact Hrun.
Qed.

(* These constructors record the actual recursive dependencies, including
   strict separation.  They are stronger than a bare finite return check. *)
Inductive Built : Z -> entry -> Prop :=
| built_root : Built 0 (One 1 0)
| built_one k v e : Built k (One v e) -> Built (k+1) (Two (Pair 1 1 v 0) e)
| built_even k x e : Built k (Two x e) -> even_head k x=true ->
    Built (k+1) (One (b x+c x+3) (e+1))
| built_lookup_one k x e s r v f : Built k (Two x e) -> separated k x s r ->
    even_head k x=false -> Built s (One v f) ->
    Built (k+1) (One (b x+c x+v+2) (e+1+f))
| built_lookup_two k x e s r y f : Built k (Two x e) -> separated k x s r ->
    even_head k x=false -> Built s (Two y f) ->
    Built (k+1) (Two (widen (next x s r y)) (e+1+f)).

Theorem built_valid k f : Built k f -> valid k f.
Proof.
  intro H. induction H; eauto using valid_root, valid_add_one, valid_add_even,
    valid_add_lookup_one, valid_add_lookup_two.
Qed.

Inductive Boundary (lib:Z->entry->Prop) k : pair -> Z -> nat -> Prop :=
| boundary_even x : even_head k x=true -> Boundary lib k x 1 1
| boundary_one x s r v e : separated k x s r -> even_head k x=false ->
    lib s (One v e) -> Boundary lib k x (1+e) 1
| boundary_two x s r y e f n : separated k x s r -> even_head k x=false ->
    lib s (Two y e) -> Boundary lib k (next x s r y) f n ->
    Boundary lib k x (1+e+f) (1+n).

Lemma pair_depth k x : sane k x -> 1<=d x.
Proof.
  intros [Hd [Hp H]]. destruct (Z.eq_dec (d x) 0); [rewrite e in Hp; change (0<p x<1) in Hp; lia|lia].
Qed.

Lemma run_zero e xs ys : run e (xs++[0]) ys -> exec e xs ys.
Proof.
  unfold run,exec,nums. rewrite map_app. cbn [map]. intro H.
  apply Prefix.zero,Prefix.run_exec,H.
Qed.

Lemma boundary_spec lib k x e n :
  (forall s f, lib s f -> valid s f) -> Boundary lib k x e n -> sane k x ->
  0<=e /\ Z.of_nat n+d x<=k+1 /\
  forall q, 1<=q -> Z.Odd q ->
    exec (Z.to_nat e) (values k q x) [2^k*q+b x+c x+3*e].
Proof.
  intros Hlib H. induction H as [x He|x s r v e Hs Ho Hsmall|
    x s r y e f n Hs Ho Hsmall Htail IH]; intro Hx.
  - split; [lia|]. split; [unfold sane in Hx; lia|].
    intros q Hq Hqo. pose proof (values_nonnegative _ _ _ Hx Hq) as [Hu Hv].
    pose proof (run_even (left k q x) (right k q x) 0 [] ltac:(lia) Hv ltac:(lia)
      (even_head_spec _ _ _ Hx Hqo He)) as Hr.
    apply run_zero. unfold values. replace (2^k*q+b x+c x+3*1) with
      (left k q x+right k q x+0+3) by (rewrite values_sum; ring). exact Hr.
  - specialize (Hlib _ _ Hsmall).
    destruct (proj1 Hlib) as [Hs0 [He Hv]]. change (0<=e) in He. change (v=1+3*e) in Hv.
    split; [lia|]. split; [unfold sane in Hx; lia|].
    intros q Hq Hqo. pose proof (lookup_one k q x s r v e 0 Hx Hq Hqo Hs Ho Hlib ltac:(lia)) as Hr.
    replace (2^k*q+b x+c x+3*(1+e)) with (2^k*q+b x+c x+v+2+0) by lia.
    rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. apply run_zero,Hr.
  - specialize (Hlib _ _ Hsmall).
    destruct (proj1 Hlib) as [Hs0 [He [Hy Hmass]]]. change (0<=e) in He.
    pose proof (next_sane _ _ _ _ _ Hx Hs Hy) as [Hnext Hc].
    destruct (IH Hnext) as [Hf [Hdepth Hexec]].
    split; [lia|]. split.
    + pose proof (pair_depth _ _ (proj1 Hy)). change (Z.of_nat n+(d x+d y)<=k+1) in Hdepth.
      rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. lia.
    + intros q Hq Hqo.
      pose proof (lookup_two k q x s r y e 0 Hx Hq Hqo Hs Ho Hlib ltac:(lia)) as Hr.
      rewrite Z.add_0_r in Hr. apply (run_zero _ (values k q x)) in Hr.
      pose proof (Prefix.exec_trans _ _ _ _ _ Hr (Hexec q Hq Hqo)) as Hrun.
      unfold exec in *. rewrite !Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
      replace (2^k*q+b x+c x+3*(1+e+f)) with
        (2^k*q+b (next x s r y)+c (next x s r y)+3*f).
      * exact Hrun.
      * pose proof (next_mass x s r y). lia.
Qed.

Definition lower x := Pair (p x) (d x) (b x) (c x-1).

Lemma lower_sane k x : table_pair k x -> sane k (lower x).
Proof.
  intros [[Hd [Hp [Ho [Hb Hc]]]] [Hhalf Hc0]].
  change (0<=d x<=k /\ 0<p x<2^d x /\ Z.Odd (p x) /\ 1<=b x /\ -1<=c x-1).
  repeat split; try lia; assumption.
Qed.

Lemma lower_values k q x : values k q (lower x)=[left k q x;right k q x-1].
Proof. cbv beta iota zeta delta [values lower left right coefficient p d b c].
  f_equal. f_equal. ring.
Qed.

Lemma last_minus e k q ys z : 1<=k -> 1<=q -> 1<=z ->
  Prefix.Run e (F k q) (nums (ys++[z])) ->
  Prefix.Run e (G k q) (nums (ys++[z-1])).
Proof.
  intros Hk Hq Hz H. unfold F,G in *. unfold nums in *. rewrite map_app in *.
  cbn [map] in *. replace (Z.to_nat k) with (1+Z.to_nat (k-1))%nat in * by lia.
  assert (Hz' : Z.to_nat z=(1+Z.to_nat (z-1))%nat) by lia. rewrite Hz' in H.
  exact (Prefix.F_to_G e (Z.to_nat (k-1)) (Z.to_nat q) (map Z.to_nat ys)
    (Z.to_nat (z-1)) ltac:(lia) H).
Qed.

Lemma G_single k v e : valid k (One v e) -> 1<=k ->
  forall q, 1<=q -> Z.Odd q ->
    Prefix.Run (Z.to_nat e) (G k q) (nums [2^k*q+v-1]).
Proof.
  intros [[Hk [He Hv]] Hr] Hk1 q Hq Ho.
  change (0<=e) in He. change (v=1+3*e) in Hv.
  pose proof (pow_pos k Hk).
  exact (last_minus (Z.to_nat e) k q [] (2^k*q+v) Hk1 Hq ltac:(nia) (Hr q Hq Ho)).
Qed.

Lemma G_pair k x e : valid k (Two x e) -> 1<=k ->
  forall q, 1<=q -> Z.Odd q ->
    Prefix.Run (Z.to_nat e) (G k q) (nums (values k q (lower x))).
Proof.
  intros [[Hk [He [Hx Hmass]]] Hr] Hk1 q Hq Ho. rewrite lower_values.
  pose proof (coefficient_bounds _ _ (proj1 Hx)) as Hcoeff.
  assert (Hright : 1<=right k q x) by (unfold right; destruct Hx as [H [_ Hc]]; nia).
  exact (last_minus (Z.to_nat e) k q [left k q x] (right k q x) Hk1 Hq Hright (Hr q Hq Ho)).
Qed.

Definition Returns lib k f := match f with
  | One _ _ => True
  | Two x _ => exists e n, Boundary lib k (lower x) e n
  end.

Lemma G_returns lib k f : (forall s g, lib s g -> valid s g) -> valid k f ->
  Returns lib k f -> 1<=k -> forall q, 1<=q -> Z.Odd q ->
    exists e m, Prefix.Exec e (G k q) [m].
Proof.
  intros Hlib Hvalid Hr Hk q Hq Ho. destruct f as [v e|x e].
  - exists (Z.to_nat e),(Z.to_nat (2^k*q+v-1)).
    apply Prefix.run_exec,G_single; assumption.
  - destruct Hr as [f [n Hb]].
    destruct (boundary_spec lib k (lower x) f n Hlib Hb
      (lower_sane _ _ (proj1 (proj2 (proj2 (proj1 Hvalid)))))) as [Hf [Hn Hexec]].
    exists (Z.to_nat e+Z.to_nat f)%nat,
      (Z.to_nat (2^k*q+b (lower x)+c (lower x)+3*f)).
    eapply Prefix.exec_trans; [apply Prefix.run_exec,G_pair; eassumption|apply Hexec; assumption].
Qed.

End Table.

Module UniqueTable.
Import Table.

Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma odd_power_injective s r t u : 0<=s -> 0<=t -> Z.Odd r -> Z.Odd u ->
  2^s*r=2^t*u -> s=t /\ r=u.
Proof.
  assert (Hlt : forall s t r u, 0<=s<t -> Z.Odd r -> 2^s*r=2^t*u -> False).
  { intros a b x y Hab [z Hz] He.
    rewrite (pow_split b a) in He by lia.
    pose proof (pow_pos a ltac:(lia)) as Hp.
    assert (Hx : x=2^(b-a)*y) by nia.
    rewrite (pow_split (b-a) 1) in Hx by lia. change (2^1) with 2 in Hx.
    assert (Hx' : x=2*(2^(b-a-1)*y)) by nia. lia. }
  intros Hs Ht Hr Hu He.
  assert (Hst : s=t).
  { destruct (Z.lt_trichotomy s t) as [H|[H|H]].
    - exfalso. exact (Hlt s t r u ltac:(lia) Hr He).
    - exact H.
    - exfalso. exact (Hlt t s u r ltac:(lia) Hu (eq_sym He)). }
  subst t. pose proof (pow_pos s Hs). split; [reflexivity|nia].
Qed.

Lemma separated_unique k x s r t u : separated k x s r -> separated k x t u ->
  s=t /\ r=u.
Proof.
  intros [[Hs Hsk] [He Hr]] [[Ht Htk] [He' Hu]].
  eapply odd_power_injective; try eassumption; lia.
Qed.

Lemma built_nonnegative k f : Built k f -> 0<=k.
Proof. intro H. exact (proj1 (proj1 (built_valid _ _ H))). Qed.

Theorem built_unique k f : Built k f -> forall g, Built k g -> f=g.
Proof.
  intro H. induction H as [|k v e Hprev IHprev|k x e Hprev IHprev Heven|
    k x e s r v f Hprev IHprev Hsep Hodd Hsmall IHsmall|
    k x e s r y f Hprev IHprev Hsep Hodd Hsmall IHsmall].
  { intros g Hg. inversion Hg; subst; [reflexivity| | | |];
      match goal with Hb:Built ?i ?f |- _ => pose proof (built_nonnegative i f Hb); lia end. }
  all: intros g Hg; inversion Hg; subst.
  all: try solve [exfalso; pose proof (built_nonnegative _ _ Hprev); lia].
  all: match goal with Hindex : ?j + 1 = ?i + 1 |- _ =>
    assert (j=i) by lia; subst j end.
  all: match type of IHprev with forall g, Built ?i g -> _ =>
    match goal with Hb:Built i ?g |- _ =>
    let Heq := fresh "Heq" in pose proof (IHprev g Hb) as Heq; inversion Heq; subst end end.
  all: try reflexivity; try congruence.
  all: match type of Hsep with separated ?k ?x ?s ?r =>
    match goal with Hs:separated k x ?t ?u |- _ =>
    destruct (separated_unique k x s r t u Hsep Hs) as [Hs_eq Hr_eq]; subst end end.
  all: match type of IHsmall with forall g, Built ?i g -> _ =>
    match goal with Hb:Built i ?g |- _ =>
    let Heq := fresh "Heq" in pose proof (IHsmall g Hb) as Heq; inversion Heq; subst end end.
  all: reflexivity.
Qed.

End UniqueTable.

Module CheckTable.
Import Table.

Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.
Local Notation "x && y" := (if x then y else false) : bool_scope.

Fixpoint split2 p : Z*Z := match p with
  | xO p => let '(s,r) := split2 p in (s+1,r)
  | _ => (0,Z.pos p)
  end.

Definition separate k x : option (Z*Z) :=
  match h x with
  | Z.pos p => let '(s,r) := split2 p in
    if ((1<=?s) && (s<?k-d x) && (h x=?2^s*r) && Z.odd r)%bool
    then Some (s,r) else None
  | _ => None
  end.

Lemma separate_spec k x s r : separate k x=Some (s,r) -> separated k x s r.
Proof.
  unfold separate. destruct (h x) as [|p|p] eqn:Hx; try discriminate.
  destruct (split2 p) as [s0 r0].
  destruct ((1<=?s0) && (s0<?k-d x) && (Z.pos p=?2^s0*r0) && Z.odd r0)%bool eqn:H; [|discriminate].
  intro He; injection He as <- <-. repeat rewrite Eqb.and_true_iff in H.
  destruct H as [[[Hs Hsk] Hh] Hr]. apply Z.leb_le in Hs. apply Z.ltb_lt in Hsk.
  apply Z.eqb_eq in Hh. apply Z.odd_spec in Hr. unfold separated. rewrite Hx. repeat split; assumption.
Qed.

Definition advance (lookup:Z->option entry) k f : option entry :=
  match f with
  | One v e => Some (Two (Pair 1 1 v 0) e)
  | Two x e =>
    if even_head k x then Some (One (b x+c x+3) (e+1)) else
    match separate k x with
    | Some (s,r) => match lookup s with
      | Some (One v f) => Some (One (b x+c x+v+2) (e+1+f))
      | Some (Two y f) => Some (Two (widen (next x s r y)) (e+1+f))
      | None => None end
    | None => None end
  end.

Lemma advance_spec lookup k f g :
  (forall s x, lookup s=Some x -> Built s x) -> Built k f ->
  advance lookup k f=Some g -> Built (k+1) g.
Proof.
  intros Hlib Hf. destruct f as [v e|x e]; cbn [advance].
  - intro H; injection H as <-. constructor; assumption.
  - destruct (even_head k x) eqn:He.
    + intro H; injection H as <-. constructor; assumption.
    + destruct (separate k x) as [[s r]|] eqn:Hs; [|discriminate].
      apply separate_spec in Hs. destruct (lookup s) as [[v f|y f]|] eqn:Hsmall; try discriminate;
        intro H; injection H as <-; eauto using built_lookup_one, built_lookup_two.
Qed.

Fixpoint finish fuel (lookup:Z->option entry) k x : option (Z*nat) :=
  match fuel with
  | O => None
  | S fuel => if even_head k x then Some (1,1%nat) else
    match separate k x with
    | Some (s,r) => match lookup s with
      | Some (One _ e) => Some (1+e,1%nat)
      | Some (Two y e) => match finish fuel lookup k (next x s r y) with
        | Some (f,n) => Some (1+e+f,(1+n)%nat)
        | None => None end
      | None => None end
    | None => None end
  end.

Lemma finish_spec fuel lookup k x e n :
  (forall s f, lookup s=Some f -> Built s f) -> finish fuel lookup k x=Some (e,n) ->
  Boundary Built k x e n.
Proof.
  intro Hlib. revert x e n. induction fuel as [|fuel IH]; intros x e n; [discriminate|].
  cbn [finish]. destruct (even_head k x) eqn:He.
  - intro H; injection H as <- <-. constructor; assumption.
  - destruct (separate k x) as [[s r]|] eqn:Hs; [|discriminate]. apply separate_spec in Hs.
    destruct (lookup s) as [[v f|y f]|] eqn:Hsmall; [| |discriminate].
    + intro H; injection H as <- <-. eapply boundary_one; eauto.
    + destruct (finish fuel lookup k (next x s r y)) as [[g m]|] eqn:Htail; [|discriminate].
      intro H; injection H as <- <-. eapply boundary_two; eauto.
Qed.

Definition return_check lookup k f := match f with
  | One _ _ => true
  | Two x _ => match finish 64 lookup k (lower x) with Some _ => true | None => false end
  end.

Lemma return_check_spec lookup k f :
  (forall s g, lookup s=Some g -> Built s g) -> return_check lookup k f=true -> Returns Built k f.
Proof.
  intros Hlib H. destruct f as [v e|x e]; [exact I|]. cbn [return_check] in H.
  destruct (finish 64 lookup k (lower x)) as [[f n]|] eqn:He; [|discriminate].
  exists f,n. eapply finish_spec; eassumption.
Qed.

(* A small immutable bank is sufficient for every lookup in the finite base.
   The checks fail, rather than guessing, if a later row requests another index. *)
Definition lookup (bank:list entry) s := if 0<=?s then nth_error bank (Z.to_nat s) else None.
Definition bank_ok bank := forall i f, nth_error bank i=Some f -> Built (Z.of_nat i) f.

Lemma lookup_spec bank : bank_ok bank -> forall s f, lookup bank s=Some f -> Built s f.
Proof.
  intros H s f. unfold lookup. destruct (0<=?s) eqn:Hs; [|discriminate].
  apply Z.leb_le in Hs. intro Hf. specialize (H _ _ Hf). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma bank_snoc bank f : bank_ok bank -> Built (Z.of_nat (length bank)) f -> bank_ok (bank++[f]).
Proof.
  intros Hbank Hf i g Hget. destruct (lt_dec i (length bank)) as [Hi|Hi].
  - rewrite nth_error_app1 in Hget by lia. apply Hbank,Hget.
  - rewrite nth_error_app2 in Hget by lia. destruct (i-length bank)%nat eqn:Hdiff.
    + cbn in Hget. injection Hget as <-. replace i with (length bank) by lia. exact Hf.
    + destruct n; discriminate.
Qed.

Fixpoint bank_build n : option (list entry) := match n with
  | O => Some [One 1 0]
  | S n => match bank_build n with
    | Some bank => match nth_error bank n with
      | Some f => match advance (lookup bank) (Z.of_nat n) f with
        | Some g => Some (bank++[g])
        | None => None end
      | None => None end
    | None => None end
  end.

Lemma bank_build_spec n bank : bank_build n=Some bank -> length bank=(1+n)%nat /\ bank_ok bank.
Proof.
  revert bank. induction n as [|n IH]; intros bank; cbn [bank_build].
  - intro H; injection H as <-. split; [reflexivity|]. intros [|i] f Hget; [|destruct i; discriminate].
    injection Hget as <-. constructor.
  - destruct (bank_build n) as [xs|] eqn:Hxs; [|discriminate]. destruct (IH _ eq_refl) as [Hlen Hbank].
    destruct (nth_error xs n) as [f|] eqn:Hf; [|discriminate].
    destruct (advance (lookup xs) (Z.of_nat n) f) as [g|] eqn:Hg; [|discriminate].
    intro H; injection H as <-. split; [rewrite app_length; cbn; lia|].
    apply bank_snoc; [assumption|]. rewrite Hlen.
    replace (Z.of_nat (1+n)) with (Z.of_nat n+1) by lia.
    eapply advance_spec; [apply lookup_spec,Hbank|apply Hbank,Hf|exact Hg].
Qed.

Definition depth f := match f with One _ _ => 0 | Two x _ => d x end.
Definition bounded k f := steps f<=4*k^3 /\ depth f<=6*Z.log2_up k+9.
Definition bounds_check k f := ((steps f<=?4*k^3) && (depth f<=?6*Z.log2_up k+9))%bool.

Lemma bounds_check_spec k f : bounds_check k f=true -> bounded k f.
Proof. unfold bounds_check,bounded. rewrite Eqb.and_true_iff,!Z.leb_le. tauto. Qed.

Fixpoint check fuel bank k f := match fuel with
  | O => true
  | S fuel =>
    if (bounds_check k f && return_check (lookup bank) k f)%bool then
      match advance (lookup bank) k f with
      | Some g => check fuel bank (k+1) g
      | None => false end
    else false
  end.

Lemma check_spec fuel bank k f : bank_ok bank -> Built k f -> check fuel bank k f=true ->
  forall j, k<=j<k+Z.of_nat fuel ->
    exists g, Built j g /\ bounded j g /\ Returns Built j g.
Proof.
  intros Hbank. revert k f. induction fuel as [|fuel IH]; intros k f Hf Hcheck j Hj; [lia|].
  cbn [check] in Hcheck.
  destruct (bounds_check k f && return_check (lookup bank) k f)%bool eqn:Hgood; [|discriminate].
  apply Eqb.and_true_iff in Hgood. destruct Hgood as [Hb Hr].
  destruct (advance (lookup bank) k f) as [g|] eqn:Hg; [|discriminate].
  destruct (Z.eq_dec j k) as [->|Hneq].
  - exists f. split; [assumption|]. split; [apply bounds_check_spec,Hb|].
    eapply return_check_spec; [apply lookup_spec,Hbank|exact Hr].
  - eapply IH; [eapply advance_spec; [apply lookup_spec,Hbank|exact Hf|exact Hg]|exact Hcheck|lia].
Qed.

Definition bank := match bank_build 128 with Some xs => xs | None => [] end.

Lemma bank_checked : bank_build 128=Some bank.
Proof. native_check_eq. Qed.

Lemma checked_bank : bank_ok bank.
Proof. exact (proj2 (bank_build_spec _ _ bank_checked)). Qed.

Lemma first : Built 1 (Two (Pair 1 1 1 0) 0).
Proof. change (Built (0+1) (Two (Pair 1 1 1 0) 0)). constructor. constructor. Qed.

Lemma finite_check : check 65536 bank 1 (Two (Pair 1 1 1 0) 0)=true.
Proof. native_check_eq. Qed.

Theorem base_structured k : 1<=k<=65536 ->
  exists f, Built k f /\ bounded k f /\ Returns Built k f.
Proof.
  intro H. eapply (check_spec _ _ _ _ checked_bank first finite_check).
  change (1<=k<1+65536). lia.
Qed.

Lemma bank16 : lookup bank 16=Some (One 37 12).
Proof. native_check_eq. Qed.

Theorem P16 : Built 16 (One 37 12).
Proof. apply (lookup_spec _ checked_bank),bank16. Qed.

End CheckTable.

Module Bridge.
Import Table.

Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition kernel x := Block.Kernel (2^d x) (p x) (b x) (b x+c x+2).

Lemma kernel_good s x : table_pair s x -> Block.good (kernel x).
Proof.
  intros [[Hd [Hp [Ho [Hb Hc]]]] [Hhalf Hc0]].
  change (0<2^d x /\ 0<p x /\ 2*p x<=2^d x /\ 1<=b x /\ b x+2<=b x+c x+2).
  repeat split; lia.
Qed.

Lemma gain_large k f : valid k f -> k<3*(steps f+1).
Proof.
  intros [Hwf Hr]. destruct Hwf as [Hk [He Hwf]].
  specialize (Hr 1 ltac:(lia) ltac:(exists 0; reflexivity)).
  pose proof (Prefix.run_length _ _ _ Hr) as Hl.
  unfold F,Prefix.F,nums in Hl. rewrite map_length in Hl.
  cbn [length] in Hl. rewrite Prefix.geometric_length in Hl.
  assert (Hlen : (length (eval k 1 f)<=2)%nat) by (destruct f; cbn [eval values length]; lia).
  lia.
Qed.

Lemma kernel_gain s x e : valid s (Two x e) -> s<Block.gain (kernel x).
Proof.
  intro H. pose proof (gain_large _ _ H).
  destruct (proj1 H) as [Hs [He [Hx Hmass]]].
  change (s<b x+c x+2). change (s<3*(e+1)) in H0. lia.
Qed.

Lemma lookup_leading k q x s r y : sane k x -> 1<=q -> Z.Odd q ->
  separated k x s r -> table_pair s y ->
  2^d y*left k q (next x s r y)=p y*(left k q x+2*right k q x+3)+2^d y*b y.
Proof.
  intros Hx Hq Ho Hs Hy.
  pose proof (quotient_spec _ _ _ _ _ Hx Hq Ho Hs) as [_ [_ HH]].
  rewrite <-(next_left k q x s r y Hx Hs Hy),HH.
  rewrite (pow_split s (d y)) by (unfold table_pair,sane in Hy; lia).
  unfold left,coefficient. ring.
Qed.

Lemma lookup_call k q x s r y : sane k x -> 1<=q -> Z.Odd q ->
  separated k x s r -> table_pair s y ->
  Block.call (kernel y)
    (left k q x+right k q x) (left k q x+2*right k q x+3)
    (left k q (next x s r y)+right k q (next x s r y))
    (left k q (next x s r y)+2*right k q (next x s r y)+3).
Proof.
  intros Hx Hq Ho Hs Hy.
  pose proof (lookup_leading _ _ _ _ _ _ Hx Hq Ho Hs Hy) as HL.
  assert (HM : left k q (next x s r y)+right k q (next x s r y)=
    left k q x+right k q x+(b y+c y+2)).
  { rewrite !values_sum. pose proof (next_mass x s r y). lia. }
  unfold Block.call. split; [exact HM|].
  change (2^d y*(left k q (next x s r y)+2*right k q (next x s r y)+3)=
    2*2^d y*(left k q x+right k q x)-p y*(left k q x+2*right k q x+3)+
      2^d y*(2*(b y+c y+2)+3-b y)).
  nia.
Qed.

Lemma head_value k q x : sane k x -> Z.Odd q -> Z.even (left k q x)=even_head k x.
Proof.
  intros Hx Hq. destruct (head_parity _ _ _ Hx Hq) as [a Ha]. rewrite Ha.
  rewrite Z.even_add,Z.even_mul. change (Z.even 2) with true.
  change (Bool.eqb (Z.even (head_constant k x)) true=Z.even (head_constant k x)).
  destruct (Z.even (head_constant k x)); reflexivity.
Qed.

Lemma lookup_parity k x s r y : sane k x -> separated k x s r -> table_pair s y ->
  even_head k (next x s r y)=even_head s y.
Proof.
  intros Hx Hs Hy. pose proof (next_sane _ _ _ _ _ Hx Hs Hy) as [Hnext Hc].
  assert (Hodd : Z.Odd 1) by (exists 0; reflexivity).
  rewrite <-(head_value k 1 _ Hnext Hodd),<-(next_left k 1 x s r y Hx Hs Hy).
  apply head_value; [exact (proj1 Hy)|].
  exact (proj1 (proj2 (quotient_spec k 1 x s r Hx ltac:(lia) Hodd Hs))).
Qed.

End Bridge.

Module Finite.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma all_base k f : 1<=k<=65536 -> Table.Built k f ->
  CheckTable.bounded k f /\ Table.Returns Table.Built k f.
Proof.
  intros Hk Hf. destruct (CheckTable.base_structured k Hk) as [g [Hg Hr]].
  pose proof (UniqueTable.built_unique _ _ Hf _ Hg). subst g. exact Hr.
Qed.

Lemma G_returns_base k t : (1<=k<=65536)%nat ->
  exists e m, Prefix.Exec e (Prefix.G k (1+2*t)) [m].
Proof.
  intros [Hk0 Hk]. apply Nat2Z.inj_le in Hk0. apply Nat2Z.inj_le in Hk.
  change (1<=Z.of_nat k) in Hk0. change (Z.of_nat k<=65536) in Hk.
  destruct (CheckTable.base_structured (Z.of_nat k) ltac:(lia))
    as [f [Hf [Hb Hr]]].
  pose proof (Table.G_returns Table.Built (Z.of_nat k) f Table.built_valid
    (Table.built_valid _ _ Hf) Hr ltac:(lia) (Z.of_nat (1+2*t))
    ltac:(lia) ltac:(exists (Z.of_nat t); lia)) as H.
  unfold Table.G in H. rewrite !Nat2Z.id in H. exact H.
Qed.

End Finite.

Module WordArith.


Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition div2 n x := exists q, x=2^n*q.

Lemma div2_zero n : div2 n 0.
Proof. exists 0. ring. Qed.

Lemma div2_refl x : div2 0 x.
Proof. exists x. ring. Qed.

Lemma div2_add n x y : div2 n x -> div2 n y -> div2 n (x+y).
Proof. intros [a Ha] [b Hb]. exists (a+b). nia. Qed.

Lemma div2_sub n x y : div2 n x -> div2 n y -> div2 n (x-y).
Proof. intros [a Ha] [b Hb]. exists (a-b). nia. Qed.

Lemma div2_scale n x a : div2 n x -> div2 n (a*x).
Proof. intros [b Hb]. exists (a*b). nia. Qed.

Lemma div2_weaken n m x : 0<=m<=n -> div2 n x -> div2 m x.
Proof.
  intros H [a Ha]. exists (2^(n-m)*a).
  rewrite Ha,(Table.pow_split n m) by lia. ring.
Qed.

Lemma div2_product n m x y : 0<=n -> 0<=m -> div2 n x -> div2 m y -> div2 (n+m) (x*y).
Proof.
  intros Hn Hm [a Ha] [b Hb]. exists (a*b). rewrite Z.pow_add_r by lia. nia.
Qed.

Lemma div2_cancel n m x : 0<=m<=n -> div2 n (2^m*x) -> div2 (n-m) x.
Proof.
  intros H [a Ha]. exists a. rewrite (Table.pow_split n m) in Ha by lia.
  pose proof (Table.pow_pos m ltac:(lia)). nia.
Qed.

Lemma div2_shift n x : 0<=n -> div2 n x -> x=2^n*Z.shiftr x n.
Proof.
  intros Hn [a Ha]. rewrite Z.shiftr_div_pow2 by lia. rewrite Ha.
  rewrite Z.mul_comm, Z.div_mul by (pose proof (Table.pow_pos n Hn); lia). ring.
Qed.

Lemma odd_not_div n x : 1<=n -> Z.Odd x -> ~div2 n x.
Proof.
  intros Hn [a Ha] Hb. destruct (div2_weaken n 1 x ltac:(lia) Hb) as [b Hb0].
  change (2^1) with 2 in Hb0. lia.
Qed.

Lemma split2_spec p : let '(s,r) := CheckTable.split2 p in
  0<=s /\ Z.pos p=2^s*r /\ Z.Odd r.
Proof.
  induction p; cbn [CheckTable.split2].
  - split; [lia|]. split; [ring|]. exists (Z.pos p). lia.
  - destruct (CheckTable.split2 p) as [s r]. destruct IHp as [Hs [He Ho]].
    split; [lia|]. split; [|assumption]. rewrite Z.pow_add_r by lia.
    change (2^1) with 2. change (Z.pos p~0) with (2*Z.pos p). nia.
  - split; [lia|]. split; [reflexivity|]. exists 0. reflexivity.
Qed.

Definition order n x := match x with
  | Z0 => n
  | Z.pos p | Z.neg p => Z.min n (fst (CheckTable.split2 p))
  end.

Lemma order_spec n x : 0<=n ->
  0<=order n x<=n /\ exists q, x=2^order n x*q /\ (order n x<n -> Z.Odd q).
Proof.
  intro Hn. destruct x as [|p|p]; cbn [order].
  - split; [lia|]. exists 0. split; [ring|lia].
  - pose proof (split2_spec p) as H. destruct (CheckTable.split2 p) as [s r]. cbn [fst].
    destruct H as [Hs [He Ho]]. split; [lia|]. destruct (Z_le_dec n s) as [Hns|Hns].
    + rewrite Z.min_l by lia. exists (2^(s-n)*r). split; [rewrite He,(Table.pow_split s n) by lia; ring|lia].
    + rewrite Z.min_r by lia. exists r. auto.
  - pose proof (split2_spec p) as H. destruct (CheckTable.split2 p) as [s r]. cbn [fst].
    destruct H as [Hs [He [a Ha]]]. split; [lia|]. destruct (Z_le_dec n s) as [Hns|Hns].
    + rewrite Z.min_l by lia. exists (-2^(s-n)*r). split; [|lia].
      change (Z.neg p) with (-Z.pos p). rewrite He,(Table.pow_split s n) by lia. ring.
    + rewrite Z.min_r by lia. exists (-r). split; [change (Z.neg p) with (-Z.pos p); nia|].
      intro H. exists (-a-1). nia.
Qed.

Lemma order_div n x : 0<=n -> div2 (order n x) x.
Proof. intro Hn. destruct (order_spec n x Hn) as [_ [q [Hq Ho]]]. exists q. exact Hq. Qed.

Lemma order_bound n x : 0<=n -> 0<=order n x<=n.
Proof. intro Hn. exact (proj1 (order_spec n x Hn)). Qed.

Lemma order_shift_odd n x : 0<=n -> order n x<n -> Z.Odd (Z.shiftr x (order n x)).
Proof.
  intros Hn Hlt. destruct (order_spec n x Hn) as [Hv [q [Hx Ho]]].
  pose proof (div2_shift (order n x) x ltac:(lia) (order_div n x Hn)) as He.
  pose proof (Table.pow_pos (order n x) ltac:(lia)).
  assert (Hq : Z.shiftr x (order n x)=q) by nia. rewrite Hq. apply Ho,Hlt.
Qed.

Lemma div2_order n x : 0<=n -> (div2 n x <-> order n x=n).
Proof.
  intro Hn. destruct (order_spec n x Hn) as [Hb [q [Hx Hodd]]]. split.
  - intro H. destruct (Z.eq_dec (order n x) n) as [He|He]; [exact He|].
    exfalso. rewrite Hx in H. eapply odd_not_div; [|apply Hodd; lia|].
    + instantiate (1:=n-order n x). lia.
    + apply div2_cancel; [lia|exact H].
  - intro H. rewrite <-H at 1. apply order_div,Hn.
Qed.

Definition divides n x := n<=?order n x.

Lemma divides_spec n x : 0<=n -> (divides n x=true <-> div2 n x).
Proof.
  intro Hn. unfold divides. rewrite Z.leb_le,div2_order by lia.
  pose proof (order_bound n x Hn). lia.
Qed.

Lemma order_compatible n x m q : 0<=n -> 0<=m -> Z.Odd q ->
  div2 n (x-2^m*q) ->
  (order n x<n -> m=order n x) /\ (order n x=n -> n<=m).
Proof.
  intros Hn Hm Hq H.
  destruct (order_spec n x Hn) as [Hv [a [Ha Ho]]].
  assert (Hsame : order n x<n -> m=order n x).
  { intro Hvlt. destruct (Z.lt_trichotomy m (order n x)) as [Hlt|[He|Hgt]]; [|exact He|].
    - assert (H1 : div2 (m+1) x) by (apply (div2_weaken (order n x)); [lia|apply order_div; lia]).
      assert (H2 : div2 (m+1) (x-2^m*q)) by (apply (div2_weaken n); [lia|exact H]).
      assert (H3 : div2 (m+1) (2^m*q)).
      { replace (2^m*q) with (x-(x-2^m*q)) by ring. apply div2_sub; assumption. }
      pose proof (div2_cancel (m+1) m q ltac:(lia) H3) as H4.
      exfalso. eapply odd_not_div; [|exact Hq|exact H4]. lia.
    - assert (H1 : div2 (order n x+1) (2^m*q)).
      { apply (div2_weaken m); [lia|exists q; reflexivity]. }
      assert (H2 : div2 (order n x+1) (x-2^m*q)) by (apply (div2_weaken n); [lia|exact H]).
      assert (H3 : div2 (order n x+1) x).
      { pose proof (div2_add _ _ _ H2 H1) as Hsum.
        replace (x-2^m*q+2^m*q) with x in Hsum by ring. exact Hsum. }
      assert (H3' : div2 (order n x+1) (2^order n x*a)) by (rewrite <-Ha; exact H3).
      pose proof (div2_cancel (order n x+1) (order n x) a ltac:(lia) H3') as H4.
      exfalso. eapply odd_not_div; [|apply Ho; lia|exact H4]. lia. }
  split; [exact Hsame|]. intro Hv0. destruct (Z_le_dec n m) as [Hle|Hle]; [exact Hle|].
  assert (H1 : div2 n x) by (apply div2_order; assumption).
  assert (H2 : div2 n (2^m*q)).
  { replace (2^m*q) with (x-(x-2^m*q)) by ring. apply div2_sub; assumption. }
  pose proof (div2_cancel n m q ltac:(lia) H2) as H3.
  exfalso. eapply odd_not_div; [|exact Hq|exact H3]. lia.
Qed.

End WordArith.

Module WordRelation.
Import WordArith.

Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Record relation := Rel { a:Z; q:Z; c:Z; n:Z; sa:Z; sb:Z; sn:Z }.
Definition holds z S U := 0<=n z /\ 0<=sn z /\ Z.Odd (q z) /\ Z.Odd (sa z) /\
  div2 (n z) (q z*U-a z*S-c z) /\ div2 (sn z) (sa z*S-sb z).

Definition choose z A Q C N a0 b0 p0 :=
  if n z <? N then Rel A Q C N a0 b0 p0 else Rel (a z) (q z) (c z) (n z) a0 b0 p0.

Lemma choose_spec z A Q C N a0 b0 p0 S U : holds z S U -> 0<=N -> Z.Odd Q ->
  div2 N (Q*U-A*S-C) -> 0<=p0 -> Z.Odd a0 -> div2 p0 (a0*S-b0) ->
  holds (choose z A Q C N a0 b0 p0) S U.
Proof.
  intros [Hn [Hp [Hq [Ha [Hr Hs]]]]] HN HQ HR Hp0 Ha0 HS.
  unfold choose. destruct (n z <? N);
    cbv beta iota zeta delta [holds a q c n sa sb sn]; repeat split; assumption.
Qed.

Lemma eliminate z A Q C N S U : holds z S U -> 0<=N -> div2 N (Q*U-A*S-C) ->
  div2 (Z.min N (n z)) ((Q*a z-q z*A)*S-(q z*C-Q*c z)).
Proof.
  intros [Hn [Hp [Hq [Ha [Hr Hs]]]]] HN Hnew.
  pose proof (div2_weaken (n z) (Z.min N (n z)) _ ltac:(lia) Hr) as Hr'.
  pose proof (div2_weaken N (Z.min N (n z)) _ ltac:(lia) Hnew) as Hnew'.
  pose proof (div2_sub _ _ _ (div2_scale _ _ (q z) Hnew') (div2_scale _ _ Q Hr')) as H.
  replace (q z*(Q*U-A*S-C)-Q*(q z*U-a z*S-c z)) with
    ((Q*a z-q z*A)*S-(q z*C-Q*c z)) in H by ring. exact H.
Qed.

Lemma check_constant m A B S : 0<=m -> div2 m (A*S-B) ->
  div2 (order m A) B.
Proof.
  intros Hm H. pose proof (order_bound m A Hm) as Hv.
  pose proof (div2_scale _ _ S (order_div m A Hm)) as HA.
  pose proof (div2_weaken m (order m A) _ ltac:(lia) H) as HB.
  pose proof (div2_sub _ _ _ HA HB) as Hsub.
  replace (S*A-(A*S-B)) with B in Hsub by ring. exact Hsub.
Qed.

Lemma divided_constraint m A B S : 0<=m -> div2 m (A*S-B) ->
  div2 (m-order m A) (Z.shiftr A (order m A)*S-Z.shiftr B (order m A)).
Proof.
  intros Hm H. pose proof (order_bound m A Hm) as Hv.
  pose proof (div2_shift (order m A) A ltac:(lia) (order_div m A Hm)) as HA.
  pose proof (div2_shift (order m A) B ltac:(lia) (check_constant _ _ _ _ Hm H)) as HB.
  apply (div2_cancel m (order m A)); [lia|].
  replace (2^order m A*(Z.shiftr A (order m A)*S-Z.shiftr B (order m A))) with (A*S-B) by nia.
  exact H.
Qed.

Lemma compatible m a0 b0 p0 a1 b1 S : 0<=m -> 0<=p0 ->
  div2 m (a0*S-b0) -> div2 p0 (a1*S-b1) ->
  div2 (Z.min m p0) (a0*b1-a1*b0).
Proof.
  intros Hm Hp H0 H1.
  pose proof (div2_weaken m (Z.min m p0) _ ltac:(lia) H0) as H0'.
  pose proof (div2_weaken p0 (Z.min m p0) _ ltac:(lia) H1) as H1'.
  pose proof (div2_sub _ _ _ (div2_scale _ _ a1 H0') (div2_scale _ _ a0 H1')) as H.
  replace (a1*(a0*S-b0)-a0*(a1*S-b1)) with (a0*b1-a1*b0) in H by ring. exact H.
Qed.

Definition intersect z A Q C N :=
  let m := Z.min N (n z) in
  let aa := Q*a z-q z*A in
  let bb := q z*C-Q*c z in
  let v := order m aa in
  if divides v bb then
    if v <? m then
      let ca := Z.shiftr aa v in
      let cb := Z.shiftr bb v in
      let cp := m-v in
      if divides (Z.min cp (sn z)) (ca*sb z-sa z*cb) then
        if sn z <? cp then Some (choose z A Q C N ca cb cp)
        else Some (choose z A Q C N (sa z) (sb z) (sn z))
      else None
    else Some (choose z A Q C N (sa z) (sb z) (sn z))
  else None.

Lemma intersect_spec z A Q C N S U : holds z S U -> 0<=N -> Z.Odd Q ->
  div2 N (Q*U-A*S-C) ->
  exists z', intersect z A Q C N=Some z' /\ holds z' S U.
Proof.
  intros Hz HN HQ Hnew.
  pose proof (eliminate _ _ _ _ _ _ _ Hz HN Hnew) as Helim.
  pose proof Hz as Hwhole. destruct Hz as [Hn [Hp [Hq [Ha [HU HS]]]]].
  set (m:=Z.min N (n z)) in *. set (aa:=Q*a z-q z*A) in *.
  set (bb:=q z*C-Q*c z) in *. assert (Hm : 0<=m) by (unfold m; lia).
  pose proof (order_bound m aa Hm) as Hv.
  pose proof (check_constant _ _ _ _ Hm Helim) as HB.
  pose proof (divided_constraint _ _ _ _ Hm Helim) as Hdiv.
  unfold intersect. fold m aa bb.
  assert (Htest : divides (order m aa) bb=true) by (apply divides_spec; [lia|exact HB]).
  rewrite Htest. destruct (order m aa <? m) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    pose proof (order_shift_odd _ _ Hm Hlt) as HO.
    pose proof (compatible (m-order m aa) (Z.shiftr aa (order m aa))
      (Z.shiftr bb (order m aa)) (sn z) (sa z) (sb z) S ltac:(lia) Hp Hdiv HS) as HC.
    assert (HCtest : divides (Z.min (m-order m aa) (sn z))
      (Z.shiftr aa (order m aa)*sb z-sa z*Z.shiftr bb (order m aa))=true).
    { apply divides_spec; [lia|exact HC]. }
    rewrite HCtest. destruct (sn z <? m-order m aa);
      eexists; split; [reflexivity| |reflexivity|]; apply choose_spec; try eassumption; try lia.
  - eexists. split; [reflexivity|]. apply choose_spec; eassumption.
Qed.

Definition optional z S U := match z with None => True | Some z => holds z S U end.
Definition add z A Q C N := match z with
  | None => Some (Rel A Q C N 1 0 0)
  | Some z => intersect z A Q C N
  end.

Lemma add_spec z A Q C N S U : optional z S U -> 0<=N -> Z.Odd Q ->
  div2 N (Q*U-A*S-C) -> exists z', add z A Q C N=Some z' /\ holds z' S U.
Proof.
  destruct z as [z|]; [apply intersect_spec|]. intros _ HN HQ Hnew.
  eexists; split; [reflexivity|].
  change (0<=N /\ 0<=0 /\ Z.Odd Q /\ Z.Odd 1 /\ div2 N (Q*U-A*S-C) /\ div2 0 (1*S-0)).
  repeat split; try assumption; try lia; [exists 0; reflexivity|apply div2_refl].
Qed.

(* The old constraints force the valuation of the next head expression,
   or a lower bound for it.  No finite bound on S or U is assumed. *)
Definition elim_a z A Q := Q*a z-q z*A.
Definition elim_b z B Q := q z*B-Q*c z.
Definition cutoff z A Q := Z.min (n z) (sn z+order (n z) (elim_a z A Q)).
Definition residual z A B Q := sa z*elim_b z B Q-elim_a z A Q*sb z.

Lemma pruning_constraint z A B Q S U H : holds z S U ->
  H=A*S-Q*U+B ->
  div2 (cutoff z A Q) (residual z A B Q-sa z*q z*H).
Proof.
  intros [Hn [Hp [Hq [Ha [HU HS]]]]] HH.
  set (aa:=elim_a z A Q). set (bb:=elim_b z B Q).
  pose proof (order_bound (n z) aa Hn) as Hv.
  pose proof (div2_product (sn z) (order (n z) aa) _ _ Hp ltac:(lia) HS (order_div (n z) aa Hn)) as Hmul.
  pose proof (div2_weaken (sn z+order (n z) aa) (cutoff z A Q) _ ltac:(unfold cutoff; fold aa; lia) Hmul) as Hmul'.
  pose proof (div2_scale _ _ (sa z*Q) HU) as Hscaled.
  pose proof (div2_weaken (n z) (cutoff z A Q) _ ltac:(unfold cutoff; fold aa; lia) Hscaled) as Hscaled'.
  pose proof (div2_add _ _ _ Hmul' Hscaled') as Hsum.
  unfold residual. fold aa bb.
  replace (sa z*bb-aa*sb z-sa z*q z*H) with
    ((sa z*S-sb z)*aa+sa z*Q*(q z*U-a z*S-c z)); [exact Hsum|].
  unfold aa,bb,elim_a,elim_b. rewrite HH. ring.
Qed.

Lemma pruning_spec z A B Q S U D s t : holds z S U -> 0<=D -> 0<=s ->
  A*S-Q*U+B=2^(D+s)*(2*t+1) ->
  let bound := cutoff z A Q in let v := order bound (residual z A B Q) in
  (v<bound -> s=v-D) /\ (v=bound -> bound-D<=s).
Proof.
  intros Hz HD Hs HH.
  pose proof (pruning_constraint z A B Q S U (2^(D+s)*(2*t+1)) Hz (eq_sym HH)) as Hdiv.
  destruct Hz as [Hn [Hp [HQ [Ha [HU HS]]]]].
  pose proof (order_bound (n z) (elim_a z A Q) Hn) as Horder.
  assert (Hbound : 0<=cutoff z A Q) by (unfold cutoff; lia).
  assert (Hodd : Z.Odd (sa z*q z*(2*t+1))).
  { destruct HQ as [u Hu],Ha as [v Hv]. exists (2*v*u*(2*t+1)+(v+u)*(2*t+1)+t). nia. }
  replace (residual z A B Q-sa z*q z*(2^(D+s)*(2*t+1))) with
    (residual z A B Q-2^(D+s)*(sa z*q z*(2*t+1))) in Hdiv by ring.
  destruct (order_compatible (cutoff z A Q) (residual z A B Q) (D+s)
    (sa z*q z*(2*t+1)) Hbound ltac:(lia) Hodd Hdiv) as [He Hle].
  split; intro H; [specialize (He H)|specialize (Hle H)]; lia.
Qed.

End WordRelation.

Module WordLibrary.
Import Table.

Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Record kernel := Kernel { index:Z; pair:Table.pair }.
Definition gain k := b (pair k)+c (pair k)+2.
Definition continuing k := exists e, Built (index k) (Two (pair k) e) /\
  1<=index k /\ even_head (index k) (pair k)=false.

Definition bank := match CheckTable.bank_build 2048 with Some xs => xs | None => [] end.
Lemma bank_checked : CheckTable.bank_build 2048=Some bank.
Proof. native_check_eq. Qed.

Lemma bank_valid : length bank=2049%nat /\ CheckTable.bank_ok bank.
Proof. exact (CheckTable.bank_build_spec _ _ bank_checked). Qed.

Lemma row_complete s f : 0<=s<=2048 -> Built s f -> CheckTable.lookup bank s=Some f.
Proof.
  intros Hs Hf. destruct bank_valid as [Hlen Hbank].
  unfold CheckTable.lookup. assert (Hs0 : (0<=?s)=true) by (apply Z.leb_le; lia). rewrite Hs0.
  destruct (nth_error bank (Z.to_nat s)) as [g|] eqn:Hg.
  - specialize (Hbank _ _ Hg). rewrite Z2Nat.id in Hbank by lia.
    pose proof (UniqueTable.built_unique _ _ Hf _ Hbank). subst g. reflexivity.
  - apply nth_error_None in Hg. rewrite Hlen in Hg.
    change (2049<=Z.to_nat s)%nat in Hg. lia.
Qed.

Fixpoint collect k xs := match xs with
  | [] => []
  | f::r => let rest := collect (k+1) r in match f with
    | One _ _ => rest
    | Two x _ => if 1<=?k then if even_head k x then rest else Kernel k x::rest else rest
    end
  end.

Lemma collect_tail k f xs z : In z (collect (k+1) xs) -> In z (collect k (f::xs)).
Proof.
  destruct f; cbn [collect]; [auto|]. destruct (1<=?k), (even_head k state); cbn; auto.
Qed.

Lemma collect_complete k xs i x e : nth_error xs i=Some (Two x e) ->
  1<=k+Z.of_nat i -> even_head (k+Z.of_nat i) x=false ->
  In (Kernel (k+Z.of_nat i) x) (collect k xs).
Proof.
  revert k i. induction xs as [|f xs IH]; intros k [|i] Hget Hk He; try discriminate.
  - injection Hget as Hf. subst f. change (1<=k+0) in Hk. change (even_head (k+0) x=false) in He.
    rewrite Z.add_0_r in *. cbn [collect].
    assert (Hk0 : (1<=?k)=true) by (apply Z.leb_le; lia). rewrite Hk0,He. left; reflexivity.
  - apply collect_tail. replace (k+Z.of_nat (S i)) with ((k+1)+Z.of_nat i) in * by lia.
    eapply IH; eassumption.
Qed.

Definition library := collect 0 bank.

Theorem library_complete k : continuing k -> index k<=2048 -> In k library.
Proof.
  destruct k as [s x]. intros [e [Hb [Hs He]]] Hmax.
  change (Built s (Two x e)) in Hb. change (1<=s) in Hs.
  change (even_head s x=false) in He. change (s<=2048) in Hmax.
  pose proof (row_complete s (Two x e) ltac:(lia) Hb) as Hrow.
  unfold CheckTable.lookup in Hrow.
  assert (Hs0 : (0<=?s)=true) by (apply Z.leb_le; lia). rewrite Hs0 in Hrow.
  unfold library. replace s with (0+Z.of_nat (Z.to_nat s)) by lia.
  eapply collect_complete; [exact Hrow|lia|]. rewrite Z2Nat.id by lia. exact He.
Qed.

Definition action k S U S' U' := S'=S+gain k /\
  2^d (pair k)*U'=p (pair k)*(2*S-U+3)+2^d (pair k)*b (pair k) /\
  exists t, 2*S-U+3=2^index k*(2*t+1).

Inductive trace : list kernel -> Z -> Z -> Prop :=
| trace_nil S U : trace [] S U
| trace_cons k r S U S' U' : action k S U S' U' -> trace r S' U' -> trace (k::r) S U.

End WordLibrary.

Module WordCheck.
Import WordArith WordRelation WordLibrary.

Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.
Local Notation "x && y" := (if x then y else false) : bool_scope.

Record state := State { rel:option relation; P:Z; Q:Z; C:Z; D:Z; mass:Z }.
Definition invariant z S0 U0 S U := 0<=D z /\ Z.Odd (Q z) /\
  2^D z*U=P z*S0+Q z*U0+C z /\ S=S0+mass z /\ optional (rel z) S0 U0.
Definition A z := 2^(D z+1)-P z.
Definition B z := (2*mass z+3)*2^D z-C z.

Lemma head_identity z S0 U0 S U : invariant z S0 U0 S U ->
  2^D z*(2*S-U+3)=A z*S0-Q z*U0+B z.
Proof.
  intros [HD [HQ [HU [HS HR]]]]. unfold A,B.
  rewrite Z.pow_add_r by lia. change (2^1) with 2. nia.
Qed.

Lemma condition_spec z k S0 U0 S U S' U' : invariant z S0 U0 S U -> 0<=index k ->
  action k S U S' U' ->
  div2 (D z+index k+1) (Q z*U0-A z*S0-(B z-2^(D z+index k))).
Proof.
  intros Hz Hk [HS [HU [t Ht]]].
  pose proof (head_identity _ _ _ _ _ Hz) as HH.
  destruct Hz as [HD Hz]. exists (-t).
  rewrite Ht in HH.
  rewrite (Z.pow_add_r 2 (D z+index k) 1) by lia. change (2^1) with 2.
  rewrite (Z.pow_add_r 2 (D z) (index k)) by lia. nia.
Qed.

Definition push z k r := State (Some r)
  (Table.p (pair k)*A z) (-Table.p (pair k)*Q z)
  (Table.p (pair k)*B z+Table.b (pair k)*2^(D z+Table.d (pair k)))
  (D z+Table.d (pair k)) (mass z+gain k).

Lemma push_spec z k r S0 U0 S U S' U' : invariant z S0 U0 S U ->
  0<=Table.d (pair k) -> Z.Odd (Table.p (pair k)) -> action k S U S' U' -> holds r S0 U0 ->
  invariant (push z k r) S0 U0 S' U'.
Proof.
  intros Hz Hd Hp [HS [HU Hs]] Hr.
  pose proof (head_identity _ _ _ _ _ Hz) as HH.
  destruct Hz as [HD [HQ [HU0 [HS0 HR0]]]].
  change (0<=D z+Table.d (pair k) /\ Z.Odd (-Table.p (pair k)*Q z) /\
    2^(D z+Table.d (pair k))*U'=
      Table.p (pair k)*A z*S0+(-Table.p (pair k)*Q z)*U0+
      (Table.p (pair k)*B z+Table.b (pair k)*2^(D z+Table.d (pair k))) /\
    S'=S0+(mass z+gain k) /\ holds r S0 U0).
  split; [lia|]. split.
  - destruct Hp as [a Ha], HQ as [b Hb]. exists (-2*a*b-a-b-1). nia.
  - split; [|split; [lia|assumption]].
    pose proof (f_equal (fun x => 2^D z*x) HU) as He.
    assert (He' : 2^D z*2^Table.d (pair k)*U'=
      Table.p (pair k)*(2^D z*(2*S-U+3))+2^D z*2^Table.d (pair k)*Table.b (pair k)) by nia.
    rewrite HH in He'. rewrite Z.pow_add_r by lia. nia.
Qed.

Definition single s := match CheckTable.lookup WordLibrary.bank s with
  | Some (Table.Two x _) => if 1<=?s then if Table.even_head s x then [] else [Kernel s x] else []
  | _ => []
  end.

Lemma single_complete k : continuing k -> index k<=2048 -> In k (single (index k)).
Proof.
  destruct k as [s x]. intros [e [Hb [Hs He]]] Hmax.
  change (Table.Built s (Table.Two x e)) in Hb. change (1<=s) in Hs.
  change (Table.even_head s x=false) in He. change (s<=2048) in Hmax.
  unfold single. change (index (Kernel s x)) with s.
  rewrite (row_complete s (Table.Two x e) ltac:(lia) Hb).
  assert (Hs0 : (1<=?s)=true) by (apply Z.leb_le; lia). rewrite Hs0,He.
  left; reflexivity.
Qed.

Definition choices z := match rel z with
  | None => library
  | Some r =>
    let bound := cutoff r (A z) (Q z) in
    let v := order bound (residual r (A z) (B z) (Q z)) in
    if v <? bound then single (v-D z)
    else filter (fun k => bound-D z<=?index k) library
  end.

Lemma choices_spec z k S0 U0 S U S' U' : invariant z S0 U0 S U ->
  continuing k -> index k<=2048 -> action k S U S' U' -> In k (choices z).
Proof.
  intros Hz Hk Hmax Hstep.
  destruct Hstep as [HS [HU [t Ht]]].
  pose proof (head_identity _ _ _ _ _ Hz) as HH.
  destruct Hz as [HD [HQ [HU0 [HS0 HR]]]].
  pose proof Hk as Hkeep. destruct Hk as [e [Hbuilt [Hindex Hodd]]].
  assert (HH' : A z*S0-Q z*U0+B z=2^(D z+index k)*(2*t+1)).
  { rewrite <-HH,Ht. rewrite (Z.pow_add_r 2 (D z) (index k)) by lia. ring. }
  unfold choices. destruct (rel z) as [r|] eqn:Hr; [|apply library_complete; assumption].
  change (holds r S0 U0) in HR.
  pose proof (pruning_spec r (A z) (B z) (Q z) S0 U0 (D z) (index k) t HR HD ltac:(lia) HH') as [He Hl].
  set (bound:=cutoff r (A z) (Q z)) in *.
  set (v:=order bound (residual r (A z) (B z) (Q z))) in *.
  assert (Hb : 0<=bound).
  { destruct HR as [Hn [Hp Hrest]]. unfold bound,cutoff.
    pose proof (order_bound (n r) (elim_a r (A z) (Q z)) Hn). lia. }
  pose proof (order_bound bound (residual r (A z) (B z) (Q z)) Hb) as Hv. fold v in Hv.
  destruct (v <? bound) eqn:Hvb.
  - apply Z.ltb_lt in Hvb. rewrite <-(He Hvb). apply single_complete; assumption.
  - apply Z.ltb_ge in Hvb.
    apply (proj2 (filter_In (fun k => bound-D z<=?index k) k library)).
    split; [apply library_complete; assumption|].
    apply Z.leb_le,Hl; lia.
Qed.

Definition advance z k := match add (rel z) (A z) (Q z)
  (B z-2^(D z+index k)) (D z+index k+1) with
  | Some r => Some (push z k r)
  | None => None end.

Lemma advance_spec z k S0 U0 S U S' U' : invariant z S0 U0 S U ->
  continuing k -> action k S U S' U' ->
  exists z', advance z k=Some z' /\ invariant z' S0 U0 S' U'.
Proof.
  intros Hz [e [Hbuilt [Hindex Hodd]]] Hstep.
  pose proof (Table.built_valid _ _ Hbuilt) as [[Hk [He [[Hsan Hrest] Hmass]]] Hreal].
  destruct Hsan as [Hd [Hp [Hpo HB]]].
  pose proof (condition_spec z k S0 U0 S U S' U' Hz ltac:(lia) Hstep) as Hcond.
  pose proof Hz as Hkeep. destruct Hz as [HD [HQ [HU [HS HR]]]].
  destruct (add_spec (rel z) (A z) (Q z) (B z-2^(D z+index k)) (D z+index k+1)
    S0 U0 HR ltac:(lia) HQ Hcond) as [r [Hadd Hholds]].
  exists (push z k r). split; [unfold advance; rewrite Hadd; reflexivity|].
  eapply push_spec; eassumption || lia.
Qed.

Fixpoint every {T} (f:T->bool) xs := match xs with
  | [] => true
  | x::r => if f x then every f r else false
  end.

Lemma every_spec {T} (f:T->bool) xs : every f xs=true -> forall x, In x xs -> f x=true.
Proof.
  induction xs as [|a xs IH]; [intros _ x H; contradiction|]. cbn [every].
  destruct (f a) eqn:Ha; [|discriminate]. intros H x [<-|Hx]; [exact Ha|apply IH; assumption].
Qed.

Fixpoint refute fuel z := match fuel with
  | O => false
  | S fuel => every (fun k => match advance z k with
      | None => true
      | Some z' => refute fuel z' end) (choices z)
  end.

Theorem refute_spec fuel z S0 U0 S U : invariant z S0 U0 S U -> refute fuel z=true ->
  forall word, Forall (fun k => continuing k /\ index k<=2048) word -> trace word S U ->
    (length word<fuel)%nat.
Proof.
  revert z S U. induction fuel as [|fuel IH]; intros z S U Hz Hcheck; [discriminate|].
  intros word Hall Htrace. inversion Htrace as [|k rest S0' U0' S' U' Hstep Htail]; subst.
  - cbn. lia.
  - inversion Hall as [|k0 r0 [Hk Hmax] Hrest]; subst.
    pose proof (choices_spec _ _ _ _ _ _ _ _ Hz Hk Hmax Hstep) as Hin.
    pose proof (every_spec _ _ Hcheck _ Hin) as Hnext.
    destruct (advance_spec _ _ _ _ _ _ _ _ Hz Hk Hstep) as [z' [Hadvance Hz']].
    change ((match advance z k with Some z' => refute fuel z' | None => true end)=true) in Hnext.
    rewrite Hadvance in Hnext.
    specialize (IH _ _ _ Hz' Hnext _ Hrest Htail). cbn [length]. lia.
Qed.

Definition initial := State None 0 1 0 0 0.

Lemma initial_spec S U : invariant initial S U S U.
Proof.
  change (0<=0 /\ Z.Odd 1 /\ 2^0*U=0*S+1*U+0 /\ S=S+0 /\ True).
  split; [lia|]. split; [exists 0; reflexivity|]. repeat split; lia.
Qed.

Lemma finite_check : refute 7 initial=true.
Proof. native_check_eq. Qed.

Theorem F2 word S U : Forall (fun k => continuing k /\ index k<=2048) word -> trace word S U ->
  (length word<=6)%nat.
Proof.
  intros Hall Htrace. pose proof (refute_spec _ _ _ _ _ _ (initial_spec S U) finite_check _ Hall Htrace).
  lia.
Qed.

Lemma finite_bounds : every (fun k =>
  ((Table.d (pair k)<=?5) && (gain k<=?5472))%bool) library=true.
Proof. native_check_eq. Qed.

Lemma kernel_bounds k : continuing k -> index k<=2048 -> Table.d (pair k)<=5 /\ gain k<=5472.
Proof.
  intros Hk Hmax. pose proof (every_spec _ _ finite_bounds k (library_complete _ Hk Hmax)) as H.
  apply Eqb.and_true_iff in H. destruct H as [Hd Hg]. apply Z.leb_le in Hd. apply Z.leb_le in Hg. auto.
Qed.

End WordCheck.

Module WordLink.
Import Table WordLibrary.

Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma continuing_good k : continuing k -> Block.good (Bridge.kernel (pair k)).
Proof.
  intros [e [Hb [Hs He]]]. pose proof (built_valid _ _ Hb) as [[H0 [He0 [Hx Hmass]]] Hr].
  apply Bridge.kernel_good with (s:=index k),Hx.
Qed.

Lemma continuing_gain k : continuing k -> index k<gain k.
Proof.
  intros [e [Hb Hrest]]. exact (Bridge.kernel_gain _ _ _ (built_valid _ _ Hb)).
Qed.

Lemma lookup_action k q x s r y e : sane k x -> 1<=q -> Z.Odd q -> separated k x s r ->
  Built s (Two y e) ->
  action (Kernel s y) (left k q x+right k q x) (left k q x)
    (left k q (next x s r y)+right k q (next x s r y)) (left k q (next x s r y)).
Proof.
  intros Hx Hq Ho Hs Hb. pose proof (built_valid _ _ Hb) as [[Hs0 [He [Hy Hmass]]] Hr].
  change (left k q (next x s r y)+right k q (next x s r y)=
    left k q x+right k q x+(b y+c y+2) /\
    2^d y*left k q (next x s r y)=p y*(2*(left k q x+right k q x)-left k q x+3)+2^d y*b y /\
    exists t,2*(left k q x+right k q x)-left k q x+3=2^s*(2*t+1)).
  split.
  - rewrite !values_sum. pose proof (next_mass x s r y). lia.
  - split.
    + pose proof (Bridge.lookup_leading _ _ _ _ _ _ Hx Hq Ho Hs Hy). nia.
    + destruct (quotient_spec _ _ _ _ _ Hx Hq Ho Hs) as [HQ [[t Ht] HH]].
      exists t. nia.
Qed.

Lemma action_block k S U S' U' : action k S U S' U' ->
  Block.call (Bridge.kernel (pair k)) S (2*S-U+3) S' (2*S'-U'+3).
Proof.
  intros [HS [HU Hodd]]. change (S'=S+gain k /\
    2^d (pair k)*(2*S'-U'+3)=2*2^d (pair k)*S-p (pair k)*(2*S-U+3)+
      2^d (pair k)*(2*gain k+3-b (pair k))).
  split; [exact HS|]. nia.
Qed.

Lemma trace_blocks word S U : trace word S U -> exists S' U',
  Block.calls (map (fun k => Bridge.kernel (pair k)) word) S (2*S-U+3) S' (2*S'-U'+3).
Proof.
  intro H. induction H as [S U|k rest S U S1 U1 Hstep Htail [S' [U' Hblocks]]].
  - exists S,U. constructor.
  - exists S',U'. eapply Block.more_calls; [apply action_block,Hstep|exact Hblocks].
Qed.

Lemma trace_suffix prefix suffix S U : trace (prefix++suffix) S U ->
  exists S' U', trace suffix S' U'.
Proof.
  revert S U. induction prefix as [|k prefix IH]; intros S U H.
  - exists S,U. exact H.
  - inversion H; subst. eapply IH; eassumption.
Qed.

Definition bound L r := forall word S U,
  Forall (fun k => continuing k /\ index k<=L) word -> trace word S U ->
    Z.of_nat (length word)<=r.

Lemma bound_nonnegative L r : bound L r -> 0<=r.
Proof. intro H. exact (H [] 0 0 (Forall_nil _) (trace_nil 0 0)). Qed.

Lemma bound_mono L L' r r' : L'<=L -> r<=r' -> bound L r -> bound L' r'.
Proof.
  intros HL Hr Hb word S U Hall Htrace. specialize (Hb word S U).
  assert (Hall' : Forall (fun k => continuing k /\ index k<=L) word).
  { eapply Forall_impl; [|exact Hall]. intros k [Hk Hindex]. split; [exact Hk|lia]. }
  specialize (Hb Hall' Htrace). lia.
Qed.

Lemma base_bound : bound 2048 6.
Proof.
  intros word S U Hall Htrace. pose proof (WordCheck.F2 word S U Hall Htrace). lia.
Qed.

End WordLink.


Module Phase.
Import Table.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

(* The small boundary stays at index s; the streaming index K grows.
   The difference of coefficient valuations stays equal to gap. *)
Definition copies s r gap x K y :=
  b y=left s r x /\ c y=right s r x /\ K-d y=s-d x+gap.

Lemma copies_head s r gap x K y : sane s x -> Z.Odd r -> 1<=gap ->
  copies s r gap x K y -> even_head K y=even_head s x.
Proof.
  intros Hx Hr Hg [Hb [Hc Hd]].
  assert (Hlt : (d y <? K)=true) by (apply Z.ltb_lt; unfold sane in Hx; lia).
  unfold even_head,head_constant at 1. rewrite Hlt,Hb. apply Bridge.head_value; assumption.
Qed.

Lemma copies_separated s r gap x K y t u : sane s x -> 1<=r -> Z.Odd r ->
  1<=gap -> copies s r gap x K y -> separated s x t u ->
  separated K y t (quotient s r x t u).
Proof.
  intros Hx Hr Ho Hg [Hb [Hc Hd]] Hsep.
  destruct (quotient_spec s r x t u Hx Hr Ho Hsep) as [HQ [HQo HH]].
  split; [unfold separated in Hsep; lia|]. split; [unfold h; rewrite Hb,Hc; exact HH|exact HQo].
Qed.

Lemma copies_next s r gap x K y t u z : sane s x -> copies s r gap x K y ->
  separated s x t u -> table_pair t z ->
  copies s r gap (next x t u z) (K+1) (widen (next y t (quotient s r x t u) z)).
Proof.
  intros Hx [Hb [Hc Hd]] Hsep Hz.
  pose proof (next_left s r x t u z Hx Hsep Hz) as HL.
  assert (HB : b (next y t (quotient s r x t u) z)=left s r (next x t u z)) by exact HL.
  pose proof (next_mass x t u z) as HM.
  pose proof (next_mass y t (quotient s r x t u) z) as HN.
  pose proof (values_sum s r x) as HS.
  pose proof (values_sum s r (next x t u z)) as HT.
  unfold copies. split; [exact HB|]. split.
  - change (c (next y t (quotient s r x t u) z)=right s r (next x t u z)). lia.
  - change (K+1-(d y+d z+1)=s-(d x+d z)+gap). lia.
Qed.

(* span includes both endpoints, so a later induction may stop in the
   middle of a copied stage without using its final singleton. *)
Definition span K n D := forall i, 0<=i<=Z.of_nat n ->
  exists f, Built (K+i) f /\ CheckTable.depth f<=D.

Lemma span_one K y e v f D : Built K (Two y e) -> Built (K+1) (One v f) ->
  d y<=D -> 0<=D -> span K 1 D.
Proof.
  intros H0 H1 HD HD0 i Hi. change (0<=i<=1) in Hi.
  assert (i=0 \/ i=1) by lia. destruct H as [-> | ->].
  - exists (Two y e). rewrite Z.add_0_r. split; assumption.
  - exists (One v f). split; [exact H1|exact HD0].
Qed.

Lemma span_prepend K f n D : Built K f -> CheckTable.depth f<=D ->
  span (K+1) n D -> span K (1+n) D.
Proof.
  intros H0 HD Htail i Hi. destruct (Z.eq_dec i 0) as [-> | Hnz].
  - exists f. rewrite Z.add_0_r. split; assumption.
  - destruct (Htail (i-1)) as [g [Hg Hdepth]].
    + rewrite Nat2Z.inj_add in Hi. change (Z.of_nat 1) with 1 in Hi. lia.
    + exists g. replace (K+i) with (K+1+(i-1)) by lia. auto.
Qed.

Theorem boundary_copy s x f n : Boundary Built s x f n -> sane s x ->
  forall r gap K y e, 1<=r -> Z.Odd r -> 1<=gap ->
  copies s r gap x K y -> Built K (Two y e) ->
  Built (K+Z.of_nat n) (One (b y+c y+3*f) (e+f)) /\
  span K n (K-s-gap+s+Z.of_nat n-1).
Proof.
  intro H. induction H as [x He|x t u v f Hsep Ho Hsmall|
    x t u z f g n Hsep Ho Hsmall Htail IH]; intros Hx r gap K y e Hr Hro Hg Hcopy Hlarge.
  all: pose proof (built_valid _ _ Hlarge) as [[_ [_ [[Hy _] _]]] _].
  - pose proof (copies_head s r gap x K y Hx Hro Hg Hcopy) as HP.
    assert (HB : Built (K+1) (One (b y+c y+3) (e+1))) by (apply built_even; congruence).
    split; [exact HB|]. apply span_one with (y:=y) (e:=e) (v:=b y+c y+3) (f:=e+1); try assumption.
    all: destruct Hcopy as [_ [_ HD]]; unfold sane in Hx,Hy; change (Z.of_nat 1) with 1; lia.
  - pose proof (copies_head s r gap x K y Hx Hro Hg Hcopy) as HP.
    pose proof (copies_separated s r gap x K y t u Hx Hr Hro Hg Hcopy Hsep) as HS.
    pose proof (built_lookup_one K y e t (quotient s r x t u) v f Hlarge HS ltac:(congruence) Hsmall) as HB.
    pose proof (built_valid _ _ Hsmall) as [[Ht [Hf Hv]] Hreal].
    change (v=1+3*f) in Hv.
    assert (HB' : Built (K+1) (One (b y+c y+3*(1+f)) (e+(1+f)))).
    { replace (b y+c y+3*(1+f)) with (b y+c y+v+2) by lia.
      replace (e+(1+f)) with (e+1+f) by lia. exact HB. }
    split; [exact HB'|]. apply span_one with (y:=y) (e:=e) (v:=b y+c y+3*(1+f)) (f:=e+(1+f)); try assumption.
    all: destruct Hcopy as [_ [_ HD]]; unfold sane in Hx,Hy; change (Z.of_nat 1) with 1; lia.
  - pose proof (built_valid _ _ Hsmall) as [[Ht [Hf [Hz Hmass]]] Hreal].
    pose proof (copies_head s r gap x K y Hx Hro Hg Hcopy) as HP.
    pose proof (copies_separated s r gap x K y t u Hx Hr Hro Hg Hcopy Hsep) as HS.
    pose proof (built_lookup_two K y e t (quotient s r x t u) z f Hlarge HS ltac:(congruence) Hsmall) as HB.
    pose proof (copies_next s r gap x K y t u z Hx Hcopy Hsep Hz) as HC.
    destruct (IH (proj1 (next_sane _ _ _ _ _ Hx Hsep Hz)) r gap (K+1)
      (widen (next y t (quotient s r x t u) z)) (e+1+f) Hr Hro Hg HC HB) as [Hend Hspan].
    split.
    + rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
      replace (K+(1+Z.of_nat n)) with (K+1+Z.of_nat n) by lia.
      change (Built (K+1+Z.of_nat n) (One
        (b (next y t (quotient s r x t u) z)+c (next y t (quotient s r x t u) z)+3*g)
        (e+1+f+g))) in Hend.
      rewrite next_mass in Hend.
      replace (b y+c y+3*(1+f+g)) with (b y+c y+b z+c z+2+3*g) by lia.
      replace (e+(1+f+g)) with (e+1+f+g) by lia. exact Hend.
    + apply span_prepend with (f:=Two y e); [exact Hlarge| |].
      * change (d y<=K-s-gap+s+Z.of_nat (1+n)-1).
        destruct Hcopy as [_ [_ HD]]. unfold sane in Hx. rewrite Nat2Z.inj_add.
        change (Z.of_nat 1) with 1. pose proof (Nat2Z.is_nonneg n). lia.
      * replace (K-s-gap+s+Z.of_nat (1+n)-1) with
          (K+1-s-gap+s+Z.of_nat n-1) by (rewrite Nat2Z.inj_add; lia). exact Hspan.
Qed.

Lemma span_mono K n D D' : D<=D' -> span K n D -> span K n D'.
Proof. intros HD Hspan i Hi. destruct (Hspan i Hi) as [f [Hf Hd]]. exists f. split; [exact Hf|lia]. Qed.

Lemma span_zero K f D : Built K f -> CheckTable.depth f<=D -> span K 0 D.
Proof. intros Hf Hd i Hi. change (0<=i<=0) in Hi. assert (i=0) by lia. subst i.
  exists f. rewrite Z.add_0_r. auto.
Qed.

Lemma initial_head l B : 1<=l -> even_head (l+1) (Pair 1 1 B 0)=Z.even B.
Proof.
  intro Hl. unfold even_head,head_constant. change (d (Pair 1 1 B 0)) with 1.
  assert (H : (1 <? l+1)=true) by (apply Z.ltb_lt; lia). rewrite H. reflexivity.
Qed.

Lemma initial_separated l B s r : 1<=s<l -> B+3=2^s*r -> Z.Odd r ->
  separated (l+1) (Pair 1 1 B 0) s r.
Proof. intros Hs HB Hr. change (1<=s<l+1-1 /\ B+2*0+3=2^s*r /\ Z.Odd r). repeat split; try lia; assumption. Qed.

Lemma initial_copies l B s r x : B+3=2^s*r ->
  copies s r (l-s) (lower x) (l+2) (widen (next (Pair 1 1 B 0) s r x)).
Proof.
  intro HB. unfold copies. split; [reflexivity|]. split.
  - change (B+2*0+3-p x*2^(s-d x)*r+c x-0-1=(2^s-p x*2^(s-d x))*r+(c x-1)). nia.
  - change (l+2-(1+d x+1)=s-d x+(l-s)). lia.
Qed.

Lemma odd_factor B s r : 1<=s -> B+3=2^s*r -> Z.even B=false.
Proof.
  intros Hs HB. assert (Ho : Z.Odd B).
  { exists (2^(s-1)*r-2). rewrite (pow_split s 1) in HB by lia. change (2^1) with 2 in HB. nia. }
  apply Z.odd_spec in Ho. rewrite <-Z.negb_even in Ho. destruct (Z.even B); cbn in Ho; congruence.
Qed.

Theorem stage_even l B e : 1<=l -> Built l (One B e) -> Z.even B=true ->
  Built (l+2) (One (B+3) (e+1)) /\ span l 2 1.
Proof.
  intros Hl HB He. pose proof (built_one _ _ _ HB) as H1.
  assert (H2 : Built (l+1+1) (One (B+3) (e+1))).
  { replace (B+3) with (B+0+3) by lia.
    change (Built (l+1+1) (One (b (Pair 1 1 B 0)+c (Pair 1 1 B 0)+3) (e+1))).
    apply built_even; [exact H1|rewrite initial_head by lia; exact He]. }
  split; [replace (l+2) with (l+1+1) by lia; exact H2|].
  change (span l (1+(1+0)) 1).
  apply span_prepend with (f:=One B e); [exact HB|cbn; lia|].
  apply span_prepend with (f:=Two (Pair 1 1 B 0) e); [exact H1|cbn; lia|].
  apply span_zero with (f:=One (B+3) (e+1)); [exact H2|cbn; lia].
Qed.

Theorem stage_odd l B e s r g : Built l (One B e) -> 1<=s<l ->
  B+3=2^s*r -> Z.Odd r -> Built s g -> Returns Built s g ->
  exists n v f, Z.of_nat n<=s /\ Built (l+2+Z.of_nat n) (One v f) /\ span l (2+n) (2*s+1).
Proof.
  intros HB Hs Hfactor Hr Hg Hreturn.
  pose proof (built_valid _ _ HB) as [[Hl [He HBmass]] Hreal].
  change (0<=e) in He. change (B=1+3*e) in HBmass.
  assert (Hr0 : 1<=r) by (pose proof (pow_pos s ltac:(lia)); nia).
  pose proof (built_one _ _ _ HB) as H1.
  pose proof (initial_separated l B s r Hs Hfactor Hr) as HS.
  assert (HO : even_head (l+1) (Pair 1 1 B 0)=false).
  { rewrite initial_head by lia. exact (odd_factor B s r ltac:(lia) Hfactor). }
  assert (Hprefix : forall n, span (l+2) n (2*s+1) -> span l (2+n) (2*s+1)).
  { intros n Hspan. change (span l (1+(1+n)) (2*s+1)).
    apply span_prepend with (f:=One B e); [exact HB|change (0<=2*s+1); lia|].
    apply span_prepend with (f:=Two (Pair 1 1 B 0) e); [exact H1|change (1<=2*s+1); lia|].
    replace (l+1+1) with (l+2) by lia. exact Hspan. }
  destruct g as [v f|x f].
  - pose proof (built_lookup_one _ _ _ _ _ _ _ H1 HS HO Hg) as H2.
    change (Built (l+1+1) (One (B+0+v+2) (e+1+f))) in H2.
    replace (l+1+1) with (l+2) in H2 by lia.
    exists 0%nat,(B+0+v+2),(e+1+f). split; [change (0<=s); lia|]. split.
    + change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact H2.
    + apply Hprefix. apply span_zero with (f:=One (B+0+v+2) (e+1+f)); [exact H2|change (0<=2*s+1); lia].
  - pose proof (built_lookup_two _ _ _ _ _ _ _ H1 HS HO Hg) as H2.
    replace (l+1+1) with (l+2) in H2 by lia.
    pose proof (built_valid _ _ Hg) as [[Hs0 [Hf [Hx Hmass]]] Hruns].
    destruct Hreturn as [j [n Hbound]].
    pose proof (lower_sane _ _ Hx) as Hlow.
    destruct (boundary_spec _ _ _ _ _ built_valid Hbound Hlow) as [Hj [Hn Hexec]].
    pose proof (pair_depth _ _ Hlow) as Hd.
    assert (Hns : Z.of_nat n<=s) by lia.
    destruct (boundary_copy _ _ _ _ Hbound Hlow r (l-s) (l+2)
      (widen (next (Pair 1 1 B 0) s r x)) (e+1+f) Hr0 Hr ltac:(lia)
      (initial_copies _ _ _ _ _ Hfactor) H2) as [Hend Hspan].
    eexists n,_,_. split; [exact Hns|]. split; [exact Hend|].
    apply Hprefix. eapply span_mono; [|exact Hspan]. lia.
Qed.

End Phase.

Module Cubic.
Import Table.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma cubic_exp k : 16<=k -> 12*k^3+4<2^k.
Proof.
  intro Hk. assert (H : forall n,12*(16+Z.of_nat n)^3+4<2^(16+Z.of_nat n)).
  { induction n as [|n IH].
    - vm_compute. reflexivity.
    - rewrite Nat2Z.inj_succ. change (Z.succ (Z.of_nat n)) with (Z.of_nat n+1).
      replace (16+(Z.of_nat n+1)) with ((16+Z.of_nat n)+1) by lia.
      rewrite Z.pow_add_r by lia. change (2^1) with 2. pose proof (Nat2Z.is_nonneg n). nia. }
  replace k with (16+Z.of_nat (Z.to_nat (k-16))) by lia. apply H.
Qed.

Lemma cubic_exp2 x : 16<=x -> 2048*x^3<=12*2^(2*x-2).
Proof.
  intro Hx. assert (H : forall n,2048*(16+Z.of_nat n)^3<=12*2^(2*(16+Z.of_nat n)-2)).
  { induction n as [|n IH].
    - vm_compute. discriminate.
    - rewrite Nat2Z.inj_succ. change (Z.succ (Z.of_nat n)) with (Z.of_nat n+1).
      replace (2*(16+(Z.of_nat n+1))-2) with ((2*(16+Z.of_nat n)-2)+2) by lia.
      rewrite Z.pow_add_r by lia. change (2^2) with 4. pose proof (Nat2Z.is_nonneg n). nia. }
  replace x with (16+Z.of_nat (Z.to_nat (x-16))) by lia. apply H.
Qed.

Lemma lookup_index k s : 2<=k -> 1<=s -> 2^s<=24*k^3+4 -> s<=3*Z.log2_up k+4.
Proof.
  intros Hk Hs Hp. set (x:=Z.log2_up k).
  pose proof (Z.log2_up_nonneg k) as Hx. fold x in Hx.
  destruct (Z.log2_up_spec k ltac:(lia)) as [Hlo Hhi]. fold x in Hhi.
  assert (HE : 2^(3*x+5)=32*2^x*2^x*2^x).
  { replace (3*x+5) with (x+(x+(x+5))) by lia. rewrite !Z.pow_add_r by lia. change (2^5) with 32. ring. }
  pose proof (Z.pow_le_mono_l k (2^x) 3 ltac:(lia)) as Hcube.
  pose proof (pow_pos x Hx) as Hpow.
  assert (HL : 2^s<2^(3*x+5)) by (rewrite HE; nia).
  apply (proj2 (Z.pow_lt_mono_r_iff 2 s (3*x+5) ltac:(lia) ltac:(lia))) in HL. lia.
Qed.

Lemma growth k s : 65536<=k -> 1<=s -> 2^s<=24*k^3+4 -> 1+4*s^3<=12*k^2.
Proof.
  intros Hk Hs Hp. pose proof (lookup_index k s ltac:(lia) Hs Hp) as Hsbound.
  set (x:=Z.log2_up k) in *.
  assert (Hx : 16<=x).
  { pose proof (Z.log2_up_le_mono 65536 k Hk). change (16<=Z.log2_up k) in H. exact H. }
  pose proof (cubic_exp2 x Hx) as HE.
  assert (Hsmall : 1+4*s^3<=2048*x^3).
  { pose proof (Z.pow_le_mono_l s (4*x) 3 ltac:(lia)). nia. }
  destruct (Z.log2_up_spec k ltac:(lia)) as [Hlo Hhi]. fold x in Hlo,Hhi.
  change (2^(x-1)<k) in Hlo.
  assert (HP : 2^(2*x-2)=2^(x-1)*2^(x-1)).
  { rewrite <-Z.pow_add_r by lia. f_equal. lia. }
  rewrite HP in HE. pose proof (pow_pos (x-1) ltac:(lia)). nia.
Qed.

Lemma lookup_h k x e s r : Built k (Two x e) -> separated k x s r ->
  e<=4*k^3 -> 2^s<=24*k^3+4.
Proof.
  intros Hb [[Hs Hsk] [Hh Hr]] He.
  pose proof (built_valid _ _ Hb) as [[Hk [He0 [Hx Hmass]]] Hreal].
  destruct Hx as [[Hd [Hp [Ho [Hb0 Hc]]]] [Hhalf Hc0]].
  unfold h in Hh. pose proof (pow_pos s ltac:(lia)). assert (1<=r) by nia. nia.
Qed.

Theorem built_cubic k f : Built k f -> steps f<=4*k^3.
Proof.
  intro H. pose proof H as Hb.
  induction H as [|k v e HB IH|k x e HB IH He|
    k x e s r v f HB IH HS HO Hsmall IHsmall|
    k x e s r y f HB IH HS HO Hsmall IHsmall].
  { change (0<=0). lia. }
  all: specialize (IH HB); try specialize (IHsmall Hsmall).
  all: destruct (Z_le_gt_dec (k+1) 65536) as [Hbase|Hlarge].
  all: try solve [exact (proj1 (proj1 (Finite.all_base (k+1) _
    ltac:(pose proof (UniqueTable.built_nonnegative _ _ HB); lia) Hb)))].
  - change (e<=4*(k+1)^3). change (e<=4*k^3) in IH. nia.
  - change (e+1<=4*(k+1)^3). change (e<=4*k^3) in IH. nia.
  - change (e+1+f<=4*(k+1)^3). change (e<=4*k^3) in IH. change (f<=4*s^3) in IHsmall.
    pose proof (growth k s ltac:(lia) ltac:(unfold separated in HS; lia) (lookup_h _ _ _ _ _ HB HS IH)). nia.
  - change (e+1+f<=4*(k+1)^3). change (e<=4*k^3) in IH. change (f<=4*s^3) in IHsmall.
    pose proof (growth k s ltac:(lia) ltac:(unfold separated in HS; lia) (lookup_h _ _ _ _ _ HB HS IH)). nia.
Qed.

End Cubic.

Module Stages.
Import Table Phase Cubic.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma split2_spec p : let '(s,r):=CheckTable.split2 p in
  0<=s /\ 1<=r /\ Z.Odd r /\ Z.pos p=2^s*r.
Proof.
  induction p as [p IH|p IH|]; cbn [CheckTable.split2].
  - repeat split; try lia. exists (Z.pos p). rewrite Pos2Z.inj_xI. lia.
  - destruct (CheckTable.split2 p) as [s r] eqn:Hsplit.
    destruct IH as [Hs [Hr [Ho HE]]]. split; [lia|]. split; [exact Hr|]. split; [exact Ho|].
    rewrite Pos2Z.inj_xO,Z.pow_add_r by lia. change (2^1) with 2. nia.
  - repeat split; try lia. exists 0. reflexivity.
Qed.

Lemma stage_parameters l B e : 16<=l -> Built l (One B e) -> Z.even B=false ->
  exists s r, 1<=s<l /\ B+3=2^s*r /\ Z.Odd r /\ s<=3*Z.log2_up l+4.
Proof.
  intros Hl HB Ho. pose proof (built_valid _ _ HB) as [[Hl0 [He Hmass]] Hreal].
  change (0<=e) in He. change (B=1+3*e) in Hmass.
  pose proof (built_cubic _ _ HB) as HE. change (e<=4*l^3) in HE.
  assert (Hpos : 0<B+3) by lia.
  remember (Z.to_pos (B+3)) as p.
  assert (Hp : Z.pos p=B+3) by (subst p; rewrite Z2Pos.id; lia).
  pose proof (split2_spec p) as Hsplit. destruct (CheckTable.split2 p) as [s r].
  destruct Hsplit as [Hs [Hr [Hro Hfactor]]]. rewrite Hp in Hfactor.
  assert (Hs1 : 1<=s).
  { destruct (Z.eq_dec s 0) as [-> | Hnz]; [|lia].
    change (B+3=1*r) in Hfactor. destruct Hro as [t Ht].
    assert (HB_even : Z.Even B) by (exists (t-1); lia).
    apply Z.even_spec in HB_even. congruence. }
  pose proof (pow_pos s Hs) as HP.
  assert (Hbound : 2^s<=12*l^3+4) by nia.
  assert (Hlt : 2^s<2^l) by (pose proof (cubic_exp l Hl); lia).
  apply (proj2 (Z.pow_lt_mono_r_iff 2 s l ltac:(lia) ltac:(lia))) in Hlt.
  exists s,r. repeat split; try assumption; try lia.
  apply lookup_index; lia.
Qed.

Theorem next_stage l B e : 16<=l -> Built l (One B e) ->
  (forall s,1<=s<l -> exists g,Built s g /\ Returns Built s g) ->
  exists n v f, 2<=Z.of_nat n /\ Built (l+Z.of_nat n) (One v f) /\
    span l n (6*Z.log2_up l+9).
Proof.
  intros Hl HB Hsmall. destruct (Z.even B) eqn:He.
  - destruct (stage_even l B e ltac:(lia) HB He) as [Hend Hspan].
    exists 2%nat,(B+3),(e+1). split; [change (2<=2); lia|]. split; [exact Hend|].
    eapply span_mono; [|exact Hspan]. pose proof (Z.log2_up_nonneg l). lia.
  - destruct (stage_parameters _ _ _ Hl HB He) as [s [r [Hs [Hfactor [Hr Hbound]]]]].
    destruct (Hsmall s Hs) as [g [Hg Hreturn]].
    destruct (stage_odd l B e s r g HB Hs Hfactor Hr Hg Hreturn) as [n [v [f [Hn [Hend Hspan]]]]].
    exists (2+n)%nat,v,f. rewrite Nat2Z.inj_add. change (Z.of_nat 2) with 2.
    split; [pose proof (Nat2Z.is_nonneg n); lia|]. split.
    + replace (l+(2+Z.of_nat n)) with (l+2+Z.of_nat n) by lia. exact Hend.
    + eapply span_mono; [|exact Hspan]. lia.
Qed.

(* Only strictly smaller G-indices are assumed.  In particular the
   current phase may end beyond target: span supplies the needed prefix. *)
Theorem through target : 0<=target ->
  (forall s,1<=s<target -> exists g,Built s g /\ Returns Built s g) ->
  exists f,Built target f /\ CheckTable.bounded target f.
Proof.
  intros Htarget Hreturns.
  destruct (Z_le_gt_dec target 16) as [Hbase|Hlarge].
  - destruct (Z.eq_dec target 0) as [-> | Hnz].
    + exists (One 1 0). split; [constructor|]. split; cbn; lia.
    + destruct (CheckTable.base_structured target ltac:(lia)) as [f [Hf [Hbounds Hret]]]. eauto.
  - assert (Hgo : forall n l B e,16<=l<=target -> target-l<=Z.of_nat n ->
      Built l (One B e) -> exists f,Built target f /\ CheckTable.bounded target f).
    { induction n as [|n IH]; intros l B e Hl Hfuel HB.
      - assert (target=l) by (change (target-l<=0) in Hfuel; lia). subst target.
        exists (One B e). split; [exact HB|]. split; [apply built_cubic,HB|].
        change (0<=6*Z.log2_up l+9). pose proof (Z.log2_up_nonneg l). lia.
      - destruct (next_stage l B e ltac:(lia) HB) as [m [v [f [Hm [Hend Hspan]]]]].
        { intros s Hs. apply Hreturns. lia. }
        destruct (Z_le_gt_dec target (l+Z.of_nat m)) as [Hstop|Hnext].
        + destruct (Hspan (target-l) ltac:(lia)) as [g [Hg HD]].
          replace (l+(target-l)) with target in Hg by lia.
          exists g. split; [exact Hg|]. split; [apply built_cubic,Hg|].
          pose proof (Z.log2_up_le_mono l target ltac:(lia)). lia.
        + eapply (IH (l+Z.of_nat m) v f); [lia| |exact Hend].
          rewrite Nat2Z.inj_succ in Hfuel. lia. }
    apply (Hgo (Z.to_nat (target-16)) 16 37 12); try lia. exact CheckTable.P16.
Qed.

End Stages.

Module BoundaryBound.
Import Table WordLibrary.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma constant_action k x s r y e : separated k x s r -> Built s (Two y e) ->
  action (Kernel s y) (b x+c x) (b x)
    (b (next x s r y)+c (next x s r y)) (b (next x s r y)).
Proof.
  intros Hsep Hb. pose proof (built_valid _ _ Hb) as [[Hs [He [Hy Hmass]]] Hreal].
  change (b (next x s r y)+c (next x s r y)=b x+c x+(b y+c y+2) /\
    2^d y*b (next x s r y)=p y*(2*(b x+c x)-b x+3)+2^d y*b y /\
    exists t,2*(b x+c x)-b x+3=2^s*(2*t+1)).
  split; [rewrite next_mass; ring|]. split.
  - pose proof (delta_exact _ _ _ _ _ Hsep Hy) as Hdelta.
    change (2^d y*(delta s r y+b y)=p y*(2*(b x+c x)-b x+3)+2^d y*b y).
    unfold h in Hdelta. nia.
  - destruct Hsep as [_ [HH [t Ht]]]. exists t. unfold h in HH. nia.
Qed.

Lemma small_separated k x L : sane k x -> 1<=L -> d x+L<k -> h x<2^L ->
  even_head k x=false -> exists s r, separated k x s r /\ s<L.
Proof.
  intros Hx HL Hdepth Hbound He.
  pose proof Hx as [Hd [Hp [Ho [Hb Hc]]]].
  assert (Hpos : 0<h x) by (unfold h; lia).
  assert (Hbodd : Z.Odd (b x)).
  { unfold even_head,head_constant in He.
    assert (Hdk : (d x <? k)=true) by (apply Z.ltb_lt; lia). rewrite Hdk in He.
    apply Z.odd_spec. rewrite <-Z.negb_even,He. reflexivity. }
  pose proof (Stages.split2_spec (Z.to_pos (h x))) as Hsplit.
  destruct (CheckTable.split2 (Z.to_pos (h x))) as [s r].
  destruct Hsplit as [Hs [Hr [Hro Hfactor]]]. rewrite Z2Pos.id in Hfactor by lia.
  assert (Hs1 : 1<=s).
  { destruct (Z.eq_dec s 0) as [-> | Hnz]; [|lia].
    change (h x=1*r) in Hfactor. unfold h in Hfactor.
    destruct Hbodd as [a Ha],Hro as [v Hv]. lia. }
  assert (HsL : s<L).
  { apply (proj2 (Z.pow_lt_mono_r_iff 2 s L ltac:(lia) ltac:(lia))).
    pose proof (pow_pos s Hs). nia. }
  exists s,r. split; [|exact HsL]. unfold separated. repeat split; try lia; assumption.
Qed.

(* The budgets pay for every continuing call.  A terminal pair lookup
   and its final even round are accepted immediately, without spending
   another continuing-call slot. *)
Lemma boundary_or_word k L D M : 1<=L -> 0<=D -> 0<=M ->
  (forall s,1<=s<=L -> exists f,Built s f) ->
  (forall s y e,1<=s<=L -> Built s (Two y e) -> d y<=D /\ b y+c y+2<=M) ->
  forall n x, sane k x -> d x+Z.of_nat n*D+L<k ->
    2*(b x+c x+Z.of_nat n*M)+3<2^L ->
    (exists e m,Boundary Built k x e m) \/
    (exists word,length word=n /\ Forall (fun z=>continuing z /\ index z<=L) word /\
      trace word (b x+c x) (b x)).
Proof.
  intros HL HD HM Hlib Hparams n. induction n as [|n IH]; intros x Hx Hdepth Hmass.
  - right. exists ([] : list WordLibrary.kernel). split; [reflexivity|]. split; constructor.
  - destruct (even_head k x) eqn:He.
    + left. exists 1,1%nat. constructor. exact He.
    + assert (Hxdepth : d x+L<k) by (pose proof (Nat2Z.is_nonneg (S n)); nia).
      assert (Hxbound : h x<2^L).
      { pose proof Hx as [_ [_ [_ [Hb Hc]]]]. unfold h.
        pose proof (Nat2Z.is_nonneg (S n)). nia. }
      destruct (small_separated k x L Hx HL Hxdepth Hxbound He) as [s [r [Hsep HsL]]].
      assert (Hs : 1<=s<=L) by (unfold separated in Hsep; lia).
      destruct (Hlib s Hs) as [[v e|y e] Hb].
      * left. exists (1+e),1%nat. eapply boundary_one; eassumption.
      * pose proof (built_valid _ _ Hb) as [[Hs0 [He0 [Hy Hysum]]] Hreal].
        pose proof (next_sane _ _ _ _ _ Hx Hsep Hy) as [Hnext Hc].
        pose proof (Bridge.lookup_parity _ _ _ _ _ Hx Hsep Hy) as HP.
        destruct (even_head s y) eqn:Hparity.
        -- left. exists (1+e+1),2%nat. eapply boundary_two; try eassumption.
           constructor. exact HP.
        -- destruct (Hparams s y e Hs Hb) as [HDy HMy].
           destruct (IH (next x s r y) Hnext) as [[f [m Hreturn]]|[word [Hlen [Hall Htrace]]]].
           ++ change (d x+d y+Z.of_nat n*D+L<k).
              rewrite Nat2Z.inj_succ in Hdepth. nia.
           ++ rewrite next_mass. rewrite Nat2Z.inj_succ in Hmass. nia.
           ++ left. exists (1+e+f),(1+m)%nat. eapply boundary_two; eassumption.
           ++ right. exists (Kernel s y::word). split; [cbn [length]; congruence|]. split.
              ** constructor; [|exact Hall]. split; [|exact (proj2 Hs)].
                 exists e. repeat split; try assumption; exact (proj1 Hs).
              ** eapply trace_cons; [eapply constant_action; eassumption|exact Htrace].
Qed.

Theorem returns_of_bound k x L D M n : 1<=L -> 0<=D -> 0<=M -> sane k x ->
  (forall s,1<=s<=L -> exists f,Built s f) ->
  (forall s y e,1<=s<=L -> Built s (Two y e) -> d y<=D /\ b y+c y+2<=M) ->
  WordLink.bound L (Z.of_nat n-1) -> d x+Z.of_nat n*D+L<k ->
  2*(b x+c x+Z.of_nat n*M)+3<2^L -> exists e m,Boundary Built k x e m.
Proof.
  intros HL HD HM Hx Hlib Hparams Hwords Hdepth Hmass.
  destruct (boundary_or_word k L D M HL HD HM Hlib Hparams n x Hx Hdepth Hmass)
    as [Hreturn|[word [Hlen [Hall Htrace]]]]; [exact Hreturn|].
  specialize (Hwords word (b x+c x) (b x) Hall Htrace). rewrite Hlen in Hwords. lia.
Qed.

End BoundaryBound.

Module Closure.
Import Table.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition good k := exists f,Built k f /\ CheckTable.bounded k f /\ Returns Built k f.
Definition earlier k := forall s,1<=s<k -> good s.
Definition budget k := exists L n,1<=L<k /\ WordLink.bound L (Z.of_nat n-1) /\
  6*Z.log2_up k+9+Z.of_nat n*(6*Z.log2_up L+9)+L<k /\
  2*(12*k^3+Z.of_nat n*(12*L^3+3))+3<2^L.

Lemma earlier_bounds k : earlier k -> forall s f,1<=s<k -> Built s f -> CheckTable.bounded s f.
Proof.
  intros H s f Hs Hf. destruct (H s Hs) as [g [Hg [Hbounds Hret]]].
  pose proof (UniqueTable.built_unique _ _ Hf _ Hg). subst g. exact Hbounds.
Qed.

Lemma kernel_bounds k L : 1<=L<k -> earlier k -> forall s y e,1<=s<=L -> Built s (Two y e) ->
  d y<=6*Z.log2_up L+9 /\ b y+c y+2<=12*L^3+3.
Proof.
  intros HL Hprevious s y e Hs Hb.
  destruct (earlier_bounds k Hprevious s (Two y e) ltac:(lia) Hb) as [HE HD].
  change (e<=4*s^3) in HE. change (d y<=6*Z.log2_up s+9) in HD.
  pose proof (Z.log2_up_le_mono s L ltac:(lia)) as Hlog.
  pose proof (Z.pow_le_mono_l s L 3 ltac:(lia)) as Hpow.
  pose proof (built_valid _ _ Hb) as [[Hs0 [He [Hy Hmass]]] Hreal]. split; lia.
Qed.

(* This is the single induction step.  The only remaining obligation
   for an infinite proof is to provide a budget using smaller entries. *)
Theorem close k : 1<=k -> earlier k -> budget k -> good k.
Proof.
  intros Hk Hprevious [L [n [HL [Hword [Hdepth Hmass]]]]].
  assert (Hentries : forall s,1<=s<k -> exists f,Built s f /\ Returns Built s f).
  { intros s Hs. destruct (Hprevious s Hs) as [f [Hf [Hbounds Hreturn]]]. eauto. }
  destruct (Stages.through k ltac:(lia) Hentries) as [f [Hf Hbounds]].
  exists f. split; [exact Hf|]. split; [exact Hbounds|]. destruct f as [v e|x e]; [exact I|].
  destruct Hbounds as [HE HD]. change (e<=4*k^3) in HE. change (d x<=6*Z.log2_up k+9) in HD.
  pose proof (built_valid _ _ Hf) as [[Hk0 [He [Hx Hsum]]] Hreal].
  apply (BoundaryBound.returns_of_bound k (lower x) L
    (6*Z.log2_up L+9) (12*L^3+3) n).
  - lia.
  - pose proof (Z.log2_up_nonneg L). lia.
  - pose proof (Z.pow_nonneg L 3 ltac:(lia)). lia.
  - apply lower_sane,Hx.
  - intros s Hs. destruct (Hentries s ltac:(lia)) as [g [Hg Hr]]. eauto.
  - apply (kernel_bounds k L HL Hprevious).
  - exact Hword.
  - change (d x+Z.of_nat n*(6*Z.log2_up L+9)+L<k). lia.
  - change (2*(b x+(c x-1)+Z.of_nat n*(12*L^3+3))+3<2^L). lia.
Qed.

Theorem induction_step k : 1<=k -> earlier k -> (65536<k -> budget k) -> good k.
Proof.
  intros Hk Hprevious Hbudget. destruct (Z_le_gt_dec k 65536) as [Hsmall|Hlarge].
  - exact (CheckTable.base_structured k ltac:(lia)).
  - apply close; [exact Hk|exact Hprevious|apply Hbudget; lia].
Qed.

Theorem all_good : (forall k,65536<k -> earlier k -> budget k) -> forall k,1<=k -> good k.
Proof.
  intros Hbudget.
  assert (Hnat : forall n,(1<=n)%nat -> good (Z.of_nat n)).
  { intro n. induction n using lt_wf_ind. intro Hn.
    assert (Hprevious : earlier (Z.of_nat n)).
    { intros s Hs. replace s with (Z.of_nat (Z.to_nat s)) by lia. apply H; lia. }
    apply induction_step; [lia|exact Hprevious|]. intro Hlarge. apply Hbudget; assumption. }
  intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia. apply Hnat. lia.
Qed.

Corollary G_returns : (forall k,65536<k -> earlier k -> budget k) ->
  forall k t,exists e m,Prefix.Exec e (Prefix.G (1+k) (1+2*t)) [m].
Proof.
  intros Hbudget k t.
  destruct (all_good Hbudget (Z.of_nat (1+k)) ltac:(lia)) as [f [Hf [Hbounds Hreturn]]].
  pose proof (Table.G_returns Built (Z.of_nat (1+k)) f built_valid
    (built_valid _ _ Hf) Hreturn ltac:(lia) (Z.of_nat (1+2*t))
    ltac:(lia) ltac:(exists (Z.of_nat t); lia)) as H.
  unfold Table.G in H. rewrite !Nat2Z.id in H. exact H.
Qed.

End Closure.


Module HighPath.
Import Block.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition certified m D M B z := exists d,
  0<=d<=D /\ scale z=2^d /\ scale z<=sc z<=2*scale z /\
  0<offset z<=scale z*(2*M+2) /\ m<added z<=M /\
  2*offset z<=sc z*(3*added z+2*B+6).

Inductive path m D M B : list summary -> Z -> Z -> Prop :=
| path_stop S H : (2^(m+1)|H) -> path m D M B [] S H
| path_step z zs S H H' : (2^(m+1)|H) -> certified m D M B z ->
    denotes z S H (S+added z) H' -> path m D M B zs (S+added z) H' ->
    path m D M B (z::zs) S H.

Lemma path_div m D M B zs S H : path m D M B zs S H -> (2^(m+1)|H).
Proof. intro Hp. inversion Hp; assumption. Qed.

Inductive chain m D M B : list summary -> Prop :=
| chain_one z : certified m D M B z -> chain m D M B [z]
| chain_more z z' zs : certified m D M B z ->
    sc z*offset z'=sc z'*(offset z-sc z*added z) ->
    chain m D M B (z'::zs) -> chain m D M B (z::z'::zs).

Lemma adjacent m D M B z z' S H0 H1 H2 : 0<=m ->
  certified m D M B z -> certified m D M B z' ->
  (2^(m+1)|H0) -> (2^(m+1)|H1) -> (2^(m+1)|H2) ->
  denotes z S H0 (S+added z) H1 ->
  denotes z' (S+added z) H1 (S+added z+added z') H2 ->
  2^(2*D)*(12*M+8)<2^(m+1) ->
  sc z*offset z'=sc z'*(offset z-sc z*added z).
Proof.
  intros Hm [d0 [Hd0 [HQ0 [HA0 [HC0 [HM0 HK0]]]]]]
    [d1 [Hd1 [HQ1 [HA1 [HC1 [HM1 HK1]]]]]] HH0 HH1 HH2 [_ HE0] [_ HE1] Hbudget.
  rewrite HQ0 in HA0,HC0,HE0. rewrite HQ1 in HA1,HC1,HE1.
  pose proof (Table.pow_pos d0 ltac:(lia)). pose proof (Table.pow_pos d1 ltac:(lia)).
  eapply dyadic_descent with (m:=m) (D:=D) (d0:=d0) (d1:=d1)
    (S:=S) (H0:=H0) (H1:=H1) (H2:=H2) (B0:=hc z) (B1:=hc z') (M:=M);
    try eassumption; lia.
Qed.

Lemma path_chain m D M B zs S H : 0<=m -> 2^(2*D)*(12*M+8)<2^(m+1) ->
  path m D M B zs S H -> zs<>[] -> chain m D M B zs.
Proof.
  intros Hm Hbudget Hp. induction Hp as [S H HH|z zs S H H' HH Hz Hstep Htail IH]; intro Hne.
  - contradiction.
  - destruct zs as [|z' zs].
    + constructor. exact Hz.
    + inversion Htail as [|z0 zs0 S0 H0 H2 HH1 Hz' Hstep' Htail']; subst.
      apply chain_more; [exact Hz| |apply IH; discriminate].
      apply (adjacent m D M B z z' S H H' H2); try assumption. eapply path_div,Htail'.
Qed.

(* Numerators of successive positive roots, all using the first root's
   denominator.  This avoids rational arithmetic and changing denominators. *)
Inductive roots A B m : Z -> nat -> Prop :=
| roots_one f : 0<f -> roots A B m f 0
| roots_more f g n : 3*g<=f+2*A*(B+3) -> g<f-A*m ->
    roots A B m g n -> roots A B m f (S n).

Lemma roots_function A B m f n : roots A B m f n -> exists v:nat->Z,
  v 0%nat=f /\ 0<v n /\
  forall i,(i<n)%nat -> 3*v (S i)<=v i+2*A*(B+3) /\ v (S i)<v i-A*m.
Proof.
  intro Hr. induction Hr as [f Hf|f g n Hshrink Hdrop Htail [v [Hv0 [Hvn Hsteps]]]].
  - exists (fun _ : nat=>f). split; [reflexivity|]. split; [exact Hf|intros; lia].
  - exists (fun i=>match i with O=>f | S j=>v j end).
    split; [reflexivity|]. split; [exact Hvn|]. intros [|i] Hi; cbn.
    + rewrite Hv0. auto.
    + apply Hsteps. lia.
Qed.

Lemma roots_count A B m f n t q V : 0<A -> 0<=B -> 0<m -> 0<=V ->
  V<=3^Z.of_nat t -> B+4<=Z.of_nat q*m -> f<=A*V ->
  roots A B m f n -> (n<t+q)%nat.
Proof.
  intros HA HB Hm HV Hpow Hq Hf Hr.
  destruct (roots_function _ _ _ _ _ Hr) as [v [Hv [Hlast Hsteps]]].
  apply (high_count v A B V m t q n); try assumption; [rewrite Hv; exact Hf| |];
    intros i Hi; apply (Hsteps i Hi).
Qed.

Lemma chain_roots m D M B zs : chain m D M B zs -> forall z rest,
  zs=z::rest -> forall A f,0<A -> A*offset z=sc z*f ->
  roots A B m f (length rest).
Proof.
  intro Hchain. induction Hchain as [z Hz|z z' zs Hz Hdescent Htail IH];
    intros z0 rest Heq A f HA Hroot; injection Heq as <- <-.
  - destruct Hz as [d [Hd [HQ [Hsc [Hc [Hmass Hcontract]]]]]].
    pose proof (Table.pow_pos d ltac:(lia)). constructor. nia.
  - pose proof Hz as [d [Hd [HQ [Hsc [Hc [Hmass Hcontract]]]]]].
    pose proof (Table.pow_pos d ltac:(lia)).
    assert (Hnext : A*offset z'=sc z'*(f-A*added z)).
    { pose proof (propagate_root A f (sc z) (offset z) (sc z') (offset z') 0 (added z)
        ltac:(lia) ltac:(rewrite Z.mul_0_r,Z.sub_0_r; exact Hroot) Hdescent) as Hprop.
      rewrite Z.add_0_l in Hprop. exact Hprop. }
    change (roots A B m f (S (length zs))).
    eapply roots_more with (g:=f-A*added z).
    + pose proof (Z.mul_le_mono_nonneg_l _ _ A ltac:(lia) Hcontract). nia.
    + nia.
    + apply (IH z' zs eq_refl A (f-A*added z) HA Hnext).
Qed.

Theorem path_count m D M B zs S H t q : 0<m -> 0<=B -> 0<=M ->
  2*M+2<=3^Z.of_nat t -> B+4<=Z.of_nat q*m ->
  2^(2*D)*(12*M+8)<2^(m+1) -> path m D M B zs S H ->
  (length zs<t+q+1)%nat.
Proof.
  intros Hm HB HM Hpow Hq Hbudget Hp. destruct zs as [|z rest]; [cbn; lia|].
  pose proof (path_chain m D M B (z::rest) S H ltac:(lia) Hbudget Hp ltac:(discriminate)) as Hchain.
  inversion Hp; subst.
  match goal with Hc:certified _ _ _ _ z |- _ =>
    pose proof Hc as [d [Hd [HQ [HA [HC [Hmass Hcontract]]]]]] end.
  pose proof (Table.pow_pos d ltac:(lia)).
  pose proof (chain_roots _ _ _ _ _ Hchain z rest eq_refl (sc z) (offset z) ltac:(lia) eq_refl) as Hr.
  pose proof (roots_count (sc z) B m (offset z) (length rest) t q (2*M+2) ltac:(lia) HB Hm ltac:(lia)
    Hpow Hq ltac:(nia) Hr). cbn [length]. lia.
Qed.

End HighPath.

Module WordBlocks.
Import WordLibrary.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition total (f:kernel->Z) := fold_right (fun k z=>f k+z) 0.
Definition depth k := Table.d (pair k).
Definition kernels := map (fun k=>Bridge.kernel (pair k)).
Definition summary word := fold_left (fun z k=>Block.push k z) (kernels word) Block.identity.

Lemma total_nonnegative f word : Forall (fun k=>0<=f k) word -> 0<=total f word.
Proof. intro H. induction H; change (0<=0) || change (0<=f x+total f l); lia. Qed.

Lemma total_bound f word C : Forall (fun k=>0<=f k<=C) word ->
  0<=total f word<=Z.of_nat (length word)*C.
Proof.
  intro H. induction H.
  - change (0<=0<=0*C). lia.
  - change (0<=f x+total f l<=Z.of_nat (S (length l))*C). rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma fold_added word z : Block.added (fold_left (fun z k=>Block.push k z) (kernels word) z)=
  Block.added z+total gain word.
Proof.
  revert z. induction word as [|k word IH]; intro z; cbn [kernels map fold_left].
  - change (Block.added z=Block.added z+0). lia.
  - rewrite IH. change (Block.added z+gain k+total gain word=Block.added z+(gain k+total gain word)). lia.
Qed.

Lemma low_fold_added word z : Block.added (fold_left (fun z k=>Block.low_push k z) (kernels word) z)=
  Block.added z+total gain word.
Proof.
  revert z. induction word as [|k word IH]; intro z; cbn [kernels map fold_left].
  - change (Block.added z=Block.added z+0). lia.
  - rewrite IH. change (Block.added z+gain k+total gain word=Block.added z+(gain k+total gain word)). lia.
Qed.

Lemma fold_scale word z : Forall (fun k=>0<=depth k) word ->
  Block.scale (fold_left (fun z k=>Block.push k z) (kernels word) z)=Block.scale z*2^total depth word.
Proof.
  intro H. revert z. induction H as [|k word Hk Hall IH]; intro z; cbn [kernels map fold_left].
  - change (Block.scale z=Block.scale z*1). lia.
  - rewrite IH. change (2^depth k*Block.scale z*2^total depth word=Block.scale z*2^(depth k+total depth word)).
    rewrite Z.pow_add_r by (try assumption; apply total_nonnegative,Hall). ring.
Qed.

Lemma fold_strong ks z : Forall Block.good ks -> Block.bounded z -> ks<>[] ->
  Block.bounded (fold_left (fun z k=>Block.push k z) ks z) /\
  Block.scale (fold_left (fun z k=>Block.push k z) ks z)<=Block.sc (fold_left (fun z k=>Block.push k z) ks z) /\
  0<Block.offset (fold_left (fun z k=>Block.push k z) ks z).
Proof.
  intro H. revert z. induction H as [|k ks Hk Hall IH]; intros z Hz Hne; [contradiction|].
  cbn [fold_left]. destruct ks as [|a ks].
  - cbn [fold_left]. apply Block.push_bounded; assumption.
  - apply IH; [apply (Block.push_bounded k z Hk Hz)|discriminate].
Qed.

Lemma summary_data word : Forall continuing word -> word<>[] ->
  0<=total depth word /\ Block.scale (summary word)=2^total depth word /\
  Block.bounded (summary word) /\ Block.scale (summary word)<=Block.sc (summary word) /\
  0<Block.offset (summary word) /\ Block.added (summary word)=total gain word.
Proof.
  intros Hall Hne.
  assert (Hgood : Forall Block.good (kernels word)).
  { apply Forall_map. eapply Forall_impl; [|exact Hall]. intros k Hk. apply WordLink.continuing_good,Hk. }
  assert (Hdepth : Forall (fun k=>0<=depth k) word).
  { eapply Forall_impl; [|exact Hall]. intros k [e [Hb Hrest]].
    pose proof (Table.built_valid _ _ Hb) as [[Hs [He [[Hx Hhalf] Hmass]]] Hr].
    unfold Table.sane in Hx. unfold depth. lia. }
  split; [apply total_nonnegative,Hdepth|]. split.
  - unfold summary. rewrite fold_scale by exact Hdepth. change (1*2^total depth word=2^total depth word). ring.
  - destruct (fold_strong (kernels word) Block.identity Hgood Block.identity_bounded
      ltac:(destruct word; [contradiction|discriminate])) as [Hb [HA HC]].
    split; [exact Hb|]. split; [exact HA|]. split; [exact HC|].
    unfold summary. rewrite fold_added. change (0+total gain word=total gain word). lia.
Qed.

Lemma trace_prefix xs ys S U : trace (xs++ys) S U -> trace xs S U.
Proof.
  revert S U. induction xs as [|k xs IH]; intros S U H.
  - constructor.
  - inversion H; subst. econstructor; [eassumption|eapply IH; eassumption].
Qed.

Lemma trace_split xs ys S U : trace (xs++ys) S U -> exists S' U',
  Block.calls (kernels xs) S (2*S-U+3) S' (2*S'-U'+3) /\ trace ys S' U'.
Proof.
  revert S U. induction xs as [|k xs IH]; intros S U H.
  - exists S,U. split; [constructor|exact H].
  - inversion H; subst.
    match goal with Htail:trace (xs++ys) ?S1 ?U1 |- _ =>
      destruct (IH S1 U1 Htail) as [S2 [U2 [Hcalls Hrest]]] end.
    exists S2,U2. split; [|exact Hrest]. econstructor; [eapply WordLink.action_block; eassumption|exact Hcalls].
Qed.

Lemma summary_sound word S U S' U' : Block.calls (kernels word) S (2*S-U+3) S' (2*S'-U'+3) ->
  Block.denotes (summary word) S (2*S-U+3) S' (2*S'-U'+3).
Proof.
  intro H. apply (Block.fold_sound _ _ _ _ _ H Block.identity S (2*S-U+3)).
  split; change (S=S+0) || change (1*(2*S-U+3)=0*S+1*(2*S-U+3)+0); ring.
Qed.

Lemma high_div m k word S U : 0<=m -> m<index k -> trace (k::word) S U -> (2^(m+1)|2*S-U+3).
Proof.
  intros Hm Hhigh Htrace. inversion Htrace; subst.
  match goal with Ha:action k S U _ _ |- _ => destruct Ha as [_ [_ [t Ht]]] end.
  rewrite Ht,(Table.pow_split (index k) (m+1)) by lia.
  exists (2^(index k-(m+1))*(2*t+1)). ring.
Qed.

Lemma certified_block m r dL dm gL gm k lows S U :
  0<=m -> 0<=r -> 0<=dm -> 0<=gm -> m<index k ->
  continuing k -> depth k<=dL -> gain k<=gL ->
  Forall (fun z=>continuing z /\ index z<=m /\ depth z<=dm /\ gain z<=gm) lows ->
  trace lows S U -> WordLink.bound m r ->
  HighPath.certified m (dL+r*dm) (gL+r*gm) (r*gm) (summary (k::lows)).
Proof.
  intros Hm Hr Hdm Hgm Hhigh Hk Hdk Hgk Hlow Htrace Hbound.
  assert (Hall : Forall continuing (k::lows)).
  { constructor; [exact Hk|]. eapply Forall_impl; [|exact Hlow]. firstorder. }
  assert (Hlen : Z.of_nat (length lows)<=r).
  { apply (Hbound lows S U); [|exact Htrace]. eapply Forall_impl; [|exact Hlow]. firstorder. }
  assert (HD : 0<=total depth lows<=r*dm).
  { assert (H : Forall (fun z=>0<=depth z<=dm) lows).
    { eapply Forall_impl; [|exact Hlow]. intros z [[e [Hb Hrest]] [Hindex [Hd Hg]]].
      pose proof (Table.built_valid _ _ Hb) as [[_ [_ [[Hx _] _]]] _]. unfold Table.sane in Hx.
      unfold depth. split; [lia|exact Hd]. }
    pose proof (total_bound _ _ _ H). nia. }
  assert (HG : 0<=total gain lows<=r*gm).
  { assert (H : Forall (fun z=>0<=gain z<=gm) lows).
    { eapply Forall_impl; [|exact Hlow]. intros z [Hz [Hindex [Hd Hg]]].
      pose proof (WordLink.continuing_good _ Hz) as Hgood.
      change (0<2^Table.d (pair z) /\ 0<Table.p (pair z) /\
        2*Table.p (pair z)<=2^Table.d (pair z) /\ 1<=Table.b (pair z) /\
        Table.b (pair z)+2<=gain z) in Hgood. lia. }
    pose proof (total_bound _ _ _ H). nia. }
  destruct (summary_data _ Hall ltac:(discriminate)) as [Hd0 [HQ [Hz [HA [HC HM]]]]].
  assert (HMbound : m<Block.added (summary (k::lows))<=gL+r*gm).
  { rewrite HM. change (m<gain k+total gain lows<=gL+r*gm).
    pose proof (WordLink.continuing_gain _ Hk). lia. }
  assert (HDfull : total depth (k::lows)<=dL+r*dm) by (change (depth k+total depth lows<=dL+r*dm); lia).
  assert (Hcontract : 2*Block.offset (summary (k::lows))<=
    Block.sc (summary (k::lows))*(3*Block.added (summary (k::lows))+2*(r*gm)+6)).
  { pose proof (Block.word_contraction (Bridge.kernel (pair k)) (kernels lows)
      (WordLink.continuing_good _ Hk)) as Hc.
    assert (Hgood : Forall Block.good (kernels lows)).
    { apply Forall_map. eapply Forall_impl; [|exact Hlow]. intros z [Hz0 Hrest]. apply WordLink.continuing_good,Hz0. }
    specialize (Hc Hgood). cbv zeta in Hc. rewrite low_fold_added in Hc.
    change (2*Block.offset (summary (k::lows))<=Block.sc (summary (k::lows))*
      (3*Block.added (summary (k::lows))+2*(0+total gain lows)+6)) in Hc.
    destruct Hz as [HQpos [HAs [HMpos HCs]]]. nia. }
  exists (total depth (k::lows)). split; [lia|]. split; [exact HQ|].
  destruct Hz as [HQpos [HAs [HMpos HCs]]]. split; [lia|]. split; [nia|]. split; assumption.
Qed.

End WordBlocks.

Module Multiscale.
Import WordLibrary WordBlocks.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition parameters L d g := forall k,continuing k -> index k<=L -> depth k<=d /\ gain k<=g.

Lemma low_split m word : exists lows tail,word=lows++tail /\
  Forall (fun k=>index k<=m) lows /\
  (tail=[] \/ exists k rest,tail=k::rest /\ m<index k).
Proof.
  induction word as [|k word IH].
  - exists ([]:list kernel),([]:list kernel). split; [reflexivity|]. split; [constructor|left; reflexivity].
  - destruct (Z_le_gt_dec (index k) m) as [Hlow|Hhigh].
    + destruct IH as [lows [tail [Heq [Hall Htail]]]].
      exists (k::lows),tail. split; [cbn; congruence|]. split; [constructor; assumption|exact Htail].
    + exists ([]:list kernel),(k::word). split; [reflexivity|]. split; [constructor|].
      right. exists k,word. split; [reflexivity|lia].
Qed.

Lemma low_parameters m L dm gm lows : parameters m dm gm ->
  Forall (fun k=>continuing k /\ index k<=L) lows -> Forall (fun k=>index k<=m) lows ->
  Forall (fun k=>continuing k /\ index k<=m /\ depth k<=dm /\ gain k<=gm) lows.
Proof.
  intros Hparams Hall Hlow. rewrite Forall_forall in *.
  intros k Hin. destruct (Hall k Hin) as [Hk HL]. specialize (Hlow k Hin).
  destruct (Hparams k Hk Hlow) as [Hd Hg]. auto.
Qed.

Lemma low_length m L r lows S U : WordLink.bound m r ->
  Forall (fun k=>continuing k /\ index k<=L) lows -> Forall (fun k=>index k<=m) lows ->
  trace lows S U -> Z.of_nat (length lows)<=r.
Proof.
  intros Hb Hall Hlow Htrace. apply (Hb lows S U); [|exact Htrace].
  rewrite Forall_forall in *. intros k Hin. destruct (Hall k Hin). split; auto.
Qed.

Lemma high_decompose m L r dL dm gL gm : 0<=m -> 0<=r -> 0<=dm -> 0<=gm ->
  parameters L dL gL -> parameters m dm gm -> WordLink.bound m r ->
  forall fuel k rest S U,(length (k::rest)<=fuel)%nat -> m<index k ->
  Forall (fun z=>continuing z /\ index z<=L) (k::rest) -> trace (k::rest) S U ->
  exists zs,HighPath.path m (dL+r*dm) (gL+r*gm) (r*gm) zs S (2*S-U+3) /\
    Z.of_nat (length (k::rest))<=(r+1)*(Z.of_nat (length zs)+1).
Proof.
  intros Hm Hr Hdm Hgm Hglobal Hlow Hbound fuel.
  induction fuel as [|fuel IH]; intros k rest Sa Ua Hfuel Hhigh Hall Htrace; [cbn in Hfuel; lia|].
  destruct (low_split m rest) as [lows [tail [Hsplit [Hindices Htail]]]]. subst rest.
  inversion Hall as [|k0 rest0 Hk Hrest]; subst. apply Forall_app in Hrest. destruct Hrest as [Hlows Htailall].
  inversion Htrace as [|k0 rest0 S0 U0 S1 U1 Hfirst Hafter]; subst.
  pose proof (trace_prefix lows tail S1 U1 Hafter) as Hlowtrace.
  pose proof (low_length m L r lows S1 U1 Hbound Hlows Hindices Hlowtrace) as Hlen.
  pose proof (high_div m k (lows++tail) Sa Ua Hm Hhigh Htrace) as Hdiv.
  destruct Htail as [-> | [k' [rest' [-> Hhigh']]]].
  - exists ([]:list Block.summary). split; [constructor; exact Hdiv|].
    rewrite app_nil_r. cbn [length]. rewrite Nat2Z.inj_succ. change (Z.of_nat 0) with 0. nia.
  - destruct (trace_split (k::lows) (k'::rest') Sa Ua Htrace) as [Sb [Ub [Hcalls Hresttrace]]].
    destruct (IH k' rest' Sb Ub) as [zs [Hpath Hcount]].
    + cbn [length] in Hfuel. rewrite length_app in Hfuel. cbn [length] in *. lia.
    + exact Hhigh'.
    + exact Htailall.
    + exact Hresttrace.
    + exists (summary (k::lows)::zs). split.
      * pose proof (summary_sound _ _ _ _ _ Hcalls) as Hsummary.
        destruct Hsummary as [HS HH]. subst Sb.
        eapply HighPath.path_step; [exact Hdiv| |split; [reflexivity|exact HH]|exact Hpath].
        destruct Hk as [Hk HK]. destruct (Hglobal k Hk HK) as [Hd Hg].
        apply (certified_block m r dL dm gL gm k lows S1 U1 Hm Hr Hdm Hgm Hhigh Hk Hd Hg
          (low_parameters m L dm gm lows Hlow Hlows Hindices) Hlowtrace Hbound).
      * cbn [length]. rewrite length_app,!Nat2Z.inj_succ,Nat2Z.inj_add.
        change (Z.of_nat (S (length rest'))<=(r+1)*(Z.of_nat (length zs)+1)) in Hcount.
        rewrite Nat2Z.inj_succ in Hcount. cbn [length]. rewrite Nat2Z.inj_succ. nia.
Qed.

Theorem lift_bound m L r dL dm gL gm t q :
  0<m -> 0<=r -> 0<=dm -> 0<=gm -> 0<=gL ->
  parameters L dL gL -> parameters m dm gm -> WordLink.bound m r ->
  2^(2*(dL+r*dm))*(12*(gL+r*gm)+8)<2^(m+1) ->
  2*(gL+r*gm)+2<=3^Z.of_nat t -> r*gm+4<=Z.of_nat q*m ->
  WordLink.bound L ((r+1)*(Z.of_nat t+Z.of_nat q+2)+r).
Proof.
  intros Hm Hr Hdm Hgm HgL Hglobal Hlow Hbound Hbudget Hpow Hq word S U Hall Htrace.
  destruct (low_split m word) as [lows [tail [-> [Hindices Htail]]]].
  apply Forall_app in Hall. destruct Hall as [Hlows Htailall].
  pose proof (trace_prefix lows tail S U Htrace) as Hlowtrace.
  pose proof (low_length m L r lows S U Hbound Hlows Hindices Hlowtrace) as Hlen.
  destruct Htail as [-> | [k [rest [-> Hhigh]]]].
  - rewrite app_nil_r. pose proof (Nat2Z.is_nonneg t). pose proof (Nat2Z.is_nonneg q). nia.
  - destruct (WordLink.trace_suffix lows (k::rest) S U Htrace) as [S' [U' Hsuffix]].
    destruct (high_decompose m L r dL dm gL gm ltac:(lia) Hr Hdm Hgm Hglobal Hlow Hbound
      (length (k::rest)) k rest S' U' ltac:(lia) Hhigh Htailall Hsuffix) as [zs [Hpath Hcount]].
    pose proof (HighPath.path_count m (dL+r*dm) (gL+r*gm) (r*gm) zs S' (2*S'-U'+3)
      t q Hm ltac:(nia) ltac:(nia) Hpow Hq Hbudget Hpath) as Hhighcount.
    rewrite length_app,Nat2Z.inj_add. apply Nat2Z.inj_lt in Hhighcount.
    rewrite !Nat2Z.inj_add in Hhighcount. change (Z.of_nat 1) with 1 in Hhighcount. nia.
Qed.

End Multiscale.

Module SmallScale.
Import WordLibrary WordBlocks Multiscale.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma base_parameters : parameters 2048 5 5472.
Proof. intros k Hk HL. exact (WordCheck.kernel_bounds k Hk HL). Qed.

Lemma earlier_parameters k L : 1<=L<k -> Closure.earlier k ->
  parameters L (6*Z.log2_up L+9) (12*L^3+3).
Proof.
  intros HL Hprevious z Hcontinuing Hindex.
  destruct Hcontinuing as [e [Hb [Hs He]]].
  exact (Closure.kernel_bounds k L HL Hprevious (index z) (pair z) e ltac:(lia) Hb).
Qed.

Lemma exp3 x : 0<=x -> 2^(3*x)=(2^x)^3.
Proof.
  intro Hx. replace (3*x) with (x*3) by lia. rewrite Z.pow_mul_r by lia. reflexivity.
Qed.

Lemma mass_bound L x : 2048<L -> 12<=x -> L<=2^x ->
  12*L^3+3+6*5472<=13*2^(3*x).
Proof.
  intros HL Hx Hpow. pose proof (Z.pow_le_mono_l L (2^x) 3 ltac:(lia)).
  assert (Hsmall : 65536<=2^(3*x)).
  { change (2^16<=2^(3*x)). apply Z.pow_le_mono_r; lia. }
  rewrite exp3 in * by lia. lia.
Qed.

Lemma budget120 x M : 12<=x<=120 -> 0<=M<=13*2^(3*x) ->
  2^(2*(6*x+39))*(12*M+8)<2^2049.
Proof.
  intros Hx HM. pose proof (Table.pow_pos (3*x) ltac:(lia)) as HP.
  assert (HB : 12*M+8<2^(3*x+8)).
  { rewrite Z.pow_add_r by lia. change (2^8) with 256. nia. }
  assert (Hbig : 2^(2*(6*x+39))*(12*M+8)<2^(15*x+86)).
  { replace (15*x+86) with (2*(6*x+39)+(3*x+8)) by lia.
    rewrite Z.pow_add_r by lia. apply Z.mul_lt_mono_pos_l; [apply Table.pow_pos; lia|exact HB]. }
  eapply Z.lt_trans; [exact Hbig|]. apply Z.pow_lt_mono_r; lia.
Qed.

Lemma contraction_time x M : 0<=x -> 0<=M<=13*2^(3*x) -> 2*M+2<=3^(2*x+4).
Proof.
  intros Hx HM. pose proof (Z.pow_le_mono_l 8 9 x ltac:(lia)) as H89.
  rewrite Z.pow_add_r,Z.pow_mul_r by lia. change (3^2) with 9. change (3^4) with 81.
  rewrite Z.pow_mul_r in HM by lia. change (2^3) with 8 in HM.
  pose proof (Z.pow_pos_nonneg 8 x ltac:(lia) Hx). nia.
Qed.

Theorem range120 L : 2<=L<=2^120 ->
  parameters L (6*Z.log2_up L+9) (12*L^3+3) -> WordLink.bound L (30*Z.log2_up L).
Proof.
  intros HL Hparams. destruct (Z_le_gt_dec L 2048) as [Hsmall|Hlarge].
  - apply (WordLink.bound_mono 2048 L 6 (30*Z.log2_up L)); try assumption; [|exact WordLink.base_bound].
    pose proof (Z.log2_up_le_mono 2 L ltac:(lia)). change (1<=Z.log2_up L) in H. lia.
  - set (x:=Z.log2_up L).
    assert (Hx : 12<=x<=120).
    { split.
      - pose proof (Z.log2_up_le_mono 2049 L ltac:(lia)). change (12<=Z.log2_up L) in H. exact H.
      - apply (proj1 (Z.log2_up_le_pow2 L 120 ltac:(lia))). exact (proj2 HL). }
    assert (HLpow : L<=2^x) by (exact (proj2 (Z.log2_up_spec L ltac:(lia)))).
    assert (HM : 0<=12*L^3+3+6*5472<=13*2^(3*x)).
    { split; [pose proof (Z.pow_nonneg L 3 ltac:(lia)); lia|apply mass_bound; lia]. }
    pose proof (lift_bound 2048 L 6 (6*x+9) 5 (12*L^3+3) 5472
      (Z.to_nat (2*x+4)) 17 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(pose proof (Z.pow_nonneg L 3 ltac:(lia)); lia)
      Hparams base_parameters WordLink.base_bound) as Hlift.
    assert (Hbudget : 2^(2*(6*x+9+6*5))*(12*(12*L^3+3+6*5472)+8)<2^(2048+1)).
    { replace (6*x+9+6*5) with (6*x+39) by lia. apply budget120; assumption. }
    assert (Htime : 2*(12*L^3+3+6*5472)+2<=3^Z.of_nat (Z.to_nat (2*x+4))).
    { rewrite Z2Nat.id by lia. apply contraction_time; lia || assumption. }
    specialize (Hlift Hbudget Htime ltac:(change (32836<=17*2048); lia)).
    apply (WordLink.bound_mono L L ((6+1)*(Z.of_nat (Z.to_nat (2*x+4))+Z.of_nat 17+2)+6) (30*x));
      [lia| |exact Hlift]. rewrite Z2Nat.id by lia. change (Z.of_nat 17) with 17. lia.
Qed.

End SmallScale.

Module Exponential.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

(* A ratio estimate at a single integer base controls every larger
   argument, without expanding a high-degree polynomial in nia. *)
Lemma power_ratio a b p c : 0<b<=a -> 0<=p -> 0<=c -> (b+1)^p<=c*b^p ->
  (a+1)^p<=c*a^p.
Proof.
  intros Hab Hp Hc Hbase.
  pose proof (Z.pow_le_mono_l (b*(a+1)) ((b+1)*a) p ltac:(nia)) as H.
  rewrite !Z.pow_mul_l in H.
  pose proof (Z.pow_nonneg a p ltac:(lia)).
  pose proof (Z.pow_pos_nonneg b p ltac:(lia) Hp).
  pose proof (Z.mul_le_mono_nonneg_r _ _ (a^p) ltac:(lia) Hbase). nia.
Qed.

Lemma shifted_power K c p start slope : 0<=K -> 0<=start -> 0<start+c -> 0<=p -> 0<=slope ->
  (start+c+1)^p<=2^slope*(start+c)^p -> K*(start+c)^p<2^(slope*start) ->
  forall n,start<=n -> K*(n+c)^p<2^(slope*n).
Proof.
  intros HK Hstart0 Hstart Hp Hs Hratio Hbase.
  assert (H : forall i,K*(start+Z.of_nat i+c)^p<2^(slope*(start+Z.of_nat i))).
  { induction i as [|i IH].
    - rewrite Z.add_0_r. exact Hbase.
    - rewrite Nat2Z.inj_succ.
      replace (start+Z.succ (Z.of_nat i)+c) with ((start+Z.of_nat i+c)+1) by lia.
      replace (slope*(start+Z.succ (Z.of_nat i))) with (slope*(start+Z.of_nat i)+slope) by ring.
      rewrite Z.pow_add_r by nia.
      pose proof (power_ratio (start+Z.of_nat i+c) (start+c) p (2^slope)
        ltac:(lia) Hp ltac:(pose proof (Table.pow_pos slope Hs); lia) Hratio) as Hstep.
      pose proof (Table.pow_pos slope Hs) as Hpositive.
      pose proof (Z.mul_le_mono_nonneg_l _ _ K HK Hstep) as Hscaled.
      assert (Hstrict : 2^slope*(K*(start+Z.of_nat i+c)^p)<2^slope*2^(slope*(start+Z.of_nat i)))
        by (apply Z.mul_lt_mono_pos_l; assumption). nia. }
  intros n Hn. replace n with (start+Z.of_nat (Z.to_nat (n-start))) by lia. apply H.
Qed.

Lemma square_tail n : 20<=n -> 1024*(n+8)^2<2^n.
Proof.
  intro Hn. replace n with (1*n) at 2 by ring.
  apply (shifted_power 1024 8 2 20 1); try lia; vm_compute; discriminate.
Qed.

Lemma fifth_tail n : 114<=n -> 2^70*(n+8)^5<2^n.
Proof.
  intro Hn. replace n with (1*n) at 2 by ring.
  apply (shifted_power (2^70) 8 5 114 1); try lia; vm_compute; discriminate.
Qed.

Lemma eighth_tail n : 114<=n -> 2^84*(n+8)^8<2^(2*n).
Proof. intro Hn. apply (shifted_power (2^84) 8 8 114 2); try lia; vm_compute; discriminate. Qed.

Lemma final_tail n : 1024<=n -> 2^70*(n+1)^5<2^(n-1).
Proof.
  intro Hn. pose proof (shifted_power (2^71) 1 5 1024 1
    ltac:(vm_compute; discriminate) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) n Hn) as H.
  rewrite Z.mul_1_l,(Table.pow_split n 1) in H by lia.
  change (2^1) with 2 in H.
  replace (2^71) with (2*2^70) in H by reflexivity. nia.
Qed.

Lemma final_square n : 17<=n -> 200*n^2<2^(n-1).
Proof.
  intro Hn. pose proof (shifted_power 400 0 2 17 1
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) n Hn) as H.
  rewrite Z.add_0_r,Z.mul_1_l,(Table.pow_split n 1) in H by lia.
  change (2^1) with 2 in H. nia.
Qed.

End Exponential.

Module LargeStep.
Import WordLibrary WordBlocks Multiscale.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma mass_bound L m x r : 3<=x -> 2<=m<=L -> L<=2^x -> 0<=r ->
  0<=12*L^3+3+r*(12*m^3+3)<=13*(r+1)*2^(3*x).
Proof.
  intros Hx Hm HL Hr.
  pose proof (Z.pow_le_mono_l m L 3 ltac:(lia)) as HmL.
  pose proof (Z.pow_le_mono_l L (2^x) 3 ltac:(lia)) as HLP.
  pose proof (Z.pow_nonneg m 3 ltac:(lia)).
  assert (HP : 8<=2^(3*x)).
  { change (2^3<=2^(3*x)). apply Z.pow_le_mono_r; lia. }
  rewrite SmallScale.exp3 in * by lia. nia.
Qed.

Lemma budget m x y r M : 3<=x -> 0<=y -> 1<=r ->
  0<=M<=13*(r+1)*2^(3*x) ->
  15*x+27+2*r*(6*y+9)+r<=m+1 ->
  2^(2*(6*x+9+r*(6*y+9)))*(12*M+8)<2^(m+1).
Proof.
  intros Hx Hy Hr HM Hbudget.
  pose proof (Z.pow_gt_lin_r 2 (r+1) ltac:(lia) ltac:(lia)) as Hrpow.
  pose proof (Table.pow_pos (3*x) ltac:(lia)) as HP.
  assert (HE : 2^(3*x+8+(r+1))=256*2^(3*x)*2^(r+1)).
  { rewrite !Z.pow_add_r by lia. change (2^8) with 256. ring. }
  assert (HMpow : 12*M+8<2^(3*x+8+(r+1))) by (rewrite HE; nia).
  assert (Hstep : 2^(2*(6*x+9+r*(6*y+9)))*(12*M+8)<2^(15*x+27+2*r*(6*y+9)+r)).
  { replace (15*x+27+2*r*(6*y+9)+r) with (2*(6*x+9+r*(6*y+9))+(3*x+8+(r+1))) by ring.
    rewrite Z.pow_add_r by nia. apply Z.mul_lt_mono_pos_l; [apply Table.pow_pos; nia|exact HMpow]. }
  eapply Z.lt_le_trans; [exact Hstep|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma contraction_time x r M : 3<=x -> 1<=r -> r+1<=2^x ->
  0<=M<=13*(r+1)*2^(3*x) -> 2*M+2<=3^(4*x).
Proof.
  intros Hx Hr Hrpow HM.
  assert (HE : 2^(4*x)=2^x*2^(3*x)).
  { rewrite <-Z.pow_add_r by lia. f_equal. ring. }
  assert (HMpow : 2*M+2<=28*2^(4*x)).
  { rewrite HE. pose proof (Table.pow_pos x ltac:(lia)). pose proof (Table.pow_pos (3*x) ltac:(lia)). nia. }
  assert (Hdominates : 28*2^(4*x)<=3^(4*x)).
  { rewrite !Z.pow_mul_r by lia. change (2^4) with 16. change (3^4) with 81.
    pose proof (Z.pow_le_mono_l 64 81 x ltac:(lia)) as H64.
    change 64 with (4*16) in H64. rewrite Z.pow_mul_l in H64.
    assert (H4 : 64<=4^x) by (change (4^3<=4^x); apply Z.pow_le_mono_r; lia).
    pose proof (Z.pow_pos_nonneg 16 x ltac:(lia) ltac:(lia)). nia. }
  lia.
Qed.

Lemma length_estimate r x m : 1<=r -> 2<=m -> x<=m^2 ->
  (r+1)*(4*x+13*r*m^2+2)+r<=64*(r+1)^2*m^2.
Proof.
  intros Hr Hm Hx.
  pose proof (Z.mul_le_mono_nonneg_l (4*x+13*r*m^2+2) (4*m^2+13*r*m^2+2)
    (r+1) ltac:(lia) ltac:(lia)). nia.
Qed.

Theorem lift m L x y r : 3<=x -> 0<=y -> 2<=m<=L -> 1<=r -> L<=2^x -> x<=m^2 ->
  parameters L (6*x+9) (12*L^3+3) -> parameters m (6*y+9) (12*m^3+3) ->
  WordLink.bound m r -> 15*x+27+2*r*(6*y+9)+r<=m+1 ->
  WordLink.bound L (64*(r+1)^2*m^2).
Proof.
  intros Hx Hy Hm Hr HL Hsquare Hparams Hlow Hbound Hbudget.
  pose proof (mass_bound L m x r Hx Hm HL ltac:(lia)) as HM.
  pose proof (budget m x y r (12*L^3+3+r*(12*m^3+3)) Hx Hy Hr HM Hbudget) as Hexp.
  assert (Hrpow : r+1<=2^x).
  { assert (Hnonneg : 0<=2*r*(6*y+9)) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  pose proof (contraction_time x r (12*L^3+3+r*(12*m^3+3)) Hx Hr Hrpow HM) as Htime.
  assert (Hq : r*(12*m^3+3)+4<=(13*r*m^2)*m) by nia.
  pose proof (lift_bound m L r (6*x+9) (6*y+9) (12*L^3+3) (12*m^3+3)
    (Z.to_nat (4*x)) (Z.to_nat (13*r*m^2)) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(pose proof (Z.pow_nonneg m 3 ltac:(lia)); lia)
    ltac:(pose proof (Z.pow_nonneg L 3 ltac:(lia)); lia)
    Hparams Hlow Hbound Hexp) as Hlift.
  assert (Hq0 : 0<=13*r*m^2) by (apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia]).
  rewrite !Z2Nat.id in Hlift by lia. specialize (Hlift Htime Hq).
  eapply WordLink.bound_mono; [apply Z.le_refl| |exact Hlift]. apply length_estimate; lia.
Qed.

End LargeStep.

Module ScaleNumbers.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma threshold x : 121<=x -> 2^20+32*x<2^(x-1).
Proof. intro Hx. pose proof (Exponential.final_square x ltac:(lia)). nia. Qed.

Lemma subscale x : 121<=x ->
  20<=Z.log2_up (2^20+32*x)<=x /\ 2^20+32*x<=2^14*x /\ x<=(2^20+32*x)^2.
Proof.
  intro Hx. pose proof (threshold x Hx) as Ht.
  split; [split|].
  - pose proof (Z.log2_up_le_mono (2^20) (2^20+32*x) ltac:(lia)) as H.
    rewrite Z.log2_up_pow2 in H by lia. exact H.
  - apply (proj1 (Z.log2_up_le_pow2 (2^20+32*x) x ltac:(lia))).
    pose proof (Z.pow_le_mono_r 2 (x-1) x ltac:(lia) ltac:(lia)). lia.
  - split; [change (1048576+32*x<=16384*x); lia|nia].
Qed.

Lemma small_window x : 121<=x<=2^20 -> Z.log2_up (2^20+32*x)<=26.
Proof.
  intro Hx. apply (proj1 (Z.log2_up_le_pow2 (2^20+32*x) 26 ltac:(lia))).
  change (1048576+32*x<=67108864). change (121<=x<=1048576) in Hx. lia.
Qed.

Lemma large_window x : 2^20<x ->
  20<=Z.log2 x /\ 2^Z.log2 x<=x<2^(Z.log2 x+1) /\
  Z.log2_up (2^20+32*x)<=Z.log2 x+7 /\ 2^20+32*x<=64*x.
Proof.
  intro Hx. pose proof (Z.log2_spec x ltac:(lia)) as Hpow.
  change (2^Z.log2 x<=x<2^(Z.log2 x+1)) in Hpow.
  assert (Hn : 20<=Z.log2 x).
  { pose proof (Z.log2_le_mono (2^20) x ltac:(lia)) as H.
    rewrite Z.log2_pow2 in H by lia. exact H. }
  split; [exact Hn|]. split; [exact Hpow|]. split; [|lia].
  apply (proj1 (Z.log2_up_le_pow2 (2^20+32*x) (Z.log2 x+7) ltac:(lia))).
  rewrite (Table.pow_split (Z.log2 x+7) 6) by lia. change (2^6) with 64.
  replace (Z.log2 x+7-6) with (Z.log2 x+1) by lia. lia.
Qed.

Lemma huge_window x : 2^120<2^20+32*x -> 2^114<x /\ 114<=Z.log2 x.
Proof.
  intro Hm. assert (Hfixed : 2^20+32*2^114<2^120) by (vm_compute; reflexivity).
  assert (Hx : 2^114<x) by lia. split; [exact Hx|].
  pose proof (Z.log2_le_mono (2^114) x ltac:(lia)) as H.
  rewrite Z.log2_pow2 in H by lia. exact H.
Qed.

Lemma small_budget_poly y n : 0<=y<=n+7 -> 0<=n ->
  27+2*(30*y)*(6*y+9)+30*y<=1024*(n+8)^2.
Proof. intros. nia. Qed.

Lemma small_budget x : 121<=x -> let y:=Z.log2_up (2^20+32*x) in
  15*x+27+2*(30*y)*(6*y+9)+30*y<=2^20+32*x+1.
Proof.
  intro Hx. pose proof (subscale x Hx) as [Hy Hrest]. cbv zeta.
  destruct (Z_le_gt_dec x (2^20)) as [Hsmall|Hlarge].
  - pose proof (small_window x ltac:(lia)).
    pose proof (small_budget_poly (Z.log2_up (2^20+32*x)) 19 ltac:(lia) ltac:(lia)). lia.
  - destruct (large_window x ltac:(lia)) as [Hn [Hpow [Hyn Hm]]].
    pose proof (small_budget_poly (Z.log2_up (2^20+32*x)) (Z.log2 x) ltac:(lia) ltac:(lia)) as Hpoly.
    pose proof (Exponential.square_tail (Z.log2 x) Hn). lia.
Qed.

Lemma large_budget_poly y : 0<=y ->
  27+2*(2^64*(y+1)^4)*(6*y+9)+2^64*(y+1)^4<=2^70*(y+1)^5.
Proof.
  intro Hy. pose proof (Z.pow_le_mono_l 1 (y+1) 4 ltac:(lia)) as HP.
  change (1<=(y+1)^4) in HP.
  replace ((y+1)^5) with ((y+1)^4*(y+1)) by ring.
  generalize ((y+1)^4) HP. intros z Hz. nia.
Qed.

Lemma large_budget x : 121<=x -> 2^120<2^20+32*x -> let y:=Z.log2_up (2^20+32*x) in
  15*x+27+2*(2^64*(y+1)^4)*(6*y+9)+2^64*(y+1)^4<=2^20+32*x+1.
Proof.
  intros Hx Hm. cbv zeta. destruct (huge_window x Hm) as [Hxlarge Hn].
  assert (H20 : 2^20<x).
  { pose proof (Z.pow_le_mono_r 2 20 114 ltac:(lia) ltac:(lia)). lia. }
  destruct (large_window x H20) as [Hn0 [Hpow [Hy Hm64]]].
  pose proof (Z.log2_up_nonneg (2^20+32*x)) as Hy0.
  pose proof (large_budget_poly (Z.log2_up (2^20+32*x)) Hy0) as Hpoly.
  pose proof (Z.pow_le_mono_l (Z.log2_up (2^20+32*x)+1) (Z.log2 x+8) 5 ltac:(lia)) as Hmono.
  pose proof (Exponential.fifth_tail (Z.log2 x) Hn) as Htail. lia.
Qed.

Lemma product_squares a A b B : 0<=a<=A -> 0<=b<=B -> 64*a^2*b^2<=64*A^2*B^2.
Proof.
  intros Ha Hb. pose proof (Z.pow_le_mono_l a A 2 Ha).
  pose proof (Z.pow_le_mono_l b B 2 Hb).
  pose proof (Z.pow_nonneg a 2 ltac:(lia)). pose proof (Z.pow_nonneg b 2 ltac:(lia)).
  pose proof (Z.mul_le_mono_nonneg (a^2) (A^2) (b^2) (B^2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma small_output x y m : 121<=x -> 0<=y<=x -> 0<=m<=2^14*x ->
  64*(30*y+1)^2*m^2<=2^64*(x+1)^4.
Proof.
  intros Hx Hy Hm.
  pose proof (product_squares (30*y+1) (32*x) m (2^14*x) ltac:(lia) Hm) as H.
  replace (64*(32*x)^2*(2^14*x)^2) with (2^44*x^4) in H by ring.
  pose proof (Z.pow_le_mono_l x (x+1) 4 ltac:(lia)).
  pose proof (Z.pow_nonneg x 4 ltac:(lia)). lia.
Qed.

Lemma large_output x y m n : 1<=x -> 0<=y<=n+7 -> 114<=n -> 2^n<=x -> 0<=m<=64*x ->
  64*(2^64*(y+1)^4+1)^2*m^2<=2^64*(x+1)^4.
Proof.
  intros Hx Hy Hn Hnx Hm.
  pose proof (Z.pow_le_mono_l 1 (y+1) 4 ltac:(lia)) as HP.
  change (1<=(y+1)^4) in HP.
  pose proof (product_squares (2^64*(y+1)^4+1) (2^65*(y+1)^4) m (64*x) ltac:(lia) Hm) as H.
  replace (64*(2^65*(y+1)^4)^2*(64*x)^2) with (2^148*(y+1)^8*x^2) in H by ring.
  pose proof (Z.pow_le_mono_l (y+1) (n+8) 8 ltac:(lia)) as Hy8.
  pose proof (Exponential.eighth_tail n Hn) as Htail.
  assert (Hn2 : 2^(2*n)<=x^2).
  { replace (2*n) with (n*2) by ring. rewrite Z.pow_mul_r by lia.
    apply Z.pow_le_mono_l. pose proof (Table.pow_pos n ltac:(lia)). lia. }
  assert (H8 : 2^84*(y+1)^8<=x^2) by lia.
  assert (Hstep : 2^148*(y+1)^8*x^2<=2^64*x^4).
  { replace (2^148*(y+1)^8*x^2) with ((2^64*(2^84*(y+1)^8))*x^2) by ring.
    replace (2^64*x^4) with ((2^64*x^2)*x^2) by ring.
    apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia|].
    apply Z.mul_le_mono_nonneg_l; [vm_compute; discriminate|exact H8]. }
  pose proof (Z.pow_le_mono_l x (x+1) 4 ltac:(lia)). lia.
Qed.

End ScaleNumbers.

Module GlobalBounds.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma linear_quartic x : 0<=x -> 30*x<=2^64*(x+1)^4.
Proof.
  intro Hx. assert (Hpow : x+1<=(x+1)^4).
  { replace (x+1) with ((x+1)^1) at 1 by ring. apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma induction_step k L : Closure.earlier k -> 2<=L<k ->
  (forall m,2<=m<L -> WordLink.bound m (2^64*(Z.log2_up m+1)^4)) ->
  WordLink.bound L (2^64*(Z.log2_up L+1)^4).
Proof.
  intros Hprevious HL IH.
  pose proof (SmallScale.earlier_parameters k L ltac:(lia) Hprevious) as Hparams.
  destruct (Z_le_gt_dec L (2^120)) as [Hsmall|Hlarge].
  - eapply WordLink.bound_mono; [reflexivity|apply linear_quartic,Z.log2_up_nonneg|].
    apply SmallScale.range120; [lia|exact Hparams].
  - set (x:=Z.log2_up L).
    assert (Hx : 121<=x).
    { destruct (Z_le_gt_dec x 120) as [Hle|Hgt]; [|lia].
      pose proof (proj2 (Z.log2_up_le_pow2 L 120 ltac:(lia)) Hle). lia. }
    pose proof (Z.log2_up_spec L ltac:(lia)) as Hpow.
    change (2^(x-1)<L<=2^x) in Hpow.
    set (m:=2^20+32*x). set (y:=Z.log2_up m).
    assert (Hm : 2<=m<L) by (pose proof (ScaleNumbers.threshold x Hx); unfold m; lia).
    pose proof (ScaleNumbers.subscale x Hx) as [Hy [Hm14 Hxm]].
    change (20<=y<=x) in Hy.
    change (m<=2^14*x) in Hm14. change (x<=m^2) in Hxm.
    pose proof (SmallScale.earlier_parameters k m ltac:(lia) Hprevious) as Hmparams.
    destruct (Z_le_gt_dec m (2^120)) as [Hmsmall|Hmlarge].
    + pose proof (SmallScale.range120 m ltac:(lia) Hmparams) as Hword.
      pose proof (LargeStep.lift m L x y (30*y) ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) (proj2 Hpow) Hxm Hparams Hmparams Hword
        (ScaleNumbers.small_budget x Hx)) as Hlift.
      eapply WordLink.bound_mono; [reflexivity| |exact Hlift].
      apply ScaleNumbers.small_output; lia.
    + pose proof (IH m Hm) as Hword.
      assert (Hr : 1<=2^64*(y+1)^4).
      { pose proof (Z.pow_le_mono_l 1 (y+1) 4 ltac:(lia)). change (1<=(y+1)^4) in H. lia. }
      pose proof (LargeStep.lift m L x y (2^64*(y+1)^4) ltac:(lia) ltac:(lia) ltac:(lia)
        Hr (proj2 Hpow) Hxm Hparams Hmparams Hword
        (ScaleNumbers.large_budget x Hx ltac:(unfold m in Hmlarge; lia))) as Hlift.
      destruct (ScaleNumbers.huge_window x ltac:(unfold m in Hmlarge; lia)) as [Hx114 Hn].
      assert (Hx20 : 2^20<x).
      { pose proof (Z.pow_le_mono_r 2 20 114 ltac:(lia) ltac:(lia)). lia. }
      destruct (ScaleNumbers.large_window x Hx20) as [Hn0 [Hnx [Hyn Hm64]]].
      change (y<=Z.log2 x+7) in Hyn. change (m<=64*x) in Hm64.
      eapply WordLink.bound_mono; [reflexivity| |exact Hlift].
      apply (ScaleNumbers.large_output x y m (Z.log2 x)); lia.
Qed.

Theorem quartic k : Closure.earlier k -> forall L,2<=L<k ->
  WordLink.bound L (2^64*(Z.log2_up L+1)^4).
Proof.
  intro Hprevious.
  assert (Hnat : forall n,2<=Z.of_nat n<k ->
    WordLink.bound (Z.of_nat n) (2^64*(Z.log2_up (Z.of_nat n)+1)^4)).
  { intro n. induction n using lt_wf_ind. intro Hn.
    apply (induction_step k (Z.of_nat n) Hprevious Hn).
    intros m Hm. replace m with (Z.of_nat (Z.to_nat m)) by lia. apply H; lia. }
  intros L HL. replace L with (Z.of_nat (Z.to_nat L)) by lia. apply Hnat. lia.
Qed.

End GlobalBounds.

Module FinalBudget.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma cutoff k : 65536<k -> let x:=Z.log2_up k in
  17<=x /\ 2^(x-1)<k<=2^x /\ 2<=8*x<k /\ 0<=Z.log2_up (8*x)<=x.
Proof.
  intro Hk. cbv zeta. set (x:=Z.log2_up k).
  assert (Hx : 17<=x).
  { pose proof (Z.log2_up_le_mono 65537 k ltac:(lia)).
    change (17<=Z.log2_up k) in H. exact H. }
  pose proof (Z.log2_up_spec k ltac:(lia)) as Hpow.
  change (2^(x-1)<k<=2^x) in Hpow.
  pose proof (Exponential.final_square x Hx) as Hsquare.
  assert (HL : 2<=8*x<k) by nia.
  split; [exact Hx|]. split; [exact Hpow|]. split; [exact HL|].
  split; [apply Z.log2_up_nonneg|].
  apply (proj1 (Z.log2_up_le_pow2 (8*x) x ltac:(lia))).
  pose proof (Z.pow_le_mono_r 2 (x-1) x ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma small_depth x y : 17<=x -> 0<=y<=x ->
  6*x+9+(30*y+1)*(6*y+9)+8*x<=200*x^2.
Proof. intros. nia. Qed.

Lemma large_depth_poly x : 0<=x ->
  6*x+9+(2^64*(x+1)^4+1)*(6*x+9)+8*x<=2^70*(x+1)^5.
Proof.
  intro Hx. pose proof (Z.pow_le_mono_l 1 (x+1) 4 ltac:(lia)) as HP.
  change (1<=(x+1)^4) in HP.
  replace ((x+1)^5) with ((x+1)^4*(x+1)) by ring.
  generalize ((x+1)^4) HP. intros z Hz. nia.
Qed.

Lemma large_depth x y : 0<=y<=x ->
  6*x+9+(2^64*(y+1)^4+1)*(6*y+9)+8*x<=2^70*(x+1)^5.
Proof.
  intro Hy. pose proof (Z.pow_le_mono_l (y+1) (x+1) 4 ltac:(lia)) as HP.
  pose proof (Z.pow_nonneg (y+1) 4 ltac:(lia)) as HP0.
  pose proof (Z.mul_le_mono_nonneg
    (2^64*(y+1)^4+1) (2^64*(x+1)^4+1) (6*y+9) (6*x+9)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hprod.
  pose proof (large_depth_poly x ltac:(lia)). lia.
Qed.

Lemma mass_poly k : 3<=k -> 2*(12*k^3+k*(12*k^3+3))+3<k^8.
Proof.
  intro Hk. assert (Hsmall : 2*(12*k^3+k*(12*k^3+3))+3<=40*k^4) by nia.
  assert (Hpow : 81<=k^4).
  { change (3^4<=k^4). apply Z.pow_le_mono_l. lia. }
  assert (Hbig : 40*k^4<k^8).
  { replace (k^8) with (k^4*k^4) by ring. generalize (k^4) Hpow. intros z Hz. nia. }
  lia.
Qed.

Lemma mass_bound k L n : 3<=k -> 0<=L<=k -> 0<=n<=k ->
  2*(12*k^3+n*(12*L^3+3))+3<k^8.
Proof.
  intros Hk HL Hn. pose proof (Z.pow_le_mono_l L k 3 HL).
  pose proof (Z.pow_nonneg L 3 ltac:(lia)).
  pose proof (Z.mul_le_mono_nonneg n k (12*L^3+3) (12*k^3+3)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (mass_poly k Hk). lia.
Qed.

Lemma assemble k x y r : 65536<k -> x=Z.log2_up k -> y=Z.log2_up (8*x) ->
  0<=r -> WordLink.bound (8*x) r -> 6*x+9+(r+1)*(6*y+9)+8*x<k ->
  Closure.budget k.
Proof.
  intros Hk Hx Hy Hr Hword HD.
  destruct (cutoff k Hk) as [Hx17 [Hpow [HL Hys]]].
  rewrite <- Hx in Hx17,Hpow,HL,Hys.
  assert (Hn : r+1<k).
  { rewrite <- Hy in Hys. nia. }
  exists (8*x),(Z.to_nat (r+1)).
  rewrite Z2Nat.id by lia. replace (r+1-1) with r by lia.
  split; [lia|]. split; [exact Hword|]. split; [rewrite <- Hx,<- Hy; exact HD|].
  eapply Z.lt_le_trans; [apply mass_bound; lia|].
  replace (8*x) with (x*8) by ring. rewrite Z.pow_mul_r by lia.
  apply Z.pow_le_mono_l. lia.
Qed.

Theorem budget k : 65536<k -> Closure.earlier k -> Closure.budget k.
Proof.
  intros Hk Hprevious. destruct (cutoff k Hk) as [Hx [Hpow [HL Hy]]].
  set (x:=Z.log2_up k) in *. set (y:=Z.log2_up (8*x)) in *.
  destruct (Z_le_gt_dec (8*x) (2^120)) as [Hsmall|Hlarge].
  - apply (assemble k x y (30*y) Hk eq_refl eq_refl ltac:(lia)).
    + apply SmallScale.range120; [lia|]. apply (SmallScale.earlier_parameters k); lia || assumption.
    + pose proof (small_depth x y Hx Hy). pose proof (Exponential.final_square x Hx). lia.
  - apply (assemble k x y (2^64*(y+1)^4) Hk eq_refl eq_refl
      ltac:(pose proof (Z.pow_nonneg (y+1) 4 ltac:(lia)); lia)).
    + apply (GlobalBounds.quartic k Hprevious). exact HL.
    + assert (Hx1024 : 1024<=x).
      { assert (8*1024<2^120) by (vm_compute; reflexivity). lia. }
      pose proof (large_depth x y Hy). pose proof (Exponential.final_tail x Hx1024). lia.
Qed.

End FinalBudget.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RD_1LA---_1RE1RD_1LF0LA_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0;0] *> [1]^^c *> r.

Definition S2 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [1;0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2 a b c r:
  S2 a b (1+c) r -->*
  S2 (1+a) b c r.
Proof.
  es.
Qed.

Lemma Incs2 a b c r:
  S2 a b c r -->*
  S2 (c+a) b 0 r.
Proof.
  gen a b.
  ind c Inc2.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 d (3+a+c) e r.
Proof.
  mid10 (S2 0 (2+a+c) d ([0] *> [1]^^e *> r)).
  1: es.
  follow Incs2.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Lemma MacroE n v w d e r :
  S1 v (2*n) w ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 d (2*n+v+w+3) e r.
Proof.
  mid01 (S1 (n+v) 0 (n+w) ([0] *> [1]^^d *> [0] *> [1]^^e *> r)).
  - applys_eq (Incs1 n v 0 w ([0] *> [1]^^d *> [0] *> [1]^^e *> r)); flia.
  - applys_eq (Ov0 (n+v) (n+w) d e r); flia.
Qed.

Lemma MacroO n v w r : 1<=n+v ->
  S1 v (2*n+1) w r -->+
  S1 0 (n+v-1) 1 ([0] *> [1]^^(w+n+1) *> r).
Proof.
  intro H. mid01 (S1 (n+v) 1 (n+w) r).
  - applys_eq (Incs1 n v 1 w r); flia.
  - applys_eq (Ov1 (n+v-1) (n+w) r); flia.
Qed.

Fixpoint tail_words (xs:list nat) :=
  match xs with [] => 0inf | n::xs => [0] *> [1]^^n *> tail_words xs end.

Definition Config (xs:list nat) :=
  match xs with
  | [] => S1 0 0 0 0inf
  | [u] => S1 0 u 0 0inf
  | [u;v] => S1 v u 0 0inf
  | u::v::w::r => S1 v u w (tail_words r)
  end.

Lemma step_spec e xs ys : Prefix.Step e xs ys -> Config xs -->+ Config ys.
Proof.
  intro H. destruct H as [n v w r|n v w r H].
  - destruct r as [|d [|e r]]; cbn [Config tail_words].
    + applys_eq (MacroE n v w 0 0 0inf); flia; unfold S1; simpl_tape; reflexivity.
    + applys_eq (MacroE n v w d 0 0inf); flia; unfold S1; simpl_tape; reflexivity.
    + apply MacroE.
  - apply MacroO; assumption.
Qed.

Lemma run_spec e xs ys : Prefix.Run e xs ys -> Config xs -->* Config ys.
Proof.
  intro H. induction H; [apply evstep_refl|].
  eapply evstep_trans; [apply progress_evstep; eapply step_spec; eassumption|assumption].
Qed.

Lemma run_progress e xs ys : Prefix.Run e xs ys -> 0<e -> Config xs -->+ Config ys.
Proof.
  intros H He. destruct H; [lia|].
  eapply progress_evstep_trans; [eapply step_spec; eassumption|eapply run_spec; eassumption].
Qed.

Lemma tail_words_zero xs : tail_words (xs++[0%nat])=tail_words xs.
Proof.
  induction xs; cbn [List.app tail_words]; [simpl_tape; reflexivity|].
  rewrite IHxs; reflexivity.
Qed.

Lemma Config_zero xs : Config (xs++[0%nat])=Config xs.
Proof.
  destruct xs as [|u [|v [|w xs]]]; cbn [Config List.app tail_words].
  all: try (rewrite tail_words_zero; reflexivity).
  all: unfold S1; simpl_tape; reflexivity.
Qed.

Lemma init : c0 -->* Config [].
Proof. unfold Config,S1. esx. Qed.

Lemma exec_spec e xs ys : Prefix.Exec e xs ys -> Config xs -->* Config ys.
Proof.
  intro H. induction H.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep; eapply step_spec; eassumption|assumption].
  - rewrite <- Config_zero. assumption.
Qed.

Lemma exec_progress e xs ys : Prefix.Exec e xs ys -> 0<e -> Config xs -->+ Config ys.
Proof.
  intro H. induction H; intro He.
  - lia.
  - eapply progress_evstep_trans; [eapply step_spec; eassumption|eapply exec_spec; eassumption].
  - rewrite <- Config_zero. auto.
Qed.

Lemma nonhalt_of_returns :
  (forall k, exists e m, Prefix.Exec (1+e) [3*k] [m]) -> ~halts tm c0.
Proof.
  intro Hreturn. eapply multistep_nonhalt; [apply init|].
  rewrite <- (Config_zero []).
  apply (progress_nonhalt_simple tm nat (fun k => Config [3*k]) 0%nat).
  intro k. destruct (Hreturn k) as [e [m H]].
  pose proof (Prefix.exec_mass _ _ _ H) as Hmass.
  cbn [Prefix.mass fold_right] in Hmass.
  exists (k+1+e). replace (3*(k+1+e)) with m by lia.
  eapply exec_progress; [exact H|lia].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply nonhalt_of_returns,Prefix.single_returns,Closure.G_returns,FinalBudget.budget.
Qed.

End TM1.

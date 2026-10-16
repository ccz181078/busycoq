From Coq Require Import List Arith Lia.
From BusyCoq Require Export Row9Eval Row9Algebra.
Import ListNotations.

Definition F (x:result) : result := bind x f.
Definition prefix (d:nat) (x:result) : result := option_map (cons d) x.
Definition Q := prefix 2.
Definition Z := prefix 0.
Definition G (x:result) : result := option_map (@tl nat) (F(Z x)).
Definition T (n:nat) (x:result) : result := Z(power F n x).
Definition H (n:nat) (x:result) : result := G(power F n x).
Definition P (n:nat) (x:result) : result := Z(power Q n x).
Definition K (n:nat) (x:result) : Prop := eventually (H n) x.

Lemma F_none : F None=None. Proof. reflexivity. Qed.
Lemma G_none : G None=None. Proof. reflexivity. Qed.
Lemma prefix_none d x : prefix d x=None <-> x=None.
Proof. unfold prefix. destruct x; simpl; split; intros E; try discriminate; reflexivity. Qed.
Lemma Q_none x : Q x=None <-> x=None.
Proof. apply prefix_none. Qed.
Lemma Z_none x : Z x=None <-> x=None.
Proof. apply prefix_none. Qed.
Lemma F_Q x : F(Q x)=Q(F x).
Proof. destruct x as [U|];[|reflexivity]. unfold F,Q,prefix,bind; simpl.
 rewrite f_two. destruct(f U);reflexivity. Qed.
Lemma f_zero_head U : f(0::U)=Q(option_map(@tl nat)(f(0::U))).
Proof.
 destruct U as [|a U];[rewrite f_zero;reflexivity|].
 destruct a as[|[|[|a]]].
 - rewrite f_zero_zero. reflexivity.
 - rewrite f_zero_one. destruct(f U);reflexivity.
 - rewrite f_zero_two. destruct(f U);reflexivity.
 - replace (S(S(S a))) with(a+3) by lia. rewrite f_zero_large.
   destruct(f(a::U));reflexivity.
Qed.
Lemma F_Z x : F(Z x)=Q(G x).
Proof. destruct x as[U|];[|reflexivity]. apply f_zero_head. Qed.
Lemma G_Q x : G(Q x)=Z(F x).
Proof. destruct x as[U|];[|reflexivity]. unfold G,F,Z,Q,prefix,bind; simpl.
 rewrite f_zero_two. destruct(f U);reflexivity. Qed.
Lemma G_nine U : G(Some(9::U))=Some(2::2::U).
Proof. unfold G,F,Z,prefix,bind; simpl.
 change (option_map(@tl nat)(f(0::(6+3)::U))=Some(2::2::U)).
 rewrite f_zero_large. replace 6 with(2+4) by lia. rewrite f_large. reflexivity.
Qed.
Lemma F_three x : F(prefix 3 x)=prefix 3(F(F x)).
Proof. destruct x as[U|];[|reflexivity]. unfold F,prefix,bind; simpl.
 rewrite f_three. destruct(f U);reflexivity. Qed.
Lemma G_three x : G(prefix 3 x)=prefix 3(G x).
Proof.
 destruct x as[U|];[|reflexivity].
 change(option_map(@tl nat)(f(0::(0+3)::U))=prefix 3(G(Some U))).
 rewrite f_zero_large.
 change (option_map (@tl nat)(lift_prefix [2](lift_plus 1(F(Z(Some U)))))=prefix 3(G(Some U))).
 rewrite F_Z. destruct(G(Some U));reflexivity.
Qed.

Lemma T_none n : T n None=None.
Proof. unfold T,result. rewrite (power_strict F F_none n). reflexivity. Qed.
Lemma H_none n : H n None=None.
Proof. unfold H,result. rewrite (power_strict F F_none n). reflexivity. Qed.
Lemma P_none n x : P n x=None <-> x=None.
Proof. apply(inert_none Q Z Q_none Z_none). Qed.
Theorem H_T n x : 1<=n -> H n(T n x)=T n(H n x).
Proof. apply(phaseG_phase F Q Z G F_Q F_Z G_Q). Qed.
Theorem T_P n x : T n(P n x)=P n(T n x).
Proof. apply(phase_inert F Q Z G F_Q F_Z G_Q). Qed.
Theorem H_P n x : 1<=n -> H n(P n x)=P n(H n x).
Proof. apply(phaseG_inert F Q Z G F_Q F_Z G_Q). Qed.
Theorem T_factor n x : 1<=n -> power(T n)(S n)x=P n(power(H n)n x).
Proof. apply(phase_factor F Q Z G F_Q F_Z G_Q). Qed.
Theorem T_cofinal_factor n k x : 1<=n ->
 power(T n)(k*S n)x=power(P n)k(power(H n)(k*n)x).
Proof. apply(cofinal_factor F Q Z G F_Q F_Z G_Q). Qed.
Theorem K_T_equiv n x : 1<=n -> eventually(T n)x <-> K n x.
Proof. apply(phase_eventually F Q Z G F_none G_none Q_none Z_none F_Q F_Z G_Q). Qed.
Theorem Q_index_nonincrease n k x : 1<=n ->
 power(H n)k(Q x)=None -> power(H n)k(F x)=None.
Proof. apply(Q_index_nonincrease_abstract F Q Z G F_none G_none Q_none Z_none F_Q F_Z G_Q). Qed.
Theorem K_Q n x : 1<=n -> K n(Q x)<->K n(F x).
Proof. apply(phaseG_eventually_Q F Q Z G F_none G_none Q_none Z_none F_Q F_Z G_Q). Qed.
Theorem K_Z n x : 1<=n -> K n(Z x)<->K n(G x).
Proof. apply(phaseG_eventually_Z F Q Z G F_none G_none Z_none F_Q F_Z G_Q). Qed.
Theorem K_H n x : K n x <-> K n(H n x).
Proof. apply eventually_step,H_none. Qed.
Theorem K_T n x : 1<=n -> K n x <-> K n(T n x).
Proof. intro Hn. rewrite <-!K_T_equiv by lia. apply eventually_step,T_none. Qed.
Theorem K_None n : K n None.
Proof. exists 0. reflexivity. Qed.

Lemma F_power_three n x : power F n(prefix 3 x)=prefix 3(power F(2*n)x).
Proof.
 induction n;[reflexivity|]. simpl power at 1. rewrite IHn,F_three.
 replace(2*S n) with(S(S(2*n))) by lia. reflexivity.
Qed.
Lemma H_three n x : H n(prefix 3 x)=prefix 3(H(2*n)x).
Proof. unfold H. rewrite F_power_three,G_three. reflexivity. Qed.
Lemma H_power_three n k x :
 power(H n)k(prefix 3 x)=prefix 3(power(H(2*n))k x).
Proof. induction k;[reflexivity|]. simpl power. rewrite IHk,H_three. reflexivity. Qed.
Theorem K_three n x : K n(prefix 3 x)<->K(2*n)x.
Proof. unfold K,eventually,result in *. split;intros[k E];exists k.
 - rewrite H_power_three in E. apply(proj1(prefix_none 3 _)),E.
 - rewrite H_power_three. unfold result in *. rewrite E. reflexivity.
Qed.

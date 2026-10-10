From Coq Require Import List Arith Lia.
From BusyCoq Require Import Row9Operators Row9Binary.
Import ListNotations.

(** A literal four is stable under every positive phase clock.  Its tail
    alternates a G call with a smaller number of F calls. *)
Lemma four_G_one x : G(prefix 1 x)=lift_plus 2(F x).
Proof.
 destruct x as [U|];[|reflexivity].
 change(option_map(@tl nat)(f(0::1::U))=lift_plus 2(f U)).
 rewrite f_zero_one. destruct(f U);reflexivity.
Qed.
Lemma four_G_six x : G(prefix 6 x)=prefix 4(F(F x)).
Proof.
 destruct x as [U|];[|reflexivity].
 change(option_map(@tl nat)(f(0::(3+3)::U))=prefix 4(F(F(Some U)))).
 rewrite f_zero_large,f_three.
 change(option_map(@tl nat)(lift_prefix [2](lift_plus 1(prefix 3(F(F(Some U))))))=
        prefix 4(F(F(Some U)))).
 destruct(F(F(Some U)));reflexivity.
Qed.
Lemma four_prefix_D_Z x : prefix 4 x=D(Z x).
Proof. destruct x;reflexivity. Qed.
Lemma four_D_Q x : D(Q x)=prefix 6 x.
Proof. destruct x;reflexivity. Qed.
Lemma four_plus_Q x : lift_plus 2(Q x)=prefix 4 x.
Proof. destruct x;reflexivity. Qed.
Lemma four_F_power_Z n x : power F(S n)(Z x)=Q(power F n(G x)).
Proof. rewrite power_succ_r,F_Z. apply power_commute,F_Q. Qed.

Lemma H_four_even m x : 1<=m ->
 H(2*m)(prefix 4 x)=prefix 4(power F(m+1)(G x)).
Proof.
 intros Hm. unfold H. rewrite four_prefix_D_Z,acc_D_even.
 - destruct m as[|m];[lia|]. rewrite four_F_power_Z,four_D_Q,four_G_six.
   replace(S m+1) with(S(S m)) by lia. reflexivity.
 - destruct x;discriminate.
Qed.
Lemma H_four_odd m x : 1<=m ->
 H(2*m+1)(prefix 4 x)=prefix 4(power F m(G x)).
Proof.
 intros Hm. unfold H. rewrite four_prefix_D_Z,acc_D_odd.
 - destruct m as[|m];[lia|]. rewrite four_F_power_Z.
   unfold L1. rewrite four_G_one,F_Q,four_plus_Q. reflexivity.
 - destruct x;discriminate.
Qed.
Lemma H_four_one x : H 1(prefix 4 x)=prefix 4(G x).
Proof.
 unfold H. rewrite four_prefix_D_Z.
 change(G(power F(2*0+1)(D(Z x)))=prefix 4(G x)).
 rewrite acc_D_odd by (destruct x;discriminate).
 cbn [power]. unfold L1. now rewrite four_G_one,F_Z,four_plus_Q.
Qed.

Lemma K_four_transfer n e x :
 (forall y,H n(prefix 4 y)=prefix 4(power F e(G y))) ->
 (K n(prefix 4 x) <-> K e(G x)).
Proof.
 intro E.
 assert(C:forall k y,power(H n)k(prefix 4 y)=
   prefix 4(power(fun z=>power F e(G z))k y)).
 { intro k;induction k;intro y;cbn [power];[reflexivity|].
   rewrite IHk,E. reflexivity. }
 assert(B:K n(prefix 4 x)<->eventually(fun z=>power F e(G z))x).
 { unfold K,eventually. split;intros[k Ek];exists k.
   - rewrite C in Ek. now apply(proj1(prefix_none 4 _))in Ek.
   - rewrite C. unfold result in *. rewrite Ek. reflexivity. }
 rewrite B. unfold K,H.
 apply(eventually_rotate (power F e) G).
 - apply power_strict,F_none.
 - apply G_none.
Qed.
Theorem K_four_even m x : 1<=m ->
 (K(2*m)(prefix 4 x)<->K(m+1)(G x)).
Proof. intro Hm;apply K_four_transfer;intro y;now apply H_four_even. Qed.
Theorem K_four_odd m x : 1<=m ->
 (K(2*m+1)(prefix 4 x)<->K m(G x)).
Proof. intro Hm;apply K_four_transfer;intro y;now apply H_four_odd. Qed.

Definition four_clock n :=
 if Nat.even n then n/2+1 else (n-1)/2.
Lemma four_clock_even m : four_clock(2*m)=m+1.
Proof.
 unfold four_clock. rewrite Nat.even_mul. change(2*m/2+1=m+1).
 replace(2*m) with(m*2) by lia. now rewrite Nat.div_mul by lia.
Qed.
Lemma four_clock_odd m : four_clock(2*m+1)=m.
Proof.
 unfold four_clock. rewrite Nat.even_add,Nat.even_mul. change((2*m+1-1)/2=m).
 replace(2*m+1-1) with(m*2) by lia. now rewrite Nat.div_mul by lia.
Qed.
Lemma four_clock_positive n : 2<=n -> 1<=four_clock n.
Proof.
 intros Hn. destruct(Nat.Even_or_Odd n)as[[m ->]|[m ->]].
 - rewrite four_clock_even;lia.
 - rewrite four_clock_odd;lia.
Qed.
Theorem H_four n x : 1<=n ->
 H n(prefix 4 x)=prefix 4(power F(four_clock n)(G x)).
Proof.
 intro Hn. destruct(Nat.Even_or_Odd n)as[[m ->]|[m ->]].
 - rewrite four_clock_even. apply H_four_even;lia.
 - rewrite four_clock_odd. destruct m.
   + apply H_four_one.
   + apply H_four_odd;lia.
Qed.
Theorem K_four n x : 2<=n ->
 (K n(prefix 4 x)<->K(four_clock n)(G x)).
Proof. intro Hn. apply K_four_transfer. intro y;apply H_four;lia. Qed.

Corollary K_three_four n x : 1<=n ->
 (K n(prefix 3(prefix 4 x))<->K(n+1)(G x)).
Proof. intro Hn. rewrite K_three. now apply K_four_even. Qed.

From BusyCoq Require Import Individual62 Longitudinal DivModCases LongN.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import PeanoNat.
Require Import String.
Require Import List.


Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac flia := repeat (lia || f_equal).

Lemma nil_lpow {A} n:
  []^^n = @nil A.
Proof.
  induction n; cbn; trivial.
Qed.

Lemma segRLs_n_trans_1 tm h1 h2 h3 h4 w1 w2 w3:
  segRLs_n tm h1 h2 w1 w2 1 ->
  segRLs_n tm h3 h4 w2 w3 1 ->
  segRLs_n tm (h1++h3) (h2++h4) w1 w3 1.
Proof.
  intros.
  eapply segRLs_n_trans; eauto; lia.
Qed.
Arguments segRLs_n_trans_1 {tm h1 h2 h3 h4 w1 w2 w3} _ _.

Lemma segRLs_n_wall4 tm h1 h2 w n:
  segRLs_n tm h1 h2 w w n ->
  segRLs_n tm (h1^^4) (h2^^4) w w n.
Proof.
  intros.
  eapply segRLs_n_wall; eauto; lia.
Qed.
Arguments segRLs_n_wall4 {tm h1 h2 w n} _.
Arguments segRLs_n_concat' {tm h1 h2 h3 w1 w2 w3 w4 n1 n2} _ _.

Ltac chain4 H1 H2 H3 H4 :=
  let H34 := fresh "H" in
  pose proof (segRLs_n_trans_1 H3 H4) as H34;
  let H234 := fresh "H" in
  pose proof (segRLs_n_trans_1 H2 H34) as H234;
  let H1234 := fresh "H" in
  pose proof (segRLs_n_trans_1 H1 H234) as H1234;
  applys_eq H1234.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC0LB_0RD1LB_1RD1RE_1RF---_0RA1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR1 := (D,@nil Sym).
Notation hR2 := (F,<[1;1]).
Notation hL := (B,@nil Sym).
Notation h1 := [(hR1,hL)].
Notation h2 := [(hR2,hL)].

Definition P1 n := segRLs_n tm (h1^^(2^n*4-2)) (h2^^(2^n*2-1)) ([1]++[0]^^(2^n*6-2)) ([0]^^(2^n*2-1)++[1;0]) (S n).
Definition P2 n := segRLs_n tm (h1^^(2^n*4-1)) (h2^^(2^n*2)) ([1]++[0]^^(2^n*6-2)) ([0]^^(2^n*2-1)) (S n).

Lemma h2s_010 n:
  n<>O ->
  segRLs_n tm (h2^^n) (h1^^(n*2)) ([0;1;0]) ([0;1;0]++[0]^^(n*2)) 1.
Proof.
  do 2 rewrite lpow_mul.
  induction n.
  1: lia.
  destruct n.
  - intros.
    solve_segRLs_n.
  - intros.
    remember (S n) as n'.
    replace (S n') with (n'+1) by lia.
    do 2 rewrite lpow_add.
    eapply segRLs_n_trans.
    + apply IHn; lia.
    + solve_segRLs_n.
    + lia.
    + lia.
Qed.

Lemma h1s_0s n m:
  n<>O ->
  m<>O ->
  segRLs_n tm (h1^^n) (h1^^n) ([0]^^m) ([0]^^m) 1.
Proof.
  intros.
  eapply segRLs_n_wall; eauto.
  destruct m; [lia|].
  solve_segRLs_n.
Qed.

Lemma h2s_10 n:
  n<>O ->
  segRLs_n tm (h2^^n) (h2^^n) [1;0] [1;0] 1.
Proof.
  intros.
  eapply segRLs_n_wall; eauto.
  solve_segRLs_n.
Qed.

Lemma h1_0s10 n:
  segRLs_n tm h1 h2 ([0]^^n++[1;0]) ([0]^^n) (S n).
Proof.
  induction n.
  - solve_segRLs_n.
  - cbn[lpow].
    rewrite <-app_assoc.
    replace (S (S n)) with (1+S n) by lia.
    eapply segRLs_n_concat'.
    2: apply IHn.
    solve_segRLs_n.
Qed.

Lemma h2_00 r:
  segRLs_n tm h2 [] ([0;0]++r) ([0;1;0]++[1]++r) 1.
Proof.
  eapply segRLs_n_S.
  solve_seg.
Qed.

Lemma lpow_add'' {A} (ls:list A) a b ls0:
  ls^^a ++ ls^^b ++ ls0 =
  ls^^(a+b) ++ ls0.
Proof.
  rewrite app_assoc,lpow_add.
  reflexivity.
Qed.

Lemma P1_S n:
  P1 n ->
  P2 n ->
  P1 (S n).
Proof.
  unfold P1,P2.
  intros HP1 HP2.
  cbn[Nat.pow].
  replace (2*2^n*4-2) with ((2^n*4-1)+(2^n*4-1)) by lia.
  replace (h2^^(2*2^n*2-1)) with (h2^^((2^n*2-1)+(2^n*2))) by flia.
  replace (2*2^n*6-2) with ((2^n*6-2)+(2+(2^n*6-2))) by lia.
  do 3 rewrite lpow_add.
  eapply segRLs_n_trans.
  - rewrite app_assoc.
    eapply segRLs_n_concat'.
    1: apply HP2.
    replace (h2^^(2^n*2-1)) with (h2^^(0+(2^n*2-1))) by flia.
    replace (h2^^(2^n*2)) with (h2^^(1+(2^n*2-1))) by flia.
    do 3 rewrite lpow_add.
    eapply segRLs_n_trans'.
    1: apply h2_00.
    eapply segRLs_n_concat'.
    1: apply h2s_010; lia.
    applys_eq HP1; flia.
  - change ([0;1;0]) with ([0]^^1++[1]++[0]^^1).
    repeat rewrite <-app_assoc.
    repeat rewrite lpow_add''.
    replace (2*2^n*2-1) with (2^n*2-1+1+(2^n*2-1)) by lia.
    rewrite (lpow_add _ (2^n*2-1+1)),<-app_assoc.
    eapply segRLs_n_concat'.
    1: eapply h1s_0s; lia.
    rewrite app_assoc.
    eapply segRLs_n_concat'.
    1: applys_eq HP2; flia.
    eapply h2s_10; lia.
  - lia.
  - lia.
Qed.

Lemma pow2_gt n:
  n<2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma P2_S n:
  P1 n ->
  P2 n.
Proof.
  unfold P1,P2.
  intros HP1.
  replace (2^n*4-1) with (2^n*4-2+1) by lia.
  replace (h2^^(2^n*2)) with (h2^^(2^n*2-1+1)) by flia.
  do 2 rewrite lpow_add.
  eapply segRLs_n_trans.
  - apply HP1.
  - eapply h1_0s10.
  - lia.
  - pose proof (pow2_gt n).
    lia.
Qed.

Lemma P1_n n:
  P1 n.
Proof.
  induction n; intros.
  - unfold P1.
    cbn.
    eapply segRLs_n_trans with (h1:=h1) (h2:=[]).
    1: solve_segRLs_n.
    1: solve_segRLs_n.
    all: lia.
  - eapply P1_S; eauto using P2_S.
Qed.

Notation hLR := [(hL,hR1)].

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^n) (0inf<*[1]) (0inf<*[1]^^(1+n)).
Proof.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans; eauto.
    esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=0inf<*[1] {{{ (hR1,R) }}} [1] *> 0inf).
  1: esx.
  eapply step_unbounded_nonhalt.
  intros n.
  epose proof (P1_n n) as HP1.
  unfold P1 in HP1.
  eapply segRLs_n_sideRLs_n in HP1.
  eapply sideRLs_n_mono with (n0:=n) in HP1.
  2: lia.
  eapply sideRLs_n_sideRLs_concat_1 in HP1.
  2: epose proof (pow2_gt n); lia.
  2: apply LIncs.
  rewrite Str_app_assoc in HP1.
  rewrite lpow_all0 in HP1.
  2: solve_const0_eq.
  apply HP1.
Qed.

End TM1.




Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1LA_1RC0LA_1RF0RD_0RE0LB_1RB---_0LB0RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hF:list (DH0*DH0) := [((F,[]),(B,[]))].
Definition hC:list (DH0*DH0) := [((C,[]),(A,[]))].
Definition hB:list (DH0*DH0) := [((B,[]),(A,[]))].
Definition hD:list (DH0*DH0) := [((D,[]),(B,[]))].
Definition hE:list (DH0*DH0) := [((E,[]),(A,[]))].

Definition hP0 := hD++hC++hB.

Definition Z3 : list Sym := [0;0;0].

Definition hA_gt x y := hF++hC++hB^^x++hD++hC++hB^^y.
Definition hA_lt x y := hC++hB^^x++hD++hC++hB^^y++hF.
Definition hA x y := if Nat.ltb y x then hA_gt x y else hA_lt x y.

Definition next_xy '(x,y) :=
  match mod2 x with
  | mod2eq0 a =>
      match mod2 y with
      | mod2eq0 b => (b+1, a*2+b+1)
      | mod2eq1 b => (b+1, a*2+b+1)
      end
  | mod2eq1 a => (a+y+2, a+1)
  end.

Fixpoint xy n :=
match n with
| O => (4,2)
| S n => next_xy (xy n)
end.

Definition period n := hA (fst (xy n)) (snd (xy n)).
Definition rect_width n := 13 + 3*n.
Definition zeros n : list Sym := [0]^^n.

Ltac rstep H w :=
  refine (@segRLs_n_trans_1 _ _ _ _ _ _ _ w H _).

Ltac rclean :=
  repeat (rewrite lpow_add || rewrite app_nil_r); cbn;
  solve [flia | reflexivity].

Lemma hB_cons_pow n (xs:list (DH0*DH0)):
  hB++hB^^n++xs = hB^^(n+1)++xs.
Proof.
  replace (n+1) with (S n) by lia.
  cbn [lpow].
  reflexivity.
Qed.

Lemma hB_pows_app m n (xs:list (DH0*DH0)):
  hB^^m++hB^^n++xs = hB^^(m+n)++xs.
Proof.
  rewrite app_assoc.
  rewrite <- (lpow_add (DH0*DH0) m n hB).
  reflexivity.
Qed.

Lemma hB_cons_pow0 n:
  hB++hB^^n = hB^^(n+1).
Proof.
  replace (hB++hB^^n) with (hB++hB^^n++[]) by (rewrite app_nil_r; reflexivity).
  rewrite hB_cons_pow.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma hB_pows0 m n:
  hB^^m++hB^^n = hB^^(m+n).
Proof.
  rewrite <- (lpow_add (DH0*DH0) m n hB).
  reflexivity.
Qed.

Ltac bclean :=
  unfold hA, hA_gt, hA_lt in *;
  cbn [fst snd lpow];
  repeat match goal with
  | H: Nat.ltb ?a ?b = ?v |- context[Nat.ltb ?a ?b] => rewrite H
  end;
  repeat match goal with
  | |- context[Nat.ltb ?a ?b] =>
      destruct (Nat.ltb_spec0 a b); try lia
  end;
  repeat (rewrite app_nil_l || rewrite app_nil_r || rewrite <- app_assoc ||
          rewrite hB_cons_pow || rewrite hB_pows_app ||
          rewrite hB_cons_pow0 || rewrite hB_pows0);
  solve [flia | reflexivity].

Lemma M_000_B: segRLs_n tm hB [] Z3 [1;0;0] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_000_C: segRLs_n tm hC [] Z3 Z3 1.
Proof. solve_segRLs_n. Qed.

Lemma M_000_D: segRLs_n tm hD hC Z3 [1;1;1] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_000_F: segRLs_n tm hF [] Z3 Z3 1.
Proof. solve_segRLs_n. Qed.

Lemma M_100_B: segRLs_n tm hB [] [1;0;0] Z3 1.
Proof. solve_segRLs_n. Qed.

Lemma M_100_D: segRLs_n tm hD [] [1;0;0] Z3 1.
Proof. solve_segRLs_n. Qed.

Lemma M_100_F: segRLs_n tm hF hF [1;0;0] [1;1;0] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_110_C: segRLs_n tm hC [] [1;1;0] [1;0;0] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_111_C: segRLs_n tm hC hB [1;1;1] [1;0;1] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_101_B: segRLs_n tm hB [] [1;0;1] [0;0;1] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_101_D: segRLs_n tm hD [] [1;0;1] [0;0;1] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_101_F: segRLs_n tm hF (hD++hC) [1;0;1] [1;1;1] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_001_B: segRLs_n tm hB hB [0;0;1] [1;0;1] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_001_C: segRLs_n tm hC [] [0;0;1] [0;0;1] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_001_D: segRLs_n tm hD [] [0;0;1] [1;1;0] 1.
Proof. solve_segRLs_n. Qed.

Lemma M_001_F: segRLs_n tm hF [] [0;0;1] [0;0;1] 1.
Proof. solve_segRLs_n. Qed.

Lemma BR_000_cycle: segRLs_n tm (hB^^2) [] Z3 Z3 1.
Proof.
  applys_eq (segRLs_n_trans_1 M_000_B M_100_B); cbn; reflexivity.
Qed.

Lemma BR_100_cycle: segRLs_n tm (hB^^2) [] [1;0;0] [1;0;0] 1.
Proof.
  applys_eq (segRLs_n_trans_1 M_100_B M_000_B); cbn; reflexivity.
Qed.

Lemma BR_001_cycle: segRLs_n tm (hB^^2) hB [0;0;1] [0;0;1] 1.
Proof.
  applys_eq (segRLs_n_trans_1 M_001_B M_101_B); cbn; reflexivity.
Qed.

Lemma BR_101_cycle: segRLs_n tm (hB^^2) hB [1;0;1] [1;0;1] 1.
Proof.
  applys_eq (segRLs_n_trans_1 M_101_B M_001_B); cbn; reflexivity.
Qed.

Ltac solve_B_even n H :=
  intros Hn;
  rewrite (lpow_mul hB n 2);
  try replace ([]:(list (DH0*DH0))) with ((@nil (DH0*DH0))^^n) by apply nil_lpow;
  eapply segRLs_n_wall; [apply H|exact Hn].

Ltac solve_B_odd n H0 Heven :=
  destruct n;
  [ applys_eq H0; cbn; reflexivity
  | pose proof (Heven (S n) ltac:(lia)) as H;
    replace (S n*2+1) with (1+S n*2) by lia;
    rewrite lpow_add;
    applys_eq (segRLs_n_trans_1 H0 H); bclean ].

Lemma BR_000_even n: n<>O -> segRLs_n tm (hB^^(n*2)) [] Z3 Z3 1.
Proof.
  solve_B_even n BR_000_cycle.
Qed.

Lemma BR_100_even n: n<>O -> segRLs_n tm (hB^^(n*2)) [] [1;0;0] [1;0;0] 1.
Proof.
  solve_B_even n BR_100_cycle.
Qed.

Lemma BR_001_even n: n<>O -> segRLs_n tm (hB^^(n*2)) (hB^^n) [0;0;1] [0;0;1] 1.
Proof.
  solve_B_even n BR_001_cycle.
Qed.

Lemma BR_101_even n: n<>O -> segRLs_n tm (hB^^(n*2)) (hB^^n) [1;0;1] [1;0;1] 1.
Proof.
  solve_B_even n BR_101_cycle.
Qed.

Lemma BR_000_odd n: segRLs_n tm (hB^^(n*2+1)) [] Z3 [1;0;0] 1.
Proof.
  solve_B_odd n M_000_B BR_100_even.
Qed.

Lemma BR_100_odd n: segRLs_n tm (hB^^(n*2+1)) [] [1;0;0] Z3 1.
Proof.
  solve_B_odd n M_100_B BR_000_even.
Qed.

Lemma BR_001_odd n: segRLs_n tm (hB^^(n*2+1)) (hB^^(n+1)) [0;0;1] [1;0;1] 1.
Proof.
  solve_B_odd n M_001_B BR_101_even.
Qed.

Lemma BR_101_odd n: segRLs_n tm (hB^^(n*2+1)) (hB^^n) [1;0;1] [0;0;1] 1.
Proof.
  solve_B_odd n M_101_B BR_001_even.
Qed.

Lemma Agt_even_000 a b:
  a<>O -> b<>O ->
  segRLs_n tm (hA_gt (a*2) (b*2)) (hC++hB++hB^^b) Z3 [1;0;1] 1.
Proof.
  intros Ha Hb.
  unfold hA_gt.
  rstep M_000_F [1;0;1].
  rstep M_000_C [1;0;1].
  rstep (BR_000_even a Ha) [1;0;1].
  rstep M_000_D [1;0;1].
  rstep M_111_C [1;0;1].
  applys_eq (BR_101_even b Hb).
  all: rclean.
Qed.

Lemma Agt_even_101 a b:
  a<>O -> b<>O ->
  segRLs_n tm (hA_gt (a*2) (b*2)) (hD++hC++hB++hB^^a++hB^^b) [1;0;1] [0;0;1] 1.
Proof.
  intros Ha Hb.
  unfold hA_gt.
  rstep M_101_F [0;0;1].
  rstep M_111_C [0;0;1].
  rstep (BR_101_even a Ha) [0;0;1].
  rstep M_101_D [0;0;1].
  rstep M_001_C [0;0;1].
  applys_eq (BR_001_even b Hb).
  all: rclean.
Qed.

Lemma Agt_even_001 a b:
  a<>O -> b<>O ->
  segRLs_n tm (hA_gt (a*2) (b*2)) (hB^^a++[]) [0;0;1] [1;0;0] 1.
Proof.
  intros Ha Hb.
  unfold hA_gt.
  rstep M_001_F [1;0;0].
  rstep M_001_C [1;0;0].
  rstep (BR_001_even a Ha) [1;0;0].
  rstep M_001_D [1;0;0].
  rstep M_110_C [1;0;0].
  applys_eq (BR_100_even b Hb).
  all: rclean.
Qed.

Lemma Agt_even_100 a b:
  a<>O -> b<>O ->
  segRLs_n tm (hA_gt (a*2) (b*2)) (hF++[]) [1;0;0] Z3 1.
Proof.
  intros Ha Hb.
  unfold hA_gt.
  rstep M_100_F Z3.
  rstep M_110_C Z3.
  rstep (BR_100_even a Ha) Z3.
  rstep M_100_D Z3.
  rstep M_000_C Z3.
  applys_eq (BR_000_even b Hb).
  all: rclean.
Qed.

Lemma Alt_even_000 a b:
  a<>O -> b<>O ->
  segRLs_n tm (hA_lt (a*2) (b*2)) (hC++hB++hB^^b++hD++hC) Z3 [1;1;1] 1.
Proof.
  intros Ha Hb.
  unfold hA_lt.
  rstep M_000_C [1;1;1].
  rstep (BR_000_even a Ha) [1;1;1].
  rstep M_000_D [1;1;1].
  rstep M_111_C [1;1;1].
  rstep (BR_101_even b Hb) [1;1;1].
  applys_eq M_101_F.
  all: rclean.
Qed.

Lemma Alt_even_111 a b:
  a<>O -> b<>O ->
  segRLs_n tm (hA_lt (a*2) (b*2)) (hB++hB^^a++hB^^b++[]) [1;1;1] [0;0;1] 1.
Proof.
  intros Ha Hb.
  unfold hA_lt.
  rstep M_111_C [0;0;1].
  rstep (BR_101_even a Ha) [0;0;1].
  rstep M_101_D [0;0;1].
  rstep M_001_C [0;0;1].
  rstep (BR_001_even b Hb) [0;0;1].
  applys_eq M_001_F.
  all: rclean.
Qed.

Lemma Alt_even_001 a b:
  a<>O -> b<>O ->
  segRLs_n tm (hA_lt (a*2) (b*2)) (hB^^a++hF) [0;0;1] [1;1;0] 1.
Proof.
  intros Ha Hb.
  unfold hA_lt.
  rstep M_001_C [1;1;0].
  rstep (BR_001_even a Ha) [1;1;0].
  rstep M_001_D [1;1;0].
  rstep M_110_C [1;1;0].
  rstep (BR_100_even b Hb) [1;1;0].
  applys_eq M_100_F.
  all: rclean.
Qed.

Lemma Alt_even_110 a b:
  a<>O -> b<>O ->
  segRLs_n tm (hA_lt (a*2) (b*2)) [] [1;1;0] Z3 1.
Proof.
  intros Ha Hb.
  unfold hA_lt.
  rstep M_110_C Z3.
  rstep (BR_100_even a Ha) Z3.
  rstep M_100_D Z3.
  rstep M_000_C Z3.
  rstep (BR_000_even b Hb) Z3.
  applys_eq M_000_F.
  all: rclean.
Qed.

Lemma Agt_odd_000 p q:
  segRLs_n tm (hA_gt (p*2+1) (q*2+1)) [] Z3 [1;0;0] 1.
Proof.
  unfold hA_gt.
  rstep M_000_F [1;0;0].
  rstep M_000_C [1;0;0].
  rstep (BR_000_odd p) [1;0;0].
  rstep M_100_D [1;0;0].
  rstep M_000_C [1;0;0].
  applys_eq (BR_000_odd q).
  all: rclean.
Qed.

Lemma Agt_odd_100 p q:
  segRLs_n tm (hA_gt (p*2+1) (q*2+1)) (hF++hC++hB++hB^^q) [1;0;0] [0;0;1] 1.
Proof.
  unfold hA_gt.
  rstep M_100_F [0;0;1].
  rstep M_110_C [0;0;1].
  rstep (BR_100_odd p) [0;0;1].
  rstep M_000_D [0;0;1].
  rstep M_111_C [0;0;1].
  applys_eq (BR_101_odd q).
  all: rclean.
Qed.

Lemma Agt_odd_001 p q:
  segRLs_n tm (hA_gt (p*2+1) (q*2+1)) (hB^^(p+1)++hB^^(q+1)) [0;0;1] [1;0;1] 1.
Proof.
  unfold hA_gt.
  rstep M_001_F [1;0;1].
  rstep M_001_C [1;0;1].
  rstep (BR_001_odd p) [1;0;1].
  rstep M_101_D [1;0;1].
  rstep M_001_C [1;0;1].
  applys_eq (BR_001_odd q).
  all: rclean.
Qed.

Lemma Agt_odd_101 p q:
  segRLs_n tm (hA_gt (p*2+1) (q*2+1)) (hD++hC++hB++hB^^p++[]) [1;0;1] Z3 1.
Proof.
  unfold hA_gt.
  rstep M_101_F Z3.
  rstep M_111_C Z3.
  rstep (BR_101_odd p) Z3.
  rstep M_001_D Z3.
  rstep M_110_C Z3.
  applys_eq (BR_100_odd q).
  all: rclean.
Qed.

Lemma Alt_odd_000 p q:
  segRLs_n tm (hA_lt (p*2+1) (q*2+1)) hF Z3 [1;1;0] 1.
Proof.
  unfold hA_lt.
  rstep M_000_C [1;1;0].
  rstep (BR_000_odd p) [1;1;0].
  rstep M_100_D [1;1;0].
  rstep M_000_C [1;1;0].
  rstep (BR_000_odd q) [1;1;0].
  applys_eq M_100_F.
  all: rclean.
Qed.

Lemma Alt_odd_110 p q:
  segRLs_n tm (hA_lt (p*2+1) (q*2+1)) (hC++hB++hB^^q++[]) [1;1;0] [0;0;1] 1.
Proof.
  unfold hA_lt.
  rstep M_110_C [0;0;1].
  rstep (BR_100_odd p) [0;0;1].
  rstep M_000_D [0;0;1].
  rstep M_111_C [0;0;1].
  rstep (BR_101_odd q) [0;0;1].
  applys_eq M_001_F.
  all: rclean.
Qed.

Lemma Alt_odd_001 p q:
  segRLs_n tm (hA_lt (p*2+1) (q*2+1)) (hB^^(p+1)++hB^^(q+1)++hD++hC) [0;0;1] [1;1;1] 1.
Proof.
  unfold hA_lt.
  rstep M_001_C [1;1;1].
  rstep (BR_001_odd p) [1;1;1].
  rstep M_101_D [1;1;1].
  rstep M_001_C [1;1;1].
  rstep (BR_001_odd q) [1;1;1].
  applys_eq M_101_F.
  all: rclean.
Qed.

Lemma Alt_odd_111 p q:
  segRLs_n tm (hA_lt (p*2+1) (q*2+1)) (hB++hB^^p++[]) [1;1;1] Z3 1.
Proof.
  unfold hA_lt.
  rstep M_111_C Z3.
  rstep (BR_101_odd p) Z3.
  rstep M_001_D Z3.
  rstep M_110_C Z3.
  rstep (BR_100_odd q) Z3.
  applys_eq M_000_F.
  all: rclean.
Qed.

Lemma step_even_gt a b:
  a<>O -> b<>O ->
  segRLs_n tm ((hA_gt (a*2) (b*2))^^4)
    (hA_lt (b+1) (a*2+b+1)) Z3 Z3 1.
Proof.
  intros Ha Hb.
  unfold hA_lt.
  chain4 (Agt_even_000 a b Ha Hb) (Agt_even_101 a b Ha Hb)
    (Agt_even_001 a b Ha Hb) (Agt_even_100 a b Ha Hb).
  all: bclean.
Qed.

Lemma step_even_lt a b:
  a<>O -> b<>O ->
  segRLs_n tm ((hA_lt (a*2) (b*2))^^4)
    (hA_lt (b+1) (a*2+b+1)) Z3 Z3 1.
Proof.
  intros Ha Hb.
  unfold hA_lt.
  chain4 (Alt_even_000 a b Ha Hb) (Alt_even_111 a b Ha Hb)
    (Alt_even_001 a b Ha Hb) (Alt_even_110 a b Ha Hb).
  all: bclean.
Qed.

Lemma step_odd_gt p q:
  segRLs_n tm ((hA_gt (p*2+1) (q*2+1))^^4)
    (hA_gt (p+2*q+3) (p+1)) Z3 Z3 1.
Proof.
  unfold hA_gt.
  chain4 (Agt_odd_000 p q) (Agt_odd_100 p q)
    (Agt_odd_001 p q) (Agt_odd_101 p q).
  all: bclean.
Qed.

Lemma step_odd_lt p q:
  segRLs_n tm ((hA_lt (p*2+1) (q*2+1))^^4)
    (hA_gt (p+2*q+3) (p+1)) Z3 Z3 1.
Proof.
  unfold hA_gt.
  chain4 (Alt_odd_000 p q) (Alt_odd_110 p q)
    (Alt_odd_001 p q) (Alt_odd_111 p q).
  all: bclean.
Qed.

Definition same_parity x y :=
  (exists a b, x=a*2 /\ y=b*2) \/
  (exists a b, x=a*2+1 /\ y=b*2+1).

Lemma same_parity_even_step a b:
  same_parity (b+1) (a*2+b+1).
Proof.
  destruct (mod2 (b+1)); subst.
  - left. exists a0, (a+a0). lia.
  - right. exists a0, (a+a0). lia.
Qed.

Lemma same_parity_odd_step a b:
  same_parity (a+(b*2+1)+2) (a+1).
Proof.
  destruct (mod2 (a+1)); subst.
  - left. exists (a0+b+1), a0. lia.
  - right. exists (a0+b+1), a0. lia.
Qed.

Lemma next_xy_same_parity x y:
  same_parity x y ->
  same_parity (fst (next_xy (x,y))) (snd (next_xy (x,y))).
Proof.
  intros H.
  unfold next_xy.
  destruct (mod2 x); subst x.
  - destruct (mod2 y); subst y.
    + apply same_parity_even_step.
    + destruct H as [[u [v [? ?]]] | [u [v [? ?]]]]; lia.
  - destruct H as [[u [v [? ?]]] | [u [v [? ?]]]].
    + lia.
    + subst y. apply same_parity_odd_step.
Qed.

Lemma xy_same_parity n:
  same_parity (fst (xy n)) (snd (xy n)).
Proof.
  induction n.
  - cbn. left. exists 2%nat,1%nat. lia.
  - cbn. destruct (xy n) as [x y]. cbn in *. apply next_xy_same_parity. exact IHn.
Qed.

Definition positive_xy x y := x<>O /\ y<>O.

Lemma next_xy_positive x y:
  positive_xy x y ->
  positive_xy (fst (next_xy (x,y))) (snd (next_xy (x,y))).
Proof.
  intros [Hx Hy].
  unfold next_xy.
  destruct (mod2 x); subst x.
  - destruct (mod2 y); subst y; cbn; split; lia.
  - cbn; split; lia.
Qed.

Lemma xy_positive n:
  positive_xy (fst (xy n)) (snd (xy n)).
Proof.
  induction n.
  - cbn. split; lia.
  - cbn. destruct (xy n) as [x y]. cbn in *. apply next_xy_positive. exact IHn.
Qed.

Lemma hA_step x y:
  same_parity x y ->
  positive_xy x y ->
  segRLs_n tm ((hA x y)^^4) (hA (fst (next_xy (x,y))) (snd (next_xy (x,y)))) Z3 Z3 1.
Proof.
  intros H [Hx Hy].
  unfold hA, next_xy.
  destruct (mod2 x) as [a|a]; subst x.
  - destruct (mod2 y) as [b|b]; subst y.
    + replace (Nat.ltb (a*2+b+1) (b+1)) with false
        by (symmetry; apply Nat.ltb_ge; lia).
      destruct (Nat.ltb (b*2) (a*2)) eqn:E.
      * applys_eq (step_even_gt a b ltac:(lia) ltac:(lia)); bclean.
      * applys_eq (step_even_lt a b ltac:(lia) ltac:(lia)); bclean.
    + destruct H as [[u [v [? ?]]] | [u [v [? ?]]]]; lia.
  - destruct H as [[u [v [? ?]]] | [u [v [? ?]]]].
    + lia.
    + subst y.
      replace (Nat.ltb (a+1) (a+(v*2+1)+2)) with true
        by (symmetry; apply Nat.ltb_lt; lia).
      destruct (Nat.ltb (v*2+1) (1+a*2)) eqn:E.
      * applys_eq (step_odd_gt a v); bclean.
      * applys_eq (step_odd_lt a v); bclean.
Qed.

Lemma period_step n:
  segRLs_n tm ((period n)^^4) (period (S n)) Z3 Z3 1.
Proof.
  unfold period.
  cbn [xy fst snd].
  destruct (xy n) as [x y] eqn:E.
  cbn [fst snd].
  apply hA_step.
  - pose proof (xy_same_parity n) as H.
    rewrite E in H.
    exact H.
  - pose proof (xy_positive n) as H.
    rewrite E in H.
    exact H.
Qed.

Lemma R_start_segRLs:
  segRLs tm (hP0^^256) (period 0) (zeros 13) (zeros 13).
Proof.
  unfold period, hA, hA_gt, hP0, zeros.
  cbn [xy fst snd Nat.ltb].
  esc.
Qed.

Lemma R_start:
  segRLs_n tm (hP0^^256) (period 0) (zeros 13) (zeros 13) 0.
Proof.
  exact (segRLs_to_segRLs_n_0 R_start_segRLs).
Qed.

Lemma zeros_rect_S n:
  zeros (rect_width (S n)) = zeros (rect_width n)++Z3.
Proof.
  unfold zeros, rect_width, Z3.
  replace (13 + 3 * S n) with (13 + 3*n + 3) by lia.
  rewrite lpow_add.
  reflexivity.
Qed.

Theorem period_rectangle n:
  segRLs_n tm (hP0^^(256 * 4^n)) (period n)
    (zeros (rect_width n)) (zeros (rect_width n)) n.
Proof.
  induction n.
  - cbn [Nat.pow rect_width].
    replace (256 * 1) with 256 by lia.
    apply R_start.
  - pose proof (segRLs_n_concat' (segRLs_n_wall4 IHn) (period_step n)) as Hcat.
    applys_eq Hcat.
    all: try rewrite zeros_rect_S.
    all: try rewrite <- lpow_mul.
    all: cbn [Nat.pow]; flia.
Qed.

Definition hP0':list (DH0*DH0) := [((B,[]),(C,[]));((A,[]),(B,[]));((A,[]),(D,[]))].

Lemma lcons_hP0' n:
  lcons (D,[]) (hP0'^^n) = (hP0^^n,(D,[])).
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Definition LC n := 0inf <* <[1;1;1;0]^^n <* <[1;0].

Lemma LIncs n:
  sideRLs (flip tm) (hP0'^^n) (LC 0) (LC n).
Proof.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans; eauto.
    ut; esx.
Qed.

Lemma pow4_gt n:
  n<4^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=LC 0 {{D}}> 0inf).
  1: esx.
  eapply step_unbounded_nonhalt.
  intros n.
  epose proof (period_rectangle n) as HP1.
  unfold zeros in HP1.
  eapply segRLs_n_sideRLs_n in HP1.
  eapply sideRLs_n_mono with (n0:=n) in HP1.
  2: lia.
  eapply sideRLs_n_sideRLs_concat in HP1.
  2: apply lcons_hP0'.
  2: rewrite lpow_length; cbv - [Nat.mul Nat.pow]; pose proof (pow4_gt n); lia.
  2: apply LIncs.
  rewrite lpow_all0 in HP1.
  2: solve_const0_eq.
  apply HP1.
Qed.

End TM2.



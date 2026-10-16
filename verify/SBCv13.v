From BusyCoq Require Import Individual62 Longitudinal ES_v3 BinaryCounter_v2.
Require Import String List Arith Lia ZifyNat.
Import ListNotations.

(* SBC TM1/TM2, REST3_20261013 numbering. The invariant permits either
   a normal round or two rounds through an interrupted right counter.
   See REST3_SBC12_NONHALTING.txt for the informal derivation. *)
Module Counter.
Section Machine.
Context (tm:TM) (qr ql:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation hR := (qr,<[0]).
Notation hL := (ql,[0]).
Notation h := [(hR,hL)].
Notation w := [1;0;0;1;0].
Notation u := [1;0;0;0;0].
Notation v := [0;0;0;1;0].
Notation z := [1;1;0].
Notation d0 := <[0;1;0;0].
Notation d1 := <[0;1;0;1].
Notation dh := (0inf <* <[1]).
Definition G n r s := sideRLs tm (h^^n) r s.

Definition RC0 a n m := w^^a *> z *> w^^n *> u^^m *> 0inf.
Definition RC1 a m := w^^(a+1) *> v^^m *> 0inf.
Definition RC2 a m := w^^(a+1) *> u^^m *> 0inf.
Lemma RC2_head a m : RC2 a m = w *> w^^a *> u^^m *> 0inf.
Proof. unfold RC2; rewrite Nat.add_comm; reflexivity. Qed.

Record Rules : Prop := {
  rule_wall : segRLs tm (h^^2) (h^^2) w w;
  rule_pair : segRLs tm (h^^6) (h^^2) (z++w++w) (w++w++z);
  rule_R : forall n m, G 6 (RC0 0 (2+n) m) (RC0 2 n (1+m));
  rule_U : forall m, G 4 (RC0 0 0 (1+m)) (RC0 1 0 m);
  rule_odd : forall m, G 2 (RC0 0 1 m) (RC1 0 (1+m));
  rule_V : forall m, G 2 (RC1 0 (1+m)) (RC1 1 m);
  rule_empty : G 4 (RC0 0 0 0) (RC2 1 0);
  rule_grow : forall m, G 2 (RC2 0 m) (RC2 0 (1+m));
  rule_reset : forall k r,
    dh <* d1^^(1+k) {{{ (hL,L) }}} w*>r -->*
    dh <* d0^^k <* d1 <* d0 {{{ (hR,R) }}} z*>r;
  rule_zero : segRL (flip tm) hL hR d0 d1;
  rule_carry : segRR (flip tm) hL hL d1 [1;0;1;0];
  rule_return : segLL (flip tm) hR hR [1;0;1;0] d0
}.
Context (rules:Rules).
Local Notation wall := (rule_wall rules).
Local Notation pair0 := (rule_pair rules).
Local Notation R_step := (rule_R rules).
Local Notation U_step := (rule_U rules).
Local Notation odd_step := (rule_odd rules).
Local Notation V_step := (rule_V rules).
Local Notation empty_step := (rule_empty rules).
Local Notation grow_step := (rule_grow rules).
Local Notation reset := (rule_reset rules).
Local Notation left_zero := (rule_zero rules).
Local Notation left_carry := (rule_carry rules).
Local Notation left_return := (rule_return rules).

Lemma G_add a b r s t : G a r s -> G b s t -> G (a+b) r t.
Proof. unfold G; apply sideRLs_trans_add. Qed.
Lemma G_split a b r t : G (a+b) r t -> exists s, G a r s /\ G b s t.
Proof. unfold G; rewrite lpow_add; apply sideRLs_split. Qed.

Lemma wp n a : segRLs tm (h^^(n*2)) (h^^(n*2)) (w^^a) (w^^a).
Proof.
  induction a; [apply segRLs_nil|].
  cbn[lpow]; eapply segRLs_concat; [|apply IHa].
  rewrite lpow_mul; apply segRLs_wall''; apply wall.
Qed.
Lemma G_w n a r s : G (n*2) r s -> G (n*2) (w^^a*>r) (w^^a*>s).
Proof. intro H; eapply segRLs_sideRLs_concat; [apply wp|exact H]. Qed.

Lemma pair a : segRLs tm (h^^6) (h^^2)
  (z++w^^(2+a)) (w^^2++z++w^^a).
Proof.
  change (segRLs tm (h^^6) (h^^2) ((z++w++w)++w^^a) ((w++w++z)++w^^a)).
  eapply segRLs_concat; [|apply (wp 1 a)]; apply pair0.
Qed.

Lemma peel n a r s : G (n*2) r s ->
  G (n*6) (z*>w^^(n*2+a)*>r) (w^^(n*2)*>z*>w^^a*>s).
Proof.
  gen r s; induction n; intros r s H.
  - inverts H; constructor.
  - destruct (G_split 2 (n*2) r s H) as [t [H2 Hn]].
    eapply G_add with (a:=6%nat) (b:=n*6).
    + unfold G; cbn[lpow app].
      applys_eq (segRLs_sideRLs_concat (pair (n*2+a)) H2); flia.
    + applys_eq (G_w (n*3) 2); flia.
      applys_eq (IHn _ _ Hn); flia.
Qed.

Lemma R_steps k a n m :
  G (k*6) (RC0 a (k*2+n) m) (RC0 (a+k*2) n (m+k)).
Proof.
  gen a n m; induction k; intros.
  - rewrite !Nat.add_0_r; constructor.
  - eapply G_add with (a:=6%nat) (b:=k*6) (s:=RC0 (a+2) (k*2+n) (1+m)).
    + applys_eq (G_w 3 a _ _ (R_step (k*2+n) m)); unfold RC0; st; flia.
    + applys_eq (IHk (a+2) n (1+m)); flia.
Qed.
Lemma U_steps k a m : G (k*4) (RC0 a 0 (k+m)) (RC0 (a+k) 0 m).
Proof.
  gen a m; induction k; intros.
  - rewrite !Nat.add_0_r; constructor.
  - eapply G_add with (a:=4%nat) (b:=k*4) (s:=RC0 (a+1) 0 (k+m)).
    + applys_eq (G_w 2 a _ _ (U_step (k+m))); unfold RC0; st; flia.
    + applys_eq (IHk (a+1) m); flia.
Qed.
Lemma V_steps k a m : G (k*2) (RC1 a (k+m)) (RC1 (a+k) m).
Proof.
  gen a m; induction k; intros.
  - rewrite !Nat.add_0_r; constructor.
  - eapply G_add with (a:=2%nat) (b:=k*2) (s:=RC1 (a+1) (k+m)).
    + applys_eq (G_w 1 a _ _ (V_step (k+m))); unfold RC1; st; flia.
    + applys_eq (IHk (a+1) m); flia.
Qed.
Lemma grow k a m : G (k*2) (RC2 a m) (RC2 a (m+k)).
Proof.
  gen m; induction k; intros.
  - rewrite !Nat.add_0_r; constructor.
  - eapply G_add with (a:=2%nat) (b:=k*2) (s:=RC2 a (1+m)).
    + applys_eq (G_w 1 a _ _ (grow_step m)); unfold RC2; st; flia.
    + applys_eq (IHk (1+m)); flia.
Qed.

Lemma normal_odd a n m t :
  G (n*8+m*2+4+t*2) (RC0 a (n*2+1) m) (RC2 (a+1+n*3+m) t).
Proof.
  replace (n*8+m*2+4+t*2) with (n*6+(2+((1+m+n)*2+t*2))) by lia.
  eapply G_add; [apply R_steps|].
  eapply G_add with (s:=RC1 (a+n*2) (1+m+n)).
  - applys_eq (G_w 1 (a+n*2) _ _ (odd_step (m+n))); unfold RC0,RC1; st; flia.
  - eapply G_add with (s:=RC1 (a+n*2+(1+m+n)) 0).
    + applys_eq (V_steps (1+m+n) (a+n*2) 0); flia.
    + change (G (t*2) (RC2 (a+n*2+(1+m+n)) 0) (RC2 (a+1+n*3+m) t)).
      applys_eq (grow t (a+1+n*3+m) 0); flia.
Qed.
Lemma normal_even a n m t :
  G (n*10+m*4+4+t*2) (RC0 a (n*2) m) (RC2 (a+1+n*3+m) t).
Proof.
  replace (n*10+m*4+4+t*2) with (n*6+((m+n)*4+(4+t*2))) by lia.
  eapply G_add.
  - applys_eq (R_steps n a 0 m); flia.
  - eapply G_add.
    + applys_eq (U_steps (m+n) (a+n*2) 0); flia.
    + eapply G_add with (s:=RC2 (a+n*2+(m+n)+1) 0).
      * applys_eq (G_w 2 (a+n*2+(m+n)) _ _ empty_step); unfold RC0,RC2; st; flia.
      * applys_eq (grow t (a+1+n*3+m) 0); flia.
Qed.

Ltac known_shift := first [apply left_zero|apply left_carry|apply left_return].

Lemma LIncs n :
  sideRLs (flip tm) ([(hL,hR)]^^((2^n-1)*2*2+1))
    (dh <* d0^^n <* d1 <* d0) (dh <* d1^^n <* d1 <* d1).
Proof.
  eapply segRLs_sideRLs_concat; [eapply BC.Incs'| ..].
  all: try known_shift.
  eapply segRLs_sideRLs_concat; [eapply BC.Mul2| ..].
  all: try known_shift.
  eapply segRLs_sideRLs_concat; [eapply BC.Incs| ..].
  all: try known_shift.
  constructor.
Qed.

Definition Cfg k r := dh <* d0^^k <* d1 <* d0 {{{ (hR,R) }}} r.
Definition S k n m := Cfg k (RC0 0 n m).

Lemma lrcons_same h1 h2 n :
  lrcons h1 ([(h2,h1)]^^n) h2 = [(h1,h2)]^^(n+1).
Proof. applys_eq lrcons_lpow1; flia. Qed.

Lemma reset2 k r :
  dh <* d1^^(2+k) {{{ (hL,L) }}} w*>r -->* Cfg (k+1) (z*>r).
Proof. unfold Cfg; applys_eq (reset (k+1) r); flia. Qed.

Lemma round k n r s : n+2=2^k*4 -> G n r (w*>s) ->
  Cfg k r -->+ Cfg (k+1) (z*>s).
Proof.
  intros Hn H; unfold Cfg at 1.
  eapply progress_evstep_trans.
  - eapply (sideRLs_concat (LIncs k)).
    rewrite lrcons_same; applys_eq H; flia.
  - applys_eq (reset2 k s); st; flia.
Qed.

Definition need n m (odd:bool) := if odd then n*8+m*2+4 else n*10+m*4+4.
Lemma normal a n m odd t :
  G (need n m odd+t*2) (RC0 a (n*2+if odd then 1 else 0) m)
    (RC2 (a+1+n*3+m) t).
Proof.
  destruct odd; [apply normal_odd|].
  applys_eq normal_even; flia.
Qed.

Lemma normal_round k n m odd t : need n m odd+t*2+2=2^k*4 ->
  S k (n*2+if odd then 1 else 0) m -->+ S (k+1) (1+n*3+m) t.
Proof.
  intro H; unfold S; unfold RC0 at 2; cbn[lpow Str_app].
  apply round with (n:=need n m odd+t*2); [exact H|].
  rewrite <-RC2_head; applys_eq (normal 0 n m odd t); flia.
Qed.

Lemma recovery_budget T a m b e c q r d v s :
  4<=T -> a*2+m+2<=T -> e<=1 -> r<=1 -> s<=1 ->
  a*3+b*2+e+1=T*2 -> m+a=b+c -> a*2+b=1+q*2+r ->
  q+e=c*2+2+d -> v*2+s=r+c+2 -> q*3+v*5+d*2+3<=T*4.
Proof. intros; lia. Qed.

Lemma recovery k a b c e q r d n (odd:bool) t m :
  a*6+b*4+e*2+2=2^k*4 -> m+a=b+c -> a*2+b=1+q*2+r ->
  c*4+4+d*2=(e+q)*2 -> r+c+2=n*2+(if odd then 1 else 0) ->
  q*6+need n d odd+t*2+2=2^(k+1)*4 ->
  S k (a*2) m -->+ S (k+2) (q*2+1+n*3+d) t.
Proof.
  intros Hclock Hzero Hprefix Htail Hparity Hclock2.
  assert (H: G (e*2+q*2) (RC0 0 0 c) (RC2 (c+1) d)).
  { applys_eq (normal_even 0 0 c d); flia. }
  destruct (G_split (e*2) (q*2) _ _ H) as [X [He Hq]].
  eapply progress_trans with (c':=Cfg (k+1) (z*>w^^(q*2+r)*>X)).
  - unfold S; apply round with (n:=a*6+(b*4+e*2)); [lia|].
    eapply G_add.
    + applys_eq (R_steps a 0 0 m); flia.
    + eapply G_add with (s:=RC0 (a*2+b) 0 c).
      * applys_eq (U_steps b (a*2) c); flia.
      * applys_eq (G_w e (a*2+b) _ _ He); rewrite Hprefix; unfold RC0; st; flia.
  - unfold S; unfold RC0 at 1; cbn[lpow Str_app].
    replace (k+2) with ((k+1)+1) by lia.
    apply round with (n:=q*6+(need n d odd+t*2)); [lia|].
    rewrite <-RC2_head.
    eapply G_add with (s:=RC0 (q*2) (r+c+2) d).
    + applys_eq (peel q r _ _ Hq); unfold RC0,RC2; st; flia.
    + applys_eq (normal (q*2) n d odd t); flia.
Qed.

Lemma recovery_safe k a b c e q r d n (odd:bool) m :
  a*6+b*4+e*2+2=2^k*4 -> m+a=b+c -> a*2+b=1+q*2+r ->
  c*4+4+d*2=(e+q)*2 -> r+c+2=n*2+(if odd then 1 else 0) ->
  q*3+n*5+d*2+3<=2^k*4 ->
  exists N M, S k (a*2) m -->+ S (k+2) N M /\ N+M+2<=2^(k+2).
Proof.
  intros Hclock Hzero Hprefix Htail Hparity Hbudget.
  set (h:=if odd then n*4+d+2 else n*5+d*2+2).
  assert (Hneed:need n d odd=h*2) by (unfold need,h; destruct odd; lia).
  assert (Hb:q*3+h+1<=2^k*4) by (unfold h; destruct odd; lia).
  set (t:=2^k*4-q*3-h-1).
  assert (Ht:q*3+h+t+1=2^k*4) by (unfold t; lia).
  exists (q*2+1+n*3+d),t; split.
  - eapply (recovery k a b c e q r d n odd t m); try assumption.
    rewrite Nat.pow_add_r; cbn[Nat.pow]; lia.
  - unfold h in Ht; destruct odd; rewrite Nat.pow_add_r; cbn[Nat.pow]; lia.
Qed.

Lemma closed k n m : 2<=k -> n+m+2<=2^k ->
  exists k' n' m', S k n m -->+ S k' n' m' /\ 2<=k' /\ n'+m'+2<=2^k'.
Proof.
  intros Hk Hsum.
  set (T:=2^k).
  assert (HT:4<=T).
  { unfold T; change (2^2<=2^k); apply Nat.pow_le_mono_r; lia. }
  set (a:=n/2).
  assert (Hn:n=a*2+n mod 2) by (unfold a; lia).
  assert (Hm:n mod 2<=1) by lia.
  clearbody a.
  destruct (n mod 2) as [|[|s]]; [| |lia].
  - destruct (le_dec (a*5+m*2+3) (T*2)) as [Hgood|Hbad].
    + set (t:=T*2-a*5-m*2-3).
      exists (k+1),(1+a*3+m),t; split.
      * replace n with (a*2+0) by lia; apply (normal_round k a m false t).
        unfold need,t; fold T; lia.
      * split; [lia|].
        rewrite Nat.pow_add_r; cbn[Nat.pow]; fold T; unfold t; lia.
    + set (D:=T*2-1-a*3).
      set (b:=D/2); set (e:=D mod 2).
      assert (Hfirst:a*3+b*2+e+1=T*2 /\ e<=1) by (unfold b,e,D; fold T in Hsum; lia).
      clearbody b e; clear D.
      set (c:=m+a-b).
      assert (Hzero:m+a=b+c) by (unfold c; fold T in Hsum; lia).
      clearbody c.
      set (q:=(a*2+b-1)/2); set (r:=(a*2+b-1) mod 2).
      assert (Hprefix:a*2+b=1+q*2+r /\ r<=1) by (unfold q,r; fold T in Hsum; lia).
      clearbody q r.
      set (d:=q+e-c*2-2).
      assert (Htail:q+e=c*2+2+d) by (unfold d; fold T in Hsum; lia).
      clearbody d.
      set (v:=(r+c+2)/2); set (s:=(r+c+2) mod 2).
      assert (Hdiv:v*2+s=r+c+2 /\ s<=1) by (unfold v,s; lia).
      clearbody v s.
      assert (Hbudget:q*3+v*5+d*2+3<=T*4).
      { eapply (recovery_budget T a m b e c q r d v s); fold T in Hsum; lia. }
      set (odd:=Nat.eqb s 1).
      assert (Hparity:r+c+2=v*2+(if odd then 1 else 0)).
      { unfold odd; destruct (Nat.eqb s 1) eqn:E.
        - apply Nat.eqb_eq in E; lia.
        - apply Nat.eqb_neq in E; lia. }
      edestruct (recovery_safe k a b c e q r d v odd m) as [N [M [Hs HI]]]; fold T; try lia.
      exists (k+2),N,M; split; [applys_eq Hs; flia|split; [lia|exact HI]].
  - set (t:=T*2-a*4-m-3).
    exists (k+1),(1+a*3+m),t; split.
    + replace n with (a*2+1) by lia; apply (normal_round k a m true t).
      unfold need,t; fold T in Hsum |- *; lia.
    + split; [lia|].
      rewrite Nat.pow_add_r; cbn[Nat.pow]; fold T in Hsum |- *; unfold t; lia.
Qed.

Lemma nonhalt_at k n m : 2<=k -> n+m+2<=2^k -> ~halts tm (S k n m).
Proof.
  intros Hk Hsum; eapply progress_nonhalt_cond with (i0:=(k,n,m))
    (C:=fun '(k,n,m) => S k n m)
    (P:=fun '(k,n,m) => 2<=k /\ n+m+2<=2^k).
  - intros [[k0 n0] m0] [Hk0 Hsum0].
    destruct (closed k0 n0 m0 Hk0 Hsum0) as [k' [n' [m' [Hrun HI]]]].
    exists (k',n',m'); auto.
  - auto.
Qed.

End Machine.

Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
Ltac solve_rules :=
  let n:=fresh "n" in let m:=fresh "m" in let k:=fresh "k" in
  let l:=fresh "l" in let r:=fresh "r" in
  constructor;
  [ finite_rule
  | finite_rule
  | intros n m; destruct m as [|m];
    [ unfold G,RC0; es' n
    | replace (Datatypes.S m) with (1+m) by lia; unfold G,RC0; es' n m ]
  | intro m; unfold G,RC0; es' m
  | intro m; unfold G,RC0,RC1; es' m
  | intro m; unfold G,RC1; es' m
  | unfold G,RC0,RC2; esx
  | intro m; destruct m as [|m];
    [ unfold G,RC2; esx
    | replace (Datatypes.S m) with (1+m) by lia; unfold G,RC2; es' m ]
  | intros k r; cbn[to_DH_config]; es' k & r
  | intros l r; cbn[to_DH_config]; es' & l r
  | intros l r; cbn[to_DH_config]; es' & l r
  | intros l r; cbn[to_DH_config]; es' & l r ].
End Counter.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC---").
Lemma rules: Counter.Rules tm C A.
Proof. Counter.solve_rules. Qed.
Lemma init: c0 -[tm]->* Counter.S C 4 6 7.
Proof. unfold Counter.S,Counter.Cfg,Counter.RC0; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply (Counter.nonhalt_at tm C A rules); cbn; lia.
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA").
Lemma rules: Counter.Rules tm B E.
Proof. Counter.solve_rules. Qed.
Lemma init: c0 -[tm]->* Counter.S B 4 6 5.
Proof. unfold Counter.S,Counter.Cfg,Counter.RC0; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply (Counter.nonhalt_at tm B E rules); cbn; lia.
Qed.
End TM2.

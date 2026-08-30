From Coq Require Import Arith.PeanoNat Lia.
Require Import Bool.
From BusyCoq Require Import Individual62.

Require Import ZArith ZifyNat Lia.
Require Import String.
Require Import List.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_---1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* <[0;1]^^a <{{D}} [0;1]^^b *> [1]^^c *> 0inf.

Definition S2 a b c d :=
  0inf <* <[0;1]^^a <{{D}} [0;1]^^b *> [1]^^c *> [0;1;0] *> [1]^^d *> 0inf.

Close Scope sym.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (2+b) c.
Proof.
  esx.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Inc2 a b c d:
  S2 (1+a) b (2+c) d -->*
  S2 a (2+b) c d.
Proof.
  esx.
Qed.

Lemma Incs2 n a b c d:
  S2 (n+a) b (n*2+c) d -->*
  S2 a (n*2+b) c d.
Proof.
  gen a b c.
  ind n Inc2.
Qed.

Lemma ROv2 a b d:
  S2 a b 0 (1+d) -->*
  S1 a (2+b) d.
Proof.
  esx.
Qed.

Lemma LOv1 b c:
  S1 0 b (1+c) -->*
  S1 (1+b) 0 (1+c).
Proof.
  esx.
Qed.

Lemma LOv2 b c d:
  S2 0 b (1+c) d -->*
  S2 (1+b) 0 (1+c) d.
Proof.
  esx.
Qed.

Lemma ROv1_1 a b:
  S1 (1+a) b 1 -->*
  S1 a (1+b) 0.
Proof.
  esx.
Qed.

Lemma ROv1_0 a b:
  S1 (4+a) b 0 -->*
  S2 1 0 (2+a*2) (4+b*2).
Proof.
  esx.
Qed.

Lemma init:
  c0 -->*
  S2 1 0 64 20.
Proof.
  unfold S2.
  esx.
Qed.

Lemma Incs2LOv2 a c d:
  1+a*2<=c ->
  S2 a 0 c d -->*
  S2 (1+a*2) 0 (c-a*2) d.
Proof.
  intros.
  follow (Incs2 a 0 0 (1+(c-(1+a*2))) d).
  follow LOv2.
  finish.
Qed.

Lemma Incs2LOv1 a c d:
  c mod 2 = 0 ->
  c<=a*2 ->
  S2 a 0 c (1+d) -->*
  S1 (a-c/2) (2+c) d.
Proof.
  intros.
  follow (Incs2 (c/2) (a-c/2) 0 0 (1+d)).
  follow ROv2.
  finish.
Qed.

Lemma Incs1LOv1 a b c:
  1+a*2<=c ->
  S1 a b c -->*
  S1 (1+a*2+b) 0 (c-a*2).
Proof.
  intros.
  follow (Incs1 a 0 b (1+(c-(1+a*2)))).
  follow LOv1.
  finish.
Qed.

Lemma pow2_gt i:
  i<2^i.
Proof.
  induction i; cbn; lia.
Qed.

Lemma Incs2LOv2s i c d:
  2^i*4-i*2-3<=c ->
  S2 1 0 c d -->*
  S2 (2^i*2-1) 0 (c-(2^i*4-i*2-4)) d.
Proof.
  gen c.
  induction i; intros.
  1: finish.
  cbn[Nat.pow] in *.
  epose proof (pow2_gt i).
  follow IHi.
  1: lia.
  follow Incs2LOv2.
  1: lia.
  finish.
Qed.

Lemma Incs2LOv2s1 i c d:
  2^i*4-i*2-3 <= c < 2^(S i)*4-(S i)*2-3 ->
  c mod 2 = 0 ->
  S2 1 0 c (1+d) -->*
  S1 (2^i*4-i-3-c/2) (3+(c-(2^i*4-i*2-3))) d.
Proof.
  intros.
  cbn[Nat.pow] in *.
  follow (Incs2LOv2s i).
  1: lia.
  follow Incs2LOv1.
  1,2: lia.
  pose proof (pow2_gt i).
  finish.
Qed.

Lemma Incs2LOv2s1' i c d:
  2^i*4-i*2-3 <= c < 2^(S i)*4-(S i)*2-3 ->
  c mod 2 = 0 ->
  2^i*8-i*2-5<=c+d ->
  S2 1 0 c (1+d) -->*
  S1 (2^i*4+1) 0 (c+d-(2^i*8-i*2-6)).
Proof.
  intros.
  follow Incs2LOv2s1.
  pose proof (pow2_gt i).
  cbn[Nat.pow] in *.
  follow Incs1LOv1.
  1: lia.
  finish.
Qed.



Lemma S2_1_S1_neq a b c d e:
  2 <= a ->
  S2 1 0 c d <> S1 a b e.
Proof.
  intros Ha HE.
  replace a with (2+(a-2)) in HE by lia.
  unfold S1, S2 in HE.
  apply (f_equal (fun z =>
    Streams.hd (Streams.tl (fst (fst (snd z)))))) in HE.
  cbn [lpow Str_app] in HE.
  rewrite const_unfold in HE.
  discriminate.
Qed.

Lemma Incs1LOv1s n a c:
  2*(a+1)*(2^n-1)-2*n+1 <= c ->
  S1 a 0 c -->*
  S1 ((a+1)*2^n-1) 0
    (c-(2*(a+1)*(2^n-1)-2*n)).
Proof.
  gen a c.
  induction n; intros.
  1: cbn; finish.
  cbn [Nat.pow] in *.
  pose proof (pow2_gt n).
  follow IHn.
  1: nia.
  follow Incs1LOv1.
  1: apply Nat.le_add_le_sub_l; nia.
  replace ((a+1)*(2*2^n)-1)
    with (1+((a+1)*2^n-1)*2+0) by nia.
  replace (c-(2*(a+1)*(2*2^n-1)-2*S n))
    with (c-(2*(a+1)*(2^n-1)-2*n)-((a+1)*2^n-1)*2).
  1: finish.
  rewrite <-Nat.sub_add_distr.
  f_equal; nia.
Qed.

Lemma S1_finish a b q:
  q+5 <= a ->
  S1 a b (q*2+1) -->*
  S2 1 0 (a*2-q*2-8) (b*2+q*4+6).
Proof.
  intros.
  follow (Incs1 q (a-q) b 1).
  follow (ROv1_1 (a-q-1) (q*2+b)).
  follow (ROv1_0 (a-q-5) (1+(q*2+b))).
  replace (a*2-q*2-8) with (2+(a-q-5)*2) by flia.
  replace (b*2+q*4+6) with (4+(1+(q*2+b))*2) by nia.
  finish.
Qed.

Lemma EventF i c d q:
  2^i*4-i*2-3 <= c < 2^(S i)*4-(S i)*2-3 ->
  c mod 2 = 0 ->
  d = q*2+1 ->
  q+5 <= 2^i*4-i-3-c/2 ->
  S2 1 0 c (1+d) -->*
  S2 1 0
    ((2^i*4-i-3-c/2)*2-q*2-8)
    ((3+(c-(2^i*4-i*2-3)))*2+q*4+6).
Proof.
  intros; subst d.
  follow Incs2LOv2s1.
  follow S1_finish.
  finish.
Qed.

Lemma EventF_progress i c d q:
  1 <= i ->
  2^i*4-i*2-3 <= c < 2^(S i)*4-(S i)*2-3 ->
  c mod 2 = 0 ->
  d = q*2+1 ->
  q+5 <= 2^i*4-i-3-c/2 ->
  S2 1 0 c (1+d) -->+
  S2 1 0
    ((2^i*4-i-3-c/2)*2-q*2-8)
    ((3+(c-(2^i*4-i*2-3)))*2+q*4+6).
Proof.
  intros; subst d.
  eapply progress_evstep_trans.
  1: eapply evstep_progress.
     1: apply Incs2LOv2s1; eauto.
     apply S2_1_S1_neq; lia.
  follow S1_finish.
  finish.
Qed.

Lemma EventT i j c d q:
  2^i*4-i*2-3 <= c < 2^(S i)*4-(S i)*2-3 ->
  c mod 2 = 0 ->
  2^i*8-i*2-5 <= c+d ->
  (2*((2^i*4+1)+1)*(2^j-1)-2*j) + (q*2+1) =
    c+d-(2^i*8-i*2-6) ->
  q+5 <= ((2^i*4+1)+1)*2^j-1 ->
  S2 1 0 c (1+d) -->*
  S2 1 0
    ((((2^i*4+1)+1)*2^j-1)*2-q*2-8)
    (q*4+6).
Proof.
  intros.
  follow Incs2LOv2s1'.
  follow (Incs1LOv1s j (2^i*4+1)
    (c+d-(2^i*8-i*2-6))).
  1: flia.
  replace
    (c+d-(2^i*8-i*2-6)-
       (2*((2^i*4+1)+1)*(2^j-1)-2*j))
    with (q*2+1) by flia.
  follow (S1_finish (((2^i*4+1)+1)*2^j-1) 0 q).
  finish.
Qed.

Definition L i := 2^i*4-i*2-3.
Definition LH i := 2^i*2-i-2.
Definition UH i := 2^i*4-i-4.
Definition Far i p := 2^(p+2)+i+p+3 <= 2^i.

Lemma bucket_adj i: UH i+1 = LH (S i).
Proof.
  unfold UH, LH.
  pose proof (pow2_gt i).
  cbn [Nat.pow].
  flia.
Qed.

Lemma half_bucket i x:
  LH i <= x <= UH i ->
  L i <= x*2+2 < L (S i).
Proof.
  unfold LH, UH, L; intros.
  pose proof (pow2_gt i).
  cbn [Nat.pow].
  flia.
Qed.

Definition A (i j:nat) := (2^i*4+1+1)*2^j-1.
Definition B (i j:nat) := (2^i*4+1+1)*2^j.

Lemma B_expand i j:
  B i j = 4*2^(i+j)+2^(j+1).
Proof.
  unfold B.
  rewrite Nat.pow_add_r.
  replace (j+1) with (S j) by lia.
  cbn [Nat.pow].
  nia.
Qed.

Lemma B_level s p:
  p <= s ->
  B (s-p) p = 4*2^s+2^(p+1).
Proof.
  intros H.
  rewrite B_expand.
  replace (s-p+p) with s by lia.
  reflexivity.
Qed.

Lemma UH_B i j k:
  k <= i+j ->
  UH k+6 <= B i j.
Proof.
  intros H.
  pose proof (Nat.pow_le_mono_r 2 k (i+j) ltac:(lia) H).
  pose proof (pow2_gt k).
  assert (UH k+6 <= 2^k*4+2).
  { unfold UH. flia. }
  pose proof (pow2_gt (j+1)).
  rewrite B_expand.
  lia.
Qed.

Lemma plus6_minus1 x: x*4+6-1 = x*4+5.
Proof. lia. Qed.

Lemma sub_scale6 b x:
  x+6 <= b ->
  (b-1)*2-(b-x-6)*2-8 = x*2+2.
Proof.
  intros H.
  rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add (x+6) b H).
  nia.
Qed.

Lemma sub6_plus5_le b x:
  x+6 <= b -> b-x-6+5 <= b-1.
Proof. lia. Qed.

Lemma u_input_expand b x:
  x+6 <= b ->
  (x*2+2+(b-x-6)*4+5)+x*2+17 = b*4.
Proof.
  intros H.
  rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add (x+6) b H).
  nia.
Qed.

Lemma u_lower p r i j bp bc x y:
  i < p -> j < r -> bc=(p*4+2)*r ->
  x+6<=bp -> y+6<=bc ->
  x+bc*2=y+bp*2+i+j+2 ->
  p*8-i*2-5 <= x*2+2+((bp-x-6)*4+5).
Proof.
  intros Hi Hj Hbc Hx Hy Hxy.
  pose proof (u_input_expand bp x Hx).
  assert (8*p+2*j+4 <= 2*bc).
  { subst bc. nia. }
  lia.
Qed.

Lemma u_q_expand b x:
  x+6 <= b ->
  (b-x-6)*2+1+x*2+11 = b*2.
Proof.
  intros H.
  rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add (x+6) b H).
  nia.
Qed.

Lemma u_t_expand p i:
  i < p ->
  (p*8-i*2-6)+i*2+6 = p*8.
Proof.
  intros H.
  rewrite <-Nat.sub_add_distr, <-Nat.add_assoc.
  apply Nat.sub_add; lia.
Qed.

Lemma u_d_expand p r i j b:
  i < p -> j < r -> b=(p*4+2)*r ->
  (2*(p*4+2)*(r-1)-2*j)+2*j+p*8+4 = b*2.
Proof.
  intros Hi Hj ->.
  rewrite Nat.sub_add by nia.
  pose proof (Nat.sub_add 1 r ltac:(lia)).
  nia.
Qed.

Lemma u_residual p r i j bp bc x y:
  i < p -> j < r -> bc=(p*4+2)*r ->
  x+6 <= bp -> y+6 <= bc ->
  p*8-i*2-6 <= x*2+2+(bp-x-6)*4+5 ->
  x+bc*2 = y+bp*2+i+j+2 ->
  (2*(p*4+2)*(r-1)-2*j)+((bc-y-6)*2+1) =
    x*2+2+((bp-x-6)*4+5)-(p*8-i*2-6).
Proof.
  intros Hi Hj Hbc Hx Hy HT Hxy.
  pose proof (u_input_expand bp x Hx).
  pose proof (u_q_expand bc y Hy).
  pose proof (u_t_expand p i Hi).
  pose proof (u_d_expand p r i j bc Hi Hj Hbc).
  apply Nat.add_cancel_r with (p:=p*8-i*2-6).
  rewrite Nat.sub_add by lia.
  lia.
Qed.

Definition UC (i j x:nat) := x*2+2.
Definition UD (i j x:nat) := (B i j-x-6)*4+6.
Definition US (i j x:nat) := S2 1 0 (UC i j x) (UD i j x).

Definition Q (n k b:nat) :=
  US (n-k-1) k (2^(n+1)+2^(k+1)-b-1).

Definition QR (n k b:nat) :=
  S2 1 0 ((2^(n+1)+2^(k+1)-b)*2) ((b-5)*4+6).

Lemma Q_eq n k b:
  k+1 <= n ->
  5 <= b ->
  b+1 <= 2^(n+1)+2^(k+1) ->
  Q n k b = QR n k b.
Proof.
  intros Hk Hb Hsub.
  unfold Q, QR, US, UC, UD.
  assert (B (n-k-1) k=2^(n+1)+2^(k+1)) as HB.
  { rewrite B_expand.
    replace (n-k-1+k) with (n-1) by lia.
    assert (2^(n+1)=4*2^(n-1)).
    { replace (n+1) with ((n-1)+2) by lia.
      rewrite Nat.pow_add_r; cbn; nia. }
    lia. }
  rewrite HB.
  pose proof (Nat.sub_add (b+1)
    (2^(n+1)+2^(k+1)) Hsub).
  pose proof (Nat.sub_add 5 b Hb).
  f_equal; nia.
Qed.

Lemma Q_B n k b:
  k+1 <= n ->
  5 <= b ->
  b+1 <= 2^(n+1)+2^(k+1) ->
  2^(n+1)+2^(k+1)-b-1+6 <= B (n-k-1) k.
Proof.
  intros Hk Hb Hsub.
  rewrite B_expand.
  replace (n-k-1+k) with (n-1) by lia.
  replace n with (S (n-1)) at 2 by lia.
  cbn [Nat.pow].
  replace (k+1) with (S k) by lia.
  cbn [Nat.pow].
  replace (S (n-1)-1) with (n-1) by lia.
  assert (2^(n+1)=4*2^(n-1)) as HP.
  { replace (n+1) with ((n-1)+2) by lia.
    rewrite Nat.pow_add_r; cbn; nia. }
  rewrite <-HP.
  replace (k+1) with (S k) in Hsub by lia.
  cbn [Nat.pow] in Hsub.
  pose proof (Nat.sub_add (b+1)
    (2^(n+1)+2^k*2) ltac:(nia)).
  nia.
Qed.

Lemma U_next_raw ip jp x i j y:
  x+6 <= B ip jp ->
  y+6 <= B i j ->
  L i <= UC ip jp x < L (S i) ->
  2^i*8-i*2-5 <= UC ip jp x+(UD ip jp x-1) ->
  (2*(2^i*4+1+1)*(2^j-1)-2*j)+
      ((B i j-y-6)*2+1) =
    UC ip jp x+(UD ip jp x-1)-(2^i*8-i*2-6) ->
  US ip jp x -->* US i j y.
Proof.
  unfold US, UC, UD, L; intros Hx Hy Hc Hl Hr.
  pose proof (Nat.Div0.mod_mul (x+1) 2).
  assert (Hl': 2^i*8-i*2-5 <=
    x*2+2+((B ip jp-x-6)*4+5)).
  { rewrite plus6_minus1 in Hl. exact Hl. }
  assert (Hr':
    (2*(2^i*4+1+1)*(2^j-1)-2*j)+
        ((B i j-y-6)*2+1) =
      x*2+2+((B ip jp-x-6)*4+5)-(2^i*8-i*2-6)).
  { rewrite plus6_minus1 in Hr. exact Hr. }
  follow (EventT i j (x*2+2)
    ((B ip jp-x-6)*4+5)
    (B i j-y-6)).
  1: replace (x*2+2) with ((x+1)*2) by nia; assumption.
  1: unfold B; apply sub6_plus5_le; exact Hy.
  fold (B i j).
  rewrite (sub_scale6 (B i j) y Hy).
  finish.
Qed.

Lemma U_next_diag ip jp x i j y:
  x+6 <= B ip jp ->
  y+6 <= B i j ->
  L i <= UC ip jp x < L (S i) ->
  2^i*8-i*2-5 <= UC ip jp x+(UD ip jp x-1) ->
  x+(B i j)*2 = y+(B ip jp)*2+i+j+2 ->
  US ip jp x -->* US i j y.
Proof.
  intros Hx Hy Hc Hl Hxy.
  apply U_next_raw; auto.
  assert (HB: B i j=(2^i*4+2)*2^j).
  { unfold B; replace (2^i*4+1+1) with (2^i*4+2) by lia; reflexivity. }
  assert (HT: 2^i*8-i*2-6 <=
    x*2+2+(B ip jp-x-6)*4+5).
  { unfold UC, UD in Hl. rewrite plus6_minus1 in Hl. lia. }
  pose proof (pow2_gt i).
  pose proof (pow2_gt j).
  pose proof (u_residual (2^i) (2^j) i j
    (B ip jp) (B i j) x y H H0 HB Hx Hy HT Hxy) as Hr.
  unfold UC, UD.
  rewrite plus6_minus1.
  replace (2^i*4+1+1) with (2^i*4+2) by lia.
  exact Hr.
Qed.

Lemma U_next ip jp x i j y:
  x+6 <= B ip jp ->
  y+6 <= B i j ->
  LH i <= x <= UH i ->
  x+(B i j)*2 = y+(B ip jp)*2+i+j+2 ->
  US ip jp x -->* US i j y.
Proof.
  intros Hx Hy Hc Hxy.
  apply U_next_diag.
  - exact Hx.
  - exact Hy.
  - apply half_bucket; exact Hc.
  - unfold UC, UD. rewrite plus6_minus1.
    apply (u_lower (2^i) (2^j) i j
      (B ip jp) (B i j) x y); auto using pow2_gt.
    unfold B; replace (2^i*4+1+1) with (2^i*4+2) by lia; reflexivity.
  - exact Hxy.
Qed.

Lemma U_same i j x:
  i+j+2 <= x ->
  x+6 <= B i j ->
  LH i <= x <= UH i ->
  US i j x -->* US i j (x-(i+j+2)).
Proof.
  intros Hx HB HC.
  apply U_next; auto.
  - eapply Nat.le_trans.
    2: exact HB.
    apply Nat.add_le_mono_r, Nat.le_sub_l.
  - pose proof (Nat.sub_add (i+j+2) x Hx).
    lia.
Qed.

Lemma U_up s p x:
  p+1 <= s ->
  s+2 <= x+2^(p+2) ->
  x+6 <= B (s-p) p ->
  x+2^(p+2)-(s+2)+6 <= B (s-(p+1)) (p+1) ->
  LH (s-(p+1)) <= x <= UH (s-(p+1)) ->
  US (s-p) p x -->*
  US (s-(p+1)) (p+1) (x+2^(p+2)-(s+2)).
Proof.
  intros Hp Hsub Hx Hy HC.
  apply U_next; auto.
  rewrite (B_level s p) by lia.
  rewrite (B_level s (p+1)) by lia.
  pose proof (Nat.sub_add (s+2) (x+2^(p+2)) Hsub).
  pose proof (Nat.sub_add (p+1) s Hp).
  assert (2^(p+2)=2*2^(p+1)).
  { replace (p+2) with (S (p+1)) by lia. cbn [Nat.pow]. nia. }
  assert (2^(p+1+1)=2*2^(p+1)).
  { replace (p+1+1) with (S (p+1)) by lia. cbn [Nat.pow]. nia. }
  lia.
Qed.

Lemma U_down s p x:
  p+1 <= s ->
  2^(p+2)+s+2 <= x ->
  x+6 <= B (s-(p+1)) (p+1) ->
  x-2^(p+2)-(s+2)+6 <= B (s-p) p ->
  LH (s-p) <= x <= UH (s-p) ->
  US (s-(p+1)) (p+1) x -->*
  US (s-p) p (x-2^(p+2)-(s+2)).
Proof.
  intros Hp Hsub Hx Hy HC.
  apply U_next; auto.
  rewrite (B_level s p) by lia.
  rewrite (B_level s (p+1)) by lia.
  rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add (2^(p+2)+s+2) x Hsub).
  pose proof (Nat.sub_add (p+1) s Hp).
  assert (2^(p+2)=2*2^(p+1)).
  { replace (p+2) with (S (p+1)) by lia. cbn [Nat.pow]. nia. }
  assert (2^(p+1+1)=2*2^(p+1)).
  { replace (p+1+1) with (S (p+1)) by lia. cbn [Nat.pow]. nia. }
  lia.
Qed.

Lemma U_up_i i p x:
  1 <= i ->
  i+p+2 <= x+2^(p+2) ->
  x+6 <= B i p ->
  x+2^(p+2)-(i+p+2)+6 <= B (i-1) (p+1) ->
  LH (i-1) <= x <= UH (i-1) ->
  US i p x -->*
  US (i-1) (p+1) (x+2^(p+2)-(i+p+2)).
Proof.
  intros.
  applys_eq (U_up (i+p) p x); try assumption; try flia.
  1: applys_eq H1; flia.
  1: applys_eq H2; flia.
  1: applys_eq H3; flia.
Qed.

Lemma U_sames i j m x:
  m*(i+j+2) <= x ->
  LH i <= x-m*(i+j+2) ->
  x <= UH i ->
  x+6 <= B i j ->
  US i j x -->* US i j (x-m*(i+j+2)).
Proof.
  gen x.
  induction m; intros.
  1: cbn; finish.
  cbn [Nat.mul] in *.
  follow U_same.
  1: lia.
  1: split; lia.
  follow IHm.
  1: apply Nat.le_add_le_sub_l; lia.
  1: rewrite <-Nat.sub_add_distr; exact H0.
  1: lia.
  1: eapply Nat.le_trans.
  2: exact H2.
  1: apply Nat.add_le_mono_r, Nat.le_sub_l.
  rewrite <-Nat.sub_add_distr.
  finish.
Qed.

Lemma pair_sub x p h:
  h*2 <= x ->
  (x+p-h)-p-h = x-h*2.
Proof.
  intros H.
  assert (h<=x) by lia.
  pose proof (Nat.sub_add h x H0).
  assert (p <= x+p-h) by lia.
  pose proof (Nat.sub_add p (x+p-h) H2).
  pose proof (Nat.sub_add (h*2) x H).
  lia.
Qed.

Lemma pair_mid_bound x p h:
  h*2 <= x -> p+h <= x+p-h.
Proof.
  intros H.
  assert (h<=x+p) by lia.
  pose proof (Nat.sub_add h (x+p) H0).
  lia.
Qed.

Lemma U_pair s p x:
  p+1 <= s ->
  (s+2)*2 <= x ->
  x+6 <= B (s-p) p ->
  x+2^(p+2)-(s+2)+6 <= B (s-(p+1)) (p+1) ->
  LH (s-(p+1)) <= x <= UH (s-(p+1)) ->
  LH (s-p) <= x+2^(p+2)-(s+2) <= UH (s-p) ->
  US (s-p) p x -->* US (s-p) p (x-(s+2)*2).
Proof.
  intros Hp Hx HB0 HB1 HC0 HC1.
  follow U_up.
  1: lia.
  follow U_down.
  1: replace (2^(p+2)+s+2) with (2^(p+2)+(s+2)) by lia.
     exact (pair_mid_bound x (2^(p+2)) (s+2) Hx).
  1: rewrite (pair_sub x (2^(p+2)) (s+2) Hx).
     eapply Nat.le_trans.
     2: exact HB0.
     apply Nat.add_le_mono_r, Nat.le_sub_l.
  rewrite (pair_sub x (2^(p+2)) (s+2) Hx).
  finish.
Qed.

Lemma pow2_twice n: n*2 <= 2^n.
Proof.
  induction n.
  1: cbn; lia.
  cbn [Nat.pow].
  pose proof (pow2_gt n).
  nia.
Qed.

Lemma pow2_twice_plus1 n:
  3 <= n -> n*2+1 <= 2^n.
Proof.
  intros Hn.
  assert (exists k, n=3+k) by (exists (n-3); lia).
  destruct H as [k ->].
  clear Hn.
  induction k.
  1: cbn; lia.
  replace (3+S k) with (S (3+k)) by lia.
  cbn [Nat.pow].
  eapply Nat.le_trans with (2*((3+k)*2+1)).
  2: apply Nat.mul_le_mono_l; exact IHk.
  lia.
Qed.

Lemma pow2_triple_plus1 n:
  4 <= n -> n*3+1 <= 2^n.
Proof.
  intros Hn.
  assert (exists k, n=4+k) by (exists (n-4); lia).
  destruct H as [k ->].
  clear Hn.
  induction k.
  1: cbn; lia.
  replace (4+S k) with (S (4+k)) by lia.
  cbn [Nat.pow].
  eapply Nat.le_trans with (2*((4+k)*3+1)).
  2: apply Nat.mul_le_mono_l; exact IHk.
  lia.
Qed.

Lemma far_i3 i p:
  Far i p -> 3 <= i.
Proof.
  unfold Far.
  destruct i.
  1: cbn; lia.
  destruct i.
  1: cbn; lia.
  destruct i.
  1: cbn; pose proof (pow2_twice (p+2)); lia.
  lia.
Qed.

Lemma far_i4 i p:
  Far i p -> 4 <= i.
Proof.
  unfold Far.
  destruct i.
  1: cbn; lia.
  destruct i.
  1: cbn; lia.
  destruct i.
  1: cbn; lia.
  destruct i.
  1: cbn; pose proof (pow2_twice (p+2)); lia.
  lia.
Qed.

Lemma LH_pred_gap i:
  1 <= i -> LH (i-1)+(2^i-1) = LH i.
Proof.
  destruct i as [|i]; intros.
  1: lia.
  unfold LH.
  cbn [Nat.sub Nat.pow].
  repeat rewrite <-Nat.sub_add_distr.
  pose proof (pow2_gt i).
  pose proof (Nat.sub_add (i+2) (2^i*2) ltac:(nia)).
  pose proof (Nat.sub_add 1 (2^i*2) ltac:(nia)).
  pose proof (Nat.sub_add (S i+2) ((2^i*2)*2) ltac:(nia)).
  rewrite Nat.sub_0_r.
  nia.
Qed.

Lemma pred_bucket_adj i:
  1 <= i -> UH (i-1)+1 = LH i.
Proof.
  intros.
  replace i with (S (i-1)) by lia.
  replace (S (i-1)-1) with (i-1) by lia.
  apply bucket_adj.
Qed.

Lemma LH_pred_eq i:
  1 <= i -> LH (i-1) = 2^i-i-1.
Proof.
  destruct i as [|i]; intros.
  1: lia.
  unfold LH.
  cbn [Nat.sub Nat.pow].
  rewrite Nat.sub_0_r.
  repeat rewrite <-Nat.sub_add_distr.
  replace (S i+1) with (i+2) by lia.
  replace (2*2^i) with (2^i*2) by nia.
  reflexivity.
Qed.

Lemma far_gap i p:
  1 <= i -> Far i p ->
  LH (i-1)+2^(p+2)+(i+p+2) <= LH i.
Proof.
  intros Hi HF.
  rewrite <-(LH_pred_gap i Hi).
  unfold Far in HF.
  lia.
Qed.

Lemma enter_gap i p:
  Far i p ->
  LH (i-1)+(i+p+2)*2 <= LH i+2^(p+2).
Proof.
  intros HF.
  pose proof (far_i3 i p HF).
  pose proof (pow2_twice_plus1 i H).
  pose proof (pow2_twice (p+2)).
  rewrite <-(LH_pred_gap i ltac:(lia)).
  lia.
Qed.

Lemma far_h_prev i p:
  Far i p -> i+p+2 <= LH (i-1).
Proof.
  intros HF.
  pose proof (far_i4 i p HF) as Hi.
  assert (2^(p+2) <= 2^i) as HP by (unfold Far in HF; lia).
  apply (Nat.pow_le_mono_r_iff 2 (p+2) i ltac:(lia)) in HP.
  pose proof (pow2_triple_plus1 i Hi).
  rewrite LH_pred_eq by lia.
  pose proof (Nat.sub_add (i+1) (2^i) ltac:(lia)).
  lia.
Qed.

Lemma bucket_B ip jp k x:
  k <= ip+jp -> x <= UH k -> x+6 <= B ip jp.
Proof.
  intros.
  eapply Nat.le_trans.
  2: apply UH_B; exact H.
  lia.
Qed.

Lemma bucket_nonempty i: LH i <= UH i.
Proof.
  unfold LH, UH.
  pose proof (pow2_gt i).
  flia.
Qed.

Lemma bucket_width i:
  LH i+(2^(i+1)-2) = UH i.
Proof.
  unfold LH, UH.
  replace (i+1) with (S i) by lia.
  cbn [Nat.pow].
  pose proof (pow2_gt i).
  repeat rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add (i+2) (2^i*2) ltac:(nia)).
  pose proof (Nat.sub_add 2 (2^i*2) ltac:(nia)).
  pose proof (Nat.sub_add (i+4) (2^i*4) ltac:(nia)).
  nia.
Qed.

Lemma far_up_upper i p x:
  Far i p -> x <= UH (i-1) ->
  x+2^(p+2)-(i+p+2) <= UH i.
Proof.
  intros HF Hx.
  pose proof (far_i4 i p HF).
  pose proof (pred_bucket_adj i ltac:(lia)).
  assert (2^(p+2) <= 2^i) by (unfold Far in HF; lia).
  assert (LH i+2^i <= UH i+1).
  { unfold LH, UH.
    pose proof (pow2_gt i).
    flia. }
  eapply Nat.le_trans.
  1: apply Nat.le_sub_l.
  lia.
Qed.

Lemma sub_twice_lower l x p h:
  h <= x -> l+h*2 <= x+p ->
  l <= x-h+p-h.
Proof.
  intros Hx Hsum.
  pose proof (Nat.sub_add h x Hx).
  assert (h <= x-h+p) as Hmid by lia.
  pose proof (Nat.sub_add h (x-h+p) Hmid).
  lia.
Qed.

Lemma pow2_center_gap m:
  8 <= m -> 4*m+3 <= 2^(m-1).
Proof.
  intros Hm.
  assert (exists k, m=8+k) by (exists (m-8); lia).
  destruct H as [k ->].
  clear Hm.
  induction k.
  1: cbn; lia.
  replace (8+S k-1) with (S (8+k-1)) by lia.
  cbn [Nat.pow].
  eapply Nat.le_trans with (2*(4*(8+k)+3)).
  2: apply Nat.mul_le_mono_l; exact IHk.
  lia.
Qed.

Lemma pow2_center_gap5 m:
  8 <= m -> 4*m+5 <= 2^(m-1).
Proof.
  intros Hm.
  assert (exists k, m=8+k) by (exists (m-8); lia).
  destruct H as [k ->].
  clear Hm.
  induction k.
  1: cbn; lia.
  replace (8+S k-1) with (S (8+k-1)) by lia.
  cbn [Nat.pow].
  eapply Nat.le_trans with (2*(4*(8+k)+5)).
  2: apply Nat.mul_le_mono_l; exact IHk.
  lia.
Qed.

Lemma center_sub_bound m:
  8 <= m -> 2*m+2 <= LH m.
Proof.
  intros Hm.
  pose proof (pow2_center_gap m Hm) as HG.
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  unfold LH.
  rewrite HP.
  pose proof (Nat.sub_add (m+2) ((2*2^(m-1))*2) ltac:(nia)).
  lia.
Qed.

Lemma center_drop_lower m x:
  8 <= m -> LH m <= x -> LH (m-1) <= x-(2*m+1).
Proof.
  intros Hm Hx.
  pose proof (LH_pred_gap m ltac:(lia)) as HL.
  pose proof (pow2_center_gap m Hm) as HG.
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  pose proof (pow2_gt m) as HP0.
  pose proof (Nat.sub_add 1 (2^m) ltac:(lia)) as HP1.
  assert (LH (m-1)+(2*m+1) <= x) as Hsum by lia.
  pose proof (Nat.sub_add (2*m+1) x ltac:(lia)).
  lia.
Qed.

Lemma center_drop_lower2 m x:
  8 <= m -> LH m <= x -> LH (m-1) <= x-(2*m+2).
Proof.
  intros Hm Hx.
  pose proof (LH_pred_gap m ltac:(lia)) as HL.
  pose proof (pow2_center_gap m Hm) as HG.
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  pose proof (pow2_gt m) as HP0.
  pose proof (Nat.sub_add 1 (2^m) ltac:(lia)) as HP1.
  assert (LH (m-1)+(2*m+2) <= x) as Hsum by lia.
  pose proof (Nat.sub_add (2*m+2) x ltac:(lia)).
  lia.
Qed.

Lemma E_up_range m x:
  8 <= m ->
  LH (m-1) <= x <= UH (m-1) ->
  LH m <= x+2^(m+1)-(2*m+1) <= UH m.
Proof.
  intros Hm [Hxl Hxu].
  pose proof (LH_pred_gap m ltac:(lia)).
  pose proof (pred_bucket_adj m ltac:(lia)).
  pose proof (bucket_width m).
  pose proof (pow2_twice m).
  assert (2^(m+1)=2*2^m) as HP.
  { replace (m+1) with (S m) by lia; cbn [Nat.pow]; nia. }
  assert (2*m+1 <= x+2^(m+1)) as Hsub by (rewrite HP; lia).
  pose proof (Nat.sub_add (2*m+1) (x+2^(m+1)) Hsub) as Hysub.
  rewrite HP in Hysub.
  split.
  1: lia.
  1: lia.
Qed.

Lemma E_drop_bucket m x:
  8 <= m ->
  LH (m-1) <= x ->
  x-(2*m+1)*2 < LH (m-1) ->
  LH (m-2) <= x-(2*m+1)*2 <= UH (m-2).
Proof.
  intros Hm Hx He.
  pose proof (LH_pred_eq m ltac:(lia)) as HL0.
  pose proof (pow2_center_gap m Hm) as HG.
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  assert ((2*m+1)*2 <= x) as Hsub by lia.
  pose proof (Nat.sub_add ((2*m+1)*2) x Hsub) as Hdrop.
  pose proof (LH_pred_gap (m-1) ltac:(lia)) as HL.
  pose proof (pred_bucket_adj (m-1) ltac:(lia)) as HA.
  replace (m-1-1) with (m-2) in HL, HA by lia.
  pose proof (pow2_center_gap5 m Hm) as HG5.
  pose proof (pow2_gt (m-1)) as HP0.
  pose proof (Nat.sub_add 1 (2^(m-1)) ltac:(lia)).
  split; lia.
Qed.

Lemma E_up2_range m x:
  8 <= m ->
  LH (m-1) <= x+(2*m+1)*2 ->
  x < LH (m-1) ->
  LH (m+1) <= x+3*2^(m+1)-(2*m+1) <= UH (m+1).
Proof.
  intros Hm Hlo Hhi.
  rewrite LH_pred_eq in Hlo, Hhi by lia.
  unfold LH, UH.
  replace (m+1) with (S m) by lia.
  cbn [Nat.pow].
  pose proof (pow2_gt m).
  assert (2*m+1 <= x+3*(2*2^m)) as Hsub by lia.
  pose proof (Nat.sub_add (2*m+1) (x+3*(2*2^m)) Hsub).
  pose proof (Nat.sub_add (S m+2) ((2*2^m)*2) ltac:(nia)).
  pose proof (Nat.sub_add (S m+4) ((2*2^m)*4) ltac:(nia)).
  split; lia.
Qed.

Lemma U_stage_B i p x:
  1 <= i -> Far i p ->
  LH (i-1) <= x <= UH (i-1) ->
  LH (i-1) <= x+2^(p+2)-(i+p+2) ->
  exists y, LH (i-1) <= y <= UH (i-1) /\
    US i p x -->* US (i-1) (p+1) y.
Proof.
  intros Hi HF.
  induction x using lt_wf_ind; intros HC Hyl.
  destruct HC as [Hxl0 Hxu0].
  pose proof (far_h_prev i p HF) as Hh.
  pose proof (far_up_upper i p x HF Hxu0) as Hyu.
  pose proof (pred_bucket_adj i Hi) as Hadj.
  destruct (le_lt_dec
    (x+2^(p+2)-(i+p+2)) (UH (i-1))) as [Hy0|Hy1].
  - exists (x+2^(p+2)-(i+p+2)); split.
    1: lia.
    apply U_up_i; auto.
    1: lia.
    1: apply bucket_B with (k:=i-1); lia.
    1: apply bucket_B with (k:=i); lia.
  - assert (LH i <= x+2^(p+2)-(i+p+2)) as Hyi by lia.
    assert ((i+p+2)*2 <= x) as H2x.
    { pose proof (far_gap i p Hi HF).
      pose proof (Nat.sub_add (i+p+2) (x+2^(p+2)) ltac:(lia)).
      lia. }
    assert (i+p+2 <= 2^(p+2)) as Hhp.
    { pose proof (Nat.sub_add (i+p+2) (x+2^(p+2)) ltac:(lia)).
      lia. }
    assert (LH (i-1) <= x-(i+p+2)*2) as Hxl.
    { pose proof (far_gap i p Hi HF).
      pose proof (Nat.sub_add (i+p+2) (x+2^(p+2)) ltac:(lia)).
      pose proof (Nat.sub_add ((i+p+2)*2) x H2x).
      lia. }
    assert (LH (i-1) <=
      (x-(i+p+2)*2)+2^(p+2)-(i+p+2)) as Hnext.
    { pose proof (far_gap i p Hi HF).
      pose proof (Nat.sub_add (i+p+2) (x+2^(p+2)) ltac:(lia)).
      pose proof (Nat.sub_add ((i+p+2)*2) x H2x).
      assert (i+p+2 <= x-(i+p+2)*2+2^(p+2)) as Hmid by lia.
      pose proof (Nat.sub_add (i+p+2)
        (x-(i+p+2)*2+2^(p+2)) Hmid).
      lia. }
    unshelve epose proof
      (H (x-(i+p+2)*2) _ _ Hnext) as [z [Hz HR]].
    1: pose proof (Nat.sub_add ((i+p+2)*2) x H2x); lia.
    1: split.
       1: exact Hxl.
       eapply Nat.le_trans.
       2: exact Hxu0.
       apply Nat.le_sub_l.
    exists z; split.
    1: exact Hz.
    follow (U_pair (i+p) p x).
    1: lia.
    1: apply bucket_B with (k:=i-1); lia.
    1: apply bucket_B with (k:=i); lia.
    1: applys_eq (conj Hxl0 Hxu0); flia.
    1: applys_eq (conj Hyi Hyu); flia.
    applys_eq HR; flia.
Qed.

Lemma U_stage i p x:
  Far i p ->
  LH i <= x <= UH i ->
  exists y, LH (i-1) <= y <= UH (i-1) /\
    US i p x -->* US (i-1) (p+1) y.
Proof.
  intros HF.
  induction x using lt_wf_ind; intros HC.
  destruct HC as [HC0 HC1].
  pose proof (far_i4 i p HF) as Hi.
  pose proof (far_h_prev i p HF) as Hh.
  assert (i+p+2 <= x) as Hhx.
  { pose proof (bucket_nonempty (i-1)).
    pose proof (pred_bucket_adj i ltac:(lia)).
    lia. }
  pose proof (Nat.sub_add (i+p+2) x Hhx) as Hsub.
  destruct (le_lt_dec (LH i) (x-(i+p+2))) as [Hstay|Hexit].
  - unshelve epose proof
      (H (x-(i+p+2)) _ _) as [y [Hy HR]].
    1: pose proof (pow2_gt (p+2)); lia.
    1: split.
       1: exact Hstay.
       eapply Nat.le_trans.
       2: exact HC1.
       apply Nat.le_sub_l.
    exists y; split.
    1: exact Hy.
    follow U_same.
    1: apply bucket_B with (k:=i); lia.
    exact HR.
  - assert (LH (i-1) <= x-(i+p+2)) as Hprevl.
    { pose proof (far_gap i p ltac:(lia) HF).
      lia. }
    assert (x-(i+p+2) <= UH (i-1)) as Hprevu.
    { pose proof (pred_bucket_adj i ltac:(lia)).
      lia. }
    assert (LH (i-1) <=
      (x-(i+p+2))+2^(p+2)-(i+p+2)) as Hnext.
    { apply sub_twice_lower.
      1: exact Hhx.
      pose proof (enter_gap i p HF).
      lia. }
    destruct (U_stage_B i p (x-(i+p+2)) ltac:(lia) HF
      (conj Hprevl Hprevu) Hnext) as [y [Hy HR]].
    exists y; split.
    1: exact Hy.
    follow U_same.
    1: apply bucket_B with (k:=i); lia.
    exact HR.
Qed.

Lemma U_carry1 i p x b:
  1 <= i ->
  5 <= b ->
  b+1 <= 2^(i+p+3)+2^(p+1) ->
  x+6 <= B (i-1) (p+1) ->
  2^(i+p+3)+2^(p+1)-b-1+6 <= B (i+1) p ->
  LH (i+1) <= x <= UH (i+1) ->
  b+x = 3*2^(p+1)+i+p+2 ->
  US (i-1) (p+1) x -->* Q (i+p+2) p b.
Proof.
  intros Hi Hb Hsub HB0 HB1 HC HE.
  unfold Q.
  replace (i+p+2-p-1) with (i+1) by lia.
  apply U_next.
  1: exact HB0.
  1: applys_eq HB1; flia.
  1: exact HC.
  rewrite !B_expand.
  replace (i-1+(p+1)) with (i+p) by lia.
  replace (i+1+p) with (S (i+p)) by lia.
  replace (i+p+2+1) with (S (S (S (i+p)))) by lia.
  replace (p+1+1) with (S (p+1)) by lia.
  cbn [Nat.pow].
  assert (2^(i+p+3)=2^(i+p)*8) as HP.
  { replace (i+p+3) with (S (S (S (i+p)))) by lia.
    cbn [Nat.pow]; nia. }
  rewrite HP in Hsub.
  pose proof (Nat.sub_add (b+1)
    (2^(i+p)*8+2^(p+1)) Hsub).
  nia.
Qed.

Lemma U_carry2 i p x b:
  2 <= i ->
  5 <= b ->
  b+1 <= 2^(i+p+3)+2^(p+1) ->
  x+6 <= B (i-2) (p+2) ->
  2^(i+p+3)+2^(p+1)-b-1+6 <= B (i+1) p ->
  LH (i+1) <= x <= UH (i+1) ->
  b+x = 7*2^(p+1)+i+p+2 ->
  US (i-2) (p+2) x -->* Q (i+p+2) p b.
Proof.
  intros Hi Hb Hsub HB0 HB1 HC HE.
  unfold Q.
  replace (i+p+2-p-1) with (i+1) by lia.
  apply U_next.
  1: exact HB0.
  1: applys_eq HB1; flia.
  1: exact HC.
  rewrite !B_expand.
  replace (i-2+(p+2)) with (i+p) by lia.
  replace (i+1+p) with (S (i+p)) by lia.
  replace (i+p+2+1) with (S (S (S (i+p)))) by lia.
  replace (p+2+1) with (S (S (p+1))) by lia.
  cbn [Nat.pow].
  assert (2^(i+p+3)=2^(i+p)*8) as HP.
  { replace (i+p+3) with (S (S (S (i+p)))) by lia.
    cbn [Nat.pow]; nia. }
  rewrite HP in Hsub.
  pose proof (Nat.sub_add (b+1)
    (2^(i+p)*8+2^(p+1)) Hsub).
  nia.
Qed.

Lemma U_up2 i p x:
  2 <= i ->
  i+p+2 <= x+3*2^(p+2) ->
  x+6 <= B i p ->
  x+3*2^(p+2)-(i+p+2)+6 <= B (i-2) (p+2) ->
  LH (i-2) <= x <= UH (i-2) ->
  US i p x -->*
    US (i-2) (p+2) (x+3*2^(p+2)-(i+p+2)).
Proof.
  intros Hi Hsub HB0 HB1 HC.
  apply U_next.
  1: exact HB0.
  1: exact HB1.
  1: exact HC.
  rewrite !B_expand.
  replace (i-2+(p+2)) with (i+p) by lia.
  replace (p+2+1) with (S (S (p+1))) by lia.
  cbn [Nat.pow].
  pose proof (Nat.sub_add (i+p+2)
    (x+3*2^(p+2)) Hsub).
  replace (p+2) with (S (p+1)) in H by lia.
  cbn [Nat.pow] in H.
  replace (2^(p+2)) with (2*2^(p+1)).
  2: replace (p+2) with (S (p+1)) by lia; cbn [Nat.pow]; nia.
  nia.
Qed.

Lemma U_down2 i p x:
  2 <= i ->
  3*2^(p+2)+i+p+2 <= x ->
  x+6 <= B (i-2) (p+2) ->
  x-3*2^(p+2)-(i+p+2)+6 <= B i p ->
  LH i <= x <= UH i ->
  US (i-2) (p+2) x -->*
    US i p (x-3*2^(p+2)-(i+p+2)).
Proof.
  intros Hi Hsub HB0 HB1 HC.
  apply U_next.
  1: exact HB0.
  1: exact HB1.
  1: exact HC.
  rewrite !B_expand.
  replace (i-2+(p+2)) with (i+p) by lia.
  replace (p+2+1) with (S (S (p+1))) by lia.
  cbn [Nat.pow].
  rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add (3*2^(p+2)+i+p+2) x Hsub).
  replace (2^(p+2)) with (2*2^(p+1)) in H |- *.
  2: replace (p+2) with (S (p+1)) by lia; cbn [Nat.pow]; nia.
  nia.
Qed.

Lemma U_pair2 i p x:
  2 <= i ->
  (i+p+2)*2 <= x ->
  x+6 <= B i p ->
  x+3*2^(p+2)-(i+p+2)+6 <= B (i-2) (p+2) ->
  LH (i-2) <= x <= UH (i-2) ->
  LH i <= x+3*2^(p+2)-(i+p+2) <= UH i ->
  US i p x -->* US i p (x-(i+p+2)*2).
Proof.
  intros Hi Hx HB0 HB1 HC0 HC1.
  follow U_up2.
  1: lia.
  follow U_down2.
  1: applys_eq (pair_mid_bound x (3*2^(p+2)) (i+p+2) Hx); flia.
  1: rewrite (pair_sub x (3*2^(p+2)) (i+p+2) Hx).
     eapply Nat.le_trans.
     2: exact HB0.
     apply Nat.add_le_mono_r, Nat.le_sub_l.
  rewrite (pair_sub x (3*2^(p+2)) (i+p+2) Hx).
  finish.
Qed.

Lemma U_up3 i p x:
  3 <= i ->
  i+p+2 <= x+7*2^(p+2) ->
  x+6 <= B i p ->
  x+7*2^(p+2)-(i+p+2)+6 <= B (i-3) (p+3) ->
  LH (i-3) <= x <= UH (i-3) ->
  US i p x -->*
    US (i-3) (p+3) (x+7*2^(p+2)-(i+p+2)).
Proof.
  intros Hi Hsub HB0 HB1 HC.
  apply U_next.
  1: exact HB0.
  1: exact HB1.
  1: exact HC.
  rewrite !B_expand.
  replace (i-3+(p+3)) with (i+p) by lia.
  replace (p+3+1) with (S (S (S (p+1)))) by lia.
  cbn [Nat.pow].
  pose proof (Nat.sub_add (i+p+2)
    (x+7*2^(p+2)) Hsub).
  replace (2^(p+2)) with (2*2^(p+1)) in H |- *.
  2: replace (p+2) with (S (p+1)) by lia; cbn [Nat.pow]; nia.
  nia.
Qed.

Lemma U_carry3 i p x b:
  3 <= i ->
  5 <= b ->
  b+1 <= 2^(i+p+3)+2^(p+1) ->
  x+6 <= B (i-3) (p+3) ->
  2^(i+p+3)+2^(p+1)-b-1+6 <= B (i+1) p ->
  LH (i+1) <= x <= UH (i+1) ->
  b+x = 15*2^(p+1)+i+p+2 ->
  US (i-3) (p+3) x -->* Q (i+p+2) p b.
Proof.
  intros Hi Hb Hsub HB0 HB1 HC HE.
  unfold Q.
  replace (i+p+2-p-1) with (i+1) by lia.
  apply U_next.
  1: exact HB0.
  1: applys_eq HB1; flia.
  1: exact HC.
  rewrite !B_expand.
  replace (i-3+(p+3)) with (i+p) by lia.
  replace (i+1+p) with (S (i+p)) by lia.
  replace (i+p+2+1) with (S (S (S (i+p)))) by lia.
  replace (p+3+1) with (S (S (S (p+1)))) by lia.
  cbn [Nat.pow].
  assert (2^(i+p+3)=2^(i+p)*8) as HP.
  { replace (i+p+3) with (S (S (S (i+p)))) by lia.
    cbn [Nat.pow]; nia. }
  rewrite HP in Hsub.
  pose proof (Nat.sub_add (b+1)
    (2^(i+p)*8+2^(p+1)) Hsub).
  nia.
Qed.

Lemma center_E_target_B m b:
  8 <= m ->
  5 <= b ->
  b+1 <= 2^(2*m+2)+2^m ->
  2^(2*m-1-(m-1)+(m-1)+3)+2^(m-1+1)-b-1+6 <=
    B (2*m-1-(m-1)+1) (m-1).
Proof.
  intros Hm Hb Hbig.
  pose proof (Q_B (2*m+1) (m-1) b ltac:(lia) Hb) as HQ.
  replace (2*m+1+1) with (2*m+2) in HQ by lia.
  replace (m-1+1) with m in HQ by lia.
  specialize (HQ Hbig).
  replace (2*m+1-(m-1)-1) with (m+1) in HQ by lia.
  replace (2*m-1-(m-1)+1) with (m+1) by lia.
  replace (2*m-1-(m-1)+(m-1)+3) with (2*m+2) by lia.
  replace (m-1+1) with m by lia.
  exact HQ.
Qed.

Lemma center_E_carry_eq m x b:
  8 <= m ->
  b+(x-(2*m+1)*2)=2^m+4*m+2 ->
  b+(x-(2*m-1+2)*2+3*2^(m-1+2)-
      (2*m-1-(m-1)+(m-1)+2)) =
    7*2^(m-1+1)+(2*m-1-(m-1))+(m-1)+2.
Proof.
  intros Hm HE.
  replace (2*m-1+2) with (2*m+1) by lia.
  replace (m-1+2) with (m+1) by lia.
  replace (m-1+1) with m by lia.
  replace (2*m-1-(m-1)+(m-1)+2) with (2*m+1) by lia.
  replace (2*m-1-(m-1)) with m by lia.
  assert (2^(m+1)=2*2^m) as HP.
  { replace (m+1) with (S m) by lia; cbn [Nat.pow]; nia. }
  rewrite HP.
  pose proof (pow2_gt m).
  pose proof (Nat.sub_add (2*m+1)
    (x-(2*m+1)*2+3*(2*2^m)) ltac:(nia)).
  nia.
Qed.

Lemma center_E_B m x:
  8 <= m ->
  LH (m-1) <= x <= UH (m-1) ->
  exists b,
    10*m+7 <= b*2 <= 18*m+11 /\
    US m (m-1) x -->* Q (2*m+1) (m-1) b.
Proof.
  intros Hm.
  induction x using lt_wf_ind; intros HC.
  destruct HC as [Hxl Hxu].
  pose proof (E_up_range m x Hm (conj Hxl Hxu)) as [Hyl Hyu].
  pose proof (LH_pred_eq m ltac:(lia)) as HL.
  pose proof (pow2_center_gap m Hm) as HG.
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  assert ((2*m+1)*2 <= x) as H2x by lia.
  pose proof (Nat.sub_add ((2*m+1)*2) x H2x) as Hdrop.
  destruct (le_lt_dec (LH (m-1)) (x-(2*m+1)*2)) as [Hstay|Hexit].
  - assert (x-(2*m+1)*2 <= UH (m-1)) as Hxu'.
    { eapply Nat.le_trans.
      1: apply Nat.le_sub_l.
      exact Hxu. }
    destruct (H (x-(2*m+1)*2) ltac:(lia)
      (conj Hstay Hxu'))
      as [b [Hb HR]].
    exists b; split.
    1: exact Hb.
    follow (U_pair (2*m-1) (m-1) x).
    1: lia.
    1: applys_eq H2x; lia.
    1: apply bucket_B with (k:=m-1); lia.
    1: apply bucket_B with (k:=m).
       1: flia.
       replace (m-1+2) with (m+1) by lia.
       replace (2*m-1+2) with (2*m+1) by lia.
       exact Hyu.
    1: replace (2*m-1-(m-1+1)) with (m-1) by lia.
       exact (conj Hxl Hxu).
    1: replace (2*m-1-(m-1)) with m by lia.
       replace (m-1+2) with (m+1) by lia.
       replace (2*m-1+2) with (2*m+1) by lia.
       exact (conj Hyl Hyu).
    replace (2*m-1-(m-1)) with m by lia.
    replace (2*m-1+2) with (2*m+1) by lia.
    exact HR.
  - pose proof (E_drop_bucket m x Hm Hxl Hexit) as [Hxtl Hxtu].
    pose proof (E_up2_range m (x-(2*m+1)*2) Hm
      ltac:(lia) Hexit) as [Hy2l Hy2u].
    set (b := 2^m+4*m+2-(x-(2*m+1)*2)).
    assert (b+(x-(2*m+1)*2)=2^m+4*m+2) as Hbdef.
    { unfold b.
      apply Nat.sub_add.
      lia. }
    assert (10*m+7 <= b*2 <= 18*m+11) as Hb by lia.
    assert (5 <= b) as Hb5 by lia.
    assert (b+1 <= 2^(2*m+2)+2^m) as Hbig.
    { pose proof (Nat.pow_le_mono_r 2 (m+1) (2*m+2)
        ltac:(lia) ltac:(lia)).
      assert (2^(m+1)=4*2^(m-1)).
      { replace (m+1) with ((m-1)+2) by lia.
        rewrite Nat.pow_add_r; cbn; nia. }
      lia. }
    exists b; split.
    1: exact Hb.
    follow (U_pair (2*m-1) (m-1) x).
    1: lia.
    1: replace (2*m-1+2) with (2*m+1) by lia.
       exact H2x.
    1: apply bucket_B with (k:=m-1); lia.
    1: apply bucket_B with (k:=m).
       1: flia.
       replace (m-1+2) with (m+1) by lia.
       replace (2*m-1+2) with (2*m+1) by lia.
       exact Hyu.
    1: replace (2*m-1-(m-1+1)) with (m-1) by lia.
       exact (conj Hxl Hxu).
    1: replace (2*m-1-(m-1)) with m by lia.
       replace (m-1+2) with (m+1) by lia.
       replace (2*m-1+2) with (2*m+1) by lia.
       exact (conj Hyl Hyu).
    follow U_up2.
    1: lia.
    1: pose proof (pow2_gt (m+1)); lia.
    1: apply bucket_B with (k:=m-2).
       1: lia.
       replace (2*m-1+2) with (2*m+1) by lia.
       exact Hxtu.
    1: apply bucket_B with (k:=m+1).
       1: lia.
       replace (m-1+2) with (m+1) by lia.
       replace (2*m-1+2) with (2*m+1) by lia.
       replace (2*m-1-(m-1)+(m-1)+2) with (2*m+1) by lia.
       exact Hy2u.
    1: replace (2*m-1+2) with (2*m+1) by lia.
       replace (2*m-1-(m-1)+(m-1)+2) with (2*m+1) by lia.
       replace (2*m-1-(m-1)-2) with (m-2) by lia.
       exact (conj Hxtl Hxtu).
    follow U_carry2.
    1: lia.
    1: replace (2*m-1-(m-1)+(m-1)+3) with (2*m+2) by lia.
       replace (m-1+1) with m by lia.
       exact Hbig.
    1: apply bucket_B with (k:=m+1).
       1: lia.
       replace (m-1+2) with (m+1) by lia.
       replace (2*m-1+2) with (2*m+1) by lia.
       replace (2*m-1-(m-1)+(m-1)+2) with (2*m+1) by lia.
       exact Hy2u.
    1: exact (center_E_target_B m b Hm Hb5 Hbig).
    1: replace (m-1+2) with (m+1) by lia.
       replace (2*m-1+2) with (2*m+1) by lia.
       replace (2*m-1-(m-1)+(m-1)+2) with (2*m+1) by lia.
       replace (2*m-1-(m-1)+1) with (m+1) by lia.
       exact (conj Hy2l Hy2u).
    1: exact (center_E_carry_eq m x b Hm Hbdef).
    finish.
Qed.

Lemma center_E m x:
  8 <= m ->
  LH m <= x <= UH m ->
  exists b,
    10*m+7 <= b*2 <= 18*m+11 /\
    US m (m-1) x -->* Q (2*m+1) (m-1) b.
Proof.
  intros Hm.
  induction x using lt_wf_ind; intros HC.
  destruct HC as [Hxl Hxu].
  pose proof (pow2_center_gap m Hm).
  pose proof (center_sub_bound m Hm).
  pose proof (pow2_twice m).
  pose proof (LH_pred_gap m ltac:(lia)).
  pose proof (pred_bucket_adj m ltac:(lia)).
  assert (2*m+1 <= x) as Hsub by lia.
  pose proof (Nat.sub_add (2*m+1) x Hsub).
  destruct (le_lt_dec (LH m) (x-(2*m+1))) as [Hstay|Hexit].
  - assert (x-(2*m+1) <= UH m) as Hxu'.
    { eapply Nat.le_trans.
      1: apply Nat.le_sub_l.
      exact Hxu. }
    destruct (H (x-(2*m+1)) ltac:(lia)
      (conj Hstay Hxu')) as [b [Hb HR]].
    exists b; split.
    1: exact Hb.
    follow U_same.
    1: lia.
    1: apply bucket_B with (k:=m); lia.
    replace (m+(m-1)+2) with (2*m+1) by lia.
    exact HR.
  - assert (LH (m-1) <= x-(2*m+1)) as Hbl.
    { exact (center_drop_lower m x Hm Hxl). }
    assert (x-(2*m+1) <= UH (m-1)) as Hbu by lia.
    destruct (center_E_B m (x-(2*m+1)) Hm (conj Hbl Hbu))
      as [b [Hb HR]].
    exists b; split.
    1: exact Hb.
    follow U_same.
    1: lia.
    1: apply bucket_B with (k:=m); lia.
    replace (m+(m-1)+2) with (2*m+1) by lia.
    exact HR.
Qed.

Lemma O0_up_range m x:
  8 <= m ->
  LH m <= x+(2*m+2) ->
  x < LH m ->
  LH (m+1) <= x+2^(m+2)-(2*m+2) <= UH (m+1).
Proof.
  intros Hm Hlo Hhi.
  unfold LH, UH in *.
  replace (m+1) with (S m) by lia.
  replace (m+2) with (S (S m)) by lia.
  cbn [Nat.pow] in *.
  repeat rewrite <-Nat.sub_add_distr in *.
  pose proof (pow2_gt m).
  pose proof (pow2_center_gap m Hm) as HG.
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  assert (2*m+2 <= x+2*(2*2^m)) as Hsub by lia.
  pose proof (Nat.sub_add (2*m+2) (x+2*(2*2^m)) Hsub).
  pose proof (Nat.sub_add (m+2) (2^m*2) ltac:(nia)).
  pose proof (Nat.sub_add (m+4) (2^m*4) ltac:(nia)).
  pose proof (Nat.sub_add (S m+2) ((2*2^m)*2) ltac:(nia)).
  pose proof (Nat.sub_add (S m+4) ((2*2^m)*4) ltac:(nia)).
  assert (m <= x) by lia.
  split.
  1: lia.
  1: lia.
Qed.

Lemma O0_b_bounds m x b:
  8 <= m ->
  LH m <= x ->
  x-(2*m+2) < LH m ->
  b+(x-(2*m+2))=2^(m+1)+4*m+4 ->
  10*m+12 <= b*2 <= 18*m+20.
Proof.
  intros Hm Hxl Hexit Hbdef.
  pose proof (pow2_center_gap m Hm) as HG.
  pose proof (center_sub_bound m Hm) as Hcenter.
  assert (2*m+2 <= x) as Hcut by lia.
  pose proof (Nat.sub_add (2*m+2) x Hcut) as Hdrop.
  assert (2^(m+1)=2*2^m) as HP.
  { replace (m+1) with (S m) by lia; cbn [Nat.pow]; nia. }
  rewrite HP in Hbdef.
  unfold LH in Hxl, Hexit.
  repeat rewrite <-Nat.sub_add_distr in Hxl, Hexit.
  pose proof (Nat.sub_add (m+2) (2^m*2) ltac:(nia)).
  lia.
Qed.

Lemma center_O0_carry_eq m x b:
  b+(x-(2*m+2))=2^(m+1)+4*m+4 ->
  b+(x-(m+m+2)+2^(m+2)-(m+m+2)) =
    3*2^(m+1)+m+m+2.
Proof.
  intros HE.
  replace (m+m+2) with (2*m+2) by lia.
  assert (2*m+2 <= x-(2*m+2)+2^(m+2)) as Hcut.
  { pose proof (pow2_twice (m+2)); lia. }
  pose proof (Nat.sub_add (2*m+2)
    (x-(2*m+2)+2^(m+2)) Hcut).
  assert (2^(m+2)=2*2^(m+1)) as HP.
  { replace (m+2) with (S (m+1)) by lia.
    cbn [Nat.pow]; nia. }
  rewrite HP in *.
  nia.
Qed.

Lemma center_O0 m x:
  8 <= m ->
  LH m <= x <= UH m ->
  exists b,
    10*m+12 <= b*2 <= 18*m+20 /\
    US m m x -->* Q (2*m+2) m b.
Proof.
  intros Hm.
  induction x using lt_wf_ind; intros HC.
  destruct HC as [Hxl Hxu].
  pose proof (pow2_center_gap m Hm).
  pose proof (center_sub_bound m Hm).
  pose proof (pow2_twice m).
  pose proof (LH_pred_gap m ltac:(lia)).
  pose proof (pred_bucket_adj m ltac:(lia)).
  assert (2*m+2 <= x) as Hsub by lia.
  pose proof (Nat.sub_add (2*m+2) x Hsub) as Hdrop.
  destruct (le_lt_dec (LH m) (x-(2*m+2))) as [Hstay|Hexit].
  - assert (x-(2*m+2) <= UH m) as Hxu'.
    { eapply Nat.le_trans.
      1: apply Nat.le_sub_l.
      exact Hxu. }
    destruct (H (x-(2*m+2)) ltac:(lia)
      (conj Hstay Hxu')) as [b [Hb HR]].
    exists b; split.
    1: exact Hb.
    follow U_same.
    1: lia.
    1: apply bucket_B with (k:=m); lia.
    replace (m+m+2) with (2*m+2) by lia.
    exact HR.
  - assert (LH (m-1) <= x-(2*m+2)) as Hbl.
    { exact (center_drop_lower2 m x Hm Hxl). }
    assert (x-(2*m+2) <= UH (m-1)) as Hbu by lia.
    pose proof (O0_up_range m (x-(2*m+2)) Hm ltac:(lia) Hexit)
      as [Hyl Hyu].
    set (b := 2^(m+1)+4*m+4-(x-(2*m+2))).
    assert (b+(x-(2*m+2))=2^(m+1)+4*m+4) as Hbdef.
    { unfold b; apply Nat.sub_add.
      unfold LH in Hexit.
      replace (m+1) with (S m) by lia.
      cbn [Nat.pow].
      lia. }
    assert (10*m+12 <= b*2 <= 18*m+20) as Hb.
    { exact (O0_b_bounds m x b Hm Hxl Hexit Hbdef). }
    assert (5 <= b) as Hb5 by lia.
    assert (b+1 <= 2^(2*m+3)+2^(m+1)) as Hbig.
    { pose proof (Nat.pow_le_mono_r 2 (m+2) (2*m+3)
        ltac:(lia) ltac:(lia)).
      pose proof (pow2_center_gap m Hm).
      assert (2^(m+2)=8*2^(m-1)).
      { replace (m+2) with ((m-1)+3) by lia.
        rewrite Nat.pow_add_r; cbn; nia. }
      lia. }
    assert (b+1 <= 2^(2*m+2+1)+2^(m+1)) as Hbig'.
    { applys_eq Hbig; flia. }
    exists b; split.
    1: exact Hb.
    follow U_same.
    1: lia.
    1: apply bucket_B with (k:=m); lia.
    follow U_up_i.
    1: lia.
    1: pose proof (pow2_twice (m+2)); lia.
    1: apply bucket_B with (k:=m-1); lia.
    1: apply bucket_B with (k:=m+1).
       1: lia.
       applys_eq Hyu; flia.
    1: replace (m+m+2) with (2*m+2) by lia.
       exact (conj Hbl Hbu).
    follow U_carry1.
    1: lia.
    1: applys_eq Hbig; flia.
    1: apply bucket_B with (k:=m+1).
       1: lia.
       applys_eq Hyu; flia.
    1: pose proof (Q_B (2*m+2) m b ltac:(lia) Hb5 Hbig') as HQ.
       applys_eq HQ; flia.
    1: applys_eq (conj Hyl Hyu); flia.
    1: exact (center_O0_carry_eq m x b Hbdef).
    finish.
Qed.

Lemma O_up1_union m x:
  8 <= m ->
  LH m <= x <= UH m ->
  LH m <= x+2^(m+1)-(2*m+2) <= UH (m+1).
Proof.
  intros Hm [Hxl Hxu].
  pose proof (bucket_width m).
  unfold LH, UH in *.
  replace (m+1) with (S m) in * by lia.
  cbn [Nat.pow] in *.
  pose proof (pow2_center_gap (S m) ltac:(lia)).
  pose proof (pow2_gt m).
  assert (2*m+2 <= x+2*2^m) as Hsub by lia.
  pose proof (Nat.sub_add (2*m+2) (x+2*2^m) Hsub).
  split; lia.
Qed.

Lemma O_drop1_bucket m x:
  8 <= m ->
  LH m <= x ->
  x-(2*m+2)*2 < LH m ->
  LH (m-1) <= x-(2*m+2)*2 <= UH (m-1).
Proof.
  intros Hm Hx He.
  pose proof (pow2_center_gap m Hm).
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  pose proof (LH_pred_gap m ltac:(lia)).
  pose proof (pred_bucket_adj m ltac:(lia)).
  assert ((2*m+2)*2 <= x) as Hsub.
  { unfold LH in Hx.
    assert (2^m*2=4*2^(m-1)).
    { replace m with (S (m-1)) at 1 by lia.
      cbn [Nat.pow]; nia. }
    lia. }
  pose proof (Nat.sub_add ((2*m+2)*2) x Hsub).
  pose proof (pow2_gt m).
  pose proof (Nat.sub_add 1 (2^m) ltac:(lia)).
  split.
  1: lia.
  1: lia.
Qed.

Lemma O_pair2_range m x:
  8 <= m ->
  LH (m-1) <= x <= UH (m-1) ->
  LH (m+1) <= x+3*2^(m+1)-(2*m+2) <= UH (m+1).
Proof.
  intros Hm [Hxl Hxu].
  rewrite LH_pred_eq in Hxl by lia.
  pose proof (pred_bucket_adj m ltac:(lia)).
  unfold LH, UH in *.
  replace (m+1) with (S m) by lia.
  cbn [Nat.pow] in *.
  pose proof (pow2_gt m).
  assert (2*m+2 <= x+3*(2*2^m)) as Hsub by lia.
  pose proof (Nat.sub_add (2*m+2) (x+3*(2*2^m)) Hsub).
  split; lia.
Qed.

Lemma O_drop2_bucket m x:
  8 <= m ->
  LH (m-1) <= x ->
  x-(2*m+2)*2 < LH (m-1) ->
  LH (m-2) <= x-(2*m+2)*2 <= UH (m-2).
Proof.
  intros Hm Hx He.
  pose proof (LH_pred_eq m ltac:(lia)).
  pose proof (pow2_center_gap m Hm).
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  assert ((2*m+2)*2 <= x) as Hsub by lia.
  pose proof (Nat.sub_add ((2*m+2)*2) x Hsub) as Hdrop.
  pose proof (LH_pred_gap (m-1) ltac:(lia)) as HL.
  pose proof (pred_bucket_adj (m-1) ltac:(lia)) as HA.
  replace (m-1-1) with (m-2) in HL, HA by lia.
  pose proof (pow2_center_gap5 m Hm) as HG5.
  pose proof (pow2_gt (m-1)) as HP0.
  pose proof (Nat.sub_add 1 (2^(m-1)) ltac:(lia)).
  split; lia.
Qed.

Lemma O_up3_range m x:
  8 <= m ->
  LH (m-1) <= x+(2*m+2)*2 ->
  x < LH (m-1) ->
  LH (m+2) <= x+7*2^(m+1)-(2*m+2) <= UH (m+2).
Proof.
  intros Hm Hlo Hhi.
  rewrite LH_pred_eq in Hlo, Hhi by lia.
  assert (2^(m+1)=2*2^m) as HP1.
  { replace (m+1) with (S m) by lia; cbn [Nat.pow]; nia. }
  assert (2^(m+2)=4*2^m) as HP2.
  { replace (m+2) with (S (S m)) by lia; cbn [Nat.pow]; nia. }
  unfold LH, UH.
  rewrite HP1, HP2.
  repeat rewrite <-Nat.sub_add_distr in *.
  pose proof (pow2_gt m).
  assert (2*m+2 <= x+7*(2*2^m)) as Hsub by lia.
  pose proof (Nat.sub_add (2*m+2) (x+7*(2*2^m)) Hsub).
  pose proof (Nat.sub_add (m+1) (2^m) ltac:(lia)).
  pose proof (Nat.sub_add (m+4) ((4*2^m)*2) ltac:(nia)).
  pose proof (Nat.sub_add (m+6) ((4*2^m)*4) ltac:(nia)).
  split.
  1: lia.
  1: lia.
Qed.

Lemma center_OB2_target_B m b:
  8 <= m ->
  5 <= b ->
  b+1 <= 2^(2*m+3)+2^m ->
  2^((m+1)+(m-1)+3)+2^(m-1+1)-b-1+6 <=
    B ((m+1)+1) (m-1).
Proof.
  intros Hm Hb Hbig.
  pose proof (Q_B (2*m+2) (m-1) b ltac:(lia) Hb) as HQ.
  replace (2*m+2+1) with (2*m+3) in HQ by lia.
  replace (m-1+1) with m in HQ by lia.
  specialize (HQ Hbig).
  replace (2*m+2-(m-1)-1) with (m+2) in HQ by lia.
  replace ((m+1)+(m-1)+3) with (2*m+3) by lia.
  replace (m-1+1) with m by lia.
  replace (m+1+1) with (m+2) by lia.
  exact HQ.
Qed.

Lemma center_OB2_carry_eq m x b:
  8 <= m ->
  b+(x-(2*m+2)*2)=2^m+4*m+4 ->
  b+(x-((m+1)+(m-1)+2)*2+7*2^(m-1+2)-
      ((m+1)+(m-1)+2)) =
    15*2^(m-1+1)+(m+1)+(m-1)+2.
Proof.
  intros Hm HE.
  replace (m-1+2) with (m+1) by lia.
  replace (m-1+1) with m by lia.
  replace ((m+1)+(m-1)+2) with (2*m+2) by lia.
  assert (2^(m+1)=2*2^m) as HP.
  { replace (m+1) with (S m) by lia; cbn [Nat.pow]; nia. }
  rewrite HP.
  pose proof (Nat.sub_add (2*m+2)
    (x-(2*m+2)*2+7*(2*2^m))
    ltac:(pose proof (pow2_gt m); nia)).
  nia.
Qed.

Lemma center_O_B2 m x:
  8 <= m ->
  LH (m-1) <= x <= UH (m-1) ->
  exists b,
    10*m+12 <= b*2 <= 18*m+20 /\
    US (m+1) (m-1) x -->* Q (2*m+2) (m-1) b.
Proof.
  intros Hm.
  induction x using lt_wf_ind; intros HC.
  destruct HC as [Hxl Hxu].
  pose proof (O_pair2_range m x Hm (conj Hxl Hxu)) as [Hyl Hyu].
  pose proof (LH_pred_eq m ltac:(lia)) as HL.
  pose proof (pow2_center_gap m Hm) as HG.
  assert (2^m=2*2^(m-1)) as HP.
  { replace m with (S (m-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  assert ((2*m+2)*2 <= x) as H2x by lia.
  pose proof (Nat.sub_add ((2*m+2)*2) x H2x) as Hdrop.
  destruct (le_lt_dec (LH (m-1)) (x-(2*m+2)*2)) as [Hstay|Hexit].
  - assert (x-(2*m+2)*2 <= UH (m-1)) as Hxu'.
    { eapply Nat.le_trans.
      1: apply Nat.le_sub_l.
      exact Hxu. }
    destruct (H (x-(2*m+2)*2) ltac:(lia)
      (conj Hstay Hxu')) as [b [Hb HR]].
    exists b; split.
    1: exact Hb.
    follow (U_pair2 (m+1) (m-1) x).
    1: lia.
    1: replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact H2x.
    1: apply bucket_B with (k:=m-1); lia.
    1: apply bucket_B with (k:=m+1).
       1: lia.
       replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact Hyu.
    1: replace (m+1-2) with (m-1) by lia.
       exact (conj Hxl Hxu).
    1: replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact (conj Hyl Hyu).
    replace (m+1+(m-1)+2) with (2*m+2) by lia.
    exact HR.
  - pose proof (O_drop2_bucket m x Hm Hxl Hexit) as [Hxtl Hxtu].
    pose proof (O_up3_range m (x-(2*m+2)*2) Hm ltac:(lia) Hexit)
      as [Hy3l Hy3u].
    set (b := 2^m+4*m+4-(x-(2*m+2)*2)).
    assert (b+(x-(2*m+2)*2)=2^m+4*m+4) as Hbdef.
    { unfold b; apply Nat.sub_add; lia. }
    assert (10*m+12 <= b*2 <= 18*m+20) as Hb by lia.
    assert (5 <= b) as Hb5 by lia.
    assert (b+1 <= 2^(2*m+3)+2^m) as Hbig.
    { pose proof (Nat.pow_le_mono_r 2 (m+2) (2*m+3)
        ltac:(lia) ltac:(lia)).
      assert (2^(m+2)=8*2^(m-1)).
      { replace (m+2) with ((m-1)+3) by lia.
        rewrite Nat.pow_add_r; cbn; nia. }
      lia. }
    assert (b+1 <= 2^(2*m+2+1)+2^(m-1+1)) as Hbig'.
    { replace (2*m+2+1) with (2*m+3) by lia.
      replace (m-1+1) with m by lia.
      exact Hbig. }
    exists b; split.
    1: exact Hb.
    follow (U_pair2 (m+1) (m-1) x).
    1: lia.
    1: replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact H2x.
    1: apply bucket_B with (k:=m-1); lia.
    1: apply bucket_B with (k:=m+1).
       1: lia.
       replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact Hyu.
    1: replace (m+1-2) with (m-1) by lia.
       exact (conj Hxl Hxu).
    1: replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact (conj Hyl Hyu).
    follow U_up3.
    1: lia.
    1: pose proof (pow2_gt (m+1)); lia.
    1: apply bucket_B with (k:=m-2).
       1: lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact Hxtu.
    1: apply bucket_B with (k:=m+2).
       1: lia.
       replace (m-1+3) with (m+2) by lia.
       replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact Hy3u.
    1: replace (m+1-3) with (m-2) by lia.
       replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact (conj Hxtl Hxtu).
    follow U_carry3.
    1: lia.
    1: replace (m+1+(m-1)+3) with (2*m+3) by lia.
       replace (m-1+1) with m by lia.
       exact Hbig.
    1: apply bucket_B with (k:=m+2).
       1: lia.
       replace (m-1+3) with (m+2) by lia.
       replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact Hy3u.
    1: exact (center_OB2_target_B m b Hm Hb5 Hbig).
    1: replace (m+1+1) with (m+2) by lia.
       replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact (conj Hy3l Hy3u).
    1: exact (center_OB2_carry_eq m x b Hm Hbdef).
    finish.
Qed.

Lemma center_O_B1 m x:
  8 <= m ->
  LH m <= x <= UH m ->
  exists k b,
    (k=m \/ k=m-1) /\
    10*m+12 <= b*2 <= 18*m+20 /\
    US (m+1) (m-1) x -->* Q (2*m+2) k b.
Proof.
  intros Hm.
  induction x using lt_wf_ind; intros HC.
  destruct HC as [Hxl Hxu].
  pose proof (O_up1_union m x Hm (conj Hxl Hxu)) as [Hyl Hyu].
  pose proof (pow2_center_gap m Hm).
  assert ((2*m+2)*2 <= x) as H2x.
  { unfold LH in Hxl.
    assert (2^m*2=4*2^(m-1)).
    { replace m with (S (m-1)) at 1 by lia.
      cbn [Nat.pow]; nia. }
    lia. }
  pose proof (Nat.sub_add ((2*m+2)*2) x H2x) as Hdrop.
  destruct (le_lt_dec
    (x+2^(m+1)-(2*m+2)) (UH m)) as [Hcentre|Hskip].
  - destruct (center_O0 m (x+2^(m+1)-(2*m+2)) Hm
      (conj Hyl Hcentre)) as [b [Hb HR]].
    exists m, b; repeat split; try lia.
    follow U_up_i.
    1: lia.
    1: pose proof (pow2_twice (m+1)); lia.
    1: apply bucket_B with (k:=m); lia.
    1: apply bucket_B with (k:=m).
       1: lia.
       replace (m-1+2) with (m+1) by lia.
       replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact Hcentre.
    1: replace (m+1-1) with m by lia.
       exact (conj Hxl Hxu).
    replace (m-1+2) with (m+1) by lia.
    replace (m+1+(m-1)+2) with (2*m+2) by lia.
    replace (m+1-1) with m by lia.
    replace (m-1+1) with m by lia.
    exact HR.
  - pose proof (pred_bucket_adj (m+1) ltac:(lia)) as HA.
    replace (m+1-1) with m in HA by lia.
    assert (LH (m+1) <= x+2^(m+1)-(2*m+2)) as Hys by lia.
    destruct (le_lt_dec (LH m) (x-(2*m+2)*2)) as [Hstay|Hexit].
    + assert (x-(2*m+2)*2 <= UH m) as Hxu'.
      { eapply Nat.le_trans.
        1: apply Nat.le_sub_l.
        exact Hxu. }
      destruct (H (x-(2*m+2)*2) ltac:(lia)
        (conj Hstay Hxu')) as [k [b [Hk [Hb HR]]]].
      exists k, b; split.
      1: exact Hk.
      split.
      1: exact Hb.
      follow (U_pair (2*m) (m-1) x).
      1: lia.
      1: apply bucket_B with (k:=m); lia.
      1: apply bucket_B with (k:=m+1).
         1: lia.
         replace (m-1+2) with (m+1) by lia.
         exact Hyu.
      1: replace (2*m-(m-1+1)) with m by lia.
         exact (conj Hxl Hxu).
      1: replace (2*m-(m-1)) with (m+1) by lia.
         replace (m-1+2) with (m+1) by lia.
         exact (conj Hys Hyu).
      replace (2*m-(m-1)) with (m+1) by lia.
      exact HR.
    + pose proof (O_drop1_bucket m x Hm Hxl Hexit) as [Hxtl Hxtu].
      destruct (center_O_B2 m (x-(2*m+2)*2) Hm
        (conj Hxtl Hxtu)) as [b [Hb HR]].
      exists (m-1), b; split.
      1: right; reflexivity.
      split.
      1: exact Hb.
      follow (U_pair (2*m) (m-1) x).
      1: lia.
      1: apply bucket_B with (k:=m); lia.
      1: apply bucket_B with (k:=m+1).
         1: lia.
         replace (m-1+2) with (m+1) by lia.
         exact Hyu.
      1: replace (2*m-(m-1+1)) with m by lia.
         exact (conj Hxl Hxu).
      1: replace (2*m-(m-1)) with (m+1) by lia.
         replace (m-1+2) with (m+1) by lia.
         exact (conj Hys Hyu).
      replace (2*m-(m-1)) with (m+1) by lia.
      exact HR.
Qed.

Lemma center_O_drop_lower m x:
  8 <= m -> LH (m+1) <= x -> LH m <= x-(2*m+2).
Proof.
  intros Hm Hx.
  pose proof (LH_pred_gap (m+1) ltac:(lia)) as HL.
  replace (m+1-1) with m in HL by lia.
  pose proof (pow2_center_gap (m+1) ltac:(lia)) as HG.
  replace (m+1-1) with m in HG by lia.
  assert (2^(m+1)=2*2^m) as HP.
  { replace (m+1) with (S m) by lia; cbn [Nat.pow]; nia. }
  pose proof (pow2_gt (m+1)) as HP0.
  pose proof (Nat.sub_add 1 (2^(m+1)) ltac:(lia)) as HP1.
  assert (2*m+2 <= 2^(m+1)-1) as Hcut by nia.
  assert (LH m+(2*m+2) <= x) as Hsum by lia.
  pose proof (Nat.sub_add (2*m+2) x ltac:(lia)).
  lia.
Qed.

Lemma center_O m x:
  8 <= m ->
  LH (m+1) <= x <= UH (m+1) ->
  exists k b,
    (k=m \/ k=m-1) /\
    10*m+12 <= b*2 <= 18*m+20 /\
    US (m+1) (m-1) x -->* Q (2*m+2) k b.
Proof.
  intros Hm.
  induction x using lt_wf_ind; intros HC.
  destruct HC as [Hxl Hxu].
  pose proof (pow2_center_gap (m+1) ltac:(lia)).
  pose proof (center_sub_bound (m+1) ltac:(lia)).
  pose proof (LH_pred_gap (m+1) ltac:(lia)).
  pose proof (pred_bucket_adj (m+1) ltac:(lia)).
  assert (2*m+2 <= x) as Hsub by lia.
  pose proof (Nat.sub_add (2*m+2) x Hsub).
  destruct (le_lt_dec (LH (m+1)) (x-(2*m+2))) as [Hstay|Hexit].
  - assert (x-(2*m+2) <= UH (m+1)) as Hxu'.
    { eapply Nat.le_trans.
      1: apply Nat.le_sub_l.
      exact Hxu. }
    destruct (H (x-(2*m+2)) ltac:(lia)
      (conj Hstay Hxu')) as [k [b [Hk [Hb HR]]]].
    exists k, b; split.
    1: exact Hk.
    split.
    1: exact Hb.
    follow U_same.
    1: replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact Hsub.
    1: apply bucket_B with (k:=m+1); lia.
    replace (m+1+(m-1)+2) with (2*m+2) by lia.
    exact HR.
  - assert (LH m <= x-(2*m+2)) as Hbl.
    { exact (center_O_drop_lower m x Hm Hxl). }
    assert (x-(2*m+2) <= UH m) as Hbu.
    { replace m with (m+1-1) by lia; lia. }
    destruct (center_O_B1 m (x-(2*m+2)) Hm (conj Hbl Hbu))
      as [k [b [Hk [Hb HR]]]].
    exists k, b; split.
    1: exact Hk.
    split.
    1: exact Hb.
    follow U_same.
    1: replace (m+1+(m-1)+2) with (2*m+2) by lia.
       exact Hsub.
    1: apply bucket_B with (k:=m+1); lia.
    replace (m+1+(m-1)+2) with (2*m+2) by lia.
    exact HR.
Qed.

Lemma U_stages i p t x:
  t <= i ->
  (forall q, q < t -> Far (i-q) (p+q)) ->
  LH i <= x <= UH i ->
  exists y, LH (i-t) <= y <= UH (i-t) /\
    US i p x -->* US (i-t) (p+t) y.
Proof.
  gen i p x.
  induction t; intros.
  1: exists x; cbn; split.
     1: rewrite Nat.sub_0_r; exact H1.
     finish.
  assert (Far i p) as HF0.
  { pose proof (H0 0 ltac:(lia)) as HFq.
    rewrite Nat.sub_0_r, Nat.add_0_r in HFq.
    exact HFq. }
  destruct (U_stage i p x HF0 H1)
    as [y [Hy HR0]].
  assert (forall q, q<t -> Far (i-1-q) (p+1+q)) as HF.
  { intros q Hq.
    applys_eq (H0 (q+1) ltac:(lia)); flia. }
  destruct (IHt (i-1) (p+1) y ltac:(lia) HF Hy)
    as [z [Hz HR1]].
  exists z; split.
  1: applys_eq Hz; flia.
  follow HR0.
  applys_eq HR1; flia.
Qed.

Lemma even_prefix_far m q:
  8 <= m -> q < m-1 ->
  Far (2*m-1-q) q.
Proof.
  intros Hm Hq.
  unfold Far.
  pose proof (Nat.pow_le_mono_r 2 (q+2) m ltac:(lia) ltac:(lia)).
  pose proof (Nat.pow_le_mono_r 2 (m+1) (2*m-1-q)
    ltac:(lia) ltac:(lia)).
  pose proof (pow2_triple_plus1 m ltac:(lia)).
  assert (2^(m+1)=2*2^m).
  { replace (m+1) with (S m) by lia; cbn [Nat.pow]; nia. }
  lia.
Qed.

Lemma odd_prefix_far m q:
  8 <= m -> q < m-1 ->
  Far (2*m-q) q.
Proof.
  intros Hm Hq.
  unfold Far.
  pose proof (Nat.pow_le_mono_r 2 (q+2) m ltac:(lia) ltac:(lia)).
  pose proof (Nat.pow_le_mono_r 2 (m+2) (2*m-q)
    ltac:(lia) ltac:(lia)).
  pose proof (pow2_twice m).
  assert (2^(m+2)=4*2^m).
  { replace (m+2) with (S (S m)) by lia; cbn [Nat.pow]; nia. }
  lia.
Qed.

Lemma pow2_14_linear k:
  6 <= k -> 14*k+28 <= 2^(k+2).
Proof.
  intros Hk.
  assert (exists q, k=6+q) by (exists (k-6); lia).
  destruct H as [q ->].
  clear Hk.
  induction q.
  1: cbn; lia.
  replace (6+S q+2) with (S (6+q+2)) by lia.
  cbn [Nat.pow].
  eapply Nat.le_trans with (2*(14*(6+q)+28)).
  2: apply Nat.mul_le_mono_l; exact IHq.
  lia.
Qed.

Lemma pow2_9_linear n:
  8 <= n -> 9*n <= 2^n.
Proof.
  intros Hn.
  assert (exists q, n=8+q) by (exists (n-8); lia).
  destruct H as [q ->].
  clear Hn.
  induction q.
  1: cbn; lia.
  replace (8+S q) with (S (8+q)) by lia.
  cbn [Nat.pow].
  eapply Nat.le_trans with (2*(9*(8+q))).
  2: apply Nat.mul_le_mono_l; exact IHq.
  lia.
Qed.

Lemma pow2_12_linear n:
  8 <= n -> 12*n <= 2^n.
Proof.
  intros Hn.
  assert (exists q, n=8+q) by (exists (n-8); lia).
  destruct H as [q ->].
  clear Hn.
  induction q.
  1: cbn; lia.
  replace (8+S q) with (S (8+q)) by lia.
  cbn [Nat.pow].
  eapply Nat.le_trans with (2*(12*(8+q))).
  2: apply Nat.mul_le_mono_l; exact IHq.
  lia.
Qed.

Definition EntryX n k b :=
  2^(n+1)-2^(k+1)-b-2*n+1.

Definition AfterFC n k b :=
  (2^n*4-n-3-((2^(n+1)+2^(k+1)-b)*2)/2)*2-
    (b*2-8)*2-8.

Definition AfterFD n k b :=
  (3+((2^(n+1)+2^(k+1)-b)*2-
    (2^n*4-n*2-3)))*2+(b*2-8)*4+5.

Lemma Q_entry_F_range n k b:
  16 <= n ->
  k+2 <= n ->
  n <= 2*k+4 ->
  5*n+2 <= b*2 <= 9*n+2 ->
  L n <= (2^(n+1)+2^(k+1)-b)*2 < L (S n).
Proof.
  intros Hn Hkn Hnk Hb.
  pose proof (pow2_14_linear k ltac:(lia)) as HK.
  pose proof (pow2_center_gap n ltac:(lia)) as HN.
  pose proof (pow2_12_linear n ltac:(lia)) as H12.
  pose proof (pow2_9_linear n ltac:(lia)) as H9.
  pose proof (Nat.pow_le_mono_r 2 (k+1) (n-1)
    ltac:(lia) ltac:(lia)) as Hpow.
  assert (2^n=2*2^(n-1)) as HPn.
  { replace n with (S (n-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  assert (2^(n+1)=2*2^n) as HPn1.
  { replace (n+1) with (S n) by lia; cbn [Nat.pow]; nia. }
  assert (2^(k+2)=2*2^(k+1)) as HPk.
  { replace (k+2) with (S (k+1)) by lia.
    cbn [Nat.pow]; nia. }
  pose proof (Nat.sub_add b (2^(n+1)+2^(k+1)) ltac:(lia)) as Hsub.
  unfold L.
  cbn [Nat.pow].
  repeat rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add (n*2+3) (2^n*4) ltac:(nia)).
  pose proof (Nat.sub_add (S n*2+3) ((2^n*2)*4) ltac:(nia)).
  nia.
Qed.

Lemma AfterFC_balance n k b:
  16 <= n ->
  k+2 <= n ->
  n <= 2*k+4 ->
  5*n+2 <= b*2 <= 9*n+2 ->
  AfterFC n k b+2^(k+2)+b*2+2*n=2^(n+2)+2.
Proof.
  intros Hn Hkn Hnk Hb.
  pose proof (pow2_center_gap n ltac:(lia)) as HN.
  pose proof (pow2_9_linear n ltac:(lia)) as H9.
  pose proof (Nat.pow_le_mono_r 2 (k+1) (n-1)
    ltac:(lia) ltac:(lia)) as Hpow.
  assert (2^n=2*2^(n-1)) as HPn0.
  { replace n with (S (n-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  assert (2^(n+1)=2*2^n) as HPn1.
  { replace (n+1) with (S n) by lia; cbn [Nat.pow]; nia. }
  assert (2^(k+2)=2*2^(k+1)) as HPk.
  { replace (k+2) with (S (k+1)) by lia.
    cbn [Nat.pow]; nia. }
  assert (2^(n+2)=4*2^n) as HPn2.
  { replace (n+2) with (S (S n)) by lia; cbn [Nat.pow]; nia. }
  unfold AfterFC.
  rewrite Nat.div_mul by lia.
  repeat rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add b
    (2^(n+1)+2^(k+1)) ltac:(lia)) as Hpb.
  pose proof (Nat.le_sub_l b (2^(n+1)+2^(k+1))) as Hple.
  assert (n+(3+(2^(n+1)+2^(k+1)-b)) <= 2^n*4)
    as Hinnerb by lia.
  pose proof (Nat.sub_add
    (n+(3+(2^(n+1)+2^(k+1)-b))) (2^n*4) Hinnerb)
    as Hinner.
  pose proof (Nat.sub_add 8 (b*2) ltac:(lia)) as Hb8.
  assert ((b*2-8)*2+8 <=
    (2^n*4-(n+(3+(2^(n+1)+2^(k+1)-b))))*2)
    as Houterb by lia.
  pose proof (Nat.sub_add ((b*2-8)*2+8)
    ((2^n*4-(n+(3+(2^(n+1)+2^(k+1)-b))))*2)
    Houterb) as Houter.
  clear Hn Hkn Hnk Hb HN H9 Hpow Hinnerb Houterb Hple.
  nia.
Qed.

Lemma AfterFD_balance n k b:
  16 <= n ->
  k+2 <= n ->
  n <= 2*k+4 ->
  5*n+2 <= b*2 <= 9*n+2 ->
  AfterFD n k b+15=2^(k+3)+b*4+4*n.
Proof.
  intros Hn Hkn Hnk Hb.
  pose proof (Q_entry_F_range n k b Hn Hkn Hnk Hb) as [HFlo HFhi].
  pose proof (pow2_9_linear n ltac:(lia)) as H9.
  assert (2^(n+1)=2*2^n) as HPn1.
  { replace (n+1) with (S n) by lia; cbn [Nat.pow]; nia. }
  assert (2^(k+3)=4*2^(k+1)) as HPk3.
  { replace (k+3) with (S (S (k+1))) by lia.
    cbn [Nat.pow]; nia. }
  unfold L in HFlo.
  cbn [Nat.pow] in HFlo.
  repeat rewrite <-Nat.sub_add_distr in HFlo.
  unfold AfterFD.
  repeat rewrite <-Nat.sub_add_distr.
  assert (b <= 2^(n+1)+2^(k+1)) as Hbsum by nia.
  pose proof (Nat.sub_add b
    (2^(n+1)+2^(k+1)) Hbsum) as Hpb.
  pose proof (Nat.sub_add (n*2+3) (2^n*4) ltac:(lia)) as HL.
  pose proof (Nat.sub_add (2^n*4-(n*2+3))
    ((2^(n+1)+2^(k+1)-b)*2) HFlo) as Hright.
  pose proof (Nat.sub_add 8 (b*2) ltac:(lia)) as Hb8.
  clear Hn Hkn Hnk Hb HFlo HFhi.
  nia.
Qed.

Lemma Q_entry_T_sum n k b:
  16 <= n ->
  k+2 <= n ->
  n <= 2*k+4 ->
  5*n+2 <= b*2 <= 9*n+2 ->
  2^(n-1)*8-(n-1)*2-5 <= AfterFC n k b+AfterFD n k b.
Proof.
  intros Hn Hkn Hnk Hb.
  pose proof (AfterFC_balance n k b Hn Hkn Hnk Hb) as HC.
  pose proof (AfterFD_balance n k b Hn Hkn Hnk Hb) as HD.
  assert (2^(k+3)=2*2^(k+2)) as HPk.
  { replace (k+3) with (S (k+2)) by lia; cbn [Nat.pow]; nia. }
  assert (2^(n-1)*8=2^(n+2)) as HPn.
  { replace (n+2) with ((n-1)+3) by lia.
    rewrite Nat.pow_add_r; cbn; nia. }
  pose proof (Nat.sub_add ((n-1)*2+5) (2^(n-1)*8)
    ltac:(pose proof (pow2_center_gap n ltac:(lia)); lia)) as Hbase.
  lia.
Qed.

Lemma Q_entry_T_equation n k b:
  16 <= n ->
  k+2 <= n ->
  n <= 2*k+4 ->
  5*n+2 <= b*2 <= 9*n+2 ->
  (2^(k+1)+b+2*n-5)*2+1 =
    AfterFC n k b+AfterFD n k b-
      (2^(n-1)*8-(n-1)*2-6).
Proof.
  intros Hn Hkn Hnk Hb.
  pose proof (AfterFC_balance n k b Hn Hkn Hnk Hb) as HC.
  pose proof (AfterFD_balance n k b Hn Hkn Hnk Hb) as HD.
  pose proof (Q_entry_T_sum n k b Hn Hkn Hnk Hb) as HS.
  assert (2^(k+2)=2*2^(k+1)) as HPk2.
  { replace (k+2) with (S (k+1)) by lia; cbn [Nat.pow]; nia. }
  assert (2^(k+3)=2*2^(k+2)) as HPk3.
  { replace (k+3) with (S (k+2)) by lia; cbn [Nat.pow]; nia. }
  assert (2^(n-1)*8=2^(n+2)) as HPn.
  { replace (n+2) with ((n-1)+3) by lia.
    rewrite Nat.pow_add_r; cbn; nia. }
  repeat rewrite <-Nat.sub_add_distr in HS |- *.
  pose proof (Nat.sub_add ((n-1)*2+6) (2^(n-1)*8)
    ltac:(pose proof (pow2_center_gap n ltac:(lia)); lia)) as Hbase.
  assert (2^(n-1)*8-((n-1)*2+6) <=
    AfterFC n k b+AfterFD n k b) as Hle by lia.
  pose proof (Nat.sub_add (2^(n-1)*8-((n-1)*2+6))
    (AfterFC n k b+AfterFD n k b) Hle) as Hdiff.
  lia.
Qed.

Lemma Q_entry n k b:
  16 <= n ->
  k+2 <= n ->
  n <= 2*k+4 ->
  5*n+2 <= b*2 <= 9*n+2 ->
  Q n k b -->+ US (n-1) 0 (EntryX n k b).
Proof.
  intros Hn Hkn Hnk Hb.
  assert (6 <= k) as Hk by lia.
  pose proof (pow2_14_linear k Hk) as HK.
  pose proof (pow2_center_gap n ltac:(lia)) as HN.
  pose proof (pow2_9_linear n ltac:(lia)) as H9.
  pose proof (Nat.pow_le_mono_r 2 (k+1) (n-1)
    ltac:(lia) ltac:(lia)) as Hpow.
  assert (2^(n+1)=4*2^(n-1)) as HPn.
  { replace (n+1) with ((n-1)+2) by lia.
    rewrite Nat.pow_add_r; cbn; nia. }
  assert (2^n=2*2^(n-1)) as HPn0.
  { replace n with (S (n-1)) at 1 by lia.
    cbn [Nat.pow]; nia. }
  assert (2^(k+2)=2*2^(k+1)) as HPk.
  { replace (k+2) with (S (k+1)) by lia.
    cbn [Nat.pow]; nia. }
  assert (5 <= b) as Hb5 by lia.
  assert (b+1 <= 2^(n+1)+2^(k+1)) as Hsum by lia.
  rewrite (Q_eq n k b ltac:(lia) Hb5 Hsum).
  unfold QR.
  replace ((b-5)*4+6) with (1+((b-5)*4+5)) by lia.
  eapply progress_evstep_trans.
  1: eapply (EventF_progress n
    ((2^(n+1)+2^(k+1)-b)*2)
    ((b-5)*4+5) (b*2-8)).
  1: lia.
  1: exact (Q_entry_F_range n k b Hn Hkn Hnk Hb).
  1: apply Nat.Div0.mod_mul.
  1: pose proof (Nat.sub_add 5 b Hb5); nia.
  1: rewrite Nat.div_mul by lia.
     pose proof (Nat.sub_add b (2^(n+1)+2^(k+1)) ltac:(lia)).
     pose proof (Nat.sub_add 8 (b*2) ltac:(lia)).
     repeat rewrite <-Nat.sub_add_distr.
     pose proof (Nat.le_sub_l b (2^(n+1)+2^(k+1))).
     pose proof (Nat.sub_add
       (n+3+(2^(n+1)+2^(k+1)-b)) (2^n*4) ltac:(lia)).
     nia.
  replace
    ((3+((2^(n+1)+2^(k+1)-b)*2-
      (2^n*4-n*2-3)))*2+(b*2-8)*4+6)
    with (1+AfterFD n k b) by (unfold AfterFD; nia).
  follow (EventT (n-1) 0 (AfterFC n k b) (AfterFD n k b)
    (2^(k+1)+b+2*n-5)).
  1: unfold L, EntryX, AfterFC, AfterFD in *.
     cbn [Nat.pow] in *.
     rewrite Nat.div_mul by lia.
     repeat rewrite <-Nat.sub_add_distr in *.
     pose proof (Nat.sub_add b
       (2^(n+1)+2^(k+1)) ltac:(lia)) as Hpb.
     pose proof (Nat.le_sub_l b (2^(n+1)+2^(k+1))) as Hple.
     assert (n+(3+(2^(n+1)+2^(k+1)-b)) <= 2^n*4)
       as Hinnerb by lia.
     pose proof (Nat.sub_add
       (n+(3+(2^(n+1)+2^(k+1)-b))) (2^n*4) Hinnerb)
       as Hinner.
     pose proof (Nat.sub_add 8 (b*2) ltac:(lia)) as Hb8.
     assert ((b*2-8)*2+8 <=
       (2^n*4-(n+(3+(2^(n+1)+2^(k+1)-b))))*2)
       as Houterb by lia.
     pose proof (Nat.sub_add ((b*2-8)*2+8)
       ((2^n*4-(n+(3+(2^(n+1)+2^(k+1)-b))))*2)
       Houterb) as Houter.
     pose proof (Nat.sub_add ((n-1)*2+3) (2^(n-1)*4)
       ltac:(lia)) as Hlow.
     pose proof (Nat.sub_add (S (n-1)*2+3)
       ((2*2^(n-1))*4) ltac:(lia)) as Hhigh.
     split.
     1: lia.
     1: lia.
  1: unfold AfterFC.
     rewrite Nat.div_mul by lia.
     replace 8 with (4*2) by lia.
     repeat rewrite <-PeanoNat.Nat.mul_sub_distr_r.
     apply Nat.Div0.mod_mul.
  1: exact (Q_entry_T_sum n k b Hn Hkn Hnk Hb).
  1: cbn [Nat.pow].
     replace
       (2*(2^(n-1)*4+1+1)*(1-1)-2*0) with 0 by lia.
     cbn.
     exact (Q_entry_T_equation n k b Hn Hkn Hnk Hb).
  1: cbn [Nat.pow].
     lia.
  unfold EntryX, US, UC, UD.
  rewrite B_expand.
  replace (n-1+0) with (n-1) by lia.
  cbn [Nat.pow].
  finish.
Qed.

Lemma EntryX_bucket n k b:
  16 <= n ->
  k+2 <= n ->
  n <= 2*k+4 ->
  5*n+2 <= b*2 <= 9*n+2 ->
  LH (n-1) <= EntryX n k b <= UH (n-1).
Proof.
  intros Hn Hkn Hnk Hb.
  pose proof (pow2_14_linear k ltac:(lia)) as HK.
  pose proof (pow2_center_gap n ltac:(lia)) as HN.
  pose proof (pow2_12_linear n ltac:(lia)) as H12.
  pose proof (Nat.pow_le_mono_r 2 (k+1) (n-1)
    ltac:(lia) ltac:(lia)) as Hpow.
  assert (2^(n+1)=4*2^(n-1)) as HPn.
  { replace (n+1) with ((n-1)+2) by lia.
    rewrite Nat.pow_add_r; cbn; nia. }
  assert (2^(k+2)=2*2^(k+1)) as HPk.
  { replace (k+2) with (S (k+1)) by lia.
    cbn [Nat.pow]; nia. }
  assert (2^(k+1)+b+2*n <= 2^(n+1)) as Hsub by lia.
  pose proof (Nat.sub_add (2^(k+1)+b+2*n) (2^(n+1)) Hsub).
  unfold EntryX, LH, UH.
  assert (2^(n-1)*2=2^n).
  { replace n with ((n-1)+1) at 2 by lia.
    rewrite Nat.pow_add_r; cbn; nia. }
  repeat rewrite <-Nat.sub_add_distr.
  pose proof (Nat.sub_add ((n-1)+2) (2^(n-1)*2) ltac:(lia)).
  pose proof (Nat.sub_add ((n-1)+4) (2^(n-1)*4) ltac:(lia)).
  split.
  1: lia.
  1: lia.
Qed.

Lemma prefix_E m x:
  8 <= m ->
  LH (2*m-1) <= x <= UH (2*m-1) ->
  exists y, LH m <= y <= UH m /\
    US (2*m-1) 0 x -->* US m (m-1) y.
Proof.
  intros Hm HC.
  assert (forall q, q<m-1 -> Far (2*m-1-q) (0+q)) as HF.
  { intros q Hq. replace (0+q) with q by lia.
    apply even_prefix_far; lia. }
  destruct (U_stages (2*m-1) 0 (m-1) x ltac:(lia) HF HC)
    as [y [Hy HR]].
  exists y; split.
  1: replace (2*m-1-(m-1)) with m in Hy by lia.
     exact Hy.
  replace (2*m-1-(m-1)) with m in HR by lia.
  replace (0+(m-1)) with (m-1) in HR by lia.
  exact HR.
Qed.

Lemma prefix_O m x:
  8 <= m ->
  LH (2*m) <= x <= UH (2*m) ->
  exists y, LH (m+1) <= y <= UH (m+1) /\
    US (2*m) 0 x -->* US (m+1) (m-1) y.
Proof.
  intros Hm HC.
  assert (forall q, q<m-1 -> Far (2*m-q) (0+q)) as HF.
  { intros q Hq. replace (0+q) with q by lia.
    apply odd_prefix_far; lia. }
  destruct (U_stages (2*m) 0 (m-1) x ltac:(lia) HF HC)
    as [y [Hy HR]].
  exists y; split.
  1: replace (2*m-(m-1)) with (m+1) in Hy by lia.
     exact Hy.
  replace (2*m-(m-1)) with (m+1) in HR by lia.
  replace (0+(m-1)) with (m-1) in HR by lia.
  exact HR.
Qed.

Lemma reset_E m k b:
  8 <= m ->
  (k=m-2 \/ k=m-1) ->
  10*m+2 <= b*2 <= 18*m+2 ->
  exists b',
    10*m+7 <= b'*2 <= 18*m+11 /\
    Q (2*m) k b -->+ Q (2*m+1) (m-1) b'.
Proof.
  intros Hm Hk Hb.
  assert (k+2 <= 2*m) as Hkn by (destruct Hk; lia).
  assert (2*m <= 2*k+4) as Hnk by (destruct Hk; lia).
  assert (5*(2*m)+2 <= b*2 <= 9*(2*m)+2) as Hbb by lia.
  pose proof (EntryX_bucket (2*m) k b ltac:(lia) Hkn Hnk Hbb) as HC.
  destruct (prefix_E m (EntryX (2*m) k b) Hm HC)
    as [x [Hx HR0]].
  destruct (center_E m x Hm Hx) as [b' [Hb' HR1]].
  exists b'; split.
  1: exact Hb'.
  follow10 (Q_entry (2*m) k b ltac:(lia) Hkn Hnk Hbb).
  follow HR0.
  exact HR1.
Qed.

Lemma reset_O m b:
  8 <= m ->
  10*m+7 <= b*2 <= 18*m+11 ->
  exists k' b',
    (k'=m \/ k'=m-1) /\
    10*m+12 <= b'*2 <= 18*m+20 /\
    Q (2*m+1) (m-1) b -->+ Q (2*m+2) k' b'.
Proof.
  intros Hm Hb.
  assert ((m-1)+2 <= 2*m+1) as Hkn by lia.
  assert (2*m+1 <= 2*(m-1)+4) as Hnk by lia.
  assert (5*(2*m+1)+2 <= b*2 <= 9*(2*m+1)+2) as Hbb by lia.
  pose proof (EntryX_bucket (2*m+1) (m-1) b ltac:(lia)
    Hkn Hnk Hbb) as HC.
  destruct (prefix_O m (EntryX (2*m+1) (m-1) b) Hm
    ltac:(replace (2*m+1-1) with (2*m) in HC by lia; exact HC))
    as [x [Hx HR0]].
  destruct (center_O m x Hm Hx) as [k' [b' [Hk' [Hb' HR1]]]].
  exists k', b'; split.
  1: exact Hk'.
  split.
  1: exact Hb'.
  follow10 (Q_entry (2*m+1) (m-1) b ltac:(lia) Hkn Hnk Hbb).
  follow HR0.
  exact HR1.
Qed.

Inductive ResetIndex :=
| ResetEven (m k b:nat)
| ResetOdd (m b:nat).

Definition reset_config r :=
  match r with
  | ResetEven m k b => Q (2*m) k b
  | ResetOdd m b => Q (2*m+1) (m-1) b
  end.

Definition reset_good r :=
  match r with
  | ResetEven m k b =>
      8 <= m /\
      (k=m-2 \/ k=m-1) /\
      10*m+2 <= b*2 <= 18*m+2
  | ResetOdd m b =>
      8 <= m /\
      10*m+7 <= b*2 <= 18*m+11
  end.

Lemma reset_step r:
  reset_good r ->
  exists r',
    reset_config r -->+ reset_config r' /\
    reset_good r'.
Proof.
  destruct r as [m k b|m b]; cbn [reset_good reset_config].
  - intros [Hm [Hk Hb]].
    destruct (reset_E m k b Hm Hk Hb) as [b' [Hb' HR]].
    exists (ResetOdd m b'); cbn [reset_config reset_good].
    auto.
  - intros [Hm Hb].
    destruct (reset_O m b Hm Hb)
      as [k' [b' [Hk' [Hb' HR]]]].
    exists (ResetEven (m+1) k' b'); cbn [reset_config reset_good].
    split.
    1: replace (2*(m+1)) with (2*m+2) by lia; exact HR.
    repeat split; try lia.
Qed.

Lemma stable_nonhalt:
  ~halts tm (Q 16 6 51).
Proof.
  eapply progress_nonhalt_cond with
    (i0:=ResetEven 8 6 51)
    (C:=reset_config) (P:=reset_good).
  2: cbn [reset_good]; lia.
  intros r Hr.
  destruct (reset_step r Hr) as [r' [Hstep Hgood]].
  exists r'; auto.
Qed.

Open Scope nat_scope.
Open Scope bool_scope.

Inductive HState :=
| HS2 (c d:nat)
| HUS (i j x:nat).

Definition hconfig s :=
  match s with
  | HS2 c d => S2 1 0 c d
  | HUS i j x => US i j x
  end.

Inductive HRule :=
| RSames (i j m x:nat)
| RNext (ip jp x i j y:nat)
| RF (i c d q:nat)
| RT (i j c d q:nat)
| RConv (i j x c d:nat).

Definition rule_src r :=
  match r with
  | RSames i j m x => HUS i j x
  | RNext ip jp x i j y => HUS ip jp x
  | RF i c d q => HS2 c (1+d)
  | RT i j c d q => HS2 c (1+d)
  | RConv i j x c d => HUS i j x
  end.

Definition rule_dst r :=
  match r with
  | RSames i j m x => HUS i j (x-m*(i+j+2))
  | RNext ip jp x i j y => HUS i j y
  | RF i c d q =>
      HS2 ((Nat.pow 2 i*4-i-3-Nat.div c 2)*2-q*2-8)
        ((3+(c-(Nat.pow 2 i*4-i*2-3)))*2+q*4+6)
  | RT i j c d q =>
      HUS i j (A i j-q-5)
  | RConv i j x c d => HS2 c d
  end.

Definition RuleValid r :=
  match r with
  | RSames i j m x =>
      m*(i+j+2) <= x /\
      LH i <= x-m*(i+j+2) /\
      x <= UH i /\
      x+6 <= B i j
  | RNext ip jp x i j y =>
      x+6 <= B ip jp /\
      y+6 <= B i j /\
      LH i <= x /\ x <= UH i /\
      x+(B i j)*2 = y+(B ip jp)*2+i+j+2
  | RF i c d q =>
      L i <= c /\ c < L (S i) /\
      Nat.modulo c 2 = 0 /\
      d = q*2+1 /\
      q+5 <= Nat.pow 2 i*4-i-3-Nat.div c 2
  | RT i j c d q =>
      L i <= c /\ c < L (S i) /\
      Nat.modulo c 2 = 0 /\
      Nat.pow 2 i*8-i*2-5 <= c+d /\
      (2*((Nat.pow 2 i*4+1)+1)*(Nat.pow 2 j-1)-2*j)+(q*2+1) =
        c+d-(Nat.pow 2 i*8-i*2-6) /\
      q+5 <= ((Nat.pow 2 i*4+1)+1)*Nat.pow 2 j-1
  | RConv i j x c d => UC i j x = c /\ UD i j x = d
  end.

Definition rule_valid r :=
  match r with
  | RSames i j m x =>
      Nat.leb (m*(i+j+2)) x &&
      Nat.leb (LH i) (x-m*(i+j+2)) &&
      Nat.leb x (UH i) &&
      Nat.leb (x+6) (B i j)
  | RNext ip jp x i j y =>
      Nat.leb (x+6) (B ip jp) &&
      Nat.leb (y+6) (B i j) &&
      Nat.leb (LH i) x && Nat.leb x (UH i) &&
      Nat.eqb (x+(B i j)*2) (y+(B ip jp)*2+i+j+2)
  | RF i c d q =>
      Nat.leb (L i) c && Nat.ltb c (L (S i)) &&
      Nat.eqb (Nat.modulo c 2) 0 &&
      Nat.eqb d (q*2+1) &&
      Nat.leb (q+5) (Nat.pow 2 i*4-i-3-Nat.div c 2)
  | RT i j c d q =>
      Nat.leb (L i) c && Nat.ltb c (L (S i)) &&
      Nat.eqb (Nat.modulo c 2) 0 &&
      Nat.leb (Nat.pow 2 i*8-i*2-5) (c+d) &&
      Nat.eqb ((2*((Nat.pow 2 i*4+1)+1)*(Nat.pow 2 j-1)-2*j)+(q*2+1))
        (c+d-(Nat.pow 2 i*8-i*2-6)) &&
      Nat.leb (q+5) (((Nat.pow 2 i*4+1)+1)*Nat.pow 2 j-1)
  | RConv i j x c d =>
      Nat.eqb (UC i j x) c && Nat.eqb (UD i j x) d
  end.

Lemma rule_valid_spec r:
  rule_valid r = true <-> RuleValid r.
Proof.
  destruct r; cbn [rule_valid RuleValid];
    repeat rewrite Bool.andb_true_iff;
    repeat rewrite Nat.leb_le;
    repeat rewrite Nat.ltb_lt;
    repeat rewrite Nat.eqb_eq;
    tauto.
Qed.

Lemma rule_sound r:
  RuleValid r ->
  hconfig (rule_src r) -->* hconfig (rule_dst r).
Proof.
  destruct r as [i j m x|ip jp x i j y|i c d q|i j c d q|i j x c d];
    cbn [RuleValid rule_src rule_dst hconfig]; intros.
  - apply U_sames; tauto.
  - apply U_next; tauto.
  - apply EventF; tauto.
  - follow (EventT i j c d q); try tauto.
    unfold US, UC, UD, A, B.
    set (p := (Nat.pow 2 i*4+1+1)*Nat.pow 2 j) in *.
    assert (Hq: q+5 <= p-1) by tauto.
    assert (Hx: p-1-q-5+(q+5)=p-1).
    { rewrite <-Nat.sub_add_distr. apply Nat.sub_add; exact Hq. }
    assert (Hp: p-1+1=p).
    { apply Nat.sub_add. pose proof (Nat.le_sub_l 1 p); lia. }
    assert (HC: (p-1)*2-q*2-8+(q*2+8)=(p-1)*2).
    { rewrite <-Nat.sub_add_distr. apply Nat.sub_add; nia. }
    assert (HD: p-(p-1-q-5)-6+((p-1-q-5)+6)=p).
    { rewrite <-Nat.sub_add_distr. apply Nat.sub_add; lia. }
    replace ((p-1-q-5)*2+2) with ((p-1)*2-q*2-8) by nia.
    replace ((p-(p-1-q-5)-6)*4+6) with (q*4+6) by nia.
    finish.
  - destruct H as [Hc Hd].
    subst c d; unfold US; finish.
Qed.

Definition HState_eq_dec (x y:HState): {x=y}+{x<>y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition apply_rule s r :=
  if HState_eq_dec s (rule_src r) then
    if rule_valid r then Some (rule_dst r) else None
  else None.

Lemma apply_rule_sound s r s':
  apply_rule s r = Some s' ->
  hconfig s -->* hconfig s'.
Proof.
  unfold apply_rule.
  destruct (HState_eq_dec s (rule_src r)) as [->|Hneq].
  2: discriminate.
  destruct (rule_valid r) eqn:Hv.
  2: discriminate.
  intros E; inversion E; subst s'.
  apply rule_sound, rule_valid_spec; exact Hv.
Qed.

Fixpoint run_rules s rs :=
  match rs with
  | [] => Some s
  | r::rs =>
      match apply_rule s r with
      | Some s' => run_rules s' rs
      | None => None
      end
  end.

Lemma run_rules_sound rs s s':
  run_rules s rs = Some s' ->
  hconfig s -->* hconfig s'.
Proof.
  revert s s'.
  induction rs as [|r rs IH]; intros s s' Hrun.
  1: cbn in Hrun; inversion Hrun; finish.
  cbn in Hrun.
  destruct (apply_rule s r) as [t|] eqn:Hr.
  2: discriminate.
  follow (apply_rule_sound s r t Hr).
  apply IH; exact Hrun.
Qed.

Definition certificate : list HRule :=
  [ RF 4 64 19 9
  ; RT 3 0 24 69 20
  ; RNext 3 0 8 2 1 7
  ; RNext 2 1 7 2 1 2
  ; RNext 2 1 2 1 2 5
  ; RNext 1 2 5 2 2 63
  ; RConv 2 2 63 128 18
  ; RF 5 128 17 8
  ; RT 4 0 88 69 21
  ; RSames 4 0 2 39
  ; RNext 4 0 27 4 0 21
  ; RNext 4 0 21 3 1 19
  ; RSames 3 1 1 19
  ; RNext 3 1 13 3 1 7
  ; RNext 3 1 7 2 2 9
  ; RNext 2 2 9 2 2 3
  ; RNext 2 2 3 1 3 13
  ; RNext 1 3 13 3 2 118
  ; RNext 3 2 118 5 0 99
  ; RSames 5 0 6 99
  ; RNext 5 0 57 5 0 50
  ; RNext 5 0 50 4 1 47
  ; RSames 4 1 3 47
  ; RNext 4 1 26 4 1 19
  ; RNext 4 1 19 3 2 20
  ; RSames 3 2 1 20
  ; RNext 3 2 13 3 2 6
  ; RNext 3 2 6 2 3 15
  ; RNext 2 3 15 3 3 263
  ; RConv 3 3 263 528 18
  ; RF 7 528 17 8
  ; RT 6 0 452 109 33
  ; RSames 6 0 12 219
  ; RNext 6 0 123 6 0 115
  ; RNext 6 0 115 5 1 111
  ; RSames 5 1 6 111
  ; RNext 5 1 63 5 1 55
  ; RNext 5 1 55 4 2 55
  ; RSames 4 2 3 55
  ; RNext 4 2 31 4 2 23
  ; RNext 4 2 23 3 3 31
  ; RNext 3 3 31 4 2 7
  ; RNext 4 2 7 2 4 47
  ; RNext 2 4 47 4 3 518
  ; RConv 4 3 518 1038 22
  ; RF 8 1038 21 10
  ; RT 7 0 960 117 36
  ; RSames 7 0 25 472
  ; RNext 7 0 247 7 0 238
  ; RNext 7 0 238 6 1 233
  ; RSames 6 1 12 233
  ; RNext 6 1 125 6 1 116
  ; RNext 6 1 116 5 2 115
  ; RSames 5 2 6 115
  ; RNext 5 2 61 5 2 52
  ; RNext 5 2 52 4 3 59
  ; RNext 4 3 59 5 2 34
  ; RNext 5 2 34 4 3 41
  ; RSames 4 3 1 41
  ; RNext 4 3 32 4 3 23
  ; RNext 4 3 23 3 4 46
  ; RNext 3 4 46 4 3 5
  ; RNext 4 3 5 2 5 92
  ; RNext 2 5 92 5 3 1010
  ; RNext 5 3 1010 8 0 972
  ; RSames 8 0 47 972
  ; RNext 8 0 502 8 0 492
  ; RNext 8 0 492 7 1 486
  ; RSames 7 1 23 486
  ; RNext 7 1 256 7 1 246
  ; RNext 7 1 246 6 2 244
  ; RSames 6 2 12 244
  ; RNext 6 2 124 6 2 114
  ; RNext 6 2 114 5 3 120
  ; RNext 5 3 120 6 2 94
  ; RNext 6 2 94 5 3 100
  ; RSames 5 3 4 100
  ; RNext 5 3 60 5 3 50
  ; RNext 5 3 50 4 4 72
  ; RNext 4 4 72 5 3 30
  ; RNext 5 3 30 4 4 52
  ; RSames 4 4 2 52
  ; RNext 4 4 32 4 4 22
  ; RNext 4 4 22 3 5 76
  ; RNext 3 5 76 5 4 2049
  ; RConv 5 4 2049 4100 106
  ; RF 10 4100 105 52
  ; RT 9 0 3954 273 77
  ; RSames 9 0 86 1967
  ; RNext 9 0 1021 9 0 1010
  ; RNext 9 0 1010 8 1 1003
  ; RSames 8 1 45 1003
  ; RNext 8 1 508 8 1 497
  ; RNext 8 1 497 7 2 494
  ; RSames 7 2 22 494
  ; RNext 7 2 252 7 2 241
  ; RNext 7 2 241 6 3 246
  ; RSames 6 3 11 246
  ; RNext 6 3 125 6 3 114
  ; RNext 6 3 114 5 4 135
  ; RNext 5 4 135 6 3 92
  ; RNext 6 3 92 5 4 113
  ; RSames 5 4 5 113
  ; RNext 5 4 58 5 4 47
  ; RNext 5 4 47 4 5 100
  ; RNext 4 5 100 5 4 25
  ; RNext 5 4 25 3 6 206
  ; RNext 3 6 206 6 4 4098
  ; RConv 6 4 4098 8198 102
  ; RF 11 8198 101 50
  ; RT 10 0 8050 273 78
  ; RSames 10 0 164 4014
  ; RNext 10 0 2046 10 0 2034
  ; RNext 10 0 2034 9 1 2026
  ; RSames 9 1 84 2026
  ; RNext 9 1 1018 9 1 1006
  ; RNext 9 1 1006 8 2 1002
  ; RSames 8 2 41 1002
  ; RNext 8 2 510 8 2 498
  ; RNext 8 2 498 7 3 502
  ; RNext 7 3 502 8 2 474
  ; RNext 8 2 474 7 3 478
  ; RSames 7 3 19 478
  ; RNext 7 3 250 7 3 238
  ; RNext 7 3 238 6 4 258
  ; RNext 6 4 258 7 3 214
  ; RNext 7 3 214 6 4 234
  ; RSames 6 4 9 234
  ; RNext 6 4 126 6 4 114
  ; RNext 6 4 114 5 5 166
  ; RNext 5 5 166 6 4 90
  ; RNext 6 4 90 5 5 142
  ; RNext 5 5 142 6 4 66
  ; RNext 6 4 66 5 5 118
  ; RSames 5 5 5 118
  ; RNext 5 5 58 5 5 46
  ; RNext 5 5 46 4 6 162
  ; RNext 4 6 162 6 5 8213
  ; RConv 6 5 8213 16428 154
  ; RF 12 16428 153 76
  ; RT 11 0 16150 457 125
  ; RSames 11 0 306 8063
  ; RNext 11 0 4085 11 0 4072
  ; RNext 11 0 4072 10 1 4063
  ; RSames 10 1 155 4063
  ; RNext 10 1 2048 10 1 2035
  ; RNext 10 1 2035 9 2 2030
  ; RSames 9 2 78 2030
  ; RNext 9 2 1016 9 2 1003
  ; RNext 9 2 1003 8 3 1006
  ; RSames 8 3 38 1006
  ; RNext 8 3 512 8 3 499
  ; RNext 8 3 499 7 4 518
  ; RNext 7 4 518 8 3 473
  ; RNext 8 3 473 7 4 492
  ; RSames 7 4 18 492
  ; RNext 7 4 258 7 4 245
  ; RNext 7 4 245 6 5 296
  ; RNext 6 5 296 7 4 219
  ; RNext 7 4 219 6 5 270
  ; RNext 6 5 270 7 4 193
  ; RNext 7 4 193 6 5 244
  ; RSames 6 5 9 244
  ; RNext 6 5 127 6 5 114
  ; RNext 6 5 114 5 6 229
  ; RNext 5 6 229 6 5 88
  ; RNext 6 5 88 5 6 203
  ; RNext 5 6 203 6 5 62
  ; RNext 6 5 62 5 6 177
  ; RNext 5 6 177 6 5 36
  ; RNext 6 5 36 4 7 407
  ; RNext 4 7 407 7 5 16393
  ; RConv 7 5 16393 32788 202
  ; RF 13 32788 201 100
  ; RT 12 0 32508 509 139
  ; RSames 12 0 575 16241
  ; RNext 12 0 8191 12 0 8177
  ; RNext 12 0 8177 11 1 8167
  ; RSames 11 1 291 8167
  ; RNext 11 1 4093 11 1 4079
  ; RNext 11 1 4079 10 2 4073
  ; RSames 10 2 145 4073
  ; RNext 10 2 2043 10 2 2029
  ; RNext 10 2 2029 9 3 2031
  ; RSames 9 3 72 2031
  ; RNext 9 3 1023 9 3 1009
  ; RNext 9 3 1009 8 4 1027
  ; RNext 8 4 1027 9 3 981
  ; RNext 9 3 981 8 4 999
  ; RSames 8 4 35 999
  ; RNext 8 4 509 8 4 495
  ; RNext 8 4 495 7 5 545
  ; RNext 7 5 545 8 4 467
  ; RNext 8 4 467 7 5 517
  ; RNext 7 5 517 8 4 439
  ; RNext 8 4 439 7 5 489
  ; RSames 7 5 17 489
  ; RNext 7 5 251 7 5 237
  ; RNext 7 5 237 6 6 351
  ; RNext 6 6 351 7 5 209
  ; RNext 7 5 209 6 6 323
  ; RNext 6 6 323 7 5 181
  ; RNext 7 5 181 6 6 295
  ; RNext 6 6 295 7 5 153
  ; RNext 7 5 153 6 6 267
  ; RNext 6 6 267 7 5 125
  ; RNext 7 5 125 6 6 239
  ; RSames 6 6 8 239
  ; RNext 6 6 127 6 6 113
  ; RNext 6 6 113 5 7 355
  ; RNext 5 7 355 7 6 32852
  ; RConv 7 6 32852 65706 158
  ; RF 14 65706 157 78
  ; RT 13 0 65168 725 194
  ; RSames 13 0 1080 32570
  ; RNext 13 0 16370 13 0 16355
  ; RNext 13 0 16355 12 1 16344
  ; RSames 12 1 544 16344
  ; RNext 12 1 8184 12 1 8169
  ; RNext 12 1 8169 11 2 8162
  ; RSames 11 2 271 8162
  ; RNext 11 2 4097 11 2 4082
  ; RNext 11 2 4082 10 3 4083
  ; RNext 10 3 4083 11 2 4052
  ; RNext 11 2 4052 10 3 4053
  ; RSames 10 3 134 4053
  ; RNext 10 3 2043 10 3 2028
  ; RNext 10 3 2028 9 4 2045
  ; RNext 9 4 2045 10 3 1998
  ; RNext 10 3 1998 9 4 2015
  ; RSames 9 4 66 2015
  ; RNext 9 4 1025 9 4 1010
  ; RNext 9 4 1010 8 5 1059
  ; RNext 8 5 1059 9 4 980
  ; RNext 9 4 980 8 5 1029
  ; RNext 8 5 1029 9 4 950
  ; RNext 9 4 950 8 5 999
  ; RSames 8 5 33 999
  ; RNext 8 5 504 8 5 489
  ; RNext 8 5 489 7 6 602
  ; RNext 7 6 602 8 5 459
  ; RNext 8 5 459 7 6 572
  ; RNext 7 6 572 8 5 429
  ; RNext 8 5 429 7 6 542
  ; RNext 7 6 542 8 5 399
  ; RNext 8 5 399 7 6 512
  ; RNext 7 6 512 8 5 369
  ; RNext 8 5 369 7 6 482
  ; RSames 7 6 15 482
  ; RNext 7 6 257 7 6 242
  ; RNext 7 6 242 6 7 483
  ; RNext 6 7 483 7 6 212
  ; RNext 7 6 212 6 7 453
  ; RNext 6 7 453 7 6 182
  ; RNext 7 6 182 6 7 423
  ; RNext 6 7 423 7 6 152
  ; RNext 7 6 152 6 7 393
  ; RNext 6 7 393 7 6 122
  ; RNext 7 6 122 6 7 363
  ; RNext 6 7 363 7 6 92
  ; RNext 7 6 92 5 8 845
  ; RNext 5 8 845 8 6 65597
  ; RConv 8 6 65597 131196 250
  ; RF 15 131196 249 124
  ; RT 14 0 130656 821 219
  ; RSames 14 0 2035 65313
  ; RNext 14 0 32753 14 0 32737
  ; RNext 14 0 32737 13 1 32725
  ; RSames 13 1 1022 32725
  ; RNext 13 1 16373 13 1 16357
  ; RNext 13 1 16357 12 2 16349
  ; RSames 12 2 510 16349
  ; RNext 12 2 8189 12 2 8173
  ; RNext 12 2 8173 11 3 8173
  ; RSames 11 3 255 8173
  ; RNext 11 3 4093 11 3 4077
  ; RNext 11 3 4077 10 4 4093
  ; RNext 10 4 4093 11 3 4045
  ; RNext 11 3 4045 10 4 4061
  ; RSames 10 4 126 4061
  ; RNext 10 4 2045 10 4 2029
  ; RNext 10 4 2029 9 5 2077
  ; RNext 9 5 2077 10 4 1997
  ; RNext 10 4 1997 9 5 2045
  ; RNext 9 5 2045 10 4 1965
  ; RNext 10 4 1965 9 5 2013
  ; RSames 9 5 62 2013
  ; RNext 9 5 1021 9 5 1005
  ; RNext 9 5 1005 8 6 1117
  ; RNext 8 6 1117 9 5 973
  ; RNext 9 5 973 8 6 1085
  ; RNext 8 6 1085 9 5 941
  ; RNext 9 5 941 8 6 1053
  ; RNext 8 6 1053 9 5 909
  ; RNext 9 5 909 8 6 1021
  ; RNext 8 6 1021 9 5 877
  ; RNext 9 5 877 8 6 989
  ; RSames 8 6 30 989
  ; RNext 8 6 509 8 6 493
  ; RNext 8 6 493 7 7 733
  ; RNext 7 7 733 8 6 461
  ; RNext 8 6 461 7 7 701
  ; RNext 7 7 701 8 6 429
  ; RNext 8 6 429 7 7 669
  ; RNext 7 7 669 8 6 397
  ; RNext 8 6 397 7 7 637
  ; RNext 7 7 637 8 6 365
  ; RNext 8 6 365 7 7 605
  ; RNext 7 7 605 8 6 333
  ; RNext 8 6 333 7 7 573
  ; RNext 7 7 573 8 6 301
  ; RNext 8 6 301 7 7 541
  ; RNext 7 7 541 8 6 269
  ; RNext 8 6 269 7 7 509
  ; RNext 7 7 509 8 6 237
  ; RNext 8 6 237 6 8 989
  ; RNext 6 8 989 8 6 205
  ; RNext 8 6 205 6 8 957
  ; RNext 6 8 957 8 6 173
  ; RNext 8 6 173 6 8 925
  ; RNext 6 8 925 8 6 141
  ; RNext 8 6 141 6 8 893
  ; RNext 6 8 893 8 6 109
  ; RNext 8 6 109 5 9 1885
  ; RNext 5 9 1885 9 6 131148
  ].

Lemma certificate_eval:
  run_rules (HS2 64 20) certificate = Some (HUS 9 6 131148).
Proof.
  native_check_eq.
Qed.

Lemma certificate_run:
  S2 1 0 64 20 -->* US 9 6 131148.
Proof.
  apply (run_rules_sound certificate (HS2 64 20) (HUS 9 6 131148)).
  exact certificate_eval.
Qed.

Lemma certificate_end:
  US 9 6 131148 = Q 16 6 51.
Proof.
  rewrite (Q_eq 16 6 51) by lia.
  unfold US, UC, UD, QR.
  replace (131148*2+2) with
    ((2^(16+1)+2^(6+1)-51)*2) by native_check_eq.
  replace ((B 9 6-131148-6)*4+6) with
    ((51-5)*4+6) by (unfold B; native_check_eq).
  reflexivity.
Qed.

Lemma finite_to_stable:
  S2 1 0 64 20 -->* Q 16 6 51.
Proof.
  rewrite <-certificate_end.
  exact certificate_run.
Qed.

Lemma init_to_stable:
  c0 -->* Q 16 6 51.
Proof.
  follow init.
  exact finite_to_stable.
Qed.

Theorem nonhalt:
  ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: exact init_to_stable.
  exact stable_nonhalt.
Qed.

Print Assumptions nonhalt.

End TM1.

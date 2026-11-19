From BusyCoq Require Import Individual62.
From Coq Require Import Arith Zpow_facts Permutation ListDec.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
Import ListNotations.


Module Differences.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Fixpoint diff (d:nat) (f:nat->Z) (x:nat) : Z :=
  match d with O => f x | S d => diff d f (S x)-diff d f x end.

Lemma diff_ext d f g : (forall x,f x=g x) -> forall x,diff d f x=diff d g x.
Proof. intro H. induction d; intro x; cbn [diff]; [apply H|rewrite !IHd; reflexivity]. Qed.

Lemma diff_add d f g x : diff d (fun x => f x+g x) x=diff d f x+diff d g x.
Proof. revert x. induction d; intro x; cbn [diff]; [reflexivity|rewrite !IHd; ring]. Qed.

Lemma diff_scale d c f x : diff d (fun x => c*f x) x=c*diff d f x.
Proof. revert x. induction d; intro x; cbn [diff]; [reflexivity|rewrite !IHd; ring]. Qed.

Lemma diff_shift d f x : diff d (fun x => f (S x)) x=diff d f (S x).
Proof. revert x. induction d; intro x; cbn [diff]; [reflexivity|rewrite !IHd; reflexivity]. Qed.

Lemma diff_mul_x d f x :
  diff (S d) (fun x => Z.of_nat x*f x) x=
  Z.of_nat x*diff (S d) f x+Z.of_nat (S d)*diff d f (S x).
Proof.
  revert x. induction d as [|d IH]; intro x.
  - cbn [diff]. rewrite Nat2Z.inj_succ. change (Z.of_nat 1) with 1. ring.
  - change (diff (S d) (fun x => Z.of_nat x*f x) (S x)-
      diff (S d) (fun x => Z.of_nat x*f x) x =
      Z.of_nat x*(diff (S d) f (S x)-diff (S d) f x)+Z.of_nat (S(S d))*diff (S d) f (S x)).
    rewrite !IH. cbn [diff]. rewrite !Nat2Z.inj_succ. ring.
Qed.

Lemma diff_exp d q x : diff d (fun x => q^Z.of_nat x) x=(q-1)^Z.of_nat d*q^Z.of_nat x.
Proof.
  revert x. induction d as [|d IH]; intro x.
  - change (q^Z.of_nat x=1*q^Z.of_nat x). ring.
  - change (diff d (fun x => q^Z.of_nat x) (S x)-diff d (fun x => q^Z.of_nat x) x =
      (q-1)^Z.of_nat (S d)*q^Z.of_nat x).
    rewrite !IH,!Nat2Z.inj_succ,!Z.pow_succ_r by lia. ring.
Qed.

Lemma power_divide a b : (a<=b)%nat -> (4^Z.of_nat a | 4^Z.of_nat b).
Proof.
  intro H. exists (4^Z.of_nat (b-a)).
  rewrite Nat2Z.inj_sub by lia.
  replace (Z.of_nat b) with (Z.of_nat a+(Z.of_nat b-Z.of_nat a)) at 1 by ring.
  rewrite Z.pow_add_r by lia. ring.
Qed.

Theorem monomial_divisibility q : (4 | q-1) -> forall k d x,
  (4^Z.of_nat (d-k) | diff d (fun x => (Z.of_nat x)^Z.of_nat k*q^Z.of_nat x) x).
Proof.
  intros [t Ht] k. induction k as [|k IH]; intros d x.
  - replace (d-0)%nat with d by lia.
    rewrite (diff_ext d (fun x => (Z.of_nat x)^Z.of_nat 0*q^Z.of_nat x)
      (fun x => q^Z.of_nat x) ltac:(intro y; change (1*q^Z.of_nat y=q^Z.of_nat y); ring)).
    rewrite diff_exp,Ht,Z.pow_mul_l.
    exists (t^Z.of_nat d*q^Z.of_nat x). ring.
  - destruct d as [|d].
    + exists ((Z.of_nat x)^Z.of_nat (S k)*q^Z.of_nat x).
      change ((Z.of_nat x)^Z.of_nat (S k)*q^Z.of_nat x=
        ((Z.of_nat x)^Z.of_nat (S k)*q^Z.of_nat x)*1). ring.
    + rewrite (diff_ext (S d) (fun x => (Z.of_nat x)^Z.of_nat (S k)*q^Z.of_nat x)
        (fun x => Z.of_nat x*((Z.of_nat x)^Z.of_nat k*q^Z.of_nat x))
        ltac:(intro y; rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia; ring)).
      rewrite diff_mul_x. cbn [Nat.sub].
      apply Z.divide_add_r.
      * apply Z.divide_mul_r.
        eapply Z.divide_trans; [exact (power_divide (d-k) (S d-k) ltac:(lia))|apply IH].
      * apply Z.divide_mul_r,IH.
Qed.

Fixpoint sum (n:nat) (f:nat->Z) :=
  match n with O => 0 | S n => sum n f+f n end.

Lemma sum_ext n f g : (forall k,(k<n)%nat -> f k=g k) -> sum n f=sum n g.
Proof. intro H. induction n; cbn [sum]; [reflexivity|rewrite IHn,H; try lia; auto]. Qed.

Lemma sum_add n f g : sum n (fun k => f k+g k)=sum n f+sum n g.
Proof. induction n; cbn [sum]; [ring|rewrite IHn; ring]. Qed.

Lemma sum_head n f : sum (S n) f=f O+sum n (fun k => f (S k)).
Proof. induction n; cbn [sum] in *; [ring|lia]. Qed.

Fixpoint binom (n d:nat) : Z :=
  match n,d with _,O => 1 | O,S _ => 0 | S n,S d => binom n d+binom n (S d) end.

Lemma binom_above n d : (n<d)%nat -> binom n d=0.
Proof.
  revert d. induction n as [|n IH]; intros [|d] H; try lia; cbn [binom]; [reflexivity|].
  rewrite !IH by lia. ring.
Qed.

Lemma binom_zero n : binom n O=1.
Proof. destruct n; reflexivity. Qed.

Lemma binom_sum n f :
  sum (S(S n)) (fun k => binom (S n) k*f k)=
  sum (S n) (fun k => binom n k*f k)+sum (S n) (fun k => binom n k*f (S k)).
Proof.
  rewrite (sum_head (S n) (fun k => binom (S n) k*f k)).
  cbn [binom].
  rewrite (sum_ext (S n) (fun k => (binom n k+binom n (S k))*f (S k))
    (fun k => binom n k*f (S k)+binom n (S k)*f (S k)) ltac:(intros; ring)),sum_add.
  rewrite (sum_head n (fun k => binom n k*f k)),binom_zero.
  cbn [sum]. rewrite (binom_above n (S n) ltac:(lia)). ring.
Qed.

Theorem newton f n x : f (x+n)%nat=sum (S n) (fun d => binom n d*diff d f x).
Proof.
  revert x. induction n as [|n IH]; intro x.
  - rewrite Nat.add_0_r. cbn [sum binom diff]. ring.
  - replace (x+S n)%nat with (S x+n)%nat by lia. rewrite IH,binom_sum,<-sum_add.
    apply sum_ext. intros k Hk. cbn [diff]. ring.
Qed.

End Differences.

Module Parameters.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

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

Lemma sixth_tail m : 59<=m -> 2^22*m^6<2^(m-1).
Proof.
  intro Hm.
  assert (H : forall i,2^22*(59+Z.of_nat i)^6<2^(58+Z.of_nat i)).
  { induction i as [|i IH].
    - vm_compute. reflexivity.
    - rewrite Nat2Z.inj_succ.
      replace (59+Z.succ (Z.of_nat i)) with ((59+Z.of_nat i)+1) by lia.
      replace (58+Z.succ (Z.of_nat i)) with ((58+Z.of_nat i)+1) by lia.
      pose proof (power_ratio (59+Z.of_nat i) 16 6 2 ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(vm_compute; discriminate)) as Hratio.
      rewrite Z.pow_add_r by lia. change (2^1) with 2.
      assert (Hmul : 2^22*(59+Z.of_nat i+1)^6<=2*(2^22*(59+Z.of_nat i)^6)).
      { apply (Z.mul_le_mono_nonneg_l _ _ (2^22) ltac:(vm_compute; discriminate)) in Hratio. nia. }
      lia. }
  specialize (H (Z.to_nat (m-59))). rewrite Z2Nat.id in H by lia.
  replace (59+(m-59)) with m in H by lia.
  replace (58+(m-59)) with (m-1) in H by lia. exact H.
Qed.

Lemma dimension_bound m n : 59<=m -> 2^(m-1)<=n -> (2048*m^3)^2<n.
Proof.
  intros Hm Hn. pose proof (sixth_tail m Hm).
  replace ((2048*m^3)^2) with (2^22*m^6) by ring. lia.
Qed.

Lemma exponent_gap m : 2<=m ->
  (2048*m^3)*(1664*m^3+m) < (2048*m^3)*((2048*m^3)-1-2*(256*m^2)).
Proof.
  intro Hm. assert (Hpos : 0<2048*m^3) by (pose proof (Z.pow_pos_nonneg m 3 ltac:(lia) ltac:(lia)); lia).
  apply Z.mul_lt_mono_pos_l; [exact Hpos|].
  assert (Hdiff : 0<384*m^3-512*m^2-m-1).
  { replace (384*m^3-512*m^2-m-1) with ((m-2)*(384*m^2+256*m+511)+1021) by ring.
    pose proof (Z.pow_nonneg m 2 ltac:(lia)). nia. }
  lia.
Qed.

End Parameters.

Module Modular.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition F n := 2*3^n+n+5.

Lemma pow_pos a : 0<=a -> 0<2^a.
Proof. apply Z.pow_pos_nonneg. lia. Qed.

Lemma power_lift a : exists t,3^(2^Z.of_nat a)=1+2^(Z.of_nat a+1)*t.
Proof.
  induction a as [|a [t Ht]]; [exists 1; reflexivity|].
  exists (t+2^Z.of_nat a*t*t).
  rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
  replace (2*2^Z.of_nat a) with (2^Z.of_nat a*2) by ring.
  rewrite Z.pow_mul_r by (try apply Z.lt_le_incl,pow_pos; lia).
  rewrite Ht. replace (Z.succ (Z.of_nat a)+1) with ((Z.of_nat a+1)+1) by lia.
  rewrite !Z.pow_add_r by lia. ring.
Qed.

Lemma congr_mod m x y : 0<m -> (m | x-y) <-> x mod m=y mod m.
Proof.
  intro Hm. split.
  - intros [q Hq]. replace x with (q*m+y) by lia.
    rewrite Z.add_mod,Z.mod_mul,Z.add_0_l,Z.mod_mod by lia. reflexivity.
  - intro H. exists (x/m-y/m).
    pose proof (Z.div_mod x m ltac:(lia)). pose proof (Z.div_mod y m ltac:(lia)). nia.
Qed.

Lemma power_congr_ordered a x y : 0<=y<=x -> (2^Z.of_nat a | x-y) ->
  (2^(Z.of_nat a+1) | 3^x-3^y).
Proof.
  intros Hxy [w Hw]. pose proof (pow_pos (Z.of_nat a) ltac:(lia)) as HP.
  assert (Hw0 : 0<=w) by nia.
  destruct (power_lift a) as [t Ht].
  pose proof (pow_pos (Z.of_nat a+1) ltac:(lia)) as HM.
  assert (Hbase : (3^(2^Z.of_nat a)) mod (2^(Z.of_nat a+1))=1 mod (2^(Z.of_nat a+1))).
  { apply (proj1 (congr_mod _ _ _ HM)). exists t. lia. }
  apply (proj2 (congr_mod _ _ _ HM)).
  replace x with (y+2^Z.of_nat a*w) by nia.
  rewrite Z.pow_add_r,Z.pow_mul_r by nia.
  rewrite Z.mul_mod by lia. rewrite (Zpower_mod (3^(2^Z.of_nat a)) w _ HM),Hbase.
  rewrite <- Zpower_mod by lia. rewrite Z.pow_1_l by lia.
  rewrite <- Z.mul_mod by lia. rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma power_congr a x y : 0<=x -> 0<=y -> (2^Z.of_nat a | x-y) ->
  (2^(Z.of_nat a+1) | 3^x-3^y).
Proof.
  intros Hx Hy H. destruct (Z_le_gt_dec y x).
  - apply power_congr_ordered; lia || assumption.
  - destruct H as [w Hw].
    destruct (power_congr_ordered a y x ltac:(lia) ltac:(exists (-w); lia)) as [v Hv].
    exists (-v). lia.
Qed.

Lemma injective a x y : 0<=x -> 0<=y ->
  (2^Z.of_nat a | F x-F y) -> (2^Z.of_nat a | x-y).
Proof.
  intros Hx Hy. induction a as [|a IH]; intro H.
  - exists (x-y). cbn. lia.
  - rewrite Nat2Z.inj_succ,Z.pow_succ_r in H |- * by lia.
    assert (Hlow : (2^Z.of_nat a | F x-F y)).
    { destruct H as [w Hw]. exists (2*w). lia. }
    destruct (power_congr a x y Hx Hy (IH Hlow)) as [v Hv].
    rewrite Z.pow_add_r in Hv by lia. change (2^1) with 2 in Hv.
    destruct H as [w Hw]. exists (w-2*v). unfold F in Hw. nia.
Qed.

Lemma root_certificate r q a : 0<=a -> Zpow_mod 3 r (2^a)=q -> 2*q+r+5=2*2^a ->
  F r mod (2^a)=0.
Proof.
  intros Ha Hpow Hroot. pose proof (pow_pos a Ha) as HP.
  rewrite Zpow_mod_correct in Hpow by lia.
  apply Z.mod_divide; [lia|]. exists (2*(3^r/(2^a))+2).
  unfold F. pose proof (Z.div_mod (3^r) (2^a) ltac:(lia)). nia.
Qed.

Lemma root8 : F 149 mod (2^8)=0.
Proof.
  apply (root_certificate 149 179 8); [lia|native_check_eq|native_check_eq].
Qed.

Lemma root64 : F 767351889479380629 mod (2^64)=0.
Proof.
  apply (root_certificate 767351889479380629 18063068128969861299 64);
    [lia|native_check_eq|native_check_eq].
Qed.

Lemma power_divide a b : 0<=a<=b -> (2^a | 2^b).
Proof.
  intro H. exists (2^(b-a)). replace b with (a+(b-a)) at 1 by lia.
  rewrite Z.pow_add_r by lia. ring.
Qed.

Lemma root_unique a n r : 0<=n -> 0<=r -> F r mod (2^Z.of_nat a)=0 ->
  (2^Z.of_nat a | F n) -> n mod (2^Z.of_nat a)=r mod (2^Z.of_nat a).
Proof.
  intros Hn Hr Hroot H.
  apply (proj1 (congr_mod (2^Z.of_nat a) n r (pow_pos (Z.of_nat a) ltac:(lia)))).
  apply injective; try assumption. apply Z.divide_sub_r; [exact H|].
  apply Z.mod_divide; [pose proof (pow_pos (Z.of_nat a) ltac:(lia)); lia|exact Hroot].
Qed.

Theorem finite_bound n : 7<=n<2^58 -> ~(2^(n+1) | F n).
Proof.
  intros Hn Hbad. destruct (Z_lt_ge_dec n 64) as [Hsmall|Hlarge].
  - assert (H8 : (2^Z.of_nat 8 | F n)).
    { eapply Z.divide_trans; [apply power_divide|exact Hbad]. change (0<=8<=n+1). lia. }
    pose proof (root_unique 8 n 149 ltac:(lia) ltac:(lia) root8 H8) as H.
    change (n mod 256=149) in H. rewrite Z.mod_small in H by lia. lia.
  - assert (H64 : (2^Z.of_nat 64 | F n)).
    { eapply Z.divide_trans; [apply power_divide|exact Hbad]. change (0<=64<=n+1). lia. }
    pose proof (root_unique 64 n 767351889479380629 ltac:(lia) ltac:(lia) root64 H64) as H.
    change (n mod (2^64)=767351889479380629) in H.
    assert (Hcut : 2^58<767351889479380629<2^64) by (vm_compute; split; reflexivity).
    rewrite Z.mod_small in H by lia. lia.
Qed.

Definition large_exclusion := forall n u,
  2^58<=n -> 1<=u<=n -> ~(2^n | (-3)^n-u).

Theorem core_of_large : large_exclusion -> forall n,7<=n -> ~(2^(n+1) | F n).
Proof.
  intros Hlarge n Hn Hbad. destruct (Z_lt_ge_dec n (2^58)) as [Hsmall|Hbig].
  - apply (finite_bound n ltac:(lia)). exact Hbad.
  - assert (Htwo : (2 | F n)).
    { change (2^1 | F n). eapply Z.divide_trans;
        [exact (power_divide 1 (n+1) ltac:(lia))|exact Hbad]. }
    destruct Htwo as [w Hw].
    assert (Hodd : Z.Odd n) by (exists (w-3^n-3); unfold F in Hw; lia).
    assert (Hhalf : 2*((n+5)/2)=n+5).
    { destruct Hodd as [v Hv]. pose proof (Z.div_mod (n+5) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (n+5) 2 ltac:(lia)). lia. }
    apply (Hlarge n ((n+5)/2) ltac:(lia) ltac:(lia)).
    assert (Hopp : (-3)^n=-(3^n)) by (exact (Z.pow_opp_odd 3 n Hodd)).
    rewrite Hopp.
    destruct Hbad as [q Hq]. rewrite Z.pow_add_r in Hq by lia. change (2^1) with 2 in Hq.
    exists (-q). unfold F in Hq. nia.
Qed.

End Modular.

Module Determinants.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Section Laplace.
Context {I:Type}.

Fixpoint lap (cols:list I) (f:I->list I->Z) : Z :=
  match cols with
  | [] => 0
  | c::cs => f c cs-lap cs (fun x xs => f x (c::xs))
  end.

Lemma lap_ext cols f g : (forall c cs,f c cs=g c cs) -> lap cols f=lap cols g.
Proof.
  revert f g. induction cols as [|c cs IH]; intros f g H; cbn [lap]; [reflexivity|].
  rewrite H,IH with (g:=fun x xs => g x (c::xs)); auto.
Qed.

Lemma lap_zero cols : lap cols (fun _ _ => 0)=0.
Proof. induction cols; cbn [lap]; [reflexivity|rewrite IHcols; ring]. Qed.

Lemma lap_add cols f g : lap cols (fun c cs => f c cs+g c cs)=lap cols f+lap cols g.
Proof.
  revert f g. induction cols; intros; cbn [lap]; [ring|rewrite IHcols; ring].
Qed.

Lemma lap_sub cols f g : lap cols (fun c cs => f c cs-g c cs)=lap cols f-lap cols g.
Proof.
  revert f g. induction cols; intros; cbn [lap]; [ring|rewrite IHcols; ring].
Qed.

Lemma lap_scale cols a f : lap cols (fun c cs => a*f c cs)=a*lap cols f.
Proof. revert f. induction cols; intros; cbn [lap]; [ring|rewrite IHcols; ring]. Qed.

Lemma lap_two_swap cols F :
  lap cols (fun c cs => lap cs (fun d ds => F c d ds)) =
  -lap cols (fun d ds => lap ds (fun c cs => F c d cs)).
Proof.
  revert F. induction cols as [|c cs IH]; intro F; cbn [lap]; [ring|].
  rewrite !lap_sub.
  rewrite (IH (fun x y ys => F x y (c::ys))).
  change (fun d ds => F c d ds) with (F c). ring.
Qed.

Lemma selection_tail (c x:I) cs xs : Permutation (x::xs) cs ->
  Permutation (x::c::xs) (c::cs).
Proof. intro H. eapply Permutation_trans; [apply perm_swap|apply perm_skip; exact H]. Qed.

Lemma lap_congr cols f g :
  (forall c cs,Permutation (c::cs) cols -> f c cs=g c cs) -> lap cols f=lap cols g.
Proof.
  revert f g. induction cols as [|c cs IH]; intros f g H; cbn [lap]; [reflexivity|].
  rewrite H by reflexivity. f_equal. apply IH. intros x xs Hxs.
  apply H,selection_tail,Hxs.
Qed.

Lemma lap_divide cols f m :
  (forall c cs,Permutation (c::cs) cols -> (m | f c cs)) -> (m | lap cols f).
Proof.
  revert f. induction cols as [|c cs IH]; intros f H; cbn [lap].
  - exists 0. ring.
  - apply Z.divide_sub_r; [apply H; reflexivity|].
    apply IH. intros x xs Hxs. apply H,selection_tail,Hxs.
Qed.

Lemma lap_bound cols f b : 0<=b ->
  (forall c cs,Permutation (c::cs) cols -> Z.abs (f c cs)<=b) ->
  Z.abs (lap cols f)<=Z.of_nat (length cols)*b.
Proof.
  revert f. induction cols as [|c cs IH]; intros f Hb H; cbn [lap List.length].
  - cbn. lia.
  - pose proof (H c cs (Permutation_refl _)) as Hhead.
    pose proof (IH (fun x xs => f x (c::xs)) Hb
      ltac:(intros x xs Hxs; apply H,selection_tail,Hxs)) as Htail.
    pose proof (Z.abs_triangle (f c cs) (-lap cs (fun x xs => f x (c::xs)))) as Habs.
    rewrite Z.abs_opp in Habs. rewrite Nat2Z.inj_succ. lia.
Qed.

(* Only square instances are used.  Empty rows have determinant one. *)
Fixpoint det (rows:list (I->Z)) (cols:list I) : Z :=
  match rows with
  | [] => 1
  | r::rs => lap cols (fun c cs => r c*det rs cs)
  end.

Lemma det_add pre r s post cols :
  det (pre++(fun c => r c+s c)::post) cols =
  det (pre++r::post) cols+det (pre++s::post) cols.
Proof.
  revert cols. induction pre as [|t pre IH]; intro cols; cbn [List.app det].
  - rewrite <-lap_add. apply lap_ext. intros. ring.
  - rewrite <-lap_add. apply lap_ext. intros. rewrite IH. ring.
Qed.

Lemma det_scale pre a r post cols :
  det (pre++(fun c => a*r c)::post) cols=a*det (pre++r::post) cols.
Proof.
  revert cols. induction pre as [|t pre IH]; intro cols; cbn [List.app det].
  - rewrite <-lap_scale. apply lap_ext. intros. ring.
  - rewrite <-lap_scale. apply lap_ext. intros. rewrite IH. ring.
Qed.

Lemma det_zero pre post cols : det (pre++(fun _ => 0)::post) cols=0.
Proof.
  change (det (pre++(fun _ => 0*0)::post) cols=0).
  rewrite det_scale. ring.
Qed.

Lemma det_swap_front r s post cols : det (r::s::post) cols = -det (s::r::post) cols.
Proof.
  cbn [det].
  rewrite (lap_ext cols (fun c cs => r c*lap cs (fun d ds => s d*det post ds))
    (fun c cs => lap cs (fun d ds => r c*(s d*det post ds)))
    ltac:(intros c cs; symmetry; apply lap_scale)).
  rewrite lap_two_swap. f_equal. apply lap_ext. intros c cs.
  rewrite <-lap_scale. apply lap_ext. intros. ring.
Qed.

Lemma det_swap pre r s post cols :
  det (pre++r::s::post) cols = -det (pre++s::r::post) cols.
Proof.
  revert cols. induction pre as [|t pre IH]; intro cols; [apply det_swap_front|].
  cbn [List.app det]. replace (-lap cols (fun c cs => t c*det (pre++s::r::post) cs))
    with ((-1)*lap cols (fun c cs => t c*det (pre++s::r::post) cs)) by ring.
  rewrite <-lap_scale. apply lap_ext. intros. rewrite IH. ring.
Qed.

Lemma det_duplicate pre mid r post cols : det (pre++r::mid++r::post) cols=0.
Proof.
  assert (Hbase : forall mid cols,det (r::mid++r::post) cols=0).
  { intro ms. induction ms as [|s ms IH]; intro cs.
    - pose proof (det_swap_front r r post cs). cbn [List.app]. lia.
    - cbn [List.app]. rewrite det_swap_front.
      change (-lap cs (fun c xs => s c*det (r::ms++r::post) xs)=0).
      rewrite (lap_ext cs (fun c xs => s c*det (r::ms++r::post) xs) (fun _ _ => 0))
        by (intros; rewrite IH; ring). rewrite lap_zero. ring. }
  revert cols. induction pre as [|s pre IH]; intro cs; [apply Hbase|].
  cbn [List.app det]. rewrite (lap_ext cs (fun c xs => s c*det (pre++r::mid++r::post) xs)
    (fun _ _ => 0)) by (intros; rewrite IH; ring). apply lap_zero.
Qed.

Lemma selection_in (c:I) cs cols : Permutation (c::cs) cols -> In c cols /\ incl cs cols.
Proof.
  intro H. split.
  - eapply Permutation_in; [exact H|left; reflexivity].
  - intros x Hx. eapply Permutation_in; [exact H|right; exact Hx].
Qed.

Lemma det_congr m rows rows' cols :
  Forall2 (fun r s => forall c,In c cols -> (m | r c-s c)) rows rows' ->
  (m | det rows cols-det rows' cols).
Proof.
  revert rows' cols. induction rows as [|r rs IH]; intros rows' cols H.
  - inversion H; subst. exists 0. cbn [det]. ring.
  - inversion H as [|r0 s rs0 ss Hr Hrs]; subst. cbn [det].
    rewrite <-lap_sub. apply lap_divide. intros c cs Hp.
    destruct (selection_in c cs cols Hp) as [Hc Hcs].
    destruct (Hr c Hc) as [a Ha].
    assert (Htail : (m | det rs cs-det ss cs)).
    { apply IH. eapply Forall2_impl; [|exact Hrs]. intros u v Huv d Hd. apply Huv,Hcs,Hd. }
    destruct Htail as [b Hb]. exists (r c*b+a*det ss cs). nia.
Qed.

Lemma det_ext rows rows' cols :
  Forall2 (fun r s => forall c,In c cols -> r c=s c) rows rows' -> det rows cols=det rows' cols.
Proof.
  intro H. assert (Hz : (0 | det rows cols-det rows' cols)).
  { apply det_congr. eapply Forall2_impl; [|exact H].
    intros r s Hrs c Hc. rewrite Hrs by exact Hc. exists 0. ring. }
  destruct Hz. lia.
Qed.

Fixpoint product (xs:list Z) : Z := match xs with [] => 1 | x::xs => x*product xs end.

Lemma product_nonneg xs : Forall (fun x => 0<=x) xs -> 0<=product xs.
Proof. intro H. induction H; cbn [product]; [lia|apply Z.mul_nonneg_nonneg; assumption]. Qed.

Definition bounded (cols:list I) rows bounds :=
  Forall2 (fun r b => 0<=b /\ forall c,In c cols -> Z.abs (r c)<=b) rows bounds.

Lemma bounded_nonneg cols rows bounds : bounded cols rows bounds -> Forall (fun b => 0<=b) bounds.
Proof. intro H. induction H; constructor; intuition. Qed.

Lemma bounded_incl cols cs rows bounds : incl cs cols -> bounded cols rows bounds -> bounded cs rows bounds.
Proof.
  intros Hcs H. eapply Forall2_impl; [|exact H]. intros r b [Hb Hr]. split; [exact Hb|].
  intros c Hc. apply Hr,Hcs,Hc.
Qed.

Theorem det_bound rows cols bounds : length rows=length cols -> bounded cols rows bounds ->
  Z.abs (det rows cols)<=Z.of_nat (fact (length rows))*product bounds.
Proof.
  revert cols bounds. induction rows as [|r rs IH]; intros cols bounds Hlen Hbounds.
  - inversion Hbounds; subst. cbn [det List.length fact product]. lia.
  - inversion Hbounds as [|r0 b rs0 bs [Hb Hr] Hrs]; subst.
    assert (Hprod : 0<=product bs) by (apply product_nonneg; eapply bounded_nonneg; exact Hrs).
    pose proof (Nat2Z.is_nonneg (fact (length rs))) as Hfact.
    change (Z.abs (lap cols (fun c cs => r c*det rs cs))<=
      Z.of_nat (fact (S(length rs)))*(b*product bs)).
    eapply Z.le_trans with (m:=Z.of_nat (length cols)*(b*(Z.of_nat (fact (length rs))*product bs))).
    + apply lap_bound; [apply Z.mul_nonneg_nonneg; [exact Hb|apply Z.mul_nonneg_nonneg; assumption]|].
      intros c cs Hp. destruct (selection_in c cs cols Hp) as [Hc Hcs].
      pose proof (Permutation_length Hp) as Hcslen.
      pose proof (IH cs bs ltac:(cbn [List.length] in Hlen,Hcslen; lia)
        (bounded_incl cols cs rs bs Hcs Hrs)) as HD.
      rewrite Z.abs_mul. apply Z.mul_le_mono_nonneg;
        [apply Z.abs_nonneg|apply Hr,Hc|apply Z.abs_nonneg|exact HD].
    + cbn [fact]. rewrite Nat2Z.inj_mul. cbn [List.length] in Hlen.
      rewrite <- Hlen. ring_simplify. lia.
Qed.

End Laplace.

Lemma sum_scale n a f : Differences.sum n (fun d => a*f d)=a*Differences.sum n f.
Proof. induction n; cbn [Differences.sum]; [ring|rewrite IHn; ring]. Qed.

Lemma sum_divide n m f : (forall d,(d<n)%nat -> (m | f d)) -> (m | Differences.sum n f).
Proof.
  intro H. induction n; cbn [Differences.sum].
  - exists 0. ring.
  - apply Z.divide_add_r; [apply IHn; intros d Hd; apply H; lia|apply H; lia].
Qed.

Lemma det_sum {I} (pre:list (I->Z)) n f post cols :
  det (pre++(fun c => Differences.sum n (fun d => f d c))::post) cols =
  Differences.sum n (fun d => det (pre++f d::post) cols).
Proof.
  induction n; cbn [Differences.sum]; [apply det_zero|rewrite det_add,IHn; reflexivity].
Qed.

Fixpoint weight {J} (coef:J->nat->Z) (rows:list J) (ds:list nat) : Z :=
  match rows,ds with
  | [],[] => 1
  | r::rs,d::ds => coef r d*weight coef rs ds
  | _,_ => 0
  end.

Theorem det_expansion_divide {I J} (coef:J->nat->Z) (basis:nat->I->Z) D m rows :
  forall pre cols a,
  (forall ds,length ds=length rows -> Forall (fun d => (d<D)%nat) ds ->
    (m | a*weight coef rows ds*det (pre++map basis ds) cols)) ->
  (m | a*det (pre++map (fun r c => Differences.sum D (fun d => coef r d*basis d c)) rows) cols).
Proof.
  induction rows as [|r rs IH]; intros pre cols a H.
  - specialize (H [] eq_refl (Forall_nil _)). cbn [map weight] in *. rewrite Z.mul_1_r in H. exact H.
  - cbn [map]. rewrite det_sum,<-sum_scale. apply sum_divide. intros d Hd.
    rewrite det_scale. replace (a*(coef r d*det (pre++basis d::
      map (fun r c => Differences.sum D (fun d => coef r d*basis d c)) rs) cols)) with
      ((a*coef r d)*det ((pre++[basis d])++
      map (fun r c => Differences.sum D (fun d => coef r d*basis d c)) rs) cols)
      by (rewrite <-app_assoc; cbn [List.app]; ring).
    apply IH. intros ds Hlen Hds.
    specialize (H (d::ds) ltac:(cbn [List.length]; lia) ltac:(constructor; assumption)).
    cbn [weight map] in H. rewrite <-app_assoc. cbn [List.app].
    replace (a*coef r d*weight coef rs ds) with (a*(coef r d*weight coef rs ds)) by ring. exact H.
Qed.

Lemma det_repeated_index {I} (basis:nat->I->Z) ds cols :
  ~NoDup ds -> det (map basis ds) cols=0.
Proof.
  revert cols. induction ds as [|d ds IH]; intros cols H; [exfalso; apply H; constructor|].
  destruct (in_dec Nat.eq_dec d ds) as [Hin|Hnot].
  - apply in_split in Hin. destruct Hin as [pre [post ->]].
    rewrite map_cons,map_app,map_cons. apply (det_duplicate [] (map basis pre) (basis d) (map basis post)).
  - assert (Hds : ~NoDup ds) by (intro Hds; apply H; constructor; assumption).
    cbn [map det]. rewrite (lap_ext cols (fun c cs => basis d c*det (map basis ds) cs)
      (fun _ _ => 0)) by (intros; rewrite IH by exact Hds; ring). apply lap_zero.
Qed.

End Determinants.

Module IndexSums.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Fixpoint total (ds:list nat) : Z :=
  match ds with [] => 0 | d::ds => Z.of_nat d+total ds end.

Lemma total_perm ds es : Permutation ds es -> total ds=total es.
Proof. intro H. induction H; cbn [total]; lia. Qed.

Lemma total_nonneg ds : 0<=total ds.
Proof. induction ds; cbn [total]; lia. Qed.

Lemma minimum ds : ds<>[] -> exists d es,
  Permutation ds (d::es) /\ Forall (fun e => (d<=e)%nat) es.
Proof.
  induction ds as [|d ds IH]; intro H; [contradiction|].
  destruct ds as [|e es].
  - exists d. exists (@nil nat). split; [reflexivity|constructor].
  - destruct (IH ltac:(discriminate)) as [m [ms [Hp Hm]]].
    destruct (Nat.le_ge_cases d m) as [Hdm|Hmd].
    + exists d,(e::es). split; [reflexivity|].
      eapply Permutation_Forall; [symmetry; exact Hp|]. constructor; [exact Hdm|].
      eapply Forall_impl; [|exact Hm]. cbn. intros; lia.
    + exists m,(d::ms). split; [|constructor; assumption].
      eapply Permutation_trans; [apply perm_skip; exact Hp|apply perm_swap].
Qed.

Lemma pred_nodup ds : NoDup ds -> Forall (fun d => (0<d)%nat) ds -> NoDup (map Nat.pred ds).
Proof.
  intros H. induction H; intro Hpos; [constructor|].
  inversion Hpos as [|x0 xs Hx Hxs]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [d [Hd Hin]].
    rewrite Forall_forall in Hxs. specialize (Hxs d Hin). apply H. replace x with d by lia. exact Hin.
  - apply IHNoDup. assumption.
Qed.

Lemma total_pred ds : Forall (fun d => (0<d)%nat) ds ->
  total ds=total (map Nat.pred ds)+Z.of_nat (length ds).
Proof.
  intro H. induction H; cbn [total map List.length]; [reflexivity|].
  rewrite Nat2Z.inj_succ. assert (Z.of_nat x=Z.of_nat (Nat.pred x)+1) by lia. lia.
Qed.

Theorem distinct_lower ds : NoDup ds ->
  Z.of_nat (length ds)*(Z.of_nat (length ds)-1)<=2*total ds.
Proof.
  remember (length ds) as n eqn:Hlen. revert ds Hlen.
  induction n as [|n IH]; intros ds Hlen Hdup.
  - destruct ds; cbn [total List.length] in *; [lia|discriminate].
  - destruct (minimum ds ltac:(intro H; subst; discriminate)) as [d [es [Hp Hmin]]].
    pose proof (Permutation_length Hp) as Hlen'.
    assert (Hes : NoDup (d::es)) by (eapply Permutation_NoDup; eassumption).
    inversion Hes as [|d0 es0 Hnot Hdup']; subst.
    assert (Hpos : Forall (fun e => (0<e)%nat) es).
    { rewrite Forall_forall in *. intros e He. specialize (Hmin e He).
      assert (e<>d) by (intro E; subst; contradiction). lia. }
    pose proof (IH (map Nat.pred es) ltac:(rewrite length_map; cbn [List.length] in Hlen'; lia)
      (pred_nodup es Hdup' Hpos)) as Hlow.
    rewrite (total_perm ds (d::es) Hp). cbn [total]. rewrite total_pred by exact Hpos.
    rewrite Nat2Z.inj_succ. cbn [List.length] in Hlen'.
    assert (length es=n) by lia. rewrite H in *. nia.
Qed.

Lemma subtract_lower ds K : total ds-Z.of_nat (length ds)*Z.of_nat K<=
  total (map (fun d => (d-K)%nat) ds).
Proof.
  induction ds; cbn [total map List.length]; [lia|]. rewrite Nat2Z.inj_succ.
  assert (Z.of_nat a-Z.of_nat K<=Z.of_nat (a-K)) by lia. nia.
Qed.

End IndexSums.

Module DeterminantDivisibility.
Import Determinants IndexSums.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma weight_divide {J} (coef:J->nat->Z) K rows ds : length ds=length rows ->
  (forall r,In r rows -> forall d,(4^Z.of_nat (d-K) | coef r d)) ->
  (4^total (map (fun d => (d-K)%nat) ds) | weight coef rows ds).
Proof.
  revert ds. induction rows as [|r rs IH]; intros [|d ds] Hlen Hcoef;
    cbn [List.length] in Hlen; try discriminate.
  - exists 1. reflexivity.
  - cbn [map total weight]. rewrite Z.pow_add_r by (pose proof (total_nonneg (map (fun d => (d-K)%nat) ds)); lia).
    destruct (Hcoef r ltac:(left; reflexivity) d) as [a Ha].
    destruct (IH ds ltac:(lia) ltac:(intros s Hs; apply Hcoef; right; exact Hs)) as [b Hb].
    exists (a*b). rewrite Ha,Hb. ring.
Qed.

Theorem expansion_divide {I J} (coef:J->nat->Z) (basis:nat->I->Z) K D e rows cols :
  0<=e -> e<=Z.of_nat (length rows)*(Z.of_nat (length rows)-1-2*Z.of_nat K) ->
  (forall r,In r rows -> forall d,(4^Z.of_nat (d-K) | coef r d)) ->
  (2^e | det (map (fun r c => Differences.sum D (fun d => coef r d*basis d c)) rows) cols).
Proof.
  intros He Heb Hcoef.
  replace (det (map (fun r c => Differences.sum D (fun d => coef r d*basis d c)) rows) cols)
    with (1*det ([]++map (fun r c => Differences.sum D (fun d => coef r d*basis d c)) rows) cols)
    by (cbn [List.app]; ring).
  apply det_expansion_divide. intros ds Hlen Hds. cbn [List.app]. rewrite Z.mul_1_l.
  destruct (NoDup_dec Nat.eq_dec ds) as [Hnd|Hnd].
  - pose proof (distinct_lower ds Hnd) as Hsum.
    pose proof (subtract_lower ds K) as Hcost.
    assert (Hexp : e<=2*total (map (fun d => (d-K)%nat) ds)) by (rewrite Hlen in Hsum,Hcost; nia).
    assert (Hweight : (2^e | weight coef rows ds)).
    { eapply Z.divide_trans with (m:=2^(2*total (map (fun d => (d-K)%nat) ds)));
        [apply Modular.power_divide; lia|].
      replace (2^(2*total (map (fun d => (d-K)%nat) ds))) with
        (4^total (map (fun d => (d-K)%nat) ds)).
      - apply weight_divide; assumption.
      - rewrite Z.pow_mul_r by (pose proof (total_nonneg (map (fun d => (d-K)%nat) ds)); lia).
        reflexivity. }
    destruct Hweight as [w Hw]. exists (w*det (map basis ds) cols). rewrite Hw. ring.
  - rewrite det_repeated_index by exact Hnd. exists 0. ring.
Qed.

Lemma sum_extend n m f : (n<=m)%nat ->
  (forall d,(n<=d<m)%nat -> f d=0) -> Differences.sum m f=Differences.sum n f.
Proof.
  intros Hnm. induction m as [|m IH]; intro Hz.
  - assert (n=0)%nat by lia. subst. reflexivity.
  - destruct (Nat.eq_dec n (S m)) as [->|Hne]; [reflexivity|].
    cbn [Differences.sum]. rewrite Hz,IH by (intros; try apply Hz; lia). ring.
Qed.

Lemma newton_common f D x : (x<D)%nat ->
  f x=Differences.sum D (fun d => Differences.diff d f 0*Differences.binom x d).
Proof.
  intro Hx. pose proof (Differences.newton f x 0) as H. cbn [Nat.add] in H. rewrite H.
  rewrite (sum_extend (S x) D (fun d => Differences.diff d f 0*Differences.binom x d)) by
    (intros; try rewrite Differences.binom_above by lia; try ring; lia).
  apply Differences.sum_ext. intros. ring.
Qed.

Theorem evaluation_divide K e (rows:list (nat*Z)) cols :
  0<=e -> e<=Z.of_nat (length rows)*(Z.of_nat (length rows)-1-2*Z.of_nat K) ->
  (forall k q,In (k,q) rows -> (k<=K)%nat /\ (4 | q-1)) ->
  (2^e | det (map (fun p x => (Z.of_nat x)^Z.of_nat (fst p)*(snd p)^Z.of_nat x) rows) cols).
Proof.
  intros He Hb Hrows.
  set (D:=S(fold_right Nat.max O cols)).
  assert (Hcols : forall x,In x cols -> (x<D)%nat).
  { unfold D. induction cols as [|y ys IH]; intros x Hx; [contradiction|].
    cbn [fold_right] in *. destruct Hx as [<-|Hx]; [lia|specialize (IH x Hx); lia]. }
  rewrite (det_ext _
    (map (fun p x => Differences.sum D (fun d =>
      Differences.diff d (fun x => (Z.of_nat x)^Z.of_nat (fst p)*(snd p)^Z.of_nat x) 0*
      Differences.binom x d)) rows) cols).
  - apply (expansion_divide _ (fun d x => Differences.binom x d) K D); try assumption.
    intros [k q] Hp d. destruct (Hrows k q Hp) as [Hk Hq]. cbn [fst snd].
    eapply Z.divide_trans with (m:=4^Z.of_nat (d-k));
      [apply Differences.power_divide; lia|apply Differences.monomial_divisibility; exact Hq].
  - clear He Hb Hrows. induction rows as [|p ps IH]; cbn [map]; constructor; auto. intros x Hx.
    apply (newton_common (fun x => (Z.of_nat x)^Z.of_nat (fst p)*(snd p)^Z.of_nat x) D x),Hcols,Hx.
Qed.

End DeterminantDivisibility.

Module NonzeroMinor.
Import Determinants.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.
Section Rows.
Context {I:Type}.

Lemma det_sub pre (r s:I->Z) post cols :
  det (pre++(fun c => r c-s c)::post) cols =
  det (pre++r::post) cols-det (pre++s::post) cols.
Proof.
  revert cols. induction pre as [|t pre IH]; intro cols; cbn [List.app det].
  - rewrite <-lap_sub. apply lap_ext. intros. ring.
  - rewrite <-lap_sub. apply lap_ext. intros. rewrite IH. ring.
Qed.

Lemma zero_column (rows:list (I->Z)) c cols : length rows=S(length cols) ->
  Forall (fun r => r c=0) rows -> det rows (c::cols)=0.
Proof.
  revert c cols. induction rows as [|r rs IH]; intros c cols Hlen Hz; [discriminate|].
  inversion Hz as [|r0 rs0 Hr Hrs]; subst.
  change (r c*det rs cols-lap cols (fun d ds => r d*det rs (c::ds))=0).
  rewrite Hr. rewrite (lap_congr cols (fun d ds => r d*det rs (c::ds)) (fun _ _ => 0)).
  - rewrite lap_zero. ring.
  - intros d ds Hp. rewrite IH; [ring|pose proof (Permutation_length Hp); cbn [List.length] in *; lia|exact Hrs].
Qed.

Lemma pivot_expansion (r:I->Z) rs c cols : length rs=length cols ->
  Forall (fun s => s c=0) rs -> det (r::rs) (c::cols)=r c*det rs cols.
Proof.
  intros Hlen Hz.
  change (r c*det rs cols-lap cols (fun d ds => r d*det rs (c::ds))=r c*det rs cols).
  rewrite (lap_congr cols (fun d ds => r d*det rs (c::ds)) (fun _ _ => 0)).
  - rewrite lap_zero. ring.
  - intros d ds Hp. rewrite zero_column; [ring|pose proof (Permutation_length Hp); cbn [List.length] in *; lia|exact Hz].
Qed.

Lemma row_eliminate (r s:I->Z) a b pre post cols :
  det (r::(pre++(fun x => a*s x-b*r x)::post)) cols=a*det (r::(pre++s::post)) cols.
Proof.
  change (det ((r::pre)++(fun x => a*s x-b*r x)::post) cols=a*det ((r::pre)++s::post) cols).
  rewrite det_sub,!det_scale.
  pose proof (det_duplicate [] pre r post cols) as Hzero. cbn [List.app] in Hzero |- *.
  rewrite Hzero. ring.
Qed.

Lemma eliminate_all (r:I->Z) c a rs : forall pre cols,
  det (r::(pre++map (fun s x => a*s x-s c*r x) rs)) cols=
  a^Z.of_nat (length rs)*det (r::(pre++rs)) cols.
Proof.
  induction rs as [|s rs IH]; intros pre cols.
  - cbn [map List.length]. change (det (r::(pre++[])) cols=1*det (r::(pre++[])) cols). ring.
  - cbn [map List.length]. rewrite row_eliminate.
    change (a*det (r::(pre++s::map (fun s x => a*s x-s c*r x) rs)) cols=
      a^Z.of_nat (S(length rs))*det (r::(pre++s::rs)) cols).
    replace (pre++s::map (fun s x => a*s x-s c*r x) rs) with
      ((pre++[s])++map (fun s x => a*s x-s c*r x) rs) by (rewrite <-app_assoc; reflexivity).
    rewrite IH,Nat2Z.inj_succ,Z.pow_succ_r by lia. rewrite <-app_assoc. cbn [List.app]. ring.
Qed.

Fixpoint combination (rows:list (I->Z)) (ws:list Z) (c:I) : Z :=
  match rows,ws with r::rs,w::ws => w*r c+combination rs ws c | _,_ => 0 end.

Lemma combination_zero rows c : combination rows (repeat 0 (length rows)) c=0.
Proof. induction rows; cbn [List.length repeat combination]; [reflexivity|rewrite IHrows; ring]. Qed.

Lemma combination_scale rows ws a c :
  combination rows (map (fun w => a*w) ws) c=a*combination rows ws c.
Proof.
  revert ws. induction rows as [|r rs IH]; intros [|w ws]; cbn [map combination]; try ring.
  rewrite IH. ring.
Qed.

Lemma combination_eliminate rows ws (r:I->Z) c a x :
  combination (map (fun s x => a*s x-s c*r x) rows) ws x=
  a*combination rows ws x-r x*combination rows ws c.
Proof.
  revert ws. induction rows as [|s rs IH]; intros [|w ws]; cbn [map combination]; try ring.
  rewrite IH. ring.
Qed.

Definition independent (rows:list (I->Z)) (cols:list I) :=
  forall ws,length ws=length rows -> (forall c,In c cols -> combination rows ws c=0) ->
    Forall (fun w => w=0) ws.

Lemma independent_pivot r rs cols : independent (r::rs) cols -> exists c,In c cols /\ r c<>0.
Proof.
  intro Hind.
  assert (Hfind : (forall c,In c cols -> r c=0) \/ exists c,In c cols /\ r c<>0).
  { clear Hind. induction cols as [|c cs IH].
    - left. intros; contradiction.
    - destruct (Z.eq_dec (r c) 0) as [Hc|Hc].
      + destruct IH as [H|[d [Hd Hr]]].
        * left. intros d [<-|Hd]; [exact Hc|apply H,Hd].
        * right. exists d. split; [right|]; assumption.
      + right. exists c. split; [left; reflexivity|exact Hc]. }
  destruct Hfind as [Hz|H]; [|exact H].
  specialize (Hind (1::repeat 0 (length rs)) ltac:(cbn [List.length]; rewrite repeat_length; reflexivity)).
  assert (Hbad : Forall (fun w : Z => w=0) (1::repeat 0 (length rs))).
  { apply Hind. intros c Hc. cbn [combination]. rewrite combination_zero,Hz by exact Hc. ring. }
  inversion Hbad. discriminate.
Qed.

Lemma independent_eliminate r rs cols c : independent (r::rs) cols -> r c<>0 ->
  independent (map (fun s x => r c*s x-s c*r x) rs) cols.
Proof.
  intros Hind Hc ws Hlen Hz. rewrite length_map in Hlen.
  specialize (Hind (-combination rs ws c::map (fun w => r c*w) ws)
    ltac:(cbn [List.length]; rewrite length_map; lia)).
  assert (Hrel : Forall (fun w : Z => w=0) (-combination rs ws c::map (fun w => r c*w) ws)).
  { apply Hind. intros x Hx. specialize (Hz x Hx). rewrite combination_eliminate in Hz.
    cbn [combination]. rewrite combination_scale. nia. }
  inversion Hrel as [|w ws0 Hw Hws]; subst. rewrite Forall_map,Forall_forall in Hws.
  rewrite Forall_forall. intros w Hw'. specialize (Hws w Hw'). nia.
Qed.

Theorem nonzero_minor rows cols : independent rows cols ->
  exists cs,length cs=length rows /\ incl cs cols /\ det rows cs<>0.
Proof.
  remember (length rows) as n eqn:Hlen. revert rows Hlen.
  induction n as [|n IH]; intros rows Hlen Hind.
  - destruct rows; [exists (@nil I); repeat split; try reflexivity; try (intros x H; contradiction); discriminate|discriminate].
  - destruct rows as [|r rs]; [discriminate|].
    destruct (independent_pivot r rs cols Hind) as [c [Hc Hr]].
    destruct (IH (map (fun s x => r c*s x-s c*r x) rs)
      ltac:(rewrite length_map; cbn [List.length] in Hlen; lia)
      (independent_eliminate r rs cols c Hind Hr)) as [cs [Hcs [Hin Hdet]]].
    exists (c::cs). split; [cbn [List.length] in Hlen |- *; lia|].
    split; [intros x [<-|Hx]; [exact Hc|apply Hin,Hx]|].
    intro Hzero.
    pose proof (eliminate_all r c (r c) rs [] (c::cs)) as Heq.
    cbn [List.app] in Heq. rewrite Hzero,Z.mul_0_r in Heq.
    rewrite pivot_expansion in Heq.
    + apply Z.mul_eq_0 in Heq. destruct Heq; contradiction.
    + rewrite length_map. cbn [List.length] in Hlen. lia.
    + rewrite Forall_forall. intros s Hs. apply in_map_iff in Hs. destruct Hs as [t [<- Ht]]. ring.
Qed.

Lemma det_combination_zero rows ws : forall pre cols,
  det (combination rows ws::(pre++rows)) cols=0.
Proof.
  revert ws. induction rows as [|r rs IH]; intros ws pre cols.
  - exact (det_zero [] (pre++[]) cols).
  - destruct ws as [|w ws]; [exact (det_zero [] (pre++r::rs) cols)|].
    change (det ([]++(fun c => w*r c+combination rs ws c)::(pre++r::rs)) cols=0).
    rewrite det_add,det_scale.
    pose proof (det_duplicate [] pre r rs cols) as Hr. cbn [List.app] in Hr |- *.
    rewrite Hr.
    replace (pre++r::rs) with ((pre++[r])++rs) by (rewrite <-app_assoc; reflexivity).
    rewrite IH. ring.
Qed.

Theorem relation_forces_zero r rs a ws cols : a<>0 ->
  (forall c,In c cols -> a*r c+combination rs ws c=0) -> det (r::rs) cols=0.
Proof.
  intros Ha Hrel.
  assert (Hdet : det ((fun c => a*r c+combination rs ws c)::rs) cols=0).
  { rewrite (det_ext _ ((fun _ => 0)::rs) cols).
    - exact (det_zero [] rs cols).
    - constructor; [exact Hrel|]. clear Hrel. induction rs; constructor; auto. }
  change (det ([]++(fun c => a*r c+combination rs ws c)::rs) cols=0) in Hdet.
  rewrite det_add,det_scale in Hdet.
  pose proof (det_combination_zero rs ws [] cols) as Hzero. cbn [List.app] in Hdet,Hzero.
  rewrite Hzero in Hdet. nia.
Qed.

End Rows.
End NonzeroMinor.

Module MatrixBounds.
Import Determinants.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma product_repeat a n : product (repeat a n)=a^Z.of_nat n.
Proof.
  induction n; cbn [repeat product]; [reflexivity|].
  rewrite IHn,Nat2Z.inj_succ,Z.pow_succ_r by lia. reflexivity.
Qed.

Lemma factorial_bound n b : 0<=b -> Z.of_nat n<=b -> Z.of_nat (fact n)<=b^Z.of_nat n.
Proof.
  intro Hb. induction n as [|n IH]; intro Hn; [reflexivity|].
  cbn [fact]. rewrite Nat2Z.inj_mul. rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia.
  apply Z.mul_le_mono_nonneg; [lia|lia|apply Nat2Z.is_nonneg|apply IH; lia].
Qed.

Theorem uniform_bound {I} (rows:list (I->Z)) cols m b :
  length rows=length cols -> 0<=m -> 0<=b -> Z.of_nat (length rows)<=2^m ->
  (forall r,In r rows -> forall c,In c cols -> Z.abs (r c)<=2^b) ->
  Z.abs (det rows cols)<=2^(Z.of_nat (length rows)*(m+b)).
Proof.
  intros Hlen Hm Hb Hsize Hrows.
  assert (Hbounds : bounded cols rows (repeat (2^b) (length rows))).
  { clear Hlen Hsize. induction rows as [|r rs IH]; cbn [List.length repeat]; constructor.
    - split; [apply Z.pow_nonneg; lia|apply Hrows; left; reflexivity].
    - apply IH. intros s Hs. apply Hrows; right; exact Hs. }
  pose proof (det_bound rows cols _ Hlen Hbounds) as Hdet. rewrite product_repeat in Hdet.
  pose proof (factorial_bound (length rows) (2^m) ltac:(pose proof (Modular.pow_pos m Hm); lia) Hsize) as Hfact.
  assert (Hp : 0<=(2^b)^Z.of_nat (length rows)) by (apply Z.pow_nonneg,Z.pow_nonneg; lia).
  apply (Z.mul_le_mono_nonneg_r _ _ _ Hp) in Hfact.
  eapply Z.le_trans; [exact Hdet|]. eapply Z.le_trans; [exact Hfact|].
  rewrite <- !Z.pow_mul_r,<-Z.pow_add_r by lia.
  replace (m*Z.of_nat (length rows)+b*Z.of_nat (length rows)) with (Z.of_nat (length rows)*(m+b)) by ring.
  reflexivity.
Qed.

Lemma incompatible_bounds D U T : 0<=U<T -> D<>0 -> (2^T | D) -> Z.abs D<=2^U -> False.
Proof.
  intros HU HD [w Hw] Hbound.
  assert (Hpow : 0<2^T) by (apply Modular.pow_pos; lia).
  assert (Hstrict : 2^U<2^T) by (apply Z.pow_lt_mono_r; lia).
  assert (Hw0 : w<>0) by (intro H; subst; apply HD; lia).
  rewrite Hw,Z.abs_mul,(Z.abs_eq (2^T) ltac:(lia)) in Hbound.
  pose proof (proj2 (Z.abs_pos w) Hw0). nia.
Qed.

Lemma lap_map {I J} (f:I->J) cs g :
  lap (map f cs) g=lap cs (fun c cs => g (f c) (map f cs)).
Proof.
  revert g. induction cs; intro g; cbn [map lap]; [reflexivity|rewrite IHcs; reflexivity].
Qed.

Lemma det_map_cols {I J} (f:I->J) rows cs :
  det rows (map f cs)=det (map (fun r c => r (f c)) rows) cs.
Proof.
  revert cs. induction rows as [|r rs IH]; intro cs; cbn [map det]; [reflexivity|].
  rewrite lap_map. apply lap_ext. intros c ds. rewrite IH. reflexivity.
Qed.

End MatrixBounds.

Module Polynomials.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Fixpoint eval (p:list Z) (x:Z) : Z :=
  match p with [] => 0 | a::p => a+x*eval p x end.

Fixpoint quotient (p:list Z) (a:Z) : list Z :=
  match p with [] => [] | _::ps =>
    match ps with [] => [] | _::_ => eval ps a::quotient ps a end
  end.

Lemma quotient_length p a : length (quotient p a)=Nat.pred (length p).
Proof.
  induction p as [|c p IH]; [reflexivity|]. destruct p;
    cbn [quotient List.length] in *; [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma quotient_spec p a x : eval p x-eval p a=(x-a)*eval (quotient p a) x.
Proof.
  induction p as [|c p IH]; [cbn [eval quotient]; ring|].
  destruct p as [|d ps]; [cbn [eval quotient]; ring|].
  change (c+x*eval (d::ps) x-(c+a*eval (d::ps) a)=
    (x-a)*(eval (d::ps) a+x*eval (quotient (d::ps) a) x)). nia.
Qed.

Lemma eval_zero p x : Forall (fun a => a=0) p -> eval p x=0.
Proof. intro H. induction H; cbn [eval]; [reflexivity|rewrite H,IHForall; ring]. Qed.

Lemma quotient_zero p a : Forall (fun c => c=0) (quotient p a) ->
  Forall (fun c => c=0) (tl p).
Proof.
  induction p as [|c p IH]; intro H; [constructor|].
  destruct p as [|d ps]; [constructor|].
  change (Forall (fun c => c=0) (eval (d::ps) a::quotient (d::ps) a)) in H.
  inversion H as [|y ys Hy Hys]; subst. specialize (IH Hys).
  cbn [eval] in Hy. rewrite eval_zero in Hy by exact IH.
  constructor; [lia|exact IH].
Qed.

Theorem roots_force_zero p roots : NoDup roots ->
  Forall (fun x => eval p x=0) roots -> (length p<=length roots)%nat ->
  Forall (fun a => a=0) p.
Proof.
  remember (length p) as n eqn:Hlen. revert p roots Hlen.
  induction n as [|n IH]; intros p roots Hlen Hnd Hz Hsize.
  - destruct p; [constructor|discriminate].
  - destruct p as [|c p]; [discriminate|]. destruct roots as [|a rs]; [cbn [List.length] in Hsize; lia|].
    inversion Hnd as [|a0 rs0 Hnot Hnd']; subst.
    inversion Hz as [|a0 rs0 Ha Hz']; subst.
    assert (Hquot : Forall (fun c => c=0) (quotient (c::p) a)).
    { apply (IH _ rs); [rewrite quotient_length; cbn [List.length] in *; lia|exact Hnd'| |].
      - rewrite Forall_forall in Hz' |- *. intros x Hx.
        pose proof (quotient_spec (c::p) a x) as Hq. specialize (Hz' x Hx).
        assert (x<>a) by (intro E; subst; contradiction). nia.
      - cbn [List.length] in Hsize,Hlen. lia. }
    pose proof (quotient_zero (c::p) a Hquot) as Hp. cbn [tl] in Hp.
    cbn [eval] in Ha. rewrite eval_zero in Ha by exact Hp. constructor; [lia|exact Hp].
Qed.

Fixpoint add (p q:list Z) : list Z :=
  match p,q with [],_ => q | _,[] => p | a::ps,b::qs => (a+b)::add ps qs end.

Definition scale a p := map (Z.mul a) p.

Fixpoint mul (p q:list Z) : list Z :=
  match p,q with [],_ => [] | _,[] => [] | a::ps,_ => add (scale a q) (0::mul ps q) end.

Lemma eval_add p q x : eval (add p q) x=eval p x+eval q x.
Proof.
  revert q. induction p as [|a p IH]; intros [|b q]; cbn [add eval]; try ring. rewrite IH. ring.
Qed.

Lemma eval_scale a p x : eval (scale a p) x=a*eval p x.
Proof.
  induction p as [|b p IH]; [change (0=a*0); ring|].
  change (a*b+x*eval (scale a p) x=a*(b+x*eval p x)). rewrite IH. ring.
Qed.

Lemma eval_mul p q x : eval (mul p q) x=eval p x*eval q x.
Proof.
  revert q. induction p; intros [|b q]; cbn [mul]; try (cbn [eval]; ring).
  rewrite eval_add,eval_scale. cbn [eval]. rewrite IHp. cbn [eval]. ring.
Qed.

Fixpoint shift (p:list Z) a : list Z :=
  match p with [] => [] | c::ps => add [c] (mul [a;1] (shift ps a)) end.

Lemma eval_shift p a x : eval (shift p a) x=eval p (x+a).
Proof.
  induction p; cbn [shift]; [reflexivity|].
  rewrite eval_add,eval_mul,IHp. cbn [eval]. ring.
Qed.

Definition coeff p n := nth n p 0.

Lemma coeff_nil n : coeff [] n=0.
Proof. destruct n; reflexivity. Qed.

Lemma coeff_over p n : (length p<=n)%nat -> coeff p n=0.
Proof. apply nth_overflow. Qed.

Lemma coeff_add p q n : coeff (add p q) n=coeff p n+coeff q n.
Proof.
  revert q n. induction p as [|a p IH]; intros [|b q] n; cbn [add];
    try (rewrite !coeff_nil; ring).
  destruct n; [reflexivity|exact (IH q n)].
Qed.

Lemma coeff_scale a p n : coeff (scale a p) n=a*coeff p n.
Proof.
  revert n. induction p as [|b p IH]; intro n.
  - change (coeff [] n=a*coeff [] n). rewrite coeff_nil. ring.
  - destruct n; [reflexivity|exact (IH n)].
Qed.

Lemma length_add p q : length (add p q)=Nat.max (length p) (length q).
Proof.
  revert q. induction p as [|a p IH]; intros [|b q]; cbn [add List.length]; try lia.
  rewrite IH. reflexivity.
Qed.

Lemma length_scale a p : length (scale a p)=length p.
Proof. apply length_map. Qed.

Lemma length_mul p q : (length (mul p q)<=length p+length q-1)%nat.
Proof.
  revert q. induction p as [|a p IH]; intros [|b q]; cbn [mul List.length]; try lia.
  rewrite length_add,length_scale. cbn [List.length]. specialize (IH (b::q)).
  cbn [List.length] in IH. lia.
Qed.

Lemma length_shift p a : (length (shift p a)<=length p)%nat.
Proof.
  induction p; cbn [shift]; [reflexivity|]. rewrite length_add.
  pose proof (length_mul [a;1] (shift p a)). cbn [List.length] in *. lia.
Qed.

Lemma coeff_mul_top p q d e : (length p<=S d)%nat -> (length q<=S e)%nat ->
  coeff (mul p q) (d+e)=coeff p d*coeff q e.
Proof.
  revert p q. induction d as [|d IH]; intros [|a p] [|b q] Hp Hq;
    try (cbn [mul]; rewrite !coeff_nil; ring).
  - assert (p=[]) by (destruct p; cbn [List.length] in Hp; [reflexivity|lia]). subst p.
    cbn [mul]. rewrite coeff_add,coeff_scale.
    change (a*coeff (b::q) e+coeff [0] e=a*coeff (b::q) e).
    assert (Hz : coeff [0] e=0) by (destruct e; [reflexivity|exact (coeff_nil e)]).
    rewrite Hz. ring.
  - change (coeff (add (scale a (b::q)) (0::mul p (b::q))) (S(d+e))=
      coeff p d*coeff (b::q) e).
    rewrite coeff_add,coeff_scale.
    rewrite (coeff_over (b::q) (S(d+e))) by lia.
    change (a*0+coeff (mul p (b::q)) (d+e)=coeff p d*coeff (b::q) e).
    rewrite IH by (cbn [List.length] in Hp; lia). ring.
Qed.

Lemma coeff_shift_top p a d : (length p<=S d)%nat -> coeff (shift p a) d=coeff p d.
Proof.
  revert p. induction d as [|d IH]; intros [|c p] Hp; [reflexivity| |reflexivity|].
  - assert (p=[]) by (destruct p; cbn [List.length] in Hp; [reflexivity|lia]). subst p. reflexivity.
  - cbn [shift]. rewrite coeff_add.
    change (coeff [c] (S d)+coeff (mul [a;1] (shift p a)) (1+d)=coeff p d).
    rewrite coeff_over by (cbn [List.length]; lia).
    rewrite coeff_mul_top by (try (cbn [List.length]; lia); pose proof (length_shift p a); cbn [List.length] in Hp; lia).
    change (0+1*coeff (shift p a) d=coeff p d). rewrite IH by (cbn [List.length] in Hp; lia). ring.
Qed.

End Polynomials.

Module PolynomialDeterminants.
Import Determinants Polynomials.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.
Section Matrices.
Context {I:Type}.

Fixpoint plap (cols:list I) (f:I->list I->list Z) : list Z :=
  match cols with [] => [] | c::cs => add (f c cs) (scale (-1) (plap cs (fun d ds => f d (c::ds)))) end.

Lemma eval_plap cols f x : eval (plap cols f) x=lap cols (fun c cs => eval (f c cs) x).
Proof.
  revert f. induction cols as [|c cs IH]; intro f; cbn [plap lap]; [reflexivity|].
  rewrite eval_add,eval_scale,IH. ring.
Qed.

Lemma coeff_plap cols f n : coeff (plap cols f) n=lap cols (fun c cs => coeff (f c cs) n).
Proof.
  revert f. induction cols as [|c cs IH]; intro f; cbn [plap lap]; [apply coeff_nil|].
  rewrite coeff_add,coeff_scale,IH. ring.
Qed.

Lemma length_plap cols f n :
  (forall c cs,(length (f c cs)<=n)%nat) -> (length (plap cols f)<=n)%nat.
Proof.
  revert f. induction cols as [|c cs IH]; intros f H; cbn [plap List.length]; [lia|].
  rewrite length_add,length_scale. pose proof (H c cs).
  pose proof (IH (fun d ds => f d (c::ds)) ltac:(intros; apply H)). lia.
Qed.

Fixpoint degree (rows:list (nat*(I->list Z))) : nat :=
  match rows with [] => O | (d,_)::rs => (d+degree rs)%nat end.

Fixpoint pdet (rows:list (nat*(I->list Z))) (cols:list I) : list Z :=
  match rows with [] => [1] | (_,r)::rs => plap cols (fun c cs => mul (r c) (pdet rs cs)) end.

Definition valid (rows:list (nat*(I->list Z))) :=
  Forall (fun p => forall c,(length (snd p c)<=S(fst p))%nat) rows.

Lemma eval_pdet rows cols x :
  eval (pdet rows cols) x=det (map (fun p c => eval (snd p c) x) rows) cols.
Proof.
  revert cols. induction rows as [|[d r] rs IH]; intro cols; cbn [pdet map det]; [cbn [eval]; ring|].
  rewrite eval_plap. apply lap_ext. intros c cs. rewrite eval_mul,IH. reflexivity.
Qed.

Lemma length_pdet rows : valid rows -> forall cols,(length (pdet rows cols)<=S(degree rows))%nat.
Proof.
  intro H. induction H as [|[d r] rs Hr Hrs IH]; intro cols; cbn [pdet degree]; [reflexivity|].
  apply length_plap. intros c cs. pose proof (length_mul (r c) (pdet rs cs)).
  specialize (Hr c). specialize (IH cs). cbn [fst snd] in Hr. lia.
Qed.

Theorem leading_pdet rows : valid rows -> forall cols,
  coeff (pdet rows cols) (degree rows)=det (map (fun p c => coeff (snd p c) (fst p)) rows) cols.
Proof.
  intro H. induction H as [|[d r] rs Hr Hrs IH]; intro cols; cbn [pdet degree map det]; [reflexivity|].
  rewrite coeff_plap. apply lap_ext. intros c cs.
  rewrite coeff_mul_top; [rewrite IH; reflexivity|apply Hr|apply length_pdet,Hrs].
Qed.

End Matrices.
End PolynomialDeterminants.

Module Transpose.
Import Determinants.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma lap_exchange {I J} (xs:list I) (ys:list J) F :
  lap xs (fun x xs => lap ys (fun y ys => F x xs y ys))=
  lap ys (fun y ys => lap xs (fun x xs => F x xs y ys)).
Proof.
  revert F. induction xs as [|x xs IH]; intro F; cbn [lap].
  - symmetry. apply lap_zero.
  - rewrite IH,lap_sub. reflexivity.
Qed.

Lemma column_expansion {I J} (M:J->I->Z) xs : forall y ys,
  length xs=S(length ys) ->
  det (map M xs) (y::ys)=lap xs (fun x xs => M x y*det (map M xs) ys).
Proof.
  induction xs as [|x xs IH]; intros y ys Hlen; [discriminate|].
  change (M x y*det (map M xs) ys-lap ys (fun z zs => M x z*det (map M xs) (y::zs))=
    M x y*det (map M xs) ys-lap xs (fun z zs => M z y*det (map M (x::zs)) ys)).
  f_equal.
  rewrite (lap_congr ys (fun z zs => M x z*det (map M xs) (y::zs))
    (fun z zs => lap xs (fun t ts => M x z*(M t y*det (map M ts) zs)))).
  - rewrite lap_exchange. apply lap_ext. intros t ts. cbn [map det].
    rewrite <-lap_scale. apply lap_ext. intros. ring.
  - intros z zs Hp. rewrite IH; [symmetry; apply lap_scale|].
    pose proof (Permutation_length Hp). cbn [List.length] in *. lia.
Qed.

Theorem transpose {I J} (M:J->I->Z) xs ys : length xs=length ys ->
  det (map M xs) ys=det (map (fun y x => M x y) ys) xs.
Proof.
  revert xs. induction ys as [|y ys IH]; intros xs Hlen.
  - destruct xs; [reflexivity|discriminate].
  - rewrite column_expansion by (cbn [List.length] in Hlen; exact Hlen).
    cbn [map det]. apply lap_congr. intros x xs' Hp. rewrite IH; [reflexivity|].
    pose proof (Permutation_length Hp). cbn [List.length] in Hlen,H. lia.
Qed.

Lemma row_permutation_zero {I} (rows rows':list (I->Z)) : Permutation rows rows' ->
  forall pre cols, det (pre++rows) cols=0 <-> det (pre++rows') cols=0.
Proof.
  intro H. induction H; intros pre cols; try reflexivity.
  - replace (pre++x::l) with ((pre++[x])++l) by (rewrite <-app_assoc; reflexivity).
    replace (pre++x::l') with ((pre++[x])++l') by (rewrite <-app_assoc; reflexivity).
    apply IHPermutation.
  - rewrite det_swap. lia.
  - rewrite IHPermutation1,IHPermutation2. reflexivity.
Qed.

Lemma column_permutation_zero {I J} (M:J->I->Z) xs ys zs :
  length xs=length ys -> Permutation ys zs ->
  (det (map M xs) ys=0 <-> det (map M xs) zs=0).
Proof.
  intros Hlen Hp. rewrite (transpose M xs ys Hlen),
    (transpose M xs zs ltac:(pose proof (Permutation_length Hp); lia)).
  exact (row_permutation_zero _ _ (Permutation_map (fun y x => M x y) Hp) [] xs).
Qed.

Lemma repeated_rows {I J} (eq_dec:forall x y:J,{x=y}+{x<>y}) (basis:J->I->Z) xs cols :
  ~NoDup xs -> det (map basis xs) cols=0.
Proof.
  revert cols. induction xs as [|x xs IH]; intros cols H; [exfalso; apply H; constructor|].
  destruct (in_dec eq_dec x xs) as [Hin|Hnot].
  - apply in_split in Hin. destruct Hin as [pre [post ->]].
    rewrite map_cons,map_app,map_cons. apply (det_duplicate [] (map basis pre) (basis x) (map basis post)).
  - assert (Hxs : ~NoDup xs) by (intro Hxs; apply H; constructor; assumption).
    cbn [map det]. rewrite (lap_ext cols (fun c cs => basis x c*det (map basis xs) cs)
      (fun _ _ => 0)) by (intros; rewrite IH by exact Hxs; ring). apply lap_zero.
Qed.

Theorem square_independent {I} (eq_dec:forall x y:I,{x=y}+{x<>y}) (rows:list (I->Z)) cols :
  length rows=length cols -> NonzeroMinor.independent rows cols -> det rows cols<>0.
Proof.
  intros Hlen Hind Hzero.
  destruct (NonzeroMinor.nonzero_minor rows cols Hind) as [cs [Hcs [Hincl Hdet]]].
  assert (Hnd : NoDup cs).
  { destruct (NoDup_dec eq_dec cs) as [H|H]; [exact H|]. exfalso. apply Hdet.
    pose proof (transpose (fun (r:I->Z) c => r c) rows cs ltac:(lia)) as Ht.
    rewrite map_id in Ht. rewrite Ht. apply (repeated_rows eq_dec); exact H. }
  assert (Hp : Permutation cs cols) by (apply NoDup_Permutation_bis; try assumption; lia).
  pose proof (column_permutation_zero (fun (r:I->Z) c => r c) rows cs cols ltac:(lia) Hp) as Hperm.
  rewrite map_id in Hperm. apply Hdet,Hperm,Hzero.
Qed.

End Transpose.

Module Vandermonde.
Import Determinants NonzeroMinor Polynomials Transpose.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma combination_powers n ws a x : length ws=n ->
  combination (map (fun k => fun x => x^Z.of_nat k) (seq a n)) ws x=
  x^Z.of_nat a*eval ws x.
Proof.
  revert ws a. induction n as [|n IH]; intros [|w ws] a Hlen;
    cbn [List.length] in Hlen; try discriminate.
  - cbn [seq map combination eval]. ring.
  - cbn [seq map combination eval]. rewrite IH by lia.
    rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia. ring.
Qed.

Theorem power_matrix_nonzero qs : NoDup qs ->
  det (map (fun k x => x^Z.of_nat k) (seq 0 (length qs))) qs<>0.
Proof.
  intro Hnd. apply (square_independent Z.eq_dec).
  - rewrite length_map,length_seq. reflexivity.
  - intros ws Hlen Hz. rewrite length_map,length_seq in Hlen.
    apply (roots_force_zero ws qs Hnd); [|lia]. rewrite Forall_forall. intros x Hx.
    specialize (Hz x Hx). rewrite combination_powers in Hz by exact Hlen.
    change (1*eval ws x=0) in Hz. lia.
Qed.

Theorem nonzero qs : NoDup qs ->
  det (map (fun q a => q^Z.of_nat a) qs) (seq 0 (length qs))<>0.
Proof.
  intro Hnd. rewrite (transpose (fun q a => q^Z.of_nat a) qs (seq 0 (length qs))) by
    (rewrite length_seq; reflexivity). apply power_matrix_nonzero,Hnd.
Qed.

End Vandermonde.

Module Casoratian.
Import Determinants Polynomials PolynomialDeterminants.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma scaled_rows {I J} (f:J->I->Z) (a:J->Z) rs : forall cols,
  det (map (fun r c => a r*f r c) rs) cols=product (map a rs)*det (map f rs) cols.
Proof.
  induction rs as [|r rs IH]; intro cols; cbn [map product det]; [ring|].
  rewrite <-lap_scale. apply lap_ext. intros c cs. rewrite IH. ring.
Qed.

Lemma product_nonzero xs : Forall (fun x => x<>0) xs -> product xs<>0.
Proof. intro H. induction H; cbn [product]; [lia|intro E; apply Z.mul_eq_0 in E; tauto]. Qed.

Record term := Term { base:Z; order:nat; polynomial:list Z }.
Definition lc t := coeff (polynomial t) (order t).
Definition good t := (length (polynomial t)<=S(order t))%nat /\ lc t<>0.
Definition rows ts := map (fun t => (order t,
  fun a => scale ((base t)^Z.of_nat a) (shift (polynomial t) (Z.of_nat a)))) ts.
Definition cols (ts:list term) := seq 0 (length ts).
Definition H ts := pdet (rows ts) (cols ts).
Definition degree ts := PolynomialDeterminants.degree (rows ts).

Lemma rows_valid ts : Forall good ts -> valid (rows ts).
Proof.
  intro Hg. unfold rows,valid. rewrite Forall_map.
  eapply Forall_impl; [|exact Hg]. intros t [Hlen Hlc] a. cbn [fst snd].
  rewrite length_scale. pose proof (length_shift (polynomial t) (Z.of_nat a)). lia.
Qed.

Theorem leading_nonzero ts : NoDup (map base ts) -> Forall good ts -> coeff (H ts) (degree ts)<>0.
Proof.
  intros Hnd Hg. unfold H,degree. rewrite leading_pdet by (apply rows_valid,Hg).
  unfold rows. rewrite map_map.
  rewrite (det_ext _ (map (fun t a => lc t*(base t)^Z.of_nat a) ts) (cols ts)).
  - rewrite scaled_rows. intro E. apply Z.mul_eq_0 in E. destruct E as [E|E].
    + apply (product_nonzero (map lc ts)); [|exact E].
      rewrite Forall_map. eapply Forall_impl; [|exact Hg]. intros t [_ Ht]. exact Ht.
    + pose proof (Vandermonde.nonzero (map base ts) Hnd) as HV.
      rewrite map_map,length_map in HV. exact (HV E).
  - clear Hnd. generalize (cols ts); intro cs.
    induction Hg as [|t ts [Hlen Hlc] Hg IH]; cbn [map]; constructor; [|exact IH].
    intros a Ha. cbn [fst snd]. rewrite coeff_scale,coeff_shift_top by exact Hlen. unfold lc. ring.
Qed.

Theorem root_bound ts roots : NoDup (map base ts) -> Forall good ts ->
  NoDup roots -> Forall (fun x => eval (H ts) x=0) roots -> (length roots<=degree ts)%nat.
Proof.
  intros Hnd Hg Hr Hz. destruct (Nat.le_gt_cases (length roots) (degree ts)); [assumption|].
  exfalso. apply (leading_nonzero ts Hnd Hg).
  assert (Hp : Forall (fun a => a=0) (H ts)).
  { apply (roots_force_zero _ roots Hr Hz).
    pose proof (length_pdet (rows ts) (rows_valid ts Hg) (cols ts)). unfold H,degree in *. lia. }
  destruct (Nat.lt_ge_cases (degree ts) (length (H ts))) as [Hin|Hout].
  - rewrite Forall_forall in Hp. apply Hp. apply nth_In,Hin.
  - apply coeff_over,Hout.
Qed.

End Casoratian.

Module GridBase.
Import Polynomials.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Fixpoint trim (p:list Z) : list Z :=
  match p with [] => [] | a::p =>
    match trim p with [] => if Z.eq_dec a 0 then [] else [a] | q => a::q end
  end.

Lemma trim_spec p : (length (trim p)<=length p)%nat /\
  (forall x,eval (trim p) x=eval p x) /\
  (trim p=[] \/ coeff (trim p) (Nat.pred (length (trim p)))<>0).
Proof.
  induction p as [|a p [Hlen [He Hlc]]]; [cbn [trim]; auto|].
  cbn [trim]. destruct (trim p) as [|b q] eqn:Hp.
  - cbn [List.length] in Hlen. destruct (Z.eq_dec a 0) as [->|Ha].
    + split; [cbn [List.length]; lia|]. split; [intro x; specialize (He x); cbn [eval] in *; lia|auto].
    + split; [cbn [List.length]; lia|]. split; [intro x; specialize (He x); cbn [eval] in *; nia|].
      right. exact Ha.
  - split; [cbn [List.length] in *; lia|]. split.
    + intro x. change (a+x*eval (b::q) x=a+x*eval p x). rewrite He. reflexivity.
    + destruct Hlc as [Hlc|Hlc]; [discriminate|]. right.
      change (coeff (b::q) (length q)<>0). exact Hlc.
Qed.

Lemma trim_empty p : trim p=[] -> Forall (fun a => a=0) p.
Proof.
  intro H. induction p as [|a p IH]; [constructor|]. cbn [trim] in H.
  destruct (trim p) as [|b q] eqn:Hp; [|discriminate].
  destruct (Z.eq_dec a 0); [constructor; auto|discriminate].
Qed.

Definition point n (rs:nat*nat) := Z.of_nat (fst rs)+Z.of_nat n*Z.of_nat (snd rs).

Fixpoint grid (R S:nat) : list (nat*nat) :=
  match S with O => [] | S s => grid R s++map (fun r => (r,s)) (seq 0 R) end.

Lemma grid_length R S : length (grid R S)=(R*S)%nat.
Proof.
  induction S; cbn [grid]; [cbn [List.length]; lia|]. rewrite length_app,length_map,length_seq,IHS. lia.
Qed.

Lemma grid_in R S r s : In (r,s) (grid R S) <-> (r<R /\ s<S)%nat.
Proof.
  induction S as [|S IH]; cbn [grid In]; [intuition lia|].
  rewrite in_app_iff,IH,in_map_iff. split.
  - intros [H|[r' [E Hr']]]; [lia|]. inversion E; subst. apply in_seq in Hr'. lia.
  - intros [Hr Hs]. destruct (Nat.eq_dec s S) as [->|Hne]; [right|left; lia].
    exists r. split; [reflexivity|apply in_seq; lia].
Qed.

Lemma map_nodup {A B} (f:A->B) xs : NoDup xs ->
  (forall x y,In x xs -> In y xs -> f x=f y -> x=y) -> NoDup (map f xs).
Proof.
  intro H. induction H as [|x xs Hnot Hnd IH]; intro Hinj; [constructor|]. constructor.
  - intro Hmap. apply in_map_iff in Hmap. destruct Hmap as [y [Hy Hyin]].
    assert (y=x) by (apply Hinj; cbn; auto). subst. contradiction.
  - apply IH. intros u v Hu Hv. apply Hinj; cbn; auto.
Qed.

Lemma nodup_app {A} (xs ys:list A) : NoDup xs -> NoDup ys ->
  (forall x,In x xs -> ~In x ys) -> NoDup (xs++ys).
Proof.
  intro Hx. induction Hx as [|x xs Hnot Hx IH]; intros Hy Hdis; cbn [List.app]; [exact Hy|]. constructor.
  - rewrite in_app_iff. intros [H|H]; [contradiction|apply (Hdis x); cbn; auto].
  - apply IH; [exact Hy|]. intros y Hy'. apply Hdis; cbn; auto.
Qed.

Lemma point_injective n R r s r' s' : (R<=n)%nat -> (r<R)%nat -> (r'<R)%nat ->
  point n (r,s)=point n (r',s') -> r=r' /\ s=s'.
Proof.
  unfold point. cbn [fst snd]. intros Hn Hr Hr' He.
  assert (Hss : s=s').
  { destruct (Nat.lt_trichotomy s s') as [Hlt|[Heq|Hgt]]; [|exact Heq|]; nia. }
  subst s'. split; [lia|reflexivity].
Qed.

Lemma grid_points_nodup n R S : (R<=n)%nat -> NoDup (map (point n) (grid R S)).
Proof.
  intro Hn. induction S as [|S IH]; cbn [grid map]; [constructor|].
  rewrite map_app,map_map. apply nodup_app; [exact IH| |].
  - apply map_nodup; [apply seq_NoDup|]. intros r r' Hr Hr' He.
    unfold point in He. cbn [fst snd] in He. lia.
  - intros x Hx Hy. apply in_map_iff in Hx,Hy.
    destruct Hx as [[r s] [Hx Hrs]],Hy as [r' [Hy Hr']].
    apply grid_in in Hrs. apply in_seq in Hr'.
    destruct (point_injective n R r s r' S Hn ltac:(lia) ltac:(lia) ltac:(congruence)). lia.
Qed.

End GridBase.

Module GridPolynomials.
Import Polynomials GridBase.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Definition lterm := (nat*list Z)%type.
Definition qbase l := (-3)^Z.of_nat l.

Fixpoint bivar (ts:list lterm) x y : Z :=
  match ts with [] => 0 | (l,p)::ts => eval p x*y^Z.of_nat l+bivar ts x y end.

Fixpoint prepare (ts:list lterm) : list lterm :=
  match ts with [] => [] | (l,p)::ts =>
    match trim p with [] => prepare ts | q => (l,q)::prepare ts end
  end.

Definition cast (t:lterm) :=
  Casoratian.Term (qbase (fst t)) (Nat.pred (length (snd t))) (snd t).

Lemma prepare_eval ts x y : bivar (prepare ts) x y=bivar ts x y.
Proof.
  induction ts as [|[l p] ts IH]; [reflexivity|]. cbn [prepare].
  destruct (trim_spec p) as [Hlen [He Hlc]].
  destruct (trim p) as [|a q] eqn:Hp; cbn [bivar]; rewrite IH.
  - specialize (He x). cbn [eval] in He. rewrite <-He. ring.
  - rewrite He. reflexivity.
Qed.

Lemma prepare_length ts : (length (prepare ts)<=length ts)%nat.
Proof.
  induction ts as [|[l p] ts IH]; [reflexivity|]. cbn [prepare].
  destruct (trim p); cbn [List.length]; lia.
Qed.

Lemma prepare_empty ts : prepare ts=[] -> Forall (fun t => Forall (fun a => a=0) (snd t)) ts.
Proof.
  induction ts as [|[l p] ts IH]; intro H; [constructor|]. cbn [prepare] in H.
  destruct (trim p) eqn:Hp; [constructor; [apply trim_empty,Hp|apply IH,H]|discriminate].
Qed.

Lemma prepare_in ts l p : In (l,p) (prepare ts) ->
  exists q,In (l,q) ts /\ p=trim q /\ p<>[].
Proof.
  induction ts as [|[a q] ts IH]; cbn [prepare]; intro Hin; [contradiction|].
  destruct (trim q) as [|b qs] eqn:Hq.
  - destruct (IH Hin) as [p' [Hi Hp]]. exists p'. split; [right; exact Hi|exact Hp].
  - destruct Hin as [E|Hi].
    + inversion E; subst. exists q. split; [left; reflexivity|]. split; [symmetry; exact Hq|discriminate].
    + destruct (IH Hi) as [p' [Hj Hp]]. exists p'. split; [right; exact Hj|exact Hp].
Qed.

Lemma prepare_good ts : Forall Casoratian.good (map cast (prepare ts)).
Proof.
  rewrite Forall_map,Forall_forall. intros [l p] Hp.
  destruct (prepare_in ts l p Hp) as [q [Hq [-> Hne]]].
  destruct (trim_spec q) as [_ [_ Hlc]]. unfold Casoratian.good,Casoratian.lc,cast.
  cbn [fst snd Casoratian.order Casoratian.polynomial].
  split; [destruct (trim q); cbn [List.length]; lia|tauto].
Qed.

Lemma prepare_bound ts K : Forall (fun t => (length (snd t)<=K)%nat) ts ->
  Forall (fun t => (length (snd t)<=K)%nat) (prepare ts).
Proof.
  rewrite !Forall_forall. intros H [l p] Hp.
  destruct (prepare_in ts l p Hp) as [q [Hq [-> Hne]]].
  specialize (H (l,q) Hq). pose proof (proj1 (trim_spec q)). cbn [snd] in H |- *. lia.
Qed.

Lemma prepare_labels ts : incl (map fst (prepare ts)) (map fst ts).
Proof.
  intros l Hl. apply in_map_iff in Hl. destruct Hl as [[l' p] [E Hp]]. cbn [fst] in E. subst l'.
  destruct (prepare_in ts l p Hp) as [q [Hq _]]. apply in_map_iff. exists (l,q). split; [reflexivity|exact Hq].
Qed.

Lemma prepare_nodup ts : NoDup (map fst ts) -> NoDup (map fst (prepare ts)).
Proof.
  induction ts as [|[l p] ts IH]; intro H; [constructor|]. cbn [map fst] in H.
  inversion H as [|l0 ls Hnot Hnd]; subst. cbn [prepare]. destruct (trim p); cbn [map fst]; [apply IH,Hnd|].
  constructor; [intro Hi; apply Hnot,prepare_labels,Hi|apply IH,Hnd].
Qed.

Lemma qbase_injective l k : qbase l=qbase k -> l=k.
Proof.
  unfold qbase. intro He. apply (f_equal Z.abs) in He. rewrite !Z.abs_pow in He.
  change (3^Z.of_nat l=3^Z.of_nat k) in He.
  apply Z.pow_inj_r in He; lia.
Qed.

Lemma cast_nodup ts : NoDup (map fst ts) -> NoDup (map Casoratian.base (map cast ts)).
Proof.
  intro H. rewrite map_map. change (NoDup (map (fun t => qbase (fst t)) ts)).
  rewrite <-map_map. apply map_nodup; [exact H|]. intros x y _ _ He. apply qbase_injective,He.
Qed.

Lemma cast_degree ts K : Forall (fun t => (length (snd t)<=K)%nat) ts ->
  (Casoratian.degree (map cast ts)<=(K-1)*length ts)%nat.
Proof.
  intro H. induction H as [|[l p] ts Hp Hts IH]; unfold Casoratian.degree,Casoratian.rows in *;
    cbn [map List.length PolynomialDeterminants.degree cast fst snd Casoratian.order] in *.
  - lia.
  - cbn [List.length snd] in *. nia.
Qed.

Definition height u (rs:nat*nat) := (-3)^Z.of_nat (fst rs)*u^Z.of_nat (snd rs).
Definition values ts x := map (fun t a => (qbase (fst t))^Z.of_nat a*
  eval (snd t) (x+Z.of_nat a)) ts.
Definition weights (ts:list lterm) y := map (fun t => y^Z.of_nat (fst t)) ts.

Lemma height_nonzero u rs : u<>0 -> height u rs<>0.
Proof.
  intro Hu. unfold height. intro H. apply Z.mul_eq_0 in H. destruct H as [H|H].
  - exact (Z.pow_nonzero (-3) (Z.of_nat (fst rs)) ltac:(lia) ltac:(lia) H).
  - exact (Z.pow_nonzero u (Z.of_nat (snd rs)) Hu ltac:(lia) H).
Qed.

Lemma qbase_comm l a : (qbase l)^Z.of_nat a=((-3)^Z.of_nat a)^Z.of_nat l.
Proof. unfold qbase. rewrite <-!Z.pow_mul_r by lia. f_equal. ring. Qed.

Lemma bivar_shift ts x y a :
  NonzeroMinor.combination (values ts x) (weights ts y) a=
  bivar ts (x+Z.of_nat a) ((-3)^Z.of_nat a*y).
Proof.
  induction ts as [|[l p] ts IH]; [reflexivity|].
  change (y^Z.of_nat l*((qbase l)^Z.of_nat a*eval p (x+Z.of_nat a))+
    NonzeroMinor.combination (values ts x) (weights ts y) a=
    eval p (x+Z.of_nat a)*((-3)^Z.of_nat a*y)^Z.of_nat l+
    bivar ts (x+Z.of_nat a) ((-3)^Z.of_nat a*y)).
  rewrite IH,Z.pow_mul_l,qbase_comm. ring.
Qed.

Lemma H_eval ts x : eval (Casoratian.H (map cast ts)) x=
  Determinants.det (values ts x) (seq 0 (length ts)).
Proof.
  unfold Casoratian.H,Casoratian.cols. rewrite length_map,PolynomialDeterminants.eval_pdet.
  unfold Casoratian.rows,values. rewrite !map_map.
  generalize (seq 0 (length ts)); intro cs. apply Determinants.det_ext.
  induction ts as [|[l p] ts IH]; cbn [map]; constructor; [|exact IH].
  intros a Ha. cbn [cast fst snd Casoratian.order Casoratian.polynomial Casoratian.base].
  rewrite eval_scale,eval_shift. reflexivity.
Qed.

Lemma relation_root ts x y : ts<>[] -> y<>0 ->
  (forall a,(a<length ts)%nat -> bivar ts (x+Z.of_nat a) ((-3)^Z.of_nat a*y)=0) ->
  eval (Casoratian.H (map cast ts)) x=0.
Proof.
  intros Hts Hy Hrel. rewrite H_eval. destruct ts as [|[l p] ts]; [contradiction|].
  unfold values at 1. cbn [map].
  apply (NonzeroMinor.relation_forces_zero _ _ (y^Z.of_nat l) (weights ts y)).
  - apply Z.pow_nonzero; [exact Hy|lia].
  - intros a Ha. change (NonzeroMinor.combination (values ((l,p)::ts) x) (weights ((l,p)::ts) y) a=0).
    rewrite bivar_shift. apply Hrel. apply in_seq in Ha. lia.
Qed.

Lemma point_shift n r s a : point n ((r+a)%nat,s)=point n (r,s)+Z.of_nat a.
Proof. unfold point. cbn [fst snd]. rewrite Nat2Z.inj_add. ring. Qed.

Lemma height_shift u r s a : height u ((r+a)%nat,s)=(-3)^Z.of_nat a*height u (r,s).
Proof. unfold height. cbn [fst snd]. rewrite Nat2Z.inj_add,Z.pow_add_r by lia. ring. Qed.

Theorem grid_vanish K L n u R0 S ts :
  (R0<=n)%nat -> ((K-1)*L<R0*S)%nat -> (length ts<=L)%nat -> u<>0 ->
  NoDup (map fst ts) -> Forall (fun t => (length (snd t)<=K)%nat) ts ->
  (forall r s,(r<R0+L-1)%nat -> (s<S)%nat -> bivar ts (point n (r,s)) (height u (r,s))=0) ->
  Forall (fun t => Forall (fun a => a=0) (snd t)) ts.
Proof.
  intros Hn Hsize Hlength Hu Hnd Hbound Hz.
  destruct (prepare ts) as [|t pts] eqn:Hprep.
  - apply prepare_empty,Hprep.
  - exfalso. assert (Hne : prepare ts<>[]) by (rewrite Hprep; discriminate).
    assert (Hroots : Forall (fun x => eval (Casoratian.H (map cast (prepare ts))) x=0)
      (map (point n) (grid R0 S))).
    { rewrite Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [[r s] [<- Hrs]].
      apply grid_in in Hrs. apply (relation_root _ _ (height u (r,s)) Hne (height_nonzero u (r,s) Hu)).
      intros a Ha. rewrite <-point_shift,<-height_shift,prepare_eval. apply Hz; [|lia].
      assert (HaL : (a<L)%nat) by
        (exact (Nat.lt_le_trans _ _ _ Ha (Nat.le_trans _ _ _ (prepare_length ts) Hlength))).
      destruct Hrs as [Hr Hs]. clear -Hr HaL. lia. }
    pose proof (Casoratian.root_bound (map cast (prepare ts)) _
      (cast_nodup _ (prepare_nodup ts Hnd)) (prepare_good ts)
      (grid_points_nodup n R0 S Hn) Hroots) as Hcount.
    pose proof (cast_degree (prepare ts) K (prepare_bound ts K Hbound)) as Hdegree.
    pose proof (prepare_length ts) as Hplen. rewrite length_map,grid_length in Hcount.
    apply (Nat.lt_irrefl ((K-1)*L)).
    eapply Nat.lt_le_trans; [exact Hsize|]. eapply Nat.le_trans; [exact Hcount|].
    eapply Nat.le_trans; [exact Hdegree|]. apply Nat.mul_le_mono_l.
    exact (Nat.le_trans _ _ _ Hplen Hlength).
Qed.

End GridPolynomials.

Module GridMatrix.
Import Polynomials NonzeroMinor GridBase GridPolynomials.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Fixpoint indices (K a L:nat) : list (nat*nat) :=
  match L with O => [] | S len => map (fun k => (k,a)) (seq 0 K)++indices K (S a) len end.

Definition entry n u (kl rs:nat*nat) := (point n rs)^Z.of_nat (fst kl)*(height u rs)^Z.of_nat (snd kl).

Fixpoint pack (K a L:nat) (ws:list Z) : list lterm :=
  match L with O => [] | S len => (a,firstn K ws)::pack K (S a) len (skipn K ws) end.

Lemma indices_length K a L : length (indices K a L)=(K*L)%nat.
Proof.
  revert a. induction L; intro a; cbn [indices List.length]; [lia|].
  rewrite length_app,length_map,length_seq,IHL. lia.
Qed.

Lemma indices_in K L : forall a k l,
  In (k,l) (indices K a L) <-> (k<K /\ a<=l<a+L)%nat.
Proof.
  induction L as [|L IH]; intros a k l; cbn [indices]; [cbn [In]; lia|].
  rewrite in_app_iff,in_map_iff,IH. split.
  - intros [[k' [E Hk]]|Hkl]; [inversion E; subst; apply in_seq in Hk|]; lia.
  - intros [Hk Hl]. destruct (Nat.eq_dec l a) as [->|Hne]; [left|right; lia].
    exists k. split; [reflexivity|apply in_seq; lia].
Qed.

Lemma pack_labels K a L ws : map fst (pack K a L ws)=seq a L.
Proof.
  revert a ws. induction L; intros a ws; cbn [pack map seq fst]; [reflexivity|rewrite IHL; reflexivity].
Qed.

Lemma pack_length K a L ws : length (pack K a L ws)=L.
Proof. pose proof (f_equal (@length nat) (pack_labels K a L ws)). rewrite length_map,length_seq in H. exact H. Qed.

Lemma pack_bound K a L ws : Forall (fun t => (length (snd t)<=K)%nat) (pack K a L ws).
Proof.
  revert a ws. induction L; intros a ws; cbn [pack]; constructor; [|apply IHL].
  cbn [snd]. rewrite firstn_length. lia.
Qed.

Lemma pack_zero K a L ws : length ws=(K*L)%nat ->
  Forall (fun t => Forall (fun a => a=0) (snd t)) (pack K a L ws) -> Forall (fun a => a=0) ws.
Proof.
  revert a ws. induction L as [|L IH]; intros a ws Hlen Hz.
  - assert (ws=[]) by (destruct ws; cbn [List.length] in *; [reflexivity|nia]). subst. constructor.
  - cbn [pack] in Hz. inversion Hz as [|t ts Hhead Htail]; subst.
    rewrite <-(firstn_skipn K ws). apply Forall_app. split; [exact Hhead|].
    apply (IH (S a)); [rewrite skipn_length; nia|exact Htail].
Qed.

Lemma combination_app {I} (rs ss:list (I->Z)) ws c :
  combination (rs++ss) ws c=combination rs (firstn (length rs) ws) c+
    combination ss (skipn (length rs) ws) c.
Proof.
  assert (Hnil : forall qs:list (I->Z),combination qs [] c=0) by (intros [|q qs]; reflexivity).
  revert ws. induction rs as [|r rs IH]; intro ws.
  - cbn [List.app List.length firstn skipn combination]. ring.
  - destruct ws as [|w ws].
    + rewrite firstn_nil,skipn_nil,!Hnil. ring.
    + cbn [List.app List.length firstn skipn combination]. rewrite IH. ring.
Qed.

Lemma block_eval n u l K ws : forall a rs,length ws=K ->
  combination (map (fun k => entry n u (k,l)) (seq a K)) ws rs=
  (point n rs)^Z.of_nat a*eval ws (point n rs)*(height u rs)^Z.of_nat l.
Proof.
  revert ws. induction K as [|K IH]; intros [|w ws] a rs Hlen;
    cbn [List.length] in Hlen; try discriminate.
  - cbn [seq map combination eval]. ring.
  - cbn [seq map combination eval]. rewrite IH by lia.
    unfold entry. cbn [fst snd]. rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia. ring.
Qed.

Lemma pack_eval n u K a L ws rs : length ws=(K*L)%nat ->
  combination (map (entry n u) (indices K a L)) ws rs=
  bivar (pack K a L ws) (point n rs) (height u rs).
Proof.
  revert a ws. induction L as [|L IH]; intros a ws Hlen.
  - destruct ws; cbn [List.length] in Hlen; [reflexivity|nia].
  - cbn [indices pack bivar]. rewrite map_app,combination_app,map_map,!length_map,length_seq.
    rewrite block_eval by (rewrite firstn_length; nia).
    rewrite IH by (rewrite skipn_length; nia). change (1*eval (firstn K ws) (point n rs)*(height u rs)^Z.of_nat a+
      bivar (pack K (S a) L (skipn K ws)) (point n rs) (height u rs)=
      eval (firstn K ws) (point n rs)*(height u rs)^Z.of_nat a+
      bivar (pack K (S a) L (skipn K ws)) (point n rs) (height u rs)). ring.
Qed.

Theorem independent_grid K L n u R0 S : (R0<=n)%nat -> ((K-1)*L<R0*S)%nat -> u<>0 ->
  independent (map (entry n u) (indices K 0 L)) (grid (R0+L-1) S).
Proof.
  intros Hn Hsize Hu ws Hlen Hz. rewrite length_map,indices_length in Hlen.
  apply (pack_zero K 0 L ws Hlen).
  apply (grid_vanish K L n u R0 S); try assumption.
  - rewrite pack_length. lia.
  - rewrite pack_labels. apply seq_NoDup.
  - apply pack_bound.
  - intros r s Hr Hs. rewrite <-pack_eval by exact Hlen. apply Hz,grid_in. lia.
Qed.

Theorem nonzero_grid K L n u R0 S : (R0<=n)%nat -> ((K-1)*L<R0*S)%nat -> u<>0 ->
  exists cs,length cs=(K*L)%nat /\ incl cs (grid (R0+L-1) S) /\
    Determinants.det (map (entry n u) (indices K 0 L)) cs<>0.
Proof.
  intros Hn Hsize Hu.
  destruct (nonzero_minor _ _ (independent_grid K L n u R0 S Hn Hsize Hu)) as [cs [Hcs Hrest]].
  exists cs. split; [rewrite length_map,indices_length in Hcs; exact Hcs|exact Hrest].
Qed.

End GridMatrix.

Module GridArithmetic.
Import Determinants GridBase GridPolynomials GridMatrix.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma det_map_ext {I J} (xs:list J) (f g:J->I->Z) cols :
  (forall x,In x xs -> forall c,In c cols -> f x c=g x c) ->
  det (map f xs) cols=det (map g xs) cols.
Proof.
  intro H. apply det_ext. induction xs; cbn [map]; constructor.
  - intros c Hc. apply H; [left; reflexivity|exact Hc].
  - apply IHxs. intros x Hx. apply H; right; exact Hx.
Qed.

Lemma det_map_congr {I J} (xs:list J) (f g:J->I->Z) cols M :
  (forall x,In x xs -> forall c,In c cols -> (M | f x c-g x c)) ->
  (M | det (map f xs) cols-det (map g xs) cols).
Proof.
  intro H. apply det_congr. induction xs; cbn [map]; constructor.
  - intros c Hc. apply H; [left; reflexivity|exact Hc].
  - apply IHxs. intros x Hx. apply H; right; exact Hx.
Qed.

Lemma pow_residue M a b e : 0<M -> a mod M=b mod M -> (a^e) mod M=(b^e) mod M.
Proof. intros HM H. rewrite (Zpower_mod a e M HM),(Zpower_mod b e M HM),H. reflexivity. Qed.

Lemma qbase_four l : (4 | qbase l-1).
Proof.
  apply (proj2 (Modular.congr_mod 4 (qbase l) 1 ltac:(lia))).
  unfold qbase. rewrite (Zpower_mod (-3) (Z.of_nat l) 4 ltac:(lia)).
  change (1^Z.of_nat l mod 4=1 mod 4). rewrite Z.pow_1_l by lia. reflexivity.
Qed.

Definition point_nat n (rs:nat*nat) := (fst rs+n*snd rs)%nat.
Lemma point_nat_spec n rs : Z.of_nat (point_nat n rs)=point n rs.
Proof. unfold point_nat,point. rewrite Nat2Z.inj_add,Nat2Z.inj_mul. reflexivity. Qed.

Definition compare_entry n (kl rs:nat*nat) :=
  (point n rs)^Z.of_nat (fst kl)*(qbase (snd kl))^(point n rs).

Lemma entry_congr n u kl rs : (2^Z.of_nat n | (-3)^Z.of_nat n-u) ->
  (2^Z.of_nat n | entry n u kl rs-compare_entry n kl rs).
Proof.
  intro Hbad. set (M:=2^Z.of_nat n).
  assert (HM : 0<M) by (apply Modular.pow_pos; lia).
  assert (Hb : ((-3)^Z.of_nat n) mod M=u mod M) by (apply (proj1 (Modular.congr_mod M _ _ HM)); exact Hbad).
  destruct kl as [k l],rs as [r s].
  assert (Hp : 0<=point n (r,s)) by (unfold point; cbn [fst snd]; nia).
  assert (Hy : height u (r,s) mod M=((-3)^point n (r,s)) mod M).
  { unfold height,point. cbn [fst snd]. rewrite Z.pow_add_r,Z.pow_mul_r by lia.
    rewrite (Z.mul_mod ((-3)^Z.of_nat r) (u^Z.of_nat s) M ltac:(lia)),
      (Z.mul_mod ((-3)^Z.of_nat r) (((-3)^Z.of_nat n)^Z.of_nat s) M ltac:(lia)).
    f_equal. f_equal. apply pow_residue; [exact HM|symmetry; exact Hb]. }
  assert (He : (height u (r,s)^Z.of_nat l) mod M=((qbase l)^point n (r,s)) mod M).
  { unfold qbase. rewrite <-Z.pow_mul_r by lia.
    rewrite (Z.mul_comm (Z.of_nat l) (point n (r,s))),Z.pow_mul_r by lia.
    apply pow_residue; assumption. }
  apply (proj2 (Modular.congr_mod M _ _ HM)).
  unfold entry,compare_entry. cbn [fst snd].
  rewrite (Z.mul_mod (point n (r,s)^Z.of_nat k) (height u (r,s)^Z.of_nat l) M ltac:(lia)),
    (Z.mul_mod (point n (r,s)^Z.of_nat k) ((qbase l)^point n (r,s)) M ltac:(lia)).
  rewrite He. reflexivity.
Qed.

Lemma compare_divide K L n cs E : 0<=E ->
  E<=Z.of_nat (K*L)*(Z.of_nat (K*L)-1-2*Z.of_nat K) ->
  (2^E | det (map (compare_entry n) (indices K 0 L)) cs).
Proof.
  intros HE Hbound.
  set (rs:=map (fun kl => (fst kl,qbase (snd kl))) (indices K 0 L)).
  assert (Hdiv : (2^E | det (map (fun p x => (Z.of_nat x)^Z.of_nat (fst p)*(snd p)^Z.of_nat x) rs)
    (map (point_nat n) cs))).
  { apply (DeterminantDivisibility.evaluation_divide K E); [exact HE| |].
    - unfold rs. rewrite length_map,indices_length. exact Hbound.
    - intros k q Hkq. unfold rs in Hkq. apply in_map_iff in Hkq.
      destruct Hkq as [[k' l] [Eq Hin]]. cbn [fst snd] in Eq. inversion Eq; subst.
      apply indices_in in Hin. split; [lia|apply qbase_four]. }
  rewrite MatrixBounds.det_map_cols in Hdiv. unfold rs in Hdiv. rewrite !map_map in Hdiv.
  erewrite (det_map_ext (indices K 0 L) _ (compare_entry n) cs) in Hdiv; [exact Hdiv|]. intros [k l] Hin c Hc.
  cbn [fst snd]. unfold compare_entry. cbn [fst snd]. rewrite point_nat_spec. reflexivity.
Qed.

Theorem matrix_divide K L n u cs E : 0<=E<=Z.of_nat n ->
  E<=Z.of_nat (K*L)*(Z.of_nat (K*L)-1-2*Z.of_nat K) ->
  (2^Z.of_nat n | (-3)^Z.of_nat n-u) ->
  (2^E | det (map (entry n u) (indices K 0 L)) cs).
Proof.
  intros HE Hbound Hbad.
  pose proof (det_map_congr (indices K 0 L) (entry n u) (compare_entry n) cs (2^Z.of_nat n)
    ltac:(intros; apply entry_congr,Hbad)) as Hcongr.
  assert (Hd : (2^E | det (map (entry n u) (indices K 0 L)) cs-
    det (map (compare_entry n) (indices K 0 L)) cs)).
  { eapply Z.divide_trans; [apply Modular.power_divide; exact HE|exact Hcongr]. }
  pose proof (compare_divide K L n cs E ltac:(lia) Hbound) as Hcomp.
  destruct Hd as [a Ha],Hcomp as [b Hb]. exists (a+b). nia.
Qed.

End GridArithmetic.

Module GridBounds.
Import Determinants GridBase GridPolynomials GridMatrix.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma point_bound n m R S r s : 0<=m -> Z.of_nat R<=Z.of_nat n -> Z.of_nat n<=2^m ->
  Z.of_nat S<=2^m -> (r<R)%nat -> (s<S)%nat -> 0<=point n (r,s)<=2^(2*m).
Proof.
  intros Hm HR Hn HS Hr Hs. unfold point. cbn [fst snd]. split; [nia|].
  eapply Z.le_trans with (m:=Z.of_nat n*Z.of_nat S); [nia|].
  replace (2^(2*m)) with (2^m*2^m) by (rewrite <-Z.pow_add_r by lia; f_equal; ring).
  apply Z.mul_le_mono_nonneg; lia.
Qed.

Lemma entry_bound n u k l r s m : 0<=m -> 0<=u<=2^m -> 0<=point n (r,s)<=2^(2*m) ->
  Z.abs (entry n u (k,l) (r,s))<=
    2^(2*m*Z.of_nat k+(2*Z.of_nat r+m*Z.of_nat s)*Z.of_nat l).
Proof.
  intros Hm Hu Hp.
  assert (Hxy : 0<=3^Z.of_nat r*u^Z.of_nat s) by
    (apply Z.mul_nonneg_nonneg; apply Z.pow_nonneg; lia).
  assert (Hheight : 3^Z.of_nat r*u^Z.of_nat s<=2^(2*Z.of_nat r+m*Z.of_nat s)).
  { rewrite Z.pow_add_r,!Z.pow_mul_r by lia.
    apply Z.mul_le_mono_nonneg; try (apply Z.pow_nonneg; lia).
    - apply Z.pow_le_mono_l. change (0<=3<=4). lia.
    - apply Z.pow_le_mono_l. exact Hu. }
  pose proof (Z.pow_le_mono_l _ _ (Z.of_nat k) Hp) as Hpoint.
  pose proof (Z.pow_le_mono_l _ _ (Z.of_nat l) ltac:(split; [exact Hxy|exact Hheight])) as Hpower.
  unfold entry,height. cbn [fst snd].
  rewrite !Z.abs_mul,!Z.abs_pow,!Z.abs_mul,!Z.abs_pow.
  rewrite (Z.abs_eq (point n (r,s)) ltac:(lia)),(Z.abs_eq u ltac:(lia)).
  change (point n (r,s)^Z.of_nat k*(3^Z.of_nat r*u^Z.of_nat s)^Z.of_nat l<=
    2^(2*m*Z.of_nat k+(2*Z.of_nat r+m*Z.of_nat s)*Z.of_nat l)).
  eapply Z.le_trans with (m:=(2^(2*m))^Z.of_nat k*(2^(2*Z.of_nat r+m*Z.of_nat s))^Z.of_nat l).
  - apply Z.mul_le_mono_nonneg; try (apply Z.pow_nonneg; assumption || lia); assumption.
  - rewrite <-!Z.pow_mul_r,<-Z.pow_add_r by nia. reflexivity.
Qed.

Theorem matrix_bound K L n u R S cs m B :
  length cs=(K*L)%nat -> incl cs (grid R S) ->
  0<=m -> 0<=B -> 0<=u<=2^m ->
  Z.of_nat R<=Z.of_nat n -> Z.of_nat n<=2^m -> Z.of_nat S<=2^m ->
  Z.of_nat (K*L)<=2^m ->
  2*m*Z.of_nat K+(2*Z.of_nat R+m*Z.of_nat S)*Z.of_nat L<=B ->
  Z.abs (det (map (entry n u) (indices K 0 L)) cs)<=2^(Z.of_nat (K*L)*(m+B)).
Proof.
  intros Hlen Hcols Hm HB Hu HR Hn HS HN Hex.
  pose proof (MatrixBounds.uniform_bound (map (entry n u) (indices K 0 L)) cs m B
    ltac:(rewrite length_map,indices_length; lia) Hm HB
    ltac:(rewrite length_map,indices_length; exact HN)) as Hbound.
  rewrite length_map,indices_length in Hbound. apply Hbound.
  intros row Hrow [r s] Hrs. apply in_map_iff in Hrow. destruct Hrow as [[k l] [<- Hkl]].
  apply indices_in in Hkl. apply Hcols,grid_in in Hrs.
  eapply Z.le_trans; [apply (entry_bound n u k l r s m Hm Hu)|].
  - apply (point_bound n m R S); tauto.
  - apply Z.pow_le_mono_r; [lia|].
    assert (Hkl' : Z.of_nat k<=Z.of_nat K /\ Z.of_nat l<=Z.of_nat L) by lia.
    assert (Hrs' : Z.of_nat r<=Z.of_nat R /\ Z.of_nat s<=Z.of_nat S) by lia.
    assert (Hfirst : 2*m*Z.of_nat k<=2*m*Z.of_nat K).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    assert (Hinner : 0<=2*Z.of_nat r+m*Z.of_nat s /\
      2*Z.of_nat r+m*Z.of_nat s<=2*Z.of_nat R+m*Z.of_nat S).
    { pose proof (Z.mul_le_mono_nonneg_l (Z.of_nat s) (Z.of_nat S) m ltac:(lia) ltac:(lia)).
      nia. }
    assert (Hsecond : (2*Z.of_nat r+m*Z.of_nat s)*Z.of_nat l<=
      (2*Z.of_nat R+m*Z.of_nat S)*Z.of_nat L).
    { apply Z.mul_le_mono_nonneg; lia. }
    lia.
Qed.

End GridBounds.

Module LargeExclusion.
Import Determinants GridBase GridPolynomials GridMatrix GridArithmetic GridBounds.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Theorem exclusion : Modular.large_exclusion.
Proof.
  intros n u Hn Hu Hbad.
  assert (Hn0 : 0<n) by (pose proof (Modular.pow_pos 58 ltac:(lia)); lia).
  set (m:=Z.succ (Z.log2 n)).
  assert (Hm0 : 0<=m) by (pose proof (Z.log2_nonneg n); unfold m; lia).
  assert (Hbits : 2^(m-1)<=n<2^m).
  { pose proof (Z.log2_spec n Hn0). unfold m. replace (Z.succ (Z.log2 n)-1) with (Z.log2 n) by lia. exact H. }
  assert (Hm : 59<=m).
  { destruct (Z_le_gt_dec 59 m); [assumption|].
    pose proof (Z.pow_le_mono_r 2 m 58 ltac:(lia) ltac:(lia)). lia. }
  pose proof (Z.pow_pos_nonneg m 2 ltac:(lia) ltac:(lia)) as Hm2.
  pose proof (Z.pow_pos_nonneg m 3 ltac:(lia) ltac:(lia)) as Hm3.
  set (nn:=Z.to_nat n).
  set (K:=Z.to_nat (256*m^2)).
  set (L:=Z.to_nat (8*m)).
  set (R0:=Z.to_nat (32*m^2)).
  set (S:=Z.to_nat (64*m)).
  set (R:=(R0+L-1)%nat).
  assert (Hnn : Z.of_nat nn=n) by (unfold nn; rewrite Z2Nat.id by lia; reflexivity).
  assert (HK : Z.of_nat K=256*m^2) by (unfold K; rewrite Z2Nat.id by lia; reflexivity).
  assert (HL : Z.of_nat L=8*m) by (unfold L; rewrite Z2Nat.id by lia; reflexivity).
  assert (HR0 : Z.of_nat R0=32*m^2) by (unfold R0; rewrite Z2Nat.id by lia; reflexivity).
  assert (HS : Z.of_nat S=64*m) by (unfold S; rewrite Z2Nat.id by lia; reflexivity).
  assert (Hpos : (0<K /\ 0<L /\ 0<R0 /\ 0<S)%nat) by lia.
  assert (HR : Z.of_nat R=32*m^2+8*m-1).
  { unfold R. rewrite Nat2Z.inj_sub by lia. rewrite Nat2Z.inj_add,HR0,HL. reflexivity. }
  assert (HN : Z.of_nat (K*L)=2048*m^3) by (rewrite Nat2Z.inj_mul,HK,HL; ring).
  assert (HRS : (R0*S=K*L)%nat).
  { apply Nat2Z.inj. rewrite !Nat2Z.inj_mul,HR0,HS,HK,HL. ring. }
  pose proof (Parameters.dimension_bound m n Hm ltac:(lia)) as Hdim.
  assert (Hdegree : m<=m^2 /\ m^2<=m^3) by (clear - m Hm; nia).
  assert (HNsmall : 2048*m^3<n).
  { generalize Hdim. generalize (2048*m^3),Hm3. intros z Hz Hd.
    clear - Hd Hz. nia. }
  assert (Hsmall : Z.of_nat R<=n /\ Z.of_nat R0<=n /\ Z.of_nat S<=2^m /\ Z.of_nat (K*L)<=2^m).
  { rewrite HR,HR0,HS,HN. clear - HNsmall Hbits Hdegree Hm. lia. }
  assert (Hroot : ((K-1)*L<R0*S)%nat).
  { rewrite HRS. clear - Hpos. apply Nat.mul_lt_mono_pos_r; lia. }
  destruct (nonzero_grid K L nn u R0 S ltac:(clear - Hsmall Hnn; lia) Hroot ltac:(clear - Hu; lia))
    as [cs [Hlen [Hcols Hnz]]].
  set (T:=(2048*m^3)*(2048*m^3-1-2*(256*m^2))).
  set (B:=1664*m^3).
  set (U:=(2048*m^3)*(m+B)).
  assert (HUT : 0<=U<T).
  { pose proof (Parameters.exponent_gap m ltac:(lia)). unfold U,B,T.
    clear - H Hm Hm3. split; [apply Z.mul_nonneg_nonneg; lia|lia]. }
  assert (HT : 0<=T<=Z.of_nat nn).
  { rewrite Hnn. split; [clear - HUT; lia|]. unfold T. clear - Hdim Hm2 Hm3.
    assert (0<2048*m^3) by lia. nia. }
  assert (Hdiv : (2^T | det (map (entry nn u) (indices K 0 L)) cs)).
  { apply matrix_divide; [exact HT| |rewrite Hnn; exact Hbad].
    rewrite HN,HK. unfold T. lia. }
  assert (Hupper : Z.abs (det (map (entry nn u) (indices K 0 L)) cs)<=2^U).
  { unfold U. rewrite <-HN at 1.
    apply (matrix_bound K L nn u R S cs m B).
    - exact Hlen.
    - exact Hcols.
    - exact Hm0.
    - unfold B. clear - Hm3. lia.
    - clear - Hu Hbits. lia.
    - rewrite Hnn. tauto.
    - rewrite Hnn. clear - Hbits. lia.
    - tauto.
    - tauto.
    - rewrite HK,HL,HR,HS. unfold B. clear - Hm. nia. }
  exact (MatrixBounds.incompatible_bounds _ U T HUT Hnz Hdiv Hupper).
Qed.

End LargeExclusion.

Module Orbit.
Local Open Scope nat_scope.
Definition A i := 3^i*4-1.
Definition B i := 3^i*6+i+4.
Definition F i := 3^i*2+i+5.
Definition core := forall i,7<=i -> ~Nat.divide (2^(i+1)) (F i).

Inductive Step : nat -> nat -> Prop :=
| R1 i n : 3^i*2-i-2<=n<=3^i*6-i-6 -> n mod 2=i mod 2 ->
    Step n ((n+B i)/2)
| R2 i n : 3^i*2-i<=n<=3^i*6-i-10 -> n mod 2=(i+1) mod 2 ->
    Step n (A (i+1)).

Inductive Steps : nat -> nat -> Prop :=
| one x y : Step x y -> Steps x y
| cons x y z : Step x y -> Steps y z -> Steps x z.

Lemma pow3_ge i : i+1<=3^i.
Proof. induction i; cbn [Nat.pow]; lia. Qed.

Lemma pow_comparison i : 7<=i -> 2^i*(2*i+13)<3^i*2.
Proof.
  intro Hi. induction Hi; [cbn; lia|].
  rewrite !Nat.pow_succ_r by lia. pose proof (Nat.pow_nonzero 2 m ltac:(lia)). nia.
Qed.

Lemma factor_odd n : 0<n -> exists v q,n=2^v*q /\ q mod 2=1 /\ 0<q.
Proof.
  induction n using lt_wf_ind. intro Hn.
  destruct (Nat.Even_or_Odd n) as [[k Hk]|[k Hk]].
  - destruct (H k ltac:(lia) ltac:(lia)) as [v [q [He [Ho Hq]]]].
    exists (1+v),q. split; [change (n=2*2^v*q); nia|auto].
  - exists 0,n. split; [cbn; lia|]. split; [lia|exact Hn].
Qed.

Lemma odd_part i : core -> 7<=i -> exists v q,
  F i=2^v*q /\ q mod 2=1 /\ 2*i+15<=q.
Proof.
  intros HC Hi. destruct (factor_odd (F i) ltac:(unfold F; lia)) as [v [q [HF [Ho Hq]]]].
  assert (Hv : v<=i).
  { destruct (le_gt_dec v i); [assumption|]. exfalso. apply (HC i Hi).
    exists (2^(v-(i+1))*q). rewrite HF.
    replace v with ((i+1)+(v-(i+1))) at 1 by lia. rewrite Nat.pow_add_r. ring. }
  pose proof (Nat.pow_le_mono_r 2 v i ltac:(lia) Hv) as HP.
  pose proof (pow_comparison i Hi) as Hlarge.
  assert (Hqbound : 2*i+13<q).
  { destruct (le_gt_dec q (2*i+13)); [|lia].
    pose proof (Nat.mul_le_mono _ _ _ _ HP l). unfold F in HF. lia. }
  exists v,q. split; [exact HF|]. split; [exact Ho|]. lia.
Qed.

Lemma descend i v q : 7<=i -> q mod 2=1 -> 2*i+15<=q -> 2^v*q<=F i ->
  Steps (B i-2^v*q) (A (i+1)).
Proof.
  intros Hi Ho Hq. induction v as [|v IH]; intro HD.
  - apply one. apply (R2 i).
    + pose proof (pow3_ge i). cbn [Nat.pow] in *. unfold B,F in *. nia.
    + cbn [Nat.pow] in *. unfold B,F in *. lia.
  - rewrite Nat.pow_succ_r in HD |- * by lia.
    pose proof (Nat.pow_nonzero 2 v ltac:(lia)) as Hp.
    assert (Hn : B i-2*2^v*q+B i=2*(B i-2^v*q)).
    { unfold B,F in *. nia. }
    eapply cons.
    + apply (R1 i).
      * pose proof (pow3_ge i). unfold B,F in *. nia.
      * unfold B,F in *. nia.
    + rewrite Hn,Nat.mul_comm,Nat.div_mul by lia. apply IH. nia.
Qed.

Theorem layer i : core -> 7<=i -> Steps (A i) (A (i+1)).
Proof.
  intros HC Hi. destruct (odd_part i HC Hi) as [v [q [HF [Ho Hq]]]].
  pose proof (descend i v q Hi Ho Hq ltac:(lia)) as H.
  rewrite <- HF in H. replace (B i-F i) with (A i) in H by (unfold A,B,F; lia). exact H.
Qed.

End Orbit.

Module ArithmeticBridge.
Local Open Scope Z_scope.
Local Ltac Zify.zify_pre_hook ::= idtac.

Lemma core : Modular.large_exclusion -> Orbit.core.
Proof.
  intros Hlarge i Hi [q Hq].
  apply (Modular.core_of_large Hlarge (Z.of_nat i) ltac:(lia)).
  exists (Z.of_nat q). unfold Orbit.F in Hq.
  apply (f_equal Z.of_nat) in Hq.
  rewrite !Nat2Z.inj_mul,!Nat2Z.inj_pow,!Nat2Z.inj_add in Hq.
  unfold Modular.F. nia.
Qed.

End ArithmeticBridge.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* <[1]^^(1+a*2) <{{C}} [0;1]^^b *> [1]^^(c*2) *> [0;1] *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (2+c) -->*
  S1 a (3+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*2+c) -->*
  S1 a (n*3+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma LOv1 b c:
  S1 0 b (3+c) -->*
  S1 (2+b) 2 c.
Proof.
  es.
Qed.

Definition S2 a b :=
  0inf <* <[1]^^(1+a*2) <{{C}} [0;1]^^b *> [1] *> 0inf.

Lemma Inc2 a b:
  S2 (1+a) b -->*
  S2 a (3+b).
Proof.
  es.
Qed.

Lemma Incs2 a b:
  S2 a b -->*
  S2 0 (a*3+b).
Proof.
  gen b.
  ind a Inc2.
Qed.

Definition S3 a b :=
  0inf <* <[1]^^(1+a*2) <{{C}} [0;1]^^b *> 0inf.

Lemma Ov2 b:
  S2 0 b -->*
  S3 (2+b) 1.
Proof.
  es.
Qed.

Lemma Inc3 a b:
  S3 (1+a) b -->*
  S3 a (2+b).
Proof.
  es.
Qed.

Lemma Incs3 a b:
  S3 a b -->*
  S3 0 (a*2+b).
Proof.
  gen b.
  ind a Inc3.
Qed.

Lemma Ov3 b:
  S3 0 b -->+
  S1 0 2 (2+b).
Proof.
  es.
Qed.

Lemma IncsOv3 a b:
  S3 a b -->+
  S1 0 2 (2+a*2+b).
Proof.
  follow Incs3.
  applys_eq Ov3; flia.
Qed.

Lemma IncsOv2 a b:
  S2 a b -->*
  S1 0 2 (7+a*6+b*2).
Proof.
  follow Incs2.
  follow Ov2.
  follow100 IncsOv3.
  finish.
Qed.

Lemma ROv1_1 a b:
  S1 (2+a) b 1 -->+
  S1 0 2 (19+a*6+b*2).
Proof.
  mid10 (S2 a (6+b)).
  1: es.
  follow IncsOv2.
  finish.
Qed.

Lemma ROv1_1_0 b:
  halts tm (S1 0 b 1).
Proof.
  esx.
Qed.

Lemma ROv1_0 a b:
  S1 a b 0 -->+
  S1 0 2 (3+a*2+b).
Proof.
  mid01 (S3 a (1+b)).
  1: es.
  applys_eq (IncsOv3 a (1+b)); flia.
Qed.

Definition P n1 n2 :=
  forall c,
  S1 0 2 (n1+c) -->*
  S1 n2 2 c.

Lemma P_O:
  P 0 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S n1 n2:
  P n1 n2 ->
  P (n1+n2*2+3) (4+n2*3).
Proof.
  unfold P; intros HP c.
  follow (HP (n2*2+(3+(c)))).
  follow (Incs1 n2 0 2 (3+(c))).
  follow LOv1.
  finish.
Qed.

Lemma pow3_ge i:
  3^i>=i+1.
Proof.
  induction i; cbn[Nat.pow]; lia.
Qed.

Lemma P_n i:
  P (3^i*2-i-2) (3^i*2-2).
Proof.
  induction i.
  1: apply P_O.
  apply P_S in IHi.
  cbn[Nat.pow].
  pose proof (pow3_ge i).
  applys_eq IHi; flia.
Qed.

Definition S' n := S1 0 2 n.

Lemma BigStep1 n1 n2 c:
  P n1 (c+(2+n2)) ->
  S' (n1+c*2+1) -->+
  S' (23+n2*6+c*6).
Proof.
  unfold S',P; intros HP.
  follow (HP (c*2+1)).
  follow Incs1.
  applys_eq ROv1_1; flia.
Qed.

Lemma BigStep0 n1 n2 c:
  P n1 (c+n2) ->
  S' (n1+c*2+0) -->+
  S' (5+n2*2+c*3).
Proof.
  unfold S',P; intros HP.
  follow (HP (c*2+0)).
  follow Incs1.
  applys_eq ROv1_0; flia.
Qed.

Lemma init:
  c0 -->*
  S' 18.
Proof.
  unfold S',S1.
  esx.
Qed.

Close Scope sym.

Lemma BigStep0' i n:
  3^i*2-i-2 <= n <= 3^i*6-i-6 ->
  n mod 2 = i mod 2 ->
  S' n -->+
  S' ((n+(3^i*6+i+4))/2).
Proof.
  intros.
  pose proof (pow3_ge i).
  pose proof (P_n i) as HP.
  remember ((n-(3^i*2-i-2))/2) as c.
  pose proof (BigStep0 (3^i*2-i-2) (3^i*2-2-c) c) as I1.
  applys_eq I1; flia. applys_eq HP; flia.
Qed.

Lemma BigStep1' i n:
  3^i*2-i <= n <= 3^i*6-i-10 ->
  n mod 2 = (i+1) mod 2 ->
  S' n -->+
  S' (3^i*12-1).
Proof.
  intros.
  pose proof (pow3_ge i).
  pose proof (P_n i) as HP.
  remember ((n-(3^i*2-i-2))/2) as c.
  pose proof (BigStep1 (3^i*2-i-2) (3^i*2-4-c) c) as I1.
  applys_eq I1; flia. applys_eq HP; flia.
Qed.

Lemma step_spec x y : Orbit.Step x y -> S' x -->+ S' y.
Proof.
  intro H. destruct H as [i n Hn Hp|i n Hn Hp].
  - unfold Orbit.B. apply BigStep0'; assumption.
  - unfold Orbit.A. rewrite Nat.pow_add_r. change (3^1) with 3.
    applys_eq (BigStep1' i n Hn Hp); flia.
Qed.

Lemma steps_spec x y : Orbit.Steps x y -> S' x -->+ S' y.
Proof.
  intro H. induction H.
  - apply step_spec; assumption.
  - eapply progress_trans; [apply step_spec; eassumption|exact IHSteps].
Qed.

Lemma init7 : c0 -->* S' (Orbit.A 7).
Proof.
  follow init.
  follow100 (BigStep0' 2 18 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep1' 2 39 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep0' 3 107 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep1' 3 138 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep1' 4 323 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep0' 5 971 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep0' 5 1219 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep0' 5 1343 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep0' 5 1405 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep1' 5 1436 ltac:(cbn; lia) ltac:(reflexivity)).
  follow100 (BigStep1' 6 2915 ltac:(cbn; lia) ltac:(reflexivity)).
  finish.
Qed.

Lemma nonhalt_of_core : Orbit.core -> ~halts tm c0.
Proof.
  intro Hcore. eapply multistep_nonhalt; [apply init7|].
  apply (progress_nonhalt_simple tm nat (fun k => S' (Orbit.A (7+k))) 0).
  intro k. exists (k+1). replace (7+(k+1)) with ((7+k)+1) by lia.
  apply steps_spec,Orbit.layer; [exact Hcore|lia].
Qed.

Lemma nonhalt_of_large_exclusion : Modular.large_exclusion -> ~halts tm c0.
Proof. intro H. apply nonhalt_of_core,ArithmeticBridge.core,H. Qed.

Theorem nonhalt: ~halts tm c0.
Proof. apply nonhalt_of_large_exclusion,LargeExclusion.exclusion. Qed.

End TM1.

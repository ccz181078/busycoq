From BusyCoq Require Import PR58Part1.


Module RouteMarkerBound.
(* A marked even-position digit bounds a conversion route.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import OddRoute.
Import List PeanoNat Lia.
Import ListNotations OddRoute.OddRoute.
Open Scope nat.

Module RouteMarkerBound.
Lemma prefix_true_index u tail i :
 nth i (repeat false u++true::tail) false=true -> u<=i.
Proof.
 intro H. destruct (Nat.le_gt_cases u i); [assumption|].
 rewrite app_nth1 in H by (rewrite repeat_length; lia).
 rewrite nth_repeat in H. discriminate.
Qed.

Lemma prefix_tail_nth u tail i : u<i ->
 nth i (repeat false u++true::tail) false=true ->
 nth (i-u-1) tail false=true.
Proof.
 intros Hi H. rewrite app_nth2 in H by (rewrite repeat_length; lia).
 rewrite repeat_length in H.
 replace (i-u) with (S (i-u-1)) in H by lia.
 cbn[nth] in H. exact H.
Qed.

Lemma route_known_even L k bs L' k' rest :
 route L k bs L' k' rest ->
 forall i, nth i bs false=true -> i mod 2=0 ->
 length bs<=i+1+length rest.
Proof.

 intro Hroute. induction Hroute; intros i Hnth Hpar.
 - pose proof (prefix_true_index (v*2) tail i Hnth).
   rewrite length_app,repeat_length. cbn[length]. lia.
 - pose proof (prefix_true_index (v*2+1) tail i Hnth) as Hlow.
   assert (Hstrict:v*2+1<i).
   { destruct (Nat.eq_dec i (v*2+1)) as [E|E]; [|lia].
     subst i. rewrite Nat.add_comm,Nat.mod_add in Hpar by lia. discriminate. }

   pose proof (prefix_tail_nth (v*2+1) tail i Hstrict Hnth) as Htail.
   assert (Hpar':(i-(v*2+1)-1) mod 2=0).
   { replace i with ((i-(v*2+1)-1)+(v+1)*2) in Hpar by lia.
     rewrite Nat.mod_add in Hpar by lia. exact Hpar. }
   pose proof (IHHroute (i-(v*2+1)-1) Htail Hpar') as Hbound.
   rewrite length_app,repeat_length. cbn[length]. lia.
Qed.

Lemma route_known_even_bound L k bs L' k' rest j i :
 route L k bs L' k' rest ->
 length bs=2*j+1+length rest ->
 nth i bs false=true -> i mod 2=0 -> 2*j<=i.
Proof.
 intros Hr Hlen Hnth Hpar.
 pose proof (route_known_even _ _ _ _ _ _ Hr i Hnth Hpar). lia.
Qed.

End RouteMarkerBound.
End RouteMarkerBound.

Module GuardedRoute.
(* The strong digit guard retains a bounded correction in the conversion fuel.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import StrongInvariant WallInvariant MarkedTrace OddRoute OddFuel OddImage.
Import OdDeficit RouteMarkerBound.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module GuardedRoute.

Definition good_deficit j delta :=
 (1<=j /\ delta=(2^(2*j+2)-3)*2^(5*j)) \/
 (exists u c, 2<=j /\ u+1<=2*j /\ c<2^(5*j-5) /\
  delta=(2^(u+2)-3)*2^(5*j)+c).

Definition source_data n bs :=
 exists L k rest j delta,
 MarkedTrace.MarkedTrace.wall_route n bs L k rest /\
 length bs=2*j+1+length rest /\ L=n+5*j+1 /\
 k+1+delta=2^L /\ good_deficit j delta.

Lemma package n bs L k rest j delta :
 MarkedTrace.MarkedTrace.wall_route n bs L k rest -> L=n+5*j+1 ->
 k+1+delta=2^L -> good_deficit j delta -> source_data n bs.
Proof.

 intros Hr HL HD HG.
 destruct (MarkedTrace.MarkedTrace.route_dimensions _ _ _ _ _ Hr) as [j0 [Hlen HL0]].
 assert (j0=j) by lia. subst j0.
 exists L,k,rest,j,delta. repeat split; assumption.
Qed.

Lemma direct_data n j tail :
 1<=j -> length (repeat false (j*2)++true::tail)+1<=n ->
 source_data n (repeat false (j*2)++true::tail).
Proof.

 intros Hj Hlen.
 eapply package with (L:=n+1+j*5)
  (k:=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (j*2)) (j*5)) (rest:=tail) (j:=j)
  (delta:=(2^(2*j+2)-3)*2^(5*j)).
 - constructor.
 - lia.

 - replace (2*j) with (j*2) by lia. replace (5*j) with (j*5) by lia.
   apply (OdDeficit.OdDeficit.initial_even_deficit n j tail); exact Hlen.
 - left. split; [exact Hj|reflexivity].
Qed.

Lemma routed_data n v tail L k rest r :
 OddRoute.OddRoute.route (n+1+(v*5+3)) (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3))
  tail L k rest ->
 length (repeat false (v*2+1)++true::tail)+1<=n ->
 length tail=2*r+1+length rest ->
 2<=v+1+r -> 7*r+3<=5*(v+1+r)-5 ->
 source_data n (repeat false (v*2+1)++true::tail).
Proof.

 intros Hr Hn Hlen Hj Hsmall.
 destruct (OdDeficit.OdDeficit.initial_odd_route_deficit _ _ _ _ _ _ Hr Hn)
  as [r0 [c [Hlen0 [HL [Hc HE]]]]].
 assert (r0=r) by lia. subst r0.
 eapply package with (L:=L) (k:=k) (rest:=rest) (j:=v+1+r)
  (delta:=(2^(v*2+3)-3)*2^(5*(v+1+r))+c).

 - constructor. exact Hr.
 - exact HL.
 - lia.
 - right. exists (v*2+1),c. repeat split; try lia.
   + eapply Nat.lt_le_trans; [exact (proj2 Hc)|]. apply Nat.pow_le_mono_r; lia.
   + replace (v*2+1+2) with (v*2+3) by lia. reflexivity.
Qed.

Lemma adjacent_data n v tail :
 1<=v -> length (repeat false (v*2+1)++true::true::tail)+1<=n ->
 source_data n (repeat false (v*2+1)++true::true::tail).
Proof.

 intros Hv Hn.
 set (L0:=n+1+(v*5+3)).
 set (k0:=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)).
 assert (Hk:1<=k0).
 { unfold k0,OddFuel.OddFuel.grown.
   assert (8<=2^(v*5+3)) by (change (2^3<=2^(v*5+3)); apply Nat.pow_le_mono_r; lia).
   nia. }

 assert (Hr:OddRoute.OddRoute.route L0 k0 (true::tail) (L0+1+1) (OddFuel.OddFuel.grown (k0-1) 1) tail).
 { replace k0 with ((k0-1)+(2^(0*2+1)-1)) at 1 by (cbn[Nat.pow]; lia).
   change (OddRoute.OddRoute.route L0 ((k0-1)+(2^(0*2+1)-1))
     (repeat false (0*2)++true::tail) (L0+1+(0*5+1))
     (OddFuel.OddFuel.grown (k0-1) (0*5+1)) tail).
   constructor. }
 apply (routed_data n v (true::tail) (L0+1+1) (OddFuel.OddFuel.grown (k0-1) 1) tail 0).

 - exact Hr.
 - exact Hn.
 - cbn[length]. lia.
 - lia.
 - lia.
Qed.

Lemma odd_index_even_tail a i :
 10*a<i -> i mod 2=1 -> (i-10*a-1) mod 2=0.
Proof.

 intros Hi Hp. destruct (mod2 (i-10*a-1)) as [t He|t He].
 - rewrite He,Nat.mod_mul by lia. reflexivity.
 - assert (Ei:i=(5*a+t+1)*2) by lia.
   rewrite Ei,Nat.mod_mul in Hp by lia. discriminate.
Qed.

Lemma close_data n a tail i :
 0<a -> length (repeat false (10*a+1)++true::tail)+1<=n ->
 nth i (repeat false (10*a)++true::tail) false=true ->
 i mod 2=1 -> i<=14*a+3 ->
 source_data n (repeat false (10*a+1)++true::tail).
Proof.

 intros Ha Hn Hbit Hp Hbound.
 assert (Hi:10*a<i).
 { pose proof (RouteMarkerBound.RouteMarkerBound.prefix_true_index (10*a) tail i Hbit) as Hlo.
   destruct (Nat.eq_dec i (10*a)) as [E|E]; [|lia].
   rewrite E in Hp. replace (10*a) with ((5*a)*2) in Hp by lia.
   rewrite Nat.mod_mul in Hp by lia. discriminate. }

 pose proof (RouteMarkerBound.RouteMarkerBound.prefix_tail_nth (10*a) tail i Hi Hbit) as Htail.
 pose proof (odd_index_even_tail a i Hi Hp) as Heven.
 assert (Hmark:WallInvariant.WallInvariant.marked 0 tail).
 { destruct (StrongInvariant.StrongInvariant.nth_true_split tail (i-10*a-1) Htail) as [pre [post [E Hlen]]].
   exists pre,post. split; [exact E|rewrite Hlen;exact Heven]. }
 set (L0:=n+1+((5*a)*5+3)).
 set (k0:=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n ((5*a)*2+1)) ((5*a)*5+3)).

 assert (Hmargin:2^(length tail+4)-1<=k0).
 { unfold k0. apply MarkedTrace.MarkedTrace.initial_margin4.
   - rewrite length_app,repeat_length in Hn. cbn[length] in Hn. lia.
   - lia. }
 assert (Hbasic:2^length tail-1<=k0).
 { assert (2^length tail<=2^(length tail+4)) by (apply Nat.pow_le_mono_r; lia). lia. }
 destruct (OddRoute.OddRoute.marked_route L0 k0 tail Hmark Hbasic) as [L [k [rest [Hr Hlower]]]].

 destruct (OddRoute.OddRoute.route_dimensions _ _ _ _ _ _ Hr) as [r [Hlen HL]].
 pose proof (RouteMarkerBound.RouteMarkerBound.route_known_even_bound _ _ _ _ _ _ r (i-10*a-1) Hr Hlen Htail Heven) as Hrbound.
 assert (Hrsmall:r<=2*a+1) by lia.
 replace (10*a+1) with ((5*a)*2+1) by lia.
 apply (routed_data n (5*a) tail L k rest r).
 - exact Hr.
 - replace ((5*a)*2+1) with (10*a+1) by lia. exact Hn.

 - exact Hlen.
 - lia.
 - lia.
Qed.

Lemma prepend_repeat u tail : false::(repeat false u++tail)=repeat false (u+1)++tail.
Proof. replace (u+1) with (S u) by lia. reflexivity. Qed.

Lemma guard_source n bs :
 length bs+2<=n -> StrongInvariant.StrongInvariant.digit_guard bs -> source_data n (false::bs).
Proof.

 intros Hn HG.
 destruct HG as [[u [tail E]]|[[u [tail [Hu E]]]|[a [tail [i [Ha [E [Hbit [Hp Hib]]]]]]]]].
 - subst bs. rewrite prepend_repeat.
   replace (u*2+1+1) with ((u+1)*2) by lia.
   apply direct_data; [lia|].
   rewrite length_app,repeat_length in Hn |-*. cbn[length] in *. lia.

 - subst bs. rewrite prepend_repeat.
   destruct (mod2 u) as [v He|v He]; subst u.
   + apply adjacent_data; [lia|].
     rewrite length_app,repeat_length in Hn |-*. cbn[length] in *. lia.
   + replace (1+v*2+1) with ((v+1)*2) by lia.
     apply direct_data; [lia|].
     rewrite length_app,repeat_length in Hn |-*. cbn[length] in *. lia.

 - subst bs. rewrite prepend_repeat.
   apply (close_data n a tail i); try assumption.
   rewrite length_app,repeat_length in Hn |-*. cbn[length] in *. lia.
Qed.

End GuardedRoute.
End GuardedRoute.

Module CounterBits.
(* Binary digits and the parity marker in a wall configuration.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import CounterRules CounterFinish WallInvariant.
Import String List PeanoNat NArith Lia.
Import CounterRules.CounterRules CounterFinish.CounterFinish WallInvariant.WallInvariant.
Open Scope nat.

Module CounterBits.
Fixpoint value (bs:list bool) : nat :=
  match bs with [] => 0 | b::bs => (if b then 1 else 0) + 2*value bs end.

Lemma digits_value n v : v < 2^n -> value (digits n v) = v.
Proof.
  gen v. induction n; intros v Hv.
  - cbn in Hv. assert (v=0) by lia. subst. reflexivity.
  - destruct (mod2 v); subst.
    + rewrite digits_even. cbn [value]. rewrite IHn by (cbn in Hv; lia). lia.
    + rewrite Nat.add_comm. rewrite digits_odd. cbn [value].
      rewrite IHn by (cbn in Hv; lia). lia.
Qed.

Lemma value_nonzero bs : value bs <> 0 -> In true bs.
Proof.
  induction bs as [|b bs IH]; cbn; intros H.
  - contradiction.
  - destruct b; [left; reflexivity|]. right. apply IH. lia.
Qed.

Lemma digits_split n i v :
  i <= n -> digits n v = digits i v ++ digits (n-i) (v/2^i).
Proof.
  gen n v. induction i; intros n v Hi.
  - cbn [digits Nat.pow]. rewrite Nat.sub_0_r, Nat.div_1_r. reflexivity.
  - destruct n; [lia|]. cbn [digits Nat.sub Nat.pow].
    rewrite IHi by lia.
    rewrite Nat.div_div by (pose proof (Nat.pow_nonzero 2 i ltac:(lia)); lia).
    reflexivity.
Qed.

Lemma digits_marked n v i q :
  i < n -> v/2^i = q*2+1 -> marked (i mod 2) (digits n v).
Proof.
  intros Hin Hq.
  rewrite (digits_split n i v) by lia.
  rewrite Hq.
  replace (n-i) with (S (n-i-1)) by lia.
  rewrite digits_odd.
  exists (digits i v), (digits (n-i-1) q).
  split; [reflexivity|]. rewrite digits_length. reflexivity.
Qed.

Lemma marked_shift_odd n q i :
  i < n -> i mod 2 = 1 -> marked 1 (digits n ((q*2+1)*2^i)).
Proof.
  intros Hin Hi.
  pose proof (digits_marked n ((q*2+1)*2^i) i q Hin) as Hm.
  rewrite Hi in Hm. apply Hm.
  rewrite Nat.div_mul by (apply Nat.pow_nonzero; lia). reflexivity.
Qed.

Lemma marked_remainder n v i q r :
  i<n -> r<2^i -> v=(q*2+1)*2^i+r ->
  marked (i mod 2) (digits n v).
Proof.
  intros Hi Hr Hv. apply (digits_marked n v i q Hi).
  rewrite Hv, Nat.add_comm, Nat.div_add by (apply Nat.pow_nonzero; lia).
  rewrite Nat.div_small by exact Hr. lia.
Qed.

Open Scope sym.

Lemma shifted_normal_word bs :
  [0;0;0;0] ++ normal bs = shifted bs ++ [0;0;0;0].
Proof.
  induction bs as [|b bs IH].
  - reflexivity.
  - destruct b; cbn [normal shifted app]; rewrite <-IH; reflexivity.
Qed.

Lemma shifted_normal bs :
  [0;0;0;0] *> normal bs *> 0inf = shifted bs *> 0inf.
Proof.
  rewrite <-Str_app_assoc, shifted_normal_word, Str_app_assoc.
  st. reflexivity.
Qed.

Lemma numeric_even n v :
  (0 < v)%nat -> (v*2 < 2^n)%nat ->
  invariant ((0inf <* <[1;1]) <* [0] {{A}}>
             ([1] *> [1;1]^^n *> RC (v*2))).
Proof.

  intros Hv Hbound.
  rewrite <- (digits_normal n (v*2) Hbound).
  replace ([1] *> [1;1]^^n *> normal (digits n (v*2)) *> 0inf)
    with ([1;1]^^n *> [1] *> normal (digits n (v*2)) *> 0inf)
    by (simpl_rotate; reflexivity).
  replace ([1;1]^^n *> [1] *> normal (digits n (v*2)) *> 0inf)
    with (([1;1]^^n ++ [1] ++ normal (digits n (v*2))) *> 0inf)
    by (repeat rewrite Str_app_assoc; reflexivity).
  change (invariant (O n (digits n (v*2)))).

  apply InvO.
  - rewrite digits_length. lia.
  - destruct n; [cbn in Hbound; lia|].
    rewrite digits_even. eexists. reflexivity.
  - apply value_nonzero. rewrite digits_value by exact Hbound. lia.
Qed.

Lemma numeric_odd n v :
  (v < 2^n)%nat -> marked 1 (digits n v) ->
  invariant ((0inf <* <[1;1]) <* [0] {{A}}>
             ([1] *> [1;1]^^(n+1) *> RC (v*2+1))).
Proof.

  intros Hv Hmark.
  unfold RC. rewrite BinInc_mul2add1.
  change (invariant ((0inf <* <[1;1]) <* [0] {{A}}>
    ([1] *> [1;1]^^(n+1) *> [1;0;0;0;0] *> RC v))).
  rewrite <- (digits_normal n v Hv).
  replace ([1] *> [1;1]^^(n+1) *> [1;0;0;0;0] *> normal (digits n v) *> 0inf)
    with ([1;1]^^(n+2) *> [0;0;0;0] *> normal (digits n v) *> 0inf)
    by (replace (n+2)%nat with ((n+1)+1)%nat by lia; st; simpl_rotate; reflexivity).
  rewrite shifted_normal.

  replace ([1;1]^^(n+2) *> shifted (digits n v) *> 0inf)
    with (([1;1]^^(n+2) ++ shifted (digits n v)) *> 0inf)
    by (rewrite Str_app_assoc; reflexivity).
  change (invariant (E (n+2) (digits n v))).
  apply InvE.
  - rewrite digits_length. lia.
  - exact Hmark.
Qed.

Lemma numeric_even_value n t :
  (0<t)%nat -> (t<2^n)%nat -> (t mod 2=0)%nat ->
  invariant ((0inf <* <[1;1]) <* [0] {{A}}>
             ([1] *> [1;1]^^n *> RC t)).
Proof.
  intros Ht Hb He.
  destruct (mod2 t); subst.
  - apply numeric_even; lia.
  - rewrite Nat.mod_add in He by lia. discriminate.
Qed.

Lemma counter_finish_even n k r :
  (k<2^n)%nat -> (0<r+k+1)%nat -> (r+k+1<2^n)%nat ->
  ((r+k+1) mod 2=0)%nat ->
  exists c, (LC n k <* [0;1] {{A}}> RC r) -[mtm]->+ c /\ invariant c.
Proof.
  intros Hk Hpos Hb He. eexists. split.
  - apply counter_finish; exact Hk.
  - apply numeric_even_value; assumption.
Qed.

End CounterBits.
End CounterBits.

Module MarkerArithmetic.
(* Preserving a low binary digit through a distant carry.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits CounterFinish WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits CounterFinish.CounterFinish WallInvariant.WallInvariant.
Open Scope nat.

Module MarkerArithmetic.
Lemma value_bound bs : value bs<2^(length bs).
Proof.
 induction bs as [|b bs IH]; cbn [value length Nat.pow]; [lia|].
 destruct b; nia.
Qed.

Lemma digits_value_inverse bs : digits (length bs) (value bs)=bs.
Proof.
 induction bs as [|b bs IH]; [reflexivity|].
 destruct b; cbn [length value].
 - replace (1+2*value bs) with (value bs*2+1) by lia.
   rewrite digits_odd, IH. reflexivity.
 - replace (0+2*value bs) with (value bs*2) by lia.
   rewrite digits_even, IH. reflexivity.
Qed.

Lemma marked_value_remainder bs i q low :
 i<length bs -> low<2^i -> value bs=(q*2+1)*2^i+low ->
 marked (i mod 2) bs.
Proof.
 intros Hi Hlow Heq.
 rewrite <-(digits_value_inverse bs).
 apply (marked_remainder (length bs) (value bs) i q low); assumption.
Qed.

Lemma marked_residue bs i r :
 i<length bs -> r<2^i -> value bs mod 2^(i+1)=2^i+r ->
 marked (i mod 2) bs.
Proof.
 intros Hi Hr He.
 pose proof (Nat.div_mod (value bs) (2^(i+1)) (Nat.pow_nonzero 2 (i+1) ltac:(lia))) as Hdiv.
 apply (marked_value_remainder bs i (value bs/2^(i+1)) r); [exact Hi|exact Hr|].
 rewrite He in Hdiv. rewrite Nat.pow_add_r in *.
 cbn [Nat.pow] in *. nia.
Qed.

Lemma power_multiple low high : low<=high ->
 2^high=2^(high-low)*2^low.
Proof.
 intro H. rewrite <-Nat.pow_add_r. f_equal. lia.
Qed.

Lemma carry_width bs j big v :
 0<big -> value bs+2^(length bs)=big*2^j+v -> j<=length bs.
Proof.
 intros Hbig Heq. pose proof (value_bound bs) as Hv.
 destruct (Nat.le_gt_cases j (length bs)); [assumption|].
 assert (Hp:2^(length bs+1)<=2^j) by (apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r in Hp. cbn [Nat.pow] in Hp.
 pose proof (Nat.pow_nonzero 2 j ltac:(lia)). nia.
Qed.

Lemma low_marker_preserved bs v i q r j big :
 0<big -> i<j -> r<2^i -> v=(q*2+1)*2^i+r ->
 value bs+2^(length bs)=big*2^j+v -> marked (i mod 2) bs.
Proof.
 intros Hbig Hij Hr Hv Heq.
 pose proof (carry_width bs j big v Hbig Heq) as Hlen.
 apply (marked_residue bs i r); [lia|exact Hr|].

 rewrite (power_multiple (i+1) (length bs)) in Heq by lia.
 rewrite (power_multiple (i+1) j) in Heq by lia.
 replace (big*(2^(j-(i+1))*2^(i+1))+v) with
   (v+(big*2^(j-(i+1)))*2^(i+1)) in Heq by nia.
 apply (f_equal (fun n=>n mod 2^(i+1))) in Heq.
 rewrite !Nat.mod_add in Heq by (apply Nat.pow_nonzero; lia).
 rewrite Heq, Hv.

 replace ((q*2+1)*2^i+r) with ((2^i+r)+q*2^(i+1)) by
   (rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
 rewrite Nat.mod_add by (apply Nat.pow_nonzero; lia).
 apply Nat.mod_small. rewrite Nat.pow_add_r. cbn [Nat.pow]. lia.
Qed.

End MarkerArithmetic.
End MarkerArithmetic.

Module GapMarker.
(* A small subtraction preserves an odd-position binary marker.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits MarkerArithmetic WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits MarkerArithmetic.MarkerArithmetic WallInvariant.WallInvariant.
Open Scope nat.

Module GapMarker.
Lemma marked_residue_auto bs i r :
 r<2^i -> value bs mod 2^(i+1)=2^i+r -> marked (i mod 2) bs.
Proof.
 intros Hr He. apply (marked_residue bs i r); [|exact Hr|exact He].
 destruct (Nat.lt_ge_cases i (length bs)); [assumption|].
 pose proof (value_bound bs) as Hv.
 assert (Hp:2^length bs<=2^i) by (apply Nat.pow_le_mono_r; lia).
 assert (Hsmall:value bs<2^(i+1)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow]. lia. }
 rewrite Nat.mod_small in He by exact Hsmall. lia.
Qed.

Lemma complement_residue v d c :
 0<c -> c<d -> (v+c) mod d=0 -> v mod d=d-c.
Proof.
 intros Hc Hcd Hsum.
 rewrite Nat.add_mod, (Nat.mod_small c d Hcd) in Hsum by lia.
 pose proof (Nat.mod_upper_bound v d ltac:(lia)) as Hv.
 pose proof (Nat.div_mod (v mod d+c) d ltac:(lia)) as Hdiv.
 rewrite Hsum in Hdiv.
 assert ((v mod d+c)/d=1) by nia. nia.
Qed.

Lemma subtraction_marker_at bs A J D c i :
 J<=A -> i<J -> J-2<=i -> i mod 2=1 ->
 0<c -> c<2^(J-2) ->
 value bs+c+D*2^J=2^A -> marked 1 bs.
Proof.

 intros HJA Hi Hlo Hpar Hc Hsmall Heq.
 assert (Hci:c<2^i).
 { assert (2^(J-2)<=2^i) by (apply Nat.pow_le_mono_r; lia). lia. }
 assert (Hcd:c<2^(i+1)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow]. lia. }

 assert (Hsum:(value bs+c) mod 2^(i+1)=0).
 { rewrite (power_multiple (i+1) A), (power_multiple (i+1) J) in Heq by lia.
   replace (D*(2^(J-(i+1))*2^(i+1))) with
     ((D*2^(J-(i+1)))*2^(i+1)) in Heq by nia.
   apply (f_equal (fun n=>n mod 2^(i+1))) in Heq.
   rewrite Nat.mod_add,Nat.mod_mul in Heq by (apply Nat.pow_nonzero; lia).
   exact Heq. }
 pose proof (complement_residue (value bs) (2^(i+1)) c Hc Hcd Hsum) as Hmod.
 pose proof (marked_residue_auto bs i (2^i-c)) as Hmark.
 rewrite Hpar in Hmark. apply Hmark; [lia|].
 rewrite Hmod, Nat.pow_add_r. cbn[Nat.pow]. lia.
Qed.

Lemma small_subtraction_marker bs A B J c :
 3<=J -> 3<=B -> 0<c -> c<2^(J-2) ->
 value bs+c+(2^B-3)*2^J=2^A -> marked 1 bs.
Proof.

 intros HJ HB Hc Hsmall Heq.
 assert (HpowB:8<=2^B).
 { change (2^3<=2^B). apply Nat.pow_le_mono_r; lia. }
 assert (HJA:J<=A).
 { destruct (Nat.le_gt_cases J A); [assumption|].
   assert (2^A<2^J) by (apply Nat.pow_lt_mono_r; lia).
   pose proof (Nat.pow_nonzero 2 J ltac:(lia)). nia. }
 destruct (mod2 J) as [a E|a E]; subst J.
 - apply (subtraction_marker_at bs A (a*2) (2^B-3) c (a*2-1)); try assumption; try lia.
 - apply (subtraction_marker_at bs A (1+a*2) (2^B-3) c (1+a*2-2)); try assumption; try lia.
Qed.

End GapMarker.
End GapMarker.

Module MultiGapMarker.
(* Marker digits below several distant subtraction terms.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits MarkerArithmetic GapMarker WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits MarkerArithmetic.MarkerArithmetic GapMarker.GapMarker WallInvariant.WallInvariant.
Open Scope nat.

Module MultiGapMarker.
Lemma positive_subtraction_marker bs A J D c :
 3<=J -> 0<D -> 0<c -> c<2^(J-2) ->
 value bs+c+D*2^J=2^A -> marked 1 bs.
Proof.

 intros HJ HD Hc Hsmall Heq.
 assert (HJA:J<=A).
 { destruct (Nat.le_gt_cases J A); [assumption|].
   assert (2^A<2^J) by (apply Nat.pow_lt_mono_r; lia).
   pose proof (Nat.pow_nonzero 2 J ltac:(lia)). nia. }
 destruct (mod2 J) as [a E|a E]; subst J.
 - apply (subtraction_marker_at bs A (a*2) D c (a*2-1)); try assumption; lia.
 - apply (subtraction_marker_at bs A (1+a*2) D c (1+a*2-2)); try assumption; lia.
Qed.

Lemma two_gap_marker bs A J K D E c :
 0<D -> 0<E -> 3<=Nat.min J K ->
 0<c -> c<2^(Nat.min J K-2) ->
 value bs+c+D*2^J+E*2^K=2^A -> marked 1 bs.
Proof.

 intros HD HE Hmin Hc Hsmall Heq.
 set (m:=Nat.min J K) in *.
 assert (HmJ:m<=J) by (unfold m; apply Nat.le_min_l).
 assert (HmK:m<=K) by (unfold m; apply Nat.le_min_r).
 apply (positive_subtraction_marker bs A m
   (D*2^(J-m)+E*2^(K-m)) c); try assumption.
 - pose proof (Nat.pow_nonzero 2 (J-m) ltac:(lia)).
   pose proof (Nat.pow_nonzero 2 (K-m) ltac:(lia)). nia.
 - rewrite (power_multiple m J HmJ), (power_multiple m K HmK) in Heq.
   nia.
Qed.

End MultiGapMarker.
End MultiGapMarker.

Module MagnitudeMarker.
(* A sufficiently large binary word contains an odd-position marker.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import CounterBits CounterFinish MarkerArithmetic WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits CounterFinish.CounterFinish MarkerArithmetic.MarkerArithmetic WallInvariant.WallInvariant.
Open Scope nat.

Module MagnitudeMarker.
Lemma value_app bs cs : value (bs++cs)=value bs+2^length bs*value cs.
Proof.
 induction bs as [|b bs IH]; [cbn;lia|].
 cbn[value length app Nat.pow]. rewrite IH. destruct b; nia.
Qed.

Lemma same_value_marker bs cs : value bs=value cs -> marked 1 bs -> marked 1 cs.
Proof.

 intros He [pre [post [E Hpar]]]. subst bs.
 pose proof (value_bound pre) as Hp.
 assert (Hvalue:value cs=(value post*2+1)*2^length pre+value pre).
 { rewrite value_app in He. cbn[value] in He. nia. }
 assert (Hindex:length pre<length cs).
 { destruct (Nat.lt_ge_cases (length pre) (length cs)); [assumption|].
   pose proof (value_bound cs).
   assert (2^length cs<=2^length pre) by (apply Nat.pow_le_mono_r; lia). nia. }
 rewrite <-Hpar.
 apply (marked_value_remainder cs (length pre) (value post) (value pre)); assumption.
Qed.

Lemma add_two_marker b c bs : marked 1 bs -> marked 1 (b::c::bs).
Proof.
 intros [pre [post [E Hp]]]. subst bs.
 exists (b::c::pre),post. split; [reflexivity|].
 cbn[length]. replace (S (S (length pre))) with (length pre+1*2) by lia.
 rewrite Nat.mod_add by lia. exact Hp.
Qed.

Lemma marker_or_bound : forall bs,
 marked 1 bs \/ 3*value bs<2^(length bs+1).
Proof.

 fix IH 1. intro bs. destruct bs as [|b [|c bs]].
 - right. cbn. lia.
 - right. destruct b; cbn; lia.
 - destruct c.
   + left. exists [b],bs. split; reflexivity.
   + destruct (IH bs) as [Hm|Hb].
     * left. apply add_two_marker. exact Hm.
     * right. cbn[value length].
       replace (S (S (length bs))+1) with ((length bs+1)+2) by lia.
       rewrite Nat.pow_add_r. cbn[Nat.pow]. destruct b; nia.
Qed.

Lemma magnitude_marker bs A :
 value bs<2^A -> 2^(A+1)<3*value bs -> marked 1 bs.
Proof.

 intros Hv Hlarge.
 pose proof (digits_value A (value bs) Hv) as Hvalue.
 destruct (marker_or_bound (digits A (value bs))) as [Hm|Hb].
 - apply (same_value_marker (digits A (value bs)) bs Hvalue Hm).
 - rewrite digits_length,Hvalue in Hb. lia.
Qed.

End MagnitudeMarker.
End MagnitudeMarker.

Module OdEvenMarker.
(* The even-position ordinary successor of an odd defective wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import CounterBits WallInvariant MultiGapMarker MagnitudeMarker.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module OdEvenMarker.

Lemma power_positive n : 0<2^n.
Proof. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia. Qed.

Lemma minus_three_positive u : 0<2^(u+2)-3.
Proof. rewrite Nat.pow_add_r. cbn[Nat.pow]. pose proof (power_positive u). nia. Qed.

Lemma scaled_minus_three u J :
 (2^(u+2)-3)*2^J<2^(u+2+J).
Proof.

 rewrite (Nat.pow_add_r 2 (u+2) J).
 pose proof (power_positive J). pose proof (minus_three_positive u). nia.
Qed.

Lemma terminal_small m T : T<=6*2^m -> 2*T-1<2^(m+4).
Proof.

 intro H. rewrite Nat.pow_add_r. cbn[Nat.pow]. pose proof (power_positive m). nia.
Qed.

Lemma sum_small J x y :
 3<=J -> x<2^(J-3) -> y<2^(J-3) -> x+y<2^(J-2).
Proof.

 intros HJ Hx Hy. replace (J-2) with ((J-3)+1) by lia.
 rewrite Nat.pow_add_r. cbn[Nat.pow]. lia.
Qed.

Lemma three_small J x y z :
 4<=J -> x<2^(J-4) -> y<2^(J-4) -> z<2^(J-4) ->
 x+y+z<2^(J-2).
Proof.

 intros HJ Hx Hy Hz. replace (J-2) with ((J-4)+2) by lia.
 rewrite Nat.pow_add_r. cbn[Nat.pow]. lia.
Qed.

Lemma magnitude_from_parts bs A x y z t :
 6<=A -> x<2^(A-2) -> y<2^(A-6) -> z<2^(A-6) -> t<2^(A-6) ->
 0<x+y+z+t -> CounterBits.CounterBits.value bs+x+y+z+t=2^A -> WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros HA Hx Hy Hz Ht Hpos HE.

 assert (HP:2^A=64*2^(A-6)).
 { replace A with ((A-6)+6) at 1 by lia. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. }

 assert (HPx:2^(A-2)=16*2^(A-6)).
 { replace (A-2) with ((A-6)+4) by lia. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. }
 apply MagnitudeMarker.MagnitudeMarker.magnitude_marker with (A:=A).
 - pose proof (power_positive (A-6)). rewrite HP in *. rewrite HPx in Hx. lia.
 - rewrite Nat.pow_add_r. cbn[Nat.pow].
   rewrite HP in *. rewrite HPx in Hx.
   pose proof (power_positive (A-6)). lia.
Qed.

Lemma reachable_even_marker bs a j m u C T :
 2<=j -> u+1<=2*j -> m<=4*a -> 0<T -> T<=6*2^m ->
 C<2^(5*j-5) ->
 CounterBits.CounterBits.value bs+(C+2*T-1)+
  (2^(u+2)-3)*2^(5*j)+(2^(10*a+6)-3)*2^(25*a+9)=2^(m+7*j+3) ->
 WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros Hj Hu Hm HT HTb HC HE.
 set (J:=5*j). set (K:=25*a+9). set (A:=m+7*j+3).
 set (D:=2^(u+2)-3). set (E:=2^(10*a+6)-3).
 set (F:=D*2^J). set (Q:=E*2^K).
 set (c:=C+2*T-1).

 assert (HD:0<D) by (unfold D; apply minus_three_positive).

 assert (HEpos:0<E).
 { unfold E. replace (10*a+6) with ((10*a+4)+2) by lia.
   apply minus_three_positive. }

 assert (HJ:3<=J) by (unfold J; lia).

 assert (HK:4<=K) by (unfold K; lia).

 assert (Hc:0<c) by (unfold c; lia).

 assert (HF:F<2^(7*j+1)).
 { unfold F,D,J. eapply Nat.lt_le_trans.
   - apply scaled_minus_three.
   - apply Nat.pow_le_mono_r; clear -Hu Hj; lia. }

 assert (HQ:Q<2^(35*a+15)).
 { unfold Q,E,K. replace (10*a+6) with ((10*a+4)+2) by lia.
   pose proof (scaled_minus_three (10*a+4) (25*a+9)) as H.
   replace (10*a+4+2+(25*a+9)) with (35*a+15) in H by lia. exact H. }

 assert (HTs:2*T-1<2^(m+4)) by (apply terminal_small; exact HTb).

 assert (HEq:CounterBits.CounterBits.value bs+c+F+Q=2^A) by exact HE.
 destruct (Nat.le_gt_cases (7*j) (25*a+4)) as [Hsmall|Hlarge].
 - assert (HF':F<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }

   assert (HC':C<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }

   assert (HT':2*T-1<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }
   apply (MultiGapMarker.MultiGapMarker.positive_subtraction_marker bs A K E (c+F)).
   + clear -HK. lia.
   + exact HEpos.
   + clearbody F c. clear -Hc. lia.
   + replace (c+F) with (C+(2*T-1)+F) by (unfold c; clearbody F; clear -HT; lia).
     apply three_small; assumption.
   + unfold Q in HEq. clear -HEq. lia.
 - destruct (Nat.le_gt_cases j (5*a+2)) as [Hmiddle|Hbig].
   + assert (HCJ:C<2^(J-3)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold J; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HTJ:2*T-1<2^(J-3)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold J; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HcJ:c<2^(J-2)).
     { replace c with (C+(2*T-1)) by (unfold c; clear -HT; lia). apply sum_small; assumption. }

     assert (HCK:C<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold K; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HTK:2*T-1<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold K; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HcK:c<2^(K-2)).
     { replace c with (C+(2*T-1)) by (unfold c; clear -HT; lia). apply sum_small; try assumption; clear -HK; lia. }
     apply (MultiGapMarker.MultiGapMarker.two_gap_marker bs A J K D E c); try assumption.
     * apply Nat.min_glb; clear -HJ HK; lia.
     * destruct (Nat.le_ge_cases J K).
       -- rewrite Nat.min_l by assumption. exact HcJ.
       -- rewrite Nat.min_r by assumption. exact HcK.
   + assert (HA:6<=A) by (unfold A; lia).

     assert (HFA:F<2^(A-2)).
     { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HCA:C<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HTA:2*T-1<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HQA:Q<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HQ|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }
     apply (magnitude_from_parts bs A F C (2*T-1) Q); try assumption.
     all: clearbody F Q; unfold c in HEq; clear -HEq HT; lia.
Qed.

End OdEvenMarker.
End OdEvenMarker.

Module OdOddMarker.
(* The odd-position ordinary successor of an odd defective wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import CounterBits WallInvariant MultiGapMarker MagnitudeMarker OdEvenMarker.
Import List PeanoNat Lia.
Import ListNotations OdEvenMarker.OdEvenMarker.
Open Scope nat.

Module OdOddMarker.

Lemma terminal_small_odd m T : 1<=m -> T<=6*2^m -> T+3<2^(m+3).
Proof.

 intros Hm HT. assert (2<=2^m) by (change (2^1<=2^m); apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
Qed.

Lemma reachable_odd_marker bs a j m u C T :
 2<=j -> u+1<=2*j -> 1<=m<=4*a+2 -> 0<T -> T<=6*2^m ->
 C<2^(5*j-6) ->
 CounterBits.CounterBits.value bs+(C+T+3)+
  (2^(u+2)-3)*2^(5*j-1)+(2^(10*a+11)-3)*2^(25*a+24)=2^(m+7*j+2) ->
 WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros Hj Hu Hm HT HTb HC HE.
 set (J:=5*j-1). set (K:=25*a+24). set (A:=m+7*j+2).
 set (D:=2^(u+2)-3). set (E:=2^(10*a+11)-3).
 set (F:=D*2^J). set (Q:=E*2^K).
 set (c:=C+T+3).

 assert (HD:0<D) by (unfold D; apply minus_three_positive).

 assert (HEpos:0<E).
 { unfold E. replace (10*a+11) with ((10*a+9)+2) by lia.
   apply minus_three_positive. }

 assert (HJ:3<=J) by (unfold J; lia).

 assert (HK:4<=K) by (unfold K; lia).

 assert (Hc:0<c) by (unfold c; lia).

 assert (HF:F<2^(7*j)).
 { unfold F,D,J. eapply Nat.lt_le_trans.
   - apply scaled_minus_three.
   - apply Nat.pow_le_mono_r; clear -Hu Hj; lia. }

 assert (HQ:Q<2^(35*a+35)).
 { unfold Q,E,K. replace (10*a+11) with ((10*a+9)+2) by lia.
   pose proof (scaled_minus_three (10*a+9) (25*a+24)) as H.
   replace (10*a+9+2+(25*a+24)) with (35*a+35) in H by lia. exact H. }

 assert (HTs:T+3<2^(m+3)) by (apply terminal_small_odd; [lia|exact HTb]).

 assert (HEq:CounterBits.CounterBits.value bs+c+F+Q=2^A) by exact HE.
 destruct (Nat.le_gt_cases (7*j) (25*a+20)) as [Hsmall|Hlarge].
 - assert (HF':F<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }

   assert (HC':C<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }

   assert (HT':T+3<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }
   apply (MultiGapMarker.MultiGapMarker.positive_subtraction_marker bs A K E (c+F)).
   + clear -HK. lia.
   + exact HEpos.
   + clearbody F c. clear -Hc. lia.
   + replace (c+F) with (C+(T+3)+F) by (unfold c; clearbody F; clear -HT; lia).
     apply three_small; assumption.
   + unfold Q in HEq. clear -HEq. lia.
 - destruct (Nat.le_gt_cases j (5*a+5)) as [Hmiddle|Hbig].
   + assert (HCJ:C<2^(J-3)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold J; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HTJ:T+3<2^(J-3)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold J; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HcJ:c<2^(J-2)).
     { replace c with (C+(T+3)) by (unfold c; clear -HT; lia). apply sum_small; assumption. }

     assert (HCK:C<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold K; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HTK:T+3<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold K; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HcK:c<2^(K-2)).
     { replace c with (C+(T+3)) by (unfold c; clear -HT; lia). apply sum_small; try assumption; clear -HK; lia. }
     apply (MultiGapMarker.MultiGapMarker.two_gap_marker bs A J K D E c); try assumption.
     * apply Nat.min_glb; clear -HJ HK; lia.
     * destruct (Nat.le_ge_cases J K).
       -- rewrite Nat.min_l by assumption. exact HcJ.
       -- rewrite Nat.min_r by assumption. exact HcK.
   + assert (HA:6<=A) by (unfold A; lia).

     assert (HFA:F<2^(A-2)).
     { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HCA:C<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HTA:T+3<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HQA:Q<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HQ|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }
     apply (magnitude_from_parts bs A F C (T+3) Q); try assumption.
     all: clearbody F Q; unfold c in HEq; clear -HEq HT; lia.
Qed.

End OdOddMarker.
End OdOddMarker.

Module OdDirectMarker.
(* Marker preservation when the first marked odd-wall digit is encountered directly.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import CounterBits WallInvariant MultiGapMarker OdEvenMarker OdOddMarker.
Import List PeanoNat Lia.
Import ListNotations OdEvenMarker.OdEvenMarker OdOddMarker.OdOddMarker.
Open Scope nat.

Module OdDirectMarker.

Lemma direct_even_marker bs a j m T :
 1<=j -> m<=4*a -> 0<T -> T<=6*2^m ->
 CounterBits.CounterBits.value bs+(2*T-1)+(2^(2*j+2)-3)*2^(5*j)+
  (2^(10*a+6)-3)*2^(25*a+9)=2^(m+7*j+3) -> WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros Hj Hm HT HTb HE.
 set (J:=5*j). set (K:=25*a+9). set (A:=m+7*j+3).
 set (D:=2^(2*j+2)-3). set (E:=2^(10*a+6)-3).
 set (F:=D*2^J). set (Q:=E*2^K).

 assert (HD:0<D) by (unfold D; apply minus_three_positive).

 assert (HEp:0<E).
 { unfold E. replace (10*a+6) with ((10*a+4)+2) by lia. apply minus_three_positive. }

 assert (HJ:3<=J) by (unfold J; clear -Hj; lia).

 assert (HK:3<=K) by (unfold K; lia).

 assert (HTs:2*T-1<2^(m+4)) by (apply terminal_small; exact HTb).

 assert (HEq:CounterBits.CounterBits.value bs+(2*T-1)+F+Q=2^A) by exact HE.
 destruct (Nat.le_gt_cases (m+6) (5*j)) as [Hsmall|Hlarge].
 - apply (MultiGapMarker.MultiGapMarker.two_gap_marker bs A J K D E (2*T-1)); try assumption.
   + apply Nat.min_glb; assumption.
   + clear -HT. lia.
   + assert (Hmin:m+6<=Nat.min J K).
     { apply Nat.min_glb; unfold J,K; clear -Hsmall Hm; lia. }
     eapply Nat.lt_le_trans; [exact HTs|].
     apply Nat.pow_le_mono_r; clear -Hmin; lia.
 - destruct a as [|a].
   + assert (m=0) by lia. subst m.

     assert (j=1) by lia. subst j.
     change (CounterBits.CounterBits.value bs+(2*T-1)+13*32+61*512=1024) in HE.
     clear -HE. lia.
   + assert (HF:F<2^(7*j+2)).
     { unfold F,D,J. pose proof (scaled_minus_three (2*j) (5*j)) as H.
       replace (2*j+2+5*j) with (7*j+2) in H by lia. exact H. }

     assert (HFK:F<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HF|].
       apply Nat.pow_le_mono_r; unfold K; clear -Hj Hm Hlarge; lia. }

     assert (HTK:2*T-1<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HTs|].
       apply Nat.pow_le_mono_r; unfold K; clear -Hm; lia. }
     apply (MultiGapMarker.MultiGapMarker.positive_subtraction_marker bs A K E ((2*T-1)+F)); try assumption.
     * clearbody F. clear -HT. lia.
     * apply sum_small; assumption.
     * unfold Q in HEq. clear -HEq. lia.
Qed.

Lemma direct_odd_marker bs a j m T :
 1<=j -> 1<=m<=4*a+2 -> 0<T -> T<=6*2^m ->
 CounterBits.CounterBits.value bs+(T+3)+(2^(2*j+2)-3)*2^(5*j-1)+
  (2^(10*a+11)-3)*2^(25*a+24)=2^(m+7*j+2) -> WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros Hj Hm HT HTb HE.
 set (J:=5*j-1). set (K:=25*a+24). set (A:=m+7*j+2).
 set (D:=2^(2*j+2)-3). set (E:=2^(10*a+11)-3).
 set (F:=D*2^J). set (Q:=E*2^K).

 assert (HD:0<D) by (unfold D; apply minus_three_positive).

 assert (HEp:0<E).
 { unfold E. replace (10*a+11) with ((10*a+9)+2) by lia. apply minus_three_positive. }

 assert (HJ:3<=J) by (unfold J; clear -Hj; lia).

 assert (HK:3<=K) by (unfold K; lia).

 assert (HTs:T+3<2^(m+3)) by (apply terminal_small_odd; [lia|exact HTb]).

 assert (HEq:CounterBits.CounterBits.value bs+(T+3)+F+Q=2^A) by exact HE.
 destruct (Nat.le_gt_cases (m+6) (5*j)) as [Hsmall|Hlarge].
 - apply (MultiGapMarker.MultiGapMarker.two_gap_marker bs A J K D E (T+3)); try assumption.
   + apply Nat.min_glb; assumption.
   + lia.
   + assert (Hmin:m+5<=Nat.min J K).
     { apply Nat.min_glb; unfold J,K; clear -Hsmall Hm; lia. }
     eapply Nat.lt_le_trans; [exact HTs|].
     apply Nat.pow_le_mono_r; clear -Hmin; lia.
 - assert (HF:F<2^(7*j+1)).
   { unfold F,D,J. eapply Nat.lt_le_trans; [apply scaled_minus_three|].
     apply Nat.pow_le_mono_r; clear -Hj; lia. }

   assert (HFK:F<2^(K-3)).
   { eapply Nat.lt_le_trans; [exact HF|].
     apply Nat.pow_le_mono_r; unfold K; clear -Hj Hm Hlarge; lia. }

   assert (HTK:T+3<2^(K-3)).
   { eapply Nat.lt_le_trans; [exact HTs|].
     apply Nat.pow_le_mono_r; unfold K; clear -Hm; lia. }
   apply (MultiGapMarker.MultiGapMarker.positive_subtraction_marker bs A K E ((T+3)+F)); try assumption.
   + lia.
   + apply sum_small; assumption.
   + unfold Q in HEq. clear -HEq. lia.
Qed.

End OdDirectMarker.
End OdDirectMarker.

Module ExceptionalPasses.
(* Exceptional pass laws for a shift-overflow counter.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses.
Import String List PeanoNat NArith Lia.
Import LocalPasses.Mirrored.
Open Scope sym.

Module Exceptional.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dc := [0;0;0;0;1].
Notation dd := [1;0;0;0;1].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].

Lemma shifted_two : segRLs mtm (p^^2) x dc da.
Proof. esc. Qed.

Lemma shifted_even k :
  segRLs mtm (p^^(2*k+2)) (x ++ p^^k) dc da.
Proof.
  replace (2*k+2) with (2+k*2) by lia.
  rewrite lpow_add.
  eapply segRLs_trans.
  - apply shifted_two.
  - apply d0_Incs.
Qed.

Lemma shifted_odd k :
  segRLs mtm (p^^(2*k+3)) (x ++ p^^k) dc db.
Proof.
  replace (2*k+3) with (2+(k*2+1)) by lia.
  rewrite lpow_add.
  eapply segRLs_trans.
  - apply shifted_two.
  - apply d01_Incs.
Qed.

Lemma exception_zero : segRLs mtm x [] da dc.
Proof. esc. Qed.

Lemma exception_one : segRLs mtm (x ++ p) [] da dd.
Proof. esc. Qed.

Lemma exception_even k :
  segRLs mtm (x ++ p^^(2*k+2)) (x ++ p^^k) da da.
Proof.
  eapply @segRLs_trans with (ls2:=[]) (ls4:=x ++ p^^k).
  - apply exception_zero.
  - apply shifted_even.
Qed.

Lemma exception_odd k :
  segRLs mtm (x ++ p^^(2*k+3)) (x ++ p^^k) da db.
Proof.
  eapply @segRLs_trans with (ls2:=[]) (ls4:=x ++ p^^k).
  - apply exception_zero.
  - apply shifted_odd.
Qed.

Lemma exception_shifted : segRLs mtm x x dc da.
Proof. esc. Qed.

Lemma exception_shifted_even k :
  segRLs mtm (x ++ p^^(k*2)) (x ++ p^^k) dc da.
Proof.
  eapply segRLs_trans.
  - apply exception_shifted.
  - apply d0_Incs.
Qed.

Lemma exception_shifted_odd k :
  segRLs mtm (x ++ p^^(k*2+1)) (x ++ p^^k) dc db.
Proof.
  eapply segRLs_trans.
  - apply exception_shifted.
  - apply d01_Incs.
Qed.

Lemma exception_zeros k n :
  segRLs mtm (x ++ p^^((k+2)*2^n-2)) (x ++ p^^k) (da^^n) (da^^n).
Proof.
  gen k.
  induction n; intros.
  - cbn [Nat.pow lpow].
    replace ((k+2)*1-2) with k by lia.
    apply segRLs_nil.
  - cbn [Nat.pow lpow].
    eapply segRLs_concat.
    2: apply IHn.
    pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
    replace ((k+2)*(2*2^n)-2) with (2*((k+2)*2^n-2)+2) by nia.
    apply exception_even.
Qed.

Lemma exception_shifteds k n :
  segRLs mtm (x ++ p^^(k*2^n)) (x ++ p^^k) (dc^^n) (da^^n).
Proof.
  gen k.
  induction n; intros.
  - cbn [Nat.pow lpow].
    replace (k*1) with k by lia.
    apply segRLs_nil.
  - cbn [Nat.pow lpow].
    eapply segRLs_concat.
    2: apply IHn.
    replace (k*(2*2^n)) with ((k*2^n)*2) by nia.
    apply exception_shifted_even.
Qed.

End Exceptional.
End ExceptionalPasses.

Module PhaseE.
(* A complete wall pass through shifted digits.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses ExceptionalPasses WallInvariant.
Import String List PeanoNat NArith Lia.
Import LocalPasses.Mirrored ExceptionalPasses.Exceptional.
Open Scope sym.

Module PhaseE.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dc := [0;0;0;0;1].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].

Fixpoint shifted (bs:list bool) : list sym :=
 match bs with
 | [] => []
 | b::t => (if b then dc else da) ++ shifted t
 end.

Fixpoint normal (bs:list bool) : list sym :=
 match bs with
 | [] => []
 | b::t => (if b then db else da) ++ normal t
 end.

Fixpoint lag (b:bool) (bs:list bool) : list bool :=
 match bs with [] => [] | c::t => b::lag c t end.

Fixpoint finalbit (b:bool) (bs:list bool) : bool :=
 match bs with [] => b | c::t => finalbit c t end.

Definition xp (n:nat) (b:bool) : list (DH0*DH0) := x ++ p^^(2^n-2+(if b then 1 else 0)).

Open Scope nat.

Lemma normal_app a b : normal (a++b) = normal a ++ normal b.
Proof.
 induction a; cbn; [reflexivity|].
 rewrite IHa, app_assoc; reflexivity.
Qed.

Lemma lag_final b bs : lag b bs ++ [finalbit b bs] = b::bs.
Proof.
 gen b. induction bs; intros; cbn; [reflexivity|].
 rewrite IHbs; reflexivity.
Qed.

Lemma digit_shift n previous bit :
 n<>0 ->
 segRLs mtm (xp (S n) previous) (xp n bit)
   (if bit then dc else da) (if previous then db else da).
Proof.
 intro Hn.
 assert (Hpow: 2 <= 2^n).
 { destruct n; [lia|]. cbn [Nat.pow].
   pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia. }
 unfold xp.
 destruct previous, bit; cbn [Nat.pow].
 - applys_eq (exception_shifted_odd (2^n-1)); flia.
 - applys_eq (exception_odd (2^n-2)); flia.
 - applys_eq (exception_shifted_even (2^n-1)); flia.
 - applys_eq (exception_even (2^n-2)); flia.
Qed.

Lemma digits_shift n previous bs :
 n<>0 ->
 segRLs mtm (xp (length bs+n) previous) (xp n (finalbit previous bs))
   (shifted bs) (normal (lag previous bs)).
Proof.
 gen previous.
 induction bs; intros; cbn [length shifted normal lag finalbit].
 - apply segRLs_nil.
 - eapply segRLs_concat.
   + apply digit_shift. change (length bs+n<>0). lia.
   + apply IHbs; exact H.
Qed.

Lemma exception_blank : sideRLs mtm x 0inf (dc *> 0inf).
Proof. esc. Qed.

Lemma flush_zeros n :
 sideRLs mtm (xp (n+1) false) 0inf (da^^n *> dc *> 0inf).
Proof.
 unfold xp.
 replace (2^(n+1)-2+0) with ((0+2)*2^n-2) by
   (rewrite Nat.pow_add_r; cbn; lia).
 replace 0inf with (da^^n *> 0inf) at 1 by
   (rewrite lpow_all0 by solve_const0_eq; reflexivity).
 eapply @segRLs_sideRLs_concat with (w1:=da^^n) (ls2:=x).
 - apply exception_zeros.
 - apply exception_blank.
Qed.

Lemma flush n b :
 sideRLs mtm (xp (n+2) b) 0inf ((if b then db else da) *> da^^n *> dc *> 0inf).
Proof.
 replace (n+2) with (S (n+1)) by lia.
 replace 0inf with (da *> 0inf) at 1 by (st; reflexivity).
 eapply @segRLs_sideRLs_concat with (w1:=da) (ls2:=xp (n+1) false).
 - apply digit_shift; lia.
 - apply flush_zeros.
Qed.

Lemma normal_lag b bs :
 normal (lag b bs) ++ (if finalbit b bs then db else da) =
 (if b then db else da) ++ normal bs.
Proof.
 replace (if finalbit b bs then db else da) with
   (normal [finalbit b bs]) by (cbn [normal]; rewrite app_nil_r; reflexivity).
 rewrite <-normal_app, lag_final. reflexivity.
Qed.

Lemma digits_flush n previous bs :
 sideRLs mtm (xp (length bs+n+2) previous) (shifted bs *> 0inf)
   ((if previous then db else da) *> normal bs *> da^^n *> dc *> 0inf).
Proof.
 replace (length bs+n+2) with (length bs+(n+2)) by lia.
 rewrite <-Str_app_assoc.
 rewrite <-normal_lag, Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - apply digits_shift; lia.
 - apply flush.
Qed.

Lemma shifted_suffix u bs n :
 sideRLs mtm (p^^(2^(u+length bs+n+3)))
   (da^^u *> dc *> shifted bs *> 0inf)
   (da^^(u+1) *> db *> normal bs *> da^^n *> dc *> 0inf).
Proof.

 replace (da^^(u+1)) with (da^^u ++ da) by
   (rewrite lpow_add; cbn [lpow]; rewrite app_nil_r; reflexivity).
 rewrite Str_app_assoc.
 eapply @segRLs_sideRLs_concat with (ls2:=p^^(2^(length bs+n+3))).
 - applys_eq (d0s_Incs (2^(length bs+n+3)) u).
   repeat rewrite Nat.pow_add_r. flia.

 - eapply @segRLs_sideRLs_concat with (ls2:=xp (length bs+n+2) true).
   + unfold xp.
     assert (Hpow: 2<=2^(length bs+n+2)).
     { rewrite Nat.pow_add_r. cbn [Nat.pow].
       pose proof (Nat.pow_nonzero 2 (length bs+n) ltac:(lia)); nia. }

     replace (length bs+n+3) with (S (length bs+n+2)) by lia.
     cbn [Nat.pow].
     applys_eq (shifted_even (2^(length bs+n+2)-1)); flia.
   + apply digits_flush.
Qed.

Open Scope sym.

Lemma even_wall u bs n :
 let k := u+length bs+n+3 in
 (0inf <* <[1;1]) <* [0] {{A}}> ([1;1]^^k *> da^^u *> dc *> shifted bs *> 0inf)
 -[mtm]->+
 (0inf <* <[1;1]) <* [0] {{A}}> ([1] *> [1;1]^^k *> da^^(u+1) *> db *> normal bs *> da^^n *> dc *> 0inf).
Proof.
 cbn zeta.
 apply BigStep.
 eapply segRLs_sideRLs_concat.
 - apply lds_Incs'.
 - rewrite Nat.mul_1_l. apply shifted_suffix.
Qed.

Open Scope nat.

Lemma shifted_app a b : shifted (a++b) = shifted a ++ shifted b.
Proof.
 induction a; cbn; [reflexivity|].
 rewrite IHa, app_assoc; reflexivity.
Qed.

Lemma shifted_zeros n : shifted (repeat false n) = da^^n.
Proof. induction n; cbn [repeat shifted lpow]; congruence. Qed.

Lemma normal_zeros n : normal (repeat false n) = da^^n.
Proof. induction n; cbn [repeat normal lpow]; congruence. Qed.

Lemma first_true bs :
 In true bs -> exists u t, bs = repeat false u ++ true::t.
Proof.
 induction bs as [|a bs IH]; intro H.
 - inversion H.
 - destruct a.
   + exists 0, bs. reflexivity.
   + destruct H as [H|H]; [discriminate|].
     destruct (IH H) as [u [t E]].
     exists (S u), t. cbn [repeat]. rewrite E. reflexivity.
Qed.

Definition output_bits n bs := false :: bs ++ repeat false (n-length bs-2).

Lemma phase_E n bs :
 length bs+2 <= n -> In true bs ->
 WallInvariant.WallInvariant.E n bs -[mtm]->+ WallInvariant.WallInvariant.Od n (output_bits n bs).
Proof.

 intros Hlen Hin.
 destruct (first_true bs Hin) as [u [t E]]. subst bs.
 rewrite length_app, repeat_length in Hlen. cbn [length] in Hlen.
 set (padding := n-length (repeat false u ++ true::t)-2).
 assert (Hk:n=u+length t+padding+3).
 { unfold padding. rewrite length_app, repeat_length. cbn [length]. lia. }

 pose proof (even_wall u t padding) as Hrun.
 cbn zeta in Hrun. rewrite <-Hk in Hrun.
 unfold WallInvariant.WallInvariant.E, WallInvariant.WallInvariant.Od, WallInvariant.WallInvariant.wall, output_bits.
 change WallInvariant.WallInvariant.shifted with shifted.
 change WallInvariant.WallInvariant.normal with normal.
 fold padding.
 rewrite shifted_app, shifted_zeros.

 cbn [shifted normal].
 repeat rewrite normal_app.
 repeat rewrite normal_zeros.
 cbn [normal].
 applys_eq Hrun; ut; st; simpl_rotate; reflexivity.
Qed.

Lemma output_length n bs :
 length bs+2<=n -> length (output_bits n bs)+1=n.
Proof.
 intro H. unfold output_bits. cbn [length].
 rewrite length_app, repeat_length. lia.
Qed.

Lemma output_first_zero n bs : WallInvariant.WallInvariant.first_zero (output_bits n bs).
Proof. exists (bs ++ repeat false (n-length bs-2)). reflexivity. Qed.

Lemma output_marked n bs :
 WallInvariant.WallInvariant.marked 1 bs -> WallInvariant.WallInvariant.marked 0 (output_bits n bs).
Proof.
 intros [pre [post [E Hparity]]].
 exists (false::pre), (post ++ repeat false (n-length bs-2)).
 split.
 - unfold output_bits. rewrite E. cbn. rewrite <-app_assoc. reflexivity.
 - cbn [length].
   replace (S (length pre)) with (length pre+1) by lia.
   rewrite Nat.add_mod by lia. rewrite Hparity. reflexivity.
Qed.

Lemma phase_E_invariant n bs :
 length bs+2<=n -> WallInvariant.WallInvariant.marked 1 bs ->
 exists c, WallInvariant.WallInvariant.E n bs -[mtm]->+ c /\ WallInvariant.WallInvariant.invariant c.
Proof.
 intros Hlen Hmark.
 exists (WallInvariant.WallInvariant.Od n (output_bits n bs)). split.
 - apply phase_E; [exact Hlen|].
   destruct Hmark as [pre [post [E Hp]]]. rewrite E.
   apply in_or_app. right. cbn. auto.
 - apply WallInvariant.WallInvariant.InvOd.
   + pose proof (output_length n bs Hlen). lia.
   + apply output_first_zero.
   + apply output_marked; exact Hmark.
Qed.

End PhaseE.
End PhaseE.

Module PhaseEd.
(* Shifted digits followed by a displaced terminal digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape.
Import LocalPasses ExceptionalPasses PhaseE CounterRules.
Import BoundaryRules CounterBatch CounterFinish WallInvariant.
Import String List PeanoNat NArith Lia.
Import LocalPasses.Mirrored ExceptionalPasses.Exceptional PhaseE.PhaseE.
Open Scope sym.

Module PhaseEd.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dd := [0;0;0;1;0].
Notation dd1 := [1;0;0;1;0].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].

Fixpoint fuel (bs:list bool) : nat :=
 match bs with
 | [] => 3
 | b::t => 2*fuel t + (if b then 1 else 3)
 end.

Fixpoint value (bs:list bool) : nat :=
 match bs with [] => 0 | b::t => (if b then 1 else 0)+2*value t end.

Open Scope nat.

Lemma defect_carry :
 sideRLs mtm (x ++ p^^3) (dd *> 0inf) (db *> dd1 *> 0inf).
Proof. esc. Qed.

Lemma carried_prefix bs :
 segRLs mtm (x ++ p^^(fuel bs)) (x ++ p^^3) (shifted bs) (db^^(length bs)).
Proof.
 induction bs as [|b bs IH].
 - cbn [fuel shifted length lpow]. apply segRLs_nil.
 - cbn [fuel shifted length lpow].
   eapply segRLs_concat.
   + destruct b.
     * applys_eq (exception_shifted_odd (fuel bs)); flia.
     * apply exception_odd.
   + exact IH.
Qed.

Lemma ordinary_prefix bs :
 In true bs ->
 segRLs mtm (p^^(fuel bs+2)) (x ++ p^^3) (shifted bs) (db^^(length bs)).
Proof.
 induction bs as [|b bs IH]; intro H.
 - inversion H.
 - destruct b; cbn [fuel shifted length lpow].
   + eapply segRLs_concat.
     * applys_eq (shifted_odd (fuel bs)); flia.
     * apply carried_prefix.
   + eapply segRLs_concat.
     * applys_eq (d01_Incs (fuel bs+2)); flia.
     * apply IH. destruct H as [H|H]; [discriminate|exact H].
Qed.

Lemma nonzero_preconversion bs :
 In true bs ->
 sideRLs mtm (p^^(fuel bs+2)) (shifted bs *> dd *> 0inf)
   (db^^(length bs+1) *> dd1 *> 0inf).
Proof.
 intro H.
 replace (db^^(length bs+1)) with (db^^(length bs) ++ db) by
   (rewrite lpow_add; cbn [lpow]; rewrite app_nil_r; reflexivity).
 rewrite Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - apply ordinary_prefix; exact H.
 - apply defect_carry.
Qed.

Lemma fuel_value bs : fuel bs+2*value bs+3 = 6*2^(length bs).
Proof.
 induction bs as [|b bs IH].
 - reflexivity.
 - destruct b; cbn [fuel value length Nat.pow] in *; nia.
Qed.

Lemma value_bound bs : value bs < 2^(length bs).
Proof.
 induction bs as [|b bs IH].
 - cbn; lia.
 - destruct b; cbn [value length Nat.pow]; nia.
Qed.

Lemma fuel_bound bs : fuel bs+3 <= 6*2^(length bs).
Proof. pose proof (fuel_value bs). lia. Qed.

Lemma fuel_positive bs : 3<=fuel bs.
Proof. induction bs as [|b bs IH]; cbn [fuel]; [lia|destruct b; lia]. Qed.

Lemma fuel_fits n bs : length bs+3<=n -> fuel bs+3 < 2^n.
Proof.
 intro Hn.
 pose proof (fuel_bound bs).
 assert (2^(length bs+3)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r in H0.
 cbn [Nat.pow] in H0.
 pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)). nia.
Qed.

Open Scope sym.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma even_wall_counter n r :
 (0inf <* <[1;1]) <* [0] {{A}}> ([1;1]^^n *> r) -[mtm]->*
 CounterRules.CounterRules.LC n (2^n-1) |> r.
Proof.
 unfold CounterRules.CounterRules.LC. rewrite BinDec_full. esx.
Qed.

Lemma shifted_rank_bound len k s :
 (k<2^len)%nat -> ((k*2+1)*2^s-1 < 2^(len+1+s))%nat.
Proof.
 intro Hk. repeat rewrite Nat.pow_add_r. cbn [Nat.pow].
 pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.
Qed.

Lemma gap2_even_counter len k a :
 (k<2^len)%nat ->
 CounterRules.CounterRules.LC len k |> db^^(a*2) *> dd1 *> 0inf -[mtm]->+
 CounterRules.CounterRules.LC (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) |> CounterRules.CounterRules.RC 1.
Proof.
 intro Hk.
 unfold CounterRules.CounterRules.LC, CounterRules.CounterRules.RC.
 rewrite BinDec_mulpow2sub1 by (apply shifted_rank_bound; exact Hk).
 rewrite BinInc_1.
 applys_eq (BoundaryRules.BoundaryRules.gap2_even (CounterRules.CounterRules.LC len k) 0inf a); ut; st; reflexivity.
Qed.

Lemma gap2_odd_counter len k a :
 (k<2^len)%nat ->
 CounterRules.CounterRules.LC len k |> db^^(a*2+1) *> dd1 *> 0inf -[mtm]->+
 CounterRules.CounterRules.LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> CounterRules.CounterRules.RC 0.
Proof.
 intro Hk.
 unfold CounterRules.CounterRules.LC, CounterRules.CounterRules.RC.
 rewrite BinDec_mulpow2sub1 by (apply shifted_rank_bound; exact Hk).
 rewrite BinInc_O.
 applys_eq (BoundaryRules.BoundaryRules.gap2_odd (CounterRules.CounterRules.LC len k) 0inf a); ut; st; reflexivity.
Qed.

Lemma gap2_even_wall len k a :
 (k<2^len)%nat ->
 CounterRules.CounterRules.LC len k |> db^^(a*2) *> dd1 *> 0inf -[mtm]->+
 (0inf <* <[1;1]) <* [0] {{A}}>
   ([1] *> [1;1]^^(len+1+(a*5+1)) *> CounterRules.CounterRules.RC ((k*2+1)*2^(a*5+1)+1)).
Proof.
 intro Hk.
 eapply progress_trans.
 - apply gap2_even_counter; exact Hk.
 - applys_eq (CounterFinish.CounterFinish.counter_finish (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) 1).
   + pose proof (Nat.pow_nonzero 2 (a*5+1) ltac:(lia)). flia.
   + apply shifted_rank_bound; exact Hk.
Qed.

Lemma gap2_odd_wall len k a :
 (k<2^len)%nat ->
 CounterRules.CounterRules.LC len k |> db^^(a*2+1) *> dd1 *> 0inf -[mtm]->+
 (0inf <* <[1;1]) <* [0] {{A}}>
   ([1] *> [1;1]^^(len+1+(a*5+4)) *> CounterRules.CounterRules.RC ((k*2+1)*2^(a*5+4))).
Proof.
 intro Hk.
 eapply progress_trans.
 - apply gap2_odd_counter; exact Hk.
 - applys_eq (CounterFinish.CounterFinish.counter_finish (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) 0).
   + pose proof (Nat.pow_nonzero 2 (a*5+4) ltac:(lia)). flia.
   + apply shifted_rank_bound; exact Hk.
Qed.

Lemma nonzero_counter_entry n bs :
 (length bs+3<=n)%nat -> In true bs ->
 WallInvariant.WallInvariant.Ed n bs -[mtm]->*
 CounterRules.CounterRules.LC n (2^n-fuel bs-3) |> db^^(length bs+1) *> dd1 *> 0inf.
Proof.
 intros Hlen Hin.
 pose proof (fuel_fits n bs Hlen) as Hfits.
 unfold WallInvariant.WallInvariant.Ed, WallInvariant.WallInvariant.wall.
 change WallInvariant.WallInvariant.shifted with shifted.
 repeat rewrite Str_app_assoc.
 eapply evstep_trans.
 - apply even_wall_counter.
 - replace (2^n-1)%nat with ((2^n-fuel bs-3)+(fuel bs+2))%nat by lia.
   apply CounterBatch.CounterBatch.right_pass_batch.
   + lia.
   + apply nonzero_preconversion; exact Hin.
Qed.

Open Scope nat.

Lemma shifted_value_bound len k s :
 k<2^len -> (k*2+1)*2^s < 2^(len+1+s).
Proof.
 intro Hk. repeat rewrite Nat.pow_add_r. cbn [Nat.pow].
 pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.
Qed.

Lemma remaining_bound n bs :
 length bs+3<=n -> 2^n-fuel bs-3 < 2^n.
Proof.
 intro Hn. pose proof (fuel_fits n bs Hn). lia.
Qed.

Lemma remaining_decomposition n bs :
 length bs+3<=n ->
 exists q, 2^n-fuel bs-3 = (q*2+1)*2^(length bs+1)+2*value bs.
Proof.
 intro Hn.
 pose proof (fuel_value bs) as Hfuel.
 pose proof (fuel_fits n bs Hn) as Hfits.
 set (d:=n-length bs-2).
 assert (Hd:0<d) by (unfold d; lia).
 assert (He:n=length bs+2+d) by (unfold d; lia).
 assert (Hp:2<=2^d).
 { destruct d; [lia|]. cbn [Nat.pow].
   pose proof (Nat.pow_nonzero 2 d ltac:(lia)); nia. }
 exists (2^d-2).
 rewrite He at 1.
 repeat rewrite Nat.pow_add_r.
 cbn [Nat.pow].
 pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)). nia.
Qed.

Lemma remaining_lower_bound n bs :
 length bs+3<=n -> 0 < 2^n-fuel bs-3.
Proof.
 intro Hn.
 destruct (remaining_decomposition n bs Hn) as [q E].
 rewrite E. pose proof (Nat.pow_nonzero 2 (length bs+1) ltac:(lia)). nia.
Qed.

End PhaseEd.
End PhaseEd.

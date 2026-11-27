From BusyCoq Require Import PR58Part1 PR58Part2 PR58Part3 PR58Part4.


Module StrongEdDirect.
(* The direct conversion of an odd-length displaced digit word.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import PhaseEd StrongDigits StrongInvariant CounterFinish CounterRules WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.

Module StrongEdDirect.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope nat.

Lemma direct_guard n bs a :
 length bs+1=a*2 -> length bs+3<=n ->
 StrongInvariant.StrongInvariant.digit_guard (CounterFinish.CounterFinish.digits (n+a*5+1)
   (((2^n-PhaseEd.PhaseEd.fuel bs-3)*2+1)*2^(a*5))).
Proof.

 intros Hlen Hn.
 set (k:=2^n-PhaseEd.PhaseEd.fuel bs-3).
 destruct (mod2 a) as [b Ha|b Ha].
 - subst a.
   replace (b*2*5) with (10*b) by lia.
   apply (StrongDigits.StrongDigits.close_shift_guard n k b (14*b+1)); try lia.
   destruct (PhaseEd.PhaseEd.remaining_decomposition n bs Hn) as [q Hk].
   fold k in Hk.
   replace (length bs+1) with (4*b) in Hk by lia.
   apply (StrongDigits.StrongDigits.digits_bit_remainder (n+10*b+1)
     ((k*2+1)*2^(10*b)) (14*b+1) q ((PhaseEd.PhaseEd.value bs*4+1)*2^(10*b)));
     try lia.

   + pose proof (PhaseEd.PhaseEd.value_bound bs) as Hv.
     assert (Hp:2^(length bs+1)=2^(4*b)) by (f_equal; lia).
     rewrite Nat.pow_add_r in Hp. cbn[Nat.pow] in Hp.
     replace (14*b+1) with ((4*b+1)+10*b) by lia.
     rewrite Nat.pow_add_r,(Nat.pow_add_r 2 (4*b) 1). cbn[Nat.pow].
     pose proof (Nat.pow_nonzero 2 (10*b) ltac:(lia)). nia.
   + replace (14*b+1) with ((4*b+1)+10*b) by lia.
     rewrite Nat.pow_add_r,(Nat.pow_add_r 2 (4*b) 1). cbn[Nat.pow].
     nia.
 - apply StrongDigits.StrongDigits.odd_shift_guard. lia.
Qed.

Open Scope sym.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma Ed_direct_strong n bs a :
 (length bs+1=a*2)%nat -> (length bs+3<=n)%nat -> WallInvariant.WallInvariant.marked 1 bs ->
 exists c, WallInvariant.WallInvariant.Ed n bs -[mtm]->+ c /\ StrongInvariant.StrongInvariant.strong c.
Proof.

 intros Hlen Hn Hmark.
 assert (Hin:In true bs).
 { destruct Hmark as [pre [post [E Hp]]]. rewrite E.
   apply in_or_app. right. cbn. auto. }
 set (k:=(2^n-PhaseEd.PhaseEd.fuel bs-3)%nat).
 assert (Hk:(k<2^n)%nat) by (unfold k; apply PhaseEd.PhaseEd.remaining_bound; exact Hn).
 pose proof (PhaseEd.PhaseEd.nonzero_counter_entry n bs Hn Hin) as Hentry.
 fold k in Hentry. rewrite Hlen in Hentry.
 pose proof (PhaseEd.PhaseEd.gap2_even_wall n k a Hk) as Hwall.
 set (v:=((k*2+1)*2^(a*5))%nat).
 assert (Hv:(v<2^(n+a*5+1))%nat).
 { unfold v. replace (n+a*5+1)%nat with (n+1+a*5)%nat by lia.
   apply PhaseEd.PhaseEd.shifted_value_bound. exact Hk. }

 assert (Heq:((k*2+1)*2^(a*5+1)+1=v*2+1)%nat).
 { unfold v. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. }
 rewrite Heq in Hwall.
 replace (n+1+(a*5+1))%nat with ((n+a*5+1)+1)%nat in Hwall by lia.
 rewrite (StrongDigits.StrongDigits.odd_counter_wall (n+a*5+1) v Hv) in Hwall.
 exists (WallInvariant.WallInvariant.E (n+a*5+1+2) (CounterFinish.CounterFinish.digits (n+a*5+1) v)). split.
 - eapply evstep_progress_trans; eassumption.
 - apply StrongInvariant.StrongInvariant.StrongE; [rewrite CounterFinish.CounterFinish.digits_length; lia|].
   unfold v,k. apply direct_guard; assumption.
Qed.

End StrongEdDirect.
End StrongEdDirect.

Module StrongEdEven.
(* Exact amplifier slack in the even-valuation defect branch.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2.
Import PhaseEd OddImage EdEvenOrbit CounterBits CounterFinish CounterRules.
Import MarkerArithmetic WallInvariant CDPasses TerminalSuccessor StrongInvariant.
Import List PeanoNat Lia.
Import ListNotations.

Module StrongEdEven.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation ld := [1;1].

Lemma even_image_exact n v width k i q r :
 (0<v)%nat -> (v*2+2<=n)%nat -> (width<=n)%nat -> (k<2^width)%nat ->
 (i<v*5-1)%nat -> (i mod 2=1)%nat -> (r<2^i)%nat ->
 (k=(q*2+1)*2^i+r)%nat ->
 exists out,
 ((length out+3=n+v*5+2)%nat \/ (length out+2=n+v*5+2)%nat) /\ WallInvariant.WallInvariant.marked 1 out /\
 WallInvariant.WallInvariant.O n (repeat false (v*2)++true::CounterFinish.CounterFinish.digits width k) -[mtm]->+
 WallInvariant.WallInvariant.Ed (n+v*5+2) out.
Proof.

 intros Hv Hn Hw Hk Hi Hodd Hr Hdecomp.
 destruct (EdEvenOrbit.EdEvenOrbit.first_mass_bounds n v width k Hv Hn Hw Hk) as [Hmin Hmax].
 assert (Hlength:(width+(n+v*5+1-width)=n+v*5+1)%nat) by lia.
 assert (Hvalue:CDPasses.CDPasses.value (CounterFinish.CounterFinish.digits width k)=k).
 { change (CounterBits.CounterBits.value (CounterFinish.CounterFinish.digits width k)=k). apply CounterBits.CounterBits.digits_value; exact Hk. }
 assert (Hmin':(2^length (CounterFinish.CounterFinish.digits width k)<=OddImage.OddImage.first_mass n v)%nat).
 { rewrite CounterFinish.CounterFinish.digits_length. exact Hmin. }
 assert (Hmax':(OddImage.OddImage.first_mass n v+CDPasses.CDPasses.value (CounterFinish.CounterFinish.digits width k)<
   2^(length (CounterFinish.CounterFinish.digits width k)+(n+v*5+1-width)))%nat).
 { rewrite CounterFinish.CounterFinish.digits_length,Hvalue,Hlength. exact Hmax. }

 destruct (OddImage.OddImage.initial_even_image n v (CounterFinish.CounterFinish.digits width k)
   (n+v*5+1-width) Hv ltac:(lia) Hmin' Hmax')
   as [out [Hlen [Hval Hrun]]].
 rewrite CounterFinish.CounterFinish.digits_length,Hlength in Hlen.
 rewrite Hvalue in Hval.
 assert (Hnonzero:(k<>0)%nat).
 { pose proof (Nat.pow_nonzero 2 i ltac:(lia)). nia. }
 assert (Hany:CDPasses.CDPasses.any (CounterFinish.CounterFinish.digits width k)=true).
 { apply EdEvenOrbit.EdEvenOrbit.any_true. apply CounterBits.CounterBits.value_nonzero. rewrite CounterBits.CounterBits.digits_value by exact Hk.
   exact Hnonzero. }
 rewrite Hany in Hrun. cbn [CDPasses.CDPasses.terminal] in Hrun.

 assert (Hlower:(2^(n+v*5-1)<=OddImage.OddImage.first_mass n v+k)%nat).
 { pose proof (TerminalSuccessor.TerminalSuccessor.first_mass_lower n v Hv Hn). lia. }
 assert (Hupper:(OddImage.OddImage.first_mass n v+k<2^((n+v*5-1)+2))%nat).
 { replace (n+v*5-1+2)%nat with (n+v*5+1)%nat by lia. exact Hmax. }
 pose proof (TerminalSuccessor.TerminalSuccessor.mass_length out (n+v*5-1) (OddImage.OddImage.first_mass n v+k)
   Hval Hlower Hupper) as Hsizes.
 exists out. split; [lia|]. split.
 - rewrite <-Hodd.
   apply (MarkerArithmetic.MarkerArithmetic.low_marker_preserved out k i q r (v*5-1)
     (2*OddImage.OddImage.first_fuel n (v*2)+1)); try lia.
   change (CounterBits.CounterBits.value out+2^length out=OddImage.OddImage.first_mass n v+k)%nat in Hval.
   exact Hval.
 - exact Hrun.
Qed.

Lemma Ed_even_valuation_exact n bs b :
 (length bs=4*b)%nat -> (length bs+3<=n)%nat -> In true bs ->
 exists out,
 ((length out+3=n+35*b+17)%nat \/ (length out+2=n+35*b+17)%nat) /\ WallInvariant.WallInvariant.marked 1 out /\
 WallInvariant.WallInvariant.Ed n bs -[mtm]->+ WallInvariant.WallInvariant.Ed (n+35*b+17) out.
Proof.

 intros Hlength Hn Hin.
 set (k:=(2^n-PhaseEd.PhaseEd.fuel bs-3)%nat).
 assert (Hk:(k<2^n)%nat) by (unfold k; apply PhaseEd.PhaseEd.remaining_bound; exact Hn).
 destruct (PhaseEd.PhaseEd.remaining_decomposition n bs Hn) as [q Hdecomp].
 fold k in Hdecomp. rewrite Hlength in Hdecomp.
 pose proof (PhaseEd.PhaseEd.value_bound bs) as Hsmall. rewrite Hlength in Hsmall.
 assert (Hr:(2*PhaseEd.PhaseEd.value bs<2^(4*b+1))%nat).
 { rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }

 destruct (even_image_exact (n+10*b+5) (5*b+2) n k (4*b+1) q
   (2*PhaseEd.PhaseEd.value bs) ltac:(lia) ltac:(lia) ltac:(lia) Hk ltac:(lia)
   ltac:(rewrite Nat.add_mod, Nat.mul_mod by lia; reflexivity) Hr Hdecomp)
   as [out [Hlen [Hmark Hrun]]].
 replace (n+10*b+5+(5*b+2)*5+2)%nat with (n+35*b+17)%nat in * by lia.
 exists out. split; [exact Hlen|]. split; [exact Hmark|].
 eapply progress_trans; [|exact Hrun].

 pose proof (PhaseEd.PhaseEd.nonzero_counter_entry n bs Hn Hin) as Hentry.
 fold k in Hentry.
 replace (length bs+1)%nat with ((b*2)*2+1)%nat in Hentry by lia.
 pose proof (PhaseEd.PhaseEd.gap2_odd_wall n k (b*2) Hk) as Hwall.

 assert (Hstart:WallInvariant.WallInvariant.Ed n bs -[mtm]->+
   (0inf <* <[1;1]) <* [0] {{A}}>
     ([1] *> ld^^(n+10*b+5) *> CounterRules.CounterRules.RC ((k*2+1)*2^((5*b+2)*2)))).
 { replace (n+10*b+5)%nat with (n+1+((b*2)*5+4))%nat by lia.
   replace ((5*b+2)*2)%nat with ((b*2)*5+4)%nat by lia.
   eapply evstep_progress_trans; eassumption. }
 unfold WallInvariant.WallInvariant.O,WallInvariant.WallInvariant.wall.
 repeat rewrite Str_app_assoc.
 rewrite EdEvenOrbit.EdEvenOrbit.normal_shift_odd by exact Hk.
 applys_eq Hstart; ut; st; simpl_rotate; reflexivity.
Qed.


Lemma Ed_even_strong n bs b :
 (length bs=4*b)%nat -> (length bs+3=n)%nat -> WallInvariant.WallInvariant.marked 1 bs ->
 exists c, WallInvariant.WallInvariant.Ed n bs -[mtm]->+ c /\ StrongInvariant.StrongInvariant.strong c.
Proof.
 intros Hlen Hn Hmark.
 assert (Hin:In true bs).
 { destruct Hmark as [pre [post [E Hp]]]. rewrite E.
   apply in_or_app. right. cbn. auto. }
 destruct (Ed_even_valuation_exact n bs b Hlen ltac:(lia) Hin)
   as [out [Hslack [Hmarker Hrun]]].
 exists (WallInvariant.WallInvariant.Ed (n+35*b+17) out). split; [exact Hrun|].
 apply StrongInvariant.StrongInvariant.StrongEd; assumption.
Qed.
End StrongEdEven.
End StrongEdEven.

Module EdOddBounds.
(* Arithmetic bounds for the odd branch of a displaced-digit wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import EdOddOrbit PhaseEd OddImage OddFuel OddRoute RouteDeficit.
Import CounterBits CounterFinish WallInvariant CDPasses RouteMarkerBound.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdOddBounds.
Open Scope nat.

Lemma source_rank_balance n bs :
 length bs+3<=n ->
 EdOddOrbit.EdOddOrbit.source_rank n bs+6*2^length bs=2^n+2*PhaseEd.PhaseEd.value bs.
Proof.
 intro Hn.
 pose proof (PhaseEd.PhaseEd.fuel_value bs) as Hfuel.
 pose proof (PhaseEd.PhaseEd.fuel_fits n bs Hn) as Hfits.
 unfold EdOddOrbit.EdOddOrbit.source_rank. lia.
Qed.

Lemma scale_deficit b j :
 (2^(10*b+11)-3)*2^(25*b+23)*2^(5*j+2)*2^(2*j+1)=
 (2^(10*b+11)-3)*2^(25*b+7*j+26).
Proof.
 replace (25*b+7*j+26) with ((25*b+23)+(5*j+2)+(2*j+1)) by lia.
 rewrite !Nat.pow_add_r, !Nat.mul_assoc. reflexivity.
Qed.

Lemma digits_true_at width value i q :
 i<width -> value/2^i=q*2+1 -> nth i (CounterFinish.CounterFinish.digits width value) false=true.
Proof.
 intros Hi Hq.
 rewrite (CounterBits.CounterBits.digits_split width i value) by lia.
 rewrite app_nth2 by (rewrite CounterFinish.CounterFinish.digits_length; lia).
 rewrite CounterFinish.CounterFinish.digits_length,Nat.sub_diag,Hq.
 replace (width-i) with (S (width-i-1)) by lia.
 rewrite CounterFinish.CounterFinish.digits_odd. reflexivity.
Qed.

Lemma source_even_bit n bs : length bs+5<=n ->
 nth (length bs+4) (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs)) false=true.
Proof.

 intro Hn.
 set (m:=length bs). set (d:=n-m-5).
 assert (He:n=m+5+d) by (unfold d,m; lia).
 pose proof (PhaseEd.PhaseEd.fuel_value bs) as Hfuel.
 pose proof (PhaseEd.PhaseEd.value_bound bs) as Hv.
 pose proof (PhaseEd.PhaseEd.fuel_fits n bs ltac:(lia)) as Hfits.
 fold m in Hfuel,Hv.
 assert (Hp:0<2^m) by (pose proof (Nat.pow_nonzero 2 m ltac:(lia)); lia).
 assert (Hd:0<2^d) by (pose proof (Nat.pow_nonzero 2 d ltac:(lia)); lia).

 assert (Hbig:2^n=2^m*32*2^d).
 { rewrite He. rewrite !Nat.pow_add_r. reflexivity. }
 assert (Hbit:2^(m+4)=2^m*16) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Hsmall:10*2^m+2*PhaseEd.PhaseEd.value bs<2^(m+4)) by (rewrite Hbit; nia).
 assert (Hdecomp:EdOddOrbit.EdOddOrbit.source_rank n bs=
   ((2^d-1)*2+1)*2^(m+4)+(10*2^m+2*PhaseEd.PhaseEd.value bs)).
 { unfold EdOddOrbit.EdOddOrbit.source_rank. rewrite Hbig,Hbit in *. nia. }

 apply (digits_true_at n (EdOddOrbit.EdOddOrbit.source_rank n bs) (m+4) (2^d-1)); [lia|].
 rewrite Hdecomp,Nat.add_comm,Nat.div_add by (apply Nat.pow_nonzero; lia).
 rewrite Nat.div_small by exact Hsmall. lia.
Qed.

Lemma first_deficit n u z : u+1<=n ->
 OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n u) z+(2^(u+2)-3)*2^z+1=2^(n+1+z).
Proof.

 intro Hn. destruct (OddImage.OddImage.first_fuel_bounds n u Hn) as [He Hb].
 assert (Hp:0<2^u) by (pose proof (Nat.pow_nonzero 2 u ltac:(lia)); lia).
 assert (Hz:0<2^z) by (pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia).
 assert (Hu:2^(u+2)=2^u*4) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Htotal:2^(n+1+z)=2^n*2*2^z).
 { rewrite !Nat.pow_add_r. reflexivity. }
 unfold OddFuel.OddFuel.grown. rewrite Hu,Htotal. nia.
Qed.

Lemma initial_deficit n (bs:list bool) b : length bs=4*b+2 -> length bs+3<=n ->
 EdOddOrbit.EdOddOrbit.initial_rank n b+(2^(10*b+11)-3)*2^(25*b+23)+1=
   2^(EdOddOrbit.EdOddOrbit.initial_width n b).
Proof.
 intros Hm Hn. unfold EdOddOrbit.EdOddOrbit.initial_rank,EdOddOrbit.EdOddOrbit.initial_width.
 replace (10*b+11) with ((10*b+9)+2) by lia.
 replace (n+35*b+34) with ((n+10*b+10)+1+(25*b+23)) by lia.
 apply first_deficit. lia.
Qed.

Lemma marked_drop_pair bs : WallInvariant.WallInvariant.marked 1 (false::false::bs) -> WallInvariant.WallInvariant.marked 1 bs.
Proof.
 intros [pre [post [E Hp]]].
 destruct pre as [|a [|a' pre]]; try discriminate E.
 inversion E; subst.
 exists pre,post. split; [reflexivity|].
 cbn [length] in Hp.
 replace (S (S (length pre))) with (length pre+1*2) in Hp by lia.
 rewrite Nat.mod_add in Hp by lia. exact Hp.
Qed.

Lemma marked_drop_even_zeros s bs :
 WallInvariant.WallInvariant.marked 1 (repeat false (s*2)++bs) -> WallInvariant.WallInvariant.marked 1 bs.
Proof.
 induction s; intro H; [exact H|].
 replace (S s*2) with (S (S (s*2))) in H by lia.
 cbn [repeat app] in H.
 apply IHs. apply marked_drop_pair. exact H.
Qed.

End EdOddBounds.
End EdOddBounds.

Module EdOddTight.
(* The low marker survives an overflowing odd-gap conversion route.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import EdOddBounds EdOddOrbit PhaseEd OddRoute RouteDeficit RouteMarkerBound.
Import CounterBits CounterFinish WallInvariant CDPasses GapMarker.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdOddTight.
Open Scope nat.

Lemma value_zeros n : CDPasses.CDPasses.value (repeat false n)=0.
Proof. induction n; cbn [repeat CDPasses.CDPasses.value CDPasses.CDPasses.bitval]; lia. Qed.

Lemma correction_small b j e v w :
 2*j<=4*b+6 -> e<2^(7*j+3) -> v<2^(4*b+2) -> w<2^(2*j+1) ->
 let c:=e*2^(2*j+1)+12*2^(4*b+2)+2*w-4*v in
 0<c /\ c<2^((25*b+7*j+26)-2) /\
 c+4*v=e*2^(2*j+1)+12*2^(4*b+2)+2*w.
Proof.

 intros Hj He Hv Hw. cbn zeta.
 set (c:=e*2^(2*j+1)+12*2^(4*b+2)+2*w-4*v).
 assert (Hp:0<2^(4*b+2)).
 { pose proof (Nat.pow_nonzero 2 (4*b+2) ltac:(lia)); lia. }
 assert (Hpos:0<c) by (unfold c; nia).
 assert (Hbalance:c+4*v=e*2^(2*j+1)+12*2^(4*b+2)+2*w)
   by (unfold c; nia).
 split; [exact Hpos|]. split; [|exact Hbalance].

 assert (Hfirst:e*2^(2*j+1)<2^(9*j+4)).
 { assert (Hprod:2^(9*j+4)=2^(7*j+3)*2^(2*j+1)).
   { replace (9*j+4) with ((7*j+3)+(2*j+1)) by lia. apply Nat.pow_add_r. }
   rewrite Hprod. pose proof (Nat.pow_nonzero 2 (2*j+1) ltac:(lia)). nia. }
 assert (Hsecond:12*2^(4*b+2)<2^(4*b+6)).
 { assert (Hprod:2^(4*b+6)=2^(4*b+2)*16).
   { replace (4*b+6) with ((4*b+2)+4) by lia.
     rewrite Nat.pow_add_r. reflexivity. }
   rewrite Hprod. nia. }
 assert (Hthird:2*w<2^(2*j+2)).
 { replace (2*j+2) with ((2*j+1)+1) by lia.
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }

 assert (Ha:2^(9*j+4)<=2^(25*b+7*j+22)) by (apply Nat.pow_le_mono_r; lia).
 assert (Hb:2^(4*b+6)<=2^(25*b+7*j+22)) by (apply Nat.pow_le_mono_r; lia).
 assert (Hc:2^(2*j+2)<=2^(25*b+7*j+22)) by (apply Nat.pow_le_mono_r; lia).
 assert (Htarget:2^(25*b+7*j+26-2)=2^(25*b+7*j+22)*4).
 { replace (25*b+7*j+26-2) with ((25*b+7*j+22)+2) by lia.
   rewrite Nat.pow_add_r. reflexivity. }
 rewrite Htarget. clear -Hbalance Hfirst Hsecond Hthird Ha Hb Hc. lia.
Qed.

Lemma odd_route_tight_marker n bs b L' k' rest out t :
 length bs=4*b+2 -> length bs+3<=n ->
 OddRoute.OddRoute.route (EdOddOrbit.EdOddOrbit.initial_width n b) (EdOddOrbit.EdOddOrbit.initial_rank n b)
   (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs)) L' k' rest ->
 t*2=k'+1 -> CDPasses.CDPasses.value out+2^length out=t+CDPasses.CDPasses.value rest ->
 length out+1=L' -> WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros Hm Hn Hroute Ht Hmass Htight.
 set (d:=(2^(10*b+11)-3)*2^(25*b+23)).
 pose proof (EdOddBounds.EdOddBounds.initial_deficit n bs b Hm ltac:(lia)) as Hd.
 fold d in Hd.
 destruct (RouteDeficit.RouteDeficit.route_deficit _ _ _ _ _ _ Hroute d Hd)
   as [j [e [Hlen [HL [Hdef He]]]]].

 assert (Hj:2*j<=4*b+6).
 { destruct (Nat.le_gt_cases (length bs+5) n) as [Hwide|Hnarrow].
   - pose proof (EdOddBounds.EdOddBounds.source_even_bit n bs Hwide) as Hbit.
     assert (Hpar:(length bs+4) mod 2=0).
     { rewrite Hm. replace (4*b+2+4) with ((2*b+3)*2) by lia.
       apply Nat.mod_mul. lia. }
     pose proof (RouteMarkerBound.RouteMarkerBound.route_known_even_bound _ _ _ _ _ _ j (length bs+4)
       Hroute Hlen Hbit Hpar). lia.
   - rewrite CounterFinish.CounterFinish.digits_length in Hlen. lia. }

 destruct (RouteDeficit.RouteDeficit.route_suffix _ _ _ _ _ _ Hroute) as [pre Hprefix].
 assert (Hpre:length pre=2*j+1).
 { rewrite Hprefix,length_app in Hlen. lia. }
 assert (Hrank:EdOddOrbit.EdOddOrbit.source_rank n bs<2^n).
 { unfold EdOddOrbit.EdOddOrbit.source_rank. apply PhaseEd.PhaseEd.remaining_bound. lia. }

 assert (Hvalue:CDPasses.CDPasses.value (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs))=EdOddOrbit.EdOddOrbit.source_rank n bs).
 { change (CounterBits.CounterBits.value (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs))=EdOddOrbit.EdOddOrbit.source_rank n bs).
   apply CounterBits.CounterBits.digits_value; exact Hrank. }
 rewrite Hprefix,CDPasses.CDPasses.value_append,Hpre in Hvalue.
 pose proof (CDPasses.CDPasses.value_bound pre) as Hw. rewrite Hpre in Hw.
 pose proof (PhaseEd.PhaseEd.value_bound bs) as Hv. rewrite Hm in Hv.
 destruct (correction_small b j e (PhaseEd.PhaseEd.value bs) (CDPasses.CDPasses.value pre) ltac:(lia) He Hv Hw)
   as [Hc [Hcsmall Hcbalance]].
 set (c:=e*2^(2*j+1)+12*2^(4*b+2)+2*CDPasses.CDPasses.value pre-4*PhaseEd.PhaseEd.value bs) in *.

 assert (Hsource:EdOddOrbit.EdOddOrbit.source_rank n bs+6*2^(4*b+2)=2^n+2*PhaseEd.PhaseEd.value bs).
 { rewrite <-Hm. now apply EdOddBounds.EdOddBounds.source_rank_balance. }
 assert (Hpowtight:2^L'=2^length out*2).
 { rewrite <-Htight,Nat.pow_add_r. reflexivity. }
 assert (Hcore:2*CDPasses.CDPasses.value out+d*2^(5*j+2)+e=2*CDPasses.CDPasses.value rest).
 { rewrite Hpowtight in Hdef. clear -Hdef Hmass Ht. nia. }

 assert (Hbig:d*2^(5*j+2)*2^(2*j+1)=
   (2^(10*b+11)-3)*2^(25*b+7*j+26)).
 { unfold d. apply EdOddBounds.EdOddBounds.scale_deficit. }

 assert (Hshift:2^(2*j+2)=2^(2*j+1)*2).
 { replace (2*j+2) with ((2*j+1)+1) by lia. rewrite Nat.pow_add_r. reflexivity. }
 assert (Hright:2^(n+1)=2^n*2) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Hequation:CDPasses.CDPasses.value out*2^(2*j+2)+c+
   (2^(10*b+11)-3)*2^(25*b+7*j+26)=2^(n+1)).
 { rewrite <-Hbig,Hshift,Hright.
   pose proof (f_equal (fun x=>x*2^(2*j+1)) Hcore) as Hscaled.
   cbn beta in Hscaled.
   clear -Hscaled Hvalue Hsource Hcbalance.
   nia. }

 assert (Hmarked:WallInvariant.WallInvariant.marked 1 (repeat false (2*j+2)++out)).
 { apply (GapMarker.GapMarker.small_subtraction_marker (repeat false (2*j+2)++out)
     (n+1) (10*b+11) (25*b+7*j+26) c).
   - clear -b j. lia.
   - clear -b. lia.
   - exact Hc.
   - exact Hcsmall.
   -
   change (CDPasses.CDPasses.value (repeat false (2*j+2)++out)+c+
     (2^(10*b+11)-3)*2^(25*b+7*j+26)=2^(n+1)).
   rewrite CDPasses.CDPasses.value_append,value_zeros,repeat_length. cbn [Nat.add].
   rewrite (Nat.mul_comm (2^(2*j+2)) (CDPasses.CDPasses.value out)). exact Hequation. }
 replace (2*j+2) with ((j+1)*2) in Hmarked by (clear -j; lia).
 apply EdOddBounds.EdOddBounds.marked_drop_even_zeros in Hmarked. exact Hmarked.
Qed.

End EdOddTight.
End EdOddTight.

Module SignedGapMarker.
(* A small signed correction preserves a marker next to a binary gap.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits MarkerArithmetic WallInvariant GapMarker.
Import String List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits MarkerArithmetic.MarkerArithmetic.
Import WallInvariant.WallInvariant GapMarker.GapMarker.
Open Scope nat.

Module SignedGapMarker.

Lemma high_residue v A C M low : M<=A -> M<=C ->
 v+2^C=2^A+low -> v mod 2^M=low mod 2^M.
Proof.
 intros HA HC Heq.
 rewrite (power_multiple M C), (power_multiple M A) in Heq by assumption.
 replace (2^(A-M)*2^M+low) with (low+2^(A-M)*2^M) in Heq by lia.
 apply (f_equal (fun n=>n mod 2^M)) in Heq.
 rewrite !Nat.mod_add in Heq by (apply Nat.pow_nonzero; lia). exact Heq.
Qed.

Lemma positive_three_marker bs A B J delta :
 3<=B -> J+2<=A -> delta<2^J ->
 value bs+(2^B-3)*2^J=2^A+delta -> marked 1 bs.
Proof.

 intros HB HA Hd Heq.
 assert (HpowB:8<=2^B) by (change (2^3<=2^B); apply Nat.pow_le_mono_r; lia).
 assert (Hsum:value bs+2^(B+J)=2^A+(3*2^J+delta)).
 { rewrite Nat.pow_add_r. clear -Heq HpowB. nia. }

 destruct (mod2 J) as [a EJ|a EJ]; subst J.
 - pose proof (high_residue (value bs) A (B+a*2) (a*2+2)
     (3*2^(a*2)+delta) ltac:(lia) ltac:(lia) Hsum) as Hmod.
   pose proof (marked_residue_auto bs (a*2+1) (2^(a*2)+delta)) as Hmark.
   replace ((a*2+1) mod 2) with 1 in Hmark by
     (rewrite Nat.add_comm,Nat.mod_add by lia; reflexivity).
   apply Hmark.
   + rewrite Nat.pow_add_r. cbn [Nat.pow]. lia.
   + replace (a*2+1+1) with (a*2+2) by lia. rewrite Hmod.
     rewrite Nat.mod_small.
     * rewrite (Nat.pow_add_r 2 (a*2) 1). cbn [Nat.pow]. nia.
     * rewrite (Nat.pow_add_r 2 (a*2) 2). cbn [Nat.pow]. lia.

 - pose proof (high_residue (value bs) A (B+(1+a*2)) ((1+a*2)+1)
     (3*2^(1+a*2)+delta) ltac:(lia) ltac:(lia) Hsum) as Hmod.

   pose proof (marked_residue_auto bs (1+a*2) delta) as Hmark.
   replace ((1+a*2) mod 2) with 1 in Hmark by
     (rewrite Nat.mod_add by lia; reflexivity).
   apply Hmark; [exact Hd|]. rewrite Hmod.
   replace (3*2^(1+a*2)+delta) with
     ((2^(1+a*2)+delta)+1*2^((1+a*2)+1)) by
     (rewrite (Nat.pow_add_r 2 (1+a*2) 1); cbn [Nat.pow]; nia).
   rewrite Nat.mod_add by (apply Nat.pow_nonzero; lia).
   apply Nat.mod_small. rewrite (Nat.pow_add_r 2 (1+a*2) 1). cbn [Nat.pow]. lia.
Qed.

Lemma signed_small_marker bs A B J c small :
 3<=J -> 3<=B -> J+2<=A ->
 0<c -> c<2^(J-2) -> small<2^(J-2) ->
 value bs+c+(2^B-3)*2^J=2^A+small -> marked 1 bs.
Proof.

 intros HJ HB HA Hc Hcsmall Hsmall Heq.
 destruct (Nat.lt_ge_cases small c) as [Hnegative|Hpositive].
 - apply (small_subtraction_marker bs A B J (c-small)); try assumption; try lia.
 - apply (positive_three_marker bs A B J (small-c)); try assumption.
   + assert (2^(J-2)<=2^J) by (apply Nat.pow_le_mono_r; lia). lia.
   + lia.
Qed.

End SignedGapMarker.
End SignedGapMarker.

Module EdOddLoose.
(* A loose displaced-digit output also retains the odd-position marker.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import EdOddBounds EdOddOrbit EdOddTight PhaseEd OddRoute RouteDeficit.
Import CounterBits CounterFinish WallInvariant CDPasses SignedGapMarker.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdOddLoose.
Open Scope nat.

Lemma odd_route_loose_marker n bs b L' k' rest out t :
 length bs=4*b+2 -> length bs+3=n ->
 OddRoute.OddRoute.route (EdOddOrbit.EdOddOrbit.initial_width n b) (EdOddOrbit.EdOddOrbit.initial_rank n b)
   (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs)) L' k' rest ->
 t*2=k'+1 -> CDPasses.CDPasses.value out+2^length out=t+CDPasses.CDPasses.value rest ->
 length out+2=L' -> WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros Hm Hn Hroute Ht Hmass Hloose.
 set (d:=(2^(10*b+11)-3)*2^(25*b+23)).
 pose proof (EdOddBounds.EdOddBounds.initial_deficit n bs b Hm ltac:(lia)) as Hd.
 fold d in Hd.
 destruct (RouteDeficit.RouteDeficit.route_deficit _ _ _ _ _ _ Hroute d Hd)
   as [j [e [Hlen [HL [Hdef He]]]]].
 assert (Hj:2*j<=4*b+6) by (rewrite CounterFinish.CounterFinish.digits_length in Hlen; lia).

 destruct (RouteDeficit.RouteDeficit.route_suffix _ _ _ _ _ _ Hroute) as [pre Hprefix].
 assert (Hpre:length pre=2*j+1).
 { rewrite Hprefix,length_app in Hlen. lia. }
 assert (Hrank:EdOddOrbit.EdOddOrbit.source_rank n bs<2^n).
 { unfold EdOddOrbit.EdOddOrbit.source_rank. apply PhaseEd.PhaseEd.remaining_bound. lia. }

 assert (Hvalue:CDPasses.CDPasses.value (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs))=EdOddOrbit.EdOddOrbit.source_rank n bs).
 { change (CounterBits.CounterBits.value (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs))=EdOddOrbit.EdOddOrbit.source_rank n bs).
   apply CounterBits.CounterBits.digits_value; exact Hrank. }
 rewrite Hprefix,CDPasses.CDPasses.value_append,Hpre in Hvalue.
 pose proof (CDPasses.CDPasses.value_bound pre) as Hw. rewrite Hpre in Hw.
 pose proof (PhaseEd.PhaseEd.value_bound bs) as Hv. rewrite Hm in Hv.
 destruct (EdOddTight.EdOddTight.correction_small b j e (PhaseEd.PhaseEd.value bs) (CDPasses.CDPasses.value pre) Hj He Hv Hw)
   as [Hc [Hcsmall Hcbalance]].
 set (c:=e*2^(2*j+1)+12*2^(4*b+2)+2*CDPasses.CDPasses.value pre-4*PhaseEd.PhaseEd.value bs) in *.

 assert (Hsource:EdOddOrbit.EdOddOrbit.source_rank n bs+6*2^(4*b+2)=2^n+2*PhaseEd.PhaseEd.value bs).
 { rewrite <-Hm. apply EdOddBounds.EdOddBounds.source_rank_balance.
   clear -Hn. lia. }
 assert (Hpowloose:2^L'=2^length out*4).
 { rewrite <-Hloose,Nat.pow_add_r. reflexivity. }
 assert (Hpowhalf:2^(L'-1)=2^length out*2).
 { replace (L'-1) with (length out+1) by (clear -Hloose; lia).
   rewrite Nat.pow_add_r. reflexivity. }
 assert (Hcore:2*CDPasses.CDPasses.value out+d*2^(5*j+2)+e=2^(L'-1)+2*CDPasses.CDPasses.value rest).
 { rewrite Hpowloose in Hdef. rewrite Hpowhalf. clear -Hdef Hmass Ht. nia. }

 assert (Hbig:d*2^(5*j+2)*2^(2*j+1)=
   (2^(10*b+11)-3)*2^(25*b+7*j+26)).
 { unfold d. apply EdOddBounds.EdOddBounds.scale_deficit. }

 assert (Hshift:2^(2*j+2)=2^(2*j+1)*2).
 { replace (2*j+2) with ((2*j+1)+1) by lia. rewrite Nat.pow_add_r. reflexivity. }
 assert (Hright:2^(n+1)=2^n*2) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Hlarge:2^(L'+2*j)=2^(L'-1)*2^(2*j+1)).
 { replace (L'+2*j) with ((L'-1)+(2*j+1)) by (clear -Hloose; lia).
   apply Nat.pow_add_r. }
 assert (Hequation:CDPasses.CDPasses.value out*2^(2*j+2)+c+
   (2^(10*b+11)-3)*2^(25*b+7*j+26)=2^(L'+2*j)+2^(n+1)).
 { rewrite <-Hbig,Hshift,Hright,Hlarge.
   pose proof (f_equal (fun x=>x*2^(2*j+1)) Hcore) as Hscaled.
   cbn beta in Hscaled.
   clear -Hscaled Hvalue Hsource Hcbalance. nia. }

 assert (Hmarked:WallInvariant.WallInvariant.marked 1 (repeat false (2*j+2)++out)).
 { apply (SignedGapMarker.SignedGapMarker.signed_small_marker (repeat false (2*j+2)++out)
     (L'+2*j) (10*b+11) (25*b+7*j+26) c (2^(n+1))).
   - clear -b j. lia.
   - clear -b. lia.
   - clear -HL Hm Hn. unfold EdOddOrbit.EdOddOrbit.initial_width in HL. lia.
   - exact Hc.
   - exact Hcsmall.

   - clear -Hm Hn. apply Nat.pow_lt_mono_r; lia.
   - change (CDPasses.CDPasses.value (repeat false (2*j+2)++out)+c+
       (2^(10*b+11)-3)*2^(25*b+7*j+26)=2^(L'+2*j)+2^(n+1)).
     rewrite CDPasses.CDPasses.value_append,EdOddTight.EdOddTight.value_zeros,repeat_length. cbn [Nat.add].
     rewrite (Nat.mul_comm (2^(2*j+2)) (CDPasses.CDPasses.value out)). exact Hequation. }

 replace (2*j+2) with ((j+1)*2) in Hmarked by (clear -j; lia).
 apply EdOddBounds.EdOddBounds.marked_drop_even_zeros in Hmarked. exact Hmarked.
Qed.

End EdOddLoose.
End EdOddLoose.

Module StrongEdOddFacts.
(* Exact rank digits and lower bounds for the marked displaced-digit family.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import EdOddOrbit EdOddBounds PhaseEd OddRoute RouteDeficit.
Import CounterBits CounterFinish MarkerArithmetic WallInvariant CDPasses.
Import String List PeanoNat Lia.
Import ListNotations.

Module StrongEdOddFacts.
Open Scope nat.

Lemma source_rank_exact n bs : length bs+3=n ->
 EdOddOrbit.EdOddOrbit.source_rank n bs=2^(length bs+1)+2*PhaseEd.PhaseEd.value bs.
Proof.

 intro Hn.
 pose proof (PhaseEd.PhaseEd.fuel_value bs) as Hf.
 pose proof (PhaseEd.PhaseEd.fuel_fits n bs ltac:(lia)) as Hfits.
 unfold EdOddOrbit.EdOddOrbit.source_rank. rewrite <-Hn in *.
 rewrite !Nat.pow_add_r in *. cbn [Nat.pow] in *. nia.
Qed.

Lemma source_digits_exact n bs : length bs+3=n ->
 CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs)=false::bs++[true;false].
Proof.
 intro Hn.
 pose proof (MarkerArithmetic.MarkerArithmetic.digits_value_inverse (false::bs++[true;false])) as H.
 assert (Hlength:length (false::bs++[true;false])=n).
 { cbn [length]. rewrite length_app. cbn [length]. lia. }

 assert (Hvalue:CounterBits.CounterBits.value (false::bs++[true;false])=EdOddOrbit.EdOddOrbit.source_rank n bs).
 { change (CDPasses.CDPasses.value (false::bs++[true;false])=EdOddOrbit.EdOddOrbit.source_rank n bs).
   cbn [CDPasses.CDPasses.value CDPasses.CDPasses.bitval]. rewrite CDPasses.CDPasses.value_append.
   cbn [CDPasses.CDPasses.value CDPasses.CDPasses.bitval]. rewrite source_rank_exact by exact Hn.
   change (CDPasses.CDPasses.value bs) with (PhaseEd.PhaseEd.value bs).
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }
 rewrite Hlength,Hvalue in H. exact H.
Qed.

Lemma marked_prefix bs : WallInvariant.WallInvariant.marked 1 bs -> WallInvariant.WallInvariant.marked 0 (false::bs).
Proof.
 intros [pre [post [Epre Hpar]]].
 exists (false::pre),post. split; [rewrite Epre; reflexivity|].
 cbn [length]. replace (S (length pre)) with (length pre+1) by lia.
 rewrite Nat.add_mod by lia. rewrite Hpar. reflexivity.
Qed.

Lemma route_append L k bs L' k' rest tail :
 OddRoute.OddRoute.route L k bs L' k' rest -> OddRoute.OddRoute.route L k (bs++tail) L' k' (rest++tail).
Proof.
 intro H. induction H.
 - rewrite <-app_assoc. cbn [app]. constructor.
 - rewrite <-app_assoc. cbn [app]. constructor. exact IHroute.
Qed.

Lemma route_mass_large n bs b L k rest t :
 length bs=4*b+2 -> length bs+3=n ->
 OddRoute.OddRoute.route (EdOddOrbit.EdOddOrbit.initial_width n b) (EdOddOrbit.EdOddOrbit.initial_rank n b)
   (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs)) L k rest ->
 t*2=k+1 -> 2^(L-2)<=t.
Proof.

 intros Hm Hn Hroute Ht.
 set (d:=(2^(10*b+11)-3)*2^(25*b+23)).
 pose proof (EdOddBounds.EdOddBounds.initial_deficit n bs b Hm ltac:(lia)) as Hd. fold d in Hd.
 destruct (RouteDeficit.RouteDeficit.route_deficit _ _ _ _ _ _ Hroute d Hd)
   as [j [e [Hlen [HL [Hdef He]]]]].
 rewrite CounterFinish.CounterFinish.digits_length in Hlen.
 unfold EdOddOrbit.EdOddOrbit.initial_width in HL.
 assert (HLpos:2<=L) by lia.

 assert (Hdom:d*2^(5*j+2)<2^(35*b+5*j+36)).
 { assert (Hp:0<2^(25*b+23)*2^(5*j+2)).
   { pose proof (Nat.pow_nonzero 2 (25*b+23) ltac:(lia)).
     pose proof (Nat.pow_nonzero 2 (5*j+2) ltac:(lia)). nia. }
   assert (HB:0<2^(10*b+11)) by (pose proof (Nat.pow_nonzero 2 (10*b+11) ltac:(lia)); lia).

   assert (Hpow:2^(35*b+5*j+36)=2^(10*b+11)*2^(25*b+23)*2^(5*j+2)).
   { replace (35*b+5*j+36) with ((10*b+11)+(25*b+23)+(5*j+2)) by lia.
     rewrite !Nat.pow_add_r. reflexivity. }
   unfold d. rewrite Hpow. clear -Hp HB. nia. }

 assert (Hsmall:2^(7*j+3)<=2^(35*b+5*j+36)) by (apply Nat.pow_le_mono_r; lia).
 assert (Hdeficit:d*2^(5*j+2)+e<2^(L-1)).
 { assert (Htwice:2^(35*b+5*j+37)=2^(35*b+5*j+36)*2).
   { replace (35*b+5*j+37) with ((35*b+5*j+36)+1) by lia.
     rewrite Nat.pow_add_r. reflexivity. }
   assert (Hcap:2^(35*b+5*j+37)<=2^(L-1)) by (apply Nat.pow_le_mono_r; lia).
   rewrite Htwice in Hcap. clear -Hdom He Hsmall Hcap. lia. }

 assert (HpowL:2^L=2^(L-2)*4).
 { replace L with ((L-2)+2) at 1 by lia. rewrite Nat.pow_add_r. reflexivity. }
 assert (HpowHalf:2^(L-1)=2^(L-2)*2).
 { replace (L-1) with ((L-2)+1) by lia. rewrite Nat.pow_add_r. reflexivity. }
 rewrite HpowL in Hdef. rewrite HpowHalf in Hdeficit.
 clear -Hdef Hdeficit Ht. nia.
Qed.

End StrongEdOddFacts.
End StrongEdOddFacts.

Module StrongEdOdd.
(* Preservation of the marked displaced-digit family in the odd-valuation case.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import EdOddOrbit EdOddTight EdOddLoose StrongEdOddFacts EdEvenOrbit.
Import OddRoute OddImage CounterFinish CounterRules WallInvariant CDPasses.
Import StrongInvariant.
Import String List PeanoNat Lia.
Import ListNotations.

Module StrongEdOdd.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma strong_ed_odd n bs b :
 (length bs=4*b+2)%nat -> (length bs+3=n)%nat -> WallInvariant.WallInvariant.marked 1 bs ->
 exists c, WallInvariant.WallInvariant.Ed n bs -[mtm]->+ c /\ StrongInvariant.StrongInvariant.strong c.
Proof.

 intros Hm Hn Hmarked.
 assert (Hin:In true bs).
 { destruct Hmarked as [pre [post [He Hp]]]. rewrite He.
   apply in_or_app. right. cbn. auto. }
 pose proof (EdOddOrbit.EdOddOrbit.Ed_odd_valuation_entry n bs b Hm ltac:(lia) Hin) as Hentry.
 destruct (EdOddOrbit.EdOddOrbit.Ed_odd_entry_fuel n bs b Hm ltac:(lia)) as [Hfuel [Hbound Hodd]].
 pose proof (StrongEdOddFacts.StrongEdOddFacts.source_digits_exact n bs Hn) as Hdigits.
 pose proof (StrongEdOddFacts.StrongEdOddFacts.marked_prefix bs Hmarked) as Hmark.
 assert (Hprefixfuel:(2^length (false::bs)-1<=EdOddOrbit.EdOddOrbit.initial_rank n b)%nat).
 { rewrite CounterFinish.CounterFinish.digits_length in Hfuel.
   assert (2^length (false::bs)<=2^n)%nat by
     (apply Nat.pow_le_mono_r; cbn [length]; lia). lia. }

 destruct (OddRoute.OddRoute.marked_route (EdOddOrbit.EdOddOrbit.initial_width n b) (EdOddOrbit.EdOddOrbit.initial_rank n b)
   (false::bs) Hmark Hprefixfuel) as [L [k [rest [Hr Hlower]]]].
 assert (Hroute:OddRoute.OddRoute.route (EdOddOrbit.EdOddOrbit.initial_width n b) (EdOddOrbit.EdOddOrbit.initial_rank n b)
   (CounterFinish.CounterFinish.digits n (EdOddOrbit.EdOddOrbit.source_rank n bs)) L k (rest++[true;false])).
 { rewrite Hdigits. change (OddRoute.OddRoute.route (EdOddOrbit.EdOddOrbit.initial_width n b) (EdOddOrbit.EdOddOrbit.initial_rank n b)
     ((false::bs)++[true;false]) L k (rest++[true;false])).
   apply StrongEdOddFacts.StrongEdOddFacts.route_append. exact Hr. }

 destruct (OddRoute.OddRoute.route_bound _ _ _ _ _ _ Hroute Hbound) as [Hcap Hpar].
 destruct (OddRoute.OddRoute.route_dimensions _ _ _ _ _ _ Hroute) as [j [Hlen HL]].
 assert (Hwidth:(length (rest++[true;false])+2<=L)%nat).
 { rewrite CounterFinish.CounterFinish.digits_length in Hlen. rewrite HL. unfold EdOddOrbit.EdOddOrbit.initial_width. lia. }
 pose proof (OddRoute.OddRoute.route_run _ _ _ _ _ _ 0inf Hroute Hbound) as Hrun.

 destruct (mod2 k) as [q Hq|q Hq].
 { rewrite Hq,Nat.mod_mul in Hpar by lia. discriminate. }
 assert (Ht:((q+1)*2=k+1)%nat) by lia.
 set (t:=(q+1)%nat). fold t in Ht.
 pose proof (StrongEdOddFacts.StrongEdOddFacts.route_mass_large n bs b L k (rest++[true;false]) t Hm Hn Hroute Ht) as Hlarge.

 assert (Hmin:(2^length (rest++[true;false])<=t)%nat).
 { assert (2^length (rest++[true;false])<=2^(L-2))%nat by
     (apply Nat.pow_le_mono_r; lia). lia. }
 pose proof (CDPasses.CDPasses.value_bound (rest++[true;false])) as Hrest.
 assert (Hmax:(t+CDPasses.CDPasses.value (rest++[true;false])<
   2^(length (rest++[true;false])+(L-length (rest++[true;false]))))%nat).
 { replace (length (rest++[true;false])+(L-length (rest++[true;false])))%nat
     with L by lia. lia. }

 destruct (OddImage.OddImage.fuel_C_image L k t (rest++[true;false])
   (L-length (rest++[true;false])) ltac:(lia) (eq_sym Ht) Hmin Hmax)
   as [out [Houtlen [Hvalue Hfinish]]].
 replace (length (rest++[true;false])+(L-length (rest++[true;false])))%nat
   with L in Houtlen by lia.
 assert (Hany:CDPasses.CDPasses.any (rest++[true;false])=true).
 { apply EdEvenOrbit.EdEvenOrbit.any_true. apply in_or_app. right. cbn. auto. }
 rewrite Hany in Hfinish.
 change (CounterRules.CounterRules.LC L k |> [1;0;0;0] *> WallInvariant.WallInvariant.normal (rest++[true;false]) *> 0inf
   -[mtm]->+ WallInvariant.WallInvariant.Ed (L+1) out) in Hfinish.

 assert (Hlo:(L-2<=length out)%nat).
 { pose proof (CDPasses.CDPasses.value_bound out) as Hv.
   destruct (Nat.le_gt_cases (L-2) (length out)); [assumption|].
   assert (Hp:(2^(length out+1)<=2^(L-2))%nat) by (apply Nat.pow_le_mono_r; lia).
   rewrite Nat.pow_add_r in Hp. cbn [Nat.pow] in Hp. lia. }

 assert (Hcases:(length out+2=L \/ length out+1=L)%nat) by lia.
 assert (Hmarker:WallInvariant.WallInvariant.marked 1 out).
 { destruct Hcases as [Hloose|Htight].
   - apply (EdOddLoose.EdOddLoose.odd_route_loose_marker n bs b L k (rest++[true;false]) out t
       Hm Hn Hroute Ht Hvalue Hloose).
   - apply (EdOddTight.EdOddTight.odd_route_tight_marker n bs b L k (rest++[true;false]) out t
       Hm ltac:(lia) Hroute Ht Hvalue Htight). }

 exists (WallInvariant.WallInvariant.Ed (L+1) out). split.
 - eapply progress_trans; [exact Hentry|].
   eapply progress_trans; eassumption.
 - apply StrongInvariant.StrongInvariant.StrongEd; [destruct Hcases; [left|right]; lia|exact Hmarker].
Qed.

End StrongEdOdd.
End StrongEdOdd.

Module StrongEdLoose.
(* Closure of the displaced-digit walls with three spare amplifier pairs.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import StrongEdDirect StrongEdEven StrongEdOdd StrongInvariant WallInvariant.
Import List PeanoNat Lia.

Module StrongEdLoose.
Notation mtm := WallInvariant.WallInvariant.mtm.

Lemma strong_ed_loose n bs :
 (length bs+3=n)%nat -> WallInvariant.WallInvariant.marked 1 bs ->
 exists c, WallInvariant.WallInvariant.Ed n bs -[mtm]->+ c /\ StrongInvariant.StrongInvariant.strong c.
Proof.
 intros Hn Hmark.
 destruct (mod2 (length bs)) as [a Ha|a Ha].
 - destruct (mod2 a) as [b Hb|b Hb].
   + apply (StrongEdEven.StrongEdEven.Ed_even_strong n bs b); try lia; exact Hmark.
   + apply (StrongEdOdd.StrongEdOdd.strong_ed_odd n bs b); try lia; exact Hmark.
 - apply (StrongEdDirect.StrongEdDirect.Ed_direct_strong n bs (a+1)); try lia; exact Hmark.
Qed.

End StrongEdLoose.
End StrongEdLoose.

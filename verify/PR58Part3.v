From BusyCoq Require Import PR58Part1 PR58Part2.


Module EdEvenOrbit.
(* Two wall steps from an even wall with a displaced terminal digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2.
Import PhaseEd OddImage CounterBits CounterFinish CounterRules.
Import MarkerArithmetic WallInvariant CDPasses.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdEvenOrbit.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope nat.

Lemma first_mass_bounds n v width k :
 0<v -> v*2+2<=n -> width<=n -> k<2^width ->
 2^width<=OddImage.OddImage.first_mass n v /\
 OddImage.OddImage.first_mass n v+k<2^(n+v*5+1).
Proof.

 intros Hv Hn Hw Hk.
 destruct (OddImage.OddImage.first_fuel_bounds n (v*2) ltac:(lia)) as [He Hf].
 assert (Hscale:2^(v*2)*4<=2^n).
 { pose proof (Nat.pow_le_mono_r 2 (v*2+2) n ltac:(lia) Hn) as H.
   rewrite Nat.pow_add_r in H. cbn [Nat.pow] in H. exact H. }
 assert (Hpositive:0<2^(v*2)).
 { pose proof (Nat.pow_nonzero 2 (v*2) ltac:(lia)); lia. }
 assert (Hbase:2^n<=2*OddImage.OddImage.first_fuel n (v*2)+1) by nia.
 assert (Hpow:0<2^(v*5-1)).
 { pose proof (Nat.pow_nonzero 2 (v*5-1) ltac:(lia)); lia. }
 assert (Hwidth:2^width<=2^n) by (apply Nat.pow_le_mono_r; lia).

 split.
 - unfold OddImage.OddImage.first_mass. nia.
 - pose proof (PhaseEd.PhaseEd.shifted_value_bound n (OddImage.OddImage.first_fuel n (v*2)) (v*5-1) Hf) as Hb.
   replace (n+1+(v*5-1)) with (n+v*5) in Hb by lia.
   unfold OddImage.OddImage.first_mass.
   assert (Hsmall:2^n<=2^(n+v*5)) by (apply Nat.pow_le_mono_r; lia).
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia.
Qed.

Lemma any_true bs : In true bs -> CDPasses.CDPasses.any bs=true.
Proof.
 induction bs as [|b bs IH]; cbn [CDPasses.CDPasses.any]; intro H; [contradiction|].
 destruct b; [reflexivity|]. apply IH. destruct H as [H|H]; [discriminate|exact H].
Qed.

Open Scope sym.
Notation ld := [1;1].
Notation da := [0;0;0;0;0].

Lemma normal_shift_odd width k u : (k<2^width)%nat ->
 WallInvariant.WallInvariant.normal (repeat false u++true::CounterFinish.CounterFinish.digits width k) *> 0inf =
 CounterRules.CounterRules.RC ((k*2+1)*2^u).
Proof.
 intro Hk. rewrite OddImage.OddImage.normal_app,OddImage.OddImage.normal_zeros.
 cbn [WallInvariant.WallInvariant.normal]. repeat rewrite Str_app_assoc.
 rewrite CounterFinish.CounterFinish.digits_normal by exact Hk.
 unfold CounterRules.CounterRules.RC. rewrite BinInc_mulpow2,BinInc_mul2add1. reflexivity.
Qed.

Lemma even_image_marker n v width k i q r :
 (0<v)%nat -> (v*2+2<=n)%nat -> (width<=n)%nat -> (k<2^width)%nat ->
 (i<v*5-1)%nat -> (i mod 2=1)%nat -> (r<2^i)%nat ->
 (k=(q*2+1)*2^i+r)%nat ->
 exists out,
 (length out+2<=n+v*5+2)%nat /\ WallInvariant.WallInvariant.marked 1 out /\
 WallInvariant.WallInvariant.O n (repeat false (v*2)++true::CounterFinish.CounterFinish.digits width k) -[mtm]->+
 WallInvariant.WallInvariant.Ed (n+v*5+2) out.
Proof.

 intros Hv Hn Hw Hk Hi Hodd Hr Hdecomp.
 destruct (first_mass_bounds n v width k Hv Hn Hw Hk) as [Hmin Hmax].
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
 { apply any_true. apply CounterBits.CounterBits.value_nonzero. rewrite CounterBits.CounterBits.digits_value by exact Hk.
   exact Hnonzero. }
 rewrite Hany in Hrun. cbn [CDPasses.CDPasses.terminal] in Hrun.

 exists out. split; [lia|]. split.
 - rewrite <-Hodd.
   apply (MarkerArithmetic.MarkerArithmetic.low_marker_preserved out k i q r (v*5-1)
     (2*OddImage.OddImage.first_fuel n (v*2)+1)); try lia.
   change (CounterBits.CounterBits.value out+2^length out=OddImage.OddImage.first_mass n v+k)%nat in Hval.
   exact Hval.
 - exact Hrun.
Qed.

Lemma Ed_even_valuation_image n bs b :
 (length bs=4*b)%nat -> (length bs+3<=n)%nat -> In true bs ->
 exists out,
 (length out+2<=n+35*b+17)%nat /\ WallInvariant.WallInvariant.marked 1 out /\
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

 destruct (even_image_marker (n+10*b+5) (5*b+2) n k (4*b+1) q
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
 rewrite normal_shift_odd by exact Hk.
 applys_eq Hstart; ut; st; simpl_rotate; reflexivity.
Qed.

End EdEvenOrbit.
End EdEvenOrbit.

Module EdOddOrbit.
(* Entry into the recursive odd-gap branch from a displaced terminal digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2.
Import PhaseEd OddImage OddFuel OddRecursion EdEvenOrbit.
Import CounterBits CounterFinish CounterRules WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdOddOrbit.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope nat.

Lemma first_fuel_half n u : u+2<=n ->
 2^n<=2*OddImage.OddImage.first_fuel n u+1.
Proof.
 intro Hn.
 destruct (OddImage.OddImage.first_fuel_bounds n u ltac:(lia)) as [He Hf].
 assert (Hscale:2^u*4<=2^n).
 { pose proof (Nat.pow_le_mono_r 2 (u+2) n ltac:(lia) Hn) as H.
   rewrite Nat.pow_add_r in H. cbn [Nat.pow] in H. exact H. }
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia.
Qed.

Lemma grown_first_lower n u width z : u+2<=n -> width<=n ->
 2^width-1<=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n u) z.
Proof.
 intros Hn Hw.
 pose proof (first_fuel_half n u Hn).
 assert (2^width<=2^n) by (apply Nat.pow_le_mono_r; lia).
 pose proof (Nat.pow_nonzero 2 z ltac:(lia)).
 unfold OddFuel.OddFuel.grown. nia.
Qed.

Lemma deficit_after_prime L k deficit u z :
 k+deficit+1=2^L -> 2^(u+1)-1<=k ->
 OddFuel.OddFuel.grown (k-(2^(u+1)-1)) z+
   (2*deficit+2^(u+2)-1)*2^z+1=2^(L+1+z).
Proof.
 intros Hleft Hprime.
 assert (Hp:0<2^(u+1)).
 { pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)); lia. }
 assert (Hz:0<2^z).
 { pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia. }
 assert (Hu:2^(u+2)=2^(u+1)*2).
 { replace (u+2) with ((u+1)+1) by lia.
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }
 assert (HL:2^(L+1+z)=2^L*2*2^z).
 { rewrite !Nat.pow_add_r. cbn [Nat.pow]. nia. }
 unfold OddFuel.OddFuel.grown. rewrite Hu,HL. nia.
Qed.

Open Scope sym.
Notation ld := [1;1].
Notation z3 := [0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Definition source_rank n bs := (2^n-PhaseEd.PhaseEd.fuel bs-3)%nat.
Definition initial_width n b := (n+35*b+34)%nat.
Definition initial_rank n b :=
 OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel (n+10*b+10) (10*b+9)) (25*b+23).

Lemma Ed_odd_valuation_entry n bs b :
 (length bs=4*b+2)%nat -> (length bs+3<=n)%nat -> In true bs ->
 WallInvariant.WallInvariant.Ed n bs -[mtm]->+
 CounterRules.CounterRules.LC (initial_width n b) (initial_rank n b) |>
 z3 *> WallInvariant.WallInvariant.normal (CounterFinish.CounterFinish.digits n (source_rank n bs)) *> 0inf.
Proof.

 intros Hlength Hn Hin.
 set (k:=source_rank n bs).
 assert (Hk:(k<2^n)%nat).
 { unfold k,source_rank. apply PhaseEd.PhaseEd.remaining_bound; exact Hn. }
 pose proof (OddRecursion.OddRecursion.initial_odd_entry (n+10*b+10) (5*b+4)
   (CounterFinish.CounterFinish.digits n k) ltac:(lia)) as Hodd.
 replace ((5*b+4)*2+1)%nat with (10*b+9)%nat in Hodd by lia.
 replace ((5*b+4)*5+3)%nat with (25*b+23)%nat in Hodd by lia.
 replace (n+10*b+10+1+(25*b+23))%nat with (initial_width n b) in Hodd by
   (unfold initial_width; lia).
 fold (initial_rank n b) in Hodd.
 eapply progress_trans; [|exact Hodd].

 pose proof (PhaseEd.PhaseEd.nonzero_counter_entry n bs Hn Hin) as Hentry.
 change (2^n-PhaseEd.PhaseEd.fuel bs-3)%nat with (source_rank n bs) in Hentry.
 fold k in Hentry.
 replace (length bs+1)%nat with ((b*2+1)*2+1)%nat in Hentry by lia.
 pose proof (PhaseEd.PhaseEd.gap2_odd_wall n k (b*2+1) Hk) as Hwall.
 assert (Hstart:WallInvariant.WallInvariant.Ed n bs -[mtm]->+
   (0inf <* <[1;1]) <* [0] {{A}}>
     ([1] *> ld^^(n+10*b+10) *> CounterRules.CounterRules.RC ((k*2+1)*2^(10*b+9)))).
 { replace (n+10*b+10)%nat with (n+1+((b*2+1)*5+4))%nat by lia.
   replace (10*b+9)%nat with ((b*2+1)*5+4)%nat by lia.
   eapply evstep_progress_trans; eassumption. }

 unfold WallInvariant.WallInvariant.O,WallInvariant.WallInvariant.wall.
 repeat rewrite Str_app_assoc.
 rewrite EdEvenOrbit.EdEvenOrbit.normal_shift_odd by exact Hk.
 applys_eq Hstart; ut; st; simpl_rotate; reflexivity.
Qed.

Lemma Ed_odd_entry_fuel n bs b :
 (length bs=4*b+2)%nat -> (length bs+3<=n)%nat ->
 (2^length (CounterFinish.CounterFinish.digits n (source_rank n bs))-1<=initial_rank n b)%nat /\
 (initial_rank n b<2^initial_width n b)%nat /\
 (initial_rank n b mod 2=1)%nat.
Proof.

 intros Hlength Hn.
 rewrite CounterFinish.CounterFinish.digits_length.
 unfold initial_rank,initial_width.
 split.
 - apply grown_first_lower; lia.
 - split.
   + pose proof (OddImage.OddImage.first_fuel_bounds (n+10*b+10) (10*b+9) ltac:(lia)) as [_ Hf].
     pose proof (OddFuel.OddFuel.grown_bound (n+10*b+10)
       (OddImage.OddImage.first_fuel (n+10*b+10) (10*b+9)) (25*b+23) Hf) as Hbound.
     replace (n+10*b+10+1+(25*b+23))%nat with (n+35*b+34)%nat in Hbound by lia.
     lia.
   + apply OddRecursion.OddRecursion.grown_odd. lia.
Qed.

Lemma source_even_marker n bs :
 (length bs+5<=n)%nat -> (length bs mod 2=0)%nat ->
 WallInvariant.WallInvariant.marked 0 (CounterFinish.CounterFinish.digits n (source_rank n bs)).
Proof.

 intros Hn Hpar.
 set (m:=length bs).
 set (d:=(n-m-5)%nat).
 assert (He:(n=m+5+d)%nat) by (unfold d,m; lia).
 pose proof (PhaseEd.PhaseEd.fuel_value bs) as Hfuel.
 pose proof (PhaseEd.PhaseEd.value_bound bs) as Hvalue.
 pose proof (PhaseEd.PhaseEd.fuel_fits n bs ltac:(lia)) as Hfits.
 fold m in Hfuel,Hvalue.
 assert (Hp:(0<2^m)%nat).
 { pose proof (Nat.pow_nonzero 2 m ltac:(lia)); lia. }
 assert (Hd:(0<2^d)%nat).
 { pose proof (Nat.pow_nonzero 2 d ltac:(lia)); lia. }
 assert (Hbig:(2^n=2^m*32*2^d)%nat).
 { rewrite He. rewrite !Nat.pow_add_r. cbn [Nat.pow]. nia. }
 assert (Hbit:(2^(m+4)=2^m*16)%nat).
 { rewrite Nat.pow_add_r. reflexivity. }

 pose proof (CounterBits.CounterBits.marked_remainder n (source_rank n bs) (m+4)
   (2^d-1) (10*2^m+2*PhaseEd.PhaseEd.value bs) ltac:(lia)) as Hmark.
 replace ((m+4) mod 2)%nat with 0%nat in Hmark by
   (rewrite Nat.add_mod by lia; unfold m; rewrite Hpar; reflexivity).
 apply Hmark.
 - rewrite Hbit. nia.
 - unfold source_rank. rewrite Hbig,Hbit in *. nia.
Qed.

End EdOddOrbit.
End EdOddOrbit.

Module CounterH.
(* Pairing contextual amplifier passes with a finite left counter.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import CounterRules CounterFinish WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterRules.CounterRules WallInvariant.WallInvariant.
Open Scope sym.

Module CounterH.
Notation h := [((A,[0]),(C,[0]))].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).

Lemma left_one len k :
 (1+k<2^len)%nat ->
 sideLR mtm (C,[0]) (A,[0])
   (LC len (1+k) <* [1]) (LC len k <* [1]).
Proof.
 intros Hk r.
 assert (H : (LC len (1+k)<*[1]) <{{C}} [0]*>r -[mtm]->+
   LC len (1+k) <| r) by esx.
 follow10 H. apply progress_evstep, left_counter. exact Hk.
Qed.

Lemma left_one_flip len k :
 (1+k<2^len)%nat ->
 sideRL (flip mtm) (C,[0]) (A,[0])
   (LC len (1+k) <* [1]) (LC len k <* [1]).
Proof.
 intros Hk r. exact (flip_progress mtm _ _ (left_one len k Hk r)).
Qed.

Lemma left_batch len k amount :
 (k+amount<2^len)%nat ->
 sideRLs (flip mtm) ([((C,[0]),(A,[0]))]^^amount)
   (LC len (k+amount)<*[1]) (LC len k<*[1]).
Proof.
 gen k. induction amount; intros k Hk.
 - rewrite Nat.add_0_r. constructor.
 - replace (k+S amount)%nat with (1+(k+amount))%nat by lia.
   cbn[lpow app]. econstructor.
   + apply left_one_flip. lia.
   + apply IHamount. lia.
Qed.

Lemma right_h_batch len k amount r r' :
 (k+amount<2^len)%nat -> sideRLs mtm (h^^amount) r r' ->
 LC len (k+amount) |> r -[mtm]->* LC len k |> r'.
Proof.
 intros Hk Hr.
 exact (sideRLs_concat_1 Hr (left_batch len k amount Hk)).
Qed.

Lemma right_h_finish n k r r' :
 (k<2^n)%nat -> sideRLs mtm (h^^(k+1)) r r' ->
 LC n k |> r -[mtm]->+
 (0inf<*<[1;1])<*[0] {{A}}> ([1]*>[1;1]^^n*>r').
Proof.

 intros Hk Hr. rewrite lpow_add in Hr.
 destruct (sideRLs_split Hr) as [middle [Hfirst Hlast]].
 eapply evstep_progress_trans.
 - replace k with (0+k)%nat at 1 by lia.
   apply right_h_batch; [exact Hk|exact Hfirst].
 - eapply progress_trans.
   + exact (sideRLs_1 _ _ _ _ _ Hlast (LC n 0<*[1])).
   + eapply progress_trans.
     * assert (H : (LC n 0<*[1]) <{{C}} [0]*>r' -[mtm]->+
         LC n 0 <| r') by esx. exact H.
     * apply CounterFinish.CounterFinish.return_wall.
Qed.

End CounterH.
End CounterH.

Module BlankPasses.
(* Exact pass counts on a blank right side.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses CounterRules CounterFinish CounterBits WallInvariant.
Import String List PeanoNat NArith Lia.
Import ListNotations.
Open Scope sym.

Module BlankPasses.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].
Notation h := [((A,[0]),(C,[0]))].
Definition shifted_counter n := BinInc c n.

Lemma ordinary_increment l r n:
 l {{A}}> b^^n *> a *> r -[mtm]->+
 l <{{B}} a^^n *> b *> r.
Proof. esx. Qed.
Lemma shifted_increment l r n:
 l {{C}}> c^^n *> a *> r -[mtm]->+
 l <{{B}} a^^n *> c *> r.
Proof. esx. Qed.

Lemma ordinary_step n:
 sideRLs mtm p (CounterRules.CounterRules.RC n) (CounterRules.CounterRules.RC (1+n)).
Proof.

 econstructor.
 2: constructor.
 unfold sideRL. intros l.
 change (l <* [] {{A}}> CounterRules.CounterRules.RC n -[mtm]->+ l <{{B}} [] *> CounterRules.CounterRules.RC (1+n)).
 unfold CounterRules.CounterRules.RC. apply RBinInc_spec.
 intros l0 r0 n0. cbn[Str_app BinaryCounter.d0 length repeat].
 apply ordinary_increment.
Qed.
Lemma shifted_step n:
 sideRLs mtm x (shifted_counter n) (shifted_counter (1+n)).
Proof.

 econstructor.
 2: constructor.
 unfold sideRL. intros l.
 change (l <* [] {{C}}> shifted_counter n -[mtm]->+
   l <{{B}} [] *> shifted_counter (1+n)).
 unfold shifted_counter. apply RBinInc_spec.
 intros l0 r0 n0. cbn[Str_app BinaryCounter.d0 length repeat].
 apply shifted_increment.
Qed.

Open Scope nat.
Lemma ordinary_blank n:
 sideRLs mtm (p^^n) 0inf (CounterRules.CounterRules.RC n).
Proof.

 induction n.
 - change (sideRLs mtm [] 0inf 0inf). constructor.
 - replace (S n) with (n+1) at 1 by lia. rewrite lpow_add.
   replace (S n) with (1+n) by lia.
   eapply sideRLs_trans.
   + exact IHn.
   + apply ordinary_step.
Qed.
Lemma shifted_blank n:
 sideRLs mtm (x^^n) 0inf (shifted_counter n).
Proof.

 induction n.
 - change (sideRLs mtm [] 0inf 0inf). constructor.
 - replace (S n) with (n+1) at 1 by lia. rewrite lpow_add.
   replace (S n) with (1+n) by lia.
   eapply sideRLs_trans.
   + exact IHn.
   + apply shifted_step.
Qed.

Lemma digits_shifted n v:
 v<2^n -> WallInvariant.WallInvariant.shifted (CounterFinish.CounterFinish.digits n v) *> 0inf=shifted_counter v.
Proof.

 gen v. induction n; intros v Hv.
 - cbn in Hv. assert (v=0) by lia. subst. reflexivity.
 - destruct (mod2 v); subst.
   + rewrite CounterFinish.CounterFinish.digits_even. cbn[WallInvariant.WallInvariant.shifted].
     rewrite Str_app_assoc,IHn by (cbn in Hv; lia).
     unfold shifted_counter. rewrite BinInc_mul2. reflexivity.
   + rewrite Nat.add_comm,CounterFinish.CounterFinish.digits_odd. cbn[WallInvariant.WallInvariant.shifted].
     rewrite Str_app_assoc,IHn by (cbn in Hv; lia).
     unfold shifted_counter. rewrite BinInc_mul2add1. reflexivity.
Qed.
Lemma shifted_counter_rotate n v:
 v<2^n -> shifted_counter v=([0;0;0;0]%sym) *> CounterRules.CounterRules.RC v.
Proof.

 intro H.
 rewrite <- (digits_shifted n v H), <- (CounterFinish.CounterFinish.digits_normal n v H).
 symmetry. apply CounterBits.CounterBits.shifted_normal.
Qed.

Lemma even_ones k n:
 sideRLs mtm (h^^k) (([1;1]%sym)^^n *> 0inf)
   (([1;1]%sym)^^n *> CounterRules.CounterRules.RC (k*2^n)).
Proof.

 eapply segRLs_sideRLs_concat.
 - apply LocalPasses.Mirrored.lds_Incs'.
 - apply ordinary_blank.
Qed.

End BlankPasses.
End BlankPasses.

Module EndpointClasses.
(* Classifying the numeric endpoints of the two terminal conversions.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses CounterH CounterRules CounterFinish CounterBits.
Import BlankPasses WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module EndpointClasses.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation one := [1].
Notation ld := [1;1].
Notation z := [0].
Notation lh := (0inf<*<[1;1]).
Notation h := [((A,[0]),(C,[0]))].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma coefficient_bound L T q :
 0<T -> 2*(T+q)<=2^L -> q*4+3<2^(L+1).
Proof. intros. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. Qed.

Lemma budget_positive L T q :
 0<T -> 2*(T+q)<=2^L -> 0<L.
Proof. intros. destruct L; [cbn in *; lia|lia]. Qed.

Lemma adjacent_marked n q s :
 s+1<n -> WallInvariant.WallInvariant.marked 1 (CounterFinish.CounterFinish.digits n ((q*4+3)*2^s)).
Proof.

 intro Hn.
 destruct (Nat.eq_dec (s mod 2) 1) as [Hs|Hs].
 - replace (q*4+3) with ((q*2+1)*2+1) by lia.
   apply CounterBits.CounterBits.marked_shift_odd; lia.
 - assert (H0:s mod 2=0) by
    (pose proof (Nat.mod_upper_bound s 2 ltac:(lia)); lia).
   assert (H1:(s+1) mod 2=1).
   { rewrite Nat.add_mod by lia. rewrite H0. reflexivity. }
   rewrite <-H1 at 1.
   apply (CounterBits.CounterBits.marked_remainder n ((q*4+3)*2^s) (s+1) q (2^s)).
   + exact Hn.
   + rewrite Nat.pow_add_r. cbn[Nat.pow].
     pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.

   + rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
Qed.

Lemma numeric_bound L T q s :
 0<T -> 2*(T+q)<=2^L -> (q*4+3)*2^s<2^(L+s+1).
Proof.

 intros HT HB. pose proof (coefficient_bound L T q HT HB).
 replace (L+s+1) with (L+1+s) by lia.
 rewrite Nat.pow_add_r.
 pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.
Qed.

Lemma shifted_numeric n v :
 v<2^n -> WallInvariant.WallInvariant.marked 1 (CounterFinish.CounterFinish.digits n v) ->
 WallInvariant.WallInvariant.invariant (lh<*z {{A}}> (ld^^(n+2) *> BlankPasses.BlankPasses.shifted_counter v)).
Proof.

 intros Hv Hm. rewrite <- (BlankPasses.BlankPasses.digits_shifted n v Hv).
 repeat rewrite <-Str_app_assoc.
 change (WallInvariant.WallInvariant.invariant (WallInvariant.WallInvariant.E (n+2) (CounterFinish.CounterFinish.digits n v))).
 apply WallInvariant.WallInvariant.InvE.
 - rewrite CounterFinish.CounterFinish.digits_length. lia.
 - exact Hm.
Qed.

Lemma shifted_endpoint L T q s :
 0<T -> 2*(T+q)<=2^L ->
 WallInvariant.WallInvariant.invariant (lh<*z {{A}}>
   (ld^^(L+s+3) *> BlankPasses.BlankPasses.shifted_counter ((q*4+3)*2^s))).
Proof.

 intros HT HB.
 replace (L+s+3) with ((L+s+1)+2) by lia.
 apply shifted_numeric.
 - apply numeric_bound with (T:=T); assumption.
 - apply adjacent_marked.
   pose proof (budget_positive L T q HT HB). lia.
Qed.

Lemma ordinary_endpoint L T q s :
 0<T -> 0<s -> 2*(T+q)<=2^L ->
 WallInvariant.WallInvariant.invariant (lh<*z {{A}}>
  (one *> ld^^(L+s+1) *> CounterRules.CounterRules.RC ((q*4+3)*2^s))).
Proof.

 intros HT Hs HB.
 apply CounterBits.CounterBits.numeric_even_value.
 - pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.
 - apply numeric_bound with (T:=T); assumption.
 - destruct s; [lia|].
   cbn[Nat.pow]. replace ((q*4+3)*(2*2^s)) with
    (((q*4+3)*2^s)*2) by nia.
   apply Nat.mod_mul; lia.
Qed.

Lemma even_word L s :
 one++ld^^L++ld++ld^^(s+1)++one=ld^^(L+s+3).
Proof.

 change (one^^1++(one^^2)^^L++one^^2++(one^^2)^^(s+1)++one^^1
  =(one^^2)^^(L+s+3)).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.
Lemma odd_word L s :
 one++ld^^L++ld++ld^^s=one++ld^^(L+s+1).
Proof.

 change (one++ld^^L++ld^^1++ld^^s=one++ld^^(L+s+1)).
 repeat rewrite <-lpow_add. f_equal. f_equal. lia.
Qed.

Lemma counter_shifted L k T q s r :
 k<2^L -> k+1=2*(T+q) -> 0<T ->
 sideRLs mtm (h^^(k+1)) r
  (ld *> ld^^(s+1) *> one *> BlankPasses.BlankPasses.shifted_counter ((q*4+3)*2^s)) ->
 exists out, CounterRules.CounterRules.LC L k |> r -[mtm]->+ out /\ WallInvariant.WallInvariant.invariant out.
Proof.

 intros Hk HE HT Hr.
 exists (lh<*z {{A}}> (ld^^(L+s+3) *> BlankPasses.BlankPasses.shifted_counter ((q*4+3)*2^s))).
 split.
 - pose proof (CounterH.CounterH.right_h_finish L k r _ Hk Hr) as H.
   repeat rewrite <-Str_app_assoc in H.
   rewrite <-app_assoc,<-app_assoc,<-app_assoc,even_word in H.
   exact H.
 - apply shifted_endpoint with (T:=T); [exact HT|lia].
Qed.

Lemma counter_ordinary L k T q s r :
 k<2^L -> k+1=2*(T+q) -> 0<T -> 0<s ->
 sideRLs mtm (h^^(k+1)) r
  (ld *> ld^^s *> CounterRules.CounterRules.RC ((q*4+3)*2^s)) ->
 exists out, CounterRules.CounterRules.LC L k |> r -[mtm]->+ out /\ WallInvariant.WallInvariant.invariant out.
Proof.

 intros Hk HE HT Hs Hr.
 exists (lh<*z {{A}}> (one *> ld^^(L+s+1) *> CounterRules.CounterRules.RC ((q*4+3)*2^s))).
 split.
 - pose proof (CounterH.CounterH.right_h_finish L k r _ Hk Hr) as H.
   repeat rewrite <-Str_app_assoc in H.
   rewrite <-app_assoc,<-app_assoc,odd_word,Str_app_assoc in H.
   exact H.
 - apply ordinary_endpoint with (T:=T); [exact HT|exact Hs|lia].
Qed.

End EndpointClasses.
End EndpointClasses.

Module OddDefectTail.
(* Terminal conversion of the odd defective wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses BoundaryRules CDPasses OddNormal.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module OddDefectTail.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation x := [((C,[]),(B,[]))].
Notation y := [((D,[]),(B,[]))].
Notation hx := [((C,[]),(C,[0]))].
Notation terminal_word := [0;0;0;0;0;0;0;1].
Notation q2 := [0;0;1].
Notation ones5 := [1;1;1;1;1].
Notation one := [1].
Notation ld := [1;1].
Notation three := [1;1;1].
Open Scope nat.

Lemma value_zero bs :
 CDPasses.CDPasses.value bs=0 -> bs=repeat false (length bs).
Proof.

 induction bs as [|b bs IH]; intro H; cbn[length repeat]; [reflexivity|].
 destruct b; cbn[CDPasses.CDPasses.value CDPasses.CDPasses.bitval] in H; [lia|].
 f_equal. apply IH. lia.
Qed.
Lemma value_full bs :
 CDPasses.CDPasses.value bs=2^length bs-1 -> bs=repeat true (length bs).
Proof.

 induction bs as [|b bs IH]; intro H; cbn[length repeat]; [reflexivity|].
 pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)).
 destruct b; cbn[CDPasses.CDPasses.value CDPasses.CDPasses.bitval length Nat.pow] in H.
 - f_equal. apply IH. nia.
 - lia.
Qed.
Lemma value_positive_any bs :
 0<CDPasses.CDPasses.value bs -> CDPasses.CDPasses.any bs=true.
Proof.

 induction bs as [|b bs IH]; intro H; cbn[CDPasses.CDPasses.value CDPasses.CDPasses.bitval] in H; [lia|].
 destruct b; cbn[CDPasses.CDPasses.any CDPasses.CDPasses.bitval] in *; [reflexivity|].
 apply IH. nia.
Qed.
Lemma third_zeros n : CDPasses.CDPasses.third (repeat false n)=a^^n.
Proof. induction n; [reflexivity|]. change (a++CDPasses.CDPasses.third(repeat false n)=a++a^^n). now rewrite IHn. Qed.
Lemma fourth_ones n : CDPasses.CDPasses.fourth (repeat true n)=c^^n.
Proof. induction n; [reflexivity|]. change (c++CDPasses.CDPasses.fourth(repeat true n)=c++c^^n). now rewrite IHn. Qed.

Lemma tail_five:
 sideRLs mtm (CDPasses.CDPasses.mass true 5) (terminal_word *> 0inf)
   (c^^2 *> q2 *> 0inf).
Proof. unfold CDPasses.CDPasses.mass. cbn[lpow]. esc. Qed.

Lemma prime_positive bs :
 0<CDPasses.CDPasses.value bs ->
 sideRLs mtm (x^^(6*2^length bs-CDPasses.CDPasses.value bs-1))
  (CDPasses.CDPasses.third bs *> terminal_word *> 0inf)
  (c^^(length bs+2) *> q2 *> 0inf).
Proof.

 intro Hvpos.
 pose proof (CDPasses.CDPasses.value_bound bs) as Hvbound.
 assert (Hp:0<2^length bs).
 { pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)); lia. }
 assert (Hn:2^length bs<=6*2^length bs-CDPasses.CDPasses.value bs-1) by nia.
 destruct (CDPasses.CDPasses.mass_digits bs false (6*2^length bs-CDPasses.CDPasses.value bs-1) Hn)
  as [low [carry [Hlen [Hval [Hcarry Hseg]]]]].
 pose proof (CDPasses.CDPasses.value_bound low) as Hlowbound.
 rewrite Hlen in Hlowbound.
 assert (Hfive:carry=5) by nia. subst carry.
 assert (Hfull:CDPasses.CDPasses.value low=2^length low-1) by (rewrite Hlen; nia).

 apply value_full in Hfull.
 rewrite Hfull,Hlen,fourth_ones in Hseg.
 unfold CDPasses.CDPasses.mass at 1 in Hseg.
 rewrite Bool.orb_false_l,value_positive_any in Hseg by exact Hvpos.
 rewrite lpow_add,Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - exact Hseg.
 - apply tail_five.
Qed.

Lemma prime_zero bs :
 CDPasses.CDPasses.value bs=0 ->
 sideRLs mtm (x^^(2^(length bs+1)-1))
  (CDPasses.CDPasses.third bs *> terminal_word *> 0inf)
  (c^^(length bs+1) *> q2 *> 0inf).
Proof.

 intro Hv.
 pose proof (value_zero bs Hv) as E.
 assert (Ht:CDPasses.CDPasses.third bs=a^^length bs).
 { rewrite E,third_zeros,repeat_length. reflexivity. }
 rewrite Ht.
 replace (terminal_word *> 0inf) with (a *> q2 *> 0inf) by reflexivity.
 rewrite <-Str_app_assoc.
 replace (a^^length bs++a) with (a^^(length bs+1)) by
  (rewrite lpow_add; cbn[lpow]; rewrite app_nil_r; reflexivity).
 eapply @segRLs_sideRLs_concat with (ls2:=[]).
 - pose proof (BoundaryRules.BoundaryRules.c_fill_zeros 0 (length bs+1)) as H.
   cbn[Nat.add Nat.mul lpow] in H. rewrite Nat.add_0_r in H.

   rewrite lpow_add in H. cbn[lpow] in H. rewrite app_nil_r in H. exact H.
 - constructor.
Qed.

Lemma final_x:
 sideRLs mtm hx (q2 *> 0inf) (three *> 0inf).
Proof. esc. Qed.
Lemma convert_tail g:
 sideRLs mtm hx (c^^g *> q2 *> 0inf)
  (ones5^^g *> three *> 0inf).
Proof.

 eapply segRLs_sideRLs_concat.
 - apply BoundaryRules.BoundaryRules.conversion_digits.
 - apply final_x.
Qed.

Lemma positive_exit bs :
 0<CDPasses.CDPasses.value bs ->
 sideRLs mtm (x^^(6*2^length bs-CDPasses.CDPasses.value bs-1)++hx)
  (CDPasses.CDPasses.third bs *> terminal_word *> 0inf)
  (ones5^^(length bs+2) *> three *> 0inf).
Proof.

 intro H. eapply sideRLs_trans.
 - apply prime_positive; exact H.
 - apply convert_tail.
Qed.
Lemma zero_exit bs :
 CDPasses.CDPasses.value bs=0 ->
 sideRLs mtm (x^^(2^(length bs+1)-1)++hx)
  (CDPasses.CDPasses.third bs *> terminal_word *> 0inf)
  (ones5^^(length bs+1) *> three *> 0inf).
Proof.

 intro H. eapply sideRLs_trans.
 - apply prime_zero; exact H.
 - apply convert_tail.
Qed.

Definition demand bs :=
 if Nat.eqb (CDPasses.CDPasses.value bs) 0 then 2^(length bs+1)
 else 6*2^length bs-CDPasses.CDPasses.value bs.
Definition converted_digits bs :=
 if Nat.eqb (CDPasses.CDPasses.value bs) 0 then length bs+1 else length bs+2.

Lemma prime bs :
 sideRLs mtm (x^^(demand bs-1))
  (CDPasses.CDPasses.third bs *> terminal_word *> 0inf)
  (c^^converted_digits bs *> q2 *> 0inf).
Proof.

 unfold demand,converted_digits.
 destruct (Nat.eqb_spec (CDPasses.CDPasses.value bs) 0).
 - apply prime_zero; exact e.
 - apply prime_positive; lia.
Qed.

Notation h := [((A,[0]%sym),(C,[0]%sym))].
Lemma odd_terminal_reduction bs q r' :
 sideRLs mtm (h^^(1+q*2))
  (ones5^^converted_digits bs *> three *> 0inf) r' ->
 sideRLs mtm (h^^((demand bs-1)*2+(1+q)))
  (one *> CDPasses.CDPasses.third bs *> terminal_word *> 0inf) (ld *> r').
Proof.

 intro H. rewrite lpow_add.
 eapply @sideRLs_trans with
   (r2:=one *> c^^converted_digits bs *> q2 *> 0inf).
 - eapply segRLs_sideRLs_concat.
   + apply OddNormal.OddNormal.one_pairs.
   + apply prime.
 - eapply segRLs_sideRLs_concat.
   + apply OddNormal.OddNormal.one_expand.
   + eapply sideRLs_trans.
     * apply convert_tail.
     * exact H.
Qed.

End OddDefectTail.
End OddDefectTail.

Module OddDefectFinish.
(* Numeric endpoints of the defective terminal conversion.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses OddNormal OddDefectTail BlankPasses CDPasses CounterRules WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module OddDefectFinish.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation z3 := [0;0;0].
Notation one := [1].
Notation ld := [1;1].
Notation three := [1;1;1].
Notation ones5 := [1;1;1;1;1].
Notation terminal_word := [0;0;0;0;0;0;0;1].
Notation h := [((A,[0]),(C,[0]))].
Notation x := [((C,[]),(B,[]))].
Open Scope nat.

Lemma demand_positive bs : 0<OddDefectTail.OddDefectTail.demand bs.
Proof.
 unfold OddDefectTail.OddDefectTail.demand.
 pose proof (CDPasses.CDPasses.value_bound bs).
 pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)).
 destruct (Nat.eqb (CDPasses.CDPasses.value bs) 0).
 - rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
 - nia.
Qed.

Lemma ones_even w :
 ones5^^(w*2)++three = ld^^(w*5+1)++one.
Proof.
 change ((one^^5)^^(w*2)++one^^3 = (one^^2)^^(w*5+1)++one^^1).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.
Lemma ones_odd w :
 ones5^^(w*2+1)++three = ld^^(w*5+4).
Proof.
 change ((one^^5)^^(w*2+1)++one^^3 = (one^^2)^^(w*5+4)).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.

Lemma odd_ones k n :
 sideRLs mtm (h^^k) (ld^^(n+1) *> one *> 0inf)
  (ld^^(n+1) *> one *> BlankPasses.BlankPasses.shifted_counter (k*2^n)).
Proof.
 eapply segRLs_sideRLs_concat.
 - apply LocalPasses.Mirrored.lds_Incs.
 - replace (k*2^(n+1)) with ((k*2^n)*2) by
    (rewrite Nat.pow_add_r; cbn[Nat.pow]; nia).
   eapply segRLs_sideRLs_concat.
   + apply OddNormal.OddNormal.one_pairs.
   + apply BlankPasses.BlankPasses.shifted_blank.
Qed.

Lemma finish_even bs w q :
 OddDefectTail.OddDefectTail.converted_digits bs=w*2 ->
 sideRLs mtm (h^^(2*(OddDefectTail.OddDefectTail.demand bs+q)))
   (one *> CDPasses.CDPasses.third bs *> terminal_word *> 0inf)
   (ld *> ld^^(w*5+1) *> one *>
      BlankPasses.BlankPasses.shifted_counter ((q*4+3)*2^(w*5))).
Proof.
 intro Hg.
 pose proof (demand_positive bs).
 replace (2*(OddDefectTail.OddDefectTail.demand bs+q)) with
   ((OddDefectTail.OddDefectTail.demand bs-1)*2+(1+(1+q*2))) by lia.
 apply OddDefectTail.OddDefectTail.odd_terminal_reduction.
 replace (1+(1+q*2)*2) with (q*4+3) by lia.
 rewrite Hg,<-Str_app_assoc,ones_even,Str_app_assoc.
 apply odd_ones.
Qed.

Lemma finish_odd bs w q :
 OddDefectTail.OddDefectTail.converted_digits bs=w*2+1 ->
 sideRLs mtm (h^^(2*(OddDefectTail.OddDefectTail.demand bs+q)))
   (one *> CDPasses.CDPasses.third bs *> terminal_word *> 0inf)
   (ld *> ld^^(w*5+4) *> CounterRules.CounterRules.RC ((q*4+3)*2^(w*5+4))).
Proof.
 intro Hg.
 pose proof (demand_positive bs).
 replace (2*(OddDefectTail.OddDefectTail.demand bs+q)) with
   ((OddDefectTail.OddDefectTail.demand bs-1)*2+(1+(1+q*2))) by lia.
 apply OddDefectTail.OddDefectTail.odd_terminal_reduction.
 replace (1+(1+q*2)*2) with (q*4+3) by lia.
 rewrite Hg,<-Str_app_assoc,ones_odd.
 apply BlankPasses.BlankPasses.even_ones.
Qed.


Lemma third_normal bs : z3++WallInvariant.WallInvariant.normal bs=CDPasses.CDPasses.third bs++z3.
Proof.
 induction bs as [|b bs IH]; [reflexivity|].
 destruct b; cbn[WallInvariant.WallInvariant.normal CDPasses.CDPasses.third CDPasses.CDPasses.third_digit app] in *;
 rewrite <-IH; reflexivity.
Qed.
Lemma third_normal_side bs :
 z3 *> WallInvariant.WallInvariant.normal bs *> c *> 0inf=CDPasses.CDPasses.third bs *> terminal_word *> 0inf.
Proof.
 rewrite <-Str_app_assoc,third_normal,Str_app_assoc. reflexivity.
Qed.
Lemma prefix_even u : one^^(5*(u*2)+1)=ld^^(u*5)++one.
Proof.
 change (one^^(5*(u*2)+1)=(one^^2)^^(u*5)++one^^1).
 rewrite <-lpow_mul,<-lpow_add. f_equal. lia.
Qed.

Lemma first_even_reduction u k bs r' :
 sideRLs mtm (h^^((1+k*2)*2^(u*5)))
   (one *> CDPasses.CDPasses.third bs *> terminal_word *> 0inf) r' ->
 sideRLs mtm (h^^((2^(u*2)-1)*2+(1+k)))
   (one *> a^^(u*2) *> b *> WallInvariant.WallInvariant.normal bs *> c *> 0inf)
   (ld *> ld^^(u*5) *> r').
Proof.
 intro H. apply OddNormal.OddNormal.odd_first_reduction.
 rewrite prefix_even,Str_app_assoc,third_normal_side.
 eapply segRLs_sideRLs_concat.
 - apply LocalPasses.Mirrored.lds_Incs.
 - exact H.
Qed.


End OddDefectFinish.
End OddDefectFinish.

Module TightTail.
(* The terminal conversion in a tight displaced-digit wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses BoundaryRules.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module TightTail.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation tail := [0;0;0;1;0;0;1;0].
Notation ones := [1;1;1;1;1;1;1].
Notation xp := [((C,[]),(C,[0]))].
Notation yp := [((D,[]),(C,[0]))].

Lemma terminal_C : segRLs mtm xp [] tail ones.
Proof.
 apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
Qed.

Lemma terminal_D : segRLs mtm yp [] tail ones.
Proof.
 apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
Qed.

End TightTail.
End TightTail.

Module TightPrimer.
(* First special return at the terminal of a tight displaced-digit wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses CDPasses BoundaryRules TightTail OddNormal.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module TightPrimer.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation d := [0;0;0;1;0].
Notation one := [1].
Notation ld := [1;1].
Notation ones5 := [1;1;1;1;1].
Notation ones7 := [1;1;1;1;1;1;1].
Notation tail := [0;0;0;1;0;0;1;0].
Notation x := [((C,[]),(B,[]))].
Notation y := [((D,[]),(B,[]))].
Notation hx := [((C,[]),(C,[0]))].
Notation hy := [((D,[]),(C,[0]))].
Notation h := [((A,[0]),(C,[0]))].

Definition special (old:bool) : list (DH0*DH0) := if old then hy else hx.
Definition departure (old:bool) (n:nat) : list (DH0*DH0) :=
 match n with
 | O => special old
 | S k => (if old then y else x) ++ x^^k ++ hx
 end.
Open Scope nat.

Lemma departure_positive old n : n<>0 ->
 departure old n=CDPasses.CDPasses.mass old n++hx.
Proof. destruct n; [lia|]. intro H. destruct old; cbn[departure CDPasses.CDPasses.mass Nat.sub lpow]; rewrite ?Nat.sub_0_r; reflexivity. Qed.
Lemma departure_false n : departure false n=x^^n++hx.
Proof. destruct n; reflexivity. Qed.

Lemma conversion_digit : segRLs mtm hx hx c ones5.
Proof. esc. Qed.

Lemma digit_exit k old bit :
 segRLs mtm (departure old ((k+1)*2-CDPasses.CDPasses.bitval bit-1))
   (departure (orb old bit) k) (CDPasses.CDPasses.third_digit bit) ones5.
Proof.

 destruct k as [|k].
 - destruct old,bit; cbn[departure special CDPasses.CDPasses.bitval CDPasses.CDPasses.third_digit orb lpow]; esc.
 - rewrite departure_positive by
    (destruct bit; cbn[CDPasses.CDPasses.bitval]; lia).
   rewrite departure_positive by lia.
   eapply segRLs_trans.
   2: apply conversion_digit.
   destruct bit.
   + cbn[CDPasses.CDPasses.bitval CDPasses.CDPasses.third_digit orb].
     replace ((S k+1)*2-1-1) with (S k*2) by lia.
     apply CDPasses.CDPasses.mass_even; lia.
   + cbn[CDPasses.CDPasses.bitval CDPasses.CDPasses.third_digit orb].
     replace ((S k+1)*2-0-1) with (1+S k*2) by lia.

     pose proof (CDPasses.CDPasses.mass_odd (S k) old false ltac:(lia)) as H.
     cbn[CDPasses.CDPasses.bitval CDPasses.CDPasses.third_digit CDPasses.CDPasses.fourth_digit negb] in H.
     rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma digits_exit bs old :
 segRLs mtm (departure old (2^length bs-CDPasses.CDPasses.value bs-1))
  (special (orb old (CDPasses.CDPasses.any bs))) (CDPasses.CDPasses.third bs) (ones5^^length bs).
Proof.

 gen old. induction bs as [|bit bs IH]; intro old.
 - cbn[CDPasses.CDPasses.third CDPasses.CDPasses.value CDPasses.CDPasses.any length Nat.pow departure].
   replace (orb old false) with old by (destruct old; reflexivity).
   apply segRLs_nil.
 - pose proof (CDPasses.CDPasses.value_bound bs) as Hv.
   cbn[CDPasses.CDPasses.third CDPasses.CDPasses.value CDPasses.CDPasses.any length Nat.pow lpow].
   replace (2*2^length bs-(CDPasses.CDPasses.bitval bit+2*CDPasses.CDPasses.value bs)-1)
    with (((2^length bs-CDPasses.CDPasses.value bs-1)+1)*2-CDPasses.CDPasses.bitval bit-1)
    by (destruct bit; cbn[CDPasses.CDPasses.bitval]; nia).
   replace (orb old (orb bit (CDPasses.CDPasses.any bs)))
    with (orb (orb old bit) (CDPasses.CDPasses.any bs)) by (destruct old,bit; reflexivity).

   eapply segRLs_concat.
   + apply digit_exit.
   + apply IH.
Qed.

Lemma terminal old : segRLs mtm (special old) [] tail ones7.
Proof.

 destruct old; unfold special.
 - apply TightTail.TightTail.terminal_D.
 - apply TightTail.TightTail.terminal_C.
Qed.

Lemma exit_side bs old :
 sideRLs mtm (departure old (2^length bs-CDPasses.CDPasses.value bs-1))
  (CDPasses.CDPasses.third bs *> tail *> 0inf) (ones5^^length bs *> ones7 *> 0inf).
Proof.

 eapply segRLs_sideRLs_concat.
 - apply digits_exit.
 - eapply segRLs_sideRLs_concat.
   + apply terminal.
   + constructor.
Qed.

Lemma exit_C bs :
 sideRLs mtm (x^^(2^length bs-CDPasses.CDPasses.value bs-1)++hx)
  (CDPasses.CDPasses.third bs *> tail *> 0inf) (ones5^^length bs *> ones7 *> 0inf).
Proof. rewrite <-departure_false. apply exit_side. Qed.

Definition demand bs := 2^length bs-CDPasses.CDPasses.value bs.

Lemma one_sequence k q :
 segRLs mtm (h^^(k*2+(1+q))) (x^^k++hx++h^^(1+q*2)) one ld.
Proof.

 rewrite lpow_add.
 eapply segRLs_trans.
 - apply OddNormal.OddNormal.one_pairs.
 - apply OddNormal.OddNormal.one_expand.
Qed.

Lemma odd_reduction bs q r' :
 sideRLs mtm (h^^(1+q*2)) (ones5^^length bs *> ones7 *> 0inf) r' ->
 sideRLs mtm (h^^((demand bs-1)*2+(1+q)))
  (one *> CDPasses.CDPasses.third bs *> tail *> 0inf) (ld *> r').
Proof.

 intro H.
 eapply segRLs_sideRLs_concat.
 - apply one_sequence.
 - rewrite app_assoc.
   eapply sideRLs_trans.
   + apply exit_C.
   + exact H.
Qed.

End TightPrimer.
End TightPrimer.

Module TightFinish.
(* Numeric endpoints after the tight-terminal conversion.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses TightPrimer OddDefectFinish BlankPasses CDPasses CounterRules.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module TightFinish.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation one := [1].
Notation ld := [1;1].
Notation ones5 := [1;1;1;1;1].
Notation ones7 := [1;1;1;1;1;1;1].
Notation tail := [0;0;0;1;0;0;1;0].
Notation h := [((A,[0]),(C,[0]))].
Open Scope nat.

Lemma demand_positive bs : 0<TightPrimer.TightPrimer.demand bs.
Proof. unfold TightPrimer.TightPrimer.demand. pose proof (CDPasses.CDPasses.value_bound bs). lia. Qed.

Lemma ones_even w :
 ones5^^(w*2)++ones7 = ld^^(w*5+3)++one.
Proof.
 change ((one^^5)^^(w*2)++one^^7 = (one^^2)^^(w*5+3)++one^^1).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.
Lemma ones_odd w :
 ones5^^(w*2+1)++ones7 = ld^^(w*5+6).
Proof.
 change ((one^^5)^^(w*2+1)++one^^7 = (one^^2)^^(w*5+6)).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.

Lemma finish_even bs w q :
 length bs=w*2 ->
 sideRLs mtm (h^^(2*(TightPrimer.TightPrimer.demand bs+q)))
  (one *> CDPasses.CDPasses.third bs *> tail *> 0inf)
  (ld *> ld^^(w*5+3) *> one *>
   BlankPasses.BlankPasses.shifted_counter ((q*4+3)*2^(w*5+2))).
Proof.
 intro Hg. pose proof (demand_positive bs).
 replace (2*(TightPrimer.TightPrimer.demand bs+q)) with
  ((TightPrimer.TightPrimer.demand bs-1)*2+(1+(1+q*2))) by lia.
 apply TightPrimer.TightPrimer.odd_reduction.
 replace (1+(1+q*2)*2) with (q*4+3) by lia.
 rewrite Hg,<-Str_app_assoc,ones_even,Str_app_assoc.
 replace (w*5+3) with ((w*5+2)+1) by lia.
 apply OddDefectFinish.OddDefectFinish.odd_ones.
Qed.

Lemma finish_odd bs w q :
 length bs=w*2+1 ->
 sideRLs mtm (h^^(2*(TightPrimer.TightPrimer.demand bs+q)))
  (one *> CDPasses.CDPasses.third bs *> tail *> 0inf)
  (ld *> ld^^(w*5+6) *> CounterRules.CounterRules.RC ((q*4+3)*2^(w*5+6))).
Proof.
 intro Hg. pose proof (demand_positive bs).
 replace (2*(TightPrimer.TightPrimer.demand bs+q)) with
  ((TightPrimer.TightPrimer.demand bs-1)*2+(1+(1+q*2))) by lia.
 apply TightPrimer.TightPrimer.odd_reduction.
 replace (1+(1+q*2)*2) with (q*4+3) by lia.
 rewrite Hg,<-Str_app_assoc,ones_odd.
 apply BlankPasses.BlankPasses.even_ones.
Qed.

End TightFinish.
End TightFinish.

Module TerminalClosure.
(* Closing either terminal phase from an odd finite counter budget.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses CounterRules CounterH CDPasses EndpointClasses WallInvariant BlankPasses.
Import OddDefectTail OddDefectFinish TightPrimer TightFinish.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module TerminalClosure.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation one := [1].

Notation ld := [1;1].
Notation z := [0].
Notation lh := (0inf<*<[1;1]).
Notation defect := [0;0;0;0;0;0;0;1].
Notation tight := [0;0;0;1;0;0;1;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma split_budget k T :
 k mod 2=1 -> 2*T<=k+1 -> exists q, k+1=2*(T+q).
Proof.

 intros Ho Hb. destruct (mod2 k) as [j He|j He]; subst k.
 - rewrite Nat.mod_mul in Ho by lia. discriminate.
 - exists (j+1-T). lia.
Qed.

Lemma defect_counter L k bs :
 k<2^L -> k mod 2=1 -> 2*OddDefectTail.OddDefectTail.demand bs<=k+1 ->
 exists out,
  CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third bs *> defect *> 0inf -[mtm]->+ out /\
  WallInvariant.WallInvariant.invariant out.
Proof.

 intros Hk Ho Hb.
 destruct (split_budget k (OddDefectTail.OddDefectTail.demand bs) Ho Hb) as [q HE].
 destruct (mod2 (OddDefectTail.OddDefectTail.converted_digits bs)) as [w Hg|w Hg].
 - eapply EndpointClasses.EndpointClasses.counter_shifted with (T:=OddDefectTail.OddDefectTail.demand bs) (q:=q) (s:=w*5).
   + exact Hk.
   + exact HE.
   + apply OddDefectFinish.OddDefectFinish.demand_positive.
   + rewrite HE. apply OddDefectFinish.OddDefectFinish.finish_even. exact Hg.
 - eapply EndpointClasses.EndpointClasses.counter_ordinary with (T:=OddDefectTail.OddDefectTail.demand bs) (q:=q) (s:=w*5+4).
   + exact Hk.
   + exact HE.
   + apply OddDefectFinish.OddDefectFinish.demand_positive.
   + lia.
   + rewrite HE. apply OddDefectFinish.OddDefectFinish.finish_odd. lia.
Qed.

Lemma tight_counter L k bs :
 k<2^L -> k mod 2=1 -> 2*TightPrimer.TightPrimer.demand bs<=k+1 ->
 exists out,
  CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third bs *> tight *> 0inf -[mtm]->+ out /\
  WallInvariant.WallInvariant.invariant out.
Proof.

 intros Hk Ho Hb.
 destruct (split_budget k (TightPrimer.TightPrimer.demand bs) Ho Hb) as [q HE].
 destruct (mod2 (length bs)) as [w Hg|w Hg].
 - eapply EndpointClasses.EndpointClasses.counter_shifted with (T:=TightPrimer.TightPrimer.demand bs) (q:=q) (s:=w*5+2).
   + exact Hk.
   + exact HE.
   + apply TightFinish.TightFinish.demand_positive.
   + replace (w*5+2+1) with (w*5+3) by lia.
     rewrite HE. apply TightFinish.TightFinish.finish_even. exact Hg.
 - eapply EndpointClasses.EndpointClasses.counter_ordinary with (T:=TightPrimer.TightPrimer.demand bs) (q:=q) (s:=w*5+6).
   + exact Hk.
   + exact HE.
   + apply TightFinish.TightFinish.demand_positive.

   + lia.
   + rewrite HE. apply TightFinish.TightFinish.finish_odd. lia.
Qed.


Definition even_wall L s q : (Q*tape)%type :=
 lh<*z {{A}}> (ld^^(L+s+3) *> BlankPasses.BlankPasses.shifted_counter ((q*4+3)*2^s)).
Definition odd_wall L s q : (Q*tape)%type :=
 lh<*z {{A}}> (one *> ld^^(L+s+1) *> CounterRules.CounterRules.RC ((q*4+3)*2^s)).

Lemma counter_shifted_exact L k q s r :
 k<2^L ->
 sideRLs mtm ([((A,[0]%sym),(C,[0]%sym))]^^(k+1)) r
  (ld *> ld^^(s+1) *> one *> BlankPasses.BlankPasses.shifted_counter ((q*4+3)*2^s)) ->
 CounterRules.CounterRules.LC L k |> r -[mtm]->+ even_wall L s q.
Proof.

 intros Hk Hr. unfold even_wall.
 pose proof (CounterH.CounterH.right_h_finish L k r _ Hk Hr) as H.
 repeat rewrite <-Str_app_assoc in H.
 rewrite <-app_assoc,<-app_assoc,<-app_assoc,EndpointClasses.EndpointClasses.even_word in H. exact H.
Qed.

Lemma counter_ordinary_exact L k q s r :
 k<2^L ->
 sideRLs mtm ([((A,[0]%sym),(C,[0]%sym))]^^(k+1)) r
  (ld *> ld^^s *> CounterRules.CounterRules.RC ((q*4+3)*2^s)) ->
 CounterRules.CounterRules.LC L k |> r -[mtm]->+ odd_wall L s q.
Proof.

 intros Hk Hr. unfold odd_wall.
 pose proof (CounterH.CounterH.right_h_finish L k r _ Hk Hr) as H.
 repeat rewrite <-Str_app_assoc in H.
 rewrite <-app_assoc,<-app_assoc,EndpointClasses.EndpointClasses.odd_word,Str_app_assoc in H. exact H.
Qed.

Lemma defect_counter_cases L k bs :
 k<2^L -> k mod 2=1 -> 2*OddDefectTail.OddDefectTail.demand bs<=k+1 ->
 exists q,
  k+1=2*(OddDefectTail.OddDefectTail.demand bs+q) /\ q*4+3<2^(L+1) /\
  ((exists w, OddDefectTail.OddDefectTail.converted_digits bs=w*2 /\
    CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third bs *> defect *> 0inf -[mtm]->+
      even_wall L (w*5) q /\ WallInvariant.WallInvariant.invariant (even_wall L (w*5) q)) \/
   (exists w, OddDefectTail.OddDefectTail.converted_digits bs=w*2+1 /\
    CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third bs *> defect *> 0inf -[mtm]->+
      odd_wall L (w*5+4) q)).
Proof.

 intros Hk Ho Hb.
 destruct (split_budget k (OddDefectTail.OddDefectTail.demand bs) Ho Hb) as [q HE].
 pose proof (OddDefectFinish.OddDefectFinish.demand_positive bs) as HT.
 assert (HB:2*(OddDefectTail.OddDefectTail.demand bs+q)<=2^L) by lia.
 exists q. split; [exact HE|]. split.
 - apply EndpointClasses.EndpointClasses.coefficient_bound with (T:=OddDefectTail.OddDefectTail.demand bs); assumption.
 - destruct (mod2 (OddDefectTail.OddDefectTail.converted_digits bs)) as [w Hg|w Hg].
   + left. exists w. split; [exact Hg|]. split.
     * apply counter_shifted_exact; [exact Hk|].
       rewrite HE. apply OddDefectFinish.OddDefectFinish.finish_even. exact Hg.

     * unfold even_wall. apply EndpointClasses.EndpointClasses.shifted_endpoint with (T:=OddDefectTail.OddDefectTail.demand bs); assumption.
   + right. exists w. split; [lia|].
     apply counter_ordinary_exact; [exact Hk|].
     rewrite HE. apply OddDefectFinish.OddDefectFinish.finish_odd. lia.
Qed.

Lemma tight_counter_cases L k bs :
 k<2^L -> k mod 2=1 -> 2*TightPrimer.TightPrimer.demand bs<=k+1 ->
 exists q,
  k+1=2*(TightPrimer.TightPrimer.demand bs+q) /\ q*4+3<2^(L+1) /\
  ((exists w, length bs=w*2 /\
    CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third bs *> tight *> 0inf -[mtm]->+
      even_wall L (w*5+2) q /\ WallInvariant.WallInvariant.invariant (even_wall L (w*5+2) q)) \/
   (exists w, length bs=w*2+1 /\
    CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third bs *> tight *> 0inf -[mtm]->+
      odd_wall L (w*5+6) q)).
Proof.

 intros Hk Ho Hb.
 destruct (split_budget k (TightPrimer.TightPrimer.demand bs) Ho Hb) as [q HE].
 pose proof (TightFinish.TightFinish.demand_positive bs) as HT.
 assert (HB:2*(TightPrimer.TightPrimer.demand bs+q)<=2^L) by lia.
 exists q. split; [exact HE|]. split.
 - apply EndpointClasses.EndpointClasses.coefficient_bound with (T:=TightPrimer.TightPrimer.demand bs); assumption.
 - destruct (mod2 (length bs)) as [w Hg|w Hg].
   + left. exists w. split; [exact Hg|]. split.
     * apply counter_shifted_exact; [exact Hk|].
       replace (w*5+2+1) with (w*5+3) by lia.
       rewrite HE. apply TightFinish.TightFinish.finish_even. exact Hg.

     * unfold even_wall. apply EndpointClasses.EndpointClasses.shifted_endpoint with (T:=TightPrimer.TightPrimer.demand bs); assumption.
   + right. exists w. split; [lia|].
     apply counter_ordinary_exact; [exact Hk|].
     rewrite HE. apply TightFinish.TightFinish.finish_odd. lia.
Qed.


End TerminalClosure.
End TerminalClosure.

Module OddAdjacent.
(* The next wall image when an ordinary counter begins with adjacent ones.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.BinaryCounter_v2.
Import OddFuel OddImage OddRecursion EdEvenOrbit EdOddOrbit.
Import CounterRules CounterFinish CounterBits CDPasses TerminalClosure WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module OddAdjacent.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation r4 := [1;0;0;0].
Notation ld := [1;1].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Definition odd_rank n v :=
 OddFuel.OddFuel.grown (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)-1) 1.
Definition odd_mass n v :=
 (2*OddImage.OddImage.first_fuel n (v*2+1)+1)*2^(v*5+4)-3.

Lemma odd_rank_bound n v : v*2+2<=n ->
 odd_rank n v+1<2^(n+v*5+6).
Proof.

 intro Hn.
 pose proof (OddFuel.OddFuel.grown_bound n (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)
   ltac:(apply OddImage.OddImage.first_fuel_bounds; lia)) as Hfirst.
 unfold odd_rank.
 replace (n+v*5+6) with ((n+1+(v*5+3))+1+1) by lia.
 apply OddFuel.OddFuel.grown_bound. lia.
Qed.

Lemma odd_mass_rank n v : odd_rank n v+1=odd_mass n v*2.
Proof.

 unfold odd_rank,odd_mass,OddFuel.OddFuel.grown.

 assert (Hz:8<=2^(v*5+3)).
 { change (2^3<=2^(v*5+3)). apply Nat.pow_le_mono_r; lia. }
 replace (v*5+4) with ((v*5+3)+1) by lia.
 rewrite (Nat.pow_add_r 2 (v*5+3) 1). cbn[Nat.pow]. nia.
Qed.

Lemma odd_entry n v bs : v*2+2<=n ->
 WallInvariant.WallInvariant.O n (repeat false (v*2+1)++true::true::bs) -[mtm]->+
 CounterRules.CounterRules.LC (n+v*5+6) (odd_rank n v) |> r4 *> WallInvariant.WallInvariant.normal bs *> 0inf.
Proof.

 intro Hn.
 set (L0:=n+1+(v*5+3)).
 set (k0:=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)).

 assert (Hk:k0+1<2^L0).
 { unfold k0,L0. apply OddFuel.OddFuel.grown_bound. apply OddImage.OddImage.first_fuel_bounds. lia. }

 assert (Hpos:1<=k0).
 { unfold k0,OddFuel.OddFuel.grown.

   assert (8<=2^(v*5+3)) by (change (2^3<=2^(v*5+3)); apply Nat.pow_le_mono_r; lia).
   nia. }

 assert (Hbefore:(k0-1)+(2^(0*2+1)-1)<2^L0) by
   (change ((k0-1)+1<2^L0); lia).
 pose proof (OddRecursion.OddRecursion.zero_even_step L0 (k0-1) 0 bs 0inf Hbefore) as Hsecond.
 cbn[Nat.mul Nat.add Nat.pow Nat.sub repeat app] in Hsecond.
 replace (k0-1+1) with k0 in Hsecond by lia.
 change (CounterRules.CounterRules.LC L0 k0 |> ([0;0;0]%sym) *> WallInvariant.WallInvariant.normal (true::bs) *> 0inf -[mtm]->+
   CounterRules.CounterRules.LC (L0+1+1) (OddFuel.OddFuel.grown (k0-1) 1) |> r4 *> WallInvariant.WallInvariant.normal bs *> 0inf) in Hsecond.
 unfold odd_rank.
 replace (n+v*5+6) with (L0+1+1) by (unfold L0; lia).
 fold k0.
 eapply progress_trans; [apply OddRecursion.OddRecursion.initial_odd_entry; exact Hn|exact Hsecond].
Qed.

Lemma odd_mass_bounds n v width q :
 v*2+3<=n -> width<=n -> q<2^width ->
 2^width<=odd_mass n v /\ odd_mass n v+q<2^(n+v*5+6).
Proof.

 intros Hn Hw Hq.
 pose proof (EdOddOrbit.EdOddOrbit.first_fuel_half n (v*2+1) ltac:(lia)) as Hfirst.

 assert (Hwidth:2^width<=2^n) by (apply Nat.pow_le_mono_r; lia).

 assert (Hz:16<=2^(v*5+4)) by (change (2^4<=2^(v*5+4)); apply Nat.pow_le_mono_r; lia).
 pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as Hpos.
 split.
 - unfold odd_mass. nia.
 - pose proof (odd_rank_bound n v ltac:(lia)) as Hb.
   rewrite odd_mass_rank in Hb.

   assert (Hqmass:q<odd_mass n v) by (unfold odd_mass; nia).
   lia.
Qed.

Lemma odd_image n v bs budget :
 v*2+2<=n -> 2^length bs<=odd_mass n v ->
 odd_mass n v+CDPasses.CDPasses.value bs<2^(length bs+budget) ->
 exists out,
 length out<length bs+budget /\
 CDPasses.CDPasses.value out+2^length out=odd_mass n v+CDPasses.CDPasses.value bs /\
 WallInvariant.WallInvariant.O n (repeat false (v*2+1)++true::true::bs) -[mtm]->+
 WallInvariant.WallInvariant.wall (ld^^(n+v*5+7)++CDPasses.CDPasses.fourth out++CDPasses.CDPasses.terminal (CDPasses.CDPasses.any bs)).
Proof.

 intros Hn Hmin Hmax.
 pose proof (odd_rank_bound n v Hn) as Hb.
 destruct (OddImage.OddImage.fuel_C_image (n+v*5+6) (odd_rank n v) (odd_mass n v)
   bs budget ltac:(lia) (odd_mass_rank n v) Hmin Hmax)
   as [out [Hlen [Hval Hrun]]].
 exists out. repeat split; try assumption.
 replace (n+v*5+7) with ((n+v*5+6)+1) by lia.
 eapply progress_trans; [apply odd_entry; exact Hn|exact Hrun].
Qed.

End OddAdjacent.
End OddAdjacent.

Module TerminalSuccessor.
(* Exact displaced-digit successors of the two ordinary terminal endpoints.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.BinaryCounter_v2.
Import OddImage OddAdjacent EdEvenOrbit CounterRules CounterFinish CounterBits CDPasses TerminalClosure WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module TerminalSuccessor.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope nat.

Lemma coefficient_parts L q : q*4+3<2^(L+1) ->
 0<L /\ q<2^L /\ q*2+1<2^L.
Proof.

 intro H. assert (HL:0<L) by (destruct L; cbn in H; lia).
 rewrite Nat.pow_add_r in H. cbn[Nat.pow] in H. repeat split; lia.
Qed.

Lemma first_coefficient n u : u+2<=n ->
 2^n+3<=2*OddImage.OddImage.first_fuel n u+1.
Proof.

 intro Hn. destruct (OddImage.OddImage.first_fuel_bounds n u ltac:(lia)) as [He Hb].

 assert (Hcap:2^(u+2)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r in Hcap. cbn[Nat.pow] in Hcap.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia.
Qed.

Lemma first_mass_lower n v : 0<v -> v*2+2<=n ->
 2^(n+v*5-1)<=OddImage.OddImage.first_mass n v.
Proof.

 intros Hv Hn. pose proof (first_coefficient n (v*2) Hn).
 unfold OddImage.OddImage.first_mass.
 replace (n+v*5-1) with (n+(v*5-1)) by lia.
 rewrite Nat.pow_add_r. nia.
Qed.

Lemma odd_mass_lower n v : v*2+3<=n ->
 2^(n+v*5+4)<=OddAdjacent.OddAdjacent.odd_mass n v.
Proof.

 intro Hn. pose proof (first_coefficient n (v*2+1) ltac:(lia)).
 unfold OddAdjacent.OddAdjacent.odd_mass.
 replace (n+v*5+4) with (n+(v*5+4)) by lia.
 rewrite (Nat.pow_add_r 2 n (v*5+4)).
 pose proof (Nat.pow_nonzero 2 (v*5+4) ltac:(lia)). nia.
Qed.

Lemma mass_length out base mass :
 CDPasses.CDPasses.value out+2^length out=mass -> 2^base<=mass -> mass<2^(base+2) ->
 length out=base \/ length out=base+1.
Proof.

 intros He Hlo Hhi. pose proof (CDPasses.CDPasses.value_bound out) as Hv.

 assert (Hlower:base<=length out).
 { destruct (Nat.le_gt_cases base (length out)); [assumption|].

   assert (2^(length out+1)<=2^base) by (apply Nat.pow_le_mono_r; lia).
   rewrite Nat.pow_add_r in H0. cbn[Nat.pow] in H0. lia. }

 assert (Hupper:length out<base+2).
 { destruct (Nat.lt_ge_cases (length out) (base+2)); [assumption|].

   assert (2^(base+2)<=2^length out) by (apply Nat.pow_le_mono_r; lia). lia. }
 lia.
Qed.

Lemma ordinary_source L s q : q*4+3<2^(L+1) ->
 TerminalClosure.TerminalClosure.odd_wall L s q=
 WallInvariant.WallInvariant.O (L+s+1) (repeat false s++true::CounterFinish.CounterFinish.digits L (q*2+1)).
Proof.

 intro H. destruct (coefficient_parts L q H) as [HL [Hq Htail]].
 unfold TerminalClosure.TerminalClosure.odd_wall,WallInvariant.WallInvariant.O,WallInvariant.WallInvariant.wall. repeat rewrite Str_app_assoc.
 rewrite EdEvenOrbit.EdEvenOrbit.normal_shift_odd by exact Htail.
 replace ((q*2+1)*2+1) with (q*4+3) by lia.
 simpl_rotate. reflexivity.
Qed.

Lemma ordinary_source_adjacent L s q : q*4+3<2^(L+1) ->
 TerminalClosure.TerminalClosure.odd_wall L s q=
 WallInvariant.WallInvariant.O (L+s+1) (repeat false s++true::true::CounterFinish.CounterFinish.digits L q).
Proof.

 intro H. destruct (coefficient_parts L q H) as [HL [Hq Htail]].

 assert (Htail':q*2+1<2^(S L)) by (cbn[Nat.pow]; lia).
 pose proof (EdEvenOrbit.EdEvenOrbit.normal_shift_odd (S L) (q*2+1) s Htail') as Henc.
 rewrite CounterFinish.CounterFinish.digits_odd in Henc.
 replace ((q*2+1)*2+1) with (q*4+3) in Henc by lia.
 unfold TerminalClosure.TerminalClosure.odd_wall,WallInvariant.WallInvariant.O,WallInvariant.WallInvariant.wall. repeat rewrite Str_app_assoc.
 rewrite Henc. simpl_rotate. reflexivity.
Qed.

Lemma ordinary_even_image L v q :
 0<v -> q*4+3<2^(L+1) ->
 exists out,
 (length out+3=L+v*7+3 \/ length out+2=L+v*7+3) /\
 2^(L+v*7)<=OddImage.OddImage.first_mass (L+v*2+1) v+(q*2+1) /\
 OddImage.OddImage.first_mass (L+v*2+1) v+(q*2+1)<2^(L+v*7+2) /\
 CDPasses.CDPasses.value out+2^length out=OddImage.OddImage.first_mass (L+v*2+1) v+(q*2+1) /\
 TerminalClosure.TerminalClosure.odd_wall L (v*2) q -[mtm]->+ WallInvariant.WallInvariant.Ed (L+v*7+3) out.
Proof.

 intros Hv Hcoef. destruct (coefficient_parts L q Hcoef) as [HL [Hq Htail]].
 set (n:=L+v*2+1).
 destruct (EdEvenOrbit.EdEvenOrbit.first_mass_bounds n v L (q*2+1) Hv ltac:(unfold n; lia)
   ltac:(unfold n; lia) Htail) as [Hmin Hmax].

 assert (Hlen:L+(n+v*5+1-L)=n+v*5+1) by (unfold n; lia).

 assert (Hvalue:CDPasses.CDPasses.value (CounterFinish.CounterFinish.digits L (q*2+1))=q*2+1).
 { change (CounterBits.CounterBits.value (CounterFinish.CounterFinish.digits L (q*2+1))=q*2+1). apply CounterBits.CounterBits.digits_value; exact Htail. }
 destruct (OddImage.OddImage.initial_even_image n v (CounterFinish.CounterFinish.digits L (q*2+1)) (n+v*5+1-L)
   Hv ltac:(unfold n; lia)
   ltac:(rewrite CounterFinish.CounterFinish.digits_length; exact Hmin)
   ltac:(rewrite CounterFinish.CounterFinish.digits_length,Hvalue,Hlen; exact Hmax))
   as [out [Hlength [Hmass Hrun]]].
 rewrite Hvalue in Hmass.

 assert (Hany:CDPasses.CDPasses.any (CounterFinish.CounterFinish.digits L (q*2+1))=true).
 { apply EdEvenOrbit.EdEvenOrbit.any_true,CounterBits.CounterBits.value_nonzero. rewrite CounterBits.CounterBits.digits_value by exact Htail. lia. }
 rewrite Hany in Hrun. cbn[CDPasses.CDPasses.terminal] in Hrun.

 assert (Hlow:2^(L+v*7)<=OddImage.OddImage.first_mass n v+(q*2+1)).
 { pose proof (first_mass_lower n v Hv ltac:(unfold n; lia)).
   replace (n+v*5-1) with (L+v*7) in H by (unfold n; lia). lia. }
 replace (n+v*5+1) with (L+v*7+2) in Hmax by (unfold n; lia).
 pose proof (mass_length out (L+v*7) _ Hmass Hlow Hmax) as Hd.
 exists out. repeat split; try assumption; try lia.
 rewrite ordinary_source by exact Hcoef. fold n.
 replace (L+v*7+3) with (n+v*5+2) by (unfold n; lia).
 exact Hrun.
Qed.

Lemma ordinary_odd_image L v q :
 0<q -> q*4+3<2^(L+1) ->
 exists out,
 (length out+3=L+v*7+9 \/ length out+2=L+v*7+9) /\
 2^(L+v*7+6)<=OddAdjacent.OddAdjacent.odd_mass (L+v*2+2) v+q /\
 OddAdjacent.OddAdjacent.odd_mass (L+v*2+2) v+q<2^(L+v*7+8) /\
 CDPasses.CDPasses.value out+2^length out=OddAdjacent.OddAdjacent.odd_mass (L+v*2+2) v+q /\
 TerminalClosure.TerminalClosure.odd_wall L (v*2+1) q -[mtm]->+ WallInvariant.WallInvariant.Ed (L+v*7+9) out.
Proof.

 intros Hqpos Hcoef. destruct (coefficient_parts L q Hcoef) as [HL [Hq Htail]].
 set (n:=L+v*2+2).
 destruct (OddAdjacent.OddAdjacent.odd_mass_bounds n v L q ltac:(unfold n; lia) ltac:(unfold n; lia) Hq)
   as [Hmin Hmax].

 assert (Hlen:L+(n+v*5+6-L)=n+v*5+6) by (unfold n; lia).

 assert (Hvalue:CDPasses.CDPasses.value (CounterFinish.CounterFinish.digits L q)=q).
 { change (CounterBits.CounterBits.value (CounterFinish.CounterFinish.digits L q)=q). apply CounterBits.CounterBits.digits_value; exact Hq. }
 destruct (OddAdjacent.OddAdjacent.odd_image n v (CounterFinish.CounterFinish.digits L q) (n+v*5+6-L)
   ltac:(unfold n; lia) ltac:(rewrite CounterFinish.CounterFinish.digits_length; exact Hmin)
   ltac:(rewrite CounterFinish.CounterFinish.digits_length,Hvalue,Hlen; exact Hmax))
   as [out [Hlength [Hmass Hrun]]].
 rewrite Hvalue in Hmass.

 assert (Hany:CDPasses.CDPasses.any (CounterFinish.CounterFinish.digits L q)=true).
 { apply EdEvenOrbit.EdEvenOrbit.any_true,CounterBits.CounterBits.value_nonzero. rewrite CounterBits.CounterBits.digits_value by exact Hq. lia. }
 rewrite Hany in Hrun. cbn[CDPasses.CDPasses.terminal] in Hrun.

 assert (Hlow:2^(L+v*7+6)<=OddAdjacent.OddAdjacent.odd_mass n v+q).
 { pose proof (odd_mass_lower n v ltac:(unfold n; lia)).
   replace (n+v*5+4) with (L+v*7+6) in H by (unfold n; lia). lia. }
 replace (n+v*5+6) with (L+v*7+8) in Hmax by (unfold n; lia).
 pose proof (mass_length out (L+v*7+6) _ Hmass Hlow ltac:(replace (L+v*7+6+2) with (L+v*7+8) by lia; exact Hmax)) as Hd.
 exists out. repeat split; try assumption; try lia.
 rewrite ordinary_source_adjacent by exact Hcoef.
 replace (L+(v*2+1)+1) with n by (unfold n; lia).
 replace (L+v*7+9) with (n+v*5+7) by (unfold n; lia).
 exact Hrun.
Qed.

End TerminalSuccessor.
End TerminalSuccessor.

Module RouteDeficit.
(* A bound on the arithmetic correction accumulated by a conversion route.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import OddRoute OddFuel EdOddOrbit.
Import String List PeanoNat Lia.
Import ListNotations.

Module RouteDeficit.
Open Scope nat.


(* The route induction already tracks a positive correction.  This
   interface only needs its upper bound and a different sum order. *)
Lemma route_deficit L k bs L' k' rest :
 OddRoute.OddRoute.route L k bs L' k' rest ->
 forall deficit, k+deficit+1=2^L ->
 exists j correction,
 length bs=2*j+1+length rest /\ L'=L+5*j+2 /\
 k'+deficit*2^(5*j+2)+correction+1=2^L' /\
 correction<2^(7*j+3).
Proof.
 intros Hr d Hd.
 destruct (OdDeficit.OdDeficit.route_deficit _ _ _ _ _ _ Hr d ltac:(lia))
   as [j [c [Hlen [HL [[Hpos Hb] He]]]]].
 exists j,c. split; [exact Hlen|]. split; [exact HL|].
 split; [clear -He; lia|exact Hb].
Qed.

Lemma route_suffix L k bs L' k' rest :
 OddRoute.OddRoute.route L k bs L' k' rest -> exists pre, bs=pre++rest.
Proof.
 intro H. induction H.
 - exists (repeat false (v*2)++[true]). rewrite <-app_assoc. reflexivity.
 - destruct IHroute as [pre E].
   exists (repeat false (v*2+1)++true::pre).
   rewrite E,<-app_assoc. reflexivity.
Qed.

End RouteDeficit.
End RouteDeficit.

Module MarkedDeficit.
(* Bounding the deficit retained by an exact marked-wall conversion path.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import OddFuel OddImage MarkedTrace RouteDeficit WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module MarkedDeficit.
Open Scope nat.

Definition initial_deficit u z := (2^(u+2)-3)*2^z.

Lemma initial_balance n u z : u+1<=n ->
 OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n u) z+initial_deficit u z+1=2^(n+1+z).
Proof.
 intro Hn. unfold initial_deficit.
 pose proof (OdDeficit.OdDeficit.initial_deficit n u z Hn) as H.
 clear -H. lia.
Qed.

Lemma initial_bound u z : initial_deficit u z<2^(u+2+z).
Proof.

 unfold initial_deficit. rewrite (Nat.pow_add_r 2 (u+2) z).

 assert (Hpos:0<2^z) by (pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia).

 assert (Hu:3<2^(u+2)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow].
   pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia. }
 nia.
Qed.

Lemma wall_deficit n bs L k rest :
 MarkedTrace.MarkedTrace.wall_route n bs L k rest -> length bs+1<=n ->
 exists j deficit,
 length bs=2*j+1+length rest /\ L=n+5*j+1 /\
 k+deficit+1=2^L /\ deficit<2^(7*j+2).
Proof.

 intros Hroute Hlen. destruct Hroute.
 - exists v,(initial_deficit (v*2) (v*5)).
   rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   rewrite length_app,repeat_length. cbn[length].
   repeat split; try lia.
   + apply initial_balance. lia.
   + replace (7*v+2) with (v*2+2+v*5) by lia. apply initial_bound.
 - rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   set (d0:=initial_deficit (v*2+1) (v*5+3)).

   assert (Hbalance:OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)+d0+1=
     2^(n+1+(v*5+3))) by (unfold d0; apply initial_balance; lia).
   destruct (RouteDeficit.RouteDeficit.route_deficit _ _ _ _ _ _ H d0 Hbalance)
     as [j [correction [Hdim [HL [Hend Hcorr]]]]].
   exists (v+1+j),(d0*2^(5*j+2)+correction).
   rewrite length_app,repeat_length. cbn[length].
   split; [lia|]. split; [lia|]. split; [lia|].

   assert (Hd0:d0<2^(7*v+6)).
   { unfold d0. replace (7*v+6) with ((v*2+1)+2+(v*5+3)) by lia.
     apply initial_bound. }

   replace (7*(v+1+j)+2) with ((7*(v+1+j)+1)+1) by lia.
   eapply (OdDeficit.OdDeficit.correction_join (7*v+6) (7*j+3)); [exact Hd0|exact Hcorr| |];
     clear; lia.
Qed.

Lemma wall_deficit_at n bs L k rest j :
 MarkedTrace.MarkedTrace.wall_route n bs L k rest -> length bs+1<=n ->
 length bs=2*j+1+length rest ->
 exists deficit, k+deficit+1=2^L /\ deficit<2^(7*j+2).
Proof.

 intros Hroute Hlen Hdim.
 destruct (wall_deficit _ _ _ _ _ Hroute Hlen)
   as [j0 [d [Hdim0 [HL [Hbalance Hb]]]]].

 assert (j0=j) by lia. subst j0. exists d. auto.
Qed.

Lemma tight_coefficient_bound n bs L k rest j T q :
 MarkedTrace.MarkedTrace.wall_route n (false::bs) L k rest -> length bs+2=n ->
 length bs=2*j+length rest ->
 T<=2^length rest -> k+1=2*(T+q) ->
 exists deficit,
 k+deficit+1=2^L /\ deficit<2^(7*j+2) /\
 q*4+3+2*deficit+4*T=2^(L+1)+3 /\ 2^L<=q*4+3.
Proof.

 intros Hroute Hn Hdim HT Hbudget.
 destruct (wall_deficit _ _ _ _ _ Hroute ltac:(cbn[length]; lia))
   as [j0 [d [Hdim0 [HL [Hbalance Hd]]]]].
 cbn[length] in Hdim0. assert (j0=j) by lia. subst j0.

 assert (HL':L=7*j+length rest+3) by lia.

 assert (Hcap:2^L=2^(7*j+2)*2^length rest*2).
 { rewrite HL'. replace (7*j+length rest+3) with ((7*j+2)+length rest+1) by lia.
   rewrite !Nat.pow_add_r. reflexivity. }

 assert (Hx:4<=2^(7*j+2)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow]. pose proof (Nat.pow_nonzero 2 (7*j) ltac:(lia)). nia. }

 assert (Hy:0<2^length rest) by (pose proof (Nat.pow_nonzero 2 (length rest) ltac:(lia)); lia).
 exists d. repeat split; try assumption.
 - rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
 - rewrite Hcap in *. nia.
Qed.

End MarkedDeficit.
End MarkedDeficit.

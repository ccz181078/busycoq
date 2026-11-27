From BusyCoq Require Import PR58Part1 PR58Part2 PR58Part3.


Module TerminalLoose.
(* Markers in the loose displaced-digit successors of terminal counters.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import OddFuel OddImage OddAdjacent TerminalSuccessor MarkedDeficit MagnitudeMarker.
Import CounterBits CDPasses WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.
Module TerminalLoose.
Open Scope nat.

Lemma initial_gap_three u z : 0<z ->
 MarkedDeficit.MarkedDeficit.initial_deficit u z+3<2^(u+2+z).
Proof.

 intro Hz. unfold MarkedDeficit.MarkedDeficit.initial_deficit.
 rewrite (Nat.pow_add_r 2 (u+2) z).
 assert (Hz2:2<=2^z) by
   (destruct z; [lia|]; cbn[Nat.pow]; pose proof (Nat.pow_nonzero 2 z ltac:(lia)); nia).
 assert (Hu:4<=2^(u+2)) by
   (rewrite Nat.pow_add_r; cbn[Nat.pow]; pose proof (Nat.pow_nonzero 2 u ltac:(lia)); nia).
 nia.
Qed.

Lemma even_balance L v : 0<v ->
 OddImage.OddImage.first_mass (L+v*2+1) v+MarkedDeficit.MarkedDeficit.initial_deficit (v*2) (v*5-1)=2^(L+v*7+1).
Proof.

 intro Hv.
 pose proof (MarkedDeficit.MarkedDeficit.initial_balance (L+v*2+1) (v*2) (v*5-1) ltac:(lia)) as H.
 unfold OddFuel.OddFuel.grown in H. unfold OddImage.OddImage.first_mass.
 pose proof (Nat.pow_nonzero 2 (v*5-1) ltac:(lia)).
 replace (L+v*2+1+1+(v*5-1)) with (L+v*7+1) in H by lia. nia.
Qed.

Lemma odd_balance L v :
 OddAdjacent.OddAdjacent.odd_mass (L+v*2+2) v+MarkedDeficit.MarkedDeficit.initial_deficit (v*2+1) (v*5+4)+3=2^(L+v*7+7).
Proof.

 pose proof (MarkedDeficit.MarkedDeficit.initial_balance (L+v*2+2) (v*2+1) (v*5+4) ltac:(lia)) as H.
 unfold OddFuel.OddFuel.grown in H. unfold OddAdjacent.OddAdjacent.odd_mass.
 assert (Hz:16<=2^(v*5+4)) by (change (2^4<=2^(v*5+4)); apply Nat.pow_le_mono_r; lia).
 replace (L+v*2+2+1+(v*5+4)) with (L+v*7+7) in H by lia. nia.
Qed.

Lemma near_power_marker out top gap :
 3<=top -> length out+1=top -> gap<2^(top-3) ->
 2^top<=CDPasses.CDPasses.value out+2^length out+gap -> WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros Htop Hlen Hgap Hvalue.
 apply (MagnitudeMarker.MagnitudeMarker.magnitude_marker out (length out)).
 - change (CDPasses.CDPasses.value out < 2^length out). apply CDPasses.CDPasses.value_bound.
 - change (2^(length out+1)<3*CDPasses.CDPasses.value out).
   set (b:=top-3).
   assert (Ht:top=b+3) by (unfold b; lia).
   assert (Hl:length out=b+2) by lia.
   rewrite Ht,Hl in Hvalue. rewrite Hl.
   fold b in Hgap.
   replace (b+2+1) with (b+3) by lia.
   rewrite !Nat.pow_add_r in *. cbn[Nat.pow] in *.
   pose proof (Nat.pow_nonzero 2 b ltac:(lia)). nia.
Qed.

Lemma even_loose_marker L v q out :
 3<=L -> 0<v -> length out+3=L+v*7+3 ->
 CDPasses.CDPasses.value out+2^length out=OddImage.OddImage.first_mass (L+v*2+1) v+(q*2+1) ->
 WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros HL Hv Hlen Hmass.
 pose proof (even_balance L v Hv) as Hbalance.
 apply (near_power_marker out (L+v*7+1) (MarkedDeficit.MarkedDeficit.initial_deficit (v*2) (v*5-1))); try lia.
 pose proof (MarkedDeficit.MarkedDeficit.initial_bound (v*2) (v*5-1)) as Hbound.
 assert (2^(v*2+2+(v*5-1))<=2^(L+v*7+1-3)) by (apply Nat.pow_le_mono_r; lia).
 lia.
Qed.

Lemma odd_loose_marker L v q out :
 3<=L -> length out+3=L+v*7+9 ->
 CDPasses.CDPasses.value out+2^length out=OddAdjacent.OddAdjacent.odd_mass (L+v*2+2) v+q ->
 WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros HL Hlen Hmass.
 pose proof (odd_balance L v) as Hbalance.
 apply (near_power_marker out (L+v*7+7) (MarkedDeficit.MarkedDeficit.initial_deficit (v*2+1) (v*5+4)+3)); try lia.
 pose proof (initial_gap_three (v*2+1) (v*5+4) ltac:(lia)) as Hbound.
 assert (2^((v*2+1)+2+(v*5+4))<=2^(L+v*7+7-3)) by (apply Nat.pow_le_mono_r; lia).
 lia.
Qed.

End TerminalLoose.
End TerminalLoose.

Module OdStrongMarker.
(* Reachable terminal counters preserve a marked displaced digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import GuardedRoute OdEvenMarker OdOddMarker OdDirectMarker.
Import TerminalLoose TerminalSuccessor MarkedDeficit OddImage OddAdjacent.
Import CounterBits CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module OdStrongMarker.

Lemma good_positive j delta : GuardedRoute.GuardedRoute.good_deficit j delta -> 1<=j.
Proof. intros [[Hj H]|[u [c [Hj H]]]]; lia. Qed.

Lemma even_tight_marker out L q j delta m a T :
 L=m+7*j+3 -> GuardedRoute.GuardedRoute.good_deficit j delta ->
 m<=4*a -> 0<T -> T<=6*2^m ->
 2*(T+q)+delta=2^L ->
 length out+2=L+(5*a+2)*7+3 ->
 CDPasses.CDPasses.value out+2^length out=OddImage.OddImage.first_mass (L+(5*a+2)*2+1) (5*a+2)+(q*2+1) ->
 WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros HL HG Hm HT HTb Hcap Hlen Hmass.
 pose proof (TerminalLoose.TerminalLoose.even_balance L (5*a+2) ltac:(lia)) as HB.
 assert (Hcancel:CDPasses.CDPasses.value out+MarkedDeficit.MarkedDeficit.initial_deficit ((5*a+2)*2) ((5*a+2)*5-1)=q*2+1).
 { clear -HB Hlen Hmass.
   replace (L+(5*a+2)*7+1) with (length out) in HB by lia. lia. }
 unfold MarkedDeficit.MarkedDeficit.initial_deficit in Hcancel.
 replace ((5*a+2)*2+2) with (10*a+6) in Hcancel by lia.
 replace ((5*a+2)*5-1) with (25*a+9) in Hcancel by lia.
 change (CounterBits.CounterBits.value out+(2^(10*a+6)-3)*2^(25*a+9)=q*2+1) in Hcancel.

 destruct HG as [[Hj HD]|[u [c [Hj [Hu [HC HD]]]]]].
 - apply (OdDirectMarker.OdDirectMarker.direct_even_marker out a j m T); try assumption.
   subst delta. rewrite HL in Hcap. clear -Hcap Hcancel HT. lia.
 - apply (OdEvenMarker.OdEvenMarker.reachable_even_marker out a j m u c T); try assumption.
   subst delta. rewrite HL in Hcap. clear -Hcap Hcancel HT. lia.
Qed.

Lemma odd_tight_marker out L q j delta m a T :
 L=m+7*j+3 -> GuardedRoute.GuardedRoute.good_deficit j delta ->
 1<=m<=4*a+2 -> 0<T -> T<=6*2^m ->
 2*(T+q)+delta=2^L ->
 length out+2=L+(5*a+4)*7+9 ->
 CDPasses.CDPasses.value out+2^length out=OddAdjacent.OddAdjacent.odd_mass (L+(5*a+4)*2+2) (5*a+4)+q ->
 WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros HL HG Hm HT HTb Hcap Hlen Hmass.
 pose proof (TerminalLoose.TerminalLoose.odd_balance L (5*a+4)) as HB.
 assert (Hcancel:CDPasses.CDPasses.value out+MarkedDeficit.MarkedDeficit.initial_deficit ((5*a+4)*2+1) ((5*a+4)*5+4)+3=q).
 { clear -HB Hlen Hmass.
   replace (L+(5*a+4)*7+7) with (length out) in HB by lia. lia. }
 unfold MarkedDeficit.MarkedDeficit.initial_deficit in Hcancel.
 replace ((5*a+4)*2+1+2) with (10*a+11) in Hcancel by lia.
 replace ((5*a+4)*5+4) with (25*a+24) in Hcancel by lia.
 change (CounterBits.CounterBits.value out+(2^(10*a+11)-3)*2^(25*a+24)+3=q) in Hcancel.

 assert (Hj:1<=j) by (apply (good_positive j delta);exact HG).
 assert (HF:2^(5*j)=2*2^(5*j-1)).
 { replace (5*j) with (S (5*j-1)) at 1 by (clear -Hj;lia). reflexivity. }
 assert (HP:2^L=2*2^(m+7*j+2)).
 { rewrite HL. replace (m+7*j+3) with (S (m+7*j+2)) by lia. reflexivity. }
 destruct HG as [[Hj0 HD]|[u [c [Hj0 [Hu [HC HD]]]]]].
 - apply (OdDirectMarker.OdDirectMarker.direct_odd_marker out a j m T); try assumption.
   subst delta. rewrite HF,HP in Hcap.
   clear -Hcap Hcancel. nia.

 - subst delta. rewrite HF,HP in Hcap.
   destruct (mod2 c) as [c0 He|c0 He]; subst c.
   + apply (OdOddMarker.OdOddMarker.reachable_odd_marker out a j m u c0 T); try assumption.
     * replace (5*j-5) with (S (5*j-6)) in HC by (clear -Hj0;lia).
       cbn[Nat.pow] in HC. clear -HC. lia.
     * clear -Hcap Hcancel. nia.
   + exfalso. clear -Hcap. nia.
Qed.

End OdStrongMarker.
End OdStrongMarker.

Module TightEd.
(* The first wall step when a displaced terminal digit has tight space.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses ExceptionalPasses PhaseE PhaseEd WallInvariant.
Import String List PeanoNat NArith Lia.
Import LocalPasses.Mirrored ExceptionalPasses.Exceptional PhaseE.PhaseE.
Open Scope sym.

Module TightEd.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dc := [0;0;0;0;1].
Notation dd := [0;0;0;1;0].
Notation dd1 := [1;0;0;1;0].
Notation p := [((A,[]),(B,[]))].

Lemma terminal_tight b :
 sideRLs mtm (xp 2 b) (dd *> 0inf) ((if b then db else da) *> dd1 *> 0inf).
Proof. destruct b; unfold xp; esc. Qed.

Lemma digits_terminal previous bs :
 sideRLs mtm (xp (length bs+2) previous) (shifted bs *> dd *> 0inf)
   ((if previous then db else da) *> normal bs *> dd1 *> 0inf).
Proof.
 rewrite <-(Str_app_assoc (if previous then db else da) (normal bs)).
 rewrite <-normal_lag, Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - apply digits_shift; lia.
 - apply terminal_tight.
Qed.

Open Scope nat.

Lemma shifted_terminal u bs :
 sideRLs mtm (p^^(2^(u+length bs+3)))
   (da^^u *> dc *> shifted bs *> dd *> 0inf)
   (da^^(u+1) *> db *> normal bs *> dd1 *> 0inf).
Proof.

 replace (da^^(u+1)) with (da^^u ++ da) by
   (rewrite lpow_add; cbn [lpow]; rewrite app_nil_r; reflexivity).
 rewrite Str_app_assoc.
 eapply @segRLs_sideRLs_concat with (ls2:=p^^(2^(length bs+3))).
 - applys_eq (d0s_Incs (2^(length bs+3)) u).
   repeat rewrite Nat.pow_add_r. flia.

 - eapply @segRLs_sideRLs_concat with (ls2:=xp (length bs+2) true).
   + unfold xp.
     assert (Hpow:2<=2^(length bs+2)).
     { rewrite Nat.pow_add_r. cbn [Nat.pow].
       pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)); nia. }
     replace (length bs+3) with (S (length bs+2)) by lia.
     cbn [Nat.pow].
     applys_eq (shifted_even (2^(length bs+2)-1)); flia.

   + apply digits_terminal.
Qed.

Open Scope sym.
Lemma even_tight_wall u bs :
 let k := u+length bs+3 in
 (0inf <* <[1;1]) <* [0] {{A}}>
   ([1;1]^^k *> da^^u *> dc *> shifted bs *> dd *> 0inf)
 -[mtm]->+
 (0inf <* <[1;1]) <* [0] {{A}}>
   ([1] *> [1;1]^^k *> da^^(u+1) *> db *> normal bs *> dd1 *> 0inf).
Proof.
 cbn zeta. apply BigStep.
 eapply segRLs_sideRLs_concat.
 - apply lds_Incs'.
 - rewrite Nat.mul_1_l. apply shifted_terminal.
Qed.

Definition after n bs := WallInvariant.WallInvariant.wall ([1;1]^^n ++ [1] ++ WallInvariant.WallInvariant.normal (false::bs) ++ dd1).

Lemma tight_Ed_step n bs :
 (length bs+2=n)%nat -> In true bs ->
 WallInvariant.WallInvariant.Ed n bs -[mtm]->+ after n bs.
Proof.

 intros Hn Hin.
 destruct (first_true bs Hin) as [u [t E]]. subst bs.
 rewrite length_app, repeat_length in Hn. cbn [length] in Hn.
 assert (Hk:(n=u+length t+3)%nat) by lia.
 pose proof (even_tight_wall u t) as Hrun.
 cbn zeta in Hrun. rewrite <-Hk in Hrun.

 unfold WallInvariant.WallInvariant.Ed, after, WallInvariant.WallInvariant.wall.
 change WallInvariant.WallInvariant.shifted with shifted.
 change WallInvariant.WallInvariant.normal with normal.
 rewrite shifted_app, shifted_zeros.
 cbn [shifted normal].
 repeat rewrite normal_app.
 repeat rewrite normal_zeros.
 cbn [normal].
 applys_eq Hrun; ut; st; simpl_rotate;
 repeat rewrite <-const_unfold; reflexivity.
Qed.

End TightEd.
End TightEd.

Module TightMarked.
(* Exact wall endpoints for a marked displaced digit with tight space.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import TightEd OddImage OddMarkedEntry TerminalClosure TightPrimer CDPasses CounterRules WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module TightMarked.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation one := [1].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation endword := [1;0;0;1;0].
Notation tight := [0;0;0;1;0;0;1;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma marked_false bs : WallInvariant.WallInvariant.marked 1 bs -> WallInvariant.WallInvariant.marked 0 (false::bs).
Proof.

 intros [pre [post [E Hp]]].
 exists (false::pre),post. split.
 - cbn. rewrite E. reflexivity.
 - cbn[length]. replace (S (length pre)) with (length pre+1) by lia.
   rewrite Nat.add_mod by lia. rewrite Hp. reflexivity.
Qed.

Lemma marked_true bs : WallInvariant.WallInvariant.marked 1 bs -> In true bs.
Proof.

 intros [pre [post [E Hp]]]. rewrite E. apply in_or_app. right. cbn. auto.
Qed.

Lemma realign bs :
 r4 *> WallInvariant.WallInvariant.normal bs *> endword *> 0inf = one *> CDPasses.CDPasses.third bs *> tight *> 0inf.
Proof.

 change (one *> z3 *> WallInvariant.WallInvariant.normal bs *> endword *> 0inf =
   one *> CDPasses.CDPasses.third bs *> tight *> 0inf).
 rewrite <-(Str_app_assoc z3 (WallInvariant.WallInvariant.normal bs)),OddImage.OddImage.phase_three_word,Str_app_assoc.
 reflexivity.
Qed.

Lemma tight_marked_entry n bs :
 length bs+2=n -> WallInvariant.WallInvariant.marked 1 bs ->
 exists L k rest j,
 length bs=2*j+length rest /\ L=n+5*j+1 /\
 k mod 2=1 /\ k+1<2^L /\ 2^(length rest+3)-1<=k /\
 WallInvariant.WallInvariant.Ed n bs -[mtm]->+
 CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third rest *> tight *> 0inf.
Proof.

 intros Hn Hmark.
 destruct (OddMarkedEntry.OddMarkedEntry.marked_entry n (false::bs) (endword *> 0inf)
    ltac:(eexists; reflexivity) (marked_false bs Hmark) ltac:(cbn[length]; lia))
   as [L [k [rest [j [Hlen [HL [Ho [Hb [Hmin Hrun]]]]]]]]].
 exists L,k,rest,j. cbn[length] in Hlen.
 repeat split; try assumption; try lia.
 rewrite <-realign.
 eapply progress_trans; [|exact Hrun].
 pose proof (TightEd.TightEd.tight_Ed_step n bs Hn (marked_true bs Hmark)) as Hstep.
 unfold TightEd.TightEd.after,WallInvariant.WallInvariant.wall,OddMarkedEntry.OddMarkedEntry.odd_wall in *.
 repeat rewrite Str_app_assoc in Hstep.
 exact Hstep.
Qed.

Lemma tight_marked_cases n bs :
 length bs+2=n -> WallInvariant.WallInvariant.marked 1 bs ->
 exists L k rest j q,
 length bs=2*j+length rest /\ L=n+5*j+1 /\
 k+1<2^L /\ k+1=2*(TightPrimer.TightPrimer.demand rest+q) /\ q*4+3<2^(L+1) /\
 ((exists w, length rest=w*2 /\
   WallInvariant.WallInvariant.Ed n bs -[mtm]->+ TerminalClosure.TerminalClosure.even_wall L (w*5+2) q /\
   WallInvariant.WallInvariant.invariant (TerminalClosure.TerminalClosure.even_wall L (w*5+2) q)) \/
  (exists w, length rest=w*2+1 /\
   WallInvariant.WallInvariant.Ed n bs -[mtm]->+ TerminalClosure.TerminalClosure.odd_wall L (w*5+6) q)).
Proof.

 intros Hn Hmark.
 destruct (tight_marked_entry n bs Hn Hmark)
   as [L [k [rest [j [Hlen [HL [Ho [Hb [Hmin Hrun]]]]]]]]].

 assert (Hdemand:2*TightPrimer.TightPrimer.demand rest<=k+1).
 { unfold TightPrimer.TightPrimer.demand. rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.
   pose proof (CDPasses.CDPasses.value_bound rest). lia. }
 destruct (TerminalClosure.TerminalClosure.tight_counter_cases L k rest ltac:(lia) Ho Hdemand)
   as [q [Heq [Hcoeff Hcases]]].
 exists L,k,rest,j,q. repeat split; try assumption.
 destruct Hcases as [[w [Hw [Hfinish Hinv]]]|[w [Hw Hfinish]]].
 - left. exists w. repeat split; try assumption.
   eapply progress_trans; eassumption.
 - right. exists w. split; [exact Hw|].
   eapply progress_trans; eassumption.
Qed.

End TightMarked.
End TightMarked.

Module ZeroDefect.
(* Converting a zero digit word with a displaced terminal digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.DivModCases.
Import LocalPasses PhaseEd CounterRules CounterFinish CounterBits CounterBatch WallInvariant.
Import String List PeanoNat NArith Lia.
Import ListNotations.
Module ZeroDefect.

Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dd := [0;0;0;1;0].
Notation dd1 := [1;0;0;1;0].
Notation p := [((A,[]),(B,[]))].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma shifted_zeros u : WallInvariant.WallInvariant.shifted (repeat false u) = da^^u.
Proof. induction u; cbn [repeat WallInvariant.WallInvariant.shifted lpow]; [reflexivity|].
 rewrite IHu. simpl_rotate. reflexivity. Qed.

Lemma zero_terminal : sideRLs mtm p (dd *> 0inf) (dd1 *> 0inf).
Proof. esc. Qed.

Lemma zero_preconversion u :
 sideRLs mtm (p^^(2^(u+1)-1)) (da^^u *> dd *> 0inf)
   (db^^u *> dd1 *> 0inf).
Proof.
 eapply segRLs_sideRLs_concat.
 - applys_eq (LocalPasses.Mirrored.d01s_Incs 1 u); rewrite Nat.pow_add_r; flia.
 - apply zero_terminal.
Qed.

Open Scope nat.
Lemma zero_remaining_bound n u : u+3<=n ->
 0<2^n-2^(u+1) /\ 2^n-2^(u+1)<2^n.
Proof.
 intro Hn.
 assert (2^(u+1)<2^n) by (apply Nat.pow_lt_mono_r; lia).
 pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)); lia.
Qed.

Lemma zero_remaining_decomposition n u : u+3<=n ->
 exists q, 2^n-2^(u+1)=(q*2+1)*2^(u+2)+2^(u+1).
Proof.
 intro Hn. set (d:=n-u-3).
 assert (He:n=u+3+d) by (unfold d; lia).
 pose proof (Nat.pow_nonzero 2 d ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 exists (2^d-1). rewrite He at 1.
 repeat rewrite Nat.pow_add_r. cbn [Nat.pow]. nia.
Qed.

Lemma zero_even_marker n a : a*2+3<=n ->
 WallInvariant.WallInvariant.marked 1 (CounterFinish.CounterFinish.digits (n+a*5+1) (((2^n-2^(a*2+1))*2+1)*2^(a*5))).
Proof.

 intro Hn. destruct (mod2 a) as [b Hb|b Hb]; subst a.
 - destruct (zero_remaining_decomposition n (b*2*2) Hn) as [q Hq].
   pose proof (CounterBits.CounterBits.marked_remainder (n+b*2*5+1)
      (((2^n-2^(b*2*2+1))*2+1)*2^(b*2*5)) (b*2*7+3) q
      ((2^(b*2*2+2)+1)*2^(b*2*5))) as Hmark.
   assert (Hpar:(b*2*7+3) mod 2=1).
   { replace (b*2*7+3) with ((b*7+1)*2+1) by lia.
     rewrite Nat.add_comm, Nat.mod_add by lia. reflexivity. }
   rewrite Hpar in Hmark. apply Hmark.

   + lia.
   + replace (b*2*7+3) with (b*2*5+(b*2*2+3)) by lia.
     repeat rewrite Nat.pow_add_r. cbn [Nat.pow].
     pose proof (Nat.pow_nonzero 2 (b*2*2) ltac:(lia)).
     pose proof (Nat.pow_nonzero 2 (b*2*5) ltac:(lia)). nia.
   + rewrite Hq. replace (b*2*7+3) with (b*2*5+(b*2*2+3)) by lia.
     repeat rewrite Nat.pow_add_r. cbn [Nat.pow]. nia.
 - apply CounterBits.CounterBits.marked_shift_odd; [lia|].
   replace ((1+b*2)*5) with ((b*5+2)*2+1) by lia.
   rewrite Nat.add_comm, Nat.mod_add by lia. reflexivity.
Qed.

Open Scope sym.
Lemma zero_counter_entry n u : (u+3<=n)%nat ->
 WallInvariant.WallInvariant.Ed n (repeat false u) -[mtm]->*
 CounterRules.CounterRules.LC n (2^n-2^(u+1)) |> db^^u *> dd1 *> 0inf.
Proof.
 intro Hn. unfold WallInvariant.WallInvariant.Ed, WallInvariant.WallInvariant.wall. rewrite shifted_zeros.
 repeat rewrite Str_app_assoc.
 eapply evstep_trans.
 - apply PhaseEd.PhaseEd.even_wall_counter.
 - destruct (zero_remaining_bound n u Hn) as [Hpos Hb].
   replace (2^n-1)%nat with ((2^n-2^(u+1))+(2^(u+1)-1))%nat by
     (assert (2^(u+1)<2^n)%nat by (apply Nat.pow_lt_mono_r; lia); lia).
   apply CounterBatch.CounterBatch.right_pass_batch.
   + pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)). lia.
   + apply zero_preconversion.
Qed.

Lemma zero_defect_invariant n u : (u+3<=n)%nat ->
 exists c, WallInvariant.WallInvariant.Ed n (repeat false u) -[mtm]->+ c /\ WallInvariant.WallInvariant.invariant c.
Proof.

 intro Hn. destruct (zero_remaining_bound n u Hn) as [Hpos Hb].
 destruct (mod2 u) as [a Hu|a Hu]; subst u.
 - eexists. split.
   + eapply evstep_progress_trans.
     * apply zero_counter_entry; exact Hn.
     * apply PhaseEd.PhaseEd.gap2_even_wall; exact Hb.

   + replace (n+1+(a*5+1))%nat with ((n+a*5+1)+1)%nat by lia.
     replace (((2^n-2^(a*2+1))*2+1)*2^(a*5+1)+1)%nat with
       ((((2^n-2^(a*2+1))*2+1)*2^(a*5))*2+1)%nat by
       (repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
     apply CounterBits.CounterBits.numeric_odd.
     * pose proof (PhaseEd.PhaseEd.shifted_value_bound n (2^n-2^(a*2+1)) (a*5) Hb).
       replace (n+1+a*5)%nat with (n+a*5+1)%nat in H by lia. exact H.
     * apply zero_even_marker; exact Hn.

 - replace (1+a*2)%nat with (a*2+1)%nat in * by lia.
   eexists. split.
   + eapply evstep_progress_trans.
     * apply zero_counter_entry; exact Hn.
     * apply PhaseEd.PhaseEd.gap2_odd_wall; exact Hb.
   + replace (((2^n-2^(a*2+1+1))*2+1)*2^(a*5+4))%nat with
       ((((2^n-2^(a*2+1+1))*2+1)*2^(a*5+3))*2)%nat by
       (replace (a*5+4)%nat with (a*5+3+1)%nat by lia;
        repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
     apply CounterBits.CounterBits.numeric_even.
     * pose proof (Nat.pow_nonzero 2 (a*5+3) ltac:(lia)). nia.
     * replace ((((2^n-2^(a*2+1+1))*2+1)*2^(a*5+3))*2)%nat with
       (((2^n-2^(a*2+1+1))*2+1)*2^(a*5+4))%nat by
       (replace (a*5+4)%nat with (a*5+3+1)%nat by lia;
        repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
       apply PhaseEd.PhaseEd.shifted_value_bound; exact Hb.
Qed.

End ZeroDefect.
End ZeroDefect.

Module ZeroEdOrbit.
(* Returning the zero-word defect branches to even walls.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import ZeroDefect PhaseEd EdEvenOrbit EdOddOrbit OddImage OddFuel OddRecursion.
Import CounterBits CounterFinish CounterRules MarkerArithmetic WallInvariant CDPasses.
Import List PeanoNat Lia.
Import ListNotations.

Module ZeroEdOrbit.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope nat.

Definition rank n m := 2^n-2^(m+1).

Lemma digits_ones n : CounterFinish.CounterFinish.digits n (2^n-1)=repeat true n.
Proof.

 induction n; [reflexivity|].
 cbn[Nat.pow repeat].
 replace (2*2^n-1) with ((2^n-1)*2+1) by
   (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia).
 rewrite CounterFinish.CounterFinish.digits_odd,IHn. reflexivity.
Qed.

Lemma digits_power_shift n v u :
 CounterFinish.CounterFinish.digits (n+u) (v*2^u)=repeat false u++CounterFinish.CounterFinish.digits n v.
Proof.

 induction u.
 - cbn[Nat.pow repeat app]. rewrite Nat.add_0_r,Nat.mul_1_r. reflexivity.
 - replace (n+S u) with (S (n+u)) by lia.
   cbn[Nat.pow repeat].
   replace (v*(2*2^u)) with ((v*2^u)*2) by nia.
   rewrite CounterFinish.CounterFinish.digits_even,IHu. reflexivity.
Qed.

Lemma rank_digits n m : m+1<=n ->
 CounterFinish.CounterFinish.digits n (rank n m)=repeat false (m+1)++repeat true (n-m-1).
Proof.

 intro Hn.

 assert (He:n=(n-m-1)+(m+1)) by lia.

 assert (Hrank:rank n m=(2^(n-m-1)-1)*2^(m+1)).
 { unfold rank. rewrite He at 1. rewrite Nat.pow_add_r.
   pose proof (Nat.pow_nonzero 2 (n-m-1) ltac:(lia)). nia. }
 rewrite Hrank.
 rewrite He at 1. rewrite digits_power_shift,digits_ones. reflexivity.
Qed.

Open Scope sym.
Notation ld := [1;1].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma zero_odd_exit n a : (a*2+4<=n)%nat ->
 WallInvariant.WallInvariant.Ed n (repeat false (a*2+1)) -[mtm]->+
 WallInvariant.WallInvariant.O (n+a*5+5)
   (repeat false (a*5+4)++true::CounterFinish.CounterFinish.digits n (rank n (a*2+1))).
Proof.

 intro Hn.
 destruct (ZeroDefect.ZeroDefect.zero_remaining_bound n (a*2+1) ltac:(lia)) as [Hpositive Hb].
 fold (rank n (a*2+1)) in Hb.
 pose proof (ZeroDefect.ZeroDefect.zero_counter_entry n (a*2+1) ltac:(lia)) as Hentry.
 fold (rank n (a*2+1)) in Hentry.
 pose proof (PhaseEd.PhaseEd.gap2_odd_wall n (rank n (a*2+1)) a Hb) as Hwall.

 assert (Hstart:WallInvariant.WallInvariant.Ed n (repeat false (a*2+1)) -[mtm]->+
   (0inf<*<[1;1])<*[0] {{A}}>
   ([1]*>ld^^(n+a*5+5)*>CounterRules.CounterRules.RC ((rank n (a*2+1)*2+1)*2^(a*5+4)))).
 { replace (n+a*5+5)%nat with (n+1+(a*5+4))%nat by lia.
   eapply evstep_progress_trans; eassumption. }
 unfold WallInvariant.WallInvariant.O,WallInvariant.WallInvariant.wall. repeat rewrite Str_app_assoc.
 rewrite EdEvenOrbit.EdEvenOrbit.normal_shift_odd by exact Hb.
 applys_eq Hstart; ut; st; simpl_rotate; reflexivity.
Qed.

Lemma zero_even_valuation n b : (4*b+4<=n)%nat ->
 exists out,
 (length out+2<=n+35*b+17)%nat /\ WallInvariant.WallInvariant.marked 1 out /\
 WallInvariant.WallInvariant.Ed n (repeat false (4*b+1)) -[mtm]->+ WallInvariant.WallInvariant.Ed (n+35*b+17) out.
Proof.

 intro Hn.
 destruct (ZeroDefect.ZeroDefect.zero_remaining_bound n (4*b+1) ltac:(lia)) as [Hp Hk].
 fold (rank n (4*b+1)) in Hp,Hk.
 destruct (ZeroDefect.ZeroDefect.zero_remaining_decomposition n (4*b+1) ltac:(lia)) as [q He].
 fold (rank n (4*b+1)) in He.

 assert (Hsmall:(2^(4*b+1+1)<2^(4*b+1+2))%nat)
   by (apply Nat.pow_lt_mono_r; lia).

 destruct (EdEvenOrbit.EdEvenOrbit.even_image_marker (n+10*b+5) (5*b+2) n
   (rank n (4*b+1)) (4*b+1+2) q (2^(4*b+1+1))
   ltac:(lia) ltac:(lia) ltac:(lia) Hk ltac:(lia)
   ltac:(lia) Hsmall He) as [out [Hlen [Hmark Hrun]]].
 replace (n+10*b+5+(5*b+2)*5+2)%nat with (n+35*b+17)%nat in * by lia.
 exists out. split; [exact Hlen|]. split; [exact Hmark|].
 eapply progress_trans; [|exact Hrun].

 pose proof (zero_odd_exit n (b*2) ltac:(lia)) as Hexit.
 replace (b*2*2+1)%nat with (4*b+1)%nat in Hexit by lia.
 replace (n+b*2*5+5)%nat with (n+10*b+5)%nat in Hexit by lia.
 replace (b*2*5+4)%nat with ((5*b+2)*2)%nat in Hexit by lia.
 exact Hexit.
Qed.

Lemma zero_odd_valuation_entry n b : (4*b+6<=n)%nat ->
 WallInvariant.WallInvariant.Ed n (repeat false (4*b+3)) -[mtm]->+
 CounterRules.CounterRules.LC (EdOddOrbit.EdOddOrbit.initial_width n b) (EdOddOrbit.EdOddOrbit.initial_rank n b) |>
 z3 *> WallInvariant.WallInvariant.normal (CounterFinish.CounterFinish.digits n (rank n (4*b+3))) *> 0inf.
Proof.

 intro Hn.
 eapply progress_trans.

 - pose proof (zero_odd_exit n (b*2+1) ltac:(lia)) as Hexit.
   replace ((b*2+1)*2+1)%nat with (4*b+3)%nat in Hexit by lia.
   replace (n+(b*2+1)*5+5)%nat with (n+10*b+10)%nat in Hexit by lia.
   replace ((b*2+1)*5+4)%nat with ((5*b+4)*2+1)%nat in Hexit by lia.
   exact Hexit.
 - pose proof (OddRecursion.OddRecursion.initial_odd_entry (n+10*b+10) (5*b+4)
     (CounterFinish.CounterFinish.digits n (rank n (4*b+3))) ltac:(lia)) as Hentry.
   replace ((5*b+4)*2+1)%nat with (10*b+9)%nat in Hentry by lia.
   replace ((5*b+4)*5+3)%nat with (25*b+23)%nat in Hentry by lia.

   replace (n+10*b+10+1+(25*b+23))%nat with (EdOddOrbit.EdOddOrbit.initial_width n b) in Hentry by
     (unfold EdOddOrbit.EdOddOrbit.initial_width; lia).
   replace ((5*b+4)*2+1)%nat with (10*b+9)%nat by lia.
   exact Hentry.
Qed.

End ZeroEdOrbit.
End ZeroEdOrbit.

Module StrongDigits.
(* Digit guards for the shifted counters produced by conversions.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import CounterBits CounterFinish CounterRules ZeroEdOrbit StrongInvariant WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.

Module StrongDigits.
Open Scope nat.

Lemma shifted_digits n q u :
 CounterFinish.CounterFinish.digits (n+u+1) ((q*2+1)*2^u)=repeat false u++true::CounterFinish.CounterFinish.digits n q.
Proof.
 replace (n+u+1) with (Datatypes.S n+u) by lia.
 rewrite ZeroEdOrbit.ZeroEdOrbit.digits_power_shift,CounterFinish.CounterFinish.digits_odd. reflexivity.
Qed.

Lemma odd_shift_guard n q u : u mod 2=1 ->
 StrongInvariant.StrongInvariant.digit_guard (CounterFinish.CounterFinish.digits (n+u+1) ((q*2+1)*2^u)).
Proof.
 intro H. rewrite shifted_digits. left.
 destruct (mod2 u) as [v E|v E]; subst u; [lia|].
 exists v,(CounterFinish.CounterFinish.digits n q). f_equal. f_equal. lia.
Qed.

Lemma adjacent_shift_guard n q u : 0<u ->
 StrongInvariant.StrongInvariant.digit_guard (CounterFinish.CounterFinish.digits (n+u+2) ((q*4+3)*2^u)).
Proof.
 intro Hu.
 replace (q*4+3) with ((q*2+1)*2+1) by lia.
 replace (n+u+2) with ((n+1)+u+1) by lia.
 rewrite shifted_digits.
 replace (n+1) with (Datatypes.S n) by lia.
 rewrite CounterFinish.CounterFinish.digits_odd. right. left.
 exists u,(CounterFinish.CounterFinish.digits n q). split; [exact Hu|reflexivity].
Qed.

Lemma digits_true_at width v i q :
 i<width -> v/2^i=q*2+1 -> nth i (CounterFinish.CounterFinish.digits width v) false=true.
Proof.
 intros Hi Hq.
 rewrite (CounterBits.CounterBits.digits_split width i v) by lia.
 rewrite app_nth2 by (rewrite CounterFinish.CounterFinish.digits_length; lia).
 rewrite CounterFinish.CounterFinish.digits_length,Nat.sub_diag,Hq.
 replace (width-i) with (Datatypes.S (width-i-1)) by lia.
 rewrite CounterFinish.CounterFinish.digits_odd. reflexivity.
Qed.

Lemma digits_bit_remainder width v i q r :
 i<width -> r<2^i -> v=(q*2+1)*2^i+r ->
 nth i (CounterFinish.CounterFinish.digits width v) false=true.
Proof.
 intros Hi Hr Hv. apply (digits_true_at width v i q Hi).
 rewrite Hv,Nat.add_comm,Nat.div_add by (apply Nat.pow_nonzero; lia).
 rewrite Nat.div_small by exact Hr. lia.
Qed.

Lemma close_shift_guard n q a i : 0<a ->
 nth i (CounterFinish.CounterFinish.digits (n+10*a+1) ((q*2+1)*2^(10*a))) false=true ->
 i mod 2=1 -> i<=14*a+3 ->
 StrongInvariant.StrongInvariant.digit_guard (CounterFinish.CounterFinish.digits (n+10*a+1) ((q*2+1)*2^(10*a))).
Proof.
 intros Ha Hi Hp Hb. right. right.
 exists a,(CounterFinish.CounterFinish.digits n q),i. repeat split; try assumption.
 apply shifted_digits.
Qed.

Open Scope sym.
Lemma odd_counter_wall n v : (v<2^n)%nat ->
 (0inf<*<[1;1])<*[0] {{A}}> ([1]*>[1;1]^^(n+1)*>CounterRules.CounterRules.RC (v*2+1))=
 WallInvariant.WallInvariant.E (n+2) (CounterFinish.CounterFinish.digits n v).
Proof.

 intro Hv. unfold CounterRules.CounterRules.RC. rewrite BinInc_mul2add1.
 change ((0inf<*<[1;1])<*[0] {{A}}>
   ([1]*>[1;1]^^(n+1)*>[1;0;0;0;0]*>CounterRules.CounterRules.RC v)=WallInvariant.WallInvariant.E (n+2) (CounterFinish.CounterFinish.digits n v)).
 rewrite <-(CounterFinish.CounterFinish.digits_normal n v Hv).
 replace ([1]*>[1;1]^^(n+1)*>[1;0;0;0;0]*>WallInvariant.WallInvariant.normal(CounterFinish.CounterFinish.digits n v)*>0inf)
   with ([1;1]^^(n+2)*>[0;0;0;0]*>WallInvariant.WallInvariant.normal(CounterFinish.CounterFinish.digits n v)*>0inf)
   by (replace (n+2)%nat with ((n+1)+1)%nat by lia; st; simpl_rotate; reflexivity).
 rewrite CounterBits.CounterBits.shifted_normal. unfold WallInvariant.WallInvariant.E,WallInvariant.WallInvariant.wall. rewrite Str_app_assoc. reflexivity.
Qed.

End StrongDigits.
End StrongDigits.

Module TightTrace.
(* Tight displaced walls with their exact conversion path retained.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import TightEd TightMarked MarkedTrace OddMarkedEntry TerminalClosure TightPrimer.
Import TerminalSuccessor StrongInvariant StrongDigits BlankPasses CounterFinish.
Import CDPasses CounterRules WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module TightTrace.

Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation one := [1].
Notation r4 := [1;0;0;0].
Notation endword := [1;0;0;1;0].
Notation tight := [0;0;0;1;0;0;1;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma terminal_even_strong L s q :
 0<s -> q*4+3<2^(L+1) -> StrongInvariant.StrongInvariant.strong (TerminalClosure.TerminalClosure.even_wall L s q).
Proof.

 intros Hs Hcoeff.
 destruct (TerminalSuccessor.TerminalSuccessor.coefficient_parts L q Hcoeff) as [HL Hrest].

 assert (Hvalue:(q*4+3)*2^s<2^(L+s+1)).
 { replace (L+s+1) with ((L+1)+s) by lia. rewrite Nat.pow_add_r.
   pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia. }

 assert (Hwall:TerminalClosure.TerminalClosure.even_wall L s q=
   WallInvariant.WallInvariant.E (L+s+3) (CounterFinish.CounterFinish.digits (L+s+1) ((q*4+3)*2^s))).
 { unfold TerminalClosure.TerminalClosure.even_wall,WallInvariant.WallInvariant.E,WallInvariant.WallInvariant.wall. rewrite Str_app_assoc.
   rewrite BlankPasses.BlankPasses.digits_shifted by exact Hvalue. reflexivity. }
 rewrite Hwall. constructor.
 - rewrite CounterFinish.CounterFinish.digits_length. lia.
 - replace (L+s+1) with ((L-1)+s+2) by lia.
   apply StrongDigits.StrongDigits.adjacent_shift_guard. exact Hs.
Qed.

Lemma tight_entry n bs :
 length bs+2=n -> WallInvariant.WallInvariant.marked 1 bs ->
 exists L k rest j,
 MarkedTrace.MarkedTrace.wall_route n (false::bs) L k rest /\
 length bs=2*j+length rest /\ L=n+5*j+1 /\
 k mod 2=1 /\ k+1<2^L /\ 2^(length rest+4)-1<=k /\
 WallInvariant.WallInvariant.Ed n bs -[mtm]->+
 CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third rest *> tight *> 0inf.
Proof.

 intros Hn Hmark.
 destruct (MarkedTrace.MarkedTrace.marked_entry_trace n (false::bs) (endword *> 0inf)
   ltac:(eexists; reflexivity) (TightMarked.TightMarked.marked_false bs Hmark)
   ltac:(cbn[length]; lia))
   as [L [k [rest [j [Hroute [Hlen [HL [Ho [Hb [Hmin Hrun]]]]]]]]]].
 exists L,k,rest,j. cbn[length] in Hlen.
 repeat split; try assumption; try lia.
 rewrite <-TightMarked.TightMarked.realign.
 eapply progress_trans; [|exact Hrun].
 pose proof (TightEd.TightEd.tight_Ed_step n bs Hn (TightMarked.TightMarked.marked_true bs Hmark)) as Hstep.
 unfold TightEd.TightEd.after,WallInvariant.WallInvariant.wall,OddMarkedEntry.OddMarkedEntry.odd_wall in *.
 repeat rewrite Str_app_assoc in Hstep. exact Hstep.
Qed.

Lemma tight_cases n bs :
 length bs+2=n -> WallInvariant.WallInvariant.marked 1 bs ->
 exists L k rest j q,
 MarkedTrace.MarkedTrace.wall_route n (false::bs) L k rest /\
 length bs=2*j+length rest /\ L=n+5*j+1 /\
 k+1<2^L /\ 2^(length rest+4)-1<=k /\
 k+1=2*(TightPrimer.TightPrimer.demand rest+q) /\ 0<q /\ q*4+3<2^(L+1) /\
 ((exists w, length rest=w*2 /\
   WallInvariant.WallInvariant.Ed n bs -[mtm]->+ TerminalClosure.TerminalClosure.even_wall L (w*5+2) q /\
   StrongInvariant.StrongInvariant.strong (TerminalClosure.TerminalClosure.even_wall L (w*5+2) q)) \/
  (exists w, length rest=w*2+1 /\
   WallInvariant.WallInvariant.Ed n bs -[mtm]->+ TerminalClosure.TerminalClosure.odd_wall L (w*5+6) q)).
Proof.

 intros Hn Hmark.
 destruct (tight_entry n bs Hn Hmark)
   as [L [k [rest [j [Hroute [Hlen [HL [Ho [Hb [Hmin Hrun]]]]]]]]]].

 assert (Hdemand:2*TightPrimer.TightPrimer.demand rest<=k+1).
 { unfold TightPrimer.TightPrimer.demand. rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.
   pose proof (CDPasses.CDPasses.value_bound rest). lia. }
 destruct (TerminalClosure.TerminalClosure.tight_counter_cases L k rest ltac:(lia) Ho Hdemand)
   as [q [Heq [Hcoeff Hcases]]].

 assert (Hq:0<q).
 { unfold TightPrimer.TightPrimer.demand in Heq.
   rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.
   pose proof (Nat.pow_nonzero 2 (length rest) ltac:(lia)). nia. }
 exists L,k,rest,j,q. repeat split; try assumption.
 destruct Hcases as [[w [Hw [Hfinish Hinv]]]|[w [Hw Hfinish]]].
 - left. exists w. repeat split; try assumption.
   + eapply progress_trans; eassumption.
   + apply terminal_even_strong; lia.
 - right. exists w. split; [exact Hw|].
   eapply progress_trans; eassumption.
Qed.

End TightTrace.
End TightTrace.

Module StrongE.
(* The guarded shifted-digit wall returns to a guarded wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import List PeanoNat Lia.
Import ListNotations.

Module StrongE.


Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation one := [1].
Notation z3 := [0;0;0].

Notation dc := [0;0;0;0;1].
Notation defect := [0;0;0;0;0;0;0;1].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma demand_bound bs : OddDefectTail.OddDefectTail.demand bs<=6*2^length bs.
Proof.

 unfold OddDefectTail.OddDefectTail.demand. destruct (Nat.eqb (CDPasses.CDPasses.value bs) 0).
 - rewrite Nat.pow_add_r. cbn[Nat.pow]. lia.
 - lia.
Qed.

Lemma converted_bounds bs :
 length bs+1<=OddDefectTail.OddDefectTail.converted_digits bs<=length bs+2.
Proof. unfold OddDefectTail.OddDefectTail.converted_digits. destruct (Nat.eqb (CDPasses.CDPasses.value bs) 0); lia. Qed.

Lemma ordinary_successor L rest j delta q w :
 L=length rest+7*j+3 -> GuardedRoute.GuardedRoute.good_deficit j delta ->
 2*(OddDefectTail.OddDefectTail.demand rest+q)+delta=2^L ->
 0<q -> q*4+3<2^(L+1) -> OddDefectTail.OddDefectTail.converted_digits rest=w*2+1 ->
 exists out, TerminalClosure.TerminalClosure.odd_wall L (w*5+4) q -[mtm]->+ out /\ StrongInvariant.StrongInvariant.strong out.
Proof.

 intros HL HG Hcap Hq Hcoeff Hg.
 pose proof (OdStrongMarker.OdStrongMarker.good_positive j delta HG) as Hj.
 pose proof (converted_bounds rest) as Hgb.
 pose proof (OddDefectFinish.OddDefectFinish.demand_positive rest) as HT.
 pose proof (demand_bound rest) as HTb.
 assert (HL3:3<=L) by (clear -HL;lia).

 destruct (mod2 w) as [a Ha|a Ha]; subst w.
 - replace (a*2*5+4) with ((5*a+2)*2) by lia.
   destruct (TerminalSuccessor.TerminalSuccessor.ordinary_even_image L (5*a+2) q ltac:(lia) Hcoeff)
    as [out [Hlen [Hlower [Hupper [Hmass Hrun]]]]].
   exists (WallInvariant.WallInvariant.Ed (L+(5*a+2)*7+3) out). split; [exact Hrun|].
   apply StrongInvariant.StrongInvariant.StrongEd; [exact Hlen|].
   destruct Hlen as [Hlo|Hti].

   + apply (TerminalLoose.TerminalLoose.even_loose_marker L (5*a+2) q out); try assumption; lia.
   + apply (OdStrongMarker.OdStrongMarker.even_tight_marker out L q j delta (length rest) a (OddDefectTail.OddDefectTail.demand rest)); try assumption.
     clear -Hgb Hg. lia.
 - replace ((1+a*2)*5+4) with ((5*a+4)*2+1) by lia.
   destruct (TerminalSuccessor.TerminalSuccessor.ordinary_odd_image L (5*a+4) q Hq Hcoeff)
    as [out [Hlen [Hlower [Hupper [Hmass Hrun]]]]].
   exists (WallInvariant.WallInvariant.Ed (L+(5*a+4)*7+9) out). split; [exact Hrun|].
   apply StrongInvariant.StrongInvariant.StrongEd; [exact Hlen|].
   destruct Hlen as [Hlo|Hti].

   + apply (TerminalLoose.TerminalLoose.odd_loose_marker L (5*a+4) q out); assumption.
   + apply (OdStrongMarker.OdStrongMarker.odd_tight_marker out L q j delta (length rest) a (OddDefectTail.OddDefectTail.demand rest)); try assumption.
     clear -Hgb Hg. lia.
Qed.

Lemma defect_entry n bs L k rest :
 MarkedTrace.MarkedTrace.wall_route n bs L k rest -> length bs+1<=n ->
 WallInvariant.WallInvariant.Od n bs -[mtm]->+ CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third rest *> defect *> 0inf.
Proof.

 intros Hr Hn.
 pose proof (MarkedTrace.MarkedTrace.route_run n bs L k rest (dc *> 0inf) Hr Hn) as Hrun.
 assert (Hwall:OddMarkedEntry.OddMarkedEntry.odd_wall n bs (dc *> 0inf)=WallInvariant.WallInvariant.Od n bs).
 { unfold OddMarkedEntry.OddMarkedEntry.odd_wall,WallInvariant.WallInvariant.Od,WallInvariant.WallInvariant.wall. repeat rewrite Str_app_assoc. reflexivity. }
 rewrite Hwall in Hrun.
 change (WallInvariant.WallInvariant.Od n bs -[mtm]->+ CounterRules.CounterRules.LC L k |> one *> z3 *> WallInvariant.WallInvariant.normal rest *> dc *> 0inf) in Hrun.
 rewrite OddDefectFinish.OddDefectFinish.third_normal_side in Hrun. exact Hrun.
Qed.

Lemma defect_strong n bs :
 length bs+1=n -> WallInvariant.WallInvariant.first_zero bs -> GuardedRoute.GuardedRoute.source_data n bs ->
 exists out, WallInvariant.WallInvariant.Od n bs -[mtm]->+ out /\ StrongInvariant.StrongInvariant.strong out.
Proof.

 intros Hfull Hzero [L [k [rest [j [delta [Hr [Hdim [HL [HD HG]]]]]]]]].
 assert (Hn:length bs+1<=n) by lia.
 assert (HLfull:L=length rest+7*j+3) by (clear -Hfull Hdim HL;lia).
 destruct (MarkedTrace.MarkedTrace.route_bounds n bs L k rest Hr Hzero Hn) as [Hk Ho].
 pose proof (MarkedTrace.MarkedTrace.route_margin4 n bs L k rest Hr Hzero Hn) as Hmin.
 pose proof (defect_entry n bs L k rest Hr Hn) as Hentry.

 pose proof (demand_bound rest) as HTb.
 assert (Hpow:0<2^length rest) by (pose proof (Nat.pow_nonzero 2 (length rest) ltac:(lia));lia).
 assert (Hb:2*OddDefectTail.OddDefectTail.demand rest<=k+1).
 { rewrite (Nat.pow_add_r 2 (length rest) 4) in Hmin. cbn[Nat.pow] in Hmin. lia. }
 destruct (TerminalClosure.TerminalClosure.defect_counter_cases L k rest ltac:(lia) Ho Hb)
   as [q [Hbudget [Hcoeff Hcases]]].
 assert (Hq:0<q).
 { rewrite (Nat.pow_add_r 2 (length rest) 4) in Hmin. cbn[Nat.pow] in Hmin. lia. }

 destruct Hcases as [[w [Hg [Hfinish Hold]]]|[w [Hg Hfinish]]].
 - exists (TerminalClosure.TerminalClosure.even_wall L (w*5) q). split.
   + eapply progress_trans; eassumption.
   + apply TightTrace.TightTrace.terminal_even_strong; [|exact Hcoeff].
     pose proof (converted_bounds rest). lia.
 - destruct (ordinary_successor L rest j delta q w HLfull HG
      ltac:(clear -HD Hbudget;lia) Hq Hcoeff Hg) as [out [Hnext Hstrong]].
   exists out. split; [|exact Hstrong].
   eapply progress_trans; [exact Hentry|].
   eapply progress_trans; eassumption.
Qed.

Lemma strong_E n bs :
 length bs+2<=n -> StrongInvariant.StrongInvariant.digit_guard bs ->
 exists out, WallInvariant.WallInvariant.E n bs -[mtm]->+ out /\ StrongInvariant.StrongInvariant.strong out.
Proof.

 intros Hn HG.
 set (padded:=bs++repeat false (n-length bs-2)).
 assert (Hp:length padded+2=n).
 { unfold padded. rewrite length_app,repeat_length. lia. }
 assert (Hpguard:StrongInvariant.StrongInvariant.digit_guard padded) by (apply StrongInvariant.StrongInvariant.guard_append; exact HG).
 pose proof (GuardedRoute.GuardedRoute.guard_source n padded ltac:(lia) Hpguard) as Hdata.

 assert (Hbits:PhaseE.PhaseE.output_bits n bs=false::padded) by reflexivity.
 assert (Htrue:In true bs).
 { destruct (StrongInvariant.StrongInvariant.guard_marked bs HG) as [pre [post [E Hparity]]].
   rewrite E. apply in_or_app. right. cbn. auto. }
 destruct (defect_strong n (false::padded) ltac:(cbn[length];lia)
   ltac:(exists padded;reflexivity) Hdata) as [out [Hnext Hstrong]].
 exists out. split; [|exact Hstrong].

 eapply progress_trans; [apply PhaseE.PhaseE.phase_E; eassumption|].
 rewrite Hbits. exact Hnext.
Qed.

End StrongE.
End StrongE.

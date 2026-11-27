From BusyCoq Require Import PR58Part1 PR58Part2 PR58Part3 PR58Part4 PR58Part5.


Module TightEquations.
(* Eliminating the terminal budget from tight successor counter values.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import OddImage OddAdjacent MarkedDeficit TerminalLoose CDPasses.
Import List PeanoNat Lia.
Import ListNotations.
Module TightEquations.
Open Scope nat.

Lemma even_tight_equation L v q k d T out :
 0<v -> 0<T -> k+d+1=2^L -> k+1=2*(T+q) ->
 length out+2=L+v*7+3 ->
 CDPasses.CDPasses.value out+2^length out=OddImage.OddImage.first_mass (L+v*2+1) v+(q*2+1) ->
 CDPasses.CDPasses.value out+(2*T-1)+d+MarkedDeficit.MarkedDeficit.initial_deficit (v*2) (v*5-1)=2^L.
Proof.

 intros Hv HT Hdef Hfuel Hlen Hmass.
 pose proof (TerminalLoose.TerminalLoose.even_balance L v Hv) as Hbal.
 assert (Hlength:length out=L+v*7+1) by lia.
 rewrite Hlength in Hmass. lia.
Qed.

Lemma deficit_half L k d :
 0<L -> k mod 2=1 -> k+d+1=2^L -> exists half, d=half*2.
Proof.

 intros HL Ho Hdef. destruct (mod2 k) as [a E|a E]; subst k; [lia|].
 destruct (mod2 d) as [b E|b E]; [eauto|]. subst d.
 replace L with (S (L-1)) in Hdef by lia. cbn[Nat.pow] in Hdef. lia.
Qed.

Lemma odd_tight_equation L v q k half T out :
 0<L -> k+half*2+1=2^L -> k+1=2*(T+q) ->
 length out+2=L+v*7+9 ->
 CDPasses.CDPasses.value out+2^length out=OddAdjacent.OddAdjacent.odd_mass (L+v*2+2) v+q ->
 CDPasses.CDPasses.value out+(T+3)+half+MarkedDeficit.MarkedDeficit.initial_deficit (v*2+1) (v*5+4)=2^(L-1).
Proof.

 intros HL Hdef Hfuel Hlen Hmass.
 pose proof (TerminalLoose.TerminalLoose.odd_balance L v) as Hbal.
 assert (Hlength:length out=L+v*7+7) by lia.
 rewrite Hlength in Hmass.
 replace L with (S (L-1)) in Hdef by lia. cbn[Nat.pow] in Hdef. lia.
Qed.

End TightEquations.
End TightEquations.

Module TightInitialMarker.
(* Markers after a tight terminal conversion whose first normal digit is even.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import CounterBits WallInvariant MarkedDeficit MultiGapMarker OdEvenMarker.
Import List PeanoNat Lia.
Import ListNotations.
Module TightInitialMarker.
Open Scope nat.

Lemma even_initial_marker out a j T :
 0<j -> 0<T -> T<=2^(a*4+1) ->
 CounterBits.CounterBits.value out+(2*T-1)+MarkedDeficit.MarkedDeficit.initial_deficit (j*2) (j*5)+
   MarkedDeficit.MarkedDeficit.initial_deficit (a*10+6) (a*25+14)=2^(j*7+a*4+4) ->
 WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros Hj HT HTb HE.
 set (J:=j*5). set (K:=a*25+14). set (A:=j*7+a*4+4).
 set (D:=2^(j*2+2)-3). set (E:=2^(a*10+8)-3).
 set (F:=D*2^J). set (c:=2*T-1).
 assert (HD:0<D) by (unfold D; apply OdEvenMarker.OdEvenMarker.minus_three_positive).
 assert (HEpos:0<E).
 { unfold E. replace (a*10+8) with ((a*10+6)+2) by lia.
   apply OdEvenMarker.OdEvenMarker.minus_three_positive. }
 assert (Hc:0<c) by (unfold c; lia).
 assert (HK:4<=K) by (unfold K; lia).
 assert (Hcb:c<2^(a*4+2)).

 { unfold c. replace (a*4+2) with ((a*4+1)+1) by lia.

   rewrite Nat.pow_add_r. cbn[Nat.pow]. lia. }
 assert (HF:F<2^(j*7+2)).
 { unfold F,D,J. pose proof (OdEvenMarker.OdEvenMarker.scaled_minus_three (j*2) (j*5)) as H.
   replace (j*2+2+j*5) with (j*7+2) in H by lia. exact H. }
 assert (HEq:CounterBits.CounterBits.value out+c+F+E*2^K=2^A).
 { unfold MarkedDeficit.MarkedDeficit.initial_deficit in HE. fold c in HE.
   replace (a*10+6+2) with (a*10+8) in HE by lia. exact HE. }
 destruct (Nat.le_gt_cases j (a*3+1)) as [Hsmall|Hlarge].
 - assert (HFsmall:F<2^(K-3)).

   { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   assert (Hcsmall:c<2^(K-3)).
   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold K; lia. }

   apply (MultiGapMarker.MultiGapMarker.positive_subtraction_marker out A K E (c+F)); try assumption; try lia.
   apply OdEvenMarker.OdEvenMarker.sum_small; assumption || lia.
 - assert (HJ:3<=J) by (unfold J; lia).
   assert (HcJ:c<2^(J-2)).
   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold J; lia. }
   assert (HcK:c<2^(K-2)).
   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   apply (MultiGapMarker.MultiGapMarker.two_gap_marker out A J K D E c); try assumption.

   + apply Nat.min_glb; lia.
   + destruct (Nat.le_ge_cases J K).
     * rewrite Nat.min_l by assumption. exact HcJ.
     * rewrite Nat.min_r by assumption. exact HcK.

Qed.

Lemma odd_initial_marker out a j T :
 0<j -> 0<T -> T<=2^(a*4+3) ->
 CounterBits.CounterBits.value out+(T+3)+MarkedDeficit.MarkedDeficit.initial_deficit (j*2) (j*5-1)+
   MarkedDeficit.MarkedDeficit.initial_deficit (a*10+11) (a*25+29)=2^(j*7+a*4+5) ->
 WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros Hj HT HTb HE.
 set (J:=j*5-1). set (K:=a*25+29). set (A:=j*7+a*4+5).
 set (D:=2^(j*2+2)-3). set (E:=2^(a*10+13)-3).
 set (F:=D*2^J). set (c:=T+3).
 assert (HD:0<D) by (unfold D; apply OdEvenMarker.OdEvenMarker.minus_three_positive).
 assert (HEpos:0<E).
 { unfold E. replace (a*10+13) with ((a*10+11)+2) by lia.
   apply OdEvenMarker.OdEvenMarker.minus_three_positive. }
 assert (Hc:0<c) by (unfold c; lia).
 assert (HK:4<=K) by (unfold K; lia).
 assert (Hcb:c<2^(a*4+4)).

 { unfold c. assert (8<=2^(a*4+3)) by (change (2^3<=2^(a*4+3)); apply Nat.pow_le_mono_r; lia).

   replace (a*4+4) with ((a*4+3)+1) by lia.
   rewrite Nat.pow_add_r. cbn[Nat.pow]. lia. }
 assert (HF:F<2^(j*7+1)).
 { unfold F,D,J. pose proof (OdEvenMarker.OdEvenMarker.scaled_minus_three (j*2) (j*5-1)) as H.
   replace (j*2+2+(j*5-1)) with (j*7+1) in H by lia. exact H. }
 assert (HEq:CounterBits.CounterBits.value out+c+F+E*2^K=2^A).
 { unfold MarkedDeficit.MarkedDeficit.initial_deficit in HE. fold c in HE.
   replace (a*10+11+2) with (a*10+13) in HE by lia. exact HE. }
 destruct (Nat.le_gt_cases j (a*3+2)) as [Hsmall|Hlarge].

 - assert (HFsmall:F<2^(K-3)).
   { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   assert (Hcsmall:c<2^(K-3)).

   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   apply (MultiGapMarker.MultiGapMarker.positive_subtraction_marker out A K E (c+F)); try assumption; try lia.
   apply OdEvenMarker.OdEvenMarker.sum_small; assumption || lia.
 - assert (HJ:3<=J) by (unfold J; lia).
   assert (HcJ:c<2^(J-2)).
   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold J; lia. }
   assert (HcK:c<2^(K-2)).

   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   apply (MultiGapMarker.MultiGapMarker.two_gap_marker out A J K D E c); try assumption.
   + apply Nat.min_glb; lia.
   + destruct (Nat.le_ge_cases J K).
     * rewrite Nat.min_l by assumption. exact HcJ.

     * rewrite Nat.min_r by assumption. exact HcK.
Qed.

End TightInitialMarker.
End TightInitialMarker.

Module TightInitialClosure.
(* Closing the ordinary endpoint after the first even normal digit.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import TerminalClosure TerminalSuccessor TerminalLoose TightEquations TightInitialMarker.
Import TightPrimer StrongInvariant MarkedDeficit CounterBits CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Module TightInitialClosure.


Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope nat.

Lemma deficit_halved j : 0<j ->
 MarkedDeficit.MarkedDeficit.initial_deficit (j*2) (j*5)=MarkedDeficit.MarkedDeficit.initial_deficit (j*2) (j*5-1)*2.
Proof.

 intro Hj. unfold MarkedDeficit.MarkedDeficit.initial_deficit.
 replace (j*5) with ((j*5-1)+1) at 1 by lia.
 rewrite (Nat.pow_add_r 2 (j*5-1) 1). cbn[Nat.pow]. nia.
Qed.

Lemma ordinary_initial_close L j rest k q w :
 0<j -> L=j*7+length rest+3 -> length rest=w*2+1 ->
 k+MarkedDeficit.MarkedDeficit.initial_deficit (j*2) (j*5)+1=2^L ->
 k+1=2*(TightPrimer.TightPrimer.demand rest+q) -> 0<q -> q*4+3<2^(L+1) ->
 exists out, TerminalClosure.TerminalClosure.odd_wall L (w*5+6) q -[mtm]->+ out /\ StrongInvariant.StrongInvariant.strong out.
Proof.

 intros Hj HL Hm Hdef Hfuel Hq Hcoef.
 assert (HL3:3<=L) by lia.
 assert (HT:0<TightPrimer.TightPrimer.demand rest<=2^length rest).
 { unfold TightPrimer.TightPrimer.demand. pose proof (CDPasses.CDPasses.value_bound rest). lia. }
 destruct (mod2 w) as [a Ha|a Ha]; subst w.
 - replace (a*2*5+6) with ((a*5+3)*2) by lia.
   destruct (TerminalSuccessor.TerminalSuccessor.ordinary_even_image L (a*5+3) q ltac:(lia) Hcoef)
     as [out [Hlen [Hlo [Hhi [Hmass Hrun]]]]].
   exists (WallInvariant.WallInvariant.Ed (L+(a*5+3)*7+3) out). split; [exact Hrun|].

   constructor; [exact Hlen|]. destruct Hlen as [Hloose|Htight].
   + apply (TerminalLoose.TerminalLoose.even_loose_marker L (a*5+3) q out); assumption || lia.
   + pose proof (TightEquations.TightEquations.even_tight_equation L (a*5+3) q k

       (MarkedDeficit.MarkedDeficit.initial_deficit (j*2) (j*5)) (TightPrimer.TightPrimer.demand rest) out
       ltac:(lia) ltac:(lia) Hdef Hfuel Htight Hmass) as HE.

     replace ((a*5+3)*2) with (a*10+6) in HE by lia.
     replace ((a*5+3)*5-1) with (a*25+14) in HE by lia.
     replace L with (j*7+a*4+4) in HE by lia.
     apply (TightInitialMarker.TightInitialMarker.even_initial_marker out a j (TightPrimer.TightPrimer.demand rest)); try assumption; try lia.
     replace (a*4+1) with (length rest) by lia. lia.
 - replace ((1+a*2)*5+6) with ((a*5+5)*2+1) by lia.
   destruct (TerminalSuccessor.TerminalSuccessor.ordinary_odd_image L (a*5+5) q Hq Hcoef)
     as [out [Hlen [Hlo [Hhi [Hmass Hrun]]]]].

   exists (WallInvariant.WallInvariant.Ed (L+(a*5+5)*7+9) out). split; [exact Hrun|].
   constructor; [exact Hlen|]. destruct Hlen as [Hloose|Htight].
   + apply (TerminalLoose.TerminalLoose.odd_loose_marker L (a*5+5) q out); assumption || lia.

   + rewrite deficit_halved in Hdef by exact Hj.

     pose proof (TightEquations.TightEquations.odd_tight_equation L (a*5+5) q k
       (MarkedDeficit.MarkedDeficit.initial_deficit (j*2) (j*5-1)) (TightPrimer.TightPrimer.demand rest) out
       ltac:(lia) Hdef Hfuel Htight Hmass) as HE.
     replace ((a*5+5)*2+1) with (a*10+11) in HE by lia.
     replace ((a*5+5)*5+4) with (a*25+29) in HE by lia.
     replace (L-1) with (j*7+a*4+5) in HE by lia.
     apply (TightInitialMarker.TightInitialMarker.odd_initial_marker out a j (TightPrimer.TightPrimer.demand rest)); try assumption; try lia.
     replace (a*4+3) with (length rest) by lia. lia.
Qed.

End TightInitialClosure.
End TightInitialClosure.

Module TightDirect.
(* Full tight-wall closure when the first ordinary one is at an even position.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import TightEd TightMarked TightTrace TightInitialClosure MarkedTrace.
Import OddMarkedEntry OddFuel OddImage MarkedDeficit TerminalClosure TightPrimer.
Import StrongInvariant CounterRules CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Module TightDirect.



Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation one := [1].
Notation endword := [1;0;0;1;0].
Notation tight := [0;0;0;1;0;0;1;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma tight_direct n bs v tail :
 length bs+2=n -> WallInvariant.WallInvariant.marked 1 bs ->
 false::bs=repeat false (v*2)++true::tail ->
 exists out, WallInvariant.WallInvariant.Ed n bs -[mtm]->+ out /\ StrongInvariant.StrongInvariant.strong out.
Proof.

 intros Hn Hmark Hword.
 assert (Hzero:WallInvariant.WallInvariant.first_zero (false::bs)) by (eexists; reflexivity).
 assert (Hv:0<v).
 { rewrite Hword in Hzero. apply MarkedTrace.MarkedTrace.first_zero_prefix in Hzero. lia. }
 assert (Hn':n=v*2+length tail+2).
 { pose proof (f_equal (@length bool) Hword) as Hlength.
   rewrite length_app,repeat_length in Hlength. cbn[length] in Hlength. lia. }
 set (L:=n+1+v*5).
 set (k:=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2)) (v*5)).

 assert (Hroute:MarkedTrace.MarkedTrace.wall_route n (false::bs) L k tail).
 { rewrite Hword. constructor. }
 destruct (MarkedTrace.MarkedTrace.route_bounds _ _ _ _ _ Hroute Hzero ltac:(cbn[length]; lia)) as [Hb Ho].

 pose proof (MarkedTrace.MarkedTrace.route_margin4 _ _ _ _ _ Hroute Hzero ltac:(cbn[length]; lia)) as Hmin.
 assert (Hrun:WallInvariant.WallInvariant.Ed n bs -[mtm]->+
   CounterRules.CounterRules.LC L k |> one *> CDPasses.CDPasses.third tail *> tight *> 0inf).
 { rewrite <-TightMarked.TightMarked.realign.
   eapply progress_trans.
   - pose proof (TightEd.TightEd.tight_Ed_step n bs Hn (TightMarked.TightMarked.marked_true bs Hmark)) as Hstep.
     unfold TightEd.TightEd.after,WallInvariant.WallInvariant.wall,OddMarkedEntry.OddMarkedEntry.odd_wall in *.
     repeat rewrite Str_app_assoc in Hstep. exact Hstep.
   - apply (MarkedTrace.MarkedTrace.route_run _ _ _ _ _ (endword *> 0inf) Hroute).

     cbn[length]. lia. }
 assert (Hdemand:2*TightPrimer.TightPrimer.demand tail<=k+1).
 { unfold TightPrimer.TightPrimer.demand. rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.

   pose proof (CDPasses.CDPasses.value_bound tail). lia. }
 destruct (TerminalClosure.TerminalClosure.tight_counter_cases L k tail ltac:(lia) Ho Hdemand)
   as [q [Hfuel [Hcoef Hcases]]].
 assert (Hq:0<q).
 { unfold TightPrimer.TightPrimer.demand in Hfuel. rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.
   pose proof (Nat.pow_nonzero 2 (length tail) ltac:(lia)). nia. }
 destruct Hcases as [[w [Hw [Hfinish Hinv]]]|[w [Hw Hfinish]]].
 - exists (TerminalClosure.TerminalClosure.even_wall L (w*5+2) q). split.
   + eapply progress_trans; eassumption.

   + apply TightTrace.TightTrace.terminal_even_strong; lia.
 - assert (Hdef:k+MarkedDeficit.MarkedDeficit.initial_deficit (v*2) (v*5)+1=2^L).
   { unfold k,L. apply MarkedDeficit.MarkedDeficit.initial_balance. lia. }
   destruct (TightInitialClosure.TightInitialClosure.ordinary_initial_close L v tail k q w Hv

     ltac:(unfold L; lia) Hw Hdef Hfuel Hq Hcoef) as [out [Hlast Hstrong]].
   exists out. split; [|exact Hstrong].
   eapply progress_trans; [exact Hrun|]. eapply progress_trans; eassumption.
Qed.

End TightDirect.
End TightDirect.

From Coq Require Import PeanoNat ZifyNat Lia.

Module DeficitResidues.
Module DeficitResidues.

Inductive pre_deficit : nat -> Prop :=
| PreInitial v : pre_deficit ((2^(2*v+3)-3)*2^(5*v+3))
| PreOdd d v : pre_deficit d ->
    pre_deficit ((2*d+2^(2*v+3)-1)*2^(5*v+4)).

Lemma pow_positive k : 0<2^k.
Proof. pose proof (Nat.pow_nonzero 2 k ltac:(lia)); lia. Qed.

Lemma factor_pow x y : y<=x -> 2^x=2^(x-y)*2^y.
Proof. intros; rewrite <-Nat.pow_add_r; f_equal; lia. Qed.

Lemma power_mod_zero coefficient z m : m<=z ->
 (coefficient*2^z) mod 2^m=0.
Proof.
 intros Hz; rewrite (factor_pow z m Hz), Nat.mul_assoc.
 apply Nat.mod_mul; pose proof (pow_positive m); lia.
Qed.

Lemma bit_residue d c i m : i<m ->
 ((d+c)/2^i) mod 2=(((d mod 2^m)+c)/2^i) mod 2.
Proof.
 intro Hi.
 pose proof (Nat.div_mod d (2^m) ltac:(pose proof (pow_positive m); lia)) as E.
 rewrite (factor_pow m (i+1) ltac:(lia)), Nat.pow_add_r in E at 1.
 change (2^1) with 2 in E.
 replace (d+c) with ((d mod 2^m+c)+(2*(2^(m-(i+1))*(d/2^m)))*2^i) by nia.
 rewrite Nat.div_add by (pose proof (pow_positive i); lia).
 replace (2*(2^(m-(i+1))*(d/2^m))) with ((2^(m-(i+1))*(d/2^m))*2) by lia.
 rewrite Nat.mod_add by lia; reflexivity.
Qed.

Lemma short_recurrence d m : 5<=m ->
 (32*d+112) mod 2^m=(32*(d mod 2^(m-5))+112) mod 2^m.
Proof.
 intro Hm.
 pose proof (Nat.div_mod d (2^(m-5)) ltac:(pose proof (pow_positive (m-5)); lia)) as E.
 assert (P:2^m=32*2^(m-5)).
 { rewrite (factor_pow m (m-5) ltac:(lia)).
   replace (m-(m-5)) with 5 by lia. reflexivity. }
 replace (32*d+112) with (32*(d mod 2^(m-5))+112+(d/2^(m-5))*2^m) by nia.
 rewrite Nat.mod_add by (pose proof (pow_positive m); lia). reflexivity.
Qed.

Lemma rec_zero d : ((2*d+2^(2*0+3)-1)*2^(5*0+4))=32*d+112.
Proof. change ((2*d+8-1)*16=32*d+112); lia. Qed.

Lemma divisible_8 d : pre_deficit d -> d mod 2^3=0.
Proof. intros Hd; destruct Hd; apply power_mod_zero; lia. Qed.

Lemma low_residue d : pre_deficit d ->
 d mod 256=0 \/ d mod 256=40 \/ d mod 256=112.
Proof.
 intro Hd; destruct Hd as [[|v]|d [|v] Hd].
 - right; left; reflexivity.
 - left; change (256) with (2^8); apply power_mod_zero; lia.
 - rewrite rec_zero; change (256) with (2^8).
   rewrite short_recurrence by lia.
   change (2^(8-5)) with (2^3); rewrite (divisible_8 d Hd).
   right; right; reflexivity.
 - left; change (256) with (2^8); apply power_mod_zero; lia.
Qed.

Lemma short_bound d : pre_deficit d -> (32*d+112) mod 2^13<=32*112+112.
Proof.
 intro Hd; pose proof (low_residue d Hd) as H.
 rewrite short_recurrence by lia. change (2^(13-5)) with 256.
 assert (d mod 256<=112) by lia.
 rewrite Nat.mod_small; [lia|].
 apply Nat.le_lt_trans with (32*112+112); [lia|apply Nat.ltb_lt; reflexivity].
Qed.

(* For a short recursive step with h=2 or h=3, bit 12 supplies
   the even witness, and bit 7 supplies the odd witness in all cases. *)
Lemma short_even d c : pre_deficit d -> c<8 ->
 (((32*d+112)+c)/2^12) mod 2=0.
Proof.
 intros Hd Hc; rewrite (bit_residue _ _ _ 13) by lia.
 pose proof (short_bound d Hd).
 rewrite Nat.div_small; [reflexivity|].
 apply Nat.lt_trans with (32*112+120); [lia|apply Nat.ltb_lt; reflexivity].
Qed.

Lemma low_odd d c : pre_deficit d -> c<8 -> ((d+c)/2^7) mod 2=0.
Proof.
 intros Hd Hc; rewrite (bit_residue _ _ _ 8) by lia.
 change (2^8) with 256. destruct (low_residue d Hd) as [E | [E | E]]; rewrite E;
   rewrite Nat.div_small by (change (2^7) with 128; lia); reflexivity.
Qed.

Lemma zero_or_initial_even d c : c<8 -> d mod 256=0 \/ d mod 256=40 ->
 ((d+c)/2^4) mod 2=0.
Proof.
 intros Hc H; rewrite (bit_residue _ _ _ 8) by lia.
 change (2^8) with 256; change (2^4) with 16.
 destruct H as [E | E]; rewrite E.
 - rewrite Nat.div_small by lia; reflexivity.
 - replace (40+c) with ((8+c)+2*16) by lia.
   rewrite Nat.div_add, Nat.div_small by lia. reflexivity.
Qed.

Lemma low_even d c : pre_deficit d -> c<8 ->
 ((d+c)/2^4) mod 2=0 \/ ((d+c)/2^12) mod 2=0.
Proof.
 intros Hd Hc; destruct Hd as [[|v]|d [|v] Hd].
 - left; apply zero_or_initial_even; [assumption|right; reflexivity].
 - left; apply zero_or_initial_even; [assumption|left; change (256) with (2^8);
     apply power_mod_zero; lia].
 - right; rewrite rec_zero; apply short_even; assumption.
 - left; apply zero_or_initial_even; [assumption|left; change (256) with (2^8);
     apply power_mod_zero; lia].
Qed.

End DeficitResidues.
End DeficitResidues.

Module BinaryZero.
Module BinaryZero.
Import DeficitResidues.DeficitResidues.

Definition has_zero d h bound p c :=
 exists i, h<=i /\ i<=bound /\ i mod 2=p /\ ((d+c)/2^i) mod 2=0.
Definition window d := forall h p c, p<2 -> c<2^h -> has_zero d h (3*h+6) p c.

Lemma parity_index n p : p<2 -> exists i, n<=i /\ i<=n+1 /\ i mod 2=p.
Proof.
 intro Hp; destruct (Nat.eq_dec (n mod 2) p).
 - exists n; repeat split; lia.
 - exists (n+1); repeat split; lia.
Qed.

Lemma zero_below_shift d z c h i : c<2^h -> h<=i -> i<z ->
 ((d*2^z+c)/2^i) mod 2=0.
Proof.
 intros Hc Hhi Hiz.
 pose proof (Nat.pow_le_mono_r 2 h i ltac:(lia) Hhi).
 rewrite (factor_pow z (i+1) ltac:(lia)), Nat.pow_add_r.
 change (2^1) with 2.
 replace (d*(2^(z-(i+1))*(2^i*2))+c) with (c+(d*2^(z-(i+1))*2)*2^i) by nia.
 rewrite Nat.div_add, (Nat.div_small c), Nat.add_0_l, Nat.mod_mul
   by (try (pose proof (pow_positive i)); lia).
 reflexivity.
Qed.

Lemma early_window d z h bound p c :
 p<2 -> c<2^h -> h+1<z -> h+1<=bound -> has_zero (d*2^z) h bound p c.
Proof.
 intros Hp Hc Hz Hb.
 destruct (parity_index h p Hp) as [i [Hi [Htop Hpar]]].
 exists i; repeat split; try lia. eapply zero_below_shift; eauto; lia.
Qed.

Lemma large_window d h width bound p c : p<2 -> c<2^h -> d<2^width ->
 Nat.max h width+2<=bound -> has_zero d h bound p c.
Proof.
 intros Hp Hc Hd Hb. set (j:=Nat.max h width) in *.
 pose proof (Nat.pow_le_mono_r 2 h j ltac:(lia) (Nat.le_max_l h width)).
 pose proof (Nat.pow_le_mono_r 2 width j ltac:(lia) (Nat.le_max_r h width)).
 destruct (parity_index (j+1) p Hp) as [i [Hi [Htop Hpar]]].
 pose proof (Nat.le_max_l h width).
 pose proof (Nat.pow_le_mono_r 2 (j+1) i ltac:(lia) Hi) as Hpow.
 rewrite Nat.pow_add_r in Hpow. change (2^1) with 2 in Hpow.
 exists i; repeat split; try lia. rewrite Nat.div_small by lia; reflexivity.
Qed.

Lemma step_div d a z c :
 ((2*d+2^(a+1)-1)*2^z+c)/2^(z+1)= d+(2^a-1+(2^z+c)/2^(z+1)).
Proof.
 pose proof (pow_positive a); pose proof (pow_positive (z+1)).
 replace ((2*d+2^(a+1)-1)*2^z+c) with ((2^z+c)+(d+(2^a-1))*2^(z+1)).
 - rewrite Nat.div_add by lia; lia.
 - rewrite !Nat.pow_add_r; change (2^1) with 2; nia.
Qed.

Lemma carry_small z c h : c<2^h -> h<=z -> (2^z+c)/2^(z+1)=0.
Proof.
 intros Hc Hh; apply Nat.div_small.
 pose proof (Nat.pow_le_mono_r 2 h z ltac:(lia) Hh).
 rewrite Nat.pow_add_r; change (2^1) with 2; lia.
Qed.

Lemma carry_large z c h : c<2^h -> z+1<=h -> (2^z+c)/2^(z+1)<=2^(h-(z+1)).
Proof.
 intros Hc Hh.
 apply Nat.lt_succ_r, Nat.div_lt_upper_bound; [pose proof (pow_positive (z+1)); lia|].
 rewrite (factor_pow h (z+1) Hh) in Hc.
 rewrite !Nat.pow_add_r in *; change (2^1) with 2 in *.
 pose proof (pow_positive z); nia.
Qed.

Lemma lift_window d a z h bound p c j : window d -> p<2 ->
 h<=z+1+j -> z+1+3*j+6<=bound ->
 2^a-1+(2^z+c)/2^(z+1)<2^j ->
 has_zero ((2*d+2^(a+1)-1)*2^z) h bound p c.
Proof.
 intros Hd Hp Hh Hbound Hsmall.
 destruct (Hd j ((p+(z+1)) mod 2) _
   (Nat.mod_upper_bound (p+(z+1)) 2 ltac:(discriminate)) Hsmall)
   as [i [Hi [Htop [Hpar Hzero]]]].
 exists (z+1+i); split; [lia|]; split; [lia|]; split.
 - rewrite Nat.add_mod, Hpar, (Nat.add_mod p (z+1)) by lia.
   pose proof (Nat.mod_upper_bound (z+1) 2 ltac:(lia)).
   rewrite (Nat.mod_small p 2 Hp); lia.
 - rewrite (Nat.pow_add_r 2 (z+1) i), <-Nat.div_div
     by (pose proof (pow_positive (z+1)); pose proof (pow_positive i); lia).
   rewrite step_div; exact Hzero.
Qed.

Lemma phase_window d a z h bound p c : window d -> p<2 -> c<2^h ->
 h+1<=bound ->
 (z<h+2 -> h<=z -> z+1+3*a+6<=bound) ->
 (z+1<=h -> z+1+3*(Nat.max (a+1) (h-z))+6<=bound) ->
 has_zero ((2*d+2^(a+1)-1)*2^z) h bound p c.
Proof.
 intros Hd Hp Hc Hb Hlow Hhigh.
 destruct (Nat.le_gt_cases (h+2) z) as [Hz|Hz].
 { apply early_window; lia. }
 destruct (Nat.le_gt_cases h z) as [Hh|Hh].
 - apply (lift_window _ _ _ _ _ _ _ a); [exact Hd|exact Hp|lia|apply Hlow; lia|].
   rewrite (carry_small z c h Hc Hh). pose proof (pow_positive a); lia.
 - set (j:=Nat.max (a+1) (h-z)).
   pose proof (Nat.le_max_l (a+1) (h-z)).
   pose proof (Nat.le_max_r (a+1) (h-z)).
   apply (lift_window _ _ _ _ _ _ _ j);
     [exact Hd|exact Hp|unfold j; lia|apply Hhigh; lia|].
   pose proof (carry_large z c h Hc ltac:(lia)).
   pose proof (Nat.pow_le_mono_r 2 (a+1) j ltac:(lia) ltac:(unfold j; lia)).
   pose proof (Nat.pow_le_mono_r 2 (h-z) j ltac:(lia) ltac:(unfold j; lia)).
   replace (h-z) with (h-(z+1)+1) in * by lia.
   rewrite !Nat.pow_add_r in *; change (2^1) with 2 in *.
   pose proof (pow_positive a); lia.
Qed.

End BinaryZero.
End BinaryZero.

Module DeficitWindow.
Module DeficitWindow.
Import DeficitResidues.DeficitResidues BinaryZero.BinaryZero.

Lemma small_window d h p c : pre_deficit d -> h<=3 -> p<2 -> c<2^h ->
 has_zero d h (3*h+6) p c.
Proof.
 intros Hd Hh Hp Hc.
 destruct (Nat.le_gt_cases h 1) as [Hsmall|Hlarge].
 { destruct Hd; apply early_window; lia. }
 assert (Hc8:c<8) by
   (pose proof (Nat.pow_le_mono_r 2 h 3 ltac:(lia) Hh); change (2^3) with 8 in *; lia).
 destruct p as [|p].
 - destruct (low_even d c Hd Hc8) as [Hz|Hz];
     [exists 4|exists 12]; repeat split; try reflexivity; try assumption; lia.
 - replace (S p) with 1 by lia. exists 7; repeat split; try reflexivity; try lia.
   apply low_odd; assumption.
Qed.

Lemma internal_window d : pre_deficit d -> window d.
Proof.
 intro Hd; induction Hd as [v|d v Hd IH]; intros h p c Hp Hc.
 - destruct (Nat.le_gt_cases h 3) as [Hsmall|Hlarge].
   { apply small_window; try assumption; constructor. }
   destruct (Nat.le_gt_cases (h+2) (5*v+3)).
   { apply early_window; lia. }
   apply (large_window _ _ (7*v+6)); try assumption.
   + replace (7*v+6) with ((2*v+3)+(5*v+3)) by lia.
     rewrite (Nat.pow_add_r 2 (2*v+3) (5*v+3)).
     set (x:=2^(2*v+3)); set (y:=2^(5*v+3)).
     assert (0<x) by apply pow_positive. assert (0<y) by apply pow_positive.
     clearbody x y; nia.
   + assert (Nat.max h (7*v+6)<=3*h+4) by (apply Nat.max_lub; lia); lia.
 - destruct (Nat.le_gt_cases h 3) as [Hsmall|Hlarge].
   { apply small_window; try assumption; constructor; assumption. }
   replace (2*v+3) with ((2*v+2)+1) by lia.
   apply phase_window; [exact IH|exact Hp|exact Hc|lia| |].
   + intros; destruct v; lia.
   + intros; destruct (Nat.le_ge_cases (2*v+2+1) (h-(5*v+4)));
       [rewrite Nat.max_r by lia|rewrite Nat.max_l by lia]; lia.
Qed.

Lemma terminal_window d v t h p c : pre_deficit d -> t<=1 -> 2<=h -> p<2 -> c<2^h ->
 has_zero ((2*d+2^(2*v+2)-1)*2^(5*v+t)) h (3*h+9-t) p c.
Proof.
 intros Hd Ht Hh Hp Hc. replace (2*v+2) with ((2*v+1)+1) by lia.
 apply phase_window; [|exact Hp|exact Hc|lia| |].
 - apply internal_window; assumption.
 - intros; destruct v; lia.
 - intros; destruct (Nat.le_ge_cases (2*v+1+1) (h-(5*v+t)));
     [rewrite Nat.max_r by lia|rewrite Nat.max_l by lia]; destruct v; lia.
Qed.

Lemma final_window d v h p c : pre_deficit d -> 2<=h -> p<2 -> c<2^h ->
 exists i, h<=i /\ i<=3*h+8 /\ i mod 2=p /\
 (((2*d+2^(2*v+2)-1)*2^(5*v+1)+c)/2^i) mod 2=0.
Proof.
 intros; replace (3*h+8) with (3*h+9-1) by lia.
 apply terminal_window; lia || assumption.
Qed.

Lemma half_window d v h p c : pre_deficit d -> 2<=h -> p<2 -> c<2^h ->
 exists i, h<=i /\ i<=3*h+9 /\ i mod 2=p /\
 (((2*d+2^(2*v+2)-1)*2^(5*v)+c)/2^i) mod 2=0.
Proof.
 intros; replace (5*v) with (5*v+0) by lia.
 replace (3*h+9) with (3*h+9-0) by lia.
 apply terminal_window; lia || assumption.
Qed.

End DeficitWindow.
End DeficitWindow.
Module TightDeficitClass.
(* The deficit grammar of an odd-wall conversion route.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import OddFuel OddImage OddRoute OdDeficit MarkedDeficit MarkedTrace DeficitResidues.
Import List PeanoNat Lia.
Import ListNotations.
Module TightDeficitClass.

Open Scope nat.

Definition final_deficit d v := (2*d+2^(v*2+2)-1)*2^(v*5+1).

Lemma exact_step L k d u z :
 k+(2^(u+1)-1)+d+1=2^L ->
 OddFuel.OddFuel.grown k z+(2*d+2^(u+2)-1)*2^z+1=2^(L+1+z).
Proof.

 intro H.
 pose proof (OdDeficit.OdDeficit.step_deficit L k d u z ltac:(lia)) as HE.
 rewrite (Nat.pow_add_r 2 z 1) in HE. cbn[Nat.pow] in HE.
 pose proof (Nat.pow_nonzero 2 (u+2) ltac:(lia)). nia.
Qed.

Lemma route_final L k bs L' k' rest :
 OddRoute.OddRoute.route L k bs L' k' rest ->
 forall d, DeficitResidues.DeficitResidues.pre_deficit d -> k+d+1=2^L ->
 exists previous v,
 DeficitResidues.DeficitResidues.pre_deficit previous /\ k'+final_deficit previous v+1=2^L'.
Proof.

 intro Hr. induction Hr; intros d Hd Hbalance.
 - exists d,v. split; [exact Hd|].
   unfold final_deficit. apply exact_step. exact Hbalance.
 - apply (IHHr ((2*d+2^(v*2+3)-1)*2^(v*5+4))).
   + replace (v*2) with (2*v) by lia.
     replace (v*5) with (5*v) by lia.
     apply DeficitResidues.DeficitResidues.PreOdd. exact Hd.
   + pose proof (exact_step L k d (v*2+1) (v*5+4)) as HE.
     replace (v*2+1+1) with (v*2+2) in HE by lia.
     replace (v*2+1+2) with (v*2+3) in HE by lia.
     apply HE. exact Hbalance.

Qed.

Lemma initial_odd_final n v tail L k rest :
 OddRoute.OddRoute.route (n+1+(v*5+3)) (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3))
   tail L k rest -> v*2+2<=n ->
 exists previous last,
 DeficitResidues.DeficitResidues.pre_deficit previous /\ k+final_deficit previous last+1=2^L.
Proof.

 intros Hr Hn.
 apply (route_final _ _ _ _ _ _ Hr ((2^(v*2+3)-3)*2^(v*5+3))).
 - replace (v*2) with (2*v) by lia.
   replace (v*5) with (5*v) by lia.
   apply DeficitResidues.DeficitResidues.PreInitial.
 - pose proof (MarkedDeficit.MarkedDeficit.initial_balance n (v*2+1) (v*5+3) ltac:(lia)) as H.
   unfold MarkedDeficit.MarkedDeficit.initial_deficit in H.
   replace (v*2+1+2) with (v*2+3) in H by lia. exact H.
Qed.

Lemma first_index_unique u v tail rest :
 repeat false u++true::tail=repeat false v++true::rest -> u=v.
Proof.

 gen v. induction u; intros v HE; destruct v; cbn[repeat app] in HE;
   try discriminate; try reflexivity.
 inversion HE. f_equal. apply IHu. assumption.
Qed.

Lemma wall_odd_final n u tail L k rest :
 MarkedTrace.MarkedTrace.wall_route n (repeat false (u*2+1)++true::tail) L k rest ->
 u*2+2<=n ->
 exists previous last,
 DeficitResidues.DeficitResidues.pre_deficit previous /\ k+final_deficit previous last+1=2^L.
Proof.

 intros Hr Hn.
 remember (repeat false (u*2+1)++true::tail) as word eqn:HE in Hr.
 destruct Hr.
 - pose proof (first_index_unique _ _ _ _ HE). lia.
 - pose proof (first_index_unique _ _ _ _ HE) as Hu.
   apply (initial_odd_final _ _ _ _ _ _ H). lia.
Qed.

End TightDeficitClass.
End TightDeficitClass.

Module ZeroComplement.
(* A zero in the subtrahend gives a one in its binary complement.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits CounterFinish WallInvariant MarkerArithmetic GapMarker.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module ZeroComplement.

Lemma zero_bit_residue S i :
 0<S -> ((S-1)/2^i) mod 2=0 ->
 exists r, r<2^i /\ S mod 2^(i+1)=r+1.
Proof.

 intros HS Hz.
 pose proof (Nat.pow_nonzero 2 i ltac:(lia)) as Hp.
 pose proof (Nat.div_mod (S-1) (2^i) Hp) as Hdiv.
 pose proof (Nat.div_mod ((S-1)/2^i) 2 ltac:(lia)) as Hquot.
 rewrite Hz in Hquot.
 pose proof (Nat.mod_upper_bound (S-1) (2^i) Hp) as Hr.
 set (r:=(S-1) mod 2^i).
 set (q:=((S-1)/2^i)/2).
 exists r. split; [exact Hr|].
 assert (HE:S=(r+1)+q*2^(i+1)).
 { unfold r,q. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. }
 rewrite HE,Nat.mod_add by (apply Nat.pow_nonzero;lia).
 apply Nat.mod_small. rewrite Nat.pow_add_r. cbn[Nat.pow]. unfold r. lia.
Qed.

Lemma zero_complement_mod bs S i :
 0<S -> i mod 2=1 -> ((S-1)/2^i) mod 2=0 ->
 (CounterBits.CounterBits.value bs+S) mod 2^(i+1)=0 -> WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros HS Hi Hz Hsum.
 destruct (zero_bit_residue S i HS Hz) as [r [Hr Hres]].
 assert (Hp:0<2^i) by (pose proof (Nat.pow_nonzero 2 i ltac:(lia));lia).
 assert (Hc:0<r+1) by lia.
 assert (Hcd:r+1<2^(i+1)) by (rewrite Nat.pow_add_r;cbn[Nat.pow];lia).
 assert (Hsum':(CounterBits.CounterBits.value bs+(r+1)) mod 2^(i+1)=0).
 { rewrite Nat.add_mod in Hsum by (apply Nat.pow_nonzero;lia).
   rewrite Hres in Hsum.
   rewrite Nat.add_mod by (apply Nat.pow_nonzero;lia).
   rewrite (Nat.mod_small (r+1) (2^(i+1)) Hcd). exact Hsum. }

 pose proof (GapMarker.GapMarker.complement_residue (CounterBits.CounterBits.value bs) (2^(i+1)) (r+1) Hc Hcd Hsum') as Hvalue.
 pose proof (GapMarker.GapMarker.marked_residue_auto bs i (2^i-(r+1))) as Hmark.
 rewrite Hi in Hmark. apply Hmark.
 - clear -Hr Hp. lia.
 - rewrite Hvalue,Nat.pow_add_r. cbn[Nat.pow]. clear -Hr Hp. lia.
Qed.

Lemma zero_complement_multiple bs A J D S i :
 0<S -> i<A -> i<J -> i mod 2=1 ->
 ((S-1)/2^i) mod 2=0 ->
 CounterBits.CounterBits.value bs+S+D*2^J=2^A -> WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros HS HiA HiJ Hi Hz HE.
 apply (zero_complement_mod bs S i); try assumption.
 rewrite (MarkerArithmetic.MarkerArithmetic.power_multiple (i+1) A), (MarkerArithmetic.MarkerArithmetic.power_multiple (i+1) J) in HE by lia.
 replace (D*(2^(J-(i+1))*2^(i+1))) with
   ((D*2^(J-(i+1)))*2^(i+1)) in HE by nia.
 apply (f_equal (fun x=>x mod 2^(i+1))) in HE.
 rewrite Nat.mod_add,Nat.mod_mul in HE by (apply Nat.pow_nonzero;lia).
 exact HE.
Qed.

Lemma zero_complement bs L S i :
 0<S -> i<L -> i mod 2=1 -> ((S-1)/2^i) mod 2=0 ->
 CounterBits.CounterBits.value bs+S=2^L -> WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros HS HiL Hi Hz HE.
 apply (zero_complement_multiple bs L L 0 S i); try assumption. lia.
Qed.

Lemma zero_complement_digits L v S i :
 0<S -> v+S=2^L -> i<L -> i mod 2=1 ->
 ((S-1)/2^i) mod 2=0 -> WallInvariant.WallInvariant.marked 1 (CounterFinish.CounterFinish.digits L v).
Proof.

 intros HS HE HiL Hi Hz.
 apply (zero_complement (CounterFinish.CounterFinish.digits L v) L S i); try assumption.
 rewrite CounterBits.CounterBits.digits_value by lia. exact HE.
Qed.

End ZeroComplement.
End ZeroComplement.

Module TightRecursiveMarker.
(* A zero in an exact conversion deficit preserves the terminal marker.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import DeficitResidues DeficitWindow TightDeficitClass MarkedDeficit ZeroComplement.
Import CounterBits WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module TightRecursiveMarker.

Lemma positive_coefficient b : 2<=b -> 0<2^b-3.
Proof.
 intro Hb. assert (4<=2^b) by (change (2^2<=2^b);apply Nat.pow_le_mono_r;lia). lia.
Qed.

Lemma multiple_width v S E K A :
 0<E -> v+S+E*2^K=2^A -> K<=A.
Proof.
 intros HE Heq. destruct (Nat.le_gt_cases K A) as [Hle|Hgt]; [exact Hle|].
 assert (Hpow:2^A<2^K) by (apply Nat.pow_lt_mono_r;lia).
 clear -HE Heq Hpow. nia.
Qed.

Lemma even_recursive_marker out a L D v T :
 DeficitResidues.DeficitResidues.pre_deficit D -> 0<T -> T<=2^(a*4+1) ->
 CounterBits.CounterBits.value out+(2*T-1)+TightDeficitClass.TightDeficitClass.final_deficit D v+
   MarkedDeficit.MarkedDeficit.initial_deficit (a*10+6) (a*25+14)=2^L -> WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros HD HT HTb HE.
 assert (Hc:2*T-2<2^(a*4+2)).
 { replace (a*4+2) with ((a*4+1)+1) by lia.
   rewrite Nat.pow_add_r. cbn[Nat.pow]. clear -HT HTb. lia. }
 destruct (DeficitWindow.DeficitWindow.final_window D v (a*4+2) 1 (2*T-2) HD ltac:(lia) ltac:(lia) Hc)
   as [i [Hlo [Hhi [Hpar Hbit]]]].

 assert (Hi:i<a*25+14).
 { destruct (Nat.lt_ge_cases i (a*25+14)); [assumption|].
   assert (Ha:a=0) by (clear -Hhi H;lia). subst a.
   assert (Hi:i=14) by (clear -Hhi H;lia). subst i. discriminate Hpar. }
 set (S:=TightDeficitClass.TightDeficitClass.final_deficit D v+(2*T-1)).
 assert (HS:0<S) by (unfold S;clear -HT;lia).
 assert (HE':CounterBits.CounterBits.value out+S+(2^(a*10+8)-3)*2^(a*25+14)=2^L).
 { unfold S. unfold MarkedDeficit.MarkedDeficit.initial_deficit in HE.
   replace (a*10+6+2) with (a*10+8) in HE by lia. clear -HE. lia. }

 assert (Hcoeff:0<2^(a*10+8)-3) by (apply positive_coefficient;clear -a;lia).
 pose proof (multiple_width (CounterBits.CounterBits.value out) S _ _ _ Hcoeff HE') as Hwidth.
 apply (ZeroComplement.ZeroComplement.zero_complement_multiple out L (a*25+14) (2^(a*10+8)-3) S i);
   [exact HS|clear -Hi Hwidth;lia|exact Hi|exact Hpar| |exact HE'].
 assert (HSbit:S-1=(2*D+2^(2*v+2)-1)*2^(5*v+1)+(2*T-2)).
 { unfold S,TightDeficitClass.TightDeficitClass.final_deficit.
   replace (v*2+2) with (2*v+2) by lia.
   replace (v*5+1) with (5*v+1) by (clear -v;lia). set (F:=(2*D+2^(2*v+2)-1)*2^(5*v+1)).
   clearbody F. clear -HT. lia. }
 rewrite HSbit. exact Hbit.
Qed.

Lemma odd_recursive_marker out a L D v T :
 DeficitResidues.DeficitResidues.pre_deficit D -> 0<T -> T<=2^(a*4+3) ->
 CounterBits.CounterBits.value out+(T+3)+(2*D+2^(v*2+2)-1)*2^(v*5)+
   MarkedDeficit.MarkedDeficit.initial_deficit (a*10+11) (a*25+29)=2^L -> WallInvariant.WallInvariant.marked 1 out.
Proof.

 intros HD HT HTb HE.
 assert (Hc:T+2<2^(a*4+4)).
 { assert (8<=2^(a*4+3)) by (change (2^3<=2^(a*4+3));apply Nat.pow_le_mono_r;lia).
   replace (a*4+4) with ((a*4+3)+1) by lia.
   rewrite Nat.pow_add_r. cbn[Nat.pow]. clear -HTb H. lia. }
 destruct (DeficitWindow.DeficitWindow.half_window D v (a*4+4) 1 (T+2) HD ltac:(lia) ltac:(lia) Hc)
   as [i [Hlo [Hhi [Hpar Hbit]]]].

 assert (Hi:i<a*25+29) by (clear -Hhi;lia).
 set (S:=(2*D+2^(v*2+2)-1)*2^(v*5)+(T+3)).
 assert (HS:0<S).
 { unfold S. apply Nat.lt_le_trans with (m:=T+3).
   - clear -T. lia.
   - apply Nat.le_add_l. }
 assert (HE':CounterBits.CounterBits.value out+S+(2^(a*10+13)-3)*2^(a*25+29)=2^L).
 { unfold S. unfold MarkedDeficit.MarkedDeficit.initial_deficit in HE.
   replace (a*10+11+2) with (a*10+13) in HE by lia. clear -HE. lia. }

 assert (Hcoeff:0<2^(a*10+13)-3) by (apply positive_coefficient;clear -a;lia).
 pose proof (multiple_width (CounterBits.CounterBits.value out) S _ _ _ Hcoeff HE') as Hwidth.
 apply (ZeroComplement.ZeroComplement.zero_complement_multiple out L (a*25+29) (2^(a*10+13)-3) S i);
   [exact HS|clear -Hi Hwidth;lia|exact Hi|exact Hpar| |exact HE'].
 assert (HSbit:S-1=(2*D+2^(2*v+2)-1)*2^(5*v)+(T+2)).
 { unfold S. replace (v*2+2) with (2*v+2) by lia.
   replace (v*5) with (5*v) by (clear -v;lia).
   set (F:=(2*D+2^(2*v+2)-1)*2^(5*v)). clearbody F. clear -T. lia. }
 rewrite HSbit. exact Hbit.
Qed.

End TightRecursiveMarker.
End TightRecursiveMarker.

Module TightRecursiveClosure.
(* Closing the ordinary endpoint after recursive odd conversions.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import TerminalClosure TerminalSuccessor TerminalLoose TightEquations TightRecursiveMarker.
Import TightPrimer StrongInvariant TightDeficitClass DeficitResidues MarkedDeficit.
Import CounterBits CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Module TightRecursiveClosure.


Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope nat.

Lemma final_halved d v :
 TightDeficitClass.TightDeficitClass.final_deficit d v=((2*d+2^(v*2+2)-1)*2^(v*5))*2.
Proof.

 unfold TightDeficitClass.TightDeficitClass.final_deficit. rewrite (Nat.pow_add_r 2 (v*5) 1). cbn[Nat.pow]. nia.
Qed.

Lemma ordinary_recursive_close L d v rest k q w :
 3<=L -> DeficitResidues.DeficitResidues.pre_deficit d -> length rest=w*2+1 ->
 k+TightDeficitClass.TightDeficitClass.final_deficit d v+1=2^L ->
 k+1=2*(TightPrimer.TightPrimer.demand rest+q) -> 0<q -> q*4+3<2^(L+1) ->
 exists out, TerminalClosure.TerminalClosure.odd_wall L (w*5+6) q -[mtm]->+ out /\ StrongInvariant.StrongInvariant.strong out.
Proof.

 intros HL Hd Hm Hdef Hfuel Hq Hcoef.
 assert (HT:0<TightPrimer.TightPrimer.demand rest<=2^length rest).
 { unfold TightPrimer.TightPrimer.demand. pose proof (CDPasses.CDPasses.value_bound rest). lia. }
 destruct (mod2 w) as [a Ha|a Ha]; subst w.
 - replace (a*2*5+6) with ((a*5+3)*2) by lia.
   destruct (TerminalSuccessor.TerminalSuccessor.ordinary_even_image L (a*5+3) q ltac:(lia) Hcoef)
     as [out [Hlen [Hlo [Hhi [Hmass Hrun]]]]].
   exists (WallInvariant.WallInvariant.Ed (L+(a*5+3)*7+3) out). split; [exact Hrun|].

   constructor; [exact Hlen|]. destruct Hlen as [Hloose|Htight].
   + apply (TerminalLoose.TerminalLoose.even_loose_marker L (a*5+3) q out); assumption || lia.
   + pose proof (TightEquations.TightEquations.even_tight_equation L (a*5+3) q k
       (TightDeficitClass.TightDeficitClass.final_deficit d v) (TightPrimer.TightPrimer.demand rest) out
       ltac:(lia) ltac:(lia) Hdef Hfuel Htight Hmass) as HE.
     replace ((a*5+3)*2) with (a*10+6) in HE by lia.
     replace ((a*5+3)*5-1) with (a*25+14) in HE by lia.

     apply (TightRecursiveMarker.TightRecursiveMarker.even_recursive_marker out a L d v (TightPrimer.TightPrimer.demand rest)); try assumption; try lia.
     replace (a*4+1) with (length rest) by lia. lia.
 - replace ((1+a*2)*5+6) with ((a*5+5)*2+1) by lia.
   destruct (TerminalSuccessor.TerminalSuccessor.ordinary_odd_image L (a*5+5) q Hq Hcoef)
     as [out [Hlen [Hlo [Hhi [Hmass Hrun]]]]].
   exists (WallInvariant.WallInvariant.Ed (L+(a*5+5)*7+9) out). split; [exact Hrun|].
   constructor; [exact Hlen|]. destruct Hlen as [Hloose|Htight].

   + apply (TerminalLoose.TerminalLoose.odd_loose_marker L (a*5+5) q out); assumption || lia.
   + rewrite final_halved in Hdef.
     pose proof (TightEquations.TightEquations.odd_tight_equation L (a*5+5) q k
       ((2*d+2^(v*2+2)-1)*2^(v*5)) (TightPrimer.TightPrimer.demand rest) out
       ltac:(lia) Hdef Hfuel Htight Hmass) as HE.
     replace ((a*5+5)*2+1) with (a*10+11) in HE by lia.
     replace ((a*5+5)*5+4) with (a*25+29) in HE by lia.
     apply (TightRecursiveMarker.TightRecursiveMarker.odd_recursive_marker out a (L-1) d v (TightPrimer.TightPrimer.demand rest)); try assumption; try lia.

     replace (a*4+3) with (length rest) by lia. lia.
Qed.

End TightRecursiveClosure.
End TightRecursiveClosure.

Module TightStrong.
(* Closure of all marked displaced walls with tight space.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import TightTrace TightDirect TightRecursiveClosure TightDeficitClass TightMarked.
Import MarkedTrace OddRoute StrongInvariant WallInvariant TerminalClosure.
Import List PeanoNat Lia.
Import ListNotations.
Module TightStrong.

Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope nat.

Lemma tight_strong n bs :
 length bs+2=n -> WallInvariant.WallInvariant.marked 1 bs ->
 exists out, WallInvariant.WallInvariant.Ed n bs -[mtm]->+ out /\ StrongInvariant.StrongInvariant.strong out.
Proof.

 intros Hn Hmark.
 destruct (TightTrace.TightTrace.tight_cases n bs Hn Hmark)
   as [L [k [rest [j [q [Hroute [Hlen [HL [Hb [Hmin [Hfuel [Hq [Hcoef Hcases]]]]]]]]]]]]].
 destruct Hcases as [[w [Hw [Hrun Hstrong]]]|[w [Hw Hrun]]].
 - eexists. split; eassumption.
 - destruct (OddRoute.OddRoute.first_true (false::bs) (OddRoute.OddRoute.marked_true _ (TightMarked.TightMarked.marked_false bs Hmark)))
     as [u [tail Hword]].
   destruct (mod2 u) as [v Hv|v Hv]; subst u.
   + apply (TightDirect.TightDirect.tight_direct n bs v tail); assumption.

   + replace (1+v*2) with (v*2+1) in Hword by lia.
     assert (Hroute':MarkedTrace.MarkedTrace.wall_route n (repeat false (v*2+1)++true::tail) L k rest).
     { rewrite <-Hword. exact Hroute. }
     assert (Hcap:v*2+2<=n).
     { pose proof (f_equal (@length bool) Hword) as Hlength.
       rewrite length_app,repeat_length in Hlength. cbn[length] in Hlength. lia. }
     destruct (TightDeficitClass.TightDeficitClass.wall_odd_final _ _ _ _ _ _ Hroute' Hcap)
       as [d [last [Hd Hbalance]]].

     destruct (TightRecursiveClosure.TightRecursiveClosure.ordinary_recursive_close L d last rest k q w
       ltac:(lia) Hd Hw Hbalance Hfuel Hq Hcoef) as [out [Hlast Hstrong]].
     exists out. split; [|exact Hstrong]. eapply progress_trans; eassumption.
Qed.

End TightStrong.
End TightStrong.

Module InitialWall.
(* Entry into the candidate wall family.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.ES_v3.
Import WallInvariant.
Import String List PeanoNat Lia.
Import WallInvariant.WallInvariant.
Open Scope sym.

Lemma initial_wall :
  c0 -[mtm]->* E 6 [false;true;false;true].
Proof.
  unfold E, wall, shifted.
  esx.
Qed.

Lemma initial_wall_invariant : invariant (E 6 [false;true;false;true]).
Proof.
  apply InvE.
  - cbn. lia.
  - exists [false], [false;true]. split; reflexivity.
Qed.

End InitialWall.

Module StrongEntry.
(* The blank-tape entry and the final progress criterion.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import InitialWall StrongInvariant WallInvariant.
Import String List Lia.
Import ListNotations.
Module StrongEntry.
Notation mtm := WallInvariant.WallInvariant.mtm.

Lemma initial_strong : StrongInvariant.StrongInvariant.strong (WallInvariant.WallInvariant.E 6 [false;true;false;true]).
Proof. constructor; [cbn; lia|apply StrongInvariant.StrongInvariant.initial_guard]. Qed.

Lemma closure_nonhalt :
 (forall c, StrongInvariant.StrongInvariant.strong c -> exists c', c -[mtm]->+ c' /\ StrongInvariant.StrongInvariant.strong c') ->
 ~halts mtm c0.
Proof.
 intro Hclosure.
 eapply multistep_nonhalt; [exact InitialWall.initial_wall|].
 apply (progress_nonhalt mtm StrongInvariant.StrongInvariant.strong).
 - intros c Hc. destruct (Hclosure c Hc) as [c' [Hrun Hnext]].
   exists c'. auto.
 - exact initial_strong.
Qed.

Lemma target_mirror :
 flip (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC")=mtm.
Proof.
 apply FunctionalExtensionality.functional_extensionality.
 intros [q s]. destruct q,s; reflexivity.
Qed.

End StrongEntry.
End StrongEntry.

Module StrongClosure.
(* Every wall in the invariant reaches another wall by positive progress.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import StrongInvariant StrongE StrongEdLoose TightStrong StrongEntry WallInvariant.

Module StrongClosure.
Notation mtm := WallInvariant.WallInvariant.mtm.

Lemma strong_progress c : StrongInvariant.StrongInvariant.strong c ->
 exists c', c -[mtm]->+ c' /\ StrongInvariant.StrongInvariant.strong c'.
Proof.
 intro H. destruct H as [n bs Hn Hguard|n bs Hslack Hmarker].
 - apply StrongE.StrongE.strong_E; assumption.
 - destruct Hslack as [Hloose|Htight].
   + apply StrongEdLoose.StrongEdLoose.strong_ed_loose; assumption.
   + apply TightStrong.TightStrong.tight_strong; assumption.
Qed.

Lemma mirrored_nonhalt : ~halts mtm c0.
Proof. apply StrongEntry.StrongEntry.closure_nonhalt. exact strong_progress. Qed.

End StrongClosure.
End StrongClosure.

From BusyCoq Require Import Individual62.
Require Import String.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC").

Theorem nonhalt: ~halts tm c0.
Proof.
 apply flip_halts_c0.
 change (~halts (flip (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC")) c0).
 rewrite StrongEntry.StrongEntry.target_mirror.
 exact StrongClosure.StrongClosure.mirrored_nonhalt.
Qed.

End TM1.

Print Assumptions TM1.nonhalt.

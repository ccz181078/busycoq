(* The machine repeatedly converts a binary counter between shifted digit
   encodings. The invariant records the spare amplifier space and the
   positions of protected one bits.

   Every wall satisfying the invariant makes positive progress to another
   wall. An inductive zero-bit bound on the recursive counter deficit
   preserves a marker after subtraction at arbitrary conversion depth.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Require BusyCoq.Individual62.
Require BusyCoq.DivModCases.
Require BusyCoq.Longitudinal.
Require BusyCoq.ES_v3.
Require String.
Require List.
Require PeanoNat.
Require Lia.
Require BusyCoq.BinaryCounter_v2.
Require NArith.
Require BusyCoq.SimplTape.
Require BusyCoq.ES_v2.
Require Bool.
From Coq Require Import ArithRing.

Module WallInvariant.
(* A candidate wall invariant for a shift-overflow counter.
   The closure theorem is developed separately.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module WallInvariant.

Definition mtm := Eval compute in
  (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC").

Fixpoint normal (bs:list bool) : list Sym :=
  match bs with
  | [] => []
  | b::bs => (if b then [1;0;0;0;0] else [0;0;0;0;0]) ++ normal bs
  end.

Fixpoint shifted (bs:list bool) : list Sym :=
  match bs with
  | [] => []
  | b::bs => (if b then [0;0;0;0;1] else [0;0;0;0;0]) ++ shifted bs
  end.

Definition wall (w:list Sym) : (Q*tape)%type :=
  (0inf <* <[1;1]) <* [0] {{A}}> w *> 0inf.

Definition E n bs := wall ([1;1]^^n ++ shifted bs).
Definition Ed n bs := wall ([1;1]^^n ++ shifted bs ++ [0;0;0;1;0]).
Definition O n bs := wall ([1;1]^^n ++ [1] ++ normal bs).
Definition Od n bs := wall ([1;1]^^n ++ [1] ++ normal bs ++ [0;0;0;0;1]).

Definition marked (parity:nat) (bs:list bool) :=
  exists pre post, bs = pre ++ true::post /\ (length pre mod 2 = parity)%nat.

Definition first_zero (bs:list bool) := exists rest, bs = false::rest.

Inductive invariant : (Q*tape)%type -> Prop :=
| InvE n bs :
    (length bs+2 <= n)%nat -> marked 1 bs -> invariant (E n bs)
| InvEd n bs :
    (length bs+3 <= n)%nat -> invariant (Ed n bs)
| InvO n bs :
    (length bs <= n)%nat -> first_zero bs -> In true bs -> invariant (O n bs)
| InvOd n bs :
    (length bs+1 <= n)%nat -> first_zero bs -> marked 0 bs -> invariant (Od n bs).

End WallInvariant.
End WallInvariant.

Module StrongInvariant.
(* Wall predicates retaining the digit information needed after conversion.
   Their global preservation is developed separately.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Module StrongInvariant.
Open Scope nat.

Definition odd_first bs :=
 exists u tail, bs=repeat false (u*2+1)++true::tail.
Definition adjacent_first bs :=
 exists u tail, 0<u /\ bs=repeat false u++true::true::tail.
Definition close_even_first bs :=
 exists a tail i, 0<a /\ bs=repeat false (10*a)++true::tail /\
 nth i bs false=true /\ i mod 2=1 /\ i<=14*a+3.
Definition digit_guard bs := odd_first bs \/ adjacent_first bs \/ close_even_first bs.

Inductive strong : (Q*tape)%type -> Prop :=
| StrongE n bs : length bs+2<=n -> digit_guard bs -> strong (WallInvariant.WallInvariant.E n bs)
| StrongEd n bs : (length bs+3=n \/ length bs+2=n) ->
    WallInvariant.WallInvariant.marked 1 bs -> strong (WallInvariant.WallInvariant.Ed n bs).

Lemma nth_true_split bs i : nth i bs false=true ->
 exists pre post, bs=pre++true::post /\ length pre=i.
Proof.
 gen i. induction bs as [|b bs IH]; intros i H; destruct i; cbn[nth] in H.
 - discriminate.
 - discriminate.
 - subst b. exists (@nil bool),bs. split; reflexivity.
 - destruct (IH i H) as [pre [post [E Hp]]].
   exists (b::pre),post. cbn[app length]. split; [rewrite E;reflexivity|lia].
Qed.

Lemma nth_true_marked bs i : nth i bs false=true -> i mod 2=1 -> WallInvariant.WallInvariant.marked 1 bs.
Proof.
 intros H Hp. destruct (nth_true_split bs i H) as [pre [post [E Hlen]]].
 exists pre,post. split; [exact E|rewrite Hlen;exact Hp].
Qed.

Lemma guard_marked bs : digit_guard bs -> WallInvariant.WallInvariant.marked 1 bs.
Proof.

 intros [[u [tail E]]|[[u [tail [Hu E]]]|[a [tail [i [Ha [E [Hbit [Hodd Hbound]]]]]]]]].
 - subst bs. exists (repeat false (u*2+1)),tail. split; [reflexivity|].
   rewrite repeat_length. lia.
 - subst bs. destruct (mod2 u) as [v Ev|v Ev]; subst u.
   + exists (repeat false (v*2)++[true]),tail. split.
     * rewrite <-app_assoc. reflexivity.
     * rewrite length_app,repeat_length. cbn[length]. lia.
   + exists (repeat false (1+v*2)),(true::tail). split; [reflexivity|].
     rewrite repeat_length. lia.
 - apply (nth_true_marked bs i); assumption.
Qed.

Lemma nth_append_true bs cs i : nth i bs false=true -> nth i (bs++cs) false=true.
Proof.
 intro H. destruct (nth_true_split bs i H) as [pre [post [E Hlen]]].
 assert (Hi:i<length bs) by (rewrite E,length_app;cbn[length];lia).
 rewrite app_nth1 by exact Hi. exact H.
Qed.

Lemma guard_append bs cs : digit_guard bs -> digit_guard (bs++cs).
Proof.

 intros [[u [tail E]]|[[u [tail [Hu E]]]|[a [tail [i [Ha [E [Hbit [Hodd Hbound]]]]]]]]].
 - left. exists u,(tail++cs). rewrite E,<-app_assoc. reflexivity.
 - right. left. exists u,(tail++cs). split; [exact Hu|].
   rewrite E,<-app_assoc. reflexivity.
 - right. right. exists a,(tail++cs),i. repeat split; try assumption.
   + rewrite E,<-app_assoc. reflexivity.
   + apply nth_append_true. exact Hbit.
Qed.

Lemma initial_guard : digit_guard [false;true;false;true].
Proof. left. exists 0,[false;true]. reflexivity. Qed.

End StrongInvariant.
End StrongInvariant.

Module LocalPasses.
(* Local pass laws for a shift-overflow counter.
   Adapted from mxdys's SOCSSv5, for the table with F1 = 1RC.
   These lemmas alone do not prove nonhalting.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import BusyCoq.Longitudinal BusyCoq.ES_v3.
Import BusyCoq.DivModCases.
Import String List PeanoNat NArith Lia.
Open Scope sym.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac cat :=
  eapply segRLs_sideRLs_concat ||
  eapply segRLs_concat.

Ltac tr :=
  eapply sideRLs_trans ||
  eapply segRLs_trans.

Ltac cat1 H :=
  cat; [apply H|].

Ltac wal := apply segRLs_wall''; esc.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.

Ltac seg_nil :=
  repeat (rewrite Nat.mul_1_r || rewrite Nat.add_sub);
  apply segRLs_nil.

Module Mirrored.

Definition local_tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC").

Notation "c -->* c'" := (c -[ local_tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ local_tm ]->+ c') (at level 40).

Notation ld := [1;1].
Notation d0 := [0;0;0;0;0].
Notation d1 := [1;0;0;0;0].
Notation d1' := [0;0;0;0;1].


Notation hR := (A,[0]).
Notation hRx := (C,[]).
Notation hL := (C,[0]).
Notation h := [(hR,hL)].
Notation hx := [(hRx,hL)].
Notation hR' := (A,[]).
Notation hL' := (B,[]).
Notation h' := [(hR',hL')].

Open Scope nat.

Lemma ld_Incs k:
  segRLs local_tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  am 1 2 k 0 0.
Qed.

Lemma d0_Incs k:
  segRLs local_tm (h'^^(k*2)) (h'^^k) d0 d0.
Proof.
  am 2 1 k 0 0.
Qed.

Lemma d01_Incs k:
  segRLs local_tm (h'^^(k*2+1)) (h'^^k) d0 d1.
Proof.
  am 2 1 k 1 0.
Qed.

Lemma d10_Incs k:
  segRLs local_tm (h'^^(k*2+1)) (h'^^(k+1)) d1 d0.
Proof.
  am 2 1 k 1 1.
Qed.

Lemma d1_Incs k:
  segRLs local_tm (h'^^(k*2)) (h'^^k) d1 d1.
Proof.
  am 2 1 k 0 0.
Qed.

Lemma m0_Incs k:
  segRLs local_tm (h^^k) (h'^^k) [] [].
Proof.
  wal.
Qed.

Lemma lds_Incs k n:
  segRLs local_tm (h^^k) (h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  induction n.
  1: seg_nil.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  cat1 IHn.
  rewrite Nat.pow_add_r.
  applys_eq ld_Incs; flia.
Qed.

Lemma lds_Incs' k n:
  segRLs local_tm (h^^k) (h'^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  rewrite <-(app_nil_r (ld^^n)).
  cat1 lds_Incs.
  wal.
Qed.

Lemma d0s_Incs k n:
  segRLs local_tm (h'^^(k*2^n)) (h'^^k) (d0^^n) (d0^^n).
Proof.
  gen k.
  induction n; intros.
  - seg_nil.
  - cbn[Nat.pow lpow].
    cat.
    2: apply IHn.
    applys_eq d0_Incs; flia.
Qed.

Lemma d01s_Incs k n:
  segRLs local_tm (h'^^((k+1)*2^n-1)) (h'^^k) (d0^^n) (d1^^n).
Proof.
  gen k.
  induction n; intros.
  - seg_nil.
  - cbn[Nat.pow lpow].
    cat.
    2: apply IHn.
    applys_eq d01_Incs; flia.
Qed.


Open Scope sym.
Notation lh := (0inf<*<[1;1]).

Lemma BigStep r r':
  sideRLs local_tm (h^^1) r r' ->
  lh {{{ (hR,R) }}} r -->+
  lh {{{ (hR,R) }}} [1]*>r'.
Proof.
  intros.
  eapply sideRLs_1 in H.
  follow10 H.
  er.
Qed.

End Mirrored.

Definition local_tm := Eval compute in
  (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC").
End LocalPasses.

Module OddNormal.
(* The first conversion of an odd wall with ordinary binary digits.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module OddNormal.
Definition mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation d := [0;0;0;1;0].
Notation ld := [1;1].
Notation h := [((A,[0]),(C,[0]))].
Notation x := [((C,[]),(B,[]))].
Notation y := [((D,[]),(B,[]))].
Notation hx := [((C,[]),(C,[0]))].

Notation one := [1].
Notation z3 := [0;0;0].
Open Scope nat.

Lemma c_zero_even k :
 segRLs mtm (x^^(k*2)) (x^^k) a a.
Proof. am 2 1 k 0 0. Qed.
Lemma c_zero_odd k :
 segRLs mtm (x^^(k*2+1)) (x^^k) a c.
Proof. am 2 1 k 1 0. Qed.
Lemma c_one_even k :
 segRLs mtm (x^^(k*2)) (x^^k) c c.
Proof. am 2 1 k 0 0. Qed.
Lemma c_one_odd k :
 segRLs mtm (x^^(k*2+1)) (x^^(k+1)) c a.
Proof. am 2 1 k 1 1. Qed.

Lemma d_zero_even k :
 segRLs mtm (y^^(k*2)) (y^^k) a a.
Proof. am 2 1 k 0 0. Qed.
Lemma d_zero_odd k :
 segRLs mtm (y^^(k*2+1)) (y^^k) a d.
Proof. am 2 1 k 1 0. Qed.
Lemma d_one_even k :
 segRLs mtm (y^^(k*2)) (y^^k) d d.
Proof. am 2 1 k 0 0. Qed.
Lemma d_one_odd k :
 segRLs mtm (y^^(k*2+1)) (y^^(k+1)) d a.
Proof. am 2 1 k 1 1. Qed.

Lemma one_pair : segRLs mtm (h^^2) x one one.
Proof. esc. Qed.

Lemma one_pairs k : segRLs mtm (h^^(k*2)) (x^^k) one one.
Proof.
 induction k.
 - cbn. constructor.
 - replace (S k*2) with (2+k*2)%nat by lia.
   rewrite lpow_add.
   change (segRLs mtm (h^^2 ++ h^^(k*2)) (x++x^^k) one one).
   eapply segRLs_trans; [apply one_pair|apply IHk].
Qed.

Lemma c_zeros_allones k n :
 segRLs mtm (x^^((k+1)*2^n-1)) (x^^k) (a^^n) (c^^n).
Proof.
 gen k.
 induction n; intros.
 - cbn [Nat.pow lpow].
   replace ((k+1)*1-1)%nat with k by lia.
   apply segRLs_nil.
 - cbn [Nat.pow lpow].
   eapply segRLs_concat.
   2: apply IHn.
   pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
   replace ((k+1)*(2*2^n)-1)%nat with (((k+1)*2^n-1)*2+1)%nat by nia.
   apply c_zero_odd.
Qed.

Lemma prime_first u :
 segRLs mtm (h^^((2^u-1)*2)) []
  (one++a^^u) (one++c^^u).
Proof.
 eapply segRLs_concat.
 - apply one_pairs.
 - pose proof (c_zeros_allones 0 u) as H.
   cbn [Nat.add Nat.mul lpow] in H.
   rewrite Nat.add_0_r in H.
   exact H.
Qed.

Lemma one_expand k :
 segRLs mtm (h^^(1+k)) (hx++h^^(1+k*2)) one ld.
Proof.
 replace (h^^(1+k)) with (h++h^^k) by reflexivity.
 replace (hx++h^^(1+k*2)) with ((hx++h)++h^^(k*2)).
 2: cbn [lpow]; reflexivity.
 eapply @segRLs_trans with (w2:=ld).
 - esc.
 - apply LocalPasses.Mirrored.ld_Incs.
Qed.

Lemma first_conversion u :
 segRLs mtm hx [] (c^^u++b) (one^^(5*u+1)++z3).
Proof.
 induction u.
 - cbn [lpow]. esc.
 - replace (5*S u+1) with (5+(5*u+1)) by lia.
   rewrite lpow_add.
   cbn [lpow].
   change (segRLs mtm hx [] (c ++ (c^^u++b)) ((one^^5) ++ (one^^(5*u+1)++z3))).
   eapply segRLs_concat.
   2: exact IHu.
   esc.
Qed.

Lemma odd_first_reduction u k r r' :
 sideRLs mtm (h^^(1+k*2))
  (one^^(5*u+1) *> z3 *> r) r' ->

 sideRLs mtm (h^^((2^u-1)*2+(1+k)))
  (one *> a^^u *> b *> r) (ld *> r').
Proof.
 intro H.
 rewrite lpow_add.
 eapply @sideRLs_trans with (r2:=one *> c^^u *> b *> r).
 - eapply @segRLs_sideRLs_concat with
     (w1:=one++a^^u) (w2:=one++c^^u) (ls2:=[]).
   + apply prime_first.
   + constructor.
 - eapply segRLs_sideRLs_concat.
   + apply one_expand.
   + eapply @sideRLs_trans with (r2:=one^^(5*u+1) *> z3 *> r).
     * repeat rewrite <-Str_app_assoc.
       eapply @segRLs_sideRLs_concat with
        (w1:=c^^u++b) (w2:=one^^(5*u+1)++z3) (ls2:=[]).
       -- apply first_conversion.
       -- constructor.
     * exact H.
Qed.

End OddNormal.
End OddNormal.

Module CounterRules.
(* Two-counter rules for a shift-overflow machine.
   The binary-counter interface follows mxdys's SOC_2_5_v1.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia PeanoNat String List.
Open Scope sym.

Module CounterRules.

Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0;0;0].
Notation rd1 := [1;0;0;0;0].

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.

Ltac follow_rule H :=
  intros;
  epose proof H as HX;
  cbn[Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *;
  follow10 HX;
  repeat (simpl_rotate || simpl_tape);
  finish.
Definition local_tm := Eval compute in
 (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC").
Notation "c -->* c'" := (c -[local_tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[local_tm]->+ c') (at level 40).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).

Lemma left_increment l r n :
 l <* ld0 <* ld1^^n <| r -->+
 l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma right_increment l r n :
 l |> rd1^^n *> [0] *> r -->+
 l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma left_overflow r n :
 ldh <* ld1^^n <| r -->+
 ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.

Lemma left_counter len n r :
 1+n < 2^len ->
 LC len (1+n) <| r -->+
 LC len n |> r.
Proof.
 intros H.
 apply LBinDec_spec; try lia.
 follow_rule left_increment.
Qed.

Lemma right_counter n l :
 l |> RC n -->+
 l <| RC (1+n).
Proof.
 apply RBinInc_spec.
 follow_rule right_increment.
Qed.

Lemma counter_round len n m :
 1+n < 2^len ->
 LC len (1+n) |> RC m -->+
 LC len n |> RC (1+m).
Proof.
 intros H.
 eapply progress_trans.
 - apply right_counter.
 - apply left_counter; exact H.
Qed.

Lemma counter_rounds len n m k :
 n+k < 2^len ->
 LC len (n+k) |> RC m -->*
 LC len n |> RC (m+k).
Proof.
 gen n m.
 induction k; intros n m H.
 - repeat rewrite Nat.add_0_r. finish.
 - replace (n+S k) with (1+(n+k)) by lia.
   apply progress_evstep.
   eapply progress_evstep_trans.
   + apply counter_round. lia.
   + replace (m+S k) with ((1+m)+k) by lia.
     apply IHk. lia.
Qed.

End CounterRules.
End CounterRules.

Module CounterBatch.
(* Composing a right-pass certificate with the left counter.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import CounterRules WallInvariant.
Import String List PeanoNat Lia.
Import CounterRules.CounterRules WallInvariant.WallInvariant.
Open Scope sym.

Module CounterBatch.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).
Notation p := [((A,[]),(B,[]))].

Lemma left_one len k :
  (1+k < 2^len)%nat ->
  sideLR mtm (B,[]) (A,[])
    (LC len (1+k) <* [0;1]) (LC len k <* [0;1]).
Proof.
  intros Hk r.
  assert (H : (LC len (1+k) <* [0;1]) <{{B}} r -[mtm]->+
              LC len (1+k) <| r) by esx.
  follow10 H.
  apply progress_evstep, left_counter. exact Hk.
Qed.

Lemma left_one_flip len k :
  (1+k < 2^len)%nat ->
  sideRL (flip mtm) (B,[]) (A,[])
    (LC len (1+k) <* [0;1]) (LC len k <* [0;1]).
Proof.
  intros Hk r.
  exact (flip_progress mtm _ _ (left_one len k Hk r)).
Qed.

Lemma left_batch len k amount :
  (k+amount < 2^len)%nat ->
  sideRLs (flip mtm) ([((B,[]),(A,[]))]^^amount)
    (LC len (k+amount) <* [0;1]) (LC len k <* [0;1]).
Proof.
  gen k. induction amount; intros k Hk.
  - rewrite Nat.add_0_r. constructor.
  - replace (k+S amount)%nat with (1+(k+amount))%nat by lia.
    cbn [lpow app]. econstructor.
    + apply left_one_flip. lia.
    + apply IHamount. lia.
Qed.

Lemma right_pass_batch len k amount r r' :
  (k+amount < 2^len)%nat ->
  sideRLs mtm (p^^amount) r r' ->
  LC len (k+amount) |> r -[mtm]->* LC len k |> r'.
Proof.
  intros Hk Hr.
  exact (sideRLs_concat_1 Hr (left_batch len k amount Hk)).
Qed.

End CounterBatch.
End CounterBatch.

Module CounterFinish.
(* Returning from an ordinary counter to a wall configuration.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v3 BusyCoq.DivModCases.
Import CounterRules WallInvariant.
Import String List PeanoNat NArith Lia.
Import CounterRules.CounterRules WallInvariant.WallInvariant.
Open Scope sym.

Module CounterFinish.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).

Lemma return_wall n r :
  LC n 0 <| r -[mtm]->+
  (0inf <* <[1;1]) <* [0] {{A}}> ([1] *> [1;1]^^n *> r).
Proof.
  unfold LC. rewrite BinDec_O.
  esx.
Qed.

Lemma counter_finish n k r :
  (k < 2^n)%nat ->
  LC n k |> RC r -[mtm]->+
  (0inf <* <[1;1]) <* [0] {{A}}> ([1] *> [1;1]^^n *> RC (r+k+1)).
Proof.
  intro Hk.
  eapply evstep_progress_trans.
  - applys_eq (counter_rounds n 0 r k Hk).
  - eapply progress_trans.
    + apply right_counter.
    + replace (1+(r+k))%nat with (r+k+1)%nat by lia.
      apply return_wall.
Qed.

Open Scope nat.

Fixpoint digits (n v:nat) : list bool :=
  match n with
  | 0 => []
  | S n => (v mod 2 =? 1) :: digits n (v/2)
  end.

Lemma digits_length n v : length (digits n v) = n.
Proof. gen v. induction n; cbn; intros; auto. Qed.

Lemma digits_even n v : digits (S n) (v*2) = false::digits n v.
Proof.
  cbn [digits]. rewrite Nat.mod_mul, Nat.div_mul by lia. reflexivity.
Qed.

Lemma digits_odd n v : digits (S n) (v*2+1) = true::digits n v.
Proof.
  cbn [digits].
  rewrite Nat.add_comm, Nat.mod_add by lia.
  replace ((1+v*2)/2) with v by (rewrite Nat.div_add; lia).
  reflexivity.
Qed.

Lemma digits_normal n v :
  v < 2^n -> normal (digits n v) *> 0inf = RC v.
Proof.
  gen v. induction n; intros v Hv.
  - cbn in Hv. assert (v=0) by lia. subst. reflexivity.
  - destruct (mod2 v); subst.
    + rewrite digits_even. cbn [normal].
      rewrite Str_app_assoc, IHn by (cbn in Hv; lia).
      unfold RC. rewrite BinInc_mul2. reflexivity.
    + rewrite Nat.add_comm. rewrite digits_odd. cbn [normal].
      rewrite Str_app_assoc, IHn by (cbn in Hv; lia).
      unfold RC. rewrite BinInc_mul2add1. reflexivity.
Qed.

End CounterFinish.
End CounterFinish.

Module BoundaryRules.
(* Boundary rules for a shift-overflow counter.
   The unchanged conversion interfaces follow mxdys's SOC_2_5_v1.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia PeanoNat String List.
Open Scope sym.

Module BoundaryRules.

Lemma unrotate_ten n (a a0 a1 a2 a3 a4 a5 a6 a7 a8:Sym) r:
 a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a]^^n *> r =
 [a;a0;a1;a2;a3;a4;a5;a6;a7;a8]^^n *> a >> r.
Proof. simpl_rotate. reflexivity. Qed.

Ltac rw_unrotate_0 ::=
 (rewrite lpow_unrotate_1 || rewrite lpow_unrotate_2 ||
  rewrite lpow_unrotate_3 || rewrite lpow_unrotate_4 ||
  rewrite lpow_unrotate_5 || rewrite lpow_unrotate_6 ||
  rewrite unrotate_ten).

Definition local_tm := Eval compute in
 (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC").
Notation "c -->* c'" := (c -[local_tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[local_tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd1 := [1;0;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).

Lemma gap0_even l r n:
 l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
 l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof. es. Qed.

Lemma gap0_odd l r n:
 l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
 l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof. es. Qed.

Lemma gap2_even l r n:
 l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
 l <* ld1 <* ld0^^(n*5+1) |> [1;0;0;0] *> r.
Proof. es. Qed.

Lemma gap2_odd l r n:
 l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
 l <* ld1 <* ld0^^(n*5+4) |> [0;0;0] *> r.
Proof. es. Qed.

Lemma gap3_forward l r n:
 l |> rd1^^n *> [1;0;0;0;1;0;0;0;0] *> r -->+
 l <* [0;1] <* [1]^^(n*5+9) {{A}}> r.
Proof. es. Qed.

Lemma gap3_zero l r n:
 l |> rd1^^n *> [1;0;0;0;1;0;0;0;0;0] *> r -->+
 l <| [0]^^(n*5+9) *> [1] *> r.
Proof. es. Qed.

Lemma gap1_reaches_D1 l r n:
 l |> rd1^^n *> [1;0;1] *> r -->*
 l <* [0;1] <* [1]^^(n*5+2) {{D}}> [1] *> r.
Proof. es. Qed.

Notation hp := [((A,[0]),(C,[0]))].
Notation cp := [((C,[]),(B,[]))].
Notation xp := [((C,[]),(C,[0]))].
Notation dz := [0;0;0;0;0].
Notation ds := [0;0;0;0;1].
Notation ones5 := [1;1;1;1;1].

Ltac bounded :=
 apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.

Lemma conversion_digit:
 segRLs local_tm xp xp ds ones5.
Proof. bounded. Qed.

Lemma conversion_stop:
 segRLs local_tm xp [] rd1 [1;0;0;0].
Proof. bounded. Qed.

Lemma conversion_digits n:
 segRLs local_tm xp xp (ds^^n) (ones5^^n).
Proof.
 induction n.
 - cbn[lpow]. apply segRLs_nil.
 - cbn[lpow]. eapply segRLs_concat.
   + apply conversion_digit.
   + exact IHn.
Qed.

Lemma conversion_stopped n:
 segRLs local_tm xp [] (ds^^n ++ rd1) (ones5^^n ++ [1;0;0;0]).
Proof.
 eapply segRLs_concat.
 - apply conversion_digits.
 - apply conversion_stop.
Qed.

Lemma odd_prefix_x_one:
 segRLs local_tm hp (xp++hp) [1] [1;1].
Proof. bounded. Qed.

Lemma even_prefix_two:
 segRLs local_tm hp (hp^^2) [1;1] [1;1].
Proof. bounded. Qed.

Lemma even_prefix_many k:
 segRLs local_tm (hp^^k) (hp^^(k*2)) [1;1] [1;1].
Proof.
 induction k.
 - cbn[lpow]. constructor.
 - replace (S k) with (1+k) at 1 by lia.
   replace (S k*2) with (2+k*2) by lia.
   repeat rewrite lpow_add.
   eapply segRLs_trans.
   + apply even_prefix_two.
   + exact IHk.
Qed.

Lemma odd_prefix_x k:
 segRLs local_tm (hp^^(k+1)) (xp++hp^^(k*2+1)) [1] [1;1].
Proof.
 replace (k+1) with (1+k) by lia.
 replace (k*2+1) with (1+k*2) by lia.
 repeat rewrite lpow_add.
 replace (xp ++ hp ^^ 1 ++ hp ^^ (k * 2))
   with ((xp++hp)++hp^^(k*2)) by (cbn[lpow]; repeat rewrite app_nil_r; symmetry; apply app_assoc).
 eapply segRLs_trans.
 - apply odd_prefix_x_one.
 - apply even_prefix_many.
Qed.

Lemma odd_prefix_c_two:
 segRLs local_tm (hp^^2) cp [1] [1].
Proof. bounded. Qed.

Lemma odd_prefix_c k:
 segRLs local_tm (hp^^(k*2)) (cp^^k) [1] [1].
Proof.
 induction k.
 - cbn[lpow]. constructor.
 - replace (S k*2) with (2+k*2) by lia.
   replace (S k) with (1+k) by lia.
   repeat rewrite lpow_add.
   eapply segRLs_trans.
   + apply odd_prefix_c_two.
   + exact IHk.
Qed.

Lemma c_zero_two:
 segRLs local_tm (cp^^2) cp dz dz.
Proof. bounded. Qed.

Lemma c_zero_one:
 segRLs local_tm cp [] dz ds.
Proof. bounded. Qed.

Lemma c_zero_even k:
 segRLs local_tm (cp^^(k*2)) (cp^^k) dz dz.
Proof.
 induction k.
 - cbn[lpow]. constructor.
 - replace (S k*2) with (2+k*2) by lia.
   replace (S k) with (1+k) by lia.
   repeat rewrite lpow_add.
   eapply segRLs_trans.
   + apply c_zero_two.
   + exact IHk.
Qed.

Lemma c_zero_odd k:
 segRLs local_tm (cp^^(k*2+1)) (cp^^k) dz ds.
Proof.
 rewrite lpow_add.
 replace (cp^^k : list (DH0*DH0)) with (cp^^k++[] : list (DH0*DH0)) by apply app_nil_r.
 eapply segRLs_trans.
 - apply c_zero_even.
 - cbn[lpow]. apply c_zero_one.
Qed.

Lemma c_fill_zeros k n:
 segRLs local_tm (cp^^((k+1)*2^n-1)) (cp^^k) (dz^^n) (ds^^n).
Proof.
 gen k. induction n; intros.
 - cbn[Nat.pow lpow].
   replace ((k+1)*1-1) with k by lia.
   apply segRLs_nil.
 - cbn[Nat.pow lpow].
   eapply segRLs_concat.
   2: apply IHn.
   pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
   replace ((k+1)*(2*2^n)-1) with (((k+1)*2^n-1)*2+1) by nia.
   apply c_zero_odd.
Qed.

Lemma before_conversion j:
 segRLs local_tm (hp^^((2^j-1)*2)) []
   ([1]++dz^^j) ([1]++ds^^j).
Proof.
 eapply segRLs_concat.
 - apply odd_prefix_c.
 - pose proof (c_fill_zeros 0 j) as H.
   cbn[lpow] in H.
   replace ((0+1)*2^j-1) with (2^j-1) in H by lia.
   exact H.
Qed.

Lemma conversion_side j r:
 sideRLs local_tm xp (ds^^j *> rd1 *> r) (ones5^^j *> [1;0;0;0] *> r).
Proof.
 repeat rewrite <-Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - apply conversion_stopped.
 - constructor.
Qed.

Lemma odd_conversion j q r r':
 sideRLs local_tm (hp^^(q*2+1)) (ones5^^j *> [1;0;0;0] *> r) r' ->
 sideRLs local_tm (hp^^((2^j-1)*2+q+1))
   ([1] *> dz^^j *> rd1 *> r) ([1;1] *> r').
Proof.
 intro H.
 replace ((2^j-1)*2+q+1) with ((2^j-1)*2+(q+1)) by lia.
 rewrite lpow_add.
 eapply @sideRLs_trans with (r2:=[1] *> ds^^j *> rd1 *> r).
 - eapply @segRLs_sideRLs_concat with
     (w1:=[1]++dz^^j) (w2:=[1]++ds^^j) (ls2:=[]).
   + apply before_conversion.
   + constructor.
 - eapply segRLs_sideRLs_concat.
   + apply odd_prefix_x.
   + eapply sideRLs_trans.
     * apply conversion_side.
     * exact H.
Qed.

End BoundaryRules.
End BoundaryRules.

Module OddFuel.
(* Counter-fuel rules for the odd-wall conversion.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.BinaryCounter_v2 BusyCoq.ES_v3.
Import LocalPasses OddNormal CounterRules CounterBatch CounterFinish BoundaryRules WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations CounterRules.CounterRules CounterBatch.CounterBatch.
Open Scope sym.

Module OddFuel.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation d := [0;0;0;1;0].
Notation one := [1].
Notation ld := [1;1].
Notation lh := (0inf <* <[1;1]).
Notation zero := [0].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation g0 := [1;1;0;0;0;0].
Notation g2 := [1;0;0;1;0;0;0;0].
Notation t3 := [1;0;0;1;0].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma scan_ones n r :
 lh <* zero {{A}}> (ld^^n *> r) -[mtm]->*
 LC n (2^n-1) |> r.
Proof.

 unfold LC. rewrite BinDec_full.
 esx.
Qed.

Definition grown k z := (2*k+1)*2^z-1.

Lemma grown_bound L k z :
 k < 2^L -> grown k z+1 < 2^(L+1+z).
Proof.

 intro Hk. unfold grown.
 rewrite Nat.pow_add_r, Nat.pow_add_r.
 cbn [Nat.pow].
 pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia.
Qed.

Lemma grow_left L k z :
 k < 2^L ->
 LC L k <* ld1 <* ld0^^z = LC (L+1+z) (grown k z).
Proof.

 intro Hk. unfold LC, grown.
 replace (2*k) with (k*2) by lia.
 rewrite BinDec_mulpow2sub1.
 - reflexivity.
 - rewrite Nat.pow_add_r, Nat.pow_add_r. cbn [Nat.pow].
   pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia.
Qed.

Lemma p_one_pairs k : segRLs mtm (p^^(k*2)) (x^^k) one one.
Proof.

 induction k.
 - cbn [lpow]. constructor.
 - replace (S k*2) with (2+k*2) by lia.
   rewrite lpow_add.
   change (segRLs mtm (p^^2++p^^(k*2)) (x++x^^k) one one).
   eapply @segRLs_trans with (w2:=one).
   + esc.
   + exact IHk.
Qed.

Lemma prime_one u :
 segRLs mtm (p^^((2^u-1)*2)) [] (one++a^^u) (one++c^^u).
Proof.

 eapply segRLs_concat.
 - apply p_one_pairs.
 - pose proof (OddNormal.c_zeros_allones 0 u) as H.
   cbn [Nat.add Nat.mul lpow] in H.
   rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma prime_gap0 u r :
 sideRLs mtm (p^^((2^u-1)*2))
   (one *> a^^u *> b *> r)
   (b^^u *> g0 *> r).
Proof.

 assert (E : one++c^^u++b = b^^u++g0).
 { induction u.
   - reflexivity.
   - cbn [lpow] in *. cbn [app] in *. congruence. }
 repeat rewrite <-Str_app_assoc.
 rewrite <-E. repeat rewrite Str_app_assoc.
 eapply @segRLs_sideRLs_concat with (w1:=one++a^^u) (w2:=one++c^^u) (ls2:=[]).
 - apply prime_one.
 - constructor.
Qed.

Lemma p_third_one : segRLs mtm p [] d t3.
Proof. esc. Qed.

Lemma prime_gap2 u r :
 sideRLs mtm (p^^(2^(u+1)-1))
   (a^^u *> d *> z3 *> r)
   (b^^u *> g2 *> r).
Proof.

 eapply @segRLs_sideRLs_concat with (ls2:=p).
 - applys_eq (LocalPasses.Mirrored.d01s_Incs 1 u).
   rewrite Nat.pow_add_r. cbn [Nat.pow]. flia.
 - change (sideRLs mtm p (d *> z3 *> r) (t3 *> z3 *> r)).
   eapply @segRLs_sideRLs_concat with (ls2:=[]).
   + apply p_third_one.
   + constructor.
Qed.

Lemma convert_gap0_even L k v r :
 k < 2^L ->
 LC L k |> b^^(v*2) *> g0 *> r -[mtm]->+
 LC (L+1+v*5) (grown k (v*5)) |> r4 *> r.
Proof.

 intro Hk. rewrite <-grow_left by exact Hk.
 apply BoundaryRules.gap0_even.
Qed.

Lemma convert_gap0_odd L k v r :
 k < 2^L ->
 LC L k |> b^^(v*2+1) *> g0 *> r -[mtm]->+
 LC (L+1+(v*5+3)) (grown k (v*5+3)) |> z3 *> r.
Proof.

 intro Hk. rewrite <-grow_left by exact Hk.
 apply BoundaryRules.gap0_odd.
Qed.

Lemma convert_gap2_even L k v r :
 k < 2^L ->
 LC L k |> b^^(v*2) *> g2 *> r -[mtm]->+
 LC (L+1+(v*5+1)) (grown k (v*5+1)) |> r4 *> r.
Proof.

 intro Hk. rewrite <-grow_left by exact Hk.
 apply BoundaryRules.gap2_even.
Qed.

Lemma convert_gap2_odd L k v r :
 k < 2^L ->
 LC L k |> b^^(v*2+1) *> g2 *> r -[mtm]->+
 LC (L+1+(v*5+4)) (grown k (v*5+4)) |> z3 *> r.
Proof.

 intro Hk. rewrite <-grow_left by exact Hk.
 apply BoundaryRules.gap2_odd.
Qed.

Lemma right_pass_finish n k r r' :
 k < 2^n -> sideRLs mtm (p^^(k+1)) r r' ->
 LC n k |> r -[mtm]->+
 lh <* zero {{A}}> (one *> ld^^n *> r').
Proof.

 intros Hk Hr. rewrite lpow_add in Hr.
 destruct (sideRLs_split Hr) as [middle [Hfirst Hlast]].
 eapply evstep_progress_trans.
 - replace k with (0+k) at 1 by lia.
   apply right_pass_batch.
   + cbn [Nat.add]. exact Hk.
   + exact Hfirst.
 - eapply progress_trans.
   + exact (sideRLs_1 _ _ _ _ _ Hlast (LC n 0 <* ([0;1]%sym))).
   + eapply progress_trans.
     * assert (H : (LC n 0 <* ([0;1]%sym)) <{{B}} r' -[mtm]->+
         LC n 0 <{{C}} ([0;1]%sym) *> r') by esx.
       exact H.
     * apply CounterFinish.return_wall.
Qed.

End OddFuel.
End OddFuel.

Module CDPasses.
(* A context-pass addition law for the third-position digit encoding.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses.
Import String List PeanoNat NArith Lia.
Import ListNotations.
Open Scope sym.

Module CDPasses.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation d := [0;0;0;1;0].
Notation x := [((C,[]),(B,[]))].
Notation y := [((D,[]),(B,[]))].

Definition bitval (b:bool) : nat := if b then 1 else 0.
Definition third_digit (b:bool) : list Sym := if b then d else a.
Definition fourth_digit (b:bool) : list Sym := if b then c else a.
Fixpoint third (bs:list bool) : list Sym :=
 match bs with [] => [] | b::bs => third_digit b ++ third bs end.
Fixpoint fourth (bs:list bool) : list Sym :=
 match bs with [] => [] | b::bs => fourth_digit b ++ fourth bs end.

Fixpoint value (bs:list bool) : nat :=
 match bs with [] => 0 | b::bs => bitval b + 2*value bs end.
Fixpoint any (bs:list bool) : bool :=
 match bs with [] => false | b::bs => orb b (any bs) end.

Definition mass (pending:bool) (n:nat) : list (DH0*DH0) :=
 if pending then y ++ x^^(n-1) else x^^n.

Open Scope nat.
Lemma c_zero_even k : segRLs mtm (x^^(k*2)) (x^^k) a a.
Proof. am 2 1 k 0 0. Qed.
Lemma c_zero_odd k : segRLs mtm (x^^(k*2+1)) (x^^k) a c.
Proof. am 2 1 k 1 0. Qed.
Lemma c_phase_hit : segRLs mtm x y d a.
Proof. esc. Qed.
Lemma d_zero : segRLs mtm y [] a d.
Proof. esc. Qed.
Lemma d_one : segRLs mtm y y d a.
Proof. esc. Qed.

Lemma c_phase_even k : k<>0 ->
 segRLs mtm (x^^(k*2)) (y++x^^(k-1)) d c.
Proof.

 intro H.
 replace (k*2) with (1+((k-1)*2+1)) by lia.
 rewrite lpow_add.
 eapply segRLs_trans.
 - apply c_phase_hit.
 - apply c_zero_odd.
Qed.
Lemma c_phase_odd k :
 segRLs mtm (x^^(k*2+1)) (y++x^^k) d a.
Proof.

 replace (k*2+1) with (1+k*2) by lia.
 rewrite lpow_add.
 eapply segRLs_trans.
 - apply c_phase_hit.
 - apply c_zero_even.
Qed.
Lemma dc_zero_even k : k<>0 ->
 segRLs mtm (y++x^^(k*2)) (y++x^^(k-1)) a c.
Proof.

 intro H.
 eapply @segRLs_trans with (ls2:=[]) (w2:=d).
 - apply d_zero.
 - apply c_phase_even; exact H.
Qed.
Lemma dc_zero_odd k :
 segRLs mtm (y++x^^(k*2+1)) (y++x^^k) a a.
Proof.

 eapply @segRLs_trans with (ls2:=[]) (w2:=d).
 - apply d_zero.
 - apply c_phase_odd.
Qed.
Lemma dc_one_even k :
 segRLs mtm (y++x^^(k*2)) (y++x^^k) d a.
Proof.

 eapply segRLs_trans.
 - apply d_one.
 - apply c_zero_even.
Qed.
Lemma dc_one_odd k :
 segRLs mtm (y++x^^(k*2+1)) (y++x^^k) d c.
Proof.

 eapply segRLs_trans.
 - apply d_one.
 - apply c_zero_odd.
Qed.

Lemma mass_even k old bit : k<>0 ->
 segRLs mtm (mass old (k*2)) (mass (orb old bit) k)
   (third_digit bit) (fourth_digit bit).
Proof.

 intro H. destruct old,bit; unfold mass,third_digit,fourth_digit; cbn[orb].
 - replace (k*2-1) with ((k-1)*2+1) by lia. apply dc_one_odd.
 - replace (k*2-1) with ((k-1)*2+1) by lia. apply dc_zero_odd.
 - apply c_phase_even; exact H.
 - apply c_zero_even.
Qed.
Lemma mass_odd k old bit : k<>0 ->
 segRLs mtm (mass old (1+k*2)) (mass (orb old bit) (k+bitval bit))
   (third_digit bit) (fourth_digit (negb bit)).

Proof.

 intro H. destruct old,bit; unfold mass,third_digit,fourth_digit,bitval; cbn[orb negb].
 - replace (1+k*2-1) with (k*2) by lia.
   replace (k+1-1) with k by lia. apply dc_one_even.
 - replace (1+k*2-1) with (k*2) by lia.
   rewrite Nat.add_0_r. apply dc_zero_even; exact H.
 - replace (k+1-1) with k by lia.
   replace (1+k*2) with (k*2+1) by lia. apply c_phase_odd.
 - rewrite Nat.add_0_r.
   replace (1+k*2) with (k*2+1) by lia. apply c_zero_odd.

Qed.

Lemma value_bound bs : value bs < 2^length bs.
Proof.

 induction bs as [|b bs IH]; cbn[length value Nat.pow]; [lia|].
 destruct b; cbn[bitval]; nia.
Qed.

Lemma mass_digits bs old n :
 2^length bs <= n ->
 exists out carry,
 length out = length bs /\
 2^length bs*carry+value out = n+value bs /\
 1<=carry /\
 segRLs mtm (mass old n) (mass (orb old (any bs)) carry)
   (third bs) (fourth out).
Proof.

 gen old n. induction bs as [|bit bs IH]; intros old n Hn.
 - exists (@nil bool),n. cbn[length value third fourth any Nat.pow].
   repeat split; try lia.
   replace (orb old false) with old by (destruct old; reflexivity).
   apply segRLs_nil.
 - assert (Hp:0<2^length bs).
   { pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)); lia. }
   cbn[length Nat.pow] in Hn.
   destruct (mod2 n) as [q E|q E]; subst n.

   + assert (Hq:2^length bs<=q) by nia.
     destruct (IH (orb old bit) q Hq) as [out [carry [Hlen [Hv [Hcarry Hseg]]]]].
     exists (bit::out),carry.
     cbn[length value third fourth any Nat.pow].
     repeat split; try lia; try nia.

     replace (orb old (orb bit (any bs))) with (orb (orb old bit) (any bs))
       by (destruct old,bit; reflexivity).
     eapply segRLs_concat.
     * apply mass_even. nia.
     * exact Hseg.
   + assert (Hq:2^length bs<=q) by nia.
     assert (Hnext:2^length bs<=q+bitval bit) by lia.
     destruct (IH (orb old bit) (q+bitval bit) Hnext)
       as [out [carry [Hlen [Hv [Hcarry Hseg]]]]].
     exists (negb bit::out),carry.

     cbn[length value third fourth any Nat.pow].
     repeat split; try lia.

     * destruct bit; cbn[bitval negb] in *; nia.
     * replace (orb old (orb bit (any bs))) with (orb (orb old bit) (any bs))
         by (destruct old,bit; reflexivity).
       eapply segRLs_concat.
       -- apply mass_odd. nia.
       -- exact Hseg.
Qed.

Definition terminal (pending:bool) : list Sym := if pending then d else c.

Lemma flush_one old :
 sideRLs mtm (mass old 1) 0inf (terminal old *> 0inf).
Proof. destruct old; unfold mass,terminal; cbn[lpow]; esc. Qed.

Lemma mass_flush budget old n :
 0<n<2^budget ->
 exists out : list bool,
 length out < budget /\
 value out+2^length out=n /\
 sideRLs mtm (mass old n) 0inf (fourth out *> terminal old *> 0inf).
Proof.

 gen old n. induction budget as [|budget IH]; intros old n Hn.
 - cbn[Nat.pow] in Hn. lia.
 - destruct (Nat.eq_dec n 1) as [E|E].
   + subst n. exists (@nil bool). cbn[length value fourth Nat.pow].
     repeat split; try lia. apply flush_one.
   + assert (Hn2:2<=n) by lia.
     cbn[Nat.pow] in Hn.
     destruct (mod2 n) as [q He|q He]; subst n.
     * assert (Hq:0<q<2^budget) by nia.
       destruct (IH old q Hq) as [out [Hlen [Hv Hseg]]].

       exists (false::out).
       cbn[length value fourth Nat.pow bitval fourth_digit].
       repeat split; try lia; try nia.

       rewrite Str_app_assoc.
       replace 0inf with (a *> 0inf) at 1 by (st; reflexivity).
       eapply segRLs_sideRLs_concat.
       -- pose proof (mass_even q old false ltac:(lia)) as H.
          rewrite Bool.orb_false_r in H. exact H.
       -- exact Hseg.
     * assert (Hq:0<q<2^budget) by nia.
       destruct (IH old q Hq) as [out [Hlen [Hv Hseg]]].
       exists (true::out).
       cbn[length value fourth Nat.pow bitval fourth_digit].

       repeat split; try lia; try nia.

       rewrite Str_app_assoc.
       replace 0inf with (a *> 0inf) at 1 by (st; reflexivity).
       eapply segRLs_sideRLs_concat.
       -- pose proof (mass_odd q old false ltac:(lia)) as H.
          rewrite Bool.orb_false_r in H. cbn[bitval negb] in H.
          rewrite Nat.add_0_r in H. exact H.
       -- exact Hseg.
Qed.

Lemma value_append left right :
 value (left++right)=value left+2^length left*value right.
Proof.

 induction left as [|b left IH]; cbn[app length value Nat.pow]; [lia|].
 rewrite IH. nia.
Qed.
Lemma fourth_append left right :
 fourth (left++right)=fourth left++fourth right.
Proof.

 induction left as [|b left IH]; cbn[app fourth]; [reflexivity|].
 rewrite IH,app_assoc. reflexivity.
Qed.

Lemma mass_full bs old n z :
 2^length bs<=n -> n+value bs<2^(length bs+z) ->
 exists out : list bool,
 length out<length bs+z /\
 value out+2^length out=n+value bs /\
 sideRLs mtm (mass old n) (third bs *> 0inf)
   (fourth out *> terminal (orb old (any bs)) *> 0inf).
Proof.

 intros Hn Hbound.
 destruct (mass_digits bs old n Hn)
   as [low [carry [Hlen [Hv [Hcarry Hseg]]]]].
 assert (Hp:0<2^length bs).
 { pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)); lia. }
 assert (Hc:0<carry<2^z).
 { rewrite Nat.pow_add_r in Hbound. nia. }
 destruct (mass_flush z (orb old (any bs)) carry Hc)
   as [high [Hhigh [Hvalue Hflush]]].
 exists (low++high).
 rewrite length_app,value_append,Hlen,Nat.pow_add_r.

 split; [lia|]. split; [nia|].
 rewrite fourth_append,Str_app_assoc.

 eapply segRLs_sideRLs_concat; eauto.
Qed.

End CDPasses.
End CDPasses.

Module OddImage.
(* Exact images of odd-wall conversions, with arithmetic bounds explicit.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses OddFuel CDPasses CounterRules CounterBatch WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Module OddImage.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.

Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation ld := [1;1].
Notation one := [1].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma normal_app bs cs : WallInvariant.WallInvariant.normal (bs++cs)=WallInvariant.WallInvariant.normal bs++WallInvariant.WallInvariant.normal cs.
Proof.


 induction bs as [|bit bs IH]; cbn[WallInvariant.WallInvariant.normal app]; [reflexivity|].
 rewrite IH,app_assoc. reflexivity.
Qed.
Lemma normal_zeros n : WallInvariant.WallInvariant.normal (repeat false n)=a^^n.
Proof. induction n; [reflexivity|].
 change (a++WallInvariant.WallInvariant.normal (repeat false n)=a++a^^n). rewrite IHn. reflexivity. Qed.
Lemma phase_three_word bs : z3++WallInvariant.WallInvariant.normal bs=CDPasses.CDPasses.third bs++z3.
Proof.


 induction bs as [|bit bs IH]; [reflexivity|].
 destruct bit; cbn[WallInvariant.WallInvariant.normal CDPasses.CDPasses.third CDPasses.CDPasses.third_digit app]; rewrite <-IH; reflexivity.
Qed.
Lemma phase_three bs : z3 *> WallInvariant.WallInvariant.normal bs *> 0inf=CDPasses.CDPasses.third bs *> 0inf.
Proof.


 rewrite <-Str_app_assoc,phase_three_word,Str_app_assoc. st. reflexivity.
Qed.

Lemma leading_one_C t bs out terminal :
 sideRLs mtm (x^^t) (CDPasses.CDPasses.third bs *> 0inf) (CDPasses.CDPasses.fourth out *> terminal *> 0inf) ->
 sideRLs mtm (p^^(t*2)) (r4 *> WallInvariant.WallInvariant.normal bs *> 0inf)
   (one *> CDPasses.CDPasses.fourth out *> terminal *> 0inf).
Proof.


 intro H.
 change (sideRLs mtm (p^^(t*2)) (one *> z3 *> WallInvariant.WallInvariant.normal bs *> 0inf)
   (one *> CDPasses.CDPasses.fourth out *> terminal *> 0inf)).
 rewrite phase_three.
 eapply segRLs_sideRLs_concat.
 - apply OddFuel.OddFuel.p_one_pairs.
 - exact H.
Qed.

Lemma fuel_C_image L k t bs budget :
 k<2^L -> k+1=t*2 ->
 2^length bs<=t -> t+CDPasses.CDPasses.value bs<2^(length bs+budget) ->
 exists out,
 length out<length bs+budget /\
 CDPasses.CDPasses.value out+2^length out=t+CDPasses.CDPasses.value bs /\
 CounterRules.CounterRules.LC L k |> r4 *> WallInvariant.WallInvariant.normal bs *> 0inf -[mtm]->+
 WallInvariant.WallInvariant.wall (ld^^(L+1)++CDPasses.CDPasses.fourth out++CDPasses.CDPasses.terminal (CDPasses.CDPasses.any bs)).
Proof.


 intros Hk Ht Hmin Hmax.
 destruct (CDPasses.CDPasses.mass_full bs false t budget Hmin Hmax)
   as [out [Hlen [Hval Hrun]]].
 cbn[CDPasses.CDPasses.mass orb] in Hrun.
 exists out. repeat split; try assumption.
 pose proof (leading_one_C t bs out (CDPasses.CDPasses.terminal (CDPasses.CDPasses.any bs)) Hrun) as HR.
 rewrite <-Ht in HR.
 pose proof (OddFuel.OddFuel.right_pass_finish L k _ _ Hk HR) as Hfinish.
 unfold WallInvariant.WallInvariant.wall.
 applys_eq Hfinish; ut; st; simpl_rotate; reflexivity.
Qed.

Definition first_fuel n u := 2^n-1-(2^u-1)*2.

Lemma first_fuel_bounds n u : u+1<=n ->
 first_fuel n u+(2^u-1)*2=2^n-1 /\
 first_fuel n u<2^n.
Proof.


 intro Hn. unfold first_fuel.
 assert (Hpow:2^(u+1)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r in Hpow. cbn[Nat.pow] in Hpow.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
Qed.

Lemma initial_even_entry n v bs : v*2+1<=n ->
 WallInvariant.WallInvariant.O n (repeat false (v*2)++true::bs) -[mtm]->+
 CounterRules.CounterRules.LC (n+1+v*5) (OddFuel.OddFuel.grown (first_fuel n (v*2)) (v*5)) |>
 r4 *> WallInvariant.WallInvariant.normal bs *> 0inf.
Proof.


 intro Hn.
 destruct (first_fuel_bounds n (v*2) Hn) as [He Hb].
 unfold WallInvariant.WallInvariant.O,WallInvariant.WallInvariant.wall.
 rewrite normal_app,normal_zeros.
 cbn[WallInvariant.WallInvariant.normal]. repeat rewrite Str_app_assoc.
 eapply evstep_progress_trans.
 - apply OddFuel.OddFuel.scan_ones.
 - eapply evstep_progress_trans.
   + rewrite <-He.
     apply CounterBatch.CounterBatch.right_pass_batch.
     * rewrite He. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
     * apply OddFuel.OddFuel.prime_gap0.
   + apply OddFuel.OddFuel.convert_gap0_even. exact Hb.
Qed.

Definition first_mass n v :=
 (2*first_fuel n (v*2)+1)*2^(v*5-1).

Lemma first_mass_fuel n v : 0<v ->
 OddFuel.OddFuel.grown (first_fuel n (v*2)) (v*5)+1=first_mass n v*2.
Proof.


 intro Hv. unfold OddFuel.OddFuel.grown,first_mass.
 assert (He:v*5=(v*5-1)+1) by lia.
 rewrite He at 1. rewrite Nat.pow_add_r. cbn[Nat.pow].
 pose proof (Nat.pow_nonzero 2 (v*5-1) ltac:(lia)). nia.
Qed.

Lemma initial_even_image n v bs budget :
 0<v -> v*2+1<=n ->
 2^length bs<=first_mass n v ->
 first_mass n v+CDPasses.CDPasses.value bs<2^(length bs+budget) ->
 exists out,
 length out<length bs+budget /\
 CDPasses.CDPasses.value out+2^length out=first_mass n v+CDPasses.CDPasses.value bs /\
 WallInvariant.WallInvariant.O n (repeat false (v*2)++true::bs) -[mtm]->+
 WallInvariant.WallInvariant.wall (ld^^(n+v*5+2)++CDPasses.CDPasses.fourth out++CDPasses.CDPasses.terminal (CDPasses.CDPasses.any bs)).
Proof.


 intros Hv Hn Hmin Hmax.
 destruct (first_fuel_bounds n (v*2) Hn) as [He Hb].
 assert (Hgrown:OddFuel.OddFuel.grown (first_fuel n (v*2)) (v*5)<2^(n+1+v*5)).
 { pose proof (OddFuel.OddFuel.grown_bound n (first_fuel n (v*2)) (v*5) Hb). lia. }
 destruct (fuel_C_image (n+1+v*5) (OddFuel.OddFuel.grown (first_fuel n (v*2)) (v*5))
   (first_mass n v) bs budget Hgrown (first_mass_fuel n v Hv) Hmin Hmax)
   as [out [Hlen [Hval Hrun]]].
 exists out. repeat split; try assumption.
 replace (n+v*5+2) with ((n+1+v*5)+1) by lia.

 eapply progress_trans.
 - apply initial_even_entry; exact Hn.
 - exact Hrun.
Qed.

End OddImage.
End OddImage.

Module OddRecursion.
(* Recursive gap-two conversion rules for odd ordinary walls.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses OddFuel OddImage CounterRules CounterBatch WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Module OddRecursion.

Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation d := [0;0;0;1;0].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma initial_odd_entry n v bs : v*2+2<=n ->
 WallInvariant.WallInvariant.O n (repeat false (v*2+1)++true::bs) -[mtm]->+
 CounterRules.CounterRules.LC (n+1+(v*5+3)) (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)) |>
 z3 *> WallInvariant.WallInvariant.normal bs *> 0inf.
Proof.

 intro Hn.
 destruct (OddImage.OddImage.first_fuel_bounds n (v*2+1) ltac:(lia)) as [He Hb].
 unfold WallInvariant.WallInvariant.O,WallInvariant.WallInvariant.wall.
 rewrite OddImage.OddImage.normal_app,OddImage.OddImage.normal_zeros.
 cbn[WallInvariant.WallInvariant.normal]. repeat rewrite Str_app_assoc.
 eapply evstep_progress_trans.
 - apply OddFuel.OddFuel.scan_ones.
 - eapply evstep_progress_trans.
   + rewrite <-He.
     apply CounterBatch.CounterBatch.right_pass_batch.
     * rewrite He. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
     * apply OddFuel.OddFuel.prime_gap0.
   + apply OddFuel.OddFuel.convert_gap0_odd. exact Hb.
Qed.

Lemma zero_rotate u : z3++a^^u++b=a^^u++d++z3.
Proof.

 induction u.
 - reflexivity.
 - cbn[lpow]. change (a++(z3++a^^u++b)=a++(a^^u++d++z3)).
   rewrite IHu. reflexivity.
Qed.

Lemma zero_rotate_side u r : z3 *> a^^u *> b *> r=a^^u *> d *> z3 *> r.
Proof.

 pose proof (f_equal (fun w => w *> r) (zero_rotate u)) as E.
 cbv beta in E. repeat rewrite Str_app_assoc in E. exact E.
Qed.

Lemma zero_prime L k u bs r : k+(2^(u+1)-1)<2^L ->
 CounterRules.CounterRules.LC L (k+(2^(u+1)-1)) |> z3 *> WallInvariant.WallInvariant.normal (repeat false u++true::bs) *> r
 -[mtm]->*
 CounterRules.CounterRules.LC L k |> b^^u *> ([1;0;0;1;0;0;0;0]%sym) *> WallInvariant.WallInvariant.normal bs *> r.
Proof.

 intro Hk. rewrite OddImage.OddImage.normal_app,OddImage.OddImage.normal_zeros.
 cbn[WallInvariant.WallInvariant.normal]. repeat rewrite Str_app_assoc.
 rewrite zero_rotate_side.
 apply CounterBatch.CounterBatch.right_pass_batch; [exact Hk|].
 apply OddFuel.OddFuel.prime_gap2.
Qed.

Lemma zero_even_step L k v bs r : k+(2^(v*2+1)-1)<2^L ->
 CounterRules.CounterRules.LC L (k+(2^(v*2+1)-1)) |>
 z3 *> WallInvariant.WallInvariant.normal (repeat false (v*2)++true::bs) *> r -[mtm]->+
 CounterRules.CounterRules.LC (L+1+(v*5+1)) (OddFuel.OddFuel.grown k (v*5+1)) |> r4 *> WallInvariant.WallInvariant.normal bs *> r.
Proof.

 intro Hk. eapply evstep_progress_trans.
 - apply zero_prime. exact Hk.
 - apply OddFuel.OddFuel.convert_gap2_even. lia.
Qed.

Lemma zero_odd_step L k v bs r : k+(2^(v*2+2)-1)<2^L ->
 CounterRules.CounterRules.LC L (k+(2^(v*2+2)-1)) |>
 z3 *> WallInvariant.WallInvariant.normal (repeat false (v*2+1)++true::bs) *> r -[mtm]->+
 CounterRules.CounterRules.LC (L+1+(v*5+4)) (OddFuel.OddFuel.grown k (v*5+4)) |> z3 *> WallInvariant.WallInvariant.normal bs *> r.
Proof.

 intro Hk. replace (v*2+2) with ((v*2+1)+1) in * by lia.
 eapply evstep_progress_trans.
 - apply zero_prime. exact Hk.
 - apply OddFuel.OddFuel.convert_gap2_odd. lia.
Qed.

Lemma grown_odd k z : 0<z -> OddFuel.OddFuel.grown k z mod 2=1.
Proof.

 intro Hz. unfold OddFuel.OddFuel.grown.
 destruct z as [|z]; [lia|].
 cbn[Nat.pow].
 pose proof (Nat.pow_nonzero 2 z ltac:(lia)).
 replace ((2*k+1)*(2*2^z)-1) with (((2*k+1)*2^z-1)*2+1) by nia.
 rewrite Nat.add_comm,Nat.mod_add by lia. reflexivity.
Qed.

Lemma remaining_lower k u m : 2^(u+1+m)-1<=k ->
 2^(u+1)-1<=k /\
 2^(u+1)*(2^m-1)<=k-(2^(u+1)-1).
Proof.

 intro Hk. rewrite Nat.pow_add_r in Hk.
 pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)). nia.
Qed.

Lemma grown_lower k u m z :
 2^(u+1)*(2^m-1)<=k -> 0<z -> 2^m-1<=OddFuel.OddFuel.grown k z.
Proof.

 intros Hk Hz. unfold OddFuel.OddFuel.grown.
 pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)).
 assert (Htwo:2<=2^z).
 { destruct z; [lia|]. cbn[Nat.pow]. pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia. }
 nia.
Qed.

End OddRecursion.
End OddRecursion.

Module OddRoute.
(* Finite conversion paths through an ordinary digit word.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import OddFuel OddImage OddRecursion CounterRules WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Module OddRoute.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].

Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Inductive route : nat -> nat -> list bool -> nat -> nat -> list bool -> Prop :=
| RouteEven L k v tail :
 route L (k+(2^(v*2+1)-1)) (repeat false (v*2)++true::tail)
   (L+1+(v*5+1)) (OddFuel.OddFuel.grown k (v*5+1)) tail
| RouteOdd L k v tail L' k' rest :
 route (L+1+(v*5+4)) (OddFuel.OddFuel.grown k (v*5+4)) tail L' k' rest ->
 route L (k+(2^(v*2+2)-1)) (repeat false (v*2+1)++true::tail)
   L' k' rest.

Lemma route_run L k bs L' k' rest r :
 route L k bs L' k' rest -> k<2^L ->
 CounterRules.CounterRules.LC L k |> z3 *> WallInvariant.WallInvariant.normal bs *> r -[mtm]->+
 CounterRules.CounterRules.LC L' k' |> r4 *> WallInvariant.WallInvariant.normal rest *> r.
Proof.


 intros H. induction H; intro Hk.
 - apply OddRecursion.OddRecursion.zero_even_step. exact Hk.
 - eapply progress_trans.
   + apply OddRecursion.OddRecursion.zero_odd_step. exact Hk.
   + apply IHroute.
     pose proof (OddFuel.OddFuel.grown_bound L k (v*5+4) ltac:(lia)). lia.
Qed.

Lemma route_bound L k bs L' k' rest :
 route L k bs L' k' rest -> k<2^L -> k'+1<2^L' /\ k' mod 2=1.
Proof.


 intros H. induction H; intro Hk.
 - split.
   + apply OddFuel.OddFuel.grown_bound. lia.
   + apply OddRecursion.OddRecursion.grown_odd. lia.
 - apply IHroute. pose proof (OddFuel.OddFuel.grown_bound L k (v*5+4) ltac:(lia)). lia.
Qed.

Lemma route_dimensions L k bs L' k' rest :
 route L k bs L' k' rest ->
 exists j, length bs=2*j+1+length rest /\ L'=L+5*j+2.
Proof.


 intro H. induction H.
 - exists v. rewrite length_app,repeat_length. cbn[length]. lia.
 - destruct IHroute as [j [Hlen HL]].
   exists (v+1+j). rewrite length_app,repeat_length. cbn[length]. lia.
Qed.

Lemma first_true bs : In true bs -> exists u tail, bs=repeat false u++true::tail.
Proof.


 induction bs as [|b bs IH]; intro H.
 - inversion H.
 - destruct b.
   + exists 0,bs. reflexivity.
   + destruct H as [H|H]; [discriminate|].
     destruct (IH H) as [u [tail E]].
     exists (S u),tail. cbn[repeat]. rewrite E. reflexivity.
Qed.

Lemma marked_true bs : WallInvariant.WallInvariant.marked 0 bs -> In true bs.
Proof.


 intros [pre [post [E Hp]]]. rewrite E.
 apply in_or_app. right. cbn. auto.
Qed.

Lemma marked_drop_pair b bs : WallInvariant.WallInvariant.marked 0 (false::b::bs) -> WallInvariant.WallInvariant.marked 0 bs.
Proof.


 intros [pre [post [E Hp]]].
 destruct pre as [|a [|a' pre]].
 - discriminate E.
 - cbn[length] in Hp. discriminate Hp.
 - inversion E; subst.
   exists pre,post. split; [reflexivity|].
   cbn[length] in Hp.
   replace (S (S (length pre))) with (length pre+1*2) in Hp by lia.
   rewrite Nat.mod_add in Hp by lia. exact Hp.
Qed.

Lemma marked_after_odd v bs :
 WallInvariant.WallInvariant.marked 0 (repeat false (v*2+1)++true::bs) -> WallInvariant.WallInvariant.marked 0 bs.
Proof.


 induction v; intro H.
 - cbn[repeat] in H. apply (marked_drop_pair true bs H).
 - replace (S v*2+1) with (S (S (v*2+1))) in H by lia.
   cbn[repeat app] in H.
   apply IHv. eapply marked_drop_pair. exact H.
Qed.

Lemma grown_lower_double k u m z :
 2^(u+1)*(2^m-1)<=k -> 0<z -> 2^(m+1)-1<=OddFuel.OddFuel.grown k z.
Proof.


 intros Hk Hz. unfold OddFuel.OddFuel.grown.
 rewrite Nat.pow_add_r. cbn[Nat.pow].
 assert (Hu:2<=2^(u+1)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow].
   pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia. }
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)).
 assert (Htwo:2<=2^z).
 { destruct z; [lia|]. cbn[Nat.pow]. pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia. }
 nia.
Qed.

Lemma marked_route_bounded bound :
 forall bs L k,
 length bs<=bound -> WallInvariant.WallInvariant.marked 0 bs -> 2^length bs-1<=k ->
 exists L' k' rest,
 route L k bs L' k' rest /\ 2^(length rest+1)-1<=k'.
Proof.


 induction bound as [|bound IH]; intros bs L k Hlen Hmark Hfuel.
 - assert (bs=[]) by (apply length_zero_iff_nil; lia). subst bs.
   destruct (marked_true [] Hmark).
 - destruct (first_true bs (marked_true bs Hmark)) as [u [tail E]]. subst bs.
   rewrite length_app,repeat_length in Hlen,Hfuel. cbn[length] in Hlen,Hfuel.
   replace (u+S (length tail)) with (u+1+length tail) in Hfuel by lia.
   destruct (OddRecursion.OddRecursion.remaining_lower k u (length tail) Hfuel) as [Hprime Hremain].
   set (rem:=k-(2^(u+1)-1)).

   assert (Hdecomp:k=rem+(2^(u+1)-1)) by (unfold rem; lia).
   destruct (mod2 u) as [v Eu|v Eu]; subst u.
   + exists (L+1+(v*5+1)),(OddFuel.OddFuel.grown rem (v*5+1)),tail.
     split.
     * rewrite Hdecomp. constructor.
     * apply (grown_lower_double rem (v*2) (length tail) (v*5+1)); [exact Hremain|lia].
   + replace (1+v*2) with (v*2+1) in * by lia.
     assert (HremainR:2^((v*2+1)+1)*(2^length tail-1)<=rem).
     { unfold rem. replace (1+v*2) with (v*2+1) by lia. exact Hremain. }

     assert (Htail:WallInvariant.WallInvariant.marked 0 tail) by (apply marked_after_odd in Hmark; exact Hmark).
     assert (Hremain':2^length tail-1<=OddFuel.OddFuel.grown rem (v*5+4)).
     { apply (OddRecursion.OddRecursion.grown_lower rem (v*2+1) (length tail) (v*5+4)); [exact HremainR|lia]. }
     destruct (IH tail (L+1+(v*5+4)) (OddFuel.OddFuel.grown rem (v*5+4)) ltac:(lia) Htail Hremain')
       as [L' [k' [rest [Hroute Hlower]]]].
     exists L',k',rest. split; [|exact Hlower].
     rewrite Hdecomp. replace ((v*2+1)+1) with (v*2+2) by lia.

     apply RouteOdd. exact Hroute.
Qed.

Lemma marked_route L k bs :
 WallInvariant.WallInvariant.marked 0 bs -> 2^length bs-1<=k ->
 exists L' k' rest,
 route L k bs L' k' rest /\ 2^(length rest+1)-1<=k'.
Proof.


 intros Hmark Hfuel.
 apply (marked_route_bounded (length bs) bs L k); [lia|exact Hmark|exact Hfuel].
Qed.

Lemma zero_marked_exit L k bs r :
 WallInvariant.WallInvariant.marked 0 bs -> 2^length bs-1<=k -> k<2^L ->
 exists L' k' rest j,
 route L k bs L' k' rest /\
 length bs=2*j+1+length rest /\ L'=L+5*j+2 /\
 2^(length rest+1)-1<=k' /\ k'+1<2^L' /\ k' mod 2=1 /\
 CounterRules.CounterRules.LC L k |> z3 *> WallInvariant.WallInvariant.normal bs *> r -[mtm]->+
 CounterRules.CounterRules.LC L' k' |> r4 *> WallInvariant.WallInvariant.normal rest *> r.
Proof.


 intros Hmark Hfuel Hbound.
 destruct (marked_route L k bs Hmark Hfuel) as [L' [k' [rest [Hroute Hlower]]]].
 destruct (route_dimensions _ _ _ _ _ _ Hroute) as [j [Hlen HL]].
 destruct (route_bound _ _ _ _ _ _ Hroute Hbound) as [Hb Ho].
 exists L',k',rest,j. repeat split; try assumption.
 apply route_run; assumption.
Qed.

End OddRoute.
End OddRoute.

Module OddMarkedEntry.
(* Reaching the C-pass phase from a marked odd wall.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import OddFuel OddImage OddRecursion OddRoute CounterRules CounterBatch WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.
Module OddMarkedEntry.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation ld := [1;1].
Notation one := [1].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Definition odd_wall n bs r :=
 (0inf <* <[1;1]) <* [0] {{A}}> (ld^^n *> one *> WallInvariant.WallInvariant.normal bs *> r).
Open Scope nat.

Lemma even_entry n v bs r : v*2+1<=n ->
 odd_wall n (repeat false (v*2)++true::bs) r -[mtm]->+
 CounterRules.CounterRules.LC (n+1+v*5) (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2)) (v*5)) |>
 r4 *> WallInvariant.WallInvariant.normal bs *> r.
Proof.


 intro Hn. destruct (OddImage.OddImage.first_fuel_bounds n (v*2) Hn) as [He Hb].
 unfold odd_wall. rewrite OddImage.OddImage.normal_app,OddImage.OddImage.normal_zeros.
 cbn[WallInvariant.WallInvariant.normal]. repeat rewrite Str_app_assoc.
 eapply evstep_progress_trans.
 - apply OddFuel.OddFuel.scan_ones.
 - eapply evstep_progress_trans.
   + rewrite <-He. apply CounterBatch.CounterBatch.right_pass_batch.
     * rewrite He. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
     * apply OddFuel.OddFuel.prime_gap0.
   + apply OddFuel.OddFuel.convert_gap0_even. exact Hb.
Qed.

Lemma odd_entry n v bs r : v*2+2<=n ->
 odd_wall n (repeat false (v*2+1)++true::bs) r -[mtm]->+
 CounterRules.CounterRules.LC (n+1+(v*5+3)) (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)) |>
 z3 *> WallInvariant.WallInvariant.normal bs *> r.
Proof.


 intro Hn. destruct (OddImage.OddImage.first_fuel_bounds n (v*2+1) ltac:(lia)) as [He Hb].
 unfold odd_wall. rewrite OddImage.OddImage.normal_app,OddImage.OddImage.normal_zeros.
 cbn[WallInvariant.WallInvariant.normal]. repeat rewrite Str_app_assoc.
 eapply evstep_progress_trans.
 - apply OddFuel.OddFuel.scan_ones.
 - eapply evstep_progress_trans.
   + rewrite <-He. apply CounterBatch.CounterBatch.right_pass_batch.
     * rewrite He. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
     * apply OddFuel.OddFuel.prime_gap0.
   + apply OddFuel.OddFuel.convert_gap0_odd. exact Hb.
Qed.

Lemma initial_margin n u m z :
 u+m+2<=n -> 3<=z ->
 2^(m+3)-1<=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n u) z.
Proof.


 intros Hn Hz.
 destruct (OddImage.OddImage.first_fuel_bounds n u ltac:(lia)) as [He Hb].
 assert (Hcap:2^(u+m+2)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 repeat rewrite Nat.pow_add_r in Hcap. cbn[Nat.pow] in Hcap.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)).
 assert (Hk:2^m<=OddImage.OddImage.first_fuel n u) by nia.
 assert (Hzpow:8<=2^z).
 { change (2^3<=2^z). apply Nat.pow_le_mono_r; lia. }
 unfold OddFuel.OddFuel.grown. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
Qed.

Lemma route_margin extra L k bs L' k' rest :
 OddRoute.OddRoute.route L k bs L' k' rest ->
 2^(length bs+extra)-1<=k -> 2^(length rest+extra)-1<=k'.
Proof.


 intro Hroute. induction Hroute; intro Hfuel.
 - rewrite length_app,repeat_length in Hfuel. cbn[length] in Hfuel.
   replace (v*2+S (length tail)+extra) with (v*2+1+(length tail+extra)) in Hfuel by lia.
   destruct (OddRecursion.OddRecursion.remaining_lower (k+(2^(v*2+1)-1)) (v*2) (length tail+extra) Hfuel)
     as [_ Hremain].
   rewrite Nat.add_sub in Hremain.
   apply (OddRecursion.OddRecursion.grown_lower k (v*2) (length tail+extra) (v*5+1)); [exact Hremain|lia].
 - apply IHHroute.
   rewrite length_app,repeat_length in Hfuel. cbn[length] in Hfuel.

   replace (v*2+1+S (length tail)+extra) with ((v*2+1)+1+(length tail+extra)) in Hfuel by lia.
   replace (v*2+2) with ((v*2+1)+1) in Hfuel by lia.
   destruct (OddRecursion.OddRecursion.remaining_lower (k+(2^((v*2+1)+1)-1)) (v*2+1) (length tail+extra) Hfuel)
     as [_ Hremain].
   rewrite Nat.add_sub in Hremain.
   apply (OddRecursion.OddRecursion.grown_lower k (v*2+1) (length tail+extra) (v*5+4)); [exact Hremain|lia].
Qed.

Lemma marked_entry n bs r :
 WallInvariant.WallInvariant.first_zero bs -> WallInvariant.WallInvariant.marked 0 bs -> length bs+1<=n ->
 exists L k rest j,
 length bs=2*j+1+length rest /\ L=n+5*j+1 /\
 k mod 2=1 /\ k+1<2^L /\ 2^(length rest+3)-1<=k /\
 odd_wall n bs r -[mtm]->+ CounterRules.CounterRules.LC L k |> r4 *> WallInvariant.WallInvariant.normal rest *> r.
Proof.


 intros Hzero Hmark Hlen.
 destruct (OddRoute.OddRoute.first_true bs (OddRoute.OddRoute.marked_true bs Hmark)) as [u [tail E]]. subst bs.
 rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
 assert (Hu:0<u).
 { destruct Hzero as [rest Hzero]. destruct u; [discriminate Hzero|lia]. }
 destruct (mod2 u) as [v Eu|v Eu]; subst u.
 - exists (n+1+v*5),(OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2)) (v*5)),tail,v.
   rewrite length_app,repeat_length. cbn[length].
   repeat split.
   + lia.
   + lia.

   + apply OddRecursion.OddRecursion.grown_odd. lia.
   + apply OddFuel.OddFuel.grown_bound. apply OddImage.OddImage.first_fuel_bounds. lia.
   + apply initial_margin; lia.
   + apply even_entry. lia.
 - replace (1+v*2) with (v*2+1) in * by lia.
   assert (Htail:WallInvariant.WallInvariant.marked 0 tail) by (apply OddRoute.OddRoute.marked_after_odd in Hmark; exact Hmark).
   set (L0:=n+1+(v*5+3)).
   set (k0:=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)).
   assert (Hmargin:2^(length tail+3)-1<=k0) by (unfold k0; apply initial_margin; lia).
   assert (Hbasic:2^length tail-1<=k0).
   { assert (2^length tail<=2^(length tail+3)) by (apply Nat.pow_le_mono_r; lia). lia. }

   assert (Hcap:k0+1<2^L0).
   { unfold k0,L0. apply OddFuel.OddFuel.grown_bound. apply OddImage.OddImage.first_fuel_bounds. lia. }
   destruct (OddRoute.OddRoute.marked_route L0 k0 tail Htail Hbasic)
     as [L' [k' [rest [Hroute Hlower]]]].
   destruct (OddRoute.OddRoute.route_dimensions _ _ _ _ _ _ Hroute) as [j [Hdim HL]].
   destruct (OddRoute.OddRoute.route_bound _ _ _ _ _ _ Hroute ltac:(lia)) as [Hbound Hodd].
   exists L',k',rest,(v+1+j).
   rewrite length_app,repeat_length. cbn[length].
   repeat split.
   + lia.
   + unfold L0 in HL. lia.

   + exact Hodd.
   + exact Hbound.
   + apply (route_margin 3 _ _ _ _ _ _ Hroute Hmargin).
   + eapply progress_trans.
     * apply odd_entry. lia.
     * apply OddRoute.OddRoute.route_run; [exact Hroute|]. change (k0<2^L0). lia.
Qed.

End OddMarkedEntry.
End OddMarkedEntry.

Module MarkedTrace.
(* Exact conversion histories from marked odd walls.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import OddFuel OddImage OddRecursion OddRoute OddMarkedEntry CounterRules WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module MarkedTrace.
Notation mtm := WallInvariant.WallInvariant.mtm.
Open Scope sym.
Notation r4 := [1;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Inductive wall_route : nat -> list bool -> nat -> nat -> list bool -> Prop :=
| WallEven n v tail :
 wall_route n (repeat false (v*2)++true::tail)
  (n+1+v*5) (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2)) (v*5)) tail
| WallOdd n v tail L k rest :
 OddRoute.OddRoute.route (n+1+(v*5+3)) (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)) tail L k rest ->
 wall_route n (repeat false (v*2+1)++true::tail) L k rest.

Lemma first_zero_prefix u tail :
 WallInvariant.WallInvariant.first_zero (repeat false u++true::tail) -> 0<u.
Proof.

 intros [rest E]. destruct u; [discriminate E|lia].
Qed.

Lemma initial_margin4 n u m z :
 u+m+2<=n -> 3<=z -> 2^(m+4)-1<=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n u) z.
Proof.

 intros Hn Hz.
 destruct (OddImage.OddImage.first_fuel_bounds n u ltac:(lia)) as [He Hb].

 assert (Hcap:2^(u+m+2)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 repeat rewrite Nat.pow_add_r in Hcap. cbn[Nat.pow] in Hcap.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)).

 assert (Hk:2^m<=OddImage.OddImage.first_fuel n u) by nia.

 assert (Hzpow:8<=2^z).
 { change (2^3<=2^z). apply Nat.pow_le_mono_r; lia. }
 unfold OddFuel.OddFuel.grown. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
Qed.

Lemma route_dimensions n bs L k rest : wall_route n bs L k rest ->
 exists j, length bs=2*j+1+length rest /\ L=n+5*j+1.
Proof.

 intro Hroute. destruct Hroute.
 - exists v. rewrite length_app,repeat_length. cbn[length]. split; lia.
 - destruct (OddRoute.OddRoute.route_dimensions _ _ _ _ _ _ H) as [j [Hlen HL]].
   exists (v+1+j). rewrite length_app,repeat_length. cbn[length]. split; lia.
Qed.

Lemma route_run n bs L k rest r :
 wall_route n bs L k rest -> length bs+1<=n ->
 OddMarkedEntry.OddMarkedEntry.odd_wall n bs r -[mtm]->+ CounterRules.CounterRules.LC L k |> r4 *> WallInvariant.WallInvariant.normal rest *> r.
Proof.

 intros Hroute Hlen. destruct Hroute.
 - apply OddMarkedEntry.OddMarkedEntry.even_entry. rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen. lia.
 - rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   eapply progress_trans.
   + apply OddMarkedEntry.OddMarkedEntry.odd_entry. lia.
   + apply OddRoute.OddRoute.route_run; [exact H|].
     pose proof (OddFuel.OddFuel.grown_bound n (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)
       ltac:(apply OddImage.OddImage.first_fuel_bounds; lia)). lia.
Qed.

Lemma route_bounds n bs L k rest :
 wall_route n bs L k rest -> WallInvariant.WallInvariant.first_zero bs -> length bs+1<=n ->
 k+1<2^L /\ k mod 2=1.
Proof.

 intros Hroute Hzero Hlen. destruct Hroute.
 - apply first_zero_prefix in Hzero.
   rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   split.
   + apply OddFuel.OddFuel.grown_bound. apply OddImage.OddImage.first_fuel_bounds. lia.
   + apply OddRecursion.OddRecursion.grown_odd. lia.
 - rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   apply (OddRoute.OddRoute.route_bound _ _ _ _ _ _ H).
   pose proof (OddFuel.OddFuel.grown_bound n (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)
     ltac:(apply OddImage.OddImage.first_fuel_bounds; lia)). lia.
Qed.

Lemma route_margin4 n bs L k rest :
 wall_route n bs L k rest -> WallInvariant.WallInvariant.first_zero bs -> length bs+1<=n ->
 2^(length rest+4)-1<=k.
Proof.

 intros Hroute Hzero Hlen. destruct Hroute.
 - apply first_zero_prefix in Hzero.
   rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   apply initial_margin4; lia.
 - rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   apply (OddMarkedEntry.OddMarkedEntry.route_margin 4 _ _ _ _ _ _ H).
   apply initial_margin4; lia.
Qed.

Lemma marked_route_exists n bs :
 WallInvariant.WallInvariant.first_zero bs -> WallInvariant.WallInvariant.marked 0 bs -> length bs+1<=n ->
 exists L k rest, wall_route n bs L k rest.
Proof.

 intros Hzero Hmark Hlen.
 destruct (OddRoute.OddRoute.first_true bs (OddRoute.OddRoute.marked_true bs Hmark)) as [u [tail E]]. subst bs.
 rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
 destruct (mod2 u) as [v Eu|v Eu]; subst u.
 - eexists; eexists; eexists. constructor.
 - replace (1+v*2) with (v*2+1) in * by lia.

   assert (Htail:WallInvariant.WallInvariant.marked 0 tail) by (apply OddRoute.OddRoute.marked_after_odd in Hmark; exact Hmark).
   set (L0:=n+1+(v*5+3)).
   set (k0:=OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3)).

   assert (Hmargin:2^(length tail+4)-1<=k0) by (unfold k0; apply initial_margin4; lia).

   assert (Hbasic:2^length tail-1<=k0).
   { assert (2^length tail<=2^(length tail+4)) by (apply Nat.pow_le_mono_r; lia). lia. }
   destruct (OddRoute.OddRoute.marked_route L0 k0 tail Htail Hbasic)
     as [L [k [rest [Hroute Hlower]]]].
   exists L,k,rest. apply WallOdd. exact Hroute.
Qed.

Lemma marked_entry_trace n bs r :
 WallInvariant.WallInvariant.first_zero bs -> WallInvariant.WallInvariant.marked 0 bs -> length bs+1<=n ->
 exists L k rest j,
 wall_route n bs L k rest /\
 length bs=2*j+1+length rest /\ L=n+5*j+1 /\
 k mod 2=1 /\ k+1<2^L /\ 2^(length rest+4)-1<=k /\
 OddMarkedEntry.OddMarkedEntry.odd_wall n bs r -[mtm]->+ CounterRules.CounterRules.LC L k |> r4 *> WallInvariant.WallInvariant.normal rest *> r.
Proof.

 intros Hzero Hmark Hlen.
 destruct (marked_route_exists n bs Hzero Hmark Hlen) as [L [k [rest Hroute]]].
 destruct (route_dimensions _ _ _ _ _ Hroute) as [j [Hdim HL]].
 destruct (route_bounds _ _ _ _ _ Hroute Hzero Hlen) as [Hbound Hodd].
 exists L,k,rest,j. repeat split; try assumption.
 - apply (route_margin4 _ _ _ _ _ Hroute Hzero Hlen).
 - apply route_run; assumption.
Qed.

End MarkedTrace.
End MarkedTrace.

Module OdDeficit.
(* Exact fuel deficits carried by a reachable odd-wall conversion path.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import OddFuel OddImage OddRoute MarkedTrace.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module OdDeficit.

Lemma grown_complete k z : OddFuel.OddFuel.grown k z+1=(2*k+1)*2^z.
Proof.
 unfold OddFuel.OddFuel.grown. apply Nat.sub_add.
 apply Nat.mul_pos_pos; [lia|].
 apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia.
Qed.

Lemma step_deficit L k D u z :
 k+(2^(u+1)-1)+1+D=2^L ->
 OddFuel.OddFuel.grown k z+1+D*2^(z+1)+(2^(u+2)-1)*2^z=2^(L+1+z).
Proof.
 intro H. rewrite grown_complete.
 rewrite (Nat.pow_add_r 2 (L+1) z), (Nat.pow_add_r 2 L 1),
         (Nat.pow_add_r 2 z 1).
 change (2^1) with 2.
 assert (He : 2^(u+2)-1=2*(2^(u+1)-1)+1).
 { replace (u+2) with ((u+1)+1) by lia.
   rewrite (Nat.pow_add_r 2 (u+1) 1). change (2^1) with 2.
   pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)). lia. }
 rewrite He, <-H. ring.
Qed.

Lemma correction_bound u z :
 0<(2^(u+2)-1)*2^z<2^(u+2+z).
Proof.
 rewrite (Nat.pow_add_r 2 (u+2) z).
 assert (Hz:0<2^z) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
 assert (Hu:1<2^(u+2)).
 { apply (Nat.lt_le_trans _ 4); [lia|].
   change (2^2 <= 2^(u+2)). apply Nat.pow_le_mono_r; lia. }
 split.
 - apply Nat.mul_pos_pos; lia.
 - apply (proj1 (Nat.mul_lt_mono_pos_r _ _ _ Hz)); lia.
Qed.

(* The shifted correction and the fresh correction fit one extra bit
   above the larger bound.  Keep the symbolic powers in factored form. *)
Lemma correction_join a b z n e f :
 e<2^a -> f<2^b -> a+z<=n -> b<=n ->
 e*2^z+f<2^(n+1).
Proof.
 intros He Hf Ha Hb.
 assert (Hz:0<2^z) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
 assert (Hp:e*2^z<2^(a+z)).
 { rewrite Nat.pow_add_r. now apply (proj1 (Nat.mul_lt_mono_pos_r _ _ _ Hz)). }
 pose proof (Nat.pow_le_mono_r 2 (a+z) n ltac:(lia) Ha) as Hpa.
 pose proof (Nat.pow_le_mono_r 2 b n ltac:(lia) Hb) as Hpb.
 rewrite (Nat.pow_add_r 2 n 1). change (2^1) with 2.
 clear -Hp Hpa Hpb Hf. lia.
Qed.

Lemma route_deficit L k bs L' k' rest :
 OddRoute.OddRoute.route L k bs L' k' rest ->
 forall D, k+1+D=2^L ->
 exists j c,
 length bs=2*j+1+length rest /\ L'=L+5*j+2 /\
 0<c<2^(7*j+3) /\
 k'+1+D*2^(5*j+2)+c=2^L'.
Proof.

 intro Hr. induction Hr; intros D HD.
 - exists v,((2^(v*2+2)-1)*2^(v*5+1)).
   split; [rewrite length_app,repeat_length; cbn[length]; lia|].
   split; [lia|]. split.
   + pose proof (correction_bound (v*2) (v*5+1)) as H.
     replace (v*2+2+(v*5+1)) with (7*v+3) in H by lia. exact H.
   + replace (5*v+2) with ((v*5+1)+1) by lia.
     apply step_deficit. exact HD.
 - set (c0:=(2^(v*2+3)-1)*2^(v*5+4)).
   set (D0:=D*2^(v*5+5)+c0).

   assert (HD0:OddFuel.OddFuel.grown k (v*5+4)+1+D0=2^(L+1+(v*5+4))).
   { unfold D0,c0.
     replace (v*5+5) with ((v*5+4)+1) by lia.
     replace (v*2+3) with ((v*2+1)+2) by lia.
     rewrite Nat.add_assoc. apply step_deficit.
     replace (v*2+1+1) with (v*2+2) by lia. exact HD. }

   destruct (IHHr D0 HD0) as [j [c [Hlen [HL [Hc HE]]]]].
   exists (v+1+j),(c0*2^(5*j+2)+c).
   split; [rewrite length_app,repeat_length; cbn[length]; lia|].
   split; [lia|]. split.
   + assert (Hc0:0<c0<2^(7*v+7)).
     { unfold c0. pose proof (correction_bound (v*2+1) (v*5+4)) as H.
       replace (v*2+1+2+(v*5+4)) with (7*v+7) in H by lia.
       replace (v*2+1+2) with (v*2+3) in H by lia. exact H. }

     split.
     * clear -Hc. lia.
     * replace (7*(v+1+j)+3) with ((7*(v+1+j)+2)+1) by lia.
       eapply (correction_join (7*v+7) (7*j+3)); [exact (proj2 Hc0)|exact (proj2 Hc)| |];
         clear; lia.
   + assert (HP:2^(5*(v+1+j)+2)=2^(v*5+5)*2^(5*j+2)).
     { rewrite <-Nat.pow_add_r. f_equal. lia. }
     rewrite HP. unfold D0 in HE. rewrite <-HE. ring.
Qed.

Lemma initial_deficit n u z :
 u+1<=n ->
 OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n u) z+1+(2^(u+2)-3)*2^z=2^(n+1+z).
Proof.

 intro Hn. pose proof (OddImage.OddImage.first_fuel_bounds n u Hn) as [HE HB].
 rewrite grown_complete.
 repeat rewrite Nat.pow_add_r in *. cbn[Nat.pow] in *.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia.
Qed.

Lemma initial_even_deficit n v tail :
 length (repeat false (v*2)++true::tail)+1<=n ->
 OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2)) (v*5)+1+
   (2^(v*2+2)-3)*2^(v*5)=2^(n+1+v*5).
Proof.

 intro H. apply initial_deficit.
 rewrite length_app,repeat_length in H. cbn[length] in H. lia.
Qed.

Lemma initial_odd_route_deficit n v tail L k rest :
 OddRoute.OddRoute.route (n+1+(v*5+3)) (OddFuel.OddFuel.grown (OddImage.OddImage.first_fuel n (v*2+1)) (v*5+3))
   tail L k rest ->
 length (repeat false (v*2+1)++true::tail)+1<=n ->
 exists j c,
 length tail=2*j+1+length rest /\ L=n+5*(v+1+j)+1 /\
 0<c<2^(7*j+3) /\
 k+1+(2^(v*2+3)-3)*2^(5*(v+1+j))+c=2^L.
Proof.

 intros Hr Hn.

 assert (Hu:v*2+1+1<=n).
 { rewrite length_app,repeat_length in Hn. cbn[length] in Hn. lia. }
 pose proof (initial_deficit n (v*2+1) (v*5+3) Hu) as HD.
 destruct (route_deficit _ _ _ _ _ _ Hr ((2^(v*2+1+2)-3)*2^(v*5+3)) HD)
  as [j [c [Hlen [HL [Hc HE]]]]].
 exists j,c. split; [exact Hlen|]. split; [lia|]. split; [exact Hc|].
 replace (v*2+1+2) with (v*2+3) in HE by lia.

 assert (HP:2^(5*(v+1+j))=2^(v*5+3)*2^(5*j+2)).
 { rewrite <-Nat.pow_add_r. f_equal. lia. }
 rewrite HP, <-HE. ring.
Qed.

End OdDeficit.
End OdDeficit.

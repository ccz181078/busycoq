From BusyCoq Require Import NatMod Helper Eqb.
Require Import ZifyNat ZifyN NArith PeanoNat Lia Streams List.
Import ListNotations.

Inductive Nexpr :=
| Nadd(a b:Nexpr)
| Nsub(a:Nexpr)(b:N)
| Nmul(a b:Nexpr)
| Ndiv(a:Nexpr)(b:N)
| Npow(a:N)(b:Nexpr)
| Nconst(a:N)
| Nvar(i:nat)
.

Ltac rw_N2Nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in * ||
  rewrite N2Nat.inj_pow in * ||
  rewrite N2Nat.id in * ||
  rewrite Nat2N.id in *).

Section Nexpr_ctx.
Hypothesis mp:list nat.
Fixpoint Neval x :=
match x with
| Nadd a b => Neval a + Neval b
| Nsub a b => Neval a - N.to_nat b
| Nmul a b => Neval a * Neval b
| Ndiv a b => Neval a / N.to_nat b
| Npow a b => N.to_nat a ^ Neval b
| Nconst a => N.to_nat a
| Nvar i => nth i mp 0
end.
End Nexpr_ctx.

Fixpoint Nevals ls :=
match ls with
| [] => []
| h::t =>
  let mp := Nevals t in
  (Neval mp h)::mp
end.

Fixpoint Nmod_pre_upd(ls:list N)(i:nat)(m:N):list N :=
match ls,i with
| h::t,S i0 => h::Nmod_pre_upd t i0 m
| h::t,O => (N.lcm h m)::t
| [],_ => []
end.

Fixpoint Nmod_pre(x:Nexpr)(m:N)(ls:list N):list N :=
match x with
| Nadd a b => Nmod_pre a m (Nmod_pre b m ls)
| Nsub a _ => Nmod_pre a m ls
| Nmul a b => Nmod_pre a m (Nmod_pre b m ls)
| Ndiv a b => Nmod_pre a (m*b) ls
| Npow a b => Nmod_pre b (phi m) ls
| Nconst _ => ls
| Nvar i => Nmod_pre_upd ls i m
end.

Fixpoint Nmod_pre'(ls:list Nexpr)(ls':list N):list N :=
match ls,ls' with
| h::t,h'::t' =>
  let t':=Nmod_pre h h' t' in
  let t':=Nmod_pre' t t' in
  h'::t'
| _,_ => []
end.

Section Nlbs_ctx.
Hypothesis max_lb:N.

Fixpoint Npowlb'(a:N)(b:positive):N*bool :=
(match b with
| xH => if a<=?max_lb then (a,true) else (max_lb,false)
| xI b0 =>
  let '(x,x0):=Npowlb' a b0 in
  let c:=x*x*a in
  (N.min max_lb c,x0&&(c<=?max_lb))
| xO b0 =>
  let '(x,x0):=Npowlb' a b0 in
  let c:=x*x in
  (N.min max_lb c,x0&&(c<=?max_lb))
end)%N.

Lemma Npowlb'_spec a b:
  (a<>0 ->
  let '(x,x0) := Npowlb' a b in
  x <= a^(Npos b) /\
  (x0=true -> x=a^(Npos b)))%N.
Proof.
  induction b; cbn[Npowlb']; intros.
  - destruct (Npowlb' a b) as [x x0].
    rewrite and_true_iff.
    rewrite N.leb_le.
    replace (N.pos b~1)%N with ((Npos b)+(Npos b)+1)%N by lia.
    repeat rewrite N.pow_add_r.
    repeat rewrite N.pow_1_r.
    remember (a^Npos b)%N as v1.
    epose proof (N.mul_le_mono x v1 x v1).
    epose proof (N.mul_le_mono_pos_r (x*x) (v1*v1) a).
    split.
    + lia.
    + intros [I1 I2].
      subst x0.
      lia.
  - destruct (Npowlb' a b) as [x x0].
    rewrite and_true_iff.
    rewrite N.leb_le.
    replace (N.pos b~0)%N with ((Npos b)+(Npos b))%N by lia.
    repeat rewrite N.pow_add_r.
    remember (a^Npos b)%N as v1.
    epose proof (N.mul_le_mono x v1 x v1).
    split.
    + lia.
    + intros [I1 I2].
      subst x0.
      lia.
  - destruct (N.leb_spec a max_lb); lia.
Qed.

Definition Npowlb(a b:N):N*bool :=
(match b with
| N0 => (1,true)
| Npos b0 =>
  if a=?0 then (0,true) else Npowlb' a b0
end)%N.

Lemma Npowlb_spec a b:
  (let '(x,x0) := Npowlb a b in
  x <= a^b /\
  (x0=true -> x=a^b))%N.
Proof.
  unfold Npowlb.
  destruct b.
  1: lia.
  destruct (N.eqb_spec a 0).
  - subst.
    rewrite N.pow_0_l by lia.
    lia.
  - apply Npowlb'_spec; lia.
Qed.


Section Nlb_ctx.
Hypothesis mp:list (N*bool).
Fixpoint Nlb(x:Nexpr):N*bool :=
(match x with
| Nadd a b =>
  let '(a,a0):=Nlb a in
  let '(b,b0):=Nlb b in
  let c := a+b in
  if a0&&b0&&(c<=?max_lb) then (c,true)
  else (N.min max_lb c,false)
| Nsub a b =>
  let '(a,a0):=Nlb a in
  (a-b,a0)
| Nmul a b =>
  let '(a,a0):=Nlb a in
  let '(b,b0):=Nlb b in
  let c := a*b in
  if a0&&b0&&(c<=?max_lb) then (c,true)
  else (N.min max_lb c,false)
| Ndiv a b =>
  let '(a,a0):=Nlb a in
  (a/b,a0)
| Npow a b =>
  if a=?0 then (0,false)
  else
  let '(b,b0):=Nlb b in
  let '(x,x0):=Npowlb a b in
  (x,b0&&x0)
| Nconst a => if a<=?max_lb then (a,true) else (max_lb,false)
| Nvar i => nth i mp (0,true)
end)%N.

Definition lb_WF(w:N*bool)(y:nat):Prop :=
let '(x,x0):=w in
(N.to_nat x<=y /\ (x0=true -> N.to_nat x=y)).

Definition lbs_WF(ls:list nat):Prop :=
  (forall i, lb_WF (nth i mp (N0,true)) (nth i ls 0)).

Lemma Nlb_spec ls x:
  lbs_WF ls ->
  lb_WF (Nlb x) (Neval ls x).
Proof.
  unfold lbs_WF,lb_WF.
  intros.
  induction x; cbn[Nlb]; cbn[Neval].
  - destruct (Nlb x1) as [a a0].
    destruct (Nlb x2) as [b b0].
    destruct (a0 && b0 && (a + b <=? max_lb)%N) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E].
      subst a0 b0.
      lia.
    + lia.
  - destruct (Nlb x) as [a a0].
    destruct a0; lia.
  - destruct (Nlb x1) as [a a0].
    destruct (Nlb x2) as [b b0].
    epose proof (Nat.mul_le_mono (N.to_nat a) (Neval ls x1) (N.to_nat b) (Neval ls x2)).
    destruct (a0 && b0 && (a * b <=? max_lb)%N) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E].
      subst a0 b0.
      lia.
    + lia.
  - destruct (Nlb x) as [a a0].
    split.
    + rewrite N2Nat.inj_div.
      apply Nat.Div0.div_le_mono; lia.
    + intros; subst a0.
      rewrite N2Nat.inj_div.
      f_equal.
      tauto.
  - destruct (N.eqb_spec a 0).
    1: lia.
    destruct (Nlb x) as [b b0].
    epose proof (Npowlb_spec a b).
    destruct (Npowlb a b) as [x' x0].
    split.
    + epose proof (Nat.pow_le_mono_r (N.to_nat a) (N.to_nat b) (Neval ls x)).
      lia.
    + rewrite and_true_iff.
      intros [I1 I2].
      subst.
      destruct H0 as [I3 I4].
      rewrite I4 by trivial.
      rewrite N2Nat.inj_pow.
      destruct IHx as [I5 I6].
      rewrite I6 by trivial.
      trivial.
  - destruct (N.leb_spec a max_lb); lia.
  - apply H.
Qed.

End Nlb_ctx.

Fixpoint Nlbs(ls:list Nexpr):list (N*bool) :=
match ls with
| h::t =>
  let t':=Nlbs t in
  (Nlb t' h)::t'
| [] => []
end.

Lemma nth_nil {A} i (a:A):
  nth i [] a = a.
Proof.
  destruct i; reflexivity.
Qed.

Lemma Nlbs_spec ls:
  lbs_WF (Nlbs ls) (Nevals ls).
Proof.
  induction ls; cbn[Nlbs]; cbn[Nevals].
  - unfold lbs_WF,lb_WF.
    intros.
    repeat rewrite nth_nil.
    lia.
  - intro i.
    destruct i; cbn[nth].
    2: apply IHls.
    apply Nlb_spec,IHls.
Qed.

Section Nmod_ctx.
Hypothesis rems mods:list N.
Hypothesis lbs:list (N*bool).
Fixpoint Nmod(x:Nexpr)(m:N):option N :=
(match x with
| Nadd a b =>
  Nmod a m &&& (fun a' =>
  Nmod b m &&& (fun b' =>
  Some ((a'+b') mod m)))
| Nsub a b =>
  if m=?0 then None else
  if b<=? fst (Nlb lbs a) then
  Nmod a m &&& (fun a' =>
  Some ((a'+(m-(b mod m))) mod m))
  else None
| Nmul a b =>
  Nmod a m &&& (fun a' =>
  Nmod b m &&& (fun b' =>
  Some ((a'*b') mod m)))
| Ndiv a b =>
  if b=?0 then None else
  Nmod a (m*b) &&& (fun a' =>
  Some (a'/b))
| Npow a b =>
  if m=?0 then None else
  let m':=phi m in
  if m'=?0 then None else
  Nmod b m' &&& (fun b' =>
  if b'+m' <=? fst (Nlb lbs b) then
    let v2 := N_pow_mod_c a b' m in
    let v3 := N_pow_mod_c a m' m in
    let v4 := (v3*v2) mod m in
    if (v4*v3) mod m =? v4 then Some v4 else None
  else
    let '(b0,b1):=Nlb lbs b in
    if b1 then Some (N_pow_mod_c a b0 m)
    else None
  )
| Nconst a => Some (a mod m)
| Nvar i =>
  if (nth i mods 0) mod m =? 0 then
  Some ((nth i rems 0) mod m)
  else None
end)%N.

Definition rems_WF (ls:list nat):Prop :=
  forall i,
  (nth i ls 0) mod (N.to_nat (nth i mods N0)) = (N.to_nat (nth i rems N0)).

Lemma mod_mod a b c:
  c mod b = 0 ->
  (a mod b) = (a mod c) mod b.
Proof.
  intros.
  assert (c=0\/c<>0) as [E|E] by lia.
  1: subst; rewrite Nat.mod_0_r; reflexivity.
  rewrite (Nat.div_mod a c) by lia.
  rewrite (Nat.mul_comm c).
  rewrite (Nat.div_mod c b) by lia.
  rewrite (Nat.mul_comm b).
  rewrite H,Nat.add_0_r.
  rewrite Nat.mul_assoc.
  rewrite <-Nat.Div0.add_mod_idemp_l.
  rewrite Nat.Div0.mod_mul.
  rewrite <-Nat.mul_assoc.
  rewrite (Nat.mul_comm _ (c/b*b)).
  rewrite <-Nat.div_mod by lia.
  reflexivity.
Qed.

Lemma Nmod_spec x m (ls:list nat):
  lbs_WF lbs ls ->
  rems_WF ls ->
  match Nmod x m with
  | Some z => (Neval ls x) mod (N.to_nat m) = N.to_nat z
  | None => True
  end.
Proof.
  intros Hlbs Hrems.
  gen m.
  induction x; intros; cbn[Nmod]; cbn[Neval]; unfold if_Some.
  - specialize (IHx1 m).
    specialize (IHx2 m).
    destruct (Nmod x1 m); trivial.
    destruct (Nmod x2 m); trivial.
    rewrite Nat.Div0.add_mod.
    rewrite IHx1,IHx2.
    rw_N2Nat.
    reflexivity.
  - destruct (N.eqb_spec m 0); trivial.
    specialize (IHx m).
    epose proof (Nlb_spec _ _ x Hlbs) as I1.
    unfold lb_WF in I1.
    unfold fst.
    destruct (Nlb lbs x) as [x0 x1].
    destruct (N.leb_spec b x0); trivial.
    destruct (Nmod x m); trivial.
    rw_N2Nat.
    rewrite sub_mod by lia.
    rewrite IHx.
    reflexivity.
  - specialize (IHx1 m).
    specialize (IHx2 m).
    destruct (Nmod x1 m); trivial.
    destruct (Nmod x2 m); trivial.
    rewrite Nat.Div0.mul_mod.
    rewrite IHx1,IHx2.
    rw_N2Nat.
    reflexivity.
  - specialize (IHx (m*b)%N).
    destruct (N.eqb_spec b 0); trivial.
    destruct (Nmod x (m*b)%N); trivial.
    rw_N2Nat.
    rewrite <-IHx.
    eapply div_mod_comm; lia.
  - destruct (N.eqb_spec m 0); trivial.
    destruct (N.eqb_spec (phi m) 0); trivial.
    rename x into b.
    specialize (IHx (phi m)).
    destruct (Nmod b (phi m)) as [b'|]; trivial.
    epose proof (Nlb_spec _ _ b Hlbs) as I1.
    unfold lb_WF in I1.
    unfold fst.
    destruct (Nlb lbs b) as [b0 b1].
    destruct (N.leb_spec (b'+phi m) b0).
    + remember (N_pow_mod_c a b' m) as v2.
      remember (N_pow_mod_c a (phi m) m) as v3.
      remember ((v3*v2) mod m)%N as v4.
      destruct (N.eqb_spec ((v4*v3) mod m) v4) as [E|E]; trivial.
      rewrite N_pow_mod_c_spec in *.
      apply f_equal with (f:=N.to_nat) in Heqv2,Heqv3,Heqv4,E.
      rw_N2Nat.
      eapply pow_mod.
      * unfold nat_phi.
        rw_N2Nat.
        reflexivity.
      * lia.
      * lia.
      * apply IHx.
      * symmetry.
        apply Heqv2.
      * symmetry.
        apply Heqv3.
      * symmetry.
        apply Heqv4.
      * lia.
      * apply E.
    + destruct b1; trivial.
      rewrite N_pow_mod_c_spec.
      rw_N2Nat.
      f_equal.
      f_equal.
      symmetry.
      tauto.
  - rw_N2Nat.
    reflexivity.
  - specialize (Hrems i).
    remember (nth i mods N0) as v1.
    remember (nth i ls 0) as v2.
    destruct (N.eqb_spec (v1 mod m) 0) as [E|E]; trivial.
    apply f_equal with (f:=N.to_nat) in E.
    rw_N2Nat.
    rewrite <-Hrems.
    apply mod_mod,E.
Qed.

End Nmod_ctx.

Fixpoint Nmods'(ls:list Nexpr)(mods:list N)(lbs:list (N*bool)):option (list N) :=
match ls with
| [] => Some []
| h::t =>
  match mods with
  | modh::mods =>
    match lbs with
    | lbh::lbs =>
      Nmods' t mods lbs &&& (fun t' =>
      Nmod t' mods lbs h modh &&& (fun h' => Some (h'::t')))
    | [] => None
    end
  | [] => None
  end
end.

Lemma Nmods'_spec ls mods lbs:
lbs_WF lbs (Nevals ls) ->
match Nmods' ls mods lbs with
| None => True
| Some rems =>
  rems_WF rems mods (Nevals ls)
end.
Proof.
  gen mods lbs.
  induction ls; cbn[Nmods']; cbn[Nevals]; intros.
  - intro i.
    repeat rewrite nth_nil.
    rewrite Nat.Div0.mod_0_l; reflexivity.
  - destruct mods as [|modh mods]; trivial.
    destruct lbs as [|lbh lbs]; trivial.
    unfold if_Some.
    specialize (IHls mods lbs).
    destruct (Nmods' ls mods lbs) as [rems|]; trivial.
    assert (I1:lbs_WF lbs (Nevals ls)) by (intro i; specialize (H (S i)); apply H).
    epose proof (Nmod_spec _ _ _ a modh _ I1 (IHls I1)).
    destruct (Nmod rems mods lbs a modh) as [z|]; trivial.
    intro i.
    destruct i.
    + apply H0.
    + apply (IHls I1 i).
Qed.

Definition Nmods(ls:list Nexpr)(m:N) :=
let lbs := Nlbs ls in
let mods := Nmod_pre' ls (repeat m (length ls)) in
Nmods' ls mods lbs.

Lemma Nmods_spec ls m:
match Nmods ls m with
| None => True
| Some rems =>
  rems_WF rems (Nmod_pre' ls (repeat m (length ls))) (Nevals ls)
end.
Proof.
  apply Nmods'_spec.
  apply Nlbs_spec.
Qed.

Definition Nmod' x ls m :=
Nmods (x::ls) m &&& (fun ls' => hd_error ls').

Lemma Nmod'_spec x ls m:
match Nmod' x ls m with
| Some z => (Neval (Nevals ls) x) mod (N.to_nat m) = N.to_nat z
| None => True
end.
Proof.
  unfold Nmod',if_Some.
  epose proof (Nmods_spec (x::ls) m) as I1.
  destruct (Nmods (x::ls) m) as [z|] eqn:E; trivial.
  specialize (I1 0).
  cbn in I1.
  destruct z as [|z0 z].
  - cbn; trivial.
  - apply I1.
Qed.

Definition Nmod'' x ls m := Nmod' x ls (N.of_nat m) &&& (fun z => Some (N.to_nat z)).

Lemma Nmod''_spec x ls m:
match Nmod'' x ls m with
| Some z => (Neval (Nevals ls) x) mod m = z
| None => True
end.
Proof.
  unfold Nmod'',if_Some.
  epose proof (Nmod'_spec x ls (N.of_nat m)) as I1.
  destruct (Nmod' x ls (N.of_nat m)) as [z|]; trivial.
  rw_N2Nat.
  apply I1.
Qed.

Definition Nsubge x ls m :=
if (N.of_nat m <=? fst (Nlb (Nlbs ls) x))%N then Some (Nsub x (N.of_nat m)) else None.

Lemma Nsubge_spec x ls m:
match Nsubge x ls m with
| Some z => Neval (Nevals ls) x = Neval (Nevals ls) z + m
| None => True
end.
Proof.
  unfold Nsubge.
  epose proof (Nlb_spec (Nlbs ls) (Nevals ls) x (Nlbs_spec _)) as I1.
  unfold lb_WF in I1.
  destruct (Nlb (Nlbs ls) x) as [x0 x1].
  unfold fst.
  destruct (N.leb_spec (N.of_nat m) x0); trivial.
  cbn.
  lia.
Qed.

Section pair_iter.
Hypothesis f: nat*nat->option (nat*nat).
Hypothesis g: (list Nexpr)->option (list Nexpr).
Hypothesis g_spec:
  forall a0 b0 ls,
  nth 0 (Nevals ls) 0 = a0 ->
  nth 1 (Nevals ls) 0 = b0 ->
  match f (a0,b0) with
  | Some (a1,b1) =>
    g ls = Some ls \/
    exists ls', g ls = Some ls' /\ nth 0 (Nevals ls') 0 = a1 /\ nth 1 (Nevals ls') 0 = b1
  | None => True
  end.

Lemma pair_iter_halts_if' a b ls:
  nth 0 (Nevals ls) 0 = a ->
  nth 1 (Nevals ls) 0 = b ->
  iter_halts g ls ->
  iter_halts f (a,b).
Proof.
  intros.
  gen a b.
  induction H1; intros.
  - specialize (g_spec _ _ _ H0 H1).
    destruct (f (a,b)) as [[a1 b1]|] eqn:E.
    + destruct g_spec as [|[ls' [I1 I2]]]; congruence.
    + econstructor.
      apply E.
  - specialize (g_spec _ _ _ H0 H2).
    destruct (f (a,b)) as [[a1 b1]|] eqn:E.
    + destruct g_spec as [|[ls' [I1 [I2a I2b]]]].
      1:{
        rewrite H3 in H.
        inverts H.
        apply IHiter_halts; assumption.
      }
      rewrite I1 in H.
      inverts H.
      eapply iter_halts_S.
      1: eassumption.
      eapply IHiter_halts; eassumption.
    + econstructor.
      apply E.
Qed.

Hypothesis a b:nat.
Lemma pair_iter_halts_if:
  iter_halts g [Nconst (N.of_nat a);Nconst (N.of_nat b)] ->
  iter_halts f (a,b).
Proof.
  apply pair_iter_halts_if'; cbn; lia.
Qed.
End pair_iter.

End Nlbs_ctx.

Definition Nnatc(x:nat):Nexpr := Nconst (N.of_nat x).

Declare Scope Nexpr_scope.
Delimit Scope Nexpr_scope with Nexpr.
Notation "a + b" := (Nadd a b) : Nexpr_scope.
Notation "a - b" := (Nsub a (b%N)) : Nexpr_scope.
Notation "a * b" := (Nmul a b) : Nexpr_scope.
Notation "a / b" := (Ndiv a (b%N)) : Nexpr_scope.
Notation "a ^ b" := (Npow (a%N) b) : Nexpr_scope.
Notation "a .[ b ]" := (Neval (Nevals a) b) : Nexpr_scope.
Coercion Nnatc : nat >-> Nexpr.

Fixpoint lift n x :=
match x with
| Nadd a b => Nadd (lift n a) (lift n b)
| Nsub a b => Nsub (lift n a) b
| Nmul a b => Nmul (lift n a) (lift n b)
| Ndiv a b => Ndiv (lift n a) b
| Npow a b => Npow a (lift n b)
| Nconst a => Nconst a
| Nvar i => Nvar (n+i)
end.

Module PairIter.

Definition cons2 x (ls:list Nexpr) :=
let '(x0,x1):=x in Some (lift 1 x0::x1::ls).

Ltac solve_v1 :=
  intros; cbn; subst;
  match goal with
  | |- context[Nmod'' ?T ?x ?ls ?m] =>
    let I1:=fresh "I" in
    epose proof (Nmod''_spec T x ls m) as I1;
    cbn in I1;
    let z:=fresh "z" in
    destruct (Nmod'' T x ls m) as [z|];
    subst
  end;
  [
    match goal with
    | |- match match ?a mod ?b with _ => _ end with _ => _ end =>
      let z:=fresh "z" in
      remember a as z
    end
  |
    match goal with
    | |- match ?a with _ => _ end =>
      destruct a as [[a1 b1]|]; [left; trivial|trivial]
    end
  ].

Ltac solve_v2 :=
  trivial || (right; eexists; split; [reflexivity|]; subst; split; cbn; reflexivity).

End PairIter.

Lemma div_mod'' a b c:
  a mod b = c ->
  a = a/b*b + c.
Proof. lia. Qed.

Module NatModTactics.

Lemma Nexpr_div_mod_v2 max_lb mp (a:Nexpr)(b c:nat):
  Nmod'' max_lb a mp b = Some c ->
  (mp .[ a ])%Nexpr = (mp .[ a ])%Nexpr / b * b + c.
Proof.
  intros.
  apply div_mod''.
  epose proof (Nmod''_spec _ _ _ _) as I1.
  rewrite H in I1.
  apply I1.
Qed.

Lemma Nexpr_div_mod_v1 max_lb mp (a:Nexpr)(b c:nat):
  Nmod'' max_lb a mp b = Some c ->
  (mp .[ a ])%Nexpr = c + (mp .[ a ])%Nexpr / b * b.
Proof.
  intros.
  apply div_mod'.
  epose proof (Nmod''_spec _ _ _ _) as I1.
  rewrite H in I1.
  apply I1.
Qed.

Lemma Nexpr_sub_v1 max_lb mp (a:Nexpr)(c:nat) a':
  Nsubge max_lb a mp c = Some a' ->
  (mp .[ a ])%Nexpr = c + (mp .[ a' ])%Nexpr.
Proof.
  intros.
  epose proof (Nsubge_spec _ _ _ _) as I1.
  rewrite H in I1.
  lia.
Qed.

Lemma Nexpr_sub_v2 max_lb mp (a:Nexpr)(c:nat) a':
  Nsubge max_lb a mp c = Some a' ->
  (mp .[ a ])%Nexpr = (mp .[ a' ])%Nexpr + c.
Proof.
  intros.
  epose proof (Nsubge_spec _ _ _ _) as I1.
  rewrite H in I1.
  lia.
Qed.

Lemma Nexpr_div_mod_v1' max_lb mp a b c a':
  Nsubge max_lb a mp c = Some a' ->
  Nmod'' max_lb a' mp b = Some O ->
  (mp .[ a ])%Nexpr = (c + (mp .[ a'])%Nexpr / b * b).
Proof.
  intros I1 I2.
  apply Nexpr_sub_v1 in I1.
  apply Nexpr_div_mod_v1 in I2.
  lia.
Qed.

Lemma Nexpr_div_mod_v2' max_lb mp a b c a':
  Nsubge max_lb a mp c = Some a' ->
  Nmod'' max_lb a' mp b = Some O ->
  (mp .[ a ])%Nexpr = ((mp .[ a'])%Nexpr / b * b + c).
Proof.
  intros I1 I2.
  apply Nexpr_sub_v2 in I1.
  apply Nexpr_div_mod_v2 in I2.
  lia.
Qed.

Ltac get_max_lb := constr:((2^30)%N).

Ltac R_mod_v1 mp a b :=
  let max_lb := get_max_lb in
  erewrite (Nexpr_div_mod_v1 max_lb mp a b) by crefl.

Ltac R_mod_v2 mp a b :=
  let max_lb := get_max_lb in
  erewrite (Nexpr_div_mod_v2 max_lb mp a b) by crefl.

Lemma feq{A B}(f g:A->B)(x y:A):
  f=g ->
  x=y ->
  f x = g y.
Proof.
  congruence.
Qed.

Lemma Peq(P Q:Prop):
  Q=P -> P -> Q.
Proof.
  congruence.
Qed.

Open Scope Nexpr.

Lemma Nconst_eq mp n n0:
  N.of_nat n = n0 ->
  n = mp .[ Nconst n0].
Proof.
  cbn; lia.
Qed.

Lemma Nadd_eq mp a b a0 b0:
  a = mp.[a0] ->
  b = mp.[b0] ->
  Nat.add a b = mp.[a0+b0].
Proof.
  cbn; lia.
Qed.

Lemma Nsub_eq mp a b a0 b0:
  a = mp.[a0] ->
  N.of_nat b = b0 ->
  Nat.sub a b = mp.[a0-b0].
Proof.
  cbn; lia.
Qed.

Lemma Nmul_eq mp a b a0 b0:
  a = mp.[a0] ->
  b = mp.[b0] ->
  Nat.mul a b = mp.[a0*b0].
Proof.
  cbn; lia.
Qed.

Lemma Ndiv_eq mp a b a0 b0:
  a = mp.[a0] ->
  N.of_nat b = b0 ->
  Nat.div a b = mp.[a0/b0].
Proof.
  cbn.
  intros; subst.
  lia.
Qed.

Lemma Npow_eq mp a b a0 b0:
  N.of_nat a = a0 ->
  b = mp.[b0] ->
  Nat.pow a b = mp.[a0^b0].
Proof.
  cbn.
  intros; subst.
  lia.
Qed.

Lemma mp_cons mp x:
  mp.[x] = (x::mp).[ Nvar 0].
Proof.
  reflexivity.
Qed.

Lemma lift_cons mp x y y':
  lift 1 y = y' ->
  mp.[y] = (x::mp).[y'].
Proof.
  intros; subst.
  induction y; cbn in *; congruence.
Qed.

Ltac get_mp :=
match goal with
| [ mp := _ |- _] => mp
| [ mp : list Nexpr |- _] => mp
end.

Ltac rw_Nexpr :=
match goal with
| |- @eq nat ?a ?a' =>
  match a with
  | ?mp .[ ?x ] => reflexivity
  | Nat.add _ _ => eapply Nadd_eq; [rw_Nexpr|rw_Nexpr]
  | Nat.sub _ _ => eapply Nsub_eq; [rw_Nexpr|crefl]
  | Nat.mul _ _ => eapply Nmul_eq; [rw_Nexpr|rw_Nexpr]
  | Nat.div _ _ => eapply Ndiv_eq; [rw_Nexpr|crefl]
  | Nat.pow _ _ => eapply Npow_eq; [crefl|rw_Nexpr]
  | _ =>
    let mp:=get_mp in
    is_nat_const a;
    eapply (Nconst_eq mp); crefl
  end
| |- ?a = _ =>
  match a with
  | _ _ => eapply feq; rw_Nexpr
  | _ => reflexivity
  end
| _ => eapply Peq; [rw_Nexpr|]
end.

Ltac match_Nexpr :=
match goal with
| |- @eq nat ?a ?a' =>
  match a with
  | ?mp .[ ?x ] =>
    match a' with
    | Neval _ _ => reflexivity
    | (?a + ?b * ?c)%nat =>
        idtac mp x a b c;
      is_nat_const c;
      let max_lb := get_max_lb in
      (is_nat_const a; eapply (Nexpr_div_mod_v1' max_lb mp x c); [crefl|]; crefl) +
      (apply (Nexpr_div_mod_v1 max_lb mp x c); crefl)
    | (?b * ?c + ?a)%nat =>
        idtac mp x a b c;
      is_nat_const c;
      let max_lb := get_max_lb in
      (is_nat_const a; eapply (Nexpr_div_mod_v2' max_lb mp x c); [crefl|]; crefl) +
      (apply (Nexpr_div_mod_v2 max_lb mp x c); crefl)
    | (?a + ?b)%nat =>
        idtac mp x a b;
      is_nat_const a;
      let max_lb := get_max_lb in
      apply (Nexpr_sub_v1 max_lb mp x a); crefl
    | (?b + ?a)%nat =>
        idtac mp x a b;
      is_nat_const a;
      let max_lb := get_max_lb in
      apply (Nexpr_sub_v2 max_lb mp x a); crefl
    | ?e => is_evar e; reflexivity
    | ?e =>
      is_nat_const e;
      match x with
      | Nconst _ => symmetry; apply Nconst_eq; crefl
      end
    end
  end
| |- ?a = _ =>
  match a with
  | _ _ => eapply feq; match_Nexpr
  | _ => reflexivity
  end
| _ => idtac
end.



Ltac rw_lift_1 :=
  progress
multimatch goal with
| |- context[ ?mp .[ ?x ] ] =>
  match x with
  | Nvar _ => idtac
  | Nconst _ => idtac
  | _ =>
    rewrite (mp_cons mp x);
    repeat erewrite (lift_cons mp x) by crefl;
    let mp0:=fresh "mp" in
    set (mp0:=x::mp);
    subst mp;
    rename mp0 into mp
  end
end.

Ltac rw_lift := repeat rw_lift_1.

Ltac arg1 a := idtac.

Ltac rw_all :=
  (tryif (arg1 get_mp) then idtac else (set (mp:=@nil Nexpr)));
  rw_Nexpr;
  rw_lift.

Lemma Nexpr_ge max_lb mp x c x':
  Nsubge max_lb x mp c = Some x' ->
  mp.[x] >= c.
Proof.
  intros.
  apply Nexpr_sub_v1 in H.
  lia.
Qed.

Ltac solve_Nexpr_ge :=
  eapply Peq;[eapply feq;[rw_Nexpr|reflexivity]|];
  let max_lb := get_max_lb in
  match goal with
  | |- ?mp .[ ?x ] >= ?c =>
    eapply (Nexpr_ge max_lb mp x c); crefl
  end.

Ltac R_mod'' a b :=
  eassert (X:_) by (eapply (div_mod'' a b _); rw_mod_1);
  rewrite X in *;
  clear X.

Ltac R_mod' a b :=
  eassert (X:_) by (eapply (div_mod' a b _); rw_mod_1);
  rewrite X in *;
  clear X.

End NatModTactics.


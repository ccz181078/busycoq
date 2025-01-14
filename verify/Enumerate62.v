Require Import List.
Require Import Lia.
From BusyCoq Require Import Individual62.
From BusyCoq Require Import CTL62.
From BusyCoq Require Import TC.
From BusyCoq Require Import Eqb.

Module TC := TC BB62.
Import TC.

Definition makeTM(a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1:option (Sym*dir*Q)):TM :=
fun '(s,m) =>
match s,m with
| A,S0 => a0
| A,S1 => a1
| B,S0 => b0
| B,S1 => b1
| C,S0 => c0
| C,S1 => c1
| D,S0 => d0
| D,S1 => d1
| E,S0 => e0
| E,S1 => e1
| F,S0 => f0
| F,S1 => f1
end.

Definition tm_simpl(tm:TM):TM :=
makeTM
(tm (A,S0))
(tm (A,S1))
(tm (B,S0))
(tm (B,S1))
(tm (C,S0))
(tm (C,S1))
(tm (D,S0))
(tm (D,S1))
(tm (E,S0))
(tm (E,S1))
(tm (F,S0))
(tm (F,S1)).

Lemma tm_simpl_spec tm:
  eqv (tm_simpl tm) tm.
Proof.
  unfold tm_simpl.
  eapply perm_eqv with (f:=fun x=>x); eauto.
  unfold Perm.
  split; intros q s; destruct q,s; cbn; tauto.
Qed.

Lemma tm_simpl_spec' tm h:
  (tm_simpl tm h) = tm h.
Proof.
  destruct h as [q s].
  destruct q,s; reflexivity.
Qed.

Definition tm_upd(tm:TM)(h:Q*Sym)(y:Sym*dir*Q):TM :=
  tm_simpl (fun x => if eqb x h then Some y else tm x).

Module TNF_Node.
Record T := {
  tm: TM;
  num_undef_trans: nat;
  min_unused_state: nat;
}.

Definition Nat_sum(x:list nat) := List.fold_right Nat.add O x.

Definition get_num_undef_trans(tm:TM) :=
Nat_sum (List.map (fun q => Nat_sum (List.map (fun s => if tm (q,s) then 0 else 1)%nat all_syms)) all_qs).

Fixpoint In_dec{A}(eq:forall a b:A,{a=b}+{a<>b})(x:A)(ls:list A):{List.In x ls}+{~List.In x ls}.
Proof.
  destruct ls as [|h t].
  - right.
    intros H.
    inverts H.
  - destruct (eq x h).
    + left. cbn. left. congruence.
    + destruct (In_dec A eq x t); cbn.
      * left; tauto.
      * right. intuition.
Defined.

Definition WF(x:T):Prop :=
let (tm,n,m):=x in
n = get_num_undef_trans tm /\
match List.skipn m all_qs with
| nil => True
| q1::qs =>
  Perm tm tm (fun q => if In_dec eqb_q q qs then q1 else q)
end.

Lemma all_qs_nodup: List.NoDup all_qs.
Proof.
  repeat econstructor.
  all:
  match goal with
  | |- ~List.In ?x ?ls => pose (In_dec eqb_q x ls) as H;
    cbn in *;
    destruct H eqn:E;
    [ unfold H in E; congruence
    | apply n ]
  end.
Qed.

Definition expand(x:T)(h:Q*Sym):list T.
Proof.
  refine (
  let (tm,n,m):=x in _).
  refine (_ ++ _)%list.
  - refine (flat_map (fun s => _) (firstn m all_qs)).
    refine (flat_map (fun o => _) all_syms).
    refine (List.map (fun d => _) [L;R]).
    refine (Build_T (tm_upd tm h (o,d,s)) (Nat.pred n) m).
  - refine (match skipn m all_qs with
            | nil => nil
            | q1::qs => _
            end).
    refine (flat_map (fun o => _) all_syms).
    refine (List.map (fun d => _) [L;R]).
    refine (Build_T (tm_upd tm h (o,d,q1)) (Nat.pred n) (S m)).
Defined.

Definition expand'(x:T)(h:Q*Sym):list T :=
  if eqb x.(num_undef_trans) (S O) then [] else expand x h.

Definition node0 := Build_T (TM_from_str "1RB---_------_------_------_------_------") 11 2.

Definition SearchQueue:Type := (list T)*(list T).
Open Scope list.

Fixpoint length_tail_0{A}(ls:list A)(n:N):N :=
match ls with
| nil => n
| h::t => length_tail_0 t (N.succ n)
end.

Definition length_tail{A}(ls:list A):N :=
  length_tail_0 ls N0.

Definition num_holdout(q:SearchQueue):N :=
length_tail (snd q).

Definition root_1RB:SearchQueue := ([node0],[]).

Definition get_SQ(q:SearchQueue+SearchQueue):SearchQueue :=
match q with
| inl x => x
| inr x => x
end.

Definition SearchQueue_upd(f:TM->DecideResult)(q:SearchQueue):SearchQueue+SearchQueue :=
let (q1,q2):=q in
match q1 with
| nil => inr q
| x::q1' =>
  inl
  match f x.(tm) with
  | Halt h => (expand' x h ++ q1',q2)
  | NonHalt => (q1',q2)
  | Unknown => (q1',x::q2)
  end
end.

Definition SearchQueue_upds(f:TM->DecideResult)(q:SearchQueue)(n:N) :=
get_SQ (N_iter_until (SearchQueue_upd f) (inl q) n).


Definition SearchQueue_upd_bfs(f:TM->DecideResult)(q:SearchQueue):SearchQueue+SearchQueue :=
let (q1,q2):=q in
match q1 with
| nil => inr q
| x::q1' =>
  inl
  match f x.(tm) with
  | Halt h => (q1',expand' x h ++ q2)
  | NonHalt => (q1',q2)
  | Unknown => (q1',x::q2)
  end
end.

Definition SearchQueue_rst(q:SearchQueue):SearchQueue :=
let (q1,q2):=q in (q1++q2,[]).

Definition SearchQueue_upds_bfs(f:TM->DecideResult)(q:SearchQueue) :=
SearchQueue_rst (get_SQ (N_iter_until (SearchQueue_upd_bfs f) (inl q) (length_tail (fst q)))).







Definition decider(tm0:TM):DecideResult.
Proof.
  refine (
    match TC_state.decide tm0 [([50]%N,20%nat);([50;100;200]%N,40%nat)] with
    | (Halt h,_) => Halt h
    | (NonHalt,_) => NonHalt
    | (Unknown,_) => _
    end).
  refine (if (decide_nonhalt tm0 (NG 0 1 100 1 0 0 0 false)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (NG 0 2 200 2 0 0 0 false)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (NG 0 8 800 3 0 0 0 false)) then NonHalt else _).
  refine (
    match TC_state.decide tm0 [([2000]%N,O)] with
    | (Halt h,_) => Halt h
    | (NonHalt,_) => NonHalt
    | (Unknown,_) => _
    end).
  refine (if (decide_nonhalt tm0 (NG 0 30 3000 3 2 4 0 true)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (RWL_mod 0 30 3000 2 320 2 1 4 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (RWL_mod 0 30 3000 3 320 2 1 4 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (RWL_mod 0 30 3000 4 320 2 1 4 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (RWL_mod 0 30 3000 6 320 2 1 4 0)) then NonHalt else _).
  refine (
    match TC_state.decide tm0 [([100000]%N,O)] with
    | (Halt h,_) => Halt h
    | (NonHalt,_) => NonHalt
    | (Unknown,_) => _
    end).
  refine (if (decide_nonhalt tm0 (NG 0 30 3000 3 2 12 0 true)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 2 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 3 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 4 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 5 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 6 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 7 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 8 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 9 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 10 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 11 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 30 3000 12 320 0 1 0 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (NG 0 100 10000 2 4 0 0 true)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 1001 100 10000 2 320 1 14 1 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (RWL_mod 1001 30 3000 2 320 2 3 12 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (NG 0 100 10000 3 8 8 0 true)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (NG 0 100 10000 2 6 0 0 true)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (RWL_mod 1001 10 1000 2 320 2 2 6 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (RWL_mod 1001 1000 100000 1 320 2 2 4 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (CPS_LRU 0 10 1000 4 320 0 3 1 0)) then NonHalt else _).
  refine (if (decide_nonhalt tm0 (RWL_mod 1001 100 10000 6 320 2 2 8 0)) then NonHalt else _).
  refine (
    match TC_state.decide tm0 [([1000000]%N,O)] with
    | (Halt h,_) => Halt h
    | (NonHalt,_) => NonHalt
    | (Unknown,_) => _
    end).
  refine Unknown.
Defined.

End TNF_Node.

Import TNF_Node.

Definition MAXT:=(2^60)%N.

Definition q_0 := (N.iter 4 (SearchQueue_upds_bfs decider) root_1RB).
Definition q_i l sz := (firstn sz (skipn l (fst q_0)),snd q_0).

(*
Compute (length_tail (fst q_0)).
Time Definition q_1 := Eval native_compute in (SearchQueue_upds decider (q_i 0 100) MAXT).
 *)

Definition show_holdout (q:SearchQueue) := (List.map (fun x => TM_to_str x.(tm)) (snd q)).
Definition holdout_i l sz := show_holdout (SearchQueue_upds decider (q_i l sz) MAXT).


